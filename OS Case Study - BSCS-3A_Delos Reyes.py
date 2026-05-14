"""
Delos Reyes, Vincent Charles M.
BSCS-3A
OS Case Study

"""

import tkinter as tk
from tkinter import ttk, messagebox
import copy
from collections import deque


# shared helper — finish times come in, waiting/turnaround go out
def _times(processes, finish):
    wt, tat = {}, {}
    for p in processes:
        tat[p["pid"]] = finish[p["pid"]] - p["arrival"]
        wt[p["pid"]]  = tat[p["pid"]] - p["burst"]
    return wt, tat


def fcfs(procs):
    # arrival first, then insertion order to break ties consistently
    ps = sorted(procs, key=lambda p: (p["arrival"], p["i"]))
    t, gantt, fin = 0, [], {}
    for p in ps:
        start = max(t, p["arrival"])
        end   = start + p["burst"]
        gantt.append((p["pid"], start, end))
        fin[p["pid"]] = end
        t = end
    return gantt, *_times(procs, fin)


def sjf(procs):
    # non-preemptive — once a process starts it runs to completion
    ps = copy.deepcopy(procs)
    t, gantt, fin, done = 0, [], {}, set()
    while len(done) < len(procs):
        ready = [p for p in ps if p["arrival"] <= t and p["pid"] not in done]
        if not ready:
            t = min(p["arrival"] for p in ps if p["pid"] not in done)
            continue
        # shortest burst wins; arrival + index break ties so it's deterministic
        chosen = min(ready, key=lambda p: (p["burst"], p["arrival"], p["i"]))
        end = t + chosen["burst"]
        gantt.append((chosen["pid"], t, end))
        fin[chosen["pid"]] = end
        done.add(chosen["pid"])
        t = end
    return gantt, *_times(procs, fin)


def srt(procs):
    # preemptive SJF — tick by tick, always pick lowest remaining time
    rem = {p["pid"]: p["burst"] for p in procs}
    ps  = copy.deepcopy(procs)
    t, gantt, fin, done = 0, [], {}, set()

    while len(done) < len(procs):
        ready = [p for p in ps if p["arrival"] <= t and p["pid"] not in done]
        if not ready:
            t += 1
            continue

        chosen = min(ready, key=lambda p: (rem[p["pid"]], p["arrival"], p["i"]))

        # extend the last bar instead of adding a new one when same process continues
        if gantt and gantt[-1][0] == chosen["pid"]:
            gantt[-1] = (gantt[-1][0], gantt[-1][1], t + 1)
        else:
            gantt.append((chosen["pid"], t, t + 1))

        rem[chosen["pid"]] -= 1
        if rem[chosen["pid"]] == 0:
            fin[chosen["pid"]] = t + 1
            done.add(chosen["pid"])
        t += 1

    return gantt, *_times(procs, fin)


def rr(procs, q):
    ps  = sorted(procs, key=lambda p: (p["arrival"], p["i"]))
    rem = {p["pid"]: p["burst"] for p in ps}
    t, gantt, fin = 0, [], {}
    queue = deque()
    idx = 0

    # seed the queue with anything already available at t=0
    while idx < len(ps) and ps[idx]["arrival"] <= t:
        queue.append(ps[idx]); idx += 1

    while queue or idx < len(ps):
        if not queue:
            t = ps[idx]["arrival"]
            while idx < len(ps) and ps[idx]["arrival"] <= t:
                queue.append(ps[idx]); idx += 1

        if not queue:
            continue

        p   = queue.popleft()
        pid = p["pid"]
        run = min(q, rem[pid])
        end = t + run

        # merge adjacent slices for the same PID so the Gantt doesn't get noisy
        if gantt and gantt[-1][0] == pid:
            gantt[-1] = (gantt[-1][0], gantt[-1][1], end)
        else:
            gantt.append((pid, t, end))

        rem[pid] -= run
        t = end

        # admit any new arrivals before deciding whether to re-queue
        while idx < len(ps) and ps[idx]["arrival"] <= t:
            queue.append(ps[idx]); idx += 1

        if rem[pid] == 0:
            fin[pid] = t
        else:
            queue.append(p)

    return gantt, *_times(procs, fin)


def priority_np(procs):
    ps = copy.deepcopy(procs)
    t, gantt, fin, done = 0, [], {}, set()

    while len(done) < len(procs):
        ready = [p for p in ps if p["arrival"] <= t and p["pid"] not in done]
        if not ready:
            t = min(p["arrival"] for p in ps if p["pid"] not in done)
            continue
        # lower number = higher priority per the usual convention
        chosen = min(ready, key=lambda p: (p["priority"], p["arrival"], p["i"]))
        end = t + chosen["burst"]
        gantt.append((chosen["pid"], t, end))
        fin[chosen["pid"]] = end
        done.add(chosen["pid"])
        t = end

    return gantt, *_times(procs, fin)


def priority_rr(procs, q):
    # RR within the highest-priority group — lower number still means higher priority
    ps  = sorted(procs, key=lambda p: (p["arrival"], p["i"]))
    rem = {p["pid"]: p["burst"] for p in ps}
    t, gantt, fin, done, pool = 0, [], {}, set(), []
    idx = 0

    def admit():
        nonlocal idx
        while idx < len(ps) and ps[idx]["arrival"] <= t:
            pool.append(ps[idx]); idx += 1

    admit()

    while len(done) < len(procs):
        available = [p for p in pool if p["pid"] not in done]
        if not available:
            if idx < len(ps):
                t = ps[idx]["arrival"]
                admit()
            continue

        top_priority = min(p["priority"] for p in available)
        # pick the first one at the front of the pool with that priority
        chosen = next(p for p in available if p["priority"] == top_priority)
        pid = chosen["pid"]
        run = min(q, rem[pid])
        end = max(t, chosen["arrival"]) + run  # shouldn't differ from t at this point but just in case

        if gantt and gantt[-1][0] == pid:
            gantt[-1] = (gantt[-1][0], gantt[-1][1], end)
        else:
            gantt.append((pid, t, end))

        rem[pid] -= run
        t = end
        admit()

        if rem[pid] == 0:
            fin[pid] = t
            done.add(pid)
            pool.remove(chosen)
        else:
            pool.remove(chosen)
            pool.append(chosen)   # send to back of pool

    return gantt, *_times(procs, fin)


# ---------------------------------------------------------------------------
# GUI
# ---------------------------------------------------------------------------

class App(tk.Tk):

    MIN_PROCS = 3

    def __init__(self):
        super().__init__()
        self.title("OS Case Study: CPU Scheduling Simulator")
        self.resizable(False, False)
        self._rows = []
        self._build_ui()
        self._refresh_controls()
        self._set_rows(3)

    def _build_ui(self):
        tk.Label(self, text="CPU Scheduling Simulator",
                 font=("TkDefaultFont", 14, "bold")).grid(
                 row=0, column=0, columnspan=2, pady=(10, 4), padx=10, sticky="w")

        # left panel — algorithm picker + process count controls
        left = tk.Frame(self)
        left.grid(row=1, column=0, sticky="nw", padx=(10, 5), pady=5)

        tk.Label(left, text="Algorithm:").grid(row=0, column=0, sticky="w")
        self._algo = tk.StringVar(value="FCFS")
        self._combo = ttk.Combobox(
            left, textvariable=self._algo, state="readonly", width=28,
            values=[
                "FCFS",
                "SJF (Non-preemptive)",
                "SRT (Preemptive)",
                "Round Robin",
                "Priority (Non-preemptive)",
                "Priority + Round Robin",
            ]
        )
        self._combo.grid(row=1, column=0, sticky="w", pady=(0, 8))
        self._combo.bind("<<ComboboxSelected>>", lambda e: self._refresh_controls())

        # quantum row — hidden unless RR is selected
        self._qframe = tk.Frame(left)
        self._qframe.grid(row=2, column=0, sticky="w")
        tk.Label(self._qframe, text="Time Quantum:").pack(side="left")
        self._quantum = tk.StringVar(value="2")
        tk.Entry(self._qframe, textvariable=self._quantum, width=5).pack(side="left", padx=4)

        tk.Label(left, text="Processes:").grid(row=3, column=0, sticky="w", pady=(8, 2))
        cnt_row = tk.Frame(left)
        cnt_row.grid(row=4, column=0, sticky="w")
        tk.Button(cnt_row, text="-", width=2,
                  command=lambda: self._set_rows(len(self._rows) - 1)).pack(side="left")
        self._cnt_lbl = tk.Label(cnt_row, text="3", width=3)
        self._cnt_lbl.pack(side="left")
        tk.Button(cnt_row, text="+", width=2,
                  command=lambda: self._set_rows(len(self._rows) + 1)).pack(side="left")

        self._pnote = tk.Label(left, text="(Lower priority number = higher priority)",
                               font=("TkDefaultFont", 8), fg="gray")
        self._pnote.grid(row=5, column=0, sticky="w", pady=(4, 0))

        tk.Button(left, text="Run",   width=28, command=self._run  ).grid(row=6, column=0, pady=(12, 2), sticky="w")
        tk.Button(left, text="Clear", width=28, command=self._clear).grid(row=7, column=0, sticky="w")

        # right panel — process table, gantt, results
        right = tk.Frame(self)
        right.grid(row=1, column=1, sticky="nw", padx=(5, 10), pady=5)

        self._tbl_frame = tk.Frame(right)
        self._tbl_frame.pack(anchor="w")

        hdr = tk.Frame(self._tbl_frame)
        hdr.pack(fill="x")
        for label, w in [("PID", 6), ("Arrival", 8), ("Burst", 8), ("Priority", 8)]:
            tk.Label(hdr, text=label, font=("TkDefaultFont", 9, "bold"),
                     width=w, anchor="w").pack(side="left")

        self._body = tk.Frame(self._tbl_frame)
        self._body.pack(fill="x")

        tk.Label(right, text="Gantt Chart:").pack(anchor="w", pady=(8, 0))
        self._canvas = tk.Canvas(right, width=520, height=60, bg="white",
                                 highlightthickness=1, highlightbackground="gray")
        self._canvas.pack(anchor="w")

        tk.Label(right, text="Results:").pack(anchor="w", pady=(8, 0))
        self._out = tk.Text(right, width=66, height=12, font=("Courier New", 9),
                            state="disabled", relief="sunken", bd=1)
        self._out.pack(anchor="w")

    # --- process row management -------------------------------------------

    def _set_rows(self, n):
        n = max(self.MIN_PROCS, n)
        self._cnt_lbl.config(text=str(n))

        # save whatever the user typed so we don't lose it on resize
        saved = []
        for r in self._rows:
            saved.append({k: r[k].get() for k in ("pid", "arrival", "burst", "priority")})
            r["frame"].destroy()
        self._rows.clear()

        need_p = "Priority" in self._algo.get()
        for i in range(n):
            prev = saved[i] if i < len(saved) else {}
            f  = tk.Frame(self._body)
            f.pack(fill="x")
            pv = tk.StringVar(value=prev.get("pid",      f"P{i+1}"))
            av = tk.StringVar(value=prev.get("arrival",  "0"))
            bv = tk.StringVar(value=prev.get("burst",    ""))
            rv = tk.StringVar(value=prev.get("priority", str(i+1)))

            for var, w in [(pv, 6), (av, 8), (bv, 8)]:
                tk.Entry(f, textvariable=var, width=w).pack(side="left", padx=(0, 2))

            # priority column stays editable regardless — just greyed out when unused
            pe = tk.Entry(f, textvariable=rv, width=8)
            pe.pack(side="left")

            self._rows.append({"frame": f, "pid": pv, "arrival": av,
                                "burst": bv, "priority": rv, "_pe": pe})

        self._apply_priority_style()

    def _refresh_controls(self):
        need_q = "Round Robin" in self._algo.get()
        need_p = "Priority"    in self._algo.get()

        if need_q: self._qframe.grid()
        else:      self._qframe.grid_remove()

        if need_p: self._pnote.grid()
        else:      self._pnote.grid_remove()

        self._apply_priority_style()

    def _apply_priority_style(self):
        """Grey out the priority column visually when the chosen algorithm ignores it."""
        using_priority = "Priority" in self._algo.get()
        for r in self._rows:
            if using_priority:
                r["_pe"].config(fg="black", bg="white")
            else:
                r["_pe"].config(fg="#888888", bg="#f0f0f0")

    # --- parse inputs & dispatch to algorithm ----------------------------

    def _run(self):
        need_p = "Priority"    in self._algo.get()
        need_q = "Round Robin" in self._algo.get()
        procs  = []

        for i, r in enumerate(self._rows):
            pid = r["pid"].get().strip()
            if not pid:
                return messagebox.showerror("Error", f"Row {i+1}: PID can't be blank.")

            try:
                arr = int(r["arrival"].get())
                bst = int(r["burst"].get())
                if arr < 0 or bst < 1:
                    raise ValueError
            except ValueError:
                return messagebox.showerror("Error", f"{pid}: Arrival must be >= 0, Burst >= 1.")

            pri = None
            pri_str = r["priority"].get().strip()
            if pri_str:
                try:
                    pri = int(pri_str)
                    if pri < 1:
                        raise ValueError
                except ValueError:
                    if need_p:
                        return messagebox.showerror("Error", f"{pid}: Priority must be a whole number >= 1.")
                    pri = None
            elif need_p:
                return messagebox.showerror("Error", f"{pid}: This algorithm needs a priority value.")

            procs.append({"pid": pid, "arrival": arr, "burst": bst, "priority": pri, "i": i})

        q = None
        if need_q:
            try:
                q = int(self._quantum.get())
                if q < 1: raise ValueError
            except ValueError:
                return messagebox.showerror("Error", "Time Quantum must be a whole number >= 1.")

        algo = self._algo.get()
        if   algo == "FCFS":                      g, wt, tat = fcfs(procs)
        elif algo == "SJF (Non-preemptive)":      g, wt, tat = sjf(procs)
        elif algo == "SRT (Preemptive)":          g, wt, tat = srt(procs)
        elif algo == "Round Robin":               g, wt, tat = rr(procs, q)
        elif algo == "Priority (Non-preemptive)": g, wt, tat = priority_np(procs)
        elif algo == "Priority + Round Robin":    g, wt, tat = priority_rr(procs, q)
        else:
            return  # shouldn't happen but just in case the combobox grows

        self._draw_gantt(g)
        self._show_results(algo, procs, wt, tat, q)

    # --- gantt rendering --------------------------------------------------

    def _draw_gantt(self, gantt):
        c = self._canvas
        c.delete("all")

        total = gantt[-1][2] - gantt[0][1]
        if not total:
            return  # edge case: zero-length schedule (single 0-burst process etc.)

        W, PAD = 520, 8
        BAR_Y, BAR_H = 6, 32

        def to_x(t):
            return PAD + (t - gantt[0][1]) / total * (W - 2 * PAD)

        for pid, s, e in gantt:
            x0, x1 = to_x(s), to_x(e)
            c.create_rectangle(x0, BAR_Y, x1, BAR_Y + BAR_H, outline="black")
            if x1 - x0 > 12:
                c.create_text((x0 + x1) / 2, BAR_Y + BAR_H / 2,
                              text=pid, font=("TkDefaultFont", 8))

        # tick marks — avoid drawing duplicates at the same x position
        seen = set()
        for _, s, e in gantt:
            for t in (s, e):
                if t in seen:
                    continue
                seen.add(t)
                xp = to_x(t)
                c.create_line(xp, BAR_Y + BAR_H, xp, BAR_Y + BAR_H + 6)
                c.create_text(xp, BAR_Y + BAR_H + 14, text=str(t), font=("TkDefaultFont", 7))

    # --- results text area ------------------------------------------------

    def _show_results(self, algo, procs, wt, tat, q=None):
        out = self._out
        out.config(state="normal")
        out.delete("1.0", "end")

        heading = algo + (f" (q={q})" if q else "")
        out.insert("end", f"Algorithm: {heading}\n\n")
        out.insert("end", f"{'PID':<8}{'Arrival':>8}{'Burst':>7}{'Priority':>10}{'WT':>6}{'TAT':>7}\n")
        out.insert("end", "-" * 46 + "\n")

        for p in procs:
            pri_str = str(p["priority"]) if p["priority"] is not None else "-"
            out.insert("end",
                f"{p['pid']:<8}{p['arrival']:>8}{p['burst']:>7}"
                f"{pri_str:>10}{wt[p['pid']]:>6}{tat[p['pid']]:>7}\n"
            )

        out.insert("end", "-" * 46 + "\n")
        out.insert("end", f"Average WT  : {sum(wt.values()) / len(wt):.2f}\n")
        out.insert("end", f"Average TAT : {sum(tat.values()) / len(tat):.2f}\n")
        out.config(state="disabled")

    def _clear(self):
        self._canvas.delete("all")
        self._out.config(state="normal")
        self._out.delete("1.0", "end")
        self._out.config(state="disabled")


if __name__ == "__main__":
    App().mainloop()