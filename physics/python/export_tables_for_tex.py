#!/usr/bin/env python3
import csv
import math
import os
from collections import defaultdict

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
AUTOGEN_DIR = os.path.join(ROOT, "physics", "tex", "autogen")

INPUTS = {
    "quantum_dpi": "physics/artifacts/quantum_dpi_summary.csv",
    "bgk_summary": "physics/artifacts/bgk_summary.csv",
    "bgk_failure_modes": "physics/artifacts/bgk_failure_modes.csv",
    "les_route_mismatch": "physics/artifacts/les_route_mismatch.csv",
    "les_subgrid_term": "physics/artifacts/les_subgrid_term.csv",
    "gravity_backreaction": "physics/artifacts/gravity_backreaction.csv",
    "gravity_packaging": "physics/artifacts/gravity_packaging_mismatch.csv",
}


def fmt(x: float) -> str:
    return f"{x:.3g}"


def read_csv(path: str):
    with open(path, newline="") as f:
        return list(csv.DictReader(f))


def ensure_inputs():
    for rel in INPUTS.values():
        path = os.path.join(ROOT, rel)
        if not os.path.exists(path):
            raise SystemExit(f"Missing CSV: {rel}")


def write_table(path: str, caption: str, label: str, header: list, rows: list, small: bool = False):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        f.write("\\begin{table}[h]\n")
        f.write("  \\centering\n")
        f.write(f"  \\caption{{{caption}}}\n")
        f.write(f"  \\label{{{label}}}\n")
        if small:
            f.write("  \\small\n")
        f.write("  \\begin{tabular}{" + "l" * len(header) + "}\n")
        f.write("    \\toprule\n")
        f.write("    " + " & ".join(header) + " \\\ \n")
        f.write("    \\midrule\n")
        for row in rows:
            f.write("    " + " & ".join(row) + " \\\ \n")
        f.write("    \\bottomrule\n")
        f.write("  \\end{tabular}\n")
        f.write("\\end{table}\n")


def write_tabular(path: str, header: list, rows: list, small: bool = False):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        if small:
            f.write("\\small\n")
        f.write("\\begin{tabular}{" + "l" * len(header) + "}\n")
        f.write("  \\toprule\n")
        f.write("  " + " & ".join(header) + " \\\ \n")
        f.write("  \\midrule\n")
        for row in rows:
            f.write("  " + " & ".join(row) + " \\\ \n")
        f.write("  \\bottomrule\n")
        f.write("\\end{tabular}\n")

def table_quantum_dpi():
    rows = read_csv(os.path.join(ROOT, INPUTS["quantum_dpi"]))
    by_d = defaultdict(list)
    for r in rows:
        d = int(r["d"])
        by_d[d].append(r)
    out_rows = []
    for d in sorted(by_d):
        rs = by_d[d]
        trials_total = sum(int(r["trials"]) for r in rs)
        min_diff = min(float(r["min_diff"]) for r in rs)
        violations_total = sum(int(r["violations"]) for r in rs)
        # weighted mean of mean_diff by trials
        mean_diff = sum(float(r["mean_diff"]) * int(r["trials"]) for r in rs) / max(trials_total, 1)
        out_rows.append([
            str(d),
            str(trials_total),
            fmt(min_diff),
            fmt(mean_diff),
            str(violations_total),
        ])
    write_table(
        os.path.join(AUTOGEN_DIR, "table_quantum_dpi.tex"),
        "Quantum DPI summary.",
        "tab:quantum-dpi-summary",
        ["d", "trials", "min diff", "mean diff", "violations"],
        out_rows,
    )


def table_bgk_endpoints():
    rows = read_csv(os.path.join(ROOT, INPUTS["bgk_summary"]))
    by_tau = defaultdict(dict)
    for r in rows:
        tau = int(float(r["tau"]))
        omega = float(r["omega"])
        by_tau[tau][omega] = float(r["mean_delta"])
    out_rows = []
    for tau in [2, 5, 10]:
        m0 = by_tau.get(tau, {}).get(0.0)
        m1 = by_tau.get(tau, {}).get(1.0)
        if m0 is None or m1 is None:
            raise SystemExit(f"Missing omega endpoints for tau={tau} in bgk_summary.csv")
        out_rows.append([str(tau), fmt(m0), fmt(m1)])
    write_table(
        os.path.join(AUTOGEN_DIR, "table_bgk_endpoints.tex"),
        "BGK endpoint idempotence defect.",
        "tab:bgk-endpoints",
        ["tau", "mean delta (omega=0)", "mean delta (omega=1)"],
        out_rows,
    )


def table_bgk_failure_modes():
    rows = read_csv(os.path.join(ROOT, INPUTS["bgk_failure_modes"]))
    by_case = defaultdict(list)
    for r in rows:
        if int(float(r["tau"])) != 5:
            continue
        by_case[r["case_id"]].append(r)
    out_rows = []
    # FM1
    fm1 = by_case.get("FM1_low_omega_strong_gradient", [])
    if not fm1:
        raise SystemExit("Missing FM1 rows at tau=5")
    mean_delta = sum(float(r["delta"]) for r in fm1) / len(fm1)
    out_rows.append(["FM1", fmt(mean_delta), "--", "--", "--"])
    # FM2
    fm2 = by_case.get("FM2_wrong_equilibrium_family", [])
    if not fm2:
        raise SystemExit("Missing FM2 rows at tau=5")
    mean_uerr = sum(float(r["u_err"]) for r in fm2) / len(fm2)
    out_rows.append(["FM2", "--", fmt(mean_uerr), "--", "--"])
    # FM3
    fm3 = by_case.get("FM3_lens_missing_slow_mode", [])
    if not fm3:
        raise SystemExit("Missing FM3 rows at tau=5")
    mean_emiss = sum(float(r["e_err_missing"]) for r in fm3) / len(fm3)
    mean_eext = sum(float(r["e_err_extended"]) for r in fm3) / len(fm3)
    out_rows.append(["FM3", "--", "--", fmt(mean_emiss), fmt(mean_eext)])

    write_table(
        os.path.join(AUTOGEN_DIR, "table_bgk_failure_modes.tex"),
        "BGK failure modes summary.",
        "tab:bgk-failure-modes",
        ["case", "mean delta", "mean u err", "mean e err missing", "mean e err extended"],
        out_rows,
        small=True,
    )


def table_les_route_mismatch():
    rows = read_csv(os.path.join(ROOT, INPUTS["les_route_mismatch"]))
    by_sigma = defaultdict(float)
    for r in rows:
        sigma = float(r["sigma"])
        mismatch = float(r["mismatch_l2"])
        by_sigma[sigma] = max(by_sigma.get(sigma, 0.0), mismatch)
    out_rows = []
    for sigma in sorted(by_sigma):
        out_rows.append([fmt(sigma), fmt(by_sigma[sigma])])
    write_table(
        os.path.join(AUTOGEN_DIR, "table_les_route_mismatch.tex"),
        "LES route mismatch summary.",
        "tab:les-route-mismatch",
        ["sigma", "max mismatch"],
        out_rows,
    )
    write_tabular(
        os.path.join(AUTOGEN_DIR, "table_les_route_mismatch_tabular.tex"),
        ["sigma", "max mismatch"],
        out_rows,
        small=True,
    )


def table_les_subgrid_term():
    rows = read_csv(os.path.join(ROOT, INPUTS["les_subgrid_term"]))
    by_sigma = defaultdict(float)
    for r in rows:
        sigma = float(r["sigma"])
        tau_l2 = float(r["tau_l2"])
        by_sigma[sigma] = max(by_sigma.get(sigma, 0.0), tau_l2)
    out_rows = []
    for sigma in sorted(by_sigma):
        out_rows.append([fmt(sigma), fmt(by_sigma[sigma])])
    write_table(
        os.path.join(AUTOGEN_DIR, "table_les_subgrid_term.tex"),
        "LES subgrid term magnitude.",
        "tab:les-subgrid-term",
        ["sigma", "max tau\\_l2"],
        out_rows,
    )
    write_tabular(
        os.path.join(AUTOGEN_DIR, "table_les_subgrid_term_tabular.tex"),
        ["sigma", "max tau\\_l2"],
        out_rows,
        small=True,
    )


def table_gravity_backreaction():
    rows = read_csv(os.path.join(ROOT, INPUTS["gravity_backreaction"]))
    by_s = defaultdict(float)
    for r in rows:
        s = float(r["s"])
        abs_mismatch = abs(float(r["mismatch"]))
        by_s[s] = max(by_s.get(s, 0.0), abs_mismatch)
    out_rows = []
    for s in sorted(by_s):
        out_rows.append([fmt(s), fmt(by_s[s])])
    write_table(
        os.path.join(AUTOGEN_DIR, "table_gravity_backreaction.tex"),
        "Gravity backreaction mismatch.",
        "tab:gravity-backreaction",
        ["s", "max |mismatch|"],
        out_rows,
    )


def table_gravity_packaging():
    rows = read_csv(os.path.join(ROOT, INPUTS["gravity_packaging"]))
    by_s_route = defaultdict(float)
    by_s_idem = defaultdict(float)
    for r in rows:
        s = float(r["s"])
        by_s_route[s] = max(by_s_route.get(s, 0.0), float(r["delta_route"]))
        by_s_idem[s] = max(by_s_idem.get(s, 0.0), float(r["delta_closure_idem"]))
    out_rows = []
    for s in sorted(by_s_route):
        out_rows.append([fmt(s), fmt(by_s_route[s]), fmt(by_s_idem[s])])
    write_table(
        os.path.join(AUTOGEN_DIR, "table_gravity_packaging.tex"),
        "Gravity packaging mismatch.",
        "tab:gravity-packaging",
        ["s", "max delta\\_route", "max delta\\_closure"],
        out_rows,
    )


def main():
    ensure_inputs()
    os.makedirs(AUTOGEN_DIR, exist_ok=True)
    table_quantum_dpi()
    table_bgk_endpoints()
    table_bgk_failure_modes()
    table_les_route_mismatch()
    table_les_subgrid_term()
    table_gravity_backreaction()
    table_gravity_packaging()


if __name__ == "__main__":
    main()
