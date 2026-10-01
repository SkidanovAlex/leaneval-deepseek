/-
# LinnikContract2 — CarryOver.lean

**Which round-1 results are re-established, and how.**

Everything under `Submission/Work/LinnikContract/`, `LinnikAreas/`, `Work/A7/` and
`ZeroFreeTables/` that is *proved* and does not depend on the height range of `λ₁` is carried over
here, with its statement rewritten in the round-2 vocabulary where that vocabulary changed
(`lamOf`, `zeroMult`, `IsZ`, `lamOf`-based definitions and the three tables are *definitionally*
round 1's; see `Bridge.lean`).  The items:

* `area5` — **`Area5` (HB Lemma 13.3, the per-character certificate) is proved** in round 2 as
  well, by transporting `Work.LinnikAreas.area5` (`PerCharCert`, `Area1` and `Bfun`/`boxAbs` are
  unchanged, so this is a definitional transport, not a new proof).
* `area7` — **re-proved** from scratch against the round-2 contract in
  `Submission.Work.LinnikContract2.A7.Area7` (`IsMin1`, `D2` and `HBNumbering` all changed, so
  the round-1 proof is *not* transportable; the §§14–15 machinery beneath it is reused verbatim).
* `linnik_of_areas` — the composition, re-proved in `Compose.lean`.
* the round-1 *interface* lemmas about the unchanged definitions (`isZ_lambda_nonneg`,
  `isZ_primitive_facts`, `box_api`, `Bfun_pos`, `Hk_norm`, `F2_norm_le_re`, `F2_eq_exp_sinh`,
  `norm_sinh_sq`).
* the round-1 *numerical certificate* (`Work.LinnikContract.numerics_summary` and the
  `lemma151*`/`margin*` family; worst total `995578/1000000`, margin `4422/1000000`).
* the round-1 *satisfiability* facts (`area1_hyps_sat`, `area2_hyps_sat`, `area5_hyps_sat`,
  `area7_hyps_sat`, `lamMax_pos`, `siegelZero_char_le3`) and the *table shape* facts
  (`rows15q_shape_cover`, `rows14q_shape_cover`, `table13q_shape`).

`Bridge.lean` records the definitional transports; this file records the *proved results*.
-/
import Submission.Work.LinnikContract2.Defs
import Submission.Work.LinnikContract.Tables
import Submission.Work.LinnikContract2.API
import Submission.Work.LinnikContract2.Bridge
import Submission.Work.LinnikAreas.area5
import Submission.Work.LinnikContract.API.isZ_lambda_nonneg
import Submission.Work.LinnikContract.API.isZ_primitive_facts
import Submission.Work.LinnikContract.API.box_api
import Submission.Work.LinnikContract.API.Bfun_pos
import Submission.Work.LinnikContract.API.Hk_norm
import Submission.Work.LinnikContract.API.F2_norm_le_re
import Submission.Work.LinnikContract.API.F2_eq_exp_sinh
import Submission.Work.LinnikContract.API.norm_sinh_sq
import Submission.Work.LinnikContract.Numerics
import Submission.Work.LinnikContract.Sat.area1_hyps_sat
import Submission.Work.LinnikContract.Sat.area2_hyps_sat
import Submission.Work.LinnikContract.Sat.area5_hyps_sat
import Submission.Work.LinnikContract.Sat.area7_hyps_sat
import Submission.Work.LinnikContract.Sat.lamMax_pos
import Submission.Work.LinnikContract.Sat.siegelZero_char_le3
import Submission.Work.LinnikContract.Tables.rows15q_shape_cover
import Submission.Work.LinnikContract.Tables.rows14q_shape_cover
import Submission.Work.LinnikContract.Tables.table13q_shape

set_option linter.unusedVariables false

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikContract2

/-! ## AREA 5 (proved in round 1, transported) -/

/-- **AREA 5 (round 2), proved.**  HB Lemma 13.3, uniform in `λ ∈ [0,R]`: transported from the
round-1 proof `Work.LinnikAreas.area5`, since `Area1`, `PerCharCert`, `boxAbs`, `Bfun`, `IsZ` and
`lamOf` are unchanged between the editions. -/
theorem area5 : Area5 := Work.LinnikAreas.area5

/-! ## The interface lemmas about the unchanged definitions -/

/-- A working-region zero has `λ ≥ 0` (round 1's `API.isZ_lambda_nonneg`; uses the proved
critical-strip location of the zeros). -/
theorem isZ_lambda_nonneg {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q} {ρ : ℂ}
    (h : IsZ χ ρ) : 0 ≤ lamOf q ρ := Work.LinnikContract.API.isZ_lambda_nonneg hq h

/-- A working-region zero of a non-principal character is a zero of the completed L-function of
a primitive non-trivial character (round 1's `API.isZ_primitive_facts`). -/
theorem isZ_primitive_facts {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {ρ : ℂ}
    (h : IsZ χ ρ) : ∃ (N : ℕ) (hN : NeZero N) (ψ : DirichletCharacter ℂ N),
      ψ ≠ 1 ∧ ψ.IsPrimitive ∧ @DirichletCharacter.completedLFunction N hN ψ ρ = 0 :=
  Work.LinnikContract.API.isZ_primitive_facts h

/-- `InBox` is monotone in `R`, `Ncount` is monotone in `λ`, and `boxAbs ≥ 0`
(round 1's `API.box_api`). -/
theorem box_api :
    (∀ (q : ℕ) {R R' : ℝ}, R ≤ R' → ∀ ρ : ℂ, InBox q R ρ → InBox q R' ρ) ∧
    (∀ (q : ℕ) [NeZero q] {lam lam' : ℝ}, lam ≤ lam' → Ncount q lam ≤ Ncount q lam') ∧
    (∀ (q : ℕ) [NeZero q] (K R : ℝ) (χ : DirichletCharacter ℂ q), 0 ≤ boxAbs q K R χ) :=
  Work.LinnikContract.API.box_api

/-- `B(λ) > 0` for `K > 0`, `λ > 0` (round 1's `API.Bfun_pos`). -/
theorem Bfun_pos {K lam : ℝ} (hK : 0 < K) (hlam : 0 < lam) : 0 < Bfun K lam :=
  Work.LinnikContract.API.Bfun_pos hK hlam

/-- `‖Hk L K z‖ = e^{-(L-2K) Re z} ‖F2 K z‖` (round 1's `API.Hk_norm`). -/
theorem Hk_norm (L K : ℝ) (z : ℂ) : ‖Hk L K z‖ = Real.exp (-(L - 2*K) * z.re) * ‖F2 K z‖ :=
  Work.LinnikContract.API.Hk_norm L K z

/-- `‖F₂ K (σ + it)‖ ≤ ‖F₂ K σ‖` for `σ > 0` (round 1's `API.F2_norm_le_re`). -/
theorem F2_norm_le_re (K : ℝ) (hK : 0 < K) (z : ℂ) (hz : 0 < z.re) :
    ‖F2 K z‖ ≤ ‖F2 K ((z.re : ℂ))‖ := Work.LinnikContract.API.F2_norm_le_re K hK z hz

/-- `F₂` in terms of `sinh` (round 1's `API.F2_eq_exp_sinh`). -/
theorem F2_eq_exp_sinh (K : ℝ) (hK : K ≠ 0) (z : ℂ) (hz : z ≠ 0) :
    F2 K z = (K:ℂ) ^ 2 * Complex.exp (-(K:ℂ) * z) *
      (Complex.sinh ((K:ℂ) * z / 2) / ((K:ℂ) * z / 2)) ^ 2 :=
  Work.LinnikContract.API.F2_eq_exp_sinh K hK z hz

/-- `‖sinh z‖² = sinh² (Re z) + sin² (Im z)` (round 1's `API.norm_sinh_sq`). -/
theorem norm_sinh_sq (z : ℂ) :
    ‖Complex.sinh z‖ ^ 2 = Real.sinh z.re ^ 2 + Real.sin z.im ^ 2 :=
  Work.LinnikContract.API.norm_sinh_sq z

/-! ## The rational tables (round 1's `Tables.tables_coe`, unchanged) -/

/-- **The round-2 tables are round-1's rational data**, coerced: `rows15`, `rows14`, `table13` are
the images of the explicit ℚ lists `rows15q`, `rows14q`, `table13q`.  (Round-1 deliverable item 5:
every numerical input of the areas is an explicit rational parameter.  The statement is round 1's,
whose right-hand sides are *definitionally* round-2's tables; `Bridge.lean` records that.) -/
theorem tables_coe :
    Work.LinnikContract.rows15q.map (fun r =>
        ((r.1 : ℝ), (r.2.1 : ℝ), (r.2.2.1 : ℝ), (r.2.2.2.1 : ℝ), (r.2.2.2.2 : ℝ))) = rows15 ∧
    Work.LinnikContract.rows14q.map (fun r =>
        ((r.1 : ℝ), (r.2.1 : ℝ), (r.2.2 : ℝ))) = rows14 ∧
    Work.LinnikContract.table13q.map (fun e =>
        ((e.1 : ℝ), (e.2.1 : ℝ), e.2.2)) = table13 :=
  Work.LinnikContract.tables_coe

/-! ## The numerical certificate (round 1's `Numerics.lean`, unchanged) -/

/-- The numerical certificate of §4: every certified §15 total is `< 1` and `≤ worstTotal`, every
HB-printed total `≤ worstTotalHB`, every §14 lower bound `≥ 288/1000`, and the recorded margins
are `4422/1000000` (the frozen tables) and `5579/1000000` (HB's printed tables); `worstTotal` is
`995578/1000000` and `worstTotalHB` is `994421/1000000`. -/
theorem numerics_summary :
    (∀ t ∈ Work.LinnikContract.lemma151Totals, t < 1) ∧
    (∀ t ∈ Work.LinnikContract.lemma151Totals, t ≤ Work.LinnikContract.worstTotal) ∧
    (∀ t ∈ Work.LinnikContract.lemma151TotalsHB, t ≤ Work.LinnikContract.worstTotalHB) ∧
    (∀ t ∈ Work.LinnikContract.lemma141Lowers, (288:ℚ)/1000 ≤ t) ∧
    (∀ t ∈ Work.LinnikContract.lemma141Tiny, 0 < t) ∧
    ((1 : ℚ) - Work.LinnikContract.worstTotal = 4422/1000000) ∧
    ((1 : ℚ) - Work.LinnikContract.worstTotalHB = 5579/1000000) :=
  Work.LinnikContract.numerics_summary

/-! ## Satisfiability and table shapes (round 1, unchanged) -/

/-- **AREA 1 is not vacuous**: a non-degenerate instance strictly inside the Burgess range. -/
theorem area1_hyps_sat :
    ∃ (k : ℕ) (ε' σ t : ℝ) (N : ℕ), 3 ≤ k ∧ 0 < ε' ∧ 2 ≤ N ∧
      (∃ χ : DirichletCharacter ℂ N, χ ≠ 1) ∧
      (1 - 1/(k:ℝ) ≤ σ ∧ σ ≤ 1 + Real.log (Real.log (N:ℝ)) / Real.log (N:ℝ)) ∧
      (1 - 1/(k:ℝ) < σ ∧ σ < 1 + Real.log (Real.log (N:ℝ)) / Real.log (N:ℝ)) :=
  Work.LinnikContract.Sat.area1_hyps_sat

/-- **AREA 2 is not vacuous**: `(3/10)² - ε > 0` and the box is inhabited at `ρ = 1` while
excluding `ρ = -1`. -/
theorem area2_hyps_sat :
    ∃ (ε R : ℝ) (q₀ q a : ℕ), 0 < ε ∧ 0 < (3/10:ℝ)^2 - ε ∧ 0 < R ∧ q₀ ≤ q ∧ 2 ≤ q ∧
      a.Coprime q ∧ a < q ∧ InBox q R (1 : ℂ) ∧ ¬ InBox q R (-1 : ℂ) :=
  Work.LinnikContract.Sat.area2_hyps_sat

/-- **AREA 5 is not vacuous**: `K²(B(λ) + η) > 0` for all admissible parameters. -/
theorem area5_hyps_sat :
    (∃ K R η lam : ℝ, 0 < K ∧ K ≤ 1 ∧ 0 < R ∧ 0 < η ∧ 0 ≤ lam ∧ lam ≤ R ∧ lam = R ∧
      0 < Bfun K lam ∧ 0 < K ^ 2 * (Bfun K lam + η)) ∧
    ∀ (K lam η : ℝ), 0 < K → 0 ≤ lam → 0 < η → 0 < K ^ 2 * (Bfun K lam + η) :=
  Work.LinnikContract.Sat.area5_hyps_sat

/-- **AREA 7 is not vacuous**: `(3/10)² - η > 0` for every `η < (3/10)²`, and the recorded
margins `56/10000`, `44/10000` are positive. -/
theorem area7_hyps_sat :
    (∀ η : ℝ, 0 < η → η < ((3:ℝ)/10)^2 → 0 < ((3:ℝ)/10)^2 - η) ∧
    (0 < ((3:ℝ)/10)^2 - (56:ℝ)/10000) ∧
    (0 < ((3:ℝ)/10)^2 - (44:ℝ)/10000) ∧
    ((9944:ℝ)/10000 + (56:ℝ)/10000 = 1) ∧
    ((9956:ℝ)/10000 + (44:ℝ)/10000 = 1) ∧
    ((9944:ℝ)/10000 < 1) ∧ ((9956:ℝ)/10000 < 1) :=
  Work.LinnikContract.Sat.area7_hyps_sat

/-- `λ₀ = (1/3) log log log q > 0` for all large `q`. -/
theorem lamMax_pos : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → 0 < lamMax q :=
  Work.LinnikContract.Sat.lamMax_pos

/-- `SiegelZero q lamS` forces `q ≥ 2`, and a non-principal real character exists at `q = 3`
(so `SiegelCase` is not vacuous on the character side). -/
theorem siegelZero_char_le3 :
    (∃ χ : DirichletCharacter ℂ 3, χ ≠ 1 ∧ χ ^ 2 = 1) ∧
    (∀ (q : ℕ) [NeZero q] {lamS : ℝ}, SiegelZero q lamS → 2 ≤ q) :=
  Work.LinnikContract.Sat.siegelZero_char_le3

/-- The §15 rows have `lo < hi`, lie in `[0.348, 0.6]`, have positive entries, and cover the whole
range `[0.348, 0.6]`. -/
theorem rows15q_shape_cover :
    (∀ r ∈ Work.LinnikContract.rows15q, r.1 < r.2.1 ∧ (348:ℚ)/1000 ≤ r.1 ∧
        r.2.1 ≤ (6:ℚ)/10 ∧ 0 < r.2.2.1 ∧ 0 < r.2.2.2.1 ∧ 0 < r.2.2.2.2) ∧
    (∀ x : ℚ, (348:ℚ)/1000 ≤ x → x ≤ (6:ℚ)/10 →
      ∃ r ∈ Work.LinnikContract.rows15q, r.1 ≤ x ∧ x ≤ r.2.1) :=
  Work.LinnikContract.Tables.rows15q_shape_cover

/-- The §14 rows are non-degenerate and cover `(0, 0.348]`. -/
theorem rows14q_shape_cover :
    (∀ r ∈ Work.LinnikContract.rows14q, r.1 < r.2.1 ∧ r.2.1 ≤ (348:ℚ)/1000 ∧ 0 < r.2.2) ∧
    (∀ x : ℚ, 0 < x → x ≤ (348:ℚ)/1000 →
      ∃ r ∈ Work.LinnikContract.rows14q, r.1 ≤ x ∧ x ≤ r.2.1) :=
  Work.LinnikContract.Tables.rows14q_shape_cover

/-- Table 13 is well formed: `λ₁ ∈ [0.348, 0.58]`, `λ ∈ [0.8, 1.325]`, `N₀ > 0`, and `N₀` is
non-decreasing in `λ` inside each `λ₁`-column. -/
theorem table13q_shape :
    (∀ e ∈ Work.LinnikContract.table13q, (348:ℚ)/1000 ≤ e.2.1 ∧ e.2.1 ≤ (58:ℚ)/100 ∧
      (8:ℚ)/10 ≤ e.1 ∧ e.1 ≤ (1325:ℚ)/1000 ∧ 0 < e.2.2) ∧
    (∀ e ∈ Work.LinnikContract.table13q, ∀ e' ∈ Work.LinnikContract.table13q,
      e.2.1 = e'.2.1 → e.1 ≤ e'.1 → e.2.2 ≤ e'.2.2) :=
  Work.LinnikContract.Tables.table13q_shape

end Work.LinnikContract2
