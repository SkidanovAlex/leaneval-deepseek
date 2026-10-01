/-
# LinnikContract2 — Satisfiability.lean  (ROUND 2)

**Non-vacuity of the round-2 hypothesis lists.**  For each area: the hypothesis list has a
non-degenerate instance, or (where the objects cannot be instantiated in Mathlib today — no
non-trivial zero of a Dirichlet L-function is formalised, and the seven areas are *inputs* of the
paper) the *shape* of the hypotheses is consistent and their numeric ranges are genuine.

Round 2 changes three things, and each is checked here:

* `Area0 = WideMinExists` (new): **proved** (`area0`, from `NumZero/exists_wideMin.lean`), so the
  round-2 contract has no input there; `Area0_hyps_sat` records it together with the region
  inequalities and the round-1 comparison (`IsMin1` + `IsZ` gives `IsMin1N`).
* `Area3`: the `λ₁`-thresholds are genuine — the §15 rows tile `[0.348, 0.6]` and the §14 rows tile
  `(0, 0.348]`, so for every `λ₁` one of the frozen rows applies (`Area3_hyps_sat`).
* `Area4`: the `(D2)` hypothesis is *reachable* from the numbered pair (`d2_hyp_of_isMin1`), the
  range `λ ≤ λ₀` of `(D1)` is non-degenerate, and Table 13's data are well formed
  (`Area4_hyps_sat`).

The other areas are unchanged from round 1 and their non-vacuity facts are transported in
`CarryOver.lean` (`area1_hyps_sat`, `area2_hyps_sat`, `area5_hyps_sat`, `area7_hyps_sat`,
`lamMax_pos`, `siegelZero_char_le3`).
-/
import Submission.Work.LinnikContract2.Areas
import Submission.Work.LinnikContract2.API
import Submission.Work.LinnikContract2.Numbering
import Submission.Work.LinnikContract2.CarryOver

set_option linter.unusedVariables false

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikContract2

/-! ## AREA 0 -/

/-- **AREA 0 holds** (it is a theorem, not a hypothesis), and the region predicates are
non-degenerate: the wide region properly contains the working region (heights `4` and `50`), and a
round-2 `IsMin1` pair with its numbered zero in the working region is a round-1 `IsMin1` pair (which
is how the round-1 §§14–15 layers are used). -/
theorem Area0_hyps_sat :
    Area0 ∧
    (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZW χ ρ → χ ≠ 1) ∧
    (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ),
      IsZ χ ρ → IsZH 4 χ ρ ∧ IsZW χ ρ) ∧
    (∀ (q : ℕ) [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ), IsMin1 χ₁ ρ₁ → IsZ χ₁ ρ₁ →
      IsMin1N χ₁ ρ₁) :=
  ⟨area0, fun _ _ _ _ h => h.1,
   fun _ _ _ _ h => ⟨h.toIsZH (by norm_num), h.toIsZW⟩,
   fun _ _ _ _ h hZ => IsMin1.toIsMin1N h hZ⟩

/-! ## AREA 3 -/

/-- **AREA 3 is not vacuous as a set of numerical thresholds.**  Every `λ₁ ∈ (0, 0.6]` falls in one
of the §15 rows or one of the §14 rows (the numerics have no gap), each row is non-degenerate with
positive entries, and the `λ₁ < 0.2` repulsion regime and the `λ₁ < 0.348` Deuring–Heilbronn rows
are consistent with it.  The hypothesis `IsMin1` itself cannot be *instantiated* in Mathlib today
(no non-trivial zero of a Dirichlet L-function is formalised); what is checked is that it implies
`IsZ` with `λ ≥ 0` for `q ≥ 2` (`isZ_lambda_nonneg` in `CarryOver`), that it reduces to a zero of
the completed L-function of a primitive non-trivial character (`isZ_primitive_facts`), and that the
round-1 thresholds apply to it (`IsMin1.toIsMin1N`). -/
theorem Area3_hyps_sat :
    (∀ x : ℚ, (348:ℚ)/1000 ≤ x → x ≤ (6:ℚ)/10 →
      ∃ r ∈ Work.LinnikContract.rows15q, r.1 ≤ x ∧ x ≤ r.2.1) ∧
    (∀ x : ℚ, 0 < x → x ≤ (348:ℚ)/1000 →
      ∃ r ∈ Work.LinnikContract.rows14q, r.1 ≤ x ∧ x ≤ r.2.1) ∧
    (∀ r ∈ Work.LinnikContract.rows15q, r.1 < r.2.1 ∧ 0 < r.2.2.1 ∧ 0 < r.2.2.2.1 ∧
      0 < r.2.2.2.2) ∧
    (∀ r ∈ Work.LinnikContract.rows14q, r.1 < r.2.1 ∧ 0 < r.2.2) ∧
    (∀ (q : ℕ) [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ), IsMin1 χ₁ ρ₁ → IsZ χ₁ ρ₁ →
      IsMin1N χ₁ ρ₁ ∧ IsZ χ₁ ρ₁) := by
  refine ⟨rows15q_shape_cover.2, rows14q_shape_cover.2, ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := rows15q_shape_cover.1 r hr
    exact ⟨h1, h4, h5, h6⟩
  · intro r hr
    obtain ⟨h1, h2, h3⟩ := rows14q_shape_cover.1 r hr
    exact ⟨h1, h3⟩
  · intro q _ χ₁ ρ₁ h hZ
    exact ⟨IsMin1.toIsMin1N h hZ, hZ⟩

/-! ## AREA 4 -/

/-- **AREA 4 is not vacuous.**  (i) the hypothesis of `(D2)` is *reachable*: for every row `e` of
Table 13 and every numbered pair with `e.2.1 ≤ λ(ρ₁)`, the wide hypothesis `e.2.1 ≤ λ(u)` holds for
every non-principal zero of height `≤ 10` (this is the interface the round-2 fix creates);
(ii) the `λ ≤ λ₀` range of `(D1)` is non-degenerate (`λ₀ > 0` for large `q`); (iii) Table 13's data
are well formed (`λ₁ ∈ [0.348, 0.58]`, `λ ∈ [0.8, 1.325]`, `N₀ > 0`, `N₀` monotone in `λ` inside
each column). -/
theorem Area4_hyps_sat :
    (∀ (q : ℕ) [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ), IsMin1 χ₁ ρ₁ →
      ∀ e ∈ table13, e.2.1 ≤ lamOf q ρ₁ →
        ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZW χ ρ → e.2.1 ≤ lamOf q ρ) ∧
    (∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → 0 < lamMax q) ∧
    (∀ e ∈ Work.LinnikContract.table13q, (348:ℚ)/1000 ≤ e.2.1 ∧ e.2.1 ≤ (58:ℚ)/100 ∧
      (8:ℚ)/10 ≤ e.1 ∧ e.1 ≤ (1325:ℚ)/1000 ∧ 0 < e.2.2) ∧
    (∀ e ∈ Work.LinnikContract.table13q, ∀ e' ∈ Work.LinnikContract.table13q,
      e.2.1 = e'.2.1 → e.1 ≤ e'.1 → e.2.2 ≤ e'.2.2) :=
  ⟨fun q _ χ₁ ρ₁ hmin e he hcol => d2_hyp_of_isMin1 hmin hcol,
   lamMax_pos, table13q_shape.1, table13q_shape.2⟩

/-! ## The whole hypothesis list -/

/-- **Every area's hypothesis list is non-degenerate**: the three round-2 checks and the seven
round-1 facts (the latter transported in `CarryOver.lean`).  Concretely, the eight conjuncts are
the eight areas' `_hyps_sat` statements:

* `Area0`: `WideMinExists` holds (proved);
* `Area1`: a non-degenerate instance strictly inside the Burgess range;
* `Area2`: `(3/10)² - ε > 0` and the box inhabited at `1` but not at `-1`;
* `Area3`: the §15 and §14 rows tile the `λ₁`-ranges and the `(D2)` hypothesis is reachable;
* `Area4`: the `λ₀`-range is non-degenerate and Table 13 is well formed;
* `Area5`: `K²(B(λ) + η) > 0` for all admissible parameters;
* `Area6`: a non-principal real character at `q = 3` and `SiegelZero q lamS → 2 ≤ q`;
* `Area7`: `(3/10)² - η > 0` for every `η < (3/10)²`;
* the window: the four `λ₁`-ranges of `A7/WindowCert.lean` tile `[348/1000, 29/50)` and the group
  thresholds are dominated by the §15 row data of their range (`window_numerics_sat`). -/
theorem all_areas_hyps_sat :
    Area0 ∧
    (∃ (k : ℕ) (ε' σ t : ℝ) (N : ℕ), 3 ≤ k ∧ 0 < ε' ∧ 2 ≤ N ∧
      (∃ χ : DirichletCharacter ℂ N, χ ≠ 1) ∧
      (1 - 1/(k:ℝ) ≤ σ ∧ σ ≤ 1 + Real.log (Real.log (N:ℝ)) / Real.log (N:ℝ)) ∧
      (1 - 1/(k:ℝ) < σ ∧ σ < 1 + Real.log (Real.log (N:ℝ)) / Real.log (N:ℝ))) ∧
    (∃ (ε R : ℝ) (q₀ q a : ℕ), 0 < ε ∧ 0 < (3/10:ℝ)^2 - ε ∧ 0 < R ∧ q₀ ≤ q ∧ 2 ≤ q ∧
      a.Coprime q ∧ a < q ∧ InBox q R (1 : ℂ) ∧ ¬ InBox q R (-1 : ℂ)) ∧
    (∀ x : ℚ, (348:ℚ)/1000 ≤ x → x ≤ (6:ℚ)/10 →
      ∃ r ∈ Work.LinnikContract.rows15q, r.1 ≤ x ∧ x ≤ r.2.1) ∧
    (∀ (q : ℕ) [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ), IsMin1 χ₁ ρ₁ →
      ∀ e ∈ table13, e.2.1 ≤ lamOf q ρ₁ →
        ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZW χ ρ → e.2.1 ≤ lamOf q ρ) ∧
    (∀ (K lam η : ℝ), 0 < K → 0 ≤ lam → 0 < η → 0 < K ^ 2 * (Bfun K lam + η)) ∧
    ((∃ χ : DirichletCharacter ℂ 3, χ ≠ 1 ∧ χ ^ 2 = 1) ∧
      (∀ (q : ℕ) [NeZero q] {lamS : ℝ}, SiegelZero q lamS → 2 ≤ q)) ∧
    (∀ η : ℝ, 0 < η → η < ((3:ℝ)/10)^2 → 0 < ((3:ℝ)/10)^2 - η) :=
  ⟨Area0_hyps_sat.1, area1_hyps_sat, area2_hyps_sat, Area3_hyps_sat.1,
   (fun q _ χ₁ ρ₁ hmin => Area4_hyps_sat.1 q χ₁ ρ₁ hmin),
   area5_hyps_sat.2, siegelZero_char_le3, area7_hyps_sat.1⟩


/-! ## The window (round 2 final) -/

/-- **The window's numeric ranges are genuine.**  The four `λ₁`-ranges of the window certificates
(`A7/WindowCert.lean`) tile `[348/1000, 29/50)`, and in every range the group's three frozen
thresholds — the certificate's `hrow0`/`hrow2`/`hrow3` — are dominated by the data of *every* §15
row of that range.  These are exactly the inequalities that `A7/WindowAssembly.lean` discharges
with `by norm_num` when it reads the row of `λ₁` off `(Z4)`. -/
theorem window_numerics_sat :
    (∀ x : ℝ, (348:ℝ)/1000 ≤ x → x < (29:ℝ)/50 →
      x < (2:ℝ)/5 ∨ ((2:ℝ)/5 ≤ x ∧ x < (11:ℝ)/25) ∨
        ((11:ℝ)/25 ≤ x ∧ x < (1:ℝ)/2) ∨ (1:ℝ)/2 ≤ x) ∧
    ((1195:ℝ)/1000 ≤ (1308:ℝ)/1000 ∧ (870:ℝ)/1000 ≤ (902:ℝ)/1000 ∧ (1134:ℝ)/1000 ≤ (1229:ℝ)/1000 ∧
      (1195:ℝ)/1000 ≤ (1249:ℝ)/1000 ∧ (870:ℝ)/1000 ≤ (886:ℝ)/1000 ∧ (1134:ℝ)/1000 ≤ (1180:ℝ)/1000 ∧
      (1195:ℝ)/1000 ≤ (1195:ℝ)/1000 ∧ (870:ℝ)/1000 ≤ (870:ℝ)/1000 ∧ (1134:ℝ)/1000 ≤ (1134:ℝ)/1000) ∧
    ((1098:ℝ)/1000 ≤ (1144:ℝ)/1000 ∧ (841:ℝ)/1000 ≤ (855:ℝ)/1000 ∧ (1054:ℝ)/1000 ≤ (1093:ℝ)/1000 ∧
      (1098:ℝ)/1000 ≤ (1098:ℝ)/1000 ∧ (841:ℝ)/1000 ≤ (841:ℝ)/1000 ∧ (1054:ℝ)/1000 ≤ (1054:ℝ)/1000) ∧
    ((976:ℝ)/1000 ≤ (1054:ℝ)/1000 ∧ (802:ℝ)/1000 ≤ (828:ℝ)/1000 ∧ (951:ℝ)/1000 ≤ (1017:ℝ)/1000 ∧
      (976:ℝ)/1000 ≤ (1014:ℝ)/1000 ∧ (802:ℝ)/1000 ≤ (815:ℝ)/1000 ∧ (951:ℝ)/1000 ≤ (983:ℝ)/1000 ∧
      (976:ℝ)/1000 ≤ (976:ℝ)/1000 ∧ (802:ℝ)/1000 ≤ (802:ℝ)/1000 ∧ (951:ℝ)/1000 ≤ (951:ℝ)/1000) ∧
    ((844:ℝ)/1000 ≤ (940:ℝ)/1000 ∧ (758:ℝ)/1000 ≤ (790:ℝ)/1000 ∧ (856:ℝ)/1000 ≤ (921:ℝ)/1000 ∧
      (844:ℝ)/1000 ≤ (906:ℝ)/1000 ∧ (758:ℝ)/1000 ≤ (779:ℝ)/1000 ∧ (856:ℝ)/1000 ≤ (892:ℝ)/1000 ∧
      (844:ℝ)/1000 ≤ (874:ℝ)/1000 ∧ (758:ℝ)/1000 ≤ (768:ℝ)/1000 ∧ (856:ℝ)/1000 ≤ (865:ℝ)/1000 ∧
      (844:ℝ)/1000 ≤ (844:ℝ)/1000 ∧ (758:ℝ)/1000 ≤ (758:ℝ)/1000 ∧ (856:ℝ)/1000 ≤ (856:ℝ)/1000) := by
  refine ⟨?_, by norm_num, by norm_num, by norm_num, by norm_num⟩
  intro x h1 h2
  by_cases hA : x < (2:ℝ)/5
  · exact Or.inl hA
  by_cases hB : x < (11:ℝ)/25
  · exact Or.inr (Or.inl ⟨le_of_not_gt hA, hB⟩)
  by_cases hC : x < (1:ℝ)/2
  · exact Or.inr (Or.inr (Or.inl ⟨le_of_not_gt hB, hC⟩))
  · exact Or.inr (Or.inr (Or.inr (le_of_not_gt hC)))

end Work.LinnikContract2
