import Mathlib
import Submission.ModelStarFamily

/-!
# ModelStarExists -- the KKM output: a gap vector with all tips `≥ 4^(1/s)`

The single topological input of the "(EX)" route to Dubinin's inequality is the
KKM lemma for closed subsets of the standard simplex.  This module isolates the
application: **for every weight vector `r` (`0 < r k`, `Σ r k = 1`) there is a gap
vector `g` in the simplex all of whose tips are `≥ 4^(1/s)`**, from

  * closedness of `{g ∈ Simp : c ≤ tip r g j}` (`isClosed_tip_ge`),
  * Konyagin–Lev `∃ j, 4^(1/s) ≤ tip r g j` (`exists_tip_ge_four_rpow_inv`),
  * face vanishing `tip r g j = 0` when `g j = 0` (`tip_eq_zero_of_gap_eq_zero`).

The KKM lemma itself is taken as an explicit hypothesis
(`exists_tip_all_ge_of_kkm`) so that this module typechecks independently; when
`Commons.Topology.Simplex.kkm_standardSimplex` lands it is a one-line corollary
(`exists_tip_all_ge`).

NOTE (used later): the conclusion forces `g j > 0` for ALL `j` — a vanishing gap
would make the `j`-th tip `0 < 4^(1/s)` — and positive gaps are exactly the
strictness the model-star hypotheses of
`Submission.ModelStarDominating.unit_case_of_dominating_modelStar` need.
-/

noncomputable section

open scoped Real BigOperators Topology
open Set Filter

namespace Submission.ModelStarExists

open Submission.ModelStarFamily

variable {s : ℕ}

/-- The KKM hypothesis, in the exact shape of
`Commons.Topology.Simplex.kkm_standardSimplex`. -/
def KKM : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (A : Fin n → Set (Fin n → ℝ)),
    (∀ i, IsClosed (A i)) →
    (∀ (I : Finset (Fin n)) (x : Fin n → ℝ), (∀ i, 0 ≤ x i) → (∑ i, x i = 1) →
      (∀ i, i ∉ I → x i = 0) → ∃ i ∈ I, x ∈ A i) →
    ∃ x : Fin n → ℝ, (∀ i, 0 ≤ x i) ∧ (∑ i, x i = 1) ∧ ∀ i, x ∈ A i

/-- **The KKM output.**  Given the KKM lemma, every weight vector admits a gap
vector all of whose tips are `≥ 4^(1/s)`. -/
theorem exists_tip_all_ge_of_kkm (hkkm : KKM) (hs : 0 < s) (r : Fin s → ℝ)
    (hr : ∀ k, 0 < r k) (hsum : (∑ k, r k) = 1) :
    ∃ g : Fin s → ℝ, g ∈ Simp ∧ ∀ j, (4 : ℝ) ^ (1 / (s : ℝ)) ≤ tip r g j := by
  classical
  have hcc : 0 < (4 : ℝ) ^ (1 / (s : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hclosed : ∀ j : Fin s, IsClosed
      {g : Fin s → ℝ | g ∈ Simp ∧ (4 : ℝ) ^ (1 / (s : ℝ)) ≤ tip r g j} :=
    fun j => isClosed_tip_ge hs r hr hsum hcc j
  have hsub : ∀ (I : Finset (Fin s)) (x : Fin s → ℝ), (∀ i, 0 ≤ x i) → (∑ i, x i = 1) →
      (∀ i, i ∉ I → x i = 0) →
      ∃ i ∈ I, x ∈ {g : Fin s → ℝ | g ∈ Simp ∧ (4 : ℝ) ^ (1 / (s : ℝ)) ≤ tip r g i} := by
    intro I x hx0 hxsum hxzero
    have hgx : x ∈ Simp := ⟨hx0, hxsum⟩
    obtain ⟨j, hj⟩ := exists_tip_ge_four_rpow_inv hs r hr hsum hgx
    refine ⟨j, ?_, hgx, hj⟩
    by_contra hjI
    have hxj : x j = 0 := hxzero j hjI
    have hz := tip_eq_zero_of_gap_eq_zero r hr (g := x) (j := j) hxj
    rw [hz] at hj
    linarith [hcc]
  obtain ⟨x, hx0, hxsum, hx⟩ := hkkm s hs
    (fun j => {g : Fin s → ℝ | g ∈ Simp ∧ (4 : ℝ) ^ (1 / (s : ℝ)) ≤ tip r g j})
    hclosed hsub
  exact ⟨x, ⟨hx0, hxsum⟩, fun j => (hx j).2⟩

/-- **The KKM solutions have strictly positive gaps.**  A vanishing gap would make
the corresponding tip `0 < 4^(1/s)`, and positive gaps are exactly the
strictness required by the model-star hypotheses of
`Submission.ModelStarDominating.unit_case_of_dominating_modelStar`. -/
theorem gap_pos_of_tips (hs : 0 < s) (r : Fin s → ℝ) (hr : ∀ k, 0 < r k)
    (hsum : (∑ k, r k) = 1) {g : Fin s → ℝ}
    (htips : ∀ j, (4 : ℝ) ^ (1 / (s : ℝ)) ≤ tip r g j) (k : Fin s) : 0 < g k := by
  by_contra hk
  have hz : tip r g k = 0 := tip_eq_zero_of_gap_nonpos r hr (le_of_not_gt hk)
  have hc : 0 < (4 : ℝ) ^ (1 / (s : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hk' := htips k
  rw [hz] at hk'
  linarith

end Submission.ModelStarExists
