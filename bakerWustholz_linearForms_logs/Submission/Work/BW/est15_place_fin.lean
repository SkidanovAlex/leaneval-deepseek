import Mathlib
import Submission.Work.BW.est15defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- At a finite place `w` of a number field, a finite sum is bounded by any nonnegative upper
bound of its summands: `w (∑_{i∈s} f i) ≤ B` whenever `0 ≤ B` and `w (f i) ≤ B` for `i ∈ s`.
This is the ultrametric (`max`) inequality iterated over the finset (no cardinality loss). -/
lemma est15_finplace_sum_le {L : Type*} [Field L] [NumberField L] (w : NumberField.FinitePlace L)
    {ι : Type*} (s : Finset ι) (f : ι → L) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ i ∈ s, w (f i) ≤ B) : w (∑ i ∈ s, f i) ≤ B := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hB
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (NumberField.FinitePlace.add_le w _ _).trans
        (max_le (h a (Finset.mem_insert_self a s))
          (ih (fun i hi => h i (Finset.mem_insert_of_mem hi))))

/-- Per-place bound at a *finite* place `w` for BW (15) at level `J`: the descended value `g^{(J)}`
is a finite sum `gKJ = ∑_λ p λ · coefKJ λ`, and at a non-archimedean place a finite sum is bounded
by the maximum of its summands (`est15_finplace_sum_le`). Hence, if every coefficient satisfies
`log (w (coefKJ λ)) ≤ Bcoef` and `gKJ ≠ 0`, then
`log (w (gKJ)) ≤ log (max_λ w (p λ)) + Bcoef`. -/
theorem est15_place_fin {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ}
    {α : Fin n → K} {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ}
    {α' : Fin r → K} {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    {J : ℕ} {μ : Fin r → ℕ} {t0 : ℕ} {t : Fin (r - 1) → ℕ} {s : ℤ} {Bcoef : ℝ}
    (w : NumberField.FinitePlace K)
    (hx : gKJ b k L ι α' (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) p J μ t0 t s ≠ 0)
    (hcoef : ∀ lm : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ),
      Real.log (w (coefKJ b k L ι α' (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) J t0 t s lm))
        ≤ Bcoef) :
    Real.log (w (gKJ b k L ι α' (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) p J μ t0 t s))
      ≤ Real.log (⨆ lm, w (p lm)) + Bcoef := by
  classical
  have hnonneg : ∀ x : K, 0 ≤ w x := fun x => apply_nonneg w x
  have hpos : ∀ x : K, 0 < w x ↔ x ≠ 0 := fun x => NumberField.FinitePlace.pos_iff
  set S : ℝ := ⨆ lm : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ), w (p lm) with hS
  have hSnn : 0 ≤ S := by
    rw [hS]; exact Real.iSup_nonneg (fun lm => hnonneg (p lm))
  have hbdd : BddAbove (Set.range (fun lm : AuxIdx r (acH K b v) (pD0 r (dK K) σ)
      (pDj r (dK K) σ) => w (p lm))) := (Set.finite_range _).bddAbove
  have hcoef' : ∀ lm : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ),
      w (coefKJ b k L ι α' (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) J t0 t s lm)
        ≤ Real.exp Bcoef := fun lm => Real.le_exp_of_log_le (hcoef lm)
  -- the non-archimedean maximality: `w (gKJ) ≤ (max_λ w (p λ)) · exp Bcoef`
  have hkey : w (gKJ b k L ι α' (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) p J μ t0 t s)
      ≤ S * Real.exp Bcoef := by
    rw [gKJ]
    refine est15_finplace_sum_le w Finset.univ _
      (mul_nonneg hSnn (Real.exp_pos Bcoef).le) (fun lm _ => ?_)
    by_cases hc : (∀ j, (lm.2.2 j : ℕ) % 2 ^ J = μ j)
    · rw [ite_eq_left hc, map_mul]
      exact mul_le_mul (le_ciSup hbdd lm) (hcoef' lm) (hnonneg _) hSnn
    · rw [ite_eq_right hc, map_zero]
      exact mul_nonneg hSnn (Real.exp_pos Bcoef).le
  have hwg : 0 < w (gKJ b k L ι α' (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ)
      p J μ t0 t s) := (hpos _).2 hx
  have hSpos : 0 < S := pos_of_mul_pos_left (lt_of_lt_of_le hwg hkey) (Real.exp_pos Bcoef).le
  calc Real.log (w (gKJ b k L ι α' (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ)
          p J μ t0 t s))
      ≤ Real.log (S * Real.exp Bcoef) := Real.log_le_log hwg hkey
    _ = Real.log S + Real.log (Real.exp Bcoef) := Real.log_mul hSpos.ne' (Real.exp_pos Bcoef).ne'
    _ = Real.log (⨆ lm, w (p lm)) + Bcoef := by rw [Real.log_exp, hS]

end Work.BW
