import Mathlib
import Submission.Work.BW.HilbSerreDefs
import Submission.Work.BW.finiteDim_vars_zero
import Submission.Work.BW.kFun_zero_eq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The empty-index-case of the multigraded Hilbert–Serre theorem

If every variable `X v` (`v : Fin (N+1) × Fin 2`) annihilates the `MR N`-module `M`, the
`ℤ^{N+1}`-grading of `M` is necessarily given by a polynomial: the Hilbert function
`u ↦ dim_ℂ (piece u)` agrees with `kFun N (fun _ => 0) P` for the polynomial `P` whose
`D`-th coefficient (`D ∈ ℕ^{N+1}`) is the dimension of `piece (castF D)`.
-/

namespace Work.BW

open MvPolynomial

theorem hilb_serre_empty {N : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
    [Module (MR N) M] [IsScalarTower ℂ (MR N) M] (piece : (Fin (N + 1) →₀ ℤ) → Submodule ℂ M)
    (hg : IsGrading N piece) (hfin : Module.Finite (MR N) M)
    (hfd : ∀ u, Module.Finite ℂ ↥(piece u))
    (h : ∀ v : Fin (N + 1) × Fin 2, ∀ m : M, (MvPolynomial.X v : MR N) • m = 0) :
    ∃ P : MvPolynomial (Fin (N + 1)) ℚ,
      ∀ u, (Module.finrank ℂ ↥(piece u) : ℚ) = kFun N (fun _ => 0) P u := by
  -- Since all variables kill `M`, the module is finite dimensional over `ℂ`.
  letI : FiniteDimensional ℂ M := finiteDim_vars_zero hfin h
  classical
  -- The (finite) set of multidegrees carrying a non-zero piece.
  let S : Finset (Fin (N + 1) →₀ ℤ) := (setOf_ne_bot_finite piece hg.isInternal).toFinset
  -- The polynomial whose coefficients are the dimensions of the pieces.
  let P : MvPolynomial (Fin (N + 1)) ℚ :=
    ∑ u ∈ S, (Module.finrank ℂ ↥(piece u) : ℚ) • MvPolynomial.monomial (HilbSerre.toNatF u) 1
  have hS_mem : ∀ u : Fin (N + 1) →₀ ℤ, u ∈ S ↔ piece u ≠ ⊥ := by
    intro u
    simp only [S]
    rw [Set.Finite.mem_toFinset]
    simp
  -- Every non-zero piece has non-negative multidegree.
  have hS_nonneg : ∀ u ∈ S, ∀ i, 0 ≤ u i := by
    intro u hu i
    by_contra hc
    rw [not_le] at hc
    exact (hS_mem u).mp hu (hg.eq_bot_of_neg u ⟨i, hc⟩)
  -- The coefficient of `P` at `toNatF u` is the dimension of `piece u`.
  have hcoeff : ∀ u, (∀ i, 0 ≤ u i) →
      P.coeff (HilbSerre.toNatF u) = (Module.finrank ℂ ↥(piece u) : ℚ) := by
    intro u hu
    have hstep : ∀ w ∈ S, (HilbSerre.toNatF w = HilbSerre.toNatF u) ↔ w = u := by
      intro w hw
      constructor
      · intro hwu
        have h1 : castF (HilbSerre.toNatF w) = castF (HilbSerre.toNatF u) := by rw [hwu]
        rwa [HilbSerre.castF_toNatF w (hS_nonneg w hw), HilbSerre.castF_toNatF u hu] at h1
      · intro hwu; rw [hwu]
    have hcalc : P.coeff (HilbSerre.toNatF u)
        = ∑ w ∈ S, (Module.finrank ℂ ↥(piece w) : ℚ) *
            (if HilbSerre.toNatF w = HilbSerre.toNatF u then 1 else 0) := by
      simp only [P]
      rw [MvPolynomial.coeff_sum]
      refine Finset.sum_congr rfl (fun w hw => ?_)
      rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial]
      simp [smul_eq_mul]
    rw [hcalc]
    have hcalc2 : ∑ w ∈ S, (Module.finrank ℂ ↥(piece w) : ℚ) *
          (if HilbSerre.toNatF w = HilbSerre.toNatF u then 1 else 0)
        = ∑ w ∈ S, (if w = u then (Module.finrank ℂ ↥(piece w) : ℚ) else 0) := by
      refine Finset.sum_congr rfl (fun w hw => ?_)
      by_cases hwu : HilbSerre.toNatF w = HilbSerre.toNatF u
      · have h' : w = u := (hstep w hw).mp hwu
        simp [hwu, h']
      · have h' : w ≠ u := fun hh => hwu ((hstep w hw).mpr hh)
        simp [hwu, h']
    rw [hcalc2, Finset.sum_ite_eq']
    by_cases huS : u ∈ S
    · rw [if_pos huS]
    · rw [if_neg huS]
      have : piece u = ⊥ := by
        by_contra hne
        exact huS ((hS_mem u).mpr hne)
      rw [this, finrank_bot]
      norm_num
  refine ⟨P, ?_⟩
  intro u
  rw [kFun_zero_eq P u]
  by_cases hu : ∀ i, 0 ≤ u i
  · rw [if_pos hu]; exact (hcoeff u hu).symm
  · rw [if_neg hu]
    have hneg : ∃ i, u i < 0 := by
      rw [not_forall] at hu
      obtain ⟨i, hi⟩ := hu
      exact ⟨i, lt_of_not_ge hi⟩
    rw [hg.eq_bot_of_neg u hneg, finrank_bot]
    norm_num

end Work.BW
