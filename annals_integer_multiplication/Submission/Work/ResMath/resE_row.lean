import Mathlib
import Submission.Work.ResMath.resE_defs
import Submission.Work.ResMath.Nmat_apply
import Submission.Work.ResMath.summable_Nsum
import Submission.Work.ResMath.summable_exp_neg_affine_sq
import Submission.Work.ResMath.quad_ineq

/-!
# The rows of `Nmat` as Gaussian series (paper Lemma 4.6)

`Work.ResMath.Nmat_mulVec_eq_tsum`: the `ℓ`-th row sum of `Nmat s t α` applied to a vector `u` is
the `ℤ`-indexed Gaussian series

`(N u)_ℓ = ∑_n exp(-π α² ((t(n-ℓ)/s + β_ℓ)² - β_n²)) u_{n mod s}`

of Harvey–van der Hoeven, *Integer multiplication in time* `O(n log n)`, §4.2, where `n = j + q s`
runs over `ℤ` using the bijection `Fin s × ℤ ≃ ℤ` (division with remainder).

We also record the pointwise size estimate for the summand `phi` that feeds Lemma 4.6.
-/

set_option maxHeartbeats 800000

namespace Work.ResMath

open HvdH

/-- The Gaussian factor `exp (-π α² (t q + t(j-ℓ)/s + β_ℓ)²)` of the `(j,q)` summand is summable
in `q`. -/
lemma summable_Egauss (s t α : ℕ) (hs : 0 < s) (hst : s < t) (hα : 0 < α) (ℓ j : Fin s) :
    Summable (fun q : ℤ => ((Real.exp (-(Real.pi * (α : ℝ) ^ 2 *
      ((t : ℝ) * (q : ℝ) + (t : ℝ) * ((j : ℤ) - (ℓ : ℤ)) / (s : ℝ)
        + betaI s t (ℓ : ℤ)) ^ 2)) : ℝ) : ℂ)) := by
  set x : ℝ := (t : ℝ) * ((j : ℤ) - (ℓ : ℤ)) / (s : ℝ) + betaI s t (ℓ : ℤ) with hx
  have ha : 0 < Real.pi * (α : ℝ) ^ 2 := by positivity
  have ht : 0 < t := by omega
  refine Summable.of_norm_bounded
    (g := fun q : ℤ => Real.exp (-(Real.pi * (α : ℝ) ^ 2) * (t * (q : ℝ) + x) ^ 2))
    (summable_exp_neg_affine_sq (Real.pi * (α : ℝ) ^ 2) x ha ht) ?_
  have hnrm : ∀ r : ℝ, ‖(((Real.exp r : ℝ)) : ℂ)‖ = Real.exp r := fun r =>
    (RCLike.norm_ofReal _).trans (abs_of_nonneg (Real.exp_nonneg _))
  intro q
  rw [hnrm]
  apply Real.exp_le_exp.mpr
  rw [hx]
  exact le_of_eq (by ring)

/-- The `(j,q)` summand of the entry formula is the `n = j + s q` summand of `phi`. -/
lemma Nsum_eq_phi (s t α : ℕ) (hs : 0 < s) (ℓ : Fin s) (u : Fin s → ℂ) (j : Fin s) (q : ℤ) :
    Nsum s t α ℓ u j q = phi s t α hs ℓ u ((j : ℤ) + s * q) := by
  have hm : modZ s hs ((j : ℤ) + s * q) = j := by
    rw [modZ_add_mul s hs (j : ℤ) q, modZ_eq_self s hs j]
  have hb : betaI s t ((j : ℤ) + s * q) = HvdH.betaR s t j := by
    rw [betaI_dvd_shift s t hs (j : ℤ) q, betaI_eq_betaR]
  have hA : (t : ℝ) * ((((j : ℤ) + s * q : ℤ) : ℝ) - (ℓ : ℝ)) / (s : ℝ) + betaI s t (ℓ : ℤ)
      = (t : ℝ) * (q : ℝ) + (t : ℝ) * ((j : ℤ) - (ℓ : ℤ)) / (s : ℝ) + betaI s t (ℓ : ℤ) := by
    push_cast
    field_simp
    ring
  simp only [Nsum, phi, hm, hb, hA]
  set X : ℝ := (t : ℝ) * (q : ℝ) + (t : ℝ) * ((j : ℤ) - (ℓ : ℤ)) / (s : ℝ)
    + betaI s t (ℓ : ℤ) with hX
  set Y : ℝ := HvdH.betaR s t j with hY
  have hr : -(Real.pi * (α : ℝ) ^ 2 * (X ^ 2 - Y ^ 2))
      = -Real.pi * (α : ℝ) ^ 2 * X ^ 2 + Real.pi * (α : ℝ) ^ 2 * Y ^ 2 := by ring
  rw [hr, Real.exp_add]
  push_cast
  ring

/-- The `ℓ`-th row of `Nmat` is the `ℤ`-indexed Gaussian series `∑_n phi n`. -/
theorem Nmat_mulVec_eq_tsum (s t α : ℕ) (hs : 0 < s) (hst : s < t) (hα : 0 < α)
    (u : Fin s → ℂ) (ℓ : Fin s) :
    (HvdH.Nmat s t α).mulVec u ℓ = ∑' n : ℤ, phi s t α hs ℓ u n := by
  haveI : NeZero s := ⟨hs.ne'⟩
  set e : Fin s × ℤ ≃ ℤ := (Equiv.prodComm (Fin s) ℤ).trans (Int.divModEquiv s).symm with he
  have heval : ∀ (j : Fin s) (q : ℤ), e (j, q) = (j : ℤ) + (s : ℤ) * q := by
    intro j q
    rw [he]
    simp [Int.divModEquiv_symm_apply, mul_comm, add_comm]
  have hsum : Summable (fun p : Fin s × ℤ => Nsum s t α ℓ u p.1 p.2) :=
    summable_Nsum s t α hs hst hα ℓ u
  have hfib : ∀ j : Fin s, Summable (fun q : ℤ => Nsum s t α ℓ u j q) :=
    fun j => hsum.prod_factor j
  have h1 : (HvdH.Nmat s t α).mulVec u ℓ = ∑ j : Fin s, HvdH.Nmat s t α ℓ j * u j :=
    Matrix.mulVec_apply_eq_sum _ _ _
  have h2 : ∀ j : Fin s, HvdH.Nmat s t α ℓ j * u j = ∑' q : ℤ, Nsum s t α ℓ u j q := by
    intro j
    have hE := summable_Egauss s t α hs hst hα ℓ j
    rw [Nmat_apply s t α hs hst ℓ j, mul_assoc,
      ← Summable.tsum_mul_right
        (((Real.exp (Real.pi * (α : ℝ) ^ 2 * (HvdH.betaR s t j) ^ 2) : ℝ) : ℂ) * u j) hE]
    exact tsum_congr (fun q => by rw [Nsum]; ring)
  rw [h1]
  simp_rw [h2]
  have hft : (∑' j : Fin s, (∑' q : ℤ, Nsum s t α ℓ u j q))
      = ∑ j : Fin s, (∑' q : ℤ, Nsum s t α ℓ u j q) :=
    (hasSum_fintype (fun j : Fin s => (∑' q : ℤ, Nsum s t α ℓ u j q))).tsum_eq
  rw [← hft]
  rw [← Summable.tsum_prod' hsum hfib]
  trans ∑' p : Fin s × ℤ, phi s t α hs ℓ u (e p)
  · exact tsum_congr (fun p => by
      rw [heval p.1 p.2]
      exact Nsum_eq_phi s t α hs ℓ u p.1 p.2)
  · exact Equiv.tsum_eq e (fun n : ℤ => phi s t α hs ℓ u n)

/-- `phi` at the index `ℓ` is `u ℓ`: the "diagonal" term of the series. -/
lemma phi_self (s t α : ℕ) (hs : 0 < s) (ℓ : Fin s) (u : Fin s → ℂ) :
    phi s t α hs ℓ u (ℓ : ℤ) = u ℓ := by
  simp [phi, modZ_eq_self]

/-- The series `∑_n phi n` is summable. -/
lemma summable_phi (s t α : ℕ) (hs : 0 < s) (hst : s < t) (hα : 0 < α)
    (u : Fin s → ℂ) (ℓ : Fin s) :
    Summable (fun n : ℤ => phi s t α hs ℓ u n) := by
  haveI : NeZero s := ⟨hs.ne'⟩
  set e : Fin s × ℤ ≃ ℤ := (Equiv.prodComm (Fin s) ℤ).trans (Int.divModEquiv s).symm with he
  have heval : ∀ (j : Fin s) (q : ℤ), e (j, q) = (j : ℤ) + (s : ℤ) * q := by
    intro j q
    rw [he]
    simp [Int.divModEquiv_symm_apply, mul_comm, add_comm]
  have h1 : Summable (fun p : Fin s × ℤ => phi s t α hs ℓ u (e p)) :=
    (summable_Nsum s t α hs hst hα ℓ u).congr (fun p =>
      (Nsum_eq_phi s t α hs ℓ u p.1 p.2).trans
        ((congrArg (fun n : ℤ => phi s t α hs ℓ u n) (heval p.1 p.2)).symm))
  exact (Equiv.summable_iff (f := fun n : ℤ => phi s t α hs ℓ u n) e).mp h1

/-- Pointwise size estimate for the summand `phi` (paper Lemma 4.6, with `θ = t/s - 1`). -/
lemma norm_phi_le (s t α : ℕ) (hs : 0 < s) (hst : s < t) (hα : 0 < α) (ℓ : Fin s)
    (u : Fin s → ℂ) (n : ℤ) (hn : n ≠ (ℓ : ℤ)) :
    ‖phi s t α hs ℓ u n‖ ≤ Real.exp (-(2 * Real.pi * ((α : ℝ) ^ 2 * ((t : ℝ) / s - 1)) *
      (|((n : ℝ) - (ℓ : ℝ))| - 1 / 2) ^ 2)) * ‖u‖ := by
  have hq' : 2 * ((t : ℝ) / s - 1) * ((|((n : ℝ) - (ℓ : ℝ))| - 1 / 2) ^ 2)
      ≤ ((t : ℝ) * ((n : ℝ) - (ℓ : ℝ)) / s + betaI s t (ℓ : ℤ)) ^ 2
        - (betaI s t n) ^ 2 := by
    have h := quad_ineq s t hs hst ℓ (n - (ℓ : ℤ)) (by simpa using sub_ne_zero.mpr hn)
    rw [show (ℓ : ℤ) + (n - (ℓ : ℤ)) = n by ring] at h
    push_cast at h
    linarith [h]
  have hexp : Real.exp (-(Real.pi * (α : ℝ) ^ 2 *
        (((t : ℝ) * ((n : ℝ) - (ℓ : ℝ)) / s + betaI s t (ℓ : ℤ)) ^ 2 - (betaI s t n) ^ 2)))
      ≤ Real.exp (-(2 * Real.pi * ((α : ℝ) ^ 2 * ((t : ℝ) / s - 1)) *
        (|((n : ℝ) - (ℓ : ℝ))| - 1 / 2) ^ 2)) := by
    apply Real.exp_le_exp.mpr
    have hx : 0 < Real.pi * (α : ℝ) ^ 2 := by positivity
    nlinarith [hq', hx]
  have hnrm : ∀ r : ℝ, ‖(((Real.exp r : ℝ)) : ℂ)‖ = Real.exp r := fun r =>
    (RCLike.norm_ofReal _).trans (abs_of_nonneg (Real.exp_nonneg _))
  rw [phi, norm_mul, hnrm]
  exact mul_le_mul hexp (norm_le_pi_norm u (modZ s hs n)) (norm_nonneg _) (Real.exp_nonneg _)

end Work.ResMath
