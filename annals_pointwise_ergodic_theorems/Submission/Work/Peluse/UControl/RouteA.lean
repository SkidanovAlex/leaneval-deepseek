import Mathlib
import Submission.Work.Peluse.Peel.boxNormPow_diag_ge

/-!
# The elementary (`L²`-mass) lower bound for Peluse's box norm, and the mass bound for `Λ`

Two ingredients of the `U`-control chapter of Area A2 that are *elementary* (no PET, no
concatenation):

* `mass_ge_of_lambdaZ`: from `δ ≤ ‖Λ^{N₀,N}(f₀,f₁,f₂)‖` (with `f₀,f₁,f₂` `1`-bounded and supported
  in `[-N₀,N₀]`) one gets `δ²N₀/3 ≤ ∑_{x ∈ symIcc N₀} ‖f₂ x‖²`.  (The `ℓ¹` form
  `δN₀ ≤ ∑‖f₂‖` is `Work.Peluse.PETTwo.sum_norm_f2_ge`; Cauchy–Schwarz upgrades it.)
* `elementary_bound`: the *diagonal* lower bound for the `2^s`-th power of the uniformity norm,
  valid for an arbitrary complex `f` (`s ≥ 2`, direction set `c[1,L]`, `1 ≤ L ≤ N₀`):

  `c · δ^{2^s} / L^s ≤ ‖f‖^{2^s}_{U^s_{c[L]}(symIcc N₀)}`,

  with `c > 0` depending on `P` and `s` only.  This is the "small `L`" regime of
  `Work.Peluse.UControl.Theorem37Chapter`: it is *free of any PET hypothesis*.

The proof of `elementary_bound` is the diagonal argument: peeling the top level of the box sum
(`Peel.boxSumPow_peel`) and keeping only the pairs `h = h'` (legitimate: every summand is a
nonnegative real, `BoxNorm.boxSumPow_eq_boxNormPow`) reduces to the nonnegative functions
`‖f (· + h)‖²`, for which the diagonal bound `Peel.boxNormPow_diag_ge` applies.

## Reference

S. Peluse, *Bounds for sets with no polynomial progressions*, Forum Math. Pi **8** (2020), e16.
-/

set_option autoImplicit false
open scoped BigOperators
open Polynomial

namespace Work.Peluse.UControl

noncomputable section

open Work.Peluse

/-! ## Elementary toolbox -/

/-- The cardinality of `arithIcc c D = c[1,D]` is `D` when `c ≠ 0`. -/
theorem arithIcc_card' {c : ℤ} (hc : c ≠ 0) (D : ℕ) : (arithIcc c D).card = D := by
  have hinj : Function.Injective (fun n : ℕ => c * (n : ℤ)) := by
    intro a b hab
    have h : c * (a : ℤ) = c * (b : ℤ) := hab
    have h2 : (a : ℤ) = (b : ℤ) := mul_left_cancel₀ hc h
    exact_mod_cast h2
  rw [arithIcc, Finset.card_image_of_injective _ hinj]
  simp

/-- The cardinality of `symIcc N = [-N,N]`. -/
theorem card_symIcc' (N : ℕ) : (symIcc N).card = 2 * N + 1 := by
  rw [symIcc, Int.card_Icc]
  have h : ((N : ℤ) + 1 - (-(N : ℤ))) = ((2 * N + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h, Int.toNat_natCast]

/-- An integer outside `symIcc N` has `N < x.natAbs`. -/
theorem natAbs_lt_of_not_mem_symIcc' {N : ℕ} {x : ℤ} (h : x ∉ symIcc N) : N < x.natAbs := by
  rw [symIcc, Finset.mem_Icc] at h
  have h2 : ¬ x.natAbs ≤ N := by
    intro hle
    apply h
    have h3 : |x| ≤ (N : ℤ) := by rw [← Int.natCast_natAbs]; exact_mod_cast hle
    exact abs_le.mp h3
  omega

/-- The box sum is `(|S|)⁻¹` times a factor which does not depend on the ambient set `S`. -/
theorem boxSumPow_eq_inv_card_mul {t : ℕ} (Q : Fin t → Finset ℤ) (f : ℤ → ℂ) :
    ∃ A : ℂ, ∀ S : Finset ℤ, boxSumPow t Q S f = ((S.card : ℂ))⁻¹ * A := by
  refine ⟨(∏ i : Fin t, (((Q i).card : ℂ))⁻¹) * (∏ i : Fin t, (((Q i).card : ℂ))⁻¹) *
    ∑ h : (i : Fin t) → {x : ℤ // x ∈ Q i}, ∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q i},
      ∑' x : ℤ, ∏ ω : Fin t → Bool,
        (star^[weight ω]) (f (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω)), ?_⟩
  intro S
  simp only [boxSumPow, prodCubeSum_eq]
  ring

/-- **Monotonicity of the box-norm power in the ambient set.**  A smaller ambient set gives a larger
box-norm power (the normalising factor is `1/|S|`). -/
theorem boxNormPow_mono_box {t : ℕ} (Q : Fin t → Finset ℤ) (f : ℤ → ℂ) {S S' : Finset ℤ}
    (hSS : S ⊆ S') (hS : S.Nonempty) :
    boxNormPow t Q S' f ≤ boxNormPow t Q S f := by
  obtain ⟨A, hA⟩ := boxSumPow_eq_inv_card_mul Q f
  have hS' : S'.Nonempty := hS.mono hSS
  have hcard : (S.card : ℝ) ≤ (S'.card : ℝ) := by exact_mod_cast Finset.card_le_card hSS
  have hpos : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hS.card_pos
  have hpos' : (0 : ℝ) < (S'.card : ℝ) := by exact_mod_cast hS'.card_pos
  rw [boxNormPow, boxNormPow, hA S, hA S', norm_mul, norm_mul, norm_inv, norm_inv,
    Complex.norm_natCast, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_right (inv_anti₀ hpos hcard) (norm_nonneg _)

/-- `symIcc N ⊆ symIcc N'` for `N ≤ N'`. -/
theorem symIcc_mono' {N N' : ℕ} (h : N ≤ N') : symIcc N ⊆ symIcc N' := by
  intro x hx
  rw [symIcc, Finset.mem_Icc] at hx ⊢
  exact ⟨by omega, by omega⟩

/-! ## The mass bound -/
