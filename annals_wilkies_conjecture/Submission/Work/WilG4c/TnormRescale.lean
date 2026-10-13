/-
  WilG4c — BNZ Lemma 4.1 (`T-less-Tr`): the diagonal rescaling.

  This file proves `Work.WilG4c.TnormRescale`: a function of unit `(T,r)`-jet norm restricted
  to a diagonal affine subcube of side `1/r` has operator norms of all derivatives of order
  `≤ r` at most `1`.

  The chain of inequalities is the one in BNZ §5.4:

      ‖D^m (f ∘ L)(t)‖ = ‖D^m f (L t) ∘ (A, …, A)‖      (A = linear part of L, `1/r`·id)
                       ≤ ‖D^m f (L t)‖ · ‖A‖^m          (‖compContinuousLinearMap‖ bound)
                       ≤ m! · tnorm r f (L t) · (1/r)^m  (`NormJet`)
                       ≤ m! · (1/r)^m ≤ 1,               (`factorial_le_pow`)
-/
import Mathlib
import Submission.Work.WilG4c.Norm

set_option autoImplicit false
noncomputable section

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-- **Affine chain rule.**  For an affine reparametrisation `y ↦ b + A y`, the `m`-th iterated
derivative of `f ∘ (b + A ·)` at `x` is the `m`-th iterated derivative of `f` at `b + A x`,
composed with `A` in every variable.  For an affine map all the Faà di Bruno corrections
vanish, which is what makes the `(T,r)`-norm rescaling of BNZ Lemma 4.1 exact. -/
lemma iteratedFDeriv_affine_rescale {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℕ) (f : E → ℝ) (hf : ContDiff ℝ (r : ℕ∞) f) (A : E →L[ℝ] E) (b : E)
    {m : ℕ} (hm : m ≤ r) (x : E) :
    iteratedFDeriv ℝ m (fun y : E => f (b + A y)) x =
      (iteratedFDeriv ℝ m f (b + A x)).compContinuousLinearMap (fun _ : Fin m => A) := by
  have hcf : ContDiff ℝ (r : ℕ∞) (fun z : E => f (b + z)) :=
    hf.comp (contDiff_const.add contDiff_id)
  rw [show (fun y : E => f (b + A y)) = (fun z : E => f (b + z)) ∘ A from rfl]
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right A hcf x (Nat.cast_le.mpr hm)]
  rw [iteratedFDeriv_comp_add_left m b (A x)]

/-- **BNZ Lemma 4.1 (`T-less-Tr`).**  A function of unit `(T,r)`-jet norm restricted to a
diagonal affine subcube of side `1/r` has operator norms of all derivatives of order `≤ r`
at most `1`.  Proof: `f ∘ L` with `L t = a + t/r` is `f` composed with a linear map of norm
`≤ 1/r`; `‖D^m (f ∘ L)‖ ≤ ‖D^m f‖ · (1/r)^m ≤ m! · (1/r)^m · tnorm r f ≤ 1` by
`Work.WilkG4c.NormJet` and `Work.WilkG4c.factorial_le_pow`.  Mathlib has
`ContinuousLinearMap.iteratedFDeriv_comp_right` and
`ContinuousMultilinearMap.norm_compContinuousLinearMap_le`; the linear map is
`t ↦ (1/r) • t`, whose operator norm is `≤ 1/r` for `1 ≤ r`. -/
theorem TnormRescale {n : ℕ} (r : ℕ) (hr : 1 ≤ r) (f : (Fin n → ℝ) → ℝ)
    (hf : ContDiff ℝ (r : ℕ∞) f) (h : ∀ x, tnorm r f x ≤ 1) (a : Fin n → ℝ) :
    ∀ m, m ≤ r → ∀ t : Fin n → ℝ,
      ‖iteratedFDeriv ℝ m (fun t : Fin n → ℝ => f (fun i => a i + t i / (r : ℝ))) t‖ ≤ 1 := by
  intro m hm t
  have hr_pos : (0 : ℝ) < r := by exact_mod_cast hr
  have hinv : (0 : ℝ) ≤ (r : ℝ)⁻¹ := inv_nonneg.mpr hr_pos.le
  -- the linear part of `t ↦ a + t / r` is multiplication by `1 / r`
  set A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
    (r : ℝ)⁻¹ • (1 : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) with hA
  have hA_apply : ∀ u : Fin n → ℝ, A u = fun i => u i / (r : ℝ) := by
    intro u; ext i
    simp [hA, div_eq_inv_mul]
  -- rewrite the rescaled function as an affine reparametrisation
  have hφ : (fun t : Fin n → ℝ => f (fun i => a i + t i / (r : ℝ))) = fun t => f (a + A t) := by
    funext u
    congr 1
    ext i
    simp only [Pi.add_apply, hA_apply u]
  rw [hφ]
  rw [iteratedFDeriv_affine_rescale r f hf A a hm t]
  -- `‖A‖ ≤ 1/r`
  have hnormA : ‖A‖ ≤ (r : ℝ)⁻¹ := by
    refine ContinuousLinearMap.opNorm_le_bound A hinv fun u => ?_
    rw [hA]
    simp [norm_smul, Real.norm_of_nonneg hinv]
  -- precomposing with `A` in every variable
  have hcomp : ‖(iteratedFDeriv ℝ m f (a + A t)).compContinuousLinearMap (fun _ : Fin m => A)‖
      ≤ ‖iteratedFDeriv ℝ m f (a + A t)‖ * ‖A‖ ^ m := by
    have hh := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (iteratedFDeriv ℝ m f (a + A t)) (fun _ : Fin m => A)
    simpa [Finset.prod_const] using hh
  -- the `m`-th jet of `f` is bounded by `m!`
  have hjet : ‖iteratedFDeriv ℝ m f (a + A t)‖ ≤ (m.factorial : ℝ) := by
    have h1 := Work.WilkG4c.NormJet r m hm f (a + A t)
    have h2 : tnorm r f (a + A t) ≤ 1 := h (a + A t)
    have h3 : (0 : ℝ) ≤ (m.factorial : ℝ) := Nat.cast_nonneg _
    calc ‖iteratedFDeriv ℝ m f (a + A t)‖
        ≤ (m.factorial : ℝ) * tnorm r f (a + A t) := h1
      _ ≤ (m.factorial : ℝ) * 1 := mul_le_mul_of_nonneg_left h2 h3
      _ = (m.factorial : ℝ) := mul_one _
  -- the arithmetic of the rescaling: `m! · (1/r)^m ≤ 1`
  have hfin : (m.factorial : ℝ) * ‖A‖ ^ m ≤ 1 := by
    have hfac : (m.factorial : ℝ) ≤ (r : ℝ) ^ m := by
      have h' := Work.WilkG4c.factorial_le_pow m r hm hr
      have h2 : (m.factorial : ℝ) ≤ ((r ^ m : ℕ) : ℝ) := by exact_mod_cast h'
      simpa using h2
    have hprod : (r : ℝ) ^ m * ((r : ℝ)⁻¹) ^ m = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ (ne_of_gt hr_pos), one_pow]
    calc (m.factorial : ℝ) * ‖A‖ ^ m
        ≤ (r : ℝ) ^ m * ((r : ℝ)⁻¹) ^ m :=
          mul_le_mul hfac (pow_le_pow_left₀ (norm_nonneg A) hnormA m)
            (pow_nonneg (norm_nonneg A) m) (pow_nonneg hr_pos.le m)
      _ = 1 := hprod
  calc ‖(iteratedFDeriv ℝ m f (a + A t)).compContinuousLinearMap (fun _ : Fin m => A)‖
      ≤ ‖iteratedFDeriv ℝ m f (a + A t)‖ * ‖A‖ ^ m := hcomp
    _ ≤ (m.factorial : ℝ) * ‖A‖ ^ m :=
        mul_le_mul_of_nonneg_right hjet (pow_nonneg (norm_nonneg A) m)
    _ ≤ 1 := hfin

end Work.WilG4c
