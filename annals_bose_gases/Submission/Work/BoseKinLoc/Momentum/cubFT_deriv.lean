import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Submission.Work.BoseKinLoc.Momentum.cubFT_prod
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The coordinate derivatives of the unit-cube Fourier symbol `cubFT`

Given the product formula `cubFT q = ∏ i, hFT (q i)` and the 1D derivative
`HasDerivAt hFT (-(mFT t)) t`, the derivative of `cubFT` in the direction of the standard
basis vector `kcStdBasis i` is

    `fderiv ℝ cubFT q (kcStdBasis i) = -(mFT (q i)) * ∏ j ≠ i, hFT (q j)`.

The proof is by the product rule for a curve: the map `s ↦ q + s • kcStdBasis i` moves only the
`i`-th coordinate, so `cubFT (q + s • kcStdBasis i) = (∏ j ≠ i, hFT (q j)) * hFT (q i + s)` and the
1D product rule gives the claim.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Momentum

open Submission.BoseGases

set_option autoImplicit false

/-- Coordinates of the standard basis vector: `(kcStdBasis i) j = δ_{ij}`. -/
lemma kcStdBasis_apply_coord (i j : Fin 3) :
    (kcStdBasis i : EuclideanSpace ℝ (Fin 3)) j = if j = i then (1 : ℝ) else 0 := by
  rw [Submission.BoseGases.kcStdBasis, EuclideanSpace.single_apply]

/-- `inner ℝ (kcStdBasis i) q = q i`. -/
lemma inner_kcStdBasis (i : Fin 3) (q : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ (kcStdBasis i) q = q i := by
  rw [Submission.BoseGases.kcStdBasis, EuclideanSpace.inner_single_left]
  simp

/-- **The coordinate derivative of `cubFT`** (conditional on the product formula and the 1D
derivative of `hFT`). -/
theorem fderiv_cubFT_coord_of
    (hprod : ∀ q : EuclideanSpace ℝ (Fin 3), cubFT q = ∏ i, hFT (q i))
    (hderiv : ∀ t : ℝ, HasDerivAt hFT (-(mFT t)) t)
    (q : EuclideanSpace ℝ (Fin 3)) (i : Fin 3) :
    fderiv ℝ cubFT q (kcStdBasis i)
      = -(mFT (q i)) * ∏ j ∈ Finset.univ.erase i, hFT (q j) := by
  set F : EuclideanSpace ℝ (Fin 3) → ℝ := fun x => ∏ j, hFT (x j) with hFdef
  set L : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ :=
    ∑ j ∈ Finset.univ, (∏ k ∈ Finset.univ.erase j, hFT (q k)) •
      ((-(mFT (q j))) • (innerSL ℝ (kcStdBasis j))) with hL
  -- the derivative of each coordinate factor
  have hg : ∀ j : Fin 3, HasFDerivAt (fun q : EuclideanSpace ℝ (Fin 3) => hFT (q j))
      ((-(mFT (q j))) • (innerSL ℝ (kcStdBasis j))) q := by
    intro j
    have h1 : HasFDerivAt (innerSL ℝ (kcStdBasis j)) (innerSL ℝ (kcStdBasis j)) q :=
      (innerSL ℝ (kcStdBasis j)).hasFDerivAt
    have h3 := (hderiv (inner ℝ (kcStdBasis j) q)).comp_hasFDerivAt q h1
    have h3' : HasFDerivAt (hFT ∘ (innerSL ℝ (kcStdBasis j)))
        ((-(mFT (inner ℝ (kcStdBasis j) q))) • (innerSL ℝ (kcStdBasis j))) q := h3
    rw [inner_kcStdBasis j q] at h3'
    have h4 : (fun x : EuclideanSpace ℝ (Fin 3) => hFT (x j))
        = (hFT ∘ (innerSL ℝ (kcStdBasis j))) := by
      funext x
      simp only [Function.comp_apply, innerSL_apply_apply, inner_kcStdBasis]
    rwa [h4]
  have hF : HasFDerivAt F L q := by
    rw [hFdef, hL]
    exact HasFDerivAt.finsetProd fun j _ => hg j
  -- the curve `s ↦ q + s • kcStdBasis i` moves only the `i`-th coordinate
  have hcoord : ∀ s : ℝ, F (q + s • kcStdBasis i)
      = (∏ j ∈ Finset.univ.erase i, hFT (q j)) * hFT (q i + s) := by
    intro s
    have hji : ∀ j : Fin 3, j ≠ i → (q + s • kcStdBasis i) j = q j := by
      intro j hj
      simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply,
        kcStdBasis_apply_coord, if_neg hj, smul_zero, add_zero]
    have hii : (q + s • kcStdBasis i) i = q i + s := by
      simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply,
        kcStdBasis_apply_coord, ite_true, smul_eq_mul, mul_one, add_zero]
    rw [hFdef]
    show (∏ j : Fin 3, hFT ((q + s • kcStdBasis i) j)) = _
    rw [← Finset.prod_erase_mul Finset.univ
      (fun j : Fin 3 => hFT ((q + s • kcStdBasis i) j)) (Finset.mem_univ i)]
    congr 1
    · exact Finset.prod_congr rfl fun j hj => by rw [hji j (Finset.ne_of_mem_erase hj)]
    · rw [hii]
  -- the derivative of the curve, computed by the 1D product rule
  have hD : HasDerivAt (fun s : ℝ => F (q + s • kcStdBasis i))
      (-(mFT (q i)) * ∏ j ∈ Finset.univ.erase i, hFT (q j)) 0 := by
    rw [show (fun s : ℝ => F (q + s • kcStdBasis i))
        = fun s : ℝ => (∏ j ∈ Finset.univ.erase i, hFT (q j)) * hFT (q i + s) from
      funext hcoord]
    have h1 : HasDerivAt (fun s : ℝ => hFT (q i + s)) (-(mFT (q i))) 0 := by
      have hinner : HasDerivAt ((fun _ : ℝ => q i) + id) (0 + 1) 0 :=
        (hasDerivAt_const (x := (0 : ℝ)) (q i)).add (hasDerivAt_id (0 : ℝ))
      rw [zero_add] at hinner
      have h := HasDerivAt.comp (0 : ℝ) (hderiv (q i + 0)) hinner
      rw [add_zero, mul_one] at h
      exact h
    have hconst : HasDerivAt (fun _ : ℝ => ∏ j ∈ Finset.univ.erase i, hFT (q j)) 0 0 :=
      hasDerivAt_const (x := (0 : ℝ)) (∏ j ∈ Finset.univ.erase i, hFT (q j))
    have h2 : HasDerivAt
        (fun s : ℝ => (∏ j ∈ Finset.univ.erase i, hFT (q j)) * hFT (q i + s))
        (-(mFT (q i)) * ∏ j ∈ Finset.univ.erase i, hFT (q j)) 0 := by
      have h := HasDerivAt.const_mul (∏ j ∈ Finset.univ.erase i, hFT (q j)) h1
      rw [show (∏ j ∈ Finset.univ.erase i, hFT (q j)) * (-(mFT (q i)))
          = -(mFT (q i)) * ∏ j ∈ Finset.univ.erase i, hFT (q j) from by ring] at h
      exact h
    exact h2
  -- the FDeriv of the curve, by composition
  have hcurve : HasDerivAt (fun s : ℝ => F (q + s • kcStdBasis i)) (L (kcStdBasis i)) 0 := by
    have hg' : HasFDerivAt (fun s : ℝ => q + s • kcStdBasis i)
        (ContinuousLinearMap.toSpanSingleton ℝ (kcStdBasis i)) 0 := by
      have h : HasFDerivAt ((fun _ : ℝ => q) +
          (ContinuousLinearMap.toSpanSingleton ℝ (kcStdBasis i) : ℝ → EuclideanSpace ℝ (Fin 3)))
          (0 + ContinuousLinearMap.toSpanSingleton ℝ (kcStdBasis i)) 0 :=
        (hasFDerivAt_const q (0 : ℝ)).add
          (ContinuousLinearMap.toSpanSingleton ℝ (kcStdBasis i)).hasFDerivAt
      rw [zero_add] at h
      rwa [show ((fun _ : ℝ => q) +
            (ContinuousLinearMap.toSpanSingleton ℝ (kcStdBasis i) : ℝ → EuclideanSpace ℝ (Fin 3)))
          = (fun s : ℝ => q + s • kcStdBasis i) from funext fun s => by
            simp [ContinuousLinearMap.toSpanSingleton_apply]] at h
    have hF0 : HasFDerivAt F L (q + (0 : ℝ) • kcStdBasis i) := by
      rw [show q + (0 : ℝ) • kcStdBasis i = q from by simp]
      exact hF
    have hcomp : HasDerivAt (fun s : ℝ => F (q + s • kcStdBasis i))
        ((L.comp (ContinuousLinearMap.toSpanSingleton ℝ (kcStdBasis i))) (1 : ℝ)) 0 := by
      have h : HasFDerivAt (F ∘ fun s : ℝ => q + s • kcStdBasis i)
          (L.comp (ContinuousLinearMap.toSpanSingleton ℝ (kcStdBasis i))) 0 :=
        HasFDerivAt.comp (0 : ℝ) hF0 hg'
      rw [hasFDerivAt_iff_hasDerivAt] at h
      exact h
    rw [show (L.comp (ContinuousLinearMap.toSpanSingleton ℝ (kcStdBasis i))) (1 : ℝ)
        = L (kcStdBasis i) from by
      simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply]] at hcomp
    exact hcomp
  rw [show cubFT = F from funext fun x => by rw [hFdef]; exact hprod x, hF.fderiv]
  exact hcurve.unique hD

end Work.BoseKinLoc.Momentum
