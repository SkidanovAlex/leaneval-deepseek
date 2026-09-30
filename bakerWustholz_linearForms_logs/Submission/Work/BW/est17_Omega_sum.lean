import Mathlib
import Submission.Work.BW.Est17Ext
import Submission.Work.BW.DefsAC
import Submission.Work.BW.est15_mon1
import Submission.Work.BW.est15_mon_bound
import Submission.Work.BW.LiouvilleAux.posLog_hasFiniteSupport

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Complex NumberField

/-- **Place accounting for the `α'`-moderator `Ω`, sign-aware.**
`L = EL φ ρ`, `w₀ = w0 φ ρ`, `inclE φ ρ : K →+* L`.  For `s : ℤ`, the per-place moderator
`Ω_w = Σ_j D_j log⁺ w(α'_j^{sign s})`, with `log⁺ w(α'_j)` when `0 ≤ s` and `log⁺ w(α'_j)⁻¹`
when `s < 0` (both have the same total height since `logHeight₁ x⁻¹ = logHeight₁ x`).
Dropping the nonnegative `w₀`-term from the full sum
`Height.logHeight₁ (inclE φ ρ (α' j)) = Σ_{all w} w.mult · log⁺(w ·) + Σᶠ_{fin w} log⁺(w ·)`
(`NumberField.logHeight₁_eq`) and using `D_j ≥ 0` gives the stated upper bound. -/
theorem est17_Omega_sum {K : Type*} [Field K] [NumberField K] {r : ℕ} {φ : K →+* ℂ}
    {ρ : Fin r → ℂ} {α' : Fin r → K} {σl : Fin r → ℝ}
    (hα' : ∀ j, α' j ≠ 0) [inst : NumberField (EL φ ρ)]
    [DecidableEq (NumberField.InfinitePlace (EL φ ρ))] (s : ℤ) :
    (∑ w ∈ Finset.univ.erase (w0 φ ρ), (w.mult : ℝ) *
        (∑ j, ((pDj r (dK K) σl j : ℕ) : ℝ) *
          (if 0 ≤ s then w (inclE φ ρ (α' j)) else (w (inclE φ ρ (α' j)))⁻¹).posLog))
      + (∑ᶠ w : NumberField.FinitePlace (EL φ ρ),
          ∑ j, ((pDj r (dK K) σl j : ℕ) : ℝ) *
            (if 0 ≤ s then w (inclE φ ρ (α' j)) else (w (inclE φ ρ (α' j)))⁻¹).posLog)
      ≤ ∑ j, ((pDj r (dK K) σl j : ℕ) : ℝ) * Height.logHeight₁ (inclE φ ρ (α' j)) := by
  classical
  have hxj : ∀ j : Fin r, inclE φ ρ (α' j) ≠ 0 :=
    fun j => (map_ne_zero (inclE φ ρ)).mpr (hα' j)
  -- The two signs of `s` share the same per-place argument, so we isolate it once: for any
  -- family `y` of nonzero elements of `L = EL φ ρ`, the sum of the (non-`w₀`) archimedean
  -- contributions plus all finite-place contributions is bounded by `∑_j D_j · logHeight₁ (y j)`.
  have key : ∀ (y : Fin r → EL φ ρ), (∀ j, y j ≠ 0) →
      (∑ w ∈ Finset.univ.erase (w0 φ ρ), (w.mult : ℝ) *
          (∑ j, ((pDj r (dK K) σl j : ℕ) : ℝ) * (w (y j)).posLog))
        + (∑ᶠ w : NumberField.FinitePlace (EL φ ρ),
            ∑ j, ((pDj r (dK K) σl j : ℕ) : ℝ) * (w (y j)).posLog)
        ≤ ∑ j, ((pDj r (dK K) σl j : ℕ) : ℝ) * Height.logHeight₁ (y j) := by
    intro y hy
    have hD : ∀ j : Fin r, (0 : ℝ) ≤ ((pDj r (dK K) σl j : ℕ) : ℝ) :=
      fun j => Nat.cast_nonneg _
    -- finite support of the finite-place summands (needed to interchange `∑ᶠ` and `∑`)
    have hfs : ∀ j : Fin r, Function.HasFiniteSupport
        (fun w : NumberField.FinitePlace (EL φ ρ) =>
          ((pDj r (dK K) σl j : ℕ) : ℝ) * (w (y j)).posLog) := by
      intro j
      refine (LiouvilleAux.posLog_hasFiniteSupport (y j) (hy j)).subset ?_
      intro w hw
      simp only [Function.mem_support] at hw ⊢
      exact fun h => hw (by rw [h, mul_zero])
    -- distribute the outer weight `w.mult` and interchange the two finite sums
    have hL1 : (∑ w ∈ Finset.univ.erase (w0 φ ρ), (w.mult : ℝ) *
          (∑ j, ((pDj r (dK K) σl j : ℕ) : ℝ) * (w (y j)).posLog))
        = ∑ j, ((pDj r (dK K) σl j : ℕ) : ℝ) *
            (∑ w ∈ Finset.univ.erase (w0 φ ρ), (w.mult : ℝ) * (w (y j)).posLog) := by
      rw [show (∑ w ∈ Finset.univ.erase (w0 φ ρ), (w.mult : ℝ) *
            (∑ j, ((pDj r (dK K) σl j : ℕ) : ℝ) * (w (y j)).posLog))
          = ∑ w ∈ Finset.univ.erase (w0 φ ρ), ∑ j, (w.mult : ℝ) *
              (((pDj r (dK K) σl j : ℕ) : ℝ) * (w (y j)).posLog)
          from Finset.sum_congr rfl (fun w _ => Finset.mul_sum _ _ _)]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun w _ => by ring)
    -- interchange the `∑ᶠ` over finite places with the finite sum over `j`
    have hL2 : (∑ᶠ w : NumberField.FinitePlace (EL φ ρ),
            ∑ j, ((pDj r (dK K) σl j : ℕ) : ℝ) * (w (y j)).posLog)
        = ∑ j, ((pDj r (dK K) σl j : ℕ) : ℝ) *
            (∑ᶠ w : NumberField.FinitePlace (EL φ ρ), (w (y j)).posLog) := by
      rw [finsum_sum_univ hfs]
      exact Finset.sum_congr rfl (fun j _ => (mul_finsum _ _).symm)
    rw [hL1, hL2, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun j _ => ?_)
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (est15_mon1 (w0 φ ρ) (y j)) (hD j)
  by_cases hs : (0 : ℤ) ≤ s
  · simp only [if_pos hs]
    exact key (fun j => inclE φ ρ (α' j)) hxj
  · have hkey := key (fun j => (inclE φ ρ (α' j))⁻¹) (fun j => inv_ne_zero (hxj j))
    simp only [if_neg hs]
    simpa only [map_inv₀, Height.logHeight₁_inv] using hkey

end Work.BW
