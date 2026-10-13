import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongPersist.N6Trans.L6FBound.mixed_le_WlInf6
import Submission.Work.FTS.GalBasis.GalDense.Xmb
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.DzIter_eq_sum_scoef_of_contDiffOn_order

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `mixed_le_WlInf6_cd6`

Pointwise control of every mixed derivative `D_z^b D_θ^a f` (`1 ≤ a`, `a + b ≤ 6`) inside the
open quadrant by the `𝒲^{6,∞}`-norm, for a datum that is only `C^6` on the open quadrant
`Q0 = (0,∞) × (0,π/2)`:

`|D_z^b D_θ^a f (z,θ)| ≤ 1000 · |f|_{𝒲^{6,∞}} · (α + sin 2θ) · sin(2θ)^{α/5}`.

This is the `C^6`-only companion of `Work.FTS.StrongPersist.N6Trans.L6FBound.mixed_le_WlInf6` (the
proved statement for `SmoothOpen` data), and of `Work.FTS.OpenPkg.Mixed_le_WlInf_open` (the
order-4 version).

## Route

The angular summands of the `𝒲^{6,∞}`-norm control
`(z+1)^k ∂_z^k D_θ^a f · sin(2θ)^{-α/5}/(α + sin 2θ)`, and
`Work.Spaces.pz_Dth_sup_bound` turns this into

`|z^k ∂_z^k D_θ^a f| ≤ |f|_𝒲 · (z+1)^{-k} (α + sin 2θ) sin(2θ)^{α/5}`   (`1 ≤ a`, `k + a ≤ 6`),

which is `Work.FTS.StrongPersist.N6Trans.L6FBound.zpz_Dth_le_WlInf6`.

It remains to write `D_z^b` as a combination of the `z^k∂_z^k`.  The Stirling expansion
`D_z^b = ∑_{k≤b} S(b,k) z^k ∂_z^k` holds on the open set where the *`z`-slices* of the function
are `C^b`; for a `C^6` datum the function `D_θ^a f` has precisely `6 - a ≥ b` orders of joint
smoothness on `Q0` (`contDiffOn_uncurry_DthIter_le`), so the order-`b` expansion
`DzIter_eq_sum_scoef_of_contDiffOn_order` applies.  The total coefficient mass is the Bell
number `bell b ≤ 1000` for `b ≤ 6` (`Work.Spaces.abs_sum_scoef_mul_le`), and since
`z^k/(z+1)^k ≤ 1` for `z > 0`, each of the at most `b+1 ≤ 7` summands is bounded by the same
quantity `|f|_𝒲 (α + sin 2θ) sin(2θ)^{α/5}`.
-/

open scoped Real Topology

namespace Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6

set_option autoImplicit false

/-! ## Finite-order smoothness of the angular operator `D_θ` and its iterates

(The open-quadrant analogue of `Work.FTS.GalBasis.Xmb.contDiffOn_uncurry_pzIter_le`; `D_θ` is
`sin(2θ) ∂_θ`, and the extra factor is smooth on the whole plane, so it costs no order.) -/

theorem contDiffOn_uncurry_Dth_le {f : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) {n : ℕ}
    (h : ContDiffOn ℝ (((n + 1 : ℕ)) : WithTop ℕ∞) (Function.uncurry f) V) :
    ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (Function.uncurry (Work.Spaces.Dth f)) V := by
  have hpth := Work.FTS.GalBasis.Xmb.contDiffOn_uncurry_pth_le hV h
  have hs : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (fun p : ℝ × ℝ => Real.sin (2 * p.2)) V := by
    fun_prop
  have hmul := hs.mul hpth
  rw [show Function.uncurry (Work.Spaces.Dth f)
      = fun p : ℝ × ℝ => Real.sin (2 * p.2) * Function.uncurry (Work.Spaces.pth f) p from rfl]
  exact hmul

/-- Every iterate of `D_θ` costs one order of differentiability on an open set. -/
theorem contDiffOn_uncurry_DthIter_le {f : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) {N : ℕ}
    (h : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) (Function.uncurry f) V) :
    ∀ j k : ℕ, j + k ≤ N →
      ContDiffOn ℝ ((k : ℕ) : WithTop ℕ∞) (Function.uncurry (Work.Spaces.DthIter j f)) V := by
  intro j
  induction j with
  | zero => intro k hk; simpa using h.of_le (by exact_mod_cast (show k ≤ N by omega))
  | succ j ih =>
      intro k hjk
      have h2 : ContDiffOn ℝ (((k + 1 : ℕ)) : WithTop ℕ∞)
          (Function.uncurry (Work.Spaces.DthIter j f)) V := ih (k + 1) (by omega)
      simpa [Work.Spaces.DthIter_succ] using contDiffOn_uncurry_Dth_le hV h2

/-! ## The pointwise bound -/

theorem mixed_le_WlInf6_cd6 {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ 6 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hfm : Work.Spaces.WlInfMem α 6 f) {a b : ℕ} (ha : 1 ≤ a) (hab : a + b ≤ 6)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |Work.Spaces.mixed b a f z θ| ≤ 1000 * (Work.Spaces.WlInf α 6 f
      * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := by
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hb6 : b ≤ 6 := by omega
  have hzθQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := by
    rw [Work.FTS.EllipticEst.mem_Q0]; exact ⟨hz, hθ.1, hθ.2⟩
  -- the target factor is nonnegative, and so is the bound
  have hsin0 : 0 ≤ Real.sin (2 * θ) := Work.Spaces.sin_two_nonneg' hθI
  have hY : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg hsin0 _)
  have hW : 0 ≤ Work.Spaces.WlInf α 6 f :=
    Work.FTS.StrongPersist.N6Trans.L6FBound.WlInf6_nonneg hfm
  have hM : 0 ≤ Work.Spaces.WlInf α 6 f
      * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := mul_nonneg hW hY
  -- `D_θ^a f` is `C^b` on the open quadrant, since `a + b ≤ 6`
  have hsmD : ContDiffOn ℝ ((b : ℕ) : WithTop ℕ∞)
      (Function.uncurry (Work.Spaces.DthIter a f)) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_uncurry_DthIter_le Work.FTS.EllipticEst.isOpen_Q0 hf a b hab
  -- the Stirling expansion of `D_z^b` on the open quadrant
  have hStir := DzIter_eq_sum_scoef_of_contDiffOn_order Work.FTS.EllipticEst.isOpen_Q0 b hsmD
    z θ hzθQ
  rw [Work.Spaces.mixed, hStir]
  -- every summand is bounded by `|f|_𝒲 · (α + sin 2θ) sin(2θ)^{α/5}`
  have hterm : ∀ k ≤ b, |z ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter a f) z θ|
      ≤ Work.Spaces.WlInf α 6 f * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
    fun k _ => Work.FTS.StrongPersist.N6Trans.L6FBound.zpz_Dth_le_WlInf6 hα hfm ha (by omega)
      hzI hθI
  have hsum := Work.Spaces.abs_sum_scoef_mul_le b
      (Work.Spaces.WlInf α 6 f * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
      (fun k => z ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter a f) z θ) hterm
  calc |∑ k ∈ Finset.range (b + 1), (Work.Spaces.scoef b k : ℝ)
        * (z ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter a f) z θ)|
      ≤ (Work.Spaces.bell b : ℝ) * (Work.Spaces.WlInf α 6 f
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := hsum
    _ ≤ 1000 * (Work.Spaces.WlInf α 6 f
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
        mul_le_mul_of_nonneg_right
          (by exact_mod_cast Work.FTS.StrongPersist.N6Trans.L6FBound.bell_le_six b hb6) hM

end Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6
