import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.H2W.Fstar_DzIter_two_F
import Submission.Work.FTS.EllipticEst.TT.Slot11.MomentChainAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
Copyright: work module for the Elgindi finite-time singularity project.

# The level-`4` moment of the solution in the weak class

The requested lemma is

```
theorem FstarDzIterFourPsiAe : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar (Work.Spaces.DzIter 4 Ψ) z = 0
```

i.e. the angular moment `F_*(D_z^4 Ψ) = ∫_θ D_z^4Ψ(z,θ)·sinθcos²θ dθ` of the four-fold
radially differentiated solution vanishes almost everywhere in `z > 0`, for every datum of the
weak hypothesis class at level `2`.

## The route

The moment chain of `H2W/momentChainAe` (`MomentAe.Fstar_DzIter_le_Psi`) gives the *pointwise*
vanishing of `F_*(D_z^j Ψ)` for `j ≤ 3` — one level short of the target.  The missing level is
obtained from the *only* other `z`-honesty the class carries, namely

`HkMem α 2 A`,   `A := z²∂_z²Ψ`,

through the radial identity `D_z^{j+2}Ψ = D_z^{j+1}Ψ + D_z^j A` (i.e.
`D_z^j A = D_z^{j+2}Ψ - D_z^{j+1}Ψ`, `MomentAe.DzIter_zsq_pzIter2_eq`).  In particular

* `j = 2`: `D_z^4Ψ = D_z^3Ψ + D_z²A` — the decomposition which reduces the target to the moment
  of `A`;
* `j = 1`: `D_zA = D_z³Ψ - D_z²Ψ`, whence `F_*(D_zA) ≡ 0` pointwise (both terms vanish by
  `Fstar_DzIter_le_Psi` at levels `3` and `2`).

Applying the *level-`2`* moment argument of `H2W/Fstar_DzIter_two_F` to the honest datum
`A ∈ ℋ²` (`SmoothOpen A` holds because `A` is `z²` times a second `z`-derivative of `Ψ`,
`MomentAe.smoothOpen_zsq`) gives `F_*(D_z²A) = 0` a.e.: the moment tower
`Cert.radIter_bmom_ae_hasDerivAt` at level `2` says that `B_1 = F_*(D_zA)` is a.e.
differentiable with derivative `B_2/r = F_*(D_z²A)/r`, and `B_1 ≡ 0` forces that derivative to
vanish.

The final assembly is the `θ`-a.e. identity `D_z^4Ψ = D_z^3Ψ + D_z²A` plus the integrability of
the two right-hand slices (`MomentAe.level_bound` for `D_z^3Ψ`, and
`Cert.GbarSin.integrableOn_DzIter_mul_sinCos2` for `D_z²A`).
-/

namespace Work.H2W

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped Topology

open MeasureTheory Set Filter

/-- **The level-`2` moment of `A = z²∂_z²Ψ` vanishes almost everywhere.**

This is `H2W/Fstar_DzIter_two_F` replayed at the datum `A = z²∂_z²Ψ`, which is honest in `ℋ²`
for every datum of the weak class (`EllWeakPos.memA`): the only input of the level-`2` argument
is the `ℋ²`-honesty together with the pointwise vanishing of the previous moment `F_*(D_zA)`,
and the latter follows from `F_*(D_z³Ψ) = F_*(D_z²Ψ) = 0`. -/
theorem fstar_DzIter_two_zsq_ae (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar (Work.Spaces.DzIter 2
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z = 0 := by
  have hΨsm : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hAsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    MomentAe.smoothOpen_zsq hΨsm
  have hAmem : Work.Spaces.HkMem α 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    h.memA
  have hBmem : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ) := h.memB
  have hmom : ∀ j : ℕ, j ≤ 3 → ∀ z : ℝ, 0 < z →
      Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) z = 0 :=
    MomentAe.Fstar_DzIter_le_Psi α F Ψ h
  have hlev : ∀ i : ℕ, i ≤ 3 → ∀ u : ℝ, 0 < u →
      MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.DzIter i Ψ u θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
    fun i hi u hu => (MomentAe.level_bound hΨsm hAmem hBmem i hi).1 u hu
  -- ## Step 1: the moment `B_1 = F_*(D_z A)` of `A` vanishes pointwise on `(0,∞)`
  have hBmomA1 : ∀ z : ℝ, 0 < z →
      Work.FTS.EllipticEst.Bmom (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) 1 z = 0 := by
    intro z hz
    rw [Work.FTS.EllipticEst.Bmom_eq_Fstar_DzIter]
    have hI2 : MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.DzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
      hlev 2 (by norm_num) z hz
    have hI3 : MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.DzIter 3 Ψ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
      hlev 3 (by norm_num) z hz
    have hsplit : (fun θ : ℝ => Work.Spaces.DzIter 1
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
            * Work.Elliptic.sinCos2 θ)
        =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun θ : ℝ => Work.Spaces.DzIter 3 Ψ z θ * Work.Elliptic.sinCos2 θ
          - Work.Spaces.DzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ) := by
      filter_upwards [MomentAe.ae_Ioo_mem] with θ hθ
      rw [MomentAe.DzIter_zsq_pzIter2_eq hΨsm 1 hz hθ]
      ring
    rw [Work.Elliptic.Fstar, MeasureTheory.integral_congr_ae hsplit,
      MeasureTheory.integral_sub hI3 hI2]
    have h3 : (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.DzIter 3 Ψ z θ * Work.Elliptic.sinCos2 θ)
        = Work.Elliptic.Fstar (Work.Spaces.DzIter 3 Ψ) z := rfl
    have h2 : (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.DzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ)
        = Work.Elliptic.Fstar (Work.Spaces.DzIter 2 Ψ) z := rfl
    rw [h3, h2, hmom 3 (by norm_num) z hz, hmom 2 (by norm_num) z hz, sub_self]
  -- ## Step 2: the moment tower at level `2` turns `B_1 = 0` into `B_2 = 0` a.e.
  have hder := Work.FTS.EllipticEst.Cert.radIter_bmom_ae_hasDerivAt α 2 hAsm hAmem
    (by norm_num : 1 ≤ 2)
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi] at hder
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
  filter_upwards [hder] with z hzimp
  intro hzmem
  have hz : 0 < z := hzmem
  have hev : (fun y : ℝ => Work.FTS.EllipticEst.Bmom
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (2 - 1) y)
      =ᶠ[𝓝 z] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
    exact hBmomA1 y hy
  have h0 : HasDerivAt (fun _ : ℝ => (0 : ℝ))
      (Work.FTS.EllipticEst.Bmom (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) 2 z / z) z :=
    hev.hasDerivAt_iff.mp (hzimp hzmem)
  have hval : Work.FTS.EllipticEst.Bmom
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) 2 z / z = 0 :=
    h0.unique (hasDerivAt_const z 0)
  rw [div_eq_zero_iff] at hval
  rcases hval with h' | h'
  · rw [Work.FTS.EllipticEst.Bmom_eq_Fstar_DzIter] at h'
    exact h'
  · exact absurd h' hz.ne'

/-- The requested lemma. -/
theorem FstarDzIterFourPsiAe : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar (Work.Spaces.DzIter 4 Ψ) z = 0 := by
  intro α F Ψ _ _ h
  have hΨsm : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hAsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    MomentAe.smoothOpen_zsq hΨsm
  have hAmem : Work.Spaces.HkMem α 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    h.memA
  have hBmem : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ) := h.memB
  have hmom : ∀ j : ℕ, j ≤ 3 → ∀ z : ℝ, 0 < z →
      Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) z = 0 :=
    MomentAe.Fstar_DzIter_le_Psi α F Ψ h
  have hlev : ∀ i : ℕ, i ≤ 3 → ∀ u : ℝ, 0 < u →
      MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.DzIter i Ψ u θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
    fun i hi u hu => (MomentAe.level_bound hΨsm hAmem hBmem i hi).1 u hu
  have hA2 := fstar_DzIter_two_zsq_ae α F Ψ h
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi] at hA2
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
  filter_upwards [hA2] with z hA2imp
  intro hzmem
  have hz : 0 < z := hzmem
  have hA2z : Work.Elliptic.Fstar (Work.Spaces.DzIter 2
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z = 0 := hA2imp hzmem
  have hI3 : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.DzIter 3 Ψ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
    hlev 3 (by norm_num) z hz
  have hIA2 : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.DzIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
        * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.Cert.GbarSin.integrableOn_DzIter_mul_sinCos2 α 2
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) hAsm hAmem le_rfl hz
  have hcongr : (fun θ : ℝ => Work.Spaces.DzIter 4 Ψ z θ * Work.Elliptic.sinCos2 θ)
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => Work.Spaces.DzIter 3 Ψ z θ * Work.Elliptic.sinCos2 θ
        + Work.Spaces.DzIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
            * Work.Elliptic.sinCos2 θ) := by
    filter_upwards [MomentAe.ae_Ioo_mem] with θ hθ
    have hid := MomentAe.DzIter_zsq_pzIter2_eq hΨsm 2 hz hθ
    rw [hid]
    ring
  have hsplit : Work.Elliptic.Fstar (Work.Spaces.DzIter 4 Ψ) z
      = Work.Elliptic.Fstar (Work.Spaces.DzIter 3 Ψ) z
        + Work.Elliptic.Fstar (Work.Spaces.DzIter 2
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z := by
    rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar, Work.Elliptic.Fstar,
      MeasureTheory.integral_congr_ae hcongr]
    rw [show (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 3 Ψ z θ
            * Work.Elliptic.sinCos2 θ
          + Work.Spaces.DzIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
              * Work.Elliptic.sinCos2 θ))
        = (∫ θ in Work.Spaces.Iθ, Work.Spaces.DzIter 3 Ψ z θ * Work.Elliptic.sinCos2 θ)
          + (∫ θ in Work.Spaces.Iθ, Work.Spaces.DzIter 2
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
                * Work.Elliptic.sinCos2 θ)
        from MeasureTheory.integral_add hI3 hIA2]
  rw [hsplit, hmom 3 (by norm_num) z hz, hA2z, add_zero]

end Work.H2W
