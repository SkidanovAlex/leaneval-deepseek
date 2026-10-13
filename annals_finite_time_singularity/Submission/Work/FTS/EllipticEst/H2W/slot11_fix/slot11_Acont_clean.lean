import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Tactic.Have
import Submission.Work.FTS.EllipticEst.H2W.Slot01W.ZTBound
import Submission.Work.FTS.EllipticEst.H2W.Slot01W.SliceKit

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.slot11_fix

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **Glueing `Ioo`-regularity with the two endpoint values.**  If `f` is `C⁰` on `(0,π/2)`,
agrees there with a function `g` continuous on `[0,π/2]`, and has the same values as `g` at the two
endpoints, then `f` is continuous on `[0,π/2]`.

(Re-proved here: in the original file it is a local helper of `H2W/slot11_Acont.lean` whose import
cone is blocked.) -/
theorem continuousOn_Icc_of_eqOn_Ioo {f g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Icc 0 (Real.pi / 2)))
    (hf : ContinuousOn f (Set.Ioo 0 (Real.pi / 2)))
    (hEq : Set.EqOn f g (Set.Ioo 0 (Real.pi / 2)))
    (h0 : f 0 = g 0) (hpi : f (Real.pi / 2) = g (Real.pi / 2)) :
    ContinuousOn f (Set.Icc 0 (Real.pi / 2)) := by
  have hab : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  have hmem0 : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝[>] (0 : ℝ) := by
    rw [← nhdsWithin_Ioo_eq_nhdsGT hab]
    exact self_mem_nhdsWithin
  have hmempi : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝[<] (Real.pi / 2) := by
    rw [← nhdsWithin_Ioo_eq_nhdsLT hab]
    exact self_mem_nhdsWithin
  refine Work.H2W.continuousOn_Icc_of_limits hf ?_ ?_
  · have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝[Set.Icc 0 (Real.pi / 2)] (0 : ℝ) := by
      rw [← nhdsWithin_Ioo_eq_nhdsGT hab]
      exact nhdsWithin_mono 0 (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
    have hg0 : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 (g 0)) :=
      (hg.continuousWithinAt (Set.left_mem_Icc.mpr hab.le)).mono_left hle
    have hev : f =ᶠ[𝓝[>] (0 : ℝ)] g := Filter.eventually_of_mem hmem0 hEq
    have := Filter.Tendsto.congr' hev.symm hg0
    simpa only [h0] using this
  · have hle : 𝓝[<] (Real.pi / 2) ≤ 𝓝[Set.Icc 0 (Real.pi / 2)] (Real.pi / 2) := by
      rw [← nhdsWithin_Ioo_eq_nhdsLT hab]
      exact nhdsWithin_mono (Real.pi / 2) (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
    have hgpi : Tendsto g (𝓝[<] (Real.pi / 2)) (𝓝 (g (Real.pi / 2))) :=
      (hg.continuousWithinAt (Set.right_mem_Icc.mpr hab.le)).mono_left hle
    have hev : f =ᶠ[𝓝[<] (Real.pi / 2)] g := Filter.eventually_of_mem hmempi hEq
    have := Filter.Tendsto.congr' hev.symm hgpi
    simpa only [hpi] using this

/-- **Clean, buildable copy of `Work.FTS.EllipticEst.H2W.slot11_Acont`**
(`Submission/Work/FTS/EllipticEst/H2W/slot11_Acont.lean`, which cannot be built: its cone reaches
the stale `RPFresh/excess_finite` through `aSliceHonest`, and `ellHyp_L2Mem_*` through
`Fstar_DzIter_le_Psi`/`momentChainAe` — see
`Submission/Work/FTS/EllipticEst/H2W/NOTES_slot11_bound_BLOCKER.md`).  The same statement is also
`Work.H2W.weakSliceZContinuousAe` and `Work.H2W.weakSliceZContinuous` (a.e. form).

You are welcome to copy the proof from `slot11_Acont.lean` (30 KB, the assembly is
`exact ⟨hcontA, hDz2⟩`) — but *every* module you import must be one whose cone does not reach
`ellHyp_L2Mem_fields`, `ellHyp_L2Mem_pz_weighted`, `Tools/ellHyp_pz_honesty_fts`,
`Cert/HkMem_Gbar_sin`, `Cert/HkMem_Fstar_sin`, `RPFresh/excess_finite` or
`AgmonSlice/zsq_pzIter2_mixed_open` (that last one is broken only because
`Submission.Work.FTS.EllipticEst.propHk_fts` imports the *deleted* `TT/ESW/Pieces.lean`); where a
helper you need is trapped, re-prove it in this file.

Route (see `Submission/Work/H2W/weakSliceZContinuous.lean`'s header for the analysis):
* `slope(z) := lim_{θ→0⁺} (z²∂_z²Ψ)(z,θ)` equals `-[F_*(D_z²F)(z) + α²·F_*(D_z⁴Ψ)(z)]` for every
  `z > 0` (IBP with the adjoint kernel `sinθcos²θ`:
  `remov.SourceBound.sliceTendstoZeroOfMoment.auxMoment` / `sliceLzero1_moment`, plus
  `bslOp α (D_z^jΨ) = D_z^jF` and `z²∂_z² = D_z² - D_z`);
* both moments vanish for a.e. `z`: `F_*(D_z²F) = 0` a.e. is `H2W.Fstar_DzIter_two_F_ae` (clean),
  and `F_*(D_z⁴Ψ) = 0` a.e. is `H2W/FstarDzIterFourPsiAe.lean` (copy/adapt it: it is trapped only
  through its imports of `momentChainAe` / `aSliceHonest`);
* the *pointwise* version is NOT derivable from `EllWeakPos α 2` — keep the `∀ᵐ`;
* the second conjunct follows from the first plus `D_z²Ψ = z²∂_z²Ψ + D_zΨ` and
  `H2W.weakSliceContinuousKit` (clean), which gives the `D_zΨ`-slice continuity pointwise;
* the slice honesty needed to apply `weakSliceLimits` is the content of `H2W/aSliceHonest.lean`
  (equivalently `slot11_fix/slot11_Ahonest_clean` once that lands; re-derive it inline if it is not
  available yet).

## The proof actually written here

The whole analytic content is already available, `sorry`-free, in the clean twin tree
`Submission/Work/FTS/EllipticEst/H2W/Slot01W/` (which repoints every import of the blocked chain at
a currently buildable module — see `Slot01W/NOTES_slot01Weak.md`):

* the first conjunct is exactly `Work.H2W.aeSliceContASelf` (`Slot01W/ZTBound.lean`): it derives the
  `a.e.`-in-`z` vanishing of the `Lzero1`-moment of the `A`-slice `A := z²∂_z²Ψ` from the a.e.
  vanishing of `F_*(D_z²F)` and `F_*(D_z⁴Ψ)` (`Fstar_DzIter_two_F_ae`,
  `Slot01W.FstarDzIterFourAe`, `Lzero1A_moment_ae`) and then applies
  `remov.SourceBound.sliceTendstoZeroOfMoment` at `0⁺` and `H2W.weakSliceLimits` at `(π/2)⁻`;
* the second conjunct is `D_z²Ψ = D_zΨ + z²∂_z²Ψ` on the open interval: the `D_zΨ`-slice is
  continuous on `[0,π/2]` by `Work.H2W.weakSliceContinuousKit` (`Slot01W/SliceKit.lean`), the
  `A`-slice by the first conjunct, and the two endpoint values of `D_z²Ψ` are `0` (they are the
  `z`-derivatives of the identically vanishing slices `Ψ · 0`, `Ψ · (π/2)`).  The glueing of the
  `Ioo` identity with the endpoint values is the helper `continuousOn_Icc_of_eqOn_Ioo` above. -/
theorem slot11_Acont_clean : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z →
      ContinuousOn (fun θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (Set.Icc 0 (Real.pi / 2))
        ∧ ContinuousOn (fun θ => Work.Spaces.DzIter 2 Ψ z θ) (Set.Icc 0 (Real.pi / 2)) := by
  intro α F Ψ hα hα4 h
  -- the `A`-slice, a.e. in `z`
  filter_upwards [Work.H2W.aeSliceContASelf α F Ψ hα hα4 h] with z hA
  intro hz
  refine ⟨hA hz, ?_⟩
  -- the second conjunct: `D_z²Ψ = D_zΨ + z²∂_z²Ψ` on the open interval, endpoints `0`
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hdz : ContinuousOn (fun θ => Work.Spaces.Dz Ψ z θ) (Set.Icc 0 (Real.pi / 2)) :=
    (Work.H2W.weakSliceContinuousKit α F Ψ hα hα4 h z hz).2
  have hsum : ContinuousOn
      (fun θ => Work.Spaces.Dz Ψ z θ + z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      (Set.Icc 0 (Real.pi / 2)) := hdz.add (hA hz)
  refine continuousOn_Icc_of_eqOn_Ioo hsum ?_ ?_ ?_ ?_
  · exact ((hΨ.DzIter 2).curry_θ hz).continuousOn
  · -- the product rule `z²∂_z² = D_z² − D_z` on the open interval
    intro θ hθ
    have hh := Work.H2W.MomentAe.zsq_pzIter2_eq hΨ hz hθ
    linarith [hh]
  · -- left endpoint
    have hz1 : (fun z' : ℝ => Work.Spaces.DzIter 1 Ψ z' 0) = fun _ => (0 : ℝ) :=
      funext fun z' => Work.H2W.dz_zero_at_zero h z'
    have hDz2 : Work.Spaces.DzIter 2 Ψ z 0 = 0 := by
      show z * Work.Spaces.pz (Work.Spaces.DzIter 1 Ψ) z 0 = 0
      rw [show Work.Spaces.pz (Work.Spaces.DzIter 1 Ψ) z 0
          = deriv (fun z' : ℝ => Work.Spaces.DzIter 1 Ψ z' 0) z from rfl, hz1, deriv_const,
        mul_zero]
    rw [hDz2, Work.H2W.dz_zero_at_zero h z,
      Work.H2W.pzIter2_at_eq_zero h.zero z, mul_zero]
    ring
  · -- right endpoint
    have hz1 : (fun z' : ℝ => Work.Spaces.DzIter 1 Ψ z' (Real.pi / 2)) = fun _ => (0 : ℝ) :=
      funext fun z' => Work.H2W.dz_zero_at_pi_half h z'
    have hDz2 : Work.Spaces.DzIter 2 Ψ z (Real.pi / 2) = 0 := by
      show z * Work.Spaces.pz (Work.Spaces.DzIter 1 Ψ) z (Real.pi / 2) = 0
      rw [show Work.Spaces.pz (Work.Spaces.DzIter 1 Ψ) z (Real.pi / 2)
          = deriv (fun z' : ℝ => Work.Spaces.DzIter 1 Ψ z' (Real.pi / 2)) z from rfl, hz1,
        deriv_const, mul_zero]
    rw [hDz2, Work.H2W.dz_zero_at_pi_half h z,
      Work.H2W.pzIter2_at_eq_zero h.pi_half z, mul_zero]
    ring

end

end Work.FTS.EllipticEst.H2W.slot11_fix
