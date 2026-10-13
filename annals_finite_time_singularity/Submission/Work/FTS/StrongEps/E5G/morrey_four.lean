/-
# `Work.FTS.StrongEps.E5G.morrey_four` — the level-`4` Morrey/Hölder-`1/2` bound on compacts

`Work.FTS.VocabO.HQo α 4 f` carries only *open-quadrant* smoothness (`SmoothOpen f`, i.e.
`C^∞` on `Q0 = (0,∞) × (0,π/2)`) together with the honest membership `HkMem α 4 f` of the
`ℋ⁴`-norm; there is no angular vanishing at `θ = 0, π/2` and no decay at `z = ∞`, so the
whole-quadrant Hardy route of `Work.FTS.StrongLWP.Sobolev` is unavailable.  On a *compact*
`K ⊆ Q0`, however, the classical 2-dimensional Sobolev/Morrey mechanism applies.

The difference from the sibling `Work.FTS.StrongEps.HQo_mixed_abs_le_on_compact` (which
handles the class `HQo α 6` and *all* slots `D_z^bD_θ^a` with `a + b ≤ 4`) is the level of the
norm: at level `4` the only slot whose second partial derivatives are still controlled is the
undifferentiated slot `(0,0)` — its second partials are the order-`2` mixed derivatives, which
occur in `HkIntegrand α 4`.  That suffices for a Hölder-`1/2` bound *of `f` itself*, which is
what is needed here.

The proof is:

* a compact `K ⊆ Q0` sits in a box `[zlo,zhi] × [tlo,thi]` whose two-fold enlargement
  `[zlo/2, zhi+1] × [tlo/2, (thi+π/2)/2]` still lies in `Q0`
  (`Work.FTS_EllLimOK.box_of_compact_inside_Q0`);
* a `C²` cut-off `χ` which is `1` on the box and vanishes off its enlargement
  (`Work.FTS.StrongLWP.Sobolev.EqcAux.exists_cutoff_rect_C2`);
* the seven rectangle `L²`-bounds of `χ`-free slots at level `4`
  (`Work.FTS.StrongEps.E5G.mixed_rect_L2_bounds_level`, the level-`k` refinement of
  `Work.FTS.StrongEps.LocUnif.mixed_rect_L2_bounds`, applied with `k = 4`, `j = i = 0`):
  the value of `f`, its two first partials and its four second partials on the enlargement are
  `L²`-bounded by `C · HkSq α 4 f`;
* the Morrey step `Work.FTS.StrongEps.E5G.morrey_step_four` (the slot-`(0,0)`, level-`4`
  instance of `Work.FTS.StrongEps.LocUnif.mixed_morrey_step`): Morrey's inequality
  `W^{2,2}(ℝ²) ⊂ C^{0,1/2}` (`Work.FTS.StrongLWP.Sobolev.holder_half_of_W22_real`) applied to
  `χ · f` gives
  `|f p - f q| ≤ Km · 2√(C + 3C(16+17M²)) · HkNorm α 4 f · √(dist p q)` for `p, q` on the box;
* the final bookkeeping `HkNorm α 4 f ≤ 1 + HkNorm α 4 f` and
  `Real.sqrt ‖p - q‖ = dist p q ^ (1/2 : ℝ)`.

The constant is independent of `α ∈ (0,1]` and of `f`: the only place where `α` enters the
argument is the comparison of the plain partial derivatives with the `ℋ⁴`-integrand, where the
angular weight `sin(2θ)^{-γ/2}` is used only through `sin(2θ) ≤ 1` (so that it is `≥ 1`), and
the radial weight `w(z) = (1+z)²/z² ≥ 1`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.E5G.Defs
import Submission.Work.FTS.VocabO
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongEps.HQo_mixed_abs_le_on_compact
import Submission.Work.FTS.StrongEps.HQoAux.cut_slot_L2_bounds
import Submission.Work.FTS.StrongLWP.Sobolev.holder_half_of_W22
import Submission.Work.FTS.StrongEps.E5G.mixed_rect_L2_bounds_level
import Submission.Work.FTS.StrongEps.E5G.morrey_step_four
import Submission.Work.FTS_EllLimOK.box_of_compact_inside_Q0
import Submission.Work.FTS.StrongLWP.Sobolev.EqcAux.exists_cutoff_rect_C2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5G

set_option autoImplicit false

theorem morrey_four {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKQ : K ⊆ Work.FTS.EllipticEst.Q0) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∀ f : Work.FTS.Galerkin.Fn,
      Work.FTS.VocabO.HQo α 4 f → ∀ p ∈ K, ∀ q ∈ K,
        |f p.1 p.2 - f q.1 q.2| ≤ C * (1 + Work.Spaces.HkNorm α 4 f) * Real.sqrt ‖p - q‖ := by
  rcases Set.eq_empty_or_nonempty K with hKe | hne
  · subst hKe
    exact ⟨1, one_pos, fun α hα f hf p hp q hq => absurd hp (by simp)⟩
  · -- ## A box `[zlo,zhi] × [tlo,thi]` containing `K`, with a two-fold enlargement in `Q0`
    obtain ⟨zlo, zhi, tlo, thi, hzlopos, hzlole, htlopos, htlole, hthilt, hKbox⟩ :=
      Work.FTS_EllLimOK.box_of_compact_inside_Q0 hK hKQ hne
    have hthipi : thi < Real.pi / 2 := hthilt
    have hzlo'pos : 0 < zlo / 2 := by linarith
    have hzlo'lt : zlo / 2 < zlo := by linarith
    have hzhi'lt : zhi < zhi + 1 := by linarith
    have hzlo'le : zlo / 2 ≤ zhi + 1 := by linarith
    have htlo'pos : 0 < tlo / 2 := by linarith
    have htlo'lt : tlo / 2 < tlo := by linarith
    have hthi'lt : thi < (thi + Real.pi / 2) / 2 := by linarith [Real.pi_pos]
    have hthi'pi : (thi + Real.pi / 2) / 2 < Real.pi / 2 := by linarith
    have hboxsub : Set.Icc (zlo / 2) (zhi + 1) ×ˢ Set.Icc (tlo / 2) ((thi + Real.pi / 2) / 2)
        ⊆ Work.FTS.EllipticEst.Q0 := by
      rintro ⟨z, θ⟩ ⟨hz, hθ⟩
      exact Work.FTS.EllipticEst.mem_Q0.mpr
        ⟨by linarith [hz.1], by linarith [hθ.1], by linarith [hθ.2]⟩
    -- ## the cut-off
    obtain ⟨χ, M, hMpos, hχsm, hχcs, hχnn, hχle1, hχone, hχzero, hM1, hM2⟩ :=
      Work.FTS.StrongLWP.Sobolev.EqcAux.exists_cutoff_rect_C2
        (a := zlo) (b := zhi) (c := tlo) (d := thi)
        (a' := zlo / 2) (b' := zhi + 1) (c' := tlo / 2) (d' := (thi + Real.pi / 2) / 2)
        hzlo'pos hzlo'lt hzlole hzhi'lt htlo'pos htlo'lt htlole hthi'lt hthi'pi
    have hχ2 : ContDiff ℝ 2 χ := by simpa using hχsm 2
    -- ## the seven rectangle `L²`-bounds at level `4` for the slot `(0,0)`
    obtain ⟨C, hCpos, hCrect⟩ := mixed_rect_L2_bounds_level (a := zlo / 2) (b := zhi + 1)
      (c := tlo / 2) (d := (thi + Real.pi / 2) / 2) hzlo'pos hzlo'le htlo'pos hthi'pi
    -- ## Morrey's inequality
    obtain ⟨Km, hKmpos, hMor⟩ := Work.FTS.StrongLWP.Sobolev.holder_half_of_W22_real
    refine ⟨Km * (2 * Real.sqrt (C + 3 * C * (16 + 17 * M ^ 2))) + 1, by positivity, ?_⟩
    intro α hα f hf p hp q hq
    have hαpos : 0 < α := hα.1
    have hFsm : Work.FTS.EllipticEst.SmoothOpen f := hf.1
    have hFmem : Work.Spaces.HkMem α 4 f := hf.2
    have hrect0 := hCrect 4 α hαpos f hFsm hFmem 0 0 (by norm_num)
    have hstep := morrey_step_four (χ := χ) (F := f) (α := α) (C := C)
      (C₀ := Work.Spaces.HkNorm α 4 f) (M := M) (Km := Km) hMor (le_of_lt hKmpos) hαpos
      hCpos (Work.Spaces.HkNorm_nonneg α 4 f) hχ2 hχcs hχnn hχle1 hχone hχzero hM1 hM2
      hboxsub hFsm hFmem (le_refl _) hrect0
    have hp' : p ∈ Set.Icc zlo zhi ×ˢ Set.Icc tlo thi := hKbox hp
    have hq' : q ∈ Set.Icc zlo zhi ×ˢ Set.Icc tlo thi := hKbox hq
    have h := hstep p hp' q hq'
    -- ## the final arithmetic: `√‖p-q‖ = dist p q ^ (1/2)` and `H ≤ 1 + H`
    have hd : Real.sqrt ‖p - q‖ = dist p q ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow, dist_eq_norm]
    rw [hd]
    refine h.trans ?_
    have hHnn : 0 ≤ Work.Spaces.HkNorm α 4 f := Work.Spaces.HkNorm_nonneg α 4 f
    have hDnn : 0 ≤ dist p q ^ (1 / 2 : ℝ) := Real.rpow_nonneg dist_nonneg _
    have hKnn : 0 ≤ Km := le_of_lt hKmpos
    have hBnn : 0 ≤ 2 * Real.sqrt (C + 3 * C * (16 + 17 * M ^ 2)) := by positivity
    have hABnn : 0 ≤ Km * (2 * Real.sqrt (C + 3 * C * (16 + 17 * M ^ 2))) := mul_nonneg hKnn hBnn
    have h1Hnn : 0 ≤ 1 + Work.Spaces.HkNorm α 4 f := by linarith
    have h1 : Km * (2 * Real.sqrt (C + 3 * C * (16 + 17 * M ^ 2))
          * Work.Spaces.HkNorm α 4 f) * dist p q ^ (1 / 2 : ℝ)
        = Km * (2 * Real.sqrt (C + 3 * C * (16 + 17 * M ^ 2)))
            * Work.Spaces.HkNorm α 4 f * dist p q ^ (1 / 2 : ℝ) := by ring
    rw [h1]
    calc Km * (2 * Real.sqrt (C + 3 * C * (16 + 17 * M ^ 2)))
          * Work.Spaces.HkNorm α 4 f * dist p q ^ (1 / 2 : ℝ)
        ≤ Km * (2 * Real.sqrt (C + 3 * C * (16 + 17 * M ^ 2)))
            * (1 + Work.Spaces.HkNorm α 4 f) * dist p q ^ (1 / 2 : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ hDnn
          exact mul_le_mul_of_nonneg_left (by linarith) hABnn
      _ ≤ (Km * (2 * Real.sqrt (C + 3 * C * (16 + 17 * M ^ 2))) + 1)
            * (1 + Work.Spaces.HkNorm α 4 f) * dist p q ^ (1 / 2 : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ hDnn
          exact mul_le_mul_of_nonneg_right (by linarith) h1Hnn

end Work.FTS.StrongEps.E5G
