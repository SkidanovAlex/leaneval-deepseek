import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.NonlinRows.Rl1.angSupHk
import Submission.Work.Spaces.Linf_H2
import Submission.Work.H2.T1Q.SliceSupOpen
import Submission.Work.FTS.StrongLWP.Sobolev.supAbs_mixed_le
import Submission.Work.FTS.StrongEps.LocUnif.mixed_rect_L2_bounds
import Submission.Work.FTS.StrongEps.LocUnif.rect_deriv_bounds
import Submission.Work.FTS.StrongEps.LocUnif.basis_apply_two
import Submission.Work.FTS.StrongLWP.Sobolev.EqcAux.exists_cutoff_rect_C2
import Submission.Work.FTS.StrongLWP.Sobolev.holder_half_of_W22
import Submission.Work.FTS.StrongLWP.Sobolev.HolderHalf.sup_le_of_holder
import Submission.Work.FTS.StrongEps.HQoAux.cut_slot_L2_bounds
import Submission.Work.FTS_EllLimOK.box_of_compact_inside_Q0

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## A Morrey-type bound on compacts for the open class `HQo α 6`

`Work.FTS.VocabO.HQo α 6 f` carries only open-quadrant smoothness and the honest membership
`HkMem α 6 f`; in particular there is no angular vanishing and no decay at `z = ∞`, so the
route of `Work.FTS.StrongLWP.Sobolev.supAbs_mixed_le` (Hardy inequalities on the whole
quadrant) is not available.  On a *compact* `K ⊆ Q0 = (0,∞) × (0,π/2)` however the classical
2-dimensional Sobolev/Morrey mechanism applies:

* a compact subset of the open quadrant sits in a closed box whose two-fold enlargement still
  lies in `Q0` (`Work.FTS_EllLimOK.box_of_compact_inside_Q0` plus padding);
* cut off by a smooth `χ` which is `1` on the box and vanishes off its enlargement
  (`Work.FTS.StrongLWP.Sobolev.EqcAux.exists_cutoff_rect_C2`);
* the products `χ · D_z^bD_θ^a f` are `C²` with compact support
  (`Work.FTS.StrongEps.LocUnif.contDiff_two_mul_of_contDiffOn_two`,
  `Work.FTS.StrongLWP.Sobolev.eqc_hasCompactSupport_mul`), and their `L²`-norms of order `0`
  and `2` are dominated by `HkNorm α 6 f` (`cut_slot_L2_bounds`, whose proof reads the box
  integrals of the mixed slots off `mixed_rect_L2_bounds`);
* Morrey's inequality `W^{2,2}(ℝ²) ⊂ C^{0,1/2}`
  (`Work.FTS.StrongLWP.Sobolev.holder_half_of_W22_real`) then gives a Hölder-`1/2` modulus
  proportional to those two `L²`-norms, and the averaging lemma
  `Work.FTS.StrongLWP.Sobolev.HolderHalf.sup_le_of_holder` converts the modulus plus the
  `L²`-bound into a *pointwise* bound.

Everything is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`. -/

theorem HQo_mixed_abs_le_on_compact {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {f : Work.FTS.Galerkin.Fn} (hf : Work.FTS.VocabO.HQo α 6 f)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKQ : K ⊆ Work.FTS.EllipticEst.Q0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (b a : ℕ), a + b ≤ 4 → ∀ z θ : ℝ, (z, θ) ∈ K →
      |Work.Spaces.mixed b a f z θ| ≤ C * Work.Spaces.HkNorm α 6 f := by
  rcases Set.eq_empty_or_nonempty K with hKe | hne
  · subst hKe
    exact ⟨1, one_pos, fun b a _ z θ hp => absurd hp (by simp)⟩
  · -- ## A box `[zlo,zhi] × [tlo,thi]` containing `K`, with a two-fold enlargement in `Q0`
    obtain ⟨zlo, zhi, tlo, thi, hzlopos, hzlole, htlopos, htlole, hthilt, hKbox⟩ :=
      Work.FTS_EllLimOK.box_of_compact_inside_Q0 hK hKQ hne
    have hthipi : thi < Real.pi / 2 := hthilt
    -- the enlarged box
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
    -- ## the two `L²`-bounds for `χ · D_z^bD_θ^a f`
    obtain ⟨C1, C2, hC1pos, hC2pos, hL2⟩ :=
      Work.FTS.StrongEps.HQoAux.cut_slot_L2_bounds hα hf.1 hf.2 hzlo'pos hzlo'le htlo'pos
        hthi'pi hχ2 hχnn hχle1 hχzero hM1 hM2
    -- ## Morrey's inequality and its averaging form
    obtain ⟨Cm, hCmpos, hMor⟩ := Work.FTS.StrongLWP.Sobolev.holder_half_of_W22_real
    refine ⟨Cm * (Real.sqrt C1 + Real.sqrt C2) + Real.sqrt C1 / 2 + 1, by positivity, ?_⟩
    intro b a hab z θ hzθ
    -- the slot, cut off
    set G : ℝ → ℝ → ℝ := Work.Spaces.mixed b a f with hGdef
    set v : ℝ × ℝ → ℝ := fun x => χ x * Function.uncurry G x with hvdef
    have hG2 : ContDiffOn ℝ 2 (Function.uncurry G) Work.FTS.EllipticEst.Q0 := by
      have h := (hf.1.mixed b a).of_le Work.FTS.StrongEps.LocUnif.two_le_smoothOrder
      simpa only [hGdef] using h
    have hv2 : ContDiff ℝ 2 v := by
      have h := Work.FTS.StrongEps.LocUnif.contDiff_two_mul_of_contDiffOn_two
        (χ := χ) (g := Function.uncurry G)
        (s := Set.Icc (zlo / 2) (zhi + 1) ×ˢ Set.Icc (tlo / 2) ((thi + Real.pi / 2) / 2))
        (U := Work.FTS.EllipticEst.Q0)
        (isClosed_Icc.prod isClosed_Icc) hboxsub Work.FTS.EllipticEst.isOpen_Q0 hχ2 hχzero hG2
      simpa only [hvdef] using h
    have hv1 : ContDiff ℝ 1 v := hv2.of_le (by norm_num)
    have hvcs : HasCompactSupport v := by
      have h := Work.FTS.StrongLWP.Sobolev.eqc_hasCompactSupport_mul
        (χ := χ) (g := Function.uncurry G) hχcs
      simpa only [hvdef] using h
    obtain ⟨hL2val, hL2hess⟩ := hL2 b a hab
    have hL2val' : (∫ x : ℝ × ℝ, (v x) ^ 2) ≤ C1 * Work.Spaces.HkSq α 6 f := by
      simpa only [hvdef, hGdef] using hL2val
    have hL2hess' : (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2)
        ≤ C2 * Work.Spaces.HkSq α 6 f := by
      simpa only [hvdef, hGdef] using hL2hess
    have hMnn : 0 ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
    have hM2 : Real.sqrt (Work.Spaces.HkSq α 6 f) = Work.Spaces.HkNorm α 6 f := rfl
    have hs1 : Real.sqrt (∫ x : ℝ × ℝ, (v x) ^ 2)
        ≤ Real.sqrt C1 * Work.Spaces.HkNorm α 6 f := by
      calc Real.sqrt (∫ x : ℝ × ℝ, (v x) ^ 2)
          ≤ Real.sqrt (C1 * Work.Spaces.HkSq α 6 f) := Real.sqrt_le_sqrt hL2val'
        _ = Real.sqrt C1 * Real.sqrt (Work.Spaces.HkSq α 6 f) := Real.sqrt_mul hC1pos.le _
        _ = Real.sqrt C1 * Work.Spaces.HkNorm α 6 f := by rw [hM2]
    have hs2 : Real.sqrt (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2)
        ≤ Real.sqrt C2 * Work.Spaces.HkNorm α 6 f := by
      calc Real.sqrt (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2)
          ≤ Real.sqrt (C2 * Work.Spaces.HkSq α 6 f) := Real.sqrt_le_sqrt hL2hess'
        _ = Real.sqrt C2 * Real.sqrt (Work.Spaces.HkSq α 6 f) := Real.sqrt_mul hC2pos.le _
        _ = Real.sqrt C2 * Work.Spaces.HkNorm α 6 f := by rw [hM2]
    -- the Hölder modulus of `v`, from Morrey
    have hmod : ∀ p q : ℝ × ℝ, |v p - v q|
        ≤ (Cm * (Real.sqrt C1 + Real.sqrt C2) * Work.Spaces.HkNorm α 6 f)
            * Real.sqrt (dist p q) := by
      intro p q
      have h := hMor v hv2 hvcs p q
      have hd0 : 0 ≤ dist p q := dist_nonneg
      have hspow : Real.sqrt (dist p q) = dist p q ^ (1 / 2 : ℝ) :=
        Real.sqrt_eq_rpow (dist p q)
      have hstep : Cm * (Real.sqrt (∫ x : ℝ × ℝ, (v x) ^ 2)
            + Real.sqrt (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2)) * dist p q ^ (1 / 2 : ℝ)
          ≤ (Cm * (Real.sqrt C1 + Real.sqrt C2) * Work.Spaces.HkNorm α 6 f)
            * Real.sqrt (dist p q) := by
        rw [← hspow]
        have hsum : Real.sqrt (∫ x : ℝ × ℝ, (v x) ^ 2)
              + Real.sqrt (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2)
            ≤ (Real.sqrt C1 + Real.sqrt C2) * Work.Spaces.HkNorm α 6 f := by
          have := add_le_add hs1 hs2
          linarith
        calc Cm * (Real.sqrt (∫ x : ℝ × ℝ, (v x) ^ 2)
              + Real.sqrt (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2)) * Real.sqrt (dist p q)
            ≤ Cm * ((Real.sqrt C1 + Real.sqrt C2) * Work.Spaces.HkNorm α 6 f)
                * Real.sqrt (dist p q) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hsum (le_of_lt hCmpos)) (Real.sqrt_nonneg _)
          _ = (Cm * (Real.sqrt C1 + Real.sqrt C2) * Work.Spaces.HkNorm α 6 f)
                * Real.sqrt (dist p q) := by ring
      exact h.trans hstep
    have hsup := Work.FTS.StrongLWP.Sobolev.HolderHalf.sup_le_of_holder hv1 hvcs
      (Cm * (Real.sqrt C1 + Real.sqrt C2) * Work.Spaces.HkNorm α 6 f)
      (by positivity) hmod (z, θ)
    -- the cut-off is `1` at the point
    have hpk : (z, θ) ∈ Set.Icc zlo zhi ×ˢ Set.Icc tlo thi := hKbox hzθ
    have hχp : χ (z, θ) = 1 := hχone z hpk.1 θ hpk.2
    have hvp : v (z, θ) = Work.Spaces.mixed b a f z θ := by
      simp only [hvdef, hGdef, Function.uncurry, hχp, one_mul]
    calc |Work.Spaces.mixed b a f z θ|
        = |v (z, θ)| := by rw [hvp]
      _ ≤ Cm * (Real.sqrt C1 + Real.sqrt C2) * Work.Spaces.HkNorm α 6 f
            + Real.sqrt (∫ x : ℝ × ℝ, (v x) ^ 2) / 2 := hsup
      _ ≤ Cm * (Real.sqrt C1 + Real.sqrt C2) * Work.Spaces.HkNorm α 6 f
            + Real.sqrt C1 * Work.Spaces.HkNorm α 6 f / 2 := by linarith
      _ ≤ (Cm * (Real.sqrt C1 + Real.sqrt C2) + Real.sqrt C1 / 2 + 1)
            * Work.Spaces.HkNorm α 6 f := by nlinarith [hMnn]

end Work.FTS.StrongEps
