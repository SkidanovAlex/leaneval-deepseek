import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongEps.LocUnif.mixed_rect_L2_bounds
import Submission.Work.FTS.StrongEps.LocUnif.rect_deriv_bounds
import Submission.Work.FTS.StrongEps.LocUnif.basis_apply_two
import Submission.Work.FTS.StrongEps.HQoAux.cut_slot_L2_bounds_uniform
import Submission.Work.FTS.StrongLWP.Sobolev.EqcAux.exists_cutoff_rect_C2
import Submission.Work.FTS.StrongLWP.Sobolev.holder_half_of_W22
import Submission.Work.FTS.StrongLWP.Sobolev.HolderHalf.sup_le_of_holder
import Submission.Work.FTS_EllLimOK.box_of_compact_inside_Q0

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-! ## The `α`-uniform Morrey bound on compacts for the open class `HQo α 6`

`Work.FTS.StrongEps.HQo_mixed_abs_le_on_compact` gives, for each *fixed* `α ∈ (0,1]`, a
constant `C = C(α,K)` with `|D_z^bD_θ^a f| ≤ C · HkNorm α 6 f` on a compact `K ⊆ Q0`.  The
block needed here is the *uniform* version: one constant `C = C(K)` valid simultaneously for
all `α ∈ (0,1]` and all `f`.  The only place where uniformity could fail is the pair of
`L²`-bounds for the cut-off products `χ · D_z^bD_θ^a f`, which are taken from
`Work.FTS.StrongEps.HQoAux.cut_slot_L2_bounds_uniform`: the existing
`Work.FTS.StrongEps.HQoAux.cut_slot_L2_bounds` with its constants pulled out in front of `α`
and `f` (they were already independent of both, since they come from
`Work.FTS.StrongEps.LocUnif.mixed_rect_L2_bounds`, whose constant is `α`-free).
Everything after that -- the box, the cut-off, Morrey and the averaging lemma -- is
`α`-independent and is copied from the per-`α` proof. -/

namespace Work.FTS.StrongEps.blocks

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The `α`-uniform Morrey bound on compacts for the open class `HQo α 6`.**

For a compact `K ⊆ Q0 = (0,∞) × (0,π/2)` there is a single constant `C = C(K)` such that for
every `α ∈ (0,1]`, every `f : Fn` with `HQo α 6 f` and every slot `D_z^bD_θ^a f` with
`a + b ≤ 4`, the pointwise bound `|D_z^bD_θ^a f z θ| ≤ C · HkNorm α 6 f` holds on `K`.

This is the `α`-uniform refinement of `Work.FTS.StrongEps.HQo_mixed_abs_le_on_compact` (whose
constant is allowed to depend on `α`).  The argument is the same 2-dimensional Sobolev/Morrey
mechanism: a compact subset of the open quadrant sits in a box whose two-fold enlargement still
lies in `Q0`, a `C²` cut-off `χ` supported in the enlargement is `1` on the box, the products
`χ · D_z^bD_θ^a f` are `C²` with compact support, their `L²`-norms of order `0` and `2` are
dominated by `HkNorm α 6 f`, and Morrey's inequality `W^{2,2}(ℝ²) ⊂ C^{0,1/2}` together with
the averaging lemma converts that into a pointwise bound.  Uniformity in `α` is exactly the
statement `Work.FTS.StrongEps.HQoAux.cut_slot_L2_bounds_uniform`: the box, the cut-off, the
two `L²`-constants, Morrey's constant `Cm` and the averaging constant do not mention `α` or
`f`. -/
theorem HQo_mixed_abs_le_on_compact_uniform {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKQ : K ⊆ Work.FTS.EllipticEst.Q0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (f : Work.FTS.Galerkin.Fn),
      Work.FTS.VocabO.HQo α 6 f → ∀ (b a : ℕ), a + b ≤ 4 → ∀ z θ : ℝ, (z, θ) ∈ K →
      |Work.Spaces.mixed b a f z θ| ≤ C * Work.Spaces.HkNorm α 6 f := by
  rcases Set.eq_empty_or_nonempty K with hKe | hne
  · subst hKe
    exact ⟨1, one_pos, fun α ha ha1 f hf b a hab z θ hp => absurd hp (by simp)⟩
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
    -- ## the two `L²`-bounds for `χ · D_z^bD_θ^a f`, with constants independent of `α` and `f`
    obtain ⟨C1, C2, hC1pos, hC2pos, hL2⟩ :=
      Work.FTS.StrongEps.HQoAux.cut_slot_L2_bounds_uniform hzlo'pos hzlo'le
        htlo'pos hthi'pi hχ2 hχnn hχle1 hχzero hM1 hM2
    -- ## Morrey's inequality and its averaging form
    obtain ⟨Cm, hCmpos, hMor⟩ := Work.FTS.StrongLWP.Sobolev.holder_half_of_W22_real
    refine ⟨Cm * (Real.sqrt C1 + Real.sqrt C2) + Real.sqrt C1 / 2 + 1, by positivity, ?_⟩
    intro α hα hα1 f hf b a hab z θ hzθ
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
    obtain ⟨hL2val, hL2hess⟩ := hL2 α hα f hf.1 hf.2 b a hab
    have hL2val' : (∫ x : ℝ × ℝ, (v x) ^ 2) ≤ C1 * Work.Spaces.HkSq α 6 f := by
      simpa only [hvdef, hGdef] using hL2val
    have hL2hess' : (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2)
        ≤ C2 * Work.Spaces.HkSq α 6 f := by
      simpa only [hvdef, hGdef] using hL2hess
    have hMnn : 0 ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
    have hMnorm : Real.sqrt (Work.Spaces.HkSq α 6 f) = Work.Spaces.HkNorm α 6 f := rfl
    have hs1 : Real.sqrt (∫ x : ℝ × ℝ, (v x) ^ 2)
        ≤ Real.sqrt C1 * Work.Spaces.HkNorm α 6 f := by
      calc Real.sqrt (∫ x : ℝ × ℝ, (v x) ^ 2)
          ≤ Real.sqrt (C1 * Work.Spaces.HkSq α 6 f) := Real.sqrt_le_sqrt hL2val'
        _ = Real.sqrt C1 * Real.sqrt (Work.Spaces.HkSq α 6 f) := Real.sqrt_mul hC1pos.le _
        _ = Real.sqrt C1 * Work.Spaces.HkNorm α 6 f := by rw [hMnorm]
    have hs2 : Real.sqrt (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2)
        ≤ Real.sqrt C2 * Work.Spaces.HkNorm α 6 f := by
      calc Real.sqrt (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2)
          ≤ Real.sqrt (C2 * Work.Spaces.HkSq α 6 f) := Real.sqrt_le_sqrt hL2hess'
        _ = Real.sqrt C2 * Real.sqrt (Work.Spaces.HkSq α 6 f) := Real.sqrt_mul hC2pos.le _
        _ = Real.sqrt C2 * Work.Spaces.HkNorm α 6 f := by rw [hMnorm]
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

end Work.FTS.StrongEps.blocks
