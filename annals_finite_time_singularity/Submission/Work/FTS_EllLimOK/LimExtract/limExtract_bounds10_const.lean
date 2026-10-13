/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Work.FTS_EllLimOK.LimExtract.limExtract_bounds10_const`

The *constant-bound* variant of `Work.FTS_EllLimOK.LimExtract_bounds10`: the pointwise growth
bounds are now honest constants `|D_z^j D_θ^i (G n)| ≤ C` (instead of `C · wt`), still for all
orders `j + i ≤ 4` on the open quadrant `Q0 = (0,∞) × (0,π/2)`.

The conclusion is unchanged: the family `fam10 G n` of the ten mixed jets `D_z^j D_θ^i (G n)`,
`j + i ≤ 3`, is locally uniformly bounded and locally uniformly equicontinuous on the compact
subsets of `Q0` — the two hypotheses of the Arzelà–Ascoli extraction
`Work.FTS.StrongEps.LocUnif.exists_subseq_tendstoLocallyUniformlyOn_fin`.

The proof is the same as for `LimExtract_bounds10`, with the weight `wt` replaced by the
constant `1`:

* **boundedness** is immediate: every component of `fam10 G n p` is an order-`≤ 3` jet, hence
  bounded by `max C 0`;
* **equicontinuity**: a compact `K ⊆ Q0` sits inside a closed box `[a,b] × [c,d]` with
  `0 < a`, `0 < c ≤ d`, `d < π/2` (`box_of_compact_inside_Q0`); on that box,
  `∂_z (D_z^jD_θ^i(G n)) = D_z^{j+1}D_θ^i(G n)/z ≤ max C 0 / a` and
  `∂_θ (D_z^jD_θ^i(G n)) = D_z^j D_θ^{i+1}(G n)/sin 2θ ≤ max C 0 / s₀`, where
  `s₀ = (4/π)·min c (π/2 - d) > 0` is the elementary lower bound for `sin(2θ)` on `[c,d]`
  (`sin_two_ge_min_of_Icc`, proved here from `Real.mul_le_sin`), and the mean value theorem on
  the box (`abs_sub_le_of_box_bounds`) gives the Lipschitz bound.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_EllLimOK.LimExtract_bounds10

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.LimExtract

open scoped Real Topology
open MeasureTheory Set Filter

/-- **The elementary lower bound for `sin (2θ)` on a closed angular interval.**  For `0 < c` and
`d < π/2` and every `θ ∈ [c,d]`, the (positive) number `(4/π) · min c (π/2 - d)` is a lower bound
for `sin (2θ)`.

Both ingredients are elementary: `min c (π/2 - d) ≤ min θ (π/2 - θ)`, and `Real.mul_le_sin`
(`(2/π)x ≤ sin x` for `x ∈ [0,π/2]`) applied to `x = 2θ` when `θ ≤ π/4` and to `x = π - 2θ` (with
`Real.sin_pi_sub`) when `θ ≥ π/4`. -/
lemma sin_two_ge_min_of_Icc {c d θ : ℝ} (hc : 0 < c) (hd : d < Real.pi / 2)
    (hθ : θ ∈ Set.Icc c d) :
    (4 / Real.pi) * min c (Real.pi / 2 - d) ≤ Real.sin (2 * θ) := by
  have hpi := Real.pi_pos
  have hθ0 : 0 ≤ θ := le_trans (le_of_lt hc) hθ.1
  have hθ1 : θ ≤ Real.pi / 2 := le_of_lt (lt_of_le_of_lt hθ.2 hd)
  have hcoef : (0 : ℝ) ≤ 4 / Real.pi := by positivity
  have hmn : min c (Real.pi / 2 - d) ≤ min θ (Real.pi / 2 - θ) :=
    le_min (le_trans (min_le_left c (Real.pi / 2 - d)) hθ.1)
      (by have hm := min_le_right c (Real.pi / 2 - d); linarith [hθ.2])
  have h1 : (4 / Real.pi) * min c (Real.pi / 2 - d)
      ≤ (4 / Real.pi) * min θ (Real.pi / 2 - θ) :=
    mul_le_mul_of_nonneg_left hmn hcoef
  rcases le_total θ (Real.pi / 4) with h | h
  · have hmn' : min θ (Real.pi / 2 - θ) = θ := min_eq_left (by linarith)
    rw [hmn'] at h1
    have h2 : 2 / Real.pi * (2 * θ) ≤ Real.sin (2 * θ) :=
      Real.mul_le_sin (by linarith) (by linarith)
    have h3 : 2 / Real.pi * (2 * θ) = (4 / Real.pi) * θ := by ring
    linarith [h1, h2, h3.le, h3.ge]
  · have hmn' : min θ (Real.pi / 2 - θ) = Real.pi / 2 - θ := min_eq_right (by linarith)
    rw [hmn'] at h1
    have h2 : 2 / Real.pi * (Real.pi - 2 * θ) ≤ Real.sin (Real.pi - 2 * θ) :=
      Real.mul_le_sin (by linarith) (by linarith)
    rw [Real.sin_pi_sub] at h2
    have h3 : 2 / Real.pi * (Real.pi - 2 * θ) = (4 / Real.pi) * (Real.pi / 2 - θ) := by ring
    linarith [h1, h2, h3.le, h3.ge]

theorem limExtract_bounds10_const {C : ℝ} {G : ℕ → ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (G n))
    (hbnd : ∀ (n : ℕ) (j i : ℕ), j + i ≤ 4 → ∀ z θ : ℝ,
      (z, θ) ∈ Work.FTS.EllipticEst.Q0 → |Work.Spaces.mixed j i (G n) z θ| ≤ C) :
    (∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 → ∃ C' : ℝ,
        ∀ (n : ℕ) (p : ℝ × ℝ), p ∈ K → ‖Work.FTS_EllLimOK.fam10 G n p‖ ≤ C') ∧
      (∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 → ∀ ε : ℝ, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (p : ℝ × ℝ), p ∈ K → ∀ q : ℝ × ℝ, q ∈ K →
          dist p q < δ → ‖Work.FTS_EllLimOK.fam10 G n p - Work.FTS_EllLimOK.fam10 G n q‖ < ε) := by
  -- replace `C` by `max C 0`, so that the bound is a nonnegative constant
  have hM : ∀ (n j i : ℕ), j + i ≤ 4 → ∀ z θ : ℝ,
      (z, θ) ∈ Work.FTS.EllipticEst.Q0 → |Work.Spaces.mixed j i (G n) z θ| ≤ max C 0 :=
    fun n j i hji z θ hQ => le_trans (hbnd n j i hji z θ hQ) (le_max_left C 0)
  constructor
  · -- (1) local uniform boundedness of the family on compact subsets of the open quadrant
    intro K hKc hKQ
    refine ⟨max C 0, ?_⟩
    intro n p hp
    rw [pi_norm_le_iff_of_nonneg (le_max_right C 0)]
    intro m
    have hsum := P10_sum_le_three m
    simpa only [Work.FTS_EllLimOK.fam10, Real.norm_eq_abs] using
      hM n (P10 m).1 (P10 m).2 (by omega) p.1 p.2 (hKQ hp)
  · -- (2) local uniform equicontinuity of the family on compact subsets of the open quadrant
    intro K hKc hKQ ε hε
    rcases Set.eq_empty_or_nonempty K with rfl | hne
    · -- the empty compact set: any `δ` works
      exact ⟨1, one_pos, fun n p hp => absurd hp (Set.notMem_empty p)⟩
    obtain ⟨a, b, c, d, ha, hab, hc, hcd, hd, hbox⟩ :=
      Work.FTS_EllLimOK.box_of_compact_inside_Q0 hKc hKQ hne
    -- the box lies in the open quadrant
    have hboxQ : Set.Icc a b ×ˢ Set.Icc c d ⊆ Work.FTS.EllipticEst.Q0 := by
      intro p hp
      obtain ⟨hp1, hp2⟩ := Set.mem_prod.mp hp
      rw [Work.FTS.EllipticEst.mem_Q0]
      exact ⟨lt_of_lt_of_le ha hp1.1, lt_of_lt_of_le hc hp2.1, lt_of_le_of_lt hp2.2 hd⟩
    -- the angular lower bound `s₀ > 0` for `sin(2θ)` on `[c,d]`
    set s0 : ℝ := (4 / Real.pi) * min c (Real.pi / 2 - d) with hs0def
    have hs0pos : 0 < s0 := by
      rw [hs0def]; exact mul_pos (by positivity) (lt_min hc (by linarith))
    have hs0le : ∀ θ ∈ Set.Icc c d, s0 ≤ Real.sin (2 * θ) := by
      intro θ hθI; rw [hs0def]; exact sin_two_ge_min_of_Icc hc hd hθI
    -- the `∂_z`-derivative of an order-`≤ 3` jet, divided by `z`, is bounded by `M / a` on the box
    have hpz : ∀ (n j i : ℕ), j + i ≤ 3 → ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
        |Work.Spaces.pz (Work.Spaces.mixed j i (G n)) z θ| ≤ max C 0 / a := by
      intro n j i hji z hz θ hθI
      have hQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := hboxQ (Set.mem_prod.mpr ⟨hz, hθI⟩)
      obtain ⟨hzpos, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hQ
      rw [(Work.FTS.StrongEps.LocUnif.mixed_partials_of_smoothOpen j i (hsm n)).1 z θ hQ]
      have hb := hM n (j + 1) i (by omega) z θ hQ
      rw [abs_div, abs_of_pos hzpos, div_le_div_iff₀ hzpos ha]
      calc |Work.Spaces.mixed (j + 1) i (G n) z θ| * a ≤ max C 0 * a :=
            mul_le_mul_of_nonneg_right hb (le_of_lt ha)
        _ ≤ max C 0 * z := mul_le_mul_of_nonneg_left hz.1 (le_max_right C 0)
    -- the `∂_θ`-derivative of an order-`≤ 3` jet, divided by `sin 2θ`, is bounded by `M / s₀`
    have hpth : ∀ (n j i : ℕ), j + i ≤ 3 → ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
        |Work.Spaces.pth (Work.Spaces.mixed j i (G n)) z θ| ≤ max C 0 / s0 := by
      intro n j i hji z hz θ hθI
      have hQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := hboxQ (Set.mem_prod.mpr ⟨hz, hθI⟩)
      obtain ⟨hzpos, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hQ
      have hsin : 0 < Real.sin (2 * θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
      rw [(Work.FTS.StrongEps.LocUnif.mixed_partials_of_smoothOpen j i (hsm n)).2.1 z θ hQ]
      have hb := hM n j (i + 1) (by omega) z θ hQ
      rw [abs_div, abs_of_pos hsin, div_le_div_iff₀ hsin hs0pos]
      calc |Work.Spaces.mixed j (i + 1) (G n) z θ| * s0 ≤ max C 0 * s0 :=
            mul_le_mul_of_nonneg_right hb (le_of_lt hs0pos)
        _ ≤ max C 0 * Real.sin (2 * θ) :=
            mul_le_mul_of_nonneg_left (hs0le θ hθI) (le_max_right C 0)
    -- the common Lipschitz constant on the box
    set L : ℝ := max (max C 0 / a) (max C 0 / s0) + 1 with hLdef
    have hLpos : 0 < L := by
      rw [hLdef]
      have h0 : 0 ≤ max (max C 0 / a) (max C 0 / s0) :=
        le_trans (div_nonneg (le_max_right C 0) (le_of_lt ha)) (le_max_left _ _)
      linarith
    have hLz : max C 0 / a ≤ L := by
      rw [hLdef]; have := le_max_left (max C 0 / a) (max C 0 / s0); linarith
    have hLth : max C 0 / s0 ≤ L := by
      rw [hLdef]; have := le_max_right (max C 0 / a) (max C 0 / s0); linarith
    -- slice differentiability in `z`, at fixed angle
    have hslice_z : ∀ (n j i : ℕ), ∀ θ ∈ Set.Icc c d, ∀ z ∈ Set.Icc a b,
        HasDerivWithinAt (fun z' : ℝ => Work.Spaces.mixed j i (G n) z' θ)
          (Work.Spaces.pz (Work.Spaces.mixed j i (G n)) z θ) (Set.Icc a b) z := by
      intro n j i θ hθI z hz
      have hQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := hboxQ (Set.mem_prod.mpr ⟨hz, hθI⟩)
      obtain ⟨hzpos, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hQ
      exact (((hsm n).mixed j i).hasDerivAt_slice ⟨hθ0, hθ1⟩ hzpos).hasDerivWithinAt
    -- slice differentiability in `θ`, at fixed radius
    have hslice_θ : ∀ (n j i : ℕ), ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
        HasDerivWithinAt (fun θ' : ℝ => Work.Spaces.mixed j i (G n) z θ')
          (Work.Spaces.pth (Work.Spaces.mixed j i (G n)) z θ) (Set.Icc c d) θ := by
      intro n j i z hz θ hθI
      have hQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := hboxQ (Set.mem_prod.mpr ⟨hz, hθI⟩)
      obtain ⟨hzpos, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hQ
      exact (Work.FTS_EllLimOK.smoothOpen_hasDerivAt_slice_theta ((hsm n).mixed j i) hzpos
        ⟨hθ0, hθ1⟩).hasDerivWithinAt
    -- every component of the family is `L`-Lipschitz on the box, hence on `K`
    have hcoord : ∀ (n : ℕ) (m : Fin 10) (p q : ℝ × ℝ), p ∈ K → q ∈ K →
        |Work.FTS_EllLimOK.fam10 G n p m - Work.FTS_EllLimOK.fam10 G n q m|
          ≤ L * (|p.1 - q.1| + |p.2 - q.2|) := by
      intro n m p q hp hq
      have hb := Work.FTS_EllLimOK.abs_sub_le_of_box_bounds
        (g := Work.Spaces.mixed (P10 m).1 (P10 m).2 (G n))
        (hslice_z n (P10 m).1 (P10 m).2) (hslice_θ n (P10 m).1 (P10 m).2)
        (fun z hz θ hθI =>
          le_trans (hpz n (P10 m).1 (P10 m).2 (P10_sum_le_three m) z hz θ hθI) hLz)
        (fun z hz θ hθI =>
          le_trans (hpth n (P10 m).1 (P10 m).2 (P10_sum_le_three m) z hz θ hθI) hLth)
        p (hbox hp) q (hbox hq)
      simpa only [Work.FTS_EllLimOK.fam10] using hb
    -- the `ε`-`δ` step
    refine ⟨ε / (4 * (L + 1)), by positivity, ?_⟩
    intro n p hp q hq hdist
    have hL1pos : 0 < L + 1 := by linarith
    have hmax1 : |p.1 - q.1| ≤ dist p q := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      exact le_max_left _ _
    have hmax2 : |p.2 - q.2| ≤ dist p q := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      exact le_max_right _ _
    have hsum : |p.1 - q.1| + |p.2 - q.2| ≤ 2 * dist p q := by linarith
    have hbound : ‖Work.FTS_EllLimOK.fam10 G n p - Work.FTS_EllLimOK.fam10 G n q‖ ≤ ε / 2 := by
      rw [pi_norm_le_iff_of_nonneg (by positivity : (0 : ℝ) ≤ ε / 2)]
      intro m
      change ‖Work.FTS_EllLimOK.fam10 G n p m - Work.FTS_EllLimOK.fam10 G n q m‖ ≤ ε / 2
      have hcm := hcoord n m p q hp hq
      have hstep1 : |Work.FTS_EllLimOK.fam10 G n p m - Work.FTS_EllLimOK.fam10 G n q m|
          ≤ L * (2 * dist p q) :=
        le_trans hcm (mul_le_mul_of_nonneg_left hsum (le_of_lt hLpos))
      have hstep2 : L * (2 * dist p q) ≤ (L + 1) * (2 * dist p q) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have hstep3 : (L + 1) * (2 * dist p q) < (L + 1) * (2 * (ε / (4 * (L + 1)))) :=
        mul_lt_mul_of_pos_left (by linarith) hL1pos
      have hstep4 : (L + 1) * (2 * (ε / (4 * (L + 1)))) = ε / 2 := by
        have hne : L + 1 ≠ 0 := ne_of_gt hL1pos
        field_simp
        norm_num
      rw [Real.norm_eq_abs]
      linarith
    linarith

end Work.FTS_EllLimOK.LimExtract
