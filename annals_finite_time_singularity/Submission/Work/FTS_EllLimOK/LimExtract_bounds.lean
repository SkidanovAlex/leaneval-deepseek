import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.LocUnif.mixed_partials_of_smoothOpen
import Submission.Work.FTS_EllLimOK.wt_bddAbove_of_compact
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.Spaces.one_le_mul_w

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## Auxiliary facts -/

/-- Every pair occurring in the list `P6` has total order at most `2`. -/
theorem P6_sum_le_two (m : Fin 6) : (P6 m).1 + (P6 m).2 ≤ 2 := by
  fin_cases m <;> decide

/-- The `θ`-slice of a function of class `C^∞` on the open quadrant is differentiable at every
interior angle, with derivative the plain partial derivative `pth`. -/
theorem smoothOpen_hasDerivAt_slice_theta {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (fun θ' : ℝ => F z θ') (Work.Spaces.pth F z θ) θ := by
  have hd : DifferentiableAt ℝ (fun θ' : ℝ => F z θ') θ :=
    ((hF.curry_θ hz).differentiableOn (by rw [Work.Stability.smoothOrder]; simp)).differentiableAt
      (isOpen_Ioo.mem_nhds hθ)
  exact hd.hasDerivAt

/-- Nonnegativity of the weight `wt` on the open quadrant. -/
theorem wt_pos_of_mem_Q0 {z θ : ℝ} (h : (z, θ) ∈ Work.FTS.EllipticEst.Q0) : 0 ≤ wt z θ := by
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp h
  have h1 : 0 < 1 / z := one_div_pos.mpr hz
  have h2 : 0 < θ * (Real.pi / 2 - θ) := mul_pos hθ0 (by linarith)
  have h3 : 0 < 1 / (θ * (Real.pi / 2 - θ)) := one_div_pos.mpr h2
  have h4 : 0 < 1 + z := by linarith
  have h5 : 0 < 1 + 1 / z + 1 / (θ * (Real.pi / 2 - θ)) := by linarith
  rw [wt]
  exact le_of_lt (div_pos h5 h4)

/-! ## The extraction bounds -/

theorem LimExtract_bounds {C : ℝ} {G : ℕ → ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (G n))
    (hbnd : ∀ (n : ℕ) (j i : ℕ), j + i ≤ 3 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      |Work.Spaces.mixed j i (G n) z θ| ≤ C * Work.FTS_EllLimOK.wt z θ) :
    (∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 → ∃ C' : ℝ,
        ∀ (n : ℕ) (p : ℝ × ℝ), p ∈ K → ‖Work.FTS_EllLimOK.fam6 G n p‖ ≤ C') ∧
      (∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 → ∀ ε : ℝ, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (p : ℝ × ℝ), p ∈ K → ∀ q : ℝ × ℝ, q ∈ K →
          dist p q < δ → ‖Work.FTS_EllLimOK.fam6 G n p - Work.FTS_EllLimOK.fam6 G n q‖ < ε) := by
  -- replace `C` by `max C 0`, so that the bound can be multiplied by a nonnegative factor
  have hbnd' : ∀ (n j i : ℕ), j + i ≤ 3 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      |Work.Spaces.mixed j i (G n) z θ| ≤ max C 0 * wt z θ := by
    intro n j i hji z θ hQ
    have h1 := hbnd n j i hji z θ hQ
    have hw := wt_pos_of_mem_Q0 hQ
    rcases le_total C 0 with hC | hC
    · have hle : C * wt z θ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC hw
      have h2 : 0 ≤ max C 0 * wt z θ := mul_nonneg (le_max_right C 0) hw
      have h3 : 0 ≤ |Work.Spaces.mixed j i (G n) z θ| := abs_nonneg _
      linarith
    · exact le_trans h1 (mul_le_mul_of_nonneg_right (le_max_left C 0) hw)
  constructor
  · -- (1) local uniform boundedness of the family on compact subsets of the open quadrant
    intro K hKc hKQ
    obtain ⟨M, -, hM, -⟩ := Work.FTS_EllLimOK.wt_bddAbove_of_compact hKc hKQ
    refine ⟨max 0 (max C 0 * M), ?_⟩
    intro n p hp
    rw [pi_norm_le_iff_of_nonneg (le_max_left 0 (max C 0 * M))]
    intro m
    have hP6 := P6_sum_le_two m
    have hQ : p ∈ Work.FTS.EllipticEst.Q0 := hKQ hp
    have h1 := hbnd' n (P6 m).1 (P6 m).2 (by omega) p.1 p.2 hQ
    have h2 : max C 0 * wt p.1 p.2 ≤ max C 0 * M :=
      mul_le_mul_of_nonneg_left (hM p hp) (le_max_right C 0)
    calc ‖fam6 G n p m‖ = |Work.Spaces.mixed (P6 m).1 (P6 m).2 (G n) p.1 p.2| := by
          simp only [fam6, Real.norm_eq_abs]
      _ ≤ max 0 (max C 0 * M) := le_trans h1 (le_trans h2 (le_max_right 0 _))
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
    have hboxc : IsCompact (Set.Icc a b ×ˢ Set.Icc c d) := isCompact_Icc.prod isCompact_Icc
    obtain ⟨M, N, hM, hN⟩ := Work.FTS_EllLimOK.wt_bddAbove_of_compact hboxc hboxQ
    -- the common Lipschitz constant on the box
    set L : ℝ := |max C 0 * N| + 1 with hLdef
    have hLpos : 0 < L := by rw [hLdef]; linarith [abs_nonneg (max C 0 * N)]
    have hCNL : max C 0 * N ≤ L := by
      rw [hLdef]; linarith [le_abs_self (max C 0 * N)]
    -- the `∂_z`-derivative of an order-`≤ 2` jet, divided by `z`, is bounded by `L` on the box
    have hpz_bound : ∀ (n j i : ℕ), j + i ≤ 2 → ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
        |Work.Spaces.pz (Work.Spaces.mixed j i (G n)) z θ| ≤ L := by
      intro n j i hji z hzI θ hθI
      have hQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := hboxQ (Set.mem_prod.mpr ⟨hzI, hθI⟩)
      obtain ⟨hzpos, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hQ
      rw [(Work.FTS.StrongEps.LocUnif.mixed_partials_of_smoothOpen j i (hsm n)).1 z θ hQ]
      have hb := hbnd' n (j + 1) i (by omega) z θ hQ
      have hw := wt_pos_of_mem_Q0 hQ
      have hsin : 0 < Real.sin (2 * θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
      have hN' := hN (z, θ) (Set.mem_prod.mpr ⟨hzI, hθI⟩)
      have hC0 : 0 ≤ max C 0 := le_max_right C 0
      have hzinv : 0 ≤ 1 / z := le_of_lt (one_div_pos.mpr hzpos)
      have hsininv : 0 ≤ 1 / Real.sin (2 * θ) := le_of_lt (one_div_pos.mpr hsin)
      rw [abs_div, abs_of_pos hzpos, div_eq_mul_one_div]
      calc |Work.Spaces.mixed (j + 1) i (G n) z θ| * (1 / z)
          ≤ max C 0 * wt z θ * (1 / z) := mul_le_mul_of_nonneg_right hb hzinv
        _ = max C 0 * (wt z θ * (1 / z)) := by ring
        _ ≤ max C 0 * (wt z θ * (1 / z + 1 / Real.sin (2 * θ))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hsininv) hw) hC0
        _ ≤ max C 0 * N := mul_le_mul_of_nonneg_left hN' hC0
        _ ≤ L := hCNL
    -- the `∂_θ`-derivative of an order-`≤ 2` jet, divided by `sin 2θ`, is bounded by `L` too
    have hpth_bound : ∀ (n j i : ℕ), j + i ≤ 2 → ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
        |Work.Spaces.pth (Work.Spaces.mixed j i (G n)) z θ| ≤ L := by
      intro n j i hji z hzI θ hθI
      have hQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := hboxQ (Set.mem_prod.mpr ⟨hzI, hθI⟩)
      obtain ⟨hzpos, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hQ
      rw [(Work.FTS.StrongEps.LocUnif.mixed_partials_of_smoothOpen j i (hsm n)).2.1 z θ hQ]
      have hb := hbnd' n j (i + 1) (by omega) z θ hQ
      have hw := wt_pos_of_mem_Q0 hQ
      have hsin : 0 < Real.sin (2 * θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
      have hN' := hN (z, θ) (Set.mem_prod.mpr ⟨hzI, hθI⟩)
      have hC0 : 0 ≤ max C 0 := le_max_right C 0
      have hzinv : 0 ≤ 1 / z := le_of_lt (one_div_pos.mpr hzpos)
      have hsininv : 0 ≤ 1 / Real.sin (2 * θ) := le_of_lt (one_div_pos.mpr hsin)
      rw [abs_div, abs_of_pos hsin, div_eq_mul_one_div]
      calc |Work.Spaces.mixed j (i + 1) (G n) z θ| * (1 / Real.sin (2 * θ))
          ≤ max C 0 * wt z θ * (1 / Real.sin (2 * θ)) := mul_le_mul_of_nonneg_right hb hsininv
        _ = max C 0 * (wt z θ * (1 / Real.sin (2 * θ))) := by ring
        _ ≤ max C 0 * (wt z θ * (1 / z + 1 / Real.sin (2 * θ))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hzinv) hw) hC0
        _ ≤ max C 0 * N := mul_le_mul_of_nonneg_left hN' hC0
        _ ≤ L := hCNL
    -- slice differentiability in `z`, at fixed angle
    have hslice_z : ∀ (n j i : ℕ), ∀ θ ∈ Set.Icc c d, ∀ z ∈ Set.Icc a b,
        HasDerivWithinAt (fun z' : ℝ => Work.Spaces.mixed j i (G n) z' θ)
          (Work.Spaces.pz (Work.Spaces.mixed j i (G n)) z θ) (Set.Icc a b) z := by
      intro n j i θ hθI z hzI
      have hQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := hboxQ (Set.mem_prod.mpr ⟨hzI, hθI⟩)
      obtain ⟨hzpos, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hQ
      exact (((hsm n).mixed j i).hasDerivAt_slice ⟨hθ0, hθ1⟩ hzpos).hasDerivWithinAt
    -- slice differentiability in `θ`, at fixed radius
    have hslice_θ : ∀ (n j i : ℕ), ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
        HasDerivWithinAt (fun θ' : ℝ => Work.Spaces.mixed j i (G n) z θ')
          (Work.Spaces.pth (Work.Spaces.mixed j i (G n)) z θ) (Set.Icc c d) θ := by
      intro n j i z hzI θ hθI
      have hQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := hboxQ (Set.mem_prod.mpr ⟨hzI, hθI⟩)
      obtain ⟨hzpos, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hQ
      exact (smoothOpen_hasDerivAt_slice_theta ((hsm n).mixed j i) hzpos
        ⟨hθ0, hθ1⟩).hasDerivWithinAt
    -- every component of the family is `L`-Lipschitz on the box, hence on `K`
    have hcoord : ∀ (n : ℕ) (m : Fin 6) (p q : ℝ × ℝ), p ∈ K → q ∈ K →
        |fam6 G n p m - fam6 G n q m| ≤ L * (|p.1 - q.1| + |p.2 - q.2|) := by
      intro n m p q hp hq
      have hb := abs_sub_le_of_box_bounds
        (g := Work.Spaces.mixed (P6 m).1 (P6 m).2 (G n))
        (hslice_z n (P6 m).1 (P6 m).2) (hslice_θ n (P6 m).1 (P6 m).2)
        (hpz_bound n (P6 m).1 (P6 m).2 (P6_sum_le_two m))
        (hpth_bound n (P6 m).1 (P6 m).2 (P6_sum_le_two m))
        p (hbox hp) q (hbox hq)
      simpa only [fam6] using hb
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
    have hbound : ‖fam6 G n p - fam6 G n q‖ ≤ ε / 2 := by
      rw [pi_norm_le_iff_of_nonneg (by positivity : (0 : ℝ) ≤ ε / 2)]
      intro m
      change ‖fam6 G n p m - fam6 G n q m‖ ≤ ε / 2
      have hcm := hcoord n m p q hp hq
      have hstep1 : |fam6 G n p m - fam6 G n q m| ≤ L * (2 * dist p q) :=
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

end Work.FTS_EllLimOK
