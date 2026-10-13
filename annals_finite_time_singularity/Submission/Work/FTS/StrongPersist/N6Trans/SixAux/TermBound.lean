import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.SupPkg
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.ExcPairBranches

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The per-term bound of the level-6 `T2` slot

For a slot `(a, b)` with `a + b ≤ 6` and a Leibniz summand
`D_z^{b1}D_θ^{a1}f · D_z^{b-b1+1}D_θ^{a-a1}g · D_z^bD_θ^a g` with `a1 + b1 ≥ 1`, the
product-measure integral of its absolute value is bounded by `Λ · |g|²_{ℋ⁶}`.
-/

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.SixAux

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg canonW_zero_z canonW_mono)
open Work.FTS.StrongPersist.N6Trans.T1SixAux (SlotW6 slotW6_z slotW6_mixed)

set_option autoImplicit false
set_option maxHeartbeats 3200000

theorem term_bound {α Kf Kg q Λ : ℝ} {f g : ℝ → ℝ → ℝ} {a b a1 b1 : ℕ}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hfs : Work.FTS.EllipticEst.SmoothOpen f) (hfm : Work.Spaces.HkMem α 6 f)
    (hgs : Work.FTS.EllipticEst.SmoothOpen g) (hgm : Work.Spaces.HkMem α 6 g)
    (h : SupPkg α f g Kf Kg) (hKf0 : 0 ≤ Kf) (hKg0 : 0 ≤ Kg)
    (hΛ1 : Kf ≤ Λ)
    (hΛ2 : Kg * Work.Spaces.HkNorm α 6 f ≤ Λ * Work.Spaces.HkNorm α 6 g)
    (hq0 : 0 < q) (hqγ : q ≤ Work.Spaces.gam α) (hqη : a = 0 → q ≤ Work.Spaces.eta)
    (ha1 : a1 ≤ a) (hb1 : b1 ≤ b) (hp : 1 ≤ a1 + b1) (hab : a + b ≤ 6)
    (hΛE1 : Real.sqrt (10 * excC11) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f
      ≤ Λ)
    (hΛE2 : Real.sqrt (10 * excC02) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f
      ≤ Λ) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => canonW q p.1 p.2
      * |Work.Spaces.mixed b1 a1 f p.1 p.2|
      * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g p.1 p.2|
      * |Work.Spaces.mixed b a g p.1 p.2|) pm ∧
    (∫ p, canonW q p.1 p.2
      * |Work.Spaces.mixed b1 a1 f p.1 p.2|
      * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g p.1 p.2|
      * |Work.Spaces.mixed b a g p.1 p.2| ∂pm) ≤ Λ * (Work.Spaces.HkNorm α 6 g) ^ 2 := by
  have hsame : Kf * Work.Spaces.HkSq α 6 g ≤ Λ * (Work.Spaces.HkNorm α 6 g) ^ 2 := by
    have hsq : Work.Spaces.HkSq α 6 g = (Work.Spaces.HkNorm α 6 g) ^ 2 := by
      rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 g)]
    rw [hsq]
    exact mul_le_mul_of_nonneg_right hΛ1 (sq_nonneg _)
  have hcross : Kg * (Real.sqrt (Work.Spaces.HkSq α 6 f) * Real.sqrt (Work.Spaces.HkSq α 6 g))
      ≤ Λ * (Work.Spaces.HkNorm α 6 g) ^ 2 := by
    have hsq : Work.Spaces.HkNorm α 6 g = Real.sqrt (Work.Spaces.HkSq α 6 g) := rfl
    rw [hsq]
    calc Kg * (Real.sqrt (Work.Spaces.HkSq α 6 f) * Real.sqrt (Work.Spaces.HkSq α 6 g))
        = (Kg * Real.sqrt (Work.Spaces.HkSq α 6 f)) * Real.sqrt (Work.Spaces.HkSq α 6 g) := by
          ring
      _ ≤ (Λ * Real.sqrt (Work.Spaces.HkSq α 6 g)) * Real.sqrt (Work.Spaces.HkSq α 6 g) :=
          mul_le_mul_of_nonneg_right hΛ2 (Real.sqrt_nonneg _)
      _ = Λ * Real.sqrt (Work.Spaces.HkSq α 6 g) ^ 2 := by ring
  by_cases ha1z : a1 = 0
  · subst ha1z
    by_cases hb16 : b1 = 6
    · -- ## case D: `a = 0`, `b = b1 = 6`
      subst hb16
      have hb6 : b = 6 := by omega
      have ha0 : a = 0 := by omega
      subst hb6
      subst ha0
      simp only [Nat.sub_self, Nat.sub_zero, Nat.zero_add, Work.Spaces.mixed_zero_right]
      have hsl1 : SlotW6 α q (Work.Spaces.DzIter 6 f) f :=
        slotW6_z α (q := q) hq0 (hqη rfl) f 6 (by norm_num)
      have hsl2 : SlotW6 α q (Work.Spaces.DzIter 6 g) g :=
        slotW6_z α (q := q) hq0 (hqη rfl) g 6 (by norm_num)
      have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          canonW q z θ * |Work.Spaces.DzIter 6 f z θ| * |Work.Spaces.DzIter 1 g z θ|
            * |Work.Spaces.DzIter 6 g z θ| ≤ Kg * (Real.sqrt (Work.Spaces.HkIntegrand α 6 f z θ)
              * Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ)) := by
        intro z θ hz hθ hθ2
        have hzI : z ∈ Work.Spaces.Iz := hz.le
        have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.le, hθ2.le⟩
        have hpt2 := pair_cross_le (α := α) (q := q) hzI hθI hsl1 hsl2
        have hG : |Work.Spaces.DzIter 1 g z θ| ≤ Kg := h.gpure 1 (by norm_num) z θ hz hθ hθ2
        calc canonW q z θ * |Work.Spaces.DzIter 6 f z θ| * |Work.Spaces.DzIter 1 g z θ|
              * |Work.Spaces.DzIter 6 g z θ|
            = (canonW q z θ * |Work.Spaces.DzIter 6 f z θ| * |Work.Spaces.DzIter 6 g z θ|)
              * |Work.Spaces.DzIter 1 g z θ| := by ring
          _ ≤ (Real.sqrt (Work.Spaces.HkIntegrand α 6 f z θ)
                * Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ)) * Kg :=
              mul_le_mul hpt2 hG (abs_nonneg _)
                (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
          _ = Kg * (Real.sqrt (Work.Spaces.HkIntegrand α 6 f z θ)
                * Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ)) := by ring
      have haesm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
          canonW q p.1 p.2 * |Work.Spaces.DzIter 6 f p.1 p.2| * |Work.Spaces.DzIter 1 g p.1 p.2|
            * |Work.Spaces.DzIter 6 g p.1 p.2|) pm :=
        aesm_canonW_abs_mul (q := q) ((hfs.DzIter 6).continuousOn)
          ((hgs.DzIter 1).continuousOn) ((hgs.DzIter 6).continuousOn)
      refine ⟨?_, ?_⟩
      · exact (integrable_of_pointwise_sqrt (f := f) (g := g) hfs hgs hfm hgm hKg0
          (F := fun z θ => canonW q z θ * |Work.Spaces.DzIter 6 f z θ|
            * |Work.Spaces.DzIter 1 g z θ| * |Work.Spaces.DzIter 6 g z θ|) haesm
          (fun z θ hz hθ hθ2 => by
            rw [abs_of_nonneg (canonW_mul_abs3_nonneg (⟨hθ.le, hθ2.le⟩ : θ ∈ Work.Spaces.Iθ) _ _ _)]
            exact hpt z θ hz hθ hθ2)).1
      · exact (integrable_of_pointwise_sqrt (f := f) (g := g) hfs hgs hfm hgm hKg0
          (F := fun z θ => canonW q z θ * |Work.Spaces.DzIter 6 f z θ|
            * |Work.Spaces.DzIter 1 g z θ| * |Work.Spaces.DzIter 6 g z θ|) haesm
          (fun z θ hz hθ hθ2 => by
            rw [abs_of_nonneg (canonW_mul_abs3_nonneg (⟨hθ.le, hθ2.le⟩ : θ ∈ Work.Spaces.Iθ) _ _ _)]
            exact hpt z θ hz hθ hθ2)).2.trans hcross
    · -- ## case A: `a1 = 0`, with the top slot `b1 = 5` treated separately
      by_cases hb1five : b1 = 5
      · by_cases ha0 : a = 0
        · exact term_bound_A5a hα hα1 hfs hfm hgs hgm h hKf0 hKg0 hΛ1 hΛ2 hq0 hqγ hqη hab
            ha0 rfl hb1five
        · have haeq : a = 1 := by omega
          have hb5 : b = 5 := by omega
          exact term_bound_A5b hα hα1 hfs hfm hgs hgm h hKf0 hKg0 hΛ1 hΛ2 hq0 hqγ hqη hab
            haeq rfl hb1five hb5 hΛE1
      have hb14 : b1 ≤ 4 := by omega
      have hb1pos : 1 ≤ b1 := by omega
      have hord1 : a - 0 + (b - b1 + 1) ≤ 6 := by omega
      have hsl1 : SlotW6 α q (Work.Spaces.mixed (b - b1 + 1) (a - 0) g) g := by
        rcases eq_or_ne (a - 0) 0 with h0 | h0
        · rw [h0, Work.Spaces.mixed_zero_right]
          exact slotW6_z α (q := q) hq0 (hqη (by omega)) g (b - b1 + 1) (by omega)
        · exact slotW6_mixed α (q := q) hq0 hqγ g (b - b1 + 1) (a - 0)
            (Nat.one_le_iff_ne_zero.mpr h0) hord1
      have hsl2 : SlotW6 α q (Work.Spaces.mixed b a g) g := by
        rcases eq_or_ne a 0 with h0 | h0
        · rw [h0, Work.Spaces.mixed_zero_right]
          exact slotW6_z α (q := q) hq0 (hqη h0) g b (by omega)
        · exact slotW6_mixed α (q := q) hq0 hqγ g b a (Nat.one_le_iff_ne_zero.mpr h0) hab
      have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          canonW q z θ * |Work.Spaces.mixed b1 0 f z θ|
            * |Work.Spaces.mixed (b - b1 + 1) (a - 0) g z θ|
            * |Work.Spaces.mixed b a g z θ| ≤ Kf * Work.Spaces.HkIntegrand α 6 g z θ := by
        intro z θ hz hθ hθ2
        have hzI : z ∈ Work.Spaces.Iz := hz.le
        have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.le, hθ2.le⟩
        simp only [Work.Spaces.mixed_zero_right]
        have hF : |Work.Spaces.DzIter b1 f z θ| ≤ Kf := h.fpure b1 hb14 z θ hz hθ hθ2
        have hpt2 := slotW6_pair_le (α := α) (q := q) hzI hθI hsl1 hsl2
        calc canonW q z θ * |Work.Spaces.DzIter b1 f z θ|
              * |Work.Spaces.mixed (b - b1 + 1) (a - 0) g z θ| * |Work.Spaces.mixed b a g z θ|
            = |Work.Spaces.DzIter b1 f z θ| * (canonW q z θ
              * |Work.Spaces.mixed (b - b1 + 1) (a - 0) g z θ|
              * |Work.Spaces.mixed b a g z θ|) := by ring
          _ ≤ Kf * Work.Spaces.HkIntegrand α 6 g z θ :=
              mul_le_mul hF hpt2 (by have h1 : 0 ≤ canonW q z θ := canonW_nonneg hθI; positivity) hKf0
      have haesm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
          canonW q p.1 p.2 * |Work.Spaces.mixed b1 0 f p.1 p.2|
            * |Work.Spaces.mixed (b - b1 + 1) (a - 0) g p.1 p.2|
            * |Work.Spaces.mixed b a g p.1 p.2|) pm :=
        aesm_canonW_abs_mul (q := q) ((hfs.mixed b1 0).continuousOn)
          ((hgs.mixed (b - b1 + 1) (a - 0)).continuousOn)
          ((hgs.mixed b a).continuousOn)
      refine ⟨?_, ?_⟩
      · exact (integrable_of_pointwise (g := g) hgs hgm hKf0
          (F := fun z θ => canonW q z θ * |Work.Spaces.mixed b1 0 f z θ|
            * |Work.Spaces.mixed (b - b1 + 1) (a - 0) g z θ|
            * |Work.Spaces.mixed b a g z θ|) haesm
          (fun z θ hz hθ hθ2 => by
            rw [abs_of_nonneg (canonW_mul_abs3_nonneg (⟨hθ.le, hθ2.le⟩ : θ ∈ Work.Spaces.Iθ) _ _ _)]
            exact hpt z θ hz hθ hθ2)).1
      · exact (integrable_of_pointwise (g := g) hgs hgm hKf0
          (F := fun z θ => canonW q z θ * |Work.Spaces.mixed b1 0 f z θ|
            * |Work.Spaces.mixed (b - b1 + 1) (a - 0) g z θ|
            * |Work.Spaces.mixed b a g z θ|) haesm
          (fun z θ hz hθ hθ2 => by
            rw [abs_of_nonneg (canonW_mul_abs3_nonneg (⟨hθ.le, hθ2.le⟩ : θ ∈ Work.Spaces.Iθ) _ _ _)]
            exact hpt z θ hz hθ hθ2)).2.trans hsame
  · have ha1pos : 1 ≤ a1 := Nat.one_le_iff_ne_zero.mpr ha1z
    have hapos : 1 ≤ a := le_trans ha1pos ha1
    have hFbody : (fun z θ => canonW q z θ * |Work.Spaces.mixed b1 a1 f z θ|
        * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ| * |Work.Spaces.mixed b a g z θ|)
        = (fun z θ => canonW q z θ * |Work.Spaces.mixed b1 a1 f z θ|
        * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ| * |Work.Spaces.mixed b a g z θ|) := rfl
    by_cases ha2z : a - a1 = 0
    · -- ## case C: the middle factor is pure
      by_cases hg16 : b - b1 + 1 = 6
      · -- ## case C2: the `σ`-gain
        have hb5 : b = 5 := by omega
        have hb1z : b1 = 0 := by omega
        have ha1e : a1 = 1 := by omega
        have hsl1 : SlotW6 α Work.Spaces.eta (Work.Spaces.DzIter 6 g) g :=
          slotW6_z α (q := Work.Spaces.eta) Work.Spaces.eta_pos le_rfl g 6 (by norm_num)
        have hηγ : Work.Spaces.eta ≤ Work.Spaces.gam α := by
          rw [Work.Spaces.gam, Work.Spaces.eta]; linarith
        have hsl2 : SlotW6 α Work.Spaces.eta (Work.Spaces.mixed 5 1 g) g :=
          slotW6_mixed α (q := Work.Spaces.eta) Work.Spaces.eta_pos hηγ g 5 1
            (by norm_num) (by norm_num)
        have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
            canonW q z θ * |Work.Spaces.mixed b1 a1 f z θ|
              * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ|
              * |Work.Spaces.mixed b a g z θ| ≤ Kf * Work.Spaces.HkIntegrand α 6 g z θ := by
          intro z θ hz hθ hθ2
          have hzI : z ∈ Work.Spaces.Iz := hz.le
          have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.le, hθ2.le⟩
          have hae : a = 1 := by omega
          have hidx1 : (5 - 0 + 1 : ℕ) = 6 := by norm_num
          have hidx2 : (1 - 1 : ℕ) = 0 := by norm_num
          rw [hb1z, ha1e, hb5, hae, hidx1, hidx2, Work.Spaces.mixed_zero_left,
            Work.Spaces.mixed_zero_right]
          have hDth : Work.Spaces.Dth f z θ
              = Real.sin (2 * θ) * Work.Spaces.pth f z θ := rfl
          have hσ0 : 0 < Real.sin (2 * θ) :=
            Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
          have hσ1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
          have hσt : Real.sin (2 * θ) * Real.sin (2 * θ) ^ (-q)
              ≤ Real.sin (2 * θ) ^ (-Work.Spaces.eta) := by
            have h1 : Real.sin (2 * θ) * Real.sin (2 * θ) ^ (-q)
                = Real.sin (2 * θ) ^ (1 - q) := by
              rw [show (1 : ℝ) - q = 1 + (-q) by ring, Real.rpow_add hσ0, Real.rpow_one]
            rw [h1]
            exact Real.rpow_le_rpow_of_exponent_ge hσ0 hσ1 (by
              have hγη : Work.Spaces.gam α ≤ 1 + Work.Spaces.eta := by
                rw [Work.Spaces.gam, Work.Spaces.eta]; linarith
              linarith)
          have hpth : |Work.Spaces.pth f z θ| ≤ Kf := h.pthf z θ hz hθ hθ2
          have hstep1 : canonW q z θ * |Work.Spaces.Dth f z θ|
              ≤ Kf * canonW Work.Spaces.eta z θ := by
            rw [hDth, abs_mul, abs_of_nonneg hσ0.le]
            simp only [canonW]
            calc (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-q)
                  * (Real.sin (2 * θ) * |Work.Spaces.pth f z θ|)
                = (Work.Spaces.w z) ^ 2
                    * (Real.sin (2 * θ) * Real.sin (2 * θ) ^ (-q))
                    * |Work.Spaces.pth f z θ| := by ring
              _ ≤ (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-Work.Spaces.eta)
                    * Kf := by
                  refine mul_le_mul (mul_le_mul_of_nonneg_left hσt (sq_nonneg _)) hpth
                    (abs_nonneg _) (by positivity)
              _ = Kf * ((Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-Work.Spaces.eta)) := by ring
          have hpair := slotW6_pair_le (α := α) (q := Work.Spaces.eta) hzI hθI hsl1 hsl2
          calc canonW q z θ * |Work.Spaces.Dth f z θ| * |Work.Spaces.DzIter 6 g z θ|
                * |Work.Spaces.mixed 5 1 g z θ|
              = (canonW q z θ * |Work.Spaces.Dth f z θ|)
                * (|Work.Spaces.DzIter 6 g z θ| * |Work.Spaces.mixed 5 1 g z θ|) := by ring
            _ ≤ (Kf * canonW Work.Spaces.eta z θ)
                * (|Work.Spaces.DzIter 6 g z θ| * |Work.Spaces.mixed 5 1 g z θ|) :=
                mul_le_mul_of_nonneg_right hstep1 (by positivity)
            _ = Kf * (canonW Work.Spaces.eta z θ * |Work.Spaces.DzIter 6 g z θ|
                * |Work.Spaces.mixed 5 1 g z θ|) := by ring
            _ ≤ Kf * Work.Spaces.HkIntegrand α 6 g z θ :=
                mul_le_mul_of_nonneg_left hpair hKf0
        have haesm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
            canonW q p.1 p.2 * |Work.Spaces.mixed b1 a1 f p.1 p.2|
              * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g p.1 p.2|
              * |Work.Spaces.mixed b a g p.1 p.2|) pm :=
          aesm_canonW_abs_mul (q := q) ((hfs.mixed b1 a1).continuousOn)
            ((hgs.mixed (b - b1 + 1) (a - a1)).continuousOn)
            ((hgs.mixed b a).continuousOn)
        refine ⟨?_, ?_⟩
        · exact (integrable_of_pointwise (g := g) hgs hgm hKf0
            (F := fun z θ => canonW q z θ * |Work.Spaces.mixed b1 a1 f z θ|
              * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ|
              * |Work.Spaces.mixed b a g z θ|) haesm
            (fun z θ hz hθ hθ2 => by
              rw [abs_of_nonneg (canonW_mul_abs3_nonneg (⟨hθ.le, hθ2.le⟩ : θ ∈ Work.Spaces.Iθ) _ _ _)]
              exact hpt z θ hz hθ hθ2)).1
        · exact (integrable_of_pointwise (g := g) hgs hgm hKf0
            (F := fun z θ => canonW q z θ * |Work.Spaces.mixed b1 a1 f z θ|
              * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ|
              * |Work.Spaces.mixed b a g z θ|) haesm
            (fun z θ hz hθ hθ2 => by
              rw [abs_of_nonneg (canonW_mul_abs3_nonneg (⟨hθ.le, hθ2.le⟩ : θ ∈ Work.Spaces.Iθ) _ _ _)]
              exact hpt z θ hz hθ hθ2)).2.trans hsame
      · -- ## case C1: the middle factor is pure
        by_cases hg5 : b - b1 + 1 = 5
        · have hcase : (a = 1 ∧ b1 = 0) ∨ (a = 1 ∧ b1 = 1) ∨ (a = 2 ∧ b1 = 0) := by
            omega
          rcases hcase with ⟨h1a, h1b⟩ | ⟨h2a, h2b⟩ | ⟨h3a, h3b⟩
          · exact term_bound_C1sigma hα hα1 hfs hfm hgs hgm h hKf0 hKg0 hΛ1 hΛ2 hq0 hqγ
              hqη hab h1a (by omega) h1b (by omega)
          · exact term_bound_C1E11 hα hα1 hfs hfm hgs hgm h hKf0 hKg0 hΛ1 hΛ2 hq0 hqγ
              hqη hab h2a (by omega) h2b (by omega) hΛE1
          · exact term_bound_C1E02 hα hα1 hfs hfm hgs hgm h hKf0 hKg0 hΛ1 hΛ2 hq0 hqγ
              hqη hab h3a (by omega) h3b (by omega) hΛE2
        have hg14 : b - b1 + 1 ≤ 4 := by omega
        have hord1 : a - a1 + (b - b1 + 1) ≤ 6 := by omega
        have hsl1 : SlotW6 α q (Work.Spaces.mixed b1 a1 f) f :=
          slotW6_mixed α (q := q) hq0 hqγ f b1 a1 ha1pos (by omega)
        have hsl2 : SlotW6 α q (Work.Spaces.mixed b a g) g :=
          slotW6_mixed α (q := q) hq0 hqγ g b a hapos hab
        have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
            canonW q z θ * |Work.Spaces.mixed b1 a1 f z θ|
              * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ|
              * |Work.Spaces.mixed b a g z θ| ≤ Kg * (Real.sqrt (Work.Spaces.HkIntegrand α 6 f z θ)
                * Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ)) := by
          intro z θ hz hθ hθ2
          have hzI : z ∈ Work.Spaces.Iz := hz.le
          have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.le, hθ2.le⟩
          have hcast : Work.Spaces.mixed (b - b1 + 1) (a - a1) g
              = Work.Spaces.DzIter (b - b1 + 1) g := by
            rw [ha2z, Work.Spaces.mixed_zero_right]
          rw [hcast]
          have hG : |Work.Spaces.DzIter (b - b1 + 1) g z θ| ≤ Kg :=
            h.gpure (b - b1 + 1) hg14 z θ hz hθ hθ2
          have hpair := pair_cross_le (α := α) (q := q) hzI hθI hsl1 hsl2
          calc canonW q z θ * |Work.Spaces.mixed b1 a1 f z θ|
                * |Work.Spaces.DzIter (b - b1 + 1) g z θ| * |Work.Spaces.mixed b a g z θ|
              = (canonW q z θ * |Work.Spaces.mixed b1 a1 f z θ| * |Work.Spaces.mixed b a g z θ|)
                * |Work.Spaces.DzIter (b - b1 + 1) g z θ| := by ring
            _ ≤ (Real.sqrt (Work.Spaces.HkIntegrand α 6 f z θ)
                  * Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ)) * Kg :=
                mul_le_mul hpair hG (abs_nonneg _)
                  (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
            _ = Kg * (Real.sqrt (Work.Spaces.HkIntegrand α 6 f z θ)
                  * Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ)) := by ring
        have haesm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
            canonW q p.1 p.2 * |Work.Spaces.mixed b1 a1 f p.1 p.2|
              * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g p.1 p.2|
              * |Work.Spaces.mixed b a g p.1 p.2|) pm :=
          aesm_canonW_abs_mul (q := q) ((hfs.mixed b1 a1).continuousOn)
            ((hgs.mixed (b - b1 + 1) (a - a1)).continuousOn)
            ((hgs.mixed b a).continuousOn)
        refine ⟨?_, ?_⟩
        · exact (integrable_of_pointwise_sqrt (f := f) (g := g) hfs hgs hfm hgm hKg0
            (F := fun z θ => canonW q z θ * |Work.Spaces.mixed b1 a1 f z θ|
              * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ|
              * |Work.Spaces.mixed b a g z θ|) haesm
            (fun z θ hz hθ hθ2 => by
              rw [abs_of_nonneg (canonW_mul_abs3_nonneg (⟨hθ.le, hθ2.le⟩ : θ ∈ Work.Spaces.Iθ) _ _ _)]
              exact hpt z θ hz hθ hθ2)).1
        · exact (integrable_of_pointwise_sqrt (f := f) (g := g) hfs hgs hfm hgm hKg0
            (F := fun z θ => canonW q z θ * |Work.Spaces.mixed b1 a1 f z θ|
              * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ|
              * |Work.Spaces.mixed b a g z θ|) haesm
            (fun z θ hz hθ hθ2 => by
              rw [abs_of_nonneg (canonW_mul_abs3_nonneg (⟨hθ.le, hθ2.le⟩ : θ ∈ Work.Spaces.Iθ) _ _ _)]
              exact hpt z θ hz hθ hθ2)).2.trans hcross
    · -- ## case B: both `F` and `G` are mixed
      have ha2pos : 1 ≤ a - a1 := Nat.one_le_iff_ne_zero.mpr ha2z
      by_cases hp4 : a1 + b1 ≤ 4
      · -- bound `F`
        have hsl1 : SlotW6 α q (Work.Spaces.mixed (b - b1 + 1) (a - a1) g) g :=
          slotW6_mixed α (q := q) hq0 hqγ g (b - b1 + 1) (a - a1) ha2pos (by omega)
        have hsl2 : SlotW6 α q (Work.Spaces.mixed b a g) g :=
          slotW6_mixed α (q := q) hq0 hqγ g b a hapos hab
        have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
            canonW q z θ * |Work.Spaces.mixed b1 a1 f z θ|
              * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ|
              * |Work.Spaces.mixed b a g z θ| ≤ Kf * Work.Spaces.HkIntegrand α 6 g z θ := by
          intro z θ hz hθ hθ2
          have hzI : z ∈ Work.Spaces.Iz := hz.le
          have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.le, hθ2.le⟩
          have hF : |Work.Spaces.mixed b1 a1 f z θ| ≤ Kf :=
            h.fmix b1 a1 ha1pos hp4 z θ hz hθ hθ2
          have hpair := slotW6_pair_le (α := α) (q := q) hzI hθI hsl1 hsl2
          calc canonW q z θ * |Work.Spaces.mixed b1 a1 f z θ|
                * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ| * |Work.Spaces.mixed b a g z θ|
              = |Work.Spaces.mixed b1 a1 f z θ| * (canonW q z θ
                * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ|
                * |Work.Spaces.mixed b a g z θ|) := by ring
            _ ≤ Kf * Work.Spaces.HkIntegrand α 6 g z θ :=
                mul_le_mul hF hpair (by have h1 : 0 ≤ canonW q z θ := canonW_nonneg hθI; positivity) hKf0
        have haesm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
            canonW q p.1 p.2 * |Work.Spaces.mixed b1 a1 f p.1 p.2|
              * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g p.1 p.2|
              * |Work.Spaces.mixed b a g p.1 p.2|) pm :=
          aesm_canonW_abs_mul (q := q) ((hfs.mixed b1 a1).continuousOn)
            ((hgs.mixed (b - b1 + 1) (a - a1)).continuousOn)
            ((hgs.mixed b a).continuousOn)
        refine ⟨?_, ?_⟩
        · exact (integrable_of_pointwise (g := g) hgs hgm hKf0
            (F := fun z θ => canonW q z θ * |Work.Spaces.mixed b1 a1 f z θ|
              * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ|
              * |Work.Spaces.mixed b a g z θ|) haesm
            (fun z θ hz hθ hθ2 => by
              rw [abs_of_nonneg (canonW_mul_abs3_nonneg (⟨hθ.le, hθ2.le⟩ : θ ∈ Work.Spaces.Iθ) _ _ _)]
              exact hpt z θ hz hθ hθ2)).1
        · exact (integrable_of_pointwise (g := g) hgs hgm hKf0
            (F := fun z θ => canonW q z θ * |Work.Spaces.mixed b1 a1 f z θ|
              * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ|
              * |Work.Spaces.mixed b a g z θ|) haesm
            (fun z θ hz hθ hθ2 => by
              rw [abs_of_nonneg (canonW_mul_abs3_nonneg (⟨hθ.le, hθ2.le⟩ : θ ∈ Work.Spaces.Iθ) _ _ _)]
              exact hpt z θ hz hθ hθ2)).2.trans hsame
      · -- `p = 5`: bound `G`
        have hp5 : a1 + b1 = 5 := by omega
        have hg14 : a - a1 + (b - b1 + 1) ≤ 4 := by omega
        have hsl1 : SlotW6 α q (Work.Spaces.mixed b1 a1 f) f :=
          slotW6_mixed α (q := q) hq0 hqγ f b1 a1 ha1pos (by omega)
        have hsl2 : SlotW6 α q (Work.Spaces.mixed b a g) g :=
          slotW6_mixed α (q := q) hq0 hqγ g b a hapos hab
        have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
            canonW q z θ * |Work.Spaces.mixed b1 a1 f z θ|
              * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ|
              * |Work.Spaces.mixed b a g z θ| ≤ Kg * (Real.sqrt (Work.Spaces.HkIntegrand α 6 f z θ)
                * Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ)) := by
          intro z θ hz hθ hθ2
          have hzI : z ∈ Work.Spaces.Iz := hz.le
          have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.le, hθ2.le⟩
          have hG : |Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ| ≤ Kg :=
            h.gmix (b - b1 + 1) (a - a1) ha2pos hg14 z θ hz hθ hθ2
          have hpair := pair_cross_le (α := α) (q := q) hzI hθI hsl1 hsl2
          calc canonW q z θ * |Work.Spaces.mixed b1 a1 f z θ|
                * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ| * |Work.Spaces.mixed b a g z θ|
              = (canonW q z θ * |Work.Spaces.mixed b1 a1 f z θ| * |Work.Spaces.mixed b a g z θ|)
                * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ| := by ring
            _ ≤ (Real.sqrt (Work.Spaces.HkIntegrand α 6 f z θ)
                  * Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ)) * Kg :=
                mul_le_mul hpair hG (abs_nonneg _)
                  (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
            _ = Kg * (Real.sqrt (Work.Spaces.HkIntegrand α 6 f z θ)
                  * Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ)) := by ring
        have haesm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
            canonW q p.1 p.2 * |Work.Spaces.mixed b1 a1 f p.1 p.2|
              * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g p.1 p.2|
              * |Work.Spaces.mixed b a g p.1 p.2|) pm :=
          aesm_canonW_abs_mul (q := q) ((hfs.mixed b1 a1).continuousOn)
            ((hgs.mixed (b - b1 + 1) (a - a1)).continuousOn)
            ((hgs.mixed b a).continuousOn)
        refine ⟨?_, ?_⟩
        · exact (integrable_of_pointwise_sqrt (f := f) (g := g) hfs hgs hfm hgm hKg0
            (F := fun z θ => canonW q z θ * |Work.Spaces.mixed b1 a1 f z θ|
              * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ|
              * |Work.Spaces.mixed b a g z θ|) haesm
            (fun z θ hz hθ hθ2 => by
              rw [abs_of_nonneg (canonW_mul_abs3_nonneg (⟨hθ.le, hθ2.le⟩ : θ ∈ Work.Spaces.Iθ) _ _ _)]
              exact hpt z θ hz hθ hθ2)).1
        · exact (integrable_of_pointwise_sqrt (f := f) (g := g) hfs hgs hfm hgm hKg0
            (F := fun z θ => canonW q z θ * |Work.Spaces.mixed b1 a1 f z θ|
              * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ|
              * |Work.Spaces.mixed b a g z θ|) haesm
            (fun z θ hz hθ hθ2 => by
              rw [abs_of_nonneg (canonW_mul_abs3_nonneg (⟨hθ.le, hθ2.le⟩ : θ ∈ Work.Spaces.Iθ) _ _ _)]
              exact hpt z θ hz hθ hθ2)).2.trans hcross

end Work.FTS.StrongPersist.N6Trans.SixAux
