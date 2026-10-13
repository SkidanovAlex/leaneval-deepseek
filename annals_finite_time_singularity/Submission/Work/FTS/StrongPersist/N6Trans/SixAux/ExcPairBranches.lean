import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.ExcPairPm
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.SupPkg

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The four exceptional branches of the level-6 `T2` per-summand bound

The Leibniz summands of `term_bound` in which the pointwise sup at order `5` would be needed,
handled instead by (i) the Cauchy–Schwarz pairing of two pure slots, (ii) the `σ`-gain of
`D_θf`, or (iii) the exceptional `L²` pairing `exc_pair_pm`.

Each lemma concludes exactly the shape of `term_bound`'s conclusion, so that `term_bound` can
invoke it directly.
-/

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.SixAux

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg canonW_zero_z canonW_mono)
open Work.FTS.StrongPersist.N6Trans.T1SixAux (SlotW6 slotW6_z slotW6_mixed)

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-- The `Kg·(√|f|²·√|g|²) ≤ Λ|g|²` bookkeeping, isolated for reuse. -/
theorem hcross_sqrt {α Λ Kg : ℝ} {f g : ℝ → ℝ → ℝ}
    (hΛ2 : Kg * Work.Spaces.HkNorm α 6 f ≤ Λ * Work.Spaces.HkNorm α 6 g) :
    Kg * (Real.sqrt (Work.Spaces.HkSq α 6 f) * Real.sqrt (Work.Spaces.HkSq α 6 g))
      ≤ Λ * (Work.Spaces.HkNorm α 6 g) ^ 2 := by
  have hsq : Work.Spaces.HkNorm α 6 g = Real.sqrt (Work.Spaces.HkSq α 6 g) := rfl
  rw [hsq]
  calc Kg * (Real.sqrt (Work.Spaces.HkSq α 6 f) * Real.sqrt (Work.Spaces.HkSq α 6 g))
      = (Kg * Real.sqrt (Work.Spaces.HkSq α 6 f)) * Real.sqrt (Work.Spaces.HkSq α 6 g) := by
        ring
    _ ≤ (Λ * Real.sqrt (Work.Spaces.HkSq α 6 g)) * Real.sqrt (Work.Spaces.HkSq α 6 g) :=
        mul_le_mul_of_nonneg_right hΛ2 (Real.sqrt_nonneg _)
    _ = Λ * Real.sqrt (Work.Spaces.HkSq α 6 g) ^ 2 := by ring

/-- **Branch `A5a`** (`a1 = 0`, `b1 = 5`, `a = 0`): the middle `g`-factor carries the sup, the
two pure slots are Cauchy–Schwarz'ed. -/
theorem term_bound_A5a {α Kf Kg q Λ : ℝ} {f g : ℝ → ℝ → ℝ} {a b a1 b1 : ℕ}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hfs : Work.FTS.EllipticEst.SmoothOpen f) (hfm : Work.Spaces.HkMem α 6 f)
    (hgs : Work.FTS.EllipticEst.SmoothOpen g) (hgm : Work.Spaces.HkMem α 6 g)
    (h : SupPkg α f g Kf Kg) (hKf0 : 0 ≤ Kf) (hKg0 : 0 ≤ Kg)
    (hΛ1 : Kf ≤ Λ)
    (hΛ2 : Kg * Work.Spaces.HkNorm α 6 f ≤ Λ * Work.Spaces.HkNorm α 6 g)
    (hq0 : 0 < q) (hqγ : q ≤ Work.Spaces.gam α) (hqη : a = 0 → q ≤ Work.Spaces.eta)
    (hab : a + b ≤ 6) (ha : a = 0) (ha1 : a1 = 0) (hb1 : b1 = 5) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => canonW q p.1 p.2
        * |Work.Spaces.mixed b1 a1 f p.1 p.2|
        * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g p.1 p.2|
        * |Work.Spaces.mixed b a g p.1 p.2|) pm ∧
      (∫ p, canonW q p.1 p.2 * |Work.Spaces.mixed b1 a1 f p.1 p.2|
        * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g p.1 p.2|
        * |Work.Spaces.mixed b a g p.1 p.2| ∂pm)
        ≤ Λ * (Work.Spaces.HkNorm α 6 g) ^ 2 := by
  subst ha1
  subst ha
  subst hb1
  have hqη' : q ≤ Work.Spaces.eta := hqη rfl
  have hmid : b - 5 + 1 ≤ 4 := by omega
  have hsl1 : SlotW6 α q (Work.Spaces.DzIter 5 f) f :=
    slotW6_z α (q := q) hq0 hqη' f 5 (by norm_num)
  have hsl2 : SlotW6 α q (Work.Spaces.DzIter b g) g :=
    slotW6_z α (q := q) hq0 hqη' g b (by omega)
  have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      canonW q z θ * |Work.Spaces.mixed 5 0 f z θ|
        * |Work.Spaces.mixed (b - 5 + 1) (0 - 0) g z θ|
        * |Work.Spaces.mixed b 0 g z θ| ≤ Kg * (Real.sqrt (Work.Spaces.HkIntegrand α 6 f z θ)
          * Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ)) := by
    intro z θ hz hθ hθ2
    have hzI : z ∈ Work.Spaces.Iz := hz.le
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.le, hθ2.le⟩
    simp only [Work.Spaces.mixed_zero_right, Nat.sub_zero]
    have hG : |Work.Spaces.DzIter (b - 5 + 1) g z θ| ≤ Kg :=
      h.gpure (b - 5 + 1) hmid z θ hz hθ hθ2
    have hpair := pair_cross_le (α := α) (q := q) hzI hθI hsl1 hsl2
    calc canonW q z θ * |Work.Spaces.DzIter 5 f z θ|
          * |Work.Spaces.DzIter (b - 5 + 1) g z θ| * |Work.Spaces.DzIter b g z θ|
        = (canonW q z θ * |Work.Spaces.DzIter 5 f z θ| * |Work.Spaces.DzIter b g z θ|)
          * |Work.Spaces.DzIter (b - 5 + 1) g z θ| := by ring
      _ ≤ (Real.sqrt (Work.Spaces.HkIntegrand α 6 f z θ)
            * Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ)) * Kg :=
          mul_le_mul hpair hG (abs_nonneg _)
            (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      _ = Kg * (Real.sqrt (Work.Spaces.HkIntegrand α 6 f z θ)
            * Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ)) := by ring
  have haesm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      canonW q p.1 p.2 * |Work.Spaces.mixed 5 0 f p.1 p.2|
        * |Work.Spaces.mixed (b - 5 + 1) (0 - 0) g p.1 p.2|
        * |Work.Spaces.mixed b 0 g p.1 p.2|) pm :=
    aesm_canonW_abs_mul (q := q) ((hfs.mixed 5 0).continuousOn)
      ((hgs.mixed (b - 5 + 1) (0 - 0)).continuousOn) ((hgs.mixed b 0).continuousOn)
  have hcross := hcross_sqrt (α := α) (Λ := Λ) (Kg := Kg) hΛ2
  refine ⟨?_, ?_⟩
  · exact (integrable_of_pointwise_sqrt (f := f) (g := g) hfs hgs hfm hgm hKg0
      (F := fun z θ => canonW q z θ * |Work.Spaces.mixed 5 0 f z θ|
        * |Work.Spaces.mixed (b - 5 + 1) (0 - 0) g z θ|
        * |Work.Spaces.mixed b 0 g z θ|) haesm
      (fun z θ hz hθ hθ2 => by
        rw [abs_of_nonneg (canonW_mul_abs3_nonneg (⟨hθ.le, hθ2.le⟩ : θ ∈ Work.Spaces.Iθ) _ _ _)]
        exact hpt z θ hz hθ hθ2)).1
  · exact (integrable_of_pointwise_sqrt (f := f) (g := g) hfs hgs hfm hgm hKg0
      (F := fun z θ => canonW q z θ * |Work.Spaces.mixed 5 0 f z θ|
        * |Work.Spaces.mixed (b - 5 + 1) (0 - 0) g z θ|
        * |Work.Spaces.mixed b 0 g z θ|) haesm
      (fun z θ hz hθ hθ2 => by
        rw [abs_of_nonneg (canonW_mul_abs3_nonneg (⟨hθ.le, hθ2.le⟩ : θ ∈ Work.Spaces.Iθ) _ _ _)]
        exact hpt z θ hz hθ hθ2)).2.trans hcross

/-- **Branch `A5b`** (`a1 = 0`, `b1 = 5`, `a = 1`, `b = 5`): the exceptional configuration, with
the pure top slot `D_z⁵f` on the `f`-side. -/
theorem term_bound_A5b {α Kf Kg q Λ : ℝ} {f g : ℝ → ℝ → ℝ} {a b a1 b1 : ℕ}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hfs : Work.FTS.EllipticEst.SmoothOpen f) (hfm : Work.Spaces.HkMem α 6 f)
    (hgs : Work.FTS.EllipticEst.SmoothOpen g) (hgm : Work.Spaces.HkMem α 6 g)
    (h : SupPkg α f g Kf Kg) (hKf0 : 0 ≤ Kf) (hKg0 : 0 ≤ Kg)
    (hΛ1 : Kf ≤ Λ)
    (hΛ2 : Kg * Work.Spaces.HkNorm α 6 f ≤ Λ * Work.Spaces.HkNorm α 6 g)
    (hq0 : 0 < q) (hqγ : q ≤ Work.Spaces.gam α) (hqη : a = 0 → q ≤ Work.Spaces.eta)
    (hab : a + b ≤ 6) (ha : a = 1) (ha1 : a1 = 0) (hb1 : b1 = 5) (hb : b = 5)
    (hΛE1 : Real.sqrt (10 * excC11) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f
      ≤ Λ) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => canonW q p.1 p.2
        * |Work.Spaces.mixed b1 a1 f p.1 p.2|
        * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g p.1 p.2|
        * |Work.Spaces.mixed b a g p.1 p.2|) pm ∧
      (∫ p, canonW q p.1 p.2 * |Work.Spaces.mixed b1 a1 f p.1 p.2|
        * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g p.1 p.2|
        * |Work.Spaces.mixed b a g p.1 p.2| ∂pm)
        ≤ Λ * (Work.Spaces.HkNorm α 6 g) ^ 2 := by
  subst ha
  subst ha1
  subst hb1
  subst hb
  obtain ⟨hL2mem, hL2sq⟩ :=
    excC11_spec (α := α) (p := f) (qq := g) hα hα1 hfs hfm hgs hgm
  obtain ⟨hint, hbound⟩ := exc_pair_pm (α := α) (q := q) (C1 := excC11) (p := f) (qq := g)
    (g := g) (b := 1) (a := 1) (B := 5) (A := 1) hα hα1 excC11_pos.le hfs hfm hgs hgm hgs hgm
    (by norm_num) (by norm_num) hq0 hqγ hL2mem hL2sq
  have hgoal_int : MeasureTheory.Integrable (fun p : ℝ × ℝ => canonW q p.1 p.2
      * |Work.Spaces.DzIter 5 f p.1 p.2| * |Work.Spaces.mixed 1 1 g p.1 p.2|
      * |Work.Spaces.mixed 5 1 g p.1 p.2|) pm := hint
  have hgoal_bnd : |∫ p, canonW q p.1 p.2 * |Work.Spaces.DzIter 5 f p.1 p.2|
      * |Work.Spaces.mixed 1 1 g p.1 p.2| * |Work.Spaces.mixed 5 1 g p.1 p.2| ∂pm|
      ≤ Λ * (Work.Spaces.HkNorm α 6 g) ^ 2 := by
    refine le_trans hbound ?_
    calc Real.sqrt (10 * excC11) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f
          * Work.Spaces.HkNorm α 6 g * Work.Spaces.HkNorm α 6 g
        = (Real.sqrt (10 * excC11) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f)
          * (Work.Spaces.HkNorm α 6 g * Work.Spaces.HkNorm α 6 g) := by ring
      _ ≤ Λ * (Work.Spaces.HkNorm α 6 g * Work.Spaces.HkNorm α 6 g) :=
          mul_le_mul_of_nonneg_right hΛE1
            (mul_nonneg (Work.Spaces.HkNorm_nonneg α 6 g) (Work.Spaces.HkNorm_nonneg α 6 g))
      _ = Λ * (Work.Spaces.HkNorm α 6 g) ^ 2 := by ring
  have hint' : MeasureTheory.Integrable (fun p : ℝ × ℝ => canonW q p.1 p.2
      * |Work.Spaces.mixed 5 0 f p.1 p.2|
      * |Work.Spaces.mixed (5 - 5 + 1) (1 - 0) g p.1 p.2|
      * |Work.Spaces.mixed 5 1 g p.1 p.2|) pm := by
    convert hgoal_int using 1 with p
    simp only [Work.Spaces.mixed_zero_right, Nat.sub_self, Nat.sub_zero]
  refine ⟨hint', ?_⟩
  have hbnd' : (∫ p, canonW q p.1 p.2
      * |Work.Spaces.mixed 5 0 f p.1 p.2|
      * |Work.Spaces.mixed (5 - 5 + 1) (1 - 0) g p.1 p.2|
      * |Work.Spaces.mixed 5 1 g p.1 p.2| ∂pm)
      ≤ Λ * (Work.Spaces.HkNorm α 6 g) ^ 2 := by
    have hcongr : (∫ p, canonW q p.1 p.2 * |Work.Spaces.mixed 5 0 f p.1 p.2|
          * |Work.Spaces.mixed (5 - 5 + 1) (1 - 0) g p.1 p.2|
          * |Work.Spaces.mixed 5 1 g p.1 p.2| ∂pm)
        = ∫ p, canonW q p.1 p.2 * |Work.Spaces.DzIter 5 f p.1 p.2|
          * |Work.Spaces.mixed 1 1 g p.1 p.2| * |Work.Spaces.mixed 5 1 g p.1 p.2| ∂pm := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      simp only [Work.Spaces.mixed_zero_right, Nat.sub_self, Nat.sub_zero]
    rw [hcongr]
    exact le_trans (le_abs_self _) hgoal_bnd
  exact hbnd'

/-- **The `σ`-branch of case `C1`** (`a1 = a = 1`, `b1 = 0`, `b = 4`): the `f`-factor is
`D_θf`, whose `σ`-gain converts the weight `q` into the lighter `η`. -/
theorem term_bound_C1sigma {α Kf Kg q Λ : ℝ} {f g : ℝ → ℝ → ℝ} {a b a1 b1 : ℕ}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hfs : Work.FTS.EllipticEst.SmoothOpen f) (hfm : Work.Spaces.HkMem α 6 f)
    (hgs : Work.FTS.EllipticEst.SmoothOpen g) (hgm : Work.Spaces.HkMem α 6 g)
    (h : SupPkg α f g Kf Kg) (hKf0 : 0 ≤ Kf) (hKg0 : 0 ≤ Kg)
    (hΛ1 : Kf ≤ Λ)
    (hΛ2 : Kg * Work.Spaces.HkNorm α 6 f ≤ Λ * Work.Spaces.HkNorm α 6 g)
    (hq0 : 0 < q) (hqγ : q ≤ Work.Spaces.gam α) (hqη : a = 0 → q ≤ Work.Spaces.eta)
    (hab : a + b ≤ 6) (ha : a = 1) (ha1 : a1 = 1) (hb1 : b1 = 0) (hb : b = 4) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => canonW q p.1 p.2
        * |Work.Spaces.mixed b1 a1 f p.1 p.2|
        * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g p.1 p.2|
        * |Work.Spaces.mixed b a g p.1 p.2|) pm ∧
      (∫ p, canonW q p.1 p.2 * |Work.Spaces.mixed b1 a1 f p.1 p.2|
        * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g p.1 p.2|
        * |Work.Spaces.mixed b a g p.1 p.2| ∂pm)
        ≤ Λ * (Work.Spaces.HkNorm α 6 g) ^ 2 := by
  subst ha
  subst ha1
  subst hb1
  subst hb
  have hηγ : Work.Spaces.eta ≤ Work.Spaces.gam α := by
    rw [Work.Spaces.gam, Work.Spaces.eta]; linarith [hα.le]
  have hsl1 : SlotW6 α Work.Spaces.eta (Work.Spaces.DzIter 5 g) g :=
    slotW6_z α (q := Work.Spaces.eta) Work.Spaces.eta_pos le_rfl g 5 (by norm_num)
  have hsl2 : SlotW6 α Work.Spaces.eta (Work.Spaces.mixed 4 1 g) g :=
    slotW6_mixed α (q := Work.Spaces.eta) Work.Spaces.eta_pos hηγ g 4 1
      (by norm_num) (by norm_num)
  have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      canonW q z θ * |Work.Spaces.mixed 0 1 f z θ|
        * |Work.Spaces.mixed (4 - 0 + 1) (1 - 1) g z θ|
        * |Work.Spaces.mixed 4 1 g z θ| ≤ Kf * Work.Spaces.HkIntegrand α 6 g z θ := by
    intro z θ hz hθ hθ2
    have hzI : z ∈ Work.Spaces.Iz := hz.le
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.le, hθ2.le⟩
    have hidx : (4 - 0 + 1 : ℕ) = 5 := by norm_num
    have hidx2 : (1 - 1 : ℕ) = 0 := by norm_num
    rw [hidx, hidx2, Work.Spaces.mixed_zero_right]
    have hDth : Work.Spaces.mixed 0 1 f z θ
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
    have hstep1 : canonW q z θ * |Work.Spaces.mixed 0 1 f z θ|
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
        _ = Kf * ((Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-Work.Spaces.eta)) := by
            ring
    have hpair := slotW6_pair_le (α := α) (q := Work.Spaces.eta) hzI hθI hsl1 hsl2
    calc canonW q z θ * |Work.Spaces.mixed 0 1 f z θ| * |Work.Spaces.DzIter 5 g z θ|
          * |Work.Spaces.mixed 4 1 g z θ|
        = (canonW q z θ * |Work.Spaces.mixed 0 1 f z θ|)
          * (|Work.Spaces.DzIter 5 g z θ| * |Work.Spaces.mixed 4 1 g z θ|) := by ring
      _ ≤ (Kf * canonW Work.Spaces.eta z θ)
          * (|Work.Spaces.DzIter 5 g z θ| * |Work.Spaces.mixed 4 1 g z θ|) :=
          mul_le_mul_of_nonneg_right hstep1 (by positivity)
      _ = Kf * (canonW Work.Spaces.eta z θ * |Work.Spaces.DzIter 5 g z θ|
            * |Work.Spaces.mixed 4 1 g z θ|) := by ring
      _ ≤ Kf * Work.Spaces.HkIntegrand α 6 g z θ :=
          mul_le_mul_of_nonneg_left hpair hKf0
  have haesm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      canonW q p.1 p.2 * |Work.Spaces.mixed 0 1 f p.1 p.2|
        * |Work.Spaces.mixed (4 - 0 + 1) (1 - 1) g p.1 p.2|
        * |Work.Spaces.mixed 4 1 g p.1 p.2|) pm :=
    aesm_canonW_abs_mul (q := q) ((hfs.mixed 0 1).continuousOn)
      ((hgs.mixed (4 - 0 + 1) (1 - 1)).continuousOn) ((hgs.mixed 4 1).continuousOn)
  have hsq : Work.Spaces.HkSq α 6 g = (Work.Spaces.HkNorm α 6 g) ^ 2 :=
    (Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 g)).symm
  refine ⟨?_, ?_⟩
  · exact (integrable_of_pointwise (g := g) hgs hgm hKf0
      (F := fun z θ => canonW q z θ * |Work.Spaces.mixed 0 1 f z θ|
        * |Work.Spaces.mixed (4 - 0 + 1) (1 - 1) g z θ|
        * |Work.Spaces.mixed 4 1 g z θ|) haesm
      (fun z θ hz hθ hθ2 => by
        rw [abs_of_nonneg (canonW_mul_abs3_nonneg (⟨hθ.le, hθ2.le⟩ : θ ∈ Work.Spaces.Iθ) _ _ _)]
        exact hpt z θ hz hθ hθ2)).1
  · refine (integrable_of_pointwise (g := g) hgs hgm hKf0
      (F := fun z θ => canonW q z θ * |Work.Spaces.mixed 0 1 f z θ|
        * |Work.Spaces.mixed (4 - 0 + 1) (1 - 1) g z θ|
        * |Work.Spaces.mixed 4 1 g z θ|) haesm
      (fun z θ hz hθ hθ2 => by
        rw [abs_of_nonneg (canonW_mul_abs3_nonneg (⟨hθ.le, hθ2.le⟩ : θ ∈ Work.Spaces.Iθ) _ _ _)]
        exact hpt z θ hz hθ hθ2)).2.trans ?_
    rw [hsq]
    exact mul_le_mul_of_nonneg_right hΛ1 (sq_nonneg _)

/-- **The exceptional branch of case `C1`** (`a1 = a = 1`, `b1 = 1`, `b = 5`): the pure top slot
`D_z⁵g` is paired with the mixed slot `D_zD_θf` of `f`. -/
theorem term_bound_C1E11 {α Kf Kg q Λ : ℝ} {f g : ℝ → ℝ → ℝ} {a b a1 b1 : ℕ}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hfs : Work.FTS.EllipticEst.SmoothOpen f) (hfm : Work.Spaces.HkMem α 6 f)
    (hgs : Work.FTS.EllipticEst.SmoothOpen g) (hgm : Work.Spaces.HkMem α 6 g)
    (h : SupPkg α f g Kf Kg) (hKf0 : 0 ≤ Kf) (hKg0 : 0 ≤ Kg)
    (hΛ1 : Kf ≤ Λ)
    (hΛ2 : Kg * Work.Spaces.HkNorm α 6 f ≤ Λ * Work.Spaces.HkNorm α 6 g)
    (hq0 : 0 < q) (hqγ : q ≤ Work.Spaces.gam α) (hqη : a = 0 → q ≤ Work.Spaces.eta)
    (hab : a + b ≤ 6) (ha : a = 1) (ha1 : a1 = 1) (hb1 : b1 = 1) (hb : b = 5)
    (hΛE1 : Real.sqrt (10 * excC11) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f
      ≤ Λ) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => canonW q p.1 p.2
        * |Work.Spaces.mixed b1 a1 f p.1 p.2|
        * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g p.1 p.2|
        * |Work.Spaces.mixed b a g p.1 p.2|) pm ∧
      (∫ p, canonW q p.1 p.2 * |Work.Spaces.mixed b1 a1 f p.1 p.2|
        * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g p.1 p.2|
        * |Work.Spaces.mixed b a g p.1 p.2| ∂pm)
        ≤ Λ * (Work.Spaces.HkNorm α 6 g) ^ 2 := by
  subst ha
  subst ha1
  subst hb1
  subst hb
  obtain ⟨hL2mem, hL2sq⟩ :=
    excC11_spec (α := α) (p := g) (qq := f) hα hα1 hgs hgm hfs hfm
  obtain ⟨hint, hbound⟩ := exc_pair_pm (α := α) (q := q) (C1 := excC11) (p := g) (qq := f)
    (g := g) (b := 1) (a := 1) (B := 5) (A := 1) hα hα1 excC11_pos.le hgs hgm hfs hfm hgs hgm
    (by norm_num) (by norm_num) hq0 hqγ hL2mem hL2sq
  have hgoal_int : MeasureTheory.Integrable (fun p : ℝ × ℝ => canonW q p.1 p.2
      * |Work.Spaces.mixed 1 1 f p.1 p.2| * |Work.Spaces.DzIter 5 g p.1 p.2|
      * |Work.Spaces.mixed 5 1 g p.1 p.2|) pm :=
    hint.congr (Filter.Eventually.of_forall fun p => by ring)
  have hiff : (∫ p, canonW q p.1 p.2 * |Work.Spaces.mixed 1 1 f p.1 p.2|
        * |Work.Spaces.DzIter 5 g p.1 p.2| * |Work.Spaces.mixed 5 1 g p.1 p.2| ∂pm)
      = ∫ p, canonW q p.1 p.2 * |Work.Spaces.DzIter 5 g p.1 p.2|
        * |Work.Spaces.mixed 1 1 f p.1 p.2| * |Work.Spaces.mixed 5 1 g p.1 p.2| ∂pm := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    ring
  have hgoal_bnd : |∫ p, canonW q p.1 p.2 * |Work.Spaces.mixed 1 1 f p.1 p.2|
      * |Work.Spaces.DzIter 5 g p.1 p.2| * |Work.Spaces.mixed 5 1 g p.1 p.2| ∂pm|
      ≤ Λ * (Work.Spaces.HkNorm α 6 g) ^ 2 := by
    rw [hiff]
    refine le_trans hbound ?_
    calc Real.sqrt (10 * excC11) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 g
          * Work.Spaces.HkNorm α 6 f * Work.Spaces.HkNorm α 6 g
        = (Real.sqrt (10 * excC11) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f)
          * (Work.Spaces.HkNorm α 6 g * Work.Spaces.HkNorm α 6 g) := by ring
      _ ≤ Λ * (Work.Spaces.HkNorm α 6 g * Work.Spaces.HkNorm α 6 g) :=
          mul_le_mul_of_nonneg_right hΛE1
            (mul_nonneg (Work.Spaces.HkNorm_nonneg α 6 g) (Work.Spaces.HkNorm_nonneg α 6 g))
      _ = Λ * (Work.Spaces.HkNorm α 6 g) ^ 2 := by ring
  have hint' : MeasureTheory.Integrable (fun p : ℝ × ℝ => canonW q p.1 p.2
      * |Work.Spaces.mixed 1 1 f p.1 p.2|
      * |Work.Spaces.mixed (5 - 1 + 1) (1 - 1) g p.1 p.2|
      * |Work.Spaces.mixed 5 1 g p.1 p.2|) pm := by
    convert hgoal_int using 1 with p
    simp only [Work.Spaces.mixed_zero_right, Nat.sub_self, Nat.sub_zero]
  refine ⟨hint', ?_⟩
  have hcongr : (∫ p, canonW q p.1 p.2 * |Work.Spaces.mixed 1 1 f p.1 p.2|
        * |Work.Spaces.mixed (5 - 1 + 1) (1 - 1) g p.1 p.2|
        * |Work.Spaces.mixed 5 1 g p.1 p.2| ∂pm)
      = ∫ p, canonW q p.1 p.2 * |Work.Spaces.mixed 1 1 f p.1 p.2|
        * |Work.Spaces.DzIter 5 g p.1 p.2| * |Work.Spaces.mixed 5 1 g p.1 p.2| ∂pm := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [Work.Spaces.mixed_zero_right, Nat.sub_self, Nat.sub_zero]
  rw [hcongr]
  exact le_trans (le_abs_self _) hgoal_bnd

/-- **The exceptional branch of case `C1`** (`a1 = a = 2`, `b1 = 0`, `b = 4`): the pure top slot
`D_z⁵g` is paired with the mixed slot `D_θ²f` of `f`. -/
theorem term_bound_C1E02 {α Kf Kg q Λ : ℝ} {f g : ℝ → ℝ → ℝ} {a b a1 b1 : ℕ}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hfs : Work.FTS.EllipticEst.SmoothOpen f) (hfm : Work.Spaces.HkMem α 6 f)
    (hgs : Work.FTS.EllipticEst.SmoothOpen g) (hgm : Work.Spaces.HkMem α 6 g)
    (h : SupPkg α f g Kf Kg) (hKf0 : 0 ≤ Kf) (hKg0 : 0 ≤ Kg)
    (hΛ1 : Kf ≤ Λ)
    (hΛ2 : Kg * Work.Spaces.HkNorm α 6 f ≤ Λ * Work.Spaces.HkNorm α 6 g)
    (hq0 : 0 < q) (hqγ : q ≤ Work.Spaces.gam α) (hqη : a = 0 → q ≤ Work.Spaces.eta)
    (hab : a + b ≤ 6) (ha : a = 2) (ha1 : a1 = 2) (hb1 : b1 = 0) (hb : b = 4)
    (hΛE2 : Real.sqrt (10 * excC02) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f
      ≤ Λ) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => canonW q p.1 p.2
        * |Work.Spaces.mixed b1 a1 f p.1 p.2|
        * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g p.1 p.2|
        * |Work.Spaces.mixed b a g p.1 p.2|) pm ∧
      (∫ p, canonW q p.1 p.2 * |Work.Spaces.mixed b1 a1 f p.1 p.2|
        * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g p.1 p.2|
        * |Work.Spaces.mixed b a g p.1 p.2| ∂pm)
        ≤ Λ * (Work.Spaces.HkNorm α 6 g) ^ 2 := by
  subst ha
  subst ha1
  subst hb1
  subst hb
  obtain ⟨hL2mem, hL2sq⟩ :=
    excC02_spec (α := α) (p := g) (qq := f) hα hα1 hgs hgm hfs hfm
  obtain ⟨hint, hbound⟩ := exc_pair_pm (α := α) (q := q) (C1 := excC02) (p := g) (qq := f)
    (g := g) (b := 0) (a := 2) (B := 4) (A := 2) hα hα1 excC02_pos.le hgs hgm hfs hfm hgs hgm
    (by norm_num) (by norm_num) hq0 hqγ hL2mem hL2sq
  have hgoal_int : MeasureTheory.Integrable (fun p : ℝ × ℝ => canonW q p.1 p.2
      * |Work.Spaces.mixed 0 2 f p.1 p.2| * |Work.Spaces.DzIter 5 g p.1 p.2|
      * |Work.Spaces.mixed 4 2 g p.1 p.2|) pm :=
    hint.congr (Filter.Eventually.of_forall fun p => by ring)
  have hiff : (∫ p, canonW q p.1 p.2 * |Work.Spaces.mixed 0 2 f p.1 p.2|
        * |Work.Spaces.DzIter 5 g p.1 p.2| * |Work.Spaces.mixed 4 2 g p.1 p.2| ∂pm)
      = ∫ p, canonW q p.1 p.2 * |Work.Spaces.DzIter 5 g p.1 p.2|
        * |Work.Spaces.mixed 0 2 f p.1 p.2| * |Work.Spaces.mixed 4 2 g p.1 p.2| ∂pm := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    ring
  have hgoal_bnd : |∫ p, canonW q p.1 p.2 * |Work.Spaces.mixed 0 2 f p.1 p.2|
      * |Work.Spaces.DzIter 5 g p.1 p.2| * |Work.Spaces.mixed 4 2 g p.1 p.2| ∂pm|
      ≤ Λ * (Work.Spaces.HkNorm α 6 g) ^ 2 := by
    rw [hiff]
    refine le_trans hbound ?_
    calc Real.sqrt (10 * excC02) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 g
          * Work.Spaces.HkNorm α 6 f * Work.Spaces.HkNorm α 6 g
        = (Real.sqrt (10 * excC02) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f)
          * (Work.Spaces.HkNorm α 6 g * Work.Spaces.HkNorm α 6 g) := by ring
      _ ≤ Λ * (Work.Spaces.HkNorm α 6 g * Work.Spaces.HkNorm α 6 g) :=
          mul_le_mul_of_nonneg_right hΛE2
            (mul_nonneg (Work.Spaces.HkNorm_nonneg α 6 g) (Work.Spaces.HkNorm_nonneg α 6 g))
      _ = Λ * (Work.Spaces.HkNorm α 6 g) ^ 2 := by ring
  have hint' : MeasureTheory.Integrable (fun p : ℝ × ℝ => canonW q p.1 p.2
      * |Work.Spaces.mixed 0 2 f p.1 p.2|
      * |Work.Spaces.mixed (4 - 0 + 1) (2 - 2) g p.1 p.2|
      * |Work.Spaces.mixed 4 2 g p.1 p.2|) pm := by
    convert hgoal_int using 1 with p
    simp only [Work.Spaces.mixed_zero_right, Nat.sub_self, Nat.sub_zero]
  refine ⟨hint', ?_⟩
  have hcongr : (∫ p, canonW q p.1 p.2 * |Work.Spaces.mixed 0 2 f p.1 p.2|
        * |Work.Spaces.mixed (4 - 0 + 1) (2 - 2) g p.1 p.2|
        * |Work.Spaces.mixed 4 2 g p.1 p.2| ∂pm)
      = ∫ p, canonW q p.1 p.2 * |Work.Spaces.mixed 0 2 f p.1 p.2|
        * |Work.Spaces.DzIter 5 g p.1 p.2| * |Work.Spaces.mixed 4 2 g p.1 p.2| ∂pm := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [Work.Spaces.mixed_zero_right, Nat.sub_self, Nat.sub_zero]
  rw [hcongr]
  exact le_trans (le_abs_self _) hgoal_bnd

end Work.FTS.StrongPersist.N6Trans.SixAux
