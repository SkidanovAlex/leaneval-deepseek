import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.Basic
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.excDz5Dth2Six
import Submission.Work.FTS.StrongPersist.N6.Exc6
import Submission.Work.FTS.StrongPersist.N6.sliceAng_le6
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.StrongPersist.N6.PwOpen6
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.mixedSupSix
import Submission.Work.FTS.StrongPersist.N6Trans.T1SlotZ.Base2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.T1SixAux

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg canonW_eta_eq canonW_gam_eq)
open Work.FTS.StrongPersist.N6Trans.SixAux (aesm_canonW_abs_mul)

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

theorem t1SlotTermZ : ∃ K : ℝ, 0 < K ∧ ∀ (α q : ℝ) (f g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
    Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 6 g →
    ∀ (a b i j : ℕ), i ≤ a → j ≤ b → a + b ≤ 6 → ¬(i = 0 ∧ j = 0 ∧ 6 ≤ a + b) →
    0 ≤ q → q ≤ Work.Spaces.gam α → (a = 0 → q ≤ Work.Spaces.eta) →
    (MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.FTS.TransportS.SlotT2.canonW q z θ * |Work.Spaces.mixed j i f z θ|
          * |Work.Spaces.mixed (b - j) (a - i + 1) g z θ|
          * |Work.Spaces.mixed b a g z θ|) Work.Spaces.Iz) ∧
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.FTS.TransportS.SlotT2.canonW q z θ * |Work.Spaces.mixed j i f z θ|
          * |Work.Spaces.mixed (b - j) (a - i + 1) g z θ|
          * |Work.Spaces.mixed b a g z θ|)
      ≤ K * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f * Work.Spaces.HkSq α 6 g := by
  obtain ⟨C, hCpos, hsup⟩ := supSix
  obtain ⟨C5, hC5pos, h5raw⟩ := excDz5_mixed_pair_bound 0 2 (by norm_num) (by norm_num)
  refine ⟨C + C5 + 11, by positivity, ?_⟩
  intro α q f g hα hα1 hF hmemF hG hmemG a b i j hi hj hab hexcl hq0 hqγ hqη
  have hNf : (0 : ℝ) ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
  have hNg : (0 : ℝ) ≤ Work.Spaces.HkNorm α 6 g := Work.Spaces.HkNorm_nonneg α 6 g
  have hSqG : (0 : ℝ) ≤ Work.Spaces.HkSq α 6 g := Work.Spaces.HkSq_nonneg α 6 g
  have haρ : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  have hCK : C ≤ C + C5 + 11 := by linarith
  have hNg2 : Work.Spaces.HkNorm α 6 g * Work.Spaces.HkNorm α 6 g
      = Work.Spaces.HkSq α 6 g := by
    rw [Work.Spaces.HkNorm]; exact Real.mul_self_sqrt hSqG
  by_cases hp4 : i + j ≤ 4
  · -- ## Case 1: the `f`-factor `D_z^j D_θ^i f` has order `≤ 4`
    have hidx6 : (a - i + 1) + (b - j) ≤ 6 := by
      rcases Nat.eq_zero_or_pos (i + j) with h0 | hpos
      · have hi0 : i = 0 := by omega
        have hj0 : j = 0 := by omega
        have hab5 : a + b ≤ 5 := by
          by_contra hcon
          exact hexcl ⟨hi0, hj0, by omega⟩
        omega
      · omega
    have hmi : 1 ≤ a - i + 1 := by omega
    have hMnn : 0 ≤ C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f :=
      mul_nonneg (mul_nonneg hCpos.le haρ) hNf
    obtain ⟨hI, hB⟩ := T1SlotZ.slotTripleFirst (α := α) (q := q)
      (M := C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f) hMnn
      (X := fun z θ => Work.Spaces.mixed j i f z θ)
      (Y := fun z θ => Work.Spaces.mixed (b - j) (a - i + 1) g z θ)
      (Z := fun z θ => Work.Spaces.mixed b a g z θ)
      hG hG hmemG hmemG
      (aesm_canonW_abs_mul (q := q) (hF.mixed j i).continuousOn
        (hG.mixed (b - j) (a - i + 1)).continuousOn (hG.mixed b a).continuousOn)
      (fun z θ hz hθ hθ2 =>
        hsup α f hα hα1 hF hmemF j i hp4 z θ hz hθ hθ2)
      (fun z θ hz hθ hθ2 =>
        T1SlotZ.canonW_mul_mixed_le_int (α := α) (q := q) hqγ ⟨hθ, hθ2⟩
          (b - j) (a - i + 1) hmi hidx6)
      (fun z θ hz hθ hθ2 => by
        rcases eq_or_ne a 0 with ha0 | ha0
        · subst ha0
          simpa only [Work.Spaces.mixed_zero_right] using
            (T1SlotZ.canonW_mul_z_le_int (α := α) (q := q) (h := g) (hqη rfl)
              ⟨hθ, hθ2⟩ b (by omega))
        · exact T1SlotZ.canonW_mul_mixed_le_int (α := α) (q := q) hqγ ⟨hθ, hθ2⟩ b a
            (Nat.one_le_iff_ne_zero.mpr ha0) (by omega))
    refine ⟨hI, ?_⟩
    rw [Real.mul_self_sqrt hSqG] at hB
    exact hB.trans (T1SlotZ.le_const_mul_alpha hα hCK hNf hSqG)
  · push_neg at hp4
    by_cases hi0 : i = 0
    · by_cases ha0 : a = 0
      · -- ## Case 2a: `i = 0`, `a = 0` — the sup goes on the middle `g`-slot
        simp only [hi0, ha0]
        have hidx4 : (0 - 0 + 1) + (b - j) ≤ 4 := by omega
        have hqη' : q ≤ Work.Spaces.eta := hqη ha0
        have hMnn : 0 ≤ C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 g :=
          mul_nonneg (mul_nonneg hCpos.le haρ) hNg
        obtain ⟨hI, hB⟩ := T1SlotZ.slotTripleMid (α := α) (q := q)
          (M := C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 g) hMnn
          (X := fun z θ => Work.Spaces.mixed j 0 f z θ)
          (Y := fun z θ => Work.Spaces.mixed (b - j) (0 - 0 + 1) g z θ)
          (Z := fun z θ => Work.Spaces.mixed b 0 g z θ)
          hF hG hmemF hmemG
          (aesm_canonW_abs_mul (q := q) (hF.mixed j 0).continuousOn
            (hG.mixed (b - j) (0 - 0 + 1)).continuousOn (hG.mixed b 0).continuousOn)
          (fun z θ hz hθ hθ2 =>
            hsup α g hα hα1 hG hmemG (b - j) (0 - 0 + 1) hidx4 z θ hz hθ hθ2)
          (fun z θ hz hθ hθ2 => by
            simpa only [Work.Spaces.mixed_zero_right] using
              (T1SlotZ.canonW_mul_z_le_int (α := α) (q := q) (h := f) hqη'
                ⟨hθ, hθ2⟩ j (by omega)))
          (fun z θ hz hθ hθ2 => by
            simpa only [Work.Spaces.mixed_zero_right] using
              (T1SlotZ.canonW_mul_z_le_int (α := α) (q := q) (h := g) hqη'
                ⟨hθ, hθ2⟩ b (by omega)))
        refine ⟨hI, ?_⟩
        have h3 : Work.Spaces.HkSq α 6 g
            = Work.Spaces.HkNorm α 6 g * Work.Spaces.HkNorm α 6 g := hNg2.symm
        have heq : (C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 g)
              * (Real.sqrt (Work.Spaces.HkSq α 6 f) * Real.sqrt (Work.Spaces.HkSq α 6 g))
            = C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f * Work.Spaces.HkSq α 6 g := by
          calc (C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 g)
                * (Real.sqrt (Work.Spaces.HkSq α 6 f) * Real.sqrt (Work.Spaces.HkSq α 6 g))
              = (C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 g)
                * (Work.Spaces.HkNorm α 6 f * Work.Spaces.HkNorm α 6 g) := by
                rw [show Real.sqrt (Work.Spaces.HkSq α 6 f) = Work.Spaces.HkNorm α 6 f from rfl,
                  show Real.sqrt (Work.Spaces.HkSq α 6 g) = Work.Spaces.HkNorm α 6 g from rfl]
            _ = C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f
                * (Work.Spaces.HkNorm α 6 g * Work.Spaces.HkNorm α 6 g) := by ring
            _ = C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f
                * Work.Spaces.HkSq α 6 g := by rw [← h3]
        exact hB.trans (heq.le.trans (T1SlotZ.le_const_mul_alpha hα hCK hNf hSqG))
      · -- ## Case 2b: `i = 0`, `a ≥ 1` — the exceptional configuration `(a,b,j) = (1,5,5)`
        have hcfg : a = 1 ∧ b = 5 ∧ j = 5 := by omega
        simp only [hi0, hcfg.1, hcfg.2.1, hcfg.2.2, Nat.sub_self, Nat.sub_zero,
          Work.Spaces.mixed_zero_right]
        obtain ⟨hAmem, hAsq⟩ := h5raw α f g hα hα1 hF hmemF hG hmemG
        set A : ℝ → ℝ → ℝ := fun z θ => Work.Spaces.DzIter 5 f z θ
          * Work.Spaces.mixed 0 2 g z θ * Work.Spaces.Wt α z θ with hAdef
        set B : ℝ → ℝ → ℝ := fun z θ => Work.Spaces.mixed 5 1 g z θ
          * Work.Spaces.Wt α z θ with hBdef
        have hAval : ∀ z θ, A z θ = Work.Spaces.DzIter 5 f z θ
            * Work.Spaces.mixed 0 2 g z θ * Work.Spaces.Wt α z θ := fun z θ => by rw [hAdef]
        have hBval : ∀ z θ, B z θ = Work.Spaces.mixed 5 1 g z θ
            * Work.Spaces.Wt α z θ := fun z θ => by rw [hBdef]
        have hBcont : ContinuousOn (Function.uncurry B) Work.FTS.EllipticEst.Q0 := by
          rw [show Function.uncurry B = Function.uncurry (fun z θ =>
              Work.Spaces.mixed 5 1 g z θ * Work.Spaces.Wt α z θ) from by
            funext p; exact hBval p.1 p.2]
          exact (hG.mixed 5 1).continuousOn.mul (T1SlotZ.continuousOn_Wt_Q0 α)
        have hBpt : ∀ z θ : ℝ, 0 ≤ z → 0 < θ → θ < Real.pi / 2 →
            (B z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 g z θ := by
          intro z θ hz hθ hθ2
          rw [hBval z θ]
          exact Work.Spaces.sq_le_HkIntegrand_mixed α 6 g z θ 1 5 (by norm_num) (by norm_num)
        have hBaesm : ∀ z ∈ Work.Spaces.Iz,
            AEStronglyMeasurable (fun θ => (B z θ) ^ 2)
              (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
          intro z hz
          rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
          · subst h0
            have hzero : ∀ θ, B 0 θ = 0 := by
              intro θ
              rw [hBval 0 θ, Work.Spaces.Wt, Work.Spaces.w]
              norm_num
            refine (MeasureTheory.aestronglyMeasurable_const :
              AEStronglyMeasurable (fun _ : ℝ => (0 : ℝ))
                (MeasureTheory.volume.restrict Work.Spaces.Iθ)).congr ?_
            exact Filter.Eventually.of_forall fun θ => by
              show (0 : ℝ) = (B 0 θ) ^ 2
              rw [hzero θ]
              ring
          · exact Work.Spaces.aesm_slice_of_continuousOn_Qd
              (fun p : ℝ × ℝ => (B p.1 p.2) ^ 2) (hBcont.pow 2) hz0
        obtain ⟨hBmem, hBsq⟩ :=
          T1SlotZ.L2Mem_of_le_HkIntegrand (α := α) (B := B) (g := g) hBcont hmemG hBaesm hBpt
        obtain ⟨hI, hBnd⟩ := T1SlotZ.iterated_cs_le (A := A) (B := B)
          (S := fun z θ => canonW q z θ * |Work.Spaces.DzIter 5 f z θ|
            * |Work.Spaces.mixed 0 2 g z θ| * |Work.Spaces.mixed 5 1 g z θ|)
          hAmem hBmem
          (aesm_canonW_abs_mul (q := q) (hF.DzIter 5).continuousOn
            (hG.mixed 0 2).continuousOn (hG.mixed 5 1).continuousOn)
          (fun z θ hz hθ hθ2 => mul_nonneg (mul_nonneg (mul_nonneg
            (canonW_nonneg ⟨hθ.le, hθ2.le⟩) (abs_nonneg _)) (abs_nonneg _)) (abs_nonneg _))
          (fun z θ hz hθ hθ2 => by
            have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.le, hθ2.le⟩
            have hcan : canonW q z θ ≤ canonW (Work.Spaces.gam α) z θ :=
              T1SlotZ.canonW_le_int hqγ ⟨hθ, hθ2⟩
            have hWt : canonW (Work.Spaces.gam α) z θ = (Work.Spaces.Wt α z θ) ^ 2 :=
              canonW_gam_eq α z θ hθI
            have hWtnn : 0 ≤ Work.Spaces.Wt α z θ := by
              rw [Work.Spaces.Wt, Work.Spaces.wTheta]
              exact mul_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))
                (Real.rpow_nonneg (le_of_lt (Real.sin_pos_of_pos_of_lt_pi
                  (by linarith) (by linarith))) _)
            have h1 : canonW q z θ * |Work.Spaces.DzIter 5 f z θ|
                  * |Work.Spaces.mixed 0 2 g z θ| * |Work.Spaces.mixed 5 1 g z θ|
                ≤ canonW (Work.Spaces.gam α) z θ * |Work.Spaces.DzIter 5 f z θ|
                  * |Work.Spaces.mixed 0 2 g z θ| * |Work.Spaces.mixed 5 1 g z θ| := by
              have hnn : 0 ≤ |Work.Spaces.DzIter 5 f z θ|
                  * |Work.Spaces.mixed 0 2 g z θ| * |Work.Spaces.mixed 5 1 g z θ| :=
                mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)
              calc canonW q z θ * |Work.Spaces.DzIter 5 f z θ|
                    * |Work.Spaces.mixed 0 2 g z θ| * |Work.Spaces.mixed 5 1 g z θ|
                  = canonW q z θ * (|Work.Spaces.DzIter 5 f z θ|
                    * |Work.Spaces.mixed 0 2 g z θ| * |Work.Spaces.mixed 5 1 g z θ|) := by ring
                _ ≤ canonW (Work.Spaces.gam α) z θ * (|Work.Spaces.DzIter 5 f z θ|
                    * |Work.Spaces.mixed 0 2 g z θ| * |Work.Spaces.mixed 5 1 g z θ|) :=
                    mul_le_mul_of_nonneg_right hcan hnn
                _ = canonW (Work.Spaces.gam α) z θ * |Work.Spaces.DzIter 5 f z θ|
                    * |Work.Spaces.mixed 0 2 g z θ| * |Work.Spaces.mixed 5 1 g z θ| := by ring
            refine h1.trans (le_of_eq ?_)
            rw [hWt, hAval z θ, hBval z θ]
            rw [abs_mul, abs_mul, abs_mul, abs_mul]
            simp only [abs_of_nonneg hWtnn]
            ring)
        refine ⟨hI, ?_⟩
        have hx : Real.sqrt (C5 / (Work.Spaces.gam α - 1))
            = Real.sqrt C5 * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) := by
          have h1 : Real.sqrt (C5 / (Work.Spaces.gam α - 1))
              = Real.sqrt C5 * (1 / Real.sqrt (Work.Spaces.gam α - 1)) := by
            rw [Real.sqrt_div hC5pos.le, div_eq_mul_inv, one_div]
          rw [h1, SixAux.one_div_sqrt_gam_sub_one hα]
          ring
        have hA' : Real.sqrt (Work.Spaces.L2Sq A)
            ≤ Real.sqrt C5 * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ))
              * Work.Spaces.HkNorm α 6 f * Work.Spaces.HkNorm α 6 g := by
          have hγ : 0 < Work.Spaces.gam α - 1 := by
            rw [Work.Spaces.gam_sub_one]; linarith
          have hnn2 : (0 : ℝ) ≤ C5 / (Work.Spaces.gam α - 1) := div_nonneg hC5pos.le hγ.le
          have hnn1 : (0 : ℝ) ≤ C5 / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 6 f :=
            mul_nonneg hnn2 (Work.Spaces.HkSq_nonneg α 6 f)
          have e1 : Real.sqrt (Work.Spaces.HkSq α 6 f) = Work.Spaces.HkNorm α 6 f := rfl
          have e2 : Real.sqrt (Work.Spaces.HkSq α 6 g) = Work.Spaces.HkNorm α 6 g := rfl
          refine le_trans (Real.sqrt_le_sqrt hAsq) (le_of_eq ?_)
          simp only [Real.sqrt_mul hnn1, Real.sqrt_mul hnn2, hx, e1, e2]
        have hB' : Real.sqrt (Work.Spaces.L2Sq B) ≤ Work.Spaces.HkNorm α 6 g :=
          Real.sqrt_le_sqrt hBsq
        have hKbig : Real.sqrt C5 * Real.sqrt 10 ≤ C + C5 + 11 := by
          have h2 : Real.sqrt (C5 * 10) ≤ (C5 + 10) / 2 := by
            have habs := Work.FTS.TransportS.T3BadAux.abs_mul_le_half_sq_add
              (Real.sqrt C5) (Real.sqrt 10)
            rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)),
              Real.sq_sqrt hC5pos.le, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10)] at habs
            rwa [Real.sqrt_mul hC5pos.le 10]
          rw [← Real.sqrt_mul hC5pos.le 10]
          linarith
        have htot : Real.sqrt (Work.Spaces.L2Sq A) * Real.sqrt (Work.Spaces.L2Sq B)
            ≤ Real.sqrt C5 * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ))
              * Work.Spaces.HkNorm α 6 f * Work.Spaces.HkSq α 6 g := by
          have h3 : Work.Spaces.HkSq α 6 g
              = Work.Spaces.HkNorm α 6 g * Work.Spaces.HkNorm α 6 g := hNg2.symm
          calc Real.sqrt (Work.Spaces.L2Sq A) * Real.sqrt (Work.Spaces.L2Sq B)
              ≤ (Real.sqrt C5 * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ))
                  * Work.Spaces.HkNorm α 6 f * Work.Spaces.HkNorm α 6 g)
                * Work.Spaces.HkNorm α 6 g :=
                mul_le_mul hA' hB' (Real.sqrt_nonneg _)
                  (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
                    (Real.sqrt_nonneg _)) haρ) hNf) hNg)
            _ = Real.sqrt C5 * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ))
                  * Work.Spaces.HkNorm α 6 f
                  * (Work.Spaces.HkNorm α 6 g * Work.Spaces.HkNorm α 6 g) := by ring
            _ = Real.sqrt C5 * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ))
                  * Work.Spaces.HkNorm α 6 f * Work.Spaces.HkSq α 6 g := by rw [← h3]
        exact hBnd.trans (htot.trans (T1SlotZ.le_const_mul_alpha hα hKbig hNf hSqG))
    · -- ## Case 2c: `i ≥ 1` — the sup goes on the middle `g`-slot
      have hi1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi0
      have ha1 : 1 ≤ a := by omega
      have hidx4 : (a - i + 1) + (b - j) ≤ 4 := by omega
      have hidx6 : i + j ≤ 6 := by omega
      have hMnn : 0 ≤ C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 g :=
        mul_nonneg (mul_nonneg hCpos.le haρ) hNg
      obtain ⟨hI, hB⟩ := T1SlotZ.slotTripleMid (α := α) (q := q)
        (M := C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 g) hMnn
        (X := fun z θ => Work.Spaces.mixed j i f z θ)
        (Y := fun z θ => Work.Spaces.mixed (b - j) (a - i + 1) g z θ)
        (Z := fun z θ => Work.Spaces.mixed b a g z θ)
        hF hG hmemF hmemG
        (aesm_canonW_abs_mul (q := q) (hF.mixed j i).continuousOn
          (hG.mixed (b - j) (a - i + 1)).continuousOn (hG.mixed b a).continuousOn)
        (fun z θ hz hθ hθ2 =>
          hsup α g hα hα1 hG hmemG (b - j) (a - i + 1) hidx4 z θ hz hθ hθ2)
        (fun z θ hz hθ hθ2 =>
          T1SlotZ.canonW_mul_mixed_le_int (α := α) (q := q) hqγ ⟨hθ, hθ2⟩
            j i hi1 hidx6)
        (fun z θ hz hθ hθ2 =>
          T1SlotZ.canonW_mul_mixed_le_int (α := α) (q := q) hqγ ⟨hθ, hθ2⟩
            b a ha1 (by omega))
      refine ⟨hI, ?_⟩
      have h3 : Work.Spaces.HkSq α 6 g
          = Work.Spaces.HkNorm α 6 g * Work.Spaces.HkNorm α 6 g := hNg2.symm
      have heq : (C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 g)
            * (Real.sqrt (Work.Spaces.HkSq α 6 f) * Real.sqrt (Work.Spaces.HkSq α 6 g))
          = C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f * Work.Spaces.HkSq α 6 g := by
        calc (C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 g)
              * (Real.sqrt (Work.Spaces.HkSq α 6 f) * Real.sqrt (Work.Spaces.HkSq α 6 g))
            = (C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 g)
              * (Work.Spaces.HkNorm α 6 f * Work.Spaces.HkNorm α 6 g) := by
              rw [show Real.sqrt (Work.Spaces.HkSq α 6 f) = Work.Spaces.HkNorm α 6 f from rfl,
                show Real.sqrt (Work.Spaces.HkSq α 6 g) = Work.Spaces.HkNorm α 6 g from rfl]
          _ = C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f
              * (Work.Spaces.HkNorm α 6 g * Work.Spaces.HkNorm α 6 g) := by ring
          _ = C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f
              * Work.Spaces.HkSq α 6 g := by rw [← h3]
      exact hB.trans (heq.le.trans (T1SlotZ.le_const_mul_alpha hα hCK hNf hSqG))

end Work.FTS.StrongPersist.N6Trans.T1SixAux
