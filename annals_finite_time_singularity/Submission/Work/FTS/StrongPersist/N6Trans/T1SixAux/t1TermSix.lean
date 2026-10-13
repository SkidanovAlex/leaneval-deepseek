import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.Basic
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.SlicePrep
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.t1SlotTermZ
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.excSlotTerm
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.Base
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.slotEnergy6
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.TermSixAux.sliceIntSup
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.TermSixAux.sliceIntCS

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.T1SixAux

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg canonW_zero_z canonW_eta_eq canonW_gam_eq)

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-! ## Auxiliary lemmas

The two slice-integrability pieces used below are the delegated lemmas
`TermSixAux.sliceIntSup` (a sup-bounded factor times two canonical slots is `θ`-slice
integrable) and `TermSixAux.sliceIntCS` (a sup-bounded factor times a Cauchy–Schwarz pair is
`θ`-slice integrable), proved in
`Submission/Work/FTS/StrongPersist/N6Trans/T1SixAux/TermSixAux/`. -/

/-! ### Swapping the two non-sup slots -/

theorem canonW_abs_swap_slice {q z : ℝ} {X Y Z : ℝ → ℝ → ℝ}
    (h : IntegrableOn (fun θ : ℝ => canonW q z θ * |X z θ| * |Y z θ| * |Z z θ|)
      Work.Spaces.Iθ) :
    IntegrableOn (fun θ : ℝ => canonW q z θ * |Y z θ| * |X z θ| * |Z z θ|)
      Work.Spaces.Iθ := by
  have heq : (fun θ : ℝ => canonW q z θ * |Y z θ| * |X z θ| * |Z z θ|)
      = (fun θ : ℝ => canonW q z θ * |X z θ| * |Y z θ| * |Z z θ|) := by
    funext θ
    ring
  rw [heq]
  exact h

/-! ## The main theorem -/

theorem t1TermSix : ∃ K : ℝ, 0 < K ∧ ∀ (α q : ℝ) (f g : ℝ → ℝ → ℝ) (a b i j : ℕ),
    0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
    Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 6 g →
    i ≤ a → j ≤ b → a + b ≤ 6 → ¬(i = 0 ∧ j = 0 ∧ 6 ≤ a + b) →
    0 ≤ q → q ≤ Work.Spaces.gam α → (a = 0 → q ≤ Work.Spaces.eta) →
    (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ : ℝ =>
        Work.FTS.TransportS.SlotT2.canonW q z θ * |Work.Spaces.mixed j i f z θ|
          * |Work.Spaces.mixed (b - j) (a - i + 1) g z θ| * |Work.Spaces.mixed b a g z θ|)
        Work.Spaces.Iθ) ∧
    MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        Work.FTS.TransportS.SlotT2.canonW q z θ * |Work.Spaces.mixed j i f z θ|
          * |Work.Spaces.mixed (b - j) (a - i + 1) g z θ| * |Work.Spaces.mixed b a g z θ|)
      Work.Spaces.Iz ∧
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.FTS.TransportS.SlotT2.canonW q z θ * |Work.Spaces.mixed j i f z θ|
          * |Work.Spaces.mixed (b - j) (a - i + 1) g z θ| * |Work.Spaces.mixed b a g z θ|)
      ≤ K * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f * Work.Spaces.HkSq α 6 g := by
  obtain ⟨K, hKpos, hZ⟩ := t1SlotTermZ
  refine ⟨K, hKpos, ?_⟩
  intro α q f g a b i j hα hα1 hF hmemF hG hmemG hi hj hab hexcl hq0 hqγ hqη
  obtain ⟨hInt, hBnd⟩ :=
    hZ α q f g hα hα1 hF hmemF hG hmemG a b i j hi hj hab hexcl hq0 hqγ hqη
  refine ⟨?_, hInt, hBnd⟩
  obtain ⟨C, hCpos, hsupC⟩ := supSix
  by_cases hp4 : i + j ≤ 4
  · -- ## Case A: the sup is put on the `f`-slot `D_z^jD_θ^i f` (order `≤ 4`)
    have hMnn : 0 ≤ C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f :=
      mul_nonneg (mul_nonneg hCpos.le (Real.rpow_nonneg hα.le _))
        (Work.Spaces.HkNorm_nonneg α 6 f)
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
    exact TermSixAux.sliceIntSup (α := α) (q := q)
      (M := C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f)
      (X := fun z θ => Work.Spaces.mixed j i f z θ)
      (Y := fun z θ => Work.Spaces.mixed (b - j) (a - i + 1) g z θ)
      (Z := fun z θ => Work.Spaces.mixed b a g z θ)
      (h₁ := g) (h₂ := g)
      hMnn (hF.mixed j i).continuousOn (hG.mixed (b - j) (a - i + 1)).continuousOn
      (hG.mixed b a).continuousOn hmemG hmemG
      (fun z θ hz hθ hθ2 => hsupC α f hα hα1 hF hmemF j i (by omega) z θ hz hθ hθ2)
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
  · push_neg at hp4
    by_cases hi0 : i = 0
    · by_cases ha0 : a = 0
      · -- ## Case C: `i = 0`, `a = 0` — the sup goes on the middle `g`-slot
        simp only [hi0, ha0]
        have hidx4 : (0 - 0 + 1) + (b - j) ≤ 4 := by omega
        have hqη' : q ≤ Work.Spaces.eta := hqη ha0
        have hMnn : 0 ≤ C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 g :=
          mul_nonneg (mul_nonneg hCpos.le (Real.rpow_nonneg hα.le _))
            (Work.Spaces.HkNorm_nonneg α 6 g)
        refine fun z hz => canonW_abs_swap_slice (q := q) (z := z)
          (X := fun z θ => Work.Spaces.mixed (b - j) (0 - 0 + 1) g z θ)
          (Y := fun z θ => Work.Spaces.mixed j 0 f z θ)
          (Z := fun z θ => Work.Spaces.mixed b 0 g z θ)
          (TermSixAux.sliceIntSup (α := α) (q := q)
            (M := C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 g)
            (X := fun z θ => Work.Spaces.mixed (b - j) (0 - 0 + 1) g z θ)
            (Y := fun z θ => Work.Spaces.mixed j 0 f z θ)
            (Z := fun z θ => Work.Spaces.mixed b 0 g z θ)
            (h₁ := f) (h₂ := g)
            hMnn (hG.mixed (b - j) (0 - 0 + 1)).continuousOn (hF.mixed j 0).continuousOn
            (hG.mixed b 0).continuousOn hmemF hmemG
            (fun z θ hz hθ hθ2 =>
              hsupC α g hα hα1 hG hmemG (b - j) (0 - 0 + 1) hidx4 z θ hz hθ hθ2)
            (fun z θ hz hθ hθ2 => by
              simpa only [Work.Spaces.mixed_zero_right] using
                (T1SlotZ.canonW_mul_z_le_int (α := α) (q := q) (h := f) hqη'
                  ⟨hθ, hθ2⟩ j (by omega)))
            (fun z θ hz hθ hθ2 => by
              simpa only [Work.Spaces.mixed_zero_right] using
                (T1SlotZ.canonW_mul_z_le_int (α := α) (q := q) (h := g) hqη'
                  ⟨hθ, hθ2⟩ b (by omega)))
            z hz)
      · -- ## Case D: `i = 0`, `a ≥ 1` — the exceptional configuration `(a,b,j) = (1,5,5)`
        have hcfg : a = 1 ∧ b = 5 ∧ j = 5 := by omega
        simp only [hi0, hcfg.1, hcfg.2.1, hcfg.2.2, Nat.sub_self, Nat.sub_zero,
          Work.Spaces.mixed_zero_right]
        obtain ⟨C5, _hC5pos, h5raw⟩ := excDz5_mixed_pair_bound 0 2 (by norm_num) (by norm_num)
        obtain ⟨hAmem, _hAsq⟩ := h5raw α f g hα hα1 hF hmemF hG hmemG
        set B : ℝ → ℝ → ℝ := fun z θ => Work.Spaces.mixed 5 1 g z θ * Work.Spaces.Wt α z θ
          with hBdef
        have hBval : ∀ z θ, B z θ = Work.Spaces.mixed 5 1 g z θ * Work.Spaces.Wt α z θ :=
          fun z θ => by rw [hBdef]
        have hBcont : ContinuousOn (Function.uncurry B) Work.FTS.EllipticEst.Q0 := by
          rw [show Function.uncurry B = Function.uncurry (fun z θ =>
              Work.Spaces.mixed 5 1 g z θ * Work.Spaces.Wt α z θ) from by
            funext p; exact hBval p.1 p.2]
          exact (hG.mixed 5 1).continuousOn.mul (T1SlotZ.continuousOn_Wt_Q0 α)
        have hBpt : ∀ z θ : ℝ, 0 ≤ z → 0 < θ → θ < Real.pi / 2 →
            (B z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 g z θ := by
          intro z θ _hz hθ hθ2
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
        obtain ⟨hBmem, _hBsq⟩ := T1SlotZ.L2Mem_of_le_HkIntegrand (α := α) (B := B) (g := g)
          hBcont hmemG hBaesm hBpt
        intro z hz
        rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
        · subst h0
          rw [show (fun θ : ℝ => canonW q 0 θ * |Work.Spaces.DzIter 5 f 0 θ|
                * |Work.Spaces.mixed 0 2 g 0 θ| * |Work.Spaces.mixed 5 1 g 0 θ|)
              = fun _ => (0 : ℝ) from by
            funext θ
            rw [canonW_zero_z, zero_mul, zero_mul, zero_mul]]
          exact integrableOn_zero
        · refine TermSixAux.sliceIntCS (z := z)
            (A := fun z θ => Work.Spaces.DzIter 5 f z θ
              * Work.Spaces.mixed 0 2 g z θ * Work.Spaces.Wt α z θ)
            (B := B)
            (S := fun z θ => canonW q z θ * |Work.Spaces.DzIter 5 f z θ|
              * |Work.Spaces.mixed 0 2 g z θ| * |Work.Spaces.mixed 5 1 g z θ|)
            hz0 ?_ (hAmem.1 z hz) (hBmem.1 z hz) ?_
          · show ContinuousOn (fun p : ℝ × ℝ => canonW q p.1 p.2
                * |Work.Spaces.DzIter 5 f p.1 p.2| * |Work.Spaces.mixed 0 2 g p.1 p.2|
                * |Work.Spaces.mixed 5 1 g p.1 p.2|) Work.FTS.EllipticEst.Q0
            exact (((Work.FTS.TransportS.SlotT2.continuousOn_canonW q).mul
              (hF.DzIter 5).continuousOn.abs).mul
              (hG.mixed 0 2).continuousOn.abs).mul (hG.mixed 5 1).continuousOn.abs
          · intro θ hθ hθ2
            have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.le, hθ2.le⟩
            have hWtnn : 0 ≤ Work.Spaces.Wt α z θ := by
              rw [Work.Spaces.Wt, Work.Spaces.wTheta]
              exact mul_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))
                (Real.rpow_nonneg (le_of_lt (Real.sin_pos_of_pos_of_lt_pi
                  (by linarith) (by linarith))) _)
            have hcan : canonW q z θ ≤ (Work.Spaces.Wt α z θ) ^ 2 := by
              rw [← canonW_gam_eq α z θ hθI]
              exact T1SlotZ.canonW_le_int hqγ ⟨hθ, hθ2⟩
            have hSnn : 0 ≤ canonW q z θ * |Work.Spaces.DzIter 5 f z θ|
                * |Work.Spaces.mixed 0 2 g z θ| * |Work.Spaces.mixed 5 1 g z θ| :=
              mul_nonneg (mul_nonneg (mul_nonneg (canonW_nonneg hθI) (abs_nonneg _))
                (abs_nonneg _)) (abs_nonneg _)
            have h1 : |(fun z θ : ℝ => canonW q z θ * |Work.Spaces.DzIter 5 f z θ|
                  * |Work.Spaces.mixed 0 2 g z θ| * |Work.Spaces.mixed 5 1 g z θ|) z θ|
                ≤ (Work.Spaces.Wt α z θ) ^ 2 * |Work.Spaces.DzIter 5 f z θ|
                  * |Work.Spaces.mixed 0 2 g z θ| * |Work.Spaces.mixed 5 1 g z θ| := by
              rw [abs_of_nonneg hSnn]
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcan (abs_nonneg _))
                  (abs_nonneg _)) (abs_nonneg _)
            have h2 : (Work.Spaces.Wt α z θ) ^ 2 * |Work.Spaces.DzIter 5 f z θ|
                  * |Work.Spaces.mixed 0 2 g z θ| * |Work.Spaces.mixed 5 1 g z θ|
                = |(fun z θ : ℝ => Work.Spaces.DzIter 5 f z θ
                      * Work.Spaces.mixed 0 2 g z θ * Work.Spaces.Wt α z θ) z θ
                    * (fun z θ : ℝ => Work.Spaces.mixed 5 1 g z θ * Work.Spaces.Wt α z θ)
                        z θ| := by
              rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hWtnn]
              ring
            exact h1.trans (le_of_eq h2)
    · -- ## Case B: `i ≥ 1` — the sup goes on the middle `g`-slot
      have hi1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi0
      have ha1 : 1 ≤ a := by omega
      have hidx4 : (a - i + 1) + (b - j) ≤ 4 := by omega
      have hidx6 : i + j ≤ 6 := by omega
      have hMnn : 0 ≤ C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 g :=
        mul_nonneg (mul_nonneg hCpos.le (Real.rpow_nonneg hα.le _))
          (Work.Spaces.HkNorm_nonneg α 6 g)
      refine fun z hz => canonW_abs_swap_slice (q := q) (z := z)
        (X := fun z θ => Work.Spaces.mixed (b - j) (a - i + 1) g z θ)
        (Y := fun z θ => Work.Spaces.mixed j i f z θ)
        (Z := fun z θ => Work.Spaces.mixed b a g z θ)
        (TermSixAux.sliceIntSup (α := α) (q := q)
          (M := C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 g)
          (X := fun z θ => Work.Spaces.mixed (b - j) (a - i + 1) g z θ)
          (Y := fun z θ => Work.Spaces.mixed j i f z θ)
          (Z := fun z θ => Work.Spaces.mixed b a g z θ)
          (h₁ := f) (h₂ := g)
          hMnn (hG.mixed (b - j) (a - i + 1)).continuousOn (hF.mixed j i).continuousOn
          (hG.mixed b a).continuousOn hmemF hmemG
          (fun z θ hz hθ hθ2 =>
            hsupC α g hα hα1 hG hmemG (b - j) (a - i + 1) hidx4 z θ hz hθ hθ2)
          (fun z θ hz hθ hθ2 =>
            T1SlotZ.canonW_mul_mixed_le_int (α := α) (q := q) hqγ ⟨hθ, hθ2⟩
              j i hi1 hidx6)
          (fun z θ hz hθ hθ2 =>
            T1SlotZ.canonW_mul_mixed_le_int (α := α) (q := q) hqγ ⟨hθ, hθ2⟩
              b a ha1 (by omega))
          z hz)

end Work.FTS.StrongPersist.N6Trans.T1SixAux
