import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Order.Group.Lattice

namespace Commons.Analysis.CalderonZygmund

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

noncomputable section

/-- Translation by `d` composed with negation preserves Lebesgue measure on `ℝ`. -/
lemma map_neg_add_eq (d : ℝ) : Measure.map (fun y : ℝ => -y + d) volume = volume := by
  have hN : Measure.map (fun y : ℝ => -y) volume = volume := Measure.map_neg_eq_self volume
  have hA : Measure.map (fun z : ℝ => z + d) volume = volume := map_add_right_eq_self volume d
  have hmm : Measure.map (fun y : ℝ => -y + d) volume
      = Measure.map (fun z : ℝ => z + d) (Measure.map (fun y : ℝ => -y) volume) := by
    rw [Measure.map_map]
    · rfl
    · fun_prop
    · fun_prop
  rw [hmm, hN, hA]

/-- The shear `(u, y) ↦ u - y + c` is quasi-measure-preserving for Lebesgue measure. -/
lemma qmp_shear (c : ℝ) :
    Measure.QuasiMeasurePreserving (fun p : ℝ × ℝ => p.1 - p.2 + c) (volume.prod volume) volume := by
  set ψ : ℝ × ℝ → ℝ := fun p => p.1 - p.2 + c with hψ
  have hψm : Measurable ψ := by rw [hψ]; fun_prop
  refine ⟨hψm, ?_⟩
  have hle : Measure.map ψ (volume.prod volume) ≤ (⊤ : ℝ≥0∞) • volume := by
    rw [Measure.le_iff]
    intro s hs
    have hpre : MeasurableSet (ψ ⁻¹' s) := hψm hs
    rw [Measure.map_apply hψm hs, Measure.prod_apply hpre]
    have hinner : ∀ u : ℝ, volume (Prod.mk u ⁻¹' ψ ⁻¹' s) = volume s := by
      intro u
      have hset : Prod.mk u ⁻¹' ψ ⁻¹' s = (fun y : ℝ => -y + (u + c)) ⁻¹' s := by
        ext y; simp only [Set.mem_preimage]; rw [hψ]; ring_nf
      rw [hset, ← Measure.map_apply (by fun_prop : Measurable fun y : ℝ => -y + (u + c)) hs,
        map_neg_add_eq]
    simp_rw [hinner]
    rw [lintegral_const, Measure.smul_apply, smul_eq_mul]
    calc volume s * volume Set.univ ≤ volume s * (⊤ : ℝ≥0∞) := by gcongr; exact le_top
      _ = (⊤ : ℝ≥0∞) * volume s := mul_comm _ _
  exact (Measure.absolutelyContinuous_of_le hle).trans Measure.smul_absolutelyContinuous

/-- The first projection `ℝ × ℝ → ℝ` is quasi-measure-preserving for Lebesgue measure. -/
lemma qmp_fst : Measure.QuasiMeasurePreserving (Prod.fst : ℝ × ℝ → ℝ) (volume.prod volume) volume :=
  ⟨measurable_fst, by rw [Measure.map_fst_prod]; exact Measure.smul_absolutelyContinuous⟩

/-- The second projection `ℝ × ℝ → ℝ` is quasi-measure-preserving for Lebesgue measure. -/
lemma qmp_snd : Measure.QuasiMeasurePreserving (Prod.snd : ℝ × ℝ → ℝ) (volume.prod volume) volume :=
  ⟨measurable_snd, by rw [Measure.map_snd_prod]; exact Measure.smul_absolutelyContinuous⟩

/-- Translation `x ↦ x - c` preserves Lebesgue measure on `ℝ`. -/
lemma qmp_sub_const (c : ℝ) :
    Measure.QuasiMeasurePreserving (fun x : ℝ => x - c) volume volume := by
  refine ⟨by fun_prop, ?_⟩
  have : (fun x : ℝ => x - c) = fun x : ℝ => x + (-c) := by funext x; ring
  rw [this, map_add_right_eq_self]

/-- Reflection followed by translation `y ↦ x - y` preserves Lebesgue measure on `ℝ`. -/
lemma qmp_const_sub (x : ℝ) :
    Measure.QuasiMeasurePreserving (fun y : ℝ => x - y) volume volume := by
  refine ⟨by fun_prop, ?_⟩
  have : (fun y : ℝ => x - y) = fun y : ℝ => -y + x := by funext y; ring
  rw [this, map_neg_add_eq]

theorem cz_bad_part_interval_lintegral {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [CompleteSpace H] (K : ℝ → ℂ) (Ak : ℝ) (hAk : 0 ≤ Ak)
    (hKmeas : MeasureTheory.AEStronglyMeasurable K MeasureTheory.volume)
    (hker : ∀ L : ℝ, 0 < L → ∀ y : ℝ, |y| ≤ L / 2 →
      ∫⁻ x in {x : ℝ | 50 * L ≤ |x|}, ‖K (x - y) - K x‖ₑ ≤ ENNReal.ofReal Ak)
    (a b : ℝ) (hab : a ≤ b) (w : ℝ → H) (hw : MeasureTheory.Integrable w)
    (hwsupp : ∀ x, x ∉ Set.Ioo a b → w x = 0)
    (hwmean : ∫ x in Set.Ioo a b, w x = 0) :
    ∫⁻ x in {x : ℝ | 50 * (b - a) ≤ |x - (a + b) / 2|}, ‖∫ y : ℝ, K (x - y) • w y‖ₑ
      ≤ ENNReal.ofReal Ak * ∫⁻ y, ‖w y‖ₑ := by
  by_cases hLpos : 0 < b - a
  · set L : ℝ := b - a with hL
    set c : ℝ := (a + b) / 2 with hc
    have hLpos' : 0 < L := by rw [hL]; exact hLpos
    -- Step 1: pointwise bound
    have hpt : ∀ x : ℝ, ‖∫ y : ℝ, K (x - y) • w y‖ₑ
        ≤ ∫⁻ y : ℝ, ‖K (x - y) - K (x - c)‖ₑ * ‖w y‖ₑ := by
      intro x
      have hfx : (∫⁻ y : ℝ, ‖(K (x - y) - K (x - c)) • w y‖ₑ)
          = ∫⁻ y : ℝ, ‖K (x - y) - K (x - c)‖ₑ * ‖w y‖ₑ := by
        apply lintegral_congr; intro y; rw [enorm_smul]
      by_cases hfin : (∫⁻ y : ℝ, ‖(K (x - y) - K (x - c)) • w y‖ₑ) < ⊤
      · have haesm : AEStronglyMeasurable
            (fun y : ℝ => (K (x - y) - K (x - c)) • w y) volume :=
          ((hKmeas.comp_quasiMeasurePreserving (qmp_const_sub x)).sub
            aestronglyMeasurable_const).smul hw.aestronglyMeasurable
        have hint : Integrable (fun y : ℝ => (K (x - y) - K (x - c)) • w y) volume :=
          ⟨haesm, hfin⟩
        have hint2 : Integrable (fun y : ℝ => K (x - c) • w y) volume :=
          Integrable.smul (K (x - c)) hw
        have hzero : ∫ y : ℝ, K (x - c) • w y = 0 := by
          rw [integral_smul]
          have hw0 : ∫ y : ℝ, w y = 0 := by
            rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hwsupp, hwmean]
          rw [hw0, smul_zero]
        have hsplit : ∫ y : ℝ, K (x - y) • w y
            = ∫ y : ℝ, (K (x - y) - K (x - c)) • w y := by
          have h1 : (∫ y : ℝ, K (x - y) • w y)
              = ∫ y : ℝ, ((K (x - y) - K (x - c)) • w y + K (x - c) • w y) := by
            apply integral_congr_ae; filter_upwards with y; rw [← add_smul, sub_add_cancel]
          rw [h1]
          rw [integral_add hint hint2]
          rw [hzero]
          simp
        calc ‖∫ y : ℝ, K (x - y) • w y‖ₑ
            = ‖∫ y : ℝ, (K (x - y) - K (x - c)) • w y‖ₑ := by rw [hsplit]
          _ ≤ ∫⁻ y : ℝ, ‖(K (x - y) - K (x - c)) • w y‖ₑ :=
              enorm_integral_le_lintegral_enorm _
          _ = ∫⁻ y : ℝ, ‖K (x - y) - K (x - c)‖ₑ * ‖w y‖ₑ := hfx
      · have htop : (∫⁻ y : ℝ, ‖K (x - y) - K (x - c)‖ₑ * ‖w y‖ₑ) = ⊤ :=
          hfx.symm.trans (top_le_iff.mp (not_lt.mp hfin))
        rw [htop]; exact le_top
    -- Step 2
    have hstep2 : ∫⁻ x in {x : ℝ | 50 * L ≤ |x - c|}, ‖∫ y : ℝ, K (x - y) • w y‖ₑ
        ≤ ∫⁻ x in {x : ℝ | 50 * L ≤ |x - c|},
            ∫⁻ y : ℝ, ‖K (x - y) - K (x - c)‖ₑ * ‖w y‖ₑ :=
      lintegral_mono hpt
    -- Step 3: Tonelli
    have hF_aem : AEMeasurable
        (Function.uncurry (fun x y : ℝ => ‖K (x - y) - K (x - c)‖ₑ * ‖w y‖ₑ))
        (volume.prod volume) := by
      have hKa : AEMeasurable (fun p : ℝ × ℝ => K (p.1 - p.2)) (volume.prod volume) := by
        have h := hKmeas.aemeasurable.comp_quasiMeasurePreserving (qmp_shear 0)
        refine h.congr ?_
        filter_upwards with p
        simp
      have hKb : AEMeasurable (fun p : ℝ × ℝ => K (p.1 - c)) (volume.prod volume) := by
        have h1 : AEMeasurable (fun x : ℝ => K (x - c)) volume :=
          hKmeas.aemeasurable.comp_quasiMeasurePreserving (qmp_sub_const c)
        have h2 := h1.comp_quasiMeasurePreserving qmp_fst
        refine h2.congr ?_
        filter_upwards with p
        rfl
      have hKw : AEMeasurable (fun p : ℝ × ℝ => ‖w p.2‖ₑ) (volume.prod volume) := by
        have h1 : AEMeasurable (fun y : ℝ => ‖w y‖ₑ) volume := hw.aestronglyMeasurable.enorm
        have h2 := h1.comp_quasiMeasurePreserving qmp_snd
        refine h2.congr ?_
        filter_upwards with p
        rfl
      exact ((hKa.sub hKb).enorm).mul hKw
    have hstep3 : ∫⁻ x in {x : ℝ | 50 * L ≤ |x - c|},
            ∫⁻ y : ℝ, ‖K (x - y) - K (x - c)‖ₑ * ‖w y‖ₑ
        = ∫⁻ y : ℝ, ‖w y‖ₑ * ∫⁻ x in {x : ℝ | 50 * L ≤ |x - c|},
            ‖K (x - y) - K (x - c)‖ₑ := by
      have hac : (volume.restrict {x : ℝ | 50 * L ≤ |x - c|}).prod (volume : Measure ℝ)
          ≪ (volume : Measure ℝ).prod (volume : Measure ℝ) :=
        Measure.absolutelyContinuous_of_le
          (Measure.prod_mono (Measure.restrict_le_self (μ := (volume : Measure ℝ))) le_rfl)
      have hswap := lintegral_lintegral_swap
        (μ := volume.restrict {x : ℝ | 50 * L ≤ |x - c|}) (ν := volume)
        (f := fun x y : ℝ => ‖K (x - y) - K (x - c)‖ₑ * ‖w y‖ₑ) (hF_aem.mono' hac)
      rw [hswap]
      apply lintegral_congr; intro y
      rw [lintegral_mul_const' _ _ (enorm_ne_top (x := w y)), mul_comm]
    -- Step 4
    have hsS : MeasurableSet {x : ℝ | 50 * L ≤ |x - c|} :=
      measurableSet_le measurable_const (by fun_prop)
    have hsS' : MeasurableSet {u : ℝ | 50 * L ≤ |u|} :=
      measurableSet_le measurable_const (by fun_prop)
    have hstep4 : ∫⁻ y : ℝ, ‖w y‖ₑ * ∫⁻ x in {x : ℝ | 50 * L ≤ |x - c|},
            ‖K (x - y) - K (x - c)‖ₑ
        ≤ ∫⁻ y : ℝ, ENNReal.ofReal Ak * ‖w y‖ₑ := by
      apply lintegral_mono; intro y
      dsimp only
      by_cases hy : y ∈ Set.Icc a b
      · have hyc : |y - c| ≤ L / 2 := by
          rw [hc, hL, abs_le]
          constructor <;> linarith [hy.1, hy.2]
        have hkey := hker L hLpos' (y - c) hyc
        have hconv : ∫⁻ x in {x : ℝ | 50 * L ≤ |x - c|}, ‖K (x - y) - K (x - c)‖ₑ
            = ∫⁻ u in {u : ℝ | 50 * L ≤ |u|}, ‖K (u - (y - c)) - K u‖ₑ := by
          rw [← lintegral_indicator hsS, ← lintegral_indicator hsS']
          rw [show (∫⁻ x : ℝ, {x : ℝ | 50 * L ≤ |x - c|}.indicator
                  (fun x => ‖K (x - y) - K (x - c)‖ₑ) x)
              = ∫⁻ x : ℝ, {u : ℝ | 50 * L ≤ |u|}.indicator
                  (fun u => ‖K (u - (y - c)) - K u‖ₑ) (x + (-c)) from by
                apply lintegral_congr; intro x
                have hxc : x + (-c) = x - c := by ring
                rw [hxc]
                by_cases hx : x ∈ {x : ℝ | 50 * L ≤ |x - c|}
                · have hx' : x - c ∈ {u : ℝ | 50 * L ≤ |u|} := hx
                  rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx']
                  congr 1
                  rw [show (x - c) - (y - c) = x - y from by ring]
                · have hx' : x - c ∉ {u : ℝ | 50 * L ≤ |u|} := hx
                  rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx']]
          rw [lintegral_add_right_eq_self]
        rw [hconv]
        calc ‖w y‖ₑ * ∫⁻ u in {u : ℝ | 50 * L ≤ |u|}, ‖K (u - (y - c)) - K u‖ₑ
            ≤ ‖w y‖ₑ * ENNReal.ofReal Ak := mul_le_mul_of_nonneg_left hkey bot_le
          _ = ENNReal.ofReal Ak * ‖w y‖ₑ := mul_comm _ _
      · have hwy : w y = 0 := hwsupp y (fun hmem => hy (Set.Ioo_subset_Icc_self hmem))
        simp [hwy]
    show ∫⁻ x in {x : ℝ | 50 * L ≤ |x - c|}, ‖∫ y : ℝ, K (x - y) • w y‖ₑ
      ≤ ENNReal.ofReal Ak * ∫⁻ y, ‖w y‖ₑ
    calc ∫⁻ x in {x : ℝ | 50 * L ≤ |x - c|}, ‖∫ y : ℝ, K (x - y) • w y‖ₑ
        ≤ ∫⁻ x in {x : ℝ | 50 * L ≤ |x - c|},
            ∫⁻ y : ℝ, ‖K (x - y) - K (x - c)‖ₑ * ‖w y‖ₑ := hstep2
      _ = ∫⁻ y : ℝ, ‖w y‖ₑ * ∫⁻ x in {x : ℝ | 50 * L ≤ |x - c|},
            ‖K (x - y) - K (x - c)‖ₑ := hstep3
      _ ≤ ∫⁻ y : ℝ, ENNReal.ofReal Ak * ‖w y‖ₑ := hstep4
      _ = ENNReal.ofReal Ak * ∫⁻ y, ‖w y‖ₑ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  · have hba : b = a := by linarith
    have hw0 : ∀ x : ℝ, w x = 0 := fun x => hwsupp x (by rw [hba]; simp)
    have hzero : ∀ x : ℝ, ∫ y : ℝ, K (x - y) • w y = 0 := by
      intro x
      have hfun : (fun y : ℝ => K (x - y) • w y) = fun _ => (0 : H) := by
        funext y; rw [hw0 y, smul_zero]
      rw [hfun, integral_zero]
    rw [show (fun x : ℝ => ‖∫ y : ℝ, K (x - y) • w y‖ₑ) = fun _ => (0 : ℝ≥0∞) by
        funext x; rw [hzero x, enorm_zero]]
    simp

end

end Commons.Analysis.CalderonZygmund