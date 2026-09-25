import Mathlib
import Submission.Commons.Analysis.Maximal.real_maximal_weak_type

namespace Commons.Analysis.HardyLittlewood

open MeasureTheory Set
open scoped ENNReal
open Commons.Analysis.Maximal (hlMax)

/-! ### Measurability of even, radially non-increasing kernels -/

/-- An even function `ℝ → ℝ≥0∞` which is non-increasing in the absolute value is measurable.
(The radial monotonicity is expressed by saying that `K` is antitone on `[0,∞)`, and evenness
transports this to all of `ℝ` through the continuous map `|·|`.) -/
theorem measurable_of_even_antitone_on_nonneg {K : ℝ → ℝ≥0∞}
    (hsym : ∀ y, K (-y) = K y) (hmono : ∀ x y : ℝ, 0 ≤ x → x ≤ y → K y ≤ K x) :
    Measurable K := by
  have hK' : Measurable (fun t : {t : ℝ // 0 ≤ t} => K (t : ℝ)) :=
    (show Antitone (fun t : {t : ℝ // 0 ≤ t} => K (t : ℝ)) from
      fun u v huv => hmono (u : ℝ) (v : ℝ) u.2 huv).measurable
  have hcont : Continuous (fun t : ℝ => (⟨|t|, abs_nonneg t⟩ : {t : ℝ // 0 ≤ t})) :=
    continuous_abs.subtype_mk (fun t => abs_nonneg t)
  have hcomp : Measurable (fun t : ℝ => K |t|) := hK'.comp hcont.measurable
  have hfun : (fun t : ℝ => K |t|) = K := by
    funext t
    rcases lt_or_ge 0 t with h | h
    · rw [abs_of_pos h]
    · rw [abs_of_nonpos h, ← hsym t]
  rwa [hfun] at hcomp

/-- An even kernel agrees with its radial profile: `K y = K |y|`. -/
theorem even_kernel_eq_abs {K : ℝ → ℝ≥0∞} (hsym : ∀ y, K (-y) = K y) (y : ℝ) :
    K y = K |y| := by
  rcases le_total 0 y with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h, ← hsym y]

/-! ### Layer cake for `ℝ≥0∞`-valued functions -/

/-- The measure of the level set `{t > 0 | t < a}` in the reals is `a`. -/
theorem volume_ofReal_lt_eq (a : ℝ≥0∞) : volume {t : ℝ | 0 < t ∧ ENNReal.ofReal t < a} = a := by
  rcases eq_or_ne a ⊤ with rfl | ha
  · have : {t : ℝ | 0 < t ∧ ENNReal.ofReal t < ⊤} = Set.Ioi 0 := by
      ext t; simp
    rw [this, Real.volume_Ioi]
  · have hset : {t : ℝ | 0 < t ∧ ENNReal.ofReal t < a} = Set.Ioo 0 a.toReal := by
      ext t
      constructor
      · rintro ⟨ht, hlt⟩
        exact ⟨ht, (ENNReal.ofReal_lt_iff_lt_toReal ht.le ha).mp hlt⟩
      · rintro ⟨ht, hlt⟩
        exact ⟨ht, (ENNReal.ofReal_lt_iff_lt_toReal ht.le ha).mpr hlt⟩
    rw [hset, Real.volume_Ioo, sub_zero, ENNReal.ofReal_toReal ha]

/-- **Layer cake formula for `ℝ≥0∞`-valued functions.**  For measurable `f, g : α → ℝ≥0∞` on an
s-finite measure space, the integral of `g * f` can be computed by integrating the integrals of
`g` over the super-level sets `{a | ofReal t < f a}`.  This is the `ℝ≥0∞`-valued, weighted
version of Tonelli's theorem applied to the layer cake decomposition of `f`. -/
theorem lintegral_mul_eq_lintegral_setLIntegral_lt {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SFinite μ] {f g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ a, g a * f a ∂μ
      = ∫⁻ t in Set.Ioi (0:ℝ), ∫⁻ a in {a : α | ENNReal.ofReal t < f a}, g a ∂μ := by
  have hS_meas : ∀ t : ℝ, MeasurableSet {a : α | ENNReal.ofReal t < f a} :=
    fun t => hf measurableSet_Ioi
  have hT_meas : ∀ a : α, MeasurableSet {t : ℝ | 0 < t ∧ ENNReal.ofReal t < f a} := by
    intro a
    exact measurableSet_Ioi.inter (ENNReal.measurable_ofReal measurableSet_Iio)
  have hkey : ∀ a : α, f a
      = ∫⁻ t : ℝ, (if 0 < t ∧ ENNReal.ofReal t < f a then (1:ℝ≥0∞) else 0) := by
    intro a
    have h1 : ∫⁻ t : ℝ, (if 0 < t ∧ ENNReal.ofReal t < f a then (1:ℝ≥0∞) else 0)
        = volume {t : ℝ | 0 < t ∧ ENNReal.ofReal t < f a} := by
      have h2 : (fun t : ℝ => (if 0 < t ∧ ENNReal.ofReal t < f a then (1:ℝ≥0∞) else 0))
          = ({t : ℝ | 0 < t ∧ ENNReal.ofReal t < f a} : Set ℝ).indicator (fun _ => (1:ℝ≥0∞)) := by
        funext t; simp only [Set.indicator_apply, Set.mem_ofPred_eq]
      rw [h2, lintegral_indicator (hT_meas a), setLIntegral_const, one_mul]
    conv_lhs => rw [← volume_ofReal_lt_eq (f a)]
    exact h1.symm
  have hInd : MeasurableSet {p : ℝ × α | 0 < p.1 ∧ ENNReal.ofReal p.1 < f p.2} :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt (measurable_fst.ennreal_ofReal) (hf.comp measurable_snd))
  have huncurry_meas : Measurable (Function.uncurry (fun t (a : α) =>
      g a * (if 0 < t ∧ ENNReal.ofReal t < f a then (1:ℝ≥0∞) else 0))) :=
    (hg.comp measurable_snd).mul (measurable_const.ite hInd measurable_const)
  calc ∫⁻ a, g a * f a ∂μ
      = ∫⁻ a, g a * (∫⁻ t : ℝ,
          (if 0 < t ∧ ENNReal.ofReal t < f a then (1:ℝ≥0∞) else 0)) ∂μ := by
        apply lintegral_congr; intro a
        conv_lhs => rw [hkey a]
    _ = ∫⁻ a, ∫⁻ t : ℝ,
          g a * (if 0 < t ∧ ENNReal.ofReal t < f a then (1:ℝ≥0∞) else 0) ∂volume ∂μ := by
        apply lintegral_congr; intro a
        exact (lintegral_const_mul (g a) (measurable_const.ite (hT_meas a) measurable_const)).symm
    _ = ∫⁻ t : ℝ, ∫⁻ a,
          g a * (if 0 < t ∧ ENNReal.ofReal t < f a then (1:ℝ≥0∞) else 0) ∂μ ∂volume := by
        exact (lintegral_lintegral_swap (μ := volume) (ν := μ)
          (f := fun t (a : α) => g a * (if 0 < t ∧ ENNReal.ofReal t < f a then (1:ℝ≥0∞) else 0))
          huncurry_meas.aemeasurable).symm
    _ = ∫⁻ t : ℝ,
          (if 0 < t then ∫⁻ a in {a : α | ENNReal.ofReal t < f a}, g a ∂μ else 0) ∂volume := by
        apply lintegral_congr; intro t
        by_cases ht : 0 < t
        · have hpt : ∀ a : α, g a * (if 0 < t ∧ ENNReal.ofReal t < f a then (1:ℝ≥0∞) else 0)
              = ({a : α | ENNReal.ofReal t < f a}).indicator g a := by
            intro a
            simp only [Set.indicator_apply, Set.mem_ofPred_eq]
            by_cases h : ENNReal.ofReal t < f a
            · rw [if_pos ⟨ht, h⟩, if_pos h, mul_one]
            · rw [if_neg (by rintro ⟨_, h2⟩; exact h h2), if_neg h, mul_zero]
          rw [if_pos ht, lintegral_congr hpt, lintegral_indicator (hS_meas t)]
        · have hpt : ∀ a : α,
              g a * (if 0 < t ∧ ENNReal.ofReal t < f a then (1:ℝ≥0∞) else 0) = 0 := by
            intro a
            rw [if_neg (by rintro ⟨h1, _⟩; exact ht h1), mul_zero]
          have hz : ∫⁻ a, g a * (if 0 < t ∧ ENNReal.ofReal t < f a then (1:ℝ≥0∞) else 0) ∂μ = 0 := by
            rw [lintegral_congr hpt]
            exact lintegral_zero
          rw [if_neg ht]
          exact hz
    _ = ∫⁻ t in Set.Ioi (0:ℝ), ∫⁻ a in {a : α | ENNReal.ofReal t < f a}, g a ∂μ := by
        rw [← lintegral_indicator measurableSet_Ioi]
        apply lintegral_congr; intro t
        simp only [Set.indicator_apply, Set.mem_Ioi]

/-! ### The Hardy–Littlewood maximal function dominates interval averages -/

/-- Any interval `[a,b]` containing `x` has its average of `g` bounded by the centred maximal
function at `x`: `∫_{[a,b]} g ≤ hlMax g x * volume [a,b]`. -/
theorem lintegral_Icc_le_hlMax_mul_volume (g : ℝ → ℝ≥0∞) {a b x : ℝ} (ha : a ≤ x) (hb : x ≤ b) :
    ∫⁻ y in Set.Icc a b, g y ≤ hlMax g x * volume (Set.Icc a b) := by
  have hM : ENNReal.ofReal (b - a)⁻¹ * ∫⁻ y in Set.Icc a b, g y ≤ hlMax g x := by
    rw [hlMax]
    exact le_iSup_of_le a (le_iSup_of_le b (le_iSup_of_le ⟨ha, hb⟩ le_rfl))
  rw [Real.volume_Icc]
  rcases lt_or_ge a b with h | h
  · have hpos : 0 < b - a := sub_pos.mpr h
    have hne : ENNReal.ofReal (b - a) ≠ 0 := (ENNReal.ofReal_pos.mpr hpos).ne'
    have htop : ENNReal.ofReal (b - a) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hmul : ENNReal.ofReal (b - a) * ENNReal.ofReal (b - a)⁻¹ = 1 := by
      rw [ENNReal.ofReal_inv_of_pos hpos, ENNReal.mul_inv_cancel hne htop]
    calc ∫⁻ y in Set.Icc a b, g y
        = 1 * ∫⁻ y in Set.Icc a b, g y := (one_mul _).symm
      _ = (ENNReal.ofReal (b - a) * ENNReal.ofReal (b - a)⁻¹) * ∫⁻ y in Set.Icc a b, g y := by
            rw [hmul]
      _ = ENNReal.ofReal (b - a) * (ENNReal.ofReal (b - a)⁻¹ * ∫⁻ y in Set.Icc a b, g y) := by
            rw [mul_assoc]
      _ ≤ ENNReal.ofReal (b - a) * hlMax g x := mul_le_mul_right hM _
      _ = hlMax g x * ENNReal.ofReal (b - a) := mul_comm _ _
  · have hzero : ∫⁻ y in Set.Icc a b, g y = 0 := by
      have h1 : ∫⁻ y in Set.Icc a b, g y ≤ ∫⁻ y in Set.Icc a b, (⊤ : ℝ≥0∞) :=
        lintegral_mono fun y => le_top
      have h2 : ∫⁻ y in Set.Icc a b, (⊤ : ℝ≥0∞) = 0 := by
        rw [setLIntegral_const, Real.volume_Icc,
          ENNReal.ofReal_eq_zero.mpr (sub_nonpos.mpr h), mul_zero]
      exact le_antisymm (h1.trans h2.le) bot_le
    rw [hzero]; exact bot_le

/-- **Maximal function bound for interval integrals.**  If `I` is an interval (an `OrdConnected`
measurable set) containing `x`, then `∫_I g ≤ hlMax g x * volume I`.  This is proved by exhausting
`I` with the bounded intervals `I ∩ [x-n, x+n]` and comparing `volume (I ∩ [x-n,x+n])` with
`(sSup I ∩ [x-n,x+n]) - (sInf I ∩ [x-n,x+n])`. -/
theorem lintegral_le_hlMax_mul_volume_of_ordConnected {g : ℝ → ℝ≥0∞} (hg : Measurable g)
    {I : Set ℝ} (hI : I.OrdConnected) (hIm : MeasurableSet I) {x : ℝ} (hx : x ∈ I) :
    ∫⁻ y in I, g y ≤ hlMax g x * volume I := by
  set S : ℕ → Set ℝ := fun n => I ∩ Set.Icc (x - (n:ℝ)) (x + (n:ℝ)) with hSdef
  have hS_ord : ∀ n, (S n).OrdConnected := fun n =>
    hI.inter (Set.ordConnected_Icc (a := x - (n:ℝ)) (b := x + (n:ℝ)))
  have hS_meas : ∀ n, MeasurableSet (S n) := fun n => hIm.inter measurableSet_Icc
  have hS_mono : Monotone S := by
    intro m n hmn
    show I ∩ Set.Icc (x - (m:ℝ)) (x + (m:ℝ)) ⊆ I ∩ Set.Icc (x - (n:ℝ)) (x + (n:ℝ))
    have hmn' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    refine Set.inter_subset_inter_right I ?_
    refine Set.Icc_subset_Icc ?_ ?_
    · show x - (n:ℝ) ≤ x - (m:ℝ); linarith
    · show x + (m:ℝ) ≤ x + (n:ℝ); linarith
  have hSx : ∀ n, x ∈ S n := by
    intro n
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    exact ⟨hx, by constructor <;> linarith⟩
  have hI_eq : I = ⋃ n, S n := by
    refine Set.Subset.antisymm (fun y hy => ?_) (Set.iUnion_subset fun n => Set.inter_subset_left)
    obtain ⟨n, hn⟩ := exists_nat_ge |y - x|
    refine Set.mem_iUnion.mpr ⟨n, hy, ?_⟩
    obtain ⟨h1, h2⟩ := abs_le.mp hn
    exact ⟨by linarith, by linarith⟩
  have hpt : ∀ y, I.indicator g y = ⨆ n, (S n).indicator g y := by
    intro y
    by_cases hy : y ∈ I
    · obtain ⟨N, hN⟩ : ∃ N, y ∈ S N := by
        obtain ⟨n, hn⟩ := exists_nat_ge |y - x|
        obtain ⟨h1, h2⟩ := abs_le.mp hn
        exact ⟨n, hy, by constructor <;> linarith⟩
      refine le_antisymm ?_ ?_
      · rw [Set.indicator_of_mem hy g]
        exact le_iSup_of_le N (by rw [Set.indicator_of_mem hN g])
      · refine iSup_le (f := fun n => (S n).indicator g y) fun n => ?_
        by_cases h : y ∈ S n
        · rw [Set.indicator_of_mem h g, Set.indicator_of_mem hy g]
        · rw [Set.indicator_of_notMem h g]; exact bot_le
    · have h0 : ∀ n, y ∉ S n := fun n h => hy (Set.inter_subset_left h)
      rw [Set.indicator_of_notMem hy g]
      refine le_antisymm bot_le ?_
      refine iSup_le (f := fun n => (S n).indicator g y) fun n => ?_
      rw [Set.indicator_of_notMem (h0 n) g]
  have hind_mono : Monotone fun n => (S n).indicator g := by
    intro m n hmn
    show (S m).indicator g ≤ (S n).indicator g
    intro y
    by_cases h : y ∈ S m
    · rw [Set.indicator_of_mem h g, Set.indicator_of_mem (hS_mono hmn h) g]
    · rw [Set.indicator_of_notMem h g]; exact bot_le
  have hMCT : ∫⁻ y in I, g y = ⨆ n, ∫⁻ y in S n, g y := by
    have hstep1 : ∫⁻ y in I, g y = ∫⁻ y, ⨆ n, (S n).indicator g y := by
      rw [← lintegral_indicator hIm]
      exact lintegral_congr hpt
    have hstep2 : ∫⁻ y, ⨆ n, (S n).indicator g y = ⨆ n, ∫⁻ y in S n, g y := by
      rw [lintegral_iSup (f := fun n => (S n).indicator g) (fun n => hg.indicator (hS_meas n))
        hind_mono]
      exact iSup_congr fun n => lintegral_indicator (hS_meas n) g
    rw [hstep1, hstep2]
  have hbound : ∀ n, ∫⁻ y in S n, g y ≤ hlMax g x * volume (S n) := by
    intro n
    have hne : (S n).Nonempty := ⟨x, hSx n⟩
    have hbdd_below : BddBelow (S n) := ⟨x - (n:ℝ), fun y hy => hy.2.1⟩
    have hbdd_above : BddAbove (S n) := ⟨x + (n:ℝ), fun y hy => hy.2.2⟩
    have hcx : sInf (S n) ≤ x := csInf_le hbdd_below (hSx n)
    have hxd : x ≤ sSup (S n) := le_csSup hbdd_above (hSx n)
    have hsub : S n ⊆ Set.Icc (sInf (S n)) (sSup (S n)) := fun y hy =>
      ⟨csInf_le hbdd_below hy, le_csSup hbdd_above hy⟩
    have hvol : volume (S n) = ENNReal.ofReal (sSup (S n) - sInf (S n)) := by
      refine le_antisymm ?_ ?_
      · calc volume (S n) ≤ volume (Set.Icc (sInf (S n)) (sSup (S n))) := measure_mono hsub
          _ = ENNReal.ofReal (sSup (S n) - sInf (S n)) := Real.volume_Icc
      · have hsub' : Set.Ioo (sInf (S n)) (sSup (S n)) ⊆ S n := by
          intro z hz
          obtain ⟨hcz, hzd⟩ := hz
          obtain ⟨v, hv, hvz⟩ := (csInf_lt_iff hbdd_below hne).mp hcz
          obtain ⟨w, hw, hzw⟩ := (lt_csSup_iff hbdd_above hne).mp hzd
          exact (hS_ord n).out hv hw ⟨le_of_lt hvz, le_of_lt hzw⟩
        calc ENNReal.ofReal (sSup (S n) - sInf (S n))
            = volume (Set.Ioo (sInf (S n)) (sSup (S n))) := (Real.volume_Ioo).symm
          _ ≤ volume (S n) := measure_mono hsub'
    calc ∫⁻ y in S n, g y ≤ ∫⁻ y in Set.Icc (sInf (S n)) (sSup (S n)), g y :=
          lintegral_mono_set hsub
      _ ≤ hlMax g x * volume (Set.Icc (sInf (S n)) (sSup (S n))) :=
          lintegral_Icc_le_hlMax_mul_volume g hcx hxd
      _ = hlMax g x * volume (S n) := by rw [Real.volume_Icc, hvol]
  calc ∫⁻ y in I, g y = ⨆ n, ∫⁻ y in S n, g y := hMCT
    _ ≤ ⨆ n, hlMax g x * volume (S n) := iSup_mono hbound
    _ = hlMax g x * ⨆ n, volume (S n) := (ENNReal.mul_iSup _ _).symm
    _ = hlMax g x * volume I := by rw [hI_eq, Monotone.measure_iUnion hS_mono]

/-! ### Domination of a radial convolution by the Hardy–Littlewood maximal function -/

/-- **Domination of a convolution with a radially non-increasing kernel by the
Hardy–Littlewood maximal function.**  If `K : ℝ → ℝ≥0∞` is even and non-increasing along
`|·|`, then for every measurable `g : ℝ → ℝ≥0∞` and every `x`,
`∫⁻ y, g y * K (x - y) ≤ (∫⁻ y, K y) * hlMax g x`.
This is the classical layer-cake comparison: for each `s` the superlevel set
`{y | s < K (y - x)}` is an interval around `x`, so each layer of the convolution is
bounded by the corresponding interval average of `g`, and
`∫_0^∞ |{t | s < K t}| ds = ∫⁻ t, K t`. -/
theorem lintegral_convolution_radial_decreasing_measurable_le_hlMax
    (K : ℝ → ENNReal) (hsym : ∀ y, K (-y) = K y)
    (hmono : ∀ x y : ℝ, 0 ≤ x → x ≤ y → K y ≤ K x)
    (g : ℝ → ENNReal) (hg : Measurable g) (x : ℝ) :
    MeasureTheory.lintegral MeasureTheory.volume (fun y : ℝ => g y * K (x - y))
      ≤ MeasureTheory.lintegral MeasureTheory.volume K
        * Commons.Analysis.Maximal.hlMax g x := by
  have hK_meas : Measurable K := measurable_of_even_antitone_on_nonneg hsym hmono
  have hf_meas : Measurable (fun y : ℝ => K (y - x)) :=
    hK_meas.comp (measurable_id.sub measurable_const)
  have hA_meas : ∀ t : ℝ, MeasurableSet {y : ℝ | ENNReal.ofReal t < K (y - x)} := fun t =>
    hf_meas measurableSet_Ioi
  have hA_ord : ∀ t : ℝ, ({y : ℝ | ENNReal.ofReal t < K (y - x)}).OrdConnected := by
    intro t
    refine Set.OrdConnected.mk (fun y1 hy1 y2 hy2 z hz => ?_)
    obtain ⟨hz1, hz2⟩ := hz
    have hy1' : ENNReal.ofReal t < K (y1 - x) := hy1
    have hy2' : ENNReal.ofReal t < K (y2 - x) := hy2
    show ENNReal.ofReal t < K (z - x)
    have hzabs : |z - x| ≤ max |y1 - x| |y2 - x| := by
      rcases le_total x z with hxz | hzx
      · calc |z - x| = z - x := abs_of_nonneg (sub_nonneg.mpr hxz)
          _ ≤ y2 - x := sub_le_sub_right hz2 x
          _ = |y2 - x| := (abs_of_nonneg (sub_nonneg.mpr (hxz.trans hz2))).symm
          _ ≤ max |y1 - x| |y2 - x| := le_max_right _ _
      · calc |z - x| = x - z := by rw [abs_of_nonpos (sub_nonpos.mpr hzx)]; ring
          _ ≤ x - y1 := sub_le_sub_left hz1 x
          _ = |y1 - x| := by
                rw [abs_of_nonpos (sub_nonpos.mpr (hz1.trans hzx))]; ring
          _ ≤ max |y1 - x| |y2 - x| := le_max_left _ _
    have h2 : K (max |y1 - x| |y2 - x|) ≤ K (z - x) := by
      rw [even_kernel_eq_abs hsym (z - x)]
      exact hmono |z - x| (max |y1 - x| |y2 - x|) (abs_nonneg _) hzabs
    rcases le_total |y1 - x| |y2 - x| with hle | hle
    · have h3 : K (max |y1 - x| |y2 - x|) = K (y2 - x) := by
        rw [max_eq_right hle, even_kernel_eq_abs hsym (y2 - x)]
      rw [← h3] at hy2'
      exact lt_of_lt_of_le hy2' h2
    · have h3 : K (max |y1 - x| |y2 - x|) = K (y1 - x) := by
        rw [max_eq_left hle, even_kernel_eq_abs hsym (y1 - x)]
      rw [← h3] at hy1'
      exact lt_of_lt_of_le hy1' h2
  have hinner : ∀ t : ℝ, ∫⁻ y in {y : ℝ | ENNReal.ofReal t < K (y - x)}, g y
      ≤ hlMax g x * volume {y : ℝ | ENNReal.ofReal t < K (y - x)} := by
    intro t
    by_cases ht : ENNReal.ofReal t < K 0
    · exact lintegral_le_hlMax_mul_volume_of_ordConnected hg (hA_ord t) (hA_meas t)
        (by simpa using ht)
    · have hempty : {y : ℝ | ENNReal.ofReal t < K (y - x)} = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro y hy
        have hle : K (y - x) ≤ K 0 := by
          rw [even_kernel_eq_abs hsym (y - x)]
          exact hmono 0 |y - x| le_rfl (abs_nonneg _)
        exact ht (lt_of_lt_of_le hy hle)
      rw [hempty, measure_empty, mul_zero]
      simp
  have htrans : ∀ t : ℝ, volume {y : ℝ | ENNReal.ofReal t < K (y - x)}
      = volume {z : ℝ | ENNReal.ofReal t < K z} := by
    intro t
    have hset : {y : ℝ | ENNReal.ofReal t < K (y - x)}
        = (fun h : ℝ => -x + h) ⁻¹' {z : ℝ | ENNReal.ofReal t < K z} := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_preimage]
      rw [show -x + y = y - x by ring]
    rw [hset, measure_preimage_add volume (-x)]
  have hmeasure : ∫⁻ t in Set.Ioi (0:ℝ), volume {y : ℝ | ENNReal.ofReal t < K (y - x)}
      = ∫⁻ z, K z := by
    have hV : ∀ t : ℝ, volume {z : ℝ | ENNReal.ofReal t < K z}
        = ∫⁻ z in {z : ℝ | ENNReal.ofReal t < K z}, (1 : ℝ≥0∞) := by
      intro t
      rw [setLIntegral_const, one_mul]
    have hlc := lintegral_mul_eq_lintegral_setLIntegral_lt volume hK_meas
      (measurable_const : Measurable fun _ : ℝ => (1:ℝ≥0∞))
    rw [lintegral_congr htrans, lintegral_congr hV, ← hlc]
    simp
  have hvol_meas : Measurable (fun t : ℝ => volume {y : ℝ | ENNReal.ofReal t < K (y - x)}) := by
    have : Antitone (fun t : ℝ => volume {y : ℝ | ENNReal.ofReal t < K (y - x)}) := by
      intro s t hst
      apply measure_mono
      intro y hy
      exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hst) hy
    exact this.measurable
  calc MeasureTheory.lintegral MeasureTheory.volume (fun y : ℝ => g y * K (x - y))
      = ∫⁻ y, g y * K (y - x) := by
        apply lintegral_congr; intro y
        congr 1
        rw [show y - x = -(x - y) by ring, hsym]
    _ = ∫⁻ t in Set.Ioi (0:ℝ), ∫⁻ y in {y : ℝ | ENNReal.ofReal t < K (y - x)}, g y :=
        lintegral_mul_eq_lintegral_setLIntegral_lt volume hf_meas hg
    _ ≤ ∫⁻ t in Set.Ioi (0:ℝ),
          hlMax g x * volume {y : ℝ | ENNReal.ofReal t < K (y - x)} :=
        lintegral_mono hinner
    _ = hlMax g x * ∫⁻ t in Set.Ioi (0:ℝ), volume {y : ℝ | ENNReal.ofReal t < K (y - x)} :=
        lintegral_const_mul _ hvol_meas
    _ = hlMax g x * ∫⁻ z, K z := by rw [hmeasure]
    _ = MeasureTheory.lintegral MeasureTheory.volume K * hlMax g x := by rw [mul_comm]

end Commons.Analysis.HardyLittlewood
