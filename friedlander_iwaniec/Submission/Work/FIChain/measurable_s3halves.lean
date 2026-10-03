import Mathlib
import Submission.Work.FIChain.s3RemPlus_defs
import Submission.Work.FIChain.s3SplitDefs
import Submission.Work.FIChain.cfRsum_le

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset MeasureTheory
open scoped BigOperators Interval

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. Parametrised interval integrals -/

/-- The set of pairs `(z,u)` with `u` in the oriented interval `Ι a (U z)` is measurable. -/
lemma measurableSet_uIoc_param {α : Type*} [MeasurableSpace α] (a : ℝ) {U : α → ℝ}
    (hU : Measurable U) :
    MeasurableSet {p : α × ℝ | p.2 ∈ Set.uIoc a (U p.1)} := by
  have hset : {p : α × ℝ | p.2 ∈ Set.uIoc a (U p.1)}
      = {p | min a (U p.1) < p.2} ∩ {p | p.2 ≤ max a (U p.1)} := by
    ext p
    simp [Set.uIoc, Set.Ioc, and_comm]
  rw [hset]
  exact (measurableSet_lt (measurable_const.min (hU.comp measurable_fst)) measurable_snd).inter
    (measurableSet_le measurable_snd (measurable_const.max (hU.comp measurable_fst)))

/-- **Measurability of a parametrised interval integral.**  If `G` is jointly measurable and `U` is
measurable, then `z ↦ ∫_a^{U z} G (z,u) du` is measurable. -/
lemma measurable_intervalIntegral_param {α : Type*} [MeasurableSpace α] (a : ℝ)
    {G : α × ℝ → ℝ} (hG : Measurable G) {U : α → ℝ} (hU : Measurable U) :
    Measurable (fun z : α => ∫ u in a..(U z), G (z, u)) := by
  have hS : MeasurableSet {p : α × ℝ | p.2 ∈ Set.uIoc a (U p.1)} :=
    measurableSet_uIoc_param a hU
  have hind : Measurable (fun p : α × ℝ =>
      if p.2 ∈ Set.uIoc a (U p.1) then G p else 0) :=
    Measurable.ite hS hG measurable_const
  have hinteg : Measurable (fun z : α => ∫ u : ℝ,
      if (z, u).2 ∈ Set.uIoc a (U z) then G (z, u) else 0) :=
    hind.stronglyMeasurable.integral_prod_right.measurable
  have hEq : ∀ z : α, (∫ u in a..(U z), G (z, u))
      = (if a ≤ U z then (1 : ℝ) else -1) *
        ∫ u, (if (z, u).2 ∈ Set.uIoc a (U z) then G (z, u) else 0) := by
    intro z
    by_cases h : a ≤ U z
    · rw [if_pos h, one_mul, intervalIntegral.integral_of_le h,
        ← integral_indicator measurableSet_Ioc]
      congr 1
      funext u
      simp only [Set.uIoc, min_eq_left h, max_eq_right h, Set.indicator_apply]
    · have hle : U z ≤ a := le_of_lt (not_le.mp h)
      rw [if_neg h, neg_one_mul, intervalIntegral.integral_of_ge hle]
      congr 1
      rw [← integral_indicator measurableSet_Ioc]
      congr 1
      funext u
      simp only [Set.uIoc, min_eq_right hle, max_eq_left hle, Set.indicator_apply]
  rw [show (fun z : α => ∫ u in a..(U z), G (z, u))
      = fun z : α => (if a ≤ U z then (1 : ℝ) else -1) *
        ∫ u, (if (z, u).2 ∈ Set.uIoc a (U z) then G (z, u) else 0) from funext hEq]
  exact (Measurable.ite (measurableSet_le measurable_const hU) measurable_const
    measurable_const).mul hinteg

/-! ## 2. Fixed-range forms of the two `(1.7)` integrands -/

/-- `Σ_{d ∈ Icc 1 ⌊u⌋₊}` equals the fixed-range sum with the indicator `d ≤ u`, provided
`u ≤ N` or `u < 1`. -/
lemma Icc_floor_eq_filter (N : ℕ) {u : ℝ} (hu : u ≤ (N : ℝ) ∨ u < 1) :
    Finset.Icc 1 ⌊u⌋₊ = (Finset.Icc 1 N).filter (fun d : ℕ => (d : ℝ) ≤ u) := by
  ext d
  simp only [Finset.mem_Icc, Finset.mem_filter]
  constructor
  · rintro ⟨hd1, hd2⟩
    have hu1 : (1 : ℝ) ≤ u := by
      by_contra hc
      push_neg at hc
      have h0 : ⌊u⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
      omega
    have huN : u ≤ (N : ℝ) := hu.resolve_right (not_lt.mpr hu1)
    exact ⟨⟨hd1, le_trans hd2 (le_trans (Nat.floor_mono huN) (by simp))⟩,
      le_trans (by exact_mod_cast hd2) (Nat.floor_le (by linarith))⟩
  · rintro ⟨⟨hd1, -⟩, hdle⟩
    exact ⟨hd1, Nat.le_floor hdle⟩

/-- The fixed-range form of a variable-range sum of `u`-dependent terms. -/
lemma sum_Icc_floor_eq_fixed (N : ℕ) (F : ℕ → ℝ) {u : ℝ} (hu : u ≤ (N : ℝ) ∨ u < 1) :
    (∑ d ∈ Finset.Icc 1 ⌊u⌋₊, F d)
      = ∑ d ∈ Finset.Icc 1 N, (if (d : ℝ) ≤ u then F d else 0) := by
  rw [Icc_floor_eq_filter N hu, Finset.sum_filter]

/-- The MAIN `(1.7)` integrand with the `d`-range made independent of `u`. -/
def s3MainIntF (x Cm N ℓ : ℕ) (sc z u : ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N,
    if (d : ℝ) ≤ u then
      (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil (ℓ * d) *
        (AcountAtilC ⌊min ((ℓ : ℝ) * (sc * z)) (x : ℝ)⌋₊
          - AcountAtilC ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊)
    else 0

/-- The REM `(1.7)` integrand with the `d`-range made independent of `u`. -/
def s3RemIntF (x Cm N ℓ : ℕ) (sc z u : ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N,
    if (d : ℝ) ≤ u then
      (ArithmeticFunction.moebius d : ℝ) *
        (cfR (ℓ * d) ⌊min ((ℓ : ℝ) * (sc * z)) (x : ℝ)⌋₊
          - cfR (ℓ * d) ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊)
    else 0

lemma measurable_AcountAtilC_floor {α : Type*} [MeasurableSpace α] {g : α → ℝ}
    (hg : Measurable g) : Measurable (fun a : α => AcountAtilC ⌊g a⌋₊) :=
  (measurable_of_countable AcountAtilC).comp hg.nat_floor

private lemma measurable_cfR_prod : Measurable (fun p : ℕ × ℕ => cfR p.1 p.2) := by
  apply measurable_of_countable

lemma measurable_cfR_const {α : Type*} [MeasurableSpace α] (ζ : ℕ) {m : α → ℕ}
    (hm : Measurable m) : Measurable (fun a : α => cfR ζ (m a)) := by
  refine (measurable_of_countable (fun n : ℕ => cfR ζ n)).comp ?_
  exact hm

lemma measurable_s3MainIntF (x Cm N ℓ : ℕ) (sc : ℝ) :
    Measurable (fun p : ℝ × ℝ => s3MainIntF x Cm N ℓ sc p.1 p.2) := by
  have hm1 : Measurable (fun p : ℝ × ℝ => AcountAtilC ⌊min ((ℓ : ℝ) * (sc * p.1)) (x : ℝ)⌋₊) :=
    measurable_AcountAtilC_floor
      ((measurable_const.mul (measurable_const.mul measurable_fst)).min measurable_const)
  have hm2 : Measurable (fun p : ℝ × ℝ =>
      AcountAtilC ⌊max ((ℓ : ℝ) * p.1) ((ℓ : ℝ) * (Cm : ℝ) * p.2)⌋₊) :=
    measurable_AcountAtilC_floor
      ((measurable_const.mul measurable_fst).max
        ((measurable_const.mul measurable_const).mul measurable_snd))
  refine Finset.measurable_sum _ (fun d _ => ?_)
  refine Measurable.ite (measurableSet_le measurable_const measurable_snd) ?_ measurable_const
  refine (measurable_const.mul measurable_const).mul ?_
  exact hm1.sub hm2

lemma measurable_s3RemIntF (x Cm N ℓ : ℕ) (sc : ℝ) :
    Measurable (fun p : ℝ × ℝ => s3RemIntF x Cm N ℓ sc p.1 p.2) := by
  refine Finset.measurable_sum _ (fun d _ => ?_)
  refine Measurable.ite (measurableSet_le measurable_const measurable_snd) ?_ measurable_const
  have h1 : Measurable (fun p : ℝ × ℝ =>
      ⌊min ((ℓ : ℝ) * (sc * p.1)) (x : ℝ)⌋₊) :=
    ((measurable_const.mul (measurable_const.mul measurable_fst)).min measurable_const).nat_floor
  have h2 : Measurable (fun p : ℝ × ℝ =>
      ⌊max ((ℓ : ℝ) * p.1) ((ℓ : ℝ) * (Cm : ℝ) * p.2)⌋₊) :=
    ((measurable_const.mul measurable_fst).max
      ((measurable_const.mul measurable_const).mul measurable_snd)).nat_floor
  exact measurable_const.mul
    ((measurable_cfR_const (ℓ * d) h1).sub (measurable_cfR_const (ℓ * d) h2))

/-! ## 3. The fixed-range forms of the two halves -/

lemma measurable_muFilterSum {α : Type*} [MeasurableSpace α] (ℓ : ℕ) {sy : α → ℝ}
    (hsy : Measurable sy) :
    Measurable (fun p : α => ∑ b ∈ ℓ.divisors.filter (fun b => sy p < ((b : ℕ) : ℝ)),
        (ArithmeticFunction.moebius b : ℝ)) := by
  have h : (fun p : α => ∑ b ∈ ℓ.divisors.filter (fun b => sy p < ((b : ℕ) : ℝ)),
        (ArithmeticFunction.moebius b : ℝ))
      = fun p : α => ∑ b ∈ ℓ.divisors,
          (if sy p < ((b : ℕ) : ℝ) then (ArithmeticFunction.moebius b : ℝ) else 0) := by
    funext p
    rw [Finset.sum_filter]
  rw [h]
  refine Finset.measurable_sum _ (fun b _ => ?_)
  exact Measurable.ite (measurableSet_lt hsy measurable_const)
    (measurable_const : Measurable (fun _ : α => (ArithmeticFunction.moebius b : ℝ)))
    (measurable_const : Measurable (fun _ : α => (0 : ℝ)))

/-- `s3MainPlus` with the `d`-range of its `u`-integrand made independent of `u` (see
`s3MainIntF`).  It agrees with `s3MainPlus` whenever the fixed range `N` dominates the `u`-cut
(`s3MainPlusF_eq`). -/
def s3MainPlusF (lam : ℕ → ℝ) (x Cm N : ℕ) (sc : ℝ) (z sy : ℝ) : ℝ :=
  ∑ ℓ ∈ Finset.Icc 1 x,
    (if ((ℓ : ℕ) : ℝ) * z ≤ (x : ℝ) then
      (∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
          (ArithmeticFunction.moebius b : ℝ)) * Submission.ASP.rhoOf lam ℓ *
        ∫ u in (1 : ℝ)..(min ((sc * z) / (Cm : ℝ)) ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)))),
          s3MainIntF x Cm N ℓ sc z u / u
     else 0)

/-- `s3RemPlus` with the `d`-range of its `u`-integrand made independent of `u`. -/
def s3RemPlusF (lam : ℕ → ℝ) (x Cm N : ℕ) (sc : ℝ) (z sy : ℝ) : ℝ :=
  ∑ ℓ ∈ Finset.Icc 1 x,
    (if ((ℓ : ℕ) : ℝ) * z ≤ (x : ℝ) then
      (∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
          (ArithmeticFunction.moebius b : ℝ)) * Submission.ASP.rhoOf lam ℓ *
        ∫ u in (1 : ℝ)..(min ((sc * z) / (Cm : ℝ)) ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)))),
          s3RemIntF x Cm N ℓ sc z u / u
     else 0)

/-- The `u`-cut of the MAIN/REM halves is at most `max 1 ⌈x/Cm⌉₊`. -/
lemma min_splitU_le_N (x Cm ℓ : ℕ) (sc z : ℝ) (hℓ : 1 ≤ ℓ) (hx : 0 ≤ (x : ℝ)) :
    min ((sc * z) / (Cm : ℝ)) ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)))
      ≤ ((max 1 ⌈(x : ℝ) / (Cm : ℝ)⌉₊ : ℕ) : ℝ) := by
  have hN1 : (1 : ℝ) ≤ ((max 1 ⌈(x : ℝ) / (Cm : ℝ)⌉₊ : ℕ) : ℝ) := by
    exact_mod_cast le_max_left 1 ⌈(x : ℝ) / (Cm : ℝ)⌉₊
  have hN2 : (x : ℝ) / (Cm : ℝ) ≤ ((max 1 ⌈(x : ℝ) / (Cm : ℝ)⌉₊ : ℕ) : ℝ) := by
    refine le_trans (Nat.le_ceil _) ?_
    exact_mod_cast le_max_right 1 ⌈(x : ℝ) / (Cm : ℝ)⌉₊
  rcases Nat.eq_zero_or_pos Cm with h | h
  · rw [h]
    simp
  · refine le_trans (min_le_right _ _) ?_
    have hCmpos : (0 : ℝ) < (Cm : ℝ) := by exact_mod_cast h
    have hℓ1R : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
    have hden : (Cm : ℝ) ≤ (ℓ : ℝ) * (Cm : ℝ) := by nlinarith
    exact le_trans (div_le_div_of_nonneg_left hx hCmpos hden) hN2

lemma s3MainPlusF_eq (lam : ℕ → ℝ) (x Cm N : ℕ) (sc z sy : ℝ) (hN1 : 1 ≤ N)
    (hN : ∀ ℓ ∈ Finset.Icc 1 x,
      min ((sc * z) / (Cm : ℝ)) ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ))) ≤ ((N : ℕ) : ℝ)) :
    s3MainPlusF lam x Cm N sc z sy
      = s3MainPlus lam x z sy (sc * z) Cm := by
  have hN1R : (1 : ℝ) ≤ ((N : ℕ) : ℝ) := by exact_mod_cast hN1
  rw [s3MainPlusF, s3MainPlus]
  refine Finset.sum_congr rfl (fun ℓ hℓ => ?_)
  by_cases hc : ((ℓ : ℕ) : ℝ) * z ≤ (x : ℝ)
  · rw [if_pos hc, if_pos hc]
    congr 1
    refine intervalIntegral.integral_congr (fun u hu => ?_)
    have huN : u ≤ ((N : ℕ) : ℝ) ∨ u < 1 := by
      refine Or.inl (le_trans ?_ (max_le hN1R (hN ℓ hℓ)))
      rcases Set.mem_uIcc.mp hu with ⟨-, hu2⟩ | ⟨-, hu2⟩
      · exact hu2.trans (le_max_right 1 _)
      · exact hu2.trans (le_max_left 1 _)
    congr 1
    rw [s3MainIntF, sum_Icc_floor_eq_fixed N _ huN]
  · rw [if_neg hc, if_neg hc]

lemma s3RemPlusF_eq (lam : ℕ → ℝ) (x Cm N : ℕ) (sc z sy : ℝ) (hN1 : 1 ≤ N)
    (hN : ∀ ℓ ∈ Finset.Icc 1 x,
      min ((sc * z) / (Cm : ℝ)) ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ))) ≤ ((N : ℕ) : ℝ)) :
    s3RemPlusF lam x Cm N sc z sy
      = s3RemPlus lam x z sy (sc * z) Cm := by
  have hN1R : (1 : ℝ) ≤ ((N : ℕ) : ℝ) := by exact_mod_cast hN1
  rw [s3RemPlusF, s3RemPlus]
  refine Finset.sum_congr rfl (fun ℓ hℓ => ?_)
  by_cases hc : ((ℓ : ℕ) : ℝ) * z ≤ (x : ℝ)
  · rw [if_pos hc, if_pos hc]
    congr 1
    refine intervalIntegral.integral_congr (fun u hu => ?_)
    have huN : u ≤ ((N : ℕ) : ℝ) ∨ u < 1 := by
      refine Or.inl (le_trans ?_ (max_le hN1R (hN ℓ hℓ)))
      rcases Set.mem_uIcc.mp hu with ⟨-, hu2⟩ | ⟨-, hu2⟩
      · exact hu2.trans (le_max_right 1 _)
      · exact hu2.trans (le_max_left 1 _)
    congr 1
    rw [s3RemIntF, sum_Icc_floor_eq_fixed N _ huN]
  · rw [if_neg hc, if_neg hc]

lemma measurable_s3MainPlusF (lam : ℕ → ℝ) (x Cm N : ℕ) (sc : ℝ) :
    Measurable (fun p : ℝ × ℝ => s3MainPlusF lam x Cm N sc p.1 (sc * p.2)) := by
  refine Finset.measurable_sum _ (fun ℓ hℓ => ?_)
  refine Measurable.ite
    (measurableSet_le (by fun_prop : Measurable (fun p : ℝ × ℝ => ((ℓ : ℕ) : ℝ) * p.1))
      measurable_const) ?_ (measurable_const : Measurable (fun _ : ℝ × ℝ => (0 : ℝ)))
  have hbw : Measurable (fun p : ℝ × ℝ =>
      ∑ b ∈ ℓ.divisors.filter (fun b => sc * p.2 < ((b : ℕ) : ℝ)),
        (ArithmeticFunction.moebius b : ℝ)) :=
    measurable_muFilterSum (α := ℝ × ℝ) ℓ (sy := fun p : ℝ × ℝ => sc * p.2) (by fun_prop)
  have hU : Measurable (fun p : ℝ × ℝ =>
      min ((sc * p.1) / (Cm : ℝ)) ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)))) := by fun_prop
  have hG : Measurable (fun q : (ℝ × ℝ) × ℝ => s3MainIntF x Cm N ℓ sc q.1.1 q.2 / q.2) := by
    have h1 : Measurable (fun q : (ℝ × ℝ) × ℝ => s3MainIntF x Cm N ℓ sc q.1.1 q.2) :=
      (measurable_s3MainIntF x Cm N ℓ sc).comp
        (by fun_prop : Measurable (fun q : (ℝ × ℝ) × ℝ => (q.1.1, q.2)))
    have h2 : Measurable (fun q : (ℝ × ℝ) × ℝ => q.2) := measurable_snd
    exact h1.div h2
  have hint : Measurable (fun p : ℝ × ℝ => ∫ u in (1 : ℝ)..(min ((sc * p.1) / (Cm : ℝ))
      ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)))), s3MainIntF x Cm N ℓ sc p.1 u / u) :=
    measurable_intervalIntegral_param 1 hG hU
  have hρ : Measurable (fun _ : ℝ × ℝ => Submission.ASP.rhoOf lam ℓ) := measurable_const
  exact (hbw.mul hρ).mul hint

lemma measurable_s3RemPlusF (lam : ℕ → ℝ) (x Cm N : ℕ) (sc : ℝ) :
    Measurable (fun p : ℝ × ℝ => s3RemPlusF lam x Cm N sc p.1 (sc * p.2)) := by
  refine Finset.measurable_sum _ (fun ℓ hℓ => ?_)
  refine Measurable.ite
    (measurableSet_le (by fun_prop : Measurable (fun p : ℝ × ℝ => ((ℓ : ℕ) : ℝ) * p.1))
      measurable_const) ?_ (measurable_const : Measurable (fun _ : ℝ × ℝ => (0 : ℝ)))
  have hbw : Measurable (fun p : ℝ × ℝ =>
      ∑ b ∈ ℓ.divisors.filter (fun b => sc * p.2 < ((b : ℕ) : ℝ)),
        (ArithmeticFunction.moebius b : ℝ)) :=
    measurable_muFilterSum (α := ℝ × ℝ) ℓ (sy := fun p : ℝ × ℝ => sc * p.2) (by fun_prop)
  have hU : Measurable (fun p : ℝ × ℝ =>
      min ((sc * p.1) / (Cm : ℝ)) ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)))) := by fun_prop
  have hG : Measurable (fun q : (ℝ × ℝ) × ℝ => s3RemIntF x Cm N ℓ sc q.1.1 q.2 / q.2) := by
    have h1 : Measurable (fun q : (ℝ × ℝ) × ℝ => s3RemIntF x Cm N ℓ sc q.1.1 q.2) :=
      (measurable_s3RemIntF x Cm N ℓ sc).comp
        (by fun_prop : Measurable (fun q : (ℝ × ℝ) × ℝ => (q.1.1, q.2)))
    have h2 : Measurable (fun q : (ℝ × ℝ) × ℝ => q.2) := measurable_snd
    exact h1.div h2
  have hint : Measurable (fun p : ℝ × ℝ => ∫ u in (1 : ℝ)..(min ((sc * p.1) / (Cm : ℝ))
      ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)))), s3RemIntF x Cm N ℓ sc p.1 u / u) :=
    measurable_intervalIntegral_param 1 hG hU
  have hρ : Measurable (fun _ : ℝ × ℝ => Submission.ASP.rhoOf lam ℓ) := measurable_const
  exact (hbw.mul hρ).mul hint

/-- **Joint Borel measurability of the two `(1.7)`-halves of `S3plusC`**: `z ↦ s3MainPlus lam x z
(sc·y) (sc·z) Cm` and its REM counterpart are Borel measurable in the pair `(z,y)`. -/
theorem measurable_s3halves_joint (x : ℕ) (B : ℝ) (lam : ℕ → ℝ) (Cm : ℕ) :
    Measurable (fun p : ℝ × ℝ => |s3MainPlus lam x p.1
        (sc x B * p.2) (sc x B * p.1) Cm|) ∧
    Measurable (fun p : ℝ × ℝ => |s3RemPlus lam x p.1
        (sc x B * p.2) (sc x B * p.1) Cm|) := by
  constructor
  · have h := measurable_s3MainPlusF lam x Cm (max 1 ⌈(x : ℝ) / (Cm : ℝ)⌉₊) (sc x B)
    rw [show (fun p : ℝ × ℝ => |s3MainPlus lam x p.1 (sc x B * p.2) (sc x B * p.1) Cm|)
        = fun p : ℝ × ℝ => |s3MainPlusF lam x Cm (max 1 ⌈(x : ℝ) / (Cm : ℝ)⌉₊) (sc x B)
            p.1 (sc x B * p.2)| from ?_]
    · exact h.abs
    · funext p
      rw [s3MainPlusF_eq lam x Cm _ (sc x B) p.1 (sc x B * p.2) (le_max_left 1 _)
        (fun ℓ hℓ => min_splitU_le_N x Cm ℓ (sc x B) p.1 (Finset.mem_Icc.mp hℓ).1
          (Nat.cast_nonneg x))]
  · have h := measurable_s3RemPlusF lam x Cm (max 1 ⌈(x : ℝ) / (Cm : ℝ)⌉₊) (sc x B)
    rw [show (fun p : ℝ × ℝ => |s3RemPlus lam x p.1 (sc x B * p.2) (sc x B * p.1) Cm|)
        = fun p : ℝ × ℝ => |s3RemPlusF lam x Cm (max 1 ⌈(x : ℝ) / (Cm : ℝ)⌉₊) (sc x B)
            p.1 (sc x B * p.2)| from ?_]
    · exact h.abs
    · funext p
      rw [s3RemPlusF_eq lam x Cm _ (sc x B) p.1 (sc x B * p.2) (le_max_left 1 _)
        (fun ℓ hℓ => min_splitU_le_N x Cm ℓ (sc x B) p.1 (Finset.mem_Icc.mp hℓ).1
          (Nat.cast_nonneg x))]

end

end Work.FIChain
