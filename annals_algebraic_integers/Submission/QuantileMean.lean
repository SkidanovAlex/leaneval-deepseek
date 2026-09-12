import Submission.Quantile
import Submission.PotentialContinuity
import Submission.SerreExample
import Submission.SupportConcentration
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Quantile means converge to the first moment of μ
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators Topology ENNReal
open Filter

namespace Submission.QuantileMean

open Submission.Quantile
open Submission.PotentialContinuity
open Submission.SerreExample
open Submission.MuAtomFree
open Submission.SupportConcentration

/-- Length of the interval `[aSerre,bSerre]`. -/
noncomputable def L : ℝ := bSerre - aSerre

lemma L_pos : 0 < L := by
  unfold L
  exact sub_pos.mpr a_lt_b

lemma L_nonneg : 0 ≤ L := le_of_lt L_pos

/-- μ-tail `μ([t,∞))` as a real. -/
noncomputable def realTail (t : ℝ) : ℝ := (muS (Set.Ici t)).toReal

/-- μ-tail as a function of the layer-cake level `u` (level `aSerre+u`). -/
noncomputable def contTail (u : ℝ) : ℝ := realTail (aSerre + u)

/-- Empirical tail count: number of `i ∈ [1..n]` with `t ≤ α_i`. -/
def empCount (n : ℕ) (t : ℝ) : ℕ :=
  ((Finset.Icc 1 n).filter fun i : ℕ => t ≤ alpha n i).card

/-- Empirical tail count (as a real, written as a sum of indicators). -/
def discTail (n : ℕ) (u : ℝ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n, (if u ≤ alpha n i - aSerre then (1 : ℝ) else 0)

/-- count of roots in `[u,v]` used by `exists_interval_no_telescope`. -/
def ntCount (n : ℕ) (u v : ℝ) : ℕ :=
  ((Finset.Icc 1 n).filter fun i : ℕ => u ≤ alpha n i ∧ alpha n i ≤ v).card


-- ---------------------------------------------------------------------
-- (A) a.e. support facts and the μ tail in terms of the cdf
-- ---------------------------------------------------------------------

/-- μ lives (a.e.) inside `[aSerre,bSerre]`. -/
lemma ae_mem_Icc : ∀ᵐ x ∂muS, x ∈ Set.Icc aSerre bSerre := by
  rw [MeasureTheory.ae_iff]
  have hset : {x : ℝ | ¬x ∈ Set.Icc aSerre bSerre} = (Set.Icc aSerre bSerre)ᶜ := by
    ext x
    simp
  rw [hset]
  exact muS_compl_Icc

lemma ae_shift_nonneg : 0 ≤ᵐ[muS] (fun x : ℝ => x - aSerre) := by
  filter_upwards [ae_mem_Icc] with x hx
  change 0 ≤ x - aSerre
  linarith [hx.1]

lemma ae_shift_le_L : (fun x : ℝ => x - aSerre) ≤ᵐ[muS] (fun _ : ℝ => L) := by
  filter_upwards [ae_mem_Icc] with x hx
  change x - aSerre ≤ bSerre - aSerre
  exact sub_le_sub_right hx.2 aSerre

lemma ae_norm_shift_le_L : ∀ᵐ x ∂muS, ‖x - aSerre‖ ≤ L := by
  filter_upwards [ae_mem_Icc] with x hx
  change ‖x - aSerre‖ ≤ bSerre - aSerre
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hx.1)]
  exact sub_le_sub_right hx.2 aSerre

/-- μ gives zero mass strictly above `bSerre`. -/
lemma muS_Ioi_b_zero : muS (Set.Ioi bSerre) = 0 := by
  apply le_antisymm
  · have hsub : Set.Ioi bSerre ⊆ (Set.Icc aSerre bSerre)ᶜ := by
      intro x hx hmem
      exact (not_le_of_gt hx) hmem.2
    calc
      muS (Set.Ioi bSerre) ≤ muS ((Set.Icc aSerre bSerre)ᶜ) := measure_mono hsub
      _ = 0 := muS_compl_Icc
  · exact zero_le

/-- `realTail t = cdf bSerre − cdf t` for `t ∈ [aSerre,bSerre]`. -/
lemma realTail_eq_cdf {t : ℝ} (ht : t ∈ Set.Icc aSerre bSerre) :
    realTail t = cdf bSerre - cdf t := by
  unfold realTail
  have hdec : Set.Icc t bSerre = Set.Ioc t bSerre ∪ ({t} : Set ℝ) := by
    ext x
    constructor
    · intro hx
      by_cases h : x = t
      · exact Or.inr h
      · exact Or.inl ⟨lt_of_le_of_ne hx.1 (by intro htx; exact h htx.symm), hx.2⟩
    · intro hx
      rcases hx with hx | hx
      · exact ⟨le_of_lt hx.1, hx.2⟩
      · rw [hx]
        exact ⟨le_rfl, ht.2⟩
  have hdecomp : Set.Ici t = Set.Icc t bSerre ∪ Set.Ioi bSerre := by
    ext x
    constructor
    · intro hx
      by_cases h : x ≤ bSerre
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr (lt_of_not_ge h)
    · intro hx
      rcases hx with hx | hx
      · exact hx.1
      · exact le_trans ht.2 (le_of_lt hx)
  have hdisj1 : Disjoint (Set.Ioc t bSerre) ({t} : Set ℝ) := by
    rw [Set.disjoint_left]
    intro x hx hxt
    rw [hxt] at hx
    exact (lt_irrefl t) hx.1
  have hdisj2 : Disjoint (Set.Icc t bSerre) (Set.Ioi bSerre) := by
    rw [Set.disjoint_left]
    intro x hx hxt
    exact (not_le_of_gt hxt) hx.2
  have hm : muS (Set.Ici t) = muS (Set.Ioc t bSerre) := by
    calc
      muS (Set.Ici t) = muS (Set.Icc t bSerre ∪ Set.Ioi bSerre) := by rw [hdecomp]
      _ = muS (Set.Icc t bSerre) + muS (Set.Ioi bSerre) :=
            measure_union hdisj2 (measurableSet_Ioi)
      _ = muS (Set.Icc t bSerre) := by simp [muS_Ioi_b_zero]
      _ = muS (Set.Ioc t bSerre ∪ ({t} : Set ℝ)) := by rw [hdec]
      _ = muS (Set.Ioc t bSerre) + muS ({t} : Set ℝ) :=
            measure_union hdisj1 (measurableSet_singleton t)
      _ = muS (Set.Ioc t bSerre) := by simp [serre_atom_free t]
  calc
    (muS (Set.Ici t)).toReal = (muS (Set.Ioc t bSerre)).toReal := by rw [hm]
    _ = cdf bSerre - cdf t := (cdf_sub_eq_Ioc ht.2).symm

lemma realTail_le_one (t : ℝ) : realTail t ≤ 1 := by
  unfold realTail
  exact muS_toReal_le_one (Set.Ici t)

lemma realTail_nonneg (t : ℝ) : 0 ≤ realTail t := by
  unfold realTail
  exact ENNReal.toReal_nonneg

/-- μ-tail as function of `u` is measurable (antitone). -/
lemma contTail_measurable : Measurable contTail := by
  unfold contTail realTail
  refine Measurable.ennreal_toReal ?_
  let F : ℝ → ℝ≥0∞ := fun u => muS (Set.Ici (aSerre + u))
  have hF : Antitone F := by
    intro u1 u2 hu
    apply measure_mono
    intro x hx
    change aSerre + u2 ≤ x at hx
    change aSerre + u1 ≤ x
    linarith
  exact Antitone.measurable hF

-- ---------------------------------------------------------------------
-- (B) the μ-moment as an integral of its tail (layer cake)
-- ---------------------------------------------------------------------

/-- `x ↦ x−aSerre` is μ-integrable (it is bounded on the support). -/
lemma integrable_shift : Integrable (fun x : ℝ => x - aSerre) muS := by
  refine Integrable.of_bound (C := L) ?_ ?_
  · fun_prop
  · exact ae_norm_shift_le_L

lemma layer_mu : (∫ x : ℝ, (x - aSerre) ∂muS) = ∫ u in Set.Ioc 0 L, contTail u ∂volume := by
  have h := Integrable.integral_eq_integral_Ioc_meas_le (f := fun x : ℝ => x - aSerre) (M := L)
      (f_intble := integrable_shift) (f_nn := ae_shift_nonneg) (f_bdd := ae_shift_le_L)
  calc
    (∫ x : ℝ, (x - aSerre) ∂muS) = ∫ t in Set.Ioc 0 L, muS.real {a : ℝ | t ≤ a - aSerre} := h
    _ = ∫ u in Set.Ioc 0 L, contTail u ∂volume := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro u
      change muS.real {a : ℝ | u ≤ a - aSerre} = (muS (Set.Ici (aSerre + u))).toReal
      rw [measureReal_def]
      have hset : {a : ℝ | u ≤ a - aSerre} = Set.Ici (aSerre + u) := by
        ext a
        simp
        constructor <;> intro h <;> linarith
      rw [hset]

/-- the first moment of μ equals `aSerre` plus the integral of its tail. -/
lemma mu_moment_eq : (∫ x : ℝ, x ∂muS) = aSerre + (∫ u in Set.Ioc 0 L, contTail u ∂volume) := by
  have hconst : Integrable (fun _ : ℝ => aSerre) muS := integrable_const (α := ℝ) (μ := muS) aSerre
  calc
    (∫ x : ℝ, x ∂muS) = (∫ x : ℝ, (x - aSerre) + aSerre ∂muS) := by
        apply integral_congr_ae
        apply Eventually.of_forall
        intro x
        ring
    _ = (∫ x : ℝ, (x - aSerre) ∂muS) + (∫ _ : ℝ, aSerre ∂muS) := by
        exact integral_add integrable_shift hconst
    _ = (∫ x : ℝ, (x - aSerre) ∂muS) + aSerre := by
        simp [integral_const]
    _ = aSerre + (∫ x : ℝ, (x - aSerre) ∂muS) := by ring
    _ = aSerre + (∫ u in Set.Ioc 0 L, contTail u ∂volume) := by rw [layer_mu]


-- ---------------------------------------------------------------------
-- (C) counting facts and the discrete layer-cake identity
-- ---------------------------------------------------------------------

lemma card_Icc_one_n (n : ℕ) : (Finset.Icc (1 : ℕ) n).card = n := by
  rw [Nat.card_Icc]
  omega

lemma empCount_eq_ntCount {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (_ht : aSerre ≤ t) :
    empCount n t = ntCount n t bSerre := by
  unfold empCount ntCount
  apply congrArg Finset.card
  ext i
  constructor
  · intro h
    rcases Finset.mem_filter.mp h with ⟨hi, hti⟩
    have hb : alpha n i ≤ bSerre := by
      have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
      have hin : i ≤ n := (Finset.mem_Icc.mp hi).2
      exact (alpha_mem_Icc hn hi1 hin).2
    exact Finset.mem_filter.mpr ⟨hi, ⟨hti, hb⟩⟩
  · intro h
    rcases Finset.mem_filter.mp h with ⟨hi, hti⟩
    exact Finset.mem_filter.mpr ⟨hi, hti.1⟩

lemma empCount_le_n (n : ℕ) (t : ℝ) : empCount n t ≤ n := by
  have hcard : empCount n t ≤ (Finset.Icc (1 : ℕ) n).card := by
    unfold empCount
    exact Finset.card_le_card (by intro i hi; exact (Finset.mem_filter.mp hi).1)
  rwa [card_Icc_one_n] at hcard

lemma discTail_eq_card (n : ℕ) (u : ℝ) : discTail n u = (empCount n (aSerre + u) : ℝ) := by
  unfold discTail empCount
  rw [← Finset.sum_filter]
  have hfilt : (Finset.Icc 1 n).filter (fun i : ℕ => u ≤ alpha n i - aSerre) =
      (Finset.Icc 1 n).filter (fun i : ℕ => aSerre + u ≤ alpha n i) := by
    apply Finset.ext
    intro i
    by_cases hi : i ∈ Finset.Icc 1 n
    · simp only [Finset.mem_filter, hi, true_and]
      constructor <;> intro h <;> linarith
    · simp [hi]
  rw [hfilt]
  simp

lemma discTail_nonneg (n : ℕ) (u : ℝ) : 0 ≤ discTail n u := by
  unfold discTail
  apply Finset.sum_nonneg
  intro i hi
  by_cases h : u ≤ alpha n i - aSerre <;> simp [h]

lemma discTail_le_n (n : ℕ) (u : ℝ) : discTail n u ≤ (n : ℝ) := by
  have h := discTail_eq_card n u
  rw [h]
  exact_mod_cast (empCount_le_n n (aSerre + u))

lemma ind_int {c : ℝ} (hc0 : 0 ≤ c) (hcL : c ≤ L) :
    (∫ u in Set.Ioc 0 L, (if u ≤ c then (1 : ℝ) else 0) ∂volume) = c := by
  have hfun : (fun u : ℝ => if u ≤ c then (1 : ℝ) else 0) =
      (fun u : ℝ => (Set.Iic c).indicator (fun _ : ℝ => (1 : ℝ)) u) := by
    funext u
    by_cases h : u ≤ c <;> simp [h]
  rw [hfun]
  rw [setIntegral_indicator measurableSet_Iic]
  rw [setIntegral_const]
  have hs : Set.Ioc 0 L ∩ Set.Iic c = Set.Ioc 0 c := by
    ext x
    simp only [Set.mem_Ioc, Set.mem_Iic, Set.mem_inter_iff]
    constructor
    · intro hx
      rcases hx with ⟨⟨hx0, hxL⟩, hxc⟩
      exact ⟨hx0, hxc⟩
    · intro hx
      rcases hx with ⟨hx0, hxc⟩
      exact ⟨⟨hx0, le_trans hxc hcL⟩, hxc⟩
  rw [hs]
  simp [hc0]

lemma per_term_int (n : ℕ) (i : ℕ) (hi : i ∈ Finset.Icc 1 n) (hn : 1 ≤ n) :
    (∫ u in Set.Ioc 0 L, (if u ≤ alpha n i - aSerre then (1 : ℝ) else 0) ∂volume) =
      alpha n i - aSerre := by
  have hai : alpha n i ∈ Set.Icc aSerre bSerre :=
    alpha_mem_Icc hn (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2
  exact ind_int (sub_nonneg.mpr hai.1) (by unfold L; exact sub_le_sub_right hai.2 aSerre)

lemma ind_integrable {c : ℝ} : IntegrableOn (fun u : ℝ => if u ≤ c then (1 : ℝ) else 0)
    (Set.Ioc 0 L) volume := by
  refine Integrable.of_bound (C := 1) ?_ ?_
  · have hm : Measurable (fun u : ℝ => if u ≤ c then (1 : ℝ) else 0) := by
      apply Measurable.ite measurableSet_Iic
      · exact measurable_const
      · exact measurable_const
    exact hm.aestronglyMeasurable
  · apply Eventually.of_forall
    intro u
    by_cases h : u ≤ c <;> simp [h]

/-- discrete layer cake: the sum of the shifted quantiles is the integral of the
empirical tail-count. -/
lemma disc_layer (n : ℕ) :
    (∑ i ∈ Finset.Icc 1 n, (alpha n i - aSerre)) =
      ∫ u in Set.Ioc 0 L, discTail n u ∂volume := by
  calc
    (∑ i ∈ Finset.Icc 1 n, (alpha n i - aSerre))
        = ∑ i ∈ Finset.Icc 1 n, (∫ u in Set.Ioc 0 L,
            (if u ≤ alpha n i - aSerre then (1 : ℝ) else 0) ∂volume) := by
            by_cases hn : 1 ≤ n
            · refine Finset.sum_congr rfl ?_
              intro i hi
              exact (per_term_int n i hi hn).symm
            · have hn0 : n = 0 := by omega
              subst n
              simp
    _ = ∫ u in Set.Ioc 0 L, discTail n u ∂volume := by
            rw [← integral_finsetSum (s := Finset.Icc 1 n) (μ := volume.restrict (Set.Ioc 0 L))
                (f := fun i u => if u ≤ alpha n i - aSerre then (1 : ℝ) else 0)]
            rfl
            · intro i hi
              exact ind_integrable

lemma disc_mean_eq (n : ℕ) :
    (∑ i ∈ Finset.Icc 1 n, (alpha n i - aSerre)) / (n : ℝ) =
      ∫ u in Set.Ioc 0 L, discTail n u / (n : ℝ) ∂volume := by
  calc
    (∑ i ∈ Finset.Icc 1 n, (alpha n i - aSerre)) / (n : ℝ)
        = (∫ u in Set.Ioc 0 L, discTail n u ∂volume) / (n : ℝ) := by rw [disc_layer]
    _ = ∫ u in Set.Ioc 0 L, discTail n u / (n : ℝ) ∂volume := by rw [integral_div]

/-- uniform pointwise comparison of the empirical tail and the μ tail. -/
lemma exists_tail_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ u : ℝ, u ∈ Set.Ioc 0 L →
      |discTail n u / (n : ℝ) - contTail u| ≤ C / (n : ℝ) := by
  rcases exists_interval_no_telescope with ⟨C, hCpos, hC⟩
  refine ⟨C, hCpos, ?_⟩
  intro n hn u hu
  have hn1 : 1 ≤ n := by omega
  have hule : u ≤ L := hu.2
  let t : ℝ := aSerre + u
  have hta : aSerre ≤ t := by dsimp [t]; linarith [hu.1]
  have htb : t ≤ bSerre := by dsimp [t]; dsimp [L] at hule; linarith
  have hticc : t ∈ Set.Icc aSerre bSerre := ⟨hta, htb⟩
  have hnt := hC n hn t bSerre hta htb le_rfl
  have hct : contTail u = realTail t := by dsimp [contTail, t]
  have heq : discTail n u / (n : ℝ) - contTail u =
      (ntCount n t bSerre : ℝ) / (n : ℝ) - (cdf bSerre - cdf t) := by
    calc
      discTail n u / (n : ℝ) - contTail u
          = (empCount n t : ℝ) / (n : ℝ) - contTail u := by
              rw [discTail_eq_card]
      _ = (ntCount n t bSerre : ℝ) / (n : ℝ) - realTail t := by
              rw [empCount_eq_ntCount hn1 hta, hct]
      _ = (ntCount n t bSerre : ℝ) / (n : ℝ) - (cdf bSerre - cdf t) := by
              rw [realTail_eq_cdf hticc]
  rw [heq]
  exact hnt


-- ---------------------------------------------------------------------
-- (D) integrability of the two tail functions and the main comparison
-- ---------------------------------------------------------------------

lemma discTail_measurable (n : ℕ) : Measurable (fun u : ℝ => discTail n u) := by
  unfold discTail
  apply Finset.measurable_sum
  intro i hi
  apply Measurable.ite measurableSet_Iic
  · exact measurable_const
  · exact measurable_const

lemma discTail_integrableOn (n : ℕ) :
    IntegrableOn (fun u : ℝ => discTail n u / (n : ℝ)) (Set.Ioc 0 L) volume := by
  refine Integrable.of_bound (C := 1) ?_ ?_
  · have hm : Measurable (fun u : ℝ => discTail n u / (n : ℝ)) := by
      have hdiv : (fun u : ℝ => discTail n u / (n : ℝ)) = fun u : ℝ => discTail n u * (n : ℝ)⁻¹ := by
        funext u
        field_simp
      rw [hdiv]
      exact (discTail_measurable n).mul measurable_const
    exact hm.aestronglyMeasurable
  · apply Eventually.of_forall
    intro u
    by_cases hn0 : n = 0
    · subst n
      simp [discTail]
    · have hn1 : 1 ≤ n := by omega
      have hnn : 0 < (n : ℝ) := by exact_mod_cast hn1
      have h1 : 0 ≤ discTail n u / (n : ℝ) := div_nonneg (discTail_nonneg n u) (le_of_lt hnn)
      have h2 : discTail n u / (n : ℝ) ≤ 1 := by
        rw [div_le_one hnn]
        exact discTail_le_n n u
      rw [Real.norm_eq_abs, abs_of_nonneg h1]
      exact h2

lemma contTail_integrableOn : IntegrableOn contTail (Set.Ioc 0 L) volume := by
  refine Integrable.of_bound (C := 1) ?_ ?_
  · exact contTail_measurable.aestronglyMeasurable
  · apply Eventually.of_forall
    intro u
    unfold contTail realTail
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact muS_toReal_le_one (Set.Ici (aSerre + u))

lemma volume_Ioc_L_real : (volume (Set.Ioc 0 L)).toReal = L := by
  rw [Real.volume_Ioc]
  simp [L_nonneg]

/-- exact identity for the difference between the empirical mean and the moment. -/
lemma mean_diff_eq (n : ℕ) (hn : 2 ≤ n) :
    (((∑ i ∈ Finset.Icc 1 n, (alpha n i : ℝ)) / (n : ℝ)) - (∫ x : ℝ, x ∂muS)) =
      ∫ u in Set.Ioc 0 L, (discTail n u / (n : ℝ) - contTail u) ∂volume := by
  let S := (∑ i ∈ Finset.Icc 1 n, (alpha n i : ℝ))
  have hnn : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (by omega : 0 < n))
  have hsumA : (∑ i ∈ Finset.Icc 1 n, aSerre) = (n : ℝ) * aSerre := by
    rw [Finset.sum_const]
    rw [card_Icc_one_n]
    simp
  have hdecomp : S = (∑ i ∈ Finset.Icc 1 n, (alpha n i - aSerre)) + (n : ℝ) * aSerre := by
    dsimp [S]
    calc
      (∑ i ∈ Finset.Icc 1 n, (alpha n i : ℝ))
          = ∑ i ∈ Finset.Icc 1 n, ((alpha n i - aSerre) + aSerre) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
      _ = (∑ i ∈ Finset.Icc 1 n, (alpha n i - aSerre)) + (∑ i ∈ Finset.Icc 1 n, aSerre) := by
              rw [Finset.sum_add_distrib]
      _ = (∑ i ∈ Finset.Icc 1 n, (alpha n i - aSerre)) + (n : ℝ) * aSerre := by rw [hsumA]
  have hsum : S / (n : ℝ) - aSerre =
      (∑ i ∈ Finset.Icc 1 n, (alpha n i - aSerre)) / (n : ℝ) := by
    rw [hdecomp]
    field_simp [hnn]
    ring
  have hSminusA : S / (n : ℝ) - aSerre =
      ∫ u in Set.Ioc 0 L, discTail n u / (n : ℝ) ∂volume := by
    rw [hsum, disc_mean_eq]
  calc
    S / (n : ℝ) - (∫ x : ℝ, x ∂muS)
        = (S / (n : ℝ) - aSerre) - ((∫ x : ℝ, x ∂muS) - aSerre) := by ring
    _ = (∫ u in Set.Ioc 0 L, discTail n u / (n : ℝ) ∂volume) -
        (∫ u in Set.Ioc 0 L, contTail u ∂volume) := by
          rw [hSminusA, mu_moment_eq]
          ring
    _ = ∫ u in Set.Ioc 0 L, (discTail n u / (n : ℝ) - contTail u) ∂volume := by
          rw [integral_sub]
          · exact discTail_integrableOn n
          · exact contTail_integrableOn


/-- The mean of the quantiles converges to the first moment of `μ`:
`(1/n)·Σ_{i=1}^n α_{n,i} → ∫ x dμ`. -/
theorem quantile_mean_converges :
    Tendsto (fun n : ℕ => ((∑ i ∈ Finset.Icc 1 n, (alpha n i : ℝ)) / (n : ℝ))) atTop
      (𝓝 (∫ x : ℝ, x ∂muS)) := by
  let E : ℝ := ∫ x : ℝ, x ∂muS
  let S : ℕ → ℝ := fun n : ℕ => (∑ i ∈ Finset.Icc 1 n, (alpha n i : ℝ)) / (n : ℝ)
  rcases exists_tail_bound with ⟨C, hCpos, hC⟩
  have hbd (n : ℕ) (hn : 2 ≤ n) : |S n - E| ≤ (L * C) / (n : ℝ) := by
    dsimp [S, E]
    have hmean := mean_diff_eq n hn
    have hpt : ∀ u ∈ Set.Ioc 0 L,
        ‖discTail n u / (n : ℝ) - contTail u‖ ≤ C / (n : ℝ) := by
      intro u hu
      simpa [Real.norm_eq_abs] using hC n hn u hu
    have hnbound := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Ioc 0 L)
        (f := fun u : ℝ => discTail n u / (n : ℝ) - contTail u) (C := C / (n : ℝ))
        (measure_Ioc_lt_top) hpt
    calc
      |((∑ i ∈ Finset.Icc 1 n, (alpha n i : ℝ)) / (n : ℝ)) - (∫ x : ℝ, x ∂muS)|
          = ‖∫ u in Set.Ioc 0 L, (discTail n u / (n : ℝ) - contTail u) ∂volume‖ := by
              rw [hmean]
              simp [Real.norm_eq_abs]
      _ ≤ (C / (n : ℝ)) * (volume (Set.Ioc 0 L)).toReal := by
              exact hnbound
      _ = (L * C) / (n : ℝ) := by
              rw [volume_Ioc_L_real]
              ring
  have hseq : Tendsto (fun n : ℕ => (L * C) / (n : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have hzero : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) :=
      tendsto_inv_atTop_zero.comp hcast
    simpa [div_eq_mul_inv] using (tendsto_const_nhds (x := L * C)).mul hzero
  have hdiff : Tendsto (fun n : ℕ => |S n - E|) atTop (𝓝 (0 : ℝ)) := by
    apply squeeze_zero' (g := fun n : ℕ => (L * C) / (n : ℝ))
    · exact Eventually.of_forall (fun n => abs_nonneg _)
    · filter_upwards [eventually_ge_atTop 2] with n hn
      exact hbd n hn
    · exact hseq
  have hS : Tendsto S atTop (𝓝 E) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa [Real.norm_eq_abs] using hdiff
  simpa [S, E] using hS



/-- Quantitative rate: the mean of the quantiles is within `C/n` of the first
moment of `μ` (for every `n ≥ 2` and a constant `C` independent of `n`). -/
theorem quantile_mean_rate :
    ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, 2 ≤ n →
        |((∑ i ∈ Finset.Icc 1 n, (alpha n i : ℝ)) / (n : ℝ)) - (∫ x : ℝ, x ∂muS)|
          ≤ C / (n : ℝ) := by
  rcases exists_tail_bound with ⟨C, hCpos, hC⟩
  refine ⟨L * C, mul_pos L_pos hCpos, ?_⟩
  intro n hn
  have hmean := mean_diff_eq n hn
  have hpt : ∀ u ∈ Set.Ioc 0 L, ‖discTail n u / (n : ℝ) - contTail u‖ ≤ C / (n : ℝ) := by
    intro u hu
    simpa [Real.norm_eq_abs] using hC n hn u hu
  have hnbound := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Ioc 0 L)
      (f := fun u : ℝ => discTail n u / (n : ℝ) - contTail u) (C := C / (n : ℝ))
      (measure_Ioc_lt_top) hpt
  calc
    |((∑ i ∈ Finset.Icc 1 n, (alpha n i : ℝ)) / (n : ℝ)) - (∫ x : ℝ, x ∂muS)|
        = ‖∫ u in Set.Ioc 0 L, (discTail n u / (n : ℝ) - contTail u) ∂volume‖ := by
            rw [hmean]
            simp [Real.norm_eq_abs]
    _ ≤ (C / (n : ℝ)) * (volume (Set.Ioc 0 L)).toReal := hnbound
    _ = (L * C) / (n : ℝ) := by
            rw [volume_Ioc_L_real]
            ring

end Submission.QuantileMean
