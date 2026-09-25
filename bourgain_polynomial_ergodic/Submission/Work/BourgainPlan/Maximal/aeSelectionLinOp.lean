import Mathlib
import Submission.Work.BourgainPlan.Maximal.ell2MaxAux
import Submission.Work.BourgainPlan.Maximal.dyCZ
import Submission.Work.BourgainPlan.Maximal.ae_le_dyMax

/-!
# The a.e. measurable selection for the linearised `ℓ²`-valued dyadic maximal operator

This file proves `Work.BourgainPlan.Maximal.aeSelectionLinOp`: for a finite family
`g : Fin n → ℝ → ℝ` whose `ℓ²`-norm `ell2Sigma g` is integrable there are a measurable selection
`m` of dyadic levels and measurable weights `e` (`0 ≤ e`, `∑ t, (e t x)² ≤ 1`) such that almost
everywhere `ell2F g ≤ 2 * linOp g m e`, and `ell2F g` is finite a.e.

The supporting lemmas are:

* `dyMax_eq_iSup_dyAvg`: the dyadic maximal function is the supremum of the cell averages over the
  dyadic levels (for a fixed point `x` the index `k` of a cell containing `x` is forced);
* `dyAvg_measurable`: `x ↦ dyAvg ψ m x` is measurable (it is a countable supremum of measurable
  functions, each constant on a cell);
* `exists_measurable_dyadic_selection`: the measurable selection of levels which is `1/2`-optimal
  off the set where the maximal function is infinite (via `Measurable.find`);
* `volume_eq_top_eq_zero_of_lintegral_lt_top`, `eq_zero_of_forall_le_ofReal_div_mul`,
  `dyMax_lt_top_ae`: the weak `(1,1)` bound for the (Hardy--Littlewood) maximal function gives
  `dyMax ψ < ∞` a.e. when `∫ ψ < ∞`;
* `ell2F_toReal_eq_sqrt`, `ell2F_eq_top_of_exists`, `ell2F_lt_top_of_forall`: the elementary
  identities converting `ell2F` into a real square root.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Work.BourgainPlan.Maximal

variable {n : ℕ}

/-! ### The dyadic maximal function as a supremum over levels -/

/-- The dyadic maximal function is the supremum of the averages over the cells of each level
containing `x`. -/
lemma dyMax_eq_iSup_dyAvg (ψ : ℝ → ℝ≥0∞) (x : ℝ) :
    dyMax ψ x = ⨆ m : ℤ, dyAvg ψ m x := by
  refine le_antisymm ?_ ?_
  · unfold dyMax
    refine iSup_le fun m => iSup_le fun k => iSup_le fun hm => ?_
    have hcell : dyCell m k = dyCell m (dyIdx m x) := dyCell_eq_of_meet hm (dyIdx_mem m x)
    rw [hcell]
    exact le_iSup_of_le m le_rfl
  · refine iSup_le fun m => ?_
    exact le_iSup_of_le m (le_iSup_of_le (dyIdx m x) (le_iSup_of_le (dyIdx_mem m x) le_rfl))

/-- The average of `ψ` over the dyadic cell of level `m` containing `x` is a measurable
function of `x`. -/
lemma dyAvg_measurable (ψ : ℝ → ℝ≥0∞) (m : ℤ) : Measurable (fun x => dyAvg ψ m x) := by
  have h : (fun x => dyAvg ψ m x) = fun x => ⨆ k : ℤ, (dyCell m k).indicator
      (fun _ => ENNReal.ofReal (((2 : ℝ) ^ m)⁻¹) * ∫⁻ y in dyCell m k, ψ y) x := by
    funext x
    refine le_antisymm ?_ ?_
    · refine le_iSup_of_le (dyIdx m x) ?_
      rw [Set.indicator_of_mem (dyIdx_mem m x)]
      exact le_rfl
    · refine iSup_le fun k => ?_
      by_cases hx : x ∈ dyCell m k
      · rw [Set.indicator_of_mem hx, ← dyIdx_eq_of_mem_cell hx]
        exact le_rfl
      · rw [Set.indicator_of_notMem hx]; exact bot_le
  rw [h]
  exact Measurable.iSup fun k => Measurable.indicator measurable_const (dyCell_measurable m k)

/-! ### A measurable selection of nearly optimal dyadic levels -/

/-- Off the set where the dyadic maximal function is infinite there is a measurable selection of
dyadic levels which is `1/2`-optimal. -/
lemma exists_measurable_dyadic_selection (ψ : ℝ → ℝ≥0∞) :
    ∃ (m : ℝ → ℤ), Measurable m ∧ ∀ x, dyMax ψ x < ⊤ → dyMax ψ x / 2 ≤ dyAvg ψ (m x) x := by
  classical
  obtain ⟨enc, henc⟩ : ∃ e : ℕ → ℤ, Function.Surjective e :=
    ⟨(Denumerable.eqv ℤ).symm, (Denumerable.eqv ℤ).symm.surjective⟩
  have hpmeas : ∀ j : ℕ, MeasurableSet {x : ℝ |
      (dyMax ψ x = ⊤) ∨ (dyMax ψ x / 2 ≤ dyAvg ψ (enc j) x)} := by
    intro j
    exact (show MeasurableSet {x : ℝ | dyMax ψ x = ⊤} from
      (dyMax_measurable ψ) (measurableSet_singleton (⊤ : ℝ≥0∞))).union
      (measurableSet_le ((dyMax_measurable ψ).div_const 2) (dyAvg_measurable ψ (enc j)))
  have hex : ∀ x : ℝ, ∃ j : ℕ,
      (dyMax ψ x = ⊤) ∨ (dyMax ψ x / 2 ≤ dyAvg ψ (enc j) x) := by
    intro x
    by_cases htop : dyMax ψ x = ⊤
    · exact ⟨0, Or.inl htop⟩
    · by_cases hz : dyMax ψ x = 0
      · refine ⟨0, Or.inr ?_⟩
        rw [hz]; simp
      · have hlt : dyMax ψ x / 2 < dyMax ψ x := by
          have hAtop : dyMax ψ x ≠ ⊤ := htop
          have h21 : (2 : ℝ≥0∞)⁻¹ < 1 := by norm_num
          have h := ENNReal.mul_lt_mul_left hz hAtop h21
          rw [ENNReal.div_eq_inv_mul]
          simpa using h
        have hsup : dyMax ψ x = ⨆ j : ℤ, dyAvg ψ j x := dyMax_eq_iSup_dyAvg ψ x
        obtain ⟨m0, hm0⟩ : ∃ m0 : ℤ, dyMax ψ x / 2 < dyAvg ψ m0 x := lt_iSup_iff.mp (hsup ▸ hlt)
        obtain ⟨j0, hj0⟩ : ∃ j0 : ℕ, enc j0 = m0 := henc m0
        exact ⟨j0, Or.inr (by rw [hj0]; exact hm0.le)⟩
  refine ⟨fun x => enc (Nat.find (hex x)), ?_, ?_⟩
  · exact Measurable.find (fun j => measurable_const) hpmeas hex
  · intro x hx
    exact (Nat.find_spec (hex x)).resolve_left (ne_of_lt hx)

/-! ### Finiteness a.e. of the dyadic maximal function -/

/-- If `ψ` has finite integral then `ψ` is finite a.e. -/
lemma volume_eq_top_eq_zero_of_lintegral_lt_top {ψ : ℝ → ℝ≥0∞} (hψ : Measurable ψ)
    (hint : ∫⁻ y, ψ y < ⊤) : volume {y : ℝ | ψ y = ⊤} = 0 := by
  set N : Set ℝ := {y | ψ y = ⊤} with hN
  have hNmeas : MeasurableSet N :=
    (show MeasurableSet {y : ℝ | ψ y = ⊤} from hψ (measurableSet_singleton (⊤ : ℝ≥0∞)))
  have hle1 : ⊤ * volume N ≤ ∫⁻ y in N, ψ y := by
    rw [← MeasureTheory.setLIntegral_const N (⊤ : ℝ≥0∞),
      ← MeasureTheory.lintegral_indicator hNmeas (f := fun _ => (⊤ : ℝ≥0∞)),
      ← MeasureTheory.lintegral_indicator hNmeas (f := ψ)]
    refine lintegral_mono fun y => ?_
    by_cases hy : y ∈ N
    · have hy' : ψ y = ⊤ := by rw [hN] at hy; exact hy
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
      exact le_of_eq hy'.symm
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
  have hlt : ⊤ * volume N < ⊤ :=
    lt_of_le_of_lt (hle1.trans (MeasureTheory.setLIntegral_le_lintegral N ψ)) hint
  by_contra hne
  rw [ENNReal.top_mul hne] at hlt
  exact absurd hlt (lt_irrefl ⊤)

/-- If `∀ lam > 0, a ≤ ofReal (C/lam) * I` with `I ≠ ⊤` and `C > 0` then `a = 0`. -/
lemma eq_zero_of_forall_le_ofReal_div_mul {a : ℝ≥0∞} {C : ℝ} (hC : 0 < C) {I : ℝ≥0∞}
    (hI : I ≠ ⊤) (h : ∀ lam : ℝ, 0 < lam → a ≤ ENNReal.ofReal (C / lam) * I) : a = 0 := by
  have htop : a < ⊤ := by
    have h1 := h 1 one_pos
    rw [div_one] at h1
    exact lt_of_le_of_lt h1 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr hI))
  have hreal : a.toReal = 0 := by
    by_contra hne
    have hpos : 0 < a.toReal := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hne)
    obtain ⟨lam, hlampos, hlt⟩ : ∃ lam : ℝ, 0 < lam ∧ C / lam * I.toReal < a.toReal := by
      obtain ⟨N, hN⟩ := exists_nat_gt (C * I.toReal / a.toReal)
      refine ⟨(N : ℝ) + 1, by positivity, ?_⟩
      have h2 : C * I.toReal / a.toReal < (N : ℝ) := hN
      rw [div_lt_iff₀ hpos] at h2
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) + 1)]
      linarith
    have h1 := h lam hlampos
    have h2 : a.toReal ≤ C / lam * I.toReal := by
      have h3 : (ENNReal.ofReal (C / lam) * I).toReal = C / lam * I.toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
      calc a.toReal ≤ (ENNReal.ofReal (C / lam) * I).toReal :=
            ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI) h1
        _ = C / lam * I.toReal := h3
    linarith
  rcases (ENNReal.toReal_eq_zero_iff a).mp hreal with h0 | htop'
  · exact h0
  · exact absurd htop' (ne_of_lt htop)

/-- For `ψ` with finite integral the dyadic maximal function is finite almost everywhere. -/
lemma dyMax_lt_top_ae {ψ : ℝ → ℝ≥0∞} (hψ : Measurable ψ) (hint : ∫⁻ y, ψ y < ⊤) :
    volume {x : ℝ | dyMax ψ x = ⊤} = 0 := by
  obtain ⟨C, hC, hb⟩ := dyMax_weak_type
  set ψ' : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal ((ψ y).toReal) with hψ'
  have hnull : volume {y : ℝ | ψ y = ⊤} = 0 := volume_eq_top_eq_zero_of_lintegral_lt_top hψ hint
  have hae : ψ =ᵐ[volume] ψ' := by
    filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hnull] with y hy
    rw [hψ']
    exact (ENNReal.ofReal_toReal hy).symm
  have hψ'_eq : (fun y => ‖(ψ y).toReal‖ₑ) = ψ' := by
    funext y
    rw [hψ', Real.enorm_eq_ofReal_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  have hcellint : ∀ (m k : ℤ), ∫⁻ y in dyCell m k, ψ y = ∫⁻ y in dyCell m k, ψ' y := by
    intro m k
    have h1 : ψ =ᵐ[volume.restrict (dyCell m k)] ψ' :=
      Filter.Eventually.filter_mono
        (MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_le_self (μ := volume)
          (s := dyCell m k))) hae
    exact MeasureTheory.lintegral_congr_ae h1
  have hdyMax : ∀ x, dyMax ψ x = dyMax ψ' x := by
    intro x
    unfold dyMax
    simp only [hcellint]
  refine eq_zero_of_forall_le_ofReal_div_mul hC (ne_of_lt hint) fun lam hlam => ?_
  have hsub : {x : ℝ | dyMax ψ x = ⊤} ⊆ {x : ℝ | ENNReal.ofReal lam < dyMax ψ x} := by
    intro x hx
    rw [Set.mem_ofPred_eq] at hx ⊢
    rw [hx]
    exact ENNReal.ofReal_lt_top
  have hb' : volume {x : ℝ | ENNReal.ofReal lam < dyMax ψ' x}
      ≤ ENNReal.ofReal (C / lam) * ∫⁻ y, ψ' y := by
    rw [← hψ'_eq]
    exact hb (fun y => (ψ y).toReal) lam hlam
  calc volume {x : ℝ | dyMax ψ x = ⊤}
      ≤ volume {x : ℝ | ENNReal.ofReal lam < dyMax ψ x} := MeasureTheory.measure_mono hsub
    _ = volume {x : ℝ | ENNReal.ofReal lam < dyMax ψ' x} := by simp only [hdyMax]
    _ ≤ ENNReal.ofReal (C / lam) * ∫⁻ y, ψ' y := hb'
    _ = ENNReal.ofReal (C / lam) * ∫⁻ y, ψ y := by rw [← MeasureTheory.lintegral_congr_ae hae]

/-! ### Elementary identities for `ell2F` -/

/-- The `ℓ²`-valued maximal function, written in terms of the real square root. -/
lemma ell2F_toReal_eq_sqrt (g : Fin n → ℝ → ℝ) (x : ℝ)
    (h : ∀ t, dyMax (fun y => ‖g t y‖ₑ) x < ⊤) :
    (ell2F g x).toReal
      = Real.sqrt (∑ t, ((dyMax (fun y => ‖g t y‖ₑ) x).toReal) ^ 2) := by
  have hgen : ∀ (A : Fin n → ℝ≥0∞), (∀ t, A t < ⊤) →
      (((∑ t, (A t) ^ (2 : ℝ)) : ℝ≥0∞) ^ ((1 : ℝ) / 2)).toReal
        = Real.sqrt (∑ t, ((A t).toReal) ^ 2) := by
    intro A hA
    have h1 : (((∑ t, (A t) ^ (2 : ℝ)) : ℝ≥0∞) ^ ((1 : ℝ) / 2)).toReal
        = ((∑ t, (A t) ^ (2 : ℝ)) : ℝ≥0∞).toReal ^ ((1 : ℝ) / 2) :=
      (ENNReal.toReal_rpow _ _).symm
    rw [h1, ENNReal.toReal_sum (fun t _ => ne_of_lt (ENNReal.rpow_lt_top_of_nonneg
      (by norm_num) (ne_of_lt (hA t)))), ← Real.sqrt_eq_rpow]
    congr 1
    exact Finset.sum_congr rfl fun t _ => by
      rw [← ENNReal.toReal_rpow, Real.rpow_two]
  rw [ell2F, ell2Max]
  exact hgen (fun t => dyMax (fun y => ‖g t y‖ₑ) x) h

/-- If one component of the dyadic maximal function is infinite then so is `ell2F`. -/
lemma ell2F_eq_top_of_exists (g : Fin n → ℝ → ℝ) (x : ℝ) (t : Fin n)
    (h : dyMax (fun y => ‖g t y‖ₑ) x = ⊤) : ell2F g x = ⊤ := by
  have hsum : (∑ s : Fin n, (dyMax (fun y => ‖g s y‖ₑ) x) ^ (2 : ℝ)) = ⊤ := by
    refine top_le_iff.mp ?_
    calc (⊤ : ℝ≥0∞) = (dyMax (fun y => ‖g t y‖ₑ) x) ^ (2 : ℝ) := by
          rw [h, ENNReal.top_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ ∑ s : Fin n, (dyMax (fun y => ‖g s y‖ₑ) x) ^ (2 : ℝ) :=
          Finset.single_le_sum
            (f := fun s : Fin n => (dyMax (fun y => ‖g s y‖ₑ) x) ^ (2 : ℝ))
            (fun s _ => bot_le) (Finset.mem_univ t)
  rw [ell2F, ell2Max, hsum, ENNReal.top_rpow_of_pos (by norm_num : (0 : ℝ) < (1 : ℝ) / 2)]

/-- If all components of the dyadic maximal function are finite then so is `ell2F`. -/
lemma ell2F_lt_top_of_forall (g : Fin n → ℝ → ℝ) (x : ℝ)
    (h : ∀ t, dyMax (fun y => ‖g t y‖ₑ) x < ⊤) : ell2F g x < ⊤ := by
  rw [ell2F, ell2Max]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
    (ne_of_lt (ENNReal.sum_lt_top.mpr fun t _ =>
      ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ne_of_lt (h t))))

/-- **A.e. measurable selection for the linearised `ℓ²`-valued dyadic maximal operator.**

If the `ℓ²`-norm `ell2Sigma g` of the family `g` is integrable, then there are a measurable
selection `m` of dyadic levels and measurable weights `e` with `0 ≤ e`, `∑ t, (e t x)² ≤ 1`,
such that almost everywhere the linearised operator `linOp g m e` dominates `ell2F g / 2`; and
`ell2F g` is finite almost everywhere. -/
theorem aeSelectionLinOp (n : ℕ) (g : Fin n → ℝ → ℝ) (hg : ∀ t, Measurable (g t))
    (hint : ∫⁻ x, Work.BourgainPlan.Maximal.ell2Sigma g x ≠ ⊤) :
    ∃ (m : Fin n → ℝ → ℤ) (e : Fin n → ℝ → ℝ),
      (∀ t, Measurable (m t)) ∧ (∀ t, Measurable (e t)) ∧ (∀ t x, 0 ≤ e t x) ∧
      (∀ x, ∑ t, (e t x) ^ 2 ≤ 1) ∧
      MeasureTheory.volume {x : ℝ | Work.BourgainPlan.Maximal.ell2F g x = ⊤} = 0 ∧
      ∀ᵐ x ∂(MeasureTheory.volume),
        Work.BourgainPlan.Maximal.ell2F g x ≤ 2 * Work.BourgainPlan.Maximal.linOp g m e x := by
  classical
  have hsigma : ∫⁻ x, ell2Sigma g x < ⊤ := lt_top_iff_ne_top.mpr hint
  -- the componentwise `L¹` bounds
  have hpsi_meas : ∀ t, Measurable (fun y => ‖g t y‖ₑ) := fun t => (hg t).enorm
  have hpsi_le : ∀ t x, ‖g t x‖ₑ ≤ ell2Sigma g x := by
    intro t x
    rw [ell2Sigma, ell2Sq]
    exact (eq_rpow_half_sq _).le.trans (ENNReal.rpow_le_rpow
      (Finset.single_le_sum (f := fun s => ‖g s x‖ₑ ^ (2 : ℝ)) (fun s _ => bot_le)
        (Finset.mem_univ t)) (by norm_num))
  have hpsi_int : ∀ t, ∫⁻ y, ‖g t y‖ₑ < ⊤ := fun t =>
    lt_of_le_of_lt (lintegral_mono fun y => hpsi_le t y) hsigma
  -- the measurable selections of levels, and the chosen weights
  choose m hm_meas hm_prop using
    fun t : Fin n => exists_measurable_dyadic_selection (fun y => ‖g t y‖ₑ)
  set e : Fin n → ℝ → ℝ :=
    fun t x => (dyMax (fun y => ‖g t y‖ₑ) x).toReal / (ell2F g x).toReal with hedef
  -- `ell2F g` is finite a.e.
  have hzero : ∀ t, volume {x : ℝ | dyMax (fun y => ‖g t y‖ₑ) x = ⊤} = 0 :=
    fun t => dyMax_lt_top_ae (hpsi_meas t) (hpsi_int t)
  have hF_top_le : volume {x : ℝ | ell2F g x = ⊤} ≤ 0 := by
    have hsub : {x : ℝ | ell2F g x = ⊤}
        ⊆ ⋃ t : Fin n, {x : ℝ | dyMax (fun y => ‖g t y‖ₑ) x = ⊤} := by
      intro x hx
      by_contra hcon
      rw [Set.mem_iUnion] at hcon
      simp only [not_exists, Set.mem_ofPred_eq] at hcon
      have hAll : ∀ t, dyMax (fun y => ‖g t y‖ₑ) x < ⊤ := fun t =>
        lt_top_iff_ne_top.mpr (by simpa [Set.mem_ofPred_eq] using hcon t)
      exact absurd hx (ne_of_lt (ell2F_lt_top_of_forall g x hAll))
    calc volume {x : ℝ | ell2F g x = ⊤}
        ≤ volume (⋃ t : Fin n, {x : ℝ | dyMax (fun y => ‖g t y‖ₑ) x = ⊤}) :=
          measure_mono hsub
      _ ≤ ∑ t : Fin n, volume {x : ℝ | dyMax (fun y => ‖g t y‖ₑ) x = ⊤} :=
          MeasureTheory.measure_iUnion_fintype_le _ _
      _ = 0 := by simp [hzero]
  have hF_top : volume {x : ℝ | ell2F g x = ⊤} = 0 := le_antisymm hF_top_le bot_le
  refine ⟨m, e, hm_meas, ?_, ?_, ?_, hF_top, ?_⟩
  · -- measurability of the weights
    intro t
    exact Measurable.div (ENNReal.measurable_toReal.comp (dyMax_measurable _))
      (ENNReal.measurable_toReal.comp (ell2F_measurable (n := n) (g := g)))
  · -- nonnegativity of the weights
    intro t x
    exact div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  · -- the `ℓ²` normalisation `∑ t, (e t x)² ≤ 1`
    intro x
    by_cases hs0 : (ell2F g x).toReal = 0
    · have hvan : ∀ t, e t x = 0 := fun t => by
        rw [hedef]
        exact by simp [hs0]
      simp [hvan]
    · set a : Fin n → ℝ := fun t => (dyMax (fun y => ‖g t y‖ₑ) x).toReal with hadef
      set s : ℝ := (ell2F g x).toReal with hsdef
      have hsne : s ≠ 0 := by rw [hsdef]; exact hs0
      have hAll : ∀ t, dyMax (fun y => ‖g t y‖ₑ) x < ⊤ := by
        intro t
        by_contra ht
        have htop : dyMax (fun y => ‖g t y‖ₑ) x = ⊤ := by
          rw [lt_top_iff_ne_top] at ht
          exact not_not.mp ht
        have hF : ell2F g x = ⊤ := ell2F_eq_top_of_exists g x t htop
        exact hs0 (by rw [hsdef, hF]; simp)
      have hs_sqrt : s = Real.sqrt (∑ t, (a t) ^ 2) := by
        rw [hsdef, hadef]
        exact ell2F_toReal_eq_sqrt g x hAll
      have hs2 : s ^ 2 = ∑ t, (a t) ^ 2 := by
        rw [hs_sqrt, Real.sq_sqrt (Finset.sum_nonneg fun t _ => sq_nonneg _)]
      have he : ∀ t, e t x = a t / s := fun t => rfl
      have hsum : ∑ t, (e t x) ^ 2 ≤ 1 := by
        have h1 : ∀ t, (e t x) ^ 2 = (a t) ^ 2 / s ^ 2 := by
          intro t
          rw [he t, div_pow]
        rw [Finset.sum_congr rfl (fun t _ => h1 t), ← Finset.sum_div, ← hs2,
          div_self (pow_ne_zero 2 hsne)]
      exact hsum
  · -- the a.e. domination
    have hbad : volume (⋃ t : Fin n, {x : ℝ | dyMax (fun y => ‖g t y‖ₑ) x = ⊤}) = 0 := by
      refine le_antisymm ?_ bot_le
      calc volume (⋃ t : Fin n, {x : ℝ | dyMax (fun y => ‖g t y‖ₑ) x = ⊤})
          ≤ ∑ t : Fin n, volume {x : ℝ | dyMax (fun y => ‖g t y‖ₑ) x = ⊤} :=
            MeasureTheory.measure_iUnion_fintype_le _ _
        _ = 0 := by simp [hzero]
    rw [MeasureTheory.measure_eq_zero_iff_ae_notMem] at hbad
    filter_upwards [hbad] with x hx
    have hA : ∀ t, dyMax (fun y => ‖g t y‖ₑ) x < ⊤ := by
      intro t
      have h1 : x ∉ ({x : ℝ | dyMax (fun y => ‖g t y‖ₑ) x = ⊤} : Set ℝ) :=
        fun h => hx (Set.mem_iUnion.mpr ⟨t, h⟩)
      exact lt_top_iff_ne_top.mpr (by simpa [Set.mem_ofPred_eq] using h1)
    have hmprop : ∀ t, dyMax (fun y => ‖g t y‖ₑ) x / 2 ≤ dyAvg (fun y => ‖g t y‖ₑ) (m t x) x :=
      fun t => hm_prop t x (hA t)
    have hFlt : ell2F g x < ⊤ := ell2F_lt_top_of_forall g x hA
    set dv : Fin n → ℝ≥0∞ := fun t => dyAvg (fun y => ‖g t y‖ₑ) (m t x) x with hdv
    set b : Fin n → ℝ := fun t => (dv t).toReal with hbdef
    set a : Fin n → ℝ := fun t => (dyMax (fun y => ‖g t y‖ₑ) x).toReal with hadef
    set s : ℝ := (ell2F g x).toReal with hsdef
    have hdv_le : ∀ t, dv t ≤ dyMax (fun y => ‖g t y‖ₑ) x := fun t => dyAvg_le_dyMax _ _ _
    have hdv_lt : ∀ t, dv t < ⊤ := fun t => lt_of_le_of_lt (hdv_le t) (hA t)
    have hb_ge : ∀ t, a t / 2 ≤ b t := by
      intro t
      have h1 : (dyMax (fun y => ‖g t y‖ₑ) x / 2).toReal ≤ (dv t).toReal :=
        ENNReal.toReal_mono (ne_of_lt (hdv_lt t)) (hmprop t)
      have h2 : (dyMax (fun y => ‖g t y‖ₑ) x / 2).toReal = a t / 2 := by
        rw [ENNReal.toReal_div, hadef, ENNReal.toReal_ofNat]
      rw [h2] at h1
      exact h1
    have he : ∀ t, e t x = a t / s := fun t => rfl
    have hb_eq : ∀ t, ENNReal.ofReal (b t) = dv t :=
      fun t => ENNReal.ofReal_toReal (ne_of_lt (hdv_lt t))
    have he0 : ∀ t, 0 ≤ e t x := fun t =>
      div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    have hlin : linOp g m e x = ENNReal.ofReal (∑ t, e t x * b t) := by
      unfold linOp
      rw [ENNReal.ofReal_sum_of_nonneg (fun t _ => mul_nonneg (he0 t) ENNReal.toReal_nonneg)]
      refine Finset.sum_congr rfl fun t _ => ?_
      calc ENNReal.ofReal (e t x) * dv t
          = ENNReal.ofReal (e t x) * ENNReal.ofReal (b t) := by rw [hb_eq t]
        _ = ENNReal.ofReal (e t x * b t) := by rw [← ENNReal.ofReal_mul (he0 t)]
    by_cases hs0 : s = 0
    · have hvan : ∀ t, e t x = 0 := fun t => by rw [he t, hs0, div_zero]
      have hZ0 : ∑ t, e t x * b t = 0 := by simp [hvan]
      have hFeq : ell2F g x = 0 := by
        rw [← ENNReal.ofReal_toReal (ne_of_lt hFlt), ← hsdef, hs0, ENNReal.ofReal_zero]
      rw [hFeq, hlin, hZ0, ENNReal.ofReal_zero, mul_zero]
    · have hsne : s ≠ 0 := hs0
      have hs_sqrt : s = Real.sqrt (∑ t, (a t) ^ 2) := by
        rw [hsdef, hadef]
        exact ell2F_toReal_eq_sqrt g x hA
      have hs2 : s ^ 2 = ∑ t, (a t) ^ 2 := by
        rw [hs_sqrt, Real.sq_sqrt (Finset.sum_nonneg fun t _ => sq_nonneg _)]
      have hterm : ∀ t, e t x * (a t / 2) = (a t) ^ 2 / (2 * s) := by
        intro t
        rw [he t]
        field_simp
      have hZeq : ∑ t, e t x * (a t / 2) = s / 2 := by
        rw [Finset.sum_congr rfl (fun t _ => hterm t), ← Finset.sum_div, ← hs2]
        field_simp
      have hZb : ∑ t, e t x * (a t / 2) ≤ ∑ t, e t x * b t :=
        Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hb_ge t) (by positivity)
      have hs_le : s ≤ 2 * ∑ t, e t x * b t := by linarith
      calc ell2F g x = ENNReal.ofReal s := (ENNReal.ofReal_toReal (ne_of_lt hFlt)).symm
        _ ≤ ENNReal.ofReal (2 * ∑ t, e t x * b t) := ENNReal.ofReal_le_ofReal hs_le
        _ = 2 * ENNReal.ofReal (∑ t, e t x * b t) := by
              rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
        _ = 2 * linOp g m e x := by rw [hlin]

end Work.BourgainPlan.Maximal
