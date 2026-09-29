import Mathlib
import Submission.Work.TMContract.Gluing.hasSum_intervalIntegral_of_taylor
import Submission.Work.TMContract.Gluing.coeff_eq_iteratedDeriv
import Submission.Work.TMContract.Gluing.taylor_slice_alt

namespace Work.TMContract.Gluing

open Set MeasureTheory Filter

open scoped Topology ENNReal NNReal

theorem analyticOnNhd_integral {a b : ℝ} {φ : ℝ → ℝ → ℝ}
    (hφ : AnalyticOnNhd ℝ (fun p : ℝ × ℝ => φ p.1 p.2) (Set.Ioo a b ×ˢ Set.univ)) :
    AnalyticOnNhd ℝ (fun E : ℝ => ∫ x in (0 : ℝ)..1, φ E x) (Set.Ioo a b) := by
  intro E₀ hE₀
  set Φ : ℝ × ℝ → ℝ := fun p => φ p.1 p.2 with hΦdef
  have han : ∀ x ∈ Set.Icc (0:ℝ) 1, AnalyticAt ℝ Φ (E₀, x) :=
    fun x _ => hφ (E₀, x) ⟨hE₀, mem_univ x⟩
  have hchart : ∀ x ∈ Set.Icc (0:ℝ) 1, ∃ p : ℝ × ℝ × (ℕ → ℝ → ℝ),
      0 < p.1 ∧ 0 < p.2.1 ∧
      (∀ m, ContinuousOn (p.2.2 m) (Set.Icc (x - p.1) (x + p.1))) ∧
      (∀ m y, y ∈ Set.Icc (x - p.1) (x + p.1) → |p.2.2 m y| ≤ p.2.1 * (1/p.1)^m) ∧
      (∀ h' y, |h'| < p.1 → |y - x| < p.1 →
        HasSum (fun m => p.2.2 m y * h'^m) (Φ (E₀ + h', y))) := by
    intro x hx
    obtain ⟨r, hr, C, hC, c, hc, hb, he⟩ := taylor_slice_alt (Φ := Φ) (han x hx)
    exact ⟨(r, C, c), hr, hC, hc, hb, he⟩
  let D : ℝ → ℝ × ℝ × (ℕ → ℝ → ℝ) :=
    fun x => if hx : x ∈ Set.Icc (0:ℝ) 1 then Classical.choose (hchart x hx)
      else (1, 1, fun _ _ => 0)
  let R : ℝ → ℝ := fun x => (D x).1
  let K : ℝ → ℝ := fun x => (D x).2.1
  let cc : ℝ → ℕ → ℝ → ℝ := fun x => (D x).2.2
  have hspec : ∀ x (hx : x ∈ Set.Icc (0:ℝ) 1), 0 < R x ∧ 0 < K x ∧
      (∀ m, ContinuousOn (cc x m) (Set.Icc (x - R x) (x + R x))) ∧
      (∀ m y, y ∈ Set.Icc (x - R x) (x + R x) → |cc x m y| ≤ K x * (1/R x)^m) ∧
      (∀ h' y, |h'| < R x → |y - x| < R x →
        HasSum (fun m => cc x m y * h'^m) (Φ (E₀ + h', y))) := by
    intro x hx
    have hD : D x = Classical.choose (hchart x hx) := by simp only [D, dif_pos hx]
    simp only [R, K, cc]
    rw [hD]
    exact Classical.choose_spec (hchart x hx)
  have hcov : Set.Icc (0:ℝ) 1 ⊆
      ⋃ x : ↥(Set.Icc (0:ℝ) 1), Set.Ioo ((x:ℝ) - R x) ((x:ℝ) + R x) := by
    intro y hy
    refine Set.mem_iUnion.mpr ⟨⟨y, hy⟩, ?_⟩
    exact ⟨sub_lt_self _ (hspec y hy).1, lt_add_of_pos_right _ (hspec y hy).1⟩
  obtain ⟨T, hT⟩ := isCompact_Icc.elim_finite_subcover
    (fun x : ↥(Set.Icc (0:ℝ) 1) => Set.Ioo ((x:ℝ) - R x) ((x:ℝ) + R x))
    (fun _ => isOpen_Ioo) hcov
  have hchartOf : ∀ y ∈ Set.Icc (0:ℝ) 1,
      ∃ i : ↥(Set.Icc (0:ℝ) 1), i ∈ T ∧ y ∈ Set.Ioo ((i:ℝ) - R i) ((i:ℝ) + R i) := by
    intro y hy
    have h := hT hy
    simpa only [Set.mem_iUnion, exists_prop] using h
  have hTne : T.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have h0 : (0:ℝ) ∈ ⋃ x ∈ T, Set.Ioo ((x:ℝ) - R x) ((x:ℝ) + R x) :=
      hT ⟨le_refl 0, zero_le_one⟩
    rw [h] at h0
    simp at h0
  let ρ : ℝ := T.inf' hTne (fun i : ↥(Set.Icc (0:ℝ) 1) => R i)
  let C₁ : ℝ := T.sup' hTne (fun i : ↥(Set.Icc (0:ℝ) 1) => K i)
  have hρpos : 0 < ρ := by
    rw [show ρ = T.inf' hTne (fun i : ↥(Set.Icc (0:ℝ) 1) => R i) from rfl,
      Finset.lt_inf'_iff]
    exact fun i hi => (hspec (i:ℝ) i.2).1
  have hCpos : 0 < C₁ := by
    obtain ⟨i, hiT⟩ := hTne
    exact lt_of_lt_of_le (hspec (i:ℝ) i.2).2.1
      (show K i ≤ C₁ from Finset.le_sup' (fun i : ↥(Set.Icc (0:ℝ) 1) => K i) hiT)
  have hmin : ∀ i ∈ T, ρ ≤ R i := fun i hi =>
    show ρ ≤ R i from Finset.inf'_le (fun i : ↥(Set.Icc (0:ℝ) 1) => R i) hi
  have hmax : ∀ i ∈ T, K i ≤ C₁ := fun i hi =>
    show K i ≤ C₁ from Finset.le_sup' (fun i : ↥(Set.Icc (0:ℝ) 1) => K i) hi
  let c : ℕ → ℝ → ℝ :=
    fun m y => iteratedDeriv m (fun h : ℝ => Φ (E₀ + h, y)) 0 / (m.factorial : ℝ)
  have hident : ∀ (i : ℝ) (hi : i ∈ Set.Icc (0:ℝ) 1) (m : ℕ) (y : ℝ),
      y ∈ Set.Ioo (i - R i) (i + R i) → c m y = cc i m y := by
    intro i hi m y hy
    have hlt : |y - i| < R i := abs_lt.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have H := coeff_eq_iteratedDeriv (Φ := Φ) (E₀ := E₀) (x₀ := i) (r := R i) (C := K i)
      (hspec i hi).1 (fun m z hz => (hspec i hi).2.2.2.1 m z hz)
      (fun h' z hh' hz => (hspec i hi).2.2.2.2 h' z hh' hz) m y hlt
    simp only [c]
    exact H.symm
  have hcont : ∀ m, ContinuousOn (c m) (Set.Icc (0:ℝ) 1) := by
    intro m y hy
    obtain ⟨i, hiT, hyi⟩ := hchartOf y hy
    have hcci : ContinuousAt (cc i m) y :=
      ((hspec (i:ℝ) i.2).2.2.1 m).continuousAt (Icc_mem_nhds hyi.1 hyi.2)
    have hev : c m =ᶠ[𝓝 y] cc i m := by
      filter_upwards [isOpen_Ioo.mem_nhds hyi] with z hz
      exact hident (i:ℝ) i.2 m z hz
    exact (hcci.congr hev.symm).continuousWithinAt
  have hbound : ∀ m y, y ∈ Set.Icc (0:ℝ) 1 → |c m y| ≤ C₁ * (1/ρ)^m := by
    intro m y hy
    obtain ⟨i, hiT, hyi⟩ := hchartOf y hy
    have hmem : y ∈ Set.Icc ((i:ℝ) - R i) ((i:ℝ) + R i) :=
      ⟨le_of_lt hyi.1, le_of_lt hyi.2⟩
    rw [hident (i:ℝ) i.2 m y hyi]
    refine ((hspec (i:ℝ) i.2).2.2.2.1 m y hmem).trans ?_
    have h1 : K i ≤ C₁ := hmax i hiT
    have h2 : (1/R i)^m ≤ (1/ρ)^m := by
      have hRi : 0 < R i := (hspec (i:ℝ) i.2).1
      have hle : ρ ≤ R i := hmin i hiT
      have : 1 / R i ≤ 1 / ρ := by
        exact one_div_le_one_div_of_le hρpos hle
      exact pow_le_pow_left₀ (div_nonneg zero_le_one (le_of_lt hRi)) this m
    exact mul_le_mul h1 h2
      (pow_nonneg (div_nonneg zero_le_one (le_of_lt ((hspec (i:ℝ) i.2).1))) m) (le_of_lt hCpos)
  have hexp : ∀ h' y, |h'| < ρ → y ∈ Set.Icc (0:ℝ) 1 →
      HasSum (fun m => c m y * h'^m) (Φ (E₀ + h', y)) := by
    intro h' y hh' hy
    obtain ⟨i, hiT, hyi⟩ := hchartOf y hy
    have hmem : |y - i| < R i := abs_lt.mpr ⟨by linarith [hyi.1], by linarith [hyi.2]⟩
    have hhR : |h'| < R i := lt_of_lt_of_le hh' (hmin i hiT)
    have H := (hspec (i:ℝ) i.2).2.2.2.2 h' y hhR hmem
    have heq : ∀ m, c m y * h'^m = cc i m y * h'^m :=
      fun m => by rw [hident (i:ℝ) i.2 m y hyi]
    have heqfun : (fun m => c m y * h' ^ m) = (fun m => cc i m y * h' ^ m) := funext heq
    rw [heqfun]
    exact H
  have hint : ∀ E, |E| < ρ → HasSum (fun m => (∫ y in (0:ℝ)..1, c m y) * E^m)
      (∫ y in (0:ℝ)..1, Φ (E₀ + E, y)) := by
    intro E hE
    have h := hasSum_intervalIntegral_of_taylor (φ := fun y => Φ (E₀ + E, y)) (c := c)
      hρpos hCpos zero_lt_one hcont hbound
      (fun y hy => hexp E y hE ⟨le_of_lt hy.1, le_of_lt hy.2⟩) hE
    simpa using h
  let p : FormalMultilinearSeries ℝ ℝ ℝ :=
    fun m => (∫ y in (0:ℝ)..1, c m y) • ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin m) ℝ
  have hpbound : ∀ m, ‖p m‖ * ((ρ/2 : ℝ))^m ≤ C₁ := by
    intro m
    have h0 : ‖p m‖ ≤ C₁ * (1/ρ)^m := by
      have hnorm : ‖p m‖ ≤ ‖∫ y in (0:ℝ)..1, c m y‖ := by
        simp only [p]
        calc ‖(∫ y in (0:ℝ)..1, c m y) • ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin m) ℝ‖
            ≤ ‖∫ y in (0:ℝ)..1, c m y‖ * ‖ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin m) ℝ‖ :=
              ContinuousMultilinearMap.opNorm_smul_le _ _
          _ = ‖∫ y in (0:ℝ)..1, c m y‖ * 1 := by
              rw [ContinuousMultilinearMap.norm_mkPiAlgebra]
          _ = ‖∫ y in (0:ℝ)..1, c m y‖ := mul_one _
      refine hnorm.trans ?_
      have : ‖∫ y in (0:ℝ)..1, c m y‖ ≤ (C₁ * (1/ρ)^m) * |1 - (0:ℝ)| :=
        intervalIntegral.norm_integral_le_of_norm_le_const
          (fun x hx => by
            have hx' : x ∈ Set.Icc (0:ℝ) 1 := by
              rw [Set.uIoc_of_le zero_le_one] at hx; exact ⟨le_of_lt hx.1, hx.2⟩
            rw [Real.norm_eq_abs]
            exact hbound m x hx')
      simpa using this
    calc ‖p m‖ * ((ρ/2 : ℝ))^m ≤ (C₁ * (1/ρ)^m) * ((ρ/2))^m := by gcongr
      _ = C₁ * (((1/ρ) * (ρ/2))^m) := by rw [mul_pow]; ring
      _ = C₁ * ((1/2 : ℝ))^m := by
          congr 2
          field_simp
      _ ≤ C₁ * 1 := by
          have h1 : ((1/2 : ℝ))^m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
          exact mul_le_mul_of_nonneg_left h1 (le_of_lt hCpos)
      _ = C₁ := mul_one C₁
  have hrle : ENNReal.ofReal (ρ/2) ≤ p.radius := by
    have h : ((Real.toNNReal (ρ/2) : ℝ≥0) : ℝ≥0∞) ≤ p.radius :=
      p.le_radius_of_bound C₁ (fun m => by
        rw [Real.coe_toNNReal _ (by positivity)]
        exact hpbound m)
    simpa only [ENNReal.ofReal] using h
  refine ⟨p, ENNReal.ofReal (ρ/2), ⟨hrle, ENNReal.ofReal_pos.mpr (by positivity), ?_⟩⟩
  intro y hy
  have hy' : |y| < ρ := by
    rw [Metric.mem_eball, edist_zero_right, Real.enorm_eq_ofReal_abs,
      ENNReal.ofReal_lt_ofReal_iff (by positivity)] at hy
    linarith
  have H := hint y hy'
  have hp : ∀ m, p m (fun _ : Fin m => y) = (∫ x in (0:ℝ)..1, c m x) * y^m := by
    intro m
    simp only [p, smul_apply, ContinuousMultilinearMap.mkPiAlgebra_apply,
      Finset.prod_const, Finset.card_fin, smul_eq_mul]
  have hfun : (fun n => p n (fun _ : Fin n => y)) =
      (fun m => (∫ x in (0:ℝ)..1, c m x) * y^m) := funext hp
  rw [hfun]
  exact H

end Work.TMContract.Gluing
