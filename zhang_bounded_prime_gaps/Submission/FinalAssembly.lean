import Submission.FinalCompetitor
import Submission.TensorThinFull
import Submission.SieveCertificate
import Submission.SieveWeightSplit
import Submission.SieveSetup
import Submission.BVFinal
import Submission.BoundedGaps

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

open scoped BigOperators Topology
open Filter Finset MeasureTheory

namespace Commons.NumberTheory.MaynardSieve

noncomputable section

/-! ## Two elementary integral bounds -/

/-- **A function vanishing past `a` and bounded by `C` on `(0,∞)`.** -/
theorem abs_setIntegral_Ioi_le {g : ℝ → ℝ} (hg : Continuous g) {a C : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hbd : ∀ x : ℝ, 0 < x → |g x| ≤ C) (hvan : ∀ x : ℝ, a < x → g x = 0) :
    |∫ x in Set.Ioi (0:ℝ), g x| ≤ C * a := by
  have hfun : (Set.Ioi (0:ℝ)).indicator g = (Set.Ioc (0:ℝ) a).indicator g := by
    funext x
    by_cases hx : x ∈ Set.Ioi (0:ℝ)
    · rw [Set.indicator_of_mem hx]
      by_cases h : x ≤ a
      · rw [Set.indicator_of_mem (f := g) (by exact ⟨hx, h⟩)]
      · rw [Set.indicator_of_notMem (f := g)
            (by intro hx'; exact absurd hx'.2 (not_le.mpr (not_le.mp h))),
          hvan x (not_le.mp h)]
    · rw [Set.indicator_of_notMem (f := g) hx, Set.indicator_of_notMem (f := g)]
      intro hx'
      exact hx hx'.1
  have hint : IntegrableOn g (Set.Ioc (0:ℝ) a) :=
    (hg.continuousOn.integrableOn_compact isCompact_Icc).mono_set
      (fun x hx => ⟨le_of_lt hx.1, hx.2⟩)
  have hInt : Integrable ((Set.Ioc (0:ℝ) a).indicator g) :=
    (integrable_indicator_iff measurableSet_Ioc).mpr hint
  have hInt2 : Integrable ((Set.Ioc (0:ℝ) a).indicator (fun _ : ℝ => C)) :=
    (integrable_indicator_iff measurableSet_Ioc).mpr
      (integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))
  rw [← MeasureTheory.integral_indicator measurableSet_Ioi, hfun]
  rw [show |∫ x, (Set.Ioc (0:ℝ) a).indicator g x|
      = ‖∫ x, (Set.Ioc (0:ℝ) a).indicator g x‖ from (Real.norm_eq_abs _).symm]
  calc ‖∫ x, (Set.Ioc (0:ℝ) a).indicator g x‖
      ≤ ∫ x, ‖(Set.Ioc (0:ℝ) a).indicator g x‖ := MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ x, (Set.Ioc (0:ℝ) a).indicator (fun _ : ℝ => C) x := by
        refine integral_mono_ae hInt.norm hInt2 (Filter.Eventually.of_forall fun x => ?_)
        by_cases hx : x ∈ Set.Ioc (0:ℝ) a
        · simp only [Set.indicator_of_mem hx]
          rw [Real.norm_eq_abs]
          exact hbd x hx.1
        · simp [Set.indicator_of_notMem hx]
    _ = C * a := by
        rw [MeasureTheory.integral_indicator_const _ measurableSet_Ioc, smul_eq_mul,
          MeasureTheory.Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
        ring

/-- **The `T`-partial marginal tensor sum as an inner integral.** -/
theorem integral_tenP_extendAt {J k : ℕ} (G : Fin J → Fin k → ℝ → ℝ)
    (hGi : ∀ j i, Integrable (G j i)) (c : Fin J → ℝ) (i₀ : Fin k) (T : Finset (Fin J))
    (t : {l : Fin k // l ≠ i₀} → ℝ) :
    (∫ x in Set.Ioi (0:ℝ), ∑ j ∈ T, c j * ∏ l, G j l (extendAt i₀ x t l))
      = tenP G c i₀ T t := by
  have hfac : ∀ (j : Fin J) (x : ℝ),
      (∏ l : Fin k, G j l (extendAt i₀ x t l))
        = G j i₀ x * ∏ l : {l : Fin k // l ≠ i₀}, G j (l : Fin k) (t l) := by
    intro j x
    rw [← Finset.mul_prod_erase Finset.univ (fun l => G j l (extendAt i₀ x t l))
      (Finset.mem_univ i₀)]
    congr 1
    · simp [extendAt]
    · rw [prod_erase_eq_prod_subtype]
      refine Finset.prod_congr rfl fun l _ => ?_
      have hl : extendAt i₀ x t l.1 = t l := by
        simp only [extendAt, dif_neg l.2]
      rw [hl]
  simp only [hfac]
  rw [tenP]
  rw [MeasureTheory.integral_finsetSum T (fun j _ => ?_)]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const]
    ring
  · have heq : (fun x : ℝ => c j * (G j i₀ x * ∏ l : {l : Fin k // l ≠ i₀}, G j (l : Fin k) (t l)))
        = fun x : ℝ =>
          (c j * ∏ l : {l : Fin k // l ≠ i₀}, G j (l : Fin k) (t l)) * G j i₀ x := by
      funext x; ring
    rw [heq]
    exact ((hGi j i₀).integrableOn).const_mul _



/-! ## The numerical budgets -/

/-- The `J₂`-slab volume bound. -/
theorem finVol_le :
    (finCC ^ 49 - finAA ^ 49) / (Nat.factorial 49 : ℝ)
      ≤ 43218 * finEta * ((6 : ℝ) / 25) ^ 48 / (Nat.factorial 49 : ℝ) := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hc : (0 : ℝ) ≤ finCC := finCC_nonneg
  have haa : finAA ≤ finCC := le_of_lt finAA_lt
  have haa0 : (0 : ℝ) ≤ finAA := finAA_nonneg
  have hgeom := geom_sum₂_mul finCC finAA 49
  rw [← hgeom]
  have hterm : ∀ i ∈ Finset.range 49, finCC ^ i * finAA ^ (49 - 1 - i) ≤ finCC ^ 48 := by
    intro i hi
    calc finCC ^ i * finAA ^ (49 - 1 - i) ≤ finCC ^ i * finCC ^ (49 - 1 - i) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ haa0 haa _) (pow_nonneg hc _)
      _ = finCC ^ 48 := by
          rw [← pow_add]; congr 1
          have hi' : i < 49 := Finset.mem_range.mp hi
          omega
  have hsum : (∑ i ∈ Finset.range 49, finCC ^ i * finAA ^ (49 - 1 - i)) ≤ 49 * finCC ^ 48 := by
    have h1 : (∑ i ∈ Finset.range 49, finCC ^ i * finAA ^ (49 - 1 - i))
        ≤ ∑ _i ∈ Finset.range 49, finCC ^ 48 := Finset.sum_le_sum hterm
    rwa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
  have hsum0 : (0 : ℝ) ≤ ∑ i ∈ Finset.range 49, finCC ^ i * finAA ^ (49 - 1 - i) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (pow_nonneg hc _) (pow_nonneg haa0 _)
  have hdiff : finCC - finAA = 882 * finEta := by rw [finAA]; ring
  calc (∑ i ∈ Finset.range 49, finCC ^ i * finAA ^ (49 - 1 - i)) * (finCC - finAA)
      ≤ (49 * finCC ^ 48) * (finCC - finAA) := mul_le_mul_of_nonneg_right hsum (by linarith)
    _ ≤ (49 * ((6 : ℝ) / 25) ^ 48) * (882 * finEta) := by
        rw [hdiff]
        have h1 : finCC ^ 48 ≤ ((6 : ℝ) / 25) ^ 48 := pow_le_pow_left₀ hc finCC_bound 48
        have h2 : (0 : ℝ) ≤ 882 * finEta := by rw [finEta]; norm_num
        nlinarith [h1]
    _ = 43218 * finEta * ((6 : ℝ) / 25) ^ 48 := by ring

/-- The `J₂` budget, numerically. -/
theorem finBudL :
    50 * ((finR + 12 * (50 : ℝ) * finEta) ^ 2
        * ((finCC ^ 49 - finAA ^ 49) / (Nat.factorial 49 : ℝ))) < (1 : ℝ) / 10 ^ 170 / 4 := by
  have hB : finR + 12 * (50 : ℝ) * finEta ≤ (27 : ℝ) / 100 := by
    rw [finR]
    have h2 : 12 * (50 : ℝ) * finEta ≤ (1 : ℝ) / 100 := by rw [finEta]; norm_num
    nlinarith [finLam_le_quarter]
  have hB0 : (0 : ℝ) ≤ finR + 12 * (50 : ℝ) * finEta := by
    rw [finR]
    have h1 : (0 : ℝ) ≤ (26 : ℝ) / 25 * finLam := mul_nonneg (by norm_num) finLam_pos.le
    have h2 : (0 : ℝ) ≤ 12 * (50 : ℝ) * finEta := by rw [finEta]; norm_num
    linarith
  have hfact : (6 * 10 ^ 62 : ℝ) ≤ (Nat.factorial 49 : ℝ) := by norm_num [Nat.factorial]
  have hvol : (finCC ^ 49 - finAA ^ 49) / (Nat.factorial 49 : ℝ) ≤ (1 : ℝ) / 10 ^ 177 := by
    have hA0 : (0 : ℝ) ≤ 43218 * finEta * ((6 : ℝ) / 25) ^ 48 := by
      have h := finEta_pos
      positivity
    have h1 : 43218 * finEta * ((6 : ℝ) / 25) ^ 48
        ≤ 43218 * ((1 : ℝ) / 10 ^ 90) * ((6 : ℝ) / 25) ^ 48 := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left finEta_le (by norm_num)
    calc (finCC ^ 49 - finAA ^ 49) / (Nat.factorial 49 : ℝ)
        ≤ 43218 * finEta * ((6 : ℝ) / 25) ^ 48 / (Nat.factorial 49 : ℝ) := finVol_le
      _ ≤ 43218 * finEta * ((6 : ℝ) / 25) ^ 48 / (6 * 10 ^ 62) :=
          div_le_div_of_nonneg_left hA0 (by norm_num) hfact
      _ ≤ 43218 * ((1 : ℝ) / 10 ^ 90) * ((6 : ℝ) / 25) ^ 48 / (6 * 10 ^ 62) :=
          div_le_div_of_nonneg_right h1 (by norm_num)
      _ ≤ (1 : ℝ) / 10 ^ 177 := by norm_num
  have hnn : (0 : ℝ) ≤ (finCC ^ 49 - finAA ^ 49) / (Nat.factorial 49 : ℝ) :=
    div_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ finAA_nonneg (le_of_lt finAA_lt) 49))
      (by positivity)
  have h2 : (finR + 12 * (50 : ℝ) * finEta) ^ 2
        * ((finCC ^ 49 - finAA ^ 49) / (Nat.factorial 49 : ℝ))
      ≤ ((27 : ℝ) / 100) ^ 2 * (1 / 10 ^ 177) :=
    mul_le_mul (pow_le_pow_left₀ hB0 hB 2) hvol hnn (by positivity)
  calc 50 * ((finR + 12 * (50 : ℝ) * finEta) ^ 2
        * ((finCC ^ 49 - finAA ^ 49) / (Nat.factorial 49 : ℝ)))
      ≤ 50 * (((27 : ℝ) / 100) ^ 2 * (1 / 10 ^ 177)) := mul_le_mul_of_nonneg_left h2 (by norm_num)
    _ < (1 : ℝ) / 10 ^ 170 / 4 := by norm_num

/-- **`DHL 50`.** -/
theorem DHL_fifty : Submission.BoundedGaps.DHL 50 := by
  intro H hHadm N0
  obtain ⟨γ, F, hγ, hFc, hFcs, hsupp, hsup, hΔlo, hΔhi, hIFpos⟩ := exists_final_competitor
  set Δ : ℝ := (∑ i : Fin 50, JFunc 50 i finCC F) - IFuncOrth 50 F with hΔdef
  have hΔpos : 0 < Δ := by rw [hΔdef]; linarith
  set δ : ℝ := Δ / 100 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  have hR0 : 0 ≤ finR := by rw [finR]; exact le_of_lt (mul_pos (by norm_num) finLam_pos)
  have hR1 : finR + 24 * (50 : ℝ) * finEta ≤ 1 := by
    rw [finR]
    have h := finLam_le_quarter
    have h2 : 24 * (50 : ℝ) * finEta ≤ (1 : ℝ) / 2 := by rw [finEta]; norm_num
    nlinarith
  obtain ⟨ψ, J, Gt, c, β, hψ0, hψ1, hψsm, hψzero, hGtsm, hGtcs, hβnn, hβind, hβsum, hthin,
      hGtvan, hfullM, hαnear, hJnear⟩ :=
    exists_tensorData_thin_full (k := 50) (F := F) (R := finR) (cc := finCC) hFc hFcs hR0 hsupp
      (by norm_num) finEta_pos hδpos hR1 hsup
  have hβsumN : ∀ j, ∑ i : Fin 50, β j i ≤ finR + 12 * (50 : ℝ) * finEta := by
    intro j; simpa using hβsum j
  have hβindN : ∀ j i, β j i ≤ finR + 12 * (50 : ℝ) * finEta := by
    intro j i; simpa using hβind j i
  have hGi : ∀ j i, Integrable (Gt j i) :=
    fun j i => ((hGtsm j i).continuous).integrable_of_hasCompactSupport (hGtcs j i)
  have hGv : ∀ j i, ∃ R : ℝ, ∀ x : ℝ, R ≤ x → Gt j i x = 0 :=
    fun j i => ⟨β j i + 1, fun x hx => hGtvan j i x (lt_of_lt_of_le (lt_add_one _) hx)⟩
  set Mr : Fin J → Fin 50 → ℝ := fun j i => max (12 * finEta) (β j i) with hMrdef
  set Sf : Fin 50 → Finset (Fin J) := fun i => splitBox Mr finCC i with hSfdef
  have hMrnn : ∀ j i, 0 ≤ Mr j i := fun j i =>
    le_max_of_le_left (by rw [finEta]; norm_num : (0:ℝ) ≤ 12 * finEta)
  have hMrsum : ∀ j, ∑ i, Mr j i ≤ finR + 24 * (50 : ℝ) * finEta := by
    intro j
    have h1 : ∀ i : Fin 50, Mr j i ≤ 12 * finEta + β j i := fun i =>
      max_le (le_add_of_nonneg_right (hβnn j i)) (le_add_of_nonneg_left (by rw [finEta]; norm_num))
    calc ∑ i : Fin 50, Mr j i ≤ ∑ i : Fin 50, (12 * finEta + β j i) :=
          Finset.sum_le_sum fun i _ => h1 i
      _ = 600 * finEta + ∑ i : Fin 50, β j i := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          ring
      _ ≤ 600 * finEta + (finR + 12 * (50 : ℝ) * finEta) := by linarith [hβsumN j]
      _ = finR + 24 * (50 : ℝ) * finEta := by ring
  have hMrsum_27 : ∀ j, ∑ i, Mr j i ≤ (27 : ℝ) / 100 := by
    intro j
    have h : finR + 24 * (50 : ℝ) * finEta ≤ (27 : ℝ) / 100 := by
      rw [finR]
      have h2 : 24 * (50 : ℝ) * finEta ≤ (1 : ℝ) / 100 := by rw [finEta]; norm_num
      nlinarith [finLam_le_quarter]
    linarith [hMrsum j]
  -- the `J₂`-pointwise bound
  have hBm : ∀ (i : Fin 50) (t : {l : Fin 50 // l ≠ i} → ℝ), (∀ l, 0 ≤ t l) →
      |tenP Gt c i (Finset.univ \ Sf i) t| ≤ finR + 12 * (50 : ℝ) * finEta := by
    intro i t ht
    have ha : (0 : ℝ) ≤ finR + 12 * (50 : ℝ) * finEta := by
      have h1 : (0 : ℝ) ≤ (26 : ℝ) / 25 * finLam := mul_nonneg (by norm_num) finLam_pos.le
      have h2 : (0 : ℝ) ≤ 12 * (50 : ℝ) * finEta := by rw [finEta]; norm_num
      rw [finR]; linarith
    have hcont : Continuous (fun x : ℝ =>
        ∑ j ∈ (Finset.univ \ Sf i), c j * ∏ l, Gt j l (extendAt i x t l)) := by
      refine continuous_finsetSum _ fun j _ => ?_
      refine Continuous.mul continuous_const ?_
      refine continuous_finsetProd _ fun l _ => ?_
      refine (hGtsm j l).continuous.comp ?_
      by_cases hl : l = i
      · simp only [extendAt, dif_pos hl]; exact continuous_id
      · simp only [extendAt, dif_neg hl]; exact continuous_const
    rw [← integral_tenP_extendAt Gt hGi c i (Finset.univ \ Sf i) t]
    have h := abs_setIntegral_Ioi_le hcont (C := 1) ha (by norm_num) ?_ ?_
    · simpa using h
    · intro x hx
      have h1 : |∑ j ∈ (Finset.univ \ Sf i), c j * ∏ l, Gt j l (extendAt i x t l)|
          ≤ ∑ j ∈ (Finset.univ \ Sf i), |c j| * ∏ l, |Gt j l (extendAt i x t l)| := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
        rw [abs_mul, Finset.abs_prod]
      have h2 : (∑ j ∈ (Finset.univ \ Sf i), |c j| * ∏ l, |Gt j l (extendAt i x t l)|)
          ≤ ∑ j : Fin J, |c j| * ∏ l, |Gt j l (extendAt i x t l)| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset)
          (fun j _ _ => mul_nonneg (abs_nonneg _) (Finset.prod_nonneg fun l _ => abs_nonneg _))
      exact le_trans h1 (le_trans h2 (hfullM _))
    · intro x hx
      refine Finset.sum_eq_zero fun j _ => ?_
      have hz : Gt j i x = 0 := hGtvan j i x (lt_of_le_of_lt (hβind j i) hx)
      have hprod : (∏ l : Fin 50, Gt j l (extendAt i x t l)) = 0 := by
        rw [← Finset.mul_prod_erase Finset.univ (fun l => Gt j l (extendAt i x t l))
          (Finset.mem_univ i)]
        rw [show extendAt i x t i = x from by simp [extendAt], hz, zero_mul]
      rw [hprod, mul_zero]
  -- the data of the criterion
  have hfcs : ∀ j i, HasCompactSupport (anti ψ (Gt j) i) := by
    intro j i
    refine HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-(12 * finEta)) (β j i))
      isCompact_Icc ?_
    intro u hu
    rw [Function.mem_support] at hu
    by_contra hcon
    rw [Set.mem_Icc, not_and_or] at hcon
    apply hu
    rcases hcon with h | h
    · have hz : ψ u = 0 := hψzero u (le_of_lt (not_le.mp h))
      simp [anti, hz]
    · have hz : (∫ s in Set.Ioi u, Gt j i s) = 0 :=
        MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun s hs =>
          hGtvan j i s (lt_of_lt_of_le (not_le.mp h) (le_of_lt hs))
      simp [anti, hz]
  have hfsm : ∀ j i, ContDiff ℝ (↑(⊤ : ℕ∞)) (anti ψ (Gt j) i) := by
    intro j i
    have h2 : anti ψ (Gt j) i = fun u : ℝ => ψ u * ∫ s in Set.Ioi u, Gt j i s := rfl
    rw [h2]
    exact hψsm.mul (Commons.Analysis.Calculus.contDiff_integral_Ioi (Gt j i) (hGtcs j i)
      (hGtsm j i))
  have hfbound : ∀ j i, β j i ≤ (27 : ℝ) / 100 := by
    intro j i
    have h1 := hβindN j i
    have h2 : finR + 12 * (50 : ℝ) * finEta ≤ (27 : ℝ) / 100 := by
      rw [finR]
      have h3 : 12 * (50 : ℝ) * finEta ≤ (1 : ℝ) / 100 := by rw [finEta]; norm_num
      nlinarith [finLam_le_quarter]
    linarith
  have hfb : ∀ j i t, 1 ≤ t → anti ψ (Gt j) i t = 0 := by
    intro j i t ht
    have hz : (∫ s in Set.Ioi t, Gt j i s) = 0 :=
      MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun s hs => by
        refine hGtvan j i s (lt_of_lt_of_le ?_ (le_of_lt hs))
        have hb := hfbound j i
        linarith
    simp [anti, hz]
  have hsuppf : ∀ j i t, Mr j i < |t| → anti ψ (Gt j) i t = 0 := by
    intro j i t ht
    have hMrβ : β j i ≤ Mr j i := le_max_right _ _
    have hMr12 : 12 * finEta ≤ Mr j i := le_max_left _ _
    rcases le_or_gt 0 t with ht0 | ht0
    · have hz : (∫ s in Set.Ioi t, Gt j i s) = 0 :=
        MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun s hs => by
          refine hGtvan j i s ?_
          rw [abs_of_nonneg ht0] at ht
          have hs' : t < s := hs
          linarith [hs', hMrβ]
      simp [anti, hz]
    · have hψ0' : ψ t = 0 := hψzero t (by
        rw [abs_of_neg ht0] at ht
        linarith)
      simp [anti, hψ0']
  -- the `J₁`-set data
  have hSfkey : ∀ i (j : Fin J), j ∈ Sf i → ∑ l : {l : Fin 50 // l ≠ i}, Mr j l < finCC := by
    intro i j hj
    have h := mem_splitBox.mp hj
    rwa [show (∑ l : {l : Fin 50 // l ≠ i}, Mr j l)
        = ∑ l ∈ (Finset.univ.erase i), Mr j l from
      (Finset.sum_subtype (Finset.univ.erase i) (fun x => by simp [Finset.mem_erase])
        (fun l => Mr j l)).symm]
  have hβlow : ∀ i (j : Fin J), j ∉ Sf i →
      finAA + 6 * finEta * ((50 : ℝ) - 1) ≤ ∑ l : {l : Fin 50 // l ≠ i}, β j l := by
    intro i j hj
    have hcc : finCC ≤ ∑ l ∈ Finset.univ.erase i, Mr j l := by
      by_contra hlt
      exact hj (mem_splitBox.mpr (lt_of_not_ge hlt))
    have hle : ∑ l ∈ Finset.univ.erase i, Mr j l
        ≤ ∑ l ∈ Finset.univ.erase i, (β j l + 12 * finEta) :=
      Finset.sum_le_sum fun l _ =>
        max_le (by have h := hβnn j l; linarith)
          (le_add_of_nonneg_right (mul_nonneg (by norm_num) (le_of_lt finEta_pos)))
    have hcard : ((Finset.univ : Finset (Fin 50)).erase i).card = 50 - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    have hsum2 : ∑ l ∈ Finset.univ.erase i, (β j l + 12 * finEta)
        = (∑ l ∈ Finset.univ.erase i, β j l) + ((50 - 1 : ℕ) : ℝ) * (12 * finEta) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, hcard, nsmul_eq_mul]
    have hgoal : finAA + 6 * finEta * ((50 : ℝ) - 1) ≤ ∑ l ∈ Finset.univ.erase i, β j l := by
      have haa : finAA = finCC - 882 * finEta := by rw [finAA]; ring
      have hcast : (((50 - 1 : ℕ)) : ℝ) = (50 : ℝ) - 1 := by norm_num
      nlinarith [hcc, hle, hsum2, hcast, haa, finEta_pos]
    rwa [show (∑ l : {l : Fin 50 // l ≠ i}, β j l)
        = ∑ l ∈ (Finset.univ.erase i), β j l from
      (Finset.sum_subtype (Finset.univ.erase i) (fun x => by simp [Finset.mem_erase])
        (fun l => β j l)).symm]
  -- the budgets
  have hcert : IFuncOrth 50 F + δ + Δ / 2 < ∑ i : Fin 50, JFunc 50 i finCC F := by
    have h : (∑ i : Fin 50, JFunc 50 i finCC F) = IFuncOrth 50 F + Δ := by
      rw [hΔdef]; ring
    rw [h, hδdef]; linarith [hΔpos]
  have hbudJ : (50 : ℝ) * (δ / 2) ≤ (Δ / 2) / 2 := by
    rw [hδdef]
    have h : (50 : ℝ) * (Δ / 100 / 2) = (Δ / 2) / 2 := by ring
    linarith [h]
  have hbudL : (50 : ℝ) * ((finR + 12 * (50 : ℝ) * finEta) ^ 2
      * ((finCC ^ 49 - finAA ^ 49) / (Nat.factorial 49 : ℝ))) < (Δ / 2) / 2 := by
    refine lt_of_lt_of_le finBudL ?_
    linarith [hΔlo]
  have hαcert : tpAlpha c (fun j i => anti ψ (Gt j) i) < IFuncOrth 50 F + δ := by
    have h := hαnear
    rw [abs_lt] at h
    linarith [h.1]
  have hαpos : 0 < tpAlpha c (fun j i => anti ψ (Gt j) i) := by
    have h : δ < IFuncOrth 50 F := by rw [hδdef]; linarith [hΔhi, hΔpos]
    have h2 := hαnear
    rw [abs_lt] at h2
    linarith [h2.1]
  have hBm0 : (0 : ℝ) ≤ finR + 12 * (50 : ℝ) * finEta := by
    have h1 : (0 : ℝ) ≤ (26 : ℝ) / 25 * finLam := mul_nonneg (by norm_num) finLam_pos.le
    have h2 : (0 : ℝ) ≤ 12 * (50 : ℝ) * finEta := by linarith [finEta_pos]
    rw [finR]; linarith
  have hkey := hkey_of_split_tensorData (k := 50) (J := J) (ψ := ψ) (F := F)
    hψ0 hψ1 Gt (fun j i => (hGtsm j i).continuous) hGtcs hGi hGv c Mr β Sf
    (η := finEta) (cc := finCC) (aa := finAA) (ef := δ) (eJ := δ / 2)
    (Bm := finR + 12 * (50 : ℝ) * finEta) (Mg := Δ / 2)
    (le_of_lt finEta_pos) (by norm_num) (by norm_num) hthin (fun j l => le_max_right _ _)
    hSfkey hβlow hBm finAA_nonneg (le_of_lt finAA_lt) hJnear hcert hbudJ hBm0 hbudL hαcert
  -- the criterion
  have hJ1 : 1 ≤ J := by
    rcases Nat.eq_zero_or_pos J with h | h
    · exfalso
      obtain rfl : J = 0 := h
      simp [tpAlpha] at hαpos
    · exact h
  have hsep : ∀ᶠ x : ℕ in atTop, ∀ i j : Fin 50, i ≠ j → H j - H i < slowCutoff x :=
    eventually_slowCutoff_gt H
  have hbex : ∀ x : ℕ, ∃ b : ℕ, ∀ i : Fin 50, (b + H i).Coprime (smoothModulus (slowCutoff x)) :=
    fun x => (exists_sieve_residue H hHadm (slowCutoff x)).imp (fun b hb => hb.2)
  choose b hb using hbex
  set Mtop : ℝ := finR + 24 * (50 : ℝ) * finEta with hMtopdef
  set D : ℕ → ℕ := fun x => ⌈max ((x : ℝ) ^ Mtop) ((x : ℝ) ^ finTheta)⌉₊ with hDdef
  have hM1 : ∀ j j', (∑ i : Fin 50, (Mr j i + Mr j' i)) < 1 := by
    intro j j'
    rw [Finset.sum_add_distrib]
    have h1 := hMrsum_27 j
    have h2 := hMrsum_27 j'
    linarith
  have hMtop : ∀ j i, Mr j i ≤ Mtop := by
    intro j i
    have h1 : Mr j i ≤ ∑ l : Fin 50, Mr j l :=
      Finset.single_le_sum (fun l _ => hMrnn j l) (Finset.mem_univ i)
    have h2 := hMrsum j
    rw [hMtopdef]; linarith
  have hM2 : ∀ j j' (i₀ : Fin 50), j' ∈ Sf i₀ →
      ∑ i ∈ Finset.univ.erase i₀, (Mr j i + Mr j' i) < finTheta := by
    refine splitBox_hM2 hMrnn hMrsum (fun j i => le_max_left _ _) ?_
    simp only [hMtopdef, finR, finCC, finLam, finTheta, finEta]
    norm_num
  have hD1 : ∀ᶠ x : ℕ in atTop, (x : ℝ) ^ Mtop ≤ (D x : ℝ) :=
    Filter.Eventually.of_forall fun x => le_trans (le_max_left _ _) (Nat.le_ceil _)
  have hD2 : ∀ᶠ x : ℕ in atTop, (x : ℝ) ^ finTheta ≤ (D x : ℝ) :=
    Filter.Eventually.of_forall fun x => le_trans (le_max_right _ _) (Nat.le_ceil _)
  refine translate_two_primes_of_tpWeight_split_family (n := 49) (J := J) (by norm_num) hJ1 c
    (fun j i => anti ψ (Gt j) i) H Sf
    ⟨Finset.univ.sup H, fun i => Finset.le_sup (Finset.mem_univ i)⟩ hHadm.1 hfcs hfsm Mr hMrnn
    hsuppf hfb finTheta_pos finTheta_lt_half hM1 Mtop hMtop hM2
    (fun x => smoothModulus (slowCutoff x)) (fun x => smoothModulus_ne_zero _) slowCutoff
    tendsto_slowCutoff (fun x p hp hpw => prime_dvd_smoothModulus hp hpw)
    tendsto_log_smoothModulus_slowCutoff_div_sqrtlog b hb
    (levelOfDistribution_of_BMVT finTheta_lt_half) ⟨2, smoothModulus_slowCutoff_le⟩ hsep D hD1 hD2
    hαpos hkey N0

end

end Commons.NumberTheory.MaynardSieve
