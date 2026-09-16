import Submission.CertPolyBound
import Submission.CertSmoothRescale

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

open scoped BigOperators Topology
open Filter Finset MeasureTheory

/-!
# The final competitor of the Maynard sieve

This module fixes the numerical parameters of the final assembly

* `finTheta = 1/2 - 10⁻⁶` (the level of distribution),
* `finEta = 10⁻³²` (the tensor-localisation thickness),
* `finLam = (finTheta - 24·50·finEta)/2` (the rescaling of §5.1),
* `finCC = (24/25)·finLam` (the marginal radius of the `J`-functionals),
* `finR = (26/25)·finLam` (the support radius of the competitor),
* `finM0 = 10^54`, `finKappa = 1/finM0` (the supremum bound of `certPoly` and the normalisation),

and produces the continuous compactly supported competitor `F = finKappa • rescale finLam
(certSmooth γ)` whose support radius is `finR`, whose supremum is at most `1`, and whose
variational margin `Σᵢ JFunc 50 i finCC F - IFuncOrth 50 F` exceeds the explicit threshold
`10⁻¹⁷⁰`.  The latter is the quantity controlling the `J₂`-loss budget of
`hkey_of_split_tensorData`.
-/

namespace Commons.NumberTheory.MaynardSieve

noncomputable section

/-! ## Scalar multiples of the functionals -/

theorem IFuncOrth_smul (k : ℕ) (c : ℝ) (F : (Fin k → ℝ) → ℝ) :
    IFuncOrth k (fun t => c * F t) = c ^ 2 * IFuncOrth k F := by
  unfold IFuncOrth
  have h : ∀ t : Fin k → ℝ, (c * F t) ^ 2 = c ^ 2 * (F t) ^ 2 := fun t => by ring
  simp only [h, MeasureTheory.integral_const_mul]

theorem JFunc_smul (k : ℕ) (i : Fin k) (cc c : ℝ) (F : (Fin k → ℝ) → ℝ) :
    JFunc k i cc (fun t => c * F t) = c ^ 2 * JFunc k i cc F := by
  classical
  unfold JFunc
  have hin : ∀ t' : ({j : Fin k // j ≠ i} → ℝ),
      (∫ x : ℝ, c * F (extendAt i x t')) = c * ∫ x : ℝ, F (extendAt i x t') :=
    fun t' => MeasureTheory.integral_const_mul c _
  simp only [hin]
  have h : ∀ t' : ({j : Fin k // j ≠ i} → ℝ),
      (c * ∫ x : ℝ, F (extendAt i x t')) ^ 2 *
          (if t' ∈ marginalSet k i cc then 1 else 0)
        = c ^ 2 * ((∫ x : ℝ, F (extendAt i x t')) ^ 2 *
          (if t' ∈ marginalSet k i cc then 1 else 0)) := fun t' => by ring
  simp only [h, MeasureTheory.integral_const_mul]

/-! ## The numerical parameters -/

/-- The level of distribution `ϑ = 1/2 - 10⁻⁶`. -/
def finTheta : ℝ := 1 / 2 - 1 / 1000000

/-- The thickness parameter of the tensor localisation. -/
def finEta : ℝ := 1 / 10 ^ 90

/-- The rescaling of the competitor. -/
def finLam : ℝ := (finTheta - 48 * 50 * finEta) / 2

/-- The marginal radius of the `J`-functionals. -/
def finCC : ℝ := (24 / 25) * finLam

/-- The lower end of the `J₂`-slab. -/
def finAA : ℝ := finCC - 18 * finEta * 49

/-- The support radius of the competitor. -/
def finR : ℝ := (26 / 25) * finLam

/-- The explicit supremum bound for `certPoly` on the certificate simplex. -/
def finM0 : ℝ := 10 ^ 54

/-- The normalisation factor. -/
def finKappa : ℝ := 1 / finM0

/-- `IFuncOrth 50 certFun`, an explicit rational. -/
def certI0 : ℝ := (certK : ℝ) * (certK : ℝ) * ((certqI : ℝ) / (certDI : ℝ))

theorem certI0_eq : certI0 = IFuncOrth 50 certFun := IFuncOrth_certFun_eq.symm

theorem certI0_pos : 0 < certI0 := by
  rw [certI0_eq]; exact certFun_IFuncOrth_pos

theorem finEta_pos : 0 < finEta := by norm_num [finEta]

theorem finEta_le : finEta ≤ (1 : ℝ) / 10 ^ 90 := le_of_eq (by norm_num [finEta])

theorem finLam_pos : 0 < finLam := by
  rw [finLam, finTheta, finEta]; norm_num

theorem finLam_lo : (249995 : ℝ) / 1000000 ≤ finLam := by
  rw [finLam, finTheta, finEta]; norm_num

theorem finLam_le_quarter : finLam ≤ 1 / 4 := by
  rw [finLam, finTheta, finEta]; norm_num

theorem finLam_e0 : (1 : ℝ) / 5000 ≤ finLam * (4001 / 1000) - 1 := by
  rw [finLam, finTheta, finEta]
  norm_num

theorem finCC_bound : finCC ≤ 6 / 25 := by
  rw [finCC]
  nlinarith [finLam_le_quarter]

theorem finCC_pos : 0 < finCC := by
  rw [finCC]; exact mul_pos (by norm_num) finLam_pos

theorem finCC_nonneg : 0 ≤ finCC := le_of_lt finCC_pos

theorem finAA_lt : finAA < finCC := by
  rw [finAA]
  nlinarith [finEta_pos]

theorem finAA_nonneg : 0 ≤ finAA := by
  rw [finAA, finCC]
  have h := finLam_lo
  have h2 := finEta_le
  nlinarith

theorem finCC_div_lam : finCC / finLam = (24 : ℝ) / 25 := by
  rw [finCC, mul_div_assoc, div_self (ne_of_gt finLam_pos), mul_one]

theorem finKappa_eq : finKappa = (1 : ℝ) / 10 ^ 54 := by
  rw [finKappa, finM0]

theorem finKappa_pos : 0 < finKappa := by
  rw [finKappa_eq]; norm_num

theorem finKappa_sq : finKappa ^ 2 = (1 : ℝ) / 10 ^ 108 := by
  rw [finKappa_eq]; norm_num

theorem finKappa_mul : finKappa * finM0 = 1 := by
  rw [finKappa, finM0]; field_simp

theorem finR_le_one : finR ≤ 1 := by
  rw [finR]
  nlinarith [finLam_le_quarter]

theorem finTheta_pos : 0 < finTheta := by rw [finTheta]; norm_num

theorem finTheta_lt_half : finTheta < 1 / 2 := by rw [finTheta]; norm_num

/-- `2/ϑ < 4001/1000` for `ϑ = 1/2 - 10⁻⁶`. -/
theorem two_div_finTheta_lt : 2 / finTheta < (4001 : ℝ) / 1000 := by
  rw [div_lt_iff₀ finTheta_pos, finTheta]
  norm_num

/-! ## The sup-bound of the smoothed certificate -/

theorem abs_certSmooth_le {γ : ℝ} (hγ : 0 < γ) (t : Fin 50 → ℝ) :
    |certSmooth γ t| ≤ (10 : ℝ) ^ 54 := by
  by_cases ht : t ∈ simplexC 50 ((26 : ℝ) / 25)
  · rw [certSmooth, abs_mul]
    have h1 : |smoothCut 50 ((26 : ℝ) / 25) γ t| ≤ 1 := by
      rw [abs_of_nonneg (smoothCut_nonneg hγ t)]
      exact smoothCut_le_one hγ t
    calc |certPoly t| * |smoothCut 50 ((26 : ℝ) / 25) γ t|
        ≤ |certPoly t| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ ≤ (10 : ℝ) ^ 54 := by simpa using abs_certPoly_le ht
  · rw [certSmooth_support hγ ht]
    norm_num

/-- The certificate's quotient is below `5` (an explicit integer inequality). -/
theorem cert_ratio_lt_five :
    (∑ i : Fin 50, JFunc 50 i ((24 : ℝ) / 25) certFun) / IFuncOrth 50 certFun < 5 := by
  rw [sum_JFunc_certFun_value_eq, IFuncOrth_certFun_eq]
  have hK2 : (0 : ℝ) < (certK : ℝ) * (certK : ℝ) := mul_pos certK_pos certK_pos
  have hDIne : (certDI : ℝ) ≠ 0 := ne_of_gt certDI_pos
  have hDJne : (certDJ : ℝ) ≠ 0 := ne_of_gt certDJ_pos
  have hineq : ((10 : ℤ) * certqJ * certDI : ℤ) < certDJ * certqI := by decide
  have hineq' : ((10 : ℝ) * (certqJ : ℝ) * (certDI : ℝ)) < (certDJ : ℝ) * (certqI : ℝ) := by
    exact_mod_cast hineq
  have h : (50 : ℝ) * ((certqJ : ℝ) / (certDJ : ℝ))
      < 5 * ((certqI : ℝ) / (certDI : ℝ)) := by
    have h1 : (50 : ℝ) * ((certqJ : ℝ) / (certDJ : ℝ))
        = (50 * (certqJ : ℝ) * (certDI : ℝ)) / ((certDI : ℝ) * (certDJ : ℝ)) := by field_simp
    have h2 : (5 : ℝ) * ((certqI : ℝ) / (certDI : ℝ))
        = (5 * (certqI : ℝ) * (certDJ : ℝ)) / ((certDI : ℝ) * (certDJ : ℝ)) := by field_simp
    rw [← mul_div_assoc, ← mul_div_assoc, div_lt_div_iff₀ certDJ_pos certDI_pos]
    linarith [hineq']
  rw [div_lt_iff₀ (mul_pos hK2 (div_pos certqI_pos certDI_pos))]
  calc (50 : ℝ) * (certK : ℝ) * (certK : ℝ) * ((certqJ : ℝ) / (certDJ : ℝ))
      = ((certK : ℝ) * (certK : ℝ)) * ((50 : ℝ) * ((certqJ : ℝ) / (certDJ : ℝ))) := by ring
    _ < ((certK : ℝ) * (certK : ℝ)) * (5 * ((certqI : ℝ) / (certDI : ℝ))) :=
        mul_lt_mul_of_pos_left h hK2
    _ = (5 : ℝ) * ((certK : ℝ) * (certK : ℝ) * ((certqI : ℝ) / (certDI : ℝ))) := by ring

/-- The parametrised certificate quotient tends to the certificate's. -/
theorem certSmooth_ratio_tendsto :
    Tendsto (fun n : ℕ =>
      (∑ i : Fin 50, JFunc 50 i ((24 : ℝ) / 25) (certSmooth ((1 : ℝ) / (n + 1))))
        / IFuncOrth 50 (certSmooth ((1 : ℝ) / (n + 1)))) atTop
      (𝓝 ((∑ i : Fin 50, JFunc 50 i ((24 : ℝ) / 25) certFun) / IFuncOrth 50 certFun)) := by
  have hnum : Tendsto (fun n : ℕ =>
      ∑ i : Fin 50, JFunc 50 i ((24 : ℝ) / 25) (certSmooth ((1 : ℝ) / (n + 1)))) atTop
      (𝓝 (∑ i : Fin 50, JFunc 50 i ((24 : ℝ) / 25) certFun)) := by
    refine tendsto_finsetSum _ (fun i _ => ?_)
    exact tendsto_JFunc_certSmooth i ((24 : ℝ) / 25)
  exact hnum.div tendsto_IFuncOrth_certSmooth (ne_of_gt certFun_IFuncOrth_pos)

/-- The explicit lower bound for `IFuncOrth 50 certFun / 2`. -/
theorem certI0_lower : (1 : ℝ) / 10 ^ 25 ≤ certI0 / 2 := by
  have hDI : (0 : ℝ) < (certDI : ℝ) := by exact_mod_cast certDI_pos
  have hrew : (certK : ℝ) * (certK : ℝ) * ((certqI : ℝ) / (certDI : ℝ))
      = ((certK : ℝ) * (certK : ℝ) * (certqI : ℝ)) / (certDI : ℝ) := by ring
  have hkey : (1 : ℝ) / 10 ^ 25 * 2 * (certDI : ℝ)
      ≤ (certK : ℝ) * (certK : ℝ) * (certqI : ℝ) := by
    rw [certDI, certK, certqI]
    norm_num
  rw [certI0, le_div_iff₀ (by norm_num : (0 : ℝ) < 2), hrew, le_div_iff₀ hDI]
  exact hkey

/-- **The competitor.** -/
theorem exists_final_competitor :
    ∃ (γ : ℝ) (F : (Fin 50 → ℝ) → ℝ),
      0 < γ ∧ Continuous F ∧ HasCompactSupport F ∧
      (∀ t, F t ≠ 0 → (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ finR) ∧
      (∀ t, |F t| ≤ 1) ∧
      ((1 : ℝ) / 10 ^ 170 < ∑ i : Fin 50, JFunc 50 i finCC F - IFuncOrth 50 F) ∧
      (∑ i : Fin 50, JFunc 50 i finCC F - IFuncOrth 50 F < IFuncOrth 50 F) ∧
      0 < IFuncOrth 50 F := by
  classical
  obtain ⟨n, hn1, hn2, hn3⟩ :
      ∃ n : ℕ,
        (4001 : ℝ) / 1000 <
            (∑ i : Fin 50, JFunc 50 i ((24 : ℝ) / 25) (certSmooth ((1 : ℝ) / (n + 1))))
              / IFuncOrth 50 (certSmooth ((1 : ℝ) / (n + 1))) ∧
        certI0 / 2 < IFuncOrth 50 (certSmooth ((1 : ℝ) / (n + 1))) ∧
        (∑ i : Fin 50, JFunc 50 i ((24 : ℝ) / 25) (certSmooth ((1 : ℝ) / (n + 1))))
              / IFuncOrth 50 (certSmooth ((1 : ℝ) / (n + 1))) < 5 := by
    have h1 : ∀ᶠ n : ℕ in atTop, (4001 : ℝ) / 1000 <
        (∑ i : Fin 50, JFunc 50 i ((24 : ℝ) / 25) (certSmooth ((1 : ℝ) / (n + 1))))
          / IFuncOrth 50 (certSmooth ((1 : ℝ) / (n + 1))) :=
      certSmooth_ratio_tendsto.eventually (Ioi_mem_nhds cert_ratio_gt_sharp)
    have h2 : ∀ᶠ n : ℕ in atTop,
        certI0 / 2 < IFuncOrth 50 (certSmooth ((1 : ℝ) / (n + 1))) :=
      tendsto_IFuncOrth_certSmooth.eventually
        (Ioi_mem_nhds (by rw [← certI0_eq]; linarith [certI0_pos]))
    have h3 : ∀ᶠ n : ℕ in atTop,
        (∑ i : Fin 50, JFunc 50 i ((24 : ℝ) / 25) (certSmooth ((1 : ℝ) / (n + 1))))
              / IFuncOrth 50 (certSmooth ((1 : ℝ) / (n + 1))) < 5 :=
      certSmooth_ratio_tendsto.eventually (Iio_mem_nhds cert_ratio_lt_five)
    exact (h1.and (h2.and h3)).exists
  set γ : ℝ := (1 : ℝ) / (n + 1) with hγdef
  have hγ : 0 < γ := by rw [hγdef]; positivity
  have hIpos : 0 < IFuncOrth 50 (certSmooth γ) := lt_trans (by linarith [certI0_pos]) hn2
  have hsupp0 : ∀ s : Fin 50 → ℝ, s ∉ simplexC 50 ((26 : ℝ) / 25) → certSmooth γ s = 0 :=
    fun s hs => certSmooth_support hγ hs
  have hGcont : Continuous (rescale finLam (certSmooth γ)) := by
    refine (continuous_certSmooth hγ).comp ?_
    refine continuous_pi (fun j => ?_)
    exact ((continuous_apply j : Continuous fun t : Fin 50 → ℝ => t j)).div_const finLam
  have hGzero : ∀ s : Fin 50 → ℝ,
      s ∉ simplexSet 50 ((26 : ℝ) / 25 * finLam) → rescale finLam (certSmooth γ) s = 0 :=
    fun s hs => rescale_eq_zero_of_notMem finLam ((26 : ℝ) / 25) finLam_pos hsupp0
      (by simpa [mul_comm] using hs)
  have hGmem : ∀ s : Fin 50 → ℝ, rescale finLam (certSmooth γ) s ≠ 0 →
      (∀ i, 0 ≤ s i) ∧ ∑ i, s i ≤ finR := by
    intro s hs
    have hmem : s ∈ simplexSet 50 (finLam * ((26 : ℝ) / 25)) := by
      by_contra hcon
      exact hs (rescale_eq_zero_of_notMem finLam ((26 : ℝ) / 25) finLam_pos hsupp0 hcon)
    exact ⟨hmem.1, by rw [finR]; linarith [hmem.2]⟩
  have hGcs : HasCompactSupport (rescale finLam (certSmooth γ)) := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_simplexC 50 finR) ?_
    intro s hs
    rw [Function.mem_support] at hs
    rw [simplexC_eq_simplexSet]
    by_contra hcon
    exact hs (hGzero s (by simpa [finR, mul_comm] using hcon))
  set F : (Fin 50 → ℝ) → ℝ := fun t => finKappa * rescale finLam (certSmooth γ) t with hFdef
  have hJrew : ∀ i : Fin 50, JFunc 50 i finCC F
      = finKappa ^ 2 * finLam ^ 51 * JFunc 50 i ((24 : ℝ) / 25) (certSmooth γ) := by
    intro i
    rw [hFdef]
    rw [JFunc_smul, JFunc_rescale finLam finLam_pos i finCC (certSmooth γ), finCC_div_lam]
    ring
  have hIrew : IFuncOrth 50 F = finKappa ^ 2 * finLam ^ 50 * IFuncOrth 50 (certSmooth γ) := by
    rw [hFdef]
    rw [IFuncOrth_smul, IFuncOrth_rescale finLam finLam_pos (certSmooth γ)]
    ring
  set r : ℝ := (∑ i : Fin 50, JFunc 50 i ((24 : ℝ) / 25) (certSmooth γ))
    / IFuncOrth 50 (certSmooth γ) with hrdef
  have hDelta : (∑ i : Fin 50, JFunc 50 i finCC F) - IFuncOrth 50 F
      = finKappa ^ 2 * finLam ^ 50
          * (IFuncOrth 50 (certSmooth γ) * (finLam * r - 1)) := by
    have hr : (∑ i : Fin 50, JFunc 50 i ((24 : ℝ) / 25) (certSmooth γ))
        = r * IFuncOrth 50 (certSmooth γ) := by
      rw [hrdef, div_mul_cancel₀ _ (ne_of_gt hIpos)]
    calc (∑ i : Fin 50, JFunc 50 i finCC F) - IFuncOrth 50 F
        = finKappa ^ 2 * finLam ^ 51
            * (∑ i : Fin 50, JFunc 50 i ((24 : ℝ) / 25) (certSmooth γ))
          - finKappa ^ 2 * finLam ^ 50 * IFuncOrth 50 (certSmooth γ) := by
          rw [Finset.sum_congr rfl (fun i _ => hJrew i), hIrew, ← Finset.mul_sum]
      _ = finKappa ^ 2 * finLam ^ 50
            * (IFuncOrth 50 (certSmooth γ) * (finLam * r - 1)) := by
          rw [hr]; ring
  refine ⟨γ, F, hγ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hGcont.const_mul finKappa
  · exact hGcs.smul_left (f := fun _ : Fin 50 → ℝ => finKappa)
  · intro t ht
    have hne : rescale finLam (certSmooth γ) t ≠ 0 := by
      intro h0
      rw [hFdef] at ht
      exact ht (by simp [h0])
    exact hGmem t hne
  · intro t
    have h1 : |F t| ≤ finKappa * (10 : ℝ) ^ 54 := by
      rw [hFdef, abs_mul, abs_of_pos finKappa_pos]
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt finKappa_pos)
      rw [show rescale finLam (certSmooth γ) t = certSmooth γ (fun j => t j / finLam)
        from rfl]
      exact abs_certSmooth_le hγ _
    have h2 : finKappa * (10 : ℝ) ^ 54 = 1 := by rw [finKappa_eq]; norm_num
    linarith [h1, h2]
  · -- the lower bound for the variational margin
    have hlow : finKappa ^ 2 * finLam ^ 50 * (certI0 / 2 * ((1 : ℝ) / 5000))
        < (∑ i : Fin 50, JFunc 50 i finCC F) - IFuncOrth 50 F := by
      rw [hDelta]
      have hrc : finLam * ((4001 : ℝ) / 1000) - 1 < finLam * r - 1 := by
        have h := mul_lt_mul_of_pos_left hn1 finLam_pos
        rw [hrdef] at h ⊢
        linarith
      have h3 : certI0 / 2 * ((1 : ℝ) / 5000)
          < IFuncOrth 50 (certSmooth γ) * (finLam * r - 1) := by
        have h4 : IFuncOrth 50 (certSmooth γ) * (finLam * ((4001 : ℝ) / 1000) - 1)
            < IFuncOrth 50 (certSmooth γ) * (finLam * r - 1) :=
          mul_lt_mul_of_pos_left hrc hIpos
        have h5 : certI0 / 2 * ((1 : ℝ) / 5000)
            ≤ IFuncOrth 50 (certSmooth γ) * (finLam * ((4001 : ℝ) / 1000) - 1) := by
          have h6 : certI0 / 2 * ((1 : ℝ) / 5000)
              ≤ IFuncOrth 50 (certSmooth γ) * ((1 : ℝ) / 5000) :=
            mul_le_mul_of_nonneg_right hn2.le (by norm_num)
          have h7 : IFuncOrth 50 (certSmooth γ) * ((1 : ℝ) / 5000)
              ≤ IFuncOrth 50 (certSmooth γ) * (finLam * ((4001 : ℝ) / 1000) - 1) :=
            mul_le_mul_of_nonneg_left finLam_e0 hIpos.le
          linarith
        exact lt_of_le_of_lt h5 h4
      exact mul_lt_mul_of_pos_left h3 (mul_pos (pow_pos finKappa_pos 2) (pow_pos finLam_pos 50))
    have hchain : (1 : ℝ) / 10 ^ 170 ≤ finKappa ^ 2 * finLam ^ 50
        * (certI0 / 2 * ((1 : ℝ) / 5000)) := by
      rw [finKappa_sq]
      have hpow : ((249995 : ℝ) / 1000000) ^ 50 ≤ finLam ^ 50 :=
        pow_le_pow_left₀ (by norm_num) finLam_lo 50
      have h1 : (0 : ℝ) < (1 : ℝ) / 10 ^ 108 := by norm_num
      have hmid : (1 : ℝ) / 10 ^ 108 * ((249995 : ℝ) / 1000000) ^ 50
            * ((1 : ℝ) / 10 ^ 25 * ((1 : ℝ) / 5000))
          ≤ (1 : ℝ) / 10 ^ 108 * finLam ^ 50 * (certI0 / 2 * ((1 : ℝ) / 5000)) := by
        have ha : (1 : ℝ) / 10 ^ 108 * ((249995 : ℝ) / 1000000) ^ 50
            ≤ (1 : ℝ) / 10 ^ 108 * finLam ^ 50 :=
          mul_le_mul_of_nonneg_left hpow h1.le
        have hb : (1 : ℝ) / 10 ^ 25 * ((1 : ℝ) / 5000) ≤ certI0 / 2 * ((1 : ℝ) / 5000) :=
          mul_le_mul_of_nonneg_right certI0_lower (by norm_num)
        calc (1 : ℝ) / 10 ^ 108 * ((249995 : ℝ) / 1000000) ^ 50
              * ((1 : ℝ) / 10 ^ 25 * ((1 : ℝ) / 5000))
            ≤ (1 : ℝ) / 10 ^ 108 * finLam ^ 50
              * ((1 : ℝ) / 10 ^ 25 * ((1 : ℝ) / 5000)) :=
              mul_le_mul_of_nonneg_right ha (by norm_num)
          _ ≤ (1 : ℝ) / 10 ^ 108 * finLam ^ 50 * (certI0 / 2 * ((1 : ℝ) / 5000)) :=
              mul_le_mul_of_nonneg_left hb (by positivity)
      have hnum : (1 : ℝ) / 10 ^ 170 ≤ (1 : ℝ) / 10 ^ 108 * ((249995 : ℝ) / 1000000) ^ 50
          * ((1 : ℝ) / 10 ^ 25 * ((1 : ℝ) / 5000)) := by norm_num
      linarith
    linarith [hlow, hchain]
  · -- the margin is less than `IFuncOrth 50 F`
    rw [hDelta, hIrew]
    have h1 : finLam * r - 1 < 1 := by nlinarith [hn3, finLam_le_quarter, finLam_pos]
    have h2 : IFuncOrth 50 (certSmooth γ) * (finLam * r - 1)
        < IFuncOrth 50 (certSmooth γ) * 1 := mul_lt_mul_of_pos_left h1 hIpos
    have h3 : (0 : ℝ) < finKappa ^ 2 * finLam ^ 50 :=
      mul_pos (pow_pos finKappa_pos 2) (pow_pos finLam_pos 50)
    simpa using mul_lt_mul_of_pos_left h2 h3
  · -- positivity of the `I`-functional
    rw [hIrew]
    exact mul_pos (mul_pos (pow_pos finKappa_pos 2) (pow_pos finLam_pos 50)) hIpos

end

end Commons.NumberTheory.MaynardSieve
