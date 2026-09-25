import Mathlib
import Submission.Work.BourgainPlan.Maximal.iw_superset
import Submission.Work.BourgainPlan.Maximal.main_narrow_sigmaLe
import Submission.Work.BourgainPlan.Maximal.taoSetS_arith
import Submission.Work.BourgainPlan.Maximal.exists_flat_bump_uniform
import Submission.Work.BourgainPlan.Maximal.ellp_interpolation
import Submission.Work.BourgainPlan.IonescuWainger.nonce_smallness_of_good
import Submission.Work.BourgainPlan.IonescuWainger.petal_smallness_of_good
import Submission.Work.BourgainPlan.KPWW.eLpNorm_opArc_le_of_finsupp

namespace Work.BourgainPlan.Maximal

open MeasureTheory ENNReal Finset
open scoped ENNReal BigOperators
open Work.BourgainPlan.IonescuWainger

noncomputable section

/-- **Uniform-in-`qmax` form of `main_narrow_sigmaLe`**: the constant of Tao's `main` is hoisted in
front of `qmax` (and `S`, `ε`, `η`, …).  This is the form the MST assembly needs, since the
superset `Σ_N` is indexed by `N` while the constant must not depend on `N`.  The proof is that of
`main_narrow_sigmaLe`, with the (in fact `qmax`-independent) constant extracted first and the
quantifiers reordered. -/
theorem main_narrow_sigmaLe_uniform {k r : ℕ} (hr : 2 ≤ r) (hk : 1 ≤ k) :
    ∀ {Cφ Mφ : ℝ} (hCφ : 0 ≤ Cφ) (hMφ : 0 ≤ Mφ),
      ∃ K : ℝ, 0 < K ∧
      ∀ {qmax : ℕ} (hqmax : 1 ≤ qmax)
        {S : Finset ℕ} (h2S : ∀ q ∈ S, 2 ≤ q)
        (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
        (hmax : ∀ q ∈ S, q ≤ qmax)
        {ε η : ℝ} (hε0 : 0 < ε) (hη0 : 0 < η)
        (hεη : ε + η < 1 / (qmax : ℝ) ^ (2 * k)) (hη2 : 2 * η < 1 / (qmax : ℝ) ^ (2 * k))
        (hεq : ε * (qmax : ℝ) ^ k ≤ 1) (hεq2 : ε * (qmax : ℝ) ^ k < 1 / 2)
        (ψ : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
        (hψ : MeasureTheory.MemLp ψ ⊤ (AddCircle.haarAddCircle (T := 1)))
        (hψsupp : ∀ (ξ : Work.BourgainPlan.IonescuWainger.Circle), ε < ‖ξ‖ → ψ ξ = 0)
        (A : ℝ) (hA : 0 ≤ A)
        (hMult : ∀ (g : ℝ → ℂ), MeasureTheory.Integrable g →
          ∫⁻ x : ℝ, ‖FourierTransformInv.fourierInv
              (fun ξ : ℝ => Work.BourgainPlan.Thm52.circleLift ψ ξ
                * FourierTransform.fourier g ξ) x‖ₑ ^ (2 * (r : ℝ)) ∂MeasureTheory.volume
            ≤ ENNReal.ofReal (A ^ (2 * (r : ℝ)))
              * ∫⁻ x : ℝ, ‖g x‖ₑ ^ (2 * (r : ℝ)) ∂MeasureTheory.volume)
        (φ : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
        (hφ : MeasureTheory.MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1)))
        (hφbd : ∀ (ξ : Work.BourgainPlan.IonescuWainger.Circle), ‖φ ξ‖ ≤ Mφ)
        (hφsupp : ∀ (ξ : Work.BourgainPlan.IonescuWainger.Circle), η < ‖ξ‖ → φ ξ = 0)
        (hφone : ∀ (ξ : Work.BourgainPlan.IonescuWainger.Circle), ‖ξ‖ ≤ ε → φ ξ = 1)
        {Kφ : ℤ → ℂ} (hKφ : ∀ m : ℤ, ∫ ξ, φ ξ * star (fourier m ξ)
          ∂(AddCircle.haarAddCircle (T := 1)) = Kφ m)
        (hdecayφ : ∀ m : ℤ, ‖Kφ m‖
          ≤ Cφ * η / (1 + (η * (m : ℝ)) ^ 2) ^ ((3 : ℝ) / 2))
        (hsmallN : ∀ A : Fin r ⊕ Fin r → Finset ℕ, (∀ j, A j ⊆ S ∧ (A j).card ≤ k) →
          Work.BourgainPlan.IonescuWainger.HasNonce A →
          2 * (r : ℝ) * ε < 1 / ((∏ j, Work.BourgainPlan.IonescuWainger.QA (A j) : ℕ) : ℝ))
        (hsmallP : ∀ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
          ∀ A : (i : Fin r) → ↥((S \ A₀).powerset.filter (fun B => B.card ≤ k - A₀.card)),
            (∀ i j : Fin r, i ≠ j → Disjoint ((A i).1) ((A j).1)) →
            2 * (r : ℝ) * ε * ((Work.BourgainPlan.IonescuWainger.QA A₀ *
              (∏ i, Work.BourgainPlan.IonescuWainger.QA ((A i).1)) : ℕ) : ℝ) < 1)
        (f : ℤ →₀ ℂ),
        ∑' n : ℤ, ENNReal.ofReal (‖Work.BourgainPlan.IonescuWainger.opArc ψ hψ
            (Work.BourgainPlan.IonescuWainger.sigmaLeFinset S k) (⇑f)
            (Work.BourgainPlan.IonescuWainger.memℓp_finsupp f) n‖ ^ (2 * r))
          ≤ ENNReal.ofReal (K * A ^ (2 * r)) *
            ∑' n : ℤ, ENNReal.ofReal (‖(⇑f : ℤ → ℂ) n‖ ^ (2 * r)) := by
  intro Cφ Mφ hCφ hMφ
  classical
  obtain ⟨M₀, hM₀⟩ := Work.BourgainPlan.IonescuWainger.erdos_rado_sunflower k r
  set M : ℕ := max M₀ 2 with hMdef
  have hM2 : 2 ≤ M := by rw [hMdef]; exact le_max_right _ _
  have hM0M : M₀ ≤ M := by rw [hMdef]; exact le_max_left _ _
  obtain ⟨C, hCpos, hC⟩ :=
    Work.IonescuWainger.ortho_apply_lower_strata_system_ennreal_uniform k r hr hk
  obtain ⟨C₃, hC₃pos, hC₃⟩ :=
    Work.BourgainPlan.Maximal.hstep3_msw_uniform (k := k) (r := r) hr hk
  set C₁ : ℝ := C ^ (k * r) * (k + 1 : ℝ) ^ (r - 1) * (4 * M : ℝ) ^ r with hC₁def
  set C₄ : ℝ := ((Mφ ^ 2 * (2 ^ k : ℝ)) ^ (1 / (2 * r : ℝ)) *
      (8 * Cφ * (2 ^ k : ℝ)) ^ (1 - 2 / (2 * r : ℝ))) ^ (2 * r : ℝ) with hC₄def
  have hC₁nn : 0 ≤ C₁ := by rw [hC₁def]; positivity
  have hC₄nn : 0 ≤ C₄ := by rw [hC₄def]; exact Real.rpow_nonneg (by positivity) _
  refine ⟨max 1 (C₁ * C₃ ^ (2 * r) * C₄), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro qmax hqmax S h2S hS hmax ε η hε0 hη0 hεη hη2 hεq hεq2
      ψ hψ hψsupp A hA hMult φ hφ hφbd hφsupp hφone Kφ hKφ hdecayφ hsmallN hsmallP f
  have hsun : ∀ T : Finset (Finset ℕ), (∀ A ∈ T, A ⊆ S) → (∀ A ∈ T, A.card ≤ k) → M ≤ T.card →
      ∃ A : Fin r → Finset ℕ, (∀ i, A i ∈ T) ∧ Function.Injective A ∧ IsSunflower A :=
    fun T _ hcard hMle => hM₀ T hcard (hM0M.trans hMle)
  have hstep1 : ∑' x : ℤ, ENNReal.ofReal (‖∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
        (1 : ℂ) * opArc ψ hψ (sigmaStrataFinset A) (⇑f) (memℓp_finsupp f) x‖ ^ (2 * r))
      ≤ ENNReal.ofReal C₁ *
        ∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
          ∑' x : ℤ, (∑ α ∈ strataCompFinset S k A₀,
              ENNReal.ofReal (‖opArc ψ hψ
                (arcShift (sigmaStrataFinset A₀) α) (⇑f)
                (memℓp_finsupp f) x‖ ^ 2)) ^ (r : ℝ) :=
    hC h2S hS hM2 hsun hε0.le ψ hψ hψsupp hsmallN hsmallP
      (fun _ => (1 : ℂ)) (fun _ => by simp) (⇑f) (memℓp_finsupp f)
  have hpow : (C₃ * A) ^ (2 * (r : ℝ)) = (C₃ * A) ^ (2 * r) := by
    rw [show (2 * (r : ℝ)) = ((2 * r : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hstep3 : ∀ (A₀ : Finset ℕ), A₀ ⊆ S → A₀.card ≤ k →
      ∀ (F : ↥(strataCompFinset S k A₀) → ℤ → ℂ) (hF : ∀ t, Memℓp (F t) 2),
      ∑' n : ℤ, (∑ α : ↥(strataCompFinset S k A₀),
          ENNReal.ofReal (‖opArc ψ hψ
            (arcShift (sigmaStrataFinset A₀) α.1)
            (F α) (hF α) n‖ ^ 2)) ^ (r : ℝ)
        ≤ ENNReal.ofReal ((C₃ * A) ^ (2 * r)) *
          ∑' n : ℤ, (∑ α : ↥(strataCompFinset S k A₀),
            ENNReal.ofReal (‖F α n‖ ^ 2)) ^ (r : ℝ) := by
    intro A₀ hA₀S hk₀ F hF
    have h := hC₃ (qmax := qmax) hqmax h2S hS hmax ε hε0 hεq2 ψ hψ hψsupp A hA hMult A₀ hA₀S hk₀ F hF
    rwa [hpow] at h
  have hstep4 : ∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
        ∑' n : ℤ, (∑ α ∈ strataCompFinset S k A₀,
            ENNReal.ofReal (‖opArc φ hφ
              (arcShift (sigmaStrataFinset A₀) α) (⇑f)
              (memℓp_finsupp f) n‖ ^ 2)) ^ (r : ℝ)
      ≤ ENNReal.ofReal C₄ * ∑' n : ℤ, ENNReal.ofReal (‖(⇑f : ℤ → ℂ) n‖ ^ (2 * r)) := by
    have h := Work.IonescuWainger.ortho_apply_upper_pow (S := S) h2S hS hmax hqmax (k := k) (ε := η)
      hη0 hη2 φ hφ (M := Mφ) hMφ hφbd hφsupp (K := Kφ) (C := Cφ) hCφ hKφ hdecayφ
      (r := r) (le_trans (by norm_num) hr) f
    rw [hC₄def]
    exact h
  have hmain := Work.IonescuWainger.main_real_of_inputs (S := S) h2S hS hr hk hmax hqmax hε0 hεη
    ψ φ hψ hφ hψsupp hφsupp hφone (εs := fun _ => (1 : ℂ)) (fun _ => by simp) f
    (C₁ := C₁) (W := (C₃ * A) ^ (2 * r)) (C₄ := C₄) hC₁nn
    (pow_nonneg (mul_nonneg hC₃pos.le hA) _) hC₄nn hstep1 hstep3 hstep4
  have hkey : (∑' n : ℤ, ENNReal.ofReal (‖opArc ψ hψ
        (sigmaLeFinset S k) (⇑f) (memℓp_finsupp f) n‖ ^ (2 * r)))
      = ∑' n : ℤ, ENNReal.ofReal (‖∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
          (1 : ℂ) * opArc ψ hψ (sigmaStrataFinset A) (⇑f) (memℓp_finsupp f) n‖ ^ (2 * r)) := by
    refine tsum_congr (fun n => ?_)
    rw [Work.IonescuWainger.opArc_sigmaLe_eq_sum_strata h2S hS ψ hψ (⇑f) (memℓp_finsupp f)]
    simp only [one_mul, Finset.sum_apply]
  rw [hkey]
  refine hmain.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
  calc C₁ * (C₃ * A) ^ (2 * r) * C₄
      = (C₁ * C₃ ^ (2 * r) * C₄) * A ^ (2 * r) := by rw [mul_pow]; ring
    _ ≤ max 1 (C₁ * C₃ ^ (2 * r) * C₄) * A ^ (2 * r) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hA _)

/-- The `q`-th power of the `eLpNorm` against the counting measure on `ℤ` is the `ℓ^q`-sum of the
`q`-th powers (i.e. the `q`-th power of the `L^q` norm is the `L^q` "integral"). -/
lemma eLpNorm_count_rpow_eq_tsum' (X : ℤ → ℂ) {q : ℝ} (hq : 0 < q) :
    (eLpNorm X (ENNReal.ofReal q) Measure.count) ^ q
      = ∑' n : ℤ, ENNReal.ofReal (‖X n‖ ^ q) := by
  rw [eLpNorm_count_eq_tsum X hq, ← ENNReal.rpow_mul, one_div_mul_cancel (ne_of_gt hq),
    ENNReal.rpow_one]

/-- The `q`-th power of the `L^q`-norm against the counting measure, written as a `lintegral`
of the `q`-th power of the extended norm. -/
lemma lintegral_enorm_rpow_eq_eLpNorm_rpow (X : ℤ → ℂ) {q : ℝ} (hq : 0 < q) :
    ∫⁻ n : ℤ, ‖X n‖ₑ ^ q ∂Measure.count
      = (eLpNorm X (ENNReal.ofReal q) Measure.count) ^ q := by
  rw [MeasureTheory.lintegral_count, eLpNorm_count_rpow_eq_tsum' X hq]
  exact tsum_congr (fun n => by
    rw [show ‖X n‖ₑ = ENNReal.ofReal ‖X n‖ by simp [enorm_eq_nnnorm],
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq.le])


/-- **The `ℓ^{2r}` endpoint of Tao's `main` at the superset `Σ_N = iwSigma ρ N`** (`r ≥ 2`), for
`ℓ²` inputs: obtained from `main_narrow_sigmaLe` with `S := taoSetS ρ N` by supplying
`qmax := ⌈N^{⌊N^{ρ/2}⌋+1}⌉₊` (`taoSetS_arith`), the flat bump at `η := 1/(4 qmax^{2k})`,
`k := iwK ρ` (`exists_flat_bump_uniform`), and the smallness hypotheses from
`nonce_smallness_of_good`/`petal_smallness_of_good`; the passage from finitely supported data to
`ℓ²` is the extension principle `Work.BourgainPlan.KPWW.eLpNorm_opArc_le_of_finsupp`. -/
theorem main_narrow_taoSetS (ρ : ℝ) (hρ : 0 < ρ) (r : ℕ) (hr : 2 ≤ r) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
      ∀ (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ Work.BourgainPlan.Maximal.iwEps ρ N)
        (ψ : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
        (hψ : MeasureTheory.MemLp ψ ⊤ (AddCircle.haarAddCircle (T := 1)))
        (hψsupp : ∀ (ξ : Work.BourgainPlan.IonescuWainger.Circle), ε < ‖ξ‖ → ψ ξ = 0)
        (A : ℝ) (hA : 0 ≤ A)
        (hMult : Work.BourgainPlan.Maximal.IWMult r ψ A)
        (f : ℤ → ℂ) (hf : Memℓp f 2),
        ∫⁻ n : ℤ, ‖Work.BourgainPlan.IonescuWainger.opArc ψ hψ
            (Work.BourgainPlan.Maximal.iwSigma ρ N) f hf n‖ₑ ^ (2 * (r : ℝ))
            ∂MeasureTheory.Measure.count
          ≤ ENNReal.ofReal ((K * A) ^ (2 * (r : ℝ)))
            * ∫⁻ n : ℤ, ‖f n‖ₑ ^ (2 * (r : ℝ)) ∂MeasureTheory.Measure.count := by
  classical
  have hk : 1 ≤ iwK ρ := by rw [iwK]; exact Nat.le_add_left 1 _
  obtain ⟨Cφ, hCφpos, hbump⟩ := exists_flat_bump_uniform
  have hCφ : 0 ≤ Cφ := hCφpos.le
  obtain ⟨K₀, hK₀pos, hmain⟩ :=
    main_narrow_sigmaLe_uniform (k := iwK ρ) (r := r) hr hk (Cφ := Cφ) (Mφ := 1) hCφ (by norm_num)
  set p : ℝ := 2 * (r : ℝ) with hpdef
  have hp : 0 < p := by rw [hpdef]; positivity
  have hp_cast : p = ((2 * r : ℕ) : ℝ) := by rw [hpdef]; push_cast; ring
  obtain ⟨N₁, hN₁⟩ := taoSetS_arith ρ hρ r (iwK ρ) hr hk
  have hKpos : 0 < K₀ ^ (1 / p) := Real.rpow_pos_of_pos hK₀pos _
  refine ⟨K₀ ^ (1 / p), hKpos, max N₁ 1, fun N hN => ?_⟩
  intro ε hε0 hεle ψ hψ hψsupp A hA hMult f hf
  set K : ℝ := K₀ ^ (1 / p) with hKdef
  have hN₁N : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  obtain ⟨h2S, hS, hmax_raw, hgood_raw⟩ := hN₁ N hN₁N
  set qmax : ℕ := ⌈(N : ℝ) ^ ((⌊(N : ℝ) ^ (ρ / 2)⌋₊ + 1 : ℕ) : ℝ)⌉₊ with hqmaxdef
  set D : ℝ := (qmax : ℝ) ^ (2 * iwK ρ) with hDdef
  set η : ℝ := 1 / (4 * D) with hηdef
  have hmax : ∀ q ∈ taoSetS ρ N, q ≤ qmax := by
    intro q hq; rw [hqmaxdef]; exact hmax_raw q hq
  have hqmax : 1 ≤ qmax := by
    rw [hqmaxdef]
    exact Nat.one_le_ceil_iff.mpr (Real.rpow_pos_of_pos hNpos _)
  have hQ1 : (1 : ℝ) ≤ (qmax : ℝ) := by exact_mod_cast hqmax
  have hD1 : 1 ≤ D := by rw [hDdef]; exact one_le_pow₀ hQ1
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD1
  -- ### smallness of `ε` against `D = qmax^{2k}`
  have hgood : ε * (2 * (r : ℝ) * (qmax : ℝ) ^ (2 * r * iwK ρ)) < 1 / 2 := by
    rw [hqmaxdef]; exact hgood_raw ε hε0 hεle
  have hQD : (qmax : ℝ) ^ (2 * iwK ρ) ≤ (qmax : ℝ) ^ (2 * r * iwK ρ) :=
    pow_le_pow_right₀ hQ1 (Nat.mul_le_mul_right (iwK ρ) (by omega : 2 ≤ 2 * r))
  have h2rD : ε * (2 * (r : ℝ) * D) < 1 / 2 := by
    have hstep : 2 * (r : ℝ) * D ≤ 2 * (r : ℝ) * (qmax : ℝ) ^ (2 * r * iwK ρ) := by
      rw [hDdef]; exact mul_le_mul_of_nonneg_left hQD (by positivity)
    have h2 : ε * (2 * (r : ℝ) * D) ≤ ε * (2 * (r : ℝ) * (qmax : ℝ) ^ (2 * r * iwK ρ)) :=
      mul_le_mul_of_nonneg_left hstep hε0.le
    linarith [h2, hgood]
  have hεD : 8 * ε * D < 1 := by
    have hr4 : (4 : ℝ) ≤ 2 * (r : ℝ) := by
      have h2r : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
      linarith
    have h4 : 4 * ε * D ≤ 2 * (r : ℝ) * ε * D := by
      have h : (4 : ℝ) * (ε * D) ≤ (2 * (r : ℝ)) * (ε * D) :=
        mul_le_mul_of_nonneg_right hr4 (by positivity)
      nlinarith [h]
    have h1 : 4 * ε * D < 1 / 2 := by nlinarith [h2rD, h4]
    nlinarith [h1]
  have hη0 : 0 < η := by rw [hηdef]; positivity
  have hηhalf : η ≤ 1 / 2 := by
    rw [hηdef, div_le_iff₀ (by positivity : (0 : ℝ) < 4 * D)]
    nlinarith [hD1]
  have h2εη : 2 * ε ≤ η := by
    rw [hηdef, le_div_iff₀ (by positivity : (0 : ℝ) < 4 * D)]
    nlinarith [hεD, hDpos]
  have hεlt8 : ε < 1 / (8 * D) := by
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 8 * D)]
    nlinarith [hεD]
  have hεη : ε + η < 1 / (qmax : ℝ) ^ (2 * iwK ρ) := by
    rw [← hDdef, hηdef]
    field_simp
    nlinarith [hεD, hDpos]
  have hη2 : 2 * η < 1 / (qmax : ℝ) ^ (2 * iwK ρ) := by
    rw [← hDdef, hηdef]
    field_simp
    nlinarith [hDpos]
  have hQkD : (qmax : ℝ) ^ (iwK ρ) ≤ D := by
    rw [hDdef]
    exact pow_le_pow_right₀ hQ1 (by omega : iwK ρ ≤ 2 * iwK ρ)
  have h18 : (1 / (8 * D)) * D = 1 / 8 := by field_simp
  have hεq : ε * (qmax : ℝ) ^ (iwK ρ) ≤ 1 := by
    have hle : ε * (qmax : ℝ) ^ (iwK ρ) ≤ (1 / (8 * D)) * D :=
      mul_le_mul hεlt8.le hQkD (by positivity) (by positivity)
    rw [h18] at hle
    linarith [hle]
  have hεq2 : ε * (qmax : ℝ) ^ (iwK ρ) < 1 / 2 := by
    have hle : ε * (qmax : ℝ) ^ (iwK ρ) ≤ (1 / (8 * D)) * D :=
      mul_le_mul hεlt8.le hQkD (by positivity) (by positivity)
    rw [h18] at hle
    linarith [hle]
  have hgood_small : ε < (1 / 2) / (2 * (r : ℝ) * (qmax : ℝ) ^ (2 * r * iwK ρ)) := by
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * (r : ℝ) * (qmax : ℝ) ^ (2 * r * iwK ρ))]
    exact hgood
  -- ### the flat bump at `η = 1/(4 D)`
  obtain ⟨φ, hφmem, hφbd, hφsupp, hφone, hφdecay⟩ := hbump ε η hε0 h2εη hηhalf
  set Kφ : ℤ → ℂ := fun m => ∫ ξ, φ ξ * star (fourier m ξ)
      ∂(AddCircle.haarAddCircle (T := 1)) with hKφdef
  have hKφ : ∀ m : ℤ, ∫ ξ, φ ξ * star (fourier m ξ) ∂(AddCircle.haarAddCircle (T := 1))
      = Kφ m := fun m => rfl
  have hdecayφ : ∀ m : ℤ, ‖Kφ m‖
      ≤ Cφ * η / (1 + (η * (m : ℝ)) ^ 2) ^ ((3 : ℝ) / 2) := fun m => hφdecay m
  -- ### the smallness hypotheses of Tao's `main`
  have hsmallN : ∀ A' : Fin r ⊕ Fin r → Finset ℕ,
      (∀ j, A' j ⊆ taoSetS ρ N ∧ (A' j).card ≤ iwK ρ) →
      HasNonce A' → 2 * (r : ℝ) * ε < 1 / ((∏ j, QA (A' j) : ℕ) : ℝ) := by
    intro A' hA' _
    exact nonce_smallness_of_good h2S hqmax hmax (c := 1 / 2) (ε := ε)
      (by norm_num) (by norm_num) hgood_small (fun j => (hA' j).1) (fun j => (hA' j).2)
  have hsmallP : ∀ A₀ ∈ (taoSetS ρ N).powerset.filter (fun A => A.card ≤ iwK ρ),
      ∀ A' : (i : Fin r) → ↥(((taoSetS ρ N) \ A₀).powerset.filter
        (fun B => B.card ≤ iwK ρ - A₀.card)),
        (∀ i j : Fin r, i ≠ j → Disjoint ((A' i).1) ((A' j).1)) →
        2 * (r : ℝ) * ε * ((QA A₀ * (∏ i, QA ((A' i).1)) : ℕ) : ℝ) < 1 := by
    intro A₀ hA₀ A' _
    exact petal_smallness_of_good h2S hqmax hmax (c := 1 / 2) (ε := ε)
      (by norm_num) (by norm_num) hgood_small (A₀ := A₀)
      (Finset.mem_powerset.mp (Finset.mem_filter.mp hA₀).1) (Finset.mem_filter.mp hA₀).2
      (A := fun i => (A' i).1)
      (fun i => Finset.mem_powerset.mp (Finset.mem_filter.mp (A' i).2).1)
      (fun i => (Finset.mem_filter.mp (A' i).2).2)
  -- ### Tao's `main` for finitely supported data
  have hfs : ∀ g : ℤ →₀ ℂ,
      ∑' n : ℤ, ENNReal.ofReal (‖opArc ψ hψ (iwSigma ρ N) (⇑g) (memℓp_finsupp g) n‖ ^ (2 * r))
        ≤ ENNReal.ofReal (K₀ * A ^ (2 * r)) *
          ∑' n : ℤ, ENNReal.ofReal (‖(⇑g : ℤ → ℂ) n‖ ^ (2 * r)) := by
    intro g
    have h := hmain hqmax h2S hS hmax hε0 hη0 hεη hη2 hεq hεq2 ψ hψ hψsupp A hA hMult
      φ hφmem hφbd hφsupp hφone hKφ hdecayφ hsmallN hsmallP g
    simpa only [iwSigma] using h
  -- ### the extension to `ℓ²`
  have hM : 0 ≤ K * A := mul_nonneg hKpos.le hA
  have hKpow : K ^ p = K₀ := by
    rw [hKdef, ← Real.rpow_mul hK₀pos.le, one_div_mul_cancel (ne_of_gt hp), Real.rpow_one]
  have hAp : A ^ p = A ^ (2 * r) := by
    rw [hpdef, show (2 : ℝ) * (r : ℝ) = ((2 * r : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hKA : (K * A) ^ p = K₀ * A ^ (2 * r) := by
    rw [Real.mul_rpow hKpos.le hA, hKpow, hAp]
  have hEA : ENNReal.ofReal (K₀ * A ^ (2 * r)) ^ (1 / p) = ENNReal.ofReal (K * A) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
    congr 1
    rw [Real.mul_rpow hK₀pos.le (pow_nonneg hA _), ← hKdef]
    congr 1
    rw [← Real.rpow_natCast A (2 * r), ← Real.rpow_mul hA,
      show ((2 * r : ℕ) : ℝ) * (1 / p) = 1 by rw [hpdef]; push_cast; field_simp, Real.rpow_one]
  have hfin : ∀ g : ℤ →₀ ℂ,
      eLpNorm (opArcLM ψ hψ (iwSigma ρ N) g) (ENNReal.ofReal p) Measure.count
        ≤ ENNReal.ofReal (K * A) * eLpNorm (⇑g) (ENNReal.ofReal p) Measure.count := by
    intro g
    have hg := hfs g
    rw [eLpNorm_count_eq_tsum ((opArcLM ψ hψ (iwSigma ρ N)) g) hp,
        eLpNorm_count_eq_tsum (⇑g) hp]
    have e1 : (∑' n : ℤ, ENNReal.ofReal (‖(opArcLM ψ hψ (iwSigma ρ N)) g n‖ ^ p))
        = ∑' n : ℤ, ENNReal.ofReal
            (‖opArc ψ hψ (iwSigma ρ N) (⇑g) (memℓp_finsupp g) n‖ ^ (2 * r)) := by
      refine tsum_congr (fun n => ?_)
      rw [Work.BourgainPlan.IonescuWainger.opArcLM_apply]
      congr 1
      rw [hp_cast, Real.rpow_natCast]
    have e2 : (∑' n : ℤ, ENNReal.ofReal (‖(⇑g : ℤ → ℂ) n‖ ^ p))
        = ∑' n : ℤ, ENNReal.ofReal (‖(⇑g : ℤ → ℂ) n‖ ^ (2 * r)) := by
      refine tsum_congr (fun n => ?_)
      congr 1
      rw [hp_cast, Real.rpow_natCast]
    rw [e1, e2]
    calc (∑' n : ℤ, ENNReal.ofReal
            (‖opArc ψ hψ (iwSigma ρ N) (⇑g) (memℓp_finsupp g) n‖ ^ (2 * r))) ^ (1 / p)
        ≤ (ENNReal.ofReal (K₀ * A ^ (2 * r))
            * ∑' n : ℤ, ENNReal.ofReal (‖(⇑g : ℤ → ℂ) n‖ ^ (2 * r))) ^ (1 / p) :=
          ENNReal.rpow_le_rpow hg (by positivity)
      _ = (ENNReal.ofReal (K₀ * A ^ (2 * r))) ^ (1 / p)
            * (∑' n : ℤ, ENNReal.ofReal (‖(⇑g : ℤ → ℂ) n‖ ^ (2 * r))) ^ (1 / p) :=
          ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
      _ = ENNReal.ofReal (K * A)
            * (∑' n : ℤ, ENNReal.ofReal (‖(⇑g : ℤ → ℂ) n‖ ^ (2 * r))) ^ (1 / p) := by rw [hEA]
  have hELp := Work.BourgainPlan.KPWW.eLpNorm_opArc_le_of_finsupp (p := p) hp (M := K * A) hM
    ψ hψ (iwSigma ρ N) hfin f hf
  rw [lintegral_enorm_rpow_eq_eLpNorm_rpow (opArc ψ hψ (iwSigma ρ N) f hf) hp,
      lintegral_enorm_rpow_eq_eLpNorm_rpow f hp]
  calc (eLpNorm (opArc ψ hψ (iwSigma ρ N) f hf) (ENNReal.ofReal p) Measure.count) ^ p
      ≤ (ENNReal.ofReal (K * A) * eLpNorm f (ENNReal.ofReal p) Measure.count) ^ p :=
        ENNReal.rpow_le_rpow hELp (by positivity)
    _ = (ENNReal.ofReal (K * A)) ^ p * (eLpNorm f (ENNReal.ofReal p) Measure.count) ^ p :=
        ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
    _ = ENNReal.ofReal ((K * A) ^ p) * (eLpNorm f (ENNReal.ofReal p) Measure.count) ^ p := by
        rw [ENNReal.ofReal_rpow_of_nonneg hM (by positivity)]

end

end Work.BourgainPlan.Maximal
