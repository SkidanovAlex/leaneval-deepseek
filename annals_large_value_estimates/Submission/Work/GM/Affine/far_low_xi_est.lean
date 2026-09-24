import Mathlib
import Submission.Work.GM.Affine.region_II_vocab
import Submission.Work.GM.Affine.region_II_defs
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.psi1hat_decay
import Submission.Work.GM.Affine.ghatFar_eq_sum_Wfar
import Submission.Work.GM.Affine.far_wsum_lattice_bound
import Submission.Work.GM.Affine.tail_part_bound
import Submission.Work.GM.Affine.finset_sum_window_le_WinMass
import Submission.Work.GM.Affine.region_I_bound
import Submission.Work.GM.Affine.f_sq_le_const_sq_smallT
import Submission.Work.GM.Affine.winMass_window_ge_center
import Submission.Work.GM.Affine.Wfar_decay_low

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

namespace Work.GM.Affine

noncomputable section

/-! ## Elementary bounds used by `far_low_xi_est` -/

/-- `‖Bsum f M₂ y‖` is at most `(Σ_{m₂∈R2 M₂} m₂) · ∫ f`. -/
lemma norm_Bsum_le_far (f : ℝ → ℝ) (hfnn : ∀ u, 0 ≤ f u) (M₂ y : ℝ) :
    ‖Bsum f M₂ y‖ ≤ (∑ m ∈ R2 M₂, (m:ℝ)) * ∫ u, f u := by
  unfold Bsum
  calc ‖∑ m₂ ∈ R2 M₂, ((m₂:ℝ):ℂ) * Fhat f ((m₂:ℝ)*y)‖
      ≤ ∑ m₂ ∈ R2 M₂, ‖((m₂:ℝ):ℂ) * Fhat f ((m₂:ℝ)*y)‖ := norm_sum_le _ _
    _ = ∑ m₂ ∈ R2 M₂, (m₂:ℝ) * ‖Fhat f ((m₂:ℝ)*y)‖ := by
        apply Finset.sum_congr rfl; intro m₂ hm₂
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (le_of_lt (R2_pos' hm₂))]
    _ ≤ ∑ m₂ ∈ R2 M₂, (m₂:ℝ) * ∫ u, f u := by
        apply Finset.sum_le_sum; intro m₂ hm₂
        exact mul_le_mul_of_nonneg_left (norm_Fhat_le_integral_aux hfnn _) (le_of_lt (R2_pos' hm₂))
    _ = (∑ m₂ ∈ R2 M₂, (m₂:ℝ)) * ∫ u, f u := by rw [Finset.sum_mul]

lemma R1_abs_lt (M₁ : ℝ) {m : ℤ} (hm : m ∈ R1 M₁) : M₁ < |(m:ℝ)| :=
  (Finset.mem_filter.mp hm).2

lemma R1_abs_le (M₁ : ℝ) {m : ℤ} (hm : m ∈ R1 M₁) : |(m:ℝ)| ≤ 2 * M₁ := by
  have h1 : m ∈ Finset.Icc (-⌊2*M₁⌋) ⌊2*M₁⌋ := (Finset.mem_filter.mp hm).1
  rw [Finset.mem_Icc] at h1
  have h2 : ((m:ℤ):ℝ) ≤ ((⌊2*M₁⌋:ℤ):ℝ) := by exact_mod_cast h1.2
  have h3 : ((-⌊2*M₁⌋:ℤ):ℝ) ≤ (m:ℝ) := by exact_mod_cast h1.1
  rw [abs_le]
  constructor
  · push_cast at h3; linarith [Int.floor_le (2*M₁)]
  · linarith [Int.floor_le (2*M₁)]

/-- **Pointwise bound for `ghatFar` on a low-frequency annulus.**

If `Wfar K M₃ ·` is bounded by `CBw * M₃ * T^{-(δ+4)}` on the range
`T^η/(2M₃) ≤ |·| ≤ a^η T^η/M₃`, then `ghatFar` is bounded on the annulus
`Icc(-X,X) \ Icc(-Rr,Rr)` (where `X = a^η T^η M₁/M₃`, `Rr = T^η M₁/M₃`) by
`8 (Σ_{m₂∈R2 M₂} m₂) (∫f) CBw M₃ T^{-(δ+4)}`. -/
lemma ghatFar_pointwise_bound {K M₁ M₂ M₃ CBw T η a δ X Rr : ℝ}
    (hK : 0 < K) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃)
    (hCBw : 0 ≤ CBw) (hT : 1 ≤ T) (ha : 0 ≤ a)
    {f : ℝ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f) (hfnn : ∀ u, 0 ≤ f u)
    (hWf : ∀ y : ℝ, T ^ η / (2 * M₃) ≤ |y| → |y| ≤ a ^ η * T ^ η / M₃ →
      ‖Wfar K M₃ y‖ ≤ CBw * M₃ * T ^ (-(δ + 4)))
    (hRr : Rr = T ^ η * M₁ / M₃) (hX : X = a ^ η * T ^ η * M₁ / M₃)
    {ξ : ℝ} (hξ : ξ ∈ Set.Icc (-X) X \ Set.Icc (-Rr) Rr) :
    ‖ghatFar K M₁ M₂ M₃ f ξ‖ ≤
      8 * (∑ m ∈ R2 M₂, (m:ℝ)) * (∫ u, f u) * CBw * M₃ * T ^ (-(δ+4)) := by
  rw [ghatFar_eq_sum_Wfar hK hM₁ hM₂ hM₃ hf hcs ξ]
  set A : ℝ := ∫ u, f u with hAdef
  set S₂ : ℝ := ∑ m ∈ R2 M₂, (m:ℝ) with hS₂def
  have hAnn : 0 ≤ A := by rw [hAdef]; exact integral_nonneg hfnn
  have hS₂nn : 0 ≤ S₂ := by
    rw [hS₂def]; exact Finset.sum_nonneg (fun m hm => le_of_lt (R2_pos' hm))
  have hS₂A : 0 ≤ S₂ * A := mul_nonneg hS₂nn hAnn
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hCn : 0 ≤ CBw * M₃ * T ^ (-(δ+4)) := by positivity
  have hξle : |ξ| ≤ X := by
    have h := hξ.1; rw [Set.mem_Icc] at h; rw [abs_le]; exact ⟨by linarith [h.1], h.2⟩
  have hξgt : Rr < |ξ| := by
    rw [← not_le]
    intro h
    exact hξ.2 (by rw [Set.mem_Icc]; exact abs_le.mp h)
  have hsum : ∀ m₁ ∈ R1 M₁,
      ‖((( |(m₁:ℝ)| : ℝ) : ℂ))⁻¹ * Bsum f M₂ (ξ / (m₁:ℝ)) * Wfar K M₃ (ξ / (m₁:ℝ))‖
        ≤ (1/|(m₁:ℝ)|) * (S₂ * A) * (CBw * M₃ * T ^ (-(δ+4))) := by
    intro m₁ hm₁
    have hlt := R1_abs_lt M₁ hm₁
    have hle := R1_abs_le M₁ hm₁
    have habsM₁ : (0:ℝ) < |(m₁:ℝ)| := lt_trans hM₁ hlt
    have hyabs : |ξ / (m₁:ℝ)| = |ξ| / |(m₁:ℝ)| := by rw [abs_div]
    have hlo' : T ^ η * M₁ / M₃ < |ξ| := by rw [hRr] at hξgt; exact hξgt
    have hhi' : |ξ| ≤ a ^ η * T ^ η * M₁ / M₃ := by rw [hX] at hξle; exact hξle
    have hW : ‖Wfar K M₃ (ξ / (m₁:ℝ))‖ ≤ CBw * M₃ * T ^ (-(δ+4)) := by
      apply hWf
      · rw [hyabs]
        have h1 : T ^ η * M₁ / M₃ / (2 * M₁) = T ^ η / (2 * M₃) := by field_simp
        have h2 : T ^ η * M₁ / M₃ / (2 * M₁) < |ξ| / (2 * M₁) :=
          div_lt_div_of_pos_right hlo' (by linarith)
        have h3 : |ξ| / (2 * M₁) ≤ |ξ| / |(m₁:ℝ)| :=
          div_le_div_of_nonneg_left (abs_nonneg ξ) habsM₁ hle
        linarith
      · rw [hyabs]
        have h0nn : (0:ℝ) ≤ a ^ η * T ^ η * M₁ / M₃ := by positivity
        have h1 : a ^ η * T ^ η * M₁ / M₃ / M₁ = a ^ η * T ^ η / M₃ := by field_simp
        have h2 : |ξ| / |(m₁:ℝ)| ≤ a ^ η * T ^ η * M₁ / M₃ / |(m₁:ℝ)| :=
          div_le_div_of_nonneg_right hhi' habsM₁.le
        have h3 : a ^ η * T ^ η * M₁ / M₃ / |(m₁:ℝ)| ≤ a ^ η * T ^ η * M₁ / M₃ / M₁ :=
          div_le_div_of_nonneg_left h0nn hM₁ hlt.le
        linarith
    have hB := norm_Bsum_le_far f hfnn M₂ (ξ / (m₁:ℝ))
    have hInv : ‖((( |(m₁:ℝ)| : ℝ) : ℂ))⁻¹‖ = 1/|(m₁:ℝ)| := by
      rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (abs_nonneg (m₁:ℝ)), one_div]
    have hB' : ‖Bsum f M₂ (ξ / (m₁:ℝ))‖ ≤ S₂ * A := by rw [hS₂def, hAdef]; exact hB
    have hA' : (0:ℝ) ≤ 1/|(m₁:ℝ)| := by positivity
    rw [norm_mul, norm_mul, hInv]
    exact mul_le_mul (mul_le_mul le_rfl hB' (norm_nonneg _) hA') hW (norm_nonneg _)
      (mul_nonneg hA' hS₂A)
  have hfac1 : (∑ m₁ ∈ R1 M₁, (1/|(m₁:ℝ)|) * (S₂ * A) * (CBw * M₃ * T ^ (-(δ+4))))
      = (∑ m₁ ∈ R1 M₁, (1/|(m₁:ℝ)|) * (S₂ * A)) * (CBw * M₃ * T ^ (-(δ+4))) :=
    (Finset.sum_mul (R1 M₁) (fun m₁ => (1/|(m₁:ℝ)|) * (S₂ * A)) (CBw * M₃ * T ^ (-(δ+4)))).symm
  have hfac2 : (∑ m₁ ∈ R1 M₁, (1/|(m₁:ℝ)|) * (S₂ * A))
      = (∑ m₁ ∈ R1 M₁, (1/|(m₁:ℝ)|)) * (S₂ * A) :=
    (Finset.sum_mul (R1 M₁) (fun m₁ => (1/|(m₁:ℝ)|)) (S₂ * A)).symm
  calc ‖∑ m₁ ∈ R1 M₁, ((( |(m₁:ℝ)| : ℝ) : ℂ))⁻¹ * Bsum f M₂ (ξ / (m₁:ℝ)) * Wfar K M₃ (ξ / (m₁:ℝ))‖
      ≤ ∑ m₁ ∈ R1 M₁, ‖((( |(m₁:ℝ)| : ℝ) : ℂ))⁻¹ * Bsum f M₂ (ξ / (m₁:ℝ)) * Wfar K M₃ (ξ / (m₁:ℝ))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ m₁ ∈ R1 M₁, (1/|(m₁:ℝ)|) * (S₂ * A) * (CBw * M₃ * T ^ (-(δ+4))) :=
        Finset.sum_le_sum hsum
    _ = (∑ m₁ ∈ R1 M₁, (1/|(m₁:ℝ)|)) * (S₂ * A) * (CBw * M₃ * T ^ (-(δ+4))) := by
        rw [hfac1, hfac2]
    _ ≤ 8 * (S₂ * A) * (CBw * M₃ * T ^ (-(δ+4))) := by
        apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (sum_inv_abs_R1_le M₁ hM₁) hS₂A) hCn
    _ = 8 * (∑ m ∈ R2 M₂, (m:ℝ)) * (∫ u, f u) * CBw * M₃ * T ^ (-(δ+4)) := by
        rw [hS₂def, hAdef]; ring

/-! ## The two analytic inputs -/

/-- The "window mass at the centre" input (proved in `Work.GM.Affine.winMass_window_ge_center`). -/
def WinMassCenterInput (C₀ : ℝ) : Prop :=
  ∃ cA : ℝ, 0 < cA ∧
    ∀ {M₂ M₃ : ℝ}, 0 < M₂ → M₂ ≤ M₃ →
      ∀ {f : ℝ → ℝ}, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
        cA * (∑ m ∈ R2 M₂, (m : ℝ)) ^ 2 * (∫ u, f u) ^ 2
          ≤ ∫ τ in Set.Icc (-2 : ℝ) 2, ‖Hfun f M₂ M₃ 0 τ‖ ^ 2

/-- The decay input for the far weight on the low-frequency annulus
(proved in `Work.GM.Affine.Wfar_decay_low`). -/
def WfarDecayInput (K T₀ a δ : ℝ) : Prop :=
  ∃ CB : ℝ, 0 < CB ∧ ∀ T : ℝ, T₀ ≤ T → ∀ M₃ y : ℝ, T ^ 4 ≤ M₃ →
    T ^ (min δ 1 / 2) / (2 * M₃) ≤ |y| →
    |y| ≤ a ^ (min δ 1 / 2) * T ^ (min δ 1 / 2) / M₃ →
    ‖Wfar K M₃ y‖ ≤ CB * M₃ * T ^ (-(δ + 4))

/-- **`far_low_xi_est`, reduced to the two analytic inputs.** -/
theorem far_low_xi_est_of_inputs {C₀ K T₀ a : ℝ} (hC₀ : 1 ≤ C₀) (hK : 0 < K) (hT₀ : 1 ≤ T₀)
    (ha : 1 ≤ a) (c : ℕ → ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hA : WinMassCenterInput C₀) (hB : WfarDecayInput K T₀ a δ) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ T : ℝ, T₀ ≤ T → ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
        ∀ Λ : ℝ, 0 < Λ →
        (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
          ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ) →
        Λ ≤ 16 * c 2 1 * T ^ 3 * ∫ u, f u →
        ∀ M₁ M₂ M₃ : ℝ, 0 < M₁ → M₁ ≤ T ^ 4 → 0 < M₂ → M₂ ≤ T ^ 4 →
          1 ≤ M₃ → T ^ 4 < M₃ →
        (∫ ξ in (Set.Icc (-(a ^ (min δ 1 / 2) * T ^ (min δ 1 / 2) * M₁ / M₃))
                    (a ^ (min δ 1 / 2) * T ^ (min δ 1 / 2) * M₁ / M₃))
            \ (Set.Icc (-(T ^ (min δ 1 / 2) * M₁ / M₃)) (T ^ (min δ 1 / 2) * M₁ / M₃)),
            ‖ghatFar K M₁ M₂ M₃ f ξ‖ ^ 2) ≤
          C' * T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃ := by
  obtain ⟨cA, hcApos, hA'⟩ := hA
  obtain ⟨CB, hCBpos, hB'⟩ := hB
  have hapos : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hηpos : 0 < min δ 1 / 2 := by
    have h : 0 < min δ 1 := lt_min hδ zero_lt_one
    linarith
  have hηle : min δ 1 / 2 ≤ 1 / 2 := by
    have h : min δ 1 ≤ 1 := min_le_right _ _
    linarith
  have haηpos : 0 < a ^ (min δ 1 / 2) := Real.rpow_pos_of_pos hapos _
  refine ⟨128 * a ^ (min δ 1 / 2) * CB ^ 2 / cA, by positivity, ?_⟩
  intro T hT f hf hfnn hSupp Λ hΛ hdec hΛbd M₁ M₂ M₃ hM₁ hM₁T hM₂ hM₂T hM₃ hM₃T
  have hT1 : (1 : ℝ) ≤ T := le_trans hT₀ hT
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hT1
  have hM₃pos : (0 : ℝ) < M₃ := lt_of_lt_of_le zero_lt_one hM₃
  have hM₂M₃ : M₂ ≤ M₃ := le_of_lt (lt_of_le_of_lt hM₂T hM₃T)
  have hcs : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (1 / C₀) C₀) isCompact_Icc
      (fun x hx => hSupp x (Function.mem_support.mp hx))
  -- the `WinMass` lower bound
  have hWin0 := hA' (M₂ := M₂) (M₃ := M₃) hM₂ hM₂M₃ (f := f) hf hfnn hSupp
  have hW1 := finset_sum_window_le_WinMass (c := c) (T := T) (Λ := Λ) hT1
    (M₂ := M₂) (M₃ := M₃) hM₂ hM₃ (f := f) hf hdec ({0} : Finset ℤ)
  rw [Finset.sum_singleton] at hW1
  have hWin : cA * (∑ m ∈ R2 M₂, (m : ℝ)) ^ 2 * (∫ u, f u) ^ 2 ≤ WinMass f M₂ M₃ :=
    le_trans hWin0 hW1
  -- abbreviate
  set η : ℝ := min δ 1 / 2 with hηdef
  have hηpos' : 0 < η := by rw [hηdef]; exact hηpos
  have hηle' : η ≤ 1 / 2 := by rw [hηdef]; exact hηle
  set X : ℝ := a ^ η * T ^ η * M₁ / M₃ with hXdef
  set Rr : ℝ := T ^ η * M₁ / M₃ with hRrdef
  have hXpos : 0 < X := by rw [hXdef]; positivity
  set S₂ : ℝ := ∑ m ∈ R2 M₂, (m : ℝ) with hS₂def
  set A : ℝ := ∫ u, f u with hAdef
  have hAnn : 0 ≤ A := by rw [hAdef]; exact integral_nonneg hfnn
  have hS₂nn : 0 ≤ S₂ := by
    rw [hS₂def]; exact Finset.sum_nonneg (fun m hm => le_of_lt (R2_pos' hm))
  -- the pointwise bound on the annulus
  have hWf : ∀ y : ℝ, T ^ η / (2 * M₃) ≤ |y| → |y| ≤ a ^ η * T ^ η / M₃ →
      ‖Wfar K M₃ y‖ ≤ CB * M₃ * T ^ (-(δ + 4)) :=
    fun y h1 h2 => hB' T hT M₃ y (le_of_lt hM₃T) h1 h2
  have hpt : ∀ ξ ∈ Set.Icc (-X) X \ Set.Icc (-Rr) Rr,
      ‖ghatFar K M₁ M₂ M₃ f ξ‖ ≤ 8 * S₂ * A * CB * M₃ * T ^ (-(δ + 4)) := by
    intro ξ hξ
    have h := ghatFar_pointwise_bound (K := K) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)
      (CBw := CB) (T := T) (η := η) (a := a) (δ := δ) (X := X) (Rr := Rr)
      hK hM₁ hM₂ hM₃pos hCBpos.le hT1 (le_of_lt hapos) hf hcs hfnn hWf hRrdef hXdef hξ
    rw [hS₂def, hAdef]
    exact h
  -- the integral bound
  set Ann : Set ℝ := Set.Icc (-X) X \ Set.Icc (-Rr) Rr with hAnndef
  have hAnnfin : volume Ann < ⊤ := by
    rw [hAnndef]
    exact lt_of_le_of_lt (measure_mono (fun ξ hξ => hξ.1))
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
  have hvol : volume.real Ann ≤ 2 * X := by
    rw [hAnndef]
    have h1 : volume (Set.Icc (-X) X \ Set.Icc (-Rr) Rr) ≤ volume (Set.Icc (-X) X) :=
      measure_mono (fun ξ hξ => hξ.1)
    have h2 : (volume (Set.Icc (-X) X)).toReal = 2 * X := by
      rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith [hXpos.le])]
      ring
    have hfinX : volume (Set.Icc (-X) X) ≠ ⊤ := by
      rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    calc (volume (Set.Icc (-X) X \ Set.Icc (-Rr) Rr)).toReal
        ≤ (volume (Set.Icc (-X) X)).toReal := ENNReal.toReal_mono hfinX h1
      _ = 2 * X := h2
  have hIntb : ∫ ξ in Ann, ‖ghatFar K M₁ M₂ M₃ f ξ‖ ^ 2
      ≤ (8 * S₂ * A * CB * M₃ * T ^ (-(δ + 4))) ^ 2 * (2 * X) := by
    have h1 : ‖∫ ξ in Ann, ‖ghatFar K M₁ M₂ M₃ f ξ‖ ^ 2‖
        ≤ (8 * S₂ * A * CB * M₃ * T ^ (-(δ + 4))) ^ 2 * volume.real Ann :=
      MeasureTheory.norm_setIntegral_le_of_norm_le_const hAnnfin (fun ξ hξ => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        have hb := hpt ξ hξ
        nlinarith [norm_nonneg (ghatFar K M₁ M₂ M₃ f ξ), hb])
    rw [Real.norm_of_nonneg (integral_nonneg fun ξ => sq_nonneg _)] at h1
    calc ∫ ξ in Ann, ‖ghatFar K M₁ M₂ M₃ f ξ‖ ^ 2
        ≤ (8 * S₂ * A * CB * M₃ * T ^ (-(δ + 4))) ^ 2 * volume.real Ann := h1
      _ ≤ (8 * S₂ * A * CB * M₃ * T ^ (-(δ + 4))) ^ 2 * (2 * X) :=
          mul_le_mul_of_nonneg_left hvol (sq_nonneg _)
  -- the arithmetic
  have hpow1 : (T ^ (-(δ + 4))) ^ 2 = T ^ (-(2 * δ + 8)) := by
    rw [← Real.rpow_natCast (T ^ (-(δ + 4))) 2, ← Real.rpow_mul hTpos.le]
    congr 1; ring
  have hpow2 : T ^ (-(2 * δ + 8)) * T ^ η = T ^ (η - 2 * δ - 8) := by
    rw [← Real.rpow_add hTpos]; congr 1; ring
  have hpow3 : M₁ * T ^ (η - 2 * δ - 8) ≤ T ^ δ := by
    have h1 : M₁ ≤ T ^ ((4:ℕ):ℝ) := by rw [Real.rpow_natCast]; exact hM₁T
    have h4 : T ^ (((4:ℕ):ℝ) + (η - 2 * δ - 8)) ≤ T ^ δ :=
      Real.rpow_le_rpow_of_exponent_le hT1 (by push_cast; linarith [hηle'])
    calc M₁ * T ^ (η - 2 * δ - 8) ≤ T ^ ((4:ℕ):ℝ) * T ^ (η - 2 * δ - 8) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hTpos.le _)
      _ = T ^ (((4:ℕ):ℝ) + (η - 2 * δ - 8)) := (Real.rpow_add hTpos _ _).symm
      _ ≤ T ^ δ := h4
  have hkey : (8 * S₂ * A * CB * M₃ * T ^ (-(δ + 4))) ^ 2 * (2 * X)
      ≤ (128 * a ^ η * CB ^ 2 / cA) * T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃ := by
    have hTaTe : (T ^ (-(δ + 4))) ^ 2 * T ^ η = T ^ (η - 2 * δ - 8) := by
      rw [hpow1, hpow2]
    have hident : (8 * S₂ * A * CB * M₃ * T ^ (-(δ + 4))) ^ 2 * (2 * X)
        = 128 * a ^ η * CB ^ 2 * S₂ ^ 2 * A ^ 2 * M₃
            * (M₁ * ((T ^ (-(δ + 4))) ^ 2 * T ^ η)) := by
      rw [hXdef]; field_simp; ring
    rw [hident, hTaTe]
    -- multiply the three elementary inequalities
    have hnn : (0 : ℝ) ≤ 128 * a ^ η * CB ^ 2 * S₂ ^ 2 * A ^ 2 * M₃ := by positivity
    have hstep1 : 128 * a ^ η * CB ^ 2 * S₂ ^ 2 * A ^ 2 * M₃ * (M₁ * T ^ (η - 2 * δ - 8))
        ≤ 128 * a ^ η * CB ^ 2 * S₂ ^ 2 * A ^ 2 * M₃ * T ^ δ :=
      mul_le_mul_of_nonneg_left hpow3 hnn
    have hstep2 : 128 * a ^ η * CB ^ 2 * S₂ ^ 2 * A ^ 2 * M₃ * T ^ δ
        ≤ 128 * a ^ η * CB ^ 2 * S₂ ^ 2 * A ^ 2 * (M₁ + M₃) * T ^ δ := by
      have hnn2 : 0 ≤ 128 * a ^ η * CB ^ 2 * S₂ ^ 2 * A ^ 2 * T ^ δ := by positivity
      calc 128 * a ^ η * CB ^ 2 * S₂ ^ 2 * A ^ 2 * M₃ * T ^ δ
          = (128 * a ^ η * CB ^ 2 * S₂ ^ 2 * A ^ 2 * T ^ δ) * M₃ := by ring
        _ ≤ (128 * a ^ η * CB ^ 2 * S₂ ^ 2 * A ^ 2 * T ^ δ) * (M₁ + M₃) :=
            mul_le_mul_of_nonneg_left (by linarith) hnn2
        _ = 128 * a ^ η * CB ^ 2 * S₂ ^ 2 * A ^ 2 * (M₁ + M₃) * T ^ δ := by ring
    -- compare with `WinMass`
    have hstep3 : 128 * a ^ η * CB ^ 2 * S₂ ^ 2 * A ^ 2 * (M₁ + M₃) * T ^ δ
        ≤ (128 * a ^ η * CB ^ 2 / cA) * T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃ := by
      have hfac : 0 ≤ (128 * a ^ η * CB ^ 2 / cA) * T ^ δ * (M₁ + M₃) := by positivity
      have h1 : (128 * a ^ η * CB ^ 2 / cA) * T ^ δ * (M₁ + M₃) * (cA * S₂ ^ 2 * A ^ 2)
          ≤ (128 * a ^ η * CB ^ 2 / cA) * T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃ :=
        mul_le_mul_of_nonneg_left hWin hfac
      have h2 : (128 * a ^ η * CB ^ 2 / cA) * T ^ δ * (M₁ + M₃) * (cA * S₂ ^ 2 * A ^ 2)
          = 128 * a ^ η * CB ^ 2 * S₂ ^ 2 * A ^ 2 * (M₁ + M₃) * T ^ δ := by
        field_simp
      rw [h2] at h1
      exact h1
    linarith [hstep1, hstep2, hstep3]
  linarith [hIntb, hkey]

/-- **GM §9, region II, low-frequency far part.** -/
theorem far_low_xi_est {C₀ K T₀ a : ℝ} (hC₀ : 1 ≤ C₀) (hK : 0 < K) (hT₀ : 1 ≤ T₀)
    (ha : 1 ≤ a) (c : ℕ → ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ T : ℝ, T₀ ≤ T → ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
        ∀ Λ : ℝ, 0 < Λ →
        (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
          ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ) →
        Λ ≤ 16 * c 2 1 * T ^ 3 * ∫ u, f u →
        ∀ M₁ M₂ M₃ : ℝ, 0 < M₁ → M₁ ≤ T ^ 4 → 0 < M₂ → M₂ ≤ T ^ 4 →
          1 ≤ M₃ → T ^ 4 < M₃ →
        (∫ ξ in (Set.Icc (-(a ^ (min δ 1 / 2) * T ^ (min δ 1 / 2) * M₁ / M₃))
                    (a ^ (min δ 1 / 2) * T ^ (min δ 1 / 2) * M₁ / M₃))
            \ (Set.Icc (-(T ^ (min δ 1 / 2) * M₁ / M₃)) (T ^ (min δ 1 / 2) * M₁ / M₃)),
            ‖ghatFar K M₁ M₂ M₃ f ξ‖ ^ 2) ≤
          C' * T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃ := by
  refine far_low_xi_est_of_inputs (C₀ := C₀) (K := K) (T₀ := T₀) (a := a)
    hC₀ hK hT₀ ha c δ hδ ?_ ?_
  · exact winMass_window_ge_center C₀ hC₀
  · exact Wfar_decay_low (K := K) (T₀ := T₀) (a := a) hK ha hT₀ δ hδ

end

end Work.GM.Affine
