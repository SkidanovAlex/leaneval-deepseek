import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.halasz_complex
import Submission.Work.BMF.norm_cpow_I_eq_one
import Submission.Work.BMF.norm_window_avg_le
import Submission.Work.BMF.aemeasurable_window_avg
import Submission.Work.BMF.block_sum_integral_le
import Submission.Work.BMF.mr_parseval_direct
import Submission.Work.BMF.mr_dirichlet_L2_sup

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open BoundedMultiplicativeFunctions

theorem dist_mono {f g : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1)
    {X Y : ℝ} (hXY : X ≤ Y) : 𝔻 f g X ≤ 𝔻 f g Y := by
  have key : ∀ p : ℕ, 0 ≤ (1 - (f p * star (g p)).re) / (p : ℝ) := by
    intro p
    have hpR : (0:ℝ) ≤ (p:ℝ) := Nat.cast_nonneg p
    have h1 : ‖f p * star (g p)‖ ≤ 1 := by
      rw [norm_mul, norm_star]
      calc ‖f p‖ * ‖g p‖ ≤ 1 * 1 := mul_le_mul (hf p) (hg p) (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    have h2 : (f p * star (g p)).re ≤ 1 := by
      have := Complex.re_le_norm (f p * star (g p)); linarith
    exact div_nonneg (by linarith) hpR
  unfold BoundedMultiplicativeFunctions.𝔻
  apply Real.rpow_le_rpow _ _ (by norm_num)
  · exact Finset.sum_nonneg (fun p _ => key p)
  · exact Finset.sum_le_sum_of_subset_of_nonneg
      (Nat.primesLE_mono (Nat.floor_mono hXY)) (fun p _ _ => key p)

theorem one_add_mul_exp_neg_antitone {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (1 + b) * Real.exp (-b) ≤ (1 + a) * Real.exp (-a) := by
  have ha1 : 0 < 1 + a := by linarith
  have hkey : (1 + b) / (1 + a) ≤ Real.exp (b - a) := by
    have h1 : 1 + (b - a) / (1 + a) ≤ Real.exp ((b - a) / (1 + a)) := by
      have := Real.add_one_le_exp ((b - a) / (1 + a)); linarith
    have h2 : (1 + b) / (1 + a) = 1 + (b - a) / (1 + a) := by field_simp; ring
    have h3 : (b - a) / (1 + a) ≤ b - a := by
      rw [div_le_iff₀ ha1]; nlinarith
    have h4 : Real.exp ((b - a) / (1 + a)) ≤ Real.exp (b - a) := Real.exp_le_exp.mpr h3
    linarith
  have hstep : (1 + b) ≤ (1 + a) * Real.exp (b - a) := by
    rw [div_le_iff₀ ha1] at hkey; linarith
  calc (1 + b) * Real.exp (-b) ≤ (1 + a) * Real.exp (b - a) * Real.exp (-b) :=
        mul_le_mul_of_nonneg_right hstep (Real.exp_nonneg _)
    _ = (1 + a) * Real.exp (-a) := by
        rw [mul_assoc, ← Real.exp_add, show b - a + -b = -a by ring]

theorem nat_cpow_I_norm_le_one (n : ℕ) (u : ℝ) : ‖(n : ℂ) ^ (Complex.I * (u : ℂ))‖ ≤ 1 := by
  rcases eq_or_ne n 0 with hn | hn
  · subst hn
    rw [show (((0 : ℕ)) : ℂ) = 0 by norm_num]
    rcases eq_or_ne u 0 with hu | hu
    · subst hu; simp
    · rw [Complex.zero_cpow (x := Complex.I * (u : ℂ))]
      · simp
      · exact mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hu)
  · have hpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have h1 : ((n:ℂ)) = (((n:ℝ)):ℂ) := by simp
    rw [h1, norm_cpow_I_eq_one u (n:ℝ) hpos]

theorem sum_natIcc_norm_le (g : ℕ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1) {Y : ℝ} (hY : 1 ≤ Y) :
    ‖∑ n ∈ natIcc Y (2*Y), g n‖ ≤
      ‖∑ n ∈ Finset.Icc 1 ⌊2*Y⌋₊, g n‖ + ‖∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, g n‖ + 1 := by
  set a : ℕ := ⌈Y⌉₊ with hadef
  set b : ℕ := ⌊2*Y⌋₊ with hbdef
  set c : ℕ := ⌊Y⌋₊ with hcdef
  have hY0 : 0 < Y := by linarith
  have ha1 : 1 ≤ a := by rw [hadef]; exact Nat.one_le_ceil_iff.mpr hY0
  have hac : a ≤ c + 1 := by rw [hadef, hcdef]; exact Nat.ceil_le_floor_add_one Y
  have hca : c ≤ a := by rw [hadef, hcdef]; exact Nat.floor_le_ceil Y
  have hab : a ≤ b := by
    rw [hadef, hbdef]
    exact Nat.le_floor (by have := Nat.ceil_lt_add_one (show (0:ℝ) ≤ Y by linarith); linarith)
  have hac' : a - 1 ≤ c := by omega
  rw [show natIcc Y (2*Y) = Finset.Icc a b from rfl]
  have hsub : Finset.Icc a b ⊆ Finset.Icc 1 b := Finset.Icc_subset_Icc_left ha1
  have hsd := Finset.sum_sdiff (s₁ := Finset.Icc a b) (s₂ := Finset.Icc 1 b) (f := g) hsub
  have hcomp : Finset.Icc 1 b \ Finset.Icc a b = Finset.Icc 1 (a-1) := by
    ext n; simp only [Finset.mem_sdiff, Finset.mem_Icc]; omega
  rw [hcomp] at hsd
  have hA : (∑ n ∈ Finset.Icc 1 b, g n) - (∑ n ∈ Finset.Icc 1 (a-1), g n)
      = ∑ n ∈ Finset.Icc a b, g n := sub_eq_iff_eq_add'.mpr hsd.symm
  have hcorr : ‖∑ n ∈ Finset.Icc 1 (a-1), g n‖ ≤ ‖∑ n ∈ Finset.Icc 1 c, g n‖ + 1 := by
    have hsub2 : Finset.Icc 1 (a-1) ⊆ Finset.Icc 1 c := Finset.Icc_subset_Icc_right hac'
    have hsd2 := Finset.sum_sdiff (s₁ := Finset.Icc 1 (a-1)) (s₂ := Finset.Icc 1 c) (f := g) hsub2
    have hcard : (Finset.Icc 1 c \ Finset.Icc 1 (a-1)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro x hx y hy
      simp only [Finset.mem_sdiff, Finset.mem_Icc] at hx hy
      omega
    have hnorm : ‖∑ n ∈ Finset.Icc 1 c \ Finset.Icc 1 (a-1), g n‖ ≤ 1 := by
      calc ‖∑ n ∈ Finset.Icc 1 c \ Finset.Icc 1 (a-1), g n‖
          ≤ ∑ n ∈ Finset.Icc 1 c \ Finset.Icc 1 (a-1), ‖g n‖ := norm_sum_le _ _
        _ ≤ ∑ _n ∈ Finset.Icc 1 c \ Finset.Icc 1 (a-1), (1:ℝ) :=
            Finset.sum_le_sum (fun n _ => hg n)
        _ = ((Finset.Icc 1 c \ Finset.Icc 1 (a-1)).card : ℝ) := by simp
        _ ≤ 1 := by exact_mod_cast hcard
    have h2 : (∑ n ∈ Finset.Icc 1 (a-1), g n)
        = (∑ n ∈ Finset.Icc 1 c, g n) - (∑ n ∈ Finset.Icc 1 c \ Finset.Icc 1 (a-1), g n) :=
      eq_sub_iff_add_eq.mpr (by rw [add_comm]; exact hsd2)
    rw [h2]
    calc ‖(∑ n ∈ Finset.Icc 1 c, g n) - (∑ n ∈ Finset.Icc 1 c \ Finset.Icc 1 (a-1), g n)‖
        ≤ ‖∑ n ∈ Finset.Icc 1 c, g n‖ + ‖∑ n ∈ Finset.Icc 1 c \ Finset.Icc 1 (a-1), g n‖ :=
          norm_sub_le _ _
      _ ≤ ‖∑ n ∈ Finset.Icc 1 c, g n‖ + 1 := by linarith
  rw [← hA]
  calc ‖(∑ n ∈ Finset.Icc 1 b, g n) - (∑ n ∈ Finset.Icc 1 (a-1), g n)‖
      ≤ ‖∑ n ∈ Finset.Icc 1 b, g n‖ + ‖∑ n ∈ Finset.Icc 1 (a-1), g n‖ := norm_sub_le _ _
    _ ≤ ‖∑ n ∈ Finset.Icc 1 b, g n‖ + (‖∑ n ∈ Finset.Icc 1 c, g n‖ + 1) := by linarith
    _ = ‖∑ n ∈ Finset.Icc 1 (⌊2*Y⌋₊), g n‖ + ‖∑ n ∈ Finset.Icc 1 (⌊Y⌋₊), g n‖ + 1 := by
        rw [hbdef, hcdef]; ring

/-- Halász: under the pretentious-distance hypothesis the long average is small. -/
theorem halasz_long_avg (θ η : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hη : 0 < η) :
    ∃ B C X₀ : ℝ, 0 < B ∧ 0 < C ∧ 1 ≤ X₀ ∧
      ∀ (g : ℕ → ℂ), g 1 = 1 →
      (∀ m n : ℕ, m.Coprime n → g (m * n) = g m * g n) → (∀ n, ‖g n‖ ≤ 1) →
      ∀ (Y H : ℝ), X₀ ≤ Y → Y ^ θ ≤ H → H ≤ Y →
      (∀ u : ℝ, |u| ≤ C * Y / H → B ≤ 𝔻 g (fun n ↦ (n : ℂ) ^ (Complex.I * u)) Y) →
      ‖(1 / Y) * ∑ n ∈ natIcc Y (2 * Y), g n‖ ≤ η / 8 := by
  obtain ⟨CH, hCHpos, hHal⟩ := halasz_complex
  set δ : ℝ := η / (96 * CH) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have htend : Filter.Tendsto (fun t : ℝ => (1 + t) * Real.exp (-t)) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun t : ℝ => Real.exp (-t)) Filter.atTop (nhds 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero
    have h2 : Filter.Tendsto (fun t : ℝ => t * Real.exp (-t)) Filter.atTop (nhds 0) := by
      simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    have h3 : Filter.Tendsto (fun t : ℝ => (1:ℝ) * Real.exp (-t) + t * Real.exp (-t))
        Filter.atTop (nhds ((1:ℝ) * 0 + 0)) := (h1.const_mul (1:ℝ)).add h2
    simpa [add_mul, one_mul, add_comm, add_left_comm, add_assoc] using h3
  obtain ⟨B₁, hB₁ge, hB₁⟩ : ∃ B₁ : ℝ, 1 ≤ B₁ ∧ (1 + B₁) * Real.exp (-B₁) ≤ δ := by
    have hmem : Set.Iio δ ∈ nhds (0:ℝ) := isOpen_Iio.mem_nhds hδpos
    have hev : ∀ᶠ t in Filter.atTop, (1 + t) * Real.exp (-t) < δ := htend.eventually hmem
    obtain ⟨B₀, hB₀⟩ := Filter.eventually_atTop.1 hev
    exact ⟨max B₀ 1, le_max_right _ _, le_of_lt (hB₀ _ (le_max_left _ _))⟩
  have hBpos : 0 < B₁ := by linarith
  refine ⟨B₁, max 2 (2/δ^2), max 3 (16/η), hBpos, by positivity, ?_, ?_⟩
  · exact le_trans (by norm_num : (1:ℝ) ≤ 3) (le_max_left _ _)
  · intro g hg1 hgmul hgb Y H hY hYθ hHY hhyp
    set C : ℝ := max 2 (2/δ^2) with hCdef
    have hC2 : 2 ≤ C := le_max_left _ _
    have hCbig : 2/δ^2 ≤ C := le_max_right _ _
    have hCpos : 0 < C := by linarith
    have hY2 : 2 ≤ Y := le_trans (le_trans (by norm_num : (2:ℝ) ≤ 3) (le_max_left _ _)) hY
    have hY0 : 0 < Y := by linarith
    have hH0 : 0 < H := by
      have : (0:ℝ) < Y ^ θ := Real.rpow_pos_of_pos hY0 θ
      linarith
    have hHle : H ≤ Y := hHY
    set T : ℝ := C * Y / (2 * H) with hTdef
    have hT1 : 1 ≤ T := by
      rw [hTdef, le_div_iff₀ (by positivity : (0:ℝ) < 2*H)]
      nlinarith [hC2, hHle, hY0]
    have h2T : 2 * T = C * Y / H := by rw [hTdef]; ring
    have hsqT : 1 / δ^2 ≤ T := by
      have h1 : C/2 ≤ T := by
        rw [hTdef, le_div_iff₀ (by positivity : (0:ℝ) < 2*H)]
        nlinarith [hHle, hY0, hC2]
      have h2 : 1/δ^2 ≤ C/2 := by
        rw [le_div_iff₀ (show (0:ℝ) < 2 by norm_num), div_mul_eq_mul_div, one_mul]
        exact hCbig
      linarith
    have hBδ : (1 + B₁^2) * Real.exp (-(B₁^2)) ≤ δ :=
      le_trans (one_add_mul_exp_neg_antitone (by positivity) (by nlinarith [hB₁ge])) hB₁
    -- first Halász application, x = 2Y
    have hM1 : B₁^2 ≤ ⨅ (t : {t : ℝ // |t| ≤ 2 * T}),
        𝔻 g (fun n ↦ (n : ℂ) ^ (Complex.I * (t.1 : ℂ))) (2*Y) ^ 2 := by
      haveI : Nonempty {t : ℝ // |t| ≤ 2 * T} := ⟨⟨0, by simp; positivity⟩⟩
      apply le_ciInf
      intro t
      have ht : |t.1| ≤ C * Y / H := by rw [← h2T]; exact t.2
      have h1 : B₁ ≤ 𝔻 g (fun n ↦ (n : ℂ) ^ (Complex.I * (t.1 : ℂ))) Y := hhyp t.1 ht
      have h2 : 𝔻 g (fun n ↦ (n : ℂ) ^ (Complex.I * (t.1 : ℂ))) Y
          ≤ 𝔻 g (fun n ↦ (n : ℂ) ^ (Complex.I * (t.1 : ℂ))) (2*Y) :=
        dist_mono hgb (fun n => nat_cpow_I_norm_le_one n t.1) (by linarith)
      exact pow_le_pow_left₀ (le_of_lt hBpos) (le_trans h1 h2) 2
    have hb2 := hHal g hg1 hgmul hgb (2*Y) T (by linarith) hT1
    have hkey1 : (1 + ⨅ (t : {t : ℝ // |t| ≤ 2 * T}),
        𝔻 g (fun n ↦ (n : ℂ) ^ (Complex.I * (t.1 : ℂ))) (2*Y) ^ 2)
        * Real.exp (-(⨅ (t : {t : ℝ // |t| ≤ 2 * T}),
        𝔻 g (fun n ↦ (n : ℂ) ^ (Complex.I * (t.1 : ℂ))) (2*Y) ^ 2)) ≤ δ :=
      le_trans (one_add_mul_exp_neg_antitone (by positivity) hM1) hBδ
    have hsqrt1 : 1 / Real.sqrt T ≤ δ := by
      have h1 : Real.sqrt (1/δ^2) ≤ Real.sqrt T := Real.sqrt_le_sqrt hsqT
      have h2 : Real.sqrt (1/δ^2) = 1/δ := by
        rw [show (1/δ^2 : ℝ) = (1/δ)^2 by ring, Real.sqrt_sq (by positivity)]
      have h3 : 1/Real.sqrt T ≤ 1/Real.sqrt (1/δ^2) :=
        one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by positivity)) h1
      have h4 : 1/(1/δ) = δ := by field_simp
      calc 1/Real.sqrt T ≤ 1/Real.sqrt (1/δ^2) := h3
        _ = 1/(1/δ) := by rw [h2]
        _ = δ := h4
    have hb2' : ‖∑ n ∈ Finset.Icc 1 ⌊2*Y⌋₊, g n‖ ≤ CH * (2*Y) * (2*δ) := by
      refine le_trans hb2 ?_
      have h0 : (0:ℝ) ≤ CH * (2*Y) := by positivity
      apply mul_le_mul_of_nonneg_left _ h0
      linarith [hkey1, hsqrt1]
    -- second Halász application, x = Y
    have hM2 : B₁^2 ≤ ⨅ (t : {t : ℝ // |t| ≤ 2 * T}),
        𝔻 g (fun n ↦ (n : ℂ) ^ (Complex.I * (t.1 : ℂ))) Y ^ 2 := by
      haveI : Nonempty {t : ℝ // |t| ≤ 2 * T} := ⟨⟨0, by simp; positivity⟩⟩
      apply le_ciInf
      intro t
      have ht : |t.1| ≤ C * Y / H := by rw [← h2T]; exact t.2
      exact pow_le_pow_left₀ (le_of_lt hBpos) (hhyp t.1 ht) 2
    have hb3 := hHal g hg1 hgmul hgb Y T (by linarith) hT1
    have hkey2 : (1 + ⨅ (t : {t : ℝ // |t| ≤ 2 * T}),
        𝔻 g (fun n ↦ (n : ℂ) ^ (Complex.I * (t.1 : ℂ))) Y ^ 2)
        * Real.exp (-(⨅ (t : {t : ℝ // |t| ≤ 2 * T}),
        𝔻 g (fun n ↦ (n : ℂ) ^ (Complex.I * (t.1 : ℂ))) Y ^ 2)) ≤ δ :=
      le_trans (one_add_mul_exp_neg_antitone (by positivity) hM2) hBδ
    have hb3' : ‖∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, g n‖ ≤ CH * Y * (2*δ) := by
      refine le_trans hb3 ?_
      have h0 : (0:ℝ) ≤ CH * Y := by positivity
      apply mul_le_mul_of_nonneg_left _ h0
      linarith [hkey2, hsqrt1]
    -- combine
    have hY1 : 1 ≤ Y := by linarith
    have hsplit := sum_natIcc_norm_le g hgb hY1
    have hδeq : 6 * CH * δ = η / 16 := by
      rw [hδdef]; field_simp; ring
    have hYbig : 1 / Y ≤ η / 16 := by
      have h16 : 16 / η ≤ Y := le_trans (le_max_right _ _) hY
      rw [div_le_iff₀ hη] at h16
      rw [div_le_iff₀ hY0, div_mul_eq_mul_div, le_div_iff₀ (show (0:ℝ) < 16 by norm_num)]
      nlinarith [h16]
    have hfinal : ‖∑ n ∈ Finset.Icc 1 ⌊2*Y⌋₊, g n‖ + ‖∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, g n‖ + 1
        ≤ 6 * CH * Y * δ + 1 := by
      have h2 := hb2'; have h3 := hb3'
      have : CH * (2*Y) * (2*δ) + CH * Y * (2*δ) = 6 * CH * Y * δ := by ring
      linarith [h2, h3, this]
    have hbound : ‖∑ n ∈ natIcc Y (2*Y), g n‖ ≤ 6 * CH * Y * δ + 1 :=
      le_trans hsplit hfinal
    have hYpos : 0 < Y := hY0
    rw [norm_mul]
    have hcoef : ‖(1/Y : ℂ)‖ = 1/Y := by
      have h1 : Complex.normSq (1/Y : ℂ) = (1/Y) * (1/Y) := by
        rw [show (1/Y : ℂ) = ((1/Y : ℝ) : ℂ) by push_cast; ring]
        exact Complex.normSq_ofReal _
      have h1' : ‖(1/Y : ℂ)‖^2 = (1/Y) * (1/Y) := by
        rw [← Complex.normSq_eq_norm_sq]; exact h1
      rw [← Real.sqrt_sq (norm_nonneg (1/Y : ℂ)), h1',
        Real.sqrt_mul_self (by positivity : (0:ℝ) ≤ 1/Y)]
    rw [hcoef]
    calc (1/Y) * ‖∑ n ∈ natIcc Y (2*Y), g n‖ ≤ (1/Y) * (6 * CH * Y * δ + 1) :=
          mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = 6 * CH * δ + 1/Y := by field_simp
      _ = η/16 + 1/Y := by rw [hδeq]
      _ ≤ η/16 + η/16 := by linarith [hYbig]
      _ = η/8 := by ring


open MeasureTheory

/-- **Assembly.**  `mr_core_window` follows from the Matomäki–Radziwiłł short-vs-long `L²` input
(`Hcore`) and the Halász long-average bound (`halasz_long_avg`), by the pointwise inequality
`‖A‖² ≤ 2‖A - L‖² + 2‖L‖²`. -/
theorem mr_core_window_of_core (θ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (η : ℝ) (hη : 0 < η)
    (Hcore : ∀ ε : ℝ, 0 < ε → ∃ B C X₀ : ℝ, 0 < B ∧ 0 < C ∧ 1 ≤ X₀ ∧
      ∀ (g : ℕ → ℂ), g 1 = 1 →
      (∀ m n : ℕ, m.Coprime n → g (m * n) = g m * g n) → (∀ n, ‖g n‖ ≤ 1) →
      ∀ (Y H : ℝ), X₀ ≤ Y → Y ^ θ ≤ H → H ≤ Y →
      (∀ u : ℝ, |u| ≤ C * Y / H → B ≤ 𝔻 g (fun n ↦ (n : ℂ) ^ (Complex.I * u)) Y) →
        1 / Y * (∫ y in Y..(2 * Y), ‖(1 / H) * ∑ n ∈ natIcc y (y + H), g n
            - (1 / Y) * ∑ n ∈ natIcc Y (2 * Y), g n‖ ^ 2) ≤ ε) :
    ∃ B C X₀ : ℝ, 0 < B ∧ 0 < C ∧ 1 ≤ X₀ ∧
      ∀ (g : ℕ → ℂ), g 1 = 1 →
      (∀ m n : ℕ, m.Coprime n → g (m * n) = g m * g n) → (∀ n, ‖g n‖ ≤ 1) →
      ∀ (Y H : ℝ), X₀ ≤ Y → Y ^ θ ≤ H → H ≤ Y →
      (∀ u : ℝ, |u| ≤ C * Y / H → B ≤ 𝔻 g (fun n ↦ (n : ℂ) ^ (Complex.I * u)) Y) →
        1 / Y * (∫ y in Y..(2 * Y), ‖(1 / H) * ∑ n ∈ natIcc y (y + H), g n‖ ^ 2)
          ≤ η ^ 2 / 4 := by
  set ε : ℝ := η^2 / 16 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  obtain ⟨B₁, C₁, X₁, hB₁, hC₁, hX₁, hcore⟩ := Hcore ε hεpos
  obtain ⟨B₂, C₂, X₂, hB₂, hC₂, hX₂, hlong⟩ := halasz_long_avg θ η hθ₀ hθ₁ hη
  refine ⟨max B₁ B₂, max C₁ C₂, max 1 (max X₁ X₂), lt_max_of_lt_left hB₁,
    lt_max_of_lt_left hC₁, le_max_left _ _, ?_⟩
  intro g hg1 hgmul hgb Y H hY hYθ hHY hhyp
  have hY1 : 1 ≤ Y := le_trans (le_max_left _ _) hY
  have hY₁ : X₁ ≤ Y := le_trans (le_trans (le_max_left X₁ X₂) (le_max_right 1 (max X₁ X₂))) hY
  have hY₂ : X₂ ≤ Y := le_trans (le_trans (le_max_right X₁ X₂) (le_max_right 1 (max X₁ X₂))) hY
  have hYpos : 0 < Y := by linarith
  have hH1 : 1 ≤ H := by
    have h1 : (1:ℝ) ≤ Y ^ θ := Real.one_le_rpow hY1 (le_of_lt hθ₀)
    linarith
  have hHpos : 0 < H := by linarith
  -- hypotheses at the smaller constants
  have hhyp₁ : ∀ u : ℝ, |u| ≤ C₁ * Y / H →
      B₁ ≤ 𝔻 g (fun n ↦ (n : ℂ) ^ (Complex.I * u)) Y := by
    intro u hu
    have h1 : |u| ≤ max C₁ C₂ * Y / H := by
      have h2 : C₁ * Y / H ≤ max C₁ C₂ * Y / H :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) hYpos.le) hHpos.le
      linarith
    exact le_trans (le_max_left B₁ B₂) (hhyp u h1)
  have hhyp₂ : ∀ u : ℝ, |u| ≤ C₂ * Y / H →
      B₂ ≤ 𝔻 g (fun n ↦ (n : ℂ) ^ (Complex.I * u)) Y := by
    intro u hu
    have h1 : |u| ≤ max C₁ C₂ * Y / H := by
      have h2 : C₂ * Y / H ≤ max C₁ C₂ * Y / H :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) hYpos.le) hHpos.le
      linarith
    exact le_trans (le_max_right B₁ B₂) (hhyp u h1)
  have hcore' := hcore g hg1 hgmul hgb Y H hY₁ hYθ hHY hhyp₁
  have hlong' := hlong g hg1 hgmul hgb Y H hY₂ hYθ hHY hhyp₂
  -- abbreviations
  set L : ℂ := (1 / Y) * ∑ n ∈ natIcc Y (2 * Y), g n with hLdef
  set A : ℝ → ℂ := fun y => (1 / H) * ∑ n ∈ natIcc y (y + H), g n with hAdef
  have hAmeas : Measurable A := (measurable_window_sum g H).const_mul (1/H)
  have h1meas : Measurable (fun y : ℝ => ‖A y‖ ^ 2) := hAmeas.norm.pow_const 2
  have h2meas : Measurable (fun y : ℝ => ‖A y - L‖ ^ 2) := (hAmeas.sub_const L).norm.pow_const 2
  -- integrability
  have hy0_of : ∀ y ∈ Set.uIcc Y (2*Y), 0 ≤ y := by
    intro y hy
    rw [Set.uIcc_of_le (by linarith : Y ≤ 2*Y)] at hy
    linarith [hy.1]
  have hintA : IntervalIntegrable (fun y : ℝ => ‖A y‖ ^ 2) volume Y (2*Y) := by
    refine IntegrableOn.intervalIntegrable ?_
    refine IntegrableOn.of_bound isCompact_uIcc.measure_lt_top
      h1meas.aestronglyMeasurable.restrict 4 ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIcc] with y hy
    have hy0 : 0 ≤ y := hy0_of y hy
    have hb : ‖A y‖ ≤ 2 := norm_window_avg_le g hgb y H hy0 hH1
    rw [Real.norm_of_nonneg (by positivity)]
    nlinarith [hb, norm_nonneg (A y)]
  have hintB : IntervalIntegrable (fun y : ℝ => ‖A y - L‖ ^ 2) volume Y (2*Y) := by
    refine IntegrableOn.intervalIntegrable ?_
    refine IntegrableOn.of_bound isCompact_uIcc.measure_lt_top
      h2meas.aestronglyMeasurable.restrict ((2 + ‖L‖)^2) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIcc] with y hy
    have hy0 : 0 ≤ y := hy0_of y hy
    have hb : ‖A y‖ ≤ 2 := norm_window_avg_le g hgb y H hy0 hH1
    have h2 : ‖A y - L‖ ≤ 2 + ‖L‖ := by
      have := norm_sub_le (A y) L; linarith [hb]
    rw [Real.norm_of_nonneg (by positivity)]
    nlinarith [h2, norm_nonneg (A y - L), norm_nonneg L]
  have hintR : IntervalIntegrable (fun y : ℝ => 2 * ‖A y - L‖ ^ 2 + 2 * ‖L‖ ^ 2) volume Y (2*Y) :=
    (hintB.const_mul 2).add (intervalIntegrable_const.const_mul 2)
  -- pointwise estimate
  have hpt : ∀ y ∈ Set.Icc Y (2*Y), ‖A y‖ ^ 2 ≤ 2 * ‖A y - L‖ ^ 2 + 2 * ‖L‖ ^ 2 := by
    intro y _
    have h1 : ‖A y‖ ≤ ‖A y - L‖ + ‖L‖ := by
      have := norm_add_le (A y - L) L
      rwa [sub_add_cancel] at this
    nlinarith [h1, norm_nonneg (A y), norm_nonneg (A y - L), norm_nonneg L,
      sq_nonneg (‖A y - L‖ - ‖L‖)]
  have hmono := intervalIntegral.integral_mono_on (show Y ≤ 2*Y by linarith) hintA hintR hpt
  have hsplit : ∫ y in Y..(2*Y), (2 * ‖A y - L‖ ^ 2 + 2 * ‖L‖ ^ 2)
      = 2 * (∫ y in Y..(2*Y), ‖A y - L‖ ^ 2) + 2 * ‖L‖ ^ 2 * (2*Y - Y) := by
    rw [intervalIntegral.integral_add (hintB.const_mul 2) (intervalIntegrable_const.const_mul 2),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const]
    simp only [smul_eq_mul]; ring
  have hLle : ‖L‖ ≤ η / 8 := hlong'
  have hcore'' : 1 / Y * (∫ y in Y..(2*Y), ‖A y - L‖ ^ 2) ≤ ε := hcore'
  calc 1 / Y * (∫ y in Y..(2*Y), ‖A y‖ ^ 2)
      ≤ 1 / Y * (2 * (∫ y in Y..(2*Y), ‖A y - L‖ ^ 2) + 2 * ‖L‖ ^ 2 * (2*Y - Y)) :=
        mul_le_mul_of_nonneg_left (le_trans hmono (le_of_eq hsplit)) (by positivity)
    _ = 2 * (1 / Y * (∫ y in Y..(2*Y), ‖A y - L‖ ^ 2)) + 2 * ‖L‖ ^ 2 := by
        field_simp; ring
    _ ≤ 2 * ε + 2 * (η/8)^2 := by
        have h2 : ‖L‖ ^ 2 ≤ (η/8)^2 := pow_le_pow_left₀ (norm_nonneg L) hLle 2
        linarith [hcore'']
    _ ≤ η ^ 2 / 4 := by rw [hεdef]; nlinarith [sq_nonneg η]




open MeasureTheory in
/-- Nested-interval monotonicity for a nonnegative integrand. -/
lemma integral_symm_le {f : ℝ → ℝ} {a : ℝ} (ha : 0 ≤ a) (hnn : ∀ t, 0 ≤ f t)
    (hF : IntervalIntegrable f volume (-(2*a)) (2*a)) :
    (∫ t in (-a)..a, f t) ≤ ∫ t in (-(2*a))..(2*a), f t :=
  intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
    (Filter.Eventually.of_forall hnn) hF

/-- The uniform Dirichlet-polynomial mean-square input (Matomäki–Radziwiłł's "far region"),
isolated as a hypothesis: for every `ε > 0` there are `B, C, X₀` such that, under the pretentious
hypothesis, `(Y/H)/T · ∫_{-2T}^{2T} ‖Σ_{Y ≤ n ≤ 3Y} g n · n^{-1-it}‖² ≤ ε` for every `T ≥ Y/H`. -/
def DirichletMeanSqInput (θ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ B C X₀ : ℝ, 0 < B ∧ 0 < C ∧ 1 ≤ X₀ ∧
    ∀ (g : ℕ → ℂ), g 1 = 1 →
    (∀ m n : ℕ, m.Coprime n → g (m * n) = g m * g n) → (∀ n, ‖g n‖ ≤ 1) →
    ∀ (Y H : ℝ), X₀ ≤ Y → Y ^ θ ≤ H → H ≤ Y →
    (∀ u : ℝ, |u| ≤ C * Y / H →
      B ≤ BoundedMultiplicativeFunctions.𝔻 g (fun n ↦ (n : ℂ) ^ (Complex.I * u)) Y) →
    ∀ T : ℝ, Y/H ≤ T →
      (Y/H)/T * (∫ t in -(2*T)..(2*T),
        ‖∑ n ∈ Work.BMF.natIcc Y (3*Y), g n * (n:ℂ)^(-(1 + Complex.I*t))‖^2) ≤ ε

/-- **Assembly of `mr_core_window`** from the Parseval bound (`mr_parseval_direct`), the Halász
long-average bound (`halasz_long_avg`) and the Dirichlet-polynomial mean-square input `HDir`. -/
theorem mr_core_window_of_pieces (θ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (η : ℝ) (hη : 0 < η)
    (HDir : DirichletMeanSqInput θ) :
    ∃ B C X₀ : ℝ, 0 < B ∧ 0 < C ∧ 1 ≤ X₀ ∧
      ∀ (g : ℕ → ℂ), g 1 = 1 →
      (∀ m n : ℕ, m.Coprime n → g (m * n) = g m * g n) → (∀ n, ‖g n‖ ≤ 1) →
      ∀ (Y H : ℝ), X₀ ≤ Y → Y ^ θ ≤ H → H ≤ Y →
      (∀ u : ℝ, |u| ≤ C * Y / H →
        B ≤ BoundedMultiplicativeFunctions.𝔻 g (fun n ↦ (n : ℂ) ^ (Complex.I * u)) Y) →
        1 / Y * (∫ y in Y..(2 * Y), ‖(1 / H) * ∑ n ∈ Work.BMF.natIcc y (y + H), g n‖ ^ 2)
          ≤ η ^ 2 / 4 := by
  obtain ⟨C₀, hC₀pos, hpar⟩ := mr_parseval_direct
  set δ : ℝ := η^2 / (64 * C₀) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  obtain ⟨B_d, C_d, X_d, hB_d, hC_d, hX_d, hdir⟩ := HDir δ hδpos
  obtain ⟨B_h, C_h, X_h, hB_h, hC_h, hX_h, hhal⟩ :=
    halasz_long_avg θ (η / Real.sqrt C₀) hθ₀ hθ₁ (by positivity)
  set X_log : ℝ := Real.exp (δ ^ (-(15/2 : ℝ))) with hXldef
  have hXl1 : 1 ≤ X_log := by rw [hXldef]; exact Real.one_le_exp (by positivity)
  refine ⟨max B_d B_h, max C_d C_h, max 4 (max X_d (max X_h X_log)),
    lt_max_of_lt_left hB_d, lt_max_of_lt_left hC_d,
    le_trans (by norm_num : (1:ℝ) ≤ 4) (le_max_left _ _), ?_⟩
  intro g hg1 hgmul hgb Y H hY hYθ hHY hhyp
  have hY4 : 4 ≤ Y := le_trans (le_max_left _ _) hY
  have hYpos : 0 < Y := by linarith
  have hY1 : 1 ≤ Y := by linarith
  have hY_d : X_d ≤ Y := le_trans (le_trans (le_max_left X_d (max X_h X_log))
    (le_max_right 4 (max X_d (max X_h X_log)))) hY
  have hY_h : X_h ≤ Y := le_trans (le_trans (le_max_left X_h X_log)
    (le_trans (le_max_right X_d (max X_h X_log)) (le_max_right 4 (max X_d (max X_h X_log))))) hY
  have hY_log : X_log ≤ Y := le_trans (le_trans (le_max_right X_h X_log)
    (le_trans (le_max_right X_d (max X_h X_log)) (le_max_right 4 (max X_d (max X_h X_log))))) hY
  have hH1 : 1 ≤ H := by
    have h1 : (1:ℝ) ≤ Y ^ θ := Real.one_le_rpow hY1 (le_of_lt hθ₀)
    linarith
  have hhyp_d : ∀ u : ℝ, |u| ≤ C_d * Y / H →
      B_d ≤ 𝔻 g (fun n ↦ (n : ℂ) ^ (Complex.I * u)) Y := by
    intro u hu
    have h2 : C_d * Y / H ≤ max C_d C_h * Y / H :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (le_of_lt hYpos))
        (by linarith : (0:ℝ) ≤ H)
    exact le_trans (le_max_left B_d B_h) (hhyp u (le_trans hu h2))
  have hhyp_h : ∀ u : ℝ, |u| ≤ C_h * Y / H →
      B_h ≤ 𝔻 g (fun n ↦ (n : ℂ) ^ (Complex.I * u)) Y := by
    intro u hu
    have h2 : C_h * Y / H ≤ max C_d C_h * Y / H :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) (le_of_lt hYpos))
        (by linarith : (0:ℝ) ≤ H)
    exact le_trans (le_max_right B_d B_h) (hhyp u (le_trans hu h2))
  have hpar' := hpar g hgb Y H hY4 hH1 hHY
  have hhal' := hhal g hg1 hgmul hgb Y H hY_h hYθ hHY hhyp_h
  set F : ℝ → ℝ := fun t => ‖∑ n ∈ Work.BMF.natIcc Y (3 * Y),
      g n * (n:ℂ)^(-(1 + Complex.I * (t:ℂ)))‖^2 with hFdef
  have hFnn : ∀ t, 0 ≤ F t := by intro t; rw [hFdef]; positivity
  have hcont : Continuous (fun t : ℝ => ‖∑ n ∈ Work.BMF.natIcc Y (3 * Y),
      g n * (n:ℂ)^(-(1 + Complex.I * (t:ℂ)))‖^2) := by
    have hbase : Continuous (fun t : ℝ => ‖∑ n ∈ Work.BMF.natIcc Y (3 * Y),
        g n * (n:ℂ)^(-(1 + Complex.I * (t:ℂ)))‖) := by
      apply Continuous.norm
      apply continuous_finsetSum
      intro n _
      exact continuous_const.mul ((by fun_prop : Continuous fun t : ℝ => -(1 + Complex.I * (t:ℂ))).const_cpow
        (Or.inr (fun t => by intro h; have := congrArg Complex.re h; simp at this)))
    exact hbase.pow 2
  have hFint : IntervalIntegrable F volume (-(2*(Y/H))) (2*(Y/H)) := by
    rw [hFdef]
    exact hcont.intervalIntegrable _ _
  have hYHpos : 0 < Y/H := div_pos hYpos (by linarith)
  have hdirYH := hdir g hg1 hgmul hgb Y H hY_d hYθ hHY hhyp_d (Y/H) le_rfl
  rw [div_self (ne_of_gt hYHpos), one_mul] at hdirYH
  have hD1 : (∫ t in (-(Y/H))..(Y/H), F t) ≤ δ :=
    le_trans (integral_symm_le (le_of_lt hYHpos) hFnn hFint) hdirYH
  have hD2 : (⨆ (T : {T : ℝ // Y/H ≤ T}), (Y/H)/T * ∫ t in -(2*T.1)..(2*T.1), F t) ≤ δ := by
    haveI : Nonempty {T : ℝ // Y/H ≤ T} := ⟨⟨Y/H, le_rfl⟩⟩
    apply ciSup_le
    intro T
    exact hdir g hg1 hgmul hgb Y H hY_d hYθ hHY hhyp_d T.1 T.2
  have hlog : (Real.log Y)^(-(2/15:ℝ)) ≤ δ := by
    have hLY : δ ^ (-(15/2:ℝ)) ≤ Real.log Y := by
      have h1 : Real.exp (δ ^ (-(15/2:ℝ))) ≤ Y := hY_log
      have h2 := Real.log_le_log (Real.exp_pos _) h1
      rwa [Real.log_exp] at h2
    have h2 : (δ ^ (-(15/2:ℝ)))^(2/15:ℝ) = δ⁻¹ := by
      rw [← Real.rpow_mul (le_of_lt hδpos)]
      rw [show (-(15/2:ℝ)) * (2/15:ℝ) = -1 by norm_num, Real.rpow_neg_one]
    have h3 : δ⁻¹ ≤ (Real.log Y)^(2/15:ℝ) := by
      have := Real.rpow_le_rpow (Real.rpow_nonneg (le_of_lt hδpos) _) hLY (by norm_num : (0:ℝ) ≤ 2/15)
      rwa [h2] at this
    have h4 : (Real.log Y)^(-(2/15:ℝ)) * (Real.log Y)^(2/15:ℝ) = 1 := by
      rw [← Real.rpow_add (Real.log_pos (x := Y) (by linarith [hY4])), show (-(2/15:ℝ)) + 2/15 = 0 by norm_num,
        Real.rpow_zero]
    have h5 : 1 ≤ δ * (Real.log Y)^(2/15:ℝ) := by
      have hh := mul_le_mul_of_nonneg_left h3 (le_of_lt hδpos)
      rwa [mul_inv_cancel₀ (ne_of_gt hδpos)] at hh
    calc (Real.log Y)^(-(2/15:ℝ)) = (Real.log Y)^(-(2/15:ℝ)) * 1 := (mul_one _).symm
      _ ≤ (Real.log Y)^(-(2/15:ℝ)) * (δ * (Real.log Y)^(2/15:ℝ)) :=
          mul_le_mul_of_nonneg_left h5 (Real.rpow_nonneg (Real.log_nonneg hY1) _)
      _ = δ := by
          rw [← mul_assoc, mul_comm ((Real.log Y)^(-(2/15:ℝ))) δ, mul_assoc, h4, mul_one]
  have hLA : ‖(1 / Y) * ∑ n ∈ Work.BMF.natIcc Y (2 * Y), g n‖ ^ 2 ≤ δ := by
    have h1 : ‖(1 / Y) * ∑ n ∈ Work.BMF.natIcc Y (2 * Y), g n‖
        ≤ (η / Real.sqrt C₀) / 8 := hhal'
    have h2 : ((η / Real.sqrt C₀) / 8)^2 = δ := by
      have hs : (Real.sqrt C₀)^2 = C₀ := Real.sq_sqrt (le_of_lt hC₀pos)
      rw [hδdef]
      have he : ((η / Real.sqrt C₀) / 8)^2 = η^2 / (64 * C₀) := by
        rw [div_pow, div_pow]
        rw [hs]
        ring
      rw [he]
    calc _ ≤ ((η / Real.sqrt C₀) / 8)^2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = δ := h2
  calc 1 / Y * (∫ y in Y..(2 * Y), ‖(1 / H) * ∑ n ∈ Work.BMF.natIcc y (y + H), g n‖ ^ 2)
      ≤ C₀ * (‖(1 / Y) * ∑ n ∈ Work.BMF.natIcc Y (2 * Y), g n‖ ^ 2
          + (Real.log Y) ^ (-(2/15:ℝ))
          + (∫ t in -(Y/H)..(Y/H), F t)
          + ⨆ (T : {T : ℝ // Y/H ≤ T}), (Y/H)/T * ∫ t in -(2*T.1)..(2*T.1), F t) := by
        rw [← hFdef]; exact hpar'
    _ ≤ C₀ * (δ + δ + δ + δ) :=
        mul_le_mul_of_nonneg_left (by linarith [hLA, hlog, hD1, hD2]) (le_of_lt hC₀pos)
    _ = η^2/16 := by rw [hδdef]; field_simp; ring
    _ ≤ η^2/4 := by nlinarith [sq_nonneg η]

/-- **N9-core (`k = 0`).** Non-pretentiousness at level `B` on every frequency `|u| ≤ C Y/H`
forces the short-interval mean square to be at most `η²/4`.

The proof is the two-step reduction: the long average `L = Y⁻¹ Σ_{Y ≤ n ≤ 2Y} g n` is small by
Halász (`halasz_long_avg`), and the centred mean square of the short averages is small by the
Matomäki–Radziwiłł short-vs-long input; the pointwise inequality
`‖A‖² ≤ 2‖A - L‖² + 2‖L‖²` then finishes.  The assembly is `mr_core_window_of_core`. -/
theorem mr_core_window (θ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (η : ℝ) (hη : 0 < η) :
    ∃ B C X₀ : ℝ, 0 < B ∧ 0 < C ∧ 1 ≤ X₀ ∧
      ∀ (g : ℕ → ℂ), g 1 = 1 →
      (∀ m n : ℕ, m.Coprime n → g (m * n) = g m * g n) → (∀ n, ‖g n‖ ≤ 1) →
      ∀ (Y H : ℝ), X₀ ≤ Y → Y ^ θ ≤ H → H ≤ Y →
      (∀ u : ℝ, |u| ≤ C * Y / H →
        B ≤ BoundedMultiplicativeFunctions.𝔻 g (fun n ↦ (n : ℂ) ^ (Complex.I * u)) Y) →
        1 / Y * (∫ y in Y..(2 * Y), ‖(1 / H) * ∑ n ∈ Work.BMF.natIcc y (y + H), g n‖ ^ 2)
          ≤ η ^ 2 / 4 := by
  exact mr_core_window_of_pieces θ hθ₀ hθ₁ η hη (mr_dirichlet_L2_sup θ hθ₀ hθ₁)

end Work.BMF
