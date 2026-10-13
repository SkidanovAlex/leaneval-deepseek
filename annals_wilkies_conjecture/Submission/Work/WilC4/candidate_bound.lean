import Mathlib
import Submission.Work.WilC4.ErealDefs
import Submission.Work.WilC4.ProfileDefs
import Submission.Work.WilC4.ulpm_mono_param
import Submission.Work.WilC4.cand_mono_of_between
import Submission.Work.WilC4.cand_slack
import Submission.Work.WilC4.cand_base

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG
open Work.WilC4.Route (Gr valY eq_valY)

variable {k : ℕ}

/-! ## Elementary helpers -/

lemma exists_finset_of_encard_le {S : Set ℝ} {N : ℕ} (h : S.encard ≤ (N : ENat)) :
    ∃ B : Finset ℝ, (∀ x, x ∈ B ↔ x ∈ S) ∧ B.card ≤ N := by
  rw [Set.encard_le_coe_iff] at h
  obtain ⟨hfin, n₀, hn₀, hle⟩ := h
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · intro x; simp [Set.Finite.mem_toFinset]
  · have h1 : S.encard = (hfin.toFinset.card : ENat) := hfin.encard_eq_coe_toFinset_card
    rw [h1] at hn₀
    have h2 : hfin.toFinset.card = n₀ := Nat.cast_inj.mp hn₀
    omega

lemma mem_image_div {x : ℝ} (hx : x ≠ 0) {B : Finset ℝ} {z : ℝ} (hz : z ∈ B) :
    z / x ∈ B.image (fun w => w / x) := by
  rw [Finset.mem_image]
  exact ⟨z, hz, rfl⟩

lemma deep_mem_Ioo {β x s : ℝ} (hβ : 1 ≤ β) (hx : 0 < x) (hs : s ∈ Set.Icc 1 β) :
    x * s ∈ Set.Ioo (x / (2 * β)) (2 * β * x) := by
  have hβ0 : 0 < β := lt_of_lt_of_le one_pos hβ
  constructor
  · have h2 : x / (2 * β) < x := by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    nlinarith [hs.1, hx, h2]
  · have h2 : x * β < 2 * β * x := by nlinarith
    nlinarith [hs.2, hx, h2]

lemma rpow_two_pow' (j : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    ((2 : ℝ) ^ j) ^ (Real.logb 2 ρ) = ρ ^ j := by
  have h2nn : (0 : ℝ) ≤ 2 := by norm_num
  have hmain : ((2 : ℝ) ^ (Real.logb 2 ρ)) = ρ :=
    Real.rpow_logb (by norm_num) (by norm_num) hρ
  calc ((2 : ℝ) ^ j) ^ (Real.logb 2 ρ)
      = ((2 : ℝ) ^ ((j : ℝ))) ^ (Real.logb 2 ρ) := by rw [Real.rpow_natCast]
    _ = (2 : ℝ) ^ ((j : ℝ) * (Real.logb 2 ρ)) :=
        (Real.rpow_mul h2nn (j : ℝ) (Real.logb 2 ρ)).symm
    _ = (2 : ℝ) ^ ((Real.logb 2 ρ) * (j : ℝ)) := by rw [mul_comm]
    _ = ((2 : ℝ) ^ (Real.logb 2 ρ)) ^ ((j : ℝ)) :=
        Real.rpow_mul h2nn (Real.logb 2 ρ) (j : ℝ)
    _ = ρ ^ ((j : ℝ)) := by rw [hmain]
    _ = ρ ^ j := by rw [Real.rpow_natCast]

/-- Comparison of `ρ ^ j` with `β ^ (logb 2 ρ)` when `2 ^ j ≤ β ≤ 2 ^ (j+1)`. -/
lemma rho_pow_le {ρ β : ℝ} (hρ : 0 < ρ) {j : ℕ}
    (hl : (2 : ℝ) ^ j ≤ β) (hr : β ≤ (2 : ℝ) ^ (j + 1)) :
    min 1 ρ⁻¹ * β ^ (Real.logb 2 ρ) ≤ ρ ^ j ∧
      ρ ^ j ≤ max 1 ρ⁻¹ * β ^ (Real.logb 2 ρ) := by
  set σ : ℝ := Real.logb 2 ρ with hσ
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hβ0 : 0 < β := lt_of_lt_of_le (by positivity : (0:ℝ) < 2^j) hl
  have h2j : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  have e1 : ((2 : ℝ) ^ j) ^ σ = ρ ^ j := rpow_two_pow' j hρ
  have e2 : ((2 : ℝ) ^ (j+1)) ^ σ = ρ ^ (j+1) := rpow_two_pow' (j+1) hρ
  have hβσ : 0 ≤ β ^ σ := Real.rpow_nonneg hβ0.le _
  rcases le_or_gt 1 ρ with hρ1 | hρ1
  · have hσ0 : 0 ≤ σ := by rw [hσ]; exact Real.logb_nonneg (by norm_num) hρ1
    have hle1 : ρ ^ j ≤ β ^ σ := by
      rw [← e1]; exact Real.rpow_le_rpow h2j.le hl hσ0
    have hle2 : β ^ σ ≤ ρ ^ (j+1) := by
      rw [← e2]; exact Real.rpow_le_rpow hβ0.le hr hσ0
    constructor
    · have h1 : min 1 ρ⁻¹ * β^σ ≤ ρ⁻¹ * β^σ :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hβσ
      have h2 : ρ⁻¹ * β^σ ≤ ρ⁻¹ * ρ^(j+1) :=
        mul_le_mul_of_nonneg_left hle2 (by positivity)
      have h3 : ρ⁻¹ * ρ^(j+1) = ρ^j := by rw [pow_succ]; field_simp
      linarith [h1, h2, h3.le, h3.ge]
    · have h2 : β^σ ≤ max 1 ρ⁻¹ * β^σ := by
        calc β^σ = 1 * β^σ := (one_mul _).symm
          _ ≤ max 1 ρ⁻¹ * β^σ :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) hβσ
      linarith [hle1, h2]
  · have hρ1' : ρ ≤ 1 := le_of_lt hρ1
    have hσ0 : σ ≤ 0 := by
      rw [hσ]; exact le_of_lt (Real.logb_neg (by norm_num) hρ (by simpa using hρ1))
    have hle1 : β ^ σ ≤ ρ ^ j := by
      rw [← e1]; exact Real.rpow_le_rpow_of_nonpos h2j hl hσ0
    have hle2 : ρ ^ (j+1) ≤ β ^ σ := by
      rw [← e2]; exact Real.rpow_le_rpow_of_nonpos hβ0 hr hσ0
    constructor
    · have h1 : min 1 ρ⁻¹ * β^σ ≤ 1 * β^σ :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) hβσ
      rw [one_mul] at h1
      linarith [hle1, h1]
    · have hρinv : ρ⁻¹ ≥ 1 := (one_le_inv₀ hρ).mpr hρ1'
      have hmax : max 1 ρ⁻¹ = ρ⁻¹ := le_antisymm (max_le hρinv le_rfl) (le_max_right _ _)
      rw [hmax, mul_comm]
      have h2 : ρ^j * ρ ≤ β^σ := by rw [← pow_succ]; exact hle2
      have h3 : ρ^j * ρ * ρ⁻¹ ≤ β^σ * ρ⁻¹ :=
        mul_le_mul_of_nonneg_right h2 (by positivity : (0:ℝ) ≤ ρ⁻¹)
      have h4 : ρ^j * ρ * ρ⁻¹ = ρ^j := by field_simp
      linarith [h3, h4.le, h4.ge]

/-- `a ^ j ≤ a ^ e` for `a ≥ 1` and `j ≤ e`. -/
lemma pow_le_rpow_of_one_le {a : ℝ} (ha : 1 ≤ a) (j : ℕ) {e : ℝ} (hje : (j : ℝ) ≤ e) :
    a ^ j ≤ a ^ e := by
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le ha hje

/-- `a ^ e ≤ a ^ j` for `0 < a ≤ 1` and `j ≤ e`. -/
lemma rpow_le_pow_of_le_one {a : ℝ} (ha0 : 0 < a) (ha : a ≤ 1) (j : ℕ) {e : ℝ}
    (hje : (j : ℝ) ≤ e) : a ^ e ≤ a ^ j := by
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_ge ha0 ha hje

lemma max_rho_ge_one {ρ : ℝ} (hρ : 0 < ρ) : 1 ≤ max ρ ρ⁻¹ := by
  rcases le_or_gt 1 ρ with h | h
  · exact le_trans h (le_max_left _ _)
  · exact le_trans ((one_le_inv₀ hρ).mpr (le_of_lt h)) (le_max_right _ _)

/-- `1 ≤ max ρ ρ⁻¹ * min 1 ρ⁻¹`. -/
lemma max_rho_mul_min_inv {ρ : ℝ} (hρ : 0 < ρ) : 1 ≤ max ρ ρ⁻¹ * min 1 ρ⁻¹ := by
  rcases le_or_gt 1 ρ with h | h
  · have h2 : max ρ ρ⁻¹ = ρ := max_eq_left (le_trans (inv_le_one_of_one_le₀ h) h)
    have h3 : min 1 ρ⁻¹ = ρ⁻¹ := min_eq_right (inv_le_one_of_one_le₀ h)
    rw [h2, h3, mul_inv_cancel₀ (ne_of_gt hρ)]
  · have hρ1 : ρ ≤ 1 := le_of_lt h
    have h2 : max ρ ρ⁻¹ = ρ⁻¹ :=
      max_eq_right (le_trans hρ1 ((one_le_inv₀ hρ).mpr hρ1))
    have h3 : min 1 ρ⁻¹ = 1 := min_eq_left ((one_le_inv₀ hρ).mpr hρ1)
    rw [h2, h3, mul_one]
    exact (one_le_inv₀ hρ).mpr hρ1

/-- `1 / β ≤ ρ / 2` when `2 / ρ ≤ β`. -/
lemma inv_beta_le_half {ρ β : ℝ} (hρ : 0 < ρ) (hβ0 : 0 < β) (h : 2 / ρ ≤ β) :
    1 / β ≤ ρ / 2 := by
  have h2 : 2 ≤ β * ρ := (div_le_iff₀ hρ).mp h
  rw [div_le_div_iff₀ hβ0 (by norm_num : (0:ℝ) < 2)]
  linarith

/-- The upper coefficient fits in the constant. -/
lemma cand_C_up (P : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    max 1 ρ⁻¹ * (2 * (2 ^ (2 * P + 1) * max ρ ρ⁻¹)) ≤
      max 1 ((2 : ℝ) ^ (2 * P + 2) * (max ρ ρ⁻¹) ^ 2) := by
  refine le_trans ?_ (le_max_right _ _)
  have hM1 : 1 ≤ max ρ ρ⁻¹ := max_rho_ge_one hρ
  have hle : max 1 ρ⁻¹ ≤ max ρ ρ⁻¹ := max_le hM1 (le_max_right _ _)
  have hkey : (2 : ℝ) ^ (2 * P + 2) = 2 * (2 : ℝ) ^ (2 * P + 1) := by
    rw [show 2 * P + 2 = 2 * P + 1 + 1 from by ring, pow_succ]; ring
  calc max 1 ρ⁻¹ * (2 * (2 ^ (2 * P + 1) * max ρ ρ⁻¹))
      ≤ max ρ ρ⁻¹ * (2 * (2 ^ (2 * P + 1) * max ρ ρ⁻¹)) := by
        apply mul_le_mul_of_nonneg_right hle; positivity
    _ = (2 : ℝ) ^ (2 * P + 2) * (max ρ ρ⁻¹) ^ 2 := by rw [hkey]; ring

/-- The lower coefficient fits in the constant. -/
lemma cand_C_lo (P : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    (max 1 ((2 : ℝ) ^ (2 * P + 2) * (max ρ ρ⁻¹) ^ 2))⁻¹ ≤
      min 1 ρ⁻¹ * (1 / 2) * (2 ^ (2 * P + 1) * max ρ ρ⁻¹)⁻¹ := by
  have hM1 : 1 ≤ max ρ ρ⁻¹ := max_rho_ge_one hρ
  have hminpos : 0 < min 1 ρ⁻¹ := lt_min one_pos (inv_pos.mpr hρ)
  have hCcpos : 0 < max 1 ((2 : ℝ) ^ (2 * P + 2) * (max ρ ρ⁻¹) ^ 2) := by positivity
  have hApos : 0 < (2 : ℝ) ^ (2 * P + 2) * (max ρ ρ⁻¹) ^ 2 := by positivity
  have hXnn : 0 ≤ min 1 ρ⁻¹ * (1 / 2) * (2 ^ (2 * P + 1) * max ρ ρ⁻¹)⁻¹ :=
    mul_nonneg (mul_nonneg hminpos.le (by norm_num)) (by positivity)
  have hbase : (2 : ℝ) ^ (2 * P + 2) * (max ρ ρ⁻¹) ^ 2 *
      (min 1 ρ⁻¹ * (1 / 2) * (2 ^ (2 * P + 1) * max ρ ρ⁻¹)⁻¹)
      = max ρ ρ⁻¹ * min 1 ρ⁻¹ := by
    have hne : (2 ^ (2 * P + 1) * max ρ ρ⁻¹) ≠ 0 := by positivity
    field_simp
    ring
  have h1 : (max 1 ((2 : ℝ) ^ (2 * P + 2) * (max ρ ρ⁻¹) ^ 2))⁻¹ ≤
      ((2 : ℝ) ^ (2 * P + 2) * (max ρ ρ⁻¹) ^ 2)⁻¹ :=
    (inv_le_inv₀ hCcpos hApos).mpr (le_max_right _ _)
  have h2 : ((2 : ℝ) ^ (2 * P + 2) * (max ρ ρ⁻¹) ^ 2)⁻¹ ≤
      min 1 ρ⁻¹ * (1 / 2) * (2 ^ (2 * P + 1) * max ρ ρ⁻¹)⁻¹ := by
    rw [inv_le_iff_one_le_mul₀ hApos]
    rw [show (min 1 ρ⁻¹ * (1 / 2) * (2 ^ (2 * P + 1) * max ρ ρ⁻¹)⁻¹) *
        ((2 : ℝ) ^ (2 * P + 2) * (max ρ ρ⁻¹) ^ 2) = max ρ ρ⁻¹ * min 1 ρ⁻¹ from by
      rw [mul_comm, hbase]]
    exact max_rho_mul_min_inv hρ
  exact le_trans h1 h2

theorem candidate_bound {k : ℕ} (hOM : WilkiesDesign.CG.OMinModels)
    (Y : Set (Fin (k + 2) → ℝ)) (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y)
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Work.WilC4.Route.Gr Y c x y → Work.WilC4.Route.Gr Y c x y' → y = y')
    (B₀ : Set (Fin (k + 1) → ℝ)) (hB₀ : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc B₀)
    (hgood : Work.WilC4.GoodFibre Y B₀)
    {ρ : ℝ} (hρ : ρ ∈ Work.WilC4.ClusterER Y B₀) (hρ0 : 0 < ρ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
      ∀ y ∈ Work.WilC4.Cand Y B₀ ρ β,
        C⁻¹ * β ^ (Real.logb 2 ρ) ≤ |y| ∧ |y| ≤ C * β ^ (Real.logb 2 ρ) := by
  obtain ⟨N, Bm, hBmdef, hBmcard, hmono3⟩ := ulpm_mono_param hOM Y hY hfun
  obtain ⟨Rsl, hRsl1, hRsl⟩ := cand_slack ρ hρ0
  set P : ℕ := N with hPdef
  set β₀ : ℝ := max 1 (max (2 / ρ) (max ((2 : ℝ) ^ (P + 1)) Rsl)) with hβ₀def
  refine ⟨max 1 ((2 : ℝ) ^ (2 * P + 2) * (max ρ ρ⁻¹) ^ 2), le_max_left _ _, β₀, ?_⟩
  intro β hβ y hy
  have h1b : 1 ≤ β₀ := by rw [hβ₀def]; exact le_max_left _ _
  have h2b : 2 / ρ ≤ β₀ := by
    rw [hβ₀def]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have h3b : (2 : ℝ) ^ (P + 1) ≤ β₀ := by
    rw [hβ₀def]
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have h4b : Rsl ≤ β₀ := by
    rw [hβ₀def]
    exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hβ1 : 1 ≤ β := le_trans h1b hβ
  have hβ2ρ : 2 / ρ ≤ β := le_trans h2b hβ
  have hβP : (2 : ℝ) ^ (P + 1) ≤ β := le_trans h3b hβ
  have hβRsl : Rsl ≤ β := le_trans h4b hβ
  have hβ0 : 0 < β := lt_of_lt_of_le one_pos hβ1
  obtain ⟨hsl1, hsl2, hsl3⟩ := hRsl β hβRsl
  -- the witness
  obtain ⟨c, x₀, hwit, u, v, hux, hvx, hyu⟩ := hy
  obtain ⟨hx₀, hdeep, hrat⟩ := hwit
  set G : ℝ → ℝ := fun s => |valY Y c (x₀ * s)| with hGdef
  have hmemD : ∀ s ∈ Set.Icc 1 β, x₀ * s ∈ Set.Ioo (x₀ / (2 * β)) (2 * β * x₀) :=
    fun s hs => deep_mem_Ioo hβ1 hx₀ hs
  have hgr : ∀ s ∈ Set.Icc 1 β, Gr Y c (x₀ * s) (valY Y c (x₀ * s)) :=
    fun s hs => (deep_val hgood hβ1 hx₀ hdeep (hmemD s hs)).1
  have hpos : ∀ s ∈ Set.Icc 1 β, 0 < G s := by
    intro s hs
    rw [hGdef]
    exact abs_pos.mpr (deep_val hgood hβ1 hx₀ hdeep (hmemD s hs)).2
  have hcont : ContinuousOn G (Set.Icc 1 β) := by
    rw [hGdef]
    have h1 : ContinuousOn (fun s => valY Y c (x₀ * s)) (Set.Icc 1 β) :=
      (deep_cont hgood hβ1 hx₀ hdeep).comp (continuousOn_id.const_mul x₀)
        (fun s hs => hmemD s hs)
    exact h1.abs
  -- the doubling ratio
  have hdoub : ∀ s ∈ Set.Icc 1 (β / 2), |G (2 * s) / G s - ρ| ≤ 1 / β := by
    intro s hs
    have hs1 : 1 ≤ s := hs.1
    have hs2 : s ≤ β / 2 := hs.2
    have hsI : s ∈ Set.Icc 1 β := ⟨hs1, by linarith⟩
    have h2sI : 2 * s ∈ Set.Icc 1 β := ⟨by linarith, by linarith⟩
    have ht1 : x₀ / β ≤ x₀ * s := by
      rw [div_le_iff₀ hβ0]
      have h1 : x₀ ≤ x₀ * s := by
        have := mul_le_mul_of_nonneg_left hs1 hx₀.le
        simpa using this
      have h2 : x₀ * s ≤ x₀ * s * β := by
        calc x₀ * s = x₀ * s * 1 := (mul_one _).symm
          _ ≤ x₀ * s * β := mul_le_mul_of_nonneg_left hβ1 (by positivity)
      linarith
    have ht2 : x₀ * s ≤ x₀ * β := mul_le_mul_of_nonneg_left (by linarith) hx₀.le
    have hV2 : valY Y c (x₀ * s) ≠ 0 := (deep_val hgood hβ1 hx₀ hdeep (hmemD s hsI)).2
    have hgr2 : Gr Y c (2 * (x₀ * s)) (valY Y c (2 * (x₀ * s))) := by
      have he : 2 * (x₀ * s) = x₀ * (2 * s) := by ring
      rw [he]; exact hgr (2 * s) h2sI
    have hr := hrat (x₀ * s) ht1 ht2 (valY Y c (x₀ * s)) (valY Y c (2 * (x₀ * s)))
      (hgr s hsI) hgr2 hV2
    have he : 2 * (x₀ * s) = x₀ * (2 * s) := by ring
    rw [he] at hr
    have hβρ : 1 / β ≤ ρ / 2 := inv_beta_le_half hρ0 hβ0 hβ2ρ
    have hVpos : 0 < valY Y c (x₀ * (2 * s)) / valY Y c (x₀ * s) := by
      have h := (abs_le.mp hr).1
      linarith
    rw [hGdef]
    rw [← abs_div, abs_of_pos hVpos]
    exact hr
  -- piecewise monotonicity from o-minimality
  have hPiece : PieceMonoOn G P β := by
    obtain ⟨Bf, hBfmem, hBfcard⟩ := exists_finset_of_encard_le (hBmcard c)
    have hx₀ne : x₀ ≠ 0 := ne_of_gt hx₀
    rw [hPdef]
    refine ⟨Bf.image (fun z => z / x₀), ?_, ?_⟩
    · exact le_trans Finset.card_image_le hBfcard
    · intro a b ha hb hab hfree
      have hsI : ∀ s ∈ Set.Ioo a b, s ∈ Set.Icc 1 β :=
        fun s hs => ⟨le_of_lt (lt_of_le_of_lt ha hs.1), le_of_lt (lt_of_lt_of_le hs.2 hb)⟩
      have htri : ∀ s₁ s₂ s₃ : ℝ, s₁ ∈ Set.Ioo a b → s₂ ∈ Set.Ioo a b →
          s₃ ∈ Set.Ioo a b → s₁ < s₂ → s₂ < s₃ →
          (valY Y c (x₀*s₁) ≤ valY Y c (x₀*s₂) ∧ valY Y c (x₀*s₂) ≤ valY Y c (x₀*s₃)) ∨
          (valY Y c (x₀*s₃) ≤ valY Y c (x₀*s₂) ∧ valY Y c (x₀*s₂) ≤ valY Y c (x₀*s₁)) := by
        intro s₁ s₂ s₃ h1 h2 h3 h12 h23
        have hbnd : ∀ z ∈ Set.Ioo (x₀*a) (x₀*b), Fin.cons z c ∉ Bm := by
          intro z hz
          have hzx : z / x₀ ∈ Set.Ioo a b := by
            constructor
            · rw [lt_div_iff₀ hx₀]; linarith [hz.1]
            · rw [div_lt_iff₀ hx₀]; nlinarith [hz.2]
          have h1 : z / x₀ ∉ Bf.image (fun w => w / x₀) := hfree _ hzx
          intro hzBm
          exact h1 (mem_image_div hx₀ne ((hBfmem z).mpr hzBm))
        have hxab : x₀ * a < x₀ * b := by nlinarith
        have hmem : ∀ s ∈ Set.Ioo a b, x₀*s ∈ Set.Ioo (x₀*a) (x₀*b) :=
          fun s hs => ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩
        exact hmono3 c (x₀*a) (x₀*b) hxab hbnd (x₀*s₁) (x₀*s₂) (x₀*s₃)
          (valY Y c (x₀*s₁)) (valY Y c (x₀*s₂)) (valY Y c (x₀*s₃))
          (hmem s₁ h1) (hmem s₂ h2) (hmem s₃ h3) (by nlinarith) (by nlinarith)
          (hgr s₁ (hsI s₁ h1)) (hgr s₂ (hsI s₂ h2)) (hgr s₃ (hsI s₃ h3))
      have hmonoVal := cand_mono_of_between hab htri
      set s₀ : ℝ := (a + b) / 2 with hs₀def
      have hs₀ : s₀ ∈ Set.Ioo a b := by rw [hs₀def]; constructor <;> linarith
      have hw₀ : valY Y c (x₀*s₀) ≠ 0 := (deep_val hgood hβ1 hx₀ hdeep (hmemD s₀ (hsI s₀ hs₀))).2
      have hsign : ∀ s ∈ Set.Ioo a b, 0 < valY Y c (x₀*s) * valY Y c (x₀*s₀) := by
        intro s hs
        exact deep_sign hgood hβ1 hx₀ hdeep (hmemD s (hsI s hs)) (hmemD s₀ (hsI s₀ hs₀))
          (hgr s (hsI s hs)) (hgr s₀ (hsI s₀ hs₀))
      rcases lt_or_gt_of_ne hw₀ with hneg | hpos₀
      · -- valY < 0 on (a,b)
        have hlt : ∀ s ∈ Set.Ioo a b, valY Y c (x₀*s) < 0 := by
          intro s hs
          have := hsign s hs
          nlinarith
        have heq : ∀ s ∈ Set.Ioo a b, G s = -(valY Y c (x₀*s)) := by
          intro s hs
          rw [hGdef]
          exact abs_of_neg (hlt s hs)
        rcases hmonoVal with hm | ha'
        · refine Or.inr fun s₁ hs₁ s₂ hs₂ hle => ?_
          have h := hm hs₁ hs₂ hle
          rw [heq s₁ hs₁, heq s₂ hs₂]; linarith
        · refine Or.inl fun s₁ hs₁ s₂ hs₂ hle => ?_
          have h := ha' hs₁ hs₂ hle
          rw [heq s₁ hs₁, heq s₂ hs₂]; linarith
      · -- valY > 0 on (a,b)
        have hgt : ∀ s ∈ Set.Ioo a b, 0 < valY Y c (x₀*s) := by
          intro s hs
          have := hsign s hs
          nlinarith
        have heq : ∀ s ∈ Set.Ioo a b, G s = valY Y c (x₀*s) := by
          intro s hs
          rw [hGdef]
          exact abs_of_pos (hgt s hs)
        rcases hmonoVal with hm | ha'
        · exact Or.inl (hm.congr (fun s hs => (heq s hs).symm))
        · exact Or.inr (ha'.congr (fun s hs => (heq s hs).symm))
  -- chain bound and base
  have hτ0 : 0 ≤ 1 / β := by positivity
  have h2ρβ : 2 ≤ ρ * β := by
    have h := (div_le_iff₀ hρ0).mp hβ2ρ
    linarith
  have hτρ : 2 * (1 / β) ≤ ρ := by
    rw [mul_one_div, div_le_iff₀ hβ0]; linarith
  have hbaset := cand_base P ρ (1 / β) β hρ0 hτ0 hτρ hβP G hcont hpos hPiece hdoub
  set j : ℕ := Nat.floor (Real.logb 2 β) with hjdef
  set t : ℝ := β / (2 : ℝ) ^ j with htdef
  have hlog0 : 0 ≤ Real.logb 2 β := Real.logb_nonneg (by norm_num : (1:ℝ) < 2) hβ1
  have ht1 : 1 ≤ t := by
    rw [htdef, le_div_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^j)]
    have h2' := (Real.le_logb_iff_rpow_le (by norm_num : (1:ℝ)<2) hβ0).mp (Nat.floor_le hlog0)
    rw [Real.rpow_natCast, ← hjdef] at h2'
    simpa using h2'
  have ht2 : t ≤ 2 := by
    rw [htdef, div_le_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^j)]
    have hj' : Real.logb 2 β < ((Nat.floor (Real.logb 2 β) + 1 : ℕ) : ℝ) := by
      have := Nat.lt_floor_add_one (Real.logb 2 β); push_cast; linarith
    have h2' := (Real.logb_lt_iff_lt_rpow (by norm_num : (1:ℝ)<2) hβ0).mp hj'
    rw [Real.rpow_natCast] at h2'
    calc β ≤ (2 : ℝ) ^ (Nat.floor (Real.logb 2 β) + 1) := le_of_lt h2'
      _ = 2 * (2 : ℝ) ^ j := by rw [hjdef, pow_succ]; ring
  have hβjt : (2 : ℝ) ^ j * t = β := by rw [htdef]; field_simp
  have htI : t ∈ Set.Icc 1 2 := ⟨ht1, ht2⟩
  have hchain := chain_bound G ρ (1 / β) β hτ0 (by linarith) hpos hdoub j t ht1 (le_of_eq hβjt)
  rw [hβjt] at hchain
  have hbt := hbaset t htI
  have hG1pos : 0 < G 1 := hpos 1 ⟨le_rfl, hβ1⟩
  have hGβpos : 0 < G β := hpos β ⟨hβ1, le_rfl⟩
  have h2jpos : 0 < (2 : ℝ) ^ j := by positivity
  have h2jle : (2 : ℝ) ^ j ≤ β := by
    calc (2 : ℝ) ^ j = (2 : ℝ) ^ j * 1 := (mul_one _).symm
      _ ≤ (2 : ℝ) ^ j * t := mul_le_mul_of_nonneg_left ht1 h2jpos.le
      _ = β := hβjt
  have hle2jp1 : β ≤ (2 : ℝ) ^ (j + 1) := by
    calc β = (2 : ℝ) ^ j * t := hβjt.symm
      _ ≤ (2 : ℝ) ^ j * 2 := mul_le_mul_of_nonneg_left ht2 h2jpos.le
      _ = (2 : ℝ) ^ (j + 1) := by rw [pow_succ]
  obtain ⟨hrho1, hrho2⟩ := rho_pow_le hρ0 h2jle hle2jp1
  have hjle : (j : ℝ) ≤ Real.logb 2 β := by simpa [hjdef] using Nat.floor_le hlog0
  have h1βρ : 1 / β ≤ ρ / 2 := inv_beta_le_half hρ0 hβ0 hβ2ρ
  have hslpos : 1 ≤ 1 + 1 / (β * ρ) := by
    have : 0 ≤ 1 / (β * ρ) := by positivity
    linarith
  have h4u : (1 + 1 / (β * ρ)) ^ j ≤ 2 :=
    le_trans (pow_le_rpow_of_one_le hslpos j hjle) hsl2
  have hbs1 : 0 < 1 - 1 / (β * ρ) := by
    have hpos : 0 < β * ρ := by positivity
    have hle : 1 / (β * ρ) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hpos (by norm_num : (0:ℝ) < 2)]
      have h2 : 2 ≤ β * ρ := (div_le_iff₀ hρ0).mp hβ2ρ
      linarith
    linarith
  have hbs2 : 1 - 1 / (β * ρ) ≤ 1 := by
    have : 0 ≤ 1 / (β * ρ) := by positivity
    linarith
  have h4l : (1 - 1 / (β * ρ)) ^ j ≥ 1 / 2 :=
    le_trans hsl3 (rpow_le_pow_of_le_one hbs1 hbs2 j hjle)
  have hsplitp : ρ + 1 / β = ρ * (1 + 1 / (β * ρ)) := by field_simp
  have hsplitm : ρ - 1 / β = ρ * (1 - 1 / (β * ρ)) := by field_simp
  have hβσnn : 0 ≤ β ^ (Real.logb 2 ρ) := Real.rpow_nonneg hβ0.le _
  have hρ1β : 0 < ρ - 1 / β := by linarith
  have hup1 : G β ≤ max 1 ρ⁻¹ * β ^ (Real.logb 2 ρ) * (2 * (2 ^ (2 * P + 1) * max ρ ρ⁻¹)) * G 1 := by
    have h1 : G β ≤ (ρ + 1/β)^j * G t := hchain.2
    have h2 : G t ≤ (2 ^ (2 * P + 1) * max ρ ρ⁻¹) * G 1 := hbt.1
    have h3 : (ρ + 1/β)^j = ρ^j * (1 + 1/(β*ρ))^j := by rw [hsplitp, mul_pow]
    have h5 : ρ^j ≤ max 1 ρ⁻¹ * β ^ (Real.logb 2 ρ) := hrho2
    have hKbG1 : 0 ≤ (2 ^ (2 * P + 1) * max ρ ρ⁻¹) * G 1 := by positivity
    have hstep1 := mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ (ρ + 1/β)^j)
    have hstep2 : (ρ + 1/β)^j * ((2 ^ (2 * P + 1) * max ρ ρ⁻¹) * G 1)
        = ρ^j * ((1 + 1/(β*ρ))^j * ((2 ^ (2 * P + 1) * max ρ ρ⁻¹) * G 1)) := by
      rw [h3]; ring
    have hstep3 : ρ^j * ((1 + 1/(β*ρ))^j * ((2 ^ (2 * P + 1) * max ρ ρ⁻¹) * G 1))
        ≤ (max 1 ρ⁻¹ * β ^ (Real.logb 2 ρ)) * (2 * ((2 ^ (2 * P + 1) * max ρ ρ⁻¹) * G 1)) :=
      mul_le_mul h5 (mul_le_mul_of_nonneg_right h4u hKbG1)
        (mul_nonneg (pow_nonneg (le_trans zero_le_one hslpos) j) hKbG1)
        (mul_nonneg (le_trans zero_le_one (le_max_left _ _)) hβσnn)
    calc G β ≤ (ρ + 1/β)^j * G t := h1
      _ ≤ (ρ + 1/β)^j * ((2 ^ (2 * P + 1) * max ρ ρ⁻¹) * G 1) := hstep1
      _ = ρ^j * ((1 + 1/(β*ρ))^j * ((2 ^ (2 * P + 1) * max ρ ρ⁻¹) * G 1)) := hstep2
      _ ≤ (max 1 ρ⁻¹ * β ^ (Real.logb 2 ρ)) * (2 * ((2 ^ (2 * P + 1) * max ρ ρ⁻¹) * G 1)) := hstep3
      _ = max 1 ρ⁻¹ * β ^ (Real.logb 2 ρ) * (2 * (2 ^ (2 * P + 1) * max ρ ρ⁻¹)) * G 1 := by ring
  have hlo1 : min 1 ρ⁻¹ * β ^ (Real.logb 2 ρ) * (1/2) * (2 ^ (2 * P + 1) * max ρ ρ⁻¹)⁻¹ * G 1 ≤ G β := by
    have h1 : (ρ - 1/β)^j * G t ≤ G β := hchain.1
    have h6 : (2 ^ (2 * P + 1) * max ρ ρ⁻¹)⁻¹ * G 1 ≤ G t := by
      rw [inv_mul_le_iff₀ (by positivity : (0:ℝ) < 2 ^ (2 * P + 1) * max ρ ρ⁻¹)]
      exact hbt.2
    have h3 : (ρ - 1/β)^j = ρ^j * (1 - 1/(β*ρ))^j := by rw [hsplitm, mul_pow]
    have h5 : min 1 ρ⁻¹ * β ^ (Real.logb 2 ρ) ≤ ρ^j := hrho1
    have hpm_nn : 0 ≤ (ρ - 1/β)^j := pow_nonneg hρ1β.le j
    have hKbnn : 0 ≤ (2 ^ (2 * P + 1) * max ρ ρ⁻¹)⁻¹ * G 1 := by positivity
    have hA1 : ρ^j * ((1 - 1/(β*ρ))^j * ((2 ^ (2 * P + 1) * max ρ ρ⁻¹)⁻¹ * G 1))
        ≤ (ρ - 1/β)^j * ((2 ^ (2 * P + 1) * max ρ ρ⁻¹)⁻¹ * G 1) := by
      rw [h3]; exact le_of_eq (by ring)
    have hA2 : ρ^j * ((1 - 1/(β*ρ))^j * ((2 ^ (2 * P + 1) * max ρ ρ⁻¹)⁻¹ * G 1))
        ≤ (ρ - 1/β)^j * G t :=
      le_trans hA1 (mul_le_mul_of_nonneg_left h6 hpm_nn)
    have hA3 : (min 1 ρ⁻¹ * β ^ (Real.logb 2 ρ)) * ((1/2) * ((2 ^ (2 * P + 1) * max ρ ρ⁻¹)⁻¹ * G 1))
        ≤ ρ^j * ((1 - 1/(β*ρ))^j * ((2 ^ (2 * P + 1) * max ρ ρ⁻¹)⁻¹ * G 1)) :=
      mul_le_mul h5 (mul_le_mul_of_nonneg_right h4l hKbnn)
        (mul_nonneg (by norm_num) hKbnn)
        (pow_nonneg hρ0.le j)
    have hA4 : (min 1 ρ⁻¹ * β ^ (Real.logb 2 ρ)) * ((1/2) * ((2 ^ (2 * P + 1) * max ρ ρ⁻¹)⁻¹ * G 1))
        ≤ G β := le_trans hA3 (le_trans hA2 h1)
    have hA5 : min 1 ρ⁻¹ * β ^ (Real.logb 2 ρ) * (1/2) * (2 ^ (2 * P + 1) * max ρ ρ⁻¹)⁻¹ * G 1
        = (min 1 ρ⁻¹ * β ^ (Real.logb 2 ρ)) * ((1/2) * ((2 ^ (2 * P + 1) * max ρ ρ⁻¹)⁻¹ * G 1)) := by
      ring
    rw [hA5]; exact hA4
  -- |y| = G β / G 1
  have hu : u = valY Y c x₀ := eq_valY hfun hux
  have hv : v = valY Y c (x₀ * β) := eq_valY hfun hvx
  have hu0 : u ≠ 0 := by
    rw [hu]; simpa using (deep_val hgood hβ1 hx₀ hdeep (hmemD 1 ⟨le_rfl, hβ1⟩)).2
  have hyv : y = v / u := (eq_div_iff hu0).mpr hyu
  have hyabs : |y| = G β / G 1 := by
    rw [hyv, hv, hu]
    rw [hGdef]
    simp only [mul_one]
    rw [abs_div]
  rw [hyabs]
  constructor
  · rw [le_div_iff₀ hG1pos]
    calc (max 1 ((2:ℝ)^(2*P+2) * (max ρ ρ⁻¹)^2))⁻¹ * β ^ (Real.logb 2 ρ) * G 1
        = (max 1 ((2:ℝ)^(2*P+2) * (max ρ ρ⁻¹)^2))⁻¹ * (β ^ (Real.logb 2 ρ) * G 1) := by ring
      _ ≤ (min 1 ρ⁻¹ * (1/2) * (2 ^ (2 * P + 1) * max ρ ρ⁻¹)⁻¹) * (β ^ (Real.logb 2 ρ) * G 1) :=
          mul_le_mul_of_nonneg_right (cand_C_lo P hρ0) (mul_nonneg hβσnn hG1pos.le)
      _ = min 1 ρ⁻¹ * β ^ (Real.logb 2 ρ) * (1/2) * (2 ^ (2 * P + 1) * max ρ ρ⁻¹)⁻¹ * G 1 := by ring
      _ ≤ G β := hlo1
  · rw [div_le_iff₀ hG1pos]
    calc G β ≤ max 1 ρ⁻¹ * β ^ (Real.logb 2 ρ) * (2 * (2 ^ (2 * P + 1) * max ρ ρ⁻¹)) * G 1 := hup1
      _ = (max 1 ρ⁻¹ * (2 * (2 ^ (2 * P + 1) * max ρ ρ⁻¹))) * (β ^ (Real.logb 2 ρ) * G 1) := by ring
      _ ≤ (max 1 ((2:ℝ)^(2*P+2) * (max ρ ρ⁻¹)^2)) * (β ^ (Real.logb 2 ρ) * G 1) :=
          mul_le_mul_of_nonneg_right (cand_C_up P hρ0) (mul_nonneg hβσnn hG1pos.le)
      _ = max 1 ((2:ℝ)^(2*P+2) * (max ρ ρ⁻¹)^2) * β ^ (Real.logb 2 ρ) * G 1 := by ring

end Work.WilC4
