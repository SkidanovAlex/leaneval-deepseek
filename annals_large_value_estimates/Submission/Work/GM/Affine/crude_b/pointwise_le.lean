import Mathlib
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.comb_sum_le
import Submission.Work.GM.Affine.aliasing_le
import Submission.Work.GM.Affine.supf_le_of_decay

/-!
# GM §9, crude case (b): the pointwise bound for `affineSum`

The crude case of GM Proposition 9.1 needs a pointwise bound for the affine sum

`J(u) = Σ_{m₁ ∈ R1, m₂ ∈ R2} Σ_{m₃ ∈ R3} f ((m₁ u + m₃)/m₂)`

in terms of `(R1 M₁).card`, `∫ f` and the two Fourier-decay constants `c j ε`, `c 2 ε`.

For fixed `m₂` the inner `m₃`-sum is bounded by `m₂ · aliasing f m₂` (Poisson summation,
`comb_sum_le`), and the *sharp* aliasing bound

`aliasing f m ≤ ∫ f + 4 (∫ f)^{1-1/j} (c j ε T^ε (T/m)^j sup f)^{1/j}`

kills one factor of `m₂`.  Summing over `m₂ ∈ R2 M₂` (where `M₂ < m₂ ≤ 2 M₂`, so that
`Σ m₂ ≤ 4 M₂²` and `#(R2 M₂) ≤ 2 M₂`) and then using the crude bound
`sup f ≤ 16 c(2,ε) T^ε T² ∫ f` (`supf_le_of_decay`) with AM–GM on the exponents
(`(∫f)^{1-1/j} (∫f)^{1/j} ≤ ∫f`) gives

`J(u) ≤ #(R1 M₁) · (∫ f) · (4 M₂² + 8 (16 c(j,ε) c(2,ε) T^{j+2+2ε})^{1/j} M₂)`.

This is exactly the pointwise input of the crude case `crude_case_b`.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine.crude_b

noncomputable section

/-! ### Elementary `rpow` arithmetic -/

/-- The AM–GM step: `z^{1-1/j} · (K z^{1/j}) ≤ K z` for `z, K ≥ 0` and `j ≥ 1`. -/
private lemma rpow_split_le {A K : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K) {j : ℕ} (hj : 1 ≤ j) :
    A ^ (1 - 1/(j:ℝ)) * (K * A ^ (1/(j:ℝ))) ≤ K * A := by
  have hje : (0:ℝ) < (j:ℝ) := by exact_mod_cast (by omega : 0 < j)
  have hle := Real.le_rpow_add hA (1 - 1/(j:ℝ)) (1/(j:ℝ))
  have hsum : 1 - 1/(j:ℝ) + 1/(j:ℝ) = 1 := by
    have hne : (j:ℝ) ≠ 0 := ne_of_gt hje
    field_simp
    ring
  rw [hsum, Real.rpow_one] at hle
  calc A ^ (1 - 1/(j:ℝ)) * (K * A ^ (1/(j:ℝ)))
      = K * (A ^ (1 - 1/(j:ℝ)) * A ^ (1/(j:ℝ))) := by ring
    _ ≤ K * A := mul_le_mul_of_nonneg_left hle hK

/-- Replacing `sup f` by its crude bound `16 c(2,ε) T^ε T² ∫f` inside the `(1/j)`-th power. -/
private lemma rpow_le_of_sup {cj c2 T S A : ℝ} {j : ℕ} {ε : ℝ}
    (hT : 0 ≤ T) (hcj : 0 ≤ cj) (hc2 : 0 ≤ c2) (hS : 0 ≤ S) (hA : 0 ≤ A)
    (hsup : S ≤ 16 * c2 * T^ε * T^2 * A) (hj : 1 ≤ j) :
    (cj * T^ε * T^(j:ℝ) * S) ^ (1/(j:ℝ)) ≤
      (16 * cj * c2 * T^((j:ℝ)+2+2*ε) * A) ^ (1/(j:ℝ)) := by
  have hprod : T^ε * T^(j:ℝ) * (T^ε * T^2) ≤ T^((j:ℝ)+2+2*ε) := by
    have h1 := Real.le_rpow_add hT ε ε
    have h2 : T^(j:ℝ) * T^2 ≤ T^((j:ℝ)+2) := by
      rw [← Real.rpow_natCast T 2]
      exact Real.le_rpow_add hT ((j:ℝ)) 2
    have h3 := Real.le_rpow_add hT (ε+ε) ((j:ℝ)+2)
    have hmul : T^ε * T^(j:ℝ) * (T^ε * T^2) = (T^ε * T^ε) * (T^(j:ℝ) * T^2) := by ring
    rw [hmul]
    calc (T^ε * T^ε) * (T^(j:ℝ) * T^2) ≤ T^(ε+ε) * T^((j:ℝ)+2) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ ≤ T^((ε+ε) + ((j:ℝ)+2)) := h3
      _ = T^((j:ℝ)+2+2*ε) := by ring_nf
  have hbase : cj * T^ε * T^(j:ℝ) * S ≤ 16 * cj * c2 * T^((j:ℝ)+2+2*ε) * A := by
    have h1 : cj * T^ε * T^(j:ℝ) * S ≤ cj * T^ε * T^(j:ℝ) * (16 * c2 * T^ε * T^2 * A) :=
      mul_le_mul_of_nonneg_left hsup (by positivity)
    have h2 : cj * T^ε * T^(j:ℝ) * (16 * c2 * T^ε * T^2 * A)
        = 16 * cj * c2 * A * (T^ε * T^(j:ℝ) * (T^ε * T^2)) := by ring
    have h3 : 16 * cj * c2 * A * (T^ε * T^(j:ℝ) * (T^ε * T^2))
        ≤ 16 * cj * c2 * A * T^((j:ℝ)+2+2*ε) :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    have h4 : 16 * cj * c2 * A * T^((j:ℝ)+2+2*ε) = 16 * cj * c2 * T^((j:ℝ)+2+2*ε) * A := by ring
    calc cj * T^ε * T^(j:ℝ) * S
        ≤ cj * T^ε * T^(j:ℝ) * (16 * c2 * T^ε * T^2 * A) := h1
      _ = 16 * cj * c2 * A * (T^ε * T^(j:ℝ) * (T^ε * T^2)) := h2
      _ ≤ 16 * cj * c2 * A * T^((j:ℝ)+2+2*ε) := h3
      _ = 16 * cj * c2 * T^((j:ℝ)+2+2*ε) * A := h4
  exact Real.rpow_le_rpow (by positivity) hbase (by positivity)

/-- The factor `m₂` is absorbed by the aliasing scale: `m · (Z (T/m)^j W)^{1/j} = (Z W T^j)^{1/j}`
for `m > 0`, `Z (T/m)^j W ≥ 0`. -/
private lemma mul_rpow_factor {T m Z W : ℝ} {j : ℕ} (hm : 0 < m) (hj : 0 < j)
    (hZ : 0 ≤ Z * (T/m)^j * W) :
    m * (Z * (T/m)^j * W) ^ (1/(j:ℝ)) = (Z * W * T^(j:ℝ)) ^ (1/(j:ℝ)) := by
  have hmj : 0 ≤ m^j := by positivity
  have h1 : (m^j)^(1/(j:ℝ)) = m := by
    rw [one_div, Real.pow_rpow_inv_natCast hm.le (by omega)]
  calc m * (Z * (T/m)^j * W)^(1/(j:ℝ))
      = (m^j)^(1/(j:ℝ)) * (Z * (T/m)^j * W)^(1/(j:ℝ)) := by rw [h1]
    _ = (m^j * (Z * (T/m)^j * W))^(1/(j:ℝ)) := by
        rw [Real.mul_rpow hmj hZ]
    _ = (Z * (m^j * (T/m)^j) * W)^(1/(j:ℝ)) := by
        rw [show m^j * (Z * (T/m)^j * W) = Z * (m^j * (T/m)^j) * W by ring]
    _ = (Z * T^j * W)^(1/(j:ℝ)) := by
        rw [show m^j * (T/m)^j = T^j by
          rw [← mul_pow, mul_comm m (T/m), div_mul_cancel₀ T (ne_of_gt hm)]]
    _ = (Z * W * T^(j:ℝ))^(1/(j:ℝ)) := by
        have : Z * T^j * W = Z * W * T^(j:ℝ) := by rw [Real.rpow_natCast]; ring
        rw [this]

/-! ### The per-`m₂` step -/

/-- Multiplying the sharp aliasing bound by `m` removes the scale `m` from the decay term and
replaces `sup f` by its crude bound: for `m > 0`,

`m · aliasing f m ≤ m ∫f + 4 (∫f) (16 c(j,ε) c(2,ε) T^{j+2+2ε})^{1/j}`. -/
private lemma mul_aliasing_le {c : ℕ → ℝ → ℝ} {T : ℝ} {f : ℝ → ℝ} {j : ℕ} {ε : ℝ}
    (hε : 0 < ε) (hj : 3 ≤ j) (hT : 0 ≤ T)
    (hf : Continuous f) (hnn : ∀ u, 0 ≤ f u) (hcs : HasCompactSupport f)
    (hdec : DecayHyp c T f) (hcj : 0 ≤ c j ε) (hc2 : 0 ≤ c 2 ε)
    (hsharp : ∀ m : ℝ, 0 < m → aliasing f m ≤ (∫ u, f u) +
        4 * (∫ u, f u) ^ (1 - 1/(j:ℝ)) * (c j ε * T ^ ε * (T/m) ^ j * supf f) ^ (1/(j:ℝ)))
    {m : ℝ} (hm : 0 < m) :
    m * aliasing f m ≤ m * (∫ u, f u) +
      4 * (∫ u, f u) * (16 * c j ε * c 2 ε * T ^ ((j:ℝ) + 2 + 2*ε)) ^ (1/(j:ℝ)) := by
  have hj1 : 1 ≤ j := by omega
  have hA : 0 ≤ ∫ u, f u := integral_nonneg hnn
  have hS : 0 ≤ supf f := supf_nonneg hf hcs hnn
  have hsup : supf f ≤ 16 * c 2 ε * T^ε * T^2 * ∫ u, f u :=
    supf_le_of_decay hf hcs hnn hdec hε hc2
  have hfac : m * (c j ε * T^ε * (T/m)^j * supf f) ^ (1/(j:ℝ))
      = (c j ε * T^ε * supf f * T^(j:ℝ)) ^ (1/(j:ℝ)) :=
    mul_rpow_factor hm (by omega) (by positivity)
  have hbound : 4 * (∫ u, f u) ^ (1 - 1/(j:ℝ)) * (c j ε * T^ε * T^(j:ℝ) * supf f) ^ (1/(j:ℝ))
      ≤ 4 * (∫ u, f u) * (16 * c j ε * c 2 ε * T ^ ((j:ℝ) + 2 + 2*ε)) ^ (1/(j:ℝ)) := by
    have h1 := rpow_le_of_sup hT hcj hc2 hS hA hsup hj1
    have hsplit : (16 * c j ε * c 2 ε * T ^ ((j:ℝ) + 2 + 2*ε) * (∫ u, f u)) ^ (1/(j:ℝ))
        = (16 * c j ε * c 2 ε * T ^ ((j:ℝ) + 2 + 2*ε)) ^ (1/(j:ℝ)) * (∫ u, f u) ^ (1/(j:ℝ)) :=
      Real.mul_rpow (by positivity) hA
    have hKnn : 0 ≤ (16 * c j ε * c 2 ε * T ^ ((j:ℝ) + 2 + 2*ε)) ^ (1/(j:ℝ)) := by positivity
    calc 4 * (∫ u, f u) ^ (1 - 1/(j:ℝ)) * (c j ε * T^ε * T^(j:ℝ) * supf f) ^ (1/(j:ℝ))
        ≤ 4 * (∫ u, f u) ^ (1 - 1/(j:ℝ)) *
            (16 * c j ε * c 2 ε * T ^ ((j:ℝ) + 2 + 2*ε) * (∫ u, f u)) ^ (1/(j:ℝ)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 4 * ((16 * c j ε * c 2 ε * T ^ ((j:ℝ) + 2 + 2*ε)) ^ (1/(j:ℝ)) *
            ((∫ u, f u) ^ (1 - 1/(j:ℝ)) * (∫ u, f u) ^ (1/(j:ℝ)))) := by
          rw [hsplit]; ring
      _ ≤ 4 * ((16 * c j ε * c 2 ε * T ^ ((j:ℝ) + 2 + 2*ε)) ^ (1/(j:ℝ)) * (∫ u, f u)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_left (by simpa using rpow_split_le hA zero_le_one hj1) hKnn
      _ = 4 * (∫ u, f u) * (16 * c j ε * c 2 ε * T ^ ((j:ℝ) + 2 + 2*ε)) ^ (1/(j:ℝ)) := by ring
  have hbound2 : 4 * (∫ u, f u) ^ (1 - 1/(j:ℝ)) * (c j ε * T^ε * supf f * T^(j:ℝ)) ^ (1/(j:ℝ))
      ≤ 4 * (∫ u, f u) * (16 * c j ε * c 2 ε * T ^ ((j:ℝ) + 2 + 2*ε)) ^ (1/(j:ℝ)) := by
    rw [show c j ε * T^ε * supf f * T^(j:ℝ) = c j ε * T^ε * T^(j:ℝ) * supf f by ring]
    exact hbound
  have hmul2 : m * (4 * (∫ u, f u) ^ (1-1/(j:ℝ)) * (c j ε * T^ε * (T/m)^j * supf f) ^ (1/(j:ℝ)))
      = 4 * (∫ u, f u) ^ (1-1/(j:ℝ)) * (c j ε * T^ε * supf f * T^(j:ℝ)) ^ (1/(j:ℝ)) := by
    rw [show m * (4 * (∫ u, f u) ^ (1-1/(j:ℝ)) * (c j ε * T^ε * (T/m)^j * supf f) ^ (1/(j:ℝ)))
        = 4 * (∫ u, f u) ^ (1-1/(j:ℝ)) *
            (m * (c j ε * T^ε * (T/m)^j * supf f) ^ (1/(j:ℝ))) by ring]
    rw [hfac]
  calc m * aliasing f m
      ≤ m * ((∫ u, f u) + 4 * (∫ u, f u) ^ (1 - 1/(j:ℝ)) *
          (c j ε * T ^ ε * (T/m) ^ j * supf f) ^ (1/(j:ℝ))) :=
        mul_le_mul_of_nonneg_left (hsharp m hm) hm.le
    _ = m * (∫ u, f u) + 4 * (∫ u, f u) ^ (1-1/(j:ℝ)) *
          (c j ε * T^ε * supf f * T^(j:ℝ)) ^ (1/(j:ℝ)) := by
        rw [mul_add, hmul2]
    _ ≤ m * (∫ u, f u) + 4 * (∫ u, f u) *
          (16 * c j ε * c 2 ε * T ^ ((j:ℝ) + 2 + 2*ε)) ^ (1/(j:ℝ)) :=
        add_le_add le_rfl hbound2

/-! ### Counting the `m₂`-range -/

/-- Every element of `R2 M₂` is a positive real. -/
private lemma R2_pos {M₂ : ℝ} {m : ℤ} (hm : m ∈ R2 M₂) : 0 < (m:ℝ) := by
  have h1 : (1:ℤ) ≤ m := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
  have h2 : (0:ℤ) < m := lt_of_lt_of_le (by norm_num) h1
  exact_mod_cast h2

/-- `#(R2 M₂) ≤ 2 M₂` for `M₂ ≥ 0`. -/
private lemma R2_card_le {M₂ : ℝ} (hM₂ : 0 ≤ M₂) : ((R2 M₂).card : ℝ) ≤ 2 * M₂ := by
  have hsub : R2 M₂ ⊆ Finset.Icc (1:ℤ) ⌊2*M₂⌋ := fun m hm => (Finset.mem_filter.mp hm).1
  have hcard_int : ((Finset.Icc (1:ℤ) ⌊2*M₂⌋).card : ℤ) = ⌊2*M₂⌋ := by
    rw [Int.card_Icc_of_le 1 ⌊2*M₂⌋ (by
      have := Int.floor_nonneg.mpr (by linarith : (0:ℝ) ≤ 2 * M₂)
      omega)]
    ring
  have h1 : (R2 M₂).card ≤ (Finset.Icc (1:ℤ) ⌊2*M₂⌋).card := Finset.card_le_card hsub
  have h2 : ((Finset.Icc (1:ℤ) ⌊2*M₂⌋).card : ℝ) = (⌊2*M₂⌋ : ℝ) := by
    exact_mod_cast hcard_int
  calc ((R2 M₂).card : ℝ) ≤ ((Finset.Icc (1:ℤ) ⌊2*M₂⌋).card : ℝ) := by exact_mod_cast h1
    _ = (⌊2*M₂⌋ : ℝ) := h2
    _ ≤ 2 * M₂ := Int.floor_le _

/-- `Σ_{m₂ ∈ R2 M₂} m₂ ≤ 4 M₂²` for `M₂ ≥ 0`. -/
private lemma R2_sum_le {M₂ : ℝ} (hM₂ : 0 ≤ M₂) :
    ∑ m ∈ R2 M₂, (m:ℝ) ≤ 4 * M₂^2 := by
  have hterm2 : ∀ m ∈ R2 M₂, (m:ℝ) ≤ 2 * M₂ := by
    intro m hm
    have h1 : m ≤ ⌊2*M₂⌋ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).2
    calc (m:ℝ) ≤ (⌊2*M₂⌋ : ℝ) := by exact_mod_cast h1
      _ ≤ 2*M₂ := Int.floor_le _
  calc ∑ m ∈ R2 M₂, (m:ℝ) ≤ ∑ m ∈ R2 M₂, (2 * M₂) := Finset.sum_le_sum hterm2
    _ = ((R2 M₂).card : ℝ) * (2*M₂) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2*M₂) * (2*M₂) := mul_le_mul_of_nonneg_right (R2_card_le hM₂) (by linarith)
    _ = 4 * M₂^2 := by ring

/-! ### The pointwise bound -/

theorem pointwise_le {c : ℕ → ℝ → ℝ} {K C₀ T M₁ M₂ M₃ : ℝ} {f : ℝ → ℝ} {j : ℕ} {ε : ℝ}
    (hε : 0 < ε) (hj : 3 ≤ j) (hT : 0 ≤ T)
    (hf : Continuous f) (hnn : ∀ u, 0 ≤ f u) (hcs : HasCompactSupport f)
    (hdec : DecayHyp c T f) (hcj : 0 ≤ c j ε) (hc2 : 0 ≤ c 2 ε)
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (hsharp : ∀ m : ℝ, 0 < m → aliasing f m ≤ (∫ u, f u) +
        4 * (∫ u, f u) ^ (1 - 1/(j:ℝ)) * (c j ε * T ^ ε * (T/m) ^ j * supf f) ^ (1/(j:ℝ))) :
    ∀ u, Submission.GM.affineSum K M₁ M₂ M₃ f u ≤
      ((R1 M₁).card : ℝ) * (∫ u, f u) *
        (4 * M₂ ^ 2 + 8 * (16 * c j ε * c 2 ε * T ^ ((j:ℝ) + 2 + 2*ε)) ^ (1/(j:ℝ)) * M₂) := by
  intro u
  have hA : 0 ≤ ∫ u, f u := integral_nonneg hnn
  have hM2nn : 0 ≤ M₂ := hM₂.le
  set Kcap : ℝ := (16 * c j ε * c 2 ε * T ^ ((j:ℝ) + 2 + 2*ε)) ^ (1/(j:ℝ)) with hKcap
  rw [affineSum_eq]
  have hinner : ∀ m₁ ∈ R1 M₁, ∀ m₂ ∈ R2 M₂,
      ∑ m₃ ∈ R3 K M₃, f (((m₁ : ℝ) * u + (m₃:ℤ)) / (m₂:ℤ)) ≤
        (m₂:ℝ) * aliasing f (m₂:ℝ) := by
    intro m₁ _ m₂ hm₂
    exact comb_sum_le hf hnn hcs hdec hε (R2_pos hm₂) ⌊K*M₃⌋ (m₁ * u)
  calc ∑ m₁ ∈ R1 M₁, ∑ m₂ ∈ R2 M₂, ∑ m₃ ∈ R3 K M₃, f (((m₁ : ℝ) * u + (m₃:ℤ)) / (m₂:ℤ))
      ≤ ∑ m₁ ∈ R1 M₁, ∑ m₂ ∈ R2 M₂, (m₂:ℝ) * aliasing f (m₂:ℝ) := by
        apply Finset.sum_le_sum; intro m₁ hm₁
        apply Finset.sum_le_sum; intro m₂ hm₂
        exact hinner m₁ hm₁ m₂ hm₂
    _ = ((R1 M₁).card : ℝ) * (∑ m₂ ∈ R2 M₂, (m₂:ℝ) * aliasing f (m₂:ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((R1 M₁).card : ℝ) * (∑ m₂ ∈ R2 M₂,
          ((m₂:ℝ) * (∫ u, f u) + 4 * (∫ u, f u) * Kcap)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum; intro m₂ hm₂
        have hb := mul_aliasing_le hε hj hT hf hnn hcs hdec hcj hc2 hsharp (R2_pos hm₂)
        simpa only [hKcap] using hb
    _ = ((R1 M₁).card : ℝ) * ((∑ m₂ ∈ R2 M₂, (m₂:ℝ)) * (∫ u, f u) +
          ((R2 M₂).card : ℝ) * (4 * (∫ u, f u) * Kcap)) := by
        congr 1
        rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((R1 M₁).card : ℝ) * (4 * M₂^2 * (∫ u, f u) +
          (2*M₂) * (4 * (∫ u, f u) * Kcap)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right (R2_sum_le hM2nn) hA
        · exact mul_le_mul_of_nonneg_right (R2_card_le hM2nn) (by positivity)
    _ = ((R1 M₁).card : ℝ) * (∫ u, f u) * (4 * M₂^2 + 8 * Kcap * M₂) := by ring

end

end Work.GM.Affine.crude_b
