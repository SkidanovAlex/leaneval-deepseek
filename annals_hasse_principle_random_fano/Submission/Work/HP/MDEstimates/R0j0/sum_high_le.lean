import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.lam_basic

/-!
# `Work.HP.MDEstimates.R0j0.sum_high_le`

High-index part of the summation bound of Browning--Le Boudec--Sawin, *The Hasse principle for
random Fano hypersurfaces* (Annals 2023), Lemma R0 (`j₀ = 0`).

For an integral lattice `L` of rank `R ≥ 1` with successive minima `λ₁ ≤ … ≤ λ_R`, cut-off `T ≥ 1`
and `Y ≥ max(T, λ_R)`, and for `j ≤ R - 1`,

`∑_{k=0}^{j} T^{R-j+k} / (λ₁ ⋯ λ_{R-j+k}) ≤ R · T^{R-j} Y^j / det L`,

as long as `det L > 0` and `det L ≤ λ₁ ⋯ λ_R` (the elementary half of Minkowski's second theorem).

The proof bounds each summand separately.  Writing `m = R - j + k` (so `R - j ≤ m ≤ R`), split the
full product at `m`:

`λ₁ ⋯ λ_R = (λ₁ ⋯ λ_m) · ∏_{i<m'} λ_{m+i+1}`

where `m' = R - m`.  Every factor of the tail is at most `Y`, hence the tail is at most
`Y^{R-m}`, and combined with `det L ≤ λ₁ ⋯ λ_R` this gives `det L ≤ (λ₁ ⋯ λ_m) Y^{R-m}`.
Since `T ≤ Y` and `R - j ≤ m`,

`T^m Y^{R-m} = T^{R-j} · T^{m-(R-j)} · Y^{R-m} ≤ T^{R-j} Y^{(m-(R-j))+(R-m)} = T^{R-j} Y^j`,

so `T^m / (λ₁ ⋯ λ_m) ≤ T^{R-j} Y^j / det L`; dividing both sides by the positive products and
using `det L > 0`, `λ_i > 0`.  Summing the `j + 1 ≤ R` equal terms gives the claim.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace Work.HP.MDEstimates.R0j0

open Work.HP

/-- Splitting the product `∏_{i < R} g (i+1)` at `m ≤ R` and bounding the tail by `Y ^ (R-m)`:
if `0 < g i ≤ Y` for `1 ≤ i ≤ R` then
`∏_{i<R} g (i+1) ≤ (∏_{i<m} g (i+1)) * Y ^ (R-m)`. -/
lemma prod_range_le_prod_range_mul_pow {g : ℕ → ℝ} {Y : ℝ} {m R : ℕ} (hm : m ≤ R)
    (hpos : ∀ i, 1 ≤ i → i ≤ R → 0 < g i) (hY : ∀ i, 1 ≤ i → i ≤ R → g i ≤ Y) :
    ∏ i ∈ Finset.range R, g (i + 1) ≤ (∏ i ∈ Finset.range m, g (i + 1)) * Y ^ (R - m) := by
  have hsplit : ∏ i ∈ Finset.range R, g (i + 1)
      = (∏ i ∈ Finset.range m, g (i + 1)) * ∏ i ∈ Finset.range (R - m), g (i + m + 1) := by
    have h := Finset.prod_range_add (fun i => g (i + 1)) m (R - m)
    rw [Nat.add_sub_of_le hm] at h
    rw [h]
    congr 1
    exact Finset.prod_congr rfl fun i _ => by congr 1; omega
  rw [hsplit]
  refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun i hi => ?_)
  · calc ∏ i ∈ Finset.range (R - m), g (i + m + 1)
        ≤ ∏ _i ∈ Finset.range (R - m), Y := by
          refine Finset.prod_le_prod₀ (fun i hi => ?_) (fun i hi => ?_)
          · exact le_of_lt (hpos _ (by omega) (by have := Finset.mem_range.mp hi; omega))
          · exact hY _ (by omega) (by have := Finset.mem_range.mp hi; omega)
      _ = Y ^ (R - m) := by rw [Finset.prod_const, Finset.card_range]
  · exact le_of_lt (hpos _ (by omega) (by have := Finset.mem_range.mp hi; omega))

/-- Elementary power arithmetic: for `0 ≤ T ≤ Y` and naturals `a ≤ m ≤ R`, `a + j = R`,
`T ^ m * Y ^ (R - m) ≤ T ^ a * Y ^ j`. -/
lemma pow_mul_pow_le {T Y : ℝ} (hT : 0 ≤ T) (hTY : T ≤ Y) {a j m R : ℕ}
    (ha : a ≤ m) (hm : m ≤ R) (haj : a + j = R) :
    T ^ m * Y ^ (R - m) ≤ T ^ a * Y ^ j := by
  have hY0 : 0 ≤ Y := le_trans hT hTY
  have h1 : T ^ a * T ^ (m - a) = T ^ m := by rw [← pow_add]; congr 1; omega
  have h2 : Y ^ (m - a) * Y ^ (R - m) = Y ^ j := by rw [← pow_add]; congr 1; omega
  calc T ^ m * Y ^ (R - m)
      = T ^ a * (T ^ (m - a) * Y ^ (R - m)) := by rw [← h1]; ring
    _ ≤ T ^ a * (Y ^ (m - a) * Y ^ (R - m)) := by
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hT a)
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hT hTY (m - a)) (pow_nonneg hY0 (R - m))
    _ = T ^ a * Y ^ j := by rw [h2]

theorem sum_high_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Submodule ℤ (ι → ℤ)) (R j : ℕ) (Y T : ℝ)
    (hrk : rk L = R) (hR : 1 ≤ R) (hj : j ≤ R - 1) (hT : 1 ≤ T) (hTY : T ≤ Y)
    (hlamR : lam L R ≤ Y) (hdet : 0 < detL L)
    (hdetle : detL L ≤ ∏ i ∈ Finset.range R, lam L (i + 1)) :
    (∑ k ∈ Finset.range (j + 1),
        T ^ (R - j + k) / ∏ i ∈ Finset.range (R - j + k), lam L (i + 1))
      ≤ (R : ℝ) * (T ^ (R - j) * Y ^ j / detL L) := by
  have hjR : j ≤ R := by omega
  have hRrk : R ≤ rk L := by rw [hrk]
  have hTpos : 0 < T := lt_of_lt_of_le one_pos hT
  have hYpos : 0 < Y := by linarith
  have hlampos : ∀ i, 1 ≤ i → i ≤ R → 0 < lam L i := fun i hi1 hiR =>
    lam_pos L hi1 (by rw [hrk]; exact hiR)
  have hlamY : ∀ i, 1 ≤ i → i ≤ R → lam L i ≤ Y := fun i _ hiR =>
    le_trans (lam_mono L hiR hRrk) hlamR
  have hPpos : ∀ k, k ≤ R → 0 < ∏ i ∈ Finset.range k, lam L (i + 1) := by
    intro k hk
    refine Finset.prod_pos fun i hi => ?_
    exact hlampos (i + 1) (by omega) (by have := Finset.mem_range.mp hi; omega)
  -- Each summand with index `m = R - j + k`, `k ≤ j`, is at most `T^(R-j) Y^j / det L`.
  have hterm : ∀ k ∈ Finset.range (j + 1),
      T ^ (R - j + k) / ∏ i ∈ Finset.range (R - j + k), lam L (i + 1)
        ≤ T ^ (R - j) * Y ^ j / detL L := by
    intro k hk
    have hkj : k ≤ j := by have := Finset.mem_range.mp hk; omega
    have hmle : R - j + k ≤ R := by omega
    -- `det L ≤ (∏_{i<m} λ_{i+1}) Y^{R-m}`
    have hdetm : detL L ≤ (∏ i ∈ Finset.range (R - j + k), lam L (i + 1))
        * Y ^ (R - (R - j + k)) :=
      le_trans hdetle (prod_range_le_prod_range_mul_pow hmle hlampos hlamY)
    have hPm : 0 < ∏ i ∈ Finset.range (R - j + k), lam L (i + 1) := hPpos _ hmle
    rw [div_le_div_iff₀ hPm hdet]
    calc T ^ (R - j + k) * detL L
        ≤ T ^ (R - j + k) * ((∏ i ∈ Finset.range (R - j + k), lam L (i + 1))
            * Y ^ (R - (R - j + k))) := mul_le_mul_of_nonneg_left hdetm (pow_nonneg hTpos.le _)
      _ = T ^ (R - j + k) * Y ^ (R - (R - j + k))
            * (∏ i ∈ Finset.range (R - j + k), lam L (i + 1)) := by ring
      _ ≤ T ^ (R - j) * Y ^ j * (∏ i ∈ Finset.range (R - j + k), lam L (i + 1)) := by
          refine mul_le_mul_of_nonneg_right ?_ hPm.le
          exact pow_mul_pow_le hTpos.le hTY (Nat.le_add_right _ _) hmle (by omega)
  calc ∑ k ∈ Finset.range (j + 1),
        T ^ (R - j + k) / ∏ i ∈ Finset.range (R - j + k), lam L (i + 1)
      ≤ ∑ _k ∈ Finset.range (j + 1), T ^ (R - j) * Y ^ j / detL L := Finset.sum_le_sum hterm
    _ = ((j + 1 : ℕ) : ℝ) * (T ^ (R - j) * Y ^ j / detL L) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (R : ℝ) * (T ^ (R - j) * Y ^ j / detL L) := by
        refine mul_le_mul_of_nonneg_right ?_ ?_
        · have : j + 1 ≤ R := by omega
          exact_mod_cast this
        · positivity

end Work.HP.MDEstimates.R0j0
