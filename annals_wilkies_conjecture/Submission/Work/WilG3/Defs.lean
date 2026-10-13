/-
  WilG3 — area G3 of the BNZ algebraic lemma (Binyamini–Novikov–Zak, arXiv 2202.05305 §5.1):
  BNZ Lemma 5.4 (`WilkieDesign.CG.G3_discrete_Cr`) and the affine interval cover
  (`WilkieDesign.CG.G3_affine_cover`), whose statements are frozen in
  `Submission/Work/Wilkies/CG/Spec.lean`.

  This file holds the vocabulary of the area — the geometric chart family that realizes the
  cover — with its basic API.  The two target theorems are proved in `Discrete.lean` and
  `Cover.lean`, which import this file; the sub-lemmas of the area are delegated and live in
  sibling modules of this directory (all of them import this one).
-/
import Submission.Work.Wilkies.CG.Spec

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilG3

/-! ## The geometric chart family

`G3_affine_cover` asks for a finite family of intervals `[u,v] ⊆ (0,1)` with
`(v - u)·(r+1) ≤ dist([u,v], {0,1}) = min u (1-v)`, covering `[ε, 1-ε]`, with at most
`8(r+1)(|log ε| + 2)` intervals.

We build it as a geometric family: the left half is `k ↦ [ρ^(k+1)/2, ρ^k/2]` for `k < K`, and
the right half is its mirror image under `x ↦ 1 - x`.  With `ρ = 1 - 1/(r+2)` the length of the
`k`-th chart is `ρ^k(1-ρ)/2`, so `(r+1)(v-u) = (r+1)/(r+2) · ρ^k/2 = ρ^{k+1}/2 = u`, and
`u ≤ 1/2 ≤ 1 - v`; this is exactly the required inequality.  The number of scales needed to
reach `ε` is `≈ (r+2)|log ε| ≈ (r+1)|log ε|`, which gives the stated bound. -/

/-- Ratio of the geometric chart family: `1 - 1/(r+2)`, which lies in `[1/2, 1)`. -/
def geoRho (r : ℕ) : ℝ := 1 - ((r : ℝ) + 2)⁻¹

/-- Left half of the chart family: the chart of scale `k` is `[ρ^(k+1)/2, ρ^k/2]`, stored as
`(lower, upper)`. -/
def geoL (r K : ℕ) : Finset (ℝ × ℝ) :=
  (Finset.range K).image fun k => (geoRho r ^ (k + 1) / 2, geoRho r ^ k / 2)

/-- Right half of the chart family: the mirror image of `geoL` under `x ↦ 1 - x`, again stored
as `(lower, upper)`. -/
def geoR (r K : ℕ) : Finset (ℝ × ℝ) :=
  (Finset.range K).image fun k => (1 - geoRho r ^ k / 2, 1 - geoRho r ^ (k + 1) / 2)

/-- The chart family.  It covers `[ρ^K/2, 1 - ρ^K/2]`; see `GeoChartsCovers`. -/
def geoCharts (r K : ℕ) : Finset (ℝ × ℝ) := geoL r K ∪ geoR r K

/-- Number of geometric scales used for a given `ε`: `⌈(r+2)·(-log ε)⌉ + 2`. -/
def geoK (r : ℕ) (ε : ℝ) : ℕ := Nat.ceil (((r : ℝ) + 2) * (-Real.log ε)) + 2

/-! ## Basic API of the ratio -/

theorem geoRho_eq (r : ℕ) : geoRho r = 1 - ((r : ℝ) + 2)⁻¹ := rfl

theorem geoRho_pos (r : ℕ) : 0 < geoRho r := by
  have h1 : (1 : ℝ) < (r : ℝ) + 2 := by
    have h2 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    linarith
  have h2 : ((r : ℝ) + 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
  simp only [geoRho]
  linarith

theorem geoRho_lt_one (r : ℕ) : geoRho r < 1 := by
  have h2 : 0 < ((r : ℝ) + 2)⁻¹ := inv_pos.mpr (by positivity)
  simp only [geoRho]
  linarith

theorem geoRho_nonneg (r : ℕ) : 0 ≤ geoRho r := le_of_lt (geoRho_pos r)

theorem geoRho_le_one (r : ℕ) : geoRho r ≤ 1 := le_of_lt (geoRho_lt_one r)

/-- `ρ ≥ 1/2`; this is why `min (ρ^k/2) (1 - ρ^{k+1}/2) = ρ^k/2`. -/
theorem half_le_geoRho (r : ℕ) : (1 : ℝ) / 2 ≤ geoRho r := by
  have h1 : (2 : ℝ) ≤ (r : ℝ) + 2 := by
    have h2 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    linarith
  have h3 : 0 < (2 : ℝ) := two_pos
  have h4 : (1 : ℝ) / ((r : ℝ) + 2) ≤ 1 / 2 := one_div_le_one_div_of_le h3 h1
  simp only [geoRho]
  rw [one_div] at h4
  rw [one_div] at h4
  linarith

/-- `(1 - ρ) * (r+1) = (r+1)/(r+2) ≤ 1`: the chart of scale `k` has length
`ρ^k (1-ρ) / 2`, and `(r+1)` times it is at most `ρ^k/2`. -/
theorem sub_geoRho_mul (r : ℕ) :
    (1 - geoRho r) * ((r : ℝ) + 1) = ((r : ℝ) + 1) / ((r : ℝ) + 2) := by
  have h2 : ((r : ℝ) + 2) ≠ 0 := by positivity
  simp only [geoRho]
  field_simp
  ring

theorem sub_geoRho_mul_le (r : ℕ) : (1 - geoRho r) * ((r : ℝ) + 1) ≤ 1 := by
  have h1 : (0 : ℝ) < (r : ℝ) + 2 := by positivity
  rw [sub_geoRho_mul]
  exact (div_le_one h1).mpr (by linarith)

theorem geoRho_pow_pos (r K : ℕ) : 0 < geoRho r ^ K := pow_pos (geoRho_pos r) K

theorem geoRho_pow_nonneg (r K : ℕ) : 0 ≤ geoRho r ^ K := le_of_lt (geoRho_pow_pos r K)

theorem geoRho_pow_le_one (r K : ℕ) : geoRho r ^ K ≤ 1 :=
  pow_le_one₀ (geoRho_nonneg r) (geoRho_le_one r)

/-- `ρ^k * (1 + ρ) ≤ 2`, used to identify `min (ρ^k/2) (1 - ρ^{k+1}/2)`. -/
theorem geoRho_pow_add_mul_le (r K : ℕ) : geoRho r ^ K * (1 + geoRho r) ≤ 2 := by
  have h1 : geoRho r ^ K ≤ 1 := geoRho_pow_le_one r K
  have h2 : 0 ≤ geoRho r ^ K := geoRho_pow_nonneg r K
  have h3 : 1 + geoRho r ≤ 2 := by linarith [geoRho_le_one r]
  have h4 : 0 ≤ 1 + geoRho r := by linarith [geoRho_nonneg r]
  calc geoRho r ^ K * (1 + geoRho r) ≤ 1 * 2 := mul_le_mul h1 h3 h4 zero_le_one
    _ = 2 := one_mul 2

/-- Quantitative mean-value estimate: if `u` is continuous on `[a,b]` and `u' x ≥ c` at every
interior point, then `u` grows by at least `c·(b-a)`. -/
theorem LeSubOfLeDeriv (u u' : ℝ → ℝ) (c a b : ℝ) (hab : a ≤ b)
    (hcont : ContinuousOn u (Set.Icc a b))
    (hder : ∀ x ∈ Set.Ioo a b, HasDerivAt u (u' x) x)
    (hc : ∀ x ∈ Set.Ioo a b, c ≤ u' x) :
    c * (b - a) ≤ u b - u a := by
  have hmem : ∀ x ∈ interior (Set.Icc a b), x ∈ Set.Ioo a b := by
    intro x hx
    rwa [interior_Icc] at hx
  exact Convex.mul_sub_le_image_sub_of_le_deriv (convex_Icc a b) hcont
    (fun x hx => ((hder x (hmem x hx)).differentiableAt).differentiableWithinAt)
    (fun x hx => by rw [(hder x (hmem x hx)).deriv]; exact hc x (hmem x hx))
    a ⟨le_refl a, hab⟩ b ⟨hab, le_refl b⟩ hab

/-! ## Membership and cardinality -/

theorem mem_geoL {r K : ℕ} {p : ℝ × ℝ} :
    p ∈ geoL r K ↔ ∃ k ∈ Finset.range K, (geoRho r ^ (k + 1) / 2, geoRho r ^ k / 2) = p := by
  simp [geoL]

theorem mem_geoR {r K : ℕ} {p : ℝ × ℝ} :
    p ∈ geoR r K ↔
      ∃ k ∈ Finset.range K, (1 - geoRho r ^ k / 2, 1 - geoRho r ^ (k + 1) / 2) = p := by
  simp [geoR]

theorem mem_geoCharts {r K : ℕ} {p : ℝ × ℝ} :
    p ∈ geoCharts r K ↔ p ∈ geoL r K ∨ p ∈ geoR r K := by
  simp [geoCharts]

theorem geoL_card_le (r K : ℕ) : (geoL r K).card ≤ K := by
  unfold geoL
  calc ((Finset.range K).image fun k => (geoRho r ^ (k + 1) / 2, geoRho r ^ k / 2)).card
      ≤ (Finset.range K).card := Finset.card_image_le
    _ = K := Finset.card_range K

theorem geoR_card_le (r K : ℕ) : (geoR r K).card ≤ K := by
  unfold geoR
  calc ((Finset.range K).image fun k => (1 - geoRho r ^ k / 2, 1 - geoRho r ^ (k + 1) / 2)).card
      ≤ (Finset.range K).card := Finset.card_image_le
    _ = K := Finset.card_range K

theorem geoCharts_card_le (r K : ℕ) : (geoCharts r K).card ≤ 2 * K := by
  have h1 : (geoL r K).card ≤ K := geoL_card_le r K
  have h2 : (geoR r K).card ≤ K := geoR_card_le r K
  have h3 : (geoL r K ∪ geoR r K).card ≤ (geoL r K).card + (geoR r K).card :=
    Finset.card_union_le _ _
  simp only [geoCharts]
  omega

end Work.WilG3
