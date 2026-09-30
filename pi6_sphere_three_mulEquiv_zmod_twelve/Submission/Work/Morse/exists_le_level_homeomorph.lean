import Mathlib

open scoped Manifold ContDiff Topology

namespace Work.Morse

/-- Given reals `A < q < p < B`, there is a strictly increasing homeomorphism of `ℝ` fixing
`(-∞,A]` and `[B,∞)` pointwise, with `ψ ≤ id` everywhere, and sending `p` to `q`. -/
theorem exists_le_level_homeomorph {A q p B : ℝ} (hAq : A < q) (hqp : q < p) (hpB : p < B) :
    ∃ ψ : ℝ ≃ₜ ℝ, StrictMono ψ ∧ ψ p = q ∧ (∀ s, ψ s ≤ s) ∧
      (∀ s ≤ A, ψ s = s) ∧ (∀ s ≥ B, ψ s = s) := by
  have hAp : A < p := lt_trans hAq hqp
  have hpa : 0 < p - A := by linarith
  have hbp : 0 < B - p := by linarith
  set u : ℝ := (q - A) / (p - A) with hu
  set v : ℝ := (B - q) / (B - p) with hv
  have hu_pos : 0 < u := by rw [hu]; exact div_pos (by linarith) hpa
  have hu_lt_one : u < 1 := by rw [hu, div_lt_one hpa]; linarith
  have hv_gt_one : 1 < v := by rw [hv, one_lt_div hbp]; linarith
  have huv : u < v := lt_trans hu_lt_one hv_gt_one
  have hu_eq : (p - A) * u = q - A := by
    rw [hu, mul_comm]; exact div_mul_cancel₀ (q - A) (ne_of_gt hpa)
  have hv_eq : (B - p) * v = B - q := by
    rw [hv, mul_comm]; exact div_mul_cancel₀ (B - q) (ne_of_gt hbp)
  let L : ℝ → ℝ := fun s => A + (s - A) * u
  let R : ℝ → ℝ := fun s => q + (s - p) * v
  let g : ℝ → ℝ := fun s => max (L s) (R s)
  let f : ℝ → ℝ := fun s => min s (g s)
  have hLp : L p = q := by simp only [L]; rw [hu_eq]; ring
  have hRp : R p = q := by simp only [R]; ring
  have hRB : q + (B - p) * v = B := by rw [hv_eq]; ring
  have hLR : ∀ s, L s - R s = (v - u) * (p - s) := by
    intro s
    have h : L s - R s = (L s - L p) - (R s - R p) := by rw [hLp, hRp]; ring
    have hLs : L s - L p = (s - p) * u := by simp only [L]; ring
    have hRs : R s - R p = (s - p) * v := by simp only [R]; ring
    rw [h, hLs, hRs]; ring
  have hR_le_L : ∀ s, s ≤ p → R s ≤ L s := by
    intro s hs
    have h1 : 0 ≤ (v - u) * (p - s) := mul_nonneg (by linarith) (by linarith)
    linarith [hLR s, h1]
  have hL_le_R : ∀ s, p ≤ s → L s ≤ R s := by
    intro s hs
    have h1 : (v - u) * (p - s) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    linarith [hLR s, h1]
  have hL_ge_self : ∀ s, s ≤ A → s ≤ L s := by
    intro s hs
    have hLs : L s - s = (s - A) * (u - 1) := by simp only [L]; ring
    have h1 : 0 ≤ (s - A) * (u - 1) :=
      mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    linarith
  have hR_ge_self : ∀ s, B ≤ s → s ≤ R s := by
    intro s hs
    have hRs : R s - s = (s - B) * (v - 1) := by simp only [R]; nlinarith [hRB]
    have h1 : 0 ≤ (s - B) * (v - 1) := mul_nonneg (by linarith) (by linarith)
    linarith
  have hg_L : ∀ s, s ≤ p → g s = L s := by
    intro s hs; simp only [g]; exact max_eq_left (hR_le_L s hs)
  have hg_R : ∀ s, p ≤ s → g s = R s := by
    intro s hs; simp only [g]; exact max_eq_right (hL_le_R s hs)
  have hf_le_A : ∀ s ≤ A, f s = s := by
    intro s hs
    have hgs : s ≤ g s := by
      rw [hg_L s (le_trans hs (le_of_lt hAp))]
      exact hL_ge_self s hs
    simp only [f]; exact min_eq_left hgs
  have hf_ge_B : ∀ s ≥ B, f s = s := by
    intro s hs
    have hgs : s ≤ g s := by
      rw [hg_R s (le_trans (le_of_lt hpB) hs)]
      exact hR_ge_self s hs
    simp only [f]; exact min_eq_left hgs
  have hf_p : f p = q := by
    have hgp : g p = q := by rw [hg_L p le_rfl, hLp]
    simp only [f]; rw [hgp]; exact min_eq_right (le_of_lt hqp)
  have hf_le_id : ∀ s, f s ≤ s := by intro s; simp only [f]; exact min_le_left _ _
  have hLmono : StrictMono L := by
    intro a b hab
    have h : 0 < (b - a) * u := mul_pos (by linarith) hu_pos
    simp only [L]; nlinarith
  have hRmono : StrictMono R := by
    intro a b hab
    have h : 0 < (b - a) * v := mul_pos (by linarith) (by linarith)
    simp only [R]; nlinarith
  have hgmono : StrictMono g := by
    intro a b hab
    simp only [g]
    exact max_lt_max (hLmono hab) (hRmono hab)
  have hfmono : StrictMono f := by
    intro a b hab
    have hga := hgmono hab
    simp only [f]
    rcases le_total a (g a) with h | h
    · rw [min_eq_left h]; exact lt_min hab (lt_of_le_of_lt h hga)
    · rw [min_eq_right h]; exact lt_min (lt_of_le_of_lt h hab) hga
  have hcontL : Continuous L := by
    simp only [L]
    exact continuous_const.add ((continuous_id.sub continuous_const).mul continuous_const)
  have hcontR : Continuous R := by
    simp only [R]
    exact continuous_const.add ((continuous_id.sub continuous_const).mul continuous_const)
  have hcontg : Continuous g := by
    simp only [g]; exact hcontL.max hcontR
  have hcontf : Continuous f := by
    simp only [f]; exact continuous_id.min hcontg
  have hIV : Set.Icc (f A) (f B) ⊆ f '' Set.Icc A B :=
    intermediate_value_Icc (a := A) (b := B) (by linarith : A ≤ B) hcontf.continuousOn
  have hsurj : Function.Surjective f := by
    intro y
    by_cases hyA : y ≤ A
    · exact ⟨y, hf_le_A y hyA⟩
    · have hyA' : A < y := lt_of_not_ge hyA
      by_cases hyB : B ≤ y
      · exact ⟨y, hf_ge_B y hyB⟩
      · have hyB' : y < B := lt_of_not_ge hyB
        have hy : y ∈ Set.Icc (f A) (f B) := by
          rw [hf_le_A A le_rfl, hf_ge_B B le_rfl]
          exact ⟨le_of_lt hyA', le_of_lt hyB'⟩
        rcases hIV hy with ⟨c, _, hc⟩
        exact ⟨c, hc⟩
  let e : ℝ ≃o ℝ := StrictMono.orderIsoOfSurjective f hfmono hsurj
  let ψ : ℝ ≃ₜ ℝ := e
  have hψ : ⇑ψ = f := rfl
  exact ⟨ψ, by rw [hψ]; exact hfmono, by rw [hψ]; exact hf_p,
    fun s => by rw [hψ]; exact hf_le_id s, fun s hs => by rw [hψ]; exact hf_le_A s hs,
    fun s hs => by rw [hψ]; exact hf_ge_B s hs⟩

end Work.Morse
