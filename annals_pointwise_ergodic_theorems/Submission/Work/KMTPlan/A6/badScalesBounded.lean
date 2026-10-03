import Mathlib
import Submission.Work.KMTPlan.A6.MdlAdelicDefs
import Submission.Work.KMTPlan.A6.PieceBoundedH.badScalesBounded

namespace Work.KMTPlan.A6

/-- **The bad (`¬ goodScale`) scales are bounded, uniformly in the quadruple of height `≤ B`.**

At bounded height `lcL l₁ l₂ k₁ k₂ = max (max l₁ l₂) (max k₁ k₂) ≤ B` the `goodScale` threshold
`8 · arithQ ρ (max l₁ l₂) · 2^{lcL l₁ l₂ k₁ k₂ + 1}` is bounded by the *quadruple-independent*
constant `C := 8 · Qmax · 2^{B+1}`, where `Qmax` dominates `arithQ ρ k` for all `k ≤ B`
(this is the only place where the bound on the heights is used).  Since a `Λ`-lacunary sequence
grows geometrically, `⌊a n⌋ ≥ C` for all `n ≥ K Λ`, and the index threshold
`K Λ = ⌊log X / log Λ + 2⌋` with `X = C + 1` depends on `Λ` only
(`Work.KMTAreas.A7.lacunary_index_bound`). -/
theorem badScalesBounded (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (B : ℕ) :
    ∃ K : NNReal → NNReal, ∀ (Λ : NNReal) (hΛ : 1 < Λ) (a : ℕ → NNReal)
      (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
      (l₁ l₂ k₁ k₂ : ℕ), Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ ≤ B → ∀ n : ℕ, K Λ ≤ n →
      Work.KMTPlan.A6.goodScale (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
        (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) (Nat.floor (a n)) := by
  -- the uniform arithmetic threshold
  set Qmax : ℕ := (Finset.range (B + 1)).sup (fun k => Work.KMTAreas.A7.arithQ ρ k) with hQmax
  set C : ℕ := 8 * Qmax * 2 ^ (B + 1) with hC
  set X : ℝ := (C : ℝ) + 1 with hX
  have hX1 : (1 : ℝ) ≤ X := by
    rw [hX]
    have : (0 : ℝ) ≤ (C : ℝ) := Nat.cast_nonneg C
    linarith
  -- the index threshold, depending on `Λ` alone
  let K : NNReal → NNReal :=
    fun Λ => ((⌊Real.log X / Real.log ((Λ : NNReal) : ℝ) + 2⌋₊ : ℕ) : NNReal)
  refine ⟨K, ?_⟩
  intro Λ hΛ a ha ha1 l₁ l₂ k₁ k₂ hL n hn
  -- the lacunary index bound at the level `X`
  obtain ⟨K₀, hK₀le, hK₀spec⟩ :=
    Work.KMTAreas.A7.lacunary_index_bound Λ hΛ a ha ha1 X hX1
  have hmn : ⌊Real.log X / Real.log ((Λ : NNReal) : ℝ) + 2⌋₊ ≤ n := by
    have h := hn
    simp only [K] at h
    exact_mod_cast h
  have hK₀m : K₀ ≤ ⌊Real.log X / Real.log ((Λ : NNReal) : ℝ) + 2⌋₊ := Nat.le_floor hK₀le
  -- hence the scale exceeds the threshold
  have hanX : X ≤ (a n : ℝ) := by
    by_contra hcon
    have hcon' : (a n : ℝ) < X := not_le.mp hcon
    have : n < K₀ := hK₀spec n hcon'
    omega
  have hCfloor : C ≤ Nat.floor (a n) := by
    have hlt : (C : ℝ) < (a n : ℝ) := by rw [hX] at hanX; linarith
    have hCnn : (C : NNReal) < a n := by exact_mod_cast hlt
    exact Nat.le_floor hCnn.le
  -- the threshold is at most `C`
  have hmax : max l₁ l₂ ≤ B := by
    have h1 : max l₁ l₂ ≤ Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ := by
      rw [Work.KMTPlan.A6.lcL]; exact le_max_left _ _
    omega
  have hQle : Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) ≤ Qmax := by
    rw [hQmax]
    exact Finset.le_sup (f := fun k => Work.KMTAreas.A7.arithQ ρ k)
      (by rw [Finset.mem_range]; omega)
  have hp : 2 ^ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ + 1) ≤ 2 ^ (B + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hconst : 8 * Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)
      * 2 ^ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ + 1) ≤ C :=
    calc 8 * Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)
          * 2 ^ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ + 1)
        ≤ 8 * Qmax * 2 ^ (B + 1) := Nat.mul_le_mul (Nat.mul_le_mul_left 8 hQle) hp
      _ = C := by rw [hC]
  exact hconst.trans hCfloor

end Work.KMTPlan.A6
