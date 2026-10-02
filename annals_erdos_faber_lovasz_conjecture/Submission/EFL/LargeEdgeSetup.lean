import Submission.EFL.Reordering
import Submission.EFL.WeakStabilityMain

/-!
# Theorem 6.1 (`large-edge-thm`): the App-1 ingredients

The proof of the paper's Theorem 6.1 (Figure 3) applies the reordering lemma
(Lemma 6.2) three times, to

* `𝓗'  = 𝓗 ∖ 𝓗_huge` at `(τ₁, K₁) = (1 − γ₂/3, ⌈(2γ₂)⁻²⌉₊)`   ("App 1"),
* `𝓗₁^left` at `(3σ, 1)`                                        ("App 2"),
* `𝓗₃` at `(1 − 1/2000, 2000²)`                                 ("App 3"),

and combines the three orderings.  App 2 and App 3 are already fired in
`Reordering.lean` (`app2_firing`, `app3_firing`); this module supplies
App 1 (`app1_margins`, `app1_firing`) together with the numeric bounds on
the App-1 constants that Figure 3 uses, namely

* `sizeFactor τ₁ K₁ ≤ γ₂^{-10}`  (so `max_{W₁}|e| ≤ r₂/γ₂^{10}`) and
* `volBound τ₁ K₁ ≥ γ₂^{20}`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ErdosFaberLovaszConjecture

noncomputable section

/-- App-1 threshold: `τ₁ = 1 − γ₂/3`. -/
def app1tau (γ₂ : ℝ) : ℝ := 1 - γ₂ / 3

/-- App-1 reordering parameter: `K₁ = ⌈(2γ₂)⁻²⌉₊`. -/
def app1K (γ₂ : ℝ) : ℕ := ⌈(1 / (2 * γ₂)) ^ 2⌉₊

/-- The reordering margins of App 1. -/
theorem app1_margins {γ₂ : ℝ} (h0 : 0 < γ₂) (h1 : γ₂ ≤ 1 / 2000) {r₁ : ℕ}
    (hR : 4 * (1 / (2 * γ₂)) ^ 20 ≤ (r₁ : ℝ)) :
    ReorderingMargins r₁ (app1tau γ₂) (app1K γ₂) := by
  have hε0 : (0 : ℝ) < 2 * γ₂ := by linarith
  have hε1 : 2 * γ₂ ≤ 1 / 1000 := by linarith
  have h := weakStability_margins (ε := 2 * γ₂) (r₁ := r₁) hε0 hε1 hR
  have h2 : (1 : ℝ) - (2 * γ₂) / 6 = 1 - γ₂ / 3 := by ring
  rw [h2] at h
  simpa only [app1tau, app1K] using h

/-- **App-1 firing**: the reordering lemma applied to a subfamily
`𝓖 ⊆ 𝓗` at `(τ₁, K₁) = (1 − γ₂/3, ⌈(2γ₂)⁻²⌉₊)`.  In Figure 3,
`𝓖 := 𝓗' = 𝓗 ∖ 𝓗_huge`. -/
theorem app1_firing {n r₁ : ℕ} {γ₂ : ℝ} {𝓗 𝓖 : Hypergraph (Fin n)} (hsub : 𝓖 ⊆ 𝓗)
    (h2n : 2 ≤ n) (h2r1 : 2 ≤ r₁) (hγ0 : 0 < γ₂) (hγ1 : γ₂ ≤ 1 / 2000)
    (hR : 4 * (1 / (2 * γ₂)) ^ 20 ≤ (r₁ : ℝ))
    (hlin : 𝓗.IsLinear)
    (hsize : ∀ e : Set (Fin n), e ∈ 𝓗 → (r₁ : ℝ) ≤ edgeSize e) :
    ∃ k : ℕ, ∃ ord : 𝓖 ≃ Fin k,
      GoodOrdering (app1tau γ₂) ord ∨ VolumeWitness (app1tau γ₂) (app1K γ₂) ord := by
  have hτ0 : 0 < app1tau γ₂ := by simp only [app1tau]; linarith
  have hτ1 : app1tau γ₂ < 1 := by simp only [app1tau]; linarith
  have hK : (1 : ℕ) ≤ app1K γ₂ := by
    simp only [app1K]
    exact Nat.one_le_ceil_iff.mpr (by positivity)
  exact reorderingLemma_of_subfamily (r₁ := r₁) (τ := app1tau γ₂) (K := app1K γ₂) hsub
    h2n h2r1 hτ0 hτ1 hK (app1_margins hγ0 hγ1 hR) hlin hsize

/-- `K₁ ≤ (2γ₂)⁻² + 1` (the ceiling bound used by the numeric estimates). -/
lemma app1K_le {γ₂ : ℝ} (h0 : 0 < γ₂) :
    (app1K γ₂ : ℝ) ≤ (1 / (2 * γ₂)) ^ 2 + 1 := by
  have hpos : (0 : ℝ) < (1 / (2 * γ₂)) ^ 2 := by positivity
  have h : ((app1K γ₂ : ℕ) : ℝ) < (1 / (2 * γ₂)) ^ 2 + 1 := by
    simp only [app1K]; exact Nat.ceil_lt_add_one (le_of_lt hpos)
  linarith [h]

/-- `(K₁)⁴ ≤ γ₂^{-8}` for `γ₂ ≤ 1/2000`. -/
lemma app1K_pow_four_le {γ₂ : ℝ} (h0 : 0 < γ₂) (h1 : γ₂ ≤ 1 / 2000) :
    ((app1K γ₂ : ℕ) : ℝ) ^ 4 ≤ 1 / γ₂ ^ 8 := by
  have h25 : (0 : ℝ) < (1 / (2 * γ₂)) ^ 2 := by positivity
  have hKle : ((app1K γ₂ : ℕ) : ℝ) ≤ 2 * (1 / (2 * γ₂)) ^ 2 := by
    have h' : ((app1K γ₂ : ℕ) : ℝ) < (1 / (2 * γ₂)) ^ 2 + 1 :=
      Nat.ceil_lt_add_one (le_of_lt h25)
    have h2 : (1 : ℝ) ≤ (1 / (2 * γ₂)) ^ 2 := by
      have h3 : (1 : ℝ) ≤ 1 / (2 * γ₂) := by
        rw [le_div_iff₀ (by linarith : (0 : ℝ) < 2 * γ₂)]
        linarith
      nlinarith [h3]
    linarith
  have h4 : ((app1K γ₂ : ℕ) : ℝ) ^ 4 ≤ (2 * (1 / (2 * γ₂)) ^ 2) ^ 4 :=
    pow_le_pow_left₀ (by positivity) hKle 4
  have hmid : (2 * (1 / (2 * γ₂)) ^ 2) ^ 4 ≤ 1 / γ₂ ^ 8 := by
    have h16 : (2 * (1 / (2 * γ₂)) ^ 2) ^ 4 = 1 / (16 * γ₂ ^ 8) := by
      field_simp
      ring
    rw [h16]
    have hpos : (0 : ℝ) < γ₂ ^ 8 := pow_pos h0 8
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hpos]
  linarith [h4, hmid]

/-- **App-1 size factor bound**: `sizeFactor τ₁ K₁ ≤ γ₂^{-10}`.  This is
`(W₁1)` of Figure 3 (`max_{e∈W₁}|e| ≤ sizeFactor τ₁ K₁ · |e*₁|`). -/
theorem app1_sizeFactor_le {γ₂ : ℝ} (h0 : 0 < γ₂) (h1 : γ₂ ≤ 1 / 2000) :
    sizeFactor (app1tau γ₂) (app1K γ₂) ≤ 1 / γ₂ ^ 10 := by
  have hτ1 : app1tau γ₂ < 1 := by simp only [app1tau]; linarith
  have hτq_le : tauQuarter (app1tau γ₂) ≤ 1 := tauQuarter_le_one (le_of_lt hτ1)
  have hτq_nn : (0 : ℝ) ≤ tauQuarter (app1tau γ₂) := tauQuarter_nonneg _
  have hK4 := app1K_pow_four_le h0 h1
  have hdef : sizeFactor (app1tau γ₂) (app1K γ₂) =
      1 + 3 * tauQuarter (app1tau γ₂) * ((app1K γ₂ : ℕ) : ℝ) ^ 4 := rfl
  have h5 : 3 * tauQuarter (app1tau γ₂) * ((app1K γ₂ : ℕ) : ℝ) ^ 4 ≤ 3 / γ₂ ^ 8 := by
    have hτ3 : 3 * tauQuarter (app1tau γ₂) ≤ 3 := by linarith [hτq_le]
    have h := mul_le_mul hτ3 hK4 (by positivity : (0 : ℝ) ≤ ((app1K γ₂ : ℕ) : ℝ) ^ 4)
      (by norm_num : (0 : ℝ) ≤ 3)
    have h3' : (3 : ℝ) / γ₂ ^ 8 = 3 * (1 / γ₂ ^ 8) := by ring
    rw [h3']
    exact h
  have h6 : (1 : ℝ) + 3 / γ₂ ^ 8 ≤ 1 / γ₂ ^ 10 := by
    have hg8pos : (0 : ℝ) < γ₂ ^ 8 := pow_pos h0 8
    have hg8le : (1 : ℝ) ≤ 1 / γ₂ ^ 8 := by
      rw [le_div_iff₀ hg8pos]
      have : γ₂ ^ 8 ≤ 1 := pow_le_one₀ (le_of_lt h0) (by linarith)
      linarith
    have h1inv : (4 : ℝ) ≤ 1 / γ₂ ^ 2 := by
      rw [le_div_iff₀ (pow_pos h0 2)]
      have h2 : γ₂ ^ 2 ≤ (1 / 2000 : ℝ) ^ 2 := pow_le_pow_left₀ (le_of_lt h0) h1 2
      have h3 : (1 / 2000 : ℝ) ^ 2 ≤ 1 / 4 := by norm_num
      nlinarith [h2, h3]
    have hsplit : (1 : ℝ) / γ₂ ^ 10 = (1 / γ₂ ^ 8) * (1 / γ₂ ^ 2) := by
      field_simp
    have h1' : (1 : ℝ) + 3 * (1 / γ₂ ^ 8) ≤ 4 * (1 / γ₂ ^ 8) := by linarith [hg8le]
    have h2' : (4 : ℝ) * (1 / γ₂ ^ 8) ≤ (1 / γ₂ ^ 8) * (1 / γ₂ ^ 2) := by
      have hh := mul_le_mul_of_nonneg_left h1inv (by positivity : (0 : ℝ) ≤ 1 / γ₂ ^ 8)
      linarith [hh]
    have h3' : (3 : ℝ) / γ₂ ^ 8 = 3 * (1 / γ₂ ^ 8) := by ring
    rw [hsplit, h3']
    linarith [h1', h2']
  rw [hdef]
  linarith [h5, h6]

/-- **App-1 volume bound**: `volBound τ₁ K₁ ≥ γ₂^{20}` — this is `(W₁2)` of
Figure 3. -/
theorem app1_volBound_ge {γ₂ : ℝ} (h0 : 0 < γ₂) (h1 : γ₂ ≤ 1 / 2000) :
    γ₂ ^ 20 ≤ volBound (app1tau γ₂) (app1K γ₂) := by
  have hε0 : (0 : ℝ) < 2 * γ₂ := by linarith
  have hε1 : 2 * γ₂ ≤ 1 / 1000 := by linarith
  have h := weakStability_volBound_ge (ε := 2 * γ₂) hε0 hε1
  have h2 : (1 : ℝ) - (2 * γ₂) / 6 = 1 - γ₂ / 3 := by ring
  rw [h2] at h
  have h' : (2 * γ₂) ^ 10 / 14400 ≤ volBound (app1tau γ₂) (app1K γ₂) := by
    simpa only [app1tau, app1K] using h
  have h3 : γ₂ ^ 20 ≤ (2 * γ₂) ^ 10 / 14400 := by
    have h1024 : (2 * γ₂) ^ 10 = 1024 * γ₂ ^ 10 := by ring
    rw [h1024]
    have h20 : γ₂ ^ 20 = γ₂ ^ 10 * γ₂ ^ 10 := by ring
    rw [h20]
    have hg2 : γ₂ ^ 2 ≤ (1 / 2000 : ℝ) ^ 2 := pow_le_pow_left₀ (le_of_lt h0) h1 2
    have hg8 : γ₂ ^ 8 ≤ 1 := pow_le_one₀ (le_of_lt h0) (by linarith)
    have hg10 : γ₂ ^ 10 ≤ γ₂ ^ 2 := by
      have h : γ₂ ^ 10 = γ₂ ^ 2 * γ₂ ^ 8 := by ring
      nlinarith [h, hg8, pow_pos h0 2]
    have hsmall : γ₂ ^ 10 ≤ 1024 / 14400 := by
      have h2 : (1 / 2000 : ℝ) ^ 2 ≤ 1024 / 14400 := by norm_num
      linarith [hg10, hg2, h2]
    nlinarith [hsmall, pow_pos h0 10]
  linarith [h3, h']

end

end ErdosFaberLovaszConjecture
