import Submission.EFL.LargeEdgeHierarchy
import Submission.EFL.Case21
import Submission.EFL.Case21Margins

/-!
# Theorem 6.7 (`large-edge-thm`): the parameter hierarchy

This module assembles the paper's Theorem 6.1 (`large-edge-thm`,
`LargeEdgeThmStatement`) from the case analysis of `LargeEdgeCase22Main.lean`
(`largeEdge_of_blocks_full`) together with the numeric margins of
`LargeEdgeHierarchy.lean` and `Case21Margins.lean`.

The proof has two layers.

* `largeEdgeInstance_of_thresholds` is the *per-instance* layer: for fixed
  parameters `γ₂, δ, σ, γ₁, β` satisfying the hierarchy
  `0 < 1/n ≪ 1/r₀ ≪ 1/r₁, β ≪ γ₁ ≪ σ ≪ δ ≪ γ₂ ≪ 1` (in the precise
  threshold form `δ ≤ δThr γ₂`, `σ ≤ σThr δ`, `γ₁ ≤ γ₁Thr σ`,
  `β ≤ βThr γ₁`, `R₁Full ≤ r₁`, `R₀Full ≤ r₀`, `N₀Full ≤ n`), every linear
  hypergraph on `Fin n` with all edge sizes `> r₁` satisfies the conclusion
  of Theorem 6.7.  Its proof fires the two Reordering-Lemma applications
  (`exists_largeEdgeBlocks`), colours the medium edges with Kahn's theorem
  (`medEdges_colouring_of_kahn`), discharges all numeric margins with the
  `margin_*` lemmas and invokes `largeEdge_of_blocks_full`.

* `largeEdgeThmStatement_of_deep` is the *threshold* layer: it destructures
  the deep inputs `MolloyReedStatement`/`KahnStatement` (plus Lemma 5.1),
  chooses the thresholds `δ₀, σ₀, γ₁₀, β₀, R₁, R₀, N₀` in the order of the
  paper's `≪`-hierarchy and applies the first layer.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-! ## Elementary consequences of the threshold hierarchy -/

/-- `δThr γ ≤ γ` for `0 < γ ≤ 1`. -/
theorem δThr_le_self {γ : ℝ} (h0 : 0 < γ) (h1 : γ ≤ 1) : δThr γ ≤ γ := by
  have h2 : γ ^ 7 ≤ γ := by
    calc γ ^ 7 ≤ γ ^ 1 := pow_le_pow_of_le_one h0.le h1 (by norm_num)
      _ = γ := by ring
  simp only [δThr]
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 40)]
  nlinarith [h2, h0]

/-- `σThr δ ≤ 10⁻⁶` for `0 < δ ≤ 1`. -/
theorem σThr_le_inv_million {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    σThr δ ≤ 1 / 10 ^ 6 := by
  have h : δ ^ 12 ≤ 1 := pow_le_one₀ hδ0.le hδ1
  simp only [σThr]
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 6) (by norm_num : (0 : ℝ) < 10 ^ 6)]
  linarith

/-- `γ₁Thr σ ≤ σ/2` for `0 < σ ≤ 1`. -/
theorem γ₁Thr_le_half {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) : γ₁Thr σ ≤ σ / 2 := by
  have h : σ ^ 5 ≤ σ := by
    calc σ ^ 5 ≤ σ ^ 1 := pow_le_pow_of_le_one hσ0.le hσ1 (by norm_num)
      _ = σ := by ring
  simp only [γ₁Thr]
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 20) (by norm_num : (0 : ℝ) < 2)]
  nlinarith [h, hσ0]

/-- `γ₁Thr σ ≤ σ/4` for `0 < σ ≤ 1`. -/
theorem γ₁Thr_le_quarter {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) : γ₁Thr σ ≤ σ / 4 := by
  have h : σ ^ 5 ≤ σ := by
    calc σ ^ 5 ≤ σ ^ 1 := pow_le_pow_of_le_one hσ0.le hσ1 (by norm_num)
      _ = σ := by ring
  have h2 : σ ^ 4 ≤ 1 := pow_le_one₀ hσ0.le hσ1
  simp only [γ₁Thr]
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 20) (by norm_num : (0 : ℝ) < 4)]
  nlinarith only [h, h2, hσ0, hσ1]

/-- `γ₁Thr σ ≤ σ/2` for `0 < σ ≤ 1`. -/
theorem βThr_le_two_thirds {γ₁ : ℝ} (h0 : 0 < γ₁) (h1 : γ₁ ≤ 1) :
    βThr γ₁ ≤ 2 * γ₁ / 3 := by
  have h : γ₁ ^ 5 ≤ γ₁ := by
    calc γ₁ ^ 5 ≤ γ₁ ^ 1 := pow_le_pow_of_le_one h0.le h1 (by norm_num)
      _ = γ₁ := by ring
  have h2 : γ₁ ^ 5 / 10 ^ 20 ≤ γ₁ / 2 := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 20) (by norm_num : (0 : ℝ) < 2)]
    nlinarith [h]
  have h3 : γ₁ / 2 ≤ 2 * γ₁ / 3 := by linarith
  simpa only [βThr] using le_trans h2 h3

/-- `sizeFactor (3σ) 1 · √(n/(1−4σ)) ≤ (1+δ)√n` when `σ ≤ δ^{12}/10⁶`. -/
theorem margin_hfac {δ σ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hσ0 : 0 < σ)
    (hσ : σ ≤ δ ^ 12 / 10 ^ 6) {m : ℕ} :
    sizeFactor (3 * σ) 1 * Real.sqrt ((m : ℝ) / (1 - 4 * σ)) ≤ (1 + δ) * Real.sqrt (m : ℝ) := by
  have hσ4 : 4 * σ ≤ 1 / 2 := by
    have h2 : δ ^ 12 ≤ 1 := pow_le_one₀ hδ0.le hδ1
    have h3 : σ ≤ 1 / 10 ^ 6 := by nlinarith [hσ, h2, hσ0]
    linarith
  have hpos : (0 : ℝ) < 1 - 4 * σ := by linarith
  have hs := sizeFactor_three_sigma_le hδ0 hδ1 hσ0 hσ
  have hsp : (0 : ℝ) < Real.sqrt (1 - 4 * σ) := Real.sqrt_pos.mpr hpos
  have hdiv : Real.sqrt ((m : ℝ) / (1 - 4 * σ)) = Real.sqrt (m : ℝ) / Real.sqrt (1 - 4 * σ) :=
    Real.sqrt_div (x := (m : ℝ)) (Nat.cast_nonneg m) (1 - 4 * σ)
  rw [hdiv]
  have hm : (0 : ℝ) ≤ Real.sqrt (m : ℝ) := Real.sqrt_nonneg _
  have h1 : sizeFactor (3 * σ) 1 / Real.sqrt (1 - 4 * σ) ≤
      (1 + δ) * Real.sqrt (1 - 4 * σ) / Real.sqrt (1 - 4 * σ) := by
    rw [div_le_div_iff_of_pos_right hsp]
    exact hs
  have h2 : (1 + δ) * Real.sqrt (1 - 4 * σ) / Real.sqrt (1 - 4 * σ) = 1 + δ := by
    field_simp
  calc sizeFactor (3 * σ) 1 * (Real.sqrt (m : ℝ) / Real.sqrt (1 - 4 * σ))
      = (sizeFactor (3 * σ) 1 / Real.sqrt (1 - 4 * σ)) * Real.sqrt (m : ℝ) := by ring
    _ ≤ ((1 + δ) * Real.sqrt (1 - 4 * σ) / Real.sqrt (1 - 4 * σ)) * Real.sqrt (m : ℝ) :=
        mul_le_mul_of_nonneg_right h1 hm
    _ = (1 + δ) * Real.sqrt (m : ℝ) := by rw [h2]

/-- `2n/((γ₁/2)(r₁−1)) < ((γ₂/3)n)/4` for `r₁ ≥ 100/(γ₂γ₁)`. -/
theorem margin_m22₃ {γ₁ γ₂ : ℝ} (hγ₁0 : 0 < γ₁) (hγ₁1 : γ₁ ≤ 1) (hγ₂0 : 0 < γ₂)
    (hγ₂1 : γ₂ ≤ 1) {r₁ m : ℕ} (h : 100 / (γ₂ * γ₁) ≤ (r₁ : ℝ)) (hm0 : 0 < m) :
    2 * (m : ℝ) / ((γ₁ / 2) * ((r₁ : ℝ) - 1)) < ((γ₂ / 3) * (m : ℝ)) / 4 := by
  have hm0' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
  have hpos : (0 : ℝ) < γ₂ * γ₁ := mul_pos hγ₂0 hγ₁0
  have hγ₂γ₁1 : γ₂ * γ₁ ≤ 1 := by nlinarith [hγ₂0, hγ₂1, hγ₁0, hγ₁1]
  have hr₁100 : 100 ≤ (r₁ : ℝ) := by
    have h2 := mul_le_mul_of_nonneg_right h (le_of_lt hpos)
    have h1 : 100 / (γ₂ * γ₁) * (γ₂ * γ₁) = 100 := by field_simp
    have h3 : (r₁ : ℝ) * (γ₂ * γ₁) ≤ (r₁ : ℝ) := by
      calc (r₁ : ℝ) * (γ₂ * γ₁) ≤ (r₁ : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left hγ₂γ₁1 (Nat.cast_nonneg r₁)
        _ = (r₁ : ℝ) := by ring
    linarith
  have h100 : 100 ≤ γ₂ * γ₁ * (r₁ : ℝ) := by
    have h2 := mul_le_mul_of_nonneg_right h (le_of_lt hpos)
    have h1 : 100 / (γ₂ * γ₁) * (γ₂ * γ₁) = 100 := by field_simp
    linarith [h2, h1]
  have hr₁ : 48 < γ₂ * γ₁ * ((r₁ : ℝ) - 1) := by nlinarith [h100, hγ₂γ₁1]
  have hden : (0 : ℝ) < (γ₁ / 2) * ((r₁ : ℝ) - 1) := by nlinarith [hr₁100, hγ₁0]
  rw [div_lt_div_iff₀ hden (by norm_num : (0 : ℝ) < 4)]
  have hstep : 48 * (m : ℝ) < γ₂ * γ₁ * ((r₁ : ℝ) - 1) * (m : ℝ) :=
    mul_lt_mul_of_pos_right hr₁ hm0'
  nlinarith [hstep]



/-- **The `bigFinset` count at an arbitrary ratio.**  In a linear family on
`Fin m` there are fewer than `c·m` edges of size at least `βm/10`, provided
`m ≥ 401/(2β²c)` (and `m ≥ 20/β`). -/
theorem margin_bigFinset_ratio {β c : ℝ} (hβ0 : 0 < β) (hc : 0 < c) {m : ℕ}
    {𝓖 : Hypergraph (Fin m)} [Fintype 𝓖] (hlin : 𝓖.IsLinear)
    (h : 401 / (β ^ 2 * (2 * c)) ≤ (m : ℝ)) (h2 : 20 / β ≤ (m : ℝ)) :
    (((bigFinset (β / 5) 𝓖).card : ℕ) : ℝ) < c * (m : ℝ) := by
  have h' := margin_bigFinset (β := β) (σ := 2 * c) (m := m) hβ0 (by positivity) hlin h h2
  rwa [show (2 * c) * (m : ℝ) / 2 = c * (m : ℝ) by ring] at h'

/-! ## The thresholds of the hierarchy -/

/-- The `r₁`-threshold of Theorem 6.7: large enough for the App-1 reordering
margins, the Case-2.1/2.2 ratio margins in `r₁`, Proposition 6.10's
`32/γ₁³ + 8/γ₁² + 8/γ₁`, the `10⁸` bound of `hr₃big` and the Case-2.1
`10⁷/δ` bound. -/
def R₁Full (γ₂ γ₁ δ : ℝ) : ℕ :=
  ⌈4 * (1 / (2 * γ₂)) ^ 20⌉₊ + ⌈100 / (γ₂ * γ₁)⌉₊ + 10 ^ 8 + 10
  + ⌈32 / γ₁ ^ 3 + 8 / γ₁ ^ 2 + 8 / γ₁⌉₊ + ⌈10 ^ 7 / δ⌉₊

/-- The `r₀`-threshold of Theorem 6.7. -/
def R₀Full (σ β δ : ℝ) : ℕ :=
  ⌈1000 / (σ * β)⌉₊ + ⌈280001 / β ^ 2⌉₊ + ⌈1000001 / β⌉₊ + 10
  + ⌈3 * 10 ^ 5 / (β ^ 2 * δ)⌉₊

/-- The `n`-threshold of Theorem 6.7: large enough for every `n`-margin. -/
def N₀Full (nLN r₁ r₀ : ℕ) (D₀K C : ℝ) (m : ℕ) (β γ₂ σ δ γ₁ : ℝ) : ℕ :=
  ⌈8 / δ ^ 2⌉₊ + ⌈16 / δ ^ 2⌉₊ + ⌈16 / β ^ 2⌉₊ + ⌈64 / β ^ 2⌉₊ + ⌈64 / β ^ 2 + 4⌉₊
  + ⌈3 / γ₂⌉₊ + ⌈20 / β⌉₊ + ⌈10 / β⌉₊ + ⌈8 / β⌉₊ + ⌈128 / β ^ 2⌉₊
  + ⌈(4 * (r₀ : ℝ) / γ₂ ^ 10) ^ 2⌉₊ + ⌈4 * ((r₀ : ℝ) + 1) / β⌉₊
  + ⌈32 / (β ^ 2 * σ)⌉₊ + ⌈512 / (β ^ 2 * σ)⌉₊ + ⌈401 / (β ^ 2 * σ)⌉₊
  + ⌈802 / (β ^ 2 * σ)⌉₊ + ⌈1604 / (β ^ 2 * σ)⌉₊ + ⌈2406000 / β ^ 2⌉₊
  + ⌈16 / σ ^ 2⌉₊ + 1000000 + nLN + ⌈C * (6 / (5 * δ)) ^ m⌉₊
  + ⌈D₀K * ((r₁ : ℝ) - 1)⌉₊ + ⌈2 / γ₁⌉₊ + 24000

theorem R₁Full_pos (γ₂ γ₁ δ : ℝ) : 0 < R₁Full γ₂ γ₁ δ := by simp only [R₁Full]; omega
theorem R₀Full_pos (σ β δ : ℝ) : 0 < R₀Full σ β δ := by simp only [R₀Full]; omega
theorem N₀Full_pos (nLN r₁ r₀ : ℕ) (D₀K C : ℝ) (m : ℕ) (β γ₂ σ δ γ₁ : ℝ) :
    0 < N₀Full nLN r₁ r₀ D₀K C m β γ₂ σ δ γ₁ := by simp only [N₀Full]; omega


/-- **The per-instance layer of Theorem 6.7.**  For fixed parameters satisfying
the threshold hierarchy `δ ≤ δThr γ₂`, `σ ≤ σThr δ`, `γ₁ ≤ γ₁Thr σ`,
`β ≤ βThr γ₁`, `R₁Full ≤ r₁`, `R₀Full ≤ r₀`, `N₀Full ≤ n`, every linear
hypergraph on `Fin n` with all edge sizes `> r₁` satisfies the conclusion of
Theorem 6.7. -/
theorem largeEdgeInstance_of_thresholds
    {n r₁ r₀ nLN : ℕ} {Δ₀ : ℝ → ℝ} {D₀K C : ℝ} {m : ℕ} {β γ₂ σ δ γ₁ : ℝ}
    (hC : 0 < C)
    (hΔ₀bnd : ∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → Δ₀ ζ' ≤ C / ζ' ^ m)
    (hMRe : ∀ (ζ' : ℝ), 0 < ζ' → ζ' ≤ 1 → ∀ (V : Type) [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℝ), Δ₀ ζ' ≤ Δ →
        (G.maxDegree : ℝ) ≤ Δ →
        (∀ v : V, (nbrEdges G v : ℝ) ≤ (1 - ζ') * Δ ^ 2 / 2) →
        ∃ k : ℕ, (k : ℝ) ≤ (1 - ζ' / Real.exp 6) * Δ ∧ G.Colorable k)
    (hK : ∀ D : ℝ, D₀K ≤ D → ∀ (m' : ℕ) (𝓖 : Hypergraph (Fin m')), 𝓖.IsLinear →
      ((hypergraphMaxDegree 𝓖 : ℕ) : ℝ) ≤ D →
      (∀ e : 𝓖, (edgeSize (e : Set (Fin m')) : ℝ) ≤ (r₀ : ℝ)) →
      ∀ c : ℕ, 2 * D ≤ (c : ℝ) → 𝓖.Colorable c)
    (hLN : ∀ m' : ℕ, nLN ≤ m' → ∀ 𝓖 : Hypergraph (Fin m'), 𝓖.IsLinear →
      (∀ e : Set (Fin m'), e ∈ 𝓖 → (1 - δ) * Real.sqrt (m' : ℝ) ≤ (edgeSize e : ℝ)) →
      ∃ φ : 𝓖.Coloring (Fin m'), ∀ c : Fin m', (φ.colorClass c).ncard ≤ 2)
    (hβ : 0 < β) (hγ₂0 : 0 < γ₂) (hγ₂1 : γ₂ ≤ 1 / 4000)
    (hδ0 : 0 < δ) (hδThr : δ ≤ δThr γ₂) (hδbig : δ ≤ 1 / 10 ^ 4)
    (hσ0 : 0 < σ) (hσThr : σ ≤ σThr δ)
    (hγ₁0 : 0 < γ₁) (hγ₁Thr : γ₁ ≤ γ₁Thr σ)
    (hβThr : β ≤ βThr γ₁)
    (hmarg₂ : ReorderingMargins r₁ (3 * σ) 1)
    (hR₁ : R₁Full γ₂ γ₁ δ ≤ r₁) (hR₀ : R₀Full σ β δ ≤ r₀)
    (hN₀ : N₀Full nLN r₁ r₀ D₀K C m β γ₂ σ δ γ₁ ≤ n) :
    ∀ (𝓗 : Hypergraph (Fin n)), (∀ e : 𝓗, (r₁ : ℝ) < (edgeSize (e : Set (Fin n)) : ℝ)) →
      𝓗.IsLinear →
      LargeEdgeNonExtremal n σ γ₁ β (r₁ : ℝ) (r₀ : ℝ) 𝓗 ∨
        LargeEdgeExtremal n δ γ₂ γ₁ β (r₁ : ℝ) (r₀ : ℝ) 𝓗 := by
  classical
  -- ## 1. Elementary consequences of the threshold hierarchy
  have hδ1 : δ ≤ 1 := by linarith only [hδbig]
  have hδhalf : δ ≤ 1 / 2 := by linarith only [hδbig]
  have hδ256 : δ ≤ 1 / 256 := by linarith only [hδbig]
  have hδ16 : δ ≤ 1 / 16 := by linarith only [hδbig]
  have hδ1e3 : δ ≤ 1 / 10 ^ 3 := by linarith only [hδbig]
  have hγ₂2000 : γ₂ ≤ 1 / 2000 := by linarith only [hγ₂1]
  have hγ₂1' : γ₂ ≤ 1 := by linarith only [hγ₂1]
  have hγ₂12 : γ₂ ≤ 1 / 2 := by linarith only [hγ₂1]
  have hγ₂34 : γ₂ ≤ 3 / 4 := by linarith only [hγ₂1]
  have hγ₂38 : γ₂ ≤ 3 / 8 := by linarith only [hγ₂1]
  have hσ1e6 : σ ≤ 1 / 10 ^ 6 := le_trans hσThr (σThr_le_inv_million hδ0 hδ1)
  have hσ4 : 4 * σ ≤ 1 / 2 := by linarith only [hσ1e6]
  have hσ16 : σ ≤ 1 / 6 := by linarith only [hσ1e6]
  have hσ18 : σ ≤ 1 / 8 := by linarith only [hσ1e6]
  have hσ12 : σ ≤ 1 / 2 := by linarith only [hσ1e6]
  have hσ1 : σ ≤ 1 := by linarith only [hσ1e6]
  have hσ31 : 3 * σ ≤ 1 := by linarith only [hσ1e6]
  have hσ100k : 3 * σ ≤ 1 / 10000 := by linarith only [hσ1e6]
  have hγ₁σ : γ₁ ≤ σ / 2 := le_trans hγ₁Thr (γ₁Thr_le_half hσ0 hσ1)
  have hγ₁σ' : γ₁ ≤ σ := by linarith only [hγ₁σ, hσ0, hσ1e6]
  have hγ₁1 : γ₁ ≤ 1 := by linarith only [hγ₁σ, hσ1e6]
  have hγ₁half : γ₁ ≤ 1 / 2 := by linarith only [hγ₁σ, hσ1e6]
  have hγ₁2000 : γ₁ ≤ 1 / 2000 := by linarith only [hγ₁σ, hσ1e6]
  have hβγ₁ : β ≤ γ₁ := le_trans hβThr (βThr_le hγ₁0 hγ₁1)
  have hβ1 : β ≤ 1 := le_trans hβγ₁ hγ₁1
  -- ## 2. The `r₁`, `r₀` and `n` margins
  have hR₁ℝ : ((R₁Full γ₂ γ₁ δ : ℕ) : ℝ) ≤ (r₁ : ℝ) := by exact_mod_cast hR₁
  have hR₀ℝ : ((R₀Full σ β δ : ℕ) : ℝ) ≤ (r₀ : ℝ) := by exact_mod_cast hR₀
  have hN₀ℝ : ((N₀Full nLN r₁ r₀ D₀K C m β γ₂ σ δ γ₁ : ℕ) : ℝ) ≤ (n : ℝ) :=
    by exact_mod_cast hN₀
  have happ1 : 4 * (1 / (2 * γ₂)) ^ 20 ≤ (r₁ : ℝ) := by
    have h : ⌈4 * (1 / (2 * γ₂)) ^ 20⌉₊ ≤ R₁Full γ₂ γ₁ δ := by
      simp only [R₁Full]; omega
    exact le_trans (Nat.le_ceil _) (le_trans (by exact_mod_cast h) hR₁ℝ)
  have h100γ₂γ₁ : 100 / (γ₂ * γ₁) ≤ (r₁ : ℝ) := by
    have h : ⌈100 / (γ₂ * γ₁)⌉₊ ≤ R₁Full γ₂ γ₁ δ := by simp only [R₁Full]; omega
    exact le_trans (Nat.le_ceil _) (le_trans (by exact_mod_cast h) hR₁ℝ)
  have hr₁thr : 32 / γ₁ ^ 3 + 8 / γ₁ ^ 2 + 8 / γ₁ ≤ (r₁ : ℝ) := by
    have h : ⌈32 / γ₁ ^ 3 + 8 / γ₁ ^ 2 + 8 / γ₁⌉₊ ≤ R₁Full γ₂ γ₁ δ := by
      simp only [R₁Full]; omega
    exact le_trans (Nat.le_ceil _) (le_trans (by exact_mod_cast h) hR₁ℝ)
  have hr₁δ : 10 ^ 7 / δ ≤ (r₁ : ℝ) := by
    have h : ⌈10 ^ 7 / δ⌉₊ ≤ R₁Full γ₂ γ₁ δ := by simp only [R₁Full]; omega
    exact le_trans (Nat.le_ceil _) (le_trans (by exact_mod_cast h) hR₁ℝ)
  have hr₁108 : (100000000 : ℝ) ≤ (r₁ : ℝ) := by
    have h : (10 : ℕ) ^ 8 ≤ R₁Full γ₂ γ₁ δ := by simp only [R₁Full]; omega
    have h2 : ((10 : ℕ) ^ 8 : ℝ) ≤ ((R₁Full γ₂ γ₁ δ : ℕ) : ℝ) := by exact_mod_cast h
    have h3 : ((10 : ℕ) ^ 8 : ℝ) = (100000000 : ℝ) := by norm_num
    linarith only [h2, h3.le, h3.ge, hR₁ℝ]
  have h2r₁ : 2 ≤ r₁ := by
    have h : (2 : ℝ) ≤ (r₁ : ℝ) := by linarith only [hr₁108]
    exact_mod_cast h
  have h1000σβ : 1000 / (σ * β) ≤ (r₀ : ℝ) := by
    have h : ⌈1000 / (σ * β)⌉₊ ≤ R₀Full σ β δ := by simp only [R₀Full]; omega
    exact le_trans (Nat.le_ceil _) (le_trans (by exact_mod_cast h) hR₀ℝ)
  have h1000001β : 1000001 / β ≤ (r₀ : ℝ) := by
    have h : ⌈1000001 / β⌉₊ ≤ R₀Full σ β δ := by simp only [R₀Full]; omega
    exact le_trans (Nat.le_ceil _) (le_trans (by exact_mod_cast h) hR₀ℝ)
  have h3e5 : 3 * 10 ^ 5 / (β ^ 2 * δ) ≤ (r₀ : ℝ) := by
    have h : ⌈3 * 10 ^ 5 / (β ^ 2 * δ)⌉₊ ≤ R₀Full σ β δ := by simp only [R₀Full]; omega
    exact le_trans (Nat.le_ceil _) (le_trans (by exact_mod_cast h) hR₀ℝ)
  have hr₀10 : (10 : ℝ) ≤ (r₀ : ℝ) := by
    have h : (10 : ℕ) ≤ R₀Full σ β δ := by simp only [R₀Full]; omega
    have h2 : (10 : ℝ) ≤ ((R₀Full σ β δ : ℕ) : ℝ) := by exact_mod_cast h
    linarith only [h2, hR₀ℝ]
  have hr₀1 : 1 ≤ r₀ := by
    have h2 : (1 : ℝ) ≤ (r₀ : ℝ) := by linarith only [hr₀10]
    exact_mod_cast h2
  have h2r₀ : 2 ≤ r₀ := by
    have h2 : (2 : ℝ) ≤ (r₀ : ℝ) := by linarith only [hr₀10]
    exact_mod_cast h2
  have h8δ : 8 / δ ^ 2 ≤ (n : ℝ) := ceil_le_of_le (by simp only [N₀Full]; omega) hN₀
  have h16δ : 16 / δ ^ 2 ≤ (n : ℝ) := ceil_le_of_le (by simp only [N₀Full]; omega) hN₀
  have h16β : 16 / β ^ 2 ≤ (n : ℝ) := ceil_le_of_le (by simp only [N₀Full]; omega) hN₀
  have h64β : 64 / β ^ 2 ≤ (n : ℝ) := ceil_le_of_le (by simp only [N₀Full]; omega) hN₀
  have h64β4 : 64 / β ^ 2 + 4 ≤ (n : ℝ) := ceil_le_of_le (by simp only [N₀Full]; omega) hN₀
  have h128β : 128 / β ^ 2 ≤ (n : ℝ) := ceil_le_of_le (by simp only [N₀Full]; omega) hN₀
  have h3γ₂ : 3 / γ₂ ≤ (n : ℝ) := ceil_le_of_le (by simp only [N₀Full]; omega) hN₀
  have h20β : 20 / β ≤ (n : ℝ) := ceil_le_of_le (by simp only [N₀Full]; omega) hN₀
  have h10β : 10 / β ≤ (n : ℝ) := ceil_le_of_le (by simp only [N₀Full]; omega) hN₀
  have h8β : 8 / β ≤ (n : ℝ) := ceil_le_of_le (by simp only [N₀Full]; omega) hN₀
  have hr₀sq : (4 * (r₀ : ℝ) / γ₂ ^ 10) ^ 2 ≤ (n : ℝ) :=
    ceil_le_of_le (by simp only [N₀Full]; omega) hN₀
  have h4r₀β : 4 * ((r₀ : ℝ) + 1) / β ≤ (n : ℝ) :=
    ceil_le_of_le (by simp only [N₀Full]; omega) hN₀
  have h32βσ : 32 / (β ^ 2 * σ) ≤ (n : ℝ) :=
    ceil_le_of_le (by simp only [N₀Full]; omega) hN₀
  have h512βσ : 512 / (β ^ 2 * σ) ≤ (n : ℝ) :=
    ceil_le_of_le (by simp only [N₀Full]; omega) hN₀
  have h401βσ : 401 / (β ^ 2 * σ) ≤ (n : ℝ) :=
    ceil_le_of_le (by simp only [N₀Full]; omega) hN₀
  have h1604βσ : 1604 / (β ^ 2 * σ) ≤ (n : ℝ) :=
    ceil_le_of_le (by simp only [N₀Full]; omega) hN₀
  have h802βσ : 802 / (β ^ 2 * σ) ≤ (n : ℝ) :=
    ceil_le_of_le (by simp only [N₀Full]; omega) hN₀
  have h2406000β : 2406000 / β ^ 2 ≤ (n : ℝ) :=
    ceil_le_of_le (by simp only [N₀Full]; omega) hN₀
  have h16σ : 16 / σ ^ 2 ≤ (n : ℝ) := ceil_le_of_le (by simp only [N₀Full]; omega) hN₀
  have hC6 : C * (6 / (5 * δ)) ^ m ≤ (n : ℝ) :=
    ceil_le_of_le (by simp only [N₀Full]; omega) hN₀
  have hD₀Kn : D₀K * ((r₁ : ℝ) - 1) ≤ (n : ℝ) :=
    ceil_le_of_le (by simp only [N₀Full]; omega) hN₀
  have h2γ₁ : 2 / γ₁ ≤ (n : ℝ) := ceil_le_of_le (by simp only [N₀Full]; omega) hN₀
  have hn4 : (4 : ℕ) ≤ n := le_trans (by simp only [N₀Full]; omega : (4 : ℕ) ≤ _) hN₀
  have hnLN : nLN ≤ n := le_trans (by simp only [N₀Full]; omega : nLN ≤ _) hN₀
  have hn24000 : 24000 ≤ n := le_trans (by simp only [N₀Full]; omega : (24000:ℕ) ≤ _) hN₀
  have hn1000000 : 1000000 ≤ n := le_trans (by simp only [N₀Full]; omega : (1000000:ℕ) ≤ _) hN₀
  -- ## 3. The App-1 and App-2 firings and the `1 − δ³` volume bound
  have hmarg₁ : ReorderingMargins r₁ (app1tau γ₂) (app1K γ₂) := app1_margins hγ₂0 hγ₂2000 happ1
  have hV₂ : (1 : ℝ) - δ ^ 3 ≤ volBound (3 * σ) 1 := volBound_three_sigma_ge hδ0 hδ1 hσ0 hσThr
  have hδV : δ ≤ volBound app3tau app3K := δThr_le_app3 hγ₂0 hγ₂1' hδThr
  have hV₁ : δ ^ 3 < volBound (app1tau γ₂) (app1K γ₂) :=
    app1_volBound_gt hγ₂0 hγ₂2000 hδ0 hδThr
  have hfac : sizeFactor (3 * σ) 1 * Real.sqrt ((n : ℝ) / (1 - 4 * σ)) ≤
      (1 + δ) * Real.sqrt (n : ℝ) := margin_hfac hδ0 hδ1 hσ0 hσThr
  -- ## 4. The numeric margins
  have hβγ : 2 * (β * (n : ℝ) / 4) + β * (n : ℝ) / 4 + (γ₁ / 2) * (n : ℝ) ≤ γ₁ * (n : ℝ) := by
    have h2 : β ≤ 2 * γ₁ / 3 := le_trans hβThr (βThr_le_two_thirds hγ₁0 hγ₁1)
    nlinarith only [h2, (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
  have hσβ1 : σ * β ≤ 1 := by nlinarith only [hσ1e6, hβ1, hσ0, hβ]
  have h2σn : 2 ≤ σ * (n : ℝ) := by
    have h : 2 / σ ≤ (n : ℝ) := by
      have h1 : 2 / σ ≤ 16 / σ ^ 2 := by
        rw [div_le_div_iff₀ hσ0 (by positivity : (0 : ℝ) < σ ^ 2)]
        nlinarith only [hσ0, hσ1e6]
      linarith only [h1, h16σ]
    rw [div_le_iff₀ hσ0] at h
    linarith only [h]
  have h12σn : 12 ≤ σ * (n : ℝ) := by
    have h : 12 / σ ≤ (n : ℝ) := by
      have h1 : 12 / σ ≤ 16 / σ ^ 2 := by
        rw [div_le_div_iff₀ hσ0 (by positivity : (0 : ℝ) < σ ^ 2)]
        nlinarith only [hσ0, hσ1e6]
      linarith only [h1, h16σ]
    rw [div_le_iff₀ hσ0] at h
    linarith only [h]
  have h16βn : 16 ≤ β ^ 2 * (n : ℝ) := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < β ^ 2)] at h16β
    linarith only [h16β]
  have hn2 : 2 ≤ n := by
    have h : (2 : ℕ) ≤ N₀Full nLN r₁ r₀ D₀K C m β γ₂ σ δ γ₁ := by
      simp only [N₀Full]; omega
    omega
  intro 𝓗 hsize hlin
  rcases Set.eq_empty_or_nonempty 𝓗 with hemp | hne
  · rw [hemp]
    exact Or.inl (largeEdgeNonExtremal_empty (by linarith only [hσ1e6]) hγ₁0.le hβ.le)
  · obtain ⟨e, he⟩ := hne
    have hrn_lt : r₁ < n := by
      have h1 : (r₁ : ℝ) < (edgeSize (e : Set (Fin n)) : ℝ) := hsize ⟨e, he⟩
      have h2 : (r₁ : ℝ) < (n : ℝ) := lt_of_lt_of_le h1 (by exact_mod_cast edgeSize_le e)
      exact_mod_cast h2
    have hn : 0 < n := by omega
    have h2n : 2 ≤ n := by omega
    have hn1 : 1 ≤ n := by omega
    have hsizeR : ∀ e : 𝓗, (r₁ : ℝ) ≤ (edgeSize (e : Set (Fin n)) : ℝ) :=
      fun e => le_of_lt (hsize e)
    have hsizeN : ∀ e : 𝓗, r₁ ≤ edgeSize (e : Set (Fin n)) := fun e => by
      exact_mod_cast hsizeR e
    -- ## 5. Firing App 1 and App 2 (Figure 3)
    obtain ⟨Good₁, Left₁, Good₂, Left₂, W₂, H₃, k₁, ord₁, k₂, ord₂, r₂, r₃, hB⟩ :=
      exists_largeEdgeBlocks (n := n) (r₁ := r₁) (β := β) (γ₂ := γ₂) (σ := σ) (δ := δ)
        (𝓗 := 𝓗) hβ hγ₂0 hγ₂2000 hσ0 (by linarith only [hσ100k])
        hδ0 (by linarith only [hδbig]) h2n h2r₁ hmarg₁ hmarg₂ hV₂ hlin hsizeR
    -- ## 6. The medium edges (Proposition 6.10 via Kahn)
    have hsize_med : ∀ e : 𝓗.medEdges r₁ r₀, edgeSize (e : Set (Fin n)) ≤ r₀ := by
      intro e
      exact ((mem_medEdges 𝓗 r₁ r₀ (e : Set (Fin n))).mp e.2).2.2
    have hDthr : D₀K ≤ (n : ℝ) / ((r₁ : ℝ) - 1) := by
      have hr₁1 : (1 : ℝ) < (r₁ : ℝ) := by
        have h : (1 : ℕ) < r₁ := by omega
        exact_mod_cast h
      rw [le_div_iff₀ (by linarith only [hr₁1])]
      exact hD₀Kn
    have hγ₁n : 2 ≤ γ₁ * (n : ℝ) := by
      rw [div_le_iff₀ hγ₁0] at h2γ₁
      linarith only [h2γ₁]
    obtain ⟨Cmed, φmed, hφmed, hCmedcard, hmedbα⟩ :=
      medEdges_colouring_of_kahn (r₁ := r₁) (r₀ := r₀) (γ₁ := γ₁) (D₀ := D₀K)
        hK hγ₁0 hγ₁half h2n h2r₁ hr₁thr hγ₁n hlin (fun e he => hsizeN ⟨e, he⟩) hsize_med hDthr
    -- ## 7. The instance-dependent margins
    have hβn : (r₀ : ℝ) < β * (n : ℝ) / 4 := margin_r0_lt hβ h4r₀β
    have hr₀γ₁n : (r₀ : ℝ) ≤ γ₁ * (n : ℝ) := by
      have h1 : β * (n : ℝ) / 4 ≤ γ₁ * (n : ℝ) := by
        have hb : β / 4 ≤ γ₁ := by linarith only [hβγ₁, hβ]
        calc β * (n : ℝ) / 4 = (β / 4) * (n : ℝ) := by ring
          _ ≤ γ₁ * (n : ℝ) := mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg n)
      linarith only [hβn, h1]
    have hmedb : ∀ c : Fin n, (φmed.classVertexCount c : ℝ) ≤ γ₁ * (n : ℝ) := by
      intro c
      have h := classVertexCount_le_of_alphaBounded (M := (r₀ : ℝ)) (c := c) φmed hmedbα
        (by positivity : (0 : ℝ) ≤ γ₁ * (n : ℝ))
        (fun e _ => by exact_mod_cast hsize_med e)
      rwa [max_eq_left hr₀γ₁n] at h
    have hsubG₂ : Good₂ ⊆ 𝓗 := fun e he => nonHuge_subset 𝓗 β (hB.hL₁sub (hB.hG₂sub he))
    have hsubH₃ : case2H3med r₁ r₀ 𝓗 H₃ ⊆ 𝓗 := fun e he => hB.hH₃sub he.1
    have hb22₂ : (((bigFinset (β / 5) Good₂).card : ℕ) : ℝ) < σ * (n : ℝ) / 2 := by
      have h := margin_bigFinset_ratio (β := β) (c := σ / 2) (m := n) hβ (by positivity)
        (IsLinear.mono hsubG₂ hlin) ?_ h20β
      · rw [show σ / 2 * (n : ℝ) = σ * (n : ℝ) / 2 by ring] at h; exact h
      · rw [show 2 * (σ / 2) = σ by ring]; exact h401βσ
    have hb22₃ : (((bigFinset (γ₁ / 2) Good₁).card : ℕ) : ℝ) < ((γ₂ / 3) * (n : ℝ)) / 2 := by
      have hemp : bigFinset (γ₁ / 2) Good₁ = ∅ :=
        bigFinset_eq_empty_of_nonHuge hβ hβγ₁
          (fun e => not_le.mp (hB.hG₁sub e.2).2)
      rw [hemp, Finset.card_empty]
      push_cast
      have h1 : (0 : ℝ) < γ₂ * (n : ℝ) := by
        have h := mul_pos hγ₂0 (show (0 : ℝ) < (n : ℝ) by exact_mod_cast hn)
        linarith only [h]
      linarith only [h1]
    have h69b : (((bigFinset (β / 5) (case2H3med r₁ r₀ 𝓗 H₃)).card : ℕ) : ℝ) <
        ((1 / 6000 : ℝ) * (n : ℝ)) / 2 :=
      (by
        have h := margin_bigFinset_ratio (β := β) (c := 1 / 12000) (m := n) hβ
          (by norm_num) (IsLinear.mono hsubH₃ hlin) ?_ h20β
        · rw [show 1 / 12000 * (n : ℝ) = (1 / 6000 : ℝ) * (n : ℝ) / 2 by ring] at h
          exact h
        · rw [show β ^ 2 * (2 * (1 / 12000)) = β ^ 2 / 6000 by ring,
            show 401 / (β ^ 2 / 6000) = 2406000 / β ^ 2 by ring]
          exact h2406000β)
    have hsubCR : case2Right r₁ r₀ 𝓗 Good₁ Good₂ ⊆ 𝓗 := by
      intro e he
      rw [case2Right] at he
      rcases he.1 with hg₂ | hg₁
      · exact nonHuge_subset 𝓗 β (hB.hL₁sub (hB.hG₂sub hg₂))
      · exact nonHuge_subset 𝓗 β (hB.hG₁sub hg₁)
    have h69bσ : (((bigFinset (β / 5) (case2Right r₁ r₀ 𝓗 Good₁ Good₂)).card : ℕ) : ℝ) <
        ((σ / 4) * (n : ℝ)) / 2 :=
      (by
        have h := margin_bigFinset_ratio (β := β) (c := σ / 8) (m := n) hβ (by positivity)
          (IsLinear.mono hsubCR hlin) ?_ h20β
        · rw [show σ / 8 * (n : ℝ) = (σ / 4) * (n : ℝ) / 2 by ring] at h
          exact h
        · rw [show β ^ 2 * (2 * (σ / 8)) = β ^ 2 * σ / 4 by ring,
            show 401 / (β ^ 2 * σ / 4) = 1604 / (β ^ 2 * σ) by ring]
          exact h1604βσ)
    have hbudget : (Cmed.card : ℝ) + 1 ≤ (σ / 2) * (n : ℝ) := by
      have hγ₁q : γ₁ ≤ σ / 4 := le_trans hγ₁Thr (γ₁Thr_le_quarter hσ0 hσ1)
      have h1 : (Cmed.card : ℝ) ≤ (σ / 4) * (n : ℝ) := by
        have h2 : γ₁ * (n : ℝ) ≤ (σ / 4) * (n : ℝ) :=
          mul_le_mul_of_nonneg_right hγ₁q (Nat.cast_nonneg n)
        linarith only [hCmedcard, h2]
      have h4σn : (4 : ℝ) ≤ σ * (n : ℝ) := by
        have h32 : (4 : ℝ) ≤ 32 / β ^ 2 := by
          rw [le_div_iff₀ (by positivity : (0 : ℝ) < β ^ 2)]
          nlinarith only [hβ, hβ1]
        have hσn' := margin_sigma_n hβ hσ0 h32βσ
        linarith only [h32, hσn']
      have h3 : (1 : ℝ) ≤ (σ / 4) * (n : ℝ) := by nlinarith only [h4σn]
      have h4 : (σ / 4) * (n : ℝ) < (σ / 2) * (n : ℝ) := by
        have h5 := mul_lt_mul_of_pos_left (by linarith only [hσ0] : σ / 4 < σ / 2)
          (show (0 : ℝ) < (n : ℝ) by exact_mod_cast hn)
        linarith only [h5]
      linarith only [h1, h3, h4]
    have hbig : (((bigFinset (β / 5) (𝓗.largeEdges r₀)).card : ℕ) : ℝ) <
        ((σ / 2) * (n : ℝ)) / 2 :=
      (by
        have h := margin_bigFinset_ratio (β := β) (c := σ / 4) (m := n) hβ (by positivity)
          (IsLinear.mono (largeEdges_subset 𝓗 r₀) hlin) ?_ h20β
        · rw [show σ / 4 * (n : ℝ) = (σ / 2) * (n : ℝ) / 2 by ring] at h
          exact h
        · rw [show β ^ 2 * (2 * (σ / 4)) = β ^ 2 * σ / 2 by ring,
            show 401 / (β ^ 2 * σ / 2) = 802 / (β ^ 2 * σ) by ring]
          exact h802βσ)
    -- ## 8. The conclusion
    rcases largeEdge_of_blocks_full (Δ₀ := Δ₀) (C := C) (m := m) hC hΔ₀bnd hMRe hB
      hσ4 hβ1 (margin_bigcase hσ0 hσ16 h16σ) hLN hnLN hγ₁0 hδ16
      hfac (margin_sq_mul hδ0 h8δ) (margin_sqrt hδ0 hδ1 h16δ) (margin_huge hδ0 hβ hδhalf h16β)
      (margin_roomNat hβ hγ₂0 hγ₂12 h64β4)
      (margin_m22₂ hσ0 hβ hσβ1 h1000σβ hn)
      hb22₂
      (margin_m22₃ hγ₁0 hγ₁1 hγ₂0 hγ₂1' h100γ₂γ₁ hn)
      hb22₃
      (margin_gamma2n hγ₂0 h3γ₂)
      hV₁ hγ₂2000
      (margin_r0h hγ₂0 hδhalf hr₀1 hr₀sq)
      hβγ hlin hn h2n hβ hγ₂0 hσ0 hδ0 hδ256 hγ₁σ hσ31 hr₀1 h2r₀ h2r₁ hr₁108 hsize hδV
      (margin_69m hβ hβ1 h1000001β hn)
      h69b
      (margin_69mσ hσ0 hβ hσβ1 h1000σβ hn)
      h69bσ
      (margin_hnbig2 hδ0 hδ1 h16δ)
      (margin_σsmall2 hσ0 hσ1e6 hn24000)
      (margin_two_beta5 hβ h10β)
      hδ1e3 hr₁δ
      (margin_sqrt4 hβ h16βn)
      (margin_alphaδ hδ0 hδbig hσ0 hσThr)
      hC6
      (margin_k2δ hδ0 hδbig hσ0 hσThr)
      (margin_marginAδ hβ hδ0 hβ1 h3e5 hn)
      (margin_2σδ hδ0 hδ1 hσ0 hσThr)
      (margin_room1C hγ₁0 hγ₁2000 Cmed hCmedcard (by omega))
      (margin_room2C hγ₁0 hσ0 hγ₁σ' Cmed hCmedcard h2σn)
      (margin_budgetC hσ0 h12σn)
      (margin_beta_n hβ h8β)
      hn1
      (margin_sigma_n hβ hσ0 h32βσ)
      (margin_gamma_m hβ hσ0 hγ₂34 hσ18 h64β)
      (margin_Kroom hσ0 hσ12 hγ₁0 (by linarith only [hγ₁σ, hσ0]) Cmed hCmedcard)
      (margin_slack hβ hβ1 hσ0 h512βσ)
      hβn
      (margin_sigma_n hβ hσ0 h32βσ)
      (margin_A2 hβ hσ0 hγ₂38 hσ18 h128β)
      (margin_margin hσ0 hβ hσβ1 h1000σβ hn)
      hbig
      hCmedcard hφmed hmedb hbudget with h | h
    · exact Or.inl h
    · exact Or.inr h

/-- Kahn's theorem in the list-free `α = 1` form consumed by
`medEdges_colouring_of_kahn`. -/
theorem kahn_two (hK : KahnStatement) {r : ℕ} (hr : 2 ≤ r) :
    ∃ D₀ : ℝ, 0 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
      ∀ (m : ℕ) (𝓖 : Hypergraph (Fin m)), 𝓖.IsLinear →
      ((hypergraphMaxDegree 𝓖 : ℕ) : ℝ) ≤ D →
      (∀ e : 𝓖, (edgeSize (e : Set (Fin m)) : ℝ) ≤ (r : ℝ)) →
      ∀ c : ℕ, 2 * D ≤ (c : ℝ) → 𝓖.Colorable c := by
  obtain ⟨D₀, hD₀, h⟩ := kahn_colorable hK (α := 1) (r := r) (by norm_num) hr
  refine ⟨D₀, hD₀, fun D hD m 𝓖 hlin hdeg hsize c hc => ?_⟩
  exact h D hD m 𝓖 hlin hdeg hsize c (by
    rw [show ((1 : ℝ) + 1) = 2 by norm_num]; exact hc)

/-- **Theorem 6.7 (`large-edge-thm`) from the deep inputs.**  The threshold
layer of the proof: the thresholds `δ₀, σ₀, γ₁₀, β₀` of the paper's
`≪`-hierarchy are chosen from `γ₂` (and from the thresholds of the deep inputs
Molloy–Reed, Kahn and Lemma 5.1), and `R₁, R₀, N₀` from the preceding
parameters; then `largeEdgeInstance_of_thresholds` is applied. -/
theorem largeEdgeThmStatement_of_deep (hMR : MolloyReedStatement) (hK : KahnStatement) :
    LargeEdgeThmStatement := by
  classical
  intro γ₂ hγ₂0 hγ₂1
  obtain ⟨Δ₀, _hΔ₀pos, ⟨C, hC, m, hΔ₀bnd⟩, hMRe⟩ := hMR
  obtain ⟨δ₀LN, hδ₀LNpos, hLNpre⟩ := nearfullColouring_exists
  set γ₂' : ℝ := min γ₂ (1 / 4000) with hγ₂'def
  have hγ₂'0 : 0 < γ₂' := lt_min hγ₂0 (by norm_num)
  have hγ₂'le : γ₂' ≤ γ₂ := min_le_left _ _
  have hγ₂'4000 : γ₂' ≤ 1 / 4000 := min_le_right _ _
  have hγ₂'1 : γ₂' ≤ 1 := by linarith only [hγ₂'4000]
  have hγ₂'2000 : γ₂' ≤ 1 / 2000 := by linarith only [hγ₂'4000]
  have hδ₀LNs : 0 < δ₀LN / 2 := by linarith only [hδ₀LNpos]
  refine ⟨min (δThr γ₂') (min (δ₀LN / 2) (1 / 10 ^ 4)), ?_, ?_, ?_⟩
  · exact lt_min (by simp only [δThr]; positivity) (lt_min hδ₀LNs (by norm_num))
  · exact le_trans (min_le_left _ _) (le_trans (δThr_le_self hγ₂'0 hγ₂'1) hγ₂'le)
  · intro δ hδ0 hδle
    have hδThr : δ ≤ δThr γ₂' := le_trans hδle (min_le_left _ _)
    have hδLN : δ ≤ δ₀LN := by
      have h1 := le_trans hδle (le_trans (min_le_right _ _) (min_le_left _ _))
      linarith only [h1, hδ₀LNpos]
    have hδbig : δ ≤ 1 / 10 ^ 4 := by
      have h1 := le_trans hδle (le_trans (min_le_right _ _) (min_le_right _ _))
      exact h1
    have hδ1 : δ ≤ 1 := by linarith only [hδbig]
    obtain ⟨nLN, hLN₀⟩ := hLNpre δ hδ0 hδLN
    refine ⟨σThr δ, (by simp only [σThr]; positivity), σThr_le hδ0 hδ1, ?_⟩
    intro σ hσ0 hσle
    have hσThr : σ ≤ σThr δ := hσle
    have hσ1 : σ ≤ 1 := le_trans hσThr (le_trans (σThr_le hδ0 hδ1) hδ1)
    have hσ1e6 : σ ≤ 1 / 10 ^ 6 := le_trans hσThr (σThr_le_inv_million hδ0 hδ1)
    have hσ3 : 3 * σ ≤ 1 / 10000 := by linarith only [hσ1e6]
    refine ⟨min (γ₁Thr σ) (σ / 2),
      lt_min (by simp only [γ₁Thr]; positivity) (by linarith only [hσ0]),
      le_trans (min_le_left _ _) (le_trans (γ₁Thr_le_half hσ0 hσ1) (by linarith only [hσ0])), ?_⟩
    intro γ₁ hγ₁0 hγ₁le
    have hγ₁Thr : γ₁ ≤ γ₁Thr σ := le_trans hγ₁le (min_le_left _ _)
    have hγ₁half : γ₁ ≤ σ / 2 := le_trans hγ₁le (min_le_right _ _)
    have hγ₁1 : γ₁ ≤ 1 := by linarith only [hγ₁half, hσ1e6]
    refine ⟨βThr γ₁, (by simp only [βThr]; positivity), βThr_le hγ₁0 hγ₁1, ?_⟩
    intro β hβ0 hβle
    have hβThr : β ≤ βThr γ₁ := hβle
    obtain ⟨Rapp, hRapp⟩ := app2_margins hσ0 hσ3
    refine ⟨R₁Full γ₂' γ₁ δ + Rapp, by simp only [R₁Full]; omega, ?_⟩
    intro r₁ hr₁
    have hR₁ : R₁Full γ₂' γ₁ δ ≤ r₁ := by omega
    have hRapp' : (Rapp : ℕ) ≤ r₁ := by omega
    have hmarg₂ : ReorderingMargins r₁ (3 * σ) 1 := hRapp r₁ (by exact_mod_cast hRapp')
    have hr₁1 : (10 : ℕ) ≤ r₁ := by
      have h : (10 : ℕ) ≤ R₁Full γ₂' γ₁ δ := by simp only [R₁Full]; omega
      omega
    have h2r₁ : 2 ≤ r₁ := by omega
    refine ⟨R₀Full σ β δ, by simp only [R₀Full]; omega, ?_⟩
    intro r₀ hr₀
    have hR₀ : R₀Full σ β δ ≤ r₀ := hr₀
    have h2r₀ : 2 ≤ r₀ := by
      have h : (10 : ℕ) ≤ R₀Full σ β δ := by simp only [R₀Full]; omega
      omega
    obtain ⟨D₀K, _hD₀K0, hKtwo⟩ := kahn_two hK (r := r₀) h2r₀
    refine ⟨N₀Full nLN r₁ r₀ D₀K C m β γ₂' σ δ γ₁,
      (by simp only [N₀Full]; omega), ?_⟩
    intro n hn 𝓗 hsize hlin
    rcases largeEdgeInstance_of_thresholds (n := n) (r₁ := r₁) (r₀ := r₀) (nLN := nLN)
      (Δ₀ := Δ₀) (D₀K := D₀K) (C := C) (m := m) (β := β) (γ₂ := γ₂') (σ := σ) (δ := δ)
      (γ₁ := γ₁) hC hΔ₀bnd hMRe hKtwo hLN₀ hβ0 hγ₂'0 hγ₂'4000 hδ0 hδThr hδbig hσ0 hσThr
      hγ₁0 hγ₁Thr hβThr hmarg₂ hR₁ hR₀ hn 𝓗 hsize hlin with h | h
    · exact Or.inl h
    · exact Or.inr (LargeEdgeExtremal_mono_γ₂ hγ₂'le h)

end

end ErdosFaberLovaszConjecture
