import Submission.EFL.S12Setup
import Submission.EFL.MedEdges

/-!
# §12: the numerical plumbing of the assembly

The parametrised statements of §12 (`s12_step4`--`s12_step7`, `s12_mbound`,
`s12_uc`, `s12_uc1`) all carry a handful of numerical hypotheses that follow
from the paper's hierarchy `1/n ≪ 1/r₀ ≪ ξ ≪ 1/r₁ ≪ β ≪ κ ≪ γ ≪ ε ≪ ρ ≪ 1`
together with `D = ⌊(1-ρ)(n-1)⌋` and `D' = ⌊10γ^{1/2}D⌋`.  This module records
those derivations, so that the final assembly only has to instantiate the
parameters.

The main declarations are

* `Dparam_ge_sub` (`⌊x⌋ ≥ x - 1` for `x = (1-ρ)(n-1)`);
* `n_le_two_Dparam` (`n ≤ 2D` for `ρ ≤ 1/4`, `n ≥ 8`), and its consequences
  `two_thirds_beta_le` (`2βD ≥ (2/3)βn + 2`) and `EP2num_le`
  (`r₁n/(r₀-1) ≤ 2βD`);
* `D'param_ge_half` (`10γ^{1/2}D/2 ≤ D'` when `10γ^{1/2}D ≥ 2`);
* `four_gamma_le_sqrt` (`4γ ≤ 100γ^{1/2}` for `γ ≤ 625`) and
  `overlap_le_gamma_mul` (`r₁n/(r₀-1) ≤ γD` for `2r₁ ≤ γ(r₀-1)`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-- `D = ⌊(1-ρ)(n-1)⌋` is at least `(1-ρ)(n-1) - 1`. -/
theorem Dparam_ge_sub (n : ℕ) (ρ : ℝ) :
    (1 - ρ) * ((n : ℝ) - 1) - 1 ≤ (Dparam n ρ : ℝ) := by
  have := Nat.lt_floor_add_one ((1 - ρ) * ((n : ℝ) - 1))
  rw [Dparam]
  linarith

/-- `D ≥ n/2` in the form `n ≤ 2D`, for `ρ ≤ 1/4` and `n ≥ 8`. -/
theorem n_le_two_Dparam {ρ : ℝ} (hρ : ρ ≤ 1 / 4) (hn : 8 ≤ n) :
    (n : ℝ) ≤ 2 * (Dparam n ρ : ℝ) := by
  have h1 := Dparam_ge_sub n ρ
  have hn8 : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  nlinarith

/-- `2βD ≥ (2/3)βn + 2` when `βn ≥ 6` and `n ≤ 2D`. -/
theorem two_thirds_beta_le {β : ℝ} {D : ℕ} (hβ0 : 0 ≤ β) (hβn : 6 ≤ β * (n : ℝ))
    (hD : (n : ℝ) ≤ 2 * (D : ℝ)) : 2 / 3 * β * (n : ℝ) + 2 ≤ 2 * β * (D : ℝ) := by
  nlinarith

/-- `r₁n/(r₀-1) ≤ 2βD` when `r₁ ≤ β(r₀-1)` and `n ≤ 2D`. -/
theorem EP2num_le {β : ℝ} {r₁ r₀ D : ℕ} (hr₀ : 2 ≤ r₀) (hβ0 : 0 ≤ β)
    (h : (r₁ : ℝ) ≤ β * ((r₀ : ℝ) - 1))
    (hD : (n : ℝ) ≤ 2 * (D : ℝ)) :
    (r₁ : ℝ) * (n : ℝ) / ((r₀ : ℝ) - 1) ≤ 2 * β * (D : ℝ) := by
  have hr₀' : (0 : ℝ) < (r₀ : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (r₀ : ℝ) := by exact_mod_cast hr₀
    linarith
  have h1 : (r₁ : ℝ) * (n : ℝ) / ((r₀ : ℝ) - 1) ≤ β * (n : ℝ) := by
    rw [div_le_iff₀ hr₀']
    nlinarith
  nlinarith

/-- `r₁n/(r₀-1) ≤ γD` when `2r₁ ≤ γ(r₀-1)` and `n ≤ 2D`. -/
theorem overlap_le_gamma_mul {γ : ℝ} {r₁ r₀ D : ℕ} (hr₀ : 2 ≤ r₀)
    (h : 2 * (r₁ : ℝ) ≤ γ * ((r₀ : ℝ) - 1)) (hD : (n : ℝ) ≤ 2 * (D : ℝ)) :
    (r₁ : ℝ) * (n : ℝ) / ((r₀ : ℝ) - 1) ≤ γ * (D : ℝ) := by
  have hr₀' : (0 : ℝ) < (r₀ : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (r₀ : ℝ) := by exact_mod_cast hr₀
    linarith
  have h1 : (r₁ : ℝ) * (n : ℝ) / ((r₀ : ℝ) - 1) ≤ γ / 2 * (n : ℝ) := by
    rw [div_le_iff₀ hr₀']
    nlinarith
  nlinarith

/-- `D' = ⌊10γ^{1/2}D⌋ ≥ 10γ^{1/2}D/2` when `10γ^{1/2}D ≥ 2`. -/
theorem D'param_ge_half (D : ℕ) (γ : ℝ) (h : 2 ≤ 10 * Real.sqrt γ * (D : ℝ)) :
    10 * Real.sqrt γ * (D : ℝ) / 2 ≤ (D'param D γ : ℝ) := by
  have := Nat.lt_floor_add_one (10 * Real.sqrt γ * (D : ℝ))
  rw [D'param]
  linarith

/-- `4γ ≤ 100γ^{1/2}` for `0 ≤ γ ≤ 625`. -/
theorem four_gamma_le_sqrt {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ ≤ 625) :
    4 * γ ≤ 100 * Real.sqrt γ := by
  have hsq := Real.sq_sqrt hγ0
  have hs := Real.sqrt_nonneg γ
  nlinarith


/-! ## The degree of a vertex in terms of `hypergraphDegree`, and the bound
for the large edges -/

/-- `MultiHypergraph.hdeg` and `hypergraphDegree` are the same number. -/
theorem hdeg_eq_hypergraphDegree (𝓖 : Hypergraph (Fin n)) (v : Fin n) :
    MultiHypergraph.hdeg 𝓖 v = hypergraphDegree 𝓖 v := by
  classical
  rw [MultiHypergraph.hdeg, hypergraphDegree, ← Nat.card_coe_set_eq]
  refine Nat.card_congr ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨e, he, hve⟩
    exact ⟨⟨e, he⟩, hve⟩
  · rintro ⟨⟨e, he⟩, hve⟩
    exact ⟨e, he, hve⟩
  · rintro ⟨e, he, hve⟩
    rfl
  · rintro ⟨⟨e, he⟩, hve⟩
    rfl

/-- A vertex is incident to at most `2n/r₀` edges of size more than `r₀`
(linearity: `d_{𝓗_large}(w) ≤ (n-1)/(r₀-1) ≤ 2n/r₀`). -/
theorem hdeg_largeEdges_le {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear) {r₀ : ℕ}
    (hr₀ : 2 ≤ r₀) (w : Fin n) :
    (MultiHypergraph.hdeg (𝓗.largeEdges r₀) w : ℝ) ≤ 2 * (n : ℝ) / (r₀ : ℝ) := by
  rw [hdeg_eq_hypergraphDegree]
  have hsize : ∀ e ∈ 𝓗.largeEdges r₀, r₀ ≤ edgeSize e :=
    fun e he => le_of_lt ((mem_largeEdges 𝓗 r₀ e).mp he).2
  have hlinL : (𝓗.largeEdges r₀).IsLinear := IsLinear.mono' (largeEdges_subset 𝓗 r₀) hlin
  have h := degree_mul_le (𝓗 := 𝓗.largeEdges r₀) (r := r₀) hlinL hsize w
  have h4 : ((hypergraphDegree (𝓗.largeEdges r₀) w * (r₀ - 1) : ℕ) : ℝ) ≤
      ((n - 1 : ℕ) : ℝ) := by exact_mod_cast h
  rw [Nat.cast_mul, Nat.cast_sub (show 1 ≤ r₀ by omega), Nat.cast_one] at h4
  have h5 : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.sub_le n 1
  have h6 : (0 : ℝ) < (r₀ : ℝ) := by
    have : (0 : ℕ) < r₀ := by omega
    exact_mod_cast this
  have hr₀' : (2 : ℝ) ≤ (r₀ : ℝ) := by exact_mod_cast hr₀
  have hdeg0 : (0 : ℝ) ≤ (hypergraphDegree (𝓗.largeEdges r₀) w : ℝ) := Nat.cast_nonneg _
  rw [le_div_iff₀ h6]
  nlinarith [h4, h5, hr₀', hdeg0]


/-- The degree decomposition used by UC1: if every edge of `𝓗_final` outside
`R_final` is a large edge (and `R_final` consists of 2-edges), then
`d_{𝓗_final}(w) ≤ d_{R_final}(w) + d_{𝓗_large}(w)`. -/
theorem hdeg_sub_le_degAt_add {𝓗 𝓗fin R_final : Hypergraph (Fin n)} {r₀ : ℕ}
    (hRpow : R_final ⊆ 𝓗.pow2)
    (h : ∀ e ∈ 𝓗fin, e ∉ R_final → e ∈ 𝓗.largeEdges r₀) (w : Fin n) :
    MultiHypergraph.hdeg 𝓗fin w ≤
      degAt R_final w + MultiHypergraph.hdeg (𝓗.largeEdges r₀) w := by
  have hsub : ({e ∈ 𝓗fin | w ∈ e} : Set (Set (Fin n))) ⊆
      ({e ∈ R_final | w ∈ e} : Set (Set (Fin n))) ∪ {e ∈ 𝓗.largeEdges r₀ | w ∈ e} := by
    rintro e ⟨hefin, hwe⟩
    by_cases hR : e ∈ R_final
    · exact Or.inl ⟨hR, hwe⟩
    · exact Or.inr ⟨h e hefin hR, hwe⟩
  have h1 : ({e ∈ 𝓗fin | w ∈ e} : Set (Set (Fin n))).ncard ≤
      ({e ∈ R_final | w ∈ e} : Set (Set (Fin n))).ncard +
        ({e ∈ 𝓗.largeEdges r₀ | w ∈ e} : Set (Set (Fin n))).ncard := by
    refine le_trans (Set.ncard_le_ncard hsub (Set.toFinite _)) ?_
    exact Set.ncard_union_le _ _
  have h2 : ({e ∈ R_final | w ∈ e} : Set (Set (Fin n))).ncard = degAt R_final w :=
    hdeg_eq_degAt R_final (fun e he => by
      rw [← edgeSize_eq_ncard]
      exact (mem_pow2.mp (hRpow he)).2) w
  rw [h2] at h1
  exact h1

end

end ErdosFaberLovaszConjecture
