import Submission.EFL.S12Step5
import Submission.EFL.Nibble

/-!
# §12, Step 6 (`step:step6`): auxiliary estimates

This module collects the self-contained estimates that checking the
hypotheses C1--C4 of the Nibble Lemma (`NibbleStatement`) in Step 6 requires:

* `Dparam_floor_bound` — `|(1-ρ)(n-1) - D| ≤ 1` for `D = ⌊(1-ρ)(n-1)⌋`;
* `s12_star_degree` — the degree bound `d_{𝓗*}(w) = (1 ± 2β)D` for
  `𝓗* = 𝓗' ∖ ⋃𝓜_diff`, from the regularising lemma's estimate
  `|d_{𝓗'}(w) - (1-ρ)(n-1)| ≤ (2/3)βn` and the fact that `𝓜_diff` has at most
  one edge at every vertex;
* `s12_C1_slack` — the slack in C1 (`D + γn ≤ |S₂|` from `D + 4εn ≤ |S₂|`);
* `s12_C4_small` — `|V(M_c)| ≤ 2βD` from `|V(M_c)| ≤ βn` and `n ≤ 2D`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-- `D = ⌊(1-ρ)(n-1)⌋` differs from `(1-ρ)(n-1)` by at most `1`. -/
theorem Dparam_floor_bound (n : ℕ) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hn : 1 ≤ n) :
    |(1 - ρ) * ((n : ℝ) - 1) - (Dparam n ρ : ℝ)| ≤ 1 := by
  have hx0 : (0 : ℝ) ≤ (1 - ρ) * ((n : ℝ) - 1) := by
    have : (0 : ℝ) ≤ (n : ℝ) - 1 := by
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    exact mul_nonneg (by linarith) this
  have h1 : (Dparam n ρ : ℝ) ≤ (1 - ρ) * ((n : ℝ) - 1) := by
    have : ((⌊(1 - ρ) * ((n : ℝ) - 1)⌋₊ : ℕ) : ℝ) ≤ (1 - ρ) * ((n : ℝ) - 1) :=
      Nat.floor_le hx0
    simpa only [Dparam] using this
  have h2 : (1 - ρ) * ((n : ℝ) - 1) < (Dparam n ρ : ℝ) + 1 := by
    have : (1 - ρ) * ((n : ℝ) - 1) < ((⌊(1 - ρ) * ((n : ℝ) - 1)⌋₊ : ℕ) : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    simpa only [Dparam] using this
  rw [abs_le]
  constructor <;> linarith

/-- **Step 6, C3.**  The degree bound `d_{𝓗*}(w) = (1 ± 2β)D` for
`𝓗* = 𝓗' ∖ 𝓕`, where `d_{𝓗'}(w) = (1-ρ)(n-1) ± (2/3)βn` and `𝓕` has at most
one edge at every vertex. -/
theorem s12_star_degree {𝓗' 𝓗star : MultiHypergraph n} {𝓕 : Hypergraph (Fin n)}
    {ρ β D : ℝ} (hstar : 𝓗star = 𝓗'.sdiff 𝓕) (hsub : 𝓕 ⊆ 𝓗'.edges)
    (hm : ∀ w, MultiHypergraph.hdeg 𝓕 w ≤ 1)
    (hdeg : ∀ w, |((𝓗'.deg w : ℝ)) - (1 - ρ) * ((n : ℝ) - 1)| ≤ 2 / 3 * β * (n : ℝ))
    (hD : |(1 - ρ) * ((n : ℝ) - 1) - D| ≤ 1)
    (hnum : 2 / 3 * β * (n : ℝ) + 2 ≤ 2 * β * D) :
    ∀ w, |((𝓗star.deg w : ℝ)) - D| ≤ 2 * β * D := by
  intro w
  have h := MultiHypergraph.abs_deg_sdiff_sub_le (𝓜 := 𝓗') (𝓕 := 𝓕) hsub hm
    (ρ := ρ) (D := D) (C := 2 / 3 * β * (n : ℝ)) hdeg w
  have h1 := abs_le.mp h
  have h2 := abs_le.mp hD
  rw [hstar, abs_le]
  constructor <;> linarith

/-- **Step 6, C1.**  The slack `D + 4εn ≤ |S₂|` implies `D + γn ≤ |S₂|` when
`γ ≤ 2ε`. -/
theorem s12_C1_slack {D γ ε : ℝ} {S₂ U : Set (Fin n)}
    (hS : D + 4 * ε * (n : ℝ) ≤ (S₂.ncard : ℝ)) (hγε : 2 * γ ≤ 4 * ε) (hε0 : 0 ≤ ε) :
    ((1 - 2 * ε) * (n : ℝ) < (U.ncard : ℝ)) → D + γ * (n : ℝ) ≤ (S₂.ncard : ℝ) := by
  intro _
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h1 : γ * (n : ℝ) ≤ 4 * ε * (n : ℝ) := by nlinarith
  linarith

/-- **Step 6, C4 (size).**  `|V(M_c)| ≤ βn ≤ 2βD` when `n ≤ 2D`. -/
theorem s12_C4_small {β D : ℝ} {X : Set (Fin n)}
    (hX : (X.ncard : ℝ) ≤ β * (n : ℝ)) (hn : (n : ℝ) ≤ 2 * D) (hβ : 0 ≤ β) :
    (X.ncard : ℝ) ≤ 2 * β * D := by
  nlinarith

end

end ErdosFaberLovaszConjecture
