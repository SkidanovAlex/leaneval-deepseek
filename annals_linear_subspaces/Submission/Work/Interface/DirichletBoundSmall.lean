import Submission.Work.Interface.Theorem9ToConjunct1

/-!
# Realizable (small-`η`) Theorem-9 contract ⟹ first conjunct of `theorem_1`

`Submission.Work.Interface.Theorem9ToConjunct1` pinned the Theorem-9-output contract as
the correlated family

    (★)  ∀ x (dim ℓ) (η > 0), ∃ v rational k-plane : distSubspaces v x ≤ η
         ∧ height v hv ≤ C·η^(-k(d-ℓ)/d)

and proved `conjunct1_of_dirichlet_bound`: (★) ⟹ conjunct 1.  That contract is however
**unrealizable as stated**: rational `k`-plane heights are bounded below (an integer wedge
has norm ≥ 1), while `η^(-α) → 0` as `η → ∞`, so no rational plane can meet
`height v ≤ C·η^(-α)` for arbitrarily large `η`.  The genuine output of the §3 machinery
(Prop 5 + Theorem 9) is the *small-`η`* family: there is a range `0 < η ≤ η₀` (any
positive `η₀` — Theorem 9 produces planes at arbitrarily small distances) on which (★)
holds.

This module records the corrected, realizable contract and proves it still implies the
first conjunct (and hence, together with an optimality witness, the full challenge):

* **`conjunct1_of_dirichlet_bound_small`** — the small-`η` contract
  `hT9 : ∀ x (dim ℓ) (η with 0 < η ≤ η₀), ∃ v : dist ≤ η ∧ height ≤ C·η^(-α)` implies
  `diophantineExponent k x ≥ d/(k(d-ℓ))` for every `ℓ`-plane `x`.  Proof: the same
  real-`rpow` chase as the all-`η` interface (`lower_bound_of_dirichlet`), except that
  for a given `0 < β < D` and `c > 0` one applies `hT9` at the clamped
  `η* := min η₀ (c·C^(-β)/2)^(1/(1-αβ))` (`α := k(d-ℓ)/d`, so `D = 1/α`), for which the
  strict bound `η*^(1-αβ) < c·C^(-β)` holds in both cases of the `min` (equality from the
  exponent choice when the base term is smaller, and strict rpow-monotonicity from
  `η₀ < (c·C^(-β)/2)^(1/(1-αβ))` otherwise), giving `dist ≤ η* < c·C^(-β)·η*^(αβ) ≤
  c·height^(-β)` as required;
* **`theorem_1_from_oracles_small`** — the top-level assembly frame with the corrected
  oracle (O1) plus the optimality witness (O2).

Math content: this is a pure real-`rpow`/`ENNReal` interface statement (ChallengeDeps +
the previously proven interface lemmas `lower_bound_of_dirichlet`, `height_pos`,
`rpow_neg_anti`); no §3 machinery is formalised here.
-/

open LinearSubspaces
open ENNReal Real Module exteriorPower InnerProductGeometry
open scoped LinearAlgebra.Projectivization

set_option autoImplicit false

noncomputable section

namespace Submission

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)
local notation "ℤᵈ" => intPoints

/-- **Interface lemma, realizable small-`η` form**: Theorem 9's output is only realizable
for `η` in a bounded range `0 < η ≤ η₀` (rational heights are bounded below, so an
`H ≤ C·η^(-α)` demand for arbitrarily large `η` cannot be met); this form of the
Dirichlet contract still suffices for the first conjunct of `LinearSubspaces.theorem_1`. -/
theorem conjunct1_of_dirichlet_bound_small (hd : 2 ≤ d) {l : ℕ} (hl0 : 0 < l) (hld : l < d)
    {k : ℕ} (hk1 : 1 ≤ k) (hkl : k ≤ l) {C η₀ : ℝ} (hC : 0 < C) (hη₀ : 0 < η₀)
    (hT9 : ∀ (x : Submodule ℝ ℝᵈ), finrank ℝ x = l → ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∃ v : Submodule ℝ ℝᵈ, ∃ hv : IsRational v, finrank ℝ v = k ∧
        distSubspaces v x ≤ η ∧
        height v hv ≤ C * η ^ (-(((k : ℝ) * ((d : ℝ) - (l : ℝ))) / (d : ℝ)))) :
    ∀ (x : Submodule ℝ ℝᵈ), finrank ℝ x = l →
      diophantineExponent k x ≥ (d : ℝ≥0∞) / (k * (d - l)) := by
  refine lower_bound_of_dirichlet hd hl0 hld hk1 hkl ?_
  intro x hx β hβ hβD c hc
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (by omega : 0 < d))
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (by omega : 0 < k))
  have hdl0 : (d : ℝ) - (l : ℝ) ≠ 0 := by
    rw [← Nat.cast_sub (le_of_lt hld)]
    exact_mod_cast (ne_of_gt (Nat.sub_pos_of_lt hld))
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hdlpos : 0 < (d : ℝ) - (l : ℝ) := by
    rw [← Nat.cast_sub (le_of_lt hld)]
    exact_mod_cast (Nat.sub_pos_of_lt hld)
  set α : ℝ := ((k : ℝ) * ((d : ℝ) - (l : ℝ))) / (d : ℝ) with hαdef
  have hαpos : 0 < α := by
    dsimp [α]
    exact div_pos (mul_pos hkpos hdlpos) hdpos
  have hαD : α * ((d : ℝ) / ((k : ℝ) * ((d : ℝ) - (l : ℝ)))) = 1 := by
    dsimp [α]
    field_simp [hd0, hk0, hdl0]
  have hαβpos : 0 < α * β := mul_pos hαpos hβ
  have hαβlt : α * β < 1 := by
    calc
      α * β < α * ((d : ℝ) / ((k : ℝ) * ((d : ℝ) - (l : ℝ)))) :=
        mul_lt_mul_of_pos_left hβD hαpos
      _ = 1 := hαD
  have hone : 0 < 1 - α * β := sub_pos.mpr hαβlt
  have he0 : 1 - α * β ≠ 0 := ne_of_gt hone
  set A : ℝ := c * C ^ (-β) with hAdef
  have hApos : 0 < A := by
    dsimp [A]
    exact mul_pos hc (Real.rpow_pos_of_pos hC (-β))
  set e : ℝ := 1 / (1 - α * β) with hedef
  set ηb : ℝ := (A / 2) ^ e with hηbdef
  have hηbpos : 0 < ηb := by
    dsimp [ηb]
    exact Real.rpow_pos_of_pos (div_pos hApos (by norm_num)) e
  set η : ℝ := min η₀ ηb with hηdef
  have hηpos : 0 < η := by
    dsimp [η]
    exact lt_min hη₀ hηbpos
  have hηle : η ≤ η₀ := by
    dsimp [η]
    exact min_le_left η₀ ηb
  obtain ⟨v, hv, hfv, hdist, hH⟩ := hT9 x hx η hηpos hηle
  have hHpos : 0 < height v hv := height_pos v hv
  have hCηpos : 0 < C * η ^ (-α) := mul_pos hC (Real.rpow_pos_of_pos hηpos (-α))
  have hmono : (C * η ^ (-α)) ^ (-β) ≤ (height v hv) ^ (-β) := by
    apply rpow_neg_anti (a := height v hv) (b := C * η ^ (-α))
    · exact hHpos
    · exact hCηpos
    · dsimp [α] at hH
      exact hH
    · exact hβ
  have hcom : (C * η ^ (-α)) ^ (-β) = C ^ (-β) * η ^ (α * β) := by
    have hηe : η ^ (α * β) = (η ^ (-α)) ^ (-β) := by
      calc
        η ^ (α * β) = η ^ ((-α) * (-β)) := by
              congr 1
              ring
        _ = (η ^ (-α)) ^ (-β) := by
              rw [Real.rpow_mul (le_of_lt hηpos) (-α) (-β)]
    rw [Real.mul_rpow (le_of_lt hC) (Real.rpow_nonneg (le_of_lt hηpos) (-α))]
    rw [← hηe]
  have hmid0 : C ^ (-β) * η ^ (α * β) ≤ (height v hv) ^ (-β) := by
    rwa [hcom] at hmono
  -- η^(1-αβ) < A : strict, from the clamping (both cases of the min)
  have hA2 : ηb ^ (1 - α * β) < A := by
    have hpos2 : 0 ≤ A / 2 := le_of_lt (div_pos hApos (by norm_num))
    have hcomb : e * (1 - α * β) = 1 := by
      dsimp [e]
      field_simp [he0]
    have hstep : ηb ^ (1 - α * β) = A / 2 := by
      dsimp [ηb]
      rw [← Real.rpow_mul hpos2 e (1 - α * β)]
      rw [hcomb, Real.rpow_one]
    calc
      ηb ^ (1 - α * β) = A / 2 := hstep
      _ < A := div_two_lt_of_pos hApos
  have hηpow : η ^ (1 - α * β) < A := by
    dsimp [η]
    by_cases hb : ηb ≤ η₀
    · rw [min_eq_right hb]
      exact hA2
    · have hle : η₀ < ηb := lt_of_not_ge hb
      rw [min_eq_left (le_of_lt hle)]
      have hr := Real.rpow_lt_rpow (le_of_lt hη₀) hle hone
      exact lt_trans hr hA2
  -- η < A·η^(αβ)
  have hηlt : η < A * η ^ (α * β) := by
    have hmul := mul_lt_mul_of_pos_right hηpow (Real.rpow_pos_of_pos hηpos (α * β))
    calc
      η = η ^ 1 := (Real.rpow_one η).symm
      _ = η ^ ((1 - α * β) + α * β) := by
            congr 1
            ring
      _ = η ^ (1 - α * β) * η ^ (α * β) := Real.rpow_add hηpos (1 - α * β) (α * β)
      _ < A * η ^ (α * β) := hmul
  -- A·η^(αβ) = (c·C^(-β))·η^(αβ) ≤ c·H^(-β)
  have hmid : A * η ^ (α * β) ≤ c * (height v hv) ^ (-β) := by
    dsimp [A]
    calc
      (c * C ^ (-β)) * η ^ (α * β) = c * (C ^ (-β) * η ^ (α * β)) := by ring
      _ ≤ c * (height v hv) ^ (-β) := mul_le_mul_of_nonneg_left hmid0 (le_of_lt hc)
  exact ⟨v, hv, hfv, lt_of_le_of_lt hdist (lt_of_lt_of_le hηlt hmid)⟩

/-- **Top-level assembly frame for `LinearSubspaces.theorem_1`, realizable small-`η`
contract**: the challenge reduces to two oracles — (O1) the small-`η` Dirichlet bound
`hT9` (the per-`x` correlated family, realizable output of the §3 machinery), and (O2)
an optimality witness with `diophantineExponent ≤ D`. -/
theorem theorem_1_from_oracles_small (hd : 2 ≤ d) {l : ℕ} (hl0 : 0 < l) (hld : l < d)
    {k : ℕ} (hk1 : 1 ≤ k) (hkl : k ≤ l) {C η₀ : ℝ} (hC : 0 < C) (hη₀ : 0 < η₀)
    (hT9 : ∀ (x : Submodule ℝ ℝᵈ), finrank ℝ x = l → ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∃ v : Submodule ℝ ℝᵈ, ∃ hv : IsRational v, finrank ℝ v = k ∧
        distSubspaces v x ≤ η ∧
        height v hv ≤ C * η ^ (-(((k : ℝ) * ((d : ℝ) - (l : ℝ))) / (d : ℝ))))
    (hO2 : (∃ x : Submodule ℝ ℝᵈ, finrank ℝ x = l ∧
      diophantineExponent k x ≤ (d : ℝ≥0∞) / (k * (d - l)))) :
    (∀ x : Submodule ℝ ℝᵈ, finrank ℝ x = l →
      diophantineExponent k x ≥ (d : ℝ≥0∞) / (k * (d - l))) ∧
    (∃ x : Submodule ℝ ℝᵈ, finrank ℝ x = l ∧
      diophantineExponent k x = (d : ℝ≥0∞) / (k * (d - l))) := by
  constructor
  · intro x hx
    exact conjunct1_of_dirichlet_bound_small hd hl0 hld hk1 hkl hC hη₀ hT9 x hx
  · rcases hO2 with ⟨x, hx, hβle⟩
    refine ⟨x, hx, ?_⟩
    have hge : diophantineExponent k x ≥ (d : ℝ≥0∞) / (k * (d - l)) :=
      conjunct1_of_dirichlet_bound_small hd hl0 hld hk1 hkl hC hη₀ hT9 x hx
    exact le_antisymm hβle hge
/-- **Per-`x` realizable Theorem-9 contract**: if for every `ℓ`-plane `x` there are
`x`-dependent constants `η₀(x) > 0`, `C(x) > 0` with the small-`η` correlated family
(`∀ 0 < η ≤ η₀(x) : ∃v rational k-plane, d(v,x) ≤ η ∧ H(v) ≤ C(x)·η^(-k(d-ℓ)/d)`), then
`diophantineExponent k x ≥ d/(k(d-ℓ))` for every `ℓ`-plane `x`.  (The constants may depend
on `x` — the chase runs per-`x`.) -/
theorem conjunct1_of_dirichlet_bound_perX (hd : 2 ≤ d) {l : ℕ} (hl0 : 0 < l) (hld : l < d)
    {k : ℕ} (hk1 : 1 ≤ k) (hkl : k ≤ l)
    (hOracle : ∀ (x : Submodule ℝ ℝᵈ), finrank ℝ x = l →
      ∃ η₀ C : ℝ, 0 < η₀ ∧ 0 < C ∧
        ∀ η : ℝ, 0 < η → η ≤ η₀ →
          ∃ v : Submodule ℝ ℝᵈ, ∃ hv : IsRational v, finrank ℝ v = k ∧
            distSubspaces v x ≤ η ∧
            height v hv ≤ C * η ^ (-(((k : ℝ) * ((d : ℝ) - (l : ℝ))) / (d : ℝ)))) :
    ∀ (x : Submodule ℝ ℝᵈ), finrank ℝ x = l →
      diophantineExponent k x ≥ (d : ℝ≥0∞) / (k * (d - l)) := by
  refine lower_bound_of_dirichlet hd hl0 hld hk1 hkl ?_
  intro x hx
  rcases hOracle x hx with ⟨η₀, C, hη₀, hC, hT9⟩
  intro β hβ hβD c hc
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (by omega : 0 < d))
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (by omega : 0 < k))
  have hdl0 : (d : ℝ) - (l : ℝ) ≠ 0 := by
    rw [← Nat.cast_sub (le_of_lt hld)]
    exact_mod_cast (ne_of_gt (Nat.sub_pos_of_lt hld))
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hdlpos : 0 < (d : ℝ) - (l : ℝ) := by
    rw [← Nat.cast_sub (le_of_lt hld)]
    exact_mod_cast (Nat.sub_pos_of_lt hld)
  set α : ℝ := ((k : ℝ) * ((d : ℝ) - (l : ℝ))) / (d : ℝ) with hαdef
  have hαpos : 0 < α := by
    dsimp [α]
    exact div_pos (mul_pos hkpos hdlpos) hdpos
  have hαD : α * ((d : ℝ) / ((k : ℝ) * ((d : ℝ) - (l : ℝ)))) = 1 := by
    dsimp [α]
    field_simp [hd0, hk0, hdl0]
  have hαβpos : 0 < α * β := mul_pos hαpos hβ
  have hαβlt : α * β < 1 := by
    calc
      α * β < α * ((d : ℝ) / ((k : ℝ) * ((d : ℝ) - (l : ℝ)))) :=
        mul_lt_mul_of_pos_left hβD hαpos
      _ = 1 := hαD
  have hone : 0 < 1 - α * β := sub_pos.mpr hαβlt
  have he0 : 1 - α * β ≠ 0 := ne_of_gt hone
  set A : ℝ := c * C ^ (-β) with hAdef
  have hApos : 0 < A := by
    dsimp [A]
    exact mul_pos hc (Real.rpow_pos_of_pos hC (-β))
  set e : ℝ := 1 / (1 - α * β) with hedef
  set ηb : ℝ := (A / 2) ^ e with hηbdef
  have hηbpos : 0 < ηb := by
    dsimp [ηb]
    exact Real.rpow_pos_of_pos (div_pos hApos (by norm_num)) e
  set η : ℝ := min η₀ ηb with hηdef
  have hηpos : 0 < η := by
    dsimp [η]
    exact lt_min hη₀ hηbpos
  have hηle : η ≤ η₀ := by
    dsimp [η]
    exact min_le_left η₀ ηb
  obtain ⟨v, hv, hfv, hdist, hH⟩ := hT9 η hηpos hηle
  have hHpos : 0 < height v hv := height_pos v hv
  have hCηpos : 0 < C * η ^ (-α) := mul_pos hC (Real.rpow_pos_of_pos hηpos (-α))
  have hmono : (C * η ^ (-α)) ^ (-β) ≤ (height v hv) ^ (-β) := by
    apply rpow_neg_anti (a := height v hv) (b := C * η ^ (-α))
    · exact hHpos
    · exact hCηpos
    · dsimp [α] at hH
      exact hH
    · exact hβ
  have hcom : (C * η ^ (-α)) ^ (-β) = C ^ (-β) * η ^ (α * β) := by
    have hηe : η ^ (α * β) = (η ^ (-α)) ^ (-β) := by
      calc
        η ^ (α * β) = η ^ ((-α) * (-β)) := by
              congr 1
              ring
        _ = (η ^ (-α)) ^ (-β) := by
              rw [Real.rpow_mul (le_of_lt hηpos) (-α) (-β)]
    rw [Real.mul_rpow (le_of_lt hC) (Real.rpow_nonneg (le_of_lt hηpos) (-α))]
    rw [← hηe]
  have hmid0 : C ^ (-β) * η ^ (α * β) ≤ (height v hv) ^ (-β) := by
    rwa [hcom] at hmono
  have hA2 : ηb ^ (1 - α * β) < A := by
    have hpos2 : 0 ≤ A / 2 := le_of_lt (div_pos hApos (by norm_num))
    have hcomb : e * (1 - α * β) = 1 := by
      dsimp [e]
      field_simp [he0]
    have hstep : ηb ^ (1 - α * β) = A / 2 := by
      dsimp [ηb]
      rw [← Real.rpow_mul hpos2 e (1 - α * β)]
      rw [hcomb, Real.rpow_one]
    calc
      ηb ^ (1 - α * β) = A / 2 := hstep
      _ < A := div_two_lt_of_pos hApos
  have hηpow : η ^ (1 - α * β) < A := by
    dsimp [η]
    by_cases hb : ηb ≤ η₀
    · rw [min_eq_right hb]
      exact hA2
    · have hle : η₀ < ηb := lt_of_not_ge hb
      rw [min_eq_left (le_of_lt hle)]
      have hr := Real.rpow_lt_rpow (le_of_lt hη₀) hle hone
      exact lt_trans hr hA2
  have hηlt : η < A * η ^ (α * β) := by
    have hmul := mul_lt_mul_of_pos_right hηpow (Real.rpow_pos_of_pos hηpos (α * β))
    calc
      η = η ^ 1 := (Real.rpow_one η).symm
      _ = η ^ ((1 - α * β) + α * β) := by
            congr 1
            ring
      _ = η ^ (1 - α * β) * η ^ (α * β) := Real.rpow_add hηpos (1 - α * β) (α * β)
      _ < A * η ^ (α * β) := hmul
  have hmid : A * η ^ (α * β) ≤ c * (height v hv) ^ (-β) := by
    dsimp [A]
    calc
      (c * C ^ (-β)) * η ^ (α * β) = c * (C ^ (-β) * η ^ (α * β)) := by ring
      _ ≤ c * (height v hv) ^ (-β) := mul_le_mul_of_nonneg_left hmid0 (le_of_lt hc)
  exact ⟨v, hv, hfv, lt_of_le_of_lt hdist (lt_of_lt_of_le hηlt hmid)⟩

end Submission

end
