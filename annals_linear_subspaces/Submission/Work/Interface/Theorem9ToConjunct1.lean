import ChallengeDeps
import Submission.DirichletTarget
import Submission.Commons.LinearAlgebra.ExteriorPower.iMulti_ne_zero_of_linearIndependent

/-!
# Interface: Theorem-9-type bound ⟹ first conjunct of `theorem_1`

This module pins down, in the formal record, the exact shape of the output that the
eventual formalization of de Saxcé's Section 3 (Theorem 9 / Prop. 5, "Dirichlet's
principle in `X_ℓ(ℝ)`") must produce, and shows that this output implies the first
conjunct of the challenge theorem.

Concretely, Theorem 9's proof (for fixed `1 ≤ k ≤ ℓ < d`) yields, for every subspace
`x ≤ ℝᵈ` of dimension `ℓ` and every target distance `η > 0`, a rational `k`-subspace
`v` with

    `distSubspaces v x ≤ η`   and   `height v hv ≤ C · η^(-k(d-ℓ)/d)`

(`(★)`; the constant `C = C_{d,ℓ,k} > 0` does not depend on `x`).  We prove here that
this per-`x` bound `(★)` implies, by the real-`rpow` chase recorded in the ROADMAP
(session 20 design memo, item (a)), the Dirichlet property

    `∀ 0 < β < d/(k(d-ℓ)), ∀ c > 0, ∃ v rational k-plane, distSubspaces v x < c · H(v)^(-β)`

and therefore — via the proven interface lemma `Submission.lower_bound_of_dirichlet` —
the lower bound `diophantineExponent k x ≥ d/(k(d-ℓ))`, which is exactly the first
conjunct of `LinearSubspaces.theorem_1`.

The chase: given `β < D := d/(k(d-ℓ))` and `c > 0`, set `α := k(d-ℓ)/d` (so `D = 1/α`
and `0 < α·β < 1`), pick `η := (c·C^(-β)/2)^(1/(1-α·β)) > 0`, and take the `v` of `(★)`.
Then `H ≤ C·η^(-α)` gives `H^(-β) ≥ C^(-β)·η^(α·β)` (monotonicity of `x ↦ x^(-β)` on
positive reals), while `η^(1-α·β) = c·C^(-β)/2 < c·C^(-β)` gives
`distSubspaces v x ≤ η < c·C^(-β)·η^(α·β) ≤ c·H^(-β)`.

We also record the elementary fact that the height of a rational subspace is strictly
positive (its defining wedge is a basis wedge, hence non-zero), which is needed for the
`rpow` monotonicity step.
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

/-- The height of a rational subspace `v` is strictly positive: the wedge of an
`ℝ`-basis of `v` (the image of a `ℤ`-basis of `v ∩ ℤᵈ`) is a non-zero vector of the
exterior power. -/
lemma height_pos (v : Submodule ℝ ℝᵈ) (hv : IsRational v) : 0 < height v hv := by
  unfold height
  let b : Basis (Fin (finrank ℝ v)) ℝ v := chosenBasis v hv
  have hliV : LinearIndependent ℝ (fun i : Fin (finrank ℝ v) => b i) := b.linearIndependent
  have hli : LinearIndependent ℝ (⇑(v.subtype) ∘ b) := by
    exact LinearIndependent.map' hliV v.subtype (Submodule.ker_subtype v)
  have hne : exteriorPower.ιMulti ℝ (finrank ℝ v) (⇑(v.subtype) ∘ b) ≠ 0 :=
    Commons.LinearAlgebra.ExteriorPower.iMulti_ne_zero_of_linearIndependent
      (K := ℝ) (v := ⇑(v.subtype) ∘ b) hli
  -- `height v hv` unfolds exactly to the norm of this wedge
  simpa [b] using (norm_pos_iff.mpr hne)

/-- Monotonicity of the real power with a negative exponent on positive reals:
`0 < a ≤ b` and `0 < β` give `b^(-β) ≤ a^(-β)`. -/
lemma rpow_neg_anti {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) (β : ℝ) (hβ : 0 < β) :
    b ^ (-β) ≤ a ^ (-β) := by
  have h1 : a ^ β ≤ b ^ β := Real.rpow_le_rpow (le_of_lt ha) hab (le_of_lt hβ)
  have hpa : 0 < a ^ β := Real.rpow_pos_of_pos ha β
  have hpb : 0 < b ^ β := Real.rpow_pos_of_pos hb β
  rw [Real.rpow_neg (le_of_lt hb) β, Real.rpow_neg (le_of_lt ha) β]
  exact (inv_le_inv₀ hpb hpa).mpr h1

/-- **Interface lemma**: the per-`x` Dirichlet bound `(★)` produced by the Section-3
machinery (Theorem 9 / Prop. 5 of de Saxcé) implies the first conjunct of
`LinearSubspaces.theorem_1`, via the real-`rpow` chase of the ROADMAP design memo.

Concretely, if for every `ℓ`-dimensional `x` and every `η > 0` there is a rational
`k`-subspace `v` with `distSubspaces v x ≤ η` and `height v ≤ C · η^(-k(d-ℓ)/d)`
(`C > 0` fixed), then `diophantineExponent k x ≥ d/(k(d-ℓ))` for every such `x`. -/
theorem conjunct1_of_dirichlet_bound (hd : 2 ≤ d) {l : ℕ} (hl0 : 0 < l) (hld : l < d)
    {k : ℕ} (hk1 : 1 ≤ k) (hkl : k ≤ l) {C : ℝ} (hC : 0 < C)
    (hT9 : ∀ (x : Submodule ℝ ℝᵈ), finrank ℝ x = l → ∀ η : ℝ, 0 < η →
      ∃ v : Submodule ℝ ℝᵈ, ∃ hv : IsRational v, finrank ℝ v = k ∧
        distSubspaces v x ≤ η ∧
        height v hv ≤ C * η ^ (-(((k : ℝ) * ((d : ℝ) - (l : ℝ))) / (d : ℝ)))) :
    ∀ (x : Submodule ℝ ℝᵈ), finrank ℝ x = l →
      diophantineExponent k x ≥ (d : ℝ≥0∞) / (k * (d - l)) := by
  refine lower_bound_of_dirichlet hd hl0 hld hk1 hkl ?_
  intro x hx β hβ hβD c hc
  -- positive-dimension arithmetic
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
  -- α := k(d-ℓ)/d ; then D := 1/α and β < D give 0 < α·β < 1
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
  -- η := (A/2)^e with A := c·C^(-β) and e := 1/(1-α·β)
  set A : ℝ := c * C ^ (-β) with hAdef
  have hApos : 0 < A := by
    dsimp [A]
    exact mul_pos hc (Real.rpow_pos_of_pos hC (-β))
  set B : ℝ := A / 2 with hBdef
  have hBpos : 0 < B := div_pos hApos (by norm_num)
  set e : ℝ := 1 / (1 - α * β) with hedef
  set η : ℝ := B ^ e with hηdef
  have hηpos : 0 < η := by
    dsimp [η]
    exact Real.rpow_pos_of_pos hBpos e
  obtain ⟨v, hv, hfv, hdist, hH⟩ := hT9 x hx η hηpos
  -- H := height v hv > 0
  have hHpos : 0 < height v hv := height_pos v hv
  -- (1) monotonicity gives C^(-β)·η^(αβ) ≤ H^(-β)
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
  -- (2) η^(1-αβ) = A/2
  have hηpow : η ^ (1 - α * β) = B := by
    dsimp [η, e]
    have hcomb : (1 / (1 - α * β)) * (1 - α * β) = 1 := by field_simp [he0]
    rw [← Real.rpow_mul (le_of_lt hBpos) (1 / (1 - α * β)) (1 - α * β), hcomb,
      Real.rpow_one]
  -- (3) η < A·η^(αβ)
  have hηlt : η < A * η ^ (α * β) := by
    have hAe : η ^ (1 - α * β) < A := by
      rw [hηpow]
      dsimp [B]
      linarith
    have hmul := mul_lt_mul_of_pos_right hAe (Real.rpow_pos_of_pos hηpos (α * β))
    calc
      η = η ^ 1 := (Real.rpow_one η).symm
      _ = η ^ ((1 - α * β) + α * β) := by
            congr 1
            ring
      _ = η ^ (1 - α * β) * η ^ (α * β) := Real.rpow_add hηpos (1 - α * β) (α * β)
      _ < A * η ^ (α * β) := hmul
  -- (4) A·η^(αβ) = (c·C^(-β))·η^(αβ) ≤ c·H^(-β)
  have hmid : A * η ^ (α * β) ≤ c * (height v hv) ^ (-β) := by
    dsimp [A]
    calc
      (c * C ^ (-β)) * η ^ (α * β) = c * (C ^ (-β) * η ^ (α * β)) := by ring
      _ ≤ c * (height v hv) ^ (-β) := mul_le_mul_of_nonneg_left hmid0 (le_of_lt hc)
  -- conclusion
  exact ⟨v, hv, hfv, lt_of_le_of_lt hdist (lt_of_lt_of_le hηlt hmid)⟩


/-! ## Top-level assembly frame for `LinearSubspaces.theorem_1`

The challenge theorem (`LinearSubspaces.theorem_1`) reduces to exactly two oracles:

- **(O1, §3 output)** `hT9`: for every `ℓ`-dimensional `x` and every target distance
  `η > 0`, a rational `k`-subspace `v` with `distSubspaces v x ≤ η` and
  `height v ≤ C·η^(-k(d-ℓ)/d)` (the per-`x` correlated family the §3 machinery — Prop 5 +
  Theorem 9 + the correspondence — must produce; this session's chain up to `lemma4_flow`
  is a fragment of that machinery);
- **(O2, optimality witness)** `hO2`: some `ℓ`-dimensional `x` with
  `diophantineExponent k x ≤ d/(k(d-ℓ))` (conjunct 2 of the paper: a.e.-`x` via the flow
  ergodicity / an explicit algebraic example).

O1 ⟹ conjunct 1 is `conjunct1_of_dirichlet_bound` (above); conjunct 2 follows from O1
applied to the O2 witness (giving `≥`) together with O2's `≤`.  This is the proof frame
`theorem_1`'s eventual proof will instantiate; the remaining work is exactly proving O1
and O2, each a recorded multi-module subproject. -/
theorem theorem_1_from_oracles (hd : 2 ≤ d) {l : ℕ} (hl0 : 0 < l) (hld : l < d)
    {k : ℕ} (hk1 : 1 ≤ k) (hkl : k ≤ l) {C : ℝ} (hC : 0 < C)
    (hT9 : ∀ (x : Submodule ℝ ℝᵈ), finrank ℝ x = l → ∀ η : ℝ, 0 < η →
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
    exact conjunct1_of_dirichlet_bound hd hl0 hld hk1 hkl hC hT9 x hx
  · rcases hO2 with ⟨x, hx, hβle⟩
    refine ⟨x, hx, ?_⟩
    have hge : diophantineExponent k x ≥ (d : ℝ≥0∞) / (k * (d - l)) :=
      conjunct1_of_dirichlet_bound hd hl0 hld hk1 hkl hC hT9 x hx
    exact le_antisymm hβle hge
end Submission
