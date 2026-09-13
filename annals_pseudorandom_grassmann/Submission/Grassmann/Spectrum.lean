import Mathlib
import Submission.Grassmann.Scheme
import Submission.Grassmann.Degree
import Submission.Grassmann.GaussianBinomial
import Submission.Commons.LinearAlgebra.Submodule.card_hyperplane_zmod_two
import Submission.Commons.LinearAlgebra.Submodule.card_hyperplanes_between
import Submission.Commons.Algebra.Eberlein.eberlein_formula
import Submission.Commons.Algebra.Eberlein.eberlein_strictAnti
import Submission.Commons.LinearAlgebra.Submodule.card_neighbors_containing_of_le
import Submission.Commons.LinearAlgebra.Submodule.card_neighbors_containing_of_inf_eq
import Submission.Commons.LinearAlgebra.Submodule.card_neighbors_containing_eq_zero

/-!
# The Eberlein eigenvalues of the Grassmann graph `Gr_{k,ℓ}` (Layer 3, spectral core)

This file develops the spectral theory of the Grassmann graph `Gr k ℓ` (vertices: the
`ℓ`-dimensional subspaces of `𝔽₂ᵏ`; adjacency: `dim (L ⊓ L') = ℓ - 1`).

The key device is the classical one: for `0 ≤ i ≤ ℓ` consider the *up operator*
`Ψ_i` sending a function `g` on the `i`-dimensional subspaces to the function
`(Ψ_i g)(L) = ∑_{W ≤ L, dim W = i} g W` on the vertices.  Its adjoint (for the uniform
measure) is the *down operator* `∂_i^*`, `(∂_i^* g)(U) = ∑_{W ≥ U} g W`.

The fundamental intertwining identity is

  `A_1 ∘ Ψ_i = Ψ_i ∘ (θ_i + ∂_i ∘ ∂_i^*)`,

equivalently `A_1 Ψ_i = θ_i Ψ_i + b_i Ψ_{i-1} ∂_i^*`, where

  `b_i = 2^(ℓ+1-i) - 1`,  `a_i = (2^(ℓ-i) - 1) (2^(k-ℓ+1) - 2)`,  `θ_i = a_i - b_i (2^i - 1)`.

Consequences: the `V_i = range Ψ_i` form an increasing chain `V_0 ≤ V_1 ≤ ⋯ ≤ V_ℓ = ⊤`
of `A_1`-invariant subspaces with `(A_1 - θ_i · 1) V_i ≤ V_{i-1}`; hence
`∏_{j ≤ ℓ} (A_1 - θ_j · 1) = 0`.  The `θ_i` are the classical *Eberlein eigenvalues*.

-/

open PseudorandomGrassmann
open Module Submodule Finset Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

local notation "𝔽₂" => ZMod 2

namespace Submission.Grassmann
namespace F2

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k ℓ : ℕ}

/-! ## 1. The up and down operators -/

/-- The **up operator** `Ψ_i`: for `g` a function on the `i`-dimensional subspaces,
`(Ψ_i g)(L) = ∑_{W ≤ L, dim W = i} g W`. -/
def upFun (i : ℕ) (g : GrVertex k i → ℚ) (L : GrVertex k ℓ) : ℚ :=
  ∑ W : GrVertex k i, if W.1 ≤ L.1 then g W else 0

/-- The **down-star operator** `∂_i^*`: for `g` a function on the `i`-dimensional
subspaces, `(∂_i^* g)(U) = ∑_{W ≥ U, dim W = i} g W`. -/
def downStarFun (i : ℕ) (g : GrVertex k i → ℚ) (U : GrVertex k (i - 1)) : ℚ :=
  ∑ W : GrVertex k i, if U.1 ≤ W.1 then g W else 0

/-- The **down operator** `∂_i`: for `h` a function on the `(i-1)`-dimensional subspaces,
`(∂_i h)(W) = ∑_{U ≤ W, dim U = i-1} h U`. -/
def downFun (i : ℕ) (h : GrVertex k (i - 1) → ℚ) (W : GrVertex k i) : ℚ :=
  ∑ U : GrVertex k (i - 1), if U.1 ≤ W.1 then h U else 0

/-- `b_i = 2^(ℓ+1-i) - 1`. -/
def bNum (ℓ i : ℕ) : ℕ := 2 ^ (ℓ + 1 - i) - 1

/-- `a_i = (2^(ℓ-i) - 1) * (2^(k-ℓ+1) - 2)`. -/
def aNum (k ℓ i : ℕ) : ℕ := (2 ^ (ℓ - i) - 1) * (2 ^ (k - ℓ + 1) - 2)

/-- The **Eberlein eigenvalue** `θ_i = a_i - b_i (2^i - 1)`. -/
def thetaZ (k ℓ i : ℕ) : ℤ := (aNum k ℓ i : ℤ) - (bNum ℓ i : ℤ) * ((2 ^ i - 1 : ℕ) : ℤ)

lemma thetaZ_eq (k ℓ i : ℕ) :
    thetaZ k ℓ i = (aNum k ℓ i : ℤ) - (bNum ℓ i : ℤ) * ((2 ^ i - 1 : ℕ) : ℤ) := rfl

/-- The Eberlein eigenvalue, as a rational number. -/
def thetaQ (k ℓ i : ℕ) : ℚ := (aNum k ℓ i : ℚ) - (bNum ℓ i : ℚ) * ((2 ^ i - 1 : ℕ) : ℚ)

lemma thetaQ_eq (k ℓ i : ℕ) :
    thetaQ k ℓ i = (aNum k ℓ i : ℚ) - (bNum ℓ i : ℚ) * ((2 ^ i - 1 : ℕ) : ℚ) := rfl

lemma thetaQ_eq_thetaZ (k ℓ i : ℕ) : thetaQ k ℓ i = ((thetaZ k ℓ i : ℤ) : ℚ) := by
  simp only [thetaQ, thetaZ]
  push_cast
  ring

/-! ## 2. Counting the `i`-subspaces between `U` and `L` -/

/-- The number of `i`-dimensional subspaces between a fixed `(i-1)`-subspace `U` and a
fixed `ℓ`-subspace `L` is `b_i` when `U ≤ L` and `0` otherwise. -/
lemma card_subspaces_between (i : ℕ) (hi : 1 ≤ i) (U : GrVertex k (i - 1))
    (L : GrVertex k ℓ) :
    Nat.card {W : GrVertex k i // U.1 ≤ W.1 ∧ W.1 ≤ L.1} =
      if U.1 ≤ L.1 then bNum ℓ i else 0 := by
  classical
  have hfk : Module.finrank 𝔽₂ U.1 = i - 1 := U.2
  by_cases hUL : U.1 ≤ L.1
  · rw [if_pos hUL]
    have hcard : Nat.card {W : GrVertex k i // U.1 ≤ W.1 ∧ W.1 ≤ L.1} =
        #(SubGr k i U.1 L.1) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      rfl
    rw [hcard, card_SubGr_eq_grCount U.1 L.1 hUL (by rw [hfk]; omega)]
    rw [hfk, L.2]
    have h1 : ℓ - (i - 1) = ℓ + 1 - i := by omega
    have h2 : i - (i - 1) = 1 := by omega
    rw [h1, h2, grCount_one, bNum]
  · rw [if_neg hUL, Nat.card_eq_fintype_card, Fintype.card_eq_zero_iff]
    exact ⟨fun W => absurd (le_trans W.2.1 W.2.2) hUL⟩

/-- Distributing a constant `if` over a sum. -/
lemma ite_sum_eq {α : Type*} [Fintype α] (p : Prop) [Decidable p] (f : α → ℚ) :
    (if p then ∑ a : α, f a else 0) = ∑ a : α, if p then f a else 0 := by
  by_cases hp : p <;> simp [hp]

/-- `Ψ_i ∘ ∂_i = b_i • Ψ_{i-1}`. -/
lemma upFun_downFun (i : ℕ) (hi : 1 ≤ i) (h : GrVertex k (i - 1) → ℚ)
    (L : GrVertex k ℓ) :
    upFun i (downFun i h) L = (bNum ℓ i : ℚ) * upFun (i - 1) h L := by
  classical
  have h1 : upFun i (downFun i h) L
      = ∑ W : GrVertex k i, ∑ U : GrVertex k (i - 1),
          if (W.1 ≤ L.1 ∧ U.1 ≤ W.1) then h U else 0 := by
    simp only [upFun, downFun]
    refine Finset.sum_congr rfl (fun W _ => ?_)
    rw [ite_sum_eq]
    refine Finset.sum_congr rfl (fun U _ => ?_)
    by_cases hW : W.1 ≤ L.1 <;> by_cases hU : U.1 ≤ W.1 <;> simp [hW, hU]
  rw [h1, Finset.sum_comm]
  have h2 : ∀ U : GrVertex k (i - 1),
      (∑ W : GrVertex k i, if (W.1 ≤ L.1 ∧ U.1 ≤ W.1) then h U else 0)
        = h U * (if U.1 ≤ L.1 then (bNum ℓ i : ℚ) else 0) := by
    intro U
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hcnt : (Finset.univ.filter
          (fun W : GrVertex k i => (W.1 ≤ L.1 ∧ U.1 ≤ W.1))).card
        = Nat.card {W : GrVertex k i // U.1 ≤ W.1 ∧ W.1 ≤ L.1} := by
      rw [← Fintype.card_subtype (fun W : GrVertex k i => W.1 ≤ L.1 ∧ U.1 ≤ W.1),
        ← Nat.card_eq_fintype_card]
      exact Nat.card_congr (Equiv.subtypeEquivRight (fun W => and_comm))
    rw [hcnt, card_subspaces_between i hi U L]
    push_cast
    by_cases hUL : U.1 ≤ L.1 <;> simp [hUL, mul_comm]
  rw [Finset.sum_congr rfl (fun U _ => h2 U)]
  rw [upFun, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun U _ => ?_)
  by_cases hUL : U.1 ≤ L.1 <;> simp [hUL, mul_comm]

/-! ## 3. The pointwise neighbour count -/

/-- Casting helper: the cardinality of a finite subtype as a sum of indicators. -/
lemma card_eq_sum_ite {α : Type*} [Fintype α] (p : α → Prop) :
    (Nat.card {x : α // p x} : ℚ) = ∑ x : α, if p x then 1 else 0 := by
  rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- The cardinality of a finite subtype, transported through an equivalence of the
underlying predicates. -/
lemma natCard_subtype_congr {α : Type*} (p q : α → Prop) (h : ∀ x, p x ↔ q x) :
    Nat.card {x : α // p x} = Nat.card {x : α // q x} :=
  Nat.card_congr (Equiv.subtypeEquivRight h)

/-- Bridging lemma: the neighbours of `L` that contain a subspace `W`, expressed with
submodules rather than vertices. -/
lemma card_adj_containing_eq (L : GrVertex k ℓ) (hℓ : 1 ≤ ℓ)
    (W : Submodule 𝔽₂ (Fin k → 𝔽₂)) :
    Nat.card {L' : GrVertex k ℓ // (Gr k ℓ).Adj L L' ∧ W ≤ L'.1} =
      Nat.card {X : Submodule 𝔽₂ (Fin k → 𝔽₂) // Module.finrank 𝔽₂ X = ℓ ∧
        Module.finrank 𝔽₂ ↥(L.1 ⊓ X) = ℓ - 1 ∧ W ≤ X} := by
  classical
  refine Nat.card_congr ?_
  refine
    { toFun := fun L' => ⟨L'.1.1, L'.1.2, ?_, L'.2.2⟩
      invFun := fun X => ⟨⟨X.1, X.2.1⟩, ?_, X.2.2.2⟩
      left_inv := fun L' => Subtype.ext rfl
      right_inv := fun X => Subtype.ext rfl }
  · have h := L'.2.1
    simp only [Gr, SimpleGraph.fromRel_adj] at h
    rcases h.2 with hh | hh
    · exact hh
    · rwa [inf_comm] at hh
  · simp only [Gr, SimpleGraph.fromRel_adj]
    refine ⟨?_, Or.inl X.2.2.1⟩
    intro h
    have h1 : L.1 = X.1 := by simpa using congrArg Subtype.val h
    have h2 : Module.finrank 𝔽₂ ↥(L.1 ⊓ X.1) = ℓ := by rw [← h1, inf_idem, L.2]
    omega

/-- The number of `(i-1)`-dimensional subspaces of a fixed `i`-dimensional space. -/
lemma card_GrVertex_le_pred (i : ℕ) (hi : 1 ≤ i) (W : GrVertex k i) :
    Nat.card {U : GrVertex k (i - 1) // U.1 ≤ W.1} = 2 ^ i - 1 := by
  refine (Nat.card_congr ?_).trans (card_hyperplanes_of W.1 W.2 hi)
  exact
    { toFun := fun U => ⟨U.1.1, U.2, U.1.2⟩
      invFun := fun U => ⟨⟨U.1, U.2.2⟩, U.2.1⟩
      left_inv := fun U => Subtype.ext rfl
      right_inv := fun U => Subtype.ext rfl }

/-- The `(i-1)`-subspaces of both `W` and `L`, when `W ≤ L`. -/
lemma card_GrVertex_le_both_of_le (i : ℕ) (hi : 1 ≤ i) {W : GrVertex k i}
    {L : GrVertex k ℓ} (hWL : W.1 ≤ L.1) :
    Nat.card {U : GrVertex k (i - 1) // U.1 ≤ W.1 ∧ U.1 ≤ L.1} = 2 ^ i - 1 := by
  refine (Nat.card_congr (Equiv.subtypeEquivRight (fun U : GrVertex k (i - 1) => ?_))).trans
    (card_GrVertex_le_pred i hi W)
  exact ⟨fun h => h.1, fun h => ⟨h, le_trans h hWL⟩⟩

/-- The `(i-1)`-subspaces of both `W` and `L`, when `dim (W ⊓ L) = i - 1`: there is
exactly one, namely `W ⊓ L`. -/
lemma card_GrVertex_le_both_of_inf_eq (i : ℕ) (hi : 1 ≤ i) {W : GrVertex k i}
    {L : GrVertex k ℓ} (hinf : Module.finrank 𝔽₂ ↥(W.1 ⊓ L.1) = i - 1) :
    Nat.card {U : GrVertex k (i - 1) // U.1 ≤ W.1 ∧ U.1 ≤ L.1} = 1 := by
  classical
  refine Nat.card_eq_one_iff_unique.mpr
    ⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩,
      ⟨⟨⟨W.1 ⊓ L.1, hinf⟩, inf_le_left, inf_le_right⟩⟩⟩
  have ha : a.1.1 = W.1 ⊓ L.1 :=
    Submodule.eq_of_le_of_finrank_eq (le_inf a.2.1 a.2.2) (by rw [a.1.2, hinf])
  have hb : b.1.1 = W.1 ⊓ L.1 :=
    Submodule.eq_of_le_of_finrank_eq (le_inf b.2.1 b.2.2) (by rw [b.1.2, hinf])
  rw [ha, hb]

/-- The `(i-1)`-subspaces of both `W` and `L`, when `dim (W ⊓ L) + 2 ≤ i`: there are none. -/
lemma card_GrVertex_le_both_eq_zero (i : ℕ) {W : GrVertex k i} {L : GrVertex k ℓ}
    (hle : Module.finrank 𝔽₂ ↥(W.1 ⊓ L.1) + 2 ≤ i) :
    Nat.card {U : GrVertex k (i - 1) // U.1 ≤ W.1 ∧ U.1 ≤ L.1} = 0 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero_iff]
  exact ⟨fun U => by
    have h : Module.finrank 𝔽₂ U.1.1 ≤ Module.finrank 𝔽₂ ↥(W.1 ⊓ L.1) :=
      Submodule.finrank_mono (le_inf U.2.1 U.2.2)
    rw [U.1.2] at h
    omega⟩

/-- **Pointwise neighbour count.** For `1 ≤ i ≤ ℓ`, `L` a vertex and `W` an
`i`-dimensional subspace, the number of neighbours `L'` of `L` with `W ≤ L'` is
`θ_i` if `W ≤ L` and `b_i · #{U ≤ W ⊓ L : dim U = i - 1}` otherwise. -/
theorem card_adj_containing (hℓ : 1 ≤ ℓ) (i : ℕ) (hi : 1 ≤ i) (hiℓ : i ≤ ℓ)
    (L : GrVertex k ℓ) (W : GrVertex k i) :
    (Nat.card {L' : GrVertex k ℓ // (Gr k ℓ).Adj L L' ∧ W.1 ≤ L'.1} : ℚ) =
      thetaQ k ℓ i * (if W.1 ≤ L.1 then 1 else 0) +
        (bNum ℓ i : ℚ) *
          (Nat.card {U : GrVertex k (i - 1) // U.1 ≤ W.1 ∧ U.1 ≤ L.1} : ℚ) := by
  classical
  rw [card_adj_containing_eq L hℓ W.1]
  by_cases hWL : W.1 ≤ L.1
  · rw [if_pos hWL]
    have hexp : (2 ^ (ℓ - i) - 1) *
        (2 ^ (Module.finrank 𝔽₂ (Fin k → 𝔽₂) - ℓ + 1) - 2) = aNum k ℓ i := by
      rw [finrank_fin_fun]; rfl
    rw [Commons.LinearAlgebra.Submodule.card_neighbors_containing_of_le W.1 L.1 i ℓ hℓ hWL
      W.2 L.2, card_GrVertex_le_both_of_le i hi hWL, hexp]
    simp only [thetaQ, aNum, bNum]
    push_cast
    ring
  · rw [if_neg hWL]
    by_cases hinf : Module.finrank 𝔽₂ ↥(W.1 ⊓ L.1) = i - 1
    · have hexp : (2 : ℕ) ^ (ℓ + 1 - i) - 1 = bNum ℓ i := by
        rfl
      rw [Commons.LinearAlgebra.Submodule.card_neighbors_containing_of_inf_eq W.1 L.1 i ℓ
        W.2 L.2 hWL hinf, card_GrVertex_le_both_of_inf_eq i hi hinf, hexp, thetaQ_eq]
      push_cast
      ring
    · have hle : Module.finrank 𝔽₂ ↥(W.1 ⊓ L.1) + 2 ≤ i := by
        have h1 : Module.finrank 𝔽₂ ↥(W.1 ⊓ L.1) ≤ i := by
          have := Submodule.finrank_mono (inf_le_left : W.1 ⊓ L.1 ≤ W.1)
          rwa [W.2] at this
        have h2 : Module.finrank 𝔽₂ ↥(W.1 ⊓ L.1) ≠ i := by
          intro h
          have he : W.1 ⊓ L.1 = W.1 :=
            Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [h, W.2])
          exact hWL (by rw [← he]; exact inf_le_right)
        omega
      rw [Commons.LinearAlgebra.Submodule.card_neighbors_containing_eq_zero W.1 L.1 i ℓ
        W.2 L.2 hle, card_GrVertex_le_both_eq_zero i hle]
      push_cast
      ring

/-! ## 4. The intertwining identity -/

/-- Distributing a constant `if` over a sum. -/
lemma ite_sum_eq_g {α : Type*} [Fintype α] (p : Prop) [Decidable p] (f : α → ℚ) :
    (if p then ∑ a : α, f a else 0) = ∑ a : α, if p then f a else 0 := by
  by_cases hp : p <;> simp [hp]

/-- `if p then (if q then x else 0) else 0 = if (p ∧ q) then x else 0`. -/
lemma ite_ite_and (p q : Prop) [Decidable p] [Decidable q] (x : ℚ) :
    (if p then (if q then x else 0) else 0) = if (p ∧ q) then x else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

/-- **Double-counting normal form.** -/
lemma sum_ite_ite {α β : Type*} [Fintype α] [Fintype β] (p : α → Prop) (q : α → β → Prop)
    (f : β → ℚ) :
    (∑ a : α, if p a then (∑ b : β, if q a b then f b else 0) else 0)
      = ∑ b : β, f b * (Nat.card {a : α // p a ∧ q a b} : ℚ) := by
  classical
  rw [Finset.sum_congr rfl (fun a _ => ite_sum_eq_g (p a) (fun b => if q a b then f b else 0))]
  rw [Finset.sum_congr rfl (fun a _ =>
    Finset.sum_congr rfl (fun b _ => ite_ite_and (p a) (q a b) (f b)))]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hcard : (Finset.univ.filter (fun a : α => p a ∧ q a b)).card
      = Nat.card {a : α // p a ∧ q a b} := by
    rw [← Fintype.card_subtype (fun a : α => p a ∧ q a b), ← Nat.card_eq_fintype_card]
  rw [hcard, mul_comm]

/-- **The intertwining identity** `A₁ ∘ Ψ_i = Ψ_i ∘ (θ_i + ∂_i ∂_i^*)`, in the form
`A₁ Ψ_i = θ_i Ψ_i + b_i Ψ_{i-1} ∂_i^*`. -/
theorem adjOp_upFun (hℓ : 1 ≤ ℓ) (i : ℕ) (hi : 1 ≤ i) (hiℓ : i ≤ ℓ)
    (g : GrVertex k i → ℚ) (L : GrVertex k ℓ) :
    adjOp (upFun i g) L =
      thetaQ k ℓ i * upFun i g L +
        (bNum ℓ i : ℚ) * upFun (i - 1) (downStarFun i g) L := by
  classical
  have hmain : adjOp (upFun i g) L
      = ∑ W : GrVertex k i, g W * (Nat.card {L' : GrVertex k ℓ //
            (Gr k ℓ).Adj L L' ∧ W.1 ≤ L'.1} : ℚ) := by
    rw [adjOp_apply, Finset.sum_filter]
    simp only [upFun]
    exact sum_ite_ite (fun L' : GrVertex k ℓ => (Gr k ℓ).Adj L L')
      (fun L' W => W.1 ≤ L'.1) g
  rw [hmain]
  rw [Finset.sum_congr rfl (fun W _ => by rw [card_adj_containing hℓ i hi hiℓ L W])]
  have hsplit : ∀ W : GrVertex k i,
      g W * (thetaQ k ℓ i * (if W.1 ≤ L.1 then 1 else 0) +
          (bNum ℓ i : ℚ) * (Nat.card {U : GrVertex k (i - 1) //
            U.1 ≤ W.1 ∧ U.1 ≤ L.1} : ℚ))
        = thetaQ k ℓ i * (g W * (if W.1 ≤ L.1 then 1 else 0)) +
          (bNum ℓ i : ℚ) * (g W * (Nat.card {U : GrVertex k (i - 1) //
            U.1 ≤ W.1 ∧ U.1 ≤ L.1} : ℚ)) := fun W => by ring
  rw [Finset.sum_congr rfl (fun W _ => hsplit W)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hstep2 : ∑ W : GrVertex k i, g W * (if W.1 ≤ L.1 then 1 else 0) = upFun i g L := by
    rw [upFun]
    refine Finset.sum_congr rfl (fun W _ => ?_)
    by_cases hW : W.1 ≤ L.1 <;> simp [hW]
  have hstep3 : ∑ W : GrVertex k i,
        g W * (Nat.card {U : GrVertex k (i - 1) // U.1 ≤ W.1 ∧ U.1 ≤ L.1} : ℚ)
      = upFun (i - 1) (downStarFun i g) L := by
    have key : ∀ W : GrVertex k i, g W * (Nat.card {U : GrVertex k (i - 1) //
          U.1 ≤ W.1 ∧ U.1 ≤ L.1} : ℚ)
        = ∑ U : GrVertex k (i - 1),
            (if U.1 ≤ L.1 then 1 else 0) * (if U.1 ≤ W.1 then g W else 0) := by
      intro W
      rw [card_eq_sum_ite, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun U _ => ?_)
      by_cases hU : U.1 ≤ L.1 <;> by_cases hW : U.1 ≤ W.1 <;> simp [hU, hW]
    rw [Finset.sum_congr rfl (fun W _ => key W), Finset.sum_comm, upFun]
    refine Finset.sum_congr rfl (fun U _ => ?_)
    by_cases hU : U.1 ≤ L.1 <;> simp [hU, downStarFun]
  rw [hstep2, hstep3]

/-! ## 5. The filtration `V_0 ≤ V_1 ≤ ⋯ ≤ V_ℓ = ⊤` -/

/-- The up operator as a linear map. -/
def upLM (i : ℕ) : (GrVertex k i → ℚ) →ₗ[ℚ] (GrVertex k ℓ → ℚ) where
  toFun g := upFun i g
  map_add' f g := by
    funext L
    simp only [upFun, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun W _ => by by_cases h : W.1 ≤ L.1 <;> simp [h])
  map_smul' c f := by
    funext L
    simp only [upFun, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun W _ => by by_cases h : W.1 ≤ L.1 <;> simp [h, mul_comm])

/-- The down-star operator as a linear map. -/
def downStarLM {k : ℕ} (i : ℕ) : (GrVertex k i → ℚ) →ₗ[ℚ] (GrVertex k (i - 1) → ℚ) where
  toFun g := downStarFun i g
  map_add' f g := by
    funext U
    simp only [downStarFun, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun W _ => by by_cases h : U.1 ≤ W.1 <;> simp [h])
  map_smul' c f := by
    funext U
    simp only [downStarFun, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun W _ => by by_cases h : U.1 ≤ W.1 <;> simp [h, mul_comm])

/-- The adjacency operator as a linear map. -/
def adjOpLM {k ℓ : ℕ} : (GrVertex k ℓ → ℚ) →ₗ[ℚ] (GrVertex k ℓ → ℚ) where
  toFun f := fun L => adjOp f L
  map_add' f g := by
    funext L
    simp only [Pi.add_apply]
    rw [adjOp_apply, adjOp_apply, adjOp_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun L' _ => by simp)
  map_smul' c f := by
    funext L
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [adjOp_apply, adjOp_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun L' _ => by simp [smul_eq_mul])

lemma upLM_apply (i : ℕ) (g : GrVertex k i → ℚ) : upLM (k := k) (ℓ := ℓ) i g = upFun i g := rfl

lemma adjOpLM_apply (f : GrVertex k ℓ → ℚ) (L : GrVertex k ℓ) :
    adjOpLM (k := k) (ℓ := ℓ) f L = adjOp f L := rfl

/-- `V_i`, the span of the functions `1_{W ⊆ ·}` for `W` of dimension `i`. -/
def Vup (i : ℕ) : Submodule ℚ (GrVertex k ℓ → ℚ) := LinearMap.range (upLM (k := k) (ℓ := ℓ) i)

/-! ## 6. The Eberlein eigenvalues and the spectrum -/

/-- `Ψ_ℓ` is the identity. -/
lemma upFun_self (g : GrVertex k ℓ → ℚ) : upFun ℓ g = g := by
  funext L
  rw [upFun]
  have h1 : ∀ W : GrVertex k ℓ, (if W.1 ≤ L.1 then g W else 0) = (if W = L then g W else 0) := by
    intro W
    by_cases h : W = L
    · subst h; simp
    · have hle : ¬ W.1 ≤ L.1 := fun hh =>
        h (Subtype.ext (Submodule.eq_of_le_of_finrank_eq hh (by rw [W.2, L.2])))
      simp [h, hle]
  rw [Finset.sum_congr rfl (fun W _ => h1 W), Finset.sum_ite_eq', if_pos (Finset.mem_univ L)]

lemma Vup_self : Vup (k := k) (ℓ := ℓ) ℓ = ⊤ := by
  refine LinearMap.range_eq_top.mpr (fun y => ⟨y, ?_⟩)
  exact upFun_self y

/-- `V_0` consists of constant functions. -/
lemma Vup_zero_const {v : GrVertex k ℓ → ℚ} (hv : v ∈ Vup (k := k) (ℓ := ℓ) 0) :
    ∃ c : ℚ, v = fun _ => c := by
  obtain ⟨g, rfl⟩ := hv
  refine ⟨g ⟨⊥, finrank_bot_eq_zero k⟩, ?_⟩
  funext L
  rw [upLM_apply, upFun]
  have hsub : (Finset.univ : Finset (GrVertex k 0)) =
      {⟨⊥, finrank_bot_eq_zero k⟩} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_univ _, fun W _ => ?_⟩
    exact Subtype.ext (Submodule.finrank_eq_zero.mp W.2)
  rw [hsub, Finset.sum_singleton]
  simp

/-- `V_{i-1} ≤ V_i` for `1 ≤ i ≤ ℓ`. -/
lemma Vup_pred_le (hℓ : 1 ≤ ℓ) (i : ℕ) (hi : 1 ≤ i) (hiℓ : i ≤ ℓ) :
    Vup (k := k) (ℓ := ℓ) (i - 1) ≤ Vup (k := k) (ℓ := ℓ) i := by
  have hb : (bNum ℓ i : ℚ) ≠ 0 := by
    have hpos : 0 < bNum ℓ i := by
      unfold bNum
      have h1 : 1 ≤ ℓ + 1 - i := by omega
      calc 0 < (2:ℕ) ^ 1 - 1 := by norm_num
        _ ≤ 2 ^ (ℓ + 1 - i) - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_right (by norm_num) h1) 1
    exact_mod_cast hpos.ne'
  rintro x ⟨h, rfl⟩
  refine ⟨((bNum ℓ i : ℚ))⁻¹ • downFun i h, ?_⟩
  have hkey : upLM (k := k) (ℓ := ℓ) i (downFun i h) =
      (bNum ℓ i : ℚ) • (upLM (k := k) (ℓ := ℓ) (i - 1) h) := by
    funext L
    simp only [upLM, Pi.smul_apply, smul_eq_mul]
    exact upFun_downFun (k := k) (ℓ := ℓ) i hi h L
  rw [map_smul, hkey, smul_smul, inv_mul_cancel₀ hb, one_smul]

/-- The identity `A Ψ_i = θ_i Ψ_i + b_i Ψ_{i-1} ∂_i^*`, as a linear-map identity on
generators. -/
lemma adjOpLM_upLM (hℓ : 1 ≤ ℓ) (i : ℕ) (hi : 1 ≤ i) (hiℓ : i ≤ ℓ) (g : GrVertex k i → ℚ) :
    adjOpLM (k := k) (ℓ := ℓ) (upLM (k := k) (ℓ := ℓ) i g) =
      (thetaQ k ℓ i) • upLM (k := k) (ℓ := ℓ) i g +
        (bNum ℓ i : ℚ) • upLM (k := k) (ℓ := ℓ) (i - 1)
          (downStarLM (k := k) i g) := by
  funext L
  simp only [upLM, downStarLM, Pi.add_apply, Pi.smul_apply, smul_eq_mul, adjOpLM_apply]
  exact adjOp_upFun hℓ i hi hiℓ g L

/-- The descent: `(A - θ_i) V_i ≤ V_{i-1}`. -/
lemma adjOpLM_sub_mem_Vup_pred (hℓ : 1 ≤ ℓ) (i : ℕ) (hi : 1 ≤ i) (hiℓ : i ≤ ℓ)
    {x : GrVertex k ℓ → ℚ} (hx : x ∈ Vup (k := k) (ℓ := ℓ) i) :
    adjOpLM x - (thetaQ k ℓ i) • x ∈ Vup (k := k) (ℓ := ℓ) (i - 1) := by
  obtain ⟨g, rfl⟩ := hx
  rw [adjOpLM_upLM hℓ i hi hiℓ g]
  refine LinearMap.mem_range.mpr
    ⟨(bNum ℓ i : ℚ) • downStarLM (k := k) i g, ?_⟩
  rw [map_smul, add_sub_cancel_left]

/-- The invariance: `A V_i ≤ V_i`. -/
lemma adjOpLM_mem_Vup (hℓ : 1 ≤ ℓ) (i : ℕ) (hi : 1 ≤ i) (hiℓ : i ≤ ℓ)
    {x : GrVertex k ℓ → ℚ} (hx : x ∈ Vup (k := k) (ℓ := ℓ) i) :
    adjOpLM x ∈ Vup (k := k) (ℓ := ℓ) i := by
  have h1 := adjOpLM_sub_mem_Vup_pred hℓ i hi hiℓ hx
  have h2 : adjOpLM x = (adjOpLM x - (thetaQ k ℓ i) • x) + (thetaQ k ℓ i) • x := by abel
  rw [h2]
  exact Submodule.add_mem _ (Vup_pred_le hℓ i hi hiℓ h1) (Submodule.smul_mem _ _ hx)

/-- `(A - θ_0)` kills `V_0` (the constants). -/
lemma adjOpLM_sub_theta_zero_mem (hℓ : 1 ≤ ℓ)
    {x : GrVertex k ℓ → ℚ} (hx : x ∈ Vup (k := k) (ℓ := ℓ) 0) :
    adjOpLM x - (thetaQ k ℓ 0) • x = 0 := by
  obtain ⟨c, rfl⟩ := Vup_zero_const hx
  funext L
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
  rw [adjOpLM_apply, adjOp_const' hℓ]
  simp only [thetaQ, aNum, bNum, Nat.sub_zero, pow_zero]
  norm_num

/-! ## 7. The spectrum is contained in the Eberlein eigenvalues -/

/-- `(A - θ_0)(A - θ_1) ⋯ (A - θ_i)`, composed right to left. -/
def Spoly {k ℓ : ℕ} : ℕ → (GrVertex k ℓ → ℚ) →ₗ[ℚ] (GrVertex k ℓ → ℚ)
  | 0 => adjOpLM - (thetaQ k ℓ 0) • LinearMap.id
  | (i + 1) => Spoly i ∘ₗ (adjOpLM - (thetaQ k ℓ (i + 1)) • LinearMap.id)

/-- `S_i` maps `V_i` into `V_0`. -/
lemma Spoly_mapsTo_Vup_zero (hℓ : 1 ≤ ℓ) :
    ∀ i, i ≤ ℓ → ∀ x ∈ Vup (k := k) (ℓ := ℓ) i,
      Spoly (k := k) (ℓ := ℓ) i x ∈ Vup (k := k) (ℓ := ℓ) 0 := by
  intro i
  induction i with
  | zero =>
      intro _ x hx
      have h := adjOpLM_sub_theta_zero_mem (k := k) (ℓ := ℓ) hℓ hx
      simp only [Spoly, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at h ⊢
      rw [h]
      exact Submodule.zero_mem _
  | succ i ih =>
      intro hiℓ x hx
      have hx' : adjOpLM (k := k) (ℓ := ℓ) x - (thetaQ k ℓ (i + 1)) • x ∈
          Vup (k := k) (ℓ := ℓ) i := by
        have := adjOpLM_sub_mem_Vup_pred (k := k) (ℓ := ℓ) hℓ (i + 1) (by omega) hiℓ hx
        simpa using this
      have hmem := ih (by omega) _ hx'
      simpa only [Spoly, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply] using hmem

/-- The action of `S_i` on an eigenvector. -/
lemma Spoly_apply_eigen {lam : ℚ} {v : GrVertex k ℓ → ℚ}
    (heig : adjOpLM (k := k) (ℓ := ℓ) v = lam • v) :
    ∀ i, Spoly (k := k) (ℓ := ℓ) i v =
      (∏ j ∈ Finset.range (i + 1), (lam - thetaQ k ℓ j)) • v := by
  intro i
  induction i with
  | zero =>
      simp only [Spoly, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
      rw [heig]
      change lam • v - thetaQ k ℓ 0 • v = (∏ j ∈ Finset.range 1, (lam - thetaQ k ℓ j)) • v
      rw [Finset.prod_range_one, sub_smul]
  | succ i ih =>
      have h1 : adjOpLM (k := k) (ℓ := ℓ) v - (thetaQ k ℓ (i + 1)) • v =
          (lam - thetaQ k ℓ (i + 1)) • v := by
        rw [heig, ← sub_smul]
      have hprod : (∏ j ∈ Finset.range (i + 1 + 1), (lam - thetaQ k ℓ j)) =
          (lam - thetaQ k ℓ (i + 1)) * (∏ j ∈ Finset.range (i + 1), (lam - thetaQ k ℓ j)) := by
        rw [Finset.prod_range_succ, mul_comm]
      simp only [Spoly, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply]
      rw [h1, LinearMap.map_smul, ih, hprod, ← smul_smul]

/-- **The spectrum of the Grassmann graph is contained in the Eberlein eigenvalues.** -/
theorem adjOpLM_eigenvalue_mem (hℓ : 1 ≤ ℓ) {lam : ℚ} {v : GrVertex k ℓ → ℚ}
    (hv : v ≠ 0) (heig : adjOpLM (k := k) (ℓ := ℓ) v = lam • v) :
    ∃ j ≤ ℓ, lam = thetaQ k ℓ j := by
  classical
  set P : ℚ := ∏ j ∈ Finset.range (ℓ + 1), (lam - thetaQ k ℓ j) with hP
  have hvtop : v ∈ Vup (k := k) (ℓ := ℓ) ℓ := by
    rw [Vup_self]; exact Submodule.mem_top
  have hS := Spoly_mapsTo_Vup_zero (k := k) (ℓ := ℓ) hℓ ℓ le_rfl v hvtop
  have hSval : Spoly (k := k) (ℓ := ℓ) ℓ v = P • v := by
    rw [Spoly_apply_eigen (k := k) (ℓ := ℓ) heig ℓ, hP]
  have h0 := adjOpLM_sub_theta_zero_mem (k := k) (ℓ := ℓ) hℓ hS
  rw [hSval] at h0
  have hlin : adjOpLM (k := k) (ℓ := ℓ) (P • v) = (P * lam) • v := by
    rw [map_smul, heig, smul_smul]
  have hgoal : (P * (lam - thetaQ k ℓ 0)) • v = 0 := by
    rw [hlin, smul_smul, ← sub_smul] at h0
    convert h0 using 1
    ring
  have hc : P * (lam - thetaQ k ℓ 0) = 0 := by
    rcases smul_eq_zero.mp hgoal with h | h
    · exact h
    · exact absurd h hv
  rcases mul_eq_zero.mp hc with hP0 | h0'
  · rw [hP, Finset.prod_eq_zero_iff] at hP0
    obtain ⟨j, hj, hj0⟩ := hP0
    exact ⟨j, by simpa using hj, sub_eq_zero.mp hj0⟩
  · exact ⟨0, by omega, sub_eq_zero.mp h0'⟩

/-! ## 8. The Eberlein eigenvalue formula and the spectral gap -/

/-- `thetaQ` written out with the `ℚ`-casts pushed inside. -/
lemma thetaQ_eq_algebra (k ℓ i : ℕ) (hℓk : ℓ ≤ k) :
    thetaQ k ℓ i = ((2 : ℚ) ^ (ℓ - i) - 1) * ((2 : ℚ) ^ (k - ℓ + 1) - 2) -
      (((2 : ℚ) ^ (ℓ + 1 - i) - 1) * ((2 : ℚ) ^ i - 1)) := by
  have e1 : ((2 ^ (ℓ - i) - 1 : ℕ) : ℚ) = (2 : ℚ) ^ (ℓ - i) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ 2 ^ (ℓ - i) by exact Nat.one_le_two_pow), Nat.cast_pow]
    norm_num
  have e2 : ((2 ^ (k - ℓ + 1) - 2 : ℕ) : ℚ) = (2 : ℚ) ^ (k - ℓ + 1) - 2 := by
    have h1 : 1 ≤ k - ℓ + 1 := by omega
    rw [Nat.cast_sub (show 2 ≤ 2 ^ (k - ℓ + 1) by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (k - ℓ + 1) := Nat.pow_le_pow_right (by norm_num) h1), Nat.cast_pow]
    norm_num
  have e3 : ((2 ^ (ℓ + 1 - i) - 1 : ℕ) : ℚ) = (2 : ℚ) ^ (ℓ + 1 - i) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ 2 ^ (ℓ + 1 - i) by exact Nat.one_le_two_pow), Nat.cast_pow]
    norm_num
  have e4 : ((2 ^ i - 1 : ℕ) : ℚ) = (2 : ℚ) ^ i - 1 := by
    rw [Nat.cast_sub (show 1 ≤ 2 ^ i by exact Nat.one_le_two_pow), Nat.cast_pow]
    norm_num
  simp only [thetaQ, aNum, bNum, Nat.cast_mul]
  rw [e1, e2, e3, e4]
  try ring

/-- The Eberlein eigenvalue in closed form, for `i ≤ ℓ ≤ k - ℓ`. -/
lemma thetaQ_eq_formula (i : ℕ) (hiℓ : i ≤ ℓ) (hcodim : ℓ ≤ k - ℓ) :
    thetaQ k ℓ i =
      2 ^ (i + 1) * ((2 : ℚ) ^ (ℓ - i) - 1) * ((2 : ℚ) ^ (k - ℓ - i) - 1) -
        ((2 : ℚ) ^ i - 1) := by
  rw [thetaQ_eq_algebra k ℓ i (by omega)]
  have hx : (2 : ℚ) ^ (ℓ + 1 - i) = 2 * 2 ^ (ℓ - i) := by
    rw [show ℓ + 1 - i = (ℓ - i) + 1 from by omega, pow_succ]; ring
  have hy : (2 : ℚ) ^ (k - ℓ + 1) = 2 * (2 ^ (k - ℓ - i) * 2 ^ i) := by
    rw [show k - ℓ + 1 = (k - ℓ - i) + i + 1 from by omega, pow_add, pow_succ]; ring
  rw [hx, hy]
  ring

/-- The Eberlein eigenvalues are strictly decreasing on `[0, min ℓ (k-ℓ)]`. -/
lemma thetaQ_strictAnti (i : ℕ) (hiℓ : i + 1 ≤ ℓ) (hcodim : ℓ ≤ k - ℓ) :
    thetaQ k ℓ (i + 1) < thetaQ k ℓ i := by
  have h := Commons.Algebra.Eberlein.eberlein_strictAnti ℓ (k - ℓ) i
    (by omega) (by omega)
  have hQ : (((2 ^ (i + 2) * (2 ^ (ℓ - (i + 1)) - 1) * (2 ^ (k - ℓ - (i + 1)) - 1) : ℤ) -
        (2 ^ (i + 1) - 1) : ℤ) : ℚ) <
      (((2 ^ (i + 1) * (2 ^ (ℓ - i) - 1) * (2 ^ (k - ℓ - i) - 1) : ℤ) -
        (2 ^ i - 1) : ℤ) : ℚ) := by
    exact_mod_cast h
  rw [thetaQ_eq_formula (i + 1) (by omega) hcodim, thetaQ_eq_formula i (by omega) hcodim]
  push_cast at hQ ⊢
  linarith

/-- On `[0, min ℓ (k-ℓ)]` the Eberlein eigenvalues are antitone. -/
lemma thetaQ_le_of_le {i j : ℕ} (hij : i ≤ j) (hj : j ≤ ℓ) (hcodim : ℓ ≤ k - ℓ) :
    thetaQ k ℓ j ≤ thetaQ k ℓ i := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  induction d with
  | zero => simp
  | succ d ih =>
      have hstep : thetaQ k ℓ (i + d + 1) ≤ thetaQ k ℓ (i + d) :=
        le_of_lt (thetaQ_strictAnti (i + d) (by omega) hcodim)
      exact le_trans hstep (ih (by omega) (by omega))

/-- **Spectral gap of the Grassmann graph** (the case `ℓ ≤ k - ℓ`): every eigenvalue other
than the trivial one `θ_0 = degree` lies between `θ_ℓ` and `θ_1`. -/
theorem adjOpLM_eigenvalue_bounds (hℓ : 1 ≤ ℓ) (hcodim : ℓ ≤ k - ℓ)
    {lam : ℚ} {v : GrVertex k ℓ → ℚ} (hv : v ≠ 0)
    (heig : adjOpLM (k := k) (ℓ := ℓ) v = lam • v) (hne : lam ≠ thetaQ k ℓ 0) :
    thetaQ k ℓ ℓ ≤ lam ∧ lam ≤ thetaQ k ℓ 1 := by
  obtain ⟨j, hj, rfl⟩ := adjOpLM_eigenvalue_mem (k := k) (ℓ := ℓ) hℓ hv heig
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · exact absurd (by rw [h]) hne
    · exact h
  exact ⟨thetaQ_le_of_le hj le_rfl hcodim, thetaQ_le_of_le hj1 hj hcodim⟩

/-- The trivial eigenvalue is the degree. -/
lemma thetaQ_zero_eq_degree (hℓ : 1 ≤ ℓ) :
    thetaQ k ℓ 0 = (((2 ^ ℓ - 1) * (2 ^ (k - ℓ + 1) - 2) : ℕ) : ℚ) := by
  rw [thetaQ_eq]
  have h2 : ((2 ^ (0:ℕ) - 1 : ℕ) : ℚ) = 0 := by norm_num
  rw [h2, mul_zero, sub_zero]
  rfl

/-! ## 9. The level-1 eigenvector: `θ_1` is an eigenvalue -/

/-- `Ψ_0 g` is the constant function `g ⊥`. -/
lemma upFun_zero (g : GrVertex k 0 → ℚ) :
    upFun 0 g = fun _ : GrVertex k ℓ => g ⟨⊥, finrank_bot_eq_zero k⟩ := by
  funext L
  rw [upFun]
  have hsub : (Finset.univ : Finset (GrVertex k 0)) = {⟨⊥, finrank_bot_eq_zero k⟩} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_univ _, fun W _ => ?_⟩
    exact Subtype.ext (Submodule.finrank_eq_zero.mp W.2)
  rw [hsub, Finset.sum_singleton]
  simp

/-- `Ψ_1` applied to the delta function at a line `W` is the indicator of `W ⊆ ·`. -/
lemma upFun_one_delta (W : GrVertex k 1) (L : GrVertex k ℓ) :
    upFun 1 (fun W' : GrVertex k 1 => if W' = W then (1 : ℚ) else 0) L =
      if W.1 ≤ L.1 then 1 else 0 := by
  classical
  rw [upFun]
  rw [Finset.sum_congr rfl (fun W' _ => ?_), Finset.sum_ite_eq', if_pos (Finset.mem_univ W)]
  by_cases h : W' = W
  · subst h; simp
  · simp [h]

/-- `∂_1^* δ_W` is `1` at `⊥`. -/
lemma downStarFun_one_delta (W : GrVertex k 1) :
    downStarFun 1 (fun W' : GrVertex k 1 => if W' = W then (1 : ℚ) else 0)
        ⟨⊥, finrank_bot_eq_zero k⟩ = 1 := by
  classical
  rw [downStarFun]
  rw [Finset.sum_congr rfl (fun W' _ => if_pos (by simp)), Finset.sum_ite_eq',
    if_pos (Finset.mem_univ W)]

/-- The degree is `θ_1 + 2^k - 1`. -/
lemma degree_eq_thetaQ_one (hℓ : 1 ≤ ℓ) (hcodim : ℓ ≤ k - ℓ) :
    (((2 ^ ℓ - 1) * (2 ^ (k - ℓ + 1) - 2) : ℕ) : ℚ) = thetaQ k ℓ 1 + ((2 : ℚ) ^ k - 1) := by
  have e0 : ((2 ^ ℓ - 1 : ℕ) : ℚ) = (2 : ℚ) ^ ℓ - 1 := by
    rw [Nat.cast_sub (show 1 ≤ 2 ^ ℓ by exact Nat.one_le_two_pow), Nat.cast_pow]
    norm_num
  have e1 : ((2 ^ (k - ℓ + 1) - 2 : ℕ) : ℚ) = (2 : ℚ) ^ (k - ℓ + 1) - 2 := by
    have h1 : 1 ≤ k - ℓ + 1 := by omega
    rw [Nat.cast_sub (show 2 ≤ 2 ^ (k - ℓ + 1) by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (k - ℓ + 1) := Nat.pow_le_pow_right (by norm_num) h1), Nat.cast_pow]
    norm_num
  have e2 : ((2 ^ (ℓ - 1) - 1 : ℕ) : ℚ) = (2 : ℚ) ^ (ℓ - 1) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ 2 ^ (ℓ - 1) by exact Nat.one_le_two_pow), Nat.cast_pow]
    norm_num
  have e3 : ((2 ^ (k - ℓ - 1) - 1 : ℕ) : ℚ) = (2 : ℚ) ^ (k - ℓ - 1) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ 2 ^ (k - ℓ - 1) by exact Nat.one_le_two_pow), Nat.cast_pow]
    norm_num
  have hx : (2 : ℚ) ^ ℓ = 2 * 2 ^ (ℓ - 1) := by
    conv_lhs => rw [show ℓ = (ℓ - 1) + 1 from by omega]
    rw [pow_succ']
  have hy : (2 : ℚ) ^ k = 2 ^ (ℓ - 1) * 2 ^ (k - ℓ + 1) := by
    conv_lhs => rw [show k = (ℓ - 1) + (k - ℓ + 1) from by omega]
    rw [pow_add]
  have hz : (2 : ℚ) ^ (k - ℓ + 1) = 4 * 2 ^ (k - ℓ - 1) := by
    conv_lhs => rw [show k - ℓ + 1 = (k - ℓ - 1) + 2 from by omega]
    rw [pow_add]
    ring
  rw [thetaQ_eq_formula (k := k) (ℓ := ℓ) 1 (by omega) hcodim]
  simp only [Nat.cast_mul]
  rw [e0, e1, hx, hy, hz]
  ring

/-- **The level-1 eigenfunction**: for `W` a line, `Ψ_1 δ_W - μ` (with
`μ = (2^ℓ-1)/(2^k-1)`) is an eigenfunction of the adjacency operator with eigenvalue `θ_1`. -/
theorem isEigenvector_theta_one (hℓ : 1 ≤ ℓ) (hcodim : ℓ ≤ k - ℓ) (W : GrVertex k 1) :
    adjOpLM (k := k) (ℓ := ℓ)
        (upFun 1 (fun W' : GrVertex k 1 => if W' = W then (1 : ℚ) else 0) -
          (((2 ^ ℓ - 1 : ℕ) : ℚ) / ((2 ^ k - 1 : ℕ) : ℚ)) • (1 : GrVertex k ℓ → ℚ)) =
      (thetaQ k ℓ 1) •
        (upFun 1 (fun W' : GrVertex k 1 => if W' = W then (1 : ℚ) else 0) -
          (((2 ^ ℓ - 1 : ℕ) : ℚ) / ((2 ^ k - 1 : ℕ) : ℚ)) • (1 : GrVertex k ℓ → ℚ)) := by
  classical
  set mu : ℚ := ((2 ^ ℓ - 1 : ℕ) : ℚ) / ((2 ^ k - 1 : ℕ) : ℚ) with hmu
  set δ : GrVertex k 1 → ℚ := fun W' => if W' = W then 1 else 0 with hdelta
  have hΨ0 : upFun 0 (downStarFun 1 δ) = (1 : GrVertex k ℓ → ℚ) := by
    rw [hdelta, upFun_zero]
    funext L
    rw [downStarFun_one_delta W]
    simp
  have hb1 : bNum ℓ 1 = 2 ^ ℓ - 1 := by
    unfold bNum
    rw [show ℓ + 1 - 1 = ℓ from by omega]
  have hμ : (((2 ^ ℓ - 1) * (2 ^ (k - ℓ + 1) - 2) : ℕ) : ℚ) * mu =
      ((2 ^ ℓ - 1 : ℕ) : ℚ) + mu * thetaQ k ℓ 1 := by
    have e1 : ((2 ^ ℓ - 1 : ℕ) : ℚ) = (2 : ℚ) ^ ℓ - 1 := by
      rw [Nat.cast_sub (show 1 ≤ 2 ^ ℓ by exact Nat.one_le_two_pow), Nat.cast_pow]
      norm_num
    have e2 : ((2 ^ k - 1 : ℕ) : ℚ) = (2 : ℚ) ^ k - 1 := by
      rw [Nat.cast_sub (show 1 ≤ 2 ^ k by exact Nat.one_le_two_pow), Nat.cast_pow]
      norm_num
    have h2k : ((2 ^ k - 1 : ℕ) : ℚ) ≠ 0 := by
      have hk1 : 1 ≤ k := by omega
      have hpow : (2 : ℕ) ≤ 2 ^ k := by
        calc (2 : ℕ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk1
      have hpos : (0 : ℕ) < 2 ^ k - 1 := by omega
      exact_mod_cast hpos.ne'
    rw [degree_eq_thetaQ_one hℓ hcodim, hmu, e1]
    field_simp
    rw [e2]
    ring
  funext L
  have hsum : (∑ L' ∈ Finset.univ.filter (fun L' : GrVertex k ℓ => (Gr k ℓ).Adj L L'),
      upFun 1 δ L') = thetaQ k ℓ 1 * upFun 1 δ L + ((2 ^ ℓ - 1 : ℕ) : ℚ) := by
    rw [← adjOp_apply, adjOp_upFun (k := k) (ℓ := ℓ) hℓ 1 le_rfl hℓ δ L, hΨ0, hb1]
    simp only [Pi.one_apply, mul_one]
  rw [adjOpLM_apply, adjOp_apply]
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
  rw [Finset.sum_sub_distrib, hsum, Finset.sum_const, card_adjFinset_eq_degree,
    Gr_degree_eq_value hℓ, nsmul_eq_mul]
  linarith [hμ]

/-- **`θ_1` is an eigenvalue of `Gr k ℓ`**: the spectral gap is attained. -/
theorem exists_eigenvector_theta_one (hℓ : 1 ≤ ℓ) (hcodim : ℓ ≤ k - ℓ) :
    ∃ v : GrVertex k ℓ → ℚ, v ≠ 0 ∧ adjOpLM (k := k) (ℓ := ℓ) v = (thetaQ k ℓ 1) • v := by
  classical
  have h1k : 1 ≤ k := by omega
  have hk : ℓ < k := by omega
  obtain ⟨W⟩ : Nonempty (GrVertex k 1) := nonempty_GrVertex_of_le h1k
  refine ⟨upFun 1 (fun W' : GrVertex k 1 => if W' = W then (1 : ℚ) else 0) -
      (((2 ^ ℓ - 1 : ℕ) : ℚ) / ((2 ^ k - 1 : ℕ) : ℚ)) • (1 : GrVertex k ℓ → ℚ), ?_, ?_⟩
  · -- the function is nonzero: evaluate it at a vertex containing `W`
    obtain ⟨L, hWL, -, hLfin⟩ :=
      Commons.LinearAlgebra.Submodule.exists_submodule_between_finrank (K := 𝔽₂)
        (V := Fin k → 𝔽₂) W.1 ⊤ le_top (ℓ := ℓ) (by rw [W.2]; exact hℓ)
        (by rw [finrank_top, finrank_fin_fun]; omega)
    intro hzero
    have hL := congrFun hzero ⟨L, hLfin⟩
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.one_apply, Pi.zero_apply, smul_eq_mul,
      mul_one] at hL
    rw [upFun_one_delta W ⟨L, hLfin⟩, if_pos hWL] at hL
    have hden : (0 : ℚ) < ((2 ^ k - 1 : ℕ) : ℚ) := by
      have hk1 : 1 ≤ k := by omega
      have hpow : (2 : ℕ) ≤ 2 ^ k := by
        calc (2 : ℕ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk1
      have hpos : (0 : ℕ) < 2 ^ k - 1 := by omega
      exact_mod_cast hpos
    have hlt : ((2 ^ ℓ - 1 : ℕ) : ℚ) < ((2 ^ k - 1 : ℕ) : ℚ) := by
      have h2 : (2 : ℕ) ^ ℓ < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) hk
      have h3 : (2 : ℕ) ^ ℓ - 1 < 2 ^ k - 1 := by
        have h1 : 1 ≤ (2 : ℕ) ^ ℓ := Nat.one_le_two_pow
        omega
      exact_mod_cast h3
    have hmu1 : ((2 ^ ℓ - 1 : ℕ) : ℚ) / ((2 ^ k - 1 : ℕ) : ℚ) < 1 := by
      rw [div_lt_one hden]; exact hlt
    linarith
  · exact isEigenvector_theta_one (k := k) (ℓ := ℓ) hℓ hcodim W

end

end F2
end Submission.Grassmann
