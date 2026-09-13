import Mathlib
import Submission.Grassmann.Degree
import Submission.Commons.LinearAlgebra.Submodule.card_submodule_finrank_inf_eq

/-!
# The association scheme of the Grassmann graph `Gr_{k,ℓ}` (Layer 3, combinatorial core)

This file begins the layer of the project that supports the spectral / Fourier analysis of
`Gr k ℓ`, the machinery underlying the Khot--Minzer--Safra theorem.

The *Grassmann distance* of two `ℓ`-dimensional subspaces `L, L'` of `𝔽₂ᵏ` is
`d(L,L') = ℓ - dim (L ⊓ L')`; it takes values in `{0, 1, …, min ℓ (k-ℓ)}`, `d = 0` iff
`L = L'`, and `d = 1` iff `L` and `L'` are adjacent (so `Gr k ℓ` is the distance-`1`
graph of the association scheme `J_2(k, ℓ)`).

Main results:

* `grDist_eq_zero_iff`, `grDist_comm`, `adj_iff_grDist_eq_one`;
* `card_dist_eq`: the size of the distance-`i` sphere,
  `#{L' : d(L,L') = i} = 2 ^ (i * i) * [ℓ choose ℓ-i]_2 * [k-ℓ choose i]_2`,
  a consequence of the distance distribution
  `Commons.LinearAlgebra.Submodule.card_submodule_finrank_inf_eq`;
* the adjacency operator `adjOp` on functions on the vertex set, its self-adjointness
  (`adjOp_comm`) and its action on constants (`adjOp_const`).
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

variable {k ℓ : ℕ}

/-! ## 1. The Grassmann distance -/

/-- The **Grassmann distance** `d(L,L') = ℓ - dim (L ⊓ L')`. -/
def grDist (L L' : GrVertex k ℓ) : ℕ := ℓ - Module.finrank 𝔽₂ ↥(L.1 ⊓ L'.1)

lemma grDist_comm (L L' : GrVertex k ℓ) : grDist L L' = grDist L' L := by
  rw [grDist, grDist, inf_comm]

lemma grDist_self (L : GrVertex k ℓ) : grDist L L = 0 := by
  rw [grDist, inf_idem, L.2, Nat.sub_self]

lemma grDist_eq_zero_iff {L L' : GrVertex k ℓ} : grDist L L' = 0 ↔ L = L' := by
  constructor
  · intro h
    have hfin : Module.finrank 𝔽₂ ↥(L.1 ⊓ L'.1) = ℓ := by
      have hle : Module.finrank 𝔽₂ ↥(L.1 ⊓ L'.1) ≤ ℓ := by
        have hh := Submodule.finrank_mono (inf_le_left : L.1 ⊓ L'.1 ≤ L.1)
        rw [L.2] at hh
        exact hh
      simp only [grDist] at h
      omega
    have h1 : L.1 ≤ L'.1 := by
      have h2 : (L.1 ⊓ L'.1) = L.1 :=
        Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [hfin, L.2])
      rw [← h2]
      exact inf_le_right
    exact Subtype.ext (Submodule.eq_of_le_of_finrank_eq h1 (by rw [L.2, L'.2]))
  · rintro rfl
    exact grDist_self L

/-- Adjacency in `Gr k ℓ` is the same as Grassmann distance `1`. -/
lemma adj_iff_grDist_eq_one (L L' : GrVertex k ℓ) (hℓ : 1 ≤ ℓ) :
    (Gr k ℓ).Adj L L' ↔ grDist L L' = 1 := by
  rw [Gr, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, hd | hd⟩
    · simp only [grDist]
      rw [hd]
      omega
    · simp only [grDist]
      rw [inf_comm, hd]
      omega
  · intro h
    have hfin : Module.finrank 𝔽₂ ↥(L.1 ⊓ L'.1) = ℓ - 1 := by
      simp only [grDist] at h
      omega
    refine ⟨?_, Or.inl hfin⟩
    intro heq
    rw [heq, inf_idem, L'.2] at hfin
    omega

/-- The Grassmann distance is at most `min ℓ (k - ℓ)`. -/
lemma grDist_le (L L' : GrVertex k ℓ) : grDist L L' ≤ ℓ := by
  simp only [grDist]
  omega

lemma grDist_le_codim (L L' : GrVertex k ℓ) : grDist L L' ≤ k - ℓ := by
  have hsp := Submodule.finrank_sup_add_finrank_inf_eq (s := L.1) (t := L'.1)
  have hsup : Module.finrank 𝔽₂ ↥(L.1 ⊔ L'.1) ≤ k := by
    have h := Submodule.finrank_le (L.1 ⊔ L'.1 : Submodule 𝔽₂ (Fin k → 𝔽₂))
    rwa [finrank_fin_fun] at h
  rw [L.2, L'.2] at hsp
  simp only [grDist]
  omega

/-! ## 2. The distance spheres -/

open Classical in
/-- The distance-`i` sphere of a vertex: its cardinality is
`2 ^ (i * i) * [ℓ choose ℓ-i]_2 * [k-ℓ choose i]_2` for `i ≤ ℓ ≤ k`. -/
lemma card_dist_eq (L : GrVertex k ℓ) (i : ℕ) (hi : i ≤ ℓ) (hk : ℓ ≤ k) :
    Nat.card {L' : GrVertex k ℓ // grDist L L' = i} =
      2 ^ (i * i) * grCount ℓ (ℓ - i) * grCount (k - ℓ) i := by
  have hbij : Nat.card {L' : GrVertex k ℓ // grDist L L' = i} =
      Nat.card {L' : Submodule 𝔽₂ (Fin k → 𝔽₂) // Module.finrank 𝔽₂ L' = ℓ ∧
        Module.finrank 𝔽₂ ↥(L.1 ⊓ L') = ℓ - i} := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun L' => ⟨L'.1.1, L'.1.2, by
          have hle : Module.finrank 𝔽₂ ↥(L.1 ⊓ L'.1.1) ≤ ℓ := by
            have hh := Submodule.finrank_mono (inf_le_left : L.1 ⊓ L'.1.1 ≤ L.1)
            rw [L.2] at hh
            exact hh
          have h := L'.2
          simp only [grDist] at h
          omega⟩
        invFun := fun X => ⟨⟨X.1, X.2.1⟩, by
          have h := X.2.2
          simp only [grDist]
          omega⟩
        left_inv := fun L' => Subtype.ext rfl
        right_inv := fun X => Subtype.ext rfl }
  rw [hbij]
  rw [Commons.LinearAlgebra.Submodule.card_submodule_finrank_inf_eq (V := Fin k → 𝔽₂) L.1 ℓ ℓ (ℓ - i)
    L.2 (by omega) (by omega) (by rw [finrank_fin_fun]; exact hk)]
  rw [finrank_fin_fun, show ℓ - (ℓ - i) = i from by omega]
  rfl

/-! ## 3. The adjacency operator -/

open Classical in
/-- The **adjacency operator** of the Grassmann graph acting on functions on the vertex
set: `(adjOp f) L = ∑_{L' ~ L} f L'`. -/
def adjOp {R : Type*} [CommSemiring R] (f : GrVertex k ℓ → R) (L : GrVertex k ℓ) : R :=
  ∑ L' ∈ Finset.univ.filter (fun L' => (Gr k ℓ).Adj L L'), f L'

open Classical in
lemma adjOp_apply {R : Type*} [CommSemiring R] (f : GrVertex k ℓ → R) (L : GrVertex k ℓ) :
    adjOp f L = ∑ L' ∈ Finset.univ.filter (fun L' => (Gr k ℓ).Adj L L'), f L' := rfl

/-- The adjacency operator is self-adjoint for the uniform measure. -/
lemma adjOp_comm (f g : GrVertex k ℓ → ℚ) :
    ∑ L, f L * adjOp g L = ∑ L, adjOp f L * g L := by
  classical
  have hlhs : ∀ L, f L * adjOp g L =
      ∑ L', if (Gr k ℓ).Adj L L' then f L * g L' else 0 := by
    intro L
    rw [adjOp, Finset.mul_sum, Finset.sum_filter]
  have hrhs : ∀ L, adjOp f L * g L =
      ∑ L', if (Gr k ℓ).Adj L L' then f L' * g L else 0 := by
    intro L
    rw [adjOp, Finset.sum_mul, Finset.sum_filter]
  rw [Finset.sum_congr rfl (fun L _ => hlhs L), Finset.sum_congr rfl (fun L _ => hrhs L)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  by_cases h : (Gr k ℓ).Adj y x
  · have h' : (Gr k ℓ).Adj x y := h.symm
    simp only [h, h']
  · have h' : ¬ (Gr k ℓ).Adj x y := fun hh => h hh.symm
    simp only [h, h']

open Classical in
/-- The number of neighbours of a vertex, as a `Finset` cardinality. -/
lemma card_adjFinset_eq_degree (L : GrVertex k ℓ) :
    (Finset.univ.filter (fun L' : GrVertex k ℓ => (Gr k ℓ).Adj L L')).card =
      (Gr k ℓ).degree L := by
  rw [← Fintype.card_subtype (fun L' : GrVertex k ℓ => (Gr k ℓ).Adj L L')]
  exact SimpleGraph.card_neighborSet_eq_degree (G := Gr k ℓ) (v := L)

open Classical in
/-- The adjacency operator applied to a constant function. -/
lemma adjOp_const (c : ℚ) (L : GrVertex k ℓ) :
    adjOp (fun _ => c) L = (Gr k ℓ).degree L * c := by
  rw [adjOp, Finset.sum_const, card_adjFinset_eq_degree, nsmul_eq_mul]

open Classical in
/-- For `1 ≤ ℓ`, the adjacency operator applied to a constant function is
`((2^ℓ - 1) * (2^(k-ℓ+1) - 2)) * c`. -/
lemma adjOp_const' (hℓ : 1 ≤ ℓ) (c : ℚ) (L : GrVertex k ℓ) :
    adjOp (fun _ => c) L = ((((2 ^ ℓ - 1) * (2 ^ (k - ℓ + 1) - 2)) : ℕ) : ℚ) * c := by
  rw [adjOp_const, Gr_degree_eq_value hℓ L]

end

end F2
end Submission.Grassmann
