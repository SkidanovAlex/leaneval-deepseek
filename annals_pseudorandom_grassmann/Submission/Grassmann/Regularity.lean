import Submission.Grassmann.Counting
import Submission.Grassmann.Expansion

/-!
# Regularity of the Grassmann graph `Gr_{k,ℓ}` (Layer 2)

The expansion functional `Φ G S hS` is meaningful for regular graphs: for an
`n`-vertex `d`-regular graph, `Φ(S) = |E(S,S̄)| / (d · |S|)`.  Here we show that the
Grassmann graph `Gr k ℓ` (vertices: `ℓ`-dimensional subspaces of `𝔽₂ᵏ`, adjacent when
`dim (L ⊓ L') = ℓ - 1`) is vertex-transitive, hence regular: all vertices have the same
degree.

The proof is the classical one: the group `GL_k(𝔽₂)` acts on `Gr k ℓ` (an invertible
linear map `e` sends `L` to `L.map e`), this action preserves adjacency, and it is
transitive (two `ℓ`-subspaces are isomorphic, and any linear equivalence between them
extends to an automorphism of the ambient space by
`Submodule.exists_linearEquiv_restrict_eq`).

The exact common degree `(2^ℓ - 1)·(2^{k-ℓ+1} - 2)` is not stated here; regularity is
what the expansion functional needs (e.g. to instantiate `Phi_le_one`).
-/

open PseudorandomGrassmann
open Module Submodule SimpleGraph Finset Filter

set_option autoImplicit false

local notation "𝔽₂" => ZMod 2

namespace Submission.Grassmann
namespace F2

variable {k ℓ : ℕ}

/-- The action of an invertible linear map `e` on the Grassmannian: `L ↦ L.map e`. -/
noncomputable def grMap (e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂)) (L : GrVertex k ℓ) :
    GrVertex k ℓ :=
  ⟨L.1.map (e : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂)),
    (LinearEquiv.finrank_eq (e.submoduleMap L.1)).symm.trans L.2⟩

/-- The underlying submodule of `grMap e L` is `L.map e`. -/
lemma grMap_val (e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂)) (L : GrVertex k ℓ) :
    (grMap e L).1 = L.1.map (e : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂)) := rfl

/-- `grMap e.symm` is a left inverse of `grMap e`. -/
lemma grMap_symm_grMap (e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂)) (L : GrVertex k ℓ) :
    grMap e.symm (grMap e L) = L := by
  apply Subtype.ext
  rw [grMap_val, grMap_val]
  ext x
  simp only [Submodule.mem_map]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, hyx⟩
    rw [← hyx]
    simpa using hz
  · intro hx
    exact ⟨e x, ⟨x, hx, rfl⟩, by simp⟩

/-- `grMap e.symm` is a right inverse of `grMap e`. -/
lemma grMap_grMap_symm (e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂)) (L : GrVertex k ℓ) :
    grMap e (grMap e.symm L) = L := by
  apply Subtype.ext
  rw [grMap_val, grMap_val]
  ext x
  simp only [Submodule.mem_map]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, hyx⟩
    rw [← hyx]
    simpa using hz
  · intro hx
    exact ⟨e.symm x, ⟨x, hx, rfl⟩, by simp⟩

/-- `grMap e` is injective. -/
lemma grMap_injective (e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂)) :
    Function.Injective (grMap e (ℓ := ℓ) (k := k)) := by
  intro L L' h
  have h' := congrArg (grMap e.symm) h
  rwa [grMap_symm_grMap, grMap_symm_grMap] at h'

/-- `grMap e` preserves the dimension of intersections of vertices. -/
lemma grMap_finrank_inf (e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂)) (X Y : GrVertex k ℓ) :
    Module.finrank 𝔽₂ ↥((grMap e X).1 ⊓ (grMap e Y).1) =
      Module.finrank 𝔽₂ ↥(X.1 ⊓ Y.1) := by
  rw [grMap_val, grMap_val,
    ← Submodule.map_inf ((e : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂)))
      (show Function.Injective ⇑(e : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂)) from e.injective)]
  exact (LinearEquiv.finrank_eq (e.submoduleMap (X.1 ⊓ Y.1))).symm

/-- `grMap e` preserves (and reflects) adjacency of the Grassmann graph. -/
lemma grMap_adj_iff (e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂)) (L L' : GrVertex k ℓ) :
    (Gr k ℓ).Adj (grMap e L) (grMap e L') ↔ (Gr k ℓ).Adj L L' := by
  have hne : grMap e L ≠ grMap e L' ↔ L ≠ L' := (grMap_injective e).ne_iff
  have hfinX := grMap_finrank_inf e L L'
  have hfinY := grMap_finrank_inf e L' L
  simp only [Gr, SimpleGraph.fromRel, hne, hfinX, hfinY]

/-- The permutation of the Grassmannian induced by `e`, as a graph isomorphism. -/
noncomputable def grMapIso (e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂)) :
    Gr k ℓ ≃g Gr k ℓ where
  toEquiv :=
    { toFun := grMap e
      invFun := grMap e.symm
      left_inv := grMap_symm_grMap e
      right_inv := grMap_grMap_symm e }
  map_rel_iff' := fun {L L'} => grMap_adj_iff e L L'

open Classical in
/-- Graph isomorphisms preserve vertex degrees. -/
lemma degree_eq_of_iso {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (f : G ≃g G) (v : V) : G.degree (f v) = G.degree v := by
  rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
  exact (Fintype.card_congr (SimpleGraph.Iso.mapNeighborSet f v)).symm

open Classical in
/-- The action of `GL_k(𝔽₂)` preserves vertex degrees of `Gr k ℓ`. -/
lemma degree_grMap (e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂)) (L : GrVertex k ℓ) :
    (Gr k ℓ).degree (grMap e L) = (Gr k ℓ).degree L :=
  degree_eq_of_iso (G := Gr k ℓ) (grMapIso e) L

/-- Two `ℓ`-dimensional subspaces of `𝔽₂ᵏ` are related by some invertible linear map. -/
lemma exists_grMap_eq (L L' : GrVertex k ℓ) :
    ∃ e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂), grMap e L = L' := by
  classical
  have hdim : Module.finrank 𝔽₂ ↥L.1 = Module.finrank 𝔽₂ ↥L'.1 := by rw [L.2, L'.2]
  let f : ↥L.1 ≃ₗ[𝔽₂] ↥L'.1 := LinearEquiv.ofFinrankEq ↥L.1 ↥L'.1 hdim
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq (W := L.1) (W' := L'.1) f
  refine ⟨g, ?_⟩
  have hmap : L.1.map (g : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂)) = L'.1 := by
    apply le_antisymm
    · rintro _ ⟨x, hxL, rfl⟩
      have hx : (f ⟨x, hxL⟩ : Fin k → 𝔽₂) =
          ((g : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂)) x : Fin k → 𝔽₂) := hg ⟨x, hxL⟩
      rw [← hx]
      exact (f ⟨x, hxL⟩).2
    · intro y hyL'
      obtain ⟨x, hx⟩ := f.surjective ⟨y, hyL'⟩
      refine ⟨x.1, x.2, ?_⟩
      have hx' : (f x : Fin k → 𝔽₂) =
          ((g : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂)) x.1 : Fin k → 𝔽₂) := hg x
      rw [← hx', congrArg Subtype.val hx]
  apply Subtype.ext
  rw [grMap_val, hmap]

open Classical in
/-- **Regularity of the Grassmann graph**: any two vertices have the same degree. -/
theorem Gr_degree_eq (L L' : GrVertex k ℓ) :
    (Gr k ℓ).degree L = (Gr k ℓ).degree L' := by
  obtain ⟨e, he⟩ := exists_grMap_eq L L'
  rw [← he]
  exact (degree_grMap e L).symm

open Classical in
/-- The expansion functional of the Grassmann graph takes values at most `1`. -/
lemma Gr_Phi_le_one (S : Finset (GrVertex k ℓ)) (hS : S.Nonempty) :
    Φ (Gr k ℓ) S hS ≤ 1 :=
  Phi_le_one (Gr k ℓ) S hS (fun v _ => le_of_eq (Gr_degree_eq v hS.choose))

end F2
end Submission.Grassmann
