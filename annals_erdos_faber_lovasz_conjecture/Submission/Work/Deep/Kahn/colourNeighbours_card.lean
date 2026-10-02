import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.Defs

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.Deep.Kahn

open ErdosFaberLovaszConjecture

/-- **The colour-neighbourhood of an edge has size `C * (D - 1)`.**

In a linear hypergraph `𝓗` on `Fin n` all of whose edges have `C` vertices and in
which, for every vertex `x` and colour `γ`, exactly `D` edges through `x` carry
`γ` in their list `L` (whenever at least one does), the edges `f ≠ e` meeting `e`
with `γ ∈ L f` number exactly `C * (D - 1)`.

Indeed, by linearity such an `f` meets `e` in a *unique* vertex `v`, so the
edges in question are partitioned by the vertex `v ∈ e` they contain; through
each `v ∈ e` there are `D` edges with `γ ∈ L f`, one of which is `e` itself,
hence `D - 1` others, and `e` has `C` vertices. -/
theorem colourNeighbours_card {n c C D : ℕ} (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)) (L : 𝓗 → Finset (Fin c)) (hlin : 𝓗.IsLinear) (hsize : ∀ e : 𝓗, ErdosFaberLovaszConjecture.edgeSize (e : Set (Fin n)) = C) (hdeg : ∀ x : Fin n, ∀ γ : Fin c, (∃ e : 𝓗, x ∈ (e : Set (Fin n)) ∧ γ ∈ L e) → Nat.card {e : 𝓗 // x ∈ (e : Set (Fin n)) ∧ γ ∈ L e} = D) (e : 𝓗) (γ : Fin c) (hγ : γ ∈ L e) : Nat.card {f : 𝓗 // f ≠ e ∧ ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty ∧ γ ∈ L f} = C * (D - 1) := by
  classical
  haveI : Fintype 𝓗 := Fintype.ofFinite 𝓗
  -- the vertex set of `e`
  set E : Set (Fin n) := (e : Set (Fin n)) with hE
  -- the edges `≠ e` meeting `e` and carrying the colour `γ`
  set S : Finset 𝓗 := (Finset.univ : Finset 𝓗).filter
    (fun f : 𝓗 => f ≠ e ∧ ((f : Set (Fin n)) ∩ E).Nonempty ∧ γ ∈ L f) with hS
  -- the edges `≠ e` through `v` carrying the colour `γ`
  set Cv : Fin n → Finset 𝓗 := fun v => (Finset.univ : Finset 𝓗).filter
    (fun f : 𝓗 => f ≠ e ∧ v ∈ (f : Set (Fin n)) ∧ γ ∈ L f) with hCv
  -- all edges through `v` carrying the colour `γ`
  set T : Fin n → Finset 𝓗 := fun v => (Finset.univ : Finset 𝓗).filter
    (fun f : 𝓗 => v ∈ (f : Set (Fin n)) ∧ γ ∈ L f) with hT
  -- the left-hand side is the cardinality of `S`
  have hLHS : Nat.card {f : 𝓗 // f ≠ e ∧ ((f : Set (Fin n)) ∩ E).Nonempty ∧ γ ∈ L f}
      = S.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, hS]
  -- through a vertex `v ∈ e` there are exactly `D` edges carrying the colour `γ`
  have hTcard : ∀ v ∈ ErdosFaberLovaszConjecture.verts E, (T v).card = D := by
    intro v hv
    have hvE : v ∈ E := (ErdosFaberLovaszConjecture.mem_verts E v).mp hv
    have hd := hdeg v γ ⟨e, hvE, hγ⟩
    rw [hT]
    rw [← hd, Nat.card_eq_fintype_card]
    exact (Fintype.card_subtype (fun f : 𝓗 => v ∈ (f : Set (Fin n)) ∧ γ ∈ L f)).symm
  -- of which exactly one is `e`, so `D - 1` others
  have hCvcard : ∀ v ∈ ErdosFaberLovaszConjecture.verts E, (Cv v).card = D - 1 := by
    intro v hv
    have hvE : v ∈ E := (ErdosFaberLovaszConjecture.mem_verts E v).mp hv
    have heT : e ∈ T v := by
      rw [hT, Finset.mem_filter]
      exact ⟨Finset.mem_univ e, hvE, hγ⟩
    have hCeq : Cv v = (T v).erase e := by
      ext f
      rw [hCv, hT]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    rw [hCeq, Finset.card_erase_of_mem heT, hTcard v hv]
  -- by linearity, `S` is the disjoint union of the `Cv v` over the vertices of `e`
  have hSuni : S = (ErdosFaberLovaszConjecture.verts E).biUnion Cv := by
    ext f
    constructor
    · intro hf
      rw [hS, Finset.mem_filter] at hf
      obtain ⟨-, hne, hnon, hγf⟩ := hf
      obtain ⟨v, hvfe⟩ := hnon
      rw [Finset.mem_biUnion]
      refine ⟨v, (ErdosFaberLovaszConjecture.mem_verts E v).mpr hvfe.2, ?_⟩
      rw [hCv, Finset.mem_filter]
      exact ⟨Finset.mem_univ f, hne, hvfe.1, hγf⟩
    · intro hf
      rw [Finset.mem_biUnion] at hf
      obtain ⟨v, hv, hfv⟩ := hf
      rw [hCv, Finset.mem_filter] at hfv
      obtain ⟨-, hne, hvf, hγf⟩ := hfv
      rw [hS, Finset.mem_filter]
      exact ⟨Finset.mem_univ f, hne,
        ⟨v, hvf, (ErdosFaberLovaszConjecture.mem_verts E v).mp hv⟩, hγf⟩
  -- the parts are pairwise disjoint: a common edge would contain two distinct
  -- vertices of `e`, hence would be `e` itself by linearity
  have hdisj : ∀ v ∈ ErdosFaberLovaszConjecture.verts E,
      ∀ w ∈ ErdosFaberLovaszConjecture.verts E, v ≠ w → Disjoint (Cv v) (Cv w) := by
    intro v hv w hw hvw
    rw [Finset.disjoint_left]
    intro f hfv hfw
    rw [hCv, Finset.mem_filter] at hfv hfw
    obtain ⟨-, hne, hvf, -⟩ := hfv
    obtain ⟨-, -, hwf, -⟩ := hfw
    have hvE : v ∈ E := (ErdosFaberLovaszConjecture.mem_verts E v).mp hv
    have hwE : w ∈ E := (ErdosFaberLovaszConjecture.mem_verts E w).mp hw
    exact hne (Subtype.ext (IsLinear.eq_of_mem_pair hlin f.2 e.2 hvw hvf hwf hvE hwE))
  -- the edge `e` has `C` vertices
  have hcardE : (ErdosFaberLovaszConjecture.verts E).card = C := hsize e
  calc Nat.card {f : 𝓗 // f ≠ e ∧ ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty ∧ γ ∈ L f}
      = S.card := hLHS
    _ = ((ErdosFaberLovaszConjecture.verts E).biUnion Cv).card := by rw [hSuni]
    _ = ∑ v ∈ ErdosFaberLovaszConjecture.verts E, (Cv v).card :=
        Finset.card_biUnion (h := fun a ha b hb hab => hdisj a ha b hb hab)
    _ = ∑ v ∈ ErdosFaberLovaszConjecture.verts E, (D - 1) :=
        Finset.sum_congr rfl (fun v hv => hCvcard v hv)
    _ = (ErdosFaberLovaszConjecture.verts E).card * (D - 1) := by
        rw [Finset.sum_const, Nat.nsmul_eq_mul]
    _ = C * (D - 1) := by rw [hcardE]

end Work.Deep.Kahn
