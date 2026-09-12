import Mathlib
import Submission.Commons.Geometry.Convex.Hadwiger.polytope_disjoint_intrinsicInterior_faces
import Submission.Commons.Geometry.Convex.Hadwiger.polytope_mem_intrinsicInterior_exposedFace
import Submission.Commons.Geometry.Convex.Hadwiger.exposed_face_strict_extension

open Set
open scoped BigOperators Convex

noncomputable section

namespace Commons.Geometry.Convex.Hadwiger

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [FiniteDimensional ℝ V]

/-- an affine subspace whose direction is the whole space and which is nonempty is the whole
space. -/
lemma affineSubspace_eq_top_of_direction_eq_top {s : AffineSubspace ℝ V}
    (hs : (s : Set V).Nonempty) (hdir : s.direction = ⊤) : s = ⊤ := by
  apply AffineSubspace.ext
  intro x
  constructor
  · intro hx
    exact AffineSubspace.mem_top ℝ V x
  · intro hx
    rcases hs with ⟨p, hp⟩
    rw [← AffineSubspace.vsub_right_mem_direction_iff_mem (s := s) hp x]
    rw [hdir]
    exact Submodule.mem_top

/-- a proper nonempty exposed face of a full-dimensional polytope has affine dimension
strictly less than that of the ambient space. -/
lemma proper_face_finrank_lt {u : Finset V} {P : Set V} (hP : P = convexHull ℝ (u : Set V))
    (hint : (interior P).Nonempty) {H : Set V}
    (hHexp : IsExposed ℝ P H) (hHne : H.Nonempty) (hHpr : H ≠ P) :
    Module.finrank ℝ (affineSpan ℝ H).direction < Module.finrank ℝ V := by
  classical
  by_contra hnot
  have hPcvx : Convex ℝ P := by
    rw [hP]
    exact convex_convexHull ℝ (u : Set V)
  have hHcvx : Convex ℝ H := hHexp.convex hPcvx
  have hdimle : Module.finrank ℝ (affineSpan ℝ H).direction ≤ Module.finrank ℝ V := by
    exact Submodule.finrank_le ((affineSpan ℝ H).direction)
  have hdimEq : Module.finrank ℝ (affineSpan ℝ H).direction = Module.finrank ℝ V := by
    omega
  have hdirTop : (affineSpan ℝ H).direction = ⊤ := by
    by_contra hne
    have hlt : (affineSpan ℝ H).direction < ⊤ := lt_of_le_of_ne le_top hne
    have hfinrank_lt :
        Module.finrank ℝ (affineSpan ℝ H).direction < Module.finrank ℝ (⊤ : Submodule ℝ V) := by
      exact Submodule.finrank_lt_finrank_of_lt hlt
    have hfinrank_top : Module.finrank ℝ (⊤ : Submodule ℝ V) = Module.finrank ℝ V := by
      exact finrank_top ℝ V
    omega
  have hHnonempty_set : ((affineSpan ℝ H : AffineSubspace ℝ V) : Set V).Nonempty := by
    rcases hHne with ⟨x, hx⟩
    exact ⟨x, subset_affineSpan ℝ H hx⟩
  have hspanTop : affineSpan ℝ H = ⊤ := affineSubspace_eq_top_of_direction_eq_top hHnonempty_set hdirTop
  have hintH : (interior H).Nonempty := by
    exact (Convex.interior_nonempty_iff_affineSpan_eq_top hHcvx).mpr hspanTop
  rcases hintH with ⟨x, hxint⟩
  have hHP : H ⊆ P := hHexp.subset
  have hxintP : x ∈ interior P := by
    exact interior_mono hHP hxint
  have hxIIP : x ∈ intrinsicInterior ℝ P := interior_subset_intrinsicInterior hxintP
  have hPsubH : P ⊆ H := by
    exact subset_of_mem_intrinsicInterior_of_isExtreme (C := P) (F := H) (G := P)
      (Set.Subset.refl P) hHexp.isExtreme (interior_subset hxint) hxIIP
  have hHP' : H ⊆ P := hHexp.subset
  have hEq : H = P := Set.Subset.antisymm hHP' hPsubH
  exact hHpr hEq

theorem facet_containing_proper_face {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] [FiniteDimensional ℝ V]
    (u : Finset V) (P : Set V) (hP : P = convexHull ℝ (u : Set V))
    (hint : (interior P).Nonempty) {F : Set V}
    (hFexp : IsExposed ℝ P F) (hFne : F.Nonempty) (hFproper : F ≠ P) :
    ∃ G : Set V, G.Nonempty ∧ IsExposed ℝ P G ∧ G ≠ P ∧
      Module.finrank ℝ (affineSpan ℝ (G : Set V)).direction = Module.finrank ℝ V - 1 ∧
      F ⊆ G := by
  classical
  let d : ℕ := Module.finrank ℝ V
  /- a nonempty exposed face of the polytope is the convex hull of the generators it contains -/
  have hface_conv : ∀ H : Set V, H.Nonempty → IsExposed ℝ P H →
      H = convexHull ℝ ((u.filter (fun x : V => x ∈ H) : Finset V) : Set V) := by
    intro H hHne hHexp
    have hset : ((u.filter (fun x : V => x ∈ H) : Finset V) : Set V) = H ∩ (u : Set V) := by
      ext x
      simp
      exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
    rw [hset]
    exact exposedFace_conv_vertices_generic u P hP hHexp hHne
  /- a strictly larger face contains strictly more generators -/
  have hcard_strict : ∀ {H H' : Set V}, H.Nonempty → IsExposed ℝ P H → H'.Nonempty →
      IsExposed ℝ P H' → H ⊂ H' →
      (u.filter (fun x : V => x ∈ H)).card < (u.filter (fun x : V => x ∈ H')).card := by
    intro H H' hHne hHexp hH'ne hH'exp hHH'
    rcases (Set.ssubset_iff_subset_ne.mp hHH') with ⟨hHsubH', hHneH'⟩
    have hsub' : u.filter (fun x : V => x ∈ H) ⊆ u.filter (fun x : V => x ∈ H') := by
      intro x hx
      rcases Finset.mem_filter.mp hx with ⟨hxu, hxH⟩
      exact Finset.mem_filter.mpr ⟨hxu, hHsubH' hxH⟩
    have hne' : u.filter (fun x : V => x ∈ H) ≠ u.filter (fun x : V => x ∈ H') := by
      intro heq
      apply hHneH'
      calc
        H = convexHull ℝ ((u.filter (fun x : V => x ∈ H) : Finset V) : Set V) :=
          hface_conv H hHne hHexp
        _ = convexHull ℝ ((u.filter (fun x : V => x ∈ H') : Finset V) : Set V) := by rw [heq]
        _ = H' := (hface_conv H' hH'ne hH'exp).symm
    exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub', hne'⟩)
  /- main recursion: either the current face is already (d - 1)-dimensional, or we strictly
     extend it, which strictly increases the number of generators in it. -/
  have hrec : ∀ N : ℕ, ∀ H : Set V, H.Nonempty → IsExposed ℝ P H → H ≠ P → F ⊆ H →
      u.card - (u.filter (fun x : V => x ∈ H)).card = N →
      ∃ G : Set V, G.Nonempty ∧ IsExposed ℝ P G ∧ G ≠ P ∧
        Module.finrank ℝ (affineSpan ℝ (G : Set V)).direction = d - 1 ∧ F ⊆ G := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro H hHne hHexp hHpr hFH hmeas
      by_cases hdim : Module.finrank ℝ (affineSpan ℝ H).direction + 1 < d
      · rcases exposed_face_strict_extension u P hP hint hHexp hHne hHpr hdim with
          ⟨H', hH'ne, hH'exp, hH'pr, hHH'⟩
        have hHsubH' : H ⊆ H' := (Set.ssubset_iff_subset_ne.mp hHH').1
        have hFH' : F ⊆ H' := Set.Subset.trans hFH hHsubH'
        have hcardlt : (u.filter (fun x : V => x ∈ H)).card <
            (u.filter (fun x : V => x ∈ H')).card :=
          hcard_strict hHne hHexp hH'ne hH'exp hHH'
        have hcardle' : (u.filter (fun x : V => x ∈ H')).card ≤ u.card := by
          exact Finset.card_le_card (Finset.filter_subset (fun x : V => x ∈ H') u)
        have hlt1 : (u.filter (fun x : V => x ∈ H)).card < u.card :=
          lt_of_lt_of_le hcardlt hcardle'
        have hmeaslt : u.card - (u.filter (fun x : V => x ∈ H')).card < N := by
          simpa [hmeas] using Nat.sub_lt_sub_left hlt1 hcardlt
        exact ih (u.card - (u.filter (fun x : V => x ∈ H')).card) hmeaslt H' hH'ne hH'exp
          hH'pr hFH' rfl
      · -- no extension possible: the dimension is already d - 1
        have hdimlt : Module.finrank ℝ (affineSpan ℝ H).direction < d := by
          have hpr := proper_face_finrank_lt (u := u) (P := P) hP hint hHexp hHne hHpr
          simpa [d] using hpr
        have hdimeq : Module.finrank ℝ (affineSpan ℝ H).direction = d - 1 := by
          omega
        exact ⟨H, hHne, hHexp, hHpr, hdimeq, hFH⟩
  exact hrec (u.card - (u.filter (fun x : V => x ∈ F)).card) F hFne hFexp hFproper
    (Set.Subset.refl F) rfl

end Commons.Geometry.Convex.Hadwiger
