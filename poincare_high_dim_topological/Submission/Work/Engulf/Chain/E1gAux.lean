import Mathlib
import Submission.Work.Engulf.Basic
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Auxi.SimplexCover
import Submission.Work.Engulf.Auxi.EngulfAux

/-!
# `E1_group`: elementary helpers

Small point-set / combinatorial helpers used by `Submission/Work/Engulf/Chain/E1_group.lean`
(one chart group of the repaired Newman Lemma 5, `Submission/Work/NOTES_LEAD_poincare_E1fix.md`
§1).  Nothing here uses the forms of `Tools`; the statements are the standard
subcomplex/smoothing-chart API in the vocabulary of `Work.Engulf`.
-/

open Set Metric PL

namespace Work.Engulf.Chain

universe u

variable {n N : ℕ} {M : Type*} [MetricSpace M] {Γ Γ' : Cx N}

/-! ## `IsSubSp` for the simplex on a face, and monotonicity in the complex -/

theorem isSubSp_simp_of_mem {s : Finset (E N)} (hs : s ∈ Γ.faces) :
    Work.Engulf.IsSubSp Γ (simp s) :=
  ⟨fun _ hx => Geometry.SimplicialComplex.convexHull_subset_space hs hx,
    fun _ hx => ⟨s, hs, hx, Subset.rfl⟩⟩

theorem isSubSp_mono {S : Set (E N)} (h : Γ.faces ⊆ Γ'.faces) (hS : Work.Engulf.IsSubSp Γ S) :
    Work.Engulf.IsSubSp Γ' S := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · exact Geometry.SimplicialComplex.mem_space_iff.2
      (let ⟨t, ht, hxt⟩ := Geometry.SimplicialComplex.mem_space_iff.1 (hS.1 hx)
       ⟨t, h ht, hxt⟩)
  · obtain ⟨t, ht, hxt, hsub⟩ := hS.2 x hx
    exact ⟨t, h ht, hxt, hsub⟩

/-! ## Splitting a simplex along a union of subcomplexes -/

/-- A face of a complex whose simplex lies in the union of two subcomplex sets lies in one of
them.  (`Work.Engulf.Aux.face_subset_of_subset_union` is the same statement; this version is
proved from the barycentre so that `E1_group` does not depend on that module.) -/
theorem simp_subset_or {A B : Set (E N)} (hA : Work.Engulf.IsSubSp Γ A)
    (hB : Work.Engulf.IsSubSp Γ B) {s : Finset (E N)} (hs : s ∈ Γ.faces)
    (h : simp s ⊆ A ∪ B) : simp s ⊆ A ∨ simp s ⊆ B := by
  by_cases hAs : simp s ⊆ A
  · exact Or.inl hAs
  · refine Or.inr ?_
    have hsne : s.Nonempty := Γ.nonempty_of_mem_faces hs
    have hb : Work.Engulf.bary s ∈ A ∪ B := h (Work.Engulf.bary_mem_simp hsne)
    rcases hb with hbA | hbB
    · exact absurd (by
        obtain ⟨t, ht, hbt, htA⟩ := hA.2 _ hbA
        exact (Work.Engulf.simp_mono (Work.Engulf.bary_mem_simp_subset hs ht hbt)).trans htA) hAs
    · obtain ⟨t, ht, hbt, htB⟩ := hB.2 _ hbB
      exact (Work.Engulf.simp_mono (Work.Engulf.bary_mem_simp_subset hs ht hbt)).trans htB

/-- Three-way version. -/
theorem simp_subset_or3 {A B C : Set (E N)} (hA : Work.Engulf.IsSubSp Γ A)
    (hB : Work.Engulf.IsSubSp Γ B) (hC : Work.Engulf.IsSubSp Γ C) {s : Finset (E N)}
    (hs : s ∈ Γ.faces) (h : simp s ⊆ A ∪ B ∪ C) :
    simp s ⊆ A ∨ simp s ⊆ B ∨ simp s ⊆ C := by
  rcases simp_subset_or hA (Work.Engulf.isSubSp_union hB hC) hs (by simpa [Set.union_assoc] using h)
    with h1 | h1
  · exact Or.inl h1
  · rcases simp_subset_or hB hC hs h1 with h2 | h2
    exacts [Or.inr (Or.inl h2), Or.inr (Or.inr h2)]

/-! ## `SmoothChart` and `Tame` are monotone in the complex and in the frozen function -/

theorem smoothChart_mono {p : ℕ} {X X' : Set M} {L : Set (E N)} {f f' : E N → M}
    {ψ : CubeChart n M} (hX : X' ⊆ X) (hsub : Γ.faces ⊆ Γ'.faces)
    (hnew : ∀ s ∈ Γ'.faces, simp s ⊆ L → s ∈ Γ.faces) (hf : Set.EqOn f' f L)
    (h : Work.Engulf.SmoothChart p X Γ L f ψ) :
    Work.Engulf.SmoothChart p X' Γ' L f' ψ := by
  obtain ⟨hDom, hLoc⟩ := h
  refine ⟨?_, ?_⟩
  · obtain ⟨P, hP, hPX⟩ := hDom
    exact ⟨P, hP, fun y hy hyX => hPX y hy (hX hyX)⟩
  · intro s hs hsL y hy hyc
    have hsΓ : s ∈ Γ.faces := hnew s hs hsL
    have hyL : y ∈ L := hsL hy
    rw [hf hyL] at hyc
    obtain ⟨δ, hδ, hlin⟩ := hLoc s hsΓ hsL y hy hyc
    obtain ⟨A, hA⟩ := hlin
    exact ⟨δ, hδ, A, fun z hz => ⟨(hA z hz).1, by rw [hf (hsL hz.1), (hA z hz).2]⟩⟩

theorem tame_mono {p : ℕ} {X X' : Set M} {L : Set (E N)} {f f' : E N → M}
    (hX : X' ⊆ X) (hsub : Γ.faces ⊆ Γ'.faces)
    (hnew : ∀ s ∈ Γ'.faces, simp s ⊆ L → s ∈ Γ.faces) (hf : Set.EqOn f' f L)
    (h : Work.Engulf.Tame n p X Γ L f) : Work.Engulf.Tame n p X' Γ' L f' := by
  intro x
  obtain ⟨ψ, hx, hs⟩ := h x
  exact ⟨ψ, hx, smoothChart_mono hX hsub hnew hf hs⟩

/-! ## The state of the inner loop over the pieces of one chart group -/

/-- State of the inner loop over the pieces of one chart group of `E1_group`: after the first `r`
pieces have been frozen as far faces.

* `Γk`, `F` are the *outer* invariant data (`E1GInv` at `k`), `ψ` the chart of this group,
  `X₁` the enlarged kept closed set, `g₀` the function at the start of the group,
  `pieces` the list of `ψ`-dominated pieces, `η` the budget of one piece;
* `Γr`, `G`, `g`, `h` are the current complex, the union of the far preimages of the frozen
  pieces, the current function and the accumulated compactly supported homeomorphism. -/
structure E1GSt (n p : ℕ) {M : Type*} [MetricSpace M] {N : ℕ}
    (V X : Set M) (Γk : Cx N) (H L F : Set (E N)) (ψ : CubeChart n M)
    (X₁ : Set M) (g₀ : E N → M) (pieces : List (Finset (E n))) (η : ℝ)
    (r : ℕ) (Γr : Cx N) (G : Set (E N)) (g : E N → M) (h : M ≃ₜ M) : Prop where
  le    : r ≤ pieces.length
  sub   : Γk.faces ⊆ Γr.faces
  fin   : Γr.faces.Finite
  dim   : DimLE Γr (p + 1)
  newG  : ∀ s ∈ Γr.faces, s ∈ Γk.faces ∨ simp s ⊆ G
  subG  : IsSubSp Γr G
  disjG : Disjoint G Γk.space
  dimG  : ∀ s ∈ Γr.faces, simp s ⊆ G → s.card ≤ p + 1
  cont  : ContinuousOn g Γr.space
  frz   : EqOn g g₀ (L ∪ F)
  gaff  : ∀ j (_hj : j < r) (hj' : j < pieces.length),
            ψ.toFun '' simp pieces[j] ⊆ g '' G
  near  : ∀ x ∈ Γk.space, dist (g x) (g₀ x) ≤ r * η
  tame  : Tame n p X Γr (L ∪ F ∪ G) g
  chart : SmoothChart p X Γr (L ∪ G) g ψ
  eng   : X₁ ∪ g '' (H ∪ F ∪ G) ⊆ h '' V
  supp  : CSupp h univ

/-! ## The space of a smaller complex, and injectivity of a cube chart -/

theorem space_mono {Γ Γ' : Cx N} (h : Γ.faces ⊆ Γ'.faces) : Γ.space ⊆ Γ'.space := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.1 hx
  exact Geometry.SimplicialComplex.mem_space_iff.2 ⟨s, h hs, hxs⟩

section Chart

variable {M₀ : Type*} [TopologicalSpace M₀]

/-- A cube chart is injective on the open unit cube. -/
theorem cubeChart_inj (ψ : PL.CubeChart n M₀) {x y : PL.E n} (hx : x ∈ PL.openCube 1)
    (hy : y ∈ PL.openCube 1) (h : ψ.toFun x = ψ.toFun y) : x = y := by
  have h' : (PL.openCube (n := n) 1).domRestrict ψ.toFun ⟨x, hx⟩
      = (PL.openCube (n := n) 1).domRestrict ψ.toFun ⟨y, hy⟩ := h
  exact congrArg Subtype.val (ψ.emb.toIsEmbedding.injective h')

end Chart

/-- `Tame` is antitone in the set `X` whose domination is required. -/
theorem tame_mono_X {p : ℕ} {X X₁ : Set M} {L : Set (E N)} {f : E N → M} (h : X₁ ⊆ X)
    (ht : Work.Engulf.Tame n p X Γ L f) : Work.Engulf.Tame n p X₁ Γ L f := by
  intro x
  obtain ⟨ψ, hx, hD, hloc⟩ := ht x
  refine ⟨ψ, hx, ?_, hloc⟩
  obtain ⟨P, hP, hPX⟩ := hD
  exact ⟨P, hP, fun y hy hyX => hPX y hy (h hyX)⟩

end Work.Engulf.Chain
