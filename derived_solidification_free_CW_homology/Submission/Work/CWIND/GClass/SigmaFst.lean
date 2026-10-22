import Mathlib
import Submission.Work.CWIND.Basic

/-!
# CWIND/GClass — maps from connected spaces into a disjoint union

Basic topological input for the `sigma` field of the CW induction: a continuous map from a
connected space into a coproduct (disjoint union) of topological spaces lands in a single piece.
The application is `T = Δⁿ` (the standard simplex, which is path connected), where the pieces are
the subspaces of maps whose image lies in a single `X j`.
-/

noncomputable section

open CategoryTheory Limits LightCondensed LightProfinite
open LightCondensed.Solid Submission.Blueprint

namespace Work.CWIND.GClass

/-- **A map from a connected space into a disjoint union lands in one piece.**  If `T` is
connected and `f : T ⟶ ↧(Σ j, X j)` is continuous, then `(f t).1` is independent of `t`. -/
theorem sigmaFst_eq_of_connected {J : Type} {X : J → TopCat.{0}} {T : TopCat.{0}}
    [ConnectedSpace T] (f : T ⟶ TopCat.of (Σ j, (X j : Type))) :
    ∃ j : J, ∀ t, (f t).1 = j := by
  have huniv : IsPreconnected (Set.univ : Set T) := isPreconnected_univ
  let t₀ : T := Classical.arbitrary T
  let j : J := (f t₀).1
  let A : Set (Σ j, (X j : Type)) := {s | s.1 = j}
  let B : Set (Σ j, (X j : Type)) := {s | s.1 ≠ j}
  have hA : IsOpen A := by
    have h : A = Sigma.fst ⁻¹' ({j} : Set J) := rfl
    rw [h]; exact isOpen_sigma_fst_preimage _
  have hB : IsOpen B := by
    have h : B = Sigma.fst ⁻¹' ({j}ᶜ : Set J) := rfl
    rw [h]; exact isOpen_sigma_fst_preimage _
  have hdisj : Disjoint (f ⁻¹' A) (f ⁻¹' B) := by
    rw [Set.disjoint_left]; intro a ha hb; exact hb ha
  have hcov : (Set.univ : Set T) ⊆ f ⁻¹' A ∪ f ⁻¹' B := by
    intro t _; by_cases h : (f t).1 = j
    · exact Or.inl h
    · exact Or.inr h
  rcases IsPreconnected.subset_or_subset (hA.preimage f.hom.continuous)
    (hB.preimage f.hom.continuous) hdisj hcov huniv with h | h
  · exact ⟨j, fun t => h (Set.mem_univ t)⟩
  · exact absurd (h (Set.mem_univ t₀)) (by simp [B, j])

/-- The same statement phrased with an unbundled continuous map. -/
theorem sigmaFst_eq_of_connected' {J : Type} {X : J → TopCat.{0}} {T : TopCat.{0}}
    [ConnectedSpace T] (f : C(T, TopCat.of (Σ j, (X j : Type)))) :
    ∃ j : J, ∀ t, (f t).1 = j :=
  sigmaFst_eq_of_connected (TopCat.ofHom f)

/-- **The simplices of a disjoint union.**  Every continuous map from the standard simplex into a
disjoint union of spaces lands in a single piece. -/
theorem singSpace_sigmaFst_eq {J : Type} (X : J → TopCat.{0}) (n : ℕ)
    (f : C(Δ n, TopCat.of (Σ j, (X j : Type)))) : ∃ j : J, ∀ t, (f t).1 = j :=
  sigmaFst_eq_of_connected' f

/-- The integral singular chain complex functor, as an `ℕ`-graded chain complex of light condensed
abelian groups (i.e. `Work.CWIND.Csrc`, bundled as a functor). -/
abbrev CsrcF : TopCat.{0} ⥤ ChainComplex LightCondAb ℕ :=
  Submission.Blueprint.singC ⋙
    (LightCondensed.discrete (ModuleCat ℤ)).mapHomologicalComplex (ComplexShape.down ℕ)

lemma CsrcF_obj (X : TopCat.{0}) : CsrcF.obj X = Work.CWIND.Csrc X := rfl

/-- **The equality form of `singSpace_sigmaFst_eq`:** the piece index of a map `Δⁿ ⟶ ⊔_j X j` is
independent of the point of the simplex. -/
theorem singSpace_sigmaFst_eq_eq {J : Type} (X : J → TopCat.{0}) (n : ℕ)
    (f : C(Δ n, TopCat.of (Σ j, (X j : Type)))) (t t' : Δ n) :
    (f t).1 = (f t').1 := by
  obtain ⟨j, hj⟩ := singSpace_sigmaFst_eq X n f
  rw [hj t, hj t']

/-- The j-th piece of a disjoint union of spaces. -/
def piece {J : Type} {X : J → TopCat.{0}} (j : J) : Set (Σ j, (X j : Type)) := {s | s.1 = j}

lemma mem_piece {J : Type} {X : J → TopCat.{0}} (j : J) (s : Σ j, (X j : Type)) :
    s ∈ piece (X := X) j ↔ s.1 = j := Iff.rfl

/-- The underlying function of `TopCat.sigmaι X j` is `Sigma.mk j`. -/
lemma sigmaι_apply {J : Type} {X : J → TopCat.{0}} (j : J) (x : X j) :
    (TopCat.sigmaι X j) x = Sigma.mk j x := rfl

/-- Equality of a `Sigma.mk` with a transported second component. -/
lemma sigmaMk_cast {J : Type} {X : J → TopCat.{0}} (s : Σ j, (X j : Type)) (j : J)
    (h : s.1 = j) : Sigma.mk j (h ▸ s.2) = s := by
  obtain ⟨j', x⟩ := s
  cases h
  rfl

/-- **The j-th piece is homeomorphic to `X j`.** -/
noncomputable def pieceHomeo {J : Type} {X : J → TopCat.{0}} (j : J) :
    ↥(piece (X := X) j) ≃ₜ X j where
  toFun u := u.2 ▸ u.1.2
  invFun x := ⟨⟨j, x⟩, rfl⟩
  left_inv u := by
    obtain ⟨⟨j', x⟩, h⟩ := u
    cases h
    rfl
  right_inv x := rfl
  continuous_toFun := by
    have hσ : Topology.IsInducing (⇑(TopCat.sigmaι X j)) := by
      rw [funext (sigmaι_apply (X := X) j)]
      exact (Topology.IsOpenEmbedding.sigmaMk (i := j)).toIsEmbedding.toIsInducing
    refine hσ.continuous_iff.2 ?_
    have hfun : (⇑(TopCat.sigmaι X j) ∘ fun u : ↥(piece (X := X) j) => u.2 ▸ u.1.2) =
        Subtype.val := by
      funext u
      exact sigmaMk_cast u.1 j u.2
    rw [hfun]
    exact continuous_subtype_val
  continuous_invFun := Continuous.subtype_mk (p := fun s : Σ j, (X j : Type) => s.1 = j)
    continuous_sigmaMk (fun _ => rfl)

/-- **Corestriction to a piece.**  A continuous map `Δⁿ ⟶ ⊔_j X j` whose image lies in the
`j`-th piece is (the composite of the inclusion with) a continuous map into `X j`. -/
noncomputable def corestrict {J : Type} {X : J → TopCat.{0}} (n : ℕ)
    (f : C(Δ n, TopCat.of (Σ j, (X j : Type)))) (j : J) (h : ∀ t, (f t).1 = j) :
    C(Δ n, X j) where
  toFun t := (pieceHomeo (X := X) j) ⟨f t, h t⟩
  continuous_toFun := (pieceHomeo (X := X) j).continuous.comp
    (Continuous.subtype_mk f.continuous h)

lemma sigmaι_corestrict {J : Type} {X : J → TopCat.{0}} (n : ℕ)
    (f : C(Δ n, TopCat.of (Σ j, (X j : Type)))) (j : J) (h : ∀ t, (f t).1 = j) :
    (TopCat.sigmaι X j).hom.comp (corestrict n f j h) = f := by
  refine ContinuousMap.ext fun t => ?_
  exact sigmaMk_cast (f t) j (h t)

end Work.CWIND.GClass
