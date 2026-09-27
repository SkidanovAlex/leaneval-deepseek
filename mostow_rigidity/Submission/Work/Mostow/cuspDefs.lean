import Submission.Work.Mostow.QIDefs

/-!
# Vocabulary for the `cuspRecognition` development

This module re-exports the hyperboloid-model toolkit of `Submission.Work.Mostow.QIDefs`
(`mink`, `lev`, `wc`, `yc`, `flatD`, `horoPt`, `hptOf`, `nvec`, `nvec'`, `wvec`, `emat`,
`POBasic`, `HypIsoData`, the explicit geodesic `geo`, ...) which is what the cusp-recognition
argument is phrased in, together with the few extra definitions used below.
-/

namespace Work.Mostow

open LeanEval.Geometry.MostowRigidity Submission.Mostow MeasureTheory

noncomputable section

variable {n : ℕ}

/-- The standard boundary point of `Sph n` (`n ≥ 1`): the first basis vector of `E n`. -/
def stdPt (n : ℕ) : E n := WithLp.toLp 2 (fun i : Fin n => if (i : ℕ) = 0 then 1 else 0)

lemma stdPt_apply (n : ℕ) (i : Fin n) : stdPt n i = if (i : ℕ) = 0 then 1 else 0 := rfl

end

end Work.Mostow

namespace Work.Mostow

open LeanEval.Geometry.MostowRigidity Submission.Mostow MeasureTheory

noncomputable section

/-- The group-theoretic "rank-2 free abelian subgroup in the centraliser" property: some power of
`γ` has a centraliser containing two independent commuting elements.

For a lattice in `PO(n,1)` with `n ≥ 3` this holds exactly for the elements of infinite order whose
centraliser is not virtually cyclic — in particular for the parabolic elements, and for no
loxodromic one.  Being group-theoretic, it is invariant under abstract isomorphism. -/
def HasZ2 {G : Type*} [Group G] (γ : G) : Prop :=
  ∃ k : ℕ, 0 < k ∧ ∃ a b : G,
    a * γ ^ k = γ ^ k * a ∧ b * γ ^ k = γ ^ k * b ∧ a * b = b * a ∧
    (∀ i j : ℤ, a ^ i * b ^ j = 1 → i = 0 ∧ j = 0)

lemma HasZ2.map {G H : Type*} [Group G] [Group H] (e : G ≃* H) {γ : G} (h : HasZ2 γ) :
    HasZ2 (e γ) := by
  obtain ⟨k, hk, a, b, ha, hb, hab, hind⟩ := h
  refine ⟨k, hk, e a, e b, ?_, ?_, ?_, ?_⟩
  · simpa only [map_mul, map_pow] using congrArg e ha
  · simpa only [map_mul, map_pow] using congrArg e hb
  · simpa only [map_mul] using congrArg e hab
  · intro i j hij
    refine hind i j ?_
    have h3 := congrArg (⇑e.symm) hij
    simpa using h3

end

end Work.Mostow
