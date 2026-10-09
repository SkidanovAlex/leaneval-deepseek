/-
Copyright (c) 2025. All rights reserved.

# The embedding-problem dictionary, in the absolute-Galois vocabulary

This file records the `H¹`/`H²` dictionary for embedding problems with **abelian kernel** over a
field `k`, in the vocabulary of this chapter (`H¹`, `H²` of `G_k = Field.absoluteGaloisGroup k`
with coefficients in a discrete `G_k`-module), so that the arithmetic statements of this chapter
(Grünwald in degree `2`, the Kummer isomorphism) can be plugged into the embedding-problem
machinery of `Submission.Work.Properness`.

## The dictionary

Let `1 → A → E →^{π} Q → 1` be a surjection of groups with abelian kernel `A`, and let
`ρ : G_k ↠ Q` be a (continuous, surjective) homomorphism.  A *solution* of the embedding problem
is a homomorphism `ψ : G_k →* E` with `π ∘ ψ = ρ` (`Work.Properness.Setup.IsLift`); it is
*proper* if it is surjective, i.e. if `ψ(G_K) = A` for `G_K = ker ρ`
(`Work.Properness.isProper_iff_map_HK_eq_A`).

* **`H¹`-dictionary.**  The set of solutions is a torsor under `Z¹(G_k, A)`: the action is
  `(x, ψ) ↦ x · ψ` pointwise (`Work.Properness.Setup.mulFun`), and two solutions are conjugate
  under `A` if and only if their difference classes in `H¹(G_k, A)` agree
  (`Work.Properness.liftClass_eq_iff_exists_conj`).  This is what makes "the obstruction of the
  next level" a class in `H¹(G_k, A)`.
* **`H²`-dictionary.**  Choosing a set-theoretic section of `π` produces a `2`-cocycle
  (`Work.AbsoluteGalois.sectionCocycle`) whose class in `H²(G_k, A)` is independent of the
  section: the **obstruction** of the embedding problem.  The problem has a solution if and only
  if this class vanishes — algebraically
  `Work.AbsoluteGalois.exists_lift_iff_pullbackCocycle_mem_B2` (equivalently
  `Work.Properness.hasLift_iff_pullbackCocycle_mem_B2`) — and *continuous* cohomology is the
  right home for it: a locally constant section gives a locally constant cocycle, and a locally
  constant solution exists exactly when the class in the continuous `H²` of this chapter vanishes.
* **Split problems.**  If `π` has a splitting section `σ` then `σ ∘ ρ` is a plain solution for
  free (`exists_lift_of_comp_eq`), and it is *not* proper unless the kernel is trivial
  (`not_isProper_of_splitting_section`): properness is the extra condition, and it is exactly what
  needs the arithmetic input (Grünwald–Wang), isolated as
  `Work.Properness.Setup.ScholzGrunwaldWangInput` and used in
  `Work.Properness.hasProperLift_of_scholzGrunwaldWang` (Proposition 11 of Schmidt–Wingberg).

The `H¹`/`H²` groups used below are `Work.AbsoluteKummer.H1`, `Work.AbsoluteKummer.H2`
(`Submission/Work/AbsoluteKummer/Defs.lean`), the continuous cohomology of a topological group
with coefficients a discrete module; for `G = G_k` these are the groups in which the obstruction
and the Grunwald conditions of the paper live.
-/
import Submission.Work.AbsoluteKummer.Defs
import Submission.Work.AbsoluteKummer.Basic
import Submission.Work.AbsoluteKummer.Coefficients
import Submission.Work.Properness.All
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v w x

namespace Work.AbsoluteKummer

noncomputable section

/-- **Split embedding problems always have a plain solution.**  If `π` has a splitting section
`σ` then `σ ∘ ρ` is a solution. -/
theorem exists_lift_of_comp_eq {S : Work.Properness.Setup.{u, v, w}} (σ : S.Q →* S.E)
    (hσ : S.π.comp σ = MonoidHom.id S.Q) :
    ∃ ψ : S.Lift, (ψ : S.H → S.E) = σ.comp S.ρ := by
  refine ⟨⟨σ.comp S.ρ, ?_⟩, rfl⟩
  ext h
  exact DFunLike.congr_fun hσ (S.ρ h)

/-- **That solution is not proper (unless the kernel is trivial).**  A splitting section misses
every non-trivial element of the kernel, so `σ ∘ ρ` is not surjective: for a *split* embedding
problem the plain solution is free, while properness is the extra, arithmetic condition. -/
theorem not_isProper_of_splitting_section {S : Work.Properness.Setup.{u, v, w}}
    (σ : S.Q →* S.E) (hσ : S.π.comp σ = MonoidHom.id S.Q) (hA : S.A ≠ ⊥) :
    ∃ ψ : S.Lift, ¬ S.IsProper ψ := by
  refine ⟨⟨σ.comp S.ρ, ?_⟩, ?_⟩
  · ext h
    exact DFunLike.congr_fun hσ (S.ρ h)
  · intro hsurj
    have hsurj' : Function.Surjective (fun h : S.H => σ (S.ρ h)) := hsurj
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA
    obtain ⟨h, hh⟩ := hsurj' (a : S.E)
    dsimp only at hh
    have hρh : S.ρ h = 1 := by
      have h1 : S.π (σ (S.ρ h)) = S.ρ h := DFunLike.congr_fun hσ (S.ρ h)
      rw [hh, a.2] at h1
      exact h1.symm
    have : a = 1 := by
      apply Subtype.ext
      show (a : S.E) = 1
      rw [← hh, hρh, map_one]
    exact ha this

/-- **Proposition 11 of Schmidt–Wingberg, on the named arithmetic input.**  Given the
Grunwald–Wang datum on subgroups `T i ≤ H_K` whose images generate the abelian kernel `A`, the
embedding problem has a proper solution.  The shared `H¹`/`H²` language of this chapter is what
lets a concrete Grunwald statement (e.g.
`Work.AbsoluteKummer.Grunwald.sqClassLocalize_surjective`) be fed into
`Work.Properness.Setup.ScholzGrunwaldWangInput`. -/
theorem hasProperLift_of_grunwaldWang {S : Work.Properness.Setup.{u, v, w}} {ι : Type x}
    [Fintype ι] (ψ₀ : S.Lift) (T : ι → Subgroup S.H) (hT : ∀ i, T i ≤ S.HK)
    (φ : ∀ i, T i →* S.A) (h : S.ScholzGrunwaldWangInput ψ₀ T hT φ)
    (hgen : (⨆ i, (φ i).range) = ⊤) : S.HasProperLift :=
  Work.Properness.hasProperLift_of_scholzGrunwaldWang ψ₀ T hT φ h hgen

end

end Work.AbsoluteKummer
