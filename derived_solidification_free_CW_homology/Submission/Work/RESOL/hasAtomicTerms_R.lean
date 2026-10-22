/-
AREA RESOL — the terms of the total complex of the resolution bicomplex are atomic sums.

The total complex `R.obj B` of the resolution bicomplex `B ↦ Tot(columns X.obj (B.X p))` has
`n`-th term the coproduct, over the fibre `{(p,q) : p - q = n}` of the total complex shape, of
the terms `(X.obj (B.X p)).X q` of the resolutions.  Each of those is a small atomic sum
(`isAtomicSum_X`), and a small coproduct of small atomic sums is again a small atomic sum
(`isAtomicSum_sigma`, proved here by hand: the colimit cocone of the big family is obtained from
the colimit cocones of the individual atomic presentations, and a colimit cocone of the points).

Everything here has to be small (`Type 0`-indexed) because `LightCondAb` lives in `Type 1` and
coproducts in it are only small; this is why `IsAtomicSum` indexes by a `Type 0`.
-/
import Mathlib
import Submission.Work.RESOL.Bicomplex
import Submission.Work.RESOL.isAtomicSum_X

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid
open HomologicalComplex

noncomputable section

namespace Work.RESOL

attribute [local instance 2000] Sheaf.instHasColimitsOfShape

/-- A small coproduct of small atomic sums is a small atomic sum.

If `M j = ∐_{i : Jj j} ℤ[S j i]` for every `j : J`, then `∐_j M j` is the coproduct of the atoms
`ℤ[S a.1 a.2]` indexed by the sigma type `Σ j, Jj j` (`Type 0`, since both `J` and the `Jj j`
are), and that coproduct cocone is a colimit: it is the composite of the colimit cocones of the
individual presentations.  The point of the big cocone is `∐_j (cj j).pt`, i.e. the coproduct of
the points of the chosen presentations; the isomorphism with `∐_j M j` is `Sigma.whiskerEquiv`. -/
theorem isAtomicSum_sigma {J : Type} (M : J → LightCondAb) [HasCoproduct M]
    (h : ∀ j, IsAtomicSum (M j)) : IsAtomicSum (∐ M) := by
  classical
  simp only [IsAtomicSum] at h
  choose Jj Sj cj hcj0 ej0 using h
  have hcj : ∀ j, IsColimit (cj j) := fun j => Classical.choice (hcj0 j)
  have ej : ∀ j, M j ≅ (cj j).pt := fun j => Classical.choice (ej0 j)
  -- the big index (of all the atoms of all the presentations) and the big family of atoms
  let Sbig : (Σ j, Jj j) → LightProfinite := fun a => Sj a.1 a.2
  let F : (Σ j, Jj j) → LightCondAb := fun a => (free ℤ).obj (Sbig a).toCondensed
  -- the big cocone: the point is the coproduct of the points of the presentations
  let c : Cofan F := Cofan.mk (∐ fun j => (cj j).pt)
    (fun a => (cj a.1).inj a.2 ≫ Sigma.ι (fun j => (cj j).pt) a.1)
  have hc : IsColimit c :=
    Cofan.IsColimit.mk c
      -- the map out of the big coproduct: the `j`-th component is induced by the colimit
      -- cocone `cj j` applied to the `j`-th block of the test cocone `s`
      (fun s => Sigma.desc fun j => Cofan.IsColimit.desc (hcj j) fun i => s.inj ⟨j, i⟩)
      (fun s a => by
        cases a with
        | mk j i =>
          rw [show c.inj ⟨j, i⟩ = (cj j).inj i ≫ Sigma.ι (fun j => (cj j).pt) j from rfl]
          rw [Category.assoc, Sigma.ι_comp_desc]
          exact Cofan.IsColimit.fac (hcj j) (fun i => s.inj ⟨j, i⟩) i)
      (fun s m hm => by
        -- uniqueness: compare the `j`-th components using the colimit cocone `cj j`
        apply Sigma.hom_ext (f := fun j => (cj j).pt)
        intro j
        rw [Sigma.ι_comp_desc]
        refine IsColimit.uniq (hcj j) (Cofan.mk s.pt fun i => s.inj ⟨j, i⟩)
          (Sigma.ι (fun j => (cj j).pt) j ≫ m) ?_
        intro i
        cases i with
        | mk i' =>
          change (cj j).inj i' ≫ (Sigma.ι (fun j => (cj j).pt) j ≫ m) = s.inj ⟨j, i'⟩
          rw [← Category.assoc]
          exact hm ⟨j, i'⟩)
  refine isAtomicSum_of_iso (Sigma.whiskerEquiv (f := fun j => (cj j).pt) (g := M) (Equiv.refl J) ej) ?_
  exact ⟨Σ j, Jj j, Sbig, c, ⟨hc⟩, ⟨Iso.refl _⟩⟩

/-- Every term of the total complex `R.obj B` of the resolution bicomplex is a small atomic sum:
it is the coproduct over the fibre `{(p,q) : p - q = n}` of the terms `(X.obj (B.X p)).X q` of
resolutions, each of which is an atomic sum. -/
theorem hasAtomicTerms_R (B : Work.RESOL.Cpx) :
    Work.RESOL.HasAtomicTerms (Work.RESOL.R.obj B) := by
  intro n
  -- the `n`-th term of `Tot` is the coproduct of the bicomplex terms over the fibre of `π`
  show IsAtomicSum (GradedObject.mapObj (bicomplexObj B).toGradedObject
    (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.down ℕ) (ComplexShape.up ℤ)) n)
  refine isAtomicSum_sigma
    (fun i : (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.down ℕ) (ComplexShape.up ℤ)) ⁻¹' {n} =>
      (bicomplexObj B).toGradedObject i.1) ?_
  -- each summand is a term of the resolution `X.obj (B.X p)` of the `p`-th term of `B`
  intro i
  exact isAtomicSum_X (B.X i.1.1) i.1.2

end Work.RESOL
