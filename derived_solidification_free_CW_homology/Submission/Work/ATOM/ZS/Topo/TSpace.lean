import Mathlib
import Submission.Work.ATOM.ZS.Topo.Defs
import Submission.Work.ATOM.ZS.Topo.tSet_isClosed
import Submission.Work.ATOM.ZS.Topo.tSet_fst_surjective
import Submission.Work.ATOM.ZS.Topo.betaFun_continuous

/-!
# AREA ATOM: the light profinite set `T'` and its projections

`T' = {(j,a_j) : j ∈ ℕ} ∪ {∞} × S` is a closed subset of `(ℕ∪{∞}) × S`
(`Work.ATOM.tSet`, `Work.ATOM.tSet_isClosed`), hence a light profinite set (`Work.ATOM.T'`).
The first projection `tProj : T' ⟶ ℕ∪{∞}` is surjective; this is the cover along which the null
sequence `g : P ⟶ ℤ[S]` is glued (`Work.ATOM.zdesc`).

The key point of the construction is that over a *finite* index `j` the fibre of `tProj` is the
single point `(j,a_j)`, so the naive section `(j,u) ↦ [u] - [e_{n(j)-1}u]` (which is continuous on
all of `(ℕ∪{∞}) × S` but does not descend from there) descends from `T'`: on the fibre over `∞`
it vanishes, and on the fibres over finite `j` there is nothing to check.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open OnePoint

noncomputable section

namespace Work.ATOM

variable (S : LightProfinite.{0}) [Infinite S]

/-- `T' = {(j,a_j)} ∪ {∞} × S` is closed in `(ℕ∪{∞}) × S`, hence compact. -/
instance instCompactSpaceTSet : CompactSpace ↥(tSet S) :=
  isCompact_iff_compactSpace.mp (ZS.Topo.tSet_isClosed S).isCompact

/-- The light profinite set `T' = {(j,a_j) : j ∈ ℕ} ∪ {∞} × S`. -/
def T' : LightProfinite.{0} := LightProfinite.of ↥(tSet S)

/-- The first projection `T' ⟶ ℕ∪{∞}`. -/
def tProj : T' S ⟶ LightProfinite.NatUnionInfty :=
  ConcreteCategory.ofHom
    ⟨fun p => p.1.1, continuous_fst.comp continuous_subtype_val⟩

/-- The second projection `T' ⟶ S`. -/
def pr₂T : T' S ⟶ S :=
  ConcreteCategory.ofHom ⟨fun p => p.1.2, continuous_snd.comp continuous_subtype_val⟩

/-- `β : T' ⟶ S`, the restriction of `Work.ATOM.betaFun`. -/
def betaT : T' S ⟶ S :=
  ConcreteCategory.ofHom ⟨fun p => betaFun S p.1, (ZS.Topo.betaFun_continuous S).comp continuous_subtype_val⟩

@[simp] lemma tProj_apply (p : ↥(T' S)) : tProj S p = p.1.1 := rfl

@[simp] lemma pr₂T_apply (p : ↥(T' S)) : pr₂T S p = p.1.2 := rfl

@[simp] lemma betaT_apply (p : ↥(T' S)) : betaT S p = betaFun S p.1 := rfl

/-- `tProj : T' ⟶ ℕ∪{∞}` is surjective. -/
theorem tProj_surjective : Function.Surjective (tProj S) := ZS.Topo.tSet_fst_surjective S

/-- Over the point at infinity, `β` is the second projection. -/
lemma betaT_eq_pr₂T_of_infty (p : ↥(T' S)) (hp : p.1.1 = (∞ : ℕ∪{∞})) :
    betaT S p = pr₂T S p := by
  rw [betaT_apply, pr₂T_apply]
  simp only [betaFun]
  rw [hp]
  rfl

/-- If two points of `T'` have the same finite first coordinate, they are equal. -/
lemma T'_eq_of_tProj_eq (p q : ↥(T' S)) (h : tProj S p = tProj S q) (j : ℕ)
    (hj : p.1.1 = ((j : ℕ) : ℕ∪{∞})) : p = q := by
  have hj' : tProj S p = ((j : ℕ) : ℕ∪{∞}) := (tProj_apply S p).trans hj
  have hq : q.1.1 = ((j : ℕ) : ℕ∪{∞}) :=
    (tProj_apply S q).symm.trans (h.symm.trans hj')
  have h1 : p.1 = q.1 := by
    refine Prod.ext ?_ ?_
    · exact hj.trans hq.symm
    · rw [tSet_second_eq (S := S) p.2 hj, tSet_second_eq (S := S) q.2 hq]
  exact Subtype.ext h1

end Work.ATOM
