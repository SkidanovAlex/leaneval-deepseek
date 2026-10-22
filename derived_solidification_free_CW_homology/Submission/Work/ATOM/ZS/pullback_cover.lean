import Mathlib
import Submission.Work.ATOM.ZS.Topo.TSpace

/-!
# AREA ATOM / `ℤ[S]`: a two-piece cover of the double pullback of `tProj`

The map `gHat : ℤ[ℕ∪{∞}] ⟶ ℤ[S]` of `Work.ATOM.ZS.NullSeqMaps` is defined by descent along the
surjection `tProj : T' ⟶ ℕ∪{∞}` (`Work.ATOM.zdesc`).  To *check* that a candidate morphism has the
required descent property one has to compare values on the double "kernel pair"
`P = T' ×_{ℕ∪{∞}} T'` of `tProj`; the point of this file is the elementary geometric fact that

> `P` is covered by two pieces: the part lying over the point `∞` of `ℕ∪{∞}`, and the diagonal.

Both pieces are closed subsets of the compact Hausdorff space `P`, hence (light) profinite, and the
covering is by the two inclusions.  Concretely:

* `pSet` is the closed subset of `P` of pairs whose first component lies over `∞` — over `∞` the
  fibre of `tProj` is all of `S`, so this piece is `S × S`;
* `dSet` is the diagonal of `P` — over a *finite* index `j` the fibre of `tProj` is the single point
  `(j, a_j)` (`Work.ATOM.ZS.T'_eq_of_tProj_eq`), so a pair in `P` whose first component lies over a
  finite index is automatically diagonal.

The main statement `Work.ATOM.ZS.pullback_cover` is the resulting cover.
-/

open CategoryTheory Limits LightProfinite OnePoint

namespace Work.ATOM.ZS

noncomputable section

variable (S : LightProfinite.{0}) [Infinite S]

/-- The double "kernel pair" `P = T' ×_{ℕ∪{∞}} T'` of the projection `tProj : T' ⟶ ℕ∪{∞}`,
i.e. the explicit `CompHausLike` pullback of `tProj` with itself.  (As a set it is
`{(p, q) ∈ T' × T' | tProj p = tProj q}`.) -/
abbrev PB : LightProfinite.{0} :=
  CompHausLike.pullback (Work.ATOM.tProj S) (Work.ATOM.tProj S)

/-- The part of the kernel pair lying over the point `∞`: pairs whose first component has first
coordinate `∞`. -/
def pSet : Set ↥(PB S) := {q | q.1.1.1.1 = OnePoint.infty}

/-- The diagonal of the kernel pair. -/
def dSet : Set ↥(PB S) := {q | q.1.1 = q.1.2}

/-- `pSet` is closed: it is the preimage of the closed point `{∞} ⊆ ℕ∪{∞}` (which is a
one-point compactification, so `T1`) under the continuous map `q ↦ q.1.1.1.1`. -/
theorem isClosed_pSet : IsClosed (pSet S) :=
  isClosed_singleton.preimage
    ((by fun_prop : Continuous (fun q : ↥(PB S) => q.1.1)).subtype_val.fst)

/-- `dSet` is closed: it is the equaliser of the two continuous projections onto `T'`. -/
theorem isClosed_dSet : IsClosed (dSet S) :=
  isClosed_eq (by fun_prop : Continuous (fun q : ↥(PB S) => q.1.1))
    (by fun_prop : Continuous (fun q : ↥(PB S) => q.1.2))

instance : CompactSpace ↥(pSet S) := by
  rw [← isCompact_iff_compactSpace]; exact (isClosed_pSet S).isCompact

instance : CompactSpace ↥(dSet S) := by
  rw [← isCompact_iff_compactSpace]; exact (isClosed_dSet S).isCompact

/-- The part of the kernel pair over `∞`, as a light profinite set (it is `S × S`). -/
noncomputable def coverInf : LightProfinite.{0} := LightProfinite.of ↥(pSet S)

/-- The diagonal of the kernel pair, as a light profinite set (it is `T'`). -/
noncomputable def coverDiag : LightProfinite.{0} := LightProfinite.of ↥(dSet S)

/-- The inclusion of the `∞`-part into the kernel pair. -/
noncomputable def ιInf : coverInf S ⟶ PB S :=
  ConcreteCategory.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The inclusion of the diagonal into the kernel pair. -/
noncomputable def ιDiag : coverDiag S ⟶ PB S :=
  ConcreteCategory.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The two-piece cover, as a family indexed by `Fin 2`. -/
noncomputable def Cov : Fin 2 → LightProfinite.{0} :=
  fun i => Fin.cases (coverInf S) (fun _ => coverDiag S) i

/-- The two inclusions, as a family indexed by `Fin 2`. -/
noncomputable def iot : ∀ i, Cov S i ⟶ PB S :=
  fun i => Fin.cases (ιInf S) (fun _ => ιDiag S) i

end

/-- **The kernel pair of `tProj` is covered by the part over `∞` and the diagonal.**

There is a two-piece cover `C : Fin 2 → LightProfinite` of `P = T' ×_{ℕ∪{∞}} T'` by the closed
subset over `∞` (`i = 0`, consisting of pairs whose first component has first coordinate `∞`) and
the diagonal (`i = 1`); the first piece lands in the fibre over `∞`, the second in the diagonal,
and together they are surjective onto `P`. -/
theorem pullback_cover (S : LightProfinite.{0}) [Infinite S] :
    ∃ (C : Fin 2 → LightProfinite.{0})
      (ι : ∀ i, C i ⟶ CompHausLike.pullback (Work.ATOM.tProj S) (Work.ATOM.tProj S)),
      (∀ p : ↥(C 0), ((ι 0 p).1.1).1.1 = OnePoint.infty) ∧
      (CategoryTheory.CategoryStruct.comp (ι 1)
          (CompHausLike.pullback.fst (Work.ATOM.tProj S) (Work.ATOM.tProj S)) =
        CategoryTheory.CategoryStruct.comp (ι 1)
          (CompHausLike.pullback.snd (Work.ATOM.tProj S) (Work.ATOM.tProj S))) ∧
      (∀ q : ↥(CompHausLike.pullback (Work.ATOM.tProj S) (Work.ATOM.tProj S)),
        q ∈ Set.range (ι 0) ∨ q ∈ Set.range (ι 1)) := by
  refine ⟨Cov S, iot S, ?_, ?_, ?_⟩
  · -- every point of the `∞`-piece lies over `∞`
    intro p
    show ((ιInf S p).1.1).1.1 = OnePoint.infty
    exact p.2
  · -- the diagonal piece maps into the diagonal
    show ιDiag S ≫ CompHausLike.pullback.fst (Work.ATOM.tProj S) (Work.ATOM.tProj S) =
      ιDiag S ≫ CompHausLike.pullback.snd (Work.ATOM.tProj S) (Work.ATOM.tProj S)
    apply ConcreteCategory.hom_ext
    intro p
    show (p.1).1.1 = (p.1).1.2
    exact p.2
  · -- every point of the kernel pair is in one of the two pieces
    intro q
    by_cases h : q.1.1.1.1 = OnePoint.infty
    · exact Or.inl ⟨⟨q, h⟩, rfl⟩
    · -- the first component is over a finite index `j`, where the fibre of `tProj` is a point
      obtain ⟨j, hj⟩ := OnePoint.ne_infty_iff_exists.mp h
      exact Or.inr
        ⟨⟨q, Work.ATOM.T'_eq_of_tProj_eq S q.1.1 q.1.2 q.2 j hj.symm⟩, rfl⟩

end Work.ATOM.ZS
