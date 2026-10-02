import Submission.Work.ThomBordism.gaussTubeData
import Submission.Work.Tubular.LocalDegree

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option linter.unusedVariables false

open CategoryTheory Limits
open scoped Topology

/-!
# The tautological Thom class is *unpinned*, and the `plainGaussSignUniformAcrossData`
  conclusion is `ℤ`-linear (hence sign-sensitive) in it

`Work.ThomBordism.Grassmann.tautologicalThomClass k m` is **a choice**:

  `Classical.choice (HasTautologicalThomClass k m)`,
  `HasTautologicalThomClass k m := Nonempty (ThomClass (tautologicalBundle k m) k)`
  (`Submission/Work/ThomBordism/Grassmann/Model.lean`),

and `Work.Thom.ThomClass` records **only** the class `τ` and the *sign-blind* field
`isThom : ∀ n, Bijective (thomMap … τ n)`: `-τ` is a Thom class with the same `isThom` proof.  So
the *only* facts Lean can prove about the chosen field `(tautologicalThomClass k m).τ` are the
"generic" ones, valid for every Thom class — in particular its *sign* is not recorded anywhere, and
(independently for each `(k, m)`, since the types `ThomClass (tautologicalBundle k m) k` are
incomparable) is not determined by the definition.

This matters for `Work.ThomBordism.plainGaussSignUniformAcrossData`, whose datum does **not** mention
the tautological class while its conclusion is `ℤ`-linear in it: the reduction
`gtdU E ND G hgm = Φ ((relCohMap G …) τ)` of `Submission/Work/ThomBordism/_gtd/P5.lean` is *linear*
in `τ`, and so is the relative cap product with the collapse class and the push-forward along
`NormalTotal.proj`.  The two lemmas below record this sensitivity, in the *exact* form of the
statement (the same `E, ND, G, hgm, C, g, R, hbox`, i.e. the same datum satisfying the same
hypotheses, with `τ` replaced by `-τ`):

* `Work.ThomBordism.ThomClass.neg` — the negated Thom class (`-τ`, same `isThom` proof shape);
* `Work.ThomBordism.gtdUWith` — `gtdU` with the tautological class replaced by an arbitrary one
  (`gtdU_eq_gtdUWith` is `rfl`);
* `Work.ThomBordism.gtdUWith_neg` — `gtdUWith (-U) = - gtdUWith U`;
* `Work.ThomBordism.proj_relCapPair_gtdUWith_neg` — the *whole* left-hand side of the target's
  conclusion is negated by replacing `U` with `-U`: no hypothesis of the target mentions `U`, so the
  target's conclusion is not determined by its hypotheses.

Consequence for the requested statement (`∃ εSign, εSign = ±1 ∧ ∀ V k …, … = εSign • V.c`):  it is
*not* a consequence of the recorded data, and additionally it asks for a *single* `εSign` over *all*
`k`, i.e. it asserts that the independent choices `tautologicalThomClass k 10` (for the various `k`)
are aligned.  The intended mathematical content (the degree of the Gauss map is a universal constant)
requires `tautologicalThomClass k 10` to be the *orientation-compatible* Thom class of the
tautological bundle, which must be pinned by a definition or by a hypothesis.
-/

namespace Work.ThomBordism

open Work.ThomBordism.PontryaginThom Work.Tubular

noncomputable section

/-- **A Thom class with the negated class.**  Since `ThomClass.isThom` is the only field recording
anything about `τ`, and `thomMap Z n (-τ) k = - thomMap Z n τ k`, the negation of a Thom class is a
Thom class with the *same* recorded properties. -/
protected noncomputable def ThomClass.neg {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type}
    {Z : Work.TangentClasses.RealBundle B F ι} {n : ℕ}
    (U : Work.Thom.ThomClass Z n) : Work.Thom.ThomClass Z n where
  τ := -U.τ
  isThom := fun k => by
    have hlin : Work.Thom.thomMap Z n (-U.τ) k = - Work.Thom.thomMap Z n U.τ k := by
      ext x
      rw [LinearMap.neg_apply]
      exact Work.Tubular.mixedCup_neg_right (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        k n ((Work.Thom.CohMap (Work.Thom.bundleProj Z) ℤ k).hom x) U.τ
    rw [hlin]
    obtain ⟨h1, h2⟩ := U.isThom k
    constructor
    · intro x y hxy
      simp only [LinearMap.neg_apply] at hxy
      exact h1 (neg_injective hxy)
    · intro y
      obtain ⟨x, hx⟩ := h2 (-y)
      exact ⟨x, by simp only [LinearMap.neg_apply]; rw [hx, neg_neg]⟩

/-- **`gtdU` with the tautological Thom class replaced by an arbitrary Thom class `U`**
(`Work.ThomBordism.gtdU`, `Submission/Work/ThomBordism/_gtd/P5.lean`, is the case
`U = Grassmann.tautologicalThomClass k 10`). -/
noncomputable def gtdUWith {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (G : C((normalBundle E ND).TotalSpace, (Grassmann.tautologicalBundle k 10).TotalSpace))
    (hgm : ∀ p ∈ Work.Thom.zeroComplement (normalBundle E ND),
      G p ∈ Work.Thom.zeroComplement (Grassmann.tautologicalBundle k 10))
    (U : Work.Thom.ThomClass (Grassmann.tautologicalBundle k 10) k) :
    Work.Thom.RelCoh ℤ k (TopCat.of (NormalTotal E)) (normalNonzero E) :=
  (Work.Thom.relCohMap ((eucNormalHomeomorph E ND).symm : C(NormalTotal E,
      (normalBundle E ND).TotalSpace)) (normalNonzero E)
    (Work.Thom.zeroComplement (normalBundle E ND)) (gtd_mem E ND) ℤ k).hom
    ((Work.Thom.relCohMap G (Work.Thom.zeroComplement (normalBundle E ND))
      (Work.Thom.zeroComplement (Grassmann.tautologicalBundle k 10)) hgm ℤ k).hom U.τ)

/-- `gtdU` is `gtdUWith` at the tautological Thom class (definitional). -/
theorem gtdU_eq_gtdUWith {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (G : C((normalBundle E ND).TotalSpace, (Grassmann.tautologicalBundle k 10).TotalSpace))
    (hgm : ∀ p ∈ Work.Thom.zeroComplement (normalBundle E ND),
      G p ∈ Work.Thom.zeroComplement (Grassmann.tautologicalBundle k 10)) :
    gtdU E ND G hgm = gtdUWith E ND G hgm (Grassmann.tautologicalThomClass k 10) := rfl

/-- **`gtdUWith` is `ℤ`-linear in the tautological class** (in particular it *flips sign* when the
class is negated). -/
theorem gtdUWith_neg {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (G : C((normalBundle E ND).TotalSpace, (Grassmann.tautologicalBundle k 10).TotalSpace))
    (hgm : ∀ p ∈ Work.Thom.zeroComplement (normalBundle E ND),
      G p ∈ Work.Thom.zeroComplement (Grassmann.tautologicalBundle k 10))
    (U : Work.Thom.ThomClass (Grassmann.tautologicalBundle k 10) k) :
    gtdUWith E ND G hgm (ThomClass.neg U) = - gtdUWith E ND G hgm U := by
  show (Work.Thom.relCohMap ((eucNormalHomeomorph E ND).symm : C(NormalTotal E,
      (normalBundle E ND).TotalSpace)) (normalNonzero E)
    (Work.Thom.zeroComplement (normalBundle E ND)) (gtd_mem E ND) ℤ k).hom
    ((Work.Thom.relCohMap G (Work.Thom.zeroComplement (normalBundle E ND))
      (Work.Thom.zeroComplement (Grassmann.tautologicalBundle k 10)) hgm ℤ k).hom (-U.τ))
    = -(Work.Thom.relCohMap ((eucNormalHomeomorph E ND).symm : C(NormalTotal E,
      (normalBundle E ND).TotalSpace)) (normalNonzero E)
    (Work.Thom.zeroComplement (normalBundle E ND)) (gtd_mem E ND) ℤ k).hom
    ((Work.Thom.relCohMap G (Work.Thom.zeroComplement (normalBundle E ND))
      (Work.Thom.zeroComplement (Grassmann.tautologicalBundle k 10)) hgm ℤ k).hom U.τ)
  rw [map_neg, map_neg]

/-- **The left-hand side of the target's conclusion is negated by negating the tautological Thom
class** — with the *same* datum `(E, ND, G, hgm, C, g, R, hbox)`, none of whose hypotheses mentions
that class.  So the target's conclusion is not determined by its hypotheses. -/
theorem proj_relCapPair_gtdUWith_neg {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (G : C((normalBundle E ND).TotalSpace, (Grassmann.tautologicalBundle k 10).TotalSpace))
    (hgm : ∀ p ∈ Work.Thom.zeroComplement (normalBundle E ND),
      G p ∈ Work.Thom.zeroComplement (Grassmann.tautologicalBundle k 10))
    {ε : ℝ} (C : TubeChart E ε)
    {R : ℝ} (hR : 0 ≤ R) (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    (U : Work.Thom.ThomClass (Grassmann.tautologicalBundle k 10) k) :
    (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (TopCat.of (NormalTotal E))
        (TopCat.of V.pt) (TopCat.ofHom ⟨fun y => NormalTotal.proj y,
          NormalTotal.continuous_proj E⟩)) 8)
      ((Work.Cohomology.relCapPair (TopCat.of (NormalTotal E)) (normalNonzero E) k 8
        (gtdUWith E ND G hgm (ThomClass.neg U))) (collapseRelK8 C g hg hR hbox))
    = - (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (TopCat.of (NormalTotal E))
        (TopCat.of V.pt) (TopCat.ofHom ⟨fun y => NormalTotal.proj y,
          NormalTotal.continuous_proj E⟩)) 8)
      ((Work.Cohomology.relCapPair (TopCat.of (NormalTotal E)) (normalNonzero E) k 8
        (gtdUWith E ND G hgm U)) (collapseRelK8 C g hg hR hbox)) := by
  have h1 : (Work.Cohomology.relCapPair (TopCat.of (NormalTotal E)) (normalNonzero E) k 8)
        (gtdUWith E ND G hgm (ThomClass.neg U))
      = - ((Work.Cohomology.relCapPair (TopCat.of (NormalTotal E)) (normalNonzero E) k 8)
        (gtdUWith E ND G hgm U)) := by
    rw [gtdUWith_neg]
    exact map_neg _ _
  rw [h1, LinearMap.neg_apply]
  exact map_neg (ConcreteCategory.hom (HomologicalComplex.homologyMap
    (Work.Cohomology.chainMap ℤ (TopCat.of (NormalTotal E)) (TopCat.of V.pt)
      (TopCat.ofHom ⟨fun y => NormalTotal.proj y, NormalTotal.continuous_proj E⟩)) 8)) _

end

end Work.ThomBordism
