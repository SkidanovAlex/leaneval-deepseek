import Submission.Work.Tubular.onePoint_pairing_transfer
import Submission.Work.Tubular.LocalStep
import Submission.Work.Cohomology.RelCupTransfer

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

/-!
# The local degree of the Pontryagin–Thom collapse, in the pair `(ν⁺, A)`

`Work.Tubular.TubeLocalDegree` (README §23) states the local degree against the pair
`(Z.TotalSpace, zeroComplement Z)` — the *relative* world of the normal bundle in the gluing-data
model.  The Pontryagin–Thom chapter consumes the pairing in the *absolute* world of
`Th(ν) = ν⁺ = OnePoint (NormalTotal E)`, and `Work.Tubular.kronH_eq_relKronH_onePoint` (this round)
rewrites that pairing in the relative world of the pair `(ν⁺, A)` — where both the universal class
`Ψ u` and the collapse class `π_*(h(collapse))` are explicit, but where nothing is stated yet.

This module states the local degree **exactly there**, as the one remaining geometric input:

* `Work.Tubular.zeroSectionOnePoint` — the zero section `V → ν⁺` of the normal bundle, composed with
  the one-point inclusion;
* `Work.Tubular.TubeLocalDegreeOnePoint E U c'` — for every degree-`8` class `x` on `ν⁺`,

  `⟨x ⌣ U, π_* c'⟩ = ⟨(zero section)^* x, [V]⟩`,

  i.e. the Thom class `U` (a class in the pair `(ν⁺,A)`) is the Poincaré dual of the zero section
  and `c'` is the collapse class.
-/

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial Topology

open Work.ThomBordism.PontryaginThom (EmbeddingData)

namespace Work.Tubular

noncomputable section

open Work.Cohomology

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- The zero normal vector is normal. -/
theorem zero_mem_normalSpace {k : ℕ} (E : EmbeddingData V (8 + k)) (x : V.pt) :
    (0 : Euc (8 + k)) ∈ normalSpace E x := by
  rw [mem_normalSpace_iff]
  intro u _
  simp

/-- **The zero section of `ν⁺`**: the composite `V → ν → ν⁺` of the zero section of the normal
bundle with the one-point inclusion `some`. -/
noncomputable def zeroSectionOnePoint {k : ℕ} (E : EmbeddingData V (8 + k)) :
    C(V.pt, OnePoint (NormalTotal E)) where
  toFun x := OnePoint.some ⟨(x, 0), zero_mem_normalSpace E x⟩
  continuous_toFun :=
    OnePoint.continuous_coe.comp (Continuous.subtype_mk
      (f := fun x : V.pt => ((x, 0) : V.pt × Euc (8 + k)))
      (continuous_id.prodMk continuous_const) (fun x => zero_mem_normalSpace E x))

@[simp] theorem zeroSectionOnePoint_apply {k : ℕ} (E : EmbeddingData V (8 + k)) (x : V.pt) :
    ((zeroSectionOnePoint E x : OnePoint (NormalTotal E)))
      = OnePoint.some ⟨(x, 0), zero_mem_normalSpace E x⟩ := rfl

/-- **The local degree of the Pontryagin–Thom collapse, in the pair `(ν⁺, A)`.**  `U` is a class of
degree `k` in the pair `(ν⁺, A = (ν∖0) ∪ {∞})` (the Thom class of the normal bundle, transported to
the one-point compactification) and `c'` is the Hurewicz class of the collapse
(`Work.Tubular.tubeGenLoopOnePoint`); the statement is that the *mixed* cup of a degree-`8` class `x`
on `ν⁺` with `U` pairs with the collapse class as `(zero section)^*x` pairs with `[V]`.

This is the same geometric content as `Work.Tubular.TubeLocalDegree` (§23) — the fibre computation
`U_ν ⌢ c = z_*[V]` — stated in the world where the consumer's Hurewicz pairing lives and where the
transfer `Work.Tubular.kronH_eq_relKronH_onePoint` applies.

> **VACUITY WARNING (README §35.2).**  The class `x` ranges over
> `H⁸(OnePoint (NormalTotal E)) = H⁸(Th ν)`, and the Thom space of the rank-`k` normal bundle is
> `(k-1)`-connected, so for `8 < k` — in particular for the project's `k = 11` — this group is
> **zero**, both sides of the identity vanish, and the statement holds for *every* pair `(U, c')`.
> The non-vacuous form of the local degree is `Work.Tubular.TubeLocalDegree` /
> `Work.Tubular.TubeLocalDegreePairing` (`LocalStep.lean`), stated on `Z.TotalSpace` (where
> `H⁸ ≅ H⁸(V) ≅ ℤ`); its wiring to the Hurewicz pairing is
> `Work.Tubular.kronH_relKronH_eq_fundClass` together with the `8 + k ↔ k + 8` transport
> `Work.Tubular.hurewiczClassOf_add_comm`.
-/


def TubeLocalDegreeOnePoint {k : ℕ} (E : EmbeddingData V (8 + k))
    (U : Work.Thom.RelCoh ℤ k (OnePoint (NormalTotal E)) (onePointNonzero E))
    (c' : (singularChains ℤ (TopCat.of (OnePoint (NormalTotal E)))).homology (k + 8)) : Prop :=
  ∀ x : Work.Thom.Coh ℤ 8 (OnePoint (NormalTotal E)),
    relKronH (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E) (k + 8)
        ((Nat.add_comm 8 k) ▸ (mixedCup (TopCat.of (OnePoint (NormalTotal E)))
          (onePointNonzero E) 8 k x U))
        ((HomologicalComplex.homologyMap (CategoryTheory.Limits.cokernel.π
          (inclChains (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E))) (k + 8)) c')
      = Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8
          ((Work.Thom.CohMap (zeroSectionOnePoint E) ℤ 8).hom x) V.c

end

end Work.Tubular
