import Mathlib
import Submission.Work.DSEQP.gf_defs
import Submission.Work.DSCHART.Basic
import Submission.Work.DSCHART.xiSec_surjective
import Submission.Work.DSEQP.Term.phiU_pspace_awayToSection_S
import Submission.Work.DSEQP.Term.chartMap_awayRes_nat

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory AlgebraicGeometry

namespace Work.DSEQP.Term

universe a

/-! ## Preliminaries

Two small ingredients: the chart isomorphism `Away 𝒜 (x_S) ≅ Γ(D₊(x_S), 𝒪_ℙ)` is Mathlib's
`Proj.awayToSection`, and the chart comparison `chartMap` is `A`-linear (as a map of `A`-algebras),
which is where the Proj-side input `phiU_pspace_awayToSection_S` enters.  -/

/-- The underlying ring hom of the chart isomorphism `Work.DSEQP.awayIso` is Mathlib's
`Proj.awayToSection`. -/
lemma awayIso_toRingHom {A : Type a} [CommRing A] {N : ℕ}
    (S : Finset (Fin (N + 1))) (hS : S.Nonempty) :
    (Work.DSEQP.awayIso (A := A) (N := N) S hS).toRingHom
      = CommRingCat.Hom.hom
          (AlgebraicGeometry.Proj.awayToSection (DSMap.PGr A N) (Work.DSEQP.xS (A := A) S)) := by
  rw [Work.DSEQP.awayIso]; rfl

/-- **`chartMap` is a map of `A`-algebras.**  The chart comparison
`chartMap i S hS : Away 𝒜 (x_S) →+* Γ(X, U_S)` sends the scalar `AtoAway S c` to the scalar
`φ c` of `𝒪_X` (the structure map of `f`), i.e. it is `A`-linear for the `A`-algebra structures
`AtoAway` (on the chart ring) and `DSMap.phiU` (on the sections of `𝒪_X`).

The proof combines the two structure-map identifications: on `ℙᴺ_A` the structure map on `D₊(x_S)`
is `awayToSection ∘ AtoAway` (`phiU_pspace_awayToSection_S`), and the structure map of `X` on
`U_S = i⁻¹D₊(x_S)` is the pullback of that along `i` when `i ≫ toSpec = f`
(`Work.DSCHART.phiU_comp`). -/
lemma chartMap_AtoAway {A : Type a} [CommRing A] {N : ℕ} {X : AlgebraicGeometry.Scheme.{a}}
    (i : X ⟶ DSMap.PSpace A N) (f : X ⟶ Spec (CommRingCat.of A))
    (hif : i ≫ DSMap.PSpace.toSpec A N = f)
    (hL : ∀ (S : Finset (Fin (N + 1))) (hS : S.Nonempty),
      DSMap.phiU A (DSMap.PSpace A N) (DSMap.PSpace.toSpec A N)
          (Work.DSEQP.Dcmp (A := A) (N := N) S)
        = ((AlgebraicGeometry.Proj.awayToSection (DSMap.PGr A N)
              (Work.DSEQP.xS (A := A) S)).hom).comp
            (Work.DSEQP.AtoAway (A := A) (N := N) S))
    (S : Finset (Fin (N + 1))) (hS : S.Nonempty) (c : A) :
    Work.DSEQP.chartMap i S hS (Work.DSEQP.AtoAway (A := A) (N := N) S c)
      = DSMap.phiU A X f (Work.DSEQP.Ucmp i S) c := by
  rw [Work.DSEQP.chartMap, RingHom.comp_apply, awayIso_toRingHom]
  have hh := DFunLike.congr_fun (hL S hS) c
  rw [RingHom.comp_apply] at hh
  rw [← hh]
  have hcomp := Work.DSCHART.phiU_comp (A := A) (X := DSMap.PSpace A N) (X' := X)
      (DSMap.PSpace.toSpec A N) i (Work.DSEQP.Dcmp (A := A) (N := N) S)
  rw [hif] at hcomp
  rw [← RingHom.comp_apply, ← hcomp]

/-! ## The chart ring of `X` at `U_S` -/

/-- The core of `awayQuot_iso_gamma`: given the two chart-level inputs (`hL`, the structure map of
`ℙᴺ_A` on `D₊(x_S)` is `awayToSection ∘ AtoAway`, and `hN`, the naturality of `chartMap` under
`awayRes`), the chart comparison identifies the quotient `Away 𝒜 (x_S) ⧸ chartJ i S` with the
sections `Γ(X, U_S)` of `𝒪_X`, naturally in the chart `S`.

Since `chartMap` is surjective (`Work.DSEQP.chartMap_surjective`) with kernel `chartJ i S`
(`hsat`), it descends to an isomorphism of `A`-algebras `Away ⧸ chartJ ≃ₐ[A] Γ(X, U_S)` — built
here as `AlgEquiv.ofBijective` applied to the descent `Ideal.Quotient.lift` of `chartMap` (made
`A`-linear by `chartMap_AtoAway`) — and the naturality is exactly `hN`. -/
theorem awayQuot_iso_gamma_of_charts {A : Type a} [CommRing A] {N : ℕ}
    {X : AlgebraicGeometry.Scheme.{a}}
    (i : X ⟶ DSMap.PSpace A N) [AlgebraicGeometry.IsClosedImmersion i]
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A))
    (hif : i ≫ DSMap.PSpace.toSpec A N = f)
    (hsat : ∀ (S : Finset (Fin (N + 1))) (hS : S.Nonempty),
      Work.DSEQP.chartJ i S = RingHom.ker (Work.DSEQP.chartMap i S hS))
    (hL : ∀ (S : Finset (Fin (N + 1))) (hS : S.Nonempty),
      DSMap.phiU A (DSMap.PSpace A N) (DSMap.PSpace.toSpec A N)
          (Work.DSEQP.Dcmp (A := A) (N := N) S)
        = ((AlgebraicGeometry.Proj.awayToSection (DSMap.PGr A N)
              (Work.DSEQP.xS (A := A) S)).hom).comp
            (Work.DSEQP.AtoAway (A := A) (N := N) S))
    (hN : ∀ (S T : Finset (Fin (N + 1))) (hST : S ⊆ T) (hS : S.Nonempty) (hT : T.Nonempty)
        (z : HomogeneousLocalization.Away (DSMap.PGr A N) (Work.DSEQP.xS (A := A) S)),
        Work.DSEQP.chartMap i T hT (Work.DSEQP.awayRes (A := A) (N := N) hST z)
          = (DSMap.cechPresheaf A X f).map
              (homOfLE (Work.DSEQP.Ucmp_anti i hST)).op
              (Work.DSEQP.chartMap i S hS z)) :
    ∃ e : ∀ (S : Finset (Fin (N + 1))) (hS : S.Nonempty),
        (((HomogeneousLocalization.Away (DSMap.PGr A N) (Work.DSEQP.xS (A := A) S)) ⧸
            Work.DSEQP.chartJ i S) ≃ₗ[A]
          ↥((DSMap.cechPresheaf A X f).obj (Opposite.op (Work.DSEQP.Ucmp i S)))),
      ∀ (S T : Finset (Fin (N + 1))) (hST : S ⊆ T) (hS : S.Nonempty) (hT : T.Nonempty)
        (z : HomogeneousLocalization.Away (DSMap.PGr A N) (Work.DSEQP.xS (A := A) S)),
        e T hT (Ideal.Quotient.mk (Work.DSEQP.chartJ i T)
            (Work.DSEQP.awayRes (A := A) (N := N) hST z))
          = (DSMap.cechPresheaf A X f).map (homOfLE (Work.DSEQP.Ucmp_anti i hST)).op
              (e S hS (Ideal.Quotient.mk (Work.DSEQP.chartJ i S) z)) := by
  have key : ∀ (S : Finset (Fin (N + 1))) (hS : S.Nonempty),
      ∃ e : (((HomogeneousLocalization.Away (DSMap.PGr A N) (Work.DSEQP.xS (A := A) S)) ⧸
            Work.DSEQP.chartJ i S) ≃ₗ[A]
          ↥((DSMap.cechPresheaf A X f).obj (Opposite.op (Work.DSEQP.Ucmp i S)))),
        ∀ z : HomogeneousLocalization.Away (DSMap.PGr A N) (Work.DSEQP.xS (A := A) S),
          e (Ideal.Quotient.mk (Work.DSEQP.chartJ i S) z) = Work.DSEQP.chartMap i S hS z := by
    intro S hS
    letI : Algebra A Γ(X, Work.DSEQP.Ucmp i S) :=
      (DSMap.phiU A X f (Work.DSEQP.Ucmp i S)).toAlgebra
    let fS : HomogeneousLocalization.Away (DSMap.PGr A N) (Work.DSEQP.xS (A := A) S) →ₐ[A]
        Γ(X, Work.DSEQP.Ucmp i S) :=
      { Work.DSEQP.chartMap i S hS with
        commutes' := by
          intro c
          rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
          exact chartMap_AtoAway i f hif hL S hS c }
    have hfs : ∀ a : HomogeneousLocalization.Away (DSMap.PGr A N) (Work.DSEQP.xS (A := A) S),
        (fS : HomogeneousLocalization.Away (DSMap.PGr A N) (Work.DSEQP.xS (A := A) S) →+*
          Γ(X, Work.DSEQP.Ucmp i S)) a = Work.DSEQP.chartMap i S hS a := fun a => rfl
    have hI : ∀ a ∈ Work.DSEQP.chartJ i S,
        (fS : HomogeneousLocalization.Away (DSMap.PGr A N) (Work.DSEQP.xS (A := A) S) →+*
          Γ(X, Work.DSEQP.Ucmp i S)) a = 0 := by
      intro a ha
      rw [hfs a]
      have h : a ∈ RingHom.ker (Work.DSEQP.chartMap i S hS) := by
        rwa [← hsat S hS]
      rwa [RingHom.mem_ker] at h
    let gR : ((HomogeneousLocalization.Away (DSMap.PGr A N) (Work.DSEQP.xS (A := A) S)) ⧸
          Work.DSEQP.chartJ i S) →+* Γ(X, Work.DSEQP.Ucmp i S) :=
      Ideal.Quotient.lift (Work.DSEQP.chartJ i S)
        (fS : HomogeneousLocalization.Away (DSMap.PGr A N) (Work.DSEQP.xS (A := A) S) →+*
          Γ(X, Work.DSEQP.Ucmp i S)) hI
    let g : ((HomogeneousLocalization.Away (DSMap.PGr A N) (Work.DSEQP.xS (A := A) S)) ⧸
          Work.DSEQP.chartJ i S) →ₐ[A] Γ(X, Work.DSEQP.Ucmp i S) :=
      { gR with
        commutes' := by
          intro c
          show gR (algebraMap A _ c) = algebraMap A Γ(X, Work.DSEQP.Ucmp i S) c
          rw [← Ideal.Quotient.mk_comp_algebraMap, RingHom.comp_apply,
            RingHom.algebraMap_toAlgebra, Ideal.Quotient.lift_mk, hfs,
            RingHom.algebraMap_toAlgebra]
          exact chartMap_AtoAway i f hif hL S hS c }
    have hgm : ∀ x, g (Ideal.Quotient.mk (Work.DSEQP.chartJ i S) x)
        = Work.DSEQP.chartMap i S hS x := by
      intro x
      change gR (Ideal.Quotient.mk (Work.DSEQP.chartJ i S) x) = Work.DSEQP.chartMap i S hS x
      rw [Ideal.Quotient.lift_mk, hfs x]
    have hbij : Function.Bijective g := by
      refine ⟨?_, ?_⟩
      · intro x y hxy
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := Work.DSEQP.chartJ i S) x
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective (I := Work.DSEQP.chartJ i S) y
        rw [hgm, hgm] at hxy
        have hsub : a - b ∈ Work.DSEQP.chartJ i S := by
          have h1 : Work.DSEQP.chartMap i S hS (a - b) = 0 := by rw [map_sub, hxy, sub_self]
          have h2 : a - b ∈ RingHom.ker (Work.DSEQP.chartMap i S hS) := by
            rwa [RingHom.mem_ker]
          rw [← hsat S hS] at h2
          exact h2
        have h0 : Ideal.Quotient.mk (Work.DSEQP.chartJ i S) (a - b) = 0 := by
          rw [Ideal.Quotient.eq_zero_iff_mem]; exact hsub
        rwa [map_sub, sub_eq_zero] at h0
      · intro y
        obtain ⟨z, hz⟩ := Work.DSEQP.chartMap_surjective i
          ‹AlgebraicGeometry.IsClosedImmersion i› S hS y
        exact ⟨Ideal.Quotient.mk (Work.DSEQP.chartJ i S) z, by rw [hgm]; exact hz⟩
    refine ⟨(AlgEquiv.ofBijective g hbij).toLinearEquiv, ?_⟩
    intro z
    change g (Ideal.Quotient.mk (Work.DSEQP.chartJ i S) z) = Work.DSEQP.chartMap i S hS z
    exact hgm z
  choose e he using key
  refine ⟨e, ?_⟩
  intro S T hST hS hT z
  rw [he T hT (Work.DSEQP.awayRes (A := A) (N := N) hST z), hN S T hST hS hT z,
    ← he S hS z]

/-- **The chart ring of `X` at `U_S`.**  For `i : X ↪ ℙᴺ_A` a closed immersion and
`f = i ≫ toSpec`, the chart comparison `chartMap i S` (the chart ring `Away 𝒜 (x_S) ≅
Γ(D₊(x_S), 𝒪_ℙ)` composed with pullback along `i`) is surjective with kernel `chartJ i S`, whence
`(Away 𝒜 (x_S) ⧸ chartJ i S) ≃ₗ[A] Γ(X, U_S)`; the naturality says that this isomorphism
intertwines the localisation maps `awayRes` between the chart rings with the restriction maps of
`𝒪_X`.  The hypothesis `hsat` is the saturation statement `chartJ i S = RingHom.ker (chartMap i S
hS)` (proved as `Work.DSEQP.gf_sat`). -/
theorem awayQuot_iso_gamma (A : Type a) [CommRing A] {N : ℕ} {X : AlgebraicGeometry.Scheme.{a}}
    (i : X ⟶ DSMap.PSpace A N) [AlgebraicGeometry.IsClosedImmersion i]
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A))
    (hif : i ≫ DSMap.PSpace.toSpec A N = f)
    (hsat : ∀ (S : Finset (Fin (N + 1))) (hS : S.Nonempty),
      Work.DSEQP.chartJ i S = RingHom.ker (Work.DSEQP.chartMap i S hS)) :
    ∃ e : ∀ (S : Finset (Fin (N + 1))) (hS : S.Nonempty),
        (((HomogeneousLocalization.Away (DSMap.PGr A N) (Work.DSEQP.xS (A := A) S)) ⧸
            Work.DSEQP.chartJ i S) ≃ₗ[A]
          ↥((DSMap.cechPresheaf A X f).obj (Opposite.op (Work.DSEQP.Ucmp i S)))),
      ∀ (S T : Finset (Fin (N + 1))) (hST : S ⊆ T) (hS : S.Nonempty) (hT : T.Nonempty)
        (z : HomogeneousLocalization.Away (DSMap.PGr A N) (Work.DSEQP.xS (A := A) S)),
        e T hT (Ideal.Quotient.mk (Work.DSEQP.chartJ i T)
            (Work.DSEQP.awayRes (A := A) (N := N) hST z))
          = (DSMap.cechPresheaf A X f).map (homOfLE (Work.DSEQP.Ucmp_anti i hST)).op
              (e S hS (Ideal.Quotient.mk (Work.DSEQP.chartJ i S) z)) := by
  exact awayQuot_iso_gamma_of_charts i f hif hsat
    (fun S hS => phiU_pspace_awayToSection_S A S hS)
    (fun S T hST hS hT z => chartMap_awayRes_nat hST hS hT z)

end Work.DSEQP.Term
