import Mathlib
import Submission.Work.DSMap.Gaps
import Submission.Work.DSCOH.chartCech_finite_vanishing
import Submission.Work.DSSEC.Main
import Submission.Work.DSEQP.gf_gamma_eq_h0_cech
import Submission.Work.DSEQP.cech_homology_zero_iso_ker
import Submission.Work.DSEQP.gf_defs
import Submission.Work.DSEQP.gf_sat
import Submission.Work.DSEQP.DZA.gf_degzero_away
import Submission.Work.DSEQP.Term.degZero_quot_away
import Submission.Work.DSEQP.Term.awayQuot_iso_gamma
import Submission.Work.DSEQP.Geom.ker_cechDiff_geomD0
import Submission.Work.DSEQP.Geom.geomD0_ker_iso_gamma

/-!
# `Work.DSEQP.gf_bridge` — Γ(X, 𝒪_X) is the degree-0 chart Čech cohomology of a f.g. graded module

The geometric bridge of area `DSEQP`'s route to `gamma_finite`: for `X` a closed subscheme of
`ℙᴺ_A = DSMap.PSpace A N` over `A` Noetherian, there is a finitely generated graded module `M`
over `A[x₀,…,x_N]` whose *chart Čech* cohomology in degree `0` (`Work.DSCOH.chartCech`) computes
`Γ(X, 𝒪_X)`.

The module is `M = A[x₀,…,x_N] ⧸ J` with `J` the saturation of the vanishing ideal of `X`
(`Work.DSEQP.Jvan`), graded by the images of the homogeneous pieces (`Work.DSEQP.Mg`).  The proof
is the chain

* `Work.DSEQP.chartCechTerm_iso` (below): the chart Čech terms `degZero (Mg i) S` are the sections
  of `𝒪_X` over the charts `U_S = i⁻¹D₊(x_S)`, compatibly with the restriction maps.  It is the
  composite of `Work.DSEQP.Term.degZero_quot_away` (the degree-zero part of the chart localisation
  of `R ⧸ J` is the chart ring modulo the chart ideal of `J`) with
  `Work.DSEQP.Term.awayQuot_iso_gamma` (the chart ring modulo that ideal is `Γ(X, U_S)`, using the
  saturation `Work.DSEQP.gf_sat`);
* hence, by `Work.DSEQP.Geom.ker_cechDiff_geomD0`, the `0`-cocycles of the chart Čech complex are
  the `0`-cocycles of the *geometric* alternating chart complex `Work.DSEQP.geomD0`;
* `Work.DSEQP.Geom.geomD0_ker_iso_gamma`: those `0`-cocycles are `Γ(X, 𝒪_X)` (gluing);
* finally `H⁰` in degree `0` is `ker (d 0 1)` (`Work.DSEQP.cech_homology_zero_iso_ker`) and
  `Γ(X, ⊤)` with the `A`-structure of `(DSMap.phi A X f).toAlgebra` is
  `↥((DSMap.cechPresheaf A X f).obj (op ⊤))` (`Work.DSEQP.gamma_id_linearEquiv`).
-/

set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry
open scoped BigOperators

namespace Work.DSEQP

universe a u v

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ## 5. The chart-wise comparison `degZero ℳ S ≅ Γ(X, U_S)` -/

section ChartComparison

/-- **The chart-wise comparison.**  For every nonempty `S`, the degree-zero part of the chart
Čech term of `M = R ⧸ J` at `S` — i.e. the sections of `M~` over `D₊(x_S)` — is the module of
sections of `𝒪_X` over `U_S = i⁻¹D₊(x_S)`, compatibly with the restriction maps.

Both sides are `Away 𝒜 (x_S) ⧸ chartJ` — the `A`-module structure on the right is the one induced
by `f` — and the identification is the chart comparison `chartMap` modulo the saturation
`chartJ_eq_ker`, with the module side coming from the exactness of localization for
`0 → J → R → M → 0`. -/
theorem chartCechTerm_iso (A : Type a) [CommRing A] (N : ℕ) {X : AlgebraicGeometry.Scheme.{a}}
    (i : X ⟶ DSMap.PSpace A N) (hi : AlgebraicGeometry.IsClosedImmersion i)
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A))
    (hif : i ≫ DSMap.PSpace.toSpec A N = f) :
    ∃ e : ∀ (S : Finset (Fin (N + 1))) (hS : S.Nonempty),
        (↥(Work.DSCOH.degZero (A := A) (n := N + 1) (M := Mmod i) (Mg i) S) ≃ₗ[A]
          ↥((DSMap.cechPresheaf A X f).obj (Opposite.op (Ucmp i S)))),
      ∀ (S T : Finset (Fin (N + 1))) (hST : S ⊆ T) (hS : S.Nonempty) (hT : T.Nonempty)
        (x : ↥(Work.DSCOH.degZero (A := A) (n := N + 1) (M := Mmod i) (Mg i) S)),
        e T hT ⟨Work.DSCOH.resAt (A := A) (n := N + 1) (M := Mmod i) hST x.1,
            Work.DSCOH.resAt_degZero (A := A) (n := N + 1) (M := Mmod i) (ℳ := Mg i)
              hST x.1 x.2⟩
          = (DSMap.cechPresheaf A X f).map (homOfLE (Ucmp_anti i hST)).op (e S hS x) := by
  haveI : AlgebraicGeometry.IsClosedImmersion i := hi
  obtain ⟨e6, hnat6⟩ := Term.degZero_quot_away (A := A) (N := N) (X := X) i hi
  obtain ⟨e5, hnat5⟩ := Term.awayQuot_iso_gamma (A := A) (N := N) (X := X) i f hif
    (fun S hS => Work.DSEQP.gf_sat (A := A) (N := N) (X := X) i hi S hS)
  refine ⟨fun S hS => (e6 S hS).symm.trans (e5 S hS), ?_⟩
  intro S T hST hS hT x
  obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (I := Work.DSEQP.chartJ i S) ((e6 S hS).symm x)
  have hx : e6 S hS (Ideal.Quotient.mk (Work.DSEQP.chartJ i S) z) = x := by
    rw [hz, LinearEquiv.apply_symm_apply]
  have h6 := hnat6 S T hST hS hT z
  rw [hx] at h6
  have h1 : (e6 T hT).symm ⟨Work.DSCOH.resAt (A := A) (n := N + 1) (M := Mmod i)
        hST x.1, Work.DSCOH.resAt_degZero (A := A) (n := N + 1) (M := Mmod i)
          (ℳ := Mg i) hST x.1 x.2⟩
      = Ideal.Quotient.mk (Work.DSEQP.chartJ i T)
          (Work.DSEQP.awayRes (A := A) (N := N) hST z) :=
    (LinearEquiv.symm_apply_eq _).mpr h6.symm
  have h2 : (e6 S hS).symm x = Ideal.Quotient.mk (Work.DSEQP.chartJ i S) z := hz.symm
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply]
  rw [h1, h2]
  exact hnat5 S T hST hS hT z

end ChartComparison

/-! ## 6. The degree-zero chart Čech cohomology of `M` -/

section ChartCechH0

/-- **The degree-`0` chart Čech cohomology of `M = R ⧸ J` is `Γ(X, 𝒪_X)`.** -/
theorem chartCech_homology_zero_iso (A : Type a) [CommRing A] (N : ℕ)
    {X : AlgebraicGeometry.Scheme.{a}} (i : X ⟶ DSMap.PSpace A N)
    (hi : AlgebraicGeometry.IsClosedImmersion i)
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A))
    (hif : i ≫ DSMap.PSpace.toSpec A N = f) :
    letI := (DSMap.phi A X f).toAlgebra
    Nonempty (↥((Work.DSCOH.chartCech (A := A) (n := N + 1) (M := Mmod i) (Mg i)).homology 0) ≃ₗ[A]
      ↥(X.presheaf.obj (Opposite.op ⊤))) := by
  letI : Algebra A ↥(X.presheaf.obj (Opposite.op ⊤)) := (DSMap.phi A X f).toAlgebra
  obtain ⟨eTerm, hnat⟩ := chartCechTerm_iso (A := A) (N := N) (X := X) i hi f hif
  obtain ⟨eK⟩ := Geom.ker_cechDiff_geomD0 (A := A) (N := N) (X := X) i f eTerm hnat
  obtain ⟨eG⟩ := Geom.geomD0_ker_iso_gamma (A := A) (N := N) (X := X) i f
  obtain ⟨eH⟩ := Work.DSEQP.cochainComplex_homology_zero_iso_ker
    (Work.DSCOH.chartCech (A := A) (n := N + 1) (M := Mmod i) (Mg i))
  obtain ⟨eg⟩ := Work.DSEQP.gamma_id_linearEquiv (A := A) (X := X) (f := f)
  refine ⟨eH.trans ((LinearEquiv.ofEq _ _ ?_).trans (eK.trans (eG.trans eg.symm)))⟩
  congr 1

end ChartCechH0

theorem gf_bridge (A : Type a) [CommRing A] [IsNoetherianRing A] {N : ℕ}
    {X : AlgebraicGeometry.Scheme.{a}} (i : X ⟶ DSMap.PSpace A N) (hi : AlgebraicGeometry.IsClosedImmersion i)
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) (hif : i ≫ DSMap.PSpace.toSpec A N = f) :
    ∃ (M : Type a) (h1 : AddCommGroup M) (h2 : Module A M)
      (h3 : Module (MvPolynomial (Fin (N + 1)) A) M)
      (h4 : IsScalarTower A (MvPolynomial (Fin (N + 1)) A) M)
      (ℳ : ℕ → Submodule A M)
      (h5 : DirectSum.Decomposition ℳ)
      (h6 : SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A) ℳ)
      (h7 : Module.Finite (MvPolynomial (Fin (N + 1)) A) M),
      letI := h1; letI := h2; letI := h3; letI := h4; letI := h5; letI := h6; letI := h7
      letI := (DSMap.phi A X f).toAlgebra
      Nonempty (↥(X.presheaf.obj (Opposite.op ⊤)) ≃ₗ[A]
        ↥((Work.DSCOH.chartCech (A := A) (n := N + 1) (M := M) ℳ).homology 0)) := by
  refine ⟨Mmod i, inferInstance, inferInstance, inferInstance, inferInstance, Mg i,
    MgDecomposition i, inferInstance, finite_Mmod i, ?_⟩
  obtain ⟨e⟩ := chartCech_homology_zero_iso A N i hi f hif
  exact ⟨e.symm⟩

end Work.DSEQP
