import Mathlib
import Submission.Work.DSEQP.gf_defs
import Submission.Work.DSEQP.vanishing_ideal_chart_monomial

/-!
# `Work.DSEQP.chartJ_saturation`

The chart-saturation statement in the form needed by the assembly around the chart Čech complex:
if a chart section `z ∈ Away 𝒜 (x_S)` vanishes on `X ∩ D₊(x_S)` (i.e. lies in the kernel of the
chart comparison `chartMap i S hS`), then `z` is the image `g / x_S^k` of a form `g` of degree
`k·|S|` whose chart sections `g / x_j^{k|S|}` vanish in *every* singleton chart `D₊(x_j)` —
equivalently, `g` lies in the saturation `Jvan i` of the vanishing ideal of `X` in `ℙᴺ_A`.

The mathematical content is `Work.DSEQP.vanishing_ideal_chart_monomial`, stated there in the
`Proj`-presentation of the charts (`D₊(∏_{k ∈ T} X k)` for the big chart and `D₊(X j)` for the
singletons); here it is transported to the `Proj.basicOpenIsoAway`/`awayIso`-presentation used by
`chartMap`, together with the translation between membership in the kernel of `chartMap` and
vanishing of the corresponding quotient by the ideal sheaf of `X`.
-/

namespace Work.DSEQP

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

universe a

set_option maxHeartbeats 1000000

variable {A : Type a} [CommRing A] {N : ℕ} {X : AlgebraicGeometry.Scheme.{a}}

/-- **The bridge between the two presentations of a singleton chart.**  If the chart section
`g / x_j^k` of `ℙᴺ_A` vanishes on `X` in the chart `D₊(X j)` — stated as the vanishing of the
class of its image under `Proj.basicOpenIsoAway` in the quotient by the ideal sheaf of `X` — then
it vanishes in the same chart presented as `D₊(F)` for any homogeneous `F = X j` of degree one.

The two presentations differ only in the chosen form `F` (of degree one) defining the chart, which
`hFj` identifies with `X j`; after `subst` the two sides differ only in (irrelevant) proof
arguments and in the identification of `i.ker.ideal` with the kernel of `i.app` (`ker_apply`,
legitimate because `i` is quasi-compact). -/
lemma chartMap_basicOpen_singleton_eq_zero (i : X ⟶ DSMap.PSpace A N) [QuasiCompact i]
    {F : MvPolynomial (Fin (N + 1)) A} (hF : F ∈ DSMap.PGr A N 1) {j : Fin (N + 1)}
    (hFj : F = MvPolynomial.X j) (k : ℕ) (g : MvPolynomial (Fin (N + 1)) A)
    (hmem : g ∈ DSMap.PGr A N (k • 1))
    (h : Ideal.Quotient.mk (i.ker.ideal
        ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A) (MvPolynomial.X j),
          Proj.isAffineOpen_basicOpen _ (MvPolynomial.X j)
            (MvPolynomial.isHomogeneous_X A j) (by norm_num)⟩)
        ((Proj.basicOpenIsoAway (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)
            (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X A j) (by norm_num)).hom
          (Away.mk (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)
            (MvPolynomial.isHomogeneous_X A j) k g hmem)) = 0) :
    (CommRingCat.Hom.hom (Scheme.Hom.app i (Proj.basicOpen (DSMap.PGr A N) F)))
      ((CommRingCat.Hom.hom (Proj.basicOpenIsoAway (DSMap.PGr A N) F hF (by norm_num)).hom)
        (Away.mk (DSMap.PGr A N) hF k g hmem)) = 0 := by
  subst hFj
  rw [Ideal.Quotient.eq_zero_iff_mem] at h
  rw [Scheme.Hom.ker_apply i ⟨Proj.basicOpen (DSMap.PGr A N) (MvPolynomial.X j),
    Proj.isAffineOpen_basicOpen _ (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X A j)
      (by norm_num)⟩, RingHom.mem_ker] at h
  exact h

theorem chartJ_saturation (A : Type a) [CommRing A] {N : ℕ} {X : AlgebraicGeometry.Scheme.{a}}
    (i : X ⟶ DSMap.PSpace A N) (hi : AlgebraicGeometry.IsClosedImmersion i)
    (S : Finset (Fin (N + 1))) (hS : S.Nonempty)
    (z : HomogeneousLocalization.Away (DSMap.PGr A N) (Work.DSEQP.xS (A := A) S))
    (hz : z ∈ RingHom.ker (Work.DSEQP.chartMap i S hS)) :
    ∃ (k : ℕ) (g : MvPolynomial (Fin (N + 1)) A)
      (hg : g ∈ Work.DSCOH.homSub A (N + 1) (k * S.card)),
      (∀ j' : Fin (N + 1), Work.DSEQP.chartMap i {j'} (Finset.singleton_nonempty j')
          (HomogeneousLocalization.Away.mk (DSMap.PGr A N) (Work.DSEQP.xS_singleton_mem j')
            (k * S.card) g (by simpa using hg)) = 0) ∧
      z = HomogeneousLocalization.Away.mk (DSMap.PGr A N) (Work.DSEQP.xS_mem_homSub S) k g
            (by simpa [smul_eq_mul] using hg) := by
  haveI : AlgebraicGeometry.IsClosedImmersion i := hi
  -- the hypothesis of the chart-saturation lemma, in the quotient formulation
  have hzquot : Ideal.Quotient.mk (i.ker.ideal
      ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)
          (∏ k ∈ S, MvPolynomial.X k),
        Proj.isAffineOpen_basicOpen _ (∏ k ∈ S, MvPolynomial.X k) (xS_mem_homSub S)
          (Finset.card_pos.mpr hS)⟩)
      ((Proj.basicOpenIsoAway (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)
          (∏ k ∈ S, MvPolynomial.X k) (xS_mem_homSub S) (Finset.card_pos.mpr hS)).hom z) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    rw [Work.DSEQP.chartMap_ker i hi S hS, Ideal.mem_comap] at hz
    exact hz
  -- the chart-saturation statement, in the `Proj` presentation of the charts
  obtain ⟨k, g, hg, h1, h2⟩ :=
    vanishing_ideal_chart_monomial A (N + 1) X i S hS (xS_mem_homSub S) z hzquot
  refine ⟨k, g, hg, ?_, ?_⟩
  · intro j'
    exact chartMap_basicOpen_singleton_eq_zero i (xS_mem_homSub (A := A) (N := N) {j'})
      (xS_singleton (A := A) (N := N) j') (k * S.card) g (by simpa using hg) (h1 j')
  · exact h2

end Work.DSEQP
