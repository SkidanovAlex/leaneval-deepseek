import Mathlib
import Submission.Work.Twist.stdGradingChart

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `chartAwayMap` commutes with the structure maps `fromZeroRingHom`

`Work.Twist.chartAwayMap 𝕜 n i : A⁰_{X_i} →+* A⁰_{X_0}` is induced by the coordinate transposition
`X₀ ↔ X_i` (`HomogeneousLocalization.map` along the graded ring endomorphism
`chartRename 𝕜 n i`).  Since that endomorphism is a *graded* ring endomorphism, it restricts to
the degree-zero part `𝒜 0`, and the induced map on the homogeneous localisations commutes with the
canonical maps `fromZeroRingHom` out of `𝒜 0`; this is the content of the present file.

The general form is proved once, for an arbitrary graded ring homomorphism `g : 𝒜 →+*ᵍ ℬ` and
arbitrary submonoids `P ≤ Q.comap g`
(`Work.Twist.HomogeneousLocalization.map_fromZeroRingHom`), and then specialised.
-/

set_option autoImplicit false

namespace Work.Twist

open MvPolynomial HomogeneousLocalization

noncomputable section

/-- **`HomogeneousLocalization.map` commutes with `fromZeroRingHom`.**  If `g : 𝒜 →+*ᵍ ℬ` is a
graded ring homomorphism and `P ≤ Q.comap g`, then the induced map
`HomogeneousLocalization 𝒜 P →+* HomogeneousLocalization ℬ Q` intertwines the structure maps from
the degree-zero parts along the degree-zero restriction `g.gradedZeroRingHom`:
`a / 1 ↦ (g a) / 1`. -/
lemma HomogeneousLocalization.map_fromZeroRingHom {ι A σ : Type*} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] [AddCommMonoid ι] [DecidableEq ι] {𝒜 : ι → σ} [GradedRing 𝒜]
    {B τ : Type*} [CommRing B] [SetLike τ B] [AddSubgroupClass τ B] {ℬ : ι → τ} [GradedRing ℬ]
    {P : Submonoid A} {Q : Submonoid B} (g : 𝒜 →+*ᵍ ℬ) (h : P ≤ Q.comap g) (a : 𝒜 0) :
    HomogeneousLocalization.map g h (HomogeneousLocalization.fromZeroRingHom 𝒜 P a) =
      HomogeneousLocalization.fromZeroRingHom ℬ Q (g.gradedZeroRingHom a) := by
  rw [show (HomogeneousLocalization.fromZeroRingHom 𝒜 P) a
      = HomogeneousLocalization.mk (HomogeneousLocalization.NumDenSameDeg.mk 0 a 1 (one_mem P))
      from rfl]
  rw [HomogeneousLocalization.map_mk]
  rw [show (HomogeneousLocalization.fromZeroRingHom ℬ Q) (g.gradedZeroRingHom a)
      = HomogeneousLocalization.mk
        (HomogeneousLocalization.NumDenSameDeg.mk 0 (g.gradedZeroRingHom a) 1 (one_mem Q))
      from rfl]
  congr 1
  exact HomogeneousLocalization.NumDenSameDeg.ext Q rfl rfl (map_one g)

/-- The two structure maps `𝒜 0 →+* A⁰_{X_0}` obtained from `chartAwayMap 𝕜 n i` and from the
degree-zero part of the coordinate transposition `chartRename 𝕜 n i` agree. -/
theorem chartAwayMap_fromZeroRingHom (𝕜 : Type) [Field 𝕜] (n : ℕ)
    (i : Fin (n + 1)) :
    (Work.Twist.chartAwayMap 𝕜 n i).comp
        (HomogeneousLocalization.fromZeroRingHom (Work.Twist.stdGrading 𝕜 n)
          (Submonoid.powers (MvPolynomial.X i))) =
      (HomogeneousLocalization.fromZeroRingHom (Work.Twist.stdGrading 𝕜 n)
          (Submonoid.powers (MvPolynomial.X (0 : Fin (n + 1))))).comp
        (Work.Twist.chartRename 𝕜 n i).gradedZeroRingHom := by
  refine RingHom.ext fun a => ?_
  simp only [RingHom.comp_apply]
  rw [show Work.Twist.chartAwayMap 𝕜 n i
        = HomogeneousLocalization.map (Work.Twist.chartRename 𝕜 n i) _ from rfl]
  exact HomogeneousLocalization.map_fromZeroRingHom (Work.Twist.chartRename 𝕜 n i) _ a

end

end Work.Twist
