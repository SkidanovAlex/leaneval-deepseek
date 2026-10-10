import Mathlib
import Submission.Work.Twist.away_chart_mvPolynomial
import Submission.Work.Twist.stdGradingChart
import Submission.Work.Twist.chartAwayMapInv_comp_chartAwayMap
import Submission.Work.Twist.chartAwayMap_comp_chartAwayMapInv
import Submission.Work.Twist.chartAwayMap_fromZeroRingHom

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Twist

open MvPolynomial

noncomputable section

/-- **`RingHom.Smooth` is invariant under transporting a ring homomorphism along ring
isomorphisms of source and target.**  If the square

```
A  --f-->  B
↑eA        ↑eB
A' --f'->  B'
```

commutes, then `f` is smooth if and only if `f'` is. -/
lemma smooth_iff_of_ringEquiv_square {A B A' B' : Type*} [CommRing A] [CommRing B]
    [CommRing A'] [CommRing B']
    (f : A →+* B) (f' : A' →+* B') (eA : A' ≃+* A) (eB : B' ≃+* B)
    (h : f.comp eA.toRingHom = eB.toRingHom.comp f') : f.Smooth ↔ f'.Smooth := by
  have heA : (eA.toRingHom).Smooth := RingHom.Smooth.of_bijective eA.bijective
  have heA' : (eA.symm.toRingHom).Smooth := RingHom.Smooth.of_bijective eA.symm.bijective
  have heB : (eB.toRingHom).Smooth := RingHom.Smooth.of_bijective eB.bijective
  have heB' : (eB.symm.toRingHom).Smooth := RingHom.Smooth.of_bijective eB.symm.bijective
  have hfwd : (eB.symm.toRingHom.comp f).comp eA.toRingHom = f' := by
    ext x
    have hx : f (eA.toRingHom x) = eB.toRingHom (f' x) := RingHom.congr_fun h x
    simp only [RingHom.comp_apply]
    rw [hx]
    exact RingEquiv.symm_apply_apply eB (f' x)
  have hbwd : (eB.toRingHom.comp f').comp eA.symm.toRingHom = f := by
    ext x
    have hx : f (eA.toRingHom (eA.symm.toRingHom x)) = eB.toRingHom (f' (eA.symm.toRingHom x)) :=
      RingHom.congr_fun h (eA.symm x)
    simp only [RingHom.comp_apply]
    exact hx.symm.trans (congrArg f (RingEquiv.apply_symm_apply eA x))
  constructor
  · intro hf
    rw [← hfwd]
    exact RingHom.Smooth.comp heA (RingHom.Smooth.comp hf heB')
  · intro hf'
    rw [← hbwd]
    exact RingHom.Smooth.comp heA' (RingHom.Smooth.comp hf' heB)

/-- **Smoothness of the chart ring of `ℙⁿ` over its constants does not depend on the chart.**

`Work.Twist.stdGrading 𝕜 n` is the standard grading of `𝕜[X₀,…,Xₙ]` (`= MvPolynomial.homogeneousSubmodule
(Fin (n+1)) 𝕜`), and `HomogeneousLocalization.Away (stdGrading 𝕜 n) (X i)` is the degree-zero part
`A⁰_{X_i}` of the localisation at `X_i`, i.e. the coordinate ring of the chart `D₊(X_i)` of
`ℙⁿ = Proj 𝕜[X₀,…,Xₙ]`.  The structure map of that chart over the constants is
`fromZeroRingHom (stdGrading 𝕜 n) (Submonoid.powers (X i)) : ↥(stdGrading 𝕜 n 0) →+* A⁰_{X_i}`.
The statement below says that `RingHom.Smooth` of this structure map is the same for every chart.

Route: the standard grading is stable under permuting the variables, so for the transposition
`σ := Equiv.swap (0 : Fin (n+1)) i` the algebra equivalence `MvPolynomial.rename σ` (which is
graded, since `MvPolynomial.IsHomogeneous.rename_isHomogeneous`) induces a graded ring
endomorphism `g` of `stdGrading 𝕜 n`, hence (`HomogeneousLocalization.Away.map g`) ring
isomorphisms `A⁰_{X_i} ≃+* A⁰_{X_σ i}`.  As `σ` is an involution, the two composites are the
identities (`HomogeneousLocalization.Away.map_comp`, `Away.map_id`, `MvPolynomial.rename_rename`,
`Equiv.swap_mul_self`).  On the constants, `g` restricts to a ring automorphism `e₀` of
`↥(stdGrading 𝕜 n 0)` (whose inverse is again the restriction of `g`), and
`HomogeneousLocalization.map` commutes with `fromZeroRingHom` (`map_mk` applied to the fraction
`c / X_i ^ 0`).  `RingHom.Smooth` is invariant under pre- and post-composition with ring
isomorphisms, which gives the equivalence. -/
theorem ringHom_smooth_fromZeroRingHom_X_iff (𝕜 : Type) [Field 𝕜] (n : ℕ) (i : Fin (n + 1)) :
    RingHom.Smooth (HomogeneousLocalization.fromZeroRingHom (Work.Twist.stdGrading 𝕜 n)
        (Submonoid.powers (MvPolynomial.X i)))
      ↔ RingHom.Smooth (HomogeneousLocalization.fromZeroRingHom (Work.Twist.stdGrading 𝕜 n)
        (Submonoid.powers (MvPolynomial.X (0 : Fin (n+1))))) := by
  -- The degree-zero restriction `e₀` of the transposition is an involution of the constants,
  -- hence a ring automorphism of `↥(stdGrading 𝕜 n 0)`.
  have he0coe : ∀ a : ↥(stdGrading 𝕜 n 0),
      ((chartRename 𝕜 n i).gradedZeroRingHom a : MvPolynomial (Fin (n + 1)) 𝕜)
        = chartRename 𝕜 n i (a : MvPolynomial (Fin (n + 1)) 𝕜) := fun a => rfl
  have he0 : Function.LeftInverse (chartRename 𝕜 n i).gradedZeroRingHom
      (chartRename 𝕜 n i).gradedZeroRingHom := by
    intro a
    apply Subtype.ext
    rw [he0coe, he0coe]
    exact GradedRingHom.congr_fun (chartRename_comp_self 𝕜 n i)
      (a : MvPolynomial (Fin (n + 1)) 𝕜)
  let E0 : ↥(stdGrading 𝕜 n 0) ≃+* ↥(stdGrading 𝕜 n 0) :=
    RingEquiv.ofBijective (chartRename 𝕜 n i).gradedZeroRingHom
      ⟨Function.LeftInverse.injective he0, Function.LeftInverse.surjective he0⟩
  -- The chart ring of `D₊(X_i)` is isomorphic to that of `D₊(X₀)` through the transposition.
  have hleft : Function.LeftInverse (chartAwayMapInv 𝕜 n i) (chartAwayMap 𝕜 n i) :=
    fun x => RingHom.congr_fun (chartAwayMapInv_comp_chartAwayMap 𝕜 n i) x
  have hright : Function.LeftInverse (chartAwayMap 𝕜 n i) (chartAwayMapInv 𝕜 n i) :=
    fun x => RingHom.congr_fun (chartAwayMap_comp_chartAwayMapInv 𝕜 n i) x
  let E : HomogeneousLocalization.Away (stdGrading 𝕜 n) (MvPolynomial.X i) ≃+*
      HomogeneousLocalization.Away (stdGrading 𝕜 n) (MvPolynomial.X (0 : Fin (n+1))) :=
    RingEquiv.ofBijective (chartAwayMap 𝕜 n i) ⟨hleft.injective, hright.surjective⟩
  -- The commuting square `E ∘ φ_i = φ_0 ∘ e₀` transfers smoothness.
  refine (smooth_iff_of_ringEquiv_square
    (HomogeneousLocalization.fromZeroRingHom (stdGrading 𝕜 n)
      (Submonoid.powers (MvPolynomial.X (0 : Fin (n+1)))))
    (HomogeneousLocalization.fromZeroRingHom (stdGrading 𝕜 n)
      (Submonoid.powers (MvPolynomial.X i)))
    E0 E ?_).symm
  exact (chartAwayMap_fromZeroRingHom 𝕜 n i).symm

end

end Work.Twist
