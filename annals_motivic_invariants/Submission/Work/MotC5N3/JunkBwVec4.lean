import Mathlib
import Submission.Work.MotC5N3.Defs
import Submission.Work.MotC5N3.AK
import Submission.Work.MotC5N3.CensusAux
-- The two ingredients (`bwASpoly_prime`, `bwASpoly_fractionRing`) come from the local fork
-- `Submission/Work/MotC5N3/BwAS/` of `MotV5/ASLocal/{BwASpolyFracRing,JunkBwVec4}.lean`.  The fork
-- exists because `MotV5/ASLocal/BwASpolyFracRing` declares `Work.MotV5.ASLocal.asQ2`, which
-- *clashes* with the `asQ2` of `MotV5/ASLocal/asRhoPoly_witPt_data` (in the closure of
-- `Work.MotC5N3.censusAS2_class_sdual`): any module importing both fails to elaborate.  The two
-- declarations used here only need the namespaces of `BwASDefs`/`MotK`, so the fork renames the
-- two files into `Work.MotC5N3.BwAS` (and `asQ2 ↦ bwASQ2`) without touching anything else.
import Submission.Work.MotC5N3.BwAS.JunkBwVec4

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC5N3

/-- **The `bwVecAS2 · 4` junk conjunct of the generic AS census** (the conjunct `hBw`): every
height-one prime of `K[Fin 3]` containing the inverse chart denominator
`bwVecAS2 (aK K D) (bK K D) g 4` is a junk class (`Work.MotV.JunkClass K x`).

Fork (through `Submission/Work/MotC5N3/BwAS/`) of `Work.MotV5.ASLocal.JunkBwVec4` (WP5, LK-4 of `MOTIVIC_CHAR5_N3_LEAD.md` §6, 473 lines),
whose base field is `RatFunc 𝕜`, whose coordinates are `Work.MotAS.aK D`, `Work.MotAS.bK D` and
whose class is `Work.MotV.fAS 𝕜`.  Here `K` is an arbitrary `𝕜`-algebra field of characteristic `5`,
the class is an arbitrary `g ∉ ℘(K)`, the coordinates are `Work.MotC5N3.aK K D`,
`Work.MotC5N3.bK K D` and the twist field is `Work.MotC5N3.twistFieldAS D g`.

`bwVecAS2 a b g 4` equals `kleinRAS (C a) (C b) (C g) (tchart K) 4` (the projection `π_{e₀}`
changes only the zeroth coordinate, cf. `bwVecAS2_four_eq` in
`Submission/Work/MotAS/CensusAS2Aux.lean`), a cubic form in the three chart variables whose
residue-field class is computed by the degree argument of the source module: fork
`Submission/Work/MotV5/ASLocal/JunkBwVec4.lean` into namespace `Work.MotC5N3` with
`RatFunc 𝕜 ↦ K`, `Work.MotV.fAS 𝕜 ↦ g`, `Work.MotAS.aK D, Work.MotAS.bK D ↦ Work.MotC5N3.aK K D,
Work.MotC5N3.bK K D`.  The chain it uses is already generic in `(a b g : K)`:
`Work.MotAS.BwASDefs.bwVecAS2_four_eq_bwASpoly` (`[CommRing K]`),
`Work.MotAS.bwASpoly_prime` and `Work.MotAS.bwASpoly_fractionRing`
(`{K} [Field K] [CharP K 5] (a b g : K)` with `asDel a b ≠ 0`, `g ≠ 0`; its conclusion is
`resF K x ≃ₐ[K] RatFunc (RatFunc K)`), `Work.MotAS.CensusPrime.eq_span_of_height_one` and the
generic `Work.MotK.junkClass_of_resF_ratFunc_ratFunc`.  `hg` gives `g ≠ 0` (take `u = 0`) and `hD`
gives `aK K D ^ 2 - aK K D * bK K D - bK K D ^ 2 ≠ 0` (`Work.MotC5N3.aK_sq_sub_ne`).
`Submission/Work/MotC5N3/port.py` performs the textual port.

Deliverable: namespace `Work.MotC5N3`, file `Submission/Work/MotC5N3/JunkBwVec4.lean` (helpers in
sibling files), sorry-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`). -/
theorem JunkBwVec4 (K : Type) [Field K] [CharP K 5] {𝕜 : Type} [Field 𝕜] [Algebra 𝕜 K]
    (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) (g : K)
    (hg : ¬ ∃ u : K, u ^ 5 - u = g) :
    ∀ x : Work.MotA.polySpec K 3, Order.coheight x = 1 →
      Work.MotAS.bwVecAS2 (Work.MotC5N3.aK K D) (Work.MotC5N3.bK K D) g 4 ∈ x.asIdeal →
        Work.MotV.JunkClass K x := by
  intro x hcoh hmem
  -- `d = a² - ab - b²` does not vanish on `ASGood D`
  have hd : Work.MotAS.asDel (aK K D) (bK K D) ≠ 0 := aK_sq_sub_ne D hD
  -- `g ∉ ℘(K)` in particular gives `g ≠ 0` (take `u = 0`)
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact hg ⟨0, by ring⟩
  -- the cubic `bwASpoly a b g` is prime
  have hprime : Prime (Work.MotAS.bwASpoly (aK K D) (bK K D) g) :=
    Work.MotC5N3.BwAS.bwASpoly_prime _ _ _ hd hg0
  have hspan : (Ideal.span {Work.MotAS.bwASpoly (aK K D) (bK K D) g} :
      Ideal (MvPolynomial (Fin 3) K)).IsPrime :=
    (Ideal.span_singleton_prime hprime.ne_zero).mpr hprime
  have hheight : Ideal.height (Ideal.span {Work.MotAS.bwASpoly (aK K D) (bK K D) g} :
      Ideal (MvPolynomial (Fin 3) K)) = 1 :=
    Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr hprime.ne_zero) hprime.not_isUnit
  -- rewrite the target chart denominator as the explicit cubic
  have hmem' : Work.MotAS.bwASpoly (aK K D) (bK K D) g ∈ x.asIdeal := by
    rw [← Work.MotAS.bwVecAS2_four_eq_bwASpoly (aK K D) (bK K D) g]
    exact hmem
  -- a height-one prime containing it is exactly the principal prime it generates
  have hx : x.asIdeal = Ideal.span {Work.MotAS.bwASpoly (aK K D) (bK K D) g} := by
    haveI : x.asIdeal.IsPrime := x.isPrime
    exact Work.MotK.CensusPrime.eq_span_of_height_one _ hspan hheight x.asIdeal
      (by rw [AlgebraicGeometry.idealHeight_eq_coheight]; exact hcoh) hmem'
  have hxe : x = ⟨Ideal.span {Work.MotAS.bwASpoly (aK K D) (bK K D) g}, hspan⟩ :=
    PrimeSpectrum.ext hx
  rw [hxe]
  -- the residue field of that prime is the rational surface `K(t)(z)`, hence junk
  exact Work.MotK.junkClass_of_resF_ratFunc_ratFunc K _
    (Work.MotC5N3.BwAS.bwASpoly_fractionRing (aK K D) (bK K D) g hd hg0 hspan)

end Work.MotC5N3
