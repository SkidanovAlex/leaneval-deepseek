import Mathlib
import Submission.Work.MotAS.ASZChartSetup
import Submission.Work.MotAS.TwistField
import Submission.Work.MotAS.transcendental_twistFieldAS
import Submission.Work.MotAS.transcendental_twistFieldAS_gen
import Submission.Work.MotV5.Defs
import Submission.Work.MotK.TGen.KerPhiHeightBound

set_option linter.unusedVariables false -- v435-speed

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

/-!
# `Work.MotAS.asChartPhi_height_le` — the chart of the AS twisted Klein curve is one-dimensional

Target: `(RingHom.ker (asChartPhi D (2 • fAS 𝕜))).height ≤ 4` for AS-good Klein data `D`.

Recall (`ASZChartPresentation.lean`) that
`asChartPhi D g : RatFunc 𝕜[X₀,…,X₄] →ₐ[RatFunc 𝕜] ↥(twistFieldAS D g)` is the chart evaluation
`X i ↦ y_i/y_0` on the twisted (Lagrange) coordinates of the Klein curve.  Its kernel is a prime
ideal of `K[X₀,…,X₄]` (`K = RatFunc 𝕜`) cutting out the affine chart of the twisted Klein curve,
which is a curve; since `K[X₀,…,X₄]` has Krull dimension `5`, the height is at most `4`.

## Route

The whole content is that `𝔭 := ker (asChartPhi D g)` is *not* a maximal ideal of `K[X₀,…,X₄]`:
given a maximal ideal `Q ⊋ 𝔭`, the height arithmetic
`𝔭.height + 1 ≤ Q.height ≤ ringKrullDim K[X₀,…,X₄] = 5` gives `𝔭.height ≤ 4`.

`𝔭` is not maximal because `K[X₀,…,X₄] ⧸ 𝔭` is isomorphic to the range `A` of `asChartPhi`, a
subalgebra of the twist field `F := twistFieldAS D g`.  If `𝔭` were maximal, `A` would be a
*field* which is a finitely generated `K`-algebra; Zariski's lemma
(`finite_of_finite_type_of_isJacobsonRing`) makes it finite (hence algebraic) over `K`.  The
generators `yᵢ/y₀ = asChartPhi (X i)` of `F` then generate an algebraic subfield, so `F` itself
would be algebraic over `K`, contradicting the existence of a transcendental element
(`Work.MotAS.transcendental_twistFieldAS_gen`, the general-`g` form of
`transcendental_twistFieldAS`).

The transfer "`A` algebraic over `K` ⟹ each `asChartPhi (X i)` algebraic" is done along the
`K`-algebra map `Ideal.kerLiftAlg (asChartPhi D g) : K[X₀,…,X₄] ⧸ 𝔭 →ₐ[K] ↥F` (`IsAlgebraic.algHom`)
and then along the inclusion `↥F ↪ Om D` (`IsAlgebraic.algebraMap`), where it becomes the
generator `asTwY D g i / asTwY D g 0` of the twist field by `asChartPhi_X`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.MotAS

open MvPolynomial

theorem asChartPhi_height_le (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) :
    (RingHom.ker (Work.MotAS.asChartPhi D (2 • Work.MotV.fAS 𝕜))).height ≤ 4 := by
  classical
  set g : RatFunc 𝕜 := 2 • Work.MotV.fAS 𝕜 with hgdef
  -- ## `ker (asChartPhi D g)` is not maximal
  have hnotmax : ¬ (RingHom.ker (asChartPhi D g)).IsMaximal := by
    intro hmax
    haveI : (RingHom.ker (asChartPhi D g)).IsMaximal := hmax
    -- `K[X₀,…,X₄] ⧸ 𝔭` is a field, finite (Zariski) hence algebraic over `K`
    letI : Field (MvPolynomial (Fin 5) (RatFunc 𝕜) ⧸ RingHom.ker (asChartPhi D g)) :=
      Ideal.Quotient.field _
    haveI hfin : Module.Finite (RatFunc 𝕜)
        (MvPolynomial (Fin 5) (RatFunc 𝕜) ⧸ RingHom.ker (asChartPhi D g)) :=
      finite_of_finite_type_of_isJacobsonRing (RatFunc 𝕜)
        (MvPolynomial (Fin 5) (RatFunc 𝕜) ⧸ RingHom.ker (asChartPhi D g))
    have halgQ : Algebra.IsAlgebraic (RatFunc 𝕜)
        (MvPolynomial (Fin 5) (RatFunc 𝕜) ⧸ RingHom.ker (asChartPhi D g)) :=
      Algebra.IsAlgebraic.of_finite _ _
    haveI := halgQ
    -- transport algebraicity to the generators `yᵢ/y₀` of the twist field
    have hgen : ∀ x ∈ Set.range (fun j : Fin 5 => asTwY D g j / asTwY D g 0),
        IsAlgebraic (RatFunc 𝕜) x := by
      rintro x ⟨i, rfl⟩
      have h1 : IsAlgebraic (RatFunc 𝕜)
          (Ideal.kerLiftAlg (asChartPhi D g)
            (Ideal.Quotient.mk (RingHom.ker (asChartPhi D g)) (MvPolynomial.X i))) :=
        IsAlgebraic.algHom (Ideal.kerLiftAlg (asChartPhi D g))
          (Algebra.IsAlgebraic.isAlgebraic _)
      rw [Ideal.kerLiftAlg_mk] at h1
      have h2 := IsAlgebraic.algebraMap (S := ↥(twistFieldAS D g)) (A := Work.MotV.Om D) h1
      simpa [asChartPhi_X D g i] using h2
    -- hence the twist field is algebraic over `K`, contradicting transcendence
    have halg : Algebra.IsAlgebraic (RatFunc 𝕜) ↥(twistFieldAS D g) :=
      (IntermediateField.isAlgebraic_adjoin_iff_isAlgebraic (RatFunc 𝕜)
        (Work.MotV.Om D)).mpr hgen
    obtain ⟨x, hx⟩ := transcendental_twistFieldAS_gen 𝕜 D hD g
    exact hx (halg.isAlgebraic x)
  -- ## height arithmetic
  have hPp : (RingHom.ker (asChartPhi D g)).IsPrime := RingHom.ker_isPrime _
  obtain ⟨Q, hQmax, hPQ⟩ := Ideal.exists_le_maximal _ hPp.ne_top
  haveI hQp : Q.IsPrime := hQmax.isPrime
  have hlt : RingHom.ker (asChartPhi D g) < Q :=
    lt_of_le_of_ne hPQ (fun heq => hnotmax (heq ▸ hQmax))
  have h1 : (RingHom.ker (asChartPhi D g)).height + 1 ≤ Q.height :=
    Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have h2 : Q.height ≤ (5 : ℕ∞) := by
    have hle := Ideal.height_le_ringKrullDim_of_isPrime (I := Q)
    have hdim : ringKrullDim (MvPolynomial (Fin 5) (RatFunc 𝕜)) = 5 := by
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
      norm_num
    rw [hdim] at hle
    exact WithBot.coe_le_coe.mp hle
  have h5 : (RingHom.ker (asChartPhi D g)).height + 1 ≤ (4 : ℕ∞) + 1 := by
    have : ((4 : ℕ∞) + 1) = 5 := by norm_num
    rw [this]
    exact h1.trans h2
  exact (ENat.add_le_add_iff_right (by norm_num : (1 : ℕ∞) ≠ ⊤)).mp h5

end Work.MotAS
