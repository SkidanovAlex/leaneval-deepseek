import Mathlib
import Submission.Work.MotK.TGen.ChartSetup
import Submission.Work.MotK.TwCensus.TwistFieldTGTrdeg

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.KerPhiHeightBound`: the chart of the twisted Klein curve is one-dimensional

Target: `(RingHom.ker (chartPhi K D H)).height ≤ 4` for good Klein data `D` and `H ≠ 0`.

Recall (`ChartSetup.lean`) that `chartPhi K D H : MvPolynomial (Fin 5) K →ₐ[K] ↥(twistFieldTG K D H)`
is the chart evaluation `X i ↦ w^{-i}·κᵢ/κ₀`.  Its kernel is a prime ideal of `K[x₀,…,x₄]` cutting
out the affine chart of the twisted Klein curve, which is one-dimensional; since
`K[x₀,…,x₄]` has Krull dimension `5`, the height is at most `4`.

## Route

The whole content is that `𝔭 := ker (chartPhi K D H)` is *not* a maximal ideal of
`K[x₀,…,x₄]`: given a maximal ideal `Q ⊋ 𝔭`, the height arithmetic
`𝔭.height + 1 ≤ Q.height ≤ ringKrullDim K[x₀,…,x₄] = 5` gives `𝔭.height ≤ 4`.

`𝔭` is not maximal because `K[x₀,…,x₄] ⧸ 𝔭` is isomorphic to the range `A` of `chartPhi`, a
subalgebra of the twist field `F := twistFieldTG K D H = K(y₀,…,y₄)`.  If `𝔭` were maximal, `A`
would be a *field* which is a finitely generated `K`-algebra; Zariski's lemma
(`finite_of_finite_type_of_isJacobsonRing`) makes it finite (hence algebraic) over `K`.  Then every
generator `yᵢ = chartPhi (X i)` of `F` is algebraic over `K`, so `F` itself is algebraic over `K`
(`IntermediateField.isAlgebraic_adjoin_iff_isAlgebraic`), contradicting
`TwistFieldTGTrdeg : trdeg_K F = 1`.

The transfer "`A` algebraic over `K` ⟹ each `chartPhi (X i)` algebraic" is done along the
`K`-algebra map `Ideal.kerLiftAlg (chartPhi K D H) : K[x₀,…,x₄] ⧸ 𝔭 →ₐ[K] F` (`IsAlgebraic.algHom`)
and then along the inclusion `F ↪ K̄(E)` (`IsAlgebraic.algebraMap`), where it becomes the generator
`twCoordG K D H i` of the twist field by `chartPhi_X`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Work.MotK.TGen

open MvPolynomial

theorem KerPhiHeightBound (K : Type) [Field K] (D : Work.MotV.KleinData K) (hD : D.Good) (H : K) (hH : H ≠ 0) : (RingHom.ker (Work.MotK.TGen.chartPhi K D H)).height ≤ 4 := by
  classical
  have hPp : (RingHom.ker (Work.MotK.TGen.chartPhi K D H)).IsPrime := RingHom.ker_isPrime _
  -- ## `ker (chartPhi)` is not maximal
  have hnotmax : ¬ (RingHom.ker (Work.MotK.TGen.chartPhi K D H)).IsMaximal := by
    intro hmax
    haveI : (RingHom.ker (Work.MotK.TGen.chartPhi K D H)).IsMaximal := hmax
    -- `K[x₀,…,x₄] ⧸ 𝔭` is a field, finite (Zariski) hence algebraic over `K`
    letI : Field (MvPolynomial (Fin 5) K ⧸ RingHom.ker (Work.MotK.TGen.chartPhi K D H)) :=
      Ideal.Quotient.field _
    have hfin := finite_of_finite_type_of_isJacobsonRing K
      (MvPolynomial (Fin 5) K ⧸ RingHom.ker (Work.MotK.TGen.chartPhi K D H))
    have halgQ : Algebra.IsAlgebraic K
        (MvPolynomial (Fin 5) K ⧸ RingHom.ker (Work.MotK.TGen.chartPhi K D H)) :=
      Algebra.IsAlgebraic.of_finite K _
    haveI := halgQ
    -- transport algebraicity to the generators `yᵢ = chartPhi (X i)` of the twist field
    have hgen : ∀ x ∈ Set.range (Work.MotK.twCoordG K D H), IsAlgebraic K x := by
      rintro x ⟨i, rfl⟩
      have h1 : IsAlgebraic K (Ideal.kerLiftAlg (Work.MotK.TGen.chartPhi K D H)
          (Ideal.Quotient.mk (RingHom.ker (Work.MotK.TGen.chartPhi K D H))
            (MvPolynomial.X i))) :=
        IsAlgebraic.algHom (Ideal.kerLiftAlg (Work.MotK.TGen.chartPhi K D H))
          (Algebra.IsAlgebraic.isAlgebraic _)
      rw [Ideal.kerLiftAlg_mk] at h1
      have h2 := IsAlgebraic.algebraMap (A := Work.MotK.OmG K D) h1
      simpa [Work.MotK.TGen.chartPhi_X K D H i] using h2
    -- hence the twist field is algebraic over `K`, contradicting `trdeg_K F = 1`
    have halg : Algebra.IsAlgebraic K ↥(Work.MotK.twistFieldTG K D H) :=
      (IntermediateField.isAlgebraic_adjoin_iff_isAlgebraic K (Work.MotK.OmG K D)).mpr hgen
    haveI := halg
    have h0 : Algebra.trdeg K ↥(Work.MotK.twistFieldTG K D H) = 0 := trdeg_eq_zero
    have h1 := Work.MotK.TwCensus.TwistFieldTGTrdeg K D hD H hH
    rw [h0] at h1
    exact zero_ne_one h1
  -- ## height arithmetic
  obtain ⟨Q, hQmax, hPQ⟩ := Ideal.exists_le_maximal _ hPp.ne_top
  haveI hQp : Q.IsPrime := hQmax.isPrime
  have hlt : RingHom.ker (Work.MotK.TGen.chartPhi K D H) < Q :=
    lt_of_le_of_ne hPQ (fun heq => hnotmax (heq ▸ hQmax))
  have h1 : (RingHom.ker (Work.MotK.TGen.chartPhi K D H)).height + 1 ≤ Q.height :=
    Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have h2 : Q.height ≤ (5 : ℕ∞) := by
    have hle := Ideal.height_le_ringKrullDim_of_isPrime (I := Q)
    have hdim : ringKrullDim (MvPolynomial (Fin 5) K) = 5 := by
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
      norm_num
    rw [hdim] at hle
    exact WithBot.coe_le_coe.mp hle
  have h5 : (RingHom.ker (Work.MotK.TGen.chartPhi K D H)).height + 1 ≤ (4 : ℕ∞) + 1 := by
    have : ((4 : ℕ∞) + 1) = 5 := by norm_num
    rw [this]
    exact h1.trans h2
  exact (ENat.add_le_add_iff_right (by norm_num : (1 : ℕ∞) ≠ ⊤)).mp h5

end Work.MotK.TGen
