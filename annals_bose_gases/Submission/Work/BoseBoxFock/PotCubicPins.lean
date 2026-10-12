import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.BombPairAux
import Submission.Work.MB.SlotWeakBase
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock` — the pinned representatives of the honest modes

The honest mode bundle `e : Fin m → Ω → ℂ` is pinned by the three pairings of
`Work.BoseBoxFock.PotCubic`'s context:

* `∫ conj (e l) · qVec(kmomLab k) = ℓ^{3/2}·f k l` — with the Bessel equality `HonestModes.hphys`
  this forces `η_{f k} := Σ_l (f k l)·e_l =ᵐ ℓ^{-3/2} qVec(kmomLab k)`
  (`Work.BoseBoxFock.qVec_eq_etaOf_of_pairing`);
* `∫ conj (e l) · thetaExp(kmomLab s) = ℓ^{3/2}·g s l` (`s ≠ 0`) — likewise
  `η_{g s} =ᵐ ℓ^{-3/2} thetaExp(kmomLab s)`
  (`Work.BoseBoxFock.thetaExp_eq_etaOf_of_pairing`);
* `e 0 =ᵐ c·thetaFun` with `c̄c = ℓ^{-3}` — and `η_{evec0} = e 0`
  (`evec0 m = Pi.single 0 1`), so `η_{evec0} =ᵐ c·thetaFun`.

This module names the three pinned *functions* (with the exact scalar `(√ℓ³)⁻¹` and the box side
`ellH v μ` of the honest data), so that the row statements can be phrased in terms of them:

    pinQ v μ N k x      = (√(ℓ³))⁻¹ · qVec ℓ (kmomLab ℓ N k) x
    pinTheta v μ N s x  = (√(ℓ³))⁻¹ · thetaExp ℓ (kmomLab ℓ N s) x
    pinCond v μ c x     = c · thetaFun ℓ x

(`ℓ := ellH v μ`.)  The companion `_etaOf` lemmas — that `etaOf e (f k)`, `etaOf e (g s)`
(`s ≠ 0`) and `etaOf e (evec0 m)` are a.e. these — are the instantiation step of the cubic row
(`Work.BoseBoxFock.potCubic_cIPn_pinned`).
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-- The pinned representative of the `f`-modes: `(√ℓ³)⁻¹ qVec(ℓ, kmomLab ℓ N k)` at the box side
`ℓ = ellH v μ`. -/
noncomputable def pinQ (v : Ω → ℝ) (μ : ℝ) (N : ℕ) (k : Lab N) : Ω → ℂ :=
  fun x => (((Real.sqrt ((ellH v μ) ^ 3))⁻¹ : ℝ) : ℂ) *
    Work.BoseK15.corpusBox.qVec (ellH v μ) (kmomLab (ellH v μ) N k) x

/-- The pinned representative of the `g`-modes: `(√ℓ³)⁻¹ thetaExp(ℓ, kmomLab ℓ N s)`. -/
noncomputable def pinTheta (v : Ω → ℝ) (μ : ℝ) (N : ℕ) (s : Lab N) : Ω → ℂ :=
  fun x => (((Real.sqrt ((ellH v μ) ^ 3))⁻¹ : ℝ) : ℂ) *
    Work.BoseK15.corpusBox.thetaExp (ellH v μ) (kmomLab (ellH v μ) N s) x

/-- The pinned representative of the condensate mode: `c·thetaFun ℓ`. -/
noncomputable def pinCond (v : Ω → ℝ) (μ : ℝ) (c : ℂ) : Ω → ℂ :=
  fun x => c * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x

/-- The condensate pin in the `pinCond` vocabulary. -/
theorem etaOf_evec0_eq_pinCond {m : ℕ} [NeZero m] {e : Fin m → Ω → ℂ}
    {v : Ω → ℝ} {μ : ℝ} {c : ℂ}
    (h : e 0 =ᵐ[volume] pinCond v μ c) :
    Work.BoseDict.etaOf e (evec0 m) =ᵐ[volume] pinCond v μ c := by
  rw [etaOf_evec0]
  exact h

end Work.BoseBoxFock
