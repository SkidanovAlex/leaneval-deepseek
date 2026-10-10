import Mathlib
import Submission.Work.MotK.TwCensus.GoodDiscNe
import Submission.Work.MotK.TwRuling.sdRuleRankTwo
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

namespace Work.MotK.TwRuling

/-- In characteristic `5`, `D.Good` forces `b⁵ ≠ 2a⁵` (equivalently `a² - ab - b² ≠ 0`).

Route (reviewer-verified, all ingredients already in the workspace): in char 5 `b⁵ = 2a⁵` gives
`(b - 2a)⁵ = b⁵ - 2a⁵ = 0`, hence `b = 2a`.  Then `hD.klein_eq` says `kleinP a (2a) (κ) = 0`, and the
existing identity `Work.MotK.sum_kleinP_two_mul` degenerates (because `5 = 0`) to
`2 · ∑ₖ kleinP a (2a) (κ) = a² (∑ κ)²`; the left side is `0` and `a ≠ 0`, `2 ≠ 0`, so `∑ κ = 0` — a
nontrivial linear relation among the Klein coordinates, contradicting `hD.spans` (which makes
`κ` linearly independent; cf. `Work.MotK.TwCensus.GoodDiscLinIndep` and the "case 2" argument in
`Submission/Work/MotK/TwRuling/sdRuleRankTwo.lean`). -/
theorem good_bFive_ne_charFive (K : Type) [Field K] (D : Work.MotV.KleinData K) (hD : D.Good)
    (h5 : ringChar K = 5) : D.b ^ 5 ≠ 2 * D.a ^ 5 := by
  intro hb5
  haveI hchar : CharP K 5 := ringChar.eq_iff.mp h5
  have ha : D.a ≠ 0 := fun h0 => hD.ab_ne (by rw [h0, zero_mul])
  have h5K : (5 : K) = 0 := CharP.cast_eq_zero K 5
  -- in characteristic `5`, `b⁵ = 2a⁵` forces `b = 2a`
  have hba : D.b = 2 * D.a := by
    have hp5 : (D.b - 2 * D.a) ^ 5 = 0 := by
      rw [sub_two_pow_five, h5K, zero_mul, add_zero, hb5]
      first | refl_ring1 | ring
    exact sub_eq_zero.mp ((pow_eq_zero_iff (by norm_num : (5 : ℕ) ≠ 0)).mp hp5)
  -- the Klein coordinates are linearly independent
  obtain ⟨e, he⟩ := hD.spans
  have hli : LinearIndependent K (Work.MotV.kleinCoord D K) :=
    Work.MotTDG.kleinCoord_linearIndependent D K e (he K)
  have haL : algebraMap K (WeierstrassCurve.Affine.FunctionField (D.E.baseChange K)) D.a ≠ 0 := fun h0 =>
    ha (RingHom.injective (algebraMap K (WeierstrassCurve.Affine.FunctionField (D.E.baseChange K)))
      (by rw [h0, map_zero]))
  have h5F : (5 : WeierstrassCurve.Affine.FunctionField (D.E.baseChange K)) = 0 := by
    have h1 : algebraMap K (WeierstrassCurve.Affine.FunctionField (D.E.baseChange K)) (5 : K)
        = (5 : WeierstrassCurve.Affine.FunctionField (D.E.baseChange K)) := map_ofNat _ 5
    rw [← h1, h5K, map_zero]
  -- `kleinP a (2a)` vanishes at the Klein coordinates
  have hz : ∀ k : Fin 5, Work.MotK.kleinP
      (algebraMap K (WeierstrassCurve.Affine.FunctionField (D.E.baseChange K)) D.a)
      (2 * algebraMap K (WeierstrassCurve.Affine.FunctionField (D.E.baseChange K)) D.a)
      (Work.MotV.kleinCoord D K) k = 0 := by
    intro k
    have h := hD.klein_eq K k
    have hb' : algebraMap K (WeierstrassCurve.Affine.FunctionField (D.E.baseChange K)) D.b
        = 2 * algebraMap K (WeierstrassCurve.Affine.FunctionField (D.E.baseChange K)) D.a := by
      rw [hba, map_mul, map_ofNat]
    rw [hb'] at h
    exact h
  have hsum0 : (∑ k : Fin 5, Work.MotK.kleinP
      (algebraMap K (WeierstrassCurve.Affine.FunctionField (D.E.baseChange K)) D.a)
      (2 * algebraMap K (WeierstrassCurve.Affine.FunctionField (D.E.baseChange K)) D.a)
      (Work.MotV.kleinCoord D K) k) = 0 := Finset.sum_eq_zero fun k _ => hz k
  -- the degenerate identity `sum_kleinP_two_mul` gives `∑ κ = 0`
  have hsum : (∑ i : Fin 5, Work.MotV.kleinCoord D K i) = 0 := by
    have hid := sum_kleinP_two_mul
      (R := WeierstrassCurve.Affine.FunctionField (D.E.baseChange K))
      (a := algebraMap K (WeierstrassCurve.Affine.FunctionField (D.E.baseChange K)) D.a)
      (x := Work.MotV.kleinCoord D K)
    rw [hsum0, mul_zero, h5F, zero_mul, zero_mul, sub_zero] at hid
    have hsq : ((∑ i : Fin 5, Work.MotV.kleinCoord D K i)) ^ 2 = 0 :=
      (mul_eq_zero.mp hid.symm).resolve_left (pow_ne_zero 2 haL)
    exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hsq
  rw [Fintype.linearIndependent_iff] at hli
  exact one_ne_zero (hli (fun _ => 1) (by simpa using hsum) 0)

end Work.MotK.TwRuling
