import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.MotV.base_preserved
import Submission.Work.MotV.twist_natural
import Submission.Work.MotV.bridge
import Submission.Work.MotV.exponent_rigidity
import Submission.Work.MotV.tp
import Submission.Work.MotT.RouteVCorollaries
import Submission.Work.MotV.CTAux
import Submission.Work.MotV.fifthPowerValued_of_pow

set_option linter.unusedVariables false -- v435-speed

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.dupNamespace false

namespace Work.MotV

open WeierstrassCurve WeierstrassCurve.Affine
open scoped WithZero

noncomputable section

/-- **Node RIG, step 1 (V1 made explicit): the base `K = 𝕜(t)` is preserved.**

`Work.MotV.base_preserved` is applied to `F₁ := twistFieldT D (hT 𝕜)`,
`F₂ := twistFieldT D (hT 𝕜 ^ 2)`, the curves `E := D.E.baseChange (Kb 𝕜)` over `N := Kb 𝕜`
(algebraically closed, `ringChar ≠ 5`, algebraic over `K`) with the subfield inclusions
`ιᵢ : Fᵢ →+* Om D = Affine.FunctionField E`.  The hypotheses are:

* `hιᵢ`: `ιᵢ (algebraMap K Fᵢ c) = algebraMap (Kb 𝕜) _ (algebraMap K (Kb 𝕜) c)` — the two
  scalar maps agree, `IsScalarTower.algebraMap_apply` on the tower `𝕜 ⊆ K ⊆ K̄ ⊆ K̄(E)`;
* `hB₁ := Work.MotV.bridge D hD (hT 𝕜) _` (node BR), which is *exactly* the required statement
  `FifthPowerValued 𝕜 (algebraMap K F₁ (hT 𝕜))`;
* `hB₂`: base_preserved asks for `FifthPowerValued 𝕜 (algebraMap K F₂ (hT 𝕜))`, i.e. for the
  *level* `hT 𝕜` inside the twist field of `hT 𝕜 ^ 2`.  `Work.MotV.bridge D hD (hT 𝕜 ^ 2) _`
  gives fifth-power-valuedness of `algebraMap K F₂ (hT 𝕜 ^ 2) = (algebraMap K F₂ (hT 𝕜)) ^ 2`,
  and fifth-power-valuedness descends through the square `2` (coprime to `5`) by
  `Work.MotV.fifthPowerValued_of_pow (k := 2)`;
* `hRᵢ := Work.MotT.twistFieldT_regular D hD hk …` (node REG): `K` is relatively algebraically
  closed in each twist field;
* `E.IsElliptic` is preserved by base change (`WeierstrassCurve.map`). -/
theorem base_preserved_twistT {𝕜 : Type} [Field 𝕜] (D : KleinData 𝕜) (hD : D.Good)
    (hk : ringChar 𝕜 ≠ 5) (θ : twistFieldT D (hT 𝕜) ≃ₐ[𝕜] twistFieldT D (hT 𝕜 ^ 2)) :
    ∀ c : RatFunc 𝕜, ∃ d, θ (algebraMap (RatFunc 𝕜) (twistFieldT D (hT 𝕜)) c)
        = algebraMap (RatFunc 𝕜) (twistFieldT D (hT 𝕜 ^ 2)) d := by
  have hhT : hT 𝕜 ≠ 0 := hT_ne_zero 𝕜
  have hhT2 : hT 𝕜 ^ 2 ≠ 0 := pow_ne_zero 2 hhT
  have hN : ringChar (Kb 𝕜) ≠ 5 := by
    have h1 := MotT.ringChar_ratFunc_ne_five hk
    intro h5
    haveI : CharP (Kb 𝕜) 5 := ringChar.of_eq h5
    have hzero : (5 : Kb 𝕜) = 0 := CharP.cast_eq_zero (Kb 𝕜) 5
    have hk5 : (5 : RatFunc 𝕜) = 0 :=
      (algebraMap (RatFunc 𝕜) (Kb 𝕜)).injective (by rw [map_ofNat, hzero, map_zero])
    haveI : CharP (RatFunc 𝕜) 5 :=
      (CharP.charP_iff_prime_eq_zero (by norm_num : Nat.Prime 5)).mpr hk5
    exact h1 (ringChar.eq (R := RatFunc 𝕜) 5)
  haveI : (D.E.baseChange (Kb 𝕜)).IsElliptic := by
    haveI := hD.elliptic
    show (D.E.map (algebraMap 𝕜 (Kb 𝕜))).IsElliptic
    infer_instance
  have hB1 : FifthPowerValued 𝕜 (algebraMap (RatFunc 𝕜) ↥(twistFieldT D (hT 𝕜)) (hT 𝕜)) :=
    bridge D hD (hT 𝕜) hhT
  have hB2 : FifthPowerValued 𝕜 (algebraMap (RatFunc 𝕜) ↥(twistFieldT D (hT 𝕜 ^ 2)) (hT 𝕜)) :=
    fifthPowerValued_of_pow (k := 2) (by norm_num) (by
      rw [← map_pow]
      exact bridge D hD (hT 𝕜 ^ 2) hhT2)
  have hR1 : ∀ r : ↥(twistFieldT D (hT 𝕜)), IsAlgebraic (RatFunc 𝕜) r →
      ∃ c, algebraMap (RatFunc 𝕜) ↥(twistFieldT D (hT 𝕜)) c = r :=
    fun r hr => MotT.twistFieldT_regular D hD hk (hT 𝕜) hhT r hr
  have hR2 : ∀ r : ↥(twistFieldT D (hT 𝕜 ^ 2)), IsAlgebraic (RatFunc 𝕜) r →
      ∃ c, algebraMap (RatFunc 𝕜) ↥(twistFieldT D (hT 𝕜 ^ 2)) c = r :=
    fun r hr => MotT.twistFieldT_regular D hD hk (hT 𝕜 ^ 2) hhT2 r hr
  have hι1 : ∀ c : RatFunc 𝕜,
      (algebraMap ↥(twistFieldT D (hT 𝕜)) (Om D))
        (algebraMap (RatFunc 𝕜) ↥(twistFieldT D (hT 𝕜)) c)
        = (algebraMap (Kb 𝕜) (Om D)) (algebraMap (RatFunc 𝕜) (Kb 𝕜) c) :=
    fun c =>
      ((IsScalarTower.algebraMap_apply (RatFunc 𝕜) ↥(twistFieldT D (hT 𝕜)) (Om D) c).symm).trans
        (IsScalarTower.algebraMap_apply (RatFunc 𝕜) (Kb 𝕜) (Om D) c)
  have hι2 : ∀ c : RatFunc 𝕜,
      (algebraMap ↥(twistFieldT D (hT 𝕜 ^ 2)) (Om D))
        (algebraMap (RatFunc 𝕜) ↥(twistFieldT D (hT 𝕜 ^ 2)) c)
        = (algebraMap (Kb 𝕜) (Om D)) (algebraMap (RatFunc 𝕜) (Kb 𝕜) c) :=
    fun c =>
      ((IsScalarTower.algebraMap_apply (RatFunc 𝕜) ↥(twistFieldT D (hT 𝕜 ^ 2)) (Om D) c).symm).trans
        (IsScalarTower.algebraMap_apply (RatFunc 𝕜) (Kb 𝕜) (Om D) c)
  exact base_preserved (F₁ := ↥(twistFieldT D (hT 𝕜))) (F₂ := ↥(twistFieldT D (hT 𝕜 ^ 2)))
    (N := Kb 𝕜) hN (D.E.baseChange (Kb 𝕜))
    (algebraMap ↥(twistFieldT D (hT 𝕜)) (Om D))
    (algebraMap ↥(twistFieldT D (hT 𝕜 ^ 2)) (Om D)) hι1 hι2 hB1 hB2 hR1 hR2 θ

namespace Work.MotV

/-- Node RIG: the two surfaces of the link are not birational over `𝕜`, i.e. the twist fields
`F_{h}` and `F_{h²}` (`h = hT = t(t-1)`, `char 𝕜 ≠ 5`) are not `𝕜`-isomorphic.

Route (all legs are already proved; only the bookkeeping is missing).
Suppose `θ : twistFieldT D (hT 𝕜) ≃ₐ[𝕜] twistFieldT D (hT 𝕜 ^ 2)`.
1. **V1** (`Work.MotV.base_preserved`, assembled as `Work.MotV.base_preserved_twistT`) with
   `F₁ := twistFieldT D (hT 𝕜)`, `F₂ := twistFieldT D (hT 𝕜 ^ 2)`, `N := Kb 𝕜`,
   `E := D.E.baseChange (Kb 𝕜)`, `ι₁`, `ι₂` the subfield inclusions into `Work.MotV.Om D`, the
   `hιᵢ` the compatibility of the scalar maps, `hBᵢ` from `Work.MotV.bridge` (`hB₂` through the
   descent of fifth-power-valuedness along the square `2 ∤ 5`, `Work.MotV.fifthPowerValued_of_pow`)
   and `hRᵢ := Work.MotT.twistFieldT_regular D hD hk …` (node REG, proved in
   `Submission/Work/MotT/RouteVCorollaries.lean`), gives
   `∀ c : RatFunc 𝕜, ∃ d, θ (algebraMap _ F₁ c) = algebraMap _ F₂ d`.
2. **NAT** (`Work.MotV.twist_natural`) gives `α : RatFunc 𝕜 ≃ₐ[𝕜] RatFunc 𝕜` and an
   `F₁ ≃ₐ[RatFunc 𝕜] twistFieldT D (α (hT 𝕜 ^ 2))`; note `α (hT 𝕜 ^ 2) = (α (hT 𝕜)) ^ 2` and
   `α (hT 𝕜) ≠ 0`.
3. **LAM** (`Work.MotT.twistFieldT_lam D hD hk …`, proved in
   `Submission/Work/MotT/RouteVCorollaries.lean`) applied to that `RatFunc 𝕜`-linear isomorphism
   gives `ε : ℤˣ` and a nonzero `y : Fin 5 → RatFunc 𝕜` with
   `kleinTw (algebraMap 𝕜 (RatFunc 𝕜) D.a) (algebraMap 𝕜 (RatFunc 𝕜) D.b)
   (hT 𝕜 * ((α (hT 𝕜)) ^ 2) ^ (ε : ℤ)) y k = 0` for all `k`.
4. **TP** (`Work.MotV.tp`) at each `ℤᵐ⁰`-valued valuation `v` of `RatFunc 𝕜` with
   `TrivOn 𝕜 v`, with `a := algebraMap 𝕜 _ D.a`, `b := algebraMap 𝕜 _ D.b`,
   `h := hT 𝕜 * (α (hT 𝕜)) ^ (2 * (ε : ℤ))` and the point `y`: the hypotheses are `v a = v b = 1`
   (`TrivOn` plus `D.a * D.b ≠ 0`), `h ≠ 0`, `y ≠ 0` and the (rewritten) twisted Klein equations.
   This gives `FifthPowerValued 𝕜 (hT 𝕜 * (α (hT 𝕜)) ^ (2 * (ε : ℤ)))`.
5. **V4** (`Work.MotV.exponent_rigidity 𝕜 α (2 * (ε : ℤ))`) contradicts step 4, because
   `(ε : ℤ) = 1 ∨ (ε : ℤ) = -1` for `ε : ℤˣ`, so `2 * (ε : ℤ) = 2 ∨ 2 * (ε : ℤ) = -2`.

Auxiliary facts: `hT 𝕜 ≠ 0` (`Work.MotV.hT_ne_zero`), `(ε : ℤ) = ±1` for `ε : ℤˣ`
(`Int.units_eq_one_or`), and `(x²)^ε = x^(2ε)` (`zpow_mul`/`zpow_natCast`). -/
theorem rigidity {𝕜 : Type} [Field 𝕜] (D : KleinData 𝕜) (hD : D.Good) (hk : ringChar 𝕜 ≠ 5) :
    IsEmpty (twistFieldT D (hT 𝕜) ≃ₐ[𝕜] twistFieldT D (hT 𝕜 ^ 2)) := by
  refine ⟨fun θ => ?_⟩
  have hhT : hT 𝕜 ≠ 0 := hT_ne_zero 𝕜
  have hhT2 : hT 𝕜 ^ 2 ≠ 0 := pow_ne_zero 2 hhT
  -- step 1: the base `𝕜(t)` is preserved by `θ` (node V1)
  have hθ : ∀ c : RatFunc 𝕜, ∃ d, θ (algebraMap (RatFunc 𝕜) (twistFieldT D (hT 𝕜)) c)
      = algebraMap (RatFunc 𝕜) (twistFieldT D (hT 𝕜 ^ 2)) d := base_preserved_twistT D hD hk θ
  -- step 2: naturality (node NAT) reduces `θ` to a `𝕜(t)`-linear isomorphism of twists
  obtain ⟨α, ⟨θ'⟩⟩ := twist_natural D hD hk (hT 𝕜) (hT 𝕜 ^ 2) hhT hhT2 θ hθ
  have hα0 : α (hT 𝕜) ≠ 0 := by
    intro h0
    exact hhT (α.injective (by rw [h0, map_zero]))
  have hα20 : α (hT 𝕜 ^ 2) ≠ 0 := by
    intro h0
    exact hhT2 (α.injective (by rw [h0, map_zero]))
  -- step 3: the point (node LAM)
  obtain ⟨ε, y, hy, heq⟩ := MotT.twistFieldT_lam D hD hk hhT hα20 θ'
  have hexp : (α (hT 𝕜 ^ 2)) ^ ((ε : ℤ)) = (α (hT 𝕜)) ^ (2 * (ε : ℤ)) := by
    rw [map_pow, ← zpow_natCast]
    exact (zpow_mul _ _ _).symm
  -- step 4: the twisted-point valuation lemma (node TP) at every `ℤᵐ⁰`-valuation
  have hFP : FifthPowerValued 𝕜 (hT 𝕜 * (α (hT 𝕜)) ^ (2 * (ε : ℤ))) := by
    intro v hv
    have ha : v (algebraMap 𝕜 (RatFunc 𝕜) D.a) = 1 :=
      hv D.a (fun h0 => hD.ab_ne (by rw [h0, zero_mul]))
    have hb : v (algebraMap 𝕜 (RatFunc 𝕜) D.b) = 1 :=
      hv D.b (fun h0 => hD.ab_ne (by rw [h0, mul_zero]))
    have hg : hT 𝕜 * (α (hT 𝕜)) ^ (2 * (ε : ℤ)) ≠ 0 :=
      mul_ne_zero hhT (zpow_ne_zero _ hα0)
    have heq' : ∀ k, kleinTw (algebraMap 𝕜 (RatFunc 𝕜) D.a) (algebraMap 𝕜 (RatFunc 𝕜) D.b)
        (hT 𝕜 * (α (hT 𝕜)) ^ (2 * (ε : ℤ))) y k = 0 := by
      intro k
      rw [← hexp]
      exact heq k
    exact Work.MotV.tp (v := v) (a := algebraMap 𝕜 (RatFunc 𝕜) D.a)
      (b := algebraMap 𝕜 (RatFunc 𝕜) D.b)
      (h := hT 𝕜 * (α (hT 𝕜)) ^ (2 * (ε : ℤ))) (y := y) ha hb hg hy heq'
  -- step 5: the exponent count (node V4) contradicts step 4
  have hkk : (2 : ℤ) * (ε : ℤ) = 2 ∨ (2 : ℤ) * (ε : ℤ) = 3 ∨
      (2 : ℤ) * (ε : ℤ) = -2 ∨ (2 : ℤ) * (ε : ℤ) = -3 := by
    rcases Int.units_eq_one_or ε with h | h
    · left; rw [h]; norm_num
    · right; right; left; rw [h]; norm_num
  exact (exponent_rigidity 𝕜 α (2 * (ε : ℤ)) hkk) hFP

end Work.MotV

/-- `Work.MotV.rigidity`: the canonical (single-namespace) statement, definitionally equal to the
declaration `Work.MotV.Work.MotV.rigidity` above, which is kept so that the doubly nested name also
resolves (the file's header opens the namespace `Work.MotV` twice, as `base_preserved.lean` does). -/
theorem rigidity {𝕜 : Type} [Field 𝕜] (D : KleinData 𝕜) (hD : D.Good) (hk : ringChar 𝕜 ≠ 5) :
    IsEmpty (twistFieldT D (hT 𝕜) ≃ₐ[𝕜] twistFieldT D (hT 𝕜 ^ 2)) :=
  _root_.Work.MotV.Work.MotV.rigidity D hD hk

end

end Work.MotV
