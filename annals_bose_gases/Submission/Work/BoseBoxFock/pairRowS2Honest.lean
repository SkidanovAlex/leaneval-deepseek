import ChallengeDeps
import Submission.Work.BoseBoxFock.pinQLimDefs
import Submission.Work.BoseFixR.Rb5Lin.W1Facts
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pairRowS2Honest` — the *weight identities* of the `Q₂` row at the honest data

The (S2) step of the `Q₂` row compares the row at the truncated pair kernel `K1exp` with the row at
the limit kernel `K1lim` (`Work.BoseBoxFock.rowPairSubC_Ksub`).  The crux
`Work.BoseBoxFock.K1exp_sub_K1lim_pairing_le` is stated for a **sum** of two weights `Wa + Wb`, while
the honest data supplies the two weights separately:

* block I carries `E.W1 k + E.W1omega k`, i.e. the weights `W1fun v h ℓ` and `W1omegaFun v h ℓ`;
* block II carries `E.W1 k` alone.

This file records the algebraic fact that makes the two spellings the same:

    `W1fun v h ℓ + W1omegaFun v h ℓ = wScaled ℓ (g2 v h)`   (pointwise),

which follows from `g2 = g0·(1+ω) = g0 + g0·ω` and the additivity of `wScaled ℓ` (a common
denominator `convScale ℓ`).  Everything is `sorry`-free.

⚠ **Recorded obstruction (read `FINDING_PotPairRows_exists.md` §9).**  These identities are the
*algebraic* half of the (S2) step and are unconditional.  The *analytic* half — the crux
`K1exp_sub_K1lim_pairing_le` and its whole support chain (`errA_sq_int_le`, `k1RowSum_L2`,
`latRowSum_tendsto_L2`, `latFourier_tendsto_periodisation`) — is stated for **bounded** weights
(`∃ C, ∀ x, ‖W x‖ ≤ C`) and uses the boundedness essentially (it derives
`Σ_{k∈ℤ³}‖chat W k‖² < ∞`, i.e. `W ∈ L²`, and the boundedness of the periodisation).  The node's
hypotheses give only `hv1 : MemLp v 1`, so `W1fun ≤ᵃᵉ 3 g₀ ≤ᵃᵉ 3 v` need not be bounded (nor in
`L²`).  The (S2) chain is therefore **not instantiable at the honest weights** as recorded; see
§9.2/§9.3 of the FINDING for the two repairs.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. `wScaled` is additive in its numerator -/

/-- `wScaled ℓ h = h / convScale ℓ` is additive in the numerator (the denominator is common). -/
theorem wScaled_add' {ℓ : ℝ} (h₁ h₂ : E3 → ℝ) (x : E3) :
    Submission.BoseGases.wScaled ℓ (fun z => h₁ z + h₂ z) x
      = Submission.BoseGases.wScaled ℓ h₁ x + Submission.BoseGases.wScaled ℓ h₂ x := by
  simp only [Submission.BoseGases.wScaled]
  ring

/-! ## 2. `g₂ = g₀ + g₀ω` -/

/-- `g₂ = g₀(1+ω) = g₀ + g₀·ω` (`ω = Classical.choose h`, the scattering solution). -/
theorem g2_eq_g0_add_g0ω {v : E3 → ℝ} {h : Work.UBB.ScatSol v} :
    Submission.BoseGases.g2 v h
      = fun z => Submission.BoseGases.g0 v h z
          + Submission.BoseGases.g0 v h z * Classical.choose h z := by
  funext x
  simp only [Submission.BoseGases.g2, Submission.BoseGases.g0]
  ring

/-! ## 3. The weight identity of block I -/

/-- **The §8.3 identity**: `W1fun + W1omegaFun = wScaled ℓ (g₂)`, pointwise.  This is what lets
the crux `K1exp_sub_K1lim_pairing_le` (stated for a *sum* `Wa + Wb`) be applied at the honest data
(`Wa = W1fun`, `Wb = W1omegaFun`), with the limit kernel `K1lim ℓ (wScaled ℓ (g₂))` of block I. -/
theorem W1fun_add_W1omegaFun {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {ℓ : ℝ} (z : E3) :
    Work.BoseFixR.W1fun v h ℓ z + Work.BoseFixR.W1omegaFun v h ℓ z
      = Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g2 v h) z := by
  simp only [Work.BoseFixR.W1fun, Work.BoseFixR.W1omegaFun, Submission.BoseGases.wScaled,
    Submission.BoseGases.g2, Submission.BoseGases.g0]
  ring_nf

/-- The same identity as an equality of functions. -/
theorem W1fun_add_W1omegaFun_fun {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {ℓ : ℝ} :
    (fun z => Work.BoseFixR.W1fun v h ℓ z + Work.BoseFixR.W1omegaFun v h ℓ z)
      = Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g2 v h) :=
  funext fun z => W1fun_add_W1omegaFun z

/-- **The limit kernel of block I is the limit kernel at the `g₂`-weight** (no `a.e.` needed: the
two weights are *equal*). -/
theorem K1lim_blockI_eq (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (ℓ : ℝ) :
    K1lim ℓ (fun z => Work.BoseFixR.W1fun v h ℓ z + Work.BoseFixR.W1omegaFun v h ℓ z)
      = K1lim ℓ (Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g2 v h)) := by
  rw [W1fun_add_W1omegaFun_fun]

/-! ## 4. The limit kernel of block II -/

/-- Block II's weight is `W1fun v h ℓ = wScaled ℓ (g₀ v h)`, definitionally. -/
theorem W1fun_eq_wScaled (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (ℓ : ℝ) :
    Work.BoseFixR.W1fun v h ℓ = Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h) :=
  rfl

end Work.BoseBoxFock
