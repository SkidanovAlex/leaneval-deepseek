import ChallengeDeps
import Submission.Work.BoseFixB3.Eps.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixB3/Conv/Q3omPairDefs`

The pair-level vocabulary of the `q3omWord`-vs-`q3convWord` comparison
(`Work.BoseFixB3.Conv.q3om_sub_q3conv_le`): every quantity in the two words is a
single ordered-pair box integral, and giving those integrals names isolates the
two *independent* layers of the comparison

* the vanishing-momentum split of the two words into ordered-pair sums
  (`q3omWord_eq_pairSum`, `q3convWord_eq_pairSum`), and
* the one-body residual estimates for `hRes` on a single ordered pair
  (`hresPairInt_abs_le`, `hresPairInt'_abs_le`),

from the arithmetic comparison of the two sums (`q3om_sub_q3conv_sum_le`,
proved in `Conv.q3om_sub_q3conv_le` together with the target).

The two words of `Work.BoseFixB3.Defs` are

  `q3omWord fc κ ℓ w₁ ω Φ = 2 Σ_{p ∈ pairSet n} ∫_{abox n ℓ} (1−f_L)_j(P_iΦ)·P_jP_iΦ·w₁(x_i,x_j)·ω(x_i−x_j)`

and

  `q3convWord fc κ ℓ I Φ = I ℓ⁻³ Σ_{i,j} ∫_{abox n ℓ} P_iΦ·(1−f_L)_j(χ_Λ²P_jΦ)`,

so that

* `omPairInt fc κ ℓ w₁ ω i j Φ` is the ordered-pair integral of `q3omWord`;
* `omPairIntχ fc κ ℓ f i j Φ` is the same integral with the pair kernel written in
  FS's localised form `χ_ℓ(x_i)·f(x_i−x_j)·χ_ℓ(x_j)`, which is the form in which
  FS `lem:Convolution` produces its bound (`f = convKernel ℓ v h = W₁·ω`, so that
  `I = ∫ f` is FS's convolution constant `Work.BoseFixB3.convI`);
* `hresPairInt fc κ ℓ i j Φ` is the residual pairing that `lem:Convolution` leaves
  behind in `q3omWord`, and `hresPairInt' fc κ ℓ i j Φ` the one belonging to
  `q3convWord` (the two differ only by `P_jP_iΦ` versus `P_jΦ`, which is where the
  `|hRes| ≤ B` hypothesis of the target enters);
* both are the fibre-collapsed form of `Eps.highSlot_chiSq_aP_eq`.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixB3.Conv

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseKinLoc
open Work.BoseBoxFix

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The ordered-pair integral of `Work.BoseFixB3.q3omWord`. -/
def omPairInt (fc : LowCut) (κ ℓ : ℝ)
    (w1 ω : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    {n : ℕ} (i j : Fin n) (Φ : X n → ℝ) : ℝ :=
  ∫ x in abox n ℓ, highSlot fc κ ℓ j (aP ℓ i Φ) x * aP ℓ j (aP ℓ i Φ) x
      * w1 (x i) (x j) * ω (x i) (x j)

/-- The ordered-pair integral of `q3omWord` with the pair kernel in FS's localised
form `χ_ℓ(x_i)·f(x_i−x_j)·χ_ℓ(x_j)` (the form produced by `lem:Convolution`). -/
def omPairIntχ (fc : LowCut) (κ ℓ : ℝ) (f : EuclideanSpace ℝ (Fin 3) → ℝ) {n : ℕ}
    (i j : Fin n) (Φ : X n → ℝ) : ℝ :=
  ∫ x in abox n ℓ, highSlot fc κ ℓ j (aP ℓ i Φ) x * aP ℓ j (aP ℓ i Φ) x
      * (chiScale ℓ (x i) * f (x i - x j) * chiScale ℓ (x j))

/-- The convolution kernel `f = W₁·ω` of FS `lem:Convolution`
(`W₁ = wScaled ℓ (g₀ v h)`, `ω = Classical.choose h`), so that `I = ∫ f`. -/
def convKernel (ℓ : ℝ) (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : ScatSol v) :
    EuclideanSpace ℝ (Fin 3) → ℝ :=
  fun z => wScaled ℓ (g0 v h) z * Classical.choose h z

/-- The residual one-body pairing of `q3omWord` in the form left by
`lem:Convolution`: `∫ P_iΦ·(P_jP_iΦ·hRes)`. -/
def hresPairInt (fc : LowCut) (κ ℓ : ℝ) {n : ℕ} (i j : Fin n) (Φ : X n → ℝ) : ℝ :=
  ∫ x in abox n ℓ, aP ℓ i Φ x * (aP ℓ j (aP ℓ i Φ) x * Eps.hRes fc κ ℓ (x j))

/-- The residual one-body pairing of `q3convWord`: `∫ P_iΦ·(P_jΦ·hRes)`. -/
def hresPairInt' (fc : LowCut) (κ ℓ : ℝ) {n : ℕ} (i j : Fin n) (Φ : X n → ℝ) : ℝ :=
  ∫ x in abox n ℓ, aP ℓ i Φ x * (aP ℓ j Φ x * Eps.hRes fc κ ℓ (x j))

end Work.BoseFixB3.Conv
