import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Submission.Work.BoseFixR.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.Rb5Lin.W1Facts` — the basic structure of `W₁ = wScaled ℓ (g₀)`

Two structural facts about `W1fun v h ℓ = g₀/(χ⋆χ)(·/ℓ)`, with `g₀ = v(1−w₀)` and `w₀` the
chosen radial scattering solution:

* **evenness**: `v` is radial (hence even) by hypothesis, `w₀` is radial by `Work.UBB.ScatSol`,
  and `χ⋆χ` is even (`Submission.BoseGases.conv3chi_even`), so `W₁` is even;
* **support**: `tsupport (W1fun v h ℓ) ⊆ ball 0 R`, because `g₀ = v·(1−w₀)` vanishes off
  `supp v` and total division cannot enlarge the support.

Note (contrast with the radial case): the corpus's bump `χ` is `Classical.choice`-based, so
`IsRadial χ` — and hence `IsRadial (convScale ℓ)` and `IsRadial (W1fun v h ℓ)` — is *not*
available; only evenness is.  The consumers use exactly this (see
`Submission/Work/ESYRound8/Dict/wScaled_radial.lean`, where `IsRadial (convScale ℓ)` is an
explicit hypothesis).
-/

noncomputable section

open MeasureTheory Metric
open scoped Topology Real

namespace Work.BoseFixR

/-! ## 1. Evenness -/

theorem isEven_g0 {v : ℝ³ → ℝ} (h : Work.UBB.ScatSol v) (hvrad : BoseGases.IsRadial v) :
    ∀ x, Submission.BoseGases.g0 v h (-x) = Submission.BoseGases.g0 v h x := by
  have hw : ∀ y, Classical.choose h (-y) = Classical.choose h y :=
    fun y => (Submission.BoseGases.w0_spec h).1 (-y) y (by simp)
  have hv : ∀ y, v (-y) = v y := fun y => hvrad (-y) y (by simp)
  intro x
  simp only [Submission.BoseGases.g0, hv x, hw x]

theorem isEven_convScale (ℓ : ℝ) :
    ∀ x, Submission.BoseGases.convScale ℓ (-x) = Submission.BoseGases.convScale ℓ x := by
  intro x
  simp only [Submission.BoseGases.convScale, smul_neg]
  rw [Submission.BoseGases.conv3chi_even]

theorem isEven_W1fun {v : ℝ³ → ℝ} (h : Work.UBB.ScatSol v) (hvrad : BoseGases.IsRadial v)
    (ℓ : ℝ) : ∀ x, W1fun v h ℓ (-x) = W1fun v h ℓ x := by
  have hg := isEven_g0 h hvrad
  have hc := isEven_convScale ℓ
  intro x
  simp only [W1fun, Submission.BoseGases.wScaled, hg x, hc x]

/-! ## 2. Support -/

theorem support_W1fun_subset {v : ℝ³ → ℝ} (h : Work.UBB.ScatSol v) (ℓ : ℝ) :
    Function.support (W1fun v h ℓ) ⊆ Function.support v := by
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  intro hvx
  exact hx (by simp [W1fun, Submission.BoseGases.wScaled, Submission.BoseGases.g0, hvx])

theorem tsupport_W1fun_subset {v : ℝ³ → ℝ} (h : Work.UBB.ScatSol v) {R : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (ℓ : ℝ) :
    tsupport (W1fun v h ℓ) ⊆ Metric.ball (0 : ℝ³) R := by
  have h1 : Function.support (W1fun v h ℓ) ⊆ Function.support v := support_W1fun_subset h ℓ
  calc tsupport (W1fun v h ℓ) = closure (Function.support (W1fun v h ℓ)) := rfl
    _ ⊆ closure (Function.support v) := closure_mono h1
    _ = tsupport v := rfl
    _ ⊆ Metric.ball (0 : ℝ³) R := hv_supp

end Work.BoseFixR
