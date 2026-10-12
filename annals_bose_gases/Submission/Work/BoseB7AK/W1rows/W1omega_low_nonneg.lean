import ChallengeDeps
import Submission.Work.BoseB7AK.W1rows.W1omegaFun_moment_integrable
import Submission.Work.BoseB7AK.W1rows.chat_low_nonneg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseB7AK/W1rows/W1omega_low_nonneg.lean`

**The low-momentum positivity of the `ω`-renormalised kernel**
`Ŵ₁ω = Work.BoseFixR.chat (Work.BoseFixR.W1omegaFun v h ℓ)`.

FS's proof of `thm:BogHamDiag` (`final_v2.tex`, lines 2390–2406) uses the
elementary quadratic Fourier estimate

  `|Ŵ₁(k) − Ŵ₁(0)| ≤ ½‖k‖² ∫ ‖y‖²|W₁(y)| dy`,

whence, since `W₁` is supported in `ball 0 R` and `Ŵ₁(0) = ∫W₁ ≥ 0`,

  `Ŵ₁(k) ≥ (1 − ½(‖k‖R)²)·∫W₁ ≥ 0`   as soon as `‖k‖ R ≤ 1`.

The same argument applies verbatim to `W₁ω = wScaled ℓ (g₀ω)`, whose numerator
`g₀ω = v(1−ω)ω` is nonnegative **almost everywhere** (`scat_gomega_ae_bounds`)
and vanishes for `‖x‖ ≥ R`; this module proves that at the corpus's own kernel and in
FS's dilute regime:

  `0 ≤ Work.BoseFixR.chat (Work.BoseFixR.W1omegaFun v h ℓ) k`  for `‖k‖ R ≤ 1`.

## Assembly

* `W1omegaFun_nonneg_ae` — `0 ≤ W₁ω` a.e. (`v(1−ω)ω` a.e. nonnegative times
  the pointwise nonnegative `(χ⋆χ)(·/ℓ)⁻¹`);
* `W1omegaFun_eq_zero_of_R_le_norm` — `W₁ω` vanishes outside `ball 0 R`;
* `W1omegaFun_integrable` — `∫|W₁ω| < ∞` (domination by `2|numerator|`);
* `W1omegaFun_moment_le` — `‖x‖²|W₁ω(x)| ≤ R²·W₁ω(x)` a.e.;
* `Work.BoseB7AK.W1rows.W1omegaFun_moment_integrable` (sibling module) —
  finiteness of the second absolute moment;
* `Work.BoseB7AK.W1rows.chat_low_nonneg` (sibling module) — the abstract
  low-momentum positivity lemma, of which the statement is one application.
-/

namespace Work.BoseB7AK.W1rows

noncomputable section

open MeasureTheory

open scoped Real Topology

-- `ℝ³` is the *global* notation `EuclideanSpace ℝ (Fin 3)` of the corpus's
-- import cone (see `Submission.Work.BoseKinLoc.Defs`); it is in scope here
-- through `Submission.Work.BoseFixR.Defs`.

/-- The numerator `W1omegaNum v h = g₀ω` of `W₁ω` is integrable: it is the
`g·ω` of the corpus's scattering calculus
(`Submission.BoseGases.scat_gomega_integrable`). -/
lemma W1omegaNum_integrable {v : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hv_nonneg : ∀ x : ℝ³, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) (h : Work.UBB.ScatSol v) :
    MeasureTheory.Integrable (W1omegaNum v h) := by
  obtain ⟨hrad, hw⟩ := Classical.choose_spec h
  exact Submission.BoseGases.scat_gomega_integrable (fun x => hv_nonneg x)
    hvrad hv_supp hrad hw

/-- `W₁ω` vanishes outside `ball 0 R`, because its numerator `g₀(1−ω)` does. -/
lemma W1omegaFun_eq_zero_of_R_le_norm {v : ℝ³ → ℝ} {R ℓ : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) (h : Work.UBB.ScatSol v)
    {x : ℝ³} (hx : R ≤ ‖x‖) : Work.BoseFixR.W1omegaFun v h ℓ x = 0 := by
  have hz : Submission.BoseGases.g0 v h x = 0 :=
    Submission.BoseGases.g0_zero_of_norm_ge hv_supp hx h
  simp [Work.BoseFixR.W1omegaFun, Submission.BoseGases.wScaled, hz]

/-- **`0 ≤ W₁ω` almost everywhere.**  The numerator is `v(1−ω)ω`, nonnegative
a.e. (`W1omegaNum_nonneg_ae`), and `wScaled` is division by the pointwise
nonnegative `(χ⋆χ)(·/ℓ)` (`convScale_nonneg`). -/
lemma W1omegaFun_nonneg_ae {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R)
    (hv_nonneg : ∀ x : ℝ³, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) (h : Work.UBB.ScatSol v) :
    ∀ᵐ x ∂(volume : Measure ℝ³), 0 ≤ Work.BoseFixR.W1omegaFun v h ℓ x := by
  filter_upwards [W1omegaNum_nonneg_ae hR hv_nonneg hvrad hv_supp h] with z hz
  rw [W1omegaFun_eq]
  dsimp only [Submission.BoseGases.wScaled]
  rw [div_eq_mul_inv]
  exact mul_nonneg hz
    (inv_nonneg.mpr (Submission.BoseGases.convScale_nonneg ℓ z))

/-- **`W₁ω` is integrable**, in the dilute regime `R ≤ ℓ·chiR0`: it is
`wScaled ℓ (W1omegaNum)` with an integrable numerator vanishing outside
`ball 0 R`, so `|W₁ω| ≤ 2|W1omegaNum|` (`Submission.BoseGases.wScaled_abs_le_two`)
and `Submission.BoseGases.wScaled_integrable_ae` applies. -/
lemma W1omegaFun_integrable {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ)
    (hv_nonneg : ∀ x : ℝ³, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) (h : Work.UBB.ScatSol v)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) :
    MeasureTheory.Integrable (Work.BoseFixR.W1omegaFun v h ℓ) := by
  have hNil : MeasureTheory.Integrable (W1omegaNum v h) :=
    W1omegaNum_integrable hR hv_nonneg hvrad hv_supp h
  have hsupp : ∀ z : ℝ³, R ≤ ‖z‖ → W1omegaNum v h z = 0 := fun z hz => by
    have hz0 : Submission.BoseGases.g0 v h z = 0 :=
      Submission.BoseGases.g0_zero_of_norm_ge hv_supp hz h
    simp [W1omegaNum, hz0]
  rw [W1omegaFun_eq]
  exact Submission.BoseGases.wScaled_integrable_ae hℓ hR.le hRℓ hNil hsupp

/-- **The second-moment domination**, a.e.: `‖x‖²|W₁ω(x)| ≤ R²·W₁ω(x)`.
On `‖x‖ ≤ R` this is just `‖x‖² ≤ R²` together with `0 ≤ W₁ω(x)`; for
`R ≤ ‖x‖` both sides vanish. -/
lemma W1omegaFun_moment_le {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R)
    (hv_nonneg : ∀ x : ℝ³, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) (h : Work.UBB.ScatSol v) :
    ∀ᵐ x ∂(volume : Measure ℝ³), ‖x‖ ^ 2 * |Work.BoseFixR.W1omegaFun v h ℓ x|
      ≤ R ^ 2 * Work.BoseFixR.W1omegaFun v h ℓ x := by
  filter_upwards [W1omegaFun_nonneg_ae (ℓ := ℓ) hR hv_nonneg hvrad hv_supp h] with x hxnn
  by_cases hx : ‖x‖ ≤ R
  · have h2 : ‖x‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg x) hx 2
    rw [abs_of_nonneg hxnn]
    exact mul_le_mul_of_nonneg_right h2 hxnn
  · have hxR : R ≤ ‖x‖ := le_of_lt (lt_of_not_ge hx)
    have hz : Work.BoseFixR.W1omegaFun v h ℓ x = 0 :=
      W1omegaFun_eq_zero_of_R_le_norm hv_supp h hxR
    simp [hz]

end

lemma W1omega_low_nonneg {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R ℓ : ℝ} (hR : 0 < R)
    (hℓ : 0 < ℓ) (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) (h : Work.UBB.ScatSol v)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (k : EuclideanSpace ℝ (Fin 3)) (hk : ‖k‖ * R ≤ 1) :
    0 ≤ Work.BoseFixR.chat (Work.BoseFixR.W1omegaFun v h ℓ) k := by
  refine chat_low_nonneg hR.le
    (W1omegaFun_integrable hR hℓ hv_nonneg hvrad hv_supp h hRℓ)
    (W1omegaFun_moment_integrable hR hℓ hv_nonneg hvrad hv_supp h hRℓ)
    (W1omegaFun_nonneg_ae (ℓ := ℓ) hR hv_nonneg hvrad hv_supp h) ?_ hk
  intro x hx
  exact W1omegaFun_eq_zero_of_R_le_norm hv_supp h hx

end Work.BoseB7AK.W1rows
