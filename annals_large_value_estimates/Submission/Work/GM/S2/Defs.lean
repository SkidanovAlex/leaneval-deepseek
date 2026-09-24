import Mathlib
import Submission.GM.Interfaces
import Submission.LargeValues.KeyProp

/-!
# GM §6 (`S₂`): shared vocabulary

This module fixes the objects used by all the lemmas of the `S₂` area
(Guth–Maynard, *New large value estimates for Dirichlet polynomials*, §6).

Setting: `T = M N = N^{6/5}`, `W ⊆ [0,T]` a finite `T^ε`-separated set, and
`ĥ_t(ξ) = ∫ w(u)² u^{it} e(-ξu) du` as in `Submission.GM.hhat`.

The weight inside `hfun` is `ψ(u) = w(u)²`; the reflection route used here writes
`ψ(u) u^{it} = ∫ ĝ(ξ) u^{i(t+2πξ)} dξ`, where `g(s) = ψ(e^s)` is the "log-window"
and `ĝ` its Fourier transform.  The truncation point of the reflected `m`-sum is
`X = max 1 ((1+|t|) T^η / N)`.

-/

open Complex Finset MeasureTheory
open scoped BigOperators Topology

set_option autoImplicit false

namespace Work.GM.S2

/-- `ψ(u) = w(u)²`, the squared Guth–Maynard bump (the weight inside `hfun`). -/
noncomputable def psi (u : ℝ) : ℝ := (Submission.LargeValues.bumpW u) ^ 2

lemma psi_nonneg (u : ℝ) : 0 ≤ psi u :=
  pow_nonneg (Submission.LargeValues.bumpW_nonneg u) 2

lemma psi_eq_zero_of_not_mem {u : ℝ} (hu : u ∉ Set.Icc 1 2) : psi u = 0 := by
  rw [psi, Submission.LargeValues.bumpW_eq_zero_of_notMem hu, zero_pow (by norm_num)]

/-- The log-window `s ↦ ψ(e^s)`: smooth, compactly supported in `[0, log 2]`. -/
noncomputable def logWindow (s : ℝ) : ℂ := ((psi (Real.exp s) : ℝ) : ℂ)

/-- The Fourier transform of the log-window, `ĝ(ξ) = ∫ s, g(s) e^{-2πiξs} ds`. -/
noncomputable def ghat (ξ : ℝ) : ℂ := FourierTransform.fourier logWindow ξ

/-- The truncation point of the reflected `m`-sum: `max 1 ((1+|t|) T^η / N)`. -/
noncomputable def truncPt (N : ℕ) (t : ℝ) (η : ℝ) : ℝ :=
  max 1 ((1 + |t|) * (Submission.LargeValues.M N) ^ η / (N : ℝ))


/-- The log-window of the weight `ψ(u)/u`: `g₁(s) = e^s · ψ(e^s)`, so that
`ψ(u) = g₁(log u)/u` for `0 < u`.  It is `C^∞` with compact support in `[0, log 2]`. -/
noncomputable def logWindow1 (s : ℝ) : ℂ := ((Real.exp s * psi (Real.exp s) : ℝ) : ℂ)

/-- The Fourier transform of `g₁` (`ĝ₁(ξ) = ∫ s, g₁(s) e^{-2πiξs} ds`). -/
noncomputable def ghat1 (ξ : ℝ) : ℂ := FourierTransform.fourier logWindow1 ξ

/-- ## Roadmap for `Work.GM.S2.hhat_reflection`

The reflection (Guth–Maynard Lemma 6.2) is proved by pairing this module's
Fourier-in-log representation of the weight with `osc_integral_bound`:

* `log_window1` (delegated separately) gives, for `u > 0`,
  `ψ(u) = (1/u) ∫ ξ, ĝ₁(ξ) u^{2πiξ} dξ`, hence
  `ψ(u) u^{it} = (1/u) ∫ ξ, ĝ₁(ξ) u^{i(t+2πξ)} dξ`.
* Fourier–Fubini turns `ĥ_t(mN) = ∫₁² ψ(u) u^{it} e(-mNu) du` into
  `∫ ξ, ĝ₁(ξ) · K_m(t+2πξ) dξ` with `K_m(σ) = ∫₁² u^{-1+iσ} e(-mNu) du`.
* The substitution `v = N m u` gives `K_m(σ) = (Nm)^{-iσ} L_m(σ)` with
  `L_m(σ) = (Nm)^{-1} ∫_{Nm}^{2Nm} v^{-1+iσ} e(-v) dv`, and `osc_integral_bound`
  gives `|L_m(σ)| ≤ C (1+|σ|)^{-1/2}` uniformly in `m ≥ 1`, `N ≥ 1`.
* Factoring out the supremum over `m ≤ Y` (the sum over `m` is finite!),
  `‖Σ_{m≤Y} ĥ_t(mN)‖ ≤ C ∫ ξ, ‖ĝ₁(ξ)‖ (1+|t+2πξ|)^{-1/2} ‖Σ_{m≤Y} m^{i(t+2πξ)}‖ dξ`.

The remaining factors (`N^{-iσ}`) are unimodular and drop out.  The finite `m`-sum
may be extended to the tail by `hhat_decay` in the caller.
-/

lemma truncPt_ge_one (N : ℕ) (t η : ℝ) : 1 ≤ truncPt N t η := le_max_left _ _

end Work.GM.S2
