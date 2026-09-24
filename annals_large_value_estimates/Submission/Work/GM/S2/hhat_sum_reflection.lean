import Mathlib
import Submission.Work.GM.S2.Defs
import Submission.Work.GM.S2.hhat_decay
import Submission.Work.GM.S2.osc_integral_bound
import Submission.Work.GM.S2.oscF_interval_bound
import Submission.Work.GM.S2.hhat_per_m_expansion

open MeasureTheory Finset
open scoped Real BigOperators

set_option autoImplicit false

namespace Work.GM.S2

/-!
# The reflection identity in sum form (the engine of GM Lemma 6.2)

This file assembles `Work.GM.S2.hhat_sum_reflection` from the per-`m` expansion
`Work.GM.S2.hhat_per_m_expansion` (`hhat_per_m_expansion.lean`), the finite-sum
rearrangement, and the substitution `v = e^s` in the inner oscillatory integral.
-/

/-- The `m`-th term of the reflected Dirichlet polynomial, `(mN)^{-i(t+2πξ)}`. -/
noncomputable def reflTerm (N : ℕ) (m : ℕ) (t ξ : ℝ) : ℂ :=
  ((m : ℂ) * (N : ℂ)) ^ (-(Complex.I * ((t + 2 * Real.pi * ξ : ℝ) : ℂ)))

/-- The reflected Dirichlet polynomial `Σ_{1 ≤ m ≤ M} (mN)^{-i(t+2πξ)}`. -/
noncomputable def reflPoly (N M : ℕ) (t ξ : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 M, reflTerm N m t ξ

/-- The inner `v`-integral `∫_N^{2MN} v^{iσ-1} e(-v) dv` of the reflection identity,
with `σ = t + 2πξ`. -/
noncomputable def reflInner (N M : ℕ) (t : ℝ) (ξ : ℝ) : ℂ :=
  ∫ v in (N : ℝ)..(2 * (M : ℝ) * (N : ℝ)), oscF (t + 2 * Real.pi * ξ) v

/-- The same inner integral after `v = e^s`: `∫_{log N}^{log 2MN} exp(i(σs - 2πe^s)) ds`. -/
noncomputable def reflInnerS (N M : ℕ) (t : ℝ) (ξ : ℝ) : ℂ :=
  ∫ s in Real.log N..Real.log (2 * (M : ℝ) * (N : ℝ)),
    Complex.exp (Complex.I * ((phase (t + 2 * Real.pi * ξ) s : ℝ) : ℂ))

/-- **The substitution `v = e^s`** in the inner oscillatory integral of the reflection
identity: `∫_N^{2MN} v^{iσ-1}e(-v) dv = ∫_{log N}^{log 2MN} exp(i(σs - 2πe^s)) ds`. -/
lemma oscF_subst_log (N M : ℕ) (hN : 1 ≤ N) (hM : 1 ≤ M) (σ : ℝ) :
    (∫ v in (N : ℝ)..(2 * (M : ℝ) * (N : ℝ)), oscF σ v)
      = ∫ s in Real.log N..Real.log (2 * (M : ℝ) * (N : ℝ)),
          Complex.exp (Complex.I * ((phase σ s : ℝ) : ℂ)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hMpos : (0 : ℝ) < (M : ℝ) := by
    have : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    linarith
  have hBpos : (0 : ℝ) < 2 * (M : ℝ) * (N : ℝ) := by positivity
  have hsub := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg (E := ℂ)
      (f := Real.exp) (f' := Real.exp) (g := oscF σ)
      (a := Real.log N) (b := Real.log (2 * (M : ℝ) * (N : ℝ)))
      Real.continuous_exp.continuousOn
      (fun x _ => Real.hasDerivAt_exp x)
      (fun x _ => Real.exp_nonneg x)
  rw [Real.exp_log hNpos, Real.exp_log hBpos] at hsub
  rw [← hsub]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  exact oscF_smul_exp σ x

/-- **The `u`-integral of `oscG` over `Icc (1/m) (2M/m)`.**  With `c = mN` and `σ = t + 2πξ`,
`∫_{1/m}^{2M/m} ĝ₁(ξ) u^{iσ-1} e(-cu) du = ĝ₁(ξ) · (mN)^{-iσ} · ∫_N^{2MN} v^{iσ-1} e(-v) dv`. -/
lemma oscG_setIntegral_Icc (N M m : ℕ) (hN : 1 ≤ N) (hm1 : 1 ≤ m) (hmM : m ≤ M)
    (t ξ : ℝ) :
    (∫ u in Set.Icc ((1 : ℝ) / (m : ℝ)) (2 * (M : ℝ) / (m : ℝ)),
        oscG t ((m : ℝ) * (N : ℝ)) u ξ)
      = ghat1 ξ * reflTerm N m t ξ * reflInner N M t ξ := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hm1' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hmM' : (m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hmM
  have hab : ((1 : ℝ) / (m : ℝ)) ≤ (2 * (M : ℝ) / (m : ℝ)) := by
    rw [div_le_div_iff_of_pos_right hm0]; linarith
  have h1 : (fun u : ℝ => oscG t ((m : ℝ) * (N : ℝ)) u ξ)
      = (fun u : ℝ => ghat1 ξ * oscU ((m : ℝ) * (N : ℝ)) (t + 2 * Real.pi * ξ) u) := rfl
  have h2 : (∫ u in Set.Icc ((1 : ℝ) / (m : ℝ)) (2 * (M : ℝ) / (m : ℝ)),
        oscU ((m : ℝ) * (N : ℝ)) (t + 2 * Real.pi * ξ) u)
      = reflTerm N m t ξ * reflInner N M t ξ := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
    rw [integral_oscU_subst m M N (t + 2 * Real.pi * ξ) hm1 hmM hN]
    simp only [reflTerm, reflInner, oscV, oscF]
  rw [h1, MeasureTheory.integral_const_mul, h2]
  ring

/-- **The reflection identity (sum form, `s`-coordinates)** — the engine of GM Lemma 6.2.

`ψ(u) = w(u)²` is the weight of `hfun`, `hhat t ξ = 𝓕(h_t) ξ`, and `hinv` is the
log-Fourier representation `ψ(u) = (1/u) ∫ ξ, ĝ₁(ξ) u^{2πiξ} dξ` for `u > 0`
(first conjunct of `Work.GM.S2.log_window1`).  For `N ≥ 1`, `M ≥ 1`, `t : ℝ`:

  `Σ_{1 ≤ m ≤ M} ĥ_t(mN) = ∫ ξ, ĝ₁(ξ) · (Σ_{1 ≤ m ≤ M} (mN)^{-iσ}) ·
      (∫_{log N}^{log(2MN)} exp(i(σ s - 2π e^s)) ds) dξ`,  where `σ = t + 2πξ`.

So the `ξ`-integral of `ĝ₁` times a Dirichlet polynomial in `m` (exponent `σ`) times the
pure phase integral `∫ exp(i·phase σ)` (`phase` is defined in `osc_integral_bound`).

Proof route (all integrands below are CONTINUOUS, so measurability is never an issue —
do NOT attack the `(v,ξ)` Fubini directly, pass to `s = log v` first):
1. per `m`: `hhat_eq_integral_amp t (mN)` gives `ĥ_t(mN) = ∫ u in (1/2)..(5/2), hhatAmp (mN) u * hhatPhase t u`
   `= ∫ u in (1/m)..(2M/m), ψ(u) · hhatKernel (mN) u · hhatPhase t u du` (the integrand vanishes off
   `[1,2] ⊆ [1/m, 2M/m]` for `1 ≤ m ≤ M`).
2. substitute `v = Nmu` (`intervalIntegral.smul_integral_comp_mul_left`, `c = Nm ≠ 0`):
   `ĥ_t(mN) = ∫ v in N..(2MN), (Nm)^{-1-it} ψ(v/(Nm)) v^{it} e(-v) dv`
   (note `hhatKernel ξ u = e(-ξu)` and `hhatPhase t u = u^{it}` on `u > 0`).
3. sum over `m` and pull the sum inside (`intervalIntegral.integral_finset_sum`; the integrands are
   continuous on `[N, 2MN]`, `N ≥ 1`): `Σ_m ĥ_t(mN) = ∫ v in N..(2MN), v^{it} e(-v) Σ_m (Nm)^{-1-it} ψ(v/(Nm)) dv`.
   (Equivalently: sum the existing per-`m` identity `Work.GM.S2.hhat_per_m_expansion` — but that
   needs integrated-hypothesis bookkeeping; the route below is direct and avoids it.)
4. pointwise in `v > 0`, use `hinv` at `u = v/(Nm)` and `Complex.cpow_add`:
   `Σ_m (Nm)^{-1-it} ψ(v/(Nm)) = v⁻¹ ∫ ξ, ĝ₁(ξ) (Σ_m (Nm)^{-iσ}) v^{2πiξ} dξ`
   (finite sum inside `∫` by linearity, `integral_finset_sum`; each `ξ`-integrand has norm `‖ĝ₁ξ‖`,
   integrable by `hint`).
5. substitute `v = e^s` in the outer integral (`intervalIntegral.integral_comp_mul_deriv` with
   `f = Real.exp` on `[log N, log(2MN)]`, `N ≥ 1 > 0`): the factors
   `v^{it} · v^{-1} · v^{2πiξ} · dv = e^{i(t+2πξ)s} ds`, and `e(-v) = e(-e^s)`, so the integrand is
   `exp(i(σ s - 2π e^s))`; this gives the double integral
   `∫_{log N}^{log(2MN)} ∫ ξ, exp(i(σ s - 2π e^s)) ĝ₁(ξ) (Σ_m (Nm)^{-iσ}) dξ ds`.
6. Fubini (`MeasureTheory.integral_integral_swap` for `volume.prod volume` restricted to the compact
   `s`-interval, or `intervalIntegral`-level swapping): the integrand is continuous on the product
   `[log N, log(2MN)] × ℝ` and dominated there by `M ‖ĝ₁ξ‖`, which is integrable; swap to
   `∫ ξ, ĝ₁(ξ) (Σ_m (Nm)^{-iσ}) (∫_{log N}^{log(2MN)} exp(i(σ s - 2π e^s)) ds) dξ`. -/
theorem hhat_sum_reflection
    (hinv : ∀ u : ℝ, 0 < u →
      ((Work.GM.S2.psi u : ℝ) : ℂ) = (1 / (u : ℂ)) * MeasureTheory.integral MeasureTheory.volume
        (fun ξ : ℝ => Work.GM.S2.ghat1 ξ * (u : ℂ) ^ (2 * Real.pi * Complex.I * (ξ : ℂ))))
    (hint : MeasureTheory.Integrable Work.GM.S2.ghat1)
    (N M : ℕ) (hN : 1 ≤ N) (hM : 1 ≤ M) (t : ℝ) :
    (∑ m ∈ Finset.Icc 1 M, Submission.GM.hhat t ((m : ℝ) * (N : ℝ)))
      = ∫ ξ, Work.GM.S2.ghat1 ξ *
          (∑ m ∈ Finset.Icc 1 M, ((m : ℂ) * (N : ℂ)) ^ (-(Complex.I * ((t + 2 * Real.pi * ξ : ℝ) : ℂ)))) *
          (∫ s in Real.log N..Real.log (2 * (M : ℝ) * (N : ℝ)),
            Complex.exp (Complex.I * ((Work.GM.S2.phase (t + 2 * Real.pi * ξ) s : ℝ) : ℂ))) := by
  have hper : ∀ m ∈ Finset.Icc 1 M,
      Submission.GM.hhat t ((m : ℝ) * (N : ℝ))
        = ∫ ξ, Work.GM.S2.ghat1 ξ * reflTerm N m t ξ * reflInner N M t ξ := by
    intro m hm
    obtain ⟨hm1, hmM⟩ := Finset.mem_Icc.mp hm
    have h := hhat_per_m_expansion hinv hint N M m hN hm1 hmM t
    simpa only [reflTerm, reflInner, oscF] using h
  have hInt : ∀ m ∈ Finset.Icc 1 M,
      Integrable (fun ξ : ℝ => Work.GM.S2.ghat1 ξ * reflTerm N m t ξ * reflInner N M t ξ) := by
    intro m hm
    obtain ⟨hm1, hmM⟩ := Finset.mem_Icc.mp hm
    have ha : (0 : ℝ) < (1 : ℝ) / (m : ℝ) := by
      have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
      positivity
    have hG := (oscG_integrable_prod hint t ((m : ℝ) * (N : ℝ)) ((1 : ℝ) / (m : ℝ))
      (2 * (M : ℝ) / (m : ℝ)) ha).integral_prod_right
    refine hG.congr (Filter.Eventually.of_forall (fun ξ => ?_))
    simp only [reflTerm, reflInner, oscF]
    exact oscG_setIntegral_Icc N M m hN hm1 hmM t ξ
  have hmain : (∑ m ∈ Finset.Icc 1 M, Submission.GM.hhat t ((m : ℝ) * (N : ℝ)))
      = ∫ ξ, Work.GM.S2.ghat1 ξ * reflPoly N M t ξ * reflInnerS N M t ξ := by
    calc ∑ m ∈ Finset.Icc 1 M, Submission.GM.hhat t ((m : ℝ) * (N : ℝ))
        = ∑ m ∈ Finset.Icc 1 M,
            ∫ ξ, Work.GM.S2.ghat1 ξ * reflTerm N m t ξ * reflInner N M t ξ :=
          Finset.sum_congr rfl hper
      _ = ∫ ξ, ∑ m ∈ Finset.Icc 1 M,
            Work.GM.S2.ghat1 ξ * reflTerm N m t ξ * reflInner N M t ξ :=
          (MeasureTheory.integral_finsetSum (Finset.Icc 1 M) hInt).symm
      _ = ∫ ξ, Work.GM.S2.ghat1 ξ * reflPoly N M t ξ * reflInner N M t ξ := by
          refine integral_congr_ae (Filter.Eventually.of_forall (fun ξ => ?_))
          simp only [reflPoly]
          rw [← Finset.sum_mul, ← Finset.mul_sum]
      _ = ∫ ξ, Work.GM.S2.ghat1 ξ * reflPoly N M t ξ * reflInnerS N M t ξ := by
          have hpt : ∀ ξ : ℝ, Work.GM.S2.ghat1 ξ * reflPoly N M t ξ * reflInner N M t ξ
              = Work.GM.S2.ghat1 ξ * reflPoly N M t ξ * reflInnerS N M t ξ := by
            intro ξ
            simp only [reflInner, reflInnerS]
            rw [oscF_subst_log N M hN hM (t + 2 * Real.pi * ξ)]
          exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  simpa only [reflPoly, reflTerm, reflInnerS] using hmain

end Work.GM.S2
