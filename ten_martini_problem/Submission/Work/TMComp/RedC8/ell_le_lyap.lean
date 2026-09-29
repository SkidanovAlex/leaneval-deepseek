import Mathlib
import Submission.Work.TMComp.RedC8.EllLyapDefs
import Submission.Work.TMComp.Kotani.Objects
import Submission.Work.TMComp.Kotani.mfun_props
import Submission.Work.TMComp.Kotani.lyap_usc
import Submission.Work.TMComp.LEAlg
import Submission.Work.TMComp.LEBridge
import Submission.Work.TMC7Core.Lyap.lyap_eq_lim
import Submission.Work.TMContract.Components

/-!
# `ℓ(E) ≤ L(E)` for `E` in the upper half plane (C8, `RedC8`)

For `E ∈ ℍ` the averaged log-modulus `ℓ(E) = ∫₀¹ log‖m(E,x)‖ dx` of the `m`-function is at
most the Lyapunov exponent `L(E) = ⨅ₙ (1/(n+1)) ∫₀¹ log‖A_{n+1}(x)‖_F dx` of the almost
Mathieu cocycle.

The proof produces, for every phase `x`, an explicit solution `u` of the transfer recurrence:
with `u_0 = 1` and ratios `u_{k}/u_{k-1} = m(E, x + kα)` the covariance relation
`m(y+α) = E - pot y - 1/m(y)` shows that `(u_k, u_{k-1}) = A_k(x) · (1, 1/m(x))` for every
`k ≥ 1` (`EllLyapDefs.uSol`, `iterC_mulVec_uSol`).  Hence

`∏_{j=1}^{n} ‖m(x+jα)‖ = ‖u_n(x)‖ ≤ ‖A_n(x)‖_F · (1 + ‖1/m(x)‖)`

(`norm_mulVec_zero_le`), and integrating over a period, where each shift `x ↦ x + jα` can be
absorbed by the `1`-periodicity of `m(E, ·)`:

`n ℓ(E) ≤ ∫₀¹ log‖A_n(x)‖_F dx + K`,   `K = ∫₀¹ log(1 + ‖1/m(x)‖) dx`.

Dividing by `n+1` and letting `n → ∞` (Fekete's lemma, `lyap_eq_lim`, transported to
`Work.TMContract.lyap` by the definitional bridges) gives `ℓ(E) ≤ L(E)`.
-/

open MeasureTheory Filter Topology Set
open scoped Matrix

noncomputable section

namespace Work.TMComp.RedC8

open Work.TMComp.Kotani
open Work.TMContract

/-! ## The linear-algebra bound -/

/-- Every matrix entry is bounded by the Frobenius norm. -/
theorem norm_coord_le_frob (A : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    ‖A i j‖ ≤ frob A := by
  rw [Work.TMContract.frob]
  refine le_trans (le_of_eq (Real.sqrt_sq (norm_nonneg _)).symm) (Real.sqrt_le_sqrt ?_)
  fin_cases i <;> fin_cases j <;> simp <;>
    nlinarith [sq_nonneg ‖A 0 0‖, sq_nonneg ‖A 0 1‖, sq_nonneg ‖A 1 0‖, sq_nonneg ‖A 1 1‖]

/-- The first coordinate of `A *ᵥ v` is bounded by the Frobenius norm of `A` times the sum
of the moduli of the two coordinates of `v`. -/
theorem norm_mulVec_zero_le (A : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℂ) :
    ‖(A *ᵥ v) 0‖ ≤ frob A * (‖v 0‖ + ‖v 1‖) := by
  have h0 := norm_coord_le_frob A 0 0
  have h1 := norm_coord_le_frob A 0 1
  have hentry : (A *ᵥ v) 0 = A 0 0 * v 0 + A 0 1 * v 1 := by
    rw [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two]
  rw [hentry]
  calc ‖A 0 0 * v 0 + A 0 1 * v 1‖
      ≤ ‖A 0 0 * v 0‖ + ‖A 0 1 * v 1‖ := norm_add_le _ _
    _ = ‖A 0 0‖ * ‖v 0‖ + ‖A 0 1‖ * ‖v 1‖ := by rw [norm_mul, norm_mul]
    _ ≤ frob A * ‖v 0‖ + frob A * ‖v 1‖ :=
        add_le_add (mul_le_mul_of_nonneg_right h0 (norm_nonneg _))
          (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
    _ = frob A * (‖v 0‖ + ‖v 1‖) := by ring

/-! ## The transfer step on the solution vector -/

/-- The explicit action of one transfer matrix on a `2`-vector. -/
theorem tmC_mulVec (lam : ℝ) (E : ℂ) (y : ℝ) (a b : ℂ) :
    tmC lam E y *ᵥ ![a, b] = ![(E - ((pot lam y : ℝ) : ℂ)) * a - b, a] := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two, Work.TMContract.tmC, pot] <;>
    ring

/-- The transfer recursion, written as an equation for `iterC (k+1)`. -/
theorem iterC_succ_eq (α lam : ℝ) (E : ℂ) (k : ℕ) (x : ℝ) :
    iterC α lam E (k + 1) x = tmC lam E (x + (k : ℝ) * α) * iterC α lam E k x := by
  simp only [Work.TMContract.iterC]

/-- Joint continuity of the cocycle, with the energy fixed. -/
theorem continuous_iterC_fixed (α lam : ℝ) (E : ℂ) (k : ℕ) :
    Continuous (fun x : ℝ => iterC α lam E k x) :=
  (continuous_iterC_prod α lam k).comp (continuous_const.prodMk continuous_id)

/-- Continuity of the Lyapunov integrand, with the energy fixed. -/
theorem continuous_log_frob_iterC_fixed (α lam : ℝ) (E : ℂ) (k : ℕ) :
    Continuous (fun x : ℝ => Real.log (frob (iterC α lam E k x))) :=
  (continuous_log_frob_iterC_prod α lam k).comp (continuous_const.prodMk continuous_id)

/-- One transfer step advances the solution vector `(uSol (n+1), uSol n)`. -/
theorem tmC_mulVec_uSol (α lam : ℝ) (E : ℂ) (hE : 0 < E.im) (n : ℕ) (x : ℝ) :
    tmC lam E (x + ((n + 1 : ℕ) : ℝ) * α)
        *ᵥ ![(uSol α lam E (n + 1) x : ℂ), uSol α lam E n x]
      = ![(uSol α lam E (n + 2) x : ℂ), uSol α lam E (n + 1) x] := by
  rw [tmC_mulVec]
  have hcov := MfunProbs.mfun_covariance α lam hE (x + ((n + 1 : ℕ) : ℝ) * α)
  have hshift : x + ((n + 1 : ℕ) : ℝ) * α + α = x + ((n + 2 : ℕ) : ℝ) * α := by
    push_cast; ring
  rw [hshift] at hcov
  have hmne : mfun α lam E (x + ((n + 1 : ℕ) : ℝ) * α) ≠ 0 := mfun_ne_zero α lam E hE _
  have hs : uSol α lam E (n + 1) x
      = uSol α lam E n x * mfun α lam E (x + ((n + 1 : ℕ) : ℝ) * α) := uSol_succ α lam E n x
  have hb : uSol α lam E n x
      = uSol α lam E (n + 1) x / mfun α lam E (x + ((n + 1 : ℕ) : ℝ) * α) := by
    rw [eq_div_iff hmne]; exact hs.symm
  have hs2 : uSol α lam E (n + 2) x
      = uSol α lam E (n + 1) x * mfun α lam E (x + ((n + 2 : ℕ) : ℝ) * α) := by
    have h := uSol_succ α lam E (n + 1) x
    rwa [show n + 1 + 1 = n + 2 from rfl] at h
  have hX : (E - ((pot lam (x + ((n + 1 : ℕ) : ℝ) * α) : ℝ) : ℂ)) * uSol α lam E (n + 1) x
        - uSol α lam E n x = uSol α lam E (n + 2) x := by
    rw [hs2, hcov, hb]
    ring
  rw [hX]

/-- The solution vector identity: `A_k(x) · (1, 1/m(x)) = (u_k, u_{k-1})`. -/
theorem iterC_mulVec_uSol (α lam : ℝ) (E : ℂ) (hE : 0 < E.im) (n : ℕ) (x : ℝ) :
    iterC α lam E (n + 1) x *ᵥ ![(1 : ℂ), wv α lam E x]
      = ![(uSol α lam E (n + 1) x : ℂ), uSol α lam E n x] := by
  induction n with
  | zero =>
    have h1 : iterC α lam E (0 + 1) x = tmC lam E x := by
      rw [iterC_succ_eq α lam E 0 x]
      simp only [Work.TMContract.iterC, Nat.cast_zero, zero_mul, add_zero, mul_one]
    rw [h1, tmC_mulVec]
    have hcov := MfunProbs.mfun_covariance α lam hE x
    have e1 : uSol α lam E 1 x = mfun α lam E (x + α) := by
      simp only [uSol, Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
      congr 1
      push_cast
      ring
    rw [e1, uSol_zero]
    simp only [wv, mul_one]
    rw [hcov]
    ring_nf
  | succ n ih =>
    rw [iterC_succ_eq α lam E (n + 1) x, ← Matrix.mulVec_mulVec, ih]
    exact tmC_mulVec_uSol α lam E hE n x


/-! ## The pointwise logarithmic bound -/

/-- The averaged log-modulus is bounded by the Lyapunov integrand plus a phase-dependent
constant: `log ‖u_{n+1}(x)‖ ≤ log ‖A_{n+1}(x)‖_F + log (1 + ‖1/m(x)‖)`. -/
theorem log_uSol_le (α lam : ℝ) (E : ℂ) (hE : 0 < E.im) (n : ℕ) (x : ℝ) :
    Real.log ‖uSol α lam E (n + 1) x‖
      ≤ Real.log (frob (iterC α lam E (n + 1) x)) + Real.log (1 + ‖wv α lam E x‖) := by
  have hb := norm_mulVec_zero_le (iterC α lam E (n + 1) x) (![(1 : ℂ), wv α lam E x])
  rw [iterC_mulVec_uSol α lam E hE n x] at hb
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, norm_one] at hb
  have hpos : 0 < ‖uSol α lam E (n + 1) x‖ :=
    norm_pos_iff.mpr (uSol_ne_zero α lam E hE (n + 1) x)
  have hlog := Real.log_le_log hpos hb
  rw [Real.log_mul (ne_of_gt (frob_iterC_pos α lam E (n + 1) x))
    (by positivity : (1 : ℝ) + ‖wv α lam E x‖ ≠ 0)] at hlog
  exact hlog

/-! ## The integral identities -/

/-- Absorbing a phase shift under the integral sign, using the `1`-periodicity of `m(E, ·)`. -/
theorem integral_log_mfun_shift (α lam : ℝ) (E : ℂ) (hE : 0 < E.im) (c : ℝ) :
    ∫ x in (0 : ℝ)..1, Real.log ‖mfun α lam E (x + c)‖ = ell α lam E := by
  have hper : Function.Periodic (fun y : ℝ => Real.log ‖mfun α lam E y‖) 1 := by
    intro y
    simp only [MfunProbs.mfun_period α lam E y]
  calc ∫ x in (0 : ℝ)..1, Real.log ‖mfun α lam E (x + c)‖
      = ∫ x in (0 : ℝ) + c..1 + c, Real.log ‖mfun α lam E x‖ := by
        simpa only using intervalIntegral.integral_comp_add_right
          (a := (0 : ℝ)) (b := 1) (d := c) (fun y : ℝ => Real.log ‖mfun α lam E y‖)
    _ = ∫ x in c..c + 1, Real.log ‖mfun α lam E x‖ := by
        rw [show (0 : ℝ) + c = c by ring, show (1 : ℝ) + c = c + 1 by ring]
    _ = ∫ x in (0 : ℝ)..0 + 1, Real.log ‖mfun α lam E x‖ := hper.intervalIntegral_add_eq c 0
    _ = ell α lam E := by rw [show (0 : ℝ) + 1 = 1 by norm_num]; rfl

/-- `∫₀¹ log ‖u_n(x)‖ dx = n ℓ(E)`. -/
theorem integral_log_norm_uSol (α lam : ℝ) (E : ℂ) (hE : 0 < E.im) (n : ℕ) :
    ∫ x in (0 : ℝ)..1, Real.log ‖uSol α lam E n x‖ = (n : ℝ) * ell α lam E := by
  have hcongr : (∫ x in (0 : ℝ)..1, Real.log ‖uSol α lam E n x‖)
      = ∫ x in (0 : ℝ)..1, ∑ j ∈ Finset.range n,
          Real.log ‖mfun α lam E (x + ((j + 1 : ℕ) : ℝ) * α)‖ := by
    apply intervalIntegral.integral_congr
    intro x _
    exact log_norm_uSol α lam E hE n x
  rw [hcongr, intervalIntegral.integral_finsetSum]
  · rw [Finset.sum_congr rfl (fun j _ =>
      integral_log_mfun_shift α lam E hE (((j + 1 : ℕ) : ℝ) * α))]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  · intro j _
    exact ((continuous_norm.comp ((continuous_mfun_phase α lam hE).comp
        (continuous_id.add continuous_const))).log
      (fun x => norm_ne_zero_iff.mpr (mfun_ne_zero α lam E hE _))).intervalIntegrable 0 1

/-! ## The finite-scale lower bound on the Lyapunov average -/

theorem lyapAvg_lower (α lam : ℝ) (E : ℂ) (hE : 0 < E.im) (n : ℕ) :
    ell α lam E - (∫ x in (0 : ℝ)..1, Real.log (1 + ‖wv α lam E x‖)) / ((n : ℝ) + 1)
      ≤ lyapAvg α lam n E := by
  set K : ℝ := ∫ x in (0 : ℝ)..1, Real.log (1 + ‖wv α lam E x‖) with hK
  have hVcont : Continuous (fun x : ℝ => 1 + ‖wv α lam E x‖) := by
    have h : Continuous (fun x : ℝ => (mfun α lam E x)⁻¹) :=
      (continuous_mfun_phase α lam hE).inv₀ (fun x => mfun_ne_zero α lam E hE x)
    exact continuous_const.add (continuous_norm.comp h)
  have h1c : Continuous (fun x : ℝ => Real.log ‖uSol α lam E (n + 1) x‖) :=
    (continuous_norm.comp (continuous_uSol α lam E hE (n + 1))).log
      (fun x => norm_ne_zero_iff.mpr (uSol_ne_zero α lam E hE (n + 1) x))
  have h2c : Continuous (fun x : ℝ => Real.log (frob (iterC α lam E (n + 1) x))) :=
    continuous_log_frob_iterC_fixed α lam E (n + 1)
  have h3c : Continuous (fun x : ℝ => Real.log (1 + ‖wv α lam E x‖)) :=
    hVcont.log (fun x => by positivity)
  have hmono : (∫ x in (0 : ℝ)..1, Real.log ‖uSol α lam E (n + 1) x‖)
      ≤ ∫ x in (0 : ℝ)..1, (Real.log (frob (iterC α lam E (n + 1) x))
          + Real.log (1 + ‖wv α lam E x‖)) := by
    apply intervalIntegral.integral_mono_on
      (f := fun x : ℝ => Real.log ‖uSol α lam E (n + 1) x‖)
      (g := fun x : ℝ => Real.log (frob (iterC α lam E (n + 1) x))
        + Real.log (1 + ‖wv α lam E x‖))
      (a := (0 : ℝ)) (b := 1) (by norm_num)
      (h1c.intervalIntegrable 0 1) ((h2c.add h3c).intervalIntegrable 0 1)
    intro x _
    exact log_uSol_le α lam E hE n x
  have hsplit : (∫ x in (0 : ℝ)..1, (Real.log (frob (iterC α lam E (n + 1) x))
        + Real.log (1 + ‖wv α lam E x‖)))
      = (∫ x in (0 : ℝ)..1, Real.log (frob (iterC α lam E (n + 1) x))) + K := by
    rw [intervalIntegral.integral_add (h2c.intervalIntegrable 0 1)
      (h3c.intervalIntegrable 0 1), ← hK]
  have hLval : (∫ x in (0 : ℝ)..1, Real.log ‖uSol α lam E (n + 1) x‖)
      = ell α lam E * ((n : ℝ) + 1) := by
    have h := integral_log_norm_uSol α lam E hE (n + 1)
    rw [show ((n + 1 : ℕ) : ℝ) * ell α lam E = ell α lam E * ((n : ℝ) + 1) from by
      push_cast; ring] at h
    exact h
  have hFval : lyapAvg α lam n E * ((n : ℝ) + 1)
      = (∫ x in (0 : ℝ)..1, Real.log (frob (iterC α lam E (n + 1) x))) := by
    rw [Work.TMComp.Kotani.lyapAvg]
    rw [div_mul_cancel₀ _ (ne_of_gt (by positivity : (0 : ℝ) < (n : ℝ) + 1))]
  have hmain : ell α lam E * ((n : ℝ) + 1)
      ≤ lyapAvg α lam n E * ((n : ℝ) + 1) + K := by
    rw [hsplit, hLval, ← hFval] at hmono
    exact hmono
  have hd : 0 < (n : ℝ) + 1 := by positivity
  have hKmul : K / ((n : ℝ) + 1) * ((n : ℝ) + 1) = K :=
    div_mul_cancel₀ _ (ne_of_gt hd)
  have h2' : (ell α lam E - K / ((n : ℝ) + 1)) * ((n : ℝ) + 1)
      ≤ lyapAvg α lam n E * ((n : ℝ) + 1) := by
    rw [sub_mul, hKmul]
    linarith [hmain]
  exact le_of_mul_le_mul_right h2' hd

/-! ## The Lyapunov exponent as the limit of its finite-scale averages -/

theorem tendsto_lyapAvg (α lam : ℝ) (E : ℂ) :
    Filter.Tendsto (fun n : ℕ => lyapAvg α lam n E) Filter.atTop
      (nhds (Work.TMContract.lyap α lam E)) := by
  have h := Work.TMC7Core.Lyap.lyap_eq_lim α lam E
  rw [Work.TMComp.lyap_bridge] at h
  simpa only [Work.TMComp.Kotani.lyapAvg, Work.TMComp.iterC_bridge,
    Work.TMComp.frob_bridge] using h

/-! ## The main inequality -/

theorem ell_le_lyap (α lam : ℝ) (E : ℂ) (hE : 0 < E.im) :
    Work.TMComp.Kotani.ell α lam E ≤ Work.TMContract.lyap α lam E := by
  have ha := tendsto_lyapAvg α lam E
  have hdiv : Filter.Tendsto (fun n : ℕ =>
      (∫ x in (0 : ℝ)..1, Real.log (1 + ‖wv α lam E x‖)) / ((n : ℝ) + 1))
      Filter.atTop (nhds 0) := by
    have hg : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1)) Filter.atTop Filter.atTop :=
      tendsto_atTop_add_const_right _ (1 : ℝ) tendsto_natCast_atTop_atTop
    exact hg.const_div_atTop _
  have hb : Filter.Tendsto (fun n : ℕ => ell α lam E
      - (∫ x in (0 : ℝ)..1, Real.log (1 + ‖wv α lam E x‖)) / ((n : ℝ) + 1))
      Filter.atTop (nhds (ell α lam E)) := by
    simpa using (tendsto_const_nhds (x := ell α lam E)).sub hdiv
  exact le_of_tendsto_of_tendsto hb ha
    (Filter.Eventually.of_forall (fun n => lyapAvg_lower α lam E hE n))

end Work.TMComp.RedC8
