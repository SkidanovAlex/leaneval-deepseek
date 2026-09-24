import Mathlib
import Submission.Work.GM.S2.Defs
import Submission.Work.GM.S2.osc_integral_bound
import Submission.Work.GM.S2.oscF_interval_bound
import Submission.Work.GM.S2.hhat_sum_reflection

/-!
# GM Lemma 6.2 (`S₂`): the reflection estimate for `ĥ_t`

This is the file requested by the `S₂` area: from the log-Fourier representation of the weight
`ψ = w²` (`hinv`, the first conjunct of `Work.GM.S2.log_window1`) we deduce

`‖Σ_{1≤m≤⌊Y⌋} ĥ_t(mN)‖ ≤ C ∫ ξ, ‖ĝ₁(ξ)‖ (1+|t+2πξ|)^{-1/2} ‖Σ_{1≤m≤⌊Y⌋} m^{i(t+2πξ)}‖ dξ`.

The mathematical content is the reflection identity `Work.GM.S2.hhat_sum_reflection` (GM Lemma 6.2,
obtained by expanding `ψ` in the log-Fourier variable and substituting `v = Nmu`), combined with the
sharp stationary-phase bound `Work.GM.S2.phase_integral_bound_aux` for `∫ exp(i(σs - 2πe^s)) ds`.
-/

open MeasureTheory Finset
open scoped BigOperators
set_option autoImplicit false

namespace Work.GM.S2

/-- For positive reals `x, y` and complex `z`: `(x*y)^z = x^z * y^z` (all powers being the
branch `exp(z log ·)` on the positive axis). -/
theorem ofReal_mul_cpow_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (z : ℂ) :
    ((x * y : ℝ) : ℂ) ^ z = (x : ℂ) ^ z * (y : ℂ) ^ z := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt (mul_pos hx hy))),
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hx)),
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hy))]
  rw [← Complex.ofReal_log hx.le, ← Complex.ofReal_log hy.le,
      ← Complex.ofReal_log (mul_nonneg hx.le hy.le), Real.log_mul (ne_of_gt hx) (ne_of_gt hy)]
  push_cast
  rw [← Complex.exp_add]
  ring_nf

/-- `‖x^{i r}‖ = 1` for `x > 0`, `r : ℝ`. -/
theorem norm_ofReal_cpow_I_mul (x : ℝ) (hx : 0 < x) (r : ℝ) :
    ‖(x : ℂ) ^ (Complex.I * (r : ℂ))‖ = 1 := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hx)), Complex.norm_exp,
    ← Complex.ofReal_log hx.le]
  have : (↑(Real.log x) * (Complex.I * ↑r)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  rw [this, Real.exp_zero]

/-- `‖x^{-i r}‖ = 1` for `x > 0`, `r : ℝ`. -/
theorem norm_ofReal_cpow_neg_I_mul (x : ℝ) (hx : 0 < x) (r : ℝ) :
    ‖(x : ℂ) ^ (-(Complex.I * (r : ℂ)))‖ = 1 := by
  rw [show -(Complex.I * (r:ℂ)) = Complex.I * ((-r:ℝ):ℂ) by push_cast; ring]
  exact norm_ofReal_cpow_I_mul x hx (-r)

/-- `conj (x^{i r}) = x^{-i r}` for `x > 0`, `r : ℝ`. -/
theorem conj_ofReal_cpow_I_mul (x : ℝ) (hx : 0 < x) (r : ℝ) :
    (starRingEnd ℂ) ((x : ℂ) ^ (Complex.I * (r : ℂ))) = (x : ℂ) ^ (-(Complex.I * (r : ℂ))) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hx)),
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hx))]
  simp only [← Complex.ofReal_log hx.le]
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofReal]
  ring

/-- `‖Σ_{1≤m≤M} m^{-i r}‖ = ‖Σ_{1≤m≤M} m^{i r}‖` (`m > 0`, so `m^{-ir}` is the conjugate). -/
theorem norm_sum_cpow_Icc (M : ℕ) (r : ℝ) :
    ‖∑ m ∈ Finset.Icc 1 M, (m : ℂ) ^ (-(Complex.I * (r : ℂ)))‖
      = ‖∑ m ∈ Finset.Icc 1 M, (m : ℂ) ^ (Complex.I * (r : ℂ))‖ := by
  have hconj : (∑ m ∈ Finset.Icc 1 M, (m : ℂ) ^ (-(Complex.I * (r : ℂ))))
      = (starRingEnd ℂ) (∑ m ∈ Finset.Icc 1 M, (m : ℂ) ^ (Complex.I * (r : ℂ))) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    exact (conj_ofReal_cpow_I_mul (m:ℝ) (by exact_mod_cast hm1) r).symm
  rw [hconj, Complex.norm_conj]

theorem hhat_reflection
    (hinv : ∀ u : ℝ, 0 < u →
      ((Work.GM.S2.psi u : ℝ) : ℂ) = (1 / (u : ℂ)) * MeasureTheory.integral MeasureTheory.volume
        (fun ξ : ℝ => Work.GM.S2.ghat1 ξ * (u : ℂ) ^ (2 * Real.pi * Complex.I * (ξ : ℂ))))
    (hint : MeasureTheory.Integrable Work.GM.S2.ghat1)
    (hfin : ∃ M : ℝ, 0 < M ∧ (∫ ξ, ‖Work.GM.S2.ghat1 ξ‖) ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (t Y : ℝ), 1 ≤ |t| → 1 ≤ Y →
      ‖∑ m ∈ Finset.Icc 1 (Nat.floor Y), Submission.GM.hhat t ((m : ℝ) * (N : ℝ))‖
        ≤ C * ∫ ξ, ‖Work.GM.S2.ghat1 ξ‖ * (1 + |t + 2 * Real.pi * ξ|) ^ (-(1 / 2 : ℝ)) *
            ‖∑ m ∈ Finset.Icc 1 (Nat.floor Y),
              (m : ℂ) ^ (Complex.I * ((t + 2 * Real.pi * ξ : ℝ) : ℂ))‖ := by
  refine ⟨10000, by norm_num, ?_⟩
  intro N hN t Y ht hY
  set M : ℕ := Nat.floor Y with hMdef
  have hM1 : 1 ≤ M := by
    rw [hMdef]
    exact Nat.le_floor (by exact_mod_cast hY : ((1:ℕ):ℝ) ≤ Y)
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hMpos : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM1
  have hgint : Integrable (fun ξ : ℝ => ‖Work.GM.S2.ghat1 ξ‖) := hint.norm
  have hid := hhat_sum_reflection hinv hint N M hN hM1 t
  have hlogN : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hle2 : (N:ℝ) ≤ 2 * (M:ℝ) * (N:ℝ) := by nlinarith [hNpos, hMpos]
  have hlog2 : Real.log (N:ℝ) ≤ Real.log (2 * (M:ℝ) * (N:ℝ)) := Real.log_le_log hNpos hle2
  -- the norm of the Dirichlet sum with `(mN)^{-iσ}` equals that with `m^{+iσ}`
  have hnorm_sum : ∀ ξ : ℝ,
      ‖∑ m ∈ Finset.Icc 1 M, ((m:ℂ)*(N:ℂ)) ^ (-(Complex.I * ((t + 2*Real.pi*ξ : ℝ):ℂ)))‖
      = ‖∑ m ∈ Finset.Icc 1 M, (m:ℂ) ^ (Complex.I * ((t + 2*Real.pi*ξ : ℝ):ℂ))‖ := by
    intro ξ
    have hsplit : (∑ m ∈ Finset.Icc 1 M, ((m:ℂ)*(N:ℂ)) ^ (-(Complex.I * ((t + 2*Real.pi*ξ : ℝ):ℂ))))
        = (N:ℂ) ^ (-(Complex.I * ((t + 2*Real.pi*ξ : ℝ):ℂ))) *
          (∑ m ∈ Finset.Icc 1 M, (m:ℂ) ^ (-(Complex.I * ((t + 2*Real.pi*ξ : ℝ):ℂ)))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      have hm1 : 0 < (m:ℝ) := by
        have : 1 ≤ m := (Finset.mem_Icc.mp hm).1
        exact_mod_cast this
      rw [show ((m:ℂ) * (N:ℂ)) = (((m:ℝ) * (N:ℝ) : ℝ) : ℂ) by push_cast; ring,
        ofReal_mul_cpow_pos hm1 hNpos]
      simp only [Complex.ofReal_natCast]
      exact mul_comm _ _
    rw [hsplit, norm_mul,
      show ‖(↑N : ℂ) ^ (-(Complex.I * ((t + 2*Real.pi*ξ : ℝ):ℂ)))‖ = 1 from
        norm_ofReal_cpow_neg_I_mul (N:ℝ) hNpos (t + 2*Real.pi*ξ),
      one_mul]
    exact norm_sum_cpow_Icc M (t + 2*Real.pi*ξ)
  -- the integrand of the reflection identity
  set Φ : ℝ → ℂ := fun ξ => Work.GM.S2.ghat1 ξ *
      (∑ m ∈ Finset.Icc 1 M, ((m:ℂ)*(N:ℂ)) ^ (-(Complex.I * ((t + 2*Real.pi*ξ : ℝ):ℂ)))) *
      (∫ s in Real.log (N:ℝ)..Real.log (2*(M:ℝ)*(N:ℝ)),
        Complex.exp (Complex.I * ((phase (t + 2*Real.pi*ξ) s : ℝ):ℂ))) with hΦdef
  -- the (real) integrand of the target bound
  set G : ℝ → ℝ := fun ξ => ‖Work.GM.S2.ghat1 ξ‖ * (1 + |t + 2*Real.pi*ξ|) ^ (-(1/2:ℝ)) *
      ‖∑ m ∈ Finset.Icc 1 M, (m:ℂ) ^ (Complex.I * ((t + 2*Real.pi*ξ : ℝ):ℂ))‖ with hGdef
  -- pointwise bound
  have hpt : ∀ ξ : ℝ, ‖Φ ξ‖ ≤ 10000 * G ξ := by
    intro ξ
    have hσ : ‖∫ s in Real.log (N:ℝ)..Real.log (2*(M:ℝ)*(N:ℝ)),
        Complex.exp (Complex.I * ((phase (t + 2*Real.pi*ξ) s : ℝ):ℂ))‖
        ≤ 10000 * (1 + |t + 2*Real.pi*ξ|) ^ (-(1/2:ℝ)) := by
      have h := phase_integral_bound_aux (Real.log (N:ℝ)) (Real.log (2*(M:ℝ)*(N:ℝ)))
        (t + 2*Real.pi*ξ) hlogN hlog2
      simpa only [Commons.Analysis.Oscillatory.osc] using h
    have h1 : 0 ≤ ‖Work.GM.S2.ghat1 ξ‖ := norm_nonneg _
    have h2 : 0 ≤ ‖∑ m ∈ Finset.Icc 1 M, (m:ℂ) ^ (Complex.I * ((t + 2*Real.pi*ξ : ℝ):ℂ))‖ :=
      norm_nonneg _
    rw [hΦdef, hGdef]
    simp only
    rw [norm_mul, norm_mul, hnorm_sum ξ]
    calc ‖Work.GM.S2.ghat1 ξ‖ *
          ‖∑ m ∈ Finset.Icc 1 M, (m:ℂ) ^ (Complex.I * ((t + 2*Real.pi*ξ : ℝ):ℂ))‖ *
          ‖∫ s in Real.log (N:ℝ)..Real.log (2*(M:ℝ)*(N:ℝ)),
            Complex.exp (Complex.I * ((phase (t + 2*Real.pi*ξ) s : ℝ):ℂ))‖
        ≤ ‖Work.GM.S2.ghat1 ξ‖ *
          ‖∑ m ∈ Finset.Icc 1 M, (m:ℂ) ^ (Complex.I * ((t + 2*Real.pi*ξ : ℝ):ℂ))‖ *
          (10000 * (1 + |t + 2*Real.pi*ξ|) ^ (-(1/2:ℝ))) :=
          mul_le_mul_of_nonneg_left hσ (mul_nonneg h1 h2)
      _ = 10000 * (‖Work.GM.S2.ghat1 ξ‖ * (1 + |t + 2*Real.pi*ξ|) ^ (-(1/2:ℝ)) *
          ‖∑ m ∈ Finset.Icc 1 M, (m:ℂ) ^ (Complex.I * ((t + 2*Real.pi*ξ : ℝ):ℂ))‖) := by ring
  -- integrability of `G`
  have hterm_cont : ∀ m ∈ Finset.Icc 1 M,
      Continuous (fun ξ : ℝ => (m:ℂ) ^ (Complex.I * ((t + 2*Real.pi*ξ : ℝ):ℂ))) := by
    intro m hm
    have hm0 : (m:ℂ) ≠ 0 := by
      have hm1 : (0:ℝ) < (m:ℝ) := by
        have : 1 ≤ m := (Finset.mem_Icc.mp hm).1
        exact_mod_cast this
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt hm1)
    rw [show (fun ξ : ℝ => (m:ℂ) ^ (Complex.I * ((t + 2*Real.pi*ξ : ℝ):ℂ)))
        = (fun ξ : ℝ => Complex.exp (Complex.log (m:ℂ) *
            (Complex.I * ((t + 2*Real.pi*ξ : ℝ):ℂ)))) from
      funext (fun ξ => Complex.cpow_def_of_ne_zero hm0 _)]
    fun_prop
  have hsum_cont : Continuous (fun ξ : ℝ =>
      ∑ m ∈ Finset.Icc 1 M, (m:ℂ) ^ (Complex.I * ((t + 2*Real.pi*ξ : ℝ):ℂ))) :=
    continuous_finsetSum _ hterm_cont
  have hGint : Integrable G := by
    rw [hGdef]
    refine Integrable.mono' (hgint.mul_const (M:ℝ)) ?_ ?_
    · refine (hint.aestronglyMeasurable.norm.mul ?_).mul (hsum_cont.norm.aestronglyMeasurable)
      have h1 : Continuous (fun ξ : ℝ => 1 + |t + 2*Real.pi*ξ|) := by fun_prop
      exact (h1.rpow_const (fun x => Or.inl (ne_of_gt (by positivity)))).aestronglyMeasurable
    · filter_upwards with ξ
      have h3 : ‖∑ m ∈ Finset.Icc 1 M, (m:ℂ) ^ (Complex.I * ((t + 2*Real.pi*ξ : ℝ):ℂ))‖ ≤ (M:ℝ) := by
        calc ‖∑ m ∈ Finset.Icc 1 M, (m:ℂ) ^ (Complex.I * ((t + 2*Real.pi*ξ : ℝ):ℂ))‖
            ≤ ∑ m ∈ Finset.Icc 1 M, ‖(m:ℂ) ^ (Complex.I * ((t + 2*Real.pi*ξ : ℝ):ℂ))‖ :=
              norm_sum_le _ _
          _ = ∑ m ∈ Finset.Icc 1 M, (1:ℝ) := by
              apply Finset.sum_congr rfl
              intro m hm
              have hm1 : 0 < (m:ℝ) := by
                have : 1 ≤ m := (Finset.mem_Icc.mp hm).1
                exact_mod_cast this
              exact norm_ofReal_cpow_I_mul (m:ℝ) hm1 (t + 2*Real.pi*ξ)
          _ = (M:ℝ) := by
              rw [Finset.sum_const, Nat.card_Icc]
              simp
      have h4 : (1 + |t + 2*Real.pi*ξ|) ^ (-(1/2:ℝ)) ≤ 1 := by
        rw [rpow_neg_half_eq _ (by positivity),
          div_le_one (Real.sqrt_pos.mpr (by positivity))]
        calc (1:ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
          _ ≤ Real.sqrt (1 + |t + 2*Real.pi*ξ|) :=
              Real.sqrt_le_sqrt (le_add_of_nonneg_right (abs_nonneg _))
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity)]
      calc ‖Work.GM.S2.ghat1 ξ‖ * (1 + |t + 2*Real.pi*ξ|) ^ (-(1/2:ℝ)) *
            ‖∑ m ∈ Finset.Icc 1 M, (m:ℂ) ^ (Complex.I * ((t + 2*Real.pi*ξ : ℝ):ℂ))‖
          ≤ ‖Work.GM.S2.ghat1 ξ‖ * 1 * (M:ℝ) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left h4 (norm_nonneg _)) h3 (norm_nonneg _) ?_
            positivity
        _ = ‖Work.GM.S2.ghat1 ξ‖ * (M:ℝ) := by ring
  -- assemble
  have hInt : ‖∑ m ∈ Finset.Icc 1 M, Submission.GM.hhat t ((m:ℝ)*(N:ℝ))‖ ≤ ∫ ξ, 10000 * G ξ := by
    rw [hid]
    refine (norm_integral_le_integral_norm _).trans ?_
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun ξ => norm_nonneg _))
      (hGint.const_mul 10000) (Filter.Eventually.of_forall (fun ξ => ?_))
    exact hpt ξ
  have hmain : ‖∑ m ∈ Finset.Icc 1 M, Submission.GM.hhat t ((m:ℝ)*(N:ℝ))‖
      ≤ 10000 * ∫ ξ, G ξ := hInt.trans (integral_const_mul 10000 G).le
  simpa only [hGdef] using hmain

end Work.GM.S2
