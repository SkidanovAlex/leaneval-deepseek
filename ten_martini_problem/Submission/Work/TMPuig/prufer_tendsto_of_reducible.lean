import Mathlib
import Submission.Work.TMContract.Components
import Submission.Work.TMPuig.Defs
import Submission.Work.TMPuig.pruferStep_basic
import Submission.Work.TMC13.Basic
import Submission.Work.TMComp.IDSPrufer.contx
import Submission.Work.TMPuig.pos_lift_exists

open Matrix Filter MeasureTheory Set
open Work.TMContract
open scoped Topology

noncomputable section

namespace Work.TMPuig

/-- `dvec t = (cos πt, sin πt)`: the direction of half-turn angle `t`. -/
def dvec (t : ℝ) : Fin 2 → ℝ := ![Real.cos (Real.pi * t), Real.sin (Real.pi * t)]

lemma dvec_zero (t : ℝ) : dvec t 0 = Real.cos (Real.pi * t) := rfl
lemma dvec_one (t : ℝ) : dvec t 1 = Real.sin (Real.pi * t) := rfl

/-- `g` is a positive projective lift of the matrix `M`: continuous, degree one, and
`M dvec t = ρ dvec (g t)` with `ρ > 0`. -/
def IsPosLiftM (M : Matrix (Fin 2) (Fin 2) ℝ) (g : ℝ → ℝ) : Prop :=
  Continuous g ∧ (∀ t, g (t + 1) = g t + 1) ∧
    ∀ t, ∃ ρ : ℝ, 0 < ρ ∧ M.mulVec (dvec t) = ρ • dvec (g t)

/-- The almost Mathieu coefficient `a(y) = E - 2λ cos 2πy`. -/
def amoA (lam E y : ℝ) : ℝ := E - 2 * lam * Real.cos (2 * Real.pi * y)

lemma continuous_amoA (lam E : ℝ) : Continuous (amoA lam E) := by
  unfold amoA; fun_prop

/-! ## The complex unit circle point -/

/-- `vcC t = exp (i π t)`, the point of the unit circle at angle `πt`. -/
def vcC (t : ℝ) : ℂ := Complex.exp (((Real.pi : ℂ) * (t : ℂ)) * Complex.I)

lemma vcC_re (t : ℝ) : (vcC t).re = Real.cos (Real.pi * t) := by
  rw [vcC, ← Complex.ofReal_mul, Complex.exp_ofReal_mul_I_re]

lemma vcC_im (t : ℝ) : (vcC t).im = Real.sin (Real.pi * t) := by
  rw [vcC, ← Complex.ofReal_mul, Complex.exp_ofReal_mul_I_im]

/-- If `vcC s = vcC s'` then `s - s'` is an even integer. -/
lemma vcC_inj {s s' : ℝ} (h : vcC s = vcC s') : ∃ k : ℤ, s - s' = 2 * (k : ℝ) := by
  have h2 : Complex.exp ((((Real.pi : ℂ) * s) * Complex.I)
      - (((Real.pi : ℂ) * s') * Complex.I)) = 1 := by
    rw [Complex.exp_sub]; simp only [vcC] at h; rw [h, div_self (Complex.exp_ne_zero _)]
  rw [Complex.exp_eq_one_iff] at h2
  obtain ⟨n, hn⟩ := h2
  have himL : ((((Real.pi : ℂ) * s) * Complex.I)
      - (((Real.pi : ℂ) * s') * Complex.I)).im = Real.pi * (s - s') := by
    simp only [Complex.sub_im, Complex.mul_I_im, ← Complex.ofReal_mul, Complex.ofReal_re]
    ring
  have himR : ((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)).im = (n : ℝ) * (2 * Real.pi) := by
    simp [Complex.mul_im, Complex.I_re, Complex.I_im]
  have h := congrArg (fun z : ℂ => z.im) hn
  rw [himL, himR] at h
  refine ⟨n, ?_⟩
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp at h
  linarith [h]

/-- If `dvec s = c • dvec s'` with `c > 0` then `s - s'` is an even integer. -/
lemma dvec_smul_pos {s s' c : ℝ} (hc : 0 < c) (h : dvec s = c • dvec s') :
    ∃ k : ℤ, s - s' = 2 * (k : ℝ) := by
  have h0 : Real.cos (Real.pi * s) = c * Real.cos (Real.pi * s') := by
    have := congrFun h 0; simpa [dvec_zero] using this
  have h1 : Real.sin (Real.pi * s) = c * Real.sin (Real.pi * s') := by
    have := congrFun h 1; simpa [dvec_one] using this
  have hc2 : c ^ 2 = 1 := by
    have h2 := Real.cos_sq_add_sin_sq (Real.pi * s)
    have h3 := Real.cos_sq_add_sin_sq (Real.pi * s')
    rw [h0, h1] at h2
    nlinarith [h2, h3]
  have hc1 : c = 1 := by nlinarith [hc, hc2, sq_nonneg c]
  subst hc1
  simp only [one_mul] at h0 h1
  refine vcC_inj ?_
  apply Complex.ext
  · rw [vcC_re, vcC_re]; exact h0
  · rw [vcC_im, vcC_im]; exact h1

/-! ## Generic positive-lift lemmas -/

lemma isPosLiftM_comp {M N : Matrix (Fin 2) (Fin 2) ℝ} {g g' : ℝ → ℝ}
    (hg : IsPosLiftM M g) (hg' : IsPosLiftM N g') :
    IsPosLiftM (M * N) (g ∘ g') := by
  refine ⟨hg.1.comp hg'.1, ?_, ?_⟩
  · intro t
    show g (g' (t + 1)) = g (g' t) + 1
    rw [hg'.2.1 t, hg.2.1]
  · intro t
    obtain ⟨ρ, hρ, h1⟩ := hg.2.2 (g' t)
    obtain ⟨σ, hσ, h2⟩ := hg'.2.2 t
    refine ⟨ρ * σ, mul_pos hρ hσ, ?_⟩
    show (M * N).mulVec (dvec t) = (ρ * σ) • dvec (g (g' t))
    rw [← Matrix.mulVec_mulVec, h2, Matrix.mulVec_smul, h1, smul_smul, mul_comm]

lemma isPosLiftM_rot (c : ℝ) : IsPosLiftM (rot c) (fun t => t + 2 * c) := by
  refine ⟨by fun_prop, fun t => by ring, fun t => ⟨1, one_pos, ?_⟩⟩
  rw [one_smul]
  have hc : (rot c).mulVec (dvec t) = dvec (t + 2 * c) := by
    ext i
    fin_cases i <;>
      simp only [Matrix.mulVec_fin_two, rot, dvec, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.of_apply, Fin.zero_eta, Fin.mk_one,
        Fin.isValue] <;>
      rw [show Real.pi * (t + 2 * c) = 2 * Real.pi * c + Real.pi * t by ring] <;>
      simp only [Real.cos_add, Real.sin_add] <;> ring
  exact hc

/-- The Prüfer step is a positive lift of the transfer matrix. -/
lemma isPosLiftM_pruferStep (lam E y : ℝ) :
    IsPosLiftM (tmR lam E y) (pruferStep (amoA lam E y)) := by
  refine ⟨pruferStep_continuous_aux _, fun t => TMComp.RotBasics.pruferStep_add_one _ _, ?_⟩
  intro t
  obtain ⟨ρ, hρ, h1, h2⟩ := pruferStep_posLift_coord (amoA lam E y) t
  refine ⟨ρ⁻¹, inv_pos.mpr hρ, ?_⟩
  have h1' : amoA lam E y * Real.cos (Real.pi * t) - Real.sin (Real.pi * t)
      = ρ⁻¹ * Real.cos (Real.pi * pruferStep (amoA lam E y) t) := by
    rw [← h1, inv_mul_cancel_left₀ (ne_of_gt hρ)]
  have h2' : Real.cos (Real.pi * t)
      = ρ⁻¹ * Real.sin (Real.pi * pruferStep (amoA lam E y) t) := by
    rw [← h2, inv_mul_cancel_left₀ (ne_of_gt hρ)]
  ext i
  fin_cases i
  · simp only [Matrix.mulVec_fin_two, tmR, dvec_zero, dvec_one, Pi.smul_apply, smul_eq_mul,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.head_cons, Matrix.head_fin_const, Matrix.tail_cons,
      Fin.zero_eta, Fin.mk_one, Fin.isValue]
    show (E - 2 * lam * Real.cos (2 * Real.pi * y)) * Real.cos (Real.pi * t)
        + -1 * Real.sin (Real.pi * t) = ρ⁻¹ * Real.cos (Real.pi * pruferStep (amoA lam E y) t)
    rw [show E - 2 * lam * Real.cos (2 * Real.pi * y) = amoA lam E y from rfl]
    linarith [h1']
  · simp only [Matrix.mulVec_fin_two, tmR, dvec_zero, dvec_one, Pi.smul_apply, smul_eq_mul,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.head_cons, Matrix.head_fin_const, Matrix.tail_cons,
      Fin.zero_eta, Fin.mk_one, Fin.isValue]
    simpa using h2'

/-- Two positive lifts of the same matrix differ by an even integer. -/
lemma eq_add_int_even {M : Matrix (Fin 2) (Fin 2) ℝ} {g g' : ℝ → ℝ}
    (hg : IsPosLiftM M g) (hg' : IsPosLiftM M g') :
    ∃ j : ℤ, ∀ t, g t = g' t + 2 * (j : ℝ) := by
  have hkey : ∀ t : ℝ, ∃ k : ℤ, (g t - g' t) / 2 = (k : ℝ) := by
    intro t
    obtain ⟨ρ, hρ, h1⟩ := hg.2.2 t
    obtain ⟨σ, hσ, h2⟩ := hg'.2.2 t
    have hs : dvec (g t) = (σ / ρ) • dvec (g' t) := by
      have hρne : ρ ≠ 0 := ne_of_gt hρ
      have heq : ρ • dvec (g t) = σ • dvec (g' t) := h1.symm.trans h2
      have hmain : ρ⁻¹ • (ρ • dvec (g t)) = ρ⁻¹ • (σ • dvec (g' t)) := by rw [heq]
      rw [smul_smul, smul_smul, inv_mul_cancel₀ hρne, one_smul] at hmain
      rw [div_eq_inv_mul]; exact hmain
    obtain ⟨k, hk⟩ := dvec_smul_pos (div_pos hσ hρ) hs
    exact ⟨k, by rw [hk]; ring⟩
  obtain ⟨j, hj⟩ := Work.TMC13.exists_int_eq_const (hg.1.sub hg'.1 |>.div_const 2) hkey
  refine ⟨j, fun t => ?_⟩
  have h := hj t
  have h2 : g t - g' t = 2 * (j : ℝ) := by
    have := congrArg (fun x : ℝ => 2 * x) h
    rw [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] at this
    exact this
  linarith [h2]

lemma pruferStep_zero (a : ℝ) :
    pruferStep a 0 = 1 / 2 - Real.arctan a / Real.pi := by
  rw [pruferStep]
  norm_num
  ring

lemma continuous_pruferStep_param_zero :
    Continuous (fun a : ℝ => pruferStep a 0) := by
  simp only [pruferStep_zero]
  fun_prop

/-! ## The model estimate

Given a positive lift `h` of `B` whose one-step identity models the Prüfer iteration up to
the constant `2c + 2j`, the phase-averaged Prüfer angle converges to `2c + 2j`. -/

lemma tendsto_avg_of_model (α lam E c : ℝ) (j : ℤ) (h : ℝ → ℝ → ℝ) (M : ℝ)
    (hcont : Continuous (Function.uncurry h))
    (hmod : ∀ y t : ℝ,
      h (y + α) (pruferStep (amoA lam E y) t) = h y t + 2 * c + 2 * (j : ℝ))
    (hM : ∀ y t : ℝ, |h y t - t| ≤ M) :
    Tendsto (fun n : ℕ => (∫ x in (0 : ℝ)..1, pruferIter α lam E n x 0) / (n : ℝ))
      atTop (𝓝 (2 * c + 2 * (j : ℝ))) := by
  set L : ℝ := 2 * c + 2 * (j : ℝ) with hL
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (h 0 0 - 0)) (hM 0 0)
  have hmain : ∀ n : ℕ, ∀ x : ℝ,
      h (x + (n : ℝ) * α) (pruferIter α lam E n x 0) = h x 0 + (n : ℝ) * L := by
    intro n
    induction n with
    | zero => intro x; simp [hL, pruferIter]
    | succ m ih =>
        intro x
        have hstep : pruferIter α lam E (m + 1) x 0
            = pruferStep (amoA lam E (x + (m : ℝ) * α)) (pruferIter α lam E m x 0) := rfl
        have h1 := hmod (x + (m : ℝ) * α) (pruferIter α lam E m x 0)
        have hcoord : x + (m : ℝ) * α + α = x + ((m : ℕ) + 1 : ℕ) * α := by push_cast; ring
        rw [hstep, ← hcoord, h1, ih, hL]
        push_cast; ring
  have hbd : ∀ n : ℕ, ∀ x : ℝ, |pruferIter α lam E n x 0 - (h x 0 + (n : ℝ) * L)| ≤ M := by
    intro n x
    rw [← hmain n x, abs_sub_comm]
    exact hM (x + (n : ℝ) * α) (pruferIter α lam E n x 0)
  set Q : ℝ := ∫ x in (0 : ℝ)..1, h x 0 with hQ
  have hcont_h0 : Continuous (fun x : ℝ => h x 0) :=
    hcont.comp (continuous_id.prodMk continuous_const)
  have hQint : IntervalIntegrable (fun x : ℝ => h x 0) volume (0 : ℝ) 1 :=
    hcont_h0.intervalIntegrable _ _
  have hkey : ∀ n : ℕ, 0 < n →
      |(∫ x in (0 : ℝ)..1, pruferIter α lam E n x 0) / (n : ℝ) - L| ≤ (M + |Q|) / (n : ℝ) := by
    intro n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hcont_u : Continuous (fun x : ℝ => pruferIter α lam E n x 0) :=
      Work.TMComp.IDSPrufer.contx α lam E n
    have hIu : IntervalIntegrable (fun x : ℝ => pruferIter α lam E n x 0) volume (0:ℝ) 1 :=
      hcont_u.intervalIntegrable _ _
    have hconst : IntervalIntegrable (fun _ : ℝ => (n : ℝ) * L) volume (0:ℝ) 1 :=
      intervalIntegrable_const
    have hmI : IntervalIntegrable (fun x : ℝ => h x 0 + (n : ℝ) * L) volume (0:ℝ) 1 :=
      hQint.add hconst
    have hdiff : ∫ x in (0 : ℝ)..1, (pruferIter α lam E n x 0 - (h x 0 + (n : ℝ) * L))
        = (∫ x in (0 : ℝ)..1, pruferIter α lam E n x 0) - (Q + (n : ℝ) * L) := by
      rw [intervalIntegral.integral_sub hIu hmI, intervalIntegral.integral_add hQint hconst,
        intervalIntegral.integral_const, ← hQ]
      norm_num
    have hbnd : |∫ x in (0 : ℝ)..1, (pruferIter α lam E n x 0 - (h x 0 + (n : ℝ) * L))| ≤ M := by
      calc |∫ x in (0 : ℝ)..1, (pruferIter α lam E n x 0 - (h x 0 + (n : ℝ) * L))|
          ≤ ∫ x in (0 : ℝ)..1, |pruferIter α lam E n x 0 - (h x 0 + (n : ℝ) * L)| :=
            intervalIntegral.abs_integral_le_integral_abs (by norm_num)
        _ ≤ ∫ x in (0 : ℝ)..1, M := by
            refine intervalIntegral.integral_mono_on (by norm_num) ?_ intervalIntegrable_const ?_
            · exact (hIu.sub hmI).abs
            · intro x _; exact hbd n x
        _ = M := by rw [intervalIntegral.integral_const]; norm_num
    have hsub : |(∫ x in (0 : ℝ)..1, pruferIter α lam E n x 0) - (Q + (n : ℝ) * L)| ≤ M := by
      rw [← hdiff]; exact hbnd
    have hdiv : (∫ x in (0 : ℝ)..1, pruferIter α lam E n x 0) / (n : ℝ) - L
        = ((∫ x in (0 : ℝ)..1, pruferIter α lam E n x 0) - (Q + (n : ℝ) * L)) / (n : ℝ)
          + Q / (n : ℝ) := by
      field_simp
      ring
    calc |(∫ x in (0 : ℝ)..1, pruferIter α lam E n x 0) / (n : ℝ) - L|
        = |((∫ x in (0 : ℝ)..1, pruferIter α lam E n x 0) - (Q + (n : ℝ) * L)) / (n : ℝ)
            + Q / (n : ℝ)| := by rw [hdiv]
      _ ≤ |((∫ x in (0 : ℝ)..1, pruferIter α lam E n x 0) - (Q + (n : ℝ) * L)) / (n : ℝ)|
            + |Q / (n : ℝ)| := abs_add_le _ _
      _ = |(∫ x in (0 : ℝ)..1, pruferIter α lam E n x 0) - (Q + (n : ℝ) * L)| / (n : ℝ)
            + |Q| / (n : ℝ) := by rw [abs_div, abs_div, abs_of_pos hnpos]
      _ ≤ M / (n : ℝ) + |Q| / (n : ℝ) :=
            add_le_add (div_le_div_of_nonneg_right hsub (le_of_lt hnpos)) le_rfl
      _ = (M + |Q|) / (n : ℝ) := by ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hg : Tendsto (fun n : ℕ => (M + |Q|) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  refine squeeze_zero' ?_ ?_ hg
  · filter_upwards with n
    rw [Real.norm_eq_abs]; exact abs_nonneg _
  · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    rw [Real.norm_eq_abs]
    exact hkey n hn

/-! ## The one-step lift identity -/

/-- The conjugacy plus positivity of the lifts forces the one-step Prüfer identity with an
*even* integer constant. -/
lemma lift_identity (α lam E c : ℝ) {B : ℝ → Matrix (Fin 2) (Fin 2) ℝ} (h : ℝ → ℝ → ℝ)
    (hcont : Continuous (Function.uncurry h))
    (hl : ∀ y : ℝ, IsPosLiftM (B y) (h y))
    (hconj : ∀ x : ℝ, B (x + α) * tmR lam E x = rot c * B x) :
    ∃ j : ℤ, ∀ y t : ℝ,
      h (y + α) (pruferStep (amoA lam E y) t) = h y t + 2 * c + 2 * (j : ℝ) := by
  have hex : ∀ y : ℝ, ∃ j : ℤ, ∀ t : ℝ,
      h (y + α) (pruferStep (amoA lam E y) t) = h y t + 2 * c + 2 * (j : ℝ) := by
    intro y
    have h1 : IsPosLiftM (B (y + α) * tmR lam E y)
        (h (y + α) ∘ pruferStep (amoA lam E y)) :=
      isPosLiftM_comp (hl (y + α)) (isPosLiftM_pruferStep lam E y)
    have h2 : IsPosLiftM (rot c * B y) ((fun t => t + 2 * c) ∘ h y) :=
      isPosLiftM_comp (isPosLiftM_rot c) (hl y)
    have h2' : IsPosLiftM (B (y + α) * tmR lam E y) ((fun t => t + 2 * c) ∘ h y) := by
      rw [hconj y]; exact h2
    obtain ⟨j, hj⟩ := eq_add_int_even h1 h2'
    exact ⟨j, fun t => by simpa only [Function.comp_apply] using hj t⟩
  choose j hj using hex
  have hcontJ : Continuous (fun y : ℝ => (j y : ℝ)) := by
    have heq : (fun y : ℝ => (j y : ℝ)) = fun y : ℝ =>
        (h (y + α) (pruferStep (amoA lam E y) 0) - h y 0 - 2 * c) / 2 := by
      funext y
      have h0 := hj y 0
      rw [h0]; ring
    rw [heq]
    have h1 : Continuous (fun y : ℝ => h (y + α) (pruferStep (amoA lam E y) 0)) :=
      hcont.comp ((continuous_id.add continuous_const).prodMk
        (Work.TMComp.IDSPrufer.pruferStep_pair_cont.comp
          ((continuous_amoA lam E).prodMk continuous_const)))
    have h2c : Continuous (fun y : ℝ => h y 0) :=
      hcont.comp (continuous_id.prodMk continuous_const)
    exact ((h1.sub h2c).sub continuous_const).div_const 2
  obtain ⟨k, hk⟩ := Work.TMC13.exists_int_eq_const hcontJ (fun y => ⟨j y, rfl⟩)
  refine ⟨k, fun y t => ?_⟩
  have hjk : ((j y : ℤ) : ℝ) = ((k : ℤ) : ℝ) := by exact_mod_cast hk y
  rw [hj y t, hjk]

/-- Assembly: a positive lift `h` of `B` with bounded displacement models the Prüfer
iteration, and the averaged Prüfer angle converges to the corresponding lift of the rotation
number. -/
lemma tendsto_of_lift (α lam E c : ℝ) {B : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (h : ℝ → ℝ → ℝ) (M : ℝ)
    (hcont : Continuous (Function.uncurry h))
    (hl : ∀ y : ℝ, IsPosLiftM (B y) (h y))
    (hM : ∀ y t : ℝ, |h y t - t| ≤ M)
    (hconj : ∀ y : ℝ, B (y + α) * tmR lam E y = rot c * B y) :
    ∃ j : ℤ, Tendsto
      (fun n : ℕ => (∫ x in (0 : ℝ)..1, pruferIter α lam E n x 0) / (n : ℝ))
      atTop (𝓝 (2 * c + 2 * (j : ℝ))) := by
  obtain ⟨j, hj⟩ := lift_identity α lam E c h hcont hl hconj
  exact ⟨j, tendsto_avg_of_model α lam E c j h M hcont hj hM⟩


/-- **Puig: convergence of the phase-averaged Prüfer angle.**  If the transfer cocycle at
`(λ,E)` is reducible to the rotation `rot c` by a `1`-periodic, degree-`0` conjugacy `B`
in `SL(2,ℝ)`, then the phase average of the Prüfer angle converges to `2c` modulo `2`. -/
theorem prufer_tendsto_of_reducible (α lam E c : ℝ)
    {B : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hB : ∀ i j, AnalyticOnNhd ℝ (fun x => B x i j) univ)
    (hper : ∀ x, B (x + 1) = B x) (hdet : ∀ x, (B x).det = 1)
    (hdeg : Work.TMContract.HasDegree B 0)
    (hconj : ∀ x, B (x + α) * Work.TMContract.tmR lam E x = Work.TMContract.rot c * B x) :
    ∃ j : ℤ, Filter.Tendsto
      (fun n : ℕ => (∫ x in (0 : ℝ)..1, Work.TMContract.pruferIter α lam E n x 0) / (n : ℝ))
      Filter.atTop (nhds (2 * c + 2 * (j : ℝ))) := by
  obtain ⟨h, hcont, hshift, hpery, hlift, M, hM⟩ := pos_lift_exists B hB hper hdet hdeg
  refine tendsto_of_lift α lam E c h M hcont ?_ hM hconj
  intro y
  exact ⟨hcont.comp (continuous_const.prodMk continuous_id), hshift y, hlift y⟩

end Work.TMPuig

