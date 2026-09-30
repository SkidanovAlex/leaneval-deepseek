import Mathlib
import Submission.Work.BMF.parseval.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The second window bound `window_J2_bound`

`window_J2_bound` bounds the mean square over `x ∈ [X, 2X]` of the smoothed Perron kernel
`∫_t dirP a X t · (x+h)^{2+it} · (∫_0^{2h/(x+h)} Φ(t,u) du)`

by the average over the smoothing variable `u ∈ [0, 2h/X]` of the frozen transform bound.

The proof is the classical two-step: Cauchy–Schwarz (Jensen) in the smoothing variable `u` for
every fixed `x`, followed by a change of variables `z = x + h`, an exchange of the two integrals
(Fubini/Tonelli) and the pointwise frozen bound `hfrozen`.

All auxiliary results are kept `private` so that they do not collide with the helpers of the
sibling file `window_J1_bound`.
-/

namespace Work.BMF

open MeasureTheory intervalIntegral
open scoped BigOperators

noncomputable section

/-! ## Generic measure-theoretic and continuity helpers -/

/-- Exchange two interval integrals of a function which is continuous on the plane. -/
private theorem swap_cont_intervalJ2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : ℝ → ℝ → E) (hcont : Continuous fun p : ℝ × ℝ => G p.1 p.2)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    ∫ x in a..b, ∫ u in c..d, G x u = ∫ u in c..d, ∫ x in a..b, G x u := by
  apply MeasureTheory.intervalIntegral_intervalIntegral_swap
  rw [Set.uIoc_of_le hab, Set.uIoc_of_le hcd]
  have hIntBig : IntegrableOn (Function.uncurry G) (Set.Icc a b ×ˢ Set.Icc c d) volume :=
    ContinuousOn.integrableOn_compact (f := Function.uncurry G) (K := Set.Icc a b ×ˢ Set.Icc c d)
      (isCompact_Icc.prod isCompact_Icc) hcont.continuousOn
  refine hIntBig.mono_set ?_
  intro p hp
  exact ⟨⟨le_of_lt hp.1.1, hp.1.2⟩, ⟨le_of_lt hp.2.1, hp.2.2⟩⟩

/-- Cauchy–Schwarz for the integral of a nonnegative continuous function on an interval:
`(∫ g)² ≤ (b - a) ∫ g²`. -/
private theorem sq_integral_leJ2 {g : ℝ → ℝ} (hg : Continuous g) (_hnn : ∀ u, 0 ≤ g u) {a b : ℝ}
    (hab : a ≤ b) :
    (∫ u in a..b, g u) ^ 2 ≤ (b - a) * ∫ u in a..b, g u ^ 2 := by
  rcases lt_or_eq_of_le hab with hlt | heq
  · have hba : 0 < b - a := sub_pos.mpr hlt
    have hgi : IntervalIntegrable g volume a b := hg.intervalIntegrable a b
    have hg2i : IntervalIntegrable (fun u => g u ^ 2) volume a b :=
      (hg.pow 2).intervalIntegrable a b
    set c : ℝ := (∫ u in a..b, g u) / (b - a) with hc
    have hcint : IntervalIntegrable (fun u => 2 * c * g u) volume a b := hgi.const_mul _
    have hsub : IntervalIntegrable (fun u => g u ^ 2 - 2 * c * g u) volume a b :=
      hg2i.sub hcint
    have hnonneg : 0 ≤ ∫ u in a..b, (g u - c) ^ 2 :=
      intervalIntegral.integral_nonneg hab (fun u _ => sq_nonneg _)
    have h_eq1 : (∫ u in a..b, (g u - c) ^ 2) = ∫ u in a..b, (g u ^ 2 - 2*c*g u + c^2) := by
      apply intervalIntegral.integral_congr
      intro u _
      ring
    have h_eq2 : (∫ u in a..b, (g u ^ 2 - 2*c*g u + c^2))
        = (∫ u in a..b, g u ^ 2) - 2*c*(∫ u in a..b, g u) + c^2*(b - a) := by
      rw [intervalIntegral.integral_add hsub intervalIntegrable_const]
      rw [intervalIntegral.integral_sub hg2i hcint]
      rw [intervalIntegral.integral_const_mul]
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring
    have hquad : 0 ≤ (∫ u in a..b, g u ^ 2) - 2*c*(∫ u in a..b, g u) + c^2*(b - a) := by
      rw [← h_eq2, ← h_eq1]; exact hnonneg
    have hS : c * (b - a) = ∫ u in a..b, g u := by
      rw [hc]; field_simp
    have hkey : c ^ 2 * (b - a) ≤ ∫ u in a..b, g u ^ 2 := by
      have h := hquad
      rw [← hS] at h
      nlinarith [h]
    calc (∫ u in a..b, g u) ^ 2 = c ^ 2 * (b - a) ^ 2 := by rw [← hS]; ring
      _ = (c ^ 2 * (b - a)) * (b - a) := by ring
      _ ≤ (∫ u in a..b, g u ^ 2) * (b - a) := mul_le_mul_of_nonneg_right hkey hba.le
      _ = (b - a) * ∫ u in a..b, g u ^ 2 := by ring
  · subst heq
    simp

/-- Cauchy–Schwarz for a continuous `E`-valued function on an interval:
`‖∫ G‖² ≤ (b - a) ∫ ‖G‖²`. -/
private theorem norm_integral_sq_leJ2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : ℝ → E) (hG : Continuous G) {a b : ℝ} (hab : a ≤ b) :
    ‖∫ u in a..b, G u‖ ^ 2 ≤ (b - a) * ∫ u in a..b, ‖G u‖ ^ 2 := by
  have h1 : ‖∫ u in a..b, G u‖ ≤ ∫ u in a..b, ‖G u‖ :=
    intervalIntegral.norm_integral_le_integral_norm hab
  have h2 : (∫ u in a..b, ‖G u‖) ^ 2 ≤ (b - a) * ∫ u in a..b, ‖G u‖ ^ 2 :=
    sq_integral_leJ2 hG.norm (fun _ => norm_nonneg _) hab
  calc ‖∫ u in a..b, G u‖ ^ 2 ≤ (∫ u in a..b, ‖G u‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (b - a) * ∫ u in a..b, ‖G u‖ ^ 2 := h2

/-- Joint continuity of the kernel `Phi` on the plane. -/
private theorem continuous_Phi_pairJ2 : Continuous fun q : ℝ × ℝ => Phi q.1 q.2 := by
  unfold Phi
  rw [continuous_iff_continuousAt]
  intro p
  apply ContinuousAt.div
  · apply ContinuousAt.sub
    · have hg : ContinuousAt (fun q : ℝ×ℝ => (1+q.2, 1+Complex.I*(q.1:ℂ))) p := by fun_prop
      have hf := Complex.continuousAt_ofReal_cpow (1+p.2) (1+Complex.I*(p.1:ℂ))
        (Or.inl (by simp : 0 < (1+Complex.I*(p.1:ℂ)).re))
      exact ContinuousAt.comp (f := fun q : ℝ×ℝ => (1+q.2, 1+Complex.I*(q.1:ℂ))) (x := p) hf hg
    · exact continuousAt_const
  · fun_prop
  · intro h; have := congrArg Complex.re h; simp at this

/-- Joint continuity of `(x,y) ↦ x^{2+iy}` for real `x`. -/
private theorem continuous_cpow_pairJ2 :
    Continuous fun q : ℝ × ℝ => ((q.1:ℝ):ℂ)^(2+Complex.I*(q.2:ℂ)) := by
  rw [continuous_iff_continuousAt]
  intro p
  have hg : ContinuousAt (fun q : ℝ×ℝ => (q.1, 2+Complex.I*(q.2:ℂ))) p := by fun_prop
  have hf := Complex.continuousAt_ofReal_cpow p.1 (2+Complex.I*(p.2:ℂ))
    (Or.inl (by simp : 0 < (2+Complex.I*(p.2:ℂ)).re))
  exact ContinuousAt.comp (f := fun q : ℝ×ℝ => (q.1, 2+Complex.I*(q.2:ℂ))) (x := p) hf hg

/-- Continuity of `t ↦ dirP a X t`. -/
private theorem continuous_dirP_wbJ2 (a : ℕ → ℂ) (X : ℝ) : Continuous (fun t : ℝ => dirP a X t) := by
  unfold dirP
  refine continuous_finsetSum _ (fun n _ => ?_)
  have h1 : Continuous (fun t : ℝ => -(1 + Complex.I*(t:ℂ))) := by continuity
  refine Continuous.mul continuous_const (Continuous.const_cpow h1 ?_)
  right
  intro t ht
  have := congrArg Complex.re ht
  simp at this

/-! ## The kernel `winGJ2` and its continuity -/

/-- The `(x,u)`-kernel `∫_t (dirP a X t * Phi t u) · x^{2+it} dt`, i.e. the frozen transform of
`window_J2`. -/
private def winGJ2 (a : ℕ → ℂ) (X T x u : ℝ) : ℂ :=
  ∫ t in (-T)..T, (dirP a X t * Phi t u) * (x:ℂ)^(2 + Complex.I*(t:ℂ))

set_option maxHeartbeats 1000000 in
/-- Joint continuity of `winGJ2`. -/
private theorem continuous_winGJ2 (a : ℕ → ℂ) (X T : ℝ) :
    Continuous fun p : ℝ × ℝ => winGJ2 a X T p.1 p.2 := by
  unfold winGJ2
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  apply Continuous.mul
  · exact ((continuous_dirP_wbJ2 a X).comp continuous_snd).mul
      (continuous_Phi_pairJ2.comp (continuous_snd.prodMk (continuous_snd.comp continuous_fst)))
  · exact continuous_cpow_pairJ2.comp ((continuous_fst.fst).prodMk continuous_snd)

/-- Continuity of the `x`-slice `x ↦ winGJ2 a X T x u`. -/
private theorem continuous_winGJ2_slice (a : ℕ → ℂ) (X T u : ℝ) :
    Continuous (fun x : ℝ => winGJ2 a X T x u) :=
  (continuous_winGJ2 a X T).comp (f := fun x : ℝ => (x, u))
    (continuous_id.prodMk continuous_const)

/-- Continuity of `u ↦ ∫_t ‖dirP a X t * Phi t u‖²`, the frozen density. -/
private theorem continuous_wDensityJ2 (a : ℕ → ℂ) (X T : ℝ) :
    Continuous (fun u : ℝ => ∫ t in (-T)..T, ‖dirP a X t * Phi t u‖^2) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun u t => ‖dirP a X t * Phi t u‖^2) (a₀ := -T) (b₀ := T)
  exact (((continuous_dirP_wbJ2 a X).comp continuous_snd).mul
    (continuous_Phi_pairJ2.comp (continuous_snd.prodMk continuous_fst))).norm.pow 2

/-! ## Interchanging the two smoothing integrals -/

/-- **Fubini step.**  Pull the `t`-dependent scalar into the `u`-integral and exchange the two
interval integrals. -/
private theorem window_J2_inner_eq (a : ℕ → ℂ) (X T x hLo : ℝ) (hX : 0 < X) (hT : 0 ≤ T)
    (hx : 0 < x) (hLo0 : 0 ≤ hLo) :
    (∫ t in (-T)..T, dirP a X t * ((x:ℂ)^(2 + Complex.I*(t:ℂ))) * (∫ u in (0:ℝ)..hLo, Phi t u))
      = ∫ u in (0:ℝ)..hLo, ∫ t in (-T)..T,
          (dirP a X t * Phi t u) * (x:ℂ)^(2 + Complex.I*(t:ℂ)) := by
  have hTle : -T ≤ T := by linarith
  have hcont : Continuous (fun p : ℝ × ℝ =>
      (dirP a X p.1 * (x:ℂ)^(2 + Complex.I*(p.1:ℂ))) * Phi p.1 p.2) := by
    have h1 : Continuous (fun p : ℝ×ℝ => dirP a X p.1 * (x:ℂ)^(2+Complex.I*(p.1:ℂ))) :=
      ((continuous_dirP_wbJ2 a X).comp continuous_fst).mul
        (continuous_cpow_pairJ2.comp (continuous_const.prodMk continuous_fst))
    exact h1.mul (continuous_Phi_pairJ2.comp (continuous_fst.prodMk continuous_snd))
  have hstep : (∫ t in (-T)..T, dirP a X t * ((x:ℂ)^(2 + Complex.I*(t:ℂ))) * (∫ u in (0:ℝ)..hLo, Phi t u))
      = ∫ t in (-T)..T, ∫ u in (0:ℝ)..hLo,
          (dirP a X t * (x:ℂ)^(2 + Complex.I*(t:ℂ))) * Phi t u := by
    apply intervalIntegral.integral_congr
    intro t _
    exact (intervalIntegral.integral_const_mul (dirP a X t * (x:ℂ)^(2 + Complex.I*(t:ℂ)))
      (fun u => Phi t u)).symm
  rw [hstep]
  rw [swap_cont_intervalJ2
        (fun t u => (dirP a X t * (x:ℂ)^(2+Complex.I*(t:ℂ))) * Phi t u) hcont hTle hLo0]
  apply intervalIntegral.integral_congr
  intro u _
  apply intervalIntegral.integral_congr
  intro t _
  ring

/-! ## The core measure-theoretic inequality -/

/-- **Core step.**  Cauchy–Schwarz in the smoothing variable `u`, the change of variables
`z = x + h`, Tonelli and the pointwise bound `hbound` give
`∫_X^{2X} ‖∫_0^{2h/(x+h)} V u (x+h) du‖² ≤ (2h/X) ∫_0^{2h/X} B`.

Only `V` and `B` are used through `hVc`, `hBint`, `hBnn` and `hbound`; the interval endpoints
`X+h`, `2X+h` all lie inside `[X,3X]` by `h ≤ X`. -/
private theorem window_J2_core (V : ℝ → ℝ → ℂ) (X h : ℝ) (hX : 0 < X) (hh : 0 < h) (hhX : h ≤ X)
    (B : ℝ → ℝ) (hVc : Continuous (Function.uncurry V))
    (hBint : IntervalIntegrable B volume (0:ℝ) (2*h/X))
    (hBnn : ∀ u, u ∈ Set.Icc (0:ℝ) (2*h/X) → 0 ≤ B u)
    (hbound : ∀ u, u ∈ Set.Icc (0:ℝ) (2*h/X) →
      (∫ z in (X+h)..(2*X+h), ‖V u z‖^2) ≤ B u) :
    (∫ x in X..(2*X), ‖∫ u in (0:ℝ)..(2*h/(x+h)), V u (x+h)‖^2)
      ≤ (2*h/X) * ∫ u in (0:ℝ)..(2*h/X), B u := by
  have hX2X : X ≤ 2*X := by linarith
  have h2h : 0 < 2*h := by linarith
  have h2hX : 0 ≤ 2*h/X := div_nonneg h2h.le hX.le
  -- a globally continuous version of the variable upper limit
  set Lex : ℝ → ℝ := fun x => 2*h/(max (x+h) X) with hLex
  have hLexc : Continuous Lex := by
    rw [hLex]
    apply Continuous.div continuous_const
    · exact (continuous_id.add continuous_const).max continuous_const
    · intro x
      exact ne_of_gt (lt_of_lt_of_le hX (le_max_right (x+h) X))
  have hLexeq : ∀ x ∈ Set.Icc X (2*X), Lex x = 2*h/(x+h) := by
    intro x hx
    have hx' : X ≤ x + h := by linarith [hx.1]
    simp only [hLex, max_eq_left hx']
  -- the LHS integrand, written with the globally continuous upper limit `Lex`
  have hFLc : Continuous (fun x : ℝ => ‖∫ u in (0:ℝ)..Lex x, V u (x+h)‖^2) := by
    have h1 : Continuous (fun x : ℝ => ∫ u in (0:ℝ)..Lex x, V u (x+h)) := by
      apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
        (f := fun x u => V u (x+h)) (s := Lex)
      · exact hVc.comp (f := fun p : ℝ × ℝ => (p.2, p.1 + h))
          (continuous_snd.prodMk (continuous_fst.add continuous_const))
      · exact hLexc
    exact h1.norm.pow 2
  -- the comparison integrand `(2h/X) ∫_0^{2h/X} ‖V u (x+h)‖²`
  have hGRc : Continuous (fun x : ℝ => (2*h/X) * ∫ u in (0:ℝ)..(2*h/X), ‖V u (x+h)‖^2) := by
    have h1 : Continuous (fun x : ℝ => ∫ u in (0:ℝ)..(2*h/X), ‖V u (x+h)‖^2) := by
      apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := fun x u => ‖V u (x+h)‖^2) (a₀ := 0) (b₀ := 2*h/X)
      exact (hVc.comp (f := fun p : ℝ × ℝ => (p.2, p.1 + h))
        (continuous_snd.prodMk (continuous_fst.add continuous_const))).norm.pow 2
    exact continuous_const.mul h1
  -- the `u`-integrand after the swap
  have hHic : Continuous (fun u : ℝ => ∫ z in (X+h)..(2*X+h), ‖V u z‖^2) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun u z => ‖V u z‖^2) (a₀ := X+h) (b₀ := 2*X+h)
    exact hVc.norm.pow 2
  have hslice : ∀ x : ℝ, Continuous (fun u : ℝ => V u (x+h)) := fun x =>
    hVc.comp (f := fun u : ℝ => (u, x + h)) (continuous_id.prodMk continuous_const)
  -- step 1: replace `2h/(x+h)` by its globally continuous version
  have hstep1 : (∫ x in X..(2*X), ‖∫ u in (0:ℝ)..(2*h/(x+h)), V u (x+h)‖^2)
      = ∫ x in X..(2*X), ‖∫ u in (0:ℝ)..Lex x, V u (x+h)‖^2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hxI : x ∈ Set.Icc X (2*X) := by
      rwa [Set.uIcc_of_le hX2X] at hx
    show ‖∫ u in (0:ℝ)..(2*h/(x+h)), V u (x+h)‖^2 = ‖∫ u in (0:ℝ)..Lex x, V u (x+h)‖^2
    rw [hLexeq x hxI]
  -- step 2: Cauchy–Schwarz in `u` and the pointwise comparison
  have hA : (∫ x in X..(2*X), ‖∫ u in (0:ℝ)..Lex x, V u (x+h)‖^2)
      ≤ ∫ x in X..(2*X), (2*h/X) * ∫ u in (0:ℝ)..(2*h/X), ‖V u (x+h)‖^2 := by
    apply intervalIntegral.integral_mono_on hX2X
    · exact hFLc.intervalIntegrable X (2*X)
    · exact hGRc.intervalIntegrable X (2*X)
    · intro x hx
      show ‖∫ u in (0:ℝ)..Lex x, V u (x+h)‖^2
          ≤ (2*h/X) * ∫ u in (0:ℝ)..(2*h/X), ‖V u (x+h)‖^2
      have hxh : 0 < x + h := by linarith [hx.1]
      have hLnn : 0 ≤ 2*h/(x+h) := div_nonneg h2h.le (by linarith)
      have hLle : 2*h/(x+h) ≤ 2*h/X := div_le_div_of_nonneg_left h2h.le hX (by linarith [hx.1])
      rw [hLexeq x hx]
      have hjensen : ‖∫ u in (0:ℝ)..(2*h/(x+h)), V u (x+h)‖^2
          ≤ (2*h/(x+h)) * ∫ u in (0:ℝ)..(2*h/(x+h)), ‖V u (x+h)‖^2 := by
        simpa only [sub_zero] using
          norm_integral_sq_leJ2 (fun u => V u (x+h)) (hslice x) hLnn
      have hmono : (∫ u in (0:ℝ)..(2*h/(x+h)), ‖V u (x+h)‖^2)
          ≤ ∫ u in (0:ℝ)..(2*h/X), ‖V u (x+h)‖^2 :=
        intervalIntegral.integral_mono_interval (le_refl 0) hLnn hLle
          (Filter.Eventually.of_forall (fun u => sq_nonneg (‖V u (x+h)‖)))
          (((hslice x).norm.pow 2).intervalIntegrable 0 (2*h/X))
      have hQ2nn : 0 ≤ ∫ u in (0:ℝ)..(2*h/X), ‖V u (x+h)‖^2 :=
        intervalIntegral.integral_nonneg h2hX
          (fun u _ => sq_nonneg (‖V u (x+h)‖))
      calc ‖∫ u in (0:ℝ)..(2*h/(x+h)), V u (x+h)‖^2
          ≤ (2*h/(x+h)) * ∫ u in (0:ℝ)..(2*h/(x+h)), ‖V u (x+h)‖^2 := hjensen
        _ ≤ (2*h/(x+h)) * ∫ u in (0:ℝ)..(2*h/X), ‖V u (x+h)‖^2 :=
            mul_le_mul_of_nonneg_left hmono hLnn
        _ ≤ (2*h/X) * ∫ u in (0:ℝ)..(2*h/X), ‖V u (x+h)‖^2 :=
            mul_le_mul_of_nonneg_right hLle hQ2nn
  -- step 3: change of variables `z = x + h`
  have hB : (∫ x in X..(2*X), (2*h/X) * ∫ u in (0:ℝ)..(2*h/X), ‖V u (x+h)‖^2)
      = (2*h/X) * ∫ z in (X+h)..(2*X+h), ∫ u in (0:ℝ)..(2*h/X), ‖V u z‖^2 := by
    rw [intervalIntegral.integral_const_mul]
    congr 1
    exact intervalIntegral.integral_comp_add_right
      (fun z => ∫ u in (0:ℝ)..(2*h/X), ‖V u z‖^2) h
  -- step 4: Tonelli
  have hC : (2*h/X) * ∫ z in (X+h)..(2*X+h), ∫ u in (0:ℝ)..(2*h/X), ‖V u z‖^2
      = (2*h/X) * ∫ u in (0:ℝ)..(2*h/X), ∫ z in (X+h)..(2*X+h), ‖V u z‖^2 := by
    rw [swap_cont_intervalJ2 (fun z u => ‖V u z‖^2)
      ((hVc.norm.pow 2).comp (f := fun p : ℝ × ℝ => (p.2, p.1))
        (continuous_snd.prodMk continuous_fst))
      (by linarith : X+h ≤ 2*X+h) h2hX]
  -- step 5: the pointwise frozen bound
  have hD : (2*h/X) * ∫ u in (0:ℝ)..(2*h/X), ∫ z in (X+h)..(2*X+h), ‖V u z‖^2
      ≤ (2*h/X) * ∫ u in (0:ℝ)..(2*h/X), B u := by
    apply mul_le_mul_of_nonneg_left _ h2hX
    apply intervalIntegral.integral_mono_on h2hX
    · exact hHic.intervalIntegrable 0 (2*h/X)
    · exact hBint
    · intro u hu
      exact hbound u hu
  rw [hstep1]
  exact hA.trans ((le_of_eq hB).trans ((le_of_eq hC).trans hD))

/-! ## The main bound -/

set_option maxHeartbeats 2000000 in
theorem window_J2_bound (a : ℕ → ℂ) (X h T C0 : ℝ) (hX : 0 < X) (hh : 0 < h) (hhX : h ≤ X) (hT : 0 ≤ T) (hC0 : 0 ≤ C0)
    (hfrozen : ∀ u : ℝ,
      (∫ z in X..(3*X), ‖∫ t in (-T)..T, (dirP a X t * Phi t u) * (z:ℂ)^(2 + Complex.I*(t:ℂ))‖^2)
        ≤ C0 * X^5 * (∫ t in (-T)..T, ‖dirP a X t * Phi t u‖^2)) :
    (∫ x in X..(2*X), ‖∫ t in (-T)..T, dirP a X t * (((x+h):ℂ)^(2 + Complex.I*(t:ℂ))) * (∫ u in (0:ℝ)..(2*h/(x+h)), Phi t u)‖^2)
      ≤ (2*h/X) * ∫ u in (0:ℝ)..(2*h/X), C0 * X^5 * (∫ t in (-T)..T, ‖dirP a X t * Phi t u‖^2) := by
  have hVc : Continuous (Function.uncurry (fun u z : ℝ => winGJ2 a X T z u)) :=
    (continuous_winGJ2 a X T).comp (f := fun p : ℝ × ℝ => (p.2, p.1))
      (continuous_snd.prodMk continuous_fst)
  have hBc : Continuous (fun u : ℝ => C0 * X^5 * (∫ t in (-T)..T, ‖dirP a X t * Phi t u‖^2)) :=
    continuous_const.mul (continuous_wDensityJ2 a X T)
  have hBint : IntervalIntegrable
      (fun u : ℝ => C0 * X^5 * (∫ t in (-T)..T, ‖dirP a X t * Phi t u‖^2)) volume (0:ℝ) (2*h/X) :=
    hBc.intervalIntegrable 0 (2*h/X)
  have hBnn : ∀ u, u ∈ Set.Icc (0:ℝ) (2*h/X) →
      0 ≤ C0 * X^5 * (∫ t in (-T)..T, ‖dirP a X t * Phi t u‖^2) := by
    intro u _
    exact mul_nonneg (mul_nonneg hC0 (pow_nonneg hX.le 5))
      (intervalIntegral.integral_nonneg (by linarith) (fun t _ => sq_nonneg _))
  have hbound : ∀ u, u ∈ Set.Icc (0:ℝ) (2*h/X) →
      (∫ z in (X+h)..(2*X+h), ‖winGJ2 a X T z u‖^2)
        ≤ C0 * X^5 * (∫ t in (-T)..T, ‖dirP a X t * Phi t u‖^2) := by
    intro u _
    have hslice : Continuous (fun z : ℝ => ‖winGJ2 a X T z u‖^2) :=
      (continuous_winGJ2_slice a X T u).norm.pow 2
    have hmono : (∫ z in (X+h)..(2*X+h), ‖winGJ2 a X T z u‖^2)
        ≤ ∫ z in X..(3*X), ‖winGJ2 a X T z u‖^2 :=
      intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
        (Filter.Eventually.of_forall (fun z => sq_nonneg _))
        (hslice.intervalIntegrable X (3*X))
    exact le_trans hmono (hfrozen u)
  have hLHS : (∫ x in X..(2*X), ‖∫ t in (-T)..T, dirP a X t * (((x+h):ℂ)^(2 + Complex.I*(t:ℂ))) * (∫ u in (0:ℝ)..(2*h/(x+h)), Phi t u)‖^2)
      = ∫ x in X..(2*X), ‖∫ u in (0:ℝ)..(2*h/(x+h)), winGJ2 a X T (x+h) u‖^2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hxge : X ≤ x := by
      rw [Set.uIcc_of_le (by linarith : X ≤ 2*X)] at hx
      exact hx.1
    have hxh : 0 < x + h := by linarith
    have hLnn : 0 ≤ 2*h/(x+h) := div_nonneg (by linarith) (by linarith)
    have hbase : ((x:ℂ) + (h:ℂ)) = ((x+h : ℝ) : ℂ) := by push_cast; ring
    simp only [winGJ2]
    rw [hbase]
    rw [window_J2_inner_eq a X T (x+h) (2*h/(x+h)) hX hT hxh hLnn]
  rw [hLHS]
  exact window_J2_core (fun u z : ℝ => winGJ2 a X T z u) X h hX hh hhX
    (fun u => C0 * X^5 * (∫ t in (-T)..T, ‖dirP a X t * Phi t u‖^2))
    hVc hBint hBnn hbound

end

end Work.BMF
