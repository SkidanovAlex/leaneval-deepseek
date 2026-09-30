import Mathlib
import Submission.Work.BMF.parseval.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open MeasureTheory intervalIntegral
open scoped BigOperators

noncomputable section

/-! ## Generic measure-theoretic helpers -/

/-- Exchange two interval integrals of a function which is continuous on the plane. -/
theorem swap_cont_interval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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
theorem sq_integral_le {g : ℝ → ℝ} (hg : Continuous g) (hnn : ∀ u, 0 ≤ g u) {a b : ℝ}
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
theorem norm_integral_sq_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : ℝ → E) (hG : Continuous G) {a b : ℝ} (hab : a ≤ b) :
    ‖∫ u in a..b, G u‖ ^ 2 ≤ (b - a) * ∫ u in a..b, ‖G u‖ ^ 2 := by
  have h1 : ‖∫ u in a..b, G u‖ ≤ ∫ u in a..b, ‖G u‖ :=
    intervalIntegral.norm_integral_le_integral_norm hab
  have h2 : (∫ u in a..b, ‖G u‖) ^ 2 ≤ (b - a) * ∫ u in a..b, ‖G u‖ ^ 2 :=
    sq_integral_le hG.norm (fun _ => norm_nonneg _) hab
  calc ‖∫ u in a..b, G u‖ ^ 2 ≤ (∫ u in a..b, ‖G u‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (b - a) * ∫ u in a..b, ‖G u‖ ^ 2 := h2

/-- Joint continuity of `Phi`. -/
theorem continuous_Phi_pair : Continuous fun q : ℝ × ℝ => Phi q.1 q.2 := by
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

/-- Joint continuity of `(x,y) ↦ x^{2+iy}` (for real `x`). -/
theorem continuous_cpow_pair :
    Continuous fun q : ℝ × ℝ => ((q.1:ℝ):ℂ)^(2+Complex.I*(q.2:ℂ)) := by
  rw [continuous_iff_continuousAt]
  intro p
  have hg : ContinuousAt (fun q : ℝ×ℝ => (q.1, 2+Complex.I*(q.2:ℂ))) p := by fun_prop
  have hf := Complex.continuousAt_ofReal_cpow p.1 (2+Complex.I*(p.2:ℂ))
    (Or.inl (by simp : 0 < (2+Complex.I*(p.2:ℂ)).re))
  exact ContinuousAt.comp (f := fun q : ℝ×ℝ => (q.1, 2+Complex.I*(q.2:ℂ))) (x := p) hf hg

/-- Continuity of `t ↦ dirP a X t`. -/
theorem continuous_dirP_wb (a : ℕ → ℂ) (X : ℝ) : Continuous (fun t : ℝ => dirP a X t) := by
  unfold dirP
  refine continuous_finsetSum _ (fun n _ => ?_)
  have h1 : Continuous (fun t : ℝ => -(1 + Complex.I*(t:ℂ))) := by continuity
  refine Continuous.mul continuous_const (Continuous.const_cpow h1 ?_)
  right
  intro t ht
  have := congrArg Complex.re ht
  simp at this

/-! ## The kernel of the bound -/

/-- The `(x,u)`-kernel `∫_t (dirP a X t * Phi t u) · x^{2+it} dt`. -/
def winG (a : ℕ → ℂ) (X T x u : ℝ) : ℂ :=
  ∫ t in (-T)..T, (dirP a X t * Phi t u) * (x:ℂ)^(2 + Complex.I*(t:ℂ))

set_option maxHeartbeats 1000000 in
/-- Joint continuity of `winG`. -/
theorem continuous_winG (a : ℕ → ℂ) (X T : ℝ) :
    Continuous fun p : ℝ × ℝ => winG a X T p.1 p.2 := by
  unfold winG
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  apply Continuous.mul
  · exact ((continuous_dirP_wb a X).comp continuous_snd).mul
      (continuous_Phi_pair.comp (continuous_snd.prodMk (continuous_snd.comp continuous_fst)))
  · exact continuous_cpow_pair.comp ((continuous_fst.fst).prodMk continuous_snd)

/-- Continuity of a slice `u ↦ winG a X T x u` of `winG`. -/
theorem continuous_winG_slice (a : ℕ → ℂ) (X T x : ℝ) :
    Continuous (fun u : ℝ => winG a X T x u) :=
  (continuous_winG a X T).comp (f := fun u : ℝ => (x, u))
    (continuous_const.prodMk continuous_id)

/-! ## The main bound -/

set_option maxHeartbeats 2000000 in
theorem window_J1_bound (a : ℕ → ℂ) (X h T C0 : ℝ) (hX : 0 < X) (hh : 0 < h) (hhX : h ≤ X) (hT : 0 ≤ T) (hC0 : 0 ≤ C0)
    (hfrozen : ∀ u : ℝ,
      (∫ x in X..(2*X), ‖∫ t in (-T)..T, (dirP a X t * Phi t u) * (x:ℂ)^(2 + Complex.I*(t:ℂ))‖^2)
        ≤ C0 * X^5 * (∫ t in (-T)..T, ‖dirP a X t * Phi t u‖^2)) :
    (∫ x in X..(2*X), ‖∫ t in (-T)..T, dirP a X t * ((x:ℂ)^(2 + Complex.I*(t:ℂ))) * (∫ u in (h/x)..(3*h/x), Phi t u)‖^2)
      ≤ (2*h/X) * ∫ u in (h/(2*X))..(3*h/X), C0 * X^5 * (∫ t in (-T)..T, ‖dirP a X t * Phi t u‖^2) := by
  have hGcont : Continuous (fun p : ℝ × ℝ => winG a X T p.1 p.2) := continuous_winG a X T
  -- basic facts
  have hX2X : X ≤ 2*X := by linarith
  have hmax_eq : ∀ x : ℝ, X ≤ x → max x X = x := fun x hx => max_eq_left hx
  have hden_ne : ∀ x : ℝ, max x X ≠ 0 := fun x =>
    ne_of_gt (lt_of_lt_of_le hX (le_max_right x X))
  have h3s : Continuous (fun x : ℝ => 3*h / max x X) :=
    Continuous.div continuous_const (continuous_id.max continuous_const) hden_ne
  have h1s : Continuous (fun x : ℝ => h / max x X) :=
    Continuous.div continuous_const (continuous_id.max continuous_const) hden_ne
  have h2s : Continuous (fun x : ℝ => 2*h / max x X) :=
    Continuous.div continuous_const (continuous_id.max continuous_const) hden_ne
  have hψc : Continuous (fun p : ℝ × ℝ => ‖winG a X T p.1 p.2‖^2) := (hGcont.norm).pow 2
  have hψc' : Continuous (fun p : ℝ × ℝ => ‖winG a X T p.2 p.1‖^2) :=
    ((hGcont.comp continuous_swap).norm).pow 2
  -- surrogate integrals with a continuous (glued) upper limit
  have hS1 : Continuous (fun x : ℝ => ∫ u in (0:ℝ)..(3*h / max x X), winG a X T x u) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (a₀ := 0) hGcont h3s
  have hS2 : Continuous (fun x : ℝ => ∫ u in (0:ℝ)..(h / max x X), winG a X T x u) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (a₀ := 0) hGcont h1s
  have hR1 : Continuous (fun x : ℝ => ∫ u in (0:ℝ)..(3*h / max x X), ‖winG a X T x u‖^2) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (a₀ := 0) hψc h3s
  have hR2 : Continuous (fun x : ℝ => ∫ u in (0:ℝ)..(h / max x X), ‖winG a X T x u‖^2) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (a₀ := 0) hψc h1s
  set J : ℝ → ℂ := fun x => ∫ u in (h/max x X)..(3*h/max x X), winG a X T x u with hJdef
  set I : ℝ → ℝ := fun x => ∫ u in (h/max x X)..(3*h/max x X), ‖winG a X T x u‖^2 with hIdef
  have hJeq : J = fun x =>
      (∫ u in (0:ℝ)..(3*h/max x X), winG a X T x u) -
        (∫ u in (0:ℝ)..(h/max x X), winG a X T x u) := by
    funext x
    have hcx : Continuous (fun u : ℝ => winG a X T x u) := continuous_winG_slice a X T x
    rw [hJdef]
    exact (intervalIntegral.integral_interval_sub_left
      (hcx.intervalIntegrable 0 (3*h/max x X)) (hcx.intervalIntegrable 0 (h/max x X))).symm
  have hJcont : Continuous J := by rw [hJeq]; exact hS1.sub hS2
  have hIeq : I = fun x =>
      (∫ u in (0:ℝ)..(3*h/max x X), ‖winG a X T x u‖^2) -
        (∫ u in (0:ℝ)..(h/max x X), ‖winG a X T x u‖^2) := by
    funext x
    have hcx : Continuous (fun u : ℝ => ‖winG a X T x u‖^2) :=
      (continuous_winG_slice a X T x).norm.pow 2
    rw [hIdef]
    exact (intervalIntegral.integral_interval_sub_left
      (hcx.intervalIntegrable 0 (3*h/max x X)) (hcx.intervalIntegrable 0 (h/max x X))).symm
  have hIcont : Continuous I := by rw [hIeq]; exact hR1.sub hR2
  have hJsqcont : Continuous (fun x : ℝ => ‖J x‖^2) := (hJcont.norm).pow 2
  have hCSmcont : Continuous (fun x : ℝ => (2*h/max x X) * I x) := h2s.mul hIcont
  have hJx : ∀ x : ℝ, X ≤ x → J x = ∫ u in (h/x)..(3*h/x), winG a X T x u := by
    intro x hx
    rw [hJdef]
    show (∫ u in (h/max x X)..(3*h/max x X), winG a X T x u) = _
    rw [hmax_eq x hx]
  have hIx : ∀ x : ℝ, X ≤ x → I x = ∫ u in (h/x)..(3*h/x), ‖winG a X T x u‖^2 := by
    intro x hx
    rw [hIdef]
    show (∫ u in (h/max x X)..(3*h/max x X), ‖winG a X T x u‖^2) = _
    rw [hmax_eq x hx]
  -- the admissible range
  have hlo_hi : h/(2*X) ≤ 3*h/X := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 2*X)]
    have he : 3*h/X * (2*X) = 6*h := by field_simp; ring
    rw [he]; linarith
  -- (1) swap `t` and `u` inside the norm
  have hinner : ∀ x ∈ Set.Icc X (2*X),
      (∫ t in (-T)..T, dirP a X t * ((x:ℂ)^(2 + Complex.I*(t:ℂ))) * (∫ u in (h/x)..(3*h/x), Phi t u)) = J x := by
    intro x hx
    have hxX : X ≤ x := hx.1
    have hxpos : 0 < x := lt_of_lt_of_le hX hxX
    have hhab : h/x ≤ 3*h/x := by
      rw [div_le_div_iff_of_pos_right hxpos]; linarith
    rw [hJx x hxX]
    simp only [winG]
    have hcontFp : Continuous (fun p : ℝ × ℝ =>
        (dirP a X p.2 * Phi p.2 p.1) * (x:ℂ)^(2 + Complex.I*(p.2:ℂ))) := by
      apply Continuous.mul
      · exact ((continuous_dirP_wb a X).comp continuous_snd).mul
          (continuous_Phi_pair.comp (continuous_snd.prodMk continuous_fst))
      · exact continuous_cpow_pair.comp (continuous_const.prodMk continuous_snd)
    rw [swap_cont_interval (fun u t => (dirP a X t * Phi t u) * (x:ℂ)^(2 + Complex.I*(t:ℂ)))
      hcontFp hhab (by linarith : -T ≤ T)]
    apply intervalIntegral.integral_congr
    intro t _
    show dirP a X t * (x:ℂ)^(2 + Complex.I*(t:ℂ)) * (∫ u in (h/x)..(3*h/x), Phi t u)
        = ∫ u in (h/x)..(3*h/x), (dirP a X t * Phi t u) * (x:ℂ)^(2 + Complex.I*(t:ℂ))
    rw [show (fun u : ℝ => (dirP a X t * Phi t u) * (x:ℂ)^(2 + Complex.I*(t:ℂ)))
          = (fun u : ℝ => (dirP a X t * (x:ℂ)^(2 + Complex.I*(t:ℂ))) * Phi t u) from
          funext (fun u => by ring)]
    rw [intervalIntegral.integral_const_mul]
  -- (2) Cauchy-Schwarz in `u` for each `x`
  have hCS : ∀ x ∈ Set.Icc X (2*X), ‖J x‖^2 ≤ (2*h/max x X) * I x := by
    intro x hx
    have hxX : X ≤ x := hx.1
    have hxpos : 0 < x := lt_of_lt_of_le hX hxX
    have hhab : h/x ≤ 3*h/x := by
      rw [div_le_div_iff_of_pos_right hxpos]; linarith
    have hcx : Continuous (fun u : ℝ => winG a X T x u) := continuous_winG_slice a X T x
    have hcs := norm_integral_sq_le (fun u : ℝ => winG a X T x u) hcx hhab
    rw [hJx x hxX, hIx x hxX, hmax_eq x hxX]
    have hlen : 3*h/x - h/x = 2*h/x := by ring
    rw [hlen] at hcs
    exact hcs
  -- (3) extend the `u`-range and bound the prefactor
  have hCSc : ∀ x ∈ Set.Icc X (2*X),
      (2*h/max x X) * I x ≤ (2*h/X) * (∫ u in (h/(2*X))..(3*h/X), ‖winG a X T x u‖^2) := by
    intro x hx
    have hxX : X ≤ x := hx.1
    have hx2X : x ≤ 2*X := hx.2
    have hxpos : 0 < x := lt_of_lt_of_le hX hxX
    have hhab : h/x ≤ 3*h/x := by
      rw [div_le_div_iff_of_pos_right hxpos]; linarith
    rw [hmax_eq x hxX, hIx x hxX]
    have hcx : Continuous (fun u : ℝ => ‖winG a X T x u‖^2) :=
      (continuous_winG_slice a X T x).norm.pow 2
    have hca : h/(2*X) ≤ h/x := by
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 2*X) hxpos]; nlinarith [hh, hx2X]
    have hbd : 3*h/x ≤ 3*h/X := by
      rw [div_le_div_iff₀ hxpos hX]; nlinarith [hh, hxX]
    have hint : (∫ u in (h/x)..(3*h/x), ‖winG a X T x u‖^2) ≤
        ∫ u in (h/(2*X))..(3*h/X), ‖winG a X T x u‖^2 := by
      refine intervalIntegral.integral_mono_interval hca hhab hbd ?_ ?_
      · exact Filter.Eventually.of_forall (fun u => sq_nonneg (‖winG a X T x u‖))
      · exact hcx.intervalIntegrable _ _
    have hfac : 2*h/x ≤ 2*h/X := by
      rw [div_le_div_iff₀ hxpos hX]; nlinarith [hh, hxX]
    have hnn1 : 0 ≤ ∫ u in (h/x)..(3*h/x), ‖winG a X T x u‖^2 :=
      intervalIntegral.integral_nonneg hhab (fun u _ => sq_nonneg _)
    have hnn2 : 0 ≤ 2*h/X := by positivity
    calc (2*h/x) * (∫ u in (h/x)..(3*h/x), ‖winG a X T x u‖^2)
        ≤ (2*h/X) * (∫ u in (h/x)..(3*h/x), ‖winG a X T x u‖^2) :=
          mul_le_mul_of_nonneg_right hfac hnn1
      _ ≤ (2*h/X) * (∫ u in (h/(2*X))..(3*h/X), ‖winG a X T x u‖^2) :=
          mul_le_mul_of_nonneg_left hint hnn2
  -- (4) the outer chain
  have hstepA : (∫ x in X..(2*X), ‖∫ t in (-T)..T, dirP a X t * ((x:ℂ)^(2 + Complex.I*(t:ℂ))) * (∫ u in (h/x)..(3*h/x), Phi t u)‖^2)
      = ∫ x in X..(2*X), ‖J x‖^2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hX2X] at hx
    show ‖∫ t in (-T)..T, dirP a X t * ((x:ℂ)^(2 + Complex.I*(t:ℂ))) * (∫ u in (h/x)..(3*h/x), Phi t u)‖^2 = ‖J x‖^2
    rw [hinner x hx]
  have hstepB : (∫ x in X..(2*X), ‖J x‖^2) ≤ ∫ x in X..(2*X), (2*h/max x X) * I x := by
    refine intervalIntegral.integral_mono_on hX2X (hJsqcont.intervalIntegrable _ _)
      (hCSmcont.intervalIntegrable _ _) ?_
    intro x hx
    exact hCS x hx
  have hcontRHS : Continuous (fun x : ℝ =>
      (2*h/X) * (∫ u in (h/(2*X))..(3*h/X), ‖winG a X T x u‖^2)) :=
    (continuous_const : Continuous (fun _ : ℝ => 2*h/X)).mul
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        hψc (h/(2*X)) (3*h/X))
  have hstepC : (∫ x in X..(2*X), (2*h/max x X) * I x) ≤
      ∫ x in X..(2*X), (2*h/X) * (∫ u in (h/(2*X))..(3*h/X), ‖winG a X T x u‖^2) := by
    refine intervalIntegral.integral_mono_on hX2X (hCSmcont.intervalIntegrable _ _)
      (hcontRHS.intervalIntegrable _ _) ?_
    intro x hx
    exact hCSc x hx
  have hstepE : (∫ x in X..(2*X), ∫ u in (h/(2*X))..(3*h/X), ‖winG a X T x u‖^2)
      = ∫ u in (h/(2*X))..(3*h/X), ∫ x in X..(2*X), ‖winG a X T x u‖^2 :=
    swap_cont_interval (fun x u => ‖winG a X T x u‖^2) hψc hX2X hlo_hi
  have hcont1 : Continuous (fun u : ℝ => ∫ x in X..(2*X), ‖winG a X T x u‖^2) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hψc' X (2*X)
  have hcont2 : Continuous (fun u : ℝ => ∫ t in (-T)..T, ‖dirP a X t * Phi t u‖^2) := by
    have hc : Continuous (fun q : ℝ × ℝ => ‖dirP a X q.2 * Phi q.2 q.1‖^2) :=
      (((continuous_dirP_wb a X).comp continuous_snd).mul
        (continuous_Phi_pair.comp (continuous_snd.prodMk continuous_fst))).norm.pow 2
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hc (-T) T
  have hcont3 : Continuous (fun u : ℝ =>
      C0 * X^5 * (∫ t in (-T)..T, ‖dirP a X t * Phi t u‖^2)) :=
    (continuous_const : Continuous (fun _ : ℝ => C0*X^5)).mul hcont2
  have hstepF : (∫ u in (h/(2*X))..(3*h/X), ∫ x in X..(2*X), ‖winG a X T x u‖^2)
      ≤ ∫ u in (h/(2*X))..(3*h/X), C0 * X^5 * (∫ t in (-T)..T, ‖dirP a X t * Phi t u‖^2) := by
    refine intervalIntegral.integral_mono_on hlo_hi (hcont1.intervalIntegrable _ _)
      (hcont3.intervalIntegrable _ _) ?_
    intro u _
    have hf := hfrozen u
    simp only [winG]
    exact hf
  have h2hX : 0 ≤ 2*h/X := by positivity
  calc
    (∫ x in X..(2*X), ‖∫ t in (-T)..T, dirP a X t * ((x:ℂ)^(2 + Complex.I*(t:ℂ))) * (∫ u in (h/x)..(3*h/x), Phi t u)‖^2)
        = ∫ x in X..(2*X), ‖J x‖^2 := hstepA
    _ ≤ ∫ x in X..(2*X), (2*h/max x X) * I x := hstepB
    _ ≤ ∫ x in X..(2*X), (2*h/X) * (∫ u in (h/(2*X))..(3*h/X), ‖winG a X T x u‖^2) := hstepC
    _ = (2*h/X) * ∫ x in X..(2*X), ∫ u in (h/(2*X))..(3*h/X), ‖winG a X T x u‖^2 :=
          intervalIntegral.integral_const_mul (2*h/X) _
    _ = (2*h/X) * ∫ u in (h/(2*X))..(3*h/X), ∫ x in X..(2*X), ‖winG a X T x u‖^2 := by rw [hstepE]
    _ ≤ (2*h/X) * ∫ u in (h/(2*X))..(3*h/X), C0 * X^5 * (∫ t in (-T)..T, ‖dirP a X t * Phi t u‖^2) :=
          mul_le_mul_of_nonneg_left hstepF h2hX

end

end Work.BMF
