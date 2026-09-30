import Mathlib
import Submission.Work.BMF.parseval.Defs
import Submission.Work.BMF.parseval.Basics
import Submission.Work.BMF.window_decomposition

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open scoped BigOperators ComplexConjugate
open MeasureTheory intervalIntegral

noncomputable section

/-!
# The single-window `L²` Perron bound via the two parts `J₁`, `J₂`

`window_decomposition` writes, for `X ≤ x ≤ 2X`,

`perronP a X h T x = (4πh²)⁻¹ (J₁(x) − J₂(x))`,

with `J₁, J₂` the two parametric integrals appearing on the right-hand side of the statement.
Combining the pointwise bound `‖J₁ − J₂‖² ≤ 2(‖J₁‖² + ‖J₂‖²)` with the fact that both parts
are continuous in `x` (hence interval integrable on the compact window) gives the stated
`L²` inequality.
-/

/-! ## Continuity of `J₁`, `J₂` and `perronP` in the window variable -/

/-- `Φ` is continuous in its clamped form (second argument clamped at `0`). -/
private lemma pvp_continuous_PhiClamp : Continuous (fun q : (ℝ × ℝ) × ℝ => Phi q.1.2 (max 0 q.2)) := by
  unfold Phi
  have ht : Continuous (fun q : (ℝ × ℝ) × ℝ => q.1.2) := continuous_snd.comp continuous_fst
  have hu : Continuous (fun q : (ℝ × ℝ) × ℝ => q.2) := continuous_snd
  refine Continuous.div ?_ ?_ ?_
  · refine Continuous.sub ?_ continuous_const
    refine Continuous.cpow ?_ ?_ ?_
    · exact Complex.continuous_ofReal.comp (continuous_const.add (continuous_const.max hu))
    · exact continuous_const.add (continuous_const.mul (Complex.continuous_ofReal.comp ht))
    · intro q
      rw [Complex.ofReal_mem_slitPlane]
      linarith [le_max_left (0:ℝ) q.2]
  · exact continuous_const.add (continuous_const.mul (Complex.continuous_ofReal.comp ht))
  · intro q
    exact one_add_I_mul_ne_zeroD _

/-- `u ↦ Φ t u` is continuous on `[0,c]`. -/
private lemma pvp_continuousOn_Phi_right (t c : ℝ) (hc : 0 ≤ c) :
    ContinuousOn (fun u : ℝ => Phi t u) (Set.uIcc 0 c) := by
  unfold Phi
  refine ContinuousOn.div ?_ continuousOn_const ?_
  · refine ContinuousOn.sub ?_ continuousOn_const
    refine ContinuousOn.cpow ?_ continuousOn_const ?_
    · exact Complex.continuous_ofReal.comp_continuousOn
        ((continuous_const.add continuous_id).continuousOn)
    · intro u hu
      rw [Complex.ofReal_mem_slitPlane]
      have h0 : 0 ≤ u := (Set.uIcc_of_le hc ▸ hu).1
      linarith
  · intro u _
    exact one_add_I_mul_ne_zeroD t

/-- Continuity on `[X, 2X]` (`X > 0`) of `J₁` as a function of `x`. -/
private lemma pvp_continuousOn_J1 (a : ℕ → ℂ) (X h T : ℝ) (hX : 0 < X) (hh : 0 ≤ h) :
    ContinuousOn (fun x : ℝ => ∫ t in (-T)..T, dirP a X t * (x:ℂ)^(2 + Complex.I*(t:ℂ)) *
        (∫ u in (h/x)..(3*h/x), Phi t u)) (Set.Icc X (2*X)) := by
  set c : ℝ := X/2 with hcdef
  have hcpos : 0 < c := by rw [hcdef]; linarith
  set Ψ : ℝ → ℝ := fun x => h / max c x with hΨdef
  have hΨcont : Continuous Ψ := by
    rw [hΨdef]
    exact continuous_const.div (continuous_const.max continuous_id) (fun x => by positivity)
  have hbase : Continuous (fun p : ℝ × ℝ => ∫ u in (0:ℝ)..(3*Ψ p.1), Phi p.2 (max 0 u)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (a₀ := 0)
    · exact pvp_continuous_PhiClamp
    · exact continuous_const.mul (hΨcont.comp continuous_fst)
  have htail : Continuous (fun p : ℝ × ℝ => ∫ u in (0:ℝ)..(Ψ p.1), Phi p.2 (max 0 u)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (a₀ := 0)
    · exact pvp_continuous_PhiClamp
    · exact hΨcont.comp continuous_fst
  have hinner : Continuous (fun p : ℝ × ℝ =>
      (∫ u in (0:ℝ)..(3*Ψ p.1), Phi p.2 (max 0 u)) - (∫ u in (0:ℝ)..(Ψ p.1), Phi p.2 (max 0 u))) :=
    hbase.sub htail
  have hint : Continuous (fun p : ℝ × ℝ => dirP a X p.2 * (((max c p.1 : ℝ)) : ℂ)^(2 + Complex.I*(p.2:ℂ)) *
      ((∫ u in (0:ℝ)..(3*Ψ p.1), Phi p.2 (max 0 u)) - (∫ u in (0:ℝ)..(Ψ p.1), Phi p.2 (max 0 u)))) := by
    refine Continuous.mul (Continuous.mul ?_ ?_) hinner
    · exact (continuous_dirP a X).comp continuous_snd
    · exact Continuous.cpow (Complex.continuous_ofReal.comp (continuous_const.max continuous_fst))
        (continuous_const.add (continuous_const.mul (Complex.continuous_ofReal.comp continuous_snd)))
        (fun p => by rw [Complex.ofReal_mem_slitPlane]; exact lt_of_lt_of_le hcpos (le_max_left _ _))
  have hcont : Continuous (fun x : ℝ => ∫ t in (-T)..T, dirP a X t * (((max c x : ℝ)) : ℂ)^(2 + Complex.I*(t:ℂ)) *
      ((∫ u in (0:ℝ)..(3*Ψ x), Phi t (max 0 u)) - (∫ u in (0:ℝ)..(Ψ x), Phi t (max 0 u)))) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact hint
  refine (hcont.continuousOn.mono (Set.subset_univ _)).congr ?_
  intro x hx
  have hxc : max c x = x := max_eq_right (by rw [hcdef]; linarith [hx.1])
  have hxpos : 0 < x := lt_of_lt_of_le hX hx.1
  have hΨx : Ψ x = h/x := by simp only [hΨdef, hxc]
  have h3nn : (0:ℝ) ≤ 3*h/x := div_nonneg (mul_nonneg (by norm_num) hh) hxpos.le
  have h1nn : (0:ℝ) ≤ h/x := div_nonneg hh hxpos.le
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  have h1t : (∫ u in (0:ℝ)..(3*h/x), Phi t (max 0 u)) = ∫ u in (0:ℝ)..(3*h/x), Phi t u := by
    apply intervalIntegral.integral_congr
    intro u hu
    have h0 : 0 ≤ u := (Set.uIcc_of_le h3nn ▸ hu).1
    simp only [max_eq_right h0]
  have h2t : (∫ u in (0:ℝ)..(h/x), Phi t (max 0 u)) = ∫ u in (0:ℝ)..(h/x), Phi t u := by
    apply intervalIntegral.integral_congr
    intro u hu
    have h0 : 0 ≤ u := (Set.uIcc_of_le h1nn ▸ hu).1
    simp only [max_eq_right h0]
  have hA : IntervalIntegrable (fun u : ℝ => Phi t u) volume 0 (3*h/x) :=
    (pvp_continuousOn_Phi_right t (3*h/x) h3nn).intervalIntegrable
  have hB : IntervalIntegrable (fun u : ℝ => Phi t u) volume 0 (h/x) :=
    (pvp_continuousOn_Phi_right t (h/x) h1nn).intervalIntegrable
  rw [hxc, hΨx, show 3*(h/x) = 3*h/x by ring]
  rw [h1t, h2t, intervalIntegral.integral_interval_sub_left hA hB]

/-- Continuity on `[X, 2X]` (`X > 0`) of `J₂` as a function of `x`. -/
private lemma pvp_continuousOn_J2 (a : ℕ → ℂ) (X h T : ℝ) (hX : 0 < X) (hh : 0 ≤ h) :
    ContinuousOn (fun x : ℝ => ∫ t in (-T)..T, dirP a X t * (((x+h:ℝ)):ℂ)^(2 + Complex.I*(t:ℂ)) *
        (∫ u in (0:ℝ)..(2*h/(x+h)), Phi t u)) (Set.Icc X (2*X)) := by
  set Ψ : ℝ → ℝ := fun x => 2*h/(max X (x+h)) with hΨdef
  have hΨcont : Continuous Ψ := by
    rw [hΨdef]
    exact continuous_const.div (continuous_const.max (continuous_id.add continuous_const))
      (fun x => by have := le_max_left X (x+h); positivity)
  have hbase : Continuous (fun p : ℝ × ℝ => ∫ u in (0:ℝ)..(Ψ p.1), Phi p.2 (max 0 u)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (a₀ := 0)
    · exact pvp_continuous_PhiClamp
    · exact hΨcont.comp continuous_fst
  have hint : Continuous (fun p : ℝ × ℝ => dirP a X p.2 * ((max X (p.1+h) : ℝ) : ℂ)^(2 + Complex.I*(p.2:ℂ)) *
      (∫ u in (0:ℝ)..(Ψ p.1), Phi p.2 (max 0 u))) := by
    refine Continuous.mul (Continuous.mul ?_ ?_) hbase
    · exact (continuous_dirP a X).comp continuous_snd
    · exact Continuous.cpow (Complex.continuous_ofReal.comp (continuous_const.max (continuous_fst.add continuous_const)))
        (continuous_const.add (continuous_const.mul (Complex.continuous_ofReal.comp continuous_snd)))
        (fun p => by rw [Complex.ofReal_mem_slitPlane]; exact lt_of_lt_of_le hX (le_max_left _ _))
  have hcont : Continuous (fun x : ℝ => ∫ t in (-T)..T, dirP a X t * ((max X (x+h) : ℝ) : ℂ)^(2 + Complex.I*(t:ℂ)) *
      (∫ u in (0:ℝ)..(Ψ x), Phi t (max 0 u))) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact hint
  refine (hcont.continuousOn.mono (Set.subset_univ _)).congr ?_
  intro x hx
  have hxc : max X (x+h) = x+h := max_eq_right (by linarith [hx.1])
  have hxpos : 0 < x := lt_of_lt_of_le hX hx.1
  have hΨx : Ψ x = 2*h/(x+h) := by simp only [hΨdef, hxc]
  have h2nn : (0:ℝ) ≤ 2*h/(x+h) := div_nonneg (mul_nonneg (by norm_num) hh) (by linarith)
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  have h1t : (∫ u in (0:ℝ)..(2*h/(x+h)), Phi t (max 0 u)) = ∫ u in (0:ℝ)..(2*h/(x+h)), Phi t u := by
    apply intervalIntegral.integral_congr
    intro u hu
    have h0 : 0 ≤ u := (Set.uIcc_of_le h2nn ▸ hu).1
    simp only [max_eq_right h0]
  rw [hxc, hΨx, h1t]

/-- Continuity of `x ↦ perronP a X h T x` on `[X, ∞)` for `X > 0`. -/
private lemma pvp_continuousOn_perronP (a : ℕ → ℂ) (X h T : ℝ) (hX : 0 < X) (hh : 0 < h) :
    ContinuousOn (fun x : ℝ => perronP a X h T x) (Set.Ici X) := by
  have hden : Continuous (fun p : ℝ × ℝ => (h:ℂ) * (1 + Complex.I*(p.2:ℂ))) :=
    continuous_const.mul (continuous_const.add (continuous_const.mul (Complex.continuous_ofReal.comp continuous_snd)))
  have hden0 : ∀ p : ℝ × ℝ, (h:ℂ) * (1 + Complex.I*(p.2:ℂ)) ≠ 0 := fun p =>
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hh.ne') (one_add_I_mul_ne_zeroD _)
  have hint : Continuous (fun p : ℝ × ℝ =>
      dirP a X p.2 * ((max X p.1 + h : ℝ) : ℂ)^(1 + Complex.I*(p.2:ℂ)) / ((h:ℂ) * (1 + Complex.I*(p.2:ℂ)))
      - dirP a X p.2 * ((max X p.1 : ℝ) : ℂ)^(1 + Complex.I*(p.2:ℂ)) / ((h:ℂ) * (1 + Complex.I*(p.2:ℂ)))) := by
    refine Continuous.sub ?_ ?_
    · refine Continuous.div (Continuous.mul ((continuous_dirP a X).comp continuous_snd) ?_) hden hden0
      exact Continuous.cpow
        (Complex.continuous_ofReal.comp ((continuous_const.max continuous_fst).add continuous_const))
        (continuous_const.add (continuous_const.mul (Complex.continuous_ofReal.comp continuous_snd)))
        (fun p => by rw [Complex.ofReal_mem_slitPlane]; have := le_max_left X p.1; linarith)
    · refine Continuous.div (Continuous.mul ((continuous_dirP a X).comp continuous_snd) ?_) hden hden0
      exact Continuous.cpow (Complex.continuous_ofReal.comp (continuous_const.max continuous_fst))
        (continuous_const.add (continuous_const.mul (Complex.continuous_ofReal.comp continuous_snd)))
        (fun p => by rw [Complex.ofReal_mem_slitPlane]; exact lt_of_lt_of_le hX (le_max_left _ _))
  have hcont : Continuous (fun x : ℝ => ∫ t in (-T)..T,
      dirP a X t * ((max X x + h : ℝ) : ℂ)^(1 + Complex.I*(t:ℂ)) / ((h:ℂ) * (1 + Complex.I*(t:ℂ)))
      - dirP a X t * ((max X x : ℝ) : ℂ)^(1 + Complex.I*(t:ℂ)) / ((h:ℂ) * (1 + Complex.I*(t:ℂ)))) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact hint
  refine ((hcont.const_mul (1/(2*Real.pi))).continuousOn.mono (Set.subset_univ _)).congr ?_
  intro x hx
  dsimp only
  simp only [perronP]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [show max X x = x from max_eq_right hx, mul_assoc,
    cpow_theta_identity h x t (lt_of_lt_of_le hX hx) hh]
  ring

/-- **The single-window `L²` Perron bound via the two parts.** -/
theorem perronP_l2_via_parts (a : ℕ → ℂ) (X h T : ℝ) (hX : 1 ≤ X) (hh : 1 ≤ h) (hhX : h ≤ X) (hT : 1 ≤ T) :
    (1/X) * (∫ x in X..(2*X), ‖perronP a X h T x‖^2)
      ≤ (1/(8*Real.pi^2*h^4)) *
        ((1/X) * (∫ x in X..(2*X), ‖∫ t in (-T)..T, dirP a X t * ((x:ℂ)^(2 + Complex.I*(t:ℂ))) * (∫ u in (h/x)..(3*h/x), Phi t u)‖^2)
       + (1/X) * (∫ x in X..(2*X), ‖∫ t in (-T)..T, dirP a X t * (((x+h):ℂ)^(2 + Complex.I*(t:ℂ))) * (∫ u in (0:ℝ)..(2*h/(x+h)), Phi t u)‖^2)) := by
  have hXpos : (0:ℝ) < X := by linarith
  have hhpos : (0:ℝ) < h := by linarith
  have hTpos : (0:ℝ) < T := by linarith
  have hhh : (0:ℝ) ≤ h := by linarith
  have hXle : X ≤ 2*X := by linarith
  set J1 : ℝ → ℂ := fun x => ∫ t in (-T)..T, dirP a X t * (x:ℂ)^(2 + Complex.I*(t:ℂ)) *
      (∫ u in (h/x)..(3*h/x), Phi t u) with hJ1def
  set J2 : ℝ → ℂ := fun x => ∫ t in (-T)..T, dirP a X t * (((x+h):ℂ))^(2 + Complex.I*(t:ℂ)) *
      (∫ u in (0:ℝ)..(2*h/(x+h)), Phi t u) with hJ2def
  have hcontPer : ContinuousOn (fun x : ℝ => ‖perronP a X h T x‖^2) (Set.Icc X (2*X)) :=
    (((pvp_continuousOn_perronP a X h T hXpos hhpos).mono
      (by intro x hx; exact hx.1)).norm).pow 2
  have hcontJ1 : ContinuousOn (fun x : ℝ => ‖J1 x‖^2) (Set.Icc X (2*X)) := by
    rw [hJ1def]
    exact (pvp_continuousOn_J1 a X h T hXpos hhh).norm.pow 2
  have hcontJ2 : ContinuousOn (fun x : ℝ => ‖J2 x‖^2) (Set.Icc X (2*X)) := by
    rw [hJ2def]
    refine ((pvp_continuousOn_J2 a X h T hXpos hhh).norm.pow 2).congr ?_
    intro x hx
    dsimp only
    apply congrArg (fun z : ℂ => ‖z‖^2)
    apply intervalIntegral.integral_congr
    intro t _
    rw [← Complex.ofReal_add]
  have hpt : ∀ x ∈ Set.Icc X (2*X), ‖perronP a X h T x‖^2
      ≤ (1/(8*Real.pi^2*h^4)) * ‖J1 x‖^2 + (1/(8*Real.pi^2*h^4)) * ‖J2 x‖^2 := by
    intro x hx
    have hdec : perronP a X h T x = (1/(4*Real.pi*h^2)) * (J1 x - J2 x) := by
      rw [hJ1def, hJ2def]
      exact window_decomposition a hX hx.1 hx.2 hhpos hTpos
    have hdec' : perronP a X h T x = ((1/(4*Real.pi*h^2) : ℝ) : ℂ) * (J1 x - J2 x) := by
      rw [hdec]
      congr 1
      push_cast
      try ring
    have hnorm : ‖((1/(4*Real.pi*h^2) : ℝ) : ℂ)‖ = (1/(4*Real.pi*h^2) : ℝ) := by
      rw [show ‖((1/(4*Real.pi*h^2) : ℝ) : ℂ)‖ = |(1/(4*Real.pi*h^2) : ℝ)| by simp]
      exact abs_of_nonneg (by positivity)
    rw [hdec', norm_mul, mul_pow, hnorm]
    have h4 : ‖J1 x - J2 x‖ ≤ ‖J1 x‖ + ‖J2 x‖ := norm_sub_le _ _
    have h5 : ‖J1 x - J2 x‖^2 ≤ (‖J1 x‖ + ‖J2 x‖)^2 := by
      nlinarith [h4, norm_nonneg (J1 x - J2 x), norm_nonneg (J1 x), norm_nonneg (J2 x)]
    have h6 : ‖J1 x - J2 x‖^2 ≤ 2 * (‖J1 x‖^2 + ‖J2 x‖^2) := by
      nlinarith [h5, sq_nonneg (‖J1 x‖ - ‖J2 x‖)]
    calc (1/(4*Real.pi*h^2))^2 * ‖J1 x - J2 x‖^2
        ≤ (1/(4*Real.pi*h^2))^2 * (2 * (‖J1 x‖^2 + ‖J2 x‖^2)) :=
          mul_le_mul_of_nonneg_left h6 (sq_nonneg _)
      _ = (1/(8*Real.pi^2*h^4)) * ‖J1 x‖^2 + (1/(8*Real.pi^2*h^4)) * ‖J2 x‖^2 := by ring
  have hgCont : ContinuousOn
      (fun x : ℝ => (1/(8*Real.pi^2*h^4)) * ‖J1 x‖^2 + (1/(8*Real.pi^2*h^4)) * ‖J2 x‖^2)
      (Set.Icc X (2*X)) :=
    (hcontJ1.const_mul (1/(8*Real.pi^2*h^4))).add (hcontJ2.const_mul (1/(8*Real.pi^2*h^4)))
  have hfInt : IntervalIntegrable (fun x : ℝ => ‖perronP a X h T x‖^2) volume X (2*X) :=
    ContinuousOn.intervalIntegrable_of_Icc hXle hcontPer
  have hgInt : IntervalIntegrable
      (fun x : ℝ => (1/(8*Real.pi^2*h^4)) * ‖J1 x‖^2 + (1/(8*Real.pi^2*h^4)) * ‖J2 x‖^2)
      volume X (2*X) :=
    ContinuousOn.intervalIntegrable_of_Icc hXle hgCont
  have hmono : (∫ x in X..(2*X), ‖perronP a X h T x‖^2)
      ≤ ∫ x in X..(2*X),
          ((1/(8*Real.pi^2*h^4)) * ‖J1 x‖^2 + (1/(8*Real.pi^2*h^4)) * ‖J2 x‖^2) :=
    intervalIntegral.integral_mono_on (hab := hXle) hfInt hgInt (fun x hx => hpt x hx)
  have hsplit : (∫ x in X..(2*X),
        ((1/(8*Real.pi^2*h^4)) * ‖J1 x‖^2 + (1/(8*Real.pi^2*h^4)) * ‖J2 x‖^2))
      = (1/(8*Real.pi^2*h^4)) * (∫ x in X..(2*X), ‖J1 x‖^2)
        + (1/(8*Real.pi^2*h^4)) * (∫ x in X..(2*X), ‖J2 x‖^2) := by
    rw [intervalIntegral.integral_add
      ((hcontJ1.const_mul (1/(8*Real.pi^2*h^4))).intervalIntegrable_of_Icc hXle)
      ((hcontJ2.const_mul (1/(8*Real.pi^2*h^4))).intervalIntegrable_of_Icc hXle)]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hXinv : (0:ℝ) ≤ 1/X := div_nonneg zero_le_one hXpos.le
  calc (1/X) * (∫ x in X..(2*X), ‖perronP a X h T x‖^2)
      ≤ (1/X) * (∫ x in X..(2*X),
          ((1/(8*Real.pi^2*h^4)) * ‖J1 x‖^2 + (1/(8*Real.pi^2*h^4)) * ‖J2 x‖^2)) :=
        mul_le_mul_of_nonneg_left hmono hXinv
    _ = (1/X) * ((1/(8*Real.pi^2*h^4)) * (∫ x in X..(2*X), ‖J1 x‖^2)
          + (1/(8*Real.pi^2*h^4)) * (∫ x in X..(2*X), ‖J2 x‖^2)) := by rw [hsplit]
    _ = (1/(8*Real.pi^2*h^4)) * ((1/X) * (∫ x in X..(2*X), ‖J1 x‖^2)
          + (1/X) * (∫ x in X..(2*X), ‖J2 x‖^2)) := by ring

end

end Work.BMF
