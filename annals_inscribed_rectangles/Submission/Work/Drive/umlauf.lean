import Mathlib
import Submission.Work.Drive.Interfaces
import Submission.Work.Drive.UmlaufSetup
import Submission.Work.Drive.curve_deriv_ne_zero
import Submission.Work.Drive.curve_eq_iff
import Submission.Work.Drive.curve_periodic
import Submission.Work.Drive.deriv_curve_periodic
import Submission.Work.Drive.deriv_second_eq_zero
import Submission.Work.Drive.exists_angle_line
import Submission.Work.Drive.exists_angle_tri
import Submission.Work.Drive.sigmaPt_antisymm
import Submission.Work.Drive.sigmaPt_im_nonneg
import Submission.Work.Drive.strip_change_pos
import Submission.Work.Drive.strip_change_neg

/-!
# Hopf's Umlaufsatz

Proof of `Submission.Drive.UmlaufProp`.
-/

namespace Work.Drive

open scoped Manifold ContDiff
open Manifold

/-! ## Elementary circle and curve facts -/

lemma umlauf_circle_exp_pi : Circle.exp Real.pi = -1 := by
  apply Subtype.ext
  rw [Circle.coe_exp, Circle.coe_neg, Circle.coe_one, Complex.exp_pi_mul_I]

/-- Integer periodicity of a `RegCurve`. -/
lemma int_periodic (c : ℝ → ℝ × ℝ) (hc : RegCurve c) (k : ℤ) (t : ℝ) :
    c (t + 2 * Real.pi * k) = c t := by
  have h : Function.Periodic c (2 * Real.pi) := hc.periodic
  have h1 := h.sub_int_mul_eq (-k) (x := t)
  have h2 : t - ((-k : ℤ) : ℝ) * (2 * Real.pi) = t + 2 * Real.pi * k := by
    push_cast; ring
  rwa [h2] at h1

/-- A lowest point of a regular closed curve, in the fundamental interval `[0, 2π]`. -/
lemma exists_global_min (c : ℝ → ℝ × ℝ) (hc : RegCurve c) :
    ∃ t₀ ∈ Set.Icc (0 : ℝ) (2 * Real.pi), ∀ t, (c t₀).2 ≤ (c t).2 := by
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc (a := (0:ℝ)) (b := 2 * Real.pi) |>.exists_isMinOn
    ⟨0, le_rfl, by linarith [Real.pi_pos]⟩
    (hc.contDiff.continuous.snd.continuousOn)
  have hmin_le : ∀ y ∈ Set.Icc (0:ℝ) (2 * Real.pi), (c t₀).2 ≤ (c y).2 := by
    intro y hy
    exact hmin hy
  refine ⟨t₀, ht₀, fun t => ?_⟩
  set k : ℤ := ⌊t / (2 * Real.pi)⌋ with hk
  have h2pi : (0:ℝ) < 2 * Real.pi := by linarith [Real.pi_pos]
  have hk1 : ((k : ℤ) : ℝ) ≤ t / (2 * Real.pi) := Int.floor_le _
  have hk2 : t / (2 * Real.pi) < ((k : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  have hk1' : ((k : ℤ) : ℝ) * (2 * Real.pi) ≤ t := (le_div_iff₀ h2pi).mp hk1
  have hk2' : t < (((k : ℤ) : ℝ) + 1) * (2 * Real.pi) := (div_lt_iff₀ h2pi).mp hk2
  have hk1'' : 2 * Real.pi * ((k : ℤ) : ℝ) ≤ t := by simpa [mul_comm] using hk1'
  have hk2'' : t < 2 * Real.pi * (((k : ℤ) : ℝ) + 1) := by simpa [mul_comm] using hk2'
  have hs_mem : t - 2 * Real.pi * k ∈ Set.Icc 0 (2 * Real.pi) := by
    constructor <;> linarith
  have hper : c (t - 2 * Real.pi * k) = c t := by
    have h3 := int_periodic c hc k (t - 2 * Real.pi * k)
    rw [show t - 2 * Real.pi * k + 2 * Real.pi * (k : ℤ) = t by push_cast; ring] at h3
    exact h3.symm
  calc (c t₀).2 ≤ (c (t - 2 * Real.pi * k)).2 := hmin_le _ hs_mem
    _ = (c t).2 := by rw [hper]

lemma dirOf_ofReal_pos {r : ℝ} (hr : 0 < r) : dirOf (r : ℂ) = 1 := by
  have hz : (r : ℂ) ≠ 0 := by rw [Complex.ofReal_ne_zero]; exact ne_of_gt hr
  apply Subtype.ext
  rw [dirOf_coe hz, norm_ofReal_complex, abs_of_pos hr, div_self (by exact_mod_cast ne_of_gt hr)]
  simp

lemma dirOf_ofReal_neg {r : ℝ} (hr : r < 0) : dirOf (r : ℂ) = -1 := by
  have hz : (r : ℂ) ≠ 0 := by rw [Complex.ofReal_ne_zero]; exact ne_of_lt hr
  apply Subtype.ext
  rw [dirOf_coe hz, norm_ofReal_complex, abs_of_neg hr]
  have h2 : (r : ℂ) / (-(r : ℂ)) = -1 := by
    rw [div_neg, div_self hz]
  simpa using h2

/-- If the tangent of a regular curve at `t₀` is horizontal then its direction is `±1`. -/
lemma tangDir_eq_one_or_neg_one (c : ℝ → ℝ × ℝ) (hc : RegCurve c) {t₀ : ℝ}
    (hderiv : (deriv c t₀).2 = 0) : tangDir c t₀ = 1 ∨ tangDir c t₀ = -1 := by
  have hre : toC (deriv c t₀) = (((deriv c t₀).1 : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simp [hderiv]
  have hr : (deriv c t₀).1 ≠ 0 := by
    intro h
    apply hc.deriv_ne_zero t₀
    ext <;> simp [h, hderiv]
  rw [tangDir, hre]
  rcases lt_trichotomy ((deriv c t₀).1) 0 with h | h | h
  · exact Or.inr (dirOf_ofReal_neg h)
  · exact absurd h hr
  · exact Or.inl (dirOf_ofReal_pos h)

/-- A continuous real function on a preconnected set whose values are all integer multiples of
`2π` is constant. -/
lemma eq_of_mem_period_multiples {f : ℝ → ℝ} {s : Set ℝ} (hpre : IsPreconnected s)
    (hf : ContinuousOn f s) (hfz : ∀ t ∈ s, ∃ n : ℤ, f t = n * (2 * Real.pi)) :
    ∀ x ∈ s, ∀ y ∈ s, f x = f y := by
  have himg : IsPreconnected (f '' s) := hpre.image f hf
  have hord : Set.OrdConnected (f '' s) := himg.ordConnected
  have h4 : (0:ℝ) < 2 * Real.pi := by linarith [Real.pi_pos]
  have key : ∀ x ∈ s, ∀ y ∈ s, f x ≤ f y → f x = f y := by
    intro x hx y hy hle
    rcases lt_or_eq_of_le hle with hlt | heq
    · exfalso
      rcases hfz x hx with ⟨n, hn⟩
      rcases hfz y hy with ⟨m, hm⟩
      have hlt' : (n : ℝ) < (m : ℝ) := by
        have h' := hlt; rw [hn, hm] at h'
        nlinarith [Real.pi_pos]
      have hnm : n < m := by exact_mod_cast hlt'
      have hnm1 : n + 1 ≤ m := by omega
      set cc : ℝ := ((n : ℝ) + 1 / 2) * (2 * Real.pi) with hcc
      have hsc : f x < cc := by
        rw [hn, hcc]
        have : (n : ℝ) < (n : ℝ) + 1 / 2 := by norm_num
        nlinarith
      have hct : cc < f y := by
        rw [hm, hcc]
        have h5 : (n : ℝ) + 1 / 2 < (m : ℝ) := by
          have h6 : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hnm1
          linarith
        nlinarith
      have hccs : cc ∈ f '' s :=
        hord.out ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ ⟨le_of_lt hsc, le_of_lt hct⟩
      obtain ⟨u, hu, huc⟩ := hccs
      rcases hfz u hu with ⟨j, hj⟩
      have h2 : (j : ℝ) = (n : ℝ) + 1 / 2 := by
        rw [huc] at hj; nlinarith [hj, hcc, Real.pi_pos]
      have h7 : ((2 * (j - n) : ℤ) : ℝ) = ((1 : ℤ) : ℝ) := by push_cast; linarith
      have h8 : 2 * (j - n) = 1 := by exact_mod_cast h7
      omega
    · exact heq
  intro x hx y hy
  rcases le_total (f x) (f y) with h | h
  · exact key x hx y hy h
  · exact (key y hy x hx h).symm

/-! ## Unfolding `sigmaPt` -/

lemma umlauf_sigmaPt_diag (c : ℝ → ℝ × ℝ) (t₀ t : ℝ) :
    sigmaPt c t₀ (t, t) = tangDir c t := by
  rw [sigmaPt]
  have h1 : ¬ (t = t₀ ∧ t = t₀ + 2 * Real.pi) := by
    rintro ⟨h2, h3⟩; linarith [Real.pi_pos]
  rw [if_neg h1, if_neg (lt_irrefl t)]

lemma umlauf_sigmaPt_corner (c : ℝ → ℝ × ℝ) (t₀ : ℝ) :
    sigmaPt c t₀ (t₀, t₀ + 2 * Real.pi) = -(tangDir c t₀) := by
  rw [sigmaPt, if_pos ⟨rfl, rfl⟩]

lemma umlauf_sigmaPt_vert (c : ℝ → ℝ × ℝ) (t₀ t : ℝ) (h : t₀ < t) (ht : t ≠ t₀ + 2 * Real.pi) :
    sigmaPt c t₀ (t₀, t) = secDir c t₀ t := by
  rw [sigmaPt]
  have h1 : ¬ (t₀ = t₀ ∧ t = t₀ + 2 * Real.pi) := fun hh => ht hh.2
  rw [if_neg h1, if_pos h]

lemma umlauf_circle_exp_add_pi (x : ℝ) : Circle.exp (x + Real.pi) = -(Circle.exp x) := by
  rw [Circle.exp_add, umlauf_circle_exp_pi, mul_neg, mul_one]

/-! ## The total turning -/

/-- The total turning of a regular closed plane curve is `±2π`. -/
theorem winding_curve (c : ℝ → ℝ × ℝ) (hc : RegCurve c) (θ : ℝ → ℝ) (hθc : Continuous θ)
    (hθ : ∀ t, Circle.exp (θ t) = tangDir c t) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ t, θ (t + 2 * Real.pi) - θ t = 2 * Real.pi * ε := by
  obtain ⟨t₀, ht₀, hmin⟩ := exists_global_min c hc
  have hderiv : (deriv c t₀).2 = 0 := deriv_second_eq_zero c hc hmin
  obtain ⟨Θ, hΘc, hΘexp, hΘbase⟩ : ∃ Θ : tri t₀ → ℝ, Continuous Θ ∧
      (∀ p, Circle.exp (Θ p) = sigma c t₀ p) ∧ Θ (triBase t₀) = θ t₀ :=
    exists_angle_tri c hc t₀ θ hθ
  have hIlo : t₀ ∈ Set.Icc t₀ (t₀ + 2 * Real.pi) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hIhi : t₀ + 2 * Real.pi ∈ Set.Icc t₀ (t₀ + 2 * Real.pi) :=
    ⟨by linarith [Real.pi_pos], le_rfl⟩
  -- ### Step 1: the angle function agrees with the diagonal lift
  have hdiag : ∀ s : Set.Icc t₀ (t₀ + 2 * Real.pi),
      θ s.1 = Θ ⟨(s.1, s.1), ⟨s.2.1, le_rfl, s.2.2⟩⟩ := by
    intro s
    haveI : PreconnectedSpace (Set.Icc t₀ (t₀ + 2 * Real.pi)) :=
      Subtype.preconnectedSpace isPreconnected_Icc
    have h1 : Continuous (fun s : Set.Icc t₀ (t₀ + 2 * Real.pi) => θ s.1) :=
      hθc.comp continuous_subtype_val
    have h2 : Continuous (fun s : Set.Icc t₀ (t₀ + 2 * Real.pi) =>
        Θ ⟨(s.1, s.1), ⟨s.2.1, le_rfl, s.2.2⟩⟩) :=
      hΘc.comp (Continuous.subtype_mk
        (continuous_subtype_val.prodMk continuous_subtype_val)
        (fun s => ⟨s.2.1, le_rfl, s.2.2⟩))
    have he : ⇑Circle.exp ∘ (fun s : Set.Icc t₀ (t₀ + 2 * Real.pi) => θ s.1) =
        ⇑Circle.exp ∘ (fun s : Set.Icc t₀ (t₀ + 2 * Real.pi) =>
          Θ ⟨(s.1, s.1), ⟨s.2.1, le_rfl, s.2.2⟩⟩) := by
      funext s
      simp only [Function.comp_apply]
      rw [hθ s.1, hΘexp ⟨(s.1, s.1), ⟨s.2.1, le_rfl, s.2.2⟩⟩, sigma]
      exact (umlauf_sigmaPt_diag c t₀ s.1).symm
    have hbase : (fun s : Set.Icc t₀ (t₀ + 2 * Real.pi) => θ s.1) ⟨t₀, hIlo⟩ =
        (fun s : Set.Icc t₀ (t₀ + 2 * Real.pi) =>
          Θ ⟨(s.1, s.1), ⟨s.2.1, le_rfl, s.2.2⟩⟩) ⟨t₀, hIlo⟩ := by
      show θ t₀ = Θ ⟨(t₀, t₀), ⟨le_rfl, le_rfl, by linarith [Real.pi_pos]⟩⟩
      rw [← hΘbase]
      exact congrArg Θ (Subtype.ext rfl)
    exact congr_fun (IsCoveringMap.eq_of_comp_eq Circle.isCoveringMap_exp h1 h2 he ⟨t₀, hIlo⟩ hbase) s
  -- ### Step 2: the vertical side and the third side of the triangle
  set G : ℝ → ℝ := fun t => if h : t ∈ Set.Icc t₀ (t₀ + 2 * Real.pi) then
      Θ ⟨(t₀, t), ⟨le_rfl, h.1, h.2⟩⟩ else 0 with hG
  set G' : ℝ → ℝ := fun t => if h : t ∈ Set.Icc t₀ (t₀ + 2 * Real.pi) then
      Θ ⟨(t, t₀ + 2 * Real.pi), ⟨h.1, h.2, le_rfl⟩⟩ else 0 with hG'
  have hGcont : ContinuousOn G (Set.Icc t₀ (t₀ + 2 * Real.pi)) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hgI : Continuous (fun s : Set.Icc t₀ (t₀ + 2 * Real.pi) =>
        Θ ⟨(t₀, s.1), ⟨le_rfl, s.2.1, s.2.2⟩⟩) :=
      hΘc.comp (Continuous.subtype_mk
        (continuous_const.prodMk continuous_subtype_val)
        (fun s => ⟨le_rfl, s.2.1, s.2.2⟩))
    apply Continuous.congr hgI
    intro s
    rw [Set.domRestrict_apply, hG]
    simp only [dif_pos s.2]
  have hG'cont : ContinuousOn G' (Set.Icc t₀ (t₀ + 2 * Real.pi)) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hgI : Continuous (fun s : Set.Icc t₀ (t₀ + 2 * Real.pi) =>
        Θ ⟨(s.1, t₀ + 2 * Real.pi), ⟨s.2.1, s.2.2, le_rfl⟩⟩) :=
      hΘc.comp (Continuous.subtype_mk
        (continuous_subtype_val.prodMk continuous_const)
        (fun s => ⟨s.2.1, s.2.2, le_rfl⟩))
    apply Continuous.congr hgI
    intro s
    rw [Set.domRestrict_apply, hG']
    simp only [dif_pos s.2]
  have hGsin : ∀ t ∈ Set.Icc t₀ (t₀ + 2 * Real.pi), 0 ≤ Real.sin (G t) := by
    intro t ht
    have h1 : (((Circle.exp (G t)) : Circle) : ℂ).im = Real.sin (G t) := by
      rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_im]
    rw [← h1, hG]
    simp only [dif_pos ht]
    rw [hΘexp, sigma]
    exact sigmaPt_im_nonneg c hc hmin hderiv ht
  have hG'a : ∀ t ∈ Set.Icc t₀ (t₀ + 2 * Real.pi),
      Circle.exp (G' t) = -(Circle.exp (G t)) := by
    intro t ht
    rw [hG', hG]
    simp only [dif_pos ht]
    rw [hΘexp, hΘexp, sigma, sigma]
    exact sigmaPt_antisymm c hc ht
  have hrel : G' (t₀ + 2 * Real.pi) - G (t₀ + 2 * Real.pi) = G' t₀ - G t₀ := by
    have hPhi := eq_of_mem_period_multiples (f := fun t => G' t - G t - Real.pi)
      isPreconnected_Icc ((hG'cont.sub hGcont).sub continuousOn_const)
      (fun t ht => by
        have h1 : Circle.exp (G' t) = Circle.exp (G t + Real.pi) := by
          rw [hG'a t ht, umlauf_circle_exp_add_pi]
        obtain ⟨n, hn⟩ := Circle.exp_eq_exp.mp h1
        exact ⟨n, by linarith [hn]⟩)
    linarith [hPhi (t₀ + 2 * Real.pi) hIhi t₀ hIlo]
  -- values at the corners (named to keep the arithmetic below syntactic)
  set A : ℝ := Θ ⟨(t₀, t₀), ⟨le_rfl, le_rfl, by linarith [Real.pi_pos]⟩⟩ with hA
  set B : ℝ := Θ ⟨(t₀, t₀ + 2 * Real.pi), ⟨le_rfl, by linarith [Real.pi_pos], le_rfl⟩⟩ with hB
  set D : ℝ := Θ ⟨(t₀ + 2 * Real.pi, t₀ + 2 * Real.pi),
      ⟨by linarith [Real.pi_pos], le_rfl, le_rfl⟩⟩ with hD
  have hG₀ : G t₀ = A := by rw [hA, hG]; simp only [dif_pos hIlo]
  have hGhi : G (t₀ + 2 * Real.pi) = B := by rw [hB, hG]; simp only [dif_pos hIhi]
  have hG'₀ : G' t₀ = B := by rw [hB, hG']; simp only [dif_pos hIlo]
  have hG'hi : G' (t₀ + 2 * Real.pi) = D := by rw [hD, hG']; simp only [dif_pos hIhi]
  have hdiag_lo : θ t₀ = A := by rw [hA]; exact hdiag ⟨t₀, hIlo⟩
  have hdiag_hi : θ (t₀ + 2 * Real.pi) = D := by rw [hD]; exact hdiag ⟨t₀ + 2 * Real.pi, hIhi⟩
  have hbase' : A = θ t₀ := by
    rw [hA]
    rw [← show triBase t₀ = ⟨(t₀, t₀), ⟨le_rfl, le_rfl, by linarith [Real.pi_pos]⟩⟩
        from Subtype.ext rfl]
    exact hΘbase
  have hdiagch : θ (t₀ + 2 * Real.pi) - θ t₀ = D - A := by rw [hdiag_hi, hdiag_lo]
  -- ### Step 3: the two cases for the sign of the turning
  have hval : θ (t₀ + 2 * Real.pi) - θ t₀ = 2 * Real.pi ∨
      θ (t₀ + 2 * Real.pi) - θ t₀ = -2 * Real.pi := by
    rcases tangDir_eq_one_or_neg_one c hc hderiv with hpos | hneg
    · left
      have hGa : Circle.exp (G t₀) = 1 := by
        rw [hG₀, hA, hΘexp]
        show sigmaPt c t₀ (t₀, t₀) = 1
        rw [umlauf_sigmaPt_diag, hpos]
      have hGb : Circle.exp (G (t₀ + 2 * Real.pi)) = -1 := by
        rw [hGhi, hB, hΘexp]
        show sigmaPt c t₀ (t₀, t₀ + 2 * Real.pi) = -1
        rw [umlauf_sigmaPt_corner, hpos]
      have hδ : G (t₀ + 2 * Real.pi) - G t₀ = Real.pi :=
        strip_change_pos (by linarith [Real.pi_pos]) hGcont hGsin hGa hGb
      linarith [hdiagch, hrel, hδ, hG₀, hGhi, hG'₀, hG'hi]
    · right
      have hGa : Circle.exp (G t₀) = -1 := by
        rw [hG₀, hA, hΘexp]
        show sigmaPt c t₀ (t₀, t₀) = -1
        rw [umlauf_sigmaPt_diag, hneg]
      have hGb : Circle.exp (G (t₀ + 2 * Real.pi)) = 1 := by
        rw [hGhi, hB, hΘexp]
        show sigmaPt c t₀ (t₀, t₀ + 2 * Real.pi) = 1
        rw [umlauf_sigmaPt_corner, hneg]
        simp
      have hδ : G (t₀ + 2 * Real.pi) - G t₀ = -Real.pi :=
        strip_change_neg (by linarith [Real.pi_pos]) hGcont hGsin hGa hGb
      linarith [hdiagch, hrel, hδ, hG₀, hGhi, hG'₀, hG'hi]
  -- ### Step 4: constancy of the increment spreads the value to all `t`
  obtain ⟨ε, hε, hεval⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      θ (t₀ + 2 * Real.pi) - θ t₀ = 2 * Real.pi * (ε : ℝ) := by
    rcases hval with h | h
    · exact ⟨1, Or.inl rfl, by push_cast; linarith⟩
    · exact ⟨-1, Or.inr rfl, by push_cast; linarith⟩
  refine ⟨ε, hε, fun t => ?_⟩
  have hvalz : ∀ t : ℝ, ∃ n : ℤ, θ (t + 2 * Real.pi) - θ t = n * (2 * Real.pi) := by
    intro t
    have h1 : Circle.exp (θ (t + 2 * Real.pi)) = Circle.exp (θ t) := by
      rw [hθ (t + 2 * Real.pi), hθ t, tangDir, tangDir, hc.deriv_periodic t]
    obtain ⟨n, hn⟩ := Circle.exp_eq_exp.mp h1
    exact ⟨n, by linarith [hn]⟩
  have hconst : ∀ x y : ℝ, θ (x + 2 * Real.pi) - θ x = θ (y + 2 * Real.pi) - θ y := by
    have h := eq_of_mem_period_multiples (f := fun t => θ (t + 2 * Real.pi) - θ t)
      isPreconnected_univ ((hθc.comp (continuous_id.add continuous_const)).sub hθc).continuousOn
      (fun t _ => hvalz t)
    intro x y
    exact h x trivial y trivial
  rw [hconst t t₀]
  exact hεval

/-- Hopf's Umlaufsatz for smooth embedded closed plane curves. -/
theorem umlauf : Submission.Drive.UmlaufProp := by
  intro γ hγ
  have hcont : ContDiff ℝ 1 (curve γ) :=
    (hγ.contMDiff.comp contMDiff_circleExp).contDiff.of_le (by simp)
  have hreg : RegCurve (curve γ) :=
    { contDiff := hcont
      deriv_ne_zero := curve_deriv_ne_zero γ hγ
      periodic := curve_periodic γ
      eq_iff := curve_eq_iff γ hγ
      deriv_periodic := deriv_curve_periodic γ hγ }
  obtain ⟨θ, hθc, hθ⟩ := exists_angle_line (curve γ) hreg
  obtain ⟨ε, hε, hper⟩ := winding_curve (curve γ) hreg θ hθc hθ
  refine ⟨θ, fun t => ‖toC (deriv (curve γ) t)‖, ε, hε, hθc, ?_, ?_, hper⟩
  · intro t
    rw [norm_pos_iff, toC_ne_zero_iff]
    exact curve_deriv_ne_zero γ hγ t
  · intro t
    have hz : toC (deriv (curve γ) t) ≠ 0 := by
      rw [toC_ne_zero_iff]
      exact curve_deriv_ne_zero γ hγ t
    have hnorm : (‖toC (deriv (curve γ) t)‖ : ℂ) ≠ 0 := by
      simpa using (norm_ne_zero_iff.mpr hz)
    have h1 : Complex.exp ((θ t : ℝ) * Complex.I) =
        toC (deriv (curve γ) t) / (‖toC (deriv (curve γ) t)‖ : ℂ) := by
      rw [← Circle.coe_exp, hθ t, tangDir, dirOf_coe hz]
    have key : toC (deriv (curve γ) t) =
        (‖toC (deriv (curve γ) t)‖ : ℂ) * Complex.exp ((θ t : ℝ) * Complex.I) := by
      rw [h1]
      field_simp
    apply toC_injective
    show toC (deriv (fun s => γ (Circle.exp s)) t) =
      toC ((‖toC (deriv (curve γ) t)‖) • (Real.cos (θ t), Real.sin (θ t)))
    rw [toC_smul, toC_cos_sin]
    exact key

end Work.Drive
