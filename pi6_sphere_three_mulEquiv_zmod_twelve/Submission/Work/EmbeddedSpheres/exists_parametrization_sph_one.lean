import Mathlib
import Submission.Work.EmbeddedSpheres.Inputs

set_option synthInstance.maxHeartbeats 400000

/-!
# A parametrization of the circle `S¹ = Sph 1` by the interval `[0,1]`

The map `t ↦ (cos (2π t), sin (2π t))` from the unit interval onto the unit circle: it is
continuous, it identifies the two endpoints (`p 0 = p 1`), it is surjective, and it is injective
away from that single identification.
-/

namespace Work.EmbeddedSpheres

noncomputable section

open Work.Surgery

/-- The point `(cos θ, sin θ)` of the plane, in the model `EuclideanSpace ℝ (Fin 2)`. -/
noncomputable def s1ParamPoint (θ : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (fun i : Fin 2 => if i = (0 : Fin 2) then Real.cos θ else Real.sin θ)

@[simp] lemma s1ParamPoint_ofLp_zero (θ : ℝ) :
    (s1ParamPoint θ).ofLp (0 : Fin 2) = Real.cos θ := by
  simp [s1ParamPoint]

@[simp] lemma s1ParamPoint_ofLp_one (θ : ℝ) :
    (s1ParamPoint θ).ofLp (1 : Fin 2) = Real.sin θ := by
  simp [s1ParamPoint]

lemma s1ParamPoint_norm (θ : ℝ) : ‖s1ParamPoint θ‖ = 1 := by
  have h := EuclideanSpace.norm_sq_eq (s1ParamPoint θ)
  rw [Fin.sum_univ_two, s1ParamPoint_ofLp_zero, s1ParamPoint_ofLp_one] at h
  simp only [Real.norm_eq_abs, sq_abs] at h
  rw [Real.cos_sq_add_sin_sq] at h
  nlinarith [norm_nonneg (s1ParamPoint θ)]

theorem continuous_s1ParamPoint : Continuous s1ParamPoint := by
  unfold s1ParamPoint
  refine (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 2 => ℝ)).comp ?_
  refine continuous_pi (fun i => ?_)
  by_cases hi : i = (0 : Fin 2)
  · subst hi; simp only [if_true]; exact Real.continuous_cos
  · simp only [if_neg hi]; exact Real.continuous_sin

/-- The circle element `(cos θ, sin θ) ∈ S¹`. -/
noncomputable def s1CircleParam (θ : ℝ) : Work.Surgery.Sph 1 :=
  ⟨s1ParamPoint θ, by rw [Metric.mem_sphere, dist_zero_right]; exact s1ParamPoint_norm θ⟩

@[simp] lemma s1CircleParam_coe (θ : ℝ) :
    ((s1CircleParam θ : Work.Surgery.Sph 1) : EuclideanSpace ℝ (Fin 2)) = s1ParamPoint θ := rfl

theorem continuous_s1CircleParam : Continuous s1CircleParam :=
  Continuous.subtype_mk continuous_s1ParamPoint fun θ => (s1CircleParam θ).2

lemma s1ParamPoint_inj_iff (θ φ : ℝ) :
    s1ParamPoint θ = s1ParamPoint φ ↔ Real.cos θ = Real.cos φ ∧ Real.sin θ = Real.sin φ := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg (fun x => x.ofLp (0 : Fin 2)) h,
           by simpa using congrArg (fun x => x.ofLp (1 : Fin 2)) h⟩
  · rintro ⟨h0, h1⟩
    apply WithLp.ofLp_injective
    funext i
    fin_cases i <;> simp [h0, h1]

lemma s1CircleParam_eq_iff (θ φ : ℝ) :
    s1CircleParam θ = s1CircleParam φ ↔
      Real.cos θ = Real.cos φ ∧ Real.sin θ = Real.sin φ := by
  rw [Subtype.ext_iff, s1CircleParam_coe, s1CircleParam_coe, s1ParamPoint_inj_iff]

lemma ofLp_norm_sq_eq (v : EuclideanSpace ℝ (Fin 2)) :
    v.ofLp 0 ^ 2 + v.ofLp 1 ^ 2 = ‖v‖ ^ 2 := by
  have h := EuclideanSpace.norm_sq_eq v
  rw [Fin.sum_univ_two] at h
  simpa only [Real.norm_eq_abs, sq_abs] using h.symm

/-- Every point of the circle is `(cos θ, sin θ)` for some `θ ∈ [0, 2π]`. -/
lemma s1CircleParam_surj (y : Work.Surgery.Sph 1) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 2 * Real.pi ∧ s1CircleParam θ = y := by
  have hnorm : ‖(y : EuclideanSpace ℝ (Fin 2))‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using y.2
  have hsq : ((y : EuclideanSpace ℝ (Fin 2)).ofLp 0) ^ 2
      + ((y : EuclideanSpace ℝ (Fin 2)).ofLp 1) ^ 2 = 1 := by
    rw [ofLp_norm_sq_eq, hnorm]; norm_num
  set a : ℝ := (y : EuclideanSpace ℝ (Fin 2)).ofLp 0 with ha
  set b : ℝ := (y : EuclideanSpace ℝ (Fin 2)).ofLp 1 with hb
  have ha_sq : a ^ 2 ≤ 1 := by
    have : b ^ 2 ≥ 0 := sq_nonneg b
    nlinarith [hsq]
  have ha_low : -1 ≤ a := (abs_le.mp ((sq_le_one_iff_abs_le_one a).mp ha_sq)).1
  have ha_high : a ≤ 1 := (abs_le.mp ((sq_le_one_iff_abs_le_one a).mp ha_sq)).2
  have h1ma : 1 - a ^ 2 = b ^ 2 := by nlinarith [hsq]
  have hsq_abs : Real.sqrt (1 - a ^ 2) = |b| := by
    rw [h1ma, Real.sqrt_sq_eq_abs]
  have key : ∀ θ : ℝ, Real.cos θ = a → Real.sin θ = b → s1CircleParam θ = y := by
    intro θ hc hs
    rw [Subtype.ext_iff, s1CircleParam_coe]
    apply WithLp.ofLp_injective
    funext i
    fin_cases i
    · simpa [ha] using hc
    · simpa [hb] using hs
  by_cases hb0 : 0 ≤ b
  · refine ⟨Real.arccos a, Real.arccos_nonneg a, ?_, ?_⟩
    · linarith [Real.arccos_le_pi a, Real.pi_pos]
    · apply key
      · exact Real.cos_arccos ha_low ha_high
      · rw [Real.sin_arccos, hsq_abs, abs_of_nonneg hb0]
  · refine ⟨2 * Real.pi - Real.arccos a, ?_, ?_, ?_⟩
    · have := Real.arccos_le_pi a; linarith [Real.pi_pos]
    · have := Real.arccos_nonneg a; linarith
    · apply key
      · rw [Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi, Real.cos_arccos ha_low ha_high]
        ring
      · rw [Real.sin_sub, Real.cos_two_pi, Real.sin_two_pi, Real.cos_arccos ha_low ha_high,
            Real.sin_arccos, hsq_abs, abs_of_neg (lt_of_not_ge hb0)]
        ring

/-- The parametrization of the circle by the unit interval. -/
noncomputable def s1ParamCm : C(Set.Icc (0 : ℝ) 1, Work.Surgery.Sph 1) where
  toFun t := s1CircleParam (2 * Real.pi * (t : ℝ))
  continuous_toFun :=
    continuous_s1CircleParam.comp (continuous_const.mul continuous_subtype_val)

@[simp] lemma s1ParamCm_apply (t : Set.Icc (0 : ℝ) 1) :
    s1ParamCm t = s1CircleParam (2 * Real.pi * (t : ℝ)) := rfl

lemma s1ParamCm_zero_eq_one : s1ParamCm (0 : Set.Icc (0 : ℝ) 1) = s1ParamCm 1 := by
  have h0 : ((0 : Set.Icc (0 : ℝ) 1) : ℝ) = 0 := rfl
  have h1 : ((1 : Set.Icc (0 : ℝ) 1) : ℝ) = 1 := rfl
  rw [s1ParamCm_apply, s1ParamCm_apply, h0, h1, s1CircleParam_eq_iff]
  exact ⟨by simp [Real.cos_zero, Real.cos_two_pi],
         by simp [Real.sin_zero, Real.sin_two_pi]⟩

lemma s1ParamCm_surjective : Function.Surjective ⇑s1ParamCm := by
  intro y
  obtain ⟨θ, hθ0, hθ2, hy⟩ := s1CircleParam_surj y
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  refine ⟨⟨θ / (2 * Real.pi), ⟨?_, ?_⟩⟩, ?_⟩
  · exact div_nonneg hθ0 (le_of_lt hπ)
  · rw [div_le_iff₀ hπ]; linarith
  · show s1ParamCm ⟨θ / (2 * Real.pi), _⟩ = y
    rw [s1ParamCm_apply]
    have h2 : 2 * Real.pi * (θ / (2 * Real.pi)) = θ := by
      field_simp
    rw [h2, hy]

lemma s1ParamCm_inj (s t : Set.Icc (0 : ℝ) 1) (h : s1ParamCm s = s1ParamCm t) :
    s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
  have hcos : Real.cos (2 * Real.pi * (s : ℝ)) = Real.cos (2 * Real.pi * (t : ℝ)) := by
    have := congrArg (fun z : Work.Surgery.Sph 1 =>
      ((z : EuclideanSpace ℝ (Fin 2))).ofLp 0) h
    simpa using this
  have hsin : Real.sin (2 * Real.pi * (s : ℝ)) = Real.sin (2 * Real.pi * (t : ℝ)) := by
    have := congrArg (fun z : Work.Surgery.Sph 1 =>
      ((z : EuclideanSpace ℝ (Fin 2))).ofLp 1) h
    simpa using this
  have hcosd : Real.cos (2 * Real.pi * (s : ℝ) - 2 * Real.pi * (t : ℝ)) = 1 := by
    rw [Real.cos_sub, hcos, hsin]
    have := Real.cos_sq_add_sin_sq (2 * Real.pi * (t : ℝ))
    nlinarith
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).mp hcosd
  have h2pi : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  have hn_eq : (n : ℝ) = (s : ℝ) - (t : ℝ) := by
    apply mul_left_cancel₀ h2pi
    have hn' : (n : ℝ) * (2 * Real.pi) = 2 * Real.pi * (s : ℝ) - 2 * Real.pi * (t : ℝ) := hn
    nlinarith
  have hnb : (-1 : ℤ) ≤ n ∧ n ≤ 1 := by
    constructor
    · have : (-1 : ℝ) ≤ (n : ℝ) := by rw [hn_eq]; linarith [s.2.1, t.2.2]
      exact_mod_cast this
    · have : (n : ℝ) ≤ 1 := by rw [hn_eq]; linarith [s.2.2, t.2.1]
      exact_mod_cast this
  obtain ⟨hn1, hn2⟩ := hnb
  have hn_cases : n = -1 ∨ n = 0 ∨ n = 1 := by omega
  rcases hn_cases with h | h | h
  · right; left
    refine ⟨?_, ?_⟩
    · apply Subtype.ext; show (s : ℝ) = (0 : ℝ)
      rw [h] at hn_eq; push_cast at hn_eq; linarith [s.2.1, t.2.2]
    · apply Subtype.ext; show (t : ℝ) = (1 : ℝ)
      rw [h] at hn_eq; push_cast at hn_eq; linarith [s.2.1, t.2.2]
  · left; apply Subtype.ext
    rw [h] at hn_eq; push_cast at hn_eq; linarith
  · right; right
    refine ⟨?_, ?_⟩
    · apply Subtype.ext; show (s : ℝ) = (1 : ℝ)
      rw [h] at hn_eq; push_cast at hn_eq; linarith [s.2.2, t.2.1]
    · apply Subtype.ext; show (t : ℝ) = (0 : ℝ)
      rw [h] at hn_eq; push_cast at hn_eq; linarith [s.2.2, t.2.1]

theorem exists_parametrization_sph_one :
    ∃ p : C(Set.Icc (0 : ℝ) 1, Work.Surgery.Sph 1),
      p 0 = p 1 ∧ Function.Surjective ⇑p ∧
      (∀ s t : Set.Icc (0 : ℝ) 1, p s = p t → s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) :=
  ⟨s1ParamCm, s1ParamCm_zero_eq_one, s1ParamCm_surjective, s1ParamCm_inj⟩

end

end Work.EmbeddedSpheres
