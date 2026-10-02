import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Topology

open Set Metric Real

noncomputable section

/-! ## Arcs of the unit circle

We build the two closed arcs of the unit circle joining two points in opposite open half planes,
and prove the elementary properties needed later.  The basic object is `arcMap a b`, the
parametrisation `t ↦ exp ((a + t (b - a)) I)` of the (short) arc from `exp (a I)` to `exp (b I)`. -/

/-- `exp (θ I)` as a function of the real angle `θ`. -/
def cexpI (θ : ℝ) : ℂ := Complex.exp (↑θ * Complex.I)

lemma cexpI_apply (θ : ℝ) : cexpI θ = Complex.exp (↑θ * Complex.I) := rfl

lemma continuous_cexpI : Continuous cexpI := by
  rw [show cexpI = fun θ : ℝ => Complex.exp (↑θ * Complex.I) from rfl]
  fun_prop

lemma cexpI_eq_coe (θ : ℝ) : cexpI θ = (Circle.exp θ : ℂ) := by
  rw [cexpI_apply, Circle.coe_exp]

@[simp] lemma cexpI_zero : cexpI 0 = 1 := by
  rw [cexpI_eq_coe, Circle.exp_zero, Circle.coe_one]

lemma cexpI_add (x y : ℝ) : cexpI (x + y) = cexpI x * cexpI y := by
  rw [cexpI_eq_coe, cexpI_eq_coe, cexpI_eq_coe, ← Circle.coe_mul, Circle.exp_add]

lemma cexpI_two_pi : cexpI (2 * π) = 1 := by
  rw [cexpI_eq_coe, Circle.exp_two_pi, Circle.coe_one]

lemma cexpI_add_two_pi (θ : ℝ) : cexpI (θ + 2 * π) = cexpI θ := by
  rw [cexpI_add, cexpI_two_pi, mul_one]

lemma cexpI_sub_two_pi (θ : ℝ) : cexpI (θ - 2 * π) = cexpI θ := by
  rw [cexpI_eq_coe, cexpI_eq_coe, Circle.exp_sub, Circle.exp_two_pi, div_one]

lemma cexpI_pi : cexpI π = -1 := by
  rw [cexpI_apply, Complex.exp_pi_mul_I]

lemma cexpI_neg_pi : cexpI (-π) = -1 := by
  have h := cexpI_add_two_pi (-π)
  rw [show -π + 2 * π = π by ring, cexpI_pi] at h
  exact h.symm

/-- The parametrisation `t ↦ exp ((a + t (b - a)) I)` of the arc of the unit circle from
`exp (a I)` to `exp (b I)`. -/
def arcMap (a b : ℝ) : C(Set.Icc (0:ℝ) 1, ℂ) where
  toFun t := cexpI (a + (t:ℝ) * (b - a))
  continuous_toFun := continuous_cexpI.comp (by fun_prop)

@[simp] lemma arcMap_apply (a b : ℝ) (t : Set.Icc (0:ℝ) 1) :
    arcMap a b t = cexpI (a + (t:ℝ) * (b - a)) := rfl

@[simp] lemma arcMap_zero (a b : ℝ) : arcMap a b 0 = cexpI a := by simp [arcMap]

@[simp] lemma arcMap_one (a b : ℝ) : arcMap a b 1 = cexpI b := by simp [arcMap]

lemma arcMap_mem_sphere (a b : ℝ) (t : Set.Icc (0:ℝ) 1) :
    arcMap a b t ∈ Metric.sphere (0:ℂ) 1 := by
  rw [Metric.mem_sphere, dist_zero_right, arcMap_apply, Subtype.coe_mk, cexpI_eq_coe]
  exact Circle.norm_coe _

/-- `θ ↦ exp (θ I)` is injective on any interval of length `< 2π`. -/
lemma cexpI_injOn {a b : ℝ} (h : |b - a| < 2 * π) :
    Set.InjOn cexpI (Set.Icc (min a b) (max a b)) := by
  have hmax : max a b - min a b < 2 * π := by rw [max_sub_min_eq_abs]; exact h
  intro x hx y hy hxy
  rw [cexpI_eq_coe, cexpI_eq_coe] at hxy
  exact Circle.exp_injOn_Icc hmax hx hy (Circle.coe_injective hxy)

lemma angle_mem_Icc (a b t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    a + t * (b - a) ∈ Set.Icc (min a b) (max a b) := by
  rcases le_total a b with hab | hab
  · rw [min_eq_left hab, max_eq_right hab]
    constructor
    · nlinarith [ht.1, mul_nonneg ht.1 (sub_nonneg.mpr hab)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hab)]
  · rw [min_eq_right hab, max_eq_left hab]
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hab)]
    · nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hab)]

/-- Every point of the arc joining `exp (a I)` to `exp (b I)` is in the range of `arcMap a b`. -/
lemma cexpI_mem_range_arcMap {a b : ℝ} (hab : a ≠ b) {θ : ℝ}
    (hθ : θ ∈ Set.Icc (min a b) (max a b)) :
    cexpI θ ∈ Set.range (arcMap a b) := by
  rcases lt_or_gt_of_ne hab with hab' | hab'
  · rw [min_eq_left hab'.le, max_eq_right hab'.le] at hθ
    obtain ⟨hθ1, hθ2⟩ := Set.mem_Icc.mp hθ
    have hdpos : 0 < b - a := sub_pos.mpr hab'
    refine ⟨⟨(θ - a) / (b - a), ?_, ?_⟩, ?_⟩
    · exact div_nonneg (by linarith) hdpos.le
    · rw [div_le_one hdpos]; linarith
    · rw [arcMap_apply]
      change cexpI (a + ((θ - a) / (b - a)) * (b - a)) = cexpI θ
      rw [show a + ((θ - a) / (b - a)) * (b - a) = θ by field_simp; ring]
  · rw [min_eq_right hab'.le, max_eq_left hab'.le] at hθ
    obtain ⟨hθ1, hθ2⟩ := Set.mem_Icc.mp hθ
    have hdneg : b - a < 0 := sub_neg.mpr hab'
    refine ⟨⟨(θ - a) / (b - a), ?_, ?_⟩, ?_⟩
    · exact div_nonneg_of_nonpos (by linarith) hdneg.le
    · rw [div_le_one_of_neg hdneg]; linarith
    · rw [arcMap_apply]
      change cexpI (a + ((θ - a) / (b - a)) * (b - a)) = cexpI θ
      rw [show a + ((θ - a) / (b - a)) * (b - a) = θ by field_simp; ring]

/-- `arcMap a b` is injective when the two angles are distinct and less than `2π` apart. -/
lemma arcMap_injective {a b : ℝ} (h : |b - a| < 2 * π) (hab : a ≠ b) :
    Function.Injective (arcMap a b) := by
  intro s t hst
  have hs := angle_mem_Icc a b s.1 s.2
  have ht := angle_mem_Icc a b t.1 t.2
  have hst' : cexpI (a + (s:ℝ) * (b - a)) = cexpI (a + (t:ℝ) * (b - a)) := hst
  have hkey : a + (s:ℝ) * (b - a) = a + (t:ℝ) * (b - a) :=
    cexpI_injOn h hs ht hst'
  have hbd : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hmul : (s:ℝ) * (b - a) = (t:ℝ) * (b - a) := by linarith
  exact Subtype.ext (mul_right_cancel₀ hbd hmul)

/-- Two angles whose exponentials coincide differ by a multiple of `2π`. -/
lemma exists_int_angle_sub {a b c s t : ℝ}
    (h : cexpI (a + s * (c - a)) = cexpI (a + t * (b - a))) :
    ∃ m : ℤ, a + s * (c - a) - (a + t * (b - a)) = (m:ℝ) * (2 * π) := by
  rw [cexpI_eq_coe, cexpI_eq_coe] at h
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp (Circle.coe_injective h)
  exact ⟨m, by linarith⟩

/-- The "crossing" condition for the two arcs, in the case `b ≤ a < c`. -/
lemma arc_disj_up {a b c : ℝ} (hba : b ≤ a) (hac : a < c) (hcb : c - b ≤ 2 * π)
    {s t : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1) (ht : t ∈ Set.Icc (0:ℝ) 1)
    (h : cexpI (a + s * (c - a)) = cexpI (a + t * (b - a))) :
    s = 0 ∨ s = 1 := by
  obtain ⟨m, hd⟩ := exists_int_angle_sub h
  have hxle : a + s * (c - a) ≤ c := by nlinarith [hs.2, hac.le]
  have hxge : a ≤ a + s * (c - a) := by nlinarith [hs.1, hac.le]
  have hyle : a + t * (b - a) ≤ a := by nlinarith [ht.1, hba]
  have hyge : b ≤ a + t * (b - a) := by nlinarith [ht.2, hba]
  have hm0le : 0 ≤ (m:ℝ) * (2 * π) := by rw [← hd]; linarith
  have hm2 : (m:ℝ) * (2 * π) ≤ 2 * π := by rw [← hd]; linarith
  have hmle : (m:ℝ) ≤ 1 := by nlinarith [hm2, Real.two_pi_pos]
  have hmge : (0:ℝ) ≤ m := by nlinarith [hm0le, Real.two_pi_pos]
  have hm01 : m = 0 ∨ m = 1 := by
    have h1 : (0:ℤ) ≤ m := by exact_mod_cast hmge
    have h2 : m ≤ 1 := by exact_mod_cast hmle
    omega
  have hca : 0 < c - a := sub_pos.mpr hac
  rcases hm01 with hm0 | hm1
  · left
    have hxy : a + s * (c - a) = a + t * (b - a) := by
      rw [hm0] at hd; push_cast at hd; linarith
    have hxa : a + s * (c - a) = a := by linarith [hxy, hyle, hxge]
    have : s * (c - a) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right (ne_of_gt hca)
  · right
    have hxy : a + s * (c - a) = a + t * (b - a) + 2 * π := by
      rw [hm1] at hd; push_cast at hd; linarith
    have hxb : a + s * (c - a) = c := by
      have : c ≤ a + s * (c - a) := by linarith [hxy, hyge, hcb]
      linarith [this, hxle]
    have : s * (c - a) = 1 * (c - a) := by linarith
    exact mul_right_cancel₀ (ne_of_gt hca) this

/-- The mirror image of `arc_disj_up`, in the case `c < a ≤ b`. -/
lemma arc_disj_down {a b c : ℝ} (hca : c < a) (hab : a ≤ b) (hbc : b - c ≤ 2 * π)
    {s t : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1) (ht : t ∈ Set.Icc (0:ℝ) 1)
    (h : cexpI (a + s * (c - a)) = cexpI (a + t * (b - a))) :
    s = 0 ∨ s = 1 := by
  obtain ⟨m, hd⟩ := exists_int_angle_sub h
  have hxle : a + s * (c - a) ≤ a := by nlinarith [hs.1, hca.le]
  have hxge : c ≤ a + s * (c - a) := by nlinarith [hs.2, hca.le]
  have hyle : a + t * (b - a) ≤ b := by nlinarith [ht.2, hab]
  have hyge : a ≤ a + t * (b - a) := by nlinarith [ht.1, hab]
  have hmle : (m:ℝ) * (2 * π) ≤ 0 := by rw [← hd]; linarith
  have hmc : -(2 * π) ≤ (m:ℝ) * (2 * π) := by rw [← hd]; linarith
  have hm0 : (m:ℝ) ≤ 0 := by nlinarith [hmle, Real.two_pi_pos]
  have hm1 : (-1:ℝ) ≤ m := by nlinarith [hmc, Real.two_pi_pos]
  have hm01 : m = 0 ∨ m = -1 := by
    have h1 : m ≤ 0 := by exact_mod_cast hm0
    have h2 : (-1:ℤ) ≤ m := by exact_mod_cast hm1
    omega
  have hca' : c - a < 0 := sub_neg.mpr hca
  rcases hm01 with hm0' | hm1'
  · left
    have hxy : a + s * (c - a) = a + t * (b - a) := by
      rw [hm0'] at hd; push_cast at hd; linarith
    have hxa : a + s * (c - a) = a := by linarith [hxy, hxle, hyge]
    have : s * (c - a) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right (ne_of_lt hca')
  · right
    have hxy : a + s * (c - a) = a + t * (b - a) - 2 * π := by
      rw [hm1'] at hd; push_cast at hd; linarith
    have hxc : a + s * (c - a) = c := by
      have : a + s * (c - a) ≤ c := by linarith [hxy, hyle, hbc]
      linarith [this, hxge]
    have : s * (c - a) = 1 * (c - a) := by linarith
    exact mul_right_cancel₀ (ne_of_lt hca') this

/-- If `z` has positive imaginary part, its argument is positive. -/
lemma arg_pos_of_im_pos {z : ℂ} (hz : 0 < z.im) : 0 < z.arg := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have hsin : 0 < Real.sin z.arg := by
    rw [Complex.sin_arg, div_pos_iff]
    exact Or.inl ⟨hz, norm_pos_iff.mpr hz0⟩
  rcases lt_trichotomy z.arg 0 with h | h | h
  · linarith [Real.sin_neg_of_neg_of_neg_pi_lt h (Complex.neg_pi_lt_arg z)]
  · rw [h, Real.sin_zero] at hsin; exact absurd hsin (lt_irrefl 0)
  · exact h

/-- **The two closed arcs of the unit circle cut out by two points in opposite open half planes.**
If `p` and `q` are distinct points of the unit circle lying in opposite open half planes, then the
unit circle is the union of two arcs joining `p` to `q` meeting only in `p`, `q`; and the two points
`-1` and `1` lie on different ones of these arcs. -/
theorem sphere_arcs_of_opposite_halfplanes {p q : ℂ}
    (hp : p ∈ Metric.sphere (0:ℂ) 1) (hq : q ∈ Metric.sphere (0:ℂ) 1) (hpq : p ≠ q)
    (hsgn : (0 < p.im ∧ q.im < 0) ∨ (p.im < 0 ∧ 0 < q.im)) :
    ∃ α₁ α₂ : C(Set.Icc (0:ℝ) 1, ℂ),
      Function.Injective α₁ ∧ Function.Injective α₂ ∧
      (∀ t : Set.Icc (0:ℝ) 1, α₁ t ∈ Metric.sphere (0:ℂ) 1) ∧
      (∀ t : Set.Icc (0:ℝ) 1, α₂ t ∈ Metric.sphere (0:ℂ) 1) ∧
      α₁ 0 = p ∧ α₁ 1 = q ∧ α₂ 0 = p ∧ α₂ 1 = q ∧
      Set.range α₁ ∪ Set.range α₂ = Metric.sphere (0:ℂ) 1 ∧
      (∀ s t : Set.Icc (0:ℝ) 1, α₁ s = α₂ t → s = 0 ∨ s = 1) ∧
      (((-1 : ℂ) ∈ Set.range α₁ ∧ (1 : ℂ) ∈ Set.range α₂) ∨
        ((1 : ℂ) ∈ Set.range α₁ ∧ (-1 : ℂ) ∈ Set.range α₂)) := by
  have hpnorm : ‖p‖ = 1 := by
    have := Metric.mem_sphere.mp hp
    rwa [dist_zero_right] at this
  have hqnorm : ‖q‖ = 1 := by
    have := Metric.mem_sphere.mp hq
    rwa [dist_zero_right] at this
  have hpexp : cexpI p.arg = p := by
    have h := Complex.norm_mul_exp_arg_mul_I p
    rw [hpnorm] at h
    simpa [cexpI] using h
  have hqexp : cexpI q.arg = q := by
    have h := Complex.norm_mul_exp_arg_mul_I q
    rw [hqnorm] at h
    simpa [cexpI] using h
  rcases hsgn with ⟨hpim, hqim⟩ | ⟨hpim, hqim⟩
  · -- Case 1: `p` in the open upper half plane, `q` in the open lower half plane.
    have ha_pos : 0 < p.arg := arg_pos_of_im_pos hpim
    have ha_le : p.arg ≤ π := Complex.arg_le_pi p
    have hb_neg : q.arg < 0 := Complex.arg_neg_iff.mpr hqim
    have hb_gt : -π < q.arg := Complex.neg_pi_lt_arg q
    have hc_exp : cexpI (q.arg + 2 * π) = q := by rw [cexpI_add_two_pi]; exact hqexp
    have hba : q.arg ≤ p.arg := by linarith
    have hac : p.arg < q.arg + 2 * π := by linarith
    have hne1 : p.arg ≠ q.arg + 2 * π := ne_of_lt hac
    have hne2 : p.arg ≠ q.arg := by linarith
    have h2a : |q.arg - p.arg| < 2 * π := by
      rw [abs_lt]; constructor <;> linarith [ha_le, hb_gt, ha_pos, hb_neg]
    have h2b : |(q.arg + 2 * π) - p.arg| < 2 * π := by
      rw [abs_lt]; constructor <;> linarith [ha_le, hb_gt, ha_pos, hb_neg]
    have hmin_ab : min p.arg q.arg = q.arg := min_eq_right hba
    have hmax_ab : max p.arg q.arg = p.arg := max_eq_left hba
    have hmin_ac : min p.arg (q.arg + 2 * π) = p.arg := min_eq_left hac.le
    have hmax_ac : max p.arg (q.arg + 2 * π) = q.arg + 2 * π := max_eq_right hac.le
    refine ⟨arcMap p.arg (q.arg + 2 * π), arcMap p.arg q.arg,
      arcMap_injective h2b hne1, arcMap_injective h2a hne2,
      arcMap_mem_sphere _ _, arcMap_mem_sphere _ _,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [arcMap_zero, hpexp]
    · rw [arcMap_one, hc_exp]
    · rw [arcMap_zero, hpexp]
    · rw [arcMap_one, hqexp]
    · ext z
      constructor
      · rintro (⟨t, rfl⟩ | ⟨t, rfl⟩)
        · exact arcMap_mem_sphere _ _ t
        · exact arcMap_mem_sphere _ _ t
      · intro hz
        have hznorm : ‖z‖ = 1 := by
          have := Metric.mem_sphere.mp hz; rwa [dist_zero_right] at this
        have hzexp : cexpI z.arg = z := by
          have h := Complex.norm_mul_exp_arg_mul_I z
          rw [hznorm] at h; simpa [cexpI] using h
        have hθlo : -π < z.arg := (Complex.arg_mem_Ioc z).1
        have hθhi : z.arg ≤ π := (Complex.arg_mem_Ioc z).2
        rcases lt_or_ge z.arg q.arg with hlt | hge
        · refine Or.inl ?_
          have hshift : cexpI (z.arg + 2 * π) = z := by rw [cexpI_add_two_pi]; exact hzexp
          have hmem : z.arg + 2 * π ∈
              Set.Icc (min p.arg (q.arg + 2 * π)) (max p.arg (q.arg + 2 * π)) := by
            rw [hmin_ac, hmax_ac]
            exact ⟨by linarith [hθlo, ha_le], by linarith [hlt]⟩
          have := cexpI_mem_range_arcMap hne1 hmem
          rwa [hshift] at this
        · rcases lt_or_ge z.arg p.arg with hlt2 | hge2
          · refine Or.inr ?_
            have hmem : z.arg ∈ Set.Icc (min p.arg q.arg) (max p.arg q.arg) := by
              rw [hmin_ab, hmax_ab]
              exact ⟨hge, hlt2.le⟩
            have := cexpI_mem_range_arcMap hne2 hmem
            rwa [hzexp] at this
          · refine Or.inl ?_
            have hmem : z.arg ∈
                Set.Icc (min p.arg (q.arg + 2 * π)) (max p.arg (q.arg + 2 * π)) := by
              rw [hmin_ac, hmax_ac]
              exact ⟨hge2, by linarith [hθhi, hb_gt]⟩
            have := cexpI_mem_range_arcMap hne1 hmem
            rwa [hzexp] at this
    · intro s t hst
      rcases arc_disj_up hba hac (by rw [add_sub_cancel_left]) s.2 t.2 hst with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · refine Or.inl ⟨?_, ?_⟩
      · have hmem : π ∈ Set.Icc (min p.arg (q.arg + 2 * π)) (max p.arg (q.arg + 2 * π)) := by
          rw [hmin_ac, hmax_ac]; exact ⟨ha_le, by linarith [hb_gt]⟩
        have h := cexpI_mem_range_arcMap (a := p.arg) (b := q.arg + 2 * π) hne1 (θ := π) hmem
        rwa [cexpI_pi] at h
      · have hmem : (0:ℝ) ∈ Set.Icc (min p.arg q.arg) (max p.arg q.arg) := by
          rw [hmin_ab, hmax_ab]; exact ⟨hb_neg.le, ha_pos.le⟩
        have h := cexpI_mem_range_arcMap (a := p.arg) (b := q.arg) hne2 (θ := 0) hmem
        rwa [cexpI_zero] at h
  · -- Case 2: `p` in the open lower half plane, `q` in the open upper half plane.
    have ha_neg : p.arg < 0 := Complex.arg_neg_iff.mpr hpim
    have ha_gt : -π < p.arg := Complex.neg_pi_lt_arg p
    have hb_pos : 0 < q.arg := arg_pos_of_im_pos hqim
    have hb_le : q.arg ≤ π := Complex.arg_le_pi q
    have hc_exp : cexpI (q.arg - 2 * π) = q := by rw [cexpI_sub_two_pi]; exact hqexp
    have hne1 : p.arg ≠ q.arg - 2 * π := by linarith
    have hne2 : p.arg ≠ q.arg := by linarith
    have h2a : |q.arg - p.arg| < 2 * π := by
      rw [abs_lt]; constructor <;> linarith [ha_neg, ha_gt, hb_pos, hb_le]
    have h2b : |(q.arg - 2 * π) - p.arg| < 2 * π := by
      rw [abs_lt]; constructor <;> linarith [ha_neg, ha_gt, hb_pos, hb_le]
    have hc_lt_a : q.arg - 2 * π < p.arg := by linarith
    have ha_le_b : p.arg ≤ q.arg := by linarith
    have hmin_ab : min p.arg q.arg = p.arg := min_eq_left ha_le_b
    have hmax_ab : max p.arg q.arg = q.arg := max_eq_right ha_le_b
    have hmin_ac : min p.arg (q.arg - 2 * π) = q.arg - 2 * π := min_eq_right hc_lt_a.le
    have hmax_ac : max p.arg (q.arg - 2 * π) = p.arg := max_eq_left hc_lt_a.le
    refine ⟨arcMap p.arg (q.arg - 2 * π), arcMap p.arg q.arg,
      arcMap_injective h2b hne1, arcMap_injective h2a hne2,
      arcMap_mem_sphere _ _, arcMap_mem_sphere _ _,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [arcMap_zero, hpexp]
    · rw [arcMap_one, hc_exp]
    · rw [arcMap_zero, hpexp]
    · rw [arcMap_one, hqexp]
    · ext z
      constructor
      · rintro (⟨t, rfl⟩ | ⟨t, rfl⟩)
        · exact arcMap_mem_sphere _ _ t
        · exact arcMap_mem_sphere _ _ t
      · intro hz
        have hznorm : ‖z‖ = 1 := by
          have := Metric.mem_sphere.mp hz; rwa [dist_zero_right] at this
        have hzexp : cexpI z.arg = z := by
          have h := Complex.norm_mul_exp_arg_mul_I z
          rw [hznorm] at h; simpa [cexpI] using h
        have hθlo : -π < z.arg := (Complex.arg_mem_Ioc z).1
        have hθhi : z.arg ≤ π := (Complex.arg_mem_Ioc z).2
        rcases lt_or_ge z.arg p.arg with hlt | hge
        · refine Or.inl ?_
          have hmem : z.arg ∈
              Set.Icc (min p.arg (q.arg - 2 * π)) (max p.arg (q.arg - 2 * π)) := by
            rw [hmin_ac, hmax_ac]
            exact ⟨by linarith [hθlo, hb_le], hlt.le⟩
          have := cexpI_mem_range_arcMap hne1 hmem
          rwa [hzexp] at this
        · rcases lt_or_ge z.arg q.arg with hlt2 | hge2
          · refine Or.inr ?_
            have hmem : z.arg ∈ Set.Icc (min p.arg q.arg) (max p.arg q.arg) := by
              rw [hmin_ab, hmax_ab]
              exact ⟨hge, hlt2.le⟩
            have := cexpI_mem_range_arcMap hne2 hmem
            rwa [hzexp] at this
          · refine Or.inl ?_
            have hshift : cexpI (z.arg - 2 * π) = z := by rw [cexpI_sub_two_pi]; exact hzexp
            have hmem : z.arg - 2 * π ∈
                Set.Icc (min p.arg (q.arg - 2 * π)) (max p.arg (q.arg - 2 * π)) := by
              rw [hmin_ac, hmax_ac]
              exact ⟨by linarith [hge2], by linarith [hθhi, ha_gt]⟩
            have := cexpI_mem_range_arcMap hne1 hmem
            rwa [hshift] at this
    · intro s t hst
      rcases arc_disj_down hc_lt_a ha_le_b (by linarith) s.2 t.2 hst with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · refine Or.inl ⟨?_, ?_⟩
      · have hmem : (-π) ∈ Set.Icc (min p.arg (q.arg - 2 * π)) (max p.arg (q.arg - 2 * π)) := by
          rw [hmin_ac, hmax_ac]; exact ⟨by linarith [hb_le], ha_gt.le⟩
        have h := cexpI_mem_range_arcMap (a := p.arg) (b := q.arg - 2 * π) hne1 (θ := -π) hmem
        rwa [cexpI_neg_pi] at h
      · have hmem : (0:ℝ) ∈ Set.Icc (min p.arg q.arg) (max p.arg q.arg) := by
          rw [hmin_ab, hmax_ab]; exact ⟨ha_neg.le, hb_pos.le⟩
        have h := cexpI_mem_range_arcMap (a := p.arg) (b := q.arg) hne2 (θ := 0) hmem
        rwa [cexpI_zero] at h

end

end Work.Topology
