import Mathlib
import Submission.Work.Smooth.SphereJordan.planeIndex
import Submission.Work.Smooth.SphereJordan.planeIndexGeom
import Submission.Work.Smooth.SphereJordan.loopIndex_eq_of_homotopy

open Set
open Work.Smooth.SphereJordan
namespace Work.Topology.PlaneCurve
namespace PlaneCrossing
noncomputable section

/-! ### The reference loop σ -/

def theta (τ : unitInterval) : ℝ := 3 * Real.pi / 4 - 2 * Real.pi * (τ : ℝ)

def sigma : C(unitInterval, ℂ) :=
  ⟨fun τ => Complex.exp (((theta τ : ℝ) : ℂ) * Complex.I), by unfold theta; fun_prop⟩

lemma sigma_re (τ : unitInterval) : (sigma τ).re = Real.cos (theta τ) := by
  have h : sigma τ = (Real.cos (theta τ) : ℂ) + (Real.sin (theta τ) : ℂ) * Complex.I := by
    simp only [sigma, ContinuousMap.coe_mk]
    exact Complex.exp_ofReal_mul_I (theta τ)
  rw [h]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, sub_zero, add_zero]

lemma sigma_im (τ : unitInterval) : (sigma τ).im = Real.sin (theta τ) := by
  have h : sigma τ = (Real.cos (theta τ) : ℂ) + (Real.sin (theta τ) : ℂ) * Complex.I := by
    simp only [sigma, ContinuousMap.coe_mk]
    exact Complex.exp_ofReal_mul_I (theta τ)
  rw [h]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, zero_add, add_zero]

lemma sigma_ne_zero (τ : unitInterval) : sigma τ ≠ 0 := by
  simp only [sigma, ContinuousMap.coe_mk]
  exact Complex.exp_ne_zero _

lemma sigma_im_pos (τ : unitInterval) (h : (τ:ℝ) ≤ 1/4) : 0 < (sigma τ).im := by
  rw [sigma_im]
  apply Real.sin_pos_of_mem_Ioo
  constructor <;> unfold theta <;> nlinarith [Real.pi_pos, τ.2.1, τ.2.2]

lemma sigma_re_pos (τ : unitInterval) (h1 : 1/4 ≤ (τ:ℝ)) (h2 : (τ:ℝ) ≤ 1/2) : 0 < (sigma τ).re := by
  rw [sigma_re]
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> unfold theta <;> nlinarith [Real.pi_pos, h1, h2]

lemma sigma_im_neg (τ : unitInterval) (h1 : 1/2 ≤ (τ:ℝ)) (h2 : (τ:ℝ) ≤ 3/4) : (sigma τ).im < 0 := by
  rw [sigma_im]
  apply Real.sin_neg_of_neg_of_neg_pi_lt
  · unfold theta; nlinarith [Real.pi_pos, h1]
  · unfold theta; nlinarith [Real.pi_pos, h2]

lemma sigma_re_neg (τ : unitInterval) (h1 : 3/4 ≤ (τ:ℝ)) : (sigma τ).re < 0 := by
  rw [sigma_re, ← Real.cos_neg]
  apply Real.cos_neg_of_pi_div_two_lt_of_lt
  · unfold theta; nlinarith [Real.pi_pos, h1]
  · unfold theta; nlinarith [Real.pi_pos, τ.2.2]

lemma sigma_zero_one : sigma 0 = sigma 1 := by
  simp only [sigma, ContinuousMap.coe_mk]
  have h0 : theta 0 = 3 * Real.pi / 4 := by unfold theta; norm_num
  have h1 : theta 1 = 3 * Real.pi / 4 - 2 * Real.pi := by unfold theta; norm_num
  rw [h0, h1]
  have hsplit : ((3 * Real.pi / 4 - 2 * Real.pi : ℝ) : ℂ) * Complex.I
      = ((3 * Real.pi / 4 : ℝ) : ℂ) * Complex.I + (-(2 * (Real.pi:ℂ) * Complex.I)) := by
    push_cast; ring
  rw [hsplit, Complex.exp_add, Complex.exp_neg, Complex.exp_two_pi_mul_I]
  simp

def liftSigma : C(unitInterval, ℂ) :=
  ⟨fun τ => ((theta τ : ℝ) : ℂ) * Complex.I, by unfold theta; fun_prop⟩

lemma liftSigma_exp (τ : unitInterval) : Complex.exp (liftSigma τ) = sigma τ := rfl

@[simp] lemma coe_zero_unitInterval : ((0:unitInterval):ℝ) = 0 := rfl
@[simp] lemma coe_one_unitInterval : ((1:unitInterval):ℝ) = 1 := rfl

/-! ### The boundary parametrisation γ -/

def gA (τ : unitInterval) : ℝ × ℝ := (-1 + 8 * (τ : ℝ), -1)
def gB (τ : unitInterval) : ℝ × ℝ := (1, 8 * (τ : ℝ) - 3)
def gC (τ : unitInterval) : ℝ × ℝ := (5 - 8 * (τ : ℝ), 1)
def gD (τ : unitInterval) : ℝ × ℝ := (-1, 7 - 8 * (τ : ℝ))

lemma continuous_gA : Continuous gA := by unfold gA; fun_prop
lemma continuous_gB : Continuous gB := by unfold gB; fun_prop
lemma continuous_gC : Continuous gC := by unfold gC; fun_prop
lemma continuous_gD : Continuous gD := by unfold gD; fun_prop

def gamFun (τ : unitInterval) : ℝ × ℝ :=
  if (τ : ℝ) ≤ 1 / 4 then gA τ
  else if (τ : ℝ) ≤ 1 / 2 then gB τ
  else if (τ : ℝ) ≤ 3 / 4 then gC τ
  else gD τ

lemma continuous_gamFun : Continuous gamFun := by
  have h34 : Continuous fun τ : unitInterval => (if (τ:ℝ) ≤ 3/4 then gC τ else gD τ) :=
    Continuous.if_le continuous_gC continuous_gD continuous_subtype_val continuous_const
      (fun τ hτ => by
        ext <;> simp only [gC, gD, hτ] <;> norm_num)
  have h12 : Continuous fun τ : unitInterval =>
      (if (τ:ℝ) ≤ 1/2 then gB τ else (if (τ:ℝ) ≤ 3/4 then gC τ else gD τ)) :=
    Continuous.if_le continuous_gB h34 continuous_subtype_val continuous_const
      (fun τ hτ => by
        rw [if_pos (by rw [hτ]; norm_num)]
        ext <;> simp only [gB, gC, hτ] <;> norm_num)
  have h14 : Continuous fun τ : unitInterval =>
      (if (τ:ℝ) ≤ 1/4 then gA τ
        else (if (τ:ℝ) ≤ 1/2 then gB τ else (if (τ:ℝ) ≤ 3/4 then gC τ else gD τ))) :=
    Continuous.if_le continuous_gA h12 continuous_subtype_val continuous_const
      (fun τ hτ => by
        rw [if_pos (by rw [hτ]; norm_num)]
        ext <;> simp only [gA, gB, hτ] <;> norm_num)
  unfold gamFun
  exact h14

def gam : C(unitInterval, ℝ × ℝ) := ⟨gamFun, continuous_gamFun⟩

lemma gamFun_eq_gA (τ : unitInterval) (h : (τ:ℝ) ≤ 1/4) : gamFun τ = gA τ := by
  unfold gamFun; rw [if_pos h]
lemma gamFun_eq_gB (τ : unitInterval) (h1 : 1/4 < (τ:ℝ)) (h2 : (τ:ℝ) ≤ 1/2) :
    gamFun τ = gB τ := by
  unfold gamFun; rw [if_neg (not_le.mpr h1), if_pos h2]
lemma gamFun_eq_gC (τ : unitInterval) (h1 : 1/2 < (τ:ℝ)) (h2 : (τ:ℝ) ≤ 3/4) :
    gamFun τ = gC τ := by
  unfold gamFun
  rw [if_neg (by rw [not_le]; linarith), if_neg (not_le.mpr h1), if_pos h2]
lemma gamFun_eq_gD (τ : unitInterval) (h1 : 3/4 < (τ:ℝ)) : gamFun τ = gD τ := by
  unfold gamFun
  rw [if_neg (by rw [not_le]; linarith), if_neg (by rw [not_le]; linarith), if_neg (not_le.mpr h1)]

lemma gamFun_mem (τ : unitInterval) :
    gamFun τ ∈ Set.Icc (-1:ℝ) 1 ×ˢ Set.Icc (-1:ℝ) 1 := by
  unfold gamFun
  by_cases h1 : (τ:ℝ) ≤ 1/4
  · rw [if_pos h1, Set.mem_prod]
    exact ⟨⟨by simp only [gA]; linarith [τ.2.1], by simp only [gA]; linarith [h1]⟩,
      by simp only [gA]; norm_num⟩
  · rw [if_neg h1]
    by_cases h2 : (τ:ℝ) ≤ 1/2
    · rw [if_pos h2, Set.mem_prod]
      exact ⟨by simp only [gB]; norm_num,
        ⟨by simp only [gB]; linarith [not_le.mp h1], by simp only [gB]; linarith [h2]⟩⟩
    · rw [if_neg h2]
      by_cases h3 : (τ:ℝ) ≤ 3/4
      · rw [if_pos h3, Set.mem_prod]
        exact ⟨⟨by simp only [gC]; linarith [h3], by simp only [gC]; linarith [not_le.mp h2]⟩,
          by simp only [gC]; norm_num⟩
      · rw [if_neg h3, Set.mem_prod]
        exact ⟨by simp only [gD]; norm_num,
          ⟨by simp only [gD]; linarith [τ.2.2], by simp only [gD]; linarith [not_le.mp h3]⟩⟩

lemma gamFun_zero_one : gamFun 0 = gamFun 1 := by
  rw [gamFun_eq_gA 0 (by norm_num), gamFun_eq_gD 1 (by norm_num)]
  ext <;> simp only [gA, gD] <;> norm_num

/-! ### The crux -/

lemma combine_im (a b : ℝ) (z w : ℂ) :
    (((a:ℂ) * z + (b:ℂ) * w).im) = a * z.im + b * w.im := by
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero]
lemma combine_re (a b : ℝ) (z w : ℂ) :
    (((a:ℂ) * z + (b:ℂ) * w).re) = a * z.re + b * w.re := by
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]

lemma hom_ne_zero_im_pos (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (z w : ℂ) (hz : 0 ≤ z.im) (hw : 0 < w.im) (hz0 : z ≠ 0) :
    (a : ℂ) * z + (b : ℂ) * w ≠ 0 := by
  intro h0
  rcases eq_or_lt_of_le hb with hb0 | hbpos
  · have ha1 : a = 1 := by linarith
    have : (a:ℂ) * z + (b:ℂ) * w = z := by rw [show b = 0 from hb0.symm, ha1]; simp
    rw [this] at h0; exact hz0 h0
  · have him : ((a:ℂ)*z + (b:ℂ)*w).im = a * z.im + b * w.im := combine_im a b z w
    rw [h0, Complex.zero_im] at him
    have h1 : 0 ≤ a * z.im := mul_nonneg ha hz
    have h2 : 0 < b * w.im := mul_pos hbpos hw
    linarith

lemma hom_ne_zero_re_pos (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (z w : ℂ) (hz : 0 ≤ z.re) (hw : 0 < w.re) (hz0 : z ≠ 0) :
    (a : ℂ) * z + (b : ℂ) * w ≠ 0 := by
  intro h0
  rcases eq_or_lt_of_le hb with hb0 | hbpos
  · have ha1 : a = 1 := by linarith
    have : (a:ℂ) * z + (b:ℂ) * w = z := by rw [show b = 0 from hb0.symm, ha1]; simp
    rw [this] at h0; exact hz0 h0
  · have hre : ((a:ℂ)*z + (b:ℂ)*w).re = a * z.re + b * w.re := combine_re a b z w
    rw [h0, Complex.zero_re] at hre
    have h1 : 0 ≤ a * z.re := mul_nonneg ha hz
    have h2 : 0 < b * w.re := mul_pos hbpos hw
    linarith

lemma hom_ne_zero_im_neg (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (z w : ℂ) (hz : z.im ≤ 0) (hw : w.im < 0) (hz0 : z ≠ 0) :
    (a : ℂ) * z + (b : ℂ) * w ≠ 0 := by
  intro h0
  have h0' : (a:ℂ) * (-z) + (b:ℂ) * (-w) = 0 := by
    rw [mul_neg, mul_neg, ← neg_add, h0, neg_zero]
  exact hom_ne_zero_im_pos a b ha hb hab (-z) (-w)
    (by simp only [Complex.neg_im]; linarith) (by simp only [Complex.neg_im]; linarith)
    (neg_ne_zero.mpr hz0) h0'

lemma hom_ne_zero_re_neg (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (z w : ℂ) (hz : z.re ≤ 0) (hw : w.re < 0) (hz0 : z ≠ 0) :
    (a : ℂ) * z + (b : ℂ) * w ≠ 0 := by
  intro h0
  have h0' : (a:ℂ) * (-z) + (b:ℂ) * (-w) = 0 := by
    rw [mul_neg, mul_neg, ← neg_add, h0, neg_zero]
  exact hom_ne_zero_re_pos a b ha hb hab (-z) (-w)
    (by simp only [Complex.neg_re]; linarith) (by simp only [Complex.neg_re]; linarith)
    (neg_ne_zero.mpr hz0) h0'

theorem square_boundary_index_aux (f : ℝ × ℝ → ℂ) (hf : Continuous f)
    (h1 : ∀ s ∈ Set.Icc (-1:ℝ) 1, 0 ≤ (f (s, -1)).im)
    (h2 : ∀ t ∈ Set.Icc (-1:ℝ) 1, 0 ≤ (f (1, t)).re)
    (h3 : ∀ s ∈ Set.Icc (-1:ℝ) 1, (f (s, 1)).im ≤ 0)
    (h4 : ∀ t ∈ Set.Icc (-1:ℝ) 1, (f (-1, t)).re ≤ 0)
    (h5 : ∀ p ∈ Set.Icc (-1:ℝ) 1 ×ˢ Set.Icc (-1:ℝ) 1, f p ≠ 0) : False := by
  classical
  let G : C(unitInterval, ℂ) := ⟨fun τ => f (gamFun τ), hf.comp continuous_gamFun⟩
  have hG_ne : ∀ τ, G τ ≠ 0 := by
    intro τ
    show f (gamFun τ) ≠ 0
    exact h5 (gamFun τ) (gamFun_mem τ)
  have hG_loop : G 0 = G 1 := by
    show f (gamFun 0) = f (gamFun 1)
    rw [gamFun_zero_one]
  have hG_bot : ∀ τ : unitInterval, (τ:ℝ) ≤ 1/4 → 0 ≤ (G τ).im := by
    intro τ hτ
    have hg : gamFun τ = gA τ := gamFun_eq_gA τ hτ
    have hs : (-1 + 8 * (τ:ℝ)) ∈ Set.Icc (-1:ℝ) 1 :=
      ⟨by linarith [τ.2.1], by linarith [hτ]⟩
    have hz : G τ = f (-1 + 8 * (τ:ℝ), -1) := by
      show f (gamFun τ) = f (-1 + 8 * (τ:ℝ), -1)
      rw [hg]
      rfl
    rw [hz]
    exact h1 _ hs
  have hG_right : ∀ τ : unitInterval, 1/4 ≤ (τ:ℝ) → (τ:ℝ) ≤ 1/2 → 0 ≤ (G τ).re := by
    intro τ h1' h2'
    rcases eq_or_lt_of_le h1' with heq | hlt
    · have hg : gamFun τ = gA τ := gamFun_eq_gA τ (le_of_eq heq.symm)
      have hpt : gA τ = (1, -1) := by
        have ht : (τ:ℝ) = 1/4 := heq.symm
        ext
        · simp only [gA]; rw [ht]; norm_num
        · simp only [gA]
      have hz : G τ = f (1, -1) := by
        show f (gamFun τ) = f (1, -1); rw [hg, hpt]
      rw [hz]
      exact h2 (-1) ⟨by norm_num, by norm_num⟩
    · have hg : gamFun τ = gB τ := gamFun_eq_gB τ hlt h2'
      have ht : 8 * (τ:ℝ) - 3 ∈ Set.Icc (-1:ℝ) 1 := ⟨by linarith, by linarith⟩
      have hz : G τ = f (1, 8 * (τ:ℝ) - 3) := by
        show f (gamFun τ) = f (1, 8 * (τ:ℝ) - 3); rw [hg]; rfl
      rw [hz]
      exact h2 _ ht
  have hG_top : ∀ τ : unitInterval, 1/2 ≤ (τ:ℝ) → (τ:ℝ) ≤ 3/4 → (G τ).im ≤ 0 := by
    intro τ h1' h2'
    rcases eq_or_lt_of_le h1' with heq | hlt
    · have hg : gamFun τ = gB τ := gamFun_eq_gB τ (by rw [← heq]; norm_num) (le_of_eq heq.symm)
      have hpt : gB τ = (1, 1) := by
        have ht : (τ:ℝ) = 1/2 := heq.symm
        ext
        · simp only [gB]
        · simp only [gB]; rw [ht]; norm_num
      have hz : G τ = f (1, 1) := by
        show f (gamFun τ) = f (1, 1); rw [hg, hpt]
      rw [hz]
      exact h3 1 ⟨by norm_num, by norm_num⟩
    · have hg : gamFun τ = gC τ := gamFun_eq_gC τ hlt h2'
      have ht : 5 - 8 * (τ:ℝ) ∈ Set.Icc (-1:ℝ) 1 := ⟨by linarith, by linarith⟩
      have hz : G τ = f (5 - 8 * (τ:ℝ), 1) := by
        show f (gamFun τ) = f (5 - 8 * (τ:ℝ), 1); rw [hg]; rfl
      rw [hz]
      exact h3 _ ht
  have hG_left : ∀ τ : unitInterval, 3/4 ≤ (τ:ℝ) → (G τ).re ≤ 0 := by
    intro τ h1'
    rcases eq_or_lt_of_le h1' with heq | hlt
    · have hg : gamFun τ = gC τ := gamFun_eq_gC τ (by rw [← heq]; norm_num) (le_of_eq heq.symm)
      have hpt : gC τ = (-1, 1) := by
        have ht : (τ:ℝ) = 3/4 := heq.symm
        ext
        · simp only [gC]; rw [ht]; norm_num
        · simp only [gC]
      have hz : G τ = f (-1, 1) := by
        show f (gamFun τ) = f (-1, 1); rw [hg, hpt]
      rw [hz]
      exact h4 1 ⟨by norm_num, by norm_num⟩
    · have hg : gamFun τ = gD τ := gamFun_eq_gD τ hlt
      have ht : 7 - 8 * (τ:ℝ) ∈ Set.Icc (-1:ℝ) 1 :=
        ⟨by linarith [τ.2.2], by linarith [hlt]⟩
      have hz : G τ = f (-1, 7 - 8 * (τ:ℝ)) := by
        show f (gamFun τ) = f (-1, 7 - 8 * (τ:ℝ)); rw [hg]; rfl
      rw [hz]
      exact h4 _ ht
  -- Hom1
  let Hom1 : C(unitInterval × unitInterval, ℂ) :=
    ⟨fun p => ((1 - (p.2:ℝ):ℝ):ℂ) * G p.1 + ((p.2:ℝ):ℂ) * sigma p.1, by
      have hGc : Continuous fun p : unitInterval × unitInterval => G p.1 :=
        G.continuous.comp continuous_fst
      have hSc : Continuous fun p : unitInterval × unitInterval => sigma p.1 :=
        sigma.continuous.comp continuous_fst
      exact ((by fun_prop : Continuous fun p : unitInterval × unitInterval => ((1 - (p.2:ℝ):ℝ):ℂ)).mul hGc).add
        ((by fun_prop : Continuous fun p : unitInterval × unitInterval => ((p.2:ℝ):ℂ)).mul hSc)⟩
  have hHom1_ne : ∀ p, Hom1 p ≠ 0 := by
    intro p
    obtain ⟨t, lam⟩ := p
    have hlam0 : (0:ℝ) ≤ (lam:ℝ) := lam.2.1
    have hlam1 : (lam:ℝ) ≤ 1 := lam.2.2
    have hab : (1 - (lam:ℝ)) + (lam:ℝ) = 1 := by ring
    have hgt : G t ≠ 0 := hG_ne t
    show ((1 - (lam:ℝ):ℝ):ℂ) * G t + ((lam:ℝ):ℂ) * sigma t ≠ 0
    rcases le_or_gt (t:ℝ) (1/4) with hb | hb
    · exact hom_ne_zero_im_pos (1 - (lam:ℝ)) (lam:ℝ) (by linarith) hlam0 hab (G t) (sigma t)
        (hG_bot t hb) (sigma_im_pos t hb) hgt
    · rcases le_or_gt (t:ℝ) (1/2) with hr | hr
      · exact hom_ne_zero_re_pos _ _ (by linarith) hlam0 hab (G t) (sigma t)
          (hG_right t (le_of_lt hb) hr) (sigma_re_pos t (le_of_lt hb) hr) hgt
      · rcases le_or_gt (t:ℝ) (3/4) with ht | ht
        · exact hom_ne_zero_im_neg _ _ (by linarith) hlam0 hab (G t) (sigma t)
            (hG_top t (le_of_lt hr) ht) (sigma_im_neg t (le_of_lt hr) ht) hgt
        · exact hom_ne_zero_re_neg _ _ (by linarith) hlam0 hab (G t) (sigma t)
            (hG_left t (le_of_lt ht)) (sigma_re_neg t (le_of_lt ht)) hgt
  have hHom1_0 : ∀ t : unitInterval, Hom1 (t, 0) = G t := by
    intro t
    show ((1 - ((0:unitInterval):ℝ):ℝ):ℂ) * G t + (((0:unitInterval):ℝ):ℂ) * sigma t = G t
    simp
  have hHom1_1 : ∀ t : unitInterval, Hom1 (t, 1) = sigma t := by
    intro t
    show ((1 - ((1:unitInterval):ℝ):ℝ):ℂ) * G t + (((1:unitInterval):ℝ):ℂ) * sigma t = sigma t
    simp
  have hHom1_loop : ∀ s : unitInterval, Hom1 (0, s) = Hom1 (1, s) := by
    intro s
    show ((1 - (s:ℝ):ℝ):ℂ) * G 0 + ((s:ℝ):ℂ) * sigma 0
      = ((1 - (s:ℝ):ℝ):ℂ) * G 1 + ((s:ℝ):ℂ) * sigma 1
    rw [hG_loop, sigma_zero_one]
  have hindex1 : loopIndex G = loopIndex sigma :=
    loopIndex_eq_of_homotopy (c₀ := G) (c₁ := sigma) hG_ne sigma_ne_zero Hom1 hHom1_ne
      hHom1_0 hHom1_1 hHom1_loop
  have hsigma_index : loopIndex sigma ≠ 0 := by
    intro h0
    have hspec := loopIndex_spec sigma sigma_ne_zero sigma_zero_one liftSigma liftSigma_exp
    have hlhs : liftSigma 1 - liftSigma 0 = -(2 * (Real.pi:ℂ) * Complex.I) := by
      show ((theta 1 : ℝ):ℂ) * Complex.I - ((theta 0 : ℝ):ℂ) * Complex.I
        = -(2 * (Real.pi:ℂ) * Complex.I)
      have e1 : theta 1 = 3 * Real.pi / 4 - 2 * Real.pi := by unfold theta; norm_num
      have e0 : theta 0 = 3 * Real.pi / 4 := by unfold theta; norm_num
      rw [e1, e0]; push_cast; ring
    rw [hlhs] at hspec
    rw [h0] at hspec
    simp only [Int.cast_zero, zero_mul] at hspec
    exact Work.Smooth.SphereJordan.two_pi_I_ne_zero (neg_eq_zero.mp hspec)
  have hG_index_ne : loopIndex G ≠ 0 := by rw [hindex1]; exact hsigma_index
  -- Hom2
  let Hom2 : C(unitInterval × unitInterval, ℂ) :=
    ⟨fun p => f (((1 - (p.2:ℝ):ℝ) • gamFun p.1)), by
      have hgam : Continuous fun p : unitInterval × unitInterval =>
          (((1 - (p.2:ℝ):ℝ) • gamFun p.1) : ℝ × ℝ) :=
        ((by fun_prop : Continuous fun p : unitInterval × unitInterval => (1 - (p.2:ℝ):ℝ)).smul
          (continuous_gamFun.comp continuous_fst))
      exact hf.comp hgam⟩
  have hHom2_ne : ∀ p, Hom2 p ≠ 0 := by
    intro p
    obtain ⟨t, lam⟩ := p
    show f (((1 - (lam:ℝ):ℝ) • gamFun t)) ≠ 0
    apply h5
    have hmem := gamFun_mem t
    rw [Set.mem_prod] at hmem ⊢
    obtain ⟨hx, hy⟩ := hmem
    obtain ⟨hxl, hxr⟩ := hx
    obtain ⟨hyl, hyr⟩ := hy
    have hl0 : 0 ≤ 1 - (lam:ℝ) := by linarith [lam.2.2]
    have hl1 : 1 - (lam:ℝ) ≤ 1 := by linarith [lam.2.1]
    constructor
    · rw [Prod.smul_fst, smul_eq_mul]
      exact ⟨by nlinarith, by nlinarith⟩
    · rw [Prod.smul_snd, smul_eq_mul]
      exact ⟨by nlinarith, by nlinarith⟩
  have hHom2_0 : ∀ t : unitInterval, Hom2 (t, 0) = G t := by
    intro t
    show f (((1 - ((0:unitInterval):ℝ):ℝ) • gamFun t)) = G t
    simp only [coe_zero_unitInterval, sub_zero, one_smul]
    rfl
  have hHom2_1 : ∀ t : unitInterval, Hom2 (t, 1) = ContinuousMap.const unitInterval (f (0,0)) t := by
    intro t
    show f (((1 - ((1:unitInterval):ℝ):ℝ) • gamFun t)) = f (0,0)
    simp only [coe_one_unitInterval, sub_self, zero_smul]
    rfl
  have hHom2_loop : ∀ s : unitInterval, Hom2 (0, s) = Hom2 (1, s) := by
    intro s
    show f (((1 - (s:ℝ):ℝ) • gamFun 0)) = f (((1 - (s:ℝ):ℝ) • gamFun 1))
    rw [gamFun_zero_one]
  have hzero_mem : ((0:ℝ), (0:ℝ)) ∈ Set.Icc (-1:ℝ) 1 ×ˢ Set.Icc (-1:ℝ) 1 :=
    ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩
  have hindex2 : loopIndex G = loopIndex (ContinuousMap.const unitInterval (f (0,0))) :=
    loopIndex_eq_of_homotopy (c₀ := G) (c₁ := ContinuousMap.const unitInterval (f (0,0)))
      hG_ne (fun _ => h5 (0,0) hzero_mem) Hom2 hHom2_ne hHom2_0 hHom2_1 hHom2_loop
  have hG_index_zero : loopIndex G = 0 := by
    rw [hindex2, loopIndex_const _ (h5 (0,0) hzero_mem)]
  exact hG_index_ne hG_index_zero

end
end PlaneCrossing

open PlaneCrossing

theorem plane_crossing_lemma {h v : ℝ → ℂ} (hh : Continuous h) (hv : Continuous v)
    (hhbox : ∀ t ∈ Set.Icc (-1:ℝ) 1, |(h t).re| ≤ 1 ∧ |(h t).im| ≤ 1)
    (hvbox : ∀ t ∈ Set.Icc (-1:ℝ) 1, |(v t).re| ≤ 1 ∧ |(v t).im| ≤ 1)
    (hh_left : (h (-1)).re = -1) (hh_right : (h 1).re = 1)
    (hv_bot : (v (-1)).im = -1) (hv_top : (v 1).im = 1) :
    ∃ s ∈ Set.Icc (-1:ℝ) 1, ∃ t ∈ Set.Icc (-1:ℝ) 1, h s = v t := by
  by_contra hcon
  push Not at hcon
  let f : ℝ × ℝ → ℂ := fun p => h p.1 - v p.2
  have hf : Continuous f := by unfold f; fun_prop
  refine square_boundary_index_aux f hf ?_ ?_ ?_ ?_ ?_
  · intro s hs
    have hb := (hhbox s hs).2
    rw [abs_le] at hb
    change 0 ≤ (h s - v (-1)).im
    rw [Complex.sub_im, hv_bot]
    linarith [hb.1]
  · intro t ht
    have hb := (hvbox t ht).1
    rw [abs_le] at hb
    change 0 ≤ (h 1 - v t).re
    rw [Complex.sub_re, hh_right]
    linarith [hb.2]
  · intro s hs
    have hb := (hhbox s hs).2
    rw [abs_le] at hb
    change (h s - v 1).im ≤ 0
    rw [Complex.sub_im, hv_top]
    linarith [hb.2]
  · intro t ht
    have hb := (hvbox t ht).1
    rw [abs_le] at hb
    change (h (-1) - v t).re ≤ 0
    rw [Complex.sub_re, hh_left]
    linarith [hb.1]
  · intro p hp
    rw [Set.mem_prod] at hp
    change h p.1 - v p.2 ≠ 0
    intro hzero
    exact hcon p.1 hp.1 p.2 hp.2 (sub_eq_zero.mp hzero)

end Work.Topology.PlaneCurve
