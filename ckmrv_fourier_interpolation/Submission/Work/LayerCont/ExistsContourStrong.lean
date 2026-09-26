/-
# The geometry of the left-detour contour at `1 + i s₀`

This file proves `Work.Asymptotics.exists_contour_left`, the geometric input for the *left* detours
of the CKMRV contour (see `Submission/Work/Asymptotics/contourLeftDefs.lean`).  It strengthens
`Work.Asymptotics.exists_contour_avoid` in two ways: the detour rectangles are mirrored to the
half-plane `Re ≤ 0` (with independent widths `ξᵢ` and heights `Aᵢ`), and a third clause
(`classify_left`) identifies the `SL(2,ℤ)`-orbit points that such a rectangle can meet.

The three clauses of the target:

* (1) *axis cleanliness*: the retained imaginary axis carries no pole
  (`jInvariantFun_ne_of_dist_lt_left`, modelled on clause (1) of `exists_contour_avoid`);
* (2) *edge avoidance*: the three open sides of the two rectangles avoid the ball in the second
  variable, i.e. no `SL(2,ℤ)`-translate of an edge point comes within `ε` of `1 + i s₀`
  (`edge_avoid_left`; clause (2) of `exists_contour_avoid` with the rectangles mirrored);
* (3) *classification*: the only orbit points of `τ` in the closed left rectangles are
  `τ - 1` and `ST⁻¹τ = -1/(τ-1)` (`classify_left`, resting on the quantitative discreteness
  `orbitGap_imagAxis_dist` of the orbit of `i s₀`: `T⁻¹τ` is within `ε` of `i s₀` and `z ∈ R₁` is
  within `b₁ ≤ δ₀ - ε` of `i s₀`, so `γT` fixes `i s₀`, whence `γT ∈ {±1, ±S}`).
-/
import Mathlib
import Submission.Work.Asymptotics.contourLeftDefs
import Submission.Work.Asymptotics.exists_contour_avoid

set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section

open UpperHalfPlane

namespace Work.LayerCont.ECS

open Work.Asymptotics

/-! ## Toolkit -/

/-- **The orbit gap at `i s₀`, in explicit form.**  There are `δ₀ > 0` and `F₀ > 0` with
`δ₀ = arcosh (1 + F₀/(2 s₀))` such that every point of the `SL(2,ℤ)`-orbit of `i s₀` other than
`i s₀` itself is at hyperbolic distance at least `δ₀` from `i s₀`.  This is the quantitative form
of `orbitGap_imagAxis`. -/
theorem orbitGap_imagAxis_dist (s₀ : ℝ) (hs₀ : 0 < s₀) :
    ∃ δ₀ F₀ : ℝ, 0 < δ₀ ∧ 0 < F₀ ∧ δ₀ = Real.arcosh (1 + F₀ / (2 * s₀)) ∧
      ∀ ν : Matrix.SpecialLinearGroup (Fin 2) ℤ,
        ν • Work.Kernels.imagAxis s₀ hs₀ ≠ Work.Kernels.imagAxis s₀ hs₀ →
        δ₀ ≤ dist (ν • Work.Kernels.imagAxis s₀ hs₀) (Work.Kernels.imagAxis s₀ hs₀) := by
  obtain ⟨F₀, hF₀pos, hgapQ⟩ := orbitGap_imagAxis s₀ hs₀
  have hgt : (1 : ℝ) < 1 + F₀ / (2 * s₀) := by
    have h : (0 : ℝ) < F₀ / (2 * s₀) := by positivity
    linarith
  refine ⟨Real.arcosh (1 + F₀ / (2 * s₀)), F₀, Real.arcosh_pos hgt, hF₀pos, rfl, ?_⟩
  intro ν hν
  have hQ := hgapQ ν hν
  have hre : (Work.Kernels.imagAxis s₀ hs₀).re = 0 := by simp [Work.Kernels.imagAxis]
  have him : (Work.Kernels.imagAxis s₀ hs₀).im = s₀ := by simp [Work.Kernels.imagAxis]
  have hcosh := UpperHalfPlane.cosh_dist' (ν • Work.Kernels.imagAxis s₀ hs₀)
    (Work.Kernels.imagAxis s₀ hs₀)
  rw [hre, him] at hcosh
  have h2 : Real.cosh (dist (ν • Work.Kernels.imagAxis s₀ hs₀) (Work.Kernels.imagAxis s₀ hs₀))
      = 1 + (((((ν • Work.Kernels.imagAxis s₀ hs₀).re) ^ 2
          + ((ν • Work.Kernels.imagAxis s₀ hs₀).im - s₀) ^ 2)
        / (ν • Work.Kernels.imagAxis s₀ hs₀).im) / (2 * s₀)) := by
    rw [hcosh]; field_simp; ring
  have h1 : Real.cosh (Real.arcosh (1 + F₀ / (2 * s₀)))
      ≤ Real.cosh (dist (ν • Work.Kernels.imagAxis s₀ hs₀) (Work.Kernels.imagAxis s₀ hs₀)) := by
    rw [Real.cosh_arcosh (le_of_lt hgt), h2]
    have := div_le_div_of_nonneg_right hQ (by positivity : (0 : ℝ) ≤ 2 * s₀)
    linarith
  have h3 := Real.cosh_le_cosh.mp h1
  rwa [abs_of_nonneg (Real.arcosh_nonneg (le_of_lt hgt)), abs_of_nonneg dist_nonneg] at h3

/-- `T⁻¹` acts on `ℍ` as the translation by `-1`. -/
lemma Tinv_smul_eq_tauSubOne (τ : UpperHalfPlane) :
    (ModularGroup.T⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • τ = tauSubOne τ := by
  apply UpperHalfPlane.ext
  rw [show (ModularGroup.T⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T ^ (-1 : ℤ)
      from by rw [zpow_neg_one],
    UpperHalfPlane.modular_T_zpow_smul, UpperHalfPlane.coe_vadd, tauSubOne_coe]
  push_cast
  ring

/-- `S² = -1` in `SL(2,ℤ)`. -/
lemma S_mul_S : (ModularGroup.S * ModularGroup.S : Matrix.SpecialLinearGroup (Fin 2) ℤ) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ModularGroup.coe_S, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]

/-- `S` acts on `ℍ` as an involution (because `S² = -1` and `-1` acts trivially). -/
lemma S_smul_self (z : UpperHalfPlane) : ModularGroup.S • (ModularGroup.S • z) = z := by
  rw [← mul_smul, S_mul_S, neg_one_smul_SL2Z]

/-- `S` maps `i/s₀` back to `i s₀`. -/
lemma S_smul_imagAxis_inv (s₀ : ℝ) (hs₀ : 0 < s₀) :
    ModularGroup.S • Work.Kernels.imagAxis s₀⁻¹ (inv_pos.mpr hs₀)
      = Work.Kernels.imagAxis s₀ hs₀ := by
  calc ModularGroup.S • Work.Kernels.imagAxis s₀⁻¹ (inv_pos.mpr hs₀)
      = ModularGroup.S • (ModularGroup.S • Work.Kernels.imagAxis s₀ hs₀) := by
        rw [S_smul_imagAxis s₀ hs₀]
    _ = (ModularGroup.S * ModularGroup.S) • Work.Kernels.imagAxis s₀ hs₀ := (mul_smul _ _ _).symm
    _ = (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) • Work.Kernels.imagAxis s₀ hs₀ := by
        rw [S_mul_S]
    _ = Work.Kernels.imagAxis s₀ hs₀ := neg_one_smul_SL2Z _

/-- `S(τ - 1) = -1/(τ-1) = ST⁻¹τ`. -/
lemma S_smul_tauSubOne (τ : UpperHalfPlane) : ModularGroup.S • tauSubOne τ = tauCoinc τ := by
  rw [← Tinv_smul_eq_tauSubOne τ, ← mul_smul, tauCoinc]

/-- `S(ST⁻¹τ) = τ - 1`. -/
lemma S_smul_tauCoinc (τ : UpperHalfPlane) : ModularGroup.S • tauCoinc τ = tauSubOne τ := by
  show ModularGroup.S • ((ModularGroup.S * ModularGroup.T⁻¹) • τ) = tauSubOne τ
  rw [← mul_smul, ← mul_assoc, S_mul_S]
  simp only [neg_mul, one_mul]
  rw [neg_smul_SL2Z, ← Tinv_smul_eq_tauSubOne]

/-- **A point of the left rectangle `[-ξ,0] × [c-A,c+A]` is hyperbolically close to `i c`.** -/
lemma dist_le_of_mem_leftRect {c A ξ : ℝ} (hA : 0 ≤ A) (hξ : 0 ≤ ξ) (hc : 0 < c) (hcA : A < c)
    {z : UpperHalfPlane} (hz : leftRect c A ξ z) :
    dist z (Work.Kernels.imagAxis c hc) ≤
      Real.arcosh (1 + (ξ ^ 2 + A ^ 2) / (2 * c * (c - A))) := by
  obtain ⟨hre₁, hre₂, him₁, him₂⟩ := hz
  have him : 0 < z.im := by linarith
  have hcosh := UpperHalfPlane.cosh_dist' z (Work.Kernels.imagAxis c hc)
  have hcre : (Work.Kernels.imagAxis c hc).re = 0 := by simp [Work.Kernels.imagAxis]
  have hcim : (Work.Kernels.imagAxis c hc).im = c := by simp [Work.Kernels.imagAxis]
  rw [hcre, hcim] at hcosh
  have hsplit : Real.cosh (dist z (Work.Kernels.imagAxis c hc))
      = 1 + (z.re ^ 2 + (z.im - c) ^ 2) / (2 * z.im * c) := by
    rw [hcosh]; field_simp; ring
  have hre_sq : z.re ^ 2 ≤ ξ ^ 2 := by nlinarith
  have him_sq : (z.im - c) ^ 2 ≤ A ^ 2 := by nlinarith
  have hden1 : (0 : ℝ) < 2 * z.im * c := by positivity
  have hden2 : (0 : ℝ) < 2 * c * (c - A) := by nlinarith
  have hub : (z.re ^ 2 + (z.im - c) ^ 2) / (2 * z.im * c)
      ≤ (ξ ^ 2 + A ^ 2) / (2 * c * (c - A)) := by
    rw [div_le_div_iff₀ hden1 hden2]
    have hnum : z.re ^ 2 + (z.im - c) ^ 2 ≤ ξ ^ 2 + A ^ 2 := by linarith
    have hH : (0 : ℝ) ≤ ξ ^ 2 + A ^ 2 := by positivity
    have h1 : (z.re ^ 2 + (z.im - c) ^ 2) * (2 * c * (c - A))
        ≤ (ξ ^ 2 + A ^ 2) * (2 * c * (c - A)) :=
      mul_le_mul_of_nonneg_right hnum (by positivity)
    have h2 : (ξ ^ 2 + A ^ 2) * (2 * c * (c - A)) ≤ (ξ ^ 2 + A ^ 2) * (2 * z.im * c) := by
      apply mul_le_mul_of_nonneg_left _ hH
      nlinarith
    linarith
  have hfinal : Real.cosh (dist z (Work.Kernels.imagAxis c hc))
      ≤ 1 + (ξ ^ 2 + A ^ 2) / (2 * c * (c - A)) := by rw [hsplit]; linarith
  have hpos1 : 0 < Real.cosh (dist z (Work.Kernels.imagAxis c hc)) := Real.cosh_pos _
  have hpos2 : 0 < 1 + (ξ ^ 2 + A ^ 2) / (2 * c * (c - A)) := by
    have : (0 : ℝ) ≤ (ξ ^ 2 + A ^ 2) / (2 * c * (c - A)) :=
      div_nonneg (by positivity) (by positivity)
    linarith
  calc dist z (Work.Kernels.imagAxis c hc)
      = Real.arcosh (Real.cosh (dist z (Work.Kernels.imagAxis c hc))) :=
        (Real.arcosh_cosh dist_nonneg).symm
    _ ≤ Real.arcosh (1 + (ξ ^ 2 + A ^ 2) / (2 * c * (c - A))) :=
        (Real.arcosh_le_arcosh hpos1 hpos2).mpr hfinal

/-- **The orbit-gap step.**  If `z = γ • τ` is within `b` of `i s₀` while `τ` is within `ε` of the
centre and `ε + b ≤ δ₀` (the orbit gap at `i s₀`), then `γT` fixes `i s₀`.

Indeed `γT • i s₀` is within `ε` of `γT • (T⁻¹τ) = z` (the action is isometric, `T⁻¹τ = τ - 1` is
within `ε` of `i s₀`), hence within `ε + b ≤ δ₀` of `i s₀`; the orbit gap forces it to be
`i s₀`. -/
lemma mul_T_smul_imagAxis_eq_of_dist_le {s₀ : ℝ} (hs₀ : 0 < s₀) {δ₀ ε b : ℝ}
    (hgap : ∀ ν : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      ν • Work.Kernels.imagAxis s₀ hs₀ ≠ Work.Kernels.imagAxis s₀ hs₀ →
      δ₀ ≤ dist (ν • Work.Kernels.imagAxis s₀ hs₀) (Work.Kernels.imagAxis s₀ hs₀))
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ} {τ z : UpperHalfPlane}
    (hτ : dist τ (onePlusI s₀ hs₀) < ε) (hz : z = γ • τ)
    (hzb : dist z (Work.Kernels.imagAxis s₀ hs₀) ≤ b) (hεb : ε + b ≤ δ₀) :
    (γ * ModularGroup.T) • Work.Kernels.imagAxis s₀ hs₀ = Work.Kernels.imagAxis s₀ hs₀ := by
  by_contra hne
  have hg := hgap (γ * ModularGroup.T) hne
  have h1 : dist ((γ * ModularGroup.T) • Work.Kernels.imagAxis s₀ hs₀) z < ε := by
    rw [hz, mul_smul, dist_smul_SL2Z, T_smul_imagAxis, dist_comm]
    exact hτ
  have h2 : dist ((γ * ModularGroup.T) • Work.Kernels.imagAxis s₀ hs₀)
      (Work.Kernels.imagAxis s₀ hs₀) < δ₀ := by
    have htri := dist_triangle ((γ * ModularGroup.T) • Work.Kernels.imagAxis s₀ hs₀) z
      (Work.Kernels.imagAxis s₀ hs₀)
    linarith
  linarith

/-- **From `γT ∈ Stab(i s₀)` to the two possible positions.**  If `γT` fixes `i s₀` then
`γ ∈ {±T⁻¹, ±ST⁻¹}`, so `z = γ • τ` is `τ - 1 = T⁻¹τ` or `ST⁻¹τ = -1/(τ-1)`. -/
lemma eq_tauSubOne_or_tauCoinc_of_mul_T_fixes {s₀ : ℝ} (hs₀ : 0 < s₀)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ} {τ z : UpperHalfPlane} (hz : z = γ • τ)
    (hfix : (γ * ModularGroup.T) • Work.Kernels.imagAxis s₀ hs₀
      = Work.Kernels.imagAxis s₀ hs₀) :
    z = tauSubOne τ ∨ z = tauCoinc τ := by
  have hmem := eq_one_or_neg_one_or_S_of_smul_imagAxis hs₀ hs₀ hfix
  rcases hmem with h | h | h | h
  · left
    have hγ : γ = ModularGroup.T⁻¹ := by
      calc γ = (γ * ModularGroup.T) * ModularGroup.T⁻¹ := by group
        _ = 1 * ModularGroup.T⁻¹ := by rw [h]
        _ = ModularGroup.T⁻¹ := one_mul _
    rw [hz, hγ, Tinv_smul_eq_tauSubOne]
  · left
    have hγ : γ = -ModularGroup.T⁻¹ := by
      calc γ = (γ * ModularGroup.T) * ModularGroup.T⁻¹ := by group
        _ = (-1) * ModularGroup.T⁻¹ := by rw [h]
        _ = -ModularGroup.T⁻¹ := by rw [neg_mul, one_mul]
    rw [hz, hγ, neg_smul_SL2Z, Tinv_smul_eq_tauSubOne]
  · right
    have hγ : γ = ModularGroup.S * ModularGroup.T⁻¹ := by
      calc γ = (γ * ModularGroup.T) * ModularGroup.T⁻¹ := by group
        _ = ModularGroup.S * ModularGroup.T⁻¹ := by rw [h]
    rw [hz, hγ, tauCoinc]
  · right
    have hγ : γ = -(ModularGroup.S * ModularGroup.T⁻¹) := by
      calc γ = (γ * ModularGroup.T) * ModularGroup.T⁻¹ := by group
        _ = (-ModularGroup.S) * ModularGroup.T⁻¹ := by rw [h]
        _ = -(ModularGroup.S * ModularGroup.T⁻¹) := by rw [neg_mul]
    rw [hz, hγ, neg_smul_SL2Z, tauCoinc]

/-- **Clause (1): the retained imaginary axis carries no pole.**  For `t > 0` outside the two
intervals `(s₀-a, s₀+a)`, `(s₀⁻¹-a, s₀⁻¹+a)` and `τ` in the ball, `j τ ≠ j(i t)`. -/
lemma jInvariantFun_ne_of_dist_lt_left (s₀ : ℝ) (hs₀ : 0 < s₀) {ε a rw₀ : ℝ} (hε : 0 < ε)
    (hε4 : ε ≤ 1 / 4) (ha : 0 < a) (hεa₁ : ε ≤ a / (4 * s₀)) (hεa₂ : ε ≤ a * s₀ / 8)
    (hεw : ε ≤ rw₀)
    (hweb : ∀ (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (t : ℝ) (ht : 0 < t),
      dist (σ • Work.Kernels.imagAxis t ht) (onePlusI s₀ hs₀) < rw₀ →
      (σ • Work.Kernels.imagAxis t ht).re = 1 ∧
        ((σ • Work.Kernels.imagAxis t ht).im = t ∨ (σ • Work.Kernels.imagAxis t ht).im = t⁻¹)) :
    ∀ (t : ℝ) (ht : 0 < t), t ∉ Set.Ioo (s₀ - a) (s₀ + a) →
      t ∉ Set.Ioo (s₀⁻¹ - a) (s₀⁻¹ + a) →
      ∀ τ : UpperHalfPlane, dist τ (onePlusI s₀ hs₀) < ε →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
  intro t ht ht1 ht2 τ hτ hjeq
  obtain ⟨σ, hσ⟩ := jInvariantFun_eq_smul_of_eq hjeq
  have hdist : dist (σ • Work.Kernels.imagAxis t ht) (onePlusI s₀ hs₀) < ε := by
    rw [hσ]; exact hτ
  have hltw : dist (σ • Work.Kernels.imagAxis t ht) (onePlusI s₀ hs₀) < rw₀ :=
    lt_of_lt_of_le hdist hεw
  have hr := hweb σ t ht hltw
  have hb := abs_im_sub_le_of_dist hs₀ hε.le (by linarith [hε4]) hr.1 hdist
  rcases hr.2 with him | him
  · have h1 : |t - s₀| ≤ 2 * s₀ * ε := by rw [← him]; exact hb
    have h3 : s₀ * ε ≤ a / 4 := by
      have h := mul_le_mul_of_nonneg_left hεa₁ hs₀.le
      rwa [show s₀ * (a / (4 * s₀)) = a / 4 by field_simp] at h
    have h2 : |t - s₀| < a := by linarith
    exact ht1 ⟨by linarith [(abs_lt.mp h2).1], by linarith [(abs_lt.mp h2).2]⟩
  · have hty : t = ((σ • Work.Kernels.imagAxis t ht).im)⁻¹ := by rw [him, inv_inv]
    set y : ℝ := (σ • Work.Kernels.imagAxis t ht).im with hydef
    have hypos : 0 < y := by rw [hydef]; exact (σ • Work.Kernels.imagAxis t ht).im_pos
    have hyge : s₀ / 2 ≤ y := by
      have h2 := abs_le.mp hb
      have h3 : 2 * s₀ * ε ≤ s₀ / 2 := by nlinarith [hε4, hs₀]
      linarith [h2.1, h3]
    have hbnd : |t - s₀⁻¹| * s₀ ≤ 4 * ε := by
      have h1 : |s₀ - y| ≤ 2 * s₀ * ε := by rw [abs_sub_comm]; exact hb
      have hsub : t - s₀⁻¹ = (s₀ - y) / (y * s₀) := by rw [hty]; field_simp
      have h2 : |t - s₀⁻¹| * s₀ = |s₀ - y| / y := by
        rw [hsub, abs_div, abs_of_pos (by positivity : (0 : ℝ) < y * s₀)]
        field_simp
      rw [h2, div_le_iff₀ hypos]
      nlinarith [h1, hyge, hs₀, hε.le]
    have hfin : |t - s₀⁻¹| < a := by
      have h3 : 4 * ε ≤ a * s₀ / 2 := by
        have h := mul_le_mul_of_nonneg_left hεa₂ (by norm_num : (0 : ℝ) ≤ 4)
        linarith
      have h4 : |t - s₀⁻¹| * s₀ ≤ a * s₀ / 2 := le_trans hbnd h3
      have h5 : |t - s₀⁻¹| ≤ a / 2 := by
        have h6 : |t - s₀⁻¹| = (|t - s₀⁻¹| * s₀) / s₀ := by field_simp
        rw [h6]
        calc (|t - s₀⁻¹| * s₀) / s₀ ≤ (a * s₀ / 2) / s₀ :=
              div_le_div_of_nonneg_right h4 hs₀.le
          _ = a / 2 := by field_simp
      linarith [h5, ha]
    exact ht2 ⟨by linarith [(abs_lt.mp hfin).1], by linarith [(abs_lt.mp hfin).2]⟩

/-- **Clause (2): edge avoidance for the left detours.**  Every `SL(2,ℤ)`-translate of a point of
the three open sides of one of the two left rectangles `[-a,0] × [s₀-a, s₀+a]`,
`[-a,0] × [s₀⁻¹-a, s₀⁻¹+a]` is at hyperbolic distance at least `ε` from `1 + i s₀`. -/
lemma edge_avoid_left (s₀ : ℝ) (hs₀ : 0 < s₀) {ε a δ₀ : ℝ} (hε : 0 < ε) (ha : 0 < a)
    (ha_s₀ : a < s₀) (ha_inv : a < s₀⁻¹)
    (hgapD : ∀ ν : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      ν • Work.Kernels.imagAxis s₀ hs₀ ≠ Work.Kernels.imagAxis s₀ hs₀ →
      δ₀ ≤ dist (ν • Work.Kernels.imagAxis s₀ hs₀) (Work.Kernels.imagAxis s₀ hs₀))
    (hεr₁ : ε ≤ Real.arcosh (1 + a ^ 2 / (2 * s₀ * (s₀ + a))))
    (hεr₂ : ε ≤ Real.arcosh (1 + a ^ 2 / (2 * s₀⁻¹ * (s₀⁻¹ + a))))
    (hεδ₁ : ε ≤ δ₀ - Real.arcosh (1 + a ^ 2 / (s₀ * (s₀ - a))))
    (hεδ₂ : ε ≤ δ₀ - Real.arcosh (1 + a ^ 2 / (s₀⁻¹ * (s₀⁻¹ - a)))) :
    ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (u v : ℝ), 0 < v →
      ((-a < u ∧ u < 0 ∧ (v = s₀ - a ∨ v = s₀ + a))
        ∨ (u = -a ∧ s₀ - a < v ∧ v < s₀ + a)
        ∨ (-a < u ∧ u < 0 ∧ (v = s₀⁻¹ - a ∨ v = s₀⁻¹ + a))
        ∨ (u = -a ∧ s₀⁻¹ - a < v ∧ v < s₀⁻¹ + a)) →
      ε ≤ dist (γ • ofReImT u v) (onePlusI s₀ hs₀) := by
  intro γ u v hv hdisj
  have hdist : dist (γ • ofReImT u v) (onePlusI s₀ hs₀)
      = dist (ofReImT u v) ((γ⁻¹ * ModularGroup.T) • Work.Kernels.imagAxis s₀ hs₀) := by
    have hγ : γ • (γ⁻¹ • onePlusI s₀ hs₀) = onePlusI s₀ hs₀ := by
      rw [← mul_smul, mul_inv_cancel, one_smul]
    rw [show dist (γ • ofReImT u v) (onePlusI s₀ hs₀)
          = dist (γ • ofReImT u v) (γ • (γ⁻¹ • onePlusI s₀ hs₀)) by rw [hγ], dist_smul_SL2Z]
    congr 1
    rw [← T_smul_imagAxis s₀ hs₀, mul_smul]
  rcases hdisj with h1 | h2 | h3 | h4
  · obtain ⟨hlow, hhigh⟩ :=
      ofReImT_dist_bounds (A := a) (c := s₀) (u := u) (v := v) ha ha_s₀ hv
        (Or.inr (Or.inr (Or.inl ⟨⟨h1.1, h1.2.1⟩, h1.2.2⟩)))
    rw [show Work.Kernels.imagAxis s₀ (lt_trans ha ha_s₀)
          = Work.Kernels.imagAxis s₀ hs₀ from rfl] at hlow hhigh
    by_cases hbase : (γ⁻¹ * ModularGroup.T) • Work.Kernels.imagAxis s₀ hs₀
        = Work.Kernels.imagAxis s₀ hs₀
    · rw [hdist, hbase]
      exact le_trans hεr₁ hlow
    · rw [hdist]
      have hδ := hgapD (γ⁻¹ * ModularGroup.T) hbase
      rw [dist_comm] at hδ
      exact le_dist_of_le_dist_sub hδ hhigh (by linarith [hεδ₁])
  · obtain ⟨hlow, hhigh⟩ :=
      ofReImT_dist_bounds (A := a) (c := s₀) (u := u) (v := v) ha ha_s₀ hv
        (Or.inr (Or.inr (Or.inr h2)))
    rw [show Work.Kernels.imagAxis s₀ (lt_trans ha ha_s₀)
          = Work.Kernels.imagAxis s₀ hs₀ from rfl] at hlow hhigh
    by_cases hbase : (γ⁻¹ * ModularGroup.T) • Work.Kernels.imagAxis s₀ hs₀
        = Work.Kernels.imagAxis s₀ hs₀
    · rw [hdist, hbase]
      exact le_trans hεr₁ hlow
    · rw [hdist]
      have hδ := hgapD (γ⁻¹ * ModularGroup.T) hbase
      rw [dist_comm] at hδ
      exact le_dist_of_le_dist_sub hδ hhigh (by linarith [hεδ₁])
  · obtain ⟨hlow, hhigh⟩ :=
      ofReImT_dist_bounds (A := a) (c := s₀⁻¹) (u := u) (v := v) ha ha_inv hv
        (Or.inr (Or.inr (Or.inl ⟨⟨h3.1, h3.2.1⟩, h3.2.2⟩)))
    rw [show Work.Kernels.imagAxis s₀⁻¹ (lt_trans ha ha_inv)
          = Work.Kernels.imagAxis s₀⁻¹ (inv_pos.mpr hs₀) from rfl] at hlow hhigh
    by_cases hbase : (γ⁻¹ * ModularGroup.T) • Work.Kernels.imagAxis s₀ hs₀
        = Work.Kernels.imagAxis s₀⁻¹ (inv_pos.mpr hs₀)
    · rw [hdist, hbase]
      exact le_trans hεr₂ hlow
    · rw [hdist]
      refine le_dist_of_le_dist_sub (p := Work.Kernels.imagAxis s₀⁻¹ (inv_pos.mpr hs₀))
        (q := (γ⁻¹ * ModularGroup.T) • Work.Kernels.imagAxis s₀ hs₀)
        (z := ofReImT u v) (r := Real.arcosh (1 + a ^ 2 / (s₀⁻¹ * (s₀⁻¹ - a))))
        (δ := δ₀) ?_ hhigh (by linarith [hεδ₂])
      have hν : (ModularGroup.S⁻¹ * (γ⁻¹ * ModularGroup.T)) • Work.Kernels.imagAxis s₀ hs₀
          ≠ Work.Kernels.imagAxis s₀ hs₀ := by
        intro hh
        apply hbase
        calc (γ⁻¹ * ModularGroup.T) • Work.Kernels.imagAxis s₀ hs₀
            = ((ModularGroup.S * ModularGroup.S⁻¹) * (γ⁻¹ * ModularGroup.T))
                • Work.Kernels.imagAxis s₀ hs₀ := by rw [mul_inv_cancel, one_mul]
          _ = ModularGroup.S • ((ModularGroup.S⁻¹ * (γ⁻¹ * ModularGroup.T))
                • Work.Kernels.imagAxis s₀ hs₀) := by rw [mul_assoc, mul_smul]
          _ = ModularGroup.S • Work.Kernels.imagAxis s₀ hs₀ := by rw [hh]
          _ = Work.Kernels.imagAxis s₀⁻¹ (inv_pos.mpr hs₀) := S_smul_imagAxis s₀ hs₀
      have hgap := hgapD (ModularGroup.S⁻¹ * (γ⁻¹ * ModularGroup.T)) hν
      rw [dist_comm] at hgap
      have h5 : dist (ModularGroup.S • Work.Kernels.imagAxis s₀ hs₀)
            ((γ⁻¹ * ModularGroup.T) • Work.Kernels.imagAxis s₀ hs₀)
          = dist (Work.Kernels.imagAxis s₀ hs₀)
            ((ModularGroup.S⁻¹ * (γ⁻¹ * ModularGroup.T)) • Work.Kernels.imagAxis s₀ hs₀) := by
        have hA : (γ⁻¹ * ModularGroup.T) • Work.Kernels.imagAxis s₀ hs₀
            = ModularGroup.S • ((ModularGroup.S⁻¹ * (γ⁻¹ * ModularGroup.T))
                • Work.Kernels.imagAxis s₀ hs₀) := by
          rw [show ModularGroup.S • ((ModularGroup.S⁻¹ * (γ⁻¹ * ModularGroup.T))
                • Work.Kernels.imagAxis s₀ hs₀)
              = (ModularGroup.S * (ModularGroup.S⁻¹ * (γ⁻¹ * ModularGroup.T)))
                • Work.Kernels.imagAxis s₀ hs₀ from (mul_smul _ _ _).symm,
            show ModularGroup.S * (ModularGroup.S⁻¹ * (γ⁻¹ * ModularGroup.T))
                = γ⁻¹ * ModularGroup.T by group]
        rw [hA, dist_smul_SL2Z]
      rw [← S_smul_imagAxis s₀ hs₀, h5]
      exact hgap
  · obtain ⟨hlow, hhigh⟩ :=
      ofReImT_dist_bounds (A := a) (c := s₀⁻¹) (u := u) (v := v) ha ha_inv hv
        (Or.inr (Or.inr (Or.inr h4)))
    rw [show Work.Kernels.imagAxis s₀⁻¹ (lt_trans ha ha_inv)
          = Work.Kernels.imagAxis s₀⁻¹ (inv_pos.mpr hs₀) from rfl] at hlow hhigh
    by_cases hbase : (γ⁻¹ * ModularGroup.T) • Work.Kernels.imagAxis s₀ hs₀
        = Work.Kernels.imagAxis s₀⁻¹ (inv_pos.mpr hs₀)
    · rw [hdist, hbase]
      exact le_trans hεr₂ hlow
    · rw [hdist]
      refine le_dist_of_le_dist_sub (p := Work.Kernels.imagAxis s₀⁻¹ (inv_pos.mpr hs₀))
        (q := (γ⁻¹ * ModularGroup.T) • Work.Kernels.imagAxis s₀ hs₀)
        (z := ofReImT u v) (r := Real.arcosh (1 + a ^ 2 / (s₀⁻¹ * (s₀⁻¹ - a))))
        (δ := δ₀) ?_ hhigh (by linarith [hεδ₂])
      have hν : (ModularGroup.S⁻¹ * (γ⁻¹ * ModularGroup.T)) • Work.Kernels.imagAxis s₀ hs₀
          ≠ Work.Kernels.imagAxis s₀ hs₀ := by
        intro hh
        apply hbase
        calc (γ⁻¹ * ModularGroup.T) • Work.Kernels.imagAxis s₀ hs₀
            = ((ModularGroup.S * ModularGroup.S⁻¹) * (γ⁻¹ * ModularGroup.T))
                • Work.Kernels.imagAxis s₀ hs₀ := by rw [mul_inv_cancel, one_mul]
          _ = ModularGroup.S • ((ModularGroup.S⁻¹ * (γ⁻¹ * ModularGroup.T))
                • Work.Kernels.imagAxis s₀ hs₀) := by rw [mul_assoc, mul_smul]
          _ = ModularGroup.S • Work.Kernels.imagAxis s₀ hs₀ := by rw [hh]
          _ = Work.Kernels.imagAxis s₀⁻¹ (inv_pos.mpr hs₀) := S_smul_imagAxis s₀ hs₀
      have hgap := hgapD (ModularGroup.S⁻¹ * (γ⁻¹ * ModularGroup.T)) hν
      rw [dist_comm] at hgap
      have h5 : dist (ModularGroup.S • Work.Kernels.imagAxis s₀ hs₀)
            ((γ⁻¹ * ModularGroup.T) • Work.Kernels.imagAxis s₀ hs₀)
          = dist (Work.Kernels.imagAxis s₀ hs₀)
            ((ModularGroup.S⁻¹ * (γ⁻¹ * ModularGroup.T)) • Work.Kernels.imagAxis s₀ hs₀) := by
        have hA : (γ⁻¹ * ModularGroup.T) • Work.Kernels.imagAxis s₀ hs₀
            = ModularGroup.S • ((ModularGroup.S⁻¹ * (γ⁻¹ * ModularGroup.T))
                • Work.Kernels.imagAxis s₀ hs₀) := by
          rw [show ModularGroup.S • ((ModularGroup.S⁻¹ * (γ⁻¹ * ModularGroup.T))
                • Work.Kernels.imagAxis s₀ hs₀)
              = (ModularGroup.S * (ModularGroup.S⁻¹ * (γ⁻¹ * ModularGroup.T)))
                • Work.Kernels.imagAxis s₀ hs₀ from (mul_smul _ _ _).symm,
            show ModularGroup.S * (ModularGroup.S⁻¹ * (γ⁻¹ * ModularGroup.T))
                = γ⁻¹ * ModularGroup.T by group]
        rw [hA, dist_smul_SL2Z]
      rw [← S_smul_imagAxis s₀ hs₀, h5]
      exact hgap

/-- **Clause (3): classification of the orbit points in the left rectangles.**  If `τ` is within
`ε` of `1 + i s₀`, `z = γ • τ` and `z` lies in one of the two closed left rectangles (whose points
are within `b₁` resp. `b₂` of the two "bad" heights `i s₀`, `i/s₀`), with
`ε + b₁, ε + b₂ ≤ δ₀` the orbit gap at `i s₀`, then `z` is one of the two forbidden positions:
the pole `z = τ - 1`, or the removable coincidence `z = -1/(τ-1)`. -/
lemma classify_left (s₀ : ℝ) (hs₀ : 0 < s₀) {ε δ₀ b₁ b₂ : ℝ}
    {A₁ ξ₁ A₂ ξ₂ : ℝ}
    (hgapD : ∀ ν : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      ν • Work.Kernels.imagAxis s₀ hs₀ ≠ Work.Kernels.imagAxis s₀ hs₀ →
      δ₀ ≤ dist (ν • Work.Kernels.imagAxis s₀ hs₀) (Work.Kernels.imagAxis s₀ hs₀))
    (hεb₁ : ε + b₁ ≤ δ₀) (hεb₂ : ε + b₂ ≤ δ₀)
    (hb₁ : ∀ z : UpperHalfPlane, leftRect s₀ A₁ ξ₁ z →
      dist z (Work.Kernels.imagAxis s₀ hs₀) ≤ b₁)
    (hb₂ : ∀ z : UpperHalfPlane, leftRect s₀⁻¹ A₂ ξ₂ z →
      dist z (Work.Kernels.imagAxis s₀⁻¹ (inv_pos.mpr hs₀)) ≤ b₂) :
    ∀ τ : UpperHalfPlane, dist τ (onePlusI s₀ hs₀) < ε →
      ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        (leftRect s₀ A₁ ξ₁ z ∨ leftRect s₀⁻¹ A₂ ξ₂ z) → z = γ • τ →
        z = tauSubOne τ ∨ z = tauCoinc τ := by
  intro τ hτ γ z hzR hzeq
  rcases hzR with hzR | hzR
  · exact eq_tauSubOne_or_tauCoinc_of_mul_T_fixes hs₀ hzeq
      (mul_T_smul_imagAxis_eq_of_dist_le hs₀ hgapD hτ hzeq (hb₁ z hzR) hεb₁)
  · -- `z` lies near `i/s₀`; conjugate by `S`, which exchanges the two bad heights
    have hz' : ModularGroup.S • z = (ModularGroup.S * γ) • τ := by rw [hzeq, mul_smul]
    have hb' : dist (ModularGroup.S • z) (Work.Kernels.imagAxis s₀ hs₀) ≤ b₂ := by
      rw [← S_smul_imagAxis_inv s₀ hs₀, show
        dist (ModularGroup.S • z) (ModularGroup.S • Work.Kernels.imagAxis s₀⁻¹ (inv_pos.mpr hs₀))
          = dist z (Work.Kernels.imagAxis s₀⁻¹ (inv_pos.mpr hs₀)) from
        dist_smul_SL2Z _ _ _]
      exact hb₂ z hzR
    have hfix := mul_T_smul_imagAxis_eq_of_dist_le hs₀ hgapD hτ hz' hb' hεb₂
    rcases eq_tauSubOne_or_tauCoinc_of_mul_T_fixes hs₀ hz' hfix with h | h
    · right
      have hz : z = ModularGroup.S • tauSubOne τ := by rw [← S_smul_self z, h]
      rw [hz, S_smul_tauSubOne]
    · left
      have hz : z = ModularGroup.S • tauCoinc τ := by rw [← S_smul_self z, h]
      rw [hz, S_smul_tauCoinc]


/-- **The geometry of the left-detour contour at `1 + i s₀`.**  There are a hyperbolic ball
`B(1 + i s₀, ε)` and two *left* rectangles `R₁ = [-ξ₁,0] × [s₀-A₁, s₀+A₁]` (the pole height) and
`R₂ = [-ξ₂,0] × [s₀⁻¹-A₂, s₀⁻¹+A₂]` (the coincidence height) with:

* (sizes) `0 < A₁, 0 < ξ₁`, `0 ≤ A₂, 0 ≤ ξ₂`, `A₁ < s₀`, `ξ₁ < 1`, `A₂ < s₀⁻¹`, and
  `4 s₀ ε ≤ A₁`, `4 s₀ ε ≤ ξ₁`: the rectangles are at least as wide as the part of the ball they
  have to cover;
* (separation) if `s₀ = 1` then `A₂ = ξ₂ = 0` (the second rectangle degenerates, since the two bad
  heights coincide); if `s₀ ≠ 1` then `A₂, ξ₂ > 0` with `4 ε ≤ A₂ s₀`, `4 ε ≤ ξ₂ s₀` and
  `A₁ + A₂ < |s₀ - s₀⁻¹|`: the two rectangles are separated in height, so the pole `τ - 1` misses
  `R₂` and the coincidence `ST⁻¹τ` misses `R₁`;
* (1) *axis cleanliness*: for `t > 0` outside the two intervals `I₁ = (s₀-A₁, s₀+A₁)` and
  `I₂ = (s₀⁻¹-A₂, s₀⁻¹+A₂)` and every `τ` in the ball, `j τ ≠ j(i t)`: the retained part of the
  imaginary axis carries no pole;
* (2) *edge avoidance*: every `SL(2,ℤ)`-translate of every point of the three open sides of `R₁`
  or of `R₂` is at distance at least `ε` from `1 + i s₀`: the contour (in the second variable)
  avoids all the moving poles, which is what makes the detours holomorphic in `τ`;
* (3) *classification*: for `τ` in the ball, every point of `R₁ ∪ R₂` lying in the `SL(2,ℤ)`-orbit
  of `τ` is one of the two points `τ - 1` (the pole, inside `R₁` when `Re τ < 1`) and
  `ST⁻¹τ = -1/(τ-1)` (the removable coincidence, which has `Re > 0` when `Re τ < 1` and hence is in
  neither rectangle).  This is what identifies the residue enclosed by the first detour.

Suggested route: adapt the fully proved `Work.Asymptotics.exists_contour_avoid` (same file
provides `orbitGap_imagAxis`, `web_near_center_param`, `abs_im_sub_le_of_dist`,
`ofReImT_dist_bounds`, `le_dist_of_le_dist_sub`, `T_smul_imagAxis`, `S_smul_imagAxis`,
`dist_smul_SL2Z`).  Clauses (1) and (2) are its conditions (1) and (2) with the rectangles
mirrored to `Re ≤ 0` and with independent parameters; clause (3) is the orbit-gap argument: if
`z ∈ R₁ ∪ R₂` has `z = γ • τ` then `d(γ • τ₀, i s₀)` (resp. `d(γ • τ₀, i/s₀)`) is at most
`ε + O(ε)`, so `T γ` (resp. `T S⁻¹ γ`) lies in the stabiliser of `i s₀`, which by
`eq_one_or_neg_one_or_S_of_smul_imagAxis` is `{±1, ±S}`, giving `γ ∈ {±T⁻¹, ±S T⁻¹}`, i.e.
`z = τ - 1` or `z = tauCoinc τ`.  (All parameters are existential, so `ε` may be shrunk at will.) -/
theorem exists_contour_left_data (s₀ : ℝ) (hs₀ : 0 < s₀) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ A₁ ξ₁ A₂ ξ₂ : ℝ,
      0 < A₁ ∧ 0 < ξ₁ ∧ 0 ≤ A₂ ∧ 0 ≤ ξ₂ ∧ A₁ < s₀ ∧ ξ₁ < 1 ∧ A₂ < s₀⁻¹ ∧
      4 * s₀ * ε ≤ A₁ ∧ 4 * s₀ * ε ≤ ξ₁ ∧
      (s₀ = 1 → A₂ = 0 ∧ ξ₂ = 0) ∧
      (s₀ ≠ 1 → 0 < A₂ ∧ 0 < ξ₂ ∧ 4 * ε ≤ A₂ * s₀ ∧ 4 * ε ≤ ξ₂ * s₀ ∧
        A₁ + A₂ < |s₀ - s₀⁻¹|) ∧
      (∀ (t : ℝ) (ht : 0 < t), t ∉ Set.Ioo (s₀ - A₁) (s₀ + A₁) →
        t ∉ Set.Ioo (s₀⁻¹ - A₂) (s₀⁻¹ + A₂) →
        ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε →
          Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) ∧
      (∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (u v : ℝ), 0 < v →
        ((-ξ₁ < u ∧ u < 0 ∧ (v = s₀ - A₁ ∨ v = s₀ + A₁))
          ∨ (u = -ξ₁ ∧ s₀ - A₁ < v ∧ v < s₀ + A₁)
          ∨ (-ξ₂ < u ∧ u < 0 ∧ (v = s₀⁻¹ - A₂ ∨ v = s₀⁻¹ + A₂))
          ∨ (u = -ξ₂ ∧ s₀⁻¹ - A₂ < v ∧ v < s₀⁻¹ + A₂)) →
        ε ≤ dist (γ • Work.Asymptotics.ofReImT u v) (Work.Asymptotics.onePlusI s₀ hs₀)) ∧
      (∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε →
        ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
          (Work.Asymptotics.leftRect s₀ A₁ ξ₁ z ∨ Work.Asymptotics.leftRect s₀⁻¹ A₂ ξ₂ z) →
          z = γ • τ →
          z = Work.Asymptotics.tauSubOne τ ∨ z = Work.Asymptotics.tauCoinc τ) ∧
      A₂ ≤ |s₀ - s₀⁻¹| / 8 ∧ ξ₂ ≤ |s₀ - s₀⁻¹| / 8 ∧ A₂ ≤ 1 / 4 ∧ ξ₂ ≤ 1 / 4 ∧ ε ≤ 1 / 4 ∧
      ε ≤ A₁ / (4 * s₀) ∧ ε ≤ A₁ * s₀ / 8 ∧
      (∃ rw₀ : ℝ, 0 < rw₀ ∧ ε ≤ rw₀ ∧
        ∀ (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (t : ℝ) (ht : 0 < t),
          dist (σ • Work.Kernels.imagAxis t ht) (Work.Asymptotics.onePlusI s₀ hs₀) < rw₀ →
          (σ • Work.Kernels.imagAxis t ht).re = 1 ∧
            ((σ • Work.Kernels.imagAxis t ht).im = t ∨
              (σ • Work.Kernels.imagAxis t ht).im = t⁻¹)) := by
  -- ## The orbit gap at `i s₀`
  obtain ⟨δ₀, F₀, hδ₀pos, hF₀pos, hδ₀eq, hgapD⟩ := orbitGap_imagAxis_dist s₀ hs₀
  have hδ₀gt : (1 : ℝ) < 1 + F₀ / (2 * s₀) := by
    have h : (0 : ℝ) < F₀ / (2 * s₀) := by positivity
    linarith
  -- ## The web radius and the scale
  obtain ⟨rw₀, hrw₀pos, hweb⟩ := web_near_center_param s₀ hs₀
  obtain ⟨m, hmpos, hmle1, hm_le_s₀, hm_le_inv⟩ :
      ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧ m ≤ s₀ ∧ m ≤ s₀⁻¹ := by
    refine ⟨min s₀ s₀⁻¹, lt_min hs₀ (inv_pos.mpr hs₀), ?_, min_le_left _ _, min_le_right _ _⟩
    rcases le_or_gt s₀ 1 with h | h
    · exact le_trans (min_le_left _ _) h
    · exact le_trans (min_le_right _ _) (inv_lt_one_of_one_lt₀ h).le
  set a : ℝ := min (m / 4) (min (m * Real.sqrt (F₀ / (4 * s₀)) / 4)
      (if s₀ = 1 then 1 else |s₀ - s₀⁻¹| / 8)) with ha_def
  have ha_le_1 : a ≤ m / 4 := by rw [ha_def]; exact min_le_left _ _
  have ha_le_2 : a ≤ m * Real.sqrt (F₀ / (4 * s₀)) / 4 := by
    rw [ha_def]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have ha_le_3 : a ≤ (if s₀ = 1 then 1 else |s₀ - s₀⁻¹| / 8) := by
    rw [ha_def]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hsep : s₀ ≠ 1 → s₀ - s₀⁻¹ ≠ 0 := by
    intro hne h0
    have hh : s₀ = s₀⁻¹ := by linarith
    have h1 : s₀ * s₀⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hs₀)
    rw [← hh] at h1
    have h2 : s₀ ^ 2 = 1 := by nlinarith [h1]
    exact hne (by nlinarith [h2, hs₀])
  have habs_pos : s₀ ≠ 1 → 0 < |s₀ - s₀⁻¹| := fun hne => abs_pos.mpr (hsep hne)
  have hapos : 0 < a := by
    rw [ha_def]
    refine lt_min (by positivity) (lt_min ?_ ?_)
    · positivity
    · by_cases h1 : s₀ = 1
      · rw [if_pos h1]; norm_num
      · rw [if_neg h1]; exact div_pos (habs_pos h1) (by norm_num)
  have ha_lt_m : a < m := by linarith
  have ha_s₀ : a < s₀ := lt_of_lt_of_le ha_lt_m hm_le_s₀
  have ha_inv : a < s₀⁻¹ := lt_of_lt_of_le ha_lt_m hm_le_inv
  have ha_one : a < 1 := lt_of_lt_of_le ha_lt_m hmle1
  have ha_sep : s₀ ≠ 1 → 2 * a < |s₀ - s₀⁻¹| := by
    intro h1
    have h := ha_le_3
    rw [if_neg h1] at h
    linarith [h, habs_pos h1]
  -- ## The quantitative estimates: the two height bounds lie well inside the gap
  have hrmax_lt : ∀ c : ℝ, m ≤ c → Real.arcosh (1 + a ^ 2 / (c * (c - a))) < δ₀ := by
    intro c hc
    have hc0 : 0 < c := lt_of_lt_of_le hmpos hc
    have hcA : 0 < c - a := by
      have : a < c := lt_of_lt_of_le ha_lt_m hc
      linarith
    have hden : 0 < c * (c - a) := by positivity
    have hkey : a ^ 2 / (c * (c - a)) ≤ F₀ / (4 * s₀) := by
      rw [div_le_iff₀ hden]
      have hsqF : (Real.sqrt (F₀ / (4 * s₀))) ^ 2 = F₀ / (4 * s₀) := Real.sq_sqrt (by positivity)
      have hcq : (3 * m ^ 2) / 4 ≤ c * (c - a) := by
        have h2 : 3 * m / 4 ≤ c - a := by linarith [ha_le_1, hc]
        have h3 := mul_le_mul hc h2 (by linarith) (le_of_lt hc0)
        linarith [h3]
      have hA2 : a ^ 2 ≤ m ^ 2 * (F₀ / (4 * s₀)) / 16 := by
        have h1 : a ≤ m * Real.sqrt (F₀ / (4 * s₀)) / 4 := ha_le_2
        nlinarith [h1, hapos, hsqF]
      nlinarith [hA2, hcq, hmpos, hF₀pos, hs₀]
    have hco : Real.cosh (Real.arcosh (1 + a ^ 2 / (c * (c - a)))) < Real.cosh δ₀ := by
      have h1 : (0 : ℝ) < a ^ 2 / (c * (c - a)) := by positivity
      have h3 : F₀ / (4 * s₀) < F₀ / (2 * s₀) := by
        have h4 : 0 < F₀ / (4 * s₀) := by positivity
        have h5 : F₀ / (4 * s₀) + F₀ / (4 * s₀) = F₀ / (2 * s₀) := by field_simp; ring
        linarith
      rw [Real.cosh_arcosh (by linarith), hδ₀eq, Real.cosh_arcosh (le_of_lt hδ₀gt)]
      linarith [hkey, h3]
    have h2 := Real.cosh_lt_cosh.mp hco
    rwa [abs_of_nonneg (Real.arcosh_nonneg (by
          have : (0 : ℝ) < a ^ 2 / (c * (c - a)) := by positivity
          linarith)),
      abs_of_nonneg hδ₀pos.le] at h2
  set b₁ : ℝ := Real.arcosh (1 + a ^ 2 / (s₀ * (s₀ - a))) with hb₁def
  set b₂ : ℝ := Real.arcosh (1 + a ^ 2 / (s₀⁻¹ * (s₀⁻¹ - a))) with hb₂def
  have hb₁_lt : b₁ < δ₀ := by rw [hb₁def]; exact hrmax_lt s₀ hm_le_s₀
  have hb₂_lt : b₂ < δ₀ := by rw [hb₂def]; exact hrmax_lt s₀⁻¹ hm_le_inv
  have hb₁_pos : 0 < b₁ := by
    rw [hb₁def]
    apply Real.arcosh_pos
    have h : (0 : ℝ) < a ^ 2 / (s₀ * (s₀ - a)) := by
      apply div_pos (by positivity)
      nlinarith [ha_s₀, hs₀]
    linarith
  set Rmx : ℝ := max b₁ b₂ with hRmxdef
  set Rmn : ℝ := min (Real.arcosh (1 + a ^ 2 / (2 * s₀ * (s₀ + a))))
      (Real.arcosh (1 + a ^ 2 / (2 * s₀⁻¹ * (s₀⁻¹ + a)))) with hRmndef
  have hRmn_pos : 0 < Rmn := by
    rw [hRmndef]
    apply lt_min
    · apply Real.arcosh_pos
      have h : (0 : ℝ) < a ^ 2 / (2 * s₀ * (s₀ + a)) := by positivity
      linarith
    · apply Real.arcosh_pos
      have h : (0 : ℝ) < a ^ 2 / (2 * s₀⁻¹ * (s₀⁻¹ + a)) := by positivity
      linarith
  have hRmx_lt : Rmx < δ₀ := by rw [hRmxdef]; exact max_lt hb₁_lt hb₂_lt
  -- ## The second rectangle degenerates exactly when the two bad heights coincide
  set A₂ : ℝ := if s₀ = 1 then 0 else a with hA₂def
  have hA₂nn : 0 ≤ A₂ := by
    rw [hA₂def]; split
    · norm_num
    · exact hapos.le
  have hA₂_le_a : A₂ ≤ a := by
    rw [hA₂def]; split
    · exact hapos.le
    · exact le_rfl
  have hA₂_lt_inv : A₂ < s₀⁻¹ := lt_of_le_of_lt hA₂_le_a ha_inv
  -- ## The radius of the ball
  obtain ⟨ε, hεpos, hε4, hεa₁, hεa₂, hεw, hεδ, hεr⟩ :
      ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 4 ∧ ε ≤ a / (4 * s₀) ∧ ε ≤ a * s₀ / 8 ∧ ε ≤ rw₀ ∧
        ε ≤ δ₀ - Rmx ∧ ε ≤ Rmn := by
    have hδRmx : 0 < δ₀ - Rmx := by linarith
    refine ⟨min (1 / 4) (min (a / (4 * s₀)) (min (a * s₀ / 8) (min rw₀ (min (δ₀ - Rmx) Rmn)))),
      lt_min (by norm_num) (lt_min (by positivity) (lt_min (by positivity) (lt_min hrw₀pos
        (lt_min hδRmx hRmn_pos)))), min_le_left _ _, ?_, ?_, ?_, ?_, ?_⟩
    · exact le_trans (min_le_right _ _) (min_le_left _ _)
    · exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    · exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _)))
    · exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
    · exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))))
  have hεr₁ : ε ≤ Real.arcosh (1 + a ^ 2 / (2 * s₀ * (s₀ + a))) :=
    le_trans hεr (by rw [hRmndef]; exact min_le_left _ _)
  have hεr₂ : ε ≤ Real.arcosh (1 + a ^ 2 / (2 * s₀⁻¹ * (s₀⁻¹ + a))) :=
    le_trans hεr (by rw [hRmndef]; exact min_le_right _ _)
  have hεδ₁ : ε ≤ δ₀ - Real.arcosh (1 + a ^ 2 / (s₀ * (s₀ - a))) := by
    rw [← hb₁def]
    have h1 : δ₀ - Rmx ≤ δ₀ - b₁ := by
      rw [hRmxdef]; exact sub_le_sub_left (le_max_left b₁ b₂) δ₀
    linarith
  have hεδ₂ : ε ≤ δ₀ - Real.arcosh (1 + a ^ 2 / (s₀⁻¹ * (s₀⁻¹ - a))) := by
    rw [← hb₂def]
    have h1 : δ₀ - Rmx ≤ δ₀ - b₂ := by
      rw [hRmxdef]; exact sub_le_sub_left (le_max_right b₁ b₂) δ₀
    linarith
  have hεb₁ : ε + b₁ ≤ δ₀ := by
    have h1 : δ₀ - Rmx ≤ δ₀ - b₁ := by
      rw [hRmxdef]; exact sub_le_sub_left (le_max_left b₁ b₂) δ₀
    linarith
  have hεb₂ : ε + b₂ ≤ δ₀ := by
    have h1 : δ₀ - Rmx ≤ δ₀ - b₂ := by
      rw [hRmxdef]; exact sub_le_sub_left (le_max_right b₁ b₂) δ₀
    linarith
  have h4sε : 4 * s₀ * ε ≤ a := by
    have h := mul_le_mul_of_nonneg_left hεa₁ (by positivity : (0 : ℝ) ≤ 4 * s₀)
    rwa [show 4 * s₀ * (a / (4 * s₀)) = a by field_simp] at h
  -- ## Assembly
  refine ⟨ε, hεpos, a, a, A₂, A₂, hapos, hapos, hA₂nn, hA₂nn, ha_s₀, ha_one, hA₂_lt_inv,
    h4sε, h4sε, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hε4, hεa₁, hεa₂,
    ⟨rw₀, hrw₀pos, hεw, hweb⟩⟩
  · -- `s₀ = 1`: the second rectangle degenerates
    intro h1
    rw [hA₂def, if_pos h1]
    exact ⟨rfl, rfl⟩
  · -- `s₀ ≠ 1`: the second rectangle is non-degenerate and separated in height
    intro hne
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hA₂def, if_neg hne]; exact hapos
    · rw [hA₂def, if_neg hne]; exact hapos
    · rw [hA₂def, if_neg hne]
      have h := mul_le_mul_of_nonneg_left hεa₂ (by norm_num : (0 : ℝ) ≤ 4)
      nlinarith [h, hs₀, hapos]
    · rw [hA₂def, if_neg hne]
      have h := mul_le_mul_of_nonneg_left hεa₂ (by norm_num : (0 : ℝ) ≤ 4)
      nlinarith [h, hs₀, hapos]
    · rw [hA₂def, if_neg hne]
      linarith [ha_sep hne]
  · -- (1) axis cleanliness
    intro t ht ht1 ht2 τ hτ
    refine jInvariantFun_ne_of_dist_lt_left s₀ hs₀ hεpos hε4 hapos hεa₁ hεa₂ hεw hweb t ht ht1 ?_ τ hτ
    by_cases h1 : s₀ = 1
    · rw [h1, inv_one]
      rw [h1] at ht1
      exact ht1
    · rw [hA₂def, if_neg h1] at ht2
      exact ht2
  · -- (2) edge avoidance
    intro γ u v hv hdisj
    have hdisj' : ((-a < u ∧ u < 0 ∧ (v = s₀ - a ∨ v = s₀ + a))
        ∨ (u = -a ∧ s₀ - a < v ∧ v < s₀ + a)
        ∨ (-a < u ∧ u < 0 ∧ (v = s₀⁻¹ - a ∨ v = s₀⁻¹ + a))
        ∨ (u = -a ∧ s₀⁻¹ - a < v ∧ v < s₀⁻¹ + a)) := by
      rcases hdisj with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · by_cases h1 : s₀ = 1
        · exfalso
          rw [hA₂def, if_pos h1] at h
          linarith [h.1, h.2.1]
        · rw [hA₂def, if_neg h1] at h
          exact Or.inr (Or.inr (Or.inl h))
      · by_cases h1 : s₀ = 1
        · exfalso
          rw [hA₂def, if_pos h1] at h
          linarith [h.2.1, h.2.2]
        · rw [hA₂def, if_neg h1] at h
          exact Or.inr (Or.inr (Or.inr h))
    exact edge_avoid_left s₀ hs₀ hεpos hapos ha_s₀ ha_inv hgapD hεr₁ hεr₂ hεδ₁ hεδ₂ γ u v hv hdisj'
  · -- (3) classification of the orbit points inside the rectangles
    refine classify_left s₀ hs₀ (A₁ := a) (ξ₁ := a) (A₂ := A₂) (ξ₂ := A₂)
      (b₁ := b₁) (b₂ := b₂) hgapD hεb₁ hεb₂ ?_ ?_
    · intro z hz
      have h := dist_le_of_mem_leftRect (c := s₀) (A := a) (ξ := a) hapos.le hapos.le hs₀
        ha_s₀ hz
      have hid : (a ^ 2 + a ^ 2) / (2 * s₀ * (s₀ - a)) = a ^ 2 / (s₀ * (s₀ - a)) := by
        field_simp; ring
      rw [hid] at h
      rwa [hb₁def]
    · intro z hz
      have h := dist_le_of_mem_leftRect (c := s₀⁻¹) (A := A₂) (ξ := A₂) hA₂nn hA₂nn
        (inv_pos.mpr hs₀) hA₂_lt_inv hz
      rw [hb₂def]
      refine le_trans h ?_
      have hc0 : 0 < s₀⁻¹ := inv_pos.mpr hs₀
      have hd1 : (0 : ℝ) < 2 * s₀⁻¹ * (s₀⁻¹ - A₂) := by nlinarith [hA₂_lt_inv, hc0]
      have hd2 : (0 : ℝ) < s₀⁻¹ * (s₀⁻¹ - a) := by nlinarith [ha_inv, hc0]
      have hnum : A₂ ^ 2 + A₂ ^ 2 ≤ 2 * a ^ 2 := by
        nlinarith [hA₂_le_a, hA₂nn]
      have hineq : (A₂ ^ 2 + A₂ ^ 2) / (2 * s₀⁻¹ * (s₀⁻¹ - A₂))
          ≤ a ^ 2 / (s₀⁻¹ * (s₀⁻¹ - a)) := by
        rw [div_le_div_iff₀ hd1 hd2]
        have h1 : (A₂ ^ 2 + A₂ ^ 2) * (s₀⁻¹ * (s₀⁻¹ - a))
            ≤ (2 * a ^ 2) * (s₀⁻¹ * (s₀⁻¹ - a)) :=
          mul_le_mul_of_nonneg_right hnum (by positivity)
        have h2 : (2 * a ^ 2) * (s₀⁻¹ * (s₀⁻¹ - a)) ≤ (2 * a ^ 2) * (s₀⁻¹ * (s₀⁻¹ - A₂)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hc0)
        have h3 : a ^ 2 * (2 * s₀⁻¹ * (s₀⁻¹ - A₂))
            = (2 * a ^ 2) * (s₀⁻¹ * (s₀⁻¹ - A₂)) := by ring
        linarith [h1, h2, h3]
      have hpos1 : (0 : ℝ) < 1 + (A₂ ^ 2 + A₂ ^ 2) / (2 * s₀⁻¹ * (s₀⁻¹ - A₂)) := by
        have h : (0 : ℝ) ≤ (A₂ ^ 2 + A₂ ^ 2) / (2 * s₀⁻¹ * (s₀⁻¹ - A₂)) :=
          div_nonneg (by positivity) hd1.le
        linarith
      have hpos2 : (0 : ℝ) < 1 + a ^ 2 / (s₀⁻¹ * (s₀⁻¹ - a)) := by
        have h : (0 : ℝ) ≤ a ^ 2 / (s₀⁻¹ * (s₀⁻¹ - a)) := div_nonneg (by positivity) hd2.le
        linarith
      exact (Real.arcosh_le_arcosh hpos1 hpos2).mpr (by linarith [hineq])

  · -- `A₂ ≤ |s₀ - s₀⁻¹| / 8`
    by_cases h1 : s₀ = 1
    · rw [hA₂def, if_pos h1, h1]; norm_num
    · have h3 : a ≤ |s₀ - s₀⁻¹| / 8 := by
        have h := ha_le_3
        rwa [if_neg h1] at h
      exact le_trans hA₂_le_a h3
  · -- `ξ₂ ≤ |s₀ - s₀⁻¹| / 8`
    by_cases h1 : s₀ = 1
    · rw [hA₂def, if_pos h1, h1]; norm_num
    · have h3 : a ≤ |s₀ - s₀⁻¹| / 8 := by
        have h := ha_le_3
        rwa [if_neg h1] at h
      exact le_trans hA₂_le_a h3
  · -- `A₂ ≤ 1 / 4`  (this is what makes `I₂ ⊆ (0,1]` for **every** height `s₀ > 1`,
    -- not only `s₀ < 7`: `A₂ ≤ m/4 ≤ 1/4` whereas `s₀⁻¹ + A₂ < 1` needs `A₂ < 1 - s₀⁻¹`
    -- and `1 - s₀⁻¹ ≥ 1/7 > 1/4` once `s₀ ≥ 7`)
    have ha14 : a ≤ 1 / 4 := by nlinarith [ha_le_1, hmle1]
    exact le_trans hA₂_le_a ha14
  · -- `ξ₂ ≤ 1 / 4`
    have ha14 : a ≤ 1 / 4 := by nlinarith [ha_le_1, hmle1]
    exact le_trans hA₂_le_a ha14

end Work.LayerCont.ECS
