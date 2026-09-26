import Mathlib
import Submission.Work.Smooth.BoxGeneric.LocalArc.local_arc_of_max_of_tangential

/-!
# The zero set of `max (max f₁ f₂) f₃` near a common regular direction

Let `f₁ f₂ f₃ : ℝ × ℝ → ℝ` be `C¹`, let `p` be a common zero of the three, and suppose that there
is a direction `r` with `(fderiv ℝ fᵢ p) r = 1` for `i = 1, 2, 3`.  Then near `p` the zero set
`{q | max (max (f₁ q) (f₂ q)) (f₃ q) = 0}` is a topological arc through `p`: it admits a continuous
injective parametrisation `ρ` on `(-1, 1)`, with `ρ 0 = p`, and the image of `ρ` is exactly the
zero set in a small ball around `p`.

The proof is the same as in `local_arc_of_max_of_tangential`, with two differences.  The three
linear parts `fderiv ℝ fᵢ p` need not be equal, so we first straighten the common direction: if
`r = (a, b) ≠ 0` we use the linear map `z ↦ (a z₁ + b z₂, b z₁ - a z₂)` (whose matrix is symmetric
and has square `(a² + b²) · id`), which sends `(1, 0)` to `r`.  Composing with `p + M ·` we reduce
to the case where all three functions grow at unit rate in the first coordinate; the zero set of
each of the three is then a graph `x = ψᵢ y` over the second coordinate (this is
`exists_root_pair` applied to the pair `(fᵢ, fᵢ)`), and the zero set of the maximum is the graph of
`y ↦ min (min (ψ₁ y) (ψ₂ y)) (ψ₃ y)`.
-/

open Set

set_option linter.unusedVariables false

namespace Work.Smooth.BoxGeneric.LocalArc

/-! ### A single function: the zero set is a graph over the second coordinate -/

/-- The one-function form of `exists_root_pair` (applied to the pair `(F, F)`). -/
private theorem exists_root_single' {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ 1 F) (hF0 : F 0 = 0)
    (ha : 0 < (fderiv ℝ F 0) (1, 0)) :
    ∃ Rx Ry : ℝ, 0 < Rx ∧ 0 < Ry ∧ ∃ ψ : ℝ → ℝ, ψ 0 = 0 ∧
      ContinuousOn ψ (Set.Ioo (-Ry) Ry) ∧
      (∀ y : ℝ, |y| ≤ Ry → |ψ y| ≤ Rx ∧ F (ψ y, y) = 0) ∧
      (∀ x y : ℝ, |x| ≤ Rx → |y| ≤ Ry → (F (x, y) ≤ 0 ↔ x ≤ ψ y)) ∧
      (∀ x y : ℝ, |x| ≤ Rx → |y| ≤ Ry → (F (x, y) = 0 ↔ x = ψ y)) := by
  obtain ⟨Rx, Ry, hRx, hRy, ψ, φ, hψ0, hφ0, hψc, hφc, hroot, hsign, hzero⟩ :=
    exists_root_pair hF hF hF0 hF0 rfl ha
  exact ⟨Rx, Ry, hRx, hRy, ψ, hψ0, hψc,
    fun y hy => ⟨(hroot y hy).1, (hroot y hy).2.2.1⟩,
    fun x y hx hy => (hsign x y hx hy).1,
    fun x y hx hy => (hzero x y hx hy).1⟩

/-- A function continuous at the origin with value `0` there is bounded by `R` on a symmetric
neighbourhood of the origin. -/
private lemma exists_abs_le_of_continuousAt_zero {ψ : ℝ → ℝ} {R : ℝ}
    (hcont : ContinuousAt ψ 0) (h0 : ψ 0 = 0) (hR : 0 < R) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, |y| ≤ δ → |ψ y| ≤ R := by
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ₀, hδ₀pos, hδ₀spec⟩ := hcont R hR
  refine ⟨δ₀ / 2, by linarith, ?_⟩
  intro y hy
  have hy' : dist y 0 < δ₀ := by rw [Real.dist_eq, sub_zero]; linarith
  have h := hδ₀spec hy'
  rw [Real.dist_eq, h0, sub_zero] at h
  exact h.le

/-! ### Three functions with a common regular direction -/

/-- **Three graphs on a common rectangle.**  If `F`, `G`, `H` are `C¹`, vanish at the origin and
have positive first partial derivative at the origin, then on a common rectangle each zero set is
the graph of a continuous function of the second coordinate. -/
private theorem exists_root_triple {F G H : ℝ × ℝ → ℝ} (hF : ContDiff ℝ 1 F) (hG : ContDiff ℝ 1 G)
    (hH : ContDiff ℝ 1 H) (hF0 : F 0 = 0) (hG0 : G 0 = 0) (hH0 : H 0 = 0)
    (haF : 0 < (fderiv ℝ F 0) (1, 0)) (haG : 0 < (fderiv ℝ G 0) (1, 0))
    (haH : 0 < (fderiv ℝ H 0) (1, 0)) :
    ∃ Rx Ry : ℝ, 0 < Rx ∧ 0 < Ry ∧ ∃ ψ φ χ : ℝ → ℝ,
      ψ 0 = 0 ∧ φ 0 = 0 ∧ χ 0 = 0 ∧
      ContinuousOn ψ (Set.Ioo (-Ry) Ry) ∧ ContinuousOn φ (Set.Ioo (-Ry) Ry) ∧
      ContinuousOn χ (Set.Ioo (-Ry) Ry) ∧
      (∀ y : ℝ, |y| ≤ Ry → |ψ y| ≤ Rx ∧ |φ y| ≤ Rx ∧ |χ y| ≤ Rx ∧
        F (ψ y, y) = 0 ∧ G (φ y, y) = 0 ∧ H (χ y, y) = 0) ∧
      (∀ x y : ℝ, |x| ≤ Rx → |y| ≤ Ry → (F (x, y) ≤ 0 ↔ x ≤ ψ y) ∧
        (G (x, y) ≤ 0 ↔ x ≤ φ y) ∧ (H (x, y) ≤ 0 ↔ x ≤ χ y)) ∧
      (∀ x y : ℝ, |x| ≤ Rx → |y| ≤ Ry → (F (x, y) = 0 ↔ x = ψ y) ∧
        (G (x, y) = 0 ↔ x = φ y) ∧ (H (x, y) = 0 ↔ x = χ y)) := by
  obtain ⟨RxF, RyF, hRxF, hRyF, ψ, hψ0, hψc, hψroot, hψsign, hψzero⟩ :=
    exists_root_single' hF hF0 haF
  obtain ⟨RxG, RyG, hRxG, hRyG, φ, hφ0, hφc, hφroot, hφsign, hφzero⟩ :=
    exists_root_single' hG hG0 haG
  obtain ⟨RxH, RyH, hRxH, hRyH, χ, hχ0, hχc, hχroot, hχsign, hχzero⟩ :=
    exists_root_single' hH hH0 haH
  set Rx : ℝ := min (min RxF RxG) RxH with hRxdef
  have hRxpos : 0 < Rx := by
    rw [hRxdef]; exact lt_min (lt_min hRxF hRxG) hRxH
  have hRxleF : Rx ≤ RxF := by
    rw [hRxdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hRxleG : Rx ≤ RxG := by
    rw [hRxdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hRxleH : Rx ≤ RxH := by rw [hRxdef]; exact min_le_right _ _
  have hψc0 : ContinuousAt ψ 0 :=
    hψc.continuousAt (isOpen_Ioo.mem_nhds ⟨by linarith, hRyF⟩)
  have hφc0 : ContinuousAt φ 0 :=
    hφc.continuousAt (isOpen_Ioo.mem_nhds ⟨by linarith, hRyG⟩)
  have hχc0 : ContinuousAt χ 0 :=
    hχc.continuousAt (isOpen_Ioo.mem_nhds ⟨by linarith, hRyH⟩)
  obtain ⟨δψ, hδψ, hδψle⟩ := exists_abs_le_of_continuousAt_zero hψc0 hψ0 hRxpos
  obtain ⟨δφ, hδφ, hδφle⟩ := exists_abs_le_of_continuousAt_zero hφc0 hφ0 hRxpos
  obtain ⟨δχ, hδχ, hδχle⟩ := exists_abs_le_of_continuousAt_zero hχc0 hχ0 hRxpos
  set Ry : ℝ := min (min δψ (min δφ δχ)) (min (min RyF RyG) RyH) with hRydef
  have hRyleδψ : Ry ≤ δψ := by
    rw [hRydef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hRyleδφ : Ry ≤ δφ := by
    rw [hRydef]
    exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hRyleδχ : Ry ≤ δχ := by
    rw [hRydef]
    exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hRyleF : Ry ≤ RyF := by
    rw [hRydef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hRyleG : Ry ≤ RyG := by
    rw [hRydef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hRyleH : Ry ≤ RyH := by
    rw [hRydef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hRypos : 0 < Ry := by
    rw [hRydef]
    exact lt_min (lt_min hδψ (lt_min hδφ hδχ)) (lt_min (lt_min hRyF hRyG) hRyH)
  refine ⟨Rx, Ry, hRxpos, hRypos, ψ, φ, χ, hψ0, hφ0, hχ0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine hψc.mono ?_
    intro y hy
    rw [Set.mem_Ioo] at hy ⊢
    exact ⟨by linarith [hy.1, hRyleF], by linarith [hy.2, hRyleF]⟩
  · refine hφc.mono ?_
    intro y hy
    rw [Set.mem_Ioo] at hy ⊢
    exact ⟨by linarith [hy.1, hRyleG], by linarith [hy.2, hRyleG]⟩
  · refine hχc.mono ?_
    intro y hy
    rw [Set.mem_Ioo] at hy ⊢
    exact ⟨by linarith [hy.1, hRyleH], by linarith [hy.2, hRyleH]⟩
  · intro y hy
    obtain ⟨h1, h2⟩ := hψroot y (le_trans hy hRyleF)
    obtain ⟨h3, h4⟩ := hφroot y (le_trans hy hRyleG)
    obtain ⟨h5, h6⟩ := hχroot y (le_trans hy hRyleH)
    exact ⟨hδψle y (le_trans hy hRyleδψ), hδφle y (le_trans hy hRyleδφ),
      hδχle y (le_trans hy hRyleδχ), h2, h4, h6⟩
  · intro x y hx hy
    exact ⟨hψsign x y (le_trans hx hRxleF) (le_trans hy hRyleF),
      hφsign x y (le_trans hx hRxleG) (le_trans hy hRyleG),
      hχsign x y (le_trans hx hRxleH) (le_trans hy hRyleH)⟩
  · intro x y hx hy
    exact ⟨hψzero x y (le_trans hx hRxleF) (le_trans hy hRyleF),
      hφzero x y (le_trans hx hRxleG) (le_trans hy hRyleG),
      hχzero x y (le_trans hx hRxleH) (le_trans hy hRyleH)⟩

/-- `max (max a b) c = 0` means that `a ≤ 0`, `b ≤ 0`, `c ≤ 0` and one of the three is zero. -/
private lemma max_max_eq_zero_iff {a b c : ℝ} :
    max (max a b) c = 0 ↔ a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0 ∧ (a = 0 ∨ b = 0 ∨ c = 0) := by
  constructor
  · intro h
    obtain ⟨hab_le, hc, hdisj⟩ := max_eq_zero_iff.mp h
    have ha : a ≤ 0 := le_trans (le_max_left a b) hab_le
    have hb : b ≤ 0 := le_trans (le_max_right a b) hab_le
    refine ⟨ha, hb, hc, ?_⟩
    rcases hdisj with h0 | h0
    · obtain ⟨_, _, hab'⟩ := max_eq_zero_iff.mp h0
      exact hab'.imp id Or.inl
    · exact Or.inr (Or.inr h0)
  · rintro ⟨ha, hb, hc, hdisj⟩
    refine max_eq_zero_iff.mpr ⟨max_le ha hb, hc, ?_⟩
    rcases hdisj with h | h | h
    · exact Or.inl (by rw [h]; exact max_eq_left hb)
    · exact Or.inl (by rw [h]; exact max_eq_right ha)
    · exact Or.inr h

/-! ### The main theorem -/

theorem local_arc_of_max_three_tangent {f₁ f₂ f₃ : ℝ × ℝ → ℝ} (h₁ : ContDiff ℝ 1 f₁) (h₂ : ContDiff ℝ 1 f₂) (h₃ : ContDiff ℝ 1 f₃) {p : ℝ × ℝ} (hp₁ : f₁ p = 0) (hp₂ : f₂ p = 0) (hp₃ : f₃ p = 0) (hd₁ : fderiv ℝ f₁ p ≠ 0) (hd₂ : fderiv ℝ f₂ p ≠ 0) (hd₃ : fderiv ℝ f₃ p ≠ 0) (htan : ∃ r : ℝ × ℝ, fderiv ℝ f₁ p r = 1 ∧ fderiv ℝ f₂ p r = 1 ∧ fderiv ℝ f₃ p r = 1) : ∃ ε : ℝ, 0 < ε ∧ ∃ ρ : ℝ → ℝ × ℝ, ρ 0 = p ∧ ContinuousOn ρ (Set.Ioo (-1 : ℝ) 1) ∧ Set.InjOn ρ (Set.Ioo (-1 : ℝ) 1) ∧ (∀ t ∈ Set.Ioo (-1 : ℝ) 1, max (max (f₁ (ρ t)) (f₂ (ρ t))) (f₃ (ρ t)) = 0) ∧ (∀ q : ℝ × ℝ, max (max (f₁ q) (f₂ q)) (f₃ q) = 0 → ‖q - p‖ < ε → ∃ t ∈ Set.Ioo (-1 : ℝ) 1, ρ t = q) := by
  obtain ⟨r, hr₁, hr₂, hr₃⟩ := htan
  have hrne : r ≠ 0 := by
    intro h
    rw [h, map_zero] at hr₁
    exact one_ne_zero hr₁.symm
  set a : ℝ := r.1 with hadef
  set b : ℝ := r.2 with hbdef
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    simp only [not_or, not_ne_iff] at h
    exact hrne (Prod.ext h.1 h.2)
  set s : ℝ := a ^ 2 + b ^ 2 with hsdef
  have hs : 0 < s := by
    rw [hsdef]
    rcases hab with h | h
    · have := sq_pos_of_ne_zero h; nlinarith [sq_nonneg b]
    · have := sq_pos_of_ne_zero h; nlinarith [sq_nonneg a]
  have hsne : s ≠ 0 := ne_of_gt hs
  -- the linear map `z ↦ (a z₁ + b z₂, b z₁ - a z₂)` sends `(1,0)` to `r` and squares to `s · id`
  set M : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    ((a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
      (b • ContinuousLinearMap.fst ℝ ℝ ℝ - a • ContinuousLinearMap.snd ℝ ℝ ℝ)) with hMdef
  have hMapply : ∀ z : ℝ × ℝ, M z = (a * z.1 + b * z.2, b * z.1 - a * z.2) := by
    intro z
    rw [hMdef, ContinuousLinearMap.prod_apply]
    simp
  have hM10 : M (1, 0) = r := by
    rw [hMapply, hadef, hbdef]
    simp
  have hMM : ∀ z : ℝ × ℝ, M (M z) = s • z := by
    intro z
    rw [hMapply, hMapply, hsdef]
    ext <;> simp <;> ring
  -- the straightened functions
  set F₁ : ℝ × ℝ → ℝ := fun z => f₁ (p + M z) with hF₁def
  set F₂ : ℝ × ℝ → ℝ := fun z => f₂ (p + M z) with hF₂def
  set F₃ : ℝ × ℝ → ℝ := fun z => f₃ (p + M z) with hF₃def
  have hF₁cd : ContDiff ℝ 1 F₁ := by rw [hF₁def]; fun_prop
  have hF₂cd : ContDiff ℝ 1 F₂ := by rw [hF₂def]; fun_prop
  have hF₃cd : ContDiff ℝ 1 F₃ := by rw [hF₃def]; fun_prop
  have hF₁0 : F₁ 0 = 0 := by rw [hF₁def]; simp [hp₁]
  have hF₂0 : F₂ 0 = 0 := by rw [hF₂def]; simp [hp₂]
  have hF₃0 : F₃ 0 = 0 := by rw [hF₃def]; simp [hp₃]
  have hder₁ : fderiv ℝ F₁ 0 = (fderiv ℝ f₁ p).comp M := by
    rw [hF₁def]; exact fderiv_comp_const_add_linear f₁ h₁ p M
  have hder₂ : fderiv ℝ F₂ 0 = (fderiv ℝ f₂ p).comp M := by
    rw [hF₂def]; exact fderiv_comp_const_add_linear f₂ h₂ p M
  have hder₃ : fderiv ℝ F₃ 0 = (fderiv ℝ f₃ p).comp M := by
    rw [hF₃def]; exact fderiv_comp_const_add_linear f₃ h₃ p M
  have ha₁ : 0 < (fderiv ℝ F₁ 0) (1, 0) := by
    rw [hder₁, ContinuousLinearMap.comp_apply, hM10, hr₁]; norm_num
  have ha₂ : 0 < (fderiv ℝ F₂ 0) (1, 0) := by
    rw [hder₂, ContinuousLinearMap.comp_apply, hM10, hr₂]; norm_num
  have ha₃ : 0 < (fderiv ℝ F₃ 0) (1, 0) := by
    rw [hder₃, ContinuousLinearMap.comp_apply, hM10, hr₃]; norm_num
  obtain ⟨Rx, Ry, hRx, hRy, ψ, φ, χ, hψ0, hφ0, hχ0, hψc, hφc, hχc, hroot, hsign, hzero⟩ :=
    exists_root_triple hF₁cd hF₂cd hF₃cd hF₁0 hF₂0 hF₃0 ha₁ ha₂ ha₃
  -- the minimum of the three graphs, and the parametrisation
  set ψm : ℝ → ℝ := fun y => min (min (ψ y) (φ y)) (χ y) with hψmdef
  set ρ : ℝ → ℝ × ℝ := fun t => p + M (ψm (Ry * t), Ry * t) with hρdef
  set C : ℝ := ‖M‖ / s with hCdef
  have hCnn : 0 ≤ C := by rw [hCdef]; positivity
  have hRpos : 0 < min Rx Ry := lt_min hRx hRy
  set ε : ℝ := min Rx Ry / (2 * (C + 1)) with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]; exact div_pos hRpos (by linarith)
  -- the key numerical estimate
  have hCε : C * ε < min Rx Ry := by
    have hfrac : C / (2 * (C + 1)) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 * (C + 1))]
      linarith [hCnn]
    calc C * ε = C * (min Rx Ry / (2 * (C + 1))) := by rw [hεdef]
      _ = (C / (2 * (C + 1))) * min Rx Ry := by ring
      _ ≤ (1 / 2) * min Rx Ry := mul_le_mul_of_nonneg_right hfrac hRpos.le
      _ < min Rx Ry := by linarith
  refine ⟨ε, hεpos, ρ, ?_, ?_, ?_, ?_, ?_⟩
  · -- `ρ 0 = p`
    show p + M (ψm (Ry * 0), Ry * 0) = p
    have h0 : (ψm (Ry * 0), Ry * 0) = (0 : ℝ × ℝ) := by
      rw [hψmdef]
      simp [hψ0, hφ0, hχ0]
    rw [h0, map_zero, add_zero]
  · -- continuity
    show ContinuousOn (fun t : ℝ => p + M (ψm (Ry * t), Ry * t)) (Set.Ioo (-1 : ℝ) 1)
    have hmaps : Set.MapsTo (fun t : ℝ => Ry * t) (Set.Ioo (-1 : ℝ) 1) (Set.Ioo (-Ry) Ry) := by
      intro t ht
      rw [Set.mem_Ioo] at ht ⊢
      exact ⟨by have := mul_lt_mul_of_pos_left ht.1 hRy; simpa using this,
        by have := mul_lt_mul_of_pos_left ht.2 hRy; simpa using this⟩
    have hψ' : ContinuousOn (fun t : ℝ => ψ (Ry * t)) (Set.Ioo (-1 : ℝ) 1) :=
      hψc.comp (continuous_const.mul continuous_id).continuousOn hmaps
    have hφ' : ContinuousOn (fun t : ℝ => φ (Ry * t)) (Set.Ioo (-1 : ℝ) 1) :=
      hφc.comp (continuous_const.mul continuous_id).continuousOn hmaps
    have hχ' : ContinuousOn (fun t : ℝ => χ (Ry * t)) (Set.Ioo (-1 : ℝ) 1) :=
      hχc.comp (continuous_const.mul continuous_id).continuousOn hmaps
    have hψm' : ContinuousOn (fun t : ℝ => ψm (Ry * t)) (Set.Ioo (-1 : ℝ) 1) := by
      intro t ht
      rw [hψmdef]
      exact ((hψ' t ht).min (hφ' t ht)).min (hχ' t ht)
    have hpair : ContinuousOn (fun t : ℝ => (ψm (Ry * t), Ry * t)) (Set.Ioo (-1 : ℝ) 1) :=
      hψm'.prodMk (continuous_const.mul continuous_id).continuousOn
    exact (continuous_const.add M.continuous).comp_continuousOn hpair
  · -- injectivity
    show Set.InjOn (fun t : ℝ => p + M (ψm (Ry * t), Ry * t)) (Set.Ioo (-1 : ℝ) 1)
    intro t₁ ht₁ t₂ ht₂ h
    have hM : M (ψm (Ry * t₁), Ry * t₁) = M (ψm (Ry * t₂), Ry * t₂) := add_left_cancel h
    have hσ : (ψm (Ry * t₁), Ry * t₁) = (ψm (Ry * t₂), Ry * t₂) := by
      have h1 : M (M (ψm (Ry * t₁), Ry * t₁)) = M (M (ψm (Ry * t₂), Ry * t₂)) := by rw [hM]
      rw [hMM, hMM] at h1
      have h2 : s * (ψm (Ry * t₁), Ry * t₁).1 = s * (ψm (Ry * t₂), Ry * t₂).1 :=
        congrArg Prod.fst h1
      have h3 : s * (ψm (Ry * t₁), Ry * t₁).2 = s * (ψm (Ry * t₂), Ry * t₂).2 :=
        congrArg Prod.snd h1
      exact Prod.ext (mul_left_cancel₀ hsne h2) (mul_left_cancel₀ hsne h3)
    have h4 : Ry * t₁ = Ry * t₂ := congrArg Prod.snd hσ
    exact mul_left_cancel₀ (ne_of_gt hRy) h4
  · -- the parametrisation lands in the zero set
    intro t ht
    rw [Set.mem_Ioo] at ht
    set z : ℝ × ℝ := (ψm (Ry * t), Ry * t) with hzdef
    have hxm : z.1 = ψm z.2 := rfl
    have hy_le : |z.2| ≤ Ry := by
      rw [hzdef]
      simp only
      rw [abs_mul, abs_of_pos hRy]
      have h1 : |t| < 1 := abs_lt.mpr ht
      have h2 : Ry * |t| < Ry * 1 := mul_lt_mul_of_pos_left h1 hRy
      linarith
    have hx_le : |z.1| ≤ Rx := by
      rw [hzdef]
      exact abs_min_le (abs_min_le (hroot (Ry * t) hy_le).1 (hroot (Ry * t) hy_le).2.1)
        (hroot (Ry * t) hy_le).2.2.1
    obtain ⟨hFle, hGle, hHle⟩ := hsign z.1 z.2 hx_le hy_le
    obtain ⟨hFeq, hGeq, hHeq⟩ := hzero z.1 z.2 hx_le hy_le
    have hleψ : z.1 ≤ ψ z.2 := by
      rw [hxm, hψmdef]
      show min (min (ψ z.2) (φ z.2)) (χ z.2) ≤ ψ z.2
      exact le_trans (min_le_left _ _) (min_le_left _ _)
    have hleφ : z.1 ≤ φ z.2 := by
      rw [hxm, hψmdef]
      show min (min (ψ z.2) (φ z.2)) (χ z.2) ≤ φ z.2
      exact le_trans (min_le_left _ _) (min_le_right _ _)
    have hleχ : z.1 ≤ χ z.2 := by
      rw [hxm, hψmdef]
      show min (min (ψ z.2) (φ z.2)) (χ z.2) ≤ χ z.2
      exact min_le_right _ _
    have hzeq : z.1 = ψ z.2 ∨ z.1 = φ z.2 ∨ z.1 = χ z.2 := by
      rw [hxm, hψmdef]
      show min (min (ψ z.2) (φ z.2)) (χ z.2) = ψ z.2 ∨
        min (min (ψ z.2) (φ z.2)) (χ z.2) = φ z.2 ∨
        min (min (ψ z.2) (φ z.2)) (χ z.2) = χ z.2
      rcases min_choice (min (ψ z.2) (φ z.2)) (χ z.2) with hm | hm
      · rcases min_choice (ψ z.2) (φ z.2) with hm' | hm'
        · exact Or.inl (by rw [hm, hm'])
        · exact Or.inr (Or.inl (by rw [hm, hm']))
      · exact Or.inr (Or.inr hm)
    have hor : F₁ z = 0 ∨ F₂ z = 0 ∨ F₃ z = 0 := by
      rcases hzeq with h | h | h
      · exact Or.inl (hFeq.mpr h)
      · exact Or.inr (Or.inl (hGeq.mpr h))
      · exact Or.inr (Or.inr (hHeq.mpr h))
    have hm : max (max (F₁ z) (F₂ z)) (F₃ z) = 0 := by
      rw [max_max_eq_zero_iff]
      exact ⟨hFle.mpr hleψ, hGle.mpr hleφ, hHle.mpr hleχ, hor⟩
    show max (max (f₁ (p + M z)) (f₂ (p + M z))) (f₃ (p + M z)) = 0
    exact hm
  · -- every zero near `p` is in the image
    intro q hq hqε
    set z : ℝ × ℝ := (1 / s) • M (q - p) with hzdef
    have hMz : M z = q - p := by
      rw [hzdef, map_smul, hMM, smul_smul]
      rw [div_mul_cancel₀ (1 : ℝ) hsne, one_smul]
    have hqz : p + M z = q := by
      rw [hMz]; abel
    have hle : ‖(1 / s) • M (q - p)‖ ≤ C * ε := by
      have hposinv : (0 : ℝ) < 1 / s := one_div_pos.mpr hs
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hposinv]
      calc (1 / s) * ‖M (q - p)‖
          ≤ (1 / s) * (‖M‖ * ‖q - p‖) :=
            mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm M (q - p)) hposinv.le
        _ ≤ (1 / s) * (‖M‖ * ε) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (le_of_lt hqε) (norm_nonneg M)) hposinv.le
        _ = C * ε := by rw [hCdef]; ring
    have hznorm : ‖z‖ < min Rx Ry := by
      rw [hzdef]; exact lt_of_le_of_lt hle hCε
    have hz1 : |z.1| ≤ ‖z‖ := by rw [Prod.norm_def]; exact le_max_left _ _
    have hz2 : |z.2| ≤ ‖z‖ := by rw [Prod.norm_def]; exact le_max_right _ _
    have hx : |z.1| ≤ Rx := le_trans hz1 (le_of_lt (lt_of_lt_of_le hznorm (min_le_left _ _)))
    have hy : |z.2| ≤ Ry := le_trans hz2 (le_of_lt (lt_of_lt_of_le hznorm (min_le_right _ _)))
    have hz2lt : |z.2| < Ry := lt_of_le_of_lt hz2 (lt_of_lt_of_le hznorm (min_le_right _ _))
    have hF1 : F₁ z = f₁ q := by show f₁ (p + M z) = f₁ q; rw [hqz]
    have hF2 : F₂ z = f₂ q := by show f₂ (p + M z) = f₂ q; rw [hqz]
    have hF3 : F₃ z = f₃ q := by show f₃ (p + M z) = f₃ q; rw [hqz]
    rw [max_max_eq_zero_iff] at hq
    obtain ⟨hf1, hf2, hf3, hdisj⟩ := hq
    have hFz1 : F₁ z ≤ 0 := by rw [hF1]; exact hf1
    have hFz2 : F₂ z ≤ 0 := by rw [hF2]; exact hf2
    have hFz3 : F₃ z ≤ 0 := by rw [hF3]; exact hf3
    have hor : F₁ z = 0 ∨ F₂ z = 0 ∨ F₃ z = 0 := by
      rcases hdisj with h | h | h
      · exact Or.inl (by rw [hF1]; exact h)
      · exact Or.inr (Or.inl (by rw [hF2]; exact h))
      · exact Or.inr (Or.inr (by rw [hF3]; exact h))
    obtain ⟨hFle, hGle, hHle⟩ := hsign z.1 z.2 hx hy
    obtain ⟨hFeq, hGeq, hHeq⟩ := hzero z.1 z.2 hx hy
    have hxψ : z.1 ≤ ψ z.2 := hFle.mp hFz1
    have hxφ : z.1 ≤ φ z.2 := hGle.mp hFz2
    have hxχ : z.1 ≤ χ z.2 := hHle.mp hFz3
    have hzeq : z.1 = ψ z.2 ∨ z.1 = φ z.2 ∨ z.1 = χ z.2 := by
      rcases hor with h | h | h
      · exact Or.inl (hFeq.mp h)
      · exact Or.inr (Or.inl (hGeq.mp h))
      · exact Or.inr (Or.inr (hHeq.mp h))
    have hxm : z.1 = ψm z.2 := by
      rw [hψmdef]
      refine le_antisymm (le_min (le_min hxψ hxφ) hxχ) ?_
      rcases hzeq with h | h | h
      · rw [h]; exact le_trans (min_le_left _ _) (min_le_left _ _)
      · rw [h]; exact le_trans (min_le_left _ _) (min_le_right _ _)
      · rw [h]; exact min_le_right _ _
    refine ⟨z.2 / Ry, ?_, ?_⟩
    · rw [Set.mem_Ioo]
      obtain ⟨hlo, hhi⟩ := abs_lt.mp hz2lt
      exact ⟨by rw [lt_div_iff₀ hRy]; linarith, by rw [div_lt_one hRy]; linarith⟩
    · show p + M (ψm (Ry * (z.2 / Ry)), Ry * (z.2 / Ry)) = q
      rw [mul_div_cancel₀ z.2 (ne_of_gt hRy), ← hxm]
      show p + M z = q
      exact hqz

end Work.Smooth.BoxGeneric.LocalArc
