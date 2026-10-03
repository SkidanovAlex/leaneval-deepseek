import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.basic
import Submission.Work.Horn.gholo
import Submission.Work.L62.cartan
import Submission.Work.L62.lift_section

noncomputable section

open MandelDim Filter Topology Metric Set
open scoped Topology

namespace Work.Horn

variable {f₀ : ℂ → ℂ} {D₀ : Set ℂ}

/-- The pushed-down horn map `g = pushdown Ẽ_{f₀}` (`HornData`'s `g₀`). -/
def hornG (d : ParabData f₀ D₀) : ℂ → ℂ := pushdown d.E

/-- The cylinder domain of the upper component: `{0} ∪ π(B^u)`. -/
def hornDu (Bu : Set ℂ) : Set ℂ := insert 0 (piExp '' Bu)

/-- The cylinder domain of the lower component: `{0} ∪ π(B^ℓ)`. -/
def hornDl (Bl : Set ℂ) : Set ℂ := insert 0 (piExp '' Bl)

/-- The domain of the pushed-down horn map: `{0} ∪ π(B^u ∪ B^ℓ)`. -/
def hornDg (Bu Bl : Set ℂ) : Set ℂ := insert 0 (piExp '' (Bu ∪ Bl))

/-! ## The map `π` and its images -/

theorem isOpenMap_piExp : IsOpenMap piExp := by
  have h1 : piExp = Complex.exp ∘ fun w : ℂ => (2 * (Real.pi : ℂ) * Complex.I) * w := by
    funext w
    rw [MandelDim.piExp, Function.comp_apply]
  rw [h1]
  refine IsOpenMap.comp Complex.isOpenMap_exp ?_
  have hc : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := Complex.two_pi_I_ne_zero
  have h2 : (fun w : ℂ => (2 * (Real.pi : ℂ) * Complex.I) * w)
      = ⇑(Homeomorph.mulLeft₀ (2 * (Real.pi : ℂ) * Complex.I) hc) := by
    funext w
    rw [Homeomorph.coe_mulLeft₀]
  rw [h2]
  exact (Homeomorph.mulLeft₀ _ hc).isOpenMap

theorem isOpen_piExp_image {S : Set ℂ} (hS : IsOpen S) : IsOpen (piExp '' S) := by
  rw [isOpen_iff_mem_nhds]
  rintro ζ ⟨w, hw, rfl⟩
  exact isOpenMap_piExp.image_mem_nhds (hS.mem_nhds hw)

theorem norm_piExp (w : ℂ) : ‖piExp w‖ = Real.exp (-(2 * Real.pi) * w.im) := by
  rw [MandelDim.piExp, Complex.norm_exp]
  congr 1
  rw [Complex.mul_re]
  simp

theorem piExp_exists_of_ne_zero {ζ : ℂ} (hζ : ζ ≠ 0) :
    ∃ w : ℂ, piExp w = ζ :=
  ⟨Complex.log ζ / (2 * Real.pi * Complex.I), Work.Horn.MandelDim.piExp_log_div ζ hζ⟩

/-- The imaginary part of the standard lift `log ζ / (2πi)` of `ζ ≠ 0`. -/
theorem log_div_im (ζ : ℂ) :
    (Complex.log ζ / (2 * (Real.pi : ℂ) * Complex.I)).im
      = -(Real.log ‖ζ‖ / (2 * Real.pi)) := by
  rw [Complex.div_im, Complex.log_re, Complex.log_im]
  have h1 : (2 * (Real.pi : ℂ) * Complex.I).re = 0 := by simp
  have h2 : (2 * (Real.pi : ℂ) * Complex.I).im = 2 * Real.pi := by simp
  have h3 : Complex.normSq ((2 : ℂ) * Real.pi * Complex.I) = (2 * Real.pi) ^ 2 := by
    rw [show ((2 : ℂ) * Real.pi * Complex.I) = ↑(2 * Real.pi) * Complex.I by push_cast; ring]
    rw [Complex.normSq_apply]
    simp
    ring
  rw [h1, h2, h3]
  field_simp
  ring

/-- A point `w` with `π w = ζ`, `ζ ≠ 0` and `‖ζ‖ < exp (-2πη)` lies above the line `Im = η`. -/
theorem im_gt_of_piExp {η : ℝ} {ζ w : ℂ} (hζ : ζ ≠ 0) (hw : piExp w = ζ)
    (h : ‖ζ‖ < Real.exp (-(2 * Real.pi) * η)) : η < w.im := by
  have h2pi : (0:ℝ) < 2 * Real.pi := by positivity
  have hlog : Real.log ‖ζ‖ < -(2 * Real.pi) * η := by
    have hpos : (0:ℝ) < ‖ζ‖ := norm_pos_iff.mpr hζ
    have := Real.log_lt_log hpos h
    rwa [Real.log_exp] at this
  have hlt : Real.log ‖ζ‖ / (2 * Real.pi) < -η := by
    have := div_lt_div_of_pos_right hlog h2pi
    rwa [show (-(2 * Real.pi) * η) / (2 * Real.pi) = -η by field_simp] at this
  have h3 : w.im = (Complex.log ζ / (2 * (Real.pi : ℂ) * Complex.I)).im := by
    obtain ⟨k, hk⟩ := Work.Horn.MandelDim.piExp_eq_iff.mp
      (show piExp w = piExp (Complex.log ζ / (2 * (Real.pi : ℂ) * Complex.I)) from by
        rw [hw]; exact (Work.Horn.MandelDim.piExp_log_div ζ hζ).symm)
    rw [hk]
    simp
  rw [h3, log_div_im]
  linarith

/-! ## The cylinder domains -/

/-- Membership in `{0} ∪ π '' B` for a set `B` containing the upper half-plane `{η < Im ·}`. -/
theorem mem_hornDu_of_norm_lt {Bu : Set ℂ} {η : ℝ} (hup : {w : ℂ | η < w.im} ⊆ Bu)
    {ζ : ℂ} (hζ : ‖ζ‖ < Real.exp (-(2 * Real.pi) * η)) : ζ ∈ hornDu Bu := by
  rcases eq_or_ne ζ 0 with rfl | hne
  · exact Set.mem_insert _ _
  · obtain ⟨w, hw⟩ := piExp_exists_of_ne_zero hne
    exact Set.mem_insert_of_mem _ ⟨w, hup (im_gt_of_piExp hne hw hζ), hw⟩

theorem hornDu_eq_ball_union {Bu : Set ℂ} {η : ℝ} (hup : {w : ℂ | η < w.im} ⊆ Bu) :
    hornDu Bu = ball 0 (Real.exp (-(2 * Real.pi) * η)) ∪ piExp '' Bu := by
  ext ζ
  constructor
  · intro hζ
    rcases Set.mem_insert_iff.mp hζ with rfl | h
    · exact Or.inl (mem_ball_self (Real.exp_pos _))
    · exact Or.inr h
  · rintro (h | h)
    · exact mem_hornDu_of_norm_lt hup (by rwa [mem_ball_zero_iff] at h)
    · exact Set.mem_insert_of_mem _ h

theorem isOpen_hornDu {Bu : Set ℂ} {η : ℝ} (hBuO : IsOpen Bu)
    (hup : {w : ℂ | η < w.im} ⊆ Bu) : IsOpen (hornDu Bu) := by
  rw [hornDu_eq_ball_union hup]
  exact isOpen_ball.union (isOpen_piExp_image hBuO)

/-- The cylinder domain of the lower component in the *inverted chart* `u = e^{-2πiw}`:
`{0} ∪ e^{-2πi}(B^ℓ) = {0} ∪ π '' (-B^ℓ)`.  This is a bounded neighbourhood of `0`
(the lower end of `B^ℓ`, i.e. `ζ = ∞` in the `π`-chart, becomes `u = 0`). -/
def hornDl' (Bl : Set ℂ) : Set ℂ := insert 0 (piExp '' {w : ℂ | -w ∈ Bl})

theorem mem_hornDl'_of_norm_lt {Bl : Set ℂ} {η : ℝ} (hlo : {w : ℂ | w.im < -η} ⊆ Bl)
    {ζ : ℂ} (hζ : ‖ζ‖ < Real.exp (-(2 * Real.pi) * η)) : ζ ∈ hornDl' Bl := by
  have h2pi : (0:ℝ) < 2 * Real.pi := by positivity
  rcases eq_or_ne ζ 0 with rfl | hne
  · exact Set.mem_insert _ _
  · have hlog : Real.log ‖ζ‖ < -(2 * Real.pi) * η := by
      have hpos : (0:ℝ) < ‖ζ‖ := norm_pos_iff.mpr hne
      have := Real.log_lt_log hpos hζ
      rwa [Real.log_exp] at this
    have hlt : Real.log ‖ζ‖ / (2 * Real.pi) < -η := by
      have := div_lt_div_of_pos_right hlog h2pi
      rwa [show (-(2 * Real.pi) * η) / (2 * Real.pi) = -η by field_simp] at this
    refine Set.mem_insert_of_mem _ ⟨Complex.log ζ / (2 * (Real.pi : ℂ) * Complex.I), ?_, ?_⟩
    · refine hlo ?_
      have hthis : (-(Complex.log ζ / (2 * (Real.pi : ℂ) * Complex.I))).im
          = Real.log ‖ζ‖ / (2 * Real.pi) := by
        rw [Complex.neg_im, log_div_im]; ring
      show (-(Complex.log ζ / (2 * (Real.pi : ℂ) * Complex.I))).im < -η
      rw [hthis]; linarith
    · exact Work.Horn.MandelDim.piExp_log_div ζ hne

theorem hornDl'_eq_ball_union {Bl : Set ℂ} {η : ℝ} (hlo : {w : ℂ | w.im < -η} ⊆ Bl) :
    hornDl' Bl = ball 0 (Real.exp (-(2 * Real.pi) * η)) ∪ piExp '' {w : ℂ | -w ∈ Bl} := by
  ext ζ
  constructor
  · intro hζ
    rcases Set.mem_insert_iff.mp hζ with rfl | h
    · exact Or.inl (mem_ball_self (Real.exp_pos _))
    · exact Or.inr h
  · rintro (h | h)
    · exact mem_hornDl'_of_norm_lt hlo (by rwa [mem_ball_zero_iff] at h)
    · exact Set.mem_insert_of_mem _ h

theorem isOpen_setOf_neg_mem {Bl : Set ℂ} (hBl : IsOpen Bl) :
    IsOpen {w : ℂ | -w ∈ Bl} :=
  hBl.preimage continuous_neg

theorem isOpen_hornDl' {Bl : Set ℂ} {η : ℝ} (hBlO : IsOpen Bl)
    (hlo : {w : ℂ | w.im < -η} ⊆ Bl) : IsOpen (hornDl' Bl) := by
  rw [hornDl'_eq_ball_union hlo]
  exact isOpen_ball.union (isOpen_piExp_image (isOpen_setOf_neg_mem hBlO))


/-! ## `g` and its basic properties -/

theorem hornG_zero (d : ParabData f₀ D₀) : hornG d 0 = 0 := by
  simp [hornG, pushdown]

theorem hornG_piExp (d : ParabData f₀ D₀) {Bu Bl : Set ℂ}
    (htBu : MandelDim.IsTInvariant Bu) (htBl : MandelDim.IsTInvariant Bl)
    (hsub : Bu ∪ Bl ⊆ d.DE) {w : ℂ} (hw : w ∈ Bu ∪ Bl) :
    hornG d (piExp w) = piExp (d.E w) := by
  have hT : MandelDim.IsTInvariant (Bu ∪ Bl) := fun v => by
    constructor
    · rintro (hv | hv)
      · exact Or.inl ((htBu v).mp hv)
      · exact Or.inr ((htBl v).mp hv)
    · rintro (hv | hv)
      · exact Or.inl ((htBu v).mpr hv)
      · exact Or.inr ((htBl v).mpr hv)
  exact Work.Horn.MandelDim.pushdown_piExp hT
    (fun v hv hv1 => Work.Horn.MandelDim.ParabData.E_add_one d (hsub hv) (hsub hv1)) hw

/-- `g = pushdown Ẽ` is holomorphic on `{0} ∪ π(B^u ∪ B^ℓ)`. -/
theorem hornG_differentiableOn (d : ParabData f₀ D₀) {η : ℝ} {Bu Bl : Set ℂ}
    (hBuO : IsOpen Bu) (hBlO : IsOpen Bl)
    (htBu : MandelDim.IsTInvariant Bu) (htBl : MandelDim.IsTInvariant Bl)
    (hsub : Bu ∪ Bl ⊆ d.DE) (hup : {w : ℂ | η < w.im} ⊆ Bu) (hlo : {w : ℂ | w.im < -η} ⊆ Bl) :
    DifferentiableOn ℂ (hornG d) (hornDg Bu Bl) :=
  pushdown_E_differentiableOn d η Bu Bl hBuO hBlO htBu htBl hsub hup hlo

theorem deriv_hornG_zero (d : ParabData f₀ D₀) : deriv (hornG d) 0 = 1 :=
  Work.Horn.MandelDim.deriv_pushdown_E d

theorem differenceOn_hornG (d : ParabData f₀ D₀) {η : ℝ} {Bu Bl : Set ℂ}
    (hBuO : IsOpen Bu) (hBlO : IsOpen Bl)
    (htBu : MandelDim.IsTInvariant Bu) (htBl : MandelDim.IsTInvariant Bl)
    (hsub : Bu ∪ Bl ⊆ d.DE) (hup : {w : ℂ | η < w.im} ⊆ Bu) (hlo : {w : ℂ | w.im < -η} ⊆ Bl) :
    DifferentiableOn ℂ (hornG d) (hornDg Bu Bl) :=
  hornG_differentiableOn d hBuO hBlO htBu htBl hsub hup hlo

/-! ## Surjectivity of `g` on the two cylinder domains -/

theorem surjOn_hornG_hornDu (d : ParabData f₀ D₀) {Bu Bl : Set ℂ}
    (htBu : MandelDim.IsTInvariant Bu) (htBl : MandelDim.IsTInvariant Bl)
    (hsub : Bu ∪ Bl ⊆ d.DE)
    (hinf : ∀ y : ℂ, (piExp '' {w : ℂ | w ∈ Bu ∧ d.E w = y}).Infinite) :
    hornG d '' hornDu Bu = univ := by
  ext ζ
  simp only [mem_univ, iff_true]
  rcases eq_or_ne ζ 0 with rfl | hne
  · exact ⟨0, Or.inl rfl, hornG_zero d⟩
  · obtain ⟨u, hu⟩ := (hinf (Complex.log ζ / (2 * Real.pi * Complex.I))).nonempty
    obtain ⟨w, ⟨hw, hEw⟩, -⟩ := hu
    refine ⟨piExp w, Or.inr ⟨w, hw, rfl⟩, ?_⟩
    rw [hornG_piExp d htBu htBl hsub (Or.inl hw), hEw]
    exact Work.Horn.MandelDim.piExp_log_div ζ hne

theorem surjOn_hornG_hornDl (d : ParabData f₀ D₀) {Bu Bl : Set ℂ}
    (htBu : MandelDim.IsTInvariant Bu) (htBl : MandelDim.IsTInvariant Bl)
    (hsub : Bu ∪ Bl ⊆ d.DE)
    (hinf : ∀ y : ℂ, (piExp '' {w : ℂ | w ∈ Bl ∧ d.E w = y}).Infinite) :
    hornG d '' hornDl Bl = univ := by
  ext ζ
  simp only [mem_univ, iff_true]
  rcases eq_or_ne ζ 0 with rfl | hne
  · exact ⟨0, Or.inl rfl, hornG_zero d⟩
  · obtain ⟨u, hu⟩ := (hinf (Complex.log ζ / (2 * Real.pi * Complex.I))).nonempty
    obtain ⟨w, ⟨hw, hEw⟩, -⟩ := hu
    refine ⟨piExp w, Or.inr ⟨w, hw, rfl⟩, ?_⟩
    rw [hornG_piExp d htBu htBl hsub (Or.inr hw), hEw]
    exact Work.Horn.MandelDim.piExp_log_div ζ hne

/-! ## The critical-point criterion -/

private theorem isOpen_parabolicBasin {f : ℂ → ℂ} {D : Set ℂ} : IsOpen (ParabolicBasin f D) := by
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨U, hU, hUd, hUt⟩
  obtain ⟨V, hVU, hVopen, hzV⟩ := _root_.mem_nhds_iff.mp hU
  refine mem_of_superset (hVopen.mem_nhds hzV) ?_
  intro z' hz'
  exact ⟨V, hVopen.mem_nhds hz', fun n => fun z hz => hUd n (hVU hz), hUt.mono hVU⟩

theorem differentiableAt_E (d : ParabData f₀ D₀) {w : ℂ} (hw : w ∈ d.DE) :
    DifferentiableAt ℂ d.E w := by
  rw [Work.Horn.MandelDim.ParabData.mem_DE] at hw
  exact (d.Φ_holo.differentiableAt (isOpen_parabolicBasin.mem_nhds hw.2)).comp w
    (d.φ_holo.differentiableAt (d.Dφ_open.mem_nhds hw.1))

theorem differentiableAt_piExp (w : ℂ) : DifferentiableAt ℂ piExp w := by
  have h : piExp = fun z : ℂ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z) := rfl
  rw [h]
  exact ((Complex.hasDerivAt_exp _).differentiableAt).comp w
    ((differentiableAt_const _).mul differentiableAt_id)

theorem deriv_piExp (w : ℂ) :
    deriv piExp w = (2 * (Real.pi : ℂ) * Complex.I) * piExp w := by
  have h : piExp = fun z : ℂ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z) := rfl
  rw [h]
  have h1 : HasDerivAt (fun z : ℂ => (2 * (Real.pi : ℂ) * Complex.I) * z)
      (2 * (Real.pi : ℂ) * Complex.I) w := by
    simpa using (hasDerivAt_id w).const_mul (2 * (Real.pi : ℂ) * Complex.I)
  have h2 : HasDerivAt (fun z : ℂ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z))
      (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * w) * (2 * (Real.pi : ℂ) * Complex.I)) w := by
    have := (Complex.hasDerivAt_exp ((2 * (Real.pi : ℂ) * Complex.I) * w)).comp w h1
    simpa [Function.comp_def] using this
  rw [h2.deriv]
  ring

theorem deriv_hornG_piExp_eq_zero_iff (d : ParabData f₀ D₀) {η : ℝ} {Bu Bl : Set ℂ}
    (hBuO : IsOpen Bu) (hBlO : IsOpen Bl)
    (htBu : MandelDim.IsTInvariant Bu) (htBl : MandelDim.IsTInvariant Bl)
    (hsub : Bu ∪ Bl ⊆ d.DE) (hup : {w : ℂ | η < w.im} ⊆ Bu) (hlo : {w : ℂ | w.im < -η} ⊆ Bl)
    {w : ℂ} (hw : w ∈ Bu ∪ Bl) :
    deriv (hornG d) (piExp w) = 0 ↔ deriv d.E w = 0 := by
  have hGhol : DifferentiableOn ℂ (hornG d) (hornDg Bu Bl) :=
    hornG_differentiableOn d hBuO hBlO htBu htBl hsub hup hlo
  have hGat : DifferentiableAt ℂ (hornG d) (piExp w) :=
    (hGhol.mono (Set.subset_insert _ _)).differentiableAt
      ((isOpen_piExp_image (hBuO.union hBlO)).mem_nhds ⟨w, hw, rfl⟩)
  have hEat : DifferentiableAt ℂ d.E w := differentiableAt_E d (hsub hw)
  have hpi : DifferentiableAt ℂ piExp w := differentiableAt_piExp w
  have heq : hornG d ∘ piExp =ᶠ[𝓝 w] piExp ∘ d.E := by
    refine Filter.eventually_of_mem ((hBuO.union hBlO).mem_nhds hw) ?_
    intro u hu
    exact hornG_piExp d htBu htBl hsub hu
  have h1 : deriv (hornG d ∘ piExp) w
      = deriv (hornG d) (piExp w) * deriv piExp w :=
    deriv_comp w hGat hpi
  have h2 : deriv (piExp ∘ d.E) w = deriv piExp (d.E w) * deriv d.E w :=
    deriv_comp w (differentiableAt_piExp (d.E w)) hEat
  have hEq : deriv (hornG d) (piExp w) * deriv piExp w
      = deriv piExp (d.E w) * deriv d.E w := by
    rw [← h1, heq.deriv_eq, h2]
  rw [deriv_piExp w, deriv_piExp (d.E w)] at hEq
  have hne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := Complex.two_pi_I_ne_zero
  have hne1 : piExp w ≠ 0 := Work.Horn.MandelDim.piExp_ne_zero w
  have hne2 : piExp (d.E w) ≠ 0 := Work.Horn.MandelDim.piExp_ne_zero _
  constructor
  · intro hA
    have h0 : ((2 * (Real.pi : ℂ) * Complex.I) * piExp (d.E w)) * deriv d.E w = 0 := by
      rw [← hEq, hA]; ring
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h (mul_ne_zero hne hne2)
    · exact h
  · intro hB
    have h0 : deriv (hornG d) (piExp w) * ((2 * (Real.pi : ℂ) * Complex.I) * piExp w) = 0 := by
      rw [hEq, hB]; ring
    rcases mul_eq_zero.mp h0 with h | h
    · exact h
    · exact absurd h (mul_ne_zero hne hne1)

/-! ## The lower-end limit in `ε`-form -/

theorem tendsto_lowerEnd_iff {f : ℂ → ℂ} {cl : ℂ} :
    Filter.Tendsto f MandelDim.lowerEnd (𝓝 cl) ↔
      ∀ ε > 0, ∃ R : ℝ, ∀ w : ℂ, w.im < R → ‖f w - cl‖ < ε := by
  constructor
  · intro h ε hε
    have h1 : ∀ᶠ w in MandelDim.lowerEnd, dist (f w) cl < ε :=
      h.eventually (Metric.ball_mem_nhds cl hε)
    rw [MandelDim.lowerEnd, Filter.eventually_iff, Filter.mem_comap] at h1
    obtain ⟨t, ht, hts⟩ := h1
    rw [Filter.mem_atBot_sets] at ht
    obtain ⟨R, hR⟩ := ht
    exact ⟨R, fun w hw => by
      have h2 : w.im ∈ t := hR w.im hw.le
      have h3 : w ∈ Complex.im ⁻¹' t := h2
      simpa [dist_eq_norm] using hts h3⟩
  · intro h
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨R, hR⟩ := h ε hε
    rw [MandelDim.lowerEnd, Filter.eventually_iff, Filter.mem_comap]
    refine ⟨Set.Iio R, ?_, ?_⟩
    · rw [Filter.mem_atBot_sets]
      exact ⟨R - 1, fun b hb => by simp only [Set.mem_Iio]; linarith⟩
    · intro w hw
      simpa [dist_eq_norm] using hR w (by simpa using hw)
/-! ## The equivariance of a section at a `T`-invariant lower end

`F := E - id - cl` is `1`-periodic (from `T`-equivariance of `E`) and decays at the deep end;
Cauchy's estimate upgrades the decay to a bound `‖deriv F‖ < 1/2` on a deep half-plane.  For an
open convex half-plane `{Im < R₀} ⊆ D` this makes `F` a contraction, and the error
`g w = s (w+1) - s w - 1 = F (s w) - F (s (w+1)) = F (s w) - F (s w + g w)` then satisfies
`‖g w‖ ≤ (1/2) ‖g w‖` at the deep end; so `g` vanishes on a nonempty open set and the identity
theorem finishes. -/

theorem section_add_one_eq {E : ℂ → ℂ} {D : Set ℂ} {s : ℂ → ℂ} {cl : ℂ} {η : ℝ}
    (hη : 0 < η) (hDo : IsOpen D) (hDc : IsPreconnected D)
    (hlow : {w : ℂ | w.im < -η} ⊆ D)
    (hT : MandelDim.IsTInvariant D)
    (hEhol : DifferentiableOn ℂ E D)
    (hEeq : ∀ w ∈ D, w + 1 ∈ D → E (w + 1) = E w + 1)
    (hcl : ∀ ε > 0, ∃ R : ℝ, ∀ u ∈ D, u.im < R → ‖E u - u - cl‖ < ε)
    (hs : DifferentiableOn ℂ s D) (hsm : ∀ w ∈ D, s w ∈ D) (hEs : ∀ w ∈ D, E (s w) = w)
    (hasymp : ∀ ε > 0, ∃ R : ℝ, ∀ w ∈ D, w.im < R → ‖s w - (w - cl)‖ < ε) :
    ∀ w ∈ D, s (w + 1) = s w + 1 := by
  obtain ⟨RF, hRF⟩ := hcl (1 / 4) (by norm_num)
  obtain ⟨RS, hRS⟩ := hasymp (1 / 4) (by norm_num)
  set F : ℂ → ℂ := fun u => E u - u - cl with hFdef
  set g : ℂ → ℂ := fun w => s (w + 1) - s w - 1 with hgdef
  set R₀ : ℝ := min (RF - 2) (-η - 1) with hR₀def
  set RT : ℝ := min (RS - 1) (R₀ - |cl.im| - 2) with hRTdef
  have hR₀_le1 : R₀ ≤ RF - 2 := by rw [hR₀def]; exact min_le_left _ _
  have hR₀_le2 : R₀ ≤ -η - 1 := by rw [hR₀def]; exact min_le_right _ _
  have hRT_le1 : RT ≤ RS - 1 := by rw [hRTdef]; exact min_le_left _ _
  have hRT_le2 : RT ≤ R₀ - |cl.im| - 2 := by rw [hRTdef]; exact min_le_right _ _
  have hFhol : DifferentiableOn ℂ F D := (hEhol.sub differentiableOn_id).sub_const cl
  have hg_hol : DifferentiableOn ℂ g D := by
    have h1 : DifferentiableOn ℂ (fun w : ℂ => s (w + 1)) D :=
      hs.comp (differentiableOn_id.add_const 1) (fun w hw => (hT w).mp hw)
    exact (h1.sub hs).sub_const 1
  have hFper : ∀ u ∈ D, u + 1 ∈ D → F (u + 1) = F u := by
    intro u hu hu1
    rw [hFdef]
    simp only
    rw [hEeq u hu hu1]
    ring
  have hderiv : ∀ u : ℂ, u.im < R₀ → u ∈ D → ‖deriv F u‖ < 1 / 2 := by
    intro u hu huD
    have h1 : ∀ z : ℂ, ‖z - u‖ ≤ 1 → z.im < R₀ + 1 := by
      intro z hz
      have h2 : |(z - u).im| ≤ ‖z - u‖ := Complex.abs_im_le_norm _
      have h3 : (z - u).im = z.im - u.im := by simp
      have h4 := (abs_le.mp h2).2
      linarith
    have hclosed : Metric.closedBall u 1 ⊆ D := by
      intro z hz
      have hz1 : ‖z - u‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
      have h5 := h1 z hz1
      refine hlow ?_
      show z.im < -η
      linarith
    have hdcl : DiffContOnCl ℂ F (Metric.ball u 1) :=
      ⟨hFhol.mono (fun z hz => hclosed (Metric.ball_subset_closedBall hz)),
       hFhol.continuousOn.mono (fun z hz => hclosed (Metric.closure_ball_subset_closedBall hz))⟩
    have hb : ∀ z ∈ Metric.sphere u 1, ‖F z‖ ≤ 1 / 4 := by
      intro z hz
      have hz1 : ‖z - u‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
      have h5 := h1 z (le_of_eq hz1)
      have hzD : z ∈ D := hclosed (Metric.sphere_subset_closedBall hz)
      have hzlt : z.im < RF := by linarith
      exact le_of_lt (hRF z hzD hzlt)
    have hmain := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (f := F) (c := u)
      (R := 1) (C := 1 / 4) one_pos hdcl hb
    rw [div_one] at hmain
    linarith
  have hconv : Convex ℝ {u : ℂ | u.im < R₀} := by
    have h : {u : ℂ | u.im < R₀} = (Complex.imCLM : ℂ →ₗ[ℝ] ℝ) ⁻¹' Set.Iio R₀ := by
      ext u; rfl
    rw [h]
    exact (convex_Iio R₀).linear_preimage _
  have hsubD : {u : ℂ | u.im < R₀} ⊆ D := by
    intro u hu
    have hu' : u.im < R₀ := hu
    refine hlow ?_
    show u.im < -η
    linarith
  have hdeep : ∀ w ∈ D, w.im < RT → g w = 0 := by
    intro w hwD hwRT
    have hw1 : w + 1 ∈ D := (hT w).mp hwD
    have hsw : ‖s w - (w - cl)‖ < 1 / 4 := hRS w hwD (by linarith)
    have hsw1 : ‖s (w + 1) - ((w + 1) - cl)‖ < 1 / 4 := by
      refine hRS (w + 1) hw1 ?_
      have h1 : (w + 1).im = w.im := by simp
      linarith
    have hA : (s w).im < R₀ := by
      have h2 : |(s w - (w - cl)).im| ≤ ‖s w - (w - cl)‖ := Complex.abs_im_le_norm _
      have h4 := (abs_le.mp h2).2
      have h3 : (s w - (w - cl)).im = (s w).im - (w - cl).im := by simp
      have h5 : (w - cl).im = w.im - cl.im := by simp
      have h6 : -(cl.im) ≤ |cl.im| := neg_le_abs _
      linarith
    have hA' : (s (w + 1) - 1).im < R₀ := by
      have h2 : |(s (w + 1) - ((w + 1) - cl)).im| ≤ ‖s (w + 1) - ((w + 1) - cl)‖ :=
        Complex.abs_im_le_norm _
      have h4 := (abs_le.mp h2).2
      have h3 : (s (w + 1) - ((w + 1) - cl)).im
          = (s (w + 1)).im - ((w + 1) - cl).im := by simp
      have h5 : ((w + 1) - cl).im = w.im - cl.im := by simp
      have h6 : -(cl.im) ≤ |cl.im| := neg_le_abs _
      have h7 : (s (w + 1) - 1).im = (s (w + 1)).im := by simp
      linarith
    have h_eq : s (w + 1) = s w + g w + 1 := by rw [hgdef]; ring
    have hmem1 : s w ∈ {u : ℂ | u.im < R₀} := hA
    have hmem2 : s w + g w ∈ {u : ℂ | u.im < R₀} := by
      have hh : s w + g w = s (w + 1) - 1 := by rw [h_eq]; ring
      rw [Set.mem_setOf_eq, hh]
      exact hA'
    have hdiff : ∀ z ∈ {u : ℂ | u.im < R₀}, DifferentiableAt ℂ F z :=
      fun z hz => hFhol.differentiableAt (hDo.mem_nhds (hsubD hz))
    have hbound : ∀ z ∈ {u : ℂ | u.im < R₀}, ‖deriv F z‖ ≤ 1 / 2 :=
      fun z hz => le_of_lt (hderiv z (by simpa using hz) (hsubD hz))
    have hmv := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound hconv hmem1 hmem2
    have hper : F (s (w + 1)) = F (s w + g w) := by
      rw [h_eq]
      have ha : s w + g w ∈ D := by
        have hh : s w + g w = s (w + 1) - 1 := by rw [h_eq]; ring
        rw [hh]
        exact (hT (s (w + 1) - 1)).mpr (by simpa using hsm (w + 1) hw1)
      have hb : s w + g w + 1 ∈ D := (hT (s w + g w)).mp ha
      rw [hFper (s w + g w) ha hb]
    have hval : g w = F (s w) - F (s (w + 1)) := by
      rw [hFdef, hgdef]
      simp only
      rw [hEs w hwD, hEs (w + 1) hw1]
      ring
    have hmv' : ‖F (s w + g w) - F (s w)‖ ≤ (1 / 2) * ‖g w‖ := by
      have h2 := hmv
      rw [show (s w + g w) - s w = g w by ring] at h2
      exact h2
    have hmain : ‖g w‖ ≤ (1 / 2) * ‖g w‖ := by
      calc ‖g w‖ = ‖F (s w) - F (s (w + 1))‖ := by rw [hval]
        _ = ‖F (s w) - F (s w + g w)‖ := by rw [hper]
        _ = ‖F (s w + g w) - F (s w)‖ := norm_sub_rev _ _
        _ ≤ (1 / 2) * ‖g w‖ := hmv'
    have hz : ‖g w‖ = 0 := by
      have := norm_nonneg (g w)
      linarith
    exact norm_eq_zero.mp hz
  intro w hwD
  set T₀ : ℝ := min RT (-η - 1) - 2 with hT₀def
  set w₀ : ℂ := Complex.I * ((T₀ : ℝ) : ℂ) with hw₀def
  have hT₀_le : T₀ ≤ RT - 2 := by
    have h1 : T₀ ≤ min RT (-η - 1) - 2 := le_of_eq hT₀def
    have h2 : min RT (-η - 1) ≤ RT := min_le_left _ _
    linarith
  have hT₀_lt : T₀ < RT := by linarith
  have hT₀_deep : T₀ < -η := by
    have h1 : T₀ ≤ min RT (-η - 1) - 2 := le_of_eq hT₀def
    have h2 : min RT (-η - 1) ≤ -η - 1 := min_le_right _ _
    linarith
  have hw₀im : w₀.im = T₀ := by
    rw [hw₀def]
    simp [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  have hpt : w₀ ∈ D := by
    refine hlow ?_
    show w₀.im < -η
    rw [hw₀im]
    exact hT₀_deep
  have key : g =ᶠ[𝓝 w₀] 0 := by
    filter_upwards [hDo.mem_nhds hpt,
      Metric.ball_mem_nhds w₀ (by norm_num : (0:ℝ) < 1/2)] with z hzD hzball
    refine hdeep z hzD ?_
    have h1 : ‖z - w₀‖ < 1 / 2 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hzball
    have h2 : (z - w₀).im ≤ ‖z - w₀‖ := (abs_le.mp (Complex.abs_im_le_norm _)).2
    have h3 : z.im = w₀.im + (z - w₀).im := by
      have h : z = w₀ + (z - w₀) := by ring
      calc z.im = (z - w₀ + w₀).im := by rw [sub_add_cancel]
        _ = (z - w₀).im + w₀.im := Complex.add_im _ _
        _ = w₀.im + (z - w₀).im := by ring
    rw [h3, hw₀im]
    have h4 : T₀ + (z - w₀).im < RT := by linarith [hT₀_le]
    linarith
  have hEq : Set.EqOn g 0 D :=
    AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (hg_hol.analyticOnNhd hDo) hDc hpt key
  have h0 : g w = 0 := hEq hwD
  rw [hgdef] at h0
  simp only at h0
  linear_combination h0


/-! ## The descent to the inverted chart `u = e^{-2πiw}`

A `T`-equivariant section `s` of `E` over `D` (as produced by `section_add_one_eq`) descends to a
self-map of the bounded cylinder domain `hornDl' D = {0} ∪ e^{-2πi}D`. -/

/-- The equivariance iterated over `ℤ`. -/
theorem section_add_int {D : Set ℂ} {s : ℂ → ℂ} (hT : MandelDim.IsTInvariant D)
    (heq : ∀ w ∈ D, s (w + 1) = s w + 1) :
    ∀ {w : ℂ}, w ∈ D → ∀ k : ℤ, s (w + k) = s w + k :=
  fun {w} hw k => Work.Horn.MandelDim.E_add_int hT (fun u hu _ => heq u hu) hw k

/-- The `u`-chart (`u = e^{-2πiw}`) representative of a function `f` of the `w`-plane. -/
def hornS (f : ℂ → ℂ) : ℂ → ℂ :=
  fun u => if u = 0 then 0 else piExp (-(f (-(Complex.log u / (2 * Real.pi * Complex.I)))))

theorem hornS_zero (f : ℂ → ℂ) : hornS f 0 = 0 := by
  simp [hornS]

/-- Well-definedness of the descent: the value at `piExp (-v)` does not depend on the lift. -/
theorem hornS_piExp {s : ℂ → ℂ} {D : Set ℂ} (hT : MandelDim.IsTInvariant D)
    (heq : ∀ w ∈ D, s (w + 1) = s w + 1) {v : ℂ} (hv : v ∈ D) :
    hornS s (piExp (-v)) = piExp (-(s v)) := by
  have hζ : piExp (-v) ≠ 0 := Work.Horn.MandelDim.piExp_ne_zero _
  rw [hornS, if_neg hζ]
  obtain ⟨k, hk⟩ := Work.Horn.MandelDim.piExp_eq_iff.mp
    (show piExp (Complex.log (piExp (-v)) / (2 * Real.pi * Complex.I)) = piExp (-v) from
      Work.Horn.MandelDim.piExp_log_div _ hζ)
  have hk' : -(Complex.log (piExp (-v)) / (2 * Real.pi * Complex.I)) = v + ((-k : ℤ) : ℂ) := by
    rw [hk]; push_cast; ring
  have hsk : s (v + ((-k : ℤ) : ℂ)) = s v + ((-k : ℤ) : ℂ) :=
    section_add_int (s := s) hT heq hv (-k)
  rw [hk', hsk]
  rw [show -(s v + ((-k : ℤ) : ℂ)) = -(s v) + (k : ℂ) by push_cast; ring,
    Work.Horn.MandelDim.piExp_add_intCast]

theorem hornS_of_ne (f : ℂ → ℂ) {u : ℂ} (hu : u ≠ 0) :
    hornS f u = piExp (-(f (-(Complex.log u / (2 * Real.pi * Complex.I))))) := by
  simp [hornS, hu]

/-- Membership in the inverted-chart domain. -/
theorem mem_hornDl' {D : Set ℂ} {u : ℂ} :
    u ∈ hornDl' D ↔ u = 0 ∨ ∃ v : ℂ, -v ∈ D ∧ piExp v = u := by
  simp [hornDl', Set.mem_insert_iff, Set.mem_image, eq_comm]

/-- The canonical (negative) lift of `u ∈ hornDl' D`, `u ≠ 0`, lies in `D`. -/
theorem neg_log_div_mem {D : Set ℂ} (hT : MandelDim.IsTInvariant D)
    {u : ℂ} (hu : u ∈ hornDl' D) (hu0 : u ≠ 0) :
    -(Complex.log u / (2 * Real.pi * Complex.I)) ∈ D := by
  rcases (mem_hornDl' (D := D)).mp hu with h0 | ⟨w, hw, hwpi⟩
  · exact absurd h0 hu0
  · obtain ⟨k, hk⟩ := Work.Horn.MandelDim.piExp_eq_iff.mp
      (show piExp (Complex.log u / (2 * Real.pi * Complex.I)) = piExp w from by
        rw [Work.Horn.MandelDim.piExp_log_div u hu0, hwpi])
    have h2 : -(Complex.log u / (2 * Real.pi * Complex.I)) = -w + ((-k : ℤ) : ℂ) := by
      rw [hk]; push_cast; ring
    rw [h2]
    exact Work.Horn.MandelDim.IsTInvariant.add_int hT hw (-k)

/-- `hornS` is holomorphic away from `0`: near `u ≠ 0` it is `π ∘ s ∘ (-L)` for an explicit
local branch `L` of `π⁻¹` (a rotated principal logarithm), which avoids the slit-plane
restriction of `Complex.differentiableAt_log`. -/
theorem hornS_differentiableAt {s : ℂ → ℂ} {D : Set ℂ} (hDo : IsOpen D)
    (hT : MandelDim.IsTInvariant D) (heq : ∀ w ∈ D, s (w + 1) = s w + 1)
    (hs : DifferentiableOn ℂ s D)
    {u : ℂ} (hu : u ∈ hornDl' D) (hu0 : u ≠ 0) :
    DifferentiableAt ℂ (hornS s) u := by
  have huD : -(Complex.log u / (2 * Real.pi * Complex.I)) ∈ D := neg_log_div_mem hT hu hu0
  obtain ⟨c, lc, hc, hcu⟩ : ∃ (c lc : ℂ), Complex.exp lc = c ∧ c * u ∈ Complex.slitPlane := by
    rcases Complex.mem_slitPlane_or_neg_mem_slitPlane hu0 with h | h
    · exact ⟨1, 0, by simp, by simpa using h⟩
    · exact ⟨-1, ↑Real.pi * Complex.I, Complex.exp_pi_mul_I, by simpa using h⟩
  have hc0 : c ≠ 0 := by rw [← hc]; exact Complex.exp_ne_zero _
  set L : ℂ → ℂ := fun ζ => (Complex.log (c * ζ) - lc) / (2 * Real.pi * Complex.I) with hLdef
  have hLpi : ∀ ζ : ℂ, c * ζ ∈ Complex.slitPlane → piExp (L ζ) = ζ := by
    intro ζ hζ
    have hζ0 : c * ζ ≠ 0 := fun h0 => Complex.zero_notMem_slitPlane (h0 ▸ hζ)
    have h2 : 2 * (Real.pi : ℂ) * Complex.I *
        ((Complex.log (c * ζ) - lc) / (2 * Real.pi * Complex.I)) = Complex.log (c * ζ) - lc := by
      field_simp
    rw [MandelDim.piExp, hLdef]
    simp only
    rw [h2, Complex.exp_sub, Complex.exp_log hζ0, hc]
    field_simp
  have hLholo : DifferentiableAt ℂ L u := by
    have h1 : DifferentiableAt ℂ (fun ζ : ℂ => c * ζ) u :=
      (differentiableAt_const c).mul differentiableAt_id
    have h2 : DifferentiableAt ℂ (fun ζ : ℂ => Complex.log (c * ζ)) u :=
      (Complex.differentiableAt_log hcu).comp u h1
    rw [hLdef]
    exact (h2.sub_const lc).div_const _
  have hLmemu : -(L u) ∈ D := by
    have h1 : piExp (L u) = u := hLpi u hcu
    have h0 : piExp (L u) = piExp (Complex.log u / (2 * Real.pi * Complex.I)) := by
      rw [h1, Work.Horn.MandelDim.piExp_log_div u hu0]
    obtain ⟨k, hk⟩ := Work.Horn.MandelDim.piExp_eq_iff.mp h0
    have h2 : -(L u) = -(Complex.log u / (2 * Real.pi * Complex.I)) + ((-k : ℤ) : ℂ) := by
      rw [hk]; push_cast; ring
    rw [h2]
    exact Work.Horn.MandelDim.IsTInvariant.add_int hT huD (-k)
  have heq' : hornS s =ᶠ[𝓝 u] fun ζ => piExp (-(s (-(L ζ)))) := by
    have hopen : {ζ : ℂ | c * ζ ∈ Complex.slitPlane} ∈ 𝓝 u :=
      (Complex.isOpen_slitPlane.preimage (continuous_const.mul continuous_id)).mem_nhds hcu
    have hmemD : {ζ : ℂ | -(L ζ) ∈ D} ∈ 𝓝 u :=
      hLholo.continuousAt.neg.preimage_mem_nhds (hDo.mem_nhds hLmemu)
    filter_upwards [hopen, hmemD, isOpen_compl_singleton.mem_nhds hu0] with ζ hζ hD hζ0
    calc hornS s ζ = hornS s (piExp (L ζ)) := by rw [hLpi ζ hζ]
      _ = hornS s (piExp (-(-(L ζ)))) := by rw [show -(-(L ζ)) = L ζ by ring]
      _ = piExp (-(s (-(L ζ)))) := hornS_piExp (s := s) hT heq hD
  have hcomp : DifferentiableAt ℂ (fun ζ : ℂ => s (-(L ζ))) u :=
    (hs.differentiableAt (hDo.mem_nhds hLmemu)).comp u hLholo.neg
  have hfin : DifferentiableAt ℂ (fun ζ : ℂ => piExp (-(s (-(L ζ))))) u :=
    (differentiableAt_piExp _).comp u hcomp.neg
  exact hfin.congr_of_eventuallyEq heq'

theorem piExp_neg (x : ℂ) : piExp (-x) = 1 / piExp x := by
  have h : 2 * (Real.pi : ℂ) * Complex.I * (-x) = -(2 * (Real.pi : ℂ) * Complex.I * x) := by ring
  rw [one_div, MandelDim.piExp, MandelDim.piExp, h, Complex.exp_neg]

/-- The `u`-chart (`u = e^{-2πiw}`) model of the horn map `g = pushdown Ẽ`. -/
def hornEt (d : ParabData f₀ D₀) : ℂ → ℂ := hornS d.E

theorem hornEt_zero (d : ParabData f₀ D₀) : hornEt d 0 = 0 := hornS_zero d.E

/-- `Ẽ` restricted to `hornDl' Bl` is surjective onto `ℂ` (transfer of `surjOn_hornG_hornDl`
through the inversion `u ↔ 1/u`). -/
theorem hornEt_surj (d : ParabData f₀ D₀) {Bu Bl : Set ℂ}
    (htBu : MandelDim.IsTInvariant Bu) (htBl : MandelDim.IsTInvariant Bl)
    (hsub : Bu ∪ Bl ⊆ d.DE)
    (hinf : ∀ y : ℂ, (piExp '' {w : ℂ | w ∈ Bl ∧ d.E w = y}).Infinite) :
    hornEt d '' hornDl' Bl = univ := by
  have hsurj : hornG d '' hornDl Bl = univ :=
    surjOn_hornG_hornDl d htBu htBl hsub hinf
  have hEeq : ∀ w ∈ Bl, d.E (w + 1) = d.E w + 1 :=
    fun w hw => Work.Horn.MandelDim.ParabData.E_add_one d (hsub (Or.inr hw))
      (hsub (Or.inr ((htBl w).mp hw)))
  ext ζ
  simp only [mem_univ, iff_true]
  rcases eq_or_ne ζ 0 with rfl | hne
  · exact ⟨0, Or.inl rfl, hornEt_zero d⟩
  · have h1 : (1 / ζ) ∈ hornG d '' hornDl Bl := by rw [hsurj]; exact mem_univ _
    obtain ⟨v, hv, hgv⟩ := h1
    rcases Set.mem_insert_iff.mp hv with rfl | ⟨w, hw, rfl⟩
    · simp only [hornG_zero] at hgv
      exact absurd hgv.symm (one_div_ne_zero hne)
    · have hwB : w ∈ Bl := hw
      refine ⟨piExp (-w), Or.inr ⟨-w, by simpa using hwB, rfl⟩, ?_⟩
      rw [hornEt, hornS_piExp (s := d.E) htBl hEeq (v := w) hwB]
      rw [piExp_neg, ← hornG_piExp d htBu htBl hsub (Or.inr hwB), hgv]
      simp

/-- The germ `Ŝ(u)/u → e^{2πi cl}` makes `Ŝ` holomorphic at the puncture `0` (removable
singularity): `Ŝ` is differentiable on the punctured disc `‖u‖ < e^{-2πη}` (which lies in
`hornDl' D`), and the germ gives continuity at `0`. -/
theorem hornS_analyticAt_zero {s : ℂ → ℂ} {D : Set ℂ} {cl : ℂ} {η : ℝ}
    (hDo : IsOpen D) (hT : MandelDim.IsTInvariant D) (heq : ∀ w ∈ D, s (w + 1) = s w + 1)
    (hs : DifferentiableOn ℂ s D) (hlow : {w : ℂ | w.im < -η} ⊆ D)
    (hgerm : Filter.Tendsto (fun u : ℂ => hornS s u / u)
      (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ)) (nhds (piExp cl))) :
    AnalyticAt ℂ (hornS s) 0 := by
  have hpos : (0 : ℝ) < Real.exp (-(2 * Real.pi) * η) := Real.exp_pos _
  refine Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_
  · have hball : Metric.ball (0 : ℂ) (Real.exp (-(2 * Real.pi) * η))
        ∈ nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ) := by
      rw [mem_nhdsWithin_iff]
      exact ⟨Real.exp (-(2 * Real.pi) * η), hpos, Set.inter_subset_left⟩
    filter_upwards [hball, self_mem_nhdsWithin] with u hu hu0
    have hne : u ≠ 0 := by simpa using hu0
    exact hornS_differentiableAt hDo hT heq hs
      (mem_hornDl'_of_norm_lt hlow (by rwa [mem_ball_zero_iff] at hu)) hne
  · rw [Metric.continuousAt_iff]
    intro ε hε
    have hc : (0 : ℝ) < ‖piExp cl‖ + 1 := by positivity
    have hb : ∀ᶠ u : ℂ in nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ),
        ‖hornS s u / u‖ < ‖piExp cl‖ + 1 := by
      have h2 : ∀ᶠ y : ℂ in nhds (piExp cl), ‖y‖ < ‖piExp cl‖ + 1 := by
        have hδ : (0 : ℝ) < ‖piExp cl‖ + 1 - ‖piExp cl‖ := by linarith
        refine Filter.mem_of_superset (Metric.ball_mem_nhds (piExp cl) hδ) ?_
        intro y hy
        rw [Metric.mem_ball, dist_eq_norm] at hy
        have h1 : ‖y‖ ≤ ‖y - piExp cl‖ + ‖piExp cl‖ := by
          calc ‖y‖ = ‖(y - piExp cl) + piExp cl‖ := by ring_nf
            _ ≤ ‖y - piExp cl‖ + ‖piExp cl‖ := norm_add_le _ _
        show ‖y‖ < ‖piExp cl‖ + 1
        linarith
      exact hgerm.eventually h2
    obtain ⟨δ, hδpos, hδsub⟩ := mem_nhdsWithin_iff.mp hb
    refine ⟨min δ (ε / (‖piExp cl‖ + 1)), lt_min hδpos (div_pos hε hc), fun x hx => ?_⟩
    have hxmem : ‖x‖ < min δ (ε / (‖piExp cl‖ + 1)) := by simpa [dist_eq_norm] using hx
    rcases eq_or_ne x 0 with rfl | hx0
    · simpa [hornS_zero] using hε
    · have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
      have h1 : ‖hornS s x / x‖ < ‖piExp cl‖ + 1 :=
        hδsub ⟨by rw [mem_ball_zero_iff]; exact lt_of_lt_of_le hxmem (min_le_left _ _),
          by simpa using hx0⟩
      have h2 : ‖hornS s x‖ = ‖x‖ * ‖hornS s x / x‖ := by
        rw [norm_div]; field_simp
      have h3 : ‖hornS s x‖ < ε := by
        rw [h2]
        have h4 : ‖x‖ < ε / (‖piExp cl‖ + 1) := lt_of_lt_of_le hxmem (min_le_right _ _)
        have h5 : ‖x‖ * ‖hornS s x / x‖ < (ε / (‖piExp cl‖ + 1)) * (‖piExp cl‖ + 1) := by
          rcases eq_or_lt_of_le (norm_nonneg (hornS s x / x)) with hz | hz
          · rw [← hz, mul_zero]; positivity
          · calc ‖x‖ * ‖hornS s x / x‖ < (ε / (‖piExp cl‖ + 1)) * ‖hornS s x / x‖ :=
                mul_lt_mul_of_pos_right h4 hz
              _ < (ε / (‖piExp cl‖ + 1)) * (‖piExp cl‖ + 1) :=
                mul_lt_mul_of_pos_left h1 (div_pos hε hc)
        rwa [div_mul_cancel₀ ε (ne_of_gt hc)] at h5
      simpa [dist_eq_norm, hornS_zero, sub_zero] using h3

theorem continuous_piExp : Continuous piExp :=
  Complex.continuous_exp.comp (continuous_const.mul continuous_id)

/-- The lower component of the cylinder is bounded in the inverted chart. -/
theorem isBounded_hornDl' {Bu Bl : Set ℂ} {η : ℝ} (hup : {w : ℂ | η < w.im} ⊆ Bu)
    (hdisj : Disjoint Bu Bl) : Bornology.IsBounded (hornDl' Bl) := by
  have hle : Bl ⊆ {w : ℂ | w.im ≤ η} := by
    intro w hw
    by_contra h
    rw [Set.mem_setOf_eq, not_le] at h
    exact Set.disjoint_left.mp hdisj (hup h) hw
  refine (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mpr
    ⟨Real.exp (2 * Real.pi * η), ?_⟩
  intro ζ hζ
  rcases Set.mem_insert_iff.mp hζ with rfl | hζ
  · exact mem_closedBall_self (Real.exp_pos _).le
  · obtain ⟨w, hw, rfl⟩ := hζ
    have h1 : -w.im ≤ η := by
      have h := hle hw
      simpa [Complex.neg_im] using h
    rw [mem_closedBall_zero_iff, norm_piExp, Real.exp_le_exp]
    have h3 : 2 * Real.pi * (-w.im) ≤ 2 * Real.pi * η :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h4 : 2 * Real.pi * (-w.im) = -(2 * Real.pi) * w.im := by ring
    linarith [h3, h4]

/-- The descended section maps `hornDl' D` into itself. -/
theorem hornS_mem {s : ℂ → ℂ} {D : Set ℂ} (hT : MandelDim.IsTInvariant D)
    (heq : ∀ w ∈ D, s (w + 1) = s w + 1) (hsm : ∀ w ∈ D, s w ∈ D) :
    ∀ {u : ℂ}, u ∈ hornDl' D → hornS s u ∈ hornDl' D := by
  intro u hu
  rcases Set.mem_insert_iff.mp hu with rfl | ⟨v, hv, rfl⟩
  · rw [hornS_zero]; exact Or.inl rfl
  · have h1 : (-v : ℂ) ∈ D := hv
    have h2 : hornS s (piExp v) = piExp (-(s (-v))) := by
      simpa using hornS_piExp (s := s) hT heq (v := -v) h1
    rw [h2]
    exact Set.mem_insert_of_mem _ ⟨-(s (-v)), by simpa using hsm (-v) h1, rfl⟩

/-- The descended section is a section of the descended map: `Ẽ ∘ Ŝ = id` on `hornDl' D`. -/
theorem hornS_section {E s : ℂ → ℂ} {D : Set ℂ} (hT : MandelDim.IsTInvariant D)
    (hEeq : ∀ w ∈ D, E (w + 1) = E w + 1) (heq : ∀ w ∈ D, s (w + 1) = s w + 1)
    (hsm : ∀ w ∈ D, s w ∈ D) (hEs : ∀ w ∈ D, E (s w) = w) :
    ∀ {u : ℂ}, u ∈ hornDl' D → hornS E (hornS s u) = u := by
  intro u hu
  rcases Set.mem_insert_iff.mp hu with rfl | ⟨v, hv, rfl⟩
  · simp [hornS]
  · have hvD : (-v : ℂ) ∈ D := hv
    have h1 : hornS s (piExp v) = piExp (-(s (-v))) := by
      simpa using hornS_piExp (s := s) hT heq (v := -v) hvD
    have h2 : hornS E (piExp (-(s (-v)))) = piExp (-(E (s (-v)))) :=
      hornS_piExp (s := E) hT hEeq (v := s (-v)) (hsm (-v) hvD)
    rw [h1, h2, hEs (-v) hvD]
    rw [show -(-v) = v by ring]


/-! ## Preconnectedness of the inverted-chart domains -/

/-- Attaching a point of the closure of a preconnected set keeps it preconnected. -/
theorem isPreconnected_insert_of_mem_closure {α : Type*} [TopologicalSpace α] {s : Set α} {x : α}
    (hs : IsPreconnected s) (hx : x ∈ closure s) : IsPreconnected (insert x s) := by
  intro u v hu hv hsub hune hvne
  have hsuv : s ⊆ u ∪ v := fun y hy => hsub (Set.mem_insert_of_mem x hy)
  have hsu : (s ∩ u).Nonempty := by
    rcases hune with ⟨y, hy⟩
    rcases hy.1 with rfl | hys
    · obtain ⟨z, hzu, hzs⟩ := mem_closure_iff.mp hx u hu hy.2
      exact ⟨z, hzs, hzu⟩
    · exact ⟨y, hys, hy.2⟩
  have hsv : (s ∩ v).Nonempty := by
    rcases hvne with ⟨y, hy⟩
    rcases hy.1 with rfl | hys
    · obtain ⟨z, hzv, hzs⟩ := mem_closure_iff.mp hx v hv hy.2
      exact ⟨z, hzs, hzv⟩
    · exact ⟨y, hys, hy.2⟩
  obtain ⟨z, hzs, hzu, hzv⟩ := hs u v hu hv hsuv hsu hsv
  exact ⟨z, Set.mem_insert_of_mem x hzs, hzu, hzv⟩

/-- Simple connectivity gives preconnectedness of the underlying set. -/
theorem isPreconnected_of_simplyConnected {Bl : Set ℂ} (h : SimplyConnectedSpace Bl) :
    IsPreconnected Bl := by
  letI := h
  have hpc : PathConnectedSpace Bl := inferInstance
  have hipc : IsPathConnected (Bl : Set ℂ) := isPathConnected_iff_pathConnectedSpace.mpr hpc
  exact hipc.isConnected.isPreconnected

/-- `hornDl' Bl` is preconnected: it is `π '' (-Bl)` (preconnected) with the point `0` attached,
and `0` lies in the closure because `{Im > η} ⊆ -Bl`. -/
theorem isPreconnected_hornDl' {Bl : Set ℂ} {η : ℝ} (hBlc : IsPreconnected Bl)
    (hlo : {w : ℂ | w.im < -η} ⊆ Bl) : IsPreconnected (hornDl' Bl) := by
  have hN : {w : ℂ | -w ∈ Bl} = Neg.neg '' Bl := by
    ext w
    constructor
    · intro hw; exact ⟨-w, hw, by simp⟩
    · rintro ⟨z, hz, rfl⟩; simpa using hz
  have hNc : IsPreconnected {w : ℂ | -w ∈ Bl} := by
    rw [hN]
    exact hBlc.image _ continuous_neg.continuousOn
  have himg : IsPreconnected (piExp '' {w : ℂ | -w ∈ Bl}) :=
    hNc.image _ continuous_piExp.continuousOn
  have hcl : (0 : ℂ) ∈ closure (piExp '' {w : ℂ | -w ∈ Bl}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨T, hTη, hTε⟩ : ∃ T : ℝ, η < T ∧ Real.exp (-(2 * Real.pi) * T) < ε := by
      refine ⟨max (η + 1) ((1 - Real.log ε) / (2 * Real.pi) + 1), ?_, ?_⟩
      · have h1 : η + 1 ≤ max (η + 1) ((1 - Real.log ε) / (2 * Real.pi) + 1) := le_max_left _ _
        linarith
      · have hpi : (0:ℝ) < 2 * Real.pi := by positivity
        have hA : (1 - Real.log ε) / (2 * Real.pi) + 1
            ≤ max (η + 1) ((1 - Real.log ε) / (2 * Real.pi) + 1) := le_max_right _ _
        have hle : -(2 * Real.pi) * (max (η + 1) ((1 - Real.log ε) / (2 * Real.pi) + 1))
            ≤ Real.log ε - (1 + 2 * Real.pi) := by
          have h1 : -(2 * Real.pi) * (max (η + 1) ((1 - Real.log ε) / (2 * Real.pi) + 1))
              ≤ -(2 * Real.pi) * ((1 - Real.log ε) / (2 * Real.pi) + 1) :=
            mul_le_mul_of_nonpos_left hA (by linarith)
          have h2 : -(2 * Real.pi) * ((1 - Real.log ε) / (2 * Real.pi) + 1)
              = Real.log ε - (1 + 2 * Real.pi) := by
            field_simp
            ring
          linarith [h1, h2.le, h2.ge]
        have h2 : Real.log ε - (1 + 2 * Real.pi) < Real.log ε := by linarith [Real.pi_pos]
        calc Real.exp (-(2 * Real.pi) * (max (η + 1) ((1 - Real.log ε) / (2 * Real.pi) + 1)))
            ≤ Real.exp (Real.log ε - (1 + 2 * Real.pi)) := Real.exp_le_exp.mpr hle
          _ < Real.exp (Real.log ε) := Real.exp_lt_exp.mpr h2
          _ = ε := Real.exp_log hε
    refine ⟨piExp (Complex.I * T), ⟨Complex.I * T, ?_, rfl⟩, ?_⟩
    · have him : (-(Complex.I * T)).im = -T := by simp
      refine hlo (by show (-(Complex.I * T)).im < -η; rw [him]; linarith)
    · rw [dist_comm, dist_zero_right, norm_piExp]
      have him : (Complex.I * T).im = T := by simp
      rw [him]; exact hTε
  rw [show hornDl' Bl = insert 0 (piExp '' {w : ℂ | -w ∈ Bl}) from rfl]
  exact isPreconnected_insert_of_mem_closure himg hcl

/-! ## Case I: the lower-end section forces `0 < cl.im` -/

/-- **Case I.** If a holomorphic section `s` of `d.E` over the lower component `Bl` exists, is
`T`-equivariant, maps `Bl` into itself, and its descent `Ŝ = hornS s` is analytic at `0` with
`Ŝ'(0) = π(cl)`, then `0 < cl.im`: Cartan's theorem (Schwarz at the fixed point) gives
`‖π(cl)‖ ≤ 1`, and the equality case would make `Ŝ` surjective onto the bounded domain
`hornDl' Bl`, contradicting that `hornS d.E` maps it onto all of `ℂ`. -/
theorem cl_im_pos_of_section (f₀ : ℂ → ℂ) (D₀ : Set ℂ) (d : ParabData f₀ D₀)
    {Bu Bl : Set ℂ} {η : ℝ} {cl : ℂ} {s : ℂ → ℂ}
    (hBuO : IsOpen Bu) (htBu : MandelDim.IsTInvariant Bu)
    (hup : {w : ℂ | η < w.im} ⊆ Bu)
    (hBlO : IsOpen Bl) (hBlS : SimplyConnectedSpace Bl) (htBl : MandelDim.IsTInvariant Bl)
    (hlo : {w : ℂ | w.im < -η} ⊆ Bl) (hdisj : Disjoint Bu Bl)
    (hsubU : Bu ∪ Bl ⊆ d.DE)
    (hinfl : ∀ y : ℂ, (piExp '' {w : ℂ | w ∈ Bl ∧ d.E w = y}).Infinite)
    (hs : DifferentiableOn ℂ s Bl) (hsm : ∀ y ∈ Bl, s y ∈ Bl)
    (hes : ∀ y ∈ Bl, d.E (s y) = y) (heq : ∀ w ∈ Bl, s (w + 1) = s w + 1)
    (hana : AnalyticAt ℂ (hornS s) 0) (hder : deriv (hornS s) 0 = piExp cl) :
    0 < cl.im := by
  have hopen : IsOpen (hornDl' Bl) := isOpen_hornDl' hBlO hlo
  have hbdd : Bornology.IsBounded (hornDl' Bl) := isBounded_hornDl' hup hdisj
  have hconn : IsPreconnected (hornDl' Bl) :=
    isPreconnected_hornDl' (isPreconnected_of_simplyConnected hBlS) hlo
  have hmem : ∀ u ∈ hornDl' Bl, hornS s u ∈ hornDl' Bl :=
    fun u hu => hornS_mem htBl heq hsm hu
  have hdiff : DifferentiableOn ℂ (hornS s) (hornDl' Bl) := by
    intro u hu
    rcases eq_or_ne u 0 with rfl | hne
    · exact hana.differentiableAt.differentiableWithinAt
    · exact (hornS_differentiableAt hBlO htBl heq hs hu hne).differentiableWithinAt
  have hcartan := Work.L62.cartan hopen hbdd hconn hdiff (fun u hu => hmem u hu)
    (Set.mem_insert _ _) (hornS_zero s)
  -- `‖π(cl)‖ ≤ 1`
  have hnorm : ‖piExp cl‖ ≤ 1 := by
    rw [← hder]; exact hcartan.1
  -- the equality case is impossible
  have hne0 : cl.im ≠ 0 := by
    intro him0
    have h1 : ‖deriv (hornS s) 0‖ = 1 := by
      rw [hder, norm_piExp, show -(2 * Real.pi) * cl.im = 0 by rw [him0]; ring, Real.exp_zero]
    have hsurj : SurjOn (hornS s) (hornDl' Bl) (hornDl' Bl) := (hcartan.2 h1).1
    have hEeq : ∀ w ∈ Bl, d.E (w + 1) = d.E w + 1 := fun w hw =>
      Work.Horn.MandelDim.ParabData.E_add_one d (hsubU (Or.inr hw))
        (hsubU (Or.inr ((htBl w).mp hw)))
    have hsec : ∀ u ∈ hornDl' Bl, hornS d.E (hornS s u) = u :=
      fun u hu => hornS_section htBl hEeq heq hsm hes hu
    -- surjectivity of `Ŝ` makes `Ê = hornS d.E` map `Ω` into `Ω`
    have hsub : hornS d.E '' (hornDl' Bl) ⊆ hornDl' Bl := by
      rintro u ⟨w, hw, hwu⟩
      have himg : (hornS s) '' (hornDl' Bl) = hornDl' Bl :=
        SurjOn.image_eq_of_mapsTo hsurj (fun u hu => hmem u hu)
      have hwΩ : w ∈ (hornS s) '' (hornDl' Bl) := by rw [himg]; exact hw
      obtain ⟨v, hv, hvw⟩ := hwΩ
      have h1 : hornS d.E w = v := by rw [← hvw, hsec v hv]
      rw [← hwu, h1]
      exact hv
    have hall : hornS d.E '' (hornDl' Bl) = univ := hornEt_surj d htBu htBl hsubU hinfl
    have huniv : (hornDl' Bl) = univ := Set.eq_univ_of_univ_subset (by rw [hall] at hsub; exact hsub)
    -- but `hornDl' Bl` is bounded
    have hunivbdd : Bornology.IsBounded (univ : Set ℂ) := huniv ▸ hbdd
    obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hunivbdd
    have h0r : 0 ≤ r := by
      have h := hr (Set.mem_univ (0 : ℂ))
      simpa [Metric.mem_closedBall, dist_eq_norm] using h
    have hmemr : ‖((r + 1 : ℝ) : ℂ)‖ ≤ r := by
      have h := hr (Set.mem_univ ((r + 1 : ℝ) : ℂ))
      simpa [Metric.mem_closedBall, dist_eq_norm] using h
    have hpos : (0:ℝ) < r + 1 := by linarith
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos] at hmemr
    linarith
  -- conclude
  have hnonneg : 0 ≤ cl.im := by
    have h : Real.exp (-(2 * Real.pi) * cl.im) ≤ 1 := by
      rw [← norm_piExp]; exact hnorm
    have h2 : -(2 * Real.pi) * cl.im ≤ 0 := by
      have := Real.exp_le_exp.mp (by simpa using h)
      simpa using this
    nlinarith [Real.pi_pos]
  exact lt_of_le_of_ne' hnonneg hne0

/-! ## The critical-value class lies in one of the two components -/

/-- Since `Bu` and `Bl` are `T`-invariant and disjoint, at most one of them contains the
`T`-orbit `v + ℤ`. -/
theorem critvalue_avoid (v : ℂ) {Bu Bl : Set ℂ} (htBu : MandelDim.IsTInvariant Bu)
    (htBl : MandelDim.IsTInvariant Bl) (hdisj : Disjoint Bu Bl) :
    (∀ k : ℤ, v + k ∉ Bl) ∨ (∀ k : ℤ, v + k ∉ Bu) := by
  by_cases hBl : ∃ k : ℤ, v + k ∈ Bl
  · right
    intro k hk
    obtain ⟨k₁, hk₁⟩ := hBl
    have h1 : v + k₁ + ((k - k₁ : ℤ) : ℂ) ∈ Bl :=
      Work.Horn.MandelDim.IsTInvariant.add_int htBl hk₁ (k - k₁)
    have heq : v + k₁ + ((k - k₁ : ℤ) : ℂ) = v + k := by push_cast; ring
    exact (Set.disjoint_left.mp hdisj hk) (heq ▸ h1)
  · left
    intro k hk
    exact hBl ⟨k, hk⟩


end Work.Horn
