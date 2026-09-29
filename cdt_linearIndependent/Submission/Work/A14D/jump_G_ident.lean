import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.LC_setup

/-!
# `Work.A14D.jump_G_ident`

The jump identity for the `x`-side transfer (design §4 of `REFS/design/a14/A14_design.lean.txt`).

Writing `D = HU − HL` for the jump of the continued `H` (its two branches `HU` on `SU` and `HL`
on `SL`), `F = HU + HL ∘ w` for the pull-back of the symmetrisation `Sym⁺ H` and
`jumpH D = D − D ∘ w`, the deck involution `w = wC` satisfies `y ∘ w = y`, so `∂_y` commutes with
precomposition by `w`:

  `∂_y (g ∘ w) = (∂_y g) ∘ w`   (`Dy_comp_wC`),   hence   `∂_y^k (g ∘ w) = (∂_y^k g) ∘ w`,

and therefore the jump of the pulled back function is the `∂_y`-derivative of the jump:

  `∂_y^k F(z) − ∂_y^k F(w z) = ∂_y^k (D − D ∘ w)(z)`.

The `∂_y`-commutation is proved for *arbitrary* `g` (no regularity), by a case split: where `g` is
differentiable at `w z` it is the chain rule combined with the algebraic identity
`w'(z)·(y'(z))^{-1} = (y'(w z))^{-1}`; where it is not, both sides are `0` (using that `w` is a
local diffeomorphism).  The linearity of `∂_y^k` used at the end does need regularity: over `ℂ`,
`DifferentiableOn ℂ` on the open half-planes `SU`, `SL` makes the branches `HU`, `HL` *analytic*,
hence smooth, so `∂_y^k F` and `∂_y^k (F ∘ w)` are analytic at every point with `z²−2z ≠ 0`.
-/

open Complex Metric Filter
open scoped Topology

noncomputable section
namespace Work.A14D

/-! ## The involution `wC` and `∂_y` -/

lemma wC_wC (z : ℂ) (hz : z ≠ 1) : wC (wC z) = z := by
  simp only [wC]; field_simp; ring

lemma wC_ne_one (z : ℂ) : wC z ≠ 1 := by
  simp only [wC]; intro h
  by_cases hz : z = 1
  · subst hz; simp at h
  · field_simp at h
    have : (1:ℂ) = 0 := by linear_combination h
    exact one_ne_zero this

lemma differentiableAt_wC (z : ℂ) (hz : z ≠ 1) : DifferentiableAt ℂ wC z := by
  have h : wC = fun w : ℂ => w/(w-1) := rfl
  rw [h]
  exact (differentiableAt_id.div (differentiableAt_id.sub_const (1:ℂ)) (sub_ne_zero.mpr hz))

lemma deriv_wC (z : ℂ) (hz : z ≠ 1) : deriv wC z = -(1/(z-1)^2) := by
  have h : wC = (fun w : ℂ => w) / (fun w : ℂ => w-1) := rfl
  rw [h]
  have hd := deriv_div (c := fun w : ℂ => w) (d := fun w : ℂ => w-1) (x := z)
    differentiableAt_id (differentiableAt_id.sub_const 1) (sub_ne_zero.mpr hz)
  rw [hd]
  have hsub : deriv (fun w : ℂ => w-1) z = 1 := by
    simpa using (HasDerivAt.sub_const (1:ℂ) (hasDerivAt_id z)).deriv
  rw [deriv_id'', hsub]
  rw [show (1 * (z-1) - z * 1 : ℂ) = -1 by ring, neg_div]

/-- The algebraic identity `w'(z)·(y'(z))^{-1} = (y'(w z))^{-1}`, `y = yC`, `w = wC`. -/
lemma wC_alg (z : ℂ) (hz : z ≠ 1) : (wC z - 1)^2/((wC z)^2 - 2*wC z) = -(1/(z^2-2*z)) := by
  rw [show (wC z - 1)^2 = ((z-1)⁻¹)^2 from by
        rw [show wC z - 1 = (z-1)⁻¹ from by simp only [wC]; field_simp; ring]]
  rw [show (wC z)^2 - 2*wC z = -(z^2-2*z) * ((z-1)^2)⁻¹ from by simp only [wC]; field_simp; ring]
  rw [inv_pow]
  field_simp

lemma Dy_eq_zero_of_sq_sub (f : ℂ → ℂ) {z : ℂ} (h : z^2 - 2*z = 0) : Dy f z = 0 := by
  simp only [Dy]
  rw [h, div_zero]

lemma iter_succ (k : ℕ) (f : ℂ → ℂ) : DyIter (k+1) f = Dy (DyIter k f) := by
  simp only [DyIter, Function.iterate_succ_apply']

lemma Dy_eq (h : ℂ → ℂ) : Dy h = deriv h * (fun w : ℂ => (w-1)^2/(w^2-2*w)) := by
  funext w; simp only [Pi.mul_apply, Dy]; rw [mul_div_assoc]

/-! ## Locality of `deriv` and of `DyIter` on open sets -/

lemma deriv_congr_of_eqOn {f f' : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (h : ∀ x ∈ U, f x = f' x) {x : ℂ} (hx : x ∈ U) : deriv f x = deriv f' x :=
  Filter.EventuallyEq.deriv_eq (Filter.mem_of_superset (hU.mem_nhds hx) (fun y hy => h y hy))

private lemma DyIter_congr_of_eqOn {f f' : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (h : ∀ x ∈ U, f x = f' x) (k : ℕ) : ∀ x ∈ U, DyIter k f x = DyIter k f' x := by
  induction k with
  | zero => intro x hx; exact h x hx
  | succ j ih =>
      intro x hx
      rw [iter_succ j f, iter_succ j f']
      simp only [Dy]
      rw [deriv_congr_of_eqOn hU ih hx]

/-! ## `∂_y` commutes with the deck involution `wC` -/

/-- `∂_y (g ∘ w) = (∂_y g) ∘ w` for **arbitrary** `g` and `z ≠ 1`. -/
lemma Dy_comp_wC (g : ℂ → ℂ) (z : ℂ) (hz : z ≠ 1) :
    Dy (g ∘ wC) z = Dy g (wC z) := by
  by_cases h2 : z^2 - 2*z = 0
  · have hy : (wC z)^2 - 2*wC z = 0 := by
      have hz02 : z = 0 ∨ z = 2 := by
        have hh : z*(z-2) = 0 := by linear_combination h2
        rcases mul_eq_zero.mp hh with h|h
        · exact Or.inl h
        · exact Or.inr (sub_eq_zero.mp h)
      rcases hz02 with rfl | rfl
      · norm_num [wC]
      · norm_num [wC]
    rw [Dy_eq_zero_of_sq_sub _ h2, Dy_eq_zero_of_sq_sub _ hy]
  · by_cases hd : DifferentiableAt ℂ g (wC z)
    · have hchain : deriv (g ∘ wC) z = deriv g (wC z) * deriv wC z :=
        deriv_comp z hd (differentiableAt_wC z hz)
      simp only [Dy]
      rw [hchain, deriv_wC z hz]
      rw [show deriv g (wC z) * -(1/(z-1)^2) * (z-1)^2 / (z^2-2*z)
            = deriv g (wC z) * (-(1/(z^2-2*z))) by field_simp,
          show deriv g (wC z) * (wC z - 1)^2 / ((wC z)^2 - 2*wC z)
            = deriv g (wC z) * (-(1/(z^2-2*z))) by rw [mul_div_assoc, wC_alg z hz]]
    · have hgn : deriv g (wC z) = 0 := by
        show (fderiv ℂ g (wC z)) 1 = 0
        rw [fderiv_zero_of_not_differentiableAt hd]; simp
      have hnd : ¬ DifferentiableAt ℂ (g ∘ wC) z := by
        intro hc
        have h1 : DifferentiableAt ℂ (g ∘ wC) (wC (wC z)) := by rw [wC_wC z hz]; exact hc
        have h2 : DifferentiableAt ℂ ((g ∘ wC) ∘ wC) (wC z) :=
          DifferentiableAt.comp (wC z) h1 (differentiableAt_wC (wC z) (wC_ne_one z))
        refine hd (h2.congr_of_eventuallyEq ?_)
        have hmem : ({y : ℂ | y ≠ 1} : Set ℂ) ∈ 𝓝 (wC z) :=
          IsOpen.mem_nhds (isOpen_ne (x := (1:ℂ))) (wC_ne_one z)
        filter_upwards [hmem] with w hw
        simp only [Function.comp_apply]
        rw [wC_wC w hw]
      have hzn : deriv (g ∘ wC) z = 0 := by
        show (fderiv ℂ (g ∘ wC) z) 1 = 0
        rw [fderiv_zero_of_not_differentiableAt hnd]; simp
      simp only [Dy, hzn, hgn, zero_mul, zero_div]

lemma DyIter_comp_wC (g : ℂ → ℂ) (k : ℕ) :
    ∀ z : ℂ, z ≠ 1 → DyIter k (g ∘ wC) z = DyIter k g (wC z) := by
  induction k with
  | zero => intro z hz; rfl
  | succ j ih =>
      intro z hz
      rw [iter_succ j (g ∘ wC), iter_succ j g]
      rw [← Dy_comp_wC (DyIter j g) z hz]
      have hd : deriv (DyIter j (g ∘ wC)) z = deriv ((DyIter j g) ∘ wC) z :=
        deriv_congr_of_eqOn (isOpen_ne (x := (1:ℂ))) (fun x hx => ih x hx) hz
      simp only [Dy, hd]

/-! ## Analyticity of `∂_y^k f` at points where `z² − 2z ≠ 0`, and linearity of `∂_y^k` -/

lemma analyticAt_DyIter {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (hz : z^2-2*z ≠ 0) (k : ℕ) :
    AnalyticAt ℂ (DyIter k f) z := by
  induction k with
  | zero => simpa [DyIter] using hf
  | succ j ih =>
      have hd : AnalyticAt ℂ (deriv (DyIter j f)) z := ih.deriv
      have hr : AnalyticAt ℂ (fun w : ℂ => (w-1)^2/(w^2-2*w)) z := by
        have hn : AnalyticAt ℂ (fun w : ℂ => (w-1)^2) z :=
          (analyticAt_id.sub (analyticAt_const (v := (1:ℂ)))).pow 2
        have hde : AnalyticAt ℂ (fun w : ℂ => w^2 - 2*w) z :=
          (analyticAt_id.pow 2).sub (analyticAt_const.mul analyticAt_id)
        exact hn.div hde (by simpa using hz)
      rw [show DyIter (j+1) f = deriv (DyIter j f) * (fun w : ℂ => (w-1)^2/(w^2-2*w)) from by
            rw [iter_succ j f, Dy_eq]]
      exact hd.mul hr

lemma Dy_sub_eventuallyEq {f g : ℂ → ℂ} {z : ℂ}
    (hf : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ f w) (hg : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ g w) :
    Dy (f - g) =ᶠ[𝓝 z] Dy f - Dy g := by
  filter_upwards [hf, hg] with w hfw hgw
  show Dy (f - g) w = Dy f w - Dy g w
  simp only [Dy]
  rw [deriv_sub hfw hgw]
  ring_nf

lemma DyIter_sub_eventuallyEq {f g : ℂ → ℂ} {z : ℂ}
    (hf : ∀ j, AnalyticAt ℂ (DyIter j f) z) (hg : ∀ j, AnalyticAt ℂ (DyIter j g) z) :
    ∀ k, DyIter k (f - g) =ᶠ[𝓝 z] DyIter k f - DyIter k g := by
  intro k
  induction k with
  | zero => exact Filter.EventuallyEq.rfl
  | succ j ih =>
      have hfd : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ (DyIter j f) w :=
        (hf j).eventually_analyticAt.mono (fun w hw => hw.differentiableAt)
      have hgd : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ (DyIter j g) w :=
        (hg j).eventually_analyticAt.mono (fun w hw => hw.differentiableAt)
      have h2 : deriv (DyIter j (f - g)) =ᶠ[𝓝 z] deriv (DyIter j f - DyIter j g) := ih.deriv
      have h4 : Dy (DyIter j (f - g)) =ᶠ[𝓝 z] Dy (DyIter j f - DyIter j g) := by
        rw [Dy_eq, Dy_eq]
        exact h2.mul Filter.EventuallyEq.rfl
      have h3 : Dy (DyIter j f - DyIter j g) =ᶠ[𝓝 z] Dy (DyIter j f) - Dy (DyIter j g) :=
        Dy_sub_eventuallyEq hfd hgd
      rw [iter_succ j (f - g), iter_succ j f, iter_succ j g]
      exact h4.trans h3

/-- Linearity of `∂_y^k` at a point where all the needed iterates are analytic. -/
lemma DyIter_sub_apply {f g : ℂ → ℂ} {z : ℂ}
    (hf : ∀ j, AnalyticAt ℂ (DyIter j f) z) (hg : ∀ j, AnalyticAt ℂ (DyIter j g) z) (k : ℕ) :
    DyIter k (f - g) z = DyIter k f z - DyIter k g z :=
  (DyIter_sub_eventuallyEq hf hg k).eq_of_nhds

/-! ## The two half-planes and `wC` -/

lemma wC_mem_SU_SL {z : ℂ} (hz : z ∈ SU ∩ SL) : wC z ∈ SU ∩ SL := by
  obtain ⟨hzU, hzL⟩ := hz
  simp only [SU, SL, Set.mem_setOf_eq] at hzU hzL
  change (1 - (wC z).re) / 8 < (wC z).im ∧ (wC z).im < ((wC z).re - 1) / 8
  have hre : 1 < z.re := by linarith
  have h1 : z ≠ 1 := by intro h; rw [h] at hre; norm_num at hre
  have hU' : -(z.re - 1) < 8 * z.im := by linarith
  have hL' : 8 * z.im < z.re - 1 := by linarith
  have hDpos : 0 < normSq (z - 1) := by rw [Complex.normSq_pos]; exact sub_ne_zero.mpr h1
  have hw : wC z = 1 + (z - 1)⁻¹ := by simp only [wC]; field_simp; ring
  have hr : (wC z).re = 1 + (z.re - 1)/normSq (z-1) := by
    rw [hw]; simp [Complex.add_re, Complex.inv_re, Complex.sub_re]
  have hi : (wC z).im = -(z.im)/normSq (z-1) := by
    rw [hw]; simp [Complex.add_im, Complex.inv_im, Complex.sub_im]
  constructor
  · rw [hr, hi, ← sub_pos]
    have hh : -(z.im)/normSq (z-1) - (1 - (1 + (z.re-1)/normSq (z-1)))/8
        = (z.re - 1 - 8*z.im)/(8*normSq (z-1)) := by field_simp; ring
    rw [hh]
    apply div_pos _ (by positivity)
    linarith
  · rw [hr, hi, ← sub_pos]
    have hh : (1 + (z.re-1)/normSq (z-1) - 1)/8 - (-(z.im)/normSq (z-1))
        = (z.re - 1 + 8*z.im)/(8*normSq (z-1)) := by field_simp; ring
    rw [hh]
    apply div_pos _ (by positivity)
    linarith

private lemma isOpen_SU : IsOpen SU := by apply isOpen_lt <;> fun_prop
private lemma isOpen_SL : IsOpen SL := by apply isOpen_lt <;> fun_prop

lemma wC_analyticAt {z : ℂ} (hz : z ≠ 1) : AnalyticAt ℂ wC z := by
  have h : wC = (fun w : ℂ => w) / (fun w : ℂ => w - 1) := rfl
  rw [h]
  exact AnalyticAt.div analyticAt_id (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hz)

lemma hne1_of_mem {w : ℂ} (hw : w ∈ SU ∩ SL) : w ≠ 1 := by
  have hwU := hw.1; have hwL := hw.2
  simp only [SU, SL, Set.mem_setOf_eq] at hwU hwL
  have : 1 < w.re := by linarith
  intro h; rw [h] at this; norm_num at this

/-! ## The jump identity -/

theorem jump_G_ident {D HU HL : ℂ → ℂ}
    (hHU : DifferentiableOn ℂ HU SU) (hHL : DifferentiableOn ℂ HL SL)
    (hDj : ∀ z ∈ SU ∩ SL, D z = HU z - HL z) (k : ℕ) :
    ∀ z ∈ SU ∩ SL,
      DyIter k (fun ζ => HU ζ + HL (wC ζ)) z
          - DyIter k (fun ζ => HU ζ + HL (wC ζ)) (wC z)
        = DyIter k (jumpH D) z := by
  intro z hz
  set F : ℂ → ℂ := fun ζ => HU ζ + HL (wC ζ) with hF
  have hz1 : z ≠ 1 := hne1_of_mem hz
  by_cases hz2 : z = 2
  · subst hz2
    have hw2 : wC 2 = 2 := by simp only [wC]; norm_num
    have hj : DyIter k (jumpH D) 2 = 0 := by
      cases k with
      | zero => rw [show DyIter 0 (jumpH D) 2 = jumpH D 2 from rfl, jumpH, hw2, sub_self]
      | succ m => rw [iter_succ m]; simp only [Dy]; norm_num
    rw [hw2, sub_self, hj]
  · have hz2ne : z^2 - 2*z ≠ 0 := by
      intro h
      have hz02 : z = 0 ∨ z = 2 := by
        have hh : z*(z-2) = 0 := by linear_combination h
        rcases mul_eq_zero.mp hh with h'|h'
        · exact Or.inl h'
        · exact Or.inr (sub_eq_zero.mp h')
      rcases hz02 with h0 | h2'
      · have hzre : 1 < z.re := by
          have hzU := hz.1; have hzL := hz.2
          simp only [SU, SL, Set.mem_setOf_eq] at hzU hzL
          linarith
        rw [h0] at hzre; norm_num at hzre
      · exact hz2 h2'
    have hHUn : AnalyticOn ℂ HU SU := hHU.analyticOn isOpen_SU
    have hHLn : AnalyticOn ℂ HL SL := hHL.analyticOn isOpen_SL
    have hAnalF : ∀ w ∈ SU ∩ SL, AnalyticAt ℂ F w := by
      intro w hw
      have hw' : wC w ∈ SU ∩ SL := wC_mem_SU_SL hw
      rw [hF]
      refine (hHUn.analyticAt (isOpen_SU.mem_nhds hw.1)).add ?_
      exact (hHLn.analyticAt (isOpen_SL.mem_nhds hw'.2)).comp (wC_analyticAt (hne1_of_mem hw))
    have hz' : wC z ∈ SU ∩ SL := wC_mem_SU_SL hz
    have hFan : AnalyticAt ℂ F z := hAnalF z hz
    have hFat : AnalyticAt ℂ F (wC z) := hAnalF (wC z) hz'
    have hGan : AnalyticAt ℂ (F ∘ wC) z := hFat.comp (wC_analyticAt hz1)
    have hFiter : ∀ j, AnalyticAt ℂ (DyIter j F) z := fun j => analyticAt_DyIter hFan hz2ne j
    have hGiter : ∀ j, AnalyticAt ℂ (DyIter j (F ∘ wC)) z :=
      fun j => analyticAt_DyIter hGan hz2ne j
    have hjd : ∀ w ∈ SU ∩ SL, jumpH D w = (fun ζ => F ζ - F (wC ζ)) w := by
      intro w hw
      have hw' : wC w ∈ SU ∩ SL := wC_mem_SU_SL hw
      simp only [jumpH, hF]
      rw [hDj w hw, hDj (wC w) hw', wC_wC w (hne1_of_mem hw)]
      ring
    have hcongr := DyIter_congr_of_eqOn (f := jumpH D) (f' := fun ζ => F ζ - F (wC ζ))
      (isOpen_SU.inter isOpen_SL) hjd k z hz
    have hsub : DyIter k (fun ζ => F ζ - F (wC ζ)) z = DyIter k F z - DyIter k (F ∘ wC) z :=
      DyIter_sub_apply hFiter hGiter k
    have hcomp := DyIter_comp_wC F k z hz1
    rw [hcongr, hsub, hcomp]

end Work.A14D
