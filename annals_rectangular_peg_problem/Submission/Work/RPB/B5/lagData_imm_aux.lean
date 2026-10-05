import Mathlib
import Submission.Work.RPB.B5.LagData
import Submission.Work.RPB.B5.Defs
import Submission.Work.RPV.VBasic
import Submission.Work.RPV.tau_symplectic

/-!
# B5: auxiliary lemmas for the immersion `Work.RPB.B5.lagData_imm`

Shared, reusable lemmas for the proof that the assembled family
`ℓ τ = lagPt W Γc Ac rho τ` is an immersion.  They are collected here (rather than in the main
file) so that the several independent pieces of the immersion proof can be delegated and proved
in parallel against a common interface.

Contents:

* `deriv_eq_of_eqOn_Ioc` — the one-sided transfer of derivatives: two functions that are
  differentiable at `x` and agree on `Ioc (x - ε) x` have the same `deriv` at `x`.  This is what
  lets one compute `deriv` at the *junctions* `x = ±√2`, `x = 0` of `lagPt`, where the formula for
  `lagPt` changes and only one side is available;
* the unfoldings of `lagPt`/`basePt` (branch by branch);
* `contDiff_K0`, and the sections of a `C¹` two-variable function;
* `contDiffAt_W` : for `τ ∈ [0,1]` the chart `W τ · ·` is `C⁸` near every `(t, ρ)` with
  `ρ ∈ Ioo (-ρ₀) ρ₀` (the `ContDiffOn` field `hWsm` of `LagData` restricted to the slice `τ`);
* `deriv_graph`, `fderiv_section_fst`, `fderiv_section_snd` : the chain rules for the two partial
  derivatives of a two-variable function, and their identification with the derivative of a
  section.
-/

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff Topology

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-! ## One-sided transfer of derivatives -/

/-- If `f` and `g` are differentiable at `x` and agree on `Ioc (x - ε) x` (a one-sided
neighbourhood of `x`, with `ε > 0`), then `deriv f x = deriv g x`.

Both derivatives are the limits of the difference quotients; restricted to `y < x` the difference
quotients of `f` and of `g` coincide. -/
theorem deriv_eq_of_eqOn_Ioc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : ℝ → E) {x ε : ℝ} (hε : 0 < ε) (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (h : ∀ y ∈ Set.Ioc (x - ε) x, f y = g y) :
    deriv f x = deriv g x := by
  have hfx : f x = g x := h x ⟨by linarith, le_rfl⟩
  have hle : 𝓝[<] x ≤ 𝓝[≠] x := nhdsWithin_mono x (fun y hy => ne_of_lt hy)
  have hsl : (slope f x) =ᶠ[𝓝[<] x] (slope g x) := by
    rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
    filter_upwards [IsOpen.mem_nhds isOpen_Ioi (show x - ε < x by linarith)] with y hy hyx
    have hy' : f y = g y := h y ⟨hy, le_of_lt hyx⟩
    simp only [slope_fun_def, vsub_eq_sub, hy', hfx]
  have h1 : Filter.Tendsto (slope f x) (𝓝[<] x) (𝓝 (deriv f x)) :=
    (hasDerivAt_iff_tendsto_slope.mp hf.hasDerivAt).mono_left hle
  have h2 : Filter.Tendsto (slope g x) (𝓝[<] x) (𝓝 (deriv f x)) := h1.congr' hsl
  have h3 : Filter.Tendsto (slope g x) (𝓝[<] x) (𝓝 (deriv g x)) :=
    (hasDerivAt_iff_tendsto_slope.mp hg.hasDerivAt).mono_left hle
  exact tendsto_nhds_unique h2 h3

/-! ## Unfolding `lagPt` and `basePt` -/

theorem lagPt_of_nonpos (W : ℝ → ℝ → ℝ → Work.RPV.PS) (Γc : ℝ → ℝ → ℝ → ℂ)
    (Ac : ℝ → ℝ → ℝ → ℝ) (rho : ℝ → ℝ → ℝ → ℝ) {τ x t : ℝ} (hx : x ≤ 0) :
    lagPt W Γc Ac rho τ x t = basePt W Γc Ac rho τ x t := by
  rw [lagPt, if_pos hx]

theorem lagPt_of_pos (W : ℝ → ℝ → ℝ → Work.RPV.PS) (Γc : ℝ → ℝ → ℝ → ℂ)
    (Ac : ℝ → ℝ → ℝ → ℝ) (rho : ℝ → ℝ → ℝ → ℝ) {τ x t : ℝ} (hx : 0 < x) :
    lagPt W Γc Ac rho τ x t
      = Work.RPV.tau Real.pi (basePt W Γc Ac rho τ (-x) (t - Real.pi)) := by
  rw [lagPt, if_neg (not_le.mpr hx)]

theorem basePt_of_le (W : ℝ → ℝ → ℝ → Work.RPV.PS) (Γc : ℝ → ℝ → ℝ → ℂ)
    (Ac : ℝ → ℝ → ℝ → ℝ) (rho : ℝ → ℝ → ℝ → ℝ) {τ x t : ℝ}
    (hx : x ≤ -Real.sqrt 2) :
    basePt W Γc Ac rho τ x t = collarPt Γc Ac τ (sig x) t := by
  rw [basePt, if_pos hx]

theorem basePt_of_gt (W : ℝ → ℝ → ℝ → Work.RPV.PS) (Γc : ℝ → ℝ → ℝ → ℂ)
    (Ac : ℝ → ℝ → ℝ → ℝ) (rho : ℝ → ℝ → ℝ → ℝ) {τ x t : ℝ}
    (hx : -Real.sqrt 2 < x) :
    basePt W Γc Ac rho τ x t = W τ t (rho τ x t) := by
  rw [basePt, if_neg (not_le.mpr hx)]

theorem lagPt_collar (W : ℝ → ℝ → ℝ → Work.RPV.PS) (Γc : ℝ → ℝ → ℝ → ℂ)
    (Ac : ℝ → ℝ → ℝ → ℝ) (rho : ℝ → ℝ → ℝ → ℝ) {τ x t : ℝ}
    (hx : x ≤ -Real.sqrt 2) :
    lagPt W Γc Ac rho τ x t = collarPt Γc Ac τ (sig x) t := by
  have hx0 : x ≤ 0 := by linarith [Real.sqrt_nonneg 2]
  rw [lagPt_of_nonpos W Γc Ac rho hx0, basePt_of_le W Γc Ac rho hx]

theorem lagPt_chart (W : ℝ → ℝ → ℝ → Work.RPV.PS) (Γc : ℝ → ℝ → ℝ → ℂ)
    (Ac : ℝ → ℝ → ℝ → ℝ) (rho : ℝ → ℝ → ℝ → ℝ) {τ x t : ℝ}
    (hx1 : -Real.sqrt 2 < x) (hx2 : x ≤ 0) :
    lagPt W Γc Ac rho τ x t = W τ t (rho τ x t) := by
  rw [lagPt_of_nonpos W Γc Ac rho hx2, basePt_of_gt W Γc Ac rho hx1]

/-! ## Smoothness of `K₀`, and sections of a `C¹` function -/

/-- `K₀` is smooth (as a function on `PS = ℝ⁴`).  We only need `C¹`. -/
theorem contDiff_K0 : ContDiff ℝ 1 (fun x : Work.RPV.PS => Work.RPV.K0 x) := by
  simp only [Work.RPV.K0]
  fun_prop

/-- The first section of a `C¹` function of two variables is differentiable. -/
theorem differentiableAt_slice_fst {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ × ℝ → E} {x t : ℝ} (hF : ContDiffAt ℝ 1 F (x, t)) :
    DifferentiableAt ℝ (fun y : ℝ => F (y, t)) x := by
  have h1 : DifferentiableAt ℝ (fun y : ℝ => ((y, t) : ℝ × ℝ)) x := by
    simpa only [id_eq] using
      (differentiableAt_id (x := x)).prodMk (differentiableAt_const (x := x) t)
  simpa only [Function.comp_def] using (hF.differentiableAt (by norm_num)).comp x h1

/-- The second section of a `C¹` function of two variables is differentiable. -/
theorem differentiableAt_slice_snd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ × ℝ → E} {x t : ℝ} (hF : ContDiffAt ℝ 1 F (x, t)) :
    DifferentiableAt ℝ (fun s : ℝ => F (x, s)) t := by
  have h1 : DifferentiableAt ℝ (fun s : ℝ => ((x, s) : ℝ × ℝ)) t := by
    simpa only [id_eq] using
      (differentiableAt_const (x := t) x).prodMk (differentiableAt_id (x := t))
  simpa only [Function.comp_def] using (hF.differentiableAt (by norm_num)).comp t h1

/-- The derivative of the first section of a two-variable function, in terms of `fderiv`. -/
theorem hasDerivAt_slice_fst {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ × ℝ → E} {x t : ℝ} (hF : DifferentiableAt ℝ F (x, t)) :
    HasDerivAt (fun y : ℝ => F (y, t)) (fderiv ℝ F (x, t) ((1 : ℝ), (0 : ℝ))) x := by
  have h1 : HasDerivAt (fun y : ℝ => ((y, t) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) x :=
    (hasDerivAt_id x).prodMk (hasDerivAt_const x t)
  simpa only [Function.comp_def] using hF.hasFDerivAt.comp_hasDerivAt x h1

/-- The derivative of the second section of a two-variable function, in terms of `fderiv`. -/
theorem hasDerivAt_slice_snd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ × ℝ → E} {x t : ℝ} (hF : DifferentiableAt ℝ F (x, t)) :
    HasDerivAt (fun s : ℝ => F (x, s)) (fderiv ℝ F (x, t) ((0 : ℝ), (1 : ℝ))) t := by
  have h1 : HasDerivAt (fun s : ℝ => ((x, s) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) t :=
    (hasDerivAt_const t x).prodMk (hasDerivAt_id t)
  simpa only [Function.comp_def] using hF.hasFDerivAt.comp_hasDerivAt t h1

/-! ## The chart `W` on a slice `τ ∈ [0,1]` -/

/-- For `τ ∈ Icc 0 1` the chart `W τ · ·` is `C⁸` (and hence `C¹`) near each `(t, ρ)` with
`ρ ∈ Ioo (-ρ₀) ρ₀` : the `ContDiffOn` field `hWsm` of `LagData` restricted to the slice. -/
theorem contDiffAt_W (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (D : Work.RPB.B5.LagData CI a) {τ t ρ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (hρ : ρ ∈ Set.Ioo (-D.ρ₀) D.ρ₀) :
    ContDiffAt ℝ 8 (fun z : ℝ × ℝ => D.W τ z.1 z.2) (t, ρ) := by
  set G : ℝ × (ℝ × ℝ) → Work.RPV.PS := fun z => D.W z.1 z.2.1 z.2.2 with hG
  have hpt : (τ, t, ρ) ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-D.ρ₀) D.ρ₀ :=
    ⟨hτ, Set.mem_univ _, hρ⟩
  have hGcd : ContDiffWithinAt ℝ 8 G
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-D.ρ₀) D.ρ₀) (τ, t, ρ) :=
    D.hWsm.contDiffWithinAt hpt
  have hφ : ContDiffWithinAt ℝ 8 (fun z : ℝ × ℝ => (τ, (z.1, z.2)))
      (Set.univ ×ˢ Set.Ioo (-D.ρ₀) D.ρ₀) (t, ρ) :=
    (by fun_prop : ContDiff ℝ 8 (fun z : ℝ × ℝ => (τ, (z.1, z.2)))).contDiffWithinAt
  have hmt : Set.MapsTo (fun z : ℝ × ℝ => (τ, (z.1, z.2)))
      (Set.univ ×ˢ Set.Ioo (-D.ρ₀) D.ρ₀)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-D.ρ₀) D.ρ₀) :=
    fun z hz => ⟨hτ, Set.mem_univ _, hz.2⟩
  have hU : (Set.univ ×ˢ Set.Ioo (-D.ρ₀) D.ρ₀) ∈ 𝓝 (t, ρ) := by
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod Filter.univ_mem (isOpen_Ioo.mem_nhds hρ)
  have h := (hGcd.comp (t, ρ) hφ hmt).contDiffAt hU
  simpa only [hG, Function.comp_def] using h

/-- `W τ · ·` is `C¹` near `(t,ρ)`, in the form needed for the chain rules. -/
theorem contDiffAt_W_one (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (D : Work.RPB.B5.LagData CI a) {τ t ρ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (hρ : ρ ∈ Set.Ioo (-D.ρ₀) D.ρ₀) :
    ContDiffAt ℝ 1 (fun z : ℝ × ℝ => D.W τ z.1 z.2) (t, ρ) :=
  (contDiffAt_W CI a D hτ hρ).of_le (by norm_num)

/-! ## Chain rules for the partial derivatives of a two-variable function -/

/-- The derivative of `s ↦ Ψ (s, h s)` in terms of the two partial derivatives of `Ψ`. -/
theorem deriv_graph {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ψ : ℝ × ℝ → E) (h : ℝ → ℝ) (L : ℝ × ℝ →L[ℝ] E) {t : ℝ}
    (hΨ : HasFDerivAt Ψ L (t, h t)) (hh : HasDerivAt h (deriv h t) t) :
    deriv (fun s : ℝ => Ψ (s, h s)) t
      = L ((1 : ℝ), (0 : ℝ)) + deriv h t • L ((0 : ℝ), (1 : ℝ)) := by
  have hg : HasDerivAt (fun s : ℝ => ((s, h s) : ℝ × ℝ)) ((1 : ℝ), deriv h t) t :=
    (hasDerivAt_id t).prodMk hh
  have hcomp : HasDerivAt (fun s : ℝ => Ψ (s, h s)) (L ((1 : ℝ), deriv h t)) t := by
    simpa only [Function.comp_def] using hΨ.comp_hasDerivAt t hg
  rw [hcomp.deriv]
  have hvec : ((1 : ℝ), deriv h t) = ((1 : ℝ), (0 : ℝ)) + deriv h t • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [hvec, map_add, map_smul]

/-- The derivative of `s ↦ Ψ (s, h s)` for a differentiable `h`. -/
theorem deriv_graph_of_differentiableAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ψ : ℝ × ℝ → E) (h : ℝ → ℝ) {t : ℝ} (hΨ : DifferentiableAt ℝ Ψ (t, h t))
    (hh : DifferentiableAt ℝ h t) :
    deriv (fun s : ℝ => Ψ (s, h s)) t
      = fderiv ℝ Ψ (t, h t) ((1 : ℝ), (0 : ℝ))
        + deriv h t • fderiv ℝ Ψ (t, h t) ((0 : ℝ), (1 : ℝ)) :=
  deriv_graph Ψ h (fderiv ℝ Ψ (t, h t)) hΨ.hasFDerivAt hh.hasDerivAt

/-- The derivative of the first section of a two-variable function is its `fderiv` on the first
basis vector. -/
theorem fderiv_section_fst {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ψ : ℝ × ℝ → E) (L : ℝ × ℝ →L[ℝ] E) {t ρ : ℝ} (hΨ : HasFDerivAt Ψ L (t, ρ)) :
    deriv (fun s : ℝ => Ψ (s, ρ)) t = L ((1 : ℝ), (0 : ℝ)) := by
  have h1 : HasDerivAt (fun y : ℝ => ((y, ρ) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t ρ)
  have hcomp : HasDerivAt (fun s : ℝ => Ψ (s, ρ)) (L ((1 : ℝ), (0 : ℝ))) t := by
    simpa only [Function.comp_def] using hΨ.comp_hasDerivAt t h1
  exact hcomp.deriv

/-- The derivative of the second section of a two-variable function is its `fderiv` on the second
basis vector. -/
theorem fderiv_section_snd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ψ : ℝ × ℝ → E) (L : ℝ × ℝ →L[ℝ] E) {t ρ : ℝ} (hΨ : HasFDerivAt Ψ L (t, ρ)) :
    deriv (fun s : ℝ => Ψ (t, s)) ρ = L ((0 : ℝ), (1 : ℝ)) := by
  have h1 : HasDerivAt (fun y : ℝ => ((t, y) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) ρ :=
    (hasDerivAt_const ρ t).prodMk (hasDerivAt_id ρ)
  have hcomp : HasDerivAt (fun s : ℝ => Ψ (t, s)) (L ((0 : ℝ), (1 : ℝ))) ρ := by
    simpa only [Function.comp_def] using hΨ.comp_hasDerivAt ρ h1
  exact hcomp.deriv

/-- The `x`-derivative of a one-variable composition `y ↦ F (g y)` is `g'(x) • F'(g x)`. -/
theorem differentiableAt_uproj (x : Work.RPV.PS) :
    DifferentiableAt ℝ (fun y : Work.RPV.PS => Work.RPV.uproj y) x := by
  simp only [Work.RPV.uproj]
  fun_prop

/-- `tauLinear π` (the linear part of the chord swap `tau π`) is injective. -/
theorem tauLinear_pi_injective : Function.Injective (Work.RPV.tauLinear Real.pi) := by
  intro a b hab
  have h : Work.RPV.tauLinear Real.pi (a - b) = 0 := by rw [map_sub, hab, sub_self]
  rw [Work.RPV.tauLinear_apply] at h
  have h1 : (a - b).1.1 = 0 := by
    have hh : Real.cos Real.pi * (a - b).1.1 - Real.sin Real.pi * (a - b).2.1 = 0 := by
      simpa using congrArg (fun y : Work.RPV.PS => y.1.1) h
    rw [Real.cos_pi, Real.sin_pi] at hh
    linarith
  have h2 : (a - b).1.2 = 0 := by
    simpa using congrArg (fun y : Work.RPV.PS => y.1.2) h
  have h3 : (a - b).2.1 = 0 := by
    have hh : Real.sin Real.pi * (a - b).1.1 + Real.cos Real.pi * (a - b).2.1 = 0 := by
      simpa using congrArg (fun y : Work.RPV.PS => y.2.1) h
    rw [Real.cos_pi, Real.sin_pi] at hh
    linarith
  have h4 : (a - b).2.2 = 0 := by
    simpa using congrArg (fun y : Work.RPV.PS => y.2.2) h
  have hab0 : a - b = 0 := by ext <;> simp_all
  exact sub_eq_zero.mp hab0

theorem deriv_comp_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → E) (g : ℝ → ℝ) (x : ℝ) (hF : DifferentiableAt ℝ F (g x))
    (hg : DifferentiableAt ℝ g x) :
    deriv (fun y => F (g y)) x = deriv g x • deriv F (g x) := by
  have h := hF.hasFDerivAt.comp_hasDerivAt x hg.hasDerivAt
  have hd : deriv (fun y => F (g y)) x = fderiv ℝ F (g x) (deriv g x) := by
    simpa only [Function.comp_def] using h.deriv
  rw [hd, fderiv_eq_smul_deriv]

end Work.RPB.B5
