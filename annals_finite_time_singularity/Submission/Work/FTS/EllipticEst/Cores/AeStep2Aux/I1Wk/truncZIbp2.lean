import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.CurrySmooth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The `θ`-integrated radial integration by parts with tests `χ`, `ψ`

We prove `I1Wk.truncZIbp2`: for `u` of class `C^∞` on the open quadrant, `χ ∈ C¹_c((0,∞))`
and `ψ ∈ C¹` with `tsupport ψ ⊆ (0,π/2)`,

`∫_z ∫_θ χ w² σ ψ (z²∂_z²u)(∂_θ²u)
  = - ∫_z ∫_θ (∂_z(χ w² z²)/z) σ ψ (z∂_zu)(∂_θ²u)
    - ∫_z ∫_θ χ w² σ ψ (z∂_zu)(z∂_z∂_θ²u)`,  `σ = sin(2θ)^{-η}`.

This is `∫_z ∂_z[(χ w² z²)·∂_zu·∂_θ²u] = 0` for every fixed `θ` (the radial integration by
parts, whose boundary terms vanish because `χ` is compactly supported away from `0` —
`tsupport χ ⊆ (0,∞)` — and `ψ` is supported in a compact subinterval of `(0,π/2)`), followed
by Fubini in `(z,θ)`.
-/

/-! ## Notation -/

private abbrev qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)

private lemma isOpen_qd : IsOpen qd := isOpen_Ioi.prod isOpen_Ioo

/-- The angular weight `σ θ = sin(2θ)^{-η}`. -/
private def sg (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

/-- The radial weight `ω(z) = χ(z)·w(z)²·z²`. -/
private def om (χ : ℝ → ℝ) (z : ℝ) : ℝ := χ z * (Work.Spaces.w z) ^ 2 * z ^ 2

/-- The boundary primitive of the `z`-integral. -/
private def prim (u : ℝ → ℝ → ℝ) (χ ψ : ℝ → ℝ) (z θ : ℝ) : ℝ :=
  om χ z * sg θ * ψ θ * Work.Spaces.pz u z θ * Work.Spaces.pthIter 2 u z θ

/-- The left-hand integrand. -/
private def J1 (u : ℝ → ℝ → ℝ) (χ ψ : ℝ → ℝ) (z θ : ℝ) : ℝ :=
  om χ z * sg θ * ψ θ * Work.Spaces.pzIter 2 u z θ * Work.Spaces.pthIter 2 u z θ

/-- The first right-hand integrand. -/
private def J2 (u : ℝ → ℝ → ℝ) (χ ψ : ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (deriv (om χ) z / z) * sg θ * ψ θ * (z * Work.Spaces.pz u z θ)
    * Work.Spaces.pthIter 2 u z θ

/-- The second right-hand integrand. -/
private def J3 (u : ℝ → ℝ → ℝ) (χ ψ : ℝ → ℝ) (z θ : ℝ) : ℝ :=
  om χ z * sg θ * ψ θ * Work.Spaces.pz u z θ
    * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ

/-- The `z`-derivative of the boundary primitive. -/
private def J4 (u : ℝ → ℝ → ℝ) (χ ψ : ℝ → ℝ) (z θ : ℝ) : ℝ :=
  deriv (fun z' => prim u χ ψ z' θ) z

private theorem sg_rfl (θ : ℝ) : sg θ = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := rfl

private theorem om_rfl (χ : ℝ → ℝ) (z : ℝ) : om χ z = χ z * (Work.Spaces.w z) ^ 2 * z ^ 2 := rfl

private theorem prim_rfl (u : ℝ → ℝ → ℝ) (χ ψ : ℝ → ℝ) (z θ : ℝ) :
    prim u χ ψ z θ = om χ z * sg θ * ψ θ * Work.Spaces.pz u z θ
      * Work.Spaces.pthIter 2 u z θ := rfl

private theorem J1_rfl (u : ℝ → ℝ → ℝ) (χ ψ : ℝ → ℝ) (z θ : ℝ) :
    J1 u χ ψ z θ = om χ z * sg θ * ψ θ * Work.Spaces.pzIter 2 u z θ
      * Work.Spaces.pthIter 2 u z θ := rfl

private theorem J2_rfl (u : ℝ → ℝ → ℝ) (χ ψ : ℝ → ℝ) (z θ : ℝ) :
    J2 u χ ψ z θ = (deriv (om χ) z / z) * sg θ * ψ θ * (z * Work.Spaces.pz u z θ)
      * Work.Spaces.pthIter 2 u z θ := rfl

private theorem J3_rfl (u : ℝ → ℝ → ℝ) (χ ψ : ℝ → ℝ) (z θ : ℝ) :
    J3 u χ ψ z θ = om χ z * sg θ * ψ θ * Work.Spaces.pz u z θ
      * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ := rfl

private theorem J4_rfl (u : ℝ → ℝ → ℝ) (χ ψ : ℝ → ℝ) (z θ : ℝ) :
    J4 u χ ψ z θ = deriv (fun z' => prim u χ ψ z' θ) z := rfl

/-! ## Calculus on the open quadrant -/

/-- `Work.Spaces.pz` lowers the order of smoothness by one (open set, finite order). -/
private theorem contDiffOn_uncurry_pz_fin {n : ℕ} {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pz G)) V := by
  have hchain : ∀ p ∈ V,
      Work.Spaces.pz G p.1 p.2 = fderiv ℝ (Function.uncurry G) p (1, 0) :=
    fun p hp => Work.Spaces.pz_eq_fderiv
      ((h.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V :=
    h.fderiv_of_isOpen hV (m := n) (by simp)
  have hcomp : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (1, 0)) V := by
    simpa using hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-- `Work.Spaces.pth` lowers the order of smoothness by one (open set, finite order). -/
private theorem contDiffOn_uncurry_pth_fin {n : ℕ} {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth G)) V := by
  have hchain : ∀ p ∈ V,
      Work.Spaces.pth G p.1 p.2 = fderiv ℝ (Function.uncurry G) p (0, 1) :=
    fun p hp => Work.Spaces.pth_eq_fderiv
      ((h.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V :=
    h.fderiv_of_isOpen hV (m := n) (by simp)
  have hcomp : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (0, 1)) V := by
    simpa using hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-- The `z`-slices of a function which is `C^n` on an open set are `C^n`. -/
private theorem contDiffOn_zslice {G : ℝ → ℝ → ℝ} {n : WithTop ℕ∞} {V : Set (ℝ × ℝ)}
    (_hV : IsOpen V) (h : ContDiffOn ℝ n (Function.uncurry G) V) {θ : ℝ} {W : Set ℝ}
    (_hW : IsOpen W) (hmem : ∀ z ∈ W, (z, θ) ∈ V) :
    ContDiffOn ℝ n (fun z => G z θ) W := by
  have hf : ContDiffOn ℝ n (fun z : ℝ => (z, θ)) W :=
    ContDiffOn.prodMk contDiffOn_id (contDiffOn_const (c := θ))
  have h2 := h.comp hf hmem
  simpa [Function.comp_def, Function.uncurry] using h2

/-! ## The weight `ω = χ w² z²` -/

private theorem contDiffOn_om (χ : ℝ → ℝ) (hχ : ContDiff ℝ 1 χ) :
    ContDiffOn ℝ 1 (om χ) (Set.Ioi 0) := by
  have hχ' : ContDiffOn ℝ 1 χ (Set.Ioi 0) := hχ.contDiffOn
  have hw2 : ContDiffOn ℝ 1 (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
    have hnum : ContDiffOn ℝ 1 (fun z : ℝ => ((1 + z) ^ 2) ^ 2) (Set.Ioi 0) := by fun_prop
    have hden : ContDiffOn ℝ 1 (fun z : ℝ => (z ^ 2) ^ 2) (Set.Ioi 0) := by fun_prop
    have hne : ∀ z ∈ Set.Ioi (0 : ℝ), (z ^ 2) ^ 2 ≠ 0 := fun z hz =>
      pow_ne_zero _ (pow_ne_zero _ (ne_of_gt (show (0 : ℝ) < z from hz)))
    refine (hnum.div hden hne).congr ?_
    intro z _
    simp only [Pi.div_apply, Work.Spaces.w, div_pow]
  have hz2 : ContDiffOn ℝ 1 (fun z : ℝ => z ^ 2) (Set.Ioi 0) := by fun_prop
  exact (hχ'.mul hw2).mul hz2

/-- The boundary primitive vanishes where its weight does. -/
private theorem prim_zero_off {u : ℝ → ℝ → ℝ} {χ ψ : ℝ → ℝ} {a b : ℝ}
    (hω0 : ∀ z : ℝ, z ∉ Set.Icc a b → om χ z = 0) :
    ∀ z θ : ℝ, z ∉ Set.Icc a b → prim u χ ψ z θ = 0 := by
  intro z θ hz
  rw [prim_rfl, hω0 z hz]
  ring

/-- The derivative of a function vanishing off `[a,b]` vanishes off `[a,b]`. -/
private theorem deriv_eq_zero_off {F : ℝ → ℝ} {a b : ℝ}
    (h : ∀ z, z ∉ Set.Icc a b → F z = 0) :
    ∀ z, z ∉ Set.Icc a b → deriv F z = 0 := by
  intro z hz
  have hz' : z < a ∨ b < z := by
    simpa only [Set.mem_Icc, not_and_or, not_le] using hz
  have hev : F =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
    rcases hz' with hlt | hgt
    · filter_upwards [isOpen_Iio.mem_nhds hlt] with y hy
      exact h y (by simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inl hy)
    · filter_upwards [isOpen_Ioi.mem_nhds hgt] with y hy
      exact h y (by simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inr hy)
  rw [hev.deriv_eq]
  simp

/-! ## The angular weight `σ` and the two support separations -/

private theorem continuousOn_sg {c d : ℝ} (hc : 0 < c) (hd : d < Real.pi / 2) :
    ContinuousOn sg (Set.Icc c d) := by
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Icc c d) := by fun_prop
  refine ContinuousOn.rpow hsin continuousOn_const ?_
  intro θ hθ
  exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, hc])
    (by linarith [hθ.2, hd])))

/-- A compactly supported function whose (closed) support avoids `0` vanishes off a compact
interval `[a,b]` with `0 < a ≤ b`. -/
private theorem exists_sep_chi {χ : ℝ → ℝ} (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Set.Ioi (0 : ℝ)) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ ∀ z : ℝ, z ∉ Set.Icc a b → χ z = 0 := by
  have hcomp : IsCompact (tsupport χ) := hc.isCompact
  have hne : (0 : ℝ) ∉ tsupport χ := fun h => lt_irrefl 0 (Set.mem_Ioi.mp (hs h))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    ((isClosed_tsupport χ).isOpen_compl.mem_nhds hne)
  obtain ⟨R, hR⟩ := hcomp.isBounded.subset_closedBall (0 : ℝ)
  refine ⟨min (ε / 2) 1, max R 1, lt_min (by linarith) one_pos, ?_, ?_⟩
  · exact le_trans (min_le_right _ _) (le_max_right _ _)
  · intro z hz
    by_contra hzc
    have hzmem : z ∈ tsupport χ := subset_tsupport χ (Function.mem_support.mpr hzc)
    have hz0 : 0 < z := hs hzmem
    have hza : min (ε / 2) 1 ≤ z := by
      have hge : ε ≤ z := by
        by_contra hlt
        push Not at hlt
        have hb : z ∈ Metric.ball (0 : ℝ) ε := by
          simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hz0]
          exact hlt
        exact (hball hb) hzmem
      exact le_trans (min_le_left _ _) (by linarith)
    have hzb : z ≤ max R 1 := by
      have hmem := hR hzmem
      simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hmem
      exact le_trans (le_trans (le_abs_self z) hmem) (le_max_left _ _)
    exact hz ⟨hza, hzb⟩

/-- A function whose (closed) support is contained in `(0,π/2)` vanishes off a compact
interval `[c,d]` with `0 < c ≤ d < π/2`. -/
private theorem exists_sep_psi {ψ : ℝ → ℝ} (hs : tsupport ψ ⊆ Set.Ioo 0 (Real.pi / 2)) :
    ∃ c d : ℝ, 0 < c ∧ c ≤ d ∧ d < Real.pi / 2 ∧
      ∀ θ : ℝ, θ ∉ Set.Icc c d → ψ θ = 0 := by
  have hbdd : Bornology.IsBounded (tsupport ψ) := by
    refine (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mpr ⟨Real.pi / 2, ?_⟩
    intro z hz
    have hz' := hs hz
    simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [hz'.1, Real.pi_pos], le_of_lt hz'.2⟩
  have hne0 : (0 : ℝ) ∉ tsupport ψ := fun h => lt_irrefl 0 (hs h).1
  have hne1 : (Real.pi / 2) ∉ tsupport ψ := fun h => lt_irrefl _ (hs h).2
  obtain ⟨ε, hε, hball0⟩ := Metric.mem_nhds_iff.mp
    ((isClosed_tsupport ψ).isOpen_compl.mem_nhds hne0)
  obtain ⟨δ, hδ, hball1⟩ := Metric.mem_nhds_iff.mp
    ((isClosed_tsupport ψ).isOpen_compl.mem_nhds hne1)
  refine ⟨min (ε / 2) (Real.pi / 4), max (Real.pi / 4) (Real.pi / 2 - δ / 2),
    lt_min (by linarith) (by linarith [Real.pi_pos]), ?_, ?_, ?_⟩
  · exact le_trans (min_le_right _ _) (le_max_left _ _)
  · exact max_lt (by linarith [Real.pi_pos]) (by linarith)
  · intro θ hθ
    by_contra hne
    have hmem : θ ∈ tsupport ψ := subset_tsupport ψ (Function.mem_support.mpr hne)
    have hθ' := hs hmem
    have hge : ε ≤ θ := by
      by_contra hlt
      push Not at hlt
      have hb : θ ∈ Metric.ball (0 : ℝ) ε := by
        simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs,
          abs_of_pos hθ'.1]
        exact hlt
      exact (hball0 hb) hmem
    have hle : δ ≤ Real.pi / 2 - θ := by
      by_contra hlt
      push Not at hlt
      have hb : θ ∈ Metric.ball (Real.pi / 2) δ := by
        rw [Metric.mem_ball, Real.dist_eq,
          abs_of_neg (show θ - Real.pi / 2 < 0 by linarith [hθ'.2])]
        linarith
      exact (hball1 hb) hmem
    exact hθ ⟨le_trans (min_le_left _ _) (by linarith),
      le_trans (by linarith) (le_max_right _ _)⟩

/-! ## Smoothness of the derivative factors -/

private theorem contDiffOn_pz_one {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) qd) :
    ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz u)) qd :=
  contDiffOn_uncurry_pz_fin isOpen_qd (n := 1) (hu 2)

private theorem contDiffOn_pzIter_two {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) qd) :
    ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pzIter 2 u)) qd := by
  have hp : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pz u)) qd :=
    contDiffOn_uncurry_pz_fin isOpen_qd (n := 2) (hu 3)
  have hp2 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz (Work.Spaces.pz u))) qd :=
    contDiffOn_uncurry_pz_fin isOpen_qd (n := 1) hp
  simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using hp2

private theorem contDiffOn_pthIter_two {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) qd) :
    ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pthIter 2 u)) qd := by
  have hp : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pth u)) qd :=
    contDiffOn_uncurry_pth_fin isOpen_qd (n := 2) (hu 3)
  have hp2 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth u))) qd :=
    contDiffOn_uncurry_pth_fin isOpen_qd (n := 1) hp
  simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using hp2

private theorem contDiffOn_pz_pth2 {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) qd) :
    ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz (Work.Spaces.pthIter 2 u))) qd := by
  have h1 : ContDiffOn ℝ 3 (Function.uncurry (Work.Spaces.pth u)) qd :=
    contDiffOn_uncurry_pth_fin isOpen_qd (n := 3) (hu 4)
  have h2 : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth u))) qd :=
    contDiffOn_uncurry_pth_fin isOpen_qd (n := 2) h1
  have h3 : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pthIter 2 u)) qd := by
    simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using h2
  exact contDiffOn_uncurry_pz_fin isOpen_qd (n := 1) h3

/-! ## The `z`-derivative of the slices -/

private theorem hasDerivAt_pz_slice {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) qd) {z θ : ℝ}
    (hz : 0 < z) (hθ1 : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    HasDerivAt (fun z' => Work.Spaces.pz u z' θ) (Work.Spaces.pzIter 2 u z θ) z := by
  have hslice : ContDiffOn ℝ 1 (fun z => Work.Spaces.pz u z θ) (Set.Ioi 0) :=
    contDiffOn_zslice isOpen_qd (contDiffOn_pz_one hu) isOpen_Ioi
      (fun z hz => ⟨hz, hθ1, hθ2⟩)
  have h := ((hslice.differentiableOn (by norm_num)).differentiableAt
    (isOpen_Ioi.mem_nhds hz)).hasDerivAt
  have h2 : Work.Spaces.pzIter 2 u z θ = deriv (fun z' => Work.Spaces.pz u z' θ) z := rfl
  rw [h2]
  exact h

private theorem hasDerivAt_pth2_slice {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) qd) {z θ : ℝ}
    (hz : 0 < z) (hθ1 : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    HasDerivAt (fun z' => Work.Spaces.pthIter 2 u z' θ)
      (Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ) z := by
  have hslice : ContDiffOn ℝ 1 (fun z => Work.Spaces.pthIter 2 u z θ) (Set.Ioi 0) :=
    contDiffOn_zslice isOpen_qd (contDiffOn_pthIter_two hu) isOpen_Ioi
      (fun z hz => ⟨hz, hθ1, hθ2⟩)
  have h := ((hslice.differentiableOn (by norm_num)).differentiableAt
    (isOpen_Ioi.mem_nhds hz)).hasDerivAt
  have h2 : Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ
      = deriv (fun z' => Work.Spaces.pthIter 2 u z' θ) z := rfl
  rw [h2]
  exact h

/-! ## The pointwise derivative identity on the open quadrant -/

/-- On `z ≠ 0` the first right-hand integrand is `∂_zω·σψ·∂_zu·∂_θ²u`. -/
private theorem J2_eq {u : ℝ → ℝ → ℝ} {χ ψ : ℝ → ℝ} {z θ : ℝ} (hz : z ≠ 0) :
    J2 u χ ψ z θ = deriv (om χ) z * sg θ * ψ θ * Work.Spaces.pz u z θ
      * Work.Spaces.pthIter 2 u z θ := by
  have h : deriv (om χ) z / z * z = deriv (om χ) z := div_mul_cancel₀ _ hz
  calc J2 u χ ψ z θ
      = (deriv (om χ) z / z * z) * (sg θ * ψ θ * Work.Spaces.pz u z θ
          * Work.Spaces.pthIter 2 u z θ) := by rw [J2_rfl]; ring
    _ = deriv (om χ) z * sg θ * ψ θ * Work.Spaces.pz u z θ
          * Work.Spaces.pthIter 2 u z θ := by rw [h]; ring

/-- The pointwise identity `J1 + J2 + J3 = J4` on the open quadrant. -/
private theorem hasDerivAt_prim_slice {u : ℝ → ℝ → ℝ} (χ ψ : ℝ → ℝ)
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) qd)
    (hχ : ContDiff ℝ 1 χ) {z θ : ℝ} (hz : 0 < z) (hθ1 : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    HasDerivAt (fun z' => prim u χ ψ z' θ)
      (J1 u χ ψ z θ + J2 u χ ψ z θ + J3 u χ ψ z θ) z := by
  have hω : HasDerivAt (om χ) (deriv (om χ) z) z :=
    ((contDiffOn_om χ hχ).differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds hz) |>.hasDerivAt
  have hA : HasDerivAt (fun z' => Work.Spaces.pz u z' θ)
      (Work.Spaces.pzIter 2 u z θ) z := hasDerivAt_pz_slice hu hz hθ1 hθ2
  have hB : HasDerivAt (fun z' => Work.Spaces.pthIter 2 u z' θ)
      (Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ) z :=
    hasDerivAt_pth2_slice hu hz hθ1 hθ2
  have hc1 : HasDerivAt (fun _ : ℝ => sg θ) 0 z := hasDerivAt_const z (sg θ)
  have hc2 : HasDerivAt (fun _ : ℝ => ψ θ) 0 z := hasDerivAt_const z (ψ θ)
  have hall : HasDerivAt
      (fun z' => om χ z' * sg θ * ψ θ * Work.Spaces.pz u z' θ
        * Work.Spaces.pthIter 2 u z' θ)
      (J1 u χ ψ z θ + J2 u χ ψ z θ + J3 u χ ψ z θ) z := by
    have h0 := (((hω.mul hc1).mul hc2).mul hA).mul hB
    refine h0.congr_deriv ?_
    simp only [Pi.mul_apply, mul_zero, add_zero]
    rw [J2_eq (ne_of_gt hz), J1_rfl, J3_rfl]
    ring
  have hfun : (fun z' => prim u χ ψ z' θ) = fun z' => om χ z' * sg θ * ψ θ
      * Work.Spaces.pz u z' θ * Work.Spaces.pthIter 2 u z' θ := by
    funext z'
    rw [prim_rfl]
  rw [hfun]
  exact hall

private theorem J1_add_J2_add_J3_eq_J4 {u : ℝ → ℝ → ℝ} {χ ψ : ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) qd)
    (hχ : ContDiff ℝ 1 χ) {z θ : ℝ} (hz : 0 < z) (hθ1 : 0 < θ)
    (hθ2 : θ < Real.pi / 2) :
    J1 u χ ψ z θ + J2 u χ ψ z θ + J3 u χ ψ z θ = J4 u χ ψ z θ :=
  (hasDerivAt_prim_slice χ ψ hu hχ hz hθ1 hθ2).deriv.symm

/-! ## The per-angle radial integration by parts -/

private theorem slice_integral_zero {u : ℝ → ℝ → ℝ} (χ ψ : ℝ → ℝ)
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) qd)
    (hχ : ContDiff ℝ 1 χ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hω0 : ∀ z : ℝ, z ∉ Set.Icc a b → om χ z = 0)
    {θ : ℝ} (hθ1 : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    (∫ z in Set.Ioi 0, deriv (fun z' => prim u χ ψ z' θ) z) = 0 := by
  have hωd : ContDiffOn ℝ 1 (om χ) (Set.Ioi 0) := contDiffOn_om χ hχ
  have hpz : ContDiffOn ℝ 1 (fun z => Work.Spaces.pz u z θ) (Set.Ioi 0) :=
    contDiffOn_zslice isOpen_qd (contDiffOn_pz_one hu) isOpen_Ioi
      (fun z hz => ⟨hz, hθ1, hθ2⟩)
  have hpth : ContDiffOn ℝ 1 (fun z => Work.Spaces.pthIter 2 u z θ) (Set.Ioi 0) :=
    contDiffOn_zslice isOpen_qd (contDiffOn_pthIter_two hu) isOpen_Ioi
      (fun z hz => ⟨hz, hθ1, hθ2⟩)
  set G : ℝ → ℝ := fun z => prim u χ ψ z θ with hGdef
  have hG1 : ContDiffOn ℝ 1 G (Set.Ioi 0) := by
    have h1 : ContDiffOn ℝ 1 (fun z : ℝ => om χ z * sg θ) (Set.Ioi 0) :=
      ContDiffOn.mul hωd contDiffOn_const
    have h2 : ContDiffOn ℝ 1 (fun z : ℝ => om χ z * sg θ * ψ θ) (Set.Ioi 0) :=
      ContDiffOn.mul h1 contDiffOn_const
    have h3 : ContDiffOn ℝ 1
        (fun z : ℝ => om χ z * sg θ * ψ θ * Work.Spaces.pz u z θ) (Set.Ioi 0) :=
      ContDiffOn.mul h2 hpz
    have h4 : ContDiffOn ℝ 1
        (fun z : ℝ => om χ z * sg θ * ψ θ * Work.Spaces.pz u z θ
          * Work.Spaces.pthIter 2 u z θ) (Set.Ioi 0) :=
      ContDiffOn.mul h3 hpth
    rw [hGdef]
    exact h4
  have hGoff : ∀ z, 0 < z → (z < a ∨ b < z) → G z = 0 := by
    intro z hz hc
    have hzc : z ∉ Set.Icc a b := by
      intro hmem
      rcases hc with h | h <;> linarith [hmem.1, hmem.2]
    exact prim_zero_off hω0 z θ hzc
  have hGderiv_off : ∀ z, 0 < z → (z < a ∨ b < z) → deriv G z = 0 := by
    intro z hz hc
    have hev : G =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
      rcases hc with hlt | hgt
      · filter_upwards [isOpen_Ioo.mem_nhds (show z ∈ Set.Ioo 0 a from ⟨hz, hlt⟩)]
          with y hy
        exact hGoff y hy.1 (Or.inl hy.2)
      · filter_upwards [isOpen_Ioo.mem_nhds
          (show z ∈ Set.Ioo b (z + 1) from ⟨hgt, by linarith⟩)] with y hy
        exact hGoff y (by linarith [hy.1, hgt, ha]) (Or.inr hy.1)
    rw [hev.deriv_eq]
    simp
  have hsub : Set.Icc (a / 2) (b + 1) ⊆ Set.Ioi (0 : ℝ) := fun z hz => by
    simp only [Set.mem_Ioi]; linarith [hz.1, ha]
  have hcontG : ContinuousOn G (Set.Icc (a / 2) (b + 1)) := hG1.continuousOn.mono hsub
  have hderivG : ContinuousOn (deriv G) (Set.Icc (a / 2) (b + 1)) :=
    (hG1.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).mono hsub
  have hGint : IntervalIntegrable (deriv G) volume (a / 2) (b + 1) :=
    ContinuousOn.intervalIntegrable_of_Icc (by linarith) hderivG
  have hFTC : (∫ x in (a / 2)..(b + 1), deriv G x) = 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (show a / 2 ≤ b + 1 by linarith)
      hcontG (fun x hx => ((hG1.differentiableOn (by norm_num)).differentiableAt
        (isOpen_Ioi.mem_nhds (hsub ⟨le_of_lt hx.1, le_of_lt hx.2⟩))).hasDerivAt) hGint
    rw [h]
    have e1 : G (b + 1) = 0 := hGoff (b + 1) (by linarith) (Or.inr (by linarith))
    have e2 : G (a / 2) = 0 := hGoff (a / 2) (by linarith) (Or.inl (by linarith))
    rw [e1, e2, sub_zero]
  have hset : (∫ z in Set.Ioi 0, deriv G z) = ∫ z in (a / 2)..(b + 1), deriv G z := by
    have h1 : (∫ z in Set.Ioi (0 : ℝ), deriv G z)
        = ∫ z in Set.Icc (a / 2) (b + 1), deriv G z :=
      MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsub
        (fun x hx => by
          have hx' : ¬ (a / 2 ≤ x ∧ x ≤ b + 1) := hx.2
          have hc : x < a / 2 ∨ b + 1 < x := by
            by_contra hcon
            push Not at hcon
            exact hx' ⟨hcon.1, hcon.2⟩
          exact hGderiv_off x hx.1 (by
            rcases hc with h | h
            · exact Or.inl (by linarith)
            · exact Or.inr (by linarith)))
    rw [h1, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (show a / 2 ≤ b + 1 by linarith)]
  rw [hset, hFTC]

/-! ## Fubini for the product of the two integrations -/

private theorem setIntegral_prod_eq {F : ℝ × ℝ → ℝ} {s t : Set ℝ}
    (h : MeasureTheory.IntegrableOn F (s ×ˢ t)) :
    (∫ p in s ×ˢ t, F p) = ∫ z in s, ∫ θ in t, F (z, θ) := by
  rw [MeasureTheory.Measure.volume_eq_prod]
  exact MeasureTheory.setIntegral_prod F h

private theorem setIntegral_swap {F : ℝ × ℝ → ℝ} {s t : Set ℝ}
    (h : MeasureTheory.IntegrableOn F (s ×ˢ t)) :
    (∫ z in s, ∫ θ in t, F (z, θ)) = ∫ θ in t, ∫ z in s, F (z, θ) := by
  have hInt : MeasureTheory.Integrable F ((volume.restrict s).prod (volume.restrict t)) := by
    rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod]
    exact h
  have hsw := MeasureTheory.integral_integral_swap (μ := volume.restrict s)
    (ν := volume.restrict t) (f := fun z θ => F (z, θ)) hInt
  simpa using hsw

/-! ## The two-dimensional identity -/

private theorem master (u : ℝ → ℝ → ℝ) (χ ψ : ℝ → ℝ)
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) qd)
    (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (hχsupp : tsupport χ ⊆ Set.Ioi (0 : ℝ))
    (hψ : ContDiff ℝ 1 ψ) (hψsupp : tsupport ψ ⊆ Set.Ioo 0 (Real.pi / 2)) :
    (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2), J1 u χ ψ z θ)
      = -(∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2), J2 u χ ψ z θ)
        -(∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2), J3 u χ ψ z θ) := by
  obtain ⟨a, b, ha, hab, hχ0⟩ := exists_sep_chi hχc hχsupp
  obtain ⟨c, d, hc, hcd, hd, hψ0⟩ := exists_sep_psi hψsupp
  have hωd : ContDiffOn ℝ 1 (om χ) (Set.Ioi 0) := contDiffOn_om χ hχ
  have hω0 : ∀ z : ℝ, z ∉ Set.Icc a b → om χ z = 0 := fun z hz => by
    rw [om_rfl, hχ0 z hz]
    ring
  have hω0' : ∀ z : ℝ, z ∉ Set.Icc a b → deriv (om χ) z = 0 := deriv_eq_zero_off hω0
  have hboxc : IsCompact (Set.Icc a b ×ˢ Set.Icc c d) := isCompact_Icc.prod isCompact_Icc
  have hboxsub : Set.Icc a b ×ˢ Set.Icc c d ⊆ qd := fun p hp =>
    ⟨lt_of_lt_of_le ha hp.1.1, lt_of_lt_of_le hc hp.2.1, lt_of_le_of_lt hp.2.2 hd⟩
  -- the four integrands on the product
  set A : ℝ × ℝ → ℝ := fun p => J1 u χ ψ p.1 p.2 with hA
  set B : ℝ × ℝ → ℝ := fun p => J2 u χ ψ p.1 p.2 with hB
  set C : ℝ × ℝ → ℝ := fun p => J3 u χ ψ p.1 p.2 with hC
  set D : ℝ × ℝ → ℝ := fun p => J4 u χ ψ p.1 p.2 with hD
  -- ## the pointwise identity `A + B + C = D` on the open quadrant
  have hpt : ∀ p ∈ qd, A p + B p + C p = D p := by
    rintro ⟨z, θ⟩ hp
    obtain ⟨hz, hθ1, hθ2⟩ := hp
    have hz' : 0 < z := hz
    have h := J1_add_J2_add_J3_eq_J4 (u := u) (χ := χ) (ψ := ψ) hu hχ hz' hθ1 hθ2
    have hA' : A (z, θ) = J1 u χ ψ z θ := by rw [hA]
    have hB' : B (z, θ) = J2 u χ ψ z θ := by rw [hB]
    have hC' : C (z, θ) = J3 u χ ψ z θ := by rw [hC]
    have hD' : D (z, θ) = J4 u χ ψ z θ := by rw [hD]
    rw [hA', hB', hC', hD']
    exact h
  -- ## vanishing off the box
  have hA0 : ∀ p, p ∉ Set.Icc a b ×ˢ Set.Icc c d → A p = 0 := by
    rintro ⟨z, θ⟩ hp
    by_cases hz : z ∈ Set.Icc a b
    · have hθ : θ ∉ Set.Icc c d := fun hθ' => hp ⟨hz, hθ'⟩
      show J1 u χ ψ z θ = 0
      rw [J1_rfl, hψ0 θ hθ]
      ring
    · show J1 u χ ψ z θ = 0
      rw [J1_rfl, hω0 z hz]
      ring
  have hB0 : ∀ p, p ∉ Set.Icc a b ×ˢ Set.Icc c d → B p = 0 := by
    rintro ⟨z, θ⟩ hp
    by_cases hz : z ∈ Set.Icc a b
    · have hθ : θ ∉ Set.Icc c d := fun hθ' => hp ⟨hz, hθ'⟩
      show J2 u χ ψ z θ = 0
      rw [J2_rfl, hψ0 θ hθ]
      ring
    · show J2 u χ ψ z θ = 0
      rw [J2_rfl, hω0' z hz]
      ring
  have hC0 : ∀ p, p ∉ Set.Icc a b ×ˢ Set.Icc c d → C p = 0 := by
    rintro ⟨z, θ⟩ hp
    by_cases hz : z ∈ Set.Icc a b
    · have hθ : θ ∉ Set.Icc c d := fun hθ' => hp ⟨hz, hθ'⟩
      show J3 u χ ψ z θ = 0
      rw [J3_rfl, hψ0 θ hθ]
      ring
    · show J3 u χ ψ z θ = 0
      rw [J3_rfl, hω0 z hz]
      ring
  -- ## continuity on the box
  have hcontA : ContinuousOn A (Set.Icc a b ×ˢ Set.Icc c d) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => om χ p.1) (Set.Icc a b ×ˢ Set.Icc c d) :=
      hωd.continuousOn.comp continuous_fst.continuousOn (fun p hp => by
        simp only [Set.mem_Ioi]; linarith [hp.1.1, ha])
    have h2 : ContinuousOn (fun p : ℝ × ℝ => sg p.2) (Set.Icc a b ×ˢ Set.Icc c d) :=
      (continuousOn_sg hc hd).comp continuous_snd.continuousOn (fun p hp => hp.2)
    have h3 : ContinuousOn (fun p : ℝ × ℝ => ψ p.2) (Set.Icc a b ×ˢ Set.Icc c d) :=
      hψ.continuous.continuousOn.comp continuous_snd.continuousOn (fun p hp => hp.2)
    have h4 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pzIter 2 u p.1 p.2)
        (Set.Icc a b ×ˢ Set.Icc c d) :=
      (contDiffOn_pzIter_two hu).continuousOn.mono hboxsub
    have h5 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pthIter 2 u p.1 p.2)
        (Set.Icc a b ×ˢ Set.Icc c d) :=
      (contDiffOn_pthIter_two hu).continuousOn.mono hboxsub
    have hprod : ContinuousOn (fun p : ℝ × ℝ => om χ p.1 * sg p.2 * ψ p.2
        * Work.Spaces.pzIter 2 u p.1 p.2 * Work.Spaces.pthIter 2 u p.1 p.2)
        (Set.Icc a b ×ˢ Set.Icc c d) := (((h1.mul h2).mul h3).mul h4).mul h5
    have hEqA : A = (fun p : ℝ × ℝ => om χ p.1) * (fun p : ℝ × ℝ => sg p.2)
        * (fun p : ℝ × ℝ => ψ p.2) * (fun p : ℝ × ℝ => Work.Spaces.pzIter 2 u p.1 p.2)
        * (fun p : ℝ × ℝ => Work.Spaces.pthIter 2 u p.1 p.2) := by
      rw [hA]
      funext p
      simp only [Pi.mul_apply, J1_rfl]
    rw [hEqA]
    exact hprod
  have hcontB : ContinuousOn B (Set.Icc a b ×ˢ Set.Icc c d) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => deriv (om χ) p.1 / p.1)
        (Set.Icc a b ×ˢ Set.Icc c d) := by
      refine ContinuousOn.div ?_ continuous_fst.continuousOn ?_
      · exact (hωd.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).comp
          continuous_fst.continuousOn (fun p hp => by
            simp only [Set.mem_Ioi]; linarith [hp.1.1, ha])
      · intro p hp
        have hpos : (0 : ℝ) < p.1 := by linarith [hp.1.1, ha]
        exact ne_of_gt hpos
    have h2 : ContinuousOn (fun p : ℝ × ℝ => sg p.2) (Set.Icc a b ×ˢ Set.Icc c d) :=
      (continuousOn_sg hc hd).comp continuous_snd.continuousOn (fun p hp => hp.2)
    have h3 : ContinuousOn (fun p : ℝ × ℝ => ψ p.2) (Set.Icc a b ×ˢ Set.Icc c d) :=
      hψ.continuous.continuousOn.comp continuous_snd.continuousOn (fun p hp => hp.2)
    have h4 : ContinuousOn (fun p : ℝ × ℝ => p.1 * Work.Spaces.pz u p.1 p.2)
        (Set.Icc a b ×ˢ Set.Icc c d) :=
      continuous_fst.continuousOn.mul
        ((contDiffOn_pz_one hu).continuousOn.mono hboxsub)
    have h5 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pthIter 2 u p.1 p.2)
        (Set.Icc a b ×ˢ Set.Icc c d) :=
      (contDiffOn_pthIter_two hu).continuousOn.mono hboxsub
    have hprod : ContinuousOn (fun p : ℝ × ℝ => deriv (om χ) p.1 / p.1 * sg p.2 * ψ p.2
        * (p.1 * Work.Spaces.pz u p.1 p.2) * Work.Spaces.pthIter 2 u p.1 p.2)
        (Set.Icc a b ×ˢ Set.Icc c d) := (((h1.mul h2).mul h3).mul h4).mul h5
    have hEqB : B = (fun p : ℝ × ℝ => deriv (om χ) p.1 / p.1) * (fun p : ℝ × ℝ => sg p.2)
        * (fun p : ℝ × ℝ => ψ p.2) * (fun p : ℝ × ℝ => p.1 * Work.Spaces.pz u p.1 p.2)
        * (fun p : ℝ × ℝ => Work.Spaces.pthIter 2 u p.1 p.2) := by
      rw [hB]
      funext p
      simp only [Pi.mul_apply, J2_rfl]
    rw [hEqB]
    exact hprod
  have hcontC : ContinuousOn C (Set.Icc a b ×ˢ Set.Icc c d) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => om χ p.1) (Set.Icc a b ×ˢ Set.Icc c d) :=
      hωd.continuousOn.comp continuous_fst.continuousOn (fun p hp => by
        simp only [Set.mem_Ioi]; linarith [hp.1.1, ha])
    have h2 : ContinuousOn (fun p : ℝ × ℝ => sg p.2) (Set.Icc a b ×ˢ Set.Icc c d) :=
      (continuousOn_sg hc hd).comp continuous_snd.continuousOn (fun p hp => hp.2)
    have h3 : ContinuousOn (fun p : ℝ × ℝ => ψ p.2) (Set.Icc a b ×ˢ Set.Icc c d) :=
      hψ.continuous.continuousOn.comp continuous_snd.continuousOn (fun p hp => hp.2)
    have h4 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz u p.1 p.2)
        (Set.Icc a b ×ˢ Set.Icc c d) :=
      (contDiffOn_pz_one hu).continuousOn.mono hboxsub
    have h5 : ContinuousOn
        (fun p : ℝ × ℝ => Work.Spaces.pz (Work.Spaces.pthIter 2 u) p.1 p.2)
        (Set.Icc a b ×ˢ Set.Icc c d) :=
      (contDiffOn_pz_pth2 hu).continuousOn.mono hboxsub
    have hprod : ContinuousOn (fun p : ℝ × ℝ => om χ p.1 * sg p.2 * ψ p.2
        * Work.Spaces.pz u p.1 p.2
        * Work.Spaces.pz (Work.Spaces.pthIter 2 u) p.1 p.2)
        (Set.Icc a b ×ˢ Set.Icc c d) := (((h1.mul h2).mul h3).mul h4).mul h5
    have hEqC : C = (fun p : ℝ × ℝ => om χ p.1) * (fun p : ℝ × ℝ => sg p.2)
        * (fun p : ℝ × ℝ => ψ p.2) * (fun p : ℝ × ℝ => Work.Spaces.pz u p.1 p.2)
        * (fun p : ℝ × ℝ => Work.Spaces.pz (Work.Spaces.pthIter 2 u) p.1 p.2) := by
      rw [hC]
      funext p
      simp only [Pi.mul_apply, J3_rfl]
    rw [hEqC]
    exact hprod
  -- ## integrability
  have hIntAbox : MeasureTheory.IntegrableOn A (Set.Icc a b ×ˢ Set.Icc c d) :=
    hcontA.integrableOn_compact hboxc
  have hIntBbox : MeasureTheory.IntegrableOn B (Set.Icc a b ×ˢ Set.Icc c d) :=
    hcontB.integrableOn_compact hboxc
  have hIntCbox : MeasureTheory.IntegrableOn C (Set.Icc a b ×ˢ Set.Icc c d) :=
    hcontC.integrableOn_compact hboxc
  have hIntA : MeasureTheory.IntegrableOn A qd :=
    hIntAbox.of_forall_sdiff_eq_zero isOpen_qd.measurableSet (fun p hp => hA0 p hp.2)
  have hIntB : MeasureTheory.IntegrableOn B qd :=
    hIntBbox.of_forall_sdiff_eq_zero isOpen_qd.measurableSet (fun p hp => hB0 p hp.2)
  have hIntC : MeasureTheory.IntegrableOn C qd :=
    hIntCbox.of_forall_sdiff_eq_zero isOpen_qd.measurableSet (fun p hp => hC0 p hp.2)
  have hIntD : MeasureTheory.IntegrableOn D qd :=
    ((hIntA.add hIntB).add hIntC).congr_fun (fun p hp => hpt p hp)
      isOpen_qd.measurableSet
  -- ## the integral of `D` vanishes
  have hDzero : (∫ p in qd, D p) = 0 := by
    rw [setIntegral_prod_eq hIntD, setIntegral_swap hIntD]
    have hinner : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        (∫ z in Set.Ioi 0, D (z, θ)) = 0 := by
      intro θ hθ
      simpa only [hD, J4_rfl] using slice_integral_zero χ ψ hu hχ ha hab hω0 hθ.1 hθ.2
    rw [show (∫ θ in Set.Ioo 0 (Real.pi / 2), ∫ z in Set.Ioi 0, D (z, θ))
        = ∫ θ in Set.Ioo 0 (Real.pi / 2), (0 : ℝ) from
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioo hinner]
    simp
  -- ## linearity
  have hAdd : (∫ p in qd, A p) + (∫ p in qd, B p) + (∫ p in qd, C p) = 0 := by
    have h1 : (∫ p in qd, A p + B p) = (∫ p in qd, A p) + (∫ p in qd, B p) :=
      MeasureTheory.integral_add hIntA hIntB
    have h2 : (∫ p in qd, A p + B p + C p)
        = (∫ p in qd, A p + B p) + (∫ p in qd, C p) :=
      MeasureTheory.integral_add (hIntA.add hIntB) hIntC
    have h3 : (∫ p in qd, A p + B p + C p) = ∫ p in qd, D p :=
      MeasureTheory.setIntegral_congr_fun isOpen_qd.measurableSet (fun p hp => hpt p hp)
    linarith [h1, h2, h3, hDzero]
  -- ## back to the iterated integrals
  have c1 : (∫ p in qd, A p)
      = ∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2), J1 u χ ψ z θ := by
    simpa only [hA] using setIntegral_prod_eq hIntA
  have c2 : (∫ p in qd, B p)
      = ∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2), J2 u χ ψ z θ := by
    simpa only [hB] using setIntegral_prod_eq hIntB
  have c3 : (∫ p in qd, C p)
      = ∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2), J3 u χ ψ z θ := by
    simpa only [hC] using setIntegral_prod_eq hIntC
  linarith [hAdd, c1, c2, c3]

/-! ## The requested identity -/

theorem truncZIbp2 (u : ℝ → ℝ → ℝ) (χ ψ : ℝ → ℝ)
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (hχsupp : tsupport χ ⊆ Set.Ioi (0:ℝ))
    (hψ : ContDiff ℝ 1 ψ) (hψsupp : tsupport ψ ⊆ Set.Ioo 0 (Real.pi / 2)) :
    (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2), χ z * (Work.Spaces.w z)^2
        * (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
        * (z^2 * Work.Spaces.pzIter 2 u z θ) * (Work.Spaces.pthIter 2 u z θ))
    = - (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2),
          (deriv (fun z' => χ z' * (Work.Spaces.w z')^2 * z'^2) z / z)
            * (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
            * (z * Work.Spaces.pz u z θ) * (Work.Spaces.pthIter 2 u z θ))
      - (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2), χ z * (Work.Spaces.w z)^2
          * (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
          * (z * Work.Spaces.pz u z θ) * (z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ)) := by
  have h1 : ∀ z θ : ℝ, χ z * (Work.Spaces.w z)^2 * (Real.sin (2*θ)) ^ (-(Work.Spaces.eta))
        * ψ θ * (z^2 * Work.Spaces.pzIter 2 u z θ) * (Work.Spaces.pthIter 2 u z θ)
      = J1 u χ ψ z θ := fun z θ => by rw [J1_rfl, om_rfl, sg_rfl]; ring
  have h2 : ∀ z θ : ℝ,
      (deriv (fun z' => χ z' * (Work.Spaces.w z')^2 * z'^2) z / z)
        * (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
        * (z * Work.Spaces.pz u z θ) * (Work.Spaces.pthIter 2 u z θ)
      = J2 u χ ψ z θ := fun z θ => by
    rw [J2_rfl, show om χ = fun z : ℝ => χ z * (Work.Spaces.w z) ^ 2 * z ^ 2 from rfl,
      sg_rfl]
  have h3 : ∀ z θ : ℝ, χ z * (Work.Spaces.w z)^2 * (Real.sin (2*θ)) ^ (-(Work.Spaces.eta))
        * ψ θ * (z * Work.Spaces.pz u z θ)
        * (z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ)
      = J3 u χ ψ z θ := fun z θ => by rw [J3_rfl, om_rfl, sg_rfl]; ring
  simp only [h1, h2, h3]
  exact master u χ ψ hu hχ hχc hχsupp hψ hψsupp

end Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk
