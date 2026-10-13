import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.CurrySmooth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.EllGap.MLevelBookkeeping

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Finite-order smoothness of the first partial derivatives

The hypothesis of the main theorem is only *finite-order* smoothness of `G`
(`∀ n : ℕ, ContDiffOn ℝ n …`), so the `⊤`-order calculus of `Work.Spaces.CurrySmooth`
does not apply.  The two lemmas below are the finite-order analogues, for an arbitrary
open set `V`. -/

/-- `∂_z` lowers finite order by one on an open set. -/
theorem contDiffOn_uncurry_pz_of_isOpen {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    {n : ℕ} (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pz G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pz G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (1, 0) := fun p hp =>
    Work.Spaces.pz_eq_fderiv
      ((h.differentiableOn (by norm_num : (n + 1 : WithTop ℕ∞) ≠ 0)).differentiableAt
        (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V :=
    h.fderiv_of_isOpen hV (m := n) (by norm_num)
  have hcomp : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (1, 0)) V :=
    hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-- `∂_θ` lowers finite order by one on an open set. -/
theorem contDiffOn_uncurry_pth_of_isOpen {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    {n : ℕ} (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pth G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (0, 1) := fun p hp =>
    Work.Spaces.pth_eq_fderiv
      ((h.differentiableOn (by norm_num : (n + 1 : WithTop ℕ∞) ≠ 0)).differentiableAt
        (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V :=
    h.fderiv_of_isOpen hV (m := n) (by norm_num)
  have hcomp : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (0, 1)) V :=
    hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-- `D_z` lowers finite order by one on an open set. -/
theorem contDiffOn_uncurry_Dz_of_isOpen {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    {n : ℕ} (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.Dz G)) V := by
  have hpz := contDiffOn_uncurry_pz_of_isOpen hV h
  have hfun : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => p.1 * Function.uncurry (Work.Spaces.pz G) p) V :=
    contDiff_fst.contDiffOn.mul hpz
  refine hfun.congr (fun p hp => ?_)
  rfl

/-- Differentiability in the second variable, for a function that is `C^{n+1}` on an open set. -/
theorem differentiableAt_curry_right_of_contDiffOn {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) {n : ℕ} {p : ℝ × ℝ} (hp : p ∈ V)
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    DifferentiableAt ℝ (fun t => G p.1 t) p.2 :=
  Work.Spaces.differentiableAt_curry_right
    ((h.differentiableOn (by norm_num : (n + 1 : WithTop ℕ∞) ≠ 0)).differentiableAt
      (hV.mem_nhds hp))

/-! ## Differentiation under the integral sign over a compact interval -/

/-- **Differentiation under the integral sign over `[a,b]`.**  If `g` and the candidate
parameter-derivative `g'` are jointly continuous on `V ×ˢ [a,b]` (`V` an open set of
parameters) and `x ↦ g x z` has derivative `x ↦ g' x z` at every `x ∈ V`, for every
`z ∈ [a,b]`, then the parametric integral over `[a,b]` has derivative the integral of `g'`.

This is the compact-interval analogue of the angular statement
`Work.Coercivity.hasDerivAt_integral_Itheta_of_hasDerivAt`. -/
theorem hasDerivAt_integral_Icc_of_hasDerivAt {g g' : ℝ → ℝ → ℝ} {V : Set ℝ} {a b θ : ℝ}
    (hV : IsOpen V) (hθ : θ ∈ V)
    (hg : ContinuousOn (Function.uncurry g) (V ×ˢ Set.Icc a b))
    (hg' : ContinuousOn (Function.uncurry g') (V ×ˢ Set.Icc a b))
    (hdiff : ∀ z ∈ Set.Icc a b, ∀ x ∈ V, HasDerivAt (fun x' => g x' z) (g' x z) x) :
    HasDerivAt (fun x => ∫ z in Set.Icc a b, g x z) (∫ z in Set.Icc a b, g' θ z) θ := by
  haveI hfin : IsFiniteMeasure (volume.restrict (Set.Icc a b)) := by
    rw [isFiniteMeasure_restrict, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hslice : ∀ x ∈ V, ContinuousOn (fun z => g x z) (Set.Icc a b) := fun x hx =>
    hg.comp (continuousOn_const.prodMk continuousOn_id) (fun z hz => ⟨hx, hz⟩)
  have hslice' : ∀ x ∈ V, ContinuousOn (fun z => g' x z) (Set.Icc a b) := fun x hx =>
    hg'.comp (continuousOn_const.prodMk continuousOn_id) (fun z hz => ⟨hx, hz⟩)
  obtain ⟨δ, hδpos, hδV⟩ := Metric.mem_nhds_iff.1 (hV.mem_nhds hθ)
  set K : Set ℝ := Set.Icc (θ - δ / 2) (θ + δ / 2) with hKdef
  have hKc : IsCompact K := by rw [hKdef]; exact isCompact_Icc
  have hKV : K ⊆ V := by
    intro x hx
    apply hδV
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    refine ⟨?_, ?_⟩ <;> linarith [hx.1, hx.2, hδpos]
  have hcontK : ContinuousOn (Function.uncurry g') (K ×ˢ Set.Icc a b) :=
    hg'.mono (Set.prod_mono hKV subset_rfl)
  obtain ⟨C, hC⟩ := (hKc.prod isCompact_Icc).exists_bound_of_continuousOn hcontK
  have hmem : θ ∈ Set.Ioo (θ - δ / 2) (θ + δ / 2) := ⟨by linarith, by linarith⟩
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Icc a b)) (𝕜 := ℝ)
    (F := fun x z => g x z) (F' := fun x z => g' x z) (bound := fun _ => C)
    (x₀ := θ) (s := Set.Ioo (θ - δ / 2) (θ + δ / 2))
    (isOpen_Ioo.mem_nhds hmem) ?_ ?_ ?_ ?_ ?_ ?_
  · exact key.2
  · filter_upwards [isOpen_Ioo.mem_nhds hmem, hV.mem_nhds hθ] with x _ hxV
    exact (hslice x hxV).aestronglyMeasurable measurableSet_Icc
  · exact ContinuousOn.integrableOn_compact isCompact_Icc (hslice θ hθ)
  · exact (hslice' θ hθ).aestronglyMeasurable measurableSet_Icc
  · rw [ae_restrict_iff' measurableSet_Icc]
    refine Eventually.of_forall fun z hz x hx => ?_
    have hxK : x ∈ K := Set.Ioo_subset_Icc_self hx
    simpa [Function.uncurry] using hC (x, z) ⟨hxK, hz⟩
  · exact integrable_const C
  · rw [ae_restrict_iff' measurableSet_Icc]
    exact Eventually.of_forall fun z hz x hx =>
      hdiff z hz x (hKV (Set.Ioo_subset_Icc_self hx))

/-! ## The main statement -/

theorem mLevel_hasDerivAt {G : ℝ → ℝ → ℝ} {a b θ : ℝ} (ha : 0 < a) (hab : a < b)
    (hG : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G)
      (Set.Ioo (a - 1) (b + 1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1)))
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (fun t : ℝ => ∫ z in Set.Icc a b,
        (Work.Spaces.w z) ^ 2 * (Work.Spaces.Dz G z t) ^ 2)
      (2 * ∫ z in Set.Icc a b, (Work.Spaces.w z) ^ 2
        * (Work.Spaces.Dz G z θ * Work.Spaces.pth (Work.Spaces.Dz G) z θ)) θ := by
  -- the angular radius around `θ`
  have hminpos : 0 < min θ (Real.pi / 2 - θ) := lt_min hθ.1 (by linarith [hθ.2])
  obtain ⟨ρ, hρpos, hρle⟩ : ∃ ρ : ℝ, 0 < ρ ∧ 2 * ρ ≤ min θ (Real.pi / 2 - θ) :=
    ⟨min θ (Real.pi / 2 - θ) / 4, by linarith, by linarith⟩
  have h2ρθ : 2 * ρ ≤ θ := le_trans hρle (min_le_left θ (Real.pi / 2 - θ))
  have h2ρπ : 2 * ρ ≤ Real.pi / 2 - θ := le_trans hρle (min_le_right θ (Real.pi / 2 - θ))
  have hlow : -1 < θ - 2 * ρ := by linarith [h2ρθ, hθ.1]
  have hhigh : θ + 2 * ρ < Real.pi / 2 + 1 := by
    have hp := Real.pi_pos; linarith [h2ρπ, hθ.2]
  set Vparam : Set ℝ := Set.Ioo (θ - 2 * ρ) (θ + 2 * ρ) with hVparamdef
  have hVparam_open : IsOpen Vparam := by rw [hVparamdef]; exact isOpen_Ioo
  have hθV : θ ∈ Vparam := by
    rw [hVparamdef]; exact ⟨by linarith, by linarith⟩
  have hVbox_open : IsOpen (Set.Ioo (a - 1) (b + 1) ×ˢ Vparam) := by
    rw [hVparamdef]; exact isOpen_Ioo.prod isOpen_Ioo
  have hIccsub : Set.Icc a b ⊆ Set.Ioo (a - 1) (b + 1) :=
    fun z hz => ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hsubbox : Set.Ioo (a - 1) (b + 1) ×ˢ Vparam
      ⊆ Set.Ioo (a - 1) (b + 1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1) := by
    refine Set.prod_mono subset_rfl (fun x hx => ?_)
    rw [hVparamdef] at hx
    exact ⟨by linarith [hlow, hx.1], by linarith [hhigh, hx.2]⟩
  have hG2 : ContDiffOn ℝ 2 (Function.uncurry G) (Set.Ioo (a - 1) (b + 1) ×ˢ Vparam) :=
    (hG (1 + 1)).mono hsubbox
  have hG3 : ContDiffOn ℝ 3 (Function.uncurry G) (Set.Ioo (a - 1) (b + 1) ×ˢ Vparam) :=
    (hG (2 + 1)).mono hsubbox
  have hDz1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.Dz G))
      (Set.Ioo (a - 1) (b + 1) ×ˢ Vparam) :=
    contDiffOn_uncurry_Dz_of_isOpen hVbox_open (n := 1) hG2
  have hDz2 : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.Dz G))
      (Set.Ioo (a - 1) (b + 1) ×ˢ Vparam) :=
    contDiffOn_uncurry_Dz_of_isOpen hVbox_open (n := 2) hG3
  have hpthDz1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pth (Work.Spaces.Dz G)))
      (Set.Ioo (a - 1) (b + 1) ×ˢ Vparam) :=
    contDiffOn_uncurry_pth_of_isOpen hVbox_open (n := 1) hDz2
  -- joint continuity of the two integrands
  have hw2 : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Icc a b) := by
    unfold Work.Spaces.w
    refine ContinuousOn.pow ?_ 2
    refine ContinuousOn.div ?_ ?_ ?_
    · exact ((continuous_const.add continuous_id).pow 2).continuousOn
    · exact (continuous_id.pow 2).continuousOn
    · intro z hz
      have hz0 : 0 < z := lt_of_lt_of_le ha hz.1
      positivity
  have hw2prod : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.2) ^ 2)
      (Vparam ×ˢ Set.Icc a b) :=
    hw2.comp continuousOn_snd (fun p hp => hp.2)
  have hDz_cont : ContinuousOn (Function.uncurry (Work.Spaces.Dz G))
      (Set.Icc a b ×ˢ Vparam) :=
    hDz1.continuousOn.mono (Set.prod_mono hIccsub subset_rfl)
  have hswap : ContinuousOn (fun p : ℝ × ℝ =>
      Function.uncurry (Work.Spaces.Dz G) (p.2, p.1)) (Vparam ×ˢ Set.Icc a b) :=
    hDz_cont.comp (continuousOn_snd.prodMk continuousOn_fst) (fun p hp => ⟨hp.2, hp.1⟩)
  have hpthDz_cont : ContinuousOn (Function.uncurry (Work.Spaces.pth (Work.Spaces.Dz G)))
      (Set.Icc a b ×ˢ Vparam) :=
    hpthDz1.continuousOn.mono (Set.prod_mono hIccsub subset_rfl)
  have hswap2 : ContinuousOn (fun p : ℝ × ℝ =>
      Function.uncurry (Work.Spaces.pth (Work.Spaces.Dz G)) (p.2, p.1))
      (Vparam ×ˢ Set.Icc a b) :=
    hpthDz_cont.comp (continuousOn_snd.prodMk continuousOn_fst) (fun p hp => ⟨hp.2, hp.1⟩)
  have hg_cont : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.w p.2) ^ 2 * (Work.Spaces.Dz G p.2 p.1) ^ 2)
      (Vparam ×ˢ Set.Icc a b) := by
    have hprod : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.2) ^ 2
        * (Function.uncurry (Work.Spaces.Dz G) (p.2, p.1)) ^ 2)
        (Vparam ×ˢ Set.Icc a b) := hw2prod.mul (hswap.pow 2)
    exact hprod.congr (fun p hp => rfl)
  have hg'_cont : ContinuousOn (fun p : ℝ × ℝ => 2 * ((Work.Spaces.w p.2) ^ 2
      * (Work.Spaces.Dz G p.2 p.1 * Work.Spaces.pth (Work.Spaces.Dz G) p.2 p.1)))
      (Vparam ×ˢ Set.Icc a b) := by
    have hprod : ContinuousOn (fun p : ℝ × ℝ => 2 * ((Work.Spaces.w p.2) ^ 2
        * (Function.uncurry (Work.Spaces.Dz G) (p.2, p.1)
          * Function.uncurry (Work.Spaces.pth (Work.Spaces.Dz G)) (p.2, p.1))))
        (Vparam ×ˢ Set.Icc a b) := continuousOn_const.mul (hw2prod.mul (hswap.mul hswap2))
    exact hprod.congr (fun p hp => rfl)
  -- the pointwise derivative
  have hdiff : ∀ z ∈ Set.Icc a b, ∀ x ∈ Vparam,
      HasDerivAt (fun x' => (Work.Spaces.w z) ^ 2 * (Work.Spaces.Dz G z x') ^ 2)
        (2 * ((Work.Spaces.w z) ^ 2
          * (Work.Spaces.Dz G z x * Work.Spaces.pth (Work.Spaces.Dz G) z x))) x := by
    intro z hz x hx
    have hpt : (z, x) ∈ Set.Ioo (a - 1) (b + 1) ×ˢ Vparam := ⟨hIccsub hz, hx⟩
    have hdz : DifferentiableAt ℝ (fun x' => Work.Spaces.Dz G z x') x :=
      differentiableAt_curry_right_of_contDiffOn hVbox_open hpt (n := 0) hDz1
    have h1 : HasDerivAt (fun x' => Work.Spaces.Dz G z x')
        (Work.Spaces.pth (Work.Spaces.Dz G) z x) x := hdz.hasDerivAt
    have h2 : HasDerivAt (fun x' => (Work.Spaces.Dz G z x') ^ 2)
        (2 * Work.Spaces.Dz G z x * Work.Spaces.pth (Work.Spaces.Dz G) z x) x := by
      have hp := h1.pow 2
      convert hp using 1
      ring
    have h3 : HasDerivAt (fun x' => (Work.Spaces.w z) ^ 2 * (Work.Spaces.Dz G z x') ^ 2)
        ((Work.Spaces.w z) ^ 2 * (2 * Work.Spaces.Dz G z x
          * Work.Spaces.pth (Work.Spaces.Dz G) z x)) x := h2.const_mul _
    have hderiv : (Work.Spaces.w z) ^ 2 * (2 * Work.Spaces.Dz G z x
          * Work.Spaces.pth (Work.Spaces.Dz G) z x)
        = 2 * ((Work.Spaces.w z) ^ 2
          * (Work.Spaces.Dz G z x * Work.Spaces.pth (Work.Spaces.Dz G) z x)) := by
      ring
    rw [hderiv] at h3
    exact h3
  -- assemble
  have key := hasDerivAt_integral_Icc_of_hasDerivAt
    (g := fun x z => (Work.Spaces.w z) ^ 2 * (Work.Spaces.Dz G z x) ^ 2)
    (g' := fun x z => 2 * ((Work.Spaces.w z) ^ 2
      * (Work.Spaces.Dz G z x * Work.Spaces.pth (Work.Spaces.Dz G) z x)))
    (V := Vparam) (a := a) (b := b) (θ := θ)
    hVparam_open hθV hg_cont hg'_cont hdiff
  rw [MeasureTheory.integral_const_mul] at key
  exact key

end

end Work.FTS.EllipticEst.EllGap.MLevelBookkeeping
