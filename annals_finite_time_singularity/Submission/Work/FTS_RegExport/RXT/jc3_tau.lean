/-
# `Work.FTS_RegExport.RXT.jc3_tau` — time-continuity of the order-≤3 jets

For a family `g` whose slices are `C⁴` on the open quadrant and whose order-≤2 slots are
Lipschitz in the fake time (`hTau`), the order-≤3 slots are continuous in the fake time
`τ ∈ [0,T]`: the order-≤2 slots are Lipschitz by `hTau`, and the order-3 slot is the spatial
derivative of an order-2 slot, so the abstract Landau step
(`RXT.tau_lip_sqrt_of_primitive_Icc`) applies along a curve on which the spatial derivative is
`D_z` (the curve `x ↦ z e^x`) or `D_θ` (the curve `x ↦ arctan (tan θ · e^{2x})`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_RegExport.RXT.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- `cth` inverts `ψ ↦ log (tan ·)` on the open quadrant. -/
lemma cth_log_tan {θ : ℝ} (h0 : 0 < θ) (hπ : θ < Real.pi / 2) :
    cth (Real.log (Real.tan θ)) = θ := by
  rw [cth, Real.exp_log (Real.tan_pos_of_pos_of_lt_pi_div_two h0 hπ),
    Real.arctan_tan (by linarith [Real.pi_pos]) hπ]

/-- The final step of the Landau estimate: on a compact time interval a `√`-Hölder bound,
available up to the size `δ₀` of the space interval of the Landau step, gives continuity. -/
lemma continuousWithinAt_of_sqrt_bound {f : ℝ → ℝ} {T τ K ε δ₀ : ℝ} (hε : 0 < ε) (hK : 0 ≤ K)
    (hδ₀ : 0 < δ₀)
    (h : ∀ σ ∈ Set.Icc (0:ℝ) T, |σ - τ| ≤ δ₀ → |f σ - f τ| ≤ K * Real.sqrt |σ - τ|) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ σ ∈ Set.Icc (0:ℝ) T, |σ - τ| < δ → |f σ - f τ| < ε := by
  refine ⟨min δ₀ ((ε / (K + 1)) ^ 2), lt_min hδ₀ (by positivity), fun σ hσ hd => ?_⟩
  have h1 : |σ - τ| ≤ δ₀ := le_of_lt (lt_of_lt_of_le hd (min_le_left _ _))
  have h2 : |σ - τ| ≤ (ε / (K + 1)) ^ 2 := le_of_lt (lt_of_lt_of_le hd (min_le_right _ _))
  have hpos : (0:ℝ) ≤ ε / (K + 1) := by positivity
  have hs : Real.sqrt |σ - τ| ≤ ε / (K + 1) := by
    calc Real.sqrt |σ - τ| ≤ Real.sqrt ((ε / (K + 1)) ^ 2) := Real.sqrt_le_sqrt h2
      _ = ε / (K + 1) := Real.sqrt_sq hpos
  have hfin : K * (ε / (K + 1)) < ε := by
    have h3 : K * (ε / (K + 1)) = ε * (K / (K + 1)) := by ring
    rw [h3]
    have h4 : K / (K + 1) < 1 := by
      rw [div_lt_one (by linarith : (0:ℝ) < K + 1)]
      linarith
    nlinarith
  calc |f σ - f τ| ≤ K * Real.sqrt |σ - τ| := h σ hσ h1
    _ ≤ K * (ε / (K + 1)) := mul_le_mul_of_nonneg_left hs hK
    _ < ε := hfin

theorem tau_cont_mixed {g : Work.FTS.Galerkin.Fam} {T z θ dθ Lτ Cs : ℝ}
    (hT : 0 < T) (hz : 0 < z) (hθ0 : 0 < θ) (hθπ : θ < Real.pi / 2)
    (hdθpos : 0 < dθ) (hdθle : dθ ≤ (Real.pi / 2 - θ) / 2)
    (hLτnn : 0 ≤ Lτ) (hCsnn : 0 ≤ Cs) {j i : ℕ} (hji : j + i ≤ 3)
    (hc4 : ∀ σ ∈ Set.Icc (0:ℝ) T, ContDiffOn ℝ 4
      (Function.uncurry (Work.FTS.Galerkin.slice g σ)) Work.FTS.EllipticEst.Q0)
    (hTau : ∀ σ ∈ Set.Icc (0:ℝ) T, ∀ σ' ∈ Set.Icc (0:ℝ) T, ∀ b a : ℕ, a + b ≤ 2 →
      ∀ x y : ℝ, 0 < x → 0 < y → y < Real.pi / 2 →
        |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g σ) x y
          - Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g σ') x y| ≤ Lτ * |σ - σ'|)
    (hSpaceZ : ∀ σ ∈ Set.Icc (0:ℝ) T, ∀ j' i' : ℕ, j' + i' ≤ 3 →
      ∀ x ∈ Set.Icc (z / 2) (3 * z / 2), ∀ y ∈ Set.Icc (θ - dθ) (θ + dθ),
      ∀ x' ∈ Set.Icc (z / 2) (3 * z / 2),
        |Work.Spaces.mixed j' i' (Work.FTS.Galerkin.slice g σ) x y
          - Work.Spaces.mixed j' i' (Work.FTS.Galerkin.slice g σ) x' y| ≤ Cs * |x - x'|)
    (hSpaceθ : ∀ σ ∈ Set.Icc (0:ℝ) T, ∀ j' i' : ℕ, j' + i' ≤ 3 →
      ∀ x ∈ Set.Icc (z / 2) (3 * z / 2), ∀ y ∈ Set.Icc (θ - dθ) (θ + dθ),
      ∀ y' ∈ Set.Icc (θ - dθ) (θ + dθ),
        |Work.Spaces.mixed j' i' (Work.FTS.Galerkin.slice g σ) x y
          - Work.Spaces.mixed j' i' (Work.FTS.Galerkin.slice g σ) x y'| ≤ Cs * |y - y'|)
    (hLandau : ∀ {V W : ℝ → ℝ → ℝ} {x₀ δc L K : ℝ}, 0 < δc → 0 ≤ L → 0 ≤ K →
      (∀ τ τ' : ℝ, 0 ≤ τ → 0 ≤ τ' → ∀ x ∈ Set.Icc x₀ (x₀ + δc),
        |V x τ - V x τ'| ≤ L * |τ - τ'|) →
      (∀ τ : ℝ, 0 ≤ τ → ContinuousOn (fun x => W x τ) (Set.Icc x₀ (x₀ + δc))) →
      (∀ τ : ℝ, 0 ≤ τ → ∀ x ∈ Set.Icc x₀ (x₀ + δc),
        |W x τ - W x₀ τ| ≤ K * |x - x₀|) →
      (∀ τ : ℝ, 0 ≤ τ → ∀ x ∈ Set.Icc x₀ (x₀ + δc),
        HasDerivAt (fun x' => V x' τ) (W x τ) x) →
      ∀ τ τ' : ℝ, 0 ≤ τ → 0 ≤ τ' → |τ - τ'| ≤ δc ^ 2 →
        |W x₀ τ - W x₀ τ'| ≤ (2 * L + K) * Real.sqrt |τ - τ'|)
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0:ℝ) T) :
    ContinuousWithinAt (fun σ : ℝ => Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g σ) z θ)
      (Set.Icc (0:ℝ) T) τ := by
  have hθmem' : θ ∈ Set.Icc (θ - dθ) (θ + dθ) := ⟨by linarith, by linarith⟩
  have hzmem' : z ∈ Set.Icc (z / 2) (3 * z / 2) := ⟨by linarith, by linarith⟩
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · -- `j = 0`
    subst hj0
    rcases lt_or_ge i 3 with hi3 | hi3
    · -- `i ≤ 2`: the slot itself is Lipschitz in `τ`
      have hi2 : i ≤ 2 := by omega
      rw [Metric.continuousWithinAt_iff]
      intro ε hε
      refine ⟨ε / (Lτ + 1), by positivity, ?_⟩
      intro σ hσ hd
      rw [Real.dist_eq] at hd ⊢
      have hb := hTau σ hσ τ hτ 0 i hi2 z θ hz hθ0 hθπ
      have hstep : Lτ * |σ - τ| ≤ Lτ * (ε / (Lτ + 1)) :=
        mul_le_mul_of_nonneg_left (le_of_lt hd) hLτnn
      have hfin : Lτ * (ε / (Lτ + 1)) < ε := by
        have h1 : Lτ * (ε / (Lτ + 1)) = ε * (Lτ / (Lτ + 1)) := by ring
        rw [h1]
        have h2 : Lτ / (Lτ + 1) < 1 := by
          rw [div_lt_one (by linarith : (0:ℝ) < Lτ + 1)]
          linarith
        nlinarith
      linarith
    · -- `i = 3`: the Landau step in the `θ`-direction
      have hi3' : i = 3 := by omega
      subst hi3'
      set ψ₀ : ℝ := Real.log (Real.tan θ) with hψ₀def
      set ψhi : ℝ := Real.log (Real.tan (θ + dθ)) with hψhidef
      set δc : ℝ := (ψhi - ψ₀) / 2 with hδcdef
      have hθhipos : 0 < θ + dθ := by linarith
      have hθhilt : θ + dθ < Real.pi / 2 := by linarith
      have htanθ : 0 < Real.tan θ := Real.tan_pos_of_pos_of_lt_pi_div_two hθ0 hθπ
      have htanθhi : 0 < Real.tan (θ + dθ) :=
        Real.tan_pos_of_pos_of_lt_pi_div_two hθhipos hθhilt
      have htan_lt : Real.tan θ < Real.tan (θ + dθ) :=
        Real.tan_lt_tan_of_lt_of_lt_pi_div_two (by linarith [Real.pi_pos]) hθhilt
          (by linarith)
      have hδcpos : 0 < δc := by
        rw [hδcdef]
        have h := Real.log_lt_log htanθ htan_lt
        linarith
      set Θ : ℝ → ℝ := fun x => cth (ψ₀ + 2 * x) with hΘdef
      have hΘderiv : ∀ x : ℝ, HasDerivAt Θ (Real.sin (2 * Θ x)) x := by
        intro x
        have h1 : HasDerivAt cth (Real.sin (2 * cth (ψ₀ + 2 * x)) / 2) (ψ₀ + 2 * x) :=
          hasDerivAt_cth (ψ₀ + 2 * x)
        have h2 : HasDerivAt (fun x' : ℝ => ψ₀ + 2 * x') 2 x := by
          simpa using ((hasDerivAt_id x).const_mul (2:ℝ)).const_add ψ₀
        have h3 := h1.comp x h2
        have hv : (Real.sin (2 * cth (ψ₀ + 2 * x)) / 2) * 2 = Real.sin (2 * Θ x) := by
          rw [hΘdef]; ring
        rw [hv] at h3
        exact h3
      have hΘ0 : Θ 0 = θ := by
        rw [hΘdef]
        show cth (ψ₀ + 2 * 0) = θ
        rw [show ψ₀ + 2 * 0 = ψ₀ by ring, hψ₀def]
        exact cth_log_tan hθ0 hθπ
      have hΘδ : Θ δc = θ + dθ := by
        rw [hΘdef]
        show cth (ψ₀ + 2 * δc) = θ + dθ
        rw [show ψ₀ + 2 * δc = ψhi by rw [hδcdef]; ring, hψhidef]
        exact cth_log_tan hθhipos hθhilt
      have hΘx_eq : ∀ x : ℝ, Real.arctan (Real.exp (ψ₀ + 2 * x)) = Θ x := by
        intro x; rw [hΘdef]; rfl
      have hΘmono : ∀ x ∈ Set.Icc (0:ℝ) δc, Θ x ≤ Θ δc := by
        intro x hx
        have h1 : Real.exp (ψ₀ + 2 * x) ≤ Real.exp (ψ₀ + 2 * δc) :=
          Real.exp_le_exp.mpr (by linarith [hx.2])
        have h2 := Real.arctan_mono h1
        rwa [hΘx_eq x, show Real.arctan (Real.exp (ψ₀ + 2 * δc)) = Θ δc from hΘx_eq δc] at h2
      have hΘge : ∀ x ∈ Set.Icc (0:ℝ) δc, θ ≤ Θ x := by
        intro x hx
        have h1 : Real.exp (ψ₀ + 2 * 0) ≤ Real.exp (ψ₀ + 2 * x) :=
          Real.exp_le_exp.mpr (by linarith [hx.1])
        have h2 := Real.arctan_mono h1
        have h3 : Real.arctan (Real.exp (ψ₀ + 2 * 0)) = θ := by
          rw [show ψ₀ + 2 * 0 = ψ₀ by ring, hψ₀def]
          exact cth_log_tan hθ0 hθπ
        rwa [h3, hΘx_eq x] at h2
      have hΘmem : ∀ x ∈ Set.Icc (0:ℝ) δc, Θ x ∈ Set.Icc (θ - dθ) (θ + dθ) := by
        intro x hx
        have h1 := hΘge x hx
        have h2 := hΘmono x hx
        rw [hΘδ] at h2
        exact ⟨by linarith, h2⟩
      have hΘlip : ∀ x ∈ Set.Icc (0:ℝ) δc, |Θ x - θ| ≤ 1 * |x| := by
        intro x hx
        have hdiff : ∀ y ∈ Set.Icc (0:ℝ) δc, DifferentiableAt ℝ Θ y :=
          fun y _ => (hΘderiv y).differentiableAt
        have hbnd : ∀ y ∈ Set.Icc (0:ℝ) δc, ‖deriv Θ y‖ ≤ 1 := by
          intro y hy
          rw [Real.norm_eq_abs, (hΘderiv y).deriv]
          exact abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
        have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbnd
          (convex_Icc (0:ℝ) δc) ⟨le_rfl, hδcpos.le⟩ hx
        rw [Real.norm_eq_abs, Real.norm_eq_abs, hΘ0, sub_zero] at h
        exact h
      set Vt : ℝ → ℝ → ℝ := fun x σ =>
        Work.Spaces.mixed 0 2 (Work.FTS.Galerkin.slice g σ) z (Θ x) with hVtdef
      set Wt : ℝ → ℝ → ℝ := fun x σ =>
        Work.Spaces.mixed 0 3 (Work.FTS.Galerkin.slice g σ) z (Θ x) with hWtdef
      have hVh : ∀ σ ∈ Set.Icc (0:ℝ) T, ∀ σ' ∈ Set.Icc (0:ℝ) T,
          ∀ x ∈ Set.Icc (0:ℝ) (0 + δc), |Vt x σ - Vt x σ'| ≤ Lτ * |σ - σ'| := by
        intro σ hσ σ' hσ' x hx
        have h := hTau σ hσ σ' hσ' 0 2 (by omega) z (Θ x) hz
          (cth_pos (ψ₀ + 2 * x)) (cth_lt (ψ₀ + 2 * x))
        simpa only [hVtdef] using h
      have hch : ∀ σ ∈ Set.Icc (0:ℝ) T,
          ContinuousOn (fun x => Wt x σ) (Set.Icc (0:ℝ) (0 + δc)) := by
        intro σ hσ
        have hc : ContinuousOn (fun p : ℝ × ℝ =>
            Work.Spaces.mixed 0 3 (Work.FTS.Galerkin.slice g σ) p.1 p.2)
            Work.FTS.EllipticEst.Q0 := continuousOn_mixed_of_four (hc4 σ hσ) (by omega)
        have hΘc : Continuous Θ := by
          rw [hΘdef]
          exact (Real.continuous_arctan.comp Real.continuous_exp).comp
            (continuous_const.add (continuous_const.mul continuous_id))
        have hmap : ∀ x ∈ Set.Icc (0:ℝ) (0 + δc), (z, Θ x) ∈ Work.FTS.EllipticEst.Q0 :=
          fun x _ => Work.FTS.EllipticEst.mem_Q0.mpr
            ⟨hz, cth_pos (ψ₀ + 2 * x), cth_lt (ψ₀ + 2 * x)⟩
        have hcomp := hc.comp (continuousOn_const.prodMk hΘc.continuousOn) hmap
        simpa only [hWtdef, Function.comp_def] using hcomp
      have hWh : ∀ σ ∈ Set.Icc (0:ℝ) T, ∀ x ∈ Set.Icc (0:ℝ) (0 + δc),
          |Wt x σ - Wt 0 σ| ≤ (1 * Cs) * |x - 0| := by
        intro σ hσ x hx
        have hx' : x ∈ Set.Icc (0:ℝ) δc := by simpa only [zero_add] using hx
        have h := hSpaceθ σ hσ 0 3 (by omega) z hzmem' (Θ x) (hΘmem x hx') θ hθmem'
        have h2 : |Θ x - θ| ≤ 1 * |x - 0| := by
          rw [sub_zero]; exact hΘlip x hx'
        rw [hWtdef]
        simp only [mul_zero, add_zero, hΘ0]
        calc |Work.Spaces.mixed 0 3 (Work.FTS.Galerkin.slice g σ) z (Θ x)
              - Work.Spaces.mixed 0 3 (Work.FTS.Galerkin.slice g σ) z θ|
            ≤ Cs * |Θ x - θ| := h
          _ ≤ Cs * (1 * |x - 0|) := mul_le_mul_of_nonneg_left h2 hCsnn
          _ = (1 * Cs) * |x - 0| := by ring
      have hdh : ∀ σ ∈ Set.Icc (0:ℝ) T, ∀ x ∈ Set.Icc (0:ℝ) (0 + δc),
          HasDerivAt (fun x' => Vt x' σ) (Wt x σ) x := by
        intro σ hσ x hx
        have hslice := hasDerivAt_slice_snd_of_contDiffOn (z := z) (θ := Θ x)
          Work.FTS.EllipticEst.isOpen_Q0
          (contDiffOn_mixed_of_four (hc4 σ hσ) (by omega : 0 + 2 ≤ 3))
          (Work.FTS.EllipticEst.mem_Q0.mpr
            ⟨hz, cth_pos (ψ₀ + 2 * x), cth_lt (ψ₀ + 2 * x)⟩)
        have hcomp := hslice.comp x (hΘderiv x)
        have hv : Work.Spaces.pth (Work.Spaces.mixed 0 2 (Work.FTS.Galerkin.slice g σ))
              z (Θ x) * Real.sin (2 * Θ x)
            = Work.Spaces.mixed 0 3 (Work.FTS.Galerkin.slice g σ) z (Θ x) := by
          rw [mixed_zero_three_eq]
          ring
        rw [hv] at hcomp
        simpa only [hVtdef, hWtdef, Function.comp_def] using hcomp
      have hLand := tau_lip_sqrt_of_primitive_Icc hT hLandau (V := Vt) (W := Wt)
        (x₀ := 0) (δc := δc) (L := Lτ) (K := 1 * Cs)
        hδcpos (by positivity) (by positivity) hVh hch hWh hdh
      have hW0 : ∀ σ : ℝ, Wt 0 σ
          = Work.Spaces.mixed 0 3 (Work.FTS.Galerkin.slice g σ) z θ := by
        intro σ
        rw [hWtdef]
        simp only [mul_zero, add_zero, hΘ0]
      have hcontWt : ContinuousWithinAt (fun σ : ℝ => Wt 0 σ) (Set.Icc (0:ℝ) T) τ := by
        rw [Metric.continuousWithinAt_iff]
        intro ε hε
        obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := continuousWithinAt_of_sqrt_bound
          (f := fun σ : ℝ => Wt 0 σ) (T := T) (τ := τ) (K := 2 * Lτ + 1 * Cs)
          (δ₀ := δc ^ 2) hε (by positivity) (by positivity)
          (fun σ hσ hστ => hLand σ hσ τ hτ hστ)
        refine ⟨min δ₂ (δc ^ 2), by positivity, ?_⟩
        intro σ hσ hd
        rw [Real.dist_eq] at hd
        exact hδ₂ σ hσ (lt_of_lt_of_le hd (min_le_left _ _))
      rw [show (fun σ : ℝ => Work.Spaces.mixed 0 3 (Work.FTS.Galerkin.slice g σ) z θ)
          = fun σ : ℝ => Wt 0 σ from funext (fun σ => (hW0 σ).symm)]
      exact hcontWt
  · -- `j ≥ 1`: the Landau step in the `z`-direction
    have hj1 : 1 ≤ j := hjpos
    have hji' : i + (j - 1) ≤ 2 := by omega
    set Vz : ℝ → ℝ → ℝ := fun x σ =>
      Work.Spaces.mixed (j - 1) i (Work.FTS.Galerkin.slice g σ) (z * Real.exp x) θ with hVzdef
    set Wz : ℝ → ℝ → ℝ := fun x σ =>
      Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g σ) (z * Real.exp x) θ with hWzdef
    have hδc : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
    have hexp2 : Real.exp (Real.log (3 / 2)) = 3 / 2 := Real.exp_log (by norm_num)
    have hKc : 0 ≤ 2 * z * Cs := by positivity
    have hVh : ∀ σ ∈ Set.Icc (0:ℝ) T, ∀ σ' ∈ Set.Icc (0:ℝ) T,
        ∀ x ∈ Set.Icc (0:ℝ) (0 + Real.log (3 / 2)), |Vz x σ - Vz x σ'| ≤ Lτ * |σ - σ'| := by
      intro σ hσ σ' hσ' x hx
      have h := hTau σ hσ σ' hσ' (j - 1) i hji' (z * Real.exp x) θ
        (by positivity) hθ0 hθπ
      simpa only [hVzdef] using h
    have hch : ∀ σ ∈ Set.Icc (0:ℝ) T,
        ContinuousOn (fun x => Wz x σ) (Set.Icc (0:ℝ) (0 + Real.log (3 / 2))) := by
      intro σ hσ
      have hc : ContinuousOn (fun p : ℝ × ℝ =>
          Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g σ) p.1 p.2)
          Work.FTS.EllipticEst.Q0 := continuousOn_mixed_of_four (hc4 σ hσ) (by omega)
      have hexpc : Continuous fun x : ℝ => z * Real.exp x :=
        continuous_const.mul Real.continuous_exp
      have hmap : ∀ x ∈ Set.Icc (0:ℝ) (0 + Real.log (3 / 2)),
          (z * Real.exp x, θ) ∈ Work.FTS.EllipticEst.Q0 :=
        fun x _ => Work.FTS.EllipticEst.mem_Q0.mpr ⟨by positivity, hθ0, hθπ⟩
      have hcomp := hc.comp (hexpc.continuousOn.prodMk continuousOn_const) hmap
      simpa only [hWzdef, Function.comp_def] using hcomp
    have hWh : ∀ σ ∈ Set.Icc (0:ℝ) T, ∀ x ∈ Set.Icc (0:ℝ) (0 + Real.log (3 / 2)),
        |Wz x σ - Wz 0 σ| ≤ (2 * z * Cs) * |x - 0| := by
      intro σ hσ x hx
      have hx' : x ∈ Set.Icc (0:ℝ) (Real.log (3 / 2)) := by simpa only [zero_add] using hx
      have hx0 : 0 ≤ x := hx'.1
      have hexp_le : Real.exp x ≤ 3 / 2 := by
        calc Real.exp x ≤ Real.exp (Real.log (3 / 2)) := Real.exp_le_exp.mpr hx'.2
          _ = 3 / 2 := hexp2
      have hexp_ge : 1 ≤ Real.exp x := Real.one_le_exp hx0
      have hmem : z * Real.exp x ∈ Set.Icc (z / 2) (3 * z / 2) :=
        ⟨by nlinarith, by nlinarith⟩
      have h := hSpaceZ σ hσ j i hji (z * Real.exp x) hmem θ hθmem' z hzmem'
      have h2 : |z * Real.exp x - z| ≤ 2 * z * |x| := by
        have h3 : z * Real.exp x - z = z * (Real.exp x - 1) := by ring
        rw [h3, abs_mul, abs_of_pos hz]
        have h4 : |Real.exp x - 1| ≤ 2 * |x| := by
          have hdiff : ∀ y ∈ Set.Icc (0:ℝ) (Real.log (3 / 2)),
              DifferentiableAt ℝ Real.exp y := fun y _ => Real.differentiableAt_exp
          have hbnd : ∀ y ∈ Set.Icc (0:ℝ) (Real.log (3 / 2)),
              ‖deriv Real.exp y‖ ≤ 3 / 2 := by
            intro y hy
            rw [Real.norm_eq_abs, Real.deriv_exp, abs_of_pos (Real.exp_pos y)]
            calc Real.exp y ≤ Real.exp (Real.log (3 / 2)) := Real.exp_le_exp.mpr hy.2
              _ = 3 / 2 := hexp2
          have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbnd
            (convex_Icc (0:ℝ) (Real.log (3 / 2)))
            (show (0:ℝ) ∈ Set.Icc (0:ℝ) (Real.log (3 / 2)) from ⟨le_rfl, hδc.le⟩) hx'
          rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.exp_zero, sub_zero] at hmvt
          nlinarith [abs_nonneg x]
        nlinarith [abs_nonneg x]
      rw [hWzdef]
      simp only [Real.exp_zero, mul_one]
      calc |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g σ) (z * Real.exp x) θ
            - Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g σ) z θ|
          ≤ Cs * |z * Real.exp x - z| := h
        _ ≤ Cs * (2 * z * |x|) := mul_le_mul_of_nonneg_left h2 hCsnn
        _ = (2 * z * Cs) * |x - 0| := by rw [sub_zero]; ring
    have hdh : ∀ σ ∈ Set.Icc (0:ℝ) T, ∀ x ∈ Set.Icc (0:ℝ) (0 + Real.log (3 / 2)),
        HasDerivAt (fun x' => Vz x' σ) (Wz x σ) x := by
      intro σ hσ x hx
      have hslice := hasDerivAt_slice_fst_of_contDiffOn (z := z * Real.exp x) (θ := θ)
        Work.FTS.EllipticEst.isOpen_Q0
        (contDiffOn_mixed_of_four (hc4 σ hσ) (by omega : (j - 1) + i ≤ 3))
        (Work.FTS.EllipticEst.mem_Q0.mpr ⟨by positivity, hθ0, hθπ⟩)
      have hexpd : HasDerivAt (fun x' : ℝ => z * Real.exp x') (z * Real.exp x) x :=
        (Real.hasDerivAt_exp x).const_mul z
      have hcomp := hslice.comp x hexpd
      have hv : Work.Spaces.pz (Work.Spaces.mixed (j - 1) i (Work.FTS.Galerkin.slice g σ))
            (z * Real.exp x) θ * (z * Real.exp x)
          = Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g σ) (z * Real.exp x) θ := by
        rw [mixed_fst_eq_mul_pz _ hj1]
        ring
      rw [hv] at hcomp
      simpa only [hVzdef, hWzdef, Function.comp_def] using hcomp
    have hLand := tau_lip_sqrt_of_primitive_Icc hT hLandau (V := Vz) (W := Wz)
      (x₀ := 0) (δc := Real.log (3 / 2)) (L := Lτ) (K := 2 * z * Cs)
      hδc hLτnn hKc hVh hch hWh hdh
    have hW0 : ∀ σ : ℝ, Wz 0 σ
        = Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g σ) z θ := by
      intro σ
      rw [hWzdef]
      simp only [Real.exp_zero, mul_one]
    have hcontWz : ContinuousWithinAt (fun σ : ℝ => Wz 0 σ) (Set.Icc (0:ℝ) T) τ := by
      rw [Metric.continuousWithinAt_iff]
      intro ε hε
      obtain ⟨δ, hδpos, hδ⟩ := continuousWithinAt_of_sqrt_bound
        (f := fun σ : ℝ => Wz 0 σ) (T := T) (τ := τ) (K := 2 * Lτ + 2 * z * Cs)
        (δ₀ := (Real.log (3 / 2)) ^ 2) hε (by positivity) (by positivity)
        (fun σ hσ hστ => hLand σ hσ τ hτ hστ)
      refine ⟨min δ ((Real.log (3 / 2)) ^ 2), by positivity, ?_⟩
      intro σ hσ hd
      rw [Real.dist_eq] at hd
      exact hδ σ hσ (lt_of_lt_of_le hd (min_le_left _ _))
    rw [show (fun σ : ℝ => Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g σ) z θ)
        = fun σ : ℝ => Wz 0 σ from funext (fun σ => (hW0 σ).symm)]
    exact hcontWz

end Work.FTS_RegExport.RXT
