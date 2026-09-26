import Mathlib
import Submission.Work.Drive.EpsForm.SweepGenericity
import Submission.Work.Drive.Generic.ae_height_morse
import Submission.Work.Smooth.Morse.Immersion.isImmersion
import Submission.Work.Embedding.finite_of_isClosed_forall_isolated
import Submission.Work.Smooth.Morse.aeRegularValues_of_contDiffTwo
import Submission.Work.Drive.N2.exists_enum_critical
import Submission.Work.Drive.EpsForm.twoPlanesSphere_finite
import Submission.Work.Drive.EpsForm.exists_unit_orthogonal_close_strict
import Submission.Work.Drive.EpsForm.exists_orthonormal_w

namespace Work.Drive.EpsForm

open LeanEval.KnotTheory.PardonDistortion
open Set
open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

/-! ## Elementary helpers for the tilted sweep genericity -/

/-- The unit vector `shiftVσ σ 1` in the `σ 2` direction has norm `1`. -/
theorem norm_shiftVσ_one (σ : Equiv.Perm (Fin 3)) : ‖Work.BoxShrink.shiftVσ σ 1‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  rw [Finset.sum_eq_single (σ 2)]
  · simp [Work.BoxShrink.shiftVσ_apply]
  · intro b _ hb; simp [Work.BoxShrink.shiftVσ_apply, hb]
  · intro h; exact absurd (Finset.mem_univ (σ 2)) h

/-- The sweep height of the functional `⟪n, ·⟫` is the pull-back of `⟪n, ·⟫` to the parameter
plane. -/
theorem sweepHeight_innerSL (ψ : Submission.Diffeo) (n : R3) :
    sweepHeight ψ ((innerSL ℝ) n) =
      fun q : ℝ × ℝ => inner ℝ n (Work.BoxShrink.Pinch.par ψ q) := by
  funext q
  show (((innerSL ℝ) n) (Work.BoxShrink.Pinch.par ψ q)) = _
  rw [innerSL_apply_apply]

/-- A conull set meets every ball of positive radius. -/
theorem exists_mem_ball_of_ae (P : R3 → Prop)
    (h : ∀ᵐ v ∂(MeasureTheory.volume : MeasureTheory.Measure R3), P v)
    (n₀ : R3) {r : ℝ} (hr : 0 < r) : ∃ n ∈ Metric.ball n₀ r, P n := by
  by_contra hc
  push Not at hc
  have h0 : MeasureTheory.volume {v : R3 | ¬ P v} = 0 := by
    rw [← MeasureTheory.ae_iff]; exact h
  have hsub : Metric.ball n₀ r ⊆ {v : R3 | ¬ P v} := fun v hv => hc v hv
  have hle : MeasureTheory.volume (Metric.ball n₀ r) ≤ (0 : ENNReal) := by
    calc MeasureTheory.volume (Metric.ball n₀ r) ≤ MeasureTheory.volume {v : R3 | ¬ P v} :=
          measure_mono hsub
      _ = 0 := h0
  have hpos : 0 < MeasureTheory.volume (Metric.ball n₀ r) :=
    Metric.measure_ball_pos MeasureTheory.volume n₀ hr
  exact (lt_irrefl (0 : ENNReal)) (lt_of_lt_of_le hpos hle)

/-- The derivative of a function that is periodic with period `c` is periodic with the same
period. -/
theorem fderiv_periodic_add {h : ℝ × ℝ → ℝ} {c : ℝ × ℝ} (hd : ∀ q, DifferentiableAt ℝ h q)
    (hper : ∀ q, h (q + c) = h q) (p : ℝ × ℝ) : fderiv ℝ h (p + c) = fderiv ℝ h p := by
  have hf : DifferentiableAt ℝ (fun q : ℝ × ℝ => q + c) p := by fun_prop
  have hcomp := fderiv_comp (𝕜 := ℝ) (x := p) (f := fun q : ℝ × ℝ => q + c) (g := h) (hd _) hf
  have heq : h ∘ (fun q : ℝ × ℝ => q + c) = h := funext hper
  have hT : fderiv ℝ (fun q : ℝ × ℝ => q + c) p = ContinuousLinearMap.id ℝ (ℝ × ℝ) := by
    rw [show (fun q : ℝ × ℝ => q + c) = (fun q => id q + c) from rfl, fderiv_add_const, fderiv_id]
  rw [heq, hT, ContinuousLinearMap.comp_id] at hcomp
  exact hcomp.symm

/-- A real number is congruent modulo `2π` to a point of `[0, 2π]`. -/
theorem exists_int_mul_two_pi (x : ℝ) :
    ∃ k : ℤ, x - (k : ℝ) * (2 * Real.pi) ∈ Set.Icc 0 (2 * Real.pi) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  refine ⟨⌊x / (2 * Real.pi)⌋, ?_, ?_⟩
  · have h := Int.floor_le (x / (2 * Real.pi))
    have h' : (⌊x / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) ≤ x :=
      (le_div_iff₀ hpi).mp h
    linarith
  · have h := Int.lt_floor_add_one (x / (2 * Real.pi))
    have h' : x < ((⌊x / (2 * Real.pi)⌋ : ℝ) + 1) * (2 * Real.pi) :=
      (div_lt_iff₀ hpi).mp h
    nlinarith [h']

/-- A nondegenerate critical point of a `C²` function on the plane is isolated in the critical
set. -/
theorem eventually_eq_of_crit_nondegen {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hnd : ∀ p, fderiv ℝ g p = 0 → Function.Injective (fderiv ℝ (fderiv ℝ g) p)) :
    ∀ p, fderiv ℝ g p = 0 → ∀ᶠ q in nhds p, fderiv ℝ g q = 0 → q = p := by
  intro p hp
  have hcd : ContDiffAt ℝ 1 (fderiv ℝ g) p :=
    hg.contDiffAt.fderiv_right (m := 1) (n := 2) (by norm_num)
  have hstr : HasStrictFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) p) p :=
    hcd.hasStrictFDerivAt (by norm_num)
  have hinj : Function.Injective (fderiv ℝ (fderiv ℝ g) p) := hnd p hp
  have h := Work.Drive.N2.eventually_eq_of_hasStrictFDerivAt_injective hstr hinj
  filter_upwards [h] with q hq
  intro hq0
  exact hq (by rw [hq0, hp])

/-- A `C²` function on the plane all of whose critical points are nondegenerate has only finitely
many critical points in the fundamental domain `[0, 2π]²`. -/
theorem finite_critSet_box {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hnd : ∀ p, fderiv ℝ g p = 0 → Function.Injective (fderiv ℝ (fderiv ℝ g) p)) :
    ({p : ℝ × ℝ | fderiv ℝ g p = 0} ∩ (Set.Icc 0 (2 * Real.pi) ×ˢ Set.Icc 0 (2 * Real.pi))).Finite := by
  have h4 := eventually_eq_of_crit_nondegen hg hnd
  have hcont : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by norm_num)
  have hC : IsClosed {p : ℝ × ℝ | fderiv ℝ g p = 0} := by
    have h : {p : ℝ × ℝ | fderiv ℝ g p = 0} = (fderiv ℝ g) ⁻¹' {0} := rfl
    rw [h]; exact isClosed_singleton.preimage hcont
  have hKc : IsCompact (Set.Icc (0:ℝ) (2*Real.pi) ×ˢ Set.Icc (0:ℝ) (2*Real.pi)) :=
    isCompact_Icc.prod isCompact_Icc
  have hcomp : IsCompact (Set.Icc (0:ℝ) (2*Real.pi) ×ˢ Set.Icc (0:ℝ) (2*Real.pi) ∩
      {p : ℝ × ℝ | fderiv ℝ g p = 0}) := hKc.inter_right hC
  have hdisj : IsDiscrete (Set.Icc (0:ℝ) (2*Real.pi) ×ˢ Set.Icc (0:ℝ) (2*Real.pi) ∩
      {p : ℝ × ℝ | fderiv ℝ g p = 0}) := by
    rw [isDiscrete_iff_forall_mem_exists_isOpen]
    intro y hy
    have hyC : fderiv ℝ g y = 0 := hy.2
    obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff.mp (h4 y hyC)
    refine ⟨Metric.ball y ε, Metric.isOpen_ball, ?_⟩
    ext z
    constructor
    · rintro ⟨hzball, hzmem⟩
      have hzC : fderiv ℝ g z = 0 := hzmem.2
      have : z = y := hεP hzball hzC
      simpa [this]
    · rintro hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨Metric.mem_ball_self hε, hy⟩
  have hfin := hcomp.finite hdisj
  rwa [Set.inter_comm] at hfin

/-- The sweep height is `C²`. -/
theorem sweepHeight_contDiff_two (ψ : Submission.Diffeo) (ℓ : R3 →L[ℝ] ℝ) :
    ContDiff ℝ 2 (sweepHeight ψ ℓ) :=
  (Work.Smooth.Morse.pullback_contDiff ψ ℓ.contDiff).of_le (WithTop.coe_le_coe.mpr le_top)

/-- The derivative of the sweep height is `2π`-periodic in both variables. -/
theorem fderiv_sweepHeight_periodic (ψ : Submission.Diffeo) (ℓ : R3 →L[ℝ] ℝ) (k m : ℤ)
    (p : ℝ × ℝ) :
    fderiv ℝ (sweepHeight ψ ℓ) (p.1 - (k : ℝ) * (2 * Real.pi), p.2 - (m : ℝ) * (2 * Real.pi))
      = fderiv ℝ (sweepHeight ψ ℓ) p := by
  have hd : ∀ q : ℝ × ℝ, DifferentiableAt ℝ (sweepHeight ψ ℓ) q := by
    intro q
    exact ((sweepHeight_contDiff_two ψ ℓ).contDiffAt).differentiableAt (by norm_num)
  have hbase1 : Function.Periodic (sweepHeight ψ ℓ) (((2:ℝ)*Real.pi), 0) := by
    intro r
    have hrr : r + (((2:ℝ)*Real.pi), 0) = (r.1 + 2*Real.pi, r.2) := by
      ext <;> simp [Prod.mk_add_mk]
    rw [hrr]
    exact Work.Smooth.Morse.pullback_add_two_pi_left ψ (fun y => ℓ y) r
  have hbase2 : Function.Periodic (sweepHeight ψ ℓ) ((0:ℝ), ((2:ℝ)*Real.pi)) := by
    intro r
    have hrr : r + ((0:ℝ), ((2:ℝ)*Real.pi)) = (r.1, r.2 + 2*Real.pi) := by
      ext <;> simp [Prod.mk_add_mk]
    rw [hrr]
    exact Work.Smooth.Morse.pullback_add_two_pi_right ψ (fun y => ℓ y) r
  have hF1 : Function.Periodic (fderiv ℝ (sweepHeight ψ ℓ)) (((2:ℝ)*Real.pi), 0) :=
    fun q => fderiv_periodic_add hd hbase1 q
  have hF2 : Function.Periodic (fderiv ℝ (sweepHeight ψ ℓ)) ((0:ℝ), ((2:ℝ)*Real.pi)) :=
    fun q => fderiv_periodic_add hd hbase2 q
  have hc1 : ((↑(-k) : ℝ × ℝ) * (((2:ℝ)*Real.pi), 0)) = (-((k:ℝ)*(2*Real.pi)), 0) := by
    ext <;> simp [Prod.mul_def, Int.cast_neg, Int.cast_mul, mul_comm, mul_left_comm, mul_assoc]
  have hc2 : ((↑(-m) : ℝ × ℝ) * ((0:ℝ), ((2:ℝ)*Real.pi))) = (0, -((m:ℝ)*(2*Real.pi))) := by
    ext <;> simp [Prod.mul_def, Int.cast_neg, Int.cast_mul, mul_comm, mul_left_comm, mul_assoc]
  have h1 := (hF1.int_mul (-k)); rw [hc1] at h1
  have h2 := (hF2.int_mul (-m)); rw [hc2] at h2
  have key1 : p + (-((k:ℝ)*(2*Real.pi)), 0) = (p.1 - (k:ℝ)*(2*Real.pi), p.2) := by
    ext <;> simp [Prod.mk_add_mk, sub_eq_add_neg] <;> ring
  have key2 : (p.1 - (k:ℝ)*(2*Real.pi), p.2) + (0, -((m:ℝ)*(2*Real.pi)))
      = (p.1 - (k:ℝ)*(2*Real.pi), p.2 - (m:ℝ)*(2*Real.pi)) := by
    ext <;> simp [Prod.mk_add_mk, sub_eq_add_neg] <;> ring
  rw [← key2, ← key1, h2 (p + (-((k:ℝ)*(2*Real.pi)), 0)), h1 p]

/-- The parametrisation of the torus is `2π`-periodic in both variables. -/
theorem par_periodic (ψ : Submission.Diffeo) (k m : ℤ) (p : ℝ × ℝ) :
    Work.BoxShrink.Pinch.par ψ (p.1 - (k : ℝ) * (2 * Real.pi), p.2 - (m : ℝ) * (2 * Real.pi))
      = Work.BoxShrink.Pinch.par ψ p := by
  show ψ (Work.Core.torusMap (p.1 - (k : ℝ) * (2 * Real.pi)) (p.2 - (m : ℝ) * (2 * Real.pi)))
      = ψ (Work.Core.torusMap p.1 p.2)
  have hθ : ∀ q : ℝ, Work.Core.torusMap (p.1 - (k : ℝ) * (2 * Real.pi)) q
      = Work.Core.torusMap p.1 q := by
    intro q
    have hper : Function.Periodic (fun θ : ℝ => Work.Core.torusMap θ q) (2 * Real.pi) :=
      fun θ => Work.Core.torusMap_add_two_pi_left θ q
    have h3 := (hper.int_mul (-k)) p.1
    have key : p.1 + (↑(-k) : ℝ) * (2 * Real.pi) = p.1 - (k : ℝ) * (2 * Real.pi) := by
      simp [Int.cast_neg, sub_eq_add_neg]
    rw [key] at h3
    exact h3
  have hφ : ∀ q : ℝ, Work.Core.torusMap q (p.2 - (m : ℝ) * (2 * Real.pi))
      = Work.Core.torusMap q p.2 := by
    intro q
    have hper : Function.Periodic (fun φ : ℝ => Work.Core.torusMap q φ) (2 * Real.pi) :=
      fun φ => Work.Core.torusMap_add_two_pi_right q φ
    have h3 := (hper.int_mul (-m)) p.2
    have key : p.2 + (↑(-m) : ℝ) * (2 * Real.pi) = p.2 - (m : ℝ) * (2 * Real.pi) := by
      simp [Int.cast_neg, sub_eq_add_neg]
    rw [key] at h3
    exact h3
  rw [hθ, hφ]

/-- Every critical point of the sweep height is realised in the fundamental domain `[0, 2π]²`. -/
theorem exists_fundamental_of_crit (ψ : Submission.Diffeo) (ℓ : R3 →L[ℝ] ℝ) {p : ℝ × ℝ}
    (hp : fderiv ℝ (sweepHeight ψ ℓ) p = 0) :
    ∃ p' : ℝ × ℝ, p' ∈ Set.Icc 0 (2 * Real.pi) ×ˢ Set.Icc 0 (2 * Real.pi) ∧
      fderiv ℝ (sweepHeight ψ ℓ) p' = 0 ∧
      Work.BoxShrink.Pinch.par ψ p' = Work.BoxShrink.Pinch.par ψ p := by
  obtain ⟨k, hk⟩ := exists_int_mul_two_pi p.1
  obtain ⟨m, hm⟩ := exists_int_mul_two_pi p.2
  refine ⟨(p.1 - (k : ℝ) * (2 * Real.pi), p.2 - (m : ℝ) * (2 * Real.pi)), ⟨hk, hm⟩, ?_, ?_⟩
  · rw [fderiv_sweepHeight_periodic]; exact hp
  · exact par_periodic ψ k m p



/-- Existence of a unit vector orthogonal to a nonzero vector of `ℝ³`. -/
theorem exists_unit_orthogonal {e : R3} (he : e ≠ 0) :
    ∃ n₀ : R3, ‖n₀‖ = 1 ∧ inner ℝ n₀ e = 0 := by
  obtain ⟨m, hmem, hmne⟩ : ∃ m : R3, m ∈ (ℝ ∙ e)ᗮ ∧ m ≠ 0 :=
    Submodule.exists_mem_ne_zero_of_ne_bot (p := (ℝ ∙ e)ᗮ) (by
      intro h
      have h1 : Module.finrank ℝ ↥(ℝ ∙ e) = 1 := finrank_span_singleton he
      have h2 := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℝ) (ℝ ∙ e)
      rw [h, finrank_bot, add_zero, h1, finrank_euclideanSpace, Fintype.card_fin] at h2
      exact absurd h2 (by norm_num))
  have hmorth : inner ℝ m e = 0 :=
    (Submodule.mem_orthogonal_singleton_iff_inner_left (𝕜 := ℝ)).mp hmem
  refine ⟨(‖m‖)⁻¹ • m, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg m),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hmne)]
  · rw [real_inner_smul_left, hmorth, mul_zero]

/-- **P1 (corrected: the slab tilts, and the tilt is inside the `ε`-slack).**  At every
configuration there are a unit direction `v` across the slab within `ε` of the `σ 2` direction, a
half-width `h > 0`, a functional `ℓ` vanishing on `v` but not identically zero, and a finite set
`exc` of levels such that

  (i) away from `exc` the wall `{ℓ = ·}` meets the surface transversally at every surface point of
      the box inside the closed tilted slab `{y | |⟪v,y⟫ - (⟪v,c⟫ + u)| ≤ h}`;
  (ii) at every critical point of the sweep height inside the box and the slab, the height is
      nondegenerate in the parameter plane and its value lies in `exc`;
  (iii) two critical points of the sweep height inside the box and the slab with the same value
      coincide (so each level of `exc` carries a single handle — what P3 consumes). -/
theorem tiltedSweepGenericity_holds (ψ : Submission.Diffeo) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    ∃ (v : R3) (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (exc : Finset ℝ),
      ‖v‖ = 1 ∧ ‖v - Work.BoxShrink.shiftVσ σ 1‖ ≤ Submission.eps ∧
      ℓ v = 0 ∧ ℓ ≠ 0 ∧ 0 < h ∧
      (∀ lam ∉ exc, ∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ →
        Work.BoxShrink.Pinch.par ψ p ∈
          Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h →
        ℓ (Work.BoxShrink.Pinch.par ψ p) = lam →
        fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠ 0) ∧
      (∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ →
        Work.BoxShrink.Pinch.par ψ p ∈
          Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h →
        fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p = 0 →
        Function.Injective (fderiv ℝ (fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ)) p) ∧
          ℓ (Work.BoxShrink.Pinch.par ψ p) ∈ exc) ∧
      (∀ p p' : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ →
        Work.BoxShrink.Pinch.par ψ p' ∈ Submission.PBox s c σ →
        Work.BoxShrink.Pinch.par ψ p ∈
          Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h →
        Work.BoxShrink.Pinch.par ψ p' ∈
          Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h →
        fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p = 0 →
        fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p' = 0 →
        ℓ (Work.BoxShrink.Pinch.par ψ p) = ℓ (Work.BoxShrink.Pinch.par ψ p') →
        Work.BoxShrink.Pinch.par ψ p = Work.BoxShrink.Pinch.par ψ p') := by
  classical
  -- ## 1. the slab direction and the Morse height direction
  set e : R3 := Work.BoxShrink.shiftVσ σ 1 with he
  have he1 : ‖e‖ = 1 := norm_shiftVσ_one σ
  have he0 : e ≠ 0 := by intro h; rw [h, norm_zero] at he1; norm_num at he1
  obtain ⟨n₀, hn₀norm, hn₀orth⟩ := exists_unit_orthogonal he0
  have hΦ3 : ContDiff ℝ 3 (Work.BoxShrink.Pinch.par ψ) :=
    (Work.Smooth.Morse.param_contDiff ψ).of_le (WithTop.coe_le_coe.mpr le_top)
  have himm : ∀ p : ℝ × ℝ, Function.Injective (fderiv ℝ (Work.BoxShrink.Pinch.par ψ) p) :=
    Work.Smooth.Morse.Immersion.isImmersion ψ
  have hae := Work.Drive.Generic.ae_height_morse hΦ3 himm
  obtain ⟨n, hnball, hnMorse⟩ :=
    exists_mem_ball_of_ae _ hae n₀ (show (0 : ℝ) < 1 / 64 by norm_num)
  have hn_dist : ‖n - n₀‖ < 1 / 64 := by
    rw [Metric.mem_ball, dist_eq_norm] at hnball; exact hnball
  have hn_ge : 63 / 64 < ‖n‖ := by
    have h1 : -(‖n - n₀‖) ≤ ‖n‖ - ‖n₀‖ := (abs_le.mp (abs_norm_sub_norm_le n n₀)).1
    rw [hn₀norm] at h1
    linarith
  have hn_ne : n ≠ 0 := by
    intro h; rw [h, norm_zero] at hn_ge; norm_num at hn_ge
  have hn_orth_small : |inner ℝ n e| ≤ ‖n‖ / 16 := by
    have h1 : inner ℝ n e = inner ℝ (n - n₀) e := by rw [inner_sub_left, hn₀orth, sub_zero]
    rw [h1]
    have h2 : |inner ℝ (n - n₀) e| ≤ ‖n - n₀‖ * ‖e‖ := abs_real_inner_le_norm _ _
    rw [he1, mul_one] at h2
    have h3 : (1 : ℝ) / 64 ≤ ‖n‖ / 16 := by linarith
    linarith
  set ℓ : R3 →L[ℝ] ℝ := (innerSL ℝ) n with hℓ
  have hheight : sweepHeight ψ ℓ =
      fun q : ℝ × ℝ => inner ℝ n (Work.BoxShrink.Pinch.par ψ q) := by
    rw [hℓ]; exact sweepHeight_innerSL ψ n
  have hMorse : ∀ p : ℝ × ℝ, fderiv ℝ (sweepHeight ψ ℓ) p = 0 →
      Function.Injective (fderiv ℝ (fderiv ℝ (sweepHeight ψ ℓ)) p) := by
    intro p hp
    rw [hheight] at hp ⊢
    intro a b hab
    have h0 : (fderiv ℝ (fderiv ℝ fun q : ℝ × ℝ => inner ℝ n (Work.BoxShrink.Pinch.par ψ q)) p)
        (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have hres := hnMorse p hp (a - b) (fun w' => by rw [h0]; rfl)
    exact sub_eq_zero.mp hres
  have hℓne : ℓ ≠ 0 := by
    rw [hℓ]
    intro hzero
    have h1 : inner ℝ n n = 0 := by
      have := congrArg (fun (L : R3 →L[ℝ] ℝ) => L n) hzero
      simpa [innerSL_apply_apply] using this
    have h2 : ‖n‖ = 0 := by
      rw [real_inner_self_eq_norm_sq] at h1
      nlinarith [h1, norm_nonneg n]
    exact hn_ne (norm_eq_zero.mp h2)
  -- ## 2. the (finite) set of critical surface points in the fundamental domain
  have hfin : ({p : ℝ × ℝ | fderiv ℝ (sweepHeight ψ ℓ) p = 0} ∩
      (Set.Icc 0 (2 * Real.pi) ×ˢ Set.Icc 0 (2 * Real.pi))).Finite :=
    finite_critSet_box (sweepHeight_contDiff_two ψ ℓ) hMorse
  set Zs : Finset R3 := (hfin.image (Work.BoxShrink.Pinch.par ψ)).toFinset with hZs
  have mem_Zs : ∀ p : ℝ × ℝ, fderiv ℝ (sweepHeight ψ ℓ) p = 0 →
      Work.BoxShrink.Pinch.par ψ p ∈ (Zs : Set R3) := by
    intro p hp
    obtain ⟨p', hp'K, hp'c, hp'par⟩ := exists_fundamental_of_crit ψ ℓ hp
    rw [← hp'par, hZs, Set.Finite.coe_toFinset]
    exact ⟨p', ⟨hp'c, hp'K⟩, rfl⟩
  -- ## 3. the base direction of the tilted slab and the orthonormal frame
  obtain ⟨v₀, hv₀unit, hv₀orth, hv₀dist⟩ :=
    exists_unit_orthogonal_close_strict he1 (by linarith) hn_orth_small
  set nhat : R3 := (‖n‖)⁻¹ • n with hnhat
  have hn_unit : ‖n‖ ≠ 0 := norm_ne_zero_iff.mpr hn_ne
  have hnhat_unit : ‖nhat‖ = 1 := by
    rw [hnhat, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg n),
      inv_mul_cancel₀ hn_unit]
  have hv₀orthn : inner ℝ nhat v₀ = 0 := by
    rw [hnhat, real_inner_smul_left, hv₀orth, mul_zero]
  obtain ⟨w, hw1, hwn, hwv⟩ := exists_orthonormal_w hnhat_unit hv₀unit hv₀orthn
  have hnv : inner ℝ n v₀ = 0 := hv₀orth
  have hnw : inner ℝ n w = 0 := by
    have hn_eq : n = ‖n‖ • nhat := by
      rw [hnhat, smul_smul, mul_inv_cancel₀ hn_unit, one_smul]
    rw [hn_eq, real_inner_smul_left, hwn, mul_zero]
  have hvw : inner ℝ v₀ w = 0 := hwv
  have hwv' : inner ℝ w v₀ = 0 := by rw [real_inner_comm]; exact hwv
  -- ## 4. the arc of admissible slab normals is infinite
  set arc : ℝ → R3 := fun θ => Real.cos θ • v₀ + Real.sin θ • w with harc
  have harc_val : ∀ θ, arc θ = Real.cos θ • v₀ + Real.sin θ • w := fun θ => by rw [harc]
  have harc_cont : Continuous arc := by rw [harc]; fun_prop
  have harc_orth : ∀ θ, inner ℝ n (arc θ) = 0 := by
    intro θ
    rw [harc_val θ, inner_add_right, real_inner_smul_right, real_inner_smul_right, hnv, hnw,
      mul_zero, mul_zero, add_zero]
  have harc_norm : ∀ θ, ‖arc θ‖ = 1 := by
    intro θ
    have h1 : inner ℝ (arc θ) (arc θ) = Real.cos θ ^ 2 + Real.sin θ ^ 2 := by
      rw [harc_val θ]
      simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hv₀unit, hw1, hvw, hwv']
      ring
    have h2 : ‖arc θ‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq, h1]; nlinarith [Real.sin_sq_add_cos_sq θ]
    rcases sq_eq_one_iff.mp h2 with h | h
    · exact h
    · exact absurd h (by intro hh; rw [hh] at *; linarith [norm_nonneg (arc θ)])
  set A : Set R3 := {v' : R3 | inner ℝ n v' = 0 ∧ ‖v'‖ = 1 ∧ ‖v' - e‖ ≤ Submission.eps} with hA
  have hAinf : A.Infinite := by
    have hEv : ∀ᶠ θ in nhds (0 : ℝ), ‖arc θ - e‖ < Submission.eps := by
      have hc : Continuous (fun θ : ℝ => ‖arc θ - e‖) := (harc_cont.sub continuous_const).norm
      exact (isOpen_lt hc continuous_const).mem_nhds (by
        have h0 : arc 0 = v₀ := by rw [harc_val 0]; simp
        rw [Set.mem_setOf_eq, h0, Submission.eps]
        linarith)
    obtain ⟨θ₀, hθ₀pos, hθ₀sub⟩ := Metric.eventually_nhds_iff.mp hEv
    set θ₁ : ℝ := min θ₀ 1 with hθ₁def
    have hθ₁pos : 0 < θ₁ := by rw [hθ₁def]; exact lt_min hθ₀pos one_pos
    have hθ₁le1 : θ₁ ≤ 1 := by rw [hθ₁def]; exact min_le_right _ _
    have hθ₁leθ₀ : θ₁ ≤ θ₀ := by rw [hθ₁def]; exact min_le_left _ _
    have hsub : arc '' Set.Ioo (-θ₁) θ₁ ⊆ A := by
      rintro _ ⟨θ, hθ, rfl⟩
      obtain ⟨hθl, hθr⟩ := hθ
      refine ⟨harc_orth θ, harc_norm θ, le_of_lt (hθ₀sub ?_)⟩
      rw [dist_eq_norm, sub_zero, Real.norm_eq_abs, abs_lt]
      exact ⟨by linarith, by linarith⟩
    have hinj : Set.InjOn arc (Set.Ioo (-θ₁) θ₁) := by
      intro a ha b hb hab
      have hsin : Real.sin a = Real.sin b := by
        have h := congrArg (fun x : R3 => inner ℝ x w) hab
        rw [harc_val a, harc_val b] at h
        simp only [inner_add_left, real_inner_smul_left, hvw, real_inner_self_eq_norm_sq, hw1,
          mul_one, mul_zero, add_zero, one_pow] at h
        simpa using h
      have ha' : a ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
        rw [Set.mem_Icc]; constructor <;> linarith [ha.1, ha.2, hθ₁le1, Real.pi_gt_three]
      have hb' : b ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
        rw [Set.mem_Icc]; constructor <;> linarith [hb.1, hb.2, hθ₁le1, Real.pi_gt_three]
      exact Real.strictMonoOn_sin.injOn ha' hb' hsin
    exact ((Set.Ioo_infinite (by linarith : (-θ₁) < θ₁)).image hinj).mono hsub

  -- ## 5. the finitely many bad slab normals
  set Zbox : Finset R3 := Zs.filter (fun z => z ∈ Submission.PBox s c σ) with hZbox
  set L : Finset R3 :=
    Zbox.filter (fun z => z - c ∈ Submodule.span ℝ ({n} : Set R3) ∧ u = 0) with hL
  set off : Finset R3 := Zbox \ L with hoff
  set ZB : Finset R3 :=
    Zbox.filter (fun z => z - c ∉ Submodule.span ℝ ({n} : Set R3)) with hZB
  set Badset : Set R3 := {v' : R3 | inner ℝ n v' = 0 ∧ ‖v'‖ = 1 ∧
      ∃ z ∈ (ZB : Set R3), inner ℝ (z - c) v' = u} with hBadset
  have hBadfin : Badset.Finite := by
    have hsub : Badset ⊆ ⋃ z ∈ (ZB : Set R3),
        {v' : R3 | inner ℝ n v' = 0 ∧ inner ℝ (z - c) v' = u ∧ ‖v'‖ = 1} := by
      rintro v' ⟨h1, h2, z, hz, h3⟩
      exact Set.mem_biUnion hz ⟨h1, h3, h2⟩
    refine Set.Finite.subset ?_ hsub
    refine Set.Finite.biUnion ZB.finite_toSet ?_
    intro z hz
    have hzn : z - c ∉ Submodule.span ℝ ({n} : Set R3) := (Finset.mem_filter.mp hz).2
    have hne' : ∀ t : ℝ, z - c ≠ t • n := by
      intro t ht
      exact hzn (Submodule.mem_span_singleton.mpr ⟨t, ht.symm⟩)
    exact twoPlanesSphere_finite hn_ne hne' u
  -- ## 6. choose the slab normal
  obtain ⟨v, hvmem⟩ := (hAinf.sdiff hBadfin).nonempty
  rw [Set.mem_sdiff] at hvmem
  obtain ⟨hvA, hvnotBad⟩ := hvmem
  have hvn : inner ℝ n v = 0 := hvA.1
  have hv1 : ‖v‖ = 1 := hvA.2.1
  have hvdist : ‖v - e‖ ≤ Submission.eps := hvA.2.2
  -- ## 7. the slab half-width
  have hoff_pos : ∀ z ∈ off, 0 < |inner ℝ v (z - c) - u| := by
    intro z hz
    rw [hoff, Finset.mem_sdiff] at hz
    obtain ⟨hzbox, hzL⟩ := hz
    rw [hZbox, Finset.mem_filter] at hzbox
    obtain ⟨hzZs, hzPBox⟩ := hzbox
    rw [abs_pos]
    intro hzero
    by_cases hspan : z - c ∈ Submodule.span ℝ ({n} : Set R3)
    · obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hspan
      have hzL' : z ∈ L := by
        rw [hL, Finset.mem_filter]
        refine ⟨by rw [hZbox, Finset.mem_filter]; exact ⟨hzZs, hzPBox⟩, ?_⟩
        refine ⟨hspan, ?_⟩
        have hvc : inner ℝ v (z - c) = 0 := by
          rw [← ht, real_inner_smul_right, real_inner_comm, hvn, mul_zero]
        linarith [hzero]
      exact hzL hzL'
    · have hzZB : z ∈ ZB := by
        rw [hZB, Finset.mem_filter]
        exact ⟨by rw [hZbox, Finset.mem_filter]; exact ⟨hzZs, hzPBox⟩, hspan⟩
      have hne' : inner ℝ (z - c) v ≠ u := by
        intro hcon
        exact hvnotBad (by
          rw [hBadset, Set.mem_ofPred_eq]
          exact ⟨hvn, hv1, z, hzZB, hcon⟩)
      rw [real_inner_comm] at hzero
      exact hne' (by linarith)
  obtain ⟨hh, hhpos, hhlt⟩ : ∃ hh : ℝ, 0 < hh ∧
      ∀ z ∈ off, hh < |inner ℝ v (z - c) - u| := by
    set S : Finset ℝ := off.image (fun z => |inner ℝ v (z - c) - u|) with hS
    by_cases hSne : S = ∅
    · refine ⟨1, one_pos, ?_⟩
      intro z hz
      have : |inner ℝ v (z - c) - u| ∈ S := Finset.mem_image.mpr ⟨z, hz, rfl⟩
      rw [hSne] at this; exact absurd this (Finset.notMem_empty _)
    · have hSne' : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hSne
      have hpos : 0 < S.min' hSne' := by
        obtain ⟨z', hz', hzeq⟩ := Finset.mem_image.mp (Finset.min'_mem S hSne')
        rw [← hzeq]
        exact hoff_pos z' hz'
      refine ⟨S.min' hSne' / 2, by linarith, ?_⟩
      intro z hz
      have hmem : |inner ℝ v (z - c) - u| ∈ S := Finset.mem_image.mpr ⟨z, hz, rfl⟩
      have hle : S.min' hSne' ≤ |inner ℝ v (z - c) - u| := Finset.min'_le S _ hmem
      linarith
  -- ## 8. assembly
  have par_in_L : ∀ p : ℝ × ℝ, fderiv ℝ (sweepHeight ψ ℓ) p = 0 →
      Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ →
      Work.BoxShrink.Pinch.par ψ p ∈ tiltedSlabClosed (inner ℝ v c + u) v hh →
      Work.BoxShrink.Pinch.par ψ p ∈ L := by
    intro p hcrit hpBox hslab
    rw [tiltedSlabClosed, Set.mem_ofPred_eq] at hslab
    have hpZ : Work.BoxShrink.Pinch.par ψ p ∈ (Zs : Set R3) := mem_Zs p hcrit
    have hpZbox : Work.BoxShrink.Pinch.par ψ p ∈ Zbox := by
      rw [hZbox, Finset.mem_filter]; exact ⟨hpZ, hpBox⟩
    by_contra hnotL
    have hoffmem : Work.BoxShrink.Pinch.par ψ p ∈ off := by
      rw [hoff, Finset.mem_sdiff]; exact ⟨hpZbox, hnotL⟩
    have hslab' : |inner ℝ v (Work.BoxShrink.Pinch.par ψ p - c) - u| ≤ hh := by
      have heq : |inner ℝ v (Work.BoxShrink.Pinch.par ψ p - c) - u| =
          |inner ℝ v (Work.BoxShrink.Pinch.par ψ p) - (inner ℝ v c + u)| := by
        rw [inner_sub_right]; ring_nf
      rw [heq]; exact hslab
    linarith [hhlt _ hoffmem, hslab']
  refine ⟨v, hh, ℓ, L.image (fun z => inner ℝ n z),
    hv1, hvdist, ?_, hℓne, hhpos, ?_, ?_, ?_⟩
  · rw [hℓ, innerSL_apply_apply]; exact hvn
  · -- (i)
    intro lam hlam p hpBox hpSlab hval hcrit
    have hparL := par_in_L p hcrit hpBox hpSlab
    have hmem : ℓ (Work.BoxShrink.Pinch.par ψ p) ∈ L.image (fun z => inner ℝ n z) := by
      refine Finset.mem_image.mpr ⟨_, hparL, ?_⟩
      rw [hℓ]; exact (innerSL_apply_apply ℝ n _).symm
    rw [hval] at hmem
    exact hlam hmem
  · -- (ii)
    intro p hpBox hpSlab hcrit
    exact ⟨hMorse p hcrit, by
      refine Finset.mem_image.mpr ⟨_, par_in_L p hcrit hpBox hpSlab, ?_⟩
      rw [hℓ]; exact (innerSL_apply_apply ℝ n _).symm⟩
  · -- (iii)
    intro p p' hpBox hpBox' hpSlab hpSlab' hcrit hcrit' hval
    have hL1 := par_in_L p hcrit hpBox hpSlab
    have hL2 := par_in_L p' hcrit' hpBox' hpSlab'
    obtain ⟨t1, ht1⟩ := Submodule.mem_span_singleton.mp (Finset.mem_filter.mp hL1).2.1
    obtain ⟨t2, ht2⟩ := Submodule.mem_span_singleton.mp (Finset.mem_filter.mp hL2).2.1
    have hval' : inner ℝ n (Work.BoxShrink.Pinch.par ψ p)
        = inner ℝ n (Work.BoxShrink.Pinch.par ψ p') := by
      simpa [hℓ, innerSL_apply_apply] using hval
    have hp1 : Work.BoxShrink.Pinch.par ψ p = c + t1 • n := by rw [ht1]; abel
    have hp2 : Work.BoxShrink.Pinch.par ψ p' = c + t2 • n := by rw [ht2]; abel
    simp only [hp1, hp2, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
      at hval'
    have ht_eq : t1 = t2 := by
      have hn2 : (0 : ℝ) < ‖n‖ ^ 2 := by positivity
      nlinarith [hval']
    rw [hp1, hp2, ht_eq]


end

end Work.Drive.EpsForm
