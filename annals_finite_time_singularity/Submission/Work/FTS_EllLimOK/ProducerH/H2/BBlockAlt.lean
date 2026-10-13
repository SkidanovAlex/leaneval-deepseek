/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.ProducerH.H2.BBlockAlt` — the `Bf`/`Mf`/`B2f` block of the box-`C²` clause

The third block of the `H2` chapter's `clause1`: the closed-box continuity of the three
boundary-corrected angular slopes

* `Bf L0 L1 Ψ = (θ ↦ ∂_θΨ)` with the one-sided traces `L0`, `L1` at `θ = 0`, `π/2`;
* `Mf N0 N1 Ψ = (θ ↦ ∂_θ∂_zΨ)` with the traces `N0`, `N1`;
* `B2f Ψ = (θ ↦ ∂_θ²Ψ)`, vanishing at both endpoints;

together with the two within-derivatives `∂_z Bf = Mf` (Clairaut at interior angles, the frozen
trace derivatives of `LimitsAt` at the endpoints) and `∂_θ Bf = B2f` (the interior derivative
with the vanishing traces of `∂_θ²Ψ` supplied by `ModWith`).

The continuity statements are instances of the generic boundary-correction gluing lemma
`continuousOn_glue`: an open-quadrant-`C^∞` function whose two one-sided angular traces are the
continuous functions `A0`, `A1` with rates `D0 θ^β0` and `D1 (π/2-θ)^β1` glues to a continuous
function on the closed box.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_EllLimOK.ProducerH.H2.Clause1Aux
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.BoxC2
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.th2EgRate
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.Trace

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter
namespace Work.FTS_EllLimOK.ProducerH.H2
open Work.FTS.Galerkin (Fn)
set_option autoImplicit false

/-- The general glued function `f` with boundary corrections `A0`, `A1`. -/
def glue (A0 A1 : ℝ → ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => if θ = 0 then A0 z else if θ = π / 2 then A1 z else f z θ

theorem glue_eq_zero (A0 A1 : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) : glue A0 A1 f z 0 = A0 z := by
  simp [glue]

theorem glue_of_mem_Ioo {A0 A1 : ℝ → ℝ} {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) : glue A0 A1 f z θ = f z θ := by
  have h0 : ¬ (θ = 0) := ne_of_gt hθ.1
  have h1 : ¬ (θ = (π : ℝ) / 2) := ne_of_lt hθ.2
  simp only [glue, if_neg h0, if_neg h1]

theorem uncurry_glue_zero (A0 A1 : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) :
    Function.uncurry (glue A0 A1 f) (z, 0) = A0 z := by
  show glue A0 A1 f z 0 = A0 z
  simp [glue]

theorem uncurry_glue_pi (A0 A1 : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) :
    Function.uncurry (glue A0 A1 f) (z, π / 2) = A1 z := by
  show glue A0 A1 f z (π / 2) = A1 z
  have hne : ¬ ((π : ℝ) / 2 = 0) := ne_of_gt (by positivity)
  simp [glue, hne]

theorem uncurry_glue_of_mem_Ioo {A0 A1 : ℝ → ℝ} {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Function.uncurry (glue A0 A1 f) (z, θ) = f z θ := by
  show glue A0 A1 f z θ = f z θ
  exact glue_of_mem_Ioo hθ

/-- **The boundary-correction gluing lemma.**  A function `f` that is `C^∞` on the open
quadrant, whose one-sided traces at the two angular endpoints are the continuous functions
`A0`, `A1` (with rates `D0 θ^β0`, `D1 (π/2-θ)^β1`), glues to a continuous function on the
closed box. -/
theorem continuousOn_glue {f : ℝ → ℝ → ℝ} {A0 A1 : ℝ → ℝ} {D0 D1 β0 β1 : ℝ} {a b : ℝ}
    (ha : 0 < a) (hβ0 : 0 < β0) (hβ1 : 0 < β1)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hA0 : ContinuousOn A0 (Set.Icc a b)) (hA1 : ContinuousOn A1 (Set.Icc a b))
    (hd0 : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo 0 (π / 2), |f z θ - A0 z| ≤ D0 * θ ^ β0)
    (hd1 : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo 0 (π / 2),
      |f z θ - A1 z| ≤ D1 * (π / 2 - θ) ^ β1) :
    ContinuousOn (Function.uncurry (glue A0 A1 f)) (Work.FTS_EllLimOK.cbox a b) := by
  have hT : (0 : ℝ) < π / 2 := by positivity
  intro p hp
  obtain ⟨z, θ⟩ := p
  rw [Work.FTS_EllLimOK.mem_cbox] at hp
  obtain ⟨hz, hθ⟩ := hp
  have hz0 : 0 < z := lt_of_lt_of_le ha hz.1
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · -- ## the angle `θ = 0`
    subst h0
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    rw [uncurry_glue_zero]
    obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.tendsto_nhdsWithin_nhds.mp
      ((hA0.continuousWithinAt hz).tendsto) (ε / 2) (by linarith)
    have hsmall : ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 ≤ t → t < δ → D0 * t ^ β0 < ε / 2 := by
      by_cases hD : D0 ≤ 0
      · exact ⟨1, one_pos, fun t ht0 _ => by
          have h1 : D0 * t ^ β0 ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg hD (Real.rpow_nonneg ht0 _)
          linarith⟩
      · have hDpos : 0 < D0 := not_le.mp hD
        have hbase : 0 < (ε / 4) / D0 := by positivity
        refine ⟨min 1 (((ε / 4) / D0) ^ (1 / β0)),
          lt_min one_pos (Real.rpow_pos_of_pos hbase _), fun t ht0 ht1 => ?_⟩
        have hle : t ≤ (((ε / 4) / D0) ^ (1 / β0)) := (lt_min_iff.mp ht1).2.le
        have hpow : t ^ β0 ≤ (ε / 4) / D0 := by
          calc t ^ β0 ≤ ((((ε / 4) / D0) ^ (1 / β0))) ^ β0 :=
                Real.rpow_le_rpow ht0 hle hβ0.le
            _ = (ε / 4) / D0 := by
                rw [← Real.rpow_mul hbase.le, one_div_mul_cancel hβ0.ne', Real.rpow_one]
        have h1 : D0 * t ^ β0 ≤ D0 * ((ε / 4) / D0) := mul_le_mul_of_nonneg_left hpow hDpos.le
        have h2 : D0 * ((ε / 4) / D0) = ε / 4 := by field_simp
        rw [h2] at h1
        linarith
    obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := hsmall
    refine ⟨min δ₁ (min δ₂ (π / 4)), lt_min hδ₁pos (lt_min hδ₂pos (by positivity)),
      fun y hy hdist => ?_⟩
    obtain ⟨z', θ'⟩ := y
    rw [Work.FTS_EllLimOK.mem_cbox] at hy
    obtain ⟨hz', hθ'⟩ := hy
    have hdist' : max |z' - z| |θ' - 0| < min δ₁ (min δ₂ (π / 4)) := by
      rwa [Prod.dist_eq, Real.dist_eq, Real.dist_eq] at hdist
    have hzδ : |z' - z| < δ₁ :=
      lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hdist' (min_le_left _ _))
    have hθδ₂ : θ' < δ₂ := by
      have h1 : |θ' - 0| < δ₂ :=
        lt_of_le_of_lt (le_max_right _ _)
          (lt_of_lt_of_le hdist' ((min_le_right _ _).trans (min_le_left _ _)))
      rwa [sub_zero, abs_of_nonneg hθ'.1] at h1
    have hθq : θ' < π / 4 := by
      have h1 : |θ' - 0| < π / 4 :=
        lt_of_le_of_lt (le_max_right _ _)
          (lt_of_lt_of_le hdist' ((min_le_right _ _).trans (min_le_right _ _)))
      rwa [sub_zero, abs_of_nonneg hθ'.1] at h1
    have hA0close : |A0 z' - A0 z| < ε / 2 := by
      have h := hδ₁ hz' hzδ
      rwa [Real.dist_eq] at h
    rcases eq_or_lt_of_le hθ'.1 with h00 | h00
    · subst h00
      rw [uncurry_glue_zero, Real.dist_eq]
      linarith
    · have hθ'mem : θ' ∈ Set.Ioo (0 : ℝ) (π / 2) := ⟨h00, by linarith [hθq, Real.pi_pos]⟩
      rw [uncurry_glue_of_mem_Ioo hθ'mem, Real.dist_eq]
      have h1 := hd0 z' hz' θ' hθ'mem
      have h2 := hδ₂ θ' hθ'.1 hθδ₂
      calc |f z' θ' - A0 z| ≤ |f z' θ' - A0 z'| + |A0 z' - A0 z| := by
            rw [show f z' θ' - A0 z = (f z' θ' - A0 z') + (A0 z' - A0 z) from by ring]
            exact abs_add_le _ _
        _ < ε := by linarith
  · rcases eq_or_lt_of_le hθ.2 with hp | hp
    · -- ## the angle `θ = π/2`
      subst hp
      rw [Metric.continuousWithinAt_iff]
      intro ε hε
      rw [uncurry_glue_pi]
      obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.tendsto_nhdsWithin_nhds.mp
        ((hA1.continuousWithinAt hz).tendsto) (ε / 2) (by linarith)
      have hsmall : ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 ≤ t → t < δ → D1 * t ^ β1 < ε / 2 := by
        by_cases hD : D1 ≤ 0
        · exact ⟨1, one_pos, fun t ht0 _ => by
            have h1 : D1 * t ^ β1 ≤ 0 :=
              mul_nonpos_of_nonpos_of_nonneg hD (Real.rpow_nonneg ht0 _)
            linarith⟩
        · have hDpos : 0 < D1 := not_le.mp hD
          have hbase : 0 < (ε / 4) / D1 := by positivity
          refine ⟨min 1 (((ε / 4) / D1) ^ (1 / β1)),
            lt_min one_pos (Real.rpow_pos_of_pos hbase _), fun t ht0 ht1 => ?_⟩
          have hle : t ≤ (((ε / 4) / D1) ^ (1 / β1)) := (lt_min_iff.mp ht1).2.le
          have hpow : t ^ β1 ≤ (ε / 4) / D1 := by
            calc t ^ β1 ≤ ((((ε / 4) / D1) ^ (1 / β1))) ^ β1 :=
                  Real.rpow_le_rpow ht0 hle hβ1.le
              _ = (ε / 4) / D1 := by
                  rw [← Real.rpow_mul hbase.le, one_div_mul_cancel hβ1.ne', Real.rpow_one]
          have h1 : D1 * t ^ β1 ≤ D1 * ((ε / 4) / D1) := mul_le_mul_of_nonneg_left hpow hDpos.le
          have h2 : D1 * ((ε / 4) / D1) = ε / 4 := by field_simp
          rw [h2] at h1
          linarith
      obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := hsmall
      refine ⟨min δ₁ (min δ₂ (π / 4)), lt_min hδ₁pos (lt_min hδ₂pos (by positivity)),
        fun y hy hdist => ?_⟩
      obtain ⟨z', θ'⟩ := y
      rw [Work.FTS_EllLimOK.mem_cbox] at hy
      obtain ⟨hz', hθ'⟩ := hy
      have hdist' : max |z' - z| |θ' - π / 2| < min δ₁ (min δ₂ (π / 4)) := by
        rwa [Prod.dist_eq, Real.dist_eq, Real.dist_eq] at hdist
      have hzδ : |z' - z| < δ₁ :=
        lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hdist' (min_le_left _ _))
      have hθδ₂ : θ' > π / 2 - δ₂ := by
        have h1 : |θ' - π / 2| < δ₂ :=
          lt_of_le_of_lt (le_max_right _ _)
            (lt_of_lt_of_le hdist' ((min_le_right _ _).trans (min_le_left _ _)))
        rw [abs_lt] at h1
        linarith [h1.1]
      have hθq : θ' > π / 4 := by
        have h1 : |θ' - π / 2| < π / 4 :=
          lt_of_le_of_lt (le_max_right _ _)
            (lt_of_lt_of_le hdist' ((min_le_right _ _).trans (min_le_right _ _)))
        rw [abs_lt] at h1
        linarith [h1.1]
      have hA1close : |A1 z' - A1 z| < ε / 2 := by
        have h := hδ₁ hz' hzδ
        rwa [Real.dist_eq] at h
      rcases eq_or_lt_of_le hθ'.2 with hpp | hpp
      · subst hpp
        rw [uncurry_glue_pi, Real.dist_eq]
        linarith
      · have hθ'mem : θ' ∈ Set.Ioo (0 : ℝ) (π / 2) :=
          ⟨by linarith [hθ'.1, hθq], hpp⟩
        rw [uncurry_glue_of_mem_Ioo hθ'mem, Real.dist_eq]
        have h1 := hd1 z' hz' θ' hθ'mem
        have h2 := hδ₂ (π / 2 - θ') (by linarith) (by linarith)
        have h3 : f z' θ' - A1 z = (f z' θ' - A1 z') + (A1 z' - A1 z) := by ring
        calc |f z' θ' - A1 z| ≤ |f z' θ' - A1 z'| + |A1 z' - A1 z| := by
              rw [h3]; exact abs_add_le _ _
          _ < ε := by linarith
    · -- ## an interior angle: `f` itself is smooth there
      have hθI : θ ∈ Set.Ioo (0 : ℝ) (π / 2) := ⟨h0, hp⟩
      have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
        Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz0, hθI.1, hθI.2⟩
      have hcd : ContDiffAt ℝ 0 (Function.uncurry f) (z, θ) :=
        (hsm.forall 0).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)
      have hev : (fun y : ℝ × ℝ => glue A0 A1 f y.1 y.2) =ᶠ[𝓝 (z, θ)] (Function.uncurry f) := by
        filter_upwards [((isOpen_univ).prod isOpen_Ioo).mem_nhds
          (show ((z, θ) : ℝ × ℝ) ∈ Set.univ ×ˢ Set.Ioo 0 (π / 2) from ⟨trivial, hθI⟩)]
          with y hy
        obtain ⟨-, hy2⟩ := hy
        exact uncurry_glue_of_mem_Ioo hy2
      exact (hcd.continuousAt.congr hev.symm).continuousWithinAt

/-- **`θ ^ β → 0` at `0⁺`, squeezed form, with the bound only on `(0,T)`.** -/
theorem tendsto_zero_of_abs_le_rpow_lt {f : ℝ → ℝ} {C β T : ℝ} (hβ : 0 < β) (hT : 0 < T)
    (h : ∀ θ : ℝ, 0 < θ → θ < T → |f θ| ≤ C * θ ^ β) :
    Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  by_cases hC : C ≤ 0
  · refine ⟨min 1 T, lt_min one_pos hT, fun θ hθ hδ => ?_⟩
    have hθT : θ < T := by
      have h1 : θ < min 1 T := by
        have := hδ; rw [Real.dist_eq, sub_zero, abs_of_pos hθ] at this; exact this
      exact lt_of_lt_of_le h1 (min_le_right _ _)
    have h1 : |f θ| ≤ 0 :=
      le_trans (h θ hθ hθT) (mul_nonpos_of_nonpos_of_nonneg hC (Real.rpow_nonneg hθ.le _))
    have h2 : f θ = 0 := abs_eq_zero.mp (le_antisymm h1 (abs_nonneg _))
    rw [h2, Real.dist_eq, sub_zero, abs_zero]
    exact hε
  · have hCpos : 0 < C := not_le.mp hC
    have hbase : 0 < (ε / 2) / C := by positivity
    refine ⟨min (min 1 T) (((ε / 2) / C) ^ (1 / β)),
      lt_min (lt_min one_pos hT) (Real.rpow_pos_of_pos hbase _), fun θ hθ hδ => ?_⟩
    have hlt : θ < min (min 1 T) (((ε / 2) / C) ^ (1 / β)) := by
      have := hδ; rw [Real.dist_eq, sub_zero, abs_of_pos hθ] at this; exact this
    have hθT : θ < T := (lt_min_iff.mp (lt_min_iff.mp hlt).1).2
    have hδ' : θ ≤ (((ε / 2) / C) ^ (1 / β)) := (lt_min_iff.mp hlt).2.le
    have hpow : θ ^ β ≤ (ε / 2) / C := by
      calc θ ^ β ≤ ((((ε / 2) / C) ^ (1 / β))) ^ β := Real.rpow_le_rpow hθ.le hδ' hβ.le
        _ = (ε / 2) / C := by
            rw [← Real.rpow_mul hbase.le, one_div_mul_cancel hβ.ne', Real.rpow_one]
    have h1 : |f θ| ≤ C * ((ε / 2) / C) :=
      le_trans (h θ hθ hθT) (mul_le_mul_of_nonneg_left hpow hCpos.le)
    have h2 : C * ((ε / 2) / C) = ε / 2 := by field_simp
    rw [Real.dist_eq, sub_zero]
    linarith [h1, h2]

theorem tendsto_zero_pi_sub_lt {f : ℝ → ℝ} {C β : ℝ} (hβ : 0 < β)
    (h : ∀ θ : ℝ, 0 < θ → θ < π / 2 → |f θ| ≤ C * (π / 2 - θ) ^ β) :
    Filter.Tendsto f (nhdsWithin (π / 2) (Set.Iio (π / 2))) (nhds 0) := by
  have hT : (0 : ℝ) < π / 2 := by positivity
  have hcomp : Filter.Tendsto (fun t : ℝ => f (π / 2 - t)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    refine tendsto_zero_of_abs_le_rpow_lt hβ (T := π / 2) hT (C := C) (fun t ht0 htT => ?_)
    have h1 : |f (π / 2 - t)| ≤ C * (π / 2 - (π / 2 - t)) ^ β :=
      h (π / 2 - t) (by linarith) (by linarith)
    have h2 : (π / 2 - (π / 2 - t)) = t := by ring
    simpa [h2] using h1
  have hshift : Filter.Tendsto (fun θ : ℝ => π / 2 - θ) (nhdsWithin (π / 2) (Set.Iio (π / 2)))
      (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h1 : Filter.Tendsto (fun θ : ℝ => π / 2 - θ) (nhdsWithin (π / 2) (Set.Iio (π / 2)))
          (nhds (π / 2 - π / 2)) :=
        (tendsto_const_nhds.sub tendsto_id).mono_left nhdsWithin_le_nhds
      simpa using h1
    · filter_upwards [Ioo_mem_nhdsLT hT] with θ hθ
      exact sub_pos.mpr hθ.2
  have h1 : Filter.Tendsto (fun θ : ℝ => f (π / 2 - (π / 2 - θ)))
      (nhdsWithin (π / 2) (Set.Iio (π / 2))) (nhds 0) := hcomp.comp hshift
  refine Filter.Tendsto.congr' (Filter.Eventually.of_forall ?_) h1
  intro θ
  congr 1
  ring

/-- **`θ ^ β ≤ max 1 (T ^ β) · θ ^ γ`** for `0 < γ ≤ β`, `1 ≤ T` and `θ ∈ [0,T]`. -/
theorem rpow_le_max_mul_rpow {β γ T θ : ℝ} (hγ : 0 < γ) (hγβ : γ ≤ β) (hT : 1 ≤ T)
    (hθ0 : 0 ≤ θ) (hθT : θ ≤ T) : θ ^ β ≤ max 1 (T ^ β) * θ ^ γ := by
  rcases eq_or_lt_of_le hθ0 with h | h
  · subst h
    rw [Real.zero_rpow hγ.ne', Real.zero_rpow (by linarith : β ≠ 0), mul_zero]
  rcases lt_or_ge θ 1 with h1 | h1
  · have h2 : θ ^ β ≤ θ ^ γ := Real.rpow_le_rpow_of_exponent_ge h (le_of_lt h1) hγβ
    exact h2.trans (le_mul_of_one_le_left (Real.rpow_nonneg hθ0 γ) (le_max_left _ _))
  · have h2 : θ ^ β ≤ T ^ β := Real.rpow_le_rpow hθ0 hθT (by linarith)
    have h3 : T ^ β ≤ max 1 (T ^ β) := le_max_right _ _
    have h4 : 1 ≤ θ ^ γ := Real.one_le_rpow h1 hγ.le
    have h5 : max 1 (T ^ β) ≤ max 1 (T ^ β) * θ ^ γ :=
      le_mul_of_one_le_right (le_trans zero_le_one (le_max_left _ _)) h4
    exact h2.trans (h3.trans h5)

theorem BBlockAlt {α Ce : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {E : Fn →ₗ[ℝ] Fn} (hE : Ctx α Ce E) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hdata : BoxData α Ce E a b) (g : Fn) (hg : Work.FTS.ClassC.ClassC α g)
    {C : ℝ} {L0 N0 L1 N1 : ℝ → ℝ}
    (hLim : LimitsAt (E g) (Work.FTS.StrongGlobal.Xn6 α g) C a b L0 N0 L1 N1) :
    ContinuousOn (Function.uncurry (Bf L0 L1 (E g))) (Work.FTS_EllLimOK.cbox a b) ∧
    ContinuousOn (Function.uncurry (Mf N0 N1 (E g))) (Work.FTS_EllLimOK.cbox a b) ∧
    ContinuousOn (Function.uncurry (B2f (E g))) (Work.FTS_EllLimOK.cbox a b) ∧
    (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2),
      HasDerivWithinAt (fun z' => Bf L0 L1 (E g) z' θ) (Mf N0 N1 (E g) z θ) (Set.Icc a b) z) ∧
    (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2),
      HasDerivWithinAt (fun θ' => Bf L0 L1 (E g) z θ') (B2f (E g) z θ) (Set.Icc 0 (π / 2)) θ) := by
  have hSm : Work.FTS.EllipticEst.SmoothOpen (E g) := (hE g hg).1.2.1
  obtain ⟨K, hK, β, hβ, hmodw, hrates, hlimw, hhol⟩ := hdata
  obtain ⟨CR, hCR, hRb⟩ := hrates
  obtain ⟨K2, hK2, β2, hβ2, hholw⟩ := hhol
  set X := Work.FTS.StrongGlobal.Xn6 α g with hXdef
  have hX0 : 0 ≤ X := by rw [hXdef]; exact Work.Spaces.HkNorm_nonneg α 6 g
  have hT : (0 : ℝ) < π / 2 := by positivity
  have hT1 : (1 : ℝ) ≤ π / 2 := by linarith [Real.pi_gt_three]
  have hLim' := hLim
  obtain ⟨hL0lim, hL0rate, hN0lim, hN0rate, hL1lim, hL1rate, hN1lim, hN1rate,
    hL0c, hN0c, hL1c, hN1c, hL0d, hL1d⟩ := hLim'
  -- Clairaut's theorem on the open strip
  have hcl : ∀ z θ, z ∈ Set.Icc a b → θ ∈ Set.Ioo 0 (π / 2) →
      Work.Spaces.pz (Work.Spaces.pth (E g)) z θ = Work.Spaces.pth (Work.Spaces.pz (E g)) z θ := by
    intro z θ hz hθ
    exact Work.Spaces.pz_pth_comm ((hSm.forall 2).contDiffAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds (Work.FTS.EllipticEst.mem_Q0.mpr
        ⟨lt_of_lt_of_le ha hz.1, hθ.1, hθ.2⟩)))
  -- the rate bounds
  have hr0 : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo 0 (π / 2),
      |Work.Spaces.pth (E g) z θ - L0 z| ≤ C * X * θ ^ (1 : ℝ) := by
    intro z hz θ hθ
    rw [Real.rpow_one]
    simpa only [hXdef] using hL0rate z hz θ hθ
  have hr1 : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo 0 (π / 2),
      |Work.Spaces.pth (E g) z θ - L1 z| ≤ C * X * (π / 2 - θ) ^ (1 : ℝ) := by
    intro z hz θ hθ
    rw [Real.rpow_one]
    simpa only [hXdef] using hL1rate z hz θ hθ
  have hrN0 : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo 0 (π / 2),
      |Work.Spaces.pth (Work.Spaces.pz (E g)) z θ - N0 z| ≤ C * X * θ ^ (1 : ℝ) := by
    intro z hz θ hθ
    rw [Real.rpow_one, ← hcl z θ hz hθ]
    simpa only [hXdef] using hN0rate z hz θ hθ
  have hrN1 : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo 0 (π / 2),
      |Work.Spaces.pth (Work.Spaces.pz (E g)) z θ - N1 z| ≤ C * X * (π / 2 - θ) ^ (1 : ℝ) := by
    intro z hz θ hθ
    rw [Real.rpow_one, ← hcl z θ hz hθ]
    simpa only [hXdef] using hN1rate z hz θ hθ
  have hmod2 : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo 0 (π / 2),
      |Work.Spaces.pth (Work.Spaces.pth (E g)) z θ| ≤ K * X * min θ (π / 2 - θ) ^ β := by
    intro z hz θ hθ
    simpa only [hXdef, Work.Spaces.pth] using hmodw g hg z hz θ hθ
  have hhol2 : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo 0 (π / 2), ∀ θ' ∈ Set.Ioo 0 (π / 2),
      |Work.Spaces.pth (Work.Spaces.pth (E g)) z θ
        - Work.Spaces.pth (Work.Spaces.pth (E g)) z θ'| ≤ K2 * X * |θ - θ'| ^ β2 := by
    intro z hz θ hθ θ' hθ'
    simpa only [hXdef, Work.Spaces.pth] using hholw g hg z hz θ hθ θ' hθ'
  have htr2 : ∀ z ∈ Set.Icc a b,
      Filter.Tendsto (fun θ => Work.Spaces.pth (Work.Spaces.pth (E g)) z θ)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    intro z hz
    refine tendsto_zero_of_abs_le_rpow_lt hβ (T := π / 4) (by positivity) (C := K * X)
      (fun t ht0 htT => ?_)
    have hmem : t ∈ Set.Ioo (0 : ℝ) (π / 2) := ⟨ht0, by linarith⟩
    have h2 : min t (π / 2 - t) ^ β ≤ t ^ β :=
      Real.rpow_le_rpow (le_of_lt (lt_min ht0 (by linarith))) (min_le_left _ _) hβ.le
    calc |Work.Spaces.pth (Work.Spaces.pth (E g)) z t|
        ≤ K * X * min t (π / 2 - t) ^ β := hmod2 z hz t hmem
      _ ≤ K * X * t ^ β := mul_le_mul_of_nonneg_left h2 (mul_nonneg hK.le hX0)
  have htr2p : ∀ z ∈ Set.Icc a b,
      Filter.Tendsto (fun θ => Work.Spaces.pth (Work.Spaces.pth (E g)) z θ)
        (nhdsWithin (π / 2) (Set.Iio (π / 2))) (nhds 0) := by
    intro z hz
    refine tendsto_zero_pi_sub_lt hβ (C := K * X) (fun t ht0 htT => ?_)
    have hmem : t ∈ Set.Ioo (0 : ℝ) (π / 2) := ⟨ht0, htT⟩
    have h2 : min t (π / 2 - t) ^ β ≤ (π / 2 - t) ^ β :=
      Real.rpow_le_rpow (le_of_lt (lt_min hmem.1 (by linarith))) (min_le_right _ _) hβ.le
    calc |Work.Spaces.pth (Work.Spaces.pth (E g)) z t|
        ≤ K * X * min t (π / 2 - t) ^ β := hmod2 z hz t hmem
      _ ≤ K * X * (π / 2 - t) ^ β := mul_le_mul_of_nonneg_left h2 (mul_nonneg hK.le hX0)
  -- ## the three continuity statements
  have hC1 : ContinuousOn (Function.uncurry (Bf L0 L1 (E g))) (Work.FTS_EllLimOK.cbox a b) :=
    continuousOn_glue (A0 := L0) (A1 := L1) (f := Work.Spaces.pth (E g)) (D0 := C * X)
      (D1 := C * X) (β0 := 1) (β1 := 1) ha one_pos one_pos hSm.pth hL0c hL1c hr0 hr1
  have hC2 : ContinuousOn (Function.uncurry (Mf N0 N1 (E g))) (Work.FTS_EllLimOK.cbox a b) :=
    continuousOn_glue (A0 := N0) (A1 := N1) (f := Work.Spaces.pth (Work.Spaces.pz (E g)))
      (D0 := C * X) (D1 := C * X) (β0 := 1) (β1 := 1) ha one_pos one_pos (hSm.pz).pth hN0c hN1c
      hrN0 hrN1
  have hC3 : ContinuousOn (Function.uncurry (B2f (E g))) (Work.FTS_EllLimOK.cbox a b) := by
    refine continuousOn_glue (A0 := fun _ => (0 : ℝ)) (A1 := fun _ => (0 : ℝ))
      (f := Work.Spaces.pth (Work.Spaces.pth (E g)))
      (D0 := K * X * max 1 (((π : ℝ) / 2) ^ β)) (D1 := K * X * max 1 (((π : ℝ) / 2) ^ β))
      (β0 := min β 1) (β1 := min β 1) ha (lt_min hβ one_pos) (lt_min hβ one_pos)
      (hSm.pth).pth continuousOn_const continuousOn_const ?_ ?_
    · intro z hz θ hθ
      have h2 : min θ (π / 2 - θ) ^ β ≤ θ ^ β :=
        Real.rpow_le_rpow (le_of_lt (lt_min hθ.1 (by linarith [hθ.2]))) (min_le_left _ _) hβ.le
      have h3 : θ ^ β ≤ max 1 (((π : ℝ) / 2) ^ β) * θ ^ (min β 1) :=
        rpow_le_max_mul_rpow (lt_min hβ one_pos) (min_le_left β 1) hT1 hθ.1.le hθ.2.le
      have h4 : |Work.Spaces.pth (Work.Spaces.pth (E g)) z θ|
          ≤ (K * X * max 1 (((π : ℝ) / 2) ^ β)) * θ ^ (min β 1) := by
        calc |Work.Spaces.pth (Work.Spaces.pth (E g)) z θ|
            ≤ K * X * min θ (π / 2 - θ) ^ β := hmod2 z hz θ hθ
          _ ≤ K * X * θ ^ β := mul_le_mul_of_nonneg_left h2 (mul_nonneg hK.le hX0)
          _ ≤ K * X * (max 1 (((π : ℝ) / 2) ^ β) * θ ^ (min β 1)) :=
              mul_le_mul_of_nonneg_left h3 (mul_nonneg hK.le hX0)
          _ = (K * X * max 1 (((π : ℝ) / 2) ^ β)) * θ ^ (min β 1) := by ring
      simpa using h4
    · intro z hz θ hθ
      have hθ' : (0 : ℝ) ≤ π / 2 - θ := by linarith [hθ.2]
      have h2 : min θ (π / 2 - θ) ^ β ≤ (π / 2 - θ) ^ β :=
        Real.rpow_le_rpow (le_of_lt (lt_min hθ.1 (by linarith [hθ.2]))) (min_le_right _ _) hβ.le
      have h3 : (π / 2 - θ) ^ β ≤ max 1 (((π : ℝ) / 2) ^ β) * (π / 2 - θ) ^ (min β 1) :=
        rpow_le_max_mul_rpow (lt_min hβ one_pos) (min_le_left β 1) hT1 hθ'
          (by linarith [hθ.1])
      have h4 : |Work.Spaces.pth (Work.Spaces.pth (E g)) z θ|
          ≤ (K * X * max 1 (((π : ℝ) / 2) ^ β)) * (π / 2 - θ) ^ (min β 1) := by
        calc |Work.Spaces.pth (Work.Spaces.pth (E g)) z θ|
            ≤ K * X * min θ (π / 2 - θ) ^ β := hmod2 z hz θ hθ
          _ ≤ K * X * (π / 2 - θ) ^ β := mul_le_mul_of_nonneg_left h2 (mul_nonneg hK.le hX0)
          _ ≤ K * X * (max 1 (((π : ℝ) / 2) ^ β) * (π / 2 - θ) ^ (min β 1)) :=
              mul_le_mul_of_nonneg_left h3 (mul_nonneg hK.le hX0)
          _ = (K * X * max 1 (((π : ℝ) / 2) ^ β)) * (π / 2 - θ) ^ (min β 1) := by ring
      simpa using h4
  refine ⟨hC1, hC2, hC3, ?_, ?_⟩
  · -- ## the radial within-derivative `∂_z Bf = Mf`
    intro z hz θ hθ
    have hz0 : 0 < z := lt_of_lt_of_le ha hz.1
    rcases eq_or_lt_of_le hθ.1 with h | h
    · subst h
      have hfun : (fun z' => Bf L0 L1 (E g) z' 0) = L0 :=
        funext (fun z' => Bf_zero L0 L1 (E g) z')
      rw [hfun, Mf_zero]
      exact hL0d z hz
    · rcases eq_or_lt_of_le hθ.2 with hp | hp
      · subst hp
        have hfun : (fun z' => Bf L0 L1 (E g) z' (π / 2)) = L1 :=
          funext (fun z' => Bf_pi L0 L1 (E g) z')
        rw [hfun, Mf_pi]
        exact hL1d z hz
      · have hmem : θ ∈ Set.Ioo 0 (π / 2) := ⟨h, hp⟩
        have hfun : (fun z' => Bf L0 L1 (E g) z' θ) = fun z' => Work.Spaces.pth (E g) z' θ :=
          funext (fun z' => Bf_of_mem_Ioo hmem)
        rw [hfun, Mf_of_mem_Ioo hmem, ← hcl z θ hz hmem]
        exact ((hSm.pth).hasDerivAt_slice hmem hz0).hasDerivWithinAt
  · -- ## the angular within-derivative `∂_θ Bf = B2f`
    intro z hz θ hθ
    have hz0 : 0 < z := lt_of_lt_of_le ha hz.1
    have hcont : ContinuousOn (fun θ' => Bf L0 L1 (E g) z θ') (Set.Icc 0 (π / 2)) := by
      refine continuousOn_thetaSlice_of_interior hT ?_ ?_ ?_
      · intro θ' hθ'
        have hev : (fun t => Bf L0 L1 (E g) z t) =ᶠ[𝓝 θ'] (fun t => Work.Spaces.pth (E g) z t) := by
          filter_upwards [isOpen_Ioo.mem_nhds hθ'] with t ht
          exact Bf_of_mem_Ioo ht
        have hct : ContinuousAt (fun t => Work.Spaces.pth (E g) z t) θ' :=
          (((hSm.pth).curry_θ hz0).contDiffAt (isOpen_Ioo.mem_nhds hθ')).continuousAt
        exact hct.congr hev.symm
      · rw [Bf_zero]
        have hev : (fun t => Work.Spaces.pth (E g) z t) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
            (fun t => Bf L0 L1 (E g) z t) := by
          filter_upwards [Ioo_mem_nhdsGT hT] with t ht
          exact (Bf_of_mem_Ioo ht).symm
        exact (hL0lim z hz).congr' hev
      · rw [Bf_pi]
        have hev : (fun t => Work.Spaces.pth (E g) z t) =ᶠ[nhdsWithin (π / 2) (Set.Iio (π / 2))]
            (fun t => Bf L0 L1 (E g) z t) := by
          filter_upwards [Ioo_mem_nhdsLT hT] with t ht
          exact (Bf_of_mem_Ioo ht).symm
        exact (hL1lim z hz).congr' hev
    have hderiv : ∀ x ∈ Set.Ioo 0 (π / 2),
        HasDerivAt (fun t => Bf L0 L1 (E g) z t)
          (Work.Spaces.pth (Work.Spaces.pth (E g)) z x) x := by
      intro x hx
      have hev : (fun t => Bf L0 L1 (E g) z t) =ᶠ[𝓝 x] (fun t => Work.Spaces.pth (E g) z t) := by
        filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
        exact Bf_of_mem_Ioo ht
      have hd : HasDerivAt (fun t => Work.Spaces.pth (E g) z t)
          (Work.Spaces.pth (Work.Spaces.pth (E g)) z x) x :=
        ((((hSm.pth).curry_θ hz0).contDiffAt (isOpen_Ioo.mem_nhds hx)).differentiableAt
          (by norm_num)).hasDerivAt
      exact (Filter.EventuallyEq.hasDerivAt_iff hev).mpr hd
    rcases eq_or_lt_of_le hθ.1 with h | h
    · subst h
      rw [B2f_zero]
      exact hasDerivWithinAt_Icc_left (T := π / 2) hT hcont hderiv (htr2 z hz)
    · rcases eq_or_lt_of_le hθ.2 with hp | hp
      · subst hp
        rw [B2f_pi]
        exact hasDerivWithinAt_Icc_right (T := π / 2) hT hcont hderiv (htr2p z hz)
      · rw [B2f_of_mem_Ioo ⟨h, hp⟩]
        exact (hderiv θ ⟨h, hp⟩).hasDerivWithinAt

end Work.FTS_EllLimOK.ProducerH.H2
