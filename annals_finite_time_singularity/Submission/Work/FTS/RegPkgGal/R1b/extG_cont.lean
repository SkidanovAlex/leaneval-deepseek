import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.RegPkgGal.R1
import Submission.Work.FTS.RegPkgGal.Defs
import Submission.Work.FTS.RegPkgGal.R1b.General
import Submission.Work.FTS.RegPkgGal.R1b.Locals
import Submission.Work.FTS.RegPkgGal.R1b.C1Facts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.RegPkgGal.R1b.extG_cont`

The joint `C¹`-gluing of the extension `g̃ = extG g` across `z = 0` and across `τ = 0`,
under *uniform* (joint in `(z,τ)`) hypotheses on `g` near `z = 0`.

The hypotheses ask for the limits as `(z,τ) → (0,τ₀)` **within `z > 0`**, i.e. they are uniform
in `τ`; that uniformity is exactly what makes the corner `(z,τ) = (0,0)` of the piecewise
definition tame.  (The earlier `R1` version of the statement, with only ray-wise limits, is
false — see `Submission/Work/FTS/RegPkgGal/R1/NOTES_extG_cont_FALSE.md`.)

## Proof outline

For fixed `θ` let `baseFn g θ (z,τ) = g z θ τ`, `tauDer g θ z = deriv (fun s => g z θ s) 0`
and `jetFn g θ (z,τ) = g z θ 0 + τ * tauDer g θ z` (the `τ < 0` branch of `extG`).  Then
`extG g z θ τ` is `0` for `z ≤ 0`, `jetFn` for `z > 0, τ < 0` and `baseFn` for `z > 0, τ ≥ 0`.
Both branches are `C¹` on `z > 0`, and the candidate derivative `extDeriv g θ` is the nested
piecewise combination of their partial derivatives.  The two joins are:

* `τ = 0`, `z > 0`: `jetFn` and `baseFn` have the *same* Fréchet derivative there, since at
  `τ = 0` the jet is the first-order Taylor expansion of `baseFn` in `τ`
  (`fderiv_jetFn_eq_fderiv_baseFn`, `jetBranch_eq_baseBranch_at_zero`);
* `z = 0`: the joint limits `g = o(z)`, `∂_zg → 0`, `∂_τg → 0`, `∂_τg(·,0) = o(z)` and
  `∂_z(∂_τg(·,0)) → 0` identify the derivative as `0` there, and give the continuity of
  `extDeriv` at `(0,τ₀)`.

The gluing itself is `hasFDerivAt_of_union`, and everything is assembled with
`contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn`.

## Layout

The supporting material lives in the sibling modules of this directory:
`General` (elementary analysis helpers), `Locals` (the local objects and their basic
rewriting lemmas) and `C1Facts` (smoothness of the two branches, their Fréchet derivatives,
the `τ = 0` join and the continuity of the branch functions).
-/

namespace Work.FTS.RegPkgGal.R1b

open Set Filter Topology MeasureTheory
open scoped Topology Real ContDiff

set_option autoImplicit false

theorem extG_cont {S : ℝ} (hS : 0 < S) {g : ℝ → ℝ → ℝ → ℝ}
    (hbase : ∀ θ ∈ Work.Spaces.Iθ, ContDiffOn ℝ 1 (fun q : ℝ × ℝ => g q.1 θ q.2)
      (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1))))
    (hj0 : ∀ θ ∈ Work.Spaces.Iθ, ∀ τ₀ ∈ Set.Ioo (-1) (S + 1),
      Filter.Tendsto (fun p : ℝ × ℝ => g p.1 θ p.2)
        (nhdsWithin (0, τ₀) (Set.prod (Set.Ioi (0:ℝ)) (Set.univ))) (nhds 0))
    (hjz : ∀ θ ∈ Work.Spaces.Iθ, ∀ τ₀ ∈ Set.Ioo (-1) (S + 1),
      Filter.Tendsto (fun p : ℝ × ℝ => p.1⁻¹ * g p.1 θ p.2)
        (nhdsWithin (0, τ₀) (Set.prod (Set.Ioi (0:ℝ)) (Set.univ))) (nhds 0))
    (hjdz : ∀ θ ∈ Work.Spaces.Iθ, ∀ τ₀ ∈ Set.Ioo (-1) (S + 1),
      Filter.Tendsto (fun p : ℝ × ℝ => deriv (fun z => g z θ p.2) p.1)
        (nhdsWithin (0, τ₀) (Set.prod (Set.Ioi (0:ℝ)) (Set.univ))) (nhds 0))
    (hjdt : ∀ θ ∈ Work.Spaces.Iθ, ∀ τ₀ ∈ Set.Ioo (-1) (S + 1),
      Filter.Tendsto (fun p : ℝ × ℝ => deriv (fun s => g p.1 θ s) p.2)
        (nhdsWithin (0, τ₀) (Set.prod (Set.Ioi (0:ℝ)) (Set.univ))) (nhds 0))
    (hd1 : ∀ θ ∈ Work.Spaces.Iθ, ContDiffOn ℝ 1 (fun q : ℝ × ℝ => deriv (fun s => g q.1 θ s) 0)
      (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1))))
    (hd1z : ∀ θ ∈ Work.Spaces.Iθ,
      Filter.Tendsto (fun p : ℝ × ℝ => deriv (fun z => deriv (fun s => g z θ s) 0) p.1)
        (nhdsWithin (0, 0) (Set.prod (Set.Ioi (0:ℝ)) (Set.univ))) (nhds 0))
    (hd1z2 : ∀ θ ∈ Work.Spaces.Iθ,
      Filter.Tendsto (fun p : ℝ × ℝ => p.1⁻¹ * deriv (fun s => g p.1 θ s) 0)
        (nhdsWithin (0, 0) (Set.prod (Set.Ioi (0:ℝ)) (Set.univ))) (nhds 0))
    (ht0 : ∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 < z →
      Filter.Tendsto (fun τ => deriv (fun s => g z θ s) τ)
        (nhdsWithin 0 (Set.Ioi (0:ℝ))) (nhds (deriv (fun s => g z θ s) 0))) :
    ∀ θ ∈ Work.Spaces.Iθ, ContDiffOn ℝ 1 (fun q : ℝ × ℝ => Work.FTS.RegPkgGal.extG g q.1 θ q.2)
      (Set.prod (Set.Ioi (-1)) (Set.Ioo (-1) (S + 1))) := by
  intro θ hθ
  change ContDiffOn ℝ 1 (extFun g θ) (Ioi (-1:ℝ) ×ˢ Ioo (-1:ℝ) (S + 1))
  have hUopen : IsOpen (Ioi (-1:ℝ) ×ˢ Ioo (-1:ℝ) (S + 1)) := isOpen_Ioi.prod isOpen_Ioo
  have hVopen : IsOpen (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)) := isOpen_Ioi.prod isOpen_Ioi
  have hbaseV : ContDiffOn ℝ 1 (baseFn g θ) (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)) := hbase θ hθ
  have hddV : ContDiffOn ℝ 1 (tauDerFn g θ) (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)) := hd1 θ hθ
  have hjetV : ContDiffOn ℝ 1 (jetFn g θ) (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)) :=
    jetFn_contDiffOn hbaseV hddV
  have hτV : ContDiffOn ℝ 1 (tauDer g θ) (Ioi (0:ℝ)) := tauDer_contDiffOn hddV
  have hbaseAt : ∀ x ∈ (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)),
      HasFDerivAt (baseFn g θ) (fderiv ℝ (baseFn g θ) x) x :=
    fun x hx => hasFDerivAt_of_contDiffOn_one hVopen hbaseV hx
  have hjetAt : ∀ x ∈ (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)),
      HasFDerivAt (jetFn g θ) (fderiv ℝ (jetFn g θ) x) x :=
    fun x hx => hasFDerivAt_of_contDiffOn_one hVopen hjetV hx
  have hbasediff : ∀ x ∈ (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)), DifferentiableAt ℝ (baseFn g θ) x :=
    fun x hx => (hbaseAt x hx).differentiableAt
  have hjetdiff : ∀ x ∈ (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)), DifferentiableAt ℝ (jetFn g θ) x :=
    fun x hx => (hjetAt x hx).differentiableAt
  have hτdiff : ∀ z ∈ Ioi (0:ℝ), DifferentiableAt ℝ (tauDer g θ) z :=
    fun z hz => (hτV.differentiableOn one_ne_zero z hz).differentiableAt (isOpen_Ioi.mem_nhds hz)
  have hz0diff : ∀ z ∈ Ioi (0:ℝ), DifferentiableAt ℝ (fun z' => g z' θ 0) z := by
    intro z hz
    have hzc : DifferentiableAt ℝ (fun z' : ℝ => (z', (0:ℝ))) z := by fun_prop
    have hbd : DifferentiableAt ℝ (baseFn g θ) (z, (0:ℝ)) := hbasediff (z, 0) ⟨hz, by norm_num⟩
    have hcomp := hbd.comp z hzc
    simpa [Function.comp_def, baseFn] using hcomp
  have hAcont : ContinuousOn (jetBranch g θ) (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)) :=
    continuousOn_jetBranch hjetV
  have hBcont : ContinuousOn (baseBranch g θ) (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)) :=
    continuousOn_baseBranch hbaseV
  have h0mem : (0:ℝ) ∈ Ioo (-1:ℝ) (S + 1) := ⟨by norm_num, by linarith⟩
  -- ## Step 1: differentiability with derivative `extDeriv`
  have hderiv : ∀ x ∈ (Ioi (-1:ℝ) ×ˢ Ioo (-1:ℝ) (S + 1)),
      HasFDerivAt (extFun g θ) (extDeriv g θ x) x := by
    rintro ⟨z, τ⟩ hxU
    have hτU : τ ∈ Ioo (-1:ℝ) (S + 1) := hxU.2
    rcases lt_trichotomy z 0 with hz | hz | hz
    · -- `z < 0`: the extension vanishes identically nearby
      have hxd : extDeriv g θ (z, τ) = 0 := extDeriv_of_nonpos g θ (le_of_lt hz) τ
      rw [hxd]
      refine (hasFDerivAt_const (c := (0:ℝ)) (x := ((z, τ) : ℝ × ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_Iio.preimage continuous_fst).mem_nhds hz] with y hy
      exact extFun_of_nonpos g θ (le_of_lt hy)
    · -- `z = 0`: the corner; everything is `o(z)`
      subst hz
      have hxd : extDeriv g θ ((0:ℝ), τ) = 0 := extDeriv_of_nonpos g θ le_rfl τ
      rw [hxd]
      refine (hasFDerivAt_iff_isLittleO).2 ?_
      have hsub : (fun y : ℝ × ℝ =>
            extFun g θ y - extFun g θ ((0:ℝ), τ)
              - (0 : (ℝ × ℝ) →L[ℝ] ℝ) (y - ((0:ℝ), τ)))
          = fun y : ℝ × ℝ => extFun g θ y := by
        funext y
        rw [extFun_of_nonpos g θ le_rfl]
        simp
      rw [hsub]
      refine Asymptotics.isLittleO_iff.2 fun c hc => ?_
      set η : ℝ := c / (2 * (|τ| + 2)) with hηdef
      have hηpos : 0 < η := by rw [hηdef]; positivity
      have hηK : η * (|τ| + 2) = c / 2 := by rw [hηdef]; field_simp
      have hηc : η ≤ c := by
        rw [hηdef]
        have h2 : (1:ℝ) ≤ 2 * (|τ| + 2) := by nlinarith [abs_nonneg τ]
        calc c / (2 * (|τ| + 2)) ≤ c / 1 := div_le_div_of_nonneg_left (le_of_lt hc) one_pos h2
          _ = c := by ring
      obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := slice_bound_of_tendsto hηpos (hjz θ hθ 0 h0mem)
      obtain ⟨δ₃, hδ₃pos, hδ₃⟩ := slice_bound_of_tendsto hηpos (hd1z2 θ hθ)
      have hev₂ : ∀ᶠ y : ℝ × ℝ in 𝓝 ((0:ℝ), τ),
          0 < y.1 → |y.1⁻¹ * g y.1 θ 0| < η := by
        filter_upwards [eventually_box τ δ₂ hδ₂pos] with y hy hy1
        exact hδ₂ y.1 hy1 (hy hy1).1
      have hev₃ : ∀ᶠ y : ℝ × ℝ in 𝓝 ((0:ℝ), τ),
          0 < y.1 → |y.1⁻¹ * tauDer g θ y.1| < η := by
        filter_upwards [eventually_box τ δ₃ hδ₃pos] with y hy hy1
        exact hδ₃ y.1 hy1 (hy hy1).1
      have hev₁ : ∀ᶠ y : ℝ × ℝ in 𝓝 ((0:ℝ), τ), 0 < y.1 → y.1 < 1 := by
        filter_upwards [eventually_box τ 1 one_pos] with y hy hy1
        exact (hy hy1).1
      have hevτ : ∀ᶠ y : ℝ × ℝ in 𝓝 ((0:ℝ), τ), 0 < y.1 → |y.2 - τ| < 1 := by
        filter_upwards [eventually_box τ 1 one_pos] with y hy hy1
        exact (hy hy1).2
      filter_upwards [eventually_of_tendsto_box hηpos (hjz θ hθ τ hτU), hev₂, hev₃, hev₁, hevτ]
        with y hyA hy₂ hy₃ hy₁ hyτ
      rw [Real.norm_eq_abs]
      by_cases hy1 : 0 < y.1
      · have hgr : |g y.1 θ y.2| < η * y.1 := abs_lt_mul_of_abs_inv_mul_lt hy1 (hyA hy1)
        have hg0 : |g y.1 θ 0| < η * y.1 := abs_lt_mul_of_abs_inv_mul_lt hy1 (hy₂ hy1)
        have hdd : |tauDer g θ y.1| < η * y.1 := abs_lt_mul_of_abs_inv_mul_lt hy1 (hy₃ hy1)
        have hyt : |y.2| ≤ |τ| + 1 := by
          have habs : |y.2 - τ| < 1 := hyτ hy1
          calc |y.2| = |(y.2 - τ) + τ| := by ring_nf
            _ ≤ |y.2 - τ| + |τ| := abs_add_le _ _
            _ ≤ |τ| + 1 := by linarith [habs]
        have hnorm : y.1 ≤ ‖y - ((0:ℝ), τ)‖ := by
          have hle : y.1 ≤ max |y.1| |y.2 - τ| := by
            rw [abs_of_pos hy1]; exact le_max_left _ _
          calc y.1 ≤ max |y.1| |y.2 - τ| := hle
            _ = ‖y - ((0:ℝ), τ)‖ := by
                rw [Prod.norm_def]
                simp [Real.norm_eq_abs]
        rcases lt_or_ge y.2 0 with hy2 | hy2
        · -- jet branch
          have he : extFun g θ y = jetFn g θ y := by
            obtain ⟨y1, y2⟩ := y
            exact extFun_of_pos_of_neg g θ hy1 hy2
          rw [he, jetFn_apply]
          have hb : |g y.1 θ 0 + y.2 * tauDer g θ y.1| ≤ η * y.1 * (|τ| + 2) := by
            have h1 : |y.2 * tauDer g θ y.1| = |y.2| * |tauDer g θ y.1| := abs_mul _ _
            have h2 : |y.2| * |tauDer g θ y.1| ≤ (|τ| + 1) * (η * y.1) :=
              mul_le_mul hyt (le_of_lt hdd) (abs_nonneg _) (by positivity)
            have h3 : |g y.1 θ 0 + y.2 * tauDer g θ y.1|
                ≤ |g y.1 θ 0| + |y.2| * |tauDer g θ y.1| := by
              calc |g y.1 θ 0 + y.2 * tauDer g θ y.1|
                  ≤ |g y.1 θ 0| + |y.2 * tauDer g θ y.1| := abs_add_le _ _
                _ = |g y.1 θ 0| + |y.2| * |tauDer g θ y.1| := by rw [h1]
            have h4 : |g y.1 θ 0| + |y.2| * |tauDer g θ y.1|
                ≤ η * y.1 + (|τ| + 1) * (η * y.1) := add_le_add (le_of_lt hg0) h2
            calc |g y.1 θ 0 + y.2 * tauDer g θ y.1|
                ≤ η * y.1 + (|τ| + 1) * (η * y.1) := le_trans h3 h4
              _ = η * y.1 * (|τ| + 2) := by ring
          calc |g y.1 θ 0 + y.2 * tauDer g θ y.1| ≤ η * y.1 * (|τ| + 2) := hb
            _ = (c / 2) * y.1 := by rw [← hηK]; ring
            _ ≤ (c / 2) * ‖y - ((0:ℝ), τ)‖ := mul_le_mul_of_nonneg_left hnorm (by positivity)
            _ ≤ c * ‖y - ((0:ℝ), τ)‖ :=
                mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
        · -- family branch
          have he : extFun g θ y = baseFn g θ y := by
            obtain ⟨y1, y2⟩ := y
            exact extFun_of_pos_of_nonneg g θ hy1 hy2
          rw [he, baseFn_apply]
          calc |g y.1 θ y.2| ≤ η * y.1 := le_of_lt hgr
            _ ≤ η * ‖y - ((0:ℝ), τ)‖ := mul_le_mul_of_nonneg_left hnorm (le_of_lt hηpos)
            _ ≤ c * ‖y - ((0:ℝ), τ)‖ := mul_le_mul_of_nonneg_right hηc (norm_nonneg _)
      · -- `y.1 ≤ 0`: the extension vanishes
        obtain ⟨y1, y2⟩ := y
        rw [extFun_of_nonpos g θ (le_of_not_gt hy1)]
        simp only [abs_zero]
        exact mul_nonneg (le_of_lt hc) (by positivity)
    · -- `z > 0`
      have hxV : (z, τ) ∈ Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ) := ⟨hz, hτU.1⟩
      by_cases hτn : τ < 0
      · -- the jet branch
        have hxd : extDeriv g θ (z, τ) = fderiv ℝ (jetFn g θ) (z, τ) :=
          extDeriv_eq_fderiv_jetFn g θ hz hτn (hjetdiff (z, τ) hxV)
        rw [hxd]
        refine (hjetAt (z, τ) hxV).congr_of_eventuallyEq ?_
        filter_upwards [(isOpen_Ioi.preimage continuous_fst).mem_nhds hz,
          (isOpen_Iio.preimage continuous_snd).mem_nhds hτn] with y hy1 hy2
        exact extFun_of_pos_of_neg g θ hy1 hy2
      · rcases lt_or_eq_of_le (le_of_not_gt hτn) with hτp | hτ0
        · -- the family branch
          have hxd : extDeriv g θ (z, τ) = fderiv ℝ (baseFn g θ) (z, τ) :=
            extDeriv_eq_fderiv_baseFn g θ hz (le_of_lt hτp) (hbasediff (z, τ) hxV)
          rw [hxd]
          refine (hbaseAt (z, τ) hxV).congr_of_eventuallyEq ?_
          filter_upwards [(isOpen_Ioi.preimage continuous_fst).mem_nhds hz,
            (isOpen_Ioi.preimage continuous_snd).mem_nhds hτp] with y hy1 hy2
          exact extFun_of_pos_of_nonneg g θ hy1 (le_of_lt hy2)
        · -- the `τ = 0` join
          subst hτ0
          exact hasFDerivAt_extFun_join hz hbaseV hjetV
  -- ## Step 2: continuity of the candidate derivative
  have hcont : ContinuousOn (extDeriv g θ) (Ioi (-1:ℝ) ×ˢ Ioo (-1:ℝ) (S + 1)) := by
    rintro ⟨z, τ⟩ hxU
    have hτU : τ ∈ Ioo (-1:ℝ) (S + 1) := hxU.2
    rcases lt_trichotomy z 0 with hz | hz | hz
    · -- `z < 0`
      have hev : extDeriv g θ =ᶠ[𝓝 ((z, τ) : ℝ × ℝ)] (fun _ => (0 : (ℝ × ℝ) →L[ℝ] ℝ)) := by
        filter_upwards [(isOpen_Iio.preimage continuous_fst).mem_nhds hz] with y hy
        exact extDeriv_of_nonpos g θ (le_of_lt hy) y.2
      exact (continuousAt_const.congr_of_eventuallyEq hev).continuousWithinAt
    · -- `z = 0`
      subst hz
      have hxd : extDeriv g θ ((0:ℝ), τ) = 0 := extDeriv_of_nonpos g θ le_rfl τ
      refine ContinuousAt.continuousWithinAt ?_
      rw [ContinuousAt, hxd, Metric.tendsto_nhds]
      simp_rw [dist_zero_right]
      intro ε hε
      set η : ℝ := ε / (2 * (|τ| + 3)) with hηdef
      have hηpos : 0 < η := by rw [hηdef]; positivity
      have hηK : η * (|τ| + 3) = ε / 2 := by rw [hηdef]; field_simp
      have hηε : η ≤ ε := by
        rw [hηdef]
        have h2 : (1:ℝ) ≤ 2 * (|τ| + 3) := by nlinarith [abs_nonneg τ]
        calc ε / (2 * (|τ| + 3)) ≤ ε / 1 := div_le_div_of_nonneg_left (le_of_lt hε) one_pos h2
          _ = ε := by ring
      have hslice₀ : ∀ᶠ y : ℝ × ℝ in 𝓝 ((0:ℝ), τ),
          0 < y.1 → |deriv (fun z => g z θ 0) y.1| < η := by
        obtain ⟨δ, hδ, H⟩ := slice_bound_of_tendsto hηpos (hjdz θ hθ 0 h0mem)
        filter_upwards [eventually_box τ δ hδ] with y hy hy1
        exact H y.1 hy1 (hy hy1).1
      have hslice₁ : ∀ᶠ y : ℝ × ℝ in 𝓝 ((0:ℝ), τ),
          0 < y.1 → |deriv (fun z => deriv (fun s => g z θ s) 0) y.1| < η := by
        obtain ⟨δ, hδ, H⟩ := slice_bound_of_tendsto hηpos (hd1z θ hθ)
        filter_upwards [eventually_box τ δ hδ] with y hy hy1
        exact H y.1 hy1 (hy hy1).1
      have hslice₂ : ∀ᶠ y : ℝ × ℝ in 𝓝 ((0:ℝ), τ),
          0 < y.1 → |tauDer g θ y.1| < η * y.1 := by
        obtain ⟨δ, hδ, H⟩ := slice_bound_of_tendsto hηpos (hd1z2 θ hθ)
        filter_upwards [eventually_box τ δ hδ] with y hy hy1
        exact abs_lt_mul_of_abs_inv_mul_lt hy1 (H y.1 hy1 (hy hy1).1)
      have hslice₃ : ∀ᶠ y : ℝ × ℝ in 𝓝 ((0:ℝ), τ), 0 < y.1 → y.1 < 1 := by
        filter_upwards [eventually_box τ 1 one_pos] with y hy hy1
        exact (hy hy1).1
      have hslice₄ : ∀ᶠ y : ℝ × ℝ in 𝓝 ((0:ℝ), τ), 0 < y.1 → |y.2 - τ| < 1 := by
        filter_upwards [eventually_box τ 1 one_pos] with y hy hy1
        exact (hy hy1).2
      filter_upwards [eventually_of_tendsto_box hηpos (hjdz θ hθ τ hτU),
        eventually_of_tendsto_box hηpos (hjdt θ hθ τ hτU),
        hslice₀, hslice₁, hslice₂, hslice₃, hslice₄]
        with y hdz hdt h₀ h₁ h₂ h₃ h₄
      by_cases hy1 : 0 < y.1
      · rcases lt_or_ge y.2 0 with hy2 | hy2
        · -- jet branch
          have hye : extDeriv g θ y = jetBranch g θ y := by
            obtain ⟨y1, y2⟩ := y
            exact extDeriv_of_pos_of_neg' g θ hy1 hy2
          rw [hye]
          have hsplit : ‖jetBranch g θ y‖
              ≤ |deriv (fun z' => jetFn g θ (z', y.2)) y.1|
                + |deriv (fun t => jetFn g θ (y.1, t)) y.2| := by
            simp only [jetBranch]
            exact norm_smul_fst_add_smul_snd_le _ _
          have hzf : deriv (fun z' => jetFn g θ (z', y.2)) y.1
              = deriv (fun z' => g z' θ 0) y.1
                + y.2 * deriv (fun z' => deriv (fun s => g z' θ s) 0) y.1 :=
            deriv_jetFn_fst g θ (hz0diff y.1 hy1) (hτdiff y.1 hy1)
          have htf : deriv (fun t => jetFn g θ (y.1, t)) y.2 = tauDer g θ y.1 :=
            deriv_jetFn_snd g θ y.1 y.2
          rw [hzf, htf] at hsplit
          have hyt : |y.2| ≤ |τ| + 1 := by
            have habs : |y.2 - τ| < 1 := h₄ hy1
            calc |y.2| = |(y.2 - τ) + τ| := by ring_nf
              _ ≤ |y.2 - τ| + |τ| := abs_add_le _ _
              _ ≤ |τ| + 1 := by linarith [habs]
          have hb : |deriv (fun z' => g z' θ 0) y.1
                + y.2 * deriv (fun z' => deriv (fun s => g z' θ s) 0) y.1|
              + |tauDer g θ y.1| < ε := by
            have hI : |deriv (fun z' => g z' θ 0) y.1
                + y.2 * deriv (fun z' => deriv (fun s => g z' θ s) 0) y.1|
                ≤ η + (|τ| + 1) * η := by
              calc |deriv (fun z' => g z' θ 0) y.1
                    + y.2 * deriv (fun z' => deriv (fun s => g z' θ s) 0) y.1|
                  ≤ |deriv (fun z' => g z' θ 0) y.1|
                    + |y.2 * deriv (fun z' => deriv (fun s => g z' θ s) 0) y.1| := abs_add_le _ _
                _ = |deriv (fun z' => g z' θ 0) y.1|
                    + |y.2| * |deriv (fun z' => deriv (fun s => g z' θ s) 0) y.1| := by
                      rw [abs_mul]
                _ ≤ η + (|τ| + 1) * η :=
                      add_le_add (le_of_lt (h₀ hy1))
                        (mul_le_mul hyt (le_of_lt (h₁ hy1)) (abs_nonneg _) (by positivity))
            have hII : |tauDer g θ y.1| ≤ η :=
              le_of_lt (lt_of_lt_of_le (h₂ hy1) (by nlinarith [h₃ hy1]))
            have hIII : η + (|τ| + 1) * η + η ≤ ε := by
              have heq : η + (|τ| + 1) * η + η = η * (|τ| + 3) := by ring
              rw [heq, hηK]
              linarith
            linarith [hI, hII, hIII]
          exact lt_of_le_of_lt hsplit hb
        · -- family branch
          have hye : extDeriv g θ y = baseBranch g θ y := by
            obtain ⟨y1, y2⟩ := y
            exact extDeriv_of_pos_of_nonneg' g θ hy1 hy2
          rw [hye]
          have hsplit : ‖baseBranch g θ y‖
              ≤ |deriv (fun z' => baseFn g θ (z', y.2)) y.1|
                + |deriv (fun t => baseFn g θ (y.1, t)) y.2| := by
            simp only [baseBranch]
            exact norm_smul_fst_add_smul_snd_le _ _
          have hb : |deriv (fun z' => baseFn g θ (z', y.2)) y.1|
              + |deriv (fun t => baseFn g θ (y.1, t)) y.2| < ε := by
            have h1 : |deriv (fun z' => baseFn g θ (z', y.2)) y.1| < η := by
              simpa [baseFn] using hdz hy1
            have h2 : |deriv (fun t => baseFn g θ (y.1, t)) y.2| < η := by
              simpa [baseFn] using hdt hy1
            have hηhalf : η ≤ ε / 2 := by
              rw [hηdef]
              have h2 : (2:ℝ) ≤ 2 * (|τ| + 3) := by linarith [abs_nonneg τ]
              exact div_le_div_of_nonneg_left (le_of_lt hε) (by norm_num) h2
            linarith [h1, h2, hηhalf]
          exact lt_of_le_of_lt hsplit hb
      · -- `y.1 ≤ 0`
        have hye : extDeriv g θ y = 0 := by
          obtain ⟨y1, y2⟩ := y
          exact extDeriv_of_nonpos g θ (le_of_not_gt hy1) y2
        rw [hye]
        simpa using hε
    · -- `z > 0`
      have hxV : (z, τ) ∈ Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ) := ⟨hz, hτU.1⟩
      by_cases hτn : τ < 0
      · -- the jet branch
        have hev : extDeriv g θ =ᶠ[𝓝 ((z, τ) : ℝ × ℝ)] jetBranch g θ := by
          filter_upwards [(isOpen_Ioi.preimage continuous_fst).mem_nhds hz,
            (isOpen_Iio.preimage continuous_snd).mem_nhds hτn] with y hy1 hy2
          exact extDeriv_of_pos_of_neg' g θ hy1 hy2
        exact ((hAcont.continuousAt (hVopen.mem_nhds hxV)).congr_of_eventuallyEq hev).continuousWithinAt
      · rcases lt_or_eq_of_le (le_of_not_gt hτn) with hτp | hτ0
        · -- the family branch
          have hev : extDeriv g θ =ᶠ[𝓝 ((z, τ) : ℝ × ℝ)] baseBranch g θ := by
            filter_upwards [(isOpen_Ioi.preimage continuous_fst).mem_nhds hz,
              (isOpen_Ioi.preimage continuous_snd).mem_nhds hτp] with y hy1 hy2
            exact extDeriv_of_pos_of_nonneg' g θ hy1 (le_of_lt hy2)
          exact ((hBcont.continuousAt (hVopen.mem_nhds hxV)).congr_of_eventuallyEq hev).continuousWithinAt
        · -- the `τ = 0` join: the two branches agree there
          subst hτ0
          have hxV0 : (z, (0:ℝ)) ∈ Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ) := ⟨hz, by norm_num⟩
          have hAca : ContinuousAt (jetBranch g θ) (z, 0) :=
            hAcont.continuousAt (hVopen.mem_nhds hxV0)
          have hBca : ContinuousAt (baseBranch g θ) (z, 0) :=
            hBcont.continuousAt (hVopen.mem_nhds hxV0)
          have hAB : jetBranch g θ (z, 0) = baseBranch g θ (z, 0) :=
            jetBranch_eq_baseBranch_at_zero g θ z
          have hxe : extDeriv g θ (z, 0) = jetBranch g θ (z, 0) := by
            rw [extDeriv_of_pos_of_nonneg' g θ hz le_rfl]
            exact hAB.symm
          refine ContinuousAt.continuousWithinAt ?_
          rw [ContinuousAt, hxe, Metric.tendsto_nhds]
          intro ε hε
          have hAev : ∀ᶠ y in 𝓝 ((z, 0) : ℝ × ℝ),
              dist (jetBranch g θ y) (jetBranch g θ (z, 0)) < ε :=
            (Metric.tendsto_nhds.mp hAca) ε hε
          have hBev : ∀ᶠ y in 𝓝 ((z, 0) : ℝ × ℝ),
              dist (baseBranch g θ y) (baseBranch g θ (z, 0)) < ε :=
            (Metric.tendsto_nhds.mp hBca) ε hε
          have hVev : ∀ᶠ y in 𝓝 ((z, 0) : ℝ × ℝ), 0 < y.1 :=
            (isOpen_Ioi.preimage continuous_fst).mem_nhds hz
          filter_upwards [hAev, hBev, hVev] with y hyA hyB hy1
          by_cases hy : y.2 < 0
          · have hye : extDeriv g θ y = jetBranch g θ y := by
              obtain ⟨y1, y2⟩ := y
              exact extDeriv_of_pos_of_neg' g θ hy1 hy
            rw [hye]
            exact hyA
          · have hye : extDeriv g θ y = baseBranch g θ y := by
              obtain ⟨y1, y2⟩ := y
              exact extDeriv_of_pos_of_nonneg' g θ hy1 (le_of_not_gt hy)
            rw [hye, hAB]
            exact hyB
  -- ## Assembly
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl]
  refine (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hUopen.uniqueDiffOn).2 ?_
  refine ⟨?_, extDeriv g θ, ?_, ?_⟩
  · intro h
    exact absurd h (by simp)
  · exact contDiffOn_zero.mpr hcont
  · intro x hx
    exact (hderiv x hx).hasFDerivWithinAt

