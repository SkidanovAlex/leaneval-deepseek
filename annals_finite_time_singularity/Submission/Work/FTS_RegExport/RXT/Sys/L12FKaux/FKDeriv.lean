import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.FKJets
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.FtauSlot
import Submission.Work.FTS_RegExport.RXR1.hasDerivAt_of_tendsto_deriv
import Submission.Work.FTS.StrongEps.classC_mixed_sup_le_four
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc
import Submission.Work.FTS_RegExport.RXT.Ftau_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `L12FKaux.FKDeriv` — the `z`-derivatives of the angular moments of `F(τ)`

* `Ftau_slot_le3` — uniform slot bounds of order `≤ 3` for `F_* + slice (gn n) τ`;
* `Qlim_eq_FK` — `FK (F_* + slice (GR α g) τ)(z) = Qlim α g τ 0 z`;
* `Qlim_bound` — `|Qlim k z| ≤ 3(π/2)C_B` for `k ≤ 2`;
* `Qlim_hasDerivAt_1`, `Qlim_hasDerivAt_2` — the first two `z`-derivatives of `Qlim · 0`, by
  passing to the limit in the corresponding derivatives of the approximants
  (`RXR1.hasDerivAt_of_tendsto_deriv`).

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.Sys.L12FKaux

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## §1 Order-`3` slot bounds for the approximants -/

/-- `F_*` is `C^n` on the open quadrant, at every order `n`. -/
theorem Fstar_contDiffOn {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (n : ℕ) :
    ContDiffOn ℝ n (Function.uncurry (Work.Construction.Fstar β))
      Work.FTS.EllipticEst.Q0 := by
  have hGam : ContDiffOn ℝ n (fun p : ℝ × ℝ => Work.Spaces.Gam β p.2)
      Work.FTS.EllipticEst.Q0 := Work.FTS_RegExport.RXT.ftau_contDiffOn_Gam_Q0 β n
  have hc : Work.Spaces.c β ≠ 0 := by
    have h := (Work.Spaces.c_bounds β hβ hβ1).1
    intro h0; rw [h0] at h; norm_num at h
  have h1 : ContDiffOn ℝ n (fun p : ℝ × ℝ => Work.Spaces.Gam β p.2 / Work.Spaces.c β)
      Work.FTS.EllipticEst.Q0 := hGam.div contDiffOn_const (fun _ _ => hc)
  have h2 : ContDiffOn ℝ n (fun p : ℝ × ℝ => β * (Work.Spaces.Gam β p.2 / Work.Spaces.c β))
      Work.FTS.EllipticEst.Q0 := contDiffOn_const.mul h1
  have h3 : ContDiffOn ℝ n (fun p : ℝ × ℝ => Work.FM.Fstar p.1)
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS_RegExport.RXT.ftau_contDiffOn_fst_of
      (Work.FTS_RegExport.RXT.ftau_contDiffOn_FM_Fstar n)
  exact (h2.mul h3).congr (fun _ _ => rfl)

/-- **Uniform slot bounds of order `≤ 3`** for `F(τ) = F_* + slice (gn n) τ`. -/
theorem Ftau_slot_le3 {α C₀ B : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {gn : ℕ → Fam}
    (hcl : ∀ (n : ℕ) (τ : ℝ), 0 ≤ τ →
      Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) (slice (gn n) τ))
    (hXn6 : ∀ (n : ℕ) (τ : ℝ), 0 ≤ τ →
      Work.FTS.StrongGlobal.Xn6 (Work.FTS.Regularity.pExp α) (slice (gn n) τ) ≤ B)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    ∃ CB : ℝ, 0 ≤ CB ∧ ∀ (n : ℕ) (k : ℕ), k ≤ 3 → ∀ z θ : ℝ,
      0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (gn n) τ) z θ| ≤ CB := by
  have hβ : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hβ1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  have hγ1 : 0 < Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1 := by
    rw [Work.Spaces.gam_sub_one]; linarith
  obtain ⟨C4, hC4pos, hC4⟩ := Work.FTS.StrongEps.classC_mixed_sup_le_four
  obtain ⟨M, hM0, hM⟩ := Work.FTS.StrongPersist.H6Pair6Aux.FstarJet7
  set Cu : ℝ := C4 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1)
    * max B 0 with hCu
  have hCu0 : 0 ≤ Cu := by
    rw [hCu]; exact mul_nonneg (div_nonneg hC4pos.le (Real.sqrt_nonneg _)) (le_max_right _ _)
  refine ⟨10 * M + Cu, by linarith, ?_⟩
  intro n k hk z θ hz h1 h2
  have hadd : Work.Spaces.DzIter k (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
      (gn n) τ) z θ
      = Work.Spaces.DzIter k (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
        + Work.Spaces.DzIter k (slice (gn n) τ) z θ := by
    have h := Work.FTS.CoercivityFix.Transfer.E2pkg.DzIter_add_of_contDiffOn
      (n := 4) (f₁ := Work.Construction.Fstar (Work.FTS.Regularity.pExp α))
      (f₂ := fun z θ => gn n z θ τ) Work.FTS.EllipticEst.isOpen_Q0
      (Fstar_contDiffOn hβ hβ1 4) ((hcl n τ hτ).reg.forall 4) k (by omega) (z, θ)
      ⟨hz, h1, h2⟩
    rw [show Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ
        = Work.Construction.Fstar (Work.FTS.Regularity.pExp α)
          + fun z θ => gn n z θ τ from rfl]
    rw [show slice (gn n) τ = fun z θ => gn n z θ τ from rfl]
    exact h
  rw [hadd]
  have hA : |Work.Spaces.DzIter k (Work.Construction.Fstar (Work.FTS.Regularity.pExp α))
      z θ| ≤ 10 * M :=
    Work.FTS_RegExport.RXT.ftau_DzIter_Fstar_le (α := α) hα hα13 hM k (by omega) z θ hz h1 h2
  have hB : |Work.Spaces.DzIter k (slice (gn n) τ) z θ| ≤ Cu := by
    have h := hC4 (Work.FTS.Regularity.pExp α) ⟨hβ, hβ1⟩ (hcl n τ hτ) k 0 (by omega)
      ⟨hz, h1, h2⟩
    have hX : Work.FTS.StrongGlobal.Xn6 (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
        ≤ max B 0 := le_trans (hXn6 n τ hτ) (le_max_left _ _)
    rw [hCu]
    refine le_trans h (mul_le_mul_of_nonneg_left hX ?_)
    exact div_nonneg hC4pos.le (Real.sqrt_nonneg _)
  calc |Work.Spaces.DzIter k (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
        + Work.Spaces.DzIter k (slice (gn n) τ) z θ|
      ≤ |Work.Spaces.DzIter k (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ|
        + |Work.Spaces.DzIter k (slice (gn n) τ) z θ| := abs_add_le _ _
    _ ≤ 10 * M + Cu := add_le_add hA hB

/-! ## §2 `FK` of the limit profile and the bounds on the moments -/

/-- `FK (F_* + slice (GR α g) τ)(z) = Qlim α g τ 0 z`. -/
theorem Qlim_eq_FK {α : ℝ} (hα : 0 < α) {g : Fam} {τ : ℝ} (hτ : 0 ≤ τ) {z : ℝ} (hz : 0 < z) :
    Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
      (Work.FTS.RegExportIface.RXT.GR α g) τ) z = Qlim α g τ 0 z := by
  rw [Work.Construction.FK, Qlim]
  refine MeasureTheory.setIntegral_congr_fun (s := Work.Spaces.Iθ) measurableSet_Icc
    (fun θ hθ => ?_)
  have hGR : Work.FTS.RegExportIface.RXT.GR α g z θ τ = g z θ τ :=
    Work.FTS_RegExport.RXT.ftau_GR_of_quad (α := α) hτ hz hθ.1 hθ.2
  simp only [Work.Spaces.DzIter_zero, Work.FTS.Galerkin.slice_apply,
    Work.Construction.Ftau, hGR]
  ring

/-- **The moments of the limit are bounded by `3(π/2)C_B`** for `k ≤ 2`. -/
theorem Qlim_bound {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {gn : ℕ → Fam} {g : Fam} {τ : ℝ} {Cw CB : ℝ} (hCw : 0 ≤ Cw) (hCB : 0 ≤ CB)
    (h4 : ∀ n : ℕ, ContDiffOn ℝ 4 (Function.uncurry (slice (gn n) τ))
      Work.FTS.EllipticEst.Q0)
    (hbd : ∀ (n : ℕ) (k : ℕ), k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k (slice (gn n) τ) z θ| ≤ Cw * SW z)
    (h2 : ∀ n : ℕ, ContDiffOn ℝ 4 (Function.uncurry
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ))
      Work.FTS.EllipticEst.Q0)
    (hsl : ∀ (n : ℕ) (k : ℕ), k ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (gn n) τ) z θ| ≤ CB)
    (hjet : ∀ (k : ℕ), k ≤ 2 → ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n => Work.Spaces.DzIter k (slice (gn n) τ) z θ) Filter.atTop
        (𝓝 (Work.Spaces.DzIter k (slice g τ) z θ)))
    {k : ℕ} (hk : k ≤ 2) {z : ℝ} (hz : 0 < z) :
    |Qlim α g τ k z| ≤ 3 * (Real.pi / 2) * CB := by
  refine le_of_tendsto ((Qapp_tendsto (α := α) hα hα13 hCw hCB h4 hbd h2 hsl hjet hk hz).abs)
    (Filter.Eventually.of_forall fun n => ?_)
  exact Qapp_bound (α := α) hα hα13 hCB h2 hsl n (by omega) hz


/-! ## §3 The `z`-derivatives of `Qlim · 0` -/

/-- **First derivative.** -/
theorem Qlim_hasDerivAt_1 {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {gn : ℕ → Fam} {g : Fam} {τ : ℝ} {Cw CB : ℝ} (hCw : 0 ≤ Cw) (hCB : 0 ≤ CB)
    (h4 : ∀ n : ℕ, ContDiffOn ℝ 4 (Function.uncurry (slice (gn n) τ))
      Work.FTS.EllipticEst.Q0)
    (hbd : ∀ (n : ℕ) (k : ℕ), k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k (slice (gn n) τ) z θ| ≤ Cw * SW z)
    (h2 : ∀ n : ℕ, ContDiffOn ℝ 4 (Function.uncurry
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ))
      Work.FTS.EllipticEst.Q0)
    (hsl : ∀ (n : ℕ) (k : ℕ), k ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (gn n) τ) z θ| ≤ CB)
    (hjet : ∀ (k : ℕ), k ≤ 2 → ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n => Work.Spaces.DzIter k (slice (gn n) τ) z θ) Filter.atTop
        (𝓝 (Work.Spaces.DzIter k (slice g τ) z θ)))
    {z : ℝ} (hz : 0 < z) :
    HasDerivAt (Qlim α g τ 0) (Qlim α g τ 1 z / z) z := by
  have hder : ∀ n : ℕ, ∀ x ∈ Set.Ioo (z / 2) (2 * z),
      HasDerivAt (Qapp α gn τ n 0) (Qapp α gn τ n 1 x / x) x := by
    intro n x hx
    have hx0 : 0 < x := by linarith [hx.1, hz]
    exact Qapp_hasDerivAt (α := α) hα hα13 hCB h2 hsl n (k := 0) (by norm_num) hx0
  have hvdiff : ∀ n : ℕ, DifferentiableOn ℝ (fun x => Qapp α gn τ n 1 x / x)
      (Set.Ioo (z / 2) (2 * z)) := by
    intro n
    refine DifferentiableOn.div ?_ differentiableOn_id ?_
    · intro x hx
      have hx0 : 0 < x := by linarith [hx.1, hz]
      exact ((Qapp_hasDerivAt (α := α) hα hα13 hCB h2 hsl n (k := 1) (by omega)
        hx0).differentiableAt).differentiableWithinAt
    · intro x hx
      exact ne_of_gt (by linarith [hx.1, hz] : (0 : ℝ) < x)
  have hM : ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, ∀ x ∈ Set.Ioo (z / 2) (2 * z),
      |Qapp α gn τ n 1 x / x| ≤ M := by
    refine ⟨3 * (Real.pi / 2) * CB * 2 / z, by positivity, ?_⟩
    intro n x hx
    have hx0 : 0 < x := by linarith [hx.1, hz]
    have h1 : |Qapp α gn τ n 1 x| ≤ 3 * (Real.pi / 2) * CB :=
      Qapp_bound (α := α) hα hα13 hCB h2 hsl n (k := 1) (by omega) hx0
    have h2' : (1 : ℝ) / x ≤ 2 / z := by
      rw [div_le_div_iff₀ hx0 hz]
      linarith [hx.1]
    rw [abs_div, abs_of_pos hx0]
    calc |Qapp α gn τ n 1 x| / x = |Qapp α gn τ n 1 x| * (1 / x) := by ring
      _ ≤ 3 * (Real.pi / 2) * CB * (2 / z) :=
          mul_le_mul h1 h2' (by positivity) (by positivity)
      _ = 3 * (Real.pi / 2) * CB * 2 / z := by ring
  have hL : ∃ L : ℝ, 0 ≤ L ∧ ∀ n : ℕ, ∀ x ∈ Set.Ioo (z / 2) (2 * z),
      |deriv (fun y => Qapp α gn τ n 1 y / y) x| ≤ L := by
    refine ⟨2 * (3 * (Real.pi / 2) * CB) / (z / 2) ^ 2, by positivity, ?_⟩
    intro n x hx
    have hx0 : 0 < x := by linarith [hx.1, hz]
    have hq := (Qapp_hasDerivAt (α := α) hα hα13 hCB h2 hsl n (k := 1) (by omega)
      hx0).div (hasDerivAt_id x) (ne_of_gt hx0)
    have hval : deriv (fun y => Qapp α gn τ n 1 y / y) x
        = (Qapp α gn τ n 2 x - Qapp α gn τ n 1 x) / x ^ 2 := by
      have hxne : x ≠ 0 := ne_of_gt hx0
      rw [show deriv (fun y : ℝ => Qapp α gn τ n 1 y / y) x
          = deriv (Qapp α gn τ n 1 / id) x from rfl, hq.deriv]
      simp only [id_eq]
      field_simp [hxne]
    rw [hval, abs_div, abs_of_pos (by positivity : (0 : ℝ) < x ^ 2)]
    have h2b : |Qapp α gn τ n 2 x| ≤ 3 * (Real.pi / 2) * CB :=
      Qapp_bound (α := α) hα hα13 hCB h2 hsl n (k := 2) (by omega) hx0
    have h1b : |Qapp α gn τ n 1 x| ≤ 3 * (Real.pi / 2) * CB :=
      Qapp_bound (α := α) hα hα13 hCB h2 hsl n (k := 1) (by omega) hx0
    have hnum : |Qapp α gn τ n 2 x - Qapp α gn τ n 1 x|
        ≤ 2 * (3 * (Real.pi / 2) * CB) := by
      calc |Qapp α gn τ n 2 x - Qapp α gn τ n 1 x|
          = |Qapp α gn τ n 2 x + -Qapp α gn τ n 1 x| := by ring_nf
        _ ≤ |Qapp α gn τ n 2 x| + |-Qapp α gn τ n 1 x| := abs_add_le _ _
        _ = |Qapp α gn τ n 2 x| + |Qapp α gn τ n 1 x| := by rw [abs_neg]
        _ ≤ 2 * (3 * (Real.pi / 2) * CB) := by linarith
    have hxd : (z / 2) ^ 2 ≤ x ^ 2 := by
      have h1 : z / 2 ≤ x := hx.1.le
      have h2y : 0 ≤ z / 2 := by linarith [hz]
      nlinarith
    exact div_le_div₀ (by positivity) hnum (by positivity) hxd
  have hu : ∀ x ∈ Set.Ioo (z / 2) (2 * z),
      Filter.Tendsto (fun n => Qapp α gn τ n 0 x) Filter.atTop (𝓝 (Qlim α g τ 0 x)) := by
    intro x hx
    exact Qapp_tendsto (α := α) hα hα13 hCw hCB h4 hbd h2 hsl hjet (k := 0) (by norm_num)
      (by linarith [hx.1, hz])
  have hv : ∀ x ∈ Set.Ioo (z / 2) (2 * z),
      Filter.Tendsto (fun n => Qapp α gn τ n 1 x / x) Filter.atTop (𝓝 (Qlim α g τ 1 x / x)) := by
    intro x hx
    exact (Qapp_tendsto (α := α) hα hα13 hCw hCB h4 hbd h2 hsl hjet (k := 1) (by norm_num)
      (by linarith [hx.1, hz])).div_const x
  exact Work.FTS_RegExport.RXR1.hasDerivAt_of_tendsto_deriv (a := z / 2) (b := 2 * z) (by linarith) hder hvdiff
    hM hL hu hv z ⟨by linarith, by linarith⟩


/-- **Second derivative**: `Qlim · 1` is differentiable with derivative `Qlim · 2 / z`. -/
theorem Qlim_hasDerivAt_2 {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {gn : ℕ → Fam} {g : Fam} {τ : ℝ} {Cw CB : ℝ} (hCw : 0 ≤ Cw) (hCB : 0 ≤ CB)
    (h4 : ∀ n : ℕ, ContDiffOn ℝ 4 (Function.uncurry (slice (gn n) τ))
      Work.FTS.EllipticEst.Q0)
    (hbd : ∀ (n : ℕ) (k : ℕ), k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k (slice (gn n) τ) z θ| ≤ Cw * SW z)
    (h2 : ∀ n : ℕ, ContDiffOn ℝ 4 (Function.uncurry
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ))
      Work.FTS.EllipticEst.Q0)
    (hsl : ∀ (n : ℕ) (k : ℕ), k ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (gn n) τ) z θ| ≤ CB)
    (hjet : ∀ (k : ℕ), k ≤ 2 → ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n => Work.Spaces.DzIter k (slice (gn n) τ) z θ) Filter.atTop
        (𝓝 (Work.Spaces.DzIter k (slice g τ) z θ)))
    {z : ℝ} (hz : 0 < z) :
    HasDerivAt (Qlim α g τ 1) (Qlim α g τ 2 z / z) z := by
  have hder : ∀ n : ℕ, ∀ x ∈ Set.Ioo (z / 2) (2 * z),
      HasDerivAt (Qapp α gn τ n 1) (Qapp α gn τ n 2 x / x) x := by
    intro n x hx
    have hx0 : 0 < x := by linarith [hx.1, hz]
    exact Qapp_hasDerivAt (α := α) hα hα13 hCB h2 hsl n (k := 1) (by omega) hx0
  have hvdiff : ∀ n : ℕ, DifferentiableOn ℝ (fun x => Qapp α gn τ n 2 x / x)
      (Set.Ioo (z / 2) (2 * z)) := by
    intro n
    refine DifferentiableOn.div ?_ differentiableOn_id ?_
    · intro x hx
      have hx0 : 0 < x := by linarith [hx.1, hz]
      exact ((Qapp_hasDerivAt (α := α) hα hα13 hCB h2 hsl n (k := 2) (by omega)
        hx0).differentiableAt).differentiableWithinAt
    · intro x hx
      exact ne_of_gt (by linarith [hx.1, hz] : (0 : ℝ) < x)
  have hM : ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, ∀ x ∈ Set.Ioo (z / 2) (2 * z),
      |Qapp α gn τ n 2 x / x| ≤ M := by
    refine ⟨3 * (Real.pi / 2) * CB * 2 / z, by positivity, ?_⟩
    intro n x hx
    have hx0 : 0 < x := by linarith [hx.1, hz]
    have h1 : |Qapp α gn τ n 2 x| ≤ 3 * (Real.pi / 2) * CB :=
      Qapp_bound (α := α) hα hα13 hCB h2 hsl n (k := 2) (by omega) hx0
    have h2' : (1 : ℝ) / x ≤ 2 / z := by
      rw [div_le_div_iff₀ hx0 hz]
      linarith [hx.1]
    rw [abs_div, abs_of_pos hx0]
    calc |Qapp α gn τ n 2 x| / x = |Qapp α gn τ n 2 x| * (1 / x) := by ring
      _ ≤ 3 * (Real.pi / 2) * CB * (2 / z) :=
          mul_le_mul h1 h2' (by positivity) (by positivity)
      _ = 3 * (Real.pi / 2) * CB * 2 / z := by ring
  have hL : ∃ L : ℝ, 0 ≤ L ∧ ∀ n : ℕ, ∀ x ∈ Set.Ioo (z / 2) (2 * z),
      |deriv (fun y => Qapp α gn τ n 2 y / y) x| ≤ L := by
    refine ⟨2 * (3 * (Real.pi / 2) * CB) / (z / 2) ^ 2, by positivity, ?_⟩
    intro n x hx
    have hx0 : 0 < x := by linarith [hx.1, hz]
    have hxne : x ≠ 0 := ne_of_gt hx0
    have hq := (Qapp_hasDerivAt (α := α) hα hα13 hCB h2 hsl n (k := 2) (by omega)
      hx0).div (hasDerivAt_id x) hxne
    have hval : deriv (fun y => Qapp α gn τ n 2 y / y) x
        = (Qapp α gn τ n 3 x - Qapp α gn τ n 2 x) / x ^ 2 := by
      rw [show deriv (fun y : ℝ => Qapp α gn τ n 2 y / y) x
          = deriv (Qapp α gn τ n 2 / id) x from rfl, hq.deriv]
      simp only [id_eq]
      field_simp [hxne]
    rw [hval, abs_div, abs_of_pos (by positivity : (0 : ℝ) < x ^ 2)]
    have h3b : |Qapp α gn τ n 3 x| ≤ 3 * (Real.pi / 2) * CB :=
      Qapp_bound (α := α) hα hα13 hCB h2 hsl n (k := 3) (by omega) hx0
    have h2b : |Qapp α gn τ n 2 x| ≤ 3 * (Real.pi / 2) * CB :=
      Qapp_bound (α := α) hα hα13 hCB h2 hsl n (k := 2) (by omega) hx0
    have hnum : |Qapp α gn τ n 3 x - Qapp α gn τ n 2 x|
        ≤ 2 * (3 * (Real.pi / 2) * CB) := by
      calc |Qapp α gn τ n 3 x - Qapp α gn τ n 2 x|
          = |Qapp α gn τ n 3 x + -Qapp α gn τ n 2 x| := by ring_nf
        _ ≤ |Qapp α gn τ n 3 x| + |-Qapp α gn τ n 2 x| := abs_add_le _ _
        _ = |Qapp α gn τ n 3 x| + |Qapp α gn τ n 2 x| := by rw [abs_neg]
        _ ≤ 2 * (3 * (Real.pi / 2) * CB) := by linarith
    have hxd : (z / 2) ^ 2 ≤ x ^ 2 := by
      have h1 : z / 2 ≤ x := hx.1.le
      have h2y : 0 ≤ z / 2 := by linarith [hz]
      nlinarith
    exact div_le_div₀ (by positivity) hnum (by positivity) hxd
  have hu : ∀ x ∈ Set.Ioo (z / 2) (2 * z),
      Filter.Tendsto (fun n => Qapp α gn τ n 1 x) Filter.atTop (𝓝 (Qlim α g τ 1 x)) := by
    intro x hx
    exact Qapp_tendsto (α := α) hα hα13 hCw hCB h4 hbd h2 hsl hjet (k := 1) (by norm_num)
      (by linarith [hx.1, hz])
  have hv : ∀ x ∈ Set.Ioo (z / 2) (2 * z),
      Filter.Tendsto (fun n => Qapp α gn τ n 2 x / x) Filter.atTop (𝓝 (Qlim α g τ 2 x / x)) := by
    intro x hx
    exact (Qapp_tendsto (α := α) hα hα13 hCw hCB h4 hbd h2 hsl hjet (k := 2) (by norm_num)
      (by linarith [hx.1, hz])).div_const x
  exact Work.FTS_RegExport.RXR1.hasDerivAt_of_tendsto_deriv (a := z / 2) (b := 2 * z)
    (by linarith) hder hvdiff hM hL hu hv z ⟨by linarith, by linarith⟩

end Work.FTS_RegExport.RXT.Sys.L12FKaux
