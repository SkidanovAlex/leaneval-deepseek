import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS_RegExport.RXT.Sys.L12FK_family_jets
import Submission.Work.FTS_RegExport.RXT.jc3
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKjet.Jets
import Submission.Work.FTS_RegExport.RXT.SysAux.L12_jet_pkg_uniform
import Submission.Work.FTS_RegExport.RXT.SysAux.FK_jet_pkg_uniform
import Submission.Work.FTS_RegExport.RXT0.QlimTauLipW
import Submission.Work.FTS_RegExport.RXT0.QlimZLipBox
import Submission.Work.FTS_RegExport.RXT0.L12densFtauIntegrable
import Submission.Work.FTS_RegExport.RXT0.slotJetsJointCont

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT0.RXJets

-- *** `L₁₂`/`𝔽K` jets of the modulated profile are jointly continuous in `(z,τ)`. ***
--
-- For a family `g` with `DynOK' (pExp α) C₀ Φs E g`, the `D_z`-jets `D_z^j L₁₂(F_τ)` and
-- `D_z^j 𝔽K(F_τ)` (`j ≤ 2`) of the profile `F_τ = F_* + slice (GR α g) τ`, evaluated at
-- `(z,0)`, are jointly continuous on `(0,∞) × [0,S]`.  (This is the sibling
-- `RXT0/L12FKJetsJointCont` at a fresh path.)
--
-- Route (implemented below).
--  * `RXT.Sys.L12FK_family_jets` gives, uniformly on the horizon, `|D_z^j 𝔽K(F_τ) z| ≤ C`
--    (`j ≤ 2`), `|L₁₂(F_τ) z| ≤ C`, `D_z L₁₂(F_τ) = -𝔽K(F_τ)`, **and the τ-Lipschitz bounds**
--    `|L₁₂(F_τ) z - L₁₂(F_τ') z| ≤ C|τ-τ'|`, `|𝔽K(F_τ) z - 𝔽K(F_τ') z| ≤ C|τ-τ'|`.
--  * `RXT0.QlimTauLipW` gives the *weighted* τ-Lipschitz bound
--    `|Qlim α g τ k z - Qlim α g τ' k z| ≤ C·SW z·|τ-τ'|` (`SW z = z^{3/2}/(1+z)²`), `k ≤ 2`;
--    since `SW ≤ 1` on `(0,∞)` (`L12FKaux.SW_le_one`) this is an unweighted τ-Lipschitz bound,
--    uniformly in `z`.  `RXT0.QlimZLipBox` gives the boxwise `z`-Lipschitz bound, uniform in `τ`;
--    `L12FKaux.FK_DzIter_eq` identifies the jets: `D_z^j 𝔽K(F_τ) z = Qlim α g τ j z`.
--  * the `L₁₂`-jets: `D_z L₁₂ = -𝔽K = -Qlim · 0` pointwise on `(0,∞)`, and therefore
--    `D_z² L₁₂ = -D_z 𝔽K = -Qlim · 1`; while `L₁₂(F_τ)` itself is continuous on `(0,∞)` at frozen
--    `τ` because it is differentiable there (`L12FKaux.L12_hasDerivAt`, which passes to the limit
--    along the class-`C` approximants of the `LimApprox` clause).
--  * Glue: `continuousOn_slab_of_lipschitz` below, the two-variable variant of the proved
--    `RXT0.slotJetsJointCont.jointContOnSlab_of_lipschitz`: a constant-`τ`-Lipschitz function
--    whose `z`-slices are continuous at every frozen `τ` is jointly continuous.

noncomputable section

open scoped Real Topology
open Set Filter MeasureTheory

set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
  {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}

/-- The modulated profile `F_τ = F_* + slice (GR α g) τ`. -/
abbrev Fpr (α : ℝ) (g : Work.FTS.Galerkin.Fam) (τ : ℝ) : ℝ → ℝ → ℝ :=
  Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ

/-- The `k`-th angular moment `Qlim α g τ k` of the limit profile. -/
abbrev Qlm (α : ℝ) (g : Work.FTS.Galerkin.Fam) (τ : ℝ) (k : ℕ) : ℝ → ℝ :=
  Work.FTS_RegExport.RXT.Sys.L12FKaux.Qlim α g τ k

/-- The radial weight `z^{3/2}/(1+z)²` of the standing bound. -/
abbrev SWq (z : ℝ) : ℝ := Work.FTS_RegExport.RXT.Sys.L12FKaux.SW z

/-! ## §1 The two-variable slab assembly -/

/-- **Two-variable slab assembly.**  A function `(z,τ) ↦ F z τ` on `(0,∞) × [0,S]` is jointly
continuous as soon as it is Lipschitz in `τ` with a constant `K` valid uniformly on `z > 0`, and
its `z`-slice at every frozen `τ ∈ [0,S]` is continuous on `(0,∞)`.

Obtained from the three-variable `jointContOnSlab_of_lipschitz` (of
`RXT0/slotJetsJointCont.lean`) by evaluating at the constant angle `θ = π/4`. -/
theorem continuousOn_slab_of_lipschitz {S K : ℝ} {F : ℝ → ℝ → ℝ} (hK : 0 ≤ K)
    (hLip : ∀ z : ℝ, 0 < z → ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ τ' ∈ Set.Icc (0 : ℝ) S,
      |F z τ - F z τ'| ≤ K * |τ - τ'|)
    (hspat : ∀ τ ∈ Set.Icc (0 : ℝ) S, ContinuousOn (fun z : ℝ => F z τ) (Set.Ioi 0)) :
    ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) S) := by
  have h3 : ContinuousOn (fun p : ℝ × ℝ × ℝ => F p.1 p.2.2)
      (Set.Ioi (0 : ℝ) ×ˢ (Set.Ioo (0 : ℝ) (Real.pi / 2) ×ˢ Set.Icc (0 : ℝ) S)) :=
    Work.FTS_RegExport.RXT0.jointContOnSlab_of_lipschitz (S := S) (K := K)
      (F := fun z _ τ => F z τ) hK
      (fun z θ hz hθ hθ2 τ hτ τ' hτ' => hLip z hz τ hτ τ' hτ')
      (fun τ hτ => by
        have hmap : Set.MapsTo (Prod.fst : ℝ × ℝ → ℝ)
            (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) (Set.Ioi 0) :=
          fun p hp => hp.1
        have h := (hspat τ hτ).comp continuous_fst.continuousOn hmap
        simpa [Function.comp_def] using h)
  have hφ : ContinuousOn (fun q : ℝ × ℝ => (q.1, (Real.pi / 4, q.2)))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) S) :=
    (continuous_fst.prodMk (continuous_const.prodMk continuous_snd)).continuousOn
  have hMaps : Set.MapsTo (fun q : ℝ × ℝ => (q.1, (Real.pi / 4, q.2)))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) S)
      (Set.Ioi (0 : ℝ) ×ˢ (Set.Ioo (0 : ℝ) (Real.pi / 2) ×ˢ Set.Icc (0 : ℝ) S)) := by
    rintro ⟨z, τ⟩ ⟨hz, hτ⟩
    exact ⟨hz, ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩, hτ⟩
  have hcomp := h3.comp hφ hMaps
  simpa [Function.comp_def] using hcomp

/-- **Continuity at an interior point of a box from a Lipschitz bound on the box.** -/
theorem continuousAt_of_lipschitz_Icc {f : ℝ → ℝ} {a b C x : ℝ}
    (hb : ∀ x' ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |f x' - f y| ≤ C * |x' - y|)
    (hx : x ∈ Set.Ioo a b) : ContinuousAt f x := by
  change Filter.Tendsto f (𝓝 x) (𝓝 (f x))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbd : ∀ᶠ y in 𝓝 x, ‖f y - f x‖ ≤ C * |y - x| := by
    filter_upwards [Icc_mem_nhds hx.1 hx.2] with y hy
    rw [Real.norm_eq_abs]
    exact hb y hy x ⟨hx.1.le, hx.2.le⟩
  have hg : Filter.Tendsto (fun y : ℝ => C * |y - x|) (𝓝 x) (𝓝 0) := by
    have h1 : ContinuousAt (fun y : ℝ => y - x) x := continuousAt_id.sub continuousAt_const
    have h2 : ContinuousAt (fun y : ℝ => |y - x|) x := h1.abs
    have h3 : ContinuousAt (fun y : ℝ => C * |y - x|) x := h2.const_mul C
    have h4 := h3.tendsto
    rwa [sub_self, abs_zero, mul_zero] at h4
  exact squeeze_zero' (Filter.Eventually.of_forall (fun y => norm_nonneg _)) hbd hg

/-- **`D_z² u = -z·d`** from `D_z u = -v` near `z` and `v' z = d`.  Applied below with
`u = L₁₂(F_τ)`, `v = 𝔽K(F_τ)`, `d = Qlim α g τ 1 z / z`. -/
theorem DzdIter_two_eq_neg_mul {u v : ℝ → ℝ} {z d : ℝ}
    (h1e : ∀ᶠ w in 𝓝 z, Work.Elliptic.DzdIter 1 u w = -v w)
    (hv : HasDerivAt v d z) :
    Work.Elliptic.DzdIter 2 u z = -z * d := by
  have hder : HasDerivAt (Work.Elliptic.DzdIter 1 u) (-d) z :=
    (hv.neg).congr_of_eventuallyEq h1e
  have h2 : Work.Elliptic.DzdIter 2 u z
      = z * deriv (Work.Elliptic.DzdIter 1 u) z := rfl
  rw [h2, hder.deriv]
  ring

/-! ## §2 The target -/

theorem L12FKJetsJointCont {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g) :
    ∀ S > 0, ∀ j : ℕ, j ≤ 2 →
      ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter j
        (fun z (_ : ℝ) => Work.Construction.L12
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) p.2) z) p.1 0)
        (Set.Ioi (0:ℝ) ×ˢ Set.Icc (0:ℝ) S) ∧
      ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter j
        (fun z (_ : ℝ) => Work.Construction.FK
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) p.2) z) p.1 0)
        (Set.Ioi (0:ℝ) ×ˢ Set.Icc (0:ℝ) S) := by
  intro S hS j hj
  have hβ : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hβ1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  -- ## §2.1 the approximating class-`C` families of the `LimApprox` clause
  have hT : 0 < max S 1 := lt_of_lt_of_le zero_lt_one (le_max_right S 1)
  obtain ⟨gn, B, L, hC, hLip, hjet0, -⟩ := hOK.2 (max S 1) hT
  have hmemT : ∀ τ ∈ Set.Icc (0:ℝ) S, τ ∈ Set.Icc (0:ℝ) (max S 1) :=
    fun τ hτ => ⟨hτ.1, le_trans hτ.2 (le_max_left S 1)⟩
  have hcl : ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0:ℝ) (max S 1) →
      Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α)
        (Work.FTS.Galerkin.slice (gn n) τ) :=
    fun n τ hτ => (hC n τ hτ).1
  have hXn : ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0:ℝ) (max S 1) →
      Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α) (Work.FTS.Galerkin.slice (gn n) τ)
        ≤ C₀ * (Work.FTS.Regularity.pExp α) ^ 2 :=
    fun n τ hτ => (hC n τ hτ).2.1
  have hXn6 : ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0:ℝ) (max S 1) →
      Work.FTS.StrongGlobal.Xn6 (Work.FTS.Regularity.pExp α)
        (Work.FTS.Galerkin.slice (gn n) τ) ≤ B :=
    fun n τ hτ => (hC n τ hτ).2.2
  obtain ⟨Cw, hCw0, hbdA⟩ := Work.FTS_RegExport.RXT.Sys.L12FKaux.approx_slot_bound
    (α := α) (C₀ := C₀) (gn := gn) (T := max S 1) hα hα13 hT hcl hXn
  obtain ⟨CB, hCB0, hCB⟩ := Work.FTS_RegExport.RXT.Sys.L12FKaux.ftau_slot_bound
    (α := α) (B := B) (gn := gn) (T := max S 1) hα hα13 hcl hXn6
  -- ## §2.2 the per-`τ` data
  have h4τ : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ n : ℕ,
      ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Galerkin.slice (gn n) τ))
        Work.FTS.EllipticEst.Q0 :=
    fun τ hτ n => (hC n τ (hmemT τ hτ)).1.reg.forall 4
  have hbdτ : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ (n k : ℕ), k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ →
      θ < Real.pi / 2 → |Work.Spaces.DzIter k (Work.FTS.Galerkin.slice (gn n) τ) z θ|
        ≤ Cw * SWq z :=
    fun τ hτ n k hk z θ hz h0 h1 => hbdA n τ (hmemT τ hτ) k hk z θ hz h0 h1
  have h2τ : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ n : ℕ,
      ContDiffOn ℝ 4 (Function.uncurry
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ))
        Work.FTS.EllipticEst.Q0 := by
    intro τ hτ n
    exact (Work.FTS_RegExport.RXT.Sys.L12FKaux.Fstar_contDiffOn hβ hβ1 4).add
      ((hC n τ (hmemT τ hτ)).1.reg.forall 4)
  have hslτ : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ (n k : ℕ), k ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ →
      θ < Real.pi / 2 → |Work.Spaces.DzIter k
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ) z θ| ≤ CB :=
    fun τ hτ n k hk z θ hz h0 h1 => hCB τ (hmemT τ hτ) n k hk z θ hz h0 h1
  have hconvτ : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n => Work.FTS.Galerkin.slice (gn n) τ z θ) Filter.atTop
        (𝓝 (Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.GR α g) τ z θ)) := by
    intro τ hτ z θ hzθ
    have h := hjet0 τ (hmemT τ hτ) 0 0 (by norm_num) z θ hzθ
    have hGr : Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.GR α g) τ z θ
        = Work.FTS.Galerkin.slice g τ z θ :=
      Work.FTS_RegExport.RXT.ftau_slice_GR_eq hτ.1 hzθ.1 hzθ.2.1.le hzθ.2.2.le
    rw [hGr]
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] using h
  have hjetτ : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ (k : ℕ), k ≤ 2 → ∀ z θ : ℝ,
      (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n => Work.Spaces.DzIter k (Work.FTS.Galerkin.slice (gn n) τ) z θ)
        Filter.atTop (𝓝 (Work.Spaces.DzIter k (Work.FTS.Galerkin.slice g τ) z θ)) :=
    fun τ hτ k hk z θ hzθ => by
      simpa only [Work.Spaces.mixed_zero_right] using
        hjet0 τ (hmemT τ hτ) k 0 (by omega) z θ hzθ
  -- ## §2.3 the jet package of `L₁₂`/`𝔽K` along the limit profile
  obtain ⟨C₁, hC₁0, hJ1, hJ2, hJ3, hJ4, hJ5⟩ :=
    Work.FTS_RegExport.RXT.Sys.L12FK_family_jets (α := α) (C₀ := C₀) (Φs := Φs) (E := E)
      (g := g) hα hα13 hOK.2 S hS
  -- ## §2.4 the weighted `τ`-modulus of the moments
  obtain ⟨CK, hCK0, hCK⟩ := Work.FTS_RegExport.RXT0.QlimTauLipW (α := α) (C₀ := C₀)
    (Φs := Φs) (E := E) (g := g) hα hα13 hOK.2 S hS
  -- ## §2.5 the identities of the `L₁₂`-jets
  have hL1' : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z : ℝ, 0 < z →
      Work.Elliptic.DzdIter 1 (fun z => Work.Construction.L12 (Fpr α g τ) z) z
        = -(Work.Construction.FK (Fpr α g τ) z) := by
    intro τ hτ z hz
    have h := hJ3 τ hτ z hz
    rw [Work.Elliptic.DzIter_rad (fun z => Work.Construction.L12 (Fpr α g τ) z) 1 z 0] at h
    exact h
  have hL2' : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z : ℝ, 0 < z →
      Work.Spaces.DzIter 2 (fun z (_ : ℝ) => Work.Construction.L12 (Fpr α g τ) z) z 0
        = -(Qlm α g τ 1 z) := by
    intro τ hτ z hz
    have h1e : ∀ᶠ w in 𝓝 z, Work.Elliptic.DzdIter 1
        (fun z => Work.Construction.L12 (Fpr α g τ) z) w
        = -(Work.Construction.FK (Fpr α g τ) w) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
      exact hL1' τ hτ w hw
    have hv : HasDerivAt (fun w => Work.Construction.FK (Fpr α g τ) w)
        (Qlm α g τ 1 z / z) z := by
      have h1 := Work.FTS_RegExport.RXT.Sys.L12FKaux.Qlim_hasDerivAt_1 (α := α) hα hα13
        (Cw := Cw) (CB := CB) hCw0 hCB0 (h4τ τ hτ) (hbdτ τ hτ) (h2τ τ hτ) (hslτ τ hτ)
        (hjetτ τ hτ) hz
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
      exact Work.FTS_RegExport.RXT.Sys.L12FKaux.Qlim_eq_FK hα hτ.1 hw
    have h2 := DzdIter_two_eq_neg_mul
      (u := fun z => Work.Construction.L12 (Fpr α g τ) z)
      (v := fun w => Work.Construction.FK (Fpr α g τ) w)
      (d := Qlm α g τ 1 z / z) h1e hv
    have h3 : -z * (Qlm α g τ 1 z / z) = -(Qlm α g τ 1 z) := by
      rw [neg_mul, mul_div_cancel₀ _ (ne_of_gt hz)]
    rw [Work.Elliptic.DzIter_rad (fun z => Work.Construction.L12 (Fpr α g τ) z) 2 z 0,
      h2, h3]
  -- ## §2.6 the identification of the `𝔽K`-jets
  have hKjet : ∀ (k : ℕ), k ≤ 2 → ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z : ℝ, 0 < z →
      Work.Spaces.DzIter k (fun z (_ : ℝ) => Work.Construction.FK (Fpr α g τ) z) z 0
        = Qlm α g τ k z :=
    fun k hk τ hτ z hz =>
      Work.FTS_RegExport.RXT.Sys.L12FKaux.FK_DzIter_eq (α := α) hα hα13 hτ.1 hCw0 hCB0
        (h4τ τ hτ) (hbdτ τ hτ) (h2τ τ hτ) (hslτ τ hτ) (hjetτ τ hτ) hz hk
  -- ## §2.7 joint continuity of the moments
  have hQlip : ∀ (k : ℕ), k ≤ 2 → ∀ z : ℝ, 0 < z →
      ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S,
      |Qlm α g τ k z - Qlm α g τ' k z| ≤ CK * |τ - τ'| := by
    intro k hk z hz τ hτ τ' hτ'
    have h := hCK k hk τ hτ τ' hτ' z hz
    have h2 : SWq z ≤ 1 := Work.FTS_RegExport.RXT.Sys.L12FKaux.SW_le_one hz
    have h3 : CK * SWq z * |τ - τ'| ≤ CK * |τ - τ'| := by
      calc CK * SWq z * |τ - τ'| ≤ CK * 1 * |τ - τ'| :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hCK0) (abs_nonneg _)
        _ = CK * |τ - τ'| := by ring
    exact le_trans h h3
  have hQslice : ∀ (k : ℕ), k ≤ 2 → ∀ τ ∈ Set.Icc (0:ℝ) S,
      ContinuousOn (fun z : ℝ => Qlm α g τ k z) (Set.Ioi 0) := by
    intro k hk τ hτ x hx
    have hx0 : 0 < x := hx
    obtain ⟨C, -, hbox⟩ := Work.FTS_RegExport.RXT0.QlimZLipBox (α := α) (C₀ := C₀)
      (Φs := Φs) (E := E) (g := g) hα hα13 hOK.2 S hS (x / 2) (2 * x)
      (by linarith) (by linarith)
    exact (continuousAt_of_lipschitz_Icc
      (a := x / 2) (b := 2 * x) (C := C)
      (fun x' hx' y hy => hbox k hk τ hτ x' hx' y hy)
      ⟨by linarith, by linarith⟩).continuousWithinAt
  have hQjoint : ∀ (k : ℕ), k ≤ 2 → ContinuousOn (fun p : ℝ × ℝ => Qlm α g p.2 k p.1)
      (Set.Ioi (0:ℝ) ×ˢ Set.Icc (0:ℝ) S) :=
    fun k hk => continuousOn_slab_of_lipschitz (S := S) (K := CK)
      (F := fun z τ => Qlm α g τ k z) hCK0 (hQlip k hk) (hQslice k hk)
  -- ## §2.8 joint continuity of `L₁₂(F_τ)`
  have hL12slice : ∀ τ ∈ Set.Icc (0:ℝ) S,
      ContinuousOn (fun z : ℝ => Work.Construction.L12 (Fpr α g τ) z) (Set.Ioi 0) := by
    intro τ hτ x hx
    exact (Work.FTS_RegExport.RXT.Sys.L12FKaux.L12_hasDerivAt (α := α) (Cw := Cw)
      hα hα13 hCw0 (h4τ τ hτ) (hbdτ τ hτ) (hconvτ τ hτ) hx).continuousAt.continuousWithinAt
  have hL12joint : ContinuousOn (fun p : ℝ × ℝ => Work.Construction.L12 (Fpr α g p.2) p.1)
      (Set.Ioi (0:ℝ) ×ˢ Set.Icc (0:ℝ) S) :=
    continuousOn_slab_of_lipschitz (S := S) (K := C₁)
      (F := fun z τ => Work.Construction.L12 (Fpr α g τ) z) hC₁0
      (fun z hz τ hτ τ' hτ' => hJ4 τ hτ τ' hτ' z hz) hL12slice
  -- ## §2.9 assembly
  constructor
  · interval_cases j
    · refine hL12joint.congr ?_
      rintro ⟨z, τ⟩ ⟨hz, hτ⟩
      simp only [Work.Spaces.DzIter_zero]
    · refine (hQjoint 0 (by norm_num)).neg.congr ?_
      rintro ⟨z, τ⟩ ⟨hz, hτ⟩
      show Work.Spaces.DzIter 1 (fun z (_ : ℝ) => Work.Construction.L12 (Fpr α g τ) z) z 0
        = -(Qlm α g τ 0 z)
      rw [hJ3 τ hτ z hz, Work.FTS_RegExport.RXT.Sys.L12FKaux.Qlim_eq_FK hα hτ.1 hz]
    · refine (hQjoint 1 (by norm_num)).neg.congr ?_
      rintro ⟨z, τ⟩ ⟨hz, hτ⟩
      exact hL2' τ hτ z hz
  · interval_cases j
    · refine (hQjoint 0 (by norm_num)).congr ?_
      rintro ⟨z, τ⟩ ⟨hz, hτ⟩
      exact hKjet 0 (by norm_num) τ hτ z hz
    · refine (hQjoint 1 (by norm_num)).congr ?_
      rintro ⟨z, τ⟩ ⟨hz, hτ⟩
      exact hKjet 1 (by norm_num) τ hτ z hz
    · refine (hQjoint 2 (by norm_num)).congr ?_
      rintro ⟨z, τ⟩ ⟨hz, hτ⟩
      exact hKjet 2 (by norm_num) τ hτ z hz

end

end Work.FTS_RegExport.RXT0.RXJets
