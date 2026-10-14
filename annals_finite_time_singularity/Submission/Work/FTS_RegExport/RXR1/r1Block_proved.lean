import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.RegPkgGal.R5Parts
import Submission.Work.FTS.StrongEps.SupPort.classC_sup_le
import Submission.Work.FTS_RegExport.RXB.l12_aux
import Submission.Work.FTS_RegExport.RXR1.classC_sub_hyp
import Submission.Work.FTS_RegExport.RXR1.mixed_abs_le_weighted
import Submission.Work.FTS_RegExport.RXR1.slice_deriv_equi
import Submission.Work.FTS_RegExport.RXR1.slice_diff_bound
import Submission.Work.FTS_RegExport.RXR1.slice_diff_weighted
import Submission.Work.FTS_RegExport.RXR5.Fstar_C1Jet
import Submission.Work.FTS_RegExport.RXT.omega_facts
import Submission.Work.FTS_RegExport.VPOpen
import Submission.Work.Stability.mul_rpow_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXR1

open Filter Set
open scoped Real Topology

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.FinalV2 (gS tauExt Sol DynOK' LimApprox)
open Work.FTS.RegPkgGal (St1Class R5Parts)
open Work.FTS.RegExportIface (psiR)
open Work.FTS.Regularity (pExp)

variable {α C₀ : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}

/-! ## §1 The sanitiser on the angular interval

Two elementary unfolding lemmas: at `z > 0` and `θ ∈ Iθ` the sanitiser `gS` is inert, and
on `τ ≥ 0` it agrees with `g` itself. -/

lemma gS_eq {α : ℝ} (h : Fam) {z θ τ : ℝ} (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    gS α h z θ τ = h z θ τ := by
  simp only [Work.FTS.FinalV2.gS, hz, ite_true, hθ.1, hθ.2, and_self]

lemma gS_tauExt_nonneg {α : ℝ} {h : Fam} {z θ τ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Work.Spaces.Iθ) (hτ : 0 ≤ τ) : gS α (tauExt h) z θ τ = h z θ τ := by
  rw [gS_eq (α := α) (tauExt h) hz hθ, Work.FTS.FinalV2.tauExt_of_nonneg h hτ]

/-! ## §2 The right-hand side at `τ = 0` is `C¹` in `z` (the interior case)

This is the analytic core of `R1Block.hd1`: for `θ ∈ (0,π/2)`, the map

  `z ↦ dynLin (pExp α) (gS α (tauExt g)) 0 z θ + dynRHS (pExp α) (psiR …) (gS α (tauExt g)) 0 z θ`

is `C¹` on `(0,∞)`.  The proof is the equi-`C¹` argument (`contDiffOn_one_of_equiC1`): the
difference quotients `Q_τ(z) = (g z θ τ - g z θ 0)/τ` are `C¹` in `z` (`c4`), converge pointwise
to the right-hand side (`R5Parts.h0`), and are equi-`C¹` on compact subsets because the
`ℋ⁴`-Lipschitz bound of the approximants (`LimApprox`) transfers, through the interior
`ℋ⁴ → L^∞` estimate, to the differences of the slices. -/

lemma rhs_c1_interior (hα : 0 < α) (hα1 : α ≤ 1) (hα13 : α ≤ 1 / 3)
    (hSol : Sol (pExp α) Φs E g) (hOK : DynOK' (pExp α) C₀ Φs E g)
    (hdat : ∃ L β : ℝ, 1 ≤ L ∧ ∀ z θ, g z θ 0 = Work.FTS.LocData6.locG6 (pExp α) L β z θ)
    (hSt1 : ∀ S > 0, St1Class α S (gS α (tauExt g)))
    (H5 : ∀ S > 0, R5Parts α S (gS α (tauExt g)) (psiR α Φs E (tauExt g)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ContDiffOn ℝ 1 (fun z : ℝ =>
        Work.FTS.Galerkin.dynLin (pExp α) (gS α (tauExt g)) 0 z θ
        + Work.FTS.Galerkin.dynRHS (pExp α) (psiR α Φs E (tauExt g)) (gS α (tauExt g)) 0 z θ)
      (Set.Ioi 0) := by
  obtain ⟨L, hL0, hNb, hEb⟩ :=
    slice_deriv_equi (α := pExp α) (C₀ := C₀) (Φs := Φs) (E := E) (g := g)
      (Work.FTS.Regularity.pExp_pos hα) (Work.FTS.Regularity.pExp_le_one hα13) hOK.2 hθ
  -- (b) `C¹` of each difference quotient
  have hsliceC : ∀ (τ' : ℝ), 0 ≤ τ' → ContDiffOn ℝ 4
      (fun z => slice g τ' z θ) (Set.Ioi 0) := by
    intro τ' hτ'
    have h := (hOK.1.1.c4) τ' hτ'
    have hmap : Set.MapsTo (fun z : ℝ => (z, θ)) (Set.Ioi 0) Work.FTS.EllipticEst.Q0 :=
      fun z hz => ⟨hz, hθ.1, hθ.2⟩
    have hlin : ContDiffOn ℝ 4 (fun z : ℝ => (z, θ)) (Set.Ioi 0) := by fun_prop
    refine (h.comp hlin hmap).congr ?_
    intro z hz
    rfl
  have hC1 : ∀ τ ∈ Set.Ioc (0:ℝ) 1, ContDiffOn ℝ 1
      (fun z => (gS α (tauExt g) z θ τ - gS α (tauExt g) z θ 0)/τ) (Set.Ioi 0) := by
    intro τ hτ
    have hτ0 : 0 < τ := hτ.1
    have hsum := (hsliceC τ hτ0.le).sub (hsliceC 0 le_rfl)
    have hdiv := hsum.div_const τ
    refine (hdiv.of_le (by norm_num)).congr ?_
    intro z hz
    rw [gS_tauExt_nonneg hz ⟨hθ.1.le, hθ.2.le⟩ hτ0.le,
      gS_tauExt_nonneg hz ⟨hθ.1.le, hθ.2.le⟩ le_rfl]
    rfl
  -- (c) the uniform bound on the derivative
  have hN : ∀ τ ∈ Set.Ioc (0:ℝ) 1, ∀ z ∈ Set.Ioi (0:ℝ),
      |deriv (fun z'' => (gS α (tauExt g) z'' θ τ - gS α (tauExt g) z'' θ 0)/τ) z|
        ≤ 10 / Real.sqrt (Work.Spaces.gam (pExp α) - 1) * L / z := by
    intro τ hτ z hz
    have hτ0 : 0 < τ := hτ.1
    have hcongr : (fun z'' => (gS α (tauExt g) z'' θ τ - gS α (tauExt g) z'' θ 0)/τ)
        =ᶠ[𝓝 z] (fun z'' => (slice g τ z'' θ - slice g 0 z'' θ)/τ) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with z'' hz''
      rw [gS_tauExt_nonneg hz'' ⟨hθ.1.le, hθ.2.le⟩ hτ0.le,
        gS_tauExt_nonneg hz'' ⟨hθ.1.le, hθ.2.le⟩ le_rfl]
      rfl
    rw [hcongr.deriv_eq]
    exact hNb τ hτ z hz
  have hE : ∀ τ ∈ Set.Ioc (0:ℝ) 1, ∀ z ∈ Set.Ioi (0:ℝ), ∀ z' ∈ Set.Ioi (0:ℝ),
      |deriv (fun z'' => (gS α (tauExt g) z'' θ τ - gS α (tauExt g) z'' θ 0)/τ) z
        - deriv (fun z'' => (gS α (tauExt g) z'' θ τ - gS α (tauExt g) z'' θ 0)/τ) z'|
      ≤ 2 * (10 / Real.sqrt (Work.Spaces.gam (pExp α) - 1)) * L * |1/z - 1/z'| := by
    intro τ hτ z hz z' hz'
    have hτ0 : 0 < τ := hτ.1
    have hcongr : (fun z'' => (gS α (tauExt g) z'' θ τ - gS α (tauExt g) z'' θ 0)/τ)
        =ᶠ[𝓝 z] (fun z'' => (slice g τ z'' θ - slice g 0 z'' θ)/τ) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with z'' hz''
      rw [gS_tauExt_nonneg hz'' ⟨hθ.1.le, hθ.2.le⟩ hτ0.le,
        gS_tauExt_nonneg hz'' ⟨hθ.1.le, hθ.2.le⟩ le_rfl]
      rfl
    have hcongr' : (fun z'' => (gS α (tauExt g) z'' θ τ - gS α (tauExt g) z'' θ 0)/τ)
        =ᶠ[𝓝 z'] (fun z'' => (slice g τ z'' θ - slice g 0 z'' θ)/τ) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz'] with z'' hz''
      rw [gS_tauExt_nonneg hz'' ⟨hθ.1.le, hθ.2.le⟩ hτ0.le,
        gS_tauExt_nonneg hz'' ⟨hθ.1.le, hθ.2.le⟩ le_rfl]
      rfl
    rw [hcongr.deriv_eq, hcongr'.deriv_eq]
    exact hEb τ hτ z hz z' hz'
  -- (d) pointwise convergence of the difference quotients
  have htend : ∀ z ∈ Set.Ioi (0:ℝ),
      Filter.Tendsto (fun τ => (gS α (tauExt g) z θ τ - gS α (tauExt g) z θ 0)/τ)
        (nhdsWithin 0 (Set.Ioi (0:ℝ)))
        (nhds (Work.FTS.Galerkin.dynLin (pExp α) (gS α (tauExt g)) 0 z θ
          + Work.FTS.Galerkin.dynRHS (pExp α) (psiR α Φs E (tauExt g)) (gS α (tauExt g)) 0 z θ)) := by
    intro z hz
    have h := ((H5 1 one_pos).h0 z θ hz (by exact ⟨hz, hθ⟩)).tendsto_slope_zero_right
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [zero_add, smul_eq_mul, inv_mul_eq_div]
  -- (e) differentiability of the limit
  have hdiff : DifferentiableOn ℝ (fun z : ℝ =>
      Work.FTS.Galerkin.dynLin (pExp α) (gS α (tauExt g)) 0 z θ
      + Work.FTS.Galerkin.dynRHS (pExp α) (psiR α Φs E (tauExt g)) (gS α (tauExt g)) 0 z θ)
      (Set.Ioi 0) := by
    intro z hz
    obtain ⟨NZ₁, -, hLz⟩ := (H5 1 one_pos).hLz
    obtain ⟨NZ₂, -, hN₀z⟩ := (H5 1 one_pos).hN₀z
    obtain ⟨NZ₃, -, hNz⟩ := (H5 1 one_pos).hNz
    obtain ⟨NZ₄, -, hNsz⟩ := (H5 1 one_pos).hNsz
    obtain ⟨Nc, hNc0, hder⟩ := Work.FTS.RegPkgGal.Der.rhs_zderiv_of_parts (α := α) (S := 1)
      hα hα13 one_pos hLz hN₀z hNz hNsz (H5 1 one_pos).hmb
    have hder0 := hder (0:ℝ) (by constructor <;> norm_num)
    obtain ⟨d, hd, -⟩ := hder0 θ ⟨hθ.1.le, hθ.2.le⟩ z hz
    exact hd.differentiableAt.differentiableWithinAt
  -- (f) the equi-`C¹` limit lemma
  have hNcont : ContinuousOn (fun z : ℝ => 10 / Real.sqrt (Work.Spaces.gam (pExp α) - 1) * L / z)
      (Set.Ioi 0) := by
    have h1 : ContinuousOn (fun z : ℝ => (10 / Real.sqrt (Work.Spaces.gam (pExp α) - 1) * L) / z)
        (Set.Ioi 0) :=
      ContinuousOn.div continuousOn_const continuousOn_id (fun z hz => ne_of_gt hz)
    exact h1
  have hEcont : ContinuousOn
      (fun p : ℝ × ℝ => 2 * (10 / Real.sqrt (Work.Spaces.gam (pExp α) - 1)) * L * |1/p.1 - 1/p.2|)
      (Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ)) := by
    have hdiv1 : ContinuousOn (fun p : ℝ × ℝ => 1/p.1) (Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ)) :=
      ContinuousOn.div continuousOn_const continuousOn_fst (fun p hp => ne_of_gt hp.1)
    have hdiv2 : ContinuousOn (fun p : ℝ × ℝ => 1/p.2) (Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ)) :=
      ContinuousOn.div continuousOn_const continuousOn_snd (fun p hp => ne_of_gt hp.2)
    exact continuousOn_const.mul ((hdiv1.sub hdiv2).abs)
  exact contDiffOn_one_of_equiC1
    (f := fun τ z => (gS α (tauExt g) z θ τ - gS α (tauExt g) z θ 0)/τ)
    (R := fun z : ℝ => Work.FTS.Galerkin.dynLin (pExp α) (gS α (tauExt g)) 0 z θ
      + Work.FTS.Galerkin.dynRHS (pExp α) (psiR α Φs E (tauExt g)) (gS α (tauExt g)) 0 z θ)
    (N := fun z : ℝ => 10 / Real.sqrt (Work.Spaces.gam (pExp α) - 1) * L / z)
    (E := fun z z' : ℝ => 2 * (10 / Real.sqrt (Work.Spaces.gam (pExp α) - 1)) * L * |1/z - 1/z'|)
    hNcont hC1 hN hEcont (by intro z hz; simp) hE htend hdiff

/-! ## §3 The right-hand side at `τ = 0` is `C¹` in `z`, for every `θ ∈ Iθ` -/

lemma rhs_c1 (hα : 0 < α) (hα1 : α ≤ 1) (hα13 : α ≤ 1 / 3)
    (hSol : Sol (pExp α) Φs E g) (hOK : DynOK' (pExp α) C₀ Φs E g)
    (hdat : ∃ L β : ℝ, 1 ≤ L ∧ ∀ z θ, g z θ 0 = Work.FTS.LocData6.locG6 (pExp α) L β z θ)
    (hSt1 : ∀ S > 0, St1Class α S (gS α (tauExt g)))
    (H5 : ∀ S > 0, R5Parts α S (gS α (tauExt g)) (psiR α Φs E (tauExt g))) :
    ∀ θ ∈ Work.Spaces.Iθ, ContDiffOn ℝ 1 (fun z : ℝ =>
        Work.FTS.Galerkin.dynLin (pExp α) (gS α (tauExt g)) 0 z θ
        + Work.FTS.Galerkin.dynRHS (pExp α) (psiR α Φs E (tauExt g)) (gS α (tauExt g)) 0 z θ)
      (Set.Ioi 0) := by
  intro θ hθ
  by_cases hθint : θ ∈ Set.Ioo 0 (π/2)
  · exact rhs_c1_interior hα hα1 hα13 hSol hOK hdat hSt1 H5 hθint
  · -- `θ = 0` or `θ = π/2`: the right-hand side vanishes identically
    have hθend : θ = 0 ∨ θ = π/2 := by
      rcases hθ with ⟨h0, h1⟩
      rcases lt_or_eq_of_le h0 with h | h
      · right
        rcases lt_or_eq_of_le h1 with h' | h'
        · exact absurd ⟨h, h'⟩ hθint
        · exact h'
      · left; exact h.symm
    have hzero : ∀ z : ℝ,
        Work.FTS.Galerkin.dynLin (pExp α) (gS α (tauExt g)) 0 z θ
          + Work.FTS.Galerkin.dynRHS (pExp α) (psiR α Φs E (tauExt g)) (gS α (tauExt g)) 0 z θ = 0 := by
      intro z
      have h01 : (0 : ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_refl 0, zero_le_one⟩
      rcases hθend with h | h
      · rw [h]; exact (H5 1 one_pos).hRθ0 0 h01 z
      · rw [h]; exact (H5 1 one_pos).hRθπ 0 h01 z
    rw [show (fun z : ℝ =>
        Work.FTS.Galerkin.dynLin (pExp α) (gS α (tauExt g)) 0 z θ
          + Work.FTS.Galerkin.dynRHS (pExp α) (psiR α Φs E (tauExt g)) (gS α (tauExt g)) 0 z θ)
        = fun _ => (0:ℝ) from funext hzero]
    exact contDiffOn_const

/-! ## §4 The `hd1` field: `C¹` of the `τ = 0` derivative in `z` -/

lemma hd1_all (hα : 0 < α) (hα1 : α ≤ 1) (hα13 : α ≤ 1 / 3)
    (hSol : Sol (pExp α) Φs E g) (hOK : DynOK' (pExp α) C₀ Φs E g)
    (hdat : ∃ L β : ℝ, 1 ≤ L ∧ ∀ z θ, g z θ 0 = Work.FTS.LocData6.locG6 (pExp α) L β z θ)
    (hSt1 : ∀ S > 0, St1Class α S (gS α (tauExt g)))
    (H5 : ∀ S > 0, R5Parts α S (gS α (tauExt g)) (psiR α Φs E (tauExt g))) :
    ∀ θ ∈ Work.Spaces.Iθ, ContDiffOn ℝ 1
      (fun q : ℝ × ℝ => deriv (fun s => gS α (tauExt g) q.1 θ s) 0)
      (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1))) := by
  intro θ hθ
  by_cases hθint : θ ∈ Set.Ioo 0 (π/2)
  · have hcore := rhs_c1_interior hα hα1 hα13 hSol hOK hdat hSt1 H5 hθint
    refine ((hcore.comp contDiffOn_fst (fun q hq => hq.1)).congr ?_)
    intro q hq
    have h0 := (H5 1 one_pos).h0 q.1 θ hq.1 (by exact ⟨hq.1, hθint⟩)
    exact h0.deriv
  · -- `θ = 0` or `θ = π/2`: the whole slice is identically `0`
    have hθend : θ = 0 ∨ θ = π/2 := by
      rcases hθ with ⟨h0, h1⟩
      rcases lt_or_eq_of_le h0 with h | h
      · right
        rcases lt_or_eq_of_le h1 with h' | h'
        · exact absurd ⟨h, h'⟩ hθint
        · exact h'
      · left; exact h.symm
    have hslice0 : ∀ z : ℝ, (fun s => gS α (tauExt g) z θ s) = fun _ => (0:ℝ) := by
      intro z
      funext s
      by_cases hz : 0 < z
      · rw [gS_eq (α := α) (tauExt g) hz hθ]
        by_cases hs : 0 ≤ s
        · rw [Work.FTS.FinalV2.tauExt_of_nonneg g hs]
          rcases hθend with h | h
          · rw [h]; exact (hOK.1.1.vanish s hs z hz.le).1
          · rw [h]; exact (hOK.1.1.vanish s hs z hz.le).2
        · have hvanish : ∀ y : ℝ, 0 ≤ y → g z θ y = 0 := by
            intro y hy
            rcases hθend with h | h
            · rw [h]; exact (hOK.1.1.vanish y hy z hz.le).1
            · rw [h]; exact (hOK.1.1.vanish y hy z hz.le).2
          have hdw : derivWithin (fun y => g z θ y) (Set.Ici 0) 0 = 0 := by
            have hc : HasDerivWithinAt (fun y => g z θ y) (0:ℝ) (Set.Ici 0) 0 :=
              (hasDerivWithinAt_const (0:ℝ) (Set.Ici 0) 0).congr (fun y hy => hvanish y hy)
                (hvanish 0 le_rfl)
            exact hc.derivWithin (uniqueDiffWithinAt_Ici 0)
          rw [Work.FTS.FinalV2.tauExt_of_neg g (lt_of_not_ge hs), hvanish 0 le_rfl, hdw,
            mul_zero, add_zero]
      · rw [Work.FTS.FinalV2.gS]; simp only [hz, ite_false]
    rw [show (fun q : ℝ × ℝ => deriv (fun s => gS α (tauExt g) q.1 θ s) 0)
        = fun _ => (0:ℝ) from funext (fun q => by rw [hslice0 q.1]; simp)]
    exact contDiffOn_const

/-! ## §5 The assembled producer -/

theorem r1Block_proved {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {g : Work.FTS.Galerkin.Fam} (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hdat : ∃ L β : ℝ, 1 ≤ L ∧ ∀ z θ,
      g z θ 0 = Work.FTS.LocData6.locG6 (Work.FTS.Regularity.pExp α) L β z θ)
    (hSt1 : ∀ S > 0,
      Work.FTS.RegPkgGal.St1Class α S (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)))
    (H5 : ∀ S > 0, Work.FTS.RegPkgGal.R5Parts α S
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))
      (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g))) :
    ∀ S > 0, Work.FTS.RegExportIface.R1Block α S
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) := by
  have hα1 : α ≤ 1 := by linarith
  -- the `hd1` field
  have hd1 := hd1_all hα hα1 hα13 hSol hOK hdat hSt1 H5
  -- the weighted difference bound, and the two limit fields
  have hw := slice_diff_weighted (β := pExp α) (C₀ := C₀) (Φs := Φs) (E := E) (g := g)
    (Work.FTS.Regularity.pExp_pos hα) (Work.FTS.Regularity.pExp_le_one hα13) hOK.2
    (mixed_abs_le_weighted (Work.FTS.Regularity.pExp_pos hα)
      (Work.FTS.Regularity.pExp_le_one hα13)) 1 one_pos
  have hd1z := hd1z_limit (α := α) (C₀ := C₀) (Φs := Φs) (E := E) (g := g) hα hα13 hOK H5 hw
  have hd1z2 := hd1z2_limit (α := α) (C₀ := C₀) (Φs := Φs) (E := E) (g := g) hα hα13 hOK H5 hw
  -- the `hbase` field and the two continuity clusters
  have hbase := hbase_gS (α := α) (C₀ := C₀) (Φs := Φs) (E := E) (g := g)
    hα hα13 hSol hOK hdat hSt1 H5 (rhs_c1 hα hα1 hα13 hSol hOK hdat hSt1 H5)
  have hj := hj_cluster (α := α) (C₀ := C₀) (Φs := Φs) (E := E) (g := g)
    hα hα13 hSol hOK hdat hSt1 H5
  have ht := tau_cluster (α := α) (C₀ := C₀) (Φs := Φs) (E := E) (g := g)
    hα hα13 hSol hOK hdat hSt1 H5
  intro S hS
  exact ⟨hbase, (hj S hS).1, (hj S hS).2.1, (hj S hS).2.2, (ht S hS).1, hd1, hd1z, hd1z2,
    (ht S hS).2⟩

end Work.FTS_RegExport.RXR1
