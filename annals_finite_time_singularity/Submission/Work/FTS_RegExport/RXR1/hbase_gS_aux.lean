import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.RegExportIface.Defs
import Submission.Work.FTS.RegPkgGal.R5Parts
import Submission.Work.FTS.StrongEps.SupPort.classC_sup_le
import Submission.Work.FTS.RegPkgGal.R1b.General
import Submission.Work.FTS.RegPkgGal.R1b.C1Facts
import Submission.Work.FTS.RegPkgGal.Der.rhs_jet_of_parts
import Submission.Work.FTS.RegPkgGal.Der.rhs_zderiv_of_parts
import Submission.Work.FTS.LocData6.Defs
import Submission.Work.FTS.LocData.SmoothQuad_locG
import Submission.Work.FTS.LocData.SmoothQuad_hLoc
import Submission.Work.FTS_RegExport.RXR1.ftc_slice
import Submission.Work.FTS_RegExport.RXR1.dz_tau_cont
import Submission.Work.FTS_RegExport.RXR1.oneSided_expansion

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXR1

open scoped Topology Real
open Set Filter MeasureTheory

/-!
# `Work.FTS_RegExport.RXR1.hbase_gS_aux` — the gluing machinery for `hbase_gS`

The joint `C¹` regularity of `(z,τ) ↦ gS α (tauExt g) z θ τ` on `z > 0, τ > -1`, at every fixed
angle `θ ∈ Iθ`.  This is the `hbase` field of the R1 block (`RegExportIface.R1Block`), one of the
inputs of the Galerkin→regularity assembly.

The proof: on `z > 0`, `θ ∈ Iθ` the sanitiser is transparent, so the function is the right-Taylor
extension `tauExt g`; for `τ ≥ 0` it is `g`, for `τ < 0` the affine jet
`g z θ 0 + τ · ∂_τ⁺g(z,θ,0)`.  The two branches are glued at `τ = 0` by the one-sided Taylor
expansion of `g` at `τ = 0⁺`, which is the fundamental theorem of calculus in `τ` together with
the `Jet` property of the equation's right-hand side (uniform in `(z,θ)`); the `τ = 0` slice is
the explicit datum `locG6`, and the continuity of the candidate derivative at `τ = 0` comes from
the uniform `z`-derivative bound of the right-hand side.  At `θ = 0, π/2` the function vanishes
identically. -/

/-- The right-hand side of the dynamic equation at the sanitised right-Taylor family. -/
noncomputable def hbgRHS (α : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn) (g : Work.FTS.Galerkin.Fam) :
    ℝ → ℝ → ℝ → ℝ :=
  fun z θ τ => Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α)
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ z θ
    + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α)
      (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g))
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ z θ

/-- `x ^ α` is arbitrarily small at small `x`, for `α > 0`. -/
lemma hbg_rpow_small {C α : ℝ} (hC : 0 ≤ C) (hα : 0 < α) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, C * δ ^ α < ε := by
  have hCp : (0:ℝ) < C + 1 := by linarith
  refine ⟨(ε / (C + 1)) ^ (1 / α), Real.rpow_pos_of_pos (by positivity) _, ?_⟩
  have hm : ((ε / (C + 1)) ^ (1 / α)) ^ α = ε / (C + 1) := by
    rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ ε / (C + 1))]
    have hone : 1 / α * α = 1 := by field_simp
    rw [hone, Real.rpow_one]
  rw [hm]
  rw [mul_div_assoc']
  rw [div_lt_iff₀ hCp]
  nlinarith

/-- A function that is `α`-Hölder on `[0,1]` is continuous there. -/
lemma hbg_contOn_of_holder {f : ℝ → ℝ} {C α : ℝ} (hC : 0 ≤ C) (hα : 0 < α)
    (h : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1, |f x - f y| ≤ C * |x - y| ^ α) :
    ContinuousOn f (Set.Icc (0:ℝ) 1) := by
  refine Metric.continuousOn_iff.2 fun b hb ε hε => ?_
  have hCp : (0:ℝ) < C + 1 := by linarith
  set δ : ℝ := min 1 ((ε / (C + 1)) ^ (1 / α)) with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    exact lt_min one_pos (Real.rpow_pos_of_pos (by positivity) _)
  refine ⟨δ, hδpos, fun a ha habs => ?_⟩
  have h1 : |f a - f b| ≤ C * |a - b| ^ α := h a ha b hb
  have h2 : |a - b| ≤ δ := by
    rw [Real.dist_eq] at habs
    exact le_of_lt habs
  have h3 : |a - b| ^ α ≤ δ ^ α := Real.rpow_le_rpow (abs_nonneg _) h2 hα.le
  have h4 : δ ^ α ≤ ε / (C + 1) := by
    rw [hδ]
    have hm : ((ε / (C + 1)) ^ (1 / α)) ^ α = ε / (C + 1) := by
      rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ ε / (C + 1))]
      have hone : 1 / α * α = 1 := by field_simp
      rw [hone, Real.rpow_one]
    calc (min 1 ((ε / (C + 1)) ^ (1 / α))) ^ α
        ≤ ((ε / (C + 1)) ^ (1 / α)) ^ α :=
          Real.rpow_le_rpow (le_min zero_le_one (by positivity)) (min_le_right _ _) hα.le
      _ = ε / (C + 1) := hm
  have h5 : C * δ ^ α < ε := by
    calc C * δ ^ α ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left h4 hC
      _ < ε := by
          rw [mul_div_assoc']
          rw [div_lt_iff₀ hCp]
          nlinarith
  rw [Real.dist_eq]
  exact lt_of_le_of_lt (le_trans h1 (mul_le_mul_of_nonneg_left h3 hC)) h5

/-- The `z`-slice of a `C¹` function on an open set is differentiable, with its `deriv`. -/
lemma hbg_hasDerivAt_slice_z {f : ℝ × ℝ → ℝ} {s : Set (ℝ × ℝ)} (hs : IsOpen s)
    (hf : ContDiffOn ℝ 1 f s) {z τ : ℝ} (h : (z, τ) ∈ s) :
    HasDerivAt (fun z' => f (z', τ)) (deriv (fun z' => f (z', τ)) z) z := by
  have hAt : HasFDerivAt f (fderiv ℝ f (z, τ)) (z, τ) :=
    Work.FTS.RegPkgGal.R1b.hasFDerivAt_of_contDiffOn_one hs hf h
  have hcurve : HasDerivAt (fun z' : ℝ => ((z', τ) : ℝ × ℝ)) ((1, 0) : ℝ × ℝ) z := by
    simpa using (hasDerivAt_id z).prodMk (hasDerivAt_const z τ)
  have hcomp := hAt.comp_hasDerivAt z hcurve
  have hval : (fderiv ℝ f (z, τ)) (1, 0) = deriv (fun z' => f (z', τ)) z := by
    rw [Work.FTS.RegPkgGal.R1b.fderiv_eq_partials hAt.differentiableAt]
    simp
  rwa [hval] at hcomp

/-- The `locG6` datum is smooth in `z` at every fixed interior angle. -/
lemma hbg_locG6_slice {α L β : ℝ} {θ : ℝ} (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2))
    (hα : 0 < α) (hα1 : α ≤ 1) :
    ContDiffOn ℝ 1 (fun z : ℝ => Work.FTS.LocData6.locG6 α L β z θ) (Set.Ioi 0) := by
  have hSQ : Work.FTS.LocData.SmoothQuad (Work.FTS.LocData6.locG6 α L β) :=
    Work.FTS.LocData.SmoothQuad_locG α L β hα hα1 (Work.FTS.LocData.SmoothQuad_hLoc α)
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z : ℝ => Work.FTS.LocData6.locG6 α L β z θ) (Set.Ioi (-1)) :=
    hSQ.curry_z hθ
  have h2 : ContDiffOn ℝ 1 (fun z : ℝ => Work.FTS.LocData6.locG6 α L β z θ) (Set.Ioi (-1)) :=
    h1.of_le (by simp [Work.Stability.smoothOrder])
  refine h2.mono (fun z hz => ?_)
  exact lt_trans (show (-1:ℝ) < 0 by norm_num) (show (0:ℝ) < z from hz)

/-- The sanitiser is transparent on the closed angular interval, at `z > 0`. -/
lemma hbg_gS_eq {α : ℝ} {h : Work.FTS.Galerkin.Fam} {z θ τ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) : Work.FTS.FinalV2.gS α h z θ τ = h z θ τ := by
  simp only [Work.FTS.FinalV2.gS, hz, hθ.1, hθ.2, and_self, ite_true]

/-- The equation's right-hand side is a `Jet` (uniformly bounded and `α`-Hölder). -/
theorem hbg_RHS_jet {α : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (H5 : ∀ S > 0, Work.FTS.RegPkgGal.R5Parts α S
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))
      (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g))) :
    ∃ Nc : ℝ, Work.FTS.Regularity.Jet α 1 Nc (fun z θ τ => hbgRHS α Φs E g z θ τ) := by
  obtain ⟨NJ, hL, hN0, hN, hNs⟩ := (H5 1 one_pos).hJ
  exact Work.FTS.RegPkgGal.Der.rhs_jet_of_parts (α := α) (S := 1)
    hα hα13 one_pos hL hN0 hN hNs (H5 1 one_pos).hmb (H5 1 one_pos).hmbh

/-- The right-hand side has a `z`-derivative bounded uniformly on the strip and in `θ`. -/
theorem hbg_RHS_zderiv {α : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (H5 : ∀ S > 0, Work.FTS.RegPkgGal.R5Parts α S
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))
      (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g))) :
    ∃ Nz : ℝ, 0 ≤ Nz ∧ ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ θ' ∈ Work.Spaces.Iθ,
      ∀ z' ∈ Set.Ioi (0:ℝ), ∃ d : ℝ,
        HasDerivAt (fun z'' => hbgRHS α Φs E g z'' θ' τ) d z' ∧ |d| ≤ Nz := by
  obtain ⟨N₁, hN₁, h1⟩ := (H5 1 one_pos).hLz
  obtain ⟨N₂, hN₂, h2⟩ := (H5 1 one_pos).hN₀z
  obtain ⟨N₃, hN₃, h3⟩ := (H5 1 one_pos).hNz
  obtain ⟨N₄, hN₄, h4⟩ := (H5 1 one_pos).hNsz
  exact Work.FTS.RegPkgGal.Der.rhs_zderiv_of_parts (α := α) (S := 1)
    hα hα13 one_pos h1 h2 h3 h4 (H5 1 one_pos).hmb

/-- **The `τ > 0` side of the junction**: the one-sided limit of the candidate derivative of the
`τ ≥ 0` branch as `(z,τ) → (z₀,0⁺)` is the jet's derivative at `(z₀,0)`. -/

lemma hbg_hcd {g R : ℝ → ℝ → ℝ → ℝ} {θ α Nc Nz : ℝ} (hα : 0 < α)
    (hθ : θ ∈ Work.Spaces.Iθ)
    (hloc : ContDiffOn ℝ 1 (fun z : ℝ => g z θ 0) (Set.Ioi 0))
    (hbc1 : ContDiffOn ℝ 1 (fun q : ℝ × ℝ => g q.1 θ q.2)
      (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (0:ℝ))))
    (hjc1 : ContDiffOn ℝ 1 (fun q : ℝ × ℝ => g q.1 θ 0 + q.2 * R q.1 θ 0)
      (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1:ℝ))))
    (hjet : Work.FTS.Regularity.Jet α 1 Nc R)
    (hNz0 : 0 ≤ Nz)
    (hE3 : ∀ z' ∈ Set.Ioi (0:ℝ), ∀ τ ∈ Set.Icc (0:ℝ) 1,
      |deriv (fun z'' => g z'' θ τ) z' - deriv (fun z'' => g z'' θ 0) z'| ≤ Nz * τ)
    (hRderiv : ∀ z ∈ Set.Ioi (0:ℝ), ∀ τ ∈ Set.Ioi (0:ℝ), deriv (fun s => g z θ s) τ = R z θ τ) :
    ∀ z ∈ Set.Ioi (0:ℝ), Filter.Tendsto
      (fun q : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => g q.1 θ q.2) q)
      (𝓝[Set.prod Set.univ (Set.Ioi (0:ℝ))] (z, 0))
      (𝓝 (fderiv ℝ (fun q : ℝ × ℝ => g q.1 θ 0 + q.2 * R q.1 θ 0) (z, 0))) := by
  intro z hz
  have hzpos : 0 < z := hz
  have hNc : 0 ≤ Nc := Work.FTS.Regularity.Jet.nonneg hjet
  have hVopen : IsOpen (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (0:ℝ))) := isOpen_Ioi.prod isOpen_Ioi
  have hUopen : IsOpen (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1:ℝ))) := isOpen_Ioi.prod isOpen_Ioi
  set L : (ℝ × ℝ) →L[ℝ] ℝ := deriv (fun z' : ℝ => g z' θ 0) z • ContinuousLinearMap.fst ℝ ℝ ℝ
      + R z θ 0 • ContinuousLinearMap.snd ℝ ℝ ℝ with hL
  have hjfd : fderiv ℝ (fun q : ℝ × ℝ => g q.1 θ 0 + q.2 * R q.1 θ 0) (z, (0:ℝ)) = L := by
    have hd : DifferentiableAt ℝ (fun q : ℝ × ℝ => g q.1 θ 0 + q.2 * R q.1 θ 0) (z, (0:ℝ)) :=
      (Work.FTS.RegPkgGal.R1b.hasFDerivAt_of_contDiffOn_one hUopen hjc1
        (show ((z, (0:ℝ)) : ℝ × ℝ) ∈ Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1:ℝ)) from
          ⟨hzpos, by norm_num⟩)).differentiableAt
    rw [Work.FTS.RegPkgGal.R1b.fderiv_eq_partials hd]
    have e1 : deriv (fun z' : ℝ => g z' θ 0 + (0:ℝ) * R z' θ 0) z
        = deriv (fun z' : ℝ => g z' θ 0) z :=
      Filter.EventuallyEq.deriv_eq (Filter.Eventually.of_forall (fun z' => by ring))
    have e2 : deriv (fun s : ℝ => g z θ 0 + s * R z θ 0) (0:ℝ) = R z θ 0 := by
      have hh : HasDerivAt (fun s : ℝ => g z θ 0 + id s * R z θ 0) (0 + 1 * R z θ 0) (0:ℝ) :=
        (hasDerivAt_const (0:ℝ) (g z θ 0)).add ((hasDerivAt_id (0:ℝ)).mul_const (R z θ 0))
      have hh2 : HasDerivAt (fun s : ℝ => g z θ 0 + s * R z θ 0) (R z θ 0) (0:ℝ) := by
        simpa using hh
      exact hh2.deriv
    rw [e1, e2]
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hε4 : 0 < ε / 4 := by linarith
  have hcont0 : ContinuousOn (fun z'' : ℝ => deriv (fun z' : ℝ => g z' θ 0) z'') (Set.Ioi 0) := by
    have h := hloc.continuousOn_fderiv_of_isOpen isOpen_Ioi (by norm_num)
    have h2 : ContinuousOn (fun x : ℝ => (fderiv ℝ (fun z' : ℝ => g z' θ 0) x) 1) (Set.Ioi 0) :=
      h.clm_apply (continuousOn_const (c := (1 : ℝ)))
    exact h2.congr (fun x hx => fderiv_apply_one_eq_deriv)
  obtain ⟨δ₁, hδ₁, h1⟩ := Metric.continuousOn_iff.1 hcont0 z hz (ε / 4) hε4
  have h2α : (0:ℝ) ≤ 2 ^ α := Real.rpow_nonneg (by norm_num) _
  obtain ⟨δ₂, hδ₂, h2⟩ := hbg_rpow_small (mul_nonneg hNc h2α) hα (ε := ε / 4) hε4
  have hNz1 : (0:ℝ) < Nz + 1 := by linarith
  refine ⟨min (min (min δ₁ δ₂) 1) (min (z / 2) (ε / (4 * (Nz + 1)))),
    lt_min (lt_min (lt_min hδ₁ hδ₂) one_pos) (lt_min (by linarith) (by positivity)), ?_⟩
  rintro ⟨q₁, q₂⟩ hqmem hqd
  have hq2pos : 0 < q₂ := hqmem.2
  have hnorm : ‖((q₁, q₂) : ℝ × ℝ) - (z, (0:ℝ))‖ = max |q₁ - z| |q₂| := by
    rw [Prod.norm_def]
    simp only [Real.norm_eq_abs, Prod.fst_sub, Prod.snd_sub, sub_zero]
  have hq2le : q₂ ≤ ‖((q₁, q₂) : ℝ × ℝ) - (z, (0:ℝ))‖ := by
    rw [hnorm]
    calc q₂ ≤ |q₂| := le_abs_self _
      _ ≤ max |q₁ - z| |q₂| := le_max_right _ _
  have hq1d : |q₁ - z| ≤ ‖((q₁, q₂) : ℝ × ℝ) - (z, (0:ℝ))‖ := by
    rw [hnorm]; exact le_max_left _ _
  have hdd : ‖((q₁, q₂) : ℝ × ℝ) - (z, (0:ℝ))‖ < min (min δ₁ δ₂) 1 :=
    lt_of_lt_of_le hqd (min_le_left _ _)
  have hδ₁le : ‖((q₁, q₂) : ℝ × ℝ) - (z, (0:ℝ))‖ < δ₁ :=
    lt_of_lt_of_le hdd (le_trans (min_le_left _ _) (min_le_left _ _))
  have hδ₂le : ‖((q₁, q₂) : ℝ × ℝ) - (z, (0:ℝ))‖ < δ₂ :=
    lt_of_lt_of_le hdd (le_trans (min_le_left _ _) (min_le_right _ _))
  have h1le : ‖((q₁, q₂) : ℝ × ℝ) - (z, (0:ℝ))‖ < 1 :=
    lt_of_lt_of_le hdd (min_le_right _ _)
  have hqd' : ‖((q₁, q₂) : ℝ × ℝ) - (z, (0:ℝ))‖ < min (z / 2) (ε / (4 * (Nz + 1))) :=
    lt_of_lt_of_le hqd (min_le_right _ _)
  have hz2 : ‖((q₁, q₂) : ℝ × ℝ) - (z, (0:ℝ))‖ < z / 2 :=
    lt_of_lt_of_le hqd' (min_le_left _ _)
  have hε' : ‖((q₁, q₂) : ℝ × ℝ) - (z, (0:ℝ))‖ < ε / (4 * (Nz + 1)) :=
    lt_of_lt_of_le hqd' (min_le_right _ _)
  have hq1pos : 0 < q₁ := by
    have h3 : |q₁ - z| < z / 2 := lt_of_le_of_lt hq1d hz2
    rw [abs_lt] at h3
    linarith [h3.1, hzpos]
  have hq2lt1 : q₂ < 1 := lt_of_le_of_lt hq2le h1le
  have hq2Icc : q₂ ∈ Set.Icc (0:ℝ) 1 := ⟨hq2pos.le, hq2lt1.le⟩
  rw [hjfd]
  have hbAt : HasFDerivAt (fun q : ℝ × ℝ => g q.1 θ q.2)
      (fderiv ℝ (fun q : ℝ × ℝ => g q.1 θ q.2) (q₁, q₂)) (q₁, q₂) :=
    Work.FTS.RegPkgGal.R1b.hasFDerivAt_of_contDiffOn_one hVopen hbc1 ⟨hq1pos, hq2pos⟩
  have hparts := Work.FTS.RegPkgGal.R1b.fderiv_eq_partials hbAt.differentiableAt
  have hbval : deriv (fun s : ℝ => g q₁ θ s) q₂ = R q₁ θ q₂ := hRderiv q₁ hq1pos q₂ hq2pos
  have hsub : fderiv ℝ (fun q : ℝ × ℝ => g q.1 θ q.2) (q₁, q₂) - L
      = (deriv (fun z' : ℝ => g z' θ q₂) q₁ - deriv (fun z' : ℝ => g z' θ 0) z)
          • ContinuousLinearMap.fst ℝ ℝ ℝ
        + (R q₁ θ q₂ - R z θ 0) • ContinuousLinearMap.snd ℝ ℝ ℝ := by
    rw [hparts, hL, hbval]
    module
  rw [dist_eq_norm, hsub]
  refine lt_of_le_of_lt (Work.FTS.RegPkgGal.R1b.norm_smul_fst_add_smul_snd_le _ _) ?_
  have hA : |deriv (fun z' : ℝ => g z' θ q₂) q₁ - deriv (fun z' : ℝ => g z' θ 0) z|
      ≤ Nz * q₂ + ε / 4 := by
    have e3 := hE3 q₁ hq1pos q₂ hq2Icc
    have e4 : |deriv (fun z' : ℝ => g z' θ 0) q₁ - deriv (fun z' : ℝ => g z' θ 0) z| < ε / 4 := by
      refine h1 q₁ hq1pos ?_
      rw [Real.dist_eq]
      exact lt_of_le_of_lt hq1d hδ₁le
    calc |deriv (fun z' : ℝ => g z' θ q₂) q₁ - deriv (fun z' : ℝ => g z' θ 0) z|
        ≤ |deriv (fun z' : ℝ => g z' θ q₂) q₁ - deriv (fun z' : ℝ => g z' θ 0) q₁|
          + |deriv (fun z' : ℝ => g z' θ 0) q₁ - deriv (fun z' : ℝ => g z' θ 0) z| :=
          abs_sub_le _ _ _
      _ ≤ Nz * q₂ + ε / 4 := add_le_add e3 (le_of_lt e4)
  have hB : |R q₁ θ q₂ - R z θ 0| < ε / 4 := by
    have hJ := hjet.2.2 q₁ z θ θ q₂ 0 hq1pos.le hzpos.le hθ hθ hq2Icc ⟨le_refl 0, zero_le_one⟩
    have hlt : |q₁ - z| + |θ - θ| + |q₂ - 0| ≤ 2 * ‖((q₁, q₂) : ℝ × ℝ) - (z, (0:ℝ))‖ := by
      rw [sub_self, abs_zero, add_zero, sub_zero, abs_of_pos hq2pos]
      nlinarith [hq1d, hq2le]
    have hpow : (|q₁ - z| + |θ - θ| + |q₂ - 0|) ^ α
        ≤ (2 * ‖((q₁, q₂) : ℝ × ℝ) - (z, (0:ℝ))‖) ^ α :=
      Real.rpow_le_rpow (by positivity) hlt hα.le
    have h2δ : (2 * ‖((q₁, q₂) : ℝ × ℝ) - (z, (0:ℝ))‖) ^ α ≤ (2 * δ₂) ^ α := by
      refine Real.rpow_le_rpow (by positivity) ?_ hα.le
      nlinarith [hδ₂le]
    have hfin : Nc * (2 * δ₂) ^ α < ε / 4 := by
      have h2αδ : (2 * δ₂) ^ α = 2 ^ α * δ₂ ^ α := Real.mul_rpow (by norm_num) hδ₂.le
      rw [h2αδ]
      calc Nc * (2 ^ α * δ₂ ^ α) = Nc * 2 ^ α * δ₂ ^ α := by ring
        _ < ε / 4 := h2
    calc |R q₁ θ q₂ - R z θ 0|
        ≤ Nc * (|q₁ - z| + |θ - θ| + |q₂ - 0|) ^ α := hJ
      _ ≤ Nc * (2 * ‖((q₁, q₂) : ℝ × ℝ) - (z, (0:ℝ))‖) ^ α :=
          mul_le_mul_of_nonneg_left hpow hNc
      _ ≤ Nc * (2 * δ₂) ^ α := mul_le_mul_of_nonneg_left h2δ hNc
      _ < ε / 4 := hfin
  have hA2 : Nz * q₂ ≤ ε / 4 := by
    have h1' : Nz * ‖((q₁, q₂) : ℝ × ℝ) - (z, (0:ℝ))‖ ≤ Nz * (ε / (4 * (Nz + 1))) :=
      mul_le_mul_of_nonneg_left hε'.le hNz0
    have h2' : Nz * (ε / (4 * (Nz + 1))) ≤ ε / 4 := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    exact le_trans (mul_le_mul_of_nonneg_left hq2le hNz0) (le_trans h1' h2')
  linarith [hA, hB, hA2]

/-- **The gluing of two half-plane branches along `τ = 0`.**  If `j` is `C¹` on
`{z > 0, τ > -1}`, `b` is `C¹` on `{z > 0, τ > 0}`, `G` agrees with `j` for `τ ≤ 0` and with `b`
for `τ ≥ 0`, the one-sided Taylor expansion of `b` at `τ = 0⁺` has derivative `fderiv j`, and
`fderiv b` tends to `fderiv j` along `τ → 0⁺`, then `G` is `C¹` on `{z > 0, τ > -1}`. -/
theorem hbg_glue
    {j b G : ℝ × ℝ → ℝ}
    (hj_c1 : ContDiffOn ℝ 1 j (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1:ℝ))))
    (hb_c1 : ContDiffOn ℝ 1 b (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (0:ℝ))))
    (hGj : ∀ q ∈ Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1:ℝ)), q.2 ≤ 0 → G q = j q)
    (hGb : ∀ q ∈ Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1:ℝ)), 0 ≤ q.2 → G q = b q)
    (hexp : ∀ z ∈ Set.Ioi (0:ℝ), ∀ ε > 0, ∃ δ > 0, ∀ y : ℝ × ℝ, ‖y - (z, (0:ℝ))‖ < δ → 0 ≤ y.2 →
      ‖b y - b (z, (0:ℝ)) - fderiv ℝ j (z, (0:ℝ)) (y - (z, (0:ℝ)))‖ ≤ ε * ‖y - (z, (0:ℝ))‖)
    (hcd : ∀ z ∈ Set.Ioi (0:ℝ), Filter.Tendsto (fun q : ℝ × ℝ => fderiv ℝ b q)
      (𝓝[Set.prod Set.univ (Set.Ioi (0:ℝ))] (z, 0)) (𝓝 (fderiv ℝ j (z, 0)))) :
    ContDiffOn ℝ 1 G (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1:ℝ))) := by
  have hUopen : IsOpen (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1:ℝ))) := isOpen_Ioi.prod isOpen_Ioi
  have hVopen : IsOpen (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (0:ℝ))) := isOpen_Ioi.prod isOpen_Ioi
  set Lc : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ :=
    fun q => if q.2 ≤ 0 then fderiv ℝ j q else fderiv ℝ b q with hLc
  have hjAt : ∀ q ∈ Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1:ℝ)), HasFDerivAt j (fderiv ℝ j q) q :=
    fun q hq => Work.FTS.RegPkgGal.R1b.hasFDerivAt_of_contDiffOn_one hUopen hj_c1 hq
  have hbAt : ∀ q ∈ Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (0:ℝ)), HasFDerivAt b (fderiv ℝ b q) q :=
    fun q hq => Work.FTS.RegPkgGal.R1b.hasFDerivAt_of_contDiffOn_one hVopen hb_c1 hq
  have hJcont : ContinuousOn (fun q : ℝ × ℝ => fderiv ℝ j q)
      (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1:ℝ))) :=
    hj_c1.continuousOn_fderiv_of_isOpen hUopen (by norm_num)
  have hBcont : ContinuousOn (fun q : ℝ × ℝ => fderiv ℝ b q)
      (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (0:ℝ))) :=
    hb_c1.continuousOn_fderiv_of_isOpen hVopen (by norm_num)
  have hjEqLc : ∀ q, q.2 ≤ 0 → Lc q = fderiv ℝ j q := by
    intro q hq; rw [hLc]; simp [hq]
  have hbEqLc : ∀ q, ¬ q.2 ≤ 0 → Lc q = fderiv ℝ b q := by
    intro q hq; rw [hLc]; simp [hq]
  have hLc_cont : ContinuousOn Lc (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1:ℝ))) := by
    rintro ⟨z, τ⟩ hx
    have hz : 0 < z := hx.1
    have hτm : -1 < τ := hx.2
    have hxU : (z, τ) ∈ Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1:ℝ)) := hx
    rcases lt_trichotomy τ 0 with h2 | h2 | h2
    · have heq : Lc =ᶠ[𝓝 ((z, τ) : ℝ × ℝ)] (fun q => fderiv ℝ j q) := by
        filter_upwards [(isOpen_Iio.preimage continuous_snd).mem_nhds h2] with q hq
        exact hjEqLc q (le_of_lt hq)
      exact ((hJcont.continuousAt (hUopen.mem_nhds hxU)).congr_of_eventuallyEq heq).continuousWithinAt
    · subst h2
      have hxU0 : (z, (0:ℝ)) ∈ Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1:ℝ)) := ⟨hz, by norm_num⟩
      refine ContinuousAt.continuousWithinAt ?_
      refine (Metric.tendsto_nhds).2 fun ε hε => ?_
      rw [hjEqLc (z, (0:ℝ)) le_rfl]
      have hjEv : ∀ᶠ q : ℝ × ℝ in 𝓝 (z, (0:ℝ)),
          dist (fderiv ℝ j q) (fderiv ℝ j (z, (0:ℝ))) < ε :=
        (Metric.tendsto_nhds).1 ((hJcont.continuousAt (hUopen.mem_nhds hxU0))) ε hε
      have hbEv : ∀ᶠ q : ℝ × ℝ in 𝓝 (z, (0:ℝ)), 0 < q.2 →
          dist (fderiv ℝ b q) (fderiv ℝ j (z, (0:ℝ))) < ε := by
        have h := (Metric.tendsto_nhds).1 (hcd z hz) ε hε
        rw [eventually_nhdsWithin_iff] at h
        exact h.mono (fun q hq hq2 => hq ⟨trivial, hq2⟩)
      filter_upwards [hjEv, hbEv] with q hqj hqb
      by_cases hk : 0 < q.2
      · rw [hbEqLc q (not_le.mpr hk)]
        exact hqb hk
      · rw [hjEqLc q (le_of_not_gt hk)]
        exact hqj
    · have hxV : (z, τ) ∈ Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (0:ℝ)) := ⟨hz, h2⟩
      have heq : Lc =ᶠ[𝓝 ((z, τ) : ℝ × ℝ)] (fun q => fderiv ℝ b q) := by
        filter_upwards [(isOpen_Ioi.preimage continuous_snd).mem_nhds h2] with q hq
        exact hbEqLc q (not_le.mpr hq)
      exact ((hBcont.continuousAt (hVopen.mem_nhds hxV)).congr_of_eventuallyEq heq).continuousWithinAt
  have hderiv : ∀ x ∈ Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1:ℝ)), HasFDerivAt G (Lc x) x := by
    rintro ⟨z, τ⟩ hx
    have hz : 0 < z := hx.1
    have hτm : -1 < τ := hx.2
    have hxU : (z, τ) ∈ Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1:ℝ)) := hx
    rcases lt_trichotomy τ 0 with h2 | h2 | h2
    · rw [hjEqLc _ (le_of_lt h2)]
      refine (hjAt (z, τ) hxU).congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_Ioi.preimage continuous_fst).mem_nhds hz,
        (isOpen_Iio.preimage continuous_snd).mem_nhds h2,
        (isOpen_Ioi.preimage continuous_snd).mem_nhds (show (-1:ℝ) < τ from hτm)] with q hq1 hq2 hq3
      exact hGj q ⟨hq1, hq3⟩ (le_of_lt hq2)
    · subst h2
      have hxU0 : (z, (0:ℝ)) ∈ Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1:ℝ)) := ⟨hz, by norm_num⟩
      rw [hjEqLc _ le_rfl]
      refine (hasFDerivAt_iff_isLittleO).2 ?_
      rw [Asymptotics.isLittleO_iff]
      intro c hc
      obtain ⟨δ, hδpos, hδ⟩ := hexp z hz (c / 2) (by positivity)
      have hjEv : ∀ᶠ y : ℝ × ℝ in 𝓝 (z, (0:ℝ)),
          ‖j y - j (z, (0:ℝ)) - fderiv ℝ j (z, (0:ℝ)) (y - (z, (0:ℝ)))‖
            ≤ (c / 2) * ‖y - (z, (0:ℝ))‖ := by
        have h := (hjAt (z, (0:ℝ)) hxU0).isLittleO
        rw [Asymptotics.isLittleO_iff] at h
        exact h (by positivity)
      filter_upwards [hjEv, Metric.ball_mem_nhds ((z, (0:ℝ)) : ℝ × ℝ) hδpos,
        (isOpen_Ioi.preimage continuous_fst).mem_nhds hz,
        (isOpen_Ioi.preimage continuous_snd).mem_nhds (show (-1:ℝ) < (0:ℝ) by norm_num)]
        with y hyj hyball hy1 hy3
      have hball' : ‖y - (z, (0:ℝ))‖ < δ := by
        simpa [Metric.mem_ball, dist_eq_norm] using hyball
      have hr : (0:ℝ) ≤ ‖y - (z, (0:ℝ))‖ := norm_nonneg _
      by_cases hk : 0 ≤ y.2
      · have hyU : y ∈ Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1:ℝ)) := ⟨hy1, hy3⟩
        have hGy : G y = b y := hGb y hyU hk
        have hGx : G (z, (0:ℝ)) = b (z, (0:ℝ)) := hGb _ hxU0 le_rfl
        rw [hGy, hGx]
        refine le_trans (hδ y hball' hk) ?_
        nlinarith [hr, hc]
      · have hk' : y.2 < 0 := lt_of_not_ge hk
        have hyU : y ∈ Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1:ℝ)) := ⟨hy1, hy3⟩
        have hGy : G y = j y := hGj y hyU (le_of_lt hk')
        have hGx : G (z, (0:ℝ)) = j (z, (0:ℝ)) := hGj _ hxU0 le_rfl
        rw [hGy, hGx]
        refine le_trans hyj ?_
        nlinarith [hr, hc]
    · rw [hbEqLc _ (not_le.mpr h2)]
      refine (hbAt (z, τ) ⟨hz, h2⟩).congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_Ioi.preimage continuous_fst).mem_nhds hz,
        (isOpen_Ioi.preimage continuous_snd).mem_nhds h2,
        (isOpen_Ioi.preimage continuous_snd).mem_nhds (show (-1:ℝ) < τ from hτm)]
        with q hq1 hq2 hq3
      exact hGb q ⟨hq1, hq3⟩ (le_of_lt hq2)
  rw [show (1 : WithTop ℕ∞) = (0 : WithTop ℕ∞) + 1 from rfl]
  refine (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hUopen.uniqueDiffOn).2
    ⟨?_, Lc, ?_, ?_⟩
  · intro h; exact absurd h (by simp)
  · exact contDiffOn_zero.mpr hLc_cont
  · intro x hx; exact (hderiv x hx).hasFDerivWithinAt

end Work.FTS_RegExport.RXR1
