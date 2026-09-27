import Mathlib
import Submission.Work.Noncompact.CompressionTube.Notation
import Submission.Work.Noncompact.CompressionTube.collar_defs
import Submission.Work.Noncompact.CompressionTube.smooth_left_inverse_tools
import Submission.Work.Noncompact.CompressionTube.isLocalDiffeomorph_of_immersion
import Submission.Work.Noncompact.CompressionTube.ctc.exists_local_transverse_piece
import Submission.Work.Noncompact.CompressionTube.ctc.transverse_open
import Submission.Work.Noncompact.CompressionTube.ctc.exists_transverse_blend
import Submission.Work.Noncompact.CompressionTube.ctc.exists_gauge
import Submission.Work.Noncompact.CompressionTube.ctc.exists_transverse_on_Icc
import Submission.Work.Compat.MFDerivCongrV433

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


/-!
# The ray version of the transverse-coordinate chapter

This file ports the first half of `Work.Noncompact.CompressionTube` to a *ray*: instead of a smooth
proper embedded line `γ : ℝ → M` with a height function `g` satisfying `g (γ s) = s` for *all*
`s : ℝ`, we consider a smooth curve `ρ : ℝ → M` which is only required to be injective, proper and
an immersion *on* `[0, ∞)`, together with `g` satisfying `g (ρ t) = t` for `t ≥ 0`.

The bundle `RayData` collects exactly these hypotheses.  The contents of this file are the
`[0, ∞)`-analogues of `Transverse`'s basic lemmas (`collar_defs`), of `exists_local_transverse_piece`,
`transverse_open`, `exists_gauge` and `exists_transverse_blend`.
-/

namespace Work.Drive.RayTube

open scoped Manifold ContDiff
open Topology Set Function
open Work.Noncompact.CompressionTube

noncomputable section

/-- The data of a smooth, properly embedded ray `ρ` together with the height function `g`. -/
structure RayData (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M] where
  ρ : ℝ → M
  hρ : ContMDiff MCreal (MC n) smoothOrder ρ
  hinj : Set.InjOn ρ (Set.Ici (0:ℝ))
  hprop : IsProperMap (fun t : Set.Ici (0:ℝ) => ρ t)
  himm : ∀ t : ℝ, 0 ≤ t → Function.Injective (mfderiv MCreal (MC n) ρ t)
  g : M → ℝ
  hg : ContMDiff (MC n) MCreal smoothOrder g
  hgc : ∀ t : ℝ, 0 ≤ t → g (ρ t) = t

/-! ## Two elementary tools -/

/-- **A function which is constant on a right-neighbourhood of `0` has vanishing derivative at
`0`.**  (This is the endpoint case that does *not* follow from `EventuallyEq` of germs, and it is
why the ray chapter needs one extra argument that the line chapter does not.) -/
theorem fderiv_apply_one_eq_zero_of_eventuallyEq_const {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : ℝ → E} (hF : DifferentiableAt ℝ F 0)
    (hconst : ∀ᶠ u in 𝓝[>] (0:ℝ), F u = F 0) :
    fderiv ℝ F 0 (1 : ℝ) = 0 := by
  have h1 : Filter.Tendsto (fun h : ℝ => ‖h - 0‖⁻¹ * ‖F h - F 0 - fderiv ℝ F 0 (h - 0)‖)
      (𝓝 (0:ℝ)) (𝓝 (0:ℝ)) :=
    (hasFDerivAt_iff_tendsto (f' := fderiv ℝ F 0)).mp hF.hasFDerivAt
  have h1' : Filter.Tendsto (fun h : ℝ => ‖h - 0‖⁻¹ * ‖F h - F 0 - fderiv ℝ F 0 (h - 0)‖)
      (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) := h1.mono_left nhdsWithin_le_nhds
  have h2 : Filter.Tendsto (fun h : ℝ => ‖h - 0‖⁻¹ * ‖F h - F 0 - fderiv ℝ F 0 (h - 0)‖)
      (𝓝[>] (0:ℝ)) (𝓝 ‖fderiv ℝ F 0 (1 : ℝ)‖) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin, hconst] with h hh hFh
    have hh0 : (0:ℝ) < h := hh
    have hne : h ≠ 0 := ne_of_gt hh0
    have hLh : (fderiv ℝ F 0) h = h • (fderiv ℝ F 0) (1:ℝ) := by
      have h1 : (fderiv ℝ F 0) (h • (1:ℝ)) = h • (fderiv ℝ F 0) (1:ℝ) :=
        ContinuousLinearMap.map_smul (fderiv ℝ F 0) h (1:ℝ)
      rwa [smul_eq_mul, mul_one] at h1
    rw [sub_zero, hFh, sub_self, zero_sub, norm_neg, hLh, norm_smul,
      Real.norm_of_nonneg hh0.le, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  have hzero : (0:ℝ) = ‖fderiv ℝ F 0 (1 : ℝ)‖ := tendsto_nhds_unique h1' h2
  exact norm_eq_zero.mp hzero.symm

set_option backward.isDefEq.respectTransparency false in
/-- **The derivative of the height in the direction of the ray velocity is `1`.**  Ray version of
`Work.Noncompact.CompressionTube.mfderiv_g_velocity`. -/
theorem ray_mfderiv_g_velocity {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    {ρ : ℝ → M} {g : M → ℝ} (hgc : ∀ s : ℝ, 0 ≤ s → g (ρ s) = s)
    (hρ : ContMDiff MCreal (MC n) smoothOrder ρ) (hg : ContMDiff (MC n) MCreal smoothOrder g)
    {s : ℝ} (hs : 0 ≤ s) :
    mfderiv (MC n) MCreal g (ρ s) (mfderiv MCreal (MC n) ρ s 1) = 1 := by
  have hn : smoothOrder ≠ (0 : WithTop ℕ∞) := by simp [smoothOrder]
  have hρd : MDifferentiableAt MCreal (MC n) ρ s := hρ.mdifferentiableAt (x := s) hn
  have hgd : MDifferentiableAt (MC n) MCreal g (ρ s) := hg.mdifferentiableAt (x := ρ s) hn
  have hcomp : mfderiv MCreal MCreal (fun t : ℝ => g (ρ t)) s =
      (mfderiv (MC n) MCreal g (ρ s)).comp (mfderiv MCreal (MC n) ρ s) :=
    mfderiv_comp (I := MCreal) (I' := MC n) (I'' := MCreal) (f := ρ) (g := g) s hgd hρd
  have key : (mfderiv MCreal MCreal (fun t : ℝ => g (ρ t)) s) (1:ℝ) = 1 := by
    rcases eq_or_lt_of_le hs with h0 | hpos
    · subst h0
      have hGsm : ContMDiff MCreal MCreal smoothOrder (fun u : ℝ => g (ρ u) - u) :=
        (hg.comp hρ).sub (contMDiff_id (I := MCreal) (n := smoothOrder))
      have hGd : DifferentiableAt ℝ (fun u : ℝ => g (ρ u) - u) 0 :=
        ((hGsm 0).mdifferentiableAt hn).differentiableAt
      have hGconst : ∀ᶠ u in 𝓝[>] (0:ℝ),
          (fun u : ℝ => g (ρ u) - u) u = (fun u : ℝ => g (ρ u) - u) 0 := by
        filter_upwards [self_mem_nhdsWithin] with u hu
        have hu0 : (0:ℝ) ≤ u := le_of_lt hu
        rw [hgc u hu0, hgc 0 le_rfl]
        ring
      have hGder : (fderiv ℝ (fun u : ℝ => g (ρ u) - u) 0) (1:ℝ) = 0 :=
        fderiv_apply_one_eq_zero_of_eventuallyEq_const hGd hGconst
      have hGderiv : deriv (fun u : ℝ => g (ρ u) - u) 0 = 0 := by
        rw [← fderiv_apply_one_eq_deriv]
        exact hGder
      have hFsm : ContMDiff MCreal MCreal smoothOrder (fun u : ℝ => g (ρ u)) := hg.comp hρ
      have hid : DifferentiableAt ℝ (fun u : ℝ => u) 0 := differentiableAt_id
      have hid_deriv : deriv (fun u : ℝ => u) 0 = 1 := by
        have h : (fun u : ℝ => u) = id := rfl
        rw [h, deriv_id]
      have hsplit : (fun u : ℝ => g (ρ u)) =
          (fun u : ℝ => g (ρ u) - u) + (fun u : ℝ => u) := by
        funext u
        simp only [Pi.add_apply]
        ring
      have hderiv : deriv (fun u : ℝ => g (ρ u)) 0 = 1 := by
        rw [hsplit, deriv_add hGd hid, hGderiv, hid_deriv]
        ring
      rw [show (mfderiv MCreal MCreal (fun t : ℝ => g (ρ t)) 0) (1:ℝ)
            = (fderiv ℝ (fun t : ℝ => g (ρ t)) 0) (1:ℝ) from
          congrArg (fun (L : ℝ →L[ℝ] ℝ) => L 1)
            (mfderiv_eq_fderiv (f := fun t : ℝ => g (ρ t)) (x := 0))]
      rw [fderiv_apply_one_eq_deriv]
      exact hderiv
    · have heq : (fun u : ℝ => g (ρ u)) =ᶠ[𝓝 s] id := by
        filter_upwards [isOpen_Ioi.mem_nhds hpos] with u hu
        exact hgc u (le_of_lt hu)
      rw [Filter.EventuallyEq.mfderiv_eq_v433 heq, mfderiv_id]
      rfl
  have h1 : (mfderiv (MC n) MCreal g (ρ s)) ((mfderiv MCreal (MC n) ρ s) 1)
      = (mfderiv MCreal MCreal (fun t : ℝ => g (ρ t)) s) 1 := by
    rw [← ContinuousLinearMap.comp_apply, ← hcomp]
  rw [h1, key]

set_option backward.isDefEq.respectTransparency false in
/-- **A function vanishing on the ray has derivative killing the ray velocity.**  Ray version of
`Work.Noncompact.CompressionTube.mfderiv_velocity_eq_zero`. -/
theorem ray_mfderiv_velocity_eq_zero {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    {ρ : ℝ → M} {ψ : M → EuclideanSpace ℝ (Fin (n - 1))}
    (hρ : ContMDiff MCreal (MC n) smoothOrder ρ)
    (hψ : ContMDiff (MC n) (MC (n - 1)) smoothOrder ψ) (h0 : ∀ s : ℝ, 0 ≤ s → ψ (ρ s) = 0)
    {s : ℝ} (hs : 0 ≤ s) :
    mfderiv (MC n) (MC (n - 1)) ψ (ρ s) (mfderiv MCreal (MC n) ρ s 1) = 0 := by
  have hn : smoothOrder ≠ (0 : WithTop ℕ∞) := by simp [smoothOrder]
  have hρd : MDifferentiableAt MCreal (MC n) ρ s := hρ.mdifferentiableAt (x := s) hn
  have hψd : MDifferentiableAt (MC n) (MC (n - 1)) ψ (ρ s) := hψ.mdifferentiableAt (x := ρ s) hn
  have hcomp : mfderiv MCreal (MC (n - 1)) (fun t : ℝ => ψ (ρ t)) s =
      (mfderiv (MC n) (MC (n - 1)) ψ (ρ s)).comp (mfderiv MCreal (MC n) ρ s) :=
    mfderiv_comp (I := MCreal) (I' := MC n) (I'' := MC (n - 1)) (f := ρ) (g := ψ) s hψd hρd
  have key : (mfderiv MCreal (MC (n - 1)) (fun t : ℝ => ψ (ρ t)) s) (1:ℝ) = 0 := by
    rcases eq_or_lt_of_le hs with h0' | hpos
    · subst h0'
      have hsm : ContMDiff MCreal (MC (n - 1)) smoothOrder (fun u : ℝ => ψ (ρ u)) := hψ.comp hρ
      have hd : DifferentiableAt ℝ (fun u : ℝ => ψ (ρ u)) 0 :=
        ((hsm 0).mdifferentiableAt hn).differentiableAt
      have hconst : ∀ᶠ u in 𝓝[>] (0:ℝ),
          (fun u : ℝ => ψ (ρ u)) u = (fun u : ℝ => ψ (ρ u)) 0 := by
        filter_upwards [self_mem_nhdsWithin] with u hu
        have hu0 : (0:ℝ) ≤ u := le_of_lt hu
        rw [h0 u hu0, h0 0 le_rfl]
      rw [show (mfderiv MCreal (MC (n - 1)) (fun t : ℝ => ψ (ρ t)) 0) (1:ℝ)
            = (fderiv ℝ (fun t : ℝ => ψ (ρ t)) 0) (1:ℝ) from
          congrArg (fun (L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin (n - 1))) => L 1)
            (mfderiv_eq_fderiv (f := fun t : ℝ => ψ (ρ t)) (x := 0))]
      exact fderiv_apply_one_eq_zero_of_eventuallyEq_const hd hconst
    · have heq : (fun t : ℝ => ψ (ρ t)) =ᶠ[𝓝 s]
          (fun _ => (0 : EuclideanSpace ℝ (Fin (n - 1)))) := by
        filter_upwards [isOpen_Ioi.mem_nhds hpos] with u hu
        exact h0 u (le_of_lt hu)
      rw [Filter.EventuallyEq.mfderiv_eq_v433 heq, mfderiv_const, ContinuousLinearMap.zero_apply]
  have h1 : (mfderiv (MC n) (MC (n - 1)) ψ (ρ s)) ((mfderiv MCreal (MC n) ρ s) 1)
      = (mfderiv MCreal (MC (n - 1)) (fun t : ℝ => ψ (ρ t)) s) 1 := by
    rw [← ContinuousLinearMap.comp_apply, ← hcomp]
  rw [h1, key]

set_option backward.isDefEq.respectTransparency false in
/-- **The matching criterion.**  Ray version of
`Work.Noncompact.CompressionTube.eq_of_agree_on_ker`. -/
theorem ray_eq_of_agree_on_ker {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    {ρ : ℝ → M} {g : M → ℝ} (hgc : ∀ s : ℝ, 0 ≤ s → g (ρ s) = s)
    (hρ : ContMDiff MCreal (MC n) smoothOrder ρ) (hg : ContMDiff (MC n) MCreal smoothOrder g)
    {s : ℝ} (hs : 0 ≤ s)
    {L₁ L₂ : TangentSpace (MC n) (ρ s) →L[ℝ] EuclideanSpace ℝ (Fin (n - 1))}
    (h₁ : L₁ (mfderiv MCreal (MC n) ρ s 1) = 0) (h₂ : L₂ (mfderiv MCreal (MC n) ρ s 1) = 0)
    (h : ∀ v : TangentSpace (MC n) (ρ s), mfderiv (MC n) MCreal g (ρ s) v = 0 → L₁ v = L₂ v) :
    L₁ = L₂ := by
  ext v
  set c : ℝ := (mfderiv (MC n) MCreal g (ρ s) v : ℝ) with hc
  have hv : mfderiv (MC n) MCreal g (ρ s)
      (v - c • (mfderiv MCreal (MC n) ρ s 1)) = 0 := by
    rw [map_sub, map_smul, ray_mfderiv_g_velocity hgc hρ hg hs, hc, smul_eq_mul, mul_one, sub_self]
  have hkey := h _ hv
  have hdecomp : v = (v - c • (mfderiv MCreal (MC n) ρ s 1)) +
      c • (mfderiv MCreal (MC n) ρ s 1) := by abel
  conv_lhs => rw [hdecomp]
  conv_rhs => rw [hdecomp]
  rw [map_add, map_add, map_smul, map_smul, h₁, h₂, hkey]

/-! ## The local transverse piece along the ray -/

set_option backward.isDefEq.respectTransparency false in
/-- **A local transverse piece along the ray.**  Ray version of
`Work.Noncompact.CompressionTube.exists_local_transverse_piece`: for every `t₀ ≥ 0` there is a
globally smooth `ψ : M → ℝ^{n-1}` vanishing on the ray and transverse to `g` at `ρ t₀`. -/
theorem ray_local_transverse_piece {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    [T2Space M] [SecondCountableTopology M] (D : RayData n M) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) :
    ∃ ψ : M → EuclideanSpace ℝ (Fin (n - 1)),
      ContMDiff (MC n) (MC (n - 1)) smoothOrder ψ ∧
      (∀ t : ℝ, 0 ≤ t → ψ (D.ρ t) = 0) ∧ Transverse D.ρ D.g ψ t₀ := by
  classical
  have hn0 : smoothOrder ≠ 0 := by simp [smoothOrder]
  -- the chart at `ρ t₀` and its (injective) derivative
  set c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    chartAt (EuclideanSpace ℝ (Fin n)) (D.ρ t₀) with hcdef
  have hc : c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M :=
    IsManifold.chart_mem_maximalAtlas (D.ρ t₀)
  have hcsrc : D.ρ t₀ ∈ c.source := mem_chart_source _ (D.ρ t₀)
  set T : TangentSpace (MC n) (D.ρ t₀) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    mfderiv (MC n) (MC n) (fun x : M => c x) (D.ρ t₀) with hTdef
  have hTinj : Function.Injective T := by
    rw [hTdef]
    exact isLocalDiffeomorphAt_chart_mfderiv_injective hc hcsrc
  have hvelne : mfderiv MCreal (MC n) D.ρ t₀ (1 : ℝ) ≠ 0 := by
    intro hzero
    have h1 : (1 : ℝ) = 0 := by
      have h2 := ray_mfderiv_g_velocity D.hgc D.hρ D.hg ht₀
      rw [hzero, map_zero] at h2
      exact h2.symm
    exact one_ne_zero h1
  set vH : EuclideanSpace ℝ (Fin n) := T (mfderiv MCreal (MC n) D.ρ t₀ 1) with hvHdef
  have hvHne : vH ≠ 0 := by
    rw [hvHdef]
    intro hzero
    refine hvelne (hTinj ?_)
    rw [hzero, map_zero]
  obtain ⟨H, hH⟩ := exists_coord_proj_kernel (n := n) (by omega) vH hvHne
  -- the ingredients of the transverse function
  set Q : M → EuclideanSpace ℝ (Fin (n - 1)) := fun x => H (c x) with hQdef
  set hh : M → M := fun x => D.ρ (D.g x) with hhdef
  set ψ₀ : M → EuclideanSpace ℝ (Fin (n - 1)) := fun x => Q x - Q (hh x) with hψ₀def
  set W : Set M := c.source ∩ hh ⁻¹' c.source with hWdef
  have hhh_cont : Continuous hh := by
    rw [hhdef]
    exact D.hρ.continuous.comp D.hg.continuous
  have hWopen : IsOpen W := by
    rw [hWdef]
    exact c.open_source.inter (hhh_cont.isOpen_preimage c.source c.open_source)
  have hWs : D.ρ t₀ ∈ W := by
    refine ⟨hcsrc, ?_⟩
    rw [hhdef]
    show D.ρ (D.g (D.ρ t₀)) ∈ c.source
    rw [D.hgc t₀ ht₀]
    exact hcsrc
  obtain ⟨β, hβsm, _hβ01, hβone, hβsupp⟩ :=
    exists_contMDiff_bump_between (n := n) (K := {D.ρ t₀}) (W := W) isCompact_singleton hWopen
      (by simpa using hWs)
  have hβeq : β =ᶠ[𝓝 (D.ρ t₀)] (fun _ => (1 : ℝ)) := by
    have hS : {x : M | β x = 1} ∈ 𝓝 (D.ρ t₀) :=
      Filter.mem_of_superset (isOpen_interior.mem_nhds (hβone (by simp))) interior_subset
    filter_upwards [hS] with x hx
    exact hx
  set ψ : M → EuclideanSpace ℝ (Fin (n - 1)) := fun x => β x • ψ₀ x with hψdef
  -- smoothness of `ψ₀` on `W`
  have hψ₀smOn : ContMDiffOn (MC n) (MC (n - 1)) smoothOrder ψ₀ W := by
    have h1 : ContMDiffOn (MC n) (MC (n - 1)) smoothOrder Q W := by
      rw [hQdef]
      exact H.contMDiff.comp_contMDiffOn
        ((contMDiffOn_of_mem_maximalAtlas hc).mono (fun x hx => (hWdef ▸ hx).1))
    have h2 : ContMDiffOn (MC n) (MC (n - 1)) smoothOrder (fun x => Q (hh x)) W := by
      rw [hQdef]
      refine H.contMDiff.comp_contMDiffOn ?_
      rw [hhdef]
      exact (contMDiffOn_of_mem_maximalAtlas hc).comp (D.hρ.comp D.hg).contMDiffOn
        (fun x hx => (hWdef ▸ hx).2)
    rw [hψ₀def]
    exact h1.sub h2
  -- global smoothness of `ψ`
  have hψsm : ContMDiff (MC n) (MC (n - 1)) smoothOrder ψ := by
    rw [hψdef]
    exact contMDiff_smul_of_tsupport_subset hWopen hβsm hβsupp hψ₀smOn
  -- `ψ` vanishes on the ray
  have hψcore : ∀ t : ℝ, 0 ≤ t → ψ (D.ρ t) = 0 := by
    intro t ht
    have hzero : ψ₀ (D.ρ t) = 0 := by
      rw [hψ₀def, hhdef]
      simp [D.hgc t ht]
    rw [hψdef]
    simp only []
    rw [hzero, smul_zero]
  -- the derivative of `ψ₀` at `ρ t₀`
  set dh : TangentSpace (MC n) (D.ρ t₀) →L[ℝ] TangentSpace (MC n) (D.ρ t₀) :=
    (mfderiv MCreal (MC n) D.ρ t₀) ∘L (mfderiv (MC n) MCreal D.g (D.ρ t₀)) with hdhdef
  have hhmem : hh (D.ρ t₀) ∈ c.source := by
    rw [hhdef]
    show D.ρ (D.g (D.ρ t₀)) ∈ c.source
    rw [D.hgc t₀ ht₀]
    exact hcsrc
  have hhhderiv : HasMFDerivAt (MC n) (MC n) hh (D.ρ t₀) dh := by
    have hrd : HasMFDerivAt MCreal (MC n) D.ρ (D.g (D.ρ t₀))
        (mfderiv MCreal (MC n) D.ρ (D.g (D.ρ t₀))) :=
      (D.hρ.mdifferentiableAt (x := D.g (D.ρ t₀)) hn0).hasMFDerivAt
    have hgd : HasMFDerivAt (MC n) MCreal D.g (D.ρ t₀)
        (mfderiv (MC n) MCreal D.g (D.ρ t₀)) :=
      (D.hg.mdifferentiableAt (x := D.ρ t₀) hn0).hasMFDerivAt
    have h := hrd.comp (D.ρ t₀) hgd
    rw [mfderiv_congr_point (f := D.ρ) (D.hgc t₀ ht₀)] at h
    rw [hdhdef]
    simpa only [hhdef, Function.comp_def] using h
  have hc_diff : MDifferentiableAt (MC n) (MC n) (fun x : M => c x) (hh (D.ρ t₀)) :=
    ((contMDiffOn_of_mem_maximalAtlas hc).contMDiffAt
      (c.open_source.mem_nhds hhmem)).mdifferentiableAt hn0
  have hQ' : HasMFDerivAt (MC n) (MC (n - 1)) Q (hh (D.ρ t₀)) (H ∘L T) := by
    rw [hQdef]
    have h := (ContinuousLinearMap.hasMFDerivAt H).comp (hh (D.ρ t₀)) hc_diff.hasMFDerivAt
    have hpoint : hh (D.ρ t₀) = D.ρ t₀ := by
      rw [hhdef]
      show D.ρ (D.g (D.ρ t₀)) = D.ρ t₀
      rw [D.hgc t₀ ht₀]
    have hmf : mfderiv (MC n) (MC n) (fun x : M => c x) (hh (D.ρ t₀))
        = mfderiv (MC n) (MC n) (fun x : M => c x) (D.ρ t₀) :=
      mfderiv_congr_point hpoint
    rw [hmf] at h
    rw [hTdef]
    simpa only [Function.comp_def] using h
  have hQderiv : HasMFDerivAt (MC n) (MC (n - 1)) Q (D.ρ t₀) (H ∘L T) := by
    rw [hQdef, hTdef]
    have hcd : MDifferentiableAt (MC n) (MC n) (fun x : M => c x) (D.ρ t₀) :=
      ((contMDiffOn_of_mem_maximalAtlas hc).contMDiffAt
        (c.open_source.mem_nhds hcsrc)).mdifferentiableAt hn0
    exact (ContinuousLinearMap.hasMFDerivAt H).comp (D.ρ t₀) hcd.hasMFDerivAt
  have hQhh : HasMFDerivAt (MC n) (MC (n - 1)) (fun x : M => Q (hh x)) (D.ρ t₀)
      ((H ∘L T) ∘L dh) := by
    have h := hQ'.comp (D.ρ t₀) hhhderiv
    simpa only [Function.comp_def] using h
  have hψ₀deriv : HasMFDerivAt (MC n) (MC (n - 1)) ψ₀ (D.ρ t₀)
      ((H ∘L T) - ((H ∘L T) ∘L dh)) := hQderiv.sub hQhh
  have hψeq : ψ =ᶠ[𝓝 (D.ρ t₀)] ψ₀ := by
    rw [hψdef]
    filter_upwards [hβeq] with x hx
    rw [hx, one_smul]
  refine ⟨ψ, hψsm, hψcore, ?_⟩
  -- transversality at `t₀`
  intro v h1 h2
  have hmfd : mfderiv (MC n) (MC (n - 1)) ψ (D.ρ t₀) = (H ∘L T) - ((H ∘L T) ∘L dh) := by
    rw [Filter.EventuallyEq.mfderiv_eq_v433 hψeq, HasMFDerivAt.mfderiv hψ₀deriv]
  have h3 : H (T v) - H (T (dh v)) = 0 := by
    have h4 : ((H ∘L T) - ((H ∘L T) ∘L dh)) v = 0 := by
      rw [← hmfd]
      exact h1
    simpa only [sub_apply, ContinuousLinearMap.comp_apply] using h4
  have hdhv : dh v = mfderiv MCreal (MC n) D.ρ t₀
      (mfderiv (MC n) MCreal D.g (D.ρ t₀) v) := by
    rw [hdhdef]
    exact ContinuousLinearMap.comp_apply _ _ _
  have hz : mfderiv MCreal (MC n) D.ρ t₀ (mfderiv (MC n) MCreal D.g (D.ρ t₀) v) = 0 := by
    rw [h2]
    exact map_zero (mfderiv MCreal (MC n) D.ρ t₀)
  have hTdh : T (dh v) = 0 := by
    rw [hdhv]
    exact (congrArg T hz).trans (map_zero T)
  have h4 : H (T v) = 0 := by
    rw [hTdh] at h3
    simpa using h3
  obtain ⟨a, ha⟩ := (hH (T v)).mp h4
  have hv : v = a • (mfderiv MCreal (MC n) D.ρ t₀ 1) := by
    refine hTinj ?_
    rw [map_smul, ← hvHdef, ← ha]
  have hdg : mfderiv (MC n) MCreal D.g (D.ρ t₀) (a • mfderiv MCreal (MC n) D.ρ t₀ 1) = a := by
    rw [map_smul, ray_mfderiv_g_velocity D.hgc D.hρ D.hg ht₀, smul_eq_mul, mul_one]
  have ha0 : a = 0 := by
    have h5 := h2
    rw [hv] at h5
    rw [hdg] at h5
    exact h5
  rw [ha0, zero_smul] at hv
  exact hv

set_option backward.isDefEq.respectTransparency false in
/-- **Transversality along the ray is open in the parameter.**  Ray version of
`Work.Noncompact.CompressionTube.transverse_open`. -/
theorem ray_transverse_open {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    [T2Space M] [SecondCountableTopology M] (D : RayData n M)
    {ψ : M → EuclideanSpace ℝ (Fin (n - 1))}
    (hψ : ContMDiff (MC n) (MC (n - 1)) smoothOrder ψ)
    (h0 : ∀ s : ℝ, 0 ≤ s → ψ (D.ρ s) = 0) {t₀ : ℝ} (ht₀ : 0 ≤ t₀)
    (hs : Transverse D.ρ D.g ψ t₀) :
    ∃ r : ℝ, 0 < r ∧ ∀ s : ℝ, 0 ≤ s → |s - t₀| < r → Transverse D.ρ D.g ψ s := by
  classical
  have hn0 : smoothOrder ≠ (0 : WithTop ℕ∞) := by simp [smoothOrder]
  -- the chart at the base point
  let c := chartAt (EuclideanSpace ℝ (Fin n)) (D.ρ t₀)
  have hcm : c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M :=
    IsManifold.chart_mem_maximalAtlas (D.ρ t₀)
  have hcs : D.ρ t₀ ∈ c.source := mem_chart_source _ (D.ρ t₀)
  have hct : c (D.ρ t₀) ∈ c.target := c.map_source hcs
  have hct' : c (D.ρ t₀) ∈ c.symm.source := by
    rwa [OpenPartialHomeomorph.symm_source]
  have hmd : c.MDifferentiable (MC n) (MC n) :=
    mdifferentiable_of_mem_atlas (chart_mem_atlas _ _)
  -- the coordinate expression of `(ψ, D.g)`
  set F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n - 1)) × ℝ :=
    fun y => (ψ (c.symm y), D.g (c.symm y)) with hF
  have hsymm : ContMDiffAt (MC n) (MC n) smoothOrder
      (c.symm : EuclideanSpace ℝ (Fin n) → M) (c (D.ρ t₀)) :=
    contMDiffAt_symm_of_mem_maximalAtlas hcm hct
  have hFdiff : ContDiffAt ℝ smoothOrder F (c (D.ρ t₀)) := by
    have h1 : ContMDiffAt (MC n) (MC (n - 1)) smoothOrder
        (fun y => ψ (c.symm y)) (c (D.ρ t₀)) :=
      (hψ.contMDiffAt (x := c.symm (c (D.ρ t₀)))).comp (c (D.ρ t₀)) hsymm
    have h2 : ContMDiffAt (MC n) MCreal smoothOrder
        (fun y => D.g (c.symm y)) (c (D.ρ t₀)) :=
      (D.hg.contMDiffAt (x := c.symm (c (D.ρ t₀)))).comp (c (D.ρ t₀)) hsymm
    rw [hF]
    exact h1.contDiffAt.prodMk h2.contDiffAt
  -- the derivative of `F` at the base point is injective
  have hbase : c.symm (c (D.ρ t₀)) = D.ρ t₀ := c.left_inv hcs
  have hFind : Function.Injective (fderiv ℝ F (c (D.ρ t₀))) := by
    have hd : fderiv ℝ F (c (D.ρ t₀)) =
        ((mfderiv (MC n) (MC (n - 1)) ψ (D.ρ t₀)).prod
            (mfderiv (MC n) MCreal D.g (D.ρ t₀))).comp
          (mfderiv (MC n) (MC n) (c.symm : EuclideanSpace ℝ (Fin n) → M) (c (D.ρ t₀))) := by
      have h := (hasFDerivAt_coord_pair hψ D.hg hcm hct).fderiv
      rw [hbase] at h
      exact h
    rw [hd]
    have hP : Function.Injective ((mfderiv (MC n) (MC (n - 1)) ψ (D.ρ t₀)).prod
        (mfderiv (MC n) MCreal D.g (D.ρ t₀))) := by
      intro a b hab
      have h0 : ((mfderiv (MC n) (MC (n - 1)) ψ (D.ρ t₀)).prod
          (mfderiv (MC n) MCreal D.g (D.ρ t₀))) (a - b) = 0 := by
        rw [map_sub, sub_eq_zero.mpr hab]
      have h1 : mfderiv (MC n) (MC (n - 1)) ψ (D.ρ t₀) (a - b) = 0 := by
        have h := congrArg Prod.fst h0
        simpa [ContinuousLinearMap.prod_apply] using h
      have h2 : mfderiv (MC n) MCreal D.g (D.ρ t₀) (a - b) = 0 := by
        have h := congrArg Prod.snd h0
        simpa [ContinuousLinearMap.prod_apply] using h
      exact sub_eq_zero.mp (hs _ h1 h2)
    have hS : Function.Injective
        (mfderiv (MC n) (MC n) (c.symm : EuclideanSpace ℝ (Fin n) → M) (c (D.ρ t₀))) :=
      (hmd.symm.mfderiv hct').injective
    intro a b hab
    exact hS (hP hab)
  -- the open set where the derivative of `F` stays injective
  obtain ⟨W, hWopen, hWmem, hWsub⟩ :=
    exists_open_injective_fderiv (finrank_euclideanSpace_prod (by omega)) hFdiff hn0 hFind
  -- a parameter interval mapping into it
  have hcontγ : ContinuousAt D.ρ t₀ := D.hρ.continuous.continuousAt
  have hcontc : ContinuousAt c (D.ρ t₀) := c.continuousAt hcs
  have hpre : D.ρ ⁻¹' (c.source ∩ c ⁻¹' W) ∈ 𝓝 t₀ := by
    rw [preimage_inter]
    exact Filter.inter_mem (hcontγ.preimage_mem_nhds (c.open_source.mem_nhds hcs))
      (hcontγ.preimage_mem_nhds (hcontc.preimage_mem_nhds (hWopen.mem_nhds hWmem)))
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨ε, hεpos, fun s _ hs' => ?_⟩
  have hsball : s ∈ Metric.ball t₀ ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    exact hs'
  obtain ⟨hxsrc, hcxW⟩ := hεsub hsball
  have hcxt : c (D.ρ s) ∈ c.target := c.map_source hxsrc
  have hleft : c.symm (c (D.ρ s)) = D.ρ s := c.left_inv hxsrc
  -- the derivatives at `D.ρ s`, with concrete types
  let A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n - 1)) :=
    mfderiv (MC n) (MC (n - 1)) ψ (D.ρ s)
  let B : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := mfderiv (MC n) MCreal D.g (D.ρ s)
  let Se : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    mfderiv (MC n) (MC n) (c.symm : EuclideanSpace ℝ (Fin n) → M) (c (D.ρ s))
  let Ce : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    mfderiv (MC n) (MC n) (c : M → EuclideanSpace ℝ (Fin n)) (D.ρ s)
  have hSeCe : Se.comp Ce = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) :=
    hmd.symm_comp_deriv hxsrc
  have hderiv : fderiv ℝ F (c (D.ρ s)) = (A.prod B).comp Se := by
    have h := (hasFDerivAt_coord_pair hψ D.hg hcm hcxt).fderiv
    rw [hleft] at h
    exact h
  have hderiv_inj : Function.Injective ((A.prod B).comp Se) := by
    rw [← hderiv]
    exact hWsub _ hcxW
  -- conclude
  intro v hv1 hv2
  have hv0 : (A.prod B) v = 0 := by
    rw [ContinuousLinearMap.prod_apply]
    exact Prod.ext hv1 hv2
  have hval : Se (Ce v) = v := by
    have h1 := congrArg
      (fun (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) => L v) hSeCe
    simpa [ContinuousLinearMap.comp_apply] using h1
  have hkey : ((A.prod B).comp Se) (Ce v) = 0 := by
    rw [ContinuousLinearMap.comp_apply, hval, hv0]
  have hzero : Ce v = 0 := hderiv_inj (by simpa using hkey)
  calc v = Se (Ce v) := hval.symm
    _ = Se 0 := by rw [hzero]
    _ = 0 := map_zero Se


set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
/-- **Blending two transverse functions along the ray.**  Ray version of
`Work.Noncompact.CompressionTube.exists_transverse_blend`. -/
theorem ray_blend {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    [T2Space M] [SecondCountableTopology M] (D : RayData n M)
    {G₁ G₂ : M → EuclideanSpace ℝ (Fin (n - 1))}
    (hG₁ : ContMDiff (MC n) (MC (n - 1)) smoothOrder G₁)
    (hG₂ : ContMDiff (MC n) (MC (n - 1)) smoothOrder G₂)
    (hv₁ : ∀ s : ℝ, 0 ≤ s → G₁ (D.ρ s) = 0) (hv₂ : ∀ s : ℝ, 0 ≤ s → G₂ (D.ρ s) = 0)
    {s₁ : ℝ} (hs₁ : 0 ≤ s₁)
    (hagree : mfderiv (MC n) (MC (n - 1)) G₁ (D.ρ s₁)
      = mfderiv (MC n) (MC (n - 1)) G₂ (D.ρ s₁))
    (htrans : Transverse D.ρ D.g G₁ s₁) :
    ∃ r : ℝ, 0 < r ∧ ∀ (χ : ℝ → ℝ), ContDiff ℝ smoothOrder χ →
      (∀ t : ℝ, χ t ∈ Set.Icc 0 1) → ∀ s : ℝ, 0 ≤ s → |s - s₁| < r →
        Transverse D.ρ D.g
          (fun x : M => χ (D.g x) • G₁ x + (1 - χ (D.g x)) • G₂ x) s := by
  classical
  have hn0 : smoothOrder ≠ (0 : WithTop ℕ∞) := by simp [smoothOrder]
  -- the chart at `D.ρ s₁`
  set c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    chartAt (EuclideanSpace ℝ (Fin n)) (D.ρ s₁) with hcdef
  have hcm : c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M :=
    IsManifold.chart_mem_maximalAtlas (D.ρ s₁)
  have hmd : c.MDifferentiable (MC n) (MC n) := mdifferentiable_chart (D.ρ s₁)
  have hcsrc : D.ρ s₁ ∈ c.source := mem_chart_source _ (D.ρ s₁)
  have hy₁t : c (D.ρ s₁) ∈ c.target := c.map_source hcsrc
  have hy₁t' : c (D.ρ s₁) ∈ c.symm.source := by rwa [OpenPartialHomeomorph.symm_source]
  -- the coordinate expressions of `G₁`, `G₂`, `D.g`
  set A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n - 1)) :=
    fun y => G₁ (c.symm y) with hAdef
  set B : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n - 1)) :=
    fun y => G₂ (c.symm y) with hBdef
  set Γ : EuclideanSpace ℝ (Fin n) → ℝ := fun y => D.g (c.symm y) with hΓdef
  -- the manifold derivatives at the base point, with concrete types
  let Se₁ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    mfderiv (MC n) (MC n) (c.symm : EuclideanSpace ℝ (Fin n) → M) (c (D.ρ s₁))
  let L₁ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n - 1)) :=
    mfderiv (MC n) (MC (n - 1)) G₁ (D.ρ s₁)
  let L₂ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n - 1)) :=
    mfderiv (MC n) (MC (n - 1)) G₂ (D.ρ s₁)
  let Lg₁ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := mfderiv (MC n) MCreal D.g (D.ρ s₁)
  have hSeInj : Function.Injective Se₁ := (hmd.symm.mfderiv hy₁t').injective
  have hAder : fderiv ℝ A (c (D.ρ s₁)) = L₁.comp Se₁ := by
    have h := (hasFDerivAt_coord (n := n) hG₁ hcm hy₁t).fderiv
    rw [c.left_inv hcsrc] at h
    rw [hAdef]
    exact h
  have hBder : fderiv ℝ B (c (D.ρ s₁)) = L₂.comp Se₁ := by
    have h := (hasFDerivAt_coord (n := n) hG₂ hcm hy₁t).fderiv
    rw [c.left_inv hcsrc] at h
    rw [hBdef]
    exact h
  have hΓder : fderiv ℝ Γ (c (D.ρ s₁)) = Lg₁.comp Se₁ := by
    have h := (hasFDerivAt_coord (n := n) D.hg hcm hy₁t).fderiv
    rw [c.left_inv hcsrc] at h
    rw [hΓdef]
    exact h
  -- the transversality hypothesis at the base point, in coordinates
  have hL12 : L₁ = L₂ := hagree
  have hBA : fderiv ℝ B (c (D.ρ s₁)) = fderiv ℝ A (c (D.ρ s₁)) := by
    rw [hBder, hAder, hL12]
  have hbase : ∀ δ : EuclideanSpace ℝ (Fin n),
      fderiv ℝ Γ (c (D.ρ s₁)) δ = 0 → fderiv ℝ A (c (D.ρ s₁)) δ = 0 → δ = 0 := by
    intro δ h1 h2
    rw [hΓder] at h1
    rw [hAder] at h2
    change Lg₁ (Se₁ δ) = 0 at h1
    change L₁ (Se₁ δ) = 0 at h2
    have h3 : Se₁ δ = 0 := htrans (Se₁ δ) h2 h1
    exact hSeInj (by rw [h3, map_zero])
  haveI : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
    haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    infer_instance
  obtain ⟨ε, hεpos, hεprop⟩ :=
    exists_uniform_blend_injective (fderiv ℝ A (c (D.ρ s₁))) (fderiv ℝ Γ (c (D.ρ s₁))) hbase
  -- continuity of the derivative of the coordinate expressions
  have hsymmb : ContMDiffAt (MC n) (MC n) smoothOrder
      (c.symm : EuclideanSpace ℝ (Fin n) → M) (c (D.ρ s₁)) :=
    contMDiffAt_symm_of_mem_maximalAtlas hcm hy₁t
  have hAcd : ContDiffAt ℝ smoothOrder A (c (D.ρ s₁)) := by
    have h1 : ContMDiffAt (MC n) (MC (n - 1)) smoothOrder
        (fun y => G₁ (c.symm y)) (c (D.ρ s₁)) :=
      (hG₁.contMDiffAt (x := c.symm (c (D.ρ s₁)))).comp (c (D.ρ s₁)) hsymmb
    rw [hAdef]
    exact h1.contDiffAt
  have hBcd : ContDiffAt ℝ smoothOrder B (c (D.ρ s₁)) := by
    have h1 : ContMDiffAt (MC n) (MC (n - 1)) smoothOrder
        (fun y => G₂ (c.symm y)) (c (D.ρ s₁)) :=
      (hG₂.contMDiffAt (x := c.symm (c (D.ρ s₁)))).comp (c (D.ρ s₁)) hsymmb
    rw [hBdef]
    exact h1.contDiffAt
  have hΓcd : ContDiffAt ℝ smoothOrder Γ (c (D.ρ s₁)) := by
    have h1 : ContMDiffAt (MC n) MCreal smoothOrder
        (fun y => D.g (c.symm y)) (c (D.ρ s₁)) :=
      (D.hg.contMDiffAt (x := c.symm (c (D.ρ s₁)))).comp (c (D.ρ s₁)) hsymmb
    rw [hΓdef]
    exact h1.contDiffAt
  have hAcont : ContinuousAt (fderiv ℝ A) (c (D.ρ s₁)) := hAcd.continuousAt_fderiv hn0
  have hBcont : ContinuousAt (fderiv ℝ B) (c (D.ρ s₁)) := hBcd.continuousAt_fderiv hn0
  have hΓcont : ContinuousAt (fderiv ℝ Γ) (c (D.ρ s₁)) := hΓcd.continuousAt_fderiv hn0
  -- a neighbourhood of the base point on which all the blends are injective
  have hnhds : ∀ᶠ y in 𝓝 (c (D.ρ s₁)),
      ‖fderiv ℝ A y - fderiv ℝ A (c (D.ρ s₁))‖ < ε ∧
      ‖fderiv ℝ B y - fderiv ℝ A (c (D.ρ s₁))‖ < ε ∧
      ‖fderiv ℝ Γ y - fderiv ℝ Γ (c (D.ρ s₁))‖ < ε := by
    have h1 : ∀ᶠ y in 𝓝 (c (D.ρ s₁)), ‖fderiv ℝ A y - fderiv ℝ A (c (D.ρ s₁))‖ < ε := by
      have hb := hAcont.preimage_mem_nhds (Metric.ball_mem_nhds (fderiv ℝ A (c (D.ρ s₁))) hεpos)
      filter_upwards [hb] with y hy
      rwa [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at hy
    have h2 : ∀ᶠ y in 𝓝 (c (D.ρ s₁)), ‖fderiv ℝ B y - fderiv ℝ A (c (D.ρ s₁))‖ < ε := by
      have hb := hBcont.preimage_mem_nhds (Metric.ball_mem_nhds (fderiv ℝ B (c (D.ρ s₁))) hεpos)
      filter_upwards [hb] with y hy
      rwa [Set.mem_preimage, Metric.mem_ball, dist_eq_norm, hBA] at hy
    have h3 : ∀ᶠ y in 𝓝 (c (D.ρ s₁)), ‖fderiv ℝ Γ y - fderiv ℝ Γ (c (D.ρ s₁))‖ < ε := by
      have hb := hΓcont.preimage_mem_nhds (Metric.ball_mem_nhds (fderiv ℝ Γ (c (D.ρ s₁))) hεpos)
      filter_upwards [hb] with y hy
      rwa [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at hy
    filter_upwards [h1, h2, h3] with y hy1 hy2 hy3
    exact ⟨hy1, hy2, hy3⟩
  obtain ⟨r₁, hr₁pos, hr₁sub⟩ := Metric.mem_nhds_iff.mp hnhds
  obtain ⟨r₂, hr₂pos, hr₂sub⟩ := Metric.isOpen_iff.mp c.open_target (c (D.ρ s₁)) hy₁t
  set r : ℝ := min r₁ r₂ with hrdef
  have hrpos : 0 < r := lt_min hr₁pos hr₂pos
  have hgood : ∀ y ∈ Metric.ball (c (D.ρ s₁)) r, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ ν : EuclideanSpace ℝ (Fin n),
      fderiv ℝ Γ y ν = 0 → (t • fderiv ℝ A y + (1 - t) • fderiv ℝ B y) ν = 0 → ν = 0 := by
    intro y hy t ht ν hv1 hv2
    have hy1 : y ∈ Metric.ball (c (D.ρ s₁)) r₁ := by
      rw [Metric.mem_ball] at hy ⊢
      exact lt_of_lt_of_le hy (min_le_left _ _)
    obtain ⟨hdA, hdB, hdΓ⟩ := hr₁sub hy1
    exact hεprop (fderiv ℝ A y) (fderiv ℝ B y) (fderiv ℝ Γ y) hdA hdB hdΓ t ht ν hv1 hv2
  -- the corresponding neighbourhood of `s₁`
  have hγc : ContinuousAt D.ρ s₁ := D.hρ.continuous.continuousAt
  have hcc : ContinuousAt (fun s : ℝ => c (D.ρ s)) s₁ := (c.continuousAt hcsrc).comp hγc
  have hV : {s : ℝ | D.ρ s ∈ c.source ∧ c (D.ρ s) ∈ Metric.ball (c (D.ρ s₁)) r} ∈ 𝓝 s₁ := by
    have h1 : D.ρ ⁻¹' c.source ∈ 𝓝 s₁ := hγc.preimage_mem_nhds (c.open_source.mem_nhds hcsrc)
    have h2 : (fun s : ℝ => c (D.ρ s)) ⁻¹' Metric.ball (c (D.ρ s₁)) r ∈ 𝓝 s₁ :=
      hcc.preimage_mem_nhds (Metric.ball_mem_nhds _ hrpos)
    filter_upwards [h1, h2] with s hs1 hs2
    exact ⟨hs1, hs2⟩
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨ρ, hρpos, ?_⟩
  intro χ hχ hχI s hs0 hs
  obtain ⟨hsrcc, hsball⟩ := hρsub (by rwa [Metric.mem_ball, Real.dist_eq])
  -- smoothness of the blended map
  have hψsm : ContMDiff (MC n) (MC (n - 1)) smoothOrder
      (fun x : M => χ (D.g x) • G₁ x + (1 - χ (D.g x)) • G₂ x) := by
    intro x
    have h1 : ContMDiffAt (MC n) MCreal smoothOrder (fun x : M => χ (D.g x)) x :=
      ((contMDiff_iff_contDiff.mpr hχ).contMDiffAt (x := D.g x)).comp x D.hg.contMDiffAt
    have h2 : ContMDiffAt (MC n) MCreal smoothOrder (fun x : M => 1 - χ (D.g x)) x :=
      contMDiffAt_const.sub h1
    exact (h1.smul hG₁.contMDiffAt).add (h2.smul hG₂.contMDiffAt)
  -- transversality of the blend
  intro v hv1 hv2
  have hyt : c (D.ρ s) ∈ c.target := c.map_source hsrcc
  have hsymm : c.symm (c (D.ρ s)) = D.ρ s := c.left_inv hsrcc
  -- the manifold derivatives at `D.ρ s`, with concrete types
  let Se : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    mfderiv (MC n) (MC n) (c.symm : EuclideanSpace ℝ (Fin n) → M) (c (D.ρ s))
  let Ce : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    mfderiv (MC n) (MC n) (c : M → EuclideanSpace ℝ (Fin n)) (D.ρ s)
  let T₁ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n - 1)) :=
    mfderiv (MC n) (MC (n - 1)) G₁ (D.ρ s)
  let T₂ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n - 1)) :=
    mfderiv (MC n) (MC (n - 1)) G₂ (D.ρ s)
  let Mψ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n - 1)) :=
    mfderiv (MC n) (MC (n - 1))
      (fun x : M => χ (D.g x) • G₁ x + (1 - χ (D.g x)) • G₂ x) (D.ρ s)
  let Lg : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := mfderiv (MC n) MCreal D.g (D.ρ s)
  have hSeCe : Se.comp Ce = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) :=
    hmd.symm_comp_deriv hsrcc
  have hAder' : fderiv ℝ A (c (D.ρ s)) = T₁.comp Se := by
    have h := (hasFDerivAt_coord (n := n) hG₁ hcm hyt).fderiv
    rw [hsymm] at h
    rw [hAdef]
    exact h
  have hBder' : fderiv ℝ B (c (D.ρ s)) = T₂.comp Se := by
    have h := (hasFDerivAt_coord (n := n) hG₂ hcm hyt).fderiv
    rw [hsymm] at h
    rw [hBdef]
    exact h
  have hΓder' : fderiv ℝ Γ (c (D.ρ s)) = Lg.comp Se := by
    have h := (hasFDerivAt_coord (n := n) D.hg hcm hyt).fderiv
    rw [hsymm] at h
    rw [hΓdef]
    exact h
  have hψder' : fderiv ℝ (fun y' => (fun x : M => χ (D.g x) • G₁ x + (1 - χ (D.g x)) • G₂ x)
        (c.symm y')) (c (D.ρ s)) = Mψ.comp Se := by
    have h := (hasFDerivAt_coord (n := n) hψsm hcm hyt).fderiv
    rw [hsymm] at h
    exact h
  have hprod : fderiv ℝ (fun y' => χ (D.g (c.symm y')) • G₁ (c.symm y')
        + (1 - χ (D.g (c.symm y'))) • G₂ (c.symm y')) (c (D.ρ s))
      = χ (D.g (D.ρ s)) • fderiv ℝ A (c (D.ρ s)) + (1 - χ (D.g (D.ρ s))) • fderiv ℝ B (c (D.ρ s)) := by
    have h := fderiv_blend_coord (n := n) hχ D.hg hG₁ hG₂ hcm hyt
      (by rw [hsymm]; exact hv₁ s hs0) (by rw [hsymm]; exact hv₂ s hs0)
    rw [h, hsymm]
  -- the vector in coordinates
  let δ : EuclideanSpace ℝ (Fin n) := Ce v
  have hDs : Se δ = v := by
    have h1 := congrArg
      (fun (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) => L v) hSeCe
    simpa [δ, ContinuousLinearMap.comp_apply] using h1
  have hΓ0 : fderiv ℝ Γ (c (D.ρ s)) δ = 0 := by
    rw [hΓder']
    change Lg (Se δ) = 0
    rw [hDs]
    exact hv2
  have hZ0 : (χ (D.g (D.ρ s)) • fderiv ℝ A (c (D.ρ s))
      + (1 - χ (D.g (D.ρ s))) • fderiv ℝ B (c (D.ρ s))) δ = 0 := by
    rw [← hprod]
    have hbridge : (fun y' => χ (D.g (c.symm y')) • G₁ (c.symm y')
          + (1 - χ (D.g (c.symm y'))) • G₂ (c.symm y'))
        = (fun y' => (fun x : M => χ (D.g x) • G₁ x + (1 - χ (D.g x)) • G₂ x) (c.symm y')) := by
      funext y'; rfl
    rw [hbridge, hψder']
    change Mψ (Se δ) = 0
    rw [hDs]
    exact hv1
  have hδ0 : δ = 0 :=
    hgood (c (D.ρ s)) hsball (χ (D.g (D.ρ s))) (hχI (D.g (D.ρ s))) δ hΓ0 hZ0
  calc v = Se δ := hDs.symm
    _ = Se 0 := by rw [hδ0]
    _ = 0 := map_zero _



set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- **The linear gauge between two transverse functions along the ray.**  Ray version of
`Work.Noncompact.CompressionTube.exists_gauge`. -/
theorem ray_gauge {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    (D : RayData n M)
    {ψ₁ ψ₂ : M → EuclideanSpace ℝ (Fin (n - 1))}
    (h₁ : ContMDiff (MC n) (MC (n - 1)) smoothOrder ψ₁)
    (h₂ : ContMDiff (MC n) (MC (n - 1)) smoothOrder ψ₂)
    (h₁0 : ∀ s : ℝ, 0 ≤ s → ψ₁ (D.ρ s) = 0)
    (h₂0 : ∀ s : ℝ, 0 ≤ s → ψ₂ (D.ρ s) = 0) {s₀ : ℝ} (hs₀ : 0 ≤ s₀)
    (hT₁ : Transverse D.ρ D.g ψ₁ s₀) (hT₂ : Transverse D.ρ D.g ψ₂ s₀) :
    ∃ A : EuclideanSpace ℝ (Fin (n - 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n - 1)),
      Function.Injective A ∧
      (∀ v : TangentSpace (MC n) (D.ρ s₀),
        A (mfderiv (MC n) (MC (n - 1)) ψ₂ (D.ρ s₀) v) =
        mfderiv (MC n) (MC (n - 1)) ψ₁ (D.ρ s₀) v) := by
  classical
  -- the two differentials at the base point, and the differential of `D.g`
  let L₁ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n - 1)) :=
    mfderiv (MC n) (MC (n - 1)) ψ₁ (D.ρ s₀)
  let L₂ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n - 1)) :=
    mfderiv (MC n) (MC (n - 1)) ψ₂ (D.ρ s₀)
  let Lg : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := mfderiv (MC n) MCreal D.g (D.ρ s₀)
  let vel : EuclideanSpace ℝ (Fin n) := mfderiv MCreal (MC n) D.ρ s₀ 1
  -- the velocity of `D.ρ` is killed by both differentials, and is not killed by `dg`
  have hvel₁ : L₁ vel = 0 := ray_mfderiv_velocity_eq_zero D.hρ h₁ h₁0 hs₀
  have hvel₂ : L₂ vel = 0 := ray_mfderiv_velocity_eq_zero D.hρ h₂ h₂0 hs₀
  have hvelg : Lg vel = 1 := ray_mfderiv_g_velocity D.hgc D.hρ D.hg hs₀
  -- the map `v ↦ (dψ₂ v, dg v)` is injective (this is the transversality of `ψ₂`)
  let Φ : EuclideanSpace ℝ (Fin n) →L[ℝ] (EuclideanSpace ℝ (Fin (n - 1)) × ℝ) := L₂.prod Lg
  have hΦapply : ∀ v : EuclideanSpace ℝ (Fin n), Φ v = (L₂ v, Lg v) := fun v => rfl
  have hΦinj : Function.Injective Φ := by
    intro v w hvw
    have h : Φ (v - w) = 0 := by rw [map_sub, hvw, sub_self]
    have h1 : L₂ (v - w) = 0 := by
      simpa [hΦapply (v - w)] using congrArg Prod.fst h
    have h2 : Lg (v - w) = 0 := by
      simpa [hΦapply (v - w)] using congrArg Prod.snd h
    exact sub_eq_zero.mp (hT₂ (v - w) h1 h2)
  -- the domain and the target of `Φ` have the same dimension
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin (n - 1)) × ℝ) := by
    rw [Module.finrank_prod, finrank_euclideanSpace, finrank_euclideanSpace,
      Module.finrank_self, Fintype.card_fin, Fintype.card_fin]
    omega
  have hΦinjL : Function.Injective Φ.toLinearMap := hΦinj
  -- hence `Φ` is a linear equivalence
  let e : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] (EuclideanSpace ℝ (Fin (n - 1)) × ℝ) :=
    Φ.toLinearMap.linearEquivOfInjective hΦinjL hdim
  have heapp : ∀ y : EuclideanSpace ℝ (Fin n), e y = Φ y := by
    intro y
    show (Φ.toLinearMap.linearEquivOfInjective hΦinjL hdim) y = Φ y
    rw [LinearMap.linearEquivOfInjective_apply]
    rfl
  -- a section of `dψ₂`, sending `u` to the unique `v` with `dψ₂ v = u`, `dg v = 0`
  let S : EuclideanSpace ℝ (Fin (n - 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    e.symm.toLinearMap.comp (LinearMap.inl ℝ (EuclideanSpace ℝ (Fin (n - 1))) ℝ)
  have hSapply : ∀ u : EuclideanSpace ℝ (Fin (n - 1)), S u = e.symm (u, 0) := fun u => rfl
  -- the gauge and its continuous version
  let Aₗ : EuclideanSpace ℝ (Fin (n - 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n - 1)) :=
    L₁.toLinearMap.comp S
  let A : EuclideanSpace ℝ (Fin (n - 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n - 1)) :=
    Aₗ.toContinuousLinearMap
  have hAapply : ∀ u : EuclideanSpace ℝ (Fin (n - 1)), A u = Aₗ u := fun u => rfl
  -- `S` is a right inverse of `dψ₂`
  have heS : ∀ u : EuclideanSpace ℝ (Fin (n - 1)), e (S u) = (u, 0) := by
    intro u
    rw [hSapply u, LinearEquiv.apply_symm_apply]
  have hvel_e : e vel = (0, 1) := by
    rw [heapp vel, hΦapply vel, hvel₂, hvelg]
  -- the decomposition of a tangent vector along the velocity
  have hvec : ∀ v : EuclideanSpace ℝ (Fin n), S (L₂ v) + Lg v • vel = v := by
    intro v
    apply e.injective
    rw [map_add, map_smul, heS (L₂ v), hvel_e, heapp v, hΦapply v]
    simp
  refine ⟨A, ?_, ?_⟩
  · -- injectivity of the gauge
    intro x y hxy
    have hz : A (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hz' : Aₗ (x - y) = 0 := by rw [← hAapply (x - y)]; exact hz
    have hL1 : L₁ (S (x - y)) = 0 := hz'
    have hLg : Lg (S (x - y)) = 0 := by
      have h := congrArg Prod.snd (heS (x - y))
      rw [heapp (S (x - y)), hΦapply (S (x - y))] at h
      simpa using h
    have hS0 : S (x - y) = 0 := hT₁ (S (x - y)) hL1 hLg
    have hxy0 : x - y = 0 := by
      have h := congrArg Prod.fst (heS (x - y))
      rw [heapp (S (x - y)), hΦapply (S (x - y)), hS0] at h
      simpa using h.symm
    exact sub_eq_zero.mp hxy0
  · -- the defining property of the gauge
    intro v
    change A (L₂ v) = L₁ v
    have h1 : A (L₂ v) = Aₗ (L₂ v) := rfl
    have h2 : Aₗ (L₂ v) = L₁ (S (L₂ v)) := rfl
    have h3 : L₁ v = L₁ (S (L₂ v)) := by
      conv_lhs => rw [← hvec v]
      rw [map_add, map_smul, hvel₁, smul_zero, add_zero]
    rw [h1, h2]
    exact h3.symm

/-! ## One step of the recursion -/

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
/-- **One step of the ray recursion.**  Ray version of
`Work.Noncompact.CompressionTube.ctc_step_exists`: from a piece transverse on the window
`(k - 21/8, k + 1)` and a raw piece transverse on `[k - 2, k + 2]` (`k ≥ 1`) build a piece
transverse on `(k - 13/8, k + 2)` which agrees with the old piece on `{g ≤ k - d}` for some
`d ∈ (0, 1/8]`. -/
theorem ray_step {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    [T2Space M] [SecondCountableTopology M] (D : RayData n M)
    {k : ℤ} (hk : 1 ≤ k) {Ψ ψ : M → EuclideanSpace ℝ (Fin (n - 1))}
    (hΨc : ContMDiff (MC n) (MC (n - 1)) smoothOrder Ψ)
    (hψc : ContMDiff (MC n) (MC (n - 1)) smoothOrder ψ)
    (hΨ0 : ∀ s : ℝ, 0 ≤ s → Ψ (D.ρ s) = 0) (hψ0 : ∀ s : ℝ, 0 ≤ s → ψ (D.ρ s) = 0)
    (hΨT : ∀ s : ℝ, 0 ≤ s → s ∈ Set.Ioo ((k : ℝ) - 21 / 8) ((k : ℝ) + 1) →
      Transverse D.ρ D.g Ψ s)
    (hψT : ∀ s : ℝ, 0 ≤ s → s ∈ Set.Icc ((k : ℝ) - 2) ((k : ℝ) + 2) →
      Transverse D.ρ D.g ψ s) :
    ∃ (Ψ' : M → EuclideanSpace ℝ (Fin (n - 1))) (d : ℝ), 0 < d ∧ d ≤ 1 / 8 ∧
      ContMDiff (MC n) (MC (n - 1)) smoothOrder Ψ' ∧
      (∀ s : ℝ, 0 ≤ s → Ψ' (D.ρ s) = 0) ∧
      (∀ s : ℝ, 0 ≤ s → s ∈ Set.Ioo ((k : ℝ) - 13 / 8) ((k : ℝ) + 2) →
        Transverse D.ρ D.g Ψ' s) ∧
      (∀ x : M, D.g x ≤ (k : ℝ) - d → Ψ' x = Ψ x) := by
  classical
  have hn0 : smoothOrder ≠ (0 : WithTop ℕ∞) := by simp [smoothOrder]
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) ≤ k)
  -- transversality at the switch point `k`
  have hΨTk : Transverse D.ρ D.g Ψ (k : ℝ) := by
    refine hΨT _ hk0 (Set.mem_Ioo.mpr ⟨?_, ?_⟩) <;> push_cast <;> norm_num
  have hψTk : Transverse D.ρ D.g ψ (k : ℝ) := by
    refine hψT _ hk0 (Set.mem_Icc.mpr ⟨?_, ?_⟩) <;> push_cast <;> norm_num
  -- the gauge
  obtain ⟨A, hAinj, hAgauge⟩ := ray_gauge hn D hΨc hψc hΨ0 hψ0 hk0 hΨTk hψTk
  -- the gauge-transformed raw piece
  set R : M → EuclideanSpace ℝ (Fin (n - 1)) := fun x => A (ψ x) with hRdef
  have hRc : ContMDiff (MC n) (MC (n - 1)) smoothOrder R := by
    rw [hRdef]
    exact (A.contMDiff (n := smoothOrder)).comp hψc
  have hR0 : ∀ s : ℝ, 0 ≤ s → R (D.ρ s) = 0 := fun s hs => by simp [hRdef, hψ0 s hs]
  -- the chain rule for `R`
  have hA_at (s : ℝ) : MDifferentiableAt (MC (n - 1)) (MC (n - 1))
      (⇑A) (ψ (D.ρ s)) :=
    (A.contMDiff (n := smoothOrder)).mdifferentiableAt (x := ψ (D.ρ s)) hn0
  have hRder (s : ℝ) : mfderiv (MC n) (MC (n - 1)) R (D.ρ s)
      = A.comp (mfderiv (MC n) (MC (n - 1)) ψ (D.ρ s)) := by
    have hψd : MDifferentiableAt (MC n) (MC (n - 1)) ψ (D.ρ s) :=
      hψc.mdifferentiableAt (x := D.ρ s) hn0
    have hcomp := mfderiv_comp (I := MC n) (I' := MC (n - 1)) (I'' := MC (n - 1))
      (f := ψ) (g := ⇑A) (D.ρ s) (hA_at s) hψd
    have h1 : mfderiv (MC (n - 1)) (MC (n - 1)) (⇑A) (ψ (D.ρ s)) = A := by
      rw [show mfderiv (MC (n - 1)) (MC (n - 1)) (⇑A) (ψ (D.ρ s))
            = fderiv ℝ (⇑A) (ψ (D.ρ s)) from mfderiv_eq_fderiv]
      exact ContinuousLinearMap.fderiv A
    have h2 : R = ⇑A ∘ ψ := rfl
    rw [h2, hcomp, h1]
  have hAgauge_vel : (A.comp (mfderiv (MC n) (MC (n - 1)) ψ (D.ρ (k : ℝ))))
      (mfderiv MCreal (MC n) D.ρ (k : ℝ) 1) = 0 := by
    show A (mfderiv (MC n) (MC (n - 1)) ψ (D.ρ (k : ℝ))
      (mfderiv MCreal (MC n) D.ρ (k : ℝ) 1)) = 0
    simp only [ray_mfderiv_velocity_eq_zero D.hρ hψc hψ0 hk0, map_zero]
  have hagree : mfderiv (MC n) (MC (n - 1)) R (D.ρ (k : ℝ))
      = mfderiv (MC n) (MC (n - 1)) Ψ (D.ρ (k : ℝ)) := by
    rw [hRder]
    refine ray_eq_of_agree_on_ker D.hgc D.hρ D.hg hk0 ?_ ?_ ?_
    · exact hAgauge_vel
    · exact ray_mfderiv_velocity_eq_zero D.hρ hΨc hΨ0 hk0
    · intro v _
      show A (mfderiv (MC n) (MC (n - 1)) ψ (D.ρ (k : ℝ)) v)
        = mfderiv (MC n) (MC (n - 1)) Ψ (D.ρ (k : ℝ)) v
      exact hAgauge v
  -- the blend radius
  obtain ⟨ρ, hρpos, hρ⟩ := ray_blend hn D hΨc hRc hΨ0 hR0 hk0 hagree.symm hΨTk
  -- the transition width
  set d : ℝ := min (ρ / 2) (1 / 8) with hddef
  have hdpos : 0 < d := lt_min (by linarith) (by norm_num)
  have hdle : d ≤ 1 / 8 := min_le_right _ _
  have hdlt : d < ρ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  obtain ⟨χ, hχsm, hχI, hχ1, hχ0⟩ := exists_smoothStep (k : ℝ) d hdpos
  refine ⟨fun x : M => χ (D.g x) • Ψ x + (1 - χ (D.g x)) • R x, d, hdpos, hdle, ?_, ?_, ?_, ?_⟩
  · -- smoothness
    intro x
    have h1 : ContMDiffAt (MC n) MCreal smoothOrder (fun x : M => χ (D.g x)) x :=
      ((contMDiff_iff_contDiff.mpr hχsm).contMDiffAt (x := D.g x)).comp x D.hg.contMDiffAt
    have h2 : ContMDiffAt (MC n) MCreal smoothOrder (fun x : M => 1 - χ (D.g x)) x :=
      contMDiffAt_const.sub h1
    exact (h1.smul hΨc.contMDiffAt).add (h2.smul hRc.contMDiffAt)
  · -- vanishing on the ray
    intro s hs0
    simp only
    rw [hΨ0 s hs0, hR0 s hs0, smul_zero, smul_zero, add_zero]
  · -- transversality
    intro s hs0 hs
    by_cases hb : |s - (k : ℝ)| < ρ
    · exact hρ χ hχsm hχI s hs0 hb
    · push_neg at hb
      rcases le_total s (k : ℝ) with hsk | hsk
      · -- left of the transition: the germ is `Ψ`
        have hks : (k : ℝ) - s = |s - (k : ℝ)| := by
          rw [abs_sub_comm, abs_of_nonneg (by linarith)]
        have hslt : s < (k : ℝ) - d := by linarith [hks.ge, hb, hdlt]
        have hgerm : (fun x : M => χ (D.g x) • Ψ x + (1 - χ (D.g x)) • R x)
            =ᶠ[𝓝 (D.ρ s)] Ψ := by
          have hopen : IsOpen {x : M | D.g x < (k : ℝ) - d} :=
            isOpen_lt D.hg.continuous continuous_const
          have hmem : D.ρ s ∈ {x : M | D.g x < (k : ℝ) - d} := by
            simp only [Set.mem_setOf_eq, D.hgc s hs0]; exact hslt
          filter_upwards [hopen.mem_nhds hmem] with x hx
          rw [hχ1 (D.g x) hx.le]
          simp
        refine (transverse_congr hgerm).mpr (hΨT s hs0 ?_)
        refine Set.mem_Ioo.mpr ⟨by linarith [hs.1], by linarith⟩
      · -- right of the transition: the germ is `R`
        have hks : s - (k : ℝ) = |s - (k : ℝ)| := by
          rw [abs_of_nonneg (by linarith)]
        have hsgt : (k : ℝ) + d < s := by linarith [hks.ge, hb, hdlt]
        have hgerm : (fun x : M => χ (D.g x) • Ψ x + (1 - χ (D.g x)) • R x)
            =ᶠ[𝓝 (D.ρ s)] R := by
          have hopen : IsOpen {x : M | (k : ℝ) + d < D.g x} :=
            isOpen_lt continuous_const D.hg.continuous
          have hmem : D.ρ s ∈ {x : M | (k : ℝ) + d < D.g x} := by
            simp only [Set.mem_setOf_eq, D.hgc s hs0]; exact hsgt
          filter_upwards [hopen.mem_nhds hmem] with x hx
          rw [hχ0 (D.g x) hx.le]
          simp
        refine (transverse_congr hgerm).mpr ?_
        intro v hv1 hv2
        have hψv : mfderiv (MC n) (MC (n - 1)) ψ (D.ρ s) v = 0 := by
          refine hAinj ?_
          have happ := congrArg (fun (L : TangentSpace (MC n) (D.ρ s) →L[ℝ]
              EuclideanSpace ℝ (Fin (n - 1))) => L v) (hRder s)
          have hzero : (A.comp (mfderiv (MC n) (MC (n - 1)) ψ (D.ρ s))) v = 0 := by
            rw [← happ]
            exact hv1
          calc A ((mfderiv (MC n) (MC (n - 1)) ψ (D.ρ s)) v)
              = (A.comp (mfderiv (MC n) (MC (n - 1)) ψ (D.ρ s))) v := rfl
            _ = 0 := hzero
            _ = A 0 := (map_zero A).symm
        exact hψT s hs0 (Set.mem_Icc.mpr ⟨by linarith, by linarith [hs.2]⟩) v hψv hv2
  · -- the equality on the left
    intro x hx
    simp only [hχ1 (D.g x) hx, one_smul, sub_self, zero_smul, add_zero]


end

end Work.Drive.RayTube
