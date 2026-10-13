import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.H5.Data
import Submission.Work.FTS.StrongEps.H5.DataW
import Submission.Work.FTS.StrongEps.H5.WlInfMem_mono
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.fstarDat
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.Nonlinear.FstarPkg.WlInf_congr
import Submission.Work.FTS.Nonlinear.FstarPkg.DzHzDefs
import Submission.Work.FTS.Nonlinear.FstarPkg.Hz_deriv_bound
import Submission.Work.Spaces.WlInf_terms
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.H5.Atoms

open Work.Spaces
open Work.FTS.Nonlinear.FstarPkg (Hz HB Hz_deriv_bound Hz_eq_mul_deriv)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The angular weight `sin(2θ)^{-α/5}/(α+sin 2θ)` of the `𝒲`-norm (the `Wt` of
`Work.FTS.Nonlinear.FstarPkg.DthAux`). -/
local notation "wθ" => Work.FTS.Nonlinear.FstarPkg.DthAux.Wt

/-! ## Separated products

Every function treated below is, on `z > -1`, a *separated product* `A(θ)·H(z)`: the angular
factor `A` is a `D_θ`-iterate of `Γ` (multiplied by a constant), and the radial factor `H` is
one of the explicit rational functions `hKer`, `Hz`.  The two slot sums of the `𝒲^{l,∞}`-norm
of such a product are then estimated by the two hypotheses `hA0`/`hAj` (angular) and `hH`
(radial), using `pzIter_decomp`/`DthIter_decomp` for the separation of variables. -/

/-- The universal constant of the separated-product estimate. -/
noncomputable def sepBnd (l : ℕ) (A0 : ℝ) (Aj B : ℕ → ℝ) : ℝ :=
  (∑ k ∈ Finset.range (l + 1), A0 * B k)
    + ∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
        (if 1 ≤ j ∧ k + j ≤ l then Aj j * B k else 0)

/-- **The `𝒲^{l,∞}`-estimate for a separated product** `(z,θ) ↦ A θ · H z`.

If the angular factor `A` is bounded by `A0` on `Iθ`, if its `D_θ`-iterates satisfy the weighted
bounds `|D_θ^j A θ| · sin(2θ)^{-α/5}/(α+sin 2θ) ≤ Aj j`, and if the radial factor satisfies
`|(z+1)^k H^{(k)}(z)| ≤ B k` for `z ≥ 0`, then

`WlInfMem α l (A ⊗ H)` and `WlInf α l (A ⊗ H) ≤ sepBnd l A0 Aj B`.

This is `Work.FTS.Nonlinear.FstarPkg.WlInf_Gamma_radial` with the angular input `Γ`
(`Gam_bounds`, `dthU_Gam_le`, `Gam_mul_weight_le`) replaced by the two general hypotheses. -/
lemma WlInf_sep {α : ℝ} {l : ℕ} {A H : ℝ → ℝ} {A0 : ℝ} {Aj B : ℕ → ℝ}
    (hA0 : ∀ θ ∈ Iθ, |A θ| ≤ A0)
    (hAj : ∀ j : ℕ, 1 ≤ j → j ≤ l → ∀ θ ∈ Iθ, |dthU^[j] A θ * wθ α θ| ≤ Aj j)
    (hH : ∀ k : ℕ, k ≤ l → ∀ z : ℝ, 0 ≤ z → |(z + 1) ^ k * deriv^[k] H z| ≤ B k) :
    WlInfMem α l (fun z θ => A θ * H z) ∧
      WlInf α l (fun z θ => A θ * H z) ≤ sepBnd l A0 Aj B := by
  -- separation of variables for the two families of slots
  have hDth : ∀ j : ℕ, DthIter j (fun z θ => A θ * H z) = fun z θ => dthU^[j] A θ * H z := by
    intro j
    funext z θ
    exact DthIter_decomp j A H z θ
  have hpt1 : ∀ k : ℕ, k ≤ l → ∀ z ∈ Iz, ∀ θ ∈ Iθ,
      |(z + 1) ^ k * pzIter k (fun z θ => A θ * H z) z θ| ≤ A0 * B k := by
    intro k hk z hz θ hθ
    rw [pzIter_decomp k A H z θ]
    rw [show (z + 1) ^ k * (A θ * deriv^[k] H z)
          = A θ * ((z + 1) ^ k * deriv^[k] H z) from by ring,
      abs_mul]
    exact mul_le_mul (hA0 θ hθ) (hH k hk z hz) (abs_nonneg _)
      (le_trans (abs_nonneg _) (hA0 θ hθ))
  have hpt2 : ∀ j : ℕ, 1 ≤ j → ∀ k : ℕ, k + j ≤ l → ∀ z ∈ Iz, ∀ θ ∈ Iθ,
      |(z + 1) ^ k * pzIter k (DthIter j (fun z θ => A θ * H z)) z θ
          * Real.sin (2 * θ) ^ (-(α / 5)) / (α + Real.sin (2 * θ))| ≤ Aj j * B k := by
    intro j hj1 k hkj z hz θ hθ
    have hjl : j ≤ l := by omega
    have hkl : k ≤ l := by omega
    rw [hDth j, pzIter_decomp k (dthU^[j] A) H z θ]
    rw [show (z + 1) ^ k * (dthU^[j] A θ * deriv^[k] H z)
          * Real.sin (2 * θ) ^ (-(α / 5)) / (α + Real.sin (2 * θ))
        = (dthU^[j] A θ * (Real.sin (2 * θ) ^ (-(α / 5)) / (α + Real.sin (2 * θ))))
          * ((z + 1) ^ k * deriv^[k] H z) from by ring,
      abs_mul]
    exact mul_le_mul (hAj j hj1 hjl θ hθ) (hH k hkl z hz) (abs_nonneg _)
      (le_trans (abs_nonneg _) (hAj j hj1 hjl θ hθ))
  constructor
  · rw [WlInfMem]
    exact ⟨fun k hk => Work.FTS.Nonlinear.FstarPkg.supFinite_of_pointwise_bound (hpt1 k hk),
      fun j hj k hk hj1 hjk =>
        Work.FTS.Nonlinear.FstarPkg.supFinite_of_pointwise_bound (hpt2 j hj1 k hjk)⟩
  · rw [WlInf, sepBnd]
    refine add_le_add ?_ ?_
    · refine Finset.sum_le_sum fun k hk => supAbs_le fun z hz θ hθ =>
        hpt1 k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) z hz θ hθ
    · refine Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun k hk => ?_
      by_cases h : 1 ≤ j ∧ k + j ≤ l
      · rw [if_pos h, if_pos h]
        exact supAbs_le fun z hz θ hθ => hpt2 j h.1 k h.2 z hz θ hθ
      · rw [if_neg h, if_neg h]

/-! ## The separated forms of the profiles -/

/-- `D_θF_*` is the separated product `((2α/c)·D_θΓ) ⊗ hKer`. -/
lemma DthFstar_sep {α : ℝ} :
    Work.Spaces.Dth (Work.Construction.Fstar α)
      = fun z θ => (2 * α / Work.Spaces.c α
          * Work.Spaces.dthU^[1] (fun t => Work.Spaces.Gam α t) θ) * Work.Spaces.hKer z := by
  rw [show Work.Spaces.Dth (Work.Construction.Fstar α)
      = Work.Spaces.DthIter 1 (Work.Construction.Fstar α) from rfl,
    Work.FTS.Nonlinear.FstarPkg.DthAux.Fstar_eq α]
  funext z θ
  rw [Work.Spaces.DthIter_decomp 1
      (fun t => 2 * α / Work.Spaces.c α * Work.Spaces.Gam α t) Work.Spaces.hKer z θ,
    Work.Spaces.dthU_iter_const_mul 1 (2 * α / Work.Spaces.c α)
      (fun t => Work.Spaces.Gam α t)]

/-- `D_θD_θF_*` is the separated product `((2α/c)·D_θ²Γ) ⊗ hKer`. -/
lemma DthDthFstar_sep {α : ℝ} :
    ∀ z : ℝ, -1 < z → ∀ θ : ℝ,
      Work.Spaces.DthIter 2 (Work.Construction.Fstar α) z θ
        = (2 * α / Work.Spaces.c α
            * Work.Spaces.dthU^[2] (fun t => Work.Spaces.Gam α t) θ) * Work.Spaces.hKer z := by
  intro z hz θ
  rw [Work.FTS.Nonlinear.FstarPkg.DthAux.Fstar_eq α,
    Work.Spaces.DthIter_decomp 2
      (fun t => 2 * α / Work.Spaces.c α * Work.Spaces.Gam α t) Work.Spaces.hKer z θ,
    Work.Spaces.dthU_iter_const_mul 2 (2 * α / Work.Spaces.c α)
      (fun t => Work.Spaces.Gam α t)]

/-- `D_zD_θF_*` is the separated product `((α/c)·D_θΓ) ⊗ Hz` on `z > -1`. -/
lemma DzDthFstar_sep {α : ℝ} :
    ∀ z : ℝ, -1 < z → ∀ θ : ℝ,
      Work.Spaces.Dz (Work.Spaces.Dth (Work.Construction.Fstar α)) z θ
        = (α / Work.Spaces.c α
            * Work.Spaces.dthU^[1] (fun t => Work.Spaces.Gam α t) θ) * Hz z := by
  intro z hz θ
  -- the `z`-slice of `D_θF_*` is a constant multiple of `hKer`
  have hslice : (fun z' : ℝ => Work.Spaces.Dth (Work.Construction.Fstar α) z' θ)
      = fun z' : ℝ => (2 * α / Work.Spaces.c α
          * Work.Spaces.dthU^[1] (fun t => Work.Spaces.Gam α t) θ) * Work.Spaces.hKer z' :=
    funext fun z' => congrFun (congrFun (DthFstar_sep (α := α)) z') θ
  show z * deriv (fun z' : ℝ => Work.Spaces.Dth (Work.Construction.Fstar α) z' θ) z
      = (α / Work.Spaces.c α
          * Work.Spaces.dthU^[1] (fun t => Work.Spaces.Gam α t) θ) * Hz z
  rw [hslice]
  have hd : DifferentiableAt ℝ Work.Spaces.hKer z := by
    have hz2 : (1 + z) ^ 2 ≠ 0 := by
      have h1 : (1 : ℝ) + z ≠ 0 := by linarith
      exact pow_ne_zero 2 h1
    have hden : DifferentiableAt ℝ (fun y : ℝ => (1 + y) ^ 2) z :=
      ((differentiableAt_const (1 : ℝ)).add differentiableAt_id).pow 2
    exact (differentiableAt_id (x := z)).div hden hz2
  rw [deriv_const_mul _ hd, Hz_eq_mul_deriv hz]
  ring

/-! ## The target -/

/-- **The `W5` data of the fixed profile `D_θF_*`.**  `W5 α F a` (defined in
`Submission/Work/FTS/StrongEps/H5/DataW.lean`) is the bundle `SmoothOpen` + `WlInfMem α 4` +
`WlInf α 4 (·) ≤ a` for `F`, `Dz F` and `Dth F`.

All nine facts are about the explicit profile `F_* α z θ = α·(Γ(θ)/c)·2z/(1+z)²` and its
`D_θ`/`D_z`-derivatives.  Known: `Work.FTS.StrongPersist.H6Rows.Npair6BWork.fstarDat` gives
`SmoothOpen` and `WlInfMem α 6` of `F_*`, `Dth F_*`, `Dz F_*` with norms `≤ Cα`, together with the
pointwise slot bounds `|mixed j i A z θ| ≤ C α (z/(1+z)²)·(if 1 ≤ i then sin(2θ)^{α/3} else 1)`
for `j + i ≤ 6` and `A` one of those three.

Concretely the new facts are `WlInfMem α 4 (Dz (Dth F_*))`, `WlInfMem α 4 (Dth (Dth F_*))` (with
`Dth (Dth F_*) = DthIter 2 F_*`) and the corresponding two `WlInf`-bounds.

Direct slot route (recommended): every slot occurring in `WlInf α 4` of these two derivative
functions is, after the elementary calculus identities
`pzIter k (Dz g) = z·pzIter (k+1) g + k·pzIter k g` and `DthIter j (Dz g) = Dz (DthIter j g)`,
a `pzIter`-iterate of `mixed b a F_*` with `a + b ≤ 6`, hence dominated pointwise by a constant
times the `fstarDat` slot bound; finish with `Work.Spaces.supAbs_le` and the definition of
`WlInfMem`/`WlInf`.  `a` may depend on `α`. -/
theorem W5DthFstar : ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∃ a : ℝ, 0 < a ∧
    Work.FTS.StrongEps.H5.W5 α (Work.Spaces.Dth (Work.Construction.Fstar α)) a := by
  obtain ⟨C, hCpos, hdat⟩ := Work.FTS.StrongPersist.H6Rows.Npair6BWork.fstarDat
  obtain ⟨K, hKpos, hKgam⟩ := Work.FTS.StrongPersist.W6Aux.dthGamWeightLe7
  intro α hαIoc
  obtain ⟨hα, hα1⟩ := hαIoc
  obtain ⟨hsmF, hsmDth, hsmDz, hFmem, hFle, hDthmem, hDthle, hDzmem, hDzle, hslot⟩ :=
    hdat α ⟨hα, hα1⟩
  -- ### the level-`4` data of `D_θF_*`
  have hDthmem4 : WlInfMem α 4 (Work.Spaces.Dth (Work.Construction.Fstar α)) :=
    (WlInfMem_mono (α := α) (l := 6) (l' := 4) (by norm_num) hDthmem).1
  have hDthle4 : WlInf α 4 (Work.Spaces.Dth (Work.Construction.Fstar α)) ≤ C * α :=
    le_trans (WlInfMem_mono (α := α) (l := 6) (l' := 4) (by norm_num) hDthmem).2 hDthle
  -- ### the two coefficient bounds
  have hc1 : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hcoef1 : |α / Work.Spaces.c α| ≤ 10 * α := by
    rw [abs_of_nonneg (div_nonneg hα.le hcpos.le), div_le_iff₀ hcpos]
    nlinarith
  have hcoef2 : |2 * α / Work.Spaces.c α| ≤ 20 * α :=
    Work.FTS.Nonlinear.FstarPkg.DthAux.Fstar_coef_leD' α hα hα1
  -- ### the angular factors
  set A1 : ℝ → ℝ := fun θ => α / Work.Spaces.c α
    * Work.Spaces.dthU^[1] (fun t => Work.Spaces.Gam α t) θ with hA1def
  set A2 : ℝ → ℝ := fun θ => 2 * α / Work.Spaces.c α
    * Work.Spaces.dthU^[2] (fun t => Work.Spaces.Gam α t) θ with hA2def
  have hcomp1 : ∀ j : ℕ, Work.Spaces.dthU^[j]
        (Work.Spaces.dthU^[1] (fun t => Work.Spaces.Gam α t))
      = Work.Spaces.dthU^[j + 1] (fun t => Work.Spaces.Gam α t) :=
    fun j => (Function.iterate_add_apply Work.Spaces.dthU j 1
      (fun t => Work.Spaces.Gam α t)).symm
  have hcomp2 : ∀ j : ℕ, Work.Spaces.dthU^[j]
        (Work.Spaces.dthU^[2] (fun t => Work.Spaces.Gam α t))
      = Work.Spaces.dthU^[j + 2] (fun t => Work.Spaces.Gam α t) :=
    fun j => (Function.iterate_add_apply Work.Spaces.dthU j 2
      (fun t => Work.Spaces.Gam α t)).symm
  have hA1iter : ∀ (j : ℕ) (θ : ℝ), Work.Spaces.dthU^[j] A1 θ
      = α / Work.Spaces.c α
          * Work.Spaces.dthU^[j + 1] (fun t => Work.Spaces.Gam α t) θ := by
    intro j θ
    rw [hA1def, Work.Spaces.dthU_iter_const_mul j (α / Work.Spaces.c α)
      (Work.Spaces.dthU^[1] (fun t => Work.Spaces.Gam α t)), hcomp1 j]
  have hA2iter : ∀ (j : ℕ) (θ : ℝ), Work.Spaces.dthU^[j] A2 θ
      = 2 * α / Work.Spaces.c α
          * Work.Spaces.dthU^[j + 2] (fun t => Work.Spaces.Gam α t) θ := by
    intro j θ
    rw [hA2def, Work.Spaces.dthU_iter_const_mul j (2 * α / Work.Spaces.c α)
      (Work.Spaces.dthU^[2] (fun t => Work.Spaces.Gam α t)), hcomp2 j]
  -- ### the angular hypotheses
  have hA1_0 : ∀ θ ∈ Iθ, |A1 θ| ≤ 10 * α * (α * Work.Spaces.tBound 0 0) := by
    intro θ hθ
    have hgoal : |α / Work.Spaces.c α
        * Work.Spaces.dthU^[1] (fun t => Work.Spaces.Gam α t) θ|
        ≤ 10 * α * (α * Work.Spaces.tBound 0 0) := by
      rw [abs_mul]
      have h1 := Work.Spaces.dthU_Gam_le 1 (by norm_num) α hα hα1 θ hθ
      have h2 := Work.Spaces.Gam_bounds α θ hα hθ
      calc |α / Work.Spaces.c α| * |Work.Spaces.dthU^[1] (fun t => Work.Spaces.Gam α t) θ|
          ≤ (10 * α) * (α * Work.Spaces.tBound 0 0 * Work.Spaces.Gam α θ) :=
            mul_le_mul hcoef1 h1 (abs_nonneg _) (by positivity)
        _ ≤ (10 * α) * (α * Work.Spaces.tBound 0 0) := by
            have ht : 0 ≤ α * Work.Spaces.tBound 0 0 :=
              mul_nonneg hα.le (Work.Spaces.tBound_nonneg 0 0)
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            calc α * Work.Spaces.tBound 0 0 * Work.Spaces.Gam α θ
                ≤ α * Work.Spaces.tBound 0 0 * 1 :=
                  mul_le_mul_of_nonneg_left h2.2 ht
              _ = α * Work.Spaces.tBound 0 0 := by ring
        _ = 10 * α * (α * Work.Spaces.tBound 0 0) := by ring
    simpa only [hA1def] using hgoal
  have hA1_j : ∀ j : ℕ, 1 ≤ j → j ≤ 4 → ∀ θ ∈ Iθ,
      |Work.Spaces.dthU^[j] A1 θ * wθ α θ| ≤ 10 * α * (K * α) := by
    intro j hj1 hj4 θ hθ
    have hw := Work.FTS.Nonlinear.FstarPkg.DthAux.Wt_nonneg hα hθ
    have hg := hKgam (j + 1) (by omega) (by omega) α hα hα1 θ hθ
    have h2 : |Work.Spaces.dthU^[j + 1] (fun t => Work.Spaces.Gam α t) θ * wθ α θ|
        ≤ K * α := by
      rw [abs_mul, abs_of_nonneg hw]
      exact hg
    rw [show Work.Spaces.dthU^[j] A1 θ * wθ α θ
        = (α / Work.Spaces.c α) * (Work.Spaces.dthU^[j + 1]
            (fun t => Work.Spaces.Gam α t) θ * wθ α θ) from by
          rw [hA1iter j θ]; ring,
      abs_mul]
    exact mul_le_mul hcoef1 h2 (abs_nonneg _) (by positivity)
  have hA2_0 : ∀ θ ∈ Iθ, |A2 θ| ≤ 20 * α * (α * Work.Spaces.tBound 1 0) := by
    intro θ hθ
    have hgoal : |2 * α / Work.Spaces.c α
        * Work.Spaces.dthU^[2] (fun t => Work.Spaces.Gam α t) θ|
        ≤ 20 * α * (α * Work.Spaces.tBound 1 0) := by
      rw [abs_mul]
      have h1 := Work.Spaces.dthU_Gam_le 2 (by norm_num) α hα hα1 θ hθ
      have h2 := Work.Spaces.Gam_bounds α θ hα hθ
      calc |2 * α / Work.Spaces.c α| * |Work.Spaces.dthU^[2] (fun t => Work.Spaces.Gam α t) θ|
          ≤ (20 * α) * (α * Work.Spaces.tBound 1 0 * Work.Spaces.Gam α θ) :=
            mul_le_mul hcoef2 h1 (abs_nonneg _) (by positivity)
        _ ≤ (20 * α) * (α * Work.Spaces.tBound 1 0) := by
            have ht : 0 ≤ α * Work.Spaces.tBound 1 0 :=
              mul_nonneg hα.le (Work.Spaces.tBound_nonneg 1 0)
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            calc α * Work.Spaces.tBound 1 0 * Work.Spaces.Gam α θ
                ≤ α * Work.Spaces.tBound 1 0 * 1 :=
                  mul_le_mul_of_nonneg_left h2.2 ht
              _ = α * Work.Spaces.tBound 1 0 := by ring
        _ = 20 * α * (α * Work.Spaces.tBound 1 0) := by ring
    simpa only [hA2def] using hgoal
  have hA2_j : ∀ j : ℕ, 1 ≤ j → j ≤ 4 → ∀ θ ∈ Iθ,
      |Work.Spaces.dthU^[j] A2 θ * wθ α θ| ≤ 20 * α * (K * α) := by
    intro j hj1 hj4 θ hθ
    have hw := Work.FTS.Nonlinear.FstarPkg.DthAux.Wt_nonneg hα hθ
    have hg := hKgam (j + 2) (by omega) (by omega) α hα hα1 θ hθ
    have h2 : |Work.Spaces.dthU^[j + 2] (fun t => Work.Spaces.Gam α t) θ * wθ α θ|
        ≤ K * α := by
      rw [abs_mul, abs_of_nonneg hw]
      exact hg
    rw [show Work.Spaces.dthU^[j] A2 θ * wθ α θ
        = (2 * α / Work.Spaces.c α) * (Work.Spaces.dthU^[j + 2]
            (fun t => Work.Spaces.Gam α t) θ * wθ α θ) from by
          rw [hA2iter j θ]; ring,
      abs_mul]
    exact mul_le_mul hcoef2 h2 (abs_nonneg _) (by positivity)
  -- ### the two separated-product estimates
  set sb1 : ℝ := sepBnd 4 (10 * α * (α * Work.Spaces.tBound 0 0))
    (fun _ => 10 * α * (K * α)) HB with hsb1
  set sb2 : ℝ := sepBnd 4 (20 * α * (α * Work.Spaces.tBound 1 0))
    (fun _ => 20 * α * (K * α)) (fun k => (k.factorial : ℝ) * (k + 1)) with hsb2
  have hsep1 : WlInfMem α 4 (fun z θ => A1 θ * Hz z) ∧
      WlInf α 4 (fun z θ => A1 θ * Hz z) ≤ sb1 := by
    rw [hsb1]
    exact WlInf_sep hA1_0 hA1_j (fun k _ z hz => Hz_deriv_bound k z hz)
  have hsep2 : WlInfMem α 4 (fun z θ => A2 θ * Work.Spaces.hKer z) ∧
      WlInf α 4 (fun z θ => A2 θ * Work.Spaces.hKer z) ≤ sb2 := by
    rw [hsb2]
    exact WlInf_sep hA2_0 hA2_j (fun k _ z hz => Work.Spaces.pzIter_hKer_bound k z hz)
  -- ### transfer along the separated forms
  have hcongr1 := Work.FTS.Nonlinear.FstarPkg.WlInf_congr (α := α) (l := 4)
    (f := Work.Spaces.Dz (Work.Spaces.Dth (Work.Construction.Fstar α)))
    (g := fun z θ => A1 θ * Hz z)
    (fun z hz θ => DzDthFstar_sep (α := α) z hz θ)
  have hcongr2 := Work.FTS.Nonlinear.FstarPkg.WlInf_congr (α := α) (l := 4)
    (f := Work.Spaces.DthIter 2 (Work.Construction.Fstar α))
    (g := fun z θ => A2 θ * Work.Spaces.hKer z)
    (fun z hz θ => DthDthFstar_sep (α := α) z hz θ)
  -- ### the constant
  refine ⟨max 1 (max (C * α) (max sb1 sb2)), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  refine ⟨hsmDth, hDthmem4, ?_, hsmDth.Dz, hcongr1.2.mpr hsep1.1, ?_,
    hsmDth.Dth, hcongr2.2.mpr hsep2.1, ?_⟩
  · calc WlInf α 4 (Work.Spaces.Dth (Work.Construction.Fstar α)) ≤ C * α := hDthle4
      _ ≤ max 1 (max (C * α) (max sb1 sb2)) :=
          le_trans (le_max_left (C * α) (max sb1 sb2))
            (le_max_right 1 (max (C * α) (max sb1 sb2)))
  · calc WlInf α 4 (Work.Spaces.Dz (Work.Spaces.Dth (Work.Construction.Fstar α)))
        = WlInf α 4 (fun z θ => A1 θ * Hz z) := hcongr1.1
      _ ≤ sb1 := hsep1.2
      _ ≤ max 1 (max (C * α) (max sb1 sb2)) :=
          le_trans (le_max_left sb1 sb2)
            (le_trans (le_max_right (C * α) (max sb1 sb2))
              (le_max_right 1 (max (C * α) (max sb1 sb2))))
  · calc WlInf α 4 (Work.Spaces.Dth (Work.Spaces.Dth (Work.Construction.Fstar α)))
        = WlInf α 4 (fun z θ => A2 θ * Work.Spaces.hKer z) := hcongr2.1
      _ ≤ sb2 := hsep2.2
      _ ≤ max 1 (max (C * α) (max sb1 sb2)) :=
          le_trans (le_max_right sb1 sb2)
            (le_trans (le_max_right (C * α) (max sb1 sb2))
              (le_max_right 1 (max (C * α) (max sb1 sb2))))

end Work.FTS.StrongEps.H5.Atoms
