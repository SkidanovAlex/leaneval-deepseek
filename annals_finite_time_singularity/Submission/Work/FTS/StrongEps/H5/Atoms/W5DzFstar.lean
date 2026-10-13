import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.H5.Data
import Submission.Work.FTS.StrongEps.H5.DataW
import Submission.Work.FTS.StrongEps.H5.WlInfMem_mono
import Submission.Work.FTS.StrongPersist.DzFstar_W6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.fstarDat
import Submission.Work.Spaces.WlInf_terms
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.Nonlinear.FstarPkg.WlInf_congr
import Submission.Work.FTS.Nonlinear.FstarPkg.WlInf_Gamma_radial
import Submission.Work.FTS.Nonlinear.FstarPkg.DzHzDefs
import Submission.Work.FTS.Nonlinear.FstarPkg.Hz_deriv_bound
import Submission.Work.FTS.Nonlinear.FstarPkg.DzFstar_W
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.WlInfAngRadial
import Submission.Work.Spaces.pzIter_hKer_bound
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongEps.H5.Atoms.W5DthFstar
import Submission.Work.FTS.StrongEps.H5.WlInfMem_Dth
import Submission.Work.Spaces.c_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.H5.Atoms

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The one-dimensional product rule for `z ↦ z u'(z)`

The single analytic fact behind the whole lemma: on an open set where `u` is smooth,

  `(z u')^{(k)}(z) = z u^{(k+1)}(z) + k u^{(k)}(z)`,

from which both the separation identities for `D_z(D_zF_*)` resp. `D_θ(D_zF_*)` and the
weighted derivative bounds for the radial factor `z ↦ z H'(z)` follow. -/

/-- The `m`-th `deriv`-iterate of a function which is `C^{m+1}` on an open set is
differentiable at every point of that set.  (The ``iteratedDerivWithin`` is `C^{m+1}`, and on
the open set it agrees with the honest iterate `deriv^[m]`.) -/
theorem differentiableAt_deriv_iterate {u : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s) {m : ℕ}
    (hu : ContDiffOn ℝ ((m + 1 : ℕ) : WithTop ℕ∞) u s) {z : ℝ} (hz : z ∈ s) :
    DifferentiableAt ℝ (deriv^[m] u) z := by
  have hd : DifferentiableWithinAt ℝ (iteratedDeriv m u) s z := by
    have h0 : DifferentiableWithinAt ℝ (iteratedDerivWithin m u s) s z :=
      (hu.differentiableOn_iteratedDerivWithin (by exact_mod_cast Nat.lt_succ_self m)
        hs.uniqueDiffOn) z hz
    exact h0.congr (fun y hy => (iteratedDerivWithin_of_isOpen hs hy).symm)
      (iteratedDerivWithin_of_isOpen hs hz).symm
  rw [← iteratedDeriv_eq_iterate]
  exact hd.differentiableAt (hs.mem_nhds hz)

/-- **The product rule for the iterated `z`-derivative of `z ↦ z·u'(z)`.**  If `u` is `C^m` on
the open set `s` for every `m`, then for `z ∈ s`

  `(z u')^{(k)}(z) = z · u^{(k+1)}(z) + k · u^{(k)}(z)`. -/
theorem deriv_iter_zpz {u : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (hu : ∀ m : ℕ, ContDiffOn ℝ ((m : ℕ) : WithTop ℕ∞) u s) :
    ∀ k : ℕ, ∀ z ∈ s,
      deriv^[k] (fun w => w * deriv u w) z = z * deriv^[k+1] u z + (k : ℝ) * deriv^[k] u z := by
  intro k
  induction k with
  | zero =>
      intro z _
      simp
  | succ k ih =>
      intro z hz
      have hev : deriv^[k] (fun w => w * deriv u w)
          =ᶠ[𝓝 z] (fun w => w * deriv^[k+1] u w + (k : ℝ) * deriv^[k] u w) := by
        filter_upwards [hs.mem_nhds hz] with w hw
        exact ih w hw
      rw [Function.iterate_succ_apply', hev.deriv_eq]
      have h1 : HasDerivAt (deriv^[k+1] u) (deriv^[k+2] u z) z := by
        have h := (differentiableAt_deriv_iterate hs (hu (k + 2)) hz).hasDerivAt
        rwa [show deriv (deriv^[k+1] u) z = deriv^[k+2] u z from
          (congrFun (Function.iterate_succ_apply' deriv (k + 1) u) z).symm] at h
      have h2 : HasDerivAt (deriv^[k] u) (deriv^[k+1] u z) z := by
        have h := (differentiableAt_deriv_iterate hs (hu (k + 1)) hz).hasDerivAt
        rwa [show deriv (deriv^[k] u) z = deriv^[k+1] u z from
          (congrFun (Function.iterate_succ_apply' deriv k u) z).symm] at h
      have hprod : HasDerivAt (fun w => w * deriv^[k+1] u w)
          (1 * deriv^[k+1] u z + z * deriv^[k+2] u z) z := (hasDerivAt_id z).mul h1
      have hcm : HasDerivAt (fun w => (k : ℝ) * deriv^[k] u w)
          ((k : ℝ) * deriv^[k+1] u z) z := h2.const_mul (k : ℝ)
      rw [show deriv (fun w => w * deriv^[k+1] u w + (k : ℝ) * deriv^[k] u w) z
          = 1 * deriv^[k+1] u z + z * deriv^[k+2] u z + (k : ℝ) * deriv^[k+1] u z
        from (hprod.add hcm).deriv]
      push_cast
      ring

/-! ## The radial factor `z ↦ z H'(z)` of `D_z(D_zF_*)` and its weighted derivative bounds -/

/-- `H = Hz = 2z(1-z)/(1+z)³` is `C^m` on `(-1,∞)` for every `m`. -/
theorem contDiffOn_Hz :
    ∀ m : ℕ, ContDiffOn ℝ ((m : ℕ) : WithTop ℕ∞)
      (Work.FTS.Nonlinear.FstarPkg.Hz) (Set.Ioi (-1 : ℝ)) := by
  intro m
  have hden : ∀ z ∈ Set.Ioi (-1 : ℝ), (1 + z) ^ 3 ≠ 0 := by
    intro z hz
    have hz' : (0 : ℝ) < 1 + z := by linarith [Set.mem_Ioi.mp hz]
    positivity
  show ContDiffOn ℝ ((m : ℕ) : WithTop ℕ∞) (fun z => 2 * z * (1 - z) / (1 + z) ^ 3)
    (Set.Ioi (-1 : ℝ))
  exact ((contDiffOn_const.mul contDiffOn_id).mul (contDiffOn_const.sub contDiffOn_id)).div
    ((contDiffOn_const.add contDiffOn_id).pow 3) hden

/-- **The weighted derivative bounds for the radial factor `z ↦ z H'(z)` of `D_z(D_zF_*)`.**
There is a sequence `B : ℕ → ℝ` of nonnegative constants with
`|(z+1)^k · (z H')^{(k)}(z)| ≤ B k` for all `k` and all `z ≥ 0`. -/
theorem HzDz_deriv_bound : ∃ B : ℕ → ℝ, (∀ k, 0 ≤ B k) ∧
    ∀ k : ℕ, ∀ z : ℝ, 0 ≤ z →
      |(z + 1) ^ k * deriv^[k] (fun w => w * deriv Work.FTS.Nonlinear.FstarPkg.Hz w) z|
        ≤ B k := by
  refine ⟨fun k => Work.FTS.Nonlinear.FstarPkg.HB (k + 1)
      + (k : ℝ) * Work.FTS.Nonlinear.FstarPkg.HB k, ?_, ?_⟩
  · intro k
    have h1 : 0 ≤ Work.FTS.Nonlinear.FstarPkg.HB (k + 1) :=
      Work.FTS.Nonlinear.FstarPkg.HB_nonneg (k + 1)
    have h2 : 0 ≤ Work.FTS.Nonlinear.FstarPkg.HB k := Work.FTS.Nonlinear.FstarPkg.HB_nonneg k
    positivity
  · intro k z hz
    have hz1 : (-1 : ℝ) < z := by linarith
    have hzp : (0 : ℝ) < z + 1 := by linarith
    rw [deriv_iter_zpz isOpen_Ioi contDiffOn_Hz k z hz1]
    have hA : |(z + 1) ^ k * z * deriv^[k+1] Work.FTS.Nonlinear.FstarPkg.Hz z|
        ≤ Work.FTS.Nonlinear.FstarPkg.HB (k + 1) := by
      have h := Work.FTS.Nonlinear.FstarPkg.Hz_deriv_bound (k + 1) z hz
      have hfac : z * ((z + 1) ^ k * deriv^[k+1] Work.FTS.Nonlinear.FstarPkg.Hz z)
          = (z / (z + 1)) * ((z + 1) ^ (k + 1)
              * deriv^[k+1] Work.FTS.Nonlinear.FstarPkg.Hz z) := by
        field_simp
        ring
      have h0 : 0 ≤ z / (z + 1) := div_nonneg hz hzp.le
      have h1 : z / (z + 1) ≤ 1 := by
        rw [div_le_one hzp]
        linarith
      rw [show (z + 1) ^ k * z * deriv^[k+1] Work.FTS.Nonlinear.FstarPkg.Hz z
            = z * ((z + 1) ^ k * deriv^[k+1] Work.FTS.Nonlinear.FstarPkg.Hz z) by ring,
        hfac, abs_mul, abs_of_nonneg h0]
      calc z / (z + 1) * |(z + 1) ^ (k + 1) * deriv^[k+1] Work.FTS.Nonlinear.FstarPkg.Hz z|
          ≤ 1 * Work.FTS.Nonlinear.FstarPkg.HB (k + 1) :=
            mul_le_mul h1 h (abs_nonneg _) zero_le_one
        _ = Work.FTS.Nonlinear.FstarPkg.HB (k + 1) := one_mul _
    have hB : |(z + 1) ^ k * ((k : ℝ) * deriv^[k] Work.FTS.Nonlinear.FstarPkg.Hz z)|
        ≤ (k : ℝ) * Work.FTS.Nonlinear.FstarPkg.HB k := by
      rw [show (z + 1) ^ k * ((k : ℝ) * deriv^[k] Work.FTS.Nonlinear.FstarPkg.Hz z)
            = (k : ℝ) * ((z + 1) ^ k * deriv^[k] Work.FTS.Nonlinear.FstarPkg.Hz z) by ring,
        abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
      exact mul_le_mul_of_nonneg_left (Work.FTS.Nonlinear.FstarPkg.Hz_deriv_bound k z hz)
        (Nat.cast_nonneg k)
    have hsplit : (z + 1) ^ k * (z * deriv^[k+1] Work.FTS.Nonlinear.FstarPkg.Hz z
          + (k : ℝ) * deriv^[k] Work.FTS.Nonlinear.FstarPkg.Hz z)
        = (z + 1) ^ k * z * deriv^[k+1] Work.FTS.Nonlinear.FstarPkg.Hz z
          + (z + 1) ^ k * ((k : ℝ) * deriv^[k] Work.FTS.Nonlinear.FstarPkg.Hz z) := by
      ring
    rw [hsplit]
    exact le_trans (abs_add_le _ _) (add_le_add hA hB)

/-! ## The separated form of `D_z(D_zF_*)` -/

/-- **`D_z(D_zF_*)` is the separated product `((α/c)·Γ) ⊗ (z·H')` on `z > -1`**, with
`H = Hz = 2z(1-z)/(1+z)³` the radial factor of `D_zF_*`. -/
lemma DzDzFstar_eq_sep {α : ℝ} (hα : 0 < α) :
    ∀ z : ℝ, -1 < z → ∀ θ : ℝ,
      Work.Spaces.Dz (Work.Spaces.Dz (Work.Construction.Fstar α)) z θ
        = (α / Work.Spaces.c α * Work.Spaces.Gam α θ)
            * (z * deriv Work.FTS.Nonlinear.FstarPkg.Hz z) := by
  intro z hz θ
  have hev : (fun z' : ℝ => Work.Spaces.Dz (Work.Construction.Fstar α) z' θ)
      =ᶠ[𝓝 z] fun z' : ℝ => α / Work.Spaces.c α
        * (Work.Spaces.Gam α θ * Work.FTS.Nonlinear.FstarPkg.Hz z') := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact Work.FTS.Nonlinear.FstarPkg.Dz_Fstar_eq_Hz (θ := θ) hα hz'
  show z * deriv (fun z' : ℝ => Work.Spaces.Dz (Work.Construction.Fstar α) z' θ) z
      = (α / Work.Spaces.c α * Work.Spaces.Gam α θ)
          * (z * deriv Work.FTS.Nonlinear.FstarPkg.Hz z)
  rw [hev.deriv_eq,
    Work.Spaces.deriv_const_mul' (α / Work.Spaces.c α) z
      (fun z' => Work.Spaces.Gam α θ * Work.FTS.Nonlinear.FstarPkg.Hz z'),
    Work.Spaces.deriv_const_mul' (Work.Spaces.Gam α θ) z Work.FTS.Nonlinear.FstarPkg.Hz]
  ring

/-- **The `W5` data of the fixed profile `D_zF_*`.**  Same shape as `W5DthFstar`, for
`F = Dz F_*`: the new facts are `WlInfMem α 4 (Dz (Dz F_*))` (`= WlInfMem α 4 (DzIter 2 F_*)`),
`WlInfMem α 4 (Dth (Dz F_*))` and the two corresponding `WlInf`-bounds.

Available: `Work.FTS.StrongPersist.DzFstar_W6` gives `WlInfMem α 6 (Dz F_*)` with norm `≤ Cα`, and
`Work.FTS.StrongPersist.H6Rows.Npair6BWork.fstarDat` gives `SmoothOpen` and `WlInfMem α 6 (F_*)`
with the pointwise slot bounds `|mixed j i F_* z θ| ≤ C α (z/(1+z)²)(…)` for `j + i ≤ 6`.

Direct slot route (recommended, and the only one needed): every slot of `WlInf α 4 (Dz (Dz F_*))`
or of `WlInf α 4 (Dth (Dz F_*))` is — after `pzIter k (Dz g) = z·pzIter (k+1) g + k·pzIter k g` and
`DthIter j (Dz g) = Dz (DthIter j g)` — a `pzIter`-iterate of `mixed b a F_*` with `a + b ≤ 6`,
hence dominated pointwise by the `fstarDat` slot bound; finish with `Work.Spaces.supAbs_le`.
`a` may depend on `α`. -/
theorem W5DzFstar : ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∃ a : ℝ, 0 < a ∧
    Work.FTS.StrongEps.H5.W5 α (Work.Spaces.Dz (Work.Construction.Fstar α)) a := by
  obtain ⟨C, _hCpos, hdat⟩ := Work.FTS.StrongPersist.H6Rows.Npair6BWork.fstarDat
  obtain ⟨K, _hKpos, hKgam⟩ := Work.FTS.StrongPersist.W6Aux.dthGamWeightLe7
  obtain ⟨B, _hBnn, hB⟩ := HzDz_deriv_bound
  intro α hαIoc
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  obtain ⟨_hsmF, _hsmDth, hsmDz, _hFmem, _hFle, _hDthmem, _hDthle, hDzmem, hDzle, _hslot⟩ :=
    hdat α hαIoc
  -- ### the level-`4` and level-`5` data of `D_zF_*`
  have hDzmem4 : Work.Spaces.WlInfMem α 4 (Work.Spaces.Dz (Work.Construction.Fstar α)) :=
    (WlInfMem_mono (α := α) (l := 6) (l' := 4) (by norm_num) hDzmem).1
  have hDzle4 : Work.Spaces.WlInf α 4 (Work.Spaces.Dz (Work.Construction.Fstar α)) ≤ C * α :=
    le_trans (WlInfMem_mono (α := α) (l := 6) (l' := 4) (by norm_num) hDzmem).2 hDzle
  have hDzmem5 : Work.Spaces.WlInfMem α 5 (Work.Spaces.Dz (Work.Construction.Fstar α)) :=
    (WlInfMem_mono (α := α) (l := 6) (l' := 5) (by norm_num) hDzmem).1
  have hDzle5 : Work.Spaces.WlInf α 5 (Work.Spaces.Dz (Work.Construction.Fstar α)) ≤ C * α :=
    le_trans (WlInfMem_mono (α := α) (l := 6) (l' := 5) (by norm_num) hDzmem).2 hDzle
  -- ### `D_θ(D_zF_*)`: one `D_θ`-derivative costs one level of the `𝒲`-norm
  have hDthDz := Work.FTS.StrongEps.H5.WlInfMem_Dth (l := 4) hα hα1 hDzmem5
  -- ### `D_z(D_zF_*)`: the separated product `A ⊗ H`
  have hc1 : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hcoef : |α / Work.Spaces.c α| ≤ 10 * α := by
    rw [abs_of_nonneg (div_nonneg hα.le hcpos.le), div_le_iff₀ hcpos]
    nlinarith
  set A : ℝ → ℝ := fun θ => α / Work.Spaces.c α * Work.Spaces.Gam α θ with hAdef
  set H : ℝ → ℝ := fun z => z * deriv Work.FTS.Nonlinear.FstarPkg.Hz z with hHdef
  set Aj : ℕ → ℝ := fun _ => 10 * α * max (Work.Spaces.tBound 0 0) (K * α) with hAjdef
  have hA0 : ∀ θ ∈ Work.Spaces.Iθ, |A θ| ≤ 10 * α := by
    intro θ hθ
    have h2 := Work.Spaces.Gam_bounds α θ hα hθ
    rw [hAdef, abs_mul]
    calc |α / Work.Spaces.c α| * |Work.Spaces.Gam α θ|
        = |α / Work.Spaces.c α| * Work.Spaces.Gam α θ := by rw [abs_of_nonneg h2.1]
      _ ≤ (10 * α) * 1 := mul_le_mul hcoef h2.2 h2.1 (by positivity)
      _ = 10 * α := by ring
  have hAj : ∀ j : ℕ, 1 ≤ j → j ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |(Work.Spaces.dthU^[j]) A θ * Work.FTS.Nonlinear.FstarPkg.DthAux.Wt α θ| ≤ Aj j := by
    intro j hj1 hj4 θ hθ
    have hiter : (Work.Spaces.dthU^[j]) A θ
        = (α / Work.Spaces.c α) * (Work.Spaces.dthU^[j])
            (fun t => Work.Spaces.Gam α t) θ := by
      rw [hAdef, Work.Spaces.dthU_iter_const_mul j (α / Work.Spaces.c α)
        (fun t => Work.Spaces.Gam α t)]
    have hb : |(Work.Spaces.dthU^[j]) (fun t => Work.Spaces.Gam α t) θ
        * Work.FTS.Nonlinear.FstarPkg.DthAux.Wt α θ|
        ≤ max (Work.Spaces.tBound 0 0) (K * α) := by
      rcases lt_or_eq_of_le hj1 with hj2 | hj1'
      · have hw := Work.FTS.Nonlinear.FstarPkg.DthAux.Wt_nonneg hα hθ
        rw [abs_mul, abs_of_nonneg hw]
        exact le_trans (hKgam j (by omega) (by omega) α hα hα1 θ hθ) (le_max_right _ _)
      · have hjeq : j = 1 := hj1'.symm
        subst hjeq
        have h1 := Work.Spaces.dthU_Gam_le 1 (le_refl 1) α hα hα1 θ hθ
        have hw := Work.FTS.Nonlinear.FstarPkg.DthAux.Wt_nonneg hα hθ
        have h2 := Work.FTS.Nonlinear.FstarPkg.DthAux.alpha_Gam_Wt_le_one
          (α := α) (θ := θ) hα hθ
        have ht : 0 ≤ Work.Spaces.tBound 0 0 := Work.Spaces.tBound_nonneg 0 0
        have h3 : |(Work.Spaces.dthU^[1]) (fun t => Work.Spaces.Gam α t) θ
            * Work.FTS.Nonlinear.FstarPkg.DthAux.Wt α θ| ≤ Work.Spaces.tBound 0 0 := by
          rw [abs_mul, abs_of_nonneg hw]
          calc |(Work.Spaces.dthU^[1]) (fun t => Work.Spaces.Gam α t) θ|
                * Work.FTS.Nonlinear.FstarPkg.DthAux.Wt α θ
              ≤ (α * Work.Spaces.tBound 0 0 * Work.Spaces.Gam α θ)
                * Work.FTS.Nonlinear.FstarPkg.DthAux.Wt α θ :=
                mul_le_mul_of_nonneg_right h1 hw
            _ = Work.Spaces.tBound 0 0
                * (α * Work.Spaces.Gam α θ * Work.FTS.Nonlinear.FstarPkg.DthAux.Wt α θ) := by
                ring
            _ ≤ Work.Spaces.tBound 0 0 * 1 := mul_le_mul_of_nonneg_left h2 ht
            _ = Work.Spaces.tBound 0 0 := mul_one _
        exact le_trans h3 (le_max_left _ _)
    have hsplit : (α / Work.Spaces.c α) * (Work.Spaces.dthU^[j])
          (fun t => Work.Spaces.Gam α t) θ
        * Work.FTS.Nonlinear.FstarPkg.DthAux.Wt α θ
        = (α / Work.Spaces.c α) * ((Work.Spaces.dthU^[j])
            (fun t => Work.Spaces.Gam α t) θ
          * Work.FTS.Nonlinear.FstarPkg.DthAux.Wt α θ) := by ring
    rw [hiter, hsplit, abs_mul]
    calc |α / Work.Spaces.c α| * |(Work.Spaces.dthU^[j])
            (fun t => Work.Spaces.Gam α t) θ
          * Work.FTS.Nonlinear.FstarPkg.DthAux.Wt α θ|
        ≤ (10 * α) * max (Work.Spaces.tBound 0 0) (K * α) :=
          mul_le_mul hcoef hb (abs_nonneg _) (by positivity)
      _ = Aj j := by rw [hAjdef]
  have hH : ∀ k : ℕ, k ≤ 4 → ∀ z : ℝ, 0 ≤ z →
      |(z + 1) ^ k * deriv^[k] H z| ≤ B k := by
    intro k _ z hz
    rw [hHdef]
    exact hB k z hz
  have hsep : Work.Spaces.WlInfMem α 4 (fun z θ => A θ * H z) ∧
      Work.Spaces.WlInf α 4 (fun z θ => A θ * H z) ≤ sepBnd 4 (10 * α) Aj B :=
    WlInf_sep (l := 4) hA0 hAj hH
  have hcongr := Work.FTS.Nonlinear.FstarPkg.WlInf_congr (α := α) (l := 4)
    (f := Work.Spaces.Dz (Work.Spaces.Dz (Work.Construction.Fstar α)))
    (g := fun z θ => A θ * H z)
    (fun z hz θ => DzDzFstar_eq_sep hα z hz θ)
  set sb1 : ℝ := sepBnd 4 (10 * α) Aj B with hsb1
  set sb2 : ℝ := (α + 1) * (C * α) with hsb2
  refine ⟨max 1 (max (C * α) (max sb1 sb2)), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  refine ⟨hsmDz, hDzmem4, ?_, hsmDz.Dz, hcongr.2.mpr hsep.1, ?_, hsmDz.Dth, hDthDz.1, ?_⟩
  · calc Work.Spaces.WlInf α 4 (Work.Spaces.Dz (Work.Construction.Fstar α)) ≤ C * α := hDzle4
      _ ≤ max 1 (max (C * α) (max sb1 sb2)) :=
          le_trans (le_max_left (C * α) (max sb1 sb2))
            (le_max_right 1 (max (C * α) (max sb1 sb2)))
  · calc Work.Spaces.WlInf α 4 (Work.Spaces.Dz (Work.Spaces.Dz (Work.Construction.Fstar α)))
        = Work.Spaces.WlInf α 4 (fun z θ => A θ * H z) := hcongr.1
      _ ≤ sb1 := by rw [hsb1]; exact hsep.2
      _ ≤ max 1 (max (C * α) (max sb1 sb2)) :=
          le_trans (le_max_left sb1 sb2)
            (le_trans (le_max_right (C * α) (max sb1 sb2))
              (le_max_right 1 (max (C * α) (max sb1 sb2))))
  · calc Work.Spaces.WlInf α 4 (Work.Spaces.Dth (Work.Spaces.Dz (Work.Construction.Fstar α)))
        ≤ (α + 1) * Work.Spaces.WlInf α 5 (Work.Spaces.Dz (Work.Construction.Fstar α)) :=
          hDthDz.2
      _ ≤ (α + 1) * (C * α) := mul_le_mul_of_nonneg_left hDzle5 (by linarith)
      _ = sb2 := by rw [hsb2]
      _ ≤ max 1 (max (C * α) (max sb1 sb2)) :=
          le_trans (le_max_right sb1 sb2)
            (le_trans (le_max_right (C * α) (max sb1 sb2))
              (le_max_right 1 (max (C * α) (max sb1 sb2))))

end Work.FTS.StrongEps.H5.Atoms
