/-
Copyright: work module for the Elgindi finite-time singularity project.

# The weighted profile `(1+z)²/z · F_*`

This proves the design statement `Fstar_z_W` of `FTS/N45_DESIGN_LEAD.md` §3.2 (row of the
table of `Submission/Work/FTS/Nonlinear/NOTES_N4.md`, §"F_* package"):

  `𝒲^{4,∞}((1+z)²/z · F_*) ≤ C α`, with `C` universal, for every `0 < α ≤ 1`.

## Mathematics

Since `F_*(z,θ) = (2α/c) Γ(θ) · z/(1+z)²` (`Fstar_eq_factored`), we have, for `z ≠ 0`,

  `(1+z)²/z · F_*(z,θ) = (2α/c) Γ(θ) · ((1+z)²/z · z/(1+z)²) = (2α/c) Γ(θ) · 1`.

So the weighted profile is (away from the single point `z = 0`) *constant in `z`*, equal to
the angular function `(2α/c) Γ(θ)`.  Its `z`-derivatives therefore vanish — the whole
content of the estimate is angular.

Formally, write `φ z = (1+z)²/z · hKer z` (`hKer z = z/(1+z)²`).  Then `φ z = 1` for
`z ∉ {0,-1}` and `φ z = 0` for `z = 0` and `z = -1`, so `φ` is equal to a constant along
the punctured neighbourhood of every point; by the junk-value convention for `deriv`
(`deriv` is `0` at a non-differentiable point) this forces `deriv^[k] φ = 0` for all
`k ≥ 1`.  Since `F_*` separates, `pzIter k (gphi α) = A · deriv^[k] φ` with
`A = (2α/c)Γ` (and likewise for the `D_θ`-iterates), so all `z`-derivative summands of
`𝒲^{4,∞}` with `k ≥ 1` vanish identically, and the surviving ones are bounded by the
angular estimates of the paper's `ΓRegularity` (`Gam_bounds`, `dthU_Gam_le`,
`Gam_mul_weight_le`, `c_bounds`) times the single factor `α`.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.FTS.Nonlinear.Defs
import Submission.Work.FTS.Nonlinear.FstarPkg.Fstar_W

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.FstarPkg

set_option autoImplicit false

/-! ## The singular factor `φ(z) = (1+z)²/z · hKer z` -/

/-- `φ z = ((z+1)^2/z)·hKer z`, where `hKer z = z/(1+z)^2`.  It equals `1` for
`z ∉ {0,-1}` and `0` at `z = 0` and `z = -1`. -/
def phi (z : ℝ) : ℝ := (z + 1) ^ 2 / z * Work.Spaces.hKer z

lemma phi_eq_one {z : ℝ} (hz : z ≠ 0) (hz1 : z ≠ -1) : phi z = 1 := by
  have h1 : (1 + z : ℝ) ≠ 0 := by intro h; exact hz1 (by linarith)
  rw [phi, Work.Spaces.hKer_apply, show (1 + z) ^ 2 = (z + 1) ^ 2 by ring]
  field_simp
  exact div_self (by intro h; exact h1 (by linarith))

lemma phi_zero : phi 0 = 0 := by
  rw [phi, Work.Spaces.hKer_apply]; norm_num

lemma phi_neg_one : phi (-1) = 0 := by
  rw [phi, Work.Spaces.hKer_apply]; norm_num

lemma phi_abs_le_one (z : ℝ) : |phi z| ≤ 1 := by
  rcases eq_or_ne z 0 with rfl | hz
  · rw [phi_zero]; norm_num
  · rcases eq_or_ne z (-1) with rfl | hz1
    · rw [phi_neg_one]; norm_num
    · rw [phi_eq_one hz hz1, abs_one]

/-- Points of the domain `Iz = [0,∞)` are never `-1`. -/
lemma Iz_ne_neg_one {z : ℝ} (hz : z ∈ Work.Spaces.Iz) : z ≠ -1 := by
  intro h
  have h2 : (0 : ℝ) ≤ z := hz
  rw [h] at h2
  norm_num at h2

/-- `φ` is eventually equal to `1` along the punctured neighbourhood of every point: the
only points where `φ ≠ 1` are `z = 0` and `z = -1`. -/
lemma eventually_phi_eq_one (x : ℝ) : ∀ᶠ z in 𝓝[≠] x, phi z = 1 := by
  rw [eventually_nhdsWithin_iff]
  rcases eq_or_ne x 0 with rfl | hx0
  · filter_upwards [(isOpen_ne (x := (-1:ℝ))).mem_nhds (by norm_num : (0:ℝ) ≠ -1)]
      with z hzm1 hzx
    exact phi_eq_one hzx hzm1
  · rcases eq_or_ne x (-1) with rfl | hx1
    · filter_upwards [(isOpen_ne (x := (0:ℝ))).mem_nhds (by norm_num : (-1:ℝ) ≠ 0)]
        with z hz0 hzx
      exact phi_eq_one hz0 hzx
    · filter_upwards [(isOpen_ne (x := (0:ℝ))).mem_nhds hx0,
        (isOpen_ne (x := (-1:ℝ))).mem_nhds hx1] with z hz0 hz1 hzx
      exact phi_eq_one hz0 hz1

/-! ## Vanishing of the `z`-derivatives of `φ` -/

/-- If `F` is eventually equal to the constant `K` along the punctured neighbourhood of
`x`, then `deriv F x = 0`: either `F` is discontinuous at `x` (and then Lean's `deriv`,
being the junk value `0` at a non-differentiable point, vanishes), or `F x = K` and `F` is
eventually equal to the constant `K` near `x`. -/
lemma deriv_eq_zero_of_eventually_nhdsNE_const {F : ℝ → ℝ} {x K : ℝ}
    (h : ∀ᶠ z in 𝓝[≠] x, F z = K) : deriv F x = 0 := by
  rcases em (DifferentiableAt ℝ F x) with hd | hd
  · have hKx : K = F x := by
      have h1 : Tendsto F (𝓝[≠] x) (𝓝 K) :=
        Tendsto.congr' (show (fun _ : ℝ => K) =ᶠ[𝓝[≠] x] F from by
          filter_upwards [h] with z hz; exact hz.symm) tendsto_const_nhds
      have h2 : Tendsto F (𝓝[≠] x) (𝓝 (F x)) :=
        hd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      exact tendsto_nhds_unique h1 h2
    have hev : F =ᶠ[𝓝 x] fun _ => K := by
      rw [eventually_nhdsWithin_iff] at h
      filter_upwards [h] with y hy
      by_cases hyx : y = x
      · subst hyx; exact hKx.symm
      · exact hy hyx
    rw [hev.deriv_eq, deriv_const]
  · exact deriv_zero_of_not_differentiableAt hd

lemma deriv_phi_eq_zero : deriv phi = fun _ => (0 : ℝ) := by
  funext x
  exact deriv_eq_zero_of_eventually_nhdsNE_const (eventually_phi_eq_one x)

lemma deriv_iter_const_zero (n : ℕ) :
    deriv^[n] (fun _ : ℝ => (0 : ℝ)) = fun _ => (0 : ℝ) := by
  have hd : deriv (fun _ : ℝ => (0 : ℝ)) = fun _ => (0 : ℝ) := by
    funext z
    exact deriv_const z 0
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, hd, ih]

lemma deriv_iter_phi_eq_zero {k : ℕ} (hk : 1 ≤ k) : deriv^[k] phi = fun _ => (0 : ℝ) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [Function.iterate_succ_apply, deriv_phi_eq_zero]
  exact deriv_iter_const_zero m

/-! ## The weighted profile and its derivatives -/

/-- The `(1+z)²/z`-weighted profile `z ↦ (1+z)²/z · F_*(z,θ)`. -/
def gphi (α : ℝ) : ℝ → ℝ → ℝ := fun z θ => (z + 1) ^ 2 / z * Work.Construction.Fstar α z θ

/-- The angular factor `A(θ) = (2α/c)·Γ(θ)`. -/
def Aang (α : ℝ) (θ : ℝ) : ℝ := (2 * α / Work.Spaces.c α) * Work.Spaces.Gam α θ

/-- The weighted profile factorizes through `φ`: `gphi α = Aang α ⊗ φ`. -/
lemma gphi_eq (α : ℝ) : gphi α = fun z θ => Aang α θ * phi z := by
  funext z θ
  rw [gphi, Aang, phi, Fstar_eq_factored]
  ring

/-- `dthU` commutes with the constant factor `2α/c`. -/
lemma dthU_iter_Aang (α : ℝ) (j : ℕ) :
    Work.Spaces.dthU^[j] (Aang α)
      = fun θ => (2 * α / Work.Spaces.c α)
          * (Work.Spaces.dthU^[j] (fun t => Work.Spaces.Gam α t)) θ :=
  Work.Spaces.dthU_iter_const_mul j (2 * α / Work.Spaces.c α) (fun t => Work.Spaces.Gam α t)

/-- The `D_θ`-iterates of the weighted profile. -/
lemma DthIter_gphi (α : ℝ) (j : ℕ) :
    Work.Spaces.DthIter j (gphi α) = fun z θ =>
      ((2 * α / Work.Spaces.c α)
          * (Work.Spaces.dthU^[j] (fun t => Work.Spaces.Gam α t)) θ) * phi z := by
  rw [gphi_eq]
  funext z θ
  rw [Work.Spaces.DthIter_decomp j (Aang α) phi z θ, dthU_iter_Aang α j]

/-- The `z`-derivatives of the weighted profile. -/
lemma pzIter_gphi (α : ℝ) (k : ℕ) :
    Work.Spaces.pzIter k (gphi α) = fun z θ => Aang α θ * deriv^[k] phi z := by
  rw [gphi_eq]
  funext z θ
  rw [Work.Spaces.pzIter_decomp k (Aang α) phi z θ]

/-- The mixed derivatives of the weighted profile. -/
lemma pzIter_DthIter_gphi (α : ℝ) (j k : ℕ) :
    Work.Spaces.pzIter k (Work.Spaces.DthIter j (gphi α)) = fun z θ =>
      ((2 * α / Work.Spaces.c α)
          * (Work.Spaces.dthU^[j] (fun t => Work.Spaces.Gam α t)) θ) * deriv^[k] phi z := by
  rw [DthIter_gphi]
  funext z θ
  rw [Work.Spaces.pzIter_decomp k (fun θ => (2 * α / Work.Spaces.c α)
    * (Work.Spaces.dthU^[j] (fun t => Work.Spaces.Gam α t)) θ) phi z θ]

/-! ## The pointwise estimates -/

/-- The angular factor times the angular weight is bounded by `20α·tBound (j-1) 0`. -/
lemma mixed_pointwise (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (j : ℕ) (hj : 1 ≤ j) :
    ∀ θ ∈ Work.Spaces.Iθ,
      |(2 * α / Work.Spaces.c α)
        * (Work.Spaces.dthU^[j] (fun t => Work.Spaces.Gam α t)) θ
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))|
      ≤ 20 * α * Work.Spaces.tBound (j - 1) 0 := by
  intro θ hθ
  have hcoef : |2 * α / Work.Spaces.c α| ≤ 20 * α := Fstar_coef_le α hα hα1
  have hGam := Work.Spaces.Gam_bounds α θ hα hθ
  have hdth := Work.Spaces.dthU_Gam_le j hj α hα hα1 θ hθ
  have hW0 : 0 ≤ (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) :=
    Work.Spaces.gamma_weight_nonneg α θ hα hθ
  have hgw : α * Work.Spaces.Gam α θ
      * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) ≤ 1 := by
    rw [← mul_div_assoc]
    exact Work.Spaces.Gam_mul_weight_le α θ hα hθ
  have hT0 : 0 ≤ Work.Spaces.tBound (j - 1) 0 := Work.Spaces.tBound_nonneg _ _
  have hmain : 0 ≤ 20 * α * Work.Spaces.tBound (j - 1) 0 := by
    have : (0 : ℝ) < 20 * α := by linarith
    exact mul_nonneg (le_of_lt this) hT0
  have hstep : |(2 * α / Work.Spaces.c α)
        * (Work.Spaces.dthU^[j] (fun t => Work.Spaces.Gam α t)) θ|
      ≤ 20 * α * (α * Work.Spaces.tBound (j - 1) 0 * Work.Spaces.Gam α θ) := by
    rw [abs_mul]
    exact mul_le_mul hcoef hdth (abs_nonneg _) (by linarith)
  calc |(2 * α / Work.Spaces.c α)
          * (Work.Spaces.dthU^[j] (fun t => Work.Spaces.Gam α t)) θ
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))|
      = |(2 * α / Work.Spaces.c α)
          * (Work.Spaces.dthU^[j] (fun t => Work.Spaces.Gam α t)) θ|
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) := by
        rw [abs_mul, abs_of_nonneg hW0]
    _ ≤ (20 * α * (α * Work.Spaces.tBound (j - 1) 0 * Work.Spaces.Gam α θ))
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) :=
        mul_le_mul_of_nonneg_right hstep hW0
    _ = (20 * α * Work.Spaces.tBound (j - 1) 0)
        * (α * Work.Spaces.Gam α θ
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))) := by ring
    _ ≤ (20 * α * Work.Spaces.tBound (j - 1) 0) * 1 :=
        mul_le_mul_of_nonneg_left hgw hmain
    _ = 20 * α * Work.Spaces.tBound (j - 1) 0 := by ring

/-- Each `z`-summand of `𝒲^{4,∞}` of the weighted profile is bounded by `20α`. -/
lemma gphi_zterm_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |(z + 1) ^ k * Work.Spaces.pzIter k (gphi α) z θ| ≤ 20 * α := by
  intro z hz θ hθ
  rw [pzIter_gphi]
  rcases eq_or_ne k 0 with rfl | hk0
  · simp only [pow_zero, one_mul, Function.iterate_zero_apply]
    have hcoef : |2 * α / Work.Spaces.c α| ≤ 20 * α := Fstar_coef_le α hα hα1
    have hGam := Work.Spaces.Gam_bounds α θ hα hθ
    rcases eq_or_ne z 0 with rfl | hz0
    · rw [phi_zero, mul_zero, abs_zero]; linarith
    · have hz1 : z ≠ -1 := Iz_ne_neg_one hz
      rw [phi_eq_one hz0 hz1, mul_one, Aang, abs_mul, abs_of_nonneg hGam.1]
      calc |2 * α / Work.Spaces.c α| * Work.Spaces.Gam α θ ≤ 20 * α * 1 :=
            mul_le_mul hcoef hGam.2 hGam.1 (by linarith)
        _ = 20 * α := by ring
  · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
    rw [deriv_iter_phi_eq_zero hk1]
    simp only [mul_zero, zero_mul, abs_zero]
    linarith

/-- Each mixed summand of `𝒲^{4,∞}` of the weighted profile is bounded by
`20α·tBound (j-1) 0`. -/
lemma gphi_mixedterm_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (j : ℕ) (hj : 1 ≤ j) (k : ℕ) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j (gphi α)) z θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))|
        ≤ 20 * α * Work.Spaces.tBound (j - 1) 0 := by
  intro z hz θ hθ
  rw [mul_div_assoc, pzIter_DthIter_gphi]
  have hmain := mixed_pointwise α hα hα1 j hj θ hθ
  have hT0 : 0 ≤ Work.Spaces.tBound (j - 1) 0 := Work.Spaces.tBound_nonneg _ _
  have hbound : 0 ≤ 20 * α * Work.Spaces.tBound (j - 1) 0 :=
    mul_nonneg (by linarith) hT0
  rcases eq_or_ne k 0 with rfl | hk0
  · simp only [pow_zero, one_mul, Function.iterate_zero_apply]
    rcases eq_or_ne z 0 with rfl | hz0
    · rw [phi_zero, mul_zero, zero_mul, abs_zero]; exact hbound
    · have hz1 : z ≠ -1 := Iz_ne_neg_one hz
      rw [phi_eq_one hz0 hz1, mul_one]
      exact hmain
  · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
    rw [deriv_iter_phi_eq_zero hk1]
    simp only [mul_zero, zero_mul, abs_zero]
    exact hbound

/-! ## Assembly -/

/-- The universal constant multiplying `20 α`: `5` (the `z`-summands) plus the (α-independent)
`tBound`-constants of the mixed summands that survive (`k = 0`, `1 ≤ j ≤ 4`). -/
noncomputable def KBz : ℝ :=
  5 + ∑ j ∈ Finset.range 5, ∑ k ∈ Finset.range 5,
        (if 1 ≤ j ∧ k + j ≤ 4 then Work.Spaces.tBound (j - 1) 0 else 0)

lemma KBz_nonneg : 0 ≤ KBz := by
  rw [KBz]
  refine add_nonneg (by norm_num) (Finset.sum_nonneg fun j hj => Finset.sum_nonneg fun k hk => ?_)
  split_ifs with h
  · exact Work.Spaces.tBound_nonneg _ _
  · norm_num

/-- The `𝒲^{4,∞}`-norm of the weighted profile is at most `20 α · KBz`. -/
lemma WlInf_gphi_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.Spaces.WlInf α 4 (gphi α) ≤ 20 * α * KBz := by
  have h5 : (∑ k ∈ Finset.range 5, (20 * α : ℝ)) = 20 * α * 5 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have hKB : 20 * α * KBz =
      (∑ k ∈ Finset.range 5, (20 * α : ℝ))
        + ∑ j ∈ Finset.range 5, ∑ k ∈ Finset.range 5,
            (20 * α * (if 1 ≤ j ∧ k + j ≤ 4 then Work.Spaces.tBound (j - 1) 0 else 0)) := by
    rw [KBz, mul_add, Finset.mul_sum, ← h5]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mul_sum]
  rw [Work.Spaces.WlInf, hKB]
  apply add_le_add
  · exact Finset.sum_le_sum fun k hk =>
      Work.Spaces.supAbs_le fun z hz θ hθ => gphi_zterm_bound α hα hα1 k z hz θ hθ
  · refine Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun k hk => ?_
    split_ifs with hcond
    · exact Work.Spaces.supAbs_le fun z hz θ hθ =>
        gphi_mixedterm_bound α hα hα1 j hcond.1 k z hz θ hθ
    · simp

/-- `gphi α ∈ 𝒲^{4,∞}` for `0 < α ≤ 1`.  Every `SupFinite` predicate is witnessed by the
explicit pointwise bound of `gphi_zterm_bound` / `gphi_mixedterm_bound`. -/
lemma WlInfMem_gphi (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.Spaces.WlInfMem α 4 (gphi α) := by
  constructor
  · intro k hk
    exact ⟨20 * α, fun y hy => by
      rcases hy with ⟨z, hz, θ, hθ, rfl⟩
      exact gphi_zterm_bound α hα hα1 k z hz θ hθ⟩
  · intro j hj k hk hj1 hjk
    exact ⟨20 * α * Work.Spaces.tBound (j - 1) 0, fun y hy => by
      rcases hy with ⟨z, hz, θ, hθ, rfl⟩
      exact gphi_mixedterm_bound α hα hα1 j hj1 k z hz θ hθ⟩

theorem Fstar_z_W :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
      Work.Spaces.WlInfMem α 4 (fun z θ => (z + 1) ^ 2 / z * Work.Construction.Fstar α z θ) ∧
      Work.Spaces.WlInf α 4 (fun z θ => (z + 1) ^ 2 / z * Work.Construction.Fstar α z θ) ≤ C * α := by
  refine ⟨20 * KBz + 1, by linarith [KBz_nonneg],
    fun α hα hα1 => ⟨WlInfMem_gphi α hα hα1, ?_⟩⟩
  refine le_trans (WlInf_gphi_le α hα hα1) ?_
  nlinarith [KBz_nonneg, hα]

end Work.FTS.Nonlinear.FstarPkg
