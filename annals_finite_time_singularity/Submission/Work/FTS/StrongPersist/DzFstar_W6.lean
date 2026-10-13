import Mathlib.Algebra.Order.Star.Real
import Submission.Work.FTS.Nonlinear.FstarPkg.DzFstar_W

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `D_z F_*` package at order `6`: `DzFstar_W6`

The radial derivative of the fundamental profile,
`D_z F_*(z,θ) = α · (Γ(θ)/c(α)) · H(z)` with `H(z) = 2z(1-z)/(1+z)³`
(`Work.FTS.Nonlinear.FstarPkg.Dz_Fstar_eq_Hz`), satisfies

  `D_z F_* ∈ 𝒲^{6,∞}`  and  `|D_z F_*|_{𝒲^{6,∞}} ≤ C α`,  `C` universal, for every `0 < α ≤ 1`.

The level-`4` version of this statement is `Work.FTS.Nonlinear.FstarPkg.DzFstar_W`.  Nothing in
that proof used the bound `4`: the generic estimate
`Work.FTS.Nonlinear.FstarPkg.WlInf_Gamma_radial` is stated for an *arbitrary* level `l`, the
radial weighted bound `Hz_deriv_bound` holds for *every* `k`, and the norms only depend on the
values on `z > -1` (`WlInf_congr`).  So the whole `𝒲^{6,∞}`-bound follows by re-running the
assembly with `4 ↦ 6`.  We prove the general statement `DzFstar_Wl l` once and specialize.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

set_option autoImplicit false

/-! ## The universal constant -/

/-- The universal (`α`-independent) constant multiplying `|α/c|` in the `𝒲^{l,∞}`-bound for
`D_z F_*`: the sum over the slots of `𝒲^{l,∞}` of the radial bound `HB` times the angular
coefficient `tBound (j-1) 0`.  This is the level-`l` analogue of
`Work.FTS.Nonlinear.FstarPkg.KBdz`. -/
noncomputable def DzKB (l : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (l + 1), Work.FTS.Nonlinear.FstarPkg.HB k)
    + ∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
        (if 1 ≤ j ∧ k + j ≤ l then
          Work.FTS.Nonlinear.FstarPkg.HB k * Work.Spaces.tBound (j - 1) 0 else 0)

lemma DzKB_nonneg (l : ℕ) : 0 ≤ DzKB l := by
  rw [DzKB]
  refine add_nonneg (Finset.sum_nonneg fun k _ => Work.FTS.Nonlinear.FstarPkg.HB_nonneg k) ?_
  refine Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => ?_
  split_ifs with h
  · exact mul_nonneg (Work.FTS.Nonlinear.FstarPkg.HB_nonneg k) (Work.Spaces.tBound_nonneg _ _)
  · norm_num

/-! ## The estimate at a general level -/

/-- `D_z F_* ∈ 𝒲^{l,∞}` with `|D_z F_*|_{𝒲^{l,∞}} ≤ (10 · DzKB l + 1) α`, for all `0 < α ≤ 1`.

The proof is the level-`4` proof of `Work.FTS.Nonlinear.FstarPkg.DzFstar_W` with `4 ↦ l`:
`D_z F_*` agrees on `z > -1` with the separated product `(α/c) · Γ ⊗ Hz`, whose `𝒲^{l,∞}`-norm
is bounded by `|α/c| · DzKB l` by `WlInf_Gamma_radial`, and `|α/c| ≤ 10 α` by `c_bounds`. -/
theorem DzFstar_Wl (l : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
      Work.Spaces.WlInfMem α l (Work.Spaces.Dz (Work.Construction.Fstar α)) ∧
      Work.Spaces.WlInf α l (Work.Spaces.Dz (Work.Construction.Fstar α)) ≤ C * α := by
  refine ⟨10 * DzKB l + 1, by linarith [DzKB_nonneg l], fun α hα hα1 => ?_⟩
  -- `c(α) ≥ 1/10`, hence `|α/c| ≤ 10α`.
  have hc : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hcoef : |α / Work.Spaces.c α| ≤ 10 * α := by
    rw [abs_of_nonneg (div_nonneg hα.le hcpos.le), div_le_iff₀ hcpos]
    nlinarith
  -- `WlInf` (and `WlInfMem`) only see `z > -1`, where `D_z F_*` is the product
  -- `(α/c) · Γ ⊗ Hz`.
  have hcongr := Work.FTS.Nonlinear.FstarPkg.WlInf_congr
    (f := Work.Spaces.Dz (Work.Construction.Fstar α))
    (g := fun z θ => (α / Work.Spaces.c α)
      * (Work.Spaces.Gam α θ * Work.FTS.Nonlinear.FstarPkg.Hz z))
    (fun z hz θ => Work.FTS.Nonlinear.FstarPkg.Dz_Fstar_eq_Hz hα hz) α l
  -- the `Γ ⊗ Hz` estimate, with `B = HB` from the radial bound
  obtain ⟨hmem, hbound⟩ := Work.FTS.Nonlinear.FstarPkg.WlInf_Gamma_radial (l := l)
    (H := Work.FTS.Nonlinear.FstarPkg.Hz) (B := Work.FTS.Nonlinear.FstarPkg.HB)
    (D := α / Work.Spaces.c α) (α := α) hα hα1
    (fun k _ z hz => Work.FTS.Nonlinear.FstarPkg.Hz_deriv_bound k z hz)
  refine ⟨hcongr.2.mpr hmem, ?_⟩
  rw [hcongr.1]
  calc Work.Spaces.WlInf α l
        (fun z θ => (α / Work.Spaces.c α)
          * (Work.Spaces.Gam α θ * Work.FTS.Nonlinear.FstarPkg.Hz z))
      ≤ |α / Work.Spaces.c α| * DzKB l := hbound
    _ ≤ 10 * α * DzKB l := mul_le_mul_of_nonneg_right hcoef (DzKB_nonneg l)
    _ = 10 * DzKB l * α := by ring
    _ ≤ (10 * DzKB l + 1) * α := by nlinarith [hα, DzKB_nonneg l]

/-! ## The requested statement -/

theorem DzFstar_W6 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 →
    Work.Spaces.WlInfMem α 6 (Work.Spaces.Dz (Work.Construction.Fstar α)) ∧
    Work.Spaces.WlInf α 6 (Work.Spaces.Dz (Work.Construction.Fstar α)) ≤ C * α :=
  DzFstar_Wl 6

end Work.FTS.StrongPersist
