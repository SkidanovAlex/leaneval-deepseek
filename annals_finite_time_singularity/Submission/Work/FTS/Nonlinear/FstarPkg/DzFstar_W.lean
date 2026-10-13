/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `D_z F_*` package, `𝒲^{4,∞}`-part: `DzFstar_W`

This proves the design statement `DzFstar_W` of `FTS/N45_DESIGN_LEAD.md` §3.2 (row 2 of the
table of `Submission/Work/FTS/Nonlinear/NOTES_N4.md`, §"`F_*` package"):

  `𝒲^{4,∞}(D_z F_*) ≤ C α`, with `C` universal, for every `0 < α ≤ 1`,

and `D_z F_* ∈ 𝒲^{4,∞}`, where `F_*(z,θ) = α (Γ(θ)/c) · 2z/(1+z)²` is the profile of
`Work.Construction.Fstar` (paper tex 1334), `Γ(θ) = (sin θ cos²θ)^{α/3}` and
`c = ∫_{Iθ} Γ K`.

## Mathematics

By `Work.Construction.Dz_Fstar_eq`, for `z > -1`

  `D_z F_*(z,θ) = α · (Γ(θ)/c) · H(z)`,   `H(z) = Hz z = 2z(1-z)/(1+z)³`,

so `D_z F_*` is again a separated product `(angular) · (radial)`, and the argument of
`Fstar_W.lean` applies verbatim with `hKer` replaced by `Hz`:

* `Hz_deriv_bound` (own file): `|(z+1)^k H^{(k)}(z)| ≤ HB k` for `z ≥ 0`, from the closed
  form `deriv^[m] hKer = hKerClosed m` and `pzIter_hKer_bound`;
* `WlInf_Gamma_radial` (own file): the `Γ ⊗ H` `𝒲^{l,∞}`-estimate
  `𝒲^{l,∞}(D · Γ ⊗ H) ≤ |D| · (Σ_k B k + Σ_{j,k} B k · tBound (j-1) 0)`, the
  `Γ`-generalization of `Work.Spaces.Gamma_WlInf`, using `Gam_bounds`, `dthU_Gam_le` and
  `Gam_mul_weight_le` exactly as there;
* `WlInf_congr` (own file): `WlInf` only sees the values of the iterated derivatives on
  `z > -1`, which is where `Dz_Fstar_eq` holds.

With `D = α/c` and `|α/c| ≤ 10α` (`c_bounds`) the constant is `C = 10 KBdz + 1`.
-/
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.FTS.Nonlinear.Defs
import Submission.Work.Construction.Basic
import Submission.Work.Spaces.Gamma_WlInf
import Submission.Work.FTS.Nonlinear.FstarPkg.DzHzDefs
import Submission.Work.FTS.Nonlinear.FstarPkg.Hz_deriv_bound
import Submission.Work.FTS.Nonlinear.FstarPkg.WlInf_congr
import Submission.Work.FTS.Nonlinear.FstarPkg.WlInf_Gamma_radial

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

/-! ## The factorization of `D_z F_*` -/

/-- `D_z F_*` separates into the angular factor `α Γ(θ)/c` and the radial factor `Hz` of
`DzHzDefs`: for `z > -1`,

  `D_z F_*(z,θ) = (α/c) · Γ(θ) · H(z)`.

This is `Work.Construction.Dz_Fstar_eq` with the radial factor collected into `Hz`. -/
theorem Dz_Fstar_eq_Hz {α z θ : ℝ} (hα : 0 < α) (hz : -1 < z) :
    Work.Spaces.Dz (Work.Construction.Fstar α) z θ
      = (α / Work.Spaces.c α) * (Work.Spaces.Gam α θ * Hz z) := by
  rw [Work.Construction.Dz_Fstar_eq hα hz, Hz]
  ring

/-! ## The universal constant -/

/-- The universal (α-independent) constant multiplying `α` in the bound of `DzFstar_W`: the
sum over the slots of `𝒲^{4,∞}` of the radial bound `HB` times the angular coefficient
`tBound (j-1) 0`. -/
noncomputable def KBdz : ℝ :=
  (∑ k ∈ Finset.range 5, HB k)
    + ∑ j ∈ Finset.range 5, ∑ k ∈ Finset.range 5,
        (if 1 ≤ j ∧ k + j ≤ 4 then HB k * Work.Spaces.tBound (j - 1) 0 else 0)

lemma KBdz_nonneg : 0 ≤ KBdz := by
  rw [KBdz]
  refine add_nonneg (Finset.sum_nonneg fun k _ => HB_nonneg k)
    (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => ?_)
  split_ifs with h
  · exact mul_nonneg (HB_nonneg k) (Work.Spaces.tBound_nonneg _ _)
  · norm_num

/-! ## The estimate -/

theorem DzFstar_W :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
      Work.Spaces.WlInfMem α 4 (Work.Spaces.Dz (Work.Construction.Fstar α)) ∧
      Work.Spaces.WlInf α 4 (Work.Spaces.Dz (Work.Construction.Fstar α)) ≤ C * α := by
  refine ⟨10 * KBdz + 1, by linarith [KBdz_nonneg], fun α hα hα1 => ?_⟩
  -- `c(α) ≥ 1/10`, hence `|α/c| ≤ 10α`.
  have hc : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hcoef : |α / Work.Spaces.c α| ≤ 10 * α := by
    rw [abs_of_nonneg (div_nonneg hα.le hcpos.le), div_le_iff₀ hcpos]
    nlinarith
  -- `WlInf` (and `WlInfMem`) only see `z > -1`, where `D_z F_*` is the product
  -- `(α/c) · Γ ⊗ Hz`.
  have hcongr := WlInf_congr (f := Work.Spaces.Dz (Work.Construction.Fstar α))
    (g := fun z θ => (α / Work.Spaces.c α) * (Work.Spaces.Gam α θ * Hz z))
    (fun z hz θ => Dz_Fstar_eq_Hz hα hz) α 4
  -- the `Γ ⊗ Hz` estimate, with `B = HB` from the radial bound
  obtain ⟨hmem, hbound⟩ := WlInf_Gamma_radial (l := 4) (H := Hz) (B := HB)
    (D := α / Work.Spaces.c α) (α := α) hα hα1 (fun k _ z hz => Hz_deriv_bound k z hz)
  refine ⟨hcongr.2.mpr hmem, ?_⟩
  rw [hcongr.1]
  calc Work.Spaces.WlInf α 4 (fun z θ => (α / Work.Spaces.c α) * (Work.Spaces.Gam α θ * Hz z))
      ≤ |α / Work.Spaces.c α| * KBdz := hbound
    _ ≤ 10 * α * KBdz := mul_le_mul_of_nonneg_right hcoef KBdz_nonneg
    _ = 10 * KBdz * α := by ring
    _ ≤ (10 * KBdz + 1) * α := by nlinarith [hα, KBdz_nonneg]

end Work.FTS.Nonlinear.FstarPkg
