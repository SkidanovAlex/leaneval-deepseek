/-
# `PieceStarBnd` — the star-piece pairing bound at level six

The level-six `N`-row pairs the nonlinear term with the perturbation `f`

  `IP6 1 1 1 1 1 1 1 1 1 1 α (N α (F_*+f) (Φs+Ef)) f`

and splits `N` into twenty pieces `A·P` (`Npair6SupAux/NDefs.lean`).  The `Ξ₁`- (star-)
coefficient pieces are of the shape `A·B·P` with `A` a `𝒲^{6,∞}`-field, `B ∈ ℋ⁶` and `P`
one of the slots `f`, `D_θf`, `D_zf`; for those the pairing bound needed downstream is

  `|IP6 1…1 α (A·B) f| ≤ C α^{-1/2} |A|_{𝒲^{6,∞}} |B|_{ℋ⁶} |f|_{ℋ⁶}`,

with the two functional-space norms priced by the two *constants* `KA`, `KB`.

## The two ingredients

The proof is the composition of the two *proved* level-six bounds:

* `hknorm_mul_of_WlInf6_cd6` (`Npair6SupAux/hknorm_mul_of_WlInf6_cd6.lean`) — the
  `𝒲^{6,∞}`-priced product rule with `C^6` data,
  `|A·B|_{ℋ⁶} ≤ C α^{-1/2} |A|_{𝒲^{6,∞}} |B|_{ℋ⁶}`.  That file states its range as
  `α ∈ (0, α₂]` with an existential `α₂`; the auxiliary `hknorm_mul_aux6` underlying it
  works verbatim for `α ≤ 1`, which is the range this file needs, so
  `hknorm_mul_of_WlInf6_le1` below re-runs it with the slot lemmas of `Cd6` instantiated at
  `α ≤ 1`.
* `ip6_cs_cd` (`Npair6SupAux/ip6_cs_cd.lean`) — the `C^6` Cauchy–Schwarz for the level-six
  pairing, `|IP6 1…1 α u v| ≤ CC |u|_{ℋ⁶} |v|_{ℋ⁶}`.  Again the range is stated with an
  existential; `ip6_cs_le1` below is the `α ≤ 1` instance.

Since the first argument `A·B` of the pairing is *fixed*, the Cauchy–Schwarz bound
`|IP6 α (A·B) f| ≤ CC |A·B|_{ℋ⁶} |f|_{ℋ⁶}` is already **linear** in `|f|_{ℋ⁶}`, and
substituting the product rule gives exactly the requested shape with constant `CC · C₀`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.NDefs
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.hknorm_mul_of_WlInf6_cd6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.ip6_cs_cd
import Submission.Work.FTS.StrongPersist.H6Rows.piecesC6

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6SupAux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The two level-six bounds, in the range `α ≤ 1` -/

/-- **The `𝒲^{6,∞}`-priced product rule with `C^6` data, for `α ≤ 1`.**  If `f` is `C^6` on the
open quadrant and of class `𝒲^{6,∞}`, and `g` is `C^6` on the open quadrant and of class `ℋ⁶`,
then
`|f·g|_{ℋ⁶} ≤ C α^{-1/2} |f|_{𝒲^{6,∞}} |g|_{ℋ⁶}`.

This is `hknorm_mul_aux6` (the auxiliary of `Npair6SupAux/hknorm_mul_of_WlInf6_cd6.lean`)
instantiated with the three `C^6` slot lemmas of `N0pair6bWork.Cd6`, all of which are stated
for `0 < α ≤ 1`. -/
theorem hknorm_mul_of_WlInf6_le1 : ∃ C : ℝ, 0 < C ∧
    ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ f g : Work.FTS.Galerkin.Fn,
      ContDiffOn ℝ 6 (Function.uncurry f) Work.FTS.EllipticEst.Q0 →
      Work.Spaces.WlInfMem α 6 f →
      ContDiffOn ℝ 6 (Function.uncurry g) Work.FTS.EllipticEst.Q0 →
      Work.Spaces.HkMem α 6 g →
      Work.Spaces.HkNorm α 6 (fun z θ => f z θ * g z θ)
        ≤ C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 6 f
            * Work.Spaces.HkNorm α 6 g := by
  obtain ⟨Cz, hCz, hZ⟩ :=
    Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.zslot_le_winf6_cd6
  obtain ⟨CB, _hCB, hCBmean⟩ :=
    Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.dzIter_w_mean_le6_cd6
  obtain ⟨Cm, hCm, hMx⟩ :=
    Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.mslot_le_winf6_cd6 CB
  refine ⟨Real.sqrt ((7 * Cz + 49 * Cm) * 42701), Real.sqrt_pos.mpr (by positivity), ?_⟩
  intro α hα hα1 f g hfs hfw hgs hgm
  exact (hknorm_mul_aux6 hα hα1 hfs hfw hgs hgm hCz hCm
    (fun i hi z θ hz hθ0 hθ1 => hZ α f g hα hα1 hfs hfw hgs i hi z θ hz hθ0 hθ1)
    (fun I J hI hIJ z θ hz hθ0 hθ1 => hMx α f g hα hα1 hfs hfw hgs hgm
      (fun d hd z' θ' hz' hθ0' hθ1' =>
        hCBmean α g d hα hα1 hgs hgm hd z' θ' hz' hθ0' hθ1')
      I J hI hIJ z θ hz hθ0 hθ1)).2

/-- **Cauchy–Schwarz for `IP6 1 … 1` at finite smoothness order, for `α ≤ 1`.**
`|IP6 1…1 α u v| ≤ CC |u|_{ℋ⁶} |v|_{ℋ⁶}` for `u`, `v` of class `C⁶` on the open quadrant and
honestly in `ℋ⁶`.

This is the `α ≤ 1` instance of `Npair6SupAux/ip6_cs_cd.lean`, whose proof uses only the
positivity of `α` (the existential upper end `α₂` of that statement is a red herring: the
underlying chain `Transfer.CSQ_iter` is `α`-free). -/
theorem ip6_cs_le1 : ∃ CC : ℝ, 0 < CC ∧
    ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ u v : Work.FTS.Galerkin.Fn,
      ContDiffOn ℝ 6 (Function.uncurry u) Work.FTS.EllipticEst.Q0 →
      ContDiffOn ℝ 6 (Function.uncurry v) Work.FTS.EllipticEst.Q0 →
      Work.Spaces.HkMem α 6 u → Work.Spaces.HkMem α 6 v →
      |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α u v|
        ≤ CC * Work.Spaces.HkNorm α 6 u * Work.Spaces.HkNorm α 6 v := by
  have hmax : (0 : ℝ) < (3 : ℝ) * max 1 (max 1 1) := by
    rw [show max 1 (max 1 1) = (1 : ℝ) from by simp]
    norm_num
  refine ⟨((3 : ℝ) * max 1 (max 1 1)) ^ 5 * (10 : ℝ) ^ 22,
    mul_pos (pow_pos hmax 5) (by norm_num), ?_⟩
  intro α hα hα1 u v hu hv hmu hmv
  have h := CSQ_iter α hα 5
  have hIP6 : Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α = IPit α 5 := rfl
  rw [hIP6]
  exact h u v hu hv hmu hmv

/-! ## The target -/

theorem PieceStarBnd : ∃ C : ℝ, 0 < C ∧ ∀ {α KA KB : ℝ} {Aa Ba f : Work.FTS.Galerkin.Fn},
    0 < α → α ≤ 1 → 0 ≤ KA → 0 ≤ KB →
    ContDiffOn ℝ 6 (Function.uncurry Aa) Work.FTS.EllipticEst.Q0 →
    Work.Spaces.WlInfMem α 6 Aa → Work.Spaces.WlInf α 6 Aa ≤ KA →
    ContDiffOn ℝ 6 (Function.uncurry Ba) Work.FTS.EllipticEst.Q0 →
    Work.Spaces.HkMem α 6 Ba → Work.Spaces.HkNorm α 6 Ba ≤ KB →
    Work.FTS.StrongPersist.H6Adm α f →
    |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α (fun z θ => Aa z θ * Ba z θ) f|
      ≤ C * α ^ (-(1 / 2 : ℝ)) * KA * KB * Work.Spaces.HkNorm α 6 f := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := hknorm_mul_of_WlInf6_le1
  obtain ⟨CC, hCCpos, hCC⟩ := ip6_cs_le1
  refine ⟨CC * C₀, mul_pos hCCpos hC₀pos, ?_⟩
  intro α KA KB Aa Ba f hα hα1 hKA hKB hAacd hAawl hAab hBacd hBamem hBanb hadm
  -- the product `Aa · Ba` is `C⁶` on the open quadrant
  have hucd : ContDiffOn ℝ 6 (Function.uncurry (fun z θ => Aa z θ * Ba z θ))
      Work.FTS.EllipticEst.Q0 := by
    have h : Function.uncurry (fun z θ => Aa z θ * Ba z θ)
        = Function.uncurry Aa * Function.uncurry Ba := by
      funext p
      obtain ⟨z, θ⟩ := p
      rfl
    rw [h]
    exact hAacd.mul hBacd
  -- the product is honestly in `ℋ⁶` ...
  have hmem : Work.Spaces.HkMem α 6 (fun z θ => Aa z θ * Ba z θ) :=
    Work.FTS.StrongPersist.H6Rows.N0pair6bWork.HkMem_mul_of_WlInf6_cd6 hα hα1 hAacd hAawl
      hBacd hBamem
  -- ... and the product rule prices its norm, so the pairing is linear in `|f|_{ℋ⁶}`
  have hnorm := hC₀ α hα hα1 Aa Ba hAacd hAawl hBacd hBamem
  -- the perturbation `f` is `C⁶` on the open quadrant and in `ℋ⁶`
  have hfcd : ContDiffOn ℝ 6 (Function.uncurry f) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongPersist.H6Rows.co6_of_smoothOpen hadm.reg.1
  have hfm : Work.Spaces.HkMem α 6 f := hadm.reg.2
  -- the product's `ℋ⁶`-norm is bounded by the two constants
  have hαp : 0 ≤ C₀ * α ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg hC₀pos.le (Real.rpow_nonneg hα.le _)
  have hbound : Work.Spaces.HkNorm α 6 (fun z θ => Aa z θ * Ba z θ)
      ≤ C₀ * α ^ (-(1 / 2 : ℝ)) * KA * KB := by
    calc Work.Spaces.HkNorm α 6 (fun z θ => Aa z θ * Ba z θ)
        ≤ C₀ * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 6 Aa
            * Work.Spaces.HkNorm α 6 Ba := hnorm
      _ ≤ C₀ * α ^ (-(1 / 2 : ℝ)) * KA * Work.Spaces.HkNorm α 6 Ba :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hAab hαp) (Work.Spaces.HkNorm_nonneg α 6 Ba)
      _ ≤ C₀ * α ^ (-(1 / 2 : ℝ)) * KA * KB :=
          mul_le_mul_of_nonneg_left hBanb (mul_nonneg hαp hKA)
  -- Cauchy–Schwarz for the level-six pairing, then the product rule
  have hcs := hCC α hα hα1 (fun z θ => Aa z θ * Ba z θ) f hucd hfcd hmem hfm
  refine le_trans hcs ?_
  calc CC * Work.Spaces.HkNorm α 6 (fun z θ => Aa z θ * Ba z θ)
        * Work.Spaces.HkNorm α 6 f
      ≤ CC * (C₀ * α ^ (-(1 / 2 : ℝ)) * KA * KB) * Work.Spaces.HkNorm α 6 f :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbound hCCpos.le)
          (Work.Spaces.HkNorm_nonneg α 6 f)
    _ = CC * C₀ * α ^ (-(1 / 2 : ℝ)) * KA * KB * Work.Spaces.HkNorm α 6 f := by ring

end Work.FTS.StrongPersist.H6Rows.Npair6SupAux
