import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.OpenPkg.prod_field
import Submission.Work.FTS.OpenPkg.wprod_field_winf
import Submission.Work.FTS.GalFields.RHS.HkSum
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnN0
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnNCoreUnif
import Submission.Work.FTS.StrongEps.ClassCRHS.HkSumOpenClosure
import Submission.Work.FTS.StrongEps.ClassCRHS.StarAtomsScaled
import Submission.Work.FTS.StrongEps.ClassCRHS.StarAtomsFK
import Submission.Work.FTS.StrongEps.ClassCRHS.SmoothOpenRHS

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.ClassCRHS

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn)

/-- **The `N`-block of the scheme's right-hand side is `ℋ⁴`-honest and bounded, for `ClassC`
data of small `ℋ⁴`-size and bounded `ℋ⁶`-size.**

`N α (Ftot α w) (Φs + Φg) = 2·Rop(Φ̃)·F - 2·Uop(Φ̃)·pth F - 2α·Vop(Φ̃)·Dz F
- (1/2)·s2·FK F·pth F - sin²θ·FK F·F`, where `Φ̃ = PhiTil α (Ftot α w) (Φs+Φg)` splits as
`PhiTs α Φs + PhiTil α w Φg` (`Theta α F = (1/(4α))s2·L₁₂ F` is linear in `F`).

Route hints (all tools are on disk and threshold-free):

* `Rop/Uop/Vop` are linear in their argument, so the split of `Φ̃` splits each of them; the
  `PhiTs`-parts are priced by `hstar` (`StarPkgo2.RW`, `VW`, `UsW`, `VzW`) as `𝒲^{4,∞}`-functions,
  the `PhiTil α w Φg`-parts by `hell` (`EllPkgGo.R`, `U`, `V`), which gives
  `HkMem α 4 (Rop …)` and `Xn ≤ Ce·Xn α w ≤ Ce·C₀α²`;
* the pieces whose first factor is the `𝒲`-coefficient `(z+1)/z·Rop(Φ̃_*)` etc. are handled by
  `Work.FTS.OpenPkg.wprod_field_winf` after the identity
  `2·Rop(Φ̃_*)·F = 2·[(z+1)/z·Rop(Φ̃_*)]·[z/(1+z)·F]` (and analogously for `(Uop/s2)·Dth f`,
  where the factor `s2·pth F = Dth F` **everywhere**); the second factor is in `HQo α 4` by
  closure of `ℋ⁴` under a bounded smooth radial factor (`prod_field` with the fixed profiles
  `(z+1)/z`, `z/(1+z)`);
* `FK(F_*+w) = FK(F_*) + FK(w)` (`Work.FTS.GalFields.RHS.FK_add_of_slices`; `FK(F_*)` is the
  explicit `α·2z/(1+z)²`), and `Work.FTS.OpenPkg.fkH_field` bounds `FK(w)` by `Ci·Xn α w`;
* the remaining factors: `F = F_* + w` (additivity), `Dth F`, `Dz F` (`ℋ⁴` via
  `Work.FTS.GalFields.Xn_Dz_le_Xn5` / `Xn_Dth_le_Xn5`, bounded by `HkNorm α 6 w ≤ B`); the
  fixed `F_*`, `Dth F_*`, `Dz F_*` via `Work.FTS.Nonlinear.FstarPkg.{Fstar_W, DthFstar_W,
  DzFstar_W}` (+ `wtoHQ_of_pointwise_open` if a pointwise form is needed);
* sums: `Work.FTS.GalFields.RHS.HkNorm_add_le_open` / `HkNorm_finset_sum_le`;
* the sibling `Work.FTS.StrongEps.ClassCRHS.HkMemXnN0` shows the same bookkeeping for `N₀`.

`K` may depend on `α, C₀, B, Ce, Cs, Φs` but **not** on `w, Φg`.

The proof splits the right-hand side `N α (Ftot α w) (Φs + Φg)` into its twenty §8 pieces
`NBlk α w Φs Φg k` (`HkMemXnNDefs`), each of which is a scalar multiple of a product of two
`ℋ⁴`-honest (or `𝒲^{4,∞}` × `ℋ⁴`-honest) factors, `nb_data` (`HkMemXnNCore`) doing the
bookkeeping and producing a uniform constant `Kbig`; the constants `C1`, `C2` for the
`F_*`-atoms come from `StarAtomsScaled` and `StarAtomsFK`.  The transfer back from the sum to
`N` itself (the pieces agree with `N` on the open quadrant, by `Work.FTS.NonlinRows.Rl1.splitOpen`)
is `HkSumOpenClosure`, and the final norm bound is `HkNorm_finset_sum_le` with
`√(2²⁰) = 1024` and `card (range 20) = 20`. -/
theorem HkMemXnN_unif : ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∀ {C₀ B Ce Cs : ℝ},
    ∃ K : ℝ, 0 < K ∧ ∀ {Φs : Work.FTS.Galerkin.Fn} {w Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      Work.Spaces.HkNorm α 6 w ≤ B →
      Work.FTS.VocabO.EllPkgGo α Ce w Φg → Work.FTS.VocabO2.StarPkgo2 α Cs Φs →
      Work.Spaces.HkMem α 4 (Work.Construction.N α (Work.Construction.Ftot α w)
        (fun z θ => Φs z θ + Φg z θ)) ∧
      Work.FTS.Nonlin.Xn α (Work.Construction.N α (Work.Construction.Ftot α w)
        (fun z θ => Φs z θ + Φg z θ)) ≤ K := by
  intro α hαmem C₀ B Ce Cs
  obtain ⟨C1, hC1, hs1⟩ := StarAtomsScaled
  obtain ⟨C2, hC2, hs2⟩ := StarAtomsFK
  obtain ⟨Kbig, hKbig, hdata⟩ := nb_data_unifΦ hαmem hC1 hC2 (hs1 α hαmem) (hs2 α hαmem)
  refine ⟨Kbig * (2 ^ 20 * 20) + 1, by positivity, ?_⟩
  intro Φs w Φg hw hXw hB hell hstar
  have hα0 : 0 < α := hαmem.1
  obtain ⟨hsm, hpm, hid⟩ := hdata hw hXw hB hell hstar
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4
      (Work.Construction.N α (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ))
      p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand
      (SmoothOpenRHS hα0 hαmem.2 hw hell hstar).2.2.2.2 α 4
  obtain ⟨hmem, hbnd⟩ := HkSumOpenClosure hα0 hcont hsm (fun k hk => (hpm k hk).1)
    (fun z θ hz h1 h2 => hid z θ ⟨hz, h1, h2⟩)
  refine ⟨hmem, ?_⟩
  refine le_trans hbnd ?_
  have h1 : Real.sqrt ((2 : ℝ) ^ 20) = 1024 := by
    rw [show (2 : ℝ) ^ 20 = 1024 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h2 : ∑ k ∈ Finset.range 20, Work.FTS.Nonlin.Xn α (NBlk α w Φs Φg k) ≤ 20 * Kbig := by
    refine le_trans (Finset.sum_le_sum (fun k hk => (hpm k hk).2)) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    norm_num
  calc Real.sqrt ((2 : ℝ) ^ 20)
        * ∑ k ∈ Finset.range 20, Work.FTS.Nonlin.Xn α (NBlk α w Φs Φg k)
      ≤ 1024 * (20 * Kbig) := by
        rw [h1]
        exact mul_le_mul_of_nonneg_left h2 (by norm_num)
    _ ≤ Kbig * (2 ^ 20 * 20) + 1 := by nlinarith [hKbig]

end Work.FTS.StrongEps.ClassCRHS
