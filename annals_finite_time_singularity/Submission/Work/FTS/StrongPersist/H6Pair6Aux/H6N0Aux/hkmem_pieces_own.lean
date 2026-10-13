/-
Copyright: work module for the Elgindi finite-time singularity project.

# `H6N0Aux/hkmem_pieces_own` — the `ℋ⁶`-memberships of the six `f`-dependent pieces of `N₀`

The pieces `NP3`, `NP4a`, `NP4b`, `NP5a`, `NP5b`, `NP6` of `N₀ α (F_*+f) f`
(`H6N0Aux/N0row_defs`) are products of a radial (or `𝒲^{6,∞}`-bounded) coefficient with `f`,
`D_θf` or `D_zf`.  Their `ℋ⁶`-memberships follow from

* the radial-times-`ℋ⁶` engine `H6Rows/N0pair6Aux/HkMem_radial_mul6` (a radial factor with
  bounded `D_z`-jets times an `ℋ⁶` datum),
* the `𝒲^{6,∞}`-priced product `HkMem_mul_of_WlInf6` (`N0SlotSplitAux`) for the `F_*`-family
  coefficients `D_θF_*`, `c2m·D_zF_*`, `c2m·L₁₂(F_*)`,
* the angular-multiplier engine `angmul6` for `c2m · (L₁₂(f)·D_zf)`,
* `HkMem_Dth_le`/`HkMem_Dz_le` (`IPGen`) for `D_θf`, `D_zf` out of `HkMem α 7 f`, and
* `LocData.HkMem_const_mul` for the scalar multiples.

The route is the one used in `N0SlotSplit`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.Construction.L12_Fstar_eq
import Submission.Work.FTS.StrongPersist.N6_L12H
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12Sup6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.SmoothN0
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.N0SlotSplitAux
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.HkMem_radial_mul6
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.N0coefA6_WlInf6
import Submission.Work.FTS.StrongPersist.angmul6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.c2mJets
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.c2mDzFstar_W6
import Submission.Work.FTS.IPGen.OpenBasic
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.N0row_defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

theorem hkmem_N0pieces_own {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hL : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 f z))
    (h0 : Work.Construction.L12 f 0 = 0)
    (m6 : Work.Spaces.HkMem α 6 f) (m7 : Work.Spaces.HkMem α 7 f) :
    Work.Spaces.HkMem α 6 (NP3 α f) ∧ Work.Spaces.HkMem α 6 (NP4a α f) ∧
    Work.Spaces.HkMem α 6 (NP4b α f) ∧ Work.Spaces.HkMem α 6 (NP5a α f) ∧
    Work.Spaces.HkMem α 6 (NP5b α f) ∧ Work.Spaces.HkMem α 6 (NP6 α f) := by
  -- ## the radial `L₁₂` machinery
  obtain ⟨Xi, Cpow, hXi, hCpow, hN6⟩ := Work.FTS.StrongPersist.N6_L12H
  have hL12mem : Work.Spaces.HkMem α 6 (fun z θ => Work.Construction.L12 f z) :=
    (hN6 α hα f ⟨hf, m6⟩ h0).1
  obtain ⟨C6, hC6pos, hsup6⟩ := Work.FTS.StrongPersist.H6Pair6Aux.L12Sup6
  have hL12jet : ∀ j : ℕ, j ≤ 6 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 f z) z|
        ≤ C6 * Work.Spaces.HkNorm α 6 f :=
    fun j hj z hz => hsup6 α f hα hα1 hf m6 m7 h0 j hj z hz
  have hB0 : 0 ≤ C6 * Work.Spaces.HkNorm α 6 f :=
    mul_nonneg hC6pos.le (Work.Spaces.HkNorm_nonneg α 6 f)
  have hL12cd : ContDiffOn ℝ 6 (fun z : ℝ => Work.Construction.L12 f z) (Set.Ioi 0) := by
    have h1 : ContDiffOn ℝ 6
        (Function.uncurry (fun z (_ : ℝ) => Work.Construction.L12 f z))
        Work.FTS.EllipticEst.Q0 := hL.forall 6
    have h2 : ContDiffOn ℝ 6 (fun z : ℝ => (z, (1 : ℝ))) (Set.Ioi 0) :=
      ContDiffOn.prodMk contDiffOn_id contDiffOn_const
    have h3 := h1.comp h2 (fun z hz => ⟨hz, by norm_num, by linarith [Real.pi_gt_three]⟩)
    refine h3.congr (fun z _ => ?_)
    rfl
  have hL12f : Work.Spaces.HkMem α 6
      (fun z θ => Work.Construction.L12 f z * f z θ) :=
    Work.FTS.StrongPersist.H6Rows.N0pair6Aux.HkMem_radial_mul6 α
      (C6 * Work.Spaces.HkNorm α 6 f) (fun z => Work.Construction.L12 f z) f
      hα hB0 hL12cd hL12jet hf m6
  have hDthmem : Work.Spaces.HkMem α 6 (Work.Spaces.Dth f) :=
    Work.FTS.IPGen.HkMem_Dth_le (α := α) (k := 6) (f := f) (by linarith) hf m7
  have hL12dth : Work.Spaces.HkMem α 6
      (fun z θ => Work.Construction.L12 f z * Work.Spaces.Dth f z θ) :=
    Work.FTS.StrongPersist.H6Rows.N0pair6Aux.HkMem_radial_mul6 α
      (C6 * Work.Spaces.HkNorm α 6 f) (fun z => Work.Construction.L12 f z)
      (Work.Spaces.Dth f) hα hB0 hL12cd hL12jet hf.Dth hDthmem
  have hDzmem : Work.Spaces.HkMem α 6 (Work.Spaces.Dz f) :=
    Work.FTS.IPGen.HkMem_Dz_le (α := α) (k := 6) (f := f) hf m7
  have hL12dz : Work.Spaces.HkMem α 6
      (fun z θ => Work.Construction.L12 f z * Work.Spaces.Dz f z θ) :=
    Work.FTS.StrongPersist.H6Rows.N0pair6Aux.HkMem_radial_mul6 α
      (C6 * Work.Spaces.HkNorm α 6 f) (fun z => Work.Construction.L12 f z)
      (Work.Spaces.Dz f) hα hB0 hL12cd hL12jet hf.Dz hDzmem
  -- ## the `F_*`-coefficient packages
  obtain ⟨CD, hCDpos, hDthFstar⟩ := Work.FTS.StrongPersist.DthFstar_W6
  obtain ⟨CC, hCCpos, hc2mDz⟩ := Work.FTS.StrongPersist.H6Pair6Aux.c2mDzFstar_W6
  obtain ⟨CA, hCApos, hN0coef⟩ :=
    Work.FTS.StrongPersist.H6Rows.N0pair6Aux.N0coefA6_WlInf6
  obtain ⟨hN0coef_sm, hN0coef_w, hN0coef_le⟩ := hN0coef α hα hα1
  obtain ⟨Cc2, hCc2pos, hc2sm, hc2b, hc2jet⟩ :=
    Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.c2mJets
  obtain ⟨Cm6, hCm6pos, hang⟩ := Work.FTS.StrongPersist.angmul6
  have hangc2 : Work.Spaces.HkMem α 6
      (fun z θ => Work.Construction.c2m θ * (Work.Construction.L12 f z
        * Work.Spaces.Dz f z θ)) :=
    (hang α hα hα1 (fun θ => Work.Construction.c2m θ)
      (fun z θ => Work.Construction.L12 f z * Work.Spaces.Dz f z θ) Cc2 hc2sm
      (fun θ hθ => hc2b θ hθ)
      (fun i hi hi6 θ hθ => hc2jet i hi (by omega) 0 θ hθ)
      (so_mul hL hf.Dz) hL12dz).1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `NP3 = (1/α)·(L₁₂(f)·f)`
    refine HkMem_congr_Qd (f := fun z θ =>
      (1 / α) * (Work.Construction.L12 f z * f z θ)) ?_ ?_
    · intro z θ hzθ
      show (1 / α) * (Work.Construction.L12 f z * f z θ) = NP3 α f z θ
      simp only [NP3] <;> ring
    · exact Work.FTS.LocData.HkMem_const_mul α 6 (1 / α) hL12f
  · -- `NP4a = (3/2α)·(L₁₂(f)·D_θF_*)`
    refine HkMem_congr_Qd (f := fun z θ => Work.Spaces.Dth (Work.Construction.Fstar α) z θ
      * ((3 / (2 * α)) * Work.Construction.L12 f z)) ?_ ?_
    · intro z θ hzθ
      show Work.Spaces.Dth (Work.Construction.Fstar α) z θ
          * ((3 / (2 * α)) * Work.Construction.L12 f z) = NP4a α f z θ
      simp only [NP4a, NA4] <;> ring
    · exact HkMem_mul_of_WlInf6 hα hα1 (smoothOpen_Fstar α).Dth
        (hDthFstar α hα hα1).1 (so_const_mul (3 / (2 * α)) hL)
        (Work.FTS.LocData.HkMem_const_mul α 6 (3 / (2 * α)) hL12mem)
  · -- `NP4b = (3/2α)·(L₁₂(f)·D_θf)`
    refine HkMem_congr_Qd (f := fun z θ =>
      (3 / (2 * α)) * (Work.Construction.L12 f z * Work.Spaces.Dth f z θ)) ?_ ?_
    · intro z θ hzθ
      show (3 / (2 * α)) * (Work.Construction.L12 f z * Work.Spaces.Dth f z θ)
        = NP4b α f z θ
      simp only [NP4b] <;> ring
    · exact Work.FTS.LocData.HkMem_const_mul α 6 (3 / (2 * α)) hL12dth
  · -- `NP5a = (-1)·(L₁₂(f)·(c2m·D_zF_*))`
    refine HkMem_congr_Qd (f := fun z θ =>
      (Work.Construction.c2m θ * Work.Spaces.Dz (Work.Construction.Fstar α) z θ)
        * (-1 * Work.Construction.L12 f z)) ?_ ?_
    · intro z θ hzθ
      show (Work.Construction.c2m θ * Work.Spaces.Dz (Work.Construction.Fstar α) z θ)
          * (-1 * Work.Construction.L12 f z) = NP5a α f z θ
      simp only [NP5a, NA5]
      ring
    · exact HkMem_mul_of_WlInf6 hα hα1
        (so_mul (so_snd contDiff_c2m) (smoothOpen_Fstar α).Dz)
        (hc2mDz α hα hα1).1 (so_const_mul (-1) hL)
        (Work.FTS.LocData.HkMem_const_mul α 6 (-1) hL12mem)
  · -- `NP5b = (-1)·(c2m·L₁₂(f)·D_zf)`
    refine HkMem_congr_Qd (f := fun z θ =>
      -1 * (Work.Construction.c2m θ * (Work.Construction.L12 f z
        * Work.Spaces.Dz f z θ))) ?_ ?_
    · intro z θ hzθ
      show -1 * (Work.Construction.c2m θ * (Work.Construction.L12 f z
          * Work.Spaces.Dz f z θ)) = NP5b α f z θ
      simp only [NP5b] <;> ring
    · exact Work.FTS.LocData.HkMem_const_mul α 6 (-1) hangc2
  · -- `NP6 = (-1)·(c2m·L₁₂(F_*)·D_zf)`
    refine HkMem_congr_Qd (f := fun z θ =>
      (-(2 * α / (1 + z)) * Work.Construction.c2m θ) * Work.Spaces.Dz f z θ) ?_ ?_
    · intro z θ hzθ
      show (-(2 * α / (1 + z)) * Work.Construction.c2m θ) * Work.Spaces.Dz f z θ
        = NP6 α f z θ
      have hz : 0 ≤ z := le_of_lt hzθ.1
      simp only [NP6, NA6]
      rw [Work.Construction.L12_Fstar_eq hα hα1 hz]
      ring
    · exact HkMem_mul_of_WlInf6 hα hα1 hN0coef_sm hN0coef_w hf.Dz hDzmem

end Work.FTS.StrongPersist.H6Pair6Aux
