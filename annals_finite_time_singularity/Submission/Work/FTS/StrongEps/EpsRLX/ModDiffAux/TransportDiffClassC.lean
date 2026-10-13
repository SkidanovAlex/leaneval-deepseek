import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.GalFields.RHS.SharpMod.transport_L12_diff
import Submission.Work.FTS.StrongEps.EpsRLX.CCSharp.Base
import Submission.Work.FTS_MuLamOK.Main
import Submission.Work.FTS.IPGen.OpenBasic
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.NonlinRows.NRow10aux.mul_phi_Hk
import Submission.Work.FTS.GalBasis.hk_sq_api

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `ModDiffAux/TransportDiffClassC` — the transport `L₁₂`-difference on the class `C`

The third of the three `L₁₂`-zero-mode differences whose combination is the difference of the
modulation constants (`Work.FTS.StrongEps.EpsRLX.ModDiffClassC`).  The transport zero mode
`g ↦ L₁₂(3·D_θg/(1+z))(0)` is **linear** in the profile (`L12_sub_eq_of_smoothOpen`, valid on
the class), so its difference is the *single-profile* row estimate
`Work.FTS.Nonlinear.Open.Rl2` (`Work.FTS_MuLamOK.KMu2_row`, constant `KMu2 = 9`) applied to the
difference `W₁ - W₂` of the two `ClassC` data.

The two auxiliary facts supplied here are

* `smoothOpen_hkMem_three_div_Dth`: the transport datum `3·D_θf/(1+z)` of an
  `SmoothOpen`/`HkMem α 5` profile is `C^∞` on the open quadrant and honest in `ℋ⁴`
  (the `RegQ α 5`-free version of `SharpMod.smoothOpen_and_hkMem_three_div_Dth`), and
* `L12_transport_diff_classC`: the difference estimate itself.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsRLX.ModDiffAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- **The transport datum `3·D_θf/(1+z)` is `C^∞` on the open quadrant and honest in `ℋ⁴`**,
from `SmoothOpen f` and `HkMem α 5 f` alone (no `SmoothQuad`/`RegQ` hypothesis: the interior
class of `ClassC` is enough).  This is `SharpMod.smoothOpen_and_hkMem_three_div_Dth` with the
`RegQ α 5`-hypothesis replaced by its two *interior* consequences. -/
theorem smoothOpen_hkMem_three_div_Dth {α : ℝ} {f : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 5 f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => 3 * Work.Spaces.Dth f z θ / (1 + z)) ∧
      Work.Spaces.HkMem α 4 (fun z θ => 3 * Work.Spaces.Dth f z θ / (1 + z)) := by
  have hDthSm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth f) := hsm.Dth
  have hDthMem : Work.Spaces.HkMem α 4 (Work.Spaces.Dth f) :=
    Work.FTS.IPGen.HkMem_Dth_le (k := 4) (by linarith [hα.le]) hsm hmem
  obtain ⟨Cphi, _hCphi, hmulphi⟩ := Work.FTS.NonlinRows.NRow10aux.mul_phi_Hk
  have hphiMem : Work.Spaces.HkMem α 4
      (fun z θ => Work.FTS.NonlinRows.NRow10aux.phiF z * Work.Spaces.Dth f z θ) :=
    (hmulphi hα hα1 ⟨hDthSm, hDthMem⟩).1
  have hphiSm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.FTS.NonlinRows.NRow10aux.phiF z * Work.Spaces.Dth f z θ) :=
    Work.FTS.NonlinRows.smoothOpen_mul
      Work.FTS.NonlinRows.NRow10aux.phiSelf_smoothOpen hDthSm
  constructor
  · exact Work.FTS.GalFields.RHS.SharpMod.smoothOpen_three_div_mul hDthSm
  · have h1 : Work.Spaces.HkMem α 4 (fun z θ => 3 * Work.Spaces.Dth f z θ) :=
      Work.FTS.LocData.HkMem_const_mul α 4 3 hDthMem
    have h2 : Work.Spaces.HkMem α 4
        (fun z θ => 3 * (Work.FTS.NonlinRows.NRow10aux.phiF z * Work.Spaces.Dth f z θ)) :=
      Work.FTS.LocData.HkMem_const_mul α 4 3 hphiMem
    have hsub : Work.Spaces.HkMem α 4
        (fun z θ => 3 * Work.Spaces.Dth f z θ
          - 3 * (Work.FTS.NonlinRows.NRow10aux.phiF z * Work.Spaces.Dth f z θ)) :=
      Work.FTS.GalBasis.hkMem_sub_open α 4
        (Work.FTS.NonlinRows.smoothOpen_const_mul 3 hDthSm)
        (Work.FTS.NonlinRows.smoothOpen_const_mul 3 hphiSm) h1 h2
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4 hsub ?_
    intro z hz θ hθ
    have hz1 : (1 : ℝ) + z ≠ 0 := ne_of_gt (by linarith [show (0 : ℝ) < z from hz])
    simp only [Work.FTS.NonlinRows.NRow10aux.phiF]
    field_simp
    ring

/-- The `ℋ⁴`-honesty of a `ClassC` datum descends to any order `≤ 7`. -/
theorem hkMem_classC_le {α : ℝ} {W : Fn} (hW : Work.FTS.ClassC.ClassC α W) {k : ℕ} (hk : k ≤ 7) :
    Work.Spaces.HkMem α k W :=
  Work.FTS.OpenPkg.HkMem_mono_open hW.reg k hk hW.mem

/-- **The `L₁₂`-zero-mode difference of the transport term, on the class `C`.** -/
theorem L12_transport_diff_classC {α : ℝ} (hα : α ∈ Set.Ioc 0 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ {W₁ W₂ : Fn},
      Work.FTS.ClassC.ClassC α W₁ → Work.FTS.ClassC.ClassC α W₂ →
      |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth W₁ z θ / (1 + z)) 0
        - Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth W₂ z θ / (1 + z)) 0|
        ≤ K * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  refine ⟨Work.FTS_MuLamOK.KMu2 + 1, by linarith [Work.FTS_MuLamOK.KMu2_pos], ?_⟩
  intro W₁ W₂ hW₁ hW₂
  -- the difference datum
  have hhC : Work.FTS.ClassC.ClassC α (fun z θ => W₁ z θ - W₂ z θ) :=
    Work.FTS.StrongEps.EpsRLX.CCSharp.sub_classC hW₁ hW₂
  have hh5 : Work.Spaces.HkMem α 5 (fun z θ => W₁ z θ - W₂ z θ) :=
    Work.FTS.OpenPkg.HkMem_mono_open hhC.reg 5 (by norm_num) hhC.mem
  -- the three data
  obtain ⟨hsm₁, hmem₁⟩ :=
    smoothOpen_hkMem_three_div_Dth hα0 hα1 hW₁.reg (hkMem_classC_le hW₁ (by norm_num))
  obtain ⟨hsm₂, hmem₂⟩ :=
    smoothOpen_hkMem_three_div_Dth hα0 hα1 hW₂.reg (hkMem_classC_le hW₂ (by norm_num))
  obtain ⟨hsmh, hmemh⟩ :=
    smoothOpen_hkMem_three_div_Dth hα0 hα1 hhC.reg hh5
  -- linearity of `L₁₂` in the profile
  have hlin := Work.FTS.GalFields.RHS.L12_sub_eq_of_smoothOpen hsm₁ hsm₂ hmem₁ hmem₂ 0 le_rfl
  -- the difference datum is the datum of `W₁ - W₂`
  have hkey : Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth W₁ z θ / (1 + z)
        - 3 * Work.Spaces.Dth W₂ z θ / (1 + z)) 0
      = Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth (fun z θ => W₁ z θ - W₂ z θ) z θ
          / (1 + z)) 0 := by
    refine Work.FTS.GalFields.RHS.SharpMod.L12_congr_of_dens (fun s hs => ?_)
    refine Work.FTS.GalFields.RHS.SharpMod.L12dens_congr_of_Iθ (fun θ hθ => ?_)
    have hadd := Work.FTS.GalFields.RHS.SharpMod.Dth_add_of_pointwise
      (g := W₁) (g' := W₂) (h := fun z θ => W₁ z θ - W₂ z θ) hW₂.reg hhC.reg
      (fun z θ => by ring) s θ hs hθ
    rw [hadd]
    ring
  rw [hlin, hkey]
  -- the row estimate at the difference, and the `ℋ⁴ ≤ ℋ⁵` comparison
  have hh4 : Work.Spaces.HkMem α 4 (fun z θ => W₁ z θ - W₂ z θ) :=
    Work.FTS.OpenPkg.HkMem_mono_open hhC.reg 4 (by norm_num) hhC.mem
  have hrow := Work.FTS_MuLamOK.KMu2_row (α := α) (f := fun z θ => W₁ z θ - W₂ z θ)
    hα0 hα1 hhC.reg hh4
  have hXle : Work.FTS.Nonlin.Xn α (fun z θ => W₁ z θ - W₂ z θ)
      ≤ Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) :=
    Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 5) (k' := 4) (by norm_num) hh5
  have hXn0 : 0 ≤ Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) :=
    Work.Spaces.HkNorm_nonneg α 5 _
  have hfac : (1 : ℝ) ≤ 1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂ := by
    have h1 := Work.Spaces.HkNorm_nonneg α 5 W₁
    have h2 := Work.Spaces.HkNorm_nonneg α 5 W₂
    linarith
  calc |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth (fun z θ => W₁ z θ - W₂ z θ) z θ
          / (1 + z)) 0|
      ≤ Work.FTS_MuLamOK.KMu2 * Work.FTS.Nonlin.Xn α (fun z θ => W₁ z θ - W₂ z θ) := hrow
    _ ≤ Work.FTS_MuLamOK.KMu2 * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) :=
        mul_le_mul_of_nonneg_left hXle (le_of_lt Work.FTS_MuLamOK.KMu2_pos)
    _ ≤ (Work.FTS_MuLamOK.KMu2 + 1)
          * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
          * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by
        have hd : 0 ≤ Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := hXn0
        have hK : (0 : ℝ) < Work.FTS_MuLamOK.KMu2 + 1 :=
          by linarith [Work.FTS_MuLamOK.KMu2_pos]
        have h1 : Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)
            ≤ (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
              * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by
          simpa using mul_le_mul_of_nonneg_right hfac hd
        calc Work.FTS_MuLamOK.KMu2
              * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)
            ≤ (Work.FTS_MuLamOK.KMu2 + 1)
              * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) :=
              mul_le_mul_of_nonneg_right (by linarith [Work.FTS_MuLamOK.KMu2_pos]) hd
          _ ≤ (Work.FTS_MuLamOK.KMu2 + 1)
              * ((1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
                * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)) :=
              mul_le_mul_of_nonneg_left h1 (le_of_lt hK)
          _ = (Work.FTS_MuLamOK.KMu2 + 1)
              * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
              * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by ring

end Work.FTS.StrongEps.EpsRLX.ModDiffAux
