/-
# `H5/HAtoms5` — the `ℋ⁵`-honest atoms of the level-`5` `N`-block

The `ℋ⁵`-side atoms of the twenty pieces are

* the three elliptic coefficients `ℛ(Φ̃)`, `𝒰(Φ̃)/sin 2θ`, `𝒱(Φ̃)` (`Φ̃ = PhiTg α w Φg`), whose
  `ℋ⁵`-data is immediate from the level-six package `EllPkgK α 6` (level-five membership and
  norm by monotonicity);
* `w`, `D_θ w`, `D_z w` (from `ClassC α w`; the two derivatives by the level shift
  `HkSq_Dz_le_Q0Sm` / `HkSq_Dth_le` from the `ℋ⁶`-data of `w`);
* the angular moment `FK w` (`StrongPersist.H6Row6.fkFacts7`);
* the three `φ`-scaled atoms `φ·w`, `φ·D_θw`, `φ·D_zw` (`φ z = z/(1+z)`), from the level-five
  `φ`-multiplication `H5.phiAtoms5` (`Submission/Work/FTS/StrongEps/H5/radial_atoms5.lean`).

Everything is packaged as `HQo α 5 A ∧ HkNorm α 5 A ≤ a` with `a` independent of `w`, `Φg`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.H5.Data
import Submission.Work.FTS.StrongEps.H5.L5of
import Submission.Work.FTS.StrongEps.H5.radial_atoms5
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.StrongPersist.H6Row6.fkFacts7
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnNAux
import Submission.Work.FTS.OpenPkg.prod_field

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.H5.Atoms

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- **Multiplication by `φ z = z/(1+z)` preserves `ℋ⁵`-honesty**, with the universal constant
of `H5.phiAtoms5`. -/
theorem phiHQo5 : ∃ C : ℝ, 0 < C ∧ ∀ {α : ℝ}, 0 < α → α ≤ 1 → ∀ {g : Fn},
    Work.FTS.VocabO.HQo α 5 g →
    Work.FTS.VocabO.HQo α 5 (fun z θ => z / (1 + z) * g z θ) ∧
    Work.Spaces.HkNorm α 5 (fun z θ => z / (1 + z) * g z θ)
      ≤ C * Work.Spaces.HkNorm α 5 g := by
  obtain ⟨C, hC, hphi⟩ := Work.FTS.StrongEps.H5.phiAtoms5
  refine ⟨C, hC, fun {α} hα hα1 {g} hg => ⟨⟨?_, (hphi α hα hα1 g hg).1⟩,
    (hphi α hα hα1 g hg).2⟩⟩
  simpa [Work.FTS.NonlinRows.NRow10aux.phiF]
    using Work.FTS.OpenPkg.smoothOpen_sepMul
      (Work.FTS.NonlinRows.NRow10aux.phiSelf_smoothOpen) hg.1

/-- **The `ℋ⁵`-honest atoms of the level-`5` `N`-block.** -/
theorem HAtoms5 : ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∀ {C₀ B Ce : ℝ},
    ∃ a : ℝ, 0 < a ∧ ∀ {w Φg : Fn},
      Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      Work.Spaces.HkNorm α 6 w ≤ B → Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
      (Work.FTS.VocabO.HQo α 5 (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg)) ∧
        Work.Spaces.HkNorm α 5 (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg)) ≤ a) ∧
      (Work.FTS.VocabO.HQo α 5 (fun z θ => Work.Construction.Uop α
          (Work.FTS.Nonlin.PhiTg α w Φg) z θ / Work.Construction.s2 θ) ∧
        Work.Spaces.HkNorm α 5 (fun z θ => Work.Construction.Uop α
          (Work.FTS.Nonlin.PhiTg α w Φg) z θ / Work.Construction.s2 θ) ≤ a) ∧
      (Work.FTS.VocabO.HQo α 5 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α w Φg)) ∧
        Work.Spaces.HkNorm α 5 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α w Φg)) ≤ a) ∧
      (Work.FTS.VocabO.HQo α 5 w ∧ Work.Spaces.HkNorm α 5 w ≤ a) ∧
      (Work.FTS.VocabO.HQo α 5 (Work.Spaces.Dth w) ∧
        Work.Spaces.HkNorm α 5 (Work.Spaces.Dth w) ≤ a) ∧
      (Work.FTS.VocabO.HQo α 5 (Work.Spaces.Dz w) ∧
        Work.Spaces.HkNorm α 5 (Work.Spaces.Dz w) ≤ a) ∧
      (Work.FTS.VocabO.HQo α 5 (fun z _ => Work.Construction.FK w z) ∧
        Work.Spaces.HkNorm α 5 (fun z _ => Work.Construction.FK w z) ≤ a) ∧
      (Work.FTS.VocabO.HQo α 5 (fun z θ => z / (1 + z) * w z θ) ∧
        Work.Spaces.HkNorm α 5 (fun z θ => z / (1 + z) * w z θ) ≤ a) ∧
      (Work.FTS.VocabO.HQo α 5 (fun z θ => z / (1 + z) * Work.Spaces.Dth w z θ) ∧
        Work.Spaces.HkNorm α 5 (fun z θ => z / (1 + z) * Work.Spaces.Dth w z θ) ≤ a) ∧
      (Work.FTS.VocabO.HQo α 5 (fun z θ => z / (1 + z) * Work.Spaces.Dz w z θ) ∧
        Work.Spaces.HkNorm α 5 (fun z θ => z / (1 + z) * Work.Spaces.Dz w z θ) ≤ a) := by
  intro α hαI C₀ B Ce
  have hα0 : 0 < α := hαI.1
  have hα1 : α ≤ 1 := hαI.2
  obtain ⟨Cphi, hCphi, hphi⟩ := phiHQo5
  obtain ⟨CFK, Xi, Cpow, hCFK, hXi, hCpow, hfk⟩ := Work.FTS.StrongPersist.H6Row6.fkFacts7
  have hXiRnn : 0 ≤ Xi * α ^ (-Cpow) :=
    mul_nonneg hXi.le (Real.rpow_pos_of_pos hα0 _).le
  set B0 : ℝ := max B 0 with hB0def
  have hB0nn : 0 ≤ B0 := by rw [hB0def]; exact le_max_right _ _
  set A1 : ℝ := |Ce| * B0 with hA1def
  set A2 : ℝ := Xi * α ^ (-Cpow) * B0 + 1 with hA2def
  set A3 : ℝ := Cphi * B0 with hA3def
  have hA1nn : 0 ≤ A1 := by rw [hA1def]; exact mul_nonneg (abs_nonneg _) hB0nn
  have hA2nn : 0 ≤ A2 := by
    rw [hA2def]; linarith [mul_nonneg hXiRnn hB0nn]
  have hA3nn : 0 ≤ A3 := by rw [hA3def]; exact mul_nonneg hCphi.le hB0nn
  refine ⟨A1 + A2 + A3 + B0 + 1, by linarith, ?_⟩
  intro w Φg hw hXw hX6 hell
  have hX6' : Work.Spaces.HkNorm α 6 w ≤ B0 :=
    le_trans hX6 (by rw [hB0def]; exact le_max_left _ _)
  have hb0 : ∀ {x : ℝ}, x ≤ B0 → x ≤ A1 + A2 + A3 + B0 + 1 := by
    intro x hx; linarith [hA1nn, hA2nn, hA3nn]
  have hb1 : ∀ {x : ℝ}, x ≤ |Ce| * B0 → x ≤ A1 + A2 + A3 + B0 + 1 := by
    intro x hx; rw [← hA1def] at hx; linarith [hA2nn, hA3nn, hB0nn]
  have hb2 : ∀ {x : ℝ}, x ≤ Xi * α ^ (-Cpow) * B0 → x ≤ A1 + A2 + A3 + B0 + 1 := by
    intro x hx
    have h2 : Xi * α ^ (-Cpow) * B0 ≤ A2 := by rw [hA2def]; linarith
    linarith [hA1nn, hA3nn, hB0nn]
  have hb3 : ∀ {x : ℝ}, x ≤ Cphi * B0 → x ≤ A1 + A2 + A3 + B0 + 1 := by
    intro x hx; rw [← hA3def] at hx; linarith [hA1nn, hA2nn, hB0nn]
  -- ### the `ℋ⁶`-data of `w`
  have hmem6w : Work.Spaces.HkMem α 6 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hw.reg 6 (by norm_num) hw.mem
  have hqo6w : Work.FTS.VocabO.HQo α 6 w := ⟨hw.reg, hmem6w⟩
  -- ### the three elliptic coefficients, from `EllPkgK α 6`
  have hell' : ∀ {A : Fn}, Work.FTS.VocabO.HQo α 6 A →
      Work.Spaces.HkNorm α 6 A ≤ Ce * Work.Spaces.HkNorm α 6 w →
      Work.FTS.VocabO.HQo α 5 A ∧ Work.Spaces.HkNorm α 5 A ≤ A1 + A2 + A3 + B0 + 1 := by
    intro A hQA hb6
    refine ⟨⟨hQA.1, Work.FTS.OpenPkg.HkMem_mono_open hQA.1 5 (by norm_num) hQA.2⟩, hb1 ?_⟩
    calc Work.Spaces.HkNorm α 5 A ≤ Work.Spaces.HkNorm α 6 A :=
          Work.FTS.StrongLWP.HkNorm_mono_of_mem (by norm_num) hQA.2
      _ ≤ Ce * Work.Spaces.HkNorm α 6 w := hb6
      _ ≤ |Ce| * B0 :=
          le_trans (mul_le_mul_of_nonneg_right (le_abs_self Ce)
            (Work.Spaces.HkNorm_nonneg α 6 w)) (mul_le_mul_of_nonneg_left hX6' (abs_nonneg Ce))
  have hR := hell' hell.R.1 hell.R.2
  have hU := hell' hell.U.1 hell.U.2
  have hV := hell' hell.V.1 hell.V.2
  -- ### `w` and its two first derivatives
  have hwB : Work.Spaces.HkNorm α 5 w ≤ B0 :=
    le_trans (Work.FTS.StrongLWP.HkNorm_mono_of_mem (by norm_num) hmem6w) hX6'
  have hw5 : Work.FTS.VocabO.HQo α 5 w ∧ Work.Spaces.HkNorm α 5 w ≤ A1 + A2 + A3 + B0 + 1 :=
    ⟨⟨hw.reg, Work.FTS.OpenPkg.HkMem_mono_open hw.reg 5 (by norm_num) hmem6w⟩, hb0 hwB⟩
  have hDzB : Work.Spaces.HkNorm α 5 (Work.Spaces.Dz w) ≤ B0 := by
    refine le_trans (Real.sqrt_le_sqrt (Work.FTS.CoercivityFix.Transfer.HkSq_Dz_le_Q0Sm α 5
      (Work.FTS.StrongPersist.q0Sm_of_smoothOpen hw.reg 6) hmem6w)) ?_
    exact le_trans (Work.FTS.StrongLWP.HkNorm_mono_of_mem (by norm_num) hmem6w) hX6'
  have hDz5 : Work.FTS.VocabO.HQo α 5 (Work.Spaces.Dz w) ∧
      Work.Spaces.HkNorm α 5 (Work.Spaces.Dz w) ≤ A1 + A2 + A3 + B0 + 1 :=
    ⟨⟨hw.reg.Dz, Work.FTS.IPGen.HkMem_Dz_le hqo6w.1 hqo6w.2⟩, hb0 hDzB⟩
  have hDthB : Work.Spaces.HkNorm α 5 (Work.Spaces.Dth w) ≤ B0 := by
    refine le_trans (Real.sqrt_le_sqrt
      (Work.FTS.CoercivityStep.Norm.HkSq_Dth_le α hα0 5 hmem6w)) ?_
    exact le_trans (Work.FTS.StrongLWP.HkNorm_mono_of_mem (by norm_num) hmem6w) hX6'
  have hDth5 : Work.FTS.VocabO.HQo α 5 (Work.Spaces.Dth w) ∧
      Work.Spaces.HkNorm α 5 (Work.Spaces.Dth w) ≤ A1 + A2 + A3 + B0 + 1 :=
    ⟨⟨hw.reg.Dth, Work.FTS.IPGen.HkMem_Dth_le (by linarith) hqo6w.1 hqo6w.2⟩, hb0 hDthB⟩
  -- ### the angular moment `FK w`
  have hfkfacts := hfk hα0 hα1 w hqo6w hw.mem hw.l12
  have hFKsmo : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.FK w z) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_FKw_of_classC hw
  have hFKmem6 : Work.Spaces.HkMem α 6 (fun z _ => Work.Construction.FK w z) :=
    hfkfacts.2.2.2.1
  have hFKbd6 : Work.Spaces.HkNorm α 6 (fun z _ => Work.Construction.FK w z)
      ≤ Xi * α ^ (-Cpow) * Work.Spaces.HkNorm α 6 w := hfkfacts.2.2.2.2.1
  have hFK5 : Work.FTS.VocabO.HQo α 5 (fun z _ => Work.Construction.FK w z) ∧
      Work.Spaces.HkNorm α 5 (fun z _ => Work.Construction.FK w z) ≤ A1 + A2 + A3 + B0 + 1 := by
    refine ⟨⟨hFKsmo, Work.FTS.OpenPkg.HkMem_mono_open hFKsmo 5 (by norm_num) hFKmem6⟩,
      hb2 ?_⟩
    calc Work.Spaces.HkNorm α 5 (fun z _ => Work.Construction.FK w z)
        ≤ Work.Spaces.HkNorm α 6 (fun z _ => Work.Construction.FK w z) :=
          Work.FTS.StrongLWP.HkNorm_mono_of_mem (by norm_num) hFKmem6
      _ ≤ Xi * α ^ (-Cpow) * Work.Spaces.HkNorm α 6 w := hFKbd6
      _ ≤ Xi * α ^ (-Cpow) * B0 := mul_le_mul_of_nonneg_left hX6' hXiRnn
  -- ### the three `φ`-scaled atoms
  obtain ⟨hphiwm, hphiwb⟩ := hphi hα0 hα1 hw5.1
  obtain ⟨hphiDthm, hphiDthb⟩ := hphi hα0 hα1 hDth5.1
  obtain ⟨hphiDzm, hphiDzb⟩ := hphi hα0 hα1 hDz5.1
  exact ⟨hR, hU, hV, hw5, hDth5, hDz5, hFK5,
    ⟨hphiwm, hb3 (le_trans hphiwb (mul_le_mul_of_nonneg_left hwB hCphi.le))⟩,
    ⟨hphiDthm, hb3 (le_trans hphiDthb (mul_le_mul_of_nonneg_left hDthB hCphi.le))⟩,
    ⟨hphiDzm, hb3 (le_trans hphiDzb (mul_le_mul_of_nonneg_left hDzB hCphi.le))⟩⟩

end Work.FTS.StrongEps.H5.Atoms
