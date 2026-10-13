import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Ineq
import Submission.Work.FTS.StrongEps.EpsWPBounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option maxHeartbeats 1600000

theorem epsWP_hyp_bounds_fam {α C₀ Ce Cs T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {G : ℕ → Work.FTS.Galerkin.Fam}
    {ε : ℕ → ℝ}
    (hα : α ∈ Set.Ioc 0 1)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hC : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T, Work.FTS.ClassC.ClassC α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s))
    (hb4 : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T, Work.FTS.Nonlin.Xn α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) ≤ C₀ * α ^ 2)
    (hb6 : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T, Work.FTS.StrongGlobal.Xn6 α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) ≤ Ce) :
    (∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T, ∀ z ∈ Work.Spaces.Iz,
        |Work.Construction.L12 (Work.FTS.Galerkin.slice
          (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z| ≤ B) ∧
      (∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T,
        |Work.Coercivity.L12f (Work.Coercivity.Transport (Work.FTS.Galerkin.slice
          (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)) 0| ≤ B) ∧
      (∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T, ∀ z ∈ Set.Ioi (0 : ℝ),
        |Work.Construction.FK (Work.FTS.Galerkin.slice
          (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z| ≤ B) ∧
      (∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T,
        |Work.Construction.mubar
          (Work.Construction.N0 α (Work.Construction.Ftau α
            (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
            (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s))
          (Work.Construction.N α (Work.Construction.Ftau α
            (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
            (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E
              (Work.FTS.StrongEps.JfamP ρ (ε n) (G n))) s))| ≤ B) := by
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  obtain ⟨CL, hCLpos, hCL⟩ := L12_abs_le_Xn
  obtain ⟨CT, hCTpos, hCT⟩ := Work.FTS.StrongPersist.L3Aux.Transport_L12_zero_le
  obtain ⟨CF, hCF0, hCF⟩ := Work.FTS.StrongEps.FK_abs_le_of_classC
  obtain ⟨CZ, hCZpos, hCZ⟩ := Work.FTS.OpenPkg.l12zero_field
  obtain ⟨K0, hK0pos, hN0z⟩ :=
    Work.FTS.StrongEps.ClassCRHS.HkMemXnN0 (α := α) hα (C₀ := C₀) (B := Ce)
  obtain ⟨K1, hK1pos, hN1z⟩ :=
    Work.FTS.StrongEps.ClassCRHS.HkMemXnN (α := α) hα (C₀ := C₀) (B := Ce) (Ce := Ce) (Cs := Cs)
      (Φs := Φs)
  have hX0 : 0 ≤ max (C₀ * α ^ 2) 0 := le_max_right _ _
  have hCe0 : 0 ≤ max Ce 0 := le_max_right _ _
  refine ⟨⟨CL * max (C₀ * α ^ 2) 0 + 1, by positivity, ?_⟩,
    ⟨CT * max (C₀ * α ^ 2) 0 + 1, by positivity, ?_⟩,
    ⟨CF * max Ce 0 + 1, by positivity, ?_⟩,
    ⟨CZ * (K0 + K1) + 1, by positivity, ?_⟩⟩
  · -- `L₁₂` of the slice, uniformly in `n`
    intro n s hs z hz
    have hCw := hC n s hs
    have hf : Work.FTS.VocabO.HQo α 4 (slice (JfamP ρ (ε n) (G n)) s) :=
      ⟨hCw.reg, Work.FTS.OpenPkg.HkMem_mono_open hCw.reg 4 (by norm_num) hCw.mem⟩
    have h1 := hCL α hα0 _ hf z hz
    have h2 : Work.FTS.Nonlin.Xn α (slice (JfamP ρ (ε n) (G n)) s) ≤ max (C₀ * α ^ 2) 0 :=
      le_trans (hb4 n s hs) (le_max_left _ _)
    have h3 := mul_le_mul_of_nonneg_left h2 hCLpos.le
    have h4 : 0 ≤ CL * max (C₀ * α ^ 2) 0 := mul_nonneg hCLpos.le hX0
    linarith
  · -- `L₁₂(Transport ·)(0)` of the slice, uniformly in `n`
    intro n s hs
    have hCw := hC n s hs
    have hm4 : Work.Spaces.HkMem α 4 (slice (JfamP ρ (ε n) (G n)) s) :=
      Work.FTS.OpenPkg.HkMem_mono_open hCw.reg 4 (by norm_num) hCw.mem
    have h1 := hCT α _ hα0 hα1 hm4
    have h2 : Work.Spaces.HkNorm α 4 (slice (JfamP ρ (ε n) (G n)) s) ≤ max (C₀ * α ^ 2) 0 :=
      le_trans (hb4 n s hs) (le_max_left _ _)
    have h3 := mul_le_mul_of_nonneg_left h2 hCTpos.le
    have h4 : 0 ≤ CT * max (C₀ * α ^ 2) 0 := mul_nonneg hCTpos.le hX0
    linarith
  · -- `FK` of the slice, uniformly in `n`
    intro n s hs z hz
    have h1 := hCF α (max Ce 0) hα (hC n s hs)
      (le_trans (hb6 n s hs) (le_max_left _ _)) z hz
    have h2 : 0 ≤ CF * max Ce 0 := mul_nonneg hCF0 hCe0
    linarith
  · -- `mubar` of the slice, uniformly in `n`
    intro n s hs
    set w : Fn := slice (JfamP ρ (ε n) (G n)) s with hw
    have hCw : Work.FTS.ClassC.ClassC α w := hC n s hs
    have hXw : Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 := hb4 n s hs
    have hBw : Work.Spaces.HkNorm α 6 w ≤ Ce := hb6 n s hs
    have hellw : Work.FTS.VocabO.EllPkgGo α Ce w (E w) := (hEll w hCw).1
    have hsmo := Work.FTS.StrongEps.ClassCRHS.SmoothOpenRHS hα0 hα1 hCw hellw hstar
    obtain ⟨hmemN0, hbndN0⟩ := hN0z hCw hXw hBw
    obtain ⟨hmemN1, hbndN1⟩ := hN1z hCw hXw hBw hellw hstar
    have hN0Q : Work.FTS.VocabO.HQo α 4 (Work.Construction.N0 α (Work.Construction.Ftot α w) w) :=
      ⟨hsmo.2.2.2.1, hmemN0⟩
    have hN1Q : Work.FTS.VocabO.HQo α 4
        (Work.Construction.N α (Work.Construction.Ftot α w) (fun z θ => Φs z θ + E w z θ)) :=
      ⟨hsmo.2.2.2.2, hmemN1⟩
    have hL0 := hCZ α hα0 hα1 _ hN0Q
    have hL1 := hCZ α hα0 hα1 _ hN1Q
    have hF : Work.Construction.Ftau α (JfamP ρ (ε n) (G n)) s = Work.Construction.Ftot α w := by
      funext z θ
      rw [hw]
      rfl
    have hPhi : slice (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ (ε n) (G n))) s
        = fun z θ => Φs z θ + E w z θ := by
      funext z θ
      rw [hw]
      rfl
    rw [hF, hPhi]
    have hmb : Work.Construction.mubar
        (Work.Construction.N0 α (Work.Construction.Ftot α w) w)
        (Work.Construction.N α (Work.Construction.Ftot α w) (fun z θ => Φs z θ + E w z θ))
        = Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α w) w) 0
          + Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α w)
              (fun z θ => Φs z θ + E w z θ)) 0 := rfl
    rw [hmb]
    have hXn0 : 0 ≤ Work.FTS.Nonlin.Xn α
        (Work.Construction.N0 α (Work.Construction.Ftot α w) w) :=
      Work.Spaces.HkNorm_nonneg α 4 _
    have hXn1 : 0 ≤ Work.FTS.Nonlin.Xn α
        (Work.Construction.N α (Work.Construction.Ftot α w) (fun z θ => Φs z θ + E w z θ)) :=
      Work.Spaces.HkNorm_nonneg α 4 _
    refine le_trans (abs_add_le _ _) ?_
    have hstep : |Work.Construction.L12
            (Work.Construction.N0 α (Work.Construction.Ftot α w) w) 0|
          + |Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α w)
              (fun z θ => Φs z θ + E w z θ)) 0|
        ≤ CZ * K0 + CZ * K1 := by
      refine add_le_add (le_trans hL0 (mul_le_mul_of_nonneg_left hbndN0 hCZpos.le))
        (le_trans hL1 (mul_le_mul_of_nonneg_left hbndN1 hCZpos.le))
    have hfin : CZ * K0 + CZ * K1 ≤ CZ * (K0 + K1) + 1 := by
      nlinarith [hCZpos.le, hK0pos.le, hK1pos.le]
    linarith

end Work.FTS.StrongEps

end
