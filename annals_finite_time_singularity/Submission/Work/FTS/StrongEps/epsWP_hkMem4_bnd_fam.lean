import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.Linarith.Frontend
import Submission.Work.FTS.StrongEps.EpsRLX.CCSharp.HonTermsC.Part2C
import Submission.Work.FTS.StrongEps.EpsRLX.LGTDiffClassC
import Submission.Work.FTS.StrongEps.H5.Nb5Core
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS_RegExport.RXT.Sys.pth_vop_slot_bd
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRLX.CCSharp.HonestTermsBoundC =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsRLX.CCSharp

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

theorem HonestTermsBoundC {α α₂ Ci Ce Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u))
    (hα : 0 < α) (hαα₂ : α ≤ α₂) :
    ∃ K : ℝ, 0 < K ∧ ∀ {W₁ W₂ : Work.FTS.Galerkin.Fn},
      Work.FTS.ClassC.ClassC α W₁ → Work.FTS.ClassC.ClassC α W₂ → α ≤ 1 →
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TRB α E W₂ (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TRB α E W₂ (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TRB α E W₂ (fun z θ => W₁ z θ - W₂ z θ))
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂) * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TUB α E W₂ (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TUB α E W₂ (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TUB α E W₂ (fun z θ => W₁ z θ - W₂ z θ))
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂) * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TVB α E W₂ (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TVB α E W₂ (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TVB α E W₂ (fun z θ => W₁ z θ - W₂ z θ))
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂) * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TDB α W₂ (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TDB α W₂ (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TDB α W₂ (fun z θ => W₁ z θ - W₂ z θ))
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂) * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TEB α W₂ (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TEB α W₂ (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TEB α W₂ (fun z θ => W₁ z θ - W₂ z θ))
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂) * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TRD α E W₁ (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TRD α E W₁ (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TRD α E W₁ (fun z θ => W₁ z θ - W₂ z θ))
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂) * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TUD α E W₁ (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TUD α E W₁ (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TUD α E W₁ (fun z θ => W₁ z θ - W₂ z θ))
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂) * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TVD α E W₁ (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TVD α E W₁ (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TVD α E W₁ (fun z θ => W₁ z θ - W₂ z θ))
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂) * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TDD α W₁ (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TDD α W₁ (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TDD α W₁ (fun z θ => W₁ z θ - W₂ z θ))
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂) * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TED α W₁ (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TED α W₁ (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TED α W₁ (fun z θ => W₁ z θ - W₂ z θ))
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂) * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ))
      := by
  obtain ⟨K1, hK1pos, h1⟩ := HonTermsC.Part1C hN hstar hEll hα hαα₂
  obtain ⟨K2, hK2pos, h2⟩ := HonTermsC.Part2C hN hstar hEll hα hαα₂
  have hK12 : 0 < K1 + K2 := by linarith
  refine ⟨K1 + K2, hK12, ?_⟩
  intro W₁ W₂ hW₁ hW₂ hα1
  have hsub : Work.FTS.ClassC.ClassC α (fun z θ => W₁ z θ - W₂ z θ) := sub_classC hW₁ hW₂
  obtain ⟨a1, a2, a3, a4, a5⟩ := h1 hW₁ hW₂ hsub hα1
  obtain ⟨b1, b2, b3, b4, b5⟩ := h2 hW₁ hW₂ hsub hα1
  have hS0 : (0 : ℝ) ≤ 1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂ := by
    have hW1 := Work.Spaces.HkNorm_nonneg α 5 W₁
    have hW2 := Work.Spaces.HkNorm_nonneg α 5 W₂
    linarith
  have hnh : (0 : ℝ) ≤ Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) :=
    Work.Spaces.HkNorm_nonneg α 5 (fun z θ => W₁ z θ - W₂ z θ)
  have up1 : ∀ {T : Fn},
      Work.FTS.EllipticEst.SmoothOpen T ∧ Work.Spaces.HkMem α 4 T ∧
        Work.FTS.Nonlin.Xn α T
          ≤ K1 * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
              * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) →
      Work.FTS.EllipticEst.SmoothOpen T ∧ Work.Spaces.HkMem α 4 T ∧
        Work.FTS.Nonlin.Xn α T
          ≤ (K1 + K2) * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
              * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by
    rintro T ⟨hS, hM, hX⟩
    exact ⟨hS, hM, le_trans hX (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) hS0) hnh)⟩
  have up2 : ∀ {T : Fn},
      Work.FTS.EllipticEst.SmoothOpen T ∧ Work.Spaces.HkMem α 4 T ∧
        Work.FTS.Nonlin.Xn α T
          ≤ K2 * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
              * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) →
      Work.FTS.EllipticEst.SmoothOpen T ∧ Work.Spaces.HkMem α 4 T ∧
        Work.FTS.Nonlin.Xn α T
          ≤ (K1 + K2) * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
              * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by
    rintro T ⟨hS, hM, hX⟩
    exact ⟨hS, hM, le_trans hX (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) hS0) hnh)⟩
  exact ⟨up1 a1, up1 a2, up1 a3, up1 a4, up1 a5,
    up2 b1, up2 b2, up2 b3, up2 b4, up2 b5⟩

end Work.FTS.StrongEps.EpsRLX.CCSharp
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.epsWP_hkMem4_bnd_fam =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.StrongEps

set_option maxHeartbeats 1600000

/-- **The uniform-in-`(g, ε)` form of `epsWP_hkMem4_bnd`.**  Under the interface hypotheses
`hEll`, `hstar`, `hml` — none of which mentions the family, the scale or the fake-time horizon —
there is a *single* constant `KW > 0` such that for **every** family `g` and **every** `ε`, and for
every `s ∈ Icc 0 T`, the projected right-hand side `epsWP α ρ ε Φs E g s` is `ℋ⁴`-honest and has
`Xn`-size at most `KW`, as soon as the slices of `JfamP ρ ε g` satisfy the class-`C` clauses and the
level-4/level-6 size bounds on `[0,T]`. -/
theorem epsWP_hkMem4_bnd_unif {α C₀ Ce Cs T : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Fn} {E : Fn → Fn}
    (hα : α ∈ Set.Ioc 0 1)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) :
    ∃ KW : ℝ, 0 < KW ∧ ∀ (g : Fam) (ε : ℝ),
      (∀ s ∈ Set.Icc 0 T, Work.FTS.ClassC.ClassC α
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s)) →
      (∀ s ∈ Set.Icc 0 T, Work.FTS.Nonlin.Xn α
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s) ≤ C₀ * α ^ 2) →
      (∀ s ∈ Set.Icc 0 T, Work.FTS.StrongGlobal.Xn6 α
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s) ≤ Ce) →
      ∀ s ∈ Set.Icc 0 T,
      Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s) ≤ KW := by
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  obtain ⟨Kl, hKl, hLGT⟩ := ClassCRHS.HkMemXnLGammaT (α := α) hα (C₀ := C₀) (B := Ce)
  obtain ⟨K0, hK0, hN0⟩ := ClassCRHS.HkMemXnN0 (α := α) hα (C₀ := C₀) (B := Ce)
  obtain ⟨KN, hKN, hN⟩ := ClassCRHS.HkMemXnN (α := α) hα (C₀ := C₀) (B := Ce) (Ce := Ce)
    (Cs := Cs) (Φs := Φs)
  obtain ⟨CM, hCM, hmub⟩ :=
    epsWP_mubar_bound (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (Φs := Φs) (E := E)
      hα hEll hstar
  obtain ⟨KAK, hKAK, hra⟩ := Work.FTS.Nonlinear.Pieces.rak_bound
  have hAKmem : Work.Spaces.HkMem α 4 (Work.Construction.AK α) :=
    Work.FTS.NonlinRows.HkMem_AK α hα0 hα1
  have hAKsmo : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.AK α) :=
    Work.FTS.StrongPersist.AK_smoothO α
  have hAKbd : Work.FTS.Nonlin.Xn α (Work.Construction.AK α) ≤ KAK := hra hα0 hα1
  set Lam : ℝ := 2 * CM * KAK + 1 with hLamdef
  set Kst : ℝ := 2 * ((1 / 2) * max (C₀ * α ^ 2) 0 + 2 * max Ce 0) + 1 with hKstdef
  have hLamnn : 0 ≤ Lam := by rw [hLamdef]; positivity
  have hKstnn : 0 ≤ Kst := by rw [hKstdef]; positivity
  have hKW : 0 < 16 * (Kl + Lam + K0 + KN + Kst) + 1 := by
    linarith [hKl, hLamnn, hK0, hKN, hKstnn]
  refine ⟨16 * (Kl + Lam + K0 + KN + Kst) + 1, hKW, ?_⟩
  intro g ε hC hb4 hb6 s hs
  set w : Fn := slice (Work.FTS.StrongEps.JfamP ρ ε g) s with hwdef
  have hcls : Work.FTS.ClassC.ClassC α w := hC s hs
  have hXw : Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 := hb4 s hs
  have hBw : Work.Spaces.HkNorm α 6 w ≤ Ce := hb6 s hs
  have hwsmo : Work.FTS.EllipticEst.SmoothOpen w := hcls.reg
  have hw7 : Work.Spaces.HkMem α 7 w := hcls.mem
  have hw6 : Work.Spaces.HkMem α 6 w := Work.FTS.OpenPkg.HkMem_mono_open hwsmo 6 (by norm_num) hw7
  have hw5 : Work.Spaces.HkMem α 5 w := Work.FTS.OpenPkg.HkMem_mono_open hwsmo 5 (by norm_num) hw7
  have hw4 : Work.Spaces.HkMem α 4 w := Work.FTS.OpenPkg.HkMem_mono_open hwsmo 4 (by norm_num) hw7
  have hDzsmo : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz w) := hwsmo.Dz
  have hDz4 : Work.Spaces.HkMem α 4 (Work.Spaces.Dz w) :=
    Work.FTS.EllipticEst.UopHk.HkMem_Dz_of_smoothOpen α 4 hwsmo hw5
  have hXn5 : Work.FTS.GalFields.Xn5 α w ≤ Ce :=
    le_trans (Work.FTS.StrongLWP.HkNorm_mono_of_mem (α := α) (k := 6) (k' := 5)
      (by norm_num) hw6) hBw
  have hDzbd : Work.FTS.Nonlin.Xn α (Work.Spaces.Dz w) ≤ Ce :=
    le_trans (Work.FTS.GalFields.Xn_Dz_le_Xn5 hα0 hwsmo hw5) hXn5
  have hellw : Work.FTS.VocabO.EllPkgGo α Ce w (E w) := (hEll w hcls).1
  obtain ⟨hmuOK, hlamOK⟩ := hml w hcls hXw
  obtain ⟨_, _, hLGTsmo, hN0smo, hNsmo⟩ :=
    ClassCRHS.SmoothOpenRHS hα0 hα1 hcls hellw hstar
  have hFtau : Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) s
      = Work.Construction.Ftot α w := rfl
  have hPsis : slice (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g)) s
      = fun z θ => Φs z θ + E w z θ := rfl
  -- ### the five blocks of the right-hand side
  set P1 : Fn := Work.FTS.StrongPersist.linPart α w with hP1def
  set mb : ℝ := Work.Construction.mubar
    (Work.Construction.N0 α (Work.Construction.Ftot α w) w)
    (Work.Construction.N α (Work.Construction.Ftot α w)
      (fun z θ => Φs z θ + E w z θ)) with hmbdef
  set P2 : Fn := fun z θ => -mb * Work.Construction.AK α z θ with hP2def
  set P3 : Fn := Work.Construction.N0 α (Work.Construction.Ftot α w) w with hP3def
  set P4 : Fn := Work.Construction.N α (Work.Construction.Ftot α w)
    (fun z θ => Φs z θ + E w z θ) with hP4def
  set muU : ℝ := Work.FTS.Galerkin.muDyn α
    (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g))
    (Work.FTS.StrongEps.JfamP ρ ε g) s with hmuUdef
  set lamU : ℝ := Work.FTS.Galerkin.lamDyn α
    (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g))
    (Work.FTS.StrongEps.JfamP ρ ε g) s with hlamUdef
  set P5 : Fn := Work.Construction.Nstar muU lamU w with hP5def
  set A2 : Fn := fun z θ => P2 z θ + P3 z θ with hA2def
  set A3 : Fn := fun z θ => A2 z θ + P4 z θ with hA3def
  set A4 : Fn := fun z θ => P1 z θ + A3 z θ with hA4def
  set A5 : Fn := fun z θ => A4 z θ + P5 z θ with hA5def
  have hmuUbd : |muU| ≤ 1 / 2 := hmuOK
  have hlamUbd : |lamU| ≤ 1 := hlamOK
  -- ### the identification of `epsWP` with the block sum
  have hsplit : Work.FTS.StrongEps.epsWP α ρ ε Φs E g s = A5 := by
    funext z θ
    simp only [Work.FTS.StrongEps.epsWP, Work.FTS.Galerkin.dynLin, Work.FTS.Galerkin.dynRHS,
      Work.FTS.StrongPersist.linPart, Work.Construction.gRHS,
      Work.Construction.Nstar, Work.FTS.Galerkin.muDyn, Work.FTS.Galerkin.lamDyn,
      hP1def, hP2def, hP3def, hP4def, hP5def, hmbdef, hmuUdef, hlamUdef,
      hA2def, hA3def, hA4def, hA5def, hFtau, hPsis, hwdef]
    ring
  -- ### smoothness of the blocks
  have hP1smo : Work.FTS.EllipticEst.SmoothOpen P1 := by
    rw [hP1def]; exact smoothOpen_neg_epsWP hLGTsmo
  have hP2smo : Work.FTS.EllipticEst.SmoothOpen P2 := by
    rw [hP2def]; exact Work.FTS.NonlinRows.smoothOpen_const_mul (-mb) hAKsmo
  have hP3smo : Work.FTS.EllipticEst.SmoothOpen P3 := hN0smo
  have hP4smo : Work.FTS.EllipticEst.SmoothOpen P4 := hNsmo
  have hP5eq : P5 = fun z θ => (-muU) * w z θ
      + (-(muU + lamU + muU * lamU)) * Work.Spaces.Dz w z θ := by
    funext z θ
    rw [hP5def, Work.Construction.Nstar]
    ring
  have hP5smo : Work.FTS.EllipticEst.SmoothOpen P5 := by
    rw [hP5eq]
    exact Work.FTS.NonlinRows.smoothOpen_add
      (Work.FTS.NonlinRows.smoothOpen_const_mul (-muU) hwsmo)
      (Work.FTS.NonlinRows.smoothOpen_const_mul (-(muU + lamU + muU * lamU)) hDzsmo)
  -- ### membership of the blocks
  have hP1mem : Work.Spaces.HkMem α 4 P1 := by
    rw [hP1def]; exact hkMem_neg_epsWP (hLGT (w := w) hcls hXw hBw).1
  have hP2mem : Work.Spaces.HkMem α 4 P2 := by
    rw [hP2def]; exact Work.FTS.StrongEps.PZeroAux.HkMem_const_mul_gen (-mb) hAKmem
  have hP3mem : Work.Spaces.HkMem α 4 P3 := (hN0 (w := w) hcls hXw hBw).1
  have hP4mem : Work.Spaces.HkMem α 4 P4 :=
    (hN (w := w) (Φg := E w) hcls hXw hBw hellw hstar).1
  have hP5mem : Work.Spaces.HkMem α 4 P5 := by
    rw [hP5eq]
    exact Work.FTS.EllipticEst.HkMem_add_open
      (Work.FTS.NonlinRows.smoothOpen_const_mul (-muU) hwsmo)
      (Work.FTS.NonlinRows.smoothOpen_const_mul (-(muU + lamU + muU * lamU)) hDzsmo)
      (Work.FTS.StrongEps.PZeroAux.HkMem_const_mul_gen (-muU) hw4)
      (Work.FTS.StrongEps.PZeroAux.HkMem_const_mul_gen (-(muU + lamU + muU * lamU)) hDz4)
  -- ### the bounds of the blocks
  have hmb_le : |mb| ≤ CM := by
    rw [hmbdef]; exact hmub w hcls hXw hBw
  have hP1bd : Work.FTS.Nonlin.Xn α P1 ≤ Kl := by
    rw [hP1def]
    show Work.Spaces.HkNorm α 4 (-(Work.Coercivity.LGammaT α w)) ≤ Kl
    rw [Work.FTS.EllipticEst.HkNorm_neg]
    exact (hLGT (w := w) hcls hXw hBw).2
  have hP2bd : Work.FTS.Nonlin.Xn α P2 ≤ Lam := by
    rw [hP2def]
    have h1 : Work.FTS.Nonlin.Xn α (fun z θ => -mb * Work.Construction.AK α z θ)
        = |mb| * Work.FTS.Nonlin.Xn α (Work.Construction.AK α) := by
      simpa only [abs_neg] using
        (Work.FTS.EllipticEst.HkNorm_const_mul (α := α) (k := 4) (c := -mb)
          (f := Work.Construction.AK α) hAKsmo.forall)
    rw [h1]
    have h2 : |mb| * Work.FTS.Nonlin.Xn α (Work.Construction.AK α) ≤ CM * KAK :=
      mul_le_mul hmb_le hAKbd (Work.Spaces.HkNorm_nonneg α 4 _) hCM.le
    rw [hLamdef]
    linarith [h2, hCM.le, hKAK.le]
  have hP3bd : Work.FTS.Nonlin.Xn α P3 ≤ K0 := (hN0 (w := w) hcls hXw hBw).2
  have hP4bd : Work.FTS.Nonlin.Xn α P4 ≤ KN :=
    (hN (w := w) (Φg := E w) hcls hXw hBw hellw hstar).2
  have hkapp : |muU + lamU + muU * lamU| ≤ 2 := by
    calc |muU + lamU + muU * lamU| ≤ |muU + lamU| + |muU * lamU| := abs_add_le _ _
      _ ≤ (|muU| + |lamU|) + |muU| * |lamU| :=
          add_le_add (abs_add_le _ _) (le_of_eq (abs_mul _ _))
      _ ≤ (1 / 2 + 1) + (1 / 2) * 1 :=
          add_le_add (add_le_add hmuUbd hlamUbd)
            (mul_le_mul hmuUbd hlamUbd (abs_nonneg _) (by norm_num))
      _ ≤ 2 := by norm_num
  have hP5bd : Work.FTS.Nonlin.Xn α P5 ≤ Kst := by
    rw [hP5eq]
    have hsum := Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα0
      (Work.FTS.NonlinRows.smoothOpen_const_mul (-muU) hwsmo)
      (Work.FTS.NonlinRows.smoothOpen_const_mul (-(muU + lamU + muU * lamU)) hDzsmo)
      (Work.FTS.StrongEps.PZeroAux.HkMem_const_mul_gen (-muU) hw4)
      (Work.FTS.StrongEps.PZeroAux.HkMem_const_mul_gen (-(muU + lamU + muU * lamU)) hDz4)
    have hc1 : Work.Spaces.HkNorm α 4 (fun z θ => (-muU) * w z θ)
        = |muU| * Work.FTS.Nonlin.Xn α w := by
      simpa only [abs_neg] using
        (Work.FTS.EllipticEst.HkNorm_const_mul (α := α) (k := 4) (c := -muU) (f := w)
          hwsmo.forall)
    have hc2 : Work.Spaces.HkNorm α 4
          (fun z θ => (-(muU + lamU + muU * lamU)) * Work.Spaces.Dz w z θ)
        = |muU + lamU + muU * lamU| * Work.FTS.Nonlin.Xn α (Work.Spaces.Dz w) := by
      simpa only [abs_neg] using
        (Work.FTS.EllipticEst.HkNorm_const_mul (α := α) (k := 4)
          (c := -(muU + lamU + muU * lamU)) (f := Work.Spaces.Dz w) hDzsmo.forall)
    refine le_trans hsum ?_
    rw [hc1, hc2]
    have hbr : |muU| * Work.FTS.Nonlin.Xn α w
          + |muU + lamU + muU * lamU| * Work.FTS.Nonlin.Xn α (Work.Spaces.Dz w)
        ≤ (1 / 2) * max (C₀ * α ^ 2) 0 + 2 * max Ce 0 :=
      add_le_add
        (mul_le_mul hmuUbd (le_trans hXw (le_max_left _ _))
          (Work.Spaces.HkNorm_nonneg α 4 w) (by norm_num))
        (mul_le_mul hkapp (le_trans hDzbd (le_max_left _ _))
          (Work.Spaces.HkNorm_nonneg α 4 (Work.Spaces.Dz w)) (by norm_num))
    rw [hKstdef]
    linarith [hbr]
  -- ### the assembly
  have hA2smo : Work.FTS.EllipticEst.SmoothOpen A2 :=
    Work.FTS.NonlinRows.smoothOpen_add hP2smo hP3smo
  have hA3smo : Work.FTS.EllipticEst.SmoothOpen A3 :=
    Work.FTS.NonlinRows.smoothOpen_add hA2smo hP4smo
  have hA4smo : Work.FTS.EllipticEst.SmoothOpen A4 :=
    Work.FTS.NonlinRows.smoothOpen_add hP1smo hA3smo
  have hA5smo : Work.FTS.EllipticEst.SmoothOpen A5 :=
    Work.FTS.NonlinRows.smoothOpen_add hA4smo hP5smo
  have hA2mem : Work.Spaces.HkMem α 4 A2 :=
    Work.FTS.EllipticEst.HkMem_add_open hP2smo hP3smo hP2mem hP3mem
  have hA3mem : Work.Spaces.HkMem α 4 A3 :=
    Work.FTS.EllipticEst.HkMem_add_open hA2smo hP4smo hA2mem hP4mem
  have hA4mem : Work.Spaces.HkMem α 4 A4 :=
    Work.FTS.EllipticEst.HkMem_add_open hP1smo hA3smo hP1mem hA3mem
  have hA5mem : Work.Spaces.HkMem α 4 A5 :=
    Work.FTS.EllipticEst.HkMem_add_open hA4smo hP5smo hA4mem hP5mem
  have hmem : Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s) := by
    rw [hsplit]; exact hA5mem
  have hbd : Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)
      ≤ 16 * (Kl + Lam + K0 + KN + Kst) + 1 := by
    rw [hsplit]
    have hb1 : Work.FTS.Nonlin.Xn α A5
        ≤ 2 * (Work.FTS.Nonlin.Xn α A4 + Work.FTS.Nonlin.Xn α P5) :=
      Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα0 hA4smo hP5smo hA4mem hP5mem
    have hb2 : Work.FTS.Nonlin.Xn α A4
        ≤ 2 * (Work.FTS.Nonlin.Xn α P1 + Work.FTS.Nonlin.Xn α A3) :=
      Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα0 hP1smo hA3smo hP1mem hA3mem
    have hb3 : Work.FTS.Nonlin.Xn α A3
        ≤ 2 * (Work.FTS.Nonlin.Xn α A2 + Work.FTS.Nonlin.Xn α P4) :=
      Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα0 hA2smo hP4smo hA2mem hP4mem
    have hb4 : Work.FTS.Nonlin.Xn α A2
        ≤ 2 * (Work.FTS.Nonlin.Xn α P2 + Work.FTS.Nonlin.Xn α P3) :=
      Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα0 hP2smo hP3smo hP2mem hP3mem
    have e4 : Work.FTS.Nonlin.Xn α A2 ≤ 2 * (Lam + K0) := by linarith [hb4, hP2bd, hP3bd]
    have e3 : Work.FTS.Nonlin.Xn α A3 ≤ 2 * (2 * (Lam + K0) + KN) := by
      linarith [hb3, e4, hP4bd]
    have e2 : Work.FTS.Nonlin.Xn α A4 ≤ 2 * (Kl + 2 * (2 * (Lam + K0) + KN)) := by
      linarith [hb2, hP1bd, e3]
    have e1 : Work.FTS.Nonlin.Xn α A5 ≤ 2 * (2 * (Kl + 2 * (2 * (Lam + K0) + KN)) + Kst) := by
      linarith [hb1, e2, hP5bd]
    linarith [e1, hKl.le, hLamnn, hK0.le, hKN.le, hKstnn]
  exact ⟨hmem, hbd⟩

/-- **The family form of `epsWP_hkMem4_bnd`.**  With the interface hypotheses `hEll`, `hstar`,
`hml` — none of which mentions `n` — a *single* constant `KW > 0` dominates the `Xn`-size of
`epsWP α ρ (ε n) Φs E (G n) s` for every `n` and every `s ∈ Icc 0 T`, and every such right-hand side
is `ℋ⁴`-honest.  This is the form needed when the scheme is solved at every scale `ε n` of a
vanishing sequence: the constant is not allowed to depend on `n`. -/
theorem epsWP_hkMem4_bnd_fam {α C₀ Ce Cs T : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {G : ℕ → Work.FTS.Galerkin.Fam} {ε : ℕ → ℝ}
    (hα : α ∈ Set.Ioc 0 1)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E)
    (hC : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T, Work.FTS.ClassC.ClassC α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s))
    (hb4 : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T, Work.FTS.Nonlin.Xn α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) ≤ C₀ * α ^ 2)
    (hb6 : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T, Work.FTS.StrongGlobal.Xn6 α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) ≤ Ce) :
    ∃ KW : ℝ, 0 < KW ∧ ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T,
      Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s) ≤ KW := by
  obtain ⟨KW, hKW, hkey⟩ :=
    epsWP_hkMem4_bnd_unif (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (T := T) (ρ := ρ)
      (Φs := Φs) (E := E) hα hEll hstar hml
  exact ⟨KW, hKW, fun n s hs =>
    hkey (G n) (ε n) (fun s hs => hC n s hs) (fun s hs => hb4 n s hs)
      (fun s hs => hb6 n s hs) s hs⟩

end Work.FTS.StrongEps
end
end
