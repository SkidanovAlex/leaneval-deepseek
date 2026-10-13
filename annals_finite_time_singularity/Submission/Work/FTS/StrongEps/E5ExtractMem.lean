/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/E5ExtractMem.lean` — the extraction from the scheme's data

`E5Extract_of_hbdd` (`E5ExtractHbdd.lean`) produces the subsequence and the limit curve from the
**value** bound of `epsRHSP`; `hbdd_of_mem_compact` (`EpsHbdd.lean`) produces that value bound from
the interface data of the projected family.  This module composes them, so that the whole E5
extraction is available from

* the solutions (`IsEpsSolP`) and their τ-regularity (`EpsRegP`),
* the class-`C` data, the `ℋ⁴`-bound and the `ℋ⁶`-bound of the *projected* slices (`hC`, `hb4`,
  `hb6p`),
* the smoothness, the `ℋ⁶`-honesty and the `ℋ⁶`-bound of the *plain* slices (`hsm`, `hmem6`,
  `hb6`),

with no slot-wise hypothesis anywhere.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.E5ExtractHbdd
import Submission.Work.FTS.StrongEps.EpsHbdd
import Submission.Work.FTS.StrongEps.EpsMemRegP
import Submission.Work.FTS.StrongEps.JfamP_norm
import Submission.Work.FTS.ClassC.A4

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

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-- **The `E5` extraction from the scheme's data.** -/
theorem E5Extract_of_mem_seq {α C₀ Ce Cs K' T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {g₀ : Fn} {ε : ℕ → ℝ} {G : ℕ → Fam}
    (hα : α ∈ Set.Ioc 0 1) (hρ : IsSmoothKernel ρ)
    (hc1 : 1 / 10 ≤ Work.Spaces.c α) (hc2 : Work.Spaces.c α ≤ 10)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : MuLamOK α C₀ Φs E)
    (hε : ∀ k : ℕ, ε k ∈ Set.Ioc 0 1) (hT : 0 < T)
    (hsol : ∀ k : ℕ, IsEpsSolP α ρ (ε k) T Φs E g₀ (G k))
    (hreg : ∀ k : ℕ, EpsRegP α ρ (ε k) T (G k))
    (hC : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T,
      Work.FTS.ClassC.ClassC α (slice (JfamP ρ (ε n) (G n)) s))
    (hb4 : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T,
      Work.FTS.Nonlin.Xn α (slice (JfamP ρ (ε n) (G n)) s) ≤ C₀ * α ^ 2)
    (hb6p : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T,
      Work.FTS.StrongGlobal.Xn6 α (slice (JfamP ρ (ε n) (G n)) s) ≤ Ce)
    (hsm : ∀ k : ℕ, ∀ τ ∈ Set.Icc 0 T, Work.FTS.EllipticEst.SmoothOpen (slice (G k) τ))
    (hmem6 : ∀ k : ℕ, ∀ τ ∈ Set.Icc 0 T, Work.Spaces.HkMem α 6 (slice (G k) τ))
    (hb6 : ∀ k : ℕ, ∀ τ ∈ Set.Icc 0 T, Work.FTS.StrongGlobal.Xn6 α (slice (G k) τ) ≤ K') :
    ∃ (φ : ℕ → ℕ) (F : ℝ → Fn), StrictMono φ ∧
      ∀ τ ∈ Set.Icc 0 T, ConvLocUnifH6 α K' (fun n => slice (G (φ n)) τ) (F τ) := by
  -- `hcont` from the joint `C¹` of the solutions
  have hcont : ∀ k : ℕ, ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 →
      ContinuousOn (fun s : ℝ => epsRHSP α ρ (ε k) Φs E (G k) s p.1 p.2) (Set.Icc 0 T) :=
    fun k => continuousOn_epsRHSP_of_regP hT (hsol k) (hreg k)
  -- `hbdd` from the value bound of `epsWP` on windows
  have hbdd : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ p ∈ K,
        |epsRHSP α ρ (ε n) Φs E (G n) s p.1 p.2| ≤ C :=
    fun K hK hKQ => hbdd_of_mem_compact (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (T := T)
      (ρ := ρ) (Φs := Φs) (E := E) (G := G) (ε := ε) hα hρ hε hT.le hc1 hc2 hEll hstar hml
      hC hb4 hb6p hK hKQ
  exact E5Extract_of_hbdd (α := α) (B := K') (T := T) (ρ := ρ) (Φs := Φs) (E := E) (g₀ := g₀)
    (ε := ε) (G := G) hα hρ hε hsol hsm hmem6 hb6 hcont hbdd

/-! ## The extraction from `EpsUniformMem` -/

/-- **The `E5` extraction from the interface `EpsUniformMem`.**  All the hypotheses of
`E5Extract_of_mem_seq` are read off the interface (`EpsUniformMem.exists_seq_one`), with the
projected `ℋ⁶`-bound produced by `HkNorm_JfamP_le` from the interface's bound on the *plain*
slices. -/
theorem E5Extract_of_mem {α C₀ K Ce Cs : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {g₀ : Fn}
    (hU : EpsUniformMem α ρ Φs E g₀ C₀ K) (hα : α ∈ Set.Ioc 0 1) (hρ : IsSmoothKernel ρ)
    (hc1 : 1 / 10 ≤ Work.Spaces.c α) (hc2 : Work.Spaces.c α ≤ 10)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : MuLamOK α C₀ Φs E)
    {T : ℝ} (hT : 0 < T) :
    ∃ (K' : ℝ) (ε : ℕ → ℝ) (G : ℕ → Fam) (φ : ℕ → ℕ) (F : ℝ → Fn),
      K ≤ K' ∧ (∀ k : ℕ, ε k ∈ Set.Ioc 0 1) ∧ StrictMono φ ∧
      (∀ k : ℕ, IsEpsSolP α ρ (ε k) T Φs E g₀ (G k)) ∧
      (∀ k : ℕ, EpsRegP α ρ (ε k) T (G k)) ∧
      (∀ k : ℕ, ∀ τ ∈ Set.Icc 0 T, Work.FTS.StrongGlobal.Xn6 α (slice (G k) τ) ≤ K') ∧
      (∀ τ ∈ Set.Icc 0 T, ConvLocUnifH6 α K' (fun n => slice (G (φ n)) τ) (F τ)) := by
  obtain ⟨-, -, K', hKK', ε, hε, hε0, Maj, hMaj, G, hG⟩ := hU.exists_seq_one hT
  have hsol : ∀ k : ℕ, IsEpsSolP α ρ (ε k) T Φs E g₀ (G k) := fun k => (hG k).1
  have hJ : ∀ k : ℕ, ∀ τ ∈ Set.Icc 0 T,
      ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => G k p.1 p.2.1 p.2.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 T) :=
    fun k τ hτ => (hG k).2 τ hτ |>.2.2.2.2.2.2.1
  have hreg : ∀ k : ℕ, EpsRegP α ρ (ε k) T (G k) := by
    intro k
    refine ⟨hJ k 0 ⟨le_rfl, hT.le⟩, fun τ hτ => ⟨(hG k).2 τ hτ |>.1, (hG k).2 τ hτ |>.2.2.1, ?_⟩⟩
    rw [← slice_JfamP]
    exact (hG k).2 τ hτ |>.2.2.2.2.2.1
  have hC : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T,
      Work.FTS.ClassC.ClassC α (slice (JfamP ρ (ε n) (G n)) s) :=
    fun n s hs => (hG n).2 s hs |>.2.2.2.2.2.1
  have hb4 : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T,
      Work.FTS.Nonlin.Xn α (slice (JfamP ρ (ε n) (G n)) s) ≤ C₀ * α ^ 2 :=
    fun n s hs => (hG n).2 s hs |>.2.2.2.1
  have hsm : ∀ k : ℕ, ∀ τ ∈ Set.Icc 0 T, Work.FTS.EllipticEst.SmoothOpen (slice (G k) τ) :=
    fun k τ hτ => (hG k).2 τ hτ |>.1
  have hmem6 : ∀ k : ℕ, ∀ τ ∈ Set.Icc 0 T, Work.Spaces.HkMem α 6 (slice (G k) τ) :=
    fun k τ hτ => (hG k).2 τ hτ |>.2.2.1
  have hb6 : ∀ k : ℕ, ∀ τ ∈ Set.Icc 0 T, Work.FTS.StrongGlobal.Xn6 α (slice (G k) τ) ≤ K' :=
    fun k τ hτ => (hG k).2 τ hτ |>.2.2.2.2.1
  -- the projected `ℋ⁶`-bound, from `HkNorm_JfamP_le`
  obtain ⟨A, hA0, hA⟩ := Work.FTS.StrongEps.HkNorm_JfamP_le (ρ := ρ) hρ
  set Ce' : ℝ := max Ce (A * K') with hCe'def
  have hb6p : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T,
      Work.FTS.StrongGlobal.Xn6 α (slice (JfamP ρ (ε n) (G n)) s) ≤ Ce' := by
    intro n s hs
    have h1 := hA (α := α) (ε := ε n) hα (hε n) (g := G n) (s := s)
      (fun k => (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp (hsm n s hs) k)
      (hmem6 n s hs)
    exact le_trans (le_trans h1.2 (mul_le_mul_of_nonneg_left (hb6 n s hs) hA0))
      (le_max_right _ _)
  -- the elliptic packages, at the (larger) constant `Ce'`
  have hEll' : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce' u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce' u (E u) :=
    fun u hu => ⟨Work.FTS.ClassC.EllPkgGo_mono hα.1 (hEll u hu).1 (by rw [hCe'def]; exact le_max_left _ _),
      Work.FTS.ClassC.EllPkgK_mono (hEll u hu).2 (by rw [hCe'def]; exact le_max_left _ _)⟩
  obtain ⟨φ, F, hφ, hconv⟩ := E5Extract_of_mem_seq (α := α) (C₀ := C₀) (Ce := Ce') (Cs := Cs)
    (K' := K') (T := T) (ρ := ρ) (Φs := Φs) (E := E) (g₀ := g₀) (ε := ε) (G := G)
    hα hρ hc1 hc2 hEll' hstar hml hε hT hsol hreg hC hb4 hb6p hsm hmem6 hb6
  exact ⟨K', ε, G, φ, F, hKK', hε, hφ, hsol, hreg, hb6, hconv⟩

end Work.FTS.StrongEps
