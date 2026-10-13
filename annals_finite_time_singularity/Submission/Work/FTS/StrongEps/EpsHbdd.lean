/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsHbdd.lean` — `hbdd` for the `E5` assembly, from the interface
# data of the sequence

This module assembles the `hbdd` hypothesis of `EpsLimVolterraP` — at every point of the open
quadrant a bound on the scheme's right-hand side *uniform in the family index and in the fake time* —

  `∀ p ∈ Q0, ∃ C, ∀ n, ∀ s ∈ Icc 0 T, |epsRHSP α ρ (ε n) Φs E (G n) s p.1 p.2| ≤ C`

from the interface data of the sequence alone:

* the window compact and its shift property: `exists_shift_window_compact` at the maximal shift
  `|q| ≤ 1` (all the scales satisfy `ε n ≤ 1`);
* the value bound of `epsWP` on the window, uniform in `n`: `epsWP_sup_le_fam`;
* the uniform ℋ⁴-size of `epsWP`: `epsWP_hkMem4_bnd_fam`;
* the per-`n` smoothness of `epsWP`, which needs no constant: `smoothOpen_epsWP`;
* the common correction bound `|L₁₂(J_{ε n}(epsWP … s))(0)| ≤ Cc`: `epsWP_corr_le_fam`;
* the pointwise split and the mollifier average: `hbdd_of_mem` (`EpsRHSPSup.lean`).

Everything here is `sorry`-free.
-/
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Submission.Work.FTS.StrongEps.EpsRHSPSup
import Submission.Work.FTS.StrongEps.epsWP_sup_le_fam
import Submission.Work.FTS.StrongEps.epsWP_hkMem4_bnd_fam
import Submission.Work.FTS.StrongEps.exists_shift_window_compact

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

/-- **`hbdd` for `EpsLimVolterraP`, from the interface data of the sequence.** -/
theorem hbdd_of_mem_all {α C₀ Ce Cs T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {G : ℕ → Fam} {ε : ℕ → ℝ}
    (hα : α ∈ Set.Ioc 0 1) (hρ : IsSmoothKernel ρ) (hε : ∀ n : ℕ, ε n ∈ Set.Ioc 0 1)
    (hT : 0 ≤ T) (hc1 : 1 / 10 ≤ Work.Spaces.c α) (hc2 : Work.Spaces.c α ≤ 10)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : MuLamOK α C₀ Φs E)
    (hC : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T,
      Work.FTS.ClassC.ClassC α (slice (JfamP ρ (ε n) (G n)) s))
    (hb4 : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T,
      Work.FTS.Nonlin.Xn α (slice (JfamP ρ (ε n) (G n)) s) ≤ C₀ * α ^ 2)
    (hb6 : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T,
      Work.FTS.StrongGlobal.Xn6 α (slice (JfamP ρ (ε n) (G n)) s) ≤ Ce) :
    ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T,
        |epsRHSP α ρ (ε n) Φs E (G n) s p.1 p.2| ≤ C := by
  intro p hp
  -- the window compact at the maximal shift `|q| ≤ 1`
  have hK : IsCompact ({p} : Set (ℝ × ℝ)) := isCompact_singleton
  have hKQ : ({p} : Set (ℝ × ℝ)) ⊆ Work.FTS.EllipticEst.Q0 := by
    intro q hq; rw [Set.mem_singleton_iff] at hq; subst hq; exact hp
  obtain ⟨K', hK'c, hK'Q, hKK', hshift1⟩ :=
    Work.FTS.StrongEps.exists_shift_window_compact one_pos le_rfl hK hKQ
  have hpK' : p ∈ K' := hKK' (Set.mem_singleton p)
  -- the value bound of `epsWP` on the window, uniform in the index
  obtain ⟨B, hB0, hwp⟩ :=
    Work.FTS.StrongEps.epsWP_sup_le_fam (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (T := T)
      (ρ := ρ) (Φs := Φs) (E := E) (G := G) (ε := ε) hα hρ hε hT hc1 hc2 hEll hstar hml
      hC hb4 hb6 hK'c hK'Q
  -- the uniform `ℋ⁴`-size of `epsWP`
  obtain ⟨KW, hKW0, hKWb⟩ :=
    Work.FTS.StrongEps.epsWP_hkMem4_bnd_fam (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (T := T)
      (ρ := ρ) (Φs := Φs) (E := E) (G := G) (ε := ε) hα hEll hstar hml hC hb4 hb6
  -- the per-index smoothness of `epsWP` (no constant involved)
  have hsm : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T,
      Work.FTS.EllipticEst.SmoothOpen (epsWP α ρ (ε n) Φs E (G n) s) :=
    fun n => Work.FTS.StrongEps.smoothOpen_epsWP (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs)
      (T := T) (ρ := ρ) (Φs := Φs) (E := E) (g := G n) (ε := ε n) hα hEll hstar (hC n)
  -- the common correction bound
  obtain ⟨Cc, hCc0, hcorr⟩ :=
    Work.FTS.StrongEps.epsWP_corr_le_fam (α := α) (T := T) (KW := KW) (ρ := ρ) (Φs := Φs)
      (E := E) (G := G) (ε := ε) hρ hα hε hsm hKWb
  refine Work.FTS.StrongEps.hbdd_of_mem (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (T := T)
    (ρ := ρ) (Φs := Φs) (E := E) (G := G) (ε := ε) hρ hε hp hB0.le hCc0 ?_ hcorr
  exact ⟨K', hK'c, hK'Q, hpK',
    (fun n q hq1 hq2 => hshift1 p (Set.mem_singleton p) q (le_trans hq1 (hε n).2)
      (le_trans hq2 (hε n).2)),
    hwp⟩

/-- **The compact form of `hbdd`.**  The same assembly as `hbdd_of_mem_all`, but for a compact
`K ⊆ Q0` (which is the shape `EpsProfileLip` consumes), using `exists_shift_window_compact` on `K`
itself. -/
theorem hbdd_of_mem_compact {α C₀ Ce Cs T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {G : ℕ → Fam} {ε : ℕ → ℝ}
    (hα : α ∈ Set.Ioc 0 1) (hρ : IsSmoothKernel ρ) (hε : ∀ n : ℕ, ε n ∈ Set.Ioc 0 1)
    (hT : 0 ≤ T) (hc1 : 1 / 10 ≤ Work.Spaces.c α) (hc2 : Work.Spaces.c α ≤ 10)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : MuLamOK α C₀ Φs E)
    (hC : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T,
      Work.FTS.ClassC.ClassC α (slice (JfamP ρ (ε n) (G n)) s))
    (hb4 : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T,
      Work.FTS.Nonlin.Xn α (slice (JfamP ρ (ε n) (G n)) s) ≤ C₀ * α ^ 2)
    (hb6 : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T,
      Work.FTS.StrongGlobal.Xn6 α (slice (JfamP ρ (ε n) (G n)) s) ≤ Ce)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKQ : K ⊆ Work.FTS.EllipticEst.Q0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T, ∀ p ∈ K,
      |epsRHSP α ρ (ε n) Φs E (G n) s p.1 p.2| ≤ C := by
  obtain ⟨K', hK'c, hK'Q, hKK', hshift1⟩ :=
    Work.FTS.StrongEps.exists_shift_window_compact one_pos le_rfl hK hKQ
  obtain ⟨B, hB0, hwp⟩ :=
    Work.FTS.StrongEps.epsWP_sup_le_fam (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (T := T)
      (ρ := ρ) (Φs := Φs) (E := E) (G := G) (ε := ε) hα hρ hε hT hc1 hc2 hEll hstar hml
      hC hb4 hb6 hK'c hK'Q
  obtain ⟨KW, hKW0, hKWb⟩ :=
    Work.FTS.StrongEps.epsWP_hkMem4_bnd_fam (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (T := T)
      (ρ := ρ) (Φs := Φs) (E := E) (G := G) (ε := ε) hα hEll hstar hml hC hb4 hb6
  have hsm : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T,
      Work.FTS.EllipticEst.SmoothOpen (epsWP α ρ (ε n) Φs E (G n) s) :=
    fun n => Work.FTS.StrongEps.smoothOpen_epsWP (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs)
      (T := T) (ρ := ρ) (Φs := Φs) (E := E) (g := G n) (ε := ε n) hα hEll hstar (hC n)
  obtain ⟨Cc, hCc0, hcorr⟩ :=
    Work.FTS.StrongEps.epsWP_corr_le_fam (α := α) (T := T) (KW := KW) (ρ := ρ) (Φs := Φs)
      (E := E) (G := G) (ε := ε) hρ hα hε hsm hKWb
  obtain ⟨B', hB'0, hbd⟩ := Work.FTS.StrongEps.epsRHSP_sup_le_fam (α := α) (C₀ := C₀) (Ce := Ce)
    (Cs := Cs) (T := T) (B := B) (Cc := Cc) hρ hε hK hKQ hKK'
    (fun n p hp q hq1 hq2 => hshift1 p hp q (le_trans hq1 (hε n).2) (le_trans hq2 (hε n).2))
    hB0.le hwp hCc0 hcorr
  exact ⟨B', hB'0.le, fun n s hs p hp => hbd n s hs p hp⟩


end Work.FTS.StrongEps
