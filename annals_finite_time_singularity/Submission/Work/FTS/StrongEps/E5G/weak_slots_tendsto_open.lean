import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Filter.Defs
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.E5Aux3.contDiffOn_two_of_jetLim
import Submission.Work.FTS.StrongEps.E5G.Defs
import Submission.Work.FTS.StrongEps.E5G.slice_lip5_norm
import Submission.Work.FTS.StrongEps.EpsE4Thr.epsRHSP_hkMem_fam
import Submission.Work.FTS.StrongEps.EpsRHSPBdd_unif
import Submission.Work.FTS.StrongEps.EpsZeroMode
import Submission.Work.FTS.StrongEps.epsWP_hkMem4_bnd_fam
import Submission.Work.FTS.StrongEps.smoothOpen_epsWP
import Submission.Work.FTS.StrongEps.smoothOpen_slice_of_epsRHSP
import Submission.Work.FTS.StrongPersist.H6Aux.E2Facts
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.AuxProof
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.HL12RawTower =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5G

/-- **`hl12` for the raw slices of a tower-like sequence.**

The unmollified zero mode is conserved along each `ε`-solution — the proved C2 leaf
`Work.FTS.StrongEps.L12_slice_eq_zero_of_hkMem`, whose inputs are produced as follows:
`hRm` (`HkMem α 4 (epsRHSP α ρ (ε k) Φs E (G k) τ)` plus a uniform `HkNorm α 4`-bound) from
`Work.FTS.StrongEps.EpsE4Thr.epsRHSP_hkMem_fam` and
`Work.FTS.StrongEps.EpsE4Thr.HkNorm_epsRHSP_le`; `hWm`
(`HkMem α 4 (Jeps ρ (ε k) (epsWP α ρ (ε k) Φs E (G k) τ))`) from
`Work.FTS.StrongEps.epsWP_hkMem4_bnd_fam` (membership of `epsWP`),
`Work.FTS.StrongEps.smoothOpen_epsWP` (all-order smoothness of `epsWP`, from `hC`/`hEll`/`hstar`)
and `Work.FTS.StrongEps.HkMem_Jeps` (mollification preserves `HkMem`); the slices' `HkMem α 4` from
`hmem6` by `Work.FTS.OpenPkg.HkMem_mono_open`.

Then the mollifier error `|L₁₂ (J_ε X) 0 − L₁₂ X 0| ≤ C ε ‖X‖_{ℋ⁵}` is
`Work.FTS.StrongEps.E5Aux3.L12_Jeps_slice_tendsto_of_zero`, whose `ℋ⁵`-data come from `hmem6` and
`hb6` (`HkNorm α 5 ≤ HkNorm α 6 = Xn6 ≤ B` by `Work.FTS.StrongPersist.L3Rhs.Assembly.HkNorm_descend_le`).

Note `hEll` is used at the constant `Ce`, and the `epsWP`-line lemmas need the *projected* `ℋ⁶`-bound
`hb6p`; both are exactly what the E5 assembly supplies (via `HkNorm_JfamP_le` + `EllPkgGo_mono`). -/
theorem HL12RawTower {α C₀ Ce Cs T B : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g₀ : Work.FTS.Galerkin.Fn}
    {ε : ℕ → ℝ} {G : ℕ → Work.FTS.Galerkin.Fam}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hc1 : 1 / 10 ≤ Work.Spaces.c α) (hc2 : Work.Spaces.c α ≤ 10)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E)
    (hε : ∀ k : ℕ, ε k ∈ Set.Ioc 0 1) (hε0 : Filter.Tendsto ε Filter.atTop (nhds 0))
    (hT : 0 < T) (hL12g₀ : Work.Construction.L12 g₀ 0 = 0)
    (hsol : ∀ k : ℕ, Work.FTS.StrongEps.IsEpsSolP α ρ (ε k) T Φs E g₀ (G k))
    (hjoint : ∀ k : ℕ, ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => G k p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 T))
    (hsm : ∀ k : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Galerkin.slice (G k) τ))
    (hmem6 : ∀ k : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkMem α 6 (Work.FTS.Galerkin.slice (G k) τ))
    (hb6 : ∀ k : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.StrongGlobal.Xn6 α (Work.FTS.Galerkin.slice (G k) τ) ≤ B)
    (hC : ∀ k : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.ClassC.ClassC α
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε k) (G k)) τ))
    (hb4 : ∀ k : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.Nonlin.Xn α
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε k) (G k)) τ) ≤ C₀ * α ^ 2)
    (hb6p : ∀ k : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.StrongGlobal.Xn6 α
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε k) (G k)) τ) ≤ Ce)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T) :
    Filter.Tendsto (fun k : ℕ =>
        Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ (ε k) (Work.FTS.Galerkin.slice (G k) s)) 0)
      Filter.atTop (nhds 0) := by
  -- ### the ℋ⁵-data of the plain slices at the fixed fake time `s`
  have hXsm : ∀ k : ℕ,
      Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Galerkin.slice (G k) s) :=
    fun k => hsm k s hs
  have hXmem5 : ∀ k : ℕ, Work.Spaces.HkMem α 5 (Work.FTS.Galerkin.slice (G k) s) :=
    fun k => Work.FTS.OpenPkg.HkMem_mono_open (hsm k s hs) 5 (by norm_num) (hmem6 k s hs)
  have hXbd5 : ∀ k : ℕ, Work.Spaces.HkNorm α 5 (Work.FTS.Galerkin.slice (G k) s) ≤ B :=
    fun k => le_trans
      (Work.FTS.StrongPersist.L3Rhs.HkNorm_descend_le (α := α) (k := 5) (k' := 6)
        (by norm_num) (hmem6 k s hs))
      (hb6 k s hs)
  -- ### the uniform ℋ⁶-bound is nonnegative (it dominates the slices' `Xn6`)
  have hB0 : 0 ≤ B :=
    le_trans (Work.Spaces.HkNorm_nonneg α 6 (Work.FTS.Galerkin.slice (G 0) 0))
      (hb6 0 0 ⟨le_rfl, hT.le⟩)
  -- ### the block membership of `epsWP` (at the projected ℋ⁶-bound `Ce`)
  obtain ⟨KW, _hKW, hwp⟩ :=
    Work.FTS.StrongEps.epsWP_hkMem4_bnd_fam (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs)
      (T := T) (ρ := ρ) (Φs := Φs) (E := E) (G := G) (ε := ε)
      hα hEll hstar hml hC hb4 hb6p
  -- ### the two halves of the input of the C2 leaf
  have hX0 : ∀ k : ℕ, Work.Construction.L12 (Work.FTS.Galerkin.slice (G k) s) 0 = 0 := by
    intro k
    have hmemR : ∀ τ ∈ Set.Icc (0 : ℝ) T, Work.Spaces.HkMem α 4
        (Work.FTS.StrongEps.epsRHSP α ρ (ε k) Φs E (G k) τ) :=
      Work.FTS.StrongEps.EpsE4Thr.epsRHSP_hkMem_fam (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs)
        (B := B) (ρ := ρ) (Φs := Φs) (E := E) (g := G k) (ε := ε k) (T := T)
        hα hρ (hε k).1 (hε k).2 hEll hstar hml hB0 (hsm k) (hmem6 k)
        (fun τ hτ => hb6 k τ hτ) (hC k) (hb4 k)
    obtain ⟨R, _hRpos, hRbd⟩ :=
      Work.FTS.StrongEps.EpsE4Thr.HkNorm_epsRHSP_le (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs)
        (B := B) (ρ := ρ) (Φs := Φs) (E := E) (g := G k) (ε := ε k) (T := T)
        hα hρ (hε k).1 (hε k).2 hEll hstar hml hB0 (hsm k) (hmem6 k)
        (fun τ hτ => hb6 k τ hτ) (hC k) (hb4 k)
    have hWmem : ∀ τ ∈ Set.Icc (0 : ℝ) T, Work.Spaces.HkMem α 4
        (Work.FTS.StrongEps.Jeps ρ (ε k)
          (Work.FTS.StrongEps.epsWP α ρ (ε k) Φs E (G k) τ)) := by
      intro τ hτ
      refine Work.FTS.StrongEps.HkMem_Jeps hρ.moll hα (hε k).1 ?_ (hwp k τ hτ).1
      exact (Work.FTS.StrongEps.smoothOpen_epsWP (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs)
        (T := T) (ρ := ρ) (Φs := Φs) (E := E) (g := G k) (ε := ε k)
        hα hEll hstar (hC k) τ hτ).forall
    exact Work.FTS.StrongEps.L12_slice_eq_zero_of_hkMem hα hρ (hε k).1 hT (hsol k) (hjoint k)
      (hsm k)
      (fun τ hτ => Work.FTS.OpenPkg.HkMem_mono_open (hsm k τ hτ) 4 (by norm_num) (hmem6 k τ hτ))
      (fun τ hτ => ⟨hmemR τ hτ, hRbd τ hτ⟩) hWmem hL12g₀ s hs
  -- ### the mollifier error along the vanishing sequence `ε → 0`
  exact Work.FTS.StrongEps.E5Aux3.L12_Jeps_slice_tendsto_of_zero
    (B := B) (X := fun k => Work.FTS.Galerkin.slice (G k) s)
    hρ hα hε hε0 hXsm hXmem5 hXbd5 hX0

end Work.FTS.StrongEps.E5G
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.Tower =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5G

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The running minimum -/

/-- The running minimum of a real sequence:
`mseq u 0 = u 0`, `mseq u (k+1) = min (mseq u k) (u (k+1))`. -/
def mseq (u : ℕ → ℝ) : ℕ → ℝ
  | 0 => u 0
  | (k + 1) => min (mseq u k) (u (k + 1))

theorem mseq_succ (u : ℕ → ℝ) (k : ℕ) :
    mseq u (k + 1) = min (mseq u k) (u (k + 1)) := rfl

/-- The running minimum is antitone. -/
theorem mseq_antitone (u : ℕ → ℝ) : Antitone (mseq u) := by
  intro m n hmn
  induction n with
  | zero => rw [Nat.le_zero.mp hmn]
  | succ n ih =>
      rw [mseq_succ]
      rcases Nat.lt_or_ge m (n + 1) with h | h
      · exact le_trans (min_le_left _ _) (ih (Nat.lt_succ_iff.mp h))
      · have hm : m = n + 1 := le_antisymm hmn h
        subst hm
        exact le_rfl

/-- The running minimum is below every earlier term. -/
theorem mseq_le (u : ℕ → ℝ) : ∀ k i : ℕ, i ≤ k → mseq u k ≤ u i := by
  intro k
  induction k with
  | zero =>
      intro i hi
      rw [Nat.le_zero.mp hi]
      exact le_rfl
  | succ k ih =>
      intro i hi
      rw [mseq_succ]
      rcases Nat.lt_or_eq_of_le hi with h | h
      · exact le_trans (min_le_left _ _) (ih i (Nat.lt_succ_iff.mp h))
      · subst h
        exact min_le_right _ _

/-- The running minimum of a positive sequence is positive. -/
theorem mseq_pos {u : ℕ → ℝ} (hu : ∀ k, 0 < u k) : ∀ k, 0 < mseq u k := by
  intro k
  induction k with
  | zero => exact hu 0
  | succ k ih => rw [mseq_succ]; exact lt_min ih (hu (k + 1))

/-! ## The datum sequence of the tower -/

/-- The positive sequence below every threshold: `dataSeq u k = min 1 (mseq u (k+1)) / (k+1)`. -/
def dataSeq (u : ℕ → ℝ) (k : ℕ) : ℝ := min 1 (mseq u (k + 1)) / ((k : ℝ) + 1)


/-- The datum sequence is positive where the input is. -/
theorem dataSeq_pos {u : ℕ → ℝ} (hu : ∀ k, 0 < u k) (k : ℕ) : 0 < dataSeq u k :=
  div_pos (lt_min one_pos (mseq_pos hu (k + 1))) (by positivity)

/-- The running minimum of a non-negative sequence is non-negative. -/
theorem mseq_nonneg {u : ℕ → ℝ} (hu : ∀ k, 0 ≤ u k) : ∀ k, 0 ≤ mseq u k := by
  intro k
  induction k with
  | zero => exact hu 0
  | succ k ih => rw [mseq_succ]; exact le_min ih (hu (k + 1))

/-- The datum sequence is non-negative over a non-negative input. -/
theorem dataSeq_nonneg {u : ℕ → ℝ} (hu : ∀ k, 0 ≤ u k) (k : ℕ) : 0 ≤ dataSeq u k :=
  div_nonneg (le_min zero_le_one (mseq_nonneg hu (k + 1))) (by positivity)

/-- The datum sequence is bounded by `1 / (k+1)`. -/
theorem dataSeq_bound (u : ℕ → ℝ) (k : ℕ) : dataSeq u k ≤ 1 / ((k : ℝ) + 1) := by
  have hnum : min 1 (mseq u (k + 1)) ≤ 1 := min_le_left _ _
  show min 1 (mseq u (k + 1)) / ((k : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1)
  exact div_le_div_of_nonneg_right hnum (by positivity)

/-- The datum sequence is bounded by `1`. -/
theorem dataSeq_le_one (u : ℕ → ℝ) {k : ℕ} : dataSeq u k ≤ 1 := by
  have hb : dataSeq u k ≤ 1 / ((k : ℝ) + 1) := dataSeq_bound u k
  have hd : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h2 : (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 := by
    rw [div_le_iff₀ hd]
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]
  exact le_trans hb h2

/-- The datum sequence is below every threshold: `dataSeq u k ≤ u n` for `n ≤ k`. -/
theorem dataSeq_le {u : ℕ → ℝ} (hu : ∀ k, 0 ≤ u k) {n k : ℕ} (hnk : n ≤ k) :
    dataSeq u k ≤ u n := by
  have hnum : min 1 (mseq u (k + 1)) ≤ mseq u (k + 1) := min_le_right _ _
  have hd : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hnonneg : 0 ≤ mseq u (k + 1) := mseq_nonneg hu (k + 1)
  have h1 : dataSeq u k ≤ mseq u (k + 1) := by
    show min 1 (mseq u (k + 1)) / ((k : ℝ) + 1) ≤ mseq u (k + 1)
    rw [div_le_iff₀ hd]
    have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]
    nlinarith [hnum, hk, hnonneg]
  refine le_trans h1 (le_trans (mseq_antitone u (Nat.le_succ_of_le hnk)) ?_)
  exact mseq_le u n n le_rfl

/-- The datum sequence tends to zero. -/
theorem dataSeq_tendsto {u : ℕ → ℝ} (hu : ∀ k, 0 ≤ u k) : Tendsto (dataSeq u) atTop (nhds 0) := by
  refine squeeze_zero (fun k => dataSeq_nonneg hu k) (fun k => dataSeq_bound u k) ?_
  simpa [div_eq_mul_inv] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)

/-! ## The tower -/


end Work.FTS.StrongEps.E5G
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.TowerFacts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5G

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **The zero mode of the tower's pre-mollified right-hand side vanishes.** -/
theorem epsWP_zero_tower {α C₀ Ce Cs T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {ε : ℕ → ℝ} {G : ℕ → Fam}
    (hα : α ∈ Set.Ioc (0 : ℝ) 1) (hρ : IsSmoothKernel ρ)
    (hε : ∀ n : ℕ, ε n ∈ Set.Ioc (0 : ℝ) 1)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) (hml : MuLamOK α C₀ Φs E)
    (hC : ∀ n : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.ClassC.ClassC α (slice (JfamP ρ (ε n) (G n)) s))
    (hb4 : ∀ n : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.Nonlin.Xn α (slice (JfamP ρ (ε n) (G n)) s) ≤ C₀ * α ^ 2) :
    ∀ n : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.Construction.L12 (epsWP α ρ (ε n) Φs E (G n) s) 0 = 0 :=
  fun n s hs => EpsZeroMode hα hρ (hε n).1 (hC n s hs) (hb4 n s hs) hEll hstar hml

end Work.FTS.StrongEps.E5G
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.exists_tendsto_of_equiholder_of_weak =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5G

open scoped Real Topology
open MeasureTheory Set Filter Metric
open Work.FTS.Galerkin (Fn)

set_option linter.unusedVariables false

/-- **Equi-Hölder implies continuity on compacta.**  A function which is `C`-Hölder of
exponent `1/2` on a set is continuous there. -/
private lemma continuousOn_of_equiholder_aux {g : ℝ × ℝ → ℝ} {K : Set (ℝ × ℝ)} {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ p ∈ K, ∀ q ∈ K, dist (g p) (g q) ≤ C * dist p q ^ (1 / 2 : ℝ)) :
    ContinuousOn g K := by
  rw [Metric.continuousOn_iff]
  intro b hb ε hε
  have hC1 : (0 : ℝ) < C + 1 := by linarith
  refine ⟨(ε / (C + 1)) ^ 2, by positivity, fun a ha hab => ?_⟩
  have hstep : dist a b ^ (1 / 2 : ℝ) ≤ ε / (C + 1) := by
    have hsq : ((ε / (C + 1)) ^ 2) ^ (1 / 2 : ℝ) = ε / (C + 1) := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]
    have h1 : dist a b ^ (1 / 2 : ℝ) ≤ ((ε / (C + 1)) ^ 2) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow dist_nonneg hab.le (by norm_num)
    rwa [hsq] at h1
  have h2 : dist (g a) (g b) ≤ C * (ε / (C + 1)) :=
    le_trans (h a ha b hb) (mul_le_mul_of_nonneg_left hstep hC)
  have h3 : C * (ε / (C + 1)) < ε := by
    have h4 : C * (ε / (C + 1)) = C * ε / (C + 1) := by ring
    rw [h4, div_lt_iff₀ hC1]
    nlinarith
  linarith

/-- **The pointwise limit exists.**  Under the weak test-integral convergence hypothesis, the
equi-Hölder family `mixed j i (V n)` converges at every point of the quadrant `Q0`. -/
private lemma exists_tendsto_pointwise {V : ℕ → Fn} (j i : ℕ)
    (hequi : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ p ∈ K, ∀ q ∈ K,
        |Work.Spaces.mixed j i (V n) p.1 p.2 - Work.Spaces.mixed j i (V n) q.1 q.2|
          ≤ C * dist p q ^ (1 / 2 : ℝ))
    (hweak : ∀ φ : ℝ → ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ)) →
      HasCompactSupport (Function.uncurry φ) →
      tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ L : ℝ, Filter.Tendsto (fun n => ∫ p in Work.FTS.EllipticEst.Q0,
        Work.Spaces.mixed j i (V n) p.1 p.2 * φ p.1 p.2) Filter.atTop (nhds L))
    (q : ℝ × ℝ) (hq : q ∈ Work.FTS.EllipticEst.Q0) :
    ∃ L : ℝ, Filter.Tendsto (fun n => Work.Spaces.mixed j i (V n) q.1 q.2)
      Filter.atTop (nhds L) := by
  classical
  -- a ball around `q` inside the open quadrant
  obtain ⟨ρ, hρpos, hρsub⟩ :=
    Metric.mem_nhds_iff.mp (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hq)
  -- the compact set carrying the Hölder bound
  set K : Set (ℝ × ℝ) := Metric.closedBall q (ρ / 2) with hKdef
  have hKcomp : IsCompact K := isCompact_closedBall q (ρ / 2)
  have hKQ : K ⊆ Work.FTS.EllipticEst.Q0 := fun p hp =>
    hρsub (Metric.closedBall_subset_ball (by linarith) hp)
  obtain ⟨C, hCnn, hCb⟩ := hequi K hKcomp hKQ
  have hqK : q ∈ K := Metric.mem_closedBall_self (by linarith)
  refine cauchySeq_tendsto_of_complete ?_
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hC1 : (0 : ℝ) < C + 1 := by linarith
  set δ : ℝ := min (ρ / 2) ((ε / (4 * (C + 1))) ^ 2) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact lt_min (by linarith) (by positivity)
  have hδρ : δ ≤ ρ / 2 := by rw [hδdef]; exact min_le_left _ _
  have hδε : δ ≤ (ε / (4 * (C + 1))) ^ 2 := by rw [hδdef]; exact min_le_right _ _
  -- the averaging bump at scale `δ`
  obtain ⟨ψ, hψsm, hψcs, hψnn, hψint, hψdist, hψzero, hψKint, hψball⟩ :=
    exists_normed_bump_test q hρpos hδpos hδρ
  have hψKint' : (∫ p in K, ψ p) = 1 := by rw [hKdef]; exact hψKint
  -- the bump lives in `Q0` *including its topological support*
  have htsupp : tsupport ψ ⊆ Work.FTS.EllipticEst.Q0 := by
    have hsupp : Function.support ψ ⊆ Metric.ball q δ := by
      intro p hp
      rw [Metric.mem_ball]
      by_contra hcon
      exact hp (hψzero p (le_of_not_gt hcon))
    calc tsupport ψ ⊆ closure (Metric.ball q δ) := closure_mono hsupp
      _ ⊆ Metric.closedBall q δ := Metric.closure_ball_subset_closedBall
      _ ⊆ Metric.closedBall q (ρ / 2) := Metric.closedBall_subset_closedBall (by linarith)
      _ ⊆ Metric.ball q ρ := Metric.closedBall_subset_ball (by linarith)
      _ ⊆ Work.FTS.EllipticEst.Q0 := hρsub
  -- the same bump, curried, as a test function
  set φ : ℝ → ℝ → ℝ := fun z θ => ψ (z, θ) with hφdef
  have huncurry : Function.uncurry φ = ψ := rfl
  obtain ⟨L, hL⟩ := hweak φ (fun n => huncurry ▸ hψsm n) (huncurry ▸ hψcs)
    (huncurry ▸ htsupp)
  set A : ℕ → ℝ := fun n => ∫ p in Work.FTS.EllipticEst.Q0,
    Work.Spaces.mixed j i (V n) p.1 p.2 * ψ p with hAdef
  have hL' : Filter.Tendsto A Filter.atTop (nhds L) := by
    rw [show A = (fun n => ∫ p in Work.FTS.EllipticEst.Q0,
        Work.Spaces.mixed j i (V n) p.1 p.2 * φ p.1 p.2) from rfl]
    exact hL
  -- the averaging estimate
  have hbound : ∀ k : ℕ, dist (Work.Spaces.mixed j i (V k) q.1 q.2) (A k)
      ≤ C * δ ^ (1 / 2 : ℝ) := by
    intro k
    have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i (V k) p.1 p.2) K :=
      continuousOn_of_equiholder_aux hCnn (fun p hp b hb => by
        rw [Real.dist_eq]
        exact hCb k p hp b hb)
    have hψcont : ContinuousOn ψ K := ((hψsm 1).continuous).continuousOn
    have hψK : ∀ p, ψ p ≠ 0 → p ∈ K := fun p hp =>
      Metric.mem_closedBall.mpr (le_of_lt (lt_of_lt_of_le (hψdist p hp) hδρ))
    have hbd : ∀ p ∈ K, dist (Work.Spaces.mixed j i (V k) p.1 p.2)
        (Work.Spaces.mixed j i (V k) q.1 q.2) ≤ C * dist p q ^ (1 / 2 : ℝ) := fun p hp => by
      rw [Real.dist_eq]
      exact hCb k p hp q hqK
    have hδb : ∀ p, ψ p ≠ 0 → dist p q ≤ δ := fun p hp => (hψdist p hp).le
    have hest := dist_setIntegral_mul_le (K := K)
      (f := fun p : ℝ × ℝ => Work.Spaces.mixed j i (V k) p.1 p.2) (ψ := ψ) (q := q)
      (C := C) (δ := δ) hKcomp hCnn hδpos.le hcont hψcont hψnn hψK hψKint' hbd hδb
    have hAeq : A k = ∫ p in K, Work.Spaces.mixed j i (V k) p.1 p.2 * ψ p := by
      rw [hAdef]
      exact MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
        Work.FTS.EllipticEst.isOpen_Q0.measurableSet hKQ (fun p hp => by
          have hpk : p ∉ K := hp.2
          have hlt : ρ / 2 < dist p q :=
            not_le.mp (fun hle => hpk (Metric.mem_closedBall.mpr hle))
          have hψp : ψ p = 0 := hψzero p (le_trans hδρ hlt.le)
          simp [hψp])
    rw [hAeq, dist_comm]
    exact hest
  have hAcauchy : CauchySeq A := hL'.cauchySeq
  rw [Metric.cauchySeq_iff] at hAcauchy
  obtain ⟨N, hN⟩ := hAcauchy (ε / 2) (by linarith)
  refine ⟨N, fun m hm n hn => ?_⟩
  have hsqle : δ ^ (1 / 2 : ℝ) ≤ ε / (4 * (C + 1)) := by
    have hsq : ((ε / (4 * (C + 1))) ^ 2) ^ (1 / 2 : ℝ) = ε / (4 * (C + 1)) := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]
    have h1 : δ ^ (1 / 2 : ℝ) ≤ ((ε / (4 * (C + 1))) ^ 2) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow hδpos.le hδε (by norm_num)
    rwa [hsq] at h1
  have hcsq : C * δ ^ (1 / 2 : ℝ) ≤ ε / 4 := by
    have h1 : C * (ε / (4 * (C + 1))) ≤ ε / 4 := by
      have h2 : C * (ε / (4 * (C + 1))) = (C * ε) / (4 * (C + 1)) := by ring
      rw [h2, div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (C + 1))]
      nlinarith
    exact le_trans (mul_le_mul_of_nonneg_left hsqle hCnn) h1
  have hbm : dist (Work.Spaces.mixed j i (V m) q.1 q.2) (A m) ≤ ε / 4 :=
    le_trans (hbound m) hcsq
  have hbn : dist (A n) (Work.Spaces.mixed j i (V n) q.1 q.2) ≤ ε / 4 := by
    rw [dist_comm]
    exact le_trans (hbound n) hcsq
  have hA : dist (A m) (A n) < ε / 2 := hN m hm n hn
  have hmid : dist (Work.Spaces.mixed j i (V m) q.1 q.2) (A m) + dist (A m) (A n)
      + dist (A n) (Work.Spaces.mixed j i (V n) q.1 q.2) < ε := by
    have h2 := add_lt_add_of_le_of_lt hbm hA
    have h3 := add_lt_add_of_lt_of_le h2 hbn
    have h4 : ε / 4 + ε / 2 + ε / 4 = ε := by ring
    rwa [h4] at h3
  exact lt_of_le_of_lt (dist_triangle4 _ _ _ _) hmid

theorem exists_tendsto_of_equiholder_of_weak {V : ℕ → Work.FTS.Galerkin.Fn} (j i : ℕ)
    (hsm : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (V n))
    (hequi : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ p ∈ K, ∀ q ∈ K,
        |Work.Spaces.mixed j i (V n) p.1 p.2 - Work.Spaces.mixed j i (V n) q.1 q.2|
          ≤ C * dist p q ^ (1 / 2 : ℝ))
    (hweak : ∀ φ : ℝ → ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ)) →
      HasCompactSupport (Function.uncurry φ) →
      tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ L : ℝ, Filter.Tendsto (fun n => ∫ p in Work.FTS.EllipticEst.Q0,
        Work.Spaces.mixed j i (V n) p.1 p.2 * φ p.1 p.2) Filter.atTop (nhds L)) :
    ∃ Φ : ℝ → ℝ → ℝ, ContinuousOn (Function.uncurry Φ) Work.FTS.EllipticEst.Q0 ∧
      ∀ q ∈ Work.FTS.EllipticEst.Q0,
        Filter.Tendsto (fun n => Work.Spaces.mixed j i (V n) q.1 q.2) Filter.atTop
          (nhds (Φ q.1 q.2)) := by
  classical
  have hpt : ∀ q : ℝ × ℝ, q ∈ Work.FTS.EllipticEst.Q0 →
      ∃ L : ℝ, Filter.Tendsto (fun n => Work.Spaces.mixed j i (V n) q.1 q.2)
        Filter.atTop (nhds L) := fun q hq => exists_tendsto_pointwise j i hequi hweak q hq
  choose Φ₀ hΦ₀ using hpt
  refine ⟨fun z θ => if h : (z, θ) ∈ Work.FTS.EllipticEst.Q0 then Φ₀ (z, θ) h else 0,
    ?_, ?_⟩
  · refine continuousOn_of_pointwise_of_equiholder
      (f := fun n p => Work.Spaces.mixed j i (V n) p.1 p.2)
      (Φ := fun p : ℝ × ℝ =>
        if h : p ∈ Work.FTS.EllipticEst.Q0 then Φ₀ p h else 0)
      Work.FTS.EllipticEst.isOpen_Q0 ?_ ?_
    · intro q hq
      show Filter.Tendsto (fun n => Work.Spaces.mixed j i (V n) q.1 q.2) Filter.atTop
        (nhds ((if h : q ∈ Work.FTS.EllipticEst.Q0 then Φ₀ q h else 0)))
      rw [dite_eq_left hq]
      exact hΦ₀ q hq
    · intro K hK hKQ
      obtain ⟨C, hCnn, hCb⟩ := hequi K hK hKQ
      exact ⟨C, hCnn, fun n p hp q hq => by
        rw [Real.dist_eq]
        exact hCb n p hp q hq⟩
  · intro q hq
    show Filter.Tendsto (fun n => Work.Spaces.mixed j i (V n) q.1 q.2) Filter.atTop
      (nhds ((if h : q ∈ Work.FTS.EllipticEst.Q0 then Φ₀ q h else 0)))
    rw [dite_eq_left hq]
    exact hΦ₀ q hq

end Work.FTS.StrongEps.E5G
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.pointwise_bound_of_tendsto_of_equiholder =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5G

set_option linter.unusedVariables false

/-- **Pointwise convergence plus a uniform `1/2`-Hölder bound on a compact set gives a uniform
bound on that set.**

Fix a point `q₀` of the compact set `K ⊆ Q0`.  Each slot `D_z^jD_θ^i (V n)` is `1/2`-Hölder with a
constant `C` that is uniform in `n` on `K` (`hequi`), whence for `p ∈ K`

`|D_z^jD_θ^i (V n) p| ≤ |D_z^jD_θ^i (V n) p - D_z^jD_θ^i (V n) q₀| + |D_z^jD_θ^i (V n) q₀|
 ≤ C · dist p q₀ ^ (1/2) + |D_z^jD_θ^i (V n) q₀| ≤ C · r ^ (1/2) + M`,

where `r` bounds `dist p q₀` (`p ∈ K`, `K` bounded) and `M` bounds the convergent sequence
`n ↦ D_z^jD_θ^i (V n) q₀` (`hconv`; a convergent sequence of reals is bounded). -/
theorem pointwise_bound_of_tendsto_of_equiholder {V : ℕ → Work.FTS.Galerkin.Fn}
    {Φ : Work.FTS.Galerkin.Fn} (j i : ℕ)
    (hsm : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (V n))
    (hequi : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ p ∈ K, ∀ q ∈ K,
        |Work.Spaces.mixed j i (V n) p.1 p.2 - Work.Spaces.mixed j i (V n) q.1 q.2|
          ≤ C * dist p q ^ (1 / 2 : ℝ))
    (hconv : ∀ q ∈ Work.FTS.EllipticEst.Q0,
      Filter.Tendsto (fun n => Work.Spaces.mixed j i (V n) q.1 q.2) Filter.atTop
        (nhds (Φ q.1 q.2)))
    (hΦc : ContinuousOn (Function.uncurry Φ) Work.FTS.EllipticEst.Q0) :
    ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ p ∈ K,
        |Work.Spaces.mixed j i (V n) p.1 p.2| ≤ C := by
  intro K hK hKQ0
  by_cases hKne : K.Nonempty
  · obtain ⟨q₀, hq₀⟩ := hKne
    obtain ⟨Ce, hCe, hequiK⟩ := hequi K hK hKQ0
    -- The sequence of values at the fixed point `q₀` is bounded (`hconv` + boundedness of the
    -- range of a convergent sequence).
    obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ n : ℕ,
        |Work.Spaces.mixed j i (V n) q₀.1 q₀.2| ≤ M := by
      have h1 : Bornology.IsBounded
          (Set.range (fun n => Work.Spaces.mixed j i (V n) q₀.1 q₀.2)) :=
        Metric.isBounded_range_of_tendsto _ (hconv q₀ (hKQ0 hq₀))
      obtain ⟨C, hC⟩ := Metric.isBounded_range_iff.1 h1
      refine ⟨C + |Work.Spaces.mixed j i (V 0) q₀.1 q₀.2|, fun n => ?_⟩
      have h2 : dist (Work.Spaces.mixed j i (V n) q₀.1 q₀.2)
          (Work.Spaces.mixed j i (V 0) q₀.1 q₀.2) ≤ C := hC n 0
      rw [Real.dist_eq] at h2
      have h3 : |Work.Spaces.mixed j i (V n) q₀.1 q₀.2|
          ≤ |Work.Spaces.mixed j i (V n) q₀.1 q₀.2 - Work.Spaces.mixed j i (V 0) q₀.1 q₀.2|
            + |Work.Spaces.mixed j i (V 0) q₀.1 q₀.2| := by
        have hsub : Work.Spaces.mixed j i (V n) q₀.1 q₀.2
            - Work.Spaces.mixed j i (V 0) q₀.1 q₀.2
            + Work.Spaces.mixed j i (V 0) q₀.1 q₀.2
            = Work.Spaces.mixed j i (V n) q₀.1 q₀.2 := sub_add_cancel _ _
        calc |Work.Spaces.mixed j i (V n) q₀.1 q₀.2|
            = |Work.Spaces.mixed j i (V n) q₀.1 q₀.2 - Work.Spaces.mixed j i (V 0) q₀.1 q₀.2
                + Work.Spaces.mixed j i (V 0) q₀.1 q₀.2| := by rw [hsub]
          _ ≤ |Work.Spaces.mixed j i (V n) q₀.1 q₀.2 - Work.Spaces.mixed j i (V 0) q₀.1 q₀.2|
                + |Work.Spaces.mixed j i (V 0) q₀.1 q₀.2| := abs_add_le _ _
      linarith
    -- `K` is contained in a closed ball around `q₀`.
    obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall q₀
    refine ⟨max 0 (Ce * r ^ (1 / 2 : ℝ) + M), le_max_left _ _, fun n p hp => ?_⟩
    have h1 : |Work.Spaces.mixed j i (V n) p.1 p.2 - Work.Spaces.mixed j i (V n) q₀.1 q₀.2|
        ≤ Ce * dist p q₀ ^ (1 / 2 : ℝ) := hequiK n p hp q₀ hq₀
    have hpK : dist p q₀ ≤ r := Metric.mem_closedBall.mp (hr hp)
    have h2 : dist p q₀ ^ (1 / 2 : ℝ) ≤ r ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow dist_nonneg hpK (by norm_num)
    have h3 : Ce * dist p q₀ ^ (1 / 2 : ℝ) ≤ Ce * r ^ (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left h2 hCe
    have h4 : |Work.Spaces.mixed j i (V n) p.1 p.2|
        ≤ |Work.Spaces.mixed j i (V n) p.1 p.2 - Work.Spaces.mixed j i (V n) q₀.1 q₀.2|
          + |Work.Spaces.mixed j i (V n) q₀.1 q₀.2| := by
      have hsub : Work.Spaces.mixed j i (V n) p.1 p.2
          - Work.Spaces.mixed j i (V n) q₀.1 q₀.2 + Work.Spaces.mixed j i (V n) q₀.1 q₀.2
          = Work.Spaces.mixed j i (V n) p.1 p.2 := sub_add_cancel _ _
      calc |Work.Spaces.mixed j i (V n) p.1 p.2|
          = |Work.Spaces.mixed j i (V n) p.1 p.2 - Work.Spaces.mixed j i (V n) q₀.1 q₀.2
              + Work.Spaces.mixed j i (V n) q₀.1 q₀.2| := by rw [hsub]
        _ ≤ |Work.Spaces.mixed j i (V n) p.1 p.2 - Work.Spaces.mixed j i (V n) q₀.1 q₀.2|
              + |Work.Spaces.mixed j i (V n) q₀.1 q₀.2| := abs_add_le _ _
    have h5 : |Work.Spaces.mixed j i (V n) q₀.1 q₀.2| ≤ M := hM n
    have h6 : Ce * r ^ (1 / 2 : ℝ) + M ≤ max 0 (Ce * r ^ (1 / 2 : ℝ) + M) := le_max_right _ _
    linarith
  · exact ⟨0, le_refl 0, fun n p hp => absurd ⟨p, hp⟩ hKne⟩

end Work.FTS.StrongEps.E5G
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.slots_eq_of_convergent_jets =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Filter Set

namespace Work.FTS.StrongEps.E5G

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The jets of a limit along convergent jets

Let `V n` be smooth on the open quadrant `Q0 = (0,∞) × (0,π/2)`, converging pointwise to `R`, and
suppose that the weighted jets `D_z^jD_θ^i (V n)` (`j + i ≤ 3`) converge pointwise to `Φ j i`, that
the jets are equi-Hölder-`1/2` on compact subsets of `Q0`, and uniformly bounded there.  The claim
is that the jets of the limit `R` are exactly the limits: `D_z^jD_θ^i R = Φ j i` on `Q0` for
`j + i ≤ 3`.

The proof has two layers.

* **Uniform convergence.**  Equi-Hölder-`1/2` plus pointwise convergence on a compact `K` gives
  *uniform* convergence on `K` (the convergence half of Arzelà–Ascoli), hence locally uniform
  convergence on `Q0` for every jet of order `≤ 3`.
* **Differentiation of the limit.**  Locally uniform convergence of `f n := D_z^jD_θ^i (V n)`
  together with locally uniform convergence of the Fréchet derivatives
  `fderiv ℝ (uncurry (f n))` (the latter is read off from the *next* jets: the `z`-partial of a jet
  is the next `z`-jet divided by `z`, the `θ`-partial the next `θ`-jet divided by `sin 2θ`) lets
  Mathlib's `hasFDerivAt_of_tendstoLocallyUniformlyOn` differentiate the limit.  Inducting over
  `j + i ≤ 3` gives the result.
-/

/-- The `(j,i)`-jet `D_z^j D_θ^i u` of a curried function, as a function on `ℝ × ℝ`. -/
private def slot (j i : ℕ) (u : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => Work.Spaces.mixed j i u p.1 p.2

/-- The pointwise limit of the `(j,i)`-jets, as a function on `ℝ × ℝ`. -/
private def slotLim (Φ : ℕ → ℕ → ℝ → ℝ → ℝ) (j i : ℕ) : ℝ × ℝ → ℝ :=
  fun p => Φ j i p.1 p.2

/-! ## The successor identity for the `θ`-jets -/

/-- `D_θ^{i+1} u = sin 2θ · ∂_θ (D_θ^i u)`. -/
private theorem mixed_succ_th (u : ℝ → ℝ → ℝ) (i : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed 0 (i + 1) u z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.mixed 0 i u) z θ := by
  simp only [Work.Spaces.mixed, Work.Spaces.DthIter_succ, Work.Spaces.Dth,
    Work.Spaces.DzIter_zero]

/-! ## Step 1: locally uniform convergence of the jets -/

/-- **Locally uniform convergence of every jet of order `≤ 3`.** -/
private theorem slot_tlu_of_jets {V : ℕ → ℝ → ℝ → ℝ} {Φ : ℕ → ℕ → ℝ → ℝ → ℝ}
    (hconv : ∀ (j i : ℕ), j + i ≤ 3 → ∀ q ∈ Work.FTS.EllipticEst.Q0,
      Filter.Tendsto (fun n => Work.Spaces.mixed j i (V n) q.1 q.2) Filter.atTop
        (nhds (Φ j i q.1 q.2)))
    (hequi : ∀ (j i : ℕ), j + i ≤ 3 → ∀ K : Set (ℝ × ℝ), IsCompact K →
      K ⊆ Work.FTS.EllipticEst.Q0 → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ p ∈ K, ∀ q ∈ K,
        |Work.Spaces.mixed j i (V n) p.1 p.2 - Work.Spaces.mixed j i (V n) q.1 q.2|
          ≤ C * dist p q ^ (1 / 2 : ℝ)) :
    ∀ (j i : ℕ), j + i ≤ 3 →
      TendstoLocallyUniformlyOn (fun n : ℕ => slot j i (V n)) (slotLim Φ j i) Filter.atTop
        Work.FTS.EllipticEst.Q0 := by
  intro j i hji
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact Work.FTS.EllipticEst.isOpen_Q0]
  intro K hKQ hK
  obtain ⟨C, hC, hCd⟩ := hequi j i hji K hK hKQ
  exact tendstoUniformlyOn_of_pointwise_of_holder hK (fun p hp => hconv j i hji p (hKQ hp))
    (equicont_of_holder hC hCd)

/-! ## Step 2: the jets of the limit

The locally uniform convergence of the jets (`slot_tlu_of_jets`) is upgraded to the jets of the
limit by induction on `j + i`: the `z`-partial of a jet is the next `z`-jet divided by `z`, the
`θ`-partial the next `θ`-jet divided by `sin 2θ` (`fderiv_uncurry_mixed_eq_clmPair`), so the
Fréchet derivatives converge locally uniformly and
`hasFDerivAt_of_slot_tlu` differentiates the limit. -/

theorem slots_eq_of_convergent_jets {V : ℕ → Work.FTS.Galerkin.Fn} {R : Work.FTS.Galerkin.Fn}
    {Φ : ℕ → ℕ → Work.FTS.Galerkin.Fn}
    (hsm : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (V n))
    (hR : ∀ q ∈ Work.FTS.EllipticEst.Q0,
      Filter.Tendsto (fun n => V n q.1 q.2) Filter.atTop (nhds (R q.1 q.2)))
    (hconv : ∀ (j i : ℕ), j + i ≤ 3 → ∀ q ∈ Work.FTS.EllipticEst.Q0,
      Filter.Tendsto (fun n => Work.Spaces.mixed j i (V n) q.1 q.2) Filter.atTop
        (nhds (Φ j i q.1 q.2)))
    (hequi : ∀ (j i : ℕ), j + i ≤ 3 → ∀ K : Set (ℝ × ℝ), IsCompact K →
      K ⊆ Work.FTS.EllipticEst.Q0 → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ p ∈ K, ∀ q ∈ K,
        |Work.Spaces.mixed j i (V n) p.1 p.2 - Work.Spaces.mixed j i (V n) q.1 q.2|
          ≤ C * dist p q ^ (1 / 2 : ℝ))
    (hbnd : ∀ (j i : ℕ), j + i ≤ 3 → ∀ K : Set (ℝ × ℝ), IsCompact K →
      K ⊆ Work.FTS.EllipticEst.Q0 → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ p ∈ K,
        |Work.Spaces.mixed j i (V n) p.1 p.2| ≤ C) :
    ∀ (j i : ℕ), j + i ≤ 3 → ∀ q ∈ Work.FTS.EllipticEst.Q0,
      Work.Spaces.mixed j i R q.1 q.2 = Φ j i q.1 q.2 := by
  classical
  have hslot : ∀ (j i : ℕ), j + i ≤ 3 →
      TendstoLocallyUniformlyOn (fun n : ℕ => slot j i (V n)) (slotLim Φ j i) Filter.atTop
        Work.FTS.EllipticEst.Q0 :=
    slot_tlu_of_jets (V := fun n => V n) (Φ := fun j i => Φ j i) hconv hequi
  have hcontΦ : ∀ (j i : ℕ), j + i ≤ 3 →
      ContinuousOn (slotLim Φ j i) Work.FTS.EllipticEst.Q0 := fun j i hji =>
    (hslot j i hji).continuousOn
      (Eventually.of_forall fun n => ((hsm n).mixed j i).forall 0 |>.continuousOn).frequently
  have hz0 : ∀ p ∈ Work.FTS.EllipticEst.Q0, p.1 ≠ 0 :=
    fun p hp => ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1
  have hs0 : ∀ p ∈ Work.FTS.EllipticEst.Q0, Real.sin (2 * p.2) ≠ 0 := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
  have hsin_cont : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      Work.FTS.EllipticEst.Q0 :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
  have hdiffV : ∀ (n j i : ℕ) (p : ℝ × ℝ), p ∈ Work.FTS.EllipticEst.Q0 →
      DifferentiableAt ℝ (Function.uncurry (Work.Spaces.mixed j i (V n))) p :=
    fun n j i p hp => (((hsm n).mixed j i).forall 1).differentiableOn (by norm_num)
      |>.differentiableAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp)
  -- the `z`-divided and `sin 2θ`-divided jets converge locally uniformly
  have hdivp1 : ∀ (j i : ℕ), (j + 1) + i ≤ 3 →
      TendstoLocallyUniformlyOn
        (fun n : ℕ => fun p : ℝ × ℝ => Work.Spaces.mixed (j + 1) i (V n) p.1 p.2 / p.1)
        (fun p : ℝ × ℝ => Φ (j + 1) i p.1 p.2 / p.1) Filter.atTop Work.FTS.EllipticEst.Q0 :=
    fun j i hji => (hslot (j + 1) i hji).div₀
      (Work.FTS.StrongEps.E5Aux.tlu_const (fun p : ℝ × ℝ => p.1) Work.FTS.EllipticEst.Q0)
      (hcontΦ (j + 1) i hji) continuous_fst.continuousOn (fun p hp => hz0 p hp)
  have hdivsn : ∀ (j i : ℕ), j + (i + 1) ≤ 3 →
      TendstoLocallyUniformlyOn
        (fun n : ℕ => fun p : ℝ × ℝ =>
          Work.Spaces.mixed j (i + 1) (V n) p.1 p.2 / Real.sin (2 * p.2))
        (fun p : ℝ × ℝ => Φ j (i + 1) p.1 p.2 / Real.sin (2 * p.2)) Filter.atTop
        Work.FTS.EllipticEst.Q0 :=
    fun j i hji => (hslot j (i + 1) hji).div₀
      (Work.FTS.StrongEps.E5Aux.tlu_const (fun p : ℝ × ℝ => Real.sin (2 * p.2))
        Work.FTS.EllipticEst.Q0)
      (hcontΦ j (i + 1) hji) hsin_cont (fun p hp => hs0 p hp)
  suffices key : ∀ m : ℕ, ∀ (j i : ℕ), j + i = m → j + i ≤ 3 →
      ∀ q ∈ Work.FTS.EllipticEst.Q0, Work.Spaces.mixed j i R q.1 q.2 = Φ j i q.1 q.2 by
    intro j i hji
    exact key (j + i) j i rfl hji
  intro m
  refine Nat.strong_induction_on m ?_
  intro k ih j i hm hji q hq
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    rcases Nat.eq_zero_or_pos i with hi | hi
    · -- the level-zero case: `V n → R` and `V n → Φ 0 0` pointwise
      subst hi
      have hcv : Filter.Tendsto (fun n : ℕ => V n q.1 q.2) Filter.atTop
          (nhds (Φ 0 0 q.1 q.2)) := by
        simpa [Work.Spaces.mixed] using hconv 0 0 (by norm_num) q hq
      have huniq := tendsto_nhds_unique (hR q hq) hcv
      simpa [Work.Spaces.mixed] using huniq
    · -- `j = 0`, `i ≥ 1`: differentiate the lower jet in `θ`
      obtain ⟨i', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
      have hlow : ∀ r ∈ Work.FTS.EllipticEst.Q0,
          Work.Spaces.mixed 0 i' R r.1 r.2 = Φ 0 i' r.1 r.2 :=
        ih (0 + i') (by omega) 0 i' rfl (by omega)
      have hJet : TendstoLocallyUniformlyOn
          (fun n : ℕ => fderiv ℝ (Function.uncurry (Work.Spaces.mixed 0 i' (V n))))
          (fun p : ℝ × ℝ => Work.FTS.StrongEps.E5Aux.clmPair
            (Φ 1 i' p.1 p.2 / p.1, Φ 0 (i' + 1) p.1 p.2 / Real.sin (2 * p.2)))
          Filter.atTop Work.FTS.EllipticEst.Q0 :=
        (Work.FTS.StrongEps.E5Aux.tendstoLocallyUniformlyOn_clmPair
          (hdivp1 0 i' (by omega)) (hdivsn 0 i' (by omega))).congr
          (fun n => fun p hp => (fderiv_uncurry_mixed_eq_clmPair (hsm n) 0 i' hp).symm)
      have hderiv : HasFDerivAt (Function.uncurry (Work.Spaces.mixed 0 i' R))
          (Work.FTS.StrongEps.E5Aux.clmPair
            (Φ 1 i' q.1 q.2 / q.1, Φ 0 (i' + 1) q.1 q.2 / Real.sin (2 * q.2))) q :=
        hasFDerivAt_of_slot_tlu (W := fun n => Work.Spaces.mixed 0 i' (V n))
          (F := Φ 0 i') (R := Work.Spaces.mixed 0 i' R)
          hq (fun n p hp => hdiffV n 0 i' p hp) (hslot 0 i' (by omega)) hJet
          (fun p hp => hlow p hp)
      have hpth : Work.Spaces.pth (Work.Spaces.mixed 0 i' R) q.1 q.2
          = Φ 0 (i' + 1) q.1 q.2 / Real.sin (2 * q.2) := by
        rw [Work.Spaces.pth_eq_fderiv hderiv.differentiableAt, hderiv.fderiv]
        simp
      rw [show Work.Spaces.mixed 0 (i' + 1) R q.1 q.2
            = Real.sin (2 * q.2) * Work.Spaces.pth (Work.Spaces.mixed 0 i' R) q.1 q.2 from
          mixed_succ_th R i' q.1 q.2, hpth]
      exact mul_div_cancel₀ _ (hs0 q hq)
  · -- `j ≥ 1`: differentiate the lower jet in `z`
    obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    have hlow : ∀ r ∈ Work.FTS.EllipticEst.Q0,
        Work.Spaces.mixed j' i R r.1 r.2 = Φ j' i r.1 r.2 :=
      ih (j' + i) (by omega) j' i rfl (by omega)
    have hJet : TendstoLocallyUniformlyOn
        (fun n : ℕ => fderiv ℝ (Function.uncurry (Work.Spaces.mixed j' i (V n))))
        (fun p : ℝ × ℝ => Work.FTS.StrongEps.E5Aux.clmPair
          (Φ (j' + 1) i p.1 p.2 / p.1, Φ j' (i + 1) p.1 p.2 / Real.sin (2 * p.2)))
        Filter.atTop Work.FTS.EllipticEst.Q0 :=
      (Work.FTS.StrongEps.E5Aux.tendstoLocallyUniformlyOn_clmPair
        (hdivp1 j' i (by omega)) (hdivsn j' i (by omega))).congr
        (fun n => fun p hp => (fderiv_uncurry_mixed_eq_clmPair (hsm n) j' i hp).symm)
    have hderiv : HasFDerivAt (Function.uncurry (Work.Spaces.mixed j' i R))
        (Work.FTS.StrongEps.E5Aux.clmPair
          (Φ (j' + 1) i q.1 q.2 / q.1, Φ j' (i + 1) q.1 q.2 / Real.sin (2 * q.2))) q :=
      hasFDerivAt_of_slot_tlu (W := fun n => Work.Spaces.mixed j' i (V n))
        (F := Φ j' i) (R := Work.Spaces.mixed j' i R)
        hq (fun n p hp => hdiffV n j' i p hp) (hslot j' i (by omega)) hJet
        (fun p hp => hlow p hp)
    have hpz : Work.Spaces.pz (Work.Spaces.mixed j' i R) q.1 q.2
        = Φ (j' + 1) i q.1 q.2 / q.1 := by
      rw [Work.Spaces.pz_eq_fderiv hderiv.differentiableAt, hderiv.fderiv]
      simp
    rw [show Work.Spaces.mixed (j' + 1) i R q.1 q.2
          = q.1 * Work.Spaces.pz (Work.Spaces.mixed j' i R) q.1 q.2 from
        mixed_succ_left_eq R j' i q.1 q.2, hpz]
    exact mul_div_cancel₀ _ (hz0 q hq)

end Work.FTS.StrongEps.E5G
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.weak_slots_tendsto_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5G

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The weak (test-function) convergence of a slot family

The target `weak_slots_tendsto_open` produces, for a sequence `V n` which is `C^∞` on the open
quadrant, converges pointwise on `Q0` to `R` and is locally uniformly bounded, a limit for the
pairings `∫_{Q0} (mixed j i (V n)) φ` against a test function `φ ∈ C_c^∞(Q0)`.

The slot derivatives of `V n` need not converge (no equi-continuity is assumed), so the argument
moves the derivatives onto the test function: by the formal adjointness
`integral_mixed_mul_adjMixed_open` the pairing equals `∫_{Q0} (V n) · adjMixed (j,i) φ`, and
`adjMixed (j,i) φ` is a *fixed* test function, so the dominated convergence theorem applies on its
(compact) support.

The measure-theoretic step is isolated first, in the reusable form
`tendsto_setIntegral_mul_of_pointwise_of_bound`. -/

/-- **Pairing a pointwise convergent, locally bounded family against a test function.**
If `W n` is continuous on the open quadrant `Q0` and converges pointwise to `L` there, and if the
family is bounded on every compact subset of `Q0`, then for every `ψ` which is continuous on `Q0`
with closed support contained in `Q0` the pairings `∫_{Q0} (W n) ψ` converge.

The proof is the dominated convergence theorem on the compact set `tsupport ψ`: off that set `ψ`
vanishes, so all the integrands vanish there; on it the family is bounded by a constant and
converges pointwise. -/
theorem tendsto_setIntegral_mul_of_pointwise_of_bound
    {W : ℕ → ℝ → ℝ → ℝ} {L ψ : ℝ → ℝ → ℝ}
    (hW : ∀ n : ℕ, ContinuousOn (fun p : ℝ × ℝ => W n p.1 p.2) Work.FTS.EllipticEst.Q0)
    (hψc : ContinuousOn (fun p : ℝ × ℝ => ψ p.1 p.2) Work.FTS.EllipticEst.Q0)
    (hKc : IsCompact (tsupport (Function.uncurry ψ)))
    (hψsub : tsupport (Function.uncurry ψ) ⊆ Work.FTS.EllipticEst.Q0)
    (hconv : ∀ q ∈ Work.FTS.EllipticEst.Q0,
      Filter.Tendsto (fun n => W n q.1 q.2) Filter.atTop (nhds (L q.1 q.2)))
    (hbnd : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, ∀ n : ℕ, ∀ q ∈ K, |W n q.1 q.2| ≤ C) :
    Filter.Tendsto (fun n => ∫ p in Work.FTS.EllipticEst.Q0, W n p.1 p.2 * ψ p.1 p.2)
      Filter.atTop
      (nhds (∫ p in Work.FTS.EllipticEst.Q0, L p.1 p.2 * ψ p.1 p.2)) := by
  classical
  set K : Set (ℝ × ℝ) := tsupport (Function.uncurry ψ) with hKdef
  have hKmeas : MeasurableSet K := hKc.measurableSet
  have hQ0meas : MeasurableSet Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.isOpen_Q0.measurableSet
  obtain ⟨C, hCb⟩ := hbnd K hKc hψsub
  set C' : ℝ := max C 0 with hC'def
  -- `ψ` vanishes off its closed support
  have hvan : ∀ p : ℝ × ℝ, p ∉ K → ψ p.1 p.2 = 0 := by
    intro p hp
    by_contra h
    exact hp (subset_tsupport (Function.uncurry ψ)
      (by show Function.uncurry ψ p ≠ 0; exact h))
  -- the dominated convergence theorem, on the measure `volume.restrict K`
  have hmeas : ∀ n : ℕ,
      AEStronglyMeasurable (fun p : ℝ × ℝ => W n p.1 p.2 * ψ p.1 p.2)
        ((volume : Measure (ℝ × ℝ)).restrict K) := by
    intro n
    exact (((hW n).mul hψc).mono hψsub).aestronglyMeasurable_of_isCompact hKc hKmeas
  have hbndint : Integrable (fun p : ℝ × ℝ => C' * ‖ψ p.1 p.2‖)
      ((volume : Measure (ℝ × ℝ)).restrict K) := by
    have hcont : ContinuousOn (fun p : ℝ × ℝ => ‖ψ p.1 p.2‖) K := (hψc.mono hψsub).norm
    exact (ContinuousOn.integrableOn_compact hKc hcont).integrable.const_mul C'
  have hbnd' : ∀ n : ℕ, ∀ᵐ p ∂((volume : Measure (ℝ × ℝ)).restrict K),
      ‖W n p.1 p.2 * ψ p.1 p.2‖ ≤ C' * ‖ψ p.1 p.2‖ := by
    intro n
    filter_upwards [ae_restrict_mem hKmeas] with p hp
    have hb : |W n p.1 p.2| ≤ C' := le_trans (hCb n p hp) (le_max_left C 0)
    calc ‖W n p.1 p.2 * ψ p.1 p.2‖ = |W n p.1 p.2| * |ψ p.1 p.2| := by
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ C' * |ψ p.1 p.2| := mul_le_mul_of_nonneg_right hb (abs_nonneg _)
      _ = C' * ‖ψ p.1 p.2‖ := by rw [Real.norm_eq_abs]
  have hlim' : ∀ᵐ p ∂((volume : Measure (ℝ × ℝ)).restrict K),
      Filter.Tendsto (fun n => W n p.1 p.2 * ψ p.1 p.2) Filter.atTop
        (nhds (L p.1 p.2 * ψ p.1 p.2)) := by
    filter_upwards [ae_restrict_mem hKmeas] with p hp
    exact (hconv p (hψsub hp)).mul_const (ψ p.1 p.2)
  have hDCT := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := (volume : Measure (ℝ × ℝ)).restrict K)
    (F := fun n (p : ℝ × ℝ) => W n p.1 p.2 * ψ p.1 p.2)
    (f := fun p : ℝ × ℝ => L p.1 p.2 * ψ p.1 p.2)
    (fun p : ℝ × ℝ => C' * ‖ψ p.1 p.2‖) hmeas hbndint hbnd' hlim'
  -- transfer the integrals from the compact support `K` back to the quadrant `Q0`
  have hQK : ∀ (Φ : ℝ × ℝ → ℝ), (∀ p, p ∉ K → Φ p = 0) →
      (∫ p in Work.FTS.EllipticEst.Q0, Φ p) = ∫ p in K, Φ p := by
    intro Φ hΦ
    exact setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hQ0meas hψsub
      (fun p hp => hΦ p hp.2)
  have h1 : (fun n => ∫ p in Work.FTS.EllipticEst.Q0, W n p.1 p.2 * ψ p.1 p.2)
      = fun n => ∫ p in K, W n p.1 p.2 * ψ p.1 p.2 :=
    funext (fun n => hQK _ (fun p hp => by rw [hvan p hp, mul_zero]))
  have h2 : (∫ p in Work.FTS.EllipticEst.Q0, L p.1 p.2 * ψ p.1 p.2)
      = ∫ p in K, L p.1 p.2 * ψ p.1 p.2 :=
    hQK _ (fun p hp => by rw [hvan p hp, mul_zero])
  rw [h1, h2]
  exact hDCT

theorem weak_slots_tendsto_open {V : ℕ → Work.FTS.Galerkin.Fn} {R : Work.FTS.Galerkin.Fn} (j i : ℕ)
    (hsm : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (V n))
    (hconv : ∀ q ∈ Work.FTS.EllipticEst.Q0,
      Filter.Tendsto (fun n => V n q.1 q.2) Filter.atTop (nhds (R q.1 q.2)))
    (hR : ContinuousOn (Function.uncurry R) Work.FTS.EllipticEst.Q0)
    (hbnd : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, ∀ n : ℕ, ∀ q ∈ K, |V n q.1 q.2| ≤ C) :
    ∀ φ : ℝ → ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ)) →
      HasCompactSupport (Function.uncurry φ) →
      tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ L : ℝ, Filter.Tendsto (fun n => ∫ q in Work.FTS.EllipticEst.Q0,
        Work.Spaces.mixed j i (V n) q.1 q.2 * φ q.1 q.2) Filter.atTop (nhds L) := by
  intro φ hφ hcs hts
  -- the adjoint `ψ = (D_z^j D_θ^i)^* φ` of the slot, a fixed test function
  set ψ : ℝ → ℝ → ℝ := Work.FTS.Apriori.Limit.adjMixed (j, i) φ with hψdef
  have hTestφ : Work.FTS.Apriori.Limit.TestQ φ := by
    refine ⟨?_, hcs, hts⟩
    exact contDiffOn_iff_forall_nat_le.mpr (fun n _ => (hφ n).contDiffOn)
  have hTestψ : Work.FTS.Apriori.Limit.TestQ ψ := by
    rw [hψdef]
    exact (Work.FTS.Apriori.Limit.TestQ_mul_adjMixed hTestφ).2 j i
  -- the adjointness of the slot, applied to each member of the family
  have hIBP : (fun n => ∫ q in Work.FTS.EllipticEst.Q0,
        Work.Spaces.mixed j i (V n) q.1 q.2 * φ q.1 q.2)
      = fun n => ∫ q in Work.FTS.EllipticEst.Q0, V n q.1 q.2 * ψ q.1 q.2 := by
    funext n
    have h := integral_mixed_mul_adjMixed_open (g := V n) (ψ := φ) (hsm n) hφ hcs hts j i
    rw [hψdef]
    exact h
  refine ⟨∫ q in Work.FTS.EllipticEst.Q0, R q.1 q.2 * ψ q.1 q.2, ?_⟩
  rw [hIBP]
  exact tendsto_setIntegral_mul_of_pointwise_of_bound
    (W := fun n => V n) (L := R) (ψ := ψ)
    (fun n => (hsm n).continuousOn) hTestψ.1.continuousOn hTestψ.2.1.isCompact hTestψ.2.2
    hconv hbnd

end Work.FTS.StrongEps.E5G
end
end
