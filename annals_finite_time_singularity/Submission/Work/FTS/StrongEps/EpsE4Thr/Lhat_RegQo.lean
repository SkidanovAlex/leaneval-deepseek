import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.StrongEps.EpsE4Thr.regQo_dth_dz
import Submission.Work.FTS.StrongPersist.H6Aux.Facts
import Submission.Work.FTS.StrongPersist.H6Aux.LhatFacts
import Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_psi_mul_open
import Submission.Work.FTS.ClassC.A1
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd
import Submission.Work.FTS.CoercivityFix.PsiMul.PsiZop

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! # `𝓛̂` preserves the open-quadrant coercivity class `RegQo`

`Lhat f = 𝓛f − Transport f = f + D_z f − 2f/(1+z) − 3 D_θ f/(1+z)` (`CoercivityFix.Lhat_eq`),
so `RegQo α m (Lhat f)` follows from `RegQo α (m+1) f` componentwise:

* **smoothness** `SmoothOpen (Lhat f)` is `H6Aux.smoothOpen_Lhat`;
* **`ℋ^m`-membership** is the pointwise integrand domination `H6Aux.Lhat_mem`
  (`HkIntegrand α m (Lhat f) ≤ C·HkIntegrand α (m+1) f`);
* **boundary traces**: each of the four summands of `Lhat f` is a `RegQo`-port of `f`
  (`f` and `D_z f` by `regQo_dth_dz`, the two radial multiples `2f/(1+z)`, `3D_θf/(1+z)` by
  the open radial-multiplier lemma `TracesAux.BdryTraces_psi_mul_open` with `ψ = 1/(1+z)`),
  and `BdryTraces` is closed under sums, scalar multiples and differences
  (`ClassC.bdryTraces_add`, `ClassC.bdryTraces_smul`). -/

/-- `ψ(z) = 1/(1+z)` is `C^n` on `(0,∞)` for every `n` — the smoothness input of
`TracesAux.BdryTraces_psi_mul_open`. -/
private theorem contDiffOn_oneDiv_fts :
    ∀ n : ℕ, ContDiffOn ℝ n (fun z : ℝ => 1 / (1 + z)) (Set.Ioi 0) := by
  intro n
  refine ContDiffOn.div contDiffOn_const (contDiffOn_const.add contDiffOn_id) ?_
  intro z hz
  have hz0 : (0 : ℝ) < z := hz
  positivity

/-- A radial multiplier (`C^n` on `(0,∞)` for every `n`) preserves `SmoothOpen`. -/
private theorem smoothOpen_psi_mul_fts {ψ : ℝ → ℝ}
    (hψ : ∀ n : ℕ, ContDiffOn ℝ n ψ (Set.Ioi 0))
    {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => ψ z * g z θ) := by
  refine (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr fun n => ?_
  have h1 : ContDiffOn ℝ n (fun p : ℝ × ℝ => ψ p.1) Work.FTS.EllipticEst.Q0 :=
    (hψ n).comp contDiff_fst.contDiffOn (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
  have h2 : ContDiffOn ℝ n (fun p : ℝ × ℝ => g p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    hg.forall n
  exact h1.mul h2

/-- `BdryTraces` is closed under multiplication by a constant, in the pointwise form (the frozen
`ClassC.bdryTraces_smul` is stated with `c • f`). -/
private theorem bdryTraces_const_mul_fts {α : ℝ} {k : ℕ} {f : Fn} (c : ℝ)
    (hf : Work.FTS.Nonlin.BdryTraces α k f) :
    Work.FTS.Nonlin.BdryTraces α k (fun z θ => c * f z θ) :=
  Work.FTS.ClassC.bdryTraces_smul (α := α) (k := k) hf c

/-- **`RegQo` is preserved by the clean operator `𝓛̂ = 𝓛 − Transport`.** -/
theorem Lhat_RegQo (α : ℝ) (hα : 0 < α) (m : ℕ) {f : Work.FTS.Galerkin.Fn}
    (hf : Work.FTS.StrongEps.EpsE4Thr.RegQo α (m + 1) f) :
    Work.FTS.StrongEps.EpsE4Thr.RegQo α m (Work.FTS.CoercivityFix.Lhat f) := by
  obtain ⟨hsm, hmem, hbd⟩ := hf
  have hf' : Work.FTS.StrongEps.EpsE4Thr.RegQo α (m + 1) f := ⟨hsm, hmem, hbd⟩
  refine ⟨Work.FTS.StrongPersist.H6Aux.smoothOpen_Lhat hsm,
    Work.FTS.StrongPersist.H6Aux.Lhat_mem α hα m hsm hmem, ?_⟩
  -- the traces of `f` at level `m`, and the two `RegQo`-ports at level `m`
  have hf_tr : Work.FTS.Nonlin.BdryTraces α m f :=
    Work.FTS.ClassC.bdryTraces_mono (k := m) (l := m + 1) (by omega) hbd
  obtain ⟨hdth, hdz⟩ := regQo_dth_dz hα hf'
  have htZ : Work.FTS.Nonlin.BdryTraces α m (Work.Spaces.Dz f) := hdz.2.2
  have htT : Work.FTS.Nonlin.BdryTraces α m (Work.Spaces.Dth f) := hdth.2.2
  -- the `Zop`-iterate bound for `ψ(z) = 1/(1+z)` up to order `m`
  obtain ⟨K, hK0, hKb⟩ := Work.FTS.CoercivityFix.PsiMul.zop_psi_bound m
  -- the first radial multiple `2f/(1+z)`
  have h2sm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => 2 * f z θ) := hsm.const_mul' 2
  have h2tr : Work.FTS.Nonlin.BdryTraces α m (fun z θ => 2 * f z θ) :=
    bdryTraces_const_mul_fts 2 hf_tr
  have hXsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (1 / (1 + z)) * (2 * f z θ)) :=
    smoothOpen_psi_mul_fts (ψ := fun z => 1 / (1 + z)) contDiffOn_oneDiv_fts h2sm
  have hXtr : Work.FTS.Nonlin.BdryTraces α m
      (fun z θ => (1 / (1 + z)) * (2 * f z θ)) :=
    TracesAux.BdryTraces_psi_mul_open (k := m)
      (ψ := fun z => 1 / (1 + z)) (K := K) (x := fun z θ => 2 * f z θ)
      hK0 hKb contDiffOn_oneDiv_fts h2sm h2tr
  -- the second radial multiple `3D_θf/(1+z)`
  have h3sm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => 3 * Work.Spaces.Dth f z θ) := hsm.Dth.const_mul' 3
  have h3tr : Work.FTS.Nonlin.BdryTraces α m
      (fun z θ => 3 * Work.Spaces.Dth f z θ) := bdryTraces_const_mul_fts 3 htT
  have hYsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (1 / (1 + z)) * (3 * Work.Spaces.Dth f z θ)) :=
    smoothOpen_psi_mul_fts (ψ := fun z => 1 / (1 + z)) contDiffOn_oneDiv_fts h3sm
  have hYtr : Work.FTS.Nonlin.BdryTraces α m
      (fun z θ => (1 / (1 + z)) * (3 * Work.Spaces.Dth f z θ)) :=
    TracesAux.BdryTraces_psi_mul_open (k := m)
      (ψ := fun z => 1 / (1 + z)) (K := K) (x := fun z θ => 3 * Work.Spaces.Dth f z θ)
      hK0 hKb contDiffOn_oneDiv_fts h3sm h3tr
  -- the summand `f + D_z f`
  have hPsm : Work.FTS.EllipticEst.SmoothOpen (f + Work.Spaces.Dz f) :=
    Work.FTS.EllipticEst.smoothOpen_add (f := f) (g := Work.Spaces.Dz f) hsm hsm.Dz
  have hPtr : Work.FTS.Nonlin.BdryTraces α m (f + Work.Spaces.Dz f) :=
    Work.FTS.ClassC.bdryTraces_add (f := f) (g := Work.Spaces.Dz f) hsm hsm.Dz hf_tr htZ
  -- the sum of the two radial multiples, and its negative
  have hQsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      (1 / (1 + z)) * (2 * f z θ) + (1 / (1 + z)) * (3 * Work.Spaces.Dth f z θ)) :=
    Work.FTS.EllipticEst.smoothOpen_add
      (f := fun z θ => (1 / (1 + z)) * (2 * f z θ))
      (g := fun z θ => (1 / (1 + z)) * (3 * Work.Spaces.Dth f z θ)) hXsm hYsm
  have hQtr : Work.FTS.Nonlin.BdryTraces α m (fun z θ =>
      (1 / (1 + z)) * (2 * f z θ) + (1 / (1 + z)) * (3 * Work.Spaces.Dth f z θ)) :=
    Work.FTS.ClassC.bdryTraces_add
      (f := fun z θ => (1 / (1 + z)) * (2 * f z θ))
      (g := fun z θ => (1 / (1 + z)) * (3 * Work.Spaces.Dth f z θ)) hXsm hYsm hXtr hYtr
  have hNQsm : Work.FTS.EllipticEst.SmoothOpen ((-1 : ℝ) •
      (fun z θ => (1 / (1 + z)) * (2 * f z θ)
        + (1 / (1 + z)) * (3 * Work.Spaces.Dth f z θ))) :=
    hQsm.const_mul' (-1)
  have hNQtr : Work.FTS.Nonlin.BdryTraces α m ((-1 : ℝ) •
      (fun z θ => (1 / (1 + z)) * (2 * f z θ)
        + (1 / (1 + z)) * (3 * Work.Spaces.Dth f z θ))) :=
    Work.FTS.ClassC.bdryTraces_smul hQtr (-1)
  -- the operator unfolds to that combination
  have hL : Work.FTS.CoercivityFix.Lhat f = (f + Work.Spaces.Dz f) + (-1 : ℝ) •
      (fun z θ => (1 / (1 + z)) * (2 * f z θ)
        + (1 / (1 + z)) * (3 * Work.Spaces.Dth f z θ)) := by
    funext z θ
    rw [Work.FTS.CoercivityFix.Lhat_eq]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hL]
  exact Work.FTS.ClassC.bdryTraces_add (f := f + Work.Spaces.Dz f)
    (g := (-1 : ℝ) • (fun z θ => (1 / (1 + z)) * (2 * f z θ)
      + (1 / (1 + z)) * (3 * Work.Spaces.Dth f z θ)))
    hPsm hNQsm hPtr hNQtr

end Work.FTS.StrongEps.EpsE4Thr
