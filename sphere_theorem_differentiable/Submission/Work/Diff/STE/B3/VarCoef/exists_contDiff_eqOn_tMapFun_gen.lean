import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.D.R_Rstar_expansion2
import Submission.Work.Diff.STE.B3.closure_Omega_goodSet

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3.VarCoef

/-- **The chart transition `tMapFun D j k = coord_j ∘ pt_k` extends to a globally `C^∞` map.**

Here `tMapFun D j k y = coord_j (pt_k y)` (first index = target chart, per its definition in
`Submission/Work/Diff/STE/D/R_Rstar_expansion2.lean`).  The statement says that its restriction to
the open set `Ω := {y | D.psi k y ≠ 0 ∧ D.ζ j (D.pt k y) ≠ 0} = Omega D j k` agrees with a globally
`C^∞` map.

This is a piece of the proof of `Work.Diff.STE.B3.VarCoef.R_Qk_chartExpr`: the chain rule
`Work.Diff.STE.B3.VarCoef.lapPow_comp_eq_varLapPow` needs the transition and its inverse to be
globally `C^∞`.  It is needed with `(j,k) = (i,l)` (the transition `τ = coord_i ∘ pt_l` used by the
pointwise expansion `R l (Qk h) a b z = Σ … coeffFun … (tMapFun D i l z)`) and with
`(j,k) = (l,i)` (its local inverse `σ`).

Proof: `Ω` is exactly `Work.Diff.STE.D.Omega D j k`; the `B3Data` weights force `M` to be Hausdorff
(`Work.Diff.STE.B3.t2Space_of_B3Data`), so `closure Ω ⊆ goodSet D j k`
(`Work.Diff.STE.D.closure_Omega_subset_goodSet`), which is open, and `tMapFun D j k` is `C^∞` there
(`Work.Diff.STE.D.tMapFun_contDiffOn`), while `closure Ω` is compact
(`Work.Diff.STE.B3.isCompact_closure_Omega`).  Apply `Work.Diff.STE.D.bump_smul_smooth` with
`K := closure Ω`, `U := goodSet D j k`; this is literally the construction performed inside
`Work.Diff.STE.D.R_Rstar_expansion2`. -/
theorem exists_contDiff_eqOn_tMapFun_gen
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j k : ι₀) :
    ∃ T : (Fin (Module.finrank ℝ E) → ℝ) → (Fin (Module.finrank ℝ E) → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) T ∧
      (∀ y : Fin (Module.finrank ℝ E) → ℝ,
        D.psi k y ≠ 0 → D.ζ j (D.pt k y) ≠ 0 →
        T y = Work.Diff.STE.D.tMapFun (I := I) (M := M) D j k y) := by
  classical
  -- The `B3Data` weights force `M` to be Hausdorff, so the Layer-D lemmas become available.
  haveI hT2 : T2Space M := Work.Diff.STE.B3.t2Space_of_B3Data (I := I) (M := M) D
  -- the transition map, restricted to the open set `goodSet D j k`
  let g : (Fin (Module.finrank ℝ E) → ℝ) → (Fin (Module.finrank ℝ E) → ℝ) :=
    Work.Diff.STE.D.tMapFun (I := I) (M := M) D j k
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) g (Work.Diff.STE.D.goodSet (I := I) (M := M) D j k) :=
    Work.Diff.STE.D.tMapFun_contDiffOn (I := I) (M := M) D j k
  -- the bump: `closure Ω` is compact, `goodSet` is open and contains it
  have hK : IsCompact (closure (Work.Diff.STE.D.Omega (I := I) (M := M) D j k)) :=
    Work.Diff.STE.D.isCompact_closure_Omega (I := I) (M := M) D j k
  have hU : IsOpen (Work.Diff.STE.D.goodSet (I := I) (M := M) D j k) :=
    Work.Diff.STE.D.isOpen_goodSet (I := I) (M := M) D j k
  have hKU : closure (Work.Diff.STE.D.Omega (I := I) (M := M) D j k) ⊆
      Work.Diff.STE.D.goodSet (I := I) (M := M) D j k :=
    Work.Diff.STE.B3.closure_Omega_goodSet (I := I) (M := M) D j k
  obtain ⟨φ, _hφ, hone, _hsupp, hsm⟩ :=
    Work.Diff.STE.D.bump_smul_smooth (closure (Work.Diff.STE.D.Omega (I := I) (M := M) D j k))
      (Work.Diff.STE.D.goodSet (I := I) (M := M) D j k) hK hU hKU g hg
  refine ⟨fun y => φ y • g y, hsm, fun y hy1 hy2 => ?_⟩
  have hyO : y ∈ Work.Diff.STE.D.Omega (I := I) (M := M) D j k := ⟨hy1, hy2⟩
  have h1 : φ y = 1 := hone y (subset_closure hyO)
  show φ y • g y = Work.Diff.STE.D.tMapFun (I := I) (M := M) D j k y
  rw [h1, one_smul]

end Work.Diff.STE.B3.VarCoef
