import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.E5G.Defs
import Submission.Work.FTS.StrongEps.EpsE4Thr.epsRHSP_hkMem_fam
import Submission.Work.FTS.StrongEps.EpsE4Thr.HkNorm_epsRHSP_le
import Submission.Work.FTS.StrongEps.epsWP_hkMem4_bnd_fam
import Submission.Work.FTS.StrongEps.smoothOpen_epsWP
import Submission.Work.FTS.StrongEps.HkMem_Jeps
import Submission.Work.FTS.StrongEps.E5Aux3.L12_slice_eq_zero_of_hkMem
import Submission.Work.FTS.StrongEps.E5Aux3.L12_Jeps_slice_tendsto_of_zero

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
