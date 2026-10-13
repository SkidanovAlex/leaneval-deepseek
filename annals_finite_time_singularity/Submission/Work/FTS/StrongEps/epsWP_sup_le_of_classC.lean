import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.epsWP_abs_le_on_compact
import Submission.Work.FTS.StrongEps.epsWP_blocks_bnd
import Submission.Work.FTS.StrongEps.ScalarBounds
import Submission.Work.FTS.StrongEps.EpsLimitDefs
import Submission.Work.FTS.ClassC.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

theorem epsWP_sup_le_of_classC {α C₀ Cs Ce T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam} {ε : ℝ}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hε : ε ∈ Set.Ioc 0 1) (hT : 0 ≤ T)
    (hc1 : 1 / 10 ≤ Work.Spaces.c α) (hc2 : Work.Spaces.c α ≤ 10)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E)
    (hC : ∀ s ∈ Set.Icc 0 T, Work.FTS.ClassC.ClassC α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s))
    (hb4 : ∀ s ∈ Set.Icc 0 T, Work.FTS.Nonlin.Xn α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s) ≤ C₀ * α ^ 2)
    (hb6 : ∀ s ∈ Set.Icc 0 T, Work.FTS.StrongGlobal.Xn6 α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s) ≤ Ce)
    (hL12g : ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ Set.Icc 0 T, ∀ z ∈ Work.Spaces.Iz,
      |Work.Construction.L12 (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s) z|
        ≤ B)
    (hL12T : ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ Set.Icc 0 T,
      |Work.Coercivity.L12f (Work.Coercivity.Transport
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s)) 0| ≤ B)
    (hFK : ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ Set.Icc 0 T, ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Construction.FK (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s) z| ≤ B)
    (hmubar : ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ Set.Icc 0 T,
      |Work.Construction.mubar
        (Work.Construction.N0 α (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) s)
          (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s))
        (Work.Construction.N α (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) s)
          (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E
            (Work.FTS.StrongEps.JfamP ρ ε g)) s))| ≤ B)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKQ : K ⊆ Work.FTS.EllipticEst.Q0) :
    ∃ B' : ℝ, 0 < B' ∧ ∀ s ∈ Set.Icc 0 T, ∀ z θ : ℝ, (z, θ) ∈ K →
      |Work.FTS.StrongEps.epsWP α ρ ε Φs E g s z θ| ≤ B' := by
  -- ### step 1: the eleven-block bound of `epsWP_blocks_bnd`, with a constant `B₀`
  obtain ⟨B₀, hB₀nn, hbnd₀⟩ :=
    epsWP_blocks_bnd (α := α) (C₀ := C₀) (Cs := Cs) (Ce := Ce) (T := T) (ρ := ρ) (Φs := Φs)
      (E := E) (g := g) (ε := ε) hα hε hT hEll hstar hC hb4 hb6 hK hKQ
  -- ### step 2: the three constants missing from `epsWP_blocks_bnd`, discharged by
  -- `ScalarBounds`
  obtain ⟨B₂, hB₂pos, hB₂⟩ := L12_Fstar_abs_le
  obtain ⟨Bg, hBgnn, hL12g'⟩ := hL12g
  obtain ⟨BT, hBTnn, hL12T'⟩ := hL12T
  obtain ⟨BF, hBFnn, hFK'⟩ := hFK
  obtain ⟨Bm, hBmnn, hmubar'⟩ := hmubar
  -- a single constant dominating all of them
  set B : ℝ := B₀ + B₂ + Bg + BT + BF + Bm + 10 with hBdef
  have hBnn : 0 ≤ B := by
    rw [hBdef]; linarith [hB₀nn, hB₂pos.le, hBgnn, hBTnn, hBFnn, hBmnn]
  have hBle : ∀ x ∈ ({B₀, B₂, Bg, BT, BF, Bm, (10 : ℝ)} : Finset ℝ), x ≤ B := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h | h | h | h | h | h <;> rw [hBdef] <;>
      linarith [hB₀nn, hB₂pos.le, hBgnn, hBTnn, hBFnn, hBmnn]
  have hB₀le : B₀ ≤ B := hBle B₀ (by simp)
  have hB₂le : B₂ ≤ B := hBle B₂ (by simp)
  have hBgle : Bg ≤ B := hBle Bg (by simp)
  have hBTle : BT ≤ B := hBle BT (by simp)
  have hBFle : BF ≤ B := hBle BF (by simp)
  have hBmle : Bm ≤ B := hBle Bm (by simp)
  have h10le : (10 : ℝ) ≤ B := hBle 10 (by simp)
  -- ### step 3: feed `epsWP_abs_le_on_compact`
  refine epsWP_abs_le_on_compact (α := α) (C₀ := C₀) (B := B) (T := T) (ρ := ρ) (Φs := Φs)
    (E := E) (g := g) (ε := ε) hα hε hBnn hml hC hb4 hK hKQ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- the eleven-block bound, at the unified constant `B`
    intro s hs z θ hzθ
    exact le_trans (hbnd₀ s hs z θ hzθ) hB₀le
  · -- first `𝓛_Γ^T` coefficient
    intro z θ hzθ
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp (hKQ hzθ)
    exact le_trans (coef_abs_le hα hc1 z θ (le_of_lt hz) ⟨le_of_lt hθ0, le_of_lt hθ1⟩).1 h10le
  · -- second `𝓛_Γ^T` coefficient
    intro z θ hzθ
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp (hKQ hzθ)
    exact le_trans (coef_abs_le hα hc1 z θ (le_of_lt hz) ⟨le_of_lt hθ0, le_of_lt hθ1⟩).2 h10le
  · -- `L₁₂` of the slice
    intro s hs z hz
    exact le_trans (hL12g' s hs z hz) hBgle
  · -- `L₁₂(Transport ·)(0)` of the slice
    intro s hs
    exact le_trans (hL12T' s hs) hBTle
  · -- `L₁₂(F_*)`
    intro z hz
    exact le_trans (hB₂ α hα z hz) hB₂le
  · -- `FK` of the slice
    intro s hs z hz
    exact le_trans (hFK' s hs z hz) hBFle
  · -- `mubar` of the slice
    intro s hs
    exact le_trans (hmubar' s hs) hBmle

end Work.FTS.StrongEps
