import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.epsWP_sup_le_of_classC
import Submission.Work.FTS.StrongEps.epsWP_abs_le_on_compact
import Submission.Work.FTS.StrongEps.epsWP_blocks_bnd
import Submission.Work.FTS.StrongEps.EpsWPBounds
import Submission.Work.FTS.StrongEps.ScalarBounds
import Submission.Work.FTS.StrongEps.epsWP_blocks_bnd_fam
import Submission.Work.FTS.StrongEps.epsWP_hyp_bounds_fam

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 2000000

namespace Work.FTS.StrongEps

/-- The family version of `epsWP_abs_le_on_compact`: the same explicit bound, uniform in `n`. -/
theorem epsWP_abs_le_on_compact_fam {α C₀ B T : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {G : ℕ → Work.FTS.Galerkin.Fam} {ε : ℕ → ℝ}
    (hα : α ∈ Set.Ioc 0 1) (hε : ∀ n : ℕ, ε n ∈ Set.Ioc 0 1) (hB : 0 ≤ B)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E)
    (hC : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T, Work.FTS.ClassC.ClassC α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s))
    (hb4 : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T, Work.FTS.Nonlin.Xn α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) ≤ C₀ * α ^ 2)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKQ : K ⊆ Work.FTS.EllipticEst.Q0)
    (hbnd : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T, ∀ z θ : ℝ, (z, θ) ∈ K →
      |Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s z θ|
        + |Work.Spaces.pth (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ|
        + |Work.Spaces.Dz (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ|
        + |Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s z θ|
        + |Work.Spaces.Dz (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ|
        + |Work.Spaces.pth (Work.Construction.Fstar α) z θ|
        + |Work.Spaces.Dz (Work.Construction.Fstar α) z θ|
        + |Work.Construction.Rop α (Work.Construction.PhiTil α
            (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
            (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E
              (Work.FTS.StrongEps.JfamP ρ (ε n) (G n))) s)) z θ|
        + |Work.Construction.Uop α (Work.Construction.PhiTil α
            (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
            (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E
              (Work.FTS.StrongEps.JfamP ρ (ε n) (G n))) s)) z θ|
        + |Work.Construction.Vop (Work.Construction.PhiTil α
            (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
            (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E
              (Work.FTS.StrongEps.JfamP ρ (ε n) (G n))) s)) z θ|
        + |Work.Construction.AK α z θ| ≤ B)
    (hcoef : ∀ z θ : ℝ, (z, θ) ∈ K →
      |2 * z * Work.Spaces.Gam α θ / (Work.Spaces.c α * (1 + z) ^ 2)| ≤ B)
    (hcoef2 : ∀ z θ : ℝ, (z, θ) ∈ K →
      |Work.Spaces.Gam α θ / Work.Spaces.c α * (2 * z ^ 2 / (1 + z) ^ 3)| ≤ B)
    (hL12f : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T, ∀ z ∈ Work.Spaces.Iz,
      |Work.Construction.L12 (Work.FTS.Galerkin.slice
        (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z| ≤ B)
    (hL12T : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T,
      |Work.Coercivity.L12f (Work.Coercivity.Transport
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)) 0| ≤ B)
    (hL12F : ∀ z ∈ Work.Spaces.Iz, |Work.Construction.L12 (Work.Construction.Fstar α) z| ≤ B)
    (hFK : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T, ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Construction.FK (Work.FTS.Galerkin.slice
        (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z| ≤ B)
    (hmubar : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T,
      |Work.Construction.mubar
        (Work.Construction.N0 α (Work.Construction.Ftau α
          (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
          (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s))
        (Work.Construction.N α (Work.Construction.Ftau α
          (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
          (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E
            (Work.FTS.StrongEps.JfamP ρ (ε n) (G n))) s))| ≤ B) :
    ∃ B' : ℝ, 0 < B' ∧ ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T, ∀ z θ : ℝ, (z, θ) ∈ K →
      |Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s z θ| ≤ B' := by
  obtain ⟨hα0, hα1⟩ := hα
  refine ⟨1 + (28 * B + 32 * B ^ 2)
      + ((B + 1) ^ 2 + (4 / α + 6) * (B + 1) ^ 2 + 8 * (B + 1) ^ 2 + 3 * (B + 1)), ?_, ?_⟩
  · have h4a : (0 : ℝ) < 4 / α := by positivity
    have hB1 : (0 : ℝ) < B + 1 := by linarith
    have hB1sq : (0 : ℝ) < (B + 1) ^ 2 := by positivity
    have hprod : (0 : ℝ) < (4 / α + 6) * (B + 1) ^ 2 := by positivity
    have h8 : (0 : ℝ) ≤ 8 * (B + 1) ^ 2 := by positivity
    have h28 : (0 : ℝ) ≤ 28 * B := by linarith
    have h32 : (0 : ℝ) ≤ 32 * B ^ 2 := by positivity
    have h3 : (0 : ℝ) < 3 * (B + 1) := by linarith
    linarith
  · intro n s hs z θ hzθ
    rw [show Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s z θ
        = -(Work.Coercivity.LGammaT α
              (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ)
          + Work.Construction.gRHS α
              (Work.FTS.Galerkin.muDyn α
                (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)))
                (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
              (Work.FTS.Galerkin.lamDyn α
                (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)))
                (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
              (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
              (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E
                (Work.FTS.StrongEps.JfamP ρ (ε n) (G n))) s)
              (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ from rfl]
    set J : Work.FTS.Galerkin.Fam := Work.FTS.StrongEps.JfamP ρ (ε n) (G n) with hJ
    set Φ : Work.FTS.Galerkin.Fam := Work.FTS.Nonlin.PsiCan Φs E J with hΦdef
    set f : Work.FTS.Galerkin.Fn := Work.FTS.Galerkin.slice J s with hfs
    set F : Work.FTS.Galerkin.Fn := Work.Construction.Ftau α J s with hFdef
    set Φs' : Work.FTS.Galerkin.Fn := Work.FTS.Galerkin.slice Φ s with hΦsdef
    -- the point of `K`
    have hQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := hKQ hzθ
    obtain ⟨hzpos, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hQ
    have hzge : (0 : ℝ) ≤ z := le_of_lt hzpos
    have hzIz : z ∈ Work.Spaces.Iz := hzge
    have hb := hbnd n s hs z θ hzθ
    -- the individual bounds extracted from the eleven-term sum
    have ha1 : (0 : ℝ) ≤ |F z θ| := abs_nonneg _
    have ha2 : (0 : ℝ) ≤ |Work.Spaces.pth F z θ| := abs_nonneg _
    have ha3 : (0 : ℝ) ≤ |Work.Spaces.Dz F z θ| := abs_nonneg _
    have ha4 : (0 : ℝ) ≤ |f z θ| := abs_nonneg _
    have ha5 : (0 : ℝ) ≤ |Work.Spaces.Dz f z θ| := abs_nonneg _
    have ha6 : (0 : ℝ) ≤ |Work.Spaces.pth (Work.Construction.Fstar α) z θ| := abs_nonneg _
    have ha7 : (0 : ℝ) ≤ |Work.Spaces.Dz (Work.Construction.Fstar α) z θ| := abs_nonneg _
    have ha8 : (0 : ℝ) ≤ |Work.Construction.Rop α (Work.Construction.PhiTil α F Φs') z θ| :=
      abs_nonneg _
    have ha9 : (0 : ℝ) ≤ |Work.Construction.Uop α (Work.Construction.PhiTil α F Φs') z θ| :=
      abs_nonneg _
    have ha10 : (0 : ℝ) ≤ |Work.Construction.Vop (Work.Construction.PhiTil α F Φs') z θ| :=
      abs_nonneg _
    have ha11 : (0 : ℝ) ≤ |Work.Construction.AK α z θ| := abs_nonneg _
    have ht2 : |Work.Spaces.pth F z θ| ≤ B := by
      linarith [hb, ha1, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11]
    have ht4 : |f z θ| ≤ B := by
      linarith [hb, ha1, ha2, ha3, ha5, ha6, ha7, ha8, ha9, ha10, ha11]
    have ht5 : |Work.Spaces.Dz f z θ| ≤ B := by
      linarith [hb, ha1, ha2, ha3, ha4, ha6, ha7, ha8, ha9, ha10, ha11]
    have ht6 : |Work.Spaces.pth (Work.Construction.Fstar α) z θ| ≤ B := by
      linarith [hb, ha1, ha2, ha3, ha4, ha5, ha7, ha8, ha9, ha10, ha11]
    -- the `D_θ`-bound on the slice: `pth (F_*+f) = pth F_* + pth f`
    have hdth : |Work.Spaces.Dth f z θ| ≤ 2 * B := by
      have h := Work.FTS.StrongEps.EpsWp.Dth_slice_le (α := α) (G := J) (s := s)
        (hC n s hs).reg hzpos hθ0 hθ1
      linarith [h, ht2, ht6]
    -- the linear part `𝓛_Γ^T`
    have hLG : |Work.Coercivity.LGammaT α f z θ| ≤ 28 * B + 32 * B ^ 2 := by
      have h4B : (0 : ℝ) ≤ 4 * B := by linarith
      have key : |Work.Coercivity.LGammaT α f z θ| ≤ 7 * (4 * B) + 2 * ((4 * B) * (4 * B)) :=
        Work.FTS.StrongEps.EpsWp.LGammaT_abs_le_explicit (α := α) (B := 4 * B) (f := f) h4B hzge
          (by linarith [ht4, ht5, hdth])
          (by linarith [hcoef z θ hzθ])
          (by linarith [hcoef2 z θ hzθ])
          (by have h := hL12f n s hs z hzIz
              have h' : |Work.Coercivity.L12f f z| ≤ B := h
              linarith)
          (by have h := hL12T n s hs
              have h' : |Work.Coercivity.L12f (Work.Coercivity.Transport f) 0| ≤ B := h
              linarith)
      convert key using 1
      ring
    -- the modulation constants, from `MuLamOK` at the slice-constant family
    have hμ : |Work.FTS.Galerkin.muDyn α Φ J s| ≤ 1 / 2 := by
      have h := (hml f (hC n s hs) (hb4 n s hs)).1
      rw [show Work.FTS.Galerkin.muDyn α Φ J s
          = Work.FTS.Galerkin.muDyn α
              (Work.FTS.Nonlin.PsiCan Φs E (fun z θ _ => f z θ)) (fun z θ _ => f z θ) 0
          from rfl]
      exact h
    have hlam : |Work.FTS.Galerkin.lamDyn α Φ J s| ≤ 1 := by
      have h := (hml f (hC n s hs) (hb4 n s hs)).2
      rw [show Work.FTS.Galerkin.lamDyn α Φ J s
          = Work.FTS.Galerkin.lamDyn α
              (Work.FTS.Nonlin.PsiCan Φs E (fun z θ _ => f z θ)) (fun z θ _ => f z θ) 0
          from rfl]
      exact h
    -- the nonlinear part `gRHS`, with the common bound `B + 1`
    have hGR : |Work.Construction.gRHS α
        (Work.FTS.Galerkin.muDyn α Φ J s) (Work.FTS.Galerkin.lamDyn α Φ J s)
        F Φs' f z θ|
        ≤ (B + 1) ^ 2 + (4 / α + 6) * (B + 1) ^ 2 + 8 * (B + 1) ^ 2 + 3 * (B + 1) := by
      have hB1 : (0 : ℝ) ≤ B + 1 := by linarith
      have hfk : |Work.Construction.FK F z| ≤ B + 1 :=
        Work.FTS.StrongEps.EpsWp.FK_fstar_add_bound (α := α) (f := f) (B := B) hα0 hα1 hB
          (by intro z' hz'; rw [hfs, hJ]; exact hFK n s hs z' hz') z hzpos
      have key : |Work.Construction.gRHS α
          (Work.FTS.Galerkin.muDyn α Φ J s) (Work.FTS.Galerkin.lamDyn α Φ J s)
          F Φs' f z θ|
          ≤ (B + 1) * (B + 1) + (4 / α + 6) * (B + 1) ^ 2 + 8 * (B + 1) ^ 2 + 3 * (B + 1) :=
        Work.FTS.StrongEps.EpsWp.gRHS_abs_le_explicit (α := α) (B := B + 1)
          (μ := Work.FTS.Galerkin.muDyn α Φ J s)
          (lam := Work.FTS.Galerkin.lamDyn α Φ J s)
          (F := F) (Φ := Φs') (g := f) hα0 hα1 hB1 hμ hlam
          (by linarith [hb]) (by linarith [hL12F z hzIz]) (by linarith [hL12f n s hs z hzIz])
          (by linarith [hmubar n s hs]) hfk
      convert key using 1
      ring
    -- assemble
    refine le_trans (abs_add_le _ _) ?_
    have h1 : |-(Work.Coercivity.LGammaT α f z θ)| ≤ 28 * B + 32 * B ^ 2 := by
      simpa using hLG
    linarith [h1, hLG, hGR]

theorem epsWP_sup_le_fam {α C₀ Ce Cs T : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {G : ℕ → Work.FTS.Galerkin.Fam} {ε : ℕ → ℝ}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hε : ∀ n : ℕ, ε n ∈ Set.Ioc 0 1) (hT : 0 ≤ T)
    (hc1 : 1 / 10 ≤ Work.Spaces.c α) (hc2 : Work.Spaces.c α ≤ 10)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E)
    (hC : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T, Work.FTS.ClassC.ClassC α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s))
    (hb4 : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T, Work.FTS.Nonlin.Xn α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) ≤ C₀ * α ^ 2)
    (hb6 : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T, Work.FTS.StrongGlobal.Xn6 α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) ≤ Ce)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKQ : K ⊆ Work.FTS.EllipticEst.Q0) :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T, ∀ p : ℝ × ℝ, p ∈ K →
      |Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s p.1 p.2| ≤ B := by
  obtain ⟨B₀, hB₀nn, hbnd₀⟩ :=
    epsWP_blocks_bnd_fam (α := α) (C₀ := C₀) (Cs := Cs) (Ce := Ce) (T := T) (ρ := ρ)
      (Φs := Φs) (E := E) (G := G) (ε := ε) hα hε hT hEll hstar hC hb4 hb6 hK hKQ
  obtain ⟨⟨BL, hBLnn, hL12⟩, ⟨BT, hBTnn, hL12T⟩, ⟨BF, hBFnn, hFK⟩, ⟨Bm, hBmnn, hmubar⟩⟩ :=
    epsWP_hyp_bounds_fam (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (T := T) (ρ := ρ)
      (Φs := Φs) (E := E) (G := G) (ε := ε) hα hEll hstar hC hb4 hb6
  obtain ⟨B₂, hB₂pos, hB₂⟩ := L12_Fstar_abs_le
  set B : ℝ := B₀ + BL + BT + BF + Bm + B₂ + 10 with hBdef
  have hBnn : 0 ≤ B := by rw [hBdef]; linarith [hB₀nn, hBLnn, hBTnn, hBFnn, hBmnn, hB₂pos.le]
  have hB₀le : B₀ ≤ B := by rw [hBdef]; linarith [hBLnn, hBTnn, hBFnn, hBmnn, hB₂pos.le]
  have hBLle : BL ≤ B := by rw [hBdef]; linarith [hB₀nn, hBTnn, hBFnn, hBmnn, hB₂pos.le]
  have hBTle : BT ≤ B := by rw [hBdef]; linarith [hB₀nn, hBLnn, hBFnn, hBmnn, hB₂pos.le]
  have hBFle : BF ≤ B := by rw [hBdef]; linarith [hB₀nn, hBLnn, hBTnn, hBmnn, hB₂pos.le]
  have hBmle : Bm ≤ B := by rw [hBdef]; linarith [hB₀nn, hBLnn, hBTnn, hBFnn, hB₂pos.le]
  have hB₂le : B₂ ≤ B := by rw [hBdef]; linarith [hB₀nn, hBLnn, hBTnn, hBFnn, hBmnn]
  have h10le : (10 : ℝ) ≤ B := by
    rw [hBdef]; linarith [hB₀nn, hBLnn, hBTnn, hBFnn, hBmnn, hB₂pos.le]
  obtain ⟨B', hB'pos, hB'bnd⟩ :=
    epsWP_abs_le_on_compact_fam (α := α) (C₀ := C₀) (B := B) (T := T) (ρ := ρ)
    (Φs := Φs) (E := E) (G := G) (ε := ε) hα hε hBnn hml hC hb4 hK hKQ
    (fun n s hs z θ hzθ => le_trans (hbnd₀ n s hs z θ hzθ) hB₀le)
    (fun z θ hzθ => by
      obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp (hKQ hzθ)
      exact le_trans (coef_abs_le hα hc1 z θ (le_of_lt hz) ⟨le_of_lt hθ0, le_of_lt hθ1⟩).1 h10le)
    (fun z θ hzθ => by
      obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp (hKQ hzθ)
      exact le_trans (coef_abs_le hα hc1 z θ (le_of_lt hz) ⟨le_of_lt hθ0, le_of_lt hθ1⟩).2 h10le)
    (fun n s hs z hz => le_trans (hL12 n s hs z hz) hBLle)
    (fun n s hs => le_trans (hL12T n s hs) hBTle)
    (fun z hz => le_trans (hB₂ α hα z hz) hB₂le)
    (fun n s hs z hz => le_trans (hFK n s hs z hz) hBFle)
    (fun n s hs => le_trans (hmubar n s hs) hBmle)
  exact ⟨B', hB'pos, fun n s hs p hp => hB'bnd n s hs p.1 p.2 hp⟩

end Work.FTS.StrongEps
