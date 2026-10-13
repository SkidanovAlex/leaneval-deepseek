import Mathlib.Basic.Real.Basic
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.epsWP_hkMem4_bnd_fam
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnN
import Submission.Work.FTS.StrongEps.ClassCRHS.SmoothOpenRHS
import Submission.Work.FTS.StrongPersist.Star6
import Submission.Work.FTS.StrongPersist.StarPkg6OfCore
import Submission.Work.FTS.StrongEps.ClassCRHS.HkSumOpenClosure
import Submission.Work.FTS.StrongEps.H5.Asm
import Submission.Work.FTS.StrongEps.H5.HkMemXnLGammaT5
import Submission.Work.FTS.StrongEps.H5.HkMemXnN05
import Submission.Work.FTS.StrongEps.H5.HkMemXnN5

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5G

theorem epsWP_hkMem5_bnd_fam {α C₀ Ce Cs Cs6 T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {G : ℕ → Work.FTS.Galerkin.Fam}
    {ε : ℕ → ℝ}
    (hα : α ∈ Set.Ioc (0 : ℝ) 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hstar6 : Work.FTS.StrongPersist.StarPkg6 α Cs6 Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E)
    (hC : ∀ n : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.ClassC.ClassC α (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s))
    (hb4 : ∀ n : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.Nonlin.Xn α (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) ≤ C₀ * α ^ 2)
    (hb6 : ∀ n : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.StrongGlobal.Xn6 α (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) ≤ Ce) :
    ∃ KW : ℝ, 0 < KW ∧ ∀ n : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkMem α 5 (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s) ∧
        Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s) ≤ KW := by
  -- ### the three block estimates at level `5`
  obtain ⟨Kl, hKl, hLGT⟩ :=
    Work.FTS.StrongEps.H5.HkMemXnLGammaT5 (α := α) hα (C₀ := C₀) (B := Ce)
  obtain ⟨K0, hK0, hN0⟩ :=
    Work.FTS.StrongEps.H5.HkMemXnN05 (α := α) hα (C₀ := C₀) (B := Ce)
  obtain ⟨KN, hKN, hNb⟩ :=
    Work.FTS.StrongEps.H5.HkMemXnN5 (α := α) hα (C₀ := C₀) (B := Ce) (Ce := Ce) (Cs6 := Cs6)
      (Φs := Φs)
  -- ### the assembly
  obtain ⟨KW, hKW, hkey⟩ :=
    Work.FTS.StrongEps.H5.epsWP_hkMem5_bnd_unif_of_blocks (α := α) (C₀ := C₀) (Ce := Ce)
      (Cs6 := Cs6) (T := T) (ρ := ρ) (Φs := Φs) (E := E) hα hρ hEll hstar6 hml hKl hK0 hKN
      hLGT hN0 hNb
  -- ### the family form
  exact ⟨KW, hKW, fun n s hs => hkey (G n) (ε n) (fun s hs => hC n s hs)
    (fun s hs => hb4 n s hs) (fun s hs => hb6 n s hs) s hs⟩

end Work.FTS.StrongEps.E5G
