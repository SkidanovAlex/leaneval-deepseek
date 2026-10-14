import Mathlib.Basic.Real.Basic
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnN0
import Submission.Work.FTS.StrongEps.EpsRLX.ModDiffAux.NBlockL12
import Submission.Work.FTS.StrongEps.EpsRLX.N0DiffClassC
import Submission.Work.FTS.StrongEps.H5.Nb5Core
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSlotInt
import Submission.Work.FTS_RegExport.THL.cs7_rop_split
import Submission.Work.FTS_StreamBdry.SB4.slice_L12_c2
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.SmoothStripDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsRLX

/-!
# `ModDiffClassC` — the `ClassC`-Lipschitz bound for the two modulation constants

Both modulation constants are, by definition (`Construction/Defs.lean`,
`Construction/MufunS.lean`),

  `μ̄ = L₁₂(N₀)(0) + L₁₂(N)(0)`,
  `μ  = (1/(2α))·(L₁₂(N₀)(0) + L₁₂(N)(0) + L₁₂(3 D_θ g/(1+z))(0))`,

so the difference of the two constants at `W₁` and `W₂` is the explicit linear combination of
the three `L₁₂`-zero-mode differences

  `ΔN₀ = L₁₂(N₀ α (F_*+W₁) W₁)(0) − L₁₂(N₀ α (F_*+W₂) W₂)(0)`,
  `ΔN  = L₁₂(N α (F_*+W₁) (Φ_s+E W₁))(0) − L₁₂(N α (F_*+W₂) (Φ_s+E W₂))(0)`,
  `ΔT  = L₁₂(3 D_θW₁/(1+z))(0) − L₁₂(3 D_θW₂/(1+z))(0)`,

each bounded by `K·(1 + |W₁|_{ℋ⁵} + |W₂|_{ℋ⁵})·|W₁−W₂|_{ℋ⁵}` by

* `EpsRLX.N0DiffClassC` (the quadratic block: the nine-piece telescoping `Rsum`),
* `ModDiffAux.NBlock.L12NDiffClassC` (the bilinear block: the twenty-term telescoping of
  `SharpAux`/`CCSharp` with the `E`-slot identity of `EComparison`), and
* `ModDiffAux.L12_transport_diff_classC` (the transport term, which is linear in the profile).

The proof below is the assembly `ModDiffAux.modDiff_of_L12_bounds`.
-/

theorem ModDiffClassC {α Ce Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} (hα : α ∈ Set.Ioc 0 1)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    ∃ K : ℝ, 0 < K ∧ ∀ {W₁ W₂ : Work.FTS.Galerkin.Fn},
      Work.FTS.ClassC.ClassC α W₁ → Work.FTS.ClassC.ClassC α W₂ →
      |Work.Construction.mufunS α (Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁)
          (Work.Construction.N α (Work.Construction.Ftot α W₁)
            (fun z θ => Φs z θ + E W₁ z θ)) W₁
        - Work.Construction.mufunS α (Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂)
          (Work.Construction.N α (Work.Construction.Ftot α W₂)
            (fun z θ => Φs z θ + E W₂ z θ)) W₂|
        ≤ K * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) ∧
      |Work.Construction.mubar (Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁)
          (Work.Construction.N α (Work.Construction.Ftot α W₁)
            (fun z θ => Φs z θ + E W₁ z θ))
        - Work.Construction.mubar (Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂)
          (Work.Construction.N α (Work.Construction.Ftot α W₂)
            (fun z θ => Φs z θ + E W₂ z θ))|
        ≤ K * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by
  obtain ⟨K0, hK0, h0spec⟩ := Work.FTS.StrongEps.EpsRLX.N0DiffClassC α hα
  obtain ⟨KN, hKN, hNN⟩ := Work.FTS.StrongEps.EpsRLX.ModDiffAux.NBlock.L12NDiffClassC
    (α := α) (Ce := Ce) (Cs := Cs) (Φs := Φs) (E := E) hα hEll hstar
  obtain ⟨KT, hKT, hTT⟩ := Work.FTS.StrongEps.EpsRLX.ModDiffAux.L12_transport_diff_classC
    (α := α) hα
  exact Work.FTS.StrongEps.EpsRLX.ModDiffAux.modDiff_of_L12_bounds (Ce := Ce) (Cs := Cs)
    hα hK0 hKN hKT (fun h₁ h₂ => (h0spec h₁ h₂).2.2.2) hNN hTT

end Work.FTS.StrongEps.EpsRLX
