/-
Copyright: work module for the Elgindi finite-time singularity project.

# `EpsRLX/ConjOne.lean` — the membership/size half of the RHS gate

For the parameters of the projected `ε`-scheme this module produces a constant `L₁ > 0` such that
for every admissible datum `u` (i.e. the target's hypotheses at a single `u`) and every `τ`

`EpsMem α (epsRHPSlice α ρ ε Φs E τ u) ∧ EpsSq α (epsRHPSlice α ρ ε Φs E τ u) ≤ L₁`.

The chain is

`epsRHPSlice … u = Pz (J_ε Φ)`,  `Φ := profRHS α Φs E W`,  `W := Pz (J_ε u)`
(`epsRHPSlice_eq_profRHS`), and then, with `R` the uniform size of the pre-mollified right-hand
side at a class-`C` small-ball profile (`XDataClean`, `ProfRHSEpsData`):

* `EpsSq α Φ ≤ R` and `EpsMem α Φ`                              (`ProfRHSEpsData`),
* `EpsSq α (J_ε Φ) ≤ C_J · EpsSq α Φ` and `EpsMem α (J_ε Φ)`
  (`EpsSq_mixed_Jeps_le` at the slot `(0,0)`, `EpsSqIter_mixed_Jeps_le6`),
* `EpsMem α (Pz (J_ε Φ)) ∧ EpsSq α (Pz (J_ε Φ)) ≤ C_P · EpsSq α (J_ε Φ)`
  (`EpsSq_Pz_le`).

Note that no trace-vanishing of `Pz (J_ε Φ)` is needed: the membership of `J_ε Φ` comes directly
from `EpsSqIter_mixed_Jeps_le6` (which needs only `SmoothOpen Φ` and `EpsMem α Φ`), and the
membership of `Pz` of it from the bump decomposition.

**The `ℋ⁶`-size hypothesis.**  `XDataClean`/`ProfRHSEpsData` ask for `|W|_{ℋ⁶} ≤ B₀` *at the
profile* `W`, while the target only bounds the *datum* (`|u|_{ℋ⁶} ≤ B`).  The uniform enlargement
`BS := max B (C_W/(γ−1)·(C_W/ε)⁶·B)` absorbs this: `|W|_{ℋ⁶} ≤ BS` by `WpSixBound`, so the data
obtained at `BS` apply to every admissible `u`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsRLX.Defs
import Submission.Work.FTS.StrongEps.EpsRLX.BasicFacts
import Submission.Work.FTS.StrongEps.EpsRLX.XDataClean
import Submission.Work.FTS.StrongEps.EpsRLX.ProfRHSEpsData
import Submission.Work.FTS.StrongEps.EpsSqTools.EpsSq_mixed_Jeps_le
import Submission.Work.FTS.StrongEps.EpsSqTools.EpsSqIter_mixed_Jeps_le6
import Submission.Work.FTS.StrongEps.HkMem_Jeps

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsRLX

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

theorem ConjOne {α C₀ Ce Cs B : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {ε : ℝ}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε)
    (hε1 : ε ≤ 1)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) (hB : 0 ≤ B) :
    ∃ L : ℝ, 0 < L ∧ ∀ (τ : ℝ) (u : Fn),
      Work.FTS.EllipticEst.SmoothOpen u → Work.Spaces.HkMem α 6 u →
      Work.Spaces.HkNorm α 6 u ≤ B →
      Work.FTS.ClassC.ClassC α (Wp ρ ε u) → Work.FTS.Nonlin.Xn α (Wp ρ ε u) ≤ C₀ * α ^ 2 →
      Work.FTS.StrongEps.EpsMem α (Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E τ u) ∧
      Work.FTS.StrongEps.EpsSq α (Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E τ u) ≤ L := by
  have hγ : 0 < Work.Spaces.gam α - 1 := by
    have := Work.Spaces.one_lt_gam hα.1
    linarith
  -- ## the uniform enlargement of the size parameter
  obtain ⟨CW, hCWpos, hCW⟩ := WpSixBound (ρ := ρ) hρ
  set BS : ℝ := max B (CW / (Work.Spaces.gam α - 1) * (CW / ε) ^ 6 * B) with hBSdef
  have hBS0 : 0 ≤ BS := le_trans hB (by rw [hBSdef]; exact le_max_left _ _)
  have hWp6 : ∀ {u : Fn}, ProfileData α C₀ B ε ρ u → Work.Spaces.HkNorm α 6 (Wp ρ ε u) ≤ BS :=
    fun hd => le_trans (hCW α hα ε ⟨hε, hε1⟩ hB hd) (by
      rw [hBSdef]; exact le_max_right _ _)
  -- ## the data of the pre-mollified right-hand side, at the enlarged size
  obtain ⟨R, hRpos, hRdata⟩ := XDataClean (α := α) (Ce := Ce) (Cs := Cs) (C₀ := C₀) (B := BS)
    hα hEll hstar hml hBS0
  obtain ⟨R₂, hR₂pos, hR₂⟩ := ProfRHSEpsData (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (B := BS)
    hα hEll hstar hml hBS0
  obtain ⟨CP, hCPpos, hCP⟩ := EpsSq_Pz_le
  obtain ⟨CJ, hCJpos, hCJ⟩ := Work.FTS.StrongEps.EpsSqTools.EpsSq_mixed_Jeps_le ρ hρ
  obtain ⟨CM, -, hCM⟩ := Work.FTS.StrongEps.EpsSqTools.EpsSqIter_mixed_Jeps_le6 ρ hρ
  refine ⟨max 1 (CP * CJ * R₂), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro τ u hu hmu hnu hclu hxnu
  set W : Fn := Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε u) with hWdef
  set Φ : Fn := Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W with hΦdef
  have hclu' : Work.FTS.ClassC.ClassC α W := hclu
  have hxnu' : Work.FTS.Nonlin.Xn α W ≤ C₀ * α ^ 2 := hxnu
  have hW6 : Work.Spaces.HkNorm α 6 W ≤ BS := hWp6 (u := u) ⟨hu, hmu, hnu, hclu, hxnu⟩
  -- the pre-mollified right-hand side at `W`
  obtain ⟨hXsm, hXmem, -⟩ := hRdata (W := W) hclu' hxnu' hW6
  obtain ⟨hXepsMem, hXepsSq⟩ := hR₂ (W := W) hclu' hxnu' hW6
  -- the mollified profile
  have hsmΦ : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Φ) Work.FTS.StrongEps.Quad :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall Φ).mp hXsm
  have hJsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Jeps ρ ε Φ) :=
    Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε hsmΦ
  have hJmem : Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.Jeps ρ ε Φ) :=
    Work.FTS.StrongEps.HkMem_Jeps hρ.moll hα hε hsmΦ hXmem
  have hJepsMem : Work.FTS.StrongEps.EpsMem α (Work.FTS.StrongEps.Jeps ρ ε Φ) :=
    (hCM α hα ε hε hε1 Φ hsmΦ hXepsMem).1
  have hJepsSq : Work.FTS.StrongEps.EpsSq α (Work.FTS.StrongEps.Jeps ρ ε Φ)
      ≤ CJ * Work.FTS.StrongEps.EpsSq α Φ := by
    have h := hCJ α hα ε ⟨hε, hε1⟩ Φ hsmΦ hXepsMem 0 0 (by norm_num)
    have h1 : Work.FTS.StrongEps.EpsSq α
        (Work.Spaces.mixed 0 0 (Work.FTS.StrongEps.Jeps ρ ε Φ))
        = Work.FTS.StrongEps.EpsSq α (Work.FTS.StrongEps.Jeps ρ ε Φ) := by
      simp only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero]
    have h2 : CJ * (CJ / ε) ^ (2 * (0 + 0)) * Work.FTS.StrongEps.EpsSq α Φ
        = CJ * Work.FTS.StrongEps.EpsSq α Φ := by norm_num
    rw [h1, h2] at h
    exact h
  obtain ⟨hPzMem, hPzSq⟩ := hCP α hα (Work.FTS.StrongEps.Jeps ρ ε Φ) hJsm hJmem hJepsMem
  have hslice : Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E τ u
      = Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε Φ) := by
    rw [Work.FTS.StrongEps.EpsLocalPStar.epsRHPSlice_eq_profRHS]
  refine ⟨?_, ?_⟩
  · rw [hslice]; exact hPzMem
  · rw [hslice]
    calc Work.FTS.StrongEps.EpsSq α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε Φ))
        ≤ CP * Work.FTS.StrongEps.EpsSq α (Work.FTS.StrongEps.Jeps ρ ε Φ) := hPzSq
      _ ≤ CP * (CJ * Work.FTS.StrongEps.EpsSq α Φ) :=
          mul_le_mul_of_nonneg_left hJepsSq hCPpos.le
      _ = CP * CJ * Work.FTS.StrongEps.EpsSq α Φ := by ring
      _ ≤ CP * CJ * R₂ := mul_le_mul_of_nonneg_left hXepsSq (mul_nonneg hCPpos.le hCJpos.le)
      _ ≤ max 1 (CP * CJ * R₂) := le_max_right _ _

end Work.FTS.StrongEps.EpsRLX
