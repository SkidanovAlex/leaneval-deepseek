import Mathlib
import Submission.Work.LayerCont.LowBadClosureClean
import Submission.Work.Asymptotics.GcuspDefs

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section

namespace Work.LayerCont

open UpperHalfPlane MeasureTheory Filter
open scoped Topology

/-- **The guarded small-`t` cusp-expansion bound on the closure of the bad-line region,
dimension-free.**

`Work.HFN.CuspExp.smallT_bound` provides the bound `‖Kaxis - Aexp‖ ≤ C` for `1 ≤ t ≤ T` on a
compact `K ⊆ 𝒟`.  This is the same statement on `K ⊆ closure lowBadSet` — the region the
continuation needs, since the closure meets the bad lines `Re τ = ±1` — with the pole excluded by
the *strict* guard `1/8 < |t - τ.im|` (strictness is essential: `{τ | 1/8 < |t - τ.im|}` is open,
`isOpen_lt`, so it is a neighbourhood of each point of `K`, which is what lets the bound of
`Work.Asymptotics.HalfFunnel.lowBad_Kaxis_bound_aux` be transferred to the closure —
`Work.LayerCont.LowBadClosureClean`), and with cleanliness as a hypothesis, which is exactly what
the differentiation-under-the-integral-sign argument supplies on the retained set
`E = Ici 1 \ Ioo (t₀-A) (t₀+A)`.

The `Aexp` half is taken as an explicit hypothesis `hAexpLow`: bounding
`‖Aexp (Gcusp ℓ d) τ t‖` on the compact region `K × [1, lowT]` (equivalently: bounding the
`Gcusp`-coefficients there — they are of moderate growth on `𝒟` and the region keeps `Im τ ∈ [1/2,2]`
away from the cusps) is a separate, purely local obligation, and keeping it out of the statement
keeps this lemma dimension-free and free of `d`-specific bookkeeping. -/
theorem SmallTClosureLowBad (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {K : Set UpperHalfPlane} (hK : IsCompact K)
    (hsub : K ⊆ closure Work.Asymptotics.HalfFunnel.lowBadSet)
    (hclean : ∀ τ ∈ K, ∀ (t : ℝ) (ht : 0 < t), t ≤ Work.Asymptotics.HalfFunnel.lowT →
      (1 / 8 : ℝ) < |t - τ.im| →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht))
    (hAexpLow : ∃ Cae : ℝ, 0 ≤ Cae ∧ ∀ τ ∈ K, ∀ t : ℝ, 1 ≤ t →
      t ≤ Work.Asymptotics.HalfFunnel.lowT →
        ‖Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖ ≤ Cae)
    {A : ℝ} (hA : (1 / 8 : ℝ) < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ : UpperHalfPlane) (t : ℝ), τ ∈ K → 1 ≤ t →
      t ≤ Work.Asymptotics.HalfFunnel.lowT → A ≤ |t - τ.im| →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖ ≤ C := by
  obtain ⟨Cs, hCs, hb⟩ := LowBadClosureClean ℓ d hd hK hsub hclean
  obtain ⟨Cae, hCaenn, hae⟩ := hAexpLow
  refine ⟨max (Cs + Cae) 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun τ t hτ ht htT hsep => ?_⟩
  have h1 : ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ Cs :=
    hb τ t hτ (lt_of_lt_of_le zero_lt_one ht) htT (lt_of_lt_of_le hA hsep)
  have h2 : ‖Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖ ≤ Cae := hae τ hτ t ht htT
  calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖
      ≤ ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖
        + ‖Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖ := norm_sub_le _ _
    _ ≤ Cs + Cae := add_le_add h1 h2
    _ ≤ max (Cs + Cae) 1 := le_max_left _ _

end Work.LayerCont
