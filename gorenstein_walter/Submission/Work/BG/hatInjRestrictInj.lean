import Mathlib
import Submission.Work.BG.HatInjDefs
import Submission.Work.BG.rem31IndexUin
import Submission.Work.BG.CharBridge

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.GW2.C16 in
/-- Two characters in `𝒮₄(C)` with the same restriction to `U` are equal.

Route: `[H₀ : U] = 2` (`Work.BG.rem31IndexUin` plus `hn`), `t ∈ H₀`, `t ∉ U`, `t² = 1` give
`H₀ = U ∪ t·U`; for `ν ∈ 𝒮₄(C)` one has `t ∈ ker ν`, hence `ν(u·t) = ν(u)`
(`OddOrder.RepresentationTheory.apply_mul_eq_of_mem_characterKernel`) and `ν` is determined by
`ν|_U`. -/
theorem hatInjRestrictInj {G : Type} [Group G] [Finite G] {D : Work.GW2.BGData G}
    (C : Work.BG.Sec2Ctx G) (hc : Work.GW2.C16.Compat D C) (hn : D.n = 2)
    {ν μ : ClassFunction ↥C.P.H0 ℂ} (hν : ν ∈ Work.GW2.C16.S4Index C)
    (hμ : μ ∈ Work.GW2.C16.S4Index C) (h : Work.BG.restrictU C ν = Work.BG.restrictU C μ) :
    ν = μ := by
  -- `[H₀ : U] = [H₀ : Uin C] = n = 2`.
  have hUin : (Uin C).index = 2 := by rw [rem31IndexUin D C hc, hn]
  -- On `U` the two characters agree, by hypothesis.
  have hU : ∀ x : ↥C.P.H0, x ∈ Uin C → ν x = μ x := by
    intro x hx
    have hxP : (x : G) ∈ C.P.U := by
      rw [← Subgroup.mem_subgroupOf]; exact hx
    have hcongr := congrFun (congrArg Subtype.val h) (⟨(x : G), hxP⟩ : ↥C.P.U)
    rw [Work.BG.restrictU_apply, Work.BG.restrictU_apply] at hcongr
    exact hcongr
  refine ClassFunction.ext fun g => ?_
  by_cases hg : g ∈ Uin C
  · exact hU g hg
  · -- `g ∉ U`: then `g` and `t` lie in the same non-trivial coset of `U ≤ H₀`, so `g·t ∈ U`.
    have hgt : g * C.t ∈ Uin C := by
      rw [Subgroup.mul_mem_iff_of_index_two hUin]
      constructor <;> intro hh
      · exact absurd hh hg
      · have : (C.t : G) ∈ C.P.U := by
          rw [← Subgroup.mem_subgroupOf]; exact hh
        exact absurd this C.t_not_mem_U
    -- `ν C.t = ν 1`, i.e. `t ∈ ker ν` (and likewise for `μ`).
    have htker : C.t ∈ OddOrder.Peterfalvi.S03.characterKernel ν := by
      rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
        OddOrder.Peterfalvi.S03.characterDegree_def]
      exact hν.2.2
    have hv : ν g = ν (g * C.t) := (apply_mul_eq_of_mem_characterKernel hν.1 htker g).symm
    have htkerμ : C.t ∈ OddOrder.Peterfalvi.S03.characterKernel μ := by
      rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
        OddOrder.Peterfalvi.S03.characterDegree_def]
      exact hμ.2.2
    have hmu : μ (g * C.t) = μ g := apply_mul_eq_of_mem_characterKernel hμ.1 htkerμ g
    rw [hv, hU (g * C.t) hgt, hmu]

end Work.BG
