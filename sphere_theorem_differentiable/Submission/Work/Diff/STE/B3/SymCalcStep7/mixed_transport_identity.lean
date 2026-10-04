import Mathlib
import Submission.Work.Diff.STE.B3.SymCalcStep5.conjCut_lapPow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3.SymCalcStep7

/-- **The transport identity for the `d`-mixed piece**, pointwise (no analysis, no smoothness): `M_d(V(Λ^k g)) − V(M_d(Λ^k g)) = compMap T' ( [M_{d∘T}, S_ε](P_k h) )`, where `V = conjCut ρ ε T T'`, `Λ^k = lapPow k`, `P_k = conjLapPow k T T'`, `S_ε = flatCut ρ ε`, `h = compMap T g`, and `[M_β,S_ε](w) = β · S_ε w − S_ε(β · w)` with `β = compMap T d`. Route: unfold `conjCut`; `M_d ∘ comp_{T'} = comp_{T'} ∘ M_{d∘T}` (needs `T ∘ T' = id`); `comp_T(Λ^k g) = P_k(comp_T g)` is `Work.Diff.STE.B3.SymCalcStep5.compMap_T_lapPow` (needs `T ∘ T' = id`); `comp_T(M_d u) = M_{d∘T}(comp_T u)` is definitional; and `compMap T'` of a difference is the difference of the `compMap T'`'s (definitional, pointwise). -/
theorem mixed_transport_identity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : (ι → ℝ) → ℝ) (ε : ℝ) (T T' : (ι → ℝ) → (ι → ℝ))
    (hTinv1 : ∀ x : ι → ℝ, T' (T x) = x) (hTinv2 : ∀ y : ι → ℝ, T (T' y) = y)
    (d g : (ι → ℝ) → ℂ) (k : ℕ) :
    (fun x => d x * Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T'
            (Work.Diff.STE.B3.SymCalcStep5.lapPow k g) x
          - Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T'
            (fun y => d y * Work.Diff.STE.B3.SymCalcStep5.lapPow k g y) x)
      = Work.Diff.STE.B3.SymCalc.compMap T'
          (fun x => Work.Diff.STE.B3.SymCalc.compMap T d x *
                Work.Diff.STE.B3.SymCalc.flatCut ρ ε
                  (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
                    (Work.Diff.STE.B3.SymCalc.compMap T g)) x
            - Work.Diff.STE.B3.SymCalc.flatCut ρ ε
                (fun y => Work.Diff.STE.B3.SymCalc.compMap T d y *
                  Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
                    (Work.Diff.STE.B3.SymCalc.compMap T g) y) x) := by
  -- `comp_T(Λ^k g) = P_k(comp_T g)`: the conjugation identity of step 5.
  have hP : Work.Diff.STE.B3.SymCalc.compMap T (Work.Diff.STE.B3.SymCalcStep5.lapPow k g)
      = Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
          (Work.Diff.STE.B3.SymCalc.compMap T g) :=
    Work.Diff.STE.B3.SymCalcStep5.compMap_T_lapPow k T T' hTinv2 g
  -- `comp_T(M_d (Λ^k g)) = M_{d∘T}(P_k(comp_T g))`: purely definitional, once `hP` is used.
  have hM : Work.Diff.STE.B3.SymCalc.compMap T
        (fun y => d y * Work.Diff.STE.B3.SymCalcStep5.lapPow k g y)
      = (fun y => d (T y) * Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
          (Work.Diff.STE.B3.SymCalc.compMap T g) y) := by
    funext y
    simp only [Work.Diff.STE.B3.SymCalc.compMap]
    rw [show Work.Diff.STE.B3.SymCalcStep5.lapPow k g (T y)
        = Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
            (Work.Diff.STE.B3.SymCalc.compMap T g) y from congrFun hP y]
  funext x
  -- unfold `V = conjCut ρ ε T T' = comp_{T'} ∘ S_ε ∘ comp_T`
  simp only [Work.Diff.STE.B3.SymCalc.conjCut]
  rw [hP, hM]
  -- `comp_{T'}` of the difference is the difference of the `comp_{T'}`'s, and `d (T (T' x)) = d x`
  simp only [Work.Diff.STE.B3.SymCalc.compMap, hTinv2]

end Work.Diff.STE.B3.SymCalcStep7
