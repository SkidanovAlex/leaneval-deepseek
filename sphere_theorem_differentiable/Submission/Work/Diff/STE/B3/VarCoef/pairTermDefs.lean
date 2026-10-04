import Mathlib
import Submission.Work.Diff.STE.B3.VarCoef.ChartCE

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The scalar operators of the final pair estimate (SESSION 23)

The chart-`l` pair of `ENormB_pair_J_commutator_v2` is
`L2re(F_α, X_l (P^{αβ} U_β)) − L2re(P^{βα} F_α, X_l U_β)` with
`X_l = M_{perPhiR_l} ∘ flatCut ρ ε ∘ M_{perPhiR_l}` (the cutoff sandwich in the cutoff's own
chart) and `P^{αβ} = pairP ce α β` the chart expression of `Qk` (`ChartCE`).  This file names the
three scalar operators that occur in the decomposition of that pair into its commutator and its
defect part:

* `xOpD D ρ ε l = XOp (perPhiR D l) (cutOp ρ ε)`;
* `ptOp ce α β i c d = POp (ce.ci i c d β) (ce.co i α c d) (varLapOp (ce.A i) (ce.B i)) k`;
* `ptStarOp ce α β i c d` is the true `L2re`-adjoint of `ptOp ce β α i c d`.
-/

namespace Work.Diff.STE.B3.VarCoef

open scoped BigOperators

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- The cutoff sandwich `M_{perPhiR} ∘ flatCut ρ ε ∘ M_{perPhiR}` of the chart `l`. -/
noncomputable def xOpD (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ) (l : ι₀) :
    Op (Fin (Module.finrank ℝ E)) :=
  XOp (perPhiR (I := I) (M := M) D l) (cutOp ρ ε)

/-- The `(i,c,d)`-term of the chart expression `pairP ce α β` (component `β` in, component `α`
out). -/
noncomputable def ptOp {D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀} {k : ℕ} {l : ι₀}
    (ce : ChartCE (I := I) (M := M) D k l)
    (α β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) (i : ι₀)
    (c d : Fin (Module.finrank ℝ E)) : Op (Fin (Module.finrank ℝ E)) :=
  POp (ce.ci i c d β.1 β.2) (ce.co i α.1 α.2 c d) (varLapOp (ce.A i) (ce.B i)) k

/-- The true `L2re`-adjoint of `ptOp ce β α i c d`. -/
noncomputable def ptStarOp {D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀} {k : ℕ} {l : ι₀}
    (ce : ChartCE (I := I) (M := M) D k l)
    (α β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) (i : ι₀)
    (c d : Fin (Module.finrank ℝ E)) : Op (Fin (Module.finrank ℝ E)) :=
  POpStar (ce.ci i c d α.1 α.2) (ce.co i β.1 β.2 c d) (ce.A i)
    (fun a => -(ce.B i a)) k

/-- `pairP ce α β` is the sum of the `(i,c,d)`-terms `ptOp ce α β i c d`. -/
theorem pairP_eq_sum_ptOp {D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀} {k : ℕ} {l : ι₀}
    (ce : ChartCE (I := I) (M := M) D k l)
    (α β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) :
    pairP ce α β
      = ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
          ptOp ce α β i c d := rfl

/-- `pairPStar ce α β` is the sum of the `(i,c,d)`-terms `ptStarOp ce α β i c d`. -/
theorem pairPStar_eq_sum_ptStarOp {D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀}
    {k : ℕ} {l : ι₀} (ce : ChartCE (I := I) (M := M) D k l)
    (α β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) :
    pairPStar ce α β
      = ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
          ptStarOp ce α β i c d := rfl

end

end Work.Diff.STE.B3.VarCoef
