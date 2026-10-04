import Mathlib
import Submission.Work.Diff.STE.B3.VarCoef.Assembly
import Submission.Work.Diff.STE.B3.VarCoef.perMatDefs
import Submission.Work.Diff.STE.B3.VarCoef.varLapStarDef
import Submission.Work.Diff.STE.B3.VarCoef.R_Qk_chartExpr_sym

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The CE data of the chart expansion of `Qk`, bundled (SESSION 23)

`VarCoef.R_Qk_chartExpr_sym D k l` produces the coefficients `A, B, ci, co` of the chart-`l`
expression of the differential operator `Qk D k` together with the **termwise coefficient
symmetry** on `‖z‖ ≤ 2σ_l`.  This file bundles that data into a structure `ChartCE D k l`, with
the symmetry strengthened to the **global** form

  `∑_{c,d} co i a b c d z * ci i c d c' d' z = ∑_{c,d} ci i c d a b z * co i c' d' c d z`

for *every* `z` (not only `‖z‖ ≤ 2σ_l`).

The global form is available because both `ci` and `co` are constructed (in the proof of
`R_Qk_chartExpr_sym`) as the periodisation of a function supported in `tsupport χl`, where `χl` is
the chart-`l` bump with `tsupport χl ⊆ {z | ‖z‖ < 2 σ l}`: hence `co` and `ci` vanish at every
point which has no lattice translate in the ball `‖·‖ < 2σ l`, and the pointwise symmetry holds on
the ball by `R_Qk_chartExpr_sym`.

The reason the global form is needed: the defect operator
`P^{αβ} - (P^{βα})^*` of the cross pair has order `2k` term by term, and its order drops to
`2k-1` only because the *sums* of the leading symbols cancel — which requires the coefficient
symmetry at every point on which the operator acts, not merely on the chart ball.
-/

namespace Work.Diff.STE.B3.VarCoef

open scoped Topology BigOperators

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- **The CE data of the chart-`l` expression of `Qk`.**  The fields `A`, `B`, `ci`, `co` are the
coefficients of the chart expression (`hCE`), with the strengthened global coefficient symmetry
(`hsym`). -/
structure ChartCE (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ) (l : ι₀) where
  /-- the chain-rule coefficients of the transition map -/
  A : ι₀ → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
    (Fin (Module.finrank ℝ E) → ℝ) → ℝ
  /-- the first-order chain-rule coefficients of the transition map -/
  B : ι₀ → Fin (Module.finrank ℝ E) → (Fin (Module.finrank ℝ E) → ℝ) → ℝ
  /-- the inner multipliers of the chart expression -/
  ci : ι₀ → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
    Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
    (Fin (Module.finrank ℝ E) → ℝ) → ℝ
  /-- the outer multipliers of the chart expression -/
  co : ι₀ → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
    Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
    (Fin (Module.finrank ℝ E) → ℝ) → ℝ
  hA : ∀ i a b, ContDiff ℝ (⊤ : ℕ∞) (A i a b)
  hAp : ∀ i a b, Work.Diff.STE.Periodic1 (A i a b)
  hB : ∀ i a, ContDiff ℝ (⊤ : ℕ∞) (B i a)
  hBp : ∀ i a, Work.Diff.STE.Periodic1 (B i a)
  hci : ∀ i c d c' d', ContDiff ℝ (⊤ : ℕ∞) (ci i c d c' d')
  hcip : ∀ i c d c' d', Work.Diff.STE.Periodic1 (ci i c d c' d')
  hco : ∀ i a b c d, ContDiff ℝ (⊤ : ℕ∞) (co i a b c d)
  hcop : ∀ i a b c d, Work.Diff.STE.Periodic1 (co i a b c d)
  /-- **the chart expression of `Qk`** in chart `l` -/
  hCE : ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
      (a b : Fin (Module.finrank ℝ E)),
      (∀ (j : ι₀) (a' b' : Fin (Module.finrank ℝ E)),
        ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R j h a' b')) →
      ∀ z : Fin (Module.finrank ℝ E) → ℝ,
        ((D.R l (Work.Diff.STE.B3.Qk D k h) a b z : ℝ) : ℂ) =
          ((D.psi l z * Real.sqrt (D.dens l z) : ℝ) : ℂ) *
            (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
              ((co i a b c d z : ℝ) : ℂ) *
                varLapPow k (A i) (B i)
                  (fun w => ∑ c' : Fin (Module.finrank ℝ E),
                    ∑ d' : Fin (Module.finrank ℝ E),
                    ((ci i c d c' d' w : ℝ) : ℂ) *
                      ((D.mat l h c' d' w : ℝ) : ℂ)) z)
  /-- **the global coefficient symmetry** -/
  hsym : ∀ (i : ι₀) (a b c' d' : Fin (Module.finrank ℝ E))
      (z : Fin (Module.finrank ℝ E) → ℝ),
      (∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
        co i a b c d z * ci i c d c' d' z)
        = ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
            ci i c d a b z * co i c' d' c d z

/-- The real-valued chart weight `φ l = ψ l · √(dens l)`, without the `ℂ`-lift of `perPhi`. -/
noncomputable def perPhiR (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (l : ι₀) :
    (Fin (Module.finrank ℝ E) → ℝ) → ℝ :=
  fun z => ∑' m : Fin (Module.finrank ℝ E) → ℤ,
    D.psi l (z + Work.Diff.STE.iVec m) * Real.sqrt (D.dens l (z + Work.Diff.STE.iVec m))

/-- `perPhi` is the `ℂ`-lift of `perPhiR`. -/
theorem perPhi_eq_ofReal_perPhiR (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (l : ι₀) :
    Work.Diff.STE.B3.perPhi (I := I) (M := M) D l
      = fun z => ((perPhiR (I := I) (M := M) D l z : ℝ) : ℂ) := by
  funext z
  rw [perPhiR, Work.Diff.STE.B3.perPhi]
  exact (Complex.ofReal_tsum _).symm

/-- The scalar operator `P^{αβ}` of the chart expression: the part of the chart-`l` expression of
`Qk` mapping the `β`-component of the chart matrix to the `α`-component. -/
noncomputable def pairP {D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀} {k : ℕ} {l : ι₀}
    (ce : ChartCE (I := I) (M := M) D k l) (α β : Fin (Module.finrank ℝ E) ×
      Fin (Module.finrank ℝ E)) : Op (Fin (Module.finrank ℝ E)) :=
  ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
    POp (ce.ci i c d β.1 β.2) (ce.co i α.1 α.2 c d)
      (varLapOp (ce.A i) (ce.B i)) k

/-- The true `L2re`-adjoint of `pairP ce β α`. -/
noncomputable def pairPStar {D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀} {k : ℕ} {l : ι₀}
    (ce : ChartCE (I := I) (M := M) D k l) (α β : Fin (Module.finrank ℝ E) ×
      Fin (Module.finrank ℝ E)) : Op (Fin (Module.finrank ℝ E)) :=
  ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
    POpStar (ce.ci i c d α.1 α.2) (ce.co i β.1 β.2 c d) (ce.A i)
      (fun a => -(ce.B i a)) k

end

end Work.Diff.STE.B3.VarCoef
