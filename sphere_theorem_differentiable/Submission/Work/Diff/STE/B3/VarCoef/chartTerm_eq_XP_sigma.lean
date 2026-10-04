import Mathlib
import Submission.Work.Diff.STE.B3.VarCoef.ChartCE
import Submission.Work.Diff.STE.B3.VarCoef.Rper_eq_perPhi_perMat_sigma
import Submission.Work.Diff.STE.B3.VarCoef.CPair_chart_term_eq_periodised
import Submission.Work.Diff.STE.B3.VarCoef.Rper_Qk_eq_perPhi_POp_sigma
import Submission.Work.Diff.STE.B3.VarCoef.chartTerm_eq_XP

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The chart term of the commutator pairing in the `XOp`/`pairP` vocabulary,
with the `σ`-ball cut-off hypothesis

This is the `σ`-ball version of `Work.Diff.STE.B3.VarCoef.chartTerm_eq_XP`: the cut-off `η` is
assumed to be `1` only on the ball of radius `D.σ l` (the hypothesis that the assembly actually
has, since the localised weight `ψ l` is supported in the open `σ l`-ball) rather than on the whole
`1/4`-ball.

The two `Rper` rewrites are supplied by the `σ`-ball variants `Rper_eq_perPhi_perMat_sigma` and
`Rper_Qk_eq_perPhi_POp_sigma`; the rest of the bookkeeping (the two `L2re` manipulations of the
cut-off sandwich, the chart expansion of `Qk` in the `pairP` vocabulary, and the final re-indexing)
is taken from `chartTerm_eq_XP`.
-/

noncomputable section

namespace Work.Diff.STE.B3.VarCoef

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-! ## 1. The two `Rper` families in the `mulOp`/`pairP` form, `σ`-ball hypothesis -/

/-- `Rper_l h = perPhi_l · perMat_l h`, with the weight written through its real part
`perPhiR_l`, under the `σ`-ball hypothesis on the cut-off. -/
theorem Rper_eq_mulOp_perMat_sigma
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (l : ι₀)
    (η : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hη1 : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ D.σ l → η z = 1)
    (hηt : tsupport η ⊆ Set.pi Set.univ
      (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)))
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (a b : Fin (Module.finrank ℝ E)) :
    D.Rper l h a b
      = mulOp (Work.Diff.STE.B3.VarCoef.perPhiR (I := I) (M := M) D l)
          (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l h a b) := by
  rw [Work.Diff.STE.B3.VarCoef.Rper_eq_perPhi_perMat_sigma (I := I) (M := M) D l η hη1 hηt h a b,
    Work.Diff.STE.B3.VarCoef.perPhi_eq_ofReal_perPhiR (I := I) (M := M) D l]
  rfl

/-- `Rper_l (Q_k h) = perPhi_l · Σ_β pairP_{αβ}(perMat_l h)`, the chart-`l` expansion of the
localised `Q_k h` written through the `pairP` operator of the scalar chart expression, under the
`σ`-ball hypothesis on the cut-off. -/
theorem Rper_Qk_eq_mulOp_pairP_sigma
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (k : ℕ) (l : ι₀)
    (η : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hη1 : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ D.σ l → η z = 1)
    (hηt : tsupport η ⊆ Set.pi Set.univ
      (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)))
    (ce : Work.Diff.STE.B3.VarCoef.ChartCE (I := I) (M := M) D k l)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hh : ∀ (j : ι₀) (a' b' : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R j h a' b'))
    (hS : ∀ c' d' : Fin (Module.finrank ℝ E),
      Work.Diff.STE.B3.VarCoef.SmoothPer
        (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l h c' d'))
    (a b : Fin (Module.finrank ℝ E)) :
    D.Rper l (Work.Diff.STE.B3.Qk D k h) a b
      = mulOp (Work.Diff.STE.B3.VarCoef.perPhiR (I := I) (M := M) D l)
          (∑ β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            Work.Diff.STE.B3.VarCoef.pairP ce (a, b) β
              (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l h β.1 β.2)) := by
  rw [Work.Diff.STE.B3.VarCoef.Rper_Qk_eq_perPhi_POp_sigma (I := I) (M := M) D k l η hη1 hηt
      ce h a b hh,
    Work.Diff.STE.B3.VarCoef.perPhi_eq_ofReal_perPhiR (I := I) (M := M) D l]
  exact mulOp_congr (A := fun z : Fin (Module.finrank ℝ E) → ℝ =>
      ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
        ((ce.co i a b c d z : ℝ) : ℂ) *
          Work.Diff.STE.B3.VarCoef.varLapPow k (ce.A i) (ce.B i)
            (fun w => ∑ c' : Fin (Module.finrank ℝ E), ∑ d' : Fin (Module.finrank ℝ E),
              ((ce.ci i c d c' d' w : ℝ) : ℂ) *
                Work.Diff.STE.B3.perMat (I := I) (M := M) D η l h c' d' w) z)
    (B := ∑ β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
        Work.Diff.STE.B3.VarCoef.pairP ce (a, b) β
          (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l h β.1 β.2))
    (pairP_expand_fun (A := ce.A) (B := ce.B) (ci := ce.ci) (co := ce.co)
      ce.hA ce.hAp ce.hB ce.hBp ce.hci ce.hcip k
      (fun c' d' => Work.Diff.STE.B3.perMat (I := I) (M := M) D η l h c' d') hS (a, b)).symm

/-! ## 2. The target -/

theorem chartTerm_eq_XP_sigma
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε)
    (f u : Work.Diff.STE.Bil (I := I) (M := M))
    (hf : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i f a b))
    (hu : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i u a b))
    (hQf : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i (Work.Diff.STE.B3.Qk D k f) a b))
    (hQu : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i (Work.Diff.STE.B3.Qk D k u) a b))
    (l : ι₀)
    (η : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hη1 : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ D.σ l → η z = 1)
    (hηt : tsupport η ⊆ Set.pi Set.univ
      (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)))
    (hφ : Work.Diff.STE.B3.VarCoef.SmoothPer
      (fun z => ((Work.Diff.STE.B3.VarCoef.perPhiR (I := I) (M := M) D l z : ℝ) : ℂ)))
    (hF : ∀ a b : Fin (Module.finrank ℝ E), Work.Diff.STE.B3.VarCoef.SmoothPer
      (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l f a b))
    (hU : ∀ a b : Fin (Module.finrank ℝ E), Work.Diff.STE.B3.VarCoef.SmoothPer
      (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l u a b))
    (ce : Work.Diff.STE.B3.VarCoef.ChartCE (I := I) (M := M) D k l) :
    (Work.Diff.STE.B3Data.CPair (E := E) l
        (fun a b z => Work.Diff.STE.B3Data.STruncR (E := E) ρ ε (D.R l f a b) z)
        (D.R l (Work.Diff.STE.B3.Qk D k u))
      - Work.Diff.STE.B3Data.CPair (E := E) l
        (fun a b z => Work.Diff.STE.B3Data.STruncR (E := E) ρ ε
          (D.R l (Work.Diff.STE.B3.Qk D k f) a b) z) (D.R l u))
    = (∑ α : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
        ∑ β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
        ( Work.Diff.STE.L2re
            (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l f α.1 α.2)
            (Work.Diff.STE.B3.VarCoef.XOp
              (Work.Diff.STE.B3.VarCoef.perPhiR (I := I) (M := M) D l)
              (Work.Diff.STE.B3.VarCoef.cutOp ρ ε)
              (Work.Diff.STE.B3.VarCoef.pairP ce α β
                (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l u β.1 β.2)))
        - Work.Diff.STE.L2re
            (Work.Diff.STE.B3.VarCoef.pairP ce β α
              (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l f α.1 α.2))
            (Work.Diff.STE.B3.VarCoef.XOp
              (Work.Diff.STE.B3.VarCoef.perPhiR (I := I) (M := M) D l)
              (Work.Diff.STE.B3.VarCoef.cutOp ρ ε)
              (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l u β.1 β.2)) )) := by
  classical
  -- ## Step 1: reduce the component pairings to the flat periodised form
  rw [Work.Diff.STE.B3.VarCoef.CPair_chart_term_eq_periodised (I := I) (M := M)
    D ρ hρ k ε hε f u hf hu hQf hQu l]
  simp only [← Work.Diff.STE.B3.VarCoef.cutOp_apply]
  -- ## Step 2: the two `Rper` families in the `mulOp`/`pairP` form
  have hψc : Continuous (fun z : Fin (Module.finrank ℝ E) → ℝ =>
      ((Work.Diff.STE.B3.VarCoef.perPhiR (I := I) (M := M) D l z : ℝ) : ℂ)) :=
    hφ.continuous
  have h1 : ∀ a b : Fin (Module.finrank ℝ E),
      Work.Diff.STE.L2re (D.Rper l f a b)
          (Work.Diff.STE.B3.VarCoef.cutOp ρ ε (D.Rper l (Work.Diff.STE.B3.Qk D k u) a b))
        = ∑ β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            Work.Diff.STE.L2re (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l f a b)
              (Work.Diff.STE.B3.VarCoef.XOp
                (Work.Diff.STE.B3.VarCoef.perPhiR (I := I) (M := M) D l)
                (Work.Diff.STE.B3.VarCoef.cutOp ρ ε)
                (Work.Diff.STE.B3.VarCoef.pairP ce (a, b) β
                  (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l u β.1 β.2))) := by
    intro a b
    rw [Rper_eq_mulOp_perMat_sigma (I := I) (M := M) D l η hη1 hηt f a b,
      Rper_Qk_eq_mulOp_pairP_sigma (I := I) (M := M) D k l η hη1 hηt ce u hu hU a b]
    exact L2re_mulOp_cutOp_mulOp_sum ρ hρ ε
      (Work.Diff.STE.B3.VarCoef.perPhiR (I := I) (M := M) D l) hψc
      (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l f a b) (hF a b).continuous
      (fun β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) =>
        Work.Diff.STE.B3.VarCoef.pairP ce (a, b) β
          (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l u β.1 β.2))
      (fun β => SmoothPer.mul hφ (pres_pairP_op ce.A ce.B ce.ci ce.co ce.hA ce.hAp ce.hB ce.hBp
        ce.hci ce.hcip ce.hco ce.hcop k (a, b) β
        (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l u β.1 β.2) (hU β.1 β.2)))
  have h2 : ∀ a b : Fin (Module.finrank ℝ E),
      Work.Diff.STE.L2re (D.Rper l (Work.Diff.STE.B3.Qk D k f) a b)
          (Work.Diff.STE.B3.VarCoef.cutOp ρ ε (D.Rper l u a b))
        = ∑ β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            Work.Diff.STE.L2re (Work.Diff.STE.B3.VarCoef.pairP ce (a, b) β
                (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l f β.1 β.2))
              (Work.Diff.STE.B3.VarCoef.XOp
                (Work.Diff.STE.B3.VarCoef.perPhiR (I := I) (M := M) D l)
                (Work.Diff.STE.B3.VarCoef.cutOp ρ ε)
                (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l u a b)) := by
    intro a b
    rw [Rper_Qk_eq_mulOp_pairP_sigma (I := I) (M := M) D k l η hη1 hηt ce f hf hF a b,
      Rper_eq_mulOp_perMat_sigma (I := I) (M := M) D l η hη1 hηt u a b]
    exact L2re_mulOp_sum_cutOp_mulOp ρ ε
      (Work.Diff.STE.B3.VarCoef.perPhiR (I := I) (M := M) D l)
      (fun β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) =>
        Work.Diff.STE.B3.VarCoef.pairP ce (a, b) β
          (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l f β.1 β.2))
      (fun β => (pres_pairP_op ce.A ce.B ce.ci ce.co ce.hA ce.hAp ce.hB ce.hBp ce.hci ce.hcip
        ce.hco ce.hcop k (a, b) β
        (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l f β.1 β.2) (hF β.1 β.2)).continuous)
      (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l u a b)
      (hψc.mul (((cutOp_isOrd ρ hρ ε).pres _
        (SmoothPer.mul hφ (hU a b))).continuous))
  -- ## Step 3: assemble the two sums
  have hT1 : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        Work.Diff.STE.L2re (D.Rper l f a b)
          (Work.Diff.STE.B3.VarCoef.cutOp ρ ε (D.Rper l (Work.Diff.STE.B3.Qk D k u) a b)))
      = ∑ α : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          ∑ β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            Work.Diff.STE.L2re (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l f α.1 α.2)
              (Work.Diff.STE.B3.VarCoef.XOp
                (Work.Diff.STE.B3.VarCoef.perPhiR (I := I) (M := M) D l)
                (Work.Diff.STE.B3.VarCoef.cutOp ρ ε)
                (Work.Diff.STE.B3.VarCoef.pairP ce α β
                  (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l u β.1 β.2))) := by
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => h1 a b))]
    rw [← sum_univ_prod (G := fun x : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) =>
      ∑ β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
        Work.Diff.STE.L2re (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l f x.1 x.2)
          (Work.Diff.STE.B3.VarCoef.XOp
            (Work.Diff.STE.B3.VarCoef.perPhiR (I := I) (M := M) D l)
            (Work.Diff.STE.B3.VarCoef.cutOp ρ ε)
            (Work.Diff.STE.B3.VarCoef.pairP ce x β
              (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l u β.1 β.2))))]
  have hT2 : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        Work.Diff.STE.L2re (D.Rper l (Work.Diff.STE.B3.Qk D k f) a b)
          (Work.Diff.STE.B3.VarCoef.cutOp ρ ε (D.Rper l u a b)))
      = ∑ α : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          ∑ β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            Work.Diff.STE.L2re (Work.Diff.STE.B3.VarCoef.pairP ce α β
                (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l f β.1 β.2))
              (Work.Diff.STE.B3.VarCoef.XOp
                (Work.Diff.STE.B3.VarCoef.perPhiR (I := I) (M := M) D l)
                (Work.Diff.STE.B3.VarCoef.cutOp ρ ε)
                (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l u α.1 α.2)) := by
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => h2 a b))]
    rw [← sum_univ_prod (G := fun x : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) =>
      ∑ β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
        Work.Diff.STE.L2re (Work.Diff.STE.B3.VarCoef.pairP ce x β
            (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l f β.1 β.2))
          (Work.Diff.STE.B3.VarCoef.XOp
            (Work.Diff.STE.B3.VarCoef.perPhiR (I := I) (M := M) D l)
            (Work.Diff.STE.B3.VarCoef.cutOp ρ ε)
            (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l u x.1 x.2)))]
  rw [hT1, hT2]
  -- ## Step 4: the final re-indexing of the subtracted double sum
  have hswap : (∑ α : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
        ∑ β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          Work.Diff.STE.L2re (Work.Diff.STE.B3.VarCoef.pairP ce β α
              (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l f α.1 α.2))
            (Work.Diff.STE.B3.VarCoef.XOp
              (Work.Diff.STE.B3.VarCoef.perPhiR (I := I) (M := M) D l)
              (Work.Diff.STE.B3.VarCoef.cutOp ρ ε)
              (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l u β.1 β.2)))
      = ∑ α : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          ∑ β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            Work.Diff.STE.L2re (Work.Diff.STE.B3.VarCoef.pairP ce α β
                (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l f β.1 β.2))
              (Work.Diff.STE.B3.VarCoef.XOp
                (Work.Diff.STE.B3.VarCoef.perPhiR (I := I) (M := M) D l)
                (Work.Diff.STE.B3.VarCoef.cutOp ρ ε)
                (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l u α.1 α.2)) :=
    Finset.sum_comm
  rw [← hswap]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [Finset.sum_sub_distrib]

end Work.Diff.STE.B3.VarCoef
