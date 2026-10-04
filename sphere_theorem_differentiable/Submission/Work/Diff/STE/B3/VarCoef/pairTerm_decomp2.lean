import Mathlib
import Submission.Work.Diff.STE.B3.VarCoef.pairTermDefs
import Submission.Work.Diff.STE.B3.VarCoef.POp_adjoint_L2re
import Submission.Work.Diff.STE.B3.SymCalcStep7.pairSharpAux
import Submission.Work.Diff.STE.B3.VarCoef.pairTerm_decomp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3.VarCoef

theorem pairTerm_decomp2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) (l : ι₀)
    (η : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (ce : Work.Diff.STE.B3.VarCoef.ChartCE (I := I) (M := M) D k l)
    (f u : Work.Diff.STE.Bil (I := I) (M := M))
    (hφ : Work.Diff.STE.B3.VarCoef.SmoothPer
      (fun z => ((Work.Diff.STE.B3.VarCoef.perPhiR (I := I) (M := M) D l z : ℝ) : ℂ)))
    (hF : ∀ a b : Fin (Module.finrank ℝ E), Work.Diff.STE.B3.VarCoef.SmoothPer
      (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l f a b))
    (hU : ∀ a b : Fin (Module.finrank ℝ E), Work.Diff.STE.B3.VarCoef.SmoothPer
      (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l u a b))
    (α β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) :
    (Work.Diff.STE.L2re (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l f α.1 α.2)
        (Work.Diff.STE.B3.VarCoef.xOpD (I := I) (M := M) D ρ ε l
          (Work.Diff.STE.B3.VarCoef.pairP ce α β
            (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l u β.1 β.2)))
      - Work.Diff.STE.L2re (Work.Diff.STE.B3.VarCoef.pairP ce β α
          (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l f α.1 α.2))
          (Work.Diff.STE.B3.VarCoef.xOpD (I := I) (M := M) D ρ ε l
            (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l u β.1 β.2)))
    = (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
        ( Work.Diff.STE.L2re (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l f α.1 α.2)
            (Work.Diff.STE.B3.VarCoef.xOpD (I := I) (M := M) D ρ ε l
              (Work.Diff.STE.B3.VarCoef.ptOp ce α β i c d
                (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l u β.1 β.2)))
        - Work.Diff.STE.L2re (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l f α.1 α.2)
            (Work.Diff.STE.B3.VarCoef.ptOp ce α β i c d
              (Work.Diff.STE.B3.VarCoef.xOpD (I := I) (M := M) D ρ ε l
                (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l u β.1 β.2))) ))
      + Work.Diff.STE.L2re (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l f α.1 α.2)
          ((Work.Diff.STE.B3.VarCoef.pairP ce α β
            - Work.Diff.STE.B3.VarCoef.pairPStar ce α β)
              (Work.Diff.STE.B3.VarCoef.xOpD (I := I) (M := M) D ρ ε l
                (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l u β.1 β.2))) := by
  classical
  -- ## The defect term, in the shape produced by `pairTerm_decomp`.
  --
  -- `pairTerm_decomp` writes the defect part as the *sum* `Σ_{icd} L2re F ((T_icd − T^*_icd) g)`
  -- of the individual operator differences; here it is stated with the *difference of sums*
  -- `L2re F ((pairP − pairPStar) g)`.  The two agree because `pairP` and `pairPStar` are by
  -- definition the finite sums `Σ_{icd} ptOp` and `Σ_{icd} ptStarOp` (`pairP_eq_sum_ptOp`,
  -- `pairPStar_eq_sum_ptStarOp`, both `rfl`) and `L2re` is additive over finite sums.
  have hdec :
      Work.Diff.STE.L2re (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l f α.1 α.2)
          ((pairP ce α β - pairPStar ce α β)
            (xOpD (I := I) (M := M) D ρ ε l
              (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l u β.1 β.2)))
        = ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
            Work.Diff.STE.L2re (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l f α.1 α.2)
              ((ptOp ce α β i c d - ptStarOp ce α β i c d)
                (xOpD (I := I) (M := M) D ρ ε l
                  (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l u β.1 β.2))) := by
    -- Replace `xOpD` by its defining cutoff sandwich and abbreviate the recurring objects.
    have hxop : ∀ g : (Fin (Module.finrank ℝ E) → ℝ) → ℂ,
        xOpD (I := I) (M := M) D ρ ε l g
          = XOp (perPhiR (I := I) (M := M) D l) (cutOp ρ ε) g := fun g => rfl
    simp only [hxop]
    set ψ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ :=
      perPhiR (I := I) (M := M) D l with hψdef
    set F : (Fin (Module.finrank ℝ E) → ℝ) → ℂ :=
      Work.Diff.STE.B3.perMat (I := I) (M := M) D η l f α.1 α.2 with hFdef
    set U2 : (Fin (Module.finrank ℝ E) → ℝ) → ℂ :=
      Work.Diff.STE.B3.perMat (I := I) (M := M) D η l u β.1 β.2 with hUdef
    set X : Op (Fin (Module.finrank ℝ E)) := XOp ψ (cutOp ρ ε) with hXdef
    -- Smoothness and periodicity of the weight `ψ = perPhiR_l`, extracted from `hφ`.
    have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := by
      have h1 : ContDiff ℝ (⊤ : ℕ∞)
          (fun z : Fin (Module.finrank ℝ E) → ℝ => Complex.re (((ψ z : ℝ) : ℂ))) :=
        Complex.reCLM.contDiff.comp hφ.1
      simpa [Complex.ofReal_re] using h1
    have hψp : Work.Diff.STE.Periodic1 ψ := by
      intro i x
      have h2 := congrArg Complex.re (hφ.2 i x)
      simpa using h2
    have hFsp : SmoothPer F := by rw [hFdef]; exact hF α.1 α.2
    have hUsp : SmoothPer U2 := by rw [hUdef]; exact hU β.1 β.2
    have hXpres : Preserves X := by rw [hXdef]; exact pres_XOp_cutOp ψ hψ hψp ρ hρ ε
    have hXUsp : SmoothPer (X U2) := hXpres U2 hUsp
    -- Smoothness of the individual summands.
    have hTsX : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)),
        SmoothPer (ptOp ce α β i c d (X U2)) := fun i c d =>
      pres_POp (ce.A i) (ce.B i) (ce.hA i) (ce.hAp i) (ce.hB i) (ce.hBp i)
        (ce.ci i c d β.1 β.2) (ce.co i α.1 α.2 c d)
        (ce.hci i c d β.1 β.2) (ce.hcip i c d β.1 β.2)
        (ce.hco i α.1 α.2 c d) (ce.hcop i α.1 α.2 c d) k (X U2) hXUsp
    have hTss : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)),
        SmoothPer (ptStarOp ce α β i c d (X U2)) := fun i c d =>
      pres_POpStar (ce.A i) (fun a => -(ce.B i a)) (ce.hA i) (ce.hAp i)
        (fun a => (ce.hB i a).neg) (fun a => periodic1_neg' (ce.hBp i a))
        (ce.ci i c d α.1 α.2) (ce.co i β.1 β.2 c d)
        (ce.hci i c d α.1 α.2) (ce.hcip i c d α.1 α.2)
        (ce.hco i β.1 β.2 c d) (ce.hcop i β.1 β.2 c d) k (X U2) hXUsp
    -- `(pairP − pairPStar) g = Σ_{icd} (ptOp − ptStarOp) g`, pointwise.
    have hdiff : (pairP ce α β - pairPStar ce α β) (X U2)
        = ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
            (ptOp ce α β i c d - ptStarOp ce α β i c d) (X U2) := by
      rw [pairP_eq_sum_ptOp, pairPStar_eq_sum_ptStarOp]
      funext z
      simp only [Pi.sub_apply, Finset.sum_apply]
      simp only [Finset.sum_sub_distrib]
    rw [hdiff]
    exact L2re_sum3_snd F hFsp.continuous
      (fun i c d => (ptOp ce α β i c d - ptStarOp ce α β i c d) (X U2))
      (fun i c d => by
        simpa only [Pi.sub_apply] using ((hTsX i c d).sub (hTss i c d)).continuous)
  rw [pairTerm_decomp D ρ hρ k ε hε l η ce f u hφ hF hU α β, hdec]

end Work.Diff.STE.B3.VarCoef
