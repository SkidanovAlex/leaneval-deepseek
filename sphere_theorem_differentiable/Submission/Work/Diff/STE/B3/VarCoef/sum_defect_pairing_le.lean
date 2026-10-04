import Mathlib
import Submission.Work.Diff.STE.B3.VarCoef.sum_pairing_le
import Submission.Work.Diff.STE.B3.VarCoef.Assembly
import Submission.Work.Diff.STE.B3.SymCalcStep8.L2re_le_sqrt_CSqZ
import Submission.Work.Diff.STE.B3.VarCoef.mulOp_isOrd
import Submission.Work.Diff.STE.B3.VarCoef.cutOp_isOrd

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `sum_defect_pairing_le` — the pairing bound for the "defect" half of the pair estimate

This is the flat, finite-family estimate needed for the defect operator
`P^{αβ} − (P^{βα})^*` of the pair estimate `ENormB_pair_J_commutator_v2`: for **arbitrary**
operators `T γ` of order `2k − 1` (the defect operator satisfies this, see
`Work.Diff.STE.B3.VarCoef.POp_swap_sub_star_isOrd`), the sum over the charts `γ` of the pairings

  `Σ_γ L2re (F γ) (T γ (XOp (ψ γ) (cutOp ρ ε) (U γ)))`

is bounded, **uniformly in the cutoff scale `ε ∈ (0,1]`**, by
`C · √(Σ_γ CSq (k−1) (fourierCoeff (F γ))) · √(Σ_γ CSq k (fourierCoeff (U γ)))`.

## Proof

Everything is the `VarCoef` order calculus of `OpOrder.lean`:

* `XOp ψ S_ε = M_ψ ∘ S_ε ∘ M_ψ` is an operator of order `0` with an `ε`-free constant: `M_ψ` is of
  order `0` (`mulOp_isOrd`, from `hψ`, `hψp`) and `S_ε = cutOp ρ ε` is of order `0` with constant
  `1`, uniformly in `ε` (`cutOp_isOrd`, from `hρ` alone).  Two compositions (`IsOrd.comp`) give the
  certificate; the constants are *explicitly* the constants produced by `IsOrd.comp`, which is what
  makes the `ε`-uniformity syntactically evident (the operator mentions `ε`, the constant does not).
* Hence `T γ ∘ XOp ψ S_ε` has order `2k − 1` with an `ε`-free constant `Ct γ`, so at `t = k` its
  `IsOrd.bound` reads
  `CSqZ (k − (2k − 1)) (fourierCoeff (T γ (XOp … (U γ)))) ≤ Ct γ k · CSqZ k (fourierCoeff (U γ))`,
  and `k − (2k − 1) = −(k − 1)`.
* The weighted Cauchy–Schwarz / Parseval estimate `L2re_le_sqrt_CSqZ (k−1)` then gives the per-`γ`
  bound with the constant `√(Ct γ k)`, using `CSqZ (k−1) = CSq (k−1)` and `CSqZ k = CSq k`
  (`CSqZ_natCast`).
* The sum over the finite family `κ` is the discrete Cauchy–Schwarz `abs_sum_le_sum_mul_sqrt`
  (from `sum_pairing_le.lean`), with the constant `C = Σ_γ √(Ct γ k)`.
-/

noncomputable section

open scoped BigOperators

namespace Work.Diff.STE.B3.VarCoef

/-- The cutoff sandwich `XOp ψ (cutOp ρ ε) = M_ψ ∘ S_ε ∘ M_ψ` is an operator of order `0` whose
constant can be chosen **independent of `ε`**.  The constant exhibited is exactly the one produced
by the two `IsOrd.comp` compositions, so no `ε` ever enters it. -/
theorem exists_isOrd_XOp_cutOp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : (ι → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψp : Work.Diff.STE.Periodic1 ψ)
    (ρ : (ι → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1) :
    ∃ Cx : ℤ → ℝ, ∀ ε : ℝ, IsOrd 0 Cx (XOp ψ (cutOp ρ ε)) := by
  obtain ⟨Cψ, hCψ⟩ := mulOp_isOrd ψ hψ hψp
  refine ⟨fun t => (fun s => Cψ (s - 0) * (fun _ => (1 : ℝ)) s) (t - 0) * Cψ t,
    fun ε => ?_⟩
  have h1 : IsOrd (0 + 0) (fun t => Cψ (t - 0) * (fun _ => (1 : ℝ)) t)
      (compOp (mulOp ψ) (cutOp ρ ε)) :=
    IsOrd.comp (T := mulOp ψ) (U := cutOp ρ ε) hCψ (cutOp_isOrd ρ hρ ε)
  have h2 : IsOrd ((0 + 0) + 0)
      (fun t => (fun s => Cψ (s - 0) * (fun _ => (1 : ℝ)) s) (t - 0) * Cψ t)
      (compOp (compOp (mulOp ψ) (cutOp ρ ε)) (mulOp ψ)) :=
    IsOrd.comp (T := compOp (mulOp ψ) (cutOp ρ ε)) (U := mulOp ψ) h1 hCψ
  exact IsOrd.mono_d h2 (by omega)

theorem sum_defect_pairing_le {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ]
    (k : ℕ) (hk : 1 ≤ k) (ρ : (ι → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1)
    (ψ : κ → (ι → ℝ) → ℝ) (hψ : ∀ γ, ContDiff ℝ (⊤ : ℕ∞) (ψ γ))
    (hψp : ∀ γ, Work.Diff.STE.Periodic1 (ψ γ))
    (T : κ → Work.Diff.STE.B3.VarCoef.Op ι) (Cfun : ℤ → ℝ)
    (hT : ∀ γ, Work.Diff.STE.B3.VarCoef.IsOrd (2 * (k : ℤ) - 1) Cfun (T γ)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ (F U : κ → (ι → ℝ) → ℂ),
        (∀ γ, Work.Diff.STE.B3.VarCoef.SmoothPer (F γ)) →
        (∀ γ, Work.Diff.STE.B3.VarCoef.SmoothPer (U γ)) →
        abs (∑ γ : κ, Work.Diff.STE.L2re (F γ)
            (T γ (Work.Diff.STE.B3.VarCoef.XOp (ψ γ)
              (Work.Diff.STE.B3.VarCoef.cutOp ρ ε) (U γ))))
        ≤ C * Real.sqrt (∑ γ : κ,
              Work.Diff.STE.CSq (k - 1) (Work.Diff.STE.fourierCoeff (F γ)))
            * Real.sqrt (∑ γ : κ, Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (U γ))) := by
  classical
  -- the `ε`-free order certificate of `M_ψ` for each `γ`
  choose Cψ hCψ using fun γ : κ => mulOp_isOrd (ψ γ) (hψ γ) (hψp γ)
  -- the per-`γ` estimate, with a constant independent of `ε`
  have hper : ∀ γ : κ, ∃ Cγ : ℝ, 0 ≤ Cγ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ F U : (ι → ℝ) → ℂ, SmoothPer F → SmoothPer U →
      |Work.Diff.STE.L2re F (T γ (XOp (ψ γ) (cutOp ρ ε) U))|
        ≤ Cγ * Real.sqrt (Work.Diff.STE.CSq (k - 1) (Work.Diff.STE.fourierCoeff F))
            * Real.sqrt (Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff U)) := by
    intro γ
    -- the constant of `XOp (ψ γ) (cutOp ρ ε)`, independent of `ε`
    let Cx : ℤ → ℝ :=
      fun t => (fun s => Cψ γ (s - 0) * (fun _ => (1 : ℝ)) s) (t - 0) * Cψ γ t
    have hX : ∀ ε : ℝ, IsOrd 0 Cx (XOp (ψ γ) (cutOp ρ ε)) := by
      intro ε
      have h1 : IsOrd (0 + 0) (fun t => Cψ γ (t - 0) * (fun _ => (1 : ℝ)) t)
          (compOp (mulOp (ψ γ)) (cutOp ρ ε)) :=
        IsOrd.comp (T := mulOp (ψ γ)) (U := cutOp ρ ε) (hCψ γ) (cutOp_isOrd ρ hρ ε)
      have h2 : IsOrd ((0 + 0) + 0)
          (fun t => (fun s => Cψ γ (s - 0) * (fun _ => (1 : ℝ)) s) (t - 0) * Cψ γ t)
          (compOp (compOp (mulOp (ψ γ)) (cutOp ρ ε)) (mulOp (ψ γ))) :=
        IsOrd.comp (T := compOp (mulOp (ψ γ)) (cutOp ρ ε)) (U := mulOp (ψ γ)) h1 (hCψ γ)
      exact IsOrd.mono_d h2 (by omega)
    -- the composite `T γ ∘ XOp (ψ γ) (cutOp ρ ε)`, order `2k - 1`, constant independent of `ε`
    let Ct : ℤ → ℝ := fun t => Cfun (t - 0) * Cx t
    have hTcomp : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        IsOrd (2 * (k : ℤ) - 1) Ct (fun f => T γ (XOp (ψ γ) (cutOp ρ ε) f)) := by
      intro ε hε hε1
      have h := IsOrd.comp (T := T γ) (U := XOp (ψ γ) (cutOp ρ ε)) (hT γ) (hX ε)
      exact IsOrd.mono_d h (by omega)
    refine ⟨Real.sqrt (Ct k), Real.sqrt_nonneg _, fun ε hε hε1 F U hF hU => ?_⟩
    let W : (ι → ℝ) → ℂ := T γ (XOp (ψ γ) (cutOp ρ ε) U)
    have hW : SmoothPer W := (hTcomp ε hε hε1).pres U hU
    have hbnd := (hTcomp ε hε hε1).bound k U hU
    have hbnd' : Work.Diff.STE.B3.SymCalcStep8.CSqZ (-((k : ℤ) - 1))
        (Work.Diff.STE.fourierCoeff W)
        ≤ Ct k * Work.Diff.STE.B3.SymCalcStep8.CSqZ (k : ℤ)
            (Work.Diff.STE.fourierCoeff U) := by
      rw [show (k : ℤ) - (2 * (k : ℤ) - 1) = -((k : ℤ) - 1) from by ring] at hbnd
      exact hbnd
    have hcs := Work.Diff.STE.B3.SymCalcStep8.L2re_le_sqrt_CSqZ ((k : ℤ) - 1) F W
      hF.1 hF.2 hW.1 hW.2
    have hFc : Work.Diff.STE.B3.SymCalcStep8.CSqZ ((k : ℤ) - 1)
        (Work.Diff.STE.fourierCoeff F)
        = Work.Diff.STE.CSq (k - 1) (Work.Diff.STE.fourierCoeff F) := by
      rw [show (k : ℤ) - 1 = ((k - 1 : ℕ) : ℤ) from by omega]
      exact Work.Diff.STE.B3.SymCalcStep8.CSqZ_natCast (k - 1) _
    have hUc : Work.Diff.STE.B3.SymCalcStep8.CSqZ (k : ℤ)
        (Work.Diff.STE.fourierCoeff U)
        = Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff U) :=
      Work.Diff.STE.B3.SymCalcStep8.CSqZ_natCast k _
    show |Work.Diff.STE.L2re F W| ≤ Real.sqrt (Ct k)
        * Real.sqrt (Work.Diff.STE.CSq (k - 1) (Work.Diff.STE.fourierCoeff F))
        * Real.sqrt (Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff U))
    calc |Work.Diff.STE.L2re F W|
        ≤ Real.sqrt (Work.Diff.STE.B3.SymCalcStep8.CSqZ ((k : ℤ) - 1)
              (Work.Diff.STE.fourierCoeff F))
            * Real.sqrt (Work.Diff.STE.B3.SymCalcStep8.CSqZ (-((k : ℤ) - 1))
              (Work.Diff.STE.fourierCoeff W)) := hcs
      _ = Real.sqrt (Work.Diff.STE.CSq (k - 1) (Work.Diff.STE.fourierCoeff F))
            * Real.sqrt (Work.Diff.STE.B3.SymCalcStep8.CSqZ (-((k : ℤ) - 1))
              (Work.Diff.STE.fourierCoeff W)) := by rw [hFc]
      _ ≤ Real.sqrt (Work.Diff.STE.CSq (k - 1) (Work.Diff.STE.fourierCoeff F))
            * (Real.sqrt (Ct k)
              * Real.sqrt (Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff U))) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
          calc Real.sqrt (Work.Diff.STE.B3.SymCalcStep8.CSqZ (-((k : ℤ) - 1))
                  (Work.Diff.STE.fourierCoeff W))
              ≤ Real.sqrt (Ct k * Work.Diff.STE.B3.SymCalcStep8.CSqZ (k : ℤ)
                  (Work.Diff.STE.fourierCoeff U)) := Real.sqrt_le_sqrt hbnd'
            _ = Real.sqrt (Ct k) * Real.sqrt (Work.Diff.STE.B3.SymCalcStep8.CSqZ (k : ℤ)
                  (Work.Diff.STE.fourierCoeff U)) :=
                Real.sqrt_mul ((hTcomp ε hε hε1).nonneg k) _
            _ = Real.sqrt (Ct k) * Real.sqrt (Work.Diff.STE.CSq k
                  (Work.Diff.STE.fourierCoeff U)) := by rw [hUc]
      _ = Real.sqrt (Ct k) * Real.sqrt (Work.Diff.STE.CSq (k - 1)
              (Work.Diff.STE.fourierCoeff F))
            * Real.sqrt (Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff U)) := by ring
  choose Cγ hCγ using hper
  refine ⟨∑ γ : κ, Cγ γ, Finset.sum_nonneg (fun γ _ => (hCγ γ).1),
    fun ε hε hε1 F U hF hU => ?_⟩
  exact abs_sum_le_sum_mul_sqrt
    (fun γ => Work.Diff.STE.L2re (F γ) (T γ (XOp (ψ γ) (cutOp ρ ε) (U γ))))
    (fun γ => Cγ γ)
    (fun γ => Work.Diff.STE.CSq (k - 1) (Work.Diff.STE.fourierCoeff (F γ)))
    (fun γ => Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (U γ)))
    (fun γ => (hCγ γ).1)
    (fun γ => Work.Diff.STE.CSq_nonneg (k - 1) _)
    (fun γ => Work.Diff.STE.CSq_nonneg k _)
    (fun γ => (hCγ γ).2 ε hε hε1 (F γ) (U γ) (hF γ) (hU γ))

end Work.Diff.STE.B3.VarCoef
