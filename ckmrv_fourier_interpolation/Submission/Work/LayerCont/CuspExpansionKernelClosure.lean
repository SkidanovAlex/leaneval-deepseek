import Mathlib
import Submission.Work.LayerCont.GapBoundKaxis
import Submission.Work.LayerCont.AexpLow
import Submission.Work.Asymptotics.cuspExpansionKernel

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section

namespace Work.LayerCont

open UpperHalfPlane MeasureTheory Filter
open scoped Topology

/-- **The guarded cusp expansion on a compact set, uniform in `τ`.**

On a compact `K`, for `t ≥ 1` and `A ≤ |t - τ.im|` (`A > 0`), with cleanliness
`j τ ≠ j (i t)` on the whole guard region, the difference between the CKMRV kernel along the
contour and its non-decaying cusp part `Aexp (Gcusp ℓ d)` decays like `e^{-πt}` up to a
polynomial factor, with constants uniform over `K`.

This is the closure version of `Work.Asymptotics.cuspExpansionKernel` (which requires
`K ⊆ 𝒟`): the small-`t` half there is `Work.HFN.CuspExp.smallT_bound` on a compact `K ⊆ 𝒟`,
here it is `Work.LayerCont.GapBoundKaxis` (pure compactness + cleanliness + guard) plus the
compactness bound `Work.LayerCont.Aexp_compact_bound` for the `Aexp` half.  The tail half
`Work.Asymptotics.kernel_axis_bound` needs only compactness, so its constants are already
uniform.

The statement is exactly the *dominator* hypothesis of `Work.LayerCont.TruncHolomorphy`: on the
retained set `E = Ici 1 \ Ioo (t₀-A) (t₀+A)` and `τ` in a ball of radius `≤ A/2` around
`1 + i t₀` the guard `A/2 ≤ |t - τ.im|` holds, and `hcleanAxis` supplies the cleanliness. -/
theorem CuspExpansionKernelClosure (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {K : Set UpperHalfPlane} (hK : IsCompact K) {A : ℝ}
    (hclean : ∀ (τ : UpperHalfPlane), τ ∈ K → ∀ (t : ℝ) (ht : 0 < t), 1 ≤ t →
      A ≤ |t - τ.im| →
      Work.Kernels.jInvariantFun τ
        ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    ∃ C M T₀ : ℝ, 0 < C ∧ 0 ≤ M ∧ 0 ≤ T₀ ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      τ ∈ K → 1 ≤ t → A ≤ |t - τ.im| →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖
          ≤ C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀))) := by
  obtain ⟨Ck, Mk, Tk, hCk, hMk, hTk, hkb⟩ := Work.Asymptotics.kernel_axis_bound ℓ d hd hK
  set T : ℝ := max Tk 1 with hTdef
  have hTpos : 0 < T := lt_max_of_lt_left hTk
  have hTk_le : Tk ≤ T := le_max_left _ _
  -- the small-`t` half on the compact region
  obtain ⟨Cg, hCg, hgb⟩ := GapBoundKaxis ℓ d hd hK (T := T) (A := A)
    (fun τ hτ t h1 _ h3 => by
      rw [axisPt_eq_imagAxis h1]
      exact hclean τ hτ t (lt_of_lt_of_le zero_lt_one h1) h1 h3)
  -- the `Aexp` half on the same compact region
  obtain ⟨Cae, hCae, hae⟩ := Aexp_compact_bound ℓ d hd hK (T := T)
  refine ⟨max (Cg + Cae) (Ck * Real.exp (-(Real.pi * T))) + 1, max Mk 0, T,
    by positivity, le_max_right _ _, hTpos.le, fun τ t hτ ht1 hsep => ?_⟩
  rcases le_or_gt t T with htT | htT
  · -- the compact piece of the contour
    have hKb : ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ Cg :=
      hgb τ t hτ ht1 htT hsep
    have hAb : ‖Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖ ≤ Cae :=
      hae τ hτ t (by rw [abs_of_nonneg (by linarith)]; exact htT)
    have hsum : ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖ ≤ Cg + Cae :=
      le_trans (norm_sub_le _ _) (add_le_add hKb hAb)
    have hw : (1 : ℝ) ≤ 1 + t := by linarith
    have h1' : (1 : ℝ) ≤ (1 + t) ^ max Mk 0 := Real.one_le_rpow hw (le_max_right _ _)
    have h2' : (1 : ℝ) ≤ Real.exp (-(Real.pi * (t - T))) := by
      rw [Real.one_le_exp_iff]
      nlinarith [Real.pi_pos]
    have hA0 : (0 : ℝ) ≤ (1 + t) ^ max Mk 0 := Real.rpow_nonneg (by linarith) _
    have hB0 : (0 : ℝ) ≤ Real.exp (-(Real.pi * (t - T))) := (Real.exp_pos _).le
    have hCC : Cg + Cae ≤ max (Cg + Cae) (Ck * Real.exp (-(Real.pi * T))) + 1 := by
      linarith [le_max_left (Cg + Cae) (Ck * Real.exp (-(Real.pi * T)))]
    have hone : (1 : ℝ) ≤ (1 + t) ^ max Mk 0 * Real.exp (-(Real.pi * (t - T))) := by
      nlinarith [h1', h2', hA0, hB0]
    refine le_trans hsum ?_
    calc Cg + Cae ≤ (max (Cg + Cae) (Ck * Real.exp (-(Real.pi * T))) + 1) * 1 := by
          rw [mul_one]; exact hCC
      _ ≤ (max (Cg + Cae) (Ck * Real.exp (-(Real.pi * T))) + 1)
            * ((1 + t) ^ max Mk 0 * Real.exp (-(Real.pi * (t - T)))) :=
          mul_le_mul_of_nonneg_left hone (by positivity)
      _ = (max (Cg + Cae) (Ck * Real.exp (-(Real.pi * T))) + 1) * (1 + t) ^ max Mk 0
            * Real.exp (-(Real.pi * (t - T))) := by ring
  · -- beyond the threshold of the cusp expansion
    have htT' : T ≤ t := le_of_lt htT
    have hb := hkb τ hτ t (le_trans hTk_le htT')
    have hw : (1 : ℝ) ≤ 1 + t := by linarith
    have hpM : (1 + t) ^ Mk ≤ (1 + t) ^ max Mk 0 :=
      Real.rpow_le_rpow_of_exponent_le hw (le_max_left _ _)
    have hY : (0 : ℝ) ≤ Real.exp (-(Real.pi * (t - T))) := (Real.exp_pos _).le
    have hX : (0 : ℝ) ≤ (1 + t) ^ max Mk 0 := Real.rpow_nonneg (by linarith) _
    have hsplit : Real.exp (-(Real.pi * t))
        = Real.exp (-(Real.pi * T)) * Real.exp (-(Real.pi * (t - T))) := by
      rw [← Real.exp_add]; congr 1; ring
    have hCkC : Ck * Real.exp (-(Real.pi * T)) ≤
        max (Cg + Cae) (Ck * Real.exp (-(Real.pi * T))) + 1 := by
      linarith [le_max_right (Cg + Cae) (Ck * Real.exp (-(Real.pi * T)))]
    have step2 : Ck * (1 + t) ^ Mk * (Real.exp (-(Real.pi * T))
          * Real.exp (-(Real.pi * (t - T))))
        ≤ Ck * (1 + t) ^ max Mk 0 * (Real.exp (-(Real.pi * T))
          * Real.exp (-(Real.pi * (t - T)))) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpM hCk.le)
        (mul_nonneg (Real.exp_pos _).le hY)
    have step3 : Ck * (1 + t) ^ max Mk 0 * (Real.exp (-(Real.pi * T))
          * Real.exp (-(Real.pi * (t - T))))
        = (Ck * Real.exp (-(Real.pi * T))) * ((1 + t) ^ max Mk 0
          * Real.exp (-(Real.pi * (t - T)))) := by ring
    have step4 : (Ck * Real.exp (-(Real.pi * T))) * ((1 + t) ^ max Mk 0
          * Real.exp (-(Real.pi * (t - T))))
        ≤ (max (Cg + Cae) (Ck * Real.exp (-(Real.pi * T))) + 1) * ((1 + t) ^ max Mk 0
          * Real.exp (-(Real.pi * (t - T)))) :=
      mul_le_mul_of_nonneg_right hCkC (mul_nonneg hX hY)
    have step5 : (max (Cg + Cae) (Ck * Real.exp (-(Real.pi * T))) + 1) * ((1 + t) ^ max Mk 0
          * Real.exp (-(Real.pi * (t - T))))
        = (max (Cg + Cae) (Ck * Real.exp (-(Real.pi * T))) + 1) * (1 + t) ^ max Mk 0
          * Real.exp (-(Real.pi * (t - T))) := by ring
    refine le_trans hb ?_
    calc Ck * (1 + t) ^ Mk * Real.exp (-(Real.pi * t))
        = Ck * (1 + t) ^ Mk * (Real.exp (-(Real.pi * T))
            * Real.exp (-(Real.pi * (t - T)))) := by rw [hsplit]
      _ ≤ Ck * (1 + t) ^ max Mk 0 * (Real.exp (-(Real.pi * T))
            * Real.exp (-(Real.pi * (t - T)))) := step2
      _ = (Ck * Real.exp (-(Real.pi * T))) * ((1 + t) ^ max Mk 0
            * Real.exp (-(Real.pi * (t - T)))) := step3
      _ ≤ (max (Cg + Cae) (Ck * Real.exp (-(Real.pi * T))) + 1) * ((1 + t) ^ max Mk 0
            * Real.exp (-(Real.pi * (t - T)))) := step4
      _ = (max (Cg + Cae) (Ck * Real.exp (-(Real.pi * T))) + 1) * (1 + t) ^ max Mk 0
            * Real.exp (-(Real.pi * (t - T))) := step5

/-- **The guard-free cusp expansion on a compact set.**

If instead of a quantitative guard one knows the contour cleanliness `j τ ≠ j (i t)` for *every*
`t ≥ 1` (which is the form the trunc mirror supplies on the retained set `E = Ici 1 \ Ioo (t₀-A) (t₀+A)`),
then the guard can be dropped altogether (`A = 0` above, the guard `0 ≤ |t - τ.im|` being
automatic).  This is the dominator interface of `Work.LayerCont.TruncHolomorphy`. -/
theorem CuspExpansionKernelClosure0 (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {K : Set UpperHalfPlane} (hK : IsCompact K)
    (hclean : ∀ (τ : UpperHalfPlane), τ ∈ K → ∀ (t : ℝ) (ht : 0 < t), 1 ≤ t →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    ∃ C M T₀ : ℝ, 0 < C ∧ 0 ≤ M ∧ 0 ≤ T₀ ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      τ ∈ K → 1 ≤ t →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖
          ≤ C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀))) := by
  obtain ⟨C, M, T₀, hC, hM, hT, hb⟩ := CuspExpansionKernelClosure ℓ d hd hK (A := 0)
    (fun τ hτ t ht h1 _ => hclean τ hτ t ht h1)
  exact ⟨C, M, T₀, hC, hM, hT, fun τ t hτ h1 => hb τ t hτ h1 (abs_nonneg _)⟩

end Work.LayerCont
