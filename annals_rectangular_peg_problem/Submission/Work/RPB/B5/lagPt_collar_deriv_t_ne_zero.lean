import Mathlib
import Submission.Work.RPB.B5.lagData_imm_aux
import Submission.Work.RPB.B5.LagData
import Submission.Work.RPB.B5.Defs

namespace Work.RPB.B5

/-- On the collar range `x ≤ -√2` the attached level `sig x = x²/2 - 1` is nonnegative. -/
private lemma sig_nonneg_of_le_neg_sqrt_two {x : ℝ} (hx : x ≤ -Real.sqrt 2) : 0 ≤ sig x := by
  have hsq : (2 : ℝ) ≤ x ^ 2 := by
    have hx' : Real.sqrt 2 ≤ -x := by linarith [Real.sqrt_nonneg 2]
    have h := pow_le_pow_left₀ (Real.sqrt_nonneg 2) hx' 2
    rwa [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), neg_sq] at h
  simp only [sig]
  linarith

/-- **The collar half of `ℓ` is a graph over the collar coordinate `Γc`.**  For `x ≤ -√2` the
`t`-slice `s ↦ ℓ τ x s` is the collar point `levelPt (Γc τ (sig x) s) (sig x) (Ac τ (sig x) s)`,
whose *reduced coordinate* `uproj` is exactly `Γc τ (sig x) ·` (`Work.RPV.uproj_levelPt`).  Since
that slice has nonvanishing `t`-derivative (`LagData.hemb` at the nonnegative level `sig x`), the
chain rule through the smooth map `uproj` forces the slice itself to have nonvanishing derivative:
if `∂_t ℓ = 0` then `∂_t (uproj ∘ ℓ) = fderiv uproj (·) 0 = 0`.

Note that the phase `Ac` never needs to be differentiated: only the existence of the derivative of
the *level point* slice is used, and that comes from the global smoothness hypothesis `hsm`. -/
theorem lagPt_collar_deriv_t_ne_zero (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) (D : Work.RPB.B5.LagData CI a)
    (hsm : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ContDiff ℝ 1 (fun z : ℝ × ℝ => lagPt D.W D.Γc D.Ac D.rho τ z.1 z.2)) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ x : ℝ, x ≤ -Real.sqrt 2 → ∀ t : ℝ,
      deriv (fun s : ℝ => lagPt D.W D.Γc D.Ac D.rho τ x s) t ≠ 0 := by
  intro τ hτ x hx t
  have hσ : 0 ≤ sig x := sig_nonneg_of_le_neg_sqrt_two hx
  -- the `t`-slice of the family at `x ≤ -√2` is the collar point at level `sig x`
  have hfun : (fun s : ℝ => lagPt D.W D.Γc D.Ac D.rho τ x s)
      = fun s : ℝ => Work.RPV.levelPt (D.Γc τ (sig x) s) (sig x) (D.Ac τ (sig x) s) := by
    funext s
    rw [lagPt_collar D.W D.Γc D.Ac D.rho (τ := τ) (x := x) (t := s) hx]
    rfl
  rw [hfun]
  -- the slice is differentiable (from the global smoothness of `ℓ` on the slab)
  have hdiff : DifferentiableAt ℝ
      (fun s : ℝ => Work.RPV.levelPt (D.Γc τ (sig x) s) (sig x) (D.Ac τ (sig x) s)) t := by
    have h := differentiableAt_slice_snd (x := x) (t := t) ((hsm τ hτ).contDiffAt)
    rw [hfun] at h
    exact h
  -- the chain rule: `uproj` of the slice is `Γc τ (sig x) ·`
  have hchain : deriv (fun s : ℝ => Work.RPV.uproj
        (Work.RPV.levelPt (D.Γc τ (sig x) s) (sig x) (D.Ac τ (sig x) s))) t
      = (fderiv ℝ Work.RPV.uproj
          (Work.RPV.levelPt (D.Γc τ (sig x) t) (sig x) (D.Ac τ (sig x) t)))
        (deriv (fun s : ℝ => Work.RPV.levelPt (D.Γc τ (sig x) s) (sig x)
          (D.Ac τ (sig x) s)) t) :=
    ((differentiableAt_uproj _).hasFDerivAt.comp_hasDerivAt t hdiff.hasDerivAt).deriv
  have huprojEq : (fun s : ℝ => Work.RPV.uproj
        (Work.RPV.levelPt (D.Γc τ (sig x) s) (sig x) (D.Ac τ (sig x) s)))
      = fun s : ℝ => D.Γc τ (sig x) s := by
    funext s
    exact Work.RPV.uproj_levelPt _ _ _
  have hG : deriv (fun s : ℝ => D.Γc τ (sig x) s) t
      = (fderiv ℝ Work.RPV.uproj
          (Work.RPV.levelPt (D.Γc τ (sig x) t) (sig x) (D.Ac τ (sig x) t)))
        (deriv (fun s : ℝ => Work.RPV.levelPt (D.Γc τ (sig x) s) (sig x)
          (D.Ac τ (sig x) s)) t) := by
    rw [← huprojEq]
    exact hchain
  intro hzero
  exact (D.hemb τ hτ (sig x) hσ).1 t (by rw [hG, hzero]; simp)

end Work.RPB.B5
