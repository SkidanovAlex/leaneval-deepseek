import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.CoreResiduals.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals

/-- **The delivered profile/modulation interface forces `T = 2`.**  Two bounds meet:

* `T ≤ 2`: at `t = 0`, `hlam_low` gives `T/2 ≤ λ̄(0) = 1`;
* `T ≥ 2`: the rate bound (`hlamd` with `hK12`, i.e. `|λ̄'| ≤ 1/2`), the normalisation `λ̄(0) = 1`
  and the MVT give `λ̄(t) ≥ 1 - t/2` for `t ∈ [0,T)`; combined with `hlam_le`
  (`λ̄(t) ≤ 2(T-t)`), `1 - t/2 ≤ 2(T-t)`, i.e. `1 + 3t/2 ≤ 2T` for all `t < T`, which at
  `t → T⁻` gives `T ≥ 2`.

So every `ProfileData α` has blow-up time exactly `2`, the delivered inhabitant (`T = 2`,
`λ̄(t) = 1 - t/2`) saturating both bounds.  In particular the paper's own normalisation
(`T* = 1`, `λ̄(t) = 1-t`, rate `κ = 1`) is *not* admissible, since the interface allows only rates
`|λ̄'| ≤ 1/2`. -/
theorem ProfileData_T_eq_two {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) :
    P.T = 2 := by
  -- `T ≤ 2`: `hlam_low` at `t = 0` together with the normalisation `λ̄(0) = 1`.
  have hle2 : P.T ≤ 2 := by
    have hmem : (0 : ℝ) ∈ Set.Ico 0 P.T := ⟨le_refl 0, P.hT⟩
    have h := P.hlam_low 0 hmem
    rw [P.hlam0] at h
    linarith
  -- `T ≥ 2`: the MVT lower bound `λ̄(t) ≥ 1 - t/2` meets `hlam_le` `λ̄(t) ≤ 2(T-t)`.
  have hge2 : 2 ≤ P.T := by
    have H : ∀ t : ℝ, 0 ≤ t → t < P.T → 1 + 3 * t / 2 ≤ 2 * P.T := by
      intro t ht0 htT
      -- the segment `[0,t]` lies in the differentiability window `preWindow T = Ioo (-2) T`
      have hsub : Set.Icc (0 : ℝ) t ⊆ Work.ConstructionInstance.preWindow P.T := by
        intro x hx
        exact ⟨by linarith [hx.1], by linarith [hx.2, htT]⟩
      -- MVT: `|λ̄ t - λ̄ 0| ≤ (1/2)·|t - 0|`
      have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le
        (s := Set.Icc (0 : ℝ) t) (f := P.lam) (x := 0) (y := t) (C := (1 / 2 : ℝ))
        (fun x hx => (P.hlamdif x (hsub hx)).differentiableAt)
        (fun x hx => by
          rw [Real.norm_eq_abs]
          exact le_trans (P.hlamd x (hsub hx)) P.hK12)
        (convex_Icc (0 : ℝ) t) ⟨le_refl 0, ht0⟩ ⟨ht0, le_refl t⟩
      rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_zero, P.hlam0, abs_of_nonneg ht0] at hmvt
      -- hence `1 - t/2 ≤ λ̄ t`
      have hlow : 1 - t / 2 ≤ P.lam t := by
        have := (abs_le.mp hmvt).1
        linarith
      have hup := P.hlam_le t ⟨ht0, htT⟩
      linarith
    -- `1 + 3t/2 ≤ 2T` for every `t < T` gives `1 + 3T/2 ≤ 2T` in the limit `t → T⁻`
    have hineq : 1 + 3 * P.T / 2 ≤ 2 * P.T := by
      refine le_of_forall_pos_le_add (fun ε hε => ?_)
      set δ := min (P.T / 2) (ε / 4) with hδdef
      have hδpos : 0 < δ := lt_min (by linarith [P.hT]) (by linarith)
      have hδleε : δ ≤ ε / 4 := min_le_right _ _
      have ht0 : 0 ≤ P.T - δ := by linarith [min_le_left (P.T / 2) (ε / 4)]
      have htT : P.T - δ < P.T := by linarith
      have Ht := H (P.T - δ) ht0 htT
      have hδ : 3 * δ / 2 ≤ ε := by linarith
      linarith
    linarith
  linarith

end Work.CoreResiduals
