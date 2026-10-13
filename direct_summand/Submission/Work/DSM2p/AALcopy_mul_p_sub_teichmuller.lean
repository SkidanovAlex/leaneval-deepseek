-- Redirected copy of `Submission.Work.DSM2p.mul_p_sub_teichmuller` (imports re-pointed to the `AALvaln` vocabulary layer so that
-- `area_AAL_proved.lean` can import the result without an import cycle).  The original
-- file is untouched; this copy is generated mechanically.
import Mathlib
import Submission.Work.DSM2p.AALcopy_DigLeDefs

namespace Work.DSM2p

/-- **Division by `p`, up to the Teichmüller lift of the constant term.**

For `Λ = PreTilt R p` (perfect of characteristic `p`) and `z : 𝕎 Λ`, the Witt vector
`p * (z₁^{1/p}, z₂^{1/p}, …)` — where `zⱼ^{1/p} = (frobeniusEquiv Λ p).symm zⱼ` is the `p`-th root of
the `j`-th Witt coordinate of `z` — equals `z - [z₀]`.

This is the algebraic heart of the "shift" step: writing `V` for `verschiebung` and `F` for
`frobenius`, the Teichmüller expansion `z = ∑ⱼ [zⱼ^♭] p^j` shows that `z - [z₀] = V(z.shift 1)`
(only the 0th coordinate is affected by subtracting the constant Teichmüller lift), while
`p * y = V(F y)`, and `F y = z.shift 1` precisely because `y` was chosen as the Frobenius-inverse
shift of `z`. -/
theorem mul_p_sub_teichmuller {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R]
    [Fact (¬ IsUnit (p : R))] [IsAdicComplete (Ideal.span {(p : R)}) R]
    (z : WittVector p (PreTilt R p)) :
    (p : WittVector p (PreTilt R p)) *
        (WittVector.mk p (fun j => (frobeniusEquiv (PreTilt R p) p).symm (z.coeff (j + 1))))
      = z - WittVector.teichmuller p (z.coeff 0) := by
  set Y : WittVector p (PreTilt R p) :=
    WittVector.mk p (fun j => (frobeniusEquiv (PreTilt R p) p).symm (z.coeff (j + 1))) with hY
  -- `z = [z₀] + V (z.shift 1)`: subtracting the constant Teichmüller lift only changes the
  -- 0th coordinate, and `V (z.shift 1)` has coordinates `(0, z₁, z₂, …)`.
  have hdecomp : z = WittVector.teichmuller p (z.coeff 0) + WittVector.verschiebung (z.shift 1) := by
    refine WittVector.ext fun m => ?_
    have hdisj : ∀ n, (WittVector.teichmuller p (z.coeff 0)).coeff n = 0 ∨
        (WittVector.verschiebung (z.shift 1)).coeff n = 0 := by
      intro n
      rcases n with _ | k
      · exact Or.inr (WittVector.verschiebung_coeff_zero _)
      · exact Or.inl (WittVector.teichmuller_coeff_pos p (z.coeff 0) (k + 1) (Nat.succ_pos k))
    rcases m with _ | k
    · rw [WittVector.coeff_add_of_disjoint 0 _ _ hdisj, WittVector.teichmuller_coeff_zero,
        WittVector.verschiebung_coeff_zero, add_zero]
    · rw [WittVector.coeff_add_of_disjoint (k + 1) _ _ hdisj,
        WittVector.teichmuller_coeff_pos p (z.coeff 0) (k + 1) (Nat.succ_pos k),
        WittVector.verschiebung_coeff_succ, WittVector.shift_coeff, zero_add, Nat.one_add]
  -- `F Y = z.shift 1`: both have `k`-th coordinate `z_{k+1}`, the Frobenius twist being undone
  -- by the `p`-th root used to define `Y`.
  have hYfrob : WittVector.frobenius Y = z.shift 1 := by
    refine WittVector.ext fun k => ?_
    rw [WittVector.coeff_frobenius_charP, WittVector.shift_coeff]
    rw [hY, WittVector.coeff_mk, frobeniusEquiv_symm_apply_pow, Nat.one_add]
  -- `p * Y = Y * p = V (F Y) = V (z.shift 1) = z - [z₀]`.
  calc (p : WittVector p (PreTilt R p)) * Y
      = Y * (p : WittVector p (PreTilt R p)) := mul_comm _ _
    _ = WittVector.verschiebung (WittVector.frobenius Y) :=
        (WittVector.verschiebung_frobenius Y).symm
    _ = WittVector.verschiebung (z.shift 1) := by rw [hYfrob]
    _ = z - WittVector.teichmuller p (z.coeff 0) := ((sub_eq_iff_eq_add').mpr hdecomp).symm

end Work.DSM2p
