import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Submission.Work.BoseC3QAll.Est1.Algebra
import Submission.Work.BoseC3QAll.completing_square
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseC3QAll.Est1.compSquare_sum` — the summed completing-the-square

This is the **completing-the-square step** of the proof of FS `eq:EstimateQ3Tilde1`
(the shift decomposition `Q3oneT = Σ_{k∈P_H}(b_k†Y_k + Y_k†b_k) + R1` of
`Est1.Skeleton`): summing the pointwise inequality of
`Work.BoseC3QAll.completing_square` over the high-momentum region `P_H` and using
the adjointness of `b_k` and of the shift `Y_k = Est1.shift F T E k` in the Fock
form `bp` gives

`- Σ_k c_k⟨b_k†b_k⟩ - Σ_k c_k⁻¹⟨Y_k†Y_k⟩ ≤ ⟨Σ_k (b_k†Y_k + Y_k†b_k)⟩`,

with `c_k = Est1.cD E k > 0`.

The two ingredients are

* `bp_shiftDag_left` — the adjointness `⟨Y_k†f, g⟩ = ⟨f, Y_k g⟩` of the shift
  (`shiftDag`, the written-out adjoint of `shift`); it follows from the
  adjointness of `Ã_s` (`bp_AtilDag_left`) and of `b_{s-k}`;
* `qw_comp_add` / `qw_sum_comp` — the two cross terms `⟨b_k†Y_k⟩` and
  `⟨Y_k†b_k⟩` of the sum both reduce to `⟨b_kΦ, Y_kΦ⟩`, so the right-hand side
  is `Σ_k 2⟨b_kΦ, Y_kΦ⟩`, exactly the cross term of the completed square.

The per-`k` inequality is then `completing_square` at `c = c_k`, and the sum
over `k ∈ P_H` is `Finset.sum_le_sum`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseC3QAll

namespace Est1

open Work.BoseB7

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
variable {F : FockData Mode}

/-- `Ã_s†` is the adjoint of `Ã_s` for the Fock form: `⟨Ã_s†f, g⟩ = ⟨f, Ã_s g⟩`. -/
theorem bp_AtilDag_left (T : TildeData F) (E : Q3Env Mode) (s k : Mode) (f g : F.H) :
    F.bp (AtilDag F T E s k f) g = F.bp f (Atil F T E s k g) := by
  simp only [Atil, AtilDag, LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul,
    smul_eq_mul, bp_taDag_left, bp_ta_left]

/-- The adjointness of the shift in the Fock form: `⟨Y_k†f, g⟩ = ⟨f, Y_k g⟩`.

Since `Y_k = (z/ℓ³)Σ_s γ_{sk}b_{s-k}†Ã_s`, its adjoint is
`(z/ℓ³)Σ_s γ_{sk}Ã_s†b_{s-k}`: this is precisely `Est1.shiftDag`. -/
theorem bp_shiftDag_left (T : TildeData F) (E : Q3Env Mode) (k : Mode) (f g : F.H) :
    F.bp (shiftDag F T E k f) g = F.bp f (shift F T E k g) := by
  simp only [shiftDag, shift, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, map_sum, map_smul, smul_eq_mul,
    bp_bOp_left, bp_AtilDag_left]

/-- The adjointness of the shift, second slot: `⟨Y_k f, g⟩ = ⟨f, Y_k† g⟩`. -/
theorem bp_shift_left (T : TildeData F) (E : Q3Env Mode) (k : Mode) (f g : F.H) :
    F.bp (shift F T E k f) g = F.bp f (shiftDag F T E k g) := by
  rw [F.bp_symm (shift F T E k f) g, ← F.bp_symm (shiftDag F T E k g) f, bp_shiftDag_left]

/-- Both cross terms of `b_k†Y_k + Y_k†b_k` reduce to the same Fock form
`⟨b_kΦ, Y_kΦ⟩`, so the whole word contributes `2⟨b_kΦ, Y_kΦ⟩`. -/
theorem qw_comp_add (T : TildeData F) (E : Q3Env Mode) (k : Mode) (Φ : F.H) :
    F.qw Φ (F.bOpDag E.alpha k ∘ₗ shift F T E k + shiftDag F T E k ∘ₗ F.bOp E.alpha k)
      = 2 * F.bp (F.bOp E.alpha k Φ) (shift F T E k Φ) := by
  rw [FockData.qw]
  simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add,
    bp_bOpDag_left, bp_shiftDag_left]
  rw [F.bp_symm (shift F T E k Φ) (F.bOp E.alpha k Φ)]
  ring

/-- `qw` of the sum over `P_H` of the shift words: the linearity of `bp` in the
operator plus `qw_comp_add`. -/
theorem qw_sum_comp (T : TildeData F) (E : Q3Env Mode) (Φ : F.H) :
    F.qw Φ (∑ k ∈ F.PHset E, (F.bOpDag E.alpha k ∘ₗ shift F T E k
        + shiftDag F T E k ∘ₗ F.bOp E.alpha k))
      = ∑ k ∈ F.PHset E, 2 * F.bp (F.bOp E.alpha k Φ) (shift F T E k Φ) := by
  rw [FockData.qw]
  rw [LinearMap.sum_apply, map_sum, LinearMap.sum_apply]
  exact Finset.sum_congr rfl (fun k _ => qw_comp_add T E k Φ)

theorem compSquare_sum {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (T : Work.BoseC3QAll.TildeData F) (E : Work.BoseB7.Q3Env Mode)
    (hpos : ∀ k ∈ F.PHset E, 0 < Work.BoseC3QAll.Est1.cD E k) (Φ : F.H) :
    - (∑ k ∈ F.PHset E, Work.BoseC3QAll.Est1.cD E k *
          F.bp (F.bOp E.alpha k Φ) (F.bOp E.alpha k Φ))
        - (∑ k ∈ F.PHset E, (Work.BoseC3QAll.Est1.cD E k)⁻¹ *
          F.bp (Work.BoseC3QAll.Est1.shift F T E k Φ) (Work.BoseC3QAll.Est1.shift F T E k Φ))
      ≤ F.qw Φ (∑ k ∈ F.PHset E, (F.bOpDag E.alpha k ∘ₗ Work.BoseC3QAll.Est1.shift F T E k
          + Work.BoseC3QAll.Est1.shiftDag F T E k ∘ₗ F.bOp E.alpha k)) := by
  -- the right-hand side is `Σ_k 2⟨b_kΦ, Y_kΦ⟩`
  rw [qw_sum_comp T E Φ]
  -- the pointwise completing-the-square inequality
  have hterm : ∀ k ∈ F.PHset E,
      -(Work.BoseC3QAll.Est1.cD E k * F.bp (F.bOp E.alpha k Φ) (F.bOp E.alpha k Φ))
        - ((Work.BoseC3QAll.Est1.cD E k)⁻¹
            * F.bp (Work.BoseC3QAll.Est1.shift F T E k Φ) (Work.BoseC3QAll.Est1.shift F T E k Φ))
      ≤ 2 * F.bp (F.bOp E.alpha k Φ) (Work.BoseC3QAll.Est1.shift F T E k Φ) := by
    intro k hk
    have hc : 0 < Work.BoseC3QAll.Est1.cD E k := hpos k hk
    have hcs := completing_square F (F.bOp E.alpha k) (Work.BoseC3QAll.Est1.shift F T E k)
      (Work.BoseC3QAll.Est1.cD E k) hc Φ
    linarith
  -- distribute the two sums over the left-hand side and sum the pointwise bound
  rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum hterm

end Est1

end Work.BoseC3QAll

end
