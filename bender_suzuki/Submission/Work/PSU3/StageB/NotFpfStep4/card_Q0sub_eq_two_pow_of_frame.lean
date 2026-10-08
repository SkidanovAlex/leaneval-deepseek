/-
# `|Q₀sub H| = 2ⁿ` from a coarse frame

The cardinality statement used by Stage B: a `CoarseFrame` on `(H, Q, t)` already determines
`|⟨Inv H⟩| = 2ⁿ`, because the frame identifies `Q₀ = ⟨Inv H⟩` with the fixed field of the
`2ⁿ`-power Frobenius `σE` on `E n = GF(2^{2n})`, which has `2ⁿ` elements
(`Work.PSU3.GaloisField.fixedField_card`).

The one subtlety is the exponent `n = 0`: `fixedField_card` needs `1 ≤ n`, and the frame's
`bar`/`zc`/`κ` data alone would be consistent with `n = 0` were it not for the unit group
`(E 0)ˣ`: the frame carries `ζ ≠ 1` in `KW` and an *injective* `κ : KW →* (E n)ˣ`, so `(E n)ˣ`
is nontrivial, whereas `(GaloisField 2 0)ˣ` is trivial (that field is `𝔽₂`).  Hence `n ≠ 0`.
-/
import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.StageB.NotFpfAux
import Submission.Work.PSU3.GaloisField.fixedField_card
import Submission.Work.PSU3.GaloisField.card_zero

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.style.haveILetI false

open Polynomial

namespace Work.PSU3.StageB.NotFpfStep4

/-! ## The field `𝔽₂ = GaloisField 2 0` -/

/-- The unit group of `𝔽₂ = GaloisField 2 0` is trivial: a finite field's units are its
nonzero elements, and `𝔽₂` has `2` of them (`Work.PSU3.GaloisField.card_zero`). -/
theorem subsingleton_units_galoisField_two_zero : Subsingleton ((GaloisField 2 0)ˣ) := by
  classical
  haveI : Fintype (GaloisField 2 0) := Fintype.ofFinite _
  have hunits : Fintype.card ((GaloisField 2 0)ˣ) = 1 := by
    rw [Fintype.card_units, ← Nat.card_eq_fintype_card, Work.PSU3.GaloisField.card_zero]
  rw [← Nat.card_eq_fintype_card] at hunits
  exact Finite.card_le_one_iff_subsingleton.mp (le_of_eq hunits)

/-! ## The exponent of a coarse frame is nonzero -/

/-- **A coarse frame has `n ≠ 0`.**  The frame contains `ζ ≠ 1` in `KW` and an injective
`κ : KW →* (E n)ˣ`; for `n = 0` the target `(𝔽₂)ˣ` is trivial. -/
theorem coarseFrame_ne_zero {G : Type} [Group G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (fr : Work.PSU3.CoarseFrame H Q t n) : n ≠ 0 := by
  haveI := subsingleton_units_galoisField_two_zero
  intro hn
  subst hn
  refine fr.ζ_ne_one (fr.κ_injective ?_)
  rw [map_one]
  exact Subsingleton.elim _ _

/-! ## The cardinality of `fr.Q0` -/

/-- The frame's `Q₀` is in bijection with the fixed field of `σE` in `E n`: `zc` is additive
and, on the fixed field, injective with image exactly `Q₀`. -/
theorem card_Q0_eq_card_fixedField {G : Type} [Group G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (fr : Work.PSU3.CoarseFrame H Q t n) :
    Nat.card fr.Q0 = Nat.card {y : Work.PSU3.E n // σE y = y} :=
  (Nat.card_congr (Equiv.ofBijective
    (fun y : {y : Work.PSU3.E n // σE y = y} =>
      (⟨fr.zc y, fr.zc_mem y y.2⟩ : fr.Q0))
    ⟨fun a b h => Subtype.ext (fr.zc_inj a b a.2 b.2 (Subtype.ext_iff.mp h)),
     fun z => by
      obtain ⟨y, hy, hzy⟩ := fr.zc_surj z z.2
      exact ⟨⟨y, hy⟩, Subtype.ext hzy⟩⟩)).symm

/-- The fixed field of the `2ⁿ`-power Frobenius on `E n = GF(2^{2n})` has `2ⁿ` elements. -/
theorem card_fixedField_E {n : ℕ} (hn : 1 ≤ n) :
    Nat.card {y : Work.PSU3.E n // σE y = y} = 2 ^ n := by
  rw [← Work.PSU3.GaloisField.fixedField_card n hn]
  rfl

/-! ## The target -/

theorem card_Q0sub_eq_two_pow_of_frame {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    {n : ℕ} (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n) :
    Nat.card (Work.ThmF.Q0sub H) = 2 ^ n := by
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (coarseFrame_ne_zero fr)
  rw [← Work.PSU3.StageB.frameQ0_eq_Q0sub hS fr]
  rw [card_Q0_eq_card_fixedField fr]
  exact card_fixedField_E hn

end Work.PSU3.StageB.NotFpfStep4
