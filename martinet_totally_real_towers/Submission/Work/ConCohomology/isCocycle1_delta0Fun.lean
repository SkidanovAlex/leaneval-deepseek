/-
Copyright: the martinet_totally_real_towers team.

# The degree `0 → 1` connecting cochain is a `1`-cocycle

Let `0 → A → B → C → 0` be a short exact sequence of `G`-modules (`S : CoeffSES G A B C`), and
let `c ∈ C` be `G`-invariant.  The raw connecting cochain of degree `0 → 1` attached to `c` is

  `S.delta0Fun c σ = S.invFun (σ • S.sect c - S.sect c)`,

where `sect` is a set-theoretic section of the projection `g` and `invFun` a set-theoretic inverse
of the inclusion `f` on the image of `f`.  The point of the present lemma is that this *raw*
cochain is already a genuine crossed homomorphism `G → A`:

  `S.delta0Fun c (σ * τ) = S.delta0Fun c σ + σ • S.delta0Fun c τ`.

The reason is that the two sides have the same `f`-image and `f` is injective: the argument of the
`invFun` on the left is `(σ * τ) • sect c - sect c`, while the `f`-image of the right hand side is
`(σ • sect c - sect c) + σ • (τ • sect c - sect c)`, and these agree by `mul_smul`.  The
hypothesis that `c` is invariant is used exactly to know that the elements `σ • sect c - sect c`
really do lie in the image of `f` (their `g`-image is `σ • c - c = 0`).
-/

import Mathlib
import Submission.Work.ConCohomology.Setup

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.ConCohomology

open Function

variable {G : Type*} [Group G] {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
  [AddCommGroup C] [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]

/-- `invFun` is a section of `f` on the image of `f`: if `b = f a` for some `a` then
`f (S.invFun b) = b`. -/
lemma f_invFun_eq_self (S : CoeffSES G A B C) {b : B} (h : ∃ a : A, S.f a = b) :
    S.f (S.invFun b) = b := by
  have h' : S.invFun b = Classical.choose h := by
    rw [CoeffSES.invFun_eq]
    exact dite_eq_left h
  rw [h', Classical.choose_spec h]

/-- `invFun` is a left inverse of `f`: if `S.f a = b` then `S.invFun b = a`. -/
lemma invFun_eq_of_apply_eq (S : CoeffSES G A B C) {a : A} {b : B} (h : S.f a = b) :
    S.invFun b = a :=
  S.injective_f (by rw [f_invFun_eq_self S ⟨a, h⟩, h])

/-- Exactness at `B`: an element with vanishing `g`-image lies in the image of `f`. -/
lemma exists_f_eq_of_g_eq_zero (S : CoeffSES G A B C) {b : B} (h : S.g b = 0) :
    ∃ a : A, S.f a = b := (S.exact b).mp h

lemma isCocycle1_delta0Fun {G : Type*} [Group G] {A B C : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [DistribMulAction G A] [DistribMulAction G B]
    [DistribMulAction G C] (S : CoeffSES G A B C) (c : C) (hc : ∀ σ : G, σ • c = c) :
    IsCocycle1 (S.delta0Fun c) := by
  intro σ τ
  show S.invFun ((σ * τ) • S.sect c - S.sect c) =
    S.invFun (σ • S.sect c - S.sect c) + σ • S.invFun (τ • S.sect c - S.sect c)
  have hX : ∃ a : A, S.f a = σ • S.sect c - S.sect c := by
    apply exists_f_eq_of_g_eq_zero
    rw [EqHom.map_sub, EqHom.map_smul, CoeffSES.g_sect, hc σ, sub_self]
  have hY : ∃ a : A, S.f a = τ • S.sect c - S.sect c := by
    apply exists_f_eq_of_g_eq_zero
    rw [EqHom.map_sub, EqHom.map_smul, CoeffSES.g_sect, hc τ, sub_self]
  exact invFun_eq_of_apply_eq S (by
    rw [EqHom.map_add, EqHom.map_smul, f_invFun_eq_self S hX, f_invFun_eq_self S hY,
      smul_sub, mul_smul]
    abel)

end Work.ConCohomology
