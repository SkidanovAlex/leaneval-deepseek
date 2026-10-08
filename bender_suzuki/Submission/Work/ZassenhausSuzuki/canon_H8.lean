import Mathlib
import Submission.Work.ZassenhausSuzuki.canon_aux
import Submission.Work.ZassenhausSuzuki.szTildeAux
import Submission.Work.PSU3.RankOne.canon_mul
import Submission.Work.PSU3.RankOne.canon_mul_ne_one

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The `h`-product formula (`canon_H8`)

The `D`-component of the uniqueness computation of `canon_mul` (i.e. exactly the proof of
`canon_H7`, which extracts the `Q`-component `f(x₁x₂)`): in the canonical structure
`t x t = g x · h x · t · f x` one has

  `h(x₁x₂) = h(x₁) · h(f(x₁)·g(x₂)) · h(x₂)`   (`x₁, x₂, x₁x₂ ≠ 1`).

This is the engine for the two group identities used in the Baumeister–Grüninger 5.14
computation (BG 5.11 — `mu_mul_eq_mu_tilde` — and BG 3.1 (l) — `mu_conj_mul_inv`), see
`Submission/Work/ZassenhausSuzuki/TitsDesign.lean` (`canon_H8`), where it appears with this
proof, and `NOTES_szMuCenter.md`.  It is a `D`-component of the same
`Work.PSU3.RankOne.canon_mul` decomposition that gives `canon_H7`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausSuzuki

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-- **`canon_H8`**: `h(x₁x₂) = h(x₁) · h(f(x₁)·g(x₂)) · h(x₂)`. -/
theorem canon_H8 (hsplit : IsSplitRankOne H Q t) (hzass : IsZassenhaus H) (h2 : IsPGroup 2 Q)
    (C : Work.ZassenhausPSL2.Canon H Q t) (x₁ x₂ : Q) (hx₁ : (x₁ : G) ≠ 1) (hx₂ : (x₂ : G) ≠ 1)
    (hx₁₂ : ((x₁ * x₂ : Q) : G) ≠ 1) :
    hG C (x₁ * x₂) = hG C x₁ * hG C (C.f x₁ * C.g x₂) * hG C x₂ := by
  have hcx := canon3_of_C hsplit C hx₁
  have hcy := canon3_of_C hsplit C hx₂
  have hz_ne : ((C.f x₁ * C.g x₂ : Q) : G) ≠ 1 :=
    Work.PSU3.RankOne.canon_mul_ne_one hsplit x₁.2 hx₁ x₂.2 hx₂ hcx hcy hx₁₂
  have hcz := canon3_of_C hsplit C hz_ne
  obtain ⟨hg', hd', hy', heq⟩ := Work.PSU3.RankOne.canon_mul hsplit hcx hcy hcz
  have hres := canon3_eq_C hsplit C (y := x₁ * x₂) hx₁₂ (g := ⟨_, hg'⟩) (d := ⟨_, hd'⟩)
    (z := ⟨_, hy'⟩) heq
  exact congrArg Subtype.val hres.2.2

end Work.ZassenhausSuzuki
