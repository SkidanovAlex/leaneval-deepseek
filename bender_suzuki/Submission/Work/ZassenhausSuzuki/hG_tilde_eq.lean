import Mathlib
import Submission.Work.ZassenhausSuzuki.szTildeAux
import Submission.Work.ZassenhausSuzuki.SzTildeDefs
import Submission.Work.ZassenhausSuzuki.canon_relations
import Submission.Work.ZassenhausSuzuki.hG_conj_gG_eq_tilde

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausSuzuki.hG_tilde_eq` (BG 3.1 (i))

`h(∼x) = h(x)`: the `D`-component `hG C x = (C.h x : D)` of the canonical form of `t x t` is
invariant under the Suzuki reflection `∼x = g ((g x)⁻¹)`.

Two of Peterfalvi's identities for the canonical maps `f, g, h` (workspace numbering) do the
work:

* the third part of (H4) — `h(f x) = h(x)⁻¹` — which is obtained from `Work.PSU3.canon_f`: the
  element `t (f x) t` has the canonical form with `Q`-part `(h x)⁻¹ (g x)⁻¹ (h x)`, `D`-part
  `(h x)⁻¹` and `Q`-part `x`, and uniqueness of the canonical form (`canon3_eq_C`) identifies
  the `D`-part;
* (H6a) `canon_H6`, `h(d x d⁻¹) = d⁻¹ d⁻¹ h(x)` for `d ∈ D` (the `D`-component of
  `Work.PSU3.RankOne.canon_conj`).

Indeed `tildeOf_eq` writes `∼x = (h x)⁻¹ · f(x) · h(x)` as an element of `Q`, i.e. `∼x` is the
`D`-conjugate (by `d := (h x)⁻¹`) of `f(x) ∈ Q#`; applying `canon_H6` and then (H4c) gives
`h(∼x) = d⁻¹ d⁻¹ h(f x) = (h x)(h x)(h x)⁻¹ = h(x)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausSuzuki

/-- **Peterfalvi (H4c)**: `h(f x) = h(x)⁻¹` for `x ∈ Q#`.

By `Work.PSU3.canon_f` applied to the canonical datum of `x`, the element `t (f x) t` has the
canonical form `((h x)⁻¹ (g x)⁻¹ (h x)) · ((h x)⁻¹) · t · x`, with the middle factor in
`D = twoPoint H t`; uniqueness of the canonical form (`canon3_eq_C`) identifies that middle
factor as `C.h (C.f x)`, i.e. `h(f x) = (h x)⁻¹`. -/
lemma hG_f {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (C : Work.ZassenhausPSL2.Canon H Q t) {x : Q} (hx : (x : G) ≠ 1) :
    hG C (C.f x) = (hG C x)⁻¹ := by
  obtain ⟨hg', hd', hy', heq⟩ := Work.PSU3.canon_f hsplit x.2 (canon3_of_C hsplit C hx)
  have hres := canon3_eq_C hsplit C (y := C.f x) (canon_f_ne_one hsplit C hx)
    (g := ⟨_, hg'⟩) (d := ⟨_, hd'⟩) (z := x) heq
  have hd : C.h (C.f x) = (⟨(C.h x : G)⁻¹, hd'⟩ : twoPoint H t) := hres.2.2
  show ((C.h (C.f x) : twoPoint H t) : G) = ((C.h x : twoPoint H t) : G)⁻¹
  rw [hd]

theorem hG_tilde_eq {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    (C : Work.ZassenhausPSL2.Canon H Q t) {x : Q} (hx : (x : G) ≠ 1) :
    Work.ZassenhausSuzuki.hG C (Work.ZassenhausSuzuki.tildeOf C x)
      = Work.ZassenhausSuzuki.hG C x := by
  have hfx : (C.f x : G) ≠ 1 := canon_f_ne_one hsplit C hx
  -- the `D`-element `d := (h x)⁻¹`, so that `∼x = d · f(x) · d⁻¹` as an element of `Q`
  obtain ⟨d, hdG⟩ : ∃ d : twoPoint H t, (d : G) = (hG C x)⁻¹ :=
    ⟨⟨(hG C x)⁻¹, (twoPoint H t).inv_mem (C.h x).2⟩, rfl⟩
  have hmem : (d : G) * (C.f x : G) * (d : G)⁻¹ ∈ Q := canon_D_conj_Q_mem hsplit d (C.f x)
  -- identify the `Q`-element `⟨d · f(x) · d⁻¹, _⟩` with the reflection `∼x`
  have hqeq : (⟨(d : G) * (C.f x : G) * (d : G)⁻¹, hmem⟩ : Q) = tildeOf C x := by
    apply Subtype.ext
    show (d : G) * (C.f x : G) * (d : G)⁻¹ = ((tildeOf C x : Q) : G)
    rw [tildeOf_eq hsplit hzass h2 C hx, hdG]
    group
  rw [← hqeq]
  have h6 : hG C ⟨(d : G) * (C.f x : G) * (d : G)⁻¹, hmem⟩
      = (d : G)⁻¹ * (d : G)⁻¹ * hG C (C.f x) :=
    canon_H6 hsplit hzass h2 C d (C.f x) hfx hmem
  rw [h6, hdG, hG_f hsplit C hx]
  group

end Work.ZassenhausSuzuki
