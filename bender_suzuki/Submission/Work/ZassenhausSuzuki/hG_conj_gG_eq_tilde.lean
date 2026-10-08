import Mathlib
import Submission.Work.ZassenhausSuzuki.szTildeAux
import Submission.Work.ZassenhausSuzuki.SzTildeDefs
import Submission.Work.ZassenhausSuzuki.canon_relations
import Submission.Work.RankOneUniqueness.t_smul_qPt

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausSuzuki.hG_conj_gG_eq_tilde`

The conjugation `h⁻¹ · g · h` of the `Q`-part `g = gG C a` of the canonical structure of `t a t`
by the `D`-part `h = hG C a`, for a non-trivial involution `a ∈ Q#`, is the Suzuki reflection of
the inverse of the reflection of `a`:

`(h a)⁻¹ · g(a) · h(a) = ∼ ((∼ a)⁻¹)`.

**Why.**  Write `b := ∼ a = C.g (C.f a)` (the second equality is H1, `(C.g a)⁻¹ = C.f a` since
`a² = 1`).  The interior of the right-hand side is

`(∼ a)⁻¹ = b⁻¹ = (C.g (C.f a))⁻¹ = C.f (C.g a)` (H1 again);

put `u := b⁻¹`, so that both `u` and `b` are non-trivial elements of `Q`.

* `((C.f (C.g a) : Q) : G) = (h a)⁻¹ · g(a) · h(a)`: this is H4 (`f(g x) = (h x)⁻¹ (f x)⁻¹ h x`)
  at `x = a`, together with `(f a)⁻¹ = g a` (H1 at `a`).  Hence the left-hand side is `(u : G)`.
* `C.f b` is an involution: by H4 at `x = C.f a` and H2 (`f(f a) = a`),
  `C.f b = (h (C.f a))⁻¹ · a · (h (C.f a))`, a conjugate of the involution `a`.
* Hence `C.g u` is an involution: H1 at `u` gives `(C.g u)⁻¹ = C.f (u⁻¹) = C.f b`, and `C.f b`
  equals its own inverse.
* Finally `∼ u = C.g ((C.g u)⁻¹) = C.g (C.g u) = u`, the last step being `canon_g_g`
  (`C.g (C.g x) = x`), which says that the Weyl element `t` acts on the `Q`-labelling of
  `Ω ∖ {∞}` as an involution: `t • qPt x = qPt (C.g x)` (`t_smul_qPt_canon`, from
  `Work.RankOneUniqueness.t_smul_qPt` and H1), so `t • (t • qPt x) = qPt x` and the labelling is
  injective (`Work.RankOneUniqueness.qPt_injective`).

Nothing here uses the Suzuki coordinates: the identity is a consequence of the canonical
relations H1, H2, H4 of Peterfalvi II Ch. VII §1 alone.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausSuzuki

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-- **The Weyl element acts on the `Q`-labelling by the structure map `g`.**  For `x ∈ Q#`,
`t • qPt H t x = qPt H t (g x)`.  Indeed `t x⁻¹ t = g(x⁻¹) h(x⁻¹) t f(x⁻¹)`, so
`Work.RankOneUniqueness.t_smul_qPt` gives `t • qPt x = qPt ((f x⁻¹)⁻¹)`, and `(f x⁻¹)⁻¹ = g x`
by H1. -/
theorem t_smul_qPt_canon (hsplit : IsSplitRankOne H Q t)
    (C : Work.ZassenhausPSL2.Canon H Q t) {x : Q} (hx : (x : G) ≠ 1) :
    t • Work.RankOneUniqueness.qPt H t (x : G)
      = Work.RankOneUniqueness.qPt H t ((C.g x : Q) : G) := by
  have hspec := C.spec x⁻¹ (canon_inv_ne_one hx)
  have hm : ((C.g x⁻¹ : Q) : G) * ((C.h x⁻¹ : twoPoint H t) : G) ∈ H :=
    H.mul_mem (hsplit.le (C.g x⁻¹).2) (Subgroup.mem_inf.mp (C.h x⁻¹).2).1
  have h := Work.RankOneUniqueness.t_smul_qPt hsplit (x := (x : G))
    (m := ((C.g x⁻¹ : Q) : G) * ((C.h x⁻¹ : twoPoint H t) : G))
    (y := ((C.f x⁻¹ : Q) : G)) x.2 hx hm (C.f x⁻¹).2 (by simpa using hspec)
  have hH1 := congrArg (fun z : Q => (z : G)) (canon_H1 hsplit C x hx)
  rw [h]
  congr 1
  show (((C.f x⁻¹ : Q) : G))⁻¹ = ((C.g x : Q) : G)
  rw [← hH1]
  simp

/-- **The structure map `g` is an involution on `Q#`**: `C.g (C.g x) = x` for `x ∈ Q#`.  The
Weyl element `t` acts on the labelling of `Ω ∖ {∞}` by `x ↦ C.g x`
(`t_smul_qPt_canon`), it is an involution, and the labelling is injective. -/
theorem canon_g_g (hsplit : IsSplitRankOne H Q t) (hzass : IsZassenhaus H) (h2 : IsPGroup 2 Q)
    (C : Work.ZassenhausPSL2.Canon H Q t) {x : Q} (hx : (x : G) ≠ 1) :
    C.g (C.g x) = x := by
  have h1 := t_smul_qPt_canon hsplit C hx
  have hgxne : ((C.g x : Q) : G) ≠ 1 := canon_g_ne_one hsplit hzass h2 C hx
  have h2' := t_smul_qPt_canon hsplit C (x := C.g x) hgxne
  have key : Work.RankOneUniqueness.qPt H t ((C.g (C.g x) : Q) : G)
      = Work.RankOneUniqueness.qPt H t (x : G) := by
    rw [← h2', ← h1, ← mul_smul, canon_t_mul_t hsplit, one_smul]
  exact Subtype.ext (Work.RankOneUniqueness.qPt_injective hsplit ((C.g (C.g x)).2) x.2 key)

theorem hG_conj_gG_eq_tilde {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    (C : Work.ZassenhausPSL2.Canon H Q t) {a : Q} (ha1 : (a : G) ≠ 1) (ha2 : a * a = 1) :
    (Work.ZassenhausSuzuki.hG C a)⁻¹ * Work.ZassenhausSuzuki.gG C a
        * Work.ZassenhausSuzuki.hG C a
      = ((Work.ZassenhausSuzuki.tildeOf C ((Work.ZassenhausSuzuki.tildeOf C a)⁻¹) : Q) : G) := by
  -- `a` is an involution of `Q`, hence `f a = (g a)⁻¹` (H1) and `a` is its own inverse in `G`
  have haG : (a : G) * (a : G) = 1 := by
    simpa using congrArg (fun z : Q => (z : G)) ha2
  have haGi : (a : G)⁻¹ = (a : G) := inv_eq_of_mul_eq_one_left haG
  have hfa : C.f a = (C.g a)⁻¹ := by
    have h := canon_H1 hsplit C a ha1
    rw [inv_eq_of_mul_eq_one_left ha2] at h
    exact h.symm
  -- `b := ∼ a = g (g a)⁻¹ = g (f a)`, and `u := b⁻¹ = f (g a)`
  set b : Q := tildeOf C a with hbdef
  have hbeq : b = C.g (C.f a) := by
    rw [hbdef, tildeOf, ite_eq_right ha1, hfa]
  have hbne : b ≠ 1 := by
    intro h
    have h' : (b : G) = 1 := congrArg (fun z : Q => (z : G)) h
    rw [hbeq] at h'
    exact canon_g_ne_one hsplit hzass h2 C (canon_f_ne_one hsplit C ha1) h'
  have hube : b⁻¹ = C.f (C.g a) := by
    rw [hbeq]
    have h1 := canon_H1 hsplit C (C.f a) (canon_f_ne_one hsplit C ha1)
    rw [h1, hfa, inv_inv]
  -- the left-hand side is `(u : G)`
  have hLHS : ((C.f (C.g a) : Q) : G) = (hG C a)⁻¹ * gG C a * hG C a := by
    have h4 := canon_H4 hsplit hzass h2 C a ha1
    rw [h4, hfa, gG, hG]
    simp
  -- `f b` is an involution: `f b = (h (f a))⁻¹ · a · (h (f a))` (H4 at `f a`, H2 at `a`)
  have hfbinv : C.f b * C.f b = 1 := by
    have hfa_ne : ((C.f a : Q) : G) ≠ 1 := canon_f_ne_one hsplit C ha1
    have h4 := canon_H4 hsplit hzass h2 C (C.f a) hfa_ne
    have hff : C.f (C.f a) = a := canon_H2 hsplit C a ha1
    have hexp : ((C.f b : Q) : G) = (hG C (C.f a))⁻¹ * (a : G) * hG C (C.f a) := by
      rw [hbeq, h4, hff, haGi]
    have hmul : ((C.f b : Q) : G) * ((C.f b : Q) : G) = 1 := by
      rw [hexp]
      rw [show (hG C (C.f a))⁻¹ * (a : G) * hG C (C.f a)
              * ((hG C (C.f a))⁻¹ * (a : G) * hG C (C.f a))
            = (hG C (C.f a))⁻¹ * ((a : G) * (a : G)) * hG C (C.f a) from by group]
      rw [haG, mul_one, inv_mul_cancel]
    exact Subtype.ext (by simpa using hmul)
  -- consequently `g u` is an involution, and `∼ u = g ((g u)⁻¹) = g (g u) = u`
  have htilde_u : tildeOf C (b⁻¹) = b⁻¹ := by
    have hbine : b⁻¹ ≠ 1 := fun h => hbne (inv_eq_one.mp h)
    have hbineG : ((b⁻¹ : Q) : G) ≠ 1 := fun h => hbine (Subtype.ext h)
    rw [tildeOf, ite_eq_right hbineG]
    have h2' : (C.f b)⁻¹ = C.f b := inv_eq_of_mul_eq_one_left hfbinv
    have h3 : C.g b⁻¹ = C.f b := by
      have h1 := canon_H1 hsplit C b⁻¹ hbineG
      rw [inv_inv] at h1
      calc C.g b⁻¹ = ((C.g b⁻¹)⁻¹)⁻¹ := (inv_inv _).symm
        _ = (C.f b)⁻¹ := by rw [h1]
        _ = C.f b := h2'
    have hinv : (C.g b⁻¹)⁻¹ = C.g b⁻¹ := by rw [h3]; exact h2'
    rw [hinv]
    exact canon_g_g hsplit hzass h2 C (x := b⁻¹) hbineG
  rw [← hLHS, htilde_u, hube]

end Work.ZassenhausSuzuki
