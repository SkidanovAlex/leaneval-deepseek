/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# Injectivity of the Magnus map `rho`

`rho t : F((α \ {t}) × ℤ) →* F α` sends the generator `(x, i)` to the conjugate `t ^ i * x * t ^ (-i)`.
It is injective: the conjugates `t ^ i x t ^ (-i)` (for `x ≠ t`, `i ∈ ℤ`) freely generate the kernel
of the exponent-sum map `F α → ℤ`.

The proof here is the word-theoretic one.  To a word `L` in the decorated letters one attaches the
word `rew t L` in the original generators (`RhoRewrite.lean`), for which

* `mk (rewAux t cur L) = t ^ (-cur) * rho t (mk L)` (`mk_rewAux_self`), and
* `rewAux t cur L` is reduced whenever `L` is (`isReduced_rewAux_aux`) and nonempty whenever `L` is
  (`rewAux_ne_nil`).

Hence for a nontrivial reduced word `L` we have `mk (rewAux t 0 L) ≠ 1`, and so `rho t (mk L) ≠ 1`.
The reducedness of `rewAux t cur L` is proved by induction on `L`: the only non-trivial junctions are
those between two letters with the *same* decoration (where the intervening power of `t` is empty), and
there the reducedness of `L` itself supplies the compatibility.  This is the extra hypothesis carried
along in `isReduced_rewAux_aux`.
-/
import Mathlib
import Submission.Work.OROneRel.RhoRewrite

namespace Work.OROneRel

universe u

variable {α : Type u}

/-! ## Elementary list and free-group helpers -/

lemma rho_mk_append {γ : Type*} (L₁ L₂ : List (γ × Bool)) :
    FreeGroup.mk (L₁ ++ L₂) = FreeGroup.mk L₁ * FreeGroup.mk L₂ :=
  (FreeGroup.mul_mk).symm

lemma mk_cons {γ : Type*} (p : γ × Bool) (tl : List (γ × Bool)) :
    FreeGroup.mk (p :: tl) = FreeGroup.mk [p] * FreeGroup.mk tl := by
  rw [← rho_mk_append, List.singleton_append]

private lemma mk_singleton_true {γ : Type*} (a : γ) : FreeGroup.mk [(a, true)] = FreeGroup.of a := rfl

private lemma mk_singleton_false {γ : Type*} (a : γ) : FreeGroup.mk [(a, false)] = (FreeGroup.of a)⁻¹ := by
  rw [FreeGroup.of, FreeGroup.inv_mk]
  rfl

/-! ## Rewriting equations for `rewAux` -/

lemma rewAux_nil (t : α) (cur : ℤ) :
    rewAux t cur ([] : List (({x : α // x ≠ t} × ℤ) × Bool)) = zword t (0 - cur) := rfl

lemma rewAux_cons (t : α) (cur i : ℤ) (s : {x : α // x ≠ t}) (b : Bool)
    (tl : List (({x : α // x ≠ t} × ℤ) × Bool)) :
    rewAux t cur (((s, i), b) :: tl) = zword t (i - cur) ++ ((s : α), b) :: rewAux t i tl := rfl

lemma rewAux_ne_nil (t : α) (cur : ℤ) (L : List (({x : α // x ≠ t} × ℤ) × Bool))
    (hL : L ≠ []) : rewAux t cur L ≠ [] := by
  cases L with
  | nil => exact absurd rfl hL
  | cons hd tl =>
    obtain ⟨⟨s, i⟩, b⟩ := hd
    rw [rewAux_cons]
    intro h
    exact List.cons_ne_nil ((s : α), b) (rewAux t i tl) (List.append_eq_nil_iff.mp h).2

/-! ## `IsReduced` bookkeeping -/

/-- Reducedness of a concatenation from the reducedness of the two halves and the compatibility of
the last letter of the first with the first letter of the second. -/
lemma isReduced_append' {A B : List (α × Bool)}
    (hA : FreeGroup.IsReduced A) (hB : FreeGroup.IsReduced B)
    (h : ∀ x ∈ A.getLast?, ∀ y ∈ B.head?, x.1 = y.1 → x.2 = y.2) :
    FreeGroup.IsReduced (A ++ B) := hA.append hB h

/-- A concatenation whose first half consists of `t`-letters only and whose second half begins with a
letter different from `t` is reduced as soon as both halves are. -/
lemma isReduced_append_of_ts {t : α} {A B : List (α × Bool)}
    (hA : FreeGroup.IsReduced A) (hB : FreeGroup.IsReduced B)
    (hAt : ∀ x ∈ A.getLast?, x.1 = t) (hBh : ∀ y ∈ B.head?, y.1 ≠ t) :
    FreeGroup.IsReduced (A ++ B) :=
  isReduced_append' hA hB fun x hx y hy hxy => absurd (hxy ▸ hAt x hx) (hBh y hy)

/-- A letter different from `t` followed by a power of `t` is reduced. -/
lemma isReduced_cons_zword {t : α} {a : α × Bool} (ha : a.1 ≠ t) (n : ℤ) :
    FreeGroup.IsReduced (a :: zword t n) :=
  List.IsChain.cons (isReduced_zword t n) fun _ hy hay =>
    absurd (hay.trans (zword_head t n hy)) ha

/-! ## The word-theoretic identity `mk (rewAux t cur L) = t ^ (-cur) * rho (mk L)` -/

lemma rho_mk_singleton_true (t : α) (s : {x : α // x ≠ t}) (i : ℤ) :
    rho t (FreeGroup.mk [((⟨s, i⟩ : {x : α // x ≠ t} × ℤ), true)]) =
      FreeGroup.of t ^ i * FreeGroup.of (s : α) * FreeGroup.of t ^ (-i) := by
  rw [mk_singleton_true]
  unfold rho
  rw [FreeGroup.lift_apply_of]

lemma rho_mk_singleton_false (t : α) (s : {x : α // x ≠ t}) (i : ℤ) :
    rho t (FreeGroup.mk [((⟨s, i⟩ : {x : α // x ≠ t} × ℤ), false)]) =
      (FreeGroup.of t ^ i * FreeGroup.of (s : α) * FreeGroup.of t ^ (-i))⁻¹ := by
  rw [mk_singleton_false]
  unfold rho
  rw [map_inv, FreeGroup.lift_apply_of]

lemma mk_rewAux_self (t : α) (cur : ℤ) (L : List (({x : α // x ≠ t} × ℤ) × Bool)) :
    FreeGroup.mk (rewAux t cur L) = FreeGroup.of t ^ (-cur) * rho t (FreeGroup.mk L) := by
  induction L generalizing cur with
  | nil =>
    show FreeGroup.mk (zword t (0 - cur)) = FreeGroup.of t ^ (-cur) *
      rho t (FreeGroup.mk ([] : List (({x : α // x ≠ t} × ℤ) × Bool)))
    rw [mk_zword, show FreeGroup.mk ([] : List (({x : α // x ≠ t} × ℤ) × Bool)) =
      (1 : FreeGroup ({x : α // x ≠ t} × ℤ)) from rfl, map_one, mul_one]
    simp
  | cons hd tl ih =>
    obtain ⟨⟨s, i⟩, b⟩ := hd
    have hzipow : FreeGroup.of t ^ (i - cur) =
        FreeGroup.of t ^ (-cur) * FreeGroup.of t ^ i := by
      rw [← zpow_add]; congr 1; ring
    cases b
    · have hfac : FreeGroup.mk (((s : α), false) :: rewAux t i tl) =
          (FreeGroup.of (s : α))⁻¹ * FreeGroup.mk (rewAux t i tl) := by
        rw [mk_cons, mk_singleton_false]
      have hrho : rho t (FreeGroup.mk (((s, i), false) :: tl)) =
          (FreeGroup.of t ^ i * FreeGroup.of (s : α) * FreeGroup.of t ^ (-i))⁻¹
            * rho t (FreeGroup.mk tl) := by
        rw [mk_cons, map_mul, rho_mk_singleton_false]
      rw [rewAux_cons, rho_mk_append, mk_zword, hfac, ih i, hrho, hzipow]
      group
    · have hfac : FreeGroup.mk (((s : α), true) :: rewAux t i tl) =
          FreeGroup.of (s : α) * FreeGroup.mk (rewAux t i tl) := by
        rw [mk_cons, mk_singleton_true]
      have hrho : rho t (FreeGroup.mk (((s, i), true) :: tl)) =
          (FreeGroup.of t ^ i * FreeGroup.of (s : α) * FreeGroup.of t ^ (-i))
            * rho t (FreeGroup.mk tl) := by
        rw [mk_cons, map_mul, rho_mk_singleton_true]
      rw [rewAux_cons, rho_mk_append, mk_zword, hfac, ih i, hrho, hzipow]
      group

/-! ## Reducedness of the rewritten word -/

theorem isReduced_rewAux_aux (t : α) :
    ∀ L : List (({x : α // x ≠ t} × ℤ) × Bool), FreeGroup.IsReduced L →
      (∀ cur : ℤ, FreeGroup.IsReduced (rewAux t cur L)) ∧
      (∀ (cur : ℤ) (a : α × Bool), a.1 ≠ t →
        (∀ p : ({x : α // x ≠ t} × ℤ) × Bool, L.head? = some p → p.1.2 = cur →
          a.1 = p.1.1 → a.2 = p.2) →
        FreeGroup.IsReduced (a :: rewAux t cur L)) := by
  intro L
  induction L with
  | nil =>
    intro _
    refine ⟨fun cur => isReduced_zword t (0 - cur), fun cur a ha _ => ?_⟩
    show FreeGroup.IsReduced (a :: zword t (0 - cur))
    exact isReduced_cons_zword ha (0 - cur)
  | cons p tl ih =>
    intro hL
    obtain ⟨⟨s, i⟩, b⟩ := p
    have htail : FreeGroup.IsReduced tl := hL.tail
    have hpair : ∀ y : ({x : α // x ≠ t} × ℤ) × Bool, y ∈ tl.head? →
        ((s, i), b).1 = y.1 → b = y.2 := (List.isChain_cons.mp hL).1
    obtain ⟨ihred, ihcons⟩ := ih htail
    have hB : FreeGroup.IsReduced (((s : α), b) :: rewAux t i tl) :=
      ihcons i ((s : α), b) s.2 (fun q hq hqi hs => by
        have hs' : s = q.1.1 := Subtype.ext hs
        exact hpair q (by rw [hq]; exact Option.mem_some_iff.mpr rfl) (Prod.ext hs' hqi.symm))
    refine ⟨fun cur => ?_, fun cur a ha hcomp => ?_⟩
    · show FreeGroup.IsReduced (rewAux t cur (((s, i), b) :: tl))
      rw [rewAux_cons]
      exact isReduced_append_of_ts (isReduced_zword t (i - cur)) hB
        (fun x hx => zword_getLast t (i - cur) hx)
        (fun y hy => by
          rw [List.head?_cons] at hy
          rw [Option.mem_some_iff] at hy
          rw [← hy]
          exact s.2)
    · show FreeGroup.IsReduced (a :: rewAux t cur (((s, i), b) :: tl))
      rw [rewAux_cons]
      by_cases hic : i = cur
      · have hz : zword t (i - cur) = [] := by rw [zword_nil_iff]; omega
        rw [hz, List.nil_append]
        refine List.IsChain.cons hB (fun y hy => ?_)
        rw [List.head?_cons] at hy
        rw [Option.mem_some_iff] at hy
        rw [← hy]
        intro hay
        exact hcomp ((s, i), b) rfl hic hay
      · have hz : zword t (i - cur) ≠ [] := by rw [ne_eq, zword_nil_iff]; omega
        refine List.IsChain.cons ?_ (fun y hy hay => ?_)
        · exact isReduced_append_of_ts (isReduced_zword t (i - cur)) hB
            (fun x hx => zword_getLast t (i - cur) hx)
            (fun y hy => by
              rw [List.head?_cons] at hy
              rw [Option.mem_some_iff] at hy
              rw [← hy]
              exact s.2)
        · rw [List.head?_append_of_ne_nil _ hz] at hy
          exact absurd (hay.trans (zword_head t (i - cur) hy)) ha

/-! ## Injectivity of `rho` -/

theorem rho_eq_one {t : α} (w : FreeGroup ({x : α // x ≠ t} × ℤ)) (hw : rho t w = 1) : w = 1 := by
  classical
  set L := FreeGroup.toWord w with hL
  have hred : FreeGroup.IsReduced L := by rw [hL]; exact FreeGroup.isReduced_toWord
  have hmk : FreeGroup.mk L = w := by rw [hL]; exact FreeGroup.mk_toWord
  have hone : FreeGroup.mk (rewAux t 0 L) = 1 := by
    rw [mk_rewAux_self, hmk, hw, mul_one]
    simp
  have hred0 : FreeGroup.IsReduced (rewAux t 0 L) := (isReduced_rewAux_aux t L hred).1 0
  have hnil : rewAux t 0 L = [] := by
    have h1 : (FreeGroup.mk (rewAux t 0 L)).toWord = rewAux t 0 L := by
      rw [FreeGroup.toWord_mk, FreeGroup.IsReduced.reduce_eq hred0]
    rw [hone, FreeGroup.toWord_one] at h1
    exact h1.symm
  have hLnil : L = [] := by
    by_contra hne
    exact rewAux_ne_nil t 0 L hne hnil
  rw [← hmk, hLnil]
  rfl

theorem rho_injective {α : Type u} (t : α) :
    Function.Injective (Work.OROneRel.rho t) := by
  intro w w' hww'
  have h1 : rho t (w * w'⁻¹) = 1 := by rw [map_mul, map_inv, hww', mul_inv_cancel]
  have h2 : w * w'⁻¹ = 1 := rho_eq_one (w * w'⁻¹) h1
  have h3 : w = w * w'⁻¹ * w' := by group
  rw [h3, h2, one_mul]

end Work.OROneRel
