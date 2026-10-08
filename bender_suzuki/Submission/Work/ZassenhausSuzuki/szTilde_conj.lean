import Mathlib
import Submission.Work.ZassenhausSuzuki.SzTildeDefs
import Submission.Work.ZassenhausSuzuki.canon_relations
import Submission.Work.ZassenhausSuzuki.canon_aux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The Suzuki reflection map `∼` is equivariant under the two-point stabiliser

The reflection map `szTilde hsplit = ∼` of the root group `Q` (BG 3.1 (j),
`SzTildeDefs.lean`) is given on `Q#` by `∼ x = g (g x)⁻¹`, where `g` is the `Q`-part of the
Weyl conjugation `t x t = g(x) h(x) t f(x)`.  This file proves that `∼` commutes with the
conjugation action of `D = twoPoint H t = H ⊓ H^t`: if `a = d b d⁻¹` with `d ∈ D`, then
`∼ a = d (∼ b) d⁻¹`.

The point is the equivariance of the structure map `g` itself
(`szCanon_conj_g`): for `d ∈ D` and `x ∈ Q#`, with `y = d⁻¹ x d`,
`g(y) = d · g(x) · d⁻¹`.  This is `Work.PSU3.RankOne.canon_conj` together with
`t d t = d⁻¹` (`canon_t_conj_inv_D`).  Applying it twice — to `a` and to `(g b)⁻¹` —
gives the claim, since `g(a) = d⁻¹ g(b) d` implies `(g a)⁻¹ = d⁻¹ (g b)⁻¹ d`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausSuzuki

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-- For `x ∈ Q#` the structure map value `g x` is again nontrivial: otherwise
`(g x)⁻¹ = 1 = f (x⁻¹)` (H1), contradicting `f y ≠ 1` for `y ≠ 1`. -/
lemma szCanon_g_ne_one (hsplit : IsSplitRankOne H Q t)
    (C : Work.ZassenhausPSL2.Canon H Q t) {x : Q} (hx : (x : G) ≠ 1) :
    ((C.g x : Q) : G) ≠ 1 := by
  intro h
  have hQ : C.g x = 1 := Subtype.ext h
  have h1 := canon_H1 hsplit C x hx
  rw [hQ, inv_one] at h1
  have hfin : C.f x⁻¹ = 1 := h1.symm
  exact (canon_f_ne_one hsplit C (canon_inv_ne_one hx)) (by rw [hfin]; rfl)

/-- **Equivariance of the structure map `g` under `D = twoPoint H t`.**  If `d ∈ D`, `x ∈ Q#`
and `y = d⁻¹ x d`, then `g(y) = d · g(x) · d⁻¹`.  (`Work.PSU3.RankOne.canon_conj` gives
`g(a⁻¹ x a) = (t a t)⁻¹ g(x) (t a t)`, and `t a t = a⁻¹` since `t` inverts `D`.) -/
lemma szCanon_conj_g (hsplit : IsSplitRankOne H Q t) (hzass : IsZassenhaus H)
    (h2 : IsPGroup 2 Q) (C : Work.ZassenhausPSL2.Canon H Q t) (d : twoPoint H t) {x y : Q}
    (hx : (x : G) ≠ 1) (hxy : (y : G) = (d : G)⁻¹ * (x : G) * (d : G)) :
    ((C.g y : Q) : G) = (d : G) * ((C.g x : Q) : G) * (d : G)⁻¹ := by
  obtain ⟨hg', hd', hy', heq⟩ :=
    Work.PSU3.RankOne.canon_conj hsplit (a := (d : G)) d.2 (canon3_of_C hsplit C hx)
  have hyne : (y : G) ≠ 1 := by
    intro hy1
    apply hx
    have hthis : (d : G)⁻¹ * (x : G) * (d : G) = 1 := by rw [← hxy]; exact hy1
    calc (x : G) = (d : G) * ((d : G)⁻¹ * (x : G) * (d : G)) * (d : G)⁻¹ := by group
      _ = (d : G) * 1 * (d : G)⁻¹ := by rw [hthis]
      _ = 1 := by group
  have hc : t * (y : G) * t
      = ((⟨(t * (d : G) * t)⁻¹ * ((C.g x : Q) : G) * (t * (d : G) * t), hg'⟩ : Q) : G)
        * ((⟨(t * (d : G) * t)⁻¹ * ((C.h x : twoPoint H t) : G) * (d : G), hd'⟩
              : twoPoint H t) : G)
        * t
        * ((⟨(t * (d : G) * t)⁻¹ * ((C.f x : Q) : G) * (t * (d : G) * t), hy'⟩ : Q) : G) := by
    rw [← hxy] at heq
    exact heq
  have hres := canon3_eq_C hsplit C (y := y) hyne hc
  have ht : t * (d : G) * t = (d : G)⁻¹ := canon_t_conj_inv_D hsplit hzass h2 d.2
  have hgy : ((C.g y : Q) : G)
      = (t * (d : G) * t)⁻¹ * ((C.g x : Q) : G) * (t * (d : G) * t) :=
    congrArg Subtype.val hres.2.1
  rw [hgy, ht]
  simp

theorem szTilde_conj {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    {d : G} (hd : d ∈ Submission.Blueprint.twoPoint H t) {a b : Q}
    (hab : (a : G) = d * (b : G) * d⁻¹) :
    (Work.ZassenhausSuzuki.szTilde hsplit a : G)
      = d * (Work.ZassenhausSuzuki.szTilde hsplit b : G) * d⁻¹ := by
  classical
  by_cases hb1 : (b : G) = 1
  · -- degenerate case: `a = d b d⁻¹ = 1` as well
    have ha1 : (a : G) = 1 := by rw [hab, hb1, mul_one, mul_inv_cancel]
    have hsa : szTilde hsplit a = 1 := by simp only [szTilde]; rw [ite_eq_left ha1]
    have hsb : szTilde hsplit b = 1 := by simp only [szTilde]; rw [ite_eq_left hb1]
    rw [hsa, hsb]; simp
  · have ha1 : (a : G) ≠ 1 := by
      intro h
      apply hb1
      have hba : (b : G) = (d : G)⁻¹ * (a : G) * (d : G) := by rw [hab]; group
      rw [hba, h]; group
    have hba : (b : G) = (d : G)⁻¹ * (a : G) * (d : G) := by rw [hab]; group
    have hsa : szTilde hsplit a = (szCanon hsplit).g (((szCanon hsplit).g a)⁻¹) := by
      simp only [szTilde]; rw [ite_eq_right ha1]
    have hsb : szTilde hsplit b = (szCanon hsplit).g (((szCanon hsplit).g b)⁻¹) := by
      simp only [szTilde]; rw [ite_eq_right hb1]
    have hgb_ne : (((szCanon hsplit).g b : Q) : G) ≠ 1 :=
      szCanon_g_ne_one hsplit (szCanon hsplit) hb1
    have hgeq : (((szCanon hsplit).g b : Q) : G)
        = d * (((szCanon hsplit).g a : Q) : G) * d⁻¹ :=
      szCanon_conj_g hsplit hzass h2 (szCanon hsplit) ⟨d, hd⟩ ha1 hba
    have hne_inv : ((((szCanon hsplit).g b)⁻¹ : Q) : G) ≠ 1 := by
      rw [Subgroup.coe_inv]; exact inv_ne_one.mpr hgb_ne
    have hinv_eq : ((((szCanon hsplit).g a)⁻¹ : Q) : G)
        = d⁻¹ * ((((szCanon hsplit).g b)⁻¹ : Q) : G) * d := by
      rw [Subgroup.coe_inv, Subgroup.coe_inv, hgeq]; group
    have hfinal :=
      szCanon_conj_g hsplit hzass h2 (szCanon hsplit) ⟨d, hd⟩ hne_inv hinv_eq
    rw [hsa, hsb]
    exact hfinal

end Work.ZassenhausSuzuki
