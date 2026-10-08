import Mathlib
import Submission.Work.ZassenhausPSL2.Defs
import Submission.Work.ZassenhausPSL2.Basic
import Submission.Work.RankOneUniqueness.canon_unique
import Submission.Work.RankOneUniqueness.canon_exists
import Submission.Work.ZassenhausPSL2.ZData.t_conj_eq_inv
import Submission.Work.PSU3.RankOne.canon_mul
import Submission.Work.PSU3.RankOne.canon_conj
import Submission.Work.PSU3.RankOne.canon_mul_ne_one

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausSuzuki.canon_aux` — auxiliary lemmas for the canonical maps

Basic facts about the canonical structure maps of a split rank-one group
`t x t = g(x) h(x) t f(x)`, used to prove Peterfalvi II Ch. VII §1 H1–H6
(`Work.ZassenhausSuzuki.canon_relations`).  The hard group computations (H1, H2, H3/H4a, H6)
are reused from the delivered area `Work.PSU3.RankOne`; here we only translate the `Canon3`
relation into the `Canon` maps and apply the `t`-inversion of `D` (which holds in the
Zassenhaus case).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausSuzuki

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-- `t` is an involution. -/
lemma canon_t_mul_t (h : IsSplitRankOne H Q t) : t * t = 1 :=
  Work.ZassenhausPSL2.t_mul_t h

/-- `t⁻¹ = t`. -/
lemma canon_t_inv (h : IsSplitRankOne H Q t) : t⁻¹ = t :=
  Work.ZassenhausPSL2.t_inv h

/-- The root group `Q` is nontrivial: otherwise `D = H` would be both odd and even. -/
lemma canon_Q_ne_bot (h : IsSplitRankOne H Q t) : Q ≠ ⊥ := by
  intro hbot
  have htwo : twoPoint H t = H := by
    have hs : Q ⊔ twoPoint H t = H := h.sup_eq
    rw [hbot, bot_sup_eq] at hs
    exact hs
  have hodd : Odd (Nat.card (twoPoint H t)) := h.stronglyEmbedded.2.2 t h.not_mem
  rw [htwo] at hodd
  exact (Nat.not_odd_iff_even.mpr h.stronglyEmbedded.2.1) hodd

/-- The Weyl element inverts the two-point stabiliser `D = twoPoint H t`. -/
lemma canon_t_conj_inv_D (h : IsSplitRankOne H Q t) (hz : IsZassenhaus H) (h2 : IsPGroup 2 Q)
    {d : G} (hd : d ∈ twoPoint H t) : t * d * t = d⁻¹ :=
  Work.ZassenhausPSL2.ZData.t_conj_eq_inv H Q t h hz (canon_Q_ne_bot h) h2 d hd

/-- `t * d = d⁻¹ * t` for `d ∈ D`. -/
lemma canon_t_mul_D_inv (h : IsSplitRankOne H Q t) (hz : IsZassenhaus H) (h2 : IsPGroup 2 Q)
    {d : G} (hd : d ∈ twoPoint H t) : t * d = d⁻¹ * t := by
  have ht2 := canon_t_mul_t h
  have hd' := canon_t_conj_inv_D h hz h2 hd
  calc t * d = t * d * (t * t) := by rw [ht2, mul_one]
    _ = (t * d * t) * t := by group
    _ = d⁻¹ * t := by rw [hd']

/-- `t * d⁻¹ = d * t` for `d ∈ D`. -/
lemma canon_t_mul_D_inv_inv (h : IsSplitRankOne H Q t) (hz : IsZassenhaus H) (h2 : IsPGroup 2 Q)
    {d : G} (hd : d ∈ twoPoint H t) : t * d⁻¹ = d * t := by
  have h' := canon_t_mul_D_inv h hz h2 ((twoPoint H t).inv_mem hd)
  simpa using h'

/-- `t * d⁻¹ * t = d` for `d ∈ D`. -/
lemma canon_t_conj_invD_inv (h : IsSplitRankOne H Q t) (hz : IsZassenhaus H) (h2 : IsPGroup 2 Q)
    {d : G} (hd : d ∈ twoPoint H t) : t * d⁻¹ * t = d := by
  have h1 : (MulAut.conj t) d⁻¹ = ((MulAut.conj t) d)⁻¹ := map_inv (MulAut.conj t) d
  rw [MulAut.conj_apply, MulAut.conj_apply, canon_t_inv h] at h1
  rw [h1, canon_t_conj_inv_D h hz h2 hd, inv_inv]

/-- `d ∈ D` normalises `Q`. -/
lemma canon_D_conj_Q_mem (h : IsSplitRankOne H Q t) (d : twoPoint H t) (q : Q) :
    (d : G) * (q : G) * (d : G)⁻¹ ∈ Q :=
  (Subgroup.le_normalizer_iff.mp (le_trans inf_le_left h.normal)) (d : G) d.2 (q : G) q.2

/-- `d ∈ D` normalises `Q` (inverse form). -/
lemma canon_D_conj_Q_mem_inv (h : IsSplitRankOne H Q t) (d : twoPoint H t) (q : Q) :
    (d : G)⁻¹ * (q : G) * (d : G) ∈ Q := by
  have hh := canon_D_conj_Q_mem h d⁻¹ q
  simpa using hh

/-- `D` is abelian when `t` inverts it. -/
lemma canon_D_abelian_mul (h : IsSplitRankOne H Q t) (hz : IsZassenhaus H) (h2 : IsPGroup 2 Q)
    {a b : G} (ha : a ∈ twoPoint H t) (hb : b ∈ twoPoint H t) : a * b = b * a := by
  have ha' := canon_t_conj_inv_D h hz h2 ha
  have hb' := canon_t_conj_inv_D h hz h2 hb
  have hab := canon_t_conj_inv_D h hz h2 ((twoPoint H t).mul_mem ha hb)
  have h1 : t * (a * b) * t = (t * a * t) * (t * b * t) := by
    have hh := map_mul (MulAut.conj t) a b
    simpa only [MulAut.conj_apply, canon_t_inv h] using hh
  rw [h1, ha', hb'] at hab
  have hthis := congrArg Inv.inv hab
  have h2' : b * a = a * b := by simpa [mul_inv_rev, inv_inv] using hthis
  exact h2'.symm

/-- Uniqueness of the decomposition `H = Q · D`. -/
lemma canon_QD_unique (h : IsSplitRankOne H Q t) {q₁ q₂ : Q} {d₁ d₂ : twoPoint H t}
    (he : (q₁ : G) * (d₁ : G) = (q₂ : G) * (d₂ : G)) : q₁ = q₂ ∧ d₁ = d₂ := by
  have hkey : (q₂ : G)⁻¹ * (q₁ : G) = (d₂ : G) * (d₁ : G)⁻¹ := by
    have h1 : (q₂ : G)⁻¹ * (q₁ : G) * (d₁ : G) = (d₂ : G) := by
      have h2 : (q₂ : G)⁻¹ * (q₁ : G) * (d₁ : G) = (q₂ : G)⁻¹ * (q₂ : G) * (d₂ : G) := by
        calc (q₂ : G)⁻¹ * (q₁ : G) * (d₁ : G) = (q₂ : G)⁻¹ * ((q₁ : G) * (d₁ : G)) := by group
          _ = (q₂ : G)⁻¹ * ((q₂ : G) * (d₂ : G)) := by rw [he]
          _ = (q₂ : G)⁻¹ * (q₂ : G) * (d₂ : G) := by group
      rwa [inv_mul_cancel, one_mul] at h2
    rw [← h1]; group
  have hmemQ : (q₂ : G)⁻¹ * (q₁ : G) ∈ Q := Q.mul_mem (Q.inv_mem q₂.2) q₁.2
  have hmemD : (q₂ : G)⁻¹ * (q₁ : G) ∈ twoPoint H t := by
    rw [hkey]
    exact (twoPoint H t).mul_mem d₂.2 ((twoPoint H t).inv_mem d₁.2)
  have hone : (q₂ : G)⁻¹ * (q₁ : G) = 1 := by
    have hb : (q₂ : G)⁻¹ * (q₁ : G) ∈ (⊥ : Subgroup G) := by
      rw [← h.inf_eq]; exact ⟨hmemQ, hmemD⟩
    simpa using hb
  have hqeq : q₁ = q₂ := Subtype.ext (inv_mul_eq_one.mp hone).symm
  refine ⟨hqeq, ?_⟩
  have hthis := he
  rw [congrArg Subtype.val hqeq] at hthis
  exact Subtype.ext (mul_left_cancel hthis)

/-- The `Canon3` datum attached to `Canon` at `x ∈ Q#`. -/
lemma canon3_of_C (h : IsSplitRankOne H Q t) (C : Work.ZassenhausPSL2.Canon H Q t) {x : Q}
    (hx : (x : G) ≠ 1) :
    Work.PSU3.Canon3 H Q t (x : G) (C.g x : G) (C.h x : G) (C.f x : G) :=
  ⟨(C.g x).2, (C.h x).2, (C.f x).2, C.spec x hx⟩

/-- A `Canon3` datum determines the `Canon` maps. -/
lemma canon3_eq_C (h : IsSplitRankOne H Q t) (C : Work.ZassenhausPSL2.Canon H Q t) {y : Q}
    (hy : (y : G) ≠ 1) {g : Q} {d : twoPoint H t} {z : Q}
    (hc : t * (y : G) * t = (g : G) * (d : G) * t * (z : G)) :
    C.f y = z ∧ C.g y = g ∧ C.h y = d := by
  have hgh : ((C.g y : Q) : G) * (C.h y : G) ∈ H :=
    H.mul_mem (h.le (C.g y).2) (Subgroup.mem_inf.mp (C.h y).2).1
  have hgd : (g : G) * (d : G) ∈ H := H.mul_mem (h.le g.2) (Subgroup.mem_inf.mp d.2).1
  have h1 : (⟨((C.g y : Q) : G) * (C.h y : G), hgh⟩ : H).1 * t * (C.f y : G)
      = t * (y : G) * t := by
    show ((C.g y : Q) : G) * (C.h y : G) * t * (C.f y : G) = t * (y : G) * t
    rw [← C.spec y hy]
  have h2 : (⟨(g : G) * (d : G), hgd⟩ : H).1 * t * (z : G) = t * (y : G) * t := hc.symm
  have hkey := Work.ZassenhausPSL2.decomp_unique h h1 h2
  have hf : C.f y = z := congrArg Prod.snd hkey
  have hprod : ((C.g y : Q) : G) * (C.h y : G) = (g : G) * (d : G) :=
    congrArg Subtype.val (congrArg Prod.fst hkey)
  have hqd := canon_QD_unique h (q₁ := C.g y) (q₂ := g) (d₁ := C.h y) (d₂ := d) hprod
  exact ⟨hf, hqd.1, hqd.2⟩

/-- `f x ≠ 1` for `x ∈ Q#`. -/
lemma canon_f_ne_one (h : IsSplitRankOne H Q t) (C : Work.ZassenhausPSL2.Canon H Q t) {x : Q}
    (hx : (x : G) ≠ 1) : (C.f x : G) ≠ 1 := by
  intro hc
  have ht2 := canon_t_mul_t h
  have hspec := C.spec x hx
  rw [hc, mul_one] at hspec
  have htx : t * (x : G) = (C.g x : G) * (C.h x : G) := by
    have h1 := congrArg (fun z : G => z * t) hspec
    simpa [mul_assoc, ht2] using h1
  have hmem : t * (x : G) ∈ H := by
    rw [htx]
    exact H.mul_mem (h.le (C.g x).2) (Subgroup.mem_inf.mp (C.h x).2).1
  have htmem : t ∈ H := by
    have h2 := H.mul_mem hmem (H.inv_mem (h.le x.2))
    rwa [mul_assoc, mul_inv_cancel, mul_one] at h2
  exact h.not_mem htmem

/-- `x⁻¹ ∈ Q#` for `x ∈ Q#`. -/
lemma canon_inv_ne_one {x : Q} (hx : (x : G) ≠ 1) : (((x⁻¹ : Q)) : G) ≠ 1 := by
  intro hc
  exact hx (by simpa using congrArg Inv.inv hc)

/-! ## The identities H1–H6 -/

/-- **H1.** `g(x)⁻¹ = f(x⁻¹)`. -/
lemma canon_H1 (h : IsSplitRankOne H Q t) (C : Work.ZassenhausPSL2.Canon H Q t) :
    ∀ x : Q, (x : G) ≠ 1 → (C.g x)⁻¹ = C.f x⁻¹ := by
  intro x hx
  obtain ⟨hg', hd', hy', heq⟩ := Work.PSU3.canon_inv h (canon3_of_C h C hx)
  have hres := canon3_eq_C h C (y := x⁻¹) (canon_inv_ne_one hx)
    (g := ⟨_, hg'⟩) (d := ⟨_, hd'⟩) (z := ⟨_, hy'⟩) heq
  exact Subtype.ext (congrArg Subtype.val hres.1).symm

/-- **H2.** `f(f(x)) = x`. -/
lemma canon_H2 (h : IsSplitRankOne H Q t) (C : Work.ZassenhausPSL2.Canon H Q t) :
    ∀ x : Q, (x : G) ≠ 1 → C.f (C.f x) = x := by
  intro x hx
  obtain ⟨hg', hd', hy', heq⟩ := Work.PSU3.canon_f h x.2 (canon3_of_C h C hx)
  exact (canon3_eq_C h C (y := C.f x) (canon_f_ne_one h C hx)
    (g := ⟨_, hg'⟩) (d := ⟨_, hd'⟩) (z := x) heq).1

/-- **H4b.** `h(x⁻¹) = h(x)`. -/
lemma canon_H3 (h : IsSplitRankOne H Q t) (hz : IsZassenhaus H) (h2 : IsPGroup 2 Q)
    (C : Work.ZassenhausPSL2.Canon H Q t) :
    ∀ x : Q, (x : G) ≠ 1 → C.h x⁻¹ = C.h x := by
  intro x hx
  obtain ⟨hg', hd', hy', heq⟩ := Work.PSU3.canon_inv h (canon3_of_C h C hx)
  have hres := canon3_eq_C h C (y := x⁻¹) (canon_inv_ne_one hx)
    (g := ⟨_, hg'⟩) (d := ⟨_, hd'⟩) (z := ⟨_, hy'⟩) heq
  refine Subtype.ext ?_
  rw [show ((C.h x⁻¹ : twoPoint H t) : G) = t * ((C.h x : twoPoint H t) : G)⁻¹ * t from
        congrArg Subtype.val hres.2.2,
      canon_t_conj_invD_inv h hz h2 (C.h x).2]

/-- **the `g(f y)` identity.** `g(f(y)) = h(y)⁻¹ g(y)⁻¹ h(y)`. -/
lemma canon_gf (h : IsSplitRankOne H Q t) (C : Work.ZassenhausPSL2.Canon H Q t) :
    ∀ y : Q, (y : G) ≠ 1 →
      ((C.g (C.f y) : Q) : G)
        = ((C.h y : twoPoint H t) : G)⁻¹ * ((C.g y : Q) : G)⁻¹
          * ((C.h y : twoPoint H t) : G) := by
  intro y hy
  obtain ⟨hg', hd', hy', heq⟩ := Work.PSU3.canon_f h y.2 (canon3_of_C h C hy)
  exact congrArg Subtype.val (canon3_eq_C h C (y := C.f y) (canon_f_ne_one h C hy)
    (g := ⟨_, hg'⟩) (d := ⟨_, hd'⟩) (z := y) heq).2.1

/-- **~H5 (HB 11.10b(5)).** `f(g x) = h(x)⁻¹ f(x)⁻¹ h(x)`. -/
lemma canon_H4 (h : IsSplitRankOne H Q t) (hz : IsZassenhaus H) (h2 : IsPGroup 2 Q)
    (C : Work.ZassenhausPSL2.Canon H Q t) :
    ∀ x : Q, (x : G) ≠ 1 →
      ((C.f (C.g x) : Q) : G)
        = ((C.h x : twoPoint H t) : G)⁻¹ * ((C.f x : Q) : G)⁻¹
          * ((C.h x : twoPoint H t) : G) := by
  intro x hx
  have hgne : ((C.g x : Q) : G) ≠ 1 := by
    intro hc
    have h1 := canon_H1 h C x hx
    have h2' := canon_f_ne_one h C (canon_inv_ne_one hx)
    rw [← h1] at h2'
    exact h2' (by simp [hc])
  have hG1 := canon_gf h C x⁻¹ (canon_inv_ne_one hx)
  have hfg : C.f x⁻¹ = (C.g x)⁻¹ := (canon_H1 h C x hx).symm
  have hgh : C.h x⁻¹ = C.h x := canon_H3 h hz h2 C x hx
  have hginv : ((C.g x⁻¹ : Q) : G)⁻¹ = ((C.f x : Q) : G) := by
    have h1 := canon_H1 h C x⁻¹ (canon_inv_ne_one hx)
    have h1' : ((C.g x⁻¹ : Q)⁻¹) = C.f x := by simpa using h1
    simpa only [Subgroup.coe_inv] using congrArg Subtype.val h1'
  rw [hfg, hgh, hginv] at hG1
  have hcp : C.f (C.g x) = (C.g ((C.g x)⁻¹))⁻¹ := by
    have h1 := canon_H1 h C ((C.g x)⁻¹) (canon_inv_ne_one hgne)
    rw [inv_inv] at h1
    exact h1.symm
  calc ((C.f (C.g x) : Q) : G) = (((C.g ((C.g x)⁻¹)) : Q) : G)⁻¹ := by
        rw [hcp]; simp only [Subgroup.coe_inv]
    _ = (((C.h x : twoPoint H t) : G)⁻¹ * ((C.f x : Q) : G)
          * ((C.h x : twoPoint H t) : G))⁻¹ := by rw [hG1]
    _ = ((C.h x : twoPoint H t) : G)⁻¹ * ((C.f x : Q) : G)⁻¹
          * ((C.h x : twoPoint H t) : G) := by group

/-- **H3.** `f(x^d) = f(x)^{d⁻¹}` for `d ∈ D`, i.e. `f(d x d⁻¹) = d⁻¹ f(x) d`. -/
lemma canon_H5 (h : IsSplitRankOne H Q t) (hz : IsZassenhaus H) (h2 : IsPGroup 2 Q)
    (C : Work.ZassenhausPSL2.Canon H Q t) :
    ∀ (d : twoPoint H t) (x : Q), (x : G) ≠ 1 →
      ∀ (hd : (d : G) * (x : G) * (d : G)⁻¹ ∈ Q)
        (hd' : (d : G)⁻¹ * ((C.f x : Q) : G) * (d : G) ∈ Q),
      C.f ⟨(d : G) * (x : G) * (d : G)⁻¹, hd⟩
        = ⟨(d : G)⁻¹ * ((C.f x : Q) : G) * (d : G), hd'⟩ := by
  intro d x hx hd hd'
  have h_tat : t * (d : G)⁻¹ * t = (d : G) := canon_t_conj_invD_inv h hz h2 d.2
  have hyne : ((⟨(d : G) * (x : G) * (d : G)⁻¹, hd⟩ : Q) : G) ≠ 1 := by
    intro hc
    apply hx
    have hc' : (d : G) * (x : G) * (d : G)⁻¹ = 1 := hc
    have : (d : G)⁻¹ * ((d : G) * (x : G) * (d : G)⁻¹) * (d : G) = (x : G) := by group
    rw [hc'] at this
    simpa using this.symm
  obtain ⟨hg', hd'', hy', heq⟩ :=
    Work.PSU3.RankOne.canon_conj h (a := (d : G)⁻¹) ((twoPoint H t).inv_mem d.2)
      (canon3_of_C h C hx)
  have heq' : t * ((⟨(d : G) * (x : G) * (d : G)⁻¹, hd⟩ : Q) : G) * t
      = ((⟨(t * (d : G)⁻¹ * t)⁻¹ * ((C.g x : Q) : G) * (t * (d : G)⁻¹ * t), hg'⟩ : Q) : G)
        * ((⟨(t * (d : G)⁻¹ * t)⁻¹ * ((C.h x : twoPoint H t) : G) * (d : G)⁻¹, hd''⟩
              : twoPoint H t) : G)
        * t * ((⟨(t * (d : G)⁻¹ * t)⁻¹ * ((C.f x : Q) : G) * (t * (d : G)⁻¹ * t), hy'⟩
                : Q) : G) := by
    simpa only [Subtype.coe_mk, inv_inv] using heq
  have hres := canon3_eq_C h C (y := ⟨_, hd⟩) hyne (g := ⟨_, hg'⟩) (d := ⟨_, hd''⟩)
    (z := ⟨_, hy'⟩) heq'
  have hzeq : (⟨(t * (d : G)⁻¹ * t)⁻¹ * ((C.f x : Q) : G) * (t * (d : G)⁻¹ * t), hy'⟩ : Q)
      = ⟨(d : G)⁻¹ * ((C.f x : Q) : G) * (d : G), hd'⟩ := by
    refine Subtype.ext ?_
    simp only [Subtype.coe_mk]
    rw [h_tat]
  exact hres.1.trans hzeq

/-- **H4a.** `h(x^d) = d⁻² h(x)` for `d ∈ D`, i.e. `h(d x d⁻¹) = d⁻¹ d⁻¹ h(x)`. -/
lemma canon_H6 (h : IsSplitRankOne H Q t) (hz : IsZassenhaus H) (h2 : IsPGroup 2 Q)
    (C : Work.ZassenhausPSL2.Canon H Q t) :
    ∀ (d : twoPoint H t) (x : Q), (x : G) ≠ 1 →
      ∀ (hd : (d : G) * (x : G) * (d : G)⁻¹ ∈ Q),
      ((C.h ⟨(d : G) * (x : G) * (d : G)⁻¹, hd⟩ : twoPoint H t) : G)
        = (d : G)⁻¹ * (d : G)⁻¹ * ((C.h x : twoPoint H t) : G) := by
  intro d x hx hd
  have h_tat : t * (d : G)⁻¹ * t = (d : G) := canon_t_conj_invD_inv h hz h2 d.2
  have hyne : ((⟨(d : G) * (x : G) * (d : G)⁻¹, hd⟩ : Q) : G) ≠ 1 := by
    intro hc
    apply hx
    have hc' : (d : G) * (x : G) * (d : G)⁻¹ = 1 := hc
    have : (d : G)⁻¹ * ((d : G) * (x : G) * (d : G)⁻¹) * (d : G) = (x : G) := by group
    rw [hc'] at this
    simpa using this.symm
  obtain ⟨hg', hd'', hy', heq⟩ :=
    Work.PSU3.RankOne.canon_conj h (a := (d : G)⁻¹) ((twoPoint H t).inv_mem d.2)
      (canon3_of_C h C hx)
  have heq' : t * ((⟨(d : G) * (x : G) * (d : G)⁻¹, hd⟩ : Q) : G) * t
      = ((⟨(t * (d : G)⁻¹ * t)⁻¹ * ((C.g x : Q) : G) * (t * (d : G)⁻¹ * t), hg'⟩ : Q) : G)
        * ((⟨(t * (d : G)⁻¹ * t)⁻¹ * ((C.h x : twoPoint H t) : G) * (d : G)⁻¹, hd''⟩
              : twoPoint H t) : G)
        * t * ((⟨(t * (d : G)⁻¹ * t)⁻¹ * ((C.f x : Q) : G) * (t * (d : G)⁻¹ * t), hy'⟩
                : Q) : G) := by
    simpa only [Subtype.coe_mk, inv_inv] using heq
  have hres := canon3_eq_C h C (y := ⟨_, hd⟩) hyne (g := ⟨_, hg'⟩) (d := ⟨_, hd''⟩)
    (z := ⟨_, hy'⟩) heq'
  have hmem : (d : G)⁻¹ * (d : G)⁻¹ * ((C.h x : twoPoint H t) : G) ∈ twoPoint H t :=
    (twoPoint H t).mul_mem
      ((twoPoint H t).mul_mem ((twoPoint H t).inv_mem d.2) ((twoPoint H t).inv_mem d.2))
      (C.h x).2
  have hzeq : (⟨(t * (d : G)⁻¹ * t)⁻¹ * ((C.h x : twoPoint H t) : G) * (d : G)⁻¹, hd''⟩
        : twoPoint H t)
      = ⟨(d : G)⁻¹ * (d : G)⁻¹ * ((C.h x : twoPoint H t) : G), hmem⟩ := by
    refine Subtype.ext ?_
    simp only [Subtype.coe_mk]
    rw [h_tat]
    calc (d : G)⁻¹ * ((C.h x : twoPoint H t) : G) * (d : G)⁻¹
        = (d : G)⁻¹ * (((C.h x : twoPoint H t) : G) * (d : G)⁻¹) := by group
      _ = (d : G)⁻¹ * ((d : G)⁻¹ * ((C.h x : twoPoint H t) : G)) := by
            rw [canon_D_abelian_mul h hz h2 (C.h x).2 ((twoPoint H t).inv_mem d.2)]
      _ = (d : G)⁻¹ * (d : G)⁻¹ * ((C.h x : twoPoint H t) : G) := by group
  exact (congrArg Subtype.val hres.2.2).trans (congrArg Subtype.val hzeq)

/-- **H6 (Hua).** `f(x₁ x₂) = h(x₂) f(f(x₁) g(x₂)) h(x₂)⁻¹ f(x₂)`. -/
lemma canon_H7 (h : IsSplitRankOne H Q t) (hz : IsZassenhaus H) (h2 : IsPGroup 2 Q)
    (C : Work.ZassenhausPSL2.Canon H Q t) :
    ∀ x₁ x₂ : Q, (x₁ : G) ≠ 1 → (x₂ : G) ≠ 1 → (x₁ * x₂ : G) ≠ 1 →
      ((C.f (x₁ * x₂) : Q) : G)
        = ((C.h x₂ : twoPoint H t) : G) * ((C.f (C.f x₁ * C.g x₂) : Q) : G)
          * ((C.h x₂ : twoPoint H t) : G)⁻¹ * ((C.f x₂ : Q) : G) := by
  intro x₁ x₂ hx₁ hx₂ hx₁₂
  have hcx := canon3_of_C h C hx₁
  have hcy := canon3_of_C h C hx₂
  have hz_ne : ((C.f x₁ * C.g x₂ : Q) : G) ≠ 1 :=
    Work.PSU3.RankOne.canon_mul_ne_one h x₁.2 hx₁ x₂.2 hx₂ hcx hcy hx₁₂
  have hcz := canon3_of_C h C hz_ne
  obtain ⟨hg', hd', hy', heq⟩ := Work.PSU3.RankOne.canon_mul h hcx hcy hcz
  have hdy : t * ((C.h x₂ : twoPoint H t) : G) * t = ((C.h x₂ : twoPoint H t) : G)⁻¹ :=
    canon_t_conj_inv_D h hz h2 (C.h x₂).2
  have hxyne : ((x₁ * x₂ : Q) : G) ≠ 1 := hx₁₂
  have hres := canon3_eq_C h C (y := x₁ * x₂) hxyne (g := ⟨_, hg'⟩) (d := ⟨_, hd'⟩)
    (z := ⟨_, hy'⟩) heq
  have hmem : ((C.h x₂ : twoPoint H t) : G) * ((C.f (C.f x₁ * C.g x₂) : Q) : G)
      * ((C.h x₂ : twoPoint H t) : G)⁻¹ * ((C.f x₂ : Q) : G) ∈ Q :=
    Q.mul_mem (canon_D_conj_Q_mem h (C.h x₂) (C.f (C.f x₁ * C.g x₂))) (C.f x₂).2
  have hzeq : (⟨(t * ((C.h x₂ : twoPoint H t) : G) * t)⁻¹ * ((C.f (C.f x₁ * C.g x₂) : Q) : G)
          * (t * ((C.h x₂ : twoPoint H t) : G) * t) * ((C.f x₂ : Q) : G), hy'⟩ : Q)
      = ⟨((C.h x₂ : twoPoint H t) : G) * ((C.f (C.f x₁ * C.g x₂) : Q) : G)
          * ((C.h x₂ : twoPoint H t) : G)⁻¹ * ((C.f x₂ : Q) : G), hmem⟩ := by
    refine Subtype.ext ?_
    simp only [Subtype.coe_mk]
    rw [hdy, inv_inv]
  exact (congrArg Subtype.val hres.1).trans (congrArg Subtype.val hzeq)

end Work.ZassenhausSuzuki
