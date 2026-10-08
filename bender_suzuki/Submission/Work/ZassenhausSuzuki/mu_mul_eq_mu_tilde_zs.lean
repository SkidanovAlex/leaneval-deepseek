import Mathlib
import Submission.Work.ZassenhausSuzuki.canon_aux
import Submission.Work.ZassenhausSuzuki.canon_H8
import Submission.Work.ZassenhausSuzuki.szTildeAux
import Submission.Work.ZassenhausSuzuki.hG_tilde_eq
import Submission.Work.ZassenhausSuzuki.hG_conj_gG_eq_tilde
import Submission.Work.ZassenhausSuzuki.DtwoPoint_regular_on_involutions
import Submission.Work.ZassenhausSuzuki.f_tilde_zs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki

/-!
# The `δ`-trick of BG 5.11

Toolkit for `mu_mul_eq_mu_tilde_zs` below: the `D`-conjugate `x^★ := h(x)·x·h(x)⁻¹` of an
element of the root group, its behaviour under the canonical maps `f`, `g`, `h` (H1–H6,
`canon_H8`), and the computation of `h(b^★·a^★)`.

The whole argument is contained in this file, on top of the delivered
`canon_aux` (H1–H7), `canon_H8` (H8), `szTildeAux`, `hG_tilde_eq`, `hG_conj_gG_eq_tilde`,
`DtwoPoint_regular_on_involutions` (regularity of `D` on `Inv(Q)`) and `f_tilde_zs`
(BG 3.1 (e): `f(∼x) = h(x)·x·h(x)⁻¹`).
-/

namespace Muzs

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-- `x^★ := h(x)·x·h(x)⁻¹`, the `D`-conjugate of `x` by its own canonical `D`-part. -/
noncomputable def starD (hsplit : IsSplitRankOne H Q t) (C : Work.ZassenhausPSL2.Canon H Q t)
    (x : Q) : Q :=
  ⟨hG C x * (x : G) * (hG C x)⁻¹, canon_D_conj_Q_mem hsplit (C.h x) x⟩

@[simp] theorem starD_coe (hsplit : IsSplitRankOne H Q t)
    (C : Work.ZassenhausPSL2.Canon H Q t) (x : Q) :
    ((starD hsplit C x : Q) : G) = hG C x * (x : G) * (hG C x)⁻¹ := rfl

/-- `x^★` is an involution as soon as `x` is. -/
theorem starD_mul_self (hsplit : IsSplitRankOne H Q t)
    (C : Work.ZassenhausPSL2.Canon H Q t) {x : Q} (hx : x * x = 1) :
    starD hsplit C x * starD hsplit C x = 1 := by
  apply Subtype.ext
  have hxG : (x : G) * (x : G) = 1 := by rw [← Subgroup.coe_mul, hx]; rfl
  show (hG C x * (x : G) * (hG C x)⁻¹) * (hG C x * (x : G) * (hG C x)⁻¹) = (1 : G)
  rw [show (hG C x * (x : G) * (hG C x)⁻¹) * (hG C x * (x : G) * (hG C x)⁻¹)
        = hG C x * ((x : G) * (x : G)) * (hG C x)⁻¹ from by group, hxG]
  group

/-- `x^★ ≠ 1` for `x ≠ 1`. -/
theorem starD_ne_one (hsplit : IsSplitRankOne H Q t)
    (C : Work.ZassenhausPSL2.Canon H Q t) {x : Q} (hx : x ≠ 1) :
    starD hsplit C x ≠ 1 := by
  intro h
  apply hx
  apply Subtype.ext
  have hc : hG C x * (x : G) * (hG C x)⁻¹ = 1 := by
    have := congrArg (fun z : Q => (z : G)) h
    simpa using this
  show (x : G) = 1
  calc (x : G) = (hG C x)⁻¹ * (hG C x * (x : G) * (hG C x)⁻¹) * (hG C x) := by group
    _ = 1 := by rw [hc]; group

/-- **BG 3.1 (i) at `x^★`** (H6): `h(x^★) = h(x)⁻¹`. -/
theorem hG_starD (hsplit : IsSplitRankOne H Q t) (hzass : IsZassenhaus H)
    (h2 : IsPGroup 2 Q) (C : Work.ZassenhausPSL2.Canon H Q t) {x : Q} (hx : (x : G) ≠ 1) :
    hG C (starD hsplit C x) = (hG C x)⁻¹ := by
  have h := canon_H6 hsplit hzass h2 C (C.h x) x hx (canon_D_conj_Q_mem hsplit (C.h x) x)
  simpa [starD, hG] using h

/-- **BG 3.1 (e)**: `f(∼x) = x^★` (`f_tilde_zs`, in the `starD` notation). -/
theorem f_tilde_starD (hsplit : IsSplitRankOne H Q t) (hzass : IsZassenhaus H)
    (h2 : IsPGroup 2 Q) (C : Work.ZassenhausPSL2.Canon H Q t) {x : Q} (hx : (x : G) ≠ 1) :
    C.f (tildeOf C x) = starD hsplit C x := by
  apply Subtype.ext
  rw [starD_coe]
  exact f_tilde_zs hsplit hzass h2 C hx

/-- `g((∼a)⁻¹) = a^★` for an involution `a ≠ 1`: H1 (`(g y)⁻¹ = f(y⁻¹)`) at `y = (∼a)⁻¹`,
`f(∼a) = a^★` and `(a^★)² = 1`. -/
theorem g_inv_tilde_starD (hsplit : IsSplitRankOne H Q t) (hzass : IsZassenhaus H)
    (h2 : IsPGroup 2 Q) (C : Work.ZassenhausPSL2.Canon H Q t) {a : Q}
    (ha1 : (a : G) ≠ 1) (ha2 : a * a = 1) :
    C.g ((tildeOf C a)⁻¹) = starD hsplit C a := by
  have hτne : ((tildeOf C a : Q) : G) ≠ 1 :=
    fun h => tildeOf_ne_one hsplit hzass h2 C ha1 (Subtype.ext h)
  have h1 := canon_H1 hsplit C ((tildeOf C a)⁻¹) (canon_inv_ne_one hτne)
  rw [inv_inv] at h1
  calc C.g ((tildeOf C a)⁻¹)
      = ((C.g ((tildeOf C a)⁻¹))⁻¹)⁻¹ := (inv_inv _).symm
    _ = (C.f (tildeOf C a))⁻¹ := by rw [h1]
    _ = (starD hsplit C a)⁻¹ := by rw [f_tilde_starD hsplit hzass h2 C ha1]
    _ = starD hsplit C a := inv_eq_of_mul_eq_one_left (starD_mul_self hsplit C ha2)

/-- `h((∼a)⁻¹) = h(a)` for `a ≠ 1`: H4b `h(x⁻¹) = h(x)` at `x = ∼a` and BG 3.1 (i). -/
theorem hG_inv_tilde_starD (hsplit : IsSplitRankOne H Q t) (hzass : IsZassenhaus H)
    (h2 : IsPGroup 2 Q) (C : Work.ZassenhausPSL2.Canon H Q t) {a : Q} (ha1 : (a : G) ≠ 1) :
    hG C ((tildeOf C a)⁻¹) = hG C a := by
  have hτne : ((tildeOf C a : Q) : G) ≠ 1 :=
    fun h => tildeOf_ne_one hsplit hzass h2 C ha1 (Subtype.ext h)
  have h3 := canon_H3 hsplit hzass h2 C (tildeOf C a) hτne
  have h3' : ((C.h ((tildeOf C a)⁻¹) : twoPoint H t) : G)
      = ((C.h (tildeOf C a) : twoPoint H t) : G) := congrArg Subtype.val h3
  show ((C.h ((tildeOf C a)⁻¹) : twoPoint H t) : G) = ((C.h a : twoPoint H t) : G)
  rw [h3']
  exact hG_tilde_eq hsplit hzass h2 C ha1

/-- `∼` is injective on `Q ∖ {1}`: `∼x = g((g x)⁻¹)` and `g∘g = id` on `Q#`. -/
theorem tildeOf_injOn (hsplit : IsSplitRankOne H Q t) (hzass : IsZassenhaus H)
    (h2 : IsPGroup 2 Q) (C : Work.ZassenhausPSL2.Canon H Q t) {a b : Q}
    (ha1 : (a : G) ≠ 1) (hb1 : (b : G) ≠ 1) (h : tildeOf C b = tildeOf C a) : b = a := by
  have hga : ((C.g a : Q) : G) ≠ 1 := canon_g_ne_one hsplit hzass h2 C ha1
  have hgb : ((C.g b : Q) : G) ≠ 1 := canon_g_ne_one hsplit hzass h2 C hb1
  have hgain : (((C.g a)⁻¹ : Q) : G) ≠ 1 := by
    simp only [Subgroup.coe_inv]; exact inv_ne_one.mpr hga
  have hgbin : (((C.g b)⁻¹ : Q) : G) ≠ 1 := by
    simp only [Subgroup.coe_inv]; exact inv_ne_one.mpr hgb
  have h1 : C.g ((C.g b)⁻¹) = C.g ((C.g a)⁻¹) := by
    have hh := h
    simp only [tildeOf, ite_eq_right hb1, ite_eq_right ha1] at hh
    exact hh
  have e1 : C.g (C.g ((C.g b)⁻¹)) = (C.g b)⁻¹ := canon_g_g hsplit hzass h2 C hgbin
  have e2 : C.g (C.g ((C.g a)⁻¹)) = (C.g a)⁻¹ := canon_g_g hsplit hzass h2 C hgain
  have key : (C.g b)⁻¹ = (C.g a)⁻¹ := by rw [← e1, ← e2, h1]
  have key2 : C.g b = C.g a := inv_inj.mp key
  calc b = C.g (C.g b) := (canon_g_g hsplit hzass h2 C hb1).symm
    _ = C.g (C.g a) := by rw [key2]
    _ = a := canon_g_g hsplit hzass h2 C ha1

/-- **The `δ`-trick of BG 5.11**: `h(b^★·a^★) = (h a)⁻¹·(h b)⁻¹·h(a·b)` for distinct
non-trivial involutions `a, b ∈ Q`.

Let `d ∈ D` be the unique element with `d a d⁻¹ = b` (regularity of `D` on `Inv(Q)`) and put
`δ := h(b)·d ∈ D`.  Then `h(a) = d²·h(b)` (H6 at `(d,a)` together with `d a d⁻¹ = b`), and with
`D` abelian:
* `δ a δ⁻¹ = h(b)·(d a d⁻¹)·h(b)⁻¹ = b^★`,
* `δ b δ⁻¹ = h(b)·d b d⁻¹·h(b)⁻¹ = (h(b)·d²)·a·(h(b)·d²)⁻¹ = h(a)·a·h(a)⁻¹ = a^★`,
* `δ² = h(b)·h(a)`.

Hence `δ·(ab)·δ⁻¹ = b^★·a^★`, and H6 at `(δ, ab)` gives
`h(b^★·a^★) = δ⁻²·h(ab) = (h a)⁻¹(h b)⁻¹h(a·b)`. -/
theorem hG_starD_mul_starD (hsplit : IsSplitRankOne H Q t) (hzass : IsZassenhaus H)
    (h2 : IsPGroup 2 Q) (C : Work.ZassenhausPSL2.Canon H Q t) {a b : Q}
    (ha1 : a ≠ 1) (ha2 : a * a = 1) (hb1 : b ≠ 1) (hb2 : b * b = 1) (hne : a ≠ b) :
    hG C (starD hsplit C b * starD hsplit C a)
      = (hG C a)⁻¹ * (hG C b)⁻¹ * hG C (a * b) := by
  classical
  have haG : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hbG : (b : G) ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hbG2 : (b : G) * (b : G) = 1 := by rw [← Subgroup.coe_mul, hb2]; rfl
  -- the unique `d ∈ D` with `d a d⁻¹ = b`
  obtain ⟨d, hdz, -⟩ := DtwoPoint_regular_on_involutions hsplit hzass h2 ha1 ha2 hb1 hb2
  -- `D` is abelian
  have hDab : ∀ u v : twoPoint H t, (u : G) * (v : G) = (v : G) * (u : G) :=
    fun u v => canon_D_abelian_mul hsplit hzass h2 u.2 v.2
  -- H6 at `(d, a)`: `h b = d⁻² h a`
  have hdQ : (d : G) * (a : G) * (d : G)⁻¹ ∈ Q := canon_D_conj_Q_mem hsplit d a
  have h6a := canon_H6 hsplit hzass h2 C d a haG hdQ
  have hb_eq : (⟨(d : G) * (a : G) * (d : G)⁻¹, hdQ⟩ : Q) = b := Subtype.ext hdz
  have h6b : ((C.h b : twoPoint H t) : G)
      = (d : G)⁻¹ * (d : G)⁻¹ * ((C.h a : twoPoint H t) : G) := by
    rw [← hb_eq]; exact h6a
  -- `h a = d² · h b`
  have hd2 : hG C a = (d : G) * (d : G) * hG C b := by
    show ((C.h a : twoPoint H t) : G) = (d : G) * (d : G) * ((C.h b : twoPoint H t) : G)
    rw [h6b]; group
  have hkey2 : hG C b * ((d : G) * (d : G)) = hG C a := by
    rw [hd2]
    exact hDab (C.h b) ⟨(d : G) * (d : G), (twoPoint H t).mul_mem d.2 d.2⟩
  -- `δ := h(b)·d ∈ D`
  set δ : twoPoint H t := ⟨hG C b * (d : G), (twoPoint H t).mul_mem (C.h b).2 d.2⟩ with hδdef
  have hδval : (δ : G) = hG C b * (d : G) := rfl
  have hδa : (δ : G) * (a : G) * (δ : G)⁻¹ = (starD hsplit C b : G) := by
    rw [hδval]
    show hG C b * (d : G) * (a : G) * (hG C b * (d : G))⁻¹
        = hG C b * (b : G) * (hG C b)⁻¹
    rw [← hdz]
    group
  have hδ2 : (δ : G) * (δ : G) = hG C b * hG C a := by
    rw [hδval]
    have hcomm : hG C b * (d : G) = (d : G) * hG C b := hDab (C.h b) d
    have hcomm2 : hG C b * ((d : G) * (d : G)) = ((d : G) * (d : G)) * hG C b :=
      hDab (C.h b) ⟨(d : G) * (d : G), (twoPoint H t).mul_mem d.2 d.2⟩
    calc (hG C b * (d : G)) * (hG C b * (d : G))
        = hG C b * (hG C b * ((d : G) * (d : G))) := by
          rw [show hG C b * (d : G) * (hG C b * (d : G))
                = hG C b * ((d : G) * hG C b) * (d : G) from by group, ← hcomm]
          group
      _ = hG C b * (((d : G) * (d : G)) * hG C b) := by rw [hcomm2]
      _ = hG C b * hG C a := by rw [hd2]
  have hδb : (δ : G) * (b : G) * (δ : G)⁻¹ = (starD hsplit C a : G) := by
    rw [hδval]
    show hG C b * (d : G) * (b : G) * (hG C b * (d : G))⁻¹
        = hG C a * (a : G) * (hG C a)⁻¹
    rw [← hdz]
    rw [show hG C b * (d : G) * ((d : G) * (a : G) * (d : G)⁻¹) * (hG C b * (d : G))⁻¹
          = (hG C b * ((d : G) * (d : G))) * (a : G)
              * (hG C b * ((d : G) * (d : G)))⁻¹ from by group,
        hkey2]
  -- the product `a·b` is non-trivial
  have habG : ((a * b : Q) : G) ≠ 1 := by
    intro h
    have h' : (a : G) * (b : G) = 1 := by rw [← Subgroup.coe_mul]; exact h
    have : (a : G) = (b : G) := by
      calc (a : G) = (a : G) * ((b : G) * (b : G)) := by rw [hbG2, mul_one]
        _ = ((a : G) * (b : G)) * (b : G) := by group
        _ = (b : G) := by rw [h', one_mul]
    exact hne (Subtype.ext this)
  -- `δ (ab) δ⁻¹ = b^★ · a^★`
  have hdQab : (δ : G) * ((a * b : Q) : G) * (δ : G)⁻¹ ∈ Q := canon_D_conj_Q_mem hsplit δ (a * b)
  have hconj : (⟨(δ : G) * ((a * b : Q) : G) * (δ : G)⁻¹, hdQab⟩ : Q)
      = starD hsplit C b * starD hsplit C a := by
    apply Subtype.ext
    show (δ : G) * ((a * b : Q) : G) * (δ : G)⁻¹
        = (starD hsplit C b : G) * (starD hsplit C a : G)
    rw [Subgroup.coe_mul, ← hδa, ← hδb]
    group
  -- the `δ`-trick
  have h6 := canon_H6 hsplit hzass h2 C δ (a * b) habG hdQab
  have h6' : hG C (starD hsplit C b * starD hsplit C a)
      = (δ : G)⁻¹ * (δ : G)⁻¹ * hG C (a * b) := by
    rw [← hconj]
    exact h6
  rw [h6']
  rw [show (δ : G)⁻¹ * (δ : G)⁻¹ = ((δ : G) * (δ : G))⁻¹ from by group, hδ2]
  group

end Muzs

/-- **BG 5.11, corrected order** (`NOTES_LEAD_bs_zs_tits.md` §0.1, §1; design copy
`Work.ZassenhausSuzuki.TitsDesign.mu_mul_eq_mu_tilde'`): `h(a·b) = h(∼b·(∼a)⁻¹)` for distinct
central involutions `a, b` of `Q` (the workspace's left action mirrors BG's right action, which
is why the unprimed statement is false).  Route: `canon_H8` at `(∼b, (∼a)⁻¹)` gives
`h(∼b(∼a)⁻¹) = h b · h(a*b*) · h a` with `z* = h z · z · (h z)⁻¹`; the `δ`-trick (`δ(z)² = h z`,
`D` of odd order, `h(a*b*)` independent of the choice by H6 and regularity on `Z(Q)^#`) gives
`h(a*b*) = h a⁻¹ h b⁻¹ h(ab)`.  Do not close the goal by citing the `unproved` placeholders in
`TitsDesign`; check `#print axioms` of your lemma. -/
theorem mu_mul_eq_mu_tilde_zs {G : Type} [Group G] [Finite G]
    {H Q : Subgroup G} {t : G} (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    (C : Work.ZassenhausPSL2.Canon H Q t) {a b : Q}
    (ha1 : a ≠ 1) (ha2 : a * a = 1) (hacen : a ∈ Subgroup.center Q)
    (hb1 : b ≠ 1) (hb2 : b * b = 1) (hbcen : b ∈ Subgroup.center Q) (hne : a ≠ b) :
    Work.ZassenhausSuzuki.hG C (a * b) =
      Work.ZassenhausSuzuki.hG C
        (Work.ZassenhausSuzuki.tildeOf C b * (Work.ZassenhausSuzuki.tildeOf C a)⁻¹) := by
  classical
  have haG : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hbG : (b : G) ≠ 1 := fun h => hb1 (Subtype.ext h)
  -- `D` is abelian, so the `h`-parts commute
  have hcommG : ∀ x y : Q, hG C x * hG C y = hG C y * hG C x :=
    fun x y => canon_D_abelian_mul hsplit hzass h2 (C.h x).2 (C.h y).2
  -- non-degeneracy of the arguments of H8
  have hτbG : ((tildeOf C b : Q) : G) ≠ 1 :=
    fun h => tildeOf_ne_one hsplit hzass h2 C hbG (Subtype.ext h)
  have hτaG : ((tildeOf C a : Q) : G) ≠ 1 :=
    fun h => tildeOf_ne_one hsplit hzass h2 C haG (Subtype.ext h)
  have hτaiG : (((tildeOf C a)⁻¹ : Q) : G) ≠ 1 := by
    simp only [Subgroup.coe_inv]; exact inv_ne_one.mpr hτaG
  have hτab : tildeOf C b ≠ tildeOf C a :=
    fun h => hne (Muzs.tildeOf_injOn hsplit hzass h2 C haG hbG h).symm
  have hx12 : (((tildeOf C b) * (tildeOf C a)⁻¹ : Q) : G) ≠ 1 := by
    intro h
    refine hτab ?_
    have h' : (tildeOf C b : Q) * (tildeOf C a)⁻¹ = 1 := Subtype.ext h
    exact mul_inv_eq_one.mp h'
  -- H8 at `(∼b, (∼a)⁻¹)`
  have h8 := canon_H8 hsplit hzass h2 C (x₁ := tildeOf C b) (x₂ := (tildeOf C a)⁻¹)
    hτbG hτaiG hx12
  rw [hG_tilde_eq hsplit hzass h2 C hbG, Muzs.f_tilde_starD hsplit hzass h2 C hbG,
      Muzs.g_inv_tilde_starD hsplit hzass h2 C haG ha2,
      Muzs.hG_inv_tilde_starD hsplit hzass h2 C haG] at h8
  rw [h8, Muzs.hG_starD_mul_starD hsplit hzass h2 C ha1 ha2 hb1 hb2 hne]
  -- the outer `h`-factors cancel against the `δ`-trick
  have hX : hG C b * (hG C a)⁻¹ = (hG C a)⁻¹ * hG C b := by
    refine mul_left_cancel (a := hG C a) ?_
    have k1 : hG C a * (hG C b * (hG C a)⁻¹) = hG C b := by
      rw [← mul_assoc, hcommG a b, mul_assoc, mul_inv_cancel, mul_one]
    have k2 : hG C a * ((hG C a)⁻¹ * hG C b) = hG C b := by
      rw [← mul_assoc, mul_inv_cancel, one_mul]
    rw [k1, k2]
  have hprod : hG C b * (hG C a)⁻¹ * (hG C b)⁻¹ * hG C a = 1 := by
    rw [hX]; group
  have hfinal : hG C b * ((hG C a)⁻¹ * (hG C b)⁻¹ * hG C (a * b)) * hG C a = hG C (a * b) := by
    calc hG C b * ((hG C a)⁻¹ * (hG C b)⁻¹ * hG C (a * b)) * hG C a
        = hG C b * (hG C a)⁻¹ * (hG C b)⁻¹ * (hG C (a * b) * hG C a) := by group
      _ = hG C b * (hG C a)⁻¹ * (hG C b)⁻¹ * (hG C a * hG C (a * b)) := by
            rw [hcommG (a * b) a]
      _ = (hG C b * (hG C a)⁻¹ * (hG C b)⁻¹ * hG C a) * hG C (a * b) := by group
      _ = hG C (a * b) := by rw [hprod, one_mul]
  exact hfinal.symm

end Work.ZassenhausSuzuki
