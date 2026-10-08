import Mathlib
import Submission.Work.ZassenhausSuzuki.TitsDefs
import Submission.Work.ZassenhausSuzuki.szTildeAux
import Submission.Work.ZassenhausSuzuki.canon_aux
import Submission.Work.ZassenhausSuzuki.hG_tilde_eq
import Submission.Work.ZassenhausSuzuki.hG_conj_gG_eq_tilde

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausSuzuki.mu_conj_mul_inv_zs`

The unproved-free, self-contained proof of BG 3.1 (l) in the workspace's left-action vocabulary
(the design copy `Work.ZassenhausSuzuki.TitsDesign.mu_conj_mul_inv'` is a `unproved` placeholder
and is *not* used).  The only inputs are the canonical relations H1, H2, H3, H6
(`canon_aux`), `hG_f` (`hG_tilde_eq`), `canon_g_g` (`hG_conj_gG_eq_tilde`), the
`D`-component formula `canon_H8` (proved in `TitsDesign`, `#print axioms` clean), the
abelianness of `D` (`canon_D_abelian_mul`) and the definition of `muPt`.

Route (as in the design note): with `η := h a = h b`, `x₁ := (μ_a b)⁻¹`, `x₂ := μ_a a`,
H1/H2/`canon_g_g` give `f x₁ = (η b η⁻¹)⁻¹` and `g x₂ = η a η⁻¹`, so
`f x₁ · g x₂ = η (b⁻¹a) η⁻¹`, and H6 gives `h(f x₁ g x₂) = η⁻¹ η⁻¹ h(b⁻¹a)`, while
`h x₁ = h x₂ = η`.  `canon_H8` then gives `h(x₁x₂) = η η⁻¹η⁻¹h(b⁻¹a) η = h(b⁻¹a)` because
`D` is abelian.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausSuzuki

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-- **Peterfalvi (H4c), `g`-form**: `h(g x) = h(x)⁻¹` for `x ∈ Q#`.  Derived from H1
(`(g x)⁻¹ = f(x⁻¹)`), H3 (`h(y⁻¹) = h(y)`) and `hG_f`. -/
theorem mu_zs_hG_g (hsplit : IsSplitRankOne H Q t) (hzass : IsZassenhaus H)
    (h2 : IsPGroup 2 Q) (C : Work.ZassenhausPSL2.Canon H Q t) {x : Q} (hx : (x : G) ≠ 1) :
    hG C (C.g x) = (hG C x)⁻¹ := by
  have hxinv : ((x⁻¹ : Q) : G) ≠ 1 := canon_inv_ne_one hx
  have hfx : ((C.f x⁻¹ : Q) : G) ≠ 1 := canon_f_ne_one hsplit C hxinv
  have h1 : C.g x = (C.f x⁻¹)⁻¹ := by
    have h := canon_H1 hsplit C x hx
    simpa using congrArg Inv.inv h
  calc hG C (C.g x) = hG C ((C.f x⁻¹)⁻¹) := by rw [h1]
    _ = hG C (C.f x⁻¹) := by
        rw [show hG C ((C.f x⁻¹)⁻¹) = hG C (C.f x⁻¹) from
          congrArg (fun z : ↥(twoPoint H t) => (z : G))
            (canon_H3 hsplit hzass h2 C (C.f x⁻¹) hfx)]
    _ = (hG C x⁻¹)⁻¹ := hG_f hsplit C hxinv
    _ = (hG C x)⁻¹ := by
        rw [show hG C x⁻¹ = hG C x from
          congrArg (fun z : ↥(twoPoint H t) => (z : G)) (canon_H3 hsplit hzass h2 C x hx)]

/-- **BG 3.1 (l), corrected order** (`NOTES_LEAD_bs_zs_tits.md` §0.2; design copy
`Work.ZassenhausSuzuki.TitsDesign.mu_conj_mul_inv'`).  With the workspace's *left* action the
correct form is `h(b'⁻¹·w) = h(b⁻¹·a)`; here `w = μ_a(a)`, `b' = μ_a(b)`: for `a ≠ b` with
`h a = h b`, `h((μ_a b)⁻¹·μ_a a) = h(b⁻¹·a)`, where `μ_a y = g(h a · y · (h a)⁻¹)` is `muPt`.
Route: `canon_H8` at `(μ_a(b)⁻¹, μ_a(a))`, `f x₁ g x₂ = η(b⁻¹a)η⁻¹` with `η = h a`, and H6.
Do not close the goal by citing `TitsDesign.mu_conj_mul_inv'` (it is a `unproved` placeholder):
check `#print axioms` of your lemma. -/
theorem mu_conj_mul_inv_zs {G : Type} [Group G] [Finite G]
    {H Q : Subgroup G} {t : G} (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    (C : Work.ZassenhausPSL2.Canon H Q t) {a b : Q}
    (ha1 : (a : G) ≠ 1) (hb1 : (b : G) ≠ 1) (hab : a ≠ b)
    (hmu : Work.ZassenhausSuzuki.hG C a = Work.ZassenhausSuzuki.hG C b) :
    Work.ZassenhausSuzuki.hG C
        ((Work.ZassenhausSuzuki.TitsDesign.muPt hsplit C a b)⁻¹ *
          Work.ZassenhausSuzuki.TitsDesign.muPt hsplit C a a)
      = Work.ZassenhausSuzuki.hG C (b⁻¹ * a) := by
  classical
  -- notation: `η = h a`, `qa = h a · a · (h a)⁻¹`, `qb = h a · b · (h a)⁻¹`
  set η : G := hG C a with hηdef
  set qa : Q := TitsDesign.conjH hsplit C a a with hqadef
  set qb : Q := TitsDesign.conjH hsplit C a b with hqbdef
  have hqaG : (qa : G) = η * (a : G) * η⁻¹ := by rw [hqadef, hηdef]; rfl
  have hqbG : (qb : G) = η * (b : G) * η⁻¹ := by rw [hqbdef, hηdef]; rfl
  -- the conjugates are non-trivial
  have hqa_ne : qa ≠ 1 := by
    intro h
    have h' : (qa : G) = 1 := by rw [h]; rfl
    rw [hqaG] at h'
    have haG : (a : G) = 1 := by
      calc (a : G) = η⁻¹ * (η * (a : G) * η⁻¹) * η := by group
        _ = η⁻¹ * 1 * η := by rw [h']
        _ = 1 := by group
    exact ha1 haG
  have hqb_ne : qb ≠ 1 := by
    intro h
    have h' : (qb : G) = 1 := by rw [h]; rfl
    rw [hqbG] at h'
    have hbG : (b : G) = 1 := by
      calc (b : G) = η⁻¹ * (η * (b : G) * η⁻¹) * η := by group
        _ = η⁻¹ * 1 * η := by rw [h']
        _ = 1 := by group
    exact hb1 hbG
  have hqa_ne' : (qa : G) ≠ 1 := fun h => hqa_ne (Subtype.ext h)
  have hqb_ne' : (qb : G) ≠ 1 := fun h => hqb_ne (Subtype.ext h)
  -- H6 at the two conjugates
  have hqa_h : hG C qa = η⁻¹ * η⁻¹ * η := by
    have h6 := canon_H6 hsplit hzass h2 C (C.h a) a ha1 (canon_D_conj_Q_mem hsplit (C.h a) a)
    simpa only [hqadef, hG, TitsDesign.conjH, hηdef] using h6
  have hqb_h : hG C qb = η⁻¹ * η⁻¹ * hG C b := by
    have h6 := canon_H6 hsplit hzass h2 C (C.h a) b hb1 (canon_D_conj_Q_mem hsplit (C.h a) b)
    simpa only [hqbdef, hG, TitsDesign.conjH, hηdef] using h6
  have hqa_h' : hG C qa = η⁻¹ := by rw [hqa_h]; group
  have hqb_h' : hG C qb = η⁻¹ := by rw [hqb_h, ← hmu]; group
  -- the two factors `x₂ = g qa`, `x₁ = (g qb)⁻¹` both have `h`-coordinate `η`
  have hx2_h : hG C (C.g qa) = η := by
    rw [mu_zs_hG_g hsplit hzass h2 C hqa_ne', hqa_h']; group
  have hx1_h : hG C ((C.g qb)⁻¹) = η := by
    rw [show hG C ((C.g qb)⁻¹) = hG C (C.g qb) from
      congrArg (fun z : ↥(twoPoint H t) => (z : G))
        (canon_H3 hsplit hzass h2 C (C.g qb) (canon_g_ne_one hsplit hzass h2 C hqb_ne'))]
    rw [mu_zs_hG_g hsplit hzass h2 C hqb_ne', hqb_h']; group
  -- H1 and H2 identify `f x₁`, `canon_g_g` identifies `g x₂`
  have hfx1 : C.f ((C.g qb)⁻¹) = qb⁻¹ := by
    have h1 := canon_H1 hsplit C qb hqb_ne'
    have h2 := canon_H2 hsplit C qb⁻¹ (canon_inv_ne_one hqb_ne')
    rw [← h1] at h2
    exact h2
  have hgx2 : C.g (C.g qa) = qa := canon_g_g hsplit hzass h2 C hqa_ne'
  -- side conditions for `canon_H8`
  have hx1ne : ((((C.g qb)⁻¹ : Q)) : G) ≠ 1 :=
    canon_inv_ne_one (canon_g_ne_one hsplit hzass h2 C hqb_ne')
  have hx2ne : ((C.g qa : Q) : G) ≠ 1 := canon_g_ne_one hsplit hzass h2 C hqa_ne'
  have hx12ne : ((((C.g qb)⁻¹ * C.g qa : Q)) : G) ≠ 1 := by
    intro h
    have hQ : (C.g qb)⁻¹ * C.g qa = 1 := Subtype.ext h
    have hg : C.g qb = C.g qa := inv_mul_eq_one.mp hQ
    have hqab : qb = qa := by
      have hh := congrArg (fun z : Q => C.g z) hg
      rwa [canon_g_g hsplit hzass h2 C hqb_ne', canon_g_g hsplit hzass h2 C hqa_ne'] at hh
    have hba : (b : G) = (a : G) := by
      have hh := congrArg (fun z : Q => (z : G)) hqab
      rw [hqbG, hqaG] at hh
      have hh2 := congrArg (fun z : G => η⁻¹ * z * η) hh
      simpa using hh2
    exact hab (Subtype.ext hba).symm
  have hbain_ne : (((b⁻¹ * a : Q)) : G) ≠ 1 := by
    intro h
    have hQ : b⁻¹ * a = 1 := Subtype.ext h
    have : a = b := by
      have := congrArg (fun z : Q => b * z) hQ
      simpa using this
    exact hab this
  -- H6 in the middle
  have hmid : hG C (qb⁻¹ * qa) = η⁻¹ * η⁻¹ * hG C (b⁻¹ * a) := by
    have h6 := canon_H6 hsplit hzass h2 C (C.h a) (b⁻¹ * a) hbain_ne
      (canon_D_conj_Q_mem hsplit (C.h a) (b⁻¹ * a))
    have hqe : qb⁻¹ * qa
        = (⟨η * (((b⁻¹ * a : Q)) : G) * η⁻¹,
            canon_D_conj_Q_mem hsplit (C.h a) (b⁻¹ * a)⟩ : Q) := by
      apply Subtype.ext
      show (qb : G)⁻¹ * (qa : G) = η * (((b⁻¹ * a : Q)) : G) * η⁻¹
      rw [hqbG, hqaG]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [hqe]
    simpa only [hG, hηdef] using h6
  -- the product `(g qb)⁻¹ · (g qa)` and `canon_H8`
  have hgoal1 : hG C ((C.g qb)⁻¹ * C.g qa) = hG C (b⁻¹ * a) := by
    rw [TitsDesign.canon_H8 hsplit hzass h2 C ((C.g qb)⁻¹) (C.g qa) hx1ne hx2ne hx12ne]
    rw [hx1_h, hfx1, hgx2, hx2_h, hmid]
    have hcomm : hG C (b⁻¹ * a) * η = η * hG C (b⁻¹ * a) := by
      have := canon_D_abelian_mul hsplit hzass h2 (C.h (b⁻¹ * a)).2 (C.h a).2
      simpa only [hG, hηdef] using this
    calc η * (η⁻¹ * η⁻¹ * hG C (b⁻¹ * a)) * η
        = η⁻¹ * (hG C (b⁻¹ * a) * η) := by group
      _ = η⁻¹ * (η * hG C (b⁻¹ * a)) := by rw [hcomm]
      _ = hG C (b⁻¹ * a) := by group
  -- `muPt` unfolds to the `g`-image of the conjugate
  have hmuPtb : TitsDesign.muPt hsplit C a b = C.g qb := by rw [hqbdef]; rfl
  have hmuPta : TitsDesign.muPt hsplit C a a = C.g qa := by rw [hqadef]; rfl
  rw [hmuPtb, hmuPta]
  exact hgoal1

end Work.ZassenhausSuzuki
