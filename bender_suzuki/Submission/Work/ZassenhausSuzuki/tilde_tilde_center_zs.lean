import Mathlib
import Submission.Work.ZassenhausSuzuki.TitsDefs
import Submission.Work.ZassenhausSuzuki.szTildeAux
import Submission.Work.ZassenhausSuzuki.ttc_defs
import Submission.Work.ZassenhausSuzuki.f_tilde_zs
import Submission.Work.ZassenhausSuzuki.g_g_zs
import Submission.Work.ZassenhausSuzuki.mu_self_zs
import Submission.Work.ZassenhausSuzuki.hG_tilde_eq
import Submission.Work.ZassenhausSuzuki.canon_H8
import Submission.Work.ZassenhausSuzuki.e_d_mul
import Submission.Work.ZassenhausSuzuki.szTilde_sq
import Submission.Work.ZassenhausSuzuki.ttc_field_arith
import Submission.Work.ZassenhausSuzuki.exists_mulD_eq
import Submission.Work.ZassenhausSuzuki.szTilde_mul_formula
import Submission.Work.ZassenhausSuzuki.mulD_h_zc

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 4000000

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausSuzuki

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
variable {m : ℕ} {θ : GaloisField 2 m ≃+* GaloisField 2 m}
variable {e : Q ≃* SzA (GaloisField 2 m) θ}

/-! ## `∼` of the inverse of a reflection -/

theorem tildeOf_tildeOf_inv {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : IsSplitRankOne H Q t) (hzass : IsZassenhaus H) (h2 : IsPGroup 2 Q)
    (C : Work.ZassenhausPSL2.Canon H Q t) {x : Q} (hx : (x : G) ≠ 1) :
    tildeOf C ((tildeOf C x)⁻¹) = (tildeOf C x⁻¹)⁻¹ := by
  set u : Q := tildeOf C x with hu
  have hu1 : (u : G) ≠ 1 := fun h => tildeOf_ne_one hsplit hzass h2 C hx (Subtype.ext h)
  have hui1 : (((u⁻¹ : Q)) : G) ≠ 1 := canon_inv_ne_one hu1
  have h1 : tildeOf C u⁻¹ = C.g (C.f u) := by
    have hg : C.g u⁻¹ = (C.f u)⁻¹ := by
      have h := canon_H1 hsplit C u⁻¹ hui1
      rw [inv_inv] at h
      have h' := congrArg Inv.inv h
      simpa using h'
    rw [tildeOf, ite_eq_right hui1, hg, inv_inv]
  have h5 : C.g (C.f u) = (tildeOf C x⁻¹)⁻¹ := by
    have hfu : C.f u = conjHQ hsplit C x x := by
      apply Subtype.ext
      rw [hu, conjHQ_coe]
      exact f_tilde_zs hsplit hzass h2 C hx
    have hmu : muPtQ hsplit C x x = C.g (C.f u) := by
      rw [hfu]
      rfl
    have hms := mu_self_zs hsplit hzass h2 C hx
    rw [← hmu]
    exact hms
  rw [h1, h5]

/-! ## The `∼`-product formula -/

/-- **The `∼`-product formula** (`NOTES_LEAD_bs_zs_tits.md` §1; design copy
`Work.ZassenhausSuzuki.TitsDesign.tilde_tilde_center`; replaces BG 5.12).  In the coordinates
`e : Q ≃* A(K,θ)` with `D = twoPoint H t` acting through the torus `Λ`,
`∼(∼z_v · (∼z_u)⁻¹) = ∼z_{v + v²/u} · (∼z_{(u+v)²/u})⁻¹` for `u, v ≠ 0`, `u ≠ v`, where
`∼x = tildeOf C x = h⁻¹ f x h` and `z_w = zc e w = e.symm ⟨0,w⟩`.
Route (H7 + H8 + `tildeOf_eq`): `∼(x₁x₂) = (h₁⁻¹·∼y)·((h₁h_y)⁻¹·∼x₂)` with `y = f x₁ g x₂`;
at `(∼z_v, (∼z_u)⁻¹)` one uses `∼((∼a)⁻¹) = g(a*) = μ_a(a) = (∼a)⁻¹` and that `h(z_w)` multiplies
`Z(Q)` by `c₀θc₀/w²`.  Do not cite the `unproved` placeholders in `TitsDesign`; check
`#print axioms`.  (`h2 : IsPGroup 2 Q` is not a hypothesis here: derive it from `e` via
`isPGroup_two_of_mulEquiv`.) -/
theorem tilde_tilde_center_zs {G : Type} [Group G] [Finite G]
    {H Q : Subgroup G} {t : G} (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H)
    {m : ℕ} {θ : GaloisField 2 m ≃+* GaloisField 2 m} (hθ1 : θ ≠ 1) (hθodd : Odd (orderOf θ))
    {e : Q ≃* Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ}
    (htorus : ∀ d : G, d ∈ Submission.Blueprint.twoPoint H t →
      ∃ lam : (GaloisField 2 m)ˣ, ∀ x : Q,
        ∃ y : Q, (y : G) = d * (x : G) * d⁻¹ ∧
          e y = Work.ZassenhausSuzuki.SzA.hLam θ (lam : GaloisField 2 m) (e x))
    {u v : GaloisField 2 m} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    Work.ZassenhausSuzuki.szTilde hsplit
        (Work.ZassenhausSuzuki.szTilde hsplit (Work.ZassenhausSuzuki.zc e v) *
          (Work.ZassenhausSuzuki.szTilde hsplit (Work.ZassenhausSuzuki.zc e u))⁻¹)
      = Work.ZassenhausSuzuki.szTilde hsplit (Work.ZassenhausSuzuki.zc e (v + v ^ 2 / u)) *
        (Work.ZassenhausSuzuki.szTilde hsplit
          (Work.ZassenhausSuzuki.zc e ((u + v) ^ 2 / u)))⁻¹ := by
  classical
  have h2 : IsPGroup 2 Q := isPGroup_two_of_mulEquiv θ e
  set C : Work.ZassenhausPSL2.Canon H Q t := szCanon hsplit with hC
  have hTfun : szTilde hsplit = tildeOf C := by rw [szTilde_eq_tildeOf, ← hC]
  rw [hTfun]
  -- the multiplier `c₀ = mulD (h(z_1))` and the middle index `W = c₀/v + c₀/u`
  set c₀ : GaloisField 2 m := mulD hsplit htorus (C.h (zc e 1)) with hc₀
  set W : GaloisField 2 m := c₀ / v + c₀ / u with hW
  have hc₀' : c₀ ≠ 0 := mulD_ne_zero hsplit htorus (C.h (zc e 1))
  obtain ⟨hW0, hWv, hWu⟩ := ttc_field_arith hc₀' hu hv huv
  rw [← hW] at hW0 hWv hWu
  have hmv : mulD hsplit htorus (C.h (zc e v)) = c₀ / v ^ 2 :=
    mulD_h_zc hsplit hzass h2 hθodd htorus C hv
  have hmW : mulD hsplit htorus (C.h (zc e W)) = c₀ / W ^ 2 :=
    mulD_h_zc hsplit hzass h2 hθodd htorus C hW0
  -- non-triviality
  have hzv1 : (zc e v : G) ≠ 1 := fun h => (zc_ne_one_iff e).mpr hv (Subtype.ext h)
  have hzu1 : (zc e u : G) ≠ 1 := fun h => (zc_ne_one_iff e).mpr hu (Subtype.ext h)
  have hσv1 : ((tildeOf C (zc e v) : Q) : G) ≠ 1 :=
    fun h => tildeOf_ne_one hsplit hzass h2 C hzv1 (Subtype.ext h)
  have hσu1 : ((tildeOf C (zc e u) : Q) : G) ≠ 1 :=
    fun h => tildeOf_ne_one hsplit hzass h2 C hzu1 (Subtype.ext h)
  have hσu1i : ((((tildeOf C (zc e u))⁻¹ : Q)) : G) ≠ 1 := canon_inv_ne_one hσu1
  have hσne : tildeOf C (zc e v) ≠ tildeOf C (zc e u) := by
    intro h
    refine huv (szTilde_zc_injective hsplit hzass hθ1 hθodd htorus hu hv ?_)
    rw [hTfun]
    exact h.symm
  have hx12 : ((((tildeOf C (zc e v)) * (tildeOf C (zc e u))⁻¹ : Q)) : G) ≠ 1 := by
    intro h
    exact hσne (mul_inv_eq_one.mp (Subtype.ext h))
  -- the `f`- and `g`-coordinates of the two reflections
  have hf_v : C.f (tildeOf C (zc e v)) = zc e (c₀ / v) := by
    have h1 : ((C.f (tildeOf C (zc e v)) : Q) : G)
        = ((conjQ hsplit (C.h (zc e v)) (zc e v) : Q) : G) := by
      rw [conjQ_coe]
      exact f_tilde_zs hsplit hzass h2 C hzv1
    have h2' : conjQ hsplit (C.h (zc e v)) (zc e v)
        = zc e (mulD hsplit htorus (C.h (zc e v)) * v) :=
      conjQ_zc hsplit htorus (C.h (zc e v)) v
    have h3 : mulD hsplit htorus (C.h (zc e v)) * v = c₀ / v := by
      rw [hmv]
      field_simp
      try ring
    apply Subtype.ext
    exact h1.trans (by rw [h2', h3])
  have hf_u : C.f (tildeOf C (zc e u)) = zc e (c₀ / u) := by
    have h1 : ((C.f (tildeOf C (zc e u)) : Q) : G)
        = ((conjQ hsplit (C.h (zc e u)) (zc e u) : Q) : G) := by
      rw [conjQ_coe]
      exact f_tilde_zs hsplit hzass h2 C hzu1
    have h2' : conjQ hsplit (C.h (zc e u)) (zc e u)
        = zc e (mulD hsplit htorus (C.h (zc e u)) * u) :=
      conjQ_zc hsplit htorus (C.h (zc e u)) u
    have h3 : mulD hsplit htorus (C.h (zc e u)) * u = c₀ / u := by
      rw [mulD_h_zc hsplit hzass h2 hθodd htorus C hu]
      field_simp
      try ring
    apply Subtype.ext
    exact h1.trans (by rw [h2', h3])
  have hg_u : C.g ((tildeOf C (zc e u))⁻¹) = zc e (c₀ / u) := by
    have h1 : C.g ((tildeOf C (zc e u))⁻¹) = (C.f (tildeOf C (zc e u)))⁻¹ := by
      have h := canon_H1 hsplit C ((tildeOf C (zc e u))⁻¹) hσu1i
      rw [inv_inv] at h
      have h' := congrArg Inv.inv h
      simpa using h'
    rw [h1, hf_u]
    exact inv_eq_of_mul_eq_one_left (zc_mul_self e (c₀ / u))
  -- the middle element `y = f(∼z_v)·g((∼z_u)⁻¹) = z_W`
  set y : Q := C.f (tildeOf C (zc e v)) * C.g ((tildeOf C (zc e u))⁻¹) with hy
  have hy_eq : y = zc e W := by
    rw [hy, hf_v, hg_u, zc_add, ← hW]
  have hy1 : (y : G) ≠ 1 := by
    intro h
    have hq : y = 1 := Subtype.ext h
    rw [hy_eq] at hq
    exact (zc_ne_one_iff e).mpr hW0 hq
  -- the product formula
  have hmul := szTilde_mul_formula hsplit hzass h2 C
    (x₁ := tildeOf C (zc e v)) (x₂ := (tildeOf C (zc e u))⁻¹) (y := y)
    hσv1 hσu1i hx12 (by simp only [hy, fG, gG, Subgroup.coe_mul]) hy1
  have hh1 : C.h (tildeOf C (zc e v)) = C.h (zc e v) :=
    Subtype.ext (hG_tilde_eq hsplit hzass h2 C hzv1)
  have hhy : C.h y = C.h (zc e W) := by rw [hy_eq]
  have hTy : tildeOf C y = szTilde hsplit (zc e W) := by rw [hy_eq, ← hTfun]
  have hTx2 : tildeOf C ((tildeOf C (zc e u))⁻¹) = (szTilde hsplit (zc e u))⁻¹ := by
    rw [tildeOf_tildeOf_inv hsplit hzass h2 C hzu1,
      inv_eq_of_mul_eq_one_left (zc_mul_self e u), hTfun]
  -- first factor
  have hA : conjQ hsplit (C.h (tildeOf C (zc e v)))⁻¹ (tildeOf C y)
      = tildeOf C (zc e (W / (c₀ / v ^ 2))) := by
    have hmvi : mulD hsplit htorus ((C.h (zc e v))⁻¹) = (c₀ / v ^ 2)⁻¹ := by
      rw [mulD_inv hsplit htorus, hmv]
    have hkey : (c₀ / v ^ 2)⁻¹ * W = W / (c₀ / v ^ 2) := by
      rw [div_eq_mul_inv]
      ring
    rw [hTy, hh1]
    rw [conjQ_szTilde_zc hsplit hzass h2 htorus ((C.h (zc e v))⁻¹) W, hmvi, hkey, ← hTfun]
  -- second factor
  have hmd : mulD hsplit htorus (((C.h (zc e v)) * (C.h (zc e W)))⁻¹)
      = ((c₀ / v ^ 2) * (c₀ / W ^ 2))⁻¹ := by
    rw [mulD_inv hsplit htorus, mulD_mul hsplit htorus, hmv, hmW]
  have hB : conjQ hsplit ((C.h (tildeOf C (zc e v))) * (C.h y))⁻¹
        (tildeOf C ((tildeOf C (zc e u))⁻¹))
      = (tildeOf C (zc e (u / ((c₀ / v ^ 2) * (c₀ / W ^ 2)))))⁻¹ := by
    have hkey : ((c₀ / v ^ 2) * (c₀ / W ^ 2))⁻¹ * u
        = u / ((c₀ / v ^ 2) * (c₀ / W ^ 2)) := by
      rw [div_eq_mul_inv]
      ring
    rw [hTx2, hh1, hhy, conjQ_inv]
    rw [conjQ_szTilde_zc hsplit hzass h2 htorus
      (((C.h (zc e v)) * (C.h (zc e W)))⁻¹) u, hmd, hkey, ← hTfun]
  rw [hmul, hA, hB, hWv, hWu]


end Work.ZassenhausSuzuki
