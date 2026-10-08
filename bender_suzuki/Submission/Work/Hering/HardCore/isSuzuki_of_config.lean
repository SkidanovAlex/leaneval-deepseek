import Mathlib
import Submission.Work.Hering.HardCore.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `C_G(V)` is a Suzuki 2-group in the reduced configuration with a Singer cycle on `V`

The reduced configuration of Peterfalvi I §2 (see `Submission.Work.Hering.Config`) gives a finite
group `G` with a normal elementary abelian subgroup `V` of order `8` such that `C = C_G(V)` is a
2-group with `Inv(C) = V#`.  When in addition `Aut(V)` contains an element of order `7` transitive
on the non-identity elements of `V` (a *Singer cycle*), the centraliser `C` is a **Suzuki
2-group**: it is a non-abelian 2-group with more than one involution and with a cyclic group of
automorphisms transitive on its involutions.

The parametrising automorphism of `C` is produced from the Singer cycle `ξ ∈ Aut(V)`: since `G`
realises *all* automorphisms of `V` (`hAut`), some `g ∈ G` conjugates on `V` as `ξ`; conjugation
by `g` normalises `V` hence restricts to an automorphism `φ` of `C = C_G(V)`, and on the
involutions of `C` — which are exactly the non-identity elements of `V` — it acts as `ξ`.
-/

set_option autoImplicit false

namespace Work.Hering.HardCore

/-- A subgroup of exponent two is abelian. -/
private lemma isSuzuki_V_comm {G : Type} [Group G] (V : Subgroup G)
    (hexp : ∀ x ∈ V, x * x = 1) {x y : G} (hx : x ∈ V) (hy : y ∈ V) : x * y = y * x := by
  have hx1 : x * x = 1 := hexp x hx
  have hxy : (x * y) * (x * y) = 1 := hexp (x * y) (V.mul_mem hx hy)
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx1
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hexp y hy)
  have h2 : x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right hxy).symm
  rw [mul_inv_rev, hxinv, hyinv] at h2
  exact h2

/-- `V ⊆ C_G(V)` when `V` has exponent two. -/
private lemma isSuzuki_V_le_C {G : Type} [Group G] (V C : Subgroup G)
    (hC : C = Subgroup.centralizer ((V : Set G))) (hexp : ∀ x ∈ V, x * x = 1) : V ≤ C := by
  intro x hx
  rw [hC, Subgroup.mem_centralizer_iff]
  intro v hv
  exact isSuzuki_V_comm V hexp hv hx

theorem isSuzuki_of_config {G : Type} [Group G] [Finite G]
    (V C : Subgroup G) (hV : V.Normal)
    (hcard : Nat.card V = 8) (hexp : ∀ x ∈ V, x * x = 1)
    (hC : C = Subgroup.centralizer ((V : Set G)))
    (hC2 : IsPGroup 2 ↥C) (hinv : ∀ x ∈ C, orderOf x = 2 → x ∈ V)
    (hAut : ActsAsAut V hV)
    (hnotab : ¬ ∀ x ∈ C, ∀ y ∈ C, x * y = y * x)
    (hSinger : ∃ ξ : MulAut ↥V, orderOf ξ = 7 ∧
      ∀ a b : ↥V, (a : G) ≠ 1 → (b : G) ≠ 1 → ∃ k : ℕ, (ξ ^ k) a = b) :
    IsSuzukiTwoGroup ↥C := by
  classical
  haveI : Fintype ↥V := Fintype.ofFinite ↥V
  have hVleC : V ≤ C := isSuzuki_V_le_C V C hC hexp
  -- the inclusion `V ↪ C`
  let incl : ↥V →* ↥C := Subgroup.inclusion hVleC
  have hincl_coe : ∀ v : ↥V, ((incl v : ↥C) : G) = (v : G) :=
    fun v => Subgroup.coe_inclusion hVleC v
  refine ⟨hC2, ?_, ?_, ?_⟩
  · -- `C` is non-abelian
    push Not at hnotab
    obtain ⟨x, hx, y, hy, hxy⟩ := hnotab
    refine ⟨⟨x, hx⟩, ⟨y, hy⟩, ?_⟩
    intro h
    exact hxy (by simpa [Subgroup.coe_mul] using congrArg Subtype.val h)
  · -- `C` has two distinct involutions, namely `incl a ≠ incl b` for `a ≠ b` non-identity in `V`
    have hcardF : Fintype.card ↥V = 8 := by rw [← Nat.card_eq_fintype_card]; exact hcard
    have hlt : 1 < Fintype.card ↥V := by omega
    obtain ⟨a, ha⟩ := Fintype.exists_ne_of_one_lt_card hlt (1 : ↥V)
    have hlt2 : ({1, a} : Finset ↥V).card < (Finset.univ : Finset ↥V).card := by
      have h : ({1, a} : Finset ↥V).card ≤ 2 := by
        have h' := Finset.card_insert_le (1 : ↥V) ({a} : Finset ↥V)
        simp only [Finset.card_singleton] at h'
        omega
      rw [Finset.card_univ, hcardF]; omega
    obtain ⟨b, _, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt2
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
    refine ⟨incl a, incl b, ?_, ?_, ?_⟩
    · rw [← Subgroup.orderOf_coe (incl a), hincl_coe a]
      exact orderOf_eq_prime (by rw [pow_two]; exact hexp _ a.2) (fun h => ha (Subtype.ext h))
    · rw [← Subgroup.orderOf_coe (incl b), hincl_coe b]
      exact orderOf_eq_prime (by rw [pow_two]; exact hexp _ b.2) (fun h => hb.1 (Subtype.ext h))
    · intro h
      exact hb.2 (Subgroup.inclusion_injective hVleC h).symm
  · -- an automorphism of `C` transitive on its involutions
    obtain ⟨ξ, _hξorder, hξtrans⟩ := hSinger
    obtain ⟨g, hg⟩ := hAut ξ
    haveI : C.Normal := hC.symm ▸ Subgroup.normal_centralizer (H := V)
    -- conjugation by `g` realises `ξ` on `V`, hence restricts to an automorphism of `C`
    let φ : MulAut ↥C := MulAut.conjNormal (H := C) g
    have hkey : ∀ v : ↥V, φ (incl v) = incl (ξ v) := by
      intro v
      apply Subtype.ext
      rw [MulAut.conjNormal_apply, hincl_coe v, hincl_coe (ξ v), hg v]
    have hpow : ∀ k : ℕ, ∀ v : ↥V, (φ ^ k) (incl v) = incl ((ξ ^ k) v) := by
      intro k
      induction k with
      | zero => intro v; simp
      | succ k ih => intro v; simp only [pow_succ, MulAut.mul_apply, hkey, ih]
    refine ⟨φ, ?_⟩
    intro x y hx hy
    -- the involutions of `C` lie in `V`
    have hxV : (x : G) ∈ V := hinv (x : G) x.2 (by rw [Subgroup.orderOf_coe]; exact hx)
    have hyV : (y : G) ∈ V := hinv (y : G) y.2 (by rw [Subgroup.orderOf_coe]; exact hy)
    have hxne : (x : G) ≠ 1 := by
      intro h
      have h1 : (x : ↥C) = 1 := Subtype.ext h
      rw [h1, orderOf_one] at hx
      exact absurd hx (by norm_num)
    have hyne : (y : G) ≠ 1 := by
      intro h
      have h1 : (y : ↥C) = 1 := Subtype.ext h
      rw [h1, orderOf_one] at hy
      exact absurd hy (by norm_num)
    obtain ⟨k, hk⟩ := hξtrans ⟨(x : G), hxV⟩ ⟨(y : G), hyV⟩ hxne hyne
    refine ⟨k, ?_⟩
    have hxe : incl ⟨(x : G), hxV⟩ = x := Subtype.ext (by rw [hincl_coe])
    have hye : incl ⟨(y : G), hyV⟩ = y := Subtype.ext (by rw [hincl_coe])
    rw [← hxe, ← hye, hpow k ⟨(x : G), hxV⟩, hk]

end Work.Hering.HardCore
