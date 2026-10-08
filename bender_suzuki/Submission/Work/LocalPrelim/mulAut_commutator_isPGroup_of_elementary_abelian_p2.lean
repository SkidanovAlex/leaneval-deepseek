import Mathlib
import Submission.Work.SmallRank.isMulCommutative_of_odd_coprime_le_GL2
import Submission.Work.SmallRank.GL2Defs
import Submission.Work.GL2odd.commutator_isPGroup_of_preserves_line
import Submission.Work.LocalPrelim.odd_GL2_commutator_isPGroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.LocalPrelim

open scoped Pointwise commutatorElement

set_option linter.style.haveILetI false

/-!
# `[L, L]` is a `p`-group for odd order `L ≤ Aut V`, `V` elementary abelian of order `≤ p ^ 2`

`V` is a finite abelian group of exponent `p`, of order at most `p ^ 2`, i.e. an elementary abelian
`p`-group of rank at most two.  We show that for any subgroup `L ≤ MulAut V` of odd order the
derived subgroup `[L, L]` is a `p`-group.

* If `V` is cyclic then `MulAut V ≃* (ZMod |V|)ˣ` is commutative, so `[L, L] = 1`.
* Otherwise `V` is elementary abelian of order `p ^ 2`; then (`V` being an `𝔽_p`-vector space of
  dimension two) `MulAut V ≃* GL(2, 𝔽_p)` and the result is
  `Work.LocalPrelim.odd_GL2_commutator_isPGroup`.
-/

/-! ## The transport `MulAut V ≃* GL(2, 𝔽_p)` -/

/-- Additive automorphisms of a `ZMod p`-module are exactly its linear automorphisms. -/
private noncomputable def addAutLinEquiv {p : ℕ} (W : Type*) [AddCommGroup W] [Module (ZMod p) W] :
    AddAut W ≃ (W ≃ₗ[ZMod p] W) where
  toFun e := LinearEquiv.ofBijective ((e : W →+ W).toZModLinearMap p) e.bijective
  invFun f := f.toAddEquiv
  left_inv e := by ext x; simp [LinearEquiv.ofBijective]
  right_inv f := by ext x; simp [LinearEquiv.ofBijective]

/-- The `ZMod p`-linear automorphism of `Additive V` underlying a group automorphism of `V`. -/
private noncomputable def linOf {p : ℕ} {V : Type*} [CommGroup V] [Module (ZMod p) (Additive V)]
    (α : MulAut V) : Additive V ≃ₗ[ZMod p] Additive V :=
  addAutLinEquiv (p := p) (Additive V) (MulEquiv.toAdditive α)

/-- `MulAut V ≃* (Additive V ≃ₗ[ZMod p] Additive V)` for a finite abelian group `V` of exponent
dividing `p` (so that `Additive V` carries a `ZMod p`-module structure). -/
private noncomputable def mulAutEquivLin {p : ℕ} {V : Type*} [CommGroup V]
    [Module (ZMod p) (Additive V)] :
    MulAut V ≃* (Additive V ≃ₗ[ZMod p] Additive V) where
  toFun := linOf (p := p)
  invFun L := MulEquiv.toAdditive.symm ((addAutLinEquiv (p := p) (Additive V)).symm L)
  left_inv α := by simp only [linOf, Equiv.symm_apply_apply]
  right_inv L := by simp only [linOf, Equiv.apply_symm_apply]
  map_mul' a b := by
    ext x
    simp only [linOf, addAutLinEquiv, LinearEquiv.ofBijective_apply,
      AddMonoidHom.coe_toZModLinearMap, LinearEquiv.mul_apply]
    rfl

/-- Conjugation by a linear equivalence on the group of linear automorphisms. -/
private noncomputable def conjLinEquiv {p : ℕ} {W : Type*} [AddCommGroup W] [Module (ZMod p) W]
    (e : W ≃ₗ[ZMod p] (Fin 2 → ZMod p)) :
    (W ≃ₗ[ZMod p] W) ≃* ((Fin 2 → ZMod p) ≃ₗ[ZMod p] (Fin 2 → ZMod p)) where
  toFun L := e.symm.trans (L.trans e)
  invFun M := e.trans (M.trans e.symm)
  left_inv L := by ext x; simp [LinearEquiv.trans_apply]
  right_inv M := by ext x; simp [LinearEquiv.trans_apply]
  map_mul' L M := by ext x; simp [LinearEquiv.trans_apply, LinearEquiv.mul_apply]

/-- The transport `MulAut V ≃* GL(2, 𝔽_p)`. -/
private noncomputable def mulAutEquivGL {p : ℕ} [Fact p.Prime] {V : Type*} [CommGroup V]
    [Module (ZMod p) (Additive V)] (e : Additive V ≃ₗ[ZMod p] (Fin 2 → ZMod p)) :
    MulAut V ≃* GL (Fin 2) (ZMod p) :=
  (mulAutEquivLin (p := p)).trans ((conjLinEquiv e).trans (Work.GL2odd.glToLinEquiv p).symm)

/-! ## The main statement -/

theorem mulAut_commutator_isPGroup_of_elementary_abelian_p2
    {p : ℕ} [Fact p.Prime] {V : Type*} [Group V] [Finite V]
    (hcomm : IsMulCommutative V) (hexp : ∀ v : V, v ^ p = 1) (hcard : Nat.card V ≤ p ^ 2)
    (L : Subgroup (MulAut V)) (hodd : Odd (Nat.card L)) :
    IsPGroup p ↥(⁅L, L⁆) := by
  letI : CommGroup V := { ‹Group V› with mul_comm := fun a b => hcomm.is_comm.comm a b }
  have hpPrime : p.Prime := Fact.out
  by_cases hcyc : IsCyclic V
  · -- `V` cyclic: `MulAut V` is commutative
    haveI := hcyc
    have hmc : IsMulCommutative (MulAut V) := by
      rw [isMulCommutative_iff]
      intro f g
      refine (IsCyclic.mulAutMulEquiv V).injective ?_
      rw [map_mul, map_mul, mul_comm]
    haveI hmcL : IsMulCommutative ↥L := by
      rw [isMulCommutative_iff]
      intro x y
      exact Subtype.ext (hmc.is_comm.comm x.1 y.1)
    have hbot : ⁅L, L⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact Subgroup.le_centralizer_iff_isMulCommutative.mpr hmcL
    rw [hbot]
    exact IsPGroup.of_bot
  · -- `V` elementary abelian of order `p ^ 2`
    have hpg : IsPGroup p V := by
      refine IsPGroup.iff_orderOf.mpr fun x => ?_
      have hdvd : orderOf x ∣ p := orderOf_dvd_iff_pow_eq_one.mpr (hexp x)
      rcases (Nat.dvd_prime hpPrime).mp hdvd with h | h
      · exact ⟨0, by rw [pow_zero]; exact h⟩
      · exact ⟨1, by rw [pow_one]; exact h⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hpg
    have hk2 : k ≤ 2 := by
      have hle : p ^ k ≤ p ^ 2 := by rw [← hk]; exact hcard
      exact (Nat.pow_le_pow_iff_right hpPrime.one_lt).mp hle
    have hkne0 : k ≠ 0 := by
      rintro rfl
      refine hcyc ?_
      have h1 : Nat.card V = 1 := by simpa using hk
      haveI : Subsingleton V := (Nat.card_eq_one_iff_unique.mp h1).1
      exact isCyclic_of_subsingleton
    have hkne1 : k ≠ 1 := by
      rintro rfl
      refine hcyc ?_
      have h1 : Nat.card V = p := by simpa using hk
      exact isCyclic_of_prime_card h1
    have hkeq : k = 2 := by omega
    have hcard2 : Nat.card V = p ^ 2 := by rw [hk, hkeq]
    -- the `ZMod p`-module structure on `Additive V`
    have hmod : ∀ x : Additive V, p • x = 0 := by
      intro x
      rw [← ofMul_toMul x, ← ofMul_pow]
      simp [hexp]
    letI : Module (ZMod p) (Additive V) := AddCommGroup.zmodModule (n := p) hmod
    haveI : Fintype (Additive V) := Fintype.ofFinite _
    haveI : Module.Free (ZMod p) (Additive V) := Module.Free.of_divisionRing _ _
    haveI : Module.Finite (ZMod p) (Additive V) := Module.Finite.of_finite
    have hfr : Module.finrank (ZMod p) (Additive V) = 2 := by
      have h := Module.card_eq_pow_finrank (K := ZMod p) (V := Additive V)
      rw [ZMod.card, ← Nat.card_eq_fintype_card] at h
      rw [show Nat.card (Additive V) = p ^ 2 from hcard2] at h
      exact Nat.pow_right_injective hpPrime.two_le h.symm
    obtain ⟨e⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq (R := ZMod p)
      (M := Additive V) (M' := (Fin 2 → ZMod p)) (by
        rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
        exact hfr)
    -- transport to `GL(2, 𝔽_p)`
    have φ := mulAutEquivGL (p := p) (V := V) e
    have hodd' : Odd (Nat.card ↥(L.map φ.toMonoidHom)) := by
      rw [Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective]
      exact hodd
    have h1 : IsPGroup p ↥⁅L.map φ.toMonoidHom, L.map φ.toMonoidHom⁆ :=
      odd_GL2_commutator_isPGroup (L.map φ.toMonoidHom) hodd'
    have hcard' : Nat.card ↥⁅L, L⁆ =
        Nat.card ↥⁅L.map φ.toMonoidHom, L.map φ.toMonoidHom⁆ := by
      rw [← Subgroup.card_map_of_injective (K := ⁅L, L⁆) (f := φ.toMonoidHom) φ.injective,
        Subgroup.map_commutator]
    rw [IsPGroup.iff_card] at h1 ⊢
    obtain ⟨n, hn⟩ := h1
    exact ⟨n, by rw [hcard', hn]⟩

end Work.LocalPrelim
