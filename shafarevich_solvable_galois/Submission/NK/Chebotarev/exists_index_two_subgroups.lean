import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.Chebotarev

/-!
# Index-two subgroups of a finite elementary abelian 2-group

If `G` is a finite group all of whose elements square to `1`, then `G` is an elementary
abelian `2`-group, i.e. a finite-dimensional vector space over `𝔽₂`.  Choosing a basis of
that vector space and taking the coordinate hyperplanes produces `r` subgroups of index two
whose intersection is trivial, with `Nat.card G = 2 ^ r`.

This is the standard "`G/Φ(G)` is the 𝔽₂-dual of `G`" package used in the group-theoretic
reconstruction of decomposition groups (Neukirch–Uchida).
-/

set_option linter.style.haveILetI false

theorem exists_index_two_subgroups {G : Type*} [Group G] [Finite G] (h : ∀ g : G, g * g = 1) :
    ∃ (r : ℕ) (H : Fin r → Subgroup G), (⨅ i, H i = ⊥) ∧
      (∀ i, Nat.card (G ⧸ H i) = 2) ∧ Nat.card G = 2 ^ r := by
  haveI : Fintype G := Fintype.ofFinite G
  -- `G` is commutative, since `(a * b) * (a * b) = 1` forces every element to be its own
  -- inverse.
  have hmul : ∀ a b : G, a * b = b * a := by
    intro a b
    have ha : a⁻¹ = a := (mul_eq_one_iff_inv_eq.mp (h a))
    have hb : b⁻¹ = b := (mul_eq_one_iff_inv_eq.mp (h b))
    have hab : (a * b)⁻¹ = a * b := (mul_eq_one_iff_inv_eq.mp (h (a * b)))
    have h2 : (a * b)⁻¹ = b * a := by rw [mul_inv_rev, hb, ha]
    exact hab.symm.trans h2
  letI : CommGroup G := { (inferInstance : Group G) with mul_comm := hmul }
  -- `Additive G` is an `𝔽₂`-vector space.
  have h2 : ∀ x : Additive G, 2 • x = 0 := by
    intro x
    rw [two_nsmul]
    exact h (Additive.toMul x)
  letI : Module (ZMod 2) (Additive G) := AddCommGroup.zmodModule h2
  letI : Module.Finite (ZMod 2) (Additive G) := Module.Finite.of_finite
  -- A basis, indexed by `Fin r` where `r` is the dimension.
  let b := Module.finBasis (ZMod 2) (Additive G)
  -- The coordinate characters `G →* Multiplicative (ZMod 2)`.
  let φ : Fin (Module.finrank (ZMod 2) (Additive G)) → (G →* Multiplicative (ZMod 2)) :=
    fun i => { toFun := fun g => Multiplicative.ofAdd ((b.coord i) (Additive.ofMul g))
               map_one' := by simp
               map_mul' := by intro a b; simp [ofMul_mul, map_add] }
  have hcoord : ∀ i, (b.coord i) (b i) = 1 := by
    intro i; simp [Module.Basis.coord_apply]
  -- Each coordinate character is onto the two-element group.
  have hsurj : ∀ i, Function.Surjective (φ i) := by
    intro i y
    refine ⟨Additive.toMul (Multiplicative.toAdd y • b i), ?_⟩
    show Multiplicative.ofAdd
      ((b.coord i) (Additive.ofMul (Additive.toMul (Multiplicative.toAdd y • b i)))) = y
    rw [ofMul_toMul, map_smul, hcoord i, smul_eq_mul, mul_one]
    simp
  refine ⟨Module.finrank (ZMod 2) (Additive G), fun i => (φ i).ker, ?_, ?_, ?_⟩
  · -- The coordinate characters jointly separate points, so the kernels meet trivially.
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    have hzero : Additive.ofMul g = 0 := by
      refine (b.forall_coord_eq_zero_iff (x := Additive.ofMul g)).mp ?_
      intro i
      have hi : g ∈ (φ i).ker := (Subgroup.mem_iInf.mp hg) i
      rw [MonoidHom.mem_ker] at hi
      have hh := congrArg Multiplicative.toAdd hi
      simpa [φ] using hh
    simpa using hzero
  · -- Each kernel has index two.
    intro i
    have e := QuotientGroup.quotientKerEquivOfSurjective (φ i) (hsurj i)
    calc Nat.card (G ⧸ (φ i).ker) = Nat.card (Multiplicative (ZMod 2)) := Nat.card_congr e
      _ = Nat.card (ZMod 2) := (Nat.card_congr Multiplicative.ofAdd).symm
      _ = 2 := by simp
  · -- The order is `2` to the dimension.
    have hcardV := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive G)
    have hZ : Nat.card (ZMod 2) = 2 := by simp
    have hAG : Nat.card (Additive G) = Nat.card G := Nat.card_congr Additive.ofMul
    rw [← hAG, hcardV, hZ]

end NK.Chebotarev
