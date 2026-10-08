import Mathlib
import Submission.Work.ThmF.ChV3.Prove.conj_eq_self_of_card_three

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.ThmF.ChV3.Prove

/-!
# The commutator with a normalising element of order `3` lies in the fixed points

Let `T ≤ G` be a finite abelian subgroup of order `9`, let `b ∈ N_G(T)` with `b ^ 3 = 1`, and
suppose that the fixed points `T ⊓ C_G(b)` have order `3`.  Then for every `a ∈ T` the
commutator `a * b * a⁻¹ * b⁻¹` again lies in `T ⊓ C_G(b)`.

The proof is the standard "`(ψ - 1)² = 0`" argument for an automorphism `ψ` of order `3` of an
abelian group of order `9`: conjugation by `b` defines an automorphism `ψ` of `T`, the map
`f x = ψ x * x⁻¹` is an endomorphism of `T` with kernel `T ⊓ C_G(b)`, so its image `f.range`
is a subgroup of `T` of order `3`.  The image is stable under `ψ`, and being of order `3` it is
fixed pointwise by `b` (this is `conj_eq_self_of_card_three`), hence `f.range ≤ ker f`, i.e.
`f ∘ f = 0`.  Finally `a * b * a⁻¹ * b⁻¹ = (f a)⁻¹`.
-/

/-- The automorphism of `X` induced by conjugation with an element `u` of `N_G(X)`. -/
private noncomputable def conjAutOf {G : Type*} [Group G] {X : Subgroup G} {u : G}
    (hu : u ∈ Subgroup.normalizer (X : Set G)) : MulAut ↥X :=
  Subgroup.normalizerMonoidHom X ⟨u, hu⟩

/-- `conjAutOf hu` acts on a point by conjugation by `u` in the ambient group. -/
private lemma conjAutOf_coe {G : Type*} [Group G] {X : Subgroup G} {u : G}
    (hu : u ∈ Subgroup.normalizer (X : Set G)) (x : ↥X) :
    ((conjAutOf hu x : ↥X) : G) = u * (x : G) * u⁻¹ := by
  rw [conjAutOf,
    show Subgroup.normalizerMonoidHom X ⟨u, hu⟩
        = MulDistribMulAction.toMulAut ↥(Subgroup.normalizer (X : Set G)) ↥X ⟨u, hu⟩ from rfl,
    MulDistribMulAction.toMulAut_apply, MulDistribMulAction.toMulEquiv_apply]
  exact Subgroup.smul_coe X ⟨u, hu⟩ x

/-- If `u ^ 3 = 1` then the induced automorphism also satisfies `conjAutOf hu ^ 3 = 1`. -/
private lemma conjAutOf_pow_three {G : Type*} [Group G] {X : Subgroup G} {u : G}
    (hu : u ∈ Subgroup.normalizer (X : Set G)) (hu3 : u ^ 3 = 1) :
    conjAutOf hu ^ 3 = 1 := by
  rw [conjAutOf, ← map_pow]
  have h3 : (⟨u, hu⟩ : ↥(Subgroup.normalizer (X : Set G))) ^ 3 = 1 := by
    apply Subtype.ext
    simpa using hu3
  rw [h3, map_one]

/-- For a commutative group `H` and an automorphism `φ`, the map `x ↦ φ x * x⁻¹` is an
endomorphism of `H`. -/
private def commHom {H : Type*} [Group H] [IsMulCommutative H] (φ : MulAut H) : H →* H where
  toFun x := φ x * x⁻¹
  map_one' := by simp
  map_mul' x y := by
    show φ (x * y) * (x * y)⁻¹ = (φ x * x⁻¹) * (φ y * y⁻¹)
    rw [map_mul, mul_inv_rev]
    ac_rfl

theorem commutator_mem_centralizer_of_card_nine {G : Type*} [Group G] [Finite G] {T : Subgroup G}
    (hcard : Nat.card ↥T = 9) (hcomm : IsMulCommutative ↥T) {b : G}
    (hb : b ∈ Subgroup.normalizer (T : Set G)) (hb3 : b ^ 3 = 1)
    (hfix : Nat.card ↥(T ⊓ Subgroup.centralizer ({b} : Set G)) = 3) :
    ∀ a ∈ T, a * b * a⁻¹ * b⁻¹ ∈ T ⊓ Subgroup.centralizer ({b} : Set G) := by
  haveI : IsMulCommutative ↥T := hcomm
  set C : Subgroup G := T ⊓ Subgroup.centralizer ({b} : Set G) with hCdef
  have hCT : C ≤ T := inf_le_left
  -- the automorphism of `T` given by conjugation with `b`
  set ψ : MulAut ↥T := conjAutOf hb with hψdef
  have hψcoe : ∀ x : ↥T, ((ψ x : ↥T) : G) = b * (x : G) * b⁻¹ := by
    intro x; rw [hψdef]; exact conjAutOf_coe hb x
  have hψ3 : ψ ^ 3 = 1 := by rw [hψdef]; exact conjAutOf_pow_three hb hb3
  have hψ2coe : ∀ x : ↥T, ((ψ (ψ x) : ↥T) : G) = b ^ 2 * (x : G) * (b ^ 2)⁻¹ := by
    intro x
    rw [hψcoe (ψ x), hψcoe x, pow_two, mul_inv_rev]
    group
  have hb2 : b ^ 2 = b⁻¹ := by
    apply mul_eq_one_iff_eq_inv.mp
    rw [← pow_succ]
    simpa using hb3
  have hb2inv : (b ^ 2)⁻¹ = b := by rw [hb2, inv_inv]
  -- the endomorphism `f x = ψ x * x⁻¹`
  let f : ↥T →* ↥T := commHom ψ
  have hfapply : ∀ x : ↥T, f x = ψ x * x⁻¹ := fun x => rfl
  have hmemker : ∀ x : ↥T, x ∈ f.ker ↔ (x : G) ∈ C := by
    intro x
    rw [MonoidHom.mem_ker, hfapply, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    constructor
    · intro hx
      have hψx : ψ x = x := by
        have h := mul_eq_one_iff_eq_inv.mp hx
        simpa using h
      refine ⟨x.2, ?_⟩
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      have hcoe2 : (ψ x : G) = (x : G) := congrArg Subtype.val hψx
      rw [hψcoe x] at hcoe2
      calc b * (x : G) = b * (x : G) * b⁻¹ * b := by group
        _ = (x : G) * b := by rw [hcoe2]
    · intro hx
      obtain ⟨-, hxc⟩ := hx
      have hbx : b * (x : G) = (x : G) * b := hxc b (Set.mem_singleton b)
      have hψx : ψ x = x := by
        apply Subtype.ext
        rw [hψcoe x, hbx, mul_assoc, mul_inv_cancel, mul_one]
      show ψ x * x⁻¹ = 1
      rw [hψx, mul_inv_cancel]
  have hker_eq : f.ker = C.subgroupOf T := by
    ext x
    rw [Subgroup.mem_subgroupOf]
    exact hmemker x
  have hker_card : Nat.card ↥f.ker = 3 := by
    rw [hker_eq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCT).toEquiv]
    exact hfix
  -- `f.range` is stable under `ψ`
  have hpsi_range : ∀ y ∈ f.range, ψ y ∈ f.range := by
    intro y hy
    obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp hy
    refine ⟨ψ w, ?_⟩
    rw [← hw]
    simp only [hfapply, map_mul, map_inv]
  have hpsi2_range : ∀ y ∈ f.range, ψ (ψ y) ∈ f.range := by
    intro y hy
    exact hpsi_range (ψ y) (hpsi_range y hy)
  -- `f.range` promoted to a subgroup of `G`
  set R : Subgroup G := f.range.map T.subtype with hRdef
  have hRcard : Nat.card ↥R = 3 := by
    rw [hRdef, Subgroup.card_map_of_injective (Subgroup.subtype_injective T)]
    have h1 : Nat.card ↥f.ker * Nat.card ↥f.range = 9 := by
      rw [← hcard, ← Subgroup.card_mul_index f.ker, Subgroup.index_ker]
    rw [hker_card] at h1
    omega
  have hbR : b ∈ Subgroup.normalizer (R : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [hRdef] at hh
      rw [Subgroup.mem_map] at hh
      obtain ⟨y, hy, hyeq⟩ := hh
      rw [Subgroup.subtype_apply] at hyeq
      rw [hRdef, Subgroup.mem_map]
      refine ⟨ψ y, hpsi_range y hy, ?_⟩
      rw [Subgroup.subtype_apply, ← hyeq, hψcoe y]
    · intro hh
      rw [hRdef] at hh
      rw [Subgroup.mem_map] at hh
      obtain ⟨y, hy, hyeq⟩ := hh
      rw [Subgroup.subtype_apply] at hyeq
      rw [hRdef, Subgroup.mem_map]
      refine ⟨ψ (ψ y), hpsi2_range y hy, ?_⟩
      rw [Subgroup.subtype_apply]
      have hh_eq : h = b⁻¹ * (y : G) * b := by rw [hyeq]; group
      rw [hh_eq, hψ2coe y, hb2inv, hb2]
  -- a subgroup of order `3` normalised by `b` is centralised by `b`
  have hfixR : ∀ z ∈ R, b * z * b⁻¹ = z :=
    conj_eq_self_of_card_three hRcard hbR hb3
  have hrange_fix : ∀ y ∈ f.range, ψ y = y := by
    intro y hy
    have hmem : (y : G) ∈ R := by
      rw [hRdef, Subgroup.mem_map]; exact ⟨y, hy, rfl⟩
    have h := hfixR (y : G) hmem
    rw [← hψcoe y] at h
    exact Subtype.ext h
  -- hence `f.range ≤ f.ker`
  have hrange_le_ker : f.range ≤ f.ker := by
    intro y hy
    rw [MonoidHom.mem_ker, hfapply, hrange_fix y hy, mul_inv_cancel]
  intro a ha
  have haf : f ⟨a, ha⟩ ∈ f.ker := hrange_le_ker ⟨⟨a, ha⟩, rfl⟩
  have hainv : (f ⟨a, ha⟩)⁻¹ ∈ f.ker := f.ker.inv_mem haf
  have hCmem : (((f ⟨a, ha⟩)⁻¹ : ↥T) : G) ∈ C := by
    rw [hker_eq] at hainv
    rw [Subgroup.mem_subgroupOf] at hainv
    exact hainv
  have heq : a * b * a⁻¹ * b⁻¹ = (((f ⟨a, ha⟩)⁻¹ : ↥T) : G) := by
    have hfa : ((f ⟨a, ha⟩ : ↥T) : G) = b * a * b⁻¹ * a⁻¹ := by
      rw [hfapply]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hψcoe ⟨a, ha⟩]
    rw [Subgroup.coe_inv, hfa]
    group
  rw [heq]
  exact hCmem

end Work.ThmF.ChV3.Prove
