import Mathlib
import Submission.Work.PGroup.Symplectic.card_eq_pow_even_of_nondegenerate_alt

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `|G/Z(G)|` is a square for a finite group of class `2` with `|G'| = p`

Let `G` be a finite group whose derived subgroup `G' = ⁅⊤,⊤⁆` is central of prime order `p`,
and suppose that every `p`-th power in `G` is central.  Then `G/Z(G)` carries the structure of
a symplectic space over `𝔽_p`: the commutator pairing `(xZ, yZ) ↦ [x,y]` is a non-degenerate
alternating bilinear form (after identifying the central subgroup `G' ≅ ℤ/p` that it takes
values in).  A non-degenerate alternating bilinear form over a finite field lives in even
dimension, so `|G/Z(G)|` is a perfect square.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped commutatorElement
open Subgroup

noncomputable section

namespace Work.PGroup.Symplectic

variable {G : Type*} [Group G]

/-- When the derived subgroup is central, `y ↦ ⁅x,y⁆` is multiplicative. -/
theorem commutator_mul_right_of_central
    (hcen : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ ≤ Subgroup.center G) (x y z : G) :
    ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj]
  have hc : ⁅x, z⁆ ∈ Subgroup.center G :=
    hcen (commutator_mem_commutator (mem_top x) (mem_top z))
  have hcy : y * ⁅x, z⁆ = ⁅x, z⁆ * y := Subgroup.mem_center_iff.mp hc y
  rw [show ⁅x, y⁆ * y * ⁅x, z⁆ * y⁻¹ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) by group]
  rw [hcy, mul_assoc, mul_inv_cancel, mul_one]

/-- When the derived subgroup is central, `x ↦ ⁅x,z⁆` is multiplicative. -/
theorem commutator_mul_left_of_central
    (hcen : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ ≤ Subgroup.center G) (x y z : G) :
    ⁅x * y, z⁆ = ⁅x, z⁆ * ⁅y, z⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul]
  have hc : ⁅y, z⁆ ∈ Subgroup.center G :=
    hcen (commutator_mem_commutator (mem_top y) (mem_top z))
  have h1 : x * ⁅y, z⁆ * x⁻¹ = ⁅y, z⁆ := by
    rw [Subgroup.mem_center_iff.mp hc x, mul_assoc, mul_inv_cancel, mul_one]
  rw [h1]
  exact ((Subgroup.mem_center_iff.mp hc) ⁅x, z⁆).symm

open scoped IsMulCommutative in
theorem sq_card_quotient_center_of_class_two {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hodd : p ≠ 2)
    (hclass : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ ≤ Subgroup.center G)
    (hder : Nat.card (⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ : Subgroup G) = p)
    (helem : ∀ x : G, x ^ p ∈ Subgroup.center G) :
    ∃ r : ℕ, Nat.card (G ⧸ Subgroup.center G) = r ^ 2 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let Z : Subgroup G := Subgroup.center G
  let D : Subgroup G := ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆
  have hDZ : D ≤ Z := hclass
  have hcardD : Nat.card D = p := hder
  haveI : IsMulCommutative (G ⧸ Z) :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := Z)).mpr hclass
  have hcardM : Nat.card (Multiplicative (ZMod p)) = p := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  let e : D ≃* Multiplicative (ZMod p) := mulEquivOfPrimeCardEq hcardD hcardM
  -- the hom `ψ x : G →* Multiplicative (ZMod p)`, `y ↦ [x,y]`
  let ψ : G → (G →* Multiplicative (ZMod p)) := fun x =>
    e.toMonoidHom.comp
      (MonoidHom.codRestrict
        ({ toFun := fun y => ⁅x, y⁆
           map_one' := commutatorElement_one_right x
           map_mul' := commutator_mul_right_of_central hclass x } : G →* G)
        D (fun y => commutator_mem_commutator (mem_top x) (mem_top y)))
  have ψ_apply : ∀ x y : G,
      ψ x y = e ⟨⁅x, y⁆, commutator_mem_commutator (mem_top x) (mem_top y)⟩ := fun x y => rfl
  have ψ_one_left : ∀ y : G, ψ 1 y = 1 := by
    intro y
    rw [ψ_apply]
    rw [show (⟨⁅(1 : G), y⁆, commutator_mem_commutator (mem_top 1) (mem_top y)⟩ : D) = 1 from
          Subtype.ext (commutatorElement_one_left y), map_one]
  have ψ_eq_one_of_mem : ∀ x z : G, z ∈ Z → ψ x z = 1 := by
    intro x z hz
    rw [ψ_apply]
    have h : (⟨⁅x, z⁆, commutator_mem_commutator (mem_top x) (mem_top z)⟩ : D) = 1 :=
      Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hz x))
    rw [h, map_one]
  have ψ_mul : ∀ x y z : G, ψ (x * y) z = ψ x z * ψ y z := by
    intro x y z
    rw [ψ_apply, ψ_apply, ψ_apply]
    rw [show (⟨⁅x * y, z⁆, commutator_mem_commutator (mem_top (x * y)) (mem_top z)⟩ : D)
          = (⟨⁅x, z⁆, commutator_mem_commutator (mem_top x) (mem_top z)⟩ : D)
            * ⟨⁅y, z⁆, commutator_mem_commutator (mem_top y) (mem_top z)⟩ from
          Subtype.ext (commutator_mul_left_of_central hclass x y z), map_mul]
  have ψ_eq_one_of_mem_left : ∀ x z : G, x ∈ Z → ψ x z = 1 := by
    intro x z hx
    rw [ψ_apply]
    have h : (⟨⁅x, z⁆, commutator_mem_commutator (mem_top x) (mem_top z)⟩ : D) = 1 :=
      Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_center_iff.mp hx z).symm)
    rw [h, map_one]
  have hψker : ∀ x : G, Z ≤ (ψ x).ker := by
    intro x z hz
    rw [MonoidHom.mem_ker]
    exact ψ_eq_one_of_mem x z hz
  -- the hom `Ψ : G →* (G ⧸ Z →* Multiplicative (ZMod p))`
  let Ψ : G →* (G ⧸ Z →* Multiplicative (ZMod p)) :=
    { toFun := fun x => QuotientGroup.lift Z (ψ x) (hψker x)
      map_one' := by
        refine MonoidHom.ext fun q => ?_
        obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective Z q
        rw [← hy, QuotientGroup.mk'_apply, QuotientGroup.lift_mk', MonoidHom.one_apply]
        exact ψ_one_left y
      map_mul' := by
        intro x y
        refine MonoidHom.ext fun q => ?_
        obtain ⟨z, hz⟩ := QuotientGroup.mk'_surjective Z q
        rw [← hz, QuotientGroup.mk'_apply, QuotientGroup.lift_mk', MonoidHom.mul_apply,
          QuotientGroup.lift_mk', QuotientGroup.lift_mk']
        exact ψ_mul x y z }
  have hΨker : Z ≤ Ψ.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    rw [show Ψ z = QuotientGroup.lift Z (ψ z) (hψker z) from rfl]
    refine MonoidHom.ext fun q => ?_
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective Z q
    rw [← hy, QuotientGroup.mk'_apply, QuotientGroup.lift_mk', MonoidHom.one_apply]
    exact ψ_eq_one_of_mem_left z y hz
  let Φ : (G ⧸ Z) →* (G ⧸ Z →* Multiplicative (ZMod p)) := QuotientGroup.lift Z Ψ hΨker
  have Φ_apply : ∀ x y : G, Φ (QuotientGroup.mk' Z x) (QuotientGroup.mk' Z y)
      = e ⟨⁅x, y⁆, commutator_mem_commutator (mem_top x) (mem_top y)⟩ := by
    intro x y
    have h1 : Φ (QuotientGroup.mk' Z x) = Ψ x := QuotientGroup.lift_mk' Z hΨker x
    rw [h1]
    have h2 : (Ψ x) (QuotientGroup.mk' Z y) = ψ x y := QuotientGroup.lift_mk' Z (hψker x) y
    rw [h2]
    exact ψ_apply x y
  -- the additive group `V = G ⧸ Z` with its `𝔽_p`-structure
  let V := Additive (G ⧸ Z)
  have hpow : ∀ (n : ℕ) (a : G ⧸ Z), n • (Additive.ofMul a : V) = Additive.ofMul (a ^ n) := by
    intro n a
    induction n with
    | zero => simp
    | succ n ih => rw [succ_nsmul, ih, pow_succ, ofMul_mul]
  have hExp : ∀ a : G ⧸ Z, a ^ p = 1 := by
    intro a
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Z a
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact helem x
  have hVexp : ∀ v : V, p • v = 0 := by
    intro v
    obtain ⟨a, rfl⟩ := Additive.ofMul.surjective v
    rw [hpow p a, hExp a]
    simp
  haveI hmod : Module (ZMod p) V := AddCommGroup.zmodModule hVexp
  -- the bi-additive map underlying the symplectic form
  have hpair_mul_right : ∀ (a b b' : G ⧸ Z),
      Multiplicative.toAdd (Φ a (b * b'))
        = Multiplicative.toAdd (Φ a b) + Multiplicative.toAdd (Φ a b') := by
    intro a b b'
    rw [map_mul, toAdd_mul]
  have hpair_mul_left : ∀ (a a' b : G ⧸ Z),
      Multiplicative.toAdd (Φ (a * a') b)
        = Multiplicative.toAdd (Φ a b) + Multiplicative.toAdd (Φ a' b) := by
    intro a a' b
    rw [map_mul, MonoidHom.mul_apply, toAdd_mul]
  let f : V →+ V →+ ZMod p :=
    { toFun := fun u =>
        { toFun := fun v => Multiplicative.toAdd (Φ u.toMul v.toMul)
          map_zero' := by
            show Multiplicative.toAdd (Φ u.toMul (1 : G ⧸ Z)) = 0
            rw [map_one]
            rfl
          map_add' := fun v w => by
            show Multiplicative.toAdd (Φ u.toMul (v.toMul * w.toMul))
                = Multiplicative.toAdd (Φ u.toMul v.toMul)
                  + Multiplicative.toAdd (Φ u.toMul w.toMul)
            exact hpair_mul_right u.toMul v.toMul w.toMul }
      map_zero' := by
        refine AddMonoidHom.ext fun v => ?_
        show Multiplicative.toAdd (Φ (1 : G ⧸ Z) v.toMul) = 0
        rw [map_one, MonoidHom.one_apply]
        rfl
      map_add' := fun u u' => by
        refine AddMonoidHom.ext fun v => ?_
        show Multiplicative.toAdd (Φ (u.toMul * u'.toMul) v.toMul)
            = Multiplicative.toAdd (Φ u.toMul v.toMul)
              + Multiplicative.toAdd (Φ u'.toMul v.toMul)
        exact hpair_mul_left u.toMul u'.toMul v.toMul }
  let B : LinearMap.BilinForm (ZMod p) V :=
    AddMonoidHom.toZModLinearMap p
      (AddMonoidHom.comp (AddMonoidHom.toZModLinearMapEquiv p).toAddMonoidHom f)
  have B_apply : ∀ u v : V, B u v = Multiplicative.toAdd (Φ u.toMul v.toMul) := fun u v => rfl
  have hB_alt : B.IsAlt := by
    intro u
    rw [B_apply]
    obtain ⟨a, rfl⟩ := Additive.ofMul.surjective u
    show Multiplicative.toAdd (Φ a a) = 0
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective Z a
    rw [← hx, Φ_apply]
    rw [show (⟨⁅x, x⁆, commutator_mem_commutator (mem_top x) (mem_top x)⟩ : D) = 1 from
          Subtype.ext (commutatorElement_self x), map_one]
    rfl
  have hB_nd : B.Nondegenerate := by
    constructor
    · intro u hu
      obtain ⟨a, rfl⟩ := Additive.ofMul.surjective u
      have hmain : ∀ y : G, Φ a (QuotientGroup.mk' Z y) = 1 := by
        intro y
        have hy := hu (Additive.ofMul (QuotientGroup.mk' Z y) : V)
        rw [B_apply] at hy
        have hy' : Multiplicative.toAdd (Φ a (QuotientGroup.mk' Z y)) = 0 := hy
        apply Multiplicative.toAdd.injective
        rw [hy']
        rfl
      obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective Z a
      rw [show (0 : V) = Additive.ofMul (1 : G ⧸ Z) from rfl]
      apply Additive.toMul.injective
      change a = 1
      rw [← hx, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      change x ∈ Subgroup.center G
      rw [Subgroup.mem_center_iff]
      intro y
      have hy : Φ (QuotientGroup.mk' Z x) (QuotientGroup.mk' Z y) = 1 := by
        rw [hx]; exact hmain y
      rw [Φ_apply x y] at hy
      have h2 : (⟨⁅x, y⁆, commutator_mem_commutator (mem_top x) (mem_top y)⟩ : D) = 1 := by
        apply e.injective
        rw [map_one]
        exact hy
      exact (commutatorElement_eq_one_iff_mul_comm.mp (Subtype.ext_iff.mp h2)).symm
    · intro v hv
      obtain ⟨a, rfl⟩ := Additive.ofMul.surjective v
      have hmain : ∀ x : G, Φ (QuotientGroup.mk' Z x) a = 1 := by
        intro x
        have hx := hv (Additive.ofMul (QuotientGroup.mk' Z x) : V)
        rw [B_apply] at hx
        have hx' : Multiplicative.toAdd (Φ (QuotientGroup.mk' Z x) a) = 0 := hx
        apply Multiplicative.toAdd.injective
        rw [hx']
        rfl
      obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective Z a
      rw [show (0 : V) = Additive.ofMul (1 : G ⧸ Z) from rfl]
      apply Additive.toMul.injective
      change a = 1
      rw [← hy, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      change y ∈ Subgroup.center G
      rw [Subgroup.mem_center_iff]
      intro x
      have hx : Φ (QuotientGroup.mk' Z x) (QuotientGroup.mk' Z y) = 1 := by
        rw [hy]; exact hmain x
      rw [Φ_apply x y] at hx
      have h2 : (⟨⁅x, y⁆, commutator_mem_commutator (mem_top x) (mem_top y)⟩ : D) = 1 := by
        apply e.injective
        rw [map_one]
        exact hx
      exact commutatorElement_eq_one_iff_mul_comm.mp (Subtype.ext_iff.mp h2)
  obtain ⟨n, hn⟩ := card_eq_pow_even_of_nondegenerate_alt hp V B hB_alt hB_nd
  refine ⟨p ^ n, ?_⟩
  have hV : Nat.card V = Nat.card (G ⧸ Z) := Nat.card_congr Additive.toMul
  rw [← hV, hn, Nat.mul_comm 2 n, pow_mul]

end Work.PGroup.Symplectic
