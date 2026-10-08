import Mathlib
import Submission.Work.BSLit.Defs
import Submission.Work.BSLit.BenderFacts2.Facts2Defs
import Submission.Work.BSLit.BenderFacts2.Facts2SzDefs
import Submission.Work.BSLit.BenderFacts2.sz_centralizer_involution_eq_U
import Submission.Work.BSLit.BenderFacts2.sz_torus_centralizer_isCyclic
import Submission.Work.BSLit.BenderFacts2.sz_torus_centralizer_card_ge
import Submission.Work.Models.ModelData.szModelData
import Submission.Work.Models.Port.Sz.Weyl
import Submission.Work.PSU3.BST.sz_wTrans

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

open LeanEval.GroupTheory.Defs

namespace Work.BSLit.BenderFacts2

/-! ## Elementary transport lemmas

The three clauses bundled in `BenderFacts2For G H` are invariant under conjugation: every
strongly embedded subgroup of a model is a conjugate of the Borel, and each clause transports
along `MulAut.conj g`.
-/

/-- `(conj g) x = g x g⁻¹`, in the form used to rewrite applications of the monoid hom. -/
theorem sz_conj_apply {G : Type*} [Group G] (g x : G) :
    (MulAut.conj g).toMonoidHom x = g * x * g⁻¹ :=
  MulAut.conj_apply g x

/-- A `2`-power-order element of `G` lies in every normal subgroup of odd index. -/
theorem sz_mem_two_pow_of_odd_index {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (hodd : Odd N.index) {k : ℕ} {x : G} (hx : orderOf x = 2 ^ k) : x ∈ N := by
  have hxpow : x ^ (2 ^ k) = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]
  set y := (QuotientGroup.mk' N) x with hy
  have hy2 : y ^ (2 ^ k) = 1 := by rw [hy, ← map_pow, hxpow, map_one]
  have hdvd2 : orderOf y ∣ 2 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hy2
  have hdvd_index : orderOf y ∣ N.index := by
    rw [Subgroup.index_eq_card]; exact orderOf_dvd_natCard y
  have hcop : Nat.Coprime (2 ^ k) N.index := (hodd.coprime_two_left).pow_left k
  have hone : orderOf y ∣ 1 := by
    rw [← hcop.gcd_eq_one]; exact Nat.dvd_gcd hdvd2 hdvd_index
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hone)

/-- `orderOf` is invariant under `x ↦ g⁻¹ x g`. -/
theorem sz_orderOf_conj {G : Type*} [Group G] (g a : G) :
    orderOf (g⁻¹ * a * g) = orderOf a := by
  have h := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) a
  rwa [MulAut.conj_apply, inv_inv] at h

/-- Membership in a conjugate subgroup. -/
theorem sz_mem_map_conj {G : Type*} [Group G] (H : Subgroup G) (g x : G) :
    x ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ H := by
  constructor
  · intro hx
    obtain ⟨h, hh, hhx⟩ := Subgroup.mem_map.mp hx
    have key : g⁻¹ * x * g = h := by
      rw [← hhx, sz_conj_apply]
      group
    rw [key]; exact hh
  · intro hx
    exact Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, hx, by rw [sz_conj_apply]; group⟩

/-- `C(c)` is the `g`-conjugate of `C(g⁻¹ c g)`. -/
theorem sz_centralizer_conj_eq {G : Type*} [Group G] (c g : G) :
    Subgroup.centralizer ({c} : Set G)
      = (Subgroup.centralizer ({g⁻¹ * c * g} : Set G)).map (MulAut.conj g).toMonoidHom := by
  ext y
  constructor
  · intro hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * y * g, ?_, by rw [sz_conj_apply]; group⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (g⁻¹ * y * g) * (g⁻¹ * c * g) = g⁻¹ * (y * c) * g := by group
      _ = g⁻¹ * (c * y) * g := by rw [hy]
      _ = (g⁻¹ * c * g) * (g⁻¹ * y * g) := by group
  · rintro ⟨y', hy', hye⟩
    have hyy : y = g * y' * g⁻¹ := by rw [← hye, sz_conj_apply]
    have hy'' : y' * (g⁻¹ * c * g) = (g⁻¹ * c * g) * y' :=
      (Subgroup.mem_centralizer_singleton_iff).mp hy'
    rw [Subgroup.mem_centralizer_singleton_iff, hyy]
    calc g * y' * g⁻¹ * c = g * (y' * (g⁻¹ * c * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * c * g) * y') * g⁻¹ := by rw [hy'']
      _ = c * (g * y' * g⁻¹) := by group

/-- The number of involutions of a conjugate subgroup. -/
theorem sz_ncard_involutions_conj {G : Type*} [Group G] (H : Subgroup G) (g : G) :
    (Submission.Blueprint.involutions
        (H.map (MulAut.conj g).toMonoidHom : Set G)).ncard
      = (Submission.Blueprint.involutions (H : Set G)).ncard := by
  classical
  have hset : Submission.Blueprint.involutions (H.map (MulAut.conj g).toMonoidHom : Set G)
      = (fun x : G => g * x * g⁻¹) '' (Submission.Blueprint.involutions (H : Set G)) := by
    ext y
    constructor
    · rintro ⟨hy, hy2⟩
      obtain ⟨h, hh, hhy⟩ := Subgroup.mem_map.mp hy
      have hyy : y = g * h * g⁻¹ := by rw [← hhy, sz_conj_apply]
      refine ⟨h, ⟨hh, ?_⟩, hyy.symm⟩
      have hord : orderOf (g * h * g⁻¹) = orderOf h := by
        rw [show g * h * g⁻¹ = (g⁻¹)⁻¹ * h * g⁻¹ by group, sz_orderOf_conj]
      rw [← hord, ← hyy]
      exact hy2
    · rintro ⟨h, ⟨hh, hh2⟩, rfl⟩
      refine ⟨Subgroup.mem_map.mpr ⟨h, hh, by rw [sz_conj_apply]⟩, ?_⟩
      change orderOf (g * h * g⁻¹) = 2
      rw [show g * h * g⁻¹ = (g⁻¹)⁻¹ * h * g⁻¹ by group, sz_orderOf_conj]
      exact hh2
  rw [hset]
  exact Set.ncard_image_of_injective _
    (fun x y hxy => by
      have h : g * x * g⁻¹ = g * y * g⁻¹ := hxy
      exact mul_left_cancel (mul_right_cancel h))

/-! ## The Suzuki model-specific inputs -/

/-- The involutions of the Suzuki `2`-group are the `u(0,c)`, `c ≠ 0`. -/
theorem exists_szUgS_zero_of_mem_szTwoGroupS (n : ℕ) {x : SzModel n}
    (hxU : x ∈ Submission.Sz.szTwoGroupS n) (hx2 : orderOf x = 2) :
    ∃ c : Submission.Sz.SzField n, c ≠ 0 ∧ x = szUgS n 0 c := by
  obtain ⟨a, b, hab⟩ := Subgroup.mem_subgroupOf.mp hxU
  have hxab : x = szUgS n a b := by
    apply Subtype.ext
    rw [szUgS_coe]
    exact hab
  have hord : orderOf (szUgS n a b) = 2 := by rw [← hxab]; exact hx2
  have hsq : (szUgS n a b) ^ 2 = 1 := by
    have h := pow_orderOf_eq_one (szUgS n a b)
    rwa [hord] at h
  have ha : a = 0 := (szUgS_sq_eq_one_iff n a b).mp hsq
  refine ⟨b, ?_, by rw [hxab, ha]⟩
  intro hb
  have hx1 : x = 1 := by rw [hxab, ha, hb, szUgS_zero]
  rw [hx1, orderOf_one] at hx2
  exact absurd hx2 (by norm_num)

/-- **(1°) every `2`-element of the Borel subgroup of `Sz(2^(2n+1))` has order dividing `4`.** -/
theorem sz_borel_twoElement_pow_four (n : ℕ) (hn : 1 ≤ n) :
    ∀ x ∈ Submission.Sz.szBorelS n, (∃ k : ℕ, orderOf x = 2 ^ k) → x ^ 4 = 1 := by
  intro x hxB hpow
  obtain ⟨k, hk⟩ := hpow
  haveI := Submission.Sz.szTwoGroupS_subgroupOf_normal n
  have hxU' : (⟨x, hxB⟩ : ↥(Submission.Sz.szBorelS n)) ∈
      (Submission.Sz.szTwoGroupS n).subgroupOf (Submission.Sz.szBorelS n) :=
    sz_mem_two_pow_of_odd_index _ (k := k) (x := (⟨x, hxB⟩ : ↥(Submission.Sz.szBorelS n)))
      (by rw [Submission.Sz.szTwoGroupS_subgroupOf_index n]
          exact Submission.Sz.odd_two_pow_sub_one (2 * n + 1) (by omega))
      (by exact (Subgroup.orderOf_coe (⟨x, hxB⟩ : ↥(Submission.Sz.szBorelS n))).symm.trans hk)
  have hxU : x ∈ Submission.Sz.szTwoGroupS n := Subgroup.mem_subgroupOf.mp hxU'
  obtain ⟨a, b, hab⟩ := Subgroup.mem_subgroupOf.mp hxU
  have hxab : x = szUgS n a b := by
    apply Subtype.ext
    rw [szUgS_coe]
    exact hab
  rw [hxab]
  apply Subtype.ext
  rw [Subgroup.coe_pow, szUgS_coe, Subgroup.coe_one]
  exact Submission.Sz.szUg_pow_four n a b

/-- The Weyl element is an involution of `SzModel n`. -/
theorem szWgMS_mul_self (n : ℕ) : szWgMS n * szWgMS n = 1 := by
  apply Subtype.ext
  show Submission.Sz.szWg n * Submission.Sz.szWg n = 1
  exact Submission.Sz.szWg_mul_self n

/-- **The Suzuki `2`-group meets the centraliser of the Weyl element trivially.**  An element of
`U` fixed by conjugation by `w` lies in `U ⊓ w B w⁻¹ ≤ B ⊓ B^w = T`, and `U ⊓ T = ⊥`. -/
theorem sz_twoGroupS_inf_centralizer_szWgMS (n : ℕ) :
    Submission.Sz.szTwoGroupS n ⊓
      Subgroup.centralizer ({szWgMS n} : Set (SzModel n)) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  obtain ⟨hyU, hyC⟩ := Subgroup.mem_inf.mp hy
  rw [Subgroup.mem_centralizer_singleton_iff] at hyC
  have hwinv : (szWgMS n)⁻¹ = szWgMS n := inv_eq_of_mul_eq_one_right (szWgMS_mul_self n)
  have hyW : y ∈ (Submission.Sz.szBorelS n).map (MulAut.conj (szWgMS n)).toMonoidHom := by
    refine Subgroup.mem_map.mpr ⟨y, Submission.Sz.szTwoGroupS_le_szBorelS n hyU, ?_⟩
    show szWgMS n * y * (szWgMS n)⁻¹ = y
    rw [hwinv, ← hyC, mul_assoc y (szWgMS n) (szWgMS n), szWgMS_mul_self n, mul_one]
  have hyT : y ∈ Submission.Sz.szTS n := by
    rw [← Submission.Sz.szBorelS_inf_map_conj_eq n]
    exact Subgroup.mem_inf.mpr ⟨Submission.Sz.szTwoGroupS_le_szBorelS n hyU, hyW⟩
  have hmem : y ∈ Submission.Sz.szTwoGroupS n ⊓ Submission.Sz.szTS n := ⟨hyU, hyT⟩
  rw [Submission.Sz.szTS_inf_szTwoGroupS n] at hmem
  exact hmem


theorem sz_centralizer_inv_eq {G : Type*} [Group G] (z : G) :
    Subgroup.centralizer ({z⁻¹} : Set G) = Subgroup.centralizer ({z} : Set G) := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h1 : (x * z⁻¹) * x⁻¹ = z⁻¹ := (mul_inv_eq_iff_eq_mul).mpr h
    have h2 : x * z * x⁻¹ = z := by
      have := congrArg (fun w => w⁻¹) h1
      simpa [mul_assoc] using this
    exact (mul_inv_eq_iff_eq_mul).mp h2
  · intro h
    have h1 : (x * z) * x⁻¹ = z := (mul_inv_eq_iff_eq_mul).mpr h
    have h2 : (x * z⁻¹) * x⁻¹ = z⁻¹ := by
      have := congrArg (fun w => w⁻¹) h1
      simpa [mul_assoc] using this
    exact (mul_inv_eq_iff_eq_mul).mp h2

/-- **A fixed-point-free involution (an automorphism `α` with `α ∘ α = id` and no non-identity
fixed points) of a finite group is inversion.** -/
theorem MulAut.eq_inv_of_mul_self_eq_one_of_fixed_trivial {G : Type*} [Group G] [Finite G]
    (α : MulAut G) (hα : ∀ x, α (α x) = x) (hfix : ∀ x, α x = x → x = 1) :
    ∀ x, α x = x⁻¹ := by
  have hφ : Function.Injective (fun y : G => y⁻¹ * α y) := by
    intro p q hpq
    have hpq' : p⁻¹ * α p = q⁻¹ * α q := hpq
    have h1 : q * p⁻¹ = α (q * p⁻¹) := by
      have h' : q * p⁻¹ * α p = α q := by
        calc q * p⁻¹ * α p = q * (p⁻¹ * α p) := by group
          _ = q * (q⁻¹ * α q) := by rw [hpq']
          _ = α q := by group
      calc q * p⁻¹ = q * p⁻¹ * α p * (α p)⁻¹ := by group
        _ = α q * (α p)⁻¹ := by rw [h']
        _ = α (q * p⁻¹) := by rw [map_mul, map_inv]
    exact (eq_of_mul_inv_eq_one (hfix (q * p⁻¹) h1.symm)).symm
  have hsurj : Function.Surjective (fun y : G => y⁻¹ * α y) :=
    (Finite.injective_iff_surjective).mp hφ
  intro y
  obtain ⟨x, hx⟩ := hsurj y
  have hyx : (α x)⁻¹ * x = y⁻¹ := by rw [← hx]; group
  calc α y = α (x⁻¹ * α x) := by rw [← hx]
    _ = α (x⁻¹) * α (α x) := by rw [map_mul]
    _ = (α x)⁻¹ * x := by rw [map_inv α x, hα x]
    _ = y⁻¹ := hyx

/-- **`u` inverts `C(uw)` when `u` is an involution and `C(u) ⊓ C(uw) = 1`.**  Conjugation by `u`
is a fixed-point-free involution of the finite group `C(uw)`. -/
theorem sz_conj_eq_inv_of_fixed_trivial {G : Type*} [Group G] [Finite G] (u z : G)
    (hu2 : u * u = 1) (hz : u * z * u⁻¹ = z⁻¹)
    (hfix : ∀ x ∈ Subgroup.centralizer ({z} : Set G), u * x * u⁻¹ = x → x = 1) :
    ∀ x ∈ Subgroup.centralizer ({z} : Set G), u * x * u⁻¹ = x⁻¹ := by
  set C := Subgroup.centralizer ({z} : Set G) with hC
  have hu_inv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hz' : u⁻¹ * z * u = z⁻¹ := by
    rw [hu_inv] at hz ⊢; exact hz
  have hnormal : ∀ x ∈ C, u * x * u⁻¹ ∈ C := by
    intro x hx
    rw [hC, Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    have hxz1 : x * z⁻¹ = z⁻¹ * x := by
      have h1 : (x * z) * x⁻¹ = z := (mul_inv_eq_iff_eq_mul).mpr hx
      have h2 : (x * z⁻¹) * x⁻¹ = z⁻¹ := by
        have := congrArg (fun w => w⁻¹) h1
        simpa [mul_assoc] using this
      exact (mul_inv_eq_iff_eq_mul).mp h2
    have huz : u * z⁻¹ = z * u⁻¹ := by
      calc u * z⁻¹ = u * (u * z * u⁻¹) := by rw [← hz]
        _ = z * u⁻¹ := by
              rw [← mul_assoc u (u * z) u⁻¹, ← mul_assoc u u z, hu2, one_mul]
    have hzu : u⁻¹ * z = z⁻¹ * u := by
      have h := congrArg (fun w => w * u) hz'
      rwa [mul_assoc (u⁻¹ * z) u u, hu2, mul_one] at h
    calc u * x * u⁻¹ * z = u * x * (u⁻¹ * z) := by group
      _ = u * x * (z⁻¹ * u) := by rw [hzu]
      _ = u * (x * z⁻¹) * u := by group
      _ = u * (z⁻¹ * x) * u := by rw [hxz1]
      _ = u * z⁻¹ * x * u := by group
      _ = z * u⁻¹ * x * u := by rw [huz]
      _ = z * (u⁻¹ * x * u) := by group
      _ = z * (u * x * u⁻¹) := by rw [hu_inv]
  have hnormal' : ∀ x ∈ C, u⁻¹ * x * u ∈ C := by
    intro x hx
    simpa [hu_inv] using hnormal x hx
  let α : MulAut ↥C :=
    { toFun := fun x => ⟨u * (x : G) * u⁻¹, hnormal x x.2⟩
      invFun := fun x => ⟨u⁻¹ * (x : G) * u, hnormal' x x.2⟩
      left_inv := fun x => Subtype.ext (by group)
      right_inv := fun x => Subtype.ext (by group)
      map_mul' := fun x y => Subtype.ext (by
        show u * ((x : G) * (y : G)) * u⁻¹ = (u * (x : G) * u⁻¹) * (u * (y : G) * u⁻¹)
        group) }
  have hα_apply : ∀ x : ↥C, ((α x : ↥C) : G) = u * (x : G) * u⁻¹ := fun x => rfl
  have hα : ∀ x : ↥C, α (α x) = x := by
    intro x
    apply Subtype.ext
    rw [hα_apply (α x), hα_apply x]
    rw [show u * (u * (x : G) * u⁻¹) * u⁻¹ = (u * u) * (x : G) * (u * u) by
      rw [hu_inv]; group, hu2]
    simp
  have hfix' : ∀ x : ↥C, α x = x → x = 1 := by
    intro x hx
    have hx' : u * (x : G) * u⁻¹ = (x : G) := by
      have h2 := congrArg (fun w : ↥C => (w : G)) hx
      rw [hα_apply] at h2
      exact h2
    have := hfix (x : G) x.2 hx'
    exact Subtype.ext (by rw [this, Subgroup.coe_one])
  have hfin := MulAut.eq_inv_of_mul_self_eq_one_of_fixed_trivial α hα hfix'
  intro x hx
  have h := congrArg (fun w : ↥C => (w : G)) (hfin ⟨x, hx⟩)
  rw [hα_apply] at h
  simpa using h


theorem sz_benderFacts2For_conj {G : Type*} [Group G] [Finite G] (H : Subgroup G) (g : G)
    (h : BenderFacts2For G H) :
    BenderFacts2For G (H.map (MulAut.conj g).toMonoidHom) := by
  classical
  obtain ⟨h1, h2⟩ := h
  constructor
  · intro x hx hpow
    obtain ⟨k, hk⟩ := hpow
    have hxH : g⁻¹ * x * g ∈ H := (sz_mem_map_conj H g x).mp hx
    have hk' : orderOf (g⁻¹ * x * g) = 2 ^ k := by rw [sz_orderOf_conj, hk]
    have h4 : (g⁻¹ * x * g) ^ 4 = 1 := h1 _ hxH ⟨k, hk'⟩
    have hg4 : (g⁻¹ * x * g) ^ 4 = g⁻¹ * x ^ 4 * g := by
      have h1' : g⁻¹ * x * g = (MulAut.conj g⁻¹) x := by rw [MulAut.conj_apply]; group
      rw [h1', ← map_pow, MulAut.conj_apply]
      group
    have h4' : g⁻¹ * x ^ 4 * g = 1 := hg4 ▸ h4
    calc x ^ 4 = g * (g⁻¹ * x ^ 4 * g) * g⁻¹ := by group
      _ = 1 := by rw [h4']; group
  · intro u hu t ht2 htH
    have hu' : g⁻¹ * u * g ∈ H := (sz_mem_map_conj H g u).mp hu.1
    have hu2' : orderOf (g⁻¹ * u * g) = 2 := by rw [sz_orderOf_conj, hu.2]
    have ht2' : orderOf (g⁻¹ * t * g) = 2 := by rw [sz_orderOf_conj, ht2]
    have htH' : g⁻¹ * t * g ∉ H := by
      intro hm
      exact htH ((sz_mem_map_conj H g t).mpr hm)
    obtain ⟨hcyc, hinv, hcard⟩ :=
      h2 (g⁻¹ * u * g) ⟨hu', hu2'⟩ (g⁻¹ * t * g) ht2' htH'
    set u' : G := g⁻¹ * u * g with hu'def
    set z' : G := u' * (g⁻¹ * t * g) with hz'def
    have hmid : g⁻¹ * (u * t) * g = z' := by rw [hz'def, hu'def]; group
    have hce : Subgroup.centralizer ({u * t} : Set G)
        = (Subgroup.centralizer ({z'} : Set G)).map (MulAut.conj g).toMonoidHom := by
      rw [sz_centralizer_conj_eq (u * t) g, hmid]
    have hcyc' : IsCyclic ↥(Subgroup.centralizer ({u * t} : Set G)) := by
      rw [hce]
      exact (Subgroup.equivMapOfInjective _ (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).isCyclic.mp hcyc
    refine ⟨hcyc', ?_, ?_⟩
    · intro y hy
      rw [hce] at hy
      obtain ⟨y', hy', hye⟩ := Subgroup.mem_map.mp hy
      have hyy : y = g * y' * g⁻¹ := by rw [← hye, sz_conj_apply]
      have hy'' : u' * y' * u'⁻¹ = y'⁻¹ := hinv y' hy'
      have hu_eq : u = g * u' * g⁻¹ := by rw [hu'def]; group
      rw [hyy, hu_eq]
      calc g * u' * g⁻¹ * (g * y' * g⁻¹) * (g * u' * g⁻¹)⁻¹
          = g * (u' * y' * u'⁻¹) * g⁻¹ := by group
        _ = g * y'⁻¹ * g⁻¹ := by rw [hy'']
        _ = (g * y' * g⁻¹)⁻¹ := by group
    · intro h127
      have h127' : 127 ≤ (Submission.Blueprint.involutions (H : Set G)).ncard := by
        rw [← sz_ncard_involutions_conj H g]; exact h127
      have h6 := hcard h127'
      have hcard_eq : Nat.card ↥(Subgroup.centralizer ({u * t} : Set G))
          = Nat.card ↥(Subgroup.centralizer ({z'} : Set G)) := by
        rw [hce, Subgroup.card_map_of_injective (MulAut.conj g).injective]
      rw [hcard_eq]; exact h6

/-- A `2`-power bound: for `n ≥ 2` the smallest Suzuki torus order `q + 1 - √(2q)` is `≥ 6`. -/
theorem sz_two_pow_torus_bound (n : ℕ) (hn : 2 ≤ n) :
    6 ≤ 2 ^ (2 * n + 1) + 1 - 2 ^ (n + 1) := by
  have hH : 2 ^ (n + 1) * 3 ≤ 2 ^ (2 * n + 1) := by
    rw [show 2 ^ (2 * n + 1) = 2 ^ (n + 1) * 2 ^ n by rw [← pow_add]; congr 1; omega]
    exact Nat.mul_le_mul_left _ (by
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn)
  have hH3 : 3 ≤ 2 ^ (n + 1) :=
    calc 3 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hHle : 2 ^ (n + 1) ≤ 2 ^ (2 * n + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- **Clause (2°) for the Borel subgroup**, with the two Suzuki-torus facts about
`C(u(0,c)·w)` taken as hypotheses (they are the content of
`sz_torus_centralizer_isCyclic` and `sz_torus_centralizer_card_ge`).

Route: `u ∈ Inv B` is an involution of the Suzuki `2`-group, hence `u = u(0,c)` with `c ≠ 0`;
`t` is `B`-conjugate to the Weyl element `w`; then `ut` is `g`-conjugate to `u(0,c')·w`, and all
three clauses transport. -/
theorem sz_borel_clause2_aux (n : ℕ) (hn : 1 ≤ n)
    (hcyc : ∀ c : Submission.Sz.SzField n, c ≠ 0 → IsCyclic
      ↥(Subgroup.centralizer ({szUgS n 0 c * szWgMS n} : Set (SzModel n))))
    (hcard : ∀ c : Submission.Sz.SzField n, c ≠ 0 →
      2 ^ (2 * n + 1) + 1 - 2 ^ (n + 1) ≤ Nat.card
        ↥(Subgroup.centralizer ({szUgS n 0 c * szWgMS n} : Set (SzModel n)))) :
    ∀ u ∈ Submission.Blueprint.involutions (Submission.Sz.szBorelS n : Set (SzModel n)),
    ∀ t : SzModel n, orderOf t = 2 → t ∉ Submission.Sz.szBorelS n →
      IsCyclic ↥(Subgroup.centralizer ({u * t} : Set (SzModel n))) ∧
      (∀ y ∈ Subgroup.centralizer ({u * t} : Set (SzModel n)), u * y * u⁻¹ = y⁻¹) ∧
      (127 ≤ (Submission.Blueprint.involutions
          (Submission.Sz.szBorelS n : Set (SzModel n))).ncard →
        6 ≤ Nat.card ↥(Subgroup.centralizer ({u * t} : Set (SzModel n)))) := by
  intro u hu t ht2 htB
  -- `u` is an involution of the Suzuki `2`-group.
  have huU : u ∈ Submission.Sz.szTwoGroupS n :=
    Submission.Sz.mem_szTwoGroupS_of_orderOf_coe_eq_two n hu.1
      ((Subgroup.orderOf_coe (⟨u, hu.1⟩ : ↥(Submission.Sz.szBorelS n))).symm.trans hu.2)
  obtain ⟨c, hc, hu_eq⟩ := exists_szUgS_zero_of_mem_szTwoGroupS n huU hu.2
  -- `t` is `B`-conjugate to the Weyl element.
  obtain ⟨β, hβB, hβt⟩ := Work.PSU3.BST.sz_wTrans n hn t ht2 htB
  set g : SzModel n := β⁻¹ with hg
  -- `β u β⁻¹` is again an involution of `U`.
  have hu''U : β * u * β⁻¹ ∈ Submission.Sz.szTwoGroupS n := by
    haveI := Submission.Sz.szTwoGroupS_subgroupOf_normal n
    have hx : (⟨u, hu.1⟩ : ↥(Submission.Sz.szBorelS n)) ∈
        (Submission.Sz.szTwoGroupS n).subgroupOf (Submission.Sz.szBorelS n) :=
      Subgroup.mem_subgroupOf.mpr huU
    have hconj := (inferInstance : ((Submission.Sz.szTwoGroupS n).subgroupOf
      (Submission.Sz.szBorelS n)).Normal).conj_mem (⟨u, hu.1⟩ : ↥(Submission.Sz.szBorelS n))
        hx (⟨β, hβB⟩ : ↥(Submission.Sz.szBorelS n))
    have hc' := Subgroup.mem_subgroupOf.mp hconj
    simpa using hc'
  have hu''2 : orderOf (β * u * β⁻¹) = 2 := by
    rw [show β * u * β⁻¹ = (β⁻¹)⁻¹ * u * β⁻¹ by group, sz_orderOf_conj, hu.2]
  obtain ⟨c', hc', hu''_eq⟩ := exists_szUgS_zero_of_mem_szTwoGroupS n hu''U hu''2
  set z' : SzModel n := szUgS n 0 c' * szWgMS n with hz'def
  -- `t` and `u` in terms of `g` and the reduced data.
  have hβt' : β * t * β⁻¹ = szWgMS n := hβt
  have ht_eq : t = g * szWgMS n * g⁻¹ := by rw [hg, ← hβt']; group
  have hu_eq' : u = g * (szUgS n 0 c') * g⁻¹ := by rw [hg, ← hu''_eq]; group
  have hz_eq : u * t = g * z' * g⁻¹ := by rw [hu_eq', ht_eq, hz'def]; group
  have hu2 : szUgS n 0 c' * szUgS n 0 c' = 1 := by
    have h := pow_orderOf_eq_one (szUgS n 0 c')
    rw [orderOf_szUgS_zero n hc'] at h
    simpa [pow_two] using h
  have hwinv : (szWgMS n)⁻¹ = szWgMS n := inv_eq_of_mul_eq_one_right (szWgMS_mul_self n)
  have huinv : (szUgS n 0 c')⁻¹ = szUgS n 0 c' := inv_eq_of_mul_eq_one_right hu2
  have hzw : szWgMS n = szUgS n 0 c' * z' := by
    rw [hz'def, ← mul_assoc, hu2, one_mul]
  have hz_inv : (szUgS n 0 c') * z' * (szUgS n 0 c')⁻¹ = z'⁻¹ := by
    calc szUgS n 0 c' * z' * (szUgS n 0 c')⁻¹
        = szUgS n 0 c' * (szUgS n 0 c' * szWgMS n) * (szUgS n 0 c')⁻¹ := by rw [hz'def]
      _ = szWgMS n * (szUgS n 0 c')⁻¹ := by rw [← mul_assoc, hu2, one_mul]
      _ = (szUgS n 0 c' * szWgMS n)⁻¹ := by rw [mul_inv_rev, hwinv, huinv]
      _ = z'⁻¹ := by rw [hz'def]
  -- `u(0,c')` inverts `C(z')`.
  have hinv'' : ∀ y ∈ Subgroup.centralizer ({z'} : Set (SzModel n)),
      szUgS n 0 c' * y * (szUgS n 0 c')⁻¹ = y⁻¹ := by
    refine sz_conj_eq_inv_of_fixed_trivial (szUgS n 0 c') z' hu2 hz_inv ?_
    · intro x hx hfix
      have hcomm : szUgS n 0 c' * x = x * szUgS n 0 c' := by
        have h := congrArg (fun z => z * szUgS n 0 c') hfix
        simp only [mul_assoc, inv_mul_cancel, mul_one] at h
        exact h
      have hxU : x ∈ Submission.Sz.szTwoGroupS n := by
        have hxC : x ∈ Subgroup.centralizer ({szUgS n 0 c'} : Set (SzModel n)) := by
          rw [Subgroup.mem_centralizer_singleton_iff]; exact hcomm.symm
        rwa [sz_centralizer_involution_eq_U n hn hc'] at hxC
      have hxW : x ∈ Subgroup.centralizer ({szWgMS n} : Set (SzModel n)) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        rw [Subgroup.mem_centralizer_singleton_iff] at hx
        calc x * szWgMS n = x * (szUgS n 0 c' * z') := by rw [hzw]
          _ = (x * szUgS n 0 c') * z' := by group
          _ = (szUgS n 0 c' * x) * z' := by rw [hcomm]
          _ = szUgS n 0 c' * (x * z') := by group
          _ = szUgS n 0 c' * (z' * x) := by rw [hx]
          _ = (szUgS n 0 c' * z') * x := by group
          _ = szWgMS n * x := by rw [hzw]
      have hmem : x ∈ Submission.Sz.szTwoGroupS n ⊓
          Subgroup.centralizer ({szWgMS n} : Set (SzModel n)) := ⟨hxU, hxW⟩
      rw [sz_twoGroupS_inf_centralizer_szWgMS n] at hmem
      exact hmem
  -- transport to `C(u t)`
  have hce : Subgroup.centralizer ({u * t} : Set (SzModel n))
      = (Subgroup.centralizer ({z'} : Set (SzModel n))).map (MulAut.conj g).toMonoidHom := by
    rw [sz_centralizer_conj_eq (u * t) g]
    have : g⁻¹ * (u * t) * g = z' := by rw [hz_eq]; group
    rw [this]
  refine ⟨?_, ?_, ?_⟩
  · rw [hce]
    exact (Subgroup.equivMapOfInjective _ (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).isCyclic.mp (hcyc c' hc')
  · intro y hy
    rw [hce] at hy
    obtain ⟨y', hy', hye⟩ := Subgroup.mem_map.mp hy
    have hyy : y = g * y' * g⁻¹ := by rw [← hye, sz_conj_apply]
    have hy'' := hinv'' y' hy'
    rw [hyy, hu_eq']
    calc g * (szUgS n 0 c') * g⁻¹ * (g * y' * g⁻¹) * (g * (szUgS n 0 c') * g⁻¹)⁻¹
        = g * (szUgS n 0 c' * y' * (szUgS n 0 c')⁻¹) * g⁻¹ := by group
      _ = g * y'⁻¹ * g⁻¹ := by rw [hy'']
      _ = (g * y' * g⁻¹)⁻¹ := by group
  · intro h127
    have hInv : 127 ≤ 2 ^ (2 * n + 1) - 1 := by
      rwa [Work.Models.Sz.ncard_involutions_szBorelS n] at h127
    have hn2 : 2 ≤ n := by
      have hX1 : 1 ≤ 2 ^ (2 * n + 1) := Nat.one_le_two_pow
      have h128 : 128 ≤ 2 ^ (2 * n + 1) := by omega
      have h27 : 2 ^ 7 ≤ 2 ^ (2 * n + 1) := by
        rw [show 2 ^ 7 = 128 by norm_num]; exact h128
      have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h27
      omega
    have hcard_eq : Nat.card ↥(Subgroup.centralizer ({u * t} : Set (SzModel n)))
        = Nat.card ↥(Subgroup.centralizer ({z'} : Set (SzModel n))) := by
      rw [hce, Subgroup.card_map_of_injective (MulAut.conj g).injective]
    rw [hcard_eq]
    exact le_trans (sz_two_pow_torus_bound n hn2) (hcard c' hc')

/-- **The lead's `BenderModelFacts2Prop` for `Sz(2^(2n+1))`** (`n ≥ 1`), with `Y = SzModel n`. Route: reduce to `H = B` with `Submission.Sz.szStronglyEmbedded_eq_benderPair_borel` (conjugation preserves `orderOf`, `x ^ 4 = 1`, the centraliser up to isomorphism, `IsCyclic`, the number of involutions and `IsZassenhaus` — prove the transport directly or via the group-theoretic form of the three-point condition `∀ x y, x ∉ H → y ∉ H → x⁻¹ * y ∉ H → H ⊓ conj x H ⊓ conj y H = ⊥`). (1°) `B = U ⋊ T` with `T = szTS n` of odd order `q - 1` and `U = szTwoGroupS n`; a 2-element of `B` has trivial image in `B ⧸ U`, hence lies in the Suzuki 2-group, whose elements have order dividing `4` (`szTwoGroup_orderOf_dvd_four`, `mem_szTwoGroupS_of_sq_eq_one`, `szUg_sq_eq_one_iff`). (2°) `w := szWgM n`; every involution outside `B` is `B`-conjugate to `w`, and `u ∈ Inv B ⊆ U` is `u(0,b)` (`szUg_sq_eq_one_iff`). The structure theory of `Sz(q)` (`q = 2^(2n+1)`) gives maximal tori of orders `q - 1`, `q + 1 + √(2q)`, `q + 1 - √(2q)`; `C(u * w)` is one of them (GAP-verified for `q = 8`: orders 5, 7, 13), hence cyclic and inverted by `u`, and `q + 1 - √(2q) ≥ 6` once `q ≥ 128`, which is what `127 ≤ #Inv H = q - 1` gives. Useful files: `Work.Models.Port.Sz.{Basic,Torus,Weyl,Main,Bruhat,Root,Involutions}`, `Work.Models.Sz.{szTS_comm,szTS_eq_invertedBy,ncard_involutions_szBorelS,szTwoGroupS_inv_central}`, `Work.Models.ModelData.szModelData`. -/
theorem sz_benderModelFacts2 (n : ℕ) (hn : 1 ≤ n) :
    ∀ H : Subgroup (LeanEval.GroupTheory.Defs.SzModel n),
      LeanEval.GroupTheory.Defs.IsStronglyEmbedded H →
      (∀ x ∈ H, (∃ k : ℕ, orderOf x = 2 ^ k) → x ^ 4 = 1) ∧
      (Submission.Blueprint.IsZassenhaus H →
        ∀ u ∈ Submission.Blueprint.involutions (H : Set (LeanEval.GroupTheory.Defs.SzModel n)),
        ∀ t : LeanEval.GroupTheory.Defs.SzModel n, orderOf t = 2 → t ∉ H →
        IsCyclic ↥(Subgroup.centralizer ({u * t} : Set (LeanEval.GroupTheory.Defs.SzModel n))) ∧
        (∀ y ∈ Subgroup.centralizer ({u * t} : Set (LeanEval.GroupTheory.Defs.SzModel n)),
          u * y * u⁻¹ = y⁻¹) ∧
        (127 ≤ (Submission.Blueprint.involutions
            (H : Set (LeanEval.GroupTheory.Defs.SzModel n))).ncard →
          6 ≤ Nat.card ↥(Subgroup.centralizer
            ({u * t} : Set (LeanEval.GroupTheory.Defs.SzModel n))))) := by
  have hBorel : BenderFacts2For (SzModel n) (Submission.Sz.szBorelS n) :=
    ⟨sz_borel_twoElement_pow_four n hn,
      sz_borel_clause2_aux n hn
        (fun c hc => sz_torus_centralizer_isCyclic n hn hc)
        (fun c hc => sz_torus_centralizer_card_ge n hn hc)⟩
  intro H hH
  obtain ⟨g, hg⟩ := Submission.Sz.szStronglyEmbedded_eq_benderPair_borel n hn H hH
  have hconj := sz_benderFacts2For_conj (Submission.Sz.szBorelS n) g hBorel
  have hH' : H = (Submission.Sz.szBorelS n).map (MulAut.conj g).toMonoidHom := by
    rw [hg]; rfl
  rw [← hH'] at hconj
  exact ⟨hconj.1, fun hZ u hu t ht2 htH => hconj.2 u hu t ht2 htH⟩

end Work.BSLit.BenderFacts2
