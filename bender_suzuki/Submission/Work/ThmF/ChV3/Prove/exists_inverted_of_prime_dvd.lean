import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Coprime action of an involution on a group of odd order (step (13a))

If an involution `u` (i.e. `orderOf u = 2`) normalises a finite subgroup `X` of odd order, and
`r` is a prime that divides `|X|` but not `|C_X(u)|`, then some element of `X` of order `r` is
inverted by `u`.

The argument is the standard one sketched in the design of step (13a):

* the number of Sylow `r`-subgroups of `X` divides `|X|`, hence is odd, so the involution
  `u` — which permutes them by conjugation — fixes one of them, say `R`;
* `R` is an `r`-group normalised by `u`, and since `r ∤ |C_X(u)|` the involution `u` acts on `R`
  without fixed points;
* for `x ∈ R` the element `φ(x) · x⁻¹` (where `φ` is conjugation by `u`) is again inverted by
  `φ` and is non-trivial, so its order is a power of `r`; raising it to a suitable power produces
  an element of `X` of order `r` inverted by `u`.
-/

open scoped Pointwise

set_option linter.style.haveILetI false

namespace Work.ThmF.ChV3.Prove

open Work.ThmF.ChV3

/-- The automorphism of `X` induced by an element `u` of `N_G(X)` (conjugation by `u`). -/
noncomputable def conjAut {G : Type} [Group G] {X : Subgroup G} {u : G}
    (hu : u ∈ Subgroup.normalizer (X : Set G)) : MulAut ↥X :=
  Subgroup.normalizerMonoidHom X ⟨u, hu⟩

/-- `conjAut hu` acts on a point by conjugation by `u` in the ambient group. -/
lemma conjAut_coe {G : Type} [Group G] {X : Subgroup G} {u : G}
    (hu : u ∈ Subgroup.normalizer (X : Set G)) (x : ↥X) :
    ((conjAut hu x : ↥X) : G) = u * (x : G) * u⁻¹ := by
  rw [conjAut,
    show Subgroup.normalizerMonoidHom X ⟨u, hu⟩
        = MulDistribMulAction.toMulAut ↥(Subgroup.normalizer (X : Set G)) ↥X ⟨u, hu⟩ from rfl,
    MulDistribMulAction.toMulAut_apply, MulDistribMulAction.toMulEquiv_apply]
  exact Subgroup.smul_coe X ⟨u, hu⟩ x

/-- For an involution `u`, the induced automorphism has order dividing two. -/
lemma conjAut_sq {G : Type} [Group G] {X : Subgroup G} {u : G}
    (hu : u ∈ Subgroup.normalizer (X : Set G)) (hu2 : orderOf u = 2) :
    conjAut hu ^ 2 = 1 := by
  rw [conjAut, ← map_pow]
  have h2 : (⟨u, hu⟩ : ↥(Subgroup.normalizer (X : Set G))) ^ 2 = 1 := by
    apply Subtype.ext
    have : u ^ 2 = 1 := by
      have h := pow_orderOf_eq_one u
      rw [hu2] at h
      simpa using h
    simpa using this
  rw [h2, map_one]

theorem exists_inverted_of_prime_dvd {G : Type} [Group G] [Finite G] {X : Subgroup G} {u : G} (hodd : Odd (Nat.card X))
    (hu : orderOf u = 2) (huX : u ∈ Work.ThmF.ChV3.NG X) {r : ℕ} (hr : r.Prime)
    (hrX : r ∣ Nat.card X)
    (hrC : ¬ r ∣ Nat.card ↥(X ⊓ Subgroup.centralizer ({u} : Set G))) :
    ∃ x ∈ X, orderOf x = r ∧ u * x * u⁻¹ = x⁻¹ := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  -- `u` normalises `X`; view it as an element of the normalizer.
  have huN : u ∈ Subgroup.normalizer (X : Set G) := huX
  -- The number of Sylow `r`-subgroups of `X` divides `|X|`, hence is odd.
  have hSylow_dvd : Nat.card (Sylow r ↥X) ∣ Nat.card ↥X := by
    obtain ⟨P⟩ := Sylow.nonempty (p := r) (G := ↥X)
    have h1 : Nat.card (Sylow r ↥X) ∣ P.toSubgroup.index := Sylow.card_dvd_index P
    have h2 : P.toSubgroup.index ∣ Nat.card ↥X :=
      ⟨Nat.card ↥P.toSubgroup,
        by rw [mul_comm]; exact (Subgroup.card_mul_index P.toSubgroup).symm⟩
    exact h1.trans h2
  have hSylow_odd : Odd (Nat.card (Sylow r ↥X)) := Odd.of_dvd_nat hodd hSylow_dvd
  -- An involution acting on an odd number of Sylow subgroups has a fixed point.
  letI : Fintype (Sylow r ↥X) := Fintype.ofFinite _
  have hcard : ¬ 2 ∣ Fintype.card (Sylow r ↥X) := by
    rw [← Nat.card_eq_fintype_card]
    intro h2
    exact Nat.not_even_iff_odd.mpr hSylow_odd (even_iff_two_dvd.mpr h2)
  have hσ : (MulAction.toPermHom (MulAut ↥X) (Sylow r ↥X) (conjAut huN)) ^ (2 ^ 1) = 1 := by
    rw [pow_one, ← map_pow, conjAut_sq huN hu, map_one]
  obtain ⟨a, ha⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := 1) hcard hσ
  rw [MulAction.toPermHom_apply, MulAction.toPerm_apply] at ha
  -- `ha : conjAut huN • a = a`; the Sylow subgroup `a` is stabilised by the automorphism.
  have hmem : ∀ x : ↥X, x ∈ (a : Subgroup ↥X) → conjAut huN x ∈ (a : Subgroup ↥X) := by
    intro x hx
    have h1 : ↑(conjAut huN • a) = (conjAut huN) • (a : Subgroup ↥X) :=
      Sylow.pointwise_smul_def
    rw [ha] at h1
    rw [Subgroup.pointwise_smul_def] at h1
    rw [MulDistribMulAction.toMonoidEnd_apply] at h1
    rw [h1]
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  -- `u` does not centralise `a`: otherwise `a ≤ C_X(u)` would give `r ∣ |C_X(u)|`.
  have hex : ∃ x : ↥X, x ∈ (a : Subgroup ↥X) ∧ conjAut huN x ≠ x := by
    by_contra h
    have h' : ∀ x : ↥X, x ∈ (a : Subgroup ↥X) → conjAut huN x = x := by
      intro x hxA
      by_contra hx
      exact h ⟨x, hxA, hx⟩
    have hrdvd : r ∣ Nat.card ↥(a : Subgroup ↥X) :=
      (a : Sylow r ↥X).dvd_card_of_dvd_card (by simpa using hrX)
    obtain ⟨x0, hx0⟩ := exists_prime_orderOf_dvd_card' r hrdvd
    have hx0mem : (x0 : ↥X) ∈ (a : Subgroup ↥X) := x0.2
    have hfix : conjAut huN (x0 : ↥X) = (x0 : ↥X) := h' (x0 : ↥X) hx0mem
    have hconj : u * ((x0 : ↥X) : G) * u⁻¹ = ((x0 : ↥X) : G) := by
      have h := conjAut_coe huN (x0 : ↥X)
      rw [hfix] at h
      exact h.symm
    have hcomm : ((x0 : ↥X) : G) * u = u * ((x0 : ↥X) : G) := by
      have key : u * ((x0 : ↥X) : G) = ((x0 : ↥X) : G) * u := by
        have h2 := congrArg (fun z => z * u) hconj
        simpa [mul_assoc] using h2
      exact key.symm
    have hmemC : ((x0 : ↥X) : G) ∈ Subgroup.centralizer ({u} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hcomm
    have hmemBoth : ((x0 : ↥X) : G) ∈ X ⊓ Subgroup.centralizer ({u} : Set G) :=
      ⟨(x0 : ↥X).2, hmemC⟩
    have hord : orderOf ((x0 : ↥X) : G) = r := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx0]
    exact hrC (hord ▸ Subgroup.orderOf_dvd_natCard _ hmemBoth)
  obtain ⟨x, hxmem, hxne⟩ := hex
  -- `y = φ x · x⁻¹ ∈ a` is inverted by `φ` and non-trivial.
  have hyR : conjAut huN x * x⁻¹ ∈ (a : Subgroup ↥X) :=
    (a : Subgroup ↥X).mul_mem (hmem x hxmem) ((a : Subgroup ↥X).inv_mem hxmem)
  have hxx : conjAut huN (conjAut huN x) = x := by
    have h := congrArg (fun g : MulAut ↥X => g x) (conjAut_sq huN hu)
    simpa [pow_two] using h
  have hy_inv : conjAut huN (conjAut huN x * x⁻¹) = (conjAut huN x * x⁻¹)⁻¹ := by
    rw [map_mul, map_inv, hxx]
    group
  have hy_ne : conjAut huN x * x⁻¹ ≠ 1 := by
    intro h1
    apply hxne
    have h2 := congrArg (fun z : ↥X => z * x) h1
    simpa [mul_assoc] using h2
  -- The order of `y` is a power of `r`, say `r ^ j` with `j ≥ 1`.
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (a : Sylow r ↥X).isPGroup'
  have hydvd : orderOf (conjAut huN x * x⁻¹) ∣ r ^ k := by
    rw [← hk]
    exact Subgroup.orderOf_dvd_natCard _ hyR
  obtain ⟨j, _hjle, hj⟩ := (Nat.dvd_prime_pow hr).mp hydvd
  have hj1 : 1 ≤ j := by
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    rw [h0, pow_zero] at hj
    exact hy_ne (orderOf_eq_one_iff.mp hj)
  -- `z = y ^ (r ^ (j-1))` has order `r` and is inverted by `u`.
  have hzpow : ((conjAut huN x * x⁻¹) ^ (r ^ (j - 1))) ^ r = 1 := by
    rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel hj1, ← hj, pow_orderOf_eq_one]
  have hzne : (conjAut huN x * x⁻¹) ^ (r ^ (j - 1)) ≠ 1 := by
    intro h1
    have hdvd : orderOf (conjAut huN x * x⁻¹) ∣ r ^ (j - 1) :=
      orderOf_dvd_iff_pow_eq_one.mpr h1
    rw [hj] at hdvd
    have hle : j ≤ j - 1 := (Nat.pow_dvd_pow_iff_le_right hr.one_lt).mp hdvd
    omega
  refine ⟨(((conjAut huN x * x⁻¹) ^ (r ^ (j - 1)) : ↥X) : G), ?_, ?_, ?_⟩
  · exact ((conjAut huN x * x⁻¹) ^ (r ^ (j - 1)) : ↥X).2
  · rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime hzpow hzne
  · have hφz : conjAut huN ((conjAut huN x * x⁻¹) ^ (r ^ (j - 1)))
        = ((conjAut huN x * x⁻¹) ^ (r ^ (j - 1)))⁻¹ := by
      rw [map_pow, hy_inv, inv_pow]
    rw [← conjAut_coe huN ((conjAut huN x * x⁻¹) ^ (r ^ (j - 1))), hφz, Subgroup.coe_inv]

end Work.ThmF.ChV3.Prove
