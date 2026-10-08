import Mathlib
import Submission.Work.Frobenius.Main
import Submission.Work.Coprime.Basic
import Submission.Work.PGroup.Omega1
import Submission.Work.Frobenius.Complement.abelian_fpf_representation_isCyclic
import Submission.Work.Frobenius.Complement.exists_invariant_sylow_of_isSolvable
import Submission.Work.Frobenius.Complement.no_fpf_module_of_nonabelian_pq
import Submission.Work.Frobenius.Complement.exists_conj_action_of_nonabelian_card_eq_mul_primes
import Submission.Work.Frobenius.Complement.false_of_fpf_action_elementaryAbelian
import Submission.Work.Frobenius.Complement.isSolvable_of_card_eq_mul_primes

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# FT 3.16(ii): subgroups of order `p * q` of a Frobenius complement are cyclic

If `H` is a Frobenius complement in the finite group `G` (so that `H` acts fixed-point-freely
by conjugation on the Frobenius kernel `N ≤ G`, with `|N|` coprime to `|H|`), then every
subgroup `K ≤ H` whose order is the product of two primes is cyclic.

The proof is the classical one, organised as follows.

* `isCyclic_of_commutative_card_eq_mul_primes`: a commutative group of order `p * q` with
  `p ≠ q` primes is cyclic.
* `isCyclic_of_fpf_action_on_elementaryAbelian` (private): a finite commutative group acting
  fixed-point-freely on a nontrivial finite commutative group of exponent a prime `r` is
  cyclic; the group becomes a nontrivial finite-dimensional `𝔽_r`-vector space and the
  fixed-point-free action is a fixed-point-free representation
  (`abelian_fpf_representation_isCyclic`).
* `isCyclic_of_abelian_fpf_action` (private): an abelian group acting fixed-point-freely on a
  group carrying an invariant nontrivial elementary abelian subgroup is cyclic.
* `isCyclic_of_card_eq_mul_primes_of_fpf`: **the heart** — a group `A` of order `p * q` acting
  fixed-point-freely (with `(|A|,|N|) = 1`) on a nontrivial finite group `N` is cyclic.
  If `A` is abelian this is immediate (`p ≠ q`) or follows from the previous items (`p = q`).
  If `A` is nonabelian, the classical structure of groups of order `p * q` provides `x, y` of
  prime order with `x * y * x⁻¹ = y ^ s`, `s ≢ 1 (mod q)`; the coprime action
  `exists_invariant_elementaryAbelian_of_solvable_action` supplies an invariant nontrivial
  elementary abelian subgroup `W`, which is a nontrivial module over `𝔽_r`, and
  `false_of_fpf_action_elementaryAbelian` contradicts the fixed-point-freeness of the actions
  of `x` and `y` on it.
* `isCyclic_of_card_eq_mul_primes`: the target, obtained by applying the previous item to the
  conjugation action of `K` on the Frobenius kernel of `G`.
-/

set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Pointwise IsMulCommutative
open Subgroup
open Additive

namespace Work.Frobenius.Complement

/-! ## Part 1: an abelian group of order `p * q` with `p ≠ q` is cyclic -/

lemma isCyclic_of_commutative_card_eq_mul_primes {A : Type*} [Group A] [Finite A] [IsMulCommutative A]
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hcard : Nat.card A = p * q) :
    IsCyclic A := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p (hcard ▸ dvd_mul_right p q)
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' q (hcard ▸ dvd_mul_left q p)
  have hcomm : Commute x y := isMulCommutative_iff.mp (inferInstance : IsMulCommutative A) x y
  have hcop : (orderOf x).Coprime (orderOf y) := by
    rw [hx, hy]
    exact hp.coprime_iff_not_dvd.mpr
      (fun h => hpq (((Nat.dvd_prime hq).mp h).resolve_left hp.ne_one))
  have hxy : orderOf (x * y) = p * q := by
    rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop, hx, hy]
  exact isCyclic_of_orderOf_eq_card (x * y) (by rw [hxy, hcard])

/-! ## Part 2: an abelian group acting fpf on a nontrivial finite group is cyclic -/

/-- A finite commutative group acting fixed-point-freely on a nontrivial finite commutative group
of exponent a prime is cyclic. -/
private theorem isCyclic_of_fpf_action_on_elementaryAbelian {A W : Type*} [Group A] [Finite A]
    [IsMulCommutative A] [Group W] [Finite W] [IsMulCommutative W] [Nontrivial W]
    [MulDistribMulAction A W] {r : ℕ} (hr : r.Prime) (hexp : ∀ w : W, w ^ r = 1)
    (hfp : ∀ a : A, a ≠ 1 → ∀ w : W, a • w = w → w = 1) : IsCyclic A := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hr0 : ∀ x : Additive W, r • x = 0 := fun x => by
    rw [← ofMul_toMul x, ← ofMul_pow, hexp, ofMul_one]
  haveI : Module (ZMod r) (Additive W) := AddCommGroup.zmodModule hr0
  haveI : Module.Finite (ZMod r) (Additive W) := Module.Finite.of_finite
  haveI : Nontrivial (Additive W) := inferInstance
  let f : A → (Additive W →+ Additive W) := fun a =>
    { toFun := fun x => Additive.ofMul (a • x.toMul)
      map_zero' := by apply Additive.ext; simp
      map_add' := fun x y => by
        apply Additive.ext
        simp [toMul_add, smul_mul', ofMul_mul] }
  let ρ : Representation (ZMod r) A (Additive W) :=
    { toFun := fun a => (f a).toZModLinearMap r
      map_one' := by
        apply LinearMap.ext
        intro x
        apply Additive.ext
        simp [f]
      map_mul' := by
        intro a b
        apply LinearMap.ext
        intro x
        apply Additive.ext
        simp [f, mul_smul] }
  have hff : ∀ a : A, a ≠ 1 → ∀ w : Additive W, ρ a w = w → w = 0 := fun a ha w hw => by
    have h1 : f a w = w := hw
    have h2 : a • w.toMul = w.toMul := by
      have := congrArg Additive.toMul h1
      simpa [f] using this
    have h3 := hfp a ha w.toMul h2
    apply Additive.ext
    simp [h3]
  exact abelian_fpf_representation_isCyclic ρ inferInstance hff

end Work.Frobenius.Complement

namespace Work.Frobenius.Complement

/-! ## Part 3: an abelian group acting fixed-point-freely on a group with an invariant
nontrivial elementary abelian subgroup is cyclic -/

private theorem isCyclic_of_abelian_fpf_action {A N : Type*} [Group A] [Finite A] [IsMulCommutative A]
    [Group N] [Finite N] [Nontrivial N] [MulDistribMulAction A N]
    (hfpf : ∀ a : A, a ≠ 1 → ∀ n : N, a • n = n → n = 1) {r : ℕ} (hr : r.Prime)
    (W : Subgroup N) (hWne : W ≠ ⊥) (hWinv : ∀ a : A, ∀ x : N, x ∈ W ↔ a • x ∈ W)
    (hWcomm : IsMulCommutative ↥W) (hWexp : ∀ w : ↥W, w ^ r = 1) : IsCyclic A := by
  haveI : Nontrivial ↥W := (Subgroup.nontrivial_iff_ne_bot W).mpr hWne
  haveI : FT.IsInvariant A W := ⟨fun a => Subgroup.ext fun x => by
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    exact (hWinv a⁻¹ x).symm⟩
  exact isCyclic_of_fpf_action_on_elementaryAbelian hr hWexp (fun a ha w hw => by
    have h2 : a • (w : N) = (w : N) := by
      have h3 := congrArg Subtype.val hw
      rwa [FT.coe_subgroup_smul] at h3
    exact Subtype.ext (hfpf a ha (w : N) h2))

private theorem exists_invariant_exponent_prime_le_of_invariant_sylow
    {A N : Type*} [Group A] [Group N] [Finite A] [Finite N] [MulDistribMulAction A N]
    {r : ℕ} (hr : r.Prime) (P : Sylow r N)
    (hPinv : ∀ a : A, ∀ x : N, x ∈ (P : Subgroup N) ↔ a • x ∈ (P : Subgroup N))
    (hPne : (P : Subgroup N) ≠ ⊥) :
    ∃ W : Subgroup N, W ≠ ⊥ ∧
      (∀ a : A, ∀ x : N, x ∈ W ↔ a • x ∈ W) ∧ IsMulCommutative ↥W ∧ ∀ w : ↥W, w ^ r = 1 := by
  haveI : Fact r.Prime := ⟨hr⟩
  -- the generating set: the `r`-torsion central elements of `P`
  set S : Set N := {x : N | x ∈ (P : Subgroup N) ∧ x ^ r = 1 ∧ ∀ y ∈ (P : Subgroup N), y * x = x * y}
    with hSdef
  have memS : ∀ x : N, x ∈ S ↔
      (x ∈ (P : Subgroup N) ∧ x ^ r = 1 ∧ ∀ y ∈ (P : Subgroup N), y * x = x * y) := by
    intro x; rw [hSdef]; rfl
  have hSsmul : ∀ (a : A) (y : N), y ∈ S ↔ a • y ∈ S := by
    intro a y
    have key2 : ((a • y) ^ r = 1) ↔ (y ^ r = 1) := by
      have h : (a • y) ^ r = a • (y ^ r) := by rw [← smul_pow']
      rw [h]
      constructor
      · intro hh
        have h1 := congrArg (fun t => a⁻¹ • t) hh
        simpa using h1
      · intro hh; rw [hh, smul_one]
    have key3 : (∀ z ∈ (P : Subgroup N), z * (a • y) = (a • y) * z) ↔
        (∀ z ∈ (P : Subgroup N), z * y = y * z) := by
      constructor
      · intro h z hz
        have hz' : a • z ∈ (P : Subgroup N) := (hPinv a z).mp hz
        have h1 := h (a • z) hz'
        have h2 := congrArg (fun t => a⁻¹ • t) h1
        simpa [smul_mul', inv_smul_smul] using h2
      · intro h z hz
        have hz' : a⁻¹ • z ∈ (P : Subgroup N) := (hPinv a⁻¹ z).mp hz
        have h1 := h (a⁻¹ • z) hz'
        have h2 := congrArg (fun t => a • t) h1
        simpa [smul_mul', inv_smul_smul] using h2
    rw [memS y, memS (a • y)]
    constructor
    · rintro ⟨hyP, hyr, hyc⟩
      exact ⟨(hPinv a y).mp hyP, key2.mpr hyr, key3.mpr hyc⟩
    · rintro ⟨hyP, hyr, hyc⟩
      exact ⟨(hPinv a y).mpr hyP, key2.mp hyr, key3.mp hyc⟩
  have hSinv : ∀ a : A, a • S = S := by
    intro a
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    exact (hSsmul a⁻¹ y).symm
  have hWinv : FT.IsInvariant A (Subgroup.closure S) := FT.IsInvariant.closure hSinv
  have hWmem : ∀ a : A, ∀ x : N, x ∈ Subgroup.closure S ↔ a • x ∈ Subgroup.closure S :=
    fun a x => (hWinv.mem_smul_iff a x).symm
  have hWle : Subgroup.closure S ≤ (P : Subgroup N) :=
    (Subgroup.closure_le _).mpr (fun x hx => (memS x).mp hx |>.1)
  have hcl : Subgroup.closure S ≤ Subgroup.centralizer ((Subgroup.closure S : Subgroup N) : Set N) := by
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    show x ∈ Subgroup.centralizer ((Subgroup.closure S : Subgroup N) : Set N)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (memS x).mp hx |>.2.2 y (hWle hy)
  have hcomm : IsMulCommutative ↥(Subgroup.closure S) := by
    refine isMulCommutative_iff.mpr fun x y => Subtype.ext ?_
    have hx := hcl x.2
    rw [Subgroup.mem_centralizer_iff] at hx
    exact (hx y y.2).symm
  have hexp : ∀ w : ↥(Subgroup.closure S), w ^ r = 1 := by
    have key : ∀ x ∈ (Subgroup.closure S : Subgroup N), x ^ r = 1 := by
      intro x hx
      induction hx using Subgroup.closure_induction with
      | mem y hy => exact (memS y).mp hy |>.2.1
      | one => rw [one_pow]
      | mul y z hy hz ihy ihz =>
          have hxy : Commute y z := by
            have h := isMulCommutative_iff.mp hcomm (⟨y, hy⟩ : ↥(Subgroup.closure S))
              (⟨z, hz⟩ : ↥(Subgroup.closure S))
            exact Subtype.ext_iff.mp h
          rw [hxy.mul_pow, ihy, ihz, one_mul]
      | inv y hy ihy => rw [inv_pow, ihy, inv_one]
    intro w
    exact Subtype.ext (by simpa [map_pow] using key (w : N) w.2)
  -- nontriviality: `P` is a nontrivial `r`-group, so `Ω₁(Z(P)) ≠ 1`
  haveI : Nontrivial ↥(P : Subgroup N) := (Subgroup.nontrivial_iff_ne_bot _).mpr hPne
  have hcne : Subgroup.center ↥(P : Subgroup N) ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot _).mp P.isPGroup'.center_nontrivial
  have hcent : Work.PGroup.omega1 ↥(P : Subgroup N) r (Subgroup.center ↥(P : Subgroup N)) ≠ ⊥ := by
    have h := Work.PGroup.inf_omega1_center_ne_bot (M := ↥(P : Subgroup N)) hr P.isPGroup'
      (N := Subgroup.center ↥(P : Subgroup N)) (inferInstance) hcne
    rwa [inf_eq_right.mpr (Work.PGroup.omega1_le r _)] at h
  have hlt : (⊥ : Subgroup ↥(P : Subgroup N)) <
      Work.PGroup.omega1 ↥(P : Subgroup N) r (Subgroup.center ↥(P : Subgroup N)) :=
    bot_lt_iff_ne_bot.mpr hcent
  obtain ⟨y, hyme, hyne'⟩ := SetLike.exists_of_lt hlt
  have hy1 : y ≠ 1 := fun h => hyne' (by rw [Subgroup.mem_bot]; exact h)
  have hzp := Work.PGroup.omega1_mem_and_pow
    (A := Subgroup.center ↥(P : Subgroup N))
    (inferInstance : IsMulCommutative ↥(Subgroup.center ↥(P:Subgroup N))) hyme
  have hsS : (y : N) ∈ S := by
    rw [memS]
    refine ⟨y.2, ?_, ?_⟩
    · have h := congrArg (fun t : ↥(P : Subgroup N) => (t : N)) hzp.2
      simpa using h
    · intro z hz
      have h := (Subgroup.mem_center_iff.mp hzp.1) (⟨z, hz⟩ : ↥(P : Subgroup N))
      exact congrArg Subtype.val h
  have hsne : (y : N) ≠ 1 := fun h => hy1 (Subtype.ext h)
  refine ⟨Subgroup.closure S, ?_, hWmem, hcomm, hexp⟩
  intro hbot
  have : (y : N) ∈ (⊥ : Subgroup N) := by
    rw [← hbot]; exact Subgroup.subset_closure hsS
  exact hsne (Subgroup.mem_bot.mp this)

/-- A finite solvable group acting coprimely on a nontrivial finite group fixes a nontrivial
elementary abelian subgroup (of exponent some prime). -/
private theorem exists_invariant_exponent_prime_of_solvable_action {A N : Type*} [Group A] [Group N]
    [Finite A] [Finite N] [Nontrivial N] [MulDistribMulAction A N] (hsol : Group.IsSolvable A)
    (hcop : (Nat.card A).Coprime (Nat.card N)) :
    ∃ (r : ℕ) (_ : r.Prime) (W : Subgroup N), W ≠ ⊥ ∧
      (∀ a : A, ∀ x : N, x ∈ W ↔ a • x ∈ W) ∧ IsMulCommutative ↥W ∧ ∀ w : ↥W, w ^ r = 1 := by
  have hcard_ne : Nat.card N ≠ 1 := by
    have h : 1 < Nat.card N := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    omega
  obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd hcard_ne
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨P, hPinv⟩ := exists_invariant_sylow_of_isSolvable hsol hcop hr
  have hPne : (P : Subgroup N) ≠ ⊥ := Sylow.ne_bot_of_dvd_card P hrdvd
  exact ⟨r, hr, exists_invariant_exponent_prime_le_of_invariant_sylow hr P hPinv hPne⟩

/-! ## Part 4: a finite group of order `p * q` acting fixed-point-freely on a nontrivial finite
group is cyclic -/

theorem isCyclic_of_card_eq_mul_primes_of_fpf {A N : Type*} [Group A] [Group N] [Finite A] [Finite N]
    [Nontrivial N] [MulDistribMulAction A N] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hcop : (Nat.card A).Coprime (Nat.card N)) (hcard : Nat.card A = p * q)
    (hfpf : ∀ a : A, a ≠ 1 → ∀ n : N, a • n = n → n = 1) : IsCyclic A := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  have hsolA : Group.IsSolvable A := isSolvable_of_card_eq_mul_primes hp hq hcard
  by_cases hcomm : IsMulCommutative A
  · by_cases hpq : p = q
    · have hcard' : Nat.card A = p ^ 2 := by rw [hcard, hpq, sq]
      obtain ⟨r, hr, W, hWne, hWinv, hWcomm, hWexp⟩ :=
        exists_invariant_exponent_prime_of_solvable_action hsolA hcop
      exact isCyclic_of_abelian_fpf_action hfpf hr W hWne hWinv hWcomm hWexp
    · exact isCyclic_of_commutative_card_eq_mul_primes hp hq hpq hcard
  · -- A is not commutative: contradiction
    have hpqne : p ≠ q := by
      rintro rfl
      exact hcomm (IsPGroup.isMulCommutative_of_card_eq_prime_sq (G := A) (p := p) (by rw [hcard, sq]))
    obtain ⟨r, hr, W, hWne, hWinv, hWcomm, hWexp⟩ :=
      exists_invariant_exponent_prime_of_solvable_action hsolA hcop
    haveI : Fact r.Prime := ⟨hr⟩
    -- r divides |N| hence r is coprime to p and q
    obtain ⟨w, hwmem, hwne⟩ : ∃ w ∈ W, w ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hWne (Subgroup.eq_bot_iff_forall W |>.mpr hcon)
    have hwr : w ^ r = 1 := by
      have := congrArg (fun t : ↥W => (t : N)) (hWexp ⟨w, hwmem⟩)
      simpa using this
    have hrW : r ∣ Nat.card ↥W := by
      have h1 : orderOf (⟨w, hwmem⟩ : ↥W) = r :=
        orderOf_eq_prime (Subtype.ext hwr) (fun h => hwne (Subtype.ext_iff.mp h))
      have h2 : orderOf (⟨w, hwmem⟩ : ↥W) ∣ Nat.card ↥W := orderOf_dvd_natCard _
      rwa [h1] at h2
    have hrN : r ∣ Nat.card N := by
      have h1 : r ∣ Nat.card ↥(⊤ : Subgroup N) := hrW.trans (Subgroup.card_dvd_of_le (le_top))
      simpa using h1
    have hpA : p ∣ Nat.card A := hcard ▸ dvd_mul_right p q
    have hqA : q ∣ Nat.card A := hcard ▸ dvd_mul_left q p
    have hrp : ¬ r ∣ p := by
      intro hdiv
      have h1 : r ∣ Nat.card A := dvd_trans hdiv hpA
      have h3 : r = 1 := Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd h1 hrN)
      exact hr.ne_one h3
    have hrq : ¬ r ∣ q := by
      intro hdiv
      have h1 : r ∣ Nat.card A := dvd_trans hdiv hqA
      have h3 : r = 1 := Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd h1 hrN)
      exact hr.ne_one h3
    have hpr : (p : ZMod r) ≠ 0 := by
      simpa [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero] using hrp
    have hqr : (q : ZMod r) ≠ 0 := by
      simpa [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero] using hrq
    rcases lt_or_gt_of_ne hpqne with hlt | hlt
    · obtain ⟨y, x, s, hy, hx, hs, hrel⟩ :=
        exists_conj_action_of_nonabelian_card_eq_mul_primes hp hq hlt hcard hcomm
      exact (false_of_fpf_action_elementaryAbelian hr hp hq hpqne hpr hqr W hWne hWinv hWcomm
        hWexp hfpf hy hx hs hrel).elim
    · obtain ⟨y, x, s, hy, hx, hs, hrel⟩ :=
        exists_conj_action_of_nonabelian_card_eq_mul_primes hq hp hlt
          (by rw [mul_comm]; exact hcard) hcomm
      exact (false_of_fpf_action_elementaryAbelian hr hq hp (Ne.symm hpqne) hqr hpr W hWne hWinv
        hWcomm hWexp hfpf hy hx hs hrel).elim

end Work.Frobenius.Complement

namespace Work.Frobenius.Complement

/-! ## Part 5: the target statement -/

theorem isCyclic_of_card_eq_mul_primes {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    (hH : IsFrobeniusComplement H) {K : Subgroup G} (hK : K ≤ H) {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hcard : Nat.card K = p * q) : IsCyclic K := by
  obtain ⟨N, hNcarrier, hNnorm, -⟩ := frobenius_theorem hH
  haveI : N.Normal := hNnorm
  have hNne : N ≠ ⊥ := kernel_ne_bot hH hNcarrier
  haveI : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr hNne
  have hfpfH : IsFixedPointFreeOn N H :=
    (frobenius_fpf_iff hNnorm (frobenius_inf_eq_bot hH hNcarrier)
      (frobenius_sup_eq_top hH hNcarrier) hH.ne_bot hNne).mp hH
  have hcopNH : (Nat.card ↥N).Coprime (Nat.card ↥H) := frobenius_coprime hH hNcarrier
  -- the conjugation action of `K` on `N`
  let act : MulDistribMulAction ↥K ↥N :=
    { smul := fun k n => MulAut.conjNormal (k : G) n
      one_smul := fun n => by
        show MulAut.conjNormal (((1 : ↥K) : G)) n = n
        simp
      mul_smul := fun a b n => by
        show MulAut.conjNormal ((a * b : ↥K) : G) n
          = MulAut.conjNormal (a : G) (MulAut.conjNormal (b : G) n)
        rw [show ((a * b : ↥K) : G) = (a : G) * (b : G) from rfl, map_mul]
        rfl
      smul_one := fun k => by
        show MulAut.conjNormal (k : G) 1 = 1
        simp
      smul_mul := fun k m n => by
        show MulAut.conjNormal (k : G) (m * n)
          = MulAut.conjNormal (k : G) m * MulAut.conjNormal (k : G) n
        simp }
  letI := act
  have hfpf : ∀ k : ↥K, k ≠ 1 → ∀ n : ↥N, k • n = n → n = 1 := by
    intro k hk n hn
    have h1 : (k : G) * (n : N) * (k : G)⁻¹ = (n : N) := by
      have h2 := congrArg Subtype.val hn
      rw [show (k • n : ↥N) = MulAut.conjNormal (k : G) n from rfl] at h2
      rwa [MulAut.conjNormal_apply] at h2
    have hk' : (k : G) ≠ 1 := fun h => hk (Subtype.ext h)
    exact Subtype.ext (hfpfH (hK k.2) hk' n.2 h1)
  have hcop : (Nat.card ↥K).Coprime (Nat.card ↥N) := by
    have h1 : Nat.card ↥K ∣ Nat.card ↥H := Subgroup.card_dvd_of_le hK
    exact (hcopNH.coprime_dvd_right h1).symm
  exact isCyclic_of_card_eq_mul_primes_of_fpf hp hq hcop hcard hfpf

end Work.Frobenius.Complement
