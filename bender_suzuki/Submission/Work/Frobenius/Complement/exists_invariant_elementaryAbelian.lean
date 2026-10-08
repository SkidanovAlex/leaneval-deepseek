import Mathlib
import Submission.Work.Coprime.Basic
import Submission.Work.PGroup.Omega1
import Submission.Work.Frobenius.Complement.exists_invariant_sylow_of_isPGroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

open scoped Pointwise
open Subgroup
open scoped IsMulCommutative

namespace Work.Frobenius.Complement

/-- Given an `A`-invariant Sylow `r`-subgroup `P` of `N`, there is an `A`-invariant
subgroup `W ≤ N` which is nontrivial, commutative, and of exponent `r`. -/
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

theorem exists_invariant_elementaryAbelian {A N : Type*} [Group A] [Finite A]
    [Group N] [Finite N] [Nontrivial N] [MulDistribMulAction A N]
    {p : ℕ} (hp : p.Prime) (hAp : IsPGroup p A) (hpN : ¬ p ∣ Nat.card N) :
    ∃ (q : ℕ) (_ : q.Prime) (H : Subgroup N), H ≠ ⊥ ∧ (∀ a : A, ∀ x : N, a • x ∈ H ↔ x ∈ H) ∧
      IsMulCommutative H ∧ (∀ h : H, h ^ q = 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- `A` is a `p`-group and `p ∤ |N|`, so `(|A|, |N|) = 1`.
  have hcop : (Nat.card A).Coprime (Nat.card N) := by
    obtain ⟨n, hn⟩ := hAp.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_left n (hp.coprime_iff_not_dvd.mpr hpN)
  -- pick a prime `r` dividing `|N|`
  have hNne : Nat.card N ≠ 1 := by
    have h : 1 < Nat.card N := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    omega
  obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd hNne
  haveI : Fact r.Prime := ⟨hr⟩
  -- an `A`-invariant Sylow `r`-subgroup of `N`
  obtain ⟨P, hPinv⟩ := exists_invariant_sylow_of_isPGroup hp hAp hcop hr
  have hPne : (P : Subgroup N) ≠ ⊥ := Sylow.ne_bot_of_dvd_card P hrdvd
  obtain ⟨W, hWne, hWmem, hWcomm, hWexp⟩ :=
    exists_invariant_exponent_prime_le_of_invariant_sylow hr P hPinv hPne
  exact ⟨r, hr, W, hWne, fun a x => (hWmem a x).symm, hWcomm, hWexp⟩

end Work.Frobenius.Complement
