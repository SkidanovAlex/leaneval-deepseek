/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PSTAB area (fundmath3-gorenstein_walter)
-/
import Mathlib
import Submission.Work.PSTAB.QuadPairAux
import Submission.Work.PSTAB.NilpotentOrder

set_option autoImplicit false

/-!
# `Work.PSTAB.NSubLePcore` — `NSub ρ` is a normal `p`-subgroup

`Work.PSTAB.NSub ρ` is the subgroup of `L` consisting of the elements acting trivially on every
factor of the chief series `Work.PSTAB.invSer ρ` of the `𝔽_p[L]`-module `V`.

If `ρ` is faithful, every element of `NSub ρ` has `p`-power order (an element acting trivially on
all factors is unipotent — `Work.PSTAB.NSub.pow_sub_one_eq_zero` — and a unipotent element whose
order is prime to `p` is trivial — `Work.PSTAB.NilpotentOrder`).  Hence `NSub ρ` is a normal
`p`-subgroup of `L`, and therefore lies in `O_p(L) = Work.GW2.pCore p L`.
-/

namespace Work.PSTAB

variable {L : Type*} [Group L] [Finite L] {p : ℕ} [Fact p.Prime] {V : Type*}
  [AddCommGroup V] [Module (ZMod p) V] [Finite V]

/-- `NSub ρ` is normal in `L`. -/
instance NSub_normal (ρ : Representation (ZMod p) L V) : (NSub ρ).Normal where
  conj_mem := by
    intro n hn g i v hv
    have hw : ρ g⁻¹ v ∈ invSer ρ i := repInv_invSer ρ i g⁻¹ v hv
    have h1 : ρ n (ρ g⁻¹ v) - ρ g⁻¹ v ∈ invSer ρ (i + 1) := hn i _ hw
    have h2 : ρ g (ρ n (ρ g⁻¹ v) - ρ g⁻¹ v) ∈ invSer ρ (i + 1) :=
      repInv_invSer ρ (i + 1) g _ h1
    have hfix : ρ g (ρ g⁻¹ v) = v := by
      have h : ρ g * ρ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
      rw [← Module.End.mul_apply, h, Module.End.one_apply]
    have hA : ρ (g * n * g⁻¹) v = ρ g (ρ n (ρ g⁻¹ v)) := by
      simp only [map_mul, Module.End.mul_apply]
    have heq : ρ (g * n * g⁻¹) v - v = ρ g (ρ n (ρ g⁻¹ v) - ρ g⁻¹ v) := by
      rw [hA, map_sub, hfix]
    rwa [heq]

/-- Every element of `NSub ρ` has `p`-power order, when `ρ` is faithful. -/
theorem NSub_isPGroup (ρ : Representation (ZMod p) L V) (hρ : Function.Injective ρ) :
    IsPGroup p ↥(NSub ρ) := by
  rw [isPGroup_iff_primeFactors_card_subset (Fact.out : Nat.Prime p).ne_zero]
  intro q hq
  rw [Nat.Prime.primeFactors (Fact.out : Nat.Prime p), Finset.mem_singleton]
  by_contra hqp
  have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hdvd : q ∣ Nat.card ↥(NSub ρ) := Nat.dvd_of_mem_primeFactors hq
  haveI : Fact q.Prime := ⟨hqprime⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' q hdvd
  -- `ρ g` is unipotent with order `q`, and `q` is invertible in characteristic `p`
  have hqZ : ((q : ℕ) : ZMod p) ≠ 0 := by
    intro h0
    have hpq : p ∣ q := (ZMod.natCast_eq_zero_iff q p).mp h0
    exact hqp ((Nat.prime_dvd_prime_iff_eq (Fact.out : Nat.Prime p) hqprime).mp hpq).symm
  have hqunit : IsUnit ((q : ℕ) : Module.End (ZMod p) V) := by
    have h1 : ((q : ℕ) : Module.End (ZMod p) V)
        = algebraMap (ZMod p) (Module.End (ZMod p) V) ((q : ℕ) : ZMod p) :=
      (map_natCast (algebraMap (ZMod p) (Module.End (ZMod p) V)) q).symm
    rw [h1]
    exact IsUnit.map _ (isUnit_iff_ne_zero.mpr hqZ)
  have hgq : g ^ q = 1 := by
    rw [← hg]
    exact pow_orderOf_eq_one g
  have hgqL : (g : L) ^ q = 1 := by
    have h := congrArg (fun z : ↥(NSub ρ) => (z : L)) hgq
    simpa using h
  have hnil : IsNilpotent ((ρ (g : L) : Module.End (ZMod p) V) - 1) :=
    NSub.pow_sub_one_eq_zero ρ g.2
  have hpow : (1 + ((ρ (g : L) : Module.End (ZMod p) V) - 1)) ^ q = 1 := by
    have h1 : 1 + ((ρ (g : L) : Module.End (ZMod p) V) - 1) = ρ (g : L) := by abel
    rw [h1, ← map_pow, hgqL, map_one]
  have hsub : (ρ (g : L) : Module.End (ZMod p) V) - 1 = 0 := NilpotentOrder hnil hqunit hpow
  have hρg : ρ (g : L) = 1 := sub_eq_zero.mp hsub
  have hgL : (g : L) = 1 := hρ (by rw [hρg, map_one])
  have hg1 : g = 1 := Subtype.ext hgL
  rw [hg1, orderOf_one] at hg
  exact hqprime.ne_one hg.symm

/-- **`NSub ρ` is contained in `O_p(L)`**: it is a normal `p`-subgroup. -/
theorem NSubLePcore (ρ : Representation (ZMod p) L V) (hρ : Function.Injective ρ) :
    NSub ρ ≤ Work.GW2.pCore p L := by
  haveI := NSub_normal ρ
  rw [Work.GW2.pCore]
  exact Subgroup.normal_le_normalCore.mpr (le_sSup ⟨NSub_normal ρ, NSub_isPGroup ρ hρ⟩)

end Work.PSTAB
