import Mathlib
import Submission.Vdw.FourierPrime
import Submission.Vdw.MultiPrimeExpansion

open Finset
open scoped BigOperators

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# The multi-prime §4 Fourier expansion (start of the `Dequi2` chapter)

This module begins the replacement of the paper's multi-prime Corollary
`Dequi2` (formalized as `FourierDequi.DequiBound`) by the *single-prime*
Proposition `ftgen2` (`FourierPrime.MIndexBound`).  It contains

* `indicator_indexClass_eq` — the per-prime Fourier inversion for the
  index-`≥k` residue set, in the form whose Fourier coefficient is the
  unnormalized sum `indexFourierCoeff`;
* `multiPrime_fourier_expansion` — the exact multi-prime expansion of the joint
  count: the number of box polynomials satisfying the index conditions modulo
  all the primes `q i` equals `(∏ i, q i ^ n)^{-1}` times the sum over
  frequency tuples of the product of the per-prime Fourier coefficients with
  the joint box character sum.

The companion modules `BoxFourierIndex`/`MultiPrimeWeight` bound the joint box
character sum (`norm_sum_joint_box_char_le`), and `FourierPrime.MIndexBound` is
the input on the per-prime coefficients.

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw
noncomputable section

/-- Membership in `indexClassFinset` is the `indexClass` condition. -/
lemma mem_indexClassFinset {p : ℕ} [Fact (Nat.Prime p)] {n k : ℕ} {x : Fin n → ZMod p} :
    x ∈ indexClassFinset p n k ↔ indexClass (F := ZMod p) n k x := by
  classical
  rw [indexClassFinset, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- Per-prime expansion of the indicator of the index-`≥k` residue set, in the
form whose coefficient is the (unnormalized) Fourier sum. -/
theorem indicator_indexClass_eq (p : ℕ) [Fact (Nat.Prime p)] (n k : ℕ)
    (x : Fin n → ZMod p) :
    (if x ∈ indexClassFinset p n k then (1 : ℂ) else 0)
      = (((p : ℂ) ^ n))⁻¹ * ∑ a : Fin n → ZMod p,
          (∑ y ∈ indexClassFinset p n k, ZMod.stdAddChar (∑ i, a i * y i)) *
            ZMod.stdAddChar (-(∑ i, a i * x i)) := by
  classical
  have hp : ((p : ℂ) ^ n) ≠ 0 := by
    have h : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
    exact pow_ne_zero _ h
  have h1 : (if x ∈ indexClassFinset p n k then (1 : ℂ) else 0)
      = ∑ y ∈ indexClassFinset p n k, (if y = x then (1 : ℂ) else 0) := by
    rw [Finset.sum_ite_eq' (indexClassFinset p n k) x (fun _ => (1 : ℂ))]
  rw [h1]
  have h2 : ∀ y ∈ indexClassFinset p n k, (if y = x then (1 : ℂ) else 0)
      = ((p : ℂ) ^ n)⁻¹ * ∑ a : Fin n → ZMod p,
          ZMod.stdAddChar (∑ i, a i * y i) * ZMod.stdAddChar (-(∑ i, a i * x i)) := by
    intro y _
    rw [indicator_eq_inv_mul_sum p n y x]
    congr 1
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [stdAddChar_sub_eq_mul p n a y x]
  rw [Finset.sum_congr rfl h2, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_mul]

/-- **The multi-prime Fourier expansion** of the joint index-condition count. -/
theorem multiPrime_fourier_expansion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℕ) [hqFact : ∀ i, Fact (Nat.Prime (q i))]
    [hqNe : ∀ i, NeZero (q i)]
    (n H : ℕ) (k : ι → ℕ) :
    ((Nat.card {f : ↥(Box n H) // ∀ i,
        indexClass (F := ZMod (q i)) n (k i) (boxResidue n H (q i) f)} : ℕ) : ℂ)
      = ((∏ i, ((q i : ℕ) : ℂ) ^ n))⁻¹ *
        ∑ a : (∀ i, Fin n → ZMod (q i)),
          (∏ i, ∑ y ∈ indexClassFinset (q i) n (k i),
              ZMod.stdAddChar (∑ j, a i j * y j)) *
          (∑ f : ↥(Box n H), ∏ i,
              ZMod.stdAddChar (-(∑ j, a i j * (boxResidue n H (q i) f) j))) := by
  classical
  set cf : (i : ι) → (Fin n → ZMod (q i)) → ℂ :=
    fun i b => ∑ y ∈ indexClassFinset (q i) n (k i), ZMod.stdAddChar (∑ j, b j * y j) with hcf
  set bx : (i : ι) → ↥(Box n H) → (Fin n → ZMod (q i)) → ℂ :=
    fun i f b => ZMod.stdAddChar (-(∑ j, b j * (boxResidue n H (q i) f) j)) with hbx
  have hcard : ((Nat.card {f : ↥(Box n H) // ∀ i,
        indexClass (F := ZMod (q i)) n (k i) (boxResidue n H (q i) f)} : ℕ) : ℂ)
      = ∑ f : ↥(Box n H), (if ∀ i,
          indexClass (F := ZMod (q i)) n (k i) (boxResidue n H (q i) f) then (1 : ℂ) else 0) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
    push_cast
    exact Finset.sum_congr rfl (fun f _ => by split_ifs <;> simp)
  have hkey : ∀ f : ↥(Box n H),
      (if ∀ i, indexClass (F := ZMod (q i)) n (k i) (boxResidue n H (q i) f)
          then (1 : ℂ) else 0)
      = (∏ i, ((q i : ℂ) ^ n))⁻¹ *
        ∑ a : (∀ i, Fin n → ZMod (q i)), ∏ i, cf i (a i) * bx i f (a i) := by
    intro f
    have hsingle : ∀ i : ι,
        (if indexClass (F := ZMod (q i)) n (k i) (boxResidue n H (q i) f)
            then (1 : ℂ) else 0)
        = ((q i : ℂ) ^ n)⁻¹ * ∑ a : Fin n → ZMod (q i), cf i a * bx i f a := by
      intro i
      have h := indicator_indexClass_eq (q i) n (k i) (boxResidue n H (q i) f)
      simpa only [mem_indexClassFinset, hcf, hbx] using h
    rw [show (if ∀ i, indexClass (F := ZMod (q i)) n (k i) (boxResidue n H (q i) f)
        then (1 : ℂ) else 0)
        = ∏ i, (if indexClass (F := ZMod (q i)) n (k i) (boxResidue n H (q i) f)
            then (1 : ℂ) else 0) from (Fintype.prod_boole).symm]
    rw [Finset.prod_congr rfl (fun i _ => hsingle i),
      Finset.prod_mul_distrib, Finset.prod_inv_distrib, Finset.prod_univ_sum,
      Fintype.piFinset_univ]
  rw [hcard]
  simp only [hkey]
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have h1 : ∀ f : ↥(Box n H), ∏ i, cf i (a i) * bx i f (a i)
      = (∏ i, cf i (a i)) * (∏ i, bx i f (a i)) := fun f => Finset.prod_mul_distrib
  rw [Finset.sum_congr rfl (fun f _ => h1 f)]
  exact (Finset.mul_sum Finset.univ (fun f : ↥(Box n H) => ∏ i, bx i f (a i))
    (∏ i, cf i (a i))).symm

end
end Submission.Vdw
