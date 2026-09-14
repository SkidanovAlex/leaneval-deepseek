import Mathlib
import Submission.Vdw.Counting
import Submission.Vdw.ResidueFiber
import Submission.Vdw.ResidueIndex

open Polynomial
open scoped BigOperators

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Multi-prime (CRT) Case-I bound: the elementary `C ≤ H` regime

The per-prime atom (`ResidueIndex.box_index_ge_ncard_le`) controls one prime.
This module controls *all* primes `q i` (`i : ι`, a finite type) at once —
Bhargava's congruence-density bound for Case I in the elementary regime
`C ≤ H`, with `C = ∏ i, q i`:

    #{f ∈ Box n H : ∀ i, index of (f mod q i) ≥ e i}
        ≤ (∏ i, 2^((n+1)^4) · (q i)^(n − e i)) · ((2H+1)/C + 1)^n

`main_multiPrime_box_le` below.  The content is:

* the only "CRT" fact needed is divisibility: if the pairwise coprime moduli
  `q i` each divide `a`, then their product divides `a`
  (`pairwise_coprime_prod_dvd_nat`, and the `ℤ`-valued variant
  `pairwise_coprime_prod_dvd_int`);
* hence the per-coordinate fibre bound `coordinate_fiber_ncard_le`: among the
  bounded integers `BddInt H`, fixing the residue modulo each `q i` leaves at
  most `(2H+1)/C + 1` integers;
* per-coordinate fibres multiply (`coeffVec` is injective on `Box`), and the
  index-class vector sets multiply by the Chinese-remainder bijection between
  `(i → Fin n → ZMod (q i))` and the global residue vectors — here realised
  simply as: a box polynomial with each per-prime index condition determines,
  for each `i`, an index-class vector; fixing all of them fixes the residue
  class of each coefficient modulo every `q i`, and these class tuples are
  counted by `∏_i |indexClassSet|`.

This is the counting engine behind Case I for `C ≤ H`; the Fourier extension
to `C ≤ H^(1+δ)` and the summation over squarefull `D` come later.
-/

namespace Submission.Vdw

noncomputable section

open UniqueFactorizationMonoid

/-! ## Chinese-remainder divisibility (the only CRT content needed) -/

section Divisibility

/-- If the elements of a finite set are pairwise coprime and each divides
`n`, then their product divides `n`. -/
theorem pairwise_coprime_prod_dvd_nat {ι : Type*} (q : ι → ℕ) (s : Finset ι) (n : ℕ)
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Nat.Coprime (q i) (q j))
    (hdvd : ∀ i ∈ s, q i ∣ n) :
    (∏ i ∈ s, q i) ∣ n := by
  classical
  refine (Finset.induction_on (motive := fun s' : Finset ι =>
      (∀ i ∈ s', ∀ j ∈ s', i ≠ j → Nat.Coprime (q i) (q j)) →
      (∀ i ∈ s', q i ∣ n) → (∏ i ∈ s', q i) ∣ n) s ?_ ?_) hcop hdvd
  · intro hcop hdvd
    simp
  · intro a t ha ih hcop' hdvd'
    rw [Finset.prod_insert ha]
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd
      (by
        apply Nat.Coprime.prod_right
        intro i hi
        exact hcop' a (by simp) i (by exact Finset.mem_insert.mpr (Or.inr hi)) (by
          intro heq
          exact ha (by simpa [heq] using hi)))
      (hdvd' a (by simp))
      (ih (fun i hi j hj => hcop' i (by exact Finset.mem_insert.mpr (Or.inr hi)) j (by exact Finset.mem_insert.mpr (Or.inr hj)))
          (fun i hi => hdvd' i (by exact Finset.mem_insert.mpr (Or.inr hi))))

/-- Fintype version of `pairwise_coprime_prod_dvd_nat`. -/
theorem pairwise_coprime_univ_prod_dvd_nat {ι : Type*} [Fintype ι] (q : ι → ℕ) (n : ℕ)
    (hcop : ∀ i j : ι, i ≠ j → Nat.Coprime (q i) (q j))
    (hdvd : ∀ i : ι, q i ∣ n) :
    (∏ i : ι, q i) ∣ n := by
  classical
  simpa using (pairwise_coprime_prod_dvd_nat q Finset.univ n
    (fun i _ j _ hij => hcop i j hij) (fun i _ => hdvd i))

/-- Same for integer divisibility: pairwise coprime naturals dividing an
integer force their product to divide it. -/
theorem pairwise_coprime_prod_dvd_int {ι : Type*} [Fintype ι] (q : ι → ℕ) (a : ℤ)
    (hcop : ∀ i j : ι, i ≠ j → Nat.Coprime (q i) (q j))
    (hdvd : ∀ i : ι, (q i : ℤ) ∣ a) :
    ((∏ i : ι, q i : ℕ) : ℤ) ∣ a := by
  classical
  -- it suffices that the product divides the absolute value
  have hdvdAbs : ∀ i : ι, q i ∣ a.natAbs := by
    intro i
    have h' : (q i : ℤ) ∣ (a.natAbs : ℤ) := (Int.dvd_natAbs (a := (q i : ℤ)) (b := a)).mpr (hdvd i)
    exact (Int.natCast_dvd_natCast (m := q i) (n := a.natAbs)).mp h'
  have hprod : (∏ i : ι, q i) ∣ a.natAbs :=
    pairwise_coprime_univ_prod_dvd_nat q a.natAbs hcop hdvdAbs
  exact (Int.dvd_natAbs (a := ((∏ i : ι, q i : ℕ) : ℤ)) (b := a)).mp
    (Int.natCast_dvd_natCast.mpr hprod)

end Divisibility


/-! ## The per-coordinate fibre bound -/

section CoordinateFiber

variable {ι : Type*} [Fintype ι]

/-- Among the bounded integers `BddInt H`, fixing the residue class modulo
each of the pairwise coprime moduli `q i` leaves at most
`(2H+1)/(∏ q i) + 1` integers. -/
theorem coordinate_fiber_ncard_le (q : ι → ℕ)
    (hcop : ∀ i j : ι, i ≠ j → Nat.Coprime (q i) (q j)) (hpos : ∀ i, 1 ≤ q i)
    (H : ℕ) (w : ∀ i, ZMod (q i)) :
    Nat.card {z : BddInt H // ∀ i, (z.1 : ZMod (q i)) = w i} ≤
      (2 * H + 1) / (∏ i, q i) + 1 := by
  classical
  let C : ℕ := ∏ i, q i
  have hC1 : 1 ≤ C := by
    dsimp [C]
    exact Finset.one_le_prod (fun i _ => hpos i)
  by_cases hne : Nonempty {z : BddInt H // ∀ i, (z.1 : ZMod (q i)) = w i}
  · rcases hne with ⟨z0, hz0⟩
    have hinj : ∀ z : BddInt H, (∀ i, (z.1 : ZMod (q i)) = w i) →
        (z.1 : ZMod C) = (z0.1 : ZMod C) := by
      intro z hz
      have hzsub : ∀ i, ((z.1 - z0.1 : ℤ) : ZMod (q i)) = 0 := by
        intro i
        have h1 : (z.1 : ZMod (q i)) = (z0.1 : ZMod (q i)) := (hz i).trans (hz0 i).symm
        simpa using sub_eq_zero.mpr h1
      have hdvd : ∀ i, (q i : ℤ) ∣ (z.1 - z0.1) := by
        intro i
        exact ((ZMod.intCast_zmod_eq_zero_iff_dvd (z.1 - z0.1) (q i)).mp (hzsub i))
      have hprod : ((∏ i : ι, q i : ℕ) : ℤ) ∣ (z.1 - z0.1) :=
        pairwise_coprime_prod_dvd_int q (z.1 - z0.1) hcop hdvd
      have hzero : ((z.1 - z0.1 : ℤ) : ZMod C) = 0 := by
        simpa [C] using ((ZMod.intCast_zmod_eq_zero_iff_dvd (z.1 - z0.1) C).mpr hprod)
      exact sub_eq_zero.mp (by simpa using hzero)
    have hleY : Nat.card {z : BddInt H // ∀ i, (z.1 : ZMod (q i)) = w i} ≤
        Nat.card {z : BddInt H // (z.1 : ZMod C) = (z0.1 : ZMod C)} := by
      let f : {z : BddInt H // ∀ i, (z.1 : ZMod (q i)) = w i} →
          {z : BddInt H // (z.1 : ZMod C) = (z0.1 : ZMod C)} :=
        fun x => ⟨x.1, hinj x.1 x.2⟩
      have hf : Function.Injective f := by
        intro x y hxy
        apply Subtype.ext
        apply Subtype.ext
        simpa [f] using (congrArg (fun t : {z : BddInt H // (z.1 : ZMod C) = (z0.1 : ZMod C)} =>
          (t : BddInt H).1) hxy)
      exact Nat.card_le_card_of_injective f hf
    calc
      Nat.card {z : BddInt H // ∀ i, (z.1 : ZMod (q i)) = w i} ≤
          Nat.card {z : BddInt H // (z.1 : ZMod C) = (z0.1 : ZMod C)} := hleY
      _ ≤ (2 * H + 1) / C + 1 := by
        simpa [C] using (bddInt_congruent_card_le H C hC1 (z0.1 : ZMod C))
  · have hzero : Nat.card {z : BddInt H // ∀ i, (z.1 : ZMod (q i)) = w i} = 0 := by
      haveI : IsEmpty {z : BddInt H // ∀ i, (z.1 : ZMod (q i)) = w i} := ⟨fun x => hne ⟨x⟩⟩
      simp
    rw [hzero]
    exact Nat.zero_le _

end CoordinateFiber


/-! ## The box fibre over a full residue tuple -/

section BoxFiber

variable {ι : Type*} [Fintype ι]

/-- Fixing, for every `i`, the residue class of *all* `n` trailing
coefficients modulo the pairwise coprime moduli `q i`, leaves at most
`((2H+1)/(∏ q i) + 1)^n` box polynomials. -/
theorem box_fiber_residues_ncard_le (q : ι → ℕ)
    (hcop : ∀ i j : ι, i ≠ j → Nat.Coprime (q i) (q j)) (hpos : ∀ i, 1 ≤ q i)
    (n H : ℕ) (w : ∀ i, Fin n → ZMod (q i)) :
    Nat.card {f : ↥(Box n H) // ∀ i, boxResidue n H (q i) f = w i} ≤
      ((2 * H + 1) / (∏ i, q i) + 1) ^ n := by
  classical
  let Xj : Fin n → Set (BddInt H) := fun j =>
    {z : BddInt H | ∀ i, (z.1 : ZMod (q i)) = w i j}
  let Y : Type := (j : Fin n) → {z : BddInt H // z ∈ Xj j}
  let φ : {f : ↥(Box n H) // ∀ i, boxResidue n H (q i) f = w i} → Y := fun f =>
    fun j => ⟨(⟨(f.1 : ℤ[X]).coeff j.1, by exact (f.1.2.2.2) j.1 j.isLt⟩ : BddInt H), by
      intro i
      simpa [boxResidue] using congrFun (f.2 i) j⟩
  have hinj : Function.Injective φ := by
    intro f g hfg
    apply Subtype.ext
    apply coeffVec_injective n H
    ext j
    have hj := congrFun hfg j
    simpa [φ, coeffVec, Xj] using (congrArg (fun t : {z : BddInt H // z ∈ Xj j} =>
      (t : BddInt H)) hj)
  have hcardY : Nat.card Y = ∏ j : Fin n, Nat.card {z : BddInt H // z ∈ Xj j} := by
    simp [Y]
  have hleY : Nat.card {f : ↥(Box n H) // ∀ i, boxResidue n H (q i) f = w i} ≤ Nat.card Y := by
    exact Nat.card_le_card_of_injective φ hinj
  calc
    Nat.card {f : ↥(Box n H) // ∀ i, boxResidue n H (q i) f = w i} ≤ Nat.card Y := hleY
    _ = ∏ j : Fin n, Nat.card {z : BddInt H // z ∈ Xj j} := hcardY
    _ ≤ ∏ j : Fin n, ((2 * H + 1) / (∏ i, q i) + 1) := by
      exact Finset.prod_le_prod (fun j _ => Nat.zero_le _) (fun j _ => by
        simpa [Xj] using (coordinate_fiber_ncard_le q hcop hpos H (fun i => w i j)))
    _ = ((2 * H + 1) / (∏ i, q i) + 1) ^ n := by
      simp

end BoxFiber


/-! ## The main multi-prime bound -/

section Main

/-- **(Case-I elementary sieve)** For pairwise coprime prime moduli `q i`
(with residue fields `ZMod (q i)`), the number of box polynomials whose
reduction modulo *each* `q i` has index at least `e i` is at most

    (∏ i, 2^((n+1)^4) · (q i)^(n − e i)) · ((2H+1)/(∏ i, q i) + 1)^n .

Equivalently: imposing per-prime index conditions of "codimension `e i`"
multiplies the box count `(2H+1)^n` by `∏ (q i)^(−e i)`-style factors, with a
single `((2H+1)/C + 1)^n` "modulus `C = ∏ q i`" lattice bound — this is
Bhargava's congruence-density bound in the elementary `C ≤ H` regime, ready to
be summed over squarefull discriminants in Case I. -/
theorem main_multiPrime_box_le {ι : Type*} [Fintype ι] (q : ι → ℕ)
    [hqFact : ∀ i, Fact (Nat.Prime (q i))]
    (hcop : ∀ i j : ι, i ≠ j → Nat.Coprime (q i) (q j))
    (n H : ℕ) (e : ι → ℕ) (he : ∀ i, e i ≤ n) :
    Nat.card {f : ↥(Box n H) // ∀ i, indexClass (F := ZMod (q i)) n (e i) (boxResidue n H (q i) f)} ≤
      (∏ i, 2 ^ ((n + 1) ^ 4) * (q i) ^ (n - e i)) * ((2 * H + 1) / (∏ i, q i) + 1) ^ n := by
  classical
  let V := {f : ↥(Box n H) //
    ∀ i, indexClass (F := ZMod (q i)) n (e i) (boxResidue n H (q i) f)}
  let Wt := {w : (i : ι) → Fin n → ZMod (q i) //
    ∀ i, indexClass (F := ZMod (q i)) n (e i) (w i)}
  let ψ : V → Wt := fun v =>
    ⟨fun i => boxResidue n H (q i) v.1, v.2⟩
  have hfibV : ∀ w : Wt, {x : V // ψ x = w} ≃
      {f : ↥(Box n H) // ∀ i, boxResidue n H (q i) f = w.1 i} := by
    intro w
    refine { toFun := fun x => ⟨x.1.1, ?_⟩,
             invFun := fun f => ⟨⟨f.1, ?_⟩, ?_⟩,
             left_inv := by intro x; apply Subtype.ext; rfl,
             right_inv := by intro f; apply Subtype.ext; rfl }
    · -- membership: ∀ i, boxResidue (q i) x.1.1 = w.1 i, from ψ x = w
      intro i
      have hc := congrFun (congrArg (fun y : Wt => y.1) x.2) i
      simpa [ψ] using hc
    · -- membership of x in V: indexClass of the residues = w's
      intro i
      have heq : boxResidue n H (q i) f.1 = w.1 i := f.2 i
      simpa [heq] using w.2 i
    · -- ψ (⟨f.1, _⟩) = w
      apply Subtype.ext
      funext i
      exact f.2 i
  have hfib_le : ∀ w : Wt,
      Nat.card {f : ↥(Box n H) // ∀ i, boxResidue n H (q i) f = w.1 i} ≤
        ((2 * H + 1) / (∏ i, q i) + 1) ^ n := by
    intro w
    exact box_fiber_residues_ncard_le q hcop (fun i => Nat.Prime.one_le (hqFact i).out) n H w.1
  -- fibre decomposition of V under ψ
  have hVle : Nat.card V ≤ Nat.card Wt * (((2 * H + 1) / (∏ i, q i) + 1) ^ n) := by
    calc
      Nat.card V = Nat.card (Sigma fun w : Wt => {f : ↥(Box n H) // ∀ i, boxResidue n H (q i) f = w.1 i}) := by
        exact Nat.card_congr (((Equiv.sigmaFiberEquiv ψ).symm).trans
          (Equiv.sigmaCongrRight fun w => hfibV w))
      _ = ∑ w : Wt, Nat.card {f : ↥(Box n H) // ∀ i, boxResidue n H (q i) f = w.1 i} := by
        simp
      _ ≤ ∑ _w : Wt, ((2 * H + 1) / (∏ i, q i) + 1) ^ n := by
        exact Finset.sum_le_sum (fun w _ => hfib_le w)
      _ = Nat.card Wt * (((2 * H + 1) / (∏ i, q i) + 1) ^ n) := by
        simp
  -- bound the number of class tuples by the product of per-prime class bounds
  let Wi : ι → Type := fun i =>
    {v : Fin n → ZMod (q i) // indexClass (F := ZMod (q i)) n (e i) v}
  have hWt : Nat.card Wt ≤ ∏ i, 2 ^ ((n + 1) ^ 4) * (q i) ^ (n - e i) := by
    calc
      Nat.card Wt = Nat.card ((i : ι) → Wi i) := by
        refine Nat.card_congr ?_
        exact { toFun := fun w i => ⟨w.1 i, w.2 i⟩,
                invFun := fun t => ⟨fun i => (t i).1, fun i => (t i).2⟩,
                left_inv := by
                  intro w
                  apply Subtype.ext
                  rfl,
                right_inv := by
                  intro t
                  funext i
                  apply Subtype.ext
                  rfl }
      _ = ∏ i, Nat.card (Wi i) := by
        exact Nat.card_pi
      _ ≤ ∏ i, 2 ^ ((n + 1) ^ 4) * (q i) ^ (n - e i) := by
        refine Finset.prod_le_prod (fun i _ => Nat.zero_le _) (fun i _ => ?_)
        have hb := indexClass_card_le (F := ZMod (q i)) n (e i) (he i)
        simpa [Wi, ZMod.card] using hb
  calc
    Nat.card V ≤ Nat.card Wt * (((2 * H + 1) / (∏ i, q i) + 1) ^ n) := hVle
    _ ≤ (∏ i, 2 ^ ((n + 1) ^ 4) * (q i) ^ (n - e i)) *
          (((2 * H + 1) / (∏ i, q i) + 1) ^ n) := by
      exact Nat.mul_le_mul_right _ hWt

end Main

end
end Submission.Vdw
