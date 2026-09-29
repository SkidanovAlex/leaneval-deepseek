import Mathlib
import Submission.Work.ZeroEst.one_var_defs
import Submission.Work.ZeroEst2.span_witness
import Submission.Commons.FieldTheory.RatFunc.exists_derivation_ratFunc

/-!
# Prefix bases of `Λ`-orbits (`Work.ZeroEst.orbit_prefix`)

Let `q ∈ ℚ[X]`, `A ∈ Mat_m(ℚ[X])`, `P ∈ ℚ[X]^m`, and let
`Λ Q = q·Q' + Q·Aᵗ` be the coefficient-level operator realising `θ = q·d/dx` on combinations
`⟨Q, f⟩ = Σᵢ Qᵢ fᵢ`, so that `orbit q A P k = Λᵏ P`.

This file shows that some **prefix** of the embedded orbit
`v k := (algebraMap (orbit q A P k j))_j ∈ ℚ(x)^m` is a `ℚ(x)`-basis of the span of
`v 0, …, v (m-1)`:

* the set `{k : v k ∈ span(v 0, …, v (k-1))}` is nonempty (indeed some `k ≤ m` lies in it, since
  `v 0, …, v m` are `m+1` vectors of the `m`-dimensional space `ℚ(x)^m`), and
  `t := min {k : v k ∈ span(v 0, …, v (k-1))}` (so `t ≤ m`);
* `v 0, …, v (t-1)` are independent because no `v k` with `k < t` lies in the span of its
  predecessors (`Work.ZeroEst2.span_witness_aux`);
* the key point, which uses the interplay of `θ` with `ℚ(x)`-coefficients: the subspace
  `S := span(v 0, …, v (t-1))` is stable under `θ`, i.e. under the *twisted-linearity*
  identity
  `Λ(Σᵢ cᵢ·uᵢ) = Σᵢ (q·cᵢ')·uᵢ + Σᵢ cᵢ·Λ(uᵢ)`,
  because `Λ vᵢ = v (i+1)` and `v j ∈ S` for all `j ≤ t`.  Hence `v k ∈ S` for every `k`, so `S`
  contains (and is contained in) the span of the first `m` orbit vectors.

The `ℚ`-linear operator `Λ` on `ℚ(x)`-vectors is `Work.ZeroEst.shift`, built from a derivation
`δ` of `ℚ(x)` with `δ (algebraMap p) = algebraMap p'` (`Work.ZeroEst.ratDeriv`, obtained from the
commons lemma `Commons.FieldTheory.RatFunc.exists_derivation_ratFunc`).  Since `δ` is only
`ℚ`-linear, `Λ` satisfies the twisted-linearity identity above rather than being `ℚ(x)`-linear —
this is exactly the identity that makes the argument work.
-/

namespace Work.ZeroEst

open Polynomial

noncomputable section

-- `exists_derivation_ratFunc` is stated for the `ℚ`-algebra structure on `ℚ(x)` induced by
-- `ℚ[X]`, which is not syntactically the same as the canonical `DivisionRing.toRatAlgebra`
-- (the two are `Subsingleton.elim`-equal, and both have the same `algebraMap` and `smul`, so
-- nothing is lost); installing it here makes every `Derivation ℚ (RatFunc ℚ) (RatFunc ℚ)` in this
-- file use that instance.
local instance : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ

/-- The `k`-th `Λ`-orbit vector `Λᵏ P`, embedded in `ℚ(x)^m`. -/
def orbitCoeff {m : ℕ} (q : Polynomial ℚ) (A : Fin m → Fin m → Polynomial ℚ)
    (P : Fin m → Polynomial ℚ) (k : ℕ) : Fin m → RatFunc ℚ :=
  fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ) (orbit q A P k j)

/-- A derivation of `ℚ(x)` which extends the polynomial derivative. -/
def ratDeriv : Derivation ℚ (RatFunc ℚ) (RatFunc ℚ) :=
  Classical.choose (Commons.FieldTheory.RatFunc.exists_derivation_ratFunc (K := ℚ))

lemma ratDeriv_algebraMap (p : Polynomial ℚ) :
    ratDeriv (algebraMap (Polynomial ℚ) (RatFunc ℚ) p)
      = algebraMap (Polynomial ℚ) (RatFunc ℚ) p.derivative :=
  Classical.choose_spec (Commons.FieldTheory.RatFunc.exists_derivation_ratFunc (K := ℚ)) p

/-- The operator `Λ = q·d/dx + Aᵗ` on `ℚ(x)`-coefficient vectors: it is `ℚ`-linear (but not
`ℚ(x)`-linear) and satisfies `shift (orbitCoeff k) = orbitCoeff (k+1)`. -/
def shift {m : ℕ} (q : Polynomial ℚ) (A : Fin m → Fin m → Polynomial ℚ) (Z : Fin m → RatFunc ℚ) :
    Fin m → RatFunc ℚ :=
  fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ) q * ratDeriv (Z j)
    + ∑ i, Z i * algebraMap (Polynomial ℚ) (RatFunc ℚ) (A i j)

lemma shift_zero {m : ℕ} (q : Polynomial ℚ) (A : Fin m → Fin m → Polynomial ℚ) :
    shift q A (0 : Fin m → RatFunc ℚ) = 0 := by
  funext j
  simp [shift]

lemma shift_add {m : ℕ} (q : Polynomial ℚ) (A : Fin m → Fin m → Polynomial ℚ)
    (Z Z' : Fin m → RatFunc ℚ) : shift q A (Z + Z') = shift q A Z + shift q A Z' := by
  funext j
  simp only [shift, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  ring

lemma shift_smul {m : ℕ} (q : Polynomial ℚ) (A : Fin m → Fin m → Polynomial ℚ) (c : RatFunc ℚ)
    (Z : Fin m → RatFunc ℚ) :
    shift q A (c • Z) = (algebraMap (Polynomial ℚ) (RatFunc ℚ) q * ratDeriv c) • Z
      + c • shift q A Z := by
  funext j
  simp only [shift, Pi.smul_apply, Pi.add_apply, smul_eq_mul, Derivation.leibniz, mul_add,
    Finset.mul_sum]
  ring_nf

/-- **Twisted linearity** of `Λ` over `ℚ(x)`-coefficients. -/
lemma shift_sum {m : ℕ} {ι : Type*} (q : Polynomial ℚ) (A : Fin m → Fin m → Polynomial ℚ)
    (s : Finset ι) (d : ι → RatFunc ℚ) (u : ι → Fin m → RatFunc ℚ) :
    shift q A (∑ i ∈ s, d i • u i)
      = ∑ i ∈ s, (algebraMap (Polynomial ℚ) (RatFunc ℚ) q * ratDeriv (d i)) • u i
        + ∑ i ∈ s, d i • shift q A (u i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [shift_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, shift_add, shift_smul,
        ih]
      abel

lemma shift_orbitCoeff_apply {m : ℕ} (q : Polynomial ℚ) (A : Fin m → Fin m → Polynomial ℚ)
    (P : Fin m → Polynomial ℚ) (k : ℕ) (j : Fin m) :
    shift q A (orbitCoeff q A P k) j = algebraMap (Polynomial ℚ) (RatFunc ℚ)
      (q * Polynomial.derivative (orbit q A P k j) + ∑ i, orbit q A P k i * A i j) := by
  simp only [shift, orbitCoeff, ratDeriv_algebraMap, map_add, map_mul, map_sum]

lemma shift_orbitCoeff {m : ℕ} (q : Polynomial ℚ) (A : Fin m → Fin m → Polynomial ℚ)
    (P : Fin m → Polynomial ℚ) (k : ℕ) :
    shift q A (orbitCoeff q A P k) = orbitCoeff q A P (k+1) := by
  funext j
  rw [shift_orbitCoeff_apply]
  simp only [orbitCoeff, orbit_succ, Lam]

theorem orbit_prefix (m : ℕ) (q : Polynomial ℚ) (A : Fin m → Fin m → Polynomial ℚ)
    (P : Fin m → Polynomial ℚ) :
    ∃ t : ℕ, t ≤ m ∧
      LinearIndependent (RatFunc ℚ) (fun a : Fin t => fun j =>
        algebraMap (Polynomial ℚ) (RatFunc ℚ) (orbit q A P (a : ℕ) j)) ∧
      (∀ a : Fin t, (fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ)
          (q * Polynomial.derivative (orbit q A P (a : ℕ) j)
            + ∑ i, orbit q A P (a : ℕ) i * A i j)) ∈
        Submodule.span (RatFunc ℚ) (Set.range fun a : Fin t => fun j =>
          algebraMap (Polynomial ℚ) (RatFunc ℚ) (orbit q A P (a : ℕ) j))) ∧
      Submodule.span (RatFunc ℚ) (Set.range fun a : Fin t => fun j =>
          algebraMap (Polynomial ℚ) (RatFunc ℚ) (orbit q A P (a : ℕ) j)) =
        Submodule.span (RatFunc ℚ) (Set.range fun a : Fin m => fun j =>
          algebraMap (Polynomial ℚ) (RatFunc ℚ) (orbit q A P (a : ℕ) j)) := by
  classical
  -- the embedded orbit, as a sequence in `ℚ(x)^m`
  set v : ℕ → (Fin m → RatFunc ℚ) := fun k => orbitCoeff q A P k with hv
  -- the span of the first `k` orbit vectors
  set Sv : ℕ → Submodule (RatFunc ℚ) (Fin m → RatFunc ℚ) :=
    fun k => Submodule.span (RatFunc ℚ) (Set.range fun i : Fin k => v i) with hSv
  -- some `k ≤ m` has `v k` in the span of its predecessors
  have hex : ∃ k, k ≤ m ∧ v k ∈ Sv k := by
    by_contra hcon
    have hcon' : ∀ k, k ≤ m → v k ∉ Sv k := fun k hk hmem => hcon ⟨k, hk, hmem⟩
    have hLI : LinearIndependent (RatFunc ℚ) (fun i : Fin (m+1) => v i) :=
      Work.ZeroEst2.span_witness_aux v (m+1) fun k hk => hcon' k (Nat.lt_succ_iff.mp hk)
    have hcard := hLI.fintype_card_le_finrank
    simp only [Fintype.card_fin, Module.finrank_fin_fun] at hcard
    omega
  -- the least such index
  let t := Nat.find hex
  have ht_le : t ≤ m := (Nat.find_spec hex).1
  have ht_mem : v t ∈ Sv t := (Nat.find_spec hex).2
  have ht_min : ∀ k < t, v k ∉ Sv k := by
    intro k hk hmem
    exact Nat.find_min hex hk ⟨le_trans (le_of_lt hk) ht_le, hmem⟩
  -- every `v j` with `j ≤ t` lies in `Sv t`
  have hgen : ∀ j ≤ t, v j ∈ Sv t := by
    intro j hj
    rcases lt_or_eq_of_le hj with h | h
    · exact Submodule.subset_span ⟨⟨j, h⟩, rfl⟩
    · rw [h]; exact ht_mem
  -- `Sv t` is stable under `Λ`
  have hstable : ∀ Z ∈ Sv t, shift q A Z ∈ Sv t := by
    intro Z hZ
    obtain ⟨d, hd⟩ := Submodule.mem_span_range_iff_exists_fun (R := RatFunc ℚ) |>.mp hZ
    have hsum : shift q A (∑ i : Fin t, d i • v i)
        = ∑ i : Fin t, (algebraMap (Polynomial ℚ) (RatFunc ℚ) q * ratDeriv (d i)) • v i
          + ∑ i : Fin t, d i • shift q A (v i) :=
      shift_sum q A Finset.univ d (fun i : Fin t => v i)
    rw [← hd, hsum]
    refine Submodule.add_mem _ ?_ ?_
    · refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hgen i i.isLt.le)
    · refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
      rw [shift_orbitCoeff]
      exact hgen ((i : ℕ) + 1) (by have := i.isLt; omega)
  -- hence every later orbit vector lies in `Sv t`
  have hprop : ∀ j, v (t + j) ∈ Sv t := by
    intro j
    induction j with
    | zero => simpa using ht_mem
    | succ j ih =>
        have h := hstable (v (t + j)) ih
        rw [shift_orbitCoeff] at h
        have hji : t + (j + 1) = (t + j) + 1 := by omega
        rwa [hji]
  -- so all of `v 0, …, v (m-1)` lies in `Sv t`
  have hgen_all : ∀ j ≤ m, v j ∈ Sv t := by
    intro j hj
    rcases lt_or_ge t j with h | h
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (le_of_lt h)
      exact hprop k
    · exact hgen j h
  refine ⟨t, ht_le, ?_, ?_, ?_⟩
  · exact Work.ZeroEst2.span_witness_aux v t ht_min
  · intro a
    have h1 : (fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ)
        (q * Polynomial.derivative (orbit q A P (a : ℕ) j)
          + ∑ i, orbit q A P (a : ℕ) i * A i j)) = v ((a : ℕ) + 1) := by
      funext j
      rw [← shift_orbitCoeff_apply, shift_orbitCoeff]
    rw [h1]
    exact hgen ((a : ℕ) + 1) (Nat.succ_le_of_lt a.isLt)
  · refine le_antisymm ?_ ?_
    · refine Submodule.span_mono fun x hx => ?_
      obtain ⟨i, rfl⟩ := hx
      exact ⟨⟨i, lt_of_lt_of_le i.isLt ht_le⟩, rfl⟩
    · refine Submodule.span_le.mpr fun x hx => ?_
      obtain ⟨i, rfl⟩ := hx
      exact hgen_all i i.isLt.le

end

end Work.ZeroEst
