import Mathlib
import Submission.Work.ZeroEst.defs

/-!
# Area Z, one variable: shared definitions and infrastructure

This file proves `Work.ZeroEst.one_var`, the one-variable zero estimate for a `D`-closed
`ℚ(x)`-linearly independent system of power series: there is a constant `C` such that any
nonzero polynomial combination `Σ Pᵢ fᵢ` with `deg Pᵢ < D` has order `≤ m·D + C`.

Notation: `q fᵢ' = Σ Aᵢⱼ fⱼ`, `θ = q·d/dx`, `Λ Q = q·Q' + Q·Aᵗ` on coefficient vectors,
so that `θ(Q·f) = (ΛQ)·f`.  Iterating `Λ` on the coefficient vector of `R = Σ Pᵢ fᵢ`
produces the "derived" combinations `Fₖ = θᵏR` of controlled degree.  If the iterated
coefficient vectors stay independent over `ℚ(x)` one uses the Wronskian-like determinant of
`(Qₖ)ₖ`; otherwise the system degenerates to fewer functions.  Both cases give
`ord R ≤ m·D + C`.
-/

namespace Work.ZeroEst

open Submission.CDTPlan
open PowerSeries Polynomial

/-! ## Order of the derivative -/

/-- `ord(S') ≥ ord S - 1`. -/
lemma order_deriv_ge (S : ℚ⟦X⟧) : S.order - 1 ≤ (PowerSeries.derivative (R := ℚ) S).order := by
  have h1 : (↑(S.order.toNat - 1) : ℕ∞) ≤ (PowerSeries.derivative (R := ℚ) S).order := by
    apply PowerSeries.nat_le_order
    intro i hi
    rw [PowerSeries.coeff_derivative]
    have h2 : PowerSeries.coeff (i+1) S = 0 := by
      apply PowerSeries.coeff_of_lt_order_toNat
      omega
    rw [h2, zero_mul]
  rcases eq_or_ne S 0 with h | h
  · subst h; simp
  · have hS : S.order = ↑(S.order.toNat) := (PowerSeries.coe_toNat_order h).symm
    have hcast : (↑(S.order.toNat) : ℕ∞) - 1 = ↑(S.order.toNat - 1) := by
      rw [show (1:ℕ∞) = ↑(1:ℕ) from rfl, ENat.natCast_sub]
    rw [hS, hcast]
    exact h1

/-- `ord (q * S') ≥ ord S - 1`. -/
lemma order_theta_ge (q : Polynomial ℚ) (S : ℚ⟦X⟧) :
    S.order - 1 ≤ ((q : ℚ⟦X⟧) * PowerSeries.derivative (R := ℚ) S).order := by
  rw [PowerSeries.order_mul]
  calc S.order - 1 ≤ (PowerSeries.derivative (R := ℚ) S).order := order_deriv_ge S
    _ ≤ (q : ℚ⟦X⟧).order + (PowerSeries.derivative (R := ℚ) S).order := le_add_left le_rfl

/-! ## The derivation operator `Λ` on coefficient vectors -/

variable {m : ℕ}

/-- The coefficient-level operator realising `θ = q·d/dx`: `Λ Q = q·Q' + Q·Aᵗ`, i.e.
`(Λ Q)ᵢ = q·Qᵢ' + Σⱼ Qⱼ·Aⱼᵢ`. -/
noncomputable def Lam (q : Polynomial ℚ) (A : Fin m → Fin m → Polynomial ℚ)
    (Q : Fin m → Polynomial ℚ) : Fin m → Polynomial ℚ :=
  fun i => q * Polynomial.derivative (Q i) + ∑ j, Q j * A j i

/-- The same operator, on power-series coefficient vectors. -/
noncomputable def LamPS (q : Polynomial ℚ) (A : Fin m → Fin m → Polynomial ℚ)
    (Q : Fin m → ℚ⟦X⟧) : Fin m → ℚ⟦X⟧ :=
  fun i => (q : ℚ⟦X⟧) * PowerSeries.derivative (R := ℚ) (Q i) + ∑ j, Q j * (A j i : ℚ⟦X⟧)

/-- Coercion of polynomials to power series commutes with `Λ`. -/
lemma Lam_coe (q : Polynomial ℚ) (A : Fin m → Fin m → Polynomial ℚ)
    (Q : Fin m → Polynomial ℚ) :
    LamPS q A (fun i => (Q i : ℚ⟦X⟧)) = fun i => ((Lam q A Q) i : ℚ⟦X⟧) := by
  funext i
  have hsum : ((∑ j, Q j * A j i : Polynomial ℚ) : ℚ⟦X⟧)
      = ∑ j, (Q j : ℚ⟦X⟧) * (A j i : ℚ⟦X⟧) := by
    simp only [← Polynomial.coeToPowerSeries.ringHom_apply, map_sum, map_mul]
  simp only [Lam, LamPS, Polynomial.coe_add, Polynomial.coe_mul, PowerSeries.derivative_coe]
  rw [hsum]

/-- The fundamental identity: `θ(⟨Q,f⟩) = ⟨ΛQ,f⟩` where `θ = q·d/dx` and `⟨Q,f⟩ = Σ Qᵢ fᵢ`. -/
lemma LamPS_dot (q : Polynomial ℚ) (A : Fin m → Fin m → Polynomial ℚ)
    (f : Fin m → ℚ⟦X⟧)
    (hdc : ∀ i, (q:ℚ⟦X⟧) * PowerSeries.derivative (R := ℚ) (f i)
      = ∑ j, (A i j : ℚ⟦X⟧) * f j)
    (Q : Fin m → ℚ⟦X⟧) :
    (∑ i, (LamPS q A Q) i * f i)
      = (q:ℚ⟦X⟧) * PowerSeries.derivative (R := ℚ) (∑ i, Q i * f i) := by
  have hder : PowerSeries.derivative (R := ℚ) (∑ i, Q i * f i)
      = ∑ i, (Q i * PowerSeries.derivative (R := ℚ) (f i)
              + PowerSeries.derivative (R := ℚ) (Q i) * f i) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    ring
  have hL : (∑ i, (LamPS q A Q) i * f i)
      = (∑ i, (q:ℚ⟦X⟧) * PowerSeries.derivative (R := ℚ) (Q i) * f i)
        + (∑ i, (∑ j, Q j * (A j i : ℚ⟦X⟧)) * f i) := by
    rw [← Finset.sum_add_distrib]
    simp only [LamPS]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [add_mul]
  have hA2 : (∑ i, (∑ j, Q j * (A j i : ℚ⟦X⟧)) * f i)
      = (∑ i, Q i * (q:ℚ⟦X⟧) * PowerSeries.derivative (R := ℚ) (f i)) := by
    have e1 : (∑ i, (∑ j, Q j * (A j i : ℚ⟦X⟧)) * f i)
        = ∑ i, ∑ j, Q j * (A j i : ℚ⟦X⟧) * f i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul]
    rw [e1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    show ∑ j, Q i * (A i j : ℚ⟦X⟧) * f j = Q i * (q:ℚ⟦X⟧) * PowerSeries.derivative (R := ℚ) (f i)
    rw [show (∑ j, Q i * (A i j:ℚ⟦X⟧) * f j) = Q i * (∑ j, (A i j:ℚ⟦X⟧) * f j) by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring]
    rw [← hdc i]
    ring
  have hR : (q:ℚ⟦X⟧) * PowerSeries.derivative (R := ℚ) (∑ i, Q i * f i)
      = (∑ i, Q i * (q:ℚ⟦X⟧) * PowerSeries.derivative (R := ℚ) (f i))
        + (∑ i, (q:ℚ⟦X⟧) * PowerSeries.derivative (R := ℚ) (Q i) * f i) := by
    rw [hder, Finset.mul_sum]
    simp only [mul_add]
    rw [Finset.sum_add_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_; ring
    · refine Finset.sum_congr rfl fun i _ => ?_; ring
  rw [hL, hA2, hR, add_comm]

/-- `⟨ΛQ, f⟩ = θ⟨Q,f⟩` for polynomial coefficient vectors. -/
lemma Lam_dot (q : Polynomial ℚ) (A : Fin m → Fin m → Polynomial ℚ)
    (f : Fin m → ℚ⟦X⟧)
    (hdc : ∀ i, (q:ℚ⟦X⟧) * PowerSeries.derivative (R := ℚ) (f i)
      = ∑ j, (A i j : ℚ⟦X⟧) * f j)
    (Q : Fin m → Polynomial ℚ) :
    (∑ i, ((Lam q A Q) i : ℚ⟦X⟧) * f i)
      = (q:ℚ⟦X⟧) * PowerSeries.derivative (R := ℚ) (∑ i, (Q i : ℚ⟦X⟧) * f i) := by
  have h := LamPS_dot q A f hdc (fun i => (Q i : ℚ⟦X⟧))
  rwa [Lam_coe] at h

/-! ## Degree bookkeeping -/

/-- The largest degree appearing in the matrix `A`. -/
noncomputable def Amax (A : Fin m → Fin m → Polynomial ℚ) : ℕ :=
  Finset.univ.sup fun i => Finset.univ.sup fun j => (A i j).natDegree

lemma le_Amax (A : Fin m → Fin m → Polynomial ℚ) (i j : Fin m) :
    (A i j).natDegree ≤ Amax A :=
  le_trans (Finset.le_sup (Finset.mem_univ j) (f := fun j => (A i j).natDegree))
    (Finset.le_sup (Finset.mem_univ i) (f := fun i => Finset.univ.sup fun j => (A i j).natDegree))

/-- Coefficient form of "degree `< d`". -/
def DegLT {n : ℕ} (Q : Fin n → Polynomial ℚ) (d : ℕ) : Prop :=
  ∀ i, ∀ k, d ≤ k → (Q i).coeff k = 0

lemma DegLT_iff_degree {n : ℕ} (Q : Fin n → Polynomial ℚ) (d : ℕ) :
    DegLT Q d ↔ ∀ i, (Q i).degree < (d : WithBot ℕ) := by
  constructor
  · intro h i
    rw [Polynomial.degree_lt_iff_coeff_zero]
    exact h i
  · intro h i k hk
    exact (Polynomial.degree_lt_iff_coeff_zero (Q i) d).mp (h i) k hk

/-- `Λ` raises the degree bound by `q.natDegree + Amax A + 1`. -/
lemma Lam_DegLT (q : Polynomial ℚ) (A : Fin m → Fin m → Polynomial ℚ)
    (Q : Fin m → Polynomial ℚ) (d : ℕ) (hd : 1 ≤ d) (hQ : DegLT Q d) :
    DegLT (Lam q A Q) (d + (q.natDegree + Amax A + 1)) := by
  intro i k hk
  have hkq : q.natDegree + d ≤ k + 1 := by omega
  have hkA : d + Amax A ≤ k := by omega
  simp only [Lam]
  rw [Polynomial.coeff_add]
  have h1 : (q * Polynomial.derivative (Q i)).coeff k = 0 := by
    rw [Polynomial.coeff_mul]
    refine Finset.sum_eq_zero fun a ha => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at ha
    rw [Polynomial.coeff_derivative]
    by_cases hq0 : q.coeff a.1 = 0
    · rw [hq0, zero_mul]
    · have hdeg : a.1 ≤ q.natDegree := by
        by_contra hh
        exact hq0 (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega))
      have hz : (Q i).coeff (a.2 + 1) = 0 := hQ i (a.2+1) (by omega)
      rw [hz]; ring
  have h2 : (∑ j, Q j * A j i).coeff k = 0 := by
    rw [← Polynomial.lcoeff_apply (R := ℚ) k, map_sum]
    simp only [Polynomial.lcoeff_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Polynomial.coeff_mul]
    refine Finset.sum_eq_zero fun a ha => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at ha
    by_cases hqa : (A j i).coeff a.2 = 0
    · rw [hqa, mul_zero]
    · have hdeg : a.2 ≤ (A j i).natDegree := by
        by_contra hh
        exact hqa (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega))
      have hA : (A j i).natDegree ≤ Amax A := le_Amax A j i
      have hz : (Q j).coeff a.1 = 0 := hQ j a.1 (by omega)
      rw [hz, zero_mul]
  rw [h1, h2, add_zero]

/-! ## The Λ-orbit of a coefficient vector

Given the `D`-closed datum `(q, A)` and a starting vector `P`, the orbit `Q k = Λᵏ P`
produces combinations `F k = ⟨Q k, f⟩ = θᵏ R`, with `DegLT (Q k) (D + k·δ)` whenever
`DegLT P D`. -/

section Orbit

variable (q : Polynomial ℚ) (A : Fin m → Fin m → Polynomial ℚ)

/-- `Q k = Λᵏ P`. -/
noncomputable def orbit (P : Fin m → Polynomial ℚ) (k : ℕ) : Fin m → Polynomial ℚ :=
  (Lam q A)^[k] P

/-- `δ = q.natDegree + Amax A + 1`: the per-step degree growth of the orbit. -/
noncomputable def dlt : ℕ := q.natDegree + Amax A + 1

lemma orbit_zero (P : Fin m → Polynomial ℚ) : orbit q A P 0 = P := rfl

lemma orbit_succ (P : Fin m → Polynomial ℚ) (k : ℕ) :
    orbit q A P (k+1) = Lam q A (orbit q A P k) :=
  Function.iterate_succ_apply' _ _ _

/-- The orbit keeps the degree bound growing by `δ` per step. -/
lemma orbit_DegLT (P : Fin m → Polynomial ℚ) (D : ℕ) (hD : 1 ≤ D) (hP : DegLT P D) :
    ∀ k, DegLT (orbit q A P k) (D + k * dlt q A) := by
  intro k
  induction k with
  | zero => simpa [orbit_zero] using hP
  | succ k ih =>
      have hd : 1 ≤ D + k * dlt q A := by omega
      have hlam := Lam_DegLT q A (orbit q A P k) (D + k * dlt q A) hd ih
      simpa [orbit_succ, dlt, Nat.succ_mul, add_assoc] using hlam

end Orbit

end Work.ZeroEst
