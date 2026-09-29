import Mathlib
import Submission.Work.Holonomy3.aux_defs
import Submission.Work.Holonomy3.finSuccEquiv_embedVar_zero
import Submission.Work.Holonomy3.finSuccEquiv_embedVar_succ
import Submission.Work.Holonomy3.finSuccEquiv_coe_mvPolynomial
import Submission.Work.Holonomy3.polyIndepPolyCoeff

/-!
# Injectivity of `auxSeries` for a `ℚ(x)`-independent family

If `f : Fin m → ℚ⟦x⟧` is `ℚ(x)`-linearly independent (`Submission.CDTPlan.PolyIndependent`)
then the map `Q ↦ auxSeries f Q = Σ_i Q_i(x) · Π_s f_{i_s}(x_s)` is injective.

The proof is by induction on the number `d` of variables.  Peeling off the first variable via the
algebra isomorphism `MvPowerSeries.finSuccEquiv : ℚ⟦X_0,…,X_n⟧ ≃ₐ[ℚ] ℚ⟦X_1,…,X_n⟧⟦X_0⟧` turns
`auxSeries f Q` into `Σ_a (f_a(X_0)) · B_a(X_1,…,X_n)[X_0]`, where the coefficients `B_a` are
*polynomials* in `X_0`.  The basic lemma `polyIndepPolyCoeff` (`Work.Holonomy3.polyIndepPolyCoeff`)
then shows `B_a = 0` for every `a`; extracting the coefficient of `X_0^k` from `B_a = 0` gives,
for each `a` and `k`, an identity of exactly the same shape in `n` variables, to which the
induction hypothesis applies.
-/

namespace Work.Holonomy3

open Submission.CDTPlan
open scoped BigOperators

noncomputable section

variable {m : ℕ}

/-! ## Helper lemmas -/

/-- Splitting a sum over the functions `Fin (n+1) → Fin m` according to their value at `0`. -/
lemma sum_cons_equiv {m n : ℕ} {M : Type*} [AddCommMonoid M]
    (G : (Fin (n+1) → Fin m) → M) :
    (∑ i, G i) = ∑ a : Fin m, ∑ j : Fin n → Fin m, G (Fin.cons a j) := by
  have h1 : (∑ i, G i) = ∑ p : Fin m × (Fin n → Fin m), G (Fin.cons p.1 p.2) :=
    (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n+1) => Fin m))
      (fun p : Fin m × (Fin n → Fin m) => G (Fin.cons p.1 p.2)) (fun i => G i)
      (fun p => by congr 1)).symm
  rw [h1, Fintype.sum_prod_type]

/-- `restK n k p` is the coefficient of `X 0 ^ k` in the polynomial `p ∈ ℚ[X_0,…,X_n]`, read as a
polynomial in the remaining variables `X_1,…,X_n` (via `MvPolynomial.finSuccEquiv`). -/
def restK (n k : ℕ) (p : MvPolynomial (Fin (n + 1)) ℚ) : MvPolynomial (Fin n) ℚ :=
  Polynomial.coeff (MvPolynomial.finSuccEquiv ℚ n p) k

/-- The polynomial in the outer variable `X_0` (with coefficients in `ℚ⟦X_1..X_n⟧`) obtained by
grouping the terms of `finSuccEquiv (auxSeries f Q)` according to the value `a` of `i 0`. -/
def peelB (f : Fin m → PowerSeries ℚ) (n : ℕ)
    (Q : (Fin (n + 1) → Fin m) → MvPolynomial (Fin (n + 1)) ℚ) (a : Fin m) :
    Polynomial (MvPowerSeries (Fin n) ℚ) :=
  ∑ j : Fin n → Fin m,
    Polynomial.map MvPolynomial.coeToMvPowerSeries.ringHom
        (MvPolynomial.finSuccEquiv ℚ n (Q (Fin.cons a j)))
      * Polynomial.C (∏ s : Fin n, embedVar s (f (j s)))

/-- The image of `Π_s embedVar s (g s)` under `finSuccEquiv`: peel off the variable `X_0`. -/
lemma finSuccEquiv_prod {n : ℕ} (g : Fin (n+1) → PowerSeries ℚ) :
    MvPowerSeries.finSuccEquiv ℚ n (∏ s : Fin (n+1), embedVar s (g s))
      = PowerSeries.map (algebraMap ℚ (MvPowerSeries (Fin n) ℚ)) (g 0)
        * PowerSeries.C (∏ j : Fin n, embedVar j (g j.succ)) := by
  rw [show (∏ s : Fin (n+1), embedVar s (g s))
      = embedVar 0 (g 0) * ∏ j : Fin n, embedVar j.succ (g j.succ) from
    Fin.prod_univ_succ (fun s => embedVar s (g s))]
  rw [map_mul, finSuccEquiv_embedVar_zero]
  rw [show MvPowerSeries.finSuccEquiv ℚ n (∏ j : Fin n, embedVar j.succ (g j.succ))
      = ∏ j : Fin n, PowerSeries.C (embedVar j (g j.succ)) from by
    rw [map_prod]
    simp only [finSuccEquiv_embedVar_succ]]
  rw [← map_prod]

/-- Transport of `auxSeries` through `finSuccEquiv`, indexed by `i`. -/
lemma finSuccEquiv_auxSeries {m n : ℕ} (f : Fin m → PowerSeries ℚ)
    (Q : (Fin (n + 1) → Fin m) → MvPolynomial (Fin (n + 1)) ℚ) :
    MvPowerSeries.finSuccEquiv ℚ n (auxSeries f Q)
      = ∑ i : Fin (n + 1) → Fin m,
          ((Polynomial.map MvPolynomial.coeToMvPowerSeries.ringHom
              (MvPolynomial.finSuccEquiv ℚ n (Q i)) : Polynomial (MvPowerSeries (Fin n) ℚ)) :
            PowerSeries (MvPowerSeries (Fin n) ℚ))
          * PowerSeries.map (algebraMap ℚ (MvPowerSeries (Fin n) ℚ)) (f (i 0))
          * PowerSeries.C (∏ j : Fin n, embedVar j (f (i j.succ))) := by
  rw [auxSeries]
  simp only [map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [finSuccEquiv_prod (fun s => f (i s))]
  rw [finSuccEquiv_coe_mvPolynomial]
  rw [mul_assoc]

/-- The coercion of `peelB f n Q a` to a power series, as an explicit sum. -/
lemma coe_peelB {m n : ℕ} (f : Fin m → PowerSeries ℚ)
    (Q : (Fin (n + 1) → Fin m) → MvPolynomial (Fin (n + 1)) ℚ) (a : Fin m) :
    ((peelB f n Q a : Polynomial (MvPowerSeries (Fin n) ℚ)) : PowerSeries (MvPowerSeries (Fin n) ℚ))
      = ∑ j : Fin n → Fin m,
          ((Polynomial.map MvPolynomial.coeToMvPowerSeries.ringHom
              (MvPolynomial.finSuccEquiv ℚ n (Q (Fin.cons a j))) : Polynomial (MvPowerSeries (Fin n) ℚ)) :
            PowerSeries (MvPowerSeries (Fin n) ℚ))
          * PowerSeries.C (∏ s : Fin n, embedVar s (f (j s))) := by
  rw [peelB, ← Polynomial.coeToPowerSeries.ringHom_apply]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul]
  simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C]

/-- Transport of `auxSeries` through `finSuccEquiv`, grouped by `a = i 0`. -/
lemma finSuccEquiv_auxSeries' {m n : ℕ} (f : Fin m → PowerSeries ℚ)
    (Q : (Fin (n + 1) → Fin m) → MvPolynomial (Fin (n + 1)) ℚ) :
    MvPowerSeries.finSuccEquiv ℚ n (auxSeries f Q)
      = ∑ a : Fin m, PowerSeries.map (algebraMap ℚ (MvPowerSeries (Fin n) ℚ)) (f a)
          * ((peelB f n Q a : Polynomial (MvPowerSeries (Fin n) ℚ)) :
              PowerSeries (MvPowerSeries (Fin n) ℚ)) := by
  rw [finSuccEquiv_auxSeries, sum_cons_equiv]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [coe_peelB, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by simp only [Fin.cons_zero, Fin.cons_succ]; ring

/-- The `k`-th coefficient of `peelB f n Q a`, expanded in the `n` remaining variables. -/
lemma peelB_coeff {m n : ℕ} (f : Fin m → PowerSeries ℚ)
    (Q : (Fin (n + 1) → Fin m) → MvPolynomial (Fin (n + 1)) ℚ) (a : Fin m) (k : ℕ) :
    Polynomial.coeff (peelB f n Q a) k
      = ∑ j : Fin n → Fin m,
          (restK n k (Q (Fin.cons a j)) : MvPowerSeries (Fin n) ℚ)
            * ∏ s : Fin n, embedVar s (f (j s)) := by
  rw [peelB, ← Polynomial.lcoeff_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.lcoeff_apply, Polynomial.coeff_mul_C, Polynomial.coeff_map,
    MvPolynomial.coeToMvPowerSeries.ringHom_apply]
  rfl

/-! ## The induction -/

/-- The induction on the number of variables. -/
theorem auxSeries_injective_aux {m : ℕ} (f : Fin m → PowerSeries ℚ)
    (hpi : Submission.CDTPlan.PolyIndependent f) :
    ∀ d : ℕ, ∀ Q : (Fin d → Fin m) → MvPolynomial (Fin d) ℚ,
      auxSeries f Q = 0 → Q = 0 := by
  intro d
  induction d with
  | zero =>
    intro Q h
    have : Subsingleton (Fin 0 → Fin m) := ⟨fun i j => funext fun k => k.elim0⟩
    refine funext fun i => ?_
    have h1 : (∑ i' : Fin 0 → Fin m,
          (Q i' : MvPowerSeries (Fin 0) ℚ) * ∏ s : Fin 0, embedVar s (f (i' s)))
        = (Q i : MvPowerSeries (Fin 0) ℚ) * ∏ s : Fin 0, embedVar s (f (i s)) :=
      Finset.sum_eq_single i (fun b _ hb => absurd (Subsingleton.elim b i) hb)
        (fun hh => absurd (Finset.mem_univ i) hh)
    rw [auxSeries] at h
    rw [h1] at h
    simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one] at h
    exact MvPolynomial.coe_eq_zero_iff.mp h
  | succ n ih =>
    intro Q h
    have hmap : MvPowerSeries.finSuccEquiv ℚ n (auxSeries f Q) = 0 := by rw [h, map_zero]
    have hB : ∀ a : Fin m, peelB f n Q a = 0 :=
      polyIndepPolyCoeff f hpi (peelB f n Q)
        (by rw [← finSuccEquiv_auxSeries']; exact hmap)
    have hcoeff : ∀ (a : Fin m) (k : ℕ),
        auxSeries f (fun j : Fin n → Fin m => restK n k (Q (Fin.cons a j))) = 0 := by
      intro a k
      rw [auxSeries, ← peelB_coeff f Q a k, hB a, Polynomial.coeff_zero]
    have hQ : ∀ i : Fin (n+1) → Fin m, Q i = 0 := by
      intro i
      have h2 : ∀ k, restK n k (Q i) = 0 := by
        intro k
        have h3 := congrFun (ih (fun j : Fin n → Fin m => restK n k (Q (Fin.cons (i 0) j)))
          (hcoeff (i 0) k)) (Fin.tail i)
        rwa [Fin.cons_self_tail] at h3
      refine (MvPolynomial.finSuccEquiv ℚ n).injective ?_
      rw [Polynomial.ext_iff]
      intro k
      simpa [restK] using h2 k
    exact funext hQ

/-- If `f` is `ℚ(x)`-linearly independent (`PolyIndependent`), then the map
`Q ↦ Σ_i Q i · f_{i_1}(x_1) ⋯ f_{i_d}(x_d)` (i.e. `Submission.CDTPlan.auxSeries f`) is injective:
if `Σ_i Q_i(x) Π_s f_{i_s}(x_s)` vanishes, then every `Q i` is `0`.

Suggested route (or something equivalent): (1) for any commutative `ℚ`-algebra `R`, if the
`g : Fin m → PowerSeries ℚ` are `ℚ`-linearly independent and `B a ∈ R[X]` satisfy
`Σ_a (g a).map (algebraMap ℚ R) * B a = 0`, then all `B a = 0`: the coefficients give, for each
`n`, a relation `Σ_{a,j} c_{a,n-j} [X^j]B_a = 0` in `R`; using a `ℚ`-basis of `R`
(`Module.Free.of_divisionRing`, `Module.Free.chooseBasis`) reduce to the `ℚ`-linear independence of
the `g a`.  (2) Induct on `d` using
`MvPowerSeries.finSuccEquiv : MvPowerSeries (Fin (d+1)) R ≃ₐ[R] PowerSeries (MvPowerSeries (Fin d) R)`
with `R = ℚ`; applying it to `auxSeries f Q = 0` and grouping by `a = i 0` produces
`Σ_a (f a).map (MvPowerSeries.C) * B_a = 0`, so all `B_a = 0` by (1); extracting the `X^k`
coefficient and expanding in the remaining variables gives an identity of the same shape in `d`
variables, to which the induction hypothesis applies. -/
theorem auxSeries_injective {m d : ℕ} (f : Fin m → PowerSeries ℚ)
    (hpi : Submission.CDTPlan.PolyIndependent f)
    (Q : (Fin d → Fin m) → MvPolynomial (Fin d) ℚ)
    (h : Submission.CDTPlan.auxSeries f Q = 0) : Q = 0 :=
  auxSeries_injective_aux f hpi d Q h

end

end Work.Holonomy3
