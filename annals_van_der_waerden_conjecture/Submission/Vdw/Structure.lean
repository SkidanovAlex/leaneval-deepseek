import ChallengeDeps
import Submission.Vdw.Counting
import Submission.Commons.FieldTheory.PolynomialGaloisGroup.card_gal_le_factorial
import Submission.Commons.FieldTheory.PolynomialGaloisGroup.card_gal_mul_le
import Submission.Commons.Data.Nat.factorial_mul_lt

open vanDerWaerdenConjecture
open Function Polynomial Filter Asymptotics
open Commons.FieldTheory.PolynomialGaloisGroup
open Commons.Data.Nat

set_option autoImplicit false

/-!
# Structure of the bad set

Every reducible (in `ℤ[X]`) polynomial in the box has Galois group of order
strictly below `n!`, hence is counted by `E n H`.  This is the "intransitive
case" half of van der Waerden's conjecture, as a *statement about individual
polynomials*: it reduces the counting problem to irreducible polynomials.

As a sanity check we also prove the matching lower bound: the polynomials
`X·g` (`g` running over the `(n-1)`-box) are all bad, so
`(2H+1)^(n-1) ≤ E n H`.
-/

namespace Submission.Vdw

/-- A polynomial is reducible over `ℤ` if it is a product of two monic
polynomials of positive degree. -/
def Reducible (p : ℤ[X]) : Prop :=
  ∃ g h : ℤ[X], g.Monic ∧ h.Monic ∧ 1 ≤ g.natDegree ∧ 1 ≤ h.natDegree ∧ g * h = p

/-- A reducible polynomial of degree `n` has a Galois group of order `< n!`.
Over the integers a monic factorisation `p = g·h` with positive degrees gives
`|Gal(p)| ≤ (deg g)! · (deg h)! < (deg g + deg h)! = n!`. -/
theorem reducible_gal_card_lt (n H : ℕ) (p : ℤ[X]) (hp : p ∈ Box n H) (hred : Reducible p) :
    Nat.card (p.map (algebraMap ℤ ℚ)).Gal < n.factorial := by
  let φ : ℤ →+* ℚ := algebraMap ℤ ℚ
  have hφinj : Function.Injective φ := by
    intro a b h
    change (a : ℚ) = (b : ℚ) at h
    exact_mod_cast h
  have hndp : p.natDegree = n := Polynomial.natDegree_eq_of_degree_eq_some hp.2.1
  obtain ⟨g, h, hgm, hhm, hgd, hhd, hprod⟩ := hred
  have hnd_mul : (g * h).natDegree = g.natDegree + h.natDegree :=
    Polynomial.natDegree_mul (Polynomial.Monic.ne_zero hgm) (Polynomial.Monic.ne_zero hhm)
  have hnd : g.natDegree + h.natDegree = n := by
    calc
      g.natDegree + h.natDegree = (g * h).natDegree := hnd_mul.symm
      _ = p.natDegree := by rw [hprod]
      _ = n := hndp
  have hsub : n - g.natDegree = h.natDegree := by omega
  have hndgm : (g.map φ).natDegree = g.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hφinj g
  have hndhm : (h.map φ).natDegree = h.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hφinj h
  calc
    Nat.card (p.map φ).Gal = Nat.card ((g * h).map φ).Gal := by rw [hprod]
    _ = Nat.card ((g.map φ) * (h.map φ)).Gal := by rw [Polynomial.map_mul]
    _ ≤ Nat.card (g.map φ).Gal * Nat.card (h.map φ).Gal :=
      card_gal_mul_le (g.map φ) (h.map φ)
    _ ≤ g.natDegree.factorial * h.natDegree.factorial := by
      exact Nat.mul_le_mul (by simpa [hndgm] using card_gal_le_factorial (g.map φ))
        (by simpa [hndhm] using card_gal_le_factorial (h.map φ))
    _ = g.natDegree.factorial * (n - g.natDegree).factorial := by rw [hsub]
    _ < n.factorial := by
      have hlt : g.natDegree.factorial * (n - g.natDegree).factorial <
          (g.natDegree + (n - g.natDegree)).factorial :=
        factorial_mul_lt g.natDegree (n - g.natDegree) hgd (by omega)
      have hsum : g.natDegree + (n - g.natDegree) = n := by omega
      simpa [hsum] using hlt

/-- Reducible polynomials in the box are bad, i.e. counted by `E n H`. -/
theorem reducible_mem_Bad (n H : ℕ) (p : ℤ[X]) (hp : p ∈ Box n H) (hred : Reducible p) :
    p ∈ Bad n H := by
  rcases hp with ⟨hpmon, hpdeg, hpbound⟩
  refine ⟨hpmon, hpdeg, hpbound, ?_⟩
  exact reducible_gal_card_lt n H p ⟨hpmon, hpdeg, hpbound⟩ hred

/-- The polynomial `X·g` is monic of degree `deg g + 1` with the same bounded
coefficients (shifted), whenever `g` is a monic bounded polynomial. -/
theorem X_mul_mem_box {n H : ℕ} (g : ℤ[X]) (hg : g ∈ Box (n - 1) H) (hn : 1 ≤ n) :
    X * g ∈ Box n H := by
  rcases hg with ⟨hgm, hgdeg, hgbound⟩
  have hgnd : g.natDegree = n - 1 := Polynomial.natDegree_eq_of_degree_eq_some hgdeg
  refine ⟨?_, ?_, ?_⟩
  · simpa [mul_comm] using hgm.mul Polynomial.monic_X
  · have hXg0 : X * g ≠ 0 := by
      exact mul_ne_zero Polynomial.X_ne_zero (Polynomial.Monic.ne_zero hgm)
    rw [Polynomial.degree_eq_natDegree hXg0]
    have hnd : (X * g).natDegree = n := by
      rw [Polynomial.natDegree_X_mul (Polynomial.Monic.ne_zero hgm), hgnd]
      omega
    rw [hnd]
  · intro i hi
    by_cases hi0 : i = 0
    · subst hi0
      simp
    · have hi1 : 1 ≤ i := by omega
      obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
      subst i
      have hjlt : j < n - 1 := by omega
      rw [Polynomial.coeff_X_mul]
      simpa using hgbound j hjlt

/-- Every polynomial of the form `X·g` with `g` in the `(n-1)`-box is bad for
`n ≥ 2`. -/
theorem X_mul_mem_Bad {n H : ℕ} (g : ℤ[X]) (hg : g ∈ Box (n - 1) H) (hn : 2 ≤ n) :
    X * g ∈ Bad n H := by
  apply reducible_mem_Bad
  · exact X_mul_mem_box g hg (by omega : 1 ≤ n)
  · refine ⟨X, g, Polynomial.monic_X, ?_, ?_, ?_, ?_⟩
    · exact hg.1
    · simp
    · have : g.natDegree = n - 1 := Polynomial.natDegree_eq_of_degree_eq_some hg.2.1
      omega
    · rfl

/-- Multiplication by `X` is injective on polynomials. -/
lemma X_mul_left_injective : Function.Injective (fun p : ℤ[X] => X * p) := by
  intro g h hgh
  apply Polynomial.ext
  intro k
  have hc := congrArg (fun q : ℤ[X] => q.coeff (k + 1)) hgh
  simpa [Polynomial.coeff_X_mul] using hc

/-- The polynomials `X·g` with `g` in the `(n-1)`-box give the
`(2H+1)^(n-1)` lower bound: `E n H` really grows like `H^(n-1)`. -/
theorem E_ge_box_pred (n H : ℕ) (hn : 2 ≤ n) : (2 * H + 1) ^ (n - 1) ≤ E n H := by
  rw [E_eq_ncard_bad]
  let f : ↥(Box (n - 1) H) → ℤ[X] := fun g => X * g.1
  have hf : Function.Injective f := by
    intro g h hgh
    apply Subtype.ext
    exact X_mul_left_injective hgh
  have himage_subset : f '' Set.univ ⊆ Bad n H := by
    intro p hp
    rcases hp with ⟨g, _, rfl⟩
    exact X_mul_mem_Bad g.1 g.2 (by omega : 2 ≤ n)
  have hcard_image : (f '' Set.univ).ncard = (2 * H + 1) ^ (n - 1) := by
    rw [Set.ncard_image_of_injective Set.univ hf, Set.ncard_univ]
    rw [← ncard_eq_natCard (Box (n - 1) H)]
    exact Box_ncard_eq (n - 1) H
  have hBadFin : (Bad n H).Finite := (box_finite n H).subset (Bad_subset_Box n H)
  have hle : (f '' Set.univ).ncard ≤ (Bad n H).ncard :=
    Set.ncard_le_ncard himage_subset hBadFin
  rw [hcard_image] at hle
  exact hle

end Submission.Vdw
