import Mathlib
import Submission.Subspace.RothHeight
import Submission.Commons.NumberTheory.Height.MvPolynomial.polyHeight_finset_prod_le
import Submission.Commons.Algebra.MvPolynomial.pderivIter_map
import Submission.Commons.Algebra.MvPolynomial.coeff_pderivIter
import Submission.Commons.NumberTheory.Height.mulHeight_finsupp_coe_eq

/-!
# The height of the Wronskian determinant

For `P ∈ ℤ[x_0, …, x_n]` with `deg_{x_j} P ≤ r_j` and multi-indices `μ_i` we bound the height of
the Wronskian determinant `V = det (∂^{μ_i + j e_0} P)_{i,j}` by `k · hZ P + (explicit loss)`.
The loss consists of the `log (k !)` of the determinant expansion, the `k · Σ r_j` of the sharp
product bound, and the `2 k² log D` of the iterated derivatives.
-/

open scoped BigOperators

namespace Submission.Subspace

open MvPolynomial
open Commons.NumberTheory.Height.MvPolynomial (gP)

variable {σ : Type*}

lemma hZ_eq (P : MvPolynomial σ ℤ) :
    hZ P = Height.logHeight (gP (P.map (Int.castRingHom ℚ))) := rfl

/-- The height of `gP Q` is at least `1` (the tuple contains the value `1`). -/
lemma one_le_mulHeight_gP (Q : MvPolynomial σ ℚ) : 1 ≤ Height.mulHeight (gP Q) := by
  classical
  have hvan : ∀ i, i ∉ (insert none (Q.support.image some) : Finset (Option (σ →₀ ℕ))) →
      gP Q i = 0 := by
    intro i hi
    rw [Finset.mem_insert] at hi
    push_neg at hi
    obtain ⟨h1, h2⟩ := hi
    cases i with
    | none => exact absurd rfl h1
    | some m =>
      simp only [gP, Option.elim_some]
      exact not_ne_iff.mp fun hc =>
        h2 (Finset.mem_image.mpr ⟨m, MvPolynomial.mem_support_iff.mpr hc, rfl⟩)
  rw [Commons.NumberTheory.Height.mulHeight_eq_mulHeight_finset _ hvan]
  exact Height.one_le_mulHeight _

lemma logHeight_gP_nonneg (Q : MvPolynomial σ ℚ) : 0 ≤ Height.logHeight (gP Q) :=
  Real.log_nonneg (one_le_mulHeight_gP Q)

/-- The support degree bound is inherited by iterated partial derivatives. -/
lemma support_pderivIter_degree_le [Fintype σ] (ν : σ →₀ ℕ) (P : MvPolynomial σ ℤ) (r : σ → ℕ)
    (h : ∀ t ∈ P.support, ∀ j, t j ≤ r j) :
    ∀ t ∈ (Commons.Algebra.MvPolynomial.pderivIter ν P).support, ∀ j, t j ≤ r j := by
  intro t ht j
  rw [MvPolynomial.mem_support_iff] at ht
  rw [Commons.Algebra.MvPolynomial.coeff_pderivIter] at ht
  by_contra hlt
  push_neg at hlt
  have hnot : t + ν ∉ P.support := by
    intro hmem
    exact absurd (h (t + ν) hmem j) (by rw [Finsupp.add_apply]; omega)
  rw [MvPolynomial.notMem_support_iff.mp hnot, zero_mul] at ht
  exact ht rfl

/-- Height of an iterated partial derivative of an integer polynomial. -/
lemma hZ_pderivIter_le [Fintype σ] (ν : σ →₀ ℕ) (P : MvPolynomial σ ℤ) (D : ℕ) (hD : 1 ≤ D)
    (hdeg : ∀ t ∈ P.support, t.sum (fun _ k => k) ≤ D) :
    hZ (Commons.Algebra.MvPolynomial.pderivIter ν P) ≤
      hZ P + (ν.sum (fun _ k => k) : ℝ) * Real.log D := by
  have hsupp : ∀ t ∈ (P.map (Int.castRingHom ℚ)).support, t.sum (fun _ k => k) ≤ D := by
    intro t ht
    rw [MvPolynomial.mem_support_iff] at ht
    rw [MvPolynomial.coeff_map] at ht
    have : MvPolynomial.coeff t P ≠ 0 := fun h0 => ht (by rw [h0]; simp)
    exact hdeg t (MvPolynomial.mem_support_iff.mpr this)
  have h := Commons.NumberTheory.Height.MvPolynomial.polyHeight_pderivIter_le D hD ν
    (P.map (Int.castRingHom ℚ)) hsupp
  rw [hZ_eq, hZ_eq, ← Commons.Algebra.MvPolynomial.pderivIter_map]
  exact h

/-- Height of a product of integer polynomials in terms of the individual heights. -/
lemma hZ_prod_le [Fintype σ] {ι : Type*} [Fintype ι] (A : ι → MvPolynomial σ ℤ) (d : σ → ℕ)
    (hd : ∀ i, ∀ t ∈ (A i).support, ∀ j, t j ≤ d j) :
    hZ (∏ i, A i) ≤ (∑ i, hZ (A i)) +
      (((Fintype.card ι * (∑ j, d j) + Fintype.card σ * (Fintype.card ι - 1) : ℕ) : ℝ) *
        Real.log 2) := by
  have hd' : ∀ i, ∀ t ∈ ((A i).map (Int.castRingHom ℚ)).support, ∀ j, t j ≤ d j := by
    intro i t ht j
    rw [MvPolynomial.mem_support_iff] at ht
    rw [MvPolynomial.coeff_map] at ht
    have : MvPolynomial.coeff t (A i) ≠ 0 := fun h0 => ht (by rw [h0]; simp)
    exact hd i t (MvPolynomial.mem_support_iff.mpr this) j
  have h := Commons.NumberTheory.Height.MvPolynomial.polyHeight_finset_prod_le
    (fun i => (A i).map (Int.castRingHom ℚ)) d hd'
  simp only [hZ_eq, map_prod] at h ⊢
  exact h


section Wronskian

open scoped Matrix

/-- The multi-index `μ_i` pushed to the `x_1,…,x_n` coordinates, plus `j` in the `x_0` coordinate,
has total degree `|μ_i| + j`. -/
lemma sum_mapDomain_succ_add_smul_single (n : ℕ) (μ : Fin n →₀ ℕ) (j : ℕ) :
    ((μ.mapDomain Fin.succ + (j : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1).sum
      (fun _ m => (m : ℝ))) = (μ.sum (fun _ m => (m : ℝ))) + j := by
  simp [Finsupp.sum_add_index', Finsupp.sum_mapDomain_index]

/-- Height of the Wronskian determinant of an integer polynomial. -/
theorem hZ_wronskian_det_le {n k : ℕ} (P : MvPolynomial (Fin (n + 1)) ℤ) (r : Fin (n + 1) → ℕ)
    (D : ℕ) (hD : 1 ≤ D) (hdeg : ∀ t ∈ P.support, ∀ j, t j ≤ r j)
    (htot : ∀ t ∈ P.support, t.sum (fun _ m => m) ≤ D)
    (μ : Fin k → Fin n →₀ ℕ) (hμ : ∀ i, (μ i).sum (fun _ m => m) ≤ (i : ℕ)) :
    hZ (Matrix.of (fun i j : Fin k =>
        Commons.Algebra.MvPolynomial.pderivIter ((μ i).mapDomain Fin.succ +
          (j : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1) P)).det ≤
      (k : ℝ) * hZ P + (2 * (k : ℝ) ^ 2 * Real.log D +
        ((k * (∑ j, r j) + (n + 1) * (k - 1) : ℕ) : ℝ) * Real.log 2 +
        Real.log (Nat.factorial k)) := by
  classical
  set H : ℝ := hZ P + 2 * k * Real.log D with hHdef
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg (by exact_mod_cast hD)
  have hHP : 0 ≤ hZ P := by
    rw [hZ_eq]; exact logHeight_gP_nonneg _
  have hH0 : 0 ≤ H := by
    rw [hHdef]; positivity
  -- bound on a single entry
  have hentry : ∀ (i j : Fin k), hZ (Commons.Algebra.MvPolynomial.pderivIter
      ((μ i).mapDomain Fin.succ + (j : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1) P) ≤ H := by
    intro i j
    have h := hZ_pderivIter_le ((μ i).mapDomain Fin.succ +
      (j : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1) P D hD htot
    have hsum : ((μ i).mapDomain Fin.succ + (j : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1).sum
        (fun _ m => (m : ℝ)) ≤ ((2 * k : ℕ) : ℝ) := by
      rw [sum_mapDomain_succ_add_smul_single]
      have hsum_i : (μ i).sum (fun _ m => (m : ℝ)) ≤ (i : ℝ) := by exact_mod_cast hμ i
      have hi : (i : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.le_of_lt i.isLt
      have hj : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.le_of_lt j.isLt
      push_cast
      linarith
    calc hZ (Commons.Algebra.MvPolynomial.pderivIter _ P)
        ≤ hZ P + ((μ i).mapDomain Fin.succ + (j : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1).sum
            (fun _ m => (m : ℝ)) * Real.log D := h
      _ ≤ hZ P + 2 * k * Real.log D := by
          have := mul_le_mul_of_nonneg_right hsum hlogD
          push_cast at this ⊢
          linarith
      _ = H := hHdef
  -- bound on the products
  have hprod : ∀ π : Equiv.Perm (Fin k),
      hZ (Finset.univ.prod fun i => Commons.Algebra.MvPolynomial.pderivIter
        ((μ (π i)).mapDomain Fin.succ + (i : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1) P)
        ≤ H * k + ((k * (∑ j, r j) + (n + 1) * (k - 1) : ℕ) : ℝ) * Real.log 2 := by
    intro π
    have hd : ∀ i : Fin k, ∀ t ∈ (Commons.Algebra.MvPolynomial.pderivIter
        ((μ (π i)).mapDomain Fin.succ + (i : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1) P).support,
        ∀ j, t j ≤ r j := fun i => support_pderivIter_degree_le _ P r hdeg
    have h := hZ_prod_le (σ := Fin (n + 1)) (fun i : Fin k =>
        Commons.Algebra.MvPolynomial.pderivIter ((μ (π i)).mapDomain Fin.succ +
          (i : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1) P) r hd
    have hsum2 : (∑ i : Fin k, hZ (Commons.Algebra.MvPolynomial.pderivIter
        ((μ (π i)).mapDomain Fin.succ + (i : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1) P)) ≤
        (k : ℝ) * H := by
      calc (∑ i : Fin k, hZ (Commons.Algebra.MvPolynomial.pderivIter
            ((μ (π i)).mapDomain Fin.succ + (i : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1) P))
          ≤ ∑ _i : Fin k, H := Finset.sum_le_sum fun i _ => hentry (π i) i
        _ = (k : ℝ) * H := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
    have hcard : ((Fintype.card (Fin k) * (∑ j, r j) + Fintype.card (Fin (n + 1)) *
        (Fintype.card (Fin k) - 1) : ℕ) : ℝ) * Real.log 2 =
        ((k * (∑ j, r j) + (n + 1) * (k - 1) : ℕ) : ℝ) * Real.log 2 := by
      simp only [Fintype.card_fin]
    rw [hcard] at h
    linarith [h, hsum2]
  have hA : ∀ i j : Fin k, hZ (Commons.Algebra.MvPolynomial.pderivIter
      ((μ i).mapDomain Fin.succ + (j : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1) P) ≤ H := hentry
  have hmain := hZ_det_le (σ := Fin (n + 1)) (A := Matrix.of (fun i j : Fin k =>
      Commons.Algebra.MvPolynomial.pderivIter ((μ i).mapDomain Fin.succ +
        (j : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1) P)) H
    (((k * (∑ j, r j) + (n + 1) * (k - 1) : ℕ) : ℝ) * Real.log 2) hH0 (by positivity)
    (fun π => hprod π)
  have hkR : H * (k : ℝ) = (k : ℝ) * hZ P + 2 * (k : ℝ) ^ 2 * Real.log D := by
    rw [hHdef]; ring
  rw [hkR] at hmain
  linarith [hmain]

end Wronskian

end Submission.Subspace
