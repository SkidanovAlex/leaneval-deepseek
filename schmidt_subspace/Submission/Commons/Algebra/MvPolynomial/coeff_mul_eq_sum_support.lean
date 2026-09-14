import Mathlib.Algebra.MvPolynomial.Basic

namespace Commons.Algebra.MvPolynomial

theorem coeff_mul_eq_sum_support {K : Type*} [CommSemiring K] {σ : Type*} [DecidableEq σ]
    (P Q : MvPolynomial σ K) (m : σ →₀ ℕ) :
    MvPolynomial.coeff m (P * Q) =
      ∑ p ∈ P.support, MvPolynomial.coeff p P *
        (if p ≤ m then MvPolynomial.coeff (m - p) Q else 0) := by
  classical
  have hmem : ∀ x : (σ →₀ ℕ) × (σ →₀ ℕ),
      x ∈ Finset.HasAntidiagonal.antidiagonal m ↔ x.1 + x.2 = m :=
    fun x => Finset.HasAntidiagonal.mem_antidiagonal
  have hsub : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal m, x.2 = m - x.1 := by
    intro x hx
    rw [hmem] at hx
    exact eq_tsub_of_add_eq (by rw [add_comm]; exact hx)
  have hinj : Set.InjOn Prod.fst
      (↑(Finset.HasAntidiagonal.antidiagonal m) : Set ((σ →₀ ℕ) × (σ →₀ ℕ))) := by
    intro x hx y hy hxy
    simp only [Finset.mem_coe] at hx hy
    exact Prod.ext hxy (by rw [hsub x hx, hsub y hy, hxy])
  have hmem_image : ∀ a : σ →₀ ℕ,
      a ∈ (Finset.HasAntidiagonal.antidiagonal m).image Prod.fst ↔ a ≤ m := by
    intro a
    rw [Finset.mem_image]
    constructor
    · rintro ⟨x, hx, hxa⟩
      rw [hmem] at hx
      rw [← hxa, le_iff_exists_add]
      exact ⟨x.2, hx.symm⟩
    · intro ha
      rw [le_iff_exists_add] at ha
      obtain ⟨c, hc⟩ := ha
      exact ⟨(a, c), by rw [hmem]; exact hc.symm, rfl⟩
  rw [MvPolynomial.coeff_mul]
  have h1 : (∑ x ∈ Finset.HasAntidiagonal.antidiagonal m,
        MvPolynomial.coeff x.1 P * MvPolynomial.coeff x.2 Q)
      = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal m,
        (MvPolynomial.coeff x.1 P * MvPolynomial.coeff (m - x.1) Q) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    rw [hsub x hx]
  rw [h1]
  have h2 : (∑ a ∈ (Finset.HasAntidiagonal.antidiagonal m).image Prod.fst,
        (MvPolynomial.coeff a P * MvPolynomial.coeff (m - a) Q))
      = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal m,
        (MvPolynomial.coeff x.1 P * MvPolynomial.coeff (m - x.1) Q) :=
    Finset.sum_image hinj
  rw [← h2]
  have hR : (∑ p ∈ P.support, MvPolynomial.coeff p P *
        (if p ≤ m then MvPolynomial.coeff (m - p) Q else 0))
      = ∑ p ∈ P.support.filter (fun p => p ≤ m),
        (MvPolynomial.coeff p P * MvPolynomial.coeff (m - p) Q) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro p hp
    rw [mul_ite, mul_zero]
  rw [hR]
  refine (Finset.sum_subset ?_ ?_).symm
  · intro p hp
    rw [Finset.mem_filter] at hp
    rw [hmem_image]
    exact hp.2
  · intro a ha hna
    rw [hmem_image] at ha
    have hnmem : a ∉ P.support := fun h => hna (Finset.mem_filter.mpr ⟨h, ha⟩)
    have hcoeff : MvPolynomial.coeff a P = 0 := by
      by_contra h
      exact hnmem (MvPolynomial.mem_support_iff.mpr h)
    rw [hcoeff, zero_mul]

end Commons.Algebra.MvPolynomial