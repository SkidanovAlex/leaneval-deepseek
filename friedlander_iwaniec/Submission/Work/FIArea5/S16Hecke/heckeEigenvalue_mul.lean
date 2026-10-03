/-
# `Submission.Work.FIArea5.S16Hecke.heckeEigenvalue_mul`

Multiplicativity of the Hecke eigenvalue sum

  `λ_χ,k(m) = ∑_{z primary, |z|² = m} χ(z) (z/|z|)^k`

for `(m, n) = 1`: the primary Gaussian integers of norm `m * n` are exactly the products
`z₁ z₂` of a primary `z₁` of norm `m` with a primary `z₂` of norm `n` (`z ↔ (z₁, z₂)` is a
bijection), and the summand `z ↦ χ(z)(z/|z|)^k` is multiplicative on such pairs: `χ` is
multiplicative and `z ↦ z/|z|` is a multiplicative map because `|z₁z₂| = |z₁||z₂|` and
`√(mn) = √m √n`.  This is the standard multiplicativity of the Hecke eigenvalues `λ(n)`
(paper (23.1), §16).
-/
import Mathlib
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea5.S16Hecke.primaryAux
import Submission.Work.FIArea5.S16Hecke.primaryFactorExists
import Submission.Work.FIArea5.S16Hecke.primaryFactorUnique

set_option autoImplicit false

namespace Work.FIArea5.S16Hecke

open Finset
open scoped BigOperators
open Work.FIPlan

noncomputable section

/-- The summand `z ↦ χ(z) (z/|z|)^k` is multiplicative on primary arguments of norms `m`, `n`. -/
theorem summand_mul (chi : GaussianInt → ℂ) (k : ℤ)
    (hchi : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w)
    {m n : ℕ} (z1 z2 : GaussianInt) (h1 : gnorm z1 = m) (h2 : gnorm z2 = n) :
    chi (z1 * z2) * ((z1 * z2).toComplex / ((Real.sqrt (gnorm (z1 * z2) : ℝ) : ℂ))) ^ k
      = (chi z1 * (z1.toComplex / ((Real.sqrt (gnorm z1 : ℝ) : ℂ))) ^ k)
        * (chi z2 * (z2.toComplex / ((Real.sqrt (gnorm z2 : ℝ) : ℂ))) ^ k) := by
  have hbase : (z1 * z2).toComplex / ((Real.sqrt (gnorm (z1 * z2) : ℝ) : ℂ))
      = (z1.toComplex / ((Real.sqrt (gnorm z1 : ℝ) : ℂ)))
        * (z2.toComplex / ((Real.sqrt (gnorm z2 : ℝ) : ℂ))) := by
    rw [GaussianInt.toComplex_mul, gnorm_mul, h1, h2, Nat.cast_mul,
      Real.sqrt_mul (Nat.cast_nonneg m), Complex.ofReal_mul, ← div_mul_div_comm]
  rw [hbase, hchi z1 z2, mul_zpow]
  ring

theorem heckeEigenvalue_mul (chi : GaussianInt → ℂ) (k : ℤ) (m n : ℕ)
    [DecidablePred fun z : GaussianInt => Work.FIPlan.IsPrimary z ∧ Work.FIPlan.gnorm z = m * n]
    [DecidablePred fun z : GaussianInt => Work.FIPlan.IsPrimary z ∧ Work.FIPlan.gnorm z = m]
    [DecidablePred fun z : GaussianInt => Work.FIPlan.IsPrimary z ∧ Work.FIPlan.gnorm z = n]
    (hchi : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w)
    (hm : 0 < m) (hn : 0 < n) (hcop : Nat.Coprime m n) :
    (∑ z ∈ (Work.FIPlan.gBox ((m * n : ℕ) : ℤ)).filter
          (fun z => Work.FIPlan.IsPrimary z ∧ Work.FIPlan.gnorm z = m * n),
        chi z * (z.toComplex / ((Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ))) ^ k)
      = (∑ z ∈ (Work.FIPlan.gBox ((m : ℕ) : ℤ)).filter
            (fun z => Work.FIPlan.IsPrimary z ∧ Work.FIPlan.gnorm z = m),
          chi z * (z.toComplex / ((Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ))) ^ k)
        * (∑ z ∈ (Work.FIPlan.gBox ((n : ℕ) : ℤ)).filter
            (fun z => Work.FIPlan.IsPrimary z ∧ Work.FIPlan.gnorm z = n),
          chi z * (z.toComplex / ((Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ))) ^ k) := by
  let F : GaussianInt → ℂ := fun z => chi z * (z.toComplex / ((Real.sqrt (gnorm z : ℝ) : ℂ))) ^ k
  let Sm : Finset GaussianInt := (gBox ((m : ℕ) : ℤ)).filter (fun z => IsPrimary z ∧ gnorm z = m)
  let Sn : Finset GaussianInt := (gBox ((n : ℕ) : ℤ)).filter (fun z => IsPrimary z ∧ gnorm z = n)
  let Smn : Finset GaussianInt :=
    (gBox ((m * n : ℕ) : ℤ)).filter (fun z => IsPrimary z ∧ gnorm z = m * n)
  have hSm : Sm = (gBox ((m : ℕ) : ℤ)).filter (fun z => IsPrimary z ∧ gnorm z = m) := rfl
  have hSn : Sn = (gBox ((n : ℕ) : ℤ)).filter (fun z => IsPrimary z ∧ gnorm z = n) := rfl
  have hSmn : Smn = (gBox ((m * n : ℕ) : ℤ)).filter
      (fun z => IsPrimary z ∧ gnorm z = m * n) := rfl
  have hbij : (∑ p ∈ Sm ×ˢ Sn, F p.1 * F p.2) = ∑ z ∈ Smn, F z := by
    refine Finset.sum_bij (fun p _ => p.1 * p.2) ?_ ?_ ?_ ?_
    · rintro ⟨z1, z2⟩ hp
      rw [Finset.mem_product] at hp
      obtain ⟨hp1, hp2⟩ := hp
      rw [hSm, Finset.mem_filter] at hp1
      rw [hSn, Finset.mem_filter] at hp2
      obtain ⟨-, hP1, hg1⟩ := hp1
      obtain ⟨-, hP2, hg2⟩ := hp2
      rw [hSmn, Finset.mem_filter]
      refine ⟨?_, isPrimary_mul hP1 hP2, ?_⟩
      · refine mem_gBox_of_gnorm_le (by exact_mod_cast Nat.mul_pos hm hn) ?_
        rw [gnorm_mul, hg1, hg2]
      · rw [gnorm_mul, hg1, hg2]
    · rintro ⟨z1, z2⟩ hp1 ⟨z1', z2'⟩ hp2 h
      rw [Finset.mem_product] at hp1 hp2
      obtain ⟨hp11, hp12⟩ := hp1
      obtain ⟨hp21, hp22⟩ := hp2
      rw [hSm, Finset.mem_filter] at hp11 hp21
      rw [hSn, Finset.mem_filter] at hp12 hp22
      obtain ⟨-, hP11, hg11⟩ := hp11
      obtain ⟨-, hP12, hg12⟩ := hp12
      obtain ⟨-, hP21, hg21⟩ := hp21
      obtain ⟨-, hP22, hg22⟩ := hp22
      have hz1 : z1 = z1' :=
        primaryFactorUnique hm hn hcop hP11 hP12 hP21 hP22 hg11 hg21 hg12 hg22 h
      have hz1ne : z1 ≠ 0 := by
        intro h0
        rw [h0] at hg11
        simp [gnorm] at hg11
        omega
      have hz2 : z2 = z2' := by
        rw [← hz1] at h
        exact mul_left_cancel₀ hz1ne h
      rw [hz1, hz2]
    · intro z hz
      rw [hSmn, Finset.mem_filter] at hz
      obtain ⟨-, hzP, hzg⟩ := hz
      obtain ⟨z1, z2, hP1, hP2, hg1, hg2, heq⟩ := primaryFactorExists hzP hzg hm hn hcop
      refine ⟨(z1, z2), ?_, heq.symm⟩
      rw [Finset.mem_product]
      constructor
      · rw [hSm, Finset.mem_filter]
        exact ⟨mem_gBox_of_gnorm_le (by exact_mod_cast hm) (by rw [hg1]), hP1, hg1⟩
      · rw [hSn, Finset.mem_filter]
        exact ⟨mem_gBox_of_gnorm_le (by exact_mod_cast hn) (by rw [hg2]), hP2, hg2⟩
    · rintro ⟨z1, z2⟩ hp
      rw [Finset.mem_product] at hp
      obtain ⟨hp1, hp2⟩ := hp
      rw [hSm, Finset.mem_filter] at hp1
      rw [hSn, Finset.mem_filter] at hp2
      obtain ⟨-, hP1, hg1⟩ := hp1
      obtain ⟨-, hP2, hg2⟩ := hp2
      show F z1 * F z2 = F (z1 * z2)
      exact (summand_mul chi k hchi z1 z2 hg1 hg2).symm
  have hgoal : (∑ z ∈ Smn, F z) = (∑ z ∈ Sm, F z) * (∑ z ∈ Sn, F z) := by
    rw [Finset.sum_mul_sum, ← Finset.sum_product Sm Sn (fun p : GaussianInt × GaussianInt => F p.1 * F p.2)]
    exact hbij.symm
  exact hgoal

end

end Work.FIArea5.S16Hecke
