import Mathlib
import Submission.Work.FIArea7.prop232Defs
import Submission.Work.FIArea5.S16Hecke.primaryFactorExists
import Submission.Work.FIArea5.S16Hecke.primaryFactorUnique
import Submission.Work.FITop3.Witness.exists_primary_norm

namespace Work.FIArea7

/-- The product map `(w, z) ↦ w * z` sends `primarySet m × primarySet n` into `primarySet (m * n)`
when `m, n ≥ 1` (no coprimality needed): `IsPrimary` and `gnorm` are multiplicative. -/
lemma mul_mem_primarySet_mul {m n : ℕ} {w z : GaussianInt}
    (hw : w ∈ primarySet m) (hz : z ∈ primarySet n) : w * z ∈ primarySet (m * n) := by
  rw [mem_primarySet] at hw hz ⊢
  exact ⟨Work.FITop3.Witness.isPrimary_mul hw.1 hz.1,
    by rw [Work.FITop3.Witness.gnorm_mul, hw.2, hz.2]⟩

/-- The product map `(w, z) ↦ w * z` is injective on `primarySet m × primarySet n` for coprime
`m, n ≥ 1`. -/
lemma mul_injOn_primarySet {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hcop : Nat.Coprime m n)
    {w z w' z' : GaussianInt} (hw : w ∈ primarySet m) (hz : z ∈ primarySet n)
    (hw' : w' ∈ primarySet m) (hz' : z' ∈ primarySet n) (h : w * z = w' * z') : w = w' ∧ z = z' := by
  rw [mem_primarySet] at hw hz hw' hz'
  have hw_eq : w = w' :=
    Work.FIArea5.S16Hecke.primaryFactorUnique hm hn hcop
      hw.1 hz.1 hw'.1 hz'.1 hw.2 hw'.2 hz.2 hz'.2 h
  have hwne : w ≠ 0 := by
    intro h0
    rw [h0] at hw
    simp [Work.FIPlan.gnorm] at hw
    omega
  have hz_eq : z = z' := by
    rw [← hw_eq] at h
    exact mul_left_cancel₀ hwne h
  exact ⟨hw_eq, hz_eq⟩

/-- **Regrouping the primary-fibre sum along coprime factorisations of the norm.**
For `m, n ≥ 1` coprime, the map `(w, z) ↦ w * z` is a bijection from
`primarySet m × primarySet n` onto `primarySet (m * n)`; hence for *any* `F : ℤ[i] → ℂ`

  `∑_{e ∈ primarySet (m*n)} F e = ∑_{w ∈ primarySet m} ∑_{z ∈ primarySet n} F (w * z)`.

The two halves of the bijection are already proved in this workspace:
* surjectivity — `Work.FIArea5.S16Hecke.primaryFactorExists` (every primary `e` of norm `m*n` is
  `e = z₁ * z₂` with `z₁, z₂` primary of norms `m`, `n`);
* injectivity — `Work.FIArea5.S16Hecke.primaryFactorUnique` (`z₁ * z₂ = z₁' * z₂'` forces
  `z₁ = z₁'`, hence `z₂ = z₂'` by cancelling `z₁ ≠ 0`).
To land in `primarySet (m * n)` one uses `Work.FITop3.Witness.isPrimary_mul`,
`Work.FITop3.Witness.gnorm_mul` and `Work.FIArea7.mem_gBox_of_gnorm_eq`; the assembly is
`Finset.sum_bij`.  The degenerate case `primarySet m = ∅` needs no case split: then the right side
is `0` and, by surjectivity, so is the left side. -/
lemma sum_primarySet_mul {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hcop : Nat.Coprime m n)
    (F : GaussianInt → ℂ) :
    ∑ e ∈ Work.FIArea7.primarySet (m * n), F e
      = ∑ w ∈ Work.FIArea7.primarySet m, ∑ z ∈ Work.FIArea7.primarySet n, F (w * z) := by
  classical
  have hm0 : 0 < m := hm
  have hn0 : 0 < n := hn
  -- the double sum is the sum over the product of the two fibres
  have hprod : (∑ p ∈ primarySet m ×ˢ primarySet n, F (p.1 * p.2))
      = ∑ w ∈ primarySet m, ∑ z ∈ primarySet n, F (w * z) := by
    rw [Finset.sum_product]
  -- the product map is a bijection onto `primarySet (m * n)`
  have hbij : (∑ p ∈ primarySet m ×ˢ primarySet n, F (p.1 * p.2))
      = ∑ e ∈ primarySet (m * n), F e := by
    refine Finset.sum_bij (fun (p : GaussianInt × GaussianInt) _ => p.1 * p.2) ?_ ?_ ?_ ?_
    · rintro ⟨z1, z2⟩ hp
      rw [Finset.mem_product] at hp
      exact mul_mem_primarySet_mul hp.1 hp.2
    · rintro ⟨z1, z2⟩ hp1 ⟨z1', z2'⟩ hp2 h
      rw [Finset.mem_product] at hp1 hp2
      obtain ⟨h1, h2⟩ := mul_injOn_primarySet hm0 hn0 hcop hp1.1 hp1.2 hp2.1 hp2.2 h
      exact Prod.ext h1 h2
    · intro e he
      rw [mem_primarySet] at he
      obtain ⟨z1, z2, hP1, hP2, hg1, hg2, heq⟩ :=
        Work.FIArea5.S16Hecke.primaryFactorExists he.1 he.2 hm0 hn0 hcop
      refine ⟨(z1, z2), ?_, heq.symm⟩
      rw [Finset.mem_product, mem_primarySet, mem_primarySet]
      exact ⟨⟨hP1, hg1⟩, ⟨hP2, hg2⟩⟩
    · rintro ⟨z1, z2⟩ hp
      rfl
  rw [← hprod, hbij]

end Work.FIArea7
