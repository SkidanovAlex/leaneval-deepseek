import Mathlib
import Submission.Commons.NumberTheory.GaussianInt.ncard_factor_set_eq_four
import Submission.Commons.NumberTheory.GaussianInt.fibre_associated_of_norm_coprime
import Submission.Commons.NumberTheory.GaussianInt.factor_exists_of_norm_mul

namespace Commons.NumberTheory.GaussianInt

open Zsqrtd Finset

/-- The imaginary part of a product of Gaussian integers. -/
lemma sumZim_im_mul (a b : GaussianInt) : (a * b).im = a.re * b.im + a.im * b.re :=
  Zsqrtd.im_mul a b

/-- Summing a function of the Gaussian integer `⟨p.1, p.2⟩` over lattice points in the box
`[-N,N]²` with `p.1² + p.2² = N` is the same as summing over the Gaussian integers of
norm `N`. -/
lemma sumZim_targetF_eq_elemF (N : ℕ) (φ : GaussianInt → ℝ) :
    (∑ p ∈ targetF N, φ ⟨p.1, p.2⟩) = ∑ z ∈ elemF N, φ z := by
  rw [elemF]
  exact (Finset.sum_image (f := φ) (s := targetF N)
    (g := fun z : ℤ × ℤ => (⟨z.1, z.2⟩ : GaussianInt)) (by
      intro a _ b _ h
      exact Prod.ext (congrArg Zsqrtd.re h) (congrArg Zsqrtd.im h))).symm

/-- **Counting the fibre of the multiplication map.**  For `m`, `n` coprime and `z` a
Gaussian integer of norm `m * n`, the pairs `(a, b)` with `‖a‖ = m`, `‖b‖ = n` and
`a * b = z` number exactly `4`. -/
lemma sumZim_fibre_card {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hcop : Nat.Coprime m n)
    (z : GaussianInt) (hz : z.norm.natAbs = m * n) :
    (((elemF m) ×ˢ (elemF n)).filter (fun i : GaussianInt × GaussianInt => i.1 * i.2 = z)).card
      = 4 := by
  classical
  have hset : ((((elemF m) ×ˢ (elemF n)).filter
        (fun i : GaussianInt × GaussianInt => i.1 * i.2 = z)) : Set (GaussianInt × GaussianInt))
      = {p : GaussianInt × GaussianInt |
          p.1.norm.natAbs = m ∧ p.2.norm.natAbs = n ∧ p.1 * p.2 = z} := by
    ext p
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨(mem_elemF hm p.1).mp h1, (mem_elemF hn p.2).mp h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨(mem_elemF hm p.1).mpr h1, (mem_elemF hn p.2).mpr h2⟩, h3⟩
  rw [← Set.ncard_coe_finset, hset]
  exact ncard_factor_set_eq_four hm hn hcop z hz

/-- **The multiplication map `elemF m × elemF n → elemF (m*n)` is four-to-one.**  Consequently
summing any function of the product `a * b` over all pairs equals `4` times the sum over the
Gaussian integers of norm `m * n`. -/
lemma sumZim_prod_eq_four_mul {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hcop : Nat.Coprime m n)
    (Z : ℤ → ℝ) :
    (∑ x ∈ (elemF m) ×ˢ (elemF n), Z (x.1 * x.2).im)
      = 4 * ∑ z ∈ elemF (m * n), Z z.im := by
  classical
  have hmn : 1 ≤ m * n := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hmap : ∀ x ∈ (elemF m) ×ˢ (elemF n), x.1 * x.2 ∈ elemF (m * n) := by
    intro x hx
    rw [Finset.mem_product] at hx
    rw [mem_elemF hmn, Zsqrtd.norm_mul, Int.natAbs_mul,
      (mem_elemF hm x.1).mp hx.1, (mem_elemF hn x.2).mp hx.2]
  rw [← Finset.sum_fiberwise_of_maps_to hmap (fun x : GaussianInt × GaussianInt => Z (x.1 * x.2).im),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  have hcard : (((elemF m) ×ˢ (elemF n)).filter
      (fun i : GaussianInt × GaussianInt => i.1 * i.2 = z)).card = 4 :=
    sumZim_fibre_card hm hn hcop z ((mem_elemF hmn z).mp hz)
  have hstep : (∑ i ∈ ((elemF m) ×ˢ (elemF n)).filter
        (fun i : GaussianInt × GaussianInt => i.1 * i.2 = z), Z (i.1 * i.2).im)
      = ∑ _i ∈ ((elemF m) ×ˢ (elemF n)).filter
        (fun i : GaussianInt × GaussianInt => i.1 * i.2 = z), Z z.im := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2]
  rw [hstep, Finset.sum_const, nsmul_eq_mul, hcard]
  norm_num

/-- **Friedlander–Iwaniec, imaginary-part factorisation.**  For coprime `m, n ≥ 1` the sum of
`Z` over the imaginary parts of the Gaussian integers of norm `m * n` (equivalently, over the
lattice points `(x,y)` with `x² + y² = m*n` in `[-mn, mn]²`) equals one quarter of the sum of
`Z` over the imaginary parts `q.1 * r.2 + q.2 * r.1` of the products of pairs of Gaussian
integers of norms `m` and `n` — the factor `1/4` accounting for the four units of `ℤ[i]`. -/
theorem sum_Z_im_factorization {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hcop : Nat.Coprime m n)
    (Z : ℤ → ℝ) :
    (∑ p ∈ (Finset.Icc (-((m * n : ℕ) : ℤ)) ((m * n : ℕ) : ℤ) ×ˢ
              Finset.Icc (-((m * n : ℕ) : ℤ)) ((m * n : ℕ) : ℤ)).filter
            (fun p : ℤ × ℤ => p.1 ^ 2 + p.2 ^ 2 = ((m * n : ℕ) : ℤ)),
          Z p.2)
      = (1 / 4) * (∑ q ∈ (Finset.Icc (-((m : ℕ) : ℤ)) ((m : ℕ) : ℤ) ×ˢ
                Finset.Icc (-((m : ℕ) : ℤ)) ((m : ℕ) : ℤ)).filter
              (fun q : ℤ × ℤ => q.1 ^ 2 + q.2 ^ 2 = ((m : ℕ) : ℤ)),
            ∑ r ∈ (Finset.Icc (-((n : ℕ) : ℤ)) ((n : ℕ) : ℤ) ×ˢ
                Finset.Icc (-((n : ℕ) : ℤ)) ((n : ℕ) : ℤ)).filter
              (fun r : ℤ × ℤ => r.1 ^ 2 + r.2 ^ 2 = ((n : ℕ) : ℤ)),
              Z (q.1 * r.2 + q.2 * r.1)) := by
  have hmn : 1 ≤ m * n := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  change (∑ p ∈ targetF (m * n), Z p.2)
      = (1 / 4) * (∑ q ∈ targetF m, ∑ r ∈ targetF n, Z (q.1 * r.2 + q.2 * r.1))
  have hL : (∑ p ∈ targetF (m * n), Z p.2) = ∑ z ∈ elemF (m * n), Z z.im := by
    simpa using sumZim_targetF_eq_elemF (m * n) (fun z : GaussianInt => Z z.im)
  have hinner : ∀ q : ℤ × ℤ, (∑ r ∈ targetF n, Z (q.1 * r.2 + q.2 * r.1))
      = ∑ r ∈ elemF n, Z (((⟨q.1, q.2⟩ : GaussianInt) * r).im) := by
    intro q
    have h := sumZim_targetF_eq_elemF n
      (fun z : GaussianInt => Z (((⟨q.1, q.2⟩ : GaussianInt) * z).im))
    rw [← h]
    apply Finset.sum_congr rfl
    intro r _
    rw [sumZim_im_mul]
  have hR : (∑ q ∈ targetF m, ∑ r ∈ targetF n, Z (q.1 * r.2 + q.2 * r.1))
      = ∑ x ∈ (elemF m) ×ˢ (elemF n), Z (x.1 * x.2).im := by
    rw [Finset.sum_congr rfl (fun q _ => hinner q)]
    have houter : (∑ q ∈ targetF m, ∑ r ∈ elemF n,
          Z (((⟨q.1, q.2⟩ : GaussianInt) * r).im))
        = ∑ q ∈ elemF m, ∑ r ∈ elemF n, Z ((q * r).im) := by
      have h := sumZim_targetF_eq_elemF m
        (fun a : GaussianInt => ∑ r ∈ elemF n, Z ((a * r).im))
      rw [← h]
    rw [houter]
    rw [Finset.sum_product]
  rw [hL, hR, sumZim_prod_eq_four_mul hm hn hcop Z]
  ring

end Commons.NumberTheory.GaussianInt
