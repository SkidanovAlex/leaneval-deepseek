import Mathlib
import Submission.Work.LinnikAreas.Density4.MuSqTotientDefs

/-!
# Reindexing the Mertens weight `hh` over squarefree radix

The weight `hh n = cw n * μ(n / rad n)` is supported on the numbers whose
`p`-adic valuation is at most `2`; each such `n` factors uniquely as `n = u * v`
with `u = rad n` squarefree and `v = n / rad n`, and on that pair
`hh (u*v) = cw u * μ v`.

This file proves the corresponding reindexing identity

`∑_{e ≤ N} hh e · f e = ∑_{u ≤ N, u squarefree} cw u · ∑_{v ∣ u, uv ≤ N} μ v · f (u·v)`

which converts a sum over all `e ≤ N` into a sum over squarefree `u` weighted by
`cw u` and over squarefree divisors `v` of `u`, weighted by `μ v`.
-/

open Finset BigOperators

namespace Work.LinnikAreas.Density4

noncomputable section

/-- The radical `rad n` is positive. -/
lemma rad_pos (n : ℕ) : 0 < rad n := by
  rw [rad]; exact Finset.prod_pos (fun p hp => Nat.pos_of_mem_primeFactors hp)

/-- The radical `rad n` is nonzero. -/
lemma rad_ne_zero (n : ℕ) : rad n ≠ 0 := ne_of_gt (rad_pos n)

/-- The radical of any number is squarefree. -/
lemma rad_squarefree (n : ℕ) : Squarefree (rad n) := by
  rw [rad]
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro a ha b hb hab
    simp only [Function.onFun]
    exact (Nat.coprime_iff_isRelPrime).mp
      ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors ha)
        (Nat.prime_of_mem_primeFactors hb)).mpr hab)
  · intro p hp
    exact (Nat.Prime.prime (Nat.prime_of_mem_primeFactors hp)).squarefree

/-- `rad` divides its argument. -/
lemma rad_dvd (n : ℕ) : rad n ∣ n := Nat.prod_primeFactors_dvd n

/-- `rad n * (n / rad n) = n`. -/
lemma rad_mul_div (n : ℕ) : rad n * (n / rad n) = n := Nat.mul_div_cancel' (rad_dvd n)

/-- For squarefree `u` and `v ∣ u`, the radical of `u*v` is `u`. -/
lemma rad_mul_of_squarefree_dvd (u v : ℕ) (hu : Squarefree u) (hv : v ∣ u) :
    rad (u * v) = u := by
  have hu0 : u ≠ 0 := hu.ne_zero
  have hv0 : v ≠ 0 := fun h => hu0 (Nat.eq_zero_of_zero_dvd (h ▸ hv))
  have hsub : v.primeFactors ⊆ u.primeFactors := Nat.primeFactors_mono hv hu0
  have hpf : (u * v).primeFactors = u.primeFactors := by
    rw [Nat.primeFactors_mul hu0 hv0, Finset.union_eq_left]
    exact hsub
  rw [rad, hpf, Nat.prod_primeFactors_of_squarefree hu]

/-- If `e / rad e` is squarefree then it divides `rad e`. -/
lemma div_rad_dvd_rad (e : ℕ) (h : Squarefree (e / rad e)) : e / rad e ∣ rad e := by
  have hvd : e / rad e ∣ e := Nat.div_dvd_of_dvd (rad_dvd e)
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [rad, Nat.primeFactors_zero, Finset.prod_empty, Nat.zero_div] at h
    exact not_squarefree_zero h
  have hsub : (e / rad e).primeFactors ⊆ e.primeFactors := Nat.primeFactors_mono hvd he0
  have h1 : rad (e / rad e) ∣ rad e := by
    rw [rad, rad]
    exact Finset.prod_dvd_prod_of_subset _ _ (fun p => p) hsub
  have h2 : rad (e / rad e) = e / rad e := by
    rw [rad]; exact Nat.prod_primeFactors_of_squarefree h
  rwa [h2] at h1

theorem hh_reindex (N : ℕ) (f : ℕ → ℝ) :
    (∑ e ∈ Finset.Icc 1 N, hh e * f e)
      = ∑ u ∈ (Finset.Icc 1 N).filter Squarefree,
          cw u * ∑ v ∈ u.divisors.filter (fun v => u * v ≤ N),
            ((ArithmeticFunction.moebius v : ℤ) : ℝ) * f (u * v) := by
  classical
  -- The left-hand sum may be restricted to the `e` with `e / rad e` squarefree,
  -- because `hh e = cw e · μ (e / rad e)` vanishes otherwise.
  have hzero : ∀ e ∈ Finset.Icc 1 N, ¬ Squarefree (e / rad e) → hh e * f e = 0 := by
    intro e _ h
    have : hh e = 0 := by
      rw [hh, ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]; simp
    rw [this, zero_mul]
  have step1 : (∑ e ∈ Finset.Icc 1 N, hh e * f e)
      = ∑ e ∈ (Finset.Icc 1 N).filter (fun e => Squarefree (e / rad e)), hh e * f e := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun e he => ?_)
    by_cases h : Squarefree (e / rad e)
    · simp [h]
    · simp [h, hzero e he h]
  -- Abbreviations for the reindexing: `Sig` is the set of pairs `(u, v)` with
  -- `u ≤ N` squarefree and `v ∣ u`, `u * v ≤ N`; `F (u,v) = u*v` maps it bijectively
  -- onto the `e` with `e / rad e` squarefree.
  let Sig : Finset (Sigma (fun _ : ℕ => ℕ)) :=
    ((Finset.Icc 1 N).filter Squarefree).sigma
      (fun u => u.divisors.filter (fun v => u * v ≤ N))
  let F : Sigma (fun _ : ℕ => ℕ) → ℕ := fun x => x.1 * x.2
  let Ψ : Sigma (fun _ : ℕ => ℕ) → ℝ :=
    fun x => cw x.1 * (((ArithmeticFunction.moebius x.2 : ℤ) : ℝ) * f (x.1 * x.2))
  -- Turn the right-hand side into a sum over the sigma-type index set.
  have hdouble : (∑ u ∈ (Finset.Icc 1 N).filter Squarefree,
          cw u * ∑ v ∈ u.divisors.filter (fun v => u * v ≤ N),
            ((ArithmeticFunction.moebius v : ℤ) : ℝ) * f (u * v))
        = ∑ x ∈ Sig, Ψ x := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_sigma'
      (s := (Finset.Icc 1 N).filter Squarefree)
      (t := fun u => u.divisors.filter (fun v => u * v ≤ N))
      (f := fun u v => cw u * (((ArithmeticFunction.moebius v : ℤ) : ℝ) * f (u * v)))]
  -- On each pair, `Ψ` equals the corresponding left-hand summand.
  have hpoint : ∀ x ∈ Sig, Ψ x = hh (F x) * f (F x) := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_sigma.mp hx
    have hSq : Squarefree x.1 := (Finset.mem_filter.mp hx1).2
    have hdvd : x.2 ∣ x.1 := (Nat.mem_divisors.mp (Finset.mem_filter.mp hx2).1).1
    rw [show Ψ x = cw x.1 * (((ArithmeticFunction.moebius x.2 : ℤ) : ℝ) * f (x.1 * x.2)) from rfl]
    rw [show hh (F x) * f (F x) = hh (x.1 * x.2) * f (x.1 * x.2) from rfl]
    rw [hh_sqfree_dvd x.1 x.2 hSq hdvd]
    ring
  -- `F` is injective on `Sig`.
  have hinj : Set.InjOn F ↑Sig := by
    intro a ha b hb hab
    obtain ⟨ha1, ha2⟩ := Finset.mem_sigma.mp ha
    obtain ⟨hb1, hb2⟩ := Finset.mem_sigma.mp hb
    have hSa : Squarefree a.1 := (Finset.mem_filter.mp ha1).2
    have hSb : Squarefree b.1 := (Finset.mem_filter.mp hb1).2
    have hda : a.2 ∣ a.1 := (Nat.mem_divisors.mp (Finset.mem_filter.mp ha2).1).1
    have hdb : b.2 ∣ b.1 := (Nat.mem_divisors.mp (Finset.mem_filter.mp hb2).1).1
    change a.1 * a.2 = b.1 * b.2 at hab
    have hra : rad (a.1 * a.2) = a.1 := rad_mul_of_squarefree_dvd a.1 a.2 hSa hda
    have hrb : rad (b.1 * b.2) = b.1 := rad_mul_of_squarefree_dvd b.1 b.2 hSb hdb
    have hu : a.1 = b.1 := by rw [← hra, hab, hrb]
    have hv : a.2 = b.2 := by
      apply Nat.mul_left_cancel (Nat.pos_of_ne_zero hSa.ne_zero)
      rw [hab, ← hu]
    exact Sigma.ext hu (heq_of_eq hv)
  -- The image of `F` is exactly the `e ≤ N` with `e / rad e` squarefree.
  have himg : Sig.image F = (Finset.Icc 1 N).filter (fun e => Squarefree (e / rad e)) := by
    ext x
    rw [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨a, ha, hax⟩
      obtain ⟨ha1, ha2⟩ := Finset.mem_sigma.mp ha
      have hSq : Squarefree a.1 := (Finset.mem_filter.mp ha1).2
      have hleN : a.1 * a.2 ≤ N := (Finset.mem_filter.mp ha2).2
      have hdvd : a.2 ∣ a.1 := (Nat.mem_divisors.mp (Finset.mem_filter.mp ha2).1).1
      have ha10 : a.1 ≠ 0 := (Nat.mem_divisors.mp (Finset.mem_filter.mp ha2).1).2
      have ha20 : a.2 ≠ 0 := fun h => ha10 (Nat.eq_zero_of_zero_dvd (h ▸ hdvd))
      rw [← hax]
      refine ⟨⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero ha10 ha20), hleN⟩, ?_⟩
      rw [rad_mul_of_squarefree_dvd a.1 a.2 hSq hdvd,
        Nat.mul_div_right a.2 (Nat.pos_of_ne_zero ha10)]
      exact Squarefree.squarefree_of_dvd hdvd hSq
    · intro hx
      obtain ⟨⟨hx1, hxN⟩, hxsq⟩ := hx
      have hx0 : x ≠ 0 := Nat.one_le_iff_ne_zero.mp hx1
      refine ⟨(⟨rad x, x / rad x⟩ : Sigma (fun _ : ℕ => ℕ)), ?_, ?_⟩
      · rw [Finset.mem_sigma]
        constructor
        · rw [Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (rad_ne_zero x),
            le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hx0) (rad_dvd x)) hxN⟩,
            rad_squarefree x⟩
        · rw [Finset.mem_filter]
          exact ⟨Nat.mem_divisors.mpr ⟨div_rad_dvd_rad x hxsq, rad_ne_zero x⟩,
            by rw [rad_mul_div x]; exact hxN⟩
      · rw [show F (⟨rad x, x / rad x⟩ : Sigma (fun _ : ℕ => ℕ)) = rad x * (x / rad x) from rfl]
        exact rad_mul_div x
  have key : (∑ x ∈ Sig, Ψ x)
      = ∑ e ∈ (Finset.Icc 1 N).filter (fun e => Squarefree (e / rad e)), hh e * f e := by
    have h1 : (∑ x ∈ Sig, Ψ x) = ∑ x ∈ Sig, hh (F x) * f (F x) := Finset.sum_congr rfl hpoint
    have h2 : (∑ x ∈ Sig, hh (F x) * f (F x)) = ∑ e ∈ Sig.image F, hh e * f e :=
      (Finset.sum_image (f := fun e => hh e * f e) (g := F) hinj).symm
    have h3 : (∑ e ∈ Sig.image F, hh e * f e)
        = ∑ e ∈ (Finset.Icc 1 N).filter (fun e => Squarefree (e / rad e)), hh e * f e := by
      rw [himg]
    exact h1.trans (h2.trans h3)
  exact step1.trans (key.symm.trans hdouble.symm)

end

end Work.LinnikAreas.Density4
