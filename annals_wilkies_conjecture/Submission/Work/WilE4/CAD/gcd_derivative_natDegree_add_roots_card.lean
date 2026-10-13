import Mathlib

/-!
# The degree of `gcd f f'` and the number of distinct roots

For a nonzero polynomial `f` over a field of characteristic zero (here `ℝ`), the degree of
`gcd f f.derivative` is the degree of `f` minus the number of *distinct* roots of `f` in an
algebraic closure (here `ℂ`):

`(gcd f f').natDegree + (f.map (algebraMap ℝ ℂ)).roots.toFinset.card = f.natDegree`.

The proof goes through the algebraic closure `ℂ`: there every polynomial splits, and for a
nonzero `F : ℂ[X]` with `G = gcd F F'` one has
`G.rootMultiplicity a = F.rootMultiplicity a - 1` for every `a : ℂ`. Summing the root
multiplicities over the root set of `G` (resp. of `F`) gives the result. The bridge between
`gcd` over `ℝ` and over `ℂ` uses `Polynomial.gcd_map` for the Euclidean gcd and the fact that
the (normalized) gcd of a `GCDMonoid` is associated to the Euclidean gcd.
-/

open Polynomial

namespace Work.WilE4.CAD

/-- The multiplicity of `a` as a root of `gcd p q` is the minimum of the multiplicities of `a`
as a root of `p` and of `q`. -/
lemma rootMultiplicity_gcd_eq_min {K : Type*} [Field K] [DecidableEq K] (p q : K[X]) (a : K)
    (hp : p ≠ 0) (hq : q ≠ 0) :
    (gcd p q).rootMultiplicity a = min (p.rootMultiplicity a) (q.rootMultiplicity a) := by
  have hg : gcd p q ≠ 0 := gcd_ne_zero_of_left hp
  refine le_antisymm (le_min ?_ ?_) ?_
  · rw [rootMultiplicity_le_iff hg a]
    exact fun h => pow_rootMultiplicity_not_dvd hp a (h.trans (gcd_dvd_left p q))
  · rw [rootMultiplicity_le_iff hg a]
    exact fun h => pow_rootMultiplicity_not_dvd hq a (h.trans (gcd_dvd_right p q))
  · rw [le_rootMultiplicity_iff hg]
    apply dvd_gcd
    · exact (pow_dvd_pow _ (min_le_left _ _)).trans (pow_rootMultiplicity_dvd p a)
    · exact (pow_dvd_pow _ (min_le_right _ _)).trans (pow_rootMultiplicity_dvd q a)

/-- Associated polynomials have the same `natDegree`. -/
lemma natDegree_eq_of_associated_poly {K : Type*} [Field K] {p q : K[X]}
    (h : Associated p q) : p.natDegree = q.natDegree := by
  obtain ⟨u, rfl⟩ := h
  obtain ⟨r, hr, hr'⟩ := isUnit_iff.mp u.isUnit
  rw [← hr']
  exact (natDegree_mul_C hr.ne_zero).symm

/-- The (normalized) `GCDMonoid.gcd` of two polynomials is associated to their Euclidean gcd. -/
lemma associated_euclidean_gcd {K : Type*} [Field K] [DecidableEq K] (p q : K[X]) :
    Associated (EuclideanDomain.gcd p q) (gcd p q) := by
  apply associated_of_dvd_dvd
  · rw [dvd_gcd_iff]
    exact ⟨EuclideanDomain.gcd_dvd_left _ _, EuclideanDomain.gcd_dvd_right _ _⟩
  · exact EuclideanDomain.dvd_gcd (gcd_dvd_left _ _) (gcd_dvd_right _ _)

/-- Over an algebraically closed field of characteristic zero, the degree of `gcd F F'` equals
the degree of `F` minus the number of distinct roots of `F`. -/
lemma gcd_derivative_natDegree_add_roots_card_of_algClosed {K : Type*} [Field K]
    [DecidableEq K] [IsAlgClosed K] [CharZero K] (F : K[X]) (hF : F ≠ 0) :
    (gcd F F.derivative).natDegree + F.roots.toFinset.card = F.natDegree := by
  classical
  by_cases hd : F.derivative = 0
  · obtain ⟨c, rfl⟩ : ∃ c : K, F = C c := ⟨F.coeff 0, eq_C_of_derivative_eq_zero hd⟩
    rw [derivative_C]
    have hle : (gcd (C c) 0).natDegree ≤ (C c).natDegree :=
      natDegree_le_of_dvd (gcd_dvd_left _ _) hF
    rw [natDegree_C, Nat.le_zero] at hle
    rw [hle, roots_C, natDegree_C]
    simp
  · have hkey : ∀ a : K, (gcd F F.derivative).rootMultiplicity a = F.rootMultiplicity a - 1 := by
      intro a
      rw [rootMultiplicity_gcd_eq_min F F.derivative a hF hd]
      rcases eq_or_ne (F.rootMultiplicity a) 0 with hm | hm
      · rw [hm]; simp
      · have hroot : F.IsRoot a := (rootMultiplicity_pos hF).mp (Nat.pos_of_ne_zero hm)
        rw [derivative_rootMultiplicity_of_root hroot]
        exact min_eq_right (Nat.sub_le _ _)
    have hGdeg : (gcd F F.derivative).natDegree
        = ∑ a ∈ (gcd F F.derivative).roots.toFinset, (F.rootMultiplicity a - 1) := by
      rw [Splits.natDegree_eq_card_roots (IsAlgClosed.splits _), ← Multiset.toFinset_sum_count_eq]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [count_roots, hkey a]
    have hTS : (gcd F F.derivative).roots.toFinset ⊆ F.roots.toFinset := by
      intro a ha
      rw [Multiset.mem_toFinset, mem_roots'] at ha
      refine Multiset.mem_toFinset.mpr (mem_roots'.mpr ⟨hF, ?_⟩)
      have : 0 < (gcd F F.derivative).rootMultiplicity a := (rootMultiplicity_pos ha.1).mpr ha.2
      rw [hkey a] at this
      exact (rootMultiplicity_pos hF).mp (lt_of_lt_of_le this (Nat.sub_le _ _))
    have hsum : ∑ a ∈ (gcd F F.derivative).roots.toFinset, (F.rootMultiplicity a - 1)
        = ∑ a ∈ F.roots.toFinset, (F.rootMultiplicity a - 1) := by
      refine Finset.sum_subset hTS fun a _ haT => ?_
      have h0 : (gcd F F.derivative).roots.count a = 0 :=
        Multiset.count_eq_zero.mpr (fun hmem => haT (Multiset.mem_toFinset.mpr hmem))
      rw [count_roots, hkey a] at h0
      exact h0
    have hFdeg : F.natDegree = ∑ a ∈ F.roots.toFinset, F.rootMultiplicity a := by
      rw [Splits.natDegree_eq_card_roots (IsAlgClosed.splits F), ← Multiset.toFinset_sum_count_eq]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [count_roots]
    rw [hGdeg, hsum, hFdeg, Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Multiset.mem_toFinset, mem_roots'] at ha
    have hpos : 1 ≤ F.rootMultiplicity a := (rootMultiplicity_pos hF).mpr ha.2
    omega

theorem gcd_derivative_natDegree_add_roots_card (f : Polynomial ℝ) (hf : f ≠ 0) :
    (gcd f f.derivative).natDegree + (f.map (algebraMap ℝ ℂ)).roots.toFinset.card
      = f.natDegree := by
  classical
  have hinj : Function.Injective (algebraMap ℝ ℂ) := RingHom.injective _
  have hF : f.map (algebraMap ℝ ℂ) ≠ 0 := (Polynomial.map_ne_zero_iff hinj).mpr hf
  have hderiv : (f.derivative).map (algebraMap ℝ ℂ) = (f.map (algebraMap ℝ ℂ)).derivative :=
    (Polynomial.derivative_map f (algebraMap ℝ ℂ)).symm
  have hgcd : (gcd f f.derivative).natDegree
      = (gcd (f.map (algebraMap ℝ ℂ)) (f.map (algebraMap ℝ ℂ)).derivative).natDegree := by
    rw [show (gcd f f.derivative).natDegree = (EuclideanDomain.gcd f f.derivative).natDegree from
        (natDegree_eq_of_associated_poly (associated_euclidean_gcd f f.derivative)).symm,
      show (EuclideanDomain.gcd f f.derivative).natDegree
          = ((EuclideanDomain.gcd f f.derivative).map (algebraMap ℝ ℂ)).natDegree from
        (Polynomial.natDegree_map_eq_of_injective hinj _).symm,
      show (EuclideanDomain.gcd f f.derivative).map (algebraMap ℝ ℂ)
          = EuclideanDomain.gcd (f.map (algebraMap ℝ ℂ)) ((f.derivative).map (algebraMap ℝ ℂ)) from
        (Polynomial.gcd_map (p := f) (q := f.derivative) (algebraMap ℝ ℂ)).symm,
      show (EuclideanDomain.gcd (f.map (algebraMap ℝ ℂ))
              ((f.derivative).map (algebraMap ℝ ℂ))).natDegree
          = (gcd (f.map (algebraMap ℝ ℂ)) ((f.derivative).map (algebraMap ℝ ℂ))).natDegree from
        natDegree_eq_of_associated_poly (associated_euclidean_gcd _ _),
      hderiv]
  rw [hgcd, ← Polynomial.natDegree_map_eq_of_injective hinj f]
  exact gcd_derivative_natDegree_add_roots_card_of_algClosed (f.map (algebraMap ℝ ℂ)) hF

end Work.WilE4.CAD
