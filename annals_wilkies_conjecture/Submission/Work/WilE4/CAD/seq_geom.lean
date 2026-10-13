import Mathlib
import Submission.Work.WilE4.CAD.seq_bounded
import Submission.Work.WilE4.CAD.gcd_derivative_natDegree_add_roots_card
import Submission.Work.WilE4.CAD.common_root_unique
import Submission.Work.WilE4.CAD.gcd_spec_natDegree_const_on_C
import Submission.Work.WilE4.CAD.gcd_spec_psc
import Submission.Work.WilE4.CAD.disk_roots_card_eventually_const
import Submission.Work.WilE4.CAD.exists_minimal_rootMultiplicity_member
import Submission.Work.WilE4.CAD.map_ofReal_ne_zero

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

open Classical Filter
open scoped Topology

namespace Work.WilE4.CAD

open MvPolynomial Polynomial
open Work.WilE4 (spec)

variable {m k : ℕ}

/-! ## Helping lemmas for the geometric data -/

/-- A non-zero real polynomial with a root `t₀` has a positive distance from `t₀` to every other
complex root. -/
theorem exists_pos_lt_dist_roots {f : Polynomial ℝ} {t₀ : ℝ} (hf : f ≠ 0)
    (hroot : f.IsRoot t₀) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℂ, (f.map (algebraMap ℝ ℂ)).IsRoot z → z ≠ (t₀ : ℂ) →
      δ < dist z (t₀ : ℂ) := by
  set S : Finset ℂ := ((f.map (algebraMap ℝ ℂ)).roots.toFinset.erase (t₀ : ℂ)) with hS
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · refine ⟨1, one_pos, fun z hz hzt => ?_⟩
    have hmem : z ∈ S := by
      rw [hS]
      exact Finset.mem_erase.mpr ⟨hzt,
        Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (map_ofReal_ne_zero hf)).mpr hz)⟩
    rw [hSe] at hmem
    simp at hmem
  · obtain ⟨z0, hz0mem, hz0min⟩ := Finset.exists_min_image S (fun z => dist z (t₀ : ℂ)) hSne
    have hz0pos : 0 < dist z0 (t₀ : ℂ) :=
      dist_pos.mpr (Finset.mem_erase.mp (by rw [← hS]; exact hz0mem)).1
    refine ⟨dist z0 (t₀ : ℂ) / 2, by linarith, fun z hz hzt => ?_⟩
    have hmem : z ∈ S := by
      rw [hS]
      exact Finset.mem_erase.mpr ⟨hzt,
        Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (map_ofReal_ne_zero hf)).mpr hz)⟩
    have h1 := hz0min z hmem
    linarith

/-- The number of distinct complex roots of a member of the family is constant on `C`. -/
theorem rootsCard_spec_const_on_C {m k : ℕ} (P : Fin k → MvPolynomial (Fin (m + 1)) ℝ) (D : ℕ)
    (hD : ∀ i : Fin k, (P i).degreeOf (Fin.last m) ≤ D)
    (hclosed : ∀ i : Fin k, ∃ j : Fin k, P j = MvPolynomial.pderiv (Fin.last m) (P i))
    (C : Set (Fin m → ℝ))
    (hcoeff : ∀ i : Fin k, ∀ j : ℕ, j ≤ D → ∀ x ∈ C, ∀ x' ∈ C,
      SignType.sign ((spec (P i) x).coeff j) = SignType.sign ((spec (P i) x').coeff j))
    (hmin : PscSignConst P C)
    (i : Fin k) {x x' : Fin m → ℝ} (hx : x ∈ C) (hx' : x' ∈ C) :
    (((spec (P i) x).map (algebraMap ℝ ℂ)).roots.toFinset.card)
      = (((spec (P i) x').map (algebraMap ℝ ℂ)).roots.toFinset.card) := by
  by_cases h0 : spec (P i) x = 0
  · have h0' : spec (P i) x' = 0 := (spec_eq_zero_iff_on_C hD hcoeff hx hx').mp h0
    simp [h0, h0']
  · have h0' : spec (P i) x' ≠ 0 := fun h => h0 ((spec_eq_zero_iff_on_C hD hcoeff hx hx').mpr h)
    obtain ⟨i', hi'⟩ := hclosed i
    have hder : (spec (P i') x) = (spec (P i) x).derivative := by
      rw [hi', Work.WilE4.Poly.spec_pderiv]
    have hder' : (spec (P i') x') = (spec (P i) x').derivative := by
      rw [hi', Work.WilE4.Poly.spec_pderiv]
    have h1 := gcd_derivative_natDegree_add_roots_card (spec (P i) x) h0
    have h2 := gcd_derivative_natDegree_add_roots_card (spec (P i) x') h0'

    have hgcd := gcd_spec_natDegree_const_on_C_psc P D hD C hcoeff hmin i i' x x' hx hx'
    rw [hder, hder'] at hgcd
    have hdeg : (spec (P i) x).natDegree = (spec (P i) x').natDegree :=
      natDegree_spec_const (coeffConst_of_hcoeff' hD hcoeff) hx hx'
    omega

/-- The degree of the gcd of two members, computed over `ℂ`, is constant on `C`. -/
theorem gcdMap_natDegree_const_on_C {m k : ℕ} (P : Fin k → MvPolynomial (Fin (m + 1)) ℝ) (D : ℕ)
    (hD : ∀ i : Fin k, (P i).degreeOf (Fin.last m) ≤ D)
    (C : Set (Fin m → ℝ))
    (hcoeff : ∀ i : Fin k, ∀ j : ℕ, j ≤ D → ∀ x ∈ C, ∀ x' ∈ C,
      SignType.sign ((spec (P i) x).coeff j) = SignType.sign ((spec (P i) x').coeff j))
    (hmin : PscSignConst P C)
    (i j : Fin k) {x x' : Fin m → ℝ} (hx : x ∈ C) (hx' : x' ∈ C) :
    (gcd ((spec (P i) x).map (algebraMap ℝ ℂ)) ((spec (P j) x).map (algebraMap ℝ ℂ))).natDegree
      = (gcd ((spec (P i) x').map (algebraMap ℝ ℂ)) ((spec (P j) x').map (algebraMap ℝ ℂ))).natDegree := by
  rw [gcd_map_ofReal_natDegree, gcd_map_ofReal_natDegree]
  exact gcd_spec_natDegree_const_on_C_psc P D hD C hcoeff hmin i j x x' hx hx'

/-- A finite family of non-zero real polynomials has all its complex roots other than `t₀` at a
uniformly positive distance from `t₀`. -/
theorem exists_pos_lt_dist_roots_family {ι : Type*} [Fintype ι] (f : ι → Polynomial ℝ) (t₀ : ℝ)
    (hf : ∀ i, f i ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (i : ι) (z : ℂ), ((f i).map (algebraMap ℝ ℂ)).IsRoot z →
      z ≠ (t₀ : ℂ) → δ < dist z (t₀ : ℂ) := by
  classical
  set T : Finset ℂ := Finset.univ.biUnion fun i =>
    (((f i).map (algebraMap ℝ ℂ)).roots.toFinset.erase (t₀ : ℂ)) with hT
  rcases T.eq_empty_or_nonempty with hTe | hTne
  · refine ⟨1, one_pos, fun i z hz hzt => ?_⟩
    have hmem : z ∈ T := by
      rw [hT]
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
        Finset.mem_erase.mpr ⟨hzt,
          Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (map_ofReal_ne_zero (hf i))).mpr hz)⟩⟩
    rw [hTe] at hmem
    simp at hmem
  · obtain ⟨z0, hz0mem, hz0min⟩ := Finset.exists_min_image T (fun z => dist z (t₀ : ℂ)) hTne
    have hz0pos : 0 < dist z0 (t₀ : ℂ) := by
      have h1 : z0 ≠ (t₀ : ℂ) := by
        rw [hT] at hz0mem
        obtain ⟨i, -, hzi⟩ := Finset.mem_biUnion.mp hz0mem
        exact (Finset.mem_erase.mp hzi).1
      exact dist_pos.mpr h1
    refine ⟨dist z0 (t₀ : ℂ) / 2, by linarith, fun i z hz hzt => ?_⟩
    have hmem : z ∈ T := by
      rw [hT]
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
        Finset.mem_erase.mpr ⟨hzt,
          Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (map_ofReal_ne_zero (hf i))).mpr hz)⟩⟩
    have h1 := hz0min z hmem
    linarith

/-- The distance between two real numbers inside `ℂ`. -/
theorem dist_ofReal_eq (a b : ℝ) : dist (a : ℂ) (b : ℂ) = |a - b| := by
  rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real]
  rfl

end Work.WilE4.CAD
