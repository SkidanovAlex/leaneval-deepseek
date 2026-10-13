import Mathlib
import Submission.Work.WilE4.Poly
import Submission.Work.WilE4.Poly.spec_pderiv
import Submission.Work.WilE4.CAD.signConst_data
import Submission.Work.WilE4.CAD.map_ofReal_ne_zero
import Submission.Work.WilE4.CAD.disk_roots_card_eventually_const
import Submission.Work.WilE4.CAD.exists_pos_sign_change_simple_root
import Submission.Work.WilE4.CAD.exists_sign_eq_of_simple_root
import Submission.Work.WilE4.CAD.sign_stable_Icc

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Classical Filter
open scoped Topology

namespace Work.WilE4.CAD

open MvPolynomial Polynomial
open Work.WilE4 (spec)

variable {m k : ℕ}

/-! ## Bridges between `ℝ[X]` and `ℂ[X]`

The projection data of the theorem is stated over `ℝ`, while the root-counting arguments are
carried out over `ℂ`.  The lemmas below transfer the degree of a gcd, the multiplicity of a root
and the property of being a root along the embedding `ℝ → ℂ`. -/

/-- The degree of the gcd agrees with the degree of the Euclidean gcd. -/
theorem natDegree_gcd_eq_euclidean_gcd {k : Type*} [Field k] (F G : Polynomial k) :
    (gcd F G).natDegree = (EuclideanDomain.gcd F G).natDegree := by
  have hd1 : gcd F G ∣ EuclideanDomain.gcd F G := by
    have h1 : gcd F G ∣ F * EuclideanDomain.gcdA F G :=
      dvd_mul_of_dvd_left (gcd_dvd_left F G) _
    have h2 : gcd F G ∣ G * EuclideanDomain.gcdB F G :=
      dvd_mul_of_dvd_left (gcd_dvd_right F G) _
    rw [EuclideanDomain.gcd_eq_gcd_ab]
    exact dvd_add h1 h2
  have hd2 : EuclideanDomain.gcd F G ∣ gcd F G :=
    dvd_gcd (EuclideanDomain.gcd_dvd_left F G) (EuclideanDomain.gcd_dvd_right F G)
  have hz : gcd F G = 0 ↔ EuclideanDomain.gcd F G = 0 := by
    constructor
    · intro h
      rw [h] at hd1
      exact zero_dvd_iff.mp hd1
    · intro h
      rw [h] at hd2
      exact zero_dvd_iff.mp hd2
  rcases eq_or_ne (gcd F G) 0 with h0 | h0
  · rw [h0, hz.mp h0]
  · have hne : EuclideanDomain.gcd F G ≠ 0 := fun h => h0 (hz.mpr h)
    exact le_antisymm (Polynomial.natDegree_le_of_dvd hd1 hne)
      (Polynomial.natDegree_le_of_dvd hd2 h0)

/-- The degree of the gcd is unchanged by the embedding `ℝ → ℂ`. -/
theorem gcd_map_ofReal_natDegree (f g : Polynomial ℝ) :
    (gcd (f.map (algebraMap ℝ ℂ)) (g.map (algebraMap ℝ ℂ))).natDegree = (gcd f g).natDegree := by
  rw [natDegree_gcd_eq_euclidean_gcd (f.map (algebraMap ℝ ℂ)) (g.map (algebraMap ℝ ℂ)),
    natDegree_gcd_eq_euclidean_gcd f g]
  have h := congrArg Polynomial.natDegree
    (Polynomial.gcd_map (algebraMap ℝ ℂ) (p := f) (q := g))
  rw [Polynomial.natDegree_map] at h
  exact h

/-- The multiplicity of a real root is unchanged by the embedding `ℝ → ℂ`. -/
theorem rootMultiplicity_map_ofReal (f : Polynomial ℝ) (t : ℝ) :
    (f.map (algebraMap ℝ ℂ)).rootMultiplicity (t : ℂ) = f.rootMultiplicity t :=
  (Polynomial.eq_rootMultiplicity_map (algebraMap ℝ ℂ).injective t).symm

/-- The embedding `ℝ → ℂ` carries roots to roots. -/
theorem isRoot_map_ofReal {f : Polynomial ℝ} {t : ℝ} (h : f.IsRoot t) :
    (f.map (algebraMap ℝ ℂ)).IsRoot (t : ℂ) :=
  Polynomial.IsRoot.map (f := algebraMap ℝ ℂ) h

/-- Conversely a real point that is a root of the embedded polynomial is a root. -/
theorem isRoot_of_map_ofReal {f : Polynomial ℝ} {t : ℝ}
    (h : (f.map (algebraMap ℝ ℂ)).IsRoot (t : ℂ)) : f.IsRoot t :=
  Polynomial.IsRoot.of_map (f := algebraMap ℝ ℂ) (x := t) h (algebraMap ℝ ℂ).injective

/-! ## Signs -/

/-- The sign of a power is the power of the sign. -/
theorem sign_pow_eq (x : ℝ) (n : ℕ) :
    SignType.sign (x ^ n) = (SignType.sign x) ^ n :=
  map_pow (signHom : ℝ →*₀ SignType) x n

/-! ## Continuity of a polynomial family in its parameter -/

/-- Evaluation of a member of a family of polynomials of bounded degree is continuous in the
parameter along a converging sequence. -/
theorem tendsto_spec_eval {m : ℕ} (P : MvPolynomial (Fin (m + 1)) ℝ) (D : ℕ)
    (hD : ∀ x : Fin m → ℝ, (spec P x).natDegree ≤ D)
    {x : ℕ → Fin m → ℝ} {x₀ : Fin m → ℝ} (hx : Filter.Tendsto x Filter.atTop (nhds x₀))
    {a : ℕ → ℝ} {a₀ : ℝ} (ha : Filter.Tendsto a Filter.atTop (nhds a₀)) :
    Filter.Tendsto (fun n => (spec P (x n)).eval (a n)) Filter.atTop
      (nhds ((spec P x₀).eval a₀)) := by
  have hcoeff : ∀ j : ℕ, Filter.Tendsto (fun n => (spec P (x n)).coeff j) Filter.atTop
      (nhds ((spec P x₀).coeff j)) := fun j =>
    ((continuous_spec_coeff P j).tendsto x₀).comp hx
  have key : ∀ n : ℕ, (spec P (x n)).eval (a n)
      = ∑ j ∈ Finset.range (D + 1), (spec P (x n)).coeff j * (a n) ^ j := fun n =>
    Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (hD (x n))) (a n)
  have hkey : (spec P x₀).eval a₀
      = ∑ j ∈ Finset.range (D + 1), (spec P x₀).coeff j * a₀ ^ j :=
    Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (hD x₀)) a₀
  have hsum : Filter.Tendsto
      (fun n => ∑ j ∈ Finset.range (D + 1), (spec P (x n)).coeff j * (a n) ^ j)
      Filter.atTop (nhds (∑ j ∈ Finset.range (D + 1), (spec P x₀).coeff j * a₀ ^ j)) :=
    tendsto_finsetSum _ fun j _ => (hcoeff j).mul (ha.pow j)
  rw [hkey]
  refine hsum.congr' ?_
  filter_upwards with n
  exact (key n).symm

/-- Along a convergent sequence of non-zero limit, the sign is eventually that of the limit. -/
theorem eventually_sign_eq_of_tendsto' {u : ℕ → ℝ} {L : ℝ}
    (hu : Filter.Tendsto u Filter.atTop (nhds L)) (hL : L ≠ 0) :
    ∀ᶠ n in Filter.atTop, SignType.sign (u n) = SignType.sign L := by
  rcases lt_trichotomy L 0 with hneg | hzero | hpos
  · filter_upwards [hu.eventually (isOpen_Iio.mem_nhds hneg)] with n hn
    rw [sign_neg hn, sign_neg hneg]
  · exact absurd hzero hL
  · filter_upwards [hu.eventually (isOpen_Ioi.mem_nhds hpos)] with n hn
    rw [sign_pos hn, sign_pos hpos]

/-! ## Consequences of the sign-constancy hypothesis `hcoeff` -/

/-- `hcoeff` packaged as `CoeffConst`. -/
theorem coeffConst_of_hcoeff' {m k : ℕ} {P : Fin k → MvPolynomial (Fin (m + 1)) ℝ} {D : ℕ}
    (hD : ∀ i : Fin k, (P i).degreeOf (Fin.last m) ≤ D) {C : Set (Fin m → ℝ)}
    (hcoeff : ∀ i : Fin k, ∀ j : ℕ, j ≤ D → ∀ x ∈ C, ∀ x' ∈ C,
      SignType.sign ((spec (P i) x).coeff j) = SignType.sign ((spec (P i) x').coeff j)) :
    CoeffConst P C :=
  fun i j hj x hx x' hx' => hcoeff i j (le_trans hj (hD i)) x hx x' hx'

/-- On `C`, a member of the family either vanishes identically or at no point. -/
theorem spec_eq_zero_iff_on_C {m k : ℕ} {P : Fin k → MvPolynomial (Fin (m + 1)) ℝ} {D : ℕ}
    (hD : ∀ i : Fin k, (P i).degreeOf (Fin.last m) ≤ D) {C : Set (Fin m → ℝ)}
    (hcoeff : ∀ i : Fin k, ∀ j : ℕ, j ≤ D → ∀ x ∈ C, ∀ x' ∈ C,
      SignType.sign ((spec (P i) x).coeff j) = SignType.sign ((spec (P i) x').coeff j))
    {i : Fin k} {x x' : Fin m → ℝ} (hx : x ∈ C) (hx' : x' ∈ C) :
    spec (P i) x = 0 ↔ spec (P i) x' = 0 := by
  have hcc : CoeffConst P C := coeffConst_of_hcoeff' hD hcoeff
  constructor
  · intro h0
    ext j
    by_cases hj : j ≤ (P i).degreeOf (Fin.last m)
    · have hiff : ((spec (P i) x).coeff j = 0) ↔ ((spec (P i) x').coeff j = 0) :=
        coeff_spec_eq_zero_iff hcc hj hx hx'
      rw [Polynomial.coeff_zero, ← hiff]
      simp [h0]
    · exact coeff_spec_eq_zero_of_degreeOf_lt (P i) x' (not_le.mp hj)
  · intro h0
    ext j
    by_cases hj : j ≤ (P i).degreeOf (Fin.last m)
    · have hiff : ((spec (P i) x).coeff j = 0) ↔ ((spec (P i) x').coeff j = 0) :=
        coeff_spec_eq_zero_iff hcc hj hx hx'
      rw [Polynomial.coeff_zero, hiff]
      simp [h0]
    · exact coeff_spec_eq_zero_of_degreeOf_lt (P i) x (not_le.mp hj)

/-- The `natDegree` of a member is bounded by the degree bound, uniformly over the parameter. -/
theorem spec_natDegree_le_of_degreeOf {m : ℕ} (P : MvPolynomial (Fin (m + 1)) ℝ) (D : ℕ)
    (hD : P.degreeOf (Fin.last m) ≤ D) (x : Fin m → ℝ) : (spec P x).natDegree ≤ D := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro j hj
  exact coeff_spec_eq_zero_of_degreeOf_lt P x (lt_of_le_of_lt hD hj)

/-- The iterated derivatives of the members of a family closed under `∂_m` are again members. -/
theorem exists_iterate_pderiv_mem {m k : ℕ} (P : Fin k → MvPolynomial (Fin (m + 1)) ℝ)
    (hclosed : ∀ i : Fin k, ∃ j : Fin k, P j = MvPolynomial.pderiv (Fin.last m) (P i))
    (i : Fin k) (r : ℕ) :
    ∃ j : Fin k, P j = (MvPolynomial.pderiv (Fin.last m))^[r] (P i) := by
  induction r with
  | zero => exact ⟨i, rfl⟩
  | succ r ih =>
      obtain ⟨j, hj⟩ := ih
      obtain ⟨j', hj'⟩ := hclosed j
      refine ⟨j', ?_⟩
      rw [Function.iterate_succ_apply', ← hj, hj']

end Work.WilE4.CAD
