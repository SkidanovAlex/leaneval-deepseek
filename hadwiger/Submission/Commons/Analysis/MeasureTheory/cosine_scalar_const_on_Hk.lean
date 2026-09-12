import Mathlib
import Submission.Commons.Analysis.MeasureTheory.cosine_harmonic_scalar
import Submission.Commons.Analysis.MeasureTheory.harmonic_sphere_integral_zero

noncomputable section
open scoped BigOperators Classical
open MvPolynomial MeasureTheory

namespace Commons.Analysis.MeasureTheory

/-- The ambient Euclidean space. -/
private abbrev Esph (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The unit sphere. -/
private abbrev Ssph (n : ℕ) := Metric.sphere (0 : Esph n) 1

/-! ## Uniformity of the cosine scalar constant

The Funk–Hecke constant of the operator `g ↦ ∫ |⟨u,θ⟩| g θ dθ` on the space of
harmonic homogeneous polynomials of a fixed degree `k` does not depend on the
polynomial: there is a single real number `c` that works for every element of
that space and every `u` on the sphere.  We first establish the statement on
polynomials (for `n ≥ 2`, using the axis computation together with rotation
invariance), then the degenerate case `n = 1`, and finally glue.
-/

/-- Uniform scalar constant, polynomial form, for `n ≥ 2`. -/
private lemma uniform_scalar_poly_of_two_le {n k : ℕ} [NeZero n] (hn2 : 2 ≤ n) :
    ∃ c : ℝ, ∀ P : MvPolynomial (Fin n) ℝ,
      P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k →
      (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i P)) = 0 →
      ∀ u : Ssph n,
      (∫ θ : Ssph n, |inner ℝ (u : Esph n) (θ : Esph n)| *
          MvPolynomial.eval (fun i : Fin n => (θ : Esph n) i) P
        ∂MeasureTheory.volume.toSphere) =
        c * MvPolynomial.eval (fun i : Fin n => (u : Esph n) i) P := by
  classical
  rcases Commons.Analysis.MeasureTheory.harmonic_cosine_integral_axis_scalar
      (n := n) (k := k) hn2 with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro P hPh hPlap u
  obtain ⟨L, hLu⟩ := Fh1.exists_isometry_unit (n := n) (FhCHS5.e0Vec n) (u : Esph n)
    (FhCHS5.e0Vec_unit n) (mem_sphere_zero_iff_norm.mp u.2)
  let Q : MvPolynomial (Fin n) ℝ := Fh2.substA n L P
  have hQh : Q ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k := by
    dsimp [Q]
    exact Fh2.substA_mem_homogeneous n L hPh
  have hQlap : (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i Q)) = 0 := by
    dsimp [Q]
    rw [Fh2.substA_lap n L P, hPlap]
    simp [Fh2.substA]
  have hrot := FhCHS5.cosine_transform_rotate n L P
  have hQeval : MvPolynomial.eval (fun i : Fin n => (FhCHS5.e0Vec n) i) Q =
      MvPolynomial.eval (fun i : Fin n => (u : Esph n) i) P := by
    dsimp [Q]
    calc
      MvPolynomial.eval (fun i : Fin n => (FhCHS5.e0Vec n) i) (Fh2.substA n L P)
          = MvPolynomial.eval (fun i : Fin n => ((L : Esph n → Esph n) (FhCHS5.e0Vec n)) i) P :=
            FhCHS5.substA_eval_coord n L P (FhCHS5.e0Point n)
      _ = MvPolynomial.eval (fun i : Fin n => (u : Esph n) i) P := by
            congr 1
            rw [hLu]
  have hax := hc Q hQh hQlap
  calc
    (∫ θ : Ssph n, |inner ℝ (u : Esph n) (θ : Esph n)| *
          MvPolynomial.eval (fun i : Fin n => (θ : Esph n) i) P
        ∂MeasureTheory.volume.toSphere)
        = (∫ θ : Ssph n, |inner ℝ (FhCHS5.e0Vec n) (θ : Esph n)| *
            MvPolynomial.eval (fun i : Fin n => (θ : Esph n) i) Q
          ∂MeasureTheory.volume.toSphere) := by
          rw [hLu] at hrot
          exact hrot.symm
    _ = c * MvPolynomial.eval (fun i : Fin n => (FhCHS5.e0Vec n) i) Q := hax
    _ = c * MvPolynomial.eval (fun i : Fin n => (u : Esph n) i) P := by rw [hQeval]

/-- Uniform scalar constant, function form, for `n ≥ 2`. -/
private lemma uniform_scalar_of_two_le {n k : ℕ} [NeZero n] (hn2 : 2 ≤ n) :
    ∃ c : ℝ, ∀ g : Ssph n → ℝ,
      (∃ P : MvPolynomial (Fin n) ℝ,
        P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k ∧
        (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i P)) = 0 ∧
        ∀ θ : Ssph n, g θ = MvPolynomial.eval (fun i : Fin n => (θ : Esph n) i) P) →
      ∀ u : Ssph n,
      (∫ θ : Ssph n, |inner ℝ (u : Esph n) (θ : Esph n)| * g θ
        ∂MeasureTheory.volume.toSphere) = c * g u := by
  classical
  obtain ⟨c, hc⟩ := uniform_scalar_poly_of_two_le (n := n) (k := k) hn2
  refine ⟨c, ?_⟩
  intro g hg u
  rcases hg with ⟨P, hPh, hPlap, hgP⟩
  calc
    (∫ θ : Ssph n, |inner ℝ (u : Esph n) (θ : Esph n)| * g θ
        ∂MeasureTheory.volume.toSphere)
        = (∫ θ : Ssph n, |inner ℝ (u : Esph n) (θ : Esph n)| *
            MvPolynomial.eval (fun i : Fin n => (θ : Esph n) i) P
          ∂MeasureTheory.volume.toSphere) := by
          apply integral_congr_ae
          filter_upwards with θ
          rw [hgP θ]
    _ = c * MvPolynomial.eval (fun i : Fin n => (u : Esph n) i) P := hc P hPh hPlap u
    _ = c * g u := by rw [hgP u]

/-! ## The one-dimensional case -/

/-- On the unit sphere of `ℝ¹`, the absolute inner product is always `1`. -/
private lemma fin_one_abs_inner (u θ : Ssph 1) :
    |inner ℝ (u : Esph 1) (θ : Esph 1)| = 1 := by
  have hcoord : ∀ x : Ssph 1, ((x : Esph 1) 0) ^ 2 = 1 := by
    intro x
    have hinner : inner ℝ (x : Esph 1) (x : Esph 1) = ‖(x : Esph 1)‖ ^ 2 :=
      real_inner_self_eq_norm_sq (x := (x : Esph 1))
    have hnorm : ‖(x : Esph 1)‖ = 1 := mem_sphere_zero_iff_norm.mp x.2
    have hsum : inner ℝ (x : Esph 1) (x : Esph 1) =
        ((x : Esph 1) 0) * ((x : Esph 1) 0) := by
      rw [Fh2.inner_eq_sum]
      simp
    rw [hnorm] at hinner
    rw [hinner] at hsum
    nlinarith [hsum]
  have habs : ∀ x : Ssph 1, |((x : Esph 1) 0)| = 1 := by
    intro x
    have h : |((x : Esph 1) 0)| ^ 2 = 1 := by
      rw [sq_abs]
      exact hcoord x
    rcases sq_eq_one_iff.mp h with h1 | h1
    · exact h1
    · have h2 : (0:ℝ) ≤ |((x : Esph 1) 0)| := abs_nonneg _
      linarith
  have h1 : inner ℝ (u : Esph 1) (θ : Esph 1) =
      ((u : Esph 1) 0) * ((θ : Esph 1) 0) := by
    rw [Fh2.inner_eq_sum]
    simp
  rw [h1, abs_mul, habs u, habs θ, mul_one]

/-- Uniform scalar constant for `n = 1`. -/
private lemma uniform_scalar_fin_one {k : ℕ} :
    ∃ c : ℝ, ∀ g : Ssph 1 → ℝ,
      (∃ P : MvPolynomial (Fin 1) ℝ,
        P ∈ MvPolynomial.homogeneousSubmodule (Fin 1) ℝ k ∧
        (∑ i : Fin 1, MvPolynomial.pderiv i (MvPolynomial.pderiv i P)) = 0 ∧
        ∀ θ : Ssph 1, g θ = MvPolynomial.eval (fun i : Fin 1 => (θ : Esph 1) i) P) →
      ∀ u : Ssph 1,
      (∫ θ : Ssph 1, |inner ℝ (u : Esph 1) (θ : Esph 1)| * g θ
        ∂MeasureTheory.volume.toSphere) = c * g u := by
  classical
  by_cases hk : k = 0
  · subst hk
    refine ⟨(MeasureTheory.volume.toSphere : Measure (Ssph 1)).real Set.univ, ?_⟩
    intro g hg u
    rcases hg with ⟨P, hP, hlap, hgP⟩
    rw [MvPolynomial.homogeneousSubmodule_zero] at hP
    rcases Submodule.mem_one.mp hP with ⟨r, hr⟩
    have hCr : P = MvPolynomial.C r := by
      simpa [MvPolynomial.algebraMap_eq] using hr.symm
    have hgconst : ∀ θ : Ssph 1, g θ = r := by
      intro θ
      calc
        g θ = MvPolynomial.eval (fun i : Fin 1 => (θ : Esph 1) i) P := hgP θ
        _ = r := by rw [hCr]; simp
    calc
      (∫ θ : Ssph 1, |inner ℝ (u : Esph 1) (θ : Esph 1)| * g θ
          ∂MeasureTheory.volume.toSphere)
          = ∫ θ : Ssph 1, r ∂MeasureTheory.volume.toSphere := by
            apply integral_congr_ae
            filter_upwards with θ
            rw [fin_one_abs_inner u θ, hgconst θ]
            simp
      _ = (MeasureTheory.volume.toSphere : Measure (Ssph 1)).real Set.univ * r := by
            rw [MeasureTheory.integral_const]
            simp [smul_eq_mul]
      _ = (MeasureTheory.volume.toSphere : Measure (Ssph 1)).real Set.univ * g u := by
            rw [hgconst u]
  · refine ⟨0, ?_⟩
    intro g hg u
    rcases hg with ⟨P, hP, hlap, hgP⟩
    have hφ : (∫ θ : Ssph 1,
          MvPolynomial.eval (fun i : Fin 1 => (θ : Esph 1) i) P
        ∂MeasureTheory.volume.toSphere) = 0 := by
      exact @harmonic_sphere_integral_zero 1 k (⟨0⟩ : Nonempty (Fin 1)) hk P hP hlap
    calc
      (∫ θ : Ssph 1, |inner ℝ (u : Esph 1) (θ : Esph 1)| * g θ
          ∂MeasureTheory.volume.toSphere)
          = ∫ θ : Ssph 1,
              MvPolynomial.eval (fun i : Fin 1 => (θ : Esph 1) i) P
            ∂MeasureTheory.volume.toSphere := by
            apply integral_congr_ae
            filter_upwards with θ
            rw [fin_one_abs_inner u θ, hgP θ]
            simp
      _ = 0 := hφ
      _ = 0 * g u := by ring

/-! ## The uniform statement in all dimensions -/

/-- The cosine transform of a function induced by a harmonic homogeneous
polynomial of degree `k` is proportional to that function, with a proportionality
constant that depends only on `n` and `k`. -/
private lemma uniform_scalar {n k : ℕ} [Nonempty (Fin n)] :
    ∃ c : ℝ, ∀ g : Ssph n → ℝ,
      (∃ P : MvPolynomial (Fin n) ℝ,
        P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k ∧
        (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i P)) = 0 ∧
        ∀ θ : Ssph n, g θ = MvPolynomial.eval (fun i : Fin n => (θ : Esph n) i) P) →
      ∀ u : Ssph n,
      (∫ θ : Ssph n, |inner ℝ (u : Esph n) (θ : Esph n)| * g θ
        ∂MeasureTheory.volume.toSphere) = c * g u := by
  by_cases hn1 : n = 1
  · subst hn1
    exact uniform_scalar_fin_one (k := k)
  · have hnpos : 0 < n := by
      rcases ‹Nonempty (Fin n)› with ⟨i⟩
      exact Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
    haveI : NeZero n := ⟨Nat.pos_iff_ne_zero.mp hnpos⟩
    exact uniform_scalar_of_two_le (n := n) (k := k) (by omega)

/-! ## The target statement -/

theorem cosine_scalar_const_on_Hk
    {n : ℕ} {k : ℕ} [Nonempty (Fin n)]
    {g1 g2 : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ}
    (hg1 : ∃ P : MvPolynomial (Fin n) ℝ,
      P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k ∧
      (∑ j : Fin n, MvPolynomial.pderiv j (MvPolynomial.pderiv j P)) = 0 ∧
      ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        g1 θ = MvPolynomial.eval (fun j : Fin n => (θ : EuclideanSpace ℝ (Fin n)) j) P)
    (hg2 : ∃ P : MvPolynomial (Fin n) ℝ,
      P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k ∧
      (∑ j : Fin n, MvPolynomial.pderiv j (MvPolynomial.pderiv j P)) = 0 ∧
      ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        g2 θ = MvPolynomial.eval (fun j : Fin n => (θ : EuclideanSpace ℝ (Fin n)) j) P)
    (hg1ne : ∃ u : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, g1 u ≠ 0)
    (hg2ne : ∃ u : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, g2 u ≠ 0)
    (c1 c2 : ℝ)
    (hsc1 : ∀ u : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          |inner ℝ (u : EuclideanSpace ℝ (Fin n)) (θ : EuclideanSpace ℝ (Fin n))| * g1 θ
        ∂MeasureTheory.volume.toSphere) = c1 * g1 u)
    (hsc2 : ∀ u : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          |inner ℝ (u : EuclideanSpace ℝ (Fin n)) (θ : EuclideanSpace ℝ (Fin n))| * g2 θ
        ∂MeasureTheory.volume.toSphere) = c2 * g2 u) :
    c1 = c2 := by
  classical
  obtain ⟨c0, h0⟩ := uniform_scalar (n := n) (k := k)
  rcases hg1ne with ⟨u1, hu1⟩
  rcases hg2ne with ⟨u2, hu2⟩
  have hkey1 := h0 g1 hg1 u1
  have hkey2 := h0 g2 hg2 u2
  have hc1 : c1 = c0 := by
    have hEq : c1 * g1 u1 = c0 * g1 u1 := by rw [← hsc1 u1, hkey1]
    have hsub : (c1 - c0) * g1 u1 = 0 := by rw [sub_mul, hEq, sub_self]
    rcases mul_eq_zero.mp hsub with h | h
    · linarith
    · exact absurd h hu1
  have hc2 : c2 = c0 := by
    have hEq : c2 * g2 u2 = c0 * g2 u2 := by rw [← hsc2 u2, hkey2]
    have hsub : (c2 - c0) * g2 u2 = 0 := by rw [sub_mul, hEq, sub_self]
    rcases mul_eq_zero.mp hsub with h | h
    · linarith
    · exact absurd h hu2
  rw [hc1, hc2]

end Commons.Analysis.MeasureTheory
