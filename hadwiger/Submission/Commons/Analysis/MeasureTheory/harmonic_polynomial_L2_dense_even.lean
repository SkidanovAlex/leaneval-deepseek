import Mathlib
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Submission.Commons.Analysis.MeasureTheory.sphere_even_polynomial_L2_dense
import Submission.Commons.Algebra.MvPolynomial.homogeneous_decompose
import Submission.Commons.Algebra.MvPolynomial.pderiv_mem_homogeneousSubmodule

noncomputable section
open Set Function MeasureTheory Metric
open scoped Classical BigOperators

namespace Commons.Analysis.MeasureTheory

abbrev Eu (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev Sph (n : ℕ) := Metric.sphere (0 : Eu n) 1
private abbrev Poly (n : ℕ) := MvPolynomial (Fin n) ℝ
private abbrev lapPoly {n : ℕ} (p : Poly n) : Poly n :=
  ∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)

/-! ## Harmonic-polynomial density on the sphere (even case)

Every even square-integrable function on the unit sphere is approximated in
`L²` by restrictions of harmonic homogeneous polynomials.
-/

private lemma pderiv_eq_zero_of_mem_homogeneous_zero {n : ℕ} (i : Fin n) (p : Poly n)
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ 0) :
    MvPolynomial.pderiv i p = 0 := by
  have h' : p ∈ (1 : Submodule ℝ (Poly n)) := by
    simpa [MvPolynomial.homogeneousSubmodule_zero] using hp
  obtain ⟨y, hy⟩ := Submodule.mem_one.mp h'
  rw [← hy]
  simpa using (MvPolynomial.pderiv_C (R := ℝ) (σ := Fin n) (a := y) (i := i))

/-- Homogeneous polynomials of degree at most one are harmonic. -/
private lemma lap_eq_zero_of_mem_homogeneous_le_one {n : ℕ} (p : Poly n) {d : ℕ}
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ d) (hd : d ≤ 1) :
    lapPoly p = 0 := by
  unfold lapPoly
  apply Finset.sum_eq_zero
  intro i hi
  have hpder : MvPolynomial.pderiv i p ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (d - 1) :=
    Commons.Algebra.MvPolynomial.pderiv_mem_homogeneousSubmodule (n := n) i hp
  have hd0 : d - 1 = 0 := by omega
  rw [hd0] at hpder
  exact pderiv_eq_zero_of_mem_homogeneous_zero i (MvPolynomial.pderiv i p) hpder

private lemma mem_homog_zero_of_totalDegree_zero {n : ℕ} (P : Poly n) (h : P.totalDegree = 0) :
    P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ 0 := by
  rw [MvPolynomial.mem_homogeneousSubmodule]
  rw [← MvPolynomial.totalDegree_zero_iff_isHomogeneous]
  exact h

/-- On the unit sphere, `∑ Xᵢ²` evaluates to one. -/
private lemma sphere_r2_eval_one {n : ℕ} (θ : Sph n) :
    MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) (∑ j : Fin n, (MvPolynomial.X j)^2) = 1 := by
  rw [map_sum]
  simp only [map_pow, MvPolynomial.eval_X]
  have hnorm : (∑ i : Fin n, ((θ : Eu n) i)^2) = ‖(θ : Eu n)‖^2 := by
    rw [show ‖(θ : Eu n)‖ ^ 2 = ∑ i : Fin n, ((θ : Eu n) i)^2 by
      simpa [Eu] using (PiLp.norm_sq_eq_of_L2 (β := fun _ : Fin n => ℝ) (x := (θ : Eu n)))]
  rw [hnorm]
  have hmem : ‖(θ : Eu n)‖ = 1 := (mem_sphere_zero_iff_norm.mp θ.2)
  rw [hmem]
  norm_num

/-- Multiplying by `∑ Xᵢ²` does not change the value on the unit sphere. -/
private lemma sphere_r2_mul_eval {n : ℕ} (Q : Poly n) (θ : Sph n) :
    MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) ((∑ j : Fin n, (MvPolynomial.X j)^2) * Q) =
      MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) Q := by
  rw [map_mul, sphere_r2_eval_one θ]
  simp

/-- The property "P restricted to the sphere is a finite sum of restrictions of
harmonic homogeneous polynomials". -/
private def HasHarmonicSphereSum {n : ℕ} (P : Poly n) : Prop :=
  ∃ (m : ℕ) (H : Fin m → Poly n),
    (∀ j : Fin m, ∃ kj : ℕ,
      H j ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ kj ∧ lapPoly (H j) = 0) ∧
    (∀ θ : Sph n, MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) P =
      ∑ j : Fin m, MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) (H j))

private lemma hasHarmonicSphereSum_zero {n : ℕ} : HasHarmonicSphereSum (0 : Poly n) := by
  refine ⟨0, (fun j : Fin 0 => j.elim0 : Fin 0 → Poly n), ?_, ?_⟩
  · intro j
    exact j.elim0
  · intro θ
    simp

private lemma hasHarmonicSphereSum_of_totalDegree_zero {n : ℕ} (P : Poly n)
    (h : P.totalDegree = 0) : HasHarmonicSphereSum P := by
  refine ⟨1, fun _ => P, ?_, ?_⟩
  · intro j
    refine ⟨0, ?_, ?_⟩
    · exact mem_homog_zero_of_totalDegree_zero P h
    · exact lap_eq_zero_of_mem_homogeneous_le_one (n := n) (p := P) (d := 0)
        (mem_homog_zero_of_totalDegree_zero P h) (by omega)
  · intro θ
    simp

private lemma totalDegree_sub_component_lt {n : ℕ} (P : Poly n) {T : ℕ} (hT : 1 ≤ T)
    (hPT : P.totalDegree = T) :
    (P - MvPolynomial.homogeneousComponent T P).totalDegree ≤ T - 1 := by
  let c : Poly n := MvPolynomial.homogeneousComponent T P
  have hsum : (∑ i ∈ Finset.range (T + 1), MvPolynomial.homogeneousComponent i P) = P := by
    simpa [hPT] using (MvPolynomial.sum_homogeneousComponent (φ := P))
  have hP : P = (∑ i ∈ Finset.range T, MvPolynomial.homogeneousComponent i P) + c := by
    calc
      P = ∑ i ∈ Finset.range (T + 1), MvPolynomial.homogeneousComponent i P := hsum.symm
      _ = (∑ i ∈ Finset.range T, MvPolynomial.homogeneousComponent i P) + c := by
        simp [c, Finset.sum_range_succ]
  change (P - c).totalDegree ≤ T - 1
  rw [hP, add_sub_cancel_right]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  have hiT : i < T := Finset.mem_range.mp hi
  have hmem : MvPolynomial.homogeneousComponent i P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ i :=
    MvPolynomial.homogeneousComponent_mem i P
  have hiso : (MvPolynomial.homogeneousComponent i P).IsHomogeneous i :=
    (MvPolynomial.mem_homogeneousSubmodule (n := i) (p := MvPolynomial.homogeneousComponent i P)).mp hmem
  have hle : (MvPolynomial.homogeneousComponent i P).totalDegree ≤ i :=
    MvPolynomial.IsHomogeneous.totalDegree_le hiso
  omega

private lemma totalDegree_homog_le {n : ℕ} (Q : Poly n) {d : ℕ}
    (hQ : Q ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ d) : Q.totalDegree ≤ d := by
  have hiso : Q.IsHomogeneous d :=
    (MvPolynomial.mem_homogeneousSubmodule (n := d) (p := Q)).mp hQ
  exact MvPolynomial.IsHomogeneous.totalDegree_le hiso

/-- Every polynomial, restricted to the unit sphere, is a finite sum of restrictions
of harmonic homogeneous polynomials (classical spherical-harmonic decomposition). -/
private theorem core_harmonic_sphere_sum {n : ℕ} [Nonempty (Fin n)] (P : Poly n) :
    HasHarmonicSphereSum P := by
  classical
  let D := P.totalDegree
  have hmain : ∀ d : ℕ,
      (∀ P' : Poly n, P'.totalDegree = d → HasHarmonicSphereSum P') := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro P' hP'd
        by_cases h0 : P' = 0
        · subst P'
          exact hasHarmonicSphereSum_zero (n := n)
        · by_cases hd0 : d = 0
          · have hP'0 : P'.totalDegree = 0 := by simpa [hd0] using hP'd
            exact hasHarmonicSphereSum_of_totalDegree_zero (n := n) P' hP'0
          · have hd1 : 1 ≤ d := by omega
            let top : Poly n := MvPolynomial.homogeneousComponent d P'
            have htop : top ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ d := by
              dsimp [top]
              exact MvPolynomial.homogeneousComponent_mem d P'
            rcases Commons.Algebra.MvPolynomial.homogeneous_decompose (n := n) (k := d) top htop with
              ⟨H, Q, hHhom, hQhom, hHlap, htopdef⟩
            let rest : Poly n := P' - top + Q
            have hrestTD : rest.totalDegree ≤ d - 1 := by
              dsimp [rest]
              have h1 : (P' - top).totalDegree ≤ d - 1 := by
                simpa [top] using (totalDegree_sub_component_lt (n := n) P' hd1 hP'd)
              have hQtd : Q.totalDegree ≤ d - 1 := by
                have hq : Q.totalDegree ≤ d - 2 := totalDegree_homog_le (n := n) Q hQhom
                omega
              exact (MvPolynomial.totalDegree_add (P' - top) Q).trans (max_le h1 hQtd)
            have hrec := ih rest.totalDegree (by omega : rest.totalDegree < d) rest rfl
            rcases hrec with ⟨mr, HR, hHRcond, hHRpoint⟩
            let newH : Fin (mr + 1) → Poly n := Fin.cons H HR
            refine ⟨mr + 1, newH, ?_, ?_⟩
            · intro k
              refine Fin.cases (motive := fun k => ∃ kj : ℕ,
                  newH k ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ kj ∧ lapPoly (newH k) = 0) ?_ ?_ k
              · refine ⟨d, ?_, ?_⟩
                · simpa [newH] using hHhom
                · simpa [newH] using hHlap
              · intro j
                simpa [newH] using (hHRcond j)
            · intro θ
              let v : Fin n → ℝ := fun i : Fin n => (θ : Eu n) i
              have hsplit : MvPolynomial.eval v P' =
                  MvPolynomial.eval v (P' - top) + MvPolynomial.eval v top := by
                calc
                  MvPolynomial.eval v P' = MvPolynomial.eval v ((P' - top) + top) := by
                    congr 1
                    rw [sub_add_cancel]
                  _ = MvPolynomial.eval v (P' - top) + MvPolynomial.eval v top := by simp
              have htopE : MvPolynomial.eval v top = MvPolynomial.eval v H + MvPolynomial.eval v Q := by
                rw [htopdef]
                simp only [map_add]
                congr 1
                exact sphere_r2_mul_eval (n := n) Q θ
              calc
                MvPolynomial.eval v P' = MvPolynomial.eval v (P' - top) + MvPolynomial.eval v top := hsplit
                _ = (MvPolynomial.eval v (P' - top) + MvPolynomial.eval v Q) + MvPolynomial.eval v H := by
                      rw [htopE]
                      ring
                _ = MvPolynomial.eval v rest + MvPolynomial.eval v H := by
                      dsimp [rest]
                      rw [map_add]
                _ = (∑ j : Fin mr, MvPolynomial.eval v (HR j)) + MvPolynomial.eval v H := by
                      rw [hHRpoint θ]
                _ = ∑ k : Fin (mr + 1), MvPolynomial.eval v (newH k) := by
                      rw [Fin.sum_univ_succ]
                      simp [newH]
                      ring
  exact hmain D P rfl

/-- Even harmonic polynomials are dense in the even functions of `L²(S, σ)`:
every even square-integrable function on the unit sphere is approximated in
`L²` (in the `(f - g)²`-error form) by finite sums of harmonic homogeneous
polynomials restricted to the sphere. -/
theorem harmonic_polynomial_L2_dense_even
    {n : ℕ} [Nonempty (Fin n)]
    (f : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ)
    (hfmeas : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume.toSphere)
    (hfeven : ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      f (⟨-θ.1, by simpa [mem_sphere_zero_iff_norm, norm_neg] using (mem_sphere_zero_iff_norm.mp θ.2)⟩ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) = f θ)
    (hfin : MeasureTheory.Integrable (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 => (f θ)^2) MeasureTheory.volume.toSphere)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (m : ℕ) (H : Fin m → MvPolynomial (Fin n) ℝ),
      (∀ j : Fin m, ∃ kj : ℕ,
        H j ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ kj ∧
        (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i (H j))) = 0) ∧
      (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          (f θ - (∑ j : Fin m, MvPolynomial.eval (fun i : Fin n => (θ : EuclideanSpace ℝ (Fin n)) i) (H j)))^2
        ∂MeasureTheory.volume.toSphere) ≤ ε := by
  obtain ⟨P, _hPeven, hPint⟩ :=
    sphere_even_polynomial_L2_dense (n := n) f hfmeas hfeven hfin (ε := ε) hε
  rcases core_harmonic_sphere_sum (n := n) P with ⟨m, H, hHcond, hHpoint⟩
  refine ⟨m, H, ?_, ?_⟩
  · -- conditions of harmonicity / homogeneity for the H j
    intro j
    rcases hHcond j with ⟨kj, hmem, hlap⟩
    refine ⟨kj, hmem, ?_⟩
    · unfold lapPoly at hlap
      simpa using hlap
  · -- L² error bound
    have hfun : (fun θ : Sph n =>
          (f θ - (∑ j : Fin m, MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) (H j)))^2)
        = (fun θ : Sph n =>
          (f θ - MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) P)^2) := by
      funext θ
      congr 1
      rw [← hHpoint θ]
    have hinteq : (∫ θ : Sph n,
          (f θ - (∑ j : Fin m, MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) (H j)))^2
        ∂MeasureTheory.volume.toSphere) =
        (∫ θ : Sph n,
          (f θ - MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) P)^2
        ∂MeasureTheory.volume.toSphere) := by
      rw [hfun]
    rw [hinteq]
    exact hPint

end Commons.Analysis.MeasureTheory
