import Mathlib
import Submission.DiscrepancyDefs
import Submission.LMAux
import Submission.F_exact

/-! Theorem 4.1 of arXiv:1907.09464v1 ("Flat Littlewood polynomials exist",
Balister--Bollobas--Morris--Sahasrabudhe--Tiba) is the "Main Partial Coloring Lemma"
of Lovett--Meka, arXiv:1203.5747v2 (Theorem 4 there):

Given `v_1,...,v_m ∈ R^n` and `x0 ∈ [-1,1]^n`, if `c_j ≥ 0` with
`∑_j exp(-c_j^2/16) ≤ n/16`, then there is `x ∈ [-1,1]^n` with
`|⟨x - x0, v_j⟩| ≤ c_j ‖v_j‖_2` for every `j`, and `x_i ∈ {-1,1}` for at least `n/2`
indices `i`.

Proved via the Lovett--Meka Gaussian freezing walk on `Vec n =
EuclideanSpace ℝ (Fin n)` (see the modules `Submission.LMProbs`, ...,
`Submission.F_exact`): an ε-version `Submission.Discrepancy.eps_coloring`
plus a diagonal/compactness limit `Submission.Discrepancy.exact_coloring`,
translated here to plain functions `Fin n → ℝ`.
-/
open scoped BigOperators

noncomputable section
namespace Submission
namespace Discrepancy

/-- `toV` distributes over subtraction (the coordinate maps are additive). -/
lemma toV_sub' {n : ℕ} (x x0 : Fin n → ℝ) : toV (fun i : Fin n => x i - x0 i) = toV x - toV x0 := by
  ext i
  simp [toV]

/-- The euclidean norm is zero exactly for the zero vector. -/
lemma eucl_eq_zero_iff_zero {n : ℕ} (f : Fin n → ℝ) : eucl f = 0 ↔ f = 0 := by
  constructor
  · intro h
    funext i
    have hsq := congrArg (fun x : ℝ => x ^ 2) h
    have hsq' : (∑ j : Fin n, (f j) ^ 2) = 0 := by
      simpa [eucl_sq] using hsq
    have hsum := Finset.single_le_sum (fun j hj => sq_nonneg (f j)) (Finset.mem_univ i)
    have this : (f i) ^ 2 ≤ 0 := by simpa [hsq'] using hsum
    exact sq_eq_zero_iff.mp (le_antisymm this (sq_nonneg (f i)))
  · intro h
    simp [h, eucl]

/-- The norm on `Vec n` of `toV f` is `eucl f`. -/
lemma norm_toV_eq_eucl {n : ℕ} (f : Fin n → ℝ) : ‖toV f‖ = eucl f := by
  simpa [vnorm] using (vnorm_toV f)

theorem partial_coloring (n m : ℕ) (v : Fin m → (Fin n → ℝ)) (x0 : Fin n → ℝ)
    (hx0 : ∀ i : Fin n, x0 i ∈ Set.Icc (-1) 1) (c : Fin m → ℝ) (hc : ∀ j, 0 ≤ c j)
    (hsum : ∑ j : Fin m, Real.exp (-(c j) ^ 2 / 16) ≤ (n : ℝ) / 16) :
    ∃ x : Fin n → ℝ,
      (∀ i : Fin n, x i ∈ Set.Icc (-1) 1) ∧
      (∀ j : Fin m, |dot (fun i => x i - x0 i) (v j)| ≤ c j * eucl (v j)) ∧
      (((n + 1) / 2 : ℕ) ≤ Fintype.card {i : Fin n // x i = -1 ∨ x i = 1}) := by
  by_cases hn0 : n = 0
  · subst n
    refine ⟨fun _ : Fin 0 => 0, ?_, ?_, ?_⟩
    · intro i; fin_cases i
    · intro j
      simp [dot, eucl]
    · simp
  · have hn : 1 ≤ n := by omega
    let ι : Type := {j : Fin m // eucl (v j) ≠ 0}
    letI : Fintype ι := Fintype.ofFinite ι
    let x0V : Vec n := toV x0
    let vι : ι → Vec n := fun j => toV (v j.1)
    let cι : ι → ℝ := fun j => c j.1
    have hx0V : ∀ i : Fin n, |x0V i| ≤ 1 := by
      intro i
      have hi := hx0 i
      exact abs_le.mpr ⟨hi.1, hi.2⟩
    have hcι : ∀ j : ι, 0 ≤ cι j := by intro j; exact hc j.1
    have hneι : ∀ j : ι, ‖vι j‖ ≠ 0 := by
      intro j
      rw [norm_toV_eq_eucl]
      exact j.2
    have hsumι : (∑ j : ι, Real.exp (-(cι j) ^ 2 / 16)) ≤ (n : ℝ) / 16 := by
      let p : Fin m → Prop := fun j => eucl (v j) ≠ 0
      let s : Finset (Fin m) := Finset.univ.filter p
      let g : Fin m → ℝ := fun j => Real.exp (-(c j) ^ 2 / 16)
      have hle : (∑ j ∈ s, g j) ≤ (∑ j : Fin m, g j) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (by intro x hx; simp [s]) (by
          intro j hj hnotin
          exact (Real.exp_pos _).le)
      calc
        (∑ j : ι, Real.exp (-(cι j) ^ 2 / 16)) = (∑ j ∈ s, g j) := by
            rw [Finset.sum_subtype (s := s) (p := p) (f := g) (by intro x; simp [s, p])]
        _ ≤ (∑ j : Fin m, g j) := hle
        _ ≤ (n : ℝ) / 16 := by simpa [g] using hsum
    rcases exact_coloring (n := n) (x0 := x0V) (v := vι) (c := cι) hn hx0V hcι hneι hsumι with
      ⟨xV, hxVbox, hxVrows, hxVcnt⟩
    let x : Fin n → ℝ := ofV xV
    refine ⟨x, ?_, ?_, ?_⟩
    · intro i
      have hi := hxVbox i
      rw [show x i = xV i by rfl]
      exact abs_le.mp hi
    · intro j
      by_cases hjz : eucl (v j) = 0
      · have hvj : v j = 0 := (eucl_eq_zero_iff_zero (v j)).mp hjz
        rw [hvj]
        simp [dot, eucl]
      · have hmain := hxVrows ⟨j, hjz⟩
        have hxVeq : xV = toV x := by simp [x]
        have hb : |vin (toV x - toV x0) (toV (v j))| ≤ c j * ‖toV (v j)‖ := by
          simpa [hxVeq, x0V, vι, cι] using hmain
        have hv : vin (toV x - toV x0) (toV (v j)) = dot (fun i : Fin n => x i - x0 i) (v j) := by
          rw [← toV_sub']
          rw [vin_toV]
        calc
          |dot (fun i : Fin n => x i - x0 i) (v j)| = |vin (toV x - toV x0) (toV (v j))| := by rw [hv]
          _ ≤ c j * ‖toV (v j)‖ := hb
          _ = c j * eucl (v j) := by rw [norm_toV_eq_eucl]
    · have hcard : Fintype.card {i : Fin n // xV i = 1 ∨ xV i = -1} =
          Fintype.card {i : Fin n // x i = -1 ∨ x i = 1} := by
        apply Fintype.card_congr
        exact Equiv.subtypeEquivRight (fun i : Fin n => by
          constructor
          · intro h
            rcases h with h1 | h2
            · right; simpa [x] using h1
            · left; simpa [x] using h2
          · intro h
            rcases h with h1 | h2
            · right; simpa [x] using h1
            · left; simpa [x] using h2)
      rw [← hcard]
      exact hxVcnt

end Discrepancy
end Submission
