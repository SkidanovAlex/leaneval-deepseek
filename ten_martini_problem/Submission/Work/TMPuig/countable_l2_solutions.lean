/-
# Countability of the energies with an `l^2` solution (Ten Martini, Puig's component)

For a real potential `a : Z -> R` and real energy `Lambda`, call `u : Z -> C` a solution if
`u (n+1) + u (n-1) + a n * u n = Lambda * u n` for all `n`.  The set of energies `Lambda`
admitting a *nonzero* square summable solution is countable.

Proof outline:
* Two `l^2` solutions at *different* energies are orthogonal: for
  `W n = star (u n) * v (n+1) - star (u (n+1)) * v n` one has
  `W (n+1) - W n = (E' - E) * star (u (n+1)) * v (n+1)`, and telescoping over `Z`
  (using summability of `W`) gives `(E' - E) * tsum (star u * v) = 0`.  (`star u` solves the
  recurrence at `E` because the potential and energy are real.)
* Hence any choice of a *unit* `l^2` solution `V Lam` at each admissible `Lam` is an
  orthonormal family in `l^2(Z)`: `inner (V Lam) (V Lam') = 0` for `Lam ≠ `Lam'`.
* `l^2(Z)` is separable: the finitely supported Gaussian rational vectors form a countable
  dense set `D`.
* Every `V Lam` is within `1/2` of some element of `D`, and `V Lam ⊥ V Lam'` forces
  `dist (V Lam) (V Lam') = sqrt 2 > 1`, so the assignment `Lam ↦ d Lam ∈ D` is injective.
  A `D`-indexed injective family is countable.

The last step is the standard "an orthonormal family in a separable space is countable".
-/
import Mathlib
import ChallengeDeps
import Submission.Work.TMContract.Components
import Submission.Work.TMPuig.Defs

open scoped BigOperators Topology
open Filter
open LeanEval.Analysis.TenMartini

namespace Work.TMPuig

lemma dense_gaussianRationals (z : ℂ) {η : ℝ} (hη : 0 < η) :
    ∃ q : ℚ × ℚ, ‖z - (((q.1 : ℚ) : ℂ) + (((q.2 : ℚ) : ℂ)) * Complex.I)‖ < η := by
  have hdense : Dense (Set.range (fun q : ℚ => (q : ℝ))) := Rat.denseRange_cast
  obtain ⟨y1, ⟨q1, rfl⟩, hy1⟩ := hdense.exists_dist_lt z.re (show (0:ℝ) < η/2 by linarith)
  obtain ⟨y2, ⟨q2, rfl⟩, hy2⟩ := hdense.exists_dist_lt z.im (show (0:ℝ) < η/2 by linarith)
  refine ⟨(q1, q2), ?_⟩
  have h1 : |z.re - (q1:ℝ)| < η/2 := by rw [← Real.dist_eq]; exact hy1
  have h2 : |z.im - (q2:ℝ)| < η/2 := by rw [← Real.dist_eq]; exact hy2
  have hre : (z - (((q1 : ℚ) : ℂ) + (((q2 : ℚ) : ℂ)) * Complex.I)).re = z.re - (q1:ℝ) := by simp
  have him : (z - (((q1 : ℚ) : ℂ) + (((q2 : ℚ) : ℂ)) * Complex.I)).im = z.im - (q2:ℝ) := by simp
  calc ‖z - (((q1 : ℚ) : ℂ) + (((q2 : ℚ) : ℂ)) * Complex.I)‖
      ≤ |(z - (((q1 : ℚ) : ℂ) + (((q2 : ℚ) : ℂ)) * Complex.I)).re|
        + |(z - (((q1 : ℚ) : ℂ) + (((q2 : ℚ) : ℂ)) * Complex.I)).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ = |z.re - (q1:ℝ)| + |z.im - (q2:ℝ)| := by rw [hre, him]
    _ < η/2 + η/2 := by linarith
    _ = η := by ring

noncomputable def gaussVec (φ : (Σ s : Finset ℤ, (s → ℚ × ℚ))) : ℤ → ℂ :=
  fun n => if h : n ∈ φ.1 then ((φ.2 ⟨n, h⟩).1 : ℂ) + ((φ.2 ⟨n, h⟩).2 : ℂ) * Complex.I else 0

lemma gaussVec_memℓp (φ : (Σ s : Finset ℤ, (s → ℚ × ℚ))) : Memℓp (gaussVec φ) 2 := by
  refine memℓp_gen ?_
  refine summable_of_ne_finset_zero (s := φ.1) (fun n hn => ?_)
  have hn0 : gaussVec φ n = 0 := by simp [gaussVec, hn]
  rw [hn0]; simp

noncomputable def gaussEll (φ : (Σ s : Finset ℤ, (s → ℚ × ℚ))) : EllTwo :=
  ⟨gaussVec φ, gaussVec_memℓp φ⟩

lemma gaussEll_apply (φ : (Σ s : Finset ℤ, (s → ℚ × ℚ))) (n : ℤ) :
    gaussEll φ n = (if h : n ∈ φ.1 then ((φ.2 ⟨n, h⟩).1 : ℂ) + ((φ.2 ⟨n, h⟩).2 : ℂ) * Complex.I else 0) := rfl

lemma gaussEll_approx (U : EllTwo) {r : ℝ} (hr : 0 < r) :
    ∃ φ : (Σ s : Finset ℤ, (s → ℚ × ℚ)), dist U (gaussEll φ) < r := by
  have hf : Summable (fun n : ℤ => ‖U n‖ ^ 2) := by
    have h := (lp.memℓp U).summable (p := 2) (by norm_num)
    simpa [Real.rpow_two] using h
  have hconv : Tendsto (fun s : Finset ℤ => ∑ n ∈ s, ‖U n‖^2) atTop (𝓝 (∑' n : ℤ, ‖U n‖^2)) :=
    hf.hasSum
  have hev : ∀ᶠ s : Finset ℤ in atTop,
      dist (∑ n ∈ s, ‖U n‖^2) (∑' n : ℤ, ‖U n‖^2) < r^2/4 :=
    (Metric.tendsto_nhds.mp hconv) (r^2/4) (by positivity)
  obtain ⟨s, hs⟩ := hev.exists
  have htail : (∑' x : ↑(((s : Set ℤ))ᶜ), ‖U (x : ℤ)‖^2) < r^2/4 := by
    have hle : (∑ n ∈ s, ‖U n‖^2) ≤ ∑' n : ℤ, ‖U n‖^2 :=
      hf.sum_le_tsum s (fun n _ => by positivity)
    have hsp := hf.sum_add_tsum_compl (s := s)
    have hd : dist (∑ n ∈ s, ‖U n‖^2) (∑' n : ℤ, ‖U n‖^2) < r^2/4 := hs
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hle)] at hd
    linarith
  set η : ℝ := r / (2 * ((s.card : ℝ) + 1)) with hηdef
  have hηpos : 0 < η := by rw [hηdef]; positivity
  have hchoice : ∀ i : {i : ℤ // i ∈ s}, ∃ q : ℚ × ℚ,
      ‖U (i:ℤ) - (((q.1 : ℚ) : ℂ) + (((q.2 : ℚ) : ℂ)) * Complex.I)‖ < η :=
    fun i => dense_gaussianRationals (U (i:ℤ)) hηpos
  choose q hq using hchoice
  set φ : (Σ s : Finset ℤ, (s → ℚ × ℚ)) := ⟨s, fun i => q i⟩ with hφ
  have hφ1 : φ.1 = s := rfl
  have hφ2 : ∀ (i : ℤ) (h : i ∈ s), φ.2 ⟨i, h⟩ = q ⟨i, h⟩ := fun i h => rfl
  refine ⟨φ, ?_⟩
  have hsumdiff : Summable (fun n : ℤ => ‖U n - gaussEll φ n‖ ^ 2) := by
    have h := (lp.memℓp (U - gaussEll φ)).summable (p := 2) (by norm_num)
    simpa [Real.rpow_two, lp.coeFn_sub] using h
  have hsplit := hsumdiff.sum_add_tsum_compl (s := s)
  have hon_s : (∑ i ∈ s, ‖U i - gaussEll φ i‖ ^ 2) ≤ (s.card : ℝ) * η^2 := by
    calc ∑ i ∈ s, ‖U i - gaussEll φ i‖ ^ 2 ≤ ∑ i ∈ s, η^2 := by
          apply Finset.sum_le_sum
          intro i hi
          have hgi : gaussEll φ i = (((q ⟨i,hi⟩).1 : ℚ) : ℂ) + (((q ⟨i,hi⟩).2 : ℚ) : ℂ) * Complex.I := by
            simp [gaussEll, gaussVec, hi, hφ1, hφ2]
          rw [hgi]
          exact le_of_lt (pow_lt_pow_left₀ (hq ⟨i, hi⟩)
            (norm_nonneg (U i - ((((q ⟨i,hi⟩).1 : ℚ) : ℂ) + (((q ⟨i,hi⟩).2 : ℚ) : ℂ) * Complex.I)))
            (by norm_num))
      _ = (s.card : ℝ) * η^2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hon_tail : (∑' x : ↑(((s : Set ℤ))ᶜ), ‖U (x : ℤ) - gaussEll φ (x : ℤ)‖ ^ 2) < r^2/4 := by
    have heq : (∑' x : ↑(((s : Set ℤ))ᶜ), ‖U (x : ℤ) - gaussEll φ (x : ℤ)‖ ^ 2)
        = (∑' x : ↑(((s : Set ℤ))ᶜ), ‖U (x : ℤ)‖ ^ 2) := by
      apply tsum_congr
      intro n
      have hn : (n : ℤ) ∉ s := n.2
      have hz : gaussEll φ (n : ℤ) = 0 := by simp [gaussEll, gaussVec, hφ1, hn]
      rw [hz, sub_zero]
    rw [heq]; exact htail
  have hcard : (s.card : ℝ) * η^2 < r^2/4 := by
    have hc1 : (0:ℝ) < (s.card : ℝ) + 1 := by positivity
    have hratio : (s.card : ℝ) / ((s.card : ℝ) + 1)^2 < 1 := by
      rw [div_lt_one (by positivity)]
      have hc : (0:ℝ) ≤ (s.card : ℝ) := by positivity
      nlinarith
    have hη2 : (s.card : ℝ) * η^2 = (r^2/4) * ((s.card : ℝ) / ((s.card : ℝ) + 1)^2) := by
      have hrne : r ≠ 0 := ne_of_gt hr
      have hcne : ((s.card : ℝ) + 1) ≠ 0 := by positivity
      rw [hηdef]
      field_simp
      ring
    rw [hη2]
    calc (r^2/4) * ((s.card : ℝ) / ((s.card : ℝ) + 1)^2) < (r^2/4) * 1 := by
          exact mul_lt_mul_of_pos_left hratio (by positivity)
      _ = r^2/4 := by ring
  have htot : (∑' n : ℤ, ‖U n - gaussEll φ n‖ ^ 2) < r^2/2 := by
    rw [← hsplit]
    linarith
  have hnorm : ‖U - gaussEll φ‖ ^ 2 = ∑' n : ℤ, ‖U n - gaussEll φ n‖ ^ 2 := by
    have h := lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : ℤ => ℂ) (by norm_num)
      (U - gaussEll φ)
    simp only [lp.coeFn_sub] at h
    simpa [Real.rpow_two] using h
  rw [dist_eq_norm]
  have hx2 : ‖U - gaussEll φ‖ ^ 2 < r^2 := by rw [hnorm]; nlinarith [htot, hr]
  rw [sq_lt_sq, abs_of_nonneg (norm_nonneg _), abs_of_nonneg hr.le] at hx2
  exact hx2

theorem ellTwo_countableDense : ∃ D : Set EllTwo, D.Countable ∧ Dense D := by
  refine ⟨Set.range gaussEll, Set.countable_range gaussEll, ?_⟩
  rw [Metric.dense_iff]
  intro U r hr
  obtain ⟨φ, hφ⟩ := gaussEll_approx U hr
  exact ⟨gaussEll φ, Metric.mem_ball.mpr (by rw [dist_comm]; exact hφ), ⟨φ, rfl⟩⟩

lemma star_solution_aux {a : ℤ → ℝ} {E : ℝ} {u : ℤ → ℂ}
    (hu : ∀ n : ℤ, u (n+1) + u (n-1) + (a n : ℂ) * u n = (E:ℂ) * u n) :
    ∀ n : ℤ, star (u (n+1)) + star (u (n-1)) + (a n : ℂ) * star (u n) = (E:ℂ) * star (u n) := by
  intro n
  have h : star (u (n+1)) + star (u (n-1)) + star (u n) * (a n : ℂ) = star (u n) * (E:ℂ) := by
    have hh := congrArg star (hu n)
    simpa [star_add, star_mul] using hh
  calc star (u (n+1)) + star (u (n-1)) + (a n : ℂ) * star (u n)
      = star (u (n+1)) + star (u (n-1)) + star (u n) * (a n : ℂ) := by ring
    _ = star (u n) * (E:ℂ) := h
    _ = (E:ℂ) * star (u n) := by ring

lemma wronskian_bilinear_aux {a : ℤ → ℝ} {E E' : ℝ} {u v : ℤ → ℂ}
    (hu : ∀ n : ℤ, u (n+1) + u (n-1) + (a n : ℂ) * u n = (E:ℂ) * u n)
    (hv : ∀ n : ℤ, v (n+1) + v (n-1) + (a n : ℂ) * v n = (E':ℂ) * v n)
    (huℓ : Memℓp u 2) (hvℓ : Memℓp v 2) (hEE : E ≠ E') :
    ∑' n : ℤ, u n * v n = 0 := by
  have hu2 : Summable (fun n : ℤ => ‖u n‖ ^ 2) := by
    simpa [Real.rpow_two] using huℓ.summable (p := 2) (by norm_num)
  have hv2 : Summable (fun n : ℤ => ‖v n‖ ^ 2) := by
    simpa [Real.rpow_two] using hvℓ.summable (p := 2) (by norm_num)
  have hv2' : Summable (fun n : ℤ => ‖v (n+1)‖ ^ 2) := by
    have h := (Equiv.summable_iff (Equiv.addRight (1:ℤ)) (f := fun n : ℤ => ‖v n‖^2)).mpr hv2
    simpa [Function.comp_def] using h
  have hu2' : Summable (fun n : ℤ => ‖u (n+1)‖ ^ 2) := by
    have h := (Equiv.summable_iff (Equiv.addRight (1:ℤ)) (f := fun n : ℤ => ‖u n‖^2)).mpr hu2
    simpa [Function.comp_def] using h
  have hprod1 : Summable (fun n : ℤ => ‖u n‖ * ‖v (n+1)‖) :=
    Summable.of_nonneg_of_le (fun n => by positivity)
      (fun n => by nlinarith [sq_nonneg (‖u n‖ - ‖v (n+1)‖)])
      ((hu2.add hv2').div_const 2)
  have hprod2 : Summable (fun n : ℤ => ‖u (n+1)‖ * ‖v n‖) :=
    Summable.of_nonneg_of_le (fun n => by positivity)
      (fun n => by nlinarith [sq_nonneg (‖u (n+1)‖ - ‖v n‖)])
      ((hu2'.add hv2).div_const 2)
  have hgnorm : Summable (fun n : ℤ => ‖u n * v (n+1) - u (n+1) * v n‖) := by
    apply Summable.of_nonneg_of_le (fun n => by positivity) _ (hprod1.add hprod2)
    intro n
    simpa only [norm_mul] using norm_sub_le (u n * v (n+1)) (u (n+1) * v n)
  have hgsum : Summable (fun n : ℤ => u n * v (n+1) - u (n+1) * v n) := hgnorm.of_norm
  have hgsum' : Summable (fun n : ℤ => (fun k : ℤ => u k * v (k+1) - u (k+1) * v k) (n+1)) := by
    have h := (Equiv.summable_iff (Equiv.addRight (1:ℤ))
      (f := fun k : ℤ => u k * v (k+1) - u (k+1) * v k)).mpr hgsum
    simpa [Function.comp_def] using h
  have hpt : ∀ n : ℤ, (fun k : ℤ => u k * v (k+1) - u (k+1) * v k) (n+1)
      - (fun k : ℤ => u k * v (k+1) - u (k+1) * v k) n
      = (E' - E) * (u (n+1) * v (n+1)) := by
    intro n
    have h1 : u (n+2) = ((E:ℂ) - (a (n+1) : ℂ)) * u (n+1) - u n := by
      have h := hu (n+1)
      rw [show (n+1)+1 = n+2 by ring, show (n+1)-1 = n by ring] at h
      linear_combination h
    have h2 : v (n+2) = ((E':ℂ) - (a (n+1) : ℂ)) * v (n+1) - v n := by
      have h := hv (n+1)
      rw [show (n+1)+1 = n+2 by ring, show (n+1)-1 = n by ring] at h
      linear_combination h
    simp only []
    rw [show n + 1 + 1 = n + 2 by ring, h1, h2]
    ring
  have hshift : (∑' n : ℤ, (fun k : ℤ => u k * v (k+1) - u (k+1) * v k) (n+1))
      = ∑' n : ℤ, (fun k : ℤ => u k * v (k+1) - u (k+1) * v k) n := by
    have h := Equiv.tsum_eq (Equiv.addRight (1:ℤ)) (fun k : ℤ => u k * v (k+1) - u (k+1) * v k)
    simpa [Function.comp_def] using h
  have htel : (∑' n : ℤ, ((fun k : ℤ => u k * v (k+1) - u (k+1) * v k) (n+1)
      - (fun k : ℤ => u k * v (k+1) - u (k+1) * v k) n)) = 0 := by
    rw [Summable.tsum_sub hgsum' hgsum, hshift, sub_self]
  have hrhs : (∑' n : ℤ, ((fun k : ℤ => u k * v (k+1) - u (k+1) * v k) (n+1)
      - (fun k : ℤ => u k * v (k+1) - u (k+1) * v k) n))
      = (E' - E) * (∑' n : ℤ, u n * v n) := by
    rw [tsum_congr hpt, tsum_mul_left]
    congr 1
    have h := Equiv.tsum_eq (Equiv.addRight (1:ℤ)) (fun k : ℤ => u k * v k)
    simpa [Function.comp_def] using h
  have hfin : (E' - E) * (∑' n : ℤ, u n * v n) = 0 := by rw [← hrhs, htel]
  have hneC : (E' : ℂ) ≠ (E : ℂ) := by exact_mod_cast (Ne.symm hEE)
  exact (mul_eq_zero.mp hfin).resolve_left (sub_ne_zero.mpr hneC)

lemma wronskian_orthogonal_aux {a : ℤ → ℝ} {E E' : ℝ} {u v : ℤ → ℂ}
    (hu : ∀ n : ℤ, u (n+1) + u (n-1) + (a n : ℂ) * u n = (E:ℂ) * u n)
    (hv : ∀ n : ℤ, v (n+1) + v (n-1) + (a n : ℂ) * v n = (E':ℂ) * v n)
    (huℓ : Memℓp u 2) (hvℓ : Memℓp v 2) (hEE : E ≠ E') :
    ∑' n : ℤ, star (u n) * v n = 0 := by
  have hu' := star_solution_aux hu
  have hmem : Memℓp (fun n : ℤ => star (u n)) 2 := memℓp_gen (by
    have h := huℓ.summable (p := 2) (by norm_num)
    simpa [norm_star] using h)
  simpa using wronskian_bilinear_aux hu' hv hmem hvℓ hEE

theorem countable_amo_general {a : ℤ → ℝ} :
    Set.Countable {Λ : ℝ | ∃ u : ℤ → ℂ, u ≠ 0 ∧ Summable (fun n : ℤ => ‖u n‖ ^ 2) ∧
      ∀ n : ℤ, u (n + 1) + u (n - 1) + ((a n - Λ : ℝ) : ℂ) * u n = 0} := by
  classical
  obtain ⟨D, hDcount, hDense⟩ := ellTwo_countableDense
  set S : Set ℝ := {Λ : ℝ | ∃ u : ℤ → ℂ, u ≠ 0 ∧ Summable (fun n : ℤ => ‖u n‖ ^ 2) ∧
      ∀ n : ℤ, u (n + 1) + u (n - 1) + ((a n - Λ : ℝ) : ℂ) * u n = 0} with hS
  change Set.Countable S
  have existsUnit : ∀ Λ : ℝ, Λ ∈ S → ∃ U : EllTwo, ‖U‖ = 1 ∧ U ≠ 0 ∧
        (∀ n : ℤ, U (n+1) + U (n-1) + (a n : ℂ) * U n = (Λ : ℂ) * U n) := by
    intro Λ hΛ
    rw [hS] at hΛ
    obtain ⟨u, hu0, hsum, hrec⟩ := hΛ
    have hm : Memℓp u 2 := memℓp_gen (by simpa [Real.rpow_two] using hsum)
    let U0 : EllTwo := ⟨u, hm⟩
    have hU0ne : U0 ≠ 0 := by
      intro hz
      refine hu0 ?_
      exact congrArg (fun w : EllTwo => (w : ℤ → ℂ)) hz
    have hrec0 : ∀ n : ℤ, U0 (n+1) + U0 (n-1) + (a n : ℂ) * U0 n = (Λ : ℂ) * U0 n := by
      intro n
      have h := hrec n
      change u (n+1) + u (n-1) + (a n : ℂ) * u n = (Λ : ℂ) * u n
      rw [Complex.ofReal_sub] at h
      linear_combination h
    have hnorm_ne : ‖U0‖ ≠ 0 := norm_ne_zero_iff.mpr hU0ne
    refine ⟨(((‖U0‖ : ℝ) : ℂ))⁻¹ • U0, ?_, ?_, ?_⟩
    · rw [norm_smul]
      have hc : ‖(((‖U0‖ : ℝ) : ℂ))⁻¹‖ = ‖U0‖⁻¹ := by simp
      rw [hc]
      exact inv_mul_cancel₀ hnorm_ne
    · intro hz
      rcases (smul_eq_zero.mp hz) with h | h
      · exact (inv_ne_zero (by exact_mod_cast hnorm_ne)) h
      · exact hU0ne h
    · intro n
      have h := hrec0 n
      rw [lp.coeFn_smul]
      simp only [Pi.smul_apply, smul_eq_mul]
      linear_combination ((((‖U0‖ : ℝ) : ℂ))⁻¹) * h
  let V : ℝ → EllTwo := fun Λ => if h : Λ ∈ S then Classical.choose (existsUnit Λ h) else 0
  have Vnorm : ∀ Λ (h : Λ ∈ S), ‖V Λ‖ = 1 := by
    intro Λ h; simpa [V, dif_pos h] using (Classical.choose_spec (existsUnit Λ h)).1
  have Vne : ∀ Λ (h : Λ ∈ S), V Λ ≠ 0 := by
    intro Λ h; simpa [V, dif_pos h] using (Classical.choose_spec (existsUnit Λ h)).2.1
  have Vrec : ∀ Λ (h : Λ ∈ S), ∀ n : ℤ,
      V Λ (n+1) + V Λ (n-1) + (a n : ℂ) * V Λ n = (Λ : ℂ) * V Λ n := by
    intro Λ h; simpa [V, dif_pos h] using (Classical.choose_spec (existsUnit Λ h)).2.2
  have Vorth : ∀ Λ Λ' (hΛ : Λ ∈ S) (hΛ' : Λ' ∈ S), Λ ≠ Λ' → inner ℂ (V Λ) (V Λ') = 0 := by
    intro Λ Λ' hΛ hΛ' hne
    have h := wronskian_orthogonal_aux (Vrec Λ hΛ) (Vrec Λ' hΛ')
      (lp.memℓp (V Λ)) (lp.memℓp (V Λ')) hne
    have hgoal : (∑' n : ℤ, inner ℂ ((V Λ) n) ((V Λ') n))
        = ∑' n : ℤ, star ((V Λ) n) * ((V Λ') n) := by
      apply tsum_congr
      intro n
      rw [RCLike.inner_apply]
      exact mul_comm _ _
    rw [lp.inner_eq_tsum, hgoal]
    exact h
  have Vsep : ∀ Λ Λ' (hΛ : Λ ∈ S) (hΛ' : Λ' ∈ S), Λ ≠ Λ' → 1 < dist (V Λ) (V Λ') := by
    intro Λ Λ' hΛ hΛ' hne
    have ho := Vorth Λ Λ' hΛ hΛ' hne
    have h1 := Vnorm Λ hΛ
    have h2 := Vnorm Λ' hΛ'
    rw [dist_eq_norm]
    have hsq : ‖V Λ - V Λ'‖ ^ 2 = 2 := by
      rw [norm_sub_sq (𝕜 := ℂ), ho]
      simp only [map_zero, mul_zero, sub_zero]
      rw [h1, h2]
      norm_num
    nlinarith [norm_nonneg (V Λ - V Λ'), hsq]
  have key : ∀ Λ (h : Λ ∈ S), ∃ d : EllTwo, d ∈ D ∧ dist (V Λ) d < 1/2 :=
    fun Λ _ => hDense.exists_dist_lt (V Λ) (by norm_num)
  let d : ℝ → EllTwo := fun Λ => if h : Λ ∈ S then Classical.choose (key Λ h) else 0
  have dmem : ∀ Λ (h : Λ ∈ S), d Λ ∈ D := by
    intro Λ h; simpa [d, dif_pos h] using (Classical.choose_spec (key Λ h)).1
  have dclose : ∀ Λ (h : Λ ∈ S), dist (V Λ) (d Λ) < 1/2 := by
    intro Λ h; simpa [d, dif_pos h] using (Classical.choose_spec (key Λ h)).2
  have dinj : ∀ Λ Λ' (hΛ : Λ ∈ S) (hΛ' : Λ' ∈ S), d Λ = d Λ' → Λ = Λ' := by
    intro Λ Λ' hΛ hΛ' heq
    by_contra hne
    have hsep := Vsep Λ Λ' hΛ hΛ' hne
    have hc1 := dclose Λ hΛ
    have hc2 := dclose Λ' hΛ'
    rw [heq] at hc1
    have hlt : dist (V Λ) (V Λ') < 1 := by
      calc dist (V Λ) (V Λ') ≤ dist (V Λ) (d Λ') + dist (d Λ') (V Λ') := dist_triangle _ _ _
        _ = dist (V Λ) (d Λ') + dist (V Λ') (d Λ') := by rw [dist_comm (d Λ') (V Λ')]
        _ < 1/2 + 1/2 := by linarith
        _ = 1 := by norm_num
    linarith
  have ginj : Function.Injective (fun x : S => (⟨d x, dmem x x.2⟩ : {y : EllTwo // y ∈ D})) := by
    intro x y hxy
    have h1 : d x = d y := congrArg Subtype.val hxy
    exact Subtype.ext (dinj x y x.2 y.2 h1)
  exact @Function.Injective.countable S {y : EllTwo // y ∈ D} hDcount _ ginj

/-- **The Ten Martini Problem, Puig's component**: the set of real energies for which the
almost Mathieu recurrence admits a nonzero square summable solution is countable. -/
theorem countable_l2_solutions (α lam θ : ℝ) (hlam : lam ≠ 0) :
    Set.Countable {Λ : ℝ | ∃ u : ℤ → ℂ, u ≠ 0 ∧ Summable (fun n : ℤ => ‖u n‖ ^ 2) ∧
      ∀ n : ℤ, u (n + 1) + u (n - 1)
        + ((2 / lam) * Real.cos (2 * Real.pi * ((n : ℝ) * α + θ)) - Λ) * u n = 0} := by
  have _h0 : lam ≠ 0 := hlam
  simpa using countable_amo_general
    (a := fun n : ℤ => (2 / lam) * Real.cos (2 * Real.pi * ((n : ℝ) * α + θ)))

end Work.TMPuig
