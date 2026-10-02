import Mathlib
import Submission.Work.FBif.Prep
import Submission.Work.FBif.five_telescope

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Polynomial
open LeanEval.ComplexAnalysis (Tantibar)

set_option linter.unusedVariables false

namespace Work.FBif

set_option maxHeartbeats 1000000

noncomputable section

/-! ## Polynomial bounds on a disc -/

private lemma norm_eval_le_sum (P : ℂ[X]) (z : ℂ) {M : ℝ} (hz : ‖z‖ ≤ M) :
    ‖P.eval z‖ ≤ ∑ i ∈ P.support, ‖P.coeff i‖ * M ^ i := by
  rw [Polynomial.eval_eq_sum]
  exact le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => by
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) hz i) (norm_nonneg _))

private lemma norm_eval_sub_le (P : ℂ[X]) {u v : ℂ} {M : ℝ} (hu : ‖u‖ ≤ M) (hv : ‖v‖ ≤ M) :
    ‖P.eval u - P.eval v‖
      ≤ (∑ i ∈ P.derivative.support, ‖P.derivative.coeff i‖ * M ^ i) * ‖u - v‖ := by
  set C := ∑ i ∈ P.derivative.support, ‖P.derivative.coeff i‖ * M ^ i with hC
  have hbound : ∀ x ∈ Metric.closedBall (0 : ℂ) M, ‖P.derivative.eval x‖ ≤ C := by
    intro x hx
    rw [hC]
    rw [Polynomial.eval_eq_sum]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg x)
      (by rwa [Metric.mem_closedBall, dist_zero_right] at hx) i) (norm_nonneg _)
  have hmemu : u ∈ Metric.closedBall (0 : ℂ) M := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hu
  have hmemv : v ∈ Metric.closedBall (0 : ℂ) M := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hv
  have hmain := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun z : ℂ => P.eval z) (f' := fun z => P.derivative.eval z)
    (s := Metric.closedBall (0 : ℂ) M) (C := C) (x := v) (y := u)
    (fun x _ => (Polynomial.hasDerivAt P x).hasDerivWithinAt) hbound
    (convex_closedBall 0 M) hmemv hmemu
  simpa [hC] using hmain

private lemma norm_eval_le_sq_mul (P : ℂ[X]) (a : ℂ) (R : ℂ[X]) (hPR : P = (X - C a) ^ 2 * R)
    (z : ℂ) {M : ℝ} (hz : ‖z‖ ≤ M) :
    ‖P.eval z‖ ≤ (∑ i ∈ R.support, ‖R.coeff i‖ * M ^ i) * ‖z - a‖ ^ 2 := by
  have hR : ‖R.eval z‖ ≤ ∑ i ∈ R.support, ‖R.coeff i‖ * M ^ i := norm_eval_le_sum R z hz
  have heval : P.eval z = (z - a) ^ 2 * R.eval z := by
    rw [hPR]
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C]
  rw [heval, norm_mul, norm_pow]
  calc ‖z - a‖ ^ 2 * ‖R.eval z‖
      ≤ ‖z - a‖ ^ 2 * (∑ i ∈ R.support, ‖R.coeff i‖ * M ^ i) :=
        mul_le_mul_of_nonneg_left hR (by positivity)
    _ = (∑ i ∈ R.support, ‖R.coeff i‖ * M ^ i) * ‖z - a‖ ^ 2 := by ring

/-! ## Iterated Lipschitz bound with a growing radius schedule -/

/-- This is the specialised form of the colleague-proved
`Work.FBif.iterate_bound` (`Submission/Work/FBif/iterate_bound.lean`) used here: the map and
Lipschitz conditions `hmap`/`hlip` are required only at the radii `i ≤ 5` that the application
actually reaches (`F = perturb c q ε` satisfies `‖F u‖ ≤ Rad i ^ 2 + ‖c‖ + ε * Q i`, and the
smallness condition `ε * Q i ≤ 1` holds for the finitely many `i ≤ 5` but *not* for all `i`,
since `Q i` grows with `Rad i`).  The proof is the same induction as in `iterate_bound`. -/
private lemma iterate_bound_aux (F : ℂ → ℂ) (Rad : ℕ → ℝ) (C : ℕ → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hmap : ∀ i, i ≤ 5 → ∀ u : ℂ, ‖u‖ ≤ Rad i → ‖F u‖ ≤ Rad (i + 1))
    (hlip : ∀ i, i ≤ 5 → ∀ u v : ℂ, ‖u‖ ≤ Rad i → ‖v‖ ≤ Rad i →
      ‖F u - F v‖ ≤ C i * ‖u - v‖)
    {u v : ℂ} (hu : ‖u‖ ≤ Rad 0) (hv : ‖v‖ ≤ Rad 0) {k : ℕ} (hk : k ≤ 5) :
    ‖(F^[k]) u - (F^[k]) v‖ ≤ (∏ i ∈ Finset.range k, C i) * ‖u - v‖ := by
  have key : ∀ k : ℕ, k ≤ 5 →
      (‖(F^[k]) u - (F^[k]) v‖ ≤ (∏ i ∈ Finset.range k, C i) * ‖u - v‖)
        ∧ ‖(F^[k]) u‖ ≤ Rad k ∧ ‖(F^[k]) v‖ ≤ Rad k := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨?_, hu, hv⟩
      simp [Function.iterate_zero]
    | succ k ih =>
      intro hk
      obtain ⟨hd, hu1, hv1⟩ := ih (by omega)
      refine ⟨?_, ?_, ?_⟩
      · simp only [Function.iterate_succ_apply']
        calc ‖F ((F^[k]) u) - F ((F^[k]) v)‖ ≤ C k * ‖(F^[k]) u - (F^[k]) v‖ :=
              hlip k (by omega) _ _ hu1 hv1
          _ ≤ C k * ((∏ i ∈ Finset.range k, C i) * ‖u - v‖) :=
              mul_le_mul_of_nonneg_left hd (hC k)
          _ = (∏ i ∈ Finset.range (k + 1), C i) * ‖u - v‖ := by
              rw [Finset.prod_range_succ]; ring
      · simp only [Function.iterate_succ_apply']; exact hmap k (by omega) _ hu1
      · simp only [Function.iterate_succ_apply']; exact hmap k (by omega) _ hv1
  exact (key k hk).1

/-! ## The telescoping identity in the form used below -/

private lemma layer_eq (f g : ℂ → ℂ) (j : ℕ) (hj : j ≤ 4) (y : ℂ) :
    (f^[5 - j]) ((g^[j]) y) - (f^[5 - (j + 1)]) ((g^[j + 1]) y)
      = (f^[4 - j]) (f ((g^[j]) y)) - (f^[4 - j]) (g ((g^[j]) y)) := by
  rw [show 5 - j = (4 - j) + 1 from by omega, Function.iterate_succ_apply,
    show 5 - (j + 1) = 4 - j from by omega, Function.iterate_succ_apply']

private lemma five_telescope_aux (f g : ℂ → ℂ) (x y : ℂ) :
    ((f^[5]) x - (g^[5]) x) - ((f^[5]) y - (g^[5]) y)
      = ∑ j ∈ Finset.range 5,
          (((f^[4 - j]) (f ((g^[j]) x)) - (f^[4 - j]) (g ((g^[j]) x)))
            - ((f^[4 - j]) (f ((g^[j]) y)) - (f^[4 - j]) (g ((g^[j]) y)))) := by
  -- the telescoping `five_telescope` of `Submission/Work/FBif/five_telescope.lean`,
  -- rewritten by `layer_eq` into the `4 - j` form used below
  rw [five_telescope f g x y]
  refine Finset.sum_congr rfl fun j hj => ?_
  have h4 : j ≤ 4 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [layer_eq f g j h4 x, layer_eq f g j h4 y]

/-- **The perturbative part of the HS estimate: the perturbed fifth iterate is `p^[5]` up to
`ε q(z₄) + O(ε‖w‖²)`.**

Let `p := Tantibar c`, `f_ε := perturb c q ε = p + ε q` with `q = P(z̄)`, and let
`Δ_ε(x) := f_ε^[5] x - p^[5] x`.  Assume `p^[5](z₁) = z₁` (`hper`) and that `P` vanishes to
second order at `z̄₀, …, z̄₃` (`hvan`) and that `P - P(z̄₄)` vanishes to second order at `z̄₄`
(`hvan4`) — exactly the first two `GoodPerturbation` conditions.  Then there are
`K, δ, ε₀ > 0` with

`‖Δ_ε(z₁+w) - Δ_ε(z₁) - 0‖ ≤ K ε ‖w‖²`  for `0 < ε < ε₀`, `‖w‖ ≤ δ`.

Together with `perturb_iterate_fifth_at` (`Δ_ε(z₁) = ε q(z₄)` exactly) this is the whole
perturbative content of the HS expansion: the perturbed iterate differs from the unperturbed
one by an `O(ε‖w‖²)` term and a constant `ε q(z₄)`.

Route (Hubbard–Schleicher; telescoping).  For arbitrary maps `f, g`,

`f^[5] x - g^[5] x = Σ_{j<5} ( f^[4-j] (f (g^[j] x)) - f^[4-j] (g (g^[j] x)) )`

(induction on the exponent).  Here `g = p`, `f = f_ε` and `f y - p y = ε q y`.  The `j`-th term
of `Δ_ε` is `f_ε^[4-j](p^[j+1] x + ε q(p^[j] x)) - f_ε^[4-j](p^[j+1] x)`, which at `x = z₁`
vanishes for `j ≤ 3` (because `q(z_j) = 0`) and equals `ε q(p^[4] x)` for `j = 4`.  Hence

* `j ≤ 3`: `‖term_j(x)‖ ≤ Lip(f_ε^[4-j]) · ε · ‖q(p^j x)‖` and
  `‖q(p^j x)‖ = ‖P(star (p^j x))‖ ≤ C ‖p^j x - z_j‖² ≤ C (Lip p^j)² ‖w‖²`;
* `j = 4`: `term_4(x) - term_4(z₁) = ε (q(p^4 x) - q(z₄))`, bounded by
  `ε C' ‖p^4 x - z₄‖² ≤ ε C' (Lip p^4)² ‖w‖²`.

The Lipschitz constants are obtained explicitly: for `M ≥ 0` and `x, y ∈ ball 0 M`,
`‖f_ε x - f_ε y‖ ≤ (2M + L_P(M)) ‖x - y‖` where `L_P(M) := Σ k ‖P.coeff k‖ M^(k-1)`
(since `u^k - v^k = (u-v) Σ_{i<k} u^i v^(k-1-i)`), and iterating from a ball that contains
`z₁ + w` (take `M₀ > ‖z₁‖` and `M_{k+1} := M_k² + ‖c‖ + Σ_i ‖P.coeff i‖ M_k^i`) gives a uniform
bound.  The two double-vanishing bounds are `(X - C a)² ∣ P → ∃ C, ∀ z, ‖P.eval z‖ ≤ C ‖z-a‖²`
(write `P = (X - C a)² * R` and bound `R.eval` on a ball).

(Note: the hypothesis `hper` is *not* needed for this estimate — no step of the telescoping
argument uses `p^[5] z₁ = z₁`; it is kept because the statement was requested in this form.) -/
theorem perturbDiffBound (c z₁ : ℂ) (P : Polynomial ℂ)
    (hper : (LeanEval.ComplexAnalysis.Tantibar c)^[5] z₁ = z₁)
    (hvan : ∀ j : ℕ, j ≤ 3 →
      (Polynomial.X - Polynomial.C (star (Work.FBif.cyclePt c z₁ j))) ^ 2 ∣ P)
    (hvan4 : (Polynomial.X - Polynomial.C (star (Work.FBif.cyclePt c z₁ 4))) ^ 2 ∣
      (P - Polynomial.C (P.eval (star (Work.FBif.cyclePt c z₁ 4))))) :
    ∃ K : ℝ, 0 < K ∧ ∃ δ : ℝ, 0 < δ ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ w : ℂ, ‖w‖ ≤ δ →
        ‖(Work.FBif.perturb c (fun z => P.eval (star z)) ε)^[5] (z₁ + w)
          - (LeanEval.ComplexAnalysis.Tantibar c)^[5] (z₁ + w)
          - ((Work.FBif.perturb c (fun z => P.eval (star z)) ε)^[5] z₁
              - (LeanEval.ComplexAnalysis.Tantibar c)^[5] z₁)‖
        ≤ K * ε * ‖w‖ ^ 2 := by
  -- ===== the parabolic cycle and the radius schedule =====
  set Z : ℝ := ∑ j ∈ Finset.range 5, ‖cyclePt c z₁ j‖ with hZ
  have hZnn : 0 ≤ Z := by
    rw [hZ]
    exact Finset.sum_nonneg fun j _ => norm_nonneg _
  have hZle : ∀ j ∈ Finset.range 5, ‖cyclePt c z₁ j‖ ≤ Z := by
    intro j hj
    rw [hZ]
    exact Finset.single_le_sum (fun i _ => norm_nonneg _) hj
  have hz₁Z : ‖z₁‖ ≤ Z := by
    have h := hZle 0 (by simp)
    rwa [show cyclePt c z₁ 0 = z₁ from rfl] at h
  set M : ℝ := Z + 3 with hMdef
  have hMpos : 0 < M := by rw [hMdef]; linarith
  have hMnn : 0 ≤ M := hMpos.le
  set Rad : ℕ → ℝ := fun k => (fun r : ℝ => max r (r ^ 2 + ‖c‖ + 1))^[k] M with hRad
  have hRad_zero : Rad 0 = M := by simp [hRad]
  have hRad_succ : ∀ k : ℕ, Rad (k + 1) = max (Rad k) (Rad k ^ 2 + ‖c‖ + 1) := by
    intro k
    simp only [hRad, Function.iterate_succ_apply']
  have hRad_mono : ∀ k : ℕ, M ≤ Rad k := by
    intro k
    induction k with
    | zero => rw [hRad_zero]
    | succ k ih => rw [hRad_succ]; exact le_trans ih (le_max_left _ _)
  have hRadnn : ∀ k : ℕ, 0 ≤ Rad k := fun k => le_trans hMnn (hRad_mono k)
  -- ===== bounds for the perturbing polynomial =====
  set Q : ℕ → ℝ := fun i => ∑ k ∈ P.support, ‖P.coeff k‖ * (Rad i) ^ k with hQ
  have hQnn : ∀ i : ℕ, 0 ≤ Q i := by
    intro i
    rw [hQ]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (norm_nonneg _) (pow_nonneg (hRadnn i) k)
  have hQbd : ∀ i : ℕ, ∀ u : ℂ, ‖u‖ ≤ Rad i → ‖P.eval (star u)‖ ≤ Q i := by
    intro i u hu
    have h := norm_eval_le_sum P (star u) (by simpa using hu)
    simpa only [hQ] using h
  set L : ℕ → ℝ := fun i => ∑ k ∈ P.derivative.support, ‖P.derivative.coeff k‖ * (Rad i) ^ k
    with hL
  have hLnn : ∀ i : ℕ, 0 ≤ L i := by
    intro i
    rw [hL]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (norm_nonneg _) (pow_nonneg (hRadnn i) k)
  have hLbd : ∀ i : ℕ, ∀ u v : ℂ, ‖u‖ ≤ Rad i → ‖v‖ ≤ Rad i →
      ‖P.eval (star u) - P.eval (star v)‖ ≤ L i * ‖u - v‖ := by
    intro i u v hu hv
    have h := norm_eval_sub_le P (by simpa using hu : ‖star u‖ ≤ Rad i)
      (by simpa using hv : ‖star v‖ ≤ Rad i)
    have h2 : ‖star u - star v‖ = ‖u - v‖ := by rw [← star_sub, norm_star]
    have h3 : ‖P.eval (star u) - P.eval (star v)‖ ≤ L i * ‖star u - star v‖ := by
      simpa only [hL] using h
    rwa [h2] at h3
  -- ===== the double-vanishing data =====
  have hex : ∀ j : ℕ, ∃ R : ℂ[X],
      (j ≤ 3 → P = (X - C (star (cyclePt c z₁ j))) ^ 2 * R) ∧
      (j = 4 → P - C (P.eval (star (cyclePt c z₁ 4))) =
          (X - C (star (cyclePt c z₁ 4))) ^ 2 * R) := by
    intro j
    by_cases h1 : j ≤ 3
    · obtain ⟨R, hR⟩ := hvan j h1
      exact ⟨R, fun _ => hR, fun h => absurd h (by omega)⟩
    · by_cases h2 : j = 4
      · obtain ⟨R, hR⟩ := hvan4
        exact ⟨R, fun h => absurd h h1, fun _ => hR⟩
      · exact ⟨0, fun h => absurd h h1, fun h => absurd h h2⟩
  choose R hR using hex
  set S : ℕ → ℝ := fun j => ∑ i ∈ (R j).support, ‖(R j).coeff i‖ * M ^ i with hSdef
  have hSnn : ∀ j : ℕ, 0 ≤ S j := by
    intro j
    rw [hSdef]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (pow_nonneg hMnn i)
  have hS3 : ∀ j : ℕ, j ≤ 3 → ∀ z : ℂ, ‖z‖ ≤ M →
      ‖P.eval z‖ ≤ S j * ‖z - star (cyclePt c z₁ j)‖ ^ 2 := by
    intro j hj z hz
    have h := norm_eval_le_sq_mul P (star (cyclePt c z₁ j)) (R j) ((hR j).1 hj) z hz
    simpa only [hSdef] using h
  have hS4 : ∀ z : ℂ, ‖z‖ ≤ M →
      ‖P.eval z - P.eval (star (cyclePt c z₁ 4))‖
        ≤ S 4 * ‖z - star (cyclePt c z₁ 4)‖ ^ 2 := by
    intro z hz
    have h := norm_eval_le_sq_mul (P - C (P.eval (star (cyclePt c z₁ 4))))
      (star (cyclePt c z₁ 4)) (R 4) ((hR 4).2 rfl) z hz
    have hev : (P - C (P.eval (star (cyclePt c z₁ 4)))).eval z
        = P.eval z - P.eval (star (cyclePt c z₁ 4)) := by simp
    rw [hev] at h
    simpa only [hSdef] using h
  -- ===== the Lipschitz schedules =====
  set PLip : ℕ → ℝ := fun k => ∏ i ∈ Finset.range k, (2 * Rad i) with hPLipdef
  set FLip : ℕ → ℝ := fun k => ∏ i ∈ Finset.range k, (2 * Rad i + 1) with hFLipdef
  have hPLipnn : ∀ k : ℕ, 0 ≤ PLip k := by
    intro k
    rw [hPLipdef]
    exact Finset.prod_nonneg fun i _ => mul_nonneg (by norm_num) (hRadnn i)
  have hFLipnn : ∀ k : ℕ, 0 ≤ FLip k := by
    intro k
    rw [hFLipdef]
    exact Finset.prod_nonneg fun i _ => add_nonneg (mul_nonneg (by norm_num) (hRadnn i))
      (by norm_num)
  set Ptot : ℝ := 1 + ∑ k ∈ Finset.range 6, PLip k with hPtot
  have hPtot1 : 1 ≤ Ptot := by
    rw [hPtot]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun k _ => hPLipnn k)
  have hPtotpos : 0 < Ptot := lt_of_lt_of_le one_pos hPtot1
  have hPLiple : ∀ k : ℕ, k ≤ 5 → PLip k ≤ Ptot := by
    intro k hk
    have h1 : PLip k ≤ ∑ j ∈ Finset.range 6, PLip j :=
      Finset.single_le_sum (fun j _ => hPLipnn j) (Finset.mem_range.mpr (by omega))
    rw [hPtot]; linarith
  set Qtot : ℝ := 1 + ∑ i ∈ Finset.range 6, Q i with hQtot
  have hQtot1 : 1 ≤ Qtot := by
    rw [hQtot]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => hQnn i)
  have hQtotpos : 0 < Qtot := lt_of_lt_of_le one_pos hQtot1
  have hQle : ∀ i : ℕ, i ≤ 5 → Q i ≤ Qtot := by
    intro i hi
    have h1 : Q i ≤ ∑ j ∈ Finset.range 6, Q j :=
      Finset.single_le_sum (fun j _ => hQnn j) (Finset.mem_range.mpr (by omega))
    rw [hQtot]; linarith
  set Ltot : ℝ := 1 + ∑ i ∈ Finset.range 6, L i with hLtot
  have hLtot1 : 1 ≤ Ltot := by
    rw [hLtot]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => hLnn i)
  have hLtotpos : 0 < Ltot := lt_of_lt_of_le one_pos hLtot1
  have hLle : ∀ i : ℕ, i ≤ 5 → L i ≤ Ltot := by
    intro i hi
    have h1 : L i ≤ ∑ j ∈ Finset.range 6, L j :=
      Finset.single_le_sum (fun j _ => hLnn j) (Finset.mem_range.mpr (by omega))
    rw [hLtot]; linarith
  -- ===== the constants =====
  set coef : ℕ → ℝ := fun j => FLip (4 - j) * S j * (PLip j) ^ 2 with hcoefdef
  have hcoefnn : ∀ j : ℕ, 0 ≤ coef j := by
    intro j
    rw [hcoefdef]
    exact mul_nonneg (mul_nonneg (hFLipnn (4 - j)) (hSnn j)) (pow_nonneg (hPLipnn j) 2)
  set K : ℝ := (∑ j ∈ Finset.range 5, coef j) + 1 with hKdef
  have hKpos : 0 < K := by
    rw [hKdef]
    have h := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range 5) => hcoefnn j)
    linarith
  set δ : ℝ := 1 / Ptot with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact div_pos one_pos hPtotpos
  have hδle1 : δ ≤ 1 := by
    rw [hδdef]
    rw [div_le_one hPtotpos]
    exact hPtot1
  have hδPLip : ∀ k : ℕ, k ≤ 5 → PLip k * δ ≤ 1 := by
    intro k hk
    rw [hδdef, mul_one_div, div_le_one hPtotpos]
    exact hPLiple k hk
  set ε₀ : ℝ := 1 / (Qtot + Ltot) with hε₀def
  have hε₀pos : 0 < ε₀ := by
    rw [hε₀def]
    exact div_pos one_pos (by linarith)
  have hεQtot : ∀ ε : ℝ, 0 < ε → ε < ε₀ → ε * Qtot < 1 := by
    intro ε hε hlt
    rw [hε₀def] at hlt
    rw [lt_div_iff₀ (by linarith : (0 : ℝ) < Qtot + Ltot)] at hlt
    nlinarith [hLtotpos, hε]
  have hεLtot : ∀ ε : ℝ, 0 < ε → ε < ε₀ → ε * Ltot < 1 := by
    intro ε hε hlt
    rw [hε₀def] at hlt
    rw [lt_div_iff₀ (by linarith : (0 : ℝ) < Qtot + Ltot)] at hlt
    nlinarith [hQtotpos, hε]
  refine ⟨K, hKpos, δ, hδpos, ε₀, hε₀pos, ?_⟩
  intro ε hεpos hεε₀ w hw
  set F : ℂ → ℂ := perturb c (fun z => P.eval (star z)) ε with hF
  set G : ℂ → ℂ := Tantibar c with hG
  have hεnorm : ‖(ε : ℂ)‖ = ε := by simp [abs_of_pos hεpos]
  have hFG : ∀ y : ℂ, F y - G y = (ε : ℂ) * P.eval (star y) := by
    intro y
    rw [hF, hG, perturb_apply]
    ring
  have hGz₁ : ∀ j : ℕ, (G^[j]) z₁ = cyclePt c z₁ j := by
    intro j
    rw [hG]
    rfl
  have hGsucc : ∀ (j : ℕ) (y : ℂ), G ((G^[j]) y) = (G^[j + 1]) y := by
    intro j y
    rw [Function.iterate_succ_apply']
  have hFfix : ∀ j : ℕ, j ≤ 3 → F ((G^[j]) z₁) = G ((G^[j]) z₁) := by
    intro j hj
    have hzero : P.eval (star ((G^[j]) z₁)) = 0 := by
      rw [hGz₁ j]
      obtain ⟨R', hR'⟩ := hvan j hj
      rw [hR']
      simp
    have h := hFG ((G^[j]) z₁)
    rw [hzero, mul_zero] at h
    exact sub_eq_zero.mp h
  -- ===== the map and Lipschitz bounds =====
  have hGmap : ∀ i : ℕ, i ≤ 5 → ∀ u : ℂ, ‖u‖ ≤ Rad i → ‖G u‖ ≤ Rad (i + 1) := by
    intro i _ u hu
    have h1 : ‖G u‖ ≤ ‖u‖ ^ 2 + ‖c‖ := by
      rw [hG]
      calc ‖Tantibar c u‖ = ‖(star u) ^ 2 + c‖ := rfl
        _ ≤ ‖(star u) ^ 2‖ + ‖c‖ := norm_add_le _ _
        _ = ‖u‖ ^ 2 + ‖c‖ := by rw [norm_pow, norm_star]
    have h2 : ‖u‖ ^ 2 ≤ Rad i ^ 2 := pow_le_pow_left₀ (norm_nonneg u) hu 2
    have h3 : Rad i ^ 2 + ‖c‖ + 1 ≤ Rad (i + 1) := by
      rw [hRad_succ]
      exact le_max_right _ _
    linarith
  have hGlip : ∀ i : ℕ, i ≤ 5 → ∀ u v : ℂ, ‖u‖ ≤ Rad i → ‖v‖ ≤ Rad i →
      ‖G u - G v‖ ≤ (2 * Rad i) * ‖u - v‖ := by
    intro i _ u v hu hv
    have h1 : ‖G u - G v‖ ≤ (‖u‖ + ‖v‖) * ‖u - v‖ := by
      rw [hG]
      have hcongr : Tantibar c u - Tantibar c v = star (u ^ 2 - v ^ 2) := by
        show (star u) ^ 2 + c - ((star v) ^ 2 + c) = star (u ^ 2 - v ^ 2)
        rw [star_sub, star_pow, star_pow]
        ring
      rw [hcongr, norm_star, sq_sub_sq, norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_add_le u v) (norm_nonneg _)
    have h2 : ‖u‖ + ‖v‖ ≤ 2 * Rad i := by linarith
    calc ‖G u - G v‖ ≤ (‖u‖ + ‖v‖) * ‖u - v‖ := h1
      _ ≤ (2 * Rad i) * ‖u - v‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
  have hFmap : ∀ i : ℕ, i ≤ 5 → ∀ u : ℂ, ‖u‖ ≤ Rad i → ‖F u‖ ≤ Rad (i + 1) := by
    intro i hi u hu
    have hQb := hQbd i u hu
    have hεQi : ε * Q i < 1 := by
      have h1 := hεQtot ε hεpos hεε₀
      nlinarith [hQle i hi, hQnn i]
    have hFu : F u = G u + (ε : ℂ) * P.eval (star u) := by
      rw [hF, hG, perturb_apply]
    have h1 : ‖F u‖ ≤ ‖G u‖ + ε * ‖P.eval (star u)‖ := by
      rw [hFu]
      calc ‖G u + (ε : ℂ) * P.eval (star u)‖
          ≤ ‖G u‖ + ‖(ε : ℂ) * P.eval (star u)‖ := norm_add_le _ _
        _ = ‖G u‖ + ε * ‖P.eval (star u)‖ := by rw [norm_mul]; simp [abs_of_pos hεpos]
    have h2 : ‖G u‖ ≤ ‖u‖ ^ 2 + ‖c‖ := by
      rw [hG]
      calc ‖Tantibar c u‖ = ‖(star u) ^ 2 + c‖ := rfl
        _ ≤ ‖(star u) ^ 2‖ + ‖c‖ := norm_add_le _ _
        _ = ‖u‖ ^ 2 + ‖c‖ := by rw [norm_pow, norm_star]
    have h3 : ‖u‖ ^ 2 ≤ Rad i ^ 2 := pow_le_pow_left₀ (norm_nonneg u) hu 2
    have h4 : Rad i ^ 2 + ‖c‖ + 1 ≤ Rad (i + 1) := by
      rw [hRad_succ]
      exact le_max_right _ _
    have h5 : ε * ‖P.eval (star u)‖ ≤ ε * Q i := mul_le_mul_of_nonneg_left hQb hεpos.le
    linarith
  have hFlip : ∀ i : ℕ, i ≤ 5 → ∀ u v : ℂ, ‖u‖ ≤ Rad i → ‖v‖ ≤ Rad i →
      ‖F u - F v‖ ≤ (2 * Rad i + 1) * ‖u - v‖ := by
    intro i hi u v hu hv
    have hLipq := hLbd i u v hu hv
    have hεLi : ε * L i < 1 := by
      have h1 := hεLtot ε hεpos hεε₀
      nlinarith [hLle i hi, hLnn i]
    have hGl := hGlip i hi u v hu hv
    have hFu : F u = G u + (ε : ℂ) * P.eval (star u) := by
      rw [hF, hG, perturb_apply]
    have hFv : F v = G v + (ε : ℂ) * P.eval (star v) := by
      rw [hF, hG, perturb_apply]
    have h1 : ‖F u - F v‖ ≤ ‖G u - G v‖ + ε * ‖P.eval (star u) - P.eval (star v)‖ := by
      rw [hFu, hFv]
      have hsplit : G u + (ε : ℂ) * P.eval (star u) - (G v + (ε : ℂ) * P.eval (star v))
          = (G u - G v) + (ε : ℂ) * (P.eval (star u) - P.eval (star v)) := by ring
      rw [hsplit]
      calc ‖(G u - G v) + (ε : ℂ) * (P.eval (star u) - P.eval (star v))‖
          ≤ ‖G u - G v‖ + ‖(ε : ℂ) * (P.eval (star u) - P.eval (star v))‖ := norm_add_le _ _
        _ = ‖G u - G v‖ + ε * ‖P.eval (star u) - P.eval (star v)‖ := by
            rw [norm_mul]; simp [abs_of_pos hεpos]
    have h2 : ε * ‖P.eval (star u) - P.eval (star v)‖ ≤ ε * (L i * ‖u - v‖) :=
      mul_le_mul_of_nonneg_left hLipq hεpos.le
    have h6 : ε * (L i * ‖u - v‖) ≤ 1 * ‖u - v‖ := by
      have h7 : ε * L i ≤ 1 := le_of_lt hεLi
      calc ε * (L i * ‖u - v‖) = (ε * L i) * ‖u - v‖ := by ring
        _ ≤ 1 * ‖u - v‖ := mul_le_mul_of_nonneg_right h7 (norm_nonneg _)
    calc ‖F u - F v‖ ≤ ‖G u - G v‖ + ε * ‖P.eval (star u) - P.eval (star v)‖ := h1
      _ ≤ (2 * Rad i) * ‖u - v‖ + ε * (L i * ‖u - v‖) := add_le_add hGl h2
      _ ≤ (2 * Rad i) * ‖u - v‖ + 1 * ‖u - v‖ := by linarith
      _ = (2 * Rad i + 1) * ‖u - v‖ := by ring
  have hGiter : ∀ (k : ℕ) (y : ℂ), k ≤ 5 → ‖y‖ ≤ M →
      ‖(G^[k]) y - (G^[k]) z₁‖ ≤ PLip k * ‖y - z₁‖ := by
    intro k y hk hy
    have h := iterate_bound_aux G Rad (fun i => 2 * Rad i)
      (fun i => mul_nonneg (by norm_num) (hRadnn i)) hGmap hGlip
      (by rw [hRad_zero]; exact hy)
      (by rw [hRad_zero]; exact le_trans hz₁Z (by rw [hMdef]; linarith)) hk
    simpa only [hPLipdef] using h
  have hFiter : ∀ (k : ℕ) (y y' : ℂ), k ≤ 5 → ‖y‖ ≤ M → ‖y'‖ ≤ M →
      ‖(F^[k]) y - (F^[k]) y'‖ ≤ FLip k * ‖y - y'‖ := by
    intro k y y' hk hy hy'
    have h := iterate_bound_aux F Rad (fun i => 2 * Rad i + 1)
      (fun i => add_nonneg (mul_nonneg (by norm_num) (hRadnn i)) (by norm_num)) hFmap hFlip
      (by rw [hRad_zero]; exact hy) (by rw [hRad_zero]; exact hy') hk
    simpa only [hFLipdef] using h
  -- ===== the base points =====
  have hxM : ‖z₁ + w‖ ≤ M := by
    have h1 : ‖z₁ + w‖ ≤ ‖z₁‖ + ‖w‖ := norm_add_le _ _
    have h2 : ‖w‖ ≤ δ := hw
    rw [hMdef]
    linarith
  have hclos : ∀ k : ℕ, k ≤ 4 → ‖(G^[k]) (z₁ + w) - cyclePt c z₁ k‖ ≤ PLip k * ‖w‖ := by
    intro k hk
    have h := hGiter k (z₁ + w) (by omega) hxM
    rw [hGz₁ k, show z₁ + w - z₁ = w from by ring] at h
    exact h
  have hGin : ∀ k : ℕ, k ≤ 4 → ‖(G^[k]) (z₁ + w)‖ ≤ Z + 1 := by
    intro k hk
    have h1 := hclos k hk
    have h2 : ‖cyclePt c z₁ k‖ ≤ Z := hZle k (Finset.mem_range.mpr (by omega))
    have h3 : PLip k * ‖w‖ ≤ PLip k * δ := mul_le_mul_of_nonneg_left hw (hPLipnn k)
    have h4 : PLip k * δ ≤ 1 := hδPLip k (by omega)
    calc ‖(G^[k]) (z₁ + w)‖ = ‖((G^[k]) (z₁ + w) - cyclePt c z₁ k) + cyclePt c z₁ k‖ := by
          rw [sub_add_cancel]
      _ ≤ ‖(G^[k]) (z₁ + w) - cyclePt c z₁ k‖ + ‖cyclePt c z₁ k‖ := norm_add_le _ _
      _ ≤ Z + 1 := by linarith
  -- ===== the telescoping identity =====
  let NN : ℕ → ℂ := fun j => (F^[4 - j]) (F ((G^[j]) (z₁ + w)))
      - (F^[4 - j]) (G ((G^[j]) (z₁ + w)))
  let NN' : ℕ → ℂ := fun j => (F^[4 - j]) (F ((G^[j]) z₁)) - (F^[4 - j]) (G ((G^[j]) z₁))
  have hnice : ((F^[5]) (z₁ + w) - (G^[5]) (z₁ + w)) - ((F^[5]) z₁ - (G^[5]) z₁)
      = ∑ j ∈ Finset.range 5, (NN j - NN' j) := five_telescope_aux F G (z₁ + w) z₁
  -- ===== the per-term estimates =====
  have hterm : ∀ j ∈ Finset.range 5, ‖NN j - NN' j‖ ≤ coef j * (ε * ‖w‖ ^ 2) := by
    intro j hj
    have hj4 : j ≤ 4 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rcases eq_or_lt_of_le hj4 with h4 | hlt
    · subst h4
      have hA : NN 4 = (ε : ℂ) * P.eval (star ((G^[4]) (z₁ + w))) := by
        dsimp only [NN]
        simp only [Nat.reduceSub, Function.iterate_zero]
        exact hFG _
      have hB : NN' 4 = (ε : ℂ) * P.eval (star (cyclePt c z₁ 4)) := by
        dsimp only [NN']
        rw [hGz₁ 4]
        simp only [Nat.reduceSub, Function.iterate_zero]
        exact hFG _
      have hq4 : ‖P.eval (star ((G^[4]) (z₁ + w))) - P.eval (star (cyclePt c z₁ 4))‖
          ≤ S 4 * ‖(G^[4]) (z₁ + w) - cyclePt c z₁ 4‖ ^ 2 := by
        have hin : ‖star ((G^[4]) (z₁ + w))‖ ≤ M := by
          rw [norm_star]
          have h1 := hGin 4 le_rfl
          rw [hMdef]
          linarith
        have h := hS4 (star ((G^[4]) (z₁ + w))) hin
        rwa [← star_sub, norm_star] at h
      have hd4 : ‖(G^[4]) (z₁ + w) - cyclePt c z₁ 4‖ ≤ PLip 4 * ‖w‖ := hclos 4 le_rfl
      calc ‖NN 4 - NN' 4‖
          = ‖(ε : ℂ) * (P.eval (star ((G^[4]) (z₁ + w))) - P.eval (star (cyclePt c z₁ 4)))‖ := by
            rw [hA, hB]
            congr 1
            ring
        _ = ε * ‖P.eval (star ((G^[4]) (z₁ + w))) - P.eval (star (cyclePt c z₁ 4))‖ := by
            rw [norm_mul]; simp [abs_of_pos hεpos]
        _ ≤ ε * (S 4 * ‖(G^[4]) (z₁ + w) - cyclePt c z₁ 4‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hq4 hεpos.le
        _ ≤ ε * (S 4 * (PLip 4 * ‖w‖) ^ 2) := by
            refine mul_le_mul_of_nonneg_left ?_ hεpos.le
            exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hd4 2) (hSnn 4)
        _ = coef 4 * (ε * ‖w‖ ^ 2) := by
            have hF0 : FLip 0 = 1 := by rw [hFLipdef]; simp
            rw [hcoefdef]
            simp only [Nat.reduceSub]
            rw [hF0]
            ring
    · have hj3 : j ≤ 3 := by omega
      have hNN'z : NN' j = 0 := by
        dsimp only [NN']
        rw [hFfix j hj3, sub_self]
      have hqj : ‖P.eval (star ((G^[j]) (z₁ + w)))‖
          ≤ S j * ‖(G^[j]) (z₁ + w) - cyclePt c z₁ j‖ ^ 2 := by
        have hin : ‖star ((G^[j]) (z₁ + w))‖ ≤ M := by
          rw [norm_star]
          have h1 := hGin j (by omega)
          rw [hMdef]
          linarith
        have h := hS3 j hj3 (star ((G^[j]) (z₁ + w))) hin
        rwa [← star_sub, norm_star] at h
      have hdj : ‖(G^[j]) (z₁ + w) - cyclePt c z₁ j‖ ≤ PLip j * ‖w‖ := hclos j (by omega)
      have hy'Z : ‖G ((G^[j]) (z₁ + w))‖ ≤ Z + 1 := by
        rw [hGsucc j (z₁ + w)]
        exact hGin (j + 1) (by omega)
      have hy'M : ‖G ((G^[j]) (z₁ + w))‖ ≤ M := by
        rw [hMdef]; linarith
      have hyM : ‖F ((G^[j]) (z₁ + w))‖ ≤ M := by
        have hqv : ‖P.eval (star ((G^[j]) (z₁ + w)))‖ ≤ Q 0 := by
          refine hQbd 0 ((G^[j]) (z₁ + w)) ?_
          rw [hRad_zero]
          have h1 := hGin j (by omega)
          rw [hMdef]
          linarith
        have hεQ0 : ε * Q 0 < 1 := by
          have h1 := hεQtot ε hεpos hεε₀
          have h2 : Q 0 ≤ Qtot := hQle 0 (by norm_num)
          nlinarith [hQnn 0]
        have hFu : F ((G^[j]) (z₁ + w))
            = G ((G^[j]) (z₁ + w)) + (ε : ℂ) * P.eval (star ((G^[j]) (z₁ + w))) := by
          rw [hF, hG, perturb_apply]
        rw [hFu]
        calc ‖G ((G^[j]) (z₁ + w)) + (ε : ℂ) * P.eval (star ((G^[j]) (z₁ + w)))‖
            ≤ ‖G ((G^[j]) (z₁ + w))‖ + ‖(ε : ℂ) * P.eval (star ((G^[j]) (z₁ + w)))‖ :=
              norm_add_le _ _
          _ = ‖G ((G^[j]) (z₁ + w))‖ + ε * ‖P.eval (star ((G^[j]) (z₁ + w)))‖ := by
              rw [norm_mul]; simp [abs_of_pos hεpos]
          _ ≤ (Z + 1) + ε * Q 0 :=
              add_le_add hy'Z (mul_le_mul_of_nonneg_left hqv hεpos.le)
          _ ≤ M := by rw [hMdef]; linarith
      have hbd : ‖NN j‖ ≤ FLip (4 - j) * (ε * ‖P.eval (star ((G^[j]) (z₁ + w)))‖) := by
        have hlip := hFiter (4 - j) (F ((G^[j]) (z₁ + w))) (G ((G^[j]) (z₁ + w)))
          (by omega) hyM hy'M
        have hdiff : F ((G^[j]) (z₁ + w)) - G ((G^[j]) (z₁ + w))
            = (ε : ℂ) * P.eval (star ((G^[j]) (z₁ + w))) := hFG _
        dsimp only [NN]
        rw [hdiff, norm_mul, hεnorm] at hlip
        exact hlip
      calc ‖NN j - NN' j‖ = ‖NN j‖ := by rw [hNN'z, sub_zero]
        _ ≤ FLip (4 - j) * (ε * ‖P.eval (star ((G^[j]) (z₁ + w)))‖) := hbd
        _ ≤ FLip (4 - j) * (ε * (S j * ‖(G^[j]) (z₁ + w) - cyclePt c z₁ j‖ ^ 2)) := by
            refine mul_le_mul_of_nonneg_left ?_ (hFLipnn (4 - j))
            exact mul_le_mul_of_nonneg_left hqj hεpos.le
        _ ≤ FLip (4 - j) * (ε * (S j * (PLip j * ‖w‖) ^ 2)) := by
            refine mul_le_mul_of_nonneg_left ?_ (hFLipnn (4 - j))
            refine mul_le_mul_of_nonneg_left ?_ hεpos.le
            exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hdj 2) (hSnn j)
        _ = coef j * (ε * ‖w‖ ^ 2) := by
            rw [hcoefdef]
            ring
  -- ===== the conclusion =====
  rw [hnice]
  calc ‖∑ j ∈ Finset.range 5, (NN j - NN' j)‖
      ≤ ∑ j ∈ Finset.range 5, ‖NN j - NN' j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range 5, coef j * (ε * ‖w‖ ^ 2) := Finset.sum_le_sum hterm
    _ = (∑ j ∈ Finset.range 5, coef j) * (ε * ‖w‖ ^ 2) := by rw [Finset.sum_mul]
    _ ≤ K * (ε * ‖w‖ ^ 2) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [hKdef]; linarith
    _ = K * ε * ‖w‖ ^ 2 := by ring

end

end Work.FBif
