import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.ENormSq_seriesFun_le
import Submission.Work.Diff.STE.CSq_le_ENormSq_seriesFun
import Submission.Work.Diff.STE.norm_seriesFun_le
import Submission.Work.Diff.STE.l1_le_sqrt_CSq
import Submission.Work.Diff.STE.summable_wt_zpow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliary bounds for `Work.Diff.STE.flat.level_step`

This module collects the elementary ("Sobolev") inputs of the `H^{s+1}` energy differential
inequality of the flat DeTurck/Galerkin system:
* `sob n = n / 2 + 1`, the level with `n < 2 * sob n` and `2 * sob n ≤ n + 2`;
* `jet_l2_le` / `jet_sup_le`: the level-`s` energy bound controls `L²` norms of derivatives up to
order `s` and *sup* norms of derivatives up to order `s - sob n`, uniformly in the box size `N`;
* the local energy-differentiation lemma for box-supported coefficient families.
-/

set_option maxHeartbeats 1000000

open MeasureTheory BigOperators

namespace Work.Diff.STE.flat

open Work.Diff.STE.Flat

noncomputable section

variable {n s : ℕ}

/-- The Sobolev level used for the sup-norm bounds: `σ = n / 2 + 1`, so that `n < 2 σ` and
`2 σ ≤ n + 2`. -/
def sob (n : ℕ) : ℕ := n / 2 + 1

lemma n_lt_two_sob (n : ℕ) : n < 2 * sob n := by
  have h2 : 2 * (n / 2) ≤ n := by
    rw [mul_comm]; exact Nat.div_mul_le_self n 2
  simp only [sob]
  omega

lemma two_sob_le (n : ℕ) : 2 * sob n ≤ n + 2 := by
  have h2 : 2 * (n / 2) ≤ n := by
    rw [mul_comm]; exact Nat.div_mul_le_self n 2
  simp only [sob]
  omega

/-! ## Moment summability of box-supported families -/

/-- A box-supported coefficient family has finite support, hence all its polynomial moments (and
their `ℓ¹` norms) are summable. -/
lemma summable_moment_box {N : ℕ} (c : (Fin n → ℤ) → MatC n)
    (hc : ∀ k : Fin n → ℤ, k ∉ box n N → c k = 0) (i j : Fin n) (M : ℕ) :
    Summable (fun k : Fin n → ℤ => (wt k) ^ M * ‖c k i j‖) := by
  refine summable_of_ne_finset_zero (s := box n N) ?_
  intro k hk
  rw [hc k hk]
  simp

/-! ## Nonnegativity of the energies -/

lemma ENormSq_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) (f : (ι → ℝ) → ℂ) :
    0 ≤ ENormSq k f :=
  Finset.sum_nonneg fun l _ => integral_nonneg fun x => sq_nonneg _

lemma ENormSqM_nonneg (k : ℕ) (u : Torus n) : 0 ≤ ENormSqM k u :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ENormSq_nonneg k _

lemma ENormSqM_le_ENormSqFull (k : ℕ) (u : Torus n) : ENormSqM k u ≤ ENormSqFull k u := by
  rw [ENormSqFull]
  exact le_add_of_nonneg_right (ENormSqM_nonneg 0 u)

lemma ENormSqM_zero_le_ENormSqFull (k : ℕ) (u : Torus n) : ENormSqM 0 u ≤ ENormSqFull k u := by
  rw [ENormSqFull]
  exact le_add_of_nonneg_left (ENormSqM_nonneg k u)

lemma ENormSqFull_nonneg (k : ℕ) (u : Torus n) : 0 ≤ ENormSqFull k u :=
  add_nonneg (ENormSqM_nonneg k u) (ENormSqM_nonneg 0 u)

/-- `CSq` is nonnegative. -/
lemma CSq_nonneg' {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) (c : (ι → ℤ) → ℂ) :
    0 ≤ CSq k c :=
  tsum_nonneg fun m => mul_nonneg (pow_nonneg (le_of_lt (wt_pos m)) k) (sq_nonneg _)

/-- Each entry energy of the matrix family is dominated by the full energy. -/
lemma ENormSq_le_ENormSqM {j : ℕ} (u : Torus n) (i j' : Fin n) :
    ENormSq j (fun x => u x i j') ≤ ENormSqM j u := by
  rw [ENormSqM]
  have h1 : ENormSq j (fun x => u x i j')
      ≤ ∑ j'' : Fin n, ENormSq j (fun x => u x i j'') :=
    Finset.single_le_sum (fun j'' _ => ENormSq_nonneg j (fun x => u x i j''))
      (Finset.mem_univ j')
  have h2 : (∑ j'' : Fin n, ENormSq j (fun x => u x i j''))
      ≤ ∑ i' : Fin n, ∑ j'' : Fin n, ENormSq j (fun x => u x i' j'') :=
    Finset.single_le_sum (fun i' _ => Finset.sum_nonneg fun j'' _ =>
      ENormSq_nonneg j (fun x => u x i' j'')) (Finset.mem_univ i)
  exact h1.trans h2

lemma ENormSq_le_ENormSqFull {j : ℕ} (u : Torus n) (i j' : Fin n) :
    ENormSq j (fun x => u x i j') ≤ ENormSqFull j u :=
  (ENormSq_le_ENormSqM (j := j) u i j').trans (ENormSqM_le_ENormSqFull j u)

lemma ENormSq_zero_le_ENormSqFull {j : ℕ} (u : Torus n) (i j' : Fin n) :
    ENormSq 0 (fun x => u x i j') ≤ ENormSqFull j u :=
  (ENormSq_le_ENormSqM (j := 0) u i j').trans (ENormSqM_zero_le_ENormSqFull j u)

/-! ## The `L²` bound for the jets -/

/-- **`L²` bounds for all derivatives up to order `s`.**  If the coefficient family `c` is
supported in the box `box n N`, then for every `m ≤ s`, every multi-index `l : Fin m → Fin n` and
every matrix entry `(i,j)`, the `L²` norm squared of `∂^l (seriesFunM c · i j)` is bounded by a
constant times the full level-`s` energy. -/
theorem jet_l2_le {N : ℕ} (c : (Fin n → ℤ) → MatC n)
    (hc : ∀ k : Fin n → ℤ, k ∉ box n N → c k = 0) (m : ℕ) (hm : m ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (l : Fin m → Fin n) (i j : Fin n),
      ∫ x in unitCube (ι := Fin n),
        ‖pdVec m l (fun y => seriesFunM c y i j) x‖ ^ 2
        ≤ C * ENormSqFull s (seriesFunM c) := by
  obtain ⟨C1, hC1, h1⟩ := ENormSq_seriesFun_le (ι := Fin n) m
  obtain ⟨C2, hC2, h2⟩ := CSq_le_ENormSq_seriesFun (ι := Fin n) s
  refine ⟨C1 * C2, mul_nonneg hC1 hC2, ?_⟩
  intro l i j
  have hfun : (fun y : Fin n → ℝ => seriesFunM c y i j)
      = seriesFun (fun k : Fin n → ℤ => c k i j) := by
    funext y; rw [seriesFunM_apply]
  rw [hfun]
  have hmom : ∀ M : ℕ, Summable (fun k : Fin n → ℤ => (wt k) ^ M * ‖c k i j‖) :=
    fun M => summable_moment_box c hc i j M
  have hsumm : ∀ M : ℕ, Summable (fun k : Fin n → ℤ => (wt k) ^ M *
      ‖(fun k : Fin n → ℤ => c k i j) k‖) := hmom
  have hterm : ∫ x in unitCube (ι := Fin n),
        ‖pdVec m l (seriesFun (fun k : Fin n → ℤ => c k i j)) x‖ ^ 2
      ≤ ENormSq m (seriesFun (fun k : Fin n → ℤ => c k i j)) := by
    rw [ENormSq]
    exact Finset.single_le_sum (f := fun l' : Fin m → Fin n =>
      ∫ x in unitCube (ι := Fin n),
        ‖pdVec m l' (seriesFun (fun k : Fin n → ℤ => c k i j)) x‖ ^ 2)
      (fun l' _ => integral_nonneg fun x => sq_nonneg _) (Finset.mem_univ l)
  have hmono : CSq m (fun k : Fin n → ℤ => c k i j)
      ≤ CSq s (fun k : Fin n → ℤ => c k i j) := by
    rw [CSq, CSq]
    refine Summable.tsum_le_tsum (fun k => ?_) (summable_wt_pow_mul_norm_sq _ hsumm m)
      (summable_wt_pow_mul_norm_sq _ hsumm s)
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (wt_one_le k) hm) (sq_nonneg _)
  have h3 : ENormSq m (seriesFun (fun k : Fin n → ℤ => c k i j))
      ≤ C1 * CSq m (fun k : Fin n → ℤ => c k i j) := h1 _ hsumm
  have h4 : CSq s (fun k : Fin n → ℤ => c k i j)
      ≤ C2 * (ENormSq s (seriesFun (fun k : Fin n → ℤ => c k i j))
          + ENormSq 0 (seriesFun (fun k : Fin n → ℤ => c k i j))) := h2 _ hsumm
  have hEs : ENormSq s (seriesFun (fun k : Fin n → ℤ => c k i j))
      ≤ ENormSqM s (seriesFunM c) := by
    have := ENormSq_le_ENormSqM (j := s) (seriesFunM c) i j
    rwa [hfun] at this
  have hE0 : ENormSq 0 (seriesFun (fun k : Fin n → ℤ => c k i j))
      ≤ ENormSqM 0 (seriesFunM c) := by
    have := ENormSq_le_ENormSqM (j := 0) (seriesFunM c) i j
    rwa [hfun] at this
  calc ∫ x in unitCube (ι := Fin n),
        ‖pdVec m l (seriesFun (fun k : Fin n → ℤ => c k i j)) x‖ ^ 2
      ≤ ENormSq m (seriesFun (fun k : Fin n → ℤ => c k i j)) := hterm
    _ ≤ C1 * CSq m (fun k : Fin n → ℤ => c k i j) := h3
    _ ≤ C1 * CSq s (fun k : Fin n → ℤ => c k i j) := mul_le_mul_of_nonneg_left hmono hC1
    _ ≤ C1 * (C2 * (ENormSq s (seriesFun (fun k : Fin n → ℤ => c k i j))
          + ENormSq 0 (seriesFun (fun k : Fin n → ℤ => c k i j)))) :=
        mul_le_mul_of_nonneg_left h4 hC1
    _ = C1 * C2 * (ENormSq s (seriesFun (fun k : Fin n → ℤ => c k i j))
          + ENormSq 0 (seriesFun (fun k : Fin n → ℤ => c k i j))) := by ring
    _ ≤ C1 * C2 * (ENormSqM s (seriesFunM c) + ENormSqM 0 (seriesFunM c)) :=
        mul_le_mul_of_nonneg_left (add_le_add hEs hE0) (mul_nonneg hC1 hC2)
    _ = C1 * C2 * ENormSqFull s (seriesFunM c) := by rw [ENormSqFull]

/-! ## The sup bound for the jets -/

/-- The weighted `ℓ²` sum of the differentiated coefficients is controlled by `CSq` at the sum of
the levels. -/
lemma CSq_dmulV_le {ι : Type*} [Fintype ι] [DecidableEq ι] (σ : ℕ) (l : List ι)
    (c : (ι → ℤ) → ℂ) (h : ∀ M : ℕ, Summable (fun k : ι → ℤ => (wt k) ^ M * ‖c k‖)) :
    CSq σ (dmulV l c) ≤ ((2 * Real.pi) ^ 2) ^ l.length * CSq (σ + l.length) c := by
  rw [CSq, CSq, ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun k => ?_)
    (summable_wt_pow_mul_norm_sq _ (fun M => summable_dmulV l c h M) σ)
    ((summable_wt_pow_mul_norm_sq c h (σ + l.length)).mul_left _)
  calc (wt k) ^ σ * ‖dmulV l c k‖ ^ 2
      ≤ (wt k) ^ σ * (((2 * Real.pi) ^ 2 * wt k) ^ l.length * ‖c k‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (norm_sq_dmulV_le l c k)
          (pow_nonneg (le_of_lt (wt_pos k)) σ)
    _ = ((2 * Real.pi) ^ 2) ^ l.length * ((wt k) ^ (σ + l.length) * ‖c k‖ ^ 2) := by
        rw [mul_pow, pow_add]; ring

/-- **Sup bounds for derivatives up to order `s - sob n`.**  If the coefficient family `c` is
supported in the box `box n N`, then for every `m` with `m + sob n ≤ s`, every multi-index
`l : Fin m → Fin n`, every entry `(i,j)` and every `x`, the derivative `∂^l (seriesFunM c · i j)`
is bounded by a constant times `1 + √(ENormSqFull s (seriesFunM c))`. -/
theorem jet_sup_le {N : ℕ} (c : (Fin n → ℤ) → MatC n)
    (hc : ∀ k : Fin n → ℤ, k ∉ box n N → c k = 0) (m : ℕ) (hm : m + sob n ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (l : Fin m → Fin n) (i j : Fin n) (x : Fin n → ℝ),
      ‖pdVec m l (fun y => seriesFunM c y i j) x‖
        ≤ C * (1 + Real.sqrt (ENormSqFull s (seriesFunM c))) := by
  obtain ⟨C0, hC0, h0⟩ := norm_seriesFun_le (ι := Fin n) (sob n) (by simpa using n_lt_two_sob n)
  obtain ⟨C2, hC2, h2⟩ := CSq_le_ENormSq_seriesFun (ι := Fin n) s
  refine ⟨C0 * (2 * Real.pi) ^ m * Real.sqrt C2, by positivity, ?_⟩
  intro l i j x
  have hfun : (fun y : Fin n → ℝ => seriesFunM c y i j)
      = seriesFun (fun k : Fin n → ℤ => c k i j) := by
    funext y; rw [seriesFunM_apply]
  rw [hfun]
  have hmom : ∀ M : ℕ, Summable (fun k : Fin n → ℤ => (wt k) ^ M * ‖c k i j‖) :=
    fun M => summable_moment_box c hc i j M
  have hsumm : ∀ M : ℕ, Summable (fun k : Fin n → ℤ => (wt k) ^ M *
      ‖(fun k : Fin n → ℤ => c k i j) k‖) := hmom
  have hpd : pdVec m l (seriesFun (fun k : Fin n → ℤ => c k i j)) x
      = seriesFun (dmulV (List.ofFn l) (fun k => c k i j)) x := by
    rw [pdVec]
    exact pdList_seriesFun (List.ofFn l) (fun k => c k i j) hmom x
  rw [hpd]
  have hstep := h0 (dmulV (List.ofFn l) (fun k => c k i j))
    (summable_wt_pow_mul_norm_sq _ (fun M => summable_dmulV _ _ hmom M) (sob n)) x
  have hCSq : CSq (sob n) (dmulV (List.ofFn l) (fun k => c k i j))
      ≤ ((2 * Real.pi) ^ 2) ^ m * CSq (sob n + m) (fun k => c k i j) := by
    have h := CSq_dmulV_le (sob n) (List.ofFn l) (fun k => c k i j) hmom
    simpa [List.length_ofFn] using h
  have hlev : sob n + m ≤ s := by omega
  have hmono : CSq (sob n + m) (fun k : Fin n → ℤ => c k i j)
      ≤ CSq s (fun k : Fin n → ℤ => c k i j) := by
    rw [CSq, CSq]
    refine Summable.tsum_le_tsum (fun k => ?_) (summable_wt_pow_mul_norm_sq _ hsumm (sob n + m))
      (summable_wt_pow_mul_norm_sq _ hsumm s)
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (wt_one_le k) hlev) (sq_nonneg _)
  have h4 : CSq s (fun k : Fin n → ℤ => c k i j)
      ≤ C2 * ENormSqFull s (seriesFunM c) := by
    have h := h2 (fun k => c k i j) hsumm
    have hEs : ENormSq s (seriesFun (fun k : Fin n → ℤ => c k i j))
        ≤ ENormSqM s (seriesFunM c) := by
      have := ENormSq_le_ENormSqM (j := s) (seriesFunM c) i j
      rwa [hfun] at this
    have hE0 : ENormSq 0 (seriesFun (fun k : Fin n → ℤ => c k i j))
        ≤ ENormSqM 0 (seriesFunM c) := by
      have := ENormSq_le_ENormSqM (j := 0) (seriesFunM c) i j
      rwa [hfun] at this
    refine h.trans ?_
    rw [ENormSqFull]
    exact mul_le_mul_of_nonneg_left (add_le_add hEs hE0) hC2
  calc ‖seriesFun (dmulV (List.ofFn l) (fun k => c k i j)) x‖
      ≤ C0 * Real.sqrt (CSq (sob n) (dmulV (List.ofFn l) (fun k => c k i j))) := hstep
    _ ≤ C0 * Real.sqrt (((2 * Real.pi) ^ 2) ^ m * CSq (sob n + m) (fun k => c k i j)) := by
        refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hCSq) hC0
    _ = C0 * ((2 * Real.pi) ^ m * Real.sqrt (CSq (sob n + m) (fun k => c k i j))) := by
        have hsq : ((2 * Real.pi) ^ 2) ^ m = ((2 * Real.pi) ^ m) ^ 2 := by
          rw [← pow_mul]; ring_nf
        rw [hsq, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    _ ≤ C0 * ((2 * Real.pi) ^ m * Real.sqrt (C2 * ENormSqFull s (seriesFunM c))) := by
        refine mul_le_mul_of_nonneg_left ?_ hC0
        refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by positivity)
        exact hmono.trans h4
    _ = C0 * ((2 * Real.pi) ^ m * (Real.sqrt C2
          * Real.sqrt (ENormSqFull s (seriesFunM c)))) := by
        rw [Real.sqrt_mul hC2]
    _ ≤ C0 * ((2 * Real.pi) ^ m * (Real.sqrt C2
          * (1 + Real.sqrt (ENormSqFull s (seriesFunM c))))) := by
        refine mul_le_mul_of_nonneg_left ?_ hC0
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg C2)
    _ = C0 * (2 * Real.pi) ^ m * Real.sqrt C2
          * (1 + Real.sqrt (ENormSqFull s (seriesFunM c))) := by ring

/-! ## The non-degeneracy of the elliptic locus -/

/-- A matrix whose quadratic form is bounded below by `lam * |v|²` with `lam > 0` is
invertible: if `det = 0` there is `v ≠ 0` in the kernel, but then `vᵀMv = 0 < lam |v|²`. -/
lemma det_ne_zero_of_elliptic {n : ℕ} (A : MatC n) {lam : ℝ} (hlam : 0 < lam)
    (hpos : ∀ v : Fin n → ℝ, lam * ∑ i, (v i) ^ 2
      ≤ ∑ i, ∑ j, reMat A i j * v i * v j) :
    (reMat A).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have h1 : ∑ i, ∑ j, reMat A i j * v i * v j = 0 := by
    have h1' : ∀ i, ∑ j, reMat A i j * v i * v j = v i * ((reMat A).mulVec v) i := by
      intro i
      rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [Finset.sum_congr rfl fun i _ => h1' i, hv0]
    simp
  have h2 : 0 < ∑ i : Fin n, (v i) ^ 2 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    exact Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩
  nlinarith [hpos v, hlam, h2]

end

end Work.Diff.STE.flat
