import Mathlib
import Submission.Work.Normal.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Escape radius, and the topology of the filled Julia set of a polynomial map

For a polynomial map `f : ℂ → ℂ` of degree `d ≥ 2` there is a radius `R ≥ 2` outside which `f` at
least doubles the modulus (`2 * ‖z‖ ≤ ‖f z‖` whenever `R ≤ ‖z‖`).  This single growth condition
controls the whole escape dichotomy:

* a point has bounded orbit iff *all* of its iterates stay in the closed disk of radius `R`;
* a point with unbounded orbit has an open neighbourhood on which the iterates tend to `∞` locally
  uniformly;
* the filled Julia set is closed, compact and nonempty.

The final theorem `Work.Normal.escapeRadius` collects these statements for a polynomial map of
degree `d ≥ 2`.
-/

namespace Work.Normal

open Set Filter Topology Function
open scoped Topology Polynomial

variable {f : ℂ → ℂ} {d : ℕ} {R : ℝ}

/-! ## Growth outside the escape disk -/

/-- **Geometric growth.**  If `f` at least doubles the modulus outside the closed disk of radius
`R` (`R ≥ 2`), then so does every iterate, and the orbit norms grow at least geometrically:
`2 ^ n * ‖z‖ ≤ ‖(f^[n]) z‖` as long as `R ≤ ‖z‖`. -/
theorem escapeRadius_pow_mul_norm_le
    (h : ∀ z : ℂ, R ≤ ‖z‖ → 2 * ‖z‖ ≤ ‖f z‖) :
    ∀ z : ℂ, R ≤ ‖z‖ → ∀ n : ℕ, 2 ^ n * ‖z‖ ≤ ‖f^[n] z‖ := by
  intro z hz n
  induction n with
  | zero => simp
  | succ n ih =>
    have hzn : R ≤ ‖f^[n] z‖ := by
      have h1 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      calc R ≤ ‖z‖ := hz
        _ = 1 * ‖z‖ := (one_mul _).symm
        _ ≤ 2 ^ n * ‖z‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg z)
        _ ≤ ‖f^[n] z‖ := ih
    have hstep : 2 * ‖f^[n] z‖ ≤ ‖f (f^[n] z)‖ := h _ hzn
    rw [Function.iterate_succ_apply']
    calc 2 ^ (n + 1) * ‖z‖ = (2 ^ n * 2) * ‖z‖ := by rw [pow_succ]
      _ = 2 * (2 ^ n * ‖z‖) := by ring
      _ ≤ 2 * ‖f^[n] z‖ := by linarith
      _ ≤ ‖f (f^[n] z)‖ := hstep

/-- **The escape dichotomy.**  If `f` at least doubles the modulus outside the closed disk of
radius `R ≥ 2`, then a point has unbounded orbit exactly when some iterate leaves that disk:
the filled Julia set is the set of points whose orbit is contained in the disk of radius `R`. -/
theorem escapeRadius_filledJulia_eq (hR : 2 ≤ R)
    (h : ∀ z : ℂ, R ≤ ‖z‖ → 2 * ‖z‖ ≤ ‖f z‖) :
    FilledJuliaSet f = {z : ℂ | ∀ n : ℕ, ‖f^[n] z‖ ≤ R} := by
  ext z
  change (∃ M : ℝ, ∀ n : ℕ, ‖f^[n] z‖ ≤ M) ↔ (∀ n : ℕ, ‖f^[n] z‖ ≤ R)
  constructor
  · rintro ⟨M, hM⟩
    by_contra hc
    rw [not_forall] at hc
    obtain ⟨n, hn⟩ := hc
    have hn' : R < ‖f^[n] z‖ := lt_of_not_ge hn
    have hr : R ≤ ‖f^[n] z‖ := hn'.le
    have hrpos : 0 < ‖f^[n] z‖ := lt_of_lt_of_le (by linarith) hr
    have hg := escapeRadius_pow_mul_norm_le (f := f) h (f^[n] z) hr
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (M / ‖f^[n] z‖) one_lt_two
    have hMk : M < 2 ^ k * ‖f^[n] z‖ := by
      have h1 : (M / ‖f^[n] z‖) * ‖f^[n] z‖ < 2 ^ k * ‖f^[n] z‖ :=
        mul_lt_mul_of_pos_right hk hrpos
      rw [div_mul_cancel₀ _ (ne_of_gt hrpos)] at h1
      exact h1
    have hbound : ‖f^[n + k] z‖ ≤ M := hM (n + k)
    have hgk : 2 ^ k * ‖f^[n] z‖ ≤ ‖f^[n + k] z‖ := by
      have hthis : ‖f^[k] (f^[n] z)‖ = ‖f^[n + k] z‖ := by
        rw [← Function.iterate_add_apply, show k + n = n + k by omega]
      rw [← hthis]
      exact hg k
    linarith
  · intro hz
    exact ⟨R, hz⟩

/-! ## Local uniform escape and the topology of the filled Julia set -/

/-- **Local uniform escape.**  If `f` is continuous and at least doubles the modulus outside the
closed disk of radius `R ≥ 2`, then every point outside the filled Julia set has an open
neighbourhood on which the iterates of `f` tend to `∞` locally uniformly. -/
theorem escapeRadius_locallyUniform (hR : 2 ≤ R) (hcont : Continuous f)
    (h : ∀ z : ℂ, R ≤ ‖z‖ → 2 * ‖z‖ ≤ ‖f z‖) :
    ∀ z : ℂ, z ∉ FilledJuliaSet f →
      ∃ U : Set ℂ, U ∈ 𝓝 z ∧ IsOpen U ∧ TendstoLocallyUniformlyAtTop (fun n : ℕ => f^[n]) U := by
  intro z hz
  rw [escapeRadius_filledJulia_eq (f := f) hR h] at hz
  have hnot : ¬ (∀ n : ℕ, ‖f^[n] z‖ ≤ R) := hz
  rw [not_forall] at hnot
  obtain ⟨m, hm⟩ := hnot
  have hm' : R < ‖f^[m] z‖ := lt_of_not_ge hm
  refine ⟨{w : ℂ | R < ‖f^[m] w‖},
    (isOpen_lt continuous_const (hcont.iterate m).norm).mem_nhds hm',
    isOpen_lt continuous_const (hcont.iterate m).norm, ?_⟩
  intro K hKU hK S
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨0, by simp⟩
  · obtain ⟨w₀, hw₀K, hw₀min⟩ := hK.exists_isMinOn hKne ((hcont.iterate m).norm).continuousOn
    have hmin : R < ‖f^[m] w₀‖ := hKU hw₀K
    have hcpos : 0 < ‖f^[m] w₀‖ := lt_of_lt_of_le (by linarith) hmin.le
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (S / ‖f^[m] w₀‖) one_lt_two
    have hSk : S ≤ 2 ^ k * ‖f^[m] w₀‖ := by
      have h1 : (S / ‖f^[m] w₀‖) * ‖f^[m] w₀‖ < 2 ^ k * ‖f^[m] w₀‖ :=
        mul_lt_mul_of_pos_right hk hcpos
      rw [div_mul_cancel₀ _ (ne_of_gt hcpos)] at h1
      linarith
    refine ⟨m + k, ?_⟩
    intro n hn w hwK
    obtain ⟨j, rfl⟩ : ∃ j, n = m + j := ⟨n - m, by omega⟩
    have hjk : k ≤ j := by omega
    have hRw : R ≤ ‖f^[m] w‖ := le_of_lt (hKU hwK)
    have hgeom := escapeRadius_pow_mul_norm_le (f := f) h (f^[m] w) hRw j
    calc S ≤ 2 ^ k * ‖f^[m] w₀‖ := hSk
      _ ≤ 2 ^ j * ‖f^[m] w‖ :=
            mul_le_mul (pow_le_pow_right₀ (by norm_num) hjk) (hw₀min hwK)
              (norm_nonneg _) (by positivity)
      _ ≤ ‖f^[j] (f^[m] w)‖ := hgeom
      _ = ‖f^[m + j] w‖ := by
            rw [← Function.iterate_add_apply, show j + m = m + j by omega]

/-- The filled Julia set of a map that doubles the modulus outside the disk of radius `R ≥ 2` and
is continuous is closed. -/
theorem escapeRadius_isClosed (hR : 2 ≤ R) (hcont : Continuous f)
    (h : ∀ z : ℂ, R ≤ ‖z‖ → 2 * ‖z‖ ≤ ‖f z‖) : IsClosed (FilledJuliaSet f) := by
  rw [escapeRadius_filledJulia_eq (f := f) hR h]
  have hset : {z : ℂ | ∀ n : ℕ, ‖f^[n] z‖ ≤ R} = ⋂ n, {z : ℂ | ‖f^[n] z‖ ≤ R} := by
    ext z
    simp
  rw [hset]
  exact isClosed_iInter fun n => isClosed_le ((hcont.iterate n).norm) continuous_const

/-- The filled Julia set of a continuous map that doubles the modulus outside the disk of radius
`R ≥ 2` is compact (it is a closed subset of the disk of radius `R`). -/
theorem escapeRadius_isCompact (hR : 2 ≤ R) (hcont : Continuous f)
    (h : ∀ z : ℂ, R ≤ ‖z‖ → 2 * ‖z‖ ≤ ‖f z‖) : IsCompact (FilledJuliaSet f) := by
  refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℂ) R)
    (escapeRadius_isClosed (f := f) hR hcont h) ?_
  intro z hz
  rw [escapeRadius_filledJulia_eq (f := f) hR h] at hz
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  exact hz 0

/-- The filled Julia set of a continuous surjective map that doubles the modulus outside the disk
of radius `R ≥ 2` is nonempty: the sets `{z | ‖(f^[n]) z‖ ≤ R}` are a decreasing sequence of
nonempty compact sets. -/
theorem escapeRadius_nonempty (hR : 2 ≤ R) (hcont : Continuous f)
    (h : ∀ z : ℂ, R ≤ ‖z‖ → 2 * ‖z‖ ≤ ‖f z‖) (hsurj : Function.Surjective f) :
    (FilledJuliaSet f).Nonempty := by
  have hmono : ∀ n : ℕ, {z : ℂ | ‖f^[n + 1] z‖ ≤ R} ⊆ {z : ℂ | ‖f^[n] z‖ ≤ R} := by
    intro n z hz
    have hz' : ‖f^[n + 1] z‖ ≤ R := hz
    by_contra hc
    have hc' : R < ‖f^[n] z‖ := not_le.mp hc
    have hRn : R ≤ ‖f^[n] z‖ := le_of_lt hc'
    have hstep : 2 * ‖f^[n] z‖ ≤ ‖f (f^[n] z)‖ := h _ hRn
    have hpos : 0 < ‖f^[n] z‖ := lt_of_lt_of_le (by linarith) hRn
    rw [Function.iterate_succ_apply'] at hz'
    linarith
  have hne : ∀ n : ℕ, ({z : ℂ | ‖f^[n] z‖ ≤ R}).Nonempty := by
    intro n
    obtain ⟨w, hw⟩ := (hsurj.iterate n) 0
    exact ⟨w, by show ‖f^[n] w‖ ≤ R; rw [hw, norm_zero]; linarith⟩
  have hclosed : ∀ n : ℕ, IsClosed {z : ℂ | ‖f^[n] z‖ ≤ R} :=
    fun n => isClosed_le ((hcont.iterate n).norm) continuous_const
  have hsub : ∀ n : ℕ, {z : ℂ | ‖f^[n] z‖ ≤ R} ⊆ {z : ℂ | ‖z‖ ≤ R} := by
    intro n
    induction n with
    | zero => intro z hz; simpa using hz
    | succ n ih => exact (hmono n).trans ih
  have hcompact : ∀ n : ℕ, IsCompact {z : ℂ | ‖f^[n] z‖ ≤ R} := by
    intro n
    refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℂ) R) (hclosed n) ?_
    intro z hz
    have hz' : ‖z‖ ≤ R := hsub n hz
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact hz'
  obtain ⟨z, hz⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n => {z : ℂ | ‖f^[n] z‖ ≤ R}) hmono hne (hcompact 0) hclosed
  refine ⟨z, ?_⟩
  rw [escapeRadius_filledJulia_eq (f := f) hR h]
  exact fun n => Set.mem_iInter.mp hz n

/-! ## Polynomial maps of degree `≥ 2` -/

/-- A nonconstant complex polynomial map is surjective (`ℂ` is algebraically closed). -/
theorem surjective_of_isPolynomialMapOfDegree {d : ℕ} {f : ℂ → ℂ} (hd : 1 ≤ d)
    (hf : IsPolynomialMapOfDegree d f) : Function.Surjective f := by
  obtain ⟨P, hPd, hPeval⟩ := hf
  intro w
  have hpos : 0 < (P - Polynomial.C w).degree := by
    rw [← Polynomial.natDegree_pos_iff_degree_pos, Polynomial.natDegree_sub_C, hPd]
    omega
  obtain ⟨z, hz⟩ := Complex.exists_root hpos
  refine ⟨z, ?_⟩
  have hz' : Polynomial.eval z P = w := by
    have h := hz
    rw [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_C, sub_eq_zero] at h
    exact h
  rw [hPeval z, hz']

/-- **Polynomial escape radius.**  For a complex polynomial `P` of degree `d ≥ 2` there is a radius
`R ≥ 2` beyond which `P` at least doubles the modulus: `2 * ‖z‖ ≤ ‖P z‖` for `R ≤ ‖z‖`. -/
theorem escapeRadius_poly (P : Polynomial ℂ) (hd : 2 ≤ d) (hPd : P.natDegree = d) :
    ∃ R : ℝ, 2 ≤ R ∧ ∀ z : ℂ, R ≤ ‖z‖ → 2 * ‖z‖ ≤ ‖P.eval z‖ := by
  have hcne : P.coeff d ≠ 0 := by
    have h1 : P.coeff d = P.leadingCoeff := by rw [← hPd, Polynomial.coeff_natDegree]
    rw [h1]
    intro hc
    have hPne : P ≠ 0 := by
      intro h0
      rw [h0, Polynomial.natDegree_zero] at hPd
      omega
    exact hPne ((Polynomial.leadingCoeff_eq_zero).mp hc)
  set c : ℝ := ‖P.coeff d‖ with hcdef
  have hcpos : 0 < c := by rw [hcdef]; exact norm_pos_iff.mpr hcne
  set S : ℝ := ∑ i ∈ Finset.range d, ‖P.coeff i‖ with hSdef
  refine ⟨max 2 (max 1 ((S + 2) / c)), le_max_left _ _, ?_⟩
  intro z hz
  have hz1 : 1 ≤ ‖z‖ := (le_max_left 1 ((S + 2) / c)).trans ((le_max_right 2 _).trans hz)
  have hzS : (S + 2) / c ≤ ‖z‖ := (le_max_right 1 _).trans ((le_max_right 2 _).trans hz)
  have hcs : S + 2 ≤ c * ‖z‖ := by
    have h1 : (S + 2) / c * c ≤ ‖z‖ * c := mul_le_mul_of_nonneg_right hzS hcpos.le
    rw [div_mul_cancel₀ _ (ne_of_gt hcpos)] at h1
    linarith
  have hsum_eval : Polynomial.eval z P
      = (∑ i ∈ Finset.range d, P.coeff i * z ^ i) + P.coeff d * z ^ d := by
    have h1 : Polynomial.eval z P = ∑ i ∈ Finset.range (d + 1), P.coeff i * z ^ i :=
      Polynomial.eval_eq_sum_range' (p := P) (n := d + 1) (by rw [hPd]; omega) z
    rw [h1, Finset.sum_range_succ]
  have hsum_le : ‖∑ i ∈ Finset.range d, P.coeff i * z ^ i‖ ≤ S * ‖z‖ ^ (d - 1) := by
    have h1 : ‖∑ i ∈ Finset.range d, P.coeff i * z ^ i‖
        ≤ ∑ i ∈ Finset.range d, ‖P.coeff i‖ * ‖z‖ ^ i := by
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      exact Finset.sum_congr rfl fun i _ => by rw [norm_mul, norm_pow]
    refine h1.trans ?_
    calc ∑ i ∈ Finset.range d, ‖P.coeff i‖ * ‖z‖ ^ i
        ≤ ∑ i ∈ Finset.range d, ‖P.coeff i‖ * ‖z‖ ^ (d - 1) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' : i ≤ d - 1 := by have := Finset.mem_range.mp hi; omega
          exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hz1 hi') (norm_nonneg _)
      _ = S * ‖z‖ ^ (d - 1) := by rw [hSdef, Finset.sum_mul]
  have hkey : c * ‖z‖ ^ d - S * ‖z‖ ^ (d - 1) ≤ ‖Polynomial.eval z P‖ := by
    have h1 : ‖P.coeff d * z ^ d‖
        ≤ ‖Polynomial.eval z P‖ + ‖∑ i ∈ Finset.range d, P.coeff i * z ^ i‖ := by
      have he : Polynomial.eval z P - (∑ i ∈ Finset.range d, P.coeff i * z ^ i)
          = P.coeff d * z ^ d := by
        rw [hsum_eval]; ring
      calc ‖P.coeff d * z ^ d‖
          = ‖Polynomial.eval z P - (∑ i ∈ Finset.range d, P.coeff i * z ^ i)‖ := by rw [he]
        _ ≤ ‖Polynomial.eval z P‖ + ‖∑ i ∈ Finset.range d, P.coeff i * z ^ i‖ :=
              norm_sub_le _ _
    have h2 : ‖P.coeff d * z ^ d‖ = c * ‖z‖ ^ d := by
      rw [norm_mul, norm_pow, ← hcdef]
    linarith
  have hdz : ‖z‖ ^ (d - 1) * ‖z‖ = ‖z‖ ^ d := by
    rw [← pow_succ, show d - 1 + 1 = d by omega]
  have hfac : c * ‖z‖ ^ d - S * ‖z‖ ^ (d - 1) = ‖z‖ ^ (d - 1) * (c * ‖z‖ - S) := by
    rw [← hdz]; ring
  have hzpow : ‖z‖ ≤ ‖z‖ ^ (d - 1) := by
    calc ‖z‖ = ‖z‖ ^ 1 := (pow_one _).symm
      _ ≤ ‖z‖ ^ (d - 1) := pow_le_pow_right₀ hz1 (by omega)
  have h2c : 2 ≤ c * ‖z‖ - S := by linarith
  calc 2 * ‖z‖ ≤ 2 * ‖z‖ ^ (d - 1) := by linarith
    _ ≤ ‖z‖ ^ (d - 1) * (c * ‖z‖ - S) := by
          rw [mul_comm 2]
          exact mul_le_mul_of_nonneg_left h2c (pow_nonneg (norm_nonneg z) _)
    _ = c * ‖z‖ ^ d - S * ‖z‖ ^ (d - 1) := hfac.symm
    _ ≤ ‖Polynomial.eval z P‖ := hkey

/-! ## The escape radius theorem -/

/-- For a polynomial map `f` of degree `d ≥ 2` there is an escape radius `R ≥ 2` with
`2 * ‖z‖ ≤ ‖f z‖` whenever `R ≤ ‖z‖`; consequently the filled Julia set (the set of points with
bounded orbit) is exactly `{z | ∀ n, ‖f^[n] z‖ ≤ R}`, it is closed, compact and nonempty, and its
complement is a union of open sets on which the iterates tend locally uniformly to `∞`. -/
theorem escapeRadius {d : ℕ} {f : ℂ → ℂ} (hd : 2 ≤ d) (hf : IsPolynomialMapOfDegree d f) :
    ∃ R : ℝ, 2 ≤ R ∧ (∀ z : ℂ, R ≤ ‖z‖ → 2 * ‖z‖ ≤ ‖f z‖) ∧
      FilledJuliaSet f = {z : ℂ | ∀ n : ℕ, ‖f^[n] z‖ ≤ R} ∧
      (∀ z : ℂ, z ∉ FilledJuliaSet f → ∃ U : Set ℂ, U ∈ nhds z ∧ IsOpen U ∧
        TendstoLocallyUniformlyAtTop (fun n => f^[n]) U) ∧
      IsClosed (FilledJuliaSet f) ∧ IsCompact (FilledJuliaSet f) ∧
      (FilledJuliaSet f).Nonempty := by
  obtain ⟨P, hPd, hPeval⟩ := hf
  obtain ⟨R, hR2, hR⟩ := escapeRadius_poly P hd hPd
  have hcont : Continuous f := by
    rw [show f = fun z : ℂ => Polynomial.eval z P from funext hPeval]
    exact Polynomial.continuous P
  have hsurj : Function.Surjective f :=
    surjective_of_isPolynomialMapOfDegree (by omega) ⟨P, hPd, hPeval⟩
  have hRf : ∀ z : ℂ, R ≤ ‖z‖ → 2 * ‖z‖ ≤ ‖f z‖ := by
    intro z hz
    rw [hPeval z]
    exact hR z hz
  exact ⟨R, hR2, hRf, escapeRadius_filledJulia_eq (f := f) hR2 hRf,
    escapeRadius_locallyUniform (f := f) hR2 hcont hRf,
    escapeRadius_isClosed (f := f) hR2 hcont hRf,
    escapeRadius_isCompact (f := f) hR2 hcont hRf,
    escapeRadius_nonempty (f := f) hR2 hcont hRf hsurj⟩

end Work.Normal
