import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.card_primeFactors_filter_le_mul_log

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `(2m)^{ω(q)} ≤ √P` for `q ≤ (2P)^{ℓm}` (MRT `n4`, elementary bound)

The number `ω(q) = q.primeFactors.card` of distinct prime factors of `q` grows like
`log q / log log q`, hence sub-polynomially: for every `j ≥ 1` and `m ≥ 1` one has
`(2m)^{j ω(q)} ≤ q` for all large `q` (lemma `pow_omega_le_pow_aux` below).  Consequently,
if `q ≤ (2P)^{ℓm}` then `(2m)^{ω(q)} ≤ P ^{1/2}` for all large `P`.

This is the estimate that makes the number of `m`-torsion points of `(ℤ/q)ˣ` (bounded by
`(2m)^{ω(q)}`) small compared with the window, and it is used in the large-`q` case of `n4`.
-/

namespace Work.BMF

/-- The number of distinct prime factors of `n` is at most `n + 1` (and at most `n` for
`n ≥ 1`).  Used to dispose of the finitely many `q` below the threshold of
`pow_omega_le_pow_aux`. -/
lemma card_primeFactors_le_succ (n : ℕ) : n.primeFactors.card ≤ n + 1 := by
  have h : n.primeFactors ⊆ Finset.range (n + 1) := by
    intro p hp
    rw [Finset.mem_range]
    obtain ⟨hp1, hpdvd, hn0⟩ := Nat.mem_primeFactors.mp hp
    exact Nat.lt_succ_of_le (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpdvd)
  calc n.primeFactors.card ≤ (Finset.range (n + 1)).card := Finset.card_le_card h
    _ = n + 1 := Finset.card_range _

/-- **Sub-polynomial growth of `2 ^ ω`.**  For every `m ≥ 1` and `j ≥ 1` there is `q₀` with
`(2m)^{j·ω(q)} ≤ q` for all `q ≥ q₀`.

Split the prime factors of `q` at the threshold `Y = (2m)^{2j+1}`.  At most `Y` of them lie
below `Y`, and the `k` of them at least `Y` satisfy `Y^k ≤ q`, i.e. `k·log Y ≤ log q`
(`card_primeFactors_filter_le_mul_log`).  Hence
`j·ω(q)·log(2m) ≤ j·Y·log(2m) + j·log(2m)·log q/log Y ≤ log q` as soon as
`q ≥ (2m)^{2jY}`, using `log Y ≥ 2j·log(2m)`. -/
lemma pow_omega_le_pow_aux (m j : ℕ) (hm : 1 ≤ m) (hj : 1 ≤ j) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      (((2 * m : ℕ) : ℝ) ^ (j * q.primeFactors.card)) ≤ (q : ℝ) := by
  set A : ℝ := ((2 * m : ℕ) : ℝ) with hA
  have hA1 : 1 < A := by rw [hA]; exact_mod_cast (show 1 < 2 * m by omega)
  have hA0 : 0 < A := by linarith
  have hlogA : 0 < Real.log A := Real.log_pos hA1
  set Y : ℕ := (2 * m) ^ (2 * j + 1) with hY
  have hY1 : 1 ≤ Y := by
    rw [hY]; have : 0 < (2 * m) ^ (2 * j + 1) := pow_pos (by omega) _
    omega
  have hYr : ((Y : ℕ) : ℝ) = A ^ (2 * j + 1) := by
    rw [hY, hA]; push_cast; ring
  have hlogY : Real.log (Y : ℝ) = (2 * (j : ℝ) + 1) * Real.log A := by
    rw [hYr, Real.log_pow]; push_cast; ring
  refine ⟨max 1 ((2 * m) ^ (2 * j * Y)), ?_⟩
  intro q hq
  have hq1 : 1 ≤ q := le_trans (le_max_left _ _) hq
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hqbig : ((2 * m) ^ (2 * j * Y) : ℕ) ≤ q := le_trans (le_max_right _ _) hq
  set S : Finset ℕ := q.primeFactors.filter (fun p => Y ≤ p) with hS
  set T : Finset ℕ := q.primeFactors.filter (fun p => ¬ (Y ≤ p)) with hT
  have hcard : S.card + T.card = q.primeFactors.card := by
    rw [hS, hT]
    exact Finset.card_filter_add_card_filter_not (s := q.primeFactors) (p := fun p => Y ≤ p)
  have hcardR : (q.primeFactors.card : ℝ) = (S.card : ℝ) + (T.card : ℝ) := by
    rw [← hcard]; push_cast; ring
  have hScard : (S.card : ℝ) * Real.log (Y : ℝ) ≤ Real.log (q : ℝ) := by
    rw [hS]; exact card_primeFactors_filter_le_mul_log q Y hq1 hY1
  have hScard' : (S.card : ℝ) * ((2 * (j : ℝ) + 1) * Real.log A) ≤ Real.log (q : ℝ) := by
    rw [← hlogY]; exact hScard
  have hTle : T.card ≤ Y := by
    have hsub : T ⊆ Finset.range Y := by
      intro p hp
      rw [hT] at hp
      simp only [Finset.mem_filter] at hp
      rw [Finset.mem_range]
      omega
    calc T.card ≤ (Finset.range Y).card := Finset.card_le_card hsub
      _ = Y := Finset.card_range Y
  have hTY : (T.card : ℝ) ≤ ((Y : ℕ) : ℝ) := by exact_mod_cast hTle
  have hlogq : ((2 * j * Y : ℕ) : ℝ) * Real.log A ≤ Real.log (q : ℝ) := by
    have hbigpos : (0:ℝ) < (((2 * m) ^ (2 * j * Y) : ℕ) : ℝ) := by
      have h : (0:ℕ) < (2 * m) ^ (2 * j * Y) := pow_pos (by omega) _
      exact_mod_cast h
    have h1 : Real.log ((((2 * m) ^ (2 * j * Y) : ℕ) : ℝ)) ≤ Real.log (q : ℝ) :=
      Real.log_le_log hbigpos (by exact_mod_cast hqbig)
    rw [Nat.cast_pow, ← hA, Real.log_pow] at h1
    exact h1
  have hb1 : (j : ℝ) * (S.card : ℝ) * Real.log A ≤ Real.log (q : ℝ) / 2 := by
    nlinarith [hScard', hlogA, (show (0:ℝ) ≤ (S.card:ℝ) by positivity), (show (0:ℝ) ≤ (j:ℝ) by positivity)]
  have hb2 : (j : ℝ) * (T.card : ℝ) * Real.log A ≤ Real.log (q : ℝ) / 2 := by
    have hlogq' : 2 * ((j : ℝ) * ((Y : ℕ) : ℝ) * Real.log A) ≤ Real.log (q : ℝ) := by
      have h := hlogq
      push_cast at h
      nlinarith [h]
    have hjl : (0:ℝ) ≤ (j:ℝ) * Real.log A := by
      have h1 : (0:ℝ) ≤ (j:ℝ) := by positivity
      nlinarith [hlogA, h1]
    have hTYj : ((j:ℝ) * Real.log A) * (T.card:ℝ) ≤ ((j:ℝ) * Real.log A) * ((Y:ℕ):ℝ) :=
      mul_le_mul_of_nonneg_left hTY hjl
    nlinarith [hlogq', hTYj]
  refine (Real.log_le_log_iff (pow_pos hA0 _) hq0).mp ?_
  rw [Real.log_pow]
  push_cast
  rw [hcardR]
  nlinarith [hb1, hb2]

/-- **MRT `n4`: the elementary square-root bound.**  For `ℓ, m ≥ 1` there is `P₀` such that
for all `P ≥ P₀` and all `q` with `q ≤ (2P)^{ℓm}` one has `(2m)^{ω(q)} ≤ √P`.

The `4ℓm`-th power of the left-hand side satisfies `(2m)^{4ℓm ω(q)} ≤ q` for `q` beyond the
threshold of `pow_omega_le_pow_aux`; taking `ℓm`-th roots and comparing with `q ≤ (2P)^{ℓm}`
gives `(2m)^{4ω(q)} ≤ 2P`, whence `(2m)^{2ω(q)} ≤ P` as soon as `P ≥ 4`.  The finitely many
smaller `q` only increase the constant `P₀`. -/
lemma n4_omega_sqrt_bound (ℓ m : ℕ) (hℓ : 1 ≤ ℓ) (hm : 1 ≤ m) :
    ∃ P₀ : ℝ, ∀ P : ℝ, P₀ ≤ P → ∀ q : ℕ, (q : ℝ) ≤ (2 * P) ^ (ℓ * m) →
      (((2 * m : ℕ) : ℝ) ^ q.primeFactors.card) ≤ P ^ ((1 : ℝ) / 2) := by
  set A : ℝ := ((2 * m : ℕ) : ℝ) with hA
  obtain ⟨q₀, hq₀⟩ := pow_omega_le_pow_aux m (4 * (ℓ * m)) hm
    (by have h : 0 < ℓ * m := Nat.mul_pos (by omega) (by omega); omega)
  refine ⟨max 4 ((A ^ q₀) ^ 2), ?_⟩
  intro P hP q hq
  have hP4 : (4:ℝ) ≤ P := le_trans (le_max_left _ _) hP
  have hPq : (A ^ q₀) ^ 2 ≤ P := le_trans (le_max_right _ _) hP
  have hA2 : (2:ℝ) ≤ A := by rw [hA]; exact_mod_cast (show 2 ≤ 2 * m by omega)
  have hA1 : (1:ℝ) ≤ A := by linarith
  have hA0 : (0:ℝ) ≤ A := by linarith
  rw [← Real.sqrt_eq_rpow P]
  by_cases hqbig : q₀ ≤ q
  · -- large `q`: sub-polynomial growth of `2^ω`
    have h1 : A ^ ((4 * (ℓ*m)) * q.primeFactors.card) ≤ (q:ℝ) := hq₀ q hqbig
    have h3 : A ^ ((4 * (ℓ*m)) * q.primeFactors.card) ≤ (2*P)^(ℓ*m) := le_trans h1 hq
    have h3' : (A ^ (4 * q.primeFactors.card)) ^ (ℓ*m) ≤ (2*P)^(ℓ*m) := by
      rw [← pow_mul]
      rw [show (4 * q.primeFactors.card) * (ℓ*m) = (4 * (ℓ*m)) * q.primeFactors.card by ring]
      exact h3
    have h5 : A ^ (4 * q.primeFactors.card) ≤ 2 * P := by
      have hL : (ℓ*m) ≠ 0 := by
        have h : 0 < ℓ * m := Nat.mul_pos (by omega) (by omega); omega
      exact (pow_le_pow_iff_left₀ (by positivity) (by linarith) hL).mp h3'
    have h6 : (A ^ q.primeFactors.card) ^ 4 ≤ 2 * P := by
      rw [← pow_mul, show q.primeFactors.card * 4 = 4 * q.primeFactors.card by ring]
      exact h5
    have hY2 : (A ^ q.primeFactors.card) ^ 2 ≤ P := by
      by_contra hcon
      have hcon' : P < (A ^ q.primeFactors.card) ^ 2 := not_le.mp hcon
      have h7 : P ^ 2 < (A ^ q.primeFactors.card) ^ 4 :=
        by nlinarith [hcon', pow_nonneg hA0 q.primeFactors.card, hP4]
      nlinarith [h7, h6, hP4]
    exact (Real.le_sqrt (by positivity) (by linarith)).mpr hY2
  · -- small `q`: `ω(q) ≤ q₀`, so only the constant `P₀` is at stake
    have hqlt : q < q₀ := not_le.mp hqbig
    have hω : q.primeFactors.card ≤ q₀ := by
      have := card_primeFactors_le_succ q; omega
    have h1 : A ^ q.primeFactors.card ≤ A ^ q₀ := pow_le_pow_right₀ hA1 hω
    have h2 : A ^ q₀ ≤ Real.sqrt P := by
      rw [← Real.sqrt_sq (show (0:ℝ) ≤ A^q₀ by positivity)]
      exact Real.sqrt_le_sqrt hPq
    exact le_trans h1 h2

end Work.BMF
