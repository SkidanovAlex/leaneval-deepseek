import Mathlib
import Submission.Work.MotT.KleinParamData
import Submission.Work.MotT.kpData_klein_eq
import Submission.Work.MotT.kpData_spans_good
import Submission.Work.MotT.kpData_coord0_ne
import Submission.Work.MotT.kpData_T_diag
import Submission.Work.MotT.kpE_invariants

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotT.exists_kleinData_kleinParam`

For every infinite field `K` of characteristic `≠ 5` there is a finite exceptional set `bad`
such that every `u ∉ bad` with `u ≠ 0` and `u¹⁰ - 11u⁵ - 1 ≠ 0` is the Klein parameter `a` of a
*Good* Klein datum with `b = 1` — i.e. the parametric Klein family over the Klein parameter
`(a,b) = (u,1)`.

The explicit data are in `Submission/Work/MotT/KleinParamData.lean` (`kpData K u`); the structural
properties (`klein_eq`, `spans`, `coord0_ne`, `T_diag`) and the Weierstrass invariants are proved
in the sibling modules.  The exceptional set collects the finitely many `u` that were excluded
while constructing the family:

* the poles of the Weierstrass coefficients: `2u⁵ - 1 = 0` (`kpW`), i.e. `u⁵ = 1/2` (`kpWPoly`),
* the zeros of `c₄ = u²⁰+228u¹⁵+494u¹⁰-228u⁵+1 = kpC4Num`, split into the three factors
  `kpC4f1`, `kpC4f2`, `kpC4f3`,
* the solutions of `j = 1728`, i.e. `c₄³ = 1728·Δ_{E_u}`, encoded by `kpJEqPoly`.

`bad` is the root set of the *product* of these five polynomials (`kpBadPoly`).  All five are
nonzero in *every* field: `kpWPoly` is monic and the other four have constant term `1`.  Hence no
`≠ 0` side condition is needed when taking `roots`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.MotT
noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine Polynomial

/-- `X ^ 5 - 1/2`: a monic polynomial whose roots contain the poles `2u⁵ = 1` of the Weierstrass
coefficients of `kpE`. -/
def kpWPoly (K : Type) [Field K] : Polynomial K := X ^ 5 - C (1 / 2)

/-- The quartic factor of the numerator of `c₄`. -/
def kpC4f1 (K : Type) [Field K] : Polynomial K := X ^ 4 + 3 * X ^ 3 - X ^ 2 - 3 * X + 1

/-- The first octic factor of the numerator of `c₄`. -/
def kpC4f2 (K : Type) [Field K] : Polynomial K :=
  X ^ 8 + X ^ 7 + 7 * X ^ 6 - 7 * X ^ 5 + 7 * X ^ 3 + 7 * X ^ 2 - X + 1

/-- The second octic factor of the numerator of `c₄`. -/
def kpC4f3 (K : Type) [Field K] : Polynomial K :=
  X ^ 8 - 4 * X ^ 7 + 7 * X ^ 6 - 2 * X ^ 5 + 15 * X ^ 4 + 2 * X ^ 3 + 7 * X ^ 2 + 4 * X + 1

/-- The numerator `u²⁰+228u¹⁵+494u¹⁰-228u⁵+1` of `c₄`, factored. -/
def kpC4Num (K : Type) [Field K] : Polynomial K := kpC4f1 K * kpC4f2 K * kpC4f3 K

/-- `u¹⁰ - 11u⁵ - 1`. -/
def kpDeltaPoly (K : Type) [Field K] : Polynomial K := X ^ 10 - C 11 * X ^ 5 - 1

/-- The polynomial encoding `j = 1728`: with `c₄ = (kpC4Num u)/(625u⁸)` and
`Δ = (kpDelta u)⁵/(5¹²u¹⁹)` the equation `c₄³ = 1728·Δ` is equivalent to
`(kpC4Num u)³ = 1728·u⁵·(kpDelta u)⁵`. -/
def kpJEqPoly (K : Type) [Field K] : Polynomial K :=
  (kpC4Num K) ^ 3 - C (1728 : K) * X ^ 5 * (kpDeltaPoly K) ^ 5

/-- The product of the five "bad" polynomials. -/
def kpBadPoly (K : Type) [Field K] : Polynomial K :=
  kpWPoly K * kpC4f1 K * kpC4f2 K * kpC4f3 K * kpJEqPoly K

/-- The exceptional set: the poles of the coefficients, the zeros of `c₄`, and the solutions of
`j = 1728`. -/
def kpBad (K : Type) [Field K] [DecidableEq K] : Finset K := (kpBadPoly K).roots.toFinset

/-! ## Evaluations of the polynomials at `u` -/

private lemma eval_kpWPoly (K : Type) [Field K] (u : K) :
    (kpWPoly K).eval u = u ^ 5 - 1 / 2 := by
  rw [kpWPoly, eval_sub, eval_pow, eval_X, eval_C]

private lemma eval_kpC4f1 (K : Type) [Field K] (u : K) :
    (kpC4f1 K).eval u = u ^ 4 + 3 * u ^ 3 - u ^ 2 - 3 * u + 1 := by
  rw [kpC4f1]
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_natCast, eval_ofNat, eval_one]

private lemma eval_kpC4f2 (K : Type) [Field K] (u : K) :
    (kpC4f2 K).eval u =
      u ^ 8 + u ^ 7 + 7 * u ^ 6 - 7 * u ^ 5 + 7 * u ^ 3 + 7 * u ^ 2 - u + 1 := by
  rw [kpC4f2]
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_natCast, eval_ofNat, eval_one]

private lemma eval_kpC4f3 (K : Type) [Field K] (u : K) :
    (kpC4f3 K).eval u =
      u ^ 8 - 4 * u ^ 7 + 7 * u ^ 6 - 2 * u ^ 5 + 15 * u ^ 4 + 2 * u ^ 3 + 7 * u ^ 2 + 4 * u + 1 := by
  rw [kpC4f3]
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_natCast, eval_ofNat, eval_one]

private lemma eval_kpC4Num (K : Type) [Field K] (u : K) :
    (kpC4Num K).eval u =
      (u ^ 4 + 3 * u ^ 3 - u ^ 2 - 3 * u + 1) *
          (u ^ 8 + u ^ 7 + 7 * u ^ 6 - 7 * u ^ 5 + 7 * u ^ 3 + 7 * u ^ 2 - u + 1) *
        (u ^ 8 - 4 * u ^ 7 + 7 * u ^ 6 - 2 * u ^ 5 + 15 * u ^ 4 + 2 * u ^ 3 + 7 * u ^ 2 + 4 * u + 1) := by
  rw [kpC4Num, eval_mul, eval_mul, eval_kpC4f1, eval_kpC4f2, eval_kpC4f3]

private lemma eval_kpDeltaPoly (K : Type) [Field K] (u : K) :
    (kpDeltaPoly K).eval u = kpDelta K u := by
  rw [kpDeltaPoly, kpDelta]
  simp only [eval_sub, eval_mul, eval_pow, eval_X, eval_C]
  norm_num

/-! ## Nonvanishing of the polynomials used -/

private lemma kpWPoly_ne_zero (K : Type) [Field K] : kpWPoly K ≠ 0 :=
  (Polynomial.monic_X_pow_sub_C (1 / 2 : K) (by norm_num)).ne_zero

private lemma kpC4f1_ne_zero (K : Type) [Field K] : kpC4f1 K ≠ 0 := by
  intro h
  have h1 : (kpC4f1 K).eval 0 = 0 := by rw [h]; simp
  rw [eval_kpC4f1] at h1
  norm_num at h1

private lemma kpC4f2_ne_zero (K : Type) [Field K] : kpC4f2 K ≠ 0 := by
  intro h
  have h1 : (kpC4f2 K).eval 0 = 0 := by rw [h]; simp
  rw [eval_kpC4f2] at h1
  norm_num at h1

private lemma kpC4f3_ne_zero (K : Type) [Field K] : kpC4f3 K ≠ 0 := by
  intro h
  have h1 : (kpC4f3 K).eval 0 = 0 := by rw [h]; simp
  rw [eval_kpC4f3] at h1
  norm_num at h1

private lemma kpC4Num_ne_zero (K : Type) [Field K] : kpC4Num K ≠ 0 :=
  mul_ne_zero (mul_ne_zero (kpC4f1_ne_zero K) (kpC4f2_ne_zero K)) (kpC4f3_ne_zero K)

private lemma kpJEqPoly_ne_zero (K : Type) [Field K] : kpJEqPoly K ≠ 0 := by
  intro h
  have h1 : (kpJEqPoly K).eval 0 = 0 := by rw [h]; simp
  rw [kpJEqPoly, kpC4Num, kpC4f1, kpC4f2, kpC4f3, kpDeltaPoly] at h1
  norm_num at h1

private lemma kpBadPoly_ne_zero (K : Type) [Field K] : kpBadPoly K ≠ 0 :=
  mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero (mul_ne_zero (kpWPoly_ne_zero K) (kpC4f1_ne_zero K)) (kpC4f2_ne_zero K))
      (kpC4f3_ne_zero K))
    (kpJEqPoly_ne_zero K)

/-! ## Membership in `kpBad` from a vanishing factor -/

private lemma mem_kpBad_of_eval {K : Type} [Field K] [DecidableEq K] {u : K}
    (h : (kpBadPoly K).eval u = 0) : u ∈ kpBad K := by
  rw [kpBad, Multiset.mem_toFinset, Polynomial.mem_roots (kpBadPoly_ne_zero K)]
  exact h

private lemma mem_kpBad_of_kpWPoly {K : Type} [Field K] [DecidableEq K] {u : K}
    (h : (kpWPoly K).eval u = 0) : u ∈ kpBad K := by
  refine mem_kpBad_of_eval ?_
  rw [kpBadPoly]
  simp only [eval_mul, h, zero_mul]

private lemma mem_kpBad_of_kpC4f1 {K : Type} [Field K] [DecidableEq K] {u : K}
    (h : (kpC4f1 K).eval u = 0) : u ∈ kpBad K := by
  refine mem_kpBad_of_eval ?_
  rw [kpBadPoly]
  simp only [eval_mul, h, zero_mul, mul_zero]

private lemma mem_kpBad_of_kpC4f2 {K : Type} [Field K] [DecidableEq K] {u : K}
    (h : (kpC4f2 K).eval u = 0) : u ∈ kpBad K := by
  refine mem_kpBad_of_eval ?_
  rw [kpBadPoly]
  simp only [eval_mul, h, zero_mul, mul_zero]

private lemma mem_kpBad_of_kpC4f3 {K : Type} [Field K] [DecidableEq K] {u : K}
    (h : (kpC4f3 K).eval u = 0) : u ∈ kpBad K := by
  refine mem_kpBad_of_eval ?_
  rw [kpBadPoly]
  simp only [eval_mul, h, zero_mul, mul_zero]

private lemma mem_kpBad_of_kpJEqPoly {K : Type} [Field K] [DecidableEq K] {u : K}
    (h : (kpJEqPoly K).eval u = 0) : u ∈ kpBad K := by
  refine mem_kpBad_of_eval ?_
  rw [kpBadPoly]
  simp only [eval_mul, h, mul_zero]

/-! ## The arithmetic of the exceptional set -/

/-- In a field of characteristic `≠ 5`, the numeral `5` is nonzero. -/
private lemma five_ne_zero_of_ringChar_ne {K : Type} [Field K] (hk : ringChar K ≠ 5) :
    (5 : K) ≠ 0 := by
  rcases CharP.char_is_prime_or_zero K (ringChar K) with hp | hz
  · intro h0
    have hdvd : ringChar K ∣ 5 := (ringChar.spec K 5).mp h0
    rcases (by norm_num : Nat.Prime 5).eq_one_or_self_of_dvd (ringChar K) hdvd with h1 | h5
    · exact hp.ne_one h1
    · exact hk h5
  · haveI : CharZero K := (CharP.charP_zero_iff_charZero K).mp (ringChar.eq_iff.mp hz)
    norm_num

/-- `kpW K u ≠ 0` for `u ∉ kpBad K`. -/
private lemma kpW_ne_zero_of_notMem {K : Type} [Field K] [DecidableEq K] {u : K}
    (hu : u ∉ kpBad K) : kpW K u ≠ 0 := by
  intro h
  have h21 : (2 : K) * u ^ 5 = 1 := sub_eq_zero.mp h
  have hu5 : u ^ 5 = (1 / 2 : K) := by
    by_cases h2 : (2 : K) = 0
    · rw [h2, zero_mul] at h21
      exact absurd h21 zero_ne_one
    · rw [one_div]
      exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h21)
  exact hu (mem_kpBad_of_kpWPoly (by rw [eval_kpWPoly, hu5, sub_self]))

/-- `(kpC4Num K).eval u ≠ 0` for `u ∉ kpBad K`. -/
private lemma kpC4Num_eval_ne_zero_of_notMem {K : Type} [Field K] [DecidableEq K] {u : K}
    (hu : u ∉ kpBad K) : (kpC4Num K).eval u ≠ 0 := by
  intro h
  rw [kpC4Num, eval_mul, eval_mul] at h
  rcases mul_eq_zero.mp h with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact hu (mem_kpBad_of_kpC4f1 h)
    · exact hu (mem_kpBad_of_kpC4f2 h)
  · exact hu (mem_kpBad_of_kpC4f3 h)

/-- The polynomial condition `(kpC4Num u)³ = 1728·u⁵·(kpDelta u)⁵` puts `u` into `kpBad K`. -/
private lemma mem_kpBad_of_j_eq {K : Type} [Field K] [DecidableEq K] {u : K}
    (h : (kpC4Num K).eval u ^ 3 = 1728 * u ^ 5 * (kpDeltaPoly K).eval u ^ 5) :
    u ∈ kpBad K := by
  refine mem_kpBad_of_kpJEqPoly ?_
  rw [kpJEqPoly]
  simp only [eval_sub, eval_mul, eval_pow, eval_X, eval_C]
  rw [h, sub_self]

/-- **The `j = 1728` condition.**  If `c₄³ = 1728·Δ` for the parametric model, with the
denominators cleared as `c₄ = (kpC4Num u)/(625u⁸)` and `Δ = (kpDelta u)⁵/(5¹²u¹⁹)`, then `u` lies
in the exceptional set. -/
private lemma mem_kpBad_of_c4_eq {K : Type} [Field K] [DecidableEq K] (hk : ringChar K ≠ 5)
    {u : K} (hu0 : u ≠ 0)
    (hc4 : (kpE K u).c₄ = (kpC4Num K).eval u / (625 * u ^ 8))
    (hDel : (kpE K u).Δ = (kpDelta K u) ^ 5 / (5 ^ 12 * u ^ 19))
    (h3 : (kpE K u).c₄ ^ 3 = 1728 * (kpE K u).Δ) :
    u ∈ kpBad K := by
  have h5 : (5 : K) ≠ 0 := five_ne_zero_of_ringChar_ne hk
  have hexp : ((5 : K) ^ 12 * u ^ 24) ≠ 0 := mul_ne_zero (pow_ne_zero 12 h5) (pow_ne_zero 24 hu0)
  have hN : (kpC4Num K).eval u ^ 3 = 1728 * u ^ 5 * (kpDeltaPoly K).eval u ^ 5 := by
    have hc4pow : (kpE K u).c₄ ^ 3 = (kpC4Num K).eval u ^ 3 / ((5 : K) ^ 12 * u ^ 24) := by
      rw [hc4, div_pow, mul_pow, show ((625 : K)) ^ 3 = (5 : K) ^ 12 by norm_num,
        show ((u : K) ^ 8) ^ 3 = u ^ 24 by ring]
    have hEq : (kpC4Num K).eval u ^ 3 / ((5 : K) ^ 12 * u ^ 24) =
        (1728 * u ^ 5 * (kpDelta K u) ^ 5) / ((5 : K) ^ 12 * u ^ 24) := by
      rw [← hc4pow, h3, hDel]
      field_simp
    have hfin := (div_left_inj' hexp).mp hEq
    rw [← eval_kpDeltaPoly] at hfin
    exact hfin
  exact mem_kpBad_of_j_eq hN

/-! ## The main theorem -/

theorem exists_kleinData_kleinParam {K : Type} [Field K] [Infinite K] (hk : ringChar K ≠ 5) :
    ∃ bad : Finset K, ∀ u : K, u ∉ bad → u ≠ 0 → u ^ 10 - 11 * u ^ 5 - 1 ≠ 0 →
      ∃ D : Work.MotV.KleinData K, D.Good ∧ D.a = u ∧ D.b = 1 := by
  classical
  have h5 : (5 : K) ≠ 0 := five_ne_zero_of_ringChar_ne hk
  have h625 : (625 : K) ≠ 0 := by
    rw [show (625 : K) = 5 ^ 4 by norm_num]
    exact pow_ne_zero 4 h5
  have h5p : (5 : K) ^ 12 ≠ 0 := pow_ne_zero 12 h5
  refine ⟨kpBad K, fun u hu hu0 hΔ0 => ?_⟩
  have hΔ : kpDelta K u ≠ 0 := by
    rw [kpDelta]
    exact hΔ0
  have hw : kpW K u ≠ 0 := kpW_ne_zero_of_notMem hu
  have hc4N : (kpC4Num K).eval u ≠ 0 := kpC4Num_eval_ne_zero_of_notMem hu
  obtain ⟨hel, hDel, hc4⟩ := kpE_invariants K hk u hu0 hw hΔ
  haveI := hel
  -- the numerator of `c₄` written as an evaluation
  have hc4'' : (kpE K u).c₄ = (kpC4Num K).eval u / (625 * u ^ 8) := by
    rw [hc4, ← eval_kpC4Num]
  have hDne : (kpE K u).Δ ≠ 0 := by
    rw [hDel]
    exact div_ne_zero (pow_ne_zero 5 hΔ) (mul_ne_zero h5p (pow_ne_zero 19 hu0))
  have hc4ne : (kpE K u).c₄ ≠ 0 := by
    rw [hc4'']
    exact div_ne_zero hc4N (mul_ne_zero h625 (pow_ne_zero 8 hu0))
  refine ⟨kpData K u, ⟨hel, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, rfl⟩
  · show u * 1 ≠ 0
    rw [mul_one]
    exact hu0
  · -- `j ≠ 0`
    show (kpE K u).j ≠ 0
    rw [WeierstrassCurve.j_eq]
    exact mul_ne_zero (inv_ne_zero hDne) (pow_ne_zero 3 hc4ne)
  · -- `j ≠ 1728`
    show (kpE K u).j ≠ 1728
    intro hj
    rw [WeierstrassCurve.j_eq] at hj
    have h3 : (kpE K u).c₄ ^ 3 = 1728 * (kpE K u).Δ := by
      have h := congrArg (fun x => x * (kpE K u).Δ) hj
      rw [mul_assoc] at h
      rw [mul_comm ((kpE K u).c₄ ^ 3) ((kpE K u).Δ), ← mul_assoc, inv_mul_cancel₀ hDne,
        one_mul] at h
      exact h
    exact hu (mem_kpBad_of_c4_eq hk hu0 hc4'' hDel h3)
  · intro L _ _ k
    exact kpData_klein_eq K hk u hu0 hw hΔ L k
  · intro L _ _
    exact kpData_coord0_ne K hk u hu0 hΔ L
  · intro L _ _ ζ hζ
    exact kpData_T_diag K hk u hu0 hw hΔ L ζ hζ
  · exact kpData_spans_good K hk u hu0 hw hΔ

end
end Work.MotT
