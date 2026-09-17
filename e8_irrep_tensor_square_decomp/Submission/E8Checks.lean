import Submission.E8Engine
import Submission.E8Enum

/-!
# The Freudenthal recursion for the candidate character of `L(ω₁+ω₈)`

This file supplies the **last hypothesis** `(d)` of `Submission.E8Character.eq_of_freudenthal` for
the candidate multiplicity function `Submission.E8Numerics.mfun`: Freudenthal's recursion at the
six dominant weights other than `λ = ω₁+ω₈`.

Two ingredients keep the `decide` proofs inside the kernel budget:

* the arithmetic is done with the hand-written engine `Submission.E8Engine` (matrix lookups and
  `List.get` replaced by `if`-chains, `k • α` by the coordinatewise `smulE`);
* the `k`-sum is **pruned**: `mfun (ν + k·αⱼ)` can only be non-zero when
  `⟪λ-ν-k·αⱼ, ρ⟫ ≥ 0`, i.e. `k·⟪αⱼ,ρ⟫ ≤ ⟪λ-ν,ρ⟫`.  This cuts the 23040 terms of the six
  unpruned computations down to 4392 (`ν = ω₂: 28`, `ω₇: 127`, `ω₁: 237`, `2ω₈: 99`, `ω₈: 370`,
  `0: 618` at the *coordinatewise* bound; the height bound used here is slightly weaker).
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Submission.E8Checks

open Submission.WeylReflect
open Submission.E8Character Submission.E8Orbit Submission.E8Casimir Submission.E8Numerics
open Submission.E8Engine Submission.E8Enum

/-- **Pruning a sum over `Icc 1 N`.**  If `K ≤ N` and the summand vanishes above `K`, then the sum
over `Finset.Icc 1 N` equals the sum over `Finset.Icc 1 K`. -/
theorem sum_Icc_eq_of_gt {M : Type*} [AddCommMonoid M] {f : ℕ → M} :
    ∀ {K N : ℕ}, K ≤ N → (∀ k, K < k → f k = 0) →
      (∑ k ∈ Finset.Icc 1 N, f k) = ∑ k ∈ Finset.Icc 1 K, f k := by
  intro K N
  induction N with
  | zero =>
    intro hK _
    have h0 : K = 0 := Nat.eq_zero_of_le_zero hK
    subst h0
    simp
  | succ n ih =>
    intro hK h
    rcases eq_or_lt_of_le hK with h' | h'
    · subst h'
      rfl
    · rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1),
          ih (by omega) (fun k hk => h k (by omega)), h (n + 1) h', add_zero]

/-- The pruned upper bound of the `k`-sum for the `j`-th root. -/
def Kb (ν : Fin 8 → ℤ) (j : Fin 120) : ℕ := (htO (lam - ν)).toNat / (htO (pRn j)).toNat

/-- The **pruned** Freudenthal recursion sum. -/
def freudGp (m : (Fin 8 → ℤ) → ℤ) (ν : Fin 8 → ℤ) : ℤ :=
  ∑ j : Fin 120, ∑ k ∈ Finset.Icc 1 (Kb ν j), Gfun m (ν + k • pRn j) j

/-- The **loose** Freudenthal recursion sum (as in the hypothesis `(d)` of `eq_of_freudenthal`,
with `pR` replaced by the extensionally equal `pRn`). -/
def freudG (m : (Fin 8 → ℤ) → ℤ) (ν : Fin 8 → ℤ) : ℤ :=
  ∑ j : Fin 120, ∑ k ∈ Finset.Icc 1 (htOf (lam - ν)).toNat, Gfun m (ν + k • pRn j) j

/-- `htOf γ ≤ (htOf γ).toNat`. -/
lemma htOf_le_toNat (γ : Fin 8 → ℤ) : htOf γ ≤ ((htOf γ).toNat : ℤ) := by
  by_cases h : 0 ≤ htOf γ
  · exact le_of_eq (Int.toNat_of_nonneg h).symm
  · simp only [not_le] at h
    have hz : (htOf γ).toNat = 0 := Int.toNat_of_nonpos (by omega)
    rw [hz]
    omega

/-- The vanishing lemma: a term whose `k`-shift leaves the cone below `λ` contributes `0`. -/
lemma mfun_eq_zero_of_height {ν : Fin 8 → ℤ} {j : Fin 120} {k : ℕ}
    (h : htOf (lam - ν) < (k : ℤ) * htOf (pR j)) : mfun (ν + k • pR j) = 0 := by
  by_contra hne
  have hkey : htOf (lam - (ν + k • pR j)) = htOf (lam - ν) - (k : ℤ) * htOf (pR j) := by
    rw [show lam - (ν + k • pR j) = (lam - ν) - k • pR j by abel, htOf_sub, htOf_nsmul]
  rcases mfun_support hne with h1 | h1
  · rw [h1, htOf_zero] at hkey
    omega
  · have := htOf_nonneg h1
    omega

/-- **The pruning step**: the loose and the pruned Freudenthal sums agree. -/
lemma freudGp_eq_freudG (m : (Fin 8 → ℤ) → ℤ)
    (hm : ∀ v, m v ≠ 0 → lam - v = 0 ∨ posCon (lam - v)) (ν : Fin 8 → ℤ) :
    freudGp m ν = freudG m ν := by
  simp only [freudGp, freudG]
  refine Finset.sum_congr rfl fun j _ => (sum_Icc_eq_of_gt ?_ ?_).symm
  · rw [Kb, htO_eq]
    exact Nat.div_le_self _ _
  · intro k hk
    have hj : (htO (pRn j)).toNat = (htOf (pR j)).toNat := by rw [htO_eq, pRn_eq]
    have hhj : ((htO (pRn j)).toNat : ℤ) = htOf (pR j) := by
      rw [hj, Int.toNat_of_nonneg (le_trans (by norm_num) (htOf_pR j))]
    have hpos : 0 < (htO (pRn j)).toNat := by
      rw [hj]
      have := htOf_pR_pos j
      omega
    have hk' : (htOf (lam - ν)).toNat / (htO (pRn j)).toNat < k := by
      simpa only [Kb, htO_eq] using hk
    have hlt : (htOf (lam - ν)).toNat < k * (htO (pRn j)).toNat :=
      (Nat.div_lt_iff_lt_mul hpos).mp hk'
    have hmain : htOf (lam - ν) < (k : ℤ) * htOf (pR j) := by
      have h1 : ((htOf (lam - ν)).toNat : ℤ) < ((k * (htO (pRn j)).toNat : ℕ) : ℤ) := by
        exact_mod_cast hlt
      have h2 : htOf (lam - ν) ≤ ((htOf (lam - ν)).toNat : ℤ) := htOf_le_toNat _
      have h3 : (((k * (htO (pRn j)).toNat : ℕ)) : ℤ) = (k : ℤ) * htOf (pR j) := by
        push_cast
        rw [hhj]
      omega
    have hz : m (ν + k • pRn j) = 0 := by
      by_contra hne'
      have hpr : htOf (pRn j) = htOf (pR j) := by rw [congrFun pRn_eq j]
      have hsub : htOf (lam - (ν + k • pRn j)) = htOf (lam - ν) - (k : ℤ) * htOf (pR j) := by
        rw [show lam - (ν + k • pRn j) = (lam - ν) - k • pRn j by abel, htOf_sub, htOf_nsmul, hpr]
      rcases hm _ hne' with h0 | h0
      · have hz0 : htOf (lam - (ν + k • pRn j)) = 0 := by rw [h0, htOf_zero]
        omega
      · have hz0 : 0 ≤ htOf (lam - (ν + k • pRn j)) := htOf_nonneg h0
        omega
    rw [Gfun, hz, mul_zero]


/-- The **guarded** Freudenthal sum: the norm test is evaluated with the quadratic formula `quad`,
which avoids building the weight `ν + k·αⱼ`.  This is what makes the `decide` proofs feasible. -/
def freudGq (m : (Fin 8 → ℤ) → ℤ) (ν : Fin 8 → ℤ) : ℤ :=
  ∑ j : Fin 120, ∑ k ∈ Finset.Icc 1 (Kb ν j),
    if normTable (quad ν j k) = true then Gfun m (ν + k • pRn j) j else 0

/-- The guard does not change the sum: when `normTable (quad ν j k) = false` the norm of
`ν + k·αⱼ` is outside `{0,2,4,6,8,10}`, so `mfunE` vanishes there. -/
lemma freudGq_eq_freudGp (ν : Fin 8 → ℤ) : freudGq mfunE ν = freudGp mfunE ν := by
  simp only [freudGq, freudGp]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  by_cases h : normTable (quad ν j k) = true
  · rw [if_pos h]
  · rw [if_neg h]
    have hη : normOkE (ν + k • pRn j) = false := by
      rw [normOkE, ← quad_eq_qE ν j k]
      simpa using h
    simp only [Gfun, mfunE, hη, Bool.false_eq_true, if_false, mul_zero]

/-- The loose sum in terms of `brk` and `m`. -/
lemma freudG_eq (m : (Fin 8 → ℤ) → ℤ) (ν : Fin 8 → ℤ) : freudG m ν =
    ∑ j : Fin 120, ∑ k ∈ Finset.Icc 1 (htOf (lam - ν)).toNat,
      brk (ν + k • pR j) j * m (ν + k • pR j) := by
  simp only [freudG]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [Gfun, brkF_eq, congrFun pRn_eq j]

/-! ## The six Freudenthal recursion checks for the candidate character

The six dominant weights below `λ = ω₁+ω₈` are `ω₂ = e 1`, `2ω₈ = 2 • e 7`, `ω₇ = e 6`,
`ω₁ = e 0`, `ω₈ = e 7` and `0` (in the order of `the7`). -/

theorem check_1 : (BintE lam - BintE (e 1)) * mfunE (e 1) = 2 * freudGq mfunE (e 1) := by
  decide

theorem check_2 : (BintE lam - BintE (2 • e 7)) * mfunE (2 • e 7)
    = 2 * freudGq mfunE (2 • e 7) := by
  decide

theorem check_3 : (BintE lam - BintE (e 6)) * mfunE (e 6) = 2 * freudGq mfunE (e 6) := by
  decide

theorem check_4 : (BintE lam - BintE (e 0)) * mfunE (e 0) = 2 * freudGq mfunE (e 0) := by
  decide

theorem check_5 : (BintE lam - BintE (e 7)) * mfunE (e 7) = 2 * freudGq mfunE (e 7) := by
  decide

theorem check_6 : (BintE lam - BintE 0) * mfunE 0 = 2 * freudGq mfunE 0 := by
  decide

/-- The support hypothesis for the fast candidate character. -/
theorem mfunE_support : ∀ v : Fin 8 → ℤ, mfunE v ≠ 0 → lam - v = 0 ∨ posCon (lam - v) :=
  fun v h => mfun_support (by simpa only [mfunE_eq_mfun] using h)

/-- **Freudenthal's recursion for the candidate character `mfun`** at every dominant weight in the
cone strictly below `λ`.  This is hypothesis `(d)` of `eq_of_freudenthal`. -/
theorem freudenthal_mfun (ν : Fin 8 → ℤ) (hν : Dominant ν)
    (hne : lam - ν ≠ 0) (hpos : posCon (lam - ν)) :
    (Bint lam - Bint ν) * (mfun ν : ℚ) =
      2 * ∑ j : Fin 120, ∑ k ∈ Finset.Icc 1 (htOf (lam - ν)).toNat,
          (brk (ν + k • pR j) j : ℚ) * (mfun (ν + k • pR j) : ℚ) := by
  have hmem : ν ∈ the7 :=
    mem_the7 (allNonneg_true.mpr hν) (posB_true.mpr hpos)
  rcases mem_the7_cases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd (sub_self lam) hne
  · have h := check_1
    have hg : freudGq mfunE (e 1) = freudG mfunE (e 1) :=
      (freudGq_eq_freudGp (e 1)).trans (freudGp_eq_freudG mfunE mfunE_support (e 1))
    rw [BintE_eq, BintE_eq, mfunE_eq_mfun, hg, freudG_eq] at h
    simp only [mfunE_eq_mfun] at h
    exact_mod_cast h
  · have h := check_2
    have hg : freudGq mfunE (2 • e 7) = freudG mfunE (2 • e 7) :=
      (freudGq_eq_freudGp (2 • e 7)).trans (freudGp_eq_freudG mfunE mfunE_support (2 • e 7))
    rw [BintE_eq, BintE_eq, mfunE_eq_mfun, hg, freudG_eq] at h
    simp only [mfunE_eq_mfun] at h
    exact_mod_cast h
  · have h := check_3
    have hg : freudGq mfunE (e 6) = freudG mfunE (e 6) :=
      (freudGq_eq_freudGp (e 6)).trans (freudGp_eq_freudG mfunE mfunE_support (e 6))
    rw [BintE_eq, BintE_eq, mfunE_eq_mfun, hg, freudG_eq] at h
    simp only [mfunE_eq_mfun] at h
    exact_mod_cast h
  · have h := check_4
    have hg : freudGq mfunE (e 0) = freudG mfunE (e 0) :=
      (freudGq_eq_freudGp (e 0)).trans (freudGp_eq_freudG mfunE mfunE_support (e 0))
    rw [BintE_eq, BintE_eq, mfunE_eq_mfun, hg, freudG_eq] at h
    simp only [mfunE_eq_mfun] at h
    exact_mod_cast h
  · have h := check_5
    have hg : freudGq mfunE (e 7) = freudG mfunE (e 7) :=
      (freudGq_eq_freudGp (e 7)).trans (freudGp_eq_freudG mfunE mfunE_support (e 7))
    rw [BintE_eq, BintE_eq, mfunE_eq_mfun, hg, freudG_eq] at h
    simp only [mfunE_eq_mfun] at h
    exact_mod_cast h
  · have h := check_6
    have hg : freudGq mfunE 0 = freudG mfunE 0 :=
      (freudGq_eq_freudGp 0).trans (freudGp_eq_freudG mfunE mfunE_support 0)
    rw [BintE_eq, BintE_eq, mfunE_eq_mfun, hg, freudG_eq] at h
    simp only [mfunE_eq_mfun] at h
    exact_mod_cast h

/-! ## The complete hypothesis set `(a)`–`(d)` for the candidate character -/

/-- Hypothesis `(a)`: `mfun` takes the value `1` at `λ`. -/
theorem mfun_lam : mfun lam = 1 := by decide

lemma dominant_lam : Dominant lam := by
  intro i
  fin_cases i <;> decide

/-- **`mfun` is *the* multiplicity function satisfying the four Freudenthal hypotheses.**  Any
`m'` with (a) `m' λ = 1`, (b) the support condition, (c) invariance under the dominant conjugate and
(d) Freudenthal's recursion at the dominant weights below `λ` agrees with `mfun` everywhere (over
`ℚ`).  This is `eq_of_freudenthal` fed with the four properties proved in this file. -/
theorem mfun_unique (m' : (Fin 8 → ℤ) → ℚ) (ha' : m' lam = 1)
    (hb' : ∀ v, m' v ≠ 0 → lam - v = 0 ∨ posCon (lam - v))
    (hc' : ∀ v, m' (dc v) = m' v)
    (hd' : ∀ ν, Dominant ν → lam - ν ≠ 0 → posCon (lam - ν) →
      (Bint lam - Bint ν) * m' ν
        = 2 * ∑ j : Fin 120, ∑ k ∈ Finset.Icc 1 (htOf (lam - ν)).toNat,
            (brk (ν + k • pR j) j : ℚ) * m' (ν + k • pR j)) :
    ∀ v, (mfun v : ℚ) = m' v :=
  eq_of_freudenthal (lam := lam) dominant_lam
    (ha := by exact_mod_cast mfun_lam)
    (hb := fun v h => mfun_support (fun h0 => h (by simp only [h0, Int.cast_zero])))
    (hc := fun v => by rw [← dcX_eq_dc v, mfun_dcX])
    (hd := freudenthal_mfun)
    ha' hb' hc' hd'


end Submission.E8Checks
