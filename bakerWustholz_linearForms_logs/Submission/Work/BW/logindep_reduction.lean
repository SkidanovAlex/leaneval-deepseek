import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.small_relation
import Submission.Work.BW.liouville_logForm
import Submission.Work.BW.minimal_dependent
import Submission.Work.BW.prod_drop_bounds
import Submission.Work.BW.fallback_arith
import Submission.Work.BW.elim_arith

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD NOTES (Baker–Wüstholz drive). Route design: BW = Baker–Wüstholz, Crelle 442 (1993); section and lemma numbers are BW's. Shared definitions are in Submission.Work.BW.Defs (namespace Work.BW).
Sibling nodes are dispatched in parallel, each as module Submission.Work.BW.<name> with its statement already in place: liouville_logForm, lehmer_bound, minkowski_basis, kummer_indep, logHeight_intermediate, discriminant_bound, siegel_numberField, small_relation, kummer_reduction, aux_poly, analytic_core, bw_independent, logindep_reduction. multiplicity_prop and group_reduction come later.
If your proof needs a sibling's result, IMPORT its module and use its statement. Do NOT reprove it, and do not restate it under another name. Its sorry disappears when it lands.
The constants are tight (see the notes below): do not weaken any numeric constant in your statement. If you believe the statement is false, give a concrete counterexample.

# logindep_reduction — BW §6 (p. 26–27); 2–3k lines, medium risk

**Claim.** If the principal logs are ℚ-dependent, then `BWHolds φ α` follows from `BWHolds`
for fewer logs.

**Steps.**
1. **Fallback.** As in `bw_independent` step 2, reduce to primitive `b₀` with `H ≥ X(n,d)`,
   using `liouville_logForm`.
2. **Small relation.** Take a minimal dependent subset `{1..m}` (after reindexing), and order
   it so that `h'(α_m)` is maximal in it. `small_relation` gives `y` with all `yᵢ ≠ 0`,
   `∑yᵢℓᵢ = 0`, and `Y = max|yᵢ| ≤ (9md³)^m∏h'`.
   * The case `α_i = 1` (`ℓᵢ = 0`) is included, with `m = 1`.
3. **Eliminate `α_m`.** Set `b⁽ᵐ⁾ = y_m b₀ - b₀ₘ y`. Then `lam(b⁽ᵐ⁾) = y_m Λ₀ ≠ 0`, and the
   `m`-th coordinate vanishes, so this is a form in `n-1` logs.
4. **Apply `IH` at `n-1`** with `B' = max(2, 2YB)`.
5. **Arithmetic (BW p. 27).**
   * `max(log B', 1/d)/h'(α_m) ≤ d(H + 3m log(9md))`. This uses `h'(α_m) ≥ 1/d`,
     `log x/x ≤ 1/e`, and `H ≥ log(9md)`.
   * `log|y_m| ≤ 3md^m H∏h'`.
   * `(3m+1)dC(n-1,d) + 3md^m ≤ C(n,d)`. This holds with large room, because
     `C(n,d)/C(n-1,d) ≥ 32(n+1)nd`.
-/

namespace Work.BW

open Complex
open BakerWustholz

/-! ## Auxiliary lemmas -/

/-- The modified height is at least `1/d`. -/
lemma one_div_finrank_le_modifiedHeight {K : Type*} [Field K] [NumberField K]
    (φ : K →+* ℂ) (β : K) :
    1 / (Module.finrank ℚ K : ℝ) ≤ modifiedHeight φ β := by
  simp only [BakerWustholz.modifiedHeight]
  exact le_trans (le_max_right _ _) (le_max_right _ _)

/-- Reindexing identity for the extension of a relation `y` supported along an injective `e`. -/
lemma sum_extend {n m : ℕ} (e : Fin m → Fin n) (he : Function.Injective e) (y : Fin m → ℤ)
    (F : Fin n → ℂ) :
    (∑ i : Fin n, (((∑ j : Fin m, if e j = i then y j else 0) : ℤ) : ℂ) * F i)
      = ∑ j : Fin m, (y j : ℂ) * F (e j) := by
  have h1 : ∀ i : Fin n, (((∑ j : Fin m, if e j = i then y j else 0) : ℤ) : ℂ)
      = ∑ j : Fin m, (if e j = i then (y j : ℂ) else 0) := by
    intro i
    rw [Int.cast_sum]
    exact Finset.sum_congr rfl fun j _ => by by_cases h : e j = i <;> simp [h]
  calc (∑ i : Fin n, (((∑ j : Fin m, if e j = i then y j else 0) : ℤ) : ℂ) * F i)
      = ∑ i : Fin n, (∑ j : Fin m, (if e j = i then (y j : ℂ) else 0)) * F i :=
        Finset.sum_congr rfl fun i _ => by rw [h1 i]
    _ = ∑ i : Fin n, ∑ j : Fin m, (if e j = i then (y j : ℂ) else 0) * F i :=
        Finset.sum_congr rfl fun i _ => Finset.sum_mul ..
    _ = ∑ j : Fin m, ∑ i : Fin n, (if e j = i then (y j : ℂ) else 0) * F i :=
        Finset.sum_comm
    _ = ∑ j : Fin m, (y j : ℂ) * F (e j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        have h2 : (∑ i : Fin n, (if e j = i then (y j : ℂ) else 0) * F i)
            = ∑ i : Fin n, (if e j = i then (y j : ℂ) * F i else 0) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          by_cases h : e j = i <;> simp [h]
        rw [h2, Finset.sum_ite_eq]
        simp

/-- Elimination of one logarithm. -/
lemma elim_identity {n : ℕ} (Yext bvec : Fin n → ℤ) (i0 : Fin n) (F : Fin n → ℂ)
    (hrel : ∑ i : Fin n, (Yext i : ℂ) * F i = 0) :
    (∑ i ∈ Finset.univ.erase i0, (((Yext i0 * bvec i - bvec i0 * Yext i : ℤ)) : ℂ) * F i)
      = (Yext i0 : ℂ) * ∑ i : Fin n, (bvec i : ℂ) * F i := by
  have hterm : ∀ i : Fin n, (((Yext i0 * bvec i - bvec i0 * Yext i : ℤ)) : ℂ) * F i
      = (Yext i0 : ℂ) * ((bvec i : ℂ) * F i) - (bvec i0 : ℂ) * ((Yext i : ℂ) * F i) := by
    intro i; push_cast; ring
  have hfull : (∑ i : Fin n, (((Yext i0 * bvec i - bvec i0 * Yext i : ℤ)) : ℂ) * F i)
      = (Yext i0 : ℂ) * ∑ i : Fin n, (bvec i : ℂ) * F i := by
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hrel]
    ring
  have hzero : (((Yext i0 * bvec i0 - bvec i0 * Yext i0 : ℤ)) : ℂ) * F i0 = 0 := by
    rw [show (Yext i0 * bvec i0 - bvec i0 * Yext i0 : ℤ) = 0 from by ring]
    simp
  have h := Finset.sum_erase_add (Finset.univ : Finset (Fin n))
    (fun i => (((Yext i0 * bvec i - bvec i0 * Yext i : ℤ)) : ℂ) * F i) (Finset.mem_univ i0)
  rw [hzero, add_zero] at h
  rw [h, hfull]

/-- If `n ≤ 1` then any linear form with zero ... -/

theorem logindep_reduction {K : Type*} [Field K] [NumberField K] {n : ℕ} (φ : K →+* ℂ)
    (α : Fin n → K) (hα : ∀ i, α i ≠ 0)
    (hdep : ¬ LinearIndependent ℚ (fun i => Complex.log (φ (α i))))
    (IH : ∀ m < n, ∀ β : Fin m → K, (∀ i, β i ≠ 0) → BWHolds φ β) :
    BWHolds φ α := by
  classical
  intro b B hB hbB hΛ
  have hφα : ∀ i, φ (α i) ≠ 0 := fun i h => hα i (φ.injective (by rw [h, map_zero]))
  set d : ℕ := Module.finrank ℚ K with hd
  have hd1 : 1 ≤ d := by
    have h : 0 < Module.finrank ℚ K := Module.finrank_pos
    omega
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd1)
  -- the maximal coefficient
  set β : ℕ := Finset.univ.sup (fun i : Fin n => (b i).natAbs) with hβ
  have hβval : β = Finset.univ.sup (fun i : Fin n => (b i).natAbs) := hβ
  have hβb : ∀ i, (b i).natAbs ≤ β := fun i => by
    rw [hβval]
    exact Finset.le_sup (f := fun i : Fin n => (b i).natAbs) (Finset.mem_univ i)
  have hβB : β ≤ B := by
    rw [hβval]; exact Finset.sup_le fun i _ => hbB i
  have hlogB : Real.log 2 ≤ Real.log (B : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hB)
  have hlogβB : Real.log (β : ℝ) ≤ Real.log (B : ℝ) := by
    rcases Nat.eq_zero_or_pos β with h | h
    · rw [h]
      simp only [Nat.cast_zero, Real.log_zero]
      exact Real.log_nonneg (by exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hB))
    · exact Real.log_le_log (by exact_mod_cast h) (by exact_mod_cast hβB)
  have hlogβ : Real.log (β : ℝ) ≤ hL b d := by
    simp only [hL, hβval]
    exact le_max_left _ _
  -- the case `n ≤ 1`
  have hsmall : n ≤ 1 → lam φ α b = 0 := by
    intro hn
    haveI : Subsingleton (Fin n) := ⟨fun a b => by
      have ha := a.isLt; have hb := b.isLt
      exact Fin.ext (by omega)⟩
    have hzero : ∀ i : Fin n, Complex.log (φ (α i)) = 0 := by
      intro i
      by_contra hne
      apply hdep
      rw [Fintype.linearIndependent_iff]
      intro g hg j
      have h1 : g j • Complex.log (φ (α j)) = 0 := by
        have h2 := hg
        rw [Finset.sum_eq_single j] at h2
        · exact h2
        · intro b _ hb
          exact absurd (Subsingleton.elim b j) hb
        · intro h
          exact absurd (Finset.mem_univ j) h
      rcases smul_eq_zero.mp h1 with h2 | h2
      · exact h2
      · exact absurd (by rwa [Subsingleton.elim j i] at h2) hne
    simp [lam, hzero]
  by_cases hn2 : 2 ≤ n
  · have hn1 : 1 ≤ n := by omega
    by_cases hcase : hL b d < Xbw n d
    · -- ============ FALLBACK (Liouville) ============
      have hliou := liouville_logForm φ α hα (fun i => Complex.log (φ (α i)))
        (fun i => Complex.exp_log (hφα i)) b (by simpa [lam] using hΛ)
      rw [← hd] at hliou
      have hPpos : 0 < ∏ i : Fin n, modifiedHeight φ (α i) :=
        Finset.prod_pos fun i _ =>
          lt_of_lt_of_le (one_div_pos.mpr hdpos) (one_div_finrank_le_modifiedHeight φ _)
      have hPlow : (1 : ℝ) / (d : ℝ) ^ n ≤ ∏ i : Fin n, modifiedHeight φ (α i) := by
        have h1 : ∏ i : Fin n, (1 / (d : ℝ)) ≤ ∏ i : Fin n, modifiedHeight φ (α i) :=
          Finset.prod_le_prod₀ (fun i _ => le_of_lt (one_div_pos.mpr hdpos))
            (fun i _ => one_div_finrank_le_modifiedHeight φ _)
        simpa [one_div, inv_pow] using h1
      have hβ1 : 1 ≤ β := by
        obtain ⟨i, hi⟩ : ∃ i : Fin n, b i ≠ 0 := by
          by_contra h
          push_neg at h
          exact hΛ (by simp [lam, h])
        exact le_trans (Int.natAbs_pos.mpr hi) (hβb i)
      have hsum1 : (∑ i : Fin n, ((b i).natAbs : ℝ) * Height.logHeight₁ (α i))
          ≤ (β : ℝ) * ∑ i : Fin n, Height.logHeight₁ (α i) := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (by exact_mod_cast hβb i) (Height.zero_le_logHeight₁ _)
      have hsum2 : (∑ i : Fin n, Height.logHeight₁ (α i))
          ≤ (d : ℝ) * ∑ i : Fin n, modifiedHeight φ (α i) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun i _ => ?_
        have h : Height.logHeight₁ (α i) / (d : ℝ) ≤ modifiedHeight φ (α i) := le_max_left _ _
        have h2 : Height.logHeight₁ (α i) = (d : ℝ) * (Height.logHeight₁ (α i) / (d : ℝ)) := by
          field_simp
        rw [h2]
        exact mul_le_mul_of_nonneg_left h (le_of_lt hdpos)
      have hper : ∀ i : Fin n, modifiedHeight φ (α i)
          ≤ (d : ℝ) ^ (n - 1) * ∏ j : Fin n, modifiedHeight φ (α j) := by
        intro i
        have hmul : modifiedHeight φ (α i) * (∏ j ∈ Finset.univ.erase i, modifiedHeight φ (α j))
            = ∏ j : Fin n, modifiedHeight φ (α j) :=
          Finset.mul_prod_erase Finset.univ (fun j => modifiedHeight φ (α j)) (Finset.mem_univ i)
        have hle : (1 / (d : ℝ)) ^ (n - 1)
            ≤ ∏ j ∈ Finset.univ.erase i, modifiedHeight φ (α j) := by
          have h1 : ∏ j ∈ Finset.univ.erase i, (1 / (d : ℝ))
              ≤ ∏ j ∈ Finset.univ.erase i, modifiedHeight φ (α j) :=
            Finset.prod_le_prod₀ (fun j _ => le_of_lt (one_div_pos.mpr hdpos))
              (fun j _ => one_div_finrank_le_modifiedHeight φ _)
          have h2 : (Finset.univ.erase i).card = n - 1 := by
            rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
          rwa [Finset.prod_const, h2] at h1
        have hpos : 0 ≤ modifiedHeight φ (α i) :=
          le_trans (le_of_lt (one_div_pos.mpr hdpos)) (one_div_finrank_le_modifiedHeight φ _)
        have h3 : modifiedHeight φ (α i) * ((1 / (d : ℝ)) ^ (n - 1))
            ≤ modifiedHeight φ (α i) * ∏ j ∈ Finset.univ.erase i, modifiedHeight φ (α j) :=
          mul_le_mul_of_nonneg_left hle hpos
        rw [hmul] at h3
        have h4 : modifiedHeight φ (α i)
            = (d : ℝ) ^ (n - 1) * (modifiedHeight φ (α i) * (1 / (d : ℝ)) ^ (n - 1)) := by
          have hpow : (d : ℝ) ^ (n - 1) * (1 / (d : ℝ)) ^ (n - 1) = 1 := by
            rw [← mul_pow, mul_one_div, div_self (ne_of_gt hdpos), one_pow]
          rw [show (d : ℝ) ^ (n - 1) * (modifiedHeight φ (α i) * (1 / (d : ℝ)) ^ (n - 1))
              = modifiedHeight φ (α i) * ((d : ℝ) ^ (n - 1) * (1 / (d : ℝ)) ^ (n - 1))
              from by ring, hpow, mul_one]
        rw [h4]
        exact mul_le_mul_of_nonneg_left h3 (by positivity)
      have hsum3 : (∑ i : Fin n, modifiedHeight φ (α i))
          ≤ (n : ℝ) * (d : ℝ) ^ (n - 1) * ∏ i : Fin n, modifiedHeight φ (α i) := by
        calc (∑ i : Fin n, modifiedHeight φ (α i))
            ≤ ∑ _i : Fin n, (d : ℝ) ^ (n - 1) * ∏ j : Fin n, modifiedHeight φ (α j) :=
              Finset.sum_le_sum fun i _ => hper i
          _ = (n : ℝ) * (d : ℝ) ^ (n - 1) * ∏ j : Fin n, modifiedHeight φ (α j) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              ring
      have hsum : (∑ i : Fin n, ((b i).natAbs : ℝ) * Height.logHeight₁ (α i))
          ≤ (n : ℝ) * (β : ℝ) * (d : ℝ) ^ n * ∏ i : Fin n, modifiedHeight φ (α i) := by
        have hd0 : (0 : ℝ) ≤ (d : ℝ) := le_of_lt hdpos
        have hβ0 : (0 : ℝ) ≤ (β : ℝ) := by positivity
        calc (∑ i : Fin n, ((b i).natAbs : ℝ) * Height.logHeight₁ (α i))
            ≤ (β : ℝ) * ∑ i : Fin n, Height.logHeight₁ (α i) := hsum1
          _ ≤ (β : ℝ) * ((d : ℝ) * ∑ i : Fin n, modifiedHeight φ (α i)) :=
              mul_le_mul_of_nonneg_left hsum2 hβ0
          _ ≤ (β : ℝ) * ((d : ℝ) * ((n : ℝ) * (d : ℝ) ^ (n - 1)
                * ∏ i : Fin n, modifiedHeight φ (α i))) := by
              refine mul_le_mul_of_nonneg_left ?_ hβ0
              exact mul_le_mul_of_nonneg_left hsum3 hd0
          _ = (n : ℝ) * (β : ℝ) * (d : ℝ) ^ n * ∏ i : Fin n, modifiedHeight φ (α i) := by
              have hdn : (d : ℝ) ^ (n - 1) * (d : ℝ) = (d : ℝ) ^ n := by
                rw [← pow_succ, Nat.sub_add_cancel hn1]
              rw [← hdn]
              ring
      have harith := fallback_arith hn1 hd1 (β := (β : ℝ))
        (M := max (Real.log (B : ℝ)) (1 / (d : ℝ)))
        (P := ∏ i : Fin n, modifiedHeight φ (α i))
        (by exact_mod_cast hβ1)
        (le_of_lt (lt_of_le_of_lt hlogβ hcase))
        (le_trans hlogβB (le_max_left _ _))
        (le_trans hlogB (le_max_left _ _))
        hPpos hPlow
      have hliou' : Real.log ‖lam φ α b‖
          ≥ -(∑ i : Fin n, ((b i).natAbs : ℝ) * Height.logHeight₁ (α i))
            - (d : ℝ) * Real.log 2 := by
        simpa only [lam] using hliou
      have hgoal : Real.log ‖lam φ α b‖
          ≥ -(BakerWustholz.C n d * max (Real.log (B : ℝ)) (1 / (d : ℝ))
              * ∏ i : Fin n, modifiedHeight φ (α i)) := by
        have h2 : (∑ i : Fin n, ((b i).natAbs : ℝ) * Height.logHeight₁ (α i)) + (d : ℝ) * Real.log 2
            ≤ BakerWustholz.C n d * max (Real.log (B : ℝ)) (1 / (d : ℝ))
              * ∏ i : Fin n, modifiedHeight φ (α i) := by linarith
        linarith
      exact hgoal
    · -- ============ MAIN CASE ============
      have hHle : hL b d ≤ max (Real.log (B : ℝ)) (1 / (d : ℝ)) := by
        simp only [hL]
        rw [← hβval]
        exact max_le_max hlogβB le_rfl
      have hMX : Xbw n d ≤ max (Real.log (B : ℝ)) (1 / (d : ℝ)) :=
        le_trans (not_lt.mp hcase) hHle
      obtain ⟨m, hm1, e, heinj, hdep_e, hind_e⟩ :=
        minimal_dependent (fun i => Complex.log (φ (α i))) hdep
      have hmn : m ≤ n := by simpa using Fintype.card_le_of_injective e heinj
      set βf : Fin m → K := fun j => α (e j) with hβf
      set ℓf : Fin m → ℂ := fun j => Complex.log (φ (βf j)) with hℓf
      have hβne : ∀ j, βf j ≠ 0 := fun j => hα (e j)
      have hℓexp : ∀ j, Complex.exp (ℓf j) = φ (βf j) := by
        intro j
        rw [hℓf, hβf]
        exact Complex.exp_log (hφα (e j))
      have hdepf : ¬ LinearIndependent ℚ ℓf := hdep_e
      have hminf : ∀ j : Fin m, LinearIndependent ℚ (fun i : {i : Fin m // i ≠ j} => ℓf i) :=
        hind_e
      obtain ⟨y, hyne, hyrel, hybd⟩ := small_relation φ βf hβne ℓf hℓexp hdepf hminf
      -- maximise the modified height
      obtain ⟨j0, -, hj0max⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin m))
        (fun j => hmod (βf j) (ℓf j)) ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
      set i0 : Fin n := e j0 with hi0
      -- the extended relation
      set Yext : Fin n → ℤ := fun i => ∑ j : Fin m, if e j = i then y j else 0 with hYext
      have hYe : ∀ j : Fin m, Yext (e j) = y j := by
        intro j
        show (∑ j' : Fin m, if e j' = e j then y j' else 0) = y j
        rw [Finset.sum_eq_single j]
        · simp
        · intro j' _ hj'
          simp only [if_neg (fun h => hj' (heinj h))]
        · intro hj
          exact absurd (Finset.mem_univ j) hj
      set Ymax : ℕ := Finset.univ.sup (fun j : Fin m => (y j).natAbs) with hYmax
      have hYmax_ge : ∀ j : Fin m, (y j).natAbs ≤ Ymax := fun j => by
        rw [hYmax]
        exact Finset.le_sup (f := fun j : Fin m => (y j).natAbs) (Finset.mem_univ j)
      have hYmax1 : 1 ≤ Ymax := le_trans (Int.natAbs_pos.mpr (hyne j0)) (hYmax_ge j0)
      have hYext_abs : ∀ i : Fin n, (Yext i).natAbs ≤ Ymax := by
        intro i
        by_cases h : ∃ j : Fin m, e j = i
        · obtain ⟨j, rfl⟩ := h
          rw [hYe j]
          exact hYmax_ge j
        · push_neg at h
          have h0 : Yext i = 0 := by
            rw [hYext]
            refine Finset.sum_eq_zero fun j _ => ?_
            simp [h j]
          rw [h0]
          simp
      have hYext_ne : Yext i0 ≠ 0 := by
        rw [hi0, hYe j0]
        exact hyne j0
      have hrel : (∑ i : Fin n, (Yext i : ℂ) * Complex.log (φ (α i))) = 0 := by
        rw [sum_extend e heinj y (fun i => Complex.log (φ (α i)))]
        simpa [hℓf, hβf] using hyrel
      have helim : (∑ i ∈ Finset.univ.erase i0,
            (((Yext i0 * b i - b i0 * Yext i : ℤ)) : ℂ) * Complex.log (φ (α i)))
          = (Yext i0 : ℂ) * lam φ α b := by
        have h1 : lam φ α b = ∑ i : Fin n, (b i : ℂ) * Complex.log (φ (α i)) := rfl
        rw [h1]
        exact elim_identity Yext b i0 (fun i => Complex.log (φ (α i))) hrel
      -- the complement and its reindexing
      set C' : Finset (Fin n) := Finset.univ.erase i0 with hC'
      have hC'card : C'.card = n - 1 := by
        rw [hC', Finset.card_erase_of_mem (Finset.mem_univ i0), Finset.card_univ,
          Fintype.card_fin]
      have hcard : Fintype.card {i : Fin n // i ∈ C'} = n - 1 := by
        rw [Fintype.card_coe, hC'card]
      set e' : Fin (n - 1) ≃ {i : Fin n // i ∈ C'} :=
        ((Fintype.equivFin {i : Fin n // i ∈ C'}).trans (finCongr hcard)).symm with he'
      set β2 : Fin (n - 1) → K := fun k => α (e' k).1 with hβ2
      set b2 : Fin (n - 1) → ℤ := fun k => Yext i0 * b (e' k).1 - b i0 * Yext (e' k).1 with hb2
      set B2 : ℕ := max 2 (2 * B * Ymax) with hB2
      have hβ2ne : ∀ k, β2 k ≠ 0 := fun k => hα _
      have hB22 : 2 ≤ B2 := by rw [hB2]; exact le_max_left _ _
      have hb2B : ∀ k, (b2 k).natAbs ≤ B2 := by
        intro k
        rw [hb2, hB2]
        refine le_trans ?_ (le_max_right 2 (2 * B * Ymax))
        have h4 : (Yext i0).natAbs ≤ Ymax := hYext_abs i0
        have h5 : (Yext (e' k).1).natAbs ≤ Ymax := hYext_abs _
        have h6 : (b (e' k).1).natAbs ≤ B := hbB _
        have h7 : (b i0).natAbs ≤ B := hbB _
        calc (Yext i0 * b (e' k).1 - b i0 * Yext (e' k).1).natAbs
            ≤ (Yext i0 * b (e' k).1).natAbs + (b i0 * Yext (e' k).1).natAbs :=
              Int.natAbs_sub_le _ _
          _ = (Yext i0).natAbs * (b (e' k).1).natAbs + (b i0).natAbs * (Yext (e' k).1).natAbs := by
              rw [Int.natAbs_mul, Int.natAbs_mul]
          _ ≤ Ymax * B + B * Ymax := add_le_add (Nat.mul_le_mul h4 h6) (Nat.mul_le_mul h7 h5)
          _ = 2 * B * Ymax := by ring
      have hlam2 : lam φ β2 b2 = (Yext i0 : ℂ) * lam φ α b := by
        have h1 : (∑ i ∈ Finset.univ.erase i0,
              (((Yext i0 * b i - b i0 * Yext i : ℤ)) : ℂ) * Complex.log (φ (α i)))
            = ∑ i ∈ C', (((Yext i0 * b i - b i0 * Yext i : ℤ)) : ℂ) * Complex.log (φ (α i)) := by
          rw [hC']
        calc lam φ β2 b2
            = ∑ k : Fin (n - 1), (b2 k : ℂ) * Complex.log (φ (β2 k)) := rfl
          _ = ∑ i : {i : Fin n // i ∈ C'},
                (((Yext i0 * b i.1 - b i0 * Yext i.1 : ℤ)) : ℂ) * Complex.log (φ (α i.1)) := by
              refine Fintype.sum_equiv e' _ _ fun k => ?_
              simp only [hβ2, hb2]
          _ = ∑ i ∈ C', (((Yext i0 * b i - b i0 * Yext i : ℤ)) : ℂ) * Complex.log (φ (α i)) := by
              conv_lhs => rw [← Finset.attach_eq_univ (s := C')]
              exact Finset.sum_attach C'
                (fun i : Fin n =>
                  (((Yext i0 * b i - b i0 * Yext i : ℤ)) : ℂ) * Complex.log (φ (α i)))
          _ = (Yext i0 : ℂ) * lam φ α b := by rw [← h1]; exact helim
      have hne2 : lam φ β2 b2 ≠ 0 := by
        rw [hlam2]
        exact mul_ne_zero (Int.cast_ne_zero.mpr hYext_ne) hΛ
      -- reindex the IH
      have hIH2 := IH (n - 1) (by omega) β2 hβ2ne b2 B2 hB22 hb2B hne2
      rw [← hd] at hIH2
      -- product bookkeeping
      have hP_eq : (∏ k : Fin (n - 1), modifiedHeight φ (β2 k))
          = ∏ i ∈ C', modifiedHeight φ (α i) := by
        have h1 : (∏ k : Fin (n - 1), modifiedHeight φ (β2 k))
            = ∏ i : {i : Fin n // i ∈ C'}, modifiedHeight φ (α i.1) := by
          refine Fintype.prod_equiv e' _ _ fun k => ?_
          simp only [hβ2]
        rw [h1]
        conv_lhs => rw [← Finset.attach_eq_univ (s := C')]
        exact Finset.prod_attach C' (fun i : Fin n => modifiedHeight φ (α i))
      have hprod_split : (∏ i : Fin n, modifiedHeight φ (α i))
          = modifiedHeight φ (α i0) * ∏ i ∈ C', modifiedHeight φ (α i) := by
        rw [hC']
        exact (Finset.mul_prod_erase Finset.univ (fun i => modifiedHeight φ (α i))
          (Finset.mem_univ i0)).symm
      have hmax' : ∀ j : Fin m, modifiedHeight φ (α (e j)) ≤ modifiedHeight φ (α (e j0)) :=
        fun j => by
          simpa only [modifiedHeight, hmod, hℓf, hβf] using hj0max j (Finset.mem_univ j)
      have hPDB := prod_drop_bounds (n := n) (m := m) (d := d) hm1 hd1
        (fun i => modifiedHeight φ (α i))
        (fun i => one_div_finrank_le_modifiedHeight φ _)
        e heinj j0 hmax'
      obtain ⟨hAlo, hAhi, hH0d, hPlow⟩ := hPDB
      -- the positivity and bound prerequisites for the arithmetic lemma
      have hA'pos : 0 < ∏ j : Fin m, modifiedHeight φ (βf j) :=
        Finset.prod_pos fun j _ =>
          lt_of_lt_of_le (one_div_pos.mpr hdpos) (one_div_finrank_le_modifiedHeight φ _)
      have hH0'pos : 0 < modifiedHeight φ (α i0) :=
        lt_of_lt_of_le (one_div_pos.mpr hdpos) (one_div_finrank_le_modifiedHeight φ _)
      have hP'pos : 0 < ∏ k : Fin (n - 1), modifiedHeight φ (β2 k) :=
        Finset.prod_pos fun k _ =>
          lt_of_lt_of_le (one_div_pos.mpr hdpos) (one_div_finrank_le_modifiedHeight φ _)
      have hYle1 : 1 ≤ (Ymax : ℝ) := by exact_mod_cast hYmax1
      obtain ⟨j1, -, hj1⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin m))
        (f := fun j => (y j).natAbs) ⟨j0, Finset.mem_univ j0⟩
      have hYbd : (Ymax : ℝ) ≤ (9 * (m : ℝ) * (d : ℝ) ^ 3) ^ m * ∏ j : Fin m,
          modifiedHeight φ (βf j) := by
        have h1 : (Ymax : ℝ) = ((y j1).natAbs : ℝ) := by
          rw [hYmax, hj1]
        rw [h1]
        rw [← hd] at hybd
        simpa only [modifiedHeight, hmod, hℓf] using hybd j1
      have hXY : Xbw n d ≤ max (Real.log (B : ℝ)) (1 / (d : ℝ)) := hMX
      have hM2 : Real.log 2 ≤ max (Real.log (B : ℝ)) (1 / (d : ℝ)) :=
        le_trans hlogB (le_max_left _ _)
      have hM'le : max (Real.log ((B2 : ℕ) : ℝ)) (1 / (d : ℝ))
          ≤ max (Real.log (B : ℝ)) (1 / (d : ℝ)) + Real.log 2 + Real.log (Ymax : ℝ) := by
        have hBY : 2 * B * Ymax = B2 := by
          rw [hB2]
          refine (max_eq_right ?_).symm
          have h1 : 1 ≤ B * Ymax :=
            Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
          calc 2 = 2 * 1 := (mul_one 2).symm
            _ ≤ 2 * (B * Ymax) := Nat.mul_le_mul_left 2 h1
            _ = 2 * B * Ymax := by ring
        have hlogB2 : Real.log ((B2 : ℕ) : ℝ)
            = Real.log 2 + Real.log (B : ℝ) + Real.log (Ymax : ℝ) := by
          have h3 : ((B2 : ℕ) : ℝ) = 2 * (B : ℝ) * (Ymax : ℝ) := by
            rw [← hBY]; push_cast; ring
          rw [h3, Real.log_mul (by positivity) (by positivity),
            Real.log_mul (by norm_num) (by positivity)]
        have h1 : Real.log ((B2 : ℕ) : ℝ)
            ≤ max (Real.log (B : ℝ)) (1 / (d : ℝ)) + Real.log 2 + Real.log (Ymax : ℝ) := by
          rw [hlogB2]
          linarith [le_max_left (Real.log (B : ℝ)) (1 / (d : ℝ))]
        have h2 : 1 / (d : ℝ)
            ≤ max (Real.log (B : ℝ)) (1 / (d : ℝ)) + Real.log 2 + Real.log (Ymax : ℝ) := by
          have h3 : (1 : ℝ) / (d : ℝ) ≤ max (Real.log (B : ℝ)) (1 / (d : ℝ)) :=
            le_max_right _ _
          have h4 : (0 : ℝ) ≤ Real.log 2 + Real.log (Ymax : ℝ) :=
            add_nonneg (le_of_lt (Real.log_pos (by norm_num)))
              (Real.log_nonneg (by exact_mod_cast hYmax1))
          linarith
        exact max_le h1 h2
      -- convert the product bounds to the vocabulary of `elim_arith`
      have hAlo' : 1 / (d : ℝ) ^ m ≤ ∏ j : Fin m, modifiedHeight φ (βf j) := by
        rw [one_div, ← inv_pow, ← one_div]
        exact hAlo
      have hAhi' : (∏ j : Fin m, modifiedHeight φ (βf j))
          ≤ (modifiedHeight φ (α i0)) ^ m := by
        rw [hi0]
        exact hAhi
      have hH0d' : 1 / (d : ℝ) ≤ modifiedHeight φ (α i0) := by
        rw [hi0]
        exact hH0d
      have hPlow' : (∏ j : Fin m, modifiedHeight φ (βf j)) / modifiedHeight φ (α i0)
            / (d : ℝ) ^ (n - m) ≤ ∏ k : Fin (n - 1), modifiedHeight φ (β2 k) := by
        rw [hP_eq, hC', hi0]
        exact hPlow
      have harith := elim_arith hn2 hm1 hmn hd1 hA'pos hH0'pos hP'pos hH0d' hAlo' hAhi' hPlow'
        hYle1 hYbd hXY hM2 hM'le
      -- conclude
      have hnorm : ‖lam φ β2 b2‖ = ((Yext i0).natAbs : ℝ) * ‖lam φ α b‖ := by
        rw [hlam2, Complex.norm_mul]
        congr 1
        rw [Complex.norm_intCast, ← Int.cast_abs, ← Int.natCast_natAbs]
        simp
      have hlog : Real.log ‖lam φ β2 b2‖
          = Real.log ((Yext i0).natAbs : ℝ) + Real.log ‖lam φ α b‖ := by
        rw [hnorm, Real.log_mul]
        · positivity
        · exact norm_ne_zero_iff.mpr hΛ
      have hYlog : Real.log ((Yext i0).natAbs : ℝ) ≤ Real.log (Ymax : ℝ) := by
        refine Real.log_le_log (by positivity) ?_
        exact_mod_cast hYext_abs i0
      have hIH3 : Real.log ‖lam φ β2 b2‖ ≥
          -(BakerWustholz.C (n - 1) d * max (Real.log ((B2 : ℕ) : ℝ)) (1 / (d : ℝ))
            * ∏ k : Fin (n - 1), modifiedHeight φ (β2 k)) := hIH2
      have hfin : Real.log ‖lam φ α b‖ ≥ -(BakerWustholz.C n d
          * max (Real.log (B : ℝ)) (1 / (d : ℝ)) * ∏ i : Fin n, modifiedHeight φ (α i)) := by
        have h1 : -(BakerWustholz.C (n - 1) d * max (Real.log ((B2 : ℕ) : ℝ)) (1 / (d : ℝ))
              * ∏ k : Fin (n - 1), modifiedHeight φ (β2 k)) - Real.log (Ymax : ℝ)
            ≥ -(BakerWustholz.C n d * max (Real.log (B : ℝ)) (1 / (d : ℝ))
              * (modifiedHeight φ (α i0)) * (∏ k : Fin (n - 1), modifiedHeight φ (β2 k))) := by
          linarith
        have h2 : BakerWustholz.C n d * max (Real.log (B : ℝ)) (1 / (d : ℝ))
              * (modifiedHeight φ (α i0)) * (∏ k : Fin (n - 1), modifiedHeight φ (β2 k))
            = BakerWustholz.C n d * max (Real.log (B : ℝ)) (1 / (d : ℝ))
              * ∏ i : Fin n, modifiedHeight φ (α i) := by
          rw [hprod_split, hP_eq]
          ring
        linarith [hlog, hYlog, hIH3]
      exact hfin
  · exfalso
    exact hΛ (hsmall (by omega))

end Work.BW
