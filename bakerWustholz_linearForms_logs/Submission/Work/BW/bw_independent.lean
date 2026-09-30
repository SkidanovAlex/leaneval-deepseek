import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.liouville_logForm
import Submission.Work.BW.lehmer_bound
import Submission.Work.BW.kummer_reduction
import Submission.Work.BW.aux_poly
import Submission.Work.BW.analytic_core
import Submission.Work.BW.group_reduction
import Submission.Work.BW.bw_smallH_case
import Submission.Work.BW.bw_drop_coordinate
import Submission.Work.BW.bw_rank_one_bound
import Submission.Work.BW.bw_arith_kappa
import Submission.Work.BW.bw_arith_rank1
import Submission.Work.BW.bw_arith_step51
import Submission.Work.BW.bw_iota_exists
import Submission.Work.BW.bw_arith_C_pred
import Submission.Work.BW.bw_arith_standing

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD NOTES (Baker–Wüstholz drive). Route design: BW = Baker–Wüstholz, Crelle 442 (1993); section and lemma numbers are BW's. Shared definitions are in Submission.Work.BW.Defs (namespace Work.BW).
Sibling nodes are dispatched in parallel, each as module Submission.Work.BW.<name> with its statement already in place: liouville_logForm, lehmer_bound, minkowski_basis, kummer_indep, logHeight_intermediate, discriminant_bound, siegel_numberField, small_relation, kummer_reduction, aux_poly, analytic_core, bw_independent, logindep_reduction. multiplicity_prop and group_reduction come later.
If your proof needs a sibling's result, IMPORT its module and use its statement. Do NOT reprove it, and do not restate it under another name. Its sorry disappears when it lands.
The constants are tight (see the notes below): do not weaken any numeric constant in your statement. If you believe the statement is false, give a concrete counterexample.

# bw_independent — BW §5 + §11 assembly (p. 25–26, 36); 2–4k lines, medium risk

**Claim.** `BWHolds φ α` when the principal logs are ℚ-independent, given `BWHolds` for fewer
logs.

**Steps.**
1. **Primitive form.** Let `g = gcd(b)` and `b = g b₀`, so `log|Λ| ≥ log|Λ₀|`. Put
   `H = hL b₀ d = h'(L)`; then `H ≤ max(log B, 1/d)`.
2. **§5 fallback: `H < X(n,d)`.** Use `liouville_logForm` with `y = b₀`:
   `log|Λ₀| ≥ -d(∑h' + log 2)·max|b₀|`.
   * `n·max h' + log 2 ≤ d^{n-1}(n+d)∏h'`, since each `h' ≥ 1/d`.
   * If `H ≤ 1`: `max|b₀| ≤ e ≤ e d H`, and `e·d^{n+1}(n+d) ≤ C(n,d)`.
   * If `1 ≤ H < X`: `max|b₀| = e^H < C/(d^n(n+d)) ≤ H·C/(d^n(n+d))`.
3. **Choose `k`.** Let `k` maximise `h'(α_k)`.
   * If `b₀ k = 0`, drop `α_k` and use `IH` at `n-1`. This uses `C(n-1,d)·d ≤ C(n,d)` and
     `h'(α_k) ≥ 1/d`.
   * `n = 1` is handled by step 2 or directly by Liouville: `d(dh' + d log 2)` against
     `C(1,d) h' /d`.
4. **Kummer reduction.** Apply `kummer_reduction` with `c' = 60d log 6d` (`lehmer_bound`).
   * Check `e ≤ c = c'^n n!`.
   * Check `log c < nH`: this follows from `H ≥ X` and
     `c'(n!)^{1/n}(n+d)d^n ≤ C(n,d)`.
5. **Minimal rank.** Take the least `r` with `BH` (`Nat.find`).
   * **`r = 1`** (BW p. 36): `qL = L₁`, `q ≤ 2^v dσ₁`, and Liouville on `α'₁` gives
     `log|Λ| ≥ -3d²σ₁`. Then use `3d²κ(1) ≤ C(n,d)`.
   * **`r ≥ 2`**: suppose the bound fails, so (8) `log|Λ₀| ≤ -κ'(r)∏σ·H`, since
     `κ'(r)κ(r) ≤ C(n,d)`.
     1. Derive (10) from `h ≤ (n+1)H max(2^v/c,1)`, using `v log2 ≤ log c·max(…)` and
        `log c < nH`.
     2. Choose `ι` (r-1 independent `∂*`).
     3. Chain `aux_poly`, `analytic_core`, `group_reduction` to get `BH` at `ρ < r`. This
        contradicts minimality.

**Arithmetic checks, done by hand.**
* `κ'(r)κ(r)/C(n,d) = (r/n)^{r+1}·log(2rd)/log(2nd) ≤ 1`, with equality at `r = n`.
* `3d²κ(1) ≪ C`.
* The Lehmer condition has at least 10⁸ room.
-/


open Complex

namespace Work.BW

/-! ## Elementary facts used by the assembly -/

private theorem bw_deg_pos {K : Type*} [Field K] [NumberField K] :
    (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by
  have h : 0 < Module.finrank ℚ K := Module.finrank_pos
  exact_mod_cast h

private theorem bw_deg_one {K : Type*} [Field K] [NumberField K] :
    1 ≤ Module.finrank ℚ K := by
  have h : 0 < Module.finrank ℚ K := Module.finrank_pos
  omega

private theorem bw_C_pos {n d : ℕ} (hn : 1 ≤ n) (hd : 1 ≤ d) : 0 < BakerWustholz.C n d := by
  have hnd : (1 : ℝ) < 2 * (n : ℝ) * (d : ℝ) := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h2 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    nlinarith
  unfold BakerWustholz.C
  have hlog : 0 < Real.log (2 * (n : ℝ) * (d : ℝ)) := Real.log_pos hnd
  have hfac : (0 : ℝ) <
      18 * ((n + 1).factorial : ℝ) * (n : ℝ) ^ (n + 1) * (32 * (d : ℝ)) ^ (n + 2) := by
    positivity
  exact mul_pos hfac hlog

private theorem bw_mh_pos {K : Type*} [Field K] [NumberField K] (φ : K →+* ℂ) (β : K) :
    0 < BakerWustholz.modifiedHeight φ β := by
  have hd : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := bw_deg_pos
  have h : (0 : ℝ) < 1 / (Module.finrank ℚ K : ℝ) := one_div_pos.mpr hd
  have h2 : 1 / (Module.finrank ℚ K : ℝ) ≤
      max (‖Complex.log (φ β)‖ / (Module.finrank ℚ K : ℝ)) (1 / (Module.finrank ℚ K : ℝ)) :=
    le_max_right _ _
  unfold BakerWustholz.modifiedHeight
  exact lt_of_lt_of_le h (le_trans h2 (le_max_right _ _))

private theorem bw_mh_ge_inv {K : Type*} [Field K] [NumberField K] (φ : K →+* ℂ) (β : K) :
    1 / (Module.finrank ℚ K : ℝ) ≤ BakerWustholz.modifiedHeight φ β := by
  have h2 : 1 / (Module.finrank ℚ K : ℝ) ≤
      max (‖Complex.log (φ β)‖ / (Module.finrank ℚ K : ℝ)) (1 / (Module.finrank ℚ K : ℝ)) :=
    le_max_right _ _
  unfold BakerWustholz.modifiedHeight
  exact le_trans h2 (le_max_right _ _)

private theorem bw_logHeight_le {K : Type*} [Field K] [NumberField K] (φ : K →+* ℂ) (β : K) :
    Height.logHeight₁ β ≤ (Module.finrank ℚ K : ℝ) * BakerWustholz.modifiedHeight φ β := by
  have hd : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := bw_deg_pos
  have h : Height.logHeight₁ β / (Module.finrank ℚ K : ℝ) ≤ BakerWustholz.modifiedHeight φ β := by
    unfold BakerWustholz.modifiedHeight
    exact le_max_left _ _
  calc Height.logHeight₁ β
      = (Height.logHeight₁ β / (Module.finrank ℚ K : ℝ)) * (Module.finrank ℚ K : ℝ) := by
        rw [div_mul_cancel₀ _ (ne_of_gt hd)]
    _ ≤ BakerWustholz.modifiedHeight φ β * (Module.finrank ℚ K : ℝ) :=
        mul_le_mul_of_nonneg_right h (le_of_lt hd)
    _ = (Module.finrank ℚ K : ℝ) * BakerWustholz.modifiedHeight φ β := by ring

private theorem bw_mh_prod_pos {K : Type*} [Field K] [NumberField K] (φ : K →+* ℂ)
    {n : ℕ} (α : Fin n → K) :
    0 < ∏ i, BakerWustholz.modifiedHeight φ (α i) :=
  Finset.prod_pos fun i _ => bw_mh_pos φ (α i)

private theorem bw_mh_prod_ge {K : Type*} [Field K] [NumberField K] (φ : K →+* ℂ)
    {n : ℕ} (α : Fin n → K) :
    (Module.finrank ℚ K : ℝ) ^ (-(n : ℤ)) ≤ ∏ i, BakerWustholz.modifiedHeight φ (α i) := by
  have h : (1 / (Module.finrank ℚ K : ℝ)) ^ n ≤ ∏ i, BakerWustholz.modifiedHeight φ (α i) := by
    calc (1 / (Module.finrank ℚ K : ℝ)) ^ n
        = ∏ _i : Fin n, (1 / (Module.finrank ℚ K : ℝ)) := by simp
      _ ≤ ∏ i, BakerWustholz.modifiedHeight φ (α i) := by
        simpa using (Finset.prod_le_prod₀ (s := (Finset.univ : Finset (Fin n)))
          (f := fun _ : Fin n => (1 / (Module.finrank ℚ K : ℝ)))
          (g := fun i : Fin n => BakerWustholz.modifiedHeight φ (α i))
          (fun i _ => by positivity) (fun i _ => bw_mh_ge_inv φ (α i)))
  have hz : (Module.finrank ℚ K : ℝ) ^ (-(n : ℤ)) = (1 / (Module.finrank ℚ K : ℝ)) ^ n := by
    rw [zpow_neg, zpow_natCast, one_div, inv_pow]
  rw [hz]; exact h

private theorem bw_hL_pos {n : ℕ} (b : Fin n → ℤ) (d : ℕ) (hd : 1 ≤ d) : 0 < hL b d := by
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have h : (0 : ℝ) < 1 / (d : ℝ) := one_div_pos.mpr hd'
  unfold hL
  exact lt_of_lt_of_le h (le_max_right _ _)

private theorem bw_hL_le {n : ℕ} (b : Fin n → ℤ) {B d : ℕ} (hB : 2 ≤ B)
    (hb : ∀ i, (b i).natAbs ≤ B) :
    hL b d ≤ max (Real.log B) (1 / (d : ℝ)) := by
  have hB1 : (1 : ℝ) < (B : ℝ) := by exact_mod_cast (by omega : 1 < B)
  have hlogB : 0 < Real.log (B : ℝ) := Real.log_pos hB1
  unfold hL
  apply max_le
  · rcases Nat.eq_zero_or_pos (Finset.univ.sup fun i => (b i).natAbs) with h0 | h0
    · have h0' : Real.log ((Finset.univ.sup fun i => (b i).natAbs : ℕ) : ℝ) = 0 := by
        rw [h0]; simp
      rw [h0']
      exact le_trans (le_of_lt hlogB) (le_max_left _ _)
    · have hsup : (Finset.univ.sup fun i => (b i).natAbs) ≤ B :=
        Finset.sup_le fun i _ => hb i
      have h1 : (0 : ℝ) < ((Finset.univ.sup fun i => (b i).natAbs : ℕ) : ℝ) := by
        exact_mod_cast h0
      have h3 : ((Finset.univ.sup fun i => (b i).natAbs : ℕ) : ℝ) ≤ (B : ℝ) := by
        exact_mod_cast hsup
      exact le_trans (Real.log_le_log h1 h3) (le_max_left _ _)
  · exact le_max_right _ _

private theorem bw_gcd_nonneg {ι : Type*} (s : Finset ι) (f : ι → ℤ) : 0 ≤ s.gcd f :=
  Int.nonneg_of_normalize_eq_self (Finset.normalize_gcd)

private theorem bw_kappa'_nonneg {n d r v : ℕ} {c : ℝ} (hd : 1 ≤ d) (hr : 1 ≤ r) :
    0 ≤ kappa' n d r v c := by
  unfold kappa'
  have hlog : (0 : ℝ) < Real.log (2 * (r : ℝ) * (d : ℝ)) := by
    apply Real.log_pos
    have h1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have h2 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    nlinarith
  have hmax : (0 : ℝ) ≤ max ((2 : ℝ) ^ v / c) 1 := le_trans zero_le_one (le_max_right _ _)
  have hrp : (0 : ℝ) ≤ (r : ℝ) ^ (r + 1) := by positivity
  have hdp : (0 : ℝ) ≤ (64 * (d : ℝ)) ^ (r + 2) := by positivity
  have hnp : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have h94 : (0 : ℝ) ≤ 9 / 4 := by norm_num
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h94 hnp) hrp) hdp)
    (le_of_lt hlog)) hmax

private theorem bw_c'_gt_one {K : Type*} [Field K] [NumberField K] :
    1 < 60 * (Module.finrank ℚ K : ℝ) * Real.log (6 * (Module.finrank ℚ K : ℝ)) := by
  have hd : (1 : ℝ) ≤ (Module.finrank ℚ K : ℝ) := by exact_mod_cast (bw_deg_one (K := K))
  have hlog6 : 1 < Real.log 6 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 6)]
    linarith [Real.exp_one_lt_three]
  have hle : Real.log 6 ≤ Real.log (6 * (Module.finrank ℚ K : ℝ)) :=
    Real.log_le_log (by norm_num) (by nlinarith)
  nlinarith

private theorem bw_c_gt_one {n : ℕ} (hn : 1 ≤ n) {c' : ℝ} (hc' : 1 < c') :
    1 < c' ^ n * (n.factorial : ℝ) := by
  have h1 : 1 < c' ^ n := one_lt_pow₀ hc' (Nat.one_le_iff_ne_zero.mp hn)
  have h2 : (1 : ℝ) ≤ (n.factorial : ℝ) := by
    have : 1 ≤ n.factorial := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero n)
    exact_mod_cast this
  have h3 : (1 : ℝ) < (c' ^ n) * (n.factorial : ℝ) := by
    have := mul_le_mul_of_nonneg_left h2 (le_of_lt (lt_trans zero_lt_one h1))
    linarith
  exact h3

private theorem bw_not_BH_zero {K : Type*} [Field K] [NumberField K] {n : ℕ} (φ : K →+* ℂ)
    (α : Fin n → K) (b : Fin n → ℤ) (hb_ne : b ≠ 0) (v : ℕ) (c : ℝ) (L : Fin 0 → Fin n → ℤ)
    (α' : Fin 0 → K) (σ : Fin 0 → ℝ) : ¬ BH φ α b v c 0 L α' σ := by
  intro h
  have hspan := h.2.1
  have hrange : (Set.range fun j : Fin 0 => fun i : Fin n => (((L j i : ℤ) : ℚ))) = ∅ := by
    rw [Set.range_eq_empty_iff]
    exact ⟨fun j => Fin.elim0 j⟩
  rw [hrange, Submodule.span_empty] at hspan
  have hb0 : (fun i => (b i : ℚ)) = 0 := by simpa using hspan
  apply hb_ne
  funext i
  have hi := congrFun hb0 i
  simp only [Pi.zero_apply] at hi
  exact_mod_cast hi

/-- Transport `BH` along an equality of ranks. -/
private theorem bw_BH_congr {K : Type*} [Field K] [NumberField K] {n r r' : ℕ} (φ : K →+* ℂ)
    (α : Fin n → K) (b : Fin n → ℤ) (v : ℕ) (c : ℝ) (h : r = r')
    (L : Fin r → Fin n → ℤ) (α' : Fin r → K) (σ : Fin r → ℝ)
    (hBH : BH φ α b v c r L α' σ) :
    BH φ α b v c r' (fun j i => L (Fin.cast h.symm j) i) (fun j => α' (Fin.cast h.symm j))
      (fun j => σ (Fin.cast h.symm j)) := by
  subst h
  simpa using hBH

/-- The heart of the assembly, for a **primitive** coefficient vector `b`. -/
private theorem bw_primitive_bound {K : Type*} [Field K] [NumberField K] {n : ℕ} (φ : K →+* ℂ)
    (α : Fin n → K) (hα : ∀ i, α i ≠ 0) (b : Fin n → ℤ) (hb : Finset.univ.gcd b = 1)
    (hind : LinearIndependent ℚ (fun i => Complex.log (φ (α i))))
    (IH : ∀ m < n, ∀ β : Fin m → K, (∀ i, β i ≠ 0) → BWHolds φ β)
    {B : ℕ} (hB : 2 ≤ B) (hbB : ∀ i, (b i).natAbs ≤ B) (hΛ : lam φ α b ≠ 0) :
    Real.log ‖lam φ α b‖ ≥
      -(BakerWustholz.C n (Module.finrank ℚ K) * max (Real.log B) (1 / (Module.finrank ℚ K : ℝ)) *
        ∏ i, BakerWustholz.modifiedHeight φ (α i)) := by
  classical
  by_cases hn0 : n = 0
  · subst hn0
    exact absurd (by simp [lam]) hΛ
  · have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    by_cases hH : hL b (Module.finrank ℚ K) < Xbw n (Module.finrank ℚ K)
    · exact bw_smallH_case φ α hα b hn hH hΛ hB hbB
    · have hHle : Xbw n (Module.finrank ℚ K) ≤ hL b (Module.finrank ℚ K) := not_lt.mp hH
      have hd := bw_deg_one (K := K)
      set c' : ℝ := 60 * (Module.finrank ℚ K : ℝ) * Real.log (6 * (Module.finrank ℚ K : ℝ))
        with hc'def
      have hc'1 : 1 < c' := by rw [hc'def]; exact bw_c'_gt_one
      have hLeh : ∀ (β : K) (ℓ : ℂ), β ≠ 0 → Complex.exp ℓ = φ β → ℓ ≠ 0 →
          1 < c' * max (Height.logHeight₁ β) ‖ℓ‖ := by
        intro β ℓ hβ hℓ hℓ0
        rw [hc'def]
        exact lehmer_bound φ β hβ ℓ hℓ hℓ0
      set c : ℝ := c' ^ n * (n.factorial : ℝ) with hcdef
      have hc1 : 1 < c := by rw [hcdef]; exact bw_c_gt_one hn hc'1
      have hcpos : 0 < c := lt_trans zero_lt_one hc1
      by_cases hn1 : n = 1
      · -- `n = 1`: the Kummer reduction lands at rank `1`, and the rank-one bound applies
        subst hn1
        obtain ⟨v, L, α', σ, hBH⟩ := kummer_reduction hn φ α hα hind c' hc'1 hLeh b
        exact bw_rank_one_bound φ α b hB hΛ v L α' σ c (by simpa using hc1) hBH
      · -- `2 ≤ n`
        have hn2 : 2 ≤ n := by omega
        have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
          ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
        obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ
          (fun i => BakerWustholz.modifiedHeight φ (α i)) hne
        have hb_ne : b ≠ 0 := by
          intro h0
          exact hΛ (by simp [lam, h0])
        by_cases hbk : b k = 0
        · exact bw_drop_coordinate φ α hα b k hbk hB hbB hΛ IH
        · -- the standing hypotheses
          have hstand_arith := bw_arith_standing n (Module.finrank ℚ K) (hL b (Module.finrank ℚ K))
            hn2 hd hHle
          have hst : Standing φ α b k c := by
            refine ⟨hn2, hα, hind, hb, hbk, fun j => hk j (Finset.mem_univ j), hHle, ?_, ?_⟩
            · rw [hcdef]; exact hstand_arith.1
            · rw [hcdef]; exact hstand_arith.2
          obtain ⟨v, L, α', σ, hBH⟩ := kummer_reduction hn φ α hα hind c' hc'1 hLeh b
          have hex : ∃ r : ℕ, ∃ (v : ℕ) (L : Fin r → Fin n → ℤ) (α' : Fin r → K) (σ : Fin r → ℝ),
              BH φ α b v c r L α' σ := ⟨n, v, L, α', σ, hBH⟩
          set r : ℕ := Nat.find hex with hrdef
          have hPr : ∃ (v : ℕ) (L : Fin r → Fin n → ℤ) (α' : Fin r → K) (σ : Fin r → ℝ),
              BH φ α b v c r L α' σ := Nat.find_spec hex
          by_cases hr1 : r = 1
          · -- `r = 1`
            obtain ⟨v1, L1, α1, σ1, hBH1⟩ := hPr
            exact bw_rank_one_bound φ α b hB hΛ v1 (fun j i => L1 (Fin.cast hr1.symm j) i)
              (fun j => α1 (Fin.cast hr1.symm j)) (fun j => σ1 (Fin.cast hr1.symm j)) c hc1
              (bw_BH_congr φ α b v1 c hr1 L1 α1 σ1 hBH1)
          · -- `r ≠ 1`; hence `2 ≤ r` and the analytic machinery applies
            have hr_ne0 : r ≠ 0 := by
              intro hr0
              obtain ⟨v1, L1, α1, σ1, hBH1⟩ := hPr
              exact bw_not_BH_zero φ α b hb_ne v1 c (fun j i => L1 (Fin.cast hr0.symm j) i)
                (fun j => α1 (Fin.cast hr0.symm j)) (fun j => σ1 (Fin.cast hr0.symm j))
                (bw_BH_congr φ α b v1 c hr0 L1 α1 σ1 hBH1)
            have hr2 : 2 ≤ r := by
              rcases r with _ | _ | r
              · exact absurd rfl hr_ne0
              · exact absurd rfl hr1
              · omega
            by_contra hgoal
            have hfail : Real.log ‖lam φ α b‖ <
                -(BakerWustholz.C n (Module.finrank ℚ K) *
                  max (Real.log B) (1 / (Module.finrank ℚ K : ℝ)) *
                    ∏ i, BakerWustholz.modifiedHeight φ (α i)) := not_le.mp hgoal
            obtain ⟨v1, L1, α1, σ1, hBH1⟩ := hPr
            have hBH1' := hBH1
            obtain ⟨hlin, hspan, hexp, hkum, hσpos, hσhmod, hσsum, hσprod⟩ := hBH1'
            have hst' := hst
            obtain ⟨hst_n, hst_a, hst_ind, hst_gcd, hst_bk, hst_max, hst_H, hst_c1, hst_c2⟩ := hst'
            have hCpos : 0 < BakerWustholz.C n (Module.finrank ℚ K) := bw_C_pos hn hd
            have hPhpos : 0 < ∏ i, BakerWustholz.modifiedHeight φ (α i) := bw_mh_prod_pos φ α
            have hHpos : 0 < hL b (Module.finrank ℚ K) := bw_hL_pos b _ hd
            have hHle' : hL b (Module.finrank ℚ K) ≤
                max (Real.log B) (1 / (Module.finrank ℚ K : ℝ)) := bw_hL_le b hB hbB
            have hrn : r ≤ n := Nat.find_min' hex ⟨v, L, α', σ, hBH⟩
            have hκκ' : kappa' n (Module.finrank ℚ K) r v1 c *
                kappa n (Module.finrank ℚ K) r v1 c ≤ BakerWustholz.C n (Module.finrank ℚ K) :=
              bw_arith_kappa n (Module.finrank ℚ K) r v1 c hn hd (by omega) hrn hcpos
            have hK'nn : 0 ≤ kappa' n (Module.finrank ℚ K) r v1 c :=
              bw_kappa'_nonneg hd (by omega)
            have hHnn : 0 ≤ hL b (Module.finrank ℚ K) := le_of_lt hHpos
            have hPhnn : 0 ≤ ∏ i, BakerWustholz.modifiedHeight φ (α i) := le_of_lt hPhpos
            have hkey : kappa' n (Module.finrank ℚ K) r v1 c * hL b (Module.finrank ℚ K) *
                (∏ j, σ1 j) ≤ BakerWustholz.C n (Module.finrank ℚ K) *
                  max (Real.log B) (1 / (Module.finrank ℚ K : ℝ)) *
                    (∏ i, BakerWustholz.modifiedHeight φ (α i)) := by
              have h1 : kappa' n (Module.finrank ℚ K) r v1 c * hL b (Module.finrank ℚ K) *
                    (∏ j, σ1 j) ≤ kappa' n (Module.finrank ℚ K) r v1 c *
                    hL b (Module.finrank ℚ K) *
                    (kappa n (Module.finrank ℚ K) r v1 c *
                      ∏ i, BakerWustholz.modifiedHeight φ (α i)) :=
                mul_le_mul_of_nonneg_left hσprod (mul_nonneg hK'nn hHnn)
              have h2 : kappa' n (Module.finrank ℚ K) r v1 c * hL b (Module.finrank ℚ K) *
                    (kappa n (Module.finrank ℚ K) r v1 c *
                      ∏ i, BakerWustholz.modifiedHeight φ (α i)) =
                  (kappa' n (Module.finrank ℚ K) r v1 c *
                    kappa n (Module.finrank ℚ K) r v1 c) *
                    (hL b (Module.finrank ℚ K) *
                      ∏ i, BakerWustholz.modifiedHeight φ (α i)) := by ring
              have h3 : (kappa' n (Module.finrank ℚ K) r v1 c *
                    kappa n (Module.finrank ℚ K) r v1 c) *
                    (hL b (Module.finrank ℚ K) *
                      ∏ i, BakerWustholz.modifiedHeight φ (α i)) ≤
                  BakerWustholz.C n (Module.finrank ℚ K) *
                    (hL b (Module.finrank ℚ K) *
                      ∏ i, BakerWustholz.modifiedHeight φ (α i)) :=
                mul_le_mul_of_nonneg_right hκκ' (mul_nonneg hHnn hPhnn)
              have h4 : BakerWustholz.C n (Module.finrank ℚ K) *
                    (hL b (Module.finrank ℚ K) *
                      ∏ i, BakerWustholz.modifiedHeight φ (α i)) ≤
                  BakerWustholz.C n (Module.finrank ℚ K) *
                    (max (Real.log B) (1 / (Module.finrank ℚ K : ℝ)) *
                      ∏ i, BakerWustholz.modifiedHeight φ (α i)) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right hHle' hPhnn) (le_of_lt hCpos)
              calc kappa' n (Module.finrank ℚ K) r v1 c * hL b (Module.finrank ℚ K) *
                    (∏ j, σ1 j)
                  ≤ kappa' n (Module.finrank ℚ K) r v1 c * hL b (Module.finrank ℚ K) *
                      (kappa n (Module.finrank ℚ K) r v1 c *
                        ∏ i, BakerWustholz.modifiedHeight φ (α i)) := h1
                _ = (kappa' n (Module.finrank ℚ K) r v1 c *
                      kappa n (Module.finrank ℚ K) r v1 c) *
                      (hL b (Module.finrank ℚ K) *
                        ∏ i, BakerWustholz.modifiedHeight φ (α i)) := h2
                _ ≤ BakerWustholz.C n (Module.finrank ℚ K) *
                      (hL b (Module.finrank ℚ K) *
                        ∏ i, BakerWustholz.modifiedHeight φ (α i)) := h3
                _ ≤ BakerWustholz.C n (Module.finrank ℚ K) *
                      (max (Real.log B) (1 / (Module.finrank ℚ K : ℝ)) *
                        ∏ i, BakerWustholz.modifiedHeight φ (α i)) := h4
                _ = BakerWustholz.C n (Module.finrank ℚ K) *
                      max (Real.log B) (1 / (Module.finrank ℚ K : ℝ)) *
                        (∏ i, BakerWustholz.modifiedHeight φ (α i)) := by ring
            have hstep := (bw_arith_step51 n (Module.finrank ℚ K) r v1 c
              (hL b (Module.finrank ℚ K)) σ1 hn hd (by omega) hHpos hst_c1 hst_c2 hσpos).2
            have h10 : Real.log ‖lam φ α b‖ ≤
                -(9 * 2 ^ r * (pS r (Module.finrank ℚ K) (ph (hL b (Module.finrank ℚ K)) v1) : ℝ) *
                  pD r (Module.finrank ℚ K) σ1) :=
              le_trans (le_of_lt hfail)
                (le_trans (neg_le_neg hkey) (neg_le_neg hstep))
            obtain ⟨ι, hι⟩ := bw_iota_exists φ α b k c hst hr2 v1 L1 α1 σ1 hBH1
            obtain ⟨p, hp0, hp9, hp12⟩ := aux_poly φ α b k c hst hr2 v1 L1 α1 σ1 hBH1 ι hι
            obtain ⟨P, hP⟩ := analytic_core φ α b k c hst hr2 v1 L1 α1 σ1 hBH1 ι hι p hp0 hp9 hp12 h10
            obtain ⟨ρ, hρ1, hρlt, L', α'', σ', hBH'⟩ :=
              group_reduction φ α b k c hst hr2 v1 L1 α1 σ1 hBH1 ι hι h10 P hP
            exact (Nat.find_min hex hρlt) ⟨v1, L', α'', σ', hBH'⟩

/-- BW §5 + §9 + §11 assembly: the bound for `ℚ`-independent principal logarithms, given the
bound for fewer logarithms (used when the coefficient of the largest-height `αₖ` is `0`). -/
theorem bw_independent {K : Type*} [Field K] [NumberField K] {n : ℕ} (φ : K →+* ℂ)
    (α : Fin n → K) (hα : ∀ i, α i ≠ 0)
    (hind : LinearIndependent ℚ (fun i => Complex.log (φ (α i))))
    (IH : ∀ m < n, ∀ β : Fin m → K, (∀ i, β i ≠ 0) → BWHolds φ β) :
    BWHolds φ α := by
  classical
  intro b B hB hbB hΛ
  have hb_ne : b ≠ 0 := by
    intro h0
    exact hΛ (by simp [lam, h0])
  set g : ℤ := Finset.univ.gcd b with hg
  have hg_ne : g ≠ 0 := by
    rw [hg]
    intro h0
    rw [Finset.gcd_eq_zero_iff] at h0
    exact hb_ne (funext fun i => h0 i (Finset.mem_univ i))
  set b0 : Fin n → ℤ := fun i => b i / g with hb0
  have hb_eq : ∀ i, b i = g * b0 i := by
    intro i
    have hdvd : g ∣ b i := by rw [hg]; exact Finset.gcd_dvd (Finset.mem_univ i)
    rw [hb0]
    exact (Int.mul_ediv_cancel' hdvd).symm
  have hb0_gcd : Finset.univ.gcd b0 = 1 := by
    have h1 : Finset.univ.gcd (fun i => g * b0 i) = g := by
      rw [show (fun i => g * b0 i) = b from funext fun i => (hb_eq i).symm, hg]
    have h2 : Finset.univ.gcd (fun i => g * b0 i) = normalize g * Finset.univ.gcd b0 :=
      Finset.gcd_mul_left
    rw [h1, Int.normalize_of_nonneg (bw_gcd_nonneg _ _)] at h2
    exact mul_left_cancel₀ hg_ne (h2.symm.trans (by ring))
  have hb0_bound : ∀ i, (b0 i).natAbs ≤ B := by
    intro i
    have hg1 : 1 ≤ g.natAbs := Int.natAbs_pos.mpr hg_ne
    have hmul : (b i).natAbs = g.natAbs * (b0 i).natAbs := by
      rw [hb_eq i, Int.natAbs_mul]
    calc (b0 i).natAbs ≤ g.natAbs * (b0 i).natAbs := by
          have := Nat.mul_le_mul_right ((b0 i).natAbs) hg1
          simpa using this
      _ = (b i).natAbs := hmul.symm
      _ ≤ B := hbB i
  have hprod : lam φ α b = (g : ℂ) * lam φ α b0 := by
    simp only [lam]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hb_eq i]
    push_cast
    ring
  have hnorm : ‖lam φ α b0‖ ≤ ‖lam φ α b‖ := by
    rw [hprod, norm_mul]
    have hg1 : (1 : ℝ) ≤ ‖(g : ℂ)‖ := by
      have hgc : ‖(g : ℂ)‖ = (g.natAbs : ℝ) := by
        rw [Complex.norm_intCast]; simp
      rw [hgc]
      exact_mod_cast Int.natAbs_pos.mpr hg_ne
    calc ‖lam φ α b0‖ = 1 * ‖lam φ α b0‖ := (one_mul _).symm
      _ ≤ ‖(g : ℂ)‖ * ‖lam φ α b0‖ := mul_le_mul_of_nonneg_right hg1 (norm_nonneg _)
  have hΛ0 : lam φ α b0 ≠ 0 := by
    intro h0
    apply hΛ
    rw [hprod, h0, mul_zero]
  have hmain := bw_primitive_bound φ α hα b0 hb0_gcd hind IH hB hb0_bound hΛ0
  exact le_trans hmain (Real.log_le_log (norm_pos_iff.mpr hΛ0) hnorm)

end Work.BW
