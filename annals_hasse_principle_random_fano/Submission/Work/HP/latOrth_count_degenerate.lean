import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.lam_basic
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.Lat.detLAux
import Submission.Work.HP.Sig2.schmidt_bound
import Submission.Work.HP.FM.minkowski_lower
import Submission.Work.HP.FM.veronese_lat

/-!
# The degenerate counting lemma for `Λ_c = {y : ⟨c,y⟩ = 0}`

This file proves `Work.HP.latOrth_count_degenerate`: the second half of the paper's Lemma `R0`
(Browning--Le Boudec--Sawin, *The Hasse principle for random Fano hypersurfaces*, Annals 197 (2023)),
specialised to the orthogonal lattice `Λ_c = latOrth c` of a primitive integer vector `c`.

For `1 ≤ T ≤ μ` with `λ_{k-1}(Λ_c) ≤ μ`, where `k = #ι`,

`#(Λ_c ∩ B(T)) ≤ K · ( T^{k-n} μ^{n-1} / ‖c‖ + T^{k-n-1} )`,

with `K` depending only on `ι` and `n`.

The pieces are

* the product form of Schmidt's bound, `Work.HP.Sig2.schmidt_bound`
  (`#(L ∩ B(T)) ≤ K ∏_{i<rk L}(T/λ_{i+1}(L) + 1)`),
* the easy half of Minkowski's second theorem, `Work.HP.FM.minkowski_lower`
  (`detL L ≤ ∏_{i<rk L} λ_{i+1}(L)`),
* the covolume identity `Work.HP.FM.detL_latOrth_of_prim` (`detL (latOrth c) = ‖c‖`),
* the rank formula `rk (latOrth c) = #ι - 1`, and
* the elementary product estimate `LCD_prod_lam_bound`, which expands the product over subsets and
  splits at `R₀ = min (n-1) (rk L)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Finset
open scoped BigOperators

namespace Work.HP

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Elementary product lemmas for `ℝ` -/

/-- A product of real numbers that are all at least `1` is at least `1`. -/
lemma LCD_one_le_prod_real {α : Type*} {s : Finset α} {f : α → ℝ} (h : ∀ i ∈ s, 1 ≤ f i) :
    1 ≤ ∏ i ∈ s, f i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have h1 : 1 ≤ f a := h a (Finset.mem_insert_self a s)
      have h2 : 1 ≤ ∏ i ∈ s, f i := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      have h4 := mul_le_mul h1 h2 (by norm_num : (0 : ℝ) ≤ 1)
        (le_trans (by norm_num : (0 : ℝ) ≤ 1) h1)
      simpa using h4

/-- Product monotonicity for real numbers, with the pointwise nonnegativity hypothesis. -/
lemma LCD_prod_le_prod_real {α : Type*} {s : Finset α} {f g : α → ℝ}
    (hf : ∀ i ∈ s, 0 ≤ f i) (h : ∀ i ∈ s, f i ≤ g i) : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have hfa : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
      have hfs : ∀ i ∈ s, 0 ≤ f i := fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have h1 : f a ≤ g a := h a (Finset.mem_insert_self a s)
      have h2 : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i :=
        ih hfs (fun i hi => h i (Finset.mem_insert_of_mem hi))
      have h3 : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg hfs
      exact mul_le_mul h1 h2 h3 (le_trans hfa h1)

/-! ## The elementary product estimate -/

/-- If `1 ≤ a i ≤ μ` for `1 ≤ i ≤ r` and `1 ≤ T ≤ μ`, then for every `R₀ ≤ r`

`∏_{i<r} (1 + T/a_{i+1}) ≤ 2^r ( T^{r-R₀} μ^{R₀} / ∏_{i<r} a_{i+1} + T^{r-R₀-1} )`.

Expand the product over subsets `S ⊆ {0,…,r-1}`: the term indexed by `S` is
`T^{|S|}/∏_{i∈S} a_{i+1}`.  Writing `j = r - |S|` for the size of the complement, the term equals
`T^{r-j}(∏_{i∉S} a_{i+1})/(∏_{i<r} a_{i+1})`; if `j ≤ R₀` it is at most
`T^{r-j}μ^j/(∏a) ≤ T^{r-R₀}μ^{R₀}/(∏a)`, and if `j > R₀` it is at most `T^{r-j} ≤ T^{r-R₀-1}`.
Summing the `2^r` terms gives the claim. -/
lemma LCD_prod_lam_bound {r R₀ : ℕ} (a : ℕ → ℝ) (μ T : ℝ) (hR₀ : R₀ ≤ r)
    (hT : 1 ≤ T) (hTμ : T ≤ μ)
    (h1 : ∀ i, 1 ≤ i → i ≤ r → 1 ≤ a i)
    (hμ : ∀ i, 1 ≤ i → i ≤ r → a i ≤ μ) :
    ∏ i ∈ Finset.range r, (T / a (i + 1) + 1) ≤
      (2 : ℝ) ^ r * (T ^ (r - R₀) * μ ^ R₀ / (∏ i ∈ Finset.range r, a (i + 1))
        + T ^ (r - R₀ - 1)) := by
  classical
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hμ0 : 0 < μ := lt_of_lt_of_le hT0 hTμ
  have hone : ∀ i ∈ Finset.range r, 1 ≤ a (i + 1) := fun i hi =>
    h1 (i + 1) (by omega) (by have := Finset.mem_range.mp hi; omega)
  have hle : ∀ i ∈ Finset.range r, a (i + 1) ≤ μ := fun i hi =>
    hμ (i + 1) (by omega) (by have := Finset.mem_range.mp hi; omega)
  set A : ℝ := ∏ i ∈ Finset.range r, a (i + 1) with hA
  have hApos : 0 < A := hA ▸ Finset.prod_pos (fun i hi => lt_of_lt_of_le zero_lt_one (hone i hi))
  -- the power comparison in the "main" case
  have hcrux : ∀ u : ℕ, u ≤ r → r - u ≤ R₀ → T ^ u * μ ^ (r - u) ≤ T ^ (r - R₀) * μ ^ R₀ := by
    intro u hu hru
    set e := u + R₀ - r with he
    have hsum : (r - R₀) + e = u := by omega
    have hsum2 : (r - u) + e = R₀ := by omega
    have hpow : T ^ e ≤ μ ^ e := pow_le_pow_left₀ hT0.le hTμ e
    have hTu : T ^ u = T ^ (r - R₀) * T ^ e := by rw [← pow_add, hsum]
    have hμR : μ ^ R₀ = μ ^ (r - u) * μ ^ e := by rw [← pow_add, hsum2]
    rw [hTu, hμR]
    calc T ^ (r - R₀) * T ^ e * μ ^ (r - u)
        = T ^ (r - R₀) * (T ^ e * μ ^ (r - u)) := by ring
      _ ≤ T ^ (r - R₀) * (μ ^ e * μ ^ (r - u)) := by
            refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hT0.le _)
            exact mul_le_mul_of_nonneg_right hpow (pow_nonneg hμ0.le _)
      _ = T ^ (r - R₀) * (μ ^ (r - u) * μ ^ e) := by ring
  -- expansion of the product over subsets
  have hexp : ∏ i ∈ Finset.range r, (T / a (i + 1) + 1)
      = ∑ t ∈ (Finset.range r).powerset, T ^ t.card / ∏ i ∈ t, a (i + 1) := by
    rw [Finset.prod_add]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.prod_const_one, mul_one]
  have hterm : ∀ t ∈ (Finset.range r).powerset,
      T ^ t.card / ∏ i ∈ t, a (i + 1) ≤
        T ^ (r - R₀) * μ ^ R₀ / A + T ^ (r - R₀ - 1) := by
    intro t ht
    have hts : t ⊆ Finset.range r := Finset.mem_powerset.mp ht
    have htr : t.card ≤ r := by
      have h := Finset.card_le_card hts
      simpa using h
    have hcard : (Finset.range r \ t).card = r - t.card := by
      rw [Finset.card_sdiff, Finset.card_range, Finset.inter_eq_left.mpr hts]
    have hDt1 : 1 ≤ ∏ i ∈ t, a (i + 1) := LCD_one_le_prod_real fun i hi => hone i (hts hi)
    have hDtpos : 0 < ∏ i ∈ t, a (i + 1) := lt_of_lt_of_le zero_lt_one hDt1
    have hDcpos : 0 < ∏ i ∈ Finset.range r \ t, a (i + 1) :=
      Finset.prod_pos fun i hi => lt_of_lt_of_le zero_lt_one (hone i (Finset.mem_sdiff.mp hi).1)
    have hDcnn : 0 ≤ ∏ i ∈ Finset.range r \ t, a (i + 1) := le_of_lt hDcpos
    have hDcA : (∏ i ∈ Finset.range r \ t, a (i + 1)) * (∏ i ∈ t, a (i + 1)) = A := by
      rw [hA]; exact Finset.prod_sdiff hts
    have hstep : T ^ t.card / (∏ i ∈ t, a (i + 1))
        = T ^ t.card * (∏ i ∈ Finset.range r \ t, a (i + 1)) / A := by
      rw [← hDcA]
      rw [div_eq_div_iff (ne_of_gt hDtpos) (ne_of_gt (mul_pos hDcpos hDtpos))]
      ring
    rw [hstep]
    by_cases hcase : r - t.card ≤ R₀
    · have hDC : ∏ i ∈ Finset.range r \ t, a (i + 1) ≤ μ ^ (r - t.card) := by
        rw [← hcard]
        calc ∏ i ∈ Finset.range r \ t, a (i + 1)
            ≤ ∏ _i ∈ Finset.range r \ t, μ :=
              LCD_prod_le_prod_real
                (fun i hi => le_trans zero_le_one (hone i (Finset.mem_sdiff.mp hi).1))
                (fun i hi => hle i (Finset.mem_sdiff.mp hi).1)
          _ = μ ^ (Finset.range r \ t).card := Finset.prod_const μ
      have hX : T ^ t.card * (∏ i ∈ Finset.range r \ t, a (i + 1)) ≤ T ^ (r - R₀) * μ ^ R₀ :=
        (mul_le_mul_of_nonneg_left hDC (pow_nonneg hT0.le _)).trans (hcrux t.card htr hcase)
      exact (div_le_div_of_nonneg_right hX hApos.le).trans
        (le_add_of_nonneg_right (pow_nonneg hT0.le _))
    · have hcase' : R₀ < r - t.card := not_le.mp hcase
      have hDcA' : ∏ i ∈ Finset.range r \ t, a (i + 1) ≤ A := by
        rw [← hDcA]
        exact le_mul_of_one_le_right hDcnn hDt1
      have htail : T ^ t.card * (∏ i ∈ Finset.range r \ t, a (i + 1)) / A ≤ T ^ t.card := by
        rw [div_le_iff₀ hApos]
        exact mul_le_mul_of_nonneg_left hDcA' (pow_nonneg hT0.le _)
      have h2 : T ^ t.card ≤ T ^ (r - R₀ - 1) := pow_le_pow_right₀ hT (by omega)
      exact (htail.trans h2).trans (le_add_of_nonneg_left (div_nonneg
        (mul_nonneg (pow_nonneg hT0.le _) (pow_nonneg hμ0.le _)) hApos.le))
  have hsum1 : ∑ t ∈ (Finset.range r).powerset, T ^ t.card / ∏ i ∈ t, a (i + 1)
      ≤ ∑ _t ∈ (Finset.range r).powerset,
          (T ^ (r - R₀) * μ ^ R₀ / A + T ^ (r - R₀ - 1)) := Finset.sum_le_sum hterm
  have hsum2 : ∑ _t ∈ (Finset.range r).powerset,
        (T ^ (r - R₀) * μ ^ R₀ / A + T ^ (r - R₀ - 1))
      = ((Finset.range r).powerset.card : ℝ) *
          (T ^ (r - R₀) * μ ^ R₀ / A + T ^ (r - R₀ - 1)) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hcard2 : ((Finset.range r).powerset.card : ℝ) = (2 : ℝ) ^ r := by
    rw [Finset.card_powerset, Finset.card_range]
    norm_num
  rw [hexp]
  refine hsum1.trans ?_
  rw [hsum2, hcard2]

/-! ## Two facts about `Λ_c` -/

/-- The successive minima of an integral lattice are at least `1`. -/
lemma LCD_one_le_lam (L : Submodule ℤ (ι → ℤ)) {j : ℕ} (hj : 1 ≤ j) (hjr : j ≤ rk L) :
    1 ≤ lam L j := by
  rw [lam_eq_sInf]
  refine le_csInf (lamSet_nonempty L hjr) ?_
  rintro r ⟨hr0, f, hfL, hfLI, hfr⟩
  have h0 : f ⟨0, hj⟩ ≠ 0 := hfLI.ne_zero ⟨0, hj⟩
  exact (one_le_eNorm h0).trans (hfr ⟨0, hj⟩)

/-- The orthogonal lattice `Λ_c` of a primitive vector `c` has rank `#ι - 1`. -/
lemma LCD_rk_latOrth (c : ι → ℤ) (hc : IsPrim c) : rk (latOrth c) = Fintype.card ι - 1 := by
  classical
  obtain ⟨u, hu⟩ := gcd_sum c
  have hc1 : Finset.univ.gcd c = 1 := hc
  rw [hc1] at hu
  have h1 : (1 : ℤ) ∈ (Fintype.linearCombination ℤ c).range :=
    ⟨u, by rw [Fintype.linearCombination_apply]; simpa [smul_eq_mul, mul_comm] using hu⟩
  have htop : (Fintype.linearCombination ℤ c).range = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    have hx : x = x • (1 : ℤ) := by simp
    rw [hx]
    exact Submodule.smul_mem _ _ h1
  have hq : Module.finrank ℤ ((ι → ℤ) ⧸ (Fintype.linearCombination ℤ c).ker) = 1 := by
    rw [LinearEquiv.finrank_eq (LinearMap.quotKerEquivRange (Fintype.linearCombination ℤ c)), htop]
    exact (LinearEquiv.finrank_eq Submodule.topEquiv).trans (Module.finrank_self ℤ)
  have hrn := Submodule.finrank_quotient_add_finrank (Fintype.linearCombination ℤ c).ker
  rw [hq, Module.finrank_pi] at hrn
  show Module.finrank ℤ (LinearMap.ker (Fintype.linearCombination ℤ c)) = Fintype.card ι - 1
  omega

/-! ## The exponent comparison -/

/-- The two exponent inequalities needed to match the Schmidt bound at `R₀ = min (n-1) (k-1)`
with the exponents of the paper's Lemma `R0`. -/
lemma LCD_exp_helper (n k : ℕ) (T μ : ℝ) (hT : 1 ≤ T) (hTμ : T ≤ μ) :
    T ^ (k - 1 - min (n - 1) (k - 1)) * μ ^ min (n - 1) (k - 1) ≤ T ^ (k - n) * μ ^ (n - 1) ∧
    T ^ (k - 1 - min (n - 1) (k - 1) - 1) ≤ T ^ (k - n - 1) := by
  have hμ1 : 1 ≤ μ := le_trans hT hTμ
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hm : min (n - 1) (0 - 1) = 0 := by simp
    rw [hm]
    constructor
    · simp only [Nat.zero_sub, Nat.sub_zero, pow_zero, mul_one, one_mul]
      exact one_le_pow₀ hμ1
    · simp
  · by_cases hn : n = 0
    · subst hn
      have hm : min (0 - 1) (k - 1) = 0 := by simp
      rw [hm]
      constructor
      · simp only [Nat.zero_sub, Nat.sub_zero, pow_zero, mul_one, one_mul]
        exact pow_le_pow_right₀ hT (by omega)
      · simp only [Nat.zero_sub, Nat.sub_zero, pow_zero, mul_one]
        exact pow_le_pow_right₀ hT (by omega)
    · have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn
      by_cases hnk : n ≤ k
      · have hm : min (n - 1) (k - 1) = n - 1 := by omega
        rw [hm]
        constructor
        · have he : k - 1 - (n - 1) = k - n := by omega
          rw [he]
        · have he : k - 1 - (n - 1) - 1 = k - n - 1 := by omega
          rw [he]
      · have hm : min (n - 1) (k - 1) = k - 1 := by omega
        rw [hm]
        constructor
        · have h1 : k - 1 - (k - 1) = 0 := by omega
          have h2 : k - n = 0 := by omega
          rw [h1, h2]
          simp only [pow_zero, mul_one, one_mul]
          exact pow_le_pow_right₀ hμ1 (by omega)
        · have h1 : k - 1 - (k - 1) - 1 = 0 := by omega
          have h2 : k - n - 1 = 0 := by omega
          rw [h1, h2]

/-! ## The degenerate counting lemma -/

theorem latOrth_count_degenerate (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (c : ι → ℤ), IsPrim c → ∀ μ T : ℝ, 1 ≤ T → T ≤ μ →
      lam (latOrth c) (Fintype.card ι - 1) ≤ μ →
      (ballCount (latOrth c) T : ℝ) ≤
        K * (T ^ (Fintype.card ι - n) * μ ^ (n - 1) / eNorm c
              + T ^ (Fintype.card ι - n - 1)) := by
  classical
  obtain ⟨K₁, hK₁pos, hsch⟩ := Sig2.schmidt_bound (ι := ι)
  refine ⟨K₁ * (2 : ℝ) ^ (Fintype.card ι) * 2, by positivity, ?_⟩
  intro c hc μ T hT hTμ hlam
  set k := Fintype.card ι with hk
  set L : Submodule ℤ (ι → ℤ) := latOrth c with hL
  have hc0 : c ≠ 0 := isPrim_ne_zero hc
  have hepos : 0 < eNorm c := eNorm_pos_of_ne_zero hc0
  have htnn : (0 : ℝ) ≤ T := le_trans zero_le_one hT
  have hmnn : (0 : ℝ) ≤ μ := le_trans htnn hTμ
  have hrk : rk L = k - 1 := by rw [hL]; exact LCD_rk_latOrth c hc
  have hlam' : lam L (rk L) ≤ μ := by rw [hrk]; exact hlam
  have hge1 : ∀ i, 1 ≤ i → i ≤ rk L → 1 ≤ lam L i := fun i hi hir => LCD_one_le_lam L hi hir
  have hleμ : ∀ i, 1 ≤ i → i ≤ rk L → lam L i ≤ μ := fun i hi hir =>
    (lam_mono L hir le_rfl).trans hlam'
  have hApos : 0 < ∏ i ∈ Finset.range (rk L), lam L (i + 1) :=
    Finset.prod_pos fun i hi => lam_pos L (by omega) (by have := Finset.mem_range.mp hi; omega)
  have hA : eNorm c ≤ ∏ i ∈ Finset.range (rk L), lam L (i + 1) := by
    rw [← FM.detL_latOrth_of_prim c hc, ← hL]
    exact FM.minkowski_lower L
  have hprod := LCD_prod_lam_bound (r := rk L) (R₀ := min (n - 1) (rk L)) (fun i => lam L i)
    μ T (min_le_right _ _) hT hTμ hge1 hleμ
  have hsc := hsch L T hT
  obtain ⟨hexp1, hexp2⟩ := LCD_exp_helper n k T μ hT hTμ
  have hexp1' : T ^ (rk L - min (n - 1) (rk L)) * μ ^ min (n - 1) (rk L)
      ≤ T ^ (k - n) * μ ^ (n - 1) := by rw [hrk]; exact hexp1
  have hexp2' : T ^ (rk L - min (n - 1) (rk L) - 1) ≤ T ^ (k - n - 1) := by rw [hrk]; exact hexp2
  have hnum2nn : (0 : ℝ) ≤ T ^ (k - n) * μ ^ (n - 1) :=
    mul_nonneg (pow_nonneg htnn _) (pow_nonneg hmnn _)
  have hterm1 : T ^ (rk L - min (n - 1) (rk L)) * μ ^ min (n - 1) (rk L) /
        (∏ i ∈ Finset.range (rk L), lam L (i + 1))
      ≤ T ^ (k - n) * μ ^ (n - 1) / eNorm c := by
    have h1 := div_le_div_of_nonneg_right hexp1' hApos.le
    have h2 : T ^ (k - n) * μ ^ (n - 1) / (∏ i ∈ Finset.range (rk L), lam L (i + 1))
        ≤ T ^ (k - n) * μ ^ (n - 1) / eNorm c := by
      have hinv : (∏ i ∈ Finset.range (rk L), lam L (i + 1))⁻¹ ≤ (eNorm c)⁻¹ := by
        simpa only [one_div] using one_div_le_one_div_of_le hepos hA
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hinv hnum2nn
    exact h1.trans h2
  have hsum : T ^ (rk L - min (n - 1) (rk L)) * μ ^ min (n - 1) (rk L) /
        (∏ i ∈ Finset.range (rk L), lam L (i + 1)) + T ^ (rk L - min (n - 1) (rk L) - 1)
      ≤ T ^ (k - n) * μ ^ (n - 1) / eNorm c + T ^ (k - n - 1) :=
    add_le_add hterm1 hexp2'
  have hy : (0 : ℝ) ≤ T ^ (k - n) * μ ^ (n - 1) / eNorm c + T ^ (k - n - 1) :=
    add_nonneg (div_nonneg (mul_nonneg (pow_nonneg htnn _) (pow_nonneg hmnn _)) hepos.le)
      (pow_nonneg htnn _)
  have h2r : (2 : ℝ) ^ (rk L) ≤ (2 : ℝ) ^ k := by
    rw [hrk]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hmid : (2 : ℝ) ^ (rk L) * (T ^ (rk L - min (n - 1) (rk L)) * μ ^ min (n - 1) (rk L) /
          (∏ i ∈ Finset.range (rk L), lam L (i + 1)) + T ^ (rk L - min (n - 1) (rk L) - 1))
      ≤ (2 : ℝ) ^ k * (T ^ (k - n) * μ ^ (n - 1) / eNorm c + T ^ (k - n - 1)) := by
    exact mul_le_mul h2r hsum
      (add_nonneg (div_nonneg (mul_nonneg (pow_nonneg htnn _) (pow_nonneg hmnn _)) hApos.le)
        (pow_nonneg htnn _)) (pow_nonneg (by norm_num) _)
  calc (ballCount L T : ℝ)
      ≤ K₁ * ∏ i ∈ Finset.range (rk L), (T / lam L (i + 1) + 1) := hsc
    _ ≤ K₁ * ((2 : ℝ) ^ (rk L) * (T ^ (rk L - min (n - 1) (rk L)) * μ ^ min (n - 1) (rk L) /
          (∏ i ∈ Finset.range (rk L), lam L (i + 1)) + T ^ (rk L - min (n - 1) (rk L) - 1))) :=
        mul_le_mul_of_nonneg_left hprod hK₁pos.le
    _ ≤ K₁ * ((2 : ℝ) ^ k * (T ^ (k - n) * μ ^ (n - 1) / eNorm c + T ^ (k - n - 1))) :=
        mul_le_mul_of_nonneg_left hmid hK₁pos.le
    _ ≤ K₁ * (2 : ℝ) ^ k * 2 * (T ^ (k - n) * μ ^ (n - 1) / eNorm c + T ^ (k - n - 1)) := by
        have h2nn : (2 : ℝ) ^ k * (T ^ (k - n) * μ ^ (n - 1) / eNorm c + T ^ (k - n - 1))
            ≤ (2 : ℝ) ^ k * (2 * (T ^ (k - n) * μ ^ (n - 1) / eNorm c + T ^ (k - n - 1))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          linarith
        calc K₁ * ((2 : ℝ) ^ k * (T ^ (k - n) * μ ^ (n - 1) / eNorm c + T ^ (k - n - 1)))
            ≤ K₁ * ((2 : ℝ) ^ k * (2 * (T ^ (k - n) * μ ^ (n - 1) / eNorm c
                + T ^ (k - n - 1)))) := mul_le_mul_of_nonneg_left h2nn hK₁pos.le
          _ = K₁ * (2 : ℝ) ^ k * 2 * (T ^ (k - n) * μ ^ (n - 1) / eNorm c + T ^ (k - n - 1)) := by
              ring

end Work.HP
