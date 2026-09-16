import Submission.ZagierHoffmanProof.ABPAssemble
import Submission.ZagierHoffmanProof.AmbRootLevel
import Submission.ZagierHoffmanProof.TmRoot

/-!
# The dual `t`-motive of Dac §4.2 (entrywise form)

Dac's dual `t`-motive attached to a tuple `s = (s_1,…,s_r)` of positive integers is the
`(r+1) × (r+1)` matrix `A` with

* `A_{t,t}  = (t - θ^q)^{w - w(t)}`  (the diagonal),
* `A_{t,t'} = Q_{last t}·(t - θ^q)^{w - w(t')}` for `t' = t.dropLast`,
* `A_{t,t'} = 0` otherwise,

where `w` is the weight (sum of the entries) and `w(t)` the weight of the tuple `t`.  Its rigid
analytic trivialisation is the matrix `Ψ` with

* `Ψ_{t,t'} = 𝓛(t \ t')·ω^{w-w(t)}` for `t'` a prefix of `t` (and `0` otherwise),

and the functional equation `Ψ = A Ψ^{(1)}` is equivalent to the "peel-the-last-factor" recursion
of the `L`-series.  This file proves the entrywise form of that functional equation, which is the
algebraic heart of Dac §4.2 / §5.1.

## Main results

* `tmWeight`, `tmWeight_append`, `tmWeight_dropLast`.
* `tmL`, `tmPsi`, `tmA`.
* `tmL_peel` — the recursion `𝓛(x,[y]) = ω^{y_1}y_2·𝓛(x)^{(1)} + 𝓛(x,[y])^{(1)}`.
* ★★★ `tmPsi_functional` — the entrywise functional equation `Ψ = A Ψ^{(1)}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Polynomial Matrix
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable {K : Type*} [Field K] [DecidableEq K] {Γ₀ : Type*}
  [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable [CompleteSpace K] [NonarchimedeanAddGroup K]

/-! ## §1. The weight of a tuple -/

/-- The weight of a tuple `t = [(s₁,Q₁),…]`: the sum of the `sᵢ`. -/
def tmWeight (t : List (ℕ × Polynomial K)) : ℕ := (t.map Prod.fst).sum

@[simp] lemma tmWeight_nil : tmWeight (K := K) [] = 0 := rfl

@[simp] lemma tmWeight_singleton (x : ℕ × Polynomial K) : tmWeight [x] = x.1 := by
  simp [tmWeight]

lemma tmWeight_append (t₁ t₂ : List (ℕ × Polynomial K)) :
    tmWeight (t₁ ++ t₂) = tmWeight t₁ + tmWeight t₂ := by
  simp [tmWeight]

lemma tmWeight_take_add_drop (t : List (ℕ × Polynomial K)) (k : ℕ) :
    tmWeight t = tmWeight (t.take k) + tmWeight (t.drop k) := by
  have h := List.sum_take_add_sum_drop (t.map Prod.fst) k
  simp [tmWeight, h]

lemma tmWeight_dropLast (t : List (ℕ × Polynomial K)) :
    tmWeight t.dropLast + (t.getLastD (0, 0)).1 = tmWeight t := by
  rcases List.eq_nil_or_concat t with h | ⟨u, x, h⟩
  · rw [h]; simp [tmWeight]
  · rw [h, List.concat_eq_append, List.dropLast_concat, List.getLastD_concat,
      tmWeight_append]
    simp

/-- Coercion of a tuple of polynomials to a tuple of power series. -/
noncomputable def tmCoe (t : List (ℕ × Polynomial K)) : List (ℕ × PowerSeries K) :=
  t.map fun x => (x.1, (x.2 : PowerSeries K))

@[simp] lemma tmCoe_nil : tmCoe (K := K) [] = [] := rfl

lemma tmCoe_append (t₁ t₂ : List (ℕ × Polynomial K)) :
    tmCoe (t₁ ++ t₂) = tmCoe t₁ ++ tmCoe t₂ := by
  simp [tmCoe]

/-- The `L`-series of a tuple. -/
noncomputable def tmL (q : ℕ) [FrobPow K q] (ω : PowerSeries K)
    (t : List (ℕ × Polynomial K)) : PowerSeries K :=
  atLrPaperGen q ω (tmCoe t)

@[simp] lemma tmL_nil (q : ℕ) [FrobPow K q] (ω : PowerSeries K) :
    tmL (K := K) q ω [] = 1 := by
  simp [tmL]

/-! ## §2. The entries of the trivialisation and of the dual `t`-motive -/

/-- `Ψ_{t,t'} = 𝓛(t \ t')·ω^{w-w(t)}` when `t'` is a prefix of `t`, and `0` otherwise. -/
noncomputable def tmPsi (q : ℕ) [FrobPow K q] (ω : PowerSeries K) (w : ℕ)
    (t t' : List (ℕ × Polynomial K)) : PowerSeries K :=
  if t.take t'.length = t' then tmL q ω (t.drop t'.length) * ω ^ (w - tmWeight t) else 0

/-- `A_{t,t} = (t-θ^q)^{w-w(t)}`, `A_{t,t'} = Q_{last t}·(t-θ^q)^{w-w(t')}` when `t' = t.dropLast`,
and `0` otherwise. -/
noncomputable def tmA (q : ℕ) (θ : K) (w : ℕ) (t t' : List (ℕ × Polynomial K)) : Polynomial K :=
  if t' = t then (X - C (θ ^ q)) ^ (w - tmWeight t)
  else if t' = t.dropLast then (t.getLastD (0, 0)).2 * (X - C (θ ^ q)) ^ (w - tmWeight t')
  else 0

lemma tmA_diag (q : ℕ) (θ : K) (w : ℕ) (t : List (ℕ × Polynomial K)) :
    tmA (K := K) q θ w t t = (X - C (θ ^ q)) ^ (w - tmWeight t) := by
  rw [tmA, if_pos rfl]

/-! ## §3. The functional equation of the `t`-motive -/

lemma frobTwist_zero_eq (q : ℕ) [FrobPow K q] (f : PowerSeries K) :
    frobTwist (R := K) (p := q) 0 f = f := by
  ext k
  rw [frobTwist_coeff, pow_zero, pow_one]

section functional

variable (q : ℕ) [FrobPow K q] (ω : PowerSeries K) (w : ℕ) {γ : Γ₀} {θ : K}

/-- **The "peel the last factor" recursion** of the `L`-series, in the form used for the
`t`-motive. -/
lemma tmL_peel (hγ : γ < 1) (harch : GammaArchimedean Γ₀) (hq : 2 ≤ q)
    (hω : GIsSmall γ ω) (L : List (ℕ × Polynomial K))
    (hL : ∀ x ∈ L, GIsSmall γ (ω ^ x.1 * (x.2 : PowerSeries K)))
    (s : ℕ) {Q : Polynomial K} (hF : GIsSmall γ (ω ^ s * (Q : PowerSeries K))) :
    tmL q ω (L ++ [(s, Q)])
      = (ω ^ s * (Q : PowerSeries K)) * frobTwist (R := K) (p := q) 1 (tmL q ω L)
        + frobTwist (R := K) (p := q) 1 (tmL q ω (L ++ [(s, Q)])) := by
  have hL' : ∀ x ∈ tmCoe L, GIsSmall γ (ω ^ x.1 * x.2) := by
    intro x hx
    rw [tmCoe, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hL y hy
  have hL'' : ∀ x ∈ tmCoe L ++ [(s, (Q : PowerSeries K))],
      GIsSmall γ (ω ^ x.1 * x.2) := by
    intro x hx
    rw [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hL' x hx
    · exact hF
  have hfold := atLrPaperGen_fold hγ harch q ω hq hω (tmCoe L) hL' s hF 0 1
  rw [Finset.sum_range_one] at hfold
  simp only [zero_add, frobTwist_zero_eq q] at hfold
  rw [← frobTwist_atLrcutPaperGen hγ harch q ω hq hω (tmCoe L) hL' 0 1,
    ← frobTwist_atLrcutPaperGen hγ harch q ω hq hω (tmCoe L ++ [(s, (Q : PowerSeries K))])
      hL'' 0 1] at hfold
  have hmap : tmCoe (L ++ [(s, Q)]) = tmCoe L ++ [(s, (Q : PowerSeries K))] := by
    simp [tmCoe]
  simp only [tmL]
  rw [hmap]
  exact hfold

lemma tmPsi_prefix {t t' : List (ℕ × Polynomial K)} (h : t.take t'.length = t') :
    tmPsi q ω w t t' = tmL q ω (t.drop t'.length) * ω ^ (w - tmWeight t) :=
  if_pos h

lemma tmPsi_not_prefix {t t' : List (ℕ × Polynomial K)} (h : ¬ t.take t'.length = t') :
    tmPsi q ω w t t' = 0 := if_neg h

lemma tmWeight_concat (u : List (ℕ × Polynomial K)) (x : ℕ × Polynomial K) :
    tmWeight (u ++ [x]) = tmWeight u + x.1 := by
  rw [tmWeight_append, tmWeight_singleton]

lemma tmA_subdiag_of_concat (θ : K) (u : List (ℕ × Polynomial K)) (x : ℕ × Polynomial K)
    {t' : List (ℕ × Polynomial K)} (h : t' = (u ++ [x]).dropLast) :
    tmA q θ w (u ++ [x]) t' = x.2 * (X - C (θ ^ q)) ^ (w - tmWeight t') := by
  subst h
  rw [tmA, List.dropLast_concat, if_neg (by simp), if_pos rfl, List.getLastD_concat]

lemma tmA_diag_concat (θ : K) (u : List (ℕ × Polynomial K)) (x : ℕ × Polynomial K) :
    tmA q θ w (u ++ [x]) (u ++ [x]) = (X - C (θ ^ q)) ^ (w - tmWeight (u ++ [x])) :=
  tmA_diag q θ w _

/-- **The functional equation of the `t`-motive**: the first column `ψ` of the rigid analytic
trivialisation satisfies `ψ = A ψ^{(1)}`, where `A` is the dual `t`-motive of Dac §4.2. -/
theorem tmPsi_functional (hγ : γ < 1) (harch : GammaArchimedean Γ₀) (hq : 2 ≤ q)
    (hω : GIsSmall γ ω)
    (hωfe : (PowerSeries.X - PowerSeries.C (θ ^ q)) * frobTwist (R := K) (p := q) 1 ω = ω)
    {t : List (ℕ × Polynomial K)}
    (hsm : ∀ y ∈ t, GIsSmall γ (ω ^ y.1 * (y.2 : PowerSeries K)))
    (hwt : tmWeight t ≤ w) (t' : List (ℕ × Polynomial K)) :
    tmPsi q ω w t t'
      = ((tmA q θ w t t : Polynomial K) : PowerSeries K)
          * frobTwist (R := K) (p := q) 1 (tmPsi q ω w t t')
        + (if t = [] then 0 else ((tmA q θ w t t.dropLast : Polynomial K) : PowerSeries K)
            * frobTwist (R := K) (p := q) 1 (tmPsi q ω w t.dropLast t')) := by
  have hΩpow : ∀ n : ℕ,
      (PowerSeries.X - PowerSeries.C (θ ^ q)) ^ n * (frobTwist (R := K) (p := q) 1 ω) ^ n
        = ω ^ n := by
    intro n
    rw [← mul_pow, hωfe]
  rcases List.eq_nil_or_concat t with h0 | ⟨u, x, h0⟩
  · subst h0
    by_cases h' : t' = []
    · subst h'
      rw [tmPsi_prefix q ω w (t := []) (t' := []) (by simp), tmA_diag]
      simp only [tmWeight_nil, Nat.sub_zero, tmL_nil, one_mul, List.length_nil,
        List.drop_zero, Polynomial.coe_pow, Polynomial.coe_sub, Polynomial.coe_X,
        Polynomial.coe_C, frobTwist_pow]
      rw [if_true, add_zero, ← mul_pow, hωfe]
    · rw [tmPsi_not_prefix q ω w (t := []) (t' := t') (by simpa using h')]
      simp
  · have hEq : t = u ++ [x] := by rw [h0, List.concat_eq_append]
    subst hEq
    by_cases hC : (u ++ [x]).take t'.length = t'
    · by_cases ht' : t' = u ++ [x]
      · subst ht'
        rw [tmPsi_prefix q ω w (t := u ++ [x]) (t' := u ++ [x]) (by simp)]
        rw [tmA_diag_concat (q := q) (w := w) (θ := θ) (u := u) (x := x)]
        rw [if_neg (by simp), List.dropLast_concat]
        have hz : ¬ (u.take (u ++ [x]).length = (u ++ [x])) := by
          intro hh
          have h1 := congrArg List.length hh
          rw [List.length_take, min_eq_right (by simp)] at h1
          rw [List.length_append, List.length_singleton] at h1
          omega
        rw [tmPsi_not_prefix q ω w (t := u) (t' := u ++ [x]) hz, frobTwist_zero, mul_zero,
          add_zero]
        rw [tmWeight_concat, Polynomial.coe_pow, Polynomial.coe_sub, Polynomial.coe_X,
          Polynomial.coe_C]
        simp only [List.drop_length, tmL_nil, one_mul, frobTwist_pow]
        rw [← mul_pow, hωfe]
      · have hlen : t'.length < (u ++ [x]).length := by
          have h1 : t'.length ≤ (u ++ [x]).length := by
            have h2 := congrArg List.length hC
            rw [List.length_take] at h2
            calc t'.length = min t'.length (u ++ [x]).length := h2.symm
              _ ≤ (u ++ [x]).length := min_le_right _ _
          rcases lt_or_eq_of_le h1 with h3 | h3
          · exact h3
          · exact absurd (by rw [← hC, h3, List.take_length]) ht'
        have hle : t'.length ≤ u.length := by
          rw [List.length_append, List.length_singleton] at hlen
          omega
        have hCu : u.take t'.length = t' := by
          have h1 : (u ++ [x]).take t'.length = u.take t'.length :=
            List.take_append_of_le_length hle
          rw [h1] at hC
          exact hC
        have hdrop : (u ++ [x]).drop t'.length = u.drop t'.length ++ [x] :=
          List.drop_append_of_le_length hle
        rw [tmPsi_prefix q ω w (t := u ++ [x]) (t' := t') hC]
        rw [List.dropLast_concat]
        rw [tmPsi_prefix q ω w (t := u) (t' := t') hCu]
        rw [tmA_subdiag_of_concat (q := q) (θ := θ) (w := w) (u := u) (x := x)
            List.dropLast_concat.symm,
          tmA_diag_concat (q := q) (w := w) (θ := θ) (u := u) (x := x)]
        rw [hdrop]
        obtain ⟨hu_mem, hx_mem⟩ : (∀ y ∈ u.drop t'.length,
              GIsSmall γ (ω ^ y.1 * (y.2 : PowerSeries K)))
            ∧ GIsSmall γ (ω ^ x.1 * (x.2 : PowerSeries K)) := by
          have hx : x ∈ u ++ [x] := by simp
          refine ⟨fun y hy => ?_, hsm x hx⟩
          exact hsm y (List.mem_append_left _ (List.mem_of_mem_drop hy))
        have hp := tmL_peel q ω hγ harch hq hω (u.drop t'.length) hu_mem x.1
          (Q := x.2) hx_mem
        conv_lhs => rw [hp]
        rw [if_neg (by simp)]
        rw [frobTwist_mul, frobTwist_mul, frobTwist_pow, frobTwist_pow]
        have hσ : w - tmWeight u = w - tmWeight (u ++ [x]) + x.1 := by
          rw [tmWeight_concat] at hwt ⊢
          omega
        rw [hσ, pow_add]
        push_cast
        rw [← hΩpow (w - tmWeight (u ++ [x])), ← hΩpow x.1]
        ring
    · rw [tmPsi_not_prefix q ω w (t := u ++ [x]) (t' := t') hC]
      rw [if_neg (by simp), List.dropLast_concat]
      have h2 : ¬ (u.take t'.length = t') := by
        intro hh
        apply hC
        have hlen : t'.length ≤ u.length := by
          rw [← hh, List.length_take]
          exact min_le_right _ _
        rw [List.take_append_of_le_length hlen, hh]
      rw [tmPsi_not_prefix q ω w (t := u) (t' := t') h2]
      simp

end functional


/-! ## §4. The index set of the merged `t`-motive -/

/-- Dac's index set `I = ⋃_{s ∈ S} {s.take k : 0 ≤ k < s.length}`: the proper prefixes. -/
noncomputable def tmI (S : Finset (List (ℕ × Polynomial K))) :
    Finset (List (ℕ × Polynomial K)) :=
  S.biUnion fun s => (Finset.range s.length).image fun k => s.take k

lemma mem_tmI {S : Finset (List (ℕ × Polynomial K))} {t : List (ℕ × Polynomial K)} :
    t ∈ tmI S ↔ ∃ s ∈ S, ∃ k < s.length, s.take k = t := by
  rw [tmI, Finset.mem_biUnion]
  constructor
  · rintro ⟨s, hs, h⟩
    rw [Finset.mem_image] at h
    obtain ⟨k, hk, hkT⟩ := h
    exact ⟨s, hs, k, Finset.mem_range.mp hk, hkT⟩
  · rintro ⟨s, hs, k, hk, hkT⟩
    exact ⟨s, hs, Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, hkT⟩⟩

/-- Dropping the last element of a prefix drops one from the length. -/
lemma dropLast_take_eq {α : Type*} (s : List α) {k : ℕ} (hk : k ≤ s.length) :
    (s.take k).dropLast = s.take (k - 1) := by
  rw [List.dropLast_eq_take, List.take_take]
  congr 1
  rw [List.length_take, min_eq_left hk]
  exact min_eq_left (by omega)

lemma dropLast_mem_tmI {S : Finset (List (ℕ × Polynomial K))} {t : List (ℕ × Polynomial K)}
    (ht : t ∈ tmI S) : t.dropLast ∈ tmI S := by
  obtain ⟨s, hs, k, hk, rfl⟩ := mem_tmI.mp ht
  refine mem_tmI.mpr ⟨s, hs, k - 1, ?_, ?_⟩
  · omega
  · exact (dropLast_take_eq (k := k) s (by omega)).symm



/-! ## §5. The merged matrices -/

section matrix

/-- Dac's `f_t`: the `a_i`-weighted sum of the `L`-series of the suffixes `s_i \ t`. -/
noncomputable def tmF (q : ℕ) [FrobPow K q] (ω : PowerSeries K) (_w : ℕ)
    (S : Finset (List (ℕ × Polynomial K))) (cf : List (ℕ × Polynomial K) → Polynomial K)
    (t : List (ℕ × Polynomial K)) : PowerSeries K :=
  ∑ s ∈ S, if s.take t.length = t then (cf s : PowerSeries K) * tmL q ω (s.drop t.length) else 0

/-- The last entry of a tuple. -/
noncomputable def tmQ (s : List (ℕ × Polynomial K)) : Polynomial K := (s.getLastD (0, 0)).2

/-- The `Q`-part of the `v`-row of the merged dual `t`-motive. -/
noncomputable def tmV (q : ℕ) (θ : K) (w : ℕ)
    (S : Finset (List (ℕ × Polynomial K))) (cf : List (ℕ × Polynomial K) → Polynomial K)
    (t : List (ℕ × Polynomial K)) : Polynomial K :=
  ∑ s ∈ S, if s.dropLast = t then cf s * tmQ s * (X - C (θ ^ q)) ^ (w - tmWeight t) else 0

/-- The rigid analytic trivialisation `Ψ` of the merged dual `t`-motive. -/
noncomputable def tmPsiOpt (q : ℕ) [FrobPow K q] (ω : PowerSeries K) (w : ℕ)
    (S : Finset (List (ℕ × Polynomial K))) (cf : List (ℕ × Polynomial K) → Polynomial K) :
    Matrix (Option ↥(tmI S)) (Option ↥(tmI S)) (PowerSeries K) :=
  fun i j => match i, j with
    | some t, some t' => tmPsi q ω w t.1 t'.1
    | some _, none => 0
    | none, some t' => tmF q ω w S cf t'.1
    | none, none => 1

/-- The merged dual `t`-motive `A` (Dac's `Φ`, in the positive-twist normalisation). -/
noncomputable def tmAOpt (q : ℕ) (θ : K) (w : ℕ)
    (S : Finset (List (ℕ × Polynomial K))) (cf : List (ℕ × Polynomial K) → Polynomial K) :
    Matrix (Option ↥(tmI S)) (Option ↥(tmI S)) (Polynomial K) :=
  fun i j => match i, j with
    | some t, some t' => tmA q θ w t.1 t'.1
    | some _, none => 0
    | none, some t' => tmV q θ w S cf t'.1
    | none, none => 1

@[simp] lemma tmPsiOpt_some_some (q : ℕ) [FrobPow K q] (ω : PowerSeries K) (w : ℕ)
    (S : Finset (List (ℕ × Polynomial K))) (cf : List (ℕ × Polynomial K) → Polynomial K)
    (t t' : ↥(tmI S)) : tmPsiOpt q ω w S cf (some t) (some t') = tmPsi q ω w t.1 t'.1 := rfl

@[simp] lemma tmPsiOpt_some_none (q : ℕ) [FrobPow K q] (ω : PowerSeries K) (w : ℕ)
    (S : Finset (List (ℕ × Polynomial K))) (cf : List (ℕ × Polynomial K) → Polynomial K)
    (t : ↥(tmI S)) : tmPsiOpt q ω w S cf (some t) none = 0 := rfl

@[simp] lemma tmPsiOpt_none_some (q : ℕ) [FrobPow K q] (ω : PowerSeries K) (w : ℕ)
    (S : Finset (List (ℕ × Polynomial K))) (cf : List (ℕ × Polynomial K) → Polynomial K)
    (t : ↥(tmI S)) : tmPsiOpt q ω w S cf none (some t) = tmF q ω w S cf t.1 := rfl

@[simp] lemma tmPsiOpt_none_none (q : ℕ) [FrobPow K q] (ω : PowerSeries K) (w : ℕ)
    (S : Finset (List (ℕ × Polynomial K))) (cf : List (ℕ × Polynomial K) → Polynomial K) :
    tmPsiOpt q ω w S cf none none = 1 := rfl

@[simp] lemma tmAOpt_some_some (q : ℕ) (θ : K) (w : ℕ)
    (S : Finset (List (ℕ × Polynomial K))) (cf : List (ℕ × Polynomial K) → Polynomial K)
    (t t' : ↥(tmI S)) : tmAOpt q θ w S cf (some t) (some t') = tmA q θ w t.1 t'.1 := rfl

@[simp] lemma tmAOpt_some_none (q : ℕ) (θ : K) (w : ℕ)
    (S : Finset (List (ℕ × Polynomial K))) (cf : List (ℕ × Polynomial K) → Polynomial K)
    (t : ↥(tmI S)) : tmAOpt q θ w S cf (some t) none = 0 := rfl

@[simp] lemma tmAOpt_none_some (q : ℕ) (θ : K) (w : ℕ)
    (S : Finset (List (ℕ × Polynomial K))) (cf : List (ℕ × Polynomial K) → Polynomial K)
    (t : ↥(tmI S)) : tmAOpt q θ w S cf none (some t) = tmV q θ w S cf t.1 := rfl

@[simp] lemma tmAOpt_none_none (q : ℕ) (θ : K) (w : ℕ)
    (S : Finset (List (ℕ × Polynomial K))) (cf : List (ℕ × Polynomial K) → Polynomial K) :
    tmAOpt q θ w S cf none none = 1 := rfl

lemma tmA_eq_zero_of_ne {q : ℕ} (θ : K) (w : ℕ) {t t' : List (ℕ × Polynomial K)}
    (h1 : t' ≠ t) (h2 : t' ≠ t.dropLast) : tmA q θ w t t' = 0 := by
  rw [tmA, if_neg h1, if_neg h2]

lemma eq_nil_of_dropLast_eq_self {t : List (ℕ × Polynomial K)} (h : t.dropLast = t) : t = [] := by
  by_contra ht
  have h1 : t.length = t.dropLast.length := by rw [h]
  rw [List.length_dropLast] at h1
  have h2 : 0 < t.length := List.length_pos_iff.mpr ht
  omega



/-! ## §6. The functional equation of the merged `t`-motive -/

section functionalMatrix

variable (S : Finset (List (ℕ × Polynomial K)))
variable (cf : List (ℕ × Polynomial K) → Polynomial K)

/-- **The sum reduction over the `(some,some)` block.** -/
lemma sum_tmAOpt_eq (q : ℕ) [FrobPow K q] (θ : K) (w : ℕ) {ω : PowerSeries K}
    (t t' : ↥(tmI S)) :
    (∑ t'' : ↥(tmI S), ((tmA q θ w t.1 t''.1 : Polynomial K) : PowerSeries K)
        * frobTwist (R := K) (p := q) 1 (tmPsi q ω w t''.1 t'.1))
      = ((tmA q θ w t.1 t.1 : Polynomial K) : PowerSeries K)
          * frobTwist (R := K) (p := q) 1 (tmPsi q ω w t.1 t'.1)
        + (if t.1 = [] then 0
            else ((tmA q θ w t.1 t.1.dropLast : Polynomial K) : PowerSeries K)
              * frobTwist (R := K) (p := q) 1 (tmPsi q ω w t.1.dropLast t'.1)) := by
  have hmem : t.1.dropLast ∈ tmI S := dropLast_mem_tmI t.2
  have hzero : ∀ x : ↥(tmI S), x ≠ (⟨t.1, t.2⟩ : ↥(tmI S)) →
      x ≠ (⟨t.1.dropLast, hmem⟩ : ↥(tmI S)) →
      ((tmA q θ w t.1 x.1 : Polynomial K) : PowerSeries K)
        * frobTwist (R := K) (p := q) 1 (tmPsi q ω w x.1 t'.1) = 0 := by
    intro x hx1 hx2
    have h1 : x.1 ≠ t.1 := fun h => hx1 (Subtype.ext h)
    have h2 : x.1 ≠ t.1.dropLast := fun h => hx2 (Subtype.ext h)
    rw [tmA_eq_zero_of_ne θ w h1 h2, Polynomial.coe_zero, zero_mul]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (⟨t.1, t.2⟩ : ↥(tmI S)))]
  by_cases hAB : (⟨t.1, t.2⟩ : ↥(tmI S)) = ⟨t.1.dropLast, hmem⟩
  · have htnil : t.1 = [] := eq_nil_of_dropLast_eq_self (by
      have h := congrArg Subtype.val hAB
      simpa using h.symm)
    have hsum : ∑ x ∈ (Finset.univ : Finset ↥(tmI S)).erase (⟨t.1, t.2⟩ : ↥(tmI S)),
        ((tmA q θ w t.1 x.1 : Polynomial K) : PowerSeries K)
          * frobTwist (R := K) (p := q) 1 (tmPsi q ω w x.1 t'.1) = 0 := by
      refine Finset.sum_eq_zero fun x hx => ?_
      exact hzero x (Finset.ne_of_mem_erase hx)
        (fun h => (Finset.ne_of_mem_erase hx) (h.trans hAB.symm))
    rw [hsum, if_pos htnil, add_zero, zero_add]
  · rw [Finset.sum_eq_single (⟨t.1.dropLast, hmem⟩ : ↥(tmI S))
      (fun x hx hxB => hzero x (Finset.ne_of_mem_erase hx) hxB)
      (fun hBmem => by
        have hBA : (⟨t.1.dropLast, hmem⟩ : ↥(tmI S)) = ⟨t.1, t.2⟩ := by
          by_contra hne
          exact hBmem (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩)
        exact absurd hBA.symm hAB),
      if_neg (fun hnil => hAB (Subtype.ext (by simp [hnil])))]
    ring



/-- **The `f`-row, entry by entry**: each tuple `s ∈ S` contributes the difference
`𝓛(s\t) - 𝓛(s\t)^{(1)}`, which the peel recursion rewrites with the `(X - θ^q)`-factor coming from
the period functional equation. -/
lemma tmF_entry (q : ℕ) [FrobPow K q] (θ : K) (w : ℕ) {ω : PowerSeries K} {γ : Γ₀}
    (hγ : γ < 1) (harch : GammaArchimedean Γ₀) (hq : 2 ≤ q) (hω : GIsSmall γ ω)
    (hωfe : (PowerSeries.X - PowerSeries.C (θ ^ q)) * frobTwist (R := K) (p := q) 1 ω = ω)
    {s : List (ℕ × Polynomial K)}
    (hs : ∀ y ∈ s, GIsSmall γ (ω ^ y.1 * (y.2 : PowerSeries K)))
    (hw : tmWeight s = w) (t' : List (ℕ × Polynomial K)) :
    (if s.take t'.length = t' then
      (cf s : PowerSeries K) * (tmL q ω (s.drop t'.length)
        - frobTwist (R := K) (p := q) 1 (tmL q ω (s.drop t'.length))) else 0)
      = (cf s : PowerSeries K) * (tmQ s : PowerSeries K)
          * (PowerSeries.X - PowerSeries.C (θ ^ q)) ^ (w - tmWeight s.dropLast)
          * frobTwist (R := K) (p := q) 1 (tmPsi q ω w s.dropLast t') := by
  have hpow : ∀ n : ℕ, (PowerSeries.X - PowerSeries.C (θ ^ q)) ^ n
      * (frobTwist (R := K) (p := q) 1 ω) ^ n = ω ^ n := by
    intro n; rw [← mul_pow, hωfe]
  by_cases hs0 : s = []
  · subst hs0
    by_cases ht' : t' = []
    · subst ht'
      simp [tmQ]
    · have hc : ¬ (([] : List (ℕ × Polynomial K)).take t'.length = t') := by simpa using ht'
      rw [if_neg hc]
      have hz : ¬ ((([] : List (ℕ × Polynomial K)).dropLast).take t'.length = t') := by
        simpa using ht'
      rw [tmPsi_not_prefix q ω w hz, frobTwist_zero, mul_zero]
  · have hsdd : s.dropLast ++ [s.getLastD (0, 0)] = s := by
      rcases List.eq_nil_or_concat s with h | ⟨u, y, h⟩
      · exact absurd h hs0
      · rw [h, List.concat_eq_append, List.dropLast_concat, List.getLastD_concat]
    by_cases hpre : s.dropLast.take t'.length = t'
    · have hlen : t'.length ≤ s.dropLast.length := by
        have h := congrArg List.length hpre
        rw [List.length_take] at h
        omega
      have hpre' : s.take t'.length = t' := by
        have h2 : s.take t'.length = s.dropLast.take t'.length := by
          conv_lhs => rw [← hsdd]
          rw [List.take_append_of_le_length hlen]
        rw [h2, hpre]
      have hdrop : s.drop t'.length
          = s.dropLast.drop t'.length ++ [s.getLastD (0, 0)] := by
        conv_lhs => rw [← hsdd]
        rw [List.drop_append_of_le_length hlen]
      have hL : ∀ y ∈ s.dropLast.drop t'.length,
          GIsSmall γ (ω ^ y.1 * (y.2 : PowerSeries K)) := by
        intro y hy
        exact hs y (by
          rw [← hsdd]
          exact List.mem_append_left _ (List.mem_of_mem_drop hy))
      have hQsm : GIsSmall γ (ω ^ (s.getLastD (0, 0)).1
          * (((s.getLastD (0, 0)).2 : Polynomial K) : PowerSeries K)) := by
        refine hs _ ?_
        rw [← hsdd]; simp
      have hp := tmL_peel q ω hγ harch hq hω (s.dropLast.drop t'.length) hL
        (s.getLastD (0, 0)).1 (Q := (s.getLastD (0, 0)).2) hQsm
      rw [← hdrop] at hp
      have hdiff : tmL q ω (s.drop t'.length)
          - frobTwist (R := K) (p := q) 1 (tmL q ω (s.drop t'.length))
          = ω ^ (s.getLastD (0, 0)).1 * ((s.getLastD (0, 0)).2 : PowerSeries K)
              * frobTwist (R := K) (p := q) 1
                  (tmL q ω (s.dropLast.drop t'.length)) := by
        nth_rewrite 1 [hp]; ring
      have hfe : ∀ n : ℕ, (PowerSeries.X - PowerSeries.C (θ ^ q)) ^ n
          * frobTwist (R := K) (p := q) 1 (tmL q ω (s.dropLast.drop t'.length) * ω ^ n)
          = frobTwist (R := K) (p := q) 1 (tmL q ω (s.dropLast.drop t'.length)) * ω ^ n := by
        intro n
        rw [frobTwist_mul, frobTwist_pow]
        rw [show (PowerSeries.X - PowerSeries.C (θ ^ q)) ^ n
              * (frobTwist (R := K) (p := q) 1 (tmL q ω (s.dropLast.drop t'.length))
                * (frobTwist (R := K) (p := q) 1 ω) ^ n)
            = frobTwist (R := K) (p := q) 1 (tmL q ω (s.dropLast.drop t'.length))
              * ((PowerSeries.X - PowerSeries.C (θ ^ q)) ^ n
                * (frobTwist (R := K) (p := q) 1 ω) ^ n) from by ring]
        rw [hpow n]
      rw [if_pos hpre', tmPsi_prefix q ω w hpre, hdiff]
      rw [show (cf s : PowerSeries K) * (tmQ s : PowerSeries K)
            * (PowerSeries.X - PowerSeries.C (θ ^ q)) ^ (w - tmWeight s.dropLast)
            * frobTwist (R := K) (p := q) 1
                (tmL q ω (s.dropLast.drop t'.length) * ω ^ (w - tmWeight s.dropLast))
          = (cf s : PowerSeries K) * (tmQ s : PowerSeries K)
            * ((PowerSeries.X - PowerSeries.C (θ ^ q)) ^ (w - tmWeight s.dropLast)
              * frobTwist (R := K) (p := q) 1
                  (tmL q ω (s.dropLast.drop t'.length) * ω ^ (w - tmWeight s.dropLast)))
          from by ring]
      rw [hfe (w - tmWeight s.dropLast)]
      have hσ : w - tmWeight s.dropLast = (s.getLastD (0, 0)).1 := by
        have h := tmWeight_dropLast s
        omega
      simp only [tmQ]
      rw [← hσ]
      ring
    · have hz : tmPsi q ω w s.dropLast t' = 0 := tmPsi_not_prefix q ω w hpre
      rw [hz, frobTwist_zero, mul_zero]
      by_cases hc : s.take t'.length = t'
      · have hts : t' = s := by
          have h1 : t'.length ≤ s.length := by
            rw [← hc, List.length_take]; exact min_le_right _ _
          rcases lt_or_eq_of_le h1 with hlt | heq
          · exfalso
            apply hpre
            have hlen2 : t'.length ≤ s.dropLast.length := by
              rw [List.length_dropLast]; omega
            have h2 : s.dropLast.take t'.length = s.take t'.length := by
              conv_rhs => rw [← hsdd]
              rw [List.take_append_of_le_length hlen2]
            rw [h2, hc]
          · rw [← hc, heq, List.take_length]
        rw [if_pos hc, hts, List.drop_length, tmL_nil, frobTwist_one, sub_self]
        ring
      · rw [if_neg hc]





/-- The `v`-row of the merged dual `t`-motive, read in `K⟦t⟧`. -/
noncomputable def tmVps (q : ℕ) (θ : K) (w : ℕ)
    (S : Finset (List (ℕ × Polynomial K))) (cf : List (ℕ × Polynomial K) → Polynomial K)
    (t : List (ℕ × Polynomial K)) : PowerSeries K :=
  ∑ s ∈ S, ((if s.dropLast = t then cf s * tmQ s
    * (X - C (θ ^ q)) ^ (w - tmWeight t) else 0 : Polynomial K) : PowerSeries K)

lemma tmV_coe (q : ℕ) (θ : K) (w : ℕ) (t : List (ℕ × Polynomial K)) :
    ((tmV q θ w S cf t : Polynomial K) : PowerSeries K) = tmVps q θ w S cf t := by
  rw [tmV, tmVps]
  exact map_sum (Polynomial.coeToPowerSeries.ringHom)
    (fun s => (if s.dropLast = t then cf s * tmQ s
      * (X - C (θ ^ q)) ^ (w - tmWeight t) else 0 : Polynomial K)) S

/-- **The `(none,some)` entry**: the `f`-row functional equation

  `f_t = f_t^{(1)} + ∑_{t'} v_{t'}·(Ψ^0_{t',t})^{(1)}`,

i.e. Dac's `f^{(-1)} = f + vΨ^0` in the positive-twist normalisation.  This is the only place
where the *coefficient invariance* `frobTwist 1 a_i = a_i` is used (see `PLAN.md`, SESSION 313
§3): the `a_i` must be polynomials in the series variable `t` with `F_q`-coefficients. -/
lemma tmF_functional (q : ℕ) [FrobPow K q] (θ : K) (w : ℕ) {ω : PowerSeries K} {γ : Γ₀}
    (hγ : γ < 1) (harch : GammaArchimedean Γ₀) (hq : 2 ≤ q) (hω : GIsSmall γ ω)
    (hωfe : (PowerSeries.X - PowerSeries.C (θ ^ q)) * frobTwist (R := K) (p := q) 1 ω = ω)
    (hw : ∀ s ∈ S, tmWeight s = w)
    (hcf : ∀ s ∈ S, frobTwist (R := K) (p := q) 1 ((cf s : Polynomial K) : PowerSeries K)
      = ((cf s : Polynomial K) : PowerSeries K))
    (hsm : ∀ s ∈ S, ∀ y ∈ s, GIsSmall γ (ω ^ y.1 * (y.2 : PowerSeries K)))
    (hne : ∀ s ∈ S, s ≠ [])
    (t' : ↥(tmI S)) :
    tmF q ω w S cf t'.1
      = frobTwist (R := K) (p := q) 1 (tmF q ω w S cf t'.1)
        + ∑ t : ↥(tmI S), (tmV q θ w S cf t.1 : PowerSeries K)
            * frobTwist (R := K) (p := q) 1 (tmPsi q ω w t.1 t'.1) := by
  have hmemS : ∀ s ∈ S, s.dropLast ∈ tmI S := by
    intro s hs
    have hpos : 0 < s.length := List.length_pos_iff.mpr (hne s hs)
    refine mem_tmI.mpr ⟨s, hs, s.length - 1, by omega, ?_⟩
    exact List.dropLast_eq_take.symm
  have hF : tmF q ω w S cf t'.1
      = ∑ s ∈ S.filter (fun s => s.take t'.1.length = t'.1),
          (cf s : PowerSeries K) * tmL q ω (s.drop t'.1.length) := by
    rw [tmF, ← Finset.sum_filter]
  have hFt : frobTwist (R := K) (p := q) 1 (tmF q ω w S cf t'.1)
      = ∑ s ∈ S.filter (fun s => s.take t'.1.length = t'.1),
          (cf s : PowerSeries K) * frobTwist (R := K) (p := q) 1
            (tmL q ω (s.drop t'.1.length)) := by
    rw [hF]
    rw [show frobTwist (R := K) (p := q) 1
          (∑ s ∈ S.filter (fun s => s.take t'.1.length = t'.1),
            (cf s : PowerSeries K) * tmL q ω (s.drop t'.1.length))
        = ∑ s ∈ S.filter (fun s => s.take t'.1.length = t'.1),
            frobTwist (R := K) (p := q) 1 ((cf s : PowerSeries K) * tmL q ω (s.drop t'.1.length))
        from map_sum (frobTwistHom (R := K) (p := q) 1) _ _]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [frobTwist_mul, hcf s (Finset.mem_of_mem_filter s hs)]
  have hper : ∑ s ∈ S.filter (fun s => s.take t'.1.length = t'.1),
        (cf s : PowerSeries K) * (tmL q ω (s.drop t'.1.length)
          - frobTwist (R := K) (p := q) 1 (tmL q ω (s.drop t'.1.length)))
      = ∑ s ∈ S, (cf s : PowerSeries K) * (tmQ s : PowerSeries K)
          * (PowerSeries.X - PowerSeries.C (θ ^ q)) ^ (w - tmWeight s.dropLast)
          * frobTwist (R := K) (p := q) 1 (tmPsi q ω w s.dropLast t'.1) := by
    have hcongr : ∀ s ∈ S.filter (fun s => s.take t'.1.length = t'.1),
        (cf s : PowerSeries K) * (tmL q ω (s.drop t'.1.length)
          - frobTwist (R := K) (p := q) 1 (tmL q ω (s.drop t'.1.length)))
        = (cf s : PowerSeries K) * (tmQ s : PowerSeries K)
            * (PowerSeries.X - PowerSeries.C (θ ^ q)) ^ (w - tmWeight s.dropLast)
            * frobTwist (R := K) (p := q) 1 (tmPsi q ω w s.dropLast t'.1) := by
      intro s hs
      have hsS : s ∈ S := Finset.mem_of_mem_filter s hs
      have hcond : s.take t'.1.length = t'.1 := (Finset.mem_filter.mp hs).2
      have hmain := tmF_entry (q := q) (θ := θ) (w := w) (cf := cf)
        hγ harch hq hω hωfe (hsm s hsS) (hw s hsS) t'.1
      rw [if_pos hcond] at hmain
      exact hmain
    rw [Finset.sum_congr rfl hcongr]
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro s hsS hsnot
    have hcond : ¬ (s.take t'.1.length = t'.1) := fun h =>
      hsnot (Finset.mem_filter.mpr ⟨hsS, h⟩)
    have hz : tmPsi q ω w s.dropLast t'.1 = 0 := by
      refine tmPsi_not_prefix q ω w (fun h => hcond ?_)
      exact (List.prefix_iff_eq_take.mp
        ((List.prefix_iff_eq_take.mpr h.symm).trans (List.dropLast_prefix s))).symm
    rw [hz, frobTwist_zero, mul_zero]
  have hswap : (∑ t : ↥(tmI S), tmVps q θ w S cf t.1
        * frobTwist (R := K) (p := q) 1 (tmPsi q ω w t.1 t'.1))
      = ∑ s ∈ S, (cf s : PowerSeries K) * (tmQ s : PowerSeries K)
          * (PowerSeries.X - PowerSeries.C (θ ^ q)) ^ (w - tmWeight s.dropLast)
          * frobTwist (R := K) (p := q) 1 (tmPsi q ω w s.dropLast t'.1) := by
    have h1 : ∀ t : ↥(tmI S), tmVps q θ w S cf t.1
        * frobTwist (R := K) (p := q) 1 (tmPsi q ω w t.1 t'.1)
        = ∑ s ∈ S, ((if s.dropLast = t.1 then cf s * tmQ s
            * (X - C (θ ^ q)) ^ (w - tmWeight t.1) else 0 : Polynomial K) : PowerSeries K)
            * frobTwist (R := K) (p := q) 1 (tmPsi q ω w t.1 t'.1) := by
      intro t; rw [tmVps, Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun t _ => h1 t), Finset.sum_comm]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [Finset.sum_eq_single (⟨s.dropLast, hmemS s hs⟩ : ↥(tmI S))
      (fun t _ ht => by
        have hz : (if s.dropLast = t.1 then cf s * tmQ s
            * (X - C (θ ^ q)) ^ (w - tmWeight t.1) else 0 : Polynomial K) = 0 :=
          if_neg (fun h => ht (Subtype.ext h).symm)
        rw [hz, Polynomial.coe_zero, zero_mul])
      (fun hmem => absurd (Finset.mem_univ _) hmem)]
    rw [if_pos rfl]
    push_cast
    simp only [tmQ]
  have hswap' : (∑ t : ↥(tmI S), (tmV q θ w S cf t.1 : PowerSeries K)
        * frobTwist (R := K) (p := q) 1 (tmPsi q ω w t.1 t'.1))
      = ∑ s ∈ S, (cf s : PowerSeries K) * (tmQ s : PowerSeries K)
          * (PowerSeries.X - PowerSeries.C (θ ^ q)) ^ (w - tmWeight s.dropLast)
          * frobTwist (R := K) (p := q) 1 (tmPsi q ω w s.dropLast t'.1) := by
    rw [← hswap]
    exact Finset.sum_congr rfl fun t _ => by rw [tmV_coe]
  have key : tmF q ω w S cf t'.1 - frobTwist (R := K) (p := q) 1 (tmF q ω w S cf t'.1)
      = ∑ t : ↥(tmI S), (tmV q θ w S cf t.1 : PowerSeries K)
          * frobTwist (R := K) (p := q) 1 (tmPsi q ω w t.1 t'.1) := by
    rw [hFt, hF, ← Finset.sum_sub_distrib]
    rw [show ∑ x ∈ S.filter (fun s => s.take t'.1.length = t'.1),
          ((cf x : PowerSeries K) * tmL q ω (x.drop t'.1.length)
            - (cf x : PowerSeries K) * frobTwist (R := K) (p := q) 1 (tmL q ω (x.drop t'.1.length)))
        = ∑ x ∈ S.filter (fun s => s.take t'.1.length = t'.1),
          (cf x : PowerSeries K) * (tmL q ω (x.drop t'.1.length)
            - frobTwist (R := K) (p := q) 1 (tmL q ω (x.drop t'.1.length)))
        from Finset.sum_congr rfl (fun x _ => by ring)]
    rw [hper, hswap']
  rw [← key]
  ring



lemma tmWeight_le_of_mem_tmI (w : ℕ) {t : List (ℕ × Polynomial K)} (ht : t ∈ tmI S)
    (hw : ∀ s ∈ S, tmWeight s = w) : tmWeight t ≤ w := by
  obtain ⟨s, hs, k, hk, rfl⟩ := mem_tmI.mp ht
  rw [← hw s hs]
  calc tmWeight (s.take k) ≤ tmWeight (s.take k) + tmWeight (s.drop k) :=
        Nat.le_add_right _ _
    _ = tmWeight s := (tmWeight_take_add_drop s k).symm

/-- ★★★ **The functional equation of the merged dual `t`-motive** (Dac §5.1):
`Ψ = A·Ψ^{(1)}`, i.e. `Ψ^{(-1)} = ΦΨ` with `Φ := A^{(-1)}`. -/
theorem tmPsiOpt_functional (q : ℕ) [FrobPow K q] (θ : K) (w : ℕ) {ω : PowerSeries K}
    {γ : Γ₀} (hγ : γ < 1) (harch : GammaArchimedean Γ₀) (hq : 2 ≤ q) (hω : GIsSmall γ ω)
    (hωfe : (PowerSeries.X - PowerSeries.C (θ ^ q)) * frobTwist (R := K) (p := q) 1 ω = ω)
    (hw : ∀ s ∈ S, tmWeight s = w)
    (hcf : ∀ s ∈ S, frobTwist (R := K) (p := q) 1 ((cf s : Polynomial K) : PowerSeries K)
      = ((cf s : Polynomial K) : PowerSeries K))
    (hsm : ∀ s ∈ S, ∀ y ∈ s, GIsSmall γ (ω ^ y.1 * (y.2 : PowerSeries K)))
    (hne : ∀ s ∈ S, s ≠ []) :
    tmPsiOpt q ω w S cf
      = (coeHom (K := K)).mapMatrix (tmAOpt q θ w S cf)
        * frobTwistMat (q := q) 1 (tmPsiOpt q ω w S cf) := by
  funext i j
  cases i with
  | none =>
    cases j with
    | none =>
      rw [Matrix.mul_apply, Fintype.sum_option]
      simp only [tmPsiOpt_none_none, tmPsiOpt_some_none,
        tmAOpt_none_none, tmAOpt_none_some, frobTwistMat_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
        coeHom_apply, Polynomial.coe_one, one_mul, frobTwist_one, frobTwist_zero, mul_zero,
        Finset.sum_const_zero, add_zero]
    | some t' =>
      rw [Matrix.mul_apply, Fintype.sum_option]
      simp only [tmPsiOpt_none_some, tmPsiOpt_some_some,
        tmAOpt_none_none, tmAOpt_none_some, frobTwistMat_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
        coeHom_apply, Polynomial.coe_one, one_mul]
      exact tmF_functional q θ w (S := S) (cf := cf) hγ harch hq hω hωfe hw hcf hsm hne t'
  | some t =>
    cases j with
    | none =>
      rw [Matrix.mul_apply, Fintype.sum_option]
      simp only [tmPsiOpt_some_none, tmPsiOpt_none_none, tmAOpt_some_none,
        tmAOpt_some_some, frobTwistMat_apply, RingHom.mapMatrix_apply, Matrix.map_apply, coeHom_apply,
        Polynomial.coe_zero, zero_mul, frobTwist_zero, mul_zero, Finset.sum_const_zero,
        add_zero]
    | some t' =>
      rw [Matrix.mul_apply, Fintype.sum_option]
      simp only [tmPsiOpt_some_some, tmPsiOpt_none_some, tmAOpt_some_none,
        tmAOpt_some_some, frobTwistMat_apply, RingHom.mapMatrix_apply, Matrix.map_apply, coeHom_apply,
        Polynomial.coe_zero, zero_mul, zero_add]
      rw [sum_tmAOpt_eq (S := S) (q := q) (θ := θ) (w := w) (ω := ω) t t']
      have hsm_t : ∀ y ∈ t.1, GIsSmall γ (ω ^ y.1 * (y.2 : PowerSeries K)) := by
        obtain ⟨s, hs, k, hk, hkt⟩ := mem_tmI.mp t.2
        intro y hy
        rw [← hkt] at hy
        exact hsm s hs y (List.mem_of_mem_take hy)
      exact tmPsi_functional (q := q) (ω := ω) (w := w)
        hγ harch hq hω hωfe hsm_t
        (tmWeight_le_of_mem_tmI (S := S) (w := w) (ht := t.2) (hw := hw)) t'.1

end functionalMatrix

end matrix

end ZagierHoffmanPositiveChar
