import Mathlib
import Submission.Vdw.LocalField.Eisenstein
import Submission.Vdw.LocalField.KpVal

open Classical
open IsLocalRing
open scoped NumberField WithZero Valued

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

/-!
# WildDifferent sub-stone (e): the derivative bound `v_P(f_ϖ'(ϖ)) ≤ e·v_p(e)+e−1`

`f_ϖ := minpoly (Wk p P α) ϖval` is Eisenstein over 𝒪_W of degree
`e := P.ramificationIdx ℤ` (sub-stone (d), Eisenstein.lean): monic with
coefficient witnesses `z_i := fϖWk_z p P α i = owToKpInt ⟨coeff i, mem⟩`,
`z_i ∈ 𝔪^e` for `i < e`, `z_e = 1`, `z₀` of exact filtration `e`, and the
annihilating identity `∑_{i ≤ e} z_i·ϖ^i = 0`.  The derivative at the
uniformizer is the `kpInt` element `d := ∑_{i=1}^e (i : kpInt)·z_i·ϖ^(i−1)`
(= `f_ϖ'(ϖval)` in `K_P`), and sub-stone (e) is `d ∉ 𝔪^{e·v_p(e)+e}`
(equivalently `kpVal d ≤ e·v_p(e) + e − 1`).

(e1) TERM-VALUE DISTINCTNESS: each nonzero term `t_i := (i)·z_i·ϖ^(i−1)`
has exact value `kpVal t_i = kpVal(i:ℕ) + kpVal(z_i) + (i−1)`
(`fϖWk_derivTerm_kpVal`); `kpVal(i:ℕ)` is an `e`-multiple
(`kpVal_natCast_eq_mul_ramIdx`) and `kpVal(z_i)` is an `e`-multiple
((U) `OW_witness_kpVal_dvd`), so `kpVal t_i ≡ (i−1) (mod e)` and the
values of distinct terms are distinct (`fϖWk_derivTerm_val_inj`, via the
ℤ-divisibility criterion `nat_eq_of_int_dvd_sub_of_le`).

(e2) NO-CANCELLATION (`sum_not_mem_pow_of_distinct_exact`): a finite sum
of elements with pairwise-distinct exact filtration values lies in
`𝔪^m \ 𝔪^(m+1)` for `m := min a_j` (choose the minimizer by
`Finset.exists_min_image` and apply `sum_exact_pow_min`); in particular it
is NOT in `𝔪^(a_{j*}+1)` for any `j*`.

THEOREM **`fϖWk_deriv_not_mem_pow`** — sub-stone (e): `d ∉
𝔪^{e·padicValNat p e + e}`: apply (e2) to the nonzero derivative terms
with the e-term (`i = e`, exact value `kpVal(e:ℕ) + (e−1) = e·v_p(e)+e−1`)
as `j*` (zero terms are dropped from the sum, which does not change its
value).  Axioms: propext/choice/Quot.sound only.
-/

namespace Submission.Vdw.LocalField

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- Generic no-cancellation at the uniformizer filtration: a finite sum of
elements with pairwise-distinct exact filtration values is not in
`𝔪^(a j* + 1)` for any index `j*`. -/
lemma sum_not_mem_pow_of_distinct_exact (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (hs : s.Nonempty) (x : ι → kpInt p P)
    (a : ι → ℕ)
    (hmem : ∀ j ∈ s, x j ∈ (maximalIdeal (kpInt p P)) ^ a j)
    (hnot : ∀ j ∈ s, x j ∉ (maximalIdeal (kpInt p P)) ^ (a j + 1))
    (hinj : ∀ ⦃j : ι⦄, j ∈ s → ∀ ⦃k : ι⦄, k ∈ s → a j = a k → j = k) :
    ∀ jstar ∈ s, (∑ j ∈ s, x j) ∉ (maximalIdeal (kpInt p P)) ^ (a jstar + 1) := by
  classical
  intro jstar hjstar
  rcases Finset.exists_min_image s a hs with ⟨j0, hj0s, hj0min⟩
  have hstrict : ∀ j ∈ s, j ≠ j0 → a j0 < a j := by
    intro j hj hne
    refine lt_of_le_of_ne (hj0min j hj) ?_
    intro heq
    apply hne
    exact (hinj hj0s hj heq).symm
  have hsum := sum_exact_pow_min (maximalIdeal (kpInt p P)) s x a (by exact hj0s) hmem hnot
    (fun j hj => hj0min j hj) hstrict
  intro hmemstar
  have hle : a j0 + 1 ≤ a jstar + 1 := Nat.succ_le_succ (hj0min jstar hjstar)
  have hsub : (maximalIdeal (kpInt p P)) ^ (a jstar + 1) ≤ (maximalIdeal (kpInt p P)) ^ (a j0 + 1) :=
    Ideal.pow_le_pow_right hle
  exact hsum.2 (hsub hmemstar)

/-- The exact filtration value of a nonzero derivative term
`t_i := (i : kpInt)·z_i·ϖ^(i−1)`. -/
lemma fϖWk_derivTerm_kpVal (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} {i : ℕ} (hi1 : 1 ≤ i) (hzi : fϖWk_z p P α i ≠ 0) :
    kpVal p P ((i : kpInt p P) * fϖWk_z p P α i * uniformizer p P ^ (i - 1))
      = kpVal p P (i : kpInt p P) + kpVal p P (fϖWk_z p P α i) + (i - 1) := by
  classical
  have hiz : (i : kpInt p P) ≠ 0 := natCast_ne_zero_kpInt p P i (by omega)
  have hc0 : uniformizer p P ^ (i - 1) ≠ 0 := uniformizer_pow_ne_zero p P (i - 1)
  have hab0 : (i : kpInt p P) * fϖWk_z p P α i ≠ 0 := mul_ne_zero hiz hzi
  calc
    kpVal p P ((i : kpInt p P) * fϖWk_z p P α i * uniformizer p P ^ (i - 1))
        = kpVal p P ((i : kpInt p P) * fϖWk_z p P α i) + kpVal p P (uniformizer p P ^ (i - 1)) := by
          rw [kpVal_mul p P ((i : kpInt p P) * fϖWk_z p P α i) (uniformizer p P ^ (i - 1)) hab0 hc0]
    _ = (kpVal p P (i : kpInt p P) + kpVal p P (fϖWk_z p P α i)) + (i - 1) := by
          rw [kpVal_mul p P (i : kpInt p P) (fϖWk_z p P α i) hiz hzi]
          rw [kpVal_uniformizer_pow p P (i - 1)]
    _ = kpVal p P (i : kpInt p P) + kpVal p P (fϖWk_z p P α i) + (i - 1) := by omega

/-- ℤ-criterion: `1 ≤ i, j ≤ e` and `e | (i − j)` (in ℤ) force `i = j`. -/
lemma nat_eq_of_int_dvd_sub_of_le {e i j : ℕ} (he1 : 1 ≤ e) (hi1 : 1 ≤ i) (hie : i ≤ e)
    (hj1 : 1 ≤ j) (hje : j ≤ e) (hdiv : (e : ℤ) ∣ (i : ℤ) - (j : ℤ)) : i = j := by
  have _he1' := he1
  classical
  classical
  rcases hdiv with ⟨c, hc⟩
  by_contra hne
  have hlo : -(e - 1 : ℤ) ≤ (i : ℤ) - (j : ℤ) := by
    have h1 : 1 ≤ (i : ℤ) := by exact_mod_cast hi1
    have h4 : (j : ℤ) ≤ (e : ℤ) := by exact_mod_cast hje
    omega
  have hhi : (i : ℤ) - (j : ℤ) ≤ (e - 1 : ℤ) := by
    have h2 : (i : ℤ) ≤ (e : ℤ) := by exact_mod_cast hie
    have h3 : 1 ≤ (j : ℤ) := by exact_mod_cast hj1
    omega
  have hcne : c ≠ 0 := by
    intro hc0
    apply hne
    rw [hc0, mul_zero] at hc
    omega
  have he0 : 0 ≤ (e : ℤ) := by exact_mod_cast (Nat.zero_le e)
  rw [hc] at hlo hhi
  by_cases hcpos : 0 < c
  · have hc1 : 1 ≤ c := by omega
    have hge : (e : ℤ) ≤ (e : ℤ) * c := by
      have h := mul_le_mul_of_nonneg_left hc1 he0
      simpa using h
    omega
  · have hcm1 : c ≤ -1 := by omega
    have hnc : 1 ≤ -c := by omega
    have hge' : (e : ℤ) ≤ (e : ℤ) * (-c) := by
      have h := mul_le_mul_of_nonneg_left hnc he0
      simpa using h
    have hle' : (e : ℤ) * c ≤ -(e : ℤ) := by
      have hrel : (e : ℤ) * c = -((e : ℤ) * -c) := by ring
      rw [hrel]
      exact neg_le_neg hge'
    omega

/-- Divisibility of an ℕ-value lifts to ℤ. -/
lemma int_dvd_of_nat_dvd_cast {e n : ℕ} (h : e ∣ n) : (e : ℤ) ∣ (n : ℤ) := by
  rcases h with ⟨c, hc⟩
  refine ⟨(c : ℤ), ?_⟩
  exact_mod_cast hc

/-- The e-term value: `kpVal ((e:ℕ):kpInt) = e · padicValNat p e`. -/
lemma kpVal_natCast_e (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    kpVal p P ((P.ramificationIdx ℤ : ℕ) : kpInt p P)
      = P.ramificationIdx ℤ * padicValNat p (P.ramificationIdx ℤ) := by
  classical
  exact kpVal_natCast_eq_mul_ramIdx p P (P.ramificationIdx ℤ)
    (by exact Nat.pos_iff_ne_zero.mp (Ideal.ramificationIdx_pos P ℤ))

/-- (e1): the exact values of distinct derivative terms are distinct. -/
lemma fϖWk_derivTerm_val_inj (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1)
    {i j : ℕ} (hi1 : 1 ≤ i) (hie : i ≤ P.ramificationIdx ℤ)
    (hzi : fϖWk_z p P α i ≠ 0) (hj1 : 1 ≤ j) (hje : j ≤ P.ramificationIdx ℤ)
    (hzj : fϖWk_z p P α j ≠ 0)
    (hv : kpVal p P ((i : kpInt p P) * fϖWk_z p P α i * uniformizer p P ^ (i - 1))
        = kpVal p P ((j : kpInt p P) * fϖWk_z p P α j * uniformizer p P ^ (j - 1))) :
    i = j := by
  classical
  apply nat_eq_of_int_dvd_sub_of_le (e := P.ramificationIdx ℤ)
  · exact Ideal.ramificationIdx_pos P ℤ
  · exact hi1
  · exact hie
  · exact hj1
  · exact hje
  -- value formulas (ℕ) and their ℤ-casts:
  have hfi := fϖWk_derivTerm_kpVal p P hi1 hzi
  have hfj := fϖWk_derivTerm_kpVal p P hj1 hzj
  have hv_z : (kpVal p P ((i : kpInt p P) * fϖWk_z p P α i * uniformizer p P ^ (i - 1)) : ℤ)
      = (kpVal p P ((j : kpInt p P) * fϖWk_z p P α j * uniformizer p P ^ (j - 1)) : ℤ) := by
    exact congrArg (fun n : ℕ => (n : ℤ)) hv
  -- e | kpVal((i:ℕ):kpInt) etc, lifted to ℤ:
  have hci_dvd : (P.ramificationIdx ℤ : ℤ) ∣ (kpVal p P (i : kpInt p P) : ℤ) := by
    have h : P.ramificationIdx ℤ ∣ kpVal p P (i : kpInt p P) := by
      rw [kpVal_natCast_eq_mul_ramIdx p P i (by omega)]
      exact ⟨padicValNat p i, rfl⟩
    exact int_dvd_of_nat_dvd_cast h
  have hcj_dvd : (P.ramificationIdx ℤ : ℤ) ∣ (kpVal p P (j : kpInt p P) : ℤ) := by
    have h : P.ramificationIdx ℤ ∣ kpVal p P (j : kpInt p P) := by
      rw [kpVal_natCast_eq_mul_ramIdx p P j (by omega)]
      exact ⟨padicValNat p j, rfl⟩
    exact int_dvd_of_nat_dvd_cast h
  have hui_dvd : (P.ramificationIdx ℤ : ℤ) ∣ (kpVal p P (fϖWk_z p P α i) : ℤ) := by
    have hc0 : (⟨(fϖWk p P α).coeff i, fϖWk_coeff_mem_OW p P α i⟩ : OW_subring p P α) ≠ 0 := by
      intro hc
      apply hzi
      dsimp [fϖWk_z]
      rw [hc]
      simp
    have h := OW_witness_kpVal_dvd p P hα hgen
      (⟨(fϖWk p P α).coeff i, fϖWk_coeff_mem_OW p P α i⟩ : OW_subring p P α) hc0
    simpa [fϖWk_z] using (int_dvd_of_nat_dvd_cast h)
  have huj_dvd : (P.ramificationIdx ℤ : ℤ) ∣ (kpVal p P (fϖWk_z p P α j) : ℤ) := by
    have hc0 : (⟨(fϖWk p P α).coeff j, fϖWk_coeff_mem_OW p P α j⟩ : OW_subring p P α) ≠ 0 := by
      intro hc
      apply hzj
      dsimp [fϖWk_z]
      rw [hc]
      simp
    have h := OW_witness_kpVal_dvd p P hα hgen
      (⟨(fϖWk p P α).coeff j, fϖWk_coeff_mem_OW p P α j⟩ : OW_subring p P α) hc0
    simpa [fϖWk_z] using (int_dvd_of_nat_dvd_cast h)
  rcases hci_dvd with ⟨a, ha⟩
  rcases hui_dvd with ⟨b, hb⟩
  rcases hcj_dvd with ⟨c, hc⟩
  rcases huj_dvd with ⟨d, hd⟩
  refine ⟨(c + d) - (a + b), ?_⟩
  -- goal: (i : ℤ) − (j : ℤ) = (e:ℤ)·((c+d)−(a+b))
  have hsubi : ((i - 1 : ℕ) : ℤ)
      = (kpVal p P ((i : kpInt p P) * fϖWk_z p P α i * uniformizer p P ^ (i - 1)) : ℤ)
        - (kpVal p P (i : kpInt p P) : ℤ) - (kpVal p P (fϖWk_z p P α i) : ℤ) := by
    have hfiz : ((kpVal p P ((i : kpInt p P) * fϖWk_z p P α i * uniformizer p P ^ (i - 1))) : ℤ)
        = (kpVal p P (i : kpInt p P) : ℤ) + (kpVal p P (fϖWk_z p P α i) : ℤ) + ((i - 1 : ℕ) : ℤ) := by
      exact_mod_cast hfi
    omega
  have hsubj : ((j - 1 : ℕ) : ℤ)
      = (kpVal p P ((j : kpInt p P) * fϖWk_z p P α j * uniformizer p P ^ (j - 1)) : ℤ)
        - (kpVal p P (j : kpInt p P) : ℤ) - (kpVal p P (fϖWk_z p P α j) : ℤ) := by
    have hfjz : ((kpVal p P ((j : kpInt p P) * fϖWk_z p P α j * uniformizer p P ^ (j - 1))) : ℤ)
        = (kpVal p P (j : kpInt p P) : ℤ) + (kpVal p P (fϖWk_z p P α j) : ℤ) + ((j - 1 : ℕ) : ℤ) := by
      exact_mod_cast hfj
    omega
  calc
    (i : ℤ) - (j : ℤ) = (((i - 1 : ℕ) : ℤ) + 1) - (((j - 1 : ℕ) : ℤ) + 1) := by
      have hi' : (i : ℤ) = ((i - 1 : ℕ) : ℤ) + 1 := by
        have h : i = (i - 1) + 1 := (Nat.sub_add_cancel hi1).symm
        exact_mod_cast h
      have hj' : (j : ℤ) = ((j - 1 : ℕ) : ℤ) + 1 := by
        have h : j = (j - 1) + 1 := (Nat.sub_add_cancel hj1).symm
        exact_mod_cast h
      rw [hi', hj']
    _ = (kpVal p P (j : kpInt p P) : ℤ) + (kpVal p P (fϖWk_z p P α j) : ℤ)
        - (kpVal p P (i : kpInt p P) : ℤ) - (kpVal p P (fϖWk_z p P α i) : ℤ) := by
      omega
    _ = (P.ramificationIdx ℤ : ℤ) * ((c + d) - (a + b)) := by
      rw [ha, hb, hc, hd]
      ring

/-- **(e)**: the derivative of `f_ϖ` at the uniformizer is not in
`𝔪^{e·v_p(e)+e}` (equivalently `kpVal ≤ e·v_p(e) + e − 1`): the sum
`d := Σ_{i=1}^e (i : kpInt)·z_i·ϖ^(i−1)` (= the value of `f_ϖ'(ϖval)` in
`K_P`) has filtration degree at most `e·v_p(e)+e−1`. -/
theorem fϖWk_deriv_not_mem_pow (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1) :
    (∑ i ∈ Finset.Icc 1 (P.ramificationIdx ℤ),
        (i : kpInt p P) * fϖWk_z p P α i * uniformizer p P ^ (i - 1))
      ∉ (maximalIdeal (kpInt p P)) ^
          (P.ramificationIdx ℤ * padicValNat p (P.ramificationIdx ℤ) + P.ramificationIdx ℤ) := by
  classical
  let e : ℕ := P.ramificationIdx ℤ
  let t : ℕ → kpInt p P := fun i =>
    (i : kpInt p P) * fϖWk_z p P α i * uniformizer p P ^ (i - 1)
  let s : Finset ℕ := (Finset.Icc 1 e).filter (fun i => fϖWk_z p P α i ≠ 0)
  have he1 : 1 ≤ e := by
    dsimp [e]
    exact (Ideal.ramificationIdx_pos P ℤ)
  have hztop : fϖWk_z p P α (P.ramificationIdx ℤ) = 1 :=
    fϖWk_z_top_eq_one p P hα hgen
  have hztop0 : fϖWk_z p P α (P.ramificationIdx ℤ) ≠ 0 := by
    rw [hztop]
    simp
  have hSne : s.Nonempty := by
    refine ⟨e, ?_⟩
    dsimp [s]
    rw [Finset.mem_filter]
    constructor
    · exact Finset.mem_Icc.mpr ⟨he1, le_rfl⟩
    · simpa [e] using hztop0
  -- zero terms are dropped: the sum over Icc 1 e equals the sum over s:
  have hsub : s ⊆ Finset.Icc 1 e := by
    intro x hx
    exact (Finset.mem_filter.mp hx).1
  have hsum_eq : (∑ i ∈ Finset.Icc 1 e, t i) = ∑ i ∈ s, t i := by
    exact (Finset.sum_subset hsub (by
      intro x hx hxs
      have hz0 : fϖWk_z p P α x = 0 := by
        by_contra hz
        apply hxs
        dsimp [s]
        rw [Finset.mem_filter]
        exact ⟨hx, hz⟩
      simp [t, hz0])).symm
  -- membership / exactness / injectivity of the term values:
  have htj0 : ∀ j ∈ s, t j ≠ 0 := by
    intro j hj
    have hmemj := (Finset.mem_filter.mp hj).1
    have hzj := (Finset.mem_filter.mp hj).2
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hmemj).1
    have hjc : (j : kpInt p P) ≠ 0 := natCast_ne_zero_kpInt p P j (by omega)
    have hpow0 : uniformizer p P ^ (j - 1) ≠ 0 := uniformizer_pow_ne_zero p P (j - 1)
    dsimp [t]
    exact mul_ne_zero (mul_ne_zero hjc hzj) hpow0
  have hmem : ∀ j ∈ s, t j ∈ (maximalIdeal (kpInt p P)) ^ kpVal p P (t j) := by
    intro j hj
    exact (kpVal_exact p P (t j) (htj0 j hj)).1
  have hnot : ∀ j ∈ s, t j ∉ (maximalIdeal (kpInt p P)) ^ (kpVal p P (t j) + 1) := by
    intro j hj
    exact (kpVal_exact p P (t j) (htj0 j hj)).2
  have hinj : ∀ ⦃j : ℕ⦄, j ∈ s → ∀ ⦃k : ℕ⦄, k ∈ s → kpVal p P (t j) = kpVal p P (t k) → j = k := by
    intro j hj k hk hval
    have hmemj := (Finset.mem_filter.mp hj).1
    have hmemk := (Finset.mem_filter.mp hk).1
    have hzj := (Finset.mem_filter.mp hj).2
    have hzk := (Finset.mem_filter.mp hk).2
    have hji : 1 ≤ j := (Finset.mem_Icc.mp hmemj).1
    have hje : j ≤ P.ramificationIdx ℤ := by simpa [e] using (Finset.mem_Icc.mp hmemj).2
    have hki : 1 ≤ k := (Finset.mem_Icc.mp hmemk).1
    have hke : k ≤ P.ramificationIdx ℤ := by simpa [e] using (Finset.mem_Icc.mp hmemk).2
    exact fϖWk_derivTerm_val_inj p P hα hgen hji hje hzj hki hke hzk (by simpa [t] using hval)
  have hse : P.ramificationIdx ℤ ∈ s := by
    dsimp [s]
    rw [Finset.mem_filter]
    constructor
    · exact Finset.mem_Icc.mpr ⟨by simpa [e] using he1, by simp [e]⟩
    · simpa [e] using hztop0
  have htop_s := sum_not_mem_pow_of_distinct_exact p P s hSne t (fun j => kpVal p P (t j)) hmem hnot hinj
    (P.ramificationIdx ℤ) hse
  -- the top term value:
  have hval_top : kpVal p P (t (P.ramificationIdx ℤ))
      = P.ramificationIdx ℤ * padicValNat p (P.ramificationIdx ℤ) + (P.ramificationIdx ℤ - 1) := by
    have hf := fϖWk_derivTerm_kpVal p P (by simpa [e] using he1)
      (by simpa [e] using hztop0)
    -- hf : kpVal (t e) = kpVal((e:ℕ):kpInt) + kpVal(z e) + (e−1)
    have hz1 : kpVal p P (fϖWk_z p P α (P.ramificationIdx ℤ)) = 0 := by
      rw [hztop]
      exact kpVal_unit p P 1
    rw [fϖWk_derivTerm_kpVal p P (by simpa [e] using he1) (by simpa [e] using hztop0)]
    rw [hz1]
    rw [kpVal_natCast_e p P]
    simp
  have hval_add : kpVal p P (t (P.ramificationIdx ℤ)) + 1
      = P.ramificationIdx ℤ * padicValNat p (P.ramificationIdx ℤ) + P.ramificationIdx ℤ := by
    rw [hval_top]
    have he1' : 1 ≤ P.ramificationIdx ℤ := Ideal.ramificationIdx_pos P ℤ
    omega
  -- assemble:
  change (∑ i ∈ Finset.Icc 1 (P.ramificationIdx ℤ), t i)
      ∉ (maximalIdeal (kpInt p P)) ^
          (P.ramificationIdx ℤ * padicValNat p (P.ramificationIdx ℤ) + P.ramificationIdx ℤ)
  rw [hsum_eq]
  rw [← hval_add]
  exact htop_s

end
end Submission.Vdw.LocalField
