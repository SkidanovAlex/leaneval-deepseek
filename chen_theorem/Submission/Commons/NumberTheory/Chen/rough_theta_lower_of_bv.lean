import Mathlib
import Submission.Commons.NumberTheory.Mertens.primeProduct_oneSubInvPred_log_tendsto_pos
import Submission.Commons.NumberTheory.Chen.twin_product_ratio

open Finset
open scoped BigOperators

namespace Commons.NumberTheory.Chen

noncomputable section

/-!
# `rough_theta_lower_of_bv` — the linear-sieve lower bound for shifted primes

Target (Chen's `p + 2` form, rough-prime step): for every `B`,

`T(x) := Σ_{p ≤ x prime, (p+2, ∏_{3 ≤ q ≤ ⌊x^{1/8}⌋} q) = 1} log p ≥ c·x/log x`.

This is the dimension-one linear sieve at sifting level `z = ⌊x^{1/8}⌋` with level of
distribution `D = √x/(log x)^B` (`s = log D/log z → 4 > 2`), fed by the
Bombieri–Vinogradov hypothesis `hBV`.

## Status of this file (everything below is PROVEN except `beta_sieve_deficit`)

Proven here:

* **β-sieve combinatorics** (β-sieve of Rosser–Iwaniec): `chainPair`/`Gp`/`Gm`, the
  decomposition lemmas `mem_Gp_iff`/`mem_Gm_iff`/`sum_Gm_decomp`/`sum_Gp_decomp`, support
  `chain_support` (`lprod c ≤ D`), `chain_primes`, the Buchstab identities
  `buchstab_sum`/`one_sub_buchstab`, the recursions `TmSum_rec`/`TpSum_rec`, and the
  **minorant/majorant property** `chain_sieve_bounds`:
  `TmSum β D Y n ≤ indP (eff D Y) n ≤ TpSum β D Y n`.
* **Mertens-type inputs**: `VLE`, `Vsieve`, `Vsieve_eq_VLE`, `Vsieve_factor_bounds`,
  `Vsieve_pos/le_one/mono`, `VLE_bounds`, `Vsieve_bounds` (two-sided `≍ 1/log`),
  `Vsieve_ratio_bound` (the `K`-hypothesis `Vsieve r ≤ K·Vsieve Y·log Y/log r`),
  `VLE_mul_split`, `sum_inv_prime_sub_one_le`.
* **Chain structure for the Bombieri–Vinogradov comparison**: `chain_prod_odd`,
  `chain_lprod_inj` (a squarefree number has at most one decreasing
  factorisation, so each modulus is counted once), `chain_err_le`.
* **The reduction** `chains_theta_sum` + `chain_err_le` + `sift_thresholds` +
  `log_rpow_eventually_le`: the target is *derived* from the main-term estimate
  `beta_sieve_deficit`, using `hBV` with `A = 4`, `Vsieve Y ≫ 1/log Y`, and
  `x/log⁴x = o(x/log x)`.

## The single remaining gap: `beta_sieve_deficit`

`∃ c₀ > 0, ∀ Y ≥ 3, ∀ D ≥ Y³,  c₀·Vsieve Y ≤ Σ_{c ∈ Gm 1 D Y} (-1)^{|c|}/φ(lprod c)`,
i.e. the main term of the fundamental lemma of the one-dimensional linear sieve
(Nathanson, *Additive Number Theory: the Classical Bases*, Ch. 9, after Iwaniec;
Friedlander–Iwaniec, *Opera de Cribro*, Ch. 11; explicit constants in Bordignon,
arXiv:2007.08774).  Note the deficit is only `≈ 0.02·Vsieve Y` at level `s = 4`, so any
`c₀ < 0.8` works; equivalently one needs `Vsieve Y − MeSum D Y ≤ (1 − c₀)·Vsieve Y`.

### Plan for the deficit bound (the `2`-step layer recursion)

For `D ≥ Y³` the deficit `W⁻(D,Y) := Vsieve Y − MeSum D Y` satisfies the *exact* recursion
`W⁻(D,Y) = Σ_{q₁>q₂<Y} a_{q₁}a_{q₂}·W⁻(D/(q₁q₂), q₂)` (`a_q = 1/(q−1)`), because at level
`≥ 3` the `A₁`/`A₂` boundary terms vanish.  (This step is already formalised below:
`MeSum_rec`/`MpSum_rec`/`Vsieve_rec`/`Wm_rec`/`Wp_rec` and then `Wm_two_step`/`Wm_two_step_pure`.)  Iterating gives `W⁻ = Σ_{k≥1} T_{2k}` with the
*finitely supported* layers

`T₂(D,Y) = Σ_{q₁q₂²>D, q₂<q₁<Y} a_{q₁}a_{q₂}V(q₂)`,
`T_{2k+2}(D,Y) = Σ_{q₁q₂²≤D, q₂<q₁<Y} a_{q₁}a_{q₂}T_{2k}(D/(q₁q₂), q₂)`.

Each layer is a sum of *positive* terms (no cancellation), and the plan is to prove, by
induction on `k`, a profile bound `T_{2k}(D,Y) ≤ A_k·Vsieve Y·h(log D/log Y)` with an
explicit decreasing `h` (e.g. `h(u) = min(1, exp(2−u))`), the recurrence
`A_{k+1} ≤ c·A_k` coming from the estimate
`Σ_{q₁>q₂<Y} a_{q₁}a_{q₂}V(q₂)h(log(D/(q₁q₂))/log q₂)
    ≲ K·Vsieve Y·(K/(ℓ h(ℓ)))∫_{ℓ−2}^∞(∫_v^∞h)/(v+1)dv·h(ℓ)`,
whose operator norm is `< 1` for `ℓ` in the relevant range (`≈ 0.65` at `ℓ = 3.9` for
`h(u) = min(1, e^{2−u})` and `K ≈ 1.01`).  The two necessary analytic ingredients are
* the `K`-hypothesis `Vsieve q/Vsieve Y ≤ K log Y/log q` (available, `Vsieve_ratio_bound`),
* an Abel-summation estimate for `Σ_{y<p<z} a_p·G(log p)` (`sum_inv_prime_sub_one_le`
  is the case `G ≡ 1`).

With `T₂ = 0` at level `≥ 3` this yields `MeSum ≥ c₀·Vsieve Y` with a comfortable margin.

### A refinement (sup-profile, `1`-function recursion)

Because the `2`-step recursion is an *identity* at level `≥ 3`, the ratio profile
`θ(ℓ) := sup{W⁻(D,Y)/Vsieve Y : log D/log Y ≥ ℓ}` satisfies the single-function inequality

`θ(ℓ) ≤ (K/ℓ)∫_{ℓ−2}^∞ F(v)/(v+1) dv`,   `F(v) = ∫_v^∞ θ`,

proved by strong induction on `Y` (the sub-states have `Y'' = q₂ < Y`).  With the
exponential ansatz `θ(u) = C·e^{−βu}` this reads `ℓ(ℓ−1)β² ≥ K e^{2β}` at `ℓ ≈ 3.9`,
and `θ(2) ≥ 1` forces `C ≥ e^{2β}`; e.g. `β = 2`, `K ≤ 1.05` gives `θ(3.9) ≈ 0.02`,
so `W⁻ ≤ 0.02·Vsieve Y`.  The catch is that the *crude* bound
`Σ_{q₂<q₁<Y} a_{q₁} θ(…) ≤ θ(max)·Σ a_{q₁}` diverges (it gives operator norm `≫ 1`);
one needs the genuine partial-summation (Abel/layer-cake) estimate
`Σ_{y<p≤z} a_p w(p) ≤ ∫_0^{w(z)} (log(log z/log y_t) + C) dt`
(`y_t` a threshold with `w ≤ t` below it), i.e. `sum_inv_prime_sub_one_le` for a
monotone weight — plus the `K`-hypothesis in the sharpened form `K(q) = 1 + o(1)`
for `q ≥ Y^{1/2}` (small `q` contribute negligibly, being damped by `θ`).
-/


/-- odd primes below `Y` -/
def oddPrimesLt (Y : ℕ) : Finset ℕ := (Finset.range Y).filter (fun q => q.Prime ∧ q ≠ 2)

def oddPrim (Y : ℕ) : ℕ := ∏ q ∈ oddPrimesLt Y, q

def Vsieve (Y : ℕ) : ℝ := ∏ q ∈ oddPrimesLt Y, (1 - (1:ℝ)/((q:ℝ)-1))

def SievePrime (Y q : ℕ) : Prop := q.Prime ∧ q ≠ 2 ∧ q < Y

lemma sievePrime_iff_mem (Y q : ℕ) : q ∈ oddPrimesLt Y ↔ SievePrime Y q := by
  simp only [oddPrimesLt, mem_filter, mem_range, SievePrime]; tauto

lemma prime_three_le {q : ℕ} (hq : q.Prime) (h2 : q ≠ 2) : 3 ≤ q := by
  have hodd : q % 2 = 1 := (hq.eq_two_or_odd).resolve_left h2
  have h := hq.two_le
  omega

/-- chain sets: `.1` = upper-bound chains `𝒟⁺`, `.2` = lower-bound chains `𝒟⁻` -/
def chainPair (β : ℝ) : ℝ → ℕ → Finset (List ℕ) × Finset (List ℕ)
  | D, Y =>
    let ps := oddPrimesLt Y
    (insert [] (ps.attach.biUnion (fun q => if (q.1:ℝ)^(β+1) ≤ D then
        ((chainPair β (D/q.1) q.1).2).image (fun l => q.1 :: l) else ∅)),
     insert [] (ps.attach.biUnion (fun q => if (q.1:ℝ) ≤ D then
        ((chainPair β (D/q.1) q.1).1).image (fun l => q.1 :: l) else ∅)))
  termination_by D Y => Y
  decreasing_by
    · exact Finset.mem_range.mp (Finset.mem_filter.mp q.2).1
    · exact Finset.mem_range.mp (Finset.mem_filter.mp q.2).1

def Gp (β D : ℝ) (Y : ℕ) : Finset (List ℕ) := (chainPair β D Y).1
def Gm (β D : ℝ) (Y : ℕ) : Finset (List ℕ) := (chainPair β D Y).2

lemma Gp_unfold (β D : ℝ) (Y : ℕ) :
    Gp β D Y = insert [] ((oddPrimesLt Y).attach.biUnion (fun q => if (q.1:ℝ)^(β+1) ≤ D then
      (Gm β (D/q.1) q.1).image (fun l => q.1 :: l) else ∅)) := by
  rw [Gp, chainPair.eq_1]; rfl

lemma Gm_unfold (β D : ℝ) (Y : ℕ) :
    Gm β D Y = insert [] ((oddPrimesLt Y).attach.biUnion (fun q => if (q.1:ℝ) ≤ D then
      (Gp β (D/q.1) q.1).image (fun l => q.1 :: l) else ∅)) := by
  rw [Gm, chainPair.eq_1]; rfl

lemma nil_mem_Gp (β D : ℝ) (Y : ℕ) : ([] : List ℕ) ∈ Gp β D Y := by
  rw [Gp_unfold]; exact mem_insert_self _ _
lemma nil_mem_Gm (β D : ℝ) (Y : ℕ) : ([] : List ℕ) ∈ Gm β D Y := by
  rw [Gm_unfold]; exact mem_insert_self _ _

lemma mem_Gp_iff {β D : ℝ} {Y : ℕ} {l : List ℕ} :
    l ∈ Gp β D Y ↔ l = [] ∨ ∃ q l', SievePrime Y q ∧ (q:ℝ)^(β+1) ≤ D ∧ l' ∈ Gm β (D/q) q ∧ l = q :: l' := by
  constructor
  · intro h
    rw [Gp_unfold] at h
    rcases mem_insert.mp h with h1 | h2
    · exact Or.inl h1
    · rcases mem_biUnion.mp h2 with ⟨q, hqmem, hqd⟩
      have hqs := (sievePrime_iff_mem Y q.1).mp q.2
      by_cases hqD : (q.1:ℝ)^(β+1) ≤ D
      · rw [if_pos hqD] at hqd
        rcases mem_image.mp hqd with ⟨l', hl', heq⟩
        exact Or.inr ⟨q.1, l', hqs, hqD, hl', heq.symm⟩
      · rw [if_neg hqD] at hqd; simp at hqd
  · intro h
    rcases h with h1 | ⟨q, l', hqs, hqD, hl', heq⟩
    · subst h1; exact nil_mem_Gp β D Y
    · subst heq
      rw [Gp_unfold]
      refine mem_insert_of_mem ?_
      obtain ⟨hqp, hq2, hqY⟩ := hqs
      refine mem_biUnion.mpr ⟨⟨q, (sievePrime_iff_mem Y q).mpr ⟨hqp, hq2, hqY⟩⟩, mem_attach _ _, ?_⟩
      simp only [Subtype.coe_mk, if_pos hqD]
      exact mem_image.mpr ⟨l', hl', rfl⟩

lemma mem_Gm_iff {β D : ℝ} {Y : ℕ} {l : List ℕ} :
    l ∈ Gm β D Y ↔ l = [] ∨ ∃ q l', SievePrime Y q ∧ (q:ℝ) ≤ D ∧ l' ∈ Gp β (D/q) q ∧ l = q :: l' := by
  constructor
  · intro h
    rw [Gm_unfold] at h
    rcases mem_insert.mp h with h1 | h2
    · exact Or.inl h1
    · rcases mem_biUnion.mp h2 with ⟨q, hqmem, hqd⟩
      have hqs := (sievePrime_iff_mem Y q.1).mp q.2
      by_cases hqD : (q.1:ℝ) ≤ D
      · rw [if_pos hqD] at hqd
        rcases mem_image.mp hqd with ⟨l', hl', heq⟩
        exact Or.inr ⟨q.1, l', hqs, hqD, hl', heq.symm⟩
      · rw [if_neg hqD] at hqd; simp at hqd
  · intro h
    rcases h with h1 | ⟨q, l', hqs, hqD, hl', heq⟩
    · subst h1; exact nil_mem_Gm β D Y
    · subst heq
      rw [Gm_unfold]
      refine mem_insert_of_mem ?_
      obtain ⟨hqp, hq2, hqY⟩ := hqs
      refine mem_biUnion.mpr ⟨⟨q, (sievePrime_iff_mem Y q).mpr ⟨hqp, hq2, hqY⟩⟩, mem_attach _ _, ?_⟩
      simp only [Subtype.coe_mk, if_pos hqD]
      exact mem_image.mpr ⟨l', hl', rfl⟩

/-- product of a chain -/
def lprod (l : List ℕ) : ℕ := l.prod

lemma lprod_cons (q : ℕ) (l : List ℕ) : lprod (q :: l) = q * lprod l := by
  simp [lprod]

lemma le_rpow_self {q β : ℝ} (hq : 1 ≤ q) (hβ : 0 ≤ β) : q ≤ q ^ (β+1) := by
  calc q = q ^ (1:ℝ) := (Real.rpow_one q).symm
    _ ≤ q ^ (β+1) := Real.rpow_le_rpow_of_exponent_le hq (by linarith)

/-- support: the product of an admissible chain is `≤ D` -/
lemma chain_support (β : ℝ) (hβ : 0 ≤ β) :
    ∀ Y : ℕ, ∀ D : ℝ, 1 ≤ D →
      (∀ l ∈ Gp β D Y, (lprod l : ℝ) ≤ D) ∧ (∀ l ∈ Gm β D Y, (lprod l : ℝ) ≤ D) := by
  intro Y
  induction Y using Nat.strong_induction_on with
  | h Y ih =>
    intro D hD
    constructor
    · intro l hl
      rcases (mem_Gp_iff.mp hl) with h1 | ⟨q, l', hqs, hqD, hl', rfl⟩
      · subst h1; simp [lprod]; exact_mod_cast hD
      · obtain ⟨hqp, hq2, hqY⟩ := hqs
        have hq3 : (3:ℝ) ≤ (q:ℝ) := by exact_mod_cast prime_three_le hqp hq2
        have hpow : (q:ℝ) ≤ (q:ℝ)^(β+1) := le_rpow_self (by linarith) hβ
        have hqleD : (q:ℝ) ≤ D := le_trans hpow hqD
        have hDq : (1:ℝ) ≤ D / (q:ℝ) := by
          rw [le_div_iff₀ (by linarith)]; linarith
        have hh := (ih q hqY (D/(q:ℝ)) hDq).2 l' hl'
        rw [lprod_cons]
        push_cast
        calc (q:ℝ) * (lprod l' : ℝ) ≤ (q:ℝ) * (D/(q:ℝ)) :=
              mul_le_mul_of_nonneg_left hh (by linarith)
          _ = D := by field_simp
    · intro l hl
      rcases (mem_Gm_iff.mp hl) with h1 | ⟨q, l', hqs, hqD, hl', rfl⟩
      · subst h1; simp [lprod]; exact_mod_cast hD
      · obtain ⟨hqp, hq2, hqY⟩ := hqs
        have hq3 : (3:ℝ) ≤ (q:ℝ) := by exact_mod_cast prime_three_le hqp hq2
        have hDq : (1:ℝ) ≤ D / (q:ℝ) := by
          rw [le_div_iff₀ (by linarith)]; linarith
        have hh := (ih q hqY (D/(q:ℝ)) hDq).1 l' hl'
        rw [lprod_cons]
        push_cast
        calc (q:ℝ) * (lprod l' : ℝ) ≤ (q:ℝ) * (D/(q:ℝ)) :=
              mul_le_mul_of_nonneg_left hh (by linarith)
          _ = D := by field_simp


lemma prime_dvd_finset_prod {ι : Type*} {p : ℕ} (hp : p.Prime) {s : Finset ι} {f : ι → ℕ}
    (h : p ∣ s.prod f) : ∃ i ∈ s, p ∣ f i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.prod_empty] at h
      exact absurd (Nat.dvd_one.mp h) hp.ne_one
  | insert a t ha ih =>
      rw [Finset.prod_insert ha] at h
      rcases hp.dvd_mul.mp h with h1 | h2
      · exact ⟨a, Finset.mem_insert_self a t, h1⟩
      · obtain ⟨i, hi, hi'⟩ := ih h2
        exact ⟨i, Finset.mem_insert_of_mem hi, hi'⟩

lemma prime_mem_oddPrimesLt_iff {Y p : ℕ} (hp : p.Prime) :
    p ∈ oddPrimesLt Y ↔ p ∣ oddPrim Y := by
  constructor
  · intro h
    exact Finset.dvd_prod_of_mem (fun q => q) h
  · intro h
    rw [oddPrim] at h
    obtain ⟨q, hq, hpq⟩ := prime_dvd_finset_prod hp h
    have hqp : q.Prime := ((sievePrime_iff_mem Y q).mp hq).1
    have hpq' : p = q := (Nat.prime_dvd_prime_iff_eq hp hqp).mp hpq
    rw [hpq']; exact hq

lemma coprime_oddPrim_iff {Y n : ℕ} :
    n.Coprime (oddPrim Y) ↔ ∀ q ∈ oddPrimesLt Y, ¬ q ∣ n := by
  rw [oddPrim, Nat.coprime_prod_right_iff]
  constructor
  · intro h q hq hqn
    have hqp : q.Prime := ((sievePrime_iff_mem Y q).mp hq).1
    exact hqp.ne_one ((h q hq).symm.eq_one_of_dvd hqn)
  · intro h q hq
    have hqp : q.Prime := ((sievePrime_iff_mem Y q).mp hq).1
    rw [Nat.coprime_comm, hqp.coprime_iff_not_dvd]
    exact h q hq

/-- Buchstab identity for the primorial. -/
lemma buchstab_sum {Y n : ℕ} :
    (∑ q ∈ oddPrimesLt Y, (if q ∣ n then (1:ℝ) else 0) *
        (if n.Coprime (oddPrim q) then 1 else 0))
      = (if n.Coprime (oddPrim Y) then 0 else 1) := by
  classical
  by_cases hcop : n.Coprime (oddPrim Y)
  · rw [if_pos hcop]
    refine Finset.sum_eq_zero (fun q hq => ?_)
    have : ¬ q ∣ n := (coprime_oddPrim_iff.mp hcop) q hq
    simp [this]
  · rw [if_neg hcop]
    set Sfil := (oddPrimesLt Y).filter (fun q => q ∣ n) with hS
    have hSiff : ∀ q : ℕ, q ∈ Sfil ↔ q ∈ oddPrimesLt Y ∧ q ∣ n := by
      intro q; rw [hS, mem_filter]
    have hne : Sfil.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      apply hcop
      rw [coprime_oddPrim_iff]
      intro q hq hqn
      have hmem : q ∈ Sfil := (hSiff q).mpr ⟨hq, hqn⟩
      rw [hempty] at hmem
      simp at hmem
    set q0 := Sfil.min' hne with hq0
    have hq0mem : q0 ∈ Sfil := Finset.min'_mem Sfil hne
    have hq0odd : q0 ∈ oddPrimesLt Y := ((hSiff q0).mp hq0mem).1
    have hq0dvd : q0 ∣ n := ((hSiff q0).mp hq0mem).2
    obtain ⟨hq0p, hq0ne2, hq0lt⟩ := (sievePrime_iff_mem Y q0).mp hq0odd
    have hmin : ∀ q ∈ oddPrimesLt Y, q < q0 → ¬ q ∣ n := by
      intro q hq hlt hdvd
      have hmem : q ∈ Sfil := (hSiff q).mpr ⟨hq, hdvd⟩
      have := Finset.min'_le Sfil q hmem
      omega
    have hcop0 : n.Coprime (oddPrim q0) := by
      rw [coprime_oddPrim_iff]
      intro q hq hqn
      obtain ⟨hqp, hqne2, hqlt⟩ := (sievePrime_iff_mem q0 q).mp hq
      have hmemY : q ∈ oddPrimesLt Y :=
        (sievePrime_iff_mem Y q).mpr ⟨hqp, hqne2, lt_trans hqlt hq0lt⟩
      exact hmin q hmemY hqlt hqn
    rw [Finset.sum_eq_single q0]
    · rw [if_pos hq0dvd, if_pos hcop0]; norm_num
    · intro q hq hne2
      by_cases hqn : q ∣ n
      · have hqgt : q0 < q := by
          have hmem : q ∈ Sfil := (hSiff q).mpr ⟨hq, hqn⟩
          have := Finset.min'_le Sfil q hmem
          omega
        have hnot : ¬ n.Coprime (oddPrim q) := by
          rw [coprime_oddPrim_iff]
          intro hcon
          have hmemq : q0 ∈ oddPrimesLt q :=
            (sievePrime_iff_mem q q0).mpr ⟨hq0p, hq0ne2, hqgt⟩
          exact hcon q0 hmemq hq0dvd
        simp [hqn, hnot]
      · simp [hqn]
    · intro hnotmem
      exact absurd hq0odd hnotmem


/-- structure: every element of a chain is an odd prime below the limit -/
lemma chain_primes (β : ℝ) :
    ∀ Y : ℕ, ∀ D : ℝ,
      (∀ l ∈ Gp β D Y, ∀ q ∈ l, SievePrime Y q) ∧ (∀ l ∈ Gm β D Y, ∀ q ∈ l, SievePrime Y q) := by
  intro Y
  induction Y using Nat.strong_induction_on with
  | h Y ih =>
    intro D
    constructor
    · intro l hl q hq
      rcases (mem_Gp_iff.mp hl) with h1 | ⟨q', l', hqs, hqD, hl', rfl⟩
      · rw [h1] at hq; exact absurd hq List.not_mem_nil
      · rcases List.mem_cons.mp hq with rfl | hq'
        · exact hqs
        · obtain ⟨h1, h2, h3⟩ := (ih q' hqs.2.2 (D/q') ).2 l' hl' q hq'
          exact ⟨h1, h2, lt_trans h3 hqs.2.2⟩
    · intro l hl q hq
      rcases (mem_Gm_iff.mp hl) with h1 | ⟨q', l', hqs, hqD, hl', rfl⟩
      · rw [h1] at hq; exact absurd hq List.not_mem_nil
      · rcases List.mem_cons.mp hq with rfl | hq'
        · exact hqs
        · obtain ⟨h1, h2, h3⟩ := (ih q' hqs.2.2 (D/q')).1 l' hl' q hq'
          exact ⟨h1, h2, lt_trans h3 hqs.2.2⟩

lemma prime_dvd_list_prod {p : ℕ} (hp : p.Prime) {l : List ℕ} (h : p ∣ l.prod) :
    ∃ a ∈ l, p ∣ a := by
  induction l with
  | nil => rw [List.prod_nil] at h; exact absurd (Nat.dvd_one.mp h) hp.ne_one
  | cons a t ih =>
      rw [List.prod_cons] at h
      rcases hp.dvd_mul.mp h with h1 | h2
      · exact ⟨a, List.mem_cons_self, h1⟩
      · obtain ⟨b, hb, hb'⟩ := ih h2
        exact ⟨b, List.mem_cons_of_mem a hb, hb'⟩

/-- the tail of a chain in `Gp β D Y` is coprime to its head -/
lemma not_head_dvd_lprod {β D' : ℝ} {q : ℕ} {l : List ℕ}
    (hl : l ∈ Gp β D' q) (hqp : q.Prime) : ¬ q ∣ lprod l := by
  intro hdvd
  rw [lprod] at hdvd
  obtain ⟨a, ha, hqa⟩ := prime_dvd_list_prod hqp hdvd
  have ha' := (chain_primes β q D').1 l hl a ha
  have : a = q := ((Nat.prime_dvd_prime_iff_eq hqp (ha'.1)).mp hqa).symm
  have := ha'.2.2
  omega

/-- `q * m ∣ n ↔ q ∣ n ∧ m ∣ n` when `q` and `m` are coprime -/
lemma mul_dvd_iff_of_coprime {q m n : ℕ} (h : q.Coprime m) :
    (q * m ∣ n) ↔ q ∣ n ∧ m ∣ n := by
  constructor
  · intro hd
    exact ⟨dvd_trans (Nat.dvd_mul_right q m) hd, dvd_trans (Nat.dvd_mul_left m q) hd⟩
  · intro ⟨h1, h2⟩
    exact h.mul_dvd_of_dvd_of_dvd h1 h2

lemma coprime_of_not_dvd_lprod {q : ℕ} (hqp : q.Prime) {l : List ℕ}
    (h : ¬ q ∣ lprod l) : q.Coprime (lprod l) :=
  (hqp.coprime_iff_not_dvd).mpr h


lemma sum_Gm_decomp (F : List ℕ → ℝ) (β D : ℝ) (Y : ℕ) :
    (Gm β D Y).sum F
      = F [] + ∑ q ∈ oddPrimesLt Y,
          (if (q:ℝ) ≤ D then (Gp β (D/q) q).sum (fun l => F (q :: l)) else 0) := by
  have hconv : (oddPrimesLt Y).attach.biUnion (fun q =>
        if (q.1:ℝ) ≤ D then (Gp β (D/q.1) q.1).image (fun l => q.1 :: l) else ∅)
      = (oddPrimesLt Y).biUnion (fun q =>
        if (q:ℝ) ≤ D then (Gp β (D/q) q).image (fun l => q :: l) else ∅) :=
    Finset.attach_biUnion (s := oddPrimesLt Y)
      (f := fun q => if (q:ℝ) ≤ D then (Gp β (D/q) q).image (fun l => q :: l) else ∅)
  have hnil : ([] : List ℕ) ∉ (oddPrimesLt Y).biUnion (fun q =>
        if (q:ℝ) ≤ D then (Gp β (D/q) q).image (fun l => q :: l) else ∅) := by
    rw [Finset.mem_biUnion]
    rintro ⟨q, -, hq⟩
    by_cases hqD : (q:ℝ) ≤ D
    · rw [if_pos hqD] at hq
      obtain ⟨l, -, hl⟩ := Finset.mem_image.mp hq
      exact List.cons_ne_nil q l hl
    · rw [if_neg hqD] at hq; simp at hq
  have hdisj : (↑(oddPrimesLt Y) : Set ℕ).PairwiseDisjoint
      (fun q => if (q:ℝ) ≤ D then (Gp β (D/q) q).image (fun l => q :: l) else ∅) := by
    rw [Finset.pairwiseDisjoint_iff]
    intro i hi j hj hint
    by_cases hiD : (i:ℝ) ≤ D
    · by_cases hjD : (j:ℝ) ≤ D
      · rw [if_pos hiD, if_pos hjD] at hint
        obtain ⟨x, hx⟩ := hint
        rw [Finset.mem_inter] at hx
        obtain ⟨hx1, hx2⟩ := hx
        obtain ⟨l, -, hl⟩ := Finset.mem_image.mp hx1
        obtain ⟨l', -, hl'⟩ := Finset.mem_image.mp hx2
        exact (List.cons.inj (hl.trans hl'.symm)).1
      · rw [if_neg hjD] at hint
        obtain ⟨x, hx⟩ := hint
        rw [Finset.mem_inter] at hx
        exact absurd hx.2 (by simp)
    · rw [if_neg hiD] at hint
      obtain ⟨x, hx⟩ := hint
      rw [Finset.mem_inter] at hx
      exact absurd hx.1 (by simp)
  have hterm : ∀ q ∈ oddPrimesLt Y,
      ((if (q:ℝ) ≤ D then (Gp β (D/q) q).image (fun l => q :: l) else ∅)).sum F
        = (if (q:ℝ) ≤ D then (Gp β (D/q) q).sum (fun l => F (q :: l)) else 0) := by
    intro q hq
    by_cases hqD : (q:ℝ) ≤ D
    · rw [if_pos hqD, if_pos hqD]
      exact Finset.sum_image (f := F) (g := fun l : List ℕ => q :: l) (fun a _ b _ hab => (List.cons.inj hab).2)
    · rw [if_neg hqD, if_neg hqD]; simp
  rw [Gm_unfold, hconv, Finset.sum_insert hnil, Finset.sum_biUnion hdisj,
    Finset.sum_congr rfl hterm]

lemma sum_Gp_decomp (F : List ℕ → ℝ) (β D : ℝ) (Y : ℕ) :
    (Gp β D Y).sum F
      = F [] + ∑ q ∈ oddPrimesLt Y,
          (if (q:ℝ)^(β+1) ≤ D then (Gm β (D/q) q).sum (fun l => F (q :: l)) else 0) := by
  have hconv : (oddPrimesLt Y).attach.biUnion (fun q =>
        if (q.1:ℝ)^(β+1) ≤ D then (Gm β (D/q.1) q.1).image (fun l => q.1 :: l) else ∅)
      = (oddPrimesLt Y).biUnion (fun q =>
        if (q:ℝ)^(β+1) ≤ D then (Gm β (D/q) q).image (fun l => q :: l) else ∅) :=
    Finset.attach_biUnion (s := oddPrimesLt Y)
      (f := fun q => if (q:ℝ)^(β+1) ≤ D then (Gm β (D/q) q).image (fun l => q :: l) else ∅)
  have hnil : ([] : List ℕ) ∉ (oddPrimesLt Y).biUnion (fun q =>
        if (q:ℝ)^(β+1) ≤ D then (Gm β (D/q) q).image (fun l => q :: l) else ∅) := by
    rw [Finset.mem_biUnion]
    rintro ⟨q, -, hq⟩
    by_cases hqD : (q:ℝ)^(β+1) ≤ D
    · rw [if_pos hqD] at hq
      obtain ⟨l, -, hl⟩ := Finset.mem_image.mp hq
      exact List.cons_ne_nil q l hl
    · rw [if_neg hqD] at hq; simp at hq
  have hdisj : (↑(oddPrimesLt Y) : Set ℕ).PairwiseDisjoint
      (fun q => if (q:ℝ)^(β+1) ≤ D then (Gm β (D/q) q).image (fun l => q :: l) else ∅) := by
    rw [Finset.pairwiseDisjoint_iff]
    intro i hi j hj hint
    by_cases hiD : (i:ℝ)^(β+1) ≤ D
    · by_cases hjD : (j:ℝ)^(β+1) ≤ D
      · rw [if_pos hiD, if_pos hjD] at hint
        obtain ⟨x, hx⟩ := hint
        rw [Finset.mem_inter] at hx
        obtain ⟨hx1, hx2⟩ := hx
        obtain ⟨l, -, hl⟩ := Finset.mem_image.mp hx1
        obtain ⟨l', -, hl'⟩ := Finset.mem_image.mp hx2
        exact (List.cons.inj (hl.trans hl'.symm)).1
      · rw [if_neg hjD] at hint
        obtain ⟨x, hx⟩ := hint
        rw [Finset.mem_inter] at hx
        exact absurd hx.2 (by simp)
    · rw [if_neg hiD] at hint
      obtain ⟨x, hx⟩ := hint
      rw [Finset.mem_inter] at hx
      exact absurd hx.1 (by simp)
  have hterm : ∀ q ∈ oddPrimesLt Y,
      ((if (q:ℝ)^(β+1) ≤ D then (Gm β (D/q) q).image (fun l => q :: l) else ∅)).sum F
        = (if (q:ℝ)^(β+1) ≤ D then (Gm β (D/q) q).sum (fun l => F (q :: l)) else 0) := by
    intro q hq
    by_cases hqD : (q:ℝ)^(β+1) ≤ D
    · rw [if_pos hqD, if_pos hqD]
      exact Finset.sum_image (f := F) (g := fun l : List ℕ => q :: l) (fun a _ b _ hab => (List.cons.inj hab).2)
    · rw [if_neg hqD, if_neg hqD]; simp
  rw [Gp_unfold, hconv, Finset.sum_insert hnil, Finset.sum_biUnion hdisj,
    Finset.sum_congr rfl hterm]


/-- the indicator of coprimality with the odd primorial -/
def indP (Y n : ℕ) : ℝ := if n.Coprime (oddPrim Y) then 1 else 0

/-- the "effective limit": primes above `D` cannot occur in a chain anyway -/
def eff (D : ℝ) (Y : ℕ) : ℕ := min Y (⌊D⌋₊ + 1)

lemma oddPrim_dvd_of_le {Y₁ Y₂ : ℕ} (h : Y₁ ≤ Y₂) : oddPrim Y₁ ∣ oddPrim Y₂ := by
  apply Finset.prod_dvd_prod_of_subset
  intro q hq
  rw [sievePrime_iff_mem] at hq ⊢
  exact ⟨hq.1, hq.2.1, lt_of_lt_of_le hq.2.2 h⟩

lemma indP_anti {Y₁ Y₂ n : ℕ} (h : Y₁ ≤ Y₂) : indP Y₂ n ≤ indP Y₁ n := by
  unfold indP
  by_cases hc : n.Coprime (oddPrim Y₂)
  · rw [if_pos hc]
    have : n.Coprime (oddPrim Y₁) := Nat.Coprime.coprime_dvd_right (oddPrim_dvd_of_le h) hc
    rw [if_pos this]
  · rw [if_neg hc]
    split <;> norm_num

lemma oddPrimesLt_eff (D : ℝ) (hD : 0 ≤ D) (Y : ℕ) :
    oddPrimesLt (eff D Y) = (oddPrimesLt Y).filter (fun q : ℕ => (q:ℝ) ≤ D) := by
  ext q
  rw [oddPrimesLt, mem_filter, mem_range, oddPrimesLt, mem_filter, mem_filter, mem_range]
  unfold eff
  constructor
  · rintro ⟨h1, h2, h3⟩
    have h4 : q ≤ ⌊D⌋₊ := by
      have h5 : q < ⌊D⌋₊ + 1 := lt_of_lt_of_le h1 (min_le_right _ _)
      omega
    exact ⟨⟨lt_of_lt_of_le h1 (min_le_left _ _), h2, h3⟩, by
      have h6 : (q:ℝ) ≤ (⌊D⌋₊ : ℝ) := by exact_mod_cast h4
      linarith [Nat.floor_le hD]⟩
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    have h5 : q ≤ ⌊D⌋₊ := Nat.le_floor (by exact_mod_cast h4)
    exact ⟨lt_min h1 (by omega), h2, h3⟩


def TmSum (β D : ℝ) (Y n : ℕ) : ℝ :=
  (Gm β D Y).sum (fun c => (-1:ℝ)^c.length * (if lprod c ∣ n then 1 else 0))

def TpSum (β D : ℝ) (Y n : ℕ) : ℝ :=
  (Gp β D Y).sum (fun c => (-1:ℝ)^c.length * (if lprod c ∣ n then 1 else 0))

lemma not_dvd_lprod_of {q : ℕ} (hqp : q.Prime) {l : List ℕ}
    (hl : ∀ p ∈ l, p.Prime ∧ p < q) : ¬ q ∣ lprod l := by
  intro hdvd
  rw [lprod] at hdvd
  obtain ⟨a, ha, hqa⟩ := prime_dvd_list_prod hqp hdvd
  have hpa := hl a ha
  have : a = q := ((Nat.prime_dvd_prime_iff_eq hqp hpa.1).mp hqa).symm
  omega

/-- peeling the head of a chain: the tail sum factorises -/
lemma tail_sum_gen {q n : ℕ} (hqp : q.Prime) (L : Finset (List ℕ))
    (hL : ∀ l ∈ L, ∀ p ∈ l, p.Prime ∧ p < q) :
    L.sum (fun l => (-1:ℝ)^(q :: l).length * (if lprod (q :: l) ∣ n then 1 else 0))
      = -((if q ∣ n then 1 else 0) *
          L.sum (fun l => (-1:ℝ)^l.length * (if lprod l ∣ n then 1 else 0))) := by
  have hstep : ∀ l ∈ L,
      (-1:ℝ)^(q :: l).length * (if lprod (q :: l) ∣ n then 1 else 0)
        = -((if q ∣ n then 1 else 0) * ((-1:ℝ)^l.length * (if lprod l ∣ n then 1 else 0))) := by
    intro l hl
    have hcop : q.Coprime (lprod l) := (hqp.coprime_iff_not_dvd).mpr (not_dvd_lprod_of hqp (hL l hl))
    rw [List.length_cons, lprod_cons, pow_succ]
    have hiff : (q * lprod l ∣ n) ↔ (q ∣ n ∧ lprod l ∣ n) := mul_dvd_iff_of_coprime hcop
    by_cases h1 : q ∣ n <;> by_cases h2 : lprod l ∣ n <;> simp [hiff, h1, h2]
  rw [Finset.sum_congr rfl hstep, Finset.sum_neg_distrib, Finset.mul_sum]

lemma TmSum_rec (β D : ℝ) (Y n : ℕ) :
    TmSum β D Y n = 1 + ∑ q ∈ oddPrimesLt Y,
      (if (q:ℝ) ≤ D then -((if q ∣ n then 1 else 0) * TpSum β (D/q) q n) else 0) := by
  have hfirst : (-1:ℝ)^([] : List ℕ).length * (if lprod ([] : List ℕ) ∣ n then 1 else 0) = 1 := by
    simp [lprod]
  rw [TmSum, sum_Gm_decomp, hfirst]
  congr 1
  refine Finset.sum_congr rfl (fun q hq => ?_)
  have hqp : q.Prime := ((sievePrime_iff_mem Y q).mp hq).1
  have hL : ∀ l ∈ Gp β (D/q) q, ∀ p ∈ l, p.Prime ∧ p < q := by
    intro l hl p hp
    have hh := (chain_primes β q (D/q)).1 l hl p hp
    exact ⟨hh.1, hh.2.2⟩
  by_cases hqD : (q:ℝ) ≤ D
  · rw [if_pos hqD, if_pos hqD]
    exact tail_sum_gen hqp _ hL
  · rw [if_neg hqD, if_neg hqD]

lemma TpSum_rec (β D : ℝ) (Y n : ℕ) :
    TpSum β D Y n = 1 + ∑ q ∈ oddPrimesLt Y,
      (if (q:ℝ)^(β+1) ≤ D then -((if q ∣ n then 1 else 0) * TmSum β (D/q) q n) else 0) := by
  have hfirst : (-1:ℝ)^([] : List ℕ).length * (if lprod ([] : List ℕ) ∣ n then 1 else 0) = 1 := by
    simp [lprod]
  rw [TpSum, sum_Gp_decomp, hfirst]
  congr 1
  refine Finset.sum_congr rfl (fun q hq => ?_)
  have hqp : q.Prime := ((sievePrime_iff_mem Y q).mp hq).1
  have hL : ∀ l ∈ Gm β (D/q) q, ∀ p ∈ l, p.Prime ∧ p < q := by
    intro l hl p hp
    have hh := (chain_primes β q (D/q)).2 l hl p hp
    exact ⟨hh.1, hh.2.2⟩
  by_cases hqD : (q:ℝ)^(β+1) ≤ D
  · rw [if_pos hqD, if_pos hqD]
    exact tail_sum_gen hqp _ hL
  · rw [if_neg hqD, if_neg hqD]


/-- the Buchstab sum rewritten: `1 - Σ = indP` -/
lemma one_sub_buchstab (Y n : ℕ) :
    (1:ℝ) - ∑ q ∈ oddPrimesLt Y, (if q ∣ n then 1 else 0) *
        (if n.Coprime (oddPrim q) then (1:ℝ) else 0) = indP Y n := by
  rw [buchstab_sum, indP]
  by_cases hc : n.Coprime (oddPrim Y)
  · rw [if_pos hc, if_pos hc]; norm_num
  · rw [if_neg hc, if_neg hc]; norm_num

lemma sum_if_le_eq (D : ℝ) (hD : 0 ≤ D) (Y n : ℕ) :
    (∑ q ∈ oddPrimesLt Y, (if (q:ℝ) ≤ D then (if q ∣ n then 1 else 0) * indP q n else 0))
      = ∑ q ∈ oddPrimesLt (eff D Y), (if q ∣ n then 1 else 0) *
          (if n.Coprime (oddPrim q) then (1:ℝ) else 0) := by
  rw [oddPrimesLt_eff D hD Y, ← Finset.sum_filter]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  rw [Finset.mem_filter] at hq
  rfl

lemma prime_one_le {Y q : ℕ} (hq : q ∈ oddPrimesLt Y) : (1:ℝ) ≤ (q:ℝ) := by
  have h := ((sievePrime_iff_mem Y q).mp hq).1.two_le
  exact_mod_cast (by omega : (1:ℕ) ≤ q)

lemma chain_sieve_bounds (β : ℝ) (hβ : 1 ≤ β) :
    ∀ Y : ℕ, ∀ D : ℝ, 0 ≤ D → ∀ n : ℕ,
      TmSum β D Y n ≤ indP (eff D Y) n ∧ indP (eff D Y) n ≤ TpSum β D Y n := by
  intro Y
  induction Y using Nat.strong_induction_on with
  | h Y ih =>
    intro D hD n
    have hDq : ∀ q : ℕ, 0 ≤ D/q := fun q => div_nonneg hD (by positivity)
    have hanti : ∀ q : ℕ, indP q n ≤ indP (eff (D/q) q) n := fun q =>
      indP_anti (Y₁ := eff (D/q) q) (Y₂ := q) (n := n) (min_le_left q (⌊D/q⌋₊ + 1))
    have hnil : ∑ q ∈ oddPrimesLt Y,
          (if (q:ℝ) ≤ D then (if q ∣ n then 1 else 0) * indP q n else 0)
        = ∑ q ∈ oddPrimesLt (eff D Y), (if q ∣ n then 1 else 0) *
            (if n.Coprime (oddPrim q) then (1:ℝ) else 0) := sum_if_le_eq D hD Y n
    constructor
    · -- ===== Tm is a minorant =====
      have key : TmSum β D Y n
          = 1 - ∑ q ∈ oddPrimesLt Y,
              (if (q:ℝ) ≤ D then (if q ∣ n then 1 else 0) * TpSum β (D/q) q n else 0) := by
        rw [TmSum_rec]
        congr 1
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl (fun q hq => ?_)
        by_cases hqD : (q:ℝ) ≤ D <;> simp [hqD]
      have hA : ∑ q ∈ oddPrimesLt Y,
              (if (q:ℝ) ≤ D then (if q ∣ n then 1 else 0) * indP (eff (D/q) q) n else 0)
          ≤ ∑ q ∈ oddPrimesLt Y,
              (if (q:ℝ) ≤ D then (if q ∣ n then 1 else 0) * TpSum β (D/q) q n else 0) := by
        refine Finset.sum_le_sum (fun q hq => ?_)
        have hqlt : q < Y := ((sievePrime_iff_mem Y q).mp hq).2.2
        have hIH := (ih q hqlt (D/q) (hDq q) n).2
        by_cases hqD : (q:ℝ) ≤ D
        · rw [if_pos hqD, if_pos hqD]
          exact mul_le_mul_of_nonneg_left hIH (by split <;> norm_num)
        · rw [if_neg hqD, if_neg hqD]
      have hB : ∑ q ∈ oddPrimesLt Y,
              (if (q:ℝ) ≤ D then (if q ∣ n then 1 else 0) * indP q n else 0)
          ≤ ∑ q ∈ oddPrimesLt Y,
              (if (q:ℝ) ≤ D then (if q ∣ n then 1 else 0) * indP (eff (D/q) q) n else 0) := by
        refine Finset.sum_le_sum (fun q hq => ?_)
        by_cases hqD : (q:ℝ) ≤ D
        · rw [if_pos hqD, if_pos hqD]
          exact mul_le_mul_of_nonneg_left (hanti q) (by split <;> norm_num)
        · rw [if_neg hqD, if_neg hqD]
      rw [key]
      have h1 : (1:ℝ) - ∑ q ∈ oddPrimesLt Y,
              (if (q:ℝ) ≤ D then (if q ∣ n then 1 else 0) * TpSum β (D/q) q n else 0)
          ≤ 1 - ∑ q ∈ oddPrimesLt Y,
              (if (q:ℝ) ≤ D then (if q ∣ n then 1 else 0) * indP (eff (D/q) q) n else 0) := by
        linarith [hA]
      have h2 : (1:ℝ) - ∑ q ∈ oddPrimesLt Y,
              (if (q:ℝ) ≤ D then (if q ∣ n then 1 else 0) * indP (eff (D/q) q) n else 0)
          ≤ indP (eff D Y) n := by
        rw [hnil] at hB
        rw [← one_sub_buchstab (eff D Y) n]
        linarith [hB]
      linarith [h1, h2]
    · -- ===== Tp is a majorant =====
      have key : TpSum β D Y n
          = 1 - ∑ q ∈ oddPrimesLt Y,
              (if (q:ℝ)^(β+1) ≤ D then (if q ∣ n then 1 else 0) * TmSum β (D/q) q n else 0) := by
        rw [TpSum_rec]
        congr 1
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl (fun q hq => ?_)
        by_cases hqD : (q:ℝ)^(β+1) ≤ D <;> simp [hqD]
      have hA : ∑ q ∈ oddPrimesLt Y,
              (if (q:ℝ)^(β+1) ≤ D then (if q ∣ n then 1 else 0) * TmSum β (D/q) q n else 0)
          ≤ ∑ q ∈ oddPrimesLt Y,
              (if (q:ℝ)^(β+1) ≤ D then (if q ∣ n then 1 else 0) * indP (eff (D/q) q) n else 0) := by
        refine Finset.sum_le_sum (fun q hq => ?_)
        have hqlt : q < Y := ((sievePrime_iff_mem Y q).mp hq).2.2
        have hIH := (ih q hqlt (D/q) (hDq q) n).1
        by_cases hqD : (q:ℝ)^(β+1) ≤ D
        · rw [if_pos hqD, if_pos hqD]
          exact mul_le_mul_of_nonneg_left hIH (by split <;> norm_num)
        · rw [if_neg hqD, if_neg hqD]
      have hEq : ∑ q ∈ oddPrimesLt Y,
              (if (q:ℝ)^(β+1) ≤ D then (if q ∣ n then 1 else 0) * indP (eff (D/q) q) n else 0)
          = ∑ q ∈ oddPrimesLt Y,
              (if (q:ℝ)^(β+1) ≤ D then (if q ∣ n then 1 else 0) * indP q n else 0) := by
        refine Finset.sum_congr rfl (fun q hq => ?_)
        by_cases hqD : (q:ℝ)^(β+1) ≤ D
        · rw [if_pos hqD, if_pos hqD]
          have hq1 : (1:ℝ) ≤ (q:ℝ) := prime_one_le hq
          have hq2 : (q:ℝ)^2 ≤ D := by
            have h1 : (q:ℝ)^((2:ℕ):ℝ) ≤ (q:ℝ)^(β+1) :=
              Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num; linarith [hβ])
            have h1' : (q:ℝ)^2 ≤ (q:ℝ)^(β+1) := by simpa using h1
            exact le_trans h1' hqD
          have heff : eff (D/q) q = q := by
            unfold eff
            have hle : (q:ℝ) ≤ D/q := by
              rw [le_div_iff₀ (by linarith)]; nlinarith [hq2]
            have hq' : q ≤ ⌊D/q⌋₊ := Nat.le_floor hle
            omega
          rw [heff]
        · rw [if_neg hqD, if_neg hqD]
      have hB : ∑ q ∈ oddPrimesLt Y,
              (if (q:ℝ)^(β+1) ≤ D then (if q ∣ n then 1 else 0) * indP q n else 0)
          ≤ ∑ q ∈ oddPrimesLt Y,
              (if (q:ℝ) ≤ D then (if q ∣ n then 1 else 0) * indP q n else 0) := by
        refine Finset.sum_le_sum (fun q hq => ?_)
        by_cases h1 : (q:ℝ)^(β+1) ≤ D
        · have hle : (q:ℝ) ≤ D :=
            le_trans (le_rpow_self (prime_one_le hq) (by linarith)) h1
          rw [if_pos h1, if_pos hle]
        · rw [if_neg h1]
          by_cases h2 : (q:ℝ) ≤ D
          · rw [if_pos h2]
            have h0 : 0 ≤ (if q ∣ n then 1 else 0) * indP q n :=
              mul_nonneg (by split <;> norm_num) (by unfold indP; split <;> norm_num)
            linarith
          · rw [if_neg h2]
      rw [key]
      have h1 : (1:ℝ) - ∑ q ∈ oddPrimesLt Y,
              (if (q:ℝ)^(β+1) ≤ D then (if q ∣ n then 1 else 0) * indP q n else 0)
          ≤ TpSum β D Y n := by
        linarith [hEq ▸ hA]
      have h2 : indP (eff D Y) n ≤ (1:ℝ) - ∑ q ∈ oddPrimesLt Y,
              (if (q:ℝ)^(β+1) ≤ D then (if q ∣ n then 1 else 0) * indP q n else 0) := by
        rw [hnil] at hB
        rw [← one_sub_buchstab (eff D Y) n]
        linarith [hB]
      linarith [h1, h2]

------ The remaining analytic input (main term of the fundamental lemma) ------



/-! ### Mertens-type inputs (from `twin_product_ratio`) -/

/-- the product over odd primes `≤ n`, matching the form of `twin_product_ratio` -/
def VLE (n : ℕ) : ℝ :=
  ∏ p ∈ (Nat.primesLE n).filter (fun p => p ≠ 2), (1 - (1:ℝ)/((p:ℝ)-1))

/-- each factor `1 - 1/(p-1)` for an odd prime lies in `(0,1]` -/
lemma Vsieve_factor_bounds {p : ℕ} (hpp : p.Prime) (hp2 : p ≠ 2) :
    0 < 1 - (1:ℝ)/((p:ℝ)-1) ∧ 1 - (1:ℝ)/((p:ℝ)-1) ≤ 1 := by
  have h3 : 3 ≤ p := prime_three_le hpp hp2
  have h3r : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast h3
  have hpos : (0:ℝ) < (p:ℝ) - 1 := by linarith
  have hnn : (0:ℝ) ≤ 1/((p:ℝ) - 1) := by positivity
  constructor
  · rw [sub_pos, div_lt_one hpos]; linarith
  · exact sub_le_self _ hnn

lemma Vsieve_eq_VLE (Y : ℕ) : Vsieve Y = VLE (Y - 1) := by
  unfold Vsieve VLE
  congr 1
  ext p
  simp only [oddPrimesLt, Finset.mem_filter, Finset.mem_range, Nat.mem_primesLE]
  constructor
  · rintro ⟨hp, hpp, hp2⟩
    exact ⟨⟨by omega, hpp⟩, hp2⟩
  · rintro ⟨⟨hle, hpp⟩, hp2⟩
    have h2 := hpp.two_le
    exact ⟨by omega, hpp, hp2⟩

lemma Vsieve_pos (Y : ℕ) : 0 < Vsieve Y := by
  unfold Vsieve
  refine Finset.prod_pos (fun p hp => ?_)
  obtain ⟨_, hpp, hp2⟩ := Finset.mem_filter.mp hp
  exact (Vsieve_factor_bounds hpp hp2).1

lemma Vsieve_le_one (Y : ℕ) : Vsieve Y ≤ 1 := by
  unfold Vsieve
  refine Finset.prod_le_one₀ (fun p hp => ?_) (fun p hp => ?_)
  · obtain ⟨_, hpp, hp2⟩ := Finset.mem_filter.mp hp
    exact (Vsieve_factor_bounds hpp hp2).1.le
  · obtain ⟨_, hpp, hp2⟩ := Finset.mem_filter.mp hp
    exact (Vsieve_factor_bounds hpp hp2).2

lemma Vsieve_mono {a b : ℕ} (h : a ≤ b) : Vsieve b ≤ Vsieve a := by
  unfold Vsieve
  refine Finset.prod_le_prod_of_subset_of_le_one₀ (fun p hp => ?_) (fun p hp => ?_)
    (fun p hp _ => ?_)
  · obtain ⟨hp', hpp, hp2⟩ := Finset.mem_filter.mp hp
    simp only [oddPrimesLt, Finset.mem_filter, Finset.mem_range]
    have hpa : p < a := Finset.mem_range.mp hp'
    exact ⟨by omega, hpp, hp2⟩
  · obtain ⟨_, hpp, hp2⟩ := Finset.mem_filter.mp hp
    exact (Vsieve_factor_bounds hpp hp2).1.le
  · obtain ⟨_, hpp, hp2⟩ := Finset.mem_filter.mp hp
    exact (Vsieve_factor_bounds hpp hp2).2

/-- two-sided Mertens bound for `VLE` (from `twin_product_ratio`) -/
lemma VLE_bounds : ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ n : ℕ, 3 ≤ n →
    c / Real.log (n:ℝ) ≤ VLE n ∧ VLE n ≤ C / Real.log (n:ℝ) := by
  obtain ⟨c, C, hc, hcC, h⟩ := twin_product_ratio
  refine ⟨c, C, hc, hcC, fun n hn => ?_⟩
  have hz : 3 ≤ (n:ℝ) := by exact_mod_cast hn
  have h1 := h (n:ℝ) hz
  rwa [Nat.floor_natCast] at h1

/-- two-sided Mertens bound for `Vsieve` -/
lemma Vsieve_bounds : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ Y : ℕ, 4 ≤ Y →
    c / Real.log (Y:ℝ) ≤ Vsieve Y ∧ Vsieve Y ≤ C / Real.log (Y:ℝ) := by
  obtain ⟨c, C, hc, hcC, h⟩ := VLE_bounds
  refine ⟨c, 2*C, hc, by linarith, fun Y hY => ?_⟩
  rw [Vsieve_eq_VLE]
  have hY' : 3 ≤ Y - 1 := by omega
  obtain ⟨h1, h2⟩ := h (Y - 1) hY'
  have hY1 : (1:ℝ) < (Y:ℝ) := by exact_mod_cast (by omega : 1 < Y)
  have hYm : ((Y-1:ℕ):ℝ) = (Y:ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ Y)]; norm_num
  have hYm1 : (1:ℝ) < ((Y-1:ℕ):ℝ) := by exact_mod_cast (by omega : 1 < Y - 1)
  have h0 : (0:ℝ) < Real.log (Y:ℝ) := Real.log_pos hY1
  have h0' : (0:ℝ) < Real.log (((Y-1:ℕ):ℝ)) := Real.log_pos hYm1
  have hler : Real.log (((Y-1:ℕ):ℝ)) ≤ Real.log (Y:ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast (by omega : Y - 1 ≤ Y))
  constructor
  · calc c / Real.log (Y:ℝ) ≤ c / Real.log (((Y-1:ℕ):ℝ)) := by
          rw [div_le_div_iff₀ h0 h0']
          nlinarith [hler, hc]
      _ ≤ VLE (Y - 1) := h1
  · -- `log Y ≤ 2 log (Y-1)` for `Y ≥ 4`
    have hsplit : Real.log (Y:ℝ) = Real.log (((Y-1:ℕ):ℝ)) +
        Real.log ((Y:ℝ)/((Y-1:ℕ):ℝ)) := by
      rw [← Real.log_mul (by positivity) (by positivity), mul_div_cancel₀]
      exact_mod_cast (by omega : (Y-1:ℕ) ≠ 0)
    have hratio : Real.log ((Y:ℝ)/((Y-1:ℕ):ℝ)) ≤ Real.log (((Y-1:ℕ):ℝ)) := by
      refine Real.log_le_log (by positivity) ?_
      calc (Y:ℝ)/((Y-1:ℕ):ℝ) ≤ 2 := by
            rw [div_le_iff₀ (by positivity)]; rw [hYm]; linarith
        _ ≤ ((Y-1:ℕ):ℝ) := by exact_mod_cast (by omega : 2 ≤ Y - 1)
    have h2log : Real.log (Y:ℝ) ≤ 2 * Real.log (((Y-1:ℕ):ℝ)) := by rw [hsplit]; linarith
    have hstep : C / Real.log (((Y-1:ℕ):ℝ)) ≤ 2 * C / Real.log (Y:ℝ) := by
      rw [div_le_div_iff₀ h0' h0]
      nlinarith [h2log, hcC, hc]
    linarith [h2, hstep]

/-- **The `K`-hypothesis**: `Vsieve r ≤ K · Vsieve Y · (log Y / log r)`. -/
lemma Vsieve_ratio_bound : ∃ K : ℝ, 0 < K ∧ ∀ r Y : ℕ, 4 ≤ r → r ≤ Y →
    Vsieve r ≤ K * Vsieve Y * (Real.log (Y:ℝ) / Real.log (r:ℝ)) := by
  obtain ⟨c, C, hc, hC, h⟩ := Vsieve_bounds
  refine ⟨C/c, by positivity, fun r Y hr hrY => ?_⟩
  have hY : 4 ≤ Y := le_trans hr hrY
  obtain ⟨h1, h2⟩ := h r hr
  obtain ⟨h3, h4⟩ := h Y hY
  have hlY : (0:ℝ) < Real.log (Y:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < Y))
  have hlr : (0:ℝ) < Real.log (r:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < r))
  have hkey : C / Real.log (r:ℝ) =
      (C/c) * (Real.log (Y:ℝ)/Real.log (r:ℝ)) * (c/Real.log (Y:ℝ)) := by
    field_simp
  have hnn : (0:ℝ) ≤ (C/c) * (Real.log (Y:ℝ)/Real.log (r:ℝ)) := by positivity
  calc Vsieve r ≤ C / Real.log (r:ℝ) := h2
    _ = (C/c) * (Real.log (Y:ℝ)/Real.log (r:ℝ)) * (c/Real.log (Y:ℝ)) := hkey
    _ ≤ (C/c) * (Real.log (Y:ℝ)/Real.log (r:ℝ)) * Vsieve Y :=
        mul_le_mul_of_nonneg_left h3 hnn
    _ = (C/c) * Vsieve Y * (Real.log (Y:ℝ)/Real.log (r:ℝ)) := by ring

/-- splitting the primorial product at `y` -/
lemma VLE_mul_split (y z : ℕ) (hyz : y ≤ z) :
    VLE z = VLE y * ∏ p ∈ ((Nat.primesLE z).filter (fun p => p ≠ 2)).filter (fun p => y < p),
        (1 - (1:ℝ)/((p:ℝ)-1)) := by
  unfold VLE
  have hsub : (Nat.primesLE y).filter (fun p => p ≠ 2) ⊆ (Nat.primesLE z).filter (fun p => p ≠ 2) := by
    intro p hp
    simp only [Finset.mem_filter] at hp ⊢
    exact ⟨Nat.primesLE_mono hyz hp.1, hp.2⟩
  have hset : (Nat.primesLE z).filter (fun p => p ≠ 2) \ (Nat.primesLE y).filter (fun p => p ≠ 2)
      = ((Nat.primesLE z).filter (fun p => p ≠ 2)).filter (fun p => y < p) := by
    ext p
    simp only [Finset.mem_sdiff, Finset.mem_filter, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨⟨hle, hpp⟩, hp2⟩, hnot⟩
      exact ⟨⟨⟨hle, hpp⟩, hp2⟩, by
        by_contra hc
        exact hnot ⟨⟨by omega, hpp⟩, hp2⟩⟩
    · rintro ⟨⟨⟨hle, hpp⟩, hp2⟩, hlt⟩
      exact ⟨⟨⟨hle, hpp⟩, hp2⟩, by rintro ⟨⟨hley, -⟩, -⟩; omega⟩
  rw [← Finset.prod_sdiff hsub, hset, mul_comm]

/-- **Reciprocal-prime-sum estimate on an interval.**  With `S` the odd primes in `(y,z]`:
termwise `1/(p-1) ≤ -log(1-1/(p-1))`, `Real.log_prod`, then `VLE z = VLE y · ∏_S(1-1/(p-1))`
(`VLE_mul_split`) and `VLE t ≍ 1/log t` (`VLE_bounds`). -/
lemma sum_inv_prime_sub_one_le (y z : ℕ) (hy : 3 ≤ y) (hyz : y ≤ z) :
    ∃ C : ℝ, 0 < C ∧
      (∑ p ∈ ((Nat.primesLE z).filter (fun p => p ≠ 2)).filter (fun p => y < p),
          (1:ℝ) / ((p:ℝ) - 1))
        ≤ Real.log (Real.log (z:ℝ) / Real.log (y:ℝ)) + C := by
  obtain ⟨c, C, hc, hC, hV⟩ := VLE_bounds
  have hz3 : 3 ≤ z := le_trans hy hyz
  obtain ⟨hl1, hu1⟩ := hV y hy
  obtain ⟨hl2, hu2⟩ := hV z hz3
  have hlz : (0:ℝ) < Real.log (z:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < z))
  have hly : (0:ℝ) < Real.log (y:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hCpos : (0:ℝ) < C := lt_of_lt_of_le hc hC
  have hVLy : 0 < VLE y := by
    have h := (Vsieve_eq_VLE (y+1)).symm
    rw [Nat.add_sub_cancel] at h
    rw [h]; exact Vsieve_pos (y+1)
  have hVLz : 0 < VLE z := by
    have h := (Vsieve_eq_VLE (z+1)).symm
    rw [Nat.add_sub_cancel] at h
    rw [h]; exact Vsieve_pos (z+1)
  -- termwise bound and non-vanishing
  have hfac : ∀ p ∈ ((Nat.primesLE z).filter (fun p => p ≠ 2)).filter (fun p => y < p),
      (1:ℝ)/((p:ℝ)-1) ≤ -Real.log (1 - (1:ℝ)/((p:ℝ)-1)) := by
    intro p hp
    obtain ⟨hp1, _⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpz, hp2⟩ := Finset.mem_filter.mp hp1
    have hpp : p.Prime := (Nat.mem_primesLE.mp hpz).2
    have hx := (Vsieve_factor_bounds hpp hp2).1
    have := Real.log_le_sub_one_of_pos hx
    linarith
  have hne : ∀ p ∈ ((Nat.primesLE z).filter (fun p => p ≠ 2)).filter (fun p => y < p),
      (1 - (1:ℝ)/((p:ℝ)-1)) ≠ 0 := by
    intro p hp
    obtain ⟨hp1, _⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpz, hp2⟩ := Finset.mem_filter.mp hp1
    have hpp : p.Prime := (Nat.mem_primesLE.mp hpz).2
    exact (Vsieve_factor_bounds hpp hp2).1.ne'
  -- the product is `VLE z / VLE y`
  have hprod_eq : (∏ p ∈ ((Nat.primesLE z).filter (fun p => p ≠ 2)).filter (fun p => y < p),
        (1 - (1:ℝ)/((p:ℝ)-1))) = VLE z / VLE y := by
    rw [VLE_mul_split y z hyz, mul_comm (VLE y)]
    field_simp [hVLy.ne']
  -- the sum is `≤ -log ∏(1-g)`
  have hsum_le : (∑ p ∈ ((Nat.primesLE z).filter (fun p => p ≠ 2)).filter (fun p => y < p),
        (1:ℝ)/((p:ℝ)-1))
      ≤ - Real.log (∏ p ∈ ((Nat.primesLE z).filter (fun p => p ≠ 2)).filter (fun p => y < p),
          (1 - (1:ℝ)/((p:ℝ)-1))) := by
    have h1 : (∑ p ∈ ((Nat.primesLE z).filter (fun p => p ≠ 2)).filter (fun p => y < p),
          (1:ℝ)/((p:ℝ)-1))
        ≤ ∑ p ∈ ((Nat.primesLE z).filter (fun p => p ≠ 2)).filter (fun p => y < p),
          -Real.log (1 - (1:ℝ)/((p:ℝ)-1)) := Finset.sum_le_sum hfac
    have h2 : (∑ p ∈ ((Nat.primesLE z).filter (fun p => p ≠ 2)).filter (fun p => y < p),
          -Real.log (1 - (1:ℝ)/((p:ℝ)-1)))
        = - Real.log (∏ p ∈ ((Nat.primesLE z).filter (fun p => p ≠ 2)).filter (fun p => y < p),
          (1 - (1:ℝ)/((p:ℝ)-1))) := by
      rw [Real.log_prod hne, Finset.sum_neg_distrib]
    rw [h2] at h1; exact h1
  rw [hprod_eq, Real.log_div hVLz.ne' hVLy.ne'] at hsum_le
  -- `-log(VLE z / VLE y) = log(VLE y) - log(VLE z)`
  have hkey : Real.log (VLE y) - Real.log (VLE z)
      ≤ Real.log (Real.log (z:ℝ) / Real.log (y:ℝ)) + Real.log (C/c) := by
    have hVy : Real.log (VLE y) ≤ Real.log (C / Real.log (y:ℝ)) := Real.log_le_log hVLy hu1
    have hVz : Real.log (c / Real.log (z:ℝ)) ≤ Real.log (VLE z) :=
      Real.log_le_log (div_pos hc hlz) hl2
    have hcalc : Real.log (C / Real.log (y:ℝ)) - Real.log (c / Real.log (z:ℝ))
        = Real.log (Real.log (z:ℝ) / Real.log (y:ℝ)) + Real.log (C/c) := by
      rw [← Real.log_div (div_ne_zero hCpos.ne' hly.ne') (div_ne_zero hc.ne' hlz.ne'),
        ← Real.log_mul (div_ne_zero hlz.ne' hly.ne') (div_ne_zero hCpos.ne' hc.ne')]
      congr 1
      field_simp
    linarith [hVy, hVz, hcalc]
  refine ⟨Real.log (C/c) + 1, by
    have h0 : (0:ℝ) ≤ Real.log (C/c) := Real.log_nonneg (by rw [le_div_iff₀ hc]; linarith)
    linarith, ?_⟩
  linarith [hsum_le, hkey]

/-- The lower-bound main term of the `β = 1` sieve: `Σ_{c ∈ Gm} (-1)^{|c|}/φ(lprod c)`. -/
def MeSum (D : ℝ) (Y : ℕ) : ℝ :=
  (Gm (1:ℝ) D Y).sum (fun c => (-1:ℝ)^c.length / (Nat.totient (lprod c) : ℝ))

/-- The `θ`-mass of the primes `p ≤ x` with `p ≡ -2 (mod d)`. -/
def thetaD (x d : ℕ) : ℝ :=
  ((Finset.range (x + 1)).filter (fun p : ℕ => p.Prime ∧ d ∣ p + 2)).sum
    (fun p => Real.log (p : ℝ))

/-- The remainder in the Bombieri–Vinogradov approximation `θ_d(x) ≈ x/φ(d)`. -/
def rrem (x d : ℕ) : ℝ := thetaD x d - (x : ℝ) / (Nat.totient d : ℝ)

/-- The upper-bound main term of the `β = 1` sieve (the `Gp` analogue of `MeSum`). -/
def MpSum (D : ℝ) (Y : ℕ) : ℝ :=
  (Gp (1:ℝ) D Y).sum (fun c => (-1:ℝ)^c.length / (Nat.totient (lprod c) : ℝ))

/-- The deficit of the lower-bound main term. -/
def Wm (D : ℝ) (Y : ℕ) : ℝ := Vsieve Y - MeSum D Y

/-- The surplus of the upper-bound main term. -/
def Wp (D : ℝ) (Y : ℕ) : ℝ := MpSum D Y - Vsieve Y

lemma totient_mul_of_coprime {q : ℕ} {l : List ℕ} (h : q.Coprime (lprod l)) :
    Nat.totient (q * lprod l) = q.totient * (lprod l).totient := Nat.totient_mul h

/-- Telescoping identity: for a `Finset` of naturals ordered by size,
`∏ (1 - a_q) = 1 - Σ_q a_q ∏_{q' < q} (1 - a_q')`. -/
lemma prod_one_sub_eq (S : Finset ℕ) (a : ℕ → ℝ) :
    ∏ q ∈ S, (1 - a q)
      = 1 - ∑ q ∈ S, a q * ∏ q' ∈ S.filter (fun q' => q' < q), (1 - a q') := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert m s hms ih =>
      have hm : m ∉ s := fun h => absurd (hms m h) (lt_irrefl m)
      rw [Finset.prod_insert hm]
      have hfil : ∀ q ∈ s, (insert m s).filter (fun q' => q' < q) = s.filter (fun q' => q' < q) := by
        intro q hq
        ext q'
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨h1, h2⟩
          rcases h1 with h1 | h1
          · rw [h1] at h2; exact absurd (hms q hq) (by omega)
          · exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨Or.inr h1, h2⟩
      have hfilm : (insert m s).filter (fun q' => q' < m) = s := by
        ext q'
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨h1, h2⟩
          rcases h1 with h1 | h1
          · rw [h1] at h2; exact absurd h2 (lt_irrefl m)
          · exact h1
        · intro h1
          exact ⟨Or.inr h1, hms q' h1⟩
      rw [Finset.sum_insert hm, hfilm]
      rw [Finset.sum_congr rfl (fun q hq => by rw [hfil q hq])]
      rw [ih]
      ring

/-- The telescoping identity for `Vsieve`: `Vsieve Y = 1 − Σ_{q<Y} a_q Vsieve q`. -/
lemma Vsieve_rec (Y : ℕ) :
    Vsieve Y = 1 - ∑ q ∈ oddPrimesLt Y, (1/((q:ℝ)-1)) * Vsieve q := by
  rw [Vsieve, prod_one_sub_eq]
  congr 1
  refine Finset.sum_congr rfl (fun q hq => ?_)
  congr 1
  have hqY : q < Y := by
    simp only [oddPrimesLt, Finset.mem_filter, Finset.mem_range] at hq
    exact hq.1
  congr 1
  ext q'
  simp only [oddPrimesLt, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    exact ⟨h4, h2, h3⟩
  · rintro ⟨h4, h2, h3⟩
    exact ⟨⟨by omega, h2, h3⟩, h4⟩

/-- `oddPrimesLt Y` is exactly the odd primes in `[3, Y-1]`. -/
lemma oddPrimesLt_eq_Icc (Y : ℕ) (hY : 3 ≤ Y) :
    oddPrimesLt Y = (Finset.Icc 3 (Y-1)).filter (fun q => q.Prime ∧ q ≠ 2) := by
  ext q
  simp only [oddPrimesLt, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨prime_three_le h2 h3, by omega⟩, h2, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨by omega, h3, h4⟩

/-- One step of the `Vsieve` product at an odd prime. -/
lemma Vsieve_succ_of_prime {q : ℕ} (hq : q.Prime) (h2 : q ≠ 2) :
    Vsieve (q+1) = (1 - 1/((q:ℝ)-1)) * Vsieve q := by
  have hset : oddPrimesLt (q+1) = insert q (oddPrimesLt q) := by
    ext r
    simp only [oddPrimesLt, Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
    constructor
    · rintro ⟨hr, hp, h2'⟩
      rcases lt_or_eq_of_le (by omega : r ≤ q) with h | h
      · exact Or.inr ⟨h, hp, h2'⟩
      · exact Or.inl h
    · rintro (h | ⟨hr, hp, h2'⟩)
      · subst h; exact ⟨by omega, hq, h2⟩
      · exact ⟨by omega, hp, h2'⟩
  have hnot : q ∉ oddPrimesLt q := by
    simp only [oddPrimesLt, Finset.mem_filter, Finset.mem_range]; omega
  rw [Vsieve, Vsieve, hset, Finset.prod_insert hnot]

/-- The `Vsieve` product does not change when passing a non-(odd-prime) level. -/
lemma Vsieve_succ_of_not_prime {q : ℕ} (hq : ¬(q.Prime ∧ q ≠ 2)) :
    Vsieve (q+1) = Vsieve q := by
  have hset : oddPrimesLt (q+1) = oddPrimesLt q := by
    ext r
    simp only [oddPrimesLt, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hr, hp, h2'⟩
      refine ⟨?_, hp, h2'⟩
      by_contra h
      have hrq : r = q := by omega
      exact hq ⟨hrq ▸ hp, hrq ▸ h2'⟩
    · rintro ⟨hr, hp, h2'⟩
      exact ⟨by omega, hp, h2'⟩
  rw [Vsieve, Vsieve, hset]

lemma Vsieve_three : Vsieve 3 = 1 := by
  have h0 : oddPrimesLt 3 = ∅ := by decide
  rw [Vsieve, h0, Finset.prod_empty]

/-- **Abel (partial-summation) identity for the `Vsieve` weight.**  Ordering the odd
primes `< Y` by size and using `Σ_{q<r} (1/(q-1)) Vsieve q = 1 - Vsieve r`, the
`Vsieve`-weighted sum of any `Φ : ℕ → ℝ` telescopes to boundary terms plus the
`Vsieve`-weighted increments.  This is the exact summation-by-parts identity behind the
`σ`-profile recursion of the linear sieve. -/
lemma Vsieve_abel (Y : ℕ) (hY : 3 ≤ Y) (Φ : ℕ → ℝ) :
    (∑ q ∈ oddPrimesLt Y, (1/((q:ℝ)-1)) * Vsieve q * Φ q)
      = Φ 3 - Vsieve Y * Φ Y
        + ∑ q ∈ Finset.Icc 3 (Y-1), Vsieve (q+1) * (Φ (q+1) - Φ q) := by
  rcases eq_or_lt_of_le hY with h | h
  · subst h
    have h0 : oddPrimesLt 3 = ∅ := by decide
    have h1 : Finset.Icc 3 (3 - 1) = ∅ := by decide
    simp only [h0, h1, Vsieve, Finset.sum_empty, Finset.prod_empty]
    ring
  have hY1 : 3 ≤ Y - 1 := by omega
  have hstep2 : (∑ q ∈ oddPrimesLt Y, (1/((q:ℝ)-1)) * Vsieve q * Φ q)
      = ∑ q ∈ Finset.Icc 3 (Y-1), (Vsieve q - Vsieve (q+1)) * Φ q := by
    rw [oddPrimesLt_eq_Icc Y hY, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun q hq => ?_)
    by_cases hp : q.Prime ∧ q ≠ 2
    · rw [if_pos hp, Vsieve_succ_of_prime hp.1 hp.2]; ring
    · rw [if_neg hp, Vsieve_succ_of_not_prime hp]; ring
  rw [hstep2]
  have hdis : (∑ q ∈ Finset.Icc 3 (Y-1), (Vsieve q - Vsieve (q+1)) * Φ q)
      = (∑ q ∈ Finset.Icc 3 (Y-1), (Vsieve q * Φ q - Vsieve (q+1) * Φ (q+1)))
        + ∑ q ∈ Finset.Icc 3 (Y-1), Vsieve (q+1) * (Φ (q+1) - Φ q) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun q hq => ?_); ring
  rw [hdis]
  have htel := Finset.sum_Icc_sub (m := 3) (n := Y-1) hY1 (fun q => Vsieve q * Φ q)
  have hYsub : Y - 1 + 1 = Y := by omega
  rw [hYsub] at htel
  have hneg : (∑ q ∈ Finset.Icc 3 (Y-1), (Vsieve q * Φ q - Vsieve (q+1) * Φ (q+1)))
      = - ∑ q ∈ Finset.Icc 3 (Y-1), (Vsieve (q+1) * Φ (q+1) - Vsieve q * Φ q) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun q hq => by ring)
  rw [hneg, htel, Vsieve_three]
  ring

/-- **The `1`-step recursion of the lower-bound main term.** -/
lemma MeSum_rec (D : ℝ) (Y : ℕ) :
    MeSum D Y = 1 - ∑ q ∈ oddPrimesLt Y,
      (if (q:ℝ) ≤ D then (1/(Nat.totient q : ℝ)) * MpSum (D/q) q else 0) := by
  rw [MeSum, sum_Gm_decomp]
  have hnil : (-1:ℝ)^([] : List ℕ).length / (Nat.totient (lprod ([] : List ℕ)) : ℝ) = 1 := by
    simp [lprod]
  rw [hnil]
  congr 1
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  have hqp : q.Prime := ((sievePrime_iff_mem Y q).mp hq).1
  have hterm : (Gp (1:ℝ) (D/q) q).sum
        (fun l => (-1:ℝ)^(q :: l).length / (Nat.totient (lprod (q :: l)) : ℝ))
      = -((1/(Nat.totient q : ℝ)) * MpSum (D/q) q) := by
    rw [MpSum, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun l hl => ?_)
    have hcop : q.Coprime (lprod l) := by
      rw [hqp.coprime_iff_not_dvd]
      intro hdvd
      rw [lprod] at hdvd
      obtain ⟨a, ha, hqa⟩ := prime_dvd_list_prod hqp hdvd
      have hh := ((chain_primes (1:ℝ) q (D/q)).1 l hl a ha)
      have hthis : a = q := ((Nat.prime_dvd_prime_iff_eq hqp hh.1).mp hqa).symm
      rw [hthis] at hh
      exact absurd hh.2.2 (lt_irrefl q)
    rw [List.length_cons, lprod_cons, totient_mul_of_coprime hcop]
    push_cast
    rw [pow_succ]
    field_simp
    try ring
  by_cases hqD : (q:ℝ) ≤ D
  · rw [if_pos hqD, if_pos hqD]; exact hterm
  · rw [if_neg hqD, if_neg hqD]; simp

/-- **The `1`-step recursion of the upper-bound main term.** -/
lemma MpSum_rec (D : ℝ) (Y : ℕ) :
    MpSum D Y = 1 - ∑ q ∈ oddPrimesLt Y,
      (if (q:ℝ)^((1:ℝ)+1) ≤ D then (1/(Nat.totient q : ℝ)) * MeSum (D/q) q else 0) := by
  rw [MpSum, sum_Gp_decomp]
  have hnil : (-1:ℝ)^([] : List ℕ).length / (Nat.totient (lprod ([] : List ℕ)) : ℝ) = 1 := by
    simp [lprod]
  rw [hnil]
  congr 1
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  have hqp : q.Prime := ((sievePrime_iff_mem Y q).mp hq).1
  have hterm : (Gm (1:ℝ) (D/q) q).sum
        (fun l => (-1:ℝ)^(q :: l).length / (Nat.totient (lprod (q :: l)) : ℝ))
      = -((1/(Nat.totient q : ℝ)) * MeSum (D/q) q) := by
    rw [MeSum, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun l hl => ?_)
    have hcop : q.Coprime (lprod l) := by
      rw [hqp.coprime_iff_not_dvd]
      intro hdvd
      rw [lprod] at hdvd
      obtain ⟨a, ha, hqa⟩ := prime_dvd_list_prod hqp hdvd
      have hh := ((chain_primes (1:ℝ) q (D/q)).2 l hl a ha)
      have hthis : a = q := ((Nat.prime_dvd_prime_iff_eq hqp hh.1).mp hqa).symm
      rw [hthis] at hh
      exact absurd hh.2.2 (lt_irrefl q)
    rw [List.length_cons, lprod_cons, totient_mul_of_coprime hcop]
    push_cast
    rw [pow_succ]
    field_simp
    try ring
  by_cases hqD : (q:ℝ)^((1:ℝ)+1) ≤ D
  · rw [if_pos hqD, if_pos hqD]; exact hterm
  · rw [if_neg hqD, if_neg hqD]; simp

/-- **The `1`-step recursion of the deficit `W⁻`.** -/
lemma Wm_rec (D : ℝ) (Y : ℕ) :
    Wm D Y = ∑ q ∈ oddPrimesLt Y,
      ((if (q:ℝ) ≤ D then (1/((q:ℝ)-1)) * Wp (D/q) q else 0)
        - (if D < (q:ℝ) then (1/((q:ℝ)-1)) * Vsieve q else 0)) := by
  have htot : ∀ q ∈ oddPrimesLt Y, (1/(Nat.totient q : ℝ)) = (1/((q:ℝ)-1)) := by
    intro q hq
    have hqp : q.Prime := ((sievePrime_iff_mem Y q).mp hq).1
    rw [Nat.totient_prime hqp]
    have hc : ((q - 1 : ℕ) : ℝ) = (q:ℝ) - 1 := by
      rw [Nat.cast_sub hqp.one_le]; norm_num
    rw [hc]
  have hone : MeSum D Y = 1 - ∑ q ∈ oddPrimesLt Y,
      (if (q:ℝ) ≤ D then (1/((q:ℝ)-1)) * MpSum (D/q) q else 0) := by
    rw [MeSum_rec, Finset.sum_congr rfl (fun q hq => by rw [htot q hq])]
  rw [Wm, hone, Vsieve_rec]
  rw [show (1 - (∑ q ∈ oddPrimesLt Y, (1/((q:ℝ)-1)) * Vsieve q))
        - (1 - (∑ q ∈ oddPrimesLt Y,
            (if (q:ℝ) ≤ D then (1/((q:ℝ)-1)) * MpSum (D/q) q else 0)))
      = (∑ q ∈ oddPrimesLt Y,
            (if (q:ℝ) ≤ D then (1/((q:ℝ)-1)) * MpSum (D/q) q else 0))
        - (∑ q ∈ oddPrimesLt Y, (1/((q:ℝ)-1)) * Vsieve q)
      from by ring]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  by_cases h : (q:ℝ) ≤ D
  · have h2 : ¬ D < (q:ℝ) := by linarith
    simp only [if_pos h, if_neg h2, Wp]
    try ring
  · have h2 : D < (q:ℝ) := by linarith
    simp only [if_neg h, if_pos h2, Wp]
    try ring

/-- **The `1`-step recursion of the surplus `W⁺`.** -/
lemma Wp_rec (D : ℝ) (Y : ℕ) :
    Wp D Y = ∑ q ∈ oddPrimesLt Y,
      ((if (q:ℝ)^((1:ℝ)+1) ≤ D then (1/((q:ℝ)-1)) * Wm (D/q) q else 0)
        + (if ¬ ((q:ℝ)^((1:ℝ)+1) ≤ D) then (1/((q:ℝ)-1)) * Vsieve q else 0)) := by
  have htot : ∀ q ∈ oddPrimesLt Y, (1/(Nat.totient q : ℝ)) = (1/((q:ℝ)-1)) := by
    intro q hq
    have hqp : q.Prime := ((sievePrime_iff_mem Y q).mp hq).1
    rw [Nat.totient_prime hqp]
    have hc : ((q - 1 : ℕ) : ℝ) = (q:ℝ) - 1 := by
      rw [Nat.cast_sub hqp.one_le]; norm_num
    rw [hc]
  have hone : MpSum D Y = 1 - ∑ q ∈ oddPrimesLt Y,
      (if (q:ℝ)^((1:ℝ)+1) ≤ D then (1/((q:ℝ)-1)) * MeSum (D/q) q else 0) := by
    rw [MpSum_rec, Finset.sum_congr rfl (fun q hq => by rw [htot q hq])]
  rw [Wp, hone, Vsieve_rec]
  rw [show (1 - (∑ q ∈ oddPrimesLt Y,
            (if (q:ℝ)^((1:ℝ)+1) ≤ D then (1/((q:ℝ)-1)) * MeSum (D/q) q else 0)))
        - (1 - (∑ q ∈ oddPrimesLt Y, (1/((q:ℝ)-1)) * Vsieve q))
      = (∑ q ∈ oddPrimesLt Y, (1/((q:ℝ)-1)) * Vsieve q)
        - (∑ q ∈ oddPrimesLt Y,
            (if (q:ℝ)^((1:ℝ)+1) ≤ D then (1/((q:ℝ)-1)) * MeSum (D/q) q else 0))
      from by ring]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  by_cases h : (q:ℝ)^((1:ℝ)+1) ≤ D
  · have h2 : ¬ ¬ ((q:ℝ)^((1:ℝ)+1) ≤ D) := fun hc => hc h
    simp only [if_pos h, if_neg h2, Wm]
    try ring
  · have h2 : ¬ ((q:ℝ)^((1:ℝ)+1) ≤ D) := h
    simp only [if_neg h, if_pos h2, Wm]
    try ring

lemma oddPrimesLt_lt {q Y : ℕ} (hq : q ∈ oddPrimesLt Y) : q < Y := by
  rw [oddPrimesLt, Finset.mem_filter, Finset.mem_range] at hq
  exact hq.1

/-- **The `2`-step recursion of the deficit.**  For `D ≥ Y` the boundary term of `W⁻`
vanishes and substituting the `W⁺` recursion gives the pair recursion
`W⁻(D,Y) = Σ_{q₁>q₂} a_{q₁}a_{q₂}·[W⁻(D/(q₁q₂),q₂)·1_{q₁q₂²≤D} + V(q₂)·1_{q₁q₂²>D}]`. -/
lemma Wm_two_step (D : ℝ) (Y : ℕ) (hDY : (Y:ℝ) ≤ D) :
    Wm D Y = (oddPrimesLt Y).sum (fun q₁ => (1/((q₁:ℝ)-1)) *
      ((oddPrimesLt q₁).sum (fun q₂ =>
        ((if (q₂:ℝ)^((1:ℝ)+1) ≤ D/q₁ then (1/((q₂:ℝ)-1)) * Wm (D/q₁/q₂) q₂ else 0)
          + (if ¬ ((q₂:ℝ)^((1:ℝ)+1) ≤ D/q₁) then (1/((q₂:ℝ)-1)) * Vsieve q₂ else 0))))) := by
  have hA1 : ∀ q ∈ oddPrimesLt Y,
      (if D < (q:ℝ) then (1/((q:ℝ)-1)) * Vsieve q else 0) = 0 := by
    intro q hq
    have hqlt : (q:ℝ) < (Y:ℝ) := by exact_mod_cast oddPrimesLt_lt hq
    rw [if_neg (by linarith)]
  rw [Wm_rec]
  rw [Finset.sum_congr rfl (fun q hq => by rw [hA1 q hq, sub_zero])]
  rw [Finset.sum_congr rfl (fun q hq => ?_)]
  have hqD : (q:ℝ) ≤ D := by
    have hqlt : (q:ℝ) < (Y:ℝ) := by exact_mod_cast oddPrimesLt_lt hq
    linarith
  rw [if_pos hqD]
  congr 1
  exact Wp_rec (D/q) q

/-- **The `2`-step recursion at level `≥ 3`.**  When `D ≥ Y³` every "`A₂`" boundary
term is empty (since `q₁q₂² < Y³ ≤ D` for `q₁,q₂ < Y`), giving
`W⁻(D,Y) = Σ_{q₁>q₂} a_{q₁}a_{q₂} W⁻(D/(q₁q₂), q₂)`. -/
lemma Wm_two_step_pure (D : ℝ) (Y : ℕ) (hDY : (Y:ℝ) ≤ D) (hD3 : (Y:ℝ)^3 ≤ D) :
    Wm D Y = (oddPrimesLt Y).sum (fun q₁ => (oddPrimesLt q₁).sum (fun q₂ =>
      (1/((q₁:ℝ)-1)) * ((1/((q₂:ℝ)-1)) * Wm (D/q₁/q₂) q₂))) := by
  rw [Wm_two_step D Y hDY]
  refine Finset.sum_congr rfl (fun q₁ hq₁ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun q₂ hq₂ => ?_)
  have h1 : (q₁:ℝ) < (Y:ℝ) := by exact_mod_cast oddPrimesLt_lt hq₁
  have h2 : (q₂:ℝ) < (q₁:ℝ) := by
    have : q₂ < q₁ := oddPrimesLt_lt hq₂
    exact_mod_cast this
  have hq₁pos : (0:ℝ) < (q₁:ℝ) := by
    have := (sievePrime_iff_mem Y q₁).mp hq₁
    exact_mod_cast this.1.pos
  have hYpos : (0:ℝ) < (Y:ℝ) := by
    have := (sievePrime_iff_mem Y q₁).mp hq₁
    exact_mod_cast (lt_trans this.1.pos this.2.2)
  have hcond : (q₂:ℝ)^((1:ℝ)+1) ≤ D/q₁ := by
    rw [le_div_iff₀ hq₁pos]
    have hY3 : ((q₂:ℝ)^((1:ℝ)+1)) * (q₁:ℝ) < (Y:ℝ)^3 := by
      have hq2sq : ((q₂:ℝ)^((1:ℝ)+1)) = (q₂:ℝ)^2 := by norm_num
      rw [hq2sq]
      have hstep : (q₂:ℝ)^2 * (q₁:ℝ) ≤ (q₁:ℝ)^3 := by
        have hq2le : (q₂:ℝ) ≤ (q₁:ℝ) := le_of_lt h2
        have hsq : (q₂:ℝ)^2 ≤ (q₁:ℝ)^2 := pow_le_pow_left₀ (by positivity) hq2le 2
        calc (q₂:ℝ)^2 * (q₁:ℝ) ≤ (q₁:ℝ)^2 * (q₁:ℝ) :=
              mul_le_mul_of_nonneg_right hsq (by positivity)
          _ = (q₁:ℝ)^3 := by ring
      have hlt : (q₁:ℝ)^3 < (Y:ℝ)^3 := by
        have hq1le : (q₁:ℝ) ≤ (Y:ℝ) - 1 := by
          have hq1Y : q₁ + 1 ≤ Y := by
            have := oddPrimesLt_lt hq₁
            omega
          have hc : ((q₁ + 1 : ℕ) : ℝ) ≤ (Y:ℝ) := by exact_mod_cast hq1Y
          push_cast at hc; linarith
        have hcube : ((Y:ℝ) - 1)^3 < (Y:ℝ)^3 := by nlinarith [hYpos]
        calc (q₁:ℝ)^3 ≤ ((Y:ℝ)-1)^3 := pow_le_pow_left₀ (by positivity) hq1le 3
          _ < (Y:ℝ)^3 := hcube
      linarith [hstep, hlt]
    linarith [hY3, hD3]
  rw [if_pos hcond, if_neg (by simp [hcond])]
  ring

/-! ## The total deficit `E = MpSum − MeSum = W⁻ + W⁺` and its cancellation-free recursion

While the individual deficits `W⁻ = Vsieve − MeSum` and `W⁺ = MpSum − Vsieve` obey
`1`-step recursions with *boundary* (`Vsieve`) contributions, their sum
`E := MpSum − MeSum` obeys the *cancellation-free* recursion
`E(D,Y) = Σ_{q<Y} (q−1)⁻¹ E(D/q,q)` as soon as `D ≥ Y²`.  Since `W⁻ ≤ E`, any upper
bound for `E` bounds the deficit of the lower-bound main term. -/

/-- The total deficit of the `β = 1` sieve main terms. -/
def EmSum (D : ℝ) (Y : ℕ) : ℝ := MpSum D Y - MeSum D Y

lemma EmSum_eq (D : ℝ) (Y : ℕ) : EmSum D Y = Wm D Y + Wp D Y := by
  unfold EmSum Wm Wp; ring

lemma inv_totient_prime {q : ℕ} (hq : q.Prime) :
    (1:ℝ)/(Nat.totient q : ℝ) = 1/((q:ℝ)-1) := by
  rw [Nat.totient_prime hq]
  have hc : ((q - 1 : ℕ) : ℝ) = (q:ℝ) - 1 := by
    rw [Nat.cast_sub hq.one_le]; norm_num
  rw [hc]

/-- **The cancellation-free recursion of the total deficit.**  For `D ≥ Y²` every
modulus `q < Y` is admissible in both `1`-step recursions, and the two `1`'s cancel. -/
lemma EmSum_rec (D : ℝ) (Y : ℕ) (hD : (Y:ℝ)^2 ≤ D) :
    EmSum D Y = ∑ q ∈ oddPrimesLt Y, (1/((q:ℝ)-1)) * EmSum (D/q) q := by
  have htot : ∀ q ∈ oddPrimesLt Y, (1:ℝ)/(Nat.totient q : ℝ) = 1/((q:ℝ)-1) :=
    fun q hq => inv_totient_prime ((sievePrime_iff_mem Y q).mp hq).1
  have hqY' : ∀ q ∈ oddPrimesLt Y, (q:ℝ) < (Y:ℝ) :=
    fun q hq => by exact_mod_cast oddPrimesLt_lt hq
  have hY1 : ∀ q ∈ oddPrimesLt Y, (1:ℝ) ≤ (Y:ℝ) := by
    intro q hq
    have : q < Y := oddPrimesLt_lt hq
    exact_mod_cast (by omega : 1 ≤ Y)
  have hqD : ∀ q ∈ oddPrimesLt Y, (q:ℝ) ≤ D := by
    intro q hq
    have h1 := hqY' q hq
    have h2 := hY1 q hq
    have h3 : (Y:ℝ) ≤ (Y:ℝ)^2 := by nlinarith
    linarith [hD, h1, h2, h3]
  have hqD2 : ∀ q ∈ oddPrimesLt Y, (q:ℝ)^((1:ℝ)+1) ≤ D := by
    intro q hq
    have h1 := hqY' q hq
    have hq2 : ((q:ℝ)^((1:ℝ)+1)) = (q:ℝ)^2 := by norm_num
    rw [hq2]
    nlinarith [hD, h1]
  have h1 : MeSum D Y = 1 - ∑ q ∈ oddPrimesLt Y,
      (if (q:ℝ) ≤ D then (1/((q:ℝ)-1)) * MpSum (D/q) q else 0) := by
    rw [MeSum_rec, Finset.sum_congr rfl (fun q hq => by rw [htot q hq])]
  have h2 : MpSum D Y = 1 - ∑ q ∈ oddPrimesLt Y,
      (if (q:ℝ)^((1:ℝ)+1) ≤ D then (1/((q:ℝ)-1)) * MeSum (D/q) q else 0) := by
    rw [MpSum_rec, Finset.sum_congr rfl (fun q hq => by rw [htot q hq])]
  unfold EmSum
  rw [h1, h2]
  have hAB : (1 - ∑ q ∈ oddPrimesLt Y,
        (if (q:ℝ)^((1:ℝ)+1) ≤ D then (1/((q:ℝ)-1)) * MeSum (D/q) q else 0))
      - (1 - ∑ q ∈ oddPrimesLt Y,
        (if (q:ℝ) ≤ D then (1/((q:ℝ)-1)) * MpSum (D/q) q else 0))
      = (∑ q ∈ oddPrimesLt Y,
        (if (q:ℝ) ≤ D then (1/((q:ℝ)-1)) * MpSum (D/q) q else 0))
      - (∑ q ∈ oddPrimesLt Y,
        (if (q:ℝ)^((1:ℝ)+1) ≤ D then (1/((q:ℝ)-1)) * MeSum (D/q) q else 0)) := by ring
  rw [hAB, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  rw [if_pos (hqD q hq), if_pos (hqD2 q hq)]
  ring

private lemma sum_Icc_sub_split (g : ℕ → ℝ) {a b c : ℕ} (hb : a ≤ b + 1) (hc : b + 1 ≤ c) :
    ∑ q ∈ Finset.Icc a c, g q = ∑ q ∈ Finset.Icc a b, g q + ∑ q ∈ Finset.Icc (b+1) c, g q := by
  rw [← Finset.sum_union (Finset.disjoint_left.mpr (by
    intro x hx hx'
    rw [Finset.mem_Icc] at hx hx'; omega))]
  congr 1
  ext x
  simp only [Finset.mem_union, Finset.mem_Icc]
  omega

/-- **Sharpened partial summation for the odd-prime sieve product.**
If `Φ` is monotone with `Φ w = 0` and `C` dominates `Vsieve t · log t` on the whole range
`[w,Y]` of summation, then the odd-prime Abel sum is dominated by the boundary term
`Φ Y (C/log Y - Vsieve Y)` plus `C` times the *staircase* of `Φ` against the jumps
`1/log q - 1/log(q+1)` of the weight `1/log`.

This is Nathanson's Lemma 9.8 with the `K`-hypothesis `∏(1-g)^{-1} ≤ K log z/log u` replaced by
the *actual* supremum of `Vsieve · log` over the effective range `[w,Y]`: taking `w = u₀` at the
edge of the support of the layer profile removes the deviation of the small primes. -/
lemma Vsieve_abel_sharp (Y w : ℕ) (hY : 3 ≤ Y) (hw : 3 ≤ w) (hwY : w ≤ Y)
    (C : ℝ) (hC : ∀ t : ℕ, w ≤ t → t ≤ Y → Vsieve t * Real.log (t:ℝ) ≤ C)
    (Φ : ℕ → ℝ) (hmono : Monotone Φ) (hΦw : Φ w = 0) :
    ∑ q ∈ (oddPrimesLt Y).filter (fun q => w ≤ q), (1/((q:ℝ)-1)) * Vsieve q * Φ q
      ≤ Φ Y * (C / Real.log (Y:ℝ) - Vsieve Y)
        + C * ∑ q ∈ Finset.Icc (w+1) (Y-1),
            Φ q * (1 / Real.log (q:ℝ) - 1 / Real.log ((q+1:ℕ):ℝ)) := by
  rcases eq_or_lt_of_le hwY with h | h
  · -- `w = Y`: both sides vanish
    have hΦY : Φ Y = 0 := by rw [← h]; exact hΦw
    rw [h]
    have he1 : (oddPrimesLt Y).filter (fun q => Y ≤ q) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro q hq
      rw [oddPrimesLt, Finset.mem_filter, Finset.mem_range] at hq
      omega
    have he2 : Finset.Icc (Y+1) (Y-1) = ∅ := by
      rw [Finset.Icc_eq_empty_iff]; omega
    rw [he1, he2, Finset.sum_empty, Finset.sum_empty, hΦY, zero_mul, mul_zero, zero_add]
  · have hwY1 : w ≤ Y - 1 := by omega
    have hY1 : 3 ≤ Y - 1 := by omega
    -- **(A) the exact sub-range Abel identity**
    have hsub : oddPrimesLt w ⊆ oddPrimesLt Y := by
      intro q hq
      rw [oddPrimesLt, Finset.mem_filter, Finset.mem_range] at hq ⊢
      exact ⟨lt_of_lt_of_le hq.1 hwY, hq.2⟩
    have hEq : (oddPrimesLt Y).filter (fun q => w ≤ q) = oddPrimesLt Y \ oddPrimesLt w := by
      ext q
      rw [Finset.mem_filter, Finset.mem_sdiff]
      constructor
      · rintro ⟨hq, hwq⟩
        refine ⟨hq, fun hw' => ?_⟩
        rw [oddPrimesLt, Finset.mem_filter, Finset.mem_range] at hw'
        omega
      · rintro ⟨hq, hqnot⟩
        refine ⟨hq, ?_⟩
        by_contra hlt
        push Not at hlt
        exact hqnot (Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr hlt, (Finset.mem_filter.mp hq).2⟩)
    have hAbelY := Vsieve_abel Y hY Φ
    have hAbelw := Vsieve_abel w hw Φ
    have hIcc := sum_Icc_sub_split (fun q => Vsieve (q+1) * (Φ (q+1) - Φ q)) (a := 3)
      (b := w - 1) (c := Y - 1) (by omega) (by omega : w - 1 + 1 ≤ Y - 1)
    rw [show w - 1 + 1 = w from by omega] at hIcc
    have hdr : ∑ q ∈ (oddPrimesLt Y).filter (fun q => w ≤ q),
            (1/((q:ℝ)-1)) * Vsieve q * Φ q
        = Vsieve w * Φ w - Vsieve Y * Φ Y
          + ∑ q ∈ Finset.Icc w (Y-1), Vsieve (q+1) * (Φ (q+1) - Φ q) := by
      have hsd : ∑ q ∈ oddPrimesLt Y \ oddPrimesLt w, (1/((q:ℝ)-1)) * Vsieve q * Φ q
          = (∑ q ∈ oddPrimesLt Y, (1/((q:ℝ)-1)) * Vsieve q * Φ q)
            - ∑ q ∈ oddPrimesLt w, (1/((q:ℝ)-1)) * Vsieve q * Φ q := by
        rw [eq_sub_iff_add_eq]
        exact Finset.sum_sdiff hsub
      rw [hEq, hsd, hAbelY, hAbelw, hIcc]
      ring
    -- **(B) termwise bound `Vsieve(q+1) ≤ C/log(q+1)`**
    have hstep : ∑ q ∈ Finset.Icc w (Y-1), Vsieve (q+1) * (Φ (q+1) - Φ q)
        ≤ C * ∑ q ∈ Finset.Icc w (Y-1),
            (Φ (q+1) - Φ q) / Real.log ((q+1:ℕ):ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun q hq => ?_)
      rw [Finset.mem_Icc] at hq
      have hq1 : w ≤ q + 1 := by omega
      have hq2 : q + 1 ≤ Y := by omega
      have hlog : 0 < Real.log ((q+1:ℕ):ℝ) := by
        have : (1:ℝ) < ((q+1:ℕ):ℝ) := by exact_mod_cast (by omega : 1 < q + 1)
        exact Real.log_pos this
      have hb := hC (q+1) hq1 hq2
      have hb' : Vsieve (q+1) ≤ C / Real.log ((q+1:ℕ):ℝ) := by
        rw [le_div_iff₀ hlog]; simpa [mul_comm] using hb
      have hd : 0 ≤ Φ (q+1) - Φ q := by
        have := hmono (Nat.le_succ q); linarith
      calc Vsieve (q+1) * (Φ (q+1) - Φ q)
          ≤ (C / Real.log ((q+1:ℕ):ℝ)) * (Φ (q+1) - Φ q) :=
            mul_le_mul_of_nonneg_right hb' hd
        _ = C * ((Φ (q+1) - Φ q) / Real.log ((q+1:ℕ):ℝ)) := by ring
    -- **(C) weighted Abel summation of the staircase**
    have habel : ∑ q ∈ Finset.Icc w (Y-1), (Φ (q+1) - Φ q) / Real.log ((q+1:ℕ):ℝ)
        = Φ Y / Real.log (Y:ℝ)
          + ∑ q ∈ Finset.Icc (w+1) (Y-1),
              Φ q * (1 / Real.log (q:ℝ) - 1 / Real.log ((q+1:ℕ):ℝ)) := by
      have hYeq : Y - 1 + 1 = Y := by omega
      have htel := Finset.sum_Icc_sub hwY1 (fun q => Φ q * (1 / Real.log (q:ℝ)))
      rw [hYeq] at htel
      -- `htel : ∑ (Φ(q+1)/log(q+1) - Φ q / log q) = Φ Y/log Y - Φ w/log w`
      have hsplit : ∑ q ∈ Finset.Icc (w+1) (Y-1),
            Φ q * (1 / Real.log (q:ℝ) - 1 / Real.log ((q+1:ℕ):ℝ))
          = ∑ q ∈ Finset.Icc w (Y-1),
            Φ q * (1 / Real.log (q:ℝ) - 1 / Real.log ((q+1:ℕ):ℝ)) := by
        have hcons : Finset.Icc w (Y-1) = insert w (Finset.Icc (w+1) (Y-1)) := by
          ext x
          rw [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Icc]
          omega
        rw [hcons, Finset.sum_insert (by rw [Finset.mem_Icc]; omega)]
        rw [hΦw, zero_mul, zero_add]
      rw [hsplit]
      have hkey : ∑ q ∈ Finset.Icc w (Y-1), (Φ (q+1) - Φ q) / Real.log ((q+1:ℕ):ℝ)
          = (Φ Y / Real.log (Y:ℝ) - Φ w / Real.log (w:ℝ))
            + ∑ q ∈ Finset.Icc w (Y-1),
                Φ q * (1 / Real.log (q:ℝ) - 1 / Real.log ((q+1:ℕ):ℝ)) := by
        have h1 : ∑ q ∈ Finset.Icc w (Y-1),
              (Φ (q+1) * (1 / Real.log ((q+1:ℕ):ℝ)) - Φ q * (1 / Real.log (q:ℝ)))
            = Φ Y * (1 / Real.log (Y:ℝ)) - Φ w * (1 / Real.log (w:ℝ)) := by
          have hsub2 := Finset.sum_Icc_sub hwY1 (fun q => Φ q * (1 / Real.log (q:ℝ)))
          rw [hYeq] at hsub2
          simpa using hsub2
        have h2 : ∑ q ∈ Finset.Icc w (Y-1), (Φ (q+1) - Φ q) / Real.log ((q+1:ℕ):ℝ)
            = ∑ q ∈ Finset.Icc w (Y-1),
                ((Φ (q+1) * (1 / Real.log ((q+1:ℕ):ℝ)) - Φ q * (1 / Real.log (q:ℝ)))
                  + Φ q * (1 / Real.log (q:ℝ) - 1 / Real.log ((q+1:ℕ):ℝ))) := by
          refine Finset.sum_congr rfl (fun q _ => ?_)
          ring
        rw [h2, Finset.sum_add_distrib, h1, hΦw]
        ring
      rw [hkey, hΦw, zero_div, sub_zero]
    -- assemble
    rw [hdr]
    have hzero : Vsieve w * Φ w - Vsieve Y * Φ Y = - Vsieve Y * Φ Y := by
      rw [hΦw, mul_zero, zero_sub]; ring
    rw [hzero]
    set S : ℝ := ∑ q ∈ Finset.Icc (w+1) (Y-1),
        Φ q * (1 / Real.log (q:ℝ) - 1 / Real.log ((q+1:ℕ):ℝ)) with hS
    have h4 : C * ∑ q ∈ Finset.Icc w (Y-1), (Φ (q+1) - Φ q) / Real.log ((q+1:ℕ):ℝ)
        ≤ C * (Φ Y / Real.log (Y:ℝ) + S) := by
      rw [habel, hS]
    have h2 : ∑ q ∈ Finset.Icc w (Y-1), Vsieve (q+1) * (Φ (q+1) - Φ q)
        ≤ C * (Φ Y / Real.log (Y:ℝ) + S) := le_trans hstep h4
    have hgoal : - Vsieve Y * Φ Y + C * (Φ Y / Real.log (Y:ℝ) + S)
        = Φ Y * (C / Real.log (Y:ℝ) - Vsieve Y) + C * S := by ring
    linarith [h2, hgoal]

/-! **Remark (state of the two-sided bound).**  Numerically one has
`MeSum D Y ≤ Vsieve Y ≤ MpSum D Y` for `D ≥ Y³` (this is the content of
`Wm ≥ 0`, `Wp ≥ 0`), but the naive strong induction on `Y` does *not* close:
bounding `MeSum D Y` needs `MpSum (D/q) q ≥ Vsieve q`, hence `D ≥ q³`, while
bounding `MpSum D Y` needs `MeSum (D/q) q ≤ Vsieve q`, hence `D ≥ q³` as well;
these requirements do not propagate downwards (`D ≥ Y^c` yields `D ≥ Y^{c+1}` at
the next level).  A *decaying profile* `Wm(D,Y) ≤ φ(log D/log Y)·Vsieve Y` (with
`φ` the linear-sieve deficit function) is required instead. -/

/-! ### Positivity of the two deficits

`Wp = MpSum − Vsieve` is nonnegative for every `D`; `Wm = Vsieve − MeSum` is nonnegative as
soon as `D ≥ Y`.  Hence `MeSum D Y ≤ Vsieve Y ≤ MpSum D Y` for `D ≥ Y`, and in particular
`Wm ≤ EmSum` (so the *cancellation-free* recursion `EmSum_rec` also bounds the lower-bound
deficit).  The proof is a strong induction on the sieve level `Y`: the recursion at level `3`
is empty, and at level `Y` the children sit at levels `q < Y` with `D/q ≥ q` whenever the
terminating branch `q² ≤ D` is taken. -/

lemma Wm_Wp_nonneg : ∀ Y : ℕ,
    (∀ D : ℝ, (Y:ℝ) ≤ D → 0 ≤ Wm D Y) ∧ (∀ D : ℝ, 0 ≤ Wp D Y) := by
  intro Y
  induction Y using Nat.strong_induction_on with
  | h Y ih =>
    constructor
    · intro D hDY
      have hstep : Wm D Y = ∑ q ∈ oddPrimesLt Y, (1/((q:ℝ)-1)) * Wp (D/q) q := by
        rw [Wm_rec]
        refine Finset.sum_congr rfl (fun q hq => ?_)
        have hqlt : (q:ℝ) < (Y:ℝ) := by exact_mod_cast oddPrimesLt_lt hq
        have h1 : (q:ℝ) ≤ D := by linarith
        rw [if_pos h1, if_neg (by linarith : ¬ D < (q:ℝ)), sub_zero]
      rw [hstep]
      refine Finset.sum_nonneg (fun q hq => ?_)
      have hqlt : q < Y := oddPrimesLt_lt hq
      have hone : (0:ℝ) < (q:ℝ) - 1 := by
        have := (sievePrime_iff_mem Y q).mp hq
        have h3 := prime_three_le this.1 this.2.1
        have : (1:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 1 < q)
        linarith
      exact mul_nonneg (by positivity) ((ih q hqlt).2 (D/q))
    · intro D
      rw [Wp_rec D Y]
      refine Finset.sum_nonneg (fun q hq => ?_)
      have hqlt : q < Y := oddPrimesLt_lt hq
      have hone : (0:ℝ) < (q:ℝ) - 1 := by
        have := (sievePrime_iff_mem Y q).mp hq
        have h3 := prime_three_le this.1 this.2.1
        have : (1:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 1 < q)
        linarith
      by_cases hc : (q:ℝ)^((1:ℝ)+1) ≤ D
      · have hq2 : ((q:ℝ)^((1:ℝ)+1)) = (q:ℝ)^2 := by norm_num
        have hqle : (q:ℝ) ≤ D/q := by
          rw [le_div_iff₀ (by linarith : (0:ℝ) < (q:ℝ))]
          rw [hq2] at hc; nlinarith
        have h0 := (ih q hqlt).1 (D/q) hqle
        simp only [if_pos hc, if_neg (not_not_intro hc), add_zero]
        exact mul_nonneg (by positivity) h0
      · simp only [if_neg hc, if_pos hc, zero_add]
        exact mul_nonneg (by positivity) (le_of_lt (Vsieve_pos q))

/-- `MeSum D Y ≤ Vsieve Y` for `D ≥ Y` (the `β = 1` lower-bound main term never exceeds the
Euler product once the level of distribution is at least the sifting limit). -/
lemma MeSum_le_Vsieve {D : ℝ} {Y : ℕ} (hDY : (Y:ℝ) ≤ D) : MeSum D Y ≤ Vsieve Y := by
  have := (Wm_Wp_nonneg Y).1 D hDY
  unfold Wm at this; linarith

/-- `Vsieve Y ≤ MpSum D Y` (the upper-bound main term always dominates the Euler product). -/
lemma Vsieve_le_MpSum (D : ℝ) (Y : ℕ) : Vsieve Y ≤ MpSum D Y := by
  have := (Wm_Wp_nonneg Y).2 D
  unfold Wp at this; linarith

/-- The lower-bound deficit is dominated by the *total* deficit `EmSum = MpSum − MeSum`
(which obeys the cancellation-free recursion `EmSum_rec`). -/
lemma Wm_le_EmSum (D : ℝ) (Y : ℕ) : Wm D Y ≤ EmSum D Y := by
  have h := (Wm_Wp_nonneg Y).2 D
  unfold EmSum Wm Wp at *; linarith

/-- **Reduction of the sieve main-term lower bound to the *total* deficit.**
Since `MeSum = Vsieve − Wm` and `Wm ≤ EmSum = MpSum − MeSum` (`Wm_le_EmSum`), a bound
`EmSum D Y ≤ (1 − c₀)·Vsieve Y` on the *total* deficit — which obeys the boundary-free
recursion `EmSum D Y = Σ_{q<Y}(q−1)⁻¹·EmSum (D/q) q` as soon as `D ≥ Y²` — immediately gives the
lower bound `c₀·Vsieve Y ≤ MeSum D Y` for the lower-bound main term.  This isolates the whole
analytical difficulty in `EmSum`, whose recursion carries no `Vsieve` boundary terms. -/
lemma beta_sieve_deficit_of_EmSum {c₀ : ℝ}
    (h : ∀ Y : ℕ, 3 ≤ Y → ∀ D : ℝ, (Y:ℝ)^3 ≤ D → EmSum D Y ≤ (1 - c₀) * Vsieve Y) :
    ∀ Y : ℕ, 3 ≤ Y → ∀ D : ℝ, (Y:ℝ)^3 ≤ D → c₀ * Vsieve Y ≤ MeSum D Y := by
  intro Y hY D hD
  have hYD : (Y:ℝ) ≤ D := by
    have h1 : (1:ℝ) ≤ (Y:ℝ) := by exact_mod_cast (by omega : 1 ≤ Y)
    have h2 : (Y:ℝ) ≤ (Y:ℝ)^3 := by
      have := pow_le_pow_right₀ h1 (by norm_num : 1 ≤ (3:ℕ))
      simpa using this
    linarith
  have h1 : Wm D Y ≤ EmSum D Y := Wm_le_EmSum D Y
  have h2 := h Y hY D hD
  have h3 : MeSum D Y = Vsieve Y - Wm D Y := by unfold Wm; ring
  have hrw : (1 - c₀) * Vsieve Y = Vsieve Y - c₀ * Vsieve Y := by ring
  rw [h3, hrw] at *
  linarith

/-! ### The exact profiles at the first three levels

The two deficits are *identically zero* at the levels `3` and `5` (as long as `D ≥ 3`), and at
level `5` the surplus `Wp` is already the step function `1/2` on `D < 9`, `0` afterwards.  These
are the "small-level" data that any level-aware profile argument needs: the universal
(level-independent) profile systematically over-estimates the deficit at these levels, and it is
exactly that over-estimate that makes the naive level-independent profile system inconsistent
(see the state notes). -/

lemma vsieve_four : Vsieve 4 = 1/2 := by
  have h := Vsieve_succ_of_prime (q := 3) (by norm_num) (by norm_num)
  rw [Vsieve_three] at h
  norm_num at h
  simpa using h

lemma vsieve_five : Vsieve 5 = 1/2 := by
  have h := Vsieve_succ_of_not_prime (q := 4) (by norm_num)
  rw [vsieve_four] at h
  simpa using h

lemma vsieve_six : Vsieve 6 = 3/8 := by
  have h := Vsieve_succ_of_prime (q := 5) (by norm_num) (by norm_num)
  rw [vsieve_five] at h
  norm_num at h
  simpa using h

lemma vsieve_seven : Vsieve 7 = 3/8 := by
  have h := Vsieve_succ_of_not_prime (q := 6) (by norm_num)
  rw [vsieve_six] at h
  simpa using h

lemma oddPrimesLt_three : oddPrimesLt 3 = ∅ := by decide
lemma oddPrimesLt_five : oddPrimesLt 5 = {3} := by decide
lemma oddPrimesLt_seven : oddPrimesLt 7 = {3, 5} := by decide

lemma totient_three : (Nat.totient 3 : ℝ) = 2 := by
  rw [Nat.totient_prime (by norm_num : Nat.Prime 3)]; norm_num

lemma MeSum_three (D : ℝ) : MeSum D 3 = 1 := by
  rw [MeSum_rec, oddPrimesLt_three, Finset.sum_empty, sub_zero]

lemma MpSum_three (D : ℝ) : MpSum D 3 = 1 := by
  rw [MpSum_rec, oddPrimesLt_three, Finset.sum_empty, sub_zero]

lemma Wm_three (D : ℝ) : Wm D 3 = 0 := by
  unfold Wm; rw [MeSum_three, Vsieve_three]; ring

lemma Wp_three (D : ℝ) : Wp D 3 = 0 := by
  unfold Wp; rw [MpSum_three, Vsieve_three]; ring

lemma MpSum_five (D : ℝ) :
    MpSum D 5 = 1 - (if ((3:ℕ):ℝ)^((1:ℝ)+1) ≤ D then 1/2 else 0) := by
  rw [MpSum_rec, oddPrimesLt_five, Finset.sum_singleton, MeSum_three]
  rw [totient_three]
  norm_num

lemma MeSum_five (D : ℝ) :
    MeSum D 5 = 1 - (if ((3:ℕ):ℝ) ≤ D then 1/2 else 0) := by
  rw [MeSum_rec, oddPrimesLt_five, Finset.sum_singleton, MpSum_three]
  rw [totient_three]
  norm_num

lemma Wm_five (D : ℝ) (hD : (3:ℝ) ≤ D) : Wm D 5 = 0 := by
  have hD' : ((3:ℕ):ℝ) ≤ D := hD
  unfold Wm; rw [MeSum_five, if_pos hD', vsieve_five]; norm_num

lemma Wp_five (D : ℝ) :
    Wp D 5 = if ((3:ℕ):ℝ)^((1:ℝ)+1) ≤ D then 0 else 1/2 := by
  unfold Wp; rw [MpSum_five, vsieve_five]
  by_cases h : ((3:ℕ):ℝ)^((1:ℝ)+1) ≤ D
  · rw [if_pos h, if_pos h]; norm_num
  · rw [if_neg h, if_neg h]; norm_num

lemma MpSum_seven (D : ℝ) :
    MpSum D 7 = 1 - (if ((3:ℕ):ℝ)^((1:ℝ)+1) ≤ D then 1/2 else 0)
      - (if ((5:ℕ):ℝ)^((1:ℝ)+1) ≤ D then 1/4 * (1 - (if ((3:ℕ):ℝ) ≤ D/5 then 1/2 else 0)) else 0) := by
  rw [MpSum_rec, oddPrimesLt_seven, Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [MeSum_three, MeSum_five]
  have h5 : (Nat.totient 5 : ℝ) = 4 := by
    rw [Nat.totient_prime (by norm_num : Nat.Prime 5)]; norm_num
  rw [h5, totient_three]
  ring

/-! ### The elementary integral `∫_q^{q+1} dt/(t log² t)`

This is the one calculus input of the staircase comparison used to turn the discrete
`Vsieve_abel_sharp` staircase into the delay-equation integral. -/

/-- `∫_q^{q+1} dt / (t (log t)^2) = 1/log q - 1/log(q+1)` for `q ≥ 4`, via the antiderivative
`t ↦ -1/log t`. -/
lemma integral_inv_mul_log_sq (q : ℕ) (hq : 4 ≤ q) :
    ∫ t in (q:ℝ)..((q:ℝ)+1), 1/(t * (Real.log t)^2)
      = 1/Real.log (q:ℝ) - 1/Real.log ((q:ℝ)+1) := by
  have hq4 : (4:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have hderiv : ∀ t ∈ Set.uIcc (q:ℝ) ((q:ℝ)+1),
      HasDerivAt (fun s : ℝ => -(Real.log s)⁻¹) (1/(t * (Real.log t)^2)) t := by
    intro t ht
    rw [Set.mem_uIcc] at ht
    have ht1 : (1:ℝ) < t := by
      rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
    have hlog : Real.log t ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
    have h1 : HasDerivAt (fun s : ℝ => Real.log s) t⁻¹ t :=
      Real.hasDerivAt_log (by linarith)
    have h2 := h1.inv hlog
    have h3 : HasDerivAt (-(fun s : ℝ => (Real.log s)⁻¹)) (-(-t⁻¹ / (Real.log t)^2)) t := h2.neg
    have heq : -(-t⁻¹ / (Real.log t)^2) = 1/(t * (Real.log t)^2) := by
      field_simp
    have hfn : (fun s : ℝ => -(Real.log s)⁻¹) = -(fun s : ℝ => (Real.log s)⁻¹) := by
      funext s
      rfl
    rw [hfn, ← heq]
    exact h3
  have hcont : ContinuousOn (fun t : ℝ => 1/(t * (Real.log t)^2)) (Set.uIcc (q:ℝ) ((q:ℝ)+1)) := by
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · refine ContinuousOn.mul continuousOn_id ?_
      refine ContinuousOn.pow ?_ 2
      refine Real.continuousOn_log.mono ?_
      intro x hx
      rw [Set.mem_compl_iff, Set.mem_singleton_iff]
      rw [Set.mem_uIcc] at hx
      rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
    · intro x hx
      rw [Set.mem_uIcc] at hx
      have hx1 : (1:ℝ) < x := by rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
      have hxp : 0 < x := by linarith
      have hxl : 0 < Real.log x := Real.log_pos hx1
      exact ne_of_gt (by positivity)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  rw [one_div, one_div]
  ring

/-! ### The staircase comparison: `Σ Φ(q)(1/log q − 1/log(q+1)) = ∫ Φ(⌊t⌋₊)/(t log² t)`

This is the bridge that turns the discrete staircase of `Vsieve_abel_sharp` into the integral
which, after the substitution `t = Y^{σ/(w+1)}`, becomes the delay-equation recursion
`σ f_n(σ) = ∫_σ^∞ f_{n−1}(t−1) dt` of the linear sieve. -/

/-- The staircase function `t ↦ Φ ⌊t⌋₊ / (t log² t)`. -/
def stairFun (Φ : ℕ → ℝ) : ℝ → ℝ := fun t => (Φ ⌊t⌋₊) / (t * (Real.log t)^2)

private lemma ae_ne_single (c : ℝ) : ∀ᵐ t : ℝ ∂MeasureTheory.volume, t ≠ c := by
  rw [MeasureTheory.ae_iff]
  have h : {t : ℝ | ¬ t ≠ c} = {c} := by ext t; simp
  rw [h]
  exact MeasureTheory.measure_singleton c

private lemma floor_eq_of_mem_Ioc {q : ℕ} {t : ℝ} (h1 : (q:ℝ) < t) (h2 : t < (q:ℝ)+1) :
    ⌊t⌋₊ = q := by
  have hq0 : (0:ℝ) ≤ (q:ℝ) := by positivity
  rw [Nat.floor_eq_iff (le_trans hq0 (le_of_lt h1))]
  constructor <;> linarith

/-- Integrability of the staircase on a unit interval `[q, q+1]`, `q ≥ 4`. -/
theorem intervalIntegrable_stairFun (q : ℕ) (hq : 4 ≤ q) (Φ : ℕ → ℝ) :
    IntervalIntegrable (stairFun Φ) MeasureTheory.volume (q:ℝ) ((q:ℝ)+1) := by
  have hq4 : (4:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have hden : ∀ x ∈ Set.uIcc (q:ℝ) ((q:ℝ)+1), x * (Real.log x)^2 ≠ 0 := by
    intro x hx
    rw [Set.mem_uIcc] at hx
    have hx1 : (1:ℝ) < x := by rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
    have hxl : 0 < Real.log x := Real.log_pos hx1
    exact ne_of_gt (by positivity)
  have hconst : IntervalIntegrable (fun t : ℝ => (Φ q) / (t * (Real.log t)^2))
      MeasureTheory.volume (q:ℝ) ((q:ℝ)+1) := by
    apply ContinuousOn.intervalIntegrable
    exact ContinuousOn.div continuousOn_const (ContinuousOn.mul continuousOn_id
      (ContinuousOn.pow (Real.continuousOn_log.mono (by
        intro x hx
        rw [Set.mem_compl_iff, Set.mem_singleton_iff]
        rw [Set.mem_uIcc] at hx
        rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith)) 2)) hden
  refine hconst.congr_ae ?_
  change ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.uIoc (q:ℝ) ((q:ℝ)+1))),
    (Φ q) / (t * (Real.log t)^2) = stairFun Φ t
  rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [ae_ne_single ((q:ℝ)+1)] with t ht hmem
  rw [Set.uIoc_of_le (by push_cast; linarith)] at hmem
  have hlt : t < (q:ℝ)+1 := lt_of_le_of_ne hmem.2 (fun hc => ht hc)
  have hfloor : ⌊t⌋₊ = q := floor_eq_of_mem_Ioc hmem.1 hlt
  simp only [stairFun, hfloor]

/-- The `q`-th step: `∫_q^{q+1} stairFun = Φ(q)(1/log q - 1/log(q+1))`. -/
theorem integral_stairFun_single (q : ℕ) (hq : 4 ≤ q) (Φ : ℕ → ℝ) :
    ∫ t in (q:ℝ)..((q:ℝ)+1), stairFun Φ t
      = Φ q * (1/Real.log (q:ℝ) - 1/Real.log ((q+1:ℕ):ℝ)) := by
  have hcongr : ∫ t in (q:ℝ)..((q:ℝ)+1), stairFun Φ t
      = ∫ t in (q:ℝ)..((q:ℝ)+1), (Φ q) * ((t * (Real.log t)^2))⁻¹ := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [ae_ne_single ((q:ℝ)+1)] with t ht hmem
    rw [Set.uIoc_of_le (by push_cast; linarith)] at hmem
    have hlt : t < (q:ℝ)+1 := lt_of_le_of_ne hmem.2 (fun hc => ht hc)
    have hfloor : ⌊t⌋₊ = q := floor_eq_of_mem_Ioc hmem.1 hlt
    simp only [stairFun, hfloor, div_eq_mul_inv]
  have h2 : ∫ t in (q:ℝ)..((q:ℝ)+1), (Φ q) * ((t * (Real.log t)^2))⁻¹
      = (Φ q) * ∫ t in (q:ℝ)..((q:ℝ)+1), ((t * (Real.log t)^2))⁻¹ :=
    intervalIntegral.integral_const_mul (Φ q) _
  have h3 : (∫ t in (q:ℝ)..((q:ℝ)+1), ((t * (Real.log t)^2))⁻¹)
      = ∫ t in (q:ℝ)..((q:ℝ)+1), 1/(t * (Real.log t)^2) :=
    intervalIntegral.integral_congr (fun t _ => by rw [one_div])
  rw [hcongr, h2, h3, integral_inv_mul_log_sq q hq]
  congr 1
  push_cast
  ring

/-- **Staircase = integral.**  For `3 ≤ w` and `w+1 ≤ Y`,
`∫_{w+1}^{Y} Φ(⌊t⌋₊)/(t log² t) dt = Σ_{w+1 ≤ q ≤ Y-1} Φ(q)(1/log q - 1/log(q+1))`. -/
theorem integral_staircase (w : ℕ) (hw : 3 ≤ w) (Φ : ℕ → ℝ) :
    ∀ Y : ℕ, w + 1 ≤ Y →
      IntervalIntegrable (stairFun Φ) MeasureTheory.volume ((w:ℝ)+1) (Y:ℝ) ∧
      ∫ t in ((w:ℝ)+1)..(Y:ℝ), stairFun Φ t
        = ∑ q ∈ Finset.Icc (w+1) (Y-1),
            Φ q * (1/Real.log (q:ℝ) - 1/Real.log ((q+1:ℕ):ℝ)) := by
  intro Y hY
  induction Y, hY using Nat.le_induction with
  | base =>
      have hbase : ((w:ℝ)+1) = ((w+1 : ℕ) : ℝ) := by push_cast; ring
      have h0 : Finset.Icc (w+1) (w+1-1) = ∅ :=
        Finset.Icc_eq_empty_iff.mpr (by omega)
      constructor
      · rw [hbase]
      · rw [hbase, h0, Finset.sum_empty, intervalIntegral.integral_same]
  | succ n hn ih =>
      obtain ⟨hint, hval⟩ := ih
      have hn4 : 4 ≤ n := by omega
      have hsingle_int := intervalIntegrable_stairFun n hn4 Φ
      have hsingle := integral_stairFun_single n hn4 Φ
      have hn1 : ((n+1 : ℕ) : ℝ) = (n:ℝ)+1 := by push_cast; ring
      have hsum : ∑ q ∈ Finset.Icc (w+1) n,
            Φ q * (1/Real.log (q:ℝ) - 1/Real.log ((q+1:ℕ):ℝ))
          = (∑ q ∈ Finset.Icc (w+1) (n-1),
              Φ q * (1/Real.log (q:ℝ) - 1/Real.log ((q+1:ℕ):ℝ)))
            + Φ n * (1/Real.log (n:ℝ) - 1/Real.log ((n+1:ℕ):ℝ)) := by
        have h := Finset.sum_Icc_succ_top (a := w+1) (b := n-1)
          (by omega : w+1 ≤ n-1+1) (fun q => Φ q * (1/Real.log (q:ℝ) - 1/Real.log ((q+1:ℕ):ℝ)))
        rwa [show n - 1 + 1 = n from by omega] at h
      constructor
      · rw [hn1]
        exact hint.trans hsingle_int
      · rw [hn1, ← intervalIntegral.integral_add_adjacent_intervals hint hsingle_int,
          hval, hsingle, show n + 1 - 1 = n from by omega, hsum]

/-- **Sharpened Abel bound, integral form.**  For `4 ≤ w`, `w+1 ≤ Y`, `Φ` monotone with
`Φ w = 0` and `Φ ≥ 0`, and `C ≥ sup_{w ≤ t ≤ Y} Vsieve t log t`:
```
Σ_{w ≤ q < Y, q odd prime} (1/(q−1)) V(q) Φ(q)
   ≤ Φ(Y)(C/log Y − V(Y)) + C ∫_w^Y Φ(⌊t⌋₊)/(t log² t) dt.
```
This is the form in which the bound is used in the layer (delay-equation) induction: it carries
no `K`-hypothesis, the small-prime deviation being absorbed by `C` taken over the *effective*
range. -/
theorem Vsieve_abel_integral (Y w : ℕ) (hY : 3 ≤ Y) (hw : 4 ≤ w) (hwY : w + 1 ≤ Y)
    (C : ℝ) (hC : ∀ t : ℕ, w ≤ t → t ≤ Y → Vsieve t * Real.log (t:ℝ) ≤ C)
    (Φ : ℕ → ℝ) (hmono : Monotone Φ) (hΦw : Φ w = 0) (hΦ0 : ∀ q, 0 ≤ Φ q) :
    ∑ q ∈ (oddPrimesLt Y).filter (fun q => w ≤ q), (1/((q:ℝ)-1)) * Vsieve q * Φ q
      ≤ Φ Y * (C / Real.log (Y:ℝ) - Vsieve Y)
        + C * ∫ t in (w:ℝ)..(Y:ℝ), stairFun Φ t := by
  have hw3 : 3 ≤ w := by omega
  have hpos : 0 < C := by
    have := hC w le_rfl (by omega)
    have hV : 0 < Vsieve w := Vsieve_pos w
    have hl : 0 < Real.log (w:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < w))
    nlinarith
  have h1 := Vsieve_abel_sharp Y w hY hw3 (by omega) C hC Φ hmono hΦw
  obtain ⟨hint, hval⟩ := integral_staircase w hw3 Φ Y hwY
  rw [← hval] at h1
  refine le_trans h1 (add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ (le_of_lt hpos)))
  -- `∫_{w+1}^Y ≤ ∫_w^Y` for a nonnegative integrand
  have hInt_w : IntervalIntegrable (stairFun Φ) MeasureTheory.volume (w:ℝ) ((w:ℝ)+1) :=
    intervalIntegrable_stairFun w hw Φ
  have hInt : IntervalIntegrable (stairFun Φ) MeasureTheory.volume (w:ℝ) (Y:ℝ) :=
    hInt_w.trans hint
  refine intervalIntegral.integral_mono_interval (by push_cast; linarith)
    (by exact_mod_cast hwY) le_rfl ?_ hInt
  refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr ?_
  have hw4 : (4:ℝ) ≤ (w:ℝ) := by exact_mod_cast hw
  filter_upwards with t ht
  rw [Set.mem_Ioc] at ht
  have ht0 : 0 < t := by linarith [ht.1, hw4]
  have hlog : 0 < Real.log t := Real.log_pos (by linarith [ht.1, hw4])
  simp only [stairFun]
  exact div_nonneg (hΦ0 _) (by positivity)

/-! ### The delay-difference functions of the linear sieve

The layer (Buchstab) induction of the linear sieve produces, at step `n`, the recursion
`s·f_{n+1}(s) = ∫_s^{n+4} f_n(t-1) dt`, with `f_1(s) = (3-s)/s` on `0 < s < 3` — the classical
delay-difference equation of the linear sieve (Nathanson, Ch. 9; Bordignon, arXiv:2007.08774).

**The lower limit is clamped at `2`.**  `f_1(u) = (3-u)/u` behaves like `3/u` near `u = 0`, so
`∫_s^{n+4} f_n(t-1) dt` *diverges* for `s ≤ 2`: the recursion is only meaningful from `2` on.
Clamping the lower limit to `max s 2` therefore (i) agrees with the classical recursion on
`s ≥ 2`, (ii) makes `f_{n+1}(s) = (∫_2^{n+4} f_n(t-1))/(s)` for `s ≤ 2`, which is *decreasing in
`s`* — exactly what the direction of the layer estimate needs.  With the unclamped definition
one would get `f_{n+1}(s) = 0` for `s ≤ 2` (the Bochner integral of a non-integrable function
being `0`), destroying antitonicity at `s = 2`.

The indexing is shifted by one from the classical one: `delayFn 0 = f_1`, and `delayFn n` is
supported on `0 ≤ s ≤ n+3`. -/

/-- The delay-difference functions of the linear sieve (clamped at `s = 2` so that the
recursion's integral always starts at `max s 2`). -/
noncomputable def delayFn : ℕ → ℝ → ℝ
  | 0 => fun s => if 0 < s ∧ s < 3 then (3 - s) / s else 0
  | (n + 1) => fun s => if 1 ≤ s ∧ s ≤ (n : ℝ) + 4 then
      (∫ t in max s 2..((n : ℝ) + 4), delayFn n (t - 1)) / s else 0

@[simp] lemma delayFn_zero_eq (s : ℝ) :
    delayFn 0 s = if 0 < s ∧ s < 3 then (3 - s) / s else 0 := rfl

@[simp] lemma delayFn_succ_eq (n : ℕ) (s : ℝ) :
    delayFn (n + 1) s = if 1 ≤ s ∧ s ≤ (n : ℝ) + 4 then
      (∫ t in max s 2..((n : ℝ) + 4), delayFn n (t - 1)) / s else 0 := rfl

/-- The classical recursion, valid on `s ≥ 2`. -/
theorem delayFn_mul_eq (n : ℕ) (s : ℝ) (h1 : 2 ≤ s) (h2 : s ≤ (n : ℝ) + 4) :
    s * delayFn (n + 1) s = ∫ t in s..((n : ℝ) + 4), delayFn n (t - 1) := by
  rw [delayFn_succ_eq, if_pos ⟨by linarith, h2⟩, max_eq_left h1, mul_div_cancel₀]
  exact ne_of_gt (by linarith)

theorem delayFn_nonneg_and_zero : ∀ n : ℕ,
    (∀ s : ℝ, s ≤ 0 → delayFn n s = 0) ∧ (∀ s : ℝ, 0 ≤ delayFn n s) := by
  intro n
  induction n with
  | zero =>
      refine ⟨fun s hs => ?_, fun s => ?_⟩
      · rw [delayFn_zero_eq, if_neg (fun hc => absurd hc.1 (not_lt.mpr hs))]
      · by_cases h : 0 < s ∧ s < 3
        · rw [delayFn_zero_eq, if_pos h]
          exact div_nonneg (by linarith [h.2]) (le_of_lt h.1)
        · rw [delayFn_zero_eq, if_neg h]
  | succ n ih =>
      refine ⟨fun s hs => ?_, fun s => ?_⟩
      · rw [delayFn_succ_eq, if_neg (fun hc => absurd hc.1 (by linarith : ¬ (1 ≤ s)))]
      · by_cases h : 1 ≤ s ∧ s ≤ (n : ℝ) + 4
        · rw [delayFn_succ_eq, if_pos h]
          refine div_nonneg ?_ (by linarith)
          have hmax : max s 2 ≤ (n : ℝ) + 4 :=
            max_le h.2 (by have hc : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n; linarith : (2:ℝ) ≤ (n:ℝ) + 4)
          refine intervalIntegral.integral_nonneg_of_forall hmax ?_
          intro u
          exact ih.2 (u - 1)
        · rw [delayFn_succ_eq, if_neg h]

theorem delayFn_eq_zero_of_ge : ∀ n : ℕ, ∀ s : ℝ, (n : ℝ) + 3 ≤ s → delayFn n s = 0 := by
  intro n
  induction n with
  | zero =>
      intro s hs
      have hs' : (3:ℝ) ≤ s := by simpa using hs
      rw [delayFn_zero_eq, if_neg (fun hc => absurd hc.2 (not_lt.mpr hs'))]
  | succ n ih =>
      intro s hs
      have h1 : (n : ℝ) + 4 ≤ s := by push_cast at hs ⊢; linarith
      by_cases hlt : s = (n : ℝ) + 4
      · have hmax : max ((n : ℝ) + 4) 2 = (n : ℝ) + 4 :=
          max_eq_left (by have hc : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n; linarith : (2:ℝ) ≤ (n:ℝ) + 4)
        rw [hlt, delayFn_succ_eq, if_pos ⟨by linarith, le_rfl⟩, hmax,
          intervalIntegral.integral_same, zero_div]
      · have hgt : (n : ℝ) + 4 < s := lt_of_le_of_ne h1 (Ne.symm hlt)
        rw [delayFn_succ_eq, if_neg (fun hc => absurd hc.2 (not_le.mpr hgt))]


/-! ### Continuity and antitonicity of `delayFn`

`delayFn n` is continuous on the whole range of its support `[1, n+3]` (the successor step
identifies `delayFn (n+1)` on `[1, n+4]` with `max ((∫_{max s 2}^{n+4} delayFn n(t-1))/s) 0`
and uses `intervalIntegral.continuousOn_primitive_interval_left`), and it is non-increasing
there.  Antitonicity is what fixes the *direction* of the layer estimate: the staircase
`Φ(⌊t⌋₊) = f_{n−1}(σ log Y/log⌊t⌋₊ − 1)` must majorize `f_{n−1}(σ log Y/log t − 1)`, which holds
because `⌊t⌋₊ ≤ t` pushes the argument up and `f_{n−1}` is non-increasing. -/

/-- `delayFn n` is continuous on the whole range of its support `[1, n+3]`. -/
theorem delayFn_continuousOn : ∀ n : ℕ, ContinuousOn (delayFn n) (Set.Icc 1 ((n : ℝ) + 3)) := by
  intro n
  induction n with
  | zero =>
      have hnc : ((0:ℕ) : ℝ) + 3 = (3:ℝ) := by norm_num
      rw [hnc]
      have hmax : ContinuousOn (fun s : ℝ => max ((3 - s)/s) 0) (Set.Icc 1 (3:ℝ)) := by
        refine ContinuousOn.sup ?_ continuousOn_const
        refine ContinuousOn.div (continuousOn_const.sub continuousOn_id) continuousOn_id ?_
        intro s hs
        rw [Set.mem_Icc] at hs
        exact ne_of_gt (by linarith [hs.1])
      refine hmax.congr ?_
      intro s hs
      change delayFn 0 s = max ((3 - s)/s) 0
      rw [Set.mem_Icc] at hs
      by_cases h : s < 3
      · rw [delayFn_zero_eq, if_pos ⟨by linarith [hs.1], h⟩, max_eq_left]
        exact div_nonneg (by linarith : (0:ℝ) ≤ 3 - s) (by linarith [hs.1] : (0:ℝ) ≤ s)
      · push Not at h
        rw [delayFn_zero_eq, if_neg (fun hc => absurd hc.2 (not_lt.mpr h)), max_eq_right]
        exact div_nonpos_of_nonpos_of_nonneg (by linarith : 3 - s ≤ 0) (by linarith [hs.1] : (0:ℝ) ≤ s)
  | succ n ih =>
      have hidx : (((n+1:ℕ)) : ℝ) + 3 = (n : ℝ) + 4 := by push_cast; ring
      rw [hidx]
      have hg : ContinuousOn (fun t : ℝ => delayFn n (t - 1)) (Set.uIcc 2 ((n:ℝ) + 4)) := by
        refine ih.comp ?_ ?_
        · exact continuousOn_id.sub continuousOn_const
        · intro t ht
          rw [Set.mem_uIcc] at ht
          rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · change t - 1 ∈ Set.Icc 1 ((n:ℝ) + 3)
            rw [Set.mem_Icc]
            constructor <;> linarith
          · change t - 1 ∈ Set.Icc 1 ((n:ℝ) + 3)
            rw [Set.mem_Icc]
            constructor <;> linarith
      have hInt : MeasureTheory.IntegrableOn (fun t : ℝ => delayFn n (t - 1)) (Set.uIcc 2 ((n:ℝ) + 4)) :=
        hg.integrableOn_Icc
      have hprim : ContinuousOn (fun u : ℝ => ∫ t in u..((n:ℝ) + 4), delayFn n (t - 1))
          (Set.uIcc 2 ((n:ℝ) + 4)) :=
        intervalIntegral.continuousOn_primitive_interval_left hInt
      have hmaxc : ContinuousOn (fun s : ℝ =>
          max ((∫ t in max s 2..((n:ℝ) + 4), delayFn n (t - 1))/s) 0)
          (Set.Icc 1 ((n:ℝ) + 4)) := by
        refine ContinuousOn.sup (ContinuousOn.div ?_ continuousOn_id ?_) continuousOn_const
        · refine hprim.comp (continuousOn_id.sup continuousOn_const) ?_
          intro s hs
          rw [Set.mem_Icc] at hs
          change max s 2 ∈ Set.uIcc 2 ((n:ℝ) + 4)
          rw [Set.mem_uIcc]
          exact Or.inl ⟨le_max_right _ _,
            max_le hs.2 (by have hc : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n; linarith)⟩
        · intro s hs
          rw [Set.mem_Icc] at hs
          exact ne_of_gt (by linarith [hs.1])
      refine hmaxc.congr ?_
      intro s hs
      change delayFn (n + 1) s = max ((∫ t in max s 2..((n:ℝ) + 4), delayFn n (t - 1))/s) 0
      rw [Set.mem_Icc] at hs
      have hnn : 0 ≤ (∫ t in max s 2..((n:ℝ) + 4), delayFn n (t - 1))/s := by
        refine div_nonneg ?_ (by linarith [hs.1])
        refine intervalIntegral.integral_nonneg_of_forall ?_
          (fun u => (delayFn_nonneg_and_zero n).2 (u - 1))
        exact max_le hs.2 (by have hc : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n; linarith)
      rw [delayFn_succ_eq, if_pos ⟨hs.1, hs.2⟩, max_eq_left hnn]

end
end Commons.NumberTheory.Chen

namespace Commons.NumberTheory.Chen

noncomputable section

lemma delayFn_zero_eq_div (s : ℝ) (h1 : 0 < s) (h2 : s ≤ 3) : delayFn 0 s = (3 - s)/s := by
  rw [delayFn_zero_eq]
  by_cases h : s < 3
  · rw [if_pos ⟨h1, h⟩]
  · rw [if_neg (fun hc => absurd hc.2 h)]
    have hs3 : s = 3 := le_antisymm h2 (not_lt.mp h)
    rw [hs3]; norm_num

/-- **Antitonicity.**  `delayFn n` is non-increasing on the range of its support. -/
theorem delayFn_antitone : ∀ n : ℕ, AntitoneOn (delayFn n) (Set.Icc 1 ((n : ℝ) + 3)) := by
  intro n
  induction n with
  | zero =>
      have hnc : ((0:ℕ) : ℝ) + 3 = (3:ℝ) := by norm_num
      rw [hnc]
      intro a ha b hb hab
      rw [Set.mem_Icc] at ha hb
      rw [delayFn_zero_eq_div b (by linarith [hb.1]) hb.2,
          delayFn_zero_eq_div a (by linarith [ha.1]) (by linarith [hab, hb.2])]
      rw [div_le_div_iff₀ (by linarith [hb.1] : (0:ℝ) < b) (by linarith [ha.1] : (0:ℝ) < a)]
      nlinarith
  | succ n ih =>
      have hidx : (((n+1:ℕ)) : ℝ) + 3 = (n : ℝ) + 4 := by push_cast; ring
      rw [hidx]
      intro a ha b hb hab
      rw [Set.mem_Icc] at ha hb
      have hg : ContinuousOn (fun t : ℝ => delayFn n (t - 1)) (Set.uIcc 2 ((n:ℝ) + 4)) := by
        refine delayFn_continuousOn n |>.comp ?_ ?_
        · exact continuousOn_id.sub continuousOn_const
        · intro t ht
          rw [Set.mem_uIcc] at ht
          rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · change t - 1 ∈ Set.Icc 1 ((n:ℝ) + 3)
            rw [Set.mem_Icc]; constructor <;> linarith
          · change t - 1 ∈ Set.Icc 1 ((n:ℝ) + 3)
            rw [Set.mem_Icc]; constructor <;> linarith
      have hInt : IntervalIntegrable (fun t : ℝ => delayFn n (t - 1)) MeasureTheory.volume
          2 ((n:ℝ) + 4) := hg.intervalIntegrable
      have hnn : ∀ u : ℝ, 0 ≤ delayFn n (u - 1) := fun u => (delayFn_nonneg_and_zero n).2 (u - 1)
      have hL : (2:ℝ) ≤ (n:ℝ) + 4 := by have hc : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n; linarith
      have hform : ∀ s : ℝ, 1 ≤ s → s ≤ (n:ℝ) + 4 →
          delayFn (n+1) s = (∫ t in max s 2..((n:ℝ) + 4), delayFn n (t - 1))/s := by
        intro s h1 h2
        rw [delayFn_succ_eq, if_pos ⟨h1, h2⟩]
      rw [hform b hb.1 hb.2, hform a ha.1 ha.2]
      have hC : 0 ≤ ∫ t in (2:ℝ)..((n:ℝ) + 4), delayFn n (t - 1) :=
        intervalIntegral.integral_nonneg_of_forall hL hnn
      by_cases hb2 : b ≤ 2
      · -- `b ≤ 2`: same numerator, `1/b ≤ 1/a`
        rw [max_eq_right (le_trans hab hb2), max_eq_right hb2]
        rw [div_le_div_iff₀ (by linarith [hb.1] : (0:ℝ) < b) (by linarith [ha.1] : (0:ℝ) < a)]
        nlinarith
      · push Not at hb2
        by_cases ha2 : a ≤ 2
        · -- `a ≤ 2 < b`
          rw [max_eq_right ha2, max_eq_left (le_of_lt hb2)]
          have hmono : ∫ t in b..((n:ℝ) + 4), delayFn n (t - 1)
              ≤ ∫ t in (2:ℝ)..((n:ℝ) + 4), delayFn n (t - 1) :=
            intervalIntegral.integral_mono_interval (le_of_lt hb2) hb.2 le_rfl
              (Filter.Eventually.of_forall hnn) hInt
          rw [div_le_div_iff₀ (by linarith [hb.1] : (0:ℝ) < b) (by linarith [ha.1] : (0:ℝ) < a)]
          have hA : 0 ≤ ∫ t in b..((n:ℝ) + 4), delayFn n (t - 1) :=
            intervalIntegral.integral_nonneg_of_forall hb.2 hnn
          nlinarith
        · push Not at ha2
          -- `2 < a ≤ b`: `∫_a^L g ≥ ∫_b^L g`
          rw [max_eq_left (le_of_lt ha2), max_eq_left (le_of_lt hb2)]
          have hmono : ∫ t in b..((n:ℝ) + 4), delayFn n (t - 1)
              ≤ ∫ t in a..((n:ℝ) + 4), delayFn n (t - 1) :=
            intervalIntegral.integral_mono_interval hab hb.2 le_rfl
              (Filter.Eventually.of_forall hnn)
              (hInt.mono_set (by
                rw [Set.uIcc_of_le (by linarith : a ≤ (n:ℝ) + 4), Set.uIcc_of_le hL]
                exact Set.Icc_subset_Icc_left (le_of_lt ha2)))
          have hA : 0 ≤ ∫ t in b..((n:ℝ) + 4), delayFn n (t - 1) :=
            intervalIntegral.integral_nonneg_of_forall hb.2 hnn
          rw [div_le_div_iff₀ (by linarith [hb.1] : (0:ℝ) < b) (by linarith [ha.1] : (0:ℝ) < a)]
          nlinarith


/-! ### The change of variables of the delay equation

Substituting `w = σ log Y/log t - 1` (i.e. `t = Y^{σ/(w+1)}`), so that
`dt/(t log² t) = -dw/(σ log Y)`, turns the staircase integral of `Vsieve_abel_integral` into a
plain integral of `g` over the corresponding `w`-interval (reversed, `w` being decreasing in `t`).
This is the step that produces `f_n(σ) = (1/σ)∫_{σ-1}^∞ f_{n-1}` from the Abel estimate. -/

theorem integral_subst_log_div (Y σ a b : ℝ) (hY : 1 < Y) (hσ : 0 < σ)
    (ha : 1 < a) (hab : a ≤ b) (g : ℝ → ℝ)
    (hg : ContinuousOn g (Set.uIcc (σ * Real.log Y / Real.log b - 1)
      (σ * Real.log Y / Real.log a - 1))) :
    (∫ t in a..b, g (σ * Real.log Y / Real.log t - 1) / (t * (Real.log t)^2))
      = (1 / (σ * Real.log Y)) *
        ∫ w in (σ * Real.log Y / Real.log b - 1)..(σ * Real.log Y / Real.log a - 1), g w := by
  have hlogY : 0 < Real.log Y := Real.log_pos hY
  have hσY : 0 < σ * Real.log Y := mul_pos hσ hlogY
  have hne : (σ * Real.log Y) ≠ 0 := ne_of_gt hσY
  have h1a : (0:ℝ) < a := by linarith
  have hlog1 : ∀ t : ℝ, a ≤ t → 0 < Real.log t := by
    intro t ht
    exact Real.log_pos (by linarith)
  -- derivative of the substitution
  have hderiv : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun s => σ * Real.log Y / Real.log s - 1)
        (-(σ * Real.log Y) / (t * (Real.log t)^2)) t := by
    intro t ht
    rw [Set.mem_uIcc] at ht
    have ht1 : a ≤ t := by rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
    have ht0 : 0 < t := by linarith
    have hlt1 : Real.log t ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one ht0 (by linarith)
    have h1 : HasDerivAt (fun s : ℝ => Real.log s) t⁻¹ t := Real.hasDerivAt_log (ne_of_gt ht0)
    have h2 : HasDerivAt (fun s : ℝ => (Real.log s)⁻¹) (-(t⁻¹) / (Real.log t)^2) t :=
      h1.inv hlt1
    have h3 : HasDerivAt (fun s : ℝ => (σ * Real.log Y) * (Real.log s)⁻¹ - 1)
        ((σ * Real.log Y) * (-(t⁻¹) / (Real.log t)^2)) t := by
      have h4 := ((hasDerivAt_const (x := t) (c := σ * Real.log Y)).mul h2).sub
        (hasDerivAt_const (x := t) (c := (1:ℝ)))
      have h5 : ((fun _ : ℝ => σ * Real.log Y) * fun s : ℝ => (Real.log s)⁻¹)
            - (fun _ : ℝ => (1:ℝ))
          = fun s : ℝ => (σ * Real.log Y) * (Real.log s)⁻¹ - 1 := by
        funext s; simp [Pi.mul_apply, Pi.sub_apply]
      have h6 : (0 * (Real.log t)⁻¹ + (σ * Real.log Y) * (-(t⁻¹) / (Real.log t)^2) - 0)
          = (σ * Real.log Y) * (-(t⁻¹) / (Real.log t)^2) := by ring
      rw [h5, h6] at h4
      exact h4
    have hfun : (fun s : ℝ => σ * Real.log Y / Real.log s - 1)
        = (fun s : ℝ => (σ * Real.log Y) * (Real.log s)⁻¹ - 1) := by
      funext s; rw [div_eq_mul_inv]
    have hval : (σ * Real.log Y) * (-(t⁻¹) / (Real.log t)^2)
        = -(σ * Real.log Y) / (t * (Real.log t)^2) := by
      field_simp
    rw [← hfun, hval] at h3
    exact h3
  have hcont_f' : ContinuousOn (fun t : ℝ => -(σ * Real.log Y) / (t * (Real.log t)^2))
      (Set.uIcc a b) := by
    have hpos : ∀ x ∈ Set.uIcc a b, 0 < x := by
      intro x hx
      rw [Set.mem_uIcc] at hx
      rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · refine ContinuousOn.mul continuousOn_id ?_
      refine ContinuousOn.pow ?_ 2
      exact Real.continuousOn_log.mono (by
        intro x hx
        rw [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact ne_of_gt (hpos x hx))
    · intro x hx
      rw [Set.mem_uIcc] at hx
      have hxa : a ≤ x := by rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
      have hxl : 0 < Real.log x := hlog1 x hxa
      have hx0 : 0 < x := by linarith
      exact ne_of_gt (by positivity)
  have hmono : ∀ s ∈ Set.uIcc a b,
      σ * Real.log Y / Real.log b - 1 ≤ σ * Real.log Y / Real.log s - 1
      ∧ σ * Real.log Y / Real.log s - 1 ≤ σ * Real.log Y / Real.log a - 1 := by
    intro s hs
    rw [Set.mem_uIcc] at hs
    have hsa : a ≤ s := by rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
    have hsb : s ≤ b := by rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
    have hla : 0 < Real.log a := hlog1 a le_rfl
    have hlb : 0 < Real.log b := hlog1 b hab
    have hls : 0 < Real.log s := hlog1 s hsa
    have hl1 : Real.log a ≤ Real.log s := Real.log_le_log (by linarith) hsa
    have hl2 : Real.log s ≤ Real.log b := Real.log_le_log (by linarith) hsb
    constructor
    · rw [sub_le_sub_iff_right]
      exact div_le_div_of_nonneg_left (le_of_lt hσY) hls hl2
    · rw [sub_le_sub_iff_right]
      exact div_le_div_of_nonneg_left (le_of_lt hσY) hla hl1
  have hg' : ContinuousOn g ((fun s : ℝ => σ * Real.log Y / Real.log s - 1) '' Set.uIcc a b) := by
    refine hg.mono ?_
    rintro y ⟨s, hs, rfl⟩
    rw [Set.mem_uIcc]
    exact Or.inl (hmono s hs)
  have key : ∫ t in a..b, (g ∘ (fun s : ℝ => σ * Real.log Y / Real.log s - 1)) t
        * (-(σ * Real.log Y) / (t * (Real.log t)^2))
      = ∫ w in (σ * Real.log Y / Real.log a - 1)..(σ * Real.log Y / Real.log b - 1), g w :=
    intervalIntegral.integral_comp_mul_deriv' hderiv hcont_f' hg'
  have hEq : ∫ t in a..b, (g ∘ (fun s : ℝ => σ * Real.log Y / Real.log s - 1)) t
        * (-(σ * Real.log Y) / (t * (Real.log t)^2))
      = -(σ * Real.log Y) * ∫ t in a..b,
          g (σ * Real.log Y / Real.log t - 1) / (t * (Real.log t)^2) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Function.comp_apply]
    field_simp
  have hkey2 : (σ * Real.log Y) * (∫ t in a..b,
        g (σ * Real.log Y / Real.log t - 1) / (t * (Real.log t)^2))
      = ∫ w in (σ * Real.log Y / Real.log b - 1)..(σ * Real.log Y / Real.log a - 1), g w := by
    have h1 : -(σ * Real.log Y) * (∫ t in a..b,
        g (σ * Real.log Y / Real.log t - 1) / (t * (Real.log t)^2))
        = ∫ w in (σ * Real.log Y / Real.log a - 1)..(σ * Real.log Y / Real.log b - 1), g w := by
      rw [← hEq]; exact key
    have h2 : (∫ w in (σ * Real.log Y / Real.log a - 1)..(σ * Real.log Y / Real.log b - 1), g w)
        = -∫ w in (σ * Real.log Y / Real.log b - 1)..(σ * Real.log Y / Real.log a - 1), g w :=
      intervalIntegral.integral_symm _ _
    linarith [h1, h2]
  rw [← hkey2]
  field_simp


/-! ### The layer sums `T_n(D,Y)` of the linear sieve

The layer (Buchstab) decomposition of the sieve introduces, for each `n`, the sum `T_n(D,Y)` of
the `β = 1` Rosser–Iwaniec chains of length `n`, weighted by `∏ a_q` and by the Euler product `V`
at the *last* (smallest) prime of the chain.  The chain set is `𝒟⁻` (`Gm`) for `n` even and `𝒟⁺`
(`Gp`) for `n` odd — the parity pattern of Nathanson's `T_n(D,z)` (Ch. 9): for `n` odd the
`squared` level condition sits at the *odd* positions, for `n` even at the *even* ones, and these
are exactly the two patterns built by `chainPair`.

The point of the layer index is that the recursion
`T_{n+1}(D,Y) = Σ_{q<Y} a_q·T_n(D/q,q) + boundary`
is *triangular* in `n`: it relates `T_{n+1}` to `T_n` only, so a profile bound
`T_n(D,Y) ≤ V(Y)·φ_n(σ)` can be propagated by induction on `n` with no reference to a
level-independent sup — precisely the loss that makes a single σ-profile infeasible (see the
state notes). -/

/-- The `n`-th **layer sum** of the linear sieve,
`T_n(D,Y) = Σ_c (∏_{q∈c} 1/(q-1)) · V(last c)`, summed over the `β = 1` Rosser–Iwaniec chains
`c` of length `n` (the lower-bound chain set `𝒟⁻` for `n` even, the upper-bound one `𝒟⁺` for `n`
odd — the parity pattern of Nathanson's `T_n(D,z)`, Ch. 9).  The weight of a chain is the product
of `a_q = 1/(q-1)` over its primes times the Euler product `V` at its *last* (smallest) prime.

The two-step recursion `T_{n+1}(D,Y) = Σ_{q<Y} a_q T_n(D/q,q)` (`+ boundary`, and with the
parity-dependent level condition) makes the layer induction *triangular* in `n` — which is why
the layer route is not affected by the sup-loss that kills a level-independent profile. -/
def TSieve (n : ℕ) (D : ℝ) (Y : ℕ) : ℝ :=
  ((if n % 2 = 0 then Gm (1:ℝ) D Y else Gp (1:ℝ) D Y).filter
      (fun c => c.length = n)).sum
    (fun c => (c.map (fun q : ℕ => (1:ℝ)/((q:ℝ)-1))).prod * Vsieve (c.getLastD 1))

lemma oddPrimesLt_one : oddPrimesLt 1 = ∅ := by decide

lemma Vsieve_one : Vsieve 1 = 1 := by
  rw [Vsieve, oddPrimesLt_one, Finset.prod_empty]

/-- `T_0 = 1`: the empty chain, weighted by `V(1) = 1`. -/
lemma TSieve_zero (D : ℝ) (Y : ℕ) : TSieve 0 D Y = 1 := by
  have hfil : ((Gm (1:ℝ) D Y).filter (fun c : List ℕ => c.length = 0)) = {([] : List ℕ)} := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hc, hl⟩
      rcases c with _ | ⟨q, l⟩
      · rfl
      · simp only [List.length_cons] at hl
        omega
    · rintro rfl
      exact ⟨nil_mem_Gm 1 D Y, rfl⟩
  rw [TSieve, if_pos (show (0:ℕ) % 2 = 0 from rfl), hfil, Finset.sum_singleton]
  simp [Vsieve_one]


/-! ### The layer sums: endomorphism of the chain weights, and the first cases -/

lemma weight_cons {q : ℕ} {l : List ℕ} {d : ℕ} :
    ((q :: l).map (fun r : ℕ => (1:ℝ)/((r:ℝ)-1))).prod * Vsieve ((q :: l).getLastD d)
      = (1/((q:ℝ)-1)) * ((l.map (fun r : ℕ => (1:ℝ)/((r:ℝ)-1))).prod * Vsieve (l.getLastD q)) := by
  rw [List.map_cons, List.prod_cons, List.getLastD_cons]
  ring

lemma weight_singleton (q d : ℕ) :
    ((q :: ([] : List ℕ)).map (fun r : ℕ => (1:ℝ)/((r:ℝ)-1))).prod
        * Vsieve ((q :: ([] : List ℕ)).getLastD d)
      = (1/((q:ℝ)-1)) * Vsieve q := by
  rw [weight_cons]
  simp

/-- `T_1`: the chains of length one are the singletons `[q]` with `q² ≤ D`. -/
lemma TSieve_one (D : ℝ) (Y : ℕ) : TSieve 1 D Y
    = ∑ q ∈ (oddPrimesLt Y).filter (fun q : ℕ => (q:ℝ)^((1:ℝ)+1) ≤ D),
        (1/((q:ℝ)-1)) * Vsieve q := by
  have hset : ((Gp (1:ℝ) D Y).filter (fun c => c.length = 1))
      = ((oddPrimesLt Y).filter (fun q : ℕ => (q:ℝ)^((1:ℝ)+1) ≤ D)).image
          (fun q => (q :: ([] : List ℕ))) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hc, hl⟩
      rcases (mem_Gp_iff.mp hc) with h1 | ⟨q, l', hq, hqD, hl', rfl⟩
      · rw [h1] at hl
        simp at hl
      · rcases l' with _ | ⟨r, l''⟩
        · exact ⟨q, ⟨(sievePrime_iff_mem Y q).mpr hq, hqD⟩, rfl⟩
        · simp only [List.length_cons] at hl
          omega
    · rintro ⟨q, hq, rfl⟩
      refine ⟨mem_Gp_iff.mpr (Or.inr ⟨q, [],
        (sievePrime_iff_mem Y q).mp hq.1, hq.2, nil_mem_Gm 1 (D/q) q, rfl⟩), rfl⟩
  rw [TSieve, if_neg (by norm_num : ¬ ((1:ℕ) % 2 = 0)), hset, Finset.sum_image]
  · refine Finset.sum_congr rfl (fun q hq => ?_)
    exact weight_singleton q 1
  · intro a ha b hb hab
    exact (List.cons.injEq a [] b []).mp hab |>.1




/-! ## The reduction: the deficit estimate implies the target

Summing `chain_sieve_bounds` against the shifted-prime weights `a_n = log(n-2)·1_{n-2 prime}`
gives, for `Y = ⌊x^{1/8}⌋+1` and `D = ⌊√x/(log x)^B⌋`,

`target ≥ Σ_{c ∈ Gm} (-1)^{|c|} θ_{lprod c}(x) = x·MeSum D Y − Σ_{c}|r_{lprod c}| ≥ c₀·Vsieve Y·x − x/log^A x`,

the last sum being bounded by Bombieri–Vinogradov because the chain products `lprod c` are
distinct odd integers `≤ D`. -/

lemma oddPrimesLt_succ (Z : ℕ) :
    oddPrimesLt (Z + 1) = (Nat.primesLE Z).filter (fun q : ℕ => q ≠ 2) := by
  ext q
  simp only [oddPrimesLt, Finset.mem_filter, Finset.mem_range, Nat.mem_primesLE]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨by omega, h2⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨by omega, h2, h3⟩

lemma oddPrim_eq_primesLE (Z : ℕ) :
    oddPrim (Z + 1) = ∏ q ∈ (Nat.primesLE Z).filter (fun q : ℕ => q ≠ 2), q := by
  rw [oddPrim, oddPrimesLt_succ]

lemma TmSum_one_le_indP (D : ℝ) (hD : 0 ≤ D) (Y n : ℕ) (hDY : (Y : ℝ) ≤ D) :
    TmSum (1:ℝ) D Y n ≤ indP Y n := by
  have h1 := (chain_sieve_bounds (1:ℝ) le_rfl Y D hD n).1
  have heff : eff D Y = Y := by
    unfold eff
    have hlt : (Y : ℝ) < ((⌊D⌋₊ + 1 : ℕ) : ℝ) := by
      have := Nat.lt_floor_add_one D
      push_cast
      linarith
    have hY : Y < ⌊D⌋₊ + 1 := by exact_mod_cast hlt
    omega
  rwa [heff] at h1

lemma list_prod_odd : ∀ l : List ℕ, (∀ q ∈ l, q % 2 = 1) → l.prod % 2 = 1 := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
      intro h
      have h1 := h a List.mem_cons_self
      have h2 := ih (fun q hq => h q (List.mem_cons_of_mem a hq))
      rw [List.prod_cons, Nat.mul_mod, h1, h2]

lemma chain_prod_odd (β D : ℝ) (Y : ℕ) :
    ∀ c ∈ Gm β D Y, lprod c % 2 = 1 := by
  intro c hc
  rw [lprod]
  refine list_prod_odd c (fun q hq => ?_)
  obtain ⟨h1, h2, _⟩ := (chain_primes β Y D).2 c hc q hq
  exact (h1.eq_two_or_odd).resolve_left h2

lemma list_one_le_prod : ∀ l : List ℕ, (∀ q ∈ l, 1 ≤ q) → 1 ≤ l.prod := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
      intro h
      have h1 : 1 ≤ a := h a List.mem_cons_self
      have h2 : 1 ≤ t.prod := ih (fun q hq => h q (List.mem_cons_of_mem a hq))
      rw [List.prod_cons]
      nlinarith

lemma lprod_ge_two_of_ne_nil {l : List ℕ} (h : l ≠ []) (hp : ∀ q ∈ l, q.Prime) :
    2 ≤ lprod l := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t =>
      rw [lprod_cons]
      have ha := Nat.Prime.two_le (hp a List.mem_cons_self)
      have ht : 1 ≤ lprod t := by
        rw [lprod]
        exact list_one_le_prod t (fun x hx => Nat.Prime.one_le (hp x (List.mem_cons_of_mem a hx)))
      nlinarith

lemma head_eq_of_lprod_eq {q q' : ℕ} {l l' : List ℕ} (hq : q.Prime) (hq' : q'.Prime)
    (hlp : ∀ x ∈ l, x.Prime) (hl'p : ∀ x ∈ l', x.Prime)
    (hl : ∀ x ∈ l, x < q) (hl' : ∀ x ∈ l', x < q')
    (h : q * lprod l = q' * lprod l') : q = q' := by
  rcases hq.dvd_mul.mp ⟨lprod l, h.symm⟩ with h1 | h1
  · exact (Nat.prime_dvd_prime_iff_eq hq hq').mp h1
  · obtain ⟨a, ha, hqa⟩ := prime_dvd_list_prod hq h1
    have haq : a = q := ((Nat.prime_dvd_prime_iff_eq hq (hl'p a ha)).mp hqa).symm
    have hlt : q < q' := by rw [← haq]; exact hl' a ha
    rcases hq'.dvd_mul.mp ⟨lprod l', h⟩ with h2 | h2
    · have : q' = q := (Nat.prime_dvd_prime_iff_eq hq' hq).mp h2
      omega
    · obtain ⟨b, hb, hqb⟩ := prime_dvd_list_prod hq' h2
      have hbq : b = q' := ((Nat.prime_dvd_prime_iff_eq hq' (hlp b hb)).mp hqb).symm
      have hlt2 : q' < q := by rw [← hbq]; exact hl b hb
      omega

lemma chain_lprod_inj (β : ℝ) :
    ∀ Y : ℕ, ∀ D : ℝ,
      (∀ c ∈ Gp β D Y, ∀ c' ∈ Gp β D Y, lprod c = lprod c' → c = c') ∧
      (∀ c ∈ Gm β D Y, ∀ c' ∈ Gm β D Y, lprod c = lprod c' → c = c') := by
  intro Y
  induction Y using Nat.strong_induction_on with
  | h Y ih =>
    intro D
    constructor
    · intro c hc c' hc' heq
      rcases (mem_Gp_iff.mp hc) with h1 | ⟨q, l, hqs, hqD, hl, hfl⟩
      · -- c = []
        rcases (mem_Gp_iff.mp hc') with h2 | ⟨q', l', hqs', hqD', hl', hfl'⟩
        · rw [h1, h2]
        · exfalso
          have hb : 2 ≤ lprod (q' :: l') :=
            lprod_ge_two_of_ne_nil (List.cons_ne_nil q' l') (fun x hx => by
              rcases List.mem_cons.mp hx with rfl | hx'
              · exact hqs'.1
              · exact ((chain_primes β q' (D/q')).2 l' hl' x hx').1)
          rw [h1] at heq
          rw [hfl'] at heq
          rw [show lprod ([] : List ℕ) = 1 from rfl] at heq
          omega
      · -- c = q :: l
        rcases (mem_Gp_iff.mp hc') with h2 | ⟨q', l', hqs', hqD', hl', hfl'⟩
        · exfalso
          have hb : 2 ≤ lprod (q :: l) :=
            lprod_ge_two_of_ne_nil (List.cons_ne_nil q l) (fun x hx => by
              rcases List.mem_cons.mp hx with rfl | hx'
              · exact hqs.1
              · exact ((chain_primes β q (D/q)).2 l hl x hx').1)
          rw [h2] at heq
          rw [hfl] at heq
          rw [show lprod ([] : List ℕ) = 1 from rfl] at heq
          omega
        · obtain ⟨hq'p, hq'2, hq'Y⟩ := hqs'
          have hq := hqs.1
          have hmul : q * lprod l = q' * lprod l' := by
            have h := heq; rw [hfl, hfl', lprod_cons, lprod_cons] at h; exact h
          have heqq : q = q' := head_eq_of_lprod_eq hq hq'p
            (fun x hx => ((chain_primes β q (D/q)).2 l hl x hx).1)
            (fun x hx => ((chain_primes β q' (D/q')).2 l' hl' x hx).1)
            (fun x hx => ((chain_primes β q (D/q)).2 l hl x hx).2.2)
            (fun x hx => ((chain_primes β q' (D/q')).2 l' hl' x hx).2.2)
            hmul
          have hqq : q' = q := heqq.symm
          have hl'2 : l' ∈ Gm β (D/q) q := by rwa [hqq] at hl'
          rw [hqq] at hmul
          have hll : lprod l = lprod l' := Nat.mul_left_cancel (Nat.Prime.pos hq) hmul
          have hll' : l = l' := (ih q hqs.2.2 (D/q)).2 l hl l' hl'2 hll
          rw [hfl, hfl', hll', hqq]
    · intro c hc c' hc' heq
      rcases (mem_Gm_iff.mp hc) with h1 | ⟨q, l, hqs, hqD, hl, hfl⟩
      · -- c = []
        rcases (mem_Gm_iff.mp hc') with h2 | ⟨q', l', hqs', hqD', hl', hfl'⟩
        · rw [h1, h2]
        · exfalso
          have hb : 2 ≤ lprod (q' :: l') :=
            lprod_ge_two_of_ne_nil (List.cons_ne_nil q' l') (fun x hx => by
              rcases List.mem_cons.mp hx with rfl | hx'
              · exact hqs'.1
              · exact ((chain_primes β q' (D/q')).1 l' hl' x hx').1)
          rw [h1] at heq
          rw [hfl'] at heq
          rw [show lprod ([] : List ℕ) = 1 from rfl] at heq
          omega
      · -- c = q :: l
        rcases (mem_Gm_iff.mp hc') with h2 | ⟨q', l', hqs', hqD', hl', hfl'⟩
        · exfalso
          have hb : 2 ≤ lprod (q :: l) :=
            lprod_ge_two_of_ne_nil (List.cons_ne_nil q l) (fun x hx => by
              rcases List.mem_cons.mp hx with rfl | hx'
              · exact hqs.1
              · exact ((chain_primes β q (D/q)).1 l hl x hx').1)
          rw [h2] at heq
          rw [hfl] at heq
          rw [show lprod ([] : List ℕ) = 1 from rfl] at heq
          omega
        · obtain ⟨hq'p, hq'2, hq'Y⟩ := hqs'
          have hq := hqs.1
          have hmul : q * lprod l = q' * lprod l' := by
            have h := heq; rw [hfl, hfl', lprod_cons, lprod_cons] at h; exact h
          have heqq : q = q' := head_eq_of_lprod_eq hq hq'p
            (fun x hx => ((chain_primes β q (D/q)).1 l hl x hx).1)
            (fun x hx => ((chain_primes β q' (D/q')).1 l' hl' x hx).1)
            (fun x hx => ((chain_primes β q (D/q)).1 l hl x hx).2.2)
            (fun x hx => ((chain_primes β q' (D/q')).1 l' hl' x hx).2.2)
            hmul
          have hqq : q' = q := heqq.symm
          have hl'2 : l' ∈ Gp β (D/q) q := by rwa [hqq] at hl'
          rw [hqq] at hmul
          have hll : lprod l = lprod l' := Nat.mul_left_cancel (Nat.Prime.pos hq) hmul
          have hll' : l = l' := (ih q hqs.2.2 (D/q)).1 l hl l' hl'2 hll
          rw [hfl, hfl', hll', hqq]

/-- the chain error is dominated by the Bombieri–Vinogradov sum over odd moduli `≤ K` -/
lemma chain_err_le (x : ℕ) (D : ℝ) (Y : ℕ) (K : ℕ) (hD1 : 1 ≤ D) (hDK : D ≤ (K : ℝ)) :
    (Gm (1:ℝ) D Y).sum (fun c => |rrem x (lprod c)|)
      ≤ ((Finset.Icc 1 K).filter (fun d : ℕ => d % 2 = 1)).sum (fun d => |rrem x d|) := by
  classical
  rw [← Finset.sum_image (f := fun d => |rrem x d|) (g := lprod)
    (fun a ha b hb hab => (chain_lprod_inj (1:ℝ) Y D).2 a ha b hb hab)]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun d _ _ => abs_nonneg _)
  intro d hd
  rw [Finset.mem_image] at hd
  obtain ⟨c, hc, rfl⟩ := hd
  rw [Finset.mem_filter, Finset.mem_Icc]
  refine ⟨⟨?_, ?_⟩, chain_prod_odd (1:ℝ) D Y c hc⟩
  · rw [lprod]
    exact list_one_le_prod c (fun q hq => ((chain_primes (1:ℝ) Y D).2 c hc q hq).1.one_le)
  · have hsupp := (chain_support (1:ℝ) (by norm_num) Y D hD1).2 c hc
    have : (lprod c : ℝ) ≤ (K : ℝ) := le_trans hsupp hDK
    exact_mod_cast this

/-- summing the minorant of `chain_sieve_bounds` against the shifted-prime weights -/
lemma chains_theta_sum (x : ℕ) (D : ℝ) (Y : ℕ) (hD : 0 ≤ D) (hDY : (Y:ℝ) ≤ D) :
    ((Finset.range (x + 1)).filter (fun p : ℕ => p.Prime)).sum
        (fun p => Real.log (p : ℝ) * TmSum (1:ℝ) D Y (p + 2))
      = (Gm (1:ℝ) D Y).sum (fun c => (-1:ℝ)^c.length * thetaD x (lprod c)) := by
  classical
  have htheta : ∀ d : ℕ, thetaD x d
      = ((Finset.range (x + 1)).filter (fun p : ℕ => p.Prime)).sum
          (fun p => if d ∣ p + 2 then Real.log (p : ℝ) else 0) := by
    intro d
    unfold thetaD
    rw [← Finset.filter_filter, ← Finset.sum_filter]
  have key : ∀ p : ℕ,
      Real.log (p:ℝ) * (∑ c ∈ Gm (1:ℝ) D Y,
          (-1:ℝ)^c.length * (if lprod c ∣ p + 2 then 1 else 0))
      = ∑ c ∈ Gm (1:ℝ) D Y,
          (-1:ℝ)^c.length * (if lprod c ∣ p + 2 then Real.log (p:ℝ) else 0) := by
    intro p
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun c hc => ?_)
    by_cases h : lprod c ∣ p + 2
    · simp only [if_pos h]; ring
    · simp only [if_neg h]; ring
  simp only [TmSum]
  rw [Finset.sum_congr rfl (fun p hp => key p), Finset.sum_comm]
  rw [show (Gm (1:ℝ) D Y).sum (fun c => (-1:ℝ)^c.length * thetaD x (lprod c))
      = (Gm (1:ℝ) D Y).sum (fun c => (-1:ℝ)^c.length *
          ((Finset.range (x + 1)).filter (fun p : ℕ => p.Prime)).sum
            (fun p => if lprod c ∣ p + 2 then Real.log (p : ℝ) else 0))
      from Finset.sum_congr rfl (fun c hc => by rw [htheta])]
  refine Finset.sum_congr rfl (fun c hc => ?_)
  rw [Finset.mul_sum]




/-! ## The target -/

private lemma rpow_add' {x y z : ℝ} (hx : 0 < x) :
    x ^ y * x ^ z = x ^ (y + z) := (Real.rpow_add hx y z).symm

private lemma rpow_mul' {x a b : ℝ} (hx : 0 ≤ x) :
    (x ^ a) ^ b = x ^ (a * b) := (Real.rpow_mul hx a b).symm

private lemma mul_rpow' {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x * y) ^ z = x ^ z * y ^ z := Real.mul_rpow hx hy

private lemma rpow_natCast' (x : ℝ) (n : ℕ) : x ^ (n:ℝ) = x^n := Real.rpow_natCast x n

private lemma one_le_rpow' {x z : ℝ} (hx : 1 ≤ x) (hz : 0 ≤ z) : 1 ≤ x ^ z :=
  Real.one_le_rpow hx hz

private lemma rpow_pos' {x : ℝ} (hx : 0 < x) (y : ℝ) : 0 < x ^ y := Real.rpow_pos_of_pos hx y

private lemma rpow_nonneg' {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : 0 ≤ x ^ y := Real.rpow_nonneg hx y

/-- A crude asymptotic bound: for `B > 0`, eventually `(log x)^B ≤ x^{1/9}`. -/
lemma log_rpow_eventually_le (B : ℝ) (hB : 0 < B) :
    ∀ᶠ x : ℝ in Filter.atTop, (Real.log x) ^ B ≤ x ^ (1/9:ℝ) := by
  set n : ℕ := ⌈B⌉₊ with hn
  have hBn : B ≤ (n:ℝ) := Nat.le_ceil B
  have hlim : Filter.Tendsto (fun x : ℝ => (Real.log x) ^ n / (1 * x + 0))
      Filter.atTop (nhds 0) :=
    Real.tendsto_pow_log_div_mul_add_atTop 1 0 n (by norm_num)
  have hlim2 := hlim.comp (tendsto_rpow_atTop (show (0:ℝ) < (1:ℝ)/9 by norm_num))
  have hc : (0:ℝ) < ((1:ℝ)/9)^n := by positivity
  have hev := Filter.Tendsto.eventually_lt_const hc hlim2
  filter_upwards [hev, Filter.eventually_ge_atTop (Real.exp 1)] with x hlt hx1
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx1
  have hlog1 : (1:ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hx1
  simp only [Function.comp_apply, mul_one, add_zero, one_mul] at hlt
  have hlogr : Real.log (x ^ (1/9:ℝ)) = (1/9) * Real.log x := Real.log_rpow hxpos _
  rw [hlogr] at hlt
  have hx9 : 0 < x ^ (1/9:ℝ) := rpow_pos' hxpos _
  have hpow : ((1:ℝ)/9 * Real.log x)^n = ((1:ℝ)/9)^n * (Real.log x)^n := mul_pow _ _ _
  have hlogn : (Real.log x)^n < x ^ (1/9:ℝ) := by
    rw [div_lt_iff₀ hx9, hpow] at hlt
    exact lt_of_mul_lt_mul_left hlt (le_of_lt hc)
  have hrpow1 : (Real.log x) ^ B ≤ (Real.log x) ^ ((n:ℕ):ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hlog1 hBn
  have hrpow2 : (Real.log x) ^ ((n:ℕ):ℝ) = (Real.log x)^n := rpow_natCast' _ n
  rw [hrpow2] at hrpow1
  linarith [hrpow1, hlogn]

/-- **Structural thresholds.**  For `B > 0` and all large `x`, with `Z = ⌊x^{1/8}⌋₊`,
`Y = Z+1` and `K = ⌊√x/(log x)^B⌋₊`, one has `3 ≤ Z`, `(Y:ℝ)^3 ≤ K` and `1 ≤ log x`. -/
lemma sift_thresholds (B : ℝ) (hB : 0 < B) :
    ∃ N : ℕ, ∀ x : ℕ, N ≤ x →
      (3 ≤ ⌊(x : ℝ) ^ (1 / 8 : ℝ)⌋₊) ∧
      ((((⌊(x : ℝ) ^ (1 / 8 : ℝ)⌋₊ + 1 : ℕ) : ℝ))^3
        ≤ (⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊ : ℝ)) ∧
      ((1:ℝ) ≤ Real.log (x : ℝ)) := by
  have h1 : ∀ᶠ x : ℝ in Filter.atTop, (1:ℝ) ≤ x := Filter.eventually_ge_atTop 1
  have hlog1 : ∀ᶠ x : ℝ in Filter.atTop, (1:ℝ) ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually_ge_atTop 1
  have hlogB : ∀ᶠ x : ℝ in Filter.atTop, (Real.log x) ^ B ≤ x ^ (1/9:ℝ) :=
    log_rpow_eventually_le B hB
  have hx72 : ∀ᶠ x : ℝ in Filter.atTop, (9:ℝ) ≤ x ^ (1/72:ℝ) :=
    (tendsto_rpow_atTop (show (0:ℝ) < (1:ℝ)/72 by norm_num)).eventually_ge_atTop 9
  have hxn : ∀ᶠ x : ℝ in Filter.atTop, ((3:ℝ)^(8:ℕ) ≤ x) := Filter.eventually_ge_atTop _
  have hreal := h1.and (hlog1.and (hlogB.and (hx72.and hxn)))
  have hev := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hreal
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  refine ⟨N, fun x hx => ?_⟩
  obtain ⟨hx1, hlog1, hlogB, hx72, hxn⟩ := hN x hx
  have hxpos : (0:ℝ) < (x:ℝ) := lt_of_lt_of_le one_pos hx1
  have hlogpos : 0 < Real.log (x:ℝ) := by linarith
  have hlogB' : (Real.log (x:ℝ)) ^ B ≤ (x:ℝ) ^ (1/9:ℝ) := hlogB
  refine ⟨?_, ?_, hlog1⟩
  · -- `3 ≤ Z`
    have hroot : (3:ℝ) ≤ (x : ℝ) ^ (1/8:ℝ) := by
      have h8 : (3:ℝ) ^ ((8:ℕ):ℝ) = (3:ℝ)^(8:ℕ) := rpow_natCast' 3 8
      have h2 : ((3:ℝ) ^ ((8:ℕ):ℝ)) ^ (1/8:ℝ) = (3:ℝ) ^ (((8:ℕ):ℝ) * (1/8:ℝ)) :=
        rpow_mul' (by norm_num : (0:ℝ) ≤ 3)
      rw [h8, show (((8:ℕ):ℝ) * (1/8:ℝ)) = 1 by norm_num] at h2
      have h1 : (3:ℝ) ^ (1:ℝ) = 3 := Real.rpow_one 3
      rw [h1] at h2
      calc (3:ℝ) = ((3:ℝ)^(8:ℕ)) ^ (1/8:ℝ) := h2.symm
        _ ≤ (x : ℝ) ^ (1/8:ℝ) := Real.rpow_le_rpow (by norm_num) hxn (by norm_num)
    calc (3:ℕ) = ⌊(3:ℝ)⌋₊ := by simp
      _ ≤ ⌊(x : ℝ) ^ (1/8:ℝ)⌋₊ := Nat.floor_mono hroot
  · -- `(Y:ℝ)^3 ≤ K`
    have hZle : ((⌊(x : ℝ) ^ (1/8:ℝ)⌋₊ : ℕ) : ℝ) ≤ (x : ℝ) ^ (1/8:ℝ) :=
      Nat.floor_le (rpow_nonneg' (le_of_lt hxpos) _)
    have hY8 : (((⌊(x : ℝ) ^ (1/8:ℝ)⌋₊ + 1 : ℕ) : ℝ)) ≤ 2 * (x : ℝ) ^ (1/8:ℝ) := by
      push_cast
      have := one_le_rpow' hx1 (by norm_num : (0:ℝ) ≤ 1/8)
      linarith
    have hY3 : (((⌊(x : ℝ) ^ (1/8:ℝ)⌋₊ + 1 : ℕ) : ℝ))^3 ≤ 8 * (x : ℝ) ^ (3/8:ℝ) := by
      have hcube : (2 * (x : ℝ) ^ (1/8:ℝ))^3 = 8 * (x : ℝ) ^ (3/8:ℝ) := by
        have h2 : (2 * (x : ℝ) ^ (1/8:ℝ)) ^ (3:ℝ)
            = (2:ℝ) ^ (3:ℝ) * ((x : ℝ) ^ (1/8:ℝ)) ^ (3:ℝ) :=
          mul_rpow' (by norm_num) (rpow_nonneg' (le_of_lt hxpos) _)
        have h3 : ((x : ℝ) ^ (1/8:ℝ)) ^ (3:ℝ) = (x : ℝ) ^ ((1/8:ℝ) * 3) :=
          rpow_mul' (le_of_lt hxpos)
        have h4 : (2:ℝ) ^ (3:ℝ) = 8 := by norm_num
        have h5 : (2 * (x : ℝ) ^ (1/8:ℝ)) ^ (3:ℝ)
            = (2 * (x : ℝ) ^ (1/8:ℝ))^3 := rpow_natCast' _ 3
        rw [h5] at h2
        rw [h2, h3, h4, show (1/8:ℝ) * 3 = 3/8 by norm_num]
      calc (((⌊(x : ℝ) ^ (1/8:ℝ)⌋₊ + 1 : ℕ) : ℝ))^3
          ≤ (2 * (x : ℝ) ^ (1/8:ℝ))^3 := pow_le_pow_left₀ (by positivity) hY8 3
        _ = 8 * (x : ℝ) ^ (3/8:ℝ) := hcube
    have hprod : (8 * ((x : ℝ) ^ (3/8:ℝ)) + 1) * (Real.log (x:ℝ)) ^ B
        ≤ (x : ℝ) ^ (1/2:ℝ) := by
      have h9 : 8 * ((x : ℝ) ^ (3/8:ℝ)) + 1 ≤ 9 * ((x : ℝ) ^ (3/8:ℝ)) := by
        have h1 : (1:ℝ) ≤ (x : ℝ) ^ (3/8:ℝ) := one_le_rpow' hx1 (by norm_num)
        linarith
      have hstep : (8 * ((x : ℝ) ^ (3/8:ℝ)) + 1) * (Real.log (x:ℝ)) ^ B
          ≤ (9 * ((x : ℝ) ^ (3/8:ℝ))) * ((x : ℝ) ^ (1/9:ℝ)) :=
        mul_le_mul h9 hlogB' (rpow_nonneg' (le_of_lt hlogpos) _) (by positivity)
      have h35 : (9:ℝ) * ((x : ℝ) ^ (35/72:ℝ)) ≤ (x : ℝ) ^ (1/2:ℝ) := by
        have hsplit : (x : ℝ) ^ (35/72:ℝ) * (x : ℝ) ^ (1/72:ℝ) = (x : ℝ) ^ (1/2:ℝ) := by
          rw [rpow_add' hxpos]
          norm_num
        calc (9:ℝ) * ((x : ℝ) ^ (35/72:ℝ))
            = ((x : ℝ) ^ (35/72:ℝ)) * 9 := by ring
          _ ≤ ((x : ℝ) ^ (35/72:ℝ)) * ((x : ℝ) ^ (1/72:ℝ)) :=
              mul_le_mul_of_nonneg_left hx72 (by positivity)
          _ = (x : ℝ) ^ (1/2:ℝ) := hsplit
      calc (8 * ((x : ℝ) ^ (3/8:ℝ)) + 1) * (Real.log (x:ℝ)) ^ B
          ≤ (9 * ((x : ℝ) ^ (3/8:ℝ))) * ((x : ℝ) ^ (1/9:ℝ)) := hstep
        _ = 9 * (((x : ℝ) ^ (3/8:ℝ)) * ((x : ℝ) ^ (1/9:ℝ))) := by ring
        _ = 9 * ((x : ℝ) ^ (3/8 + 1/9 : ℝ)) := by rw [rpow_add' hxpos]
        _ = 9 * ((x : ℝ) ^ (35/72:ℝ)) := by norm_num
        _ ≤ (x : ℝ) ^ (1/2:ℝ) := h35
    have hK : 8 * ((x : ℝ) ^ (3/8:ℝ)) + 1
        ≤ Real.sqrt (x:ℝ) / (Real.log (x:ℝ)) ^ B := by
      have hs : Real.sqrt (x:ℝ) = (x:ℝ) ^ (1/2:ℝ) := Real.sqrt_eq_rpow x
      rw [hs, le_div_iff₀ (rpow_pos' hlogpos B)]
      exact hprod
    have hKge : Real.sqrt (x:ℝ) / (Real.log (x:ℝ)) ^ B
        < ((⌊Real.sqrt (x:ℝ) / (Real.log (x:ℝ)) ^ B⌋₊ : ℕ) : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have hfinal : (((⌊(x : ℝ) ^ (1/8:ℝ)⌋₊ + 1 : ℕ) : ℝ))^3
        < ((⌊Real.sqrt (x:ℝ) / (Real.log (x:ℝ)) ^ B⌋₊ : ℕ) : ℝ) + 1 :=
      lt_of_le_of_lt (by linarith [hY3, hK]) hKge
    have hnat : (⌊(x : ℝ) ^ (1/8:ℝ)⌋₊ + 1)^3
        < (⌊Real.sqrt (x:ℝ) / (Real.log (x:ℝ)) ^ B⌋₊ + 1) := by
      have hh := hfinal
      push_cast at hh
      exact_mod_cast hh
    have hle := Nat.lt_succ_iff.mp hnat
    calc (((⌊(x : ℝ) ^ (1/8:ℝ)⌋₊ + 1 : ℕ) : ℝ))^3
        = (((⌊(x : ℝ) ^ (1/8:ℝ)⌋₊ + 1)^3 : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((⌊Real.sqrt (x:ℝ) / (Real.log (x:ℝ)) ^ B⌋₊ : ℕ) : ℝ) := by exact_mod_cast hle


/-! ## The target -/

namespace ChenEight

noncomputable section

/-- `alpha = 31/50`, the cut-off ratio `y_k = y ^ (alpha^k)`. -/
def sieveAlpha : ℝ := 599 / 1000

/-- `beta = -log alpha = log(1000/599)`. -/
def sieveBeta : ℝ := Real.log (1000/599)

/-- the `k`-th cutoff `y ^ (alpha^k)` (real exponent). -/
noncomputable def cut (y : ℝ) (k : ℕ) : ℝ := y ^ (sieveAlpha ^ k)

/-- odd primorial below `M` (product of `3 ≤ p < M`, `p` prime). -/
def oddPrimLt (M : ℕ) : ℕ := ∏ p ∈ (Finset.range M).filter (fun p : ℕ => p.Prime ∧ 3 ≤ p), p

/-- the ideal sifted indicator. -/
def Id (m M : ℕ) : ℝ := if m.Coprime (oddPrimLt M) then 1 else 0

/-- lower-bound chain set: chains `p₁ > p₂ > … ` with `p ⱼ < M` at the head (position `j`),
the cut-off `p ⱼ ≤ y^{α^{⌈j/2⌉}}` imposed at EVEN positions `j`. -/
noncomputable def loChain (y : ℝ) : ℕ → ℕ → Finset (List ℕ)
  | j, M =>
    insert [] (((Finset.range M).filter (fun p : ℕ => p.Prime ∧ 3 ≤ p)).attach.biUnion
      (fun p => if j % 2 = 1 ∨ (p.1 : ℝ) ≤ cut y ((j + 1) / 2) then
                  (loChain y (j + 1) p.1).image (fun l => p.1 :: l) else ∅))
  termination_by j M => M
  decreasing_by exact Finset.mem_range.mp (Finset.mem_filter.mp p.2).1

/-- upper-bound chain set: cut-off imposed at ODD positions. -/
noncomputable def hiChain (y : ℝ) : ℕ → ℕ → Finset (List ℕ)
  | j, M =>
    insert [] (((Finset.range M).filter (fun p : ℕ => p.Prime ∧ 3 ≤ p)).attach.biUnion
      (fun p => if j % 2 = 0 ∨ (p.1 : ℝ) ≤ cut y ((j + 1) / 2) then
                  (hiChain y (j + 1) p.1).image (fun l => p.1 :: l) else ∅))
  termination_by j M => M
  decreasing_by exact Finset.mem_range.mp (Finset.mem_filter.mp p.2).1

/-- sum over the lower chain set, weighted by `(-1)^{|c|}` and divisibility. -/
def Rlo (y : ℝ) (j M m : ℕ) : ℝ :=
  (loChain y j M).sum (fun c => (-1 : ℝ) ^ c.length * (if c.prod ∣ m then 1 else 0))

/-- sum over the upper chain set. -/
def Rhi (y : ℝ) (j M m : ℕ) : ℝ :=
  (hiChain y j M).sum (fun c => (-1 : ℝ) ^ c.length * (if c.prod ∣ m then 1 else 0))

/-- odd primes below `M`. -/
def oddLt (M : ℕ) : Finset ℕ := (Finset.range M).filter (fun p : ℕ => p.Prime ∧ 3 ≤ p)

lemma oddPrimLt_eq_prod_oddLt (M : ℕ) : oddPrimLt M = ∏ p ∈ oddLt M, p := rfl

/-- unfolding of `loChain`. -/
lemma loChain_unfold (y : ℝ) (j M : ℕ) :
    loChain y j M =
      insert [] ((oddLt M).attach.biUnion
        (fun p => if j % 2 = 1 ∨ (p.1 : ℝ) ≤ cut y ((j + 1) / 2) then
                    (loChain y (j + 1) p.1).image (fun l => p.1 :: l) else ∅)) := by
  rw [loChain]; rfl

lemma hiChain_unfold (y : ℝ) (j M : ℕ) :
    hiChain y j M =
      insert [] ((oddLt M).attach.biUnion
        (fun p => if j % 2 = 0 ∨ (p.1 : ℝ) ≤ cut y ((j + 1) / 2) then
                    (hiChain y (j + 1) p.1).image (fun l => p.1 :: l) else ∅)) := by
  rw [hiChain]; rfl

lemma loChain_decomp (y : ℝ) (j M : ℕ) (F : List ℕ → ℝ) :
    (loChain y j M).sum F
      = F [] + ∑ p ∈ oddLt M,
          (if j % 2 = 1 ∨ (p : ℝ) ≤ cut y ((j + 1) / 2)
            then (loChain y (j + 1) p).sum (fun l => F (p :: l)) else 0) := by
  have hconv : (oddLt M).attach.biUnion (fun p =>
        if j % 2 = 1 ∨ (p.1 : ℝ) ≤ cut y ((j + 1) / 2)
          then (loChain y (j + 1) p.1).image (fun l => p.1 :: l) else ∅)
      = (oddLt M).biUnion (fun p =>
        if j % 2 = 1 ∨ (p : ℝ) ≤ cut y ((j + 1) / 2)
          then (loChain y (j + 1) p).image (fun l => p :: l) else ∅) :=
    Finset.attach_biUnion (s := oddLt M)
      (f := fun p => if j % 2 = 1 ∨ (p : ℝ) ≤ cut y ((j + 1) / 2)
          then (loChain y (j + 1) p).image (fun l => p :: l) else ∅)
  have hnil : ([] : List ℕ) ∉ (oddLt M).biUnion (fun p =>
        if j % 2 = 1 ∨ (p : ℝ) ≤ cut y ((j + 1) / 2)
          then (loChain y (j + 1) p).image (fun l => p :: l) else ∅) := by
    rw [Finset.mem_biUnion]
    rintro ⟨p, -, hp⟩
    by_cases hc : j % 2 = 1 ∨ (p : ℝ) ≤ cut y ((j + 1) / 2)
    · rw [if_pos hc] at hp
      obtain ⟨l, -, hl⟩ := Finset.mem_image.mp hp
      exact List.cons_ne_nil p l hl
    · rw [if_neg hc] at hp; simp at hp
  have hdisj : (↑(oddLt M) : Set ℕ).PairwiseDisjoint
      (fun p => if j % 2 = 1 ∨ (p : ℝ) ≤ cut y ((j + 1) / 2)
          then (loChain y (j + 1) p).image (fun l => p :: l) else ∅) := by
    rw [Finset.pairwiseDisjoint_iff]
    intro i hi jj hj hint
    by_cases hiD : j % 2 = 1 ∨ (i : ℝ) ≤ cut y ((j + 1) / 2)
    · by_cases hjD : j % 2 = 1 ∨ (jj : ℝ) ≤ cut y ((j + 1) / 2)
      · rw [if_pos hiD, if_pos hjD] at hint
        obtain ⟨x, hx⟩ := hint
        rw [Finset.mem_inter] at hx
        obtain ⟨hx1, hx2⟩ := hx
        obtain ⟨l, -, hl⟩ := Finset.mem_image.mp hx1
        obtain ⟨l', -, hl'⟩ := Finset.mem_image.mp hx2
        exact (List.cons.inj (hl.trans hl'.symm)).1
      · rw [if_neg hjD] at hint
        obtain ⟨x, hx⟩ := hint
        rw [Finset.mem_inter] at hx
        exact absurd hx.2 (by simp)
    · rw [if_neg hiD] at hint
      obtain ⟨x, hx⟩ := hint
      rw [Finset.mem_inter] at hx
      exact absurd hx.1 (by simp)
  have hterm : ∀ p ∈ oddLt M,
      ((if j % 2 = 1 ∨ (p : ℝ) ≤ cut y ((j + 1) / 2)
          then (loChain y (j + 1) p).image (fun l => p :: l) else ∅)).sum F
        = (if j % 2 = 1 ∨ (p : ℝ) ≤ cut y ((j + 1) / 2)
            then (loChain y (j + 1) p).sum (fun l => F (p :: l)) else 0) := by
    intro p hp
    by_cases hc : j % 2 = 1 ∨ (p : ℝ) ≤ cut y ((j + 1) / 2)
    · rw [if_pos hc, if_pos hc]
      exact Finset.sum_image (f := F) (g := fun l : List ℕ => p :: l)
        (fun a _ b _ hab => (List.cons.inj hab).2)
    · rw [if_neg hc, if_neg hc]; simp
  rw [loChain_unfold, hconv, Finset.sum_insert hnil, Finset.sum_biUnion hdisj,
    Finset.sum_congr rfl hterm]

lemma hiChain_decomp (y : ℝ) (j M : ℕ) (F : List ℕ → ℝ) :
    (hiChain y j M).sum F
      = F [] + ∑ p ∈ oddLt M,
          (if j % 2 = 0 ∨ (p : ℝ) ≤ cut y ((j + 1) / 2)
            then (hiChain y (j + 1) p).sum (fun l => F (p :: l)) else 0) := by
  have hconv : (oddLt M).attach.biUnion (fun p =>
        if j % 2 = 0 ∨ (p.1 : ℝ) ≤ cut y ((j + 1) / 2)
          then (hiChain y (j + 1) p.1).image (fun l => p.1 :: l) else ∅)
      = (oddLt M).biUnion (fun p =>
        if j % 2 = 0 ∨ (p : ℝ) ≤ cut y ((j + 1) / 2)
          then (hiChain y (j + 1) p).image (fun l => p :: l) else ∅) :=
    Finset.attach_biUnion (s := oddLt M)
      (f := fun p => if j % 2 = 0 ∨ (p : ℝ) ≤ cut y ((j + 1) / 2)
          then (hiChain y (j + 1) p).image (fun l => p :: l) else ∅)
  have hnil : ([] : List ℕ) ∉ (oddLt M).biUnion (fun p =>
        if j % 2 = 0 ∨ (p : ℝ) ≤ cut y ((j + 1) / 2)
          then (hiChain y (j + 1) p).image (fun l => p :: l) else ∅) := by
    rw [Finset.mem_biUnion]
    rintro ⟨p, -, hp⟩
    by_cases hc : j % 2 = 0 ∨ (p : ℝ) ≤ cut y ((j + 1) / 2)
    · rw [if_pos hc] at hp
      obtain ⟨l, -, hl⟩ := Finset.mem_image.mp hp
      exact List.cons_ne_nil p l hl
    · rw [if_neg hc] at hp; simp at hp
  have hdisj : (↑(oddLt M) : Set ℕ).PairwiseDisjoint
      (fun p => if j % 2 = 0 ∨ (p : ℝ) ≤ cut y ((j + 1) / 2)
          then (hiChain y (j + 1) p).image (fun l => p :: l) else ∅) := by
    rw [Finset.pairwiseDisjoint_iff]
    intro i hi jj hj hint
    by_cases hiD : j % 2 = 0 ∨ (i : ℝ) ≤ cut y ((j + 1) / 2)
    · by_cases hjD : j % 2 = 0 ∨ (jj : ℝ) ≤ cut y ((j + 1) / 2)
      · rw [if_pos hiD, if_pos hjD] at hint
        obtain ⟨x, hx⟩ := hint
        rw [Finset.mem_inter] at hx
        obtain ⟨hx1, hx2⟩ := hx
        obtain ⟨l, -, hl⟩ := Finset.mem_image.mp hx1
        obtain ⟨l', -, hl'⟩ := Finset.mem_image.mp hx2
        exact (List.cons.inj (hl.trans hl'.symm)).1
      · rw [if_neg hjD] at hint
        obtain ⟨x, hx⟩ := hint
        rw [Finset.mem_inter] at hx
        exact absurd hx.2 (by simp)
    · rw [if_neg hiD] at hint
      obtain ⟨x, hx⟩ := hint
      rw [Finset.mem_inter] at hx
      exact absurd hx.1 (by simp)
  have hterm : ∀ p ∈ oddLt M,
      ((if j % 2 = 0 ∨ (p : ℝ) ≤ cut y ((j + 1) / 2)
          then (hiChain y (j + 1) p).image (fun l => p :: l) else ∅)).sum F
        = (if j % 2 = 0 ∨ (p : ℝ) ≤ cut y ((j + 1) / 2)
            then (hiChain y (j + 1) p).sum (fun l => F (p :: l)) else 0) := by
    intro p hp
    by_cases hc : j % 2 = 0 ∨ (p : ℝ) ≤ cut y ((j + 1) / 2)
    · rw [if_pos hc, if_pos hc]
      exact Finset.sum_image (f := F) (g := fun l : List ℕ => p :: l)
        (fun a _ b _ hab => (List.cons.inj hab).2)
    · rw [if_neg hc, if_neg hc]; simp
  rw [hiChain_unfold, hconv, Finset.sum_insert hnil, Finset.sum_biUnion hdisj,
    Finset.sum_congr rfl hterm]

lemma dvd_mul_iff_left {p x m : ℕ} (hp : 0 < p) : p * x ∣ m ↔ p ∣ m ∧ x ∣ m / p := by
  constructor
  · intro h
    refine ⟨(dvd_mul_right p x).trans h, ?_⟩
    obtain ⟨k, hk⟩ := h
    have : m / p = x * k := by
      rw [hk, Nat.mul_assoc, Nat.mul_div_right (x*k) hp]
    rw [this]; exact dvd_mul_right x k
  · rintro ⟨h1, h2⟩
    obtain ⟨k, hk⟩ := h1
    obtain ⟨j, hj⟩ := h2
    have hkp : k = x * j := by
      have h2' := hj
      rw [hk, Nat.mul_div_right k hp] at h2'
      exact h2'
    rw [hk, hkp]
    exact ⟨j, by ring⟩

lemma Rlo_eq (y : ℝ) (j M m : ℕ) :
    Rlo y j M m = 1 + ∑ p ∈ oddLt M,
      (if j % 2 = 1 ∨ (p : ℝ) ≤ cut y ((j + 1) / 2) then
        (-1 : ℝ) * (if p ∣ m then 1 else 0) * Rlo y (j + 1) p (m / p) else 0) := by
  simp only [Rlo]
  rw [loChain_decomp y j M (fun c : List ℕ => (-1 : ℝ) ^ c.length * (if c.prod ∣ m then 1 else 0))]
  have hnil : (-1 : ℝ) ^ ([] : List ℕ).length * (if ([] : List ℕ).prod ∣ m then 1 else 0) = 1 := by
    simp
  rw [hnil]
  congr 1
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hp0 : 0 < p := (Finset.mem_filter.mp hp).2.1.pos
  by_cases hc : j % 2 = 1 ∨ (p : ℝ) ≤ cut y ((j + 1) / 2)
  · rw [if_pos hc, if_pos hc]
    have hpoint : ∀ l ∈ loChain y (j + 1) p,
        (-1:ℝ)^(p :: l).length * (if (p :: l).prod ∣ m then 1 else 0)
          = (-1) * (if p ∣ m then 1 else 0) *
              ((-1:ℝ)^l.length * (if l.prod ∣ (m / p) then 1 else 0)) := by
      intro l hl
      rw [List.length_cons, List.prod_cons, pow_succ]
      by_cases hpm : p ∣ m
      · rw [if_pos hpm]
        by_cases hl : l.prod ∣ m / p
        · have hgm : p * l.prod ∣ m := (dvd_mul_iff_left hp0).mpr ⟨hpm, hl⟩
          rw [if_pos hl, if_pos hgm]; ring
        · have hgm : ¬ (p * l.prod ∣ m) := fun h => hl ((dvd_mul_iff_left hp0).mp h).2
          rw [if_neg hl, if_neg hgm]; ring
      · have hgm : ¬ (p * l.prod ∣ m) := fun h => hpm ((dvd_mul_iff_left hp0).mp h).1
        rw [if_neg hpm, if_neg hgm]; ring
    rw [Finset.sum_congr rfl hpoint]
    rw [← Finset.mul_sum]
  · rw [if_neg hc, if_neg hc]

lemma Rhi_eq (y : ℝ) (j M m : ℕ) :
    Rhi y j M m = 1 + ∑ p ∈ oddLt M,
      (if j % 2 = 0 ∨ (p : ℝ) ≤ cut y ((j + 1) / 2) then
        (-1 : ℝ) * (if p ∣ m then 1 else 0) * Rhi y (j + 1) p (m / p) else 0) := by
  simp only [Rhi]
  rw [hiChain_decomp y j M (fun c : List ℕ => (-1 : ℝ) ^ c.length * (if c.prod ∣ m then 1 else 0))]
  have hnil : (-1 : ℝ) ^ ([] : List ℕ).length * (if ([] : List ℕ).prod ∣ m then 1 else 0) = 1 := by
    simp
  rw [hnil]
  congr 1
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hp0 : 0 < p := (Finset.mem_filter.mp hp).2.1.pos
  by_cases hc : j % 2 = 0 ∨ (p : ℝ) ≤ cut y ((j + 1) / 2)
  · rw [if_pos hc, if_pos hc]
    have hpoint : ∀ l ∈ hiChain y (j + 1) p,
        (-1:ℝ)^(p :: l).length * (if (p :: l).prod ∣ m then 1 else 0)
          = (-1) * (if p ∣ m then 1 else 0) *
              ((-1:ℝ)^l.length * (if l.prod ∣ (m / p) then 1 else 0)) := by
      intro l hl
      rw [List.length_cons, List.prod_cons, pow_succ]
      by_cases hpm : p ∣ m
      · rw [if_pos hpm]
        by_cases hl : l.prod ∣ m / p
        · have hgm : p * l.prod ∣ m := (dvd_mul_iff_left hp0).mpr ⟨hpm, hl⟩
          rw [if_pos hl, if_pos hgm]; ring
        · have hgm : ¬ (p * l.prod ∣ m) := fun h => hl ((dvd_mul_iff_left hp0).mp h).2
          rw [if_neg hl, if_neg hgm]; ring
      · have hgm : ¬ (p * l.prod ∣ m) := fun h => hpm ((dvd_mul_iff_left hp0).mp h).1
        rw [if_neg hpm, if_neg hgm]; ring
    rw [Finset.sum_congr rfl hpoint]
    rw [← Finset.mul_sum]
  · rw [if_neg hc, if_neg hc]

/-- coprimality with a squarefree product of primes. -/
lemma coprime_prod_prime_iff (m : ℕ) {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    m.Coprime (∏ p ∈ s, p) ↔ ∀ p ∈ s, ¬ p ∣ m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have has : ∀ p ∈ s, p.Prime := fun p hp => hs p (Finset.mem_insert_of_mem hp)
    rw [Finset.prod_insert ha, Nat.coprime_mul_iff_right, ih has]
    have hap : a.Prime := hs a (Finset.mem_insert_self a s)
    constructor
    · rintro ⟨h1, h2⟩ p hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact (Nat.Prime.coprime_iff_not_dvd hap).mp h1.symm
      · exact h2 p hp
    · intro h
      refine ⟨?_, fun p hp => h p (Finset.mem_insert_of_mem hp)⟩
      exact ((Nat.Prime.coprime_iff_not_dvd hap).mpr
        (fun hd => h a (Finset.mem_insert_self a s) hd)).symm

/-- coprimality with the odd primorial below `M`. -/
lemma coprime_oddPrimLt_iff (m M : ℕ) :
    m.Coprime (oddPrimLt M) ↔ ∀ p ∈ oddLt M, ¬ p ∣ m :=
  coprime_prod_prime_iff m (fun p hp => (Finset.mem_filter.mp hp).2.1)

/-- Buchstab identity for the ideal sifted indicator. -/
lemma buchstab_id (m M : ℕ) :
    Id m M = 1 - ∑ p ∈ oddLt M, (if p ∣ m then 1 else 0) * Id (m / p) p := by
  classical
  have hId : ∀ n t : ℕ, Id n t = if n.Coprime (oddPrimLt t) then 1 else 0 := fun n t => rfl
  rw [hId m M]
  by_cases hc : m.Coprime (oddPrimLt M)
  · rw [if_pos hc]
    have hM : ∀ p ∈ oddLt M, ¬ p ∣ m := (coprime_oddPrimLt_iff m M).mp hc
    have hz : ∀ p ∈ oddLt M, (if p ∣ m then (1:ℝ) else 0) * Id (m / p) p = 0 := by
      intro p hp; rw [if_neg (hM p hp)]; ring
    rw [Finset.sum_eq_zero hz]; ring
  · rw [if_neg hc]
    have hne : ((oddLt M).filter (fun p => p ∣ m)).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hemp
      refine hc ((coprime_oddPrimLt_iff m M).mpr (fun p hp hpm => ?_))
      have hmem : p ∈ (oddLt M).filter (fun p => p ∣ m) := Finset.mem_filter.mpr ⟨hp, hpm⟩
      rw [hemp] at hmem; exact absurd hmem (by simp)
    set P : ℕ := ((oddLt M).filter (fun p => p ∣ m)).min' hne with hPdef
    have hPmem : P ∈ oddLt M := (Finset.mem_filter.mp (Finset.min'_mem _ hne)).1
    have hPdvd : P ∣ m := (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2
    have hPprime : P.Prime := (Finset.mem_filter.mp hPmem).2.1
    have hPthree : 3 ≤ P := (Finset.mem_filter.mp hPmem).2.2
    have hPle : ∀ q ∈ oddLt M, q ∣ m → P ≤ q := fun q hq hqd =>
      Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hq, hqd⟩)
    have hkey : ∀ p ∈ oddLt M,
        (if p ∣ m then (1:ℝ) else 0) * Id (m / p) p = if p = P then 1 else 0 := by
      intro p hp
      by_cases hpP : p = P
      · subst hpP
        rw [if_pos hPdvd, if_pos rfl]
        have hone : Id (m / P) P = 1 := by
          have hcop : (m / P).Coprime (oddPrimLt P) := by
            rw [coprime_oddPrimLt_iff]
            intro q hq hqd
            have hqm : q ∣ m := dvd_trans hqd (Nat.div_dvd_of_dvd hPdvd)
            have hqM : q ∈ oddLt M := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
              (lt_trans (Finset.mem_range.mp (Finset.mem_filter.mp hq).1)
                (Finset.mem_range.mp (Finset.mem_filter.mp hPmem).1)),
              (Finset.mem_filter.mp hq).2⟩
            have hle := hPle q hqM hqm
            have hqlt : q < P := Finset.mem_range.mp (Finset.mem_filter.mp hq).1
            omega
          rw [hId, if_pos hcop]
        rw [hone]; ring
      · rw [if_neg hpP]
        by_cases hpm : p ∣ m
        · rw [if_pos hpm]
          have hnco : ¬ (m / p).Coprime (oddPrimLt p) := by
            rw [coprime_oddPrimLt_iff]; push_neg
            have hpPlt : P < p := lt_of_le_of_ne (hPle p hp hpm) (Ne.symm hpP)
            have hPdvdmp : P ∣ m / p := by
              obtain ⟨k, hk⟩ := hpm
              have hPk : P ∣ k := by
                rcases hPprime.dvd_mul.mp (hk ▸ hPdvd) with h | h
                · exfalso
                  have hEq : P = p := (Nat.prime_dvd_prime_iff_eq hPprime
                    (Finset.mem_filter.mp hp).2.1).mp h
                  exact hpP hEq.symm
                · exact h
              rw [hk, Nat.mul_div_right k (Finset.mem_filter.mp hp).2.1.pos]; exact hPk
            exact ⟨P, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hpPlt, hPprime, hPthree⟩, hPdvdmp⟩
          rw [hId, if_neg hnco]
          ring
        · rw [if_neg hpm]; ring
    rw [Finset.sum_congr rfl hkey]
    rw [Finset.sum_ite_eq' (oddLt M) P (fun _ => (1:ℝ)), if_pos hPmem]
    ring

lemma oddLt_eq_empty_of_le {M : ℕ} (h : M ≤ 3) : oddLt M = ∅ := by
  rw [oddLt, Finset.filter_eq_empty_iff]
  intro p hp hp'
  have := Finset.mem_range.mp hp
  omega

lemma loChain_eq_singleton_of (y : ℝ) (j M : ℕ) (h : oddLt M = ∅) :
    loChain y j M = {[]} := by
  rw [loChain_unfold, h]; simp

lemma hiChain_eq_singleton_of (y : ℝ) (j M : ℕ) (h : oddLt M = ∅) :
    hiChain y j M = {[]} := by
  rw [hiChain_unfold, h]; simp

lemma Rlo_eq_one_of (y : ℝ) (j M m : ℕ) (h : oddLt M = ∅) : Rlo y j M m = 1 := by
  unfold Rlo; rw [loChain_eq_singleton_of y j M h]; simp

lemma Rhi_eq_one_of (y : ℝ) (j M m : ℕ) (h : oddLt M = ∅) : Rhi y j M m = 1 := by
  unfold Rhi; rw [hiChain_eq_singleton_of y j M h]; simp

lemma Id_eq_one_of (m M : ℕ) (h : oddLt M = ∅) : Id m M = 1 := by
  unfold Id
  rw [show oddPrimLt M = ∏ p ∈ oddLt M, p from rfl, h]
  simp

lemma Id_nonneg (m M : ℕ) : 0 ≤ Id m M := by unfold Id; split <;> norm_num

/-- **Minorant / majorant property of the combinatorial sieve.**
`Rlo y 1 M ·` is a lower-bound sieve and `Rhi y 1 M ·` an upper-bound sieve for the
odd primes below `M`. -/
lemma chain_bounds (y : ℝ) (hy : 3 ≤ y) :
    ∀ M : ℕ,
      (∀ m j, j % 2 = 1 → Rlo y j M m ≤ Id m M) ∧
      (∀ m j, j % 2 = 0 → Id m M ≤ Rlo y j M m) ∧
      (∀ m j, j % 2 = 0 → Rhi y j M m ≤ Id m M) ∧
      (∀ m j, j % 2 = 1 → Id m M ≤ Rhi y j M m) := by
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
  by_cases hM : M ≤ 3
  · have hemp := oddLt_eq_empty_of_le hM
    refine ⟨fun m j _ => ?_, fun m j _ => ?_, fun m j _ => ?_, fun m j _ => ?_⟩
    · rw [Rlo_eq_one_of y j M m hemp, Id_eq_one_of m M hemp]
    · rw [Id_eq_one_of m M hemp, Rlo_eq_one_of y j M m hemp]
    · rw [Rhi_eq_one_of y j M m hemp, Id_eq_one_of m M hemp]
    · rw [Id_eq_one_of m M hemp, Rhi_eq_one_of y j M m hemp]
  · push_neg at hM
    have hlt : ∀ p ∈ oddLt M, p < M := fun p hp =>
      Finset.mem_range.mp (Finset.mem_filter.mp hp).1
    have ha0 : ∀ p m : ℕ, 0 ≤ (if p ∣ m then (1:ℝ) else 0) := by
      intro p m; split <;> norm_num
    refine ⟨fun m j hj => ?_, fun m j hj => ?_, fun m j hj => ?_, fun m j hj => ?_⟩
    · -- (A) j odd : Rlo ≤ Id
      rw [Rlo_eq, buchstab_id m M]
      have hcond : ∀ p ∈ oddLt M,
          (if j % 2 = 1 ∨ (p : ℝ) ≤ cut y ((j + 1) / 2) then
            (-1 : ℝ) * (if p ∣ m then 1 else 0) * Rlo y (j + 1) p (m / p) else 0)
            = (-1 : ℝ) * (if p ∣ m then 1 else 0) * Rlo y (j + 1) p (m / p) :=
        fun p hp => if_pos (Or.inl hj)
      rw [Finset.sum_congr rfl hcond]
      have hj1 : (j + 1) % 2 = 0 := by omega
      have hpt : ∀ p ∈ oddLt M,
          (-1 : ℝ) * (if p ∣ m then 1 else 0) * Rlo y (j + 1) p (m / p)
            + (if p ∣ m then 1 else 0) * Id (m / p) p ≤ 0 := by
        intro p hp
        have hle : Id (m / p) p ≤ Rlo y (j + 1) p (m / p) :=
          (ih p (hlt p hp)).2.1 (m / p) (j + 1) hj1
        have heq : (-1 : ℝ) * (if p ∣ m then 1 else 0) * Rlo y (j + 1) p (m / p)
            + (if p ∣ m then 1 else 0) * Id (m / p) p
            = (if p ∣ m then (1:ℝ) else 0) * (Id (m / p) p - Rlo y (j + 1) p (m / p)) := by
          ring
        rw [heq]; exact mul_nonpos_of_nonneg_of_nonpos (ha0 p m) (by linarith [hle])
      have hsum : ∑ p ∈ oddLt M,
          ((-1 : ℝ) * (if p ∣ m then 1 else 0) * Rlo y (j + 1) p (m / p)
            + (if p ∣ m then 1 else 0) * Id (m / p) p) ≤ 0 := Finset.sum_nonpos hpt
      rw [Finset.sum_add_distrib] at hsum
      linarith
    · -- (B) j even : Id ≤ Rlo
      rw [Rlo_eq, buchstab_id m M]
      have hj1 : (j + 1) % 2 = 1 := by omega
      have hpt : ∀ p ∈ oddLt M, 0 ≤
          (if j % 2 = 1 ∨ (p : ℝ) ≤ cut y ((j + 1) / 2) then
              (-1 : ℝ) * (if p ∣ m then 1 else 0) * Rlo y (j + 1) p (m / p) else 0)
            + ((if p ∣ m then 1 else 0) * Id (m / p) p) := by
        intro p hp
        by_cases hpc : (p : ℝ) ≤ cut y ((j + 1) / 2)
        · rw [if_pos (Or.inr hpc)]
          have hle : Rlo y (j + 1) p (m / p) ≤ Id (m / p) p :=
            (ih p (hlt p hp)).1 (m / p) (j + 1) hj1
          have heq : (-1 : ℝ) * (if p ∣ m then 1 else 0) * Rlo y (j + 1) p (m / p)
              + (if p ∣ m then 1 else 0) * Id (m / p) p
              = (if p ∣ m then (1:ℝ) else 0) * (Id (m / p) p - Rlo y (j + 1) p (m / p)) := by
            ring
          rw [heq]; exact mul_nonneg (ha0 p m) (by linarith [hle])
        · rw [if_neg (fun h => h.elim (by omega) hpc)]
          exact add_nonneg le_rfl (mul_nonneg (ha0 p m) (Id_nonneg (m / p) p))
      have hsum : 0 ≤ ∑ p ∈ oddLt M,
          ((if j % 2 = 1 ∨ (p : ℝ) ≤ cut y ((j + 1) / 2) then
              (-1 : ℝ) * (if p ∣ m then 1 else 0) * Rlo y (j + 1) p (m / p) else 0)
            + ((if p ∣ m then 1 else 0) * Id (m / p) p)) := Finset.sum_nonneg hpt
      rw [Finset.sum_add_distrib] at hsum
      linarith
    · -- (C) j even : Rhi ≤ Id
      rw [Rhi_eq, buchstab_id m M]
      have hcond : ∀ p ∈ oddLt M,
          (if j % 2 = 0 ∨ (p : ℝ) ≤ cut y ((j + 1) / 2) then
            (-1 : ℝ) * (if p ∣ m then 1 else 0) * Rhi y (j + 1) p (m / p) else 0)
            = (-1 : ℝ) * (if p ∣ m then 1 else 0) * Rhi y (j + 1) p (m / p) :=
        fun p hp => if_pos (Or.inl hj)
      rw [Finset.sum_congr rfl hcond]
      have hj1 : (j + 1) % 2 = 1 := by omega
      have hpt : ∀ p ∈ oddLt M,
          (-1 : ℝ) * (if p ∣ m then 1 else 0) * Rhi y (j + 1) p (m / p)
            + (if p ∣ m then 1 else 0) * Id (m / p) p ≤ 0 := by
        intro p hp
        have hle : Id (m / p) p ≤ Rhi y (j + 1) p (m / p) :=
          (ih p (hlt p hp)).2.2.2 (m / p) (j + 1) hj1
        have heq : (-1 : ℝ) * (if p ∣ m then 1 else 0) * Rhi y (j + 1) p (m / p)
            + (if p ∣ m then 1 else 0) * Id (m / p) p
            = (if p ∣ m then (1:ℝ) else 0) * (Id (m / p) p - Rhi y (j + 1) p (m / p)) := by
          ring
        rw [heq]; exact mul_nonpos_of_nonneg_of_nonpos (ha0 p m) (by linarith [hle])
      have hsum : ∑ p ∈ oddLt M,
          ((-1 : ℝ) * (if p ∣ m then 1 else 0) * Rhi y (j + 1) p (m / p)
            + (if p ∣ m then 1 else 0) * Id (m / p) p) ≤ 0 := Finset.sum_nonpos hpt
      rw [Finset.sum_add_distrib] at hsum
      linarith
    · -- (D) j odd : Id ≤ Rhi
      rw [Rhi_eq, buchstab_id m M]
      have hj1 : (j + 1) % 2 = 0 := by omega
      have hpt : ∀ p ∈ oddLt M, 0 ≤
          (if j % 2 = 0 ∨ (p : ℝ) ≤ cut y ((j + 1) / 2) then
              (-1 : ℝ) * (if p ∣ m then 1 else 0) * Rhi y (j + 1) p (m / p) else 0)
            + ((if p ∣ m then 1 else 0) * Id (m / p) p) := by
        intro p hp
        by_cases hpc : (p : ℝ) ≤ cut y ((j + 1) / 2)
        · rw [if_pos (Or.inr hpc)]
          have hle : Rhi y (j + 1) p (m / p) ≤ Id (m / p) p :=
            (ih p (hlt p hp)).2.2.1 (m / p) (j + 1) hj1
          have heq : (-1 : ℝ) * (if p ∣ m then 1 else 0) * Rhi y (j + 1) p (m / p)
              + (if p ∣ m then 1 else 0) * Id (m / p) p
              = (if p ∣ m then (1:ℝ) else 0) * (Id (m / p) p - Rhi y (j + 1) p (m / p)) := by
            ring
          rw [heq]; exact mul_nonneg (ha0 p m) (by linarith [hle])
        · rw [if_neg (fun h => h.elim (by omega) hpc)]
          exact add_nonneg le_rfl (mul_nonneg (ha0 p m) (Id_nonneg (m / p) p))
      have hsum : 0 ≤ ∑ p ∈ oddLt M,
          ((if j % 2 = 0 ∨ (p : ℝ) ≤ cut y ((j + 1) / 2) then
              (-1 : ℝ) * (if p ∣ m then 1 else 0) * Rhi y (j + 1) p (m / p) else 0)
            + ((if p ∣ m then 1 else 0) * Id (m / p) p)) := Finset.sum_nonneg hpt
      rw [Finset.sum_add_distrib] at hsum
      linarith

lemma mem_loChain_iff {y : ℝ} {j M : ℕ} {c : List ℕ} :
    c ∈ loChain y j M ↔ c = [] ∨ ∃ p tail, p ∈ oddLt M ∧
      (j % 2 = 1 ∨ (p : ℝ) ≤ cut y ((j + 1) / 2)) ∧ tail ∈ loChain y (j + 1) p ∧ c = p :: tail := by
  constructor
  · intro h
    rw [loChain_unfold] at h
    rcases Finset.mem_insert.mp h with h1 | h2
    · exact Or.inl h1
    · rcases Finset.mem_biUnion.mp h2 with ⟨p, hpatt, hpd⟩
      have hpm : p.1 ∈ oddLt M := p.2
      by_cases hc : j % 2 = 1 ∨ (p.1 : ℝ) ≤ cut y ((j + 1) / 2)
      · rw [if_pos hc] at hpd
        rcases Finset.mem_image.mp hpd with ⟨l, hl, heq⟩
        exact Or.inr ⟨p.1, l, hpm, hc, hl, heq.symm⟩
      · rw [if_neg hc] at hpd; simp at hpd
  · rintro (h1 | ⟨p, tail, hpm, hcond, htail, rfl⟩)
    · rw [h1, loChain_unfold]; exact Finset.mem_insert_self _ _
    · rw [loChain_unfold]
      refine Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨⟨p, hpm⟩, Finset.mem_attach _ _, ?_⟩)
      rw [if_pos hcond]
      exact Finset.mem_image.mpr ⟨tail, htail, rfl⟩

lemma loChain_elems_lt (y : ℝ) :
    ∀ M : ℕ, ∀ j (c : List ℕ), c ∈ loChain y j M → ∀ x ∈ c, x < M := by
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    intro j c hc x hx
    rw [mem_loChain_iff] at hc
    rcases hc with rfl | ⟨p, tail, hpM, hcond, htail, rfl⟩
    · exact absurd hx (by simp)
    · have hpMlt : p < M := Finset.mem_range.mp (Finset.mem_filter.mp hpM).1
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hpMlt
      · exact lt_trans (ih p hpMlt (j + 1) tail htail x hx') hpMlt

lemma loChain_pairwise (y : ℝ) :
    ∀ M : ℕ, ∀ j (c : List ℕ), c ∈ loChain y j M → c.Pairwise (· > ·) := by
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    intro j c hc
    rw [mem_loChain_iff] at hc
    rcases hc with rfl | ⟨p, tail, hpM, hcond, htail, rfl⟩
    · exact List.Pairwise.nil
    · refine List.pairwise_cons.mpr ⟨?_, ih p (Finset.mem_range.mp (Finset.mem_filter.mp hpM).1) (j+1) tail htail⟩
      intro a ha
      exact loChain_elems_lt y p (j+1) tail htail a ha

lemma loChain_even_le (y : ℝ) (hy : 1 ≤ y) :
    ∀ M : ℕ, ∀ j (c : List ℕ), c ∈ loChain y j M → ∀ (i : ℕ) (h : i < c.length),
      (j + i) % 2 = 0 → ((c.get ⟨i, h⟩ : ℕ) : ℝ) ≤ cut y ((j + i) / 2) := by
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    intro j c hc i hlen hev
    rw [mem_loChain_iff] at hc
    rcases hc with rfl | ⟨p, tail, hpM, hcond, htail, rfl⟩
    · simp at hlen
    · rcases i with _ | i'
      · -- i = 0
        have hpMlt : p < M := Finset.mem_range.mp (Finset.mem_filter.mp hpM).1
        have hc1 : (j + 0) % 2 = 0 := hev
        have hcut : (p : ℝ) ≤ cut y ((j + 0) / 2) := by
          rcases hcond with hodd | hle
          · -- j odd, but (j+0) even: contradiction? j%2=1 and (j+0)%2=0 impossible
            omega
          · -- j even: (j+1)/2 = j/2
            have : (j + 1) / 2 = j / 2 := by omega
            rwa [this] at hle
        simpa using hcut
      · -- i = i'+1
        have hlen' : i' < tail.length := by simpa using hlen
        have hev' : ((j + 1) + i') % 2 = 0 := by
          have : (j + 1) + i' = j + (i' + 1) := by ring
          rw [this]; simpa using hev
        have := ih p (Finset.mem_range.mp (Finset.mem_filter.mp hpM).1) (j + 1) tail htail i' hlen' hev'
        have hget : ((p :: tail).get ⟨i' + 1, hlen⟩ : ℕ) = tail.get ⟨i', hlen'⟩ := by
          simp
        rw [hget]
        convert this using 2 <;> omega

lemma loChain_one_elem_le (y : ℝ) (hy : 1 < y) (M : ℕ) (hM : M ≤ ⌊y⌋₊ + 1) :
    ∀ (c : List ℕ), c ∈ loChain y 1 M → ∀ (i : ℕ) (h : i < c.length),
      ((c.get ⟨i, h⟩ : ℕ) : ℝ) ≤ cut y ((1 + i) / 2) := by
  intro c hc i hlen
  have hylt : (1:ℝ) ≤ y := le_of_lt hy
  by_cases hev : (1 + i) % 2 = 0
  · exact loChain_even_le y hylt M 1 c hc i hlen (by simpa using hev)
  · rcases i with _ | i'
    · -- i = 0
      have hpMlt : ((c.get ⟨0, hlen⟩ : ℕ)) < M :=
        loChain_elems_lt y M 1 c hc _ (List.get_mem c ⟨0, hlen⟩)
      have hcut0 : cut y ((1 + 0) / 2) = y := by
        rw [show (1+0)/2 = 0 by norm_num, cut, pow_zero, Real.rpow_one]
      rw [hcut0]
      have hpy : ((c.get ⟨0, hlen⟩ : ℕ) : ℝ) ≤ (⌊y⌋₊ : ℝ) := by
        have h1 : c.get ⟨0, hlen⟩ ≤ ⌊y⌋₊ := by omega
        exact_mod_cast h1
      linarith [Nat.floor_le (by linarith : (0:ℝ) ≤ y)]
    · -- i = i'+1, i'+1 odd ⇒ i' even, use decreasing + even bound at i'
      have hlen' : i' < c.length := by omega
      have hev' : (1 + i') % 2 = 0 := by omega
      have hdec : ((c.get ⟨i' + 1, hlen⟩ : ℕ) : ℝ) < ((c.get ⟨i', hlen'⟩ : ℕ) : ℝ) := by
        have hpw := loChain_pairwise y M 1 c hc
        -- pairwise in a cons/list: get along the list
        have := List.pairwise_iff_get.mp hpw
        exact_mod_cast this ⟨i', hlen'⟩ ⟨i'+1, hlen⟩ (by simp)
      have heven := loChain_even_le y (le_of_lt hy) M 1 c hc i' hlen' (by simpa using hev')
      have hcutEq : (1 + i') / 2 = (1 + (i' + 1)) / 2 := by omega
      calc ((c.get ⟨i' + 1, hlen⟩ : ℕ) : ℝ) ≤ ((c.get ⟨i', hlen'⟩ : ℕ) : ℝ) := le_of_lt hdec
        _ ≤ cut y ((1 + i') / 2) := heven
        _ = cut y ((1 + (i' + 1)) / 2) := by rw [hcutEq]

lemma list_prod_le : ∀ (l : List ℕ) (f : ℕ → ℝ),
    (∀ i (hi : i < l.length), ((l.get ⟨i, hi⟩ : ℕ) : ℝ) ≤ f i) →
    (l.prod : ℝ) ≤ ∏ i ∈ Finset.range l.length, f i
  | [], f, h => by simp
  | a :: t, f, h => by
    rw [List.prod_cons, Nat.cast_mul, List.length_cons]
    have hg : ∏ i ∈ Finset.range (t.length + 1), f i
        = (∏ i ∈ Finset.range t.length, f (i+1)) * f 0 :=
      Finset.prod_range_succ' _ _
    rw [hg]
    have h0 : (a : ℝ) ≤ f 0 := h 0 (by simp)
    have ht : (t.prod : ℝ) ≤ ∏ i ∈ Finset.range t.length, f (i + 1) :=
      list_prod_le t (fun i => f (i+1)) (fun i hi => by
        have := h (i + 1) (by simpa using hi)
        simpa using this)
    have ht0 : (0:ℝ) ≤ (t.prod : ℝ) := Nat.cast_nonneg _
    have hf0 : (0:ℝ) ≤ f 0 := le_trans (Nat.cast_nonneg a) h0
    have hprod0 : (0:ℝ) ≤ ∏ i ∈ Finset.range t.length, f (i + 1) := by
      refine Finset.prod_nonneg (fun i hi => ?_)
      exact le_trans (Nat.cast_nonneg _) (h (i+1) (by simpa using hi))
    calc (a : ℝ) * (t.prod : ℝ) ≤ f 0 * (∏ i ∈ Finset.range t.length, f (i + 1)) :=
          mul_le_mul h0 ht ht0 hf0
      _ = (∏ i ∈ Finset.range t.length, f (i + 1)) * f 0 := mul_comm _ _

lemma sqrtsieveAlpha_lt : Real.sqrt sieveAlpha ≤ 4/5 := by
  rw [Real.sqrt_le_left (by norm_num)]
  rw [sieveAlpha]
  norm_num

lemma sieveAlpha_pow_le_sqrt_pow (i : ℕ) :
    sieveAlpha ^ ((1 + i) / 2) ≤ (Real.sqrt sieveAlpha) ^ i := by
  have hα : sieveAlpha = (Real.sqrt sieveAlpha)^2 := (Real.sq_sqrt (by
    rw [sieveAlpha]; norm_num)).symm
  have hx1 : (Real.sqrt sieveAlpha) ≤ 1 := by
    rw [Real.sqrt_le_one]; rw [sieveAlpha]; norm_num
  have hx0 : 0 ≤ Real.sqrt sieveAlpha := Real.sqrt_nonneg _
  have hle : i ≤ 2 * ((1 + i) / 2) := by omega
  have step1 : sieveAlpha ^ ((1 + i) / 2) = (Real.sqrt sieveAlpha) ^ (2 * ((1 + i) / 2)) := by
    conv_lhs => rw [hα]
    rw [← pow_mul]
  rw [step1]
  exact pow_le_pow_of_le_one hx0 hx1 hle

lemma geom_range_le (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, x^i ≤ 1/(1-x) := by
  rcases Nat.eq_zero_or_pos n with h | hn
  · subst h; rw [Finset.sum_range_zero]; exact div_nonneg zero_le_one (by linarith)
  · rw [geom_sum_eq (by linarith : x ≠ 1)]
    have h1 : (x^n - 1)/(x-1) = (1 - x^n)/(1-x) := by
      rw [show x^n - 1 = -(1 - x^n) by ring, show x - 1 = -(1 - x) by ring, neg_div_neg_eq]
    rw [h1]
    exact div_le_div_of_nonneg_right (by linarith [pow_nonneg hx0 n]) (by linarith)

lemma sieveAlpha_sum_le (r : ℕ) :
    ∑ i ∈ Finset.range r, sieveAlpha ^ ((1+i)/2) ≤ 399/100 := by
  have hα0 : 0 ≤ sieveAlpha := by rw [sieveAlpha]; norm_num
  have hα1 : sieveAlpha < 1 := by rw [sieveAlpha]; norm_num
  have hpos : (0:ℝ) < 1 - sieveAlpha := by linarith
  -- pairing bound: the terms come in pairs `(α^m, α^{m+1})`
  have hpair : ∀ m : ℕ, ∑ i ∈ Finset.range (2*m), sieveAlpha ^ ((1+i)/2)
      ≤ (1 + sieveAlpha) * ∑ j ∈ Finset.range m, sieveAlpha^j := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hsplit : ∑ i ∈ Finset.range (2*(m+1)), sieveAlpha ^ ((1+i)/2)
          = ∑ i ∈ Finset.range (2*m), sieveAlpha ^ ((1+i)/2)
            + (sieveAlpha^m + sieveAlpha^(m+1)) := by
        rw [show 2*(m+1) = 2*m+1+1 by omega, Finset.sum_range_succ, Finset.sum_range_succ]
        rw [show (1 + 2*m)/2 = m by omega, show (1 + (2*m+1))/2 = m+1 by omega]
        ring
      have h2 : ∑ j ∈ Finset.range (m+1), sieveAlpha^j
          = (∑ j ∈ Finset.range m, sieveAlpha^j) + sieveAlpha^m :=
        Finset.sum_range_succ _ _
      rw [hsplit, h2]
      have h3 : sieveAlpha^m + sieveAlpha^(m+1) = (1 + sieveAlpha) * sieveAlpha^m := by ring
      rw [h3]
      nlinarith [ih]
  have hmain : ∑ i ∈ Finset.range r, sieveAlpha ^ ((1+i)/2)
      ≤ (1 + sieveAlpha) * ∑ j ∈ Finset.range r, sieveAlpha^j := by
    refine le_trans ?_ (hpair r)
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => pow_nonneg hα0 _)
    intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  calc ∑ i ∈ Finset.range r, sieveAlpha ^ ((1+i)/2)
      ≤ (1 + sieveAlpha) * ∑ j ∈ Finset.range r, sieveAlpha^j := hmain
    _ ≤ (1 + sieveAlpha) * (1/(1-sieveAlpha)) :=
        mul_le_mul_of_nonneg_left (geom_range_le _ hα0 hα1 r) (by linarith)
    _ ≤ 399/100 := by
        rw [mul_one_div, div_le_iff₀ hpos]
        rw [sieveAlpha]; norm_num

lemma loChain_prod_le (y : ℝ) (hy : 1 < y) (M : ℕ) (hM : M ≤ ⌊y⌋₊ + 1) :
    ∀ c ∈ loChain y 1 M, (c.prod : ℝ) ≤ y ^ ((399:ℝ)/100) := by
  intro c hc
  refine le_trans (list_prod_le c (fun i => cut y ((1+i)/2))
    (fun i hi => loChain_one_elem_le y hy M hM c hc i hi)) ?_
  have h2 : ∏ i ∈ Finset.range c.length, cut y ((1+i)/2)
      = y ^ (∑ i ∈ Finset.range c.length, sieveAlpha ^ ((1+i)/2)) :=
    (Real.rpow_sum_of_nonneg (by linarith : (0:ℝ) ≤ y) (fun i hi => by
      exact pow_nonneg (by rw [sieveAlpha]; norm_num) _)).symm
  rw [h2]
  exact Real.rpow_le_rpow_of_exponent_le (le_of_lt hy) (sieveAlpha_sum_le c.length)

/-- the odd Euler product below `M`. -/
noncomputable def VsieveOdd (M : ℕ) : ℝ := ∏ p ∈ oddLt M, (1 - 1/((p:ℝ)-1))

lemma VsieveOdd_eq :
    ∀ M : ℕ, VsieveOdd M = 1 - ∑ p ∈ oddLt M, ((p:ℝ)-1)⁻¹ * VsieveOdd p := by
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    by_cases h3 : M ≤ 3
    · rw [oddLt_eq_empty_of_le h3, Finset.sum_empty]
      unfold VsieveOdd; rw [oddLt_eq_empty_of_le h3, Finset.prod_empty]; ring
    · push_neg at h3
      have hM1 : M - 1 < M := by omega
      have hr : Finset.range M = insert (M-1) (Finset.range (M-1)) := by
        ext x; simp only [Finset.mem_range, Finset.mem_insert]; omega
      have hnotin : (M - 1) ∉ oddLt (M - 1) := by
        rw [oddLt, Finset.mem_filter, Finset.mem_range]; omega
      have hoddLt : oddLt M = if (M-1).Prime ∧ 3 ≤ M-1 then insert (M-1) (oddLt (M-1))
          else oddLt (M-1) := by
        unfold oddLt
        rw [hr, Finset.filter_insert]
      have hprod : VsieveOdd M
          = (if (M-1).Prime ∧ 3 ≤ M-1 then (1 - (((M-1:ℕ):ℝ)-1)⁻¹) else 1) * VsieveOdd (M-1) := by
        unfold VsieveOdd
        rw [hoddLt]
        by_cases hp : (M-1).Prime ∧ 3 ≤ M-1
        · rw [if_pos hp, if_pos hp, Finset.prod_insert hnotin]
          simp only [one_div]
        · rw [if_neg hp, if_neg hp, one_mul]
      have ih1 := ih (M-1) hM1
      rw [hprod, hoddLt]
      by_cases hp : (M-1).Prime ∧ 3 ≤ M-1
      · rw [if_pos hp, if_pos hp, Finset.sum_insert hnotin]
        rw [ih1]
        have h3M : (3:ℝ) ≤ (((M-1:ℕ)):ℝ) := by exact_mod_cast hp.2
        have hne : (((M-1:ℕ):ℝ)) - 1 ≠ 0 := by linarith
        field_simp
        ring
      · rw [if_neg hp, if_neg hp, one_mul, ih1]

lemma list_prod_pos_of {l : List ℕ} (h : ∀ x ∈ l, 0 < x) : 0 < l.prod := by
  induction l with
  | nil => simp
  | cons a t ih => rw [List.prod_cons]; exact Nat.mul_pos (h a (by simp)) (ih (fun x hx => h x (by simp [hx])))

lemma loChain_elems_mem (y : ℝ) :
    ∀ M : ℕ, ∀ j (c : List ℕ), c ∈ loChain y j M → ∀ x ∈ c, x ∈ oddLt M := by
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    intro j c hc x hx
    rw [mem_loChain_iff] at hc
    rcases hc with rfl | ⟨p, tail, hpM, hcond, htail, rfl⟩
    · exact absurd hx (by simp)
    · rcases List.mem_cons.mp hx with rfl | hx'
      · exact hpM
      · have hpMlt : p < M := Finset.mem_range.mp (Finset.mem_filter.mp hpM).1
        have hxmem := ih p hpMlt (j + 1) tail htail x hx'
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (lt_trans (Finset.mem_range.mp (Finset.mem_filter.mp hxmem).1) hpMlt),
          (Finset.mem_filter.mp hxmem).2⟩

lemma prime_not_dvd_prod_lt {p : ℕ} (hp : p.Prime) (l : List ℕ)
    (hl : ∀ x ∈ l, x.Prime ∧ x < p) : ¬ p ∣ l.prod := by
  induction l with
  | nil => intro h; exact hp.ne_one (Nat.dvd_one.mp h)
  | cons a t ih =>
    rw [List.prod_cons]; intro hd
    rcases hp.dvd_mul.mp hd with h | h
    · have ha := hl a (by simp)
      have hpa : p = a := (Nat.prime_dvd_prime_iff_eq hp ha.1).mp h
      omega
    · exact ih (fun x hx => hl x (by simp [hx])) h

/-- the `lo`-chain weighted sum with weight `1/φ(∏c)`. -/
noncomputable def Elo (y : ℝ) (j M : ℕ) : ℝ :=
  (loChain y j M).sum (fun c => (-1:ℝ)^c.length / (Nat.totient c.prod : ℝ))

lemma Elo_eq (y : ℝ) (j M : ℕ) :
    Elo y j M = 1 - ∑ p ∈ oddLt M,
      (if j % 2 = 1 ∨ (p:ℝ) ≤ cut y ((j+1)/2) then ((p:ℝ)-1)⁻¹ * Elo y (j+1) p else 0) := by
  show (loChain y j M).sum (fun c => (-1:ℝ)^c.length / (Nat.totient c.prod : ℝ))
      = 1 - ∑ p ∈ oddLt M, (if j % 2 = 1 ∨ (p:ℝ) ≤ cut y ((j+1)/2) then
          ((p:ℝ)-1)⁻¹ * (loChain y (j+1) p).sum
            (fun c => (-1:ℝ)^c.length / (Nat.totient c.prod : ℝ)) else 0)
  rw [loChain_decomp y j M (fun c => (-1:ℝ)^c.length / (Nat.totient c.prod : ℝ))]
  have hnil : (-1:ℝ)^([] : List ℕ).length / (Nat.totient ([] : List ℕ).prod : ℝ) = 1 := by simp
  rw [hnil]
  have hpoint : ∀ p ∈ oddLt M,
      (if j % 2 = 1 ∨ (p:ℝ) ≤ cut y ((j+1)/2) then
        (loChain y (j+1) p).sum (fun l => (-1:ℝ)^(p::l).length / (Nat.totient (p::l).prod : ℝ)) else 0)
      = - (if j % 2 = 1 ∨ (p:ℝ) ≤ cut y ((j+1)/2) then
          ((p:ℝ)-1)⁻¹ * (loChain y (j+1) p).sum
            (fun c => (-1:ℝ)^c.length / (Nat.totient c.prod : ℝ)) else 0) := by
    intro p hp
    by_cases hc : j % 2 = 1 ∨ (p:ℝ) ≤ cut y ((j+1)/2)
    · rw [if_pos hc, if_pos hc]
      have hpprime : p.Prime := (Finset.mem_filter.mp hp).2.1
      have hsp : (loChain y (j+1) p).sum
            (fun l => (-1:ℝ)^(p::l).length / (Nat.totient (p::l).prod : ℝ))
          = - (((p:ℝ)-1)⁻¹ * (loChain y (j+1) p).sum
              (fun l => (-1:ℝ)^l.length / (Nat.totient l.prod : ℝ))) := by
        rw [Finset.sum_congr rfl (fun l hl => ?_), Finset.sum_neg_distrib, ← Finset.mul_sum]
        have hlt : ∀ x ∈ l, x.Prime ∧ x < p := fun x hx => by
          have hxm := loChain_elems_mem y p (j+1) l hl x hx
          exact ⟨(Finset.mem_filter.mp hxm).2.1, Finset.mem_range.mp (Finset.mem_filter.mp hxm).1⟩
        have hcop : p.Coprime l.prod := (hpprime.coprime_iff_not_dvd).mpr (prime_not_dvd_prod_lt hpprime l hlt)
        have hl1 : 0 < l.prod := list_prod_pos_of (fun x hx => (hlt x hx).1.pos)
        have htot : (Nat.totient (p * l.prod) : ℝ) = ((p:ℝ)-1) * (Nat.totient l.prod : ℝ) := by
          rw [Nat.totient_mul hcop, Nat.totient_prime hpprime]
          push_cast [Nat.cast_sub hpprime.one_le]
          ring
        have hpne : ((p:ℝ)-1) ≠ 0 := by
          have : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hpprime.two_le
          linarith
        have hphine : (Nat.totient l.prod : ℝ) ≠ 0 := by
          have : 0 < Nat.totient l.prod := Nat.totient_pos.mpr hl1
          exact_mod_cast this.ne'
        rw [List.length_cons, List.prod_cons, pow_succ, htot]
        field_simp
      rw [hsp]
    · rw [if_neg hc, if_neg hc]; ring
  rw [Finset.sum_congr rfl hpoint, Finset.sum_neg_distrib]
  ring

/-- the first-violation quantity: `VsieveOdd M − Elo y j M` computed by the Buchstab recursion. -/
noncomputable def VioFrom (y : ℝ) : ℕ → ℕ → ℝ
  | j, M => if j % 2 = 0 then
      - (∑ p ∈ (oddLt M).attach,
          (if cut y ((j+1)/2) < ((p:ℕ):ℝ) then (((p:ℕ):ℝ)-1)⁻¹ * VsieveOdd (p:ℕ) else 0))
      - ∑ p ∈ (oddLt M).attach,
          (if ((p:ℕ):ℝ) ≤ cut y ((j+1)/2) then (((p:ℕ):ℝ)-1)⁻¹ * VioFrom y (j+1) (p:ℕ) else 0)
    else
      - ∑ p ∈ (oddLt M).attach, (((p:ℕ):ℝ)-1)⁻¹ * VioFrom y (j+1) (p:ℕ)
  termination_by j M => M
  decreasing_by
    all_goals (exact Finset.mem_range.mp (Finset.mem_filter.mp (by simpa only [oddLt] using p.2)).1)

lemma VioFrom_even (y : ℝ) (j M : ℕ) (h : j % 2 = 0) :
    VioFrom y j M =
      - (∑ p ∈ oddLt M,
          (if cut y ((j+1)/2) < (p:ℝ) then ((p:ℝ)-1)⁻¹ * VsieveOdd p else 0))
      - ∑ p ∈ oddLt M,
          (if (p:ℝ) ≤ cut y ((j+1)/2) then ((p:ℝ)-1)⁻¹ * VioFrom y (j+1) p else 0) := by
  rw [VioFrom, if_pos h]
  rw [Finset.sum_attach (oddLt M)
        (fun q : ℕ => if cut y ((j+1)/2) < (q:ℝ) then ((q:ℝ)-1)⁻¹ * VsieveOdd q else 0),
      Finset.sum_attach (oddLt M)
        (fun q : ℕ => if (q:ℝ) ≤ cut y ((j+1)/2) then ((q:ℝ)-1)⁻¹ * VioFrom y (j+1) q else 0)]

lemma VioFrom_odd (y : ℝ) (j M : ℕ) (h : j % 2 = 1) :
    VioFrom y j M = - ∑ p ∈ oddLt M, ((p:ℝ)-1)⁻¹ * VioFrom y (j+1) p := by
  rw [VioFrom, if_neg (by omega)]
  rw [Finset.sum_attach (oddLt M) (fun q : ℕ => ((q:ℝ)-1)⁻¹ * VioFrom y (j+1) q)]

lemma VioFrom_eq (y : ℝ) : ∀ M : ℕ, ∀ j : ℕ, VioFrom y j M = VsieveOdd M - Elo y j M := by
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    intro j
    have hv : ∀ p ∈ oddLt M, VioFrom y (j+1) p = VsieveOdd p - Elo y (j+1) p :=
      fun p hp => ih p (Finset.mem_range.mp (Finset.mem_filter.mp hp).1) (j+1)
    by_cases hj : j % 2 = 0
    · have hElo_split : (∑ p ∈ oddLt M,
            (if j % 2 = 1 ∨ (p:ℝ) ≤ cut y ((j+1)/2) then ((p:ℝ)-1)⁻¹ * Elo y (j+1) p else 0))
          = ∑ p ∈ oddLt M,
            (if (p:ℝ) ≤ cut y ((j+1)/2) then ((p:ℝ)-1)⁻¹ * Elo y (j+1) p else 0) := by
        refine Finset.sum_congr rfl (fun p hp => ?_)
        by_cases hc : (p:ℝ) ≤ cut y ((j+1)/2)
        · simp only [if_pos (Or.inr hc), if_pos hc]
        · have hneg : ¬ (j % 2 = 1 ∨ (p:ℝ) ≤ cut y ((j+1)/2)) := by
            rintro (h1 | h2)
            · omega
            · exact hc h2
          rw [if_neg hneg, if_neg hc]
      have hBs : (∑ p ∈ oddLt M,
            (if (p:ℝ) ≤ cut y ((j+1)/2) then ((p:ℝ)-1)⁻¹ * (VsieveOdd p - Elo y (j+1) p) else 0))
          = (∑ p ∈ oddLt M,
              (if (p:ℝ) ≤ cut y ((j+1)/2) then ((p:ℝ)-1)⁻¹ * VsieveOdd p else 0))
            - ∑ p ∈ oddLt M,
              (if (p:ℝ) ≤ cut y ((j+1)/2) then ((p:ℝ)-1)⁻¹ * Elo y (j+1) p else 0) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun p hp => ?_)
        by_cases hc : (p:ℝ) ≤ cut y ((j+1)/2)
        · rw [if_pos hc, if_pos hc, if_pos hc]; ring
        · rw [if_neg hc, if_neg hc, if_neg hc]; ring
      have hAc : (∑ p ∈ oddLt M,
              (if cut y ((j+1)/2) < (p:ℝ) then ((p:ℝ)-1)⁻¹ * VsieveOdd p else 0))
            + (∑ p ∈ oddLt M,
              (if (p:ℝ) ≤ cut y ((j+1)/2) then ((p:ℝ)-1)⁻¹ * VsieveOdd p else 0))
          = ∑ p ∈ oddLt M, ((p:ℝ)-1)⁻¹ * VsieveOdd p := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun p hp => ?_)
        by_cases hc : cut y ((j+1)/2) < (p:ℝ)
        · rw [if_pos hc, if_neg (not_le.mpr hc)]; ring
        · rw [if_neg hc, if_pos (not_lt.mp hc)]; ring
      have hB : (∑ p ∈ oddLt M,
            (if (p:ℝ) ≤ cut y ((j+1)/2) then ((p:ℝ)-1)⁻¹ * VioFrom y (j+1) p else 0))
          = ∑ p ∈ oddLt M,
            (if (p:ℝ) ≤ cut y ((j+1)/2) then ((p:ℝ)-1)⁻¹ * (VsieveOdd p - Elo y (j+1) p) else 0) :=
        Finset.sum_congr rfl (fun p hp => by rw [hv p hp])
      rw [VioFrom_even y j M hj, Elo_eq, VsieveOdd_eq, hElo_split, hB, hBs, ← hAc]
      ring
    · have hj1 : j % 2 = 1 := by omega
      have hElo_split : (∑ p ∈ oddLt M,
            (if j % 2 = 1 ∨ (p:ℝ) ≤ cut y ((j+1)/2) then ((p:ℝ)-1)⁻¹ * Elo y (j+1) p else 0))
          = ∑ p ∈ oddLt M, ((p:ℝ)-1)⁻¹ * Elo y (j+1) p :=
        Finset.sum_congr rfl (fun p hp => if_pos (Or.inl hj1))
      have hB : (∑ p ∈ oddLt M, ((p:ℝ)-1)⁻¹ * VioFrom y (j+1) p)
          = ∑ p ∈ oddLt M, ((p:ℝ)-1)⁻¹ * (VsieveOdd p - Elo y (j+1) p) :=
        Finset.sum_congr rfl (fun p hp => by rw [hv p hp])
      have hdist : ∀ p ∈ oddLt M, ((p:ℝ)-1)⁻¹ * (VsieveOdd p - Elo y (j+1) p)
          = ((p:ℝ)-1)⁻¹ * VsieveOdd p - ((p:ℝ)-1)⁻¹ * Elo y (j+1) p := fun p hp => by ring
      rw [VioFrom_odd y j M hj1, Elo_eq, VsieveOdd_eq, hElo_split, hB,
        Finset.sum_congr rfl hdist, Finset.sum_sub_distrib]
      ring

lemma inv_pred_nonneg {p : ℕ} (hp : p.Prime) : (0:ℝ) ≤ ((p:ℝ)-1)⁻¹ := by
  have h : (0:ℝ) < (p:ℝ) - 1 := by
    have h2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.two_le
    linarith
  exact inv_nonneg.mpr (le_of_lt h)

/-- the upper envelope of `|VioFrom|`. -/
noncomputable def Bnd (y : ℝ) : ℕ → ℕ → ℝ
  | j, M => if j % 2 = 0 then
      (∑ p ∈ (oddLt M).attach,
          (if cut y ((j+1)/2) < ((p:ℕ):ℝ) then (((p:ℕ):ℝ)-1)⁻¹ * VsieveOdd (p:ℕ) else 0))
      + ∑ p ∈ (oddLt M).attach,
          (if ((p:ℕ):ℝ) ≤ cut y ((j+1)/2) then (((p:ℕ):ℝ)-1)⁻¹ * Bnd y (j+1) (p:ℕ) else 0)
    else
      ∑ p ∈ (oddLt M).attach, (((p:ℕ):ℝ)-1)⁻¹ * Bnd y (j+1) (p:ℕ)
  termination_by j M => M
  decreasing_by
    all_goals (exact Finset.mem_range.mp (Finset.mem_filter.mp (by simpa only [oddLt] using p.2)).1)

lemma Bnd_even (y : ℝ) (j M : ℕ) (h : j % 2 = 0) :
    Bnd y j M =
      (∑ p ∈ oddLt M,
          (if cut y ((j+1)/2) < (p:ℝ) then ((p:ℝ)-1)⁻¹ * VsieveOdd p else 0))
      + ∑ p ∈ oddLt M,
          (if (p:ℝ) ≤ cut y ((j+1)/2) then ((p:ℝ)-1)⁻¹ * Bnd y (j+1) p else 0) := by
  rw [Bnd, if_pos h]
  rw [Finset.sum_attach (oddLt M)
        (fun q : ℕ => if cut y ((j+1)/2) < (q:ℝ) then ((q:ℝ)-1)⁻¹ * VsieveOdd q else 0),
      Finset.sum_attach (oddLt M)
        (fun q : ℕ => if (q:ℝ) ≤ cut y ((j+1)/2) then ((q:ℝ)-1)⁻¹ * Bnd y (j+1) q else 0)]

lemma Bnd_odd (y : ℝ) (j M : ℕ) (h : j % 2 = 1) :
    Bnd y j M = ∑ p ∈ oddLt M, ((p:ℝ)-1)⁻¹ * Bnd y (j+1) p := by
  rw [Bnd, if_neg (by omega)]
  rw [Finset.sum_attach (oddLt M) (fun q : ℕ => ((q:ℝ)-1)⁻¹ * Bnd y (j+1) q)]

lemma VsieveOdd_nonneg (M : ℕ) : 0 ≤ VsieveOdd M := by
  unfold VsieveOdd
  refine Finset.prod_nonneg (fun p hp => ?_)
  have h3 : 3 ≤ p := (Finset.mem_filter.mp hp).2.2
  have hpR : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast h3
  have hne : (p:ℝ) - 1 ≠ 0 := by linarith
  have heq : (1:ℝ) - 1/((p:ℝ)-1) = ((p:ℝ)-2)/((p:ℝ)-1) := by field_simp; ring
  rw [heq]; exact div_nonneg (by linarith) (by linarith)

lemma abs_VioFrom_le_Bnd (y : ℝ) : ∀ M : ℕ, ∀ j : ℕ, |VioFrom y j M| ≤ Bnd y j M := by
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    intro j
    by_cases hj : j % 2 = 0
    · rw [VioFrom_even y j M hj, Bnd_even y j M hj]
      set A := ∑ p ∈ oddLt M, (if cut y ((j+1)/2) < (p:ℝ) then ((p:ℝ)-1)⁻¹ * VsieveOdd p else 0) with hA
      set B := ∑ p ∈ oddLt M, (if (p:ℝ) ≤ cut y ((j+1)/2) then ((p:ℝ)-1)⁻¹ * VioFrom y (j+1) p else 0) with hB
      set T := ∑ p ∈ oddLt M, (if (p:ℝ) ≤ cut y ((j+1)/2) then ((p:ℝ)-1)⁻¹ * Bnd y (j+1) p else 0) with hT
      have hAnn : 0 ≤ A := by
        rw [hA]
        refine Finset.sum_nonneg (fun p hp => ?_)
        by_cases hc : cut y ((j+1)/2) < (p:ℝ)
        · rw [if_pos hc]
          exact mul_nonneg (inv_pred_nonneg (Finset.mem_filter.mp hp).2.1) (VsieveOdd_nonneg p)
        · rw [if_neg hc]
      have hBabs : |B| ≤ T := by
        rw [hB, hT]
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        refine Finset.sum_le_sum (fun p hp => ?_)
        by_cases hc : (p:ℝ) ≤ cut y ((j+1)/2)
        · rw [if_pos hc, if_pos hc, abs_mul, abs_of_nonneg (inv_pred_nonneg (Finset.mem_filter.mp hp).2.1)]
          exact mul_le_mul_of_nonneg_left
            (ih p (Finset.mem_range.mp (Finset.mem_filter.mp hp).1) (j+1))
            (inv_pred_nonneg (Finset.mem_filter.mp hp).2.1)
        · rw [if_neg hc, if_neg hc, abs_zero]
      have htri : |-A - B| ≤ A + |B| := by
        have h1 : (-A - B : ℝ) = -((A) + (B)) := by ring
        rw [h1, abs_neg]
        calc |A + B| ≤ |A| + |B| := abs_add_le A B
          _ = A + |B| := by rw [abs_of_nonneg hAnn]
      linarith
    · have hj1 : j % 2 = 1 := by omega
      rw [VioFrom_odd y j M hj1, Bnd_odd y j M hj1, abs_neg]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine Finset.sum_le_sum (fun p hp => ?_)
      rw [abs_mul, abs_of_nonneg (inv_pred_nonneg (Finset.mem_filter.mp hp).2.1)]
      exact mul_le_mul_of_nonneg_left
        (ih p (Finset.mem_range.mp (Finset.mem_filter.mp hp).1) (j+1))
        (inv_pred_nonneg (Finset.mem_filter.mp hp).2.1)

/-- the "violation at level `j`" sum: lo-compatible prefixes of length `2j-1`, an element
`q > cut y j` below all of them, weighted by `1/φ(∏c) · (q−1)⁻¹ · VsieveOdd q`. -/
noncomputable def V2T (y : ℝ) (j M : ℕ) : ℝ :=
  (((loChain y 1 M).filter (fun c => c.length = 2*j - 1))).sum (fun c =>
    (1 / (Nat.totient c.prod : ℝ)) *
      ((oddLt M).filter (fun q : ℕ => cut y j < (q:ℝ) ∧ ∀ x ∈ c, q < x)).sum
        (fun q => ((q:ℝ)-1)⁻¹ * VsieveOdd q))

/-- the "lo-compatible prefix continuation": prefixes of length `2k` weighted by `1/φ(∏c)`
and multiplied by `Bnd (2k+1)` at the last element.  The summand is PROOF-FREE
(`(c.getLast?).getD 0`), so `Finset.sum_congr`/`Finset.sum_image` fire directly and no
`.attach`/membership is ever needed; for `c ∈ filter (length = 2k)` with `k ≥ 1`, `c ≠ []`
and `(c.getLast?).getD 0 = c.getLast _`. -/
noncomputable def PB (y : ℝ) (k M : ℕ) : ℝ :=
  ((loChain y 1 M).filter (fun c => c.length = 2*k)).sum (fun c =>
    (1 / (Nat.totient c.prod : ℝ)) * Bnd y (2*k+1) ((c.getLast?).getD 0))

lemma oddLt_mono {M M' : ℕ} (h : M ≤ M') : oddLt M ⊆ oddLt M' := by
  intro x hx
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
    (lt_of_lt_of_le (Finset.mem_range.mp (Finset.mem_filter.mp hx).1) h),
    (Finset.mem_filter.mp hx).2⟩

lemma mem_oddLt_of {x M p : ℕ} (hx : x ∈ oddLt M) (hxp : x < p) : x ∈ oddLt p :=
  Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hxp, (Finset.mem_filter.mp hx).2⟩

/-- **Filtration lemma.**  The chains in `loChain y j M` are exactly the strictly decreasing
lists of elements of `oddLt M` whose entry at every EVEN position `j+i` is below the corresponding
cut-off. -/
lemma mem_loChain_iff' (y : ℝ) :
    ∀ M : ℕ, ∀ j (c : List ℕ), c ∈ loChain y j M ↔
      c.Pairwise (· > ·) ∧ (∀ x ∈ c, x ∈ oddLt M) ∧
        (∀ (i : ℕ) (h : i < c.length), (j + i) % 2 = 0 →
          ((c.get ⟨i, h⟩ : ℕ) : ℝ) ≤ cut y ((j + i) / 2)) := by
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    intro j c
    constructor
    · intro hc
      rw [mem_loChain_iff] at hc
      rcases hc with rfl | ⟨p, tail, hpM, hcond, htail, rfl⟩
      · exact ⟨List.Pairwise.nil, by simp, by intro i hi; simp at hi⟩
      · have hpMlt : p < M := Finset.mem_range.mp (Finset.mem_filter.mp hpM).1
        obtain ⟨htp, hte, hpos⟩ := (ih p hpMlt (j+1) tail).mp htail
        refine ⟨?_, ?_, ?_⟩
        · rw [List.pairwise_cons]
          exact ⟨fun a' ha' => Finset.mem_range.mp (Finset.mem_filter.mp (hte a' ha')).1, htp⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact hpM
          · exact oddLt_mono (le_of_lt hpMlt) (hte x hx')
        · intro i hi hev
          rcases i with _ | i'
          · rw [show (p :: tail).get ⟨0, hi⟩ = p from by simp]
            have hje : j % 2 = 0 := by simpa using hev
            rcases hcond with h | h
            · omega
            · rwa [show (j+1)/2 = j/2 by omega] at h
          · rw [List.get_cons_succ, show j + (i' + 1) = j + 1 + i' by omega]
            exact hpos i' _ (by omega)
    · rintro ⟨hpw, hmem, hpos⟩
      rw [mem_loChain_iff]
      rcases c with _ | ⟨p, tail⟩
      · exact Or.inl rfl
      · refine Or.inr ⟨p, tail, hmem p (by simp), ?_, ?_, rfl⟩
        · rw [List.pairwise_cons] at hpw
          rcases hpw with ⟨hpw1, hpw2⟩
          by_cases hje : j % 2 = 0
          · right
            rw [show (j+1)/2 = j/2 by omega]
            exact hpos 0 (by simp) (by simpa using hje)
          · left
            omega
        · have hpw1 : ∀ a' ∈ tail, (p : ℕ) > a' := (List.pairwise_cons.mp hpw).1
          have hpw2 : tail.Pairwise (· > ·) := (List.pairwise_cons.mp hpw).2
          refine (ih p (Finset.mem_range.mp (Finset.mem_filter.mp (hmem p (by simp))).1) (j+1) tail).mpr
            ⟨hpw2, ?_, ?_⟩
          · intro x hx
            exact mem_oddLt_of (hmem x (List.mem_cons_of_mem p hx)) (hpw1 x hx)
          · intro i hi hev
            have h1 := hpos (i+1) (by simpa using hi) (by omega)
            rwa [List.get_cons_succ, show j + (i+1) = (j+1) + i by omega] at h1

lemma loChain_len_one (y : ℝ) (M : ℕ) :
    (loChain y 1 M).filter (fun c => c.length = 1) = (oddLt M).image (fun p => [p]) := by
  ext c
  constructor
  · intro hc
    rcases Finset.mem_filter.mp hc with ⟨hc1, hclen⟩
    obtain ⟨p, rfl⟩ := List.length_eq_one_iff.mp hclen
    exact Finset.mem_image.mpr ⟨p, ((mem_loChain_iff' y M 1 [p]).mp hc1).2.1 p (by simp), rfl⟩
  · intro hc
    rcases Finset.mem_image.mp hc with ⟨p, hp, rfl⟩
    refine Finset.mem_filter.mpr ⟨(mem_loChain_iff' y M 1 [p]).mpr ⟨by simp, ?_, ?_⟩, by simp⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hp
      · simp at hx
    · intro i hi hev
      have h0 : i = 0 := by simpa using hi
      subst h0
      omega

lemma loChain_len_two (y : ℝ) (M : ℕ) :
    (loChain y 1 M).filter (fun c => c.length = 2)
      = (oddLt M).biUnion (fun p =>
          ((oddLt p).filter (fun q : ℕ => (q:ℝ) ≤ cut y 1)).image (fun q => [p, q])) := by
  ext c
  constructor
  · intro hc
    rcases Finset.mem_filter.mp hc with ⟨hc1, hclen⟩
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hclen
    obtain ⟨hpw, hmem, hpos⟩ := (mem_loChain_iff' y M 1 [a, b]).mp hc1
    have hab : b < a := by
      have h := (List.pairwise_cons.mp hpw).1 b (by simp)
      simpa using h
    refine Finset.mem_biUnion.mpr ⟨a, hmem a (by simp), ?_⟩
    refine Finset.mem_image.mpr ⟨b, ?_, rfl⟩
    refine Finset.mem_filter.mpr ⟨mem_oddLt_of (hmem b (by simp)) hab, ?_⟩
    have h := hpos 1 (by simp) (by norm_num)
    simpa using h
  · intro hc
    rcases Finset.mem_biUnion.mp hc with ⟨p, hp, hc⟩
    rcases Finset.mem_image.mp hc with ⟨q, hq, rfl⟩
    rcases Finset.mem_filter.mp hq with ⟨hqp, hqcut⟩
    refine Finset.mem_filter.mpr ⟨(mem_loChain_iff' y M 1 [p, q]).mpr ⟨?_, ?_, ?_⟩, by simp⟩
    · rw [List.pairwise_cons]
      refine ⟨?_, by simp⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Finset.mem_range.mp (Finset.mem_filter.mp hqp).1
      · simp at hx
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hp
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact oddLt_mono (le_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp hp).1)) hqp
        · simp at hx
    · intro i hi hev
      have hi2 : i < 2 := by simpa using hi
      interval_cases i
      · omega
      · rw [show ([p, q].get ⟨1, ‹1 < [p,q].length›⟩ : ℕ) = q from by simp]
        simpa using hqcut

lemma V2T_one (y : ℝ) (M : ℕ) :
    V2T y 1 M = ∑ p ∈ oddLt M, ((p:ℝ)-1)⁻¹ *
      ∑ q ∈ (oddLt p).filter (fun q : ℕ => cut y 1 < (q:ℝ)), ((q:ℝ)-1)⁻¹ * VsieveOdd q := by
  unfold V2T
  have h2 : (2*1-1 : ℕ) = 1 := by norm_num
  have hinj : Set.InjOn (fun p : ℕ => ([p] : List ℕ)) ↑(oddLt M) := by
    intro a _ b _ h; simpa using h
  rw [h2, loChain_len_one, Finset.sum_image hinj]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hpprime : p.Prime := (Finset.mem_filter.mp hp).2.1
  have hpmem : ∀ x ∈ ([p] : List ℕ), x ∈ oddLt M := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hp
    · simp at hx
  have hpmem2 : ∀ x ∈ ([p] : List ℕ), x.Prime ∧ 3 ≤ x := by
    intro x hx
    exact (Finset.mem_filter.mp (hpmem x hx)).2
  have htot : (Nat.totient ([p] : List ℕ).prod : ℝ) = (p:ℝ) - 1 := by
    rw [List.prod_singleton, Nat.totient_prime hpprime,
        Nat.cast_sub (R := ℝ) hpprime.one_le, Nat.cast_one]
  have hfil : (oddLt M).filter (fun q : ℕ => cut y 1 < (q:ℝ) ∧ ∀ x ∈ ([p] : List ℕ), q < x)
      = (oddLt p).filter (fun q : ℕ => cut y 1 < (q:ℝ)) := by
    ext q
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hq, hcq, hqx⟩
      exact ⟨mem_oddLt_of hq (by have := hqx p (by simp); simpa using this), hcq⟩
    · rintro ⟨hqp, hcq⟩
      refine ⟨oddLt_mono (le_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp hp).1)) hqp, hcq, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Finset.mem_range.mp (Finset.mem_filter.mp hqp).1
      · simp at hx
  rw [htot, hfil]
  congr 1
  rw [one_div]

lemma PB_one (y : ℝ) (M : ℕ) :
    PB y 1 M = ∑ p ∈ oddLt M, ((p:ℝ)-1)⁻¹ *
      ∑ q ∈ (oddLt p).filter (fun q : ℕ => (q:ℝ) ≤ cut y 1), ((q:ℝ)-1)⁻¹ * Bnd y 3 q := by
  unfold PB
  rw [show (2*1 : ℕ) = 2 from by norm_num, loChain_len_two]
  rw [Finset.sum_biUnion]
  swap
  · intro p hp p' hp' hne
    refine Finset.disjoint_left.mpr (fun c hc hc' => ?_)
    rcases Finset.mem_image.mp hc with ⟨q, _, hq⟩
    rcases Finset.mem_image.mp hc' with ⟨q', _, hq'⟩
    exact hne (List.cons.inj (hq.trans hq'.symm)).1
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hinj2 : Set.InjOn (fun q : ℕ => ([p, q] : List ℕ))
      ↑((oddLt p).filter (fun q : ℕ => (q:ℝ) ≤ cut y 1)) := by
    intro a _ b _ h; simpa using h
  rw [Finset.sum_image hinj2, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  rw [show (2*1+1 : ℕ) = 3 from by norm_num]
  have hpP : p.Prime := (Finset.mem_filter.mp hp).2.1
  have hqp : q ∈ oddLt p := (Finset.mem_filter.mp hq).1
  have hqP : q.Prime := (Finset.mem_filter.mp hqp).2.1
  have hqltp : q < p := Finset.mem_range.mp (Finset.mem_filter.mp hqp).1
  have hcop : p.Coprime q := (hpP.coprime_iff_not_dvd).mpr (fun hd => by
    have hpq := (Nat.prime_dvd_prime_iff_eq hpP hqP).mp hd
    omega)
  have htot : (Nat.totient (p * q) : ℝ) = ((p:ℝ)-1) * ((q:ℝ)-1) := by
    rw [Nat.totient_mul hcop, Nat.totient_prime hpP, Nat.totient_prime hqP, Nat.cast_mul,
      Nat.cast_sub (R := ℝ) hpP.one_le, Nat.cast_sub (R := ℝ) hqP.one_le, Nat.cast_one]
  have hpne : ((p:ℝ)-1) ≠ 0 := by
    have : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hpP.two_le
    linarith
  have hqne : ((q:ℝ)-1) ≠ 0 := by
    have : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hqP.two_le
    linarith
  simp only [List.prod_cons, List.prod_nil, mul_one]
  rw [show ((p :: q :: ([] : List ℕ)).getLast?).getD 0 = q from by simp]
  rw [htot]
  field_simp

lemma Bnd_one_eq (y : ℝ) (M : ℕ) :
    Bnd y 1 M = V2T y 1 M + PB y 1 M := by
  have hB : ∀ p : ℕ, Bnd y 2 p =
      (∑ q ∈ (oddLt p).filter (fun q : ℕ => cut y 1 < (q:ℝ)), ((q:ℝ)-1)⁻¹ * VsieveOdd q)
      + ∑ q ∈ (oddLt p).filter (fun q : ℕ => (q:ℝ) ≤ cut y 1), ((q:ℝ)-1)⁻¹ * Bnd y 3 q := by
    intro p
    rw [Bnd_even y 2 p (by norm_num)]
    rw [show (2+1:ℕ)/2 = 1 from by norm_num, show (2+1:ℕ) = 3 from by norm_num]
    rw [← Finset.sum_filter, ← Finset.sum_filter]
  rw [V2T_one, PB_one, Bnd_odd y 1 M (by norm_num)]
  rw [show (1+1:ℕ) = 2 from by norm_num]
  simp only [hB, mul_add, Finset.sum_add_distrib]

/-- **Step 2 of recurrence (2).**  Expand `PB y k M` one level: peel `Bnd y (2k+1)` at the
last element of each lo-compatible prefix of length `2k`. -/
lemma PB_expand (y : ℝ) (k M : ℕ) :
    PB y k M = ∑ c ∈ (loChain y 1 M).filter (fun c => c.length = 2*k),
      (1 / (Nat.totient c.prod : ℝ)) *
        ∑ p ∈ oddLt ((c.getLast?).getD 0), ((p:ℝ)-1)⁻¹ * Bnd y (2*k+2) p := by
  unfold PB
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Bnd_odd y (2*k+1) ((c.getLast?).getD 0) (by omega),
    show (2*k+1+1 : ℕ) = 2*k+2 from by omega]

/-- **Step 3, ⊆ direction, core piece**: dropping the last element of a `loChain` element keeps
it in `loChain y 1 M`. -/
lemma loChain_dropLast (y : ℝ) (M : ℕ) {c : List ℕ} (hc : c ∈ loChain y 1 M) :
    c.dropLast ∈ loChain y 1 M := by
  obtain ⟨hpw, hmem, hpos⟩ := (mem_loChain_iff' y M 1 c).mp hc
  refine (mem_loChain_iff' y M 1 c.dropLast).mpr ⟨?_, ?_, ?_⟩
  · rw [List.dropLast_eq_take]
    exact hpw.take
  · intro x hx
    rw [List.dropLast_eq_take] at hx
    exact hmem x (List.mem_of_mem_take hx)
  · intro i hi hev
    have h2 : i < c.length := by rw [List.length_dropLast] at hi; omega
    have hget : (c.dropLast).get ⟨i, hi⟩ = c.get ⟨i, h2⟩ := by
      rw [List.get_eq_getElem, List.get_eq_getElem]
      exact List.getElem_dropLast hi
    rw [hget]
    exact hpos i h2 hev

/-- **Step 3, ⊆ direction, packaging**: the last element of a `loChain` element of length `≥ 2`
lies in `oddLt` below the last element of its `dropLast`. -/
lemma last_mem_oddLt_dropLast (y : ℝ) (M : ℕ) {c' : List ℕ} (hc' : c' ∈ loChain y 1 M)
    (hlen : 2 ≤ c'.length) :
    c'.getLast (by rintro rfl; simp at hlen) ∈ oddLt (((c'.dropLast).getLast?).getD 0) := by
  obtain ⟨hpw, hmem, hpos⟩ := (mem_loChain_iff' y M 1 c').mp hc'
  have hne : c' ≠ [] := by rintro rfl; simp at hlen
  have hcdne : c'.dropLast ≠ [] := by
    rw [List.ne_nil_iff_length_pos, List.length_dropLast]; omega
  have hsplit : c' = c'.dropLast ++ [c'.getLast hne] := (List.dropLast_append_getLast hne).symm
  have hbound : ((c'.dropLast).getLast?).getD 0 = (c'.dropLast).getLast hcdne := by
    rw [List.getLast?_eq_getLast hcdne]
    rfl
  rw [hbound]
  have hlt : c'.getLast hne < (c'.dropLast).getLast hcdne := by
    rw [hsplit, List.pairwise_append] at hpw
    exact hpw.2.2 _ (List.getLast_mem hcdne) _ (by simp)
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt,
    (Finset.mem_filter.mp (hmem _ (List.getLast_mem hne))).2⟩

/-- **Step 3, ⊆ direction, odd-`m` ingredient**: the LAST element of a `loChain` element sits at
index `c'.length - 1`, so if that position is even it obeys the cut-off. -/
lemma getLast_le_cut_of_even (y : ℝ) (M : ℕ) {c' : List ℕ} (hc' : c' ∈ loChain y 1 M)
    (hne : c' ≠ []) (hev : (1 + (c'.length - 1)) % 2 = 0) :
    ((c'.getLast hne : ℕ) : ℝ) ≤ cut y ((1 + (c'.length - 1)) / 2) := by
  have h1 : c'.length - 1 < c'.length := by rw [List.ne_nil_iff_length_pos] at hne; omega
  have h2 := (mem_loChain_iff' y M 1 c').mp hc' |>.2.2 (c'.length - 1) h1 hev
  have h3 : ((c'.getLast hne : ℕ) : ℝ) = ((c'.get ⟨c'.length - 1, h1⟩ : ℕ) : ℝ) := by
    rw [List.getLast_eq_getElem hne, List.get_eq_getElem]
  rw [h3]
  exact h2

/-- **Step 3, ⊆ direction assembly** (`loChain_extend`, corrected statement). -/
lemma loChain_extend_subset (y : ℝ) (M m : ℕ) (hm : 1 ≤ m) {c' : List ℕ}
    (hc' : c' ∈ (loChain y 1 M).filter (fun c => c.length = m+1)) :
    c' ∈ ((loChain y 1 M).filter (fun c => c.length = m)).biUnion (fun c =>
          (((oddLt ((c.getLast?).getD 0))).filter
            (fun p : ℕ => (m+1) % 2 = 1 ∨ (p:ℝ) ≤ cut y ((m+1)/2))).image (fun p => c ++ [p])) := by
  obtain ⟨hc'1, hc'len⟩ := Finset.mem_filter.mp hc'
  have hne : c' ≠ [] := by rintro rfl; simp at hc'len
  have hlen : 2 ≤ c'.length := by rw [hc'len]; omega
  refine Finset.mem_biUnion.mpr
    ⟨c'.dropLast, Finset.mem_filter.mpr ⟨loChain_dropLast y M hc'1, ?_⟩, ?_⟩
  · rw [List.length_dropLast]; omega
  · refine Finset.mem_image.mpr ⟨c'.getLast hne, ?_, (List.dropLast_append_getLast hne)⟩
    refine Finset.mem_filter.mpr ⟨last_mem_oddLt_dropLast y M hc'1 hlen, ?_⟩
    by_cases hev : (m+1) % 2 = 1
    · exact Or.inl hev
    · refine Or.inr ?_
      have hev2 : (1 + (c'.length - 1)) % 2 = 0 := by rw [hc'len]; omega
      have h := getLast_le_cut_of_even y M hc'1 hne hev2
      rw [hc'len, show (1 + (m + 1 - 1)) = m + 1 by omega] at h
      exact h

/-- appending an element below the last entry of a strictly decreasing nonempty list keeps it
strictly decreasing. -/
lemma pairwise_append_singleton {c : List ℕ} (hpw : c.Pairwise (·>·)) (hcdne : c ≠ [])
    {p : ℕ} (hplt : p < c.getLast hcdne) : (c ++ [p]).Pairwise (·>·) := by
  have hlast : c.getLast hcdne
      = c.get ⟨c.length - 1, by rw [List.ne_nil_iff_length_pos] at hcdne; omega⟩ := by
    rw [List.getLast_eq_getElem, List.get_eq_getElem]
  rw [List.pairwise_append]
  refine ⟨hpw, by simp, ?_⟩
  intro a ha b hb
  simp at hb
  subst hb
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ha
  have hle : c.get ⟨c.length - 1, by rw [List.ne_nil_iff_length_pos] at hcdne; omega⟩ ≤ c.get i := by
    by_cases hic : (i : ℕ) = c.length - 1
    · rw [show i = (⟨c.length - 1, by rw [List.ne_nil_iff_length_pos] at hcdne; omega⟩ : Fin c.length)
          from Fin.ext hic]
    · have hlt : i < (⟨c.length - 1, by rw [List.ne_nil_iff_length_pos] at hcdne; omega⟩ : Fin c.length) := by
        simp only [Fin.lt_def]; omega
      exact le_of_lt (List.pairwise_iff_get.mp hpw i _ hlt)
  rw [hlast] at hplt
  omega


/-- **Step 3, ⊇ direction assembly** (`loChain_extend`, corrected statement). -/
lemma loChain_extend_supset (y : ℝ) (M m : ℕ) (hm : 1 ≤ m) {c' : List ℕ}
    (hc' : c' ∈ ((loChain y 1 M).filter (fun c => c.length = m)).biUnion (fun c =>
          (((oddLt ((c.getLast?).getD 0))).filter
            (fun p : ℕ => (m+1) % 2 = 1 ∨ (p:ℝ) ≤ cut y ((m+1)/2))).image (fun p => c ++ [p]))) :
    c' ∈ (loChain y 1 M).filter (fun c => c.length = m+1) := by
  rcases Finset.mem_biUnion.mp hc' with ⟨c, hc, hc'⟩
  rcases Finset.mem_image.mp hc' with ⟨p, hp, rfl⟩
  rcases Finset.mem_filter.mp hc with ⟨hc1, hclen⟩
  rcases Finset.mem_filter.mp hp with ⟨hpodd, hpcond⟩
  obtain ⟨hpw, hmem, hpos⟩ := (mem_loChain_iff' y M 1 c).mp hc1
  have hcne : c ≠ [] := by rintro rfl; simp at hclen; omega
  have hlast : (c.getLast?).getD 0 = c.getLast hcne := by
    rw [List.getLast?_eq_some_getLast hcne]
    rfl
  have hplt : p < c.getLast hcne := by
    have h := Finset.mem_range.mp (Finset.mem_filter.mp hpodd).1
    rwa [hlast] at h
  have hpoddM : p ∈ oddLt M := by
    have hcl : c.getLast hcne ∈ oddLt M := hmem _ (List.getLast_mem hcne)
    have hlt : p < M :=
      lt_of_lt_of_le hplt (le_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp hcl).1))
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, (Finset.mem_filter.mp hpodd).2⟩
  refine Finset.mem_filter.mpr ⟨?_, ?_⟩
  · refine (mem_loChain_iff' y M 1 (c ++ [p])).mpr ⟨?_, ?_, ?_⟩
    · exact pairwise_append_singleton hpw hcne hplt
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hmem x hx
      · rw [List.mem_singleton] at hx; exact hx ▸ hpoddM
    · intro i hi hev
      have hi1 : i < c.length + 1 := by
        rw [List.length_append, List.length_singleton] at hi; exact hi
      rcases lt_or_eq_of_le (show i ≤ c.length by omega) with hlt | heq
      · have hget : (c ++ [p]).get ⟨i, hi⟩ = c.get ⟨i, hlt⟩ := by
          rw [List.get_eq_getElem, List.get_eq_getElem]
          exact List.getElem_append_left hlt
        rw [hget]
        exact hpos i hlt hev
      · have hget : (c ++ [p]).get ⟨i, hi⟩ = p := by
          have hle : c.length ≤ i := by omega
          rw [List.get_eq_getElem, List.getElem_append_right hle]
          simp [show i - c.length = 0 by omega]
        rw [hget]
        have hcalc : (1 + i) / 2 = (m + 1) / 2 := by omega
        rw [hcalc]
        rcases hpcond with h1 | h2
        · omega
        · exact h2
  · rw [List.length_append, List.length_singleton, hclen]
/-- **Step 3, final form**: the chains of length `m+1` are obtained from the chains of length `m` by
appending one element `p` of `oddLt (last c)`, subject to the even-position cut-off. -/
lemma loChain_extend (y : ℝ) (M m : ℕ) (hm : 1 ≤ m) :
    (loChain y 1 M).filter (fun c => c.length = m+1) =
      ((loChain y 1 M).filter (fun c => c.length = m)).biUnion (fun c =>
          (((oddLt ((c.getLast?).getD 0))).filter
            (fun p : ℕ => (m+1) % 2 = 1 ∨ (p:ℝ) ≤ cut y ((m+1)/2))).image (fun p => c ++ [p])) :=
  Finset.Subset.antisymm
    (fun c' hc' => loChain_extend_subset y M m hm hc')
    (fun c' hc' => loChain_extend_supset y M m hm hc')

/-- **Sum form of the extension step.** -/
lemma sum_loChain_extend (y : ℝ) (M m : ℕ) (hm : 1 ≤ m) (F : List ℕ → ℝ) :
    ((loChain y 1 M).filter (fun c => c.length = m+1)).sum F =
      ((loChain y 1 M).filter (fun c => c.length = m)).sum
        (fun c => (((oddLt ((c.getLast?).getD 0))).filter
            (fun p : ℕ => (m+1) % 2 = 1 ∨ (p:ℝ) ≤ cut y ((m+1)/2))).sum
          (fun p => F (c ++ [p]))) := by
  rw [loChain_extend y M m hm]
  rw [Finset.sum_biUnion]
  swap
  · intro c _ c' _ hne
    refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
    rcases Finset.mem_image.mp hx with ⟨p, _, hp⟩
    rcases Finset.mem_image.mp hx' with ⟨p', _, hp'⟩
    refine hne ?_
    have h2 : (c ++ [p]).dropLast = (c' ++ [p']).dropLast := by rw [hp, hp']
    simpa [List.dropLast_append] using h2
  · refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.sum_image]
    intro a _ b _ h
    simpa using List.append_cancel_left h


/-! ### Totient factorisation of chain products -/

/-- For a strictly decreasing list of odd primes, `φ(∏c) = ∏(p−1)`. -/
lemma totient_prod_eq (M : ℕ) : ∀ c : List ℕ, c.Pairwise (·>·) → (∀ x ∈ c, x ∈ oddLt M) →
    (Nat.totient c.prod : ℝ) = (c.map (fun x : ℕ => (x:ℝ)-1)).prod := by
  intro c
  induction c with
  | nil => intro _ _; simp
  | cons p t ih =>
    intro hpw hmem
    have hmemt : ∀ x ∈ t, x ∈ oddLt M := fun x hx => hmem x (by simp [hx])
    have hpt : t.Pairwise (·>·) := (List.pairwise_cons.mp hpw).2
    have hplt : ∀ x ∈ t, x < p := fun x hx => (List.pairwise_cons.mp hpw).1 x hx
    have hpprime : p.Prime := (Finset.mem_filter.mp (hmem p (by simp))).2.1
    have hcop : p.Coprime t.prod :=
      hpprime.coprime_iff_not_dvd.mpr (fun hd => prime_not_dvd_prod_lt hpprime t
        (fun x hx => ⟨(Finset.mem_filter.mp (hmemt x hx)).2.1, hplt x hx⟩) hd)
    rw [List.prod_cons, List.map_cons, List.prod_cons, Nat.totient_mul hcop, Nat.cast_mul,
      Nat.totient_prime hpprime, Nat.cast_sub (R := ℝ) hpprime.one_le, Nat.cast_one,
      ih hpt hmemt]

lemma getLast?_getD_eq {c : List ℕ} (h : c ≠ []) : (c.getLast?).getD 0 = c.getLast h := by
  rw [List.getLast?_eq_some_getLast h]
  rfl

lemma getLast?_append_singleton (c : List ℕ) (p : ℕ) : (c ++ [p]).getLast? = some p := by simp

/-- `φ(∏(c ++ [p])) = φ(∏c)·(p−1)` for a chain `c` and `p` a prime below its last entry. -/
lemma totient_prod_append_raw (M : ℕ) {c : List ℕ} (hpw : c.Pairwise (·>·)) (hcne : c ≠ [])
    (hmem : ∀ x ∈ c, x ∈ oddLt M) {p : ℕ} (hplt : p < c.getLast hcne) (hp : p ∈ oddLt M) :
    (Nat.totient (c ++ [p]).prod : ℝ) = (Nat.totient c.prod : ℝ) * ((p:ℝ) - 1) := by
  have hpw' : (c ++ [p]).Pairwise (·>·) := pairwise_append_singleton hpw hcne hplt
  have hmem' : ∀ x ∈ c ++ [p], x ∈ oddLt M := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hmem x hx
    · rw [List.mem_singleton] at hx; exact hx ▸ hp
  rw [totient_prod_eq M (c ++ [p]) hpw' hmem', totient_prod_eq M c hpw hmem,
    List.map_append, List.map_singleton, List.prod_append, List.prod_singleton]

/-- `φ(∏(c ++ [p])) = φ(∏c)·(p−1)` for `c` a chain and `p ∈ oddLt (last c)`. -/
lemma totient_prod_append (y : ℝ) (M : ℕ) {c : List ℕ} (hc : c ∈ loChain y 1 M)
    {p : ℕ} (hp : p ∈ oddLt ((c.getLast?).getD 0)) :
    (Nat.totient (c ++ [p]).prod : ℝ) = (Nat.totient c.prod : ℝ) * ((p:ℝ) - 1) := by
  have hcne : c ≠ [] := by rintro rfl; simp [oddLt] at hp
  have hpw : c.Pairwise (·>·) := loChain_pairwise y M 1 c hc
  have hmem : ∀ x ∈ c, x ∈ oddLt M := loChain_elems_mem y M 1 c hc
  have hplt : p < c.getLast hcne := by
    have h := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
    rwa [getLast?_getD_eq hcne] at h
  have hcl : c.getLast hcne ∈ oddLt M := hmem _ (List.getLast_mem hcne)
  have hpM : p ∈ oddLt M :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (lt_of_lt_of_le hplt (le_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp hcl).1))),
      (Finset.mem_filter.mp hp).2⟩
  exact totient_prod_append_raw M hpw hcne hmem hplt hpM

/-- The set of `q` below an extended chain `c ++ [p]` is `oddLt p` (for `p` a prime below `c`). -/
lemma filter_oddLt_vio (y : ℝ) (M p j : ℕ) {c : List ℕ} (hc : c ∈ loChain y 1 M)
    (hp : p ∈ oddLt ((c.getLast?).getD 0)) :
    (oddLt M).filter (fun q : ℕ => cut y j < (q:ℝ) ∧ ∀ x ∈ c ++ [p], q < x)
      = (oddLt p).filter (fun q : ℕ => cut y j < (q:ℝ)) := by
  have hcne : c ≠ [] := by rintro rfl; simp [oddLt] at hp
  have hpw : c.Pairwise (·>·) := loChain_pairwise y M 1 c hc
  have hplt : p < c.getLast hcne := by
    have h := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
    rwa [getLast?_getD_eq hcne] at h
  have hac : ∀ x ∈ c, p < x := fun x hx =>
    (List.pairwise_append.mp (pairwise_append_singleton hpw hcne hplt)).2.2 x hx p (by simp)
  have hcl : c.getLast hcne ∈ oddLt M := loChain_elems_mem y M 1 c hc _ (List.getLast_mem hcne)
  have hpM : p < M := lt_of_lt_of_le hplt (le_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp hcl).1))
  ext q
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hq, hcq, hqx⟩
    have hqp : q < p := hqx p (by rw [List.mem_append]; exact Or.inr (List.mem_singleton_self p))
    exact ⟨mem_oddLt_of hq hqp, hcq⟩
  · rintro ⟨hqp, hcq⟩
    have hqM : q ∈ oddLt M := oddLt_mono (le_of_lt hpM) hqp
    have hqltp : q < p := Finset.mem_range.mp (Finset.mem_filter.mp hqp).1
    refine ⟨hqM, hcq, ?_⟩
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact lt_of_lt_of_le hqltp (le_of_lt (hac x hx))
    · rw [List.mem_singleton] at hx; exact hx ▸ hqltp

/-! ### Extension-step sum identities -/

/-- Extending chains of length `2k` to `2k+1` (odd step: no cut-off). -/
lemma sum_loChain_extend_even (y : ℝ) (M k : ℕ) (hk : 1 ≤ k) (F : List ℕ → ℝ) :
    ((loChain y 1 M).filter (fun c => c.length = 2*k+1)).sum F =
      ((loChain y 1 M).filter (fun c => c.length = 2*k)).sum
        (fun c => (oddLt ((c.getLast?).getD 0)).sum (fun p => F (c ++ [p]))) := by
  have hm : 1 ≤ 2*k := by omega
  rw [sum_loChain_extend y M (2*k) hm F]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  have hfil : (oddLt ((c.getLast?).getD 0)).filter
        (fun p : ℕ => (2*k+1) % 2 = 1 ∨ (p:ℝ) ≤ cut y ((2*k+1)/2))
      = oddLt ((c.getLast?).getD 0) := by
    ext p
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.1, fun h => ⟨h, Or.inl (by omega)⟩⟩
  rw [hfil]

/-- Extending chains of length `2k+1` to `2k+2` (even step: cut-off `cut y (k+1)`). -/
lemma sum_loChain_extend_odd (y : ℝ) (M k : ℕ) (F : List ℕ → ℝ) :
    ((loChain y 1 M).filter (fun c => c.length = 2*(k+1))).sum F =
      ((loChain y 1 M).filter (fun c => c.length = 2*k+1)).sum
        (fun c => ((oddLt ((c.getLast?).getD 0)).filter
            (fun p : ℕ => (p:ℝ) ≤ cut y (k+1))).sum (fun p => F (c ++ [p]))) := by
  have hm : 1 ≤ 2*k+1 := by omega
  rw [show 2*(k+1) = 2*k+1+1 by omega]
  rw [sum_loChain_extend y M (2*k+1) hm F]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  have hfil : (oddLt ((c.getLast?).getD 0)).filter
        (fun p : ℕ => (2*k+1+1) % 2 = 1 ∨ (p:ℝ) ≤ cut y ((2*k+1+1)/2))
      = (oddLt ((c.getLast?).getD 0)).filter (fun p : ℕ => (p:ℝ) ≤ cut y (k+1)) := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨h, hc⟩
      refine ⟨h, ?_⟩
      rcases hc with h1 | h2
      · omega
      · rwa [show (2*k+1+1)/2 = k+1 by omega] at h2
    · rintro ⟨h, hc⟩
      exact ⟨h, Or.inr (by rwa [show (2*k+1+1)/2 = k+1 by omega])⟩
  rw [hfil]

/-- `φ(∏(c ++ [p] ++ [q])) = φ(∏c)·(p−1)·(q−1)` for two successive chain extensions. -/
lemma totient_prod_append2 (y : ℝ) (M : ℕ) {c : List ℕ} (hc : c ∈ loChain y 1 M)
    {p q : ℕ} (hp : p ∈ oddLt ((c.getLast?).getD 0)) (hq : q ∈ oddLt p) :
    (Nat.totient (c ++ [p] ++ [q]).prod : ℝ)
      = (Nat.totient c.prod : ℝ) * ((p:ℝ) - 1) * ((q:ℝ) - 1) := by
  have hcne : c ≠ [] := by rintro rfl; simp [oddLt] at hp
  have hpw : c.Pairwise (·>·) := loChain_pairwise y M 1 c hc
  have hmem : ∀ x ∈ c, x ∈ oddLt M := loChain_elems_mem y M 1 c hc
  have hplt : p < c.getLast hcne := by
    have h := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
    rwa [getLast?_getD_eq hcne] at h
  have hcl : c.getLast hcne ∈ oddLt M := hmem _ (List.getLast_mem hcne)
  have hpM : p ∈ oddLt M :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (lt_of_lt_of_le hplt (le_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp hcl).1))),
      (Finset.mem_filter.mp hp).2⟩
  have h1 : (Nat.totient (c ++ [p]).prod : ℝ) = (Nat.totient c.prod : ℝ) * ((p:ℝ) - 1) :=
    totient_prod_append_raw M hpw hcne hmem hplt hpM
  have hpw' : (c ++ [p]).Pairwise (·>·) := pairwise_append_singleton hpw hcne hplt
  have hne' : (c ++ [p]) ≠ [] := by simp
  have hmem' : ∀ x ∈ c ++ [p], x ∈ oddLt M := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hmem x hx
    · rw [List.mem_singleton] at hx; exact hx ▸ hpM
  have hlast' : (c ++ [p]).getLast hne' = p := by simp
  have hqlt : q < (c ++ [p]).getLast hne' := by
    rw [hlast']; exact Finset.mem_range.mp (Finset.mem_filter.mp hq).1
  have hpMle : p ≤ M := le_of_lt (lt_of_lt_of_le hplt
    (le_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp hcl).1)))
  have hqM : q ∈ oddLt M := oddLt_mono hpMle hq
  have h2 : (Nat.totient ((c ++ [p]) ++ [q]).prod : ℝ)
      = (Nat.totient (c ++ [p]).prod : ℝ) * ((q:ℝ) - 1) :=
    totient_prod_append_raw M hpw' hne' hmem' hqlt hqM
  rw [h2, h1]

/-- **Recurrence (2), first half.**  `V2T y (k+1) M` expressed on chains of length `2k`. -/
lemma V2T_step (y : ℝ) (k M : ℕ) (hk : 1 ≤ k) :
    V2T y (k+1) M = ((loChain y 1 M).filter (fun c => c.length = 2*k)).sum (fun c =>
      (1 / (Nat.totient c.prod : ℝ)) *
        ∑ p ∈ oddLt ((c.getLast?).getD 0), ((p:ℝ)-1)⁻¹ *
          ∑ q ∈ (oddLt p).filter (fun q : ℕ => cut y (k+1) < (q:ℝ)),
            ((q:ℝ)-1)⁻¹ * VsieveOdd q) := by
  have h1 : 2*(k+1) - 1 = 2*k+1 := by omega
  unfold V2T
  rw [h1]
  rw [sum_loChain_extend_even y M k hk]
  refine Finset.sum_congr rfl (fun c hc => ?_)
  have hc1 : c ∈ loChain y 1 M := (Finset.mem_filter.mp hc).1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [totient_prod_append y M hc1 hp, filter_oddLt_vio y M p (k+1) hc1 hp]
  simp only [one_div, mul_inv]
  ring

/-- **Recurrence (2), second half.**  `PB y (k+1) M` expressed on chains of length `2k`. -/
lemma PB_step (y : ℝ) (k M : ℕ) (hk : 1 ≤ k) :
    PB y (k+1) M = ((loChain y 1 M).filter (fun c => c.length = 2*k)).sum (fun c =>
      (1 / (Nat.totient c.prod : ℝ)) *
        ∑ p ∈ oddLt ((c.getLast?).getD 0), ((p:ℝ)-1)⁻¹ *
          ∑ q ∈ (oddLt p).filter (fun q : ℕ => (q:ℝ) ≤ cut y (k+1)),
            ((q:ℝ)-1)⁻¹ * Bnd y (2*k+3) q) := by
  have h3 : 2*(k+1)+1 = 2*k+3 := by omega
  unfold PB
  rw [sum_loChain_extend_odd y M k]
  rw [h3]
  rw [sum_loChain_extend_even y M k hk]
  refine Finset.sum_congr rfl (fun c hc => ?_)
  have hc1 : c ∈ loChain y 1 M := (Finset.mem_filter.mp hc).1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [← mul_assoc, Finset.mul_sum]
  have hlastp : ((c ++ [p]).getLast?).getD 0 = p := by
    rw [getLast?_append_singleton]; rfl
  rw [hlastp]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  have hqp : q ∈ oddLt p := (Finset.mem_filter.mp hq).1
  rw [totient_prod_append2 y M hc1 hp hqp, getLast?_append_singleton]
  simp only [Option.getD_some, one_div, mul_inv]
  ring

/-- **Recurrence (2)**: `PB y k M = V2T y (k+1) M + PB y (k+1) M`. -/
lemma PB_rec (y : ℝ) (k M : ℕ) (hk : 1 ≤ k) :
    PB y k M = V2T y (k+1) M + PB y (k+1) M := by
  rw [PB_expand y k M, V2T_step y k M hk, PB_step y k M hk]
  have hB : ∀ p : ℕ, Bnd y (2*k+2) p =
      (∑ q ∈ (oddLt p).filter (fun q : ℕ => cut y (k+1) < (q:ℝ)), ((q:ℝ)-1)⁻¹ * VsieveOdd q)
      + ∑ q ∈ (oddLt p).filter (fun q : ℕ => (q:ℝ) ≤ cut y (k+1)),
          ((q:ℝ)-1)⁻¹ * Bnd y (2*k+3) q := by
    intro p
    rw [Bnd_even y (2*k+2) p (by omega)]
    rw [show (2*k+2+1)/2 = k+1 by omega, show (2*k+2+1) = 2*k+3 by omega]
    rw [← Finset.sum_filter, ← Finset.sum_filter]
  have hpoint : ∀ c : List ℕ,
      (∑ p ∈ oddLt ((c.getLast?).getD 0), ((p:ℝ)-1)⁻¹ * Bnd y (2*k+2) p)
      = (∑ p ∈ oddLt ((c.getLast?).getD 0), ((p:ℝ)-1)⁻¹ *
            ∑ q ∈ (oddLt p).filter (fun q : ℕ => cut y (k+1) < (q:ℝ)),
              ((q:ℝ)-1)⁻¹ * VsieveOdd q)
        + ∑ p ∈ oddLt ((c.getLast?).getD 0), ((p:ℝ)-1)⁻¹ *
            ∑ q ∈ (oddLt p).filter (fun q : ℕ => (q:ℝ) ≤ cut y (k+1)),
              ((q:ℝ)-1)⁻¹ * Bnd y (2*k+3) q := by
    intro c
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [hB p, mul_add]
  calc (∑ c ∈ (loChain y 1 M).filter (fun c => c.length = 2*k),
          (1 / (Nat.totient c.prod : ℝ)) *
            ∑ p ∈ oddLt ((c.getLast?).getD 0), ((p:ℝ)-1)⁻¹ * Bnd y (2*k+2) p)
      = ∑ c ∈ (loChain y 1 M).filter (fun c => c.length = 2*k),
          ((1 / (Nat.totient c.prod : ℝ)) *
            ∑ p ∈ oddLt ((c.getLast?).getD 0), ((p:ℝ)-1)⁻¹ *
              ∑ q ∈ (oddLt p).filter (fun q : ℕ => cut y (k+1) < (q:ℝ)),
                ((q:ℝ)-1)⁻¹ * VsieveOdd q
           + (1 / (Nat.totient c.prod : ℝ)) *
            ∑ p ∈ oddLt ((c.getLast?).getD 0), ((p:ℝ)-1)⁻¹ *
              ∑ q ∈ (oddLt p).filter (fun q : ℕ => (q:ℝ) ≤ cut y (k+1)),
                ((q:ℝ)-1)⁻¹ * Bnd y (2*k+3) q) :=
        Finset.sum_congr rfl (fun c _ => by rw [hpoint c, mul_add])
    _ = (∑ c ∈ (loChain y 1 M).filter (fun c => c.length = 2*k),
          (1 / (Nat.totient c.prod : ℝ)) *
            ∑ p ∈ oddLt ((c.getLast?).getD 0), ((p:ℝ)-1)⁻¹ *
              ∑ q ∈ (oddLt p).filter (fun q : ℕ => cut y (k+1) < (q:ℝ)),
                ((q:ℝ)-1)⁻¹ * VsieveOdd q)
        + ∑ c ∈ (loChain y 1 M).filter (fun c => c.length = 2*k),
          (1 / (Nat.totient c.prod : ℝ)) *
            ∑ p ∈ oddLt ((c.getLast?).getD 0), ((p:ℝ)-1)⁻¹ *
              ∑ q ∈ (oddLt p).filter (fun q : ℕ => (q:ℝ) ≤ cut y (k+1)),
                ((q:ℝ)-1)⁻¹ * Bnd y (2*k+3) q := Finset.sum_add_distrib

/-! ### Elementary-symmetric (powerset) bound -/

lemma add_mul_pow_le {T b : ℝ} (hT : 0 ≤ T) (hb : 0 ≤ b) (n : ℕ) :
    T ^ n + (n:ℝ) * b * T ^ (n-1) ≤ (T + b) ^ n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · rcases eq_or_lt_of_le hT with h0 | hpos
    · rw [← h0]
      rcases Nat.eq_or_lt_of_le hn with h1 | h2
      · subst h1; simp
      · have hz1 : (0:ℝ) ^ n = 0 := zero_pow (by omega)
        have hz2 : (0:ℝ) ^ (n-1) = 0 := zero_pow (by omega)
        rw [hz1, hz2, mul_zero, add_zero]
        simpa using pow_nonneg hb n
    · have hne : T ≠ 0 := ne_of_gt hpos
      have hbt : 0 ≤ b/T := div_nonneg hb (le_of_lt hpos)
      have hle := one_add_mul_le_pow (a := b/T) (by linarith) n
      have h1 : T ^ n * (1 + (n:ℝ) * (b/T)) = T ^ n + (n:ℝ) * b * T ^ (n-1) := by
        have hTp : T ^ n = T ^ (n-1) * T := by
          conv_lhs => rw [show n = (n-1)+1 by omega, pow_succ]
        rw [hTp]
        field_simp
      have h2 : T ^ n * (1 + b/T) ^ n = (T + b) ^ n := by
        rw [← mul_pow]
        congr 1
        field_simp
      have hm := mul_le_mul_of_nonneg_left hle (pow_nonneg (le_of_lt hpos) n)
      rw [h1, h2] at hm
      exact hm

lemma factorial_mul_sum_powersetCard_prod_le_pow :
    ∀ (s : Finset ℕ) (g : ℕ → ℝ) (n : ℕ), (∀ x ∈ s, 0 ≤ g x) →
      (n.factorial : ℝ) * (s.powersetCard n).sum (fun t => ∏ x ∈ t, g x) ≤ (s.sum g) ^ n := by
  intro s
  induction s using Finset.induction with
  | empty =>
    intro g n hg
    rcases n with _ | n
    · simp
    · rw [Finset.powersetCard_eq_empty.mpr (by simp), Finset.sum_empty, mul_zero]
      simp
  | insert a s ha ih =>
    intro g n hg
    have hga : 0 ≤ g a := hg a (Finset.mem_insert_self a s)
    have hgs : ∀ x ∈ s, 0 ≤ g x := fun x hx => hg x (Finset.mem_insert_of_mem hx)
    have hT : 0 ≤ s.sum g := Finset.sum_nonneg hgs
    rcases n with _ | m
    · simp
    · have hsplit := Finset.powersetCard_succ_insert (α := ℕ) ha m
      have hdisj : Disjoint (s.powersetCard (m+1)) ((s.powersetCard m).image (insert a)) := by
        refine Finset.disjoint_left.mpr (fun t ht ht' => ?_)
        rw [Finset.mem_powersetCard] at ht
        rcases Finset.mem_image.mp ht' with ⟨u, _, rfl⟩
        exact ha (ht.1 (Finset.mem_insert_self a u))
      have hinj : Set.InjOn (insert a) ((s.powersetCard m : Finset (Finset ℕ)) : Set (Finset ℕ)) := by
        intro u hu v hv huv
        have hau : a ∉ u := fun h => ha ((Finset.mem_powersetCard.mp hu).1 h)
        have hav : a ∉ v := fun h => ha ((Finset.mem_powersetCard.mp hv).1 h)
        have h := congrArg (Finset.erase · a) huv
        simpa [Finset.erase_insert hau, Finset.erase_insert hav] using h
      have hsum : ((insert a s).powersetCard (m+1)).sum (fun t => ∏ x ∈ t, g x)
          = (s.powersetCard (m+1)).sum (fun t => ∏ x ∈ t, g x)
            + g a * (s.powersetCard m).sum (fun t => ∏ x ∈ t, g x) := by
        rw [hsplit, Finset.sum_union hdisj, Finset.sum_image hinj]
        congr 1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun u hu => ?_)
        have hau : a ∉ u := fun h => ha ((Finset.mem_powersetCard.mp hu).1 h)
        rw [Finset.prod_insert hau, mul_comm]
      rw [hsum]
      have hIH1 : ((m+1).factorial : ℝ) * (s.powersetCard (m+1)).sum (fun t => ∏ x ∈ t, g x)
          ≤ (s.sum g) ^ (m+1) := ih g (m+1) hgs
      have hIH2 : (m.factorial : ℝ) * (s.powersetCard m).sum (fun t => ∏ x ∈ t, g x)
          ≤ (s.sum g) ^ m := ih g m hgs
      have hfac : ((m+1).factorial : ℝ) = ((m+1 : ℕ) : ℝ) * (m.factorial : ℝ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      have hgoal : ((m+1).factorial : ℝ)
            * ((s.powersetCard (m+1)).sum (fun t => ∏ x ∈ t, g x)
               + g a * (s.powersetCard m).sum (fun t => ∏ x ∈ t, g x))
          = ((m+1).factorial : ℝ) * (s.powersetCard (m+1)).sum (fun t => ∏ x ∈ t, g x)
            + ((m+1 : ℕ) : ℝ) * g a
              * ((m.factorial : ℝ) * (s.powersetCard m).sum (fun t => ∏ x ∈ t, g x)) := by
        rw [hfac]; ring
      rw [hgoal]
      have hf2 : ((m+1 : ℕ) : ℝ) * g a
              * ((m.factorial : ℝ) * (s.powersetCard m).sum (fun t => ∏ x ∈ t, g x))
          ≤ ((m+1 : ℕ) : ℝ) * g a * (s.sum g) ^ m := by
        refine mul_le_mul_of_nonneg_left hIH2 ?_
        positivity
      have hfin := add_mul_pow_le hT hga (m+1)
      simp only [Nat.add_sub_cancel] at hfin
      have hins : (insert a s).sum g = s.sum g + g a := by rw [Finset.sum_insert ha]; ring
      rw [hins]
      linarith

/-! ### Chain length, vanishing of `PB`, telescoping -/

lemma loChain_length_le (y : ℝ) :
    ∀ M : ℕ, ∀ j (c : List ℕ), c ∈ loChain y j M → c.length ≤ M := by
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    intro j c hc
    rw [mem_loChain_iff] at hc
    rcases hc with rfl | ⟨p, tail, hpM, hcond, htail, rfl⟩
    · simp
    · have hpMlt : p < M := Finset.mem_range.mp (Finset.mem_filter.mp hpM).1
      have := ih p hpMlt (j+1) tail htail
      simp only [List.length_cons]
      omega

lemma PB_eq_zero (y : ℝ) (K M : ℕ) (h : M < 2*K) : PB y K M = 0 := by
  unfold PB
  have hempty : (loChain y 1 M).filter (fun c => c.length = 2*K) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro c hc hlen
    have := loChain_length_le y M 1 c hc
    omega
  rw [hempty, Finset.sum_empty]

lemma PB_telescope (y : ℝ) (M : ℕ) : ∀ K : ℕ,
    PB y 1 M = (Finset.range K).sum (fun i => V2T y (i+2) M) + PB y (K+1) M := by
  intro K
  induction K with
  | zero => simp
  | succ K ih =>
    rw [ih, Finset.sum_range_succ, PB_rec y (K+1) M (by omega)]
    ring

lemma Bnd_eq_V2T_sum (y : ℝ) (M : ℕ) : ∀ J : ℕ,
    Bnd y 1 M = (Finset.range (J+1)).sum (fun j => V2T y (j+1) M) + PB y (J+1) M := by
  intro J
  induction J with
  | zero => rw [Bnd_one_eq]; simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ih, PB_rec y (J+1) M (by omega)]
    ring

/-! ### Monotonicity of the odd sieve product -/

lemma oneSubInvPred_mem_Icc {p : ℕ} (hp : 3 ≤ p) :
    0 ≤ (1:ℝ) - 1/((p:ℝ)-1) ∧ (1:ℝ) - 1/((p:ℝ)-1) ≤ 1 := by
  have hpR : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
  have hne : (p:ℝ) - 1 ≠ 0 := by linarith
  have heq : (1:ℝ) - 1/((p:ℝ)-1) = ((p:ℝ)-2)/((p:ℝ)-1) := by field_simp; ring
  rw [heq]
  constructor
  · exact div_nonneg (by linarith) (by linarith)
  · rw [div_le_one (by linarith)]
    linarith

lemma VsieveOdd_mono {M M' : ℕ} (h : M ≤ M') : VsieveOdd M' ≤ VsieveOdd M := by
  unfold VsieveOdd
  rw [← Finset.prod_sdiff (f := fun p : ℕ => (1:ℝ) - 1/((p:ℝ)-1)) (oddLt_mono h)]
  have h1 : ∏ p ∈ oddLt M' \ oddLt M, ((1:ℝ) - 1/((p:ℝ)-1)) ≤ 1 := by
    refine Finset.prod_le_one₀ (fun p hp => ?_) (fun p hp => ?_)
    · exact (oneSubInvPred_mem_Icc (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).2.2).1
    · exact (oneSubInvPred_mem_Icc (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).2.2).2
  exact mul_le_of_le_one_left (VsieveOdd_nonneg M) h1

lemma VsieveOdd_primesLE (n : ℕ) :
    VsieveOdd (n+1) = ∏ p ∈ (Nat.primesLE n).filter (fun p => p ≠ 2),
      ((1:ℝ) - 1/((p:ℝ)-1)) := by
  unfold VsieveOdd oddLt
  rw [Nat.primesLE_eq_filter_range]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hpn, hpr, h3⟩
    exact ⟨⟨hpn, hpr⟩, by omega⟩
  · rintro ⟨⟨hpn, hpr⟩, hne2⟩
    exact ⟨hpn, hpr, by have := hpr.two_le; omega⟩

/-! ### The first-violation chains and the `V2T` bound -/

/-- the first-violation chains of length `2j` as a `Finset` of lists. -/
noncomputable def Vset (y : ℝ) (j M : ℕ) : Finset (List ℕ) :=
  ((loChain y 1 M).filter (fun c => c.length = 2*j-1)).biUnion (fun c =>
    (((oddLt M).filter (fun q : ℕ => cut y j < (q:ℝ) ∧ ∀ x ∈ c, q < x)).image
      (fun q => c ++ [q])))

lemma sum_Vset (y : ℝ) (j M : ℕ) (F : List ℕ → ℝ) :
    (Vset y j M).sum F =
      ∑ c ∈ (loChain y 1 M).filter (fun c => c.length = 2*j-1),
        ∑ q ∈ (oddLt M).filter (fun q : ℕ => cut y j < (q:ℝ) ∧ ∀ x ∈ c, q < x),
          F (c ++ [q]) := by
  unfold Vset
  rw [Finset.sum_biUnion]
  swap
  · intro c _ c' _ hne
    refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
    rcases Finset.mem_image.mp hx with ⟨q, _, hqx⟩
    rcases Finset.mem_image.mp hx' with ⟨q', _, hqx'⟩
    refine hne ?_
    have h2 : (c ++ [q]).dropLast = (c' ++ [q']).dropLast := by rw [hqx, hqx']
    simpa [List.dropLast_append] using h2
  · refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.sum_image]
    intro a _ b _ h
    simpa using List.append_cancel_left h

lemma V2T_le_Vset (y : ℝ) (hy : 1 ≤ y) (j M : ℕ) :
    V2T y j M ≤ VsieveOdd (⌊cut y j⌋₊ + 1) *
      (Vset y j M).sum (fun l => ∏ x ∈ l.toFinset, ((x:ℝ)-1)⁻¹) := by
  have hcy : (0:ℝ) ≤ cut y j := Real.rpow_nonneg (by linarith) _
  have key : ∀ c ∈ (loChain y 1 M).filter (fun c => c.length = 2*j-1),
      ∀ q ∈ (oddLt M).filter (fun q : ℕ => cut y j < (q:ℝ) ∧ ∀ x ∈ c, q < x),
      (1 / (Nat.totient c.prod : ℝ)) * (((q:ℝ)-1)⁻¹ * VsieveOdd q)
        ≤ VsieveOdd (⌊cut y j⌋₊ + 1) * ∏ x ∈ (c ++ [q]).toFinset, ((x:ℝ)-1)⁻¹ := by
    intro c hc q hq
    rcases Finset.mem_filter.mp hc with ⟨hc1, hclen⟩
    rcases Finset.mem_filter.mp hq with ⟨hqodd, hqcut, hqlt⟩
    have hqprime : q.Prime := (Finset.mem_filter.mp hqodd).2.1
    have hqge : ⌊cut y j⌋₊ + 1 ≤ q := by
      have h1 : ((⌊cut y j⌋₊ : ℕ) : ℝ) ≤ cut y j := Nat.floor_le hcy
      have h2 : (⌊cut y j⌋₊ : ℝ) < (q:ℝ) := lt_of_le_of_lt h1 hqcut
      have h3 : ⌊cut y j⌋₊ < q := by exact_mod_cast h2
      omega
    have hV : VsieveOdd q ≤ VsieveOdd (⌊cut y j⌋₊ + 1) := VsieveOdd_mono hqge
    have hpw : c.Pairwise (·>·) := loChain_pairwise y M 1 c hc1
    have hmem : ∀ x ∈ c, x ∈ oddLt M := loChain_elems_mem y M 1 c hc1
    have htot : (Nat.totient c.prod : ℝ) = ∏ x ∈ c.toFinset, ((x:ℝ)-1) := by
      rw [List.prod_toFinset (fun x : ℕ => ((x:ℝ)-1)) hpw.nodup]
      exact totient_prod_eq M c hpw hmem
    have hφinv : (1 / (Nat.totient c.prod : ℝ)) = ∏ x ∈ c.toFinset, ((x:ℝ)-1)⁻¹ := by
      rw [htot, one_div, Finset.prod_inv_distrib]
    have hqnotin : q ∉ c.toFinset := by
      rw [List.mem_toFinset]
      intro hqc
      exact absurd (hqlt q hqc) (lt_irrefl q)
    have hsing : ([q] : List ℕ).toFinset = {q} := by simp
    have hprod : ∏ x ∈ (c ++ [q]).toFinset, ((x:ℝ)-1)⁻¹
        = (∏ x ∈ c.toFinset, ((x:ℝ)-1)⁻¹) * ((q:ℝ)-1)⁻¹ := by
      rw [List.toFinset_append, hsing, Finset.prod_union
        (Finset.disjoint_singleton_right.mpr hqnotin)]
      simp
    rw [hφinv, hprod]
    have hzn : 0 ≤ ∏ x ∈ c.toFinset, ((x:ℝ)-1)⁻¹ := by
      refine Finset.prod_nonneg (fun x hx => ?_)
      have hx3 : 3 ≤ x := (Finset.mem_filter.mp (hmem x (by rwa [List.mem_toFinset] at hx))).2.2
      have : (0:ℝ) < (x:ℝ) - 1 := by
        have : (3:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx3
        linarith
      exact inv_nonneg.mpr (le_of_lt this)
    have hqn : 0 ≤ ((q:ℝ)-1)⁻¹ := inv_pred_nonneg hqprime
    have hstep : ((q:ℝ)-1)⁻¹ * VsieveOdd q ≤ ((q:ℝ)-1)⁻¹ * VsieveOdd (⌊cut y j⌋₊ + 1) :=
      mul_le_mul_of_nonneg_left hV hqn
    calc (∏ x ∈ c.toFinset, ((x:ℝ)-1)⁻¹) * (((q:ℝ)-1)⁻¹ * VsieveOdd q)
        ≤ (∏ x ∈ c.toFinset, ((x:ℝ)-1)⁻¹)
            * (((q:ℝ)-1)⁻¹ * VsieveOdd (⌊cut y j⌋₊ + 1)) :=
          mul_le_mul_of_nonneg_left hstep hzn
      _ = VsieveOdd (⌊cut y j⌋₊ + 1)
            * ((∏ x ∈ c.toFinset, ((x:ℝ)-1)⁻¹) * ((q:ℝ)-1)⁻¹) := by ring
  rw [sum_Vset]
  rw [Finset.mul_sum]
  unfold V2T
  refine Finset.sum_le_sum (fun c hc => ?_)
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum (fun q hq => ?_)
  exact key c hc q hq

lemma Vset_mem_pairwise (y : ℝ) (j M : ℕ) {l : List ℕ} (hl : l ∈ Vset y j M) :
    l.Pairwise (·>·) := by
  unfold Vset at hl
  rcases Finset.mem_biUnion.mp hl with ⟨c, hc, hl⟩
  rcases Finset.mem_image.mp hl with ⟨q, hq, rfl⟩
  rcases Finset.mem_filter.mp hc with ⟨hc1, hclen⟩
  rcases Finset.mem_filter.mp hq with ⟨hqodd, hqcut, hqlt⟩
  by_cases hcne : c = []
  · subst hcne; simp
  · have hpw : c.Pairwise (·>·) := loChain_pairwise y M 1 c hc1
    have hplt : q < c.getLast hcne := by
      simpa using hqlt (c.getLast hcne) (List.getLast_mem hcne)
    exact pairwise_append_singleton hpw hcne hplt

lemma Vset_toFinset_inj (y : ℝ) (j M : ℕ) {l l' : List ℕ} (hl : l ∈ Vset y j M)
    (hl' : l' ∈ Vset y j M) (h : l.toFinset = l'.toFinset) : l = l' := by
  have h1 : l.Nodup := (Vset_mem_pairwise y j M hl).nodup
  have h2 : l'.Nodup := (Vset_mem_pairwise y j M hl').nodup
  exact (List.perm_of_nodup_nodup_toFinset_eq h1 h2 h).eq_of_pairwise'
    (Vset_mem_pairwise y j M hl) (Vset_mem_pairwise y j M hl')

lemma Vset_image_subset (y : ℝ) (j M : ℕ) (hj : 1 ≤ j) :
    (Vset y j M).image List.toFinset ⊆
      ((oddLt M).filter (fun p : ℕ => cut y j < (p:ℝ))).powersetCard (2*j) := by
  intro t ht
  rcases Finset.mem_image.mp ht with ⟨l, hl, rfl⟩
  unfold Vset at hl
  rcases Finset.mem_biUnion.mp hl with ⟨c, hc, hl⟩
  rcases Finset.mem_image.mp hl with ⟨q, hq, rfl⟩
  rcases Finset.mem_filter.mp hc with ⟨hc1, hclen⟩
  rcases Finset.mem_filter.mp hq with ⟨hqodd, hqcut, hqlt⟩
  obtain ⟨hpw, hmem, hpos⟩ := (mem_loChain_iff' y M 1 c).mp hc1
  rw [Finset.mem_powersetCard]
  have hqlt' : ∀ x ∈ c, q < x := hqlt
  constructor
  · intro x hx
    rw [List.mem_toFinset] at hx
    rcases List.mem_append.mp hx with hx | hx
    · refine Finset.mem_filter.mpr ⟨hmem x hx, ?_⟩
      have hqx : q < x := hqlt' x hx
      have h2 : (q:ℝ) < (x:ℝ) := by exact_mod_cast hqx
      linarith
    · rw [List.mem_singleton] at hx
      subst hx
      exact Finset.mem_filter.mpr ⟨hqodd, hqcut⟩
  · have hne : c ≠ [] := by rintro rfl; simp at hclen; omega
    have hpw2 : (c ++ [q]).Pairwise (·>·) := by
      have hplt : q < c.getLast hne := by
        simpa using hqlt' (c.getLast hne) (List.getLast_mem hne)
      exact pairwise_append_singleton hpw hne hplt
    rw [List.toFinset_card_of_nodup hpw2.nodup, List.length_append, List.length_singleton]
    omega

lemma V2T_bound (y : ℝ) (hy : 1 ≤ y) (j M : ℕ) (hj : 1 ≤ j) :
    V2T y j M ≤ VsieveOdd (⌊cut y j⌋₊ + 1) *
      (((∑ p ∈ (oddLt M).filter (fun p : ℕ => cut y j < (p:ℝ)), ((p:ℝ)-1)⁻¹))^(2*j)
        / ((2*j).factorial : ℝ)) := by
  have h1 := V2T_le_Vset y hy j M
  have h2a : (Vset y j M).sum (fun l => ∏ x ∈ l.toFinset, ((x:ℝ)-1)⁻¹)
      = ((Vset y j M).image List.toFinset).sum (fun t => ∏ x ∈ t, ((x:ℝ)-1)⁻¹) := by
    rw [Finset.sum_image]
    intro a ha b hb hab
    exact Vset_toFinset_inj y j M ha hb hab
  have h2 : ((Vset y j M).image List.toFinset).sum (fun t => ∏ x ∈ t, ((x:ℝ)-1)⁻¹)
      ≤ (((oddLt M).filter (fun p : ℕ => cut y j < (p:ℝ))).powersetCard (2*j)).sum
          (fun t => ∏ x ∈ t, ((x:ℝ)-1)⁻¹) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Vset_image_subset y j M hj) ?_
    intro t ht _
    refine Finset.prod_nonneg (fun x hx => ?_)
    have hxS : x ∈ (oddLt M).filter (fun p : ℕ => cut y j < (p:ℝ)) :=
      (Finset.mem_powersetCard.mp ht).1 hx
    have hx3 : 3 ≤ x := (Finset.mem_filter.mp (Finset.mem_filter.mp hxS).1).2.2
    have hx3' : (0:ℝ) < (x:ℝ) - 1 := by
      have : (3:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx3
      linarith
    exact inv_nonneg.mpr (le_of_lt hx3')
  have h3 : ((2*j).factorial : ℝ) *
      ((((oddLt M).filter (fun p : ℕ => cut y j < (p:ℝ))).powersetCard (2*j)).sum
          (fun t => ∏ x ∈ t, ((x:ℝ)-1)⁻¹))
      ≤ ((∑ p ∈ (oddLt M).filter (fun p : ℕ => cut y j < (p:ℝ)), ((p:ℝ)-1)⁻¹))^(2*j) := by
    exact factorial_mul_sum_powersetCard_prod_le_pow _ _ _ (fun x hx => by
      have hx3 : 3 ≤ x := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2.2
      have hx3' : (0:ℝ) < (x:ℝ) - 1 := by
        have : (3:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx3
        linarith
      exact inv_nonneg.mpr (le_of_lt hx3'))
  have h4 : (((oddLt M).filter (fun p : ℕ => cut y j < (p:ℝ))).powersetCard (2*j)).sum
          (fun t => ∏ x ∈ t, ((x:ℝ)-1)⁻¹)
      ≤ ((∑ p ∈ (oddLt M).filter (fun p : ℕ => cut y j < (p:ℝ)), ((p:ℝ)-1)⁻¹))^(2*j)
        / ((2*j).factorial : ℝ) := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < ((2*j).factorial : ℝ))]
    linarith [h3]
  have hCn : 0 ≤ VsieveOdd (⌊cut y j⌋₊ + 1) := VsieveOdd_nonneg _
  calc V2T y j M ≤ VsieveOdd (⌊cut y j⌋₊ + 1) * (Vset y j M).sum
        (fun l => ∏ x ∈ l.toFinset, ((x:ℝ)-1)⁻¹) := h1
    _ = VsieveOdd (⌊cut y j⌋₊ + 1) * ((Vset y j M).image List.toFinset).sum
        (fun t => ∏ x ∈ t, ((x:ℝ)-1)⁻¹) := by rw [h2a]
    _ ≤ VsieveOdd (⌊cut y j⌋₊ + 1) *
          ((((oddLt M).filter (fun p : ℕ => cut y j < (p:ℝ))).powersetCard (2*j)).sum
            (fun t => ∏ x ∈ t, ((x:ℝ)-1)⁻¹)) := mul_le_mul_of_nonneg_left h2 hCn
    _ ≤ VsieveOdd (⌊cut y j⌋₊ + 1) *
          (((∑ p ∈ (oddLt M).filter (fun p : ℕ => cut y j < (p:ℝ)), ((p:ℝ)-1)⁻¹))^(2*j)
            / ((2*j).factorial : ℝ)) := mul_le_mul_of_nonneg_left h4 hCn

/-! ### The odd sieve product at a real scale, and its Mertens asymptotics -/

/-- `∏_{3 ≤ p ≤ z} (1 - 1/(p-1))`, indexed by a real parameter. -/
noncomputable def Vodd (z : ℝ) : ℝ :=
  ∏ p ∈ (Nat.primesLE ⌊z⌋₊).filter (fun p : ℕ => p ≠ 2), (1 - 1/((p:ℝ)-1))

lemma VsieveOdd_eq_Vodd_pred (M : ℕ) (hM : 1 ≤ M) : VsieveOdd M = Vodd ((M:ℝ) - 1) := by
  have hcast : ((M:ℝ) - 1) = ((M - 1 : ℕ) : ℝ) := by rw [Nat.cast_sub hM, Nat.cast_one]
  rw [hcast, Vodd, Nat.floor_natCast]
  rw [show M = (M-1)+1 by omega]
  exact VsieveOdd_primesLE (M-1)

lemma VsieveOdd_eq_Vodd (z : ℝ) : VsieveOdd (⌊z⌋₊ + 1) = Vodd z := by
  rw [VsieveOdd_primesLE]; rfl

lemma oneSubInvPred_pos_of_ne_two {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    0 < (1:ℝ) - 1/((p:ℝ)-1) := by
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  have hpR : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast h3
  have hne : (p:ℝ) - 1 ≠ 0 := by linarith
  have heq : (1:ℝ) - 1/((p:ℝ)-1) = ((p:ℝ)-2)/((p:ℝ)-1) := by field_simp; ring
  rw [heq]; exact div_pos (by linarith) (by linarith)

lemma Vodd_pos (z : ℝ) : 0 < Vodd z :=
  Finset.prod_pos (fun p hp => oneSubInvPred_pos_of_ne_two
    (Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1) (Finset.mem_filter.mp hp).2)

lemma Vodd_nonneg (z : ℝ) : 0 ≤ Vodd z := le_of_lt (Vodd_pos z)

/-- the factors of `Vodd` are nonnegative and `≤ 1` -/
lemma Vodd_factor_bounds (z : ℝ) {p : ℕ} (hp : p ∈ (Nat.primesLE ⌊z⌋₊).filter (fun p : ℕ => p ≠ 2)) :
    0 ≤ (1:ℝ) - 1/((p:ℝ)-1) ∧ (1:ℝ) - 1/((p:ℝ)-1) ≤ 1 := by
  have hpr : p.Prime := Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1
  have hne2 : p ≠ 2 := (Finset.mem_filter.mp hp).2
  have h3 : 3 ≤ p := by have := hpr.two_le; omega
  exact oneSubInvPred_mem_Icc h3

lemma three_mem_Vodd_set {z : ℝ} (hz : 3 ≤ z) :
    (3:ℕ) ∈ (Nat.primesLE ⌊z⌋₊).filter (fun p : ℕ => p ≠ 2) := by
  rw [Finset.mem_filter, Nat.mem_primesLE]
  exact ⟨⟨Nat.le_floor (by exact_mod_cast hz), Nat.prime_three⟩, by norm_num⟩

lemma Vodd_le_half {z : ℝ} (hz : 3 ≤ z) : Vodd z ≤ 1/2 := by
  have hmem := three_mem_Vodd_set hz
  have hsub : ({(3:ℕ)} : Finset ℕ) ⊆ (Nat.primesLE ⌊z⌋₊).filter (fun p : ℕ => p ≠ 2) := by
    intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp; exact hmem
  have hprodsplit : ∏ p ∈ (Nat.primesLE ⌊z⌋₊).filter (fun p : ℕ => p ≠ 2),
        ((1:ℝ) - 1/((p:ℝ)-1))
      = (∏ p ∈ ((Nat.primesLE ⌊z⌋₊).filter (fun p : ℕ => p ≠ 2)) \ {(3:ℕ)},
          ((1:ℝ) - 1/((p:ℝ)-1))) * (1/2) := by
    rw [← Finset.prod_sdiff hsub (f := fun p : ℕ => ((1:ℝ) - 1/((p:ℝ)-1)))]
    congr 1
    rw [Finset.prod_singleton]
    norm_num
  rw [Vodd, hprodsplit]
  have hle1 : ∏ p ∈ ((Nat.primesLE ⌊z⌋₊).filter (fun p : ℕ => p ≠ 2)) \ {(3:ℕ)},
      ((1:ℝ) - 1/((p:ℝ)-1)) ≤ 1 := by
    refine Finset.prod_le_one₀ (fun p hp => ?_) (fun p hp => ?_)
    · exact (Vodd_factor_bounds z (Finset.mem_sdiff.mp hp).1).1
    · exact (Vodd_factor_bounds z (Finset.mem_sdiff.mp hp).1).2
  have hnn : 0 ≤ ∏ p ∈ ((Nat.primesLE ⌊z⌋₊).filter (fun p : ℕ => p ≠ 2)) \ {(3:ℕ)},
      ((1:ℝ) - 1/((p:ℝ)-1)) := by
    refine Finset.prod_nonneg (fun p hp => ?_)
    exact (Vodd_factor_bounds z (Finset.mem_sdiff.mp hp).1).1
  nlinarith [hle1, hnn]

lemma Vodd_limit : ∃ L : ℝ, 0 < L ∧
    Filter.Tendsto (fun z : ℝ => Real.log z * Vodd z) Filter.atTop (nhds L) := by
  obtain ⟨L, hL, h⟩ := Commons.NumberTheory.Mertens.primeProduct_oneSubInvPred_log_tendsto_pos
  exact ⟨L, hL, h⟩

lemma Vodd_eventually {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (h : Filter.Tendsto (fun z : ℝ => Real.log z * Vodd z) Filter.atTop (nhds L)) :
    ∃ Z : ℝ, 3 ≤ Z ∧ ∀ z : ℝ, Z ≤ z →
      (1-δ) * L ≤ Real.log z * Vodd z ∧ Real.log z * Vodd z ≤ (1+δ) * L := by
  have hev1 : ∀ᶠ z : ℝ in Filter.atTop, Real.log z * Vodd z < (1+δ) * L :=
    h.eventually_lt tendsto_const_nhds (by nlinarith)
  have hev2 : ∀ᶠ z : ℝ in Filter.atTop, (1-δ) * L < Real.log z * Vodd z :=
    tendsto_const_nhds.eventually_lt h (by nlinarith)
  obtain ⟨Z₁, hZ₁⟩ := Filter.eventually_atTop.mp (hev1.and hev2)
  refine ⟨max 3 Z₁, le_max_left _ _, fun z hz => ?_⟩
  have hz₁ : Z₁ ≤ z := le_trans (le_max_right _ _) hz
  exact ⟨le_of_lt (hZ₁ z hz₁).2, le_of_lt (hZ₁ z hz₁).1⟩

/-! ### The numeric series bound for the sieve deficit -/

lemma one_add_inv_pow_le (n : ℕ) (hn : 1 ≤ n) : (1 + 1/(n:ℝ))^(2*n) ≤ 739/100 := by
  have hn1 : (0:ℝ) < 1 + 1/(n:ℝ) := by positivity
  have hlog : Real.log (1 + 1/(n:ℝ)) ≤ 1/(n:ℝ) := by
    have h := Real.log_le_sub_one_of_pos hn1
    linarith
  have hpow : ((1 + 1/(n:ℝ))^(2*n)) ≤ Real.exp 2 := by
    have h2 : Real.log ((1 + 1/(n:ℝ))^(2*n)) ≤ 2 := by
      rw [Real.log_pow]
      have h3 : (0:ℝ) ≤ ((2*n : ℕ) : ℝ) := by positivity
      calc ((2*n : ℕ) : ℝ) * Real.log (1 + 1/(n:ℝ)) ≤ ((2*n : ℕ):ℝ) * (1/(n:ℝ)) :=
            mul_le_mul_of_nonneg_left hlog h3
        _ = 2 := by
            have hnne : (n:ℝ) ≠ 0 := by positivity
            push_cast
            field_simp
    calc ((1 + 1/(n:ℝ))^(2*n)) = Real.exp (Real.log ((1 + 1/(n:ℝ))^(2*n))) :=
          (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp 2 := Real.exp_le_exp.mpr h2
  have hexp2 : Real.exp 2 ≤ 739/100 := by
    rw [show (2:ℝ) = 1 + 1 by norm_num, Real.exp_add]
    have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have h1p : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
    nlinarith [h1, h1p]
  linarith

/-! ### The numeric series bound for the sieve deficit -/

/-- `term j := (1000/599)^j (13j/25)^{2j} / (2j)!`. -/
noncomputable def sterm (j : ℕ) : ℝ :=
  ((1000:ℝ)/599)^j * (((13:ℝ)/25)*((j:ℕ):ℝ))^(2*j) / (((2*j).factorial : ℕ) : ℝ)

lemma series_term_ratio (j : ℕ) (hj : 20 ≤ j) : sterm (j+1) ≤ (7/8) * sterm j := by
  unfold sterm
  have hjR : (20:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj
  have hjR0 : (0:ℝ) < (j:ℝ) := by linarith
  have hcastj : ((j+1:ℕ):ℝ) = (j:ℝ)+1 := by push_cast; ring
  have hcast1 : ((2*j+1:ℕ):ℝ) = 2*(j:ℝ)+1 := by push_cast; ring
  have hcast2 : ((2*j+2:ℕ):ℝ) = 2*(j:ℝ)+2 := by push_cast; ring
  have hfac : (((2*(j+1)).factorial : ℕ) : ℝ)
      = (((2*j+1:ℕ):ℝ) * ((2*j+2:ℕ):ℝ)) * (((2*j).factorial : ℕ) : ℝ) := by
    rw [show 2*(j+1) = (2*j+1)+1 by omega, Nat.factorial_succ, Nat.factorial_succ]
    push_cast; ring
  have hpoweq : (((13:ℝ)/25)*((j:ℝ)+1))^(2*j+2)
      = ((((j:ℝ)+1)/(j:ℝ))^(2*j)) * ((((13:ℝ)/25)*((j:ℝ)))^(2*j))
        * ((((13:ℝ)/25)*((j:ℝ)+1))^2) := by
    rw [pow_add]
    have hbase : ((13:ℝ)/25)*((j:ℝ)+1) = (((j:ℝ)+1)/(j:ℝ)) * (((13:ℝ)/25)*((j:ℝ))) := by
      field_simp
    rw [hbase, mul_pow, mul_pow]
  have hK : ((1000:ℝ)/599) * (((j:ℝ)+1)/(j:ℝ))^(2*j) * ((((13:ℝ)/25)*((j:ℝ)+1))^2)
      ≤ (7/8) * (((2*j+1:ℕ):ℝ) * ((2*j+2:ℕ):ℝ)) := by
    rw [hcast1, hcast2]
    have hp := one_add_inv_pow_le j (by omega)
    rw [show ((j:ℝ)+1)/(j:ℝ) = 1 + 1/(j:ℝ) by field_simp]
    nlinarith [hp, hjR]
  have hnum : ((1000:ℝ)/599)^(j+1) * (((13:ℝ)/25)*(((j+1:ℕ):ℝ)))^(2*(j+1))
      = (((1000:ℝ)/599) * (((j:ℝ)+1)/(j:ℝ))^(2*j) * ((((13:ℝ)/25)*((j:ℝ)+1))^2))
        * (((1000:ℝ)/599)^j * ((((13:ℝ)/25)*((j:ℝ)))^(2*j))) := by
    rw [hcastj, show 2*(j+1) = 2*j+2 by omega, pow_succ, hpoweq]
    ring
  have hkey : ((1000:ℝ)/599)^(j+1) * (((13:ℝ)/25)*(((j+1:ℕ):ℝ)))^(2*(j+1))
        / (((2*(j+1)).factorial : ℕ) : ℝ)
      = (((1000:ℝ)/599) * (((j:ℝ)+1)/(j:ℝ))^(2*j) * ((((13:ℝ)/25)*((j:ℝ)+1))^2)
          / (((2*j+1:ℕ):ℝ) * ((2*j+2:ℕ):ℝ)))
        * (((1000:ℝ)/599)^j * ((((13:ℝ)/25)*((j:ℝ)))^(2*j)) / (((2*j).factorial : ℕ) : ℝ)) := by
    rw [hnum, hfac]
    field_simp
  rw [hkey]
  have hK' : ((1000:ℝ)/599) * (((j:ℝ)+1)/(j:ℝ))^(2*j) * ((((13:ℝ)/25)*((j:ℝ)+1))^2)
      / (((2*j+1:ℕ):ℝ) * ((2*j+2:ℕ):ℝ)) ≤ 7/8 := by
    rw [div_le_iff₀ (by positivity)]
    exact hK
  exact mul_le_mul_of_nonneg_right hK' (by positivity)

lemma series_term_iter (a : ℕ) (ha : 20 ≤ a) : ∀ k : ℕ, sterm (a+k) ≤ (7/8:ℝ)^k * sterm a := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : sterm (a+k+1) ≤ (7/8) * sterm (a+k) := series_term_ratio (a+k) (by omega)
    calc sterm (a+k+1) ≤ (7/8) * sterm (a+k) := h1
      _ ≤ (7/8) * ((7/8)^k * sterm a) := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = (7/8)^(k+1) * sterm a := by ring

lemma geom_telescope (a : ℕ) : ∀ k : ℕ,
    ∑ j ∈ Finset.Icc a (a+k), ((7/8:ℝ)^j - (7/8)^(j+1)) = (7/8)^a - (7/8)^(a+k+1) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show a + (k+1) = a + k + 1 by omega, Finset.sum_Icc_succ_top (by omega), ih]
    ring

lemma geom_tail_le (a : ℕ) : ∀ k : ℕ,
    ∑ j ∈ Finset.Icc a (a+k), (7/8:ℝ)^j ≤ 8 * (7/8)^a := by
  intro k
  have h1 := geom_telescope a k
  have h2 : ∑ j ∈ Finset.Icc a (a+k), (7/8:ℝ)^j
      = 8 * ∑ j ∈ Finset.Icc a (a+k), ((7/8)^j - (7/8)^(j+1)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [h2, h1]
  have := pow_nonneg (by norm_num : (0:ℝ) ≤ 7/8) (a+k+1)
  linarith

lemma sterm_Icc_eq_range (N : ℕ) :
    ∑ j ∈ Finset.Icc 1 N, sterm j = ∑ k ∈ Finset.range N, sterm (k+1) := by
  rw [show Finset.Icc 1 N = (Finset.range N).image (fun k => k+1) by
    ext j; simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨j-1, by omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩; omega]
  rw [Finset.sum_image]
  intro a _ b _ h
  exact Nat.succ.inj h

set_option maxHeartbeats 4000000 in
lemma sterm_head : ∑ k ∈ Finset.range 41, sterm (k+1) ≤ 19/25 := by
  unfold sterm
  norm_num

lemma series_bound (N : ℕ) : ∑ j ∈ Finset.Icc 1 N, sterm j ≤ 5/6 := by
  rw [sterm_Icc_eq_range]
  rcases Nat.lt_or_ge N 41 with hN | hN
  · have hsub : ∑ k ∈ Finset.range N, sterm (k+1) ≤ ∑ k ∈ Finset.range 41, sterm (k+1) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => ?_)
      · intro k hk; simp only [Finset.mem_range] at hk ⊢; omega
      · unfold sterm
        exact div_nonneg (mul_nonneg (pow_nonneg (by norm_num) _)
          (pow_nonneg (by positivity) _)) (by positivity)
    linarith [sterm_head, hsub]
  · rw [show N = 41 + (N-41) by omega, Finset.sum_range_add]
    have htail : ∑ k ∈ Finset.range (N-41), sterm (41+k+1) ≤ 1/100 := by
      have hpt : ∀ k : ℕ, sterm (41+k+1) ≤ ((7/8:ℝ)^(12+k)) * sterm 30 := by
        intro k
        have h1 := series_term_iter 30 (by norm_num) (11+k+1)
        have hidx : 30 + (11+k+1) = 41+k+1 := by omega
        rw [hidx] at h1
        calc sterm (41+k+1) ≤ (7/8:ℝ)^(11+k+1) * sterm 30 := h1
          _ = (7/8:ℝ)^(12+k) * sterm 30 := by
              congr 2
              omega
      calc ∑ k ∈ Finset.range (N-41), sterm (41+k+1)
          ≤ ∑ k ∈ Finset.range (N-41), ((7/8:ℝ)^(12+k)) * sterm 30 :=
            Finset.sum_le_sum (fun k _ => hpt k)
        _ = sterm 30 * ∑ k ∈ Finset.range (N-41), (7/8:ℝ)^(12+k) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun k _ => by ring)
        _ ≤ sterm 30 * (8 * (7/8)^12) := by
            refine mul_le_mul_of_nonneg_left ?_ (by unfold sterm; positivity)
            have hsplit : ∑ k ∈ Finset.range (N-41), (7/8:ℝ)^(12+k)
                = (7/8)^12 * ∑ k ∈ Finset.range (N-41), (7/8)^k := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl (fun k _ => ?_)
              rw [pow_add]
            rw [hsplit]
            have hg := geom_range_le (7/8:ℝ) (by norm_num) (by norm_num) (N-41)
            have h2 : (0:ℝ) ≤ (7/8)^12 := by positivity
            calc (7/8:ℝ)^12 * ∑ k ∈ Finset.range (N-41), (7/8)^k
                ≤ (7/8)^12 * (1/(1-7/8)) := mul_le_mul_of_nonneg_left hg h2
              _ = 8 * (7/8)^12 := by norm_num
        _ ≤ 1/100 := by
            have h30 : sterm 30 ≤ 1/2000 := by unfold sterm; norm_num
            have h68 : (7/8:ℝ)^12 * 8 ≤ 2 := by norm_num
            nlinarith [h30]
    have hhead : ∑ k ∈ Finset.range 41, sterm (k+1) ≤ 19/25 := sterm_head
    have hpos : (0:ℝ) < sterm 30 := by unfold sterm; positivity
    linarith [hhead, htail]
lemma V2T_sum_range_eq_Icc (y : ℝ) (M N : ℕ) :
    ∑ j ∈ Finset.range N, V2T y (j+1) M = ∑ j ∈ Finset.Icc 1 N, V2T y j M := by
  rw [show Finset.Icc 1 N = (Finset.range N).image (fun k => k+1) by
    ext j; simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨j-1, by omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩; omega]
  rw [Finset.sum_image]
  intro a _ b _ h
  exact Nat.succ.inj h

/-- `Bnd y 1 M` is the sum of the first-violation terms over all levels `1 ≤ j ≤ M`. -/
lemma Bnd_eq_Icc (y : ℝ) (M : ℕ) (hM : 1 ≤ M) :
    Bnd y 1 M = ∑ j ∈ Finset.Icc 1 M, V2T y j M := by
  have h := Bnd_eq_V2T_sum y M (M-1)
  rw [show (M-1)+1 = M by omega] at h
  rw [h, PB_eq_zero y M M (by omega), add_zero, V2T_sum_range_eq_Icc]

/-- `t ≤ -log(1-t)` for `0 ≤ t < 1` (the elementary inequality used to pass from a product
to the sum of reciprocals). -/
lemma le_neg_log_one_sub {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) : t ≤ -Real.log (1 - t) := by
  have hpos : (0:ℝ) < 1 - t := by linarith
  rw [show -Real.log (1 - t) = Real.log (1/(1-t)) by
    rw [Real.log_div one_ne_zero (ne_of_gt hpos), Real.log_one, zero_sub]]
  rw [Real.le_log_iff_exp_le (by positivity)]
  rw [le_div_iff₀ hpos]
  have h2 : (1:ℝ) - t ≤ Real.exp (-t) := by
    have := Real.add_one_le_exp (-t); linarith
  have h3 : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add]; ring_nf; simp
  have := mul_le_mul_of_nonneg_left h2 (le_of_lt (Real.exp_pos t))
  linarith [this, h3]

/-- The reciprocal sum over the primes above the sifting level is bounded by the logarithm of the
ratio of the two sifted products. -/
lemma T_le_log_ratio (y : ℝ) (j M : ℕ) (hM : 1 ≤ M) (hcut0 : 0 ≤ cut y j)
    (hcut : cut y j ≤ (M:ℝ) - 1) :
    (∑ p ∈ (oddLt M).filter (fun p : ℕ => cut y j < (p:ℝ)), ((p:ℝ)-1)⁻¹)
      ≤ Real.log (Vodd (cut y j) / Vodd ((M:ℝ)-1)) := by
  set S : Finset ℕ := (oddLt M).filter (fun p : ℕ => cut y j < (p:ℝ)) with hS
  have hM1 : ((M - 1 : ℕ) : ℝ) = (M:ℝ) - 1 := by rw [Nat.cast_sub hM, Nat.cast_one]
  have hfl : ((⌊cut y j⌋₊ : ℕ) : ℝ) ≤ cut y j := Nat.floor_le hcut0
  have hfloor : ⌊cut y j⌋₊ ≤ M - 1 := by
    have h1 : ((⌊cut y j⌋₊ : ℕ) : ℝ) ≤ (M:ℝ) - 1 := le_trans hfl hcut
    rw [← hM1] at h1; exact_mod_cast h1
  have hVc : Vodd (cut y j) = (∏ p ∈ (Nat.primesLE ⌊cut y j⌋₊).filter (fun p : ℕ => p ≠ 2),
      ((1:ℝ) - 1/((p:ℝ)-1))) := rfl
  have hVm : Vodd ((M:ℝ)-1) = (∏ p ∈ (Nat.primesLE (M-1)).filter (fun p : ℕ => p ≠ 2),
      ((1:ℝ) - 1/((p:ℝ)-1))) := by
    rw [Vodd, ← hM1, Nat.floor_natCast]
  have hBS : (Nat.primesLE (M-1)).filter (fun p : ℕ => p ≠ 2)
      = ((Nat.primesLE ⌊cut y j⌋₊).filter (fun p : ℕ => p ≠ 2)) ∪ S := by
    rw [hS]
    ext p
    simp only [Finset.mem_union, Finset.mem_filter, Nat.mem_primesLE, oddLt, Finset.mem_range]
    constructor
    · rintro ⟨⟨hple, hprime⟩, hne2⟩
      by_cases hpc : p ≤ ⌊cut y j⌋₊
      · exact Or.inl ⟨⟨hpc, hprime⟩, hne2⟩
      · push_neg at hpc
        refine Or.inr ⟨⟨by omega, hprime, ?_⟩, ?_⟩
        · have := hprime.two_le; omega
        · have h2 : ((⌊cut y j⌋₊ : ℕ) : ℝ) < (p:ℝ) := by exact_mod_cast hpc
          have h3 : cut y j < ((⌊cut y j⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
          have h4 : ((⌊cut y j⌋₊ : ℕ) : ℝ) + 1 ≤ (p:ℝ) := by
            exact_mod_cast (by omega : ⌊cut y j⌋₊ + 1 ≤ p)
          linarith
    · rintro (⟨⟨hple, hprime⟩, hne2⟩ | ⟨⟨hpm, hprime, h3⟩, hpc⟩)
      · exact ⟨⟨le_trans hple hfloor, hprime⟩, hne2⟩
      · exact ⟨⟨by omega, hprime⟩, by omega⟩
  have hdisj : Disjoint ((Nat.primesLE ⌊cut y j⌋₊).filter (fun p : ℕ => p ≠ 2)) S := by
    rw [Finset.disjoint_left]
    intro p hpA hpS
    rw [Finset.mem_filter, Nat.mem_primesLE] at hpA
    rw [hS, Finset.mem_filter, oddLt, Finset.mem_filter, Finset.mem_range] at hpS
    have h1 : ((p:ℕ):ℝ) ≤ (⌊cut y j⌋₊ : ℝ) := by exact_mod_cast hpA.1.1
    linarith
  have hAne : (∏ p ∈ (Nat.primesLE ⌊cut y j⌋₊).filter (fun p : ℕ => p ≠ 2),
      ((1:ℝ) - 1/((p:ℝ)-1))) ≠ 0 := by
    apply ne_of_gt
    apply Finset.prod_pos
    intro p hp
    rw [Finset.mem_filter, Nat.mem_primesLE] at hp
    exact oneSubInvPred_pos_of_ne_two hp.1.2 hp.2
  have hquot : Vodd (cut y j) / Vodd ((M:ℝ)-1) = (∏ p ∈ S, ((1:ℝ) - 1/((p:ℝ)-1)))⁻¹ := by
    rw [hVc, hVm, hBS, Finset.prod_union hdisj]
    rw [div_eq_mul_inv, mul_inv, ← mul_assoc, mul_inv_cancel₀ hAne, one_mul]
  rw [hquot]
  have hfS : ∀ p ∈ S, (1:ℝ) - 1/((p:ℝ)-1) ≠ 0 := by
    intro p hp
    rw [hS, Finset.mem_filter, oddLt, Finset.mem_filter, Finset.mem_range] at hp
    exact ne_of_gt (oneSubInvPred_pos_of_ne_two hp.1.2.1
      (by have := hp.1.2.1.two_le; omega))
  have hpt : ∀ p ∈ S, ((p:ℝ)-1)⁻¹ ≤ -Real.log (1 - 1/((p:ℝ)-1)) := by
    intro p hp
    rw [hS, Finset.mem_filter, oddLt, Finset.mem_filter, Finset.mem_range] at hp
    have h3 : 3 ≤ p := hp.1.2.2
    have hpR : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast h3
    have hinv0 : 0 ≤ ((p:ℝ)-1)⁻¹ := inv_nonneg.mpr (by linarith)
    have h2p : (2:ℝ) ≤ (p:ℝ) - 1 := by linarith
    have hinv1 : ((p:ℝ)-1)⁻¹ ≤ 1/2 := by
      have h := inv_anti₀ (by norm_num : (0:ℝ) < 2) h2p
      simpa using h
    have := le_neg_log_one_sub hinv0 (by linarith : ((p:ℝ)-1)⁻¹ < 1)
    simpa using this
  calc (∑ p ∈ S, ((p:ℝ)-1)⁻¹)
      ≤ ∑ p ∈ S, -Real.log (1 - 1/((p:ℝ)-1)) := Finset.sum_le_sum hpt
    _ = -∑ p ∈ S, Real.log (1 - 1/((p:ℝ)-1)) := by rw [Finset.sum_neg_distrib]
    _ = -Real.log (∏ p ∈ S, (1 - 1/((p:ℝ)-1))) := by
        rw [Real.log_prod]; intro p hp; exact hfS p hp
    _ = Real.log ((∏ p ∈ S, (1 - 1/((p:ℝ)-1)))⁻¹) := by rw [Real.log_inv]

/-- Ratio of two positive quantities whose products with their logarithms are controlled. -/
lemma ratio_le_mul {a b la lb L δ : ℝ} (ha : 0 < la) (hb : 0 < lb) (hL : 0 < L)
    (hδ0 : 0 < δ) (hδ : δ < 1) (ha' : a * la ≤ (1+δ)*L) (hb' : (1-δ)*L ≤ b * lb)
    (hbpos : 0 < b) :
    a / b ≤ ((1+δ)/(1-δ)) * (lb / la) := by
  have h1δ : 0 < 1 - δ := by linarith
  have h1 : a ≤ (1+δ)*L/la := (le_div_iff₀ ha).mpr ha'
  have h2 : (1-δ)*L/lb ≤ b := (div_le_iff₀ hb).mpr hb'
  have hfac : 0 ≤ ((1+δ)/(1-δ)) * (lb/la) :=
    mul_nonneg (div_nonneg (by linarith) (le_of_lt h1δ)) (div_nonneg (le_of_lt hb) (le_of_lt ha))
  rw [div_le_iff₀ hbpos]
  calc a ≤ (1+δ)*L/la := h1
    _ = (((1+δ)/(1-δ)) * (lb/la)) * ((1-δ)*L/lb) := by
        field_simp
    _ ≤ (((1+δ)/(1-δ)) * (lb/la)) * b := mul_le_mul_of_nonneg_left h2 hfac

/-- **Sharp levels.**  If both `cut y j` and `M-1` lie above the threshold `Z` of the Mertens
product asymptotics, then the reciprocal sum above the level is at most `β j + ε` with
`β = log(1000/599)` and `ε = log((1+δ)/(1-δ)) + log(1+δ)`. -/
lemma T_le_beta_j (y : ℝ) (hy : 1 < y) (j M : ℕ) (hM : 1 ≤ M) (hcut0 : 0 ≤ cut y j)
    (hcut : cut y j ≤ (M:ℝ) - 1) {Z L δ : ℝ} (hL : 0 < L) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hZ3 : 3 ≤ Z) (hZc : Z ≤ cut y j) (hZM : Z ≤ (M:ℝ) - 1)
    (hZ : ∀ z : ℝ, Z ≤ z → (1-δ)*L ≤ Real.log z * Vodd z ∧ Real.log z * Vodd z ≤ (1+δ)*L)
    (hlogM : Real.log ((M:ℝ) - 1) ≤ (1 + δ) * Real.log y) :
    (∑ p ∈ (oddLt M).filter (fun q : ℕ => cut y j < (q:ℝ)), ((p:ℝ)-1)⁻¹)
      ≤ Real.log (1000/599) * j + (Real.log ((1+δ)/(1-δ)) + Real.log (1+δ)) := by
  refine le_trans (T_le_log_ratio y j M hM hcut0 hcut) ?_
  have hy1 : (0:ℝ) < y := by linarith
  have hsapos : 0 < sieveAlpha := by rw [sieveAlpha]; norm_num
  have hZ3' : (3:ℝ) ≤ Z := by exact_mod_cast hZ3
  have hc1 : (1:ℝ) < cut y j := by linarith
  have hlc : 0 < Real.log (cut y j) := Real.log_pos hc1
  have hm1 : (1:ℝ) < (M:ℝ) - 1 := by linarith
  have hlm : 0 < Real.log ((M:ℝ) - 1) := Real.log_pos hm1
  have hVc : Vodd (cut y j) * Real.log (cut y j) ≤ (1+δ)*L := by
    simpa [mul_comm] using (hZ (cut y j) hZc).2
  have hVm : (1-δ)*L ≤ Vodd ((M:ℝ) - 1) * Real.log ((M:ℝ) - 1) := by
    simpa [mul_comm] using (hZ ((M:ℝ) - 1) hZM).1
  have hratio : Vodd (cut y j) / Vodd ((M:ℝ) - 1)
      ≤ ((1+δ)/(1-δ)) * (Real.log ((M:ℝ) - 1) / Real.log (cut y j)) :=
    ratio_le_mul (a := Vodd (cut y j)) (b := Vodd ((M:ℝ) - 1)) (la := Real.log (cut y j))
      (lb := Real.log ((M:ℝ) - 1)) (L := L) (δ := δ) hlc hlm hL hδ0 hδ1 hVc hVm
      (Vodd_pos ((M:ℝ) - 1))
  have hlogcut : Real.log (cut y j) = sieveAlpha^j * Real.log y := by
    rw [cut, Real.log_rpow hy1]
  have hpow : ((1000:ℝ)/599)^j * sieveAlpha^j = 1 := by
    rw [← mul_pow, show ((1000:ℝ)/599) * sieveAlpha = 1 by rw [sieveAlpha]; norm_num, one_pow]
  have hdenpos : 0 < sieveAlpha^j * Real.log y :=
    mul_pos (pow_pos hsapos j) (Real.log_pos hy)
  have hlm_lc : Real.log ((M:ℝ) - 1) / Real.log (cut y j) ≤ (1+δ) * ((1000:ℝ)/599)^j := by
    rw [hlogcut, div_le_iff₀ hdenpos]
    have h2 : (1+δ) * ((1000:ℝ)/599)^j * (sieveAlpha^j * Real.log y) = (1+δ) * Real.log y := by
      rw [show (1+δ) * ((1000:ℝ)/599)^j * (sieveAlpha^j * Real.log y)
          = (1+δ) * (((1000:ℝ)/599)^j * sieveAlpha^j) * Real.log y by ring, hpow]
      ring
    linarith [hlogM, h2.le, h2.ge]
  calc Real.log (Vodd (cut y j) / Vodd ((M:ℝ) - 1))
      ≤ Real.log (((1+δ)/(1-δ)) * (Real.log ((M:ℝ) - 1) / Real.log (cut y j))) :=
        Real.log_le_log (div_pos (Vodd_pos _) (Vodd_pos _)) hratio
    _ = Real.log ((1+δ)/(1-δ)) + Real.log (Real.log ((M:ℝ) - 1) / Real.log (cut y j)) := by
        rw [Real.log_mul (by positivity) (by positivity)]
    _ ≤ Real.log ((1+δ)/(1-δ)) + Real.log ((1+δ) * ((1000:ℝ)/599)^j) := by
        have h2 : 0 < Real.log ((M:ℝ) - 1) / Real.log (cut y j) := div_pos hlm hlc
        have h3 : 0 < (1+δ) * ((1000:ℝ)/599)^j := by positivity
        linarith [Real.log_le_log h2 hlm_lc]
    _ = Real.log (1000/599) * j + (Real.log ((1+δ)/(1-δ)) + Real.log (1+δ)) := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
        ring

/-- **Sharp-level `V2T` bound.**  For a level whose cut lies above the threshold `Z` (and `M-1`
above it too), the first-violation mass is at most
`((1+δ)/(1-δ))(1+δ)·VsieveOdd M·(1000/599)^j·(βj+ε)^{2j}/(2j)!` with `β = log(1000/599)`,
`ε = log((1+δ)/(1-δ)) + log(1+δ)`; the factor `(1000/599)^j = e^{βj}` is what `series_bound` consumes. -/
lemma V2T_sharp_le (y : ℝ) (hy : 1 < y) (j M : ℕ) (hj : 1 ≤ j) (hM : 1 ≤ M)
    (hcut0 : 0 ≤ cut y j) (hcut : cut y j ≤ (M:ℝ) - 1) {Z L δ : ℝ}
    (hL : 0 < L) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hZ3 : 3 ≤ Z)
    (hZc : Z ≤ cut y j) (hZM : Z ≤ (M:ℝ) - 1)
    (hZ : ∀ z : ℝ, Z ≤ z → (1-δ)*L ≤ Real.log z * Vodd z ∧ Real.log z * Vodd z ≤ (1+δ)*L)
    (hlogM : Real.log ((M:ℝ) - 1) ≤ (1 + δ) * Real.log y) :
    V2T y j M ≤ ((1+δ)/(1-δ)) * (1+δ) * VsieveOdd M * ((1000:ℝ)/599)^j *
      ((Real.log (1000/599) * j + (Real.log ((1+δ)/(1-δ)) + Real.log (1+δ)))^(2*j)
        / ((2*j).factorial : ℝ)) := by
  have hy1 : (0:ℝ) < y := by linarith
  have hsapos : 0 < sieveAlpha := by rw [sieveAlpha]; norm_num
  have hZ3' : (3:ℝ) ≤ Z := by exact_mod_cast hZ3
  have hc1 : (1:ℝ) < cut y j := by linarith
  have hlc : 0 < Real.log (cut y j) := Real.log_pos hc1
  have hm1 : (1:ℝ) < (M:ℝ) - 1 := by linarith
  have hlm : 0 < Real.log ((M:ℝ) - 1) := Real.log_pos hm1
  have hVc : Vodd (cut y j) * Real.log (cut y j) ≤ (1+δ)*L := by
    simpa [mul_comm] using (hZ (cut y j) hZc).2
  have hVm : (1-δ)*L ≤ Vodd ((M:ℝ) - 1) * Real.log ((M:ℝ) - 1) := by
    simpa [mul_comm] using (hZ ((M:ℝ) - 1) hZM).1
  have hratio := ratio_le_mul (a := Vodd (cut y j)) (b := Vodd ((M:ℝ) - 1))
      (la := Real.log (cut y j)) (lb := Real.log ((M:ℝ) - 1)) (L := L) (δ := δ)
      hlc hlm hL hδ0 hδ1 hVc hVm (Vodd_pos ((M:ℝ) - 1))
  have hlogcut : Real.log (cut y j) = sieveAlpha^j * Real.log y := by
    rw [cut, Real.log_rpow hy1]
  have hpow : ((1000:ℝ)/599)^j * sieveAlpha^j = 1 := by
    rw [← mul_pow, show ((1000:ℝ)/599) * sieveAlpha = 1 by rw [sieveAlpha]; norm_num, one_pow]
  have hdenpos : 0 < sieveAlpha^j * Real.log y := mul_pos (pow_pos hsapos j) (Real.log_pos hy)
  have hlm_lc : Real.log ((M:ℝ) - 1) / Real.log (cut y j) ≤ (1+δ) * ((1000:ℝ)/599)^j := by
    rw [hlogcut, div_le_iff₀ hdenpos]
    have h2 : (1+δ) * ((1000:ℝ)/599)^j * (sieveAlpha^j * Real.log y) = (1+δ) * Real.log y := by
      rw [show (1+δ) * ((1000:ℝ)/599)^j * (sieveAlpha^j * Real.log y)
          = (1+δ) * (((1000:ℝ)/599)^j * sieveAlpha^j) * Real.log y by ring, hpow]
      ring
    linarith [hlogM, h2.le, h2.ge]
  have hVmpos : 0 < Vodd ((M:ℝ) - 1) := Vodd_pos _
  have hVbound : Vodd (cut y j) ≤ ((1+δ)/(1-δ)) * (1+δ) * ((1000:ℝ)/599)^j * Vodd ((M:ℝ) - 1) := by
    rw [div_le_iff₀ hVmpos] at hratio
    have hstep : ((1+δ)/(1-δ)) * (Real.log ((M:ℝ) - 1)/Real.log (cut y j)) * Vodd ((M:ℝ) - 1)
        ≤ ((1+δ)/(1-δ)) * ((1+δ) * ((1000:ℝ)/599)^j) * Vodd ((M:ℝ) - 1) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlm_lc (by positivity)) (le_of_lt hVmpos)
    calc Vodd (cut y j)
        ≤ ((1+δ)/(1-δ)) * (Real.log ((M:ℝ) - 1)/Real.log (cut y j)) * Vodd ((M:ℝ) - 1) := hratio
      _ ≤ ((1+δ)/(1-δ)) * ((1+δ) * ((1000:ℝ)/599)^j) * Vodd ((M:ℝ) - 1) := hstep
      _ = ((1+δ)/(1-δ)) * (1+δ) * ((1000:ℝ)/599)^j * Vodd ((M:ℝ) - 1) := by ring
  have hT := T_le_beta_j y hy j M hM hcut0 hcut hL hδ0 hδ1 hZ3 hZc hZM hZ hlogM
  have hVb := V2T_bound y (le_of_lt hy) j M hj
  set S : Finset ℕ := (oddLt M).filter (fun q : ℕ => cut y j < (q:ℝ)) with hS
  have hT' : ∑ p ∈ S, ((p:ℝ)-1)⁻¹
      ≤ Real.log (1000/599) * j + (Real.log ((1+δ)/(1-δ)) + Real.log (1+δ)) := by
    rw [hS]; exact hT
  have hsum0 : 0 ≤ ∑ p ∈ S, ((p:ℝ)-1)⁻¹ := by
    rw [hS]
    refine Finset.sum_nonneg (fun p hp => ?_)
    rw [Finset.mem_filter, oddLt, Finset.mem_filter, Finset.mem_range] at hp
    exact inv_nonneg.mpr (by have h2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.1.2.1.two_le
                             linarith)
  have hXpos : 0 ≤ (Real.log (1000/599) * j + (Real.log ((1+δ)/(1-δ)) + Real.log (1+δ)))^(2*j)
      / ((2*j).factorial : ℝ) := by
    have h3 : (1:ℝ) ≤ (1+δ)/(1-δ) := by
      rw [one_le_div (by linarith : (0:ℝ) < 1-δ)]; linarith
    have h4 : 0 ≤ Real.log ((1+δ)/(1-δ)) := Real.log_nonneg h3
    have h5 : 0 ≤ Real.log (1+δ) := Real.log_nonneg (by linarith)
    have h6 : 0 ≤ Real.log (1000/599) := Real.log_nonneg (by norm_num)
    exact div_nonneg (pow_nonneg (by linarith) _) (by positivity)
  calc V2T y j M
      ≤ VsieveOdd (⌊cut y j⌋₊ + 1) *
          ((∑ p ∈ S, ((p:ℝ)-1)⁻¹)^(2*j) / ((2*j).factorial : ℝ)) := by
        rw [hS]; exact hVb
    _ = Vodd (cut y j) * ((∑ p ∈ S, ((p:ℝ)-1)⁻¹)^(2*j) / ((2*j).factorial : ℝ)) := by
        rw [VsieveOdd_eq_Vodd]
    _ ≤ Vodd (cut y j) *
          ((Real.log (1000/599) * j + (Real.log ((1+δ)/(1-δ)) + Real.log (1+δ)))^(2*j)
            / ((2*j).factorial : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (Vodd_pos _))
        exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hsum0 hT' (2*j)) (by positivity)
    _ ≤ (((1+δ)/(1-δ)) * (1+δ) * ((1000:ℝ)/599)^j * Vodd ((M:ℝ) - 1)) *
          ((Real.log (1000/599) * j + (Real.log ((1+δ)/(1-δ)) + Real.log (1+δ)))^(2*j)
            / ((2*j).factorial : ℝ)) := by
        exact mul_le_mul_of_nonneg_right hVbound hXpos
    _ = ((1+δ)/(1-δ)) * (1+δ) * VsieveOdd M * ((1000:ℝ)/599)^j *
          ((Real.log (1000/599) * j + (Real.log ((1+δ)/(1-δ)) + Real.log (1+δ)))^(2*j)
            / ((2*j).factorial : ℝ)) := by
        rw [← VsieveOdd_eq_Vodd_pred M hM]
        ring

/-- `log(1000/599) ≤ 49/100` (so that `log(1000/599)·j + ε ≤ j/2` for `ε ≤ 1/100`). -/
lemma log_1000_599_le : Real.log (1000/599) ≤ 513/1000 := by
  rw [Real.log_le_iff_le_exp (by norm_num : (0:ℝ) < 1000/599)]
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 513/1000) 6
  have h2 : (1000:ℝ)/599 ≤ ∑ k ∈ Finset.range 6, (513/1000)^k / ((k.factorial : ℕ) : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  linarith

/-- **Sharp-level series collapse.**  With `β = log(1000/599) ≤ 49/100` and `ε ≤ 1/100` we have
`β j + ε ≤ j/2`, so the sharp-level series is bounded by `series_bound`. -/
lemma sharp_series_sum (J : ℕ) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 7/1000) :
    ∑ j ∈ Finset.Icc 1 J,
        ((1000:ℝ)/599)^j * ((Real.log (1000/599) * j + ε)^(2*j) / ((2*j).factorial : ℝ))
      ≤ 5/6 := by
  have hlogpos : 0 ≤ Real.log (1000/599) := Real.log_nonneg (by norm_num)
  have hpt : ∀ j ∈ Finset.Icc 1 J,
      ((1000:ℝ)/599)^j * ((Real.log (1000/599) * j + ε)^(2*j) / ((2*j).factorial : ℝ))
        ≤ sterm j := by
    intro j hj
    have hj1 : (1:ℝ) ≤ (j:ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hj).1
    have hj0 : (0:ℝ) ≤ (j:ℝ) := by linarith
    have h0 : 0 ≤ Real.log (1000/599) * j + ε := by nlinarith [hlogpos, hε0, hj0]
    have h1 : Real.log (1000/599) * j + ε ≤ ((13:ℝ)/25) * (j:ℝ) := by
      nlinarith [log_1000_599_le, hε1, hj1]
    have h2 : (Real.log (1000/599) * j + ε)^(2*j) ≤ (((13:ℝ)/25) * (j:ℝ))^(2*j) :=
      pow_le_pow_left₀ h0 h1 (2*j)
    have h3 : (0:ℝ) < (((2*j).factorial : ℕ) : ℝ) := by positivity
    have hmain : ((1000:ℝ)/599)^j * ((Real.log (1000/599) * j + ε)^(2*j) / ((2*j).factorial : ℝ))
        ≤ ((1000:ℝ)/599)^j * ((((13:ℝ)/25) * (j:ℝ))^(2*j) / ((2*j).factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h2 (le_of_lt h3)) (by positivity)
    simpa only [sterm, mul_div_assoc] using hmain
  exact le_trans (Finset.sum_le_sum hpt) (series_bound J)

/-- **Sharp-level sum.**  Summing `V2T_sharp_le` over all levels whose cuts lie above the threshold
`Z` and collapsing with `sharp_series_sum`. -/
lemma V2T_sharp_sum (y : ℝ) (hy : 1 < y) (M J : ℕ) (hM : 1 ≤ M) {Z L δ : ℝ}
    (hL : 0 < L) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hZ3 : 3 ≤ Z)
    (hZ : ∀ z : ℝ, Z ≤ z → (1-δ)*L ≤ Real.log z * Vodd z ∧ Real.log z * Vodd z ≤ (1+δ)*L)
    (hZc : ∀ j ∈ Finset.Icc 1 J, Z ≤ cut y j)
    (hZM : Z ≤ (M:ℝ) - 1)
    (hcutM : ∀ j ∈ Finset.Icc 1 J, cut y j ≤ (M:ℝ) - 1)
    (hcut0 : ∀ j ∈ Finset.Icc 1 J, 0 ≤ cut y j)
    (hlogM : Real.log ((M:ℝ) - 1) ≤ (1 + δ) * Real.log y)
    (hε1 : Real.log ((1+δ)/(1-δ)) + Real.log (1+δ) ≤ 7/1000) :
    ∑ j ∈ Finset.Icc 1 J, V2T y j M ≤ ((1+δ)/(1-δ)) * (1+δ) * VsieveOdd M * (5/6) := by
  have h3 : (1:ℝ) ≤ (1+δ)/(1-δ) := by
    rw [one_le_div (by linarith : (0:ℝ) < 1-δ)]; linarith
  have hε0 : 0 ≤ Real.log ((1+δ)/(1-δ)) + Real.log (1+δ) :=
    add_nonneg (Real.log_nonneg h3) (Real.log_nonneg (by linarith))
  set C : ℝ := ((1+δ)/(1-δ)) * (1+δ) * VsieveOdd M with hC
  have hC0 : 0 ≤ C := by
    rw [hC]; have := VsieveOdd_nonneg M; positivity
  have hpt : ∀ j ∈ Finset.Icc 1 J, V2T y j M ≤ C * (((1000:ℝ)/599)^j *
      ((Real.log (1000/599) * j + (Real.log ((1+δ)/(1-δ)) + Real.log (1+δ)))^(2*j)
        / ((2*j).factorial : ℝ))) := by
    intro j hj
    have h1 := V2T_sharp_le y hy j M (Finset.mem_Icc.mp hj).1 hM (hcut0 j hj) (hcutM j hj)
      hL hδ0 hδ1 hZ3 (hZc j hj) hZM hZ hlogM
    rw [hC]
    calc V2T y j M
        ≤ ((1+δ)/(1-δ)) * (1+δ) * VsieveOdd M * ((1000:ℝ)/599)^j *
            ((Real.log (1000/599) * j + (Real.log ((1+δ)/(1-δ)) + Real.log (1+δ)))^(2*j)
              / ((2*j).factorial : ℝ)) := h1
      _ = ((1+δ)/(1-δ)) * (1+δ) * VsieveOdd M * (((1000:ℝ)/599)^j *
            ((Real.log (1000/599) * j + (Real.log ((1+δ)/(1-δ)) + Real.log (1+δ)))^(2*j)
              / ((2*j).factorial : ℝ))) := by ring
  calc ∑ j ∈ Finset.Icc 1 J, V2T y j M
      ≤ ∑ j ∈ Finset.Icc 1 J, C * (((1000:ℝ)/599)^j *
            ((Real.log (1000/599) * j + (Real.log ((1+δ)/(1-δ)) + Real.log (1+δ)))^(2*j)
              / ((2*j).factorial : ℝ))) := Finset.sum_le_sum hpt
    _ = C * ∑ j ∈ Finset.Icc 1 J, (((1000:ℝ)/599)^j *
            ((Real.log (1000/599) * j + (Real.log ((1+δ)/(1-δ)) + Real.log (1+δ)))^(2*j)
              / ((2*j).factorial : ℝ))) := by rw [Finset.mul_sum]
    _ ≤ C * (5/6) :=
        mul_le_mul_of_nonneg_left
          (sharp_series_sum J (Real.log ((1+δ)/(1-δ)) + Real.log (1+δ)) hε0 hε1) hC0
    _ = ((1+δ)/(1-δ)) * (1+δ) * VsieveOdd M * (5/6) := by rw [hC]

lemma VsieveOdd_pos (M : ℕ) : 0 < VsieveOdd M := by
  unfold VsieveOdd
  refine Finset.prod_pos (fun p hp => ?_)
  exact oneSubInvPred_pos_of_ne_two (Finset.mem_filter.mp hp).2.1
    (by have := (Finset.mem_filter.mp hp).2.2; omega)

/-- **Crude level.**  When the cut is at least `3` (so the sifted product at that level is at most
`1/2`) the level contributes at most `(1/2) · (log(1/VsieveOdd M))^{2j}/(2j)!`. -/
lemma V2T_crude_le (y : ℝ) (hy : 1 < y) (j M : ℕ) (hj : 1 ≤ j) (hM : 1 ≤ M)
    (hcut0 : 0 ≤ cut y j) (hcut : cut y j ≤ (M:ℝ) - 1) (h3 : 3 ≤ cut y j) :
    V2T y j M ≤ (1/2) *
      ((Real.log (1 / VsieveOdd M))^(2*j) / ((2*j).factorial : ℝ)) := by
  have hVs : VsieveOdd (⌊cut y j⌋₊ + 1) ≤ 1/2 := by
    rw [VsieveOdd_eq_Vodd]
    exact Vodd_le_half h3
  have hVodd1 : Vodd (cut y j) ≤ 1/2 := by rw [← VsieveOdd_eq_Vodd]; exact hVs
  have hVsM : 0 < VsieveOdd M := VsieveOdd_pos M
  have hT := T_le_log_ratio y j M hM hcut0 hcut
  have hT' : (∑ p ∈ (oddLt M).filter (fun q : ℕ => cut y j < (q:ℝ)), ((p:ℝ)-1)⁻¹)
      ≤ Real.log (1 / VsieveOdd M) := by
    rw [← VsieveOdd_eq_Vodd_pred M hM] at hT
    have hA : Vodd (cut y j) / VsieveOdd M ≤ (1/2) / VsieveOdd M :=
      div_le_div_of_nonneg_right hVodd1 (le_of_lt hVsM)
    have hB : (1/2) / VsieveOdd M ≤ 1 / VsieveOdd M :=
      div_le_div_of_nonneg_right (by norm_num) (le_of_lt hVsM)
    exact le_trans hT (le_trans (Real.log_le_log (div_pos (Vodd_pos _) hVsM) hA)
      (Real.log_le_log (by positivity) hB))
  have hTnn : 0 ≤ ∑ p ∈ (oddLt M).filter (fun q : ℕ => cut y j < (q:ℝ)), ((p:ℝ)-1)⁻¹ := by
    refine Finset.sum_nonneg (fun p hp => ?_)
    rw [Finset.mem_filter, oddLt, Finset.mem_filter, Finset.mem_range] at hp
    exact inv_nonneg.mpr (by have h2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.1.2.1.two_le
                             linarith)
  have hpow : (∑ p ∈ (oddLt M).filter (fun q : ℕ => cut y j < (q:ℝ)), ((p:ℝ)-1)⁻¹)^(2*j)
      ≤ (Real.log (1 / VsieveOdd M))^(2*j) := pow_le_pow_left₀ hTnn hT' (2*j)
  refine le_trans (V2T_bound y (le_of_lt hy) j M hj) ?_
  have hfact : (0:ℝ) < (((2*j).factorial : ℕ) : ℝ) := by positivity
  calc VsieveOdd (⌊cut y j⌋₊ + 1) *
        ((∑ p ∈ (oddLt M).filter (fun q : ℕ => cut y j < (q:ℝ)), ((p:ℝ)-1)⁻¹)^(2*j)
          / ((2*j).factorial : ℝ))
      ≤ (1/2) * ((Real.log (1 / VsieveOdd M))^(2*j) / ((2*j).factorial : ℝ)) := by
        have hD : (∑ p ∈ (oddLt M).filter (fun q : ℕ => cut y j < (q:ℝ)), ((p:ℝ)-1)⁻¹)^(2*j)
              / ((2*j).factorial : ℝ)
            ≤ (Real.log (1 / VsieveOdd M))^(2*j) / ((2*j).factorial : ℝ) :=
          div_le_div_of_nonneg_right hpow (le_of_lt hfact)
        exact mul_le_mul hVs hD (by positivity) (by norm_num)

/-- The Taylor-tail step: if `2x² ≤ (2N+1)(2N+2)` then the terms `x^(2j)/(2j)!` shrink by at
least a factor `2` per step from `j = N` on. -/
lemma factorial_tail_step (x : ℝ) (hx : 0 ≤ x) (N j : ℕ) (hNj : N ≤ j)
    (hρ : 2 * x^2 ≤ (((2*N+1)*(2*N+2) : ℕ) : ℝ)) :
    x^(2*(j+1)) / (((2*(j+1)).factorial : ℕ) : ℝ)
      ≤ (1/2) * (x^(2*j) / (((2*j).factorial : ℕ) : ℝ)) := by
  have hfac : (((2*(j+1)).factorial : ℕ) : ℝ)
      = (((2*j+1)*(2*j+2) : ℕ) : ℝ) * (((2*j).factorial : ℕ) : ℝ) := by
    rw [show 2*(j+1) = (2*j+1)+1 by omega, Nat.factorial_succ, Nat.factorial_succ]
    push_cast; ring
  have hcast : (((2*N+1)*(2*N+2) : ℕ) : ℝ) ≤ (((2*j+1)*(2*j+2) : ℕ) : ℝ) := by
    have h : (2*N+1)*(2*N+2) ≤ (2*j+1)*(2*j+2) := Nat.mul_le_mul (by omega) (by omega)
    exact_mod_cast h
  have hF : (0:ℝ) < (((2*j).factorial : ℕ) : ℝ) := by positivity
  have hA : (0:ℝ) < (((2*j+1)*(2*j+2) : ℕ) : ℝ) := by positivity
  rw [hfac, show 2*(j+1) = 2*j+2 by omega, pow_add]
  have hkey : (1/2) * (x^(2*j) / (((2*j).factorial : ℕ) : ℝ))
      * ((((2*j+1)*(2*j+2) : ℕ) : ℝ) * (((2*j).factorial : ℕ) : ℝ))
      = (1/2) * (x^(2*j) * (((2*j+1)*(2*j+2) : ℕ) : ℝ)) := by
    field_simp
  rw [div_le_iff₀ (by positivity :
    (0:ℝ) < ((((2*j+1)*(2*j+2) : ℕ) : ℝ) * (((2*j).factorial : ℕ) : ℝ))), hkey]
  have hx2 : (0:ℝ) ≤ x^(2*j) := pow_nonneg hx _
  nlinarith [hρ, hcast, hx2]

/-- **Geometric domination of the factorial tail.**  If `2x² ≤ (2N+1)(2N+2)` then the tail
`∑_{j ∈ Icc N K} x^(2j)/(2j)!` is at most twice its first term. -/
lemma geom_factorial_tail (x : ℝ) (hx : 0 ≤ x) (N : ℕ)
    (hρ : 2 * x^2 ≤ (((2*N+1)*(2*N+2) : ℕ) : ℝ)) :
    ∀ K, ∑ j ∈ Finset.Icc N K, x^(2*j) / (((2*j).factorial : ℕ) : ℝ)
      ≤ 2 * (x^(2*N) / (((2*N).factorial : ℕ) : ℝ)) := by
  have hstep : ∀ j, N ≤ j →
      x^(2*(j+1)) / (((2*(j+1)).factorial : ℕ) : ℝ)
        ≤ (1/2) * (x^(2*j) / (((2*j).factorial : ℕ) : ℝ)) :=
    fun j hj => factorial_tail_step x hx N j hj hρ
  have hmain : ∀ K, N ≤ K →
      (∑ j ∈ Finset.Icc N K, x^(2*j) / (((2*j).factorial : ℕ) : ℝ))
        + 2 * (x^(2*(K+1)) / (((2*(K+1)).factorial : ℕ) : ℝ))
      ≤ 2 * (x^(2*N) / (((2*N).factorial : ℕ) : ℝ)) := by
    intro K hK
    induction K, hK using Nat.le_induction with
    | base =>
      rw [Finset.Icc_self, Finset.sum_singleton]
      have h0 := hstep N le_rfl
      linarith
    | succ K hK ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have h0 := hstep (K+1) (by omega)
      linarith
  intro K
  by_cases hK : N ≤ K
  · have h := hmain K hK
    have hnn : 0 ≤ 2 * (x^(2*(K+1)) / (((2*(K+1)).factorial : ℕ) : ℝ)) := by positivity
    linarith
  · push_neg at hK
    have hemp : Finset.Icc N K = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro j hj
      have h1 := (Finset.mem_Icc.mp hj).1
      have h2 := (Finset.mem_Icc.mp hj).2
      omega
    rw [hemp, Finset.sum_empty]
    have hnn : 0 ≤ 2 * (x^(2*N) / (((2*N).factorial : ℕ) : ℝ)) := by positivity
    linarith

/-- `(n/e)^n ≤ n!` for `n ≥ 1` (from Mathlib's `le_factorial_stirling`). -/
lemma pow_div_exp_le_factorial (n : ℕ) (hn : 1 ≤ n) :
    ((n:ℝ) / Real.exp 1)^n ≤ ((n.factorial : ℕ) : ℝ) := by
  have h := Stirling.le_factorial_stirling n
  have h1 : (1:ℝ) ≤ Real.sqrt (2 * Real.pi * (n:ℝ)) := by
    rw [Real.one_le_sqrt]
    have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    nlinarith [Real.pi_gt_three, hn1]
  calc ((n:ℝ) / Real.exp 1)^n = 1 * ((n:ℝ) / Real.exp 1)^n := by ring
    _ ≤ Real.sqrt (2 * Real.pi * (n:ℝ)) * ((n:ℝ) / Real.exp 1)^n :=
        mul_le_mul_of_nonneg_right h1 (pow_nonneg (div_nonneg (Nat.cast_nonneg n) (le_of_lt (Real.exp_pos 1))) n)
    _ ≤ ((n.factorial : ℕ) : ℝ) := h

/-- **Crude numeric estimate.**  For `0 ≤ x ≤ N/2` the `2N`-th factorial tail term is at most
`(3/4)^(2N)` (via `pow_div_exp_le_factorial` and `e/4 ≤ 3/4`). -/
lemma factorial_tail_le_three_quarters (x : ℝ) (hx : 0 ≤ x) (N : ℕ) (hN : 1 ≤ N)
    (hxN : x ≤ (N:ℝ)/2) :
    x^(2*N) / (((2*N).factorial : ℕ) : ℝ) ≤ (3/4)^(2*N) := by
  have hpos : (0:ℝ) < (((2*N).factorial : ℕ) : ℝ) := by positivity
  have hNpos : (0:ℝ) < ((2*N : ℕ) : ℝ) := by positivity
  have hst := pow_div_exp_le_factorial (2*N) (by omega)
  have h1 : x^(2*N) / (((2*N).factorial : ℕ) : ℝ)
      ≤ ((Real.exp 1 * x / ((2*N : ℕ) : ℝ)))^(2*N) := by
    rw [div_le_iff₀ hpos]
    have h2 : ((Real.exp 1 * x / ((2*N : ℕ) : ℝ)))^(2*N) * (((2*N : ℕ) : ℝ)/Real.exp 1)^(2*N)
        = x^(2*N) := by
      rw [← mul_pow]
      congr 1
      field_simp
    calc x^(2*N)
        = ((Real.exp 1 * x / ((2*N : ℕ) : ℝ)))^(2*N) * (((2*N : ℕ) : ℝ)/Real.exp 1)^(2*N) :=
          h2.symm
      _ ≤ ((Real.exp 1 * x / ((2*N : ℕ) : ℝ)))^(2*N) * (((2*N).factorial : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hst (by positivity)
  refine le_trans h1 ?_
  apply pow_le_pow_left₀ (by positivity)
  rw [div_le_iff₀ hNpos]
  have hcast : ((2*N : ℕ) : ℝ) = 2 * (N:ℝ) := by push_cast; ring
  have hxe : Real.exp 1 ≤ 3 := by
    have h := Real.exp_one_lt_d9; linarith
  rw [hcast]
  nlinarith [hxe, hxN, hx, mul_nonneg (sub_nonneg.mpr hxe) hx]

/-! ### Toolbox for the final assembly: injectivity of `List.prod` on decreasing prime lists -/

lemma factorization_list_prod_of_primes (l : List ℕ) (hp : ∀ x ∈ l, x.Prime) (p : ℕ) :
    (l.prod).factorization p = l.count p := by
  induction l with
  | nil => simp
  | cons a as ih =>
    have ha : a.Prime := hp a (by simp)
    have hpa : ∀ x ∈ as, x.Prime := fun x hx => hp x (by simp [hx])
    have hpos : 0 < as.prod := List.prod_pos (fun x hx => (hpa x hx).pos)
    rw [List.prod_cons, Nat.factorization_mul ha.ne_zero (ne_of_gt hpos), Finsupp.add_apply,
      ih hpa]
    have hfac : a.factorization p = if p = a then 1 else 0 := by
      by_cases h : p = a
      · subst h; simpa using ha.factorization_self
      · rw [if_neg h]
        by_contra hc
        exact h (ha.eq_of_factorization_pos hc).symm
    rw [hfac]
    have hcount : (a :: as).count p = (if p = a then 1 else 0) + as.count p := by
      by_cases h : p = a
      · subst h; rw [if_pos rfl, List.count_cons_self]; ring
      · rw [if_neg h, List.count_cons_of_ne (Ne.symm h)]; ring
    rw [hcount]

lemma perm_of_prod_eq_of_primes (l l' : List ℕ) (hp : ∀ x ∈ l, x.Prime)
    (hp' : ∀ x ∈ l', x.Prime) (h : l.prod = l'.prod) : l.Perm l' := by
  rw [List.perm_iff_count]
  intro p
  rw [← factorization_list_prod_of_primes l hp p, h, factorization_list_prod_of_primes l' hp' p]

lemma eq_of_perm_of_pairwise_gt : ∀ (l l' : List ℕ), l.Pairwise (· > ·) → l'.Pairwise (· > ·) →
    l.Perm l' → l = l' := by
  intro l
  induction l with
  | nil => intro l' _ _ h; exact (List.perm_nil.mp h.symm).symm
  | cons a as ih =>
    intro l' hl hl' h
    match l' with
    | [] => exact absurd h (by simp)
    | b :: bs =>
      have hl2 := List.pairwise_cons.mp hl
      have hl2' := List.pairwise_cons.mp hl'
      have hb_le : b ≤ a := by
        have hx : b ∈ (a :: as) := (List.Perm.mem_iff h).mpr (by simp)
        rcases List.mem_cons.mp hx with h1 | h1
        · exact le_of_eq h1
        · exact le_of_lt (hl2.1 b h1)
      have ha_le : a ≤ b := by
        have hx : a ∈ (b :: bs) := (List.Perm.mem_iff h).mp (by simp)
        rcases List.mem_cons.mp hx with h1 | h1
        · exact le_of_eq h1
        · exact le_of_lt (hl2'.1 a h1)
      have hab : a = b := le_antisymm ha_le hb_le
      subst hab
      rw [List.perm_cons] at h
      rw [ih bs hl2.2 hl2'.2 h]

lemma prod_injective_of_prime_pairwise_gt {c c' : List ℕ}
    (hc : c.Pairwise (· > ·)) (hc' : c'.Pairwise (· > ·))
    (hp : ∀ x ∈ c, x.Prime) (hp' : ∀ x ∈ c', x.Prime)
    (h : c.prod = c'.prod) : c = c' :=
  eq_of_perm_of_pairwise_gt c c' hc hc' (perm_of_prod_eq_of_primes c c' hp hp' h)

/-! ### `VsieveOdd`/`Vodd` are at most one; `cut` is positive, decreasing and eventually `< Z` -/

lemma VsieveOdd_le_one (M : ℕ) : VsieveOdd M ≤ 1 := by
  unfold VsieveOdd
  refine Finset.prod_le_one₀ (fun p hp => (oneSubInvPred_mem_Icc (Finset.mem_filter.mp hp).2.2).1)
    (fun p hp => (oneSubInvPred_mem_Icc (Finset.mem_filter.mp hp).2.2).2)

lemma Vodd_le_one (z : ℝ) : Vodd z ≤ 1 := by
  rw [← VsieveOdd_eq_Vodd]; exact VsieveOdd_le_one _

lemma cut_pos {y : ℝ} (hy : 0 < y) (j : ℕ) : 0 < cut y j := Real.rpow_pos_of_pos hy _

lemma cut_one (y : ℝ) : cut y 1 = y ^ sieveAlpha := by
  unfold cut; rw [pow_one]

lemma cut_anti {y : ℝ} (hy : 1 < y) {j k : ℕ} (h : j ≤ k) : cut y k ≤ cut y j := by
  unfold cut
  refine Real.rpow_le_rpow_of_exponent_le (le_of_lt hy) ?_
  exact pow_le_pow_of_le_one (by rw [sieveAlpha]; norm_num) (by rw [sieveAlpha]; norm_num) h

/-- The top level `y^α` is at most `y - 1` once `y ≥ 8`. -/
lemma cut_one_le_sub_one {y : ℝ} (hy : 8 ≤ y) : cut y 1 ≤ y - 1 := by
  have hy0 : (0:ℝ) < y := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hly : (1000/401 : ℝ) * Real.log 2 ≤ Real.log y := by
    have h1 : Real.log 8 ≤ Real.log y := Real.log_le_log (by norm_num) hy
    have h2 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]; push_cast; ring
    rw [h2] at h1; nlinarith
  have hexp : Real.log 2 ≤ (401/1000 : ℝ) * Real.log y := by nlinarith
  have hpow : (2:ℝ) ≤ y ^ ((401:ℝ)/1000) := by
    rw [Real.rpow_def_of_pos hy0]
    calc (2:ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (Real.log y * (401/1000 : ℝ)) := Real.exp_le_exp.mpr (by linarith)
  rw [cut_one, show sieveAlpha = 1 - 401/1000 by rw [sieveAlpha]; norm_num,
    Real.rpow_sub hy0 (1:ℝ) (401/1000), Real.rpow_one]
  have hpos : 0 < y ^ ((401:ℝ)/1000) := Real.rpow_pos_of_pos hy0 _
  rw [div_le_iff₀ hpos]
  nlinarith

/-- Some level index at which the cut has dropped below `Z`. -/
lemma exists_cut_lt {y Z : ℝ} (hy : 1 < y) (hZ : 1 < Z) : ∃ J : ℕ, cut y (J+1) < Z := by
  have hy0 : (0:ℝ) < y := by linarith
  have hly : 0 < Real.log y := Real.log_pos hy
  have hlZ : 0 < Real.log Z := Real.log_pos hZ
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show (0:ℝ) < Real.log Z / Real.log y by positivity)
    (by norm_num : ((4:ℝ)/5) < 1)
  refine ⟨n, ?_⟩
  have hsα : sieveAlpha ^ n ≤ ((4:ℝ)/5)^n :=
    pow_le_pow_left₀ (by rw [sieveAlpha]; norm_num) (by rw [sieveAlpha]; norm_num) n
  have h1 : sieveAlpha ^ (n+1) ≤ sieveAlpha ^ n :=
    pow_le_pow_of_le_one (by rw [sieveAlpha]; norm_num) (by rw [sieveAlpha]; norm_num)
      (Nat.le_succ n)
  have hexp : sieveAlpha ^ (n+1) * Real.log y < Real.log Z := by
    calc sieveAlpha ^ (n+1) * Real.log y ≤ sieveAlpha ^ n * Real.log y :=
          mul_le_mul_of_nonneg_right h1 (le_of_lt hly)
      _ ≤ ((4:ℝ)/5)^n * Real.log y := mul_le_mul_of_nonneg_right hsα (le_of_lt hly)
      _ < (Real.log Z / Real.log y) * Real.log y := mul_lt_mul_of_pos_right hn hly
      _ = Real.log Z := by field_simp
  have hxpos : (0:ℝ) < cut y (n+1) := cut_pos hy0 _
  have hlog : Real.log (cut y (n+1)) < Real.log Z := by
    unfold cut
    rw [Real.log_rpow hy0]
    exact hexp
  exact (Real.log_lt_log_iff hxpos (show (0:ℝ) < Z by linarith)).mp hlog

/-! ### Pointwise and summed bounds for the crude (`cut < Z`) range -/

lemma V2T_le_factorial_term (y : ℝ) (hy : 1 < y) (j M : ℕ) (hj : 1 ≤ j) (hM : 1 ≤ M)
    (hcut0 : 0 ≤ cut y j) (hcut : cut y j ≤ (M:ℝ) - 1) :
    V2T y j M ≤ (Real.log (1 / VsieveOdd M))^(2*j) / ((2*j).factorial : ℝ) := by
  have hVs : VsieveOdd (⌊cut y j⌋₊ + 1) ≤ 1 := VsieveOdd_le_one _
  have hVodd1 : Vodd (cut y j) ≤ 1 := by rw [← VsieveOdd_eq_Vodd]; exact hVs
  have hVsM : 0 < VsieveOdd M := VsieveOdd_pos M
  have hT := T_le_log_ratio y j M hM hcut0 hcut
  have hT' : (∑ p ∈ (oddLt M).filter (fun q : ℕ => cut y j < (q:ℝ)), ((p:ℝ)-1)⁻¹)
      ≤ Real.log (1 / VsieveOdd M) := by
    rw [← VsieveOdd_eq_Vodd_pred M hM] at hT
    have hA : Vodd (cut y j) / VsieveOdd M ≤ 1 / VsieveOdd M :=
      div_le_div_of_nonneg_right hVodd1 (le_of_lt hVsM)
    exact le_trans hT (Real.log_le_log (div_pos (Vodd_pos _) hVsM) hA)
  have hTnn : 0 ≤ ∑ p ∈ (oddLt M).filter (fun q : ℕ => cut y j < (q:ℝ)), ((p:ℝ)-1)⁻¹ := by
    refine Finset.sum_nonneg (fun p hp => ?_)
    rw [Finset.mem_filter, oddLt, Finset.mem_filter, Finset.mem_range] at hp
    exact inv_nonneg.mpr (by have h2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.1.2.1.two_le
                             linarith)
  have hpow : (∑ p ∈ (oddLt M).filter (fun q : ℕ => cut y j < (q:ℝ)), ((p:ℝ)-1)⁻¹)^(2*j)
      ≤ (Real.log (1 / VsieveOdd M))^(2*j) := pow_le_pow_left₀ hTnn hT' (2*j)
  have hfact : (0:ℝ) < (((2*j).factorial : ℕ) : ℝ) := by positivity
  refine le_trans (V2T_bound y (le_of_lt hy) j M hj) ?_
  have hD := div_le_div_of_nonneg_right hpow (le_of_lt hfact)
  have hstep : VsieveOdd (⌊cut y j⌋₊ + 1) *
        ((∑ p ∈ (oddLt M).filter (fun q : ℕ => cut y j < (q:ℝ)), ((p:ℝ)-1)⁻¹)^(2*j)
          / ((2*j).factorial : ℝ))
      ≤ 1 * ((Real.log (1 / VsieveOdd M))^(2*j) / ((2*j).factorial : ℝ)) :=
    mul_le_mul hVs hD (by positivity) (by norm_num)
  simpa using hstep

lemma crude_sum_le (y : ℝ) (hy : 1 < y) (M J : ℕ) (hM : 1 ≤ M)
    (hcut0 : ∀ j ∈ Finset.Icc (J+1) M, 0 ≤ cut y j)
    (hcut : ∀ j ∈ Finset.Icc (J+1) M, cut y j ≤ (M:ℝ) - 1)
    (hρ : 2 * (Real.log (1 / VsieveOdd M))^2 ≤ (((2*(J+1)+1)*(2*(J+1)+2) : ℕ) : ℝ)) :
    ∑ j ∈ Finset.Icc (J+1) M, V2T y j M
      ≤ 2 * ((Real.log (1 / VsieveOdd M))^(2*(J+1)) / (((2*(J+1)).factorial : ℕ) : ℝ)) := by
  have hV := VsieveOdd_pos M
  have hTB : 0 ≤ Real.log (1 / VsieveOdd M) :=
    Real.log_nonneg ((one_le_div hV).mpr (VsieveOdd_le_one M))
  have hpt : ∀ j ∈ Finset.Icc (J+1) M, V2T y j M
      ≤ (Real.log (1 / VsieveOdd M))^(2*j) / ((2*j).factorial : ℝ) := by
    intro j hj
    have hj1 : 1 ≤ j := by have := (Finset.mem_Icc.mp hj).1; omega
    exact V2T_le_factorial_term y hy j M hj1 hM (hcut0 j hj) (hcut j hj)
  refine le_trans (Finset.sum_le_sum hpt) ?_
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc le_rfl (le_max_left M (J+1)))
    (fun x _ _ => div_nonneg (pow_nonneg hTB _) (by positivity))) ?_
  exact geom_factorial_tail (Real.log (1 / VsieveOdd M)) hTB (J+1) hρ (max M (J+1))

/-- **`Bnd` decomposition.**  `Bnd y 1 M` splits into the sharp range `1 … J` (bounded by the
series collapse) and the crude range `J+1 … M` (bounded by the factorial tail). -/
lemma Bnd_le_sharp_plus_crude (y : ℝ) (hy : 1 < y) (M J : ℕ) (hM : 1 ≤ M) (hJM : J ≤ M)
    {Z L δ : ℝ}
    (hL : 0 < L) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hZ3 : 3 ≤ Z)
    (hZ : ∀ z : ℝ, Z ≤ z → (1-δ)*L ≤ Real.log z * Vodd z ∧ Real.log z * Vodd z ≤ (1+δ)*L)
    (hZc : ∀ j ∈ Finset.Icc 1 J, Z ≤ cut y j)
    (hZM : Z ≤ (M:ℝ) - 1)
    (hcutM : ∀ j ∈ Finset.Icc 1 J, cut y j ≤ (M:ℝ) - 1)
    (hcut0 : ∀ j ∈ Finset.Icc 1 J, 0 ≤ cut y j)
    (hlogM : Real.log ((M:ℝ) - 1) ≤ (1 + δ) * Real.log y)
    (hε1 : Real.log ((1+δ)/(1-δ)) + Real.log (1+δ) ≤ 7/1000)
    (hcutc0 : ∀ j ∈ Finset.Icc (J+1) M, 0 ≤ cut y j)
    (hcutc : ∀ j ∈ Finset.Icc (J+1) M, cut y j ≤ (M:ℝ) - 1)
    (hρ : 2 * (Real.log (1 / VsieveOdd M))^2 ≤ (((2*(J+1)+1)*(2*(J+1)+2) : ℕ) : ℝ)) :
    Bnd y 1 M ≤ ((1+δ)/(1-δ)) * (1+δ) * VsieveOdd M * (5/6)
      + 2 * ((Real.log (1 / VsieveOdd M))^(2*(J+1)) / (((2*(J+1)).factorial : ℕ) : ℝ)) := by
  rw [Bnd_eq_Icc y M hM]
  have hunion : Finset.Icc 1 J ∪ Finset.Icc (J+1) M = Finset.Icc 1 M := by
    ext k; simp only [Finset.mem_union, Finset.mem_Icc]; omega
  have hdisj : Disjoint (Finset.Icc 1 J) (Finset.Icc (J+1) M) :=
    Finset.disjoint_left.mpr (fun x hx1 hx2 => by
      simp only [Finset.mem_Icc] at hx1 hx2; omega)
  rw [← hunion, Finset.sum_union hdisj]
  exact add_le_add
    (V2T_sharp_sum y hy M J hM hL hδ0 hδ1 hZ3 hZ hZc hZM hcutM hcut0 hlogM hε1)
    (crude_sum_le y hy M J hM hcutc0 hcutc hρ)

/-! ### The factorial tail estimate for the crude range -/

/-- Stirling: `T^(2N)/(2N)! ≤ (e T/(2N))^(2N)`. -/
lemma factorial_tail_stirling (T : ℝ) (hT : 0 ≤ T) (N : ℕ) (hN : 1 ≤ N) :
    T^(2*N) / (((2*N).factorial : ℕ) : ℝ)
      ≤ (Real.exp 1 * T / (((2*N : ℕ) : ℝ)))^(2*N) := by
  have hpos : (0:ℝ) < (((2*N).factorial : ℕ) : ℝ) := by positivity
  have hNpos : (0:ℝ) < ((2*N : ℕ) : ℝ) := by positivity
  have hst := pow_div_exp_le_factorial (2*N) (by omega)
  rw [div_le_iff₀ hpos]
  have h2 : ((Real.exp 1 * T / ((2*N : ℕ) : ℝ)))^(2*N) * (((2*N : ℕ) : ℝ)/Real.exp 1)^(2*N)
      = T^(2*N) := by
    rw [← mul_pow]
    congr 1
    field_simp
  calc T^(2*N)
      = ((Real.exp 1 * T / ((2*N : ℕ) : ℝ)))^(2*N)
          * (((2*N : ℕ) : ℝ)/Real.exp 1)^(2*N) := h2.symm
    _ ≤ ((Real.exp 1 * T / ((2*N : ℕ) : ℝ)))^(2*N) * (((2*N).factorial : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hst (by positivity)

lemma crude_tail_small (T_B V : ℝ) (N : ℕ) (hN : 1 ≤ N) (hTB0 : 0 ≤ T_B)
    (hTB : Real.exp 1 * T_B ≤ (71/100) * ((2*N : ℕ) : ℝ))
    (h3 : 2 * ((71:ℝ)/100)^(2*N) ≤ V/20) :
    2 * (T_B^(2*N) / (((2*N).factorial : ℕ) : ℝ)) ≤ V/20 := by
  have h := factorial_tail_stirling T_B hTB0 N hN
  have h2 : ((Real.exp 1 * T_B) / (((2*N : ℕ) : ℝ)))^(2*N) ≤ ((71:ℝ)/100)^(2*N) := by
    apply pow_le_pow_left₀ (by positivity)
    rw [div_le_iff₀ (by positivity : (0:ℝ) < ((2*N : ℕ) : ℝ))]
    linarith
  have h3' : 2 * (T_B^(2*N) / (((2*N).factorial : ℕ) : ℝ)) ≤ 2 * ((71:ℝ)/100)^(2*N) :=
    mul_le_mul_of_nonneg_left (le_trans h h2) (by norm_num)
  linarith

lemma exp_sixty_eight_ge : Real.exp (68/100 : ℝ) ≤ 10000/5041 := by
  have hb := Real.exp_bound' (x := (68:ℝ)/100) (by norm_num) (by norm_num) (n := 4) (by norm_num)
  have hsum : ∑ m ∈ Finset.range 4, ((68:ℝ)/100)^m / ((m.factorial:ℕ):ℝ)
      + ((68:ℝ)/100)^4 * 5 / ((((4:ℕ).factorial:ℕ):ℝ) * 4) ≤ (10000:ℝ)/5041 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  linarith

/-- `(7/10)^(2n) ≤ exp(-(71/100) n)`. -/
lemma sev_one_pow_le_exp (n : ℕ) : ((71:ℝ)/100)^(2*n) ≤ Real.exp (-((68:ℝ)/100 * n)) := by
  have hlog : (68:ℝ)/100 ≤ Real.log (10000/5041) := by
    rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 10000/5041)]
    exact exp_sixty_eight_ge
  have h1 : ((71:ℝ)/100)^(2*n) = ((10000:ℝ)/5041)⁻¹ ^ n := by
    rw [show ((71:ℝ)/100)^(2*n) = (((71:ℝ)/100)^2)^n by rw [← pow_mul]]
    norm_num
  rw [h1, ← Real.exp_log (by positivity : (0:ℝ) < ((10000:ℝ)/5041)⁻¹), ← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  rw [Real.log_inv]
  have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  nlinarith [hlog, hn]

lemma crude_tail_exp_small {V τ c₁ L : ℝ} {N : ℕ}
    (hV : (1 - (1/1000)) * L * Real.exp (-τ) ≤ V)
    (hN2 : (2000/513) * (τ - c₁) ≤ ((2*N : ℕ) : ℝ))
    (hX : 40 * Real.exp ((132/100) * c₁ - (32/100) * τ) ≤ (1 - (1/1000)) * L) :
    2 * ((71:ℝ)/100)^(2*N) ≤ V/20 := by
  have h1 := sev_one_pow_le_exp N
  have h2 : - ((68:ℝ)/100 * (N:ℝ)) ≤ -((132/100) * (τ - c₁)) := by
    have h3 : ((2*N : ℕ) : ℝ) = 2 * (N:ℝ) := by push_cast; ring
    rw [h3] at hN2
    nlinarith [hN2]
  have h3 : Real.exp (- ((68:ℝ)/100 * (N:ℝ))) ≤ Real.exp (-((132/100)*(τ - c₁))) :=
    Real.exp_le_exp.mpr h2
  have h4 : Real.exp (-((132/100)*(τ - c₁))) =
      Real.exp ((132/100)*c₁ - (32/100)*τ) * Real.exp (-τ) := by
    rw [← Real.exp_add]; congr 1; ring
  have hXe : 0 < Real.exp (-τ) := Real.exp_pos _
  have h5 : 2 * ((71:ℝ)/100)^(2*N)
      ≤ 2 * (Real.exp ((132/100)*c₁ - (32/100)*τ) * Real.exp (-τ)) := by
    refine le_trans (mul_le_mul_of_nonneg_left (le_trans h1 h3) (by norm_num)) ?_
    rw [← h4]
  have h6 : 40 * Real.exp ((132/100)*c₁ - (32/100)*τ) * Real.exp (-τ) ≤
      ((1 - (1/1000)) * L) * Real.exp (-τ) :=
    mul_le_mul_of_nonneg_right hX (le_of_lt hXe)
  have h7 : 2 * (Real.exp ((132/100)*c₁ - (32/100)*τ) * Real.exp (-τ)) ≤ V/20 := by
    nlinarith [hV, h6, hXe]
  linarith [h5, h7]

/-! ### The sieve assembly: primes `p` with `p + 2` coprime to the primorial -/

/-- `θ_d(x) = Σ_{p ≤ x, p prime, d ∣ p + 2} log p`. -/
noncomputable def thetaD (x d : ℕ) : ℝ :=
  ((Finset.range (x + 1)).filter (fun p : ℕ => p.Prime ∧ d ∣ p + 2)).sum
    (fun p => Real.log (p : ℝ))

/-- the sieve remainder `θ_d(x) - x/φ(d)`. -/
noncomputable def rD (x d : ℕ) : ℝ := thetaD x d - (x : ℝ) / (Nat.totient d : ℝ)

/-- `Σ_{p ≤ x, p prime} log p · 1_{(p+2, oddPrimLt M) = 1}`. -/
noncomputable def goodSum (x M : ℕ) : ℝ :=
  ((Finset.range (x + 1)).filter (fun p : ℕ => p.Prime)).sum
    (fun p => Real.log (p : ℝ) * Id (p + 2) M)

/-- the target sum: primes `p ≤ x` with `p + 2` coprime to the primorial of `a`. -/
noncomputable def targetSum (x a : ℕ) : ℝ :=
  ((Finset.range (x + 1)).filter
    (fun p : ℕ => p.Prime ∧ Nat.Coprime (p + 2) (primorial a))).sum
      (fun p => Real.log (p : ℝ))

lemma thetaD_eq (x d : ℕ) :
    thetaD x d = ((Finset.range (x + 1)).filter (fun p : ℕ => p.Prime)).sum
      (fun p => Real.log (p : ℝ) * (if d ∣ p + 2 then 1 else 0)) := by
  unfold thetaD
  rw [← Finset.filter_filter (fun p : ℕ => p.Prime) (fun p : ℕ => d ∣ p + 2)
        (Finset.range (x + 1)), Finset.sum_filter]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  by_cases h : d ∣ p + 2 <;> simp [h]

lemma chain_theta_eq (x M : ℕ) (y : ℝ) :
    (loChain y 1 M).sum (fun c => (-1:ℝ)^c.length * thetaD x c.prod)
      = ((Finset.range (x + 1)).filter (fun p : ℕ => p.Prime)).sum
          (fun p => Real.log (p : ℝ) * Rlo y 1 M (p + 2)) := by
  have h1 : ∀ c : List ℕ, (-1:ℝ)^c.length * thetaD x c.prod
      = ((Finset.range (x + 1)).filter (fun p : ℕ => p.Prime)).sum
          (fun p => Real.log (p : ℝ) * ((-1:ℝ)^c.length * (if c.prod ∣ p + 2 then 1 else 0))) := by
    intro c
    rw [thetaD_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p hp => by ring)
  rw [Finset.sum_congr rfl (fun c hc => h1 c), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [Rlo, Finset.mul_sum]

lemma goodSum_ge_chain (x M : ℕ) (y : ℝ) (hy : 3 ≤ y) :
    (loChain y 1 M).sum (fun c => (-1:ℝ)^c.length * thetaD x c.prod) ≤ goodSum x M := by
  rw [chain_theta_eq]
  unfold goodSum
  refine Finset.sum_le_sum (fun p hp => ?_)
  have hlog : 0 ≤ Real.log (p:ℝ) := by
    refine Real.log_nonneg ?_
    have h2 : 1 ≤ p := le_trans (by norm_num : 1 ≤ 2) (Finset.mem_filter.mp hp).2.two_le
    exact_mod_cast h2
  have hb := (chain_bounds y hy M).1 (p + 2) 1 (by norm_num)
  exact mul_le_mul_of_nonneg_left hb hlog

lemma chain_theta_main_error (x M : ℕ) (y : ℝ) :
    (loChain y 1 M).sum (fun c => (-1:ℝ)^c.length * thetaD x c.prod)
      = (x:ℝ) * Elo y 1 M
        + (loChain y 1 M).sum (fun c => (-1:ℝ)^c.length * rD x c.prod) := by
  have h : ∀ c : List ℕ, (-1:ℝ)^c.length * thetaD x c.prod
      = (x:ℝ) * ((-1:ℝ)^c.length / (Nat.totient c.prod : ℝ))
        + (-1:ℝ)^c.length * rD x c.prod := by
    intro c; unfold rD; ring
  rw [Finset.sum_congr rfl (fun c hc => h c), Finset.sum_add_distrib]
  congr 1
  unfold Elo
  rw [Finset.mul_sum]

lemma odd_list_prod : ∀ (l : List ℕ), (∀ x ∈ l, x % 2 = 1) → l.prod % 2 = 1 := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a as ih =>
    intro h
    have ha : a % 2 = 1 := h a (by simp)
    have has : ∀ x ∈ as, x % 2 = 1 := fun x hx => h x (by simp [hx])
    rw [List.prod_cons, Nat.mul_mod, ha, ih has]

lemma odd_finset_prod {s : Finset ℕ} (h : ∀ x ∈ s, x % 2 = 1) :
    (∏ x ∈ s, x) % 2 = 1 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Nat.mul_mod, h a (Finset.mem_insert_self a s),
      ih (fun x hx => h x (Finset.mem_insert_of_mem hx))]

lemma oddPrimLt_odd (M : ℕ) : oddPrimLt M % 2 = 1 := by
  rw [oddPrimLt_eq_prod_oddLt]
  refine odd_finset_prod (fun p hp => ?_)
  have hp' := Finset.mem_filter.mp hp
  rcases hp'.2.1.eq_two_or_odd with h | h
  · have := hp'.2.2; omega
  · exact h

lemma sum_abs_chain_eq (x M : ℕ) (y : ℝ) :
    (loChain y 1 M).sum (fun c => |rD x c.prod|)
      = ((loChain y 1 M).image (fun c => c.prod)).sum (fun d => |rD x d|) := by
  rw [Finset.sum_image]
  intro c hc c' hc' h
  have h1 := (mem_loChain_iff' y M 1 c).mp hc
  have h2 := (mem_loChain_iff' y M 1 c').mp hc'
  exact prod_injective_of_prime_pairwise_gt h1.1 h2.1
    (fun x hx => (Finset.mem_filter.mp (h1.2.1 x hx)).2.1)
    (fun x hx => (Finset.mem_filter.mp (h2.2.1 x hx)).2.1) h

lemma abs_chain_rD_le (x M D : ℕ) (y : ℝ) (hy : 1 < y) (hM : M ≤ ⌊y⌋₊ + 1)
    (hD : y ^ ((399:ℝ)/100) ≤ (D:ℝ)) :
    |(loChain y 1 M).sum (fun c => (-1:ℝ)^c.length * rD x c.prod)|
      ≤ ((Finset.Icc 1 D).filter (fun d : ℕ => d % 2 = 1)).sum (fun d => |rD x d|) := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have h1 : ∀ c : List ℕ, |(-1:ℝ)^c.length * rD x c.prod| = |rD x c.prod| := by
    intro c
    rw [abs_mul, abs_pow]
    simp
  rw [Finset.sum_congr rfl (fun c hc => h1 c), sum_abs_chain_eq]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun d hd hnd => abs_nonneg _)
  intro d hd
  rw [Finset.mem_image] at hd
  obtain ⟨c, hc, rfl⟩ := hd
  have hcf := (mem_loChain_iff' y M 1 c).mp hc
  rw [Finset.mem_filter, Finset.mem_Icc]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact List.one_le_prod (fun x hx => (Finset.mem_filter.mp (hcf.2.1 x hx)).2.1.one_le)
  · have := loChain_prod_le y hy M hM c hc
    exact_mod_cast le_trans this hD
  · refine odd_list_prod _ (fun x hx => ?_)
    have hxp := (Finset.mem_filter.mp (hcf.2.1 x hx)).2.1
    rcases hxp.eq_two_or_odd with h | h
    · have := (Finset.mem_filter.mp (hcf.2.1 x hx)).2.2
      omega
    · exact h

/-- `primorial a = 2 · oddPrimLt (a+1)` for `a ≥ 2`. -/
lemma primorial_eq_two_mul_oddPrimLt (a : ℕ) (ha : 2 ≤ a) :
    primorial a = 2 * oddPrimLt (a + 1) := by
  have h2 : (2:ℕ) ∈ Nat.primesLE a := Nat.mem_primesLE.mpr ⟨ha, Nat.prime_two⟩
  have hnotmem : (2:ℕ) ∉ (Nat.primesLE a).filter (fun q : ℕ => q ≠ 2) := by
    rw [Finset.mem_filter]; simp
  have hins : Nat.primesLE a = insert 2 ((Nat.primesLE a).filter (fun q : ℕ => q ≠ 2)) := by
    ext q; simp only [Finset.mem_insert, Finset.mem_filter]
    constructor
    · intro hq; by_cases h : q = 2
      · exact Or.inl h
      · exact Or.inr ⟨hq, h⟩
    · rintro (rfl | ⟨hq, _⟩)
      · exact h2
      · exact hq
  have hprod : (∏ p ∈ Nat.primesLE a, p)
      = 2 * (∏ p ∈ (Nat.primesLE a).filter (fun q : ℕ => q ≠ 2), p) := by
    conv_lhs => rw [hins]
    rw [Finset.prod_insert hnotmem]
  have hset : (Nat.primesLE a).filter (fun q : ℕ => q ≠ 2)
      = oddLt (a + 1) := by
    rw [oddLt]
    ext p
    simp only [Finset.mem_filter, Nat.mem_primesLE, Finset.mem_range]
    constructor
    · rintro ⟨⟨hp, hpp⟩, hp2⟩
      refine ⟨Nat.lt_succ_iff.mpr hp, hpp, ?_⟩
      rcases hpp.eq_two_or_odd with h | h
      · exact absurd h hp2
      · have := hpp.two_le; omega
    · rintro ⟨h1, hpp, h3⟩
      exact ⟨⟨Nat.lt_succ_iff.mp h1, hpp⟩, by rintro rfl; omega⟩
  rw [primorial_eq_prod_primesLE, hprod, oddPrimLt_eq_prod_oddLt, hset]

/-- `4` is coprime to the odd primorial. -/
lemma coprime_four_oddPrimLt (M : ℕ) : Nat.Coprime 4 (oddPrimLt M) := by
  have hodd : Odd (oddPrimLt M) := Nat.odd_iff.mpr (oddPrimLt_odd M)
  have h : Nat.Coprime (2:ℕ) (oddPrimLt M) := Nat.coprime_two_left.mpr hodd
  simpa using Nat.Coprime.pow_left 2 h

/-- For a prime `p ≠ 2`, `p + 2` is coprime to `2`. -/
lemma coprime_add_two_two_of_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Nat.Coprime (p + 2) 2 := by
  rw [Nat.coprime_two_right, Nat.odd_iff]
  rcases hp.eq_two_or_odd with h | h
  · exact absurd h hp2
  · have hp2' := hp.two_le
    have : (p + 2) % 2 = p % 2 := by omega
    omega

lemma not_coprime_four_two_mul (L : ℕ) : ¬ Nat.Coprime (2 + 2) (2 * L) := by
  rw [Nat.coprime_mul_iff_right]
  exact fun h => absurd (Nat.odd_iff.mp (Nat.coprime_two_right.mp h.1)) (by norm_num)

/-- **The good sum vs. the target sum.**  Adding the prime `2` (which `goodSum` counts and
`targetSum` does not) accounts exactly for `log 2`. -/
lemma goodSum_eq_targetSum_add (x a : ℕ) (ha : 2 ≤ a) (hx : 2 ≤ x) :
    goodSum x (a + 1) = targetSum x a + Real.log 2 := by
  set P : Finset ℕ := (Finset.range (x + 1)).filter (fun p : ℕ => p.Prime) with hP
  have h2P : (2:ℕ) ∈ P := by
    rw [hP, Finset.mem_filter]
    exact ⟨Finset.mem_range.mpr (by omega), Nat.prime_two⟩
  have hts : targetSum x a
      = ∑ p ∈ P, (if Nat.Coprime (p + 2) (2 * oddPrimLt (a+1)) then Real.log (p:ℝ) else 0) := by
    unfold targetSum
    rw [primorial_eq_two_mul_oddPrimLt a ha,
      ← Finset.filter_filter (fun p : ℕ => p.Prime)
        (fun p : ℕ => Nat.Coprime (p + 2) (2 * oddPrimLt (a+1))) (Finset.range (x+1)),
      hP, Finset.sum_filter]
  rw [hts, goodSum, hP]
  have hpt : ∀ p ∈ P, Real.log (p:ℝ) * Id (p + 2) (a + 1)
      = (if Nat.Coprime (p + 2) (2 * oddPrimLt (a+1)) then Real.log (p:ℝ) else 0)
        + (if p = 2 then Real.log 2 else 0) := by
    intro p hp
    have hpp : p.Prime := (Finset.mem_filter.mp hp).2
    unfold Id
    by_cases hp2 : p = 2
    · subst hp2
      rw [if_pos (coprime_four_oddPrimLt (a+1)),
        if_neg (not_coprime_four_two_mul (oddPrimLt (a+1))), if_pos rfl]
      ring
    · by_cases hC : Nat.Coprime (p + 2) (oddPrimLt (a + 1))
      · have hC2 : Nat.Coprime (p + 2) (2 * oddPrimLt (a + 1)) :=
          Nat.coprime_mul_iff_right.mpr ⟨coprime_add_two_two_of_prime hpp hp2, hC⟩
        rw [if_pos hC2, if_pos hC, if_neg (by rintro rfl; exact hp2 rfl)]
        ring
      · have hC2 : ¬ Nat.Coprime (p + 2) (2 * oddPrimLt (a + 1)) := fun h =>
          hC (Nat.coprime_mul_iff_right.mp h).2
        rw [if_neg hC2, if_neg hC, if_neg (by rintro rfl; exact hp2 rfl)]
        ring
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib]
  have hsum2 : (∑ p ∈ P, if p = 2 then Real.log 2 else 0) = Real.log 2 := by
    rw [Finset.sum_ite_eq', if_pos h2P]
  rw [hsum2]

/-- **The lower bound for the chain Euler product.** -/
lemma Elo_ge_twelfth (y : ℝ) (M : ℕ) (hBnd : Bnd y 1 M ≤ (11/12) * VsieveOdd M) :
    (1/12) * VsieveOdd M ≤ Elo y 1 M := by
  have h1 := VioFrom_eq y M 1
  have h2 := abs_VioFrom_le_Bnd y M 1
  have h3 : VioFrom y 1 M ≤ (11/12) * VsieveOdd M :=
    le_trans (le_abs_self _) (le_trans h2 hBnd)
  linarith [h1, h3]

/-! ### Eventual largeness of the sieve parameters -/

lemma eventually_rpow_one_eighth_ge (T : ℝ) :
    ∀ᶠ x : ℕ in Filter.atTop, T ≤ Real.rpow (x : ℝ) (1/8) := by
  have h : Filter.Tendsto (fun x : ℕ => Real.rpow (x : ℝ) (1/8)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/8)).comp tendsto_natCast_atTop_atTop
  exact h.eventually (Filter.eventually_ge_atTop T)

lemma eventually_loglog_large (T : ℝ) :
    ∀ᶠ x : ℕ in Filter.atTop,
      T ≤ Real.log (Real.log (Real.rpow (x : ℝ) (1/8))) := by
  have h1 : Filter.Tendsto (fun x : ℕ => Real.rpow (x : ℝ) (1/8)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/8)).comp tendsto_natCast_atTop_atTop
  have h : Filter.Tendsto (fun x : ℕ => Real.log (Real.log (Real.rpow (x : ℝ) (1/8))))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp h1)
  exact h.eventually (Filter.eventually_ge_atTop T)

lemma eventually_log_le_rpow_mul {c : ℝ} (hc : 0 < c) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ x : ℕ in Filter.atTop, Real.log (x : ℝ) ≤ c * (x : ℝ)^r := by
  have h1 : ∀ᶠ x : ℝ in Filter.atTop, Real.log x ≤ c * x ^ r := by
    have h2 : ∀ᶠ x : ℝ in Filter.atTop, ‖Real.log x‖ ≤ c * ‖x ^ r‖ :=
      (isLittleO_log_rpow_atTop hr).def hc
    filter_upwards [h2, Filter.eventually_ge_atTop (1:ℝ)] with x hx hx1
    have hxr : (0:ℝ) ≤ x ^ r := Real.rpow_nonneg (by linarith) _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hxr] at hx
    exact le_trans (le_abs_self _) hx
  exact tendsto_natCast_atTop_atTop.eventually h1

lemma eventually_log_pow_le_quarter_rpow {B : ℝ} (hB : 0 < B) :
    ∀ᶠ x : ℕ in Filter.atTop,
      (Real.log (x : ℝ))^B ≤ (1/4) * (x : ℝ) ^ ((800:ℝ)⁻¹) := by
  have hc : (0:ℝ) < (1/4) ^ B⁻¹ := Real.rpow_pos_of_pos (by norm_num) _
  have h1 := eventually_log_le_rpow_mul hc (r := (800*B)⁻¹) (by positivity)
  filter_upwards [h1, Filter.eventually_ge_atTop (2:ℕ)] with x hx hx2
  have hBne : B ≠ 0 := ne_of_gt hB
  have hx1 : (1:ℝ) ≤ (x:ℝ) := by
    exact_mod_cast (le_trans (by norm_num : (1:ℕ) ≤ 2) hx2)
  have hxpos : (0:ℝ) < (x:ℝ) := by linarith
  have hlogpos : 0 ≤ Real.log (x:ℝ) := Real.log_nonneg hx1
  have h4 := Real.rpow_le_rpow hlogpos hx (le_of_lt hB)
  rw [Real.mul_rpow (le_of_lt hc) (Real.rpow_nonneg (le_of_lt hxpos) _),
    ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ (1/4 : ℝ)) B⁻¹ B,
    ← Real.rpow_mul (le_of_lt hxpos) ((800*B)⁻¹) B,
    show B⁻¹ * B = (1:ℝ) by field_simp, Real.rpow_one,
    show (800*B)⁻¹ * B = (800:ℝ)⁻¹ by field_simp] at h4
  exact h4

lemma eventually_D_ge_rpow {B : ℝ} (hB : 0 < B) :
    ∀ᶠ x : ℕ in Filter.atTop,
      Real.rpow (x : ℝ) (1/8) ^ ((399:ℝ)/100)
        ≤ (⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊ : ℝ) := by
  filter_upwards [eventually_log_pow_le_quarter_rpow hB, Filter.eventually_ge_atTop (2:ℕ)]
    with x hlog hx2
  have hx1 : (1:ℝ) ≤ (x:ℝ) := by
    exact_mod_cast (le_trans (by norm_num : (1:ℕ) ≤ 2) hx2)
  have hx2' : (2:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx2
  have hxpos : (0:ℝ) < (x:ℝ) := by linarith
  have hlogx : 0 < Real.log (x:ℝ) := Real.log_pos (by linarith)
  have hlogB : 0 < (Real.log (x:ℝ))^B := Real.rpow_pos_of_pos hlogx B
  have hfund : (x:ℝ) ^ ((399:ℝ)/800)
      ≤ Real.sqrt (x:ℝ) / (Real.log (x:ℝ))^B - 1 := by
    have hp : (x:ℝ) ^ ((399:ℝ)/800) * (x:ℝ) ^ ((800:ℝ)⁻¹) = (x:ℝ) ^ ((1:ℝ)/2) := by
      rw [← Real.rpow_add hxpos, show (399:ℝ)/800 + (800:ℝ)⁻¹ = (1:ℝ)/2 by norm_num]
    have h1 : (x:ℝ)^((800:ℝ)⁻¹) ≤ (x:ℝ)^((1:ℝ)/2) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    have h2 : (0:ℝ) ≤ (x:ℝ)^((1:ℝ)/2) := Real.rpow_nonneg (le_of_lt hxpos) _
    rw [Real.sqrt_eq_rpow, le_sub_iff_add_le, le_div_iff₀ hlogB]
    calc ((x:ℝ) ^ ((399:ℝ)/800) + 1) * (Real.log (x:ℝ))^B
        ≤ ((x:ℝ) ^ ((399:ℝ)/800) + 1) * ((1/4) * (x:ℝ) ^ ((800:ℝ)⁻¹)) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = (1/4) * ((x:ℝ)^((399:ℝ)/800) * (x:ℝ)^((800:ℝ)⁻¹) + (x:ℝ)^((800:ℝ)⁻¹)) := by ring
      _ = (1/4) * ((x:ℝ)^((1:ℝ)/2) + (x:ℝ)^((800:ℝ)⁻¹)) := by rw [hp]
      _ ≤ (1/4) * ((x:ℝ)^((1:ℝ)/2) + (x:ℝ)^((1:ℝ)/2)) := by linarith
      _ ≤ (x:ℝ)^((1:ℝ)/2) := by linarith
  have hlt : Real.sqrt (x:ℝ) / (Real.log (x:ℝ))^B - 1
      < (⌊Real.sqrt (x:ℝ) / (Real.log (x:ℝ))^B⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one (Real.sqrt (x:ℝ) / (Real.log (x:ℝ))^B)
    linarith
  have hy : Real.rpow (x:ℝ) (1/8) ^ ((399:ℝ)/100) = (x:ℝ)^((399:ℝ)/800) := by
    rw [show (Real.rpow (x:ℝ) (1/8)) ^ ((399:ℝ)/100)
        = (x:ℝ) ^ ((1:ℝ)/8 * ((399:ℝ)/100)) from
          (Real.rpow_mul (le_of_lt hxpos) (1/8) ((399:ℝ)/100)).symm]
    norm_num
  rw [hy]
  linarith


/-! ### `cut y (⌊y⌋+1) < Z`: the cut at the sifting level itself is already below `Z` -/

lemma four_fifths_pow_le_inv (n : ℕ) (hn : 20 ≤ n) : ((4:ℝ)/5)^n ≤ 1/((n:ℝ)+1) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hk3 : (3:ℝ) ≤ (k:ℝ) := by
      exact_mod_cast (le_trans (by norm_num : 3 ≤ 20) hk)
    calc ((4:ℝ)/5)^(k+1) = ((4:ℝ)/5) * ((4:ℝ)/5)^k := by rw [pow_succ']
      _ ≤ ((4:ℝ)/5) * (1/((k:ℝ)+1)) := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = ((4:ℝ)/5) / ((k:ℝ)+1) := mul_one_div _ _
      _ ≤ 1/((k:ℝ)+2) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
      _ = 1/(((k+1:ℕ):ℝ)+1) := by push_cast; ring

lemma log_le_two_sqrt {y : ℝ} (hy : 0 ≤ y) : Real.log y ≤ 2 * Real.sqrt y := by
  rcases eq_or_lt_of_le hy with rfl | hy0
  · simp
  · have h1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hy0)
    rw [Real.log_sqrt (le_of_lt hy0)] at h1
    linarith

lemma cut_at_floor_succ_lt {y Z : ℝ} (hy : 20 ≤ y) (hZ : 3 ≤ Z) :
    cut y (⌊y⌋₊ + 1) < Z := by
  have hy0 : (0:ℝ) < y := by linarith
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hlogZ : 0 < Real.log Z := Real.log_pos (by linarith)
  have hsy : (0:ℝ) < Real.sqrt y := Real.sqrt_pos.mpr hy0
  have hs2 : (2:ℝ) ≤ Real.sqrt y := (Real.le_sqrt (by norm_num) (by positivity)).mpr (by linarith)
  have hfl : y ≤ (⌊y⌋₊ : ℝ) + 1 := by
    have := Nat.lt_floor_add_one y; linarith
  have hpow : ((4:ℝ)/5)^(⌊y⌋₊) ≤ 1/((⌊y⌋₊ : ℝ) + 1) :=
    four_fifths_pow_le_inv _ (Nat.le_floor (by exact_mod_cast hy))
  have h1 : ((4:ℝ)/5)^(⌊y⌋₊) * Real.log y ≤ 2/Real.sqrt y := by
    have hA : ((4:ℝ)/5)^(⌊y⌋₊) * Real.log y ≤ (1/((⌊y⌋₊ : ℝ)+1)) * Real.log y :=
      mul_le_mul_of_nonneg_right hpow (le_of_lt hlogy)
    have hB : (1/((⌊y⌋₊ : ℝ)+1)) * Real.log y ≤ (1/y) * Real.log y :=
      mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le hy0 hfl) (le_of_lt hlogy)
    have hC : (1/y) * Real.log y ≤ 2/Real.sqrt y := by
      rw [one_div_mul_eq_div, div_le_div_iff₀ hy0 hsy]
      have hlog := log_le_two_sqrt (le_of_lt hy0)
      have h2 := mul_le_mul_of_nonneg_right hlog (le_of_lt hsy)
      have hsq : Real.sqrt y * Real.sqrt y = y := by
        rw [← pow_two, Real.sq_sqrt (le_of_lt hy0)]
      nlinarith [h2, hsq]
    linarith
  have h2 : 2/Real.sqrt y < Real.log Z := by
    have h3 : 2/Real.sqrt y ≤ 1 := by
      rw [div_le_one hsy]; exact hs2
    have h4 : (1:ℝ) < Real.log Z := by
      have h5 : (1:ℝ) < Real.log 3 := (Real.lt_log_iff_exp_lt (by norm_num)).mpr (by
        have := Real.exp_one_lt_d9; linarith)
      exact lt_of_lt_of_le h5 (Real.log_le_log (by norm_num) (by linarith))
    linarith
  have hα : sieveAlpha ^ (⌊y⌋₊ + 1) * Real.log y ≤ ((4:ℝ)/5)^(⌊y⌋₊) * Real.log y := by
    have hα1 : sieveAlpha ^ (⌊y⌋₊ + 1) ≤ sieveAlpha ^ ⌊y⌋₊ := by
      rw [pow_succ]
      nlinarith [pow_nonneg (by rw [sieveAlpha]; norm_num : (0:ℝ) ≤ sieveAlpha) (⌊y⌋₊),
        show sieveAlpha ≤ 1 by rw [sieveAlpha]; norm_num]
    have hα2 : sieveAlpha ^ ⌊y⌋₊ ≤ ((4:ℝ)/5)^⌊y⌋₊ :=
      pow_le_pow_left₀ (by rw [sieveAlpha]; norm_num) (by rw [sieveAlpha]; norm_num) (⌊y⌋₊)
    exact mul_le_mul_of_nonneg_right (le_trans hα1 hα2) (le_of_lt hlogy)
  have hlog : Real.log (cut y (⌊y⌋₊ + 1)) < Real.log Z := by
    rw [cut, Real.log_rpow hy0]
    linarith
  exact (Real.log_lt_log_iff (x := cut y (⌊y⌋₊ + 1)) (y := Z) (cut_pos hy0 _)
    (by linarith : (0:ℝ) < Z)).mp hlog

/-! ### Two final eventual estimates -/

lemma eventually_log_ge (K : ℝ) : ∀ᶠ x : ℕ in Filter.atTop, K ≤ Real.log (x:ℝ) :=
  (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (Filter.eventually_ge_atTop K)

lemma eventually_x_div_log_ge (K : ℝ) :
    ∀ᶠ x : ℕ in Filter.atTop, K ≤ (x:ℝ)/Real.log (x:ℝ) := by
  by_cases hK : K ≤ 0
  · filter_upwards [Filter.eventually_ge_atTop (3:ℕ)] with x hx
    have hxpos : (0:ℝ) < (x:ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) hx)
    have hlogpos : 0 < Real.log (x:ℝ) :=
      Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 3) hx))
    exact le_trans hK (div_nonneg (le_of_lt hxpos) (le_of_lt hlogpos))
  · push_neg at hK
    filter_upwards [Filter.eventually_ge_atTop (max 3 (⌈4*K^2⌉₊ + 1))] with x hx
    have hx3 : (3:ℕ) ≤ x := le_trans (le_max_left _ _) hx
    have hxK : (4*K^2 : ℝ) ≤ (x:ℝ) := by
      have h : ((⌈4*K^2⌉₊ : ℕ) : ℝ) + 1 ≤ (x:ℝ) := by
        exact_mod_cast (le_trans (le_max_right _ _) hx)
      have h2 : (4*K^2 : ℝ) ≤ (⌈4*K^2⌉₊ : ℕ) := Nat.le_ceil _
      linarith
    have hxpos : (0:ℝ) < (x:ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) hx3)
    have hlogpos : 0 < Real.log (x:ℝ) :=
      Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 3) hx3))
    have hsqrt : (2*K) ≤ Real.sqrt (x:ℝ) :=
      (Real.le_sqrt (by linarith) (le_of_lt hxpos)).mpr (by nlinarith)
    have hlog2 : Real.log (x:ℝ) ≤ 2*(x:ℝ)^((1:ℝ)/2) := by
      have h := log_le_two_sqrt (le_of_lt hxpos)
      rwa [Real.sqrt_eq_rpow] at h
    have hsq : (x:ℝ)^((1:ℝ)/2) * (x:ℝ)^((1:ℝ)/2) = (x:ℝ) := by
      rw [← Real.rpow_add hxpos]; norm_num
    have hsqrt' : 2*K ≤ (x:ℝ)^((1:ℝ)/2) := by
      rwa [Real.sqrt_eq_rpow] at hsqrt
    rw [le_div_iff₀ hlogpos]
    nlinarith [hlog2, hsqrt', hsq, Real.rpow_pos_of_pos hxpos ((1:ℝ)/2)]

/-! ### The main sieve estimate, with the numeric bookkeeping extracted -/

set_option maxHeartbeats 4000000 in
lemma sieve_bound_of_params {x : ℕ} {y : ℝ} {M J : ℕ} {B L Z : ℝ}
    (hB0 : 0 < B) (hL : 0 < L) (hZ3 : 3 ≤ Z)
    (hZl : ∀ z : ℝ, Z ≤ z →
      (1-1/1000)*L ≤ Real.log z * Vodd z ∧ Real.log z * Vodd z ≤ (1+1/1000)*L)
    (hx3 : 3 ≤ x) (hy20 : 20 ≤ y) (hyZ : Z + 1 ≤ y)
    (hydef : y = Real.rpow (x:ℝ) (1/8))
    (hMdef : M = ⌊y⌋₊ + 1)
    (hT0 : 800 * (max (Real.log (1/((1-1/1000)*L))) 0 + max (Real.log (Real.log Z)) 0 + 20)
            ≤ Real.log (Real.log y))
    (hD : y ^ ((399:ℝ)/100) ≤ (⌊Real.sqrt (x:ℝ)/(Real.log (x:ℝ))^B⌋₊ : ℝ))
    (hbv : ((Finset.Icc 1 ⌊Real.sqrt (x:ℝ)/(Real.log (x:ℝ))^B⌋₊).filter
            (fun d : ℕ => d % 2 = 1)).sum
          (fun d => |thetaD x d - (x:ℝ)/(Nat.totient d : ℝ)|)
        ≤ (x:ℝ)/(Real.log (x:ℝ))^2)
    (hxlog : 8*Real.log 2/((1-1/1000)*L) ≤ (x:ℝ)/Real.log (x:ℝ))
    (hlogx : max 1 (8/((1-1/1000)*L)) ≤ Real.log (x:ℝ)) :
    (1/4)*(1-1/1000)*L * ((x:ℝ)/Real.log (x:ℝ)) ≤ goodSum x M := by
  classical
  have hy1 : 1 < y := by linarith
  have hy0 : (0:ℝ) < y := by linarith
  have hlogypos : 0 < Real.log y := Real.log_pos (by linarith)
  have hflt : (M:ℝ) - 1 = (⌊y⌋₊ : ℝ) := by rw [hMdef]; push_cast; ring
  have hfl20 : (20:ℕ) ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast hy20)
  have hM1 : 1 ≤ M := by rw [hMdef]; omega
  have hZM : Z ≤ (M:ℝ) - 1 := by
    rw [hflt]
    have := Nat.lt_floor_add_one y
    linarith
  -- the level index
  have hZex : ∃ J : ℕ, cut y (J + 1) < Z := exists_cut_lt hy1 (by linarith)
  set J₀ : ℕ := Nat.find hZex with hJdef
  have hJspec : cut y (J₀ + 1) < Z := Nat.find_spec hZex
  have hJmin : ∀ k < J₀, ¬ (cut y (k + 1) < Z) := fun k hk => Nat.find_min hZex hk
  set N : ℕ := J₀ + 1 with hNdef
  have hJM : J₀ ≤ M := by
    have hcutMlt : cut y M < Z := by
      rw [hMdef]
      exact cut_at_floor_succ_lt (by linarith : (20:ℝ) ≤ y) hZ3
    have h : cut y (M + 1) < Z := by
      have hle := cut_anti hy1 (Nat.le_succ M)
      linarith
    exact Nat.find_le h
  have hZc : ∀ j ∈ Finset.Icc 1 J₀, Z ≤ cut y j := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hjJ : j ≤ J₀ := (Finset.mem_Icc.mp hj).2
    have h1 : j - 1 < J₀ := by omega
    have h2 := hJmin (j - 1) h1
    have h3 : j - 1 + 1 = j := by omega
    rw [h3] at h2
    exact not_lt.mp h2
  have hcutM : ∀ j ∈ Finset.Icc 1 J₀, cut y j ≤ (M:ℝ) - 1 := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have h1 : cut y j ≤ cut y 1 := cut_anti hy1 hj1
    have h2 : cut y 1 ≤ y - 1 := cut_one_le_sub_one (by linarith)
    have h3 : y - 1 ≤ (M:ℝ) - 1 := by
      rw [hflt]; have := Nat.lt_floor_add_one y; linarith
    linarith
  have hcut0 : ∀ j ∈ Finset.Icc 1 J₀, (0:ℝ) ≤ cut y j := fun j _ => le_of_lt (cut_pos hy0 j)
  have hlogM : Real.log ((M:ℝ) - 1) ≤ (1 + 1/1000) * Real.log y := by
    have h1 : Real.log ((M:ℝ) - 1) ≤ Real.log y := by
      rw [hflt]
      exact Real.log_le_log (by positivity) (by have := Nat.floor_le (le_of_lt hy0); linarith)
    nlinarith [hlogypos]
  have hε1 : Real.log ((1+1/1000)/(1-1/1000)) + Real.log (1+1/1000) ≤ 7/1000 := by
    have h1 : Real.log ((1+1/1000)/(1-1/1000)) ≤ (1+1/1000)/(1-1/1000) - 1 :=
      Real.log_le_sub_one_of_pos (by norm_num)
    have h2 : Real.log (1+1/1000) ≤ 1/1000 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 1+1/1000)
      linarith
    have h3 : (1+1/1000)/(1-1/1000) - 1 ≤ 6/1000 := by norm_num
    linarith
  have hcutc : ∀ j ∈ Finset.Icc (J₀+1) M, cut y j ≤ (M:ℝ) - 1 := by
    intro j hj
    have h1 : J₀ + 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have h2 : cut y j ≤ cut y (J₀+1) := cut_anti hy1 h1
    linarith [hJspec]
  have hcutc0 : ∀ j ∈ Finset.Icc (J₀+1) M, (0:ℝ) ≤ cut y j :=
    fun j _ => le_of_lt (cut_pos hy0 j)
  -- T_B and its bounds
  have hVodd : VsieveOdd M = Vodd ((M:ℝ) - 1) := VsieveOdd_eq_Vodd_pred M hM1
  have hlogMpos : 0 < Real.log ((M:ℝ) - 1) := by
    rw [hflt]; exact Real.log_pos (by exact_mod_cast (show 1 < ⌊y⌋₊ by omega))
  have hVlb : (1-1/1000)*L ≤ Real.log ((M:ℝ) - 1) * VsieveOdd M := by
    rw [hVodd]; exact (hZl ((M:ℝ)-1) hZM).1
  have hVpos : 0 < VsieveOdd M := VsieveOdd_pos M
  have hVle1 : VsieveOdd M ≤ 1 := VsieveOdd_le_one M
  have hVlow : (1-1/1000)*L / Real.log y ≤ VsieveOdd M := by
    have h1 : (1-1/1000)*L / Real.log ((M:ℝ)-1) ≤ VsieveOdd M := by
      rw [div_le_iff₀ hlogMpos]; linarith [hVlb, mul_comm (Real.log ((M:ℝ)-1)) (VsieveOdd M)]
    have h2 : Real.log ((M:ℝ)-1) ≤ Real.log y := by
      rw [hflt]
      exact Real.log_le_log (by positivity) (by have := Nat.floor_le (le_of_lt hy0); linarith)
    have h3 : (1-1/1000)*L / Real.log y ≤ (1-1/1000)*L / Real.log ((M:ℝ)-1) :=
      div_le_div_of_nonneg_left (by positivity) hlogMpos h2
    linarith
  have hVexp : (1-1/1000)*L * Real.exp (-(Real.log (Real.log y))) ≤ VsieveOdd M := by
    have hexp : Real.exp (-(Real.log (Real.log y))) = (Real.log y)⁻¹ := by
      rw [Real.exp_neg, Real.exp_log hlogypos]
    rw [hexp, div_eq_mul_inv]
    simpa only [div_eq_mul_inv] using hVlow
  -- threshold bookkeeping
  set K : ℝ := max (Real.log (1/((1-1/1000)*L))) 0 + max (Real.log (Real.log Z)) 0 + 20 with hKdef
  have hK20 : 20 ≤ K := by
    rw [hKdef]
    nlinarith [le_max_left (Real.log (1/((1-1/1000)*L))) 0,
      le_max_right (Real.log (1/((1-1/1000)*L))) 0,
      le_max_left (Real.log (Real.log Z)) 0,
      le_max_right (Real.log (Real.log Z)) 0]
  have hKnn : 0 ≤ K := by linarith
  have hKτ : 800*K ≤ Real.log (Real.log y) := hT0
  have hC1K : Real.log (1/((1-1/1000)*L)) ≤ K := by
    rw [hKdef]
    linarith [le_max_left (Real.log (1/((1-1/1000)*L))) 0,
      le_max_left (Real.log (Real.log Z)) 0, le_max_right (Real.log (Real.log Z)) 0]
  have hc1K : Real.log (Real.log Z) ≤ K := by
    rw [hKdef]
    linarith [le_max_right (Real.log (1/((1-1/1000)*L))) 0,
      le_max_left (Real.log (Real.log Z)) 0, le_max_right (Real.log (Real.log Z)) 0]
  have hc1τ : Real.log (Real.log Z) ≤ Real.log (Real.log y) := by linarith
  have hlog40 : Real.log (40:ℝ) ≤ 39 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 40)
    linarith
  have hτ0 : 0 ≤ Real.log (Real.log y) := by linarith
  -- T_B
  have hTBnn : 0 ≤ Real.log (1/VsieveOdd M) :=
    Real.log_nonneg ((one_le_div hVpos).mpr hVle1)
  have hTBub : Real.log (1/VsieveOdd M)
      ≤ Real.log (Real.log y) + K := by
    have hpos1 : 0 < (1-1/1000)*L := by positivity
    have hpos2 : 0 < (1-1/1000)*L / Real.log y := div_pos hpos1 hlogypos
    have h1 : Real.log (1/VsieveOdd M)
        ≤ Real.log (Real.log y) + Real.log (1/((1-1/1000)*L)) := by
      have h12 : 1 / VsieveOdd M ≤ Real.log y / ((1-1/1000)*L) := by
        have h := one_div_le_one_div_of_le hpos2 hVlow
        rwa [one_div_div] at h
      refine le_trans (Real.log_le_log (one_div_pos.mpr hVpos) h12) ?_
      have h3 : Real.log (Real.log y / ((1-1/1000)*L))
          = Real.log (Real.log y) - Real.log ((1-1/1000)*L) :=
        Real.log_div (ne_of_gt hlogypos) (ne_of_gt hpos1)
      have h4 : Real.log ((1-1/1000)*L) = -Real.log (1/((1-1/1000)*L)) := by
        rw [← inv_eq_one_div ((1-1/1000)*L), Real.log_inv, neg_neg]
      rw [h3, h4]
      norm_num
    linarith [h1, hC1K]
  -- N is large
  have hβpos : 0 < sieveBeta := Real.log_pos (by norm_num : (1:ℝ) < 1000/599)
  have hNlow : (Real.log (Real.log y) - Real.log (Real.log Z)) / sieveBeta < (N:ℝ) := by
    have hlogZpos : 0 < Real.log Z := Real.log_pos (by linarith)
    have hcll : 0 < Real.log (Real.log Z) := by
      apply Real.log_pos
      have hlt : (1:ℝ) < Real.log 3 :=
        (Real.lt_log_iff_exp_lt (by norm_num)).mpr (by have := Real.exp_one_lt_d9; linarith)
      exact lt_of_lt_of_le hlt (Real.log_le_log (by norm_num) (by linarith))
    have hα0 : 0 < sieveAlpha := by rw [sieveAlpha]; norm_num
    have h1 : Real.log (cut y N) < Real.log Z :=
      (Real.log_lt_log_iff (x := cut y N) (y := Z) (cut_pos hy0 N)
        (by linarith : (0:ℝ) < Z)).mpr hJspec
    rw [cut, Real.log_rpow hy0] at h1
    have h2 : Real.log (sieveAlpha ^ N * Real.log y) < Real.log (Real.log Z) :=
      (Real.log_lt_log_iff (x := sieveAlpha ^ N * Real.log y) (y := Real.log Z)
        (by positivity) hlogZpos).mpr h1
    rw [Real.log_mul (ne_of_gt (pow_pos hα0 N)) (ne_of_gt hlogypos), Real.log_pow] at h2
    have h3 : Real.log sieveAlpha = -sieveBeta := by
      rw [sieveBeta, sieveAlpha, show (599:ℝ)/1000 = ((1000:ℝ)/599)⁻¹ by norm_num, Real.log_inv]
    rw [h3] at h2
    rw [div_lt_iff₀ hβpos]
    linarith
  have hX0 : (0:ℝ) ≤ Real.log (Real.log y) - Real.log (Real.log Z) := by linarith
  have hNinv : (1000/513 : ℝ) ≤ sieveBeta⁻¹ := by
    have h2 : sieveBeta ≤ ((1000:ℝ)/513)⁻¹ := by
      rw [show (((1000:ℝ)/513))⁻¹ = 513/1000 by norm_num]
      exact log_1000_599_le
    exact (le_inv_comm₀ (a := (1000:ℝ)/513) (b := sieveBeta) (by norm_num) hβpos).mpr h2
  have hNstep : (1000/513 : ℝ) * (Real.log (Real.log y) - Real.log (Real.log Z))
      ≤ (Real.log (Real.log y) - Real.log (Real.log Z)) / sieveBeta := by
    have h6 := mul_le_mul_of_nonneg_right hNinv hX0
    calc (1000/513 : ℝ) * (Real.log (Real.log y) - Real.log (Real.log Z))
        ≤ sieveBeta⁻¹ * (Real.log (Real.log y) - Real.log (Real.log Z)) := h6
      _ = (Real.log (Real.log y) - Real.log (Real.log Z)) / sieveBeta := by
          rw [div_eq_mul_inv, mul_comm]
  have hN2 : (2000/513) * (Real.log (Real.log y) - Real.log (Real.log Z))
      ≤ ((2*N : ℕ) : ℝ) := by
    have h3 : ((2*N : ℕ) : ℝ) = 2 * (N:ℝ) := by push_cast; ring
    rw [h3]
    nlinarith [hNstep, hNlow]
  have hN1 : 1 ≤ N := by omega
  -- T_B is dominated by (7/10)(2N)
  have hTB : Real.exp 1 * Real.log (1/VsieveOdd M) ≤ (71/100) * ((2*N : ℕ) : ℝ) := by
    have he : Real.exp 1 ≤ (272/100 : ℝ) := by have := Real.exp_one_lt_d9; linarith
    have hKd : K ≤ Real.log (Real.log y) / 800 := by linarith [hKτ]
    have h1 : Real.exp 1 * (Real.log (Real.log y) + K)
        ≤ (272/100) * (Real.log (Real.log y) + K) :=
      mul_le_mul_of_nonneg_right he (by linarith [hKnn, hτ0])
    have h2 : (272/100) * (Real.log (Real.log y) + K)
        ≤ (273/100) * Real.log (Real.log y) := by
      nlinarith [hKd, hKnn, hτ0]
    have h3 : (273/100) * Real.log (Real.log y)
        ≤ (71/100) * ((2000/513) * (Real.log (Real.log y) - Real.log (Real.log Z))) := by
      have h2' : (2000/513 : ℝ) * (Real.log (Real.log y) - Real.log (Real.log Z))
          ≥ (2000/513) * ((799/800) * Real.log (Real.log y)) := by
        nlinarith [hc1K, hKd, hτ0]
      nlinarith [h2', hτ0]
    refine le_trans (mul_le_mul_of_nonneg_left hTBub (le_of_lt (Real.exp_pos 1))) ?_
    exact le_trans h1 (le_trans h2 (le_trans h3 (by linarith [hN2])))
  -- the factorial-decay condition
  have hdecay : 2 * ((71:ℝ)/100)^(2*N) ≤ VsieveOdd M / 20 := by
    have h := crude_tail_exp_small (V := VsieveOdd M) (τ := Real.log (Real.log y))
      (c₁ := Real.log (Real.log Z)) (N := N) (L := L) hVexp hN2 ?_
    · linarith
    · have hpos1 : 0 < (1-1/1000)*L := by positivity
      have hlog : Real.log 40 + ((132/100)*Real.log (Real.log Z)
            - (32/100)*Real.log (Real.log y))
          ≤ Real.log ((1-1/1000)*L/40) := by
        rw [Real.log_div (ne_of_gt hpos1) (by norm_num : (40:ℝ) ≠ 0)]
        have h4 : Real.log ((1-1/1000)*L) = -Real.log (1/((1-1/1000)*L)) := by
          rw [← inv_eq_one_div ((1-1/1000)*L), Real.log_inv, neg_neg]
        rw [h4]
        nlinarith [hC1K, hc1K, hKτ, hK20, hlog40]
      have h2 : 40 * Real.exp ((132/100)*Real.log (Real.log Z)
            - (32/100)*Real.log (Real.log y))
          = Real.exp (Real.log 40
              + ((132/100)*Real.log (Real.log Z) - (32/100)*Real.log (Real.log y))) := by
        rw [Real.exp_add, Real.exp_log (by norm_num : (0:ℝ) < 40)]
      rw [h2]
      refine le_trans (Real.exp_le_exp.mpr hlog) ?_
      rw [Real.exp_log (by positivity : (0:ℝ) < (1-1/1000)*L/40)]
      linarith
  have hcru : 2 * ((Real.log (1/VsieveOdd M))^(2*N) / (((2*N).factorial : ℕ) : ℝ))
      ≤ VsieveOdd M / 20 :=
    crude_tail_small (Real.log (1/VsieveOdd M)) (VsieveOdd M) N hN1 hTBnn hTB hdecay
  have hρ : 2 * (Real.log (1/VsieveOdd M))^2 ≤ (((2*N+1)*(2*N+2) : ℕ) : ℝ) := by
    have h1 : Real.log (1/VsieveOdd M) ≤ Real.log (Real.log y) + K := hTBub
    have h2 : 2 * (Real.log (Real.log y) + K)^2
        ≤ 15 * (Real.log (Real.log y) - Real.log (Real.log Z))^2 := by
      have h3 : Real.log (Real.log y) - K ≤ Real.log (Real.log y) - Real.log (Real.log Z) := by
        linarith
      have h4 : Real.log (Real.log y) + K ≤ (801/799 : ℝ) * (Real.log (Real.log y) - K) := by
        have h5 : K ≤ Real.log (Real.log y) / 800 := by linarith [hKτ]
        nlinarith [h5, hKnn]
      have h5 : (0:ℝ) ≤ Real.log (Real.log y) - K := by linarith [hKτ, hKnn]
      have h6 : (0:ℝ) ≤ Real.log (Real.log y) + K := by linarith [hKnn]
      nlinarith [h3, h4, h5, h6, sq_nonneg (Real.log (Real.log y) - Real.log (Real.log Z)),
        sq_nonneg (Real.log (Real.log y) - K),
        mul_nonneg h6 (sub_nonneg.mpr h4)]
    have h7 : 15 * (Real.log (Real.log y) - Real.log (Real.log Z))^2
        ≤ (((2*N : ℕ) : ℝ))^2 := by
      have h3 : ((2*N : ℕ) : ℝ) = 2 * (N:ℝ) := by push_cast; ring
      rw [h3]
      nlinarith [hN2, hX0,
        sq_nonneg ((2000/513:ℝ)*(Real.log (Real.log y) - Real.log (Real.log Z))
          - ((2*N:ℕ):ℝ))]
    have h8 : ((2*(N:ℝ))^2) ≤ (((2*N+1)*(2*N+2) : ℕ) : ℝ) := by
      have hNnn : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
      push_cast
      nlinarith
    have h9 : 2 * (Real.log (Real.log y) + K)^2
        ≥ 2 * (Real.log (1/VsieveOdd M))^2 := by
      nlinarith [hTBnn, h1]
    have h10 : ((2*(N:ℝ))^2) = (((2*N : ℕ) : ℝ))^2 := by push_cast; ring
    linarith [h2, h7, h8, h9]
  -- Bnd bound
  have hcoef : ((1+1/1000)/(1-1/1000))*(1+1/1000)*(5/6) ≤ (17/20 : ℝ) := by norm_num
  have hVnn : 0 ≤ VsieveOdd M := le_of_lt hVpos
  have hBnd : Bnd y 1 M ≤ (11/12) * VsieveOdd M := by
    have h1 := Bnd_le_sharp_plus_crude y hy1 M J₀ hM1 hJM hL (by norm_num : (0:ℝ) < 1/1000)
      (by norm_num : (1:ℝ)/1000 < 1) hZ3 hZl hZc hZM hcutM hcut0 hlogM hε1 hcutc0 hcutc hρ
    have h2 : 2 * (Real.log (1 / VsieveOdd M) ^ (2*(J₀+1)) / (((2*(J₀+1)).factorial : ℕ) : ℝ))
        ≤ VsieveOdd M / 20 := by
      rw [← hNdef]; exact hcru
    have h3 : ((1+1/1000)/(1-1/1000))*(1+1/1000)*(VsieveOdd M)*(5/6)
        ≤ (17/20) * VsieveOdd M := by
      nlinarith [hcoef, hVnn]
    linarith [h1, h2, h3]
  have hElo : (1/12) * VsieveOdd M ≤ Elo y 1 M := Elo_ge_twelfth y M hBnd
  -- the assembly
  have hy3 : 3 ≤ y := by linarith
  have hD' : y ^ ((399:ℝ)/100) ≤ ((⌊Real.sqrt (x:ℝ)/(Real.log (x:ℝ))^B⌋₊ : ℕ) : ℝ) := hD
  have hgs := goodSum_ge_chain x M y hy3
  have hmt := chain_theta_main_error x M y
  have herr := abs_chain_rD_le x M ⌊Real.sqrt (x:ℝ)/(Real.log (x:ℝ))^B⌋₊ y hy1
    (by rw [hMdef]) hD'
  have hEbound : |(loChain y 1 M).sum (fun c => (-1:ℝ)^c.length * rD x c.prod)|
      ≤ (x:ℝ)/(Real.log (x:ℝ))^2 := le_trans herr hbv
  have hlogxpos : 0 < Real.log (x:ℝ) := Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hstep : (x:ℝ) * ((1/12) * VsieveOdd M) - ((x:ℝ)/(Real.log (x:ℝ))^2)
      ≤ goodSum x M := by
    have h3 : (x:ℝ) * ((1/12) * VsieveOdd M) ≤ (x:ℝ) * Elo y 1 M :=
      mul_le_mul_of_nonneg_left hElo (Nat.cast_nonneg x)
    have h4 : -((x:ℝ)/(Real.log (x:ℝ))^2)
        ≤ (loChain y 1 M).sum (fun c => (-1:ℝ)^c.length * rD x c.prod) :=
      le_trans (neg_le_neg hEbound) (neg_abs_le _)
    linarith [hmt, hgs, h3, h4]
  -- final numeric comparison
  have hlogy_eq : Real.log y = Real.log (x:ℝ)/8 := by
    rw [hydef, show Real.rpow (x:ℝ) (1/8) = (x:ℝ) ^ ((1:ℝ)/8) from rfl,
      Real.log_rpow (by positivity : (0:ℝ) < (x:ℝ))]
    ring
  have hVfin : 8*((1-1/1000)*L)/Real.log (x:ℝ) ≤ VsieveOdd M := by
    have h2 : (1-1/1000)*L / Real.log y = 8*((1-1/1000)*L / Real.log (x:ℝ)) := by
      rw [hlogy_eq]; ring
    have hXnn : (0:ℝ) ≤ (1-1/1000)*L / Real.log (x:ℝ) :=
      div_nonneg (by positivity) (le_of_lt hlogxpos)
    have h9 : 8*((1-1/1000)*L / Real.log (x:ℝ)) ≤ VsieveOdd M := by
      rw [← h2]; exact hVlow
    have h10 : 8*((1-1/1000)*L)/Real.log (x:ℝ)
        = 8*((1-1/1000)*L / Real.log (x:ℝ)) := by ring
    linarith [h9, h10, hXnn]
  have hlogx8 : 8/((1-1/1000)*L) ≤ Real.log (x:ℝ) := le_trans (le_max_right _ _) hlogx
  have hposL : 0 < (1-1/1000)*L := by positivity
  have hxpos : (0:ℝ) < (x:ℝ) := by exact_mod_cast (show 0 < x by omega)
  have h3 : 8 ≤ (1-1/1000)*L * Real.log (x:ℝ) := by
    rw [div_le_iff₀ hposL] at hlogx8; linarith
  have h4 : 8*Real.log 2 ≤ ((1-1/1000)*L) * ((x:ℝ)/Real.log (x:ℝ)) := by
    rw [div_le_iff₀ hposL] at hxlog
    linarith [hxlog]
  have hbig : (1/4)*((1-1/1000)*L) * ((x:ℝ)/Real.log (x:ℝ))
      ≤ (x:ℝ) * ((1/12) * VsieveOdd M) - ((x:ℝ)/(Real.log (x:ℝ))^2) := by
    have hA : (1/4)*((1-1/1000)*L) * ((x:ℝ)/Real.log (x:ℝ)) + (x:ℝ)/(Real.log (x:ℝ))^2
        ≤ (x:ℝ) * ((1/12) * (8*((1-1/1000)*L)/Real.log (x:ℝ))) := by
      have h5 : (x:ℝ)/Real.log (x:ℝ)^2
          ≤ (1/8)*((1-1/1000)*L) * ((x:ℝ)/Real.log (x:ℝ)) := by
        rw [div_le_iff₀ (by positivity : (0:ℝ) < Real.log (x:ℝ)^2)]
        rw [show ((1/8)*((1-1/1000)*L) * ((x:ℝ)/Real.log (x:ℝ))) * (Real.log (x:ℝ))^2
            = (1/8)*((1-1/1000)*L) * (x:ℝ) * Real.log (x:ℝ) by field_simp]
        have h6 : (1:ℝ) ≤ (1/8)*((1-1/1000)*L) * Real.log (x:ℝ) := by linarith
        nlinarith [h6, hxpos, hlogxpos, hposL]
      have h7 : (x:ℝ) * ((1/12) * (8*((1-1/1000)*L)/Real.log (x:ℝ)))
          = (2/3)*((1-1/1000)*L) * ((x:ℝ)/Real.log (x:ℝ)) := by ring
      rw [h7]
      have hu : 0 ≤ ((1-1/1000)*L) * ((x:ℝ)/Real.log (x:ℝ)) :=
        mul_nonneg (by positivity) (le_of_lt (div_pos hxpos hlogxpos))
      linarith [h5, hu]
    have h1 : (x:ℝ) * ((1/12) * (8*((1-1/1000)*L)/Real.log (x:ℝ)))
        ≤ (x:ℝ) * ((1/12) * VsieveOdd M) := by
      have h8 : (1/12) * (8*((1-1/1000)*L)/Real.log (x:ℝ)) ≤ (1/12) * VsieveOdd M := by
        linarith [hVfin]
      exact mul_le_mul_of_nonneg_left h8 (le_of_lt hxpos)
    linarith [hA, h1]
  linarith [hstep, hbig]

/-- **Chen's dimension-one lower bound sieve** (the fundamental lemma, `κ = 1`):
Bombieri--Vinogradov implies that the primes `p ≤ x` with `p + 2` free of prime factors
`≤ x^{1/8}` carry mass `≫ x / log x`. -/
theorem dim1_sieve_lower_rpow
    (hBV : ∀ A : ℝ, 0 < A →
      ∃ B : ℝ, 0 < B ∧ ∀ᶠ x : ℕ in Filter.atTop,
        ((Finset.Icc 1 ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊).filter
            (fun d : ℕ => d % 2 = 1)).sum
          (fun d =>
            |((Finset.range (x + 1)).filter (fun p : ℕ => p.Prime ∧ d ∣ p + 2)).sum
                (fun p => Real.log (p : ℝ))
              - (x : ℝ) / (Nat.totient d : ℝ)|)
        ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℕ in Filter.atTop,
      c * (x : ℝ) / Real.log (x : ℝ) ≤
        (((Finset.range (x + 1)).filter
          (fun p => p.Prime ∧ Nat.Coprime (p + 2)
            (∏ q ∈ (Nat.primesLE ⌊Real.rpow (x : ℝ) (1 / 8)⌋₊).filter (fun q : ℕ => q ≠ 2), q))).sum
            (fun p => Real.log (p : ℝ)) : ℝ) := by
  classical
  obtain ⟨L, hL, hlim⟩ := Vodd_limit
  obtain ⟨Z, hZ3, hZ⟩ := Vodd_eventually hL (by norm_num : (0:ℝ) < 1/1000) hlim
  obtain ⟨B, hB0, hBv⟩ := hBV 2 (by norm_num)
  refine ⟨(1/4)*(1-1/1000)*L, by positivity, ?_⟩
  filter_upwards [hBv, eventually_D_ge_rpow hB0,
    eventually_loglog_large (800 * (max (Real.log (1/((1-1/1000)*L))) 0
      + max (Real.log (Real.log Z)) 0 + 20)),
    eventually_rpow_one_eighth_ge (max 20 (Z+1)),
    eventually_x_div_log_ge (8*Real.log 2/((1-1/1000)*L)),
    eventually_log_ge (max 1 (8/((1-1/1000)*L))),
    Filter.eventually_ge_atTop 3] with x hbv hD hT hY hxlog hlogx hx
  have hy20 : 20 ≤ Real.rpow (x:ℝ) (1/8) := le_trans (le_max_left _ _) hY
  have hyZ : Z + 1 ≤ Real.rpow (x:ℝ) (1/8) := le_trans (le_max_right _ _) hY
  have hbv' : ((Finset.Icc 1 ⌊Real.sqrt (x:ℝ)/(Real.log (x:ℝ))^B⌋₊).filter
        (fun d : ℕ => d % 2 = 1)).sum
        (fun d => |thetaD x d - (x:ℝ)/(Nat.totient d : ℝ)|)
      ≤ (x:ℝ)/(Real.log (x:ℝ))^2 := by
    simpa [thetaD] using hbv
  have hmain := sieve_bound_of_params (J := 0) (y := Real.rpow (x:ℝ) (1/8))
    (M := ⌊Real.rpow (x:ℝ) (1/8)⌋₊ + 1) (B := B) (L := L) (Z := Z)
    hB0 hL hZ3 hZ hx hy20 hyZ rfl rfl hT hD hbv' hxlog hlogx
  have hP : oddPrimLt (⌊Real.rpow (x:ℝ) (1/8)⌋₊ + 1)
      = (∏ q ∈ (Nat.primesLE ⌊Real.rpow (x : ℝ) (1/8)⌋₊).filter (fun q : ℕ => q ≠ 2), q) := by
    unfold oddPrimLt
    rw [Nat.primesLE_eq_filter_range]
    congr 1
    ext q
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, by have := h2.two_le; omega⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, h2, by have h2' : 2 ≤ q := h2.two_le; omega⟩
  have hgood : goodSum x (⌊Real.rpow (x:ℝ) (1/8)⌋₊ + 1)
      = (((Finset.range (x + 1)).filter
          (fun p => p.Prime ∧ Nat.Coprime (p + 2)
            (∏ q ∈ (Nat.primesLE ⌊Real.rpow (x : ℝ) (1/8)⌋₊).filter (fun q : ℕ => q ≠ 2), q))).sum
            (fun p => Real.log (p : ℝ)) : ℝ) := by
    have hL : goodSum x (⌊Real.rpow (x:ℝ) (1/8)⌋₊ + 1)
        = ∑ p ∈ Finset.range (x+1),
            (if p.Prime then Real.log (p:ℝ) * Id (p+2) (⌊Real.rpow (x:ℝ) (1/8)⌋₊ + 1) else 0) := by
      unfold goodSum
      rw [Finset.sum_filter]
    have hR : (((Finset.range (x + 1)).filter
          (fun p => p.Prime ∧ Nat.Coprime (p + 2)
            (∏ q ∈ (Nat.primesLE ⌊Real.rpow (x : ℝ) (1/8)⌋₊).filter (fun q : ℕ => q ≠ 2), q))).sum
            (fun p => Real.log (p : ℝ)) : ℝ)
        = ∑ p ∈ Finset.range (x+1),
            (if p.Prime ∧ Nat.Coprime (p + 2)
                (∏ q ∈ (Nat.primesLE ⌊Real.rpow (x : ℝ) (1/8)⌋₊).filter (fun q : ℕ => q ≠ 2), q)
              then Real.log (p:ℝ) else 0) := by
      rw [Finset.sum_filter]
    rw [hL, hR]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    unfold Id
    rw [hP]
    by_cases hq : p.Prime
    · by_cases hc : Nat.Coprime (p + 2)
          (∏ q ∈ (Nat.primesLE ⌊Real.rpow (x : ℝ) (1/8)⌋₊).filter (fun q : ℕ => q ≠ 2), q)
      · simp only [if_pos hq, if_pos hc, if_pos (show p.Prime ∧ Nat.Coprime (p + 2)
          (∏ q ∈ (Nat.primesLE ⌊Real.rpow (x : ℝ) (1/8)⌋₊).filter (fun q : ℕ => q ≠ 2), q)
          from ⟨hq, hc⟩), mul_one]
      · have hconj : ¬ (p.Prime ∧ Nat.Coprime (p + 2)
            (∏ q ∈ (Nat.primesLE ⌊Real.rpow (x : ℝ) (1/8)⌋₊).filter (fun q : ℕ => q ≠ 2), q)) :=
          fun h => hc h.2
        simp only [if_pos hq, if_neg hc, if_neg hconj, mul_zero]
    · have hconj : ¬ (p.Prime ∧ Nat.Coprime (p + 2)
          (∏ q ∈ (Nat.primesLE ⌊Real.rpow (x : ℝ) (1/8)⌋₊).filter (fun q : ℕ => q ≠ 2), q)) :=
        fun h => hq h.1
      simp only [if_neg hq, if_neg hconj]
  rw [← hgood]
  have hLHS : (1/4)*(1-1/1000)*L * (x:ℝ) / Real.log (x:ℝ)
      = (1/4)*(1-1/1000)*L * ((x:ℝ)/Real.log (x:ℝ)) := by ring
  rw [hLHS]
  exact hmain

end

end ChenEight

theorem rough_theta_lower_of_bv
    (hBV : ∀ A : ℝ, 0 < A →
      ∃ B : ℝ, 0 < B ∧ ∀ᶠ x : ℕ in Filter.atTop,
        ((Finset.Icc 1 ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊).filter
            (fun d : ℕ => d % 2 = 1)).sum
          (fun d =>
            |((Finset.range (x + 1)).filter (fun p : ℕ => p.Prime ∧ d ∣ p + 2)).sum
                (fun p => Real.log (p : ℝ))
              - (x : ℝ) / (Nat.totient d : ℝ)|)
        ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℕ in Filter.atTop,
      c * (x : ℝ) / Real.log (x : ℝ) ≤
        ((Finset.range (x + 1)).filter
          (fun p : ℕ => p.Prime ∧
            Nat.Coprime (p + 2)
              (∏ q ∈ (Nat.primesLE ⌊Real.rpow (x : ℝ) (1 / 8 : ℝ)⌋₊).filter
                  (fun q : ℕ => q ≠ 2), q))).sum
          (fun p => Real.log (p : ℝ)) := by
  exact ChenEight.dim1_sieve_lower_rpow hBV
