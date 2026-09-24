import Mathlib
import Submission.Commons.NumberTheory.Chen.rough_theta_lower_of_bv
import Submission.Chen.SwitchDefs

/-!
# `RosserLinear` — the one-sided Rosser–Iwaniec linear sieve: definitions

This area supplies the **one-sided `λ±` weight family of the linear sieve** for the
shifted-prime sifted mass of Chen's theorem, and the sharp fundamental-lemma main-term
estimate that the parent assembly (`Submission.Chen.Switch`) needs.

## The weight family

For a *sieve parameter* `β ≥ 1`, a *level of distribution* `D` and a *sift limit* `Y`
we use the `β`-chain sets `Gm β D Y` / `Gp β D Y` of `Commons.NumberTheory.Chen` (the
Rosser one-sided chains `q₁ > q₂ > ⋯`, with the *odd* slots constrained by
`q₁⋯q_{2k-1} ≤ D` and the *even* slots by `q₁⋯q_{2k-1}·q_{2k}^{β+1} ≤ D`).
`Gm` is the lower-bound (minorant) side, `Gp` the upper-bound (majorant) side.

* `lamM β D Y d` (resp. `lamP β D Y d`) is the **weight** of the integer `d`: the sum of
  `(-1)^{|c|}` over the admissible chains `c` with `lprod c = d`.  Since a square-free
  number has at most one decreasing factorisation (`chain_lprod_inj`), `lamM β D Y d` is
  `μ d · 1_{d admissible}` — the classical `λ⁻` weight (and `lamP` is `λ⁺`).
* `Msum β D Y = Σ_{c ∈ Gm} (-1)^{|c|}/φ(lprod c)` and `Psum β D Y` are the corresponding
  **main terms** `Σ_d λ_d/φ d`.
* `Wminus β D Y = Vsieve Y - Msum β D Y` is the **deficit** of the lower-bound main term,
  `Wplus β D Y = Psum β D Y - Vsieve Y` the surplus of the upper-bound main term, and
  `Wtot = Psum - Msum` the total bracket width.

The classical facts (proved in the sibling modules of this directory) are

* `lamM_minorant` : `Σ_{d|n} λ⁻_d ≤ 1_{(n, P(Y)) = 1} ≤ Σ_{d|n} λ⁺_d` (one-sidedness);
* `Msum_le_Vsieve` / `Vsieve_le_Psum` : `Msum ≤ Vsieve ≤ Psum` for `D ≥ Y`;
* `Wtot_rec` : for `D ≥ Y^{β+1}` the total bracket satisfies the *cancellation-free*
  Buchstab recursion `Wtot(D,Y) = Σ_{q<Y} (q-1)⁻¹ Wtot(D/q, q)`;
* `deficit_bound` : the sharp fundamental-lemma bound `Wminus ≤ ε · Vsieve Y`.

## Convention

`λ⁻` is indexed by `Gm` (the *lower*-bound sieve, a minorant of the indicator), `λ⁺` by
`Gp`.  Both are supported on odd `d` with `(d:ℝ) ≤ D` all of whose prime factors are
`< Y` (`lamM_support`).
-/

open Finset
open scoped BigOperators
open scoped ArithmeticFunction.Omega

namespace Work.NumberTheory.Sieve.RosserLinear

open Commons.NumberTheory.Chen

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The one-sided **lower-bound** weight `λ⁻`: the sum of `(-1)^{|c|}` over the admissible
chains `c ∈ Gm β D Y` with product `d`. -/
noncomputable def lamM (β D : ℝ) (Y d : ℕ) : ℝ :=
  ((Gm β D Y).filter (fun c => lprod c = d)).sum (fun c => (-1 : ℝ) ^ c.length)

/-- The one-sided **upper-bound** weight `λ⁺`: the sum of `(-1)^{|c|}` over the admissible
chains `c ∈ Gp β D Y` with product `d`. -/
noncomputable def lamP (β D : ℝ) (Y d : ℕ) : ℝ :=
  ((Gp β D Y).filter (fun c => lprod c = d)).sum (fun c => (-1 : ℝ) ^ c.length)

/-- The lower-bound **main term** `Σ_{d} λ⁻_d/φ(d)`, written as the chain sum (so that no
square-free hypothesis on `d` is needed). -/
noncomputable def Msum (β D : ℝ) (Y : ℕ) : ℝ :=
  (Gm β D Y).sum (fun c => (-1 : ℝ) ^ c.length / (Nat.totient (lprod c) : ℝ))

/-- The upper-bound **main term** `Σ_{d} λ⁺_d/φ(d)`. -/
noncomputable def Psum (β D : ℝ) (Y : ℕ) : ℝ :=
  (Gp β D Y).sum (fun c => (-1 : ℝ) ^ c.length / (Nat.totient (lprod c) : ℝ))

/-- The **deficit** of the lower-bound main term: `Vsieve Y - Msum β D Y`. -/
noncomputable def Wminus (β D : ℝ) (Y : ℕ) : ℝ := Vsieve Y - Msum β D Y

/-- The **surplus** of the upper-bound main term: `Psum β D Y - Vsieve Y`. -/
noncomputable def Wplus (β D : ℝ) (Y : ℕ) : ℝ := Psum β D Y - Vsieve Y

/-- The **total bracket width** `Psum - Msum`. -/
noncomputable def Wtot (β D : ℝ) (Y : ℕ) : ℝ := Psum β D Y - Msum β D Y

lemma Wtot_eq (β D : ℝ) (Y : ℕ) : Wtot β D Y = Wminus β D Y + Wplus β D Y := by
  unfold Wtot Wminus Wplus; ring

lemma Wminus_eq (β D : ℝ) (Y : ℕ) : Wminus β D Y = Vsieve Y - Msum β D Y := rfl

lemma Wplus_eq (β D : ℝ) (Y : ℕ) : Wplus β D Y = Psum β D Y - Vsieve Y := rfl

/-! ## The weight of a chain -/

/-- On the chain `c` itself the weight `λ⁻` reproduces `(-1)^{|c|}` — the decreasing
factorisation of a square-free integer is unique (`chain_lprod_inj`). -/
lemma lamM_lprod {β D : ℝ} {Y : ℕ} {c : List ℕ} (hc : c ∈ Gm β D Y) :
    lamM β D Y (lprod c) = (-1 : ℝ) ^ c.length := by
  have hfilter : (Gm β D Y).filter (fun c' => lprod c' = lprod c) = {c} := by
    ext c'
    rw [Finset.mem_filter, Finset.mem_singleton]
    exact ⟨fun h => (chain_lprod_inj β Y D).2 c' h.1 c hc h.2, fun h => ⟨h ▸ hc, by rw [h]⟩⟩
  unfold lamM
  rw [hfilter, Finset.sum_singleton]

lemma lamP_lprod {β D : ℝ} {Y : ℕ} {c : List ℕ} (hc : c ∈ Gp β D Y) :
    lamP β D Y (lprod c) = (-1 : ℝ) ^ c.length := by
  have hfilter : (Gp β D Y).filter (fun c' => lprod c' = lprod c) = {c} := by
    ext c'
    rw [Finset.mem_filter, Finset.mem_singleton]
    exact ⟨fun h => (chain_lprod_inj β Y D).1 c' h.1 c hc h.2, fun h => ⟨h ▸ hc, by rw [h]⟩⟩
  unfold lamP
  rw [hfilter, Finset.sum_singleton]

@[simp] lemma lamM_one (β D : ℝ) (Y : ℕ) : lamM β D Y 1 = 1 := by
  simpa [lprod] using lamM_lprod (β := β) (D := D) (Y := Y) (c := ([] : List ℕ)) (nil_mem_Gm β D Y)

@[simp] lemma lamP_one (β D : ℝ) (Y : ℕ) : lamP β D Y 1 = 1 := by
  simpa [lprod] using lamP_lprod (β := β) (D := D) (Y := Y) (c := ([] : List ℕ)) (nil_mem_Gp β D Y)

/-- `lprod` of a list of odd numbers is odd. -/
lemma odd_lprod : ∀ {c : List ℕ}, (∀ q ∈ c, Odd q) → Odd (lprod c)
  | [], _ => by simp [lprod]
  | q :: l, h => by
      rw [lprod_cons]
      exact (h q List.mem_cons_self).mul (odd_lprod (fun x hx => h x (List.mem_cons_of_mem _ hx)))

/-- Elements of an upper-bound chain are odd primes. -/
lemma odd_of_mem_Gp {β D : ℝ} {Y : ℕ} {c : List ℕ} (hc : c ∈ Gp β D Y) :
    ∀ q ∈ c, Odd q := by
  intro q hq
  obtain ⟨hp, hp2, -⟩ := (chain_primes β Y D).1 c hc q hq
  exact hp.odd_of_ne_two hp2

/-- `λ⁻_d` vanishes on even `d`. -/
lemma lamM_eq_zero_of_even {β D : ℝ} {Y d : ℕ} (hd : d % 2 = 0) : lamM β D Y d = 0 := by
  unfold lamM
  refine Finset.sum_eq_zero (fun c hc => ?_)
  rw [Finset.mem_filter] at hc
  obtain ⟨hcg, hprod⟩ := hc
  exfalso
  have hodd := chain_prod_odd β D Y c hcg
  rw [hprod] at hodd
  omega

/-- `λ⁺_d` vanishes on even `d`. -/
lemma lamP_eq_zero_of_even {β D : ℝ} {Y d : ℕ} (hd : d % 2 = 0) : lamP β D Y d = 0 := by
  unfold lamP
  refine Finset.sum_eq_zero (fun c hc => ?_)
  rw [Finset.mem_filter] at hc
  obtain ⟨hcg, hprod⟩ := hc
  exfalso
  have hodd := Nat.odd_iff.mp (odd_lprod (odd_of_mem_Gp hcg))
  rw [hprod] at hodd
  omega

/-- Support of `λ⁻`: a non-vanishing weight forces `d` odd and `(d : ℝ) ≤ D`. -/
lemma lamM_support {β D : ℝ} {Y d : ℕ} (hβ : 0 ≤ β) (hD : 1 ≤ D)
    (hd : lamM β D Y d ≠ 0) : d % 2 = 1 ∧ (d : ℝ) ≤ D := by
  by_cases hodd : d % 2 = 1
  · refine ⟨hodd, ?_⟩
    by_contra hle
    push Not at hle
    have hempty : (Gm β D Y).filter (fun c => lprod c = d) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro c hc hpd
      have hsupp := (chain_support β hβ Y D hD).2 c hc
      rw [hpd] at hsupp
      exact absurd hsupp (not_le.mpr hle)
    unfold lamM at hd
    rw [hempty] at hd
    simp at hd
  · refine absurd hd ?_
    rw [lamM_eq_zero_of_even (d := d) ?_]
    exact fun h => h rfl
    omega

/-! ## The weights against the truncation sums and the minorant property -/

/-- The truncation sum `TmSum` regrouped by the value of the product: it is the sum of the
weights `λ⁻` against `d ∣ n`. -/
lemma TmSum_eq_lamM_sum (β D : ℝ) (Y n : ℕ) :
    TmSum β D Y n
      = ∑ d ∈ (Gm β D Y).image lprod, lamM β D Y d * (if d ∣ n then 1 else 0) := by
  rw [TmSum]
  symm
  rw [Finset.sum_image (f := fun d => lamM β D Y d * (if d ∣ n then 1 else 0))
        (g := lprod) (s := Gm β D Y) (chain_lprod_inj β Y D).2]
  refine Finset.sum_congr rfl (fun c hc => ?_)
  rw [lamM_lprod hc]

lemma TpSum_eq_lamP_sum (β D : ℝ) (Y n : ℕ) :
    TpSum β D Y n
      = ∑ d ∈ (Gp β D Y).image lprod, lamP β D Y d * (if d ∣ n then 1 else 0) := by
  rw [TpSum]
  symm
  rw [Finset.sum_image (f := fun d => lamP β D Y d * (if d ∣ n then 1 else 0))
        (g := lprod) (s := Gp β D Y) (chain_lprod_inj β Y D).1]
  refine Finset.sum_congr rfl (fun c hc => ?_)
  rw [lamP_lprod hc]

/-- The main term as a sum of weights: `Msum = Σ_d λ⁻_d/φ(d)`. -/
lemma Msum_eq_sum_lamM (β D : ℝ) (Y : ℕ) :
    Msum β D Y = ∑ d ∈ (Gm β D Y).image lprod, lamM β D Y d / (Nat.totient d : ℝ) := by
  rw [Msum]
  symm
  rw [Finset.sum_image (f := fun d => lamM β D Y d / (Nat.totient d : ℝ))
        (g := lprod) (s := Gm β D Y) (chain_lprod_inj β Y D).2]
  refine Finset.sum_congr rfl (fun c hc => ?_)
  rw [lamM_lprod hc]

lemma Psum_eq_sum_lamP (β D : ℝ) (Y : ℕ) :
    Psum β D Y = ∑ d ∈ (Gp β D Y).image lprod, lamP β D Y d / (Nat.totient d : ℝ) := by
  rw [Psum]
  symm
  rw [Finset.sum_image (f := fun d => lamP β D Y d / (Nat.totient d : ℝ))
        (g := lprod) (s := Gp β D Y) (chain_lprod_inj β Y D).1]
  refine Finset.sum_congr rfl (fun c hc => ?_)
  rw [lamP_lprod hc]

/-- **One-sidedness of `λ⁻`.**  The truncated weight sum is a minorant of the indicator of
coprimality with the odd primorial below the effective level. -/
lemma lamM_minorant (β D : ℝ) (hβ : 1 ≤ β) (hD : 0 ≤ D) (Y n : ℕ) :
    ∑ d ∈ (Gm β D Y).image lprod, lamM β D Y d * (if d ∣ n then 1 else 0)
      ≤ indP (eff D Y) n := by
  rw [← TmSum_eq_lamM_sum]
  exact (chain_sieve_bounds β hβ Y D hD n).1

/-- **One-sidedness of `λ⁺`.**  The truncated weight sum is a majorant of the indicator. -/
lemma lamP_majorant (β D : ℝ) (hβ : 1 ≤ β) (hD : 0 ≤ D) (Y n : ℕ) :
    indP (eff D Y) n
      ≤ ∑ d ∈ (Gp β D Y).image lprod, lamP β D Y d * (if d ∣ n then 1 else 0) := by
  rw [← TpSum_eq_lamP_sum]
  exact (chain_sieve_bounds β hβ Y D hD n).2

/-! ## Bridge to the `ChenEight` vocabulary used by the target statement -/

/-- The odd primes below `M`, in the two vocabularies of the workspace. -/
lemma oddPrimesLt_eq_oddLt (M : ℕ) : oddPrimesLt M = ChenEight.oddLt M := by
  ext p
  simp only [oddPrimesLt, ChenEight.oddLt, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    have hp2 : 2 ≤ p := h2.two_le
    rcases h2.eq_two_or_odd with h | h
    · exact absurd h h3
    · omega
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, by omega⟩

/-- The sift density `VsieveOdd` of the `ChenEight` vocabulary is `Vsieve` of the
`β`-sieve vocabulary. -/
lemma VsieveOdd_eq_Vsieve (M : ℕ) : ChenEight.VsieveOdd M = Vsieve M := by
  have h : ChenEight.oddLt M = oddPrimesLt M := (oddPrimesLt_eq_oddLt M).symm
  unfold ChenEight.VsieveOdd Vsieve
  rw [h]

/-- The sifted indicator `Id` of the `ChenEight` vocabulary is `indP`. -/
lemma Id_eq_indP (m M : ℕ) : ChenEight.Id m M = indP M m := by
  have h : ChenEight.oddPrimLt M = oddPrim M := by
    rw [ChenEight.oddPrimLt_eq_prod_oddLt]
    unfold oddPrim
    rw [← oddPrimesLt_eq_oddLt M]
  unfold ChenEight.Id indP
  rw [h]

/-! ## Elementary facts about the target's `goodSum` -/

lemma Id_eq_zero_or_one (m M : ℕ) : ChenEight.Id m M = 0 ∨ ChenEight.Id m M = 1 := by
  unfold ChenEight.Id
  split <;> simp

lemma goodSum_nonneg (x M : ℕ) : 0 ≤ ChenEight.goodSum x M := by
  unfold ChenEight.goodSum
  refine Finset.sum_nonneg (fun p hp => ?_)
  rw [Finset.mem_filter] at hp
  have hp2 : 2 ≤ p := hp.2.two_le
  have hlog : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
  rcases Id_eq_zero_or_one (p + 2) M with h | h <;> simp [h, hlog]

lemma VsieveOdd_nonneg (M : ℕ) : 0 ≤ ChenEight.VsieveOdd M := by
  rw [VsieveOdd_eq_Vsieve M]
  exact le_of_lt (Vsieve_pos M)

end
end Work.NumberTheory.Sieve.RosserLinear
