/-
# `Submission.Work.FIChain.RhoWin2Defs` — vocabulary of the `ρ`-window `Π`-removal

The endgame of `Submission/Work/FIChain/RhoWindowIntegrated2.lean` has to pass from the
`Π`-restricted Proposition 4.1 (`Work.FITop4.Prop41StatementPiBig`, the companion paper's (B*))
to the *unrestricted* integrated `ρ`-window of Theorem 3 of the companion paper (§10):

  `∫_{lo}^{hi} ∫_1^C Σ_c τ(c)² |Σ_{w<n≤2w, cn≤x} γ_σ(n) μ(cn) ã(cn)| dσ/σ dw/w ≪ Ã(x)(log x)^{-4}`

where `γ_σ(n) = Σ_{d | n, d ≤ σ} μ(d)` is the truncated Möbius weight of the companion's (B2).

The passage (the companion's §10) writes the inner variable as `n = n₀n₁` with `n₁ | Π` and
`(n₀, Π) = 1`; this file introduces the two objects the argument needs:

* `Xpg x Pz c σ u` — the `Π`-restricted window sum at the *real* position `u` and truncation `σ`,
  `Σ_{cn ≤ x, (n,Π)=1, u<n≤2u} μ(n)·γ_σ(n)·ã(cn)`; this is exactly the inner sum of `BformPi`
  when `u` is a natural number (see `Submission.Work.FIChain.RhoWin2Bounds`);
* `DpiC x = ⌈exp(2^40 (log log x)³)⌉` — the Rankin threshold `Δπ` of the `n₁`-split.

Everything here is definitions and elementary facts (no `sorry`, no `axiom`).
-/
import Mathlib
import Submission.Work.FIChain.Defs
import Submission.Work.FIChain.BpWinDefs
import Submission.Work.FITop.Defs

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The `Π`-restricted `γ`-window sum at the real position `u` and truncation `σ`:
`Xpg x Pz c σ u = Σ_{n : cn ≤ x, (n,Π)=1, u < n ≤ 2u} μ(n)·γ_σ(n)·ã(cn)`. -/
def Xpg (x Pz c : ℕ) (σ u : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 x).filter (fun n => c * n ≤ x ∧ Work.FITop4.PiCond Pz n ∧
      u < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ 2 * u),
    (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc σ n * atilc (c * n)

/-- The Rankin threshold `Δπ = ⌈exp(2^{40}(log log x)³)⌉` of the `n₁`-split (the companion's (10.2)
level; `κ = 2^{40}` as in `Submission.Work.FIChain.BprimeWindowIntegrated`). -/
def DpiC (x : ℕ) : ℕ := Dpi x ((2 : ℝ) ^ (40 : ℕ))

/-- `γ_σ(n) = 0` for `σ < 1`: the only divisors contributing are `≥ 1`. -/
lemma gammaTrunc_eq_zero_of_lt_one (σ : ℝ) (n : ℕ) (h : σ < 1) :
    Work.FIPlan.gammaTrunc σ n = 0 := by
  rw [Work.FIPlan.gammaTrunc]
  refine Finset.sum_eq_zero (fun d hd => ?_)
  rw [Finset.mem_filter, Nat.mem_divisors] at hd
  obtain ⟨⟨hdvd, hn⟩, hdle⟩ := hd
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hn)
  have h1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdpos
  linarith

/-- `Xpg` vanishes for `σ < 1`. -/
lemma Xpg_eq_zero_of_lt_one (x Pz c : ℕ) (σ u : ℝ) (h : σ < 1) : Xpg x Pz c σ u = 0 := by
  rw [Xpg]
  refine Finset.sum_eq_zero (fun n _ => ?_)
  rw [gammaTrunc_eq_zero_of_lt_one σ n h]; ring

/-- `Xpg` vanishes when the window `(u,2u]` contains no positive integer. -/
lemma Xpg_eq_zero_of_le (x Pz c : ℕ) (σ u : ℝ) (hu : 2 * u < 1) : Xpg x Pz c σ u = 0 := by
  rw [Xpg]
  refine Finset.sum_eq_zero (fun n hn => ?_)
  rw [Finset.mem_filter] at hn
  exfalso
  have h1 : (1 : ℝ) ≤ ((n : ℕ) : ℝ) := by
    exact_mod_cast (Finset.mem_Icc.mp hn.1).1
  linarith [hn.2.2.2]

/-- `Xpg` written as a sum over a `u`-independent index set with `u`-dependent `if`s. -/
lemma Xpg_eq_ite (x Pz c : ℕ) (σ u : ℝ) :
    Xpg x Pz c σ u = ∑ n ∈ (Finset.Icc 1 x).filter
        (fun n => c * n ≤ x ∧ Work.FITop4.PiCond Pz n),
      (if u < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ 2 * u
        then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc σ n * atilc (c * n)
        else 0) := by
  rw [Xpg, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun n _ => ?_)
  · ext n; simp only [Finset.mem_filter]; tauto
  · by_cases h : u < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ 2 * u <;>
      simp only [h, if_true, if_false, mul_zero]

/-- Measurability of `u ↦ Xpg x Pz c σ u`. -/
lemma measurable_Xpg (x Pz c : ℕ) (σ : ℝ) : Measurable (fun u : ℝ => Xpg x Pz c σ u) := by
  have h : (fun u : ℝ => Xpg x Pz c σ u) = fun u =>
      ∑ n ∈ (Finset.Icc 1 x).filter (fun n => c * n ≤ x ∧ Work.FITop4.PiCond Pz n),
        (if u < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ 2 * u
          then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc σ n * atilc (c * n)
          else 0) := by
    funext u; exact Xpg_eq_ite x Pz c σ u
  rw [h]
  refine Finset.measurable_sum _ (fun n _ => ?_)
  refine Measurable.ite ?_ measurable_const measurable_const
  exact (measurableSet_lt measurable_id measurable_const).inter
    (measurableSet_le measurable_const (measurable_const.mul measurable_id))

/-- The pointwise domination of `Xpg` by the unsigned window mass: drop the `Π`-condition, the
Möbius sign and replace `|γ_σ|` by `τ`. -/
lemma abs_Xpg_le_mass (x Pz c : ℕ) (σ u : ℝ) :
    |Xpg x Pz c σ u| ≤ ∑ n ∈ (Finset.Icc 1 x).filter
        (fun n => c * n ≤ x ∧ u < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ 2 * u),
      ((n.divisors.card : ℝ)) * atilc (c * n) := by
  rw [Xpg]
  have hsub : (Finset.Icc 1 x).filter (fun n => c * n ≤ x ∧ Work.FITop4.PiCond Pz n ∧
        u < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ 2 * u)
      ⊆ (Finset.Icc 1 x).filter
        (fun n => c * n ≤ x ∧ u < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ 2 * u) := by
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, hn.2.1, hn.2.2.2.1, hn.2.2.2.2⟩
  have hγ : ∀ n : ℕ, |Work.FIPlan.gammaTrunc σ n| ≤ ((n.divisors.card : ℝ)) := by
    intro n
    rw [Work.FIPlan.gammaTrunc]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have h1 : (∑ d ∈ n.divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ σ),
          |(ArithmeticFunction.moebius d : ℝ)|)
        ≤ ∑ d ∈ n.divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ σ), (1 : ℝ) :=
      Finset.sum_le_sum (fun d _ => by
        have h := ArithmeticFunction.abs_moebius_le_one (n := d)
        exact_mod_cast h)
    have h2 : (∑ _d ∈ n.divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ σ), (1 : ℝ))
        ≤ ∑ _d ∈ n.divisors, (1 : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by norm_num)
    have h3 : (∑ _d ∈ n.divisors, (1 : ℝ)) = ((n.divisors.card : ℝ)) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    linarith [h1, h2, h3]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine le_trans (Finset.sum_le_sum (fun n _ => ?_))
    (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun i _ _ => mul_nonneg (Nat.cast_nonneg _) (Work.FITop.atilFIa_nonneg _)))
  have hμ : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
    have h := ArithmeticFunction.abs_moebius_le_one (n := n)
    exact_mod_cast h
  have hã0 : 0 ≤ atilc (c * n) := Work.FITop.atilFIa_nonneg _
  rw [abs_mul, abs_mul]
  calc |(ArithmeticFunction.moebius n : ℝ)| * |Work.FIPlan.gammaTrunc σ n| * |atilc (c * n)|
      ≤ 1 * ((n.divisors.card : ℝ)) * |atilc (c * n)| := by
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul hμ (hγ n) (abs_nonneg _) (by norm_num)) (abs_nonneg _)
    _ = ((n.divisors.card : ℝ)) * atilc (c * n) := by
        rw [abs_of_nonneg hã0]; ring

/-- `Xpg` at an integer position is the window `(N, 2N]` with `N` a natural number. -/
lemma Xpg_natCast (x Pz c : ℕ) (σ : ℝ) (N : ℕ) :
    Xpg x Pz c σ ((N : ℕ) : ℝ) = ∑ n ∈ (Finset.Icc 1 x).filter
        (fun n => c * n ≤ x ∧ Work.FITop4.PiCond Pz n ∧ N < n ∧ n ≤ 2 * N),
      (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc σ n * atilc (c * n) := by
  rw [Xpg]
  refine Finset.sum_congr ?_ (fun n _ => rfl)
  ext n
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, ?_, ?_⟩
    · exact_mod_cast h3
    · exact_mod_cast h4
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, by exact_mod_cast h3, by exact_mod_cast h4⟩

/-! ## The integrands of the `ρ`-window `Π`-removal

After the identity `RhoWin2Ident` the `ρ`-window integrand is dominated by the `Π`-split sum
`Wall`, and the companion's §10 splits `Wall = Wmain + Wtail` according to `n₁ ≤ Δπ` / `n₁ > Δπ`. -/

/-- The `n₁ ≤ Δ` part of the `Π`-split integrand of the integrated `ρ`-window. -/
def Wmain (x Pz : ℕ) (Δ : ℝ) (s t : ℝ) : ℝ :=
  ∑ c ∈ Finset.Icc 1 x, ((c.divisors.card : ℝ)) ^ 2 *
    ∑ n₁ ∈ (ProdP Pz).divisors.filter (fun n₁ : ℕ => (n₁ : ℝ) ≤ Δ),
      ∑ d₁ ∈ n₁.divisors, |Xpg x Pz (c * n₁) (s / d₁) (t / n₁)|

/-- The `n₁ > Δ` part of the `Π`-split integrand of the integrated `ρ`-window. -/
def Wtail (x Pz : ℕ) (Δ : ℝ) (s t : ℝ) : ℝ :=
  ∑ c ∈ Finset.Icc 1 x, ((c.divisors.card : ℝ)) ^ 2 *
    ∑ n₁ ∈ (ProdP Pz).divisors.filter (fun n₁ : ℕ => Δ < (n₁ : ℝ)),
      ∑ d₁ ∈ n₁.divisors, |Xpg x Pz (c * n₁) (s / d₁) (t / n₁)|

/-- The full `Π`-split integrand: the sum over all divisors `n₁` of `Π`. -/
def Wall (x Pz : ℕ) (s t : ℝ) : ℝ :=
  ∑ c ∈ Finset.Icc 1 x, ((c.divisors.card : ℝ)) ^ 2 *
    ∑ n₁ ∈ (ProdP Pz).divisors,
      ∑ d₁ ∈ n₁.divisors, |Xpg x Pz (c * n₁) (s / d₁) (t / n₁)|

/-- `Wall = Wmain + Wtail`. -/
lemma Wall_eq_Wmain_add_Wtail (x Pz : ℕ) (Δ : ℝ) (s t : ℝ) :
    Wall x Pz s t = Wmain x Pz Δ s t + Wtail x Pz Δ s t := by
  rw [Wall, Wmain, Wtail, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [← mul_add]
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not (s := (ProdP Pz).divisors)
    (p := fun n₁ : ℕ => (n₁ : ℝ) ≤ Δ)]
  congr 1
  simp only [not_le]

/-- `Wall` is nonnegative. -/
lemma Wall_nonneg (x Pz : ℕ) (s t : ℝ) : 0 ≤ Wall x Pz s t := by
  rw [Wall]
  exact Finset.sum_nonneg (fun c _ => mul_nonneg (by positivity)
    (Finset.sum_nonneg (fun n₁ _ => Finset.sum_nonneg (fun d₁ _ => abs_nonneg _))))

/-- `Wmain` is nonnegative. -/
lemma Wmain_nonneg (x Pz : ℕ) (Δ s t : ℝ) : 0 ≤ Wmain x Pz Δ s t := by
  rw [Wmain]
  exact Finset.sum_nonneg (fun c _ => mul_nonneg (by positivity)
    (Finset.sum_nonneg (fun n₁ _ => Finset.sum_nonneg (fun d₁ _ => abs_nonneg _))))

/-- `Wtail` is nonnegative. -/
lemma Wtail_nonneg (x Pz : ℕ) (Δ s t : ℝ) : 0 ≤ Wtail x Pz Δ s t := by
  rw [Wtail]
  exact Finset.sum_nonneg (fun c _ => mul_nonneg (by positivity)
    (Finset.sum_nonneg (fun n₁ _ => Finset.sum_nonneg (fun d₁ _ => abs_nonneg _))))

/-- Measurability of `σ ↦ γ_σ(n)`. -/
lemma measurable_gammaTrunc (n : ℕ) : Measurable (fun σ : ℝ => Work.FIPlan.gammaTrunc σ n) := by
  rw [show (fun σ : ℝ => Work.FIPlan.gammaTrunc σ n) = fun σ =>
      ∑ d ∈ n.divisors,
        (if ((d : ℕ) : ℝ) ≤ σ then (ArithmeticFunction.moebius d : ℝ) else 0) from by
    funext σ; rw [Work.FIPlan.gammaTrunc, Finset.sum_filter]]
  exact Finset.measurable_sum _ (fun d _ =>
    Measurable.ite (measurableSet_le measurable_const measurable_id)
      measurable_const measurable_const)

/-- Measurability of `(σ,u) ↦ Xpg x Pz c σ u`. -/
lemma measurable_Xpg_pair (x Pz c : ℕ) :
    Measurable (fun p : ℝ × ℝ => Xpg x Pz c p.1 p.2) := by
  rw [show (fun p : ℝ × ℝ => Xpg x Pz c p.1 p.2) = fun p : ℝ × ℝ =>
      ∑ n ∈ (Finset.Icc 1 x).filter (fun n => c * n ≤ x ∧ Work.FITop4.PiCond Pz n),
        (if p.2 < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ 2 * p.2 then
          (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc p.1 n * atilc (c * n)
          else 0) from by
    funext p; exact Xpg_eq_ite x Pz c p.1 p.2]
  refine Finset.measurable_sum _ (fun n _ => ?_)
  refine Measurable.ite ?_ ?_ measurable_const
  · exact (measurableSet_lt measurable_snd measurable_const).inter
      (measurableSet_le measurable_const (measurable_const.mul measurable_snd))
  · exact Measurable.mul (Measurable.mul measurable_const ((measurable_gammaTrunc n).comp measurable_fst))
      measurable_const

end

end Work.FIChain
