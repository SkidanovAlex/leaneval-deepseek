/-
# Area 4 (route `Area4_6c`): the smooth cut `uA`, its bump `psiA`, the weights `wA` and the junk cut

This is the vocabulary of the amended route to `Work.FITop4.Area4_6c` (design:
`Submission/Work/FIArea4/AREA4_ENGINES_LEAD.md` §3.2).  The sharp middle sum `Vcut` is split with
the *slower* smooth cut

  `uA t = S15u (3 t / 2)`   (`0` for `t ≤ 2/3`, `1` for `t ≥ 1`),

whose transition region `(2/3, 1)` is narrower than `S15u`'s `(1, 3/2)`.  The remainder of the
splitting is then

  `uA t − 1{1 < t}` (nonzero only on `(2/3, 1)`),
  `1{X < d}·(uA t − 1{1<t}) = 1{X<d}·1{t ≤ 1} − 1{X<d}·(1 − uA t)`,

and the second piece is expanded with the discrete Stieltjes measure

  `wA X m = uA((m+1)/X) − uA(m/X)   (m ∈ ℕ)`,

using `1 − uA(n/X) = Σ_{m ∈ Ico 1 X} wA X m·1{n ≤ m}` for the *integer* `n = |Δ|/(4d)` (which is
what `4d ∣ |Δ|` makes `t = |Δ|/(4Xd) = n/X`).  Since `Wcut m + Bcut m` is the cut
`1{m < d}·1{|Δ| ≤ 4dm}`, this turns the remainder into a convex combination of `Wcut m + Bcut m`
over `m < X` — each of which is handled by the *proved* area 7 — plus the `junk`

  `junkCut X m = 1{m < d ∧ d ≤ X ∧ |Δ| ≤ 4dm}`,

supported on `|Δ| ≤ 4Xm < 4X²`, `d ≤ X`, which is bounded crudely.
-/
import Mathlib
import Submission.Work.FIArea4.A6Defs
import Submission.Work.FIArea4.A6R2.Defs

namespace Work.FIArea4.A4c

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The slow cut `uA`, its bump `psiA` and the weights `wA` -/

/-- The smooth cut of the amended route: `uA t = S15u (3t/2)`, `0` for `t ≤ 2/3` and `1` for
`t ≥ 1`. -/
def uA (t : ℝ) : ℝ := S15u (3 * t / 2)

/-- The smooth bump of the amended splitting: `psiA s = uA s − uA (s/2)`, supported in
`(2/3, 2) ⊂ (1/2, 5/2)`. -/
def psiA (s : ℝ) : ℝ := uA s - uA (s / 2)

/-- The discrete weights of the remainder expansion: `wA X m = uA((m+1)/X) − uA(m/X)`. -/
def wA (X m : ℕ) : ℝ := uA (((m : ℝ) + 1) / (X : ℝ)) - uA ((m : ℝ) / (X : ℝ))

/-- The junk of the amended splitting: the cut `1{m < d ∧ d ≤ X ∧ |Δ(z₁,z₂)| ≤ 4dm}`, supported on
`d ≤ X` and `|Δ| ≤ 4Xm < 4X²`. -/
def junkCut (X m : ℕ) : GaussianInt → GaussianInt → ℕ → ℝ :=
  fun z1 z2 d =>
    if m < d ∧ d ≤ X ∧ Work.FIPlan.absDelta z1 z2 ≤ 4 * d * m then (1 : ℝ) else 0

/-! ## 2. Elementary properties of `uA` -/

lemma uA_contDiff : ContDiff ℝ (⊤ : ℕ∞) uA := by
  unfold uA
  exact S15u_contDiff.comp (by fun_prop)

lemma uA_zero {t : ℝ} (h : t ≤ 2 / 3) : uA t = 0 := by
  unfold uA
  refine S15u_zero ?_
  linarith

lemma uA_one {t : ℝ} (h : 1 ≤ t) : uA t = 1 := by
  unfold uA
  refine S15u_one ?_
  linarith

lemma uA_nonneg (t : ℝ) : 0 ≤ uA t := S15u_nonneg _

lemma uA_le_one (t : ℝ) : uA t ≤ 1 := S15u_le_one _

lemma uA_mono : Monotone uA := by
  intro s t hst
  unfold uA
  exact S15u_mono (by linarith)

/-! ## 3. Elementary properties of `psiA` -/

lemma psiA_contDiff : ContDiff ℝ (⊤ : ℕ∞) psiA := by
  unfold psiA
  exact uA_contDiff.sub (uA_contDiff.comp (by fun_prop))

lemma psiA_nonneg (s : ℝ) : 0 ≤ psiA s := by
  unfold psiA
  by_cases h : s ≤ 0
  · rw [uA_zero (by linarith), uA_zero (by linarith)]
    norm_num
  · push_neg at h
    exact sub_nonneg.mpr (uA_mono (by linarith))

lemma psiA_le_one (s : ℝ) : psiA s ≤ 1 := by
  unfold psiA
  have h1 := uA_le_one s
  have h2 := uA_nonneg (s / 2)
  linarith

lemma psiA_support {s : ℝ} (h : psiA s ≠ 0) : 1 / 2 < s ∧ s < 5 / 2 := by
  constructor
  · by_contra hc
    rw [not_lt] at hc
    exact h (by unfold psiA; rw [uA_zero (by linarith), uA_zero (by linarith)]; ring)
  · by_contra hc
    rw [not_lt] at hc
    exact h (by unfold psiA; rw [uA_one (by linarith), uA_one (by linarith)]; ring)

/-- `psiA` satisfies the support hypothesis of the §15 piece bound. -/
lemma psiA_support_half (y : ℝ) (hy : y ≤ 1 / 2 ∨ 5 / 2 ≤ y) : psiA y = 0 := by
  by_contra h
  have hs := psiA_support h
  rcases hy with h1 | h1 <;> linarith [hs.1, hs.2]

/-- The pointwise form of the definition of `psiA`. -/
lemma psiA_apply (s : ℝ) : psiA s = uA s - uA (s / 2) := rfl

/-! ## 4. Elementary properties of `wA` -/

lemma wA_nonneg (X m : ℕ) : 0 ≤ wA X m := by
  unfold wA
  refine sub_nonneg.mpr (uA_mono ?_)
  rcases Nat.eq_zero_or_pos X with hX | hX
  · subst hX; simp
  · have hXr : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
    have hle : (m : ℝ) ≤ (m : ℝ) + 1 := by linarith
    exact div_le_div_of_nonneg_right hle hXr.le

/-- If `uA((m+1)/X) = 0` and `uA(m/X) = 0` then `wA X m = 0`; equivalently a nonzero weight forces
`(m+1)/X > 2/3`. -/
lemma wA_eq_zero_of {X m : ℕ} (h : 3 * ((m : ℝ) + 1) ≤ 2 * (X : ℝ)) : wA X m = 0 := by
  unfold wA
  have h1 : ((m : ℝ) + 1) / (X : ℝ) ≤ 2 / 3 := by
    by_cases hX0 : X = 0
    · subst hX0; simp only [Nat.cast_zero, div_zero]; norm_num
    · have hXr : (0 : ℝ) < (X : ℝ) := by positivity
      rw [div_le_iff₀ hXr]
      linarith
  have h2 : (m : ℝ) / (X : ℝ) ≤ 2 / 3 := by
    have hm : (m : ℝ) ≤ (m : ℝ) + 1 := by linarith
    have h3 : (m : ℝ) / (X : ℝ) ≤ ((m : ℝ) + 1) / (X : ℝ) := by
      rcases Nat.eq_zero_or_pos X with hX | hX
      · subst hX; simp
      · exact div_le_div_of_nonneg_right hm (by exact_mod_cast hX.le)
    linarith
  rw [uA_zero h1, uA_zero h2]
  ring

lemma wA_support {X m : ℕ} (h : wA X m ≠ 0) : 2 * (X : ℝ) < 3 * ((m : ℝ) + 1) := by
  by_contra hc
  rw [not_lt] at hc
  exact h (wA_eq_zero_of hc)

/-! ## 5. The telescoping of the weights -/

/-- Telescoping of the weights: `Σ_{a ≤ m < b} wA X m = uA(b/X) − uA(a/X)`. -/
lemma sum_Ico_wA (X a b : ℕ) (hab : a ≤ b) :
    ∑ m ∈ Finset.Ico a b, wA X m = uA ((b : ℝ) / (X : ℝ)) - uA ((a : ℝ) / (X : ℝ)) := by
  have htel : ∀ N : ℕ,
      ∑ m ∈ Finset.range N, wA X m = uA ((N : ℝ) / (X : ℝ)) - uA (0 : ℝ) := by
    intro N
    induction N with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        have harg : (((n : ℝ) + 1) / (X : ℝ)) = (((n + 1 : ℕ) : ℝ)) / (X : ℝ) := by
          push_cast
          ring
        unfold wA
        rw [harg]
        ring
  have hsub : Finset.Ico a b = (Finset.range b) \ (Finset.range a) := by
    ext m
    simp only [Finset.mem_Ico, Finset.mem_sdiff, Finset.mem_range]
    omega
  have hsdiff2 : (∑ m ∈ Finset.range b \ Finset.range a, wA X m)
      = (∑ m ∈ Finset.range b, wA X m) - (∑ m ∈ Finset.range a, wA X m) := by
    have h := Finset.sum_sdiff (s₁ := Finset.range a) (s₂ := Finset.range b)
      (f := fun m => wA X m) (Finset.range_subset_range.mpr hab)
    linarith
  rw [hsub, hsdiff2, htel b, htel a]
  ring

/-- The weights sum to `1` (for `X ≥ 2`). -/
lemma sum_wA_eq_one (X : ℕ) (hX : 2 ≤ X) : ∑ m ∈ Finset.Ico 1 X, wA X m = 1 := by
  rw [sum_Ico_wA X 1 X (by omega)]
  have hXr : (0 : ℝ) < (X : ℝ) := by
    have : (0 : ℕ) < X := by omega
    exact_mod_cast this
  have h1 : ((X : ℝ)) / (X : ℝ) = 1 := by
    rw [div_self (ne_of_gt hXr)]
  have h2 : ((1 : ℕ) : ℝ) / (X : ℝ) ≤ 2 / 3 := by
    rw [div_le_iff₀ hXr]
    have : (1 : ℝ) ≤ 2 / 3 * 2 := by norm_num
    nlinarith [show (2 : ℝ) ≤ (X : ℝ) by exact_mod_cast hX]
  rw [h1, uA_one le_rfl, uA_zero h2]
  ring

/-- **The key identity of the remainder expansion.**  For an integer ratio `n/X` (`n = |Δ|/(4d)`),
`1 − uA(n/X) = Σ_{m ∈ Ico 1 X} wA X m·1{n ≤ m}`. -/
lemma one_sub_uA_div (X n : ℕ) (hX : 2 ≤ X) :
    1 - uA ((n : ℝ) / (X : ℝ))
      = ∑ m ∈ Finset.Ico 1 X, wA X m * (if n ≤ m then (1 : ℝ) else 0) := by
  by_cases hn : X ≤ n
  · -- `n ≥ X`: both sides vanish
    have hnX : (1 : ℝ) ≤ (n : ℝ) / (X : ℝ) := by
      rw [le_div_iff₀ (by exact_mod_cast (by omega : 0 < X))]
      have h : (X : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hz : (∑ m ∈ Finset.Ico 1 X, wA X m * (if n ≤ m then (1 : ℝ) else 0)) = 0 := by
      refine Finset.sum_eq_zero (fun m hm => ?_)
      rw [Finset.mem_Ico] at hm
      have hlt : ¬ n ≤ m := by omega
      rw [if_neg hlt, mul_zero]
    rw [uA_one hnX, show (1 : ℝ) - 1 = 0 by norm_num, hz]
  · have hnX : n < X := by omega
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · -- `n = 0`
      subst hn0
      have hsum : (∑ m ∈ Finset.Ico 1 X, wA X m * (if 0 ≤ m then (1 : ℝ) else 0))
          = ∑ m ∈ Finset.Ico 1 X, wA X m := by
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [if_pos (Nat.zero_le m), mul_one]
      rw [Nat.cast_zero, zero_div, uA_zero (by norm_num), hsum, sum_wA_eq_one X hX]
      norm_num
    · -- `1 ≤ n < X`
      have hsum : (∑ m ∈ Finset.Ico 1 X, wA X m * (if n ≤ m then (1 : ℝ) else 0))
          = ∑ m ∈ Finset.Ico 1 X, (if n ≤ m then wA X m else 0) := by
        refine Finset.sum_congr rfl (fun m _ => ?_)
        by_cases h : n ≤ m <;> simp [h]
      have hfil : (Finset.Ico 1 X).filter (fun m => n ≤ m) = Finset.Ico n X := by
        ext m
        simp only [Finset.mem_filter, Finset.mem_Ico]
        omega
      rw [hsum, ← Finset.sum_filter, hfil, sum_Ico_wA X n X hnX.le]
      have hXr : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
      rw [div_self (ne_of_gt hXr), uA_one le_rfl]

/-! ## 6. The three Prop-valued interfaces of the route

These are the *interfaces* (not the proofs) that the route's nodes are stated against, so that the
nodes can be dispatched and developed in parallel.
-/

/-- `DivBound Pa β T`: every finite set of divisors of a support point of `β` has at most `T`
elements.  With `T = 4·Pa.τ` this is furnished by the divisor count `card_dvd_finset_le` (the
squarefreeness `Squarefree (gnorm z)` of `IsBetaCoeff6.squarefree_gnorm` and the (5.9) clause
`τ(gnorm z) ≤ Pa.τ` of the coefficient), and it is the exact place where the route pays for the
Möbius summation over the divisor set `W`. -/
def DivBound (Pa : Work.FITop.Params) (β : GaussianInt → ℂ) (T : ℝ) : Prop :=
  ∀ z, β z ≠ 0 → ∀ W' : Finset GaussianInt, (∀ w ∈ W', w ∣ z) → (W'.card : ℝ) ≤ T

/-- **The variance half of the Möbius-split crux.**  For the *unfiltered* separated sum
`expSum6ng` of every restricted array `β_w` the proved `ExpBound6ng` applies, and the Gaussian
Möbius removal `moebiusSplit6` rewrites the *filtered* separated sum as the `(W,μ)`-sum of those
unfiltered sums.  Summing the resulting bound against the energy costs exactly the divisor count
`DivBound Pa β T`:

  `‖expSum6 Pa X j β ℓ u t‖ ≤ C(log N+1)^4 · S15Br6 Pa X · (T · A6Ener3 Pa β)`.

(No decay in `w` is used anywhere: the divisor count replaces the per-`w` dilation decay of the
abandoned `perW6b` route.) -/
def ExpBound6T : Prop :=
  ∃ C x0 : ℝ, 0 < C ∧ ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) →
  ∀ (X j : ℕ) (φ : ℝ) (β : GaussianInt → ℂ) (ℓ : ℤ) (u t T : ℝ),
    IsPrimBoxCoeff Pa φ β → 1 ≤ X → (X : ℝ) ≤ Pa.N ^ ((1 : ℝ) / 9) →
    DivBound Pa β T →
    ‖Work.FIArea4.A6R2.expSum6 Pa X j β ℓ u t‖
      ≤ C * (Real.log Pa.N + 1) ^ 4 * S15Br6 Pa X * (T * A6Ener3 Pa β)

/-- **The reduction half of §15, with the divisor factor `T` carried through.**  This is
`Work.FIArea4.A6RedProp` with `ExpBound6T` in place of `ExpBound6`: the exponents compose as
`2 + 2 + 4 = 8` and the extra factor `T` of the crux is carried to the right-hand side. -/
def A6RedTProp : Prop :=
  ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → (∀ y : ℝ, 0 ≤ ψ y) → (∀ y : ℝ, ψ y ≤ 1) →
    (∀ y : ℝ, (y ≤ 1 / 2 ∨ 5 / 2 ≤ y) → ψ y = 0) →
    ∃ C x0 : ℝ, 0 < C ∧ ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) →
      ∀ (X : ℕ) (φ : ℝ) (j : ℕ) (β : GaussianInt → ℂ) (T : ℝ),
        IsPrimBoxCoeff Pa φ β → DivBound Pa β T →
        1 ≤ X → (X : ℝ) ≤ Pa.N ^ ((1 : ℝ) / 9) →
        ‖Work.FITop4.Tcut (Work.FITop.radN Pa) (Work.FIArea4.A6cut ψ X j) β‖
          ≤ C * (Real.log Pa.N + 1) ^ 8 * S15Br6 Pa X * (T * A6Ener3 Pa β)

/-- **The divisor count** (`Work.FIArea4.A4c.card_dvd_finset_le`, proved in the sibling file
`A4c/card_dvd_finset_le.lean`): every finite set of divisors of a non-zero `z` with squarefree
norm has at most `4·τ(|z|²)` elements.  Named here so that the downstream nodes can be *stated*
against it and developed in parallel. -/
def CardDvdLe : Prop :=
  ∀ (z : GaussianInt), z ≠ 0 → Squarefree (Work.FIPlan.gnorm z) →
    ∀ W' : Finset GaussianInt, (∀ w ∈ W', w ∣ z) →
      (W'.card : ℝ) ≤ 4 * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)

/-- **The crude junk bound** (`Work.FIArea4.A4c.junk_le`, proved in the sibling file
`A4c/junk_le.lean`), named so that the remainder node can be stated against it and developed in
parallel. -/
def JunkBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (Pa : Work.FITop.Params) (φ : ℝ) (z0 : GaussianInt)
    (β : GaussianInt → ℂ) (X m : ℕ), Work.FITop4.IsBetaCoeff6 Pa φ z0 β → 1 ≤ m → m < X →
    ‖Work.FITop4.Tcut (Work.FITop.radN Pa) (junkCut X m) β‖
      ≤ C * Pa.τ ^ 2 * (X : ℝ) ^ 3 * Pa.N ^ ((3 : ℝ) / 2) * (Real.log Pa.N + 1)

end

end Work.FIArea4.A4c
