/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team.

# `Work.Peluse.Ulower.gap_localise` — the vocabulary of the gap-regime localisation

This module holds the two definitions on which the *localisation* of the gap-regime box-norm
hypothesis to a **balanced** block is phrased (`Submission/Work/Peluse/Ulower/gap_local_block.lean`),
and which the balanced core of the extraction consumes.

## The mathematical point

In the gap regime (`2 N^d < N₀`, i.e. the support `N₀` is much larger than the polynomial scale
`N^d`), the "many shift tuples" hypothesis `ManyShiftsHypδ P s N₀ N D f₀ f₁ δ` is a statement about
the *big* box `symIcc (dSup P N₀ N)`.  But every *configuration* of the box norm uses only the
values of the dual function `F₂ = dualFn N P f₀ f₁` on an interval of length

  `K := (s-2)·|lc P|·D + dSup P Ns N  ≍ N^d   (because `D ≤ N^d`)`

around the point `x`.  Hence the box sum over the big box is a *sum over blocks of length `≍ N^d`*
of the corresponding box sums of the **localised** functions `gapLocalise f a Ns`
(`= f(· + a)` truncated to `symIcc Ns`), each of which is 1-bounded and supported in `symIcc Ns`
with `Ns ≍ N^d` — i.e. **balanced**.  A pigeonhole over the finitely many blocks then produces a
*single* block on which the whole "many shift tuples" hypothesis holds (with the level and the
density both multiplied by a constant depending only on `s` and `P`).

This is what makes the gap regime reduce to the *balanced* chapter (Peluse's Lemma 3.9 + §9) rather
than requiring a separate, scale-free §9.

## Contents

* `gapLocalise f a L` — the translate-and-truncate of `f` to the window `symIcc L`;
* `ManyShiftsHypDensity P s N₀ N D f₀ f₁ δ γ` — the "many shift tuples" hypothesis with the level
  `δ` and the density `γ` *decoupled* (the form produced by the pigeonhole over the blocks), with
  `manyShiftsHypDensity_of_hypδ` recording that `ManyShiftsHypδ` is the case
  `δ = δ/4`, `γ = δ/(4(1+s+|lc P|))`.
-/
import Mathlib
import Submission.Work.Peluse.Ulower.gap_defs

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.Ulower

noncomputable section

open Work.Peluse

/-- Membership in the symmetric interval `symIcc L`. -/
lemma mem_symIcc_iff {L : ℕ} {x : ℤ} : x ∈ symIcc L ↔ x.natAbs ≤ L := by
  rw [symIcc, Finset.mem_Icc]
  constructor
  · intro h
    have h1 : |x| ≤ (L : ℤ) := abs_le.mpr h
    rw [← Int.natCast_natAbs] at h1
    exact_mod_cast h1
  · intro hx
    have h1 : (x.natAbs : ℤ) ≤ (L : ℤ) := by exact_mod_cast hx
    rw [Int.natCast_natAbs] at h1
    exact abs_le.mp h1

/-- **The window localisation of a function.**  `gapLocalise f a L` is the translate `x ↦ f (x + a)`
truncated to the window `symIcc L = [-L,L]` (and zero outside).  It is the piece of `f` seen by the
configurations of the box norm that live in the interval `[-L+a, L+a]`. -/
def gapLocalise (f : ℤ → ℂ) (a : ℤ) (L : ℕ) : ℤ → ℂ :=
  fun x => if x ∈ symIcc L then f (x + a) else 0

lemma gapLocalise_apply_of_mem {f : ℤ → ℂ} {a : ℤ} {L : ℕ} {x : ℤ} (hx : x ∈ symIcc L) :
    gapLocalise f a L x = f (x + a) := by
  simp [gapLocalise, hx]

lemma gapLocalise_apply_of_not_mem {f : ℤ → ℂ} {a : ℤ} {L : ℕ} {x : ℤ} (hx : x ∉ symIcc L) :
    gapLocalise f a L x = 0 := by
  simp [gapLocalise, hx]

/-- `gapLocalise f a L` is supported in `symIcc L`. -/
lemma supportIn_gapLocalise_self (f : ℤ → ℂ) (a : ℤ) (L : ℕ) :
    SupportIn (gapLocalise f a L) L := by
  intro x hx
  exact gapLocalise_apply_of_not_mem
    (fun hmem => absurd (mem_symIcc_iff.mp hmem) (not_le.mpr hx))

/-- `gapLocalise f a L` is 1-bounded whenever `f` is. -/
lemma norm_gapLocalise_le_one {f : ℤ → ℂ} (hf : ∀ x : ℤ, ‖f x‖ ≤ 1) (a : ℤ) (L : ℕ) :
    ∀ x : ℤ, ‖gapLocalise f a L x‖ ≤ 1 := by
  intro x
  by_cases hx : x ∈ symIcc L
  · rw [gapLocalise_apply_of_mem hx]; exact hf _
  · rw [gapLocalise_apply_of_not_mem hx]; simp

/-- **The "many shift tuples" hypothesis**, with the level `δ` and the density `γ` decoupled.

There is a set `H` of shift tuples (each entry in the shift set `arithIcc P.leadingCoeff D`) of
relative size at least `γ` such that for every `sh ∈ H` the *level-two* box norm of the iterated
difference `iterDelta (s-2) sh (dualFn N P f₀ f₁)` over the big box `symIcc (dSup P N₀ N)` is at
least `δ`.

This is the form produced by the pigeonhole over the blocks of the gap-regime localisation: the
block carrying the mass of the box norm has the level multiplied by a constant and the density by a
constant, both depending only on `s` and `P`.  The original interface `ManyShiftsHypδ` of the peel
is the case `δ = δ/4`, `γ = δ/(4(1+s+|lc P|))` (`manyShiftsHypDensity_of_hypδ`). -/
def ManyShiftsHypDensity (P : Polynomial ℤ) (s N₀ N D : ℕ) (f₀ f₁ : ℤ → ℂ) (δ γ : ℝ) : Prop :=
  ∃ H : Finset (Fin (s - 2) → ℤ × ℤ),
    (∀ sh ∈ H, ∀ i, (sh i).1 ∈ Work.Peluse.arithIcc P.leadingCoeff D ∧
      (sh i).2 ∈ Work.Peluse.arithIcc P.leadingCoeff D) ∧
    γ * (((Work.Peluse.arithIcc P.leadingCoeff D).card : ℝ)) ^ (2 * (s - 2)) ≤ (H.card : ℝ) ∧
    (∀ sh ∈ H, δ ≤ Work.Peluse.boxNormPow 2
      (fun _ : Fin 2 => Work.Peluse.arithIcc P.leadingCoeff D)
      (Work.Peluse.symIcc (Work.Peluse.dSup P N₀ N))
      (iterDelta (s - 2) sh (Work.Peluse.dualFn N P f₀ f₁)))

/-- `ManyShiftsHypδ P s N₀ N D f₀ f₁ δ` is `ManyShiftsHypDensity` with level `δ/4` and density
`δ/4/(1+s+|lc P|)`. -/
theorem manyShiftsHypDensity_of_hypδ {P : Polynomial ℤ} {s N₀ N D : ℕ} {f₀ f₁ : ℤ → ℂ}
    {δ : ℝ} (h : ManyShiftsHypδ P s N₀ N D f₀ f₁ δ) :
    ManyShiftsHypDensity P s N₀ N D f₀ f₁ (δ / 4) (δ / 4 / (1 + (s : ℝ) + |((P.leadingCoeff : ℤ) : ℝ)|)) := by
  obtain ⟨H, h1, h2, h3⟩ := h
  exact ⟨H, h1, h2, h3⟩


/-! ## The support of a progression average -/

/-- The reverse triangle inequality `|a| ≤ |a + b| + |b|` for `ℤ`. -/
private lemma abs_le_abs_add_add (a b : ℤ) : |a| ≤ |a + b| + |b| := by
  have h := abs_add_le (a + b) (-b)
  have h2 : |(a + b) + (-b)| = |a| := by ring_nf
  rw [h2, abs_neg] at h
  simpa using h

/-- **The support of a progression average.**  If `f` vanishes off `symIcc N₀`, then
`progAvg N' q f` vanishes off `symIcc (N₀ + N'·|q|)`:  a point `x` with
`|x| > N₀ + N'|q|` has `|x + q m| ≥ |x| - |q| m > N₀` for every `1 ≤ m ≤ N'`, so every term of the
average vanishes. -/
theorem progAvg_supportIn' {f : ℤ → ℂ} {N₀ : ℕ} (h : SupportIn f N₀) {N' : ℕ} (q : ℤ) :
    SupportIn (Work.Peluse.progAvg N' q f) (N₀ + N' * q.natAbs) := by
  intro x hx
  rw [Work.Peluse.progAvg, Finset.sum_eq_zero (fun m hm => ?_), mul_zero]
  apply h
  have hm2 : (m : ℤ) ≤ (N' : ℤ) := by exact_mod_cast (Finset.mem_Icc.mp hm).2
  have hxZ : ((N₀ + N' * q.natAbs : ℕ) : ℤ) < (x.natAbs : ℤ) := by exact_mod_cast hx
  have hqnn : (0 : ℤ) ≤ (q.natAbs : ℤ) := by positivity
  have hmnn : (0 : ℤ) ≤ (m : ℤ) := by
    have : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    linarith
  have htri : |x| ≤ |x + q * (m : ℤ)| + |q * (m : ℤ)| := abs_le_abs_add_add x (q * (m : ℤ))
  have hqm : |q * (m : ℤ)| = (q.natAbs : ℤ) * (m : ℤ) := by
    rw [abs_mul]
    have h1 : (|q| : ℤ) = (q.natAbs : ℤ) := (Int.natCast_natAbs q).symm
    have h2 : (|(m : ℤ)| : ℤ) = (m : ℤ) := abs_of_nonneg hmnn
    rw [h1, h2]
  have hxabs : |x| = (x.natAbs : ℤ) := (Int.natCast_natAbs x).symm
  have hkey : ((N₀ : ℤ)) < |x + q * (m : ℤ)| := by
    have h1 : ((N₀ + N' * q.natAbs : ℕ) : ℤ) < |x| := by rw [hxabs]; exact hxZ
    have h2 : ((N₀ + N' * q.natAbs : ℕ) : ℤ) = (N₀ : ℤ) + (N' : ℤ) * (q.natAbs : ℤ) := by
      push_cast; ring
    rw [h2] at h1
    rw [hqm] at htri
    nlinarith [htri, h1, hm2, hqnn]
  rw [← Int.natCast_natAbs (x + q * (m : ℤ))] at hkey
  exact_mod_cast hkey

end

end Work.Peluse.Ulower
