import Mathlib
import Submission.Work.Peluse.UControl.assembly
import Submission.Work.Peluse.Pairing.boxSumPow_neg_directions
import Submission.Work.Peluse.Ulower.boxSumPow_neg
import Submission.Work.Peluse.TransferUp.arithIcc_pairSum
import Submission.Work.Peluse.Track.boxNormPow_one_arithIcc_window
import Submission.Work.Peluse.Concat.TransferDefs
import Submission.Work.Peluse.MajorArc.Defs
import Submission.Work.Peluse.Peel.arithIcc_sum_window_eq
import Submission.Work.Peluse.UControl.diagMassDefs

/-!
# `Work.Peluse.UControl.bandCore`

The requested statement is the **box-norm form of the coarse-scale inverse theorem** for the
bilinear average `Λ^{N₁,N}_{X,P}(g₀,g₁,g₂)`: from the hypotheses `Hyp` of
`Work.Peluse.UControl.CoreChapter` (the scale relations `N₁ ≍_{A'} N^d`, the window
`1 ≤ ⌊δ'N⌋`, the smallness `C·dirLen ≤ γ^K N₁`, the PET non-degeneracy `C ≤ (γδ')^K(δ'N)²`,
and the correlation `γ ≤ ‖Λ(g₀,g₁,g₂)‖`) it asks, with `K₀`, `c` **independent of `A'` and `C`**,

  `c * γ ^ K₀ ≤ uNormPow s (arithIcc (dirCoeff P) (dirLen P δ' N)) (symIcc N₁) g₂`.

## What this file contains (summary of the state, 2026)

* `coherence_gauge_period` (**proved**): the gauge-period identity of the exact-coherence relation
  `g₀(x)g₁(x+y)g₂(x+P(y)) = λ ≠ 0`: comparing the relation at `(x,y)` and at `(x+k,y−k)` (the
  `g₁`-argument `x+y` is common, so the `g₁`-factors cancel) gives
  `g₀(x+k)·g₂(x+k+P(y−k)) = g₀(x)·g₂(x+P(y))`, i.e. `g₂` is invariant under the shift
  `Δ = P(y) − P(y−k) − k` along the curve, up to the `g₀`-gauge.  This is the algebraic heart of
  the rigidity/chaining step of the coarse-scale inverse theorem.  (The number-theoretic companion
  — that an integer dividing the periods divides `(deg P)!·lc P` — is already proved in the
  workspace as `Work.Peluse.UControl.shift_dvd_dirCoeff_of_two_le_natDegree`.)

* `cubeAligned` (proved in `Submission/Work/Peluse/UControl/cubeAligned.lean`; delegated from this
  session): if the cube terms at the lower corners `x ∈ B` have real part at least `‖f x‖^{2^s} − ε`
  and the cube terms outside `B` have nonnegative real part, then
  `|S|⁻¹ ∑_{x∈B}(‖f x‖^{2^s} − ε) ≤ uNormPow s Q S f` — the "structure ⟹ box norm" mechanism,
  with **no** `|Q|^{-s}` loss.  Together with `coherence_gauge_period` (and its quantitative
  version) this is the last step of the rigidity argument.

## What this file contains

* `peel_bound` (**proved**): the *elementary* bound for the box-norm power,
  `c₁ * γ^(2^s) / L^s ≤ uNormPow s (κ[L]) (symIcc N₁) g₂` with the *explicit* constant
  `c₁ = 9^{-2^{s-1}}` (`Work.Peluse.UControl.elementary_bound_v2`), obtained from the correlation
  hypothesis alone through its consequence `γ²N₁/3 ≤ ∑_{symIcc N₁}‖g₂‖²`
  (`Work.Peluse.UControl.mass_bound_of_lambdaZ`) and the diagonal peel of the Gowers box norm.
  This disposes of the regime `L^s ≤ (c₁/c)·γ^{2^s-K₀}` (see `hardCase_of_peel_etc` below).

* `BandHard` (**the open input**): the complementary regime, i.e. the statement of the target with
  the peel regime removed.  This is the coarse-scale inverse theorem: the box norm at a *large*
  direction length `L = ⌊δ'N^d⌋` must be bounded below by a power of the correlation, uniformly in
  the scale imbalance `A'` and in `C`.

* `uNormPow_window_ratio` (**proved**): the window `S` of the box-norm power enters the definition
  of `prodCubeSum` *only* through the factor `|S|⁻¹`; hence
  `uNormPow t Q S f = (|S'|/|S|) · uNormPow t Q S' f` for any nonempty `S'`.  (This is why the
  `∑'_x` in the definition is over all of `ℤ`.)

* `uNormPow_level_raise_win` (**proved**): **level raising with window slack.**  The proved
  `uNormPow_level_raise` (`assembly.lean`) needs the fit `∀ a ∈ Q, |a| ≤ N` in the window `symIcc N`;
  in the band the fit `|dirCoeff P|·dirLen ≤ N₁` may fail.  It is only needed at the *larger* window
  `symIcc (max N (L |κ|))`, where it is automatic for `Q = κ[L]` with `L ≤ N`; transporting back with
  `uNormPow_window_ratio` costs the *constant* `(2 max 1 |κ| + 1)^{2^{s-s₀}-1}` (because `Hyp` gives
  `L ≤ N₁`).  So the level raising is available in the band, at the price of a constant.

* `bandCore_of_levelTwo` (**proved**): **the level reduction.**  The target at any level `s ≥ 2`
  follows from its level-`2` instance (with `K₀ := K₂·2^{s-2}`), by iterating
  `uNormPow_level_raise_win`.  This is scale preserving in the direction set, so *no §5
  concatenation* (which would change `⌊δ'N⌋` into `⌊δ'N^{deg P}⌋`) is involved: the level is free.
  Consequently the single remaining input of this file is stated at the fixed level `2`.

* `bandCore` (the requested statement) — currently **open**; it follows from `BandHard` and
  `peel_bound` by the elementary dichotomy in `bandCore_of_hard` (input at level `s`), or — as wired
  now — from the level-`2` input `BandHardSharpAt 2 P cdiag cpeel` together with the level-`2`
  elementary bounds, by `bandCore_of_sharp 2` followed by `bandCore_of_levelTwo`.  So the single
  remaining input is the **level-`2`** instance of the coarse-scale inverse theorem, and
  `Submission/Work/Peluse/UControl/levelTwoSufficient.lean` shows that it also suffices for the
  area's inputs `HardInputAt s P` at all levels and for `CoreChapter P`.

  **The current single `sorry` sits on the *residual* `ResidSharpEx P cdiag cpeel`** (see the
  section "The residual" below): the level-`2` inverse theorem restricted to the `Hyp`-data whose
  third function `g₂` satisfies the *two elementary-branch complements* of this file — no Fourier
  coefficient of size `(1/2)γ^{K₀/4}N₁` (a threshold *smaller* than the area's `NoLargeFourier`,
  hence implied by it) and level-one box-norm power `< (1/2)γ^{K₀/2}` — and on which the two
  elementary bounds (the diagonal `diagBound_of_hyp` and the peel `peel_bound`) do not already
  suffice.  Both complementary branches are *proved* in-file:
  `uNormPow_two_ge_of_charCorr_thr` (modulation invariance + the level-two mean bound, at an
  arbitrary threshold) and `uNormPow_two_ge_of_uNorm_one` (Gowers–Cauchy–Schwarz level raising).

  **The obligation is the area's named input**: `Submission/Work/Peluse/UControl/bandCoreFromSF.lean`
  proves `BandStructureSF P 2 → ResidSharpEx P cdiag cpeel` and
  `(∀ P, 2 ≤ P.natDegree → BandStructureSF P 2) → ⟨the conclusion of bandCore, at every level⟩`.
  Since `BandStructureSF P s` is `BandStructure P s` + `NoLargeFourier` and `BandStructure P s` is
  *verbatim* the conclusion of `bandCore` (`bandStructure_of_bandCore` gives the other direction),
  the whole band reduces to the single unconditional statement `BandStructureSF`.  (The residual is
  strictly *weaker* than `BandStructureSF`: its domain is the sub-domain where the two further
  elementary branches are silent.)

  What is still open at level `2` (nothing elementary reaches it): the sharp bound
  `uNormPow 2 (κ[L]) (symIcc N₁) g₂ ≳ γ^{K₀}`, i.e. the diagonal bound
  `uNormPow 2 ≥ cγ⁴/L` (`diagBound_of_hyp` at `s = 2`) must be improved by a factor `L`.  The
  density family (`g₀ = g₁ = 1`, `g₂ = 1_A` of density `ρ`, `γ ≈ ρ`) has
  `uNormPow 2 = ρ⁴ = γ⁴`, so this is sharp; on the other side the periodic family shows that
  *no* bound at level `1` can suffice.  `uNormPow_two_eq_shiftAvg`
  (`Submission/Work/Peluse/UControl/uNormPow_two_eq_shiftAvg.lean`) exhibits the level-`2` norm as
  the average `|Q|⁻²∑_{h,h'∈Q} uNormPow 1 Q S (f(·+h)·conj(f(·+h')))`, which makes the gap exactly
  "the off-diagonal shifts `h ≠ h'` must carry as much mass as the diagonal `h = h'`".

* `BandDenseStructure s P` (**REFUTED** — do not attempt to prove it): the previous session's
  "dense phase structure" (`g₂ ≈ ω·h` with `ω` `dirCoeff P`-periodic and `h ≥ 0` real), from which
  `BandHard` follows via the proved flat arm `phaseToBox` and mass bound `massOfHyp`
  (`bandHard_of_denseStructure` below).  The implication is true but **vacuous**: the hypothesis is
  false already at `s = 2`, `P = X²` — the `4`-periodic character `g₂ x = i^x` satisfies all of
  `Hyp` (with `‖Λ‖ ≈ 1.2718 ≥ 1`) but is not a `2`-periodic phase times a non-negative function.
  See the refutation immediately above `BandDenseStructure` below and the formal statement
  `Work.Peluse.UControl.bandDenseStructureFalse`.

## Why the elementary bounds do not settle the target

At level `2` the elementary bounds are `uNormPow 2 ≥ c·γ^4/L` (`diagBound_of_hyp`, fit-free) and, for
small `γ`, the peel `uNormPow 2 ≥ c₁γ^4/L²`.  Both lose a power of `L = dirLen P δ' N`, while `Hyp`
only gives `L ≤ γ^{K₀}N₁`, so for `L` large (e.g. `L ≈ γ^{K₀}N₁ ≈ N^d`, which the PET non-degeneracy
`C ≤ (γδ')^K(δ'N)²` together with `C·L ≤ γ^K N₁` *forces*: `L ≳ N^{d-o(1)}`) the gap is exactly the
factor `L`.  No elementary argument (the mass bound, the power mean, the modulation invariance
`uNormPow_mul_ee`, the fit-free diagonal peel, or the invariance-implies-box-norm lemmas) closes it:
the missing ingredient is the *structure* of `g₂` forced by the correlation
`γ ≤ ‖Λ(g₀,g₁,g₂)‖` with `g₀,g₁` arbitrary — i.e. Peluse's inverse theorem (arXiv:1909.00309,
Thm 3.3/3.7) *without* the scale-imbalance losses of the source's statement; the direction set must
be grown from the van der Corput scale `N` to the target scale `⌊δ'N^{deg P}⌋`.

Two formulations that were tried and are **refuted** (do not re-attempt): `BandDenseStructure`
(below, and `bandDenseStructureFalse.lean`) and the area's `BandDenseStructureInput`
(`bandDenseStructureInputFalse.lean`).  See `NOTES_UControl_bandCore.md` and
`NOTES_bandCore_SESSION*.md` at the workspace root.
-/

set_option autoImplicit false
open scoped BigOperators
open Polynomial

namespace Work.Peluse.UControl

noncomputable section

open Work.Peluse


/-! ## A product of the coherence analysis: the gauge-period identity

The exact-coherence relation `g₀(x)·g₁(x+y)·g₂(x+P(y)) = λ` (the output of the alignment lemma
`Work.Peluse.exists_alignment_of_correlation`, in its exact form) is unchanged when `(x,y)` is
replaced by `(x+k, y-k)` in the `g₁`-argument.  Comparing the two instances gives the
*gauge-period* identity below: `g₂` is invariant under the shift `Δ = P(y) - P(y-k) - k` along the
curve, up to the `g₀`-gauge.  Iterating it (and using that the periods `Δ` generate
`(dirCoeff P)ℤ`, which follows from
`gcd_y (P(y)-P(y-1)-1) ∣ (P.natDegree)! · P.leadingCoeff` by finite differences) is the first half
of the rigidity/concatenation step of the coarse-scale inverse theorem. -/

/-- **The gauge-period identity from exact coherence.**  If the coherence relation
`g₀(x)·g₁(x+y)·g₂(x+P(y)) = λ` holds exactly for all `x y : ℤ` and `λ ≠ 0`, then the `g₂`-values at
`x + P(y)` and at `x + k + P(y-k)` differ by the `g₀`-gauge `g₀(x+k)/g₀(x)`. -/
theorem coherence_gauge_period (P : Polynomial ℤ) {g₀ g₁ g₂ : ℤ → ℂ} {lam : ℂ} (hlam : lam ≠ 0)
    (hcoh : ∀ x y : ℤ, g₀ x * g₁ (x + y) * g₂ (x + P.eval y) = lam) (x y k : ℤ) :
    g₀ (x + k) * g₂ (x + k + P.eval (y - k)) = g₀ x * g₂ (x + P.eval y) := by
  set gm : ℂ := g₁ (x + y) with hgm
  have h1 : g₀ x * gm * g₂ (x + P.eval y) = lam := by
    have h := hcoh x y
    rw [← hgm] at h
    exact h
  have h2 : g₀ (x + k) * gm * g₂ (x + k + P.eval (y - k)) = lam := by
    have h := hcoh (x + k) (y - k)
    have harg : (x + k) + (y - k) = x + y := by ring
    rw [harg] at h
    rw [← hgm] at h
    exact h
  have hgm0 : gm ≠ 0 := by
    intro h0
    rw [h0] at h1
    exact hlam (by simpa using h1.symm)
  have hkey : g₀ x * g₂ (x + P.eval y) = g₀ (x + k) * g₂ (x + k + P.eval (y - k)) := by
    apply mul_left_cancel₀ hgm0
    calc gm * (g₀ x * g₂ (x + P.eval y))
        = g₀ x * gm * g₂ (x + P.eval y) := by ring
      _ = lam := h1
      _ = g₀ (x + k) * gm * g₂ (x + k + P.eval (y - k)) := h2.symm
      _ = gm * (g₀ (x + k) * g₂ (x + k + P.eval (y - k))) := by ring
  exact hkey.symm

/-- **The open input: the complementary (`L` large) regime.**

This is the target's conclusion in the regime where the elementary peel bound
(`peel_bound`) is insufficient, i.e. where the direction length `L = dirLen P δ' N` exceeds
`(c₁/c)^{1/s} γ^{(2^s-K₀)/s}`.  It is the coarse-scale inverse-theorem content of the statement:
the correlation `γ ≤ ‖Λ(g₀,g₁,g₂)‖` for `1`-bounded functions must force the box norm of `g₂` at a
*long* direction set to be at least a fixed power of `γ`, uniformly in the scale imbalance `A'`
and in `C`. 
### The shape of the remaining content (analysis, session 3)

`peel_bound` supplies `c₁ γ^{2^s} / L^s ≤ uNormPow s ... g₂`; the *only* content of `BandHard` is
therefore the regime in which that bound is insufficient, i.e. `L^s > γ^{2^s - K₀}`.  Because `Hyp`
also gives `L ≤ γ^K N₁ ≤ γ^{K₀} N₁` (as `γ ≤ 1 ≤ K/K₀`), the two constraints squeeze the datum:

* `L ≥ N^{d-1}` (the window hypothesis `1 ≤ ⌊δ'N⌋` and `L = ⌊δ'N^d⌋`), hence
  `γ^{K₀} ≥ L/N₁ ≥ N^{d-1}/N₁` — so `γ` is *bounded below* in terms of the scale;
* consequently sparse data are excluded: for `g₂ = 1_A` one has `‖Λ‖ ≤ |A|/N₁` and
  `uNormPow s ≈ |A|/(2N₁)`, and the two constraints force `|A| ≳ N^{d-1/K₀}` — i.e. `g₂` must have
  `ℓ¹`-mass of the order of the window `N^d`, not less;
* **the sharp exponent is `2^s`**: for the "density" family `g₀ = g₁ = 1_{symIcc N₁}`,
  `g₂ = 1_A` with `A ⊆ symIcc N₁` of density `ρ`, one has `‖Λ‖ ≈ 2ρ` and
  `uNormPow s ≈ ρ^{2^s}` (numerically `uNormPow 2 / ρ^4 ∈ [0.5, 1.3]` over random `A`), so
  `uNormPow s / γ^{K₀} ≈ ρ^{2^s-K₀}/2^{K₀} → 0` as `ρ → 0` whenever `K₀ < 2^s`: the target's
  conclusion is unreachable for `K₀ < 2^s`.  Hence it suffices to prove the *sharp form*
  `uNormPow s ((dirCoeff P)[L]) (symIcc N₁) g₂ ≥ c · γ^{2^s}` (the case `K₀ = 2^s`) for all
  admissible data; conversely the target applied to data with `γ = 1` gives `uNormPow s ≥ c`.

With `γ ≈ 1` (the hardest case, since `γ^{K₀}` is then `≈ 1`) the hypothesis reads
`‖Λ(g₀,g₁,g₂)‖ ≥ 1` with `L ≤ N₁`, and the conclusion reduces to the *scale-free* lower bound
`uNormPow s ((dirCoeff P)[L]) (symIcc N₁) g₂ ≥ c` — the box-norm power at the long direction set is
bounded below by a constant.  Two-sided evidence for this: the `4`-periodic character
`g₂ x = i^x` (with `g₀ x = i^{-x}`, `g₁ = 1`) has `‖Λ‖ ≈ 1.2718` and
`uNormPow 2 (arithIcc 2 16) (symIcc 32) g₂ ≈ 0.673`; the indicator of `symIcc N₁` has limit
`E[(1 - (|κ|/2) Σ_{i≤s}|X_i - X'_i|)^+] > 0` for `A' = 1` (numerically `0.383` at `N = 4`); and the
"missing point" family `1_{symIcc N₁ \ {0}}` gives `0.2847` at `s = 2, N = 2`.  What is *not*
available is the inverse direction: a Gowers-uniform `g₂` (e.g. random signs) has
`uNormPow s ≈ c/L`, but its correlation `‖Λ‖` is only `≈ (N₁N)^{-1/2}` — the density-increment
step of the source's §§4–5 that upgrades coherence on a `γ`-density set of pairs to the structure
that forces a large box norm is the genuine missing chapter.

-/
def BandHard (s : ℕ) (P : Polynomial ℤ) : Prop :=
  ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∃ c : ℝ, 0 < c ∧
    ∀ A' : ℝ, 1 ≤ A' → ∀ C : ℝ, 1 ≤ C → ∀ K : ℕ, K₀ ≤ K →
    ∀ (N N₁ : ℕ) (g₀ g₁ g₂ : ℤ → ℂ) (γ δ' : ℝ),
      Hyp P A' C K N N₁ g₀ g₁ g₂ γ δ' →
      (c * γ ^ (2 ^ s) / ((dirLen P δ' N : ℝ) ^ s) < c * γ ^ K₀) →
      c * γ ^ K₀ ≤ uNormPow s (arithIcc (dirCoeff P) (dirLen P δ' N)) (symIcc N₁) g₂

/-! ## Helper arithmetic: the direction length against the data

The two elementary facts about the direction length `L = dirLen P δ' N` that the assembly below
needs (both extracted from the argument of `peel_bound` above). -/

/-- The direction length never exceeds the support radius `N₁`: `Hyp`'s smallness
`C · dirLen ≤ γ^K N₁` together with `C ≥ 1` and `γ ≤ 1` gives `dirLen ≤ N₁`. -/
theorem dirLen_le_of_hyp {P : Polynomial ℤ} {A' C : ℝ} {K : ℕ} {N N₁ : ℕ} {g₀ g₁ g₂ : ℤ → ℂ}
    {γ δ' : ℝ} (h : Hyp P A' C K N N₁ g₀ g₁ g₂ γ δ') : dirLen P δ' N ≤ N₁ := by
  obtain ⟨hd, hN, hN₁, hγ0, hγ1, hδ'0, hδ'1, hwin, hsc1, hsc2, hC1, hK1, hsmall, hnd,
    hs0, hs1, hs2, hb0, hb1, hb2, hΛ⟩ := h
  have hγK1 : γ ^ K ≤ 1 := pow_le_one₀ hγ0.le hγ1
  have h1 : (dirLen P δ' N : ℝ) ≤ (C : ℝ) * (dirLen P δ' N : ℝ) := by
    nlinarith [hC1, Nat.cast_nonneg (α := ℝ) (dirLen P δ' N)]
  have hLle : (dirLen P δ' N : ℝ) ≤ (N₁ : ℝ) := by
    calc (dirLen P δ' N : ℝ) ≤ (C : ℝ) * (dirLen P δ' N : ℝ) := h1
      _ ≤ γ ^ K * (N₁ : ℝ) := hsmall
      _ ≤ 1 * (N₁ : ℝ) := mul_le_mul_of_nonneg_right hγK1 (by positivity)
      _ = (N₁ : ℝ) := one_mul _
  exact_mod_cast hLle

/-- The direction coefficient `(deg P)! · lc P` is non-zero as soon as `2 ≤ P.natDegree`
(needed to apply the diagonal bound `Work.Peluse.UControl.diagMassGen`, whose statement
normalises by `|arithIcc κ L| = L`). -/
theorem dirCoeff_ne_zero {P : Polynomial ℤ} (hd : 2 ≤ P.natDegree) : dirCoeff P ≠ 0 := by
  rw [dirCoeff]
  refine mul_ne_zero ?_ ?_
  · exact_mod_cast (Nat.factorial_ne_zero P.natDegree)
  · refine Polynomial.leadingCoeff_ne_zero.mpr ?_
    intro h0
    rw [h0] at hd
    simp at hd

/-- The fit constant of the direction set: `C = max 1 |κ|`, the constant needed by the
"dense phase structure ⟹ box norm" step (`Work.Peluse.UControl.phaseToBox`), since the direction
set `κ[L]` fits in the support `symIcc N₁` up to the factor `C`: `|κ| L ≤ C N₁` (as `L ≤ N₁`). -/
def fitC (P : Polynomial ℤ) : ℕ := max 1 (dirCoeff P).natAbs

/-- The exceptional-set/error constant `D` of the dense phase structure, in the explicit form in
which `Work.Peluse.UControl.phaseToBox` consumes it. -/
def structDC (s C : ℕ) : ℝ :=
  8 * (2 : ℝ) ^ (2 * s) * (2 * ((C : ℝ) + 1)) ^ (2 ^ s - 1) * (6 : ℝ) ^ (2 ^ s)

/-! ## The dense phase structure — **REFUTED** (do not attempt to prove it)

*Historical note (session 3 of this node).*  The previous session reduced the target to the
following "dense phase structure": the correlation `γ ≤ ‖Λ(g₀,g₁,g₂)‖` should force `g₂` to be, up
to a small error and off a small exceptional set, a `κ`-periodic unimodular phase (`κ = dirCoeff P`)
times a real non-negative function, with errors of the *sharp* size `γ^{2^s}` — and
`bandHard_of_denseStructure` below converts that structure into `BandHard` with the proved flat arm
`Work.Peluse.UControl.phaseToBox` and the proved mass bound `Work.Peluse.UControl.massOfHyp`.

**That statement is FALSE**, already at `s = 2`, `P = X²`.  The counterexample is the
`4`-periodic character `g₂ (x) = i ^ x`, which is *not* the product of a `2`-periodic phase with a
non-negative function, while its correlation with `Λ` is `> 1`:

```
P = X²,  N = 4,  N₁ = 32,  δ' = 1,  L = ⌊δ' N²⌋ = 16  ( = dirLen X² 1 4 ),
A' = 2,  C = 1,  K = 2,  γ = 1,
g₀ x = i ^ (-x) · 1_{symIcc 32},   g₁ x = 1_{symIcc 32},   g₂ x = i ^ x · 1_{symIcc 32}.
```

Every conjunct of `Hyp X² 2 1 2 4 32 g₀ g₁ g₂ 1 1` holds:

* `N₁ = 32 ≤ A' N^d = 2·16` and `N^d = 16 ≤ A' γ⁻¹ N₁ = 64`;
* `C · dirLen = 16 ≤ γ^K N₁ = 32`  and  `C = 1 ≤ (γ δ')^K (δ' N)² = 16`;
* the three functions are `1`-bounded with support in `symIcc 32`;
* `γ = 1 ≤ ‖Λ‖`:  since `g₀ x · g₁ (x+y) · g₂ (x+y²) = i ^ (y²)` on the support, and for `y = 1,2,3,4`
  the number of `x` with `|x| ≤ 32`, `|x+y| ≤ 32`, `|x+y²| ≤ 32` is `64, 61, 56, 49`,

  `Λ = (1/128) (110 + 120 i)`,  so `‖Λ‖ = √26500 / 128 ≈ 1.2718 > 1`.

The conclusion of `BandDenseStructure 2 X²` is impossible for this datum: `fitC X² = 2`, hence
`structDC 2 2 = 35 831 808`, so `ε ≤ γ^{2^s}/structDC ≈ 2.79·10⁻⁸` and
`T.card ≤ γ^{2^s}·65/structDC ≈ 1.81·10⁻⁶`, i.e. `T = ∅`.  Writing `ω (0) = ω (2)` (the periodicity
`κ = 2`) and using `g₂ 0 = 1`, `g₂ 2 = -1`, the pointwise bound at `x = 0` and `x = 2` gives
`h 0 + h 2 ≤ 2 ε`, whence `‖1 - ω 0 · h 0‖ ≥ 1 - h 0 ≥ 1 - 2 ε > ε` — a contradiction.

The formal refutation is `Work.Peluse.UControl.bandDenseStructureFalse`
(`import Submission.Work.Peluse.UControl.bandDenseStructureFalse`).

Consequently `bandHard_of_denseStructure` below is *vacuously* true and the reduction recorded in
`bandCoreUnified.lean` does **not** reduce the target: the honest single input is `BandHard s P`
itself (`bandCore_of_hard` below).  The correct structural statement that the source's §4 actually
produces is a *twist* — `g (x + t) = g (x) · χ t` for a multiplicative character `χ` — which is
weaker than the phase form above and is consumed by the proved
`Work.Peluse.UControl.uNormPow_ge_of_denseApprox`/`bandShiftTwistAssembly`; but the twist is also
*not* implied by `Hyp` (it fails for the `5`-periodic chirp `g₂ x = e^{2πi x³/5}`, for which
`Hyp` is satisfiable with `P = X²`, `N = 3`, `A' = 2`, `K = 2`, `γ = 1/2` and `‖Λ‖ ≈ 0.89 > 1/2`).

The *entry point* of the inverse-theorem chapter that is genuinely available remains
`Work.Peluse.UControl.coherenceDensity` (a global phase `μ`, `‖μ‖ = 1`, and a set `Ω` of pairs with
`|Ω| ≥ γN₁N/4` on which `Re(μ · g₀(x)g₁(x+y)g₂(x+P(y))) ≥ γ/4`).

**Caution for the chaining route**: the coherence of the *base* pairs does **not** by itself produce
"chained" pairs — the naive Cauchy–Schwarz/energy step is *false* (a reviewer's counterexample: the
`{0,±1}`-valued stripe functions `g₀ = 1_{3ℤ}`, `g₁ = 1_{3ℤ ∪ (3ℤ+1)}`, `g₂ = 1_{(3ℤ+1) ∪ (3ℤ+2)}`
truncated at `|x| ≤ N₁`, with `P = X²`, `N = 2`, `N₁ = 24`, `γ = 1/4`, `A' = 24`, `δ' = K = C = 1`,
satisfy `Hyp` with `‖Λ‖ = 1/3`, yet *no* pair `(x,y),(x+y',y−y')` is coherent twice).  A
**localisation** step (restrict `x` to a block on which the coherence is uniform), as in the area's
`Ulower/gap_local_block`, is needed before the chaining can start.  The remaining gap is the
*density increment* — upgrading coherence on a `γ`-density set to structure on a `1 - δ`-density set
(the source's §§4–5, not available in the no-gauge regime). -/
def BandDenseStructure (s : ℕ) (P : Polynomial ℤ) : Prop :=
  ∃ K₀ : ℕ, 1 ≤ K₀ ∧
    ∀ A' : ℝ, 1 ≤ A' → ∀ C : ℝ, 1 ≤ C → ∀ K : ℕ, K₀ ≤ K →
    ∀ (N N₁ : ℕ) (g₀ g₁ g₂ : ℤ → ℂ) (γ δ' : ℝ),
      Hyp P A' C K N N₁ g₀ g₁ g₂ γ δ' →
      ∃ (ω h : ℤ → ℂ) (T : Finset ℤ) (ε : ℝ),
        (∀ x : ℤ, ‖ω x‖ = 1) ∧
        (∀ x m : ℤ, ω (x + dirCoeff P * m) = ω x) ∧
        SupportIn h N₁ ∧ (∀ x : ℤ, ‖h x‖ ≤ 1) ∧
        (∀ x : ℤ, h x = ((‖h x‖ : ℝ) : ℂ)) ∧
        0 ≤ ε ∧
        (∀ x : ℤ, x ∉ T → ‖g₂ x - ω x * h x‖ ≤ ε) ∧
        ε ≤ γ ^ (2 ^ s) / structDC s (fitC P) ∧
        (T.card : ℝ) ≤ γ ^ (2 ^ s) * ((symIcc N₁).card : ℝ) / structDC s (fitC P)

/-! ## The counterexample data that refutes `BandDenseStructure`

The explicit datum of the refutation described in the docstring of `BandDenseStructure`: the
`4`-periodic character `x ↦ i^x` (and its conjugate) truncated to `symIcc N₁`.  It satisfies
`Hyp (X^2) 2 1 2 4 32 · · · 1 1` with `‖Λ‖ ≈ 1.2718 ≥ 1`, but it cannot be `ω·h` with `ω`
`dirCoeff X² = 2`-periodic and `h ≥ 0` real. -/

/-- The conjugate character `x ↦ i^{-x}`, truncated to `symIcc N₁` (the first function). -/
def ce4g0 (N₁ : ℕ) : ℤ → ℂ := fun x => if x.natAbs ≤ N₁ then (Complex.I : ℂ) ^ (-x) else 0

/-- The indicator `1_{symIcc N₁}` (the second function). -/
def ce4g1 (N₁ : ℕ) : ℤ → ℂ := fun x => if x.natAbs ≤ N₁ then 1 else 0

/-- The `4`-periodic character `x ↦ i^x`, truncated to `symIcc N₁` (the third function). -/
def ce4g2 (N₁ : ℕ) : ℤ → ℂ := fun x => if x.natAbs ≤ N₁ then (Complex.I : ℂ) ^ x else 0


 /-! ## The sharpened dichotomy

`Work.Peluse.UControl.diagMassGen` (proved) gives a level-`s` lower bound for the box-norm power of
`g₂` with the loss `L^{s-1}` — one power of `L` better than the peel bound `elementary_bound_v2`
(which loses `L^s`), and with no fit hypothesis.  Feeding it with the `ℓ¹`-mass bound
`Work.Peluse.UControl.massOfHyp` produces a *stronger* elementary bound than `peel_bound`, and the
dichotomy below can therefore invoke the named input on strictly fewer data than `BandHard` did. -/

/-- **The band's hard input, in the sharpened (dichotomy-complement) form.**

This is `BandHard` with the peel-complement hypothesis replaced by the **conjunction** of the peel
complement and the complement of the sharper diagonal bound (with constant `cdiag`):

* `cdiag · γ^{2^s} / L^{s-1} < c γ^{K₀}`  (the diagonal bound of `diagMassGen` does not suffice),
* `cpeel · γ^{2^s} / L^s < c γ^{K₀}`      (the peel bound does not suffice).

Since the diagonal bound dominates the peel bound as soon as `cpeel ≤ cdiag` (both are stated for
the same data, and `L ≥ 1`), a datum admitted by the hypothesis above is admitted by `BandHard`'s
hypothesis; the input is therefore *strictly weaker* than `BandHard`, and `bandCore_of_sharp`
discharges the conclusion on it using the two elementary bounds. -/
def BandHardSharpAt (s : ℕ) (P : Polynomial ℤ) (cdiag cpeel : ℝ) : Prop :=
  ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∃ c : ℝ, 0 < c ∧
    ∀ A' : ℝ, 1 ≤ A' → ∀ C : ℝ, 1 ≤ C → ∀ K : ℕ, K₀ ≤ K →
    ∀ (N N₁ : ℕ) (g₀ g₁ g₂ : ℤ → ℂ) (γ δ' : ℝ),
      Hyp P A' C K N N₁ g₀ g₁ g₂ γ δ' →
      (cdiag * γ ^ (2 ^ s) / ((dirLen P δ' N : ℝ) ^ (s - 1)) < c * γ ^ K₀) →
      (cpeel * γ ^ (2 ^ s) / ((dirLen P δ' N : ℝ) ^ s) < c * γ ^ K₀) →
      c * γ ^ K₀ ≤ uNormPow s (arithIcc (dirCoeff P) (dirLen P δ' N)) (symIcc N₁) g₂

/-- **The dichotomy with the sharpened elementary bound.**

From the two elementary bounds — the diagonal bound (constant `cdiag`, loss `L^{s-1}`, fit-free)
and the peel bound (constant `cpeel`, loss `L^s`) — plus the sharpened input
`BandHardSharpAt s P cdiag cpeel`, one gets the target's conclusion for `P`. -/
theorem bandCore_of_sharp (s : ℕ) (hs : 2 ≤ s) (P : Polynomial ℤ) (hP : 2 ≤ P.natDegree)
    {cdiag cpeel : ℝ} (hcdiag : 0 < cdiag) (hcpeel : 0 < cpeel)
    (hdiag : ∀ A' C K N N₁ g₀ g₁ g₂ γ δ',
      Hyp P A' C K N N₁ g₀ g₁ g₂ γ δ' →
      cdiag * γ ^ (2 ^ s) / ((dirLen P δ' N : ℝ) ^ (s - 1)) ≤
        uNormPow s (arithIcc (dirCoeff P) (dirLen P δ' N)) (symIcc N₁) g₂)
    (hpeel : ∀ A' C K N N₁ g₀ g₁ g₂ γ δ',
      Hyp P A' C K N N₁ g₀ g₁ g₂ γ δ' →
      cpeel * γ ^ (2 ^ s) / ((dirLen P δ' N : ℝ) ^ s) ≤
        uNormPow s (arithIcc (dirCoeff P) (dirLen P δ' N)) (symIcc N₁) g₂)
    (hhard : BandHardSharpAt s P cdiag cpeel) :
    ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∃ c : ℝ, 0 < c ∧
      ∀ A' : ℝ, 1 ≤ A' → ∀ C : ℝ, 1 ≤ C → ∀ K : ℕ, K₀ ≤ K →
      ∀ (N N₁ : ℕ) (g₀ g₁ g₂ : ℤ → ℂ) (γ δ' : ℝ),
        Hyp P A' C K N N₁ g₀ g₁ g₂ γ δ' →
        c * γ ^ K₀ ≤ uNormPow s
          (arithIcc (dirCoeff P) (dirLen P δ' N)) (symIcc N₁) g₂ := by
  obtain ⟨K₀, hK₀, c, hc, hcase⟩ := hhard
  refine ⟨K₀, hK₀, c, hc, ?_⟩
  intro A' hA' C hC K hK N N₁ g₀ g₁ g₂ γ δ' hHyp
  by_cases h1 : cdiag * γ ^ (2 ^ s) / ((dirLen P δ' N : ℝ) ^ (s - 1)) < c * γ ^ K₀
  · by_cases h2 : cpeel * γ ^ (2 ^ s) / ((dirLen P δ' N : ℝ) ^ s) < c * γ ^ K₀
    · exact hcase A' hA' C hC K hK N N₁ g₀ g₁ g₂ γ δ' hHyp h1 h2
    · exact le_trans (not_lt.mp h2) (hpeel A' C K N N₁ g₀ g₁ g₂ γ δ' hHyp)
  · exact le_trans (not_lt.mp h1) (hdiag A' C K N N₁ g₀ g₁ g₂ γ δ' hHyp)


/-! ## The window of the box-norm power, and level raising with window slack

The Gowers–Cauchy–Schwarz level raising `Work.Peluse.UControl.uNormPow_level_raise` is only stated
for a direction set `Q` that *fits* in the window (`∀ a ∈ Q, |a| ≤ N`, the window being
`symIcc N`).  In the band the fit `|dirCoeff P| · dirLen ≤ N₁` may fail, and the previous sessions
recorded this as an obstruction to using the level raising there.  It is not one: the window of the
box-norm power enters *only* through the normalisation `|S|⁻¹` (`uNormPow_window_ratio` below), so
the level raising may be applied at the larger window `symIcc M`, `M := max N₁ (L |κ|)`, where the
fit holds, and transported back at the cost of the *constant* `(2 max 1 |κ| + 1)^{2^{s-s₀}-1}`
(valid because `Hyp` gives `L ≤ N₁`, so `M ≤ |κ| N₁`).

Consequently the whole target at level `s` follows from its level-`2` instance
(`bandCore_of_levelTwo`), with `K₀ := K₂ · 2^{s-2}`.  This is the reason why the single remaining
input of this file is stated at level `2` only. -/

/-- The cardinality of the symmetric interval `symIcc N` is `2N+1`. -/
lemma card_symIcc (N : ℕ) : (symIcc N).card = 2 * N + 1 := by
  rw [symIcc, Int.card_Icc]
  have h2 : (((N : ℤ)) + 1 - (-(N : ℤ)) : ℤ) = ((2 * N + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h2, Int.toNat_natCast]

lemma symIcc_nonempty (N : ℕ) : (symIcc N).Nonempty :=
  ⟨0, by rw [symIcc, Finset.mem_Icc]; omega⟩

/-- The cube sum depends on the window `S` only through the factor `|S|⁻¹`. -/
lemma prodCubeSum_window (t : ℕ) (Q : Fin t → Finset ℤ) (S S' : Finset ℤ)
    (f : (Fin t → Bool) → ℤ → ℂ) (hS' : S'.Nonempty) :
    prodCubeSum t Q S f = ((S.card : ℂ))⁻¹ * ((S'.card : ℂ)) * prodCubeSum t Q S' f := by
  have hc : ((S'.card : ℂ)) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hS'
  rw [prodCubeSum, prodCubeSum]
  field_simp

/-- The window of the box-norm power is only a normalisation factor. -/
theorem boxNormPow_window_ratio (t : ℕ) (Q : Fin t → Finset ℤ) (S S' : Finset ℤ) (f : ℤ → ℂ)
    (hS' : S'.Nonempty) :
    boxNormPow t Q S f = ((S'.card : ℝ) / (S.card : ℝ)) * boxNormPow t Q S' f := by
  simp only [boxNormPow, boxSumPow]
  rw [prodCubeSum_window t Q S S' (fun _ => f) hS']
  rw [norm_mul, norm_mul, norm_inv]
  simp only [Complex.norm_natCast]
  ring

/-- The same statement for the uniformity norm `uNormPow`. -/
theorem uNormPow_window_ratio (t : ℕ) (Q : Finset ℤ) (S S' : Finset ℤ) (f : ℤ → ℂ)
    (hS' : S'.Nonempty) :
    uNormPow t Q S f = ((S'.card : ℝ) / (S.card : ℝ)) * uNormPow t Q S' f :=
  boxNormPow_window_ratio t (fun _ : Fin t => Q) S S' f hS'

/-- **Level raising with window slack.**  The fit is needed only at the *larger* window
`symIcc (max N (L |κ|))`, where it holds automatically for the directions `κ[L]` with `L ≤ N`.
Hence, up to a constant depending only on `s`, `s₀` and `κ`, the level raising is available for the
direction set `κ[L]` in the window `symIcc N` *without* the fit `|κ| L ≤ N`. -/
theorem uNormPow_level_raise_win (s₀ s : ℕ) (hs : 1 ≤ s₀) (hss : s₀ ≤ s) {κ : ℤ}
    (hκ : κ ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ (L N : ℕ) (f : ℤ → ℂ),
      L ≤ N → 1 ≤ L → SupportIn f N → (∀ x : ℤ, ‖f x‖ ≤ 1) →
      c * (uNormPow s₀ (arithIcc κ L) (symIcc N) f) ^ (2 ^ (s - s₀))
        ≤ uNormPow s (arithIcc κ L) (symIcc N) f := by
  obtain ⟨c₀, hc₀, hlev⟩ := uNormPow_level_raise s₀ s hs hss
  set k : ℕ := 2 ^ (s - s₀) with hk
  have hk1 : 1 ≤ k := by rw [hk]; exact Nat.one_le_two_pow
  set A : ℝ := 2 * (max 1 κ.natAbs : ℝ) + 1 with hA
  refine ⟨c₀ / A ^ (k - 1), by positivity, ?_⟩
  intro L N f hLN hL1 hsupp hbdd
  set M : ℕ := max N (L * κ.natAbs) with hM
  set a : ℝ := ((symIcc M).card : ℝ) with ha
  set b : ℝ := ((symIcc N).card : ℝ) with hb
  have hMN : N ≤ M := le_max_left _ _
  have hcardM : a = (2 * M + 1 : ℕ) := by rw [ha, card_symIcc]
  have hcardN : b = (2 * N + 1 : ℕ) := by rw [hb, card_symIcc]
  have ha0 : 0 < a := by rw [hcardM]; positivity
  have hb0 : 0 < b := by rw [hcardN]; positivity
  -- the fit at the larger window
  have hMk : M ≤ N * max 1 κ.natAbs := by
    rw [hM]
    refine max_le ?_ ?_
    · calc N = N * 1 := (Nat.mul_one N).symm
        _ ≤ N * max 1 κ.natAbs := Nat.mul_le_mul_left _ (le_max_left _ _)
    · calc L * κ.natAbs ≤ N * κ.natAbs := Nat.mul_le_mul_right _ hLN
        _ ≤ N * max 1 κ.natAbs := Nat.mul_le_mul_left _ (le_max_right _ _)
  have hMb : 2 * M + 1 ≤ (2 * max 1 κ.natAbs + 1) * (2 * N + 1) := by
    have h1 : 2 * M ≤ 2 * (N * max 1 κ.natAbs) := by omega
    have hk1' : 1 ≤ max 1 κ.natAbs := le_max_left _ _
    nlinarith [Nat.zero_le M, Nat.zero_le N, hk1']
  have hQne : (arithIcc κ L).Nonempty := arithIcc_nonempty hκ hL1
  have hbnd : ∀ x ∈ arithIcc κ L, |x| ≤ (M : ℤ) := by
    intro x hx
    rw [arithIcc] at hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
    have hnL : n ≤ L := (Finset.mem_Icc.mp hn).2
    have h1 : |κ * (n : ℤ)| ≤ ((L * κ.natAbs : ℕ) : ℤ) := by
      rw [abs_mul, ← Int.natCast_natAbs κ]
      have hn0 : (0 : ℤ) ≤ (n : ℤ) := by positivity
      rw [abs_of_nonneg hn0]
      push_cast
      nlinarith [Nat.zero_le (κ.natAbs), hnL]
    have h2 : ((L * κ.natAbs : ℕ) : ℤ) ≤ (M : ℤ) := by
      have : L * κ.natAbs ≤ M := by rw [hM]; exact le_max_right _ _
      exact_mod_cast this
    exact le_trans h1 h2
  have hlevM := hlev (arithIcc κ L) M f hQne (by omega) hbnd (hsupp.mono hMN) hbdd
  have hw1 := uNormPow_window_ratio s (arithIcc κ L) (symIcc N) (symIcc M) f (symIcc_nonempty M)
  have hw2 := uNormPow_window_ratio s₀ (arithIcc κ L) (symIcc M) (symIcc N) f (symIcc_nonempty N)
  have hαle : a / b ≤ A := by
    rw [div_le_iff₀ hb0]
    calc (a : ℝ) = ((2 * M + 1 : ℕ) : ℝ) := hcardM
      _ ≤ (((2 * max 1 κ.natAbs + 1) * (2 * N + 1) : ℕ) : ℝ) := by exact_mod_cast hMb
      _ = (2 * (max 1 κ.natAbs : ℝ) + 1) * b := by rw [hcardN]; push_cast; ring
      _ = A * b := by rw [hA]
  have hα0 : 0 < a / b := div_pos ha0 hb0
  have hkey : a / b * (b / a) ^ k = 1 / (a / b) ^ (k - 1) := by
    have hmain : (a / b) ^ (k - 1) * (a / b * (b / a) ^ k) = 1 := by
      have hsucc : (k - 1) + 1 = k := by omega
      have hba : b / a = (a / b)⁻¹ := by rw [inv_div]
      calc (a / b) ^ (k - 1) * (a / b * (b / a) ^ k)
          = ((a / b) ^ (k - 1) * (a / b)) * (b / a) ^ k := by ring
        _ = (a / b) ^ ((k - 1) + 1) * (b / a) ^ k := by rw [pow_succ]
        _ = (a / b) ^ k * ((a / b)⁻¹) ^ k := by rw [hsucc, hba]
        _ = ((a / b) * (a / b)⁻¹) ^ k := by rw [← mul_pow]
        _ = 1 := by rw [mul_inv_cancel₀ (ne_of_gt hα0), one_pow]
    have hne : (a / b) ^ (k - 1) ≠ 0 := pow_ne_zero _ (ne_of_gt hα0)
    rw [eq_div_iff hne, mul_comm]
    exact hmain
  have hpow : (a / b) ^ (k - 1) ≤ A ^ (k - 1) := pow_le_pow_left₀ hα0.le hαle _
  have hU0 : (0 : ℝ) ≤ (uNormPow s₀ (arithIcc κ L) (symIcc N) f) ^ k :=
    pow_nonneg (by rw [uNormPow, boxNormPow]; exact norm_nonneg _) _
  calc uNormPow s (arithIcc κ L) (symIcc N) f
      = a / b * uNormPow s (arithIcc κ L) (symIcc M) f := by rw [hw1]
    _ ≥ a / b * (c₀ * (uNormPow s₀ (arithIcc κ L) (symIcc M) f) ^ k) :=
        mul_le_mul_of_nonneg_left hlevM hα0.le
    _ = a / b * (c₀ * ((b / a) * uNormPow s₀ (arithIcc κ L) (symIcc N) f) ^ k) := by rw [hw2]
    _ = a / b * (c₀ * ((b / a) ^ k * (uNormPow s₀ (arithIcc κ L) (symIcc N) f) ^ k)) := by
        rw [mul_pow]
    _ = (a / b * (b / a) ^ k) * c₀ * (uNormPow s₀ (arithIcc κ L) (symIcc N) f) ^ k := by ring
    _ = (1 / (a / b) ^ (k - 1)) * c₀ * (uNormPow s₀ (arithIcc κ L) (symIcc N) f) ^ k := by
        rw [hkey]
    _ ≥ (1 / A ^ (k - 1)) * c₀ * (uNormPow s₀ (arithIcc κ L) (symIcc N) f) ^ k := by
        have hpos : (0 : ℝ) < (a / b) ^ (k - 1) := by positivity
        have hone : 1 / A ^ (k - 1) ≤ 1 / (a / b) ^ (k - 1) := by
          rw [one_div, one_div, inv_le_inv₀ (by positivity) hpos]
          exact hpow
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hone hc₀.le) hU0
    _ = c₀ / A ^ (k - 1) * (uNormPow s₀ (arithIcc κ L) (symIcc N) f) ^ k := by ring
    _ = c₀ / A ^ (k - 1) * (uNormPow s₀ (arithIcc κ L) (symIcc N) f) ^ (2 ^ (s - s₀)) := by
        rw [hk]

/-- **The level-`2` form of the target's conclusion.** -/
def LevelTwoConcl (P : Polynomial ℤ) : Prop :=
  ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∃ c : ℝ, 0 < c ∧
    ∀ A' : ℝ, 1 ≤ A' → ∀ C : ℝ, 1 ≤ C → ∀ K : ℕ, K₀ ≤ K →
    ∀ (N N₁ : ℕ) (g₀ g₁ g₂ : ℤ → ℂ) (γ δ' : ℝ),
      Hyp P A' C K N N₁ g₀ g₁ g₂ γ δ' →
      c * γ ^ K₀ ≤ uNormPow 2
        (arithIcc (dirCoeff P) (dirLen P δ' N)) (symIcc N₁) g₂

/-! ## The level-`2` bound from the flatness of the autocorrelation, **without** the fit

`Work.Peluse.Concat.uNormPow_two_ge_autocorr_l2` requires the *fit* `c₀·D ≤ N` between the direction
length and the window.  In the band that fit can fail (`|dirCoeff P|·dirLen` may exceed `N₁`), and
the previous sessions recorded this as an obstruction.  It is not one: the window of the box norm
enters the definition only through the normalisation `|S|⁻¹` (`uNormPow_window_ratio`), so the
existing lemma may be applied in the *larger* window `symIcc (max N (|κ|L))` — where the fit holds
automatically — and the result transported back, paying the window ratio `|symIcc N|/|symIcc M|`
*once* (the two `autocorr`s contribute its square, the `uNormPow` its inverse, so the net factor is
`|S_N|/|S_M|`).  This is the fit-free form of the flatness bound needed in the non-fit regime. -/

/-! ## The flatness input at the diagonal lag

The remaining input of the target (see `NOTES_bandCore_SESSION7.md` §7, §11, §12) is the pointwise
flatness of the autocorrelation of `g₂` on the multiples of `κ`.  Its `m = 0` case is elementary:
`‖autocorr N₁ g₂ 0‖ = |symIcc N₁|⁻¹ ∑_{symIcc N₁} ‖g₂‖²`, and `massOfHyp` plus Cauchy–Schwarz give
`∑ ‖g₂‖² ≥ γ²N₁²/(2N₁+1)`, hence `≥ γ²/9` (the constant `17` below is deliberate slack). -/

/-- In the non-fit regime `N < |κ| L` the window ratio `(2N+1)/(2·max N (|κ|L) + 1)` is at least
`(2N/|κ|)/(4L)`: the factor lost in the fit-free flatness bound. -/
theorem window_ratio_ge {κ : ℤ} (hκ : κ ≠ 0) {L N : ℕ} (hL : 1 ≤ L) (hN : 1 ≤ N)
    (hfit : (N : ℝ) < (κ.natAbs : ℝ) * (L : ℝ)) :
    (2 * (N : ℝ) + 1) / (2 * (max N (κ.natAbs * L) : ℝ) + 1)
      ≥ (2 * (N : ℝ) / (κ.natAbs : ℝ)) / (4 * (L : ℝ)) := by
  have hκpos : (0 : ℝ) < (κ.natAbs : ℝ) := by
    have h : κ.natAbs ≠ 0 := fun h0 => hκ (Int.natAbs_eq_zero.mp h0)
    exact_mod_cast Nat.pos_of_ne_zero h
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hden : (0 : ℝ) < 2 * ((κ.natAbs : ℝ) * (L : ℝ)) + 1 := by positivity
  rw [max_eq_right (le_of_lt hfit), ge_iff_le,
    div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (L : ℝ)) hden, div_mul_eq_mul_div,
    div_le_iff₀ hκpos]
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hκL : (1 : ℝ) ≤ (κ.natAbs : ℝ) * (L : ℝ) := by
    have h1 : (1 : ℕ) ≤ κ.natAbs :=
      Nat.one_le_iff_ne_zero.mpr (fun h0 => hκ (Int.natAbs_eq_zero.mp h0))
    have h2 : (1 : ℝ) ≤ (κ.natAbs : ℝ) := by exact_mod_cast h1
    nlinarith [h2, hLpos]
  nlinarith [hN1, hκL, hLpos, hκpos]

/-! ## The level-two mean bound, in-file

The single remaining input of this file is the **residual** `ResidSharpOne P cdiag cpeel` below: the
level-two box-norm inverse theorem on the `Hyp`-data whose third function satisfies the two
elementary-branch complements — *no* large character correlation (at the free threshold
`(1/2)γ^{K₀/4}N₁`) and a *small* level-one box-norm power.  Both complementary branches are
*elementary*, and both are proved here (the same Fourier split that `meanBoundPow.lean` and
`bandResidualSmallFourier.lean` perform for the band area, at a free threshold, plus the level
raising `uNormPow_two_ge_of_uNorm_one`).

To keep the file self-contained (and to avoid the import cycle with `meanBoundPow.lean`, which
imports this file) the level-two mean bound is reproved here from the level-one mean bound
(`boxNormPow_one_arithIcc_ge_meanGen` below, itself the Cauchy–Schwarz step against the constant
function together with the normal form `Track.boxNormPow_one_arithIcc_window`) and the in-file
`uNormPow_level_raise_win`.  It is `uNormPow_ge_mean_pow` of `meanBoundPow.lean` under a different
name. -/

/-- **Re-indexing a window sum.**  If `F` is supported in `symIcc N` and `N + |d| ≤ A`, then
shifting the window `symIcc A` by `-d` exhausts the support of `F`. -/
lemma sum_symIcc_add_eq_tsum' {N A : ℕ} {d : ℤ} (hNA : N + d.natAbs ≤ A) {F : ℤ → ℂ}
    (hF : SupportIn F N) : ∑ x ∈ symIcc A, F (x + d) = ∑' x : ℤ, F x := by
  have hsub : symIcc N ⊆ (symIcc A).image (fun x : ℤ => x + d) := by
    intro y hy
    rw [symIcc, Finset.mem_Icc] at hy
    rw [Finset.mem_image]
    refine ⟨y - d, ?_, by ring⟩
    rw [symIcc, Finset.mem_Icc]
    have hA : ((N + d.natAbs : ℕ) : ℤ) ≤ (A : ℤ) := by exact_mod_cast hNA
    have hA' : (N : ℤ) + (d.natAbs : ℤ) ≤ (A : ℤ) := by
      push_cast at hA ⊢
      exact hA
    have hyabs : |y| ≤ (N : ℤ) := abs_le.mpr hy
    have h1 : |y - d| ≤ |y| + |d| := by
      simpa using (abs_sub_le y 0 d)
    have h2 : |d| = (d.natAbs : ℤ) := by rw [Int.natCast_natAbs]
    rw [h2] at h1
    exact abs_le.mp (by linarith)
  have hzero : ∀ x : ℤ, x ∉ symIcc N → F x = 0 := by
    intro x hx
    refine hF x ?_
    rw [symIcc, Finset.mem_Icc] at hx
    by_contra hcon
    push_neg at hcon
    have h1 : (x.natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast hcon
    rw [Int.natCast_natAbs] at h1
    exact hx (abs_le.mp h1)
  have himg : ∑ x ∈ (symIcc A).image (fun a : ℤ => a + d), F x = ∑ x ∈ symIcc A, F (x + d) :=
    Finset.sum_image (f := F) (g := fun a : ℤ => a + d) (fun a _ b _ hab => by simpa using hab)
  rw [tsum_eq_sum (s := symIcc N) hzero, ← himg]
  exact (Finset.sum_subset hsub (fun x _ hxN => hzero x hxN)).symm

/-- **The level-one mean bound.**  Cauchy–Schwarz against the constant function: the window sums
`∑_{y ≤ H} F (x + cy)` add up to `H` times the total mass of `F`, so the box norm dominates
`‖∑ F‖² / ((2N+1)(2(N+H|c|)+1))`.  (This is `Work.Peluse.PETTwo.boxNormPow_one_arithIcc_ge_mean`,
reproved here so that this file does not depend on the (partly open) `PETTwo` area.) -/
theorem boxNormPow_one_arithIcc_ge_meanGen {c : ℤ} (hc : c ≠ 0) {N H : ℕ} (hH : 1 ≤ H)
    {F : ℤ → ℂ} (hFs : SupportIn F N) :
    ‖∑' x : ℤ, F x‖ ^ 2
        / (((2 * N + 1 : ℕ) : ℝ) * ((2 * (N + H * c.natAbs) + 1 : ℕ) : ℝ))
      ≤ Work.Peluse.boxNormPow 1 (fun _ : Fin 1 => Work.Peluse.arithIcc c H)
          (Work.Peluse.symIcc N) F := by
  classical
  rw [Work.Peluse.Track.boxNormPow_one_arithIcc_window hc hH F hFs]
  set W : Finset ℤ := Work.Peluse.symIcc (N + H * c.natAbs) with hW
  set A : ℤ → ℂ := fun x => ∑ y ∈ Finset.Icc 1 H, F (x + c * (y : ℤ)) with hA
  have hcardS : (((Work.Peluse.symIcc N).card : ℕ) : ℝ) = 2 * (N : ℝ) + 1 := by
    rw [card_symIcc]; push_cast; ring
  have hcardW : ((W.card : ℕ) : ℝ) = 2 * ((N + H * c.natAbs : ℕ) : ℝ) + 1 := by
    rw [hW, card_symIcc]; push_cast; ring
  have hcs : ‖∑ x ∈ W, A x‖ ^ 2 ≤ (W.card : ℝ) * ∑ x ∈ W, ‖A x‖ ^ 2 := by
    have h1 : ‖∑ x ∈ W, A x‖ ≤ ∑ x ∈ W, ‖A x‖ := norm_sum_le W A
    have h2 : (∑ x ∈ W, ‖A x‖) ^ 2 ≤ (W.card : ℝ) * ∑ x ∈ W, ‖A x‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    exact le_trans (pow_le_pow_left₀ (norm_nonneg _) h1 2) h2
  have hstep : ∀ y ∈ Finset.Icc 1 H, (∑ x ∈ W, F (x + c * (y : ℤ))) = ∑' x : ℤ, F x := by
    intro y hy
    refine sum_symIcc_add_eq_tsum' (N := N) (A := N + H * c.natAbs) (d := c * (y : ℤ)) ?_ hFs
    have hyH' : (y : ℤ).natAbs ≤ H := by
      rw [Int.natAbs_natCast]
      exact (Finset.mem_Icc.mp hy).2
    have : (c * (y : ℤ)).natAbs ≤ H * c.natAbs := by
      rw [Int.natAbs_mul, mul_comm c.natAbs]
      exact Nat.mul_le_mul_right _ hyH'
    exact Nat.add_le_add_left this N
  have hsum : ∑ x ∈ W, A x = (H : ℂ) * ∑' x : ℤ, F x := by
    rw [hA, Finset.sum_comm]
    rw [Finset.sum_congr rfl hstep, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    push_cast
    ring
  have hnorm : ‖∑ x ∈ W, A x‖ ^ 2 = ((H : ℝ)) ^ 2 * ‖∑' x : ℤ, F x‖ ^ 2 := by
    rw [hsum, norm_mul, Complex.norm_natCast, mul_pow]
  have hkey : ((H : ℝ)) ^ 2 * ‖∑' x : ℤ, F x‖ ^ 2 ≤ (W.card : ℝ) * ∑ x ∈ W, ‖A x‖ ^ 2 := by
    rw [← hnorm]; exact hcs
  have hH2 : (0 : ℝ) < ((H : ℝ)) ^ 2 := by positivity
  have hone : ‖∑' x : ℤ, F x‖ ^ 2
      ≤ ((W.card : ℝ) * ∑ x ∈ W, ‖A x‖ ^ 2) / ((H : ℝ)) ^ 2 := by
    rw [le_div_iff₀ hH2]
    linarith [hkey]
  calc ‖∑' x : ℤ, F x‖ ^ 2 / (((2 * N + 1 : ℕ) : ℝ) * ((2 * (N + H * c.natAbs) + 1 : ℕ) : ℝ))
      ≤ (((W.card : ℝ) * ∑ x ∈ W, ‖A x‖ ^ 2) / ((H : ℝ)) ^ 2)
          / (((2 * N + 1 : ℕ) : ℝ) * ((2 * (N + H * c.natAbs) + 1 : ℕ) : ℝ)) :=
        div_le_div_of_nonneg_right hone (by positivity)
    _ = (((Work.Peluse.symIcc N).card : ℝ))⁻¹ * (((H : ℝ))⁻¹) ^ 2 * ∑ x ∈ W, ‖A x‖ ^ 2 := by
        rw [hcardS, hcardW]
        have h1 : ((2 * (N : ℝ) + 1)) ≠ 0 := by positivity
        have h2 : (2 * ((N + H * c.natAbs : ℕ) : ℝ) + 1) ≠ 0 := by positivity
        have h3 : ((H : ℝ)) ≠ 0 := by positivity
        field_simp
        push_cast
        ring

private lemma two_mul_two_pow_pred {s : ℕ} (hs : 1 ≤ s) : 2 * 2 ^ (s - 1) = 2 ^ s := by
  cases s with
  | zero => omega
  | succ n => rw [Nat.succ_sub_one, pow_succ]; ring

/-- **The mean bound at every level** (`uNormPow_ge_mean_pow` of `meanBoundPow.lean`, reproved here
so that this file does not depend on a module that imports it). -/
theorem uNormPow_ge_mean_powGen (κ : ℤ) (hκ : κ ≠ 0) (s : ℕ) (hs : 1 ≤ s) :
    ∃ c : ℝ, 0 < c ∧ ∀ (L N : ℕ) (f : ℤ → ℂ), 1 ≤ L → 1 ≤ N → L ≤ N →
      SupportIn f N → (∀ x : ℤ, ‖f x‖ ≤ 1) →
      c * (‖∑' x : ℤ, f x‖ / ((symIcc N).card : ℝ)) ^ (2 ^ s)
        ≤ uNormPow s (arithIcc κ L) (symIcc N) f := by
  obtain ⟨c₁, hc₁pos, hc₁⟩ := uNormPow_level_raise_win 1 s le_rfl hs hκ
  refine ⟨c₁ * (2 : ℝ) ^ (2 ^ s) / ((6 * (κ.natAbs : ℝ) + 9) ^ (2 ^ (s - 1))),
    by positivity, ?_⟩
  intro L N f hL hN hLN hsup hbdd
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hLN' : (L : ℝ) ≤ (N : ℝ) := by exact_mod_cast hLN
  have hk : (0 : ℝ) ≤ (κ.natAbs : ℝ) := by positivity
  have hCS : ((symIcc N).card : ℝ) = (2 * (N : ℝ) + 1) := by
    rw [card_symIcc]; push_cast; ring
  set D : ℝ := (((2 * N + 1 : ℕ) : ℝ)) * (((2 * (N + L * κ.natAbs) + 1 : ℕ) : ℝ)) with hD
  have hDpos : 0 < D := by rw [hD]; positivity
  have hDval : D = (2 * (N : ℝ) + 1) * (2 * ((N : ℝ) + (L : ℝ) * (κ.natAbs : ℝ)) + 1) := by
    rw [hD]; push_cast; ring
  have hlev1 : ‖∑' x : ℤ, f x‖ ^ 2 / D ≤ uNormPow 1 (arithIcc κ L) (symIcc N) f := by
    have h := boxNormPow_one_arithIcc_ge_meanGen (c := κ) (N := N) (H := L) (F := f) hκ hL hsup
    rw [hD]
    simpa only [uNormPow] using h
  have hpow : (‖∑' x : ℤ, f x‖ ^ 2 / D) ^ (2 ^ (s - 1))
      ≤ (uNormPow 1 (arithIcc κ L) (symIcc N) f) ^ (2 ^ (s - 1)) :=
    pow_le_pow_left₀ (by positivity) hlev1 _
  have hraise := hc₁ L N f hLN hL hsup hbdd
  have hkey : c₁ * (‖∑' x : ℤ, f x‖ ^ 2 / D) ^ (2 ^ (s - 1))
      ≤ uNormPow s (arithIcc κ L) (symIcc N) f :=
    le_trans (mul_le_mul_of_nonneg_left hpow hc₁pos.le) hraise
  have hDle : D ≤ (6 * (κ.natAbs : ℝ) + 9) * (N : ℝ) ^ 2 := by
    rw [hDval]
    have h1 : (2 * (N : ℝ) + 1) ≤ 3 * (N : ℝ) := by linarith
    have h2 : (2 * ((N : ℝ) + (L : ℝ) * (κ.natAbs : ℝ)) + 1)
        ≤ (2 * (κ.natAbs : ℝ) + 3) * (N : ℝ) := by
      have hmul : (L : ℝ) * (κ.natAbs : ℝ) ≤ (N : ℝ) * (κ.natAbs : ℝ) :=
        mul_le_mul_of_nonneg_right hLN' hk
      nlinarith [hmul, hN1, hk]
    calc (2 * (N : ℝ) + 1) * (2 * ((N : ℝ) + (L : ℝ) * (κ.natAbs : ℝ)) + 1)
        ≤ (3 * (N : ℝ)) * ((2 * (κ.natAbs : ℝ) + 3) * (N : ℝ)) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = (6 * (κ.natAbs : ℝ) + 9) * (N : ℝ) ^ 2 := by ring
  have h2k : 2 * 2 ^ (s - 1) = 2 ^ s := two_mul_two_pow_pred hs
  have hstep1 : c₁ * (‖∑' x : ℤ, f x‖ ^ 2 / ((6 * (κ.natAbs : ℝ) + 9) * (N : ℝ) ^ 2))
          ^ (2 ^ (s - 1))
      ≤ c₁ * (‖∑' x : ℤ, f x‖ ^ 2 / D) ^ (2 ^ (s - 1)) := by
    have hle : (‖∑' x : ℤ, f x‖ ^ 2 / ((6 * (κ.natAbs : ℝ) + 9) * (N : ℝ) ^ 2))
        ≤ ‖∑' x : ℤ, f x‖ ^ 2 / D :=
      div_le_div_of_nonneg_left (by positivity) hDpos hDle
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hle _) hc₁pos.le
  have hXval : ((6 * (κ.natAbs : ℝ) + 9) * (N : ℝ) ^ 2) ^ (2 ^ (s - 1))
      = (6 * (κ.natAbs : ℝ) + 9) ^ (2 ^ (s - 1)) * (N : ℝ) ^ (2 ^ s) := by
    rw [mul_pow, ← pow_mul, h2k]
  have hnum : (‖∑' x : ℤ, f x‖ ^ 2) ^ (2 ^ (s - 1)) = ‖∑' x : ℤ, f x‖ ^ (2 ^ s) := by
    rw [← pow_mul, h2k]
  have hstep2 : c₁ * (‖∑' x : ℤ, f x‖ ^ 2 / ((6 * (κ.natAbs : ℝ) + 9) * (N : ℝ) ^ 2))
        ^ (2 ^ (s - 1))
      = c₁ * ‖∑' x : ℤ, f x‖ ^ (2 ^ s)
          / ((6 * (κ.natAbs : ℝ) + 9) ^ (2 ^ (s - 1)) * (N : ℝ) ^ (2 ^ s)) := by
    rw [div_pow, hXval, hnum]
    ring
  have hkey2 : c₁ * ‖∑' x : ℤ, f x‖ ^ (2 ^ s)
      / ((6 * (κ.natAbs : ℝ) + 9) ^ (2 ^ (s - 1)) * (N : ℝ) ^ (2 ^ s))
      ≤ uNormPow s (arithIcc κ L) (symIcc N) f := by
    rw [← hstep2]
    exact le_trans hstep1 hkey
  rw [hCS]
  have hstep3 : c₁ * (2 : ℝ) ^ (2 ^ s) / ((6 * (κ.natAbs : ℝ) + 9) ^ (2 ^ (s - 1)))
        * ((‖∑' x : ℤ, f x‖ / (2 * (N : ℝ) + 1)) ^ (2 ^ s))
      ≤ c₁ * ‖∑' x : ℤ, f x‖ ^ (2 ^ s)
          / ((6 * (κ.natAbs : ℝ) + 9) ^ (2 ^ (s - 1)) * (N : ℝ) ^ (2 ^ s)) := by
    have h2z : (2 : ℝ) ^ (2 ^ s) ≠ 0 := by positivity
    have hNz : (N : ℝ) ^ (2 ^ s) ≠ 0 := by positivity
    have hYz : (6 * (κ.natAbs : ℝ) + 9) ^ (2 ^ (s - 1)) ≠ 0 := by positivity
    have hle : ‖∑' x : ℤ, f x‖ / (2 * (N : ℝ) + 1) ≤ ‖∑' x : ℤ, f x‖ / (2 * (N : ℝ)) :=
      div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) (by linarith)
    have hdiv : (‖∑' x : ℤ, f x‖ / (2 * (N : ℝ) + 1)) ^ (2 ^ s)
        ≤ (‖∑' x : ℤ, f x‖ / (2 * (N : ℝ))) ^ (2 ^ s) :=
      pow_le_pow_left₀ (by positivity) hle _
    calc c₁ * (2 : ℝ) ^ (2 ^ s) / ((6 * (κ.natAbs : ℝ) + 9) ^ (2 ^ (s - 1)))
          * ((‖∑' x : ℤ, f x‖ / (2 * (N : ℝ) + 1)) ^ (2 ^ s))
        ≤ c₁ * (2 : ℝ) ^ (2 ^ s) / ((6 * (κ.natAbs : ℝ) + 9) ^ (2 ^ (s - 1)))
          * ((‖∑' x : ℤ, f x‖ / (2 * (N : ℝ))) ^ (2 ^ s)) :=
          mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ = c₁ * ‖∑' x : ℤ, f x‖ ^ (2 ^ s)
          / ((6 * (κ.natAbs : ℝ) + 9) ^ (2 ^ (s - 1)) * (N : ℝ) ^ (2 ^ s)) := by
          rw [div_pow, mul_pow]
          field_simp
  exact le_trans hstep3 hkey2

/-! ## The residual: the single remaining input of this file

`BandHardSharpAt 2 P cdiag cpeel` (the level-two coarse-scale inverse theorem on the data where the
two elementary bounds fail) splits three ways, along the two *elementary* branches of this file:

* **the large-character-correlation branch** (`uNormPow_two_ge_of_charCorr_thr`) is *elementary*: if
  some character correlation of `g₂` is at least `T = (1/2)γ^{K₀/4}N₁` — a threshold that is
  *smaller* than the `bandFourierTheta · γ · N₁` of the area's `NoLargeFourier` — then Peluse's
  modulation invariance `BoxNorm.uNormPow_mul_ee` and the level-two mean bound give
  `meanBoundC P · (T/|symIcc N₁|)⁴ ≤ uNormPow 2 ((dirCoeff P)[dirLen]) (symIcc N₁) g₂`, and
  `T/|symIcc N₁| ≥ γ^{K₀/4}/6`, so `(meanBoundC P / 6⁴) γ^{4⌊K₀/4⌋} ≤ …` and a fortiori
  `(meanBoundC P / 6⁴) γ^{K₀} ≤ …`;
* **the large-level-one branch** (`uNormPow_two_ge_of_uNorm_one`) is *elementary* too: if the
  *level-one* box-norm power of `g₂` at the target's direction set is at least `(1/2)γ^{K₀/2}`, then
  Gowers–Cauchy–Schwarz level raising (the in-file `uNormPow_level_raise_win`) gives
  `(cu/4) γ^{K₀} ≤ uNormPow 2 …`;
* **the residual** `ResidSharp P cdiag cpeel K₀` is the remaining case, in which *both* branches are
  silent — every character correlation of `g₂` is strictly smaller than `(1/2) γ^{K₀/4} N₁`, and the
  level-one box-norm power is strictly smaller than `(1/2) γ^{K₀/2}` — and it is the only place where
  the inverse theorem is still needed.  Its Fourier hypothesis is *implied* by the area's
  `NoLargeFourier N₁ g₂ γ` (`bandResidualSmallFourier.lean`, threshold `(1/2)γN₁`), because
  `K₀ ≥ 4` and `γ ≤ 1` give `γ^{K₀/4} ≤ γ`; this is why the area's named input feeds the residual:
  `Submission/Work/Peluse/UControl/bandCoreFromSF.lean` proves `BandStructureSF P 2 → ResidSharpEx`,
  and hence `BandStructureSF P 2 → bandCore`.

`bandHardSharpAt_two_of_residSharp` assembles the three branches.  `AverResid` is the same statement
with the conclusion in the *averaged-autocorrelation* form of the band area (the one the fit-free
flatness brick `uNormPow_two_ge_flatness_win'` consumes), and `residSharp_of_averResid` converts it
back.

`ResidSharpOne`/`AverResidOne` fix `K₀ = 8`: the smallest exponent that is both `≥ 4` (as the
elementary branch requires) and above the sharp threshold `5` forced by the "chaotic" family of
`NOTES_ucontrol_of_concat_SESSION12.md` §2 (`K₀ ≤ 4` is *false* for `deg P ≥ 3`). -/

/-- The constant of the level-two mean bound at the direction coefficient `dirCoeff P`. -/
noncomputable def meanBoundC (P : Polynomial ℤ) (hP : 2 ≤ P.natDegree) : ℝ :=
  Classical.choose (uNormPow_ge_mean_powGen (dirCoeff P) (dirCoeff_ne_zero hP) 2 (by norm_num))

theorem meanBoundC_pos (P : Polynomial ℤ) (hP : 2 ≤ P.natDegree) : 0 < meanBoundC P hP :=
  (Classical.choose_spec (uNormPow_ge_mean_powGen (dirCoeff P) (dirCoeff_ne_zero hP) 2
    (by norm_num))).1

theorem meanBoundC_spec (P : Polynomial ℤ) (hP : 2 ≤ P.natDegree) (L N : ℕ) (f : ℤ → ℂ)
    (hL : 1 ≤ L) (hN : 1 ≤ N) (hLN : L ≤ N) (hsup : SupportIn f N)
    (hb : ∀ x : ℤ, ‖f x‖ ≤ 1) :
    meanBoundC P hP * (‖∑' x : ℤ, f x‖ / ((symIcc N).card : ℝ)) ^ (2 ^ 2)
      ≤ Work.Peluse.uNormPow 2 (arithIcc (dirCoeff P) L) (symIcc N) f :=
  (Classical.choose_spec (uNormPow_ge_mean_powGen (dirCoeff P) (dirCoeff_ne_zero hP) 2
    (by norm_num))).2 L N f hL hN hLN hsup hb

/-- **A large level-one box-norm power settles the hard input.**  Gowers–Cauchy–Schwarz level
raising (`uNormPow_level_raise_win` with `s₀ = 1`, `s = 2`) turns a lower bound for the *level-one*
box-norm power at the target's direction set into one for the level-two power, at the same scale and
the same window, with no loss other than the absolute constant `c`. -/
theorem uNormPow_two_ge_of_uNorm_one {P : Polynomial ℤ} (hP : 2 ≤ P.natDegree) :
    ∃ c : ℝ, 0 < c ∧ ∀ (L N₁ : ℕ) (f : ℤ → ℂ), 1 ≤ L → L ≤ N₁ →
      SupportIn f N₁ → (∀ x : ℤ, ‖f x‖ ≤ 1) →
      c * (Work.Peluse.uNormPow 1 (arithIcc (dirCoeff P) L) (symIcc N₁) f) ^ 2
        ≤ Work.Peluse.uNormPow 2 (arithIcc (dirCoeff P) L) (symIcc N₁) f := by
  obtain ⟨c, hc, h⟩ := uNormPow_level_raise_win 1 2 le_rfl (by norm_num) (dirCoeff_ne_zero hP)
  exact ⟨c, hc, fun L N f hL hLN hsup hb => h L N f hLN hL hsup hb⟩

/-- **The residual of the band's hard input.**  The data of `BandHardSharpAt 2` (including the two
complement hypotheses, stated with the constant `c` that is to be produced) whose third function
`g₂` satisfies *both* of the two elementary-branch complements of this file:

* **no large Fourier coefficient**: `∀ β, ‖∑_{x∈symIcc N₁} g₂ x · ee(βx)‖ < (1/2) γ^{K₀/4} N₁` — the
  area's `NoLargeFourier N₁ g₂ γ` (`bandResidualSmallFourier.lean`, threshold `(1/2)γN₁`) with the
  *smaller* threshold `(1/2)γ^{K₀/4}N₁`; since `K₀ ≥ 4` and `γ ≤ 1` this is *implied* by
  `NoLargeFourier`, which is what lets the named input `BandStructureSF P 2` feed this statement
  (`bandCoreFromSF.lean`), and the branch proved above (`uNormPow_two_ge_of_charCorr_thr` with
  `T = (1/2)γ^{K₀/4}N₁`) is the corresponding elementary conclusion;
* **small level-one box-norm power**: `uNormPow 1 (κ[L]) (symIcc N₁) g₂ < (1/2) γ^{K₀/2}`, whose
  complement is settled elementarily by `uNormPow_two_ge_of_uNorm_one` (level raising).

Both thresholds are *smaller* for larger `K₀` (and so are the conclusion and the complemented
domain), so the residual is stated at the free exponent `K₀`, which is also the target's data
threshold `K₀ ≤ K`; the dichotomy `bandHardSharpAt_two_of_residSharp` below consumes it at any
`K₀ ≥ 4`.  `ResidSharpOne` fixes `K₀ = 8`, the smallest round value that is both `≥ 4` and above the
sharp threshold `5` forced by the "chaotic" family of `NOTES_ucontrol_of_concat_SESSION12.md` §2
(`K₀ ≤ 4` is *false* for `deg P ≥ 3`).

(The previous sessions stated the residual with the threshold `(1/2)γN₁` — the area's
`NoLargeFourier` — and with no level-one hypothesis; the two extra, *proved* branches above are what
allows the domain to be cut down here.) -/
def ResidSharp (P : Polynomial ℤ) (cdiag cpeel : ℝ) (K₀ : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ A' : ℝ, 1 ≤ A' → ∀ C : ℝ, 1 ≤ C → ∀ K : ℕ, K₀ ≤ K →
    ∀ (N N₁ : ℕ) (g₀ g₁ g₂ : ℤ → ℂ) (γ δ' : ℝ),
      Hyp P A' C K N N₁ g₀ g₁ g₂ γ δ' →
      (cdiag * γ ^ (2 ^ 2) / ((dirLen P δ' N : ℝ) ^ (2 - 1)) < c * γ ^ K₀) →
      (cpeel * γ ^ (2 ^ 2) / ((dirLen P δ' N : ℝ) ^ 2) < c * γ ^ K₀) →
      (∀ β : ℝ, ‖∑ x ∈ symIcc N₁, g₂ x * Work.Peluse.ee (β * (x : ℝ))‖
        < (1 / 2) * γ ^ (K₀ / 4) * (N₁ : ℝ)) →
      (Work.Peluse.uNormPow 1 (arithIcc (dirCoeff P) (dirLen P δ' N)) (symIcc N₁) g₂
        < (1 / 2) * γ ^ (K₀ / 2)) →
      c * γ ^ K₀ ≤ Work.Peluse.uNormPow 2
        (arithIcc (dirCoeff P) (dirLen P δ' N)) (symIcc N₁) g₂

/-- **The residual with the exponent left free** — the form in which the area's named input
`BandStructureSF` feeds this file.  It asks for a *single* exponent `K₀ ≥ 4` (the same one serving as
the target's data-threshold and as the power of `γ` in the conclusion) for which the residual holds.
This is the weakest formulation of the obligation — the prover may take `K₀` as large as they like,
and larger `K₀` weakens the conclusion and *all four* of the complemented-hypothesis thresholds — and
its domain is the sub-domain of `BandStructureSF P 2`'s on which the two extra elementary branches of
this file (`uNormPow_two_ge_of_charCorr_thr`, `uNormPow_two_ge_of_uNorm_one`) are silent.  (In truth
`K₀ ≥ 5` is required: `K₀ ≤ 4` is *false* for `deg P ≥ 3`, by the chaotic family of
`NOTES_ucontrol_of_concat_SESSION12.md` §2; that costs nothing, the witness being free.) -/
def ResidSharpEx (P : Polynomial ℤ) (cdiag cpeel : ℝ) : Prop :=
  ∃ K₀ : ℕ, 4 ≤ K₀ ∧ ResidSharp P cdiag cpeel K₀

/-- The residual at the fixed exponent `K₀ = 8`, a convenient representative of `ResidSharpEx`. -/
def ResidSharpOne (P : Polynomial ℤ) (cdiag cpeel : ℝ) : Prop :=
  ResidSharp P cdiag cpeel 8

end

end Work.Peluse.UControl
