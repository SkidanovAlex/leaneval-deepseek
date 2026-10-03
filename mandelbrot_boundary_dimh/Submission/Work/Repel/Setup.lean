import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Repel.Spec
import Submission.Work.L62.chain

/-!
# REPEL area: the §6 setup data (Shishikura Step 0, Step 1, Lemma 6.1, Lemma 6.2)

This file fixes the vocabulary of the **first stage** of the §6 assembly: the two levels
(level 0 = `f₀ = x + x²` with data `d₀, hd₀`; level 1 = the rescaled horn map
`ǧ₀ = g0germ d₀` with data `d₁, hd₁`), the two starting points `ζa, ζb` of the level-1
Fatou coordinate (Shishikura Lemma 6.2 applied at level 1), and the `η`-independent constants
(`ρ, K₂, y₁, δ, C₀, C₁, C₁'`) of the backward chain.

`Work.Repel.Setup` and `Work.Repel.ChainSetup` are produced by the two lemmas
* `Work.Repel.setup_exists` (`Submission/Work/Repel/setup_exists.lean`),
* `Work.Repel.chain_setup_exists` (`Submission/Work/Repel/chain_setup_exists.lean`),

and consumed by the assembly `Work.Repel.repel` (`Submission/Work/Repel/repel.lean`).

## How `Setup` is built (recipe)

Given `hParab : ParabStatement`, `hHorn : HornStatement`, `hL61 : L61Statement`,
`hF0 : F0FactsStatement`:

1. `hF0` gives `hF0in : InF0 f0 univ` and an inverse orbit `z` of `0` under `f0` with
   `z 0 = 0`, `z j ≠ 0` for `j ≥ 1`, `z → 0`.
2. `d₀ := (hParab f0 univ hF0in.1).some`, `hd₀ := (hHorn f0 univ hF0in.1 d₀).some`.
3. `d₁ := (hParab (g0germ d₀) (Dg0germ d₀ hd₀) (isParabolicGerm_g0germ d₀ hd₀)).some`,
   `hd₁ := (hHorn (g0germ d₀) (Dg0germ d₀ hd₀) (inF0_g0germ d₀ hd₀) d₁).some`,
   `s₀ := s0 d₀` (with `hs₀ : s₀ = s0 d₀` by `rfl`, `hne := s0_ne_zero d₀ hd₀`).
4. `Work.Repel.step1_point d₀ hd₀ hF0in.1 z hz0 hzrec hztend (fun _ _ => trivial) ⟨1, ...⟩`
   gives `w̃₀ ∈ d₀.Dφ` with `d₀.φ (w̃₀ - j) = z j` and
   `π w̃₀ ∉ insert 0 (π '' (hd₀.Bu ∪ hd₀.Bl))`.
5. **Lemma 6.1 is applied at LEVEL 0** (this is the point where one can go wrong):
   `hL61 f0 univ hF0in d₀ hd₀ (piExp w̃₀) (piExp_ne_zero _) hnotdom`
   gives `wa, wb : ℕ → ℂ` with `wa 0 = wb 0 = π w̃₀`, both non-critical inverse orbits of
   `pushdown d₀.E` with `wa (j+1) ∈ π '' (hd₀.Bu ∪ hd₀.Bl)`, `pushdown d₀.E (wa (j+1)) = wa j`,
   `wa → 0`, `wb → 0`, and `wa i ≠ wb j` for `i, j ≥ 1`.
   (The hypothesis `π w̃₀ ∉ insert 0 (π '' (hd₀.Bu ∪ hd₀.Bl))` is exactly Step 1's output; and
   `insert 0 (π '' (hd₀.Bu ∪ hd₀.Bl))` is the domain of `g₀ = pushdown d₀.E`.)
   Do **not** apply `hL61` at level 1 (`hL61 (g0germ d₀) (Dg0germ d₀ hd₀) ... d₁ hd₁`): that
   would give inverse orbits of `pushdown d₁.E`, which is the LEVEL-2 horn map, and its
   hypothesis `w ∉ insert 0 (π '' (hd₁.Bu ∪ hd₁.Bl))` is not available.
6. Rescale: `va j := s₀ * wa j`, `vb j := s₀ * wb j`.  These are inverse orbits of the LEVEL-1
   base germ `ǧ₀ = g0germ d₀` (because `g0germ d₀ = germ1 s₀ d₀.E = ζ ↦ s₀ * pushdown d₀.E (ζ/s₀)`
   and `s₀ * wa (j+1) / s₀ = wa (j+1)`), with `va (j+1) ∈ Dg0germ d₀ hd₀` for `j ≥ 1`
   (as `Dg0germ d₀ hd₀ = s₀ '' insert 0 (π '' (hd₀.Bu ∪ hd₀.Bl))`), `va → 0`, `va 0 = s₀ * π w̃₀ ≠ 0`.
7. Lemma 5.1 at level 1: `d₁.invOrbit va ...` gives `ζa ∈ d₁.Dφ` with
   `∀ j, ζa - j ∈ d₁.Dφ ∧ d₁.φ (ζa - j) = va j`; similarly `ζb` from `vb`.
8. `ζa ∉ d₁.DE`: if `ζa ∈ d₁.DE` then `d₁.φ ζa = va 0 = s₀ * π w̃₀` lies in
   `ParabolicBasin (g0germ d₀) (Dg0germ d₀ hd₀)`, hence (by
   `Work.L62.parabolicBasin_subset`) in `Dg0germ d₀ hd₀ = s₀ '' insert 0 (π '' (hd₀.Bu ∪ hd₀.Bl))`,
   contradicting `π w̃₀ ∉ insert 0 (π '' (hd₀.Bu ∪ hd₀.Bl))` and `s₀ ≠ 0`.  Same for `ζb`.
9. `ζa ≢ ζb (mod ℤ)`: if `ζa = ζb + k`, use `d₁.φ (ζa - (k+1)) = va (k+1)` and
   `d₁.φ (ζb - 1) = vb 1` when `k ≥ 0` (both arguments equal `ζb - 1`), and
   `d₁.φ (ζa - 1) = va 1`, `d₁.φ (ζb - (1-k)) = vb (1-k)` when `k < 0`; either way this yields
   `va i = vb j` with `i, j ≥ 1`, contradicting Lemma 6.1's disjointness.

## How `ChainSetup` is built (recipe)

From `hL62 : L62Statement` applied to `(g0germ d₀, Dg0germ d₀ hd₀)` with
`hF0in : InF0 (g0germ d₀) (Dg0germ d₀ hd₀)` (that is `inF0_g0germ d₀ hd₀`), the data `d₁, hd₁`,
the given `b > 0` and the two points `S.ζa, S.ζb`: this gives `ρ₀ > 0` such that for every
`ρ ∈ (0, ρ₀]` there are `K₂, y₁, δ, C₀, C₁, C₁'` with `IsCompact K₂`, `K₂ ⊆ d₁.DE`,
`d₁.η₀ < y₁`, `0 < δ`, `0 < C₁`, and for every admissible `(R, DR, β)` the L62 chain exists.
Take `ρ := ρ₀ / 2` (so `0 < ρ` and `ρ ≤ ρ₀`), record `y₁, δ, C₀, C₁, C₁'` unchanged, and put
`chain` equal to the L62 statement's concluding `∀ (R) (DR), ... → ∀ β, ... → ∃ W s, ...`
re-read as `∃ W s, Work.L62.IsChain R β DR ζa ζb ρ s C₀ C₁ C₁' W` (`IsChain` has exactly the
fields of that conjunction, in the same order, so `⟨...⟩` works).
-/

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology
open LeanEval.Dynamics.MandelbrotBoundary

noncomputable section

/-- **The §6 setup at the two parabolic levels.**  `d₀, hd₀` are the §4.1 / Prop-5.3 data of
the level-0 germ `f₀ = x + x²`; `d₁, hd₁` those of the level-1 base germ `ǧ₀ = g0germ d₀`;
`s₀` is the rescaling constant `s0 d₀ = ½ (pushdown Ẽ_{f₀})''(0)`; and `ζa, ζb` are the two
starting points of Lemma 6.2 (Shishikura's Step 2), i.e. the `d₁`-Fatou-coordinate preimages of
the two disjoint Lemma 6.1 inverse orbits of `ǧ₀`, which lie in `d₁.Dφ` but not in `d₁.DE`
(so that the chain of Lemma 6.2 starts outside the parabolic basin) and which are not congruent
modulo `ℤ`. -/
structure Setup where
  d₀ : ParabData f0 univ
  hd₀ : HornData d₀
  d₁ : ParabData (g0germ d₀) (Dg0germ d₀ hd₀)
  hd₁ : HornData d₁
  s₀ : ℂ
  hs₀ : s₀ = s0 d₀
  hne : s₀ ≠ 0
  ζa : ℂ
  ζb : ℂ
  hζa : ζa ∉ d₁.DE
  hζb : ζb ∉ d₁.DE
  hdisj : ∀ k : ℤ, ζa ≠ ζb + k

/-- **The chain data of Lemma 6.2 at level 1**, with all constants `η`- and `a₁a₂β`-independent.

`chain` says: for every lifted map `R` on an open `T`-invariant `DR` which is holomorphic there,
contains `K₂ ∪ {|Im| ≥ y₁}`, and is `δ`-close to the level-1 horn map `d₁.E` on that set, and for
every `β` in one period with `|Im β| ≤ b`, the backward chain `W` of Lemma 6.2 exists for
`ĥ = R - β`, with the derivative bounds `C₁, C₁'` and the step bound `C₀`, starting at the ball
`ball ζa ρ` (or `ball ζb ρ`). -/
structure ChainSetup (S : Setup) (b : ℝ) where
  ρ : ℝ
  hρ : 0 < ρ
  K₂ : Set ℂ
  hK₂c : IsCompact K₂
  hK₂sub : K₂ ⊆ S.d₁.DE
  y₁ : ℝ
  hy₁ : S.d₁.η₀ < y₁
  δ : ℝ
  hδ : 0 < δ
  C₀ : ℝ
  C₁ : ℝ
  C₁' : ℝ
  hC₁ : 0 < C₁
  chain : ∀ (R : ℂ → ℂ) (DR : Set ℂ), IsOpen DR → IsTEquivariantOn R DR →
    DifferentiableOn ℂ R DR → K₂ ∪ {w : ℂ | y₁ ≤ |w.im|} ⊆ DR →
    (∀ w ∈ K₂ ∪ {w : ℂ | y₁ ≤ |w.im|}, ‖R w - S.d₁.E w‖ < δ) →
    ∀ β : ℂ, 0 ≤ β.re → β.re ≤ 1 → |β.im| ≤ b →
      ∃ (W : ℕ → Set ℂ) (s : ℝ),
        Work.L62.IsChain R β DR S.ζa S.ζb ρ s C₀ C₁ C₁' W

end

end Work.Repel
