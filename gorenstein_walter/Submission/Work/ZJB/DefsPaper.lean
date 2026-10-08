import Submission.Work.ZJB.Defs

/-!
# ZJB — Glauberman's conditions in the paper's own convention

Glauberman 1968 writes `x^g = g⁻¹ x g` (his proof of Lemma 5.1 uses `c^{m⁻¹} = m c m⁻¹`),
while Mathlib's `MulAut.conj g` is `x ↦ g x g⁻¹`.  Consequently the *printed* `(C_p)` of p. 1116,

> `W ⊆ S`, `g ∈ G`, `W^g ⊆ S` ⟹ `∃ c ∈ C_G(W), n ∈ N_G(K(S))`, `g = c·n`,

reads in Mathlib's vocabulary as: for `w ∈ W`, `g⁻¹ * w * g ∈ S`, and then `g = c * n` — which is
`ControlsStrongFusionPaper` below.  The contract's `ControlsStrongFusion` (`Defs.lean`) uses the
*same* hypothesis shape with Mathlib's `MulAut.conj` and the same conclusion, i.e. it is the
printed `(C_p)` with `g` replaced by `g⁻¹` *in the hypothesis only*; equivalently it asserts
`Good(W) ⊆ C_G(W)·N_G(K)` where the paper asserts `Good(W) ⊆ N_G(K)·C_G(W)`
(`Good(W) := {x | conj x(W) ⊆ P}`).  `controlsStrongFusionPaper_iff_rev` below records the exact
relation.  See `NOTES_ZJB.md` §5 for the GAP evidence in the intended class.

Everything the source proves — Lemma 5.1, Theorem 5.1, Lemma 5.2, Theorem 5.2 and Theorem B — is
proved here for the *paper's* conditions; the paper's proofs transfer verbatim to this vocabulary.
-/

namespace Work.ZJB

open Work.GW2
open Subgroup

variable {G : Type*} [Group G]

/-- **Glauberman's `(C_p)` (p. 1116), verbatim.**  For the paper `K` is a characteristic functor
and `P = S` a Sylow `p`-subgroup; `W^g ⊆ P` is the paper's `g⁻¹Wg ⊆ P`. -/
def ControlsStrongFusionPaper (P K : Subgroup G) : Prop :=
  ∀ W : Set G, W.Nonempty → W ⊆ (P : Set G) → ∀ g : G,
    (∀ w ∈ W, g⁻¹ * w * g ∈ (P : Set G)) →
    ∃ c n : G, c ∈ centralizer W ∧ n ∈ normalizer (K : Set G) ∧ g = c * n

/-- **Glauberman's `(C_p*)` (p. 1116), verbatim**: the same condition tested on the `p`-subgroups
of `N_G(K)` rather than on subsets of the Sylow subgroup. -/
def ControlsStrongFusionPaperStar (p : ℕ) (K : Subgroup G) : Prop :=
  ∀ W : Subgroup G, W ≤ normalizer (K : Set G) → IsPGroup p W → ∀ g : G,
    (∀ w ∈ W, g⁻¹ * w * g ∈ normalizer (K : Set G)) →
    ∃ c n : G, c ∈ centralizer (W : Set G) ∧ n ∈ normalizer (K : Set G) ∧ g = c * n

/-- `(C_p)` for every Sylow `p`-subgroup, in the paper's convention. -/
def SatisfiesCpPaper (p : ℕ) (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ S : Sylow p G, ControlsStrongFusionPaper (S : Subgroup G) (ZJ (S : Subgroup G))

/-- `(C_p*)` for every Sylow `p`-subgroup, in the paper's convention. -/
def SatisfiesCpPaperStar (p : ℕ) (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ S : Sylow p G, ControlsStrongFusionPaperStar p (ZJ (S : Subgroup G))

/-- The `p`-stable form of Glauberman's Theorem B in the paper's convention — i.e. exactly what
the source's §5–§6 prove (for `Qd(p)`-free groups, which `PStableProp` supplies). -/
def TheoremBStablePaper : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) [Fact p.Prime], p ≠ 2 → IsPStable' p X →
    SatisfiesCpPaper p X

/-- The paper's `(C_p)` with the element inverted is the "reversed product order" form of the
contract's `(C_p)`: both test `Good(W) := {x | conj x(W) ⊆ P}`, and the paper's conclusion
`g = c·n` for `g ∈ Good(W)⁻¹` is the assertion `x ∈ N_G(K)·C_G(W)` for `x ∈ Good(W)`. -/
theorem controlsStrongFusionPaper_iff_rev (P K : Subgroup G) :
    ControlsStrongFusionPaper P K ↔
      ∀ W : Set G, W.Nonempty → W ⊆ (P : Set G) → ∀ x : G,
        (∀ w ∈ W, x * w * x⁻¹ ∈ (P : Set G)) →
        ∃ n c : G, n ∈ normalizer (K : Set G) ∧ c ∈ centralizer W ∧ x = n * c := by
  constructor
  · intro h W hW hWP x hx
    have hx' : ∀ w ∈ W, (x⁻¹)⁻¹ * w * x⁻¹ ∈ (P : Set G) := by
      intro w hw
      simpa using hx w hw
    obtain ⟨c, n, hc, hn, hcn⟩ := h W hW hWP x⁻¹ hx'
    exact ⟨n⁻¹, c⁻¹, (normalizer (K : Set G)).inv_mem hn, (centralizer W).inv_mem hc,
      by simpa [mul_inv_rev] using congrArg Inv.inv hcn⟩
  · intro h W hW hWP g hg
    have hg' : ∀ w ∈ W, g⁻¹ * w * (g⁻¹)⁻¹ ∈ (P : Set G) := by
      intro w hw
      simpa using hg w hw
    obtain ⟨n, c, hn, hc, hnc⟩ := h W hW hWP g⁻¹ hg'
    exact ⟨c⁻¹, n⁻¹, (centralizer W).inv_mem hc, (normalizer (K : Set G)).inv_mem hn,
      by simpa [mul_inv_rev] using congrArg Inv.inv hnc⟩

end Work.ZJB
