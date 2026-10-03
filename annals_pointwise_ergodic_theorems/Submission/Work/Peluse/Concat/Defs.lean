import Mathlib
import Submission.Work.Peluse.Nodes
import Submission.Work.Peluse.BoxNorm.boxNorm_pow

/-!
# The intermediate statements of the concatenation chapter (Peluse §5 + Lemma 4.10)

This module records, as `Prop`-valued definitions, the two halves of the proof of Peluse's
Theorem 3.5 (the main concatenation result, `Work.Peluse.PeluseConcatenation`):

* `ExpansionPET` — the target's hypothesis (an average over `a ∈ [M₂]` of the level-`s` box norm
  with the direction sets `c(a+b_i)[M₁]`) implies, after the *expansion* of the box sum and one
  application of Peluse's Lemma 4.10 (the PET/linear-shifts step with the directions `k_m - k_i`),
  a lower bound for the *average over `h, h' ∈ [M₁]^s`* of the level-`2^s - 1` box-norm power with
  the direction sets `c((h-h')·ω)[δ'M₂]`, `ω ∈ {0,1}^s ∖ {0}` (Peluse's Lemma 5.6 hypothesis);

* `ConcatBridge` — that average is controlled by the uniformity norm of `f` at the concatenated
  scale `c[δ'M₁M₂]` (Peluse's Lemma 5.6, whose proof is `s` applications of Lemma 5.1).

The enumeration of the nonzero sign patterns is a parameter `ωOf : Fin (2^s - 1) → (Fin s → Bool)`
required to be injective with nonzero values; any two such enumerations give the same box norm,
because the box sum is invariant under a permutation of the direction slots
(`Work.Peluse.Track.boxSumPow_comp_bij_proved`).

The hypotheses `δ' ≤ δ^K` and `1 ≤ M₁M₂(δδ')^{K₀}` are exactly the two "small shift parameter"
hypotheses of `PeluseConcatenation` (the second with its own exponent `K₀`), so that both Props can
be instantiated from the target's hypotheses by taking `K` in the target large.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.Concat

noncomputable section

/-- The integer `ω · u = ∑ i, ω i * u i` of Peluse's notation (for `ω : Fin s → Bool`). -/
def dotZ {s : ℕ} (ω : Fin s → Bool) (u : Fin s → ℤ) : ℤ := ∑ i : Fin s, if ω i then u i else 0

/-- The difference tuple of two shift tuples of `[1,M₁]^s`. -/
def tupSub {s M₁ : ℕ} (h h' : Fin s → Fin M₁) : Fin s → ℤ :=
  fun j => (((h j : ℕ) : ℤ) + 1) - (((h' j : ℕ) : ℤ) + 1)

/-- The (normalised) average over `h, h' ∈ [1,M₁]^s` of the `(2^s-1)`-fold box-norm power of `f`
with the direction sets `c((h-h')·ω)[D]`, `ω` running over the nonzero sign patterns (enumerated by
`ωOf`). -/
def boxAvg (s M₁ : ℕ) (c : ℤ) (ωOf : Fin (2 ^ s - 1) → (Fin s → Bool)) (D : ℕ)
    (N : ℕ) (f : ℤ → ℂ) : ℝ :=
  ((M₁ : ℝ))⁻¹ ^ (2 * s) *
    ∑ h : Fin s → Fin M₁, ∑ h' : Fin s → Fin M₁,
      Work.Peluse.boxNormPow (2 ^ s - 1)
        (fun i : Fin (2 ^ s - 1) => Work.Peluse.arithIcc (c * dotZ (ωOf i) (tupSub h h')) D)
        (Work.Peluse.symIcc N) f

/-! ## The two halves of the proof of Theorem 3.5 -/

/-- **Expansion + the PET/linear-shifts step (the paper's 4.10)**: the first half of the proof of
the concatenation result.  The hypotheses are exactly those of `Nodes.PeluseConcatenation` at the
scale `s`; the conclusion is stated for the *input* exponent `K` and with the constant on the left,
so that this Prop and `ConcatBridge` compose into `PeluseConcatenation`.

**Statement repair (this session).**  The box-norm family in the hypothesis is
`arithIcc (c * (a : ℤ) + b i) M₁` — the source's direction form, with *arbitrary* integer shifts
`b i` (Peluse, arXiv:1909.00309 l. 305, and the form her §5 ladder uses).  Until this session it read
`arithIcc (c * ((a : ℤ) + b i)) M₁`, i.e. shifts forced to be multiples of `c`: a *strict* subfamily
(`Work.Peluse.ConcatenationDir.shift_family_defect`) which the ladder cannot use.
`Work.Peluse.PeluseConcatenation` (`Nodes.lean`) was repaired to match.  A proof of this Prop must
be written against the repaired family (the two agree only for `c = 1`).  See
`NOTES_ucontrol_of_concat_SESSION8.md` §8b. -/
def ExpansionPET : Prop :=
  ∀ s : ℕ, 1 ≤ s → ∃ C : ℝ, 0 < C ∧ ∃ K₀ : ℕ, 1 ≤ K₀ ∧
    ∀ (c : ℤ), 0 < c → ∀ C₀ : ℕ, ∀ A : ℝ, ∀ K : ℕ, 1 ≤ A → K₀ ≤ K →
      ∀ (N M₁ M₂ : ℕ) (b : Fin s → ℤ) (δ δ' : ℝ) (f : ℤ → ℂ),
        1 ≤ M₂ → M₂ ≤ M₁ → 1 ≤ N → (M₁ : ℝ) * (M₂ : ℝ) ≤ (N : ℝ) / (c : ℝ) →
        (∀ i : Fin s, |b i| ≤ (C₀ : ℤ) * (N : ℤ) / (M₁ : ℤ)) →
        Work.Peluse.SupportIn f N → (∀ x : ℤ, ‖f x‖ ≤ 1) →
        0 < δ → δ ≤ 1 → 0 < δ' → A * δ' ≤ δ ^ K → A ≤ (M₂ : ℝ) * (δ * δ') ^ K →
        δ ≤ ((M₂ : ℝ))⁻¹ * ∑ a ∈ Finset.Icc 1 M₂,
          Work.Peluse.boxNorm s (fun i : Fin s => Work.Peluse.arithIcc (c * (a : ℤ) + b i) M₁)
            (Work.Peluse.symIcc N) f →
        ∃ ωOf : Fin (2 ^ s - 1) → (Fin s → Bool),
          Function.Injective ωOf ∧ (∀ i : Fin (2 ^ s - 1), ωOf i ≠ 0) ∧
          C * δ ^ K ≤ boxAvg s M₁ c ωOf (⌊δ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat N f

/-- **Peluse's Lemma 5.6** (whose proof is `s` applications of Lemma 5.1): from the average over
`h,h' ∈ [M₁]^s` of the `(2^s-1)`-fold box-norm power with the direction sets `c((h-h')·ω)[γ'M₂]`
one reaches the uniformity norm of `f` at the concatenated scale `c[γ'M₁M₂]`.  `C₁` is the
constant supplied by `ExpansionPET` and is quantified *before* the conclusion's constant `C` (so
that `C` may depend on it); the conclusion carries the input exponent `K`. -/
def ConcatBridge : Prop :=
  ∀ s : ℕ, 1 ≤ s → ∀ C₁ : ℝ, 0 < C₁ →
    ∃ s' : ℕ, 1 ≤ s' ∧ ∃ C : ℝ, 0 < C ∧ ∃ K₀ : ℕ, 1 ≤ K₀ ∧
    ∀ (c : ℤ), 0 < c → ∀ C₀ : ℕ, ∀ A : ℝ, ∀ K : ℕ, 1 ≤ A → K₀ ≤ K →
      ∀ (N M₁ M₂ : ℕ) (b : Fin s → ℤ) (γ γ' : ℝ) (f : ℤ → ℂ),
        1 ≤ M₂ → M₂ ≤ M₁ → 1 ≤ N → (M₁ : ℝ) * (M₂ : ℝ) ≤ (N : ℝ) / (c : ℝ) →
        (∀ i : Fin s, |b i| ≤ (C₀ : ℤ) * (N : ℤ) / (M₁ : ℤ)) →
        Work.Peluse.SupportIn f N → (∀ x : ℤ, ‖f x‖ ≤ 1) →
        0 < γ → γ ≤ 1 → 0 < γ' → A * γ' ≤ γ ^ K → A ≤ (M₂ : ℝ) * (γ * γ') ^ K →
        (∃ ωOf : Fin (2 ^ s - 1) → (Fin s → Bool),
          Function.Injective ωOf ∧ (∀ i : Fin (2 ^ s - 1), ωOf i ≠ 0) ∧
          C₁ * γ ^ K ≤ boxAvg s M₁ c ωOf (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat N f) →
        C * (γ * γ') ^ K ≤ Work.Peluse.uNorm s'
          (Work.Peluse.arithIcc c (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat) (Work.Peluse.symIcc N) f

end

end Work.Peluse.Concat
