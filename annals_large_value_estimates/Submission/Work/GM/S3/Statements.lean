import Mathlib
import Submission.GM.Interfaces
import Submission.Work.GM.S3.Base
import Submission.Work.GM.S3.Defs

/-!
# Statement-level interfaces of the area `Work.GM.S3`

The pieces of the area are proved as separate files (`R_l2`, `R_l4`, `lemma84`, `prop71_main`,
`prop72`, ...).  The properties are repeated here as `Prop`-valued definitions so that the final
assembly (GM Prop 10.1, and then `S3Statement`) can be stated and proved *from the pieces as
hypotheses*: each proved piece contributes its statement by definitional equality, e.g.

`example : R_l2Statement := R_l2`

(no unfolding by hand is needed, the definitions are written as the identical formula).

## History of `Prop72Statement` (read this if the statement looks impossible)

An earlier version of `Prop72Statement` asked for `IsBumpAtOne ψ₂ 2` **together with**
`∀ x ∈ Icc (1/2) 2, 1 ≤ ψ₂ x`.  That conjunction is *unsatisfiable* (the support clause makes `ψ₂`
vanish on `(-∞, 1/2)`, so continuity forces `ψ₂ (1/2) = 0`).  The current version uses the support
constant `C₀ = 4` for both bumps (supports `[-4,4]` and `[1/4,4]`, strictly containing the
majorized sets `[-1,1]` and `[1/2,2]`) and is satisfiable.  It also fixes the smoothing frequency
of `Rtilde` at exactly `T = M N` (parameter `T/N`) and requires `T/N ≤ M`; see `ROADMAP.md` for why
the §10 assembly needs exactly this.  So: `Prop72Statement` is *provable as stated now*; do not try
to refute it (an earlier version was indeed refutable, which is why it was changed).
-/

namespace Work.GM.S3

open Complex Finset MeasureTheory
open scoped BigOperators

/-- **GM Lemma 8.2** (L² bound for `R`), exactly as proved in `Work/GM/S3/R_l2`. -/
def R_l2Statement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ W : Finset ℝ,
    (∀ t ∈ W, t ∈ Set.Icc 0 (Submission.LargeValues.M N)) →
    Submission.GM.Separated W ((Submission.LargeValues.M N) ^ ε) →
    ∫ v in (1 : ℝ)..2, ‖Submission.GM.Rfun W v‖ ^ 2 ≤ C * (N : ℝ) ^ ε * (W.card : ℝ)

/-- **GM Lemma 8.3** (L⁴ bound for `R`), exactly as proved in `Work/GM/S3/R_l4`. -/
def R_l4Statement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ W : Finset ℝ,
    (∀ t ∈ W, t ∈ Set.Icc 0 (Submission.LargeValues.M N)) →
    Submission.GM.Separated W ((Submission.LargeValues.M N) ^ ε) →
    ∫ v in (1 : ℝ)..2, ‖Submission.GM.Rfun W v‖ ^ 4 ≤
      C * (N : ℝ) ^ ε * (Submission.GM.energy W : ℝ)

/-- **GM 8.4** (Fourier decay of smoothings of `|R|²`), exactly as proved in `Work/GM/S3/lemma84`. -/
def Lemma84Statement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ C₀ : ℝ, 1 ≤ C₀ →
  ∀ (ψ₁ ψ₂ ψ₃ : ℝ → ℝ), IsBumpAtOne ψ₁ C₀ →
    IsBumpAtOne ψ₂ C₀ → IsBumpAtZero ψ₃ C₀ →
  ∃ c : ℕ → ℝ → ℝ,
    ∀ N : ℕ, 1 ≤ N → ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc 0 (Submission.LargeValues.M N)) →
      Submission.GM.Separated W ((Submission.LargeValues.M N) ^ ε) →
    ∀ B : ℝ, 1 ≤ (N : ℝ) * B → (N : ℝ) * B ≤ Submission.LargeValues.M N →
    ∀ (j : ℕ) (η : ℝ), 0 < η → ∀ ξ : ℝ, ξ ≠ 0 →
      ‖FourierTransform.fourier
          (fun u => ((ψ₁ u * RtildeSq W N B ψ₃ ψ₂ u : ℝ) : ℂ)) ξ‖ ≤
        c j η * (Submission.LargeValues.M N) ^ η *
          (Submission.LargeValues.M N / |ξ|) ^ j *
          sSup (Set.range (fun u => ψ₁ u * RtildeSq W N B ψ₃ ψ₂ u))

/-- **GM 7.2** (expansion of `S₃`), in the form consumed by the §10 assembly (GM Prop 10.1).

The two bumps `ψ₁`, `ψ₂` are quantified **before** `∀ N, ∀ W`: this is essential.  With the `∃`
inside `∀ N, ∀ W` the witnesses could be inflated (`ψ₁ := γ + K·φ` satisfies every structural
clause for every `K`, and `R̃²` — hence the right-hand side — scales with `K`), so the statement
would be true but useless, and the §10 assembly could not be closed with a uniform constant; see
`NOTES_prop101_interface_gap.md` and `not_uniform_S30.lean`.

For every `ε, δ > 0` there are `C > 0`, `N₀` and a **fixed** pair of bumps `ψ₁`, `ψ₂` (smooth,
non-negative, `≤ 1`, with `IsBumpAtZero ψ₁ 4`, `IsBumpAtOne ψ₂ 4`, `ψ₁ ≥ 1` on `|x| ≤ 1` and
`ψ₂ ≥ 1` on `[1/2,2]`) such that for every `N ≥ N₀` and every `W ⊆ [0, M N]` that is
`(M N)^ε`-separated there are dyadic scales and a smoothing constant with

`1 ≤ M₁`, `M₁ ≤ M`, `M ≤ (M N)^{1+δ}/N`, `32 ≤ N B`, `N B ≤ M N`, `B ≤ M`, `M ≤ N B`

and, with `R̃ = Rtilde W N B ψ₁ ψ₂` (GM (7.5) with parameter `B`),

`‖Spart 3 N W‖ ≤ C N^δ (N²/M) Σ_{|m₁|∼M₁, |m₂|,|m₃|≍M} ∫_{v∈[1/2,2]} ‖R(v)‖ ·
   R̃((m₁v+m₃)/(m₂v)) · R̃((m₁v+m₃)/m₂) dv + C N^{-20}`,

where `|m₁|∼M₁` means `M₁ < |m₁| ≤ 2M₁` and `|m₂|,|m₃| ≍ M` means `M < |m₂|,|m₃| ≤ 2M`.

The conditions on `B` are exactly what the assembly consumes: `N B ≤ M N` is the hypothesis of
`Lemma84Statement` (GM 8.4), `B ≤ M` puts the constraint region `|v₂-(m₁v₁+m₃)/(-m₂)| ⪅ 1/(M N)`
of Proposition 7.1 inside the smoothing window `1/(N B)`, `M ≤ N B` compares the window average
with the region integral, and `32 ≤ N B` keeps the support of `R̃` inside a fixed interval (so that
the assembly can pick a fixed bump `γ` with `γ = 1` on that support). -/
def Prop72Statement : Prop :=
  ∀ ε δ : ℝ, 0 < ε → 0 < δ → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∃ (ψ₁ ψ₂ : ℝ → ℝ),
    IsBumpAtZero ψ₁ 4 ∧ IsBumpAtOne ψ₂ 4 ∧
    (∀ x, ψ₁ x ≤ 1) ∧ (∀ x, ψ₂ x ≤ 1) ∧
    (∀ x, |x| ≤ 1 → 1 ≤ ψ₁ x) ∧ (∀ x ∈ Set.Icc (1 / 2 : ℝ) 2, 1 ≤ ψ₂ x) ∧
    (∀ N : ℕ, N₀ ≤ N → ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc 0 (Submission.LargeValues.M N)) →
        Submission.GM.Separated W ((Submission.LargeValues.M N) ^ ε) →
      ∃ (M₁ M B : ℝ),
        1 ≤ M₁ ∧ M₁ ≤ M ∧ M ≤ (Submission.LargeValues.M N) ^ (1 + δ) / (N : ℝ) ∧
        32 ≤ (N : ℝ) * B ∧ (N : ℝ) * B ≤ Submission.LargeValues.M N ∧
        B ≤ M ∧ M ≤ (N : ℝ) * B ∧
        ‖Submission.GM.Spart 3 N W‖ ≤
          C * (N : ℝ) ^ δ * ((N : ℝ) ^ 2 / M) *
            (∑ m₁ ∈ (Finset.Icc (-⌊2 * M₁⌋) ⌊2 * M₁⌋).filter (fun m : ℤ => M₁ < |(m : ℝ)|),
              ∑ m₂ ∈ (Finset.Icc (-⌊2 * M⌋) ⌊2 * M⌋).filter (fun m : ℤ => M < |(m : ℝ)|),
                ∑ m₃ ∈ (Finset.Icc (-⌊2 * M⌋) ⌊2 * M⌋).filter (fun m : ℤ => M < |(m : ℝ)|),
                  ∫ v in (1 / 2 : ℝ)..2,
                    ‖Submission.GM.Rfun W v‖ *
                      Rtilde W N B ψ₁ ψ₂ (((m₁ : ℝ) * v + (m₃ : ℝ)) / ((m₂ : ℝ) * v)) *
                      Rtilde W N B ψ₁ ψ₂ (((m₁ : ℝ) * v + (m₃ : ℝ)) / (m₂ : ℝ)))
          + C * (N : ℝ) ^ (-20 : ℤ))

/-- **GM 8.4 with the cap removed** (the paper's `B ⪅ T`): the body of `Lemma84Statement` with the
hypothesis `(N : ℝ) * B ≤ M N` deleted.  See `NOTES_prop72_obstruction_and_restructure.md`. -/
def Lemma84RelaxedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ C₀ : ℝ, 1 ≤ C₀ →
  ∀ (ψ₁ ψ₂ ψ₃ : ℝ → ℝ), IsBumpAtOne ψ₁ C₀ →
    IsBumpAtOne ψ₂ C₀ → IsBumpAtZero ψ₃ C₀ →
  ∃ c : ℕ → ℝ → ℝ,
    ∀ N : ℕ, 1 ≤ N → ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc 0 (Submission.LargeValues.M N)) →
      Submission.GM.Separated W ((Submission.LargeValues.M N) ^ ε) →
    ∀ B : ℝ, 1 ≤ (N : ℝ) * B →
    ∀ (j : ℕ) (η : ℝ), 0 < η → ∀ ξ : ℝ, ξ ≠ 0 →
      ‖FourierTransform.fourier
          (fun u => ((ψ₁ u * RtildeSq W N B ψ₃ ψ₂ u : ℝ) : ℂ)) ξ‖ ≤
        c j η * (Submission.LargeValues.M N) ^ η *
          (Submission.LargeValues.M N / |ξ|) ^ j *
          sSup (Set.range (fun u => ψ₁ u * RtildeSq W N B ψ₃ ψ₂ u))

/-- **GM 7.2 with the cap on the smoothing frequency relaxed**: the body of `Prop72Statement` with
`(N : ℝ) * B ≤ M N` replaced by `(N : ℝ) * B ≤ (M N) ^ (1 + δ)`, as the paper's `B ⪅ T` requires
for the dyadic boxes with `T/N < M ≤ (M N)^{1+δ}/N`.  See
`NOTES_prop72_obstruction_and_restructure.md`. -/
def Prop72RelaxedStatement : Prop :=
  ∀ ε δ : ℝ, 0 < ε → 0 < δ → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∃ (ψ₁ ψ₂ : ℝ → ℝ),
    IsBumpAtZero ψ₁ 4 ∧ IsBumpAtOne ψ₂ 4 ∧
    (∀ x, ψ₁ x ≤ 1) ∧ (∀ x, ψ₂ x ≤ 1) ∧
    (∀ x, |x| ≤ 1 → 1 ≤ ψ₁ x) ∧ (∀ x ∈ Set.Icc (1 / 2 : ℝ) 2, 1 ≤ ψ₂ x) ∧
    (∀ N : ℕ, N₀ ≤ N → ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc 0 (Submission.LargeValues.M N)) →
        Submission.GM.Separated W ((Submission.LargeValues.M N) ^ ε) →
      ∃ (M₁ M B : ℝ),
        1 ≤ M₁ ∧ M₁ ≤ M ∧ M ≤ (Submission.LargeValues.M N) ^ (1 + δ) / (N : ℝ) ∧
        32 ≤ (N : ℝ) * B ∧ (N : ℝ) * B ≤ (Submission.LargeValues.M N) ^ (1 + δ) ∧
        B ≤ M ∧ M ≤ (N : ℝ) * B ∧
        ‖Submission.GM.Spart 3 N W‖ ≤
          C * (N : ℝ) ^ δ * ((N : ℝ) ^ 2 / M) *
            (∑ m₁ ∈ (Finset.Icc (-⌊2 * M₁⌋) ⌊2 * M₁⌋).filter (fun m : ℤ => M₁ < |(m : ℝ)|),
              ∑ m₂ ∈ (Finset.Icc (-⌊2 * M⌋) ⌊2 * M⌋).filter (fun m : ℤ => M < |(m : ℝ)|),
                ∑ m₃ ∈ (Finset.Icc (-⌊2 * M⌋) ⌊2 * M⌋).filter (fun m : ℤ => M < |(m : ℝ)|),
                  ∫ v in (1 / 2 : ℝ)..2,
                    ‖Submission.GM.Rfun W v‖ *
                      Rtilde W N B ψ₁ ψ₂ (((m₁ : ℝ) * v + (m₃ : ℝ)) / ((m₂ : ℝ) * v)) *
                      Rtilde W N B ψ₁ ψ₂ (((m₁ : ℝ) * v + (m₃ : ℝ)) / (m₂ : ℝ)))
          + C * (N : ℝ) ^ (-20 : ℤ))

end Work.GM.S3
