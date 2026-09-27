import Mathlib
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.StableTailDefs
import Submission.Work.EQ.H0_invParam_ge
import Submission.Work.EQ.LaTB.la_fan_trichotomy_v2

/-! # Local vocabulary for `junction_nontrivial_of_unbounded_tails`

This module collects the small definitions the target lemma and its helpers share, so that the
pieces can be stated without importing any of the more volatile files:

* `A1` — the axis point `(-1/2, 0)`;
* `Trich a h δ` — Rychlik's Theorem 7(2)(3) with case (i) = *literally constant* words (the body
  of `Work.EQ.LaTB.la_fan_trichotomy_v2`), packaged at a fixed radius;
* `Trich_mono` — its monotonicity in the radius;
* `bwdTailP' a h q M` — the backward tail condition, written out;
* `bwdTailP'_iff` — the identification of the backward tail of a chain with the forward tail of its
  mirror.
-/

namespace Work.EQ.JNT

noncomputable section

open Filter _root_.Topology

/-- The axis point `A₁ = (-1/2, 0)`. -/
abbrev A1 : ℂ × ℂ := ((-1 / 2 : ℂ), (0 : ℂ))

/-- **Rychlik's trichotomy with literally constant words** (the shape of
`Work.EQ.LaTB.la_fan_trichotomy_v2`) at a fixed radius `δ`. -/
def Trich (a : ℝ) (h : ℂ → ℂ) (δ : ℝ) : Prop :=
  ∀ ε : ℕ → List Bool, ∃ φ : ℕ → ℕ, StrictMono φ ∧
    ((∃ ε₀ : List Bool, ∀ k, ε (φ k) = ε₀) ∨
     (∃ (ε₀ ε₁ : List Bool) (s : ℕ → ℕ) (C : ℕ → List Bool),
        Tendsto s atTop atTop ∧
        (∀ k, ε (φ k) = ε₀ ++ List.replicate (s k) true ++ C k) ∧
        (∀ k, fan a h (C k) 0 = A1 ∧ charVal a h (C k) = charVal a h ε₁) ∧
        fan a h ε₁ 0 = A1 ∧ (charVal a h ε₁).im = 0 ∧ 0 < (charVal a h ε₁).re ∧
        (charVal a h ε₁).re ≤ 1) ∨
     ((∀ n : ℕ, ∀ᶠ k in atTop, n ≤ nonA1Count a h (ε (φ k))) ∧
        ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ u ∈ Metric.ball (0 : ℂ) δ,
          ‖(fan a h (ε (φ k)) u).1 - (fan a h (ε (φ k)) 0).1‖ < η ∧
          ‖(fan a h (ε (φ k)) u).2‖ < η * ‖(fan a h (ε (φ k)) u).1 - ((a / 2 : ℝ) : ℂ)‖))

/-- The trichotomy holds at every radius below the one supplied by
`Work.EQ.LaTB.la_fan_trichotomy_v2`. -/
theorem Trich_mono {a : ℝ} {h : ℂ → ℂ} {δ δ' : ℝ} (htri : Trich a h δ) (hδ : δ' ≤ δ) :
    Trich a h δ' := by
  intro ε
  obtain ⟨φ, hφ, hcase⟩ := htri ε
  refine ⟨φ, hφ, ?_⟩
  rcases hcase with h1 | h2 | h3
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · refine Or.inr (Or.inr ⟨h3.1, fun η hη => ?_⟩)
    filter_upwards [h3.2 η hη] with k hk
    exact fun u hu => hk u (Metric.ball_subset_ball hδ hu)

/-- **The trichotomy of `Work.EQ.LaTB.la_fan_trichotomy_v2`, packaged.** -/
theorem exists_Trich {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) : ∃ δ : ℝ, 0 < δ ∧ Trich a h δ := by
  obtain ⟨δ, hδ, htri⟩ := LaTB.la_fan_trichotomy_v2 ha0 ha1 hh
  exact ⟨δ, hδ, htri⟩

/-- The backward tail condition: from index `-M` on, the chain follows the principal unstable
leaf, `q.1 (-n) = ugermC a h (λⁿ ψ₂ q)`. -/
def bwdTailP' (a : ℝ) (h : ℂ → ℂ) (q : ChainData) (M : ℕ) : Prop :=
  ∀ k : ℕ, M ≤ k → q.1 (-(k : ℤ)) = ugermC a h (((eqLam a : ℝ) : ℂ) ^ k * q.2.2)

/-- The backward tail of a chain is the forward tail of its mirror. -/
theorem bwdTailP'_iff {a : ℝ} {h : ℂ → ℂ} (q : ChainData) (M : ℕ) :
    bwdTailP' a h q M ↔ TailP a h (mirrorChain q) M := by
  constructor
  · intro h k hk
    rw [mirrorChain_fst, mirrorChain_psi1]
    rw [h k hk]
    simp [ugermC, eqMirror]
  · intro h k hk
    have h1 := h k hk
    rw [mirrorChain_fst, mirrorChain_psi1] at h1
    have h2 := congrArg eqMirror h1
    simpa [ugermC, eqMirror] using h2

end

end Work.EQ.JNT
