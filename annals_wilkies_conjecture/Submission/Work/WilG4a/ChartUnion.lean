/-
  WilG4a — the `n = 1` machinery for BNZ §5.1: bookkeeping for families of charts.

  A chart collection is a `Finset` of functions `(Fin p → ℝ) → ℝ → ℝ`.  The lemmas here are
  the elementary operations used when collections built on a subdivision of the parameter set
  are glued together: monotonicity of the per-chart condition in the parameter set, and unions
  of collections (with the resulting count bound).
-/
import Submission.Work.WilG4a.Defs

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilG4a
open WilkiesConjecture WilkiesDesign

/-- `ChartOK` is monotone in the parameter set: conditions imposed on fewer parameters are
weaker. -/
theorem ChartOK.mono {S : SOMin} {p a bD : ℕ} {Λ Λ' : Set (Fin p → ℝ)} {k r : ℕ}
    {F : Fin k → (Fin p → ℝ) → ℝ → ℝ} {φ : (Fin p → ℝ) → ℝ → ℝ}
    (h : ChartOK S a bD Λ k r F φ) (hsub : Λ' ⊆ Λ) : ChartOK S a bD Λ' k r F φ :=
  ⟨h.1, fun l hl => h.2 l (hsub hl)⟩

/-- `Covers` is monotone in the parameter set. -/
theorem Covers.mono {p : ℕ} {Λ Λ' : Set (Fin p → ℝ)} {k : ℕ}
    {F : Fin k → (Fin p → ℝ) → ℝ → ℝ} {Φ : Finset ((Fin p → ℝ) → ℝ → ℝ)} {ε : ℝ}
    (h : Covers Λ k F Φ ε) (hsub : Λ' ⊆ Λ) : Covers Λ' k F Φ ε :=
  fun l hl => h l (hsub hl)

/-- Union of two chart collections: the per-chart conditions are inherited. -/
theorem ChartOK.union {S : SOMin} {p a bD : ℕ} {Λ : Set (Fin p → ℝ)} {k r : ℕ}
    {F : Fin k → (Fin p → ℝ) → ℝ → ℝ} {Φ Ψ : Finset ((Fin p → ℝ) → ℝ → ℝ)}
    (hΦ : ∀ φ ∈ Φ, ChartOK S a bD Λ k r F φ)
    (hΨ : ∀ φ ∈ Ψ, ChartOK S a bD Λ k r F φ) :
    ∀ φ ∈ Φ ∪ Ψ, ChartOK S a bD Λ k r F φ := by
  intro φ hφ
  rw [Finset.mem_union] at hφ
  exact hφ.elim (hΦ φ) (hΨ φ)

/-- Union of two chart collections: the covering condition is inherited. -/
theorem Covers.union {p : ℕ} {Λ : Set (Fin p → ℝ)} {k : ℕ}
    {F : Fin k → (Fin p → ℝ) → ℝ → ℝ}
    {Φ Ψ : Finset ((Fin p → ℝ) → ℝ → ℝ)} {ε : ℝ}
    (hΦ : Covers Λ k F Φ ε) (hΨ : Covers Λ k F Ψ ε) :
    Covers Λ k F (Φ ∪ Ψ) ε := by
  intro l hl x hx
  rcases hΦ l hl x hx with ⟨φ, hφ, t, ht, h⟩
  exact ⟨φ, Finset.mem_union_left _ hφ, t, ht, h⟩

/-- The number of charts of a finite union is bounded by the sum of the numbers over the
indexing finset. -/
theorem card_biUnion_le {α β : Type*} [DecidableEq β] (s : Finset α)
    (f : α → Finset β) : (s.biUnion f).card ≤ ∑ i ∈ s, (f i).card :=
  Finset.card_biUnion_le

end Work.WilG4a
