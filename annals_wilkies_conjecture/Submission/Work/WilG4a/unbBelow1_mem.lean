/-
  WilG4a : `Work.WilG4a.unbBelow1_mem`.

  `unbBelow1 p Z = {z | Fin.init z ∈ (projLast (LB1 p Z))ᶜ}` is obtained from `LB1 p Z` by
  three of the four operations of the `Ω`-calculus: one projection (`SOMin.proj`), one
  complement (`SOMin.compl`) and one coordinate lift of the form `SOMin.prod_right`.  Hence
  its format gain over `LB1 p Z` is exactly `3`, its degree is unchanged, and the whole proof
  is the bookkeeping of `LB1_mem`.
-/
import Mathlib
import Submission.Work.WilG4a.NoStripDefs
import Submission.Work.WilG4a.LB1_mem

namespace Work.WilG4a

open WilkiesDesign

theorem unbBelow1_mem (S : WilkiesDesign.SOMin) (p F : ℕ) :
    ∃ (A c c' : ℕ), ∀ (D : ℕ) (Z : Set (Fin (p + 1) → ℝ)), Z ∈ S.Ω F D (p + 1) →
      Work.WilG4a.unbBelow1 p Z ∈ S.Ω (A + F) (c * D + c') (p + 1) := by
  obtain ⟨A₀, c₀, d₀, hLB⟩ := LB1_mem S p F
  refine ⟨A₀ + 3, c₀, d₀, ?_⟩
  intro D Z hZ
  have h1 : projLast (LB1 p Z) ∈ S.Ω (A₀ + F + 1) (c₀ * D + d₀) p := S.proj (hLB D Z hZ)
  have h2 : (projLast (LB1 p Z))ᶜ ∈ S.Ω (A₀ + F + 2) (c₀ * D + d₀) p := S.compl h1
  have h3 : {z : Fin (p + 1) → ℝ | Fin.init z ∈ (projLast (LB1 p Z))ᶜ} ∈
      S.Ω (A₀ + F + 3) (c₀ * D + d₀) (p + 1) := S.prod_right h2
  rw [show A₀ + 3 + F = A₀ + F + 3 by omega]
  exact h3

end Work.WilG4a
