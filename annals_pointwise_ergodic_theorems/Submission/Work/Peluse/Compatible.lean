/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Submission.Work.Peluse.Statement
import Submission.Work.KMTContract.Areas

/-!
# Compatibility of `Work.Peluse.PeluseInverseKMT` with the contract subproject

The contract subproject `KMTContract` (`Submission/Work/KMTContract/Areas.lean`, marked "DRAFT — not
yet frozen") freezes Area A2 as its own `Work.KMTContract.PeluseInverseKMT` / `AreaA2`.  This module
records that the statement of `Submission/Work/Peluse/Statement.lean` is *literally the same*, so
that whichever of the two is used, `AreaA2` transfers.

The only notational difference is that the contract writes the progression sum out
(`∑' x, ‖(N')⁻¹ ∑_{m ∈ [N']} f (x + q m)‖`) where this area uses the definition
`Work.Peluse.progAvgSum` of `Basic.lean`; the two are definitionally equal (`rfl`).
-/

set_option autoImplicit false

open scoped BigOperators
open Polynomial

namespace Work.Peluse

/-- `progAvgSum` is the sum displayed in the contract's `PeluseInverseKMT`. -/
theorem progAvgSum_eq (N' : ℕ) (q : ℤ) (f : ℤ → ℂ) :
    progAvgSum N' q f
      = ∑' x : ℤ, ‖(N' : ℂ)⁻¹ * ∑ m ∈ Finset.Icc 1 N', f (x + q * (m : ℤ))‖ :=
  rfl

/-- The two statements of Area A2 are equivalent. -/
theorem peluseInverseKMT_iff (P : Polynomial ℤ) :
    Work.KMTContract.PeluseInverseKMT P ↔ PeluseInverseKMT P := by
  constructor
  · intro h A hA
    obtain ⟨C, K, hC, hK, hrest⟩ := h A hA
    refine ⟨C, K, hC, hK, ?_⟩
    intro N N₀ δ f g hh hN hδ0 hδ1 hN₀A hsf hsg hsh hbf hbg hbh hmain
    rcases hrest N N₀ δ f g hh hN hδ0 hδ1 hN₀A hsf hsg hsh hbf hbg hbh hmain with h' | h'
    · exact Or.inl h'
    · right
      obtain ⟨q, N', h1, h2, h3, h4, h5, h6⟩ := h'
      exact ⟨q, N', h1, h2, h3, h4, h5, by rw [progAvgSum_eq]; exact h6⟩
  · intro h A hA
    obtain ⟨C, K, hC, hK, hrest⟩ := h A hA
    refine ⟨C, K, hC, hK, ?_⟩
    intro N N₀ δ f g hh hN hδ0 hδ1 hN₀A hsf hsg hsh hbf hbg hbh hmain
    rcases hrest N N₀ δ f g hh hN hδ0 hδ1 hN₀A hsf hsg hsh hbf hbg hbh hmain with h' | h'
    · exact Or.inl h'
    · right
      obtain ⟨q, N', h1, h2, h3, h4, h5, h6⟩ := h'
      exact ⟨q, N', h1, h2, h3, h4, h5, by simpa only [progAvgSum, progAvg, norm_mul,
        Complex.norm_natCast] using h6⟩

/-- `AreaA2` transfers between this area and the contract subproject. -/
theorem areaA2_iff : Work.KMTContract.AreaA2 ↔ AreaA2 :=
  forall_congr' fun P => imp_congr_right fun _ => peluseInverseKMT_iff P

end Work.Peluse
