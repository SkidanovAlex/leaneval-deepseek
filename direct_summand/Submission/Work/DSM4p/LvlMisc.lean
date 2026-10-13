import Mathlib
import Submission.Work.DSM4p.Lvl

/-!
# DSM4p — small auxiliary facts of the Route U transfer

* `Work.DSM4p.witt_span_p_teich` — the ideal of `𝕎 R` spanned by `p` and the Teichmüller
  representatives is everything (trivially, since `teichmuller 1 = 1`); this is the generation
  statement used to reduce a statement about all of `𝕎 R` to the generators `p` and
  `teichmuller r`.
-/

namespace Work.DSM4p

universe a

/-- The ideal of the Witt vectors spanned by `p` and the Teichmüller representatives is `⊤`.

This is what lets a statement about `Z ∈ 𝕎 R` be checked on the generators `p` and
`teichmuller p r` (used in the transfer of the cokernel clause to the untilted levels). -/
theorem witt_span_p_teich (p : ℕ) [Fact p.Prime] (R : Type a) [CommRing R] [CharP R p]
    [PerfectRing R p] :
    Ideal.span ({(p : WittVector p R)} ∪ Set.range (WittVector.teichmuller (p := p) (R := R))) =
      ⊤ := by
  rw [Ideal.eq_top_iff_one]
  exact Ideal.subset_span (Or.inr ⟨1, map_one _⟩)

end Work.DSM4p

namespace Work.DSM4p

universe a

open DSMap

/-- **The completed untilted level** `D n := (lvl Q hgr n)^`, the `p`-adic completion of the
untilted level of Route U: the levels of the tower of the frozen node `DSMap.Mix2.area_M4p`. -/
noncomputable abbrev lvlComp {p : ℕ} [Fact p.Prime] {B : Type a} [CommRing B]
    [Fact (¬ IsUnit (p : B))] [IsAdicComplete (Ideal.span {(p : B)}) B]
    (Q : PerfectoidData p B) {gr : ℕ → B} (hgr : IsRootSystem p gr) (n : ℕ) : Type a :=
  AdicCompletion (Ideal.span {((p : lvl Q hgr n))}) (lvl Q hgr n)

end Work.DSM4p
