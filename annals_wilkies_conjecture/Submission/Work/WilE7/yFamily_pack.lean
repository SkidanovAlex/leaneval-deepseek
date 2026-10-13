/-
  Area E7 / `CoreLT_succ`: **the `Y`-family packaging step** (uniform bounds in a common fibre dimension).

  The inner `CoreLT n K` call of the `(n+1,K+1)` step takes a `Y`-family of `SemiPf (n + m')` sets and
  returns base cells compatible with each `projFirst n m' '' (Y j).set`.  The candidate sets that must
  be forced into that family live, a priori, in *different* fibre dimensions `m i` (the `π_n`-fibre-cut
  pieces of the ambient family, the `hE5`-strata and frontier strata of the `π_{n+1}`-cut pieces, the
  refined cut of `refinedCutFamily`, the `±1` slices, and the transported outer `Y`).  This file does
  the bookkeeping: pad them all to a common dimension `n + M`, keeping the base projections *equal*
  (not merely contained) and keeping the bounds.

  `yFamily_pack` is the packaged statement: with the explicit witness
  `Y i := SemiPf.pad (Nat.add_le_add_left (hm i) n) (X i)` the three conjuncts are exactly
  `pad_proj` (projection), `semipf_deg_pad_le` (degree) and the format arithmetic
  `(n+M) + (X i).r = (n+m i) + (X i).r + (M - m i) ≤ F' + M`.

  Callers will take `M` to be a bound for all the fibre dimensions — e.g. `M := F'`, which is
  legitimate because `(X i).fmt ≤ F'` gives `m i ≤ F'` — so that the packaged format bound
  `F' + M = 2 F'` remains a function of the outer format bound `F` alone.
-/
import Mathlib
import Submission.Work.WilE7.Defs
import Submission.Work.WilE7.pad_proj
import Submission.Work.WilE7.pad_deg

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7

open WilkiesDesign WilkiesDesign.E

/-- **Packaging a family of candidate sets into a single `Y`-family.**  Given candidates
`X i : SemiPf (n + m i)` with a common format bound `F'` and a common dimension bound `M` on their
fibre dimensions, there is a family `Y : Fin ι → SemiPf (n + M)` with the *same base projections*
and controlled format/degree. -/
theorem yFamily_pack {n M : ℕ} {ι : ℕ} (m : Fin ι → ℕ) (hm : ∀ i, m i ≤ M)
    (X : (i : Fin ι) → WilkiesDesign.E.SemiPf (n + m i)) (F' : ℕ)
    (hfmt : ∀ i, (X i).fmt ≤ F') :
    ∃ Y : Fin ι → WilkiesDesign.E.SemiPf (n + M),
      (∀ i, (Y i).fmt ≤ F' + M ∧ (Y i).deg ≤ (X i).deg ∧
        WilkiesDesign.E.projFirst n M '' (Y i).set =
          WilkiesDesign.E.projFirst n (m i) '' (X i).set) := by
  refine ⟨fun i => Work.WilE7.SemiPf.pad (Nat.add_le_add_left (hm i) n) (X i), ?_⟩
  intro i
  refine ⟨?_, ?_, pad_proj (hm i) (X i)⟩
  · -- format: padding only raises the ambient dimension; `(X i).fmt ≤ F'` and `m i ≤ M`
    have h1 : (Work.WilE7.SemiPf.pad (Nat.add_le_add_left (hm i) n) (X i)).fmt
        = (n + M) + (X i).r := rfl
    have h3 : (X i).fmt = (n + m i) + (X i).r := rfl
    have h4 : (n + m i) + (X i).r ≤ F' := by rw [← h3]; exact hfmt i
    have h6 : n + (X i).r ≤ (n + m i) + (X i).r :=
      Nat.add_le_add_right (Nat.le_add_right n (m i)) (X i).r
    have h7 : n + (X i).r ≤ F' := le_trans h6 h4
    rw [h1, Nat.add_right_comm]
    exact Nat.add_le_add_right h7 M
  · exact semipf_deg_pad_le _ (X i)

end Work.WilE7
