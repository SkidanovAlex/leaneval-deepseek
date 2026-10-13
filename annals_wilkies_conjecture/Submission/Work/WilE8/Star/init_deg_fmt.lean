/-
  WilE8 / Star — the format and degree of the `init`-projection of a `*`-piece.

  `Work.WilE7.StarPiece.init P` reindexes the semi-Pfaffian data of `P` along the
  value-preserving identification `(N+1)+m = N+(m+1)` of coordinates (`finEquiv`), so:

  * the *format* changes by the arity only (the chain length `r` is untouched), and the two
    numeral expressions `N + (m+1)` and `(N+1) + m` agree by `omega`;
  * the *degree* is literally unchanged, because reindexing is `MvPolynomial.rename` along a
    bijection of the variables, and total degree is preserved by renamings along injective
    maps (`Work.WilE8.Extend.totalDegree_rename_of_injective`).

  The degree computation is the `reindex`-analogue of `Work.WilE8.Extend.semipf_deg_extend`.
-/
import Mathlib
import Submission.Work.WilE7.Defs
import Submission.Work.WilE8.Extend.semipf_deg_extend

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE8.Star

open WilkiesDesign WilkiesDesign.E

/-! ## Reindexing does not change the degree -/

/-- Reindexing an `EA`-polynomial along a bijection of the coordinates does not change its atom
degree.  `Work.WilE7.EAPoly.reindex` is by definition `MvPolynomial.rename` along the injective
variable map `Sum.map e id`. -/
theorem atomDeg_reindex {k K r : ℕ} (e : Fin k ≃ Fin K) (Q : EAPoly k r) :
    atomDeg (Work.WilE7.EAPoly.reindex e Q) = atomDeg Q :=
  Work.WilE8.Extend.atomDeg_extend e.injective Q

/-- Reindexing a basic set along a bijection of the coordinates does not change its degree. -/
theorem basic_deg_reindex {k K r : ℕ} (e : Fin k ≃ Fin K) (B : Basic k r) :
    (Work.WilE7.Basic.reindex e B).deg = B.deg :=
  Work.WilE8.Extend.basic_deg_extend e.injective B

/-- Reindexing a semi-Pfaffian set along a bijection of the coordinates does not change its
degree.  (The format *does* change: it is `k + X.r` in the target arity.) -/
theorem semipf_deg_reindex {k K : ℕ} (e : Fin k ≃ Fin K) (X : SemiPf k) :
    (Work.WilE7.SemiPf.reindex e X).deg = X.deg :=
  Work.WilE8.Extend.semipf_deg_extend e.injective X

/-- The format of a reindexed semi-Pfaffian set, in the target arity `K`. -/
theorem semipf_fmt_reindex {k K : ℕ} (e : Fin k ≃ Fin K) (X : SemiPf k) :
    (Work.WilE7.SemiPf.reindex e X).fmt = K + X.r := rfl

/-! ## The target -/

theorem init_deg_fmt {N : ℕ} (P : WilkiesDesign.E.StarPiece (N + 1)) :
    (Work.WilE7.StarPiece.init P).X.fmt = P.X.fmt ∧
    (Work.WilE7.StarPiece.init P).X.deg = P.X.deg := by
  have hfmt : (Work.WilE7.StarPiece.init P).X.fmt = N + (P.m + 1) + P.X.r := rfl
  have hfmtP : P.X.fmt = (N + 1) + P.m + P.X.r := rfl
  refine ⟨?_, ?_⟩
  · rw [hfmt, hfmtP]
    omega
  · exact semipf_deg_reindex _ P.X

end Work.WilE8.Star
