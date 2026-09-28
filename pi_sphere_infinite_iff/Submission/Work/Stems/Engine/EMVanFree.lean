import Submission.Work.Stems.fin_prod_ratH_vanishing
import Submission.Work.Serre.Basic

/-!
# The free part of `EMVan` in range form (area STEMS, assignment of the project lead)

`EMVan(k)` asks that `H̃_i(K(A,k);ℚ) = 0` for `k < i ≤ 2k-2` (the consumer
`Work.RatHurewicz.TruncationHomologyTransfer` needs the range up to `2k-1`) for `A` finitely
generated abelian.  The free part is

    `H̃_j((K(ℤ,k))^r × T;ℚ) = 0` for `k < j ≤ 2k-1`,

with `K(ℤ^r,k)` realised as the `r`-fold product of `K(ℤ,k)` (the Künneth step) and `T` a
rationally acyclic space (the finite/torsion factor, SERRE's `Work.Serre.RangeEMVanAll`).

This file assembles the two proved ingredients

* `Work.Stems.product_ratH_vanishing` — the product step (Künneth, vanishing range only);
* `Work.Stems.fin_prod_ratH_vanishing` — the `r`-fold product (`ℤ^r`), with its connectivity
  lemmas `Work.Stems.conn_prod`, `Work.Stems.conn_fin_prod`,

into the statement in the shape the EM-space dictionary of RATHUREWICZ's chapter needs.  The
remaining inputs (`C2` for `K(ℤ,k)` in the range — see `Submission/Work/Stems/EMVAN_PLAN.md` §2 for
the deficit warning — and the comparison of a range model with the genuine spaces) are *not* used
here: this file is purely about the products of the genuine models.
-/

open scoped Topology

namespace Work.Stems

noncomputable section

/-- **The free part of `EMVan` in range form.**  Let `k ≥ 2`.  If

* `Z` is `(k-1)`-connected with vanishing rational homology in the range `k < j ≤ 2k-1`
  (for `Z = K(ℤ,k)` this is the `C2` input of the lead's assignment), and
* `T` is `(k-1)`-connected and rationally acyclic in positive degrees
  (for `T = K(A,k)` with `A` finite this is SERRE's `Work.Serre.RangeEMVanAll`),

then the product `(Fin r → Z) × T` — the free-times-torsion model — has vanishing rational homology
in the same range, from `Work.Serre.SerreExactRangeCorrected` (SERRE's engine, consumed as a hypothesis;
the statement of `Work.StemsB.SerreExactRange` without the hypothesis `1 ≤ b` is *false*, see
`Submission/Work/Serre/StableExact.lean`). -/
theorem prod_acyclic_ratH_vanishing (k : ℕ) (hk : 2 ≤ k) (r : ℕ) {Z T : Type} [TopologicalSpace Z]
    [TopologicalSpace T] (z₀ : Z) (t₀ : T) (hZc : Work.Serre.Conn Z z₀ k)
    (hZ : ∀ j : ℕ, k < j → j ≤ 2 * k - 1 →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of Z) j))
    (hTc : Work.Serre.Conn T t₀ k)
    (hT : ∀ j : ℕ, 0 < j → CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of T) j))
    (hSerre : Work.Serre.SerreExactRangeCorrected) :
    ∀ j : ℕ, k < j → j ≤ 2 * k - 1 →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of ((Fin r → Z) × T)) j) := by
  have hZr : ∀ j : ℕ, k < j → j ≤ 2 * k - 1 →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Fin r → Z)) j) :=
    fin_prod_ratH_vanishing k hk r z₀ hZc hZ hSerre
  have hTr : ∀ j : ℕ, k < j → j ≤ 2 * k - 1 →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of T) j) :=
    fun j hj1 _ => hT j (by omega)
  have hZrc : Work.Serre.Conn (Fin r → Z) (fun _ => z₀) k := conn_fin_prod k r z₀ hZc
  exact product_ratH_vanishing k hk (fun _ => z₀) t₀ hZrc hTc hZr hTr hSerre

end

end Work.Stems
