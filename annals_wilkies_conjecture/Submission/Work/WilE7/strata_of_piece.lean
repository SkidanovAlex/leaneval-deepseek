/-
  Area E7: the stratum step of the level induction (`NOTES_S26_level_step.md` §4.3).

  Given the fibrewise weak stratification `E5_strat` (as the hypothesis `hE5`, whose statement is
  literally that of `WilkiesDesign.E.E5_strat`), every semi-Pfaffian piece `P : SemiPf (n + (M+1))`
  with **finite fibres** over `ℝⁿ` (and format `≤ F`, degree `≤ D`) can be written, at the cost of a
  bound depending only on `F`, as a **pairwise disjoint** union of `Good` strata `S` which

  * have `S.j = M + 1` (so that the fibrewise Jacobian of `S.h` has as many rows as the fibre has
    coordinates: `strat_j_of_finite`),
  * still have finite fibres, and
  * are nonempty (so that `strat_j_of_finite` applies at all, and so that the sheets of the level
    step have a point to start from).

  The proof is bookkeeping: `hE5` at `(p, q) = (n, M + 1)` covers `P.set` by `L.length ≤ b.eval P.deg`
  pairwise disjoint `Good` strata; every member `S ∈ L` of the list satisfies `S.X.set ⊆ P.set`, so
  its fibres are finite (a subset of a finite fibre); passing to the *nonempty* members `T ⊆ L`
  (dropping the empty ones changes neither the union nor disjointness) every member has `S.j = M+1`
  by `strat_j_of_finite`, and all the bounds are monotone in the degree because the polynomials have
  natural-number coefficients.
-/
import Mathlib
import Submission.Work.WilE7.strat_j_of_finite

set_option autoImplicit false
noncomputable section
namespace Work.WilE7

open WilkiesDesign WilkiesDesign.E

/-! ## Two elementary tools -/

/-- `Polynomial.eval` is monotone at natural arguments when the coefficients are natural numbers. -/
theorem poly_eval_mono_nat (p : Polynomial ℕ) {n m : ℕ} (h : n ≤ m) : p.eval n ≤ p.eval m := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  exact Finset.sum_le_sum fun k _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h k)

/-- The sublist of `L` of the strata whose underlying set is nonempty.  The `DecidablePred`
instance is pinned to `Classical.propDecidable`, exactly as in `Work.WilE7.cellsOutside`, so that
uses of this definition never depend on instance synthesis. -/
def strataNonempty {n q : ℕ} (L : List (WilkiesDesign.E.Stratum n q)) :
    List (WilkiesDesign.E.Stratum n q) :=
  @List.filter (WilkiesDesign.E.Stratum n q)
    (fun S => @decide (S.X.set.Nonempty) (Classical.propDecidable _)) L

theorem mem_strataNonempty {n q : ℕ} {L : List (WilkiesDesign.E.Stratum n q)}
    {S : WilkiesDesign.E.Stratum n q} :
    S ∈ strataNonempty L ↔ S ∈ L ∧ S.X.set.Nonempty := by
  simp only [strataNonempty, List.mem_filter, decide_eq_true_eq]

theorem length_strataNonempty_le {n q : ℕ} (L : List (WilkiesDesign.E.Stratum n q)) :
    (strataNonempty L).length ≤ L.length :=
  @List.length_filter_le (WilkiesDesign.E.Stratum n q)
    (fun S => @decide (S.X.set.Nonempty) (Classical.propDecidable _)) L

theorem pairwise_strataNonempty {n q : ℕ} {L : List (WilkiesDesign.E.Stratum n q)}
    (h : L.Pairwise (fun S S' => Disjoint S.X.set S'.X.set)) :
    (strataNonempty L).Pairwise (fun S S' => Disjoint S.X.set S'.X.set) :=
  h.sublist (@List.filter_sublist (WilkiesDesign.E.Stratum n q)
    (fun S => @decide (S.X.set.Nonempty) (Classical.propDecidable _)) L)

/-! ## The stratum step -/

theorem strata_of_piece
    (hE5 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ) (X : WilkiesDesign.E.SemiPf (p + q)),
      X.fmt ≤ F →
      ∃ L : List (WilkiesDesign.E.Stratum p q), L.length ≤ b.eval X.deg ∧
        (∀ S ∈ L, S.X.fmt ≤ a ∧ S.deg ≤ b.eval X.deg ∧ S.Good) ∧
        X.set = (⋃ S ∈ L, S.X.set) ∧
        L.Pairwise (fun S S' => Disjoint S.X.set S'.X.set))
    (F : ℕ) :
    ∃ (A : ℕ) (B : Polynomial ℕ),
      ∀ (D n M : ℕ) (P : WilkiesDesign.E.SemiPf (n + (M + 1))), P.fmt ≤ F → P.deg ≤ D →
      (∀ x : Fin n → ℝ, (WilkiesDesign.E.fiber P.set x).Finite) →
      ∃ (T : List (WilkiesDesign.E.Stratum n (M + 1))),
        T.length ≤ B.eval D ∧
        (∀ S ∈ T, S.X.fmt ≤ A ∧ S.deg ≤ B.eval D ∧ S.Good ∧ S.j = M + 1 ∧
          (∀ x : Fin n → ℝ, (WilkiesDesign.E.fiber S.X.set x).Finite) ∧ S.X.set.Nonempty) ∧
        P.set = (⋃ S ∈ T, S.X.set) ∧
        T.Pairwise (fun S S' => Disjoint S.X.set S'.X.set) := by
  obtain ⟨a, b, hb⟩ := hE5 F
  refine ⟨a, b, ?_⟩
  intro D n M P hfmt hdeg hfin
  obtain ⟨L, hLlen, hLmem, hLcov, hLdisj⟩ := hb n (M + 1) P hfmt
  refine ⟨strataNonempty L, ?_, ?_, ?_, ?_⟩
  · -- the length bound: filtering only shortens, and `b.eval` is monotone
    calc (strataNonempty L).length ≤ L.length := length_strataNonempty_le L
      _ ≤ b.eval P.deg := hLlen
      _ ≤ b.eval D := poly_eval_mono_nat b hdeg
  · -- every member of the filtered list is a nonempty `Good` stratum with `j = M + 1`
    intro S hS
    obtain ⟨hSL, hne⟩ := mem_strataNonempty.mp hS
    obtain ⟨hfmtS, hdegS, hgoodS⟩ := hLmem S hSL
    -- `S.X.set ⊆ P.set`, hence the fibres of `S.X.set` are finite
    have hsub : S.X.set ⊆ P.set := by
      intro z hz
      rw [hLcov]
      simp only [Set.mem_iUnion₂, exists_prop]
      exact ⟨S, hSL, hz⟩
    have hfinS : ∀ x : Fin n → ℝ, (WilkiesDesign.E.fiber S.X.set x).Finite :=
      fun x => (hfin x).subset fun y hy => hsub hy
    refine ⟨hfmtS, le_trans hdegS (poly_eval_mono_nat b hdeg), hgoodS,
      Work.WilE7.strat_j_of_finite S hgoodS hne hfinS, hfinS, hne⟩
  · -- the union is unchanged: the discarded strata are empty
    apply Set.Subset.antisymm
    · intro z hz
      have hz' : z ∈ ⋃ S ∈ L, S.X.set := hLcov ▸ hz
      simp only [Set.mem_iUnion₂, exists_prop] at hz'
      obtain ⟨S, hSL, hzS⟩ := hz'
      simp only [Set.mem_iUnion₂, exists_prop]
      exact ⟨S, mem_strataNonempty.mpr ⟨hSL, ⟨z, hzS⟩⟩, hzS⟩
    · intro z hz
      simp only [Set.mem_iUnion₂, exists_prop] at hz
      obtain ⟨S, hST, hzS⟩ := hz
      have hSL : S ∈ L := (mem_strataNonempty.mp hST).1
      rw [hLcov]
      simp only [Set.mem_iUnion₂, exists_prop]
      exact ⟨S, hSL, hzS⟩
  · -- disjointness is inherited from the larger list
    exact pairwise_strataNonempty hLdisj

end Work.WilE7
