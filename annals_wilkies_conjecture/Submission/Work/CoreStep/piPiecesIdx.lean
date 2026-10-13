import Mathlib
import Submission.Work.WilE7.CoreStep.piFamilyTopSingle
import Submission.Work.WilE7.MainDesignDefs

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.CoreStep

open WilkiesDesign WilkiesDesign.E

/-!
  `Work.CoreStep.piPiecesIdx`: the **indexed** form of `Work.CoreStep.piFamilyTopSingle`.

  `piFamilyTopSingle` produces, for a *single* semi-Pfaffian set `X : SemiPf ((n+1)+m)` of format
  `≤ F` and degree `≤ D`, a list `Pi` of absolute `Good` strata with the exact coverage
  `π_{n+1}(X) = ⋃ T ∈ Pi, π_{n+1}(absSet T)`, together with format/degree/finite-fibre/rank bounds
  and the inclusion `π_{n+1}(absSet T) ⊆ π_{n+1}(X)` for every `T ∈ Pi`.

  The `CoreLT_succ` assembly needs this for a *family* `X : Fin k → SemiPf ((n+1)+m)`, with a
  single collected list `Pi : List (Fin k × Stratum 0 ((n+1)+m))` in which each piece carries its
  provenance `i : Fin k`, such that the pieces of provenance `i` cover *exactly* `π_{n+1}(X i)`.

  The construction is the obvious one: apply `piFamilyTopSingle` to each member `X i`, obtaining
  the sub-list `L i`, and concatenate the tagged lists `(L i).map (fun T => (i, T))`.  The size
  bound is `k * eval ![D,1] N₁`, realised by the polynomial `X 1 * N₁` (`eval_X_one_mul`), using
  the monotonicity of `ℕ`-valued polynomial evaluation in the second variable (`poly_bound`).
-/

/-- Evaluating the bivariate monomial `X 1 * N₁` at `![D,k]` multiplies `N₁`'s value by `k`. -/
private lemma eval_X_one_mul (N1 : MvPolynomial (Fin 2) ℕ) (D k : ℕ) :
    MvPolynomial.eval ![D, k] (MvPolynomial.X (1 : Fin 2) * N1)
      = k * MvPolynomial.eval ![D, k] N1 := by
  rw [map_mul, MvPolynomial.eval_X]
  simp

/-- `k * N₁(D,1) ≤ k * N₁(D,k)`: monotonicity of the `ℕ`-valued evaluation in the second variable
(`poly_bound`), together with the trivial case `k = 0`. -/
private lemma mul_eval_one_le (N1 : MvPolynomial (Fin 2) ℕ) (D k : ℕ) :
    k * N1.eval ![D, 1] ≤ k * N1.eval ![D, k] := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp
  · exact Nat.mul_le_mul_left _ ((Work.WilE7.poly_bound N1).2.2.2 D 1 k hk)

theorem piPiecesIdx
    (hFC : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ),
      ∀ (n m : ℕ) (X : WilkiesDesign.E.SemiPf (n + m)), X.fmt ≤ F →
        ∃ L : List (WilkiesDesign.E.SemiPf (n + m)), L.length ≤ b.eval X.deg ∧
          (∀ Xh ∈ L, Xh.fmt ≤ a ∧ Xh.deg ≤ b.eval X.deg ∧
            ∀ x, (WilkiesDesign.E.fiber Xh.set x).Finite) ∧
          WilkiesDesign.E.projFirst n m '' X.set =
            ⋃ Xh ∈ L, WilkiesDesign.E.projFirst n m '' Xh.set)
    (hE5 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ),
      ∀ (p q : ℕ) (X : WilkiesDesign.E.SemiPf (p + q)), X.fmt ≤ F →
        ∃ L : List (WilkiesDesign.E.Stratum p q), L.length ≤ b.eval X.deg ∧
          (∀ S ∈ L, S.X.fmt ≤ a ∧ S.deg ≤ b.eval X.deg ∧ S.Good) ∧
          X.set = (⋃ S ∈ L, S.X.set) ∧
          L.Pairwise (fun S T => Disjoint S.X.set T.X.set))
    (F : ℕ) :
    ∃ (A : ℕ) (B : Polynomial ℕ) (N : MvPolynomial (Fin 2) ℕ),
      ∀ (D k n m : ℕ) (X : Fin k → WilkiesDesign.E.SemiPf ((n + 1) + m)),
        (∀ i, (X i).fmt ≤ F ∧ (X i).deg ≤ D) →
        ∃ Pi : List (Fin k × WilkiesDesign.E.Stratum 0 ((n + 1) + m)),
          Pi.length ≤ MvPolynomial.eval ![D, k] N ∧
          (∀ p ∈ Pi, (p.2).Good ∧ (p.2).X.fmt ≤ A ∧ (p.2).deg ≤ B.eval D ∧
            (∀ x : Fin (n + 1) → ℝ,
              (WilkiesDesign.E.fiber (Work.WilE7.MainDesign.absSet p.2) x).Finite) ∧
            (∀ z ∈ (p.2).X.set,
              Work.WilE7.MainDesign.projRank p.2 z = (n + 1) + m - (p.2).j) ∧
            WilkiesDesign.E.projFirst (n + 1) m '' (Work.WilE7.MainDesign.absSet p.2) ⊆
              WilkiesDesign.E.projFirst (n + 1) m '' (X p.1).set) ∧
          (∀ i : Fin k, WilkiesDesign.E.projFirst (n + 1) m '' (X i).set =
            ⋃ p ∈ Pi.filter (fun p => p.1 = i),
              WilkiesDesign.E.projFirst (n + 1) m '' (Work.WilE7.MainDesign.absSet p.2)) := by
  classical
  obtain ⟨A1, B1, N1, hN1⟩ := piFamilyTopSingle hFC hE5 F
  refine ⟨A1, B1, MvPolynomial.X (1 : Fin 2) * N1, ?_⟩
  intro D k n m X hX
  -- per-index sub-lists from the single-set statement
  choose L hLlen hLmem hLcov using fun i : Fin k =>
    hN1 D n m (X i) (hX i).1 (hX i).2
  -- tag each sub-list with its index and concatenate
  let Pi : List (Fin k × WilkiesDesign.E.Stratum 0 ((n + 1) + m)) :=
    (List.finRange k).flatMap (fun i => (L i).map (fun T => (i, T)))
  have mem_Pi : ∀ p : Fin k × WilkiesDesign.E.Stratum 0 ((n + 1) + m),
      p ∈ Pi ↔ ∃ i : Fin k, ∃ T ∈ L i, (i, T) = p := by
    intro p
    simp only [Pi, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map]
  refine ⟨Pi, ?_, ?_, ?_⟩
  · -- the size bound `|Π| ≤ k * N₁(D,1) ≤ eval ![D,k] (X 1 * N₁)`
    rw [eval_X_one_mul]
    have h1 : Pi.length ≤ k * N1.eval ![D, 1] := by
      have h := Work.WilE7.CoreStep.length_flatMap_le_mul (List.finRange k)
        (fun i : Fin k => (L i).map (fun T => (i, T))) (N1.eval ![D, 1])
        (fun i _ => by rw [List.length_map]; exact hLlen i)
      simpa only [Pi, List.length_finRange] using h
    exact le_trans h1 (mul_eval_one_le N1 D k)
  · -- the per-piece properties are those of the sub-list of the corresponding index
    intro p hp
    obtain ⟨i, T, hT, rfl⟩ := (mem_Pi p).mp hp
    exact hLmem i T hT
  · -- exact per-index coverage
    intro i
    rw [hLcov i]
    apply Set.Subset.antisymm
    · intro y hy
      obtain ⟨T, hT, hyT⟩ := Set.mem_iUnion₂.mp hy
      refine Set.mem_iUnion₂.mpr ⟨(i, T), ?_, hyT⟩
      rw [List.mem_filter]
      exact ⟨(mem_Pi _).mpr ⟨i, T, hT, rfl⟩, by simp⟩
    · intro y hy
      obtain ⟨p, hp, hyp⟩ := Set.mem_iUnion₂.mp hy
      rw [List.mem_filter] at hp
      obtain ⟨hpPi, hp1⟩ := hp
      obtain ⟨j, T, hT, rfl⟩ := (mem_Pi p).mp hpPi
      have hji : j = i := by simpa using hp1
      subst hji
      exact Set.mem_iUnion₂.mpr ⟨T, hT, hyp⟩

end Work.CoreStep
