import Mathlib
import Submission.Work.WilE7.Defs
import Submission.Work.WilE7.FiberCutDefs
import Submission.Work.WilE7.FiberCutCover
import Submission.Work.WilE7.FiberCutInputs
import Submission.Work.WilE7.cover_cut_deg
import Submission.Work.WilE7.FrontierDropFromDimDrop
import Submission.Work.WilE7.FrontierDim.dimDropCS

namespace Work.WilE7
open WilkiesDesign WilkiesDesign.E

/-- A semi-Pfaffian set in `ℝ^{n+0}` has finite fibres over `ℝ^n`: the fibre lives in the
one-point space `Fin 0 → ℝ`. -/
theorem fiber_finite_zero {n : ℕ} (X : WilkiesDesign.E.SemiPf (n + 0)) (x : Fin n → ℝ) :
    (WilkiesDesign.E.fiber X.set x).Finite :=
  (Set.finite_univ).subset (Set.subset_univ _)

/-- The `m = 0` case of fibre cutting: a single piece (`X` itself) suffices, with `a = F` and
`b = X + 1`. -/
theorem fiber_cut_zero (F : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (n : ℕ) (X : WilkiesDesign.E.SemiPf (n + 0)),
      X.fmt ≤ F →
      ∃ L : List (WilkiesDesign.E.SemiPf (n + 0)), L.length ≤ b.eval X.deg ∧
        (∀ Xh ∈ L, Xh.fmt ≤ a ∧ Xh.deg ≤ b.eval X.deg ∧
          ∀ x, (WilkiesDesign.E.fiber Xh.set x).Finite) ∧
        WilkiesDesign.E.projFirst n 0 '' X.set =
          ⋃ Xh ∈ L, WilkiesDesign.E.projFirst n 0 '' Xh.set := by
  refine ⟨F, Polynomial.X + 1, ?_⟩
  intro n X hX
  refine ⟨[X], ?_, ?_, ?_⟩
  · simp
  · intro Xh hXh
    simp only [List.mem_singleton] at hXh
    subst Xh
    exact ⟨hX, by simp, fun x => fiber_finite_zero X x⟩
  · simp

/-- **BV's Lemma 8 in list form, from the single general analytic input `DimDrop`.**

This is exactly `Work.WilE7.E7_fiber_cut_of_rankDrop` with the frontier dimension drop produced by
`Work.WilE7.frontierDrop_of_dimDrop` from `DimDrop` (rather than from the isolated statement
`FrontierRankDrop`).  It depends on no other unproved input. -/
theorem E7_fiber_cut_of_dimDrop
    (hDim : DimDrop)
    (hE2 : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : WilkiesDesign.E.SemiPf k), X.fmt ≤ F →
      ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ (↑s : Set (Fin k → ℝ)) ⊆ X.set ∧
        ∀ x ∈ X.set, ∃ y ∈ s,
          connectedComponentIn X.set x = connectedComponentIn X.set y)
    (hE5 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ) (X : WilkiesDesign.E.SemiPf (p + q)),
      X.fmt ≤ F →
      ∃ L : List (WilkiesDesign.E.Stratum p q), L.length ≤ b.eval X.deg ∧
        (∀ S ∈ L, S.X.fmt ≤ a ∧ S.deg ≤ b.eval X.deg ∧ S.Good) ∧
        X.set = (⋃ S ∈ L, S.X.set) ∧
        L.Pairwise (fun S T => Disjoint S.X.set T.X.set))
    (hE6 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ) (X : WilkiesDesign.E.SemiPf (p + q)),
      X.fmt ≤ F →
      ∃ Y Y' : WilkiesDesign.E.SemiPf (p + q), Y.fmt ≤ a ∧ Y.deg ≤ b.eval X.deg ∧ Y'.fmt ≤ a ∧
        Y'.deg ≤ b.eval X.deg ∧ Y.set = WilkiesDesign.E.fiberClosure X.set ∧
        Y'.set = WilkiesDesign.E.fiberClosure X.set \ X.set) :
    ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (n m : ℕ) (X : WilkiesDesign.E.SemiPf (n + m)),
      X.fmt ≤ F →
      ∃ L : List (WilkiesDesign.E.SemiPf (n + m)), L.length ≤ b.eval X.deg ∧
        (∀ Xh ∈ L, Xh.fmt ≤ a ∧ Xh.deg ≤ b.eval X.deg ∧
          ∀ x, (WilkiesDesign.E.fiber Xh.set x).Finite) ∧
        WilkiesDesign.E.projFirst n m '' X.set =
          ⋃ Xh ∈ L, WilkiesDesign.E.projFirst n m '' Xh.set := by
  intro F
  obtain ⟨a5, b5, h5⟩ := hE5 F
  obtain ⟨a, b, hb⟩ :=
    cover_cut_deg hE2 hE5 hE6 closureProj_proved' (frontierDrop_of_dimDrop hDim)
      critDrop_proved' critWitness_proved' (max a5 F) F
  refine ⟨a, b5 * b.comp b5 + b.comp b5, ?_⟩
  intro n m X hX
  obtain ⟨Ys, hYlen, hgood, hset, -⟩ := h5 n m X hX
  have hfmt : ∀ S ∈ Ys, S.X.fmt ≤ max a5 F := fun S hS =>
    le_trans (hgood S hS).1 (le_max_left _ _)
  have hdeg : ∀ S ∈ Ys, S.deg ≤ b5.eval X.deg := fun S hS => (hgood S hS).2.1
  have hbud : ∀ S ∈ Ys, S.j < m → m - S.j ≤ F := by
    intro S hS _
    have h1 : m ≤ X.fmt := by
      rw [WilkiesDesign.E.SemiPf.fmt]
      omega
    exact le_trans (Nat.sub_le m S.j) (le_trans h1 hX)
  obtain ⟨L, hlen, hprops, hcov, hsub⟩ :=
    hb F (max a5 F) n m Ys (b5.eval X.deg) le_rfl le_rfl
      (fun S hS => (hgood S hS).2.2) hfmt hdeg hbud
  have hbc : (b.comp b5).eval X.deg = b.eval (b5.eval X.deg) := Polynomial.eval_comp
  refine ⟨L, ?_, ?_, ?_⟩
  · -- the length bound
    have h1 : L.length ≤ b5.eval X.deg * (b.comp b5).eval X.deg := by
      rw [hbc]
      exact le_trans hlen (Nat.mul_le_mul hYlen le_rfl)
    calc L.length ≤ b5.eval X.deg * (b.comp b5).eval X.deg := h1
      _ ≤ (b5 * b.comp b5 + b.comp b5).eval X.deg := by
          rw [Polynomial.eval_add, Polynomial.eval_mul]
          exact Nat.le_add_right _ _
  · -- the format/degree/finiteness clauses
    intro Xh hXh
    obtain ⟨hf, hd, hfin⟩ := hprops Xh hXh
    refine ⟨hf, ?_, hfin⟩
    rw [← hbc] at hd
    calc Xh.deg ≤ (b.comp b5).eval X.deg := hd
      _ ≤ (b5 * b.comp b5 + b.comp b5).eval X.deg := by
          rw [Polynomial.eval_add, Polynomial.eval_mul]
          exact Nat.le_add_left _ _
  · -- the projection equality
    have hunion : WilkiesDesign.E.projFirst n m '' X.set =
        ⋃ S ∈ Ys, WilkiesDesign.E.projFirst n m '' S.X.set := by
      rw [hset]
      ext x
      simp only [Set.mem_image, Set.mem_iUnion]
      constructor
      · rintro ⟨z, ⟨S, hS, hzS⟩, rfl⟩
        exact ⟨S, hS, z, hzS, rfl⟩
      · rintro ⟨S, hS, z, hzS, rfl⟩
        exact ⟨z, ⟨S, hS, hzS⟩, rfl⟩
    refine Set.Subset.antisymm ?_ ?_
    · rw [hunion]
      exact hcov
    · intro x hx
      have h1 : x ∈ ⋃ S ∈ Ys, WilkiesDesign.E.projFirst n m ''
          (WilkiesDesign.E.fiberClosure S.X.set) := hsub hx
      simp only [Set.mem_iUnion] at h1
      obtain ⟨S, hS, hxS⟩ := h1
      rw [closureProj_proved' n m S.X.set] at hxS
      rw [hunion]
      simp only [Set.mem_iUnion]
      exact ⟨S, hS, hxS⟩

/-- **The target modulo the single general analytic input `Work.WilE7.DimDrop`.**

This is `E7_fiber_cut_proved` with the classical dimension drop for analytic level sets made
explicit as a hypothesis.  Everything else — BV's induction on the fibre dimension, the worklist
recursion, the format/degree/length bookkeeping, the critical-point input, the closure trick and
the frontier bookkeeping — is machinery already proved in the workspace; the frontier dimension
drop is the only geometric input that is not, and `Work.WilE7.frontierDrop_of_dimDrop` reduces it
to `DimDrop`. -/
theorem E7_fiber_cut_proved_of_dimDrop
    (hDim : DimDrop)
    (hE2 : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : WilkiesDesign.E.SemiPf k), X.fmt ≤ F →
      ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ (↑s : Set (Fin k → ℝ)) ⊆ X.set ∧
        ∀ x ∈ X.set, ∃ y ∈ s,
          connectedComponentIn X.set x = connectedComponentIn X.set y)
    (hE5 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ) (X : WilkiesDesign.E.SemiPf (p + q)),
      X.fmt ≤ F →
      ∃ L : List (WilkiesDesign.E.Stratum p q), L.length ≤ b.eval X.deg ∧
        (∀ S ∈ L, S.X.fmt ≤ a ∧ S.deg ≤ b.eval X.deg ∧ S.Good) ∧
        X.set = (⋃ S ∈ L, S.X.set) ∧
        L.Pairwise (fun S T => Disjoint S.X.set T.X.set))
    (hE6 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ) (X : WilkiesDesign.E.SemiPf (p + q)),
      X.fmt ≤ F →
      ∃ Y Y' : WilkiesDesign.E.SemiPf (p + q), Y.fmt ≤ a ∧ Y.deg ≤ b.eval X.deg ∧ Y'.fmt ≤ a ∧
        Y'.deg ≤ b.eval X.deg ∧ Y.set = WilkiesDesign.E.fiberClosure X.set ∧
        Y'.set = WilkiesDesign.E.fiberClosure X.set \ X.set) :
    ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (n m : ℕ) (X : WilkiesDesign.E.SemiPf (n + m)),
      X.fmt ≤ F →
      ∃ L : List (WilkiesDesign.E.SemiPf (n + m)), L.length ≤ b.eval X.deg ∧
        (∀ Xh ∈ L, Xh.fmt ≤ a ∧ Xh.deg ≤ b.eval X.deg ∧
          ∀ x, (WilkiesDesign.E.fiber Xh.set x).Finite) ∧
        WilkiesDesign.E.projFirst n m '' X.set =
          ⋃ Xh ∈ L, WilkiesDesign.E.projFirst n m '' Xh.set :=
  E7_fiber_cut_of_dimDrop hDim hE2 hE5 hE6

theorem E7_fiber_cut_proved
    (hE2 : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : WilkiesDesign.E.SemiPf k), X.fmt ≤ F →
      ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ (↑s : Set (Fin k → ℝ)) ⊆ X.set ∧
        ∀ x ∈ X.set, ∃ y ∈ s,
          connectedComponentIn X.set x = connectedComponentIn X.set y)
    (hE5 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ) (X : WilkiesDesign.E.SemiPf (p + q)),
      X.fmt ≤ F →
      ∃ L : List (WilkiesDesign.E.Stratum p q), L.length ≤ b.eval X.deg ∧
        (∀ S ∈ L, S.X.fmt ≤ a ∧ S.deg ≤ b.eval X.deg ∧ S.Good) ∧
        X.set = (⋃ S ∈ L, S.X.set) ∧
        L.Pairwise (fun S T => Disjoint S.X.set T.X.set))
    (hE6 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ) (X : WilkiesDesign.E.SemiPf (p + q)),
      X.fmt ≤ F →
      ∃ Y Y' : WilkiesDesign.E.SemiPf (p + q), Y.fmt ≤ a ∧ Y.deg ≤ b.eval X.deg ∧ Y'.fmt ≤ a ∧
        Y'.deg ≤ b.eval X.deg ∧ Y.set = WilkiesDesign.E.fiberClosure X.set ∧
        Y'.set = WilkiesDesign.E.fiberClosure X.set \ X.set) :
    ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (n m : ℕ) (X : WilkiesDesign.E.SemiPf (n + m)),
      X.fmt ≤ F →
      ∃ L : List (WilkiesDesign.E.SemiPf (n + m)), L.length ≤ b.eval X.deg ∧
        (∀ Xh ∈ L, Xh.fmt ≤ a ∧ Xh.deg ≤ b.eval X.deg ∧
          ∀ x, (WilkiesDesign.E.fiber Xh.set x).Finite) ∧
        WilkiesDesign.E.projFirst n m '' X.set =
          ⋃ Xh ∈ L, WilkiesDesign.E.projFirst n m '' Xh.set := by
  -- The classical frontier dimension drop for real analytic level sets, proved by the CS-slice
  -- route from analytic curve selection (`Work.WilE7.FrontierDim.dimDropCS`, clean axioms, no
  -- import cycle with this file), which is exactly the body of `Work.WilE7.DimDrop`.
  exact E7_fiber_cut_proved_of_dimDrop Work.WilE7.FrontierDim.dimDropCS hE2 hE5 hE6

end Work.WilE7
