import Mathlib
import Submission.Work.WilE7.coreLT_succ.gcase_strata
import Submission.Work.WilE7.MainDesignDefs

namespace Work.WilE7.Endgame

theorem gcase_strata_uniform
    (hE5 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ),
      ∀ (p q : ℕ) (X : WilkiesDesign.E.SemiPf (p + q)), X.fmt ≤ F →
        ∃ L : List (WilkiesDesign.E.Stratum p q), L.length ≤ b.eval X.deg ∧
          (∀ S ∈ L, S.X.fmt ≤ a ∧ S.deg ≤ b.eval X.deg ∧ S.Good) ∧
          X.set = (⋃ S ∈ L, S.X.set) ∧
          L.Pairwise (fun S T => Disjoint S.X.set T.X.set))
    (F : ℕ) :
    ∃ (A : ℕ) (B : Polynomial ℕ),
      ∀ (n m D : ℕ) (T : WilkiesDesign.E.Stratum 0 (n + (m + 1))),
        T.Good → T.X.fmt ≤ F → T.deg ≤ D →
        ∃ Ld : List (WilkiesDesign.E.Stratum 0 (n + (m + 1))),
          (∀ S ∈ Ld, S.Good) ∧
          (∀ S ∈ Ld, S.X.fmt ≤ A ∧ S.deg ≤ B.eval D) ∧
          Ld.length ≤ B.eval D ∧
          (∀ S ∈ Ld, S.X.set ⊆ {z | z ∈ T.X.set ∧
            Work.WilE7.MainDesign.projRank T z = n + (m + 1) - T.j}) ∧
          (∀ S ∈ Ld, ∀ z ∈ S.X.set,
            Work.WilE7.MainDesign.projRank S z = n + (m + 1) - S.j) ∧
          {z | z ∈ T.X.set ∧ Work.WilE7.MainDesign.projRank T z = n + (m + 1) - T.j}
            = ⋃ S ∈ Ld, S.X.set := by
  -- The rank-`(n + (m + 1) - T.j)` slice of `T` is semi-Pfaffian with format/degree bounds
  -- depending only on `F` (resp. polynomially on `T.deg`).
  obtain ⟨A₀, B₀, hRS⟩ := Work.CoreStep.rankSlice_projRank F
  -- Stratify any semi-Pfaffian set of format `≤ max F A₀` (E5), with bounds depending only on `F`.
  obtain ⟨a, b, hE5'⟩ := hE5 (max F A₀)
  refine ⟨a, b.comp B₀, ?_⟩
  intro n m D T hT hF hD
  obtain ⟨Y, hYset, hYfmt, hYdeg⟩ := hRS n (m + 1) (n + (m + 1) - T.j) T hF
  obtain ⟨L, hLlen, hLprops, hLcov, hLdisj⟩ :=
    hE5' 0 (n + (m + 1)) Y (le_trans hYfmt (le_max_right F A₀))
  -- Rewrite the slice description in terms of `projRank`.
  have hYset' : Y.set = {z | z ∈ T.X.set ∧
      Work.WilE7.MainDesign.projRank T z = n + (m + 1) - T.j} := by
    rw [hYset]
    ext z
    simp only [Set.mem_ofPred_eq, Work.WilE7.MainDesign.projRank]
  have hSY : ∀ S ∈ L, S.X.set ⊆ Y.set := fun S hS x hx => by
    rw [hLcov]
    exact Set.mem_iUnion₂.mpr ⟨S, hS, hx⟩
  have hrankT : ∀ S ∈ L, ∀ z ∈ S.X.set,
      Work.WilE7.MainDesign.projRank T z = n + (m + 1) - T.j :=
    fun S hS z hz => by
      have h1 := hSY S hS hz
      rw [hYset'] at h1
      exact h1.2
  have hsubsetT : ∀ S ∈ L, S.X.set ⊆ T.X.set := fun S hS z hz => by
      have h1 := hSY S hS hz
      rw [hYset'] at h1
      exact h1.1
  refine ⟨L, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro S hS
    exact (hLprops S hS).2.2
  · intro S hS
    refine ⟨(hLprops S hS).1, ?_⟩
    calc S.deg ≤ b.eval Y.deg := (hLprops S hS).2.1
      _ ≤ b.eval (B₀.eval T.deg) := Work.WilE7.coreLT_succ.eval_mono_nat b hYdeg
      _ ≤ b.eval (B₀.eval D) :=
          Work.WilE7.coreLT_succ.eval_mono_nat b
            (Work.WilE7.coreLT_succ.eval_mono_nat B₀ hD)
      _ = (b.comp B₀).eval D := by rw [Polynomial.eval_comp]
  · calc L.length ≤ b.eval Y.deg := hLlen
      _ ≤ b.eval (B₀.eval T.deg) := Work.WilE7.coreLT_succ.eval_mono_nat b hYdeg
      _ ≤ b.eval (B₀.eval D) :=
          Work.WilE7.coreLT_succ.eval_mono_nat b
            (Work.WilE7.coreLT_succ.eval_mono_nat B₀ hD)
      _ = (b.comp B₀).eval D := by rw [Polynomial.eval_comp]
  · intro S hS z hz
    have h1 := hSY S hS hz
    rw [hYset'] at h1
    exact h1
  · intro S hS z hz
    -- The rank identity is inherited from `T` on the rank locus.
    exact Work.WilE7.coreLT_succ.projRank_eq_dim_of_sub_rankLocus S T (hLprops S hS).2.2 hT
      (hsubsetT S hS) (hrankT S hS) z hz
  · rw [← hLcov]
    exact hYset'.symm

end Work.WilE7.Endgame
