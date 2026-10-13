import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.coreLT_succ.SubStratum
import Submission.Work.WilE7.CoreStep.FibreEndDefs
import Submission.Work.WilE7.CoreStep.ProjTopDefs
import Submission.Work.CoreStep.rankSlice_projRank

namespace Work.WilE7.coreLT_succ

open WilkiesConjecture WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign

/-- A univariate polynomial with coefficients in `ℕ` is monotone for `Polynomial.eval`. -/
theorem eval_mono_nat (q : Polynomial ℕ) : Monotone (fun x => Polynomial.eval x q) := by
  intro x y hxy
  change q.eval x ≤ q.eval y
  rw [Polynomial.eval_eq_sum_range x, Polynomial.eval_eq_sum_range y]
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hxy i)

theorem gcase_strata {n m : ℕ}
    (hE5 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ),
      ∀ (p q : ℕ) (X : WilkiesDesign.E.SemiPf (p + q)), X.fmt ≤ F →
        ∃ L : List (WilkiesDesign.E.Stratum p q), L.length ≤ b.eval X.deg ∧
          (∀ S ∈ L, S.X.fmt ≤ a ∧ S.deg ≤ b.eval X.deg ∧ S.Good) ∧
          X.set = (⋃ S ∈ L, S.X.set) ∧
          L.Pairwise (fun S T => Disjoint S.X.set T.X.set))
    (F : ℕ) (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (hT : WilkiesDesign.E.Stratum.Good T) (hF : T.X.fmt ≤ F) :
    ∃ (A : ℕ) (B : Polynomial ℕ) (Ld : List (WilkiesDesign.E.Stratum 0 (n + (m + 1)))),
      (∀ S ∈ Ld, S.Good) ∧
      (∀ S ∈ Ld, S.X.fmt ≤ A ∧ S.deg ≤ B.eval T.deg) ∧
      Ld.length ≤ B.eval T.deg ∧
      (∀ S ∈ Ld, S.X.set ⊆ {z | z ∈ T.X.set ∧
        Work.WilE7.MainDesign.projRank T z = n + (m + 1) - T.j}) ∧
      (∀ S ∈ Ld, ∀ z ∈ S.X.set,
        Work.WilE7.MainDesign.projRank S z = n + (m + 1) - S.j) ∧
      {z | z ∈ T.X.set ∧ Work.WilE7.MainDesign.projRank T z = n + (m + 1) - T.j}
        = ⋃ S ∈ Ld, S.X.set := by
  -- The rank-`(n + (m + 1) - T.j)` slice of `T` is semi-Pfaffian of bounded format and degree.
  obtain ⟨A₀, B₀, hRS⟩ := Work.CoreStep.rankSlice_projRank F
  obtain ⟨Y, hYset, hYfmt, hYdeg⟩ := hRS n (m + 1) (n + (m + 1) - T.j) T hF
  -- Stratify it (E5), with a format bound large enough to cover `Y`.
  obtain ⟨a, b, hE5'⟩ := hE5 (max F A₀)
  obtain ⟨L, hLlen, hLprops, hLcov, hLdisj⟩ :=
    hE5' 0 (n + (m + 1)) Y (le_trans hYfmt (le_max_right F A₀))
  -- Rewrite the slice description in terms of `projRank`.
  have hYset' : Y.set = {z | z ∈ T.X.set ∧ projRank T z = n + (m + 1) - T.j} := by
    rw [hYset]
    ext z
    simp only [Set.mem_ofPred_eq, projRank]
  have hSY : ∀ S ∈ L, S.X.set ⊆ Y.set := fun S hS x hx => by
    rw [hLcov]
    exact Set.mem_iUnion₂.mpr ⟨S, hS, hx⟩
  have hrankT : ∀ S ∈ L, ∀ z ∈ S.X.set, projRank T z = n + (m + 1) - T.j :=
    fun S hS z hz => by
      have h1 := hSY S hS hz
      rw [hYset'] at h1
      exact h1.2
  have hsubsetT : ∀ S ∈ L, S.X.set ⊆ T.X.set := fun S hS z hz => by
      have h1 := hSY S hS hz
      rw [hYset'] at h1
      exact h1.1
  refine ⟨a, b.comp B₀, L, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro S hS
    exact (hLprops S hS).2.2
  · intro S hS
    refine ⟨(hLprops S hS).1, ?_⟩
    calc S.deg ≤ b.eval Y.deg := (hLprops S hS).2.1
      _ ≤ b.eval (B₀.eval T.deg) := eval_mono_nat b hYdeg
      _ = (b.comp B₀).eval T.deg := by rw [Polynomial.eval_comp]
  · calc L.length ≤ b.eval Y.deg := hLlen
      _ ≤ b.eval (B₀.eval T.deg) := eval_mono_nat b hYdeg
      _ = (b.comp B₀).eval T.deg := by rw [Polynomial.eval_comp]
  · intro S hS z hz
    have h1 := hSY S hS hz
    rw [hYset'] at h1
    exact h1
  · intro S hS z hz
    -- `hrank` is inherited from `T` on the rank locus.
    exact projRank_eq_dim_of_sub_rankLocus S T (hLprops S hS).2.2 hT (hsubsetT S hS)
      (hrankT S hS) z hz
  · rw [← hLcov]
    exact hYset'.symm

end Work.WilE7.coreLT_succ
