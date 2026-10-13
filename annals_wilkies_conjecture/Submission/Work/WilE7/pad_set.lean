import Mathlib
import Submission.Work.WilE7.Defs

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-!
## The set of the padded semi-Pfaffian set

`SemiPf.pad hm X` views a semi-Pfaffian set `X ⊆ ℝ^k` as a set in `ℝ^K`, `k ≤ K`, by
declaring the extra `K - k` coordinates unconstrained (zero coefficients in the chain).  The
content of `pad_set` is that this operation is exactly the operation

* take the closed cube `[-1,1]^K`, and
* project the last `K - k` coordinates away, i.e. ask `takeZ hm y ∈ X.set`.

The proof reduces everything to the evaluation of a padded `EA`-polynomial against a padded
chain: `eaEval (EAChain.pad hm c) (EAPoly.pad hm Q) y = eaEval c Q (takeZ hm y)`.  The chain
part is a reindexing of the finite sum `∑ i : Fin K, c.a j i * y i`, whose non-zero terms are
exactly those with `i.val < k`.
-/

/-- Sums over `Fin K` of a function supported in the first `k ≤ K` coordinates, reindexed along
`Fin.castLE hm`. -/
private theorem padSet_sum {k K : ℕ} (hm : k ≤ K) (g u : Fin K → ℝ) (f : Fin k → ℝ)
    (hg : ∀ i : Fin K, k ≤ i.val → g i = 0)
    (hf : ∀ i : Fin k, g (Fin.castLE hm i) * u (Fin.castLE hm i) = f i) :
    ∑ i : Fin K, g i * u i = ∑ i : Fin k, f i := by
  have hsub : (Finset.univ.filter (fun i : Fin K => i.val < k)) ⊆ (Finset.univ : Finset (Fin K)) :=
    Finset.subset_univ _
  have hzero : ∀ x ∈ (Finset.univ : Finset (Fin K)),
      x ∉ Finset.univ.filter (fun i : Fin K => i.val < k) → (fun i => g i * u i) x = 0 := by
    intro i _ hi
    show g i * u i = 0
    have hik : k ≤ i.val := by
      by_contra h
      exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.not_le.mp h⟩)
    rw [hg i hik, zero_mul]
  rw [← Finset.sum_subset hsub hzero]
  refine Finset.sum_bij (fun (a : Fin K) (ha : a ∈ Finset.univ.filter (fun i : Fin K => i.val < k))
      => (⟨a.val, (Finset.mem_filter.mp ha).2⟩ : Fin k)) ?_ ?_ ?_ ?_
  · intro a ha; exact Finset.mem_univ _
  · intro a₁ ha₁ a₂ ha₂ heq
    exact Fin.ext (by simpa using congrArg (fun x : Fin k => x.val) heq)
  · intro b _
    refine ⟨Fin.castLE hm b, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact b.isLt
    · exact Fin.ext (Fin.val_castLE hm b)
  · intro a ha
    have ha' : a.val < k := (Finset.mem_filter.mp ha).2
    have hcast : Fin.castLE hm (⟨a.val, ha'⟩ : Fin k) = a := Fin.ext rfl
    rw [← hf ⟨a.val, ha'⟩, hcast]

/-- The coefficient of a padded chain at an interior coordinate. -/
private theorem padSet_pad_a {k K r : ℕ} (hm : k ≤ K) (c : EAChain k r) (j : Fin r) (i : Fin k) :
    (EAChain.pad hm c).a j (Fin.castLE hm i) = c.a j i := by
  show (if h : (Fin.castLE hm i).val < k then c.a j ⟨(Fin.castLE hm i).val, h⟩ else 0) = c.a j i
  have hlt : (Fin.castLE hm i).val < k := i.isLt
  rw [dite_eq_left hlt]
  congr 1

/-- `takeZ` really is the projection along `Fin.castLE`. -/
private theorem padSet_takeZ_apply {k K : ℕ} (hm : k ≤ K) (y : Fin K → ℝ) (i : Fin k) :
    takeZ hm y i = y (Fin.castLE hm i) := rfl

/-- Padding a chain does not change the affine forms, up to `takeZ`. -/
private theorem padSet_ell {k K r : ℕ} (hm : k ≤ K) (c : EAChain k r) (j : Fin r)
    (y : Fin K → ℝ) :
    (EAChain.pad hm c).ell j y = c.ell j (takeZ hm y) := by
  rw [EAChain.ell, EAChain.ell]
  congr 1
  refine padSet_sum hm (fun i => (EAChain.pad hm c).a j i) y
    (fun i => c.a j i * takeZ hm y i) ?_ ?_
  · intro i hi
    show (if h : i.val < k then c.a j ⟨i.val, h⟩ else 0) = 0
    exact dite_eq_right (not_lt.mpr hi)
  · intro i
    rw [padSet_pad_a hm c j i, padSet_takeZ_apply hm y i]

/-- Evaluation of a padded `EA`-polynomial against a padded chain. -/
private theorem padSet_eaEval {k K r : ℕ} (hm : k ≤ K) (c : EAChain k r) (Q : EAPoly k r)
    (y : Fin K → ℝ) :
    eaEval (EAChain.pad hm c) (EAPoly.pad hm Q) y = eaEval c Q (takeZ hm y) := by
  have hcomp : (Sum.elim y (fun j => Real.exp ((EAChain.pad hm c).ell j y))) ∘
        (Sum.map (Fin.castLE hm) id) =
      Sum.elim (takeZ hm y) (fun j => Real.exp (c.ell j (takeZ hm y))) := by
    funext s
    cases s with
    | inl i => rfl
    | inr j =>
      show Real.exp ((EAChain.pad hm c).ell j y) = Real.exp (c.ell j (takeZ hm y))
      rw [padSet_ell hm c j y]
  unfold eaEval
  rw [EAPoly.pad, MvPolynomial.eval_rename, hcomp]

/-- A padded basic set holds at `y` iff the original one holds at `takeZ hm y`. -/
private theorem padSet_holds {k K r : ℕ} (hm : k ≤ K) (c : EAChain k r) (B : Basic k r)
    (y : Fin K → ℝ) :
    (Basic.pad hm B).holds (EAChain.pad hm c) y ↔ B.holds c (takeZ hm y) := by
  simp only [Basic.holds, Basic.pad, List.mem_map]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun f hf => by rw [← padSet_eaEval hm c f y]; exact h1 (EAPoly.pad hm f) ⟨f, hf, rfl⟩,
      fun g hg => by rw [← padSet_eaEval hm c g y]; exact h2 (EAPoly.pad hm g) ⟨g, hg, rfl⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun b ⟨a, ha, hba⟩ => by rw [← hba, padSet_eaEval hm c a y]; exact h1 a ha,
      fun b ⟨a, ha, hba⟩ => by rw [← hba, padSet_eaEval hm c a y]; exact h2 a ha⟩

/-- The cube in `ℝ^K` projects into the cube in `ℝ^k` along `takeZ`. -/
private theorem padSet_takeZ_cube {k K : ℕ} (hm : k ≤ K) {y : Fin K → ℝ} (hy : y ∈ cubeC K) :
    takeZ hm y ∈ cubeC k := by
  intro i
  exact hy ⟨i.val, lt_of_lt_of_le i.isLt hm⟩

theorem pad_set {k K : ℕ} (hm : k ≤ K) (X : WilkiesDesign.E.SemiPf k) :
    (Work.WilE7.SemiPf.pad hm X).set = {y | y ∈ WilkiesDesign.E.cubeC K ∧
      Work.WilE7.takeZ hm y ∈ X.set} := by
  ext y
  simp only [SemiPf.set, Set.mem_ofPred_eq, SemiPf.pad]
  constructor
  · rintro ⟨hyc, B, hB, hhold⟩
    obtain ⟨B₀, hB₀, rfl⟩ := List.mem_map.mp hB
    exact ⟨hyc, padSet_takeZ_cube hm hyc, B₀, hB₀, (padSet_holds hm X.c B₀ y).mp hhold⟩
  · rintro ⟨hyc, _hcube, B₀, hB₀, hhold⟩
    exact ⟨hyc, Basic.pad hm B₀, List.mem_map.mpr ⟨B₀, hB₀, rfl⟩,
      (padSet_holds hm X.c B₀ y).mpr hhold⟩

end Work.WilE7
