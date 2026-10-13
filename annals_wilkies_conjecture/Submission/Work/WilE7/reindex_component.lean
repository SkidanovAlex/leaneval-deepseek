import Mathlib
import Submission.Work.WilE7.Defs

set_option autoImplicit false
noncomputable section

namespace Work.WilE7

open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-! ## The coordinate-permutation homeomorphism -/

/-- The homeomorphism `(Fin K → ℝ) ≃ₜ (Fin k → ℝ)` sending `y` to `fun i => y (e i)`;
its inverse is `x ↦ fun j => x (e.symm j)`. -/
def coordHomeomorph {k K : ℕ} (e : Fin k ≃ Fin K) : (Fin K → ℝ) ≃ₜ (Fin k → ℝ) where
  toEquiv :=
    { toFun := fun y => fun i => y (e i)
      invFun := fun x => fun j => x (e.symm j)
      left_inv := by intro y; funext j; simp
      right_inv := by intro x; funext i; simp }
  continuous_toFun := continuous_pi fun i => continuous_apply (e i)
  continuous_invFun := continuous_pi fun j => continuous_apply (e.symm j)

@[simp] theorem coordHomeomorph_apply {k K : ℕ} (e : Fin k ≃ Fin K) (y : Fin K → ℝ) :
    coordHomeomorph e y = fun i => y (e i) := rfl

@[simp] theorem coordHomeomorph_symm_apply {k K : ℕ} (e : Fin k ≃ Fin K) (x : Fin k → ℝ) :
    (coordHomeomorph e).symm x = fun j => x (e.symm j) := rfl

/-! ## A general topology fact -/

/-- A homeomorphism carries the connected component of `a` inside the preimage of `S`
to the preimage of the connected component of `h a` inside `S`. -/
theorem homeomorph_preimage_connectedComponentIn {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] (h : α ≃ₜ β) (S : Set β) (a : α) :
    connectedComponentIn (h ⁻¹' S) a = h ⁻¹' connectedComponentIn S (h a) := by
  by_cases ha : a ∈ h ⁻¹' S
  · have himg : h '' connectedComponentIn (h ⁻¹' S) a = connectedComponentIn S (h a) := by
      rw [Homeomorph.image_connectedComponentIn h ha, Set.image_preimage_eq _ h.surjective]
    calc connectedComponentIn (h ⁻¹' S) a
        = h ⁻¹' (h '' connectedComponentIn (h ⁻¹' S) a) :=
          (Set.preimage_image_eq _ h.injective).symm
      _ = h ⁻¹' connectedComponentIn S (h a) := by rw [himg]
  · have hna : h a ∉ S := ha
    rw [connectedComponentIn_eq_empty ha, connectedComponentIn_eq_empty hna, Set.preimage_empty]

/-! ## Evaluating a reindexed chain and polynomial -/

/-- The affine form of a reindexed chain, evaluated at a point, equals the affine form of the
original chain evaluated at the correspondingly permuted point. -/
theorem EAChain.reindex_ell {k K r : ℕ} (e : Fin k ≃ Fin K) (c : EAChain k r) (j : Fin r)
    (y : Fin K → ℝ) :
    (Work.WilE7.EAChain.reindex e c).ell j y = c.ell j (fun i => y (e i)) := by
  simp only [EAChain.ell, Work.WilE7.EAChain.reindex]
  have hsum : (∑ i : Fin K, c.a j (e.symm i) * y i) =
      ∑ i : Fin k, c.a j i * y (e i) :=
    Fintype.sum_equiv e.symm (fun i : Fin K => c.a j (e.symm i) * y i)
      (fun i : Fin k => c.a j i * y (e i)) (fun i => by simp)
  rw [hsum]

/-- Evaluating a reindexed `EA`-polynomial on a reindexed chain at a point equals evaluating the
original polynomial on the original chain at the permuted point. -/
theorem EAChain.reindex_eaEval {k K r : ℕ} (e : Fin k ≃ Fin K) (c : EAChain k r)
    (Q : EAPoly k r) (y : Fin K → ℝ) :
    eaEval (Work.WilE7.EAChain.reindex e c) (Work.WilE7.EAPoly.reindex e Q) y =
      eaEval c Q (fun i => y (e i)) := by
  have hfun : (Sum.elim y (fun j => Real.exp ((Work.WilE7.EAChain.reindex e c).ell j y))) ∘
        (Sum.map e id) =
      (Sum.elim (fun i => y (e i)) (fun j => Real.exp (c.ell j (fun i => y (e i))))) := by
    funext s
    rcases s with i | j
    · simp
    · simp only [Function.comp_apply, Sum.map_inr, Sum.elim_inr]
      rw [Work.WilE7.EAChain.reindex_ell]
      rfl
  simp only [eaEval, Work.WilE7.EAPoly.reindex]
  rw [MvPolynomial.eval_rename, hfun]

/-- A basic set reindexed along `e` holds at `y` iff the original basic set holds at the
permuted point. -/
theorem Basic.reindex_holds {k K r : ℕ} (e : Fin k ≃ Fin K) (c : EAChain k r)
    (B : Basic k r) (y : Fin K → ℝ) :
    (Work.WilE7.Basic.reindex e B).holds (Work.WilE7.EAChain.reindex e c) y ↔
      B.holds c (fun i => y (e i)) := by
  simp only [Basic.holds, Work.WilE7.Basic.reindex]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun f hf => ?_, fun g hg => ?_⟩
    · rw [← Work.WilE7.EAChain.reindex_eaEval e c f y]
      exact h1 _ (List.mem_map.mpr ⟨f, hf, rfl⟩)
    · rw [← Work.WilE7.EAChain.reindex_eaEval e c g y]
      exact h2 _ (List.mem_map.mpr ⟨g, hg, rfl⟩)
  · rintro ⟨h1, h2⟩
    refine ⟨fun f hf => ?_, fun g hg => ?_⟩
    · obtain ⟨f', hf', hfe⟩ := List.mem_map.mp hf
      subst hfe
      rw [Work.WilE7.EAChain.reindex_eaEval e c f' y]
      exact h1 f' hf'
    · obtain ⟨g', hg', hge⟩ := List.mem_map.mp hg
      subst hge
      rw [Work.WilE7.EAChain.reindex_eaEval e c g' y]
      exact h2 g' hg'

/-! ## The set of a reindexed semi-Pfaffian set -/

theorem mem_cubeC_reindex {k K : ℕ} (e : Fin k ≃ Fin K) (y : Fin K → ℝ) :
    y ∈ cubeC K ↔ (fun i => y (e i)) ∈ cubeC k := by
  simp only [cubeC, Set.mem_ofPred_eq]
  exact e.forall_congr_right.symm

theorem mem_basics_reindex {k K : ℕ} (e : Fin k ≃ Fin K) (X : SemiPf k) (y : Fin K → ℝ) :
    (∃ B ∈ X.basics.map (Work.WilE7.Basic.reindex e),
        B.holds (Work.WilE7.EAChain.reindex e X.c) y) ↔
      ∃ B ∈ X.basics, B.holds X.c (fun i => y (e i)) := by
  constructor
  · rintro ⟨B, hB, hh⟩
    obtain ⟨B', hB', hBe⟩ := List.mem_map.mp hB
    subst hBe
    exact ⟨B', hB', (Work.WilE7.Basic.reindex_holds e X.c B' y).mp hh⟩
  · rintro ⟨B, hB, hh⟩
    exact ⟨Work.WilE7.Basic.reindex e B, List.mem_map.mpr ⟨B, hB, rfl⟩,
      (Work.WilE7.Basic.reindex_holds e X.c B y).mpr hh⟩

/-- The set of a reindexed semi-Pfaffian set is the preimage of the original set. -/
theorem reindex_set {k K : ℕ} (e : Fin k ≃ Fin K) (X : SemiPf k) :
    (Work.WilE7.SemiPf.reindex e X).set = {y | (fun i => y (e i)) ∈ X.set} := by
  ext y
  simp only [SemiPf.set, Work.WilE7.SemiPf.reindex, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hy, hb⟩
    exact ⟨(mem_cubeC_reindex e y).mp hy, (mem_basics_reindex e X y).mp hb⟩
  · rintro ⟨hy, hb⟩
    exact ⟨(mem_cubeC_reindex e y).mpr hy, (mem_basics_reindex e X y).mpr hb⟩

/-! ## The main statement -/

theorem reindex_component {k K : ℕ} (e : Fin k ≃ Fin K) (X : WilkiesDesign.E.SemiPf k)
    (p : Fin k → ℝ) :
    connectedComponentIn (Work.WilE7.SemiPf.reindex e X).set (fun i => p (e.symm i))
      = {y | (fun i => y (e i)) ∈ connectedComponentIn X.set p} := by
  have hset : (Work.WilE7.SemiPf.reindex e X).set = (coordHomeomorph e) ⁻¹' X.set := by
    rw [reindex_set]
    rfl
  have ha : (coordHomeomorph e) (fun i => p (e.symm i)) = p := by
    funext i
    simp
  rw [hset, homeomorph_preimage_connectedComponentIn (coordHomeomorph e) X.set
    (fun i => p (e.symm i)), ha]
  rfl

end Work.WilE7
