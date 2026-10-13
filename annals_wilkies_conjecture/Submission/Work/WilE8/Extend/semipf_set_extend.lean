import Mathlib
import Submission.Work.WilE8.Extend

namespace Work.WilE8.Extend

open WilkiesDesign WilkiesDesign.E

/-!
# Extending a semi-Pfaffian set along a map of variables

`Work.WilE8.SemiPf.extend e X` pulls back the data of a semi-Pfaffian set `X` in `ℝ^k` along a
map `e : Fin k → Fin k'`.  This file computes the underlying point set: extending is *literally*
applying `x ↦ (fun i => x (e i))`, and the only condition on the new coordinates is that they lie
in the closed cube.

The mathematical content is that the chain extension `EAChain.extend` reproduces the affine forms
`c.ell j` after substituting `x i ↦ x (e i)`; this is where injectivity of `e` is used (the
extension sets the coefficients on coordinates that are *not* in the image of `e` to `0`, so the
value of `a` on `e i` must be recoverable, which needs `e` injective).
-/

/-- The chain extension preserves the affine forms after the substitution `x ↦ x ∘ e`. -/
lemma extend_ell_inj {k k' r : ℕ} {e : Fin k → Fin k'} (he : Function.Injective e)
    (c : EAChain k r) (j : Fin r) (x : Fin k' → ℝ) :
    (Work.WilE8.EAChain.extend e c).ell j x = c.ell j (fun i => x (e i)) := by
  -- On the image of `e` the extended coefficients are the original ones.
  have ha : ∀ i : Fin k, (Work.WilE8.EAChain.extend e c).a j (e i) = c.a j i := by
    intro i
    have h : ∃ i', e i' = e i := ⟨i, rfl⟩
    have h2 : (Work.WilE8.EAChain.extend e c).a j (e i) = c.a j h.choose := by
      show (dite (∃ i', e i' = e i) (fun h => c.a j h.choose) (fun _ => 0)) = c.a j h.choose
      exact dite_eq_left h
    rw [h2]
    congr 1
    exact he h.choose_spec
  -- Off the image of `e` the extended coefficients vanish, so the finite sum may be
  -- restricted to the image and then reindexed.
  have hzero : ∀ i' : Fin k', i' ∉ Set.range e →
      (Work.WilE8.EAChain.extend e c).a j i' * x i' = 0 := by
    intro i' hi'
    have hni : ¬ (∃ i, e i = i') := by rintro ⟨i, hi⟩; exact hi' ⟨i, hi⟩
    show (dite (∃ i, e i = i') (fun h => c.a j h.choose) (fun _ => 0)) * x i' = 0
    rw [dite_eq_right (fun h => absurd h hni), zero_mul]
  have hsum : (∑ i' : Fin k', (Work.WilE8.EAChain.extend e c).a j i' * x i')
      = ∑ i : Fin k, c.a j i * x (e i) := by
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image e))
      (fun i' _ hi' => hzero i' (by
        intro h; exact hi' (Finset.mem_image.mpr ⟨h.choose, Finset.mem_univ _, h.choose_spec⟩)))]
    rw [Finset.sum_image (fun a _ b _ hab => he hab)]
    exact Finset.sum_congr rfl (fun i _ => by rw [ha i])
  simp only [EAChain.ell]
  rw [hsum]
  rfl

/-- Evaluating an extended EA polynomial at `x` is evaluating the original one at `x ∘ e`. -/
lemma extend_eaEval_inj {k k' r : ℕ} {e : Fin k → Fin k'} (he : Function.Injective e)
    (c : EAChain k r) (Q : EAPoly k r) (x : Fin k' → ℝ) :
    eaEval (Work.WilE8.EAChain.extend e c) (Work.WilE8.EAPoly.extend e Q) x
      = eaEval c Q (fun i => x (e i)) := by
  have hell := fun (j : Fin r) => extend_ell_inj he c j x
  unfold eaEval Work.WilE8.EAPoly.extend
  rw [MvPolynomial.eval_rename]
  have hfun : ((Sum.elim x fun j => Real.exp ((Work.WilE8.EAChain.extend e c).ell j x)) ∘
        Sum.map e id) =
      (Sum.elim (fun i => x (e i)) fun j => Real.exp (c.ell j fun i => x (e i))) := by
    funext s
    rcases s with i | j
    · rfl
    · show Real.exp ((Work.WilE8.EAChain.extend e c).ell j x) =
        Real.exp (c.ell j fun i => x (e i))
      rw [hell j]
  rw [hfun]

/-- The equations of an extended basic set, spelled out. -/
lemma extend_basic_eqs {k k' r : ℕ} (e : Fin k → Fin k') (B : Basic k r) :
    (Work.WilE8.Basic.extend e B).eqs = B.eqs.map (Work.WilE8.EAPoly.extend e) := rfl

/-- The inequalities of an extended basic set, spelled out. -/
lemma extend_basic_pos {k k' r : ℕ} (e : Fin k → Fin k') (B : Basic k r) :
    (Work.WilE8.Basic.extend e B).pos = B.pos.map (Work.WilE8.EAPoly.extend e) := rfl

/-- Extending a basic set preserves the solution set, after the substitution `x ↦ x ∘ e`. -/
lemma extend_basic_holds_inj {k k' r : ℕ} {e : Fin k → Fin k'} (he : Function.Injective e)
    (c : EAChain k r) (B : Basic k r) (x : Fin k' → ℝ) :
    (Work.WilE8.Basic.extend e B).holds (Work.WilE8.EAChain.extend e c) x ↔
      B.holds c (fun i => x (e i)) := by
  have heq : ∀ f, eaEval (Work.WilE8.EAChain.extend e c) (Work.WilE8.EAPoly.extend e f) x
      = eaEval c f (fun i => x (e i)) := fun f => extend_eaEval_inj he c f x
  simp only [Basic.holds]
  rw [extend_basic_eqs, extend_basic_pos, List.forall_mem_map, List.forall_mem_map]
  refine and_congr ?_ ?_
  · refine forall₂_congr (fun f _ => ?_); rw [heq f]
  · refine forall₂_congr (fun f _ => ?_); rw [heq f]

theorem semipf_set_extend {k k' : ℕ} {e : Fin k → Fin k'} (he : Function.Injective e)
    (X : WilkiesDesign.E.SemiPf k) :
    (Work.WilE8.SemiPf.extend e X).set
      = {x : Fin k' → ℝ | x ∈ WilkiesDesign.E.cubeC k' ∧ (fun i => x (e i)) ∈ X.set} := by
  ext x
  constructor
  · intro hx
    obtain ⟨hcube, B', hB', hholds⟩ := hx
    have hB'' : B' ∈ X.basics.map (Work.WilE8.Basic.extend e) := hB'
    obtain ⟨B, hB, hB'eq⟩ := List.mem_map.mp hB''
    rw [← hB'eq] at hholds
    exact ⟨hcube, fun i => hcube (e i), B, hB, (extend_basic_holds_inj he X.c B x).mp hholds⟩
  · intro hx
    obtain ⟨hcube, hyc, B, hB, hholds⟩ := hx
    exact ⟨hcube, Work.WilE8.Basic.extend e B, List.mem_map.mpr ⟨B, hB, rfl⟩,
      (extend_basic_holds_inj he X.c B x).mpr hholds⟩

end Work.WilE8.Extend
