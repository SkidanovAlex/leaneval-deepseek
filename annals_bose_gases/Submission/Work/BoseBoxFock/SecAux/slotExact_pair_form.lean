import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.FibreProjDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.SecAux.slotExact_pair_form`

The two-term (paired) form of the `S`-sector `slotExact e S Ψ`: for `i ∉ S` the inclusion–exclusion
sum over the supersets of `S` can be reorganized into a sum over the supersets of `S` that *avoid*
`i`, each carrying the pair `slotProj e T Ψ − slotProj e (insert i T) Ψ`.

The content is purely combinatorial: the supersets of `S` split into those avoiding `i` (the index
set `R` of the right-hand side) and those containing `i`; the map `T ↦ insert i T` is a bijection
from the former onto the latter, and on it the alternating sign flips:
`(-1)^{|insert i T| - |S|} = -(-1)^{|T| - |S|}`.
-/

namespace Work.BoseBoxFock.SecAux

theorem slotExact_pair_form {m n : ℕ} (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ)
    (S : Finset (Fin n)) (i : Fin n) (hi : i ∉ S)
    (Ψ : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ) :
    slotExact e S Ψ = ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T ∧ i ∉ T),
      (-1 : ℂ) ^ (T.card - S.card) • (slotProj e T Ψ - slotProj e (insert i T) Ψ) := by
  classical
  -- The index set of the right-hand side (supersets of `S` avoiding `i`) and its two companions:
  -- `R'` = supersets of `S` containing `i`, `A` = all supersets of `S`.
  set R : Finset (Finset (Fin n)) := Finset.univ.filter (fun T => S ⊆ T ∧ i ∉ T) with hR
  set R' : Finset (Finset (Fin n)) := Finset.univ.filter (fun T => S ⊆ T ∧ i ∈ T) with hR'
  set A : Finset (Finset (Fin n)) := Finset.univ.filter (fun T => S ⊆ T) with hA
  have hRmem : ∀ T : Finset (Fin n), T ∈ R ↔ S ⊆ T ∧ i ∉ T := by
    intro T; rw [hR, Finset.mem_filter]; simp
  have hR'mem : ∀ T : Finset (Fin n), T ∈ R' ↔ S ⊆ T ∧ i ∈ T := by
    intro T; rw [hR', Finset.mem_filter]; simp
  have hAmem : ∀ T : Finset (Fin n), T ∈ A ↔ S ⊆ T := by
    intro T; rw [hA, Finset.mem_filter]; simp
  -- `A` is the disjoint union of `R` and `R'` (as `i ∉ S`, a superset of `S` either avoids or
  -- contains `i`).
  have hAeq : A = R ∪ R' := by
    refine Finset.ext (fun T => ?_)
    rw [hAmem T, Finset.mem_union, hRmem T, hR'mem T]
    constructor
    · intro h; by_cases hc : i ∈ T
      · exact Or.inr ⟨h, hc⟩
      · exact Or.inl ⟨h, hc⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  have hdisj : Disjoint R R' := Finset.disjoint_left.mpr (fun T hT hT' => by
    have h1 : i ∉ T := ((hRmem T).mp hT).2
    have h2 : i ∈ T := ((hR'mem T).mp hT').2
    exact h1 h2)
  -- Splitting the defining sum of `slotExact` over `R ⊔ R'`.
  have hsplit : ∑ T ∈ A, (-1 : ℂ) ^ (T.card - S.card) • slotProj e T Ψ
      = ∑ T ∈ R, (-1 : ℂ) ^ (T.card - S.card) • slotProj e T Ψ
        + ∑ T ∈ R', (-1 : ℂ) ^ (T.card - S.card) • slotProj e T Ψ := by
    rw [hAeq, Finset.sum_union hdisj]
  -- Reindexing the `insert i`-leg of the right-hand side by the bijection `R → R'`, `T ↦ insert i T`
  -- (the sign flips, see the last goal of `sum_nbij`).
  have hbij : ∑ T ∈ R, (-1 : ℂ) ^ (T.card - S.card) • slotProj e (insert i T) Ψ
      = ∑ T ∈ R', (-(-1 : ℂ) ^ (T.card - S.card)) • slotProj e T Ψ := by
    refine Finset.sum_nbij (fun T : Finset (Fin n) => insert i T) ?_ ?_ ?_ ?_
    · intro a ha
      exact (hR'mem (insert i a)).mpr
        ⟨Finset.Subset.trans ((hRmem a).mp ha).1 (Finset.subset_insert i a),
          Finset.mem_insert_self i a⟩
    · intro a ha b hb hab
      have ha2 : i ∉ a := ((hRmem a).mp ha).2
      have hb2 : i ∉ b := ((hRmem b).mp hb).2
      have h' := congrArg (fun (U : Finset (Fin n)) => U.erase i) hab
      rwa [Finset.erase_insert ha2, Finset.erase_insert hb2] at h'
    · intro b hb
      refine ⟨b.erase i, ?_, ?_⟩
      · exact (hRmem (b.erase i)).mpr
          ⟨Finset.subset_erase.mpr ⟨((hR'mem b).mp hb).1, hi⟩, Finset.notMem_erase i b⟩
      · exact Finset.insert_erase ((hR'mem b).mp hb).2
    · intro a ha
      have ha2 : i ∉ a := ((hRmem a).mp ha).2
      have hcard : (insert i a).card = a.card + 1 := Finset.card_insert_of_notMem ha2
      have hle : S.card ≤ a.card := Finset.card_le_card ((hRmem a).mp ha).1
      have hexp : (insert i a).card - S.card = (a.card - S.card) + 1 := by
        rw [hcard]; omega
      have hval : (-1 : ℂ) ^ (a.card - S.card)
          = -((-1 : ℂ) ^ ((insert i a).card - S.card)) := by
        rw [hexp, pow_succ]; ring
      rw [hval]
  -- Distributing the scalar multiplication in the difference.
  have hRHS : ∑ T ∈ R, (-1 : ℂ) ^ (T.card - S.card) •
        (slotProj e T Ψ - slotProj e (insert i T) Ψ)
      = ∑ T ∈ R, (-1 : ℂ) ^ (T.card - S.card) • slotProj e T Ψ
        - ∑ T ∈ R, (-1 : ℂ) ^ (T.card - S.card) • slotProj e (insert i T) Ψ := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun T _ => smul_sub _ _ _)
  -- Pulling the global sign out of the reindexed sum.
  have hneg : ∑ T ∈ R', (-(-1 : ℂ) ^ (T.card - S.card)) • slotProj e T Ψ
      = - ∑ T ∈ R', (-1 : ℂ) ^ (T.card - S.card) • slotProj e T Ψ := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun T _ => neg_smul _ _)
  rw [slotExact, ← hA, hsplit, hRHS, hbij, hneg, sub_neg_eq_add]

end Work.BoseBoxFock.SecAux
