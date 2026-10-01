import Mathlib
import Submission.Work.LinnikBurgess.frame_step_defs

/-!
# Symmetry of the frame sum (`frameSum_eq_zero`)

The frame sum

`frameSum H m d g i = ∑_{q ∈ S_i} W_m(shift6 q,i) * frameW d g q`,

where `S_i` is the set of pairs `q = (a, b)` of triples whose shift vector `v = shift6 q` has a
*unique* entry at position `i`, is independent of `i ∈ Fin 6`.

The proof exhibits the symmetries of the situation.  Write `Fin 6` as `Fin 3 ⊕ Fin 3`, the first
summand being the three entries of the first triple and the second summand the three entries of the
second triple:

* **swap** (`(a,b) ↦ (b,a)`) interchanges the two summands, hence acts on indices by
  `i ↦ swapEq i` (`summand-swap`); it preserves both the uniqueness condition and the weight,
  because `contAB` and `DLd` are symmetric in their two arguments;
* **permuting the first triple** (`a ↦ a ∘ σ`) acts on indices by `i ↦ permAEq σ i`, fixing the
  second summand; it preserves the weight because `esymm3`, `contAB`, `critN` and `DLd` are
  symmetric functions of the entries of a triple.

Both transformations are bijections of the finite set of pairs, so reindexing the sum shows that
`frameSum i = frameSum (g · i)` for each symmetry `g`; since the generated group acts transitively
on `Fin 6` (any index is carried to `0`), all frame sums agree.

The two reindexings are collected in `frameSum_reindex`, and the (two) relevant differences
`shift6 (T q) = shift6 q ∘ e` are `shift6_swap` and `shift6_permA`.
-/

open scoped BigOperators
open Classical

namespace Work.LinnikBurgess

open Polynomial

/-! ## The six shift positions as `Fin 3 ⊕ Fin 3` -/

/-- The `Fin 3 ⊕ Fin 3` description of the six positions: the first summand indexes the three
entries of the first triple, the second summand the three entries of the second triple. -/
private def e6 : Fin 6 ≃ Fin 3 ⊕ Fin 3 := (finSumFinEquiv (m := 3) (n := 3)).symm

private lemma e6_inl (l : Fin 3) : e6.symm (Sum.inl l) = Fin.castAdd 3 l := by
  show finSumFinEquiv (Sum.inl l) = Fin.castAdd 3 l
  exact finSumFinEquiv_apply_left l

private lemma e6_inr (l : Fin 3) : e6.symm (Sum.inr l) = Fin.natAdd 3 l := by
  show finSumFinEquiv (Sum.inr l) = Fin.natAdd 3 l
  exact finSumFinEquiv_apply_right l

/-- The first three of the six shifts are the shifts of the first triple. -/
private lemma shift6_castAdd {H : ℕ} (q : (Fin 3 → Fin H) × (Fin 3 → Fin H)) (l : Fin 3) :
    shift6 q (Fin.castAdd 3 l) = (q.1 l : ℕ) + 1 := by
  obtain ⟨f, g⟩ := q; fin_cases l <;> simp [shift6, Fin.castAdd]

/-- The last three of the six shifts are the shifts of the second triple. -/
private lemma shift6_natAdd {H : ℕ} (q : (Fin 3 → Fin H) × (Fin 3 → Fin H)) (l : Fin 3) :
    shift6 q (Fin.natAdd 3 l) = (q.2 l : ℕ) + 1 := by
  obtain ⟨f, g⟩ := q; fin_cases l <;> simp [shift6, Fin.natAdd]

/-- The index permutation of `Fin 6` induced by swapping the two triples. -/
private def swapEq : Fin 6 ≃ Fin 6 := (e6.trans (Equiv.sumComm (Fin 3) (Fin 3))).trans e6.symm

/-- The index permutation of `Fin 6` induced by permuting the entries of the first triple. -/
private def permAEq (σ : Equiv.Perm (Fin 3)) : Fin 6 ≃ Fin 6 :=
  (e6.trans (Equiv.sumCongr σ (Equiv.refl (Fin 3)))).trans e6.symm

private lemma swapEq_inl (l : Fin 3) : swapEq (e6.symm (Sum.inl l)) = e6.symm (Sum.inr l) := by
  simp only [swapEq, Equiv.trans_apply, Equiv.sumComm_apply, Equiv.apply_symm_apply, Sum.swap,
    Sum.elim_inl]

private lemma swapEq_inr (l : Fin 3) : swapEq (e6.symm (Sum.inr l)) = e6.symm (Sum.inl l) := by
  simp only [swapEq, Equiv.trans_apply, Equiv.sumComm_apply, Equiv.apply_symm_apply, Sum.swap,
    Sum.elim_inr]

private lemma permAEq_inl (σ : Equiv.Perm (Fin 3)) (l : Fin 3) :
    permAEq σ (e6.symm (Sum.inl l)) = e6.symm (Sum.inl (σ l)) := by
  simp only [permAEq, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl,
    Equiv.apply_symm_apply]

private lemma permAEq_inr (σ : Equiv.Perm (Fin 3)) (l : Fin 3) :
    permAEq σ (e6.symm (Sum.inr l)) = e6.symm (Sum.inr l) := by
  simp only [permAEq, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr,
    Equiv.apply_symm_apply, Equiv.refl_apply]

/-- Swapping the two triples twists the shift vector by `swapEq`. -/
private lemma shift6_swap {H : ℕ} (q : (Fin 3 → Fin H) × (Fin 3 → Fin H)) :
    shift6 (Prod.swap q) = shift6 q ∘ swapEq := by
  funext i
  rcases h : e6 i with l | l
  · have hi : i = e6.symm (Sum.inl l) := by rw [← h, Equiv.symm_apply_apply]
    rw [hi, Function.comp_apply, swapEq_inl, e6_inl, e6_inr]
    fin_cases l <;> simp [shift6, Fin.castAdd, Fin.natAdd]
  · have hi : i = e6.symm (Sum.inr l) := by rw [← h, Equiv.symm_apply_apply]
    rw [hi, Function.comp_apply, swapEq_inr, e6_inl, e6_inr]
    fin_cases l <;> simp [shift6, Fin.castAdd, Fin.natAdd]

/-- Permuting the entries of the first triple twists the shift vector by `permAEq σ`. -/
private lemma shift6_permA {H : ℕ} (σ : Equiv.Perm (Fin 3))
    (q : (Fin 3 → Fin H) × (Fin 3 → Fin H)) :
    shift6 (q.1 ∘ σ, q.2) = shift6 q ∘ permAEq σ := by
  obtain ⟨f, g⟩ := q
  funext i
  rcases h : e6 i with l | l
  · have hi : i = e6.symm (Sum.inl l) := by rw [← h, Equiv.symm_apply_apply]
    rw [hi, Function.comp_apply, permAEq_inl, e6_inl l, e6_inl (σ l),
      shift6_castAdd, shift6_castAdd]
    rfl
  · have hi : i = e6.symm (Sum.inr l) := by rw [← h, Equiv.symm_apply_apply]
    rw [hi, Function.comp_apply, permAEq_inr, e6_inr l, shift6_natAdd, shift6_natAdd]

private lemma e6_zero : e6.symm (Sum.inl (0 : Fin 3)) = (0 : Fin 6) := by
  rw [e6_inl]
  apply Fin.ext
  simp

/-! ## Invariance of the two factors of the weight -/

/-- The predicate "the `i`-th entry of `v` occurs exactly once". -/
private def U (v : Fin 6 → ℕ) (i : Fin 6) : Prop := ∀ i', i' ≠ i → v i ≠ v i'

/-- Uniqueness is transported by a bijection of the index set. -/
private lemma U_comp (e : Fin 6 ≃ Fin 6) (v : Fin 6 → ℕ) (j : Fin 6) :
    U (v ∘ e) j ↔ U v (e j) := by
  constructor
  · intro h j'' hj''
    obtain ⟨j', rfl⟩ := e.surjective j''
    exact h j' (fun hh => hj'' (congrArg e hh))
  · intro h j' hj'
    exact h (e j') (fun h' => hj' (e.injective h'))

/-- The weight `sqrtGcdW` is transported by a bijection of the index set. -/
private lemma sqrtGcdW_comp (m : ℕ) (e : Fin 6 ≃ Fin 6) (v : Fin 6 → ℕ) (i : Fin 6) :
    sqrtGcdW m i (v ∘ e) = sqrtGcdW m (e i) v := by
  unfold sqrtGcdW
  refine Finset.prod_bij (fun l _ => e l) ?_ ?_ ?_ ?_
  · intro l hl
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hl ⊢
    exact fun h => hl (e.injective h)
  · intro l₁ hl₁ l₂ hl₂ h
    exact e.injective h
  · intro b hb
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hb
    obtain ⟨a, ha⟩ := e.surjective b
    refine ⟨a, ?_, ha⟩
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro hai
    exact hb (by rw [← ha, hai])
  · intro l hl
    rfl

/-! ## Symmetry of `contAB` and `DLd` under permutations of one triple -/

/-- Explicit expansion of the cubic `∏_l (X + a_l)`. -/
private lemma cubicZ_eq_expand' (a : Fin 3 → ℕ) :
    cubicZ a = X^3 + C (esymm3 a 0) * X^2 + C (esymm3 a 1) * X + C (esymm3 a 2) := by
  rw [cubicZ, Fin.prod_univ_three]
  simp [esymm3]
  ring

/-- `cubicZ` only depends on the multiset of the entries. -/
private lemma cubicZ_comp (a : Fin 3 → ℕ) (σ : Equiv.Perm (Fin 3)) :
    cubicZ (a ∘ σ) = cubicZ a := by
  unfold cubicZ
  exact Fintype.prod_equiv σ (fun l => (X + C (((a ∘ σ) l : ℕ) : ℤ)))
    (fun l => (X + C ((a l : ℕ) : ℤ))) (by intro l; simp)

private lemma coeff_two_cub {c2 c1 c0 : ℤ} :
    ((X^3 + C c2 * X^2 + C c1 * X + C c0 : ℤ[X])).coeff 2 = c2 := by
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_X, Polynomial.coeff_C]
  norm_num

private lemma coeff_one_cub {c2 c1 c0 : ℤ} :
    ((X^3 + C c2 * X^2 + C c1 * X + C c0 : ℤ[X])).coeff 1 = c1 := by
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_X, Polynomial.coeff_C]
  norm_num

private lemma coeff_zero_cub {c2 c1 c0 : ℤ} :
    ((X^3 + C c2 * X^2 + C c1 * X + C c0 : ℤ[X])).coeff 0 = c0 := by
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_X, Polynomial.coeff_C]
  norm_num

/-- The elementary symmetric functions of a triple are invariant under permutations. -/
private lemma esymm3_comp (a : Fin 3 → ℕ) (σ : Equiv.Perm (Fin 3)) :
    esymm3 (a ∘ σ) = esymm3 a := by
  have h := cubicZ_comp a σ
  rw [cubicZ_eq_expand', cubicZ_eq_expand'] at h
  funext k
  fin_cases k
  · have hh := congrArg (fun p : ℤ[X] => p.coeff 2) h
    rw [coeff_two_cub, coeff_two_cub] at hh
    exact hh
  · have hh := congrArg (fun p : ℤ[X] => p.coeff 1) h
    rw [coeff_one_cub, coeff_one_cub] at hh
    exact hh
  · have hh := congrArg (fun p : ℤ[X] => p.coeff 0) h
    rw [coeff_zero_cub, coeff_zero_cub] at hh
    exact hh

/-- `contAB` is invariant under permutations of the first triple. -/
private lemma contAB_comp (a b : Fin 3 → ℕ) (σ : Equiv.Perm (Fin 3)) :
    contAB (a ∘ σ) b = contAB a b := by
  simp only [contAB, esymm3_comp]

/-- `critN` is invariant under permutations of the first triple. -/
private lemma critN_comp (a b : Fin 3 → ℕ) (σ : Equiv.Perm (Fin 3)) :
    critN (a ∘ σ) b = critN a b := by
  unfold critN
  rw [cubicZ_comp]

/-- `UnitAt` is invariant under permutations of the first triple. -/
private lemma UnitAt_comp (p y : ℕ) (a b : Fin 3 → ℕ) (σ : Equiv.Perm (Fin 3)) :
    UnitAt p y (a ∘ σ) b ↔ UnitAt p y a b := by
  unfold UnitAt
  constructor
  · intro h l
    refine ⟨?_, (h l).2⟩
    have hh := (h (σ.symm l)).1
    simp only [Function.comp_apply] at hh
    rwa [Equiv.apply_symm_apply] at hh
  · intro h l
    exact ⟨(h (σ l)).1, (h l).2⟩

/-- `DLd` is invariant under permutations of the first triple. -/
private lemma DLd_comp (d : ℕ) (a b : Fin 3 → ℕ) (σ : Equiv.Perm (Fin 3)) :
    DLd d (a ∘ σ) b ↔ DLd d a b := by
  unfold DLd
  constructor
  · rintro ⟨y, hU, h1, h2⟩
    refine ⟨y, fun p hp => (UnitAt_comp p y a b σ).mp (hU p hp), ?_, ?_⟩
    · rwa [critN_comp a b σ] at h1
    · rwa [critN_comp a b σ] at h2
  · rintro ⟨y, hU, h1, h2⟩
    refine ⟨y, fun p hp => (UnitAt_comp p y a b σ).mpr (hU p hp), ?_, ?_⟩
    · rwa [critN_comp a b σ]
    · rwa [critN_comp a b σ]

/-- `contAB` is symmetric in its two arguments. -/
private lemma contAB_comm (a b : Fin 3 → ℕ) : contAB a b = contAB b a := by
  have h : ∀ k : Fin 3, (esymm3 b k - esymm3 a k).natAbs =
      (esymm3 a k - esymm3 b k).natAbs := by
    intro k
    rw [show esymm3 b k - esymm3 a k = -(esymm3 a k - esymm3 b k) by ring, Int.natAbs_neg]
  simp only [contAB, h]

/-- `critN` is antisymmetric in its two arguments. -/
private lemma critN_comm (a b : Fin 3 → ℕ) : critN b a = -critN a b := by
  unfold critN; ring

/-- `UnitAt` is symmetric in its two triples. -/
private lemma UnitAt_comm (p y : ℕ) (a b : Fin 3 → ℕ) : UnitAt p y a b ↔ UnitAt p y b a := by
  unfold UnitAt
  exact forall_congr' (fun l => and_comm)

/-- `DLd` is symmetric in its two triples. -/
private lemma DLd_comm (d : ℕ) (a b : Fin 3 → ℕ) : DLd d a b ↔ DLd d b a := by
  unfold DLd
  constructor
  · rintro ⟨y, hU, h1, h2⟩
    refine ⟨y, fun p hp => (UnitAt_comm p y a b).mp (hU p hp), ?_, ?_⟩
    · rw [critN_comm, Polynomial.eval_neg]; exact dvd_neg.mpr h1
    · rw [critN_comm, Polynomial.derivative_neg, Polynomial.eval_neg]; exact dvd_neg.mpr h2
  · rintro ⟨y, hU, h1, h2⟩
    refine ⟨y, fun p hp => (UnitAt_comm p y a b).mpr (hU p hp), ?_, ?_⟩
    · rw [critN_comm, Polynomial.eval_neg]; exact dvd_neg.mpr h1
    · rw [critN_comm, Polynomial.derivative_neg, Polynomial.eval_neg]; exact dvd_neg.mpr h2

/-! ## Invariance of `frameW` -/

/-- The indicator weight `frameW` is invariant under swapping the two triples. -/
private lemma frameW_swap (H d g : ℕ) (fg : (Fin 3 → Fin H) × (Fin 3 → Fin H)) :
    frameW d g (Prod.swap fg) = frameW d g fg := by
  have h1 : aOf (Prod.swap fg) = bOf fg := rfl
  have h2 : bOf (Prod.swap fg) = aOf fg := rfl
  unfold frameW
  rw [h1, h2]
  refine if_congr ?_ rfl rfl
  constructor
  · rintro ⟨h, hc⟩
    exact ⟨(DLd_comm d _ _).mp h, by rwa [contAB_comm] at hc⟩
  · rintro ⟨h, hc⟩
    exact ⟨(DLd_comm d _ _).mpr h, by rwa [contAB_comm] at hc⟩

/-- The indicator weight `frameW` is invariant under permuting the entries of the first triple. -/
private lemma frameW_permA (H d g : ℕ) (σ : Equiv.Perm (Fin 3))
    (fg : (Fin 3 → Fin H) × (Fin 3 → Fin H)) :
    frameW d g (fg.1 ∘ σ, fg.2) = frameW d g fg := by
  have h1 : aOf (fg.1 ∘ σ, fg.2) = aOf fg ∘ σ := rfl
  have h2 : bOf (fg.1 ∘ σ, fg.2) = bOf fg := rfl
  unfold frameW
  rw [h1, h2]
  refine if_congr ?_ rfl rfl
  constructor
  · rintro ⟨h, hc⟩
    exact ⟨(DLd_comp d _ _ σ).mp h, by rwa [contAB_comp] at hc⟩
  · rintro ⟨h, hc⟩
    exact ⟨(DLd_comp d _ _ σ).mpr h, by rwa [contAB_comp]⟩

/-! ## Reindexing the frame sum -/

/-- A symmetry `T` of the set of pairs whose shift vector is twisted by the index bijection `e`
(`shift6 (T q) = shift6 q ∘ e`) and which preserves the weight `frameW` leaves the frame sum
invariant, with the indices transported by `e`. -/
private lemma frameSum_reindex (H m d g : ℕ) (i : Fin 6)
    (T : ((Fin 3 → Fin H) × (Fin 3 → Fin H)) ≃ ((Fin 3 → Fin H) × (Fin 3 → Fin H)))
    (e : Fin 6 ≃ Fin 6)
    (hshift : ∀ fg, shift6 (T fg) = shift6 fg ∘ e)
    (hW : ∀ fg, frameW d g (T fg) = frameW d g fg) :
    frameSum H m d g (e i) = frameSum H m d g i := by
  unfold frameSum
  refine Finset.sum_bijective T T.bijective ?_ ?_
  · intro fg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hshift fg]
    exact (U_comp e (shift6 fg) i).symm
  · intro fg _
    rw [hshift fg, hW fg, sqrtGcdW_comp m e (shift6 fg) i]

/-- The bijection of pairs swapping the two triples. -/
private def swapP (H : ℕ) :
    ((Fin 3 → Fin H) × (Fin 3 → Fin H)) ≃ ((Fin 3 → Fin H) × (Fin 3 → Fin H)) where
  toFun := Prod.swap
  invFun := Prod.swap
  left_inv := by rintro ⟨a, b⟩; rfl
  right_inv := by rintro ⟨a, b⟩; rfl

/-- The bijection of pairs permuting the entries of the first triple. -/
private def permAP (H : ℕ) (σ : Equiv.Perm (Fin 3)) :
    ((Fin 3 → Fin H) × (Fin 3 → Fin H)) ≃ ((Fin 3 → Fin H) × (Fin 3 → Fin H)) where
  toFun fg := (fg.1 ∘ σ, fg.2)
  invFun fg := (fg.1 ∘ σ.symm, fg.2)
  left_inv := by
    rintro ⟨f, g⟩
    refine Prod.ext ?_ rfl
    funext l
    simp
  right_inv := by
    rintro ⟨f, g⟩
    refine Prod.ext ?_ rfl
    funext l
    simp

/-- Symmetry of the frame sum.  `frameSum H m d g i` (the left-hand side of `frame_count` with unique index `i`) is independent of `i ∈ Fin 6`: swapping the two triples (`(f,g) ↦ (g,f)`) maps the index `i` to `i+3` and preserves the filtered sum, and relabelling the three `a`-coordinates permutes the indices `0,1,2`.  Hence the sum for any `i` equals the one for `i = 0`. -/
theorem frameSum_eq_zero (H m d g : ℕ) (i : Fin 6) : frameSum H m d g i = frameSum H m d g 0 := by
  have hswap : ∀ i : Fin 6, frameSum H m d g i = frameSum H m d g (swapEq i) := by
    intro i
    exact (frameSum_reindex H m d g i (swapP H) swapEq (fun fg => shift6_swap fg)
      (fun fg => frameW_swap H d g fg)).symm
  have hpermA : ∀ (σ : Equiv.Perm (Fin 3)) (i : Fin 6),
      frameSum H m d g i = frameSum H m d g (permAEq σ i) := by
    intro σ i
    exact (frameSum_reindex H m d g i (permAP H σ) (permAEq σ)
      (fun fg => shift6_permA σ fg) (fun fg => frameW_permA H d g σ fg)).symm
  have hreduce : ∀ l : Fin 3,
      frameSum H m d g (e6.symm (Sum.inr l)) = frameSum H m d g (e6.symm (Sum.inl l)) := by
    intro l
    calc frameSum H m d g (e6.symm (Sum.inr l))
        = frameSum H m d g (swapEq (e6.symm (Sum.inr l))) := hswap _
      _ = frameSum H m d g (e6.symm (Sum.inl l)) := by rw [swapEq_inr]
  have hfinal : ∀ l : Fin 3, frameSum H m d g (e6.symm (Sum.inl l)) = frameSum H m d g 0 := by
    intro l
    calc frameSum H m d g (e6.symm (Sum.inl l))
        = frameSum H m d g (permAEq (Equiv.swap l 0) (e6.symm (Sum.inl l))) :=
            hpermA (Equiv.swap l 0) _
      _ = frameSum H m d g (e6.symm (Sum.inl 0)) := by
            rw [permAEq_inl, Equiv.swap_apply_left]
      _ = frameSum H m d g 0 := by rw [e6_zero]
  rcases h : e6 i with l | l
  · have hi : i = e6.symm (Sum.inl l) := by rw [← h, Equiv.symm_apply_apply]
    rw [hi]; exact hfinal l
  · have hi : i = e6.symm (Sum.inr l) := by rw [← h, Equiv.symm_apply_apply]
    rw [hi, hreduce]; exact hfinal l

end Work.LinnikBurgess
