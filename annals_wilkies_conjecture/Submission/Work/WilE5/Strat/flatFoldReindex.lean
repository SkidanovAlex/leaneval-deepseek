import Mathlib
import Submission.Work.WilE5.Sys
import Submission.Work.Strat.detOp_extH_eq

noncomputable section
open Classical Filter
open scoped Topology

namespace Work.WilE5.Strat

open WilkiesDesign WilkiesDesign.E

/-! ## §0. Reindexing the folds: the extended system computes `yOpSt`

`opMono` folds over the ambient index type `Fin (p+q)`, `yOpSt` over the fibre index type
`Fin q`.  For a multi-index supported on the fibre directions the two agree; the content is the
splitting `List.finRange (p + q) = base directions ++ fibre directions`. -/

/-- `List.finRange (p + q)` splits into the base directions followed by the fibre directions. -/
theorem finRange_add_eq (p q : ℕ) :
    List.finRange (p + q) =
      ((List.finRange p).map (Fin.castAdd q)) ++ ((List.finRange q).map (Fin.natAdd p)) := by
  have hfun : (id : Fin (p + q) → Fin (p + q)) =
      Fin.append (fun i : Fin p => Fin.castAdd q i) (fun i : Fin q => Fin.natAdd p i) := by
    funext i
    rcases exists_castAdd_or_yDir i with ⟨j, rfl⟩ | ⟨l, rfl⟩
    · simp
    · simp [Work.WilE5.yDir]
  rw [show List.finRange (p + q) =
      List.ofFn (Fin.append (fun i : Fin p => Fin.castAdd q i)
        (fun i : Fin q => Fin.natAdd p i)) from by
    rw [← hfun]
    exact (List.ofFn_id (p + q)).symm]
  rw [List.ofFn_fin_append, List.ofFn_eq_map, List.ofFn_eq_map]

/-- A right fold whose steps are all the identity is the identity. -/
private theorem foldr_id_of_forall {ι α : Type*} (l : List ι) (f : ι → α → α) (a : α)
    (h : ∀ i ∈ l, ∀ x, f i x = x) : l.foldr (fun i acc => f i acc) a = a := by
  induction l generalizing a with
  | nil => rfl
  | cons i is ih =>
    rw [List.foldr_cons]
    rw [h i (by simp) (is.foldr (fun i acc => f i acc) a)]
    exact ih a fun j hj => h j (by simp [hj])

/-- A right fold is unchanged when its steps agree on the list. -/
private theorem foldr_congr_of_forall {ι α : Type*} (l : List ι) (f f' : ι → α → α)
    (h : ∀ i ∈ l, f i = f' i) (a : α) :
    l.foldr (fun i acc => f i acc) a = l.foldr (fun i acc => f' i acc) a := by
  induction l generalizing a with
  | nil => rfl
  | cons i is ih =>
    rw [List.foldr_cons, List.foldr_cons, h i (by simp)]
    exact congrArg (f' i) (ih (fun j hj => h j (by simp [hj])) a)

/-- Reindexing the ordered operator's fold along the base/fibre split. -/
theorem foldr_finRange_eq {p q : ℕ} {α : Type*} (g : Fin (p + q) → α → α)
    (m : Fin (p + q) → ℕ) (a : α) (hm : ∀ i : Fin p, m (Fin.castAdd q i) = 0) :
    (List.finRange (p + q)).foldr (fun i acc => (g i)^[m i] acc) a
      = (List.finRange q).foldr (fun l acc => (g (Fin.natAdd p l))^[m (Fin.natAdd p l)] acc) a := by
  rw [finRange_add_eq p q, List.foldr_append, List.foldr_map, List.foldr_map]
  rw [foldr_id_of_forall (List.finRange p)
    (fun i (acc : α) => (g (Fin.castAdd q i))^[m (Fin.castAdd q i)] acc) _
    (fun i _ x => by rw [hm i, Function.iterate_zero_apply])]

/-- The ordered operator of the extended system `(hFun B, x_i - z_i)` computes the iterated
fibrewise operator `yOpSt` on multi-indices supported on the fibre directions. -/
theorem opMono_extH_eq_yOpSt {p q r : ℕ} (c : EAChain (p + q) r)
    (B : List (EAPoly (p + q) r × Fin q)) (z : Fin (p + q) → ℝ)
    (m : Fin (p + q) → ℕ) (ψ : EAPoly (p + q) r)
    (hm : ∀ i : Fin p, m (Fin.castAdd q i) = 0) :
    opMono c (extH (hFun B) z) (extι (pivFun B)) m ψ
      = yOpSt c B (fun l => m (yDir p l)) ψ := by
  unfold WilkiesDesign.E.opMono Work.WilE5.yOpSt
  rw [foldr_finRange_eq (g := fun i (acc : EAPoly (p + q) r) =>
      detOp c (extH (hFun B) z) (extι (pivFun B)) i acc) m ψ hm]
  refine foldr_congr_of_forall (List.finRange q) _ _ (fun l _ => ?_) ψ
  funext acc
  show (detOp c (extH (hFun B) z) (extι (pivFun B)) (Fin.natAdd p l))^[m (Fin.natAdd p l)] acc
      = (detOpSt c B l)^[m (yDir p l)] acc
  rw [show detOp c (extH (hFun B) z) (extι (pivFun B)) (Fin.natAdd p l) = detOpSt c B l from
    funext fun f =>
      Work.Strat.detOp_extH_eq c (hFun B) (pivFun B) (fun a => ⟨(B.get a).2, rfl⟩) z f l]
  rfl

/-- The atom degrees of the extended system are dominated by those of the system plus `2 p`. -/
theorem sum_atomDeg_extH_le {p q r j : ℕ} (h : Fin j → EAPoly (p + q) r)
    (z : Fin (p + q) → ℝ) :
    (∑ a : Fin (j + p), atomDeg (extH h z a)) ≤ (∑ a : Fin j, atomDeg (h a)) + 2 * p := by
  rw [Fin.sum_univ_add]
  have h1 : (∑ i : Fin j, atomDeg (extH h z (Fin.castAdd p i))) = ∑ i : Fin j, atomDeg (h i) :=
    Finset.sum_congr rfl fun i _ => by rw [extH, Fin.append_left]
  have hx : ∀ i : Fin p, atomDeg (extH h z (Fin.natAdd j i)) ≤ 2 := by
    intro i
    rw [extH, Fin.append_right]
    show (xShift (q := q) (r := r) z i).totalDegree + 1 ≤ 2
    have h2 : (xShift (q := q) (r := r) z i).totalDegree ≤ 1 := by
      rw [xShift]
      refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
      rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C]
      exact le_of_eq (max_eq_left (Nat.zero_le 1))
    omega
  have h2 : (∑ i : Fin p, atomDeg (extH h z (Fin.natAdd j i))) ≤ 2 * p := by
    calc (∑ i : Fin p, atomDeg (extH h z (Fin.natAdd j i))) ≤ ∑ _i : Fin p, 2 :=
          Finset.sum_le_sum fun i _ => hx i
      _ = 2 * p := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
          ring
  rw [h1]
  omega

end Work.WilE5.Strat
