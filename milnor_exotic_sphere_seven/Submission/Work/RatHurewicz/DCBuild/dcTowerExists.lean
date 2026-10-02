import Mathlib
import Submission.Work.RatHurewicz.DCTowerDefs
import Submission.Work.RatHurewicz.fillingFamilyConst
import Submission.Work.RatHurewicz.boundaryMap
import Submission.Work.RatHurewicz.boundaryMapOne
import Submission.Work.RatHurewicz.faceComm
import Submission.Work.RatHurewicz.degenFaces
import Submission.Work.RatHurewicz.towerContraction
import Submission.Work.RatHurewicz.DCTowerAux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Existence of the degeneracy-compatible filling tower

`Work.RatHurewicz.DCTower` (`Submission/Work/RatHurewicz/DCTowerDefs.lean`) is a filling tower whose
filling of a degenerate cube is the degenerate extension of the filling of the underlying cube:
`Kf (m+1) (degenOp j φ) = degenOp (Fin.castSucc j) (Kf m φ)`.  Here we build such a tower, level by
level, from the triviality of `π_i (X, x₀)` for `i ≤ N`:

* a cube of the form `degenOp j φ` is filled by the degenerate extension of the filling of `φ`;
* every other cube is filled as in `Work.RatHurewicz.Tower_succ` (`boundaryMap` + `exists_level`).

The only point needing a genuine argument is that the value attached to a degenerate cube does not
depend on its presentation: if `degenOp i ψ = degenOp i' ψ'` with `i ≠ i'`, the two underlying
cubes are both degeneracies of a common `(n-1)`-cube (`exists_common_degenOp`, from the face
formulas of `degenFaces.lean`), and the two values agree by the double-degeneracy identity
`degenOp_degenOp_swap` (a consequence of `delG_comp_eq` of `faceComm.lean`).

The cube being filled is a `(m+1)`-cube, so the `hDC` compatibility of the previous level is only
needed at level `m-1`, which is exactly what the induction hypothesis supplies.
-/

open scoped unitInterval Topology
open Work.Stems.Cubical

namespace Work.RatHurewicz.DCBuild

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-! ## Degeneracy algebra -/

/-- A degeneracy is injective: `degenOp k` forgets nothing, since the degenerate cube determines
the cube it comes from by taking the face in the degeneracy direction. -/
theorem degenOp_injective {n : ℕ} (k : Fin (n + 1)) {χ χ' : C(IC n, X)}
    (h : degenOp k χ = degenOp k χ') : χ = χ' := by
  calc χ = (degenOp k χ).comp (faceCM k 0) := (degenOp_comp_faceCM_self k χ 0).symm
    _ = (degenOp k χ').comp (faceCM k 0) := by rw [h]
    _ = χ' := degenOp_comp_faceCM_self k χ' 0

/-- **Two presentations of a degenerate cube differ by a common cube.**  If `degenOp i ψ` and
`degenOp i' ψ'` are the same cube with `i ≠ i'`, then `ψ` and `ψ'` are both degeneracies (in the
indices obtained by deleting the other one) of a single cube `χ`. -/
theorem exists_common_degenOp {n : ℕ} {i i' : Fin (n + 2)} (h : i ≠ i')
    {ψ ψ' : C(IC (n + 1), X)} (heq : degenOp i ψ = degenOp i' ψ') :
    ∃ χ : C(IC n, X),
      ψ = degenOp (delIdx i i' h.symm) χ ∧ ψ' = degenOp (delIdx i' i h) χ := by
  refine ⟨ψ.comp (faceCM (delIdx i i' h.symm) 0), ?_, ?_⟩
  · have h1 : ψ' = degenOp (delIdx i' i h) (ψ.comp (faceCM (delIdx i i' h.symm) 0)) := by
      calc ψ' = (degenOp i' ψ').comp (faceCM i' 0) := (degenOp_comp_faceCM_self i' ψ' 0).symm
        _ = (degenOp i ψ).comp (faceCM i' 0) := by rw [← heq]
        _ = degenOp (delIdx i' i h) (ψ.comp (faceCM (delIdx i i' h.symm) 0)) :=
              degenOp_comp_faceCM (i := i) (j := i') (hij := h.symm) (χ := ψ) (b := 0)
    calc ψ = (degenOp i ψ).comp (faceCM i 0) := (degenOp_comp_faceCM_self i ψ 0).symm
      _ = (degenOp i' ψ').comp (faceCM i 0) := by rw [heq]
      _ = degenOp (delIdx i i' h.symm) (ψ'.comp (faceCM (delIdx i' i h) 0)) :=
            degenOp_comp_faceCM (i := i') (j := i) (hij := h) (χ := ψ') (b := 0)
      _ = degenOp (delIdx i i' h.symm) (ψ.comp (faceCM (delIdx i i' h.symm) 0)) := by
            rw [h1, degenOp_comp_faceCM_self]
  · calc ψ' = (degenOp i' ψ').comp (faceCM i' 0) := (degenOp_comp_faceCM_self i' ψ' 0).symm
      _ = (degenOp i ψ).comp (faceCM i' 0) := by rw [← heq]
      _ = degenOp (delIdx i' i h) (ψ.comp (faceCM (delIdx i i' h.symm) 0)) :=
            degenOp_comp_faceCM (i := i) (j := i') (hij := h.symm) (χ := ψ) (b := 0)


/-- The index of `i'` after deleting `i` (as a value), in the `delIdx` normal form. -/
theorem val_predG_eq_delIdx {m : ℕ} (i i' : Fin (m + 1)) (h : i ≠ i') :
    predG (Fin.castSucc i) (Fin.castSucc i') (castSucc_ne h.symm)
      = (Fin.castSucc (delIdx i i' h.symm) : Fin (m + 1)) := by
  have hL : ((predG (Fin.castSucc i) (Fin.castSucc i') (castSucc_ne h.symm) : Fin (m + 1)) : ℕ)
      = (if (i : ℕ) < (i' : ℕ) then (i' : ℕ) - 1 else (i' : ℕ)) := by
    rw [val_predG]
    simp only [Fin.val_castSucc]
  have hR : ((Fin.castSucc (delIdx i i' h.symm) : Fin (m + 1)) : ℕ)
      = (if (i : ℕ) < (i' : ℕ) then (i' : ℕ) - 1 else (i' : ℕ)) := by
    rw [Fin.val_castSucc, delIdx_val]
    split_ifs <;> omega
  exact Fin.ext (hL.trans hR.symm)

/-- **The double-degeneracy identity.**  Deleting two of the coordinates of `I^{m+2}` in the two
possible orders gives the same cube. -/
theorem degenOp_degenOp_swap {m : ℕ} (i i' : Fin (m + 1)) (h : i ≠ i') (η : C(IC m, X)) :
    degenOp (Fin.castSucc i) (degenOp (Fin.castSucc (delIdx i i' h.symm)) η)
      = degenOp (Fin.castSucc i') (degenOp (Fin.castSucc (delIdx i' i h)) η) := by
  have hcast : (Fin.castSucc i : Fin (m + 2)) ≠ Fin.castSucc i' := castSucc_ne h
  have e1 : predG (Fin.castSucc i) (Fin.castSucc i') hcast.symm
      = (Fin.castSucc (delIdx i i' h.symm) : Fin (m + 1)) :=
    val_predG_eq_delIdx i i' h
  have e2 : predG (Fin.castSucc i') (Fin.castSucc i) hcast
      = (Fin.castSucc (delIdx i' i h) : Fin (m + 1)) :=
    val_predG_eq_delIdx i' i h.symm
  have hD := delG_comp_eq (n := m) (Fin.castSucc i) (Fin.castSucc i') hcast
  rw [e1, e2] at hD
  simp only [degenOp]
  rw [ContinuousMap.comp_assoc, ContinuousMap.comp_assoc, hD]


/-! ## The tower -/

/-- **The value attached to a degenerate cube does not depend on its presentation.**  If
`degenOp a ψ = degenOp a' ψ'` then the degenerate extensions of the two fillings of `ψ` and `ψ'`
are the same cube. -/
theorem dcFill_congr {x₀ : X} {N : ℕ} (K : DCTower x₀ N) (L : ℕ) (hL : L ≤ N)
    {a a' : Fin (L + 1)} {ψ ψ' : C(IC L, X)} (h : degenOp a ψ = degenOp a' ψ') :
    degenOp (Fin.castSucc a) (K.Kf L ψ) = degenOp (Fin.castSucc a') (K.Kf L ψ') := by
  by_cases haa : a = a'
  · subst haa
    rw [degenOp_injective a h]
  · rcases Nat.eq_zero_or_pos L with hL0 | hLpos
    · subst hL0
      exact absurd (Fin.ext (by omega)) haa
    · obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, (Nat.succ_pred_eq_of_pos hLpos).symm⟩
      obtain ⟨χ, hψ, hψ'⟩ := exists_common_degenOp (n := L') haa h
      rw [hψ, hψ', K.hDC L' (by omega) (delIdx a a' (Ne.symm haa)) χ,
        K.hDC L' (by omega) (delIdx a' a haa) χ]
      exact degenOp_degenOp_swap a a' haa (K.Kf L' χ)

/-- The tower at level `0`: a path from `x₀` to each point, and the vacuous `hDC`. -/
theorem DCTower_zero (x₀ : X) (h0 : Subsingleton (HomotopyGroup (Fin 0) X x₀)) :
    Nonempty (DCTower x₀ 0) := by
  classical
  obtain ⟨K0, hα0, hγ0⟩ := exists_Kf_zero x₀ h0
  refine ⟨{ toTower :=
    { Kf := fun n => if h : n = 0 then h ▸ K0 else fun _ => cconst (n + 1) x₀,
      hα := ?_, hβ := ?_, hγ := ?_ }, hDC := ?_ }⟩
  · intro n hn p
    have hn0 : n = 0 := Nat.eq_zero_of_le_zero hn
    subst hn0
    dsimp only
    rw [dif_pos rfl]
    exact hα0 p
  · intro n hn
    exact absurd hn (Nat.not_succ_le_zero n)
  · intro n hn
    have hn0 : n = 0 := Nat.eq_zero_of_le_zero hn
    subst hn0
    dsimp only
    rw [dif_pos rfl]
    exact hγ0
  · intro m hm
    exact absurd hm (Nat.not_succ_le_zero m)

/-- **One level of the construction.**  From a `DCTower` at level `L` build one at level `L + 1`,
using the triviality of `π_{L+1}` for the cubes that are not degenerate and the degenerate
extension of the filling of the underlying cube for the ones that are. -/
theorem DCTower_succ (L : ℕ) (x₀ : X) (T : DCTower x₀ L)
    (htriv : Subsingleton (HomotopyGroup (Fin (L + 1)) X x₀)) :
    Nonempty (DCTower x₀ (L + 1)) := by
  classical
  have hper : ∀ p : C(IC (L + 1), X), ∃ F : C(IC (L + 2), X),
      (F.comp (faceCM (Fin.last (L + 1)) 1) = p ∧
        F.comp (faceCM (Fin.last (L + 1)) 0) = cconst (L + 1) x₀) ∧
      (∀ (j : Fin (L + 1)) (b : Fin 2),
        F.comp (faceCM (Fin.castSucc j) (cval b)) = T.Kf L (p.comp (faceCM j (cval b)))) := by
    intro p
    have hB : ∃ B : C(↥(Cube.boundary (Fin (L + 2))), X),
        B.comp (bface (L + 1) (Fin.last (L + 1)) 0) = cconst (L + 1) x₀ ∧
        B.comp (bface (L + 1) (Fin.last (L + 1)) 1) = p ∧
        (∀ (j : Fin (L + 1)) (b : Fin 2),
          B.comp (bface (L + 1) (Fin.castSucc j) b)
            = T.Kf L (p.comp (faceCM j (cval b)))) := by
      rcases Nat.eq_zero_or_pos L with h0 | hpos
      · subst h0
        obtain ⟨B, hBt, hBb, hBs⟩ := boundaryMapOne x₀ (T.Kf 0) p (fun q => T.hα 0 (by omega) q)
        exact ⟨B, hBb, hBt, hBs⟩
      · obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 :=
          ⟨L - 1, (Nat.succ_pred_eq_of_pos hpos).symm⟩
        have hβL : ∀ (q : C(IC (L' + 1), X)) (j : Fin (L' + 1)) (b : Fin 2),
            ((T.Kf (L' + 1)) q).comp (faceCM (Fin.castSucc j) (cval b))
              = (T.Kf L') (q.comp (faceCM j (cval b))) := by
          intro q j b
          have h := T.hβ L' (by omega) q j
          fin_cases b
          · simpa using h.1
          · simpa using h.2
        obtain ⟨B, hBt, hBb, hBs⟩ := boundaryMap (k := L') x₀ (T.Kf (L' + 1)) (T.Kf L') p
          (fun q => T.hα (L' + 1) (by omega) q) hβL
        exact ⟨B, hBb, hBt, hBs⟩
    obtain ⟨B, hBb, hBt, hBs⟩ := hB
    exact exists_level L x₀ (T.Kf L) htriv p B hBb hBt hBs
  choose F hF using hper
  -- the filling of a degenerate cube is the degenerate extension of the filling of the cube
  let newK : C(IC (L + 1), X) → C(IC (L + 2), X) := fun p =>
    if hp : ∃ (a : Fin (L + 1)) (ψ : C(IC L, X)), p = degenOp a ψ
    then degenOp (Fin.castSucc (Classical.choose hp))
      (T.Kf L (Classical.choose (Classical.choose_spec hp)))
    else F p
  have hDCnew : ∀ (j : Fin (L + 1)) (φ : C(IC L, X)),
      newK (degenOp j φ) = degenOp (Fin.castSucc j) (T.Kf L φ) := by
    intro j φ
    have hdeg : ∃ (a : Fin (L + 1)) (ψ : C(IC L, X)), degenOp j φ = degenOp a ψ :=
      ⟨j, φ, rfl⟩
    have hunf : newK (degenOp j φ) = degenOp (Fin.castSucc (Classical.choose hdeg))
        (T.Kf L (Classical.choose (Classical.choose_spec hdeg))) := by
      simp only [newK]
      rw [dif_pos hdeg]
    rw [hunf]
    exact dcFill_congr T L le_rfl (Classical.choose_spec (Classical.choose_spec hdeg)).symm
  have hnewα : ∀ p : C(IC (L + 1), X),
      (newK p).comp (faceCM (Fin.last (L + 1)) 1) = p ∧
      (newK p).comp (faceCM (Fin.last (L + 1)) 0) = cconst (L + 1) x₀ := by
    intro p
    by_cases hp : ∃ (a : Fin (L + 1)) (ψ : C(IC L, X)), p = degenOp a ψ
    · obtain ⟨a, ψ, rfl⟩ := hp
      rw [hDCnew a ψ, dcTower_last_face L a (T.Kf L ψ) 1,
        dcTower_last_face L a (T.Kf L ψ) 0, (T.hα L le_rfl ψ).1, (T.hα L le_rfl ψ).2,
        degenOp_cconst]
      exact ⟨rfl, rfl⟩
    · have hFn : newK p = F p := by simp only [newK]; rw [dif_neg hp]
      rw [hFn]
      exact (hF p).1
  have hnewβ : ∀ (p : C(IC (L + 1), X)) (j : Fin (L + 1)) (b : Fin 2),
      (newK p).comp (faceCM (Fin.castSucc j) (cval b))
        = T.Kf L (p.comp (faceCM j (cval b))) := by
    intro p j b
    by_cases hp : ∃ (a : Fin (L + 1)) (ψ : C(IC L, X)), p = degenOp a ψ
    · obtain ⟨a, ψ, rfl⟩ := hp
      rw [hDCnew a ψ]
      by_cases hja : j = a
      · subst hja
        rw [degenOp_comp_faceCM_self, degenOp_comp_faceCM_self]
      · have hja' : j ≠ a := hja
        have haj : a ≠ j := fun hh => hja hh.symm
        fin_cases b
        · simpa using dcTower_side_matched_zero (x₀ := x₀) T L le_rfl a j hja' haj ψ
        · simpa using dcTower_side_matched_one (x₀ := x₀) T L le_rfl a j hja' haj ψ
    · have hFn : newK p = F p := by simp only [newK]; rw [dif_neg hp]
      rw [hFn]
      exact (hF p).2 j b
  have hnewγ : newK (cconst (L + 1) x₀) = cconst (L + 2) x₀ := by
    rw [← degenOp_cconst L (0 : Fin (L + 1)) x₀, hDCnew 0 (cconst L x₀), T.hγ L le_rfl,
      degenOp_cconst]
  let Kf' : (n : ℕ) → C(IC n, X) → C(IC (n + 1), X) :=
    fun n => if hn : n ≤ L then T.Kf n
      else if h : n = L + 1 then h ▸ newK else fun _ => cconst (n + 1) x₀
  have hKf'_le : ∀ n, n ≤ L → Kf' n = T.Kf n := by
    intro n hn
    simp only [Kf']
    rw [dif_pos hn]
  have hKf'_new : Kf' (L + 1) = newK := by
    simp only [Kf']
    rw [dif_neg (by omega : ¬ L + 1 ≤ L)]
    simp
  refine ⟨{ toTower := { Kf := Kf', hα := ?_, hβ := ?_, hγ := ?_ }, hDC := ?_ }⟩
  · intro n hn p
    rcases Nat.lt_or_ge n (L + 1) with h1 | h1
    · rw [hKf'_le n (by omega)]
      exact T.hα n (by omega) p
    · have hn' : n = L + 1 := by omega
      subst n
      rw [hKf'_new]
      exact hnewα p
  · intro n hn p j
    rcases Nat.lt_or_ge n L with h1 | h1
    · have h2 : n + 1 ≤ L := by omega
      rw [hKf'_le (n + 1) h2, hKf'_le n (by omega)]
      exact T.hβ n (by omega) p j
    · have hn' : n = L := by omega
      subst n
      rw [hKf'_new, hKf'_le L le_rfl]
      exact ⟨hnewβ p j 0, hnewβ p j 1⟩
  · intro n hn
    rcases Nat.lt_or_ge n (L + 1) with h1 | h1
    · rw [hKf'_le n (by omega)]
      exact T.hγ n (by omega)
    · have hn' : n = L + 1 := by omega
      subst n
      rw [hKf'_new]
      exact hnewγ
  · intro m hm j φ
    rcases Nat.lt_or_ge m L with h1 | h1
    · rw [hKf'_le (m + 1) (by omega), hKf'_le m (by omega)]
      exact T.hDC m (by omega) j φ
    · have hm' : m = L := by omega
      subst m
      rw [hKf'_new, hKf'_le L le_rfl]
      exact hDCnew j φ

/-- **Existence of the degeneracy-compatible filling tower.** -/
theorem dcTowerExists (N : ℕ) (x₀ : X)
    (hconn : ∀ i : ℕ, i ≤ N → Subsingleton (HomotopyGroup (Fin i) X x₀)) :
    Nonempty (DCTower x₀ N) := by
  revert hconn
  induction N with
  | zero =>
      intro hconn
      exact DCTower_zero x₀ (hconn 0 le_rfl)
  | succ L ih =>
      intro hconn
      exact DCTower_succ L x₀ (ih (fun i hi => hconn i (by omega))).some (hconn (L + 1) le_rfl)

end

end Work.RatHurewicz.DCBuild
