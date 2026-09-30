import Mathlib
import Submission.Work.RatHurewicz.Bridge.Defs

/-!
# The faces of the cumulative-coordinate map `H`

The comparison `σ ↦ σ ∘ H n` between the singular *simplicial* and the singular *cubical* chains is
a chain map modulo degenerate cubes because of the two face relations of the cumulative-coordinate
map `H n : I^n → Δ^n`, `(H n t) j = (∏_{i<j} t_i)·(1 - t_j)`:

* `H_face_one` : the face `t_k = 1` is the coface `k` applied to `H (n-1)`;
* `H_face_last_zero` : the face `t_m = 0` is the last coface applied to `H m`;
* `H_face_zero_mem_Deg` : the other faces `t_k = 0` (`k < m`) are degenerate cubes.

These are the inputs of the chain-map property `Bridge.sim_chainMap_gen`.
-/

open scoped unitInterval Topology Simplicial
open CategoryTheory AlgebraicTopology
open Work.Stems.Cubical

namespace Work.RatHurewicz.Bridge

noncomputable section

/-- The coercion of `1 : unitInterval` to `ℝ`. -/
@[simp] theorem coe_unitInterval_one : ((1 : unitInterval) : ℝ) = 1 := rfl

/-- The coercion of `0 : unitInterval` to `ℝ`. -/
@[simp] theorem coe_unitInterval_zero : ((0 : unitInterval) : ℝ) = 0 := rfl

/-! ## Coordinates -/

/-- The coordinates of the face of a cube. -/
theorem tval_faceCM (m : ℕ) (k : Fin (m + 1)) (b : unitInterval) (t : IC m) (l : ℕ) :
    tval (m + 1) (faceCM k b t) l =
      if l = k.val then (b : ℝ) else if l < k.val then tval m t l else tval m t (l - 1) := by
  rcases lt_or_ge l (m + 1) with hl | hl
  · rw [tval_of_lt _ hl]
    by_cases h1 : l = k.val
    · rw [if_pos h1]
      have hk : (⟨l, hl⟩ : Fin (m + 1)) = k := Fin.ext h1
      rw [hk]
      have hb : (faceCM k b t) k = b := by
        simp only [faceCM_apply, faceFun_apply, Fin.succAbove_cases_eq_insertNth]
        exact Fin.insertNth_apply_same (α := fun _ => unitInterval) k b t
      rw [hb]
    · rw [if_neg h1]
      by_cases h2 : l < k.val
      · rw [if_pos h2]
        have hj : l < m := by omega
        have hsucc : k.succAbove (⟨l, hj⟩ : Fin m) = (⟨l, hl⟩ : Fin (m + 1)) := by
          rw [Fin.succAbove_of_castSucc_lt k ⟨l, hj⟩
            (by simp only [Fin.lt_def, Fin.val_castSucc]; omega)]
          exact Fin.ext rfl
        rw [tval_of_lt _ hj]
        conv_lhs => rw [← hsucc]
        rw [faceCM_apply, faceFun_apply, Fin.succAbove_cases_eq_insertNth,
          Fin.insertNth_apply_succAbove]
      · rw [if_neg h2]
        have hlk : k.val < l := by omega
        have hjm : l - 1 < m := by omega
        have hsucc : k.succAbove (⟨l - 1, hjm⟩ : Fin m) = (⟨l, hl⟩ : Fin (m + 1)) := by
          rw [Fin.succAbove_of_le_castSucc k ⟨l - 1, hjm⟩
            (by simp only [Fin.le_def, Fin.val_castSucc]; omega)]
          exact Fin.ext (by simp only [Fin.val_succ]; omega)
        rw [tval_of_lt _ hjm]
        conv_lhs => rw [← hsucc]
        rw [faceCM_apply, faceFun_apply, Fin.succAbove_cases_eq_insertNth,
          Fin.insertNth_apply_succAbove]
  · have h0 : tval (m + 1) (faceCM k b t) l = 0 := tval_of_le _ (by omega)
    have h1 : ¬ l = k.val := by omega
    have h2 : ¬ l < k.val := by omega
    have h3 : tval m t (l - 1) = 0 := tval_of_le _ (by omega)
    rw [h0, if_neg h1, if_neg h2, h3]

/-- The partial products of the face of a cube. -/
theorem Pnat_faceCM (m : ℕ) (k : Fin (m + 1)) (b : unitInterval) (t : IC m) (L : ℕ) :
    Pnat (m + 1) (faceCM k b t) L =
      if L ≤ k.val then Pnat m t L else (b : ℝ) * Pnat m t (L - 1) := by
  induction L with
  | zero => simp [Pnat]
  | succ L ih =>
    rw [Pnat_succ, ih]
    by_cases hL : L + 1 ≤ k.val
    · have hL' : L ≤ k.val := by omega
      rw [if_pos hL, if_pos hL']
      have ht : tval (m + 1) (faceCM k b t) L = tval m t L := by
        rw [tval_faceCM]
        rw [if_neg (by omega : ¬ L = k.val), if_pos (by omega : L < k.val)]
      rw [ht, Pnat_succ]
    · rw [if_neg hL]
      by_cases hLk : L = k.val
      · subst hLk
        rw [if_pos (le_refl _)]
        have hb : tval (m + 1) (faceCM k b t) k.val = (b : ℝ) := by
          rw [tval_faceCM, if_pos rfl]
        rw [hb]
        have : k.val + 1 - 1 = k.val := by omega
        rw [this]
        ring
      · have hLk' : k.val < L := by omega
        rw [if_neg (by omega : ¬ L ≤ k.val)]
        have ht : tval (m + 1) (faceCM k b t) L = tval m t (L - 1) := by
          rw [tval_faceCM]
          rw [if_neg hLk, if_neg (by omega : ¬ L < k.val)]
        rw [ht, mul_assoc, ← Pnat_succ]
        rw [show L - 1 + 1 = L + 1 - 1 by omega]

/-- The coordinates of the coface `Δⁿ → Δⁿ⁺¹` given by `p.castSucc.succAbove`. -/
theorem stdSimplex_map_castSucc_succAbove_apply {n : ℕ} (p : Fin n)
    (z : stdSimplex ℝ (Fin n)) (j : Fin (n + 1)) :
    (stdSimplex.map p.castSucc.succAbove z) j =
      if j = p.castSucc then 0 else z (p.predAbove j) := by
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply, Finset.sum_filter]
  by_cases h : j = p.castSucc
  · rw [if_pos h]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [if_neg]
    rintro hx
    exact Fin.succAbove_ne p.castSucc x (h ▸ hx)
  · rw [if_neg h]
    rw [Finset.sum_eq_single (p.predAbove j) ?_ ?_]
    · rw [if_pos (Fin.succAbove_predAbove h)]
    · intro b _ hb
      rw [if_neg]
      intro hbx
      refine hb (Fin.succAbove_right_injective (p := p.castSucc) ?_)
      rw [hbx, Fin.succAbove_predAbove h]
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem

/-- The coordinates of the last coface `Δⁿ → Δⁿ⁺¹` (a zero inserted at the end). -/
theorem stdSimplex_map_castSucc_apply {n : ℕ} (z : stdSimplex ℝ (Fin n)) (j : Fin (n + 1)) :
    (stdSimplex.map (Fin.castSucc : Fin n → Fin (n + 1)) z) j =
      if h : j = Fin.last n then 0 else z (j.castPred h) := by
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply, Finset.sum_filter]
  by_cases h : j = Fin.last n
  · rw [dif_pos h]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [if_neg]
    rintro hx
    have hv : (x : ℕ) = n := by
      have h1 := congrArg Fin.val hx
      simp only [Fin.val_castSucc] at h1
      rw [h1, h, Fin.val_last]
    omega
  · rw [dif_neg h]
    rw [Finset.sum_eq_single (j.castPred h) ?_ ?_]
    · rw [if_pos]
      exact Fin.ext (Fin.coe_castPred j h)
    · intro b _ hb
      rw [if_neg]
      intro hbx
      have h1 : (b : ℕ) = (j : ℕ) := by
        have := congrArg Fin.val hbx
        simpa using this
      have h2 : (j.castPred h : ℕ) = (j : ℕ) := Fin.coe_castPred j h
      exact hb (Fin.ext (by omega))
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem

/-- `Pnat` vanishes beyond the dimension of the cube. -/
theorem Pnat_eq_zero {n L : ℕ} (t : IC n) (h : n < L) : Pnat n t L = 0 := by
  refine Finset.prod_eq_zero (Finset.mem_range.mpr h) ?_
  exact tval_of_le t (by omega)

/-- Two points agreeing away from the last coordinate have the same `Pnat` along the faces
`t_k = 0`, `k < m`. -/
theorem Pnat_faceCM_zero_agree (m : ℕ) (k : Fin (m + 1)) (hk : k.val < m) {t t' : IC m}
    (ht : ∀ j : Fin m, j ≠ (⟨m - 1, by omega⟩ : Fin m) → t j = t' j) (L : ℕ) :
    Pnat (m + 1) (faceCM k 0 t) L = Pnat (m + 1) (faceCM k 0 t') L := by
  rw [Pnat_faceCM, Pnat_faceCM]
  by_cases h : L ≤ k.val
  · rw [if_pos h, if_pos h]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hiL : i < L := Finset.mem_range.mp hi
    have him : i < m := by omega
    have hne : (⟨i, him⟩ : Fin m) ≠ (⟨m - 1, by omega⟩ : Fin m) := by
      intro hc; rw [Fin.ext_iff] at hc; simp only at hc; omega
    rw [tval_of_lt _ him, tval_of_lt _ him, ht ⟨i, him⟩ hne]
  · rw [if_neg h, if_neg h, coe_unitInterval_zero, zero_mul, zero_mul]

/-! ## The three face relations -/

/-- The face `t_k = 1` of `H (m+1)` is the coface `k` applied to `H m`. -/
theorem H_face_one (m : ℕ) (k : Fin (m + 1)) :
    (H (m + 1)).comp (faceCM k 1) = (coface m (Fin.castSucc k)).comp (H m) := by
  ext t j
  rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply, coface_apply,
    stdSimplex_map_castSucc_succAbove_apply k (H m t) j, H_apply, H_apply, Hfun_eq, Hfun_eq]
  rcases lt_trichotomy j.val k.val with hlt | heq | hgt
  · have hj : j.val < m + 1 := by omega
    have h1 : j.val ≤ k.val := by omega
    have h2 : j.val + 1 ≤ k.val := by omega
    have h3 : ¬ (j = k.castSucc) := by
      intro h; rw [Fin.ext_iff] at h; simp only [Fin.val_castSucc] at h; omega
    rw [Pnat_faceCM, Pnat_faceCM, if_pos h1, if_pos h2, if_neg h3]
    have hcast : k.predAbove j = (⟨j.val, hj⟩ : Fin (m + 1)) := by
      rw [Fin.predAbove_of_le_castSucc k j (by simp only [Fin.le_def, Fin.val_castSucc]; omega)]
      exact Fin.ext (Fin.coe_castPred j _)
    rw [hcast]
  · have h1 : j.val ≤ k.val := by omega
    have h2 : ¬ j.val + 1 ≤ k.val := by omega
    have h3 : j = k.castSucc := by
      apply Fin.ext; simp only [Fin.val_castSucc]; omega
    rw [Pnat_faceCM, Pnat_faceCM, if_pos h1, if_neg h2, if_pos h3]
    rw [coe_unitInterval_one, one_mul]
    have hz : j.val + 1 - 1 = j.val := by omega
    simp only [hz, sub_self]
  · have h1 : ¬ j.val ≤ k.val := by omega
    have h2 : ¬ j.val + 1 ≤ k.val := by omega
    have h3 : ¬ (j = k.castSucc) := by
      intro h; rw [Fin.ext_iff] at h; simp only [Fin.val_castSucc] at h; omega
    rw [Pnat_faceCM, Pnat_faceCM, if_neg h1, if_neg h2, if_neg h3]
    rw [coe_unitInterval_one, one_mul, one_mul]
    have hj : j.val - 1 < m + 1 := by omega
    have hz : j.val + 1 - 1 = j.val - 1 + 1 := by omega
    rw [hz]
    have hcast : k.predAbove j = (⟨j.val - 1, hj⟩ : Fin (m + 1)) := by
      rw [Fin.predAbove_of_castSucc_lt k j (by simp only [Fin.lt_def, Fin.val_castSucc]; omega)]
      exact Fin.ext (by simp only [Fin.val_pred])
    rw [hcast]

/-- The face `t_m = 0` of `H (m+1)` is the last coface applied to `H m`. -/
theorem H_face_last_zero (m : ℕ) :
    (H (m + 1)).comp (faceCM (Fin.last m) 0)
      = (coface m (Fin.last (m + 1))).comp (H m) := by
  ext t j
  rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply, coface_apply, Fin.succAbove_last,
    stdSimplex_map_castSucc_apply, H_apply, Hfun_eq]
  by_cases hJ : j = Fin.last (m + 1)
  · rw [dif_pos hJ]
    have h1 : ¬ j.val ≤ (Fin.last m).val := by
      rw [Fin.val_last, hJ, Fin.val_last]; omega
    have h2 : ¬ j.val + 1 ≤ (Fin.last m).val := by
      rw [Fin.val_last, hJ, Fin.val_last]; omega
    rw [Pnat_faceCM, Pnat_faceCM, if_neg h1, if_neg h2, coe_unitInterval_zero, zero_mul,
      zero_mul, sub_zero]
  · rw [dif_neg hJ, H_apply, Hfun_eq]
    have hj : j.val < m + 1 := by
      rw [Fin.ext_iff] at hJ; simp only [Fin.val_last] at hJ; omega
    have hcast : j.castPred hJ = (⟨j.val, hj⟩ : Fin (m + 1)) :=
      Fin.ext (Fin.coe_castPred j hJ)
    rw [hcast, Pnat_faceCM, Pnat_faceCM]
    have h1 : j.val ≤ (Fin.last m).val := by simp only [Fin.val_last]; omega
    rw [if_pos h1]
    by_cases h4 : j.val + 1 ≤ (Fin.last m).val
    · rw [if_pos h4]
    · rw [if_neg h4]
      have h5 : m < j.val + 1 := by simp only [Fin.val_last] at h4 ⊢; omega
      rw [coe_unitInterval_zero, zero_mul, Pnat_eq_zero t h5]

/-- The faces `t_k = 0`, `k < m`, of `H (m+1)` are degenerate cubes. -/
theorem H_face_zero_mem_Deg (m : ℕ) (k : Fin (m + 1)) (hk : k.val < m) :
    Finsupp.single ((H (m + 1)).comp (faceCM k 0)) (1 : ℤ)
      ∈ Deg m (stdSimplex ℝ (Fin (m + 2))) := by
  have hm : 0 < m := by omega
  refine Deg_of_indep (⟨m - 1, by omega⟩ : Fin m) ?_
  intro t t' ht
  ext j
  rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply, H_apply, H_apply, Hfun_eq, Hfun_eq]
  congr 1
  · exact Pnat_faceCM_zero_agree m k hk ht j.val
  · exact Pnat_faceCM_zero_agree m k hk ht (j.val + 1)

end

end Work.RatHurewicz.Bridge
