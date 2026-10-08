import Mathlib
import Submission.Work.Hering.GL32.rad_defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Simplicity of the conjugation module on trace-zero `3 × 3` matrices over `F₂`

This is Appendix IX of Peterfalvi I: the space `M₄` of trace-zero `3 × 3` matrices over `F₂`
(an `8`-dimensional `F₂`-space) is a simple `F₂[GL(3,2)]`-module for the conjugation action
`A ↦ g A g⁻¹`, i.e. the only submodules are `0` and `M₄`.

## Proof

The unitriangular subgroup `P = ⟨t₁,t₂,t₃⟩` of `GL(3,2)` (order `8`) acts on `M₄` by conjugation,
and in characteristic `2` an involution on a nonzero module has a nonzero fixed vector.  Since
`t₃` is central and `t₁`, `t₂` commute modulo `t₃`, an iterated application of this fact produces
a nonzero `B ∈ W` fixed by all of `P`.  The centralizer of `P` inside the trace-zero matrices is
one-dimensional, spanned by `M20 = E_{2,0}` (a finite verification); hence `M20 ∈ W`.

Finally `W` contains the whole `GL(3,2)`-orbit of `M20`, and the orbit contains the eight explicit
matrices `M01, M10, M12, M21, M02, M20, EE01, EE02`, which span the trace-zero space.  Hence
`W = M₄`.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Work.Hering.GL32

/-! ## The eight matrices of the orbit of `M20`

For each of the eight generators of the trace-zero space we record an explicit invertible matrix
conjugating `M20` to it. -/

def P_M01 : Mat := ![![0,0,1],![1,0,0],![0,1,0]]
def Q_M01 : Mat := ![![0,1,0],![0,0,1],![1,0,0]]
def P_M10 : Mat := ![![1,0,0],![0,0,1],![0,1,0]]
def Q_M10 : Mat := ![![1,0,0],![0,0,1],![0,1,0]]
def P_M12 : Mat := ![![0,1,0],![0,0,1],![1,0,0]]
def Q_M12 : Mat := ![![0,0,1],![1,0,0],![0,1,0]]
def P_M21 : Mat := ![![0,1,0],![1,0,0],![0,0,1]]
def Q_M21 : Mat := ![![0,1,0],![1,0,0],![0,0,1]]
def P_M02 : Mat := ![![0,0,1],![0,1,0],![1,0,0]]
def Q_M02 : Mat := ![![0,0,1],![0,1,0],![1,0,0]]
def P_M20 : Mat := ![![1,0,0],![0,1,0],![0,0,1]]
def Q_M20 : Mat := ![![1,0,0],![0,1,0],![0,0,1]]
def P_EE01 : Mat := ![![1,0,1],![0,0,1],![0,1,0]]
def Q_EE01 : Mat := ![![1,1,0],![0,0,1],![0,1,0]]
def P_EE02 : Mat := ![![1,0,1],![0,1,0],![0,0,1]]
def Q_EE02 : Mat := ![![1,0,1],![0,1,0],![0,0,1]]

lemma QP_M01 : Q_M01 * P_M01 = 1 := by decide
lemma PQ_M01 : P_M01 * Q_M01 = 1 := by decide
lemma conj_M01 : P_M01 * M20 * Q_M01 = M01 := by decide

lemma QP_M10 : Q_M10 * P_M10 = 1 := by decide
lemma PQ_M10 : P_M10 * Q_M10 = 1 := by decide
lemma conj_M10 : P_M10 * M20 * Q_M10 = M10 := by decide

lemma QP_M12 : Q_M12 * P_M12 = 1 := by decide
lemma PQ_M12 : P_M12 * Q_M12 = 1 := by decide
lemma conj_M12 : P_M12 * M20 * Q_M12 = M12 := by decide

lemma QP_M21 : Q_M21 * P_M21 = 1 := by decide
lemma PQ_M21 : P_M21 * Q_M21 = 1 := by decide
lemma conj_M21 : P_M21 * M20 * Q_M21 = M21 := by decide

lemma QP_M02 : Q_M02 * P_M02 = 1 := by decide
lemma PQ_M02 : P_M02 * Q_M02 = 1 := by decide
lemma conj_M02 : P_M02 * M20 * Q_M02 = M02 := by decide

lemma QP_M20 : Q_M20 * P_M20 = 1 := by decide
lemma PQ_M20 : P_M20 * Q_M20 = 1 := by decide
lemma conj_M20 : P_M20 * M20 * Q_M20 = M20 := by decide

lemma QP_EE01 : Q_EE01 * P_EE01 = 1 := by decide
lemma PQ_EE01 : P_EE01 * Q_EE01 = 1 := by decide
lemma conj_EE01 : P_EE01 * M20 * Q_EE01 = EE01 := by decide

lemma QP_EE02 : Q_EE02 * P_EE02 = 1 := by decide
lemma PQ_EE02 : P_EE02 * Q_EE02 = 1 := by decide
lemma conj_EE02 : P_EE02 * M20 * Q_EE02 = EE02 := by decide

/-! ## The eight matrices span the trace-zero space -/

lemma tracezero_mem_span (A : Mat) (hA : A.trace = 0) :
    A ∈ Submodule.span (ZMod 2) (S : Set Mat) := by
  rw [tracezero_eq_combo A hA]
  repeat' apply Submodule.add_mem
  all_goals
    apply Submodule.smul_mem
    apply Submodule.subset_span
    simp [S]

/-! ## The conjugation action of the unitriangular subgroup -/

/-- `cEnd T1 T1` is an involution. -/
lemma cT1_sq : ∀ A : Mat, cEnd T1 T1 (cEnd T1 T1 A) = A := by decide

/-- `cEnd T2 T2` is an involution. -/
lemma cT2_sq : ∀ A : Mat, cEnd T2 T2 (cEnd T2 T2 A) = A := by decide

/-- `cEnd T3 T3` is an involution. -/
lemma cT3_sq : ∀ A : Mat, cEnd T3 T3 (cEnd T3 T3 A) = A := by decide

/-- `cEnd T3 T3` is `cEnd T1 T1`-equivariant (i.e. `T1` and `T3` commute). -/
lemma cT1_pres_T3 : ∀ A : Mat,
    cEnd T3 T3 A = A → cEnd T3 T3 (cEnd T1 T1 A) = cEnd T1 T1 A := by decide

/-- `cEnd T3 T3` is `cEnd T2 T2`-equivariant (i.e. `T2` and `T3` commute). -/
lemma cT2_pres_T3 : ∀ A : Mat,
    cEnd T3 T3 A = A → cEnd T3 T3 (cEnd T2 T2 A) = cEnd T2 T2 A := by decide

/-- On the fixed points of `cEnd T3 T3`, the maps `cEnd T1 T1` and `cEnd T2 T2` commute
(the commutator `[t₁,t₂]` is `t₃`). -/
lemma cT2_fix_T1 : ∀ A : Mat, cEnd T3 T3 A = A → cEnd T1 T1 A = A →
    cEnd T1 T1 (cEnd T2 T2 A) = cEnd T2 T2 A := by decide

/-- The centralizer of `⟨t₁,t₂,t₃⟩` inside the trace-zero matrices is spanned by
`M20 = E_{2,0}`. -/
lemma centralizer : ∀ A : Mat, cEnd T1 T1 A = A → cEnd T2 T2 A = A → cEnd T3 T3 A = A →
    A.trace = 0 → A = 0 ∨ A = M20 := by decide

/-! ## The main theorem -/

theorem rad_irreducible (W : Submodule (ZMod 2) (Matrix (Fin 3) (Fin 3) (ZMod 2)))
    (htr : ∀ A ∈ W, A.trace = 0)
    (hW : ∀ (g : GL32) (A : Matrix (Fin 3) (Fin 3) (ZMod 2)), A ∈ W →
      (LinearMap.toMatrix' (g : (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2))) * A *
        (LinearMap.toMatrix' (g.symm : (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2))) ∈ W) :
    W = ⊥ ∨ ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2), A.trace = 0 → A ∈ W := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  -- `W` is preserved by conjugation by the three involutions `t₁, t₂, t₃`.
  have hW1 : ∀ B ∈ W, cEnd T1 T1 B ∈ W := by
    intro B hB
    have h := hW t1 B hB
    rw [toMatrix'_t1, toMatrix'_t1_symm] at h
    exact h
  have hW2 : ∀ B ∈ W, cEnd T2 T2 B ∈ W := by
    intro B hB
    have h := hW t2 B hB
    rw [toMatrix'_t2, toMatrix'_t2_symm] at h
    exact h
  have hW3 : ∀ B ∈ W, cEnd T3 T3 B ∈ W := by
    intro B hB
    have h := hW t3 B hB
    rw [toMatrix'_t3, toMatrix'_t3_symm] at h
    exact h
  -- Three-step descent to a nonzero `P`-fixed element of `W`.
  have hU1 : fixSub T3 T3 W ≠ ⊥ := fixSub_ne_bot cT3_sq hbot hW3
  have hmap1 : ∀ B ∈ fixSub T3 T3 W, cEnd T1 T1 B ∈ fixSub T3 T3 W :=
    map_fixSub_of (P := T3) (Q := T3) (P' := T1) (Q' := T1) (W := W) hW1
      (fun B _ hB => cT1_pres_T3 B hB)
  have hU2 : fixSub T1 T1 (fixSub T3 T3 W) ≠ ⊥ := fixSub_ne_bot cT1_sq hU1 hmap1
  have hmap2inner : ∀ B ∈ fixSub T3 T3 W, cEnd T2 T2 B ∈ fixSub T3 T3 W :=
    map_fixSub_of (P := T3) (Q := T3) (P' := T2) (Q' := T2) (W := W) hW2
      (fun B _ hB => cT2_pres_T3 B hB)
  have hmap2 : ∀ B ∈ fixSub T1 T1 (fixSub T3 T3 W),
      cEnd T2 T2 B ∈ fixSub T1 T1 (fixSub T3 T3 W) :=
    map_fixSub_of (P := T1) (Q := T1) (P' := T2) (Q' := T2)
      (W := fixSub T3 T3 W) hmap2inner
      (fun B hB hBfix => cT2_fix_T1 B (mem_fixSub.mp hB).2 hBfix)
  obtain ⟨B, hB, hBne, hBfix2⟩ :=
    exists_fixed_of_sq (cEnd T2 T2) cT2_sq (fixSub T1 T1 (fixSub T3 T3 W)) hU2 hmap2
  obtain ⟨hB2, hBfix1⟩ := mem_fixSub.mp hB
  obtain ⟨hB0, hBfix0⟩ := mem_fixSub.mp hB2
  -- `B` is a nonzero element of the centralizer of `P` inside the trace-zero matrices.
  have hBtr : B.trace = 0 := htr B hB0
  have hM20 : M20 ∈ W := by
    rcases centralizer B hBfix1 hBfix2 hBfix0 hBtr with h | h
    · exact absurd h hBne
    · rw [← h]; exact hB0
  -- The eight generators of the trace-zero space are conjugates of `M20`, hence lie in `W`.
  have hmem01 : M01 ∈ W := by
    have h := hW (mkGL P_M01 Q_M01 QP_M01 PQ_M01) M20 hM20
    rw [toMatrix'_mkGL P_M01 Q_M01 QP_M01 PQ_M01,
      toMatrix'_mkGL_symm P_M01 Q_M01 QP_M01 PQ_M01, conj_M01] at h
    exact h
  have hmem10 : M10 ∈ W := by
    have h := hW (mkGL P_M10 Q_M10 QP_M10 PQ_M10) M20 hM20
    rw [toMatrix'_mkGL P_M10 Q_M10 QP_M10 PQ_M10,
      toMatrix'_mkGL_symm P_M10 Q_M10 QP_M10 PQ_M10, conj_M10] at h
    exact h
  have hmem12 : M12 ∈ W := by
    have h := hW (mkGL P_M12 Q_M12 QP_M12 PQ_M12) M20 hM20
    rw [toMatrix'_mkGL P_M12 Q_M12 QP_M12 PQ_M12,
      toMatrix'_mkGL_symm P_M12 Q_M12 QP_M12 PQ_M12, conj_M12] at h
    exact h
  have hmem21 : M21 ∈ W := by
    have h := hW (mkGL P_M21 Q_M21 QP_M21 PQ_M21) M20 hM20
    rw [toMatrix'_mkGL P_M21 Q_M21 QP_M21 PQ_M21,
      toMatrix'_mkGL_symm P_M21 Q_M21 QP_M21 PQ_M21, conj_M21] at h
    exact h
  have hmem02 : M02 ∈ W := by
    have h := hW (mkGL P_M02 Q_M02 QP_M02 PQ_M02) M20 hM20
    rw [toMatrix'_mkGL P_M02 Q_M02 QP_M02 PQ_M02,
      toMatrix'_mkGL_symm P_M02 Q_M02 QP_M02 PQ_M02, conj_M02] at h
    exact h
  have hmem20 : M20 ∈ W := hM20
  have hmemEE01 : EE01 ∈ W := by
    have h := hW (mkGL P_EE01 Q_EE01 QP_EE01 PQ_EE01) M20 hM20
    rw [toMatrix'_mkGL P_EE01 Q_EE01 QP_EE01 PQ_EE01,
      toMatrix'_mkGL_symm P_EE01 Q_EE01 QP_EE01 PQ_EE01, conj_EE01] at h
    exact h
  have hmemEE02 : EE02 ∈ W := by
    have h := hW (mkGL P_EE02 Q_EE02 QP_EE02 PQ_EE02) M20 hM20
    rw [toMatrix'_mkGL P_EE02 Q_EE02 QP_EE02 PQ_EE02,
      toMatrix'_mkGL_symm P_EE02 Q_EE02 QP_EE02 PQ_EE02, conj_EE02] at h
    exact h
  -- Every trace-zero matrix lies in the span of these eight, hence in `W`.
  have hSW : S ⊆ W := by
    intro x hx
    simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hmem01, hmem10, hmem12, hmem21, hmem02, hmem20, hmemEE01, hmemEE02]
  intro A hA
  exact Submodule.span_le.mpr hSW (tracezero_mem_span A hA)

end Work.Hering.GL32
