import Submission.Work.RouteB.OpSOS
import Submission.Work.RouteB.SimplexTrans
import Submission.Commons.GroupTheory.GroupAction.sum_smul_card_smul

open OnPropertyT Submission.FreeGroupAut Submission.Helpers
open scoped BigOperators

set_option autoImplicit false

/-!
# The counting identities of the symmetrisation (the paper's `delta comp`,
`Adj comp`, `Op comp`)

Averaging `permRingHom σ (X)` over all permutations `σ ∈ S_m` replaces each
summand indexed by the sub-simplex on the first `n` vertices by the
corresponding summand of the full simplex, the average being a scalar multiple
of the full sum with scalar the ratio of the numbers of constituent blocks.  The
engine is the orbit-sum lemma `sum_smul_eq_div_card_smul`.

The paper uses the alternating group `A_m`; the argument only uses transitivity
of the permutation action on edges, adjacent pairs and opposite pairs, and the
full symmetric group is transitive on each (`exists_smul_eq_edge`,
`exists_smul_eq_adjPair`, `exists_smul_eq_opPair`), so we use `S_m`, which
avoids all parity bookkeeping (the paper's exceptional treatment of `A_4`).
-/

namespace Submission.RouteB

namespace Edge

variable {m : ℕ}

local notation "Sm" => Equiv.Perm (Fin m)

/-- The sub-simplex version of `Sq_n`. -/
noncomputable def SqPair (m r : ℕ) : MonoidAlgebra ℝ (MulAut (FreeGroup (Fin m))) :=
  ∑ x ∈ Dsub m r, edgeLap x.1 * edgeLap x.2

/-- The sub-simplex version of `Adj_n`. -/
noncomputable def AdjPair (m r : ℕ) : MonoidAlgebra ℝ (MulAut (FreeGroup (Fin m))) :=
  ∑ x ∈ Psub m r, edgeLap x.1 * edgeLap x.2

/-- The sub-simplex version of `Op_n`. -/
noncomputable def OpPair (m r : ℕ) : MonoidAlgebra ℝ (MulAut (FreeGroup (Fin m))) :=
  ∑ x ∈ Qsub m r, edgeLap x.1 * edgeLap x.2

@[simp] lemma SqPair_self (m : ℕ) : SqPair m m = SqLap m := rfl
@[simp] lemma AdjPair_self (m : ℕ) : AdjPair m m = AdjLap m := rfl
@[simp] lemma OpPair_self (m : ℕ) : OpPair m m = OpLap m := rfl

/-! ## The orbit-sum engine -/

open scoped Classical in
/-- **Orbit sum with a real scalar.**  For an orbit block `T` of `x`,
`∑_σ f (σ • x) = (|G| / |T|) • ∑_{y ∈ T} f y`. -/
lemma sum_smul_eq_div_card_smul' {X : Type*} [MulAction Sm X] [DecidableEq X]
    (f : X → MonoidAlgebra ℝ (MulAut (FreeGroup (Fin m)))) (x : X) (T : Finset X)
    (hmem : ∀ σ : Sm, σ • x ∈ T) (hsurj : ∀ y ∈ T, ∃ σ : Sm, σ • x = y) (hT : T.card ≠ 0) :
    (∑ σ : Sm, f (σ • x)) = ((Fintype.card Sm : ℝ) / (T.card : ℝ)) • ∑ y ∈ T, f y := by
  classical
  have h := Commons.GroupTheory.GroupAction.sum_smul_card_smul f x T hmem hsurj
  rw [← Nat.cast_smul_eq_nsmul ℝ T.card (∑ σ : Sm, f (σ • x)),
    ← Nat.cast_smul_eq_nsmul ℝ (Fintype.card Sm) (∑ y ∈ T, f y)] at h
  have hcast : (T.card : ℝ) ≠ 0 := by exact_mod_cast hT
  calc (∑ σ : Sm, f (σ • x))
      = ((T.card : ℝ)⁻¹ * (T.card : ℝ)) • (∑ σ : Sm, f (σ • x)) := by
          rw [inv_mul_cancel₀ hcast, one_smul]
    _ = (T.card : ℝ)⁻¹ • ((T.card : ℝ) • (∑ σ : Sm, f (σ • x))) := by rw [smul_smul]
    _ = (T.card : ℝ)⁻¹ • ((Fintype.card Sm : ℝ) • ∑ y ∈ T, f y) := by rw [h]
    _ = ((Fintype.card Sm : ℝ) / (T.card : ℝ)) • ∑ y ∈ T, f y := by
          rw [smul_smul, div_eq_mul_inv, mul_comm]

/-- **Counting identity for a family of edges.** -/
theorem sum_permRingHom_edgeSum {S T : Finset (Edge m)} (hT : T.card ≠ 0)
    (hmem : ∀ x ∈ S, ∀ σ : Sm, σ • x ∈ T)
    (hsurj : ∀ x ∈ S, ∀ y ∈ T, ∃ σ : Sm, σ • x = y) :
    (∑ σ : Sm, permRingHom σ (∑ x ∈ S, edgeLap x))
      = ((S.card : ℝ) * ((Fintype.card Sm : ℝ) / (T.card : ℝ))) • (∑ y ∈ T, edgeLap y) := by
  classical
  have h1 : ∀ σ : Sm, permRingHom σ (∑ x ∈ S, edgeLap x)
      = ∑ x ∈ S, edgeLap (σ • x) := by
    intro σ
    rw [map_sum]
    exact Finset.sum_congr rfl (fun x _ => permRingHom_edgeLap σ x)
  rw [Finset.sum_congr rfl (fun σ _ => h1 σ), Finset.sum_comm]
  have h2 : ∀ x ∈ S, (∑ σ : Sm, edgeLap (σ • x))
      = ((Fintype.card Sm : ℝ) / (T.card : ℝ)) • (∑ y ∈ T, edgeLap y) :=
    fun x hx => sum_smul_eq_div_card_smul' (fun y : Edge m => edgeLap y) x T
      (hmem x hx) (hsurj x hx) hT
  rw [Finset.sum_congr rfl (fun x hx => h2 x hx), Finset.sum_const]
  rw [← Nat.cast_smul_eq_nsmul ℝ S.card, smul_smul]

/-- **Counting identity for a family of ordered pairs of edges.** -/
theorem sum_permRingHom_pairSum {S T : Finset (Edge m × Edge m)} (hT : T.card ≠ 0)
    (hmem : ∀ x ∈ S, ∀ σ : Sm, σ • x ∈ T)
    (hsurj : ∀ x ∈ S, ∀ y ∈ T, ∃ σ : Sm, σ • x = y) :
    (∑ σ : Sm, permRingHom σ (∑ x ∈ S, edgeLap x.1 * edgeLap x.2))
      = ((S.card : ℝ) * ((Fintype.card Sm : ℝ) / (T.card : ℝ)))
          • (∑ y ∈ T, edgeLap y.1 * edgeLap y.2) := by
  classical
  have h1 : ∀ σ : Sm, permRingHom σ (∑ x ∈ S, edgeLap x.1 * edgeLap x.2)
      = ∑ x ∈ S, edgeLap (σ • x).1 * edgeLap (σ • x).2 := by
    intro σ
    rw [map_sum]
    exact Finset.sum_congr rfl (fun x _ => by
      rw [map_mul, permRingHom_edgeLap, permRingHom_edgeLap, Prod.smul_fst, Prod.smul_snd])
  rw [Finset.sum_congr rfl (fun σ _ => h1 σ), Finset.sum_comm]
  have h2 : ∀ x ∈ S, (∑ σ : Sm, edgeLap (σ • x).1 * edgeLap (σ • x).2)
      = ((Fintype.card Sm : ℝ) / (T.card : ℝ)) • (∑ y ∈ T, edgeLap y.1 * edgeLap y.2) :=
    fun x hx => sum_smul_eq_div_card_smul' (fun y : Edge m × Edge m => edgeLap y.1 * edgeLap y.2) x T
      (hmem x hx) (hsurj x hx) hT
  rw [Finset.sum_congr rfl (fun x hx => h2 x hx), Finset.sum_const]
  rw [← Nat.cast_smul_eq_nsmul ℝ S.card, smul_smul]

/-! ## The four counting identities -/

/-- There is at least one edge as soon as `2 ≤ m`. -/
lemma Esub_univ_card_ne_zero {m : ℕ} (hm : 2 ≤ m) : (Esub m m).card ≠ 0 := by
  rw [Esub_self]
  refine Finset.card_ne_zero.mpr ⟨edgeOf ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp), Finset.mem_univ _⟩

/-- The scalar of the counting identity for `Δ`. -/
noncomputable def cDelta (m n : ℕ) : ℝ :=
  ((Esub m n).card : ℝ) * ((Fintype.card (Equiv.Perm (Fin m)) : ℝ) / ((Esub m m).card : ℝ))

/-- The scalar of the counting identity for `Sq`. -/
noncomputable def cSq (m n : ℕ) : ℝ :=
  ((Dsub m n).card : ℝ) * ((Fintype.card (Equiv.Perm (Fin m)) : ℝ) / ((Dsub m m).card : ℝ))

/-- The scalar of the counting identity for `Adj`. -/
noncomputable def cAdj (m n : ℕ) : ℝ :=
  ((Psub m n).card : ℝ) * ((Fintype.card (Equiv.Perm (Fin m)) : ℝ) / ((Psub m m).card : ℝ))

/-- The scalar of the counting identity for `Op`. -/
noncomputable def cOp (m n : ℕ) : ℝ :=
  ((Qsub m n).card : ℝ) * ((Fintype.card (Equiv.Perm (Fin m)) : ℝ) / ((Qsub m m).card : ℝ))

/-- **The paper's `delta comp`**: the `S_m`-average of `Δ_n` is `cDelta • Δ_m`. -/
theorem sum_permRingHom_deltaSub (m n : ℕ) (hm : 2 ≤ m) :
    (∑ σ : Equiv.Perm (Fin m), permRingHom σ (deltaSub m n)) = cDelta m n • deltaSub m m := by
  classical
  rw [show deltaSub m n = ∑ p ∈ Esub m n, edgeLap p from deltaSub_eq_sum m n,
    show deltaSub m m = ∑ p ∈ Esub m m, edgeLap p from deltaSub_eq_sum m m]
  have hT : (Esub m m).card ≠ 0 := Esub_univ_card_ne_zero hm
  rw [sum_permRingHom_edgeSum (S := Esub m n) (T := Esub m m) hT
    (fun x _ σ => by rw [Esub_self]; exact Finset.mem_univ _)
    (fun x _ y _ => exists_smul_eq_edge x y), cDelta]

theorem sum_permRingHom_SqPair (m n : ℕ) (hm : 2 ≤ m) :
    (∑ σ : Equiv.Perm (Fin m), permRingHom σ (SqPair m n)) = cSq m n • SqLap m := by
  classical
  rw [show SqPair m n = ∑ x ∈ Dsub m n, edgeLap x.1 * edgeLap x.2 from rfl,
    show SqLap m = ∑ x ∈ Dsub m m, edgeLap x.1 * edgeLap x.2 from rfl]
  have hT : (Dsub m m).card ≠ 0 := by
    rw [card_Dsub]
    exact (card_Esub_pos (by omega) le_rfl).ne'
  refine (sum_permRingHom_pairSum (S := Dsub m n) (T := Dsub m m) hT ?_ ?_).trans ?_
  · intro x hx σ
    rw [mem_Dsub] at hx
    rw [mem_Dsub, Prod.smul_fst, Prod.smul_snd, hx.1]
    exact ⟨rfl, by rw [Esub_self]; exact Finset.mem_univ _⟩
  · intro x hx y hy
    rw [mem_Dsub] at hx hy
    obtain ⟨σ, hσ⟩ := exists_smul_eq_edge x.1 y.1
    exact ⟨σ, Prod.ext (by rw [Prod.smul_fst, hσ])
      (by rw [Prod.smul_snd, ← hx.1, hσ, hy.1])⟩
  · rw [cSq]

theorem sum_permRingHom_AdjPair (m n : ℕ) (hm : 3 ≤ m) :
    (∑ σ : Equiv.Perm (Fin m), permRingHom σ (AdjPair m n)) = cAdj m n • AdjLap m := by
  classical
  rw [show AdjPair m n = ∑ x ∈ Psub m n, edgeLap x.1 * edgeLap x.2 from rfl,
    show AdjLap m = ∑ x ∈ Psub m m, edgeLap x.1 * edgeLap x.2 from rfl]
  have hT : (Psub m m).card ≠ 0 := (card_Psub_pos hm).ne'
  refine (sum_permRingHom_pairSum (S := Psub m n) (T := Psub m m) hT ?_ ?_).trans ?_
  · intro x hx σ
    rw [mem_Psub] at hx
    rw [mem_Psub]
    exact ⟨(Edge.smul_adj σ x.1 x.2).mpr hx.1,
      by rw [Esub_self]; exact Finset.mem_univ _,
      by rw [Esub_self]; exact Finset.mem_univ _⟩
  · intro x hx y hy
    rw [mem_Psub] at hx hy
    exact exists_smul_eq_adjPair hx.1 hy.1
  · rw [cAdj]

theorem sum_permRingHom_OpPair (m n : ℕ) (hm : 4 ≤ m) :
    (∑ σ : Equiv.Perm (Fin m), permRingHom σ (OpPair m n)) = cOp m n • OpLap m := by
  classical
  rw [show OpPair m n = ∑ x ∈ Qsub m n, edgeLap x.1 * edgeLap x.2 from rfl,
    show OpLap m = ∑ x ∈ Qsub m m, edgeLap x.1 * edgeLap x.2 from rfl]
  have hT : (Qsub m m).card ≠ 0 := (card_Qsub_pos hm).ne'
  refine (sum_permRingHom_pairSum (S := Qsub m n) (T := Qsub m m) hT ?_ ?_).trans ?_
  · intro x hx σ
    rw [mem_Qsub] at hx
    rw [mem_Qsub]
    exact ⟨(Edge.smul_op σ x.1 x.2).mpr hx.1,
      by rw [Esub_self]; exact Finset.mem_univ _,
      by rw [Esub_self]; exact Finset.mem_univ _⟩
  · intro x hx y hy
    rw [mem_Qsub] at hx hy
    exact exists_smul_eq_opPair hx.1 hy.1
  · rw [cOp]

end Edge

end Submission.RouteB
