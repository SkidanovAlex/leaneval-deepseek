import Mathlib
import Submission.Work.WilE6.Closure
import Submission.Work.WilE6.CritSA
import Submission.Work.WilE6.Base
import Submission.Work.WilE6.Block
import Submission.Work.WilE6.Setup
import Submission.Work.WilE6.critSA_mem_iff
import Submission.Work.WilE6.critSA_deg_le
import Submission.Work.WilE6.mem_saSlice_iff
import Submission.Work.WilE6.eaTaylor_poly_shifted
import Submission.Work.WilE6.norm_witness_iff
import Submission.Work.WilE6.critFibreCond_imp_critCond
import Submission.Work.WilE6.critCond_imp_exists_witness
import Submission.Work.WilE6.eaTaylor_baseAtom

noncomputable section
namespace Work.WilE6
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-! ## §1. Elementary topological helpers

The closure of the fibre of a set under the inclusion `y ↦ Fin.append x y` of `ℝ^q` into the
fibre `{z | projFirst p q z = x}` of `ℝ^{p+q}`, and the behaviour of `closure` under a
translation. -/

/-- `Fin.append x ·` is an isometry onto its image. -/
theorem dist_append_append (p q : ℕ) (x : Fin p → ℝ) (y y' : Fin q → ℝ) :
    dist (Fin.append x y) (Fin.append x y') = dist y y' := by
  refine le_antisymm ?_ ?_
  · rw [dist_pi_le_iff dist_nonneg]
    intro i
    induction i using Fin.addCases with
    | left i => rw [Fin.append_left, Fin.append_left]; simp
    | right j => rw [Fin.append_right, Fin.append_right]; exact dist_le_pi_dist y y' j
  · rw [dist_pi_le_iff dist_nonneg]
    intro j
    have h := dist_le_pi_dist (Fin.append x y) (Fin.append x y') (Fin.natAdd p j)
    rw [Fin.append_right, Fin.append_right] at h
    exact h

/-- Continuity of `y ↦ Fin.append x y`. -/
theorem continuous_fin_append (p q : ℕ) (x : Fin p → ℝ) :
    Continuous (fun y : Fin q → ℝ => Fin.append x y) := by
  rw [continuous_pi_iff]
  intro i
  induction i using Fin.addCases with
  | left i =>
    have h : (fun y : Fin q → ℝ => Fin.append x y (Fin.castAdd q i)) = fun _ => x i := by
      funext y; rw [Fin.append_left]
    rw [h]; exact continuous_const
  | right j =>
    have h : (fun y : Fin q → ℝ => Fin.append x y (Fin.natAdd p j)) = fun y => y j := by
      funext y; rw [Fin.append_right]
    rw [h]; exact continuous_apply j

/-- The cube `[-1,1]^n` is closed. -/
theorem isClosed_cubeC (n : ℕ) : IsClosed (cubeC n) := by
  rw [show cubeC n = ⋂ i, {x : Fin n → ℝ | |x i| ≤ 1} by
    ext x; simp [cubeC]]
  exact isClosed_iInter fun i => isClosed_le (continuous_apply i |>.abs) continuous_const

/-- Membership in the closure of a fibre set, transported to `ℝ^{p+q}`. -/
theorem mem_closure_append_iff (p q : ℕ) (x : Fin p → ℝ) (S : Set (Fin q → ℝ))
    (w : Fin q → ℝ) :
    w ∈ closure S ↔ Fin.append x w ∈ closure ((fun y : Fin q → ℝ => Fin.append x y) '' S) := by
  rw [Metric.mem_closure_iff, Metric.mem_closure_iff]
  constructor
  · intro h ε hε
    obtain ⟨y, hy, hyε⟩ := h ε hε
    exact ⟨Fin.append x y, ⟨y, hy, rfl⟩, by rw [dist_append_append]; exact hyε⟩
  · intro h ε hε
    obtain ⟨t, ⟨y, hy, rfl⟩, hyt⟩ := h ε hε
    exact ⟨y, hy, by rw [dist_append_append] at hyt; exact hyt⟩

/-- A fibre set contained in the cube has its closure inside the (closed) fibre cube. -/
theorem closure_fiber_subset_cube {p q : ℕ} {S : Set (Fin (p + q) → ℝ)}
    (hS : S ⊆ cubeC (p + q)) {x : Fin p → ℝ} :
    closure (fiber S x) ⊆ (fun y : Fin q → ℝ => Fin.append x y) ⁻¹' cubeC (p + q) := by
  intro y hy
  rw [Set.mem_preimage]
  refine closure_minimal ?_
    ((isClosed_cubeC (p + q)).preimage (continuous_fin_append p q x)) hy
  intro y' hy'
  exact hS hy'

/-- `closure` commutes with a translation. -/
theorem mem_closure_translate (k : ℕ) (a : Fin k → ℝ) (V : Set (Fin k → ℝ)) :
    a ∈ closure ((fun u : Fin k → ℝ => a + u) '' V) ↔ 0 ∈ closure V := by
  rw [Metric.mem_closure_iff, Metric.mem_closure_iff]
  constructor
  · intro h ε hε
    obtain ⟨z, ⟨u, hu, rfl⟩, hzu⟩ := h ε hε
    exact ⟨u, hu, by simpa using hzu⟩
  · intro h ε hε
    obtain ⟨u, hu, huε⟩ := h ε hε
    exact ⟨a + u, ⟨u, hu, rfl⟩, by simpa using huε⟩

/-! ## §2. The frozen basic set and the Taylor criterion

For a basic set `B` of the presentation and a point `z`, the fibre closure at `z` is computed by
E3b applied to the *frozen* basic set: the merged equation `mergeEq B = ∑ f²`, the `p`
base-fixing atoms `z'_i - z_i` (which force the closure to be taken inside the fibre over
`projFirst z`), and the positivity atoms of `B`.  This section identifies the criterion set of
E3b for that frozen basic set with the `critSA`/`critCond` vocabulary. -/

section Frozen

variable {r p q : ℕ}

/-- The base-fixing atom `z'_i - z_i` (one equation `projFirst z' = projFirst z`). -/
def baseAtom (r p q : ℕ) (z : Fin (p + q) → ℝ) (i : Fin p) : EAPoly (p + q) r :=
  MvPolynomial.X (Sum.inl (Fin.castAdd q i)) - MvPolynomial.C (z (Fin.castAdd q i))

/-- The list of base-fixing atoms. -/
def baseAtoms (r p q : ℕ) (z : Fin (p + q) → ℝ) : List (EAPoly (p + q) r) :=
  (List.finRange p).map (baseAtom r p q z)

/-- The frozen basic set: merged equation, base-fixing atoms, positivity atoms. -/
def frozenBasic (p q r : ℕ) (B : Basic (p + q) r) (z : Fin (p + q) → ℝ) : Basic (p + q) r :=
  ⟨mergeEq B :: baseAtoms r p q z, B.pos⟩

@[simp] theorem eaEval_baseAtom (c : EAChain (p + q) r) (z z' : Fin (p + q) → ℝ) (i : Fin p) :
    eaEval c (baseAtom r p q z i) z' = z' (Fin.castAdd q i) - z (Fin.castAdd q i) := by
  simp only [baseAtom, eaEval, MvPolynomial.eval_sub, MvPolynomial.eval_X, MvPolynomial.eval_C,
    Sum.elim_inl]

theorem totalDegree_baseAtom_le (z : Fin (p + q) → ℝ) (i : Fin p) :
    (baseAtom r p q z i).totalDegree ≤ 1 := by
  rw [baseAtom]
  refine (totalDegree_sub_le_max _ _).trans ?_
  rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C]
  omega

theorem sum_map_atomDeg_baseAtoms_le (z : Fin (p + q) → ℝ) :
    ((baseAtoms r p q z).map atomDeg).sum ≤ 2 * p := by
  rw [baseAtoms, List.map_map]
  have h2 : ∀ x ∈ (List.finRange p).map (atomDeg ∘ baseAtom r p q z), x ≤ 2 := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
    simp only [Function.comp_apply, atomDeg]
    have := totalDegree_baseAtom_le (r := r) (q := q) z i
    omega
  have h3 : ((List.finRange p).map (atomDeg ∘ baseAtom r p q z)).sum ≤ p * 2 := by
    simpa [List.length_finRange, nsmul_eq_mul] using
      (List.sum_le_length_nsmul ((List.finRange p).map (atomDeg ∘ baseAtom r p q z)) 2 h2)
  omega

theorem frozenBasic_deg_le (B : Basic (p + q) r) (z : Fin (p + q) → ℝ) :
    (frozenBasic p q r B z).deg ≤ 3 * B.deg + 2 * p + 1 := by
  have h1 : atomDeg (mergeEq B) ≤ 2 * B.deg + 1 := by
    simp only [atomDeg]
    have := totalDegree_mergeEq_le (k := p + q) B
    omega
  have h2 := sum_map_atomDeg_baseAtoms_le (r := r) (p := p) (q := q) z
  have h3 : (B.pos.map atomDeg).sum ≤ B.deg := by
    simp only [Basic.deg, List.map_append, List.sum_append]; omega
  have hdeg : (frozenBasic p q r B z).deg = atomDeg (mergeEq B)
      + ((baseAtoms r p q z).map atomDeg).sum + (B.pos.map atomDeg).sum := by
    simp only [frozenBasic, Basic.deg, List.map_append, List.sum_append, List.map_cons,
      List.sum_cons]
  rw [hdeg]
  omega

/-- The frozen basic set holds exactly when `B` holds and the base coordinate is `projFirst z`. -/
theorem frozenBasic_holds_iff (c : EAChain (p + q) r) (B : Basic (p + q) r)
    (z z' : Fin (p + q) → ℝ) :
    (frozenBasic p q r B z).holds c z' ↔ B.holds c z' ∧ projFirst p q z' = projFirst p q z := by
  have hbase : (∀ a ∈ baseAtoms r p q z, eaEval c a z' = 0)
      ↔ projFirst p q z' = projFirst p q z := by
    rw [baseAtoms, List.forall_mem_map]
    simp only [List.mem_finRange, true_implies, eaEval_baseAtom]
    constructor
    · intro h
      funext i
      exact sub_eq_zero.mp (h i)
    · intro h i
      rw [show z' (Fin.castAdd q i) = z (Fin.castAdd q i) from congrFun h i, sub_self]
  have hmerge := mergeEq_holds_iff (k := p + q) (r := r) c B z'
  rw [frozenBasic, Basic.holds, List.forall_mem_cons, hbase]
  constructor
  · rintro ⟨⟨hm, hb⟩, hp⟩
    exact ⟨⟨hmerge.mp hm, hp⟩, hb⟩
  · rintro ⟨⟨he, hp⟩, hb⟩
    exact ⟨⟨hmerge.mpr he, hb⟩, hp⟩

theorem eval_Pof (c : EAChain (p + q) r) (B : Basic (p + q) r) (κ : ℕ) (z u : Fin (p + q) → ℝ) :
    eaTaylor c (mergeEq B) (κ ^ 2) z (z + u) =
      MvPolynomial.eval (Sum.elim u (Fin.append z (hvec c z))) (Pof c B κ) := by
  have h := (eval_eaTaylorPoly c (mergeEq B) (κ ^ 2) z u).symm
  simpa only [graphPt, Pof] using h

theorem eval_eaTaylorPoly' (c : EAChain (p + q) r) (Q : EAPoly (p + q) r) (N : ℕ)
    (z u : Fin (p + q) → ℝ) :
    eaTaylor c Q N z (z + u) =
      MvPolynomial.eval (Sum.elim u (Fin.append z (hvec c z))) (eaTaylorPoly c Q N) := by
  have h := (eval_eaTaylorPoly c Q N z u).symm
  simpa only [graphPt] using h

/-- The criterion set of E3b for the frozen basic set, in the shifted variable `u = z' - z`,
is exactly `critCond`. -/
theorem frozen_crit_iff (hp : p ≤ p + q) {κ : ℕ} (hκ : 1 ≤ κ) (c : EAChain (p + q) r)
    (B : Basic (p + q) r) (z u : Fin (p + q) → ℝ) :
    ((∀ f ∈ (frozenBasic p q r B z).eqs,
        |eaTaylor c f (κ ^ 2) z (z + u)| ≤ dist (z + u) z ^ (κ ^ 2)) ∧
      (∀ g ∈ B.pos, dist (z + u) z ^ κ < eaTaylor c g κ z (z + u))) ↔
    critCond (p := p) hp κ (Pof c B κ) (Gsof c B κ) z (hvec c z) u := by
  have hdist : dist (z + u) z = dist u 0 := by simpa using dist_add_left z u 0
  have hN : 1 ≤ κ ^ 2 := Nat.one_le_pow 2 κ (by omega)
  have hmerge := eval_Pof c B κ z u
  have hbase : ∀ i : Fin p, eaTaylor c (baseAtom r p q z i) (κ ^ 2) z (z + u) =
      u (Fin.castAdd q i) := by
    intro i
    rw [show baseAtom r p q z i = MvPolynomial.X (Sum.inl (Fin.castAdd q i)) -
        MvPolynomial.C (z (Fin.castAdd q i)) from rfl,
      eaTaylor_baseAtom c (Fin.castAdd q i) (z (Fin.castAdd q i)) hN z (z + u)]
    simp
  have hpos : ∀ g : EAPoly (p + q) r, eaTaylor c g κ z (z + u) =
      MvPolynomial.eval (Sum.elim u (Fin.append z (hvec c z))) (eaTaylorPoly c g κ) :=
    fun g => eval_eaTaylorPoly' c g κ z u
  have hcast : ∀ i : Fin p, (⟨i.1, lt_of_lt_of_le i.2 hp⟩ : Fin (p + q)) = Fin.castAdd q i :=
    fun i => Fin.ext rfl
  simp only [frozenBasic, List.forall_mem_cons, baseAtoms, List.forall_mem_map, List.mem_finRange,
    true_implies, critCond, Gsof]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [hmerge, hdist] at h1; exact h1
    · intro i
      have hi := h2 i
      rw [hbase i, hdist] at hi
      rw [hcast i]; exact hi
    · intro G hG
      have hg3 := h3 G hG
      rw [hpos G, hdist] at hg3
      exact hg3
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [← hmerge, ← hdist] at h1; exact h1
    · intro i
      have hi := h2 i
      rw [hcast i, ← hbase i, ← hdist] at hi
      exact hi
    · intro g hg
      have hg3 := h3 g hg
      rw [← hpos g, ← hdist] at hg3
      exact hg3

end Frozen

/-! ## §3. The witness closure equivalence

The fibre of `critSA` for a basic set `B` (the "witness set" `uSet`) and the criterion set
`critSet` have the same closure at the origin.  The forward inclusion is `projU` composed with
the implication `critFibreCond → critCond`; the reverse direction uses the canonical witnesses
(`critCond → ∃ j v, critFibreCond`) and the quantitative bound on the witnesses. -/

end Work.WilE6
