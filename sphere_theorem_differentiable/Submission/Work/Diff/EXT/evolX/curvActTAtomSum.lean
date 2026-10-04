import Mathlib
import Submission.Work.Diff.EXT.evolX.ladderAtoms
import Submission.Work.Diff.EXT.evolX.baseGDN
import Submission.Work.Diff.EXT.reactDefs
import Submission.Work.Diff.EXT.lapComm_tower
import Submission.Work.Diff.EXT.evolX.atomZf_pair
import Submission.Work.Diff.EXT.evolX.atomZf_smooth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The curvature action is a negated sum of base atoms

`Work.Diff.EXT.curvActT g j H` is the curvature action at level `j`: it is the sum over the slots
`s : Fin (j+4)` of the level-`j` tower `∇^j Rm` evaluated on the tuple which is `H ∘ succ ∘ succ`
except in the slot `s`, where the curvature field `R(H 0, H 1, H_{s+2})` is inserted.

`Work.Diff.EXT.evolX.Atom g W j 0 (j+6) s (baseK j s) (baseXi j s) H` is that same tower with the
slot `s` replaced by the *frame-expanded* curvature vector `Zf g W 0 (H ∘ baseXi j s)`, i.e. by
`∑ i, ckt g 0 (H 0, H 1, H_{s+2}, W i) • W i`.

The present module proves that these two agree, up to the sign of the curvature convention:

* the index maps `baseK j s`, `baseXi j s` form a partition of the `j + 6` tuple positions
  (`Work.Diff.EXT.evolX.baseGDN`);
* the frame-expanded curvature vector is the *negated* curvature field
  (`Work.Diff.EXT.evolX.Zf_zero_eq_neg_curv` below: `⟪R(a,b,c), d⟫ = -⟪R(a,b,d), c⟫` and the
  orthonormal frame expansion `∑ i, ⟪v, W i⟫ • W i = v`);
* the tower is multilinear in its slots and depends only on the slot *values* at the base point
  (`Work.Diff.EXT.ckt_eq_Kpt'`, `Work.Diff.EXT.Kpt_smul`).

Hence `curvActT g j H x = - ∑ s, Atom … s … H x`.

This is exactly the statement of the (still `sorry`-ed) sibling `curvActT_eq_atomSum_v2` (with the
tuple named `H` rather than `H'`); a consumer of that path may be re-pointed here.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.evolX

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-! ## Index arithmetic of `baseXi` -/

/-- The third value of `baseXi` is the `(s+2)`-th position, i.e. `s.succ.succ`. -/
lemma baseXi_two_eq (j : ℕ) (s : Fin (j + 4)) : baseXi j s 2 = s.succ.succ := by
  rw [baseXi_two]
  rfl

/-- Away from the special slot, `baseK j s i` is `i.succ.succ`. -/
lemma baseK_eq_succ_succ {j : ℕ} {s i : Fin (j + 4)} (hi : i ≠ s) :
    baseK j s i = i.succ.succ := by
  apply Fin.ext
  rw [baseK_val_of_ne (j := j) (s := s) hi]
  rfl

/-! ## The frozen curvature form as an inner product of the curvature field -/

/-- `rmP g x a b c d = g(R(a,b)d, c)` with `R` the curvature of the Levi-Civita connection and all
four arguments the *values* of smooth fields at `x`. -/
lemma rmP_eq_g_inner_curv (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (x : M) {A B C D : Work.Diff.EXT.TField (I := I) (M := M)}
    (hA : Work.Diff.EXT.SmoothF A) (hB : Work.Diff.EXT.SmoothF B)
    (_hC : Work.Diff.EXT.SmoothF C) (hD : Work.Diff.EXT.SmoothF D) :
    rmP g x (A x) (B x) (C x) (D x)
      = g.inner x (curv (Submission.Diff.lcOf g) A B D x) (C x) := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  obtain ⟨hcov⟩ := (hLC g).1
  show g.inner x (rmVec (Submission.Diff.lcOf g) x (A x) (B x) (D x)) (C x)
    = g.inner x (curv (Submission.Diff.lcOf g) A B D x) (C x)
  have hrv : rmVec (Submission.Diff.lcOf g) x (A x) (B x) (D x)
      = curv (Submission.Diff.lcOf g) A B D x := by
    rw [show rmVec (Submission.Diff.lcOf g) x (A x) (B x) (D x)
        = curv (Submission.Diff.lcOf g) (Submission.Diff.smoothExt x (A x))
            (Submission.Diff.smoothExt x (B x)) (Submission.Diff.smoothExt x (D x)) x from rfl]
    exact Submission.Curvature.curv_eq_of_apply_eq (Submission.Diff.lcOf g) hcov
      (Work.Diff.GE.smoothExt_cmdiff x (A x)) hA
      (Work.Diff.GE.smoothExt_cmdiff x (B x)) hB
      (Work.Diff.GE.smoothExt_cmdiff x (D x)) hD
      (Work.Diff.GE.smoothExt_apply x (A x)) (Work.Diff.GE.smoothExt_apply x (B x))
      (Work.Diff.GE.smoothExt_apply x (D x))
  rw [hrv]

/-! ## The frame-expanded curvature vector is the negated curvature field -/

/-- **The level-`0` frame expansion of the curvature vector.**
For a `g`-orthonormal frame field `W` near `x` and smooth fields `A, B, C`,
`Zf g W 0 (A, B, C) x = - R(A,B,C)(x)`: expanding the curvature in the frame and using the
antisymmetry `⟪R(a,b,d),c⟫ = -⟪R(a,b,c),d⟫` of the curvature form. -/
lemma Zf_zero_eq_neg_curv (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (x : M) (W : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (hW : ∀ i, SmTf (I := I) (M := M) (W i))
    (hON : ONFrameAt (I := I) (M := M) g x W)
    (A B C : Work.Diff.EXT.TField (I := I) (M := M))
    (hA : SmTf (I := I) (M := M) A) (hB : SmTf (I := I) (M := M) B)
    (hC : SmTf (I := I) (M := M) C) :
    Zf (I := I) (M := M) g W 0 (fun r : Fin 3 => ![A, B, C] r) x
      = - curv (Submission.Diff.lcOf g) A B C x := by
  have hONx : IsONFrame g x (fun i => W i x) := hON.self_of_nhds
  -- the frame coefficients of the left-hand side
  have key : ∀ i : Fin (Module.finrank ℝ E),
      g.inner x (Zf (I := I) (M := M) g W 0 (fun r : Fin 3 => ![A, B, C] r) x) (W i x)
        = - g.inner x (curv (Submission.Diff.lcOf g) A B C x) (W i x) := by
    intro i
    rw [atomZf_pair (I := I) (M := M) g x W hW hON 0 (fun r : Fin 3 => ![A, B, C] r)
      (fun r => by fin_cases r <;> assumption) (W i) (hW i)]
    have hsnoc : (Fin.snoc (fun r : Fin 3 => ![A, B, C] r) (W i) :
        Fin 4 → Work.Diff.EXT.TField (I := I) (M := M)) = ![A, B, C, W i] := by
      funext r
      fin_cases r <;> simp
    rw [hsnoc]
    show rmP g x (A x) (B x) (C x) (W i x)
      = - g.inner x (curv (Submission.Diff.lcOf g) A B C x) (W i x)
    rw [Work.Diff.GE.rmP_skew hLC g x (A x) (B x) (C x) (W i x),
        rmP_eq_g_inner_curv hLC g x hA hB (hW i) hC]
  calc Zf (I := I) (M := M) g W 0 (fun r : Fin 3 => ![A, B, C] r) x
      = ∑ i, g.inner x (Zf (I := I) (M := M) g W 0 (fun r : Fin 3 => ![A, B, C] r) x)
          (W i x) • W i x :=
        (Work.EXT.sum_inner_smul_eq_self_of_isONFrame g x (fun i => W i x) hONx _).symm
    _ = ∑ i, (- g.inner x (curv (Submission.Diff.lcOf g) A B C x) (W i x)) • W i x :=
        Finset.sum_congr rfl (fun i _ => by rw [key i])
    _ = - ∑ i, g.inner x (curv (Submission.Diff.lcOf g) A B C x) (W i x) • W i x := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun i _ => neg_smul _ _)
    _ = - curv (Submission.Diff.lcOf g) A B C x := by
        rw [Work.EXT.sum_inner_smul_eq_self_of_isONFrame g x (fun i => W i x) hONx
            (curv (Submission.Diff.lcOf g) A B C x)]

/-! ## The main theorem -/

theorem curvActTAtomSum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M) (j : ℕ)
    (W : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (hW : ∀ i, Work.Diff.EXT.evolX.SmTf (I := I) (M := M) (W i))
    (hON : Work.Diff.EXT.evolX.ONFrameAt (I := I) (M := M) g x W)
    (H' : Fin (j + 6) → Work.Diff.EXT.TField (I := I) (M := M))
    (hH' : ∀ u, Work.Diff.EXT.evolX.SmTf (I := I) (M := M) (H' u)) :
    (∀ s : Fin (j + 4), Work.Diff.EXT.evolX.GoodDataN j 0 (j + 6) s
        (Work.Diff.EXT.evolX.baseK j s) (Work.Diff.EXT.evolX.baseXi j s))
      ∧ Work.Diff.EXT.curvActT (I := I) (M := M) g j H' x
        = - ∑ s : Fin (j + 4), Work.Diff.EXT.evolX.Atom (I := I) (M := M) g W j 0 (j + 6) s
            (Work.Diff.EXT.evolX.baseK j s) (Work.Diff.EXT.evolX.baseXi j s) H' x := by
  classical
  have hcov : ContMDiffCovariantDerivative (Submission.Diff.lcOf g) ∞ := (hLC g).1.some
  -- the two base index maps of the curvature action
  have hTLsm : ∀ i : Fin (j + 4),
      Work.Diff.EXT.SmoothF ((fun i : Fin (j + 4) => H' i.succ.succ) i) :=
    fun i => hH' i.succ.succ
  have hCsm : ∀ s : Fin (j + 4), Work.Diff.EXT.SmoothF
      (fun z => curv (Submission.Diff.lcOf g) (H' 0) (H' 1) (H' s.succ.succ) z) :=
    fun s => Work.Diff.GE.contMDiff_curv_fields (Submission.Diff.lcOf g) hcov
      (hH' 0) (hH' 1) (hH' s.succ.succ)
  -- the inserted curvature vector, written as the tuple `![H' 0, H' 1, H' (s+2)]`
  have hPsi : ∀ s : Fin (j + 4),
      (fun r : Fin 3 => H' (baseXi j s r)) = ![H' 0, H' 1, H' s.succ.succ] := by
    intro s
    funext r
    fin_cases r
    · exact congrArg H' (baseXi_zero j s)
    · exact congrArg H' (baseXi_one j s)
    · exact congrArg H' (baseXi_two_eq j s)
  -- the value of the inserted curvature vector at `x`
  have hZfval : ∀ s : Fin (j + 4),
      Zf (I := I) (M := M) g W 0 (fun r : Fin 3 => H' (baseXi j s r)) x
        = - curv (Submission.Diff.lcOf g) (H' 0) (H' 1) (H' s.succ.succ) x := by
    intro s
    rw [hPsi s]
    exact Zf_zero_eq_neg_curv (I := I) (M := M) hLC g x W hW hON (H' 0) (H' 1)
      (H' s.succ.succ) (hH' 0) (hH' 1) (hH' s.succ.succ)
  -- each base atom is the negated corresponding summand of the curvature action
  have hAtom : ∀ s : Fin (j + 4),
      Atom (I := I) (M := M) g W j 0 (j + 6) s (baseK j s) (baseXi j s) H' x
        = - ckt g j (Function.update (fun i : Fin (j + 4) => H' i.succ.succ) s
            (fun z => curv (Submission.Diff.lcOf g) (H' 0) (H' 1) (H' s.succ.succ) z)) x := by
    intro s
    have hZsm : SmTf (I := I) (M := M)
        (Zf (I := I) (M := M) g W 0 (fun r : Fin 3 => H' (baseXi j s r))) :=
      atomZf_smooth (I := I) (M := M) hLC g W hW 0 _ (fun r => hH' (baseXi j s r))
    have hUpd1 : ∀ i, Work.Diff.EXT.SmoothF
        ((Function.update (fun i : Fin (j + 4) => H' i.succ.succ) s
          (Zf (I := I) (M := M) g W 0 (fun r : Fin 3 => H' (baseXi j s r)))) i) := by
      intro i
      rcases eq_or_ne i s with hi | hi
      · subst hi; rw [Function.update_self]; exact hZsm
      · rw [Function.update_of_ne hi]; exact hTLsm i
    have hUpd2 : ∀ i, Work.Diff.EXT.SmoothF
        ((Function.update (fun i : Fin (j + 4) => H' i.succ.succ) s
          (fun z => curv (Submission.Diff.lcOf g) (H' 0) (H' 1) (H' s.succ.succ) z)) i) :=
      Work.Diff.EXT.smoothF_update hTLsm (hCsm s)
    have hTuple : (fun i : Fin (j + 4) => if i = s then Zf (I := I) (M := M) g W 0
          (fun r : Fin 3 => H' (baseXi j s r)) else H' (baseK j s i))
        = Function.update (fun i : Fin (j + 4) => H' i.succ.succ) s
            (Zf (I := I) (M := M) g W 0 (fun r : Fin 3 => H' (baseXi j s r))) := by
      funext i
      by_cases hi : i = s
      · subst hi; simp [Function.update_self]
      · simp [hi, baseK_eq_succ_succ hi]
    have hA : Atom (I := I) (M := M) g W j 0 (j + 6) s (baseK j s) (baseXi j s) H' x
        = ckt g j (Function.update (fun i : Fin (j + 4) => H' i.succ.succ) s
            (Zf (I := I) (M := M) g W 0 (fun r : Fin 3 => H' (baseXi j s r)))) x := by
      simp only [Atom]
      rw [hTuple]
    have hB : ckt g j (Function.update (fun i : Fin (j + 4) => H' i.succ.succ) s
          (Zf (I := I) (M := M) g W 0 (fun r : Fin 3 => H' (baseXi j s r)))) x
        = Kpt g x j (Function.update (fun i : Fin (j + 4) => H' i.succ.succ x) s
            (Zf (I := I) (M := M) g W 0 (fun r : Fin 3 => H' (baseXi j s r)) x)) := by
      rw [ckt_eq_Kpt' hLC g j x hUpd1]
      congr 1
      funext i
      by_cases hi : i = s <;> simp [hi]
    have hC : Kpt g x j (Function.update (fun i : Fin (j + 4) => H' i.succ.succ x) s
          (Zf (I := I) (M := M) g W 0 (fun r : Fin 3 => H' (baseXi j s r)) x))
        = - Kpt g x j (Function.update (fun i : Fin (j + 4) => H' i.succ.succ x) s
            (curv (Submission.Diff.lcOf g) (H' 0) (H' 1) (H' s.succ.succ) x)) := by
      rw [hZfval s]
      have h := Kpt_smul hLC g x j (fun i : Fin (j + 4) => H' i.succ.succ x) s (-1 : ℝ)
        (curv (Submission.Diff.lcOf g) (H' 0) (H' 1) (H' s.succ.succ) x)
      simpa only [neg_one_smul] using h
    have hD : Kpt g x j (Function.update (fun i : Fin (j + 4) => H' i.succ.succ x) s
          (curv (Submission.Diff.lcOf g) (H' 0) (H' 1) (H' s.succ.succ) x))
        = ckt g j (Function.update (fun i : Fin (j + 4) => H' i.succ.succ) s
            (fun z => curv (Submission.Diff.lcOf g) (H' 0) (H' 1) (H' s.succ.succ) z)) x := by
      rw [ckt_eq_Kpt' hLC g j x hUpd2]
      congr 1
      funext i
      by_cases hi : i = s <;> simp [hi]
    rw [hA, hB, hC, ← hD]
  -- sum over the slots
  refine ⟨fun s => baseGDN j s, ?_⟩
  have hsum : (∑ s : Fin (j + 4), Atom (I := I) (M := M) g W j 0 (j + 6) s
        (baseK j s) (baseXi j s) H' x)
      = - curvActT (I := I) (M := M) g j H' x := by
    rw [Finset.sum_congr rfl (fun s _ => hAtom s), Finset.sum_neg_distrib]
    rw [show curvActT (I := I) (M := M) g j H' x
        = ∑ s : Fin (j + 4), ckt g j (Function.update (fun i : Fin (j + 4) => H' i.succ.succ) s
            (fun z => curv (Submission.Diff.lcOf g) (H' 0) (H' 1) (H' s.succ.succ) z)) x
        from rfl]
  rw [hsum, neg_neg]

end Work.Diff.EXT.evolX
