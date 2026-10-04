import Mathlib
import Submission.Work.Diff.EXT.curvDefs
import Submission.Work.Diff.EXT.frobSqN_frame_indep
import Submission.Work.Diff.EXT.sum_fin_add_four

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology Matrix
open Bundle ContDiff Set VectorField CovariantDerivative Metric

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-! ## Re-indexing the nested sum

The nested sum over the `k` differentiation slots (`Fin k → Fin n`) followed by the four curvature
slots (`Fin 4 → Fin n`, written out as `![i, j, l, m]`) is the sum over *all* functions
`Fin (k + 4) → Fin n`: this is `sum_fin_add_four` together with the inverse of the splitting
`w ↦ (w ∘ Fin.castAdd 4, w ∘ Fin.natAdd k)`. -/

theorem sum_k4_nested {k n : ℕ} (Φ : (Fin k → Fin n) → (Fin 4 → Fin n) → ℝ) :
    (∑ w : Fin (k + 4) → Fin n, Φ (fun s : Fin k => w (Fin.castAdd 4 s))
        (fun t : Fin 4 => w (Fin.natAdd k t)))
      = ∑ ι : Fin k → Fin n, ∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin n, ∑ m : Fin n,
          Φ ι ![i, j, l, m] := by
  rw [sum_fin_add_four (fun w : Fin (k + 4) → Fin n =>
    Φ (fun s : Fin k => w (Fin.castAdd 4 s)) (fun t : Fin 4 => w (Fin.natAdd k t)))]
  refine Finset.sum_congr rfl (fun ι _ => ?_)
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  refine Finset.sum_congr rfl (fun m _ => ?_)
  have h1 : (fun s : Fin k => Fin.append ι ![i, j, l, m] (Fin.castAdd 4 s)) = ι := by
    funext s; simp
  have h2 : (fun t : Fin 4 => Fin.append ι ![i, j, l, m] (Fin.natAdd k t)) = ![i, j, l, m] := by
    funext t; simp
  rw [h1, h2]

/-! ## `∇^k Rm` at a point as a multilinear map

`KrMulti g x k` says that `krV g x k` is additive and `ℝ`-homogeneous in each of its `k + 4`
tangent arguments.  We package it as a `MultilinearMap` on the index type `Fin k ⊕ Fin 4` (first the
`k` differentiation slots, then the four curvature slots) and transport it along the canonical
equivalence `Fin k ⊕ Fin 4 ≃ Fin (k + 4)`. -/

/-- `∇^k Rm` at `x`, with the `k + 4` arguments indexed by `Fin k ⊕ Fin 4`. -/
noncomputable def krVCur (g : Submission.Diff.SMet I M) (x : M) (k : ℕ)
    (w : Fin k ⊕ Fin 4 → TangentSpace I x) : ℝ :=
  krV g x k (fun s : Fin k => w (Sum.inl s)) (fun t : Fin 4 => w (Sum.inr t))

private lemma krV_update_add_w (g : Submission.Diff.SMet I M) (x : M) (k : ℕ)
    (hM : KrMulti g x k) (i : Fin k)
    (w : Fin k → TangentSpace I x) (u v : TangentSpace I x) (v4 : Fin 4 → TangentSpace I x) :
    krV g x k (Function.update w i (u + v)) v4
      = krV g x k (Function.update w i u) v4 + krV g x k (Function.update w i v) v4 := by
  have h := hM.1 i (Function.update w i u) v v4
  simpa only [Function.update_self, Function.update_idem] using h

private lemma krV_update_smul_w (g : Submission.Diff.SMet I M) (x : M) (k : ℕ)
    (hM : KrMulti g x k) (i : Fin k) (r : ℝ)
    (w : Fin k → TangentSpace I x) (a : TangentSpace I x) (v4 : Fin 4 → TangentSpace I x) :
    krV g x k (Function.update w i (r • a)) v4 = r * krV g x k (Function.update w i a) v4 := by
  have h := hM.2.1 i r (Function.update w i a) v4
  simpa only [Function.update_self, Function.update_idem] using h

private lemma krV_update_add_v (g : Submission.Diff.SMet I M) (x : M) (k : ℕ)
    (hM : KrMulti g x k) (j : Fin 4)
    (w : Fin k → TangentSpace I x) (v : Fin 4 → TangentSpace I x)
    (u v' : TangentSpace I x) :
    krV g x k w (Function.update v j (u + v'))
      = krV g x k w (Function.update v j u) + krV g x k w (Function.update v j v') := by
  have h := hM.2.2.1 j w (Function.update v j u) v'
  simpa only [Function.update_self, Function.update_idem] using h

private lemma krV_update_smul_v (g : Submission.Diff.SMet I M) (x : M) (k : ℕ)
    (hM : KrMulti g x k) (j : Fin 4) (r : ℝ)
    (w : Fin k → TangentSpace I x) (v : Fin 4 → TangentSpace I x) (a : TangentSpace I x) :
    krV g x k w (Function.update v j (r • a)) = r * krV g x k w (Function.update v j a) := by
  have h := hM.2.2.2 j r w (Function.update v j a)
  simpa only [Function.update_self, Function.update_idem] using h

/-- `krV g x k`, packaged as a multilinear map on the index type `Fin k ⊕ Fin 4`. -/
noncomputable def krVCurLin (g : Submission.Diff.SMet I M) (x : M) (k : ℕ)
    (hM : KrMulti g x k) :
    MultilinearMap ℝ (fun _ : Fin k ⊕ Fin 4 => TangentSpace I x) ℝ where
  toFun := krVCur g x k
  map_update_add' := by
    intro _ w s a b
    rcases s with i | j
    · change krVCur g x k (Function.update w (Sum.inl i) (a + b))
        = krVCur g x k (Function.update w (Sum.inl i) a)
          + krVCur g x k (Function.update w (Sum.inl i) b)
      simp only [krVCur, Sum.update_inl_apply_inl, Sum.update_inl_apply_inr]
      exact krV_update_add_w g x k hM i (fun s => w (Sum.inl s)) a b (fun t => w (Sum.inr t))
    · change krVCur g x k (Function.update w (Sum.inr j) (a + b))
        = krVCur g x k (Function.update w (Sum.inr j) a)
          + krVCur g x k (Function.update w (Sum.inr j) b)
      simp only [krVCur, Sum.update_inr_apply_inl, Sum.update_inr_apply_inr]
      exact krV_update_add_v g x k hM j (fun s => w (Sum.inl s)) (fun t => w (Sum.inr t)) a b
  map_update_smul' := by
    intro _ w s c a
    rcases s with i | j
    · change krVCur g x k (Function.update w (Sum.inl i) (c • a))
        = c • krVCur g x k (Function.update w (Sum.inl i) a)
      simp only [krVCur, Sum.update_inl_apply_inl, Sum.update_inl_apply_inr]
      exact krV_update_smul_w g x k hM i c (fun s => w (Sum.inl s)) a (fun t => w (Sum.inr t))
    · change krVCur g x k (Function.update w (Sum.inr j) (c • a))
        = c • krVCur g x k (Function.update w (Sum.inr j) a)
      simp only [krVCur, Sum.update_inr_apply_inl, Sum.update_inr_apply_inr]
      exact krV_update_smul_v g x k hM j c (fun s => w (Sum.inl s)) (fun t => w (Sum.inr t)) a

/-- `∇^k Rm` at `x`, packaged as a multilinear map on `Fin (k + 4)`: the first `k` slots are the
differentiation slots, the last four the curvature slots. -/
noncomputable def krVLin (g : Submission.Diff.SMet I M) (x : M) (k : ℕ)
    (hM : KrMulti g x k) :
    MultilinearMap ℝ (fun _ : Fin (k + 4) => TangentSpace I x) ℝ :=
  (krVCurLin g x k hM).domDomCongr (finSumFinEquiv : Fin k ⊕ Fin 4 ≃ Fin (k + 4))

lemma krVLin_apply (g : Submission.Diff.SMet I M) (x : M) (k : ℕ) (hM : KrMulti g x k)
    (w : Fin (k + 4) → TangentSpace I x) :
    krVLin g x k hM w = krVCurLin g x k hM (fun i : Fin k ⊕ Fin 4 => w (finSumFinEquiv i)) :=
  rfl

/-- On a concatenated tuple, `krVLin` is `krV`. -/
lemma krVLin_append (g : Submission.Diff.SMet I M) (x : M) (k : ℕ) (hM : KrMulti g x k)
    (ι : Fin k → TangentSpace I x) (v : Fin 4 → TangentSpace I x) :
    krVLin g x k hM (Fin.append ι v) = krV g x k ι v := by
  rw [krVLin_apply]
  have h : (fun i : Fin k ⊕ Fin 4 => Fin.append ι v (finSumFinEquiv i)) = Sum.elim ι v := by
    funext i
    rcases i with s | t <;> simp
  rw [h]
  rfl

/-- **Frame independence of the sum of squares of the components of `∇^k Rm`.**  If `krV g x k` is
multilinear in its `k + 4` tangent arguments (`KrMulti g x k`, which has additivity and homogeneity
in each of the `k` `Fin k`-slots and each of the four `Fin 4`-slots), then for any two orthonormal
frames `e`, `f` of `T_xM` the sum of the squares of the components of `∇^k Rm` is the same.  This is
pure finite-dimensional linear algebra: the sum of squares of the components of a multilinear form
in an orthonormal basis is its Hilbert–Schmidt norm squared, which is basis-independent.

PROOF: with `c β α := ⟪e β, f α⟫` one has `e β = ∑_α c β α • f α`
(`Work.Diff.GE.sum_inner_smul_eq_self`), and `∑_α c β α * c β' α = ⟪e β, e β'⟫ = δ` (orthonormality
of `e`, using the orthonormal expansion in `f`), because both frames are orthonormal bases
(`Work.Diff.GE.sum_inner_smul_eq_self` again).  Substituting with `KrMulti` and exchanging sums
(`Finset.prod_univ_sum` for the factorisation over `Fin k → Fin n`, `Finset.sum_mul_sum` and
`Finset.sum_comm` for the squares) gives the claim.  NOTE: the statement
`Work.Diff.EXT.frobSqN_frame_indep` (same directory, currently unproved) is the corresponding
statement for a `MultilinearMap ℝ (Fin N → V) ℝ`; if it has been proved by the time you work, you may
derive the claim from it (by currying `krV` into a `MultilinearMap` on `Fin (k+4) → T_xM`, using
`IsONFrame → Orthonormal` after `letI : RiemannianBundle … := ⟨g.toRiemannianMetric⟩`). -/
theorem covK_frameInv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [T2Space M] (g : Submission.Diff.SMet I M) (x : M) (k : ℕ)
    (hM : KrMulti (I := I) (M := M) g x k)
    (e f : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (he : IsONFrame g x e) (hf : IsONFrame g x f) :
    (∑ ι : Fin k → Fin (Module.finrank ℝ E), ∑ i, ∑ j, ∑ l, ∑ m,
        (krV g x k (fun s ↦ e (ι s)) ![e i, e j, e l, e m]) ^ 2)
      = ∑ ι : Fin k → Fin (Module.finrank ℝ E), ∑ i, ∑ j, ∑ l, ∑ m,
        (krV g x k (fun s ↦ f (ι s)) ![f i, f j, f l, f m]) ^ 2 := by
  classical
  letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun y : M ↦ TangentSpace I y) := inferInstance
  have hone : Orthonormal ℝ e := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [show inner ℝ (e i) (e j) = g.inner x (e i) (e j) from rfl]
    exact he i j
  have honf : Orthonormal ℝ f := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [show inner ℝ (f i) (f j) = g.inner x (f i) (f j) from rfl]
    exact hf i j
  have hvec : ∀ (fr : Fin (Module.finrank ℝ E) → TangentSpace I x)
      (i j l m : Fin (Module.finrank ℝ E)),
      (fun t : Fin 4 => fr (![i, j, l, m] t)) = ![fr i, fr j, fr l, fr m] := by
    intro fr i j l m
    funext t
    fin_cases t <;> rfl
  have hsum : ∀ fr : Fin (Module.finrank ℝ E) → TangentSpace I x,
      (∑ ι : Fin k → Fin (Module.finrank ℝ E), ∑ i, ∑ j, ∑ l, ∑ m,
          (krV g x k (fun s => fr (ι s)) ![fr i, fr j, fr l, fr m]) ^ 2)
        = ∑ w : Fin (k + 4) → Fin (Module.finrank ℝ E),
            (krVLin g x k hM (fun s => fr (w s))) ^ 2 := by
    intro fr
    calc (∑ ι : Fin k → Fin (Module.finrank ℝ E), ∑ i, ∑ j, ∑ l, ∑ m,
              (krV g x k (fun s => fr (ι s)) ![fr i, fr j, fr l, fr m]) ^ 2)
        = ∑ ι : Fin k → Fin (Module.finrank ℝ E), ∑ i, ∑ j, ∑ l, ∑ m,
              (krV g x k (fun s => fr (ι s)) (fun t => fr (![i, j, l, m] t))) ^ 2 := by
            refine Finset.sum_congr rfl (fun ι _ => ?_)
            refine Finset.sum_congr rfl (fun i _ => ?_)
            refine Finset.sum_congr rfl (fun j _ => ?_)
            refine Finset.sum_congr rfl (fun l _ => ?_)
            refine Finset.sum_congr rfl (fun m _ => ?_)
            rw [hvec fr i j l m]
      _ = ∑ w : Fin (k + 4) → Fin (Module.finrank ℝ E),
              (krV g x k (fun s => fr (w (Fin.castAdd 4 s)))
                (fun t => fr (w (Fin.natAdd k t)))) ^ 2 := by
            rw [← sum_k4_nested (k := k) (n := Module.finrank ℝ E)
              (fun (ι : Fin k → Fin (Module.finrank ℝ E))
                   (v : Fin 4 → Fin (Module.finrank ℝ E)) =>
                (krV g x k (fun s => fr (ι s)) (fun t => fr (v t))) ^ 2)]
      _ = ∑ w : Fin (k + 4) → Fin (Module.finrank ℝ E),
              (krVLin g x k hM (fun s => fr (w s))) ^ 2 := by
            refine Finset.sum_congr rfl (fun w _ => ?_)
            have key : krV g x k (fun s => fr (w (Fin.castAdd 4 s)))
                  (fun t => fr (w (Fin.natAdd k t)))
                = krVLin g x k hM (fun s => fr (w s)) := by
              rw [← krVLin_append g x k hM (fun s : Fin k => fr (w (Fin.castAdd 4 s)))
                    (fun t : Fin 4 => fr (w (Fin.natAdd k t)))]
              exact congrArg (krVLin g x k hM)
                (Fin.append_castAdd_natAdd (m := k) (n := 4)
                  (f := fun s : Fin (k + 4) => fr (w s)))
            rw [key]
  rw [hsum e, hsum f]
  exact frobSqN_frame_indep (k + 4) (krVLin g x k hM) e f hone honf

end Work.Diff.EXT
