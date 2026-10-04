import Mathlib
import Submission.Work.Diff.EXT.curvDefs
import Submission.Work.Diff.EXT.curvNormK_frame_indep
import Submission.Work.Diff.GE.NablaRm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-! ## The slot packaging of the `k + 4` arguments of `∇^k Rm` -/

/-- The `k + 4` tangent vectors on which `∇^k Rm` is evaluated at a point, packaged as one
`Fin (k+4)`-tuple: the first `k` are the differentiation slots, the last four the curvature
slots. -/
def combTup {k : ℕ} {x : M} (w : Fin k → TangentSpace I x) (v : Fin 4 → TangentSpace I x) :
    Fin (k + 4) → TangentSpace I x :=
  Fin.addCases (motive := fun _ => TangentSpace I x) w v

@[simp] lemma combTup_castAdd {k : ℕ} {x : M} (w : Fin k → TangentSpace I x)
    (v : Fin 4 → TangentSpace I x) (i : Fin k) :
    combTup w v (Fin.castAdd 4 i) = w i :=
  Fin.addCases_left (motive := fun _ => TangentSpace I x) i

@[simp] lemma combTup_natAdd {k : ℕ} {x : M} (w : Fin k → TangentSpace I x)
    (v : Fin 4 → TangentSpace I x) (j : Fin 4) :
    combTup w v (Fin.natAdd k j) = v j :=
  Fin.addCases_right (motive := fun _ => TangentSpace I x) j

lemma castAdd_ne_natAdd {k : ℕ} (i : Fin k) (j : Fin 4) :
    (Fin.castAdd 4 i : Fin (k + 4)) ≠ Fin.natAdd k j := by
  intro h
  have h1 : (Fin.castAdd 4 i : Fin (k + 4)).val = i.val := rfl
  have h2 : (Fin.natAdd k j).val = k + j.val := by rw [Fin.natAdd_mk]
  have := congrArg Fin.val h
  omega

/-! ## `krV` as the point-level evaluation `Kpt` of the library -/

/-- `krV g x k w v` is the library's `Kpt` evaluated on the combined tuple. -/
lemma krV_eq_Kpt (g : SMet I M) (x : M) (k : ℕ) (w : Fin k → TangentSpace I x)
    (v : Fin 4 → TangentSpace I x) :
    krV g x k w v = Kpt g x k (combTup w v) := by
  rw [Kpt, ckt_eq_covKRmExt]
  simp only [krV, covKRm, combTup_castAdd, combTup_natAdd]

lemma combTup_update_left {k : ℕ} {x : M} (w : Fin k → TangentSpace I x)
    (v : Fin 4 → TangentSpace I x) (i : Fin k) (u : TangentSpace I x) :
    combTup (Function.update w i u) v
      = Function.update (combTup w v) (Fin.castAdd 4 i) u := by
  funext s
  refine Fin.addCases (motive := fun s => combTup (Function.update w i u) v s
      = Function.update (combTup w v) (Fin.castAdd 4 i) u s) ?_ ?_ s
  · intro i'
    simp only [combTup_castAdd, Function.update_apply]
    by_cases h : i' = i
    · subst h; simp
    · have hne : (Fin.castAdd 4 i' : Fin (k + 4)) ≠ Fin.castAdd 4 i := by
        simp [Fin.castAdd_inj, h]
      rw [if_neg h, if_neg hne]
  · intro j
    simp only [combTup_natAdd, Function.update_apply]
    rw [if_neg (Ne.symm (castAdd_ne_natAdd i j))]

lemma combTup_update_right {k : ℕ} {x : M} (w : Fin k → TangentSpace I x)
    (v : Fin 4 → TangentSpace I x) (j : Fin 4) (u : TangentSpace I x) :
    combTup w (Function.update v j u)
      = Function.update (combTup w v) (Fin.natAdd k j) u := by
  funext s
  refine Fin.addCases (motive := fun s => combTup w (Function.update v j u) s
      = Function.update (combTup w v) (Fin.natAdd k j) u s) ?_ ?_ s
  · intro i
    simp only [combTup_castAdd, Function.update_apply]
    rw [if_neg (castAdd_ne_natAdd i j)]
  · intro j'
    simp only [combTup_natAdd, Function.update_apply]
    by_cases h : j' = j
    · subst h; simp
    · have hne : (Fin.natAdd k j' : Fin (k + 4)) ≠ Fin.natAdd k j := by
        simp [Fin.natAdd_inj, h]
      rw [if_neg h, if_neg hne]

/-- **Multilinearity in the values.**  The point-level evaluation `Kpt` of the tower is
multilinear (`Kpt_add`, `Kpt_smul` in `Submission/Work/Diff/EXT/curvNormK_frame_indep.lean`), and
`krV` is `Kpt` on the combined tuple, so `krV g x k` is multilinear in the `k + 4` values. -/
theorem KrMulti_of_Kpt (hLC : LCSmooth I M) (g : SMet I M) (x : M) (k : ℕ) :
    KrMulti (I := I) (M := M) g x k := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i w w' v
    have h1 : combTup (Function.update w i (w i + w')) v
        = Function.update (combTup w v) (Fin.castAdd 4 i) (w i + w') :=
      combTup_update_left w v i (w i + w')
    have h2 : combTup (Function.update w i w') v
        = Function.update (combTup w v) (Fin.castAdd 4 i) w' :=
      combTup_update_left w v i w'
    have h3 : Function.update (combTup w v) (Fin.castAdd 4 i) (w i) = combTup w v := by
      rw [← combTup_castAdd (w := w) (v := v) (i := i)]
      exact Function.update_eq_self _ _
    have hK : Kpt g x k (Function.update (combTup w v) (Fin.castAdd 4 i) (w i + w'))
        = Kpt g x k (combTup w v)
          + Kpt g x k (Function.update (combTup w v) (Fin.castAdd 4 i) w') := by
      have hh := Kpt_add hLC g x k (combTup w v) (Fin.castAdd 4 i) (w i) w'
      rwa [h3] at hh
    rw [krV_eq_Kpt, krV_eq_Kpt, krV_eq_Kpt, h1, h2, hK]
  · intro i r w v
    have h1 : combTup (Function.update w i (r • w i)) v
        = Function.update (combTup w v) (Fin.castAdd 4 i) (r • w i) :=
      combTup_update_left w v i (r • w i)
    have h3 : Function.update (combTup w v) (Fin.castAdd 4 i) (w i) = combTup w v := by
      rw [← combTup_castAdd (w := w) (v := v) (i := i)]
      exact Function.update_eq_self _ _
    have hK : Kpt g x k (Function.update (combTup w v) (Fin.castAdd 4 i) (r • w i))
        = r • Kpt g x k (combTup w v) := by
      have hh := Kpt_smul hLC g x k (combTup w v) (Fin.castAdd 4 i) r (w i)
      rwa [h3] at hh
    rw [krV_eq_Kpt, krV_eq_Kpt, h1, hK, smul_eq_mul]
  · intro j w v v'
    have h1 : combTup w (Function.update v j (v j + v'))
        = Function.update (combTup w v) (Fin.natAdd k j) (v j + v') :=
      combTup_update_right w v j (v j + v')
    have h2 : combTup w (Function.update v j v')
        = Function.update (combTup w v) (Fin.natAdd k j) v' :=
      combTup_update_right w v j v'
    have h3 : Function.update (combTup w v) (Fin.natAdd k j) (v j) = combTup w v := by
      rw [← combTup_natAdd (w := w) (v := v) (j := j)]
      exact Function.update_eq_self _ _
    have hK : Kpt g x k (Function.update (combTup w v) (Fin.natAdd k j) (v j + v'))
        = Kpt g x k (combTup w v)
          + Kpt g x k (Function.update (combTup w v) (Fin.natAdd k j) v') := by
      have hh := Kpt_add hLC g x k (combTup w v) (Fin.natAdd k j) (v j) v'
      rwa [h3] at hh
    rw [krV_eq_Kpt, krV_eq_Kpt, krV_eq_Kpt, h1, h2, hK]
  · intro j r w v
    have h1 : combTup w (Function.update v j (r • v j))
        = Function.update (combTup w v) (Fin.natAdd k j) (r • v j) :=
      combTup_update_right w v j (r • v j)
    have h3 : Function.update (combTup w v) (Fin.natAdd k j) (v j) = combTup w v := by
      rw [← combTup_natAdd (w := w) (v := v) (j := j)]
      exact Function.update_eq_self _ _
    have hK : Kpt g x k (Function.update (combTup w v) (Fin.natAdd k j) (r • v j))
        = r • Kpt g x k (combTup w v) := by
      have hh := Kpt_smul hLC g x k (combTup w v) (Fin.natAdd k j) r (v j)
      rwa [h3] at hh
    rw [krV_eq_Kpt, krV_eq_Kpt, h1, hK, smul_eq_mul]

/-! ## The target statement

The value-dependence `KrValueDep` for fields that are merely `C^∞` *at* `x` (Mathlib's weak
`ContMDiffAt ∞`, which does **not** imply smoothness on a neighbourhood) needs the tower to be
developed at the "smooth at a point" level: the fields occurring in `KrValueDep` are not smooth on
any neighbourhood of `x`, so the bump/cut-off route (and `KrGerm`, whose hypotheses are the same
weak ones) does not apply directly.  The plan is:

* `rmP_field_contMDiffAt` (delegated): `y ↦ rmP g y (A y) (B y) (C y) (D y)` is `C^∞` at `x` for
  fields that are `C^∞` at `x`;
* `dirF_contMDiffAt` (delegated): `y ↦ lcOf g Z y (V y)` is `C^∞` at `x` for such fields;
* these give, by induction over the defining recursion of `covKRmExt`, that the tower is `C^∞` at
  `x` and `C^∞(M)`-linear in each slot for fields that are `C^∞` at `x` (with the Leibniz rules for
  `mvfderiv` and `lcOf` as the inductive step);
* combined with the frame decomposition of a field that is `C^∞` at `x` and vanishes at `x`
  (`frame_decomp_at`, delegated) and the germ-locality `hG`, this yields `KrValueDep`. -/

/-- **Value-dependence (tensoriality) of `∇^k Rm`, and multilinearity in the values.**
Assuming the field-level linearity `KrLinear g k` and the germ-locality `KrGerm g k` (both in
`Submission/Work/Diff/EXT/curvDefs.lean`, to be supplied by `covK_linear` and `covK_germ`), the value
of `covKRmExt g k V A B C D` at `x` depends only on the values at `x` of the `k + 4` fields
(`KrValueDep`); consequently the components `krV g x k` of `∇^k Rm` are multilinear in the `k + 4`
tangent vectors (`KrMulti`). -/
theorem covK_valueDep
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [T2Space M] (hLC : Submission.Diff.LCSmooth I M)
    (g : Submission.Diff.SMet I M) (k : ℕ)
    (hL : KrLinear (I := I) (M := M) g k) (hG : KrGerm (I := I) (M := M) g k) :
    KrValueDep (I := I) (M := M) g k ∧ ∀ x : M, KrMulti (I := I) (M := M) g x k := by
  refine ⟨?_, fun x => KrMulti_of_Kpt (I := I) (M := M) hLC g x k⟩
  sorry

end Work.Diff.EXT
