import Mathlib
import Submission.Work.Diff.EXT.LocalExtDefs
import Submission.Work.Diff.GE.curvbasic

/-!
# Vocabulary for the joint smoothness of `|∇^k Rm|²` (area EXT)

This module only contains definitions and definitional lemmas, in the vocabulary of the frozen
file `Submission/Work/Diff/EXT/local_ext_of_bounded_curv.lean` (`covKRmExt`, `covKRmC`,
`curvNormK`, `NormSmoothK`, `joint`/`JointSmooth`, `IsRicciFlow`).

It is the interface module for `Work.Diff.EXT.curvNormK_jointSmooth` and can be imported freely.

WARNING for importers: this module imports `Submission.Work.Diff.GE.curvbasic`, whose constants
`Work.Diff.GE.exists_isONFrame` / `Work.Diff.GE.isONFrame_onFrame` clash with those of
`Submission.Work.Diff.GE.bianchi_kato_defs` (and hence with `Submission.Work.Diff.GE.smooth_onframe`
and `Submission.Work.EXT.exists_smooth_ONFrame`).  Do **not** import any of those in files that
import this one.

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-/

namespace Work.Diff.EXT

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- A tangent field on `M`. -/
abbrev TField : Type _ := Π y : M, TangentSpace I y

/-- A tangent field which is `C^∞`. -/
abbrev SmoothTField (X : TField (I := I) (M := M)) : Prop := CMDiff ∞ (T% X)

/-- A tangent field which is `C^∞` at a point. -/
abbrev SmoothTFieldAt (X : TField (I := I) (M := M)) (x : M) : Prop :=
  ContMDiffAt I I.tangent ∞ (T% X) x

/-- A family of metrics is jointly smooth on a set `V ⊆ ℝ × M` (section of bilinear forms). -/
def JointMet (G : ℝ → Submission.Diff.SMet I M) (V : Set (ℝ × M)) : Prop :=
  ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
    (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) p.2
      ((G p.1).inner p.2)) V

/-- A family of tangent fields is jointly smooth on a set `V ⊆ ℝ × M`. -/
def JointField (X : ℝ → TField (I := I) (M := M)) (V : Set (ℝ × M)) : Prop :=
  ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) I.tangent ∞
    (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)) V

/-- `JointSmooth G J` is `JointMet G (J ×ˢ univ)`, definitionally. -/
theorem jointMet_prod (G : ℝ → Submission.Diff.SMet I M) (J : Set ℝ) :
    JointSmooth G J ↔ JointMet (I := I) (M := M) G (J ×ˢ (univ : Set M)) := Iff.rfl

/-- The `k`-th covariant derivative of the curvature as a `(0,k+4)`-tensor: its value on `k + 4`
tangent vectors, computed with `Classical.epsilon`-chosen smooth extensions. -/
noncomputable def covKRm (g : Submission.Diff.SMet I M) (x : M) (k : ℕ)
    (v : Fin k → TangentSpace I x) (a b c d : TangentSpace I x) : ℝ :=
  covKRmExt g k (fun s => smoothExt x (v s)) (smoothExt x a) (smoothExt x b)
    (smoothExt x c) (smoothExt x d) x

/-- The components of `∇^k Rm` in a frame are `covKRm` on the frame vectors. -/
theorem covKRmC_eq_covKRm (g : Submission.Diff.SMet I M) (x : M) (k : ℕ)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (ι : Fin k → Fin (Module.finrank ℝ E)) (i j l m : Fin (Module.finrank ℝ E)) :
    covKRmC g x e k ι i j l m =
      covKRm g x k (fun s => e (ι s)) (e i) (e j) (e l) (e m) := rfl

/-- `curvNormK` as the sum of squares of `covKRm` in the chosen orthonormal frame. -/
theorem curvNormK_eq_sum_covKRm (g : Submission.Diff.SMet I M) (x : M) (k : ℕ) :
    curvNormK g x k = ∑ ι : Fin k → Fin (Module.finrank ℝ E), ∑ i, ∑ j, ∑ l, ∑ m,
      (covKRm g x k (fun s => onFrame g x (ι s)) (onFrame g x i) (onFrame g x j)
        (onFrame g x l) (onFrame g x m)) ^ 2 := rfl




/-- `krE g k V F` is `covKRmExt g k` with the four curvature slots packaged as a `Fin 4`-tuple. -/
noncomputable def krE (g : Submission.Diff.SMet I M) (k : ℕ)
    (V : Fin k → TField (I := I) (M := M)) (F : Fin 4 → TField (I := I) (M := M)) : M → ℝ :=
  covKRmExt g k V (F 0) (F 1) (F 2) (F 3)

/-- `krV g x k w v` is `∇^k Rm` at `x` on the `k + 4` tangent vectors `w ·` and `v 0,…,v 3`. -/
noncomputable def krV (g : Submission.Diff.SMet I M) (x : M) (k : ℕ)
    (w : Fin k → TangentSpace I x) (v : Fin 4 → TangentSpace I x) : ℝ :=
  covKRm g x k w (v 0) (v 1) (v 2) (v 3)

/-- **`C^∞(M)`-linearity of `∇^k Rm` in its field slots** (the field-level tensor is linear in
each of the `k` derivative slots and each of the four curvature slots). -/
def KrLinear (g : Submission.Diff.SMet I M) (k : ℕ) : Prop :=
  (∀ (i : Fin k) (V : Fin k → TField (I := I) (M := M))
      (V' : TField (I := I) (M := M)) (A B C D : TField (I := I) (M := M)),
    (∀ j, SmoothTField (I := I) (M := M) (V j)) → SmoothTField (I := I) (M := M) V' →
    SmoothTField (I := I) (M := M) A → SmoothTField (I := I) (M := M) B →
    SmoothTField (I := I) (M := M) C → SmoothTField (I := I) (M := M) D →
    covKRmExt g k (Function.update V i (V i + V')) A B C D
      = covKRmExt g k V A B C D + covKRmExt g k (Function.update V i V') A B C D) ∧
  (∀ (i : Fin k) (V : Fin k → TField (I := I) (M := M)) (f : M → ℝ)
      (A B C D : TField (I := I) (M := M)),
    CMDiff ∞ f → (∀ j, SmoothTField (I := I) (M := M) (V j)) →
    SmoothTField (I := I) (M := M) A → SmoothTField (I := I) (M := M) B →
    SmoothTField (I := I) (M := M) C → SmoothTField (I := I) (M := M) D →
    covKRmExt g k (Function.update V i (f • V i)) A B C D = f • covKRmExt g k V A B C D) ∧
  (∀ (V : Fin k → TField (I := I) (M := M)) (A : TField (I := I) (M := M))
      (A' : TField (I := I) (M := M)) (B C D : TField (I := I) (M := M)),
    (∀ j, SmoothTField (I := I) (M := M) (V j)) → SmoothTField (I := I) (M := M) A →
    SmoothTField (I := I) (M := M) A' → SmoothTField (I := I) (M := M) B →
    SmoothTField (I := I) (M := M) C → SmoothTField (I := I) (M := M) D →
    covKRmExt g k V (A + A') B C D = covKRmExt g k V A B C D + covKRmExt g k V A' B C D) ∧
  (∀ (V : Fin k → TField (I := I) (M := M)) (f : M → ℝ) (A B C D : TField (I := I) (M := M)),
    CMDiff ∞ f → (∀ j, SmoothTField (I := I) (M := M) (V j)) →
    SmoothTField (I := I) (M := M) A → SmoothTField (I := I) (M := M) B →
    SmoothTField (I := I) (M := M) C → SmoothTField (I := I) (M := M) D →
    covKRmExt g k V (f • A) B C D = f • covKRmExt g k V A B C D) ∧
  (∀ (V : Fin k → TField (I := I) (M := M)) (A B : TField (I := I) (M := M))
      (B' : TField (I := I) (M := M)) (C D : TField (I := I) (M := M)),
    (∀ j, SmoothTField (I := I) (M := M) (V j)) → SmoothTField (I := I) (M := M) A →
    SmoothTField (I := I) (M := M) B → SmoothTField (I := I) (M := M) B' →
    SmoothTField (I := I) (M := M) C → SmoothTField (I := I) (M := M) D →
    covKRmExt g k V A (B + B') C D = covKRmExt g k V A B C D + covKRmExt g k V A B' C D) ∧
  (∀ (V : Fin k → TField (I := I) (M := M)) (f : M → ℝ) (A B C D : TField (I := I) (M := M)),
    CMDiff ∞ f → (∀ j, SmoothTField (I := I) (M := M) (V j)) →
    SmoothTField (I := I) (M := M) A → SmoothTField (I := I) (M := M) B →
    SmoothTField (I := I) (M := M) C → SmoothTField (I := I) (M := M) D →
    covKRmExt g k V A (f • B) C D = f • covKRmExt g k V A B C D) ∧
  (∀ (V : Fin k → TField (I := I) (M := M)) (A B C : TField (I := I) (M := M))
      (C' : TField (I := I) (M := M)) (D : TField (I := I) (M := M)),
    (∀ j, SmoothTField (I := I) (M := M) (V j)) → SmoothTField (I := I) (M := M) A →
    SmoothTField (I := I) (M := M) B → SmoothTField (I := I) (M := M) C →
    SmoothTField (I := I) (M := M) C' → SmoothTField (I := I) (M := M) D →
    covKRmExt g k V A B (C + C') D = covKRmExt g k V A B C D + covKRmExt g k V A B C' D) ∧
  (∀ (V : Fin k → TField (I := I) (M := M)) (f : M → ℝ) (A B C D : TField (I := I) (M := M)),
    CMDiff ∞ f → (∀ j, SmoothTField (I := I) (M := M) (V j)) →
    SmoothTField (I := I) (M := M) A → SmoothTField (I := I) (M := M) B →
    SmoothTField (I := I) (M := M) C → SmoothTField (I := I) (M := M) D →
    covKRmExt g k V A B (f • C) D = f • covKRmExt g k V A B C D) ∧
  (∀ (V : Fin k → TField (I := I) (M := M)) (A B C : TField (I := I) (M := M))
      (D : TField (I := I) (M := M)) (D' : TField (I := I) (M := M)),
    (∀ j, SmoothTField (I := I) (M := M) (V j)) → SmoothTField (I := I) (M := M) A →
    SmoothTField (I := I) (M := M) B → SmoothTField (I := I) (M := M) C →
    SmoothTField (I := I) (M := M) D → SmoothTField (I := I) (M := M) D' →
    covKRmExt g k V A B C (D + D') = covKRmExt g k V A B C D + covKRmExt g k V A B C D') ∧
  (∀ (V : Fin k → TField (I := I) (M := M)) (f : M → ℝ) (A B C D : TField (I := I) (M := M)),
    CMDiff ∞ f → (∀ j, SmoothTField (I := I) (M := M) (V j)) →
    SmoothTField (I := I) (M := M) A → SmoothTField (I := I) (M := M) B →
    SmoothTField (I := I) (M := M) C → SmoothTField (I := I) (M := M) D →
    covKRmExt g k V A B C (f • D) = f • covKRmExt g k V A B C D)

/-- **Germ-locality of `∇^k Rm`**: the value at `x` depends only on the germs of the arguments. -/
def KrGerm (g : Submission.Diff.SMet I M) (k : ℕ) : Prop :=
  ∀ (V V' : Fin k → TField (I := I) (M := M)) (A A' B B' C C' D D' : TField (I := I) (M := M))
    (x : M),
    (∀ j, SmoothTFieldAt (I := I) (M := M) (V j) x) →
    (∀ j, SmoothTFieldAt (I := I) (M := M) (V' j) x) →
    SmoothTFieldAt (I := I) (M := M) A x → SmoothTFieldAt (I := I) (M := M) A' x →
    SmoothTFieldAt (I := I) (M := M) B x → SmoothTFieldAt (I := I) (M := M) B' x →
    SmoothTFieldAt (I := I) (M := M) C x → SmoothTFieldAt (I := I) (M := M) C' x →
    SmoothTFieldAt (I := I) (M := M) D x → SmoothTFieldAt (I := I) (M := M) D' x →
    (∀ j, V j =ᶠ[𝓝 x] V' j) → A =ᶠ[𝓝 x] A' → B =ᶠ[𝓝 x] B' → C =ᶠ[𝓝 x] C' →
    D =ᶠ[𝓝 x] D' → covKRmExt g k V A B C D x = covKRmExt g k V' A' B' C' D' x

/-- **Value-dependence of `∇^k Rm`**: the value at `x` depends only on the values of the arguments
at `x`.  (This is the tensoriality of the covariant derivative tower.) -/
def KrValueDep (g : Submission.Diff.SMet I M) (k : ℕ) : Prop :=
  ∀ (V V' : Fin k → TField (I := I) (M := M)) (A A' B B' C C' D D' : TField (I := I) (M := M))
    (x : M),
    (∀ j, SmoothTFieldAt (I := I) (M := M) (V j) x) →
    (∀ j, SmoothTFieldAt (I := I) (M := M) (V' j) x) →
    SmoothTFieldAt (I := I) (M := M) A x → SmoothTFieldAt (I := I) (M := M) A' x →
    SmoothTFieldAt (I := I) (M := M) B x → SmoothTFieldAt (I := I) (M := M) B' x →
    SmoothTFieldAt (I := I) (M := M) C x → SmoothTFieldAt (I := I) (M := M) C' x →
    SmoothTFieldAt (I := I) (M := M) D x → SmoothTFieldAt (I := I) (M := M) D' x →
    (∀ j, V j x = V' j x) → A x = A' x → B x = B' x → C x = C' x → D x = D' x →
    covKRmExt g k V A B C D x = covKRmExt g k V' A' B' C' D' x

/-- **Multilinearity in the values**: the components `krV g x k` form a multilinear function of the
`k + 4` tangent vectors. -/
def KrMulti (g : Submission.Diff.SMet I M) (x : M) (k : ℕ) : Prop :=
  (∀ (i : Fin k) (w : Fin k → TangentSpace I x) (w' : TangentSpace I x)
      (v : Fin 4 → TangentSpace I x),
    krV g x k (Function.update w i (w i + w')) v
      = krV g x k w v + krV g x k (Function.update w i w') v) ∧
  (∀ (i : Fin k) (r : ℝ) (w : Fin k → TangentSpace I x) (v : Fin 4 → TangentSpace I x),
    krV g x k (Function.update w i (r • w i)) v = r * krV g x k w v) ∧
  (∀ (j : Fin 4) (w : Fin k → TangentSpace I x) (v : Fin 4 → TangentSpace I x)
      (v' : TangentSpace I x),
    krV g x k w (Function.update v j (v j + v'))
      = krV g x k w v + krV g x k w (Function.update v j v')) ∧
  (∀ (j : Fin 4) (r : ℝ) (w : Fin k → TangentSpace I x) (v : Fin 4 → TangentSpace I x),
    krV g x k w (Function.update v j (r • v j)) = r * krV g x k w v)


end Work.Diff.EXT
