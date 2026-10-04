import Mathlib
import Submission.Work.Diff.GE.RL.Kit
import Submission.Work.Diff.GE.RL.roughLap_rot_abstract
import Submission.Work.Diff.GE.RL.covRm_linear_fst
import Submission.Work.Diff.PP.evolution
import Submission.Work.Diff.GE.Frame
import Submission.Work.Diff.GE.kato_cov3RmExt_field

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Frame-change law of the rough Laplacian (`roughLap_rot`)

`Work.Diff.PP.roughLap g x e i j k l = ∑ m, cov2Rm g x (e m) (e m) (e i) (e j) (e k) (e l)` is the
trace `ΔRm = tr_g ∇²Rm` of the `(0,6)`-tensor `∇²Rm`, computed in the frame `e`.  Since `∇²Rm` is a
tensor, this trace is a `(0,4)`-tensor, so when the frame is changed by an orthogonal matrix `A`
(`e' i = ∑ j, A i j • e j`), the components transform by `Submission.Diff.Alg.rot A`:

`roughLap g x e' = rot A (roughLap g x e)`.

The proof has two ingredients:

* **multilinearity of `∇²Rm`.**  `Work.Diff.GE.cov2Rm` (the `(0,6)`-tensor `∇²Rm`, definitionally
  equal to `Work.Diff.PP.cov2Rm` after unfolding the `Classical.epsilon` extension
  `smoothExt` via `smoothExt_apply`) is `ℝ`-linear in each of its six arguments — the six lemmas
  `Work.Diff.GE.Kato3.cov2Rm_lin_{first,snd,thd,fth,fif,sixth}` proved in
  `Submission/Work/Diff/GE/kato_cov3RmExt_field.lean`.  From this we get the nested-sum expansion
  `pp_cov2Rm_expand` for `Work.Diff.PP.cov2Rm` (the translation `pp_cov2Rm_eq` between the two
  definitions is the rewriting of `smoothExt x v x` to `v`).

* **the algebraic trace computation** `Work.Diff.GE.RL.roughLap_rot_abstract`, which contracts the
  doubled index (`∑ m, A m p * A m q` is the Kronecker delta by orthogonality of `A`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE

/-- If `f : V → ℝ` is `ℝ`-linear (additive and homogeneous), then its value on a finite sum
`∑ i, c i • u i` is `∑ i, c i * f (u i)`. -/
private theorem lin_sum_expand {V : Type*} [AddCommMonoid V] [Module ℝ V] {ι : Type*} [Fintype ι]
    (f : V → ℝ) (hf : ∀ (r s : ℝ) (x y : V), f (r • x + s • y) = r * f x + s * f y)
    (c : ι → ℝ) (u : ι → V) :
    f (∑ i, c i • u i) = ∑ i, c i * f (u i) := by
  let φ : V →ₗ[ℝ] ℝ :=
    { toFun := f
      map_add' := fun x y => by
        have h := hf 1 1 x y
        simpa using h
      map_smul' := fun r x => by
        have h := hf r 0 x x
        simpa using h }
  calc f (∑ i, c i • u i) = φ (∑ i, c i • u i) := rfl
    _ = ∑ i, φ (c i • u i) := map_sum φ _ _
    _ = ∑ i, c i * f (u i) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [map_smul]
        rfl

/-- The two definitions of `∇²Rm` (one in `Submission/Work/Diff/PP/evolution.lean`, one in
`Submission/Work/Diff/GE/NablaRm.lean`) coincide: they differ only by the rewriting of the
`Classical.epsilon` extension `smoothExt x v` at its base point. -/
theorem pp_cov2Rm_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (g : SMet I M) (x : M) (v w a b c d : TangentSpace I x) :
    Work.Diff.PP.cov2Rm g x v w a b c d = Work.Diff.GE.cov2Rm g x v w a b c d := by
  simp only [Work.Diff.PP.cov2Rm, Work.Diff.GE.cov2Rm, Work.Diff.GE.cov2RmExt,
    Work.Diff.GE.smoothExt_apply]

/-- `∇²Rm` is `ℝ`-linear in its first argument, for the definition of
`Submission/Work/Diff/PP/evolution.lean`. -/
theorem pp_cov2Rm_lin_first
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (hLC : LCSmooth I M) (g : SMet I M) (x : M) (r s : ℝ) (v₁ v₂ w a b c d : TangentSpace I x) :
    Work.Diff.PP.cov2Rm g x (r • v₁ + s • v₂) w a b c d
      = r * Work.Diff.PP.cov2Rm g x v₁ w a b c d + s * Work.Diff.PP.cov2Rm g x v₂ w a b c d := by
  rw [pp_cov2Rm_eq (g := g) x (r • v₁ + s • v₂) w a b c d, pp_cov2Rm_eq (g := g) x v₁ w a b c d,
    pp_cov2Rm_eq (g := g) x v₂ w a b c d]
  exact Work.Diff.GE.Kato3.cov2Rm_lin_first hLC g x r s v₁ v₂ w a b c d

/-- `∇²Rm` is `ℝ`-linear in its second argument, for the definition of
`Submission/Work/Diff/PP/evolution.lean`. -/
theorem pp_cov2Rm_lin_snd
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (hLC : LCSmooth I M) (g : SMet I M) (x : M) (r s : ℝ) (v w₁ w₂ a b c d : TangentSpace I x) :
    Work.Diff.PP.cov2Rm g x v (r • w₁ + s • w₂) a b c d
      = r * Work.Diff.PP.cov2Rm g x v w₁ a b c d + s * Work.Diff.PP.cov2Rm g x v w₂ a b c d := by
  rw [pp_cov2Rm_eq (g := g) x v (r • w₁ + s • w₂) a b c d, pp_cov2Rm_eq (g := g) x v w₁ a b c d,
    pp_cov2Rm_eq (g := g) x v w₂ a b c d]
  exact Work.Diff.GE.Kato3.cov2Rm_lin_snd hLC g x r s v w₁ w₂ a b c d

/-- `∇²Rm` is `ℝ`-linear in its third argument, for the definition of
`Submission/Work/Diff/PP/evolution.lean`. -/
theorem pp_cov2Rm_lin_thd
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (hLC : LCSmooth I M) (g : SMet I M) (x : M) (r s : ℝ) (v w a₁ a₂ b c d : TangentSpace I x) :
    Work.Diff.PP.cov2Rm g x v w (r • a₁ + s • a₂) b c d
      = r * Work.Diff.PP.cov2Rm g x v w a₁ b c d + s * Work.Diff.PP.cov2Rm g x v w a₂ b c d := by
  rw [pp_cov2Rm_eq (g := g) x v w (r • a₁ + s • a₂) b c d, pp_cov2Rm_eq (g := g) x v w a₁ b c d,
    pp_cov2Rm_eq (g := g) x v w a₂ b c d]
  exact Work.Diff.GE.Kato3.cov2Rm_lin_thd hLC g x r s v w a₁ a₂ b c d

/-- `∇²Rm` is `ℝ`-linear in its fourth argument, for the definition of
`Submission/Work/Diff/PP/evolution.lean`. -/
theorem pp_cov2Rm_lin_fth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (hLC : LCSmooth I M) (g : SMet I M) (x : M) (r s : ℝ) (v w a b₁ b₂ c d : TangentSpace I x) :
    Work.Diff.PP.cov2Rm g x v w a (r • b₁ + s • b₂) c d
      = r * Work.Diff.PP.cov2Rm g x v w a b₁ c d + s * Work.Diff.PP.cov2Rm g x v w a b₂ c d := by
  rw [pp_cov2Rm_eq (g := g) x v w a (r • b₁ + s • b₂) c d,
    pp_cov2Rm_eq (g := g) x v w a b₁ c d, pp_cov2Rm_eq (g := g) x v w a b₂ c d]
  exact Work.Diff.GE.Kato3.cov2Rm_lin_fth hLC g x r s v w a b₁ b₂ c d

/-- `∇²Rm` is `ℝ`-linear in its fifth argument, for the definition of
`Submission/Work/Diff/PP/evolution.lean`. -/
theorem pp_cov2Rm_lin_fif
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (hLC : LCSmooth I M) (g : SMet I M) (x : M) (r s : ℝ) (v w a b c₁ c₂ d : TangentSpace I x) :
    Work.Diff.PP.cov2Rm g x v w a b (r • c₁ + s • c₂) d
      = r * Work.Diff.PP.cov2Rm g x v w a b c₁ d + s * Work.Diff.PP.cov2Rm g x v w a b c₂ d := by
  rw [pp_cov2Rm_eq (g := g) x v w a b (r • c₁ + s • c₂) d,
    pp_cov2Rm_eq (g := g) x v w a b c₁ d, pp_cov2Rm_eq (g := g) x v w a b c₂ d]
  exact Work.Diff.GE.Kato3.cov2Rm_lin_fif hLC g x r s v w a b c₁ c₂ d

/-- `∇²Rm` is `ℝ`-linear in its sixth argument, for the definition of
`Submission/Work/Diff/PP/evolution.lean`. -/
theorem pp_cov2Rm_lin_sixth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (hLC : LCSmooth I M) (g : SMet I M) (x : M) (r s : ℝ) (v w a b c d₁ d₂ : TangentSpace I x) :
    Work.Diff.PP.cov2Rm g x v w a b c (r • d₁ + s • d₂)
      = r * Work.Diff.PP.cov2Rm g x v w a b c d₁ + s * Work.Diff.PP.cov2Rm g x v w a b c d₂ := by
  rw [pp_cov2Rm_eq (g := g) x v w a b c (r • d₁ + s • d₂),
    pp_cov2Rm_eq (g := g) x v w a b c d₁, pp_cov2Rm_eq (g := g) x v w a b c d₂]
  exact Work.Diff.GE.Kato3.cov2Rm_lin_sixth hLC g x r s v w a b c d₁ d₂

/-- Multilinearity of `∇²Rm` in all six arguments as a nested sum: for any coefficients `cᵢ` and
vectors `uᵢ`,
`∇²Rm (∑ a, c₁ a • u₁ a) … (∑ f, c₆ f • u₆ f) = ∑ a, … , ∑ f, c₁ a * … * c₆ f * ∇²Rm (u₁ a) … (u₆ f)`.
This is the computational content of the fact that `∇²Rm` is a `(0,6)`-tensor. -/
theorem pp_cov2Rm_expand
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (hLC : LCSmooth I M) (g : SMet I M) (x : M) :
    ∀ (c₁ c₂ c₃ c₄ c₅ c₆ : Fin (Module.finrank ℝ E) → ℝ)
      (u₁ u₂ u₃ u₄ u₅ u₆ : Fin (Module.finrank ℝ E) → TangentSpace I x),
      Work.Diff.PP.cov2Rm g x (∑ a, c₁ a • u₁ a) (∑ b, c₂ b • u₂ b) (∑ c, c₃ c • u₃ c)
        (∑ d, c₄ d • u₄ d) (∑ e, c₅ e • u₅ e) (∑ f, c₆ f • u₆ f)
      = ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, c₁ a * c₂ b * c₃ c * c₄ d * c₅ e * c₆ f
          * Work.Diff.PP.cov2Rm g x (u₁ a) (u₂ b) (u₃ c) (u₄ d) (u₅ e) (u₆ f) := by
  intro c₁ c₂ c₃ c₄ c₅ c₆ u₁ u₂ u₃ u₄ u₅ u₆
  have hsum1 : ∀ (w a b c d : TangentSpace I x) (cc : Fin (Module.finrank ℝ E) → ℝ)
      (uu : Fin (Module.finrank ℝ E) → TangentSpace I x),
      Work.Diff.PP.cov2Rm g x (∑ p, cc p • uu p) w a b c d
        = ∑ p, cc p * Work.Diff.PP.cov2Rm g x (uu p) w a b c d := by
    intro w a b c d cc uu
    exact lin_sum_expand (fun z => Work.Diff.PP.cov2Rm g x z w a b c d)
      (fun r s z₁ z₂ => pp_cov2Rm_lin_first hLC g x r s z₁ z₂ w a b c d) cc uu
  have hsum2 : ∀ (v a b c d : TangentSpace I x) (cc : Fin (Module.finrank ℝ E) → ℝ)
      (uu : Fin (Module.finrank ℝ E) → TangentSpace I x),
      Work.Diff.PP.cov2Rm g x v (∑ p, cc p • uu p) a b c d
        = ∑ p, cc p * Work.Diff.PP.cov2Rm g x v (uu p) a b c d := by
    intro v a b c d cc uu
    exact lin_sum_expand (fun z => Work.Diff.PP.cov2Rm g x v z a b c d)
      (fun r s z₁ z₂ => pp_cov2Rm_lin_snd hLC g x r s v z₁ z₂ a b c d) cc uu
  have hsum3 : ∀ (v w b c d : TangentSpace I x) (cc : Fin (Module.finrank ℝ E) → ℝ)
      (uu : Fin (Module.finrank ℝ E) → TangentSpace I x),
      Work.Diff.PP.cov2Rm g x v w (∑ p, cc p • uu p) b c d
        = ∑ p, cc p * Work.Diff.PP.cov2Rm g x v w (uu p) b c d := by
    intro v w b c d cc uu
    exact lin_sum_expand (fun z => Work.Diff.PP.cov2Rm g x v w z b c d)
      (fun r s z₁ z₂ => pp_cov2Rm_lin_thd hLC g x r s v w z₁ z₂ b c d) cc uu
  have hsum4 : ∀ (v w a c d : TangentSpace I x) (cc : Fin (Module.finrank ℝ E) → ℝ)
      (uu : Fin (Module.finrank ℝ E) → TangentSpace I x),
      Work.Diff.PP.cov2Rm g x v w a (∑ p, cc p • uu p) c d
        = ∑ p, cc p * Work.Diff.PP.cov2Rm g x v w a (uu p) c d := by
    intro v w a c d cc uu
    exact lin_sum_expand (fun z => Work.Diff.PP.cov2Rm g x v w a z c d)
      (fun r s z₁ z₂ => pp_cov2Rm_lin_fth hLC g x r s v w a z₁ z₂ c d) cc uu
  have hsum5 : ∀ (v w a b d : TangentSpace I x) (cc : Fin (Module.finrank ℝ E) → ℝ)
      (uu : Fin (Module.finrank ℝ E) → TangentSpace I x),
      Work.Diff.PP.cov2Rm g x v w a b (∑ p, cc p • uu p) d
        = ∑ p, cc p * Work.Diff.PP.cov2Rm g x v w a b (uu p) d := by
    intro v w a b d cc uu
    exact lin_sum_expand (fun z => Work.Diff.PP.cov2Rm g x v w a b z d)
      (fun r s z₁ z₂ => pp_cov2Rm_lin_fif hLC g x r s v w a b z₁ z₂ d) cc uu
  have hsum6 : ∀ (v w a b c : TangentSpace I x) (cc : Fin (Module.finrank ℝ E) → ℝ)
      (uu : Fin (Module.finrank ℝ E) → TangentSpace I x),
      Work.Diff.PP.cov2Rm g x v w a b c (∑ p, cc p • uu p)
        = ∑ p, cc p * Work.Diff.PP.cov2Rm g x v w a b c (uu p) := by
    intro v w a b c cc uu
    exact lin_sum_expand (fun z => Work.Diff.PP.cov2Rm g x v w a b c z)
      (fun r s z₁ z₂ => pp_cov2Rm_lin_sixth hLC g x r s v w a b c z₁ z₂) cc uu
  rw [hsum1]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [hsum2]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [hsum3]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [hsum4]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [hsum5]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [hsum6]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun f _ => ?_)
  ring

theorem roughLap_rot
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (e e' : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (A : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
    (hA : ∀ i, e' i = ∑ j, A i j • e j)
    (hAO : A ∈ Matrix.orthogonalGroup (Fin (Module.finrank ℝ E)) ℝ) :
    Work.Diff.PP.roughLap g x e'
      = Submission.Diff.Alg.rot A (Work.Diff.PP.roughLap g x e) := by
  have hmem := pp_cov2Rm_expand (I := I) (M := M) hLC g x
  ext i j k l
  simp only [Work.Diff.PP.roughLap, Submission.Diff.Alg.rot]
  simp_rw [hA]
  have hin : ∀ m, Work.Diff.PP.cov2Rm g x (∑ p, A m p • e p) (∑ q, A m q • e q)
        (∑ r, A i r • e r) (∑ s, A j s • e s) (∑ t, A k t • e t) (∑ u, A l u • e u)
      = ∑ p, ∑ q, ∑ r, ∑ s, ∑ t, ∑ u,
          A m p * A m q * A i r * A j s * A k t * A l u
            * Work.Diff.PP.cov2Rm g x (e p) (e q) (e r) (e s) (e t) (e u) :=
    fun m => hmem (A m) (A m) (A i) (A j) (A k) (A l) e e e e e e
  simp only [hin]
  rw [Work.Diff.GE.RL.roughLap_rot_abstract A hAO
      (fun p q r s t u => Work.Diff.PP.cov2Rm g x (e p) (e q) (e r) (e s) (e t) (e u)) i j k l]

end Work.Diff.GE
