import Mathlib
import Submission.Work.Diff.Evol.Vocab
import Submission.Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
import Submission.Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The second-order Leibniz rule for `∇_W` (Levi-Civita connection of a smooth metric)

`Work.Diff.Evol.lcOf_transition_second` computes the *second* covariant derivative
`∇_W ∇_W S` at a point `x`, where `S = ∑_p A_{p,i} F_p` is a finite sum of smooth sections with
smooth point-dependent scalar coefficients, and `W` is a fixed smooth field.

The lemma is a pure consequence of the two structural axioms of a covariant derivative
(`IsCovariantDerivativeOn.add` and `IsCovariantDerivativeOn.leibniz`) together with smoothness of
the sections involved:

* `∇_W (∑_p f_p X_p) = ∑_p (f_p • ∇_W X_p + (∇_W f_p) • X_p)`  (finite sum rule),
* applying it twice gives the second order rule
  `∇_W∇_W(f • X) = f • ∇_W∇_W X + 2 • ((∇_W f) • ∇_W X) + (∇_W∇_W f) • X`.

The helpers below (`dirF`, `smoothF_*`, `cov_sum`, `dirF_add`, `dirF_smul`, `dirF_sum`,
`dirF_smooth`, `dirF_smul2`, `dirF_second_sum`) are the general form of the two rules; the target
theorem is the instance needed by the `Evol` area.
-/

namespace Work.Diff.Evol

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M] [I.Boundaryless] [T2Space M]

/-- The field `∇_W X`, for the Levi-Civita connection of the smooth metric `g`. -/
noncomputable def dirF (g : Submission.Diff.SMet I M) (X v : Π y : M, TangentSpace I y) :
    Π y : M, TangentSpace I y := fun y => Submission.Diff.lcOf g X y (v y)

/-! ## Smoothness of tangent fields -/

lemma smoothF_zero : SmoothField I M (0 : Π y : M, TangentSpace I y) :=
  contMDiff_zeroSection ℝ (TangentSpace I)

lemma smoothF_add {X Y : Π y : M, TangentSpace I y} (hX : SmoothField I M X)
    (hY : SmoothField I M Y) : SmoothField I M (X + Y) := hX.add_section hY

lemma smoothF_smul {f : M → ℝ} {X : Π y : M, TangentSpace I y} (hf : CMDiff ∞ f)
    (hX : SmoothField I M X) : SmoothField I M (f • X) := hf.smul_section hX

lemma smoothF_sum {ι : Type*} (s : Finset ι) (X : ι → Π y : M, TangentSpace I y)
    (hX : ∀ i ∈ s, SmoothField I M (X i)) :
    SmoothField I M (fun y : M => ∑ i ∈ s, X i y) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have h0 : (fun y : M => ∑ i ∈ (∅ : Finset ι), X i y) = 0 := by funext y; simp
      rw [h0]; exact smoothF_zero
  | insert a t ha ih =>
      have h1 : (fun y : M => ∑ i ∈ insert a t, X i y) = X a + fun y : M => ∑ i ∈ t, X i y := by
        funext y; rw [Finset.sum_insert ha]; rfl
      rw [h1]
      exact smoothF_add (hX a (Finset.mem_insert_self a t))
        (ih fun i hi => hX i (Finset.mem_insert_of_mem hi))

/-! ## The sum rule and the Leibniz rule for `∇` -/

/-- Additivity of the covariant derivative over a finite sum of smooth sections. -/
lemma cov_sum (g : Submission.Diff.SMet I M) {ι : Type*} (s : Finset ι)
    (X : ι → Π y : M, TangentSpace I y) (hX : ∀ i ∈ s, SmoothField I M (X i)) (y : M) :
    Submission.Diff.lcOf g (fun y' : M => ∑ i ∈ s, X i y') y
      = ∑ i ∈ s, Submission.Diff.lcOf g (X i) y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have h0 : (fun y' : M => ∑ i ∈ (∅ : Finset ι), X i y') = 0 := by funext y'; simp
      rw [h0, CovariantDerivative.zero, Finset.sum_empty]
      exact Pi.zero_apply y
  | insert a t ha ih =>
      have h1 : (fun y' : M => ∑ i ∈ insert a t, X i y')
          = X a + fun y' : M => ∑ i ∈ t, X i y' := by
        funext y'; rw [Finset.sum_insert ha]; rfl
      have hsm : SmoothField I M (fun y' : M => ∑ i ∈ t, X i y') :=
        smoothF_sum t X (fun i hi => hX i (Finset.mem_insert_of_mem hi))
      have ha' : MDiffAt (T% (X a)) y :=
        (hX a (Finset.mem_insert_self a t)).mdifferentiableAt (by simp)
      have ht' : MDiffAt (T% (fun y' : M => ∑ i ∈ t, X i y')) y :=
        hsm.mdifferentiableAt (by simp)
      rw [h1, (Submission.Diff.lcOf g).isCovariantDerivativeOn.add ha' ht',
        Finset.sum_insert ha,
        ih (fun i hi => hX i (Finset.mem_insert_of_mem hi))]

/-- `∇_W` is additive in the field argument. -/
lemma dirF_add (g : Submission.Diff.SMet I M) {X₁ X₂ v : Π y : M, TangentSpace I y}
    (h₁ : SmoothField I M X₁) (h₂ : SmoothField I M X₂) :
    dirF g (X₁ + X₂) v = dirF g X₁ v + dirF g X₂ v := by
  funext y
  simp only [dirF, Pi.add_apply]
  rw [(Submission.Diff.lcOf g).isCovariantDerivativeOn (s := Set.univ).add
    (h₁.mdifferentiableAt (by simp)) (h₂.mdifferentiableAt (by simp))]
  simp

/-- The Leibniz rule for `∇_W` in a scalar multiple `f • X`. -/
lemma dirF_smul (g : Submission.Diff.SMet I M) {f : M → ℝ} {X v : Π y : M, TangentSpace I y}
    (hf : CMDiff ∞ f) (hX : SmoothField I M X) :
    dirF g (f • X) v = f • dirF g X v + (fun y : M => mvfderiv I f y (v y)) • X := by
  funext y
  have h := (Submission.Diff.lcOf g).isCovariantDerivativeOn (s := Set.univ).leibniz
    (σ := X) (g := f) (x := y) (hX.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp))
  simp only [dirF]
  rw [h]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, Pi.smul_apply',
    Pi.add_apply]
  rfl

/-- `∇_W` of a finite sum of smooth fields is the sum of the `∇_W`'s. -/
lemma dirF_sum (g : Submission.Diff.SMet I M) {ι : Type*} (s : Finset ι)
    (X : ι → Π y : M, TangentSpace I y) (v : Π y : M, TangentSpace I y)
    (hX : ∀ i ∈ s, SmoothField I M (X i)) :
    dirF g (fun y : M => ∑ i ∈ s, X i y) v = fun y : M => ∑ i ∈ s, dirF g (X i) v y := by
  funext y
  simp only [dirF]
  rw [cov_sum g s X hX y, sum_apply]

/-- `∇_W X` is smooth when `X` and `W` are. -/
lemma dirF_smooth (g : Submission.Diff.SMet I M) (hLC : Submission.Diff.LCSmooth I M)
    {X v : Π y : M, TangentSpace I y} (hX : SmoothField I M X) (hv : SmoothField I M v) :
    SmoothField I M (dirF g X v) := by
  obtain ⟨hcov⟩ := (hLC g).1
  exact Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
    (Submission.Diff.lcOf g) hcov hX hv

/-- The second-order Leibniz rule for a single term `f • X`. -/
lemma dirF_smul2 (g : Submission.Diff.SMet I M) (hLC : Submission.Diff.LCSmooth I M)
    {f : M → ℝ} {X v : Π y : M, TangentSpace I y} (hf : CMDiff ∞ f) (hX : SmoothField I M X)
    (hv : SmoothField I M v) :
    dirF g (dirF g (f • X) v) v
      = (fun y : M => mvfderiv I (fun y' : M => mvfderiv I f y' (v y')) y (v y)) • X
        + (2 : ℝ) • ((fun y : M => mvfderiv I f y (v y)) • dirF g X v)
        + f • dirF g (dirF g X v) v := by
  have hY : SmoothField I M (dirF g X v) := dirF_smooth g hLC hX hv
  have hw : CMDiff ∞ (fun y : M => mvfderiv I f y (v y)) :=
    Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff hf hv
  have hInner : dirF g (f • X) v = f • dirF g X v + (fun y : M => mvfderiv I f y (v y)) • X :=
    dirF_smul g hf hX
  have hAdd : dirF g (f • dirF g X v + (fun y : M => mvfderiv I f y (v y)) • X) v
      = dirF g (f • dirF g X v) v + dirF g ((fun y : M => mvfderiv I f y (v y)) • X) v :=
    dirF_add g (hf.smul_section hY) (hw.smul_section hX)
  have hs1 : dirF g (f • dirF g X v) v
      = f • dirF g (dirF g X v) v + (fun y : M => mvfderiv I f y (v y)) • dirF g X v :=
    dirF_smul g hf hY
  have hs2 : dirF g ((fun y : M => mvfderiv I f y (v y)) • X) v
      = (fun y : M => mvfderiv I f y (v y)) • dirF g X v
        + (fun y : M => mvfderiv I (fun y' : M => mvfderiv I f y' (v y')) y (v y)) • X :=
    dirF_smul g hw hX
  rw [hInner, hAdd, hs1, hs2]
  rw [two_smul ℝ ((fun y : M => mvfderiv I f y (v y)) • dirF g X v)]
  abel

/-- The second-order Leibniz rule for a finite sum `∑_j f_j • X_j`. -/
lemma dirF_second_sum (g : Submission.Diff.SMet I M) (hLC : Submission.Diff.LCSmooth I M)
    {ι : Type*} (s : Finset ι) (f : ι → M → ℝ) (X : ι → Π y : M, TangentSpace I y)
    (v : Π y : M, TangentSpace I y) (hf : ∀ j ∈ s, CMDiff ∞ (f j))
    (hX : ∀ j ∈ s, SmoothField I M (X j)) (hv : SmoothField I M v) :
    dirF g (dirF g (fun y : M => ∑ j ∈ s, f j y • X j y) v) v
      = fun y : M => ∑ j ∈ s,
          ((mvfderiv I (fun y' : M => mvfderiv I (f j) y' (v y')) y (v y)) • (X j y)
            + (2 : ℝ) • ((mvfderiv I (f j) y (v y)) • (dirF g (X j) v y))
            + (f j y) • (dirF g (dirF g (X j) v) v y)) := by
  have h1 : dirF g (fun y : M => ∑ j ∈ s, f j y • X j y) v
      = fun y : M => ∑ j ∈ s, dirF g (f j • X j) v y :=
    dirF_sum g s (fun j => f j • X j) v (fun j hj => (hf j hj).smul_section (hX j hj))
  rw [h1]
  rw [dirF_sum g s (fun j => dirF g (f j • X j) v) v
    (fun j hj => dirF_smooth g hLC ((hf j hj).smul_section (hX j hj)) hv)]
  funext y
  refine Finset.sum_congr rfl (fun j hj => ?_)
  exact congrFun (dirF_smul2 g hLC (hf j hj) (hX j hj) hv) y

/-- A component of a smooth map into a finite product of scalars is smooth. -/
lemma smoothMap_eval {n : ℕ} {A : M → (Fin n → Fin n → ℝ)} (hA : SmoothMap I M A)
    (p i : Fin n) : CMDiff ∞ (fun y : M => A y p i) :=
  (contMDiff_pi_space.mp ((contMDiff_pi_space.mp hA) p)) i

theorem lcOf_transition_second
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M] [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    {n : ℕ} (A : M → (Fin n → Fin n → ℝ)) (hA : Work.Diff.Evol.SmoothMap I M A)
    (F : Fin n → Π y : M, TangentSpace I y)
    (hF : ∀ i, Work.Diff.Evol.SmoothField I M (F i))
    (W : Π y : M, TangentSpace I y) (hW : Work.Diff.Evol.SmoothField I M W)
    (x : M) (i : Fin n) :
    Submission.Diff.lcOf g (fun y : M => Submission.Diff.lcOf g
        (fun z : M => ∑ p : Fin n, (A z p i) • (F p z)) y (W y)) x (W x)
      = ∑ p : Fin n,
          ((mvfderiv I (fun y : M => mvfderiv I (fun z : M => A z p i) y (W y)) x (W x)) • (F p x)
            + (2 : ℝ) • ((mvfderiv I (fun y : M => A y p i) x (W x))
                • (Submission.Diff.lcOf g (F p) x (W x)))
            + (A x p i) • (Submission.Diff.lcOf g
                (fun y : M => Submission.Diff.lcOf g (F p) y (W y)) x (W x))) := by
  have hf : ∀ p : Fin n, CMDiff ∞ (fun y : M => A y p i) := fun p => smoothMap_eval hA p i
  change dirF g (dirF g (fun y : M => ∑ p : Fin n, (A y p i) • (F p y)) W) W x
      = ∑ p : Fin n,
          ((mvfderiv I (fun y : M => mvfderiv I (fun z : M => A z p i) y (W y)) x (W x)) • (F p x)
            + (2 : ℝ) • ((mvfderiv I (fun y : M => A y p i) x (W x))
                • (Submission.Diff.lcOf g (F p) x (W x)))
            + (A x p i) • (Submission.Diff.lcOf g
                (fun y : M => Submission.Diff.lcOf g (F p) y (W y)) x (W x)))
  rw [dirF_second_sum (g := g) (hLC := hLC) (s := Finset.univ)
    (f := fun p : Fin n => fun y : M => A y p i) (X := F) (v := W)
    (fun p _ => hf p) (fun p _ => hF p) hW]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rfl

end Work.Diff.Evol
