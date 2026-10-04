import Mathlib
import Submission.Work.Diff.EXT.aCovArr_eq_covKAExt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Linearity of the connection-difference tower (`covKAExt` / `KKT`) in its three tensor slots

The frozen definition `Work.Diff.EXT.covKAExt G t k` is the `k`-th covariant derivative, with
respect to the *fixed* background connection `∇^{G 0}`, of the lowered connection difference
`aOf G t = g_t(∇^{G t} − ∇^{G 0})`, evaluated on `k` direction fields and three argument fields.

This file collects the vocabulary used to prove that `KKT G t k w t3` is linear in each of the
three tensor slots (the statements `Work.Diff.EXT.KaLinT` and `Work.Diff.EXT.KaLinD`):

* `KAddPt` — additivity in a slot, with a **pointwise** representation hypothesis
  `S = W₁ + W₂ on U` (the field `S` is not assumed to be *literally* the sum: the recursion only
  sees the germ, and the connection terms need the pointwise form);
* `KSmulPt` — homogeneity in a slot with respect to multiplication by a smooth function, again with
  a pointwise representation hypothesis;
* elementary lemmas about `mvfderiv` (congruence, additivity, Leibniz, finite sums) and about
  `lcOf` (additivity, Leibniz, germ-locality) that the inductions use.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Work.Diff.EXT

namespace Work.Diff.EXT.ATower

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-! ## Elementary rewriting lemmas for `Π`-type fields -/

@[simp] lemma pi_smul_apply_ka (f : M → ℝ) (W : KaTF (I := I) (M := M)) (y : M) :
    (f • W) y = f y • W y := rfl

@[simp] lemma pi_add_apply_ka (W₁ W₂ : KaTF (I := I) (M := M)) (y : M) :
    (W₁ + W₂) y = W₁ y + W₂ y := rfl

@[simp] lemma pi_sum_apply_ka {ι : Type*} (s : Finset ι) (f : ι → M → ℝ)
    (W : ι → KaTF (I := I) (M := M)) (y : M) :
    (fun z : M => ∑ q ∈ s, f q z • W q z) y = ∑ q ∈ s, f q y • W q y := rfl

/-! ## `mvfderiv` -/

/-- `mvfderiv` respects eventual equality. -/
lemma mvfderiv_congr_ka {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {g₁ g₂ : M → F}
    {x : M} (h : g₁ =ᶠ[𝓝 x] g₂) : mvfderiv I g₁ x = mvfderiv I g₂ x := by
  rw [mvfderiv, mvfderiv, h.eq_of_nhds, Filter.EventuallyEq.mfderiv_eq h]
  all_goals first | rfl | (ext v; rfl)

/-- Applied form of `mvfderiv_add`. -/
lemma mvfderiv_add_ka {f g : M → ℝ} {x : M} {v : TangentSpace I x}
    (hf : MDiffAt f x) (hg : MDiffAt g x) :
    mvfderiv I (f + g) x v = mvfderiv I f x v + mvfderiv I g x v := by
  have h := congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L v) (mvfderiv_add (I := I) hf hg)
  simpa only [add_apply] using h

/-- Applied form of the Leibniz rule for `mvfderiv` of a pointwise product of scalar functions. -/
lemma mvfderiv_smul_ka {f g : M → ℝ} {x : M} {v : TangentSpace I x}
    (hf : MDiffAt f x) (hg : MDiffAt g x) :
    mvfderiv I (f • g) x v = f x * mvfderiv I g x v + mvfderiv I f x v * g x := by
  have h := congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L v)
    (mvfderiv_smul (I := I) (a := f) (g := g) hf hg)
  simpa only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul] using h

/-- Differentiability of a finite sum of scalar functions. -/
lemma mdifferentiableAt_sum_ka {ι : Type*} (s : Finset ι) (f : ι → M → ℝ) {x : M}
    (hf : ∀ i ∈ s, MDiffAt (f i) x) :
    MDiffAt (fun y : M => ∑ i ∈ s, f i y) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hz : (fun y : M => ∑ i ∈ (∅ : Finset ι), f i y) = 0 := by
        funext y; simp
      rw [hz]; exact mdifferentiableAt_const
  | insert a t ha ih =>
      have hfun : (fun y : M => ∑ i ∈ insert a t, f i y)
          = (f a + fun y : M => ∑ i ∈ t, f i y) := by
        funext y; rw [Finset.sum_insert ha]; rfl
      rw [hfun]
      exact (hf a (Finset.mem_insert_self a t)).add
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- `mvfderiv` of a finite sum of scalar functions. -/
lemma mvfderiv_sum_ka {ι : Type*} (s : Finset ι) (f : ι → M → ℝ) {x : M} {v : TangentSpace I x}
    (hf : ∀ i ∈ s, MDiffAt (f i) x) :
    mvfderiv I (fun y : M => ∑ i ∈ s, f i y) x v = ∑ i ∈ s, mvfderiv I (f i) x v := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hz : (fun y : M => ∑ i ∈ (∅ : Finset ι), f i y) = 0 := by
        funext y; simp
      rw [hz, Finset.sum_empty]
      simp [mvfderiv_const]
  | insert a t ha ih =>
      have hfun : (fun y : M => ∑ i ∈ insert a t, f i y)
          = (f a + fun y : M => ∑ i ∈ t, f i y) := by
        funext y; rw [Finset.sum_insert ha]; rfl
      rw [hfun, mvfderiv_add_ka (hf a (Finset.mem_insert_self a t))
        (mdifferentiableAt_sum_ka t f fun i hi => hf i (Finset.mem_insert_of_mem hi)),
        Finset.sum_insert ha]
      rw [ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

/-! ## Smoothness of fields and of the tower -/

/-- Smoothness of the product of a smooth scalar function and a smooth tangent field. -/
lemma kaSm_smul_ka {U : Set M} {f : M → ℝ} {W : KaTF (I := I) (M := M)}
    (hf : ContMDiffOn I 𝓘(ℝ,ℝ) ∞ f U) (hW : KaSm (I := I) (M := M) U W) :
    KaSm (I := I) (M := M) U (f • W) :=
  ContMDiffOn.smul_section hf hW

/-- Smoothness of a sum of two smooth tangent fields. -/
lemma kaSm_add_ka {U : Set M} {W₁ W₂ : KaTF (I := I) (M := M)}
    (h₁ : KaSm (I := I) (M := M) U W₁) (h₂ : KaSm (I := I) (M := M) U W₂) :
    KaSm (I := I) (M := M) U (W₁ + W₂) :=
  ContMDiffOn.add_section h₁ h₂

/-- Smoothness of a finite sum of smooth tangent fields. -/
lemma kaSm_sum_ka {ι : Type*} {U : Set M} {s : Finset ι} {f : ι → M → ℝ}
    {W : ι → KaTF (I := I) (M := M)}
    (hf : ∀ q ∈ s, ContMDiffOn I 𝓘(ℝ,ℝ) ∞ (f q) U)
    (hW : ∀ q ∈ s, KaSm (I := I) (M := M) U (W q)) :
    KaSm (I := I) (M := M) U (fun y : M => ∑ q ∈ s, f q y • W q y) := by
  refine ContMDiffOn.sum_section (t := fun q y => f q y • W q y) (fun q hq => ?_)
  exact ContMDiffOn.smul_section (hf q hq) (hW q hq)

/-- Differentiability of a smooth tangent field on an open set. -/
lemma kaSm_mdiffAt_ka {U : Set M} (hU : IsOpen U) {X : KaTF (I := I) (M := M)}
    (hX : KaSm (I := I) (M := M) U X) {x : M} (hx : x ∈ U) :
    MDiffAt (T% X) x :=
  ((hX x hx).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)

/-- Differentiability of the tower, from joint smoothness on an open set. -/
lemma kkt_mdiffAt_ka (G : ℝ → SMet I M) (t : ℝ) {U : Set M} (hU : IsOpen U) (k : ℕ)
    {w : Fin k → KaTF (I := I) (M := M)} {t3 : Fin 3 → KaTF (I := I) (M := M)}
    (hw : ∀ s, KaSm (I := I) (M := M) U (w s))
    (h3 : ∀ j', KaSm (I := I) (M := M) U (t3 j')) {x : M} (hx : x ∈ U) :
    MDiffAt (KKT G t k w t3) x :=
  (((ka_KKT_smooth (I := I) (M := M) G t hU k w t3 hw h3) x hx).contMDiffAt
    (hU.mem_nhds hx)).mdifferentiableAt (by simp)

/-! ## The Levi-Civita connection of a smooth metric: computational rules -/

/-- Additivity of `lcOf` in the section slot (at a point). -/
lemma lcOf_add_ka (g : SMet I M) {B₁ B₂ : KaTF (I := I) (M := M)} {x : M}
    (h₁ : MDiffAt (T% B₁) x) (h₂ : MDiffAt (T% B₂) x) :
    (lcOf g) (B₁ + B₂) x = (lcOf g) B₁ x + (lcOf g) B₂ x :=
  ((lcOf g).isCovariantDerivativeOn (s := Set.univ)).add h₁ h₂

/-- The Leibniz rule for `lcOf` in the section slot (at a point). -/
lemma lcOf_smul_ka (g : SMet I M) {f : M → ℝ} {W : KaTF (I := I) (M := M)} {x : M}
    (hW : MDiffAt (T% W) x) (hf : MDiffAt f x) :
    (lcOf g) (f • W) x = f x • (lcOf g) W x + (mvfderiv I f x).smulRight (W x) :=
  ((lcOf g).isCovariantDerivativeOn (s := Set.univ)).leibniz hW hf

/-- Germ-locality of `lcOf` in the section slot (at a point). -/
lemma lcOf_congr_ka (g : SMet I M) {W₁ W₂ : KaTF (I := I) (M := M)} {x : M}
    (h₁ : MDiffAt (T% W₁) x) (h₂ : MDiffAt (T% W₂) x) (h : W₁ =ᶠ[𝓝 x] W₂) :
    (lcOf g) W₁ x = (lcOf g) W₂ x :=
  ((lcOf g).isCovariantDerivativeOn (s := Set.univ)).congr_of_eventuallyEq h₁ h₂
    Filter.univ_mem h

/-! ## The two slot-linearity predicates -/

/-- **Additivity of the tower in one tensor slot**, with the slot field only assumed to be
*pointwise* equal to the sum of the two fields on `U` (this is exactly the form in which the
recursion produces the slot fields, e.g. `∇_{w₀}(W₁ + W₂) = ∇_{w₀}W₁ + ∇_{w₀}W₂`). -/
def KAddPt (G : ℝ → SMet I M) (t : ℝ) (U : Set M) (k : ℕ) : Prop :=
  ∀ (w : Fin k → KaTF (I := I) (M := M)) (t3 : Fin 3 → KaTF (I := I) (M := M)) (j : Fin 3)
    (S W₁ W₂ : KaTF (I := I) (M := M)),
    (∀ s, KaSm (I := I) (M := M) U (w s)) → (∀ j', KaSm (I := I) (M := M) U (t3 j')) →
    KaSm (I := I) (M := M) U S → KaSm (I := I) (M := M) U W₁ →
    KaSm (I := I) (M := M) U W₂ → (∀ y ∈ U, S y = W₁ y + W₂ y) →
    ∀ x ∈ U, KKT G t k w (Function.update t3 j S) x
      = KKT G t k w (Function.update t3 j W₁) x + KKT G t k w (Function.update t3 j W₂) x

/-- **Homogeneity of the tower in one tensor slot** with respect to a smooth scalar factor, with
the slot field only assumed to be *pointwise* equal to the product on `U`. -/
def KSmulPt (G : ℝ → SMet I M) (t : ℝ) (U : Set M) (k : ℕ) : Prop :=
  ∀ (w : Fin k → KaTF (I := I) (M := M)) (t3 : Fin 3 → KaTF (I := I) (M := M)) (j : Fin 3)
    (f : M → ℝ) (S W : KaTF (I := I) (M := M)),
    (∀ s, KaSm (I := I) (M := M) U (w s)) → (∀ j', KaSm (I := I) (M := M) U (t3 j')) →
    KaSm (I := I) (M := M) U S → ContMDiffOn I 𝓘(ℝ,ℝ) ∞ f U →
    KaSm (I := I) (M := M) U W → (∀ y ∈ U, S y = f y • W y) →
    ∀ x ∈ U, KKT G t k w (Function.update t3 j S) x
      = f x * KKT G t k w (Function.update t3 j W) x

end Work.Diff.EXT.ATower
