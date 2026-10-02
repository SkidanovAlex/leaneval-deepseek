import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Real.Basic
import Submission.Work.Deep.Reed.Prob.Certified.Defs

/-!
# Invariance of Talagrand's `Engine` under reindexing

`Engine ι` (see `Submission/Work/Deep/Reed/Prob/Certified/Defs.lean`) states
Talagrand's convex distance inequality for products indexed by `ι`.  This file
shows that the property only depends on the *cardinality* of `ι`, and in
particular transfers along an equivalence `e : α ≃ β`:

* `engine_equiv_transfer` — `Engine α → Engine β` for `e : α ≃ β`, when the two
  `Engine`s are taken at the same universe level for the product family;
* `engine_univ_raise` — `Engine ι` at any level of the product family implies
  `Engine ι` at any other level (finite fibres are equivalent to `Fin (card …)`);
* `engine_equiv` — the two combined.

The index transfer is proved by transporting the data of the `β`-side along
`e`.  If `Ψ : β → Type*` is a family of finite types, the reindexed `α`-side
space is `∀ a, Ψ (e a)`, identified with `∀ b, Ψ b` by Mathlib's
`Equiv.piCongrLeft Ψ e`, whose inverse is the cast-free map `g ↦ fun a => g (e a)`.
The needed ingredients are that the weights of the product measure are preserved
(a reindexed product of finitely many factors) and that the squared convex
distance is preserved appropriately: we transport the `0/1`-witnesses of `Uset`
along the reindexing `s ↦ s ∘ e.symm` of `ℝ`-valued vectors, which is linear,
hence commutes with convex hulls (`IsLinearMap.image_convexHull`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped BigOperators

universe u v w w'

namespace Work.Deep.Reed.Prob.Certified

/-! ## Reindexing of real vectors -/

/-- Reindexing of a real vector along an equivalence: `(vecReindex e s) b = s (e.symm b)`. -/
noncomputable def vecReindex {α β : Type*} (e : α ≃ β) (s : α → ℝ) : β → ℝ :=
  fun b => s (e.symm b)

@[simp] lemma vecReindex_apply {α β : Type*} (e : α ≃ β) (s : α → ℝ) (b : β) :
    vecReindex e s b = s (e.symm b) := rfl

lemma isLinearMap_vecReindex {α β : Type*} (e : α ≃ β) : IsLinearMap ℝ (vecReindex e) := by
  refine ⟨fun s t => ?_, fun c s => ?_⟩
  · funext b
    simp [vecReindex]
  · funext b
    simp [vecReindex, smul_eq_mul]

/-- Reindexing of vectors does not change the squared Euclidean norm. -/
lemma sqnorm_vecReindex {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) (s : α → ℝ) :
    sqnorm (vecReindex e s) = sqnorm s := by
  show ∑ b, vecReindex e s b ^ 2 = ∑ a, s a ^ 2
  simp only [vecReindex_apply]
  exact Equiv.sum_comp e.symm (fun a => s a ^ 2)

/-- Reindexing of vectors, being linear, commutes with convex hulls. -/
lemma image_convexHull_vecReindex {α β : Type*} (e : α ≃ β) (s : Set (α → ℝ)) :
    vecReindex e '' convexHull ℝ s = convexHull ℝ (vecReindex e '' s) :=
  (isLinearMap_vecReindex e).image_convexHull s

/-- Reindexing preserves the set of squared norms of a family of vectors. -/
lemma sqnorm_image_vecReindex {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β)
    (W : Set (α → ℝ)) : sqnorm '' (vecReindex e '' W) = sqnorm '' W := by
  ext x
  constructor
  · rintro ⟨q, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨p, hp, (sqnorm_vecReindex e p).symm⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨vecReindex e p, ⟨p, hp, rfl⟩, sqnorm_vecReindex e p⟩

/-! ## Step 1: transfer of `Engine` along an equivalence of the index types -/

section IndexTransfer

variable {α : Type u} {β : Type v} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
variable (e : α ≃ β) {Ψ : β → Type w} [∀ b, Fintype (Ψ b)]

/-- The reindexing of witnesses: a `0/1`-vector witnessing the up-set of the shifted
set maps to a witness for the original `β`-side set. -/
lemma vecReindex_mem_Uset {A : Set (∀ b, Ψ b)} {g : ∀ b, Ψ b} {s : α → ℝ}
    (hs : s ∈ Uset ((Equiv.piCongrLeft Ψ e).symm '' A) ((Equiv.piCongrLeft Ψ e).symm g)) :
    vecReindex e s ∈ Uset A g := by
  obtain ⟨h01, y, hy, hys⟩ := hs
  obtain ⟨y', hy', rfl⟩ := hy
  refine ⟨fun b => h01 (e.symm b), y', hy', fun b hb => ?_⟩
  have h1 := hys (e.symm b) hb
  simp only [Equiv.piCongrLeft_symm_apply] at h1
  exact (Equiv.apply_symm_apply e b) ▸ h1

/-- Convex hulls are transported as well. -/
lemma vecReindex_image_Vset_subset {A : Set (∀ b, Ψ b)} {g : ∀ b, Ψ b} :
    vecReindex e ''
        Vset ((Equiv.piCongrLeft Ψ e).symm '' A) ((Equiv.piCongrLeft Ψ e).symm g)
      ⊆ Vset A g := by
  have hU : vecReindex e ''
        Uset ((Equiv.piCongrLeft Ψ e).symm '' A) ((Equiv.piCongrLeft Ψ e).symm g)
      ⊆ Uset A g := by
    rintro _ ⟨p, hp, rfl⟩
    exact vecReindex_mem_Uset e hp
  show vecReindex e ''
        convexHull ℝ (Uset ((Equiv.piCongrLeft Ψ e).symm '' A) ((Equiv.piCongrLeft Ψ e).symm g))
      ⊆ convexHull ℝ (Uset A g)
  rw [image_convexHull_vecReindex]
  exact convexHull_min (fun q hq => subset_convexHull ℝ _ (hU hq)) (convex_convexHull ℝ _)

/-- The squared convex distance to the shifted set dominates the original one. -/
lemma cdsq_shift_le {A : Set (∀ b, Ψ b)} (hA : A.Nonempty) (g : ∀ b, Ψ b) :
    cdsq A g ≤ cdsq ((Equiv.piCongrLeft Ψ e).symm '' A) ((Equiv.piCongrLeft Ψ e).symm g) := by
  have hne : (Vset ((Equiv.piCongrLeft Ψ e).symm '' A) ((Equiv.piCongrLeft Ψ e).symm g)).Nonempty :=
    Vset_nonempty (hA.image _)
  have hne' :
      (sqnorm '' Vset ((Equiv.piCongrLeft Ψ e).symm '' A) ((Equiv.piCongrLeft Ψ e).symm g)).Nonempty :=
    hne.image _
  show cdsq A g ≤
    sInf (sqnorm '' Vset ((Equiv.piCongrLeft Ψ e).symm '' A) ((Equiv.piCongrLeft Ψ e).symm g))
  refine le_csInf hne' fun q hq => ?_
  obtain ⟨p, hp, rfl⟩ := hq
  have hp' : vecReindex e p ∈ Vset A g := vecReindex_image_Vset_subset e ⟨p, hp, rfl⟩
  calc cdsq A g ≤ sqnorm (vecReindex e p) := cdsq_le_sqnorm hp'
    _ = sqnorm p := sqnorm_vecReindex e p

/-- The weight of a point of the product measure is preserved by reindexing. -/
lemma pi_wt_shift {μ' : ∀ b, FinProb (Ψ b)} (g : ∀ b, Ψ b) :
    (FinProb.pi (fun a => μ' (e a))).wt ((Equiv.piCongrLeft Ψ e).symm g)
      = (FinProb.pi μ').wt g := by
  rw [FinProb.pi_wt, FinProb.pi_wt]
  rw [← Equiv.prod_comp e (fun b => (μ' b).wt (g b))]
  exact Finset.prod_congr rfl fun a _ => by simp

/-- Probabilities are preserved by reindexing. -/
lemma prob_shift {μ' : ∀ b, FinProb (Ψ b)} (A : Set (∀ b, Ψ b)) :
    (FinProb.pi (fun a => μ' (e a))).prob ((Equiv.piCongrLeft Ψ e).symm '' A)
      = (FinProb.pi μ').prob A := by
  classical
  rw [FinProb.prob, FinProb.prob]
  refine (Finset.sum_bij (s := (Finset.univ : Finset (∀ b, Ψ b)))
      (t := (Finset.univ : Finset (∀ a, Ψ (e a))))
      (f := fun g => if g ∈ A then (FinProb.pi μ').wt g else 0)
      (g := fun f => if f ∈ (Equiv.piCongrLeft Ψ e).symm '' A
        then (FinProb.pi (fun a => μ' (e a))).wt f else 0)
      (fun g (_ : g ∈ (Finset.univ : Finset (∀ b, Ψ b))) => (Equiv.piCongrLeft Ψ e).symm g)
      (fun g _ => Finset.mem_univ _)
      (fun g₁ _ g₂ _ h => (Equiv.piCongrLeft Ψ e).symm.injective h)
      (fun f _ => ⟨(Equiv.piCongrLeft Ψ e) f, Finset.mem_univ _, by simp⟩)
      (fun g _ => ?_)).symm
  by_cases hg : g ∈ A
  · have hgm : (Equiv.piCongrLeft Ψ e).symm g ∈ (Equiv.piCongrLeft Ψ e).symm '' A :=
      ⟨g, hg, rfl⟩
    rw [if_pos hg, if_pos hgm, pi_wt_shift e g]
  · have hgm : ¬ ((Equiv.piCongrLeft Ψ e).symm g ∈ (Equiv.piCongrLeft Ψ e).symm '' A) := by
      rintro ⟨y, hy, hyy⟩
      exact hg ((Equiv.piCongrLeft Ψ e).symm.injective hyy ▸ hy)
    rw [if_neg hg, if_neg hgm]

/-- The exponential moment of the squared convex distance does not increase under
reindexing. -/
lemma exp_shift_le {μ' : ∀ b, FinProb (Ψ b)} (A : Set (∀ b, Ψ b)) (hA : A.Nonempty) :
    (FinProb.pi μ').exp (fun g => Real.exp (cdsq A g / 4)) ≤
      (FinProb.pi (fun a => μ' (e a))).exp
        (fun f => Real.exp (cdsq ((Equiv.piCongrLeft Ψ e).symm '' A) f / 4)) := by
  rw [FinProb.exp, FinProb.exp]
  calc ∑ g, (FinProb.pi μ').wt g * Real.exp (cdsq A g / 4)
      ≤ ∑ g, (FinProb.pi (fun a => μ' (e a))).wt ((Equiv.piCongrLeft Ψ e).symm g)
            * Real.exp (cdsq ((Equiv.piCongrLeft Ψ e).symm '' A)
                ((Equiv.piCongrLeft Ψ e).symm g) / 4) := by
        refine Finset.sum_le_sum fun g _ => ?_
        rw [pi_wt_shift e g]
        refine mul_le_mul_of_nonneg_left ?_ ((FinProb.pi μ').wt_nonneg g)
        refine Real.exp_le_exp.mpr ?_
        linarith [cdsq_shift_le (Ψ := Ψ) e hA g]
    _ = ∑ f, (FinProb.pi (fun a => μ' (e a))).wt f
            * Real.exp (cdsq ((Equiv.piCongrLeft Ψ e).symm '' A) f / 4) :=
        Equiv.sum_comp (Equiv.piCongrLeft Ψ e).symm
          (fun f => (FinProb.pi (fun a => μ' (e a))).wt f
            * Real.exp (cdsq ((Equiv.piCongrLeft Ψ e).symm '' A) f / 4))

end IndexTransfer

/-- **`Engine` is invariant under an equivalence of the index type** (with the product
family taken at a fixed universe level on both sides). -/
theorem engine_equiv_transfer {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (e : α ≃ β) (h : Work.Deep.Reed.Prob.Engine.{u, w} α) :
    Work.Deep.Reed.Prob.Engine.{v, w} β := by
  intro Ψ' instΨ μ' hμ' A'
  by_cases hA' : A' = ∅
  · rw [hA', FinProb.prob_empty, zero_mul]
    norm_num
  · have hAne : A'.Nonempty := Set.nonempty_iff_ne_empty.mpr hA'
    have hprob : (FinProb.pi μ').prob A'
        = (FinProb.pi (fun a => μ' (e a))).prob ((Equiv.piCongrLeft Ψ' e).symm '' A') :=
      (prob_shift (Ψ := Ψ') e A' (μ' := μ')).symm
    have hexp := exp_shift_le (Ψ := Ψ') e A' hAne (μ' := μ')
    have hmain := h (Ω := fun a => Ψ' (e a)) (μ := fun a => μ' (e a))
      (fun a x => hμ' (e a) x) ((Equiv.piCongrLeft Ψ' e).symm '' A')
    have hnn : 0 ≤ (FinProb.pi (fun a => μ' (e a))).prob ((Equiv.piCongrLeft Ψ' e).symm '' A') :=
      FinProb.prob_nonneg _ _
    calc (FinProb.pi μ').prob A' * (FinProb.pi μ').exp (fun g => Real.exp (cdsq A' g / 4))
        = (FinProb.pi (fun a => μ' (e a))).prob ((Equiv.piCongrLeft Ψ' e).symm '' A')
            * (FinProb.pi μ').exp (fun g => Real.exp (cdsq A' g / 4)) := by rw [hprob]
        _ ≤ (FinProb.pi (fun a => μ' (e a))).prob ((Equiv.piCongrLeft Ψ' e).symm '' A')
            * (FinProb.pi (fun a => μ' (e a))).exp
                (fun f => Real.exp (cdsq ((Equiv.piCongrLeft Ψ' e).symm '' A') f / 4)) :=
            mul_le_mul_of_nonneg_left hexp hnn
        _ ≤ 1 := hmain

/-! ## Step 2: `Engine` is insensitive to the universe of the product family -/

/-- The push-forward ("co-map") of a finite probability space along an equivalence:
`wt x = μ.wt (θ x)`. -/
noncomputable def probComap {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω'] (θ : Ω ≃ Ω')
    (μ : FinProb Ω') : FinProb Ω where
  wt x := μ.wt (θ x)
  wt_nonneg x := μ.wt_nonneg (θ x)
  wt_sum := by
    rw [← μ.wt_sum]
    exact Equiv.sum_comp θ μ.wt

@[simp] lemma probComap_wt {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω'] (θ : Ω ≃ Ω')
    (μ : FinProb Ω') (x : Ω) : (probComap θ μ).wt x = μ.wt (θ x) := rfl

/-- The product of a family of equivalences of the fibres. -/
noncomputable def piEquiv {ι : Type*} {Ω Ω' : ι → Type*} (θ : ∀ i, Ω i ≃ Ω' i) :
    (∀ i, Ω i) ≃ (∀ i, Ω' i) where
  toFun x i := θ i (x i)
  invFun y i := (θ i).symm (y i)
  left_inv x := funext fun i => (θ i).symm_apply_apply (x i)
  right_inv y := funext fun i => (θ i).apply_symm_apply (y i)

@[simp] lemma piEquiv_apply {ι : Type*} {Ω Ω' : ι → Type*} (θ : ∀ i, Ω i ≃ Ω' i)
    (x : ∀ i, Ω i) (i : ι) : piEquiv θ x i = θ i (x i) := rfl

@[simp] lemma piEquiv_symm_apply {ι : Type*} {Ω Ω' : ι → Type*} (θ : ∀ i, Ω i ≃ Ω' i)
    (y : ∀ i, Ω' i) (i : ι) : (piEquiv θ).symm y i = (θ i).symm (y i) := rfl

section Fiberwise

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {Ω Ω' : ι → Type*} [∀ i, Fintype (Ω i)] [∀ i, Fintype (Ω' i)]
variable (θ : ∀ i, Ω i ≃ Ω' i)

/-- The product weight of the pushed-forward measures is the pulled-back product weight. -/
lemma pi_wt_probComap {ν : ∀ i, FinProb (Ω' i)} (x : ∀ i, Ω i) :
    (FinProb.pi (fun i => probComap (θ i) (ν i))).wt x
      = (FinProb.pi ν).wt (piEquiv θ x) := by
  rw [FinProb.pi_wt, FinProb.pi_wt]
  exact Finset.prod_congr rfl fun i _ => by simp

/-- The up-set is preserved by the product of the equivalences. -/
lemma Uset_piEquiv_preimage {B : Set (∀ i, Ω' i)} (x : ∀ i, Ω i) :
    Uset (piEquiv θ ⁻¹' B) x = Uset B (piEquiv θ x) := by
  ext s
  constructor
  · rintro ⟨h01, y, hy, hys⟩
    refine ⟨h01, piEquiv θ y, hy, fun i hi => ?_⟩
    simpa using congrArg (θ i) (hys i hi)
  · rintro ⟨h01, z, hz, hzs⟩
    have hz' : (piEquiv θ) ((piEquiv θ).symm z) ∈ B := by simpa using hz
    refine ⟨h01, (piEquiv θ).symm z, hz', fun i hi => ?_⟩
    have h := hzs i hi
    simp only [piEquiv_apply] at h
    have h3 : (θ i).symm (θ i (x i)) = (θ i).symm (z i) := congrArg (θ i).symm h
    rw [piEquiv_symm_apply]
    rwa [(θ i).symm_apply_apply (x i)] at h3

/-- The squared convex distance is preserved by the product of the equivalences. -/
lemma cdsq_piEquiv_preimage {B : Set (∀ i, Ω' i)} (x : ∀ i, Ω i) :
    cdsq (piEquiv θ ⁻¹' B) x = cdsq B (piEquiv θ x) := by
  simp only [cdsq, Vset, Uset_piEquiv_preimage]

/-- Probabilities are preserved by the product of the equivalences. -/
lemma prob_piEquiv_preimage {ν : ∀ i, FinProb (Ω' i)} (B : Set (∀ i, Ω' i)) :
    (FinProb.pi (fun i => probComap (θ i) (ν i))).prob (piEquiv θ ⁻¹' B)
      = (FinProb.pi ν).prob B := by
  classical
  rw [FinProb.prob, FinProb.prob]
  rw [← Equiv.sum_comp (piEquiv θ) (fun y => if y ∈ B then (FinProb.pi ν).wt y else 0)]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : piEquiv θ x ∈ B
  · have hx' : x ∈ piEquiv θ ⁻¹' B := hx
    rw [if_pos hx', if_pos hx, pi_wt_probComap]
  · have hx' : ¬ (x ∈ piEquiv θ ⁻¹' B) := hx
    rw [if_neg hx', if_neg hx]

/-- Exponential moments of the squared convex distance are preserved by the product of
the equivalences. -/
lemma exp_piEquiv_preimage {ν : ∀ i, FinProb (Ω' i)} (B : Set (∀ i, Ω' i)) :
    (FinProb.pi (fun i => probComap (θ i) (ν i))).exp
        (fun x => Real.exp (cdsq (piEquiv θ ⁻¹' B) x / 4))
      = (FinProb.pi ν).exp (fun y => Real.exp (cdsq B y / 4)) := by
  rw [FinProb.exp, FinProb.exp]
  rw [← Equiv.sum_comp (piEquiv θ)
    (fun y => (FinProb.pi ν).wt y * Real.exp (cdsq B y / 4))]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [pi_wt_probComap, cdsq_piEquiv_preimage]

end Fiberwise

/-- **`Engine` is insensitive to the universe level of the product family**: finite fibres
can be replaced by `Fin (card …)` (lifted to the target universe). -/
theorem engine_univ_raise {ι : Type u} [Fintype ι] [DecidableEq ι]
    (h : Work.Deep.Reed.Prob.Engine.{u, w} ι) : Work.Deep.Reed.Prob.Engine.{u, w'} ι := by
  classical
  intro Ψ instΨ ν hν B
  let θ : ∀ i, ULift.{w, 0} (Fin (Fintype.card (Ψ i))) ≃ Ψ i :=
    fun i => Equiv.ulift.trans (Fintype.equivFin (Ψ i)).symm
  have hmain := h (Ω := fun i => ULift.{w, 0} (Fin (Fintype.card (Ψ i))))
    (μ := fun i => probComap (θ i) (ν i)) (by intro i x; exact hν i (θ i x))
    ((piEquiv θ) ⁻¹' B)
  rwa [prob_piEquiv_preimage θ B, exp_piEquiv_preimage θ B] at hmain

theorem engine_equiv {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (h : Work.Deep.Reed.Prob.Engine α) : Work.Deep.Reed.Prob.Engine β :=
  engine_equiv_transfer e (engine_univ_raise h)

end Work.Deep.Reed.Prob.Certified
