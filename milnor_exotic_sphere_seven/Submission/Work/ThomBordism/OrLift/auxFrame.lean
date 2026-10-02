import Mathlib
import Submission.Work.PTGeometric.GrRank
import Submission.Work.PTGeometric.ProjOfPlane.Defs
import Submission.Work.ThomBordism.OrLift.ogFlipNeSelf
import Submission.Work.ThomBordism.Grassmann.projOfPlaneEqIff

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Elementary frame/projection lemmas for the oriented-lift construction

* `Work.ThomBordism.ol_eq_of_range_eq`: two members of the Grassmannian `Gr n k` with the same
  range are equal (an orthogonal projection is determined by its range).
* `Work.ThomBordism.ol_frameProj_eq_of_span_eq`: `frameProj` of an orthonormal frame depends only
  on its span.
* `Work.ThomBordism.ol_gramSchmidtNormed_eq_self`: Gram-Schmidt fixes an orthonormal family.
* `Work.ThomBordism.ol_linearIndependent_comp`: the composite of a linearly independent family with
  an operator injective on its span is linearly independent.
* `Work.ThomBordism.ol_injectiveOn_plane`: a projection within `1/4` of a plane projection is
  injective on that plane.
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open scoped Topology Matrix
open Classical

namespace Work.ThomBordism

open Work.PTGeometric
open Work.ThomBordism.Grassmann hiding Amb

/-! ## A projection is determined by its range -/

/-- **Two rank-`k` orthogonal projections with the same range are equal.** -/
theorem ol_eq_of_range_eq {n k : ℕ} {P Q : EndOp n} (hP : P ∈ Gr n k) (hQ : Q ∈ Gr n k)
    (h : LinearMap.range (P : Amb n →ₗ[ℝ] Amb n) = LinearMap.range (Q : Amb n →ₗ[ℝ] Amb n)) :
    P = Q := by
  have hsymQ : ∀ x y : Amb n, inner ℝ (Q x) y = inner ℝ x (Q y) := by
    intro x y
    have h1 := ContinuousLinearMap.adjoint_inner_left Q y x
    rw [hQ.1] at h1
    exact h1
  have hsymP : ∀ x y : Amb n, inner ℝ (P x) y = inner ℝ x (P y) := by
    intro x y
    have h1 := ContinuousLinearMap.adjoint_inner_left P y x
    rw [hP.1] at h1
    exact h1
  have hfixQ : ∀ x ∈ LinearMap.range (Q : Amb n →ₗ[ℝ] Amb n), Q x = x := by
    rintro x ⟨y, rfl⟩
    exact Work.PTGeometric.mem_Gr_apply_apply hQ y
  have hfixP : ∀ x ∈ LinearMap.range (P : Amb n →ₗ[ℝ] Amb n), P x = x := by
    rintro x ⟨y, rfl⟩
    exact Work.PTGeometric.mem_Gr_apply_apply hP y
  refine ContinuousLinearMap.ext fun w => ?_
  have hQwP : Q w ∈ LinearMap.range (P : Amb n →ₗ[ℝ] Amb n) := by
    rw [h]; exact ⟨w, rfl⟩
  have hperp : ∀ u ∈ LinearMap.range (P : Amb n →ₗ[ℝ] Amb n), inner ℝ (w - Q w) u = 0 := by
    intro u hu
    have huQ : u ∈ LinearMap.range (Q : Amb n →ₗ[ℝ] Amb n) := by rw [← h]; exact hu
    rw [inner_sub_left, hsymQ w u, hfixQ u huQ]
    ring
  have hzero : P (w - Q w) = 0 := by
    have hPv : P (w - Q w) ∈ LinearMap.range (P : Amb n →ₗ[ℝ] Amb n) := ⟨w - Q w, rfl⟩
    have hself : inner ℝ (P (w - Q w)) (P (w - Q w)) = 0 := by
      rw [hsymP (w - Q w) (P (w - Q w)), Work.PTGeometric.mem_Gr_apply_apply hP (w - Q w),
        hperp _ hPv]
    exact inner_self_eq_zero.mp hself
  rw [map_sub, hfixP (Q w) hQwP] at hzero
  exact sub_eq_zero.mp hzero

/-- **`frameProj` of an orthonormal frame depends only on its span.** -/
theorem ol_frameProj_eq_of_span_eq {k m : ℕ} {f g : Fin k → Amb (k + m)}
    (hf : Orthonormal ℝ f) (hg : Orthonormal ℝ g)
    (h : Submodule.span ℝ (Set.range f) = Submodule.span ℝ (Set.range g)) :
    frameProj f = frameProj g := by
  refine ol_eq_of_range_eq (frameProj_mem_Gr hf) (frameProj_mem_Gr hg) ?_
  rw [frameProj_range hf, frameProj_range hg, h]

/-! ## Gram-Schmidt fixes orthonormal families -/

/-- **Gram-Schmidt of an orthonormal family is the family.** -/
theorem ol_gramSchmidtNormed_eq_self {k m : ℕ} {f : Fin k → Amb (k + m)}
    (hf : Orthonormal ℝ f) :
    InnerProductSpace.gramSchmidtNormed ℝ f = f := by
  have hgs : InnerProductSpace.gramSchmidt ℝ f = f :=
    InnerProductSpace.gramSchmidt_of_orthogonal ℝ hf.2
  funext i
  rw [InnerProductSpace.gramSchmidtNormed, hgs, hf.1 i]
  simp

/-! ## Linear independence after composing with an operator -/

/-- **A linearly independent family stays independent after applying an operator which is injective
on its span.** -/
theorem ol_linearIndependent_comp {n k : ℕ} {Q : Amb n →L[ℝ] Amb n} {f : Fin k → Amb n}
    (hf : LinearIndependent ℝ f)
    (hinj : ∀ v ∈ Submodule.span ℝ (Set.range f), Q v = 0 → v = 0) :
    LinearIndependent ℝ (fun i => Q (f i)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hsum : (∑ j, g j • f j) ∈ Submodule.span ℝ (Set.range f) :=
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hzero : Q (∑ j, g j • f j) = 0 := by
    rw [map_sum]
    simpa only [map_smul] using hg
  have h0 := hinj _ hsum hzero
  exact (Fintype.linearIndependent_iff.mp hf g h0) i

/-! ## Injectivity on a nearby plane -/

/-- **A projection within `1/4` of a plane projection is injective on that plane.** -/
theorem ol_injectiveOn_plane {n k : ℕ} {P Q : Amb n →L[ℝ] Amb n} (hP : P ∈ Gr n k)
    (h : ‖Q - P‖ < 1 / 4) {v : Amb n} (hv : P v = v) (hQv : Q v = 0) : v = 0 := by
  have hv_eq : v = (P - Q) v := by rw [sub_apply, hv, hQv, sub_zero]
  rcases eq_or_lt_of_le (norm_nonneg v) with h0 | h0
  · exact norm_eq_zero.mp h0.symm
  have h1 : ‖v‖ = ‖(P - Q) v‖ := congrArg norm hv_eq
  have h2 : ‖(P - Q) v‖ ≤ ‖P - Q‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
  have hneg : P - Q = -(Q - P) := by abel
  have h3 : ‖P - Q‖ = ‖Q - P‖ := by rw [hneg, norm_neg]
  have hlt : ‖v‖ < 1 / 4 * ‖v‖ := by
    calc ‖v‖ = ‖(P - Q) v‖ := h1
      _ ≤ ‖P - Q‖ * ‖v‖ := h2
      _ = ‖Q - P‖ * ‖v‖ := by rw [h3]
      _ < 1 / 4 * ‖v‖ := mul_lt_mul_of_pos_right h h0
  have hz : ‖v‖ = 0 := by nlinarith [norm_nonneg v, hlt]
  exact norm_eq_zero.mp hz

/-! ## The Gram-Schmidt frame of a projected orthonormal frame -/

/-- **The Gram-Schmidt orthonormalisation of `Q ∘ f` has `frameProj` equal to `Q`**, for `Q` a
rank-`k` orthogonal projection and `f` an orthonormal `k`-frame on whose span `Q` is injective. -/
theorem ol_frameProj_gramSchmidt_comp {k m : ℕ} {Q : Amb (k + m) →L[ℝ] Amb (k + m)}
    (hQ : Q ∈ Gr (k + m) k) {f : Fin k → Amb (k + m)} (hf : Orthonormal ℝ f)
    (hinj : ∀ v ∈ Submodule.span ℝ (Set.range f), Q v = 0 → v = 0) :
    frameProj (fun i : Fin k => InnerProductSpace.gramSchmidtNormed ℝ
      (fun i : Fin k => Q (f i)) i) = Q := by
  have hLI : LinearIndependent ℝ (fun i : Fin k => Q (f i)) :=
    ol_linearIndependent_comp hf.linearIndependent hinj
  have hgorth : Orthonormal ℝ (fun i : Fin k =>
      InnerProductSpace.gramSchmidtNormed ℝ (fun i : Fin k => Q (f i)) i) :=
    InnerProductSpace.gramSchmidtNormed_orthonormal (𝕜 := ℝ) hLI
  have hspan_g : Submodule.span ℝ (Set.range (fun i : Fin k =>
        InnerProductSpace.gramSchmidtNormed ℝ (fun i : Fin k => Q (f i)) i))
      = Submodule.span ℝ (Set.range (fun i : Fin k => Q (f i))) := by
    rw [InnerProductSpace.span_gramSchmidtNormed_range (𝕜 := ℝ) (fun i : Fin k => Q (f i)),
      InnerProductSpace.span_gramSchmidt]
  have hle : Submodule.span ℝ (Set.range (fun i : Fin k => Q (f i)))
      ≤ LinearMap.range (Q : Amb (k + m) →ₗ[ℝ] Amb (k + m)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨f i, rfl⟩
  have hfin : Module.finrank ℝ (Submodule.span ℝ (Set.range (fun i : Fin k => Q (f i)))) = k := by
    rw [finrank_span_eq_card hLI]
    simp
  have hfinQ : Module.finrank ℝ (LinearMap.range (Q : Amb (k + m) →ₗ[ℝ] Amb (k + m))) = k :=
    finrank_range_mem_Gr hQ
  have heq : Submodule.span ℝ (Set.range (fun i : Fin k => Q (f i)))
      = LinearMap.range (Q : Amb (k + m) →ₗ[ℝ] Amb (k + m)) :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hfin, hfinQ])
  refine ol_eq_of_range_eq (frameProj_mem_Gr hgorth) hQ ?_
  rw [frameProj_range hgorth, hspan_g, heq]

/-! ## Uniqueness of the lift of a path along the double cover -/

/-- **Two continuous lifts of the same path in `Gr (k+m) k` which agree at `0` agree everywhere**
(`k ≥ 1`). -/
theorem ol_path_lift_unique {k m : ℕ} (hk : 0 < k) {a b : ↥(Set.Icc (0 : ℝ) 1) → OG k m}
    (ha : Continuous a) (hb : Continuous b)
    (hab : ∀ t, projOfPlane k m (a t) = projOfPlane k m (b t))
    (h0 : a ⟨0, by norm_num⟩ = b ⟨0, by norm_num⟩) : a = b := by
  have hset : {t : ↥(Set.Icc (0 : ℝ) 1) | a t = b t}ᶜ = {t | b t = ogFlip k m (a t)} := by
    ext t
    constructor
    · intro ht
      rcases (projOfPlaneEqIff k m (b t) (a t)).mp (hab t).symm with h | h
      · exact absurd h.symm ht
      · exact h
    · intro ht
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
      rw [ht]
      exact fun h => ol_ogFlip_ne_self hk (a t) h.symm
  have hcl : IsClopen {t : ↥(Set.Icc (0 : ℝ) 1) | a t = b t} := by
    refine ⟨isClosed_eq ha hb, ?_⟩
    rw [← isClosed_compl_iff, hset]
    exact isClosed_eq hb ((continuous_ogFlip k m).comp ha)
  haveI : PreconnectedSpace ↥(Set.Icc (0 : ℝ) 1) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  have huniv := hcl.eq_univ ⟨⟨0, by norm_num⟩, h0⟩
  funext t
  have ht : t ∈ {t : ↥(Set.Icc (0 : ℝ) 1) | a t = b t} := by rw [huniv]; trivial
  exact ht

/-! ## Gluing continuous maps over an open cover -/

/-- **Gluing of continuous maps over an open cover** (the maps agree on the overlaps). -/
theorem ol_exists_glue {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) (hcov : ∀ x, ∃ i, x ∈ U i)
    (f : ∀ i, ↥(U i) → Y) (hf : ∀ i, Continuous (f i))
    (hag : ∀ (i j : ι) (x : X) (hxi : x ∈ U i) (hxj : x ∈ U j), f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩) :
    ∃ F : X → Y, Continuous F ∧ ∀ (i : ι) (x : X) (hx : x ∈ U i), F x = f i ⟨x, hx⟩ := by
  classical
  let c : X → ι := fun x => Classical.choose (hcov x)
  have hc : ∀ x, x ∈ U (c x) := fun x => Classical.choose_spec (hcov x)
  refine ⟨fun x => f (c x) ⟨x, hc x⟩, ?_, ?_⟩
  · refine continuous_of_continuousOn_iUnion_of_isOpen (fun i => ?_) hU ?_
    · rw [continuousOn_iff_continuous_domRestrict]
      have hfun : (U i).domRestrict (fun x => f (c x) ⟨x, hc x⟩) = f i := by
        funext y
        simpa using hag (c (y : X)) i (y : X) (hc (y : X)) y.2
      rw [hfun]
      exact hf i
    · ext x
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      exact hcov x
  · intro i x hx
    exact hag (c x) i x (hc x) hx

end Work.ThomBordism
