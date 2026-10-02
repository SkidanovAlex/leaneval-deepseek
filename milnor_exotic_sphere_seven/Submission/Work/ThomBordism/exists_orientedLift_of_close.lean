import Mathlib
import Submission.Work.PTGeometric.RieszProj.Defs
import Submission.Work.PTGeometric.exists_projOfPlane
import Submission.Work.PTGeometric.exists_Rmap_lipschitz
import Submission.Work.ThomBordism.Grassmann.Grassmannian
import Submission.Work.PTGeometric.GrRank
import Submission.Work.ThomBordism.Grassmann.GrassmannianTopology
import Submission.Work.ThomBordism.Grassmann.projOfPlaneEqIff
import Submission.Work.ThomBordism.Grassmann.chartFrameAt
import Submission.Work.PTGeometric.smoothMap_into_tautTotal_eqOn_close
import Submission.Work.ThomBordism.OrLift.ogFlipNeSelf
import Submission.Work.ThomBordism.OrLift.auxFrame

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedVariables false

open scoped Topology Matrix
open Classical

namespace Work.ThomBordism

open Work.PTGeometric
open Work.ThomBordism.Grassmann hiding Amb

/-- The continuous orthonormal frame field on a chart cell `baseSet S` of the oriented
Grassmannian: the descent of the Gram-Schmidt orthonormalisation of the chart coordinates. -/
noncomputable def olCF (k m : ℕ) (S : ChartIdx k m) : ↥(baseSet S) → Fin k → Amb (k + m) :=
  Classical.choose (exists_chartFrameAt k m S)

theorem olCF_orthonormal (k m : ℕ) (S : ChartIdx k m) (y : ↥(baseSet S)) :
    Orthonormal ℝ (olCF k m S y) :=
  (Classical.choose_spec (exists_chartFrameAt k m S)).1 y

theorem olCF_span (k m : ℕ) (S : ChartIdx k m) (y : ↥(baseSet S)) :
    Submodule.span ℝ (Set.range (olCF k m S y))
      = Submodule.span ℝ (Set.range fun v : Amb k => evalChart S (y, v)) :=
  (Classical.choose_spec (exists_chartFrameAt k m S)).2.1 y

theorem olCF_continuous (k m : ℕ) (S : ChartIdx k m) : Continuous (olCF k m S) :=
  (Classical.choose_spec (exists_chartFrameAt k m S)).2.2

/-- **The projection of the chart frame field is the point of the Grassmannian.** -/
theorem olCF_frameProj (k m : ℕ) (S : ChartIdx k m) (y : ↥(baseSet S)) :
    frameProj (olCF k m S y) = projOfPlane k m (y : OG k m) := by
  obtain ⟨f, hf⟩ := Quotient.exists_rep (y : OG k m)
  have hf' : (ogMk k m f : OG k m) = (y : OG k m) := hf
  have hmem : (ogMk k m f : OG k m) ∈ baseSet S := by rw [hf']; exact y.2
  have hfy : f ∈ chartSet S := (mem_baseSet_iff S f).mp hmem
  have hspan : Submodule.span ℝ (Set.range fun v : Amb k => evalChart S (y, v))
      = Submodule.span ℝ (Set.range (f.1 : Fin k → Amb (k + m))) :=
    span_evalChart_eq S y f hfy hf'.symm
  have h2 : frameProj (olCF k m S y) = frameProj f.1 :=
    ol_frameProj_eq_of_span_eq (olCF_orthonormal k m S y) f.2 (by rw [olCF_span]; exact hspan)
  have h3 : projOfPlane k m (y : OG k m) = frameProj f.1 := by
    rw [← hf']
    exact projOfPlane_mk k m f
  rw [h2, h3]

/-! ## The chart frame as a point of the Stiefel manifold -/

/-- The chart frame, as an element of the Stiefel manifold. -/
noncomputable def olCFS (k m : ℕ) (S : ChartIdx k m) (y : ↥(baseSet S)) : Stiefel k m :=
  ⟨olCF k m S y, olCF_orthonormal k m S y⟩

theorem olCFS_continuous (k m : ℕ) (S : ChartIdx k m) : Continuous (olCFS k m S) :=
  Continuous.subtype_mk (olCF_continuous k m S) _

/-- The plane of the chart frame field is the plane of the point of the Grassmannian. -/
theorem olCFS_proj (k m : ℕ) (S : ChartIdx k m) (y : ↥(baseSet S)) :
    projOfPlane k m (ogMk k m (olCFS k m S y)) = projOfPlane k m (y : OG k m) := by
  change projOfPlane k m (Quotient.mk'' (olCFS k m S y)) = projOfPlane k m (y : OG k m)
  rw [projOfPlane_mk]
  exact olCF_frameProj k m S y

/-- Two lifts of the same plane in `OG k m` differ by the orientation flip. -/
theorem olCFS_eq_or_flip (k m : ℕ) (S : ChartIdx k m) (y : ↥(baseSet S)) :
    (ogMk k m (olCFS k m S y) : OG k m) = (y : OG k m) ∨
      (ogMk k m (olCFS k m S y) : OG k m) = ogFlip k m (y : OG k m) :=
  (projOfPlaneEqIff k m (ogMk k m (olCFS k m S y)) (y : OG k m)).mp
    (olCFS_proj k m S y)

/-- The set on which the chart frame has the orientation of the point is clopen (for `k ≥ 1`). -/
theorem olCFS_clopen (k m : ℕ) (hk : 0 < k) (S : ChartIdx k m) {X : Type*} [TopologicalSpace X]
    (γ : X → ↥(baseSet S)) (hγ : Continuous γ) :
    IsClopen {x : X | (ogMk k m (olCFS k m S (γ x)) : OG k m) = (γ x : OG k m)} := by
  have hcont1 : Continuous fun x : X => (ogMk k m (olCFS k m S (γ x)) : OG k m) :=
    (ogMk k m).continuous.comp ((olCFS_continuous k m S).comp hγ)
  have hcont2 : Continuous fun x : X => ((γ x : OG k m)) :=
    continuous_subtype_val.comp hγ
  have hset : {x : X | (ogMk k m (olCFS k m S (γ x)) : OG k m) = (γ x : OG k m)}ᶜ
      = {x : X | (ogMk k m (olCFS k m S (γ x)) : OG k m)
          = ogFlip k m (γ x : OG k m)} := by
    ext x
    constructor
    · intro hx
      rcases olCFS_eq_or_flip k m S (γ x) with h | h
      · exact absurd h hx
      · exact h
    · intro hx hcon
      have h1 : (ogMk k m (olCFS k m S (γ x)) : OG k m) = (γ x : OG k m) := hcon
      have h2 : (ogMk k m (olCFS k m S (γ x)) : OG k m) = ogFlip k m (γ x : OG k m) := hx
      have h3 : (γ x : OG k m) = ogFlip k m (γ x : OG k m) := by
        nth_rewrite 1 [← h1]
        exact h2
      exact ol_ogFlip_ne_self (k := k) (m := m) hk (γ x) h3.symm
  refine ⟨isClosed_eq hcont1 hcont2, ?_⟩
  rw [← isClosed_compl_iff, hset]
  exact isClosed_eq hcont1 ((continuous_ogFlip k m).comp hcont2)

/-! ## The Gram-Schmidt frame of a projected chart frame -/

/-- The Stiefel element whose frame is the Gram-Schmidt orthonormalisation of `Q` applied to the
frame `f`. -/
noncomputable def olGS (k m : ℕ) (Q : EndOp (k + m)) (f : Stiefel k m)
    (hinj : ∀ v ∈ Submodule.span ℝ (Set.range (f.1 : Fin k → Amb (k + m))), Q v = 0 → v = 0) :
    Stiefel k m :=
  ⟨fun i : Fin k => InnerProductSpace.gramSchmidtNormed ℝ (fun i : Fin k => Q (f.1 i)) i,
    InnerProductSpace.gramSchmidtNormed_orthonormal (𝕜 := ℝ)
      (ol_linearIndependent_comp f.2.linearIndependent hinj)⟩

theorem olGS_proj (k m : ℕ) {Q : EndOp (k + m)} (hQ : Q ∈ Gr (k + m) k) (f : Stiefel k m)
    (hinj : ∀ v ∈ Submodule.span ℝ (Set.range (f.1 : Fin k → Amb (k + m))), Q v = 0 → v = 0) :
    projOfPlane k m (ogMk k m (olGS k m Q f hinj)) = Q := by
  change projOfPlane k m (Quotient.mk'' (olGS k m Q f hinj)) = Q
  rw [projOfPlane_mk]
  exact ol_frameProj_gramSchmidt_comp hQ f.2 hinj

theorem olGS_continuous (k m : ℕ) {X : Type*} [TopologicalSpace X] {Q : X → EndOp (k + m)}
    (hQc : Continuous Q) {f : X → Stiefel k m} (hfc : Continuous f)
    (hinj : ∀ x, ∀ v ∈ Submodule.span ℝ (Set.range ((f x).1 : Fin k → Amb (k + m))),
      Q x v = 0 → v = 0) :
    Continuous fun x => olGS k m (Q x) (f x) (hinj x) := by
  have hbase : ∀ j : Fin k, Continuous fun x : X => Q x ((f x).1 j) := fun j =>
    hQc.clm_apply ((continuous_apply j).comp hfc.subtype_val)
  exact Continuous.subtype_mk
    (continuous_pi (Work.ThomBordism.Grassmann.Smooth.gramSchmidtContinuous
      (fun x (i : Fin k) => Q x ((f x).1 i)) hbase
      (fun x => ol_linearIndependent_comp (f x).2.linearIndependent (hinj x)))) _

/-- If `Q` fixes every vector of the frame `f`, the Gram-Schmidt frame of `Q ∘ f` is `f`. -/
theorem olGS_eq_self_of_fixes (k m : ℕ) {Q : EndOp (k + m)} {f : Stiefel k m}
    (hfix : ∀ i, Q (f.1 i) = f.1 i)
    (hinj : ∀ v ∈ Submodule.span ℝ (Set.range (f.1 : Fin k → Amb (k + m))), Q v = 0 → v = 0) :
    olGS k m Q f hinj = f := by
  refine Subtype.ext ?_
  show (fun i : Fin k => InnerProductSpace.gramSchmidtNormed ℝ
    (fun i : Fin k => Q (f.1 i)) i) = f.1
  rw [show (fun i : Fin k => Q (f.1 i)) = f.1 from funext hfix]
  exact ol_gramSchmidtNormed_eq_self f.2

/-! ## The corrected local lift on a chart -/

/-- The candidate lift of a projection `Q` over a chart: the plane of `Q` with the orientation
chosen so that, when `Q` is the plane of the chart point, one recovers the chart point itself. -/
noncomputable def olLocPoint (k m : ℕ) (S : ChartIdx k m) (y : ↥(baseSet S))
    (Q : EndOp (k + m))
    (hinj : ∀ v ∈ Submodule.span ℝ (Set.range ((olCFS k m S y).1)), Q v = 0 → v = 0) : OG k m :=
  if (ogMk k m (olCFS k m S y) : OG k m) = (y : OG k m)
    then ogMk k m (olGS k m Q (olCFS k m S y) hinj)
    else ogFlip k m (ogMk k m (olGS k m Q (olCFS k m S y) hinj))

/-- The `Q`-plane over a chart with the corrected orientation. -/
theorem olLocPoint_proj (k m : ℕ) (S : ChartIdx k m) (y : ↥(baseSet S)) {Q : EndOp (k + m)}
    (hQ : Q ∈ Gr (k + m) k)
    (hinj : ∀ v ∈ Submodule.span ℝ (Set.range ((olCFS k m S y).1)), Q v = 0 → v = 0) :
    projOfPlane k m (olLocPoint k m S y Q hinj) = Q := by
  rw [olLocPoint]
  by_cases h : (ogMk k m (olCFS k m S y) : OG k m) = (y : OG k m)
  · rw [if_pos h]
    exact olGS_proj k m hQ _ hinj
  · rw [if_neg h, projOfPlane_ogFlip]
    exact olGS_proj k m hQ _ hinj

/-- If `Q` is the plane of the chart point, the corrected candidate is that plane. -/
theorem olLocPoint_start (k m : ℕ) (S : ChartIdx k m) (y : ↥(baseSet S)) {Q : EndOp (k + m)}
    (hQ : Q = projOfPlane k m (y : OG k m))
    (hinj : ∀ v ∈ Submodule.span ℝ (Set.range ((olCFS k m S y).1)), Q v = 0 → v = 0) :
    olLocPoint k m S y Q hinj = (y : OG k m) := by
  have hfix : ∀ i, Q ((olCFS k m S y).1 i) = (olCFS k m S y).1 i := by
    intro i
    have h1 : Q = frameProj (olCFS k m S y).1 := by
      rw [hQ]
      exact (olCF_frameProj k m S y).symm
    rw [h1]
    exact frameProj_fixes (olCFS k m S y).2 i
  have hgs : ogMk k m (olGS k m Q (olCFS k m S y) hinj) = ogMk k m (olCFS k m S y) :=
    congrArg (ogMk k m) (olGS_eq_self_of_fixes k m hfix hinj)
  rw [olLocPoint]
  by_cases h : (ogMk k m (olCFS k m S y) : OG k m) = (y : OG k m)
  · rw [if_pos h, hgs, h]
  · rw [if_neg h, hgs]
    have hflip : (ogMk k m (olCFS k m S y) : OG k m) = ogFlip k m (y : OG k m) := by
      rcases olCFS_eq_or_flip k m S y with h' | h'
      · exact absurd h' h
      · exact h'
    rw [hflip, ogFlip_idem]

/-- The corrected local candidate, as a function on a chart-valued parameter space. -/
noncomputable def olLocCand (k m : ℕ) (S : ChartIdx k m) {X : Type*} (γ : X → ↥(baseSet S))
    (Q : X → EndOp (k + m))
    (hinj : ∀ x, ∀ v ∈ Submodule.span ℝ (Set.range ((olCFS k m S (γ x)).1)),
      Q x v = 0 → v = 0) (x : X) : OG k m :=
  olLocPoint k m S (γ x) (Q x) (hinj x)

theorem olLocCand_proj (k m : ℕ) (S : ChartIdx k m) {X : Type*} (γ : X → ↥(baseSet S))
    {Q : X → EndOp (k + m)} (hQ : ∀ x, Q x ∈ Gr (k + m) k)
    (hinj : ∀ x, ∀ v ∈ Submodule.span ℝ (Set.range ((olCFS k m S (γ x)).1)),
      Q x v = 0 → v = 0) (x : X) :
    projOfPlane k m (olLocCand k m S γ Q hinj x) = Q x :=
  olLocPoint_proj k m S (γ x) (hQ x) (hinj x)

theorem olLocCand_start (k m : ℕ) (S : ChartIdx k m) {X : Type*} (γ : X → ↥(baseSet S))
    {Q : X → EndOp (k + m)} (hinj : ∀ x, ∀ v ∈ Submodule.span ℝ (Set.range ((olCFS k m S (γ x)).1)),
      Q x v = 0 → v = 0) {x : X} (hQ : Q x = projOfPlane k m (γ x : OG k m)) :
    olLocCand k m S γ Q hinj x = (γ x : OG k m) :=
  olLocPoint_start k m S (γ x) hQ (hinj x)

theorem olLocCand_continuous (k m : ℕ) (hk : 0 < k) (S : ChartIdx k m) {X : Type*}
    [TopologicalSpace X] (γ : X → ↥(baseSet S)) (hγ : Continuous γ) {Q : X → EndOp (k + m)}
    (hQc : Continuous Q)
    (hinj : ∀ x, ∀ v ∈ Submodule.span ℝ (Set.range ((olCFS k m S (γ x)).1)),
      Q x v = 0 → v = 0) :
    Continuous (olLocCand k m S γ Q hinj) := by
  have hE := olCFS_clopen k m hk S γ hγ
  have hb : Continuous fun x : X =>
      ogMk k m (olGS k m (Q x) (olCFS k m S (γ x)) (hinj x)) :=
    (ogMk k m).continuous.comp
      (olGS_continuous k m hQc ((olCFS_continuous k m S).comp hγ) hinj)
  have hb2 : Continuous fun x : X => ogFlip k m
      (ogMk k m (olGS k m (Q x) (olCFS k m S (γ x)) (hinj x))) :=
    (continuous_ogFlip k m).comp hb
  exact ol_continuous_ite_of_clopen hE hb hb2

/-! ## The straight-line homotopy of projections -/

/-- The straight-line homotopy of projections, in the symmetrised variable: the Riesz projection of
`P x + t • (symm (Pm x) - P x)`.  This is `P x` at `t = 0` and `Rmap (Pm x)` at `t = 1`. -/
noncomputable def olQ (k m : ℕ) {M : Type} (P Pm : M → EndOp (k + m)) (x : M) (t : ℝ) :
    EndOp (k + m) :=
  Rmap (P x + t • (symm (Pm x) - P x))

theorem abs_le_one_of_mem_Icc {t : ℝ} (h : t ∈ Set.Icc (0 : ℝ) 1) : |t| ≤ 1 := by
  rw [abs_le]
  exact ⟨by linarith [h.1], h.2⟩

/-- The symmetrised line from `P x` to `Pm x` stays in the good set. -/
theorem ol_mem_good (k m : ℕ) {M : Type} {P Pm : M → EndOp (k + m)}
    (hProj : ∀ x, P x ∈ Gr (k + m) k) (hPm : ∀ x, ‖Pm x - P x‖ < 1 / 8) (x : M) {t : ℝ}
    (ht : |t| ≤ 1) : P x + t • (symm (Pm x) - P x) ∈ good (k + m) k := by
  refine good_of_dist (hProj x) ?_
  have h1 : P x + t • (symm (Pm x) - P x) - P x = t • (symm (Pm x) - P x) := by module
  rw [h1, norm_smul, Real.norm_eq_abs]
  have h2 : ‖symm (Pm x) - P x‖ ≤ ‖Pm x - P x‖ := by
    have h3 : symm (Pm x) - P x = symm (Pm x) - symm (P x) := by
      rw [symm_eq_self_of_mem_Gr (hProj x)]
    rw [h3]
    exact norm_symm_sub_le (Pm x) (P x)
  calc |t| * ‖symm (Pm x) - P x‖ ≤ 1 * ‖Pm x - P x‖ :=
        mul_le_mul ht h2 (norm_nonneg _) (by norm_num)
    _ < 1 / 4 := by linarith [hPm x]

theorem olQ_mem (k m : ℕ) {M : Type} {P Pm : M → EndOp (k + m)}
    (hProj : ∀ x, P x ∈ Gr (k + m) k) (hPm : ∀ x, ‖Pm x - P x‖ < 1 / 8) (x : M) {t : ℝ}
    (ht : |t| ≤ 1) : olQ k m P Pm x t ∈ Gr (k + m) k :=
  Rmap_mem_Gr_of_mem_good (ol_mem_good k m hProj hPm x ht)

theorem olQ_zero (k m : ℕ) {M : Type} {P Pm : M → EndOp (k + m)}
    (hProj : ∀ x, P x ∈ Gr (k + m) k) (x : M) : olQ k m P Pm x 0 = P x := by
  have h : P x + (0 : ℝ) • (symm (Pm x) - P x) = P x := by module
  show Phi (symm (P x + (0 : ℝ) • (symm (Pm x) - P x))) = P x
  rw [h, symm_eq_self_of_mem_Gr (hProj x)]
  exact Phi_eq_self_of_mem_Gr (hProj x) (finrank_amb (k + m))

theorem olQ_one (k m : ℕ) {M : Type} (P Pm : M → EndOp (k + m)) (x : M) :
    olQ k m P Pm x 1 = Rmap (Pm x) := by
  have h : P x + (1 : ℝ) • (symm (Pm x) - P x) = symm (Pm x) := by module
  have hs : symm (symm (Pm x)) = symm (Pm x) := by
    rw [show symm (symm (Pm x)) = (2 : ℝ)⁻¹ •
        (symm (Pm x) + ContinuousLinearMap.adjoint (symm (Pm x))) from rfl, adjoint_symm]
    module
  show Phi (symm (P x + (1 : ℝ) • (symm (Pm x) - P x))) = Phi (symm (Pm x))
  rw [h, hs]

theorem olQ_continuous (k m : ℕ) {M : Type} [TopologicalSpace M] {P Pm : M → EndOp (k + m)}
    (hPc : Continuous P) (hPmc : Continuous Pm)
    (hProj : ∀ x, P x ∈ Gr (k + m) k) (hPm : ∀ x, ‖Pm x - P x‖ < 1 / 8) :
    Continuous fun p : M × ↥(Set.Icc (0 : ℝ) 1) => olQ k m P Pm p.1 (p.2 : ℝ) := by
  have h1 : Continuous fun p : M × ↥(Set.Icc (0 : ℝ) 1) => Pm p.1 := hPmc.comp continuous_fst
  have h2 : Continuous fun p : M × ↥(Set.Icc (0 : ℝ) 1) => P p.1 := hPc.comp continuous_fst
  have h3 : Continuous fun p : M × ↥(Set.Icc (0 : ℝ) 1) => (p.2 : ℝ) :=
    continuous_subtype_val.comp continuous_snd
  have hA : Continuous fun p : M × ↥(Set.Icc (0 : ℝ) 1) =>
      P p.1 + (p.2 : ℝ) • (symm (Pm p.1) - P p.1) :=
    h2.add (h3.smul ((continuous_symm.comp h1).sub h2))
  refine ((contDiffOn_Rmap (k + m) k).continuousOn).comp_continuous hA ?_
  intro p
  exact ol_mem_good k m hProj hPm p.1 (abs_le_one_of_mem_Icc p.2.2)

/-! ## The degenerate cases `k = 0` and `m = 0` -/

theorem ol_eq_zero_of_mem_Gr_zero {n : ℕ} {P : EndOp n} (h : P ∈ Gr n 0) : P = 0 := by
  have hfin : Module.finrank ℝ (LinearMap.range (P : Amb n →ₗ[ℝ] Amb n)) = 0 := by
    rw [finrank_range_mem_Gr h]
  haveI : Subsingleton ↥(LinearMap.range (P : Amb n →ₗ[ℝ] Amb n)) :=
    Module.finrank_zero_iff.mp hfin
  refine ContinuousLinearMap.ext fun v => ?_
  have hv : (⟨P v, (⟨v, rfl⟩ : P v ∈ LinearMap.range (P : Amb n →ₗ[ℝ] Amb n))⟩ :
      ↥(LinearMap.range (P : Amb n →ₗ[ℝ] Amb n))) = 0 := Subsingleton.elim _ _
  have h2 : P v = 0 := by
    have := congrArg Subtype.val hv
    simpa using this
  simpa using h2

theorem ol_eq_one_of_mem_Gr_self {n : ℕ} {P : EndOp n} (h : P ∈ Gr n n) : P = 1 := by
  have hfin : Module.finrank ℝ (LinearMap.range (P : Amb n →ₗ[ℝ] Amb n)) = n :=
    finrank_range_mem_Gr h
  have htop : LinearMap.range (P : Amb n →ₗ[ℝ] Amb n) = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [hfin, finrank_amb]
  refine ContinuousLinearMap.ext fun v => ?_
  rw [ContinuousLinearMap.one_apply]
  have hv : v ∈ LinearMap.range (P : Amb n →ₗ[ℝ] Amb n) := by rw [htop]; trivial
  obtain ⟨w, hw⟩ := hv
  rw [← hw]
  exact mem_Gr_apply_apply h w

/-! ## Injectivity on the plane, from the quadratic-form estimates -/

/-- **The Riesz projection of a self-adjoint operator close to a plane projection is injective on
that plane.**  This is the quadratic-form estimate `⟨A v, v⟩ ≤ (1/4)‖v‖²` for `Phi A v = 0`
(`le_quarter_mul_of_Phi_eq_zero`) against `⟨A v, v⟩ ≥ (3/4)‖v‖²` for `v` in the plane of `P`. -/
theorem ol_injectiveOn_plane_riesz {n k : ℕ} {P A : EndOp n} (hP : P ∈ Gr n k)
    (hA : (A : Amb n →ₗ[ℝ] Amb n).IsSymmetric) (h : ‖A - P‖ < 1 / 4) {v : Amb n}
    (hv : P v = v) (hQv : Phi A v = 0) : v = 0 := by
  have hCl : Cluster A := Cluster.of_dist hP h
  have hn : Module.finrank ℝ (Amb n) = n := finrank_amb n
  have h1 : inner ℝ (A v) v ≤ (1 / 4) * ‖v‖ ^ 2 :=
    le_quarter_mul_of_Phi_eq_zero hA hCl hn hQv
  have hsplit : inner ℝ (A v) v = inner ℝ (P v) v + inner ℝ ((A - P) v) v := by
    rw [show A v = P v + (A - P) v by rw [sub_apply]; abel, inner_add_left]
  have hPv : inner ℝ (P v) v = ‖v‖ ^ 2 := by
    rw [hv, real_inner_self_eq_norm_sq]
  have h3 : |inner ℝ ((A - P) v) v| ≤ ‖(A - P) v‖ * ‖v‖ := abs_real_inner_le_norm _ _
  have h4 : ‖(A - P) v‖ ≤ ‖A - P‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
  have h2 : -(1 / 4) * ‖v‖ ^ 2 ≤ inner ℝ ((A - P) v) v := by
    nlinarith [abs_nonneg (inner ℝ ((A - P) v) v), norm_nonneg v, norm_nonneg ((A - P) v),
      h3, h4, h, le_abs_self (inner ℝ ((A - P) v) v),
      neg_abs_le (inner ℝ ((A - P) v) v), sq_nonneg ‖v‖, sq_nonneg ‖A - P‖]
  have hfin : ‖v‖ ^ 2 = 0 := by nlinarith [h1, hsplit, hPv, h2]
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hfin)

/-- **Injectivity of the homotopy's Riesz projection on the plane of `P x`.** -/
theorem ol_inj_of_homotopy (k m : ℕ) {M : Type} {P Pm : M → EndOp (k + m)}
    (hProj : ∀ x, P x ∈ Gr (k + m) k) (hPm : ∀ x, ‖Pm x - P x‖ < 1 / 8) (x : M) {t : ℝ}
    (ht : |t| ≤ 1) {v : Amb (k + m)} (hv : P x v = v) (hQv : olQ k m P Pm x t v = 0) :
    v = 0 := by
  have hBound : ‖symm (P x + t • (symm (Pm x) - P x)) - P x‖ < 1 / 4 := by
    have h2 : symm (P x + t • (symm (Pm x) - P x)) - P x
        = symm (P x + t • (symm (Pm x) - P x)) - symm (P x) := by
      rw [symm_eq_self_of_mem_Gr (hProj x)]
    rw [h2]
    refine lt_of_le_of_lt (norm_symm_sub_le _ _) ?_
    have h3 : P x + t • (symm (Pm x) - P x) - P x = t • (symm (Pm x) - P x) := by module
    rw [h3, norm_smul, Real.norm_eq_abs]
    have h4 : ‖symm (Pm x) - P x‖ ≤ ‖Pm x - P x‖ := by
      have h5 : symm (Pm x) - P x = symm (Pm x) - symm (P x) := by
        rw [symm_eq_self_of_mem_Gr (hProj x)]
      rw [h5]
      exact norm_symm_sub_le (Pm x) (P x)
    calc |t| * ‖symm (Pm x) - P x‖ ≤ 1 * ‖Pm x - P x‖ :=
          mul_le_mul ht h4 (norm_nonneg _) (by norm_num)
      _ = ‖Pm x - P x‖ := one_mul _
      _ < 1 / 8 := hPm x
      _ < 1 / 4 := by norm_num
  exact ol_injectiveOn_plane_riesz (hProj x)
    (symm_isSymmetric (P x + t • (Work.PTGeometric.symm (Pm x) - P x))) hBound hv hQv

theorem exists_orientedLift_of_close (k m : ℕ) {M : Type} [TopologicalSpace M]
    (P : M → Work.PTGeometric.Amb (k + m) →L[ℝ] Work.PTGeometric.Amb (k + m))
    (hPc : Continuous P) (hProj : ∀ x, P x ∈ Work.PTGeometric.Gr (k + m) k)
    (G : M → Work.ThomBordism.Grassmann.OG k m) (hGc : Continuous G)
    (hG : ∀ x, Work.PTGeometric.projOfPlane k m (G x) = P x)
    (Pm : M → Work.PTGeometric.Amb (k + m) →L[ℝ] Work.PTGeometric.Amb (k + m))
    (hPmc : Continuous Pm) (hPm : ∀ x, ‖Pm x - P x‖ < 1 / 8)
    (S : Set M) (hSP : ∀ x ∈ S, Pm x = P x) :
    ∃ G' : M → Work.ThomBordism.Grassmann.OG k m, Continuous G' ∧
      (∀ x, Work.PTGeometric.projOfPlane k m (G' x) = Work.PTGeometric.Rmap (Pm x)) ∧
      (∀ x ∈ S, G' x = G x) := by
  classical
  by_cases hk : k = 0
  · subst hk
    refine ⟨G, hGc, ?_, fun x _ => rfl⟩
    intro x
    have hg : Rmap (Pm x) ∈ Gr (0 + m) 0 := by
      rw [← olQ_one 0 m P Pm x]
      exact olQ_mem 0 m hProj hPm x (by norm_num)
    rw [hG x, ol_eq_zero_of_mem_Gr_zero (hProj x), ol_eq_zero_of_mem_Gr_zero hg]
  by_cases hm : m = 0
  · subst hm
    refine ⟨G, hGc, ?_, fun x _ => rfl⟩
    intro x
    have hg : Rmap (Pm x) ∈ Gr (k + 0) (k + 0) := by
      rw [← olQ_one k 0 P Pm x]
      exact olQ_mem k 0 hProj hPm x (by norm_num)
    rw [hG x, ol_eq_one_of_mem_Gr_self (hProj x), ol_eq_one_of_mem_Gr_self hg]
  -- main case
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  set US : ChartIdx k m → Set M := fun A => {x | G x ∈ baseSet A} with hUS
  have hUSopen : ∀ A, IsOpen (US A) := fun A => (isOpen_baseSet A).preimage hGc
  set Qh : M × ↥(Set.Icc (0 : ℝ) 1) → EndOp (k + m) :=
    fun p => olQ k m P Pm p.1 (p.2 : ℝ) with hQh
  have hQhc : Continuous Qh := olQ_continuous k m hPc hPmc hProj hPm
  have hQhmem : ∀ p, Qh p ∈ Gr (k + m) k := fun p =>
    olQ_mem k m hProj hPm p.1 (abs_le_one_of_mem_Icc p.2.2)
  -- the local data on each chart
  have hloc : ∀ A : ChartIdx k m, ∃ F : ↥(US A) × ↥(Set.Icc (0 : ℝ) 1) → OG k m,
      Continuous F ∧ (∀ p, projOfPlane k m (F p) = Qh (p.1.1, p.2)) ∧
      (∀ x hx, F (⟨x, hx⟩, ⟨0, by norm_num⟩) = G x) := by
    intro A
    have hGp : Continuous fun p : ↥(US A) × ↥(Set.Icc (0 : ℝ) 1) => G p.1.1 :=
      hGc.comp (continuous_subtype_val.comp continuous_fst)
    have hγfun : Continuous fun p : ↥(US A) × ↥(Set.Icc (0 : ℝ) 1) =>
        (⟨G p.1.1, p.1.2⟩ : ↥(baseSet A)) :=
      Continuous.subtype_mk (f := fun p : ↥(US A) × ↥(Set.Icc (0 : ℝ) 1) => G p.1.1) hGp
        (fun p => p.1.2)
    let γ : ↥(US A) × ↥(Set.Icc (0 : ℝ) 1) → ↥(baseSet A) := fun p => ⟨G p.1.1, p.1.2⟩
    have hγ : Continuous γ := hγfun
    let Q' : ↥(US A) × ↥(Set.Icc (0 : ℝ) 1) → EndOp (k + m) := fun p => Qh (p.1.1, p.2)
    have hQ'c : Continuous Q' :=
      hQhc.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
    have hinj : ∀ p, ∀ v ∈ Submodule.span ℝ (Set.range ((olCFS k m A (γ p)).1)),
        Q' p v = 0 → v = 0 := by
      intro p v hv hQv
      have hspan : Submodule.span ℝ (Set.range ((olCFS k m A (γ p)).1))
          = LinearMap.range (P p.1.1 : Amb (k + m) →ₗ[ℝ] Amb (k + m)) := by
        have h1 : frameProj (olCF k m A (γ p)) = P p.1.1 := by
          have h2 : frameProj (olCF k m A (γ p))
              = projOfPlane k m (ogMk k m (olCFS k m A (γ p))) :=
            (projOfPlane_mk k m (olCFS k m A (γ p))).symm
          rw [h2, olCFS_proj k m A (γ p)]
          exact hG p.1.1
        have hfr : Submodule.span ℝ (Set.range ((olCFS k m A (γ p)).1))
            = LinearMap.range (frameProj (olCF k m A (γ p)) :
                Amb (k + m) →ₗ[ℝ] Amb (k + m)) :=
          (frameProj_range (olCF_orthonormal k m A (γ p))).symm
        rw [hfr, h1]
      have hv' : P p.1.1 v = v := by
        have hv2 : v ∈ LinearMap.range (P p.1.1 : Amb (k + m) →ₗ[ℝ] Amb (k + m)) := by
          rw [← hspan]; exact hv
        obtain ⟨u, hu⟩ := hv2
        rw [← hu]
        exact mem_Gr_apply_apply (hProj p.1.1) u
      exact ol_inj_of_homotopy k m hProj hPm p.1.1 (abs_le_one_of_mem_Icc p.2.2) hv' hQv
    refine ⟨olLocCand k m A γ Q' hinj, ?_, ?_, ?_⟩
    · exact olLocCand_continuous k m hkpos A γ hγ hQ'c hinj
    · intro p
      exact olLocCand_proj k m A γ (fun p => hQhmem (p.1.1, p.2)) hinj p
    · intro x hx
      refine olLocCand_start k m A γ hinj ?_
      show Q' (⟨x, hx⟩, ⟨0, by norm_num⟩) = projOfPlane k m (↑(γ (⟨x, hx⟩, ⟨0, by norm_num⟩)))
      rw [show Q' (⟨x, hx⟩, ⟨0, by norm_num⟩) = P x from olQ_zero k m hProj x]
      exact (hG x).symm
  choose F hFc hFproj hF0 using hloc
  -- the local maps agree on the overlaps
  have hagree : ∀ (A B : ChartIdx k m) (x : M) (hxA : x ∈ US A) (hxB : x ∈ US B),
      F A (⟨x, hxA⟩, ⟨1, by norm_num⟩) = F B (⟨x, hxB⟩, ⟨1, by norm_num⟩) := by
    intro A B x hxA hxB
    have ha : Continuous fun t : ↥(Set.Icc (0 : ℝ) 1) => F A (⟨x, hxA⟩, t) :=
      (hFc A).comp (continuous_const.prodMk continuous_id)
    have hb : Continuous fun t : ↥(Set.Icc (0 : ℝ) 1) => F B (⟨x, hxB⟩, t) :=
      (hFc B).comp (continuous_const.prodMk continuous_id)
    have hab : ∀ t : ↥(Set.Icc (0 : ℝ) 1),
        projOfPlane k m (F A (⟨x, hxA⟩, t)) = projOfPlane k m (F B (⟨x, hxB⟩, t)) := by
      intro t
      rw [hFproj A (⟨x, hxA⟩, t), hFproj B (⟨x, hxB⟩, t)]
    have h0 : F A (⟨x, hxA⟩, ⟨0, by norm_num⟩) = F B (⟨x, hxB⟩, ⟨0, by norm_num⟩) := by
      rw [hF0 A x hxA, hF0 B x hxB]
    exact congrFun (ol_path_lift_unique hkpos ha hb hab h0) ⟨1, by norm_num⟩
  -- glue
  obtain ⟨G', hG'c, hG'val⟩ := ol_exists_glue US hUSopen
    (fun x => ⟨chartCover (G x), mem_baseSet_chartCover (G x)⟩)
    (fun A p => F A (p, ⟨1, by norm_num⟩))
    (fun A => (hFc A).comp (continuous_id.prodMk continuous_const))
    (fun A B x hxA hxB => hagree A B x hxA hxB)
  refine ⟨G', hG'c, ?_, ?_⟩
  · intro x
    have hx : x ∈ US (chartCover (G x)) := mem_baseSet_chartCover (G x)
    rw [hG'val (chartCover (G x)) x hx]
    show projOfPlane k m (F (chartCover (G x)) (⟨x, hx⟩, ⟨1, by norm_num⟩)) = Rmap (Pm x)
    rw [hFproj (chartCover (G x)) (⟨x, hx⟩, ⟨1, by norm_num⟩)]
    exact olQ_one k m P Pm x
  · intro x hxS
    have hx : x ∈ US (chartCover (G x)) := mem_baseSet_chartCover (G x)
    rw [hG'val (chartCover (G x)) x hx]
    have hconst : ∀ t : ↥(Set.Icc (0 : ℝ) 1), Qh (x, t) = projOfPlane k m (G x) := by
      intro t
      show olQ k m P Pm x (t : ℝ) = projOfPlane k m (G x)
      have h : olQ k m P Pm x (t : ℝ) = P x := by
        show Phi (symm (P x + (t : ℝ) • (symm (Pm x) - P x))) = P x
        rw [hSP x hxS]
        have h2 : P x + (t : ℝ) • (symm (P x) - P x) = P x := by
          rw [symm_eq_self_of_mem_Gr (hProj x)]
          module
        rw [h2, symm_eq_self_of_mem_Gr (hProj x)]
        exact Phi_eq_self_of_mem_Gr (hProj x) (finrank_amb (k + m))
      rw [h, hG x]
    have ha : Continuous fun t : ↥(Set.Icc (0 : ℝ) 1) =>
        F (chartCover (G x)) (⟨x, hx⟩, t) :=
      (hFc (chartCover (G x))).comp (continuous_const.prodMk continuous_id)
    have hab : ∀ t : ↥(Set.Icc (0 : ℝ) 1),
        projOfPlane k m (F (chartCover (G x)) (⟨x, hx⟩, t)) = projOfPlane k m (G x) := by
      intro t
      rw [hFproj (chartCover (G x)) (⟨x, hx⟩, t), hconst t]
    have h0 : F (chartCover (G x)) (⟨x, hx⟩, ⟨0, by norm_num⟩) = G x :=
      hF0 (chartCover (G x)) x hx
    exact congrFun (ol_path_lift_unique hkpos ha continuous_const hab h0) ⟨1, by norm_num⟩

end Work.ThomBordism
