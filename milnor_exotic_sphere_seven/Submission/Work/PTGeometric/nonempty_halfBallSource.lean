import Mathlib
import Submission.Work.PTGeometric.Source

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The half-ball source: `S^n × [1,2]` as a smooth manifold with boundary over the half-space model

`Work.PTGeometric.SourceModel n = S^n × [1,2]` carries a product manifold structure, modelled on
`ModelProd (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace 1)`.  The last-mile development needs the
*same* space as a manifold with boundary modelled on `EuclideanHalfSpace (n+1)`.

This file constructs that structure by re-indexing the model: the linear isometry
`Ψ : ℝ^n × ℝ^1 ≃ ℝ^{n+1}` (putting the last coordinate first) identifies the product model with the
half-space model, and the corresponding homeomorphism of the `H`-parts transports the charted space
and the smooth structure.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology
open WithLp

namespace Work.PTGeometric

noncomputable section

/-! ## Elementary continuous linear maps on `ℝ^m` -/

/-- The canonical continuous linear equivalence `ℝ^m ≃ (Fin m → ℝ)`. -/
abbrev euclToPi (m : ℕ) : EuclideanSpace ℝ (Fin m) ≃L[ℝ] ((j : Fin m) → ℝ) :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)

/-- The canonical continuous linear equivalence `(Fin m → ℝ) ≃ ℝ^m`. -/
abbrev piToEucl (m : ℕ) : ((j : Fin m) → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin m) :=
  (euclToPi m).symm

/-- `Fin.tail` as a continuous linear map. -/
def tailCLM (n : ℕ) : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (piToEucl n).toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun k : Fin n =>
      (ContinuousLinearMap.proj k.succ).comp (euclToPi (n + 1)).toContinuousLinearMap)

/-- `Fin.cons` as a continuous linear map. -/
def consCLM (n : ℕ) : ℝ × EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  (piToEucl (n + 1)).toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j : Fin (n + 1) =>
      Fin.cases (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin n)))
        (fun k => (ContinuousLinearMap.proj k).comp
          ((euclToPi n).toContinuousLinearMap.comp
            (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin n))))) j)

lemma tailCLM_apply (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) (k : Fin n) :
    tailCLM n x k = x k.succ := by
  simp [tailCLM, piToEucl, euclToPi]

lemma consCLM_apply_zero (n : ℕ) (a : ℝ) (z : EuclideanSpace ℝ (Fin n)) :
    consCLM n (a, z) 0 = a := by
  simp [consCLM, piToEucl, euclToPi]

lemma consCLM_apply_succ (n : ℕ) (a : ℝ) (z : EuclideanSpace ℝ (Fin n)) (k : Fin n) :
    consCLM n (a, z) k.succ = z k := by
  simp [consCLM, piToEucl, euclToPi]

lemma tailCLM_consCLM (n : ℕ) (a : ℝ) (z : EuclideanSpace ℝ (Fin n)) :
    tailCLM n (consCLM n (a, z)) = z := by
  ext k
  rw [tailCLM_apply, consCLM_apply_succ]

lemma consCLM_tail (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    consCLM n (x 0, tailCLM n x) = x := by
  ext j
  induction j using Fin.cases with
  | zero => rw [consCLM_apply_zero]
  | succ k => rw [consCLM_apply_succ, tailCLM_apply]

/-- `tail` is insensitive to a change of the `0`-th coordinate. -/
lemma tailCLM_update (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) (c : ℝ) :
    tailCLM n (WithLp.toLp 2 (Function.update x.ofLp 0 c)) = tailCLM n x := by
  ext k
  rw [tailCLM_apply, tailCLM_apply, WithLp.ofLp_toLp, Function.update_of_ne (Fin.succ_ne_zero k)]

/-! ## The re-indexing equivalence `Ψ` -/

/-- The source of the product model: `ℝ^n`. -/
abbrev E1 (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The source of the second (interval) model factor: `ℝ^1`. -/
abbrev E2 := EuclideanSpace ℝ (Fin 1)

/-- The half-space of dimension `1`, i.e. `[0,∞)`. -/
abbrev H1 := EuclideanHalfSpace 1

/-- The source of the half-space model of dimension `n+1`. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin (n + 1))

/-- The half-space model of dimension `n+1`. -/
abbrev H (n : ℕ) := EuclideanHalfSpace (n + 1)

/-- `(a, t) ↦ (t 0, a)`. -/
def pairCLM (n : ℕ) : E1 n × E2 →L[ℝ] ℝ × E1 n :=
  ((ContinuousLinearMap.proj (0 : Fin 1)).comp
      ((euclToPi 1).toContinuousLinearMap.comp (ContinuousLinearMap.snd ℝ (E1 n) E2))).prod
    (ContinuousLinearMap.fst ℝ (E1 n) E2)

/-- `x ↦ fun _ => x 0`. -/
def constE2CLM (n : ℕ) : E n →L[ℝ] E2 :=
  (piToEucl 1).toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun _ : Fin 1 =>
      (ContinuousLinearMap.proj (0 : Fin (n + 1))).comp
        (euclToPi (n + 1)).toContinuousLinearMap)

/-- `(a, t) ↦ cons (t 0) a` as a continuous linear map. -/
def Ψf (n : ℕ) : E1 n × E2 →L[ℝ] E n := (consCLM n).comp (pairCLM n)

/-- `x ↦ (tail x, fun _ => x 0)` as a continuous linear map. -/
def Ψg (n : ℕ) : E n →L[ℝ] E1 n × E2 := (tailCLM n).prod (constE2CLM n)

lemma Ψf_apply (n : ℕ) (z : E1 n × E2) : Ψf n z = consCLM n (z.2 0, z.1) := by
  simp [Ψf, pairCLM, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply]

lemma constE2CLM_apply (n : ℕ) (x : E n) :
    constE2CLM n x = WithLp.toLp 2 (fun _ : Fin 1 => x 0) := by
  simp [constE2CLM, piToEucl, euclToPi]

lemma Ψg_apply (n : ℕ) (x : E n) : Ψg n x = (tailCLM n x, constE2CLM n x) := rfl

lemma Ψg_Ψf (n : ℕ) (z : E1 n × E2) : Ψg n (Ψf n z) = z := by
  rw [Ψg_apply, Ψf_apply]
  refine Prod.ext ?_ ?_
  · show tailCLM n (consCLM n (z.2 0, z.1)) = z.1
    rw [tailCLM_consCLM]
  · show constE2CLM n (consCLM n (z.2 0, z.1)) = z.2
    rw [constE2CLM_apply]
    ext i
    fin_cases i
    rw [consCLM_apply_zero]
    rfl

lemma Ψf_Ψg (n : ℕ) (x : E n) : Ψf n (Ψg n x) = x := by
  rw [Ψg_apply, Ψf_apply, constE2CLM_apply]
  have h : (WithLp.toLp 2 (fun _ : Fin 1 => x 0)) 0 = x 0 := rfl
  rw [h, consCLM_tail]

/-- The re-indexing continuous linear equivalence `ℝ^n × ℝ^1 ≃ ℝ^{n+1}`. -/
def Ψ (n : ℕ) : (E1 n × E2) ≃L[ℝ] E n :=
  ContinuousLinearEquiv.equivOfInverse (Ψf n) (Ψg n) (Ψg_Ψf n) (Ψf_Ψg n)

lemma Ψ_apply (n : ℕ) (z : E1 n × E2) : Ψ n z = consCLM n (z.2 0, z.1) := by
  rw [show (Ψ n : E1 n × E2 → E n) = Ψf n from rfl, Ψf_apply]

lemma Ψ_symm_apply (n : ℕ) (x : E n) : (Ψ n).symm x = (tailCLM n x, constE2CLM n x) := by
  rw [show ((Ψ n).symm : E n → E1 n × E2) = Ψg n from rfl, Ψg_apply]

/-! ## The two model with corners, and the homeomorphism of the `H`-parts -/

/-- The product model with corners on `ℝ^n × ℝ^1` with target `ℝ^n × [0,∞)`. -/
abbrev Iold (n : ℕ) : ModelWithCorners ℝ (E1 n × E2) (E1 n × H1) := (𝓡 n).prod (𝓡∂ 1)

/-- The half-space model with corners on `ℝ^{n+1}`. -/
abbrev Inew (n : ℕ) : ModelWithCorners ℝ (E n) (H n) := 𝓡∂ (n + 1)

/-- The homeomorphism `ℝ^n × [0,∞) ≃ {x : ℝ^{n+1} // 0 ≤ x 0}` induced by `Ψ`. -/
def φfun (n : ℕ) : E1 n × H1 → H n :=
  fun z => ⟨Ψ n (z.1, z.2.val), by rw [Ψ_apply, consCLM_apply_zero]; exact z.2.2⟩

/-- Its inverse. -/
def φinv (n : ℕ) : H n → E1 n × H1 :=
  fun x => (tailCLM n x.val, ⟨constE2CLM n x.val, by rw [constE2CLM_apply]; exact x.2⟩)

lemma φinv_fst (n : ℕ) (x : H n) : (φinv n x).1 = tailCLM n x.val := rfl

lemma φinv_snd (n : ℕ) (x : H n) :
    (φinv n x).2 = (⟨constE2CLM n x.val, by rw [constE2CLM_apply]; exact x.2⟩ : H1) := rfl

lemma φinv_φfun (n : ℕ) (z : E1 n × H1) : φinv n (φfun n z) = z := by
  have h : (tailCLM n (φfun n z).val, constE2CLM n (φfun n z).val) = (z.1, z.2.val) :=
    Ψg_Ψf n (z.1, z.2.val)
  have h1 : (φinv n (φfun n z)).1 = z.1 := by
    rw [φinv_fst n]
    exact (Prod.ext_iff.mp h).1
  have h2 : (φinv n (φfun n z)).2 = z.2 := by
    rw [φinv_snd n]
    exact Subtype.ext (Prod.ext_iff.mp h).2
  exact Prod.ext_iff.mpr ⟨h1, h2⟩

lemma φfun_apply (n : ℕ) (z : E1 n × H1) :
    φfun n z = ⟨Ψ n (z.1, z.2.val), by rw [Ψ_apply, consCLM_apply_zero]; exact z.2.2⟩ := rfl

lemma φfun_φinv (n : ℕ) (x : H n) : φfun n (φinv n x) = x := by
  have h : Ψ n (tailCLM n x.val, constE2CLM n x.val) = x.val := Ψf_Ψg n x.val
  have h1 : (φinv n x).1 = tailCLM n x.val := φinv_fst n x
  have h2 : (φinv n x).2.val = constE2CLM n x.val := by rw [φinv_snd n]
  refine Subtype.ext ?_
  show Ψ n ((φinv n x).1, (φinv n x).2.val) = x.val
  rw [h1, h2]
  exact h

/-- The homeomorphism of model spaces. -/
def φ (n : ℕ) : (E1 n × H1) ≃ₜ H n where
  toFun := φfun n
  invFun := φinv n
  left_inv := φinv_φfun n
  right_inv := φfun_φinv n
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (Ψ n).continuous.comp (Continuous.prodMk continuous_fst
      (continuous_subtype_val.comp continuous_snd))
  continuous_invFun := by
    have h1 : Continuous (fun x : H n => (x.val : E n)) := continuous_subtype_val
    exact Continuous.prodMk ((tailCLM n).continuous.comp h1)
      (Continuous.subtype_mk ((constE2CLM n).continuous.comp h1) (fun x => by
        simpa [Function.comp_apply, constE2CLM_apply] using x.2))

lemma φ_apply (n : ℕ) (z : E1 n × H1) :
    φ n z = ⟨Ψ n (z.1, z.2.val), by rw [Ψ_apply, consCLM_apply_zero]; exact z.2.2⟩ := rfl

/-- `Inew` composed with `φ` is `Ψ` composed with `Iold`. -/
lemma Inew_comp_φ (n : ℕ) (z : E1 n × H1) : Inew n (φ n z) = Ψ n (Iold n z) := rfl

/-- On `ℝ^n` the boundaryless model is the identity. -/
lemma self_symm (n : ℕ) (a : E1 n) : (𝓡 n).symm a = a := rfl

/-- The inverse of the product model with corners, componentwise. -/
lemma Iold_symm_apply (n : ℕ) (w : E1 n × E2) :
    (Iold n).symm w = ((𝓡 n).symm w.1, (𝓡∂ 1).symm w.2) := by
  rw [Iold, modelWithCorners_prod_coe_symm]
  rfl

lemma Iold_symm_fst (n : ℕ) (w : E1 n × E2) : ((Iold n).symm w).1 = (𝓡 n).symm w.1 := by
  rw [Iold_symm_apply]

lemma Iold_symm_snd (n : ℕ) (w : E1 n × E2) : ((Iold n).symm w).2 = (𝓡∂ 1).symm w.2 := by
  rw [Iold_symm_apply]

/-- The inverse of the half-space model is the coordinatewise clamping. -/
lemma Inew_symm_val (n : ℕ) (x : E n) : ((Inew n).symm x).val
    = WithLp.toLp 2 (Function.update x.ofLp 0 (max (x 0) 0)) := by
  rw [Inew, modelWithCornersEuclideanHalfSpace_symm_apply]

/-- A constant function on `Fin 1` is unchanged by an update at `0`, up to `toLp`. -/
lemma toLp_update_const (a b : ℝ) :
    WithLp.toLp 2 (Function.update (fun _ : Fin 1 => a) 0 b)
      = WithLp.toLp 2 (fun _ : Fin 1 => b) := by
  congr 1
  funext i
  rw [Subsingleton.elim i 0, Function.update_self]

lemma halfSpace_symm_eq (b : ℝ) :
    (𝓡∂ 1).symm (WithLp.toLp 2 (fun _ : Fin 1 => b))
      = (⟨WithLp.toLp 2 (fun _ : Fin 1 => max b 0), by
          rw [WithLp.ofLp_toLp]; exact le_max_right _ _⟩ : EuclideanHalfSpace 1) := by
  rw [modelWithCornersEuclideanHalfSpace_symm_apply]
  congr 1
  rw [WithLp.ofLp_toLp]
  exact toLp_update_const b (max b 0)

lemma halfSpace_symm_val (b : ℝ) :
    ((𝓡∂ 1).symm (WithLp.toLp 2 (fun _ : Fin 1 => b))).val
      = WithLp.toLp 2 (fun _ : Fin 1 => max b 0) :=
  congrArg Subtype.val (halfSpace_symm_eq b)

/-- `φ.symm` composed with `Inew.symm` is `Iold.symm` composed with `Ψ.symm`. -/
lemma φ_symm_Inew_symm (n : ℕ) (x : E n) :
    (φ n).symm ((Inew n).symm x) = (Iold n).symm ((Ψ n).symm x) := by
  have hφ : (φ n).symm ((Inew n).symm x) = φinv n ((Inew n).symm x) := rfl
  rw [hφ]
  refine Prod.ext_iff.mpr ⟨?_, ?_⟩
  · rw [φinv_fst, Inew_symm_val, tailCLM_update, Iold_symm_fst, Ψ_symm_apply]
    simp only [self_symm]
  · rw [φinv_snd, Iold_symm_snd, Ψ_symm_apply]
    refine Subtype.ext ?_
    show (constE2CLM n ((Inew n).symm x).val : E2) = ((𝓡∂ 1).symm (constE2CLM n x)).val
    rw [Inew_symm_val, constE2CLM_apply, WithLp.ofLp_toLp, Function.update_self,
      constE2CLM_apply, halfSpace_symm_val]


/-! ## The charted space and the smooth structure on the source -/

lemma trans_symm_assoc {M H H' : Type*} [TopologicalSpace M] [TopologicalSpace H]
    [TopologicalSpace H'] (c c' : OpenPartialHomeomorph M H) (φ : H ≃ₜ H') :
    (c ≫ₕ φ.toOpenPartialHomeomorph).symm ≫ₕ (c' ≫ₕ φ.toOpenPartialHomeomorph)
      = φ.symm.toOpenPartialHomeomorph ≫ₕ (c.symm ≫ₕ c') ≫ₕ φ.toOpenPartialHomeomorph := by
  rw [show (c ≫ₕ φ.toOpenPartialHomeomorph).symm
        = φ.symm.toOpenPartialHomeomorph ≫ₕ c.symm from rfl]
  simp only [OpenPartialHomeomorph.trans_assoc]

/-- The product charted space structure on `SourceModel n` (the model is an opaque `def`, so the
product instance is registered here explicitly). -/
instance instChartedSpaceSourceModelProd (n : ℕ) :
    ChartedSpace (E1 n × H1) (SourceModel n) := by
  haveI : Fact ((1 : ℝ) < 2) := ⟨by norm_num⟩
  exact inferInstanceAs (ChartedSpace (ModelProd (E1 n) H1)
    (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 × Set.Icc (1 : ℝ) 2))

/-- The product smooth structure on `SourceModel n`, at smoothness `∞`. -/
instance instIsManifoldSourceModelProd (n : ℕ) : IsManifold (Iold n) ∞ (SourceModel n) := by
  haveI : Fact ((1 : ℝ) < 2) := ⟨by norm_num⟩
  haveI h : IsManifold (Iold n) ω (SourceModel n) :=
    inferInstanceAs (IsManifold ((𝓡 n).prod (𝓡∂ 1)) ω
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 × Set.Icc (1 : ℝ) 2))
  exact IsManifold.of_le (m := ∞) (n := ω) le_top

/-- `SourceModel n` is nonempty. -/
instance instNonemptySourceModel (n : ℕ) : Nonempty (SourceModel n) :=
  ⟨(⟨EuclideanSpace.single 0 1, by simp [Metric.mem_sphere]⟩, ⟨1, by norm_num⟩)⟩

/-- The charted space structure on `S^n × [1,2]` modelled on the half-space of dimension `n+1`. -/
noncomputable def chartedSpaceHalf (n : ℕ) : ChartedSpace (H n) (SourceModel n) where
  atlas := Set.range fun x : SourceModel n =>
    (chartAt (E1 n × H1) x).trans (φ n).toOpenPartialHomeomorph
  chartAt := fun x => (chartAt (E1 n × H1) x).trans (φ n).toOpenPartialHomeomorph
  mem_chart_source := fun x => by
    rw [OpenPartialHomeomorph.trans_source]
    exact ⟨mem_chart_source (E1 n × H1) x, by
      rw [Homeomorph.toOpenPartialHomeomorph_source]; trivial⟩
  chart_mem_atlas := fun x => ⟨x, rfl⟩

instance instChartedSpaceHalf (n : ℕ) : ChartedSpace (H n) (SourceModel n) :=
  chartedSpaceHalf n

/-- Conjugation of smoothness by the re-indexing `Ψ`. -/
lemma contDiffOn_conj_linear (n : ℕ) {f : E1 n × E2 → E1 n × E2} {s : Set (E1 n × E2)}
    (hf : ContDiffOn ℝ ∞ f s) :
    ContDiffOn ℝ ∞ (⇑(Ψ n) ∘ f ∘ ⇑(Ψ n).symm) (⇑(Ψ n).symm ⁻¹' s) := by
  have h1 : ContDiffOn ℝ ∞ (f ∘ ⇑(Ψ n).symm) (⇑(Ψ n).symm ⁻¹' s) :=
    hf.comp ((Ψ n).symm).contDiff.contDiffOn (fun x hx => hx)
  exact ((Ψ n).contDiff.contDiffOn).comp h1 (fun x _ => Set.mem_univ _)

lemma Ψ_symm_preimage_range_Iold (n : ℕ) :
    ⇑(Ψ n).symm ⁻¹' Set.range (Iold n) = Set.range (Inew n) := by
  ext x
  show (Ψ n).symm x ∈ Set.range ((𝓡 n).prod (𝓡∂ 1)) ↔ x ∈ Set.range (𝓡∂ (n + 1))
  simp only [ModelWithCorners.range_prod, range_modelWithCornersEuclideanHalfSpace,
    ModelWithCorners.range_eq_univ, Ψ_symm_apply, Set.mem_prod, Set.mem_ofPred_eq,
    Set.mem_univ, true_and, constE2CLM_apply]

/-- The main computation: conjugation of a `C^∞` transition map by the model re-indexing. -/
lemma contDiffOn_conj (n : ℕ) (g : OpenPartialHomeomorph (E1 n × H1) (E1 n × H1))
    (hg : ContDiffOn ℝ ∞ (⇑(Iold n) ∘ ⇑g ∘ ⇑(Iold n).symm)
      ((Iold n).symm ⁻¹' g.source ∩ Set.range (Iold n))) :
    ContDiffOn ℝ ∞
      (⇑(Inew n) ∘ ⇑((φ n).symm.toOpenPartialHomeomorph ≫ₕ g ≫ₕ (φ n).toOpenPartialHomeomorph)
        ∘ ⇑(Inew n).symm)
      ((Inew n).symm ⁻¹'
        ((φ n).symm.toOpenPartialHomeomorph ≫ₕ g ≫ₕ (φ n).toOpenPartialHomeomorph).source
        ∩ Set.range (Inew n)) := by
  have hsrc : ((φ n).symm.toOpenPartialHomeomorph ≫ₕ g ≫ₕ (φ n).toOpenPartialHomeomorph).source
      = (φ n).symm.toOpenPartialHomeomorph ⁻¹' g.source := by
    simp only [OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
      Set.univ_inter, Set.preimage_univ, Set.inter_univ]
  have hfun : ⇑(Inew n)
        ∘ ⇑((φ n).symm.toOpenPartialHomeomorph ≫ₕ g ≫ₕ (φ n).toOpenPartialHomeomorph)
        ∘ ⇑(Inew n).symm
      = ⇑(Ψ n) ∘ (⇑(Iold n) ∘ ⇑g ∘ ⇑(Iold n).symm) ∘ ⇑(Ψ n).symm := by
    funext x
    show Inew n ((φ n) (g ((φ n).symm ((Inew n).symm x))))
      = Ψ n (Iold n (g ((Iold n).symm ((Ψ n).symm x))))
    rw [φ_symm_Inew_symm n x, Inew_comp_φ n]
  have hR2' : ⇑(φ n).symm.toOpenPartialHomeomorph ∘ ⇑(Inew n).symm
      = ⇑(Iold n).symm ∘ ⇑(Ψ n).symm := by
    funext x
    show (φ n).symm ((Inew n).symm x) = (Iold n).symm ((Ψ n).symm x)
    exact φ_symm_Inew_symm n x
  have hset : (Inew n).symm ⁻¹'
          ((φ n).symm.toOpenPartialHomeomorph ≫ₕ g ≫ₕ (φ n).toOpenPartialHomeomorph).source
        ∩ Set.range (Inew n)
      = ⇑(Ψ n).symm ⁻¹' ((Iold n).symm ⁻¹' g.source ∩ Set.range (Iold n)) := by
    rw [hsrc, ← Set.preimage_comp, hR2', Set.preimage_comp, ← Ψ_symm_preimage_range_Iold,
      ← Set.preimage_inter]
  rw [hfun, hset]
  exact contDiffOn_conj_linear n hg

/-- `S^n × [1,2]` as a smooth manifold with boundary modelled on the half-space of dimension
`n+1`. -/
theorem isManifoldHalf (n : ℕ) : IsManifold (Inew n) ∞ (SourceModel n) := by
  refine isManifold_of_contDiffOn (Inew n) ∞ (SourceModel n) ?_
  intro e e' he he'
  obtain ⟨x, rfl⟩ := he
  obtain ⟨x', rfl⟩ := he'
  have hmid : (chartAt (E1 n × H1) x).symm ≫ₕ (chartAt (E1 n × H1) x')
      ∈ contDiffGroupoid ∞ (Iold n) :=
    StructureGroupoid.compatible (contDiffGroupoid ∞ (Iold n))
      (chart_mem_atlas (E1 n × H1) x) (chart_mem_atlas (E1 n × H1) x')
  rw [trans_symm_assoc]
  exact contDiffOn_conj n ((chartAt (E1 n × H1) x).symm ≫ₕ (chartAt (E1 n × H1) x'))
    (mem_groupoid_of_pregroupoid.mp hmid).1

instance instIsManifoldHalf (n : ℕ) : IsManifold (𝓡∂ (n + 1)) ∞ (SourceModel n) :=
  isManifoldHalf n

/-- **The compact half-ball source exists**: `S^n × [1,2]` with the half-space model. -/
theorem nonempty_halfBallSource (n : ℕ) : Nonempty (Work.PTGeometric.HalfBallSource n) :=
  ⟨{ M := SourceModel n
     homeo := Homeomorph.refl (SourceModel n) }⟩

end

end Work.PTGeometric
