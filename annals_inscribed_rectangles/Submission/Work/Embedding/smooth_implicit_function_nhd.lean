import Mathlib
import Submission.Work.Embedding.isInvertible_adjoint_comp

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


namespace Work.Embedding

open scoped ContDiff
open Filter

/-- The adjoint operation `T ↦ T†`, as a real continuous linear map, for continuous linear maps
between real inner product spaces. -/
noncomputable def adjointCLM {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] :
    (E →L[ℝ] F) →L[ℝ] (F →L[ℝ] E) :=
  LinearMap.mkContinuous
    { toFun := fun T => T.adjoint
      map_add' := fun T S => by ext x; simp
      map_smul' := fun c T => by ext x; simp }
    1
    (fun T => by
      rw [one_mul]
      exact le_of_eq ((ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := E) (F := F)).norm_map T))

lemma adjointCLM_apply {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (T : E →L[ℝ] F) : adjointCLM T = T.adjoint := rfl

/-- For a continuous linear endomorphism of a real Banach space, being invertible is the same as
being a unit of the normed ring of continuous linear endomorphisms. -/
lemma isInvertible_iff_isUnit_end {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (S : E →L[ℝ] E) : S.IsInvertible ↔ IsUnit S := by
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  exact ⟨fun h => h.bijective, fun h => ⟨ContinuousLinearEquiv.ofBijective S
    (by rw [LinearMap.ker_eq_bot]; simpa using h.1)
    (by rw [LinearMap.range_eq_top]; simpa using h.2),
    ContinuousLinearEquiv.coe_ofBijective _ _ _⟩⟩

/-- The invertible continuous linear endomorphisms of a real Banach space form an open set. -/
lemma isOpen_isInvertible_end {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] : IsOpen {S : E →L[ℝ] E | S.IsInvertible} := by
  rw [show {S : E →L[ℝ] E | S.IsInvertible} = {S : E →L[ℝ] E | IsUnit S} from
    Set.ext fun S => isInvertible_iff_isUnit_end S]
  exact Units.isOpen

/-- The invertible continuous linear maps between two real Banach spaces form an open set. -/
lemma isOpen_isInvertible {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] :
    IsOpen {T : E →L[ℝ] F | T.IsInvertible} := by
  rw [isOpen_iff_mem_nhds]
  rintro T₀ ⟨e₀, he₀⟩
  have hcont : Continuous (fun T : E →L[ℝ] F => (e₀.symm : F →L[ℝ] E) ∘L T) :=
    (ContinuousLinearMap.compL ℝ E F E (e₀.symm : F →L[ℝ] E)).continuous
  have hset : {T : E →L[ℝ] F | T.IsInvertible} =
      (fun T : E →L[ℝ] F => (e₀.symm : F →L[ℝ] E) ∘L T) ⁻¹'
        {S : E →L[ℝ] E | S.IsInvertible} := by
    ext T
    exact ContinuousLinearMap.isInvertible_equiv_comp.symm
  rw [hset]
  exact (hcont.isOpen_preimage _ isOpen_isInvertible_end).mem_nhds
    (ContinuousLinearMap.isInvertible_equiv_comp.mpr ⟨e₀, he₀⟩)

/-- The negative of an invertible continuous linear endomorphism is invertible. -/
lemma isInvertible_neg' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : E →L[ℝ] E} (h : T.IsInvertible) : (-T).IsInvertible := by
  refine ContinuousLinearMap.IsInvertible.of_inverse (f := -T) (g := -(T.inverse)) ?_ ?_
  · rw [ContinuousLinearMap.neg_comp, ContinuousLinearMap.comp_neg, neg_neg,
      h.self_comp_inverse]
  · rw [ContinuousLinearMap.neg_comp, ContinuousLinearMap.comp_neg, neg_neg,
      h.inverse_comp_self]

theorem smooth_implicit_function_nhd {n N : ℕ}
    (ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    {V : Set (EuclideanSpace ℝ (Fin n))} {u₀ : EuclideanSpace ℝ (Fin n)}
    (hV : IsOpen V) (hu₀ : u₀ ∈ V) (hψ : ContDiffOn ℝ ∞ ψ V)
    (hinj : Function.Injective (fderiv ℝ ψ u₀)) :
    ∃ (η : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin n))
      (O : Set (EuclideanSpace ℝ (Fin N))),
      IsOpen O ∧ ψ u₀ ∈ O ∧ η (ψ u₀) = u₀ ∧ ContDiffOn ℝ ∞ η O ∧
      (∀ᶠ z in nhds (ψ u₀, u₀),
        (fderiv ℝ ψ z.2).adjoint (z.1 - ψ z.2) = 0 ↔ η z.1 = z.2) := by
  classical
  have hu₀V : V ∈ nhds u₀ := hV.mem_nhds hu₀
  have hψat : ContDiffAt ℝ ∞ ψ u₀ := hψ.contDiffAt hu₀V
  have hdfat : ContDiffAt ℝ ∞ (fderiv ℝ ψ) u₀ :=
    (hψ.fderiv_of_isOpen hV (by simp)).contDiffAt hu₀V
  have hnz : (∞ : ℕ∞ω) ≠ 0 := by simp
  let A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin N) := fderiv ℝ ψ u₀
  let A₂ : EuclideanSpace ℝ (Fin n) →L[ℝ]
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin N)) := fderiv ℝ (fderiv ℝ ψ) u₀
  let F : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun z => (fderiv ℝ ψ z.2).adjoint (z.1 - ψ z.2)
  let prodF : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin N) := fun z => (F z, z.1)
  have hψm : ∀ m : ℕ, ContDiffOn ℝ (m : ℕ∞ω) ψ V := fun m =>
    hψ.of_le (by exact_mod_cast (le_top : (m : ℕ∞) ≤ ⊤))
  have hdfm : ∀ m : ℕ, ContDiffOn ℝ (m : ℕ∞ω) (fderiv ℝ ψ) V := fun m =>
    hψ.fderiv_of_isOpen hV (by exact_mod_cast (le_top : ((m + 1 : ℕ) : ℕ∞) ≤ ⊤))
  -- ### `F` is `C^∞` at the base point
  have hFcont : ContDiffAt ℝ ∞ F (ψ u₀, u₀) := by
    have hsndc : ContDiffAt ℝ ∞ (fun z : EuclideanSpace ℝ (Fin N) ×
        EuclideanSpace ℝ (Fin n) => z.2) (ψ u₀, u₀) := by fun_prop
    have hc : ContDiffAt ℝ ∞ (fun z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin n) =>
        (fderiv ℝ ψ z.2).adjoint) (ψ u₀, u₀) := by
      have h1 : ContDiffAt ℝ ∞ (fun z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin n) =>
          fderiv ℝ ψ z.2) (ψ u₀, u₀) := hdfat.comp (ψ u₀, u₀) hsndc
      have h2 : ContDiffAt ℝ ∞
          (⇑(adjointCLM (E := EuclideanSpace ℝ (Fin n)) (F := EuclideanSpace ℝ (Fin N))))
          (fderiv ℝ ψ u₀) := (ContinuousLinearMap.contDiff _).contDiffAt
      have h3 := h2.comp (ψ u₀, u₀) h1
      simpa only [Function.comp_def, adjointCLM_apply] using h3
    have hd : ContDiffAt ℝ ∞ (fun z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin n) =>
        z.1 - ψ z.2) (ψ u₀, u₀) := by
      have h2 : ContDiffAt ℝ ∞ (fun z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin n) =>
          ψ z.2) (ψ u₀, u₀) := hψat.comp (ψ u₀, u₀) hsndc
      exact (by fun_prop : ContDiffAt ℝ ∞ (fun z : EuclideanSpace ℝ (Fin N) ×
          EuclideanSpace ℝ (Fin n) => z.1) (ψ u₀, u₀)).sub h2
    exact hc.clm_apply hd
  -- ### the derivative of `F` at the base point
  have hAfd : HasFDerivAt (fderiv ℝ ψ) A₂ u₀ := (hdfat.differentiableAt hnz).hasFDerivAt
  have hψfd : HasFDerivAt ψ A u₀ := (hψat.differentiableAt hnz).hasFDerivAt
  have hsnd_fd : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin n) =>
      z.2) (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin N)) (EuclideanSpace ℝ (Fin n)))
      (ψ u₀, u₀) := hasFDerivAt_snd
  have hfst_fd : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin n) =>
      z.1) (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin N)) (EuclideanSpace ℝ (Fin n)))
      (ψ u₀, u₀) := hasFDerivAt_fst
  have hc_fd : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin n) =>
      (fderiv ℝ ψ z.2).adjoint)
      (adjointCLM (E := EuclideanSpace ℝ (Fin n)) (F := EuclideanSpace ℝ (Fin N)) ∘L
        (A₂ ∘L ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin N))
          (EuclideanSpace ℝ (Fin n)))) (ψ u₀, u₀) := by
    have h := (ContinuousLinearMap.hasFDerivAt (x := fderiv ℝ ψ u₀)
      (adjointCLM (E := EuclideanSpace ℝ (Fin n)) (F := EuclideanSpace ℝ (Fin N)))).comp
      (ψ u₀, u₀) (hAfd.comp (ψ u₀, u₀) hsnd_fd)
    simpa only [Function.comp_def, adjointCLM_apply] using h
  have hd_fd : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin n) =>
      z.1 - ψ z.2)
      (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin N)) (EuclideanSpace ℝ (Fin n)) -
        A ∘L ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin N))
          (EuclideanSpace ℝ (Fin n))) (ψ u₀, u₀) :=
    hfst_fd.sub (hψfd.comp (ψ u₀, u₀) hsnd_fd)
  have hFfd : HasFDerivAt F
      ((A.adjoint).comp (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin N))
            (EuclideanSpace ℝ (Fin n)) -
          A ∘L ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin N))
            (EuclideanSpace ℝ (Fin n)))
        + (adjointCLM (E := EuclideanSpace ℝ (Fin n)) (F := EuclideanSpace ℝ (Fin N)) ∘L
            (A₂ ∘L ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin N))
              (EuclideanSpace ℝ (Fin n)))).flip
            ((ψ u₀, u₀).1 - ψ (ψ u₀, u₀).2)) (ψ u₀, u₀) :=
    hc_fd.clm_apply hd_fd
  have hL : fderiv ℝ F (ψ u₀, u₀) ∘L
      ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin N)) (EuclideanSpace ℝ (Fin n))
      = -(A.adjoint ∘L A) := by
    rw [hFfd.fderiv]
    ext w
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
  -- ### the hypothesis of the implicit function theorem
  have hB : (A.adjoint ∘L A).IsInvertible := isInvertible_adjoint_comp A hinj
  have hif : (fderiv ℝ F (ψ u₀, u₀) ∘L
      ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin N))
        (EuclideanSpace ℝ (Fin n))).IsInvertible := by
    rw [hL]
    exact isInvertible_neg' hB
  -- ### the implicit function
  let hφd : ImplicitFunctionData ℝ
      (EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin N)) :=
    (hFcont.hasStrictFDerivAt hnz).implicitFunctionDataOfProdDomain hif
  let η : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin n) :=
    hFcont.implicitFunction hnz hif
  let e : OpenPartialHomeomorph
      (EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin N)) := hφd.toOpenPartialHomeomorph
  have hη_eq : ∀ x, η x = (e.symm (F (ψ u₀, u₀), x)).2 := fun x => rfl
  have hη_self : η (ψ u₀) = u₀ := hFcont.implicitFunction_apply_self hnz hif
  have hη_iff : ∀ᶠ z in nhds (ψ u₀, u₀), F z = F (ψ u₀, u₀) ↔ η z.1 = z.2 :=
    hFcont.eventually_apply_eq_iff_implicitFunction hnz hif
  -- ### smoothness of `η` on a neighbourhood
  have htube_open : IsOpen {z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin n) | z.2 ∈ V} :=
    hV.preimage continuous_snd
  have htube_mem : (ψ u₀, u₀) ∈
      {z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin n) | z.2 ∈ V} := hu₀
  have hFOn : ∀ m : ℕ, ContDiffOn ℝ (m : ℕ∞ω) F
      {z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin n) | z.2 ∈ V} := by
    intro m
    have h1 : ContDiffOn ℝ (m : ℕ∞ω) (fun z : EuclideanSpace ℝ (Fin N) ×
        EuclideanSpace ℝ (Fin n) => fderiv ℝ ψ z.2)
        {z | z.2 ∈ V} :=
      (hdfm m).comp contDiffOn_snd (fun z hz => hz)
    have h2 : ContDiffOn ℝ (m : ℕ∞ω) (fun z : EuclideanSpace ℝ (Fin N) ×
        EuclideanSpace ℝ (Fin n) => (fderiv ℝ ψ z.2).adjoint) {z | z.2 ∈ V} := by
      have h := ((ContinuousLinearMap.contDiff
        (adjointCLM (E := EuclideanSpace ℝ (Fin n))
          (F := EuclideanSpace ℝ (Fin N)))).contDiffOn).comp h1 (fun z _ => Set.mem_univ _)
      simpa only [Function.comp_def, adjointCLM_apply] using h
    have h3 : ContDiffOn ℝ (m : ℕ∞ω) (fun z : EuclideanSpace ℝ (Fin N) ×
        EuclideanSpace ℝ (Fin n) => z.1 - ψ z.2) {z | z.2 ∈ V} :=
      contDiffOn_fst.sub ((hψm m).comp contDiffOn_snd (fun z hz => hz))
    exact h2.clm_apply h3
  have hprodOn : ∀ m : ℕ, ContDiffOn ℝ (m : ℕ∞ω) prodF
      {z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin n) | z.2 ∈ V} :=
    fun m => (hFOn m).prodMk contDiffOn_fst
  have hInvU : (fderiv ℝ prodF (ψ u₀, u₀)).IsInvertible := hφd.isInvertible_fderiv_prodFun
  have hcontfd : ContinuousAt (fun z : EuclideanSpace ℝ (Fin N) ×
      EuclideanSpace ℝ (Fin n) => fderiv ℝ prodF z) (ψ u₀, u₀) := by
    have h2 : ContDiffOn ℝ (2 : ℕ∞ω) prodF
        {z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin n) | z.2 ∈ V} := hprodOn 2
    have h1 : ContDiffOn ℝ (1 : ℕ∞ω) (fderiv ℝ prodF)
        {z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin n) | z.2 ∈ V} :=
      h2.fderiv_of_isOpen htube_open (by norm_num)
    exact h1.continuousOn.continuousAt (htube_open.mem_nhds htube_mem)
  have hGood_mem : {z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin n) |
        z.2 ∈ V ∧ (fderiv ℝ prodF z).IsInvertible} ∈ nhds (ψ u₀, u₀) :=
    Filter.inter_mem (htube_open.mem_nhds htube_mem)
      (hcontfd.preimage_mem_nhds (isOpen_isInvertible.mem_nhds hInvU))
  have htp : (F (ψ u₀, u₀), ψ u₀) ∈ e.target := hφd.map_pt_mem_toOpenPartialHomeomorph_target
  have hsymm_pt : (⇑e.symm) (F (ψ u₀, u₀), ψ u₀) = (ψ u₀, u₀) :=
    e.left_inv hφd.pt_mem_toOpenPartialHomeomorph_source
  have hpre : (⇑e.symm) ⁻¹' {z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin n) |
      z.2 ∈ V ∧ (fderiv ℝ prodF z).IsInvertible} ∈ nhds (F (ψ u₀, u₀), ψ u₀) :=
    (e.continuousAt_symm htp).preimage_mem_nhds (by rw [hsymm_pt]; exact hGood_mem)
  obtain ⟨U, hUsub, hUopen, hUmem⟩ := mem_nhds_iff.mp hpre
  let Tset : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin N)) := U ∩ e.target
  have hTset_open : IsOpen Tset := hUopen.inter e.open_target
  have hTset_mem : (F (ψ u₀, u₀), ψ u₀) ∈ Tset := ⟨hUmem, htp⟩
  have hTset_good : ∀ a ∈ Tset, (⇑e.symm) a ∈ {z : EuclideanSpace ℝ (Fin N) ×
      EuclideanSpace ℝ (Fin n) | z.2 ∈ V ∧ (fderiv ℝ prodF z).IsInvertible} :=
    fun a ha => hUsub ha.1
  have hsymm_smooth : ∀ m : ℕ, ContDiffOn ℝ (m : ℕ∞ω) (⇑e.symm) Tset := by
    intro m a ha
    rw [contDiffWithinAt_iff_contDiffAt (hTset_open.mem_nhds ha)]
    obtain ⟨hzV, hzInv⟩ := hTset_good a ha
    have h1 : ContDiffAt ℝ (m : ℕ∞ω) (⇑e) ((⇑e.symm) a) :=
      (hprodOn m).contDiffAt (htube_open.mem_nhds hzV)
    obtain ⟨e', he'⟩ := hzInv
    have h2 : HasFDerivAt (⇑e) (e' : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin N)) ((⇑e.symm) a) := by
      have h3 : HasFDerivAt prodF (fderiv ℝ prodF ((⇑e.symm) a)) ((⇑e.symm) a) :=
        ((hprodOn 1).contDiffAt (htube_open.mem_nhds hzV)).differentiableAt
          (by norm_num) |>.hasFDerivAt
      exact h3.congr_fderiv he'.symm
    exact e.contDiffAt_symm ha.2 h2 h1
  have hsymm_infty : ContDiffOn ℝ ∞ (⇑e.symm) Tset := contDiffOn_infty.mpr hsymm_smooth
  refine ⟨η, {x : EuclideanSpace ℝ (Fin N) | (F (ψ u₀, u₀), x) ∈ Tset}, ?_, ?_, hη_self, ?_, ?_⟩
  · exact hTset_open.preimage (continuous_const.prodMk continuous_id)
  · exact hTset_mem
  · rw [contDiffOn_infty]
    intro m
    have hbase : ContDiffOn ℝ (m : ℕ∞ω)
        (fun x : EuclideanSpace ℝ (Fin N) => (⇑e.symm) (F (ψ u₀, u₀), x))
        {x : EuclideanSpace ℝ (Fin N) | (F (ψ u₀, u₀), x) ∈ Tset} :=
      (hsymm_infty.of_le (by exact_mod_cast (le_top : (m : ℕ∞) ≤ ⊤))).comp
        (ContDiffOn.prodMk contDiffOn_const contDiffOn_id) (fun x hx => hx)
    have hsnd_on : ContDiffOn ℝ (m : ℕ∞ω)
        (fun p : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin n) => p.2) Set.univ :=
      contDiffOn_snd
    have hcomp := ContDiffOn.comp
      (f := fun x : EuclideanSpace ℝ (Fin N) => e.symm (F (ψ u₀, u₀), x))
      (g := fun p : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin n) => p.2)
      (s := {x : EuclideanSpace ℝ (Fin N) | (F (ψ u₀, u₀), x) ∈ Tset})
      (t := Set.univ) hsnd_on hbase (fun x _ => Set.mem_univ _)
    refine hcomp.congr (fun x hx => ?_)
    show η x = (e.symm (F (ψ u₀, u₀), x)).2
    exact hη_eq x
  · have hF0 : F (ψ u₀, u₀) = 0 := by
      change (fderiv ℝ ψ u₀).adjoint (ψ u₀ - ψ u₀) = 0
      simp
    filter_upwards [hη_iff] with z hz
    rw [hF0] at hz
    exact hz

end Work.Embedding
