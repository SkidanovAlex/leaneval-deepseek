import Mathlib
import Submission.Work.WilE2.Setup
import Submission.Work.WilE2.integral_curve_unique_global
import Submission.Work.WilE2.exists_linearEquiv_fst_eq_of_ker

open scoped Topology ContDiff
open Filter
set_option autoImplicit false

namespace Work.WilE2

/-! ## Auxiliary lemmas -/

lemma exists_pos_abs_lt_of_eventually {P : ℝ → Prop} (h : ∀ᶠ t in nhds (0:ℝ), P t) :
    ∃ δ > 0, ∀ t, |t| < δ → P t := by
  obtain ⟨S, hS, hSP⟩ := h.exists_mem
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hS
  exact ⟨ε, hε, fun t ht => hSP t (hball (by rw [Metric.mem_ball, Real.dist_eq, sub_zero]; exact ht))⟩

lemma hasDerivAt_comp {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → E} {f' : E} {g : E → F} {g' : E →L[ℝ] F} {x : ℝ}
    (hg : HasFDerivAt g g' (f x)) (hf : HasDerivAt f f' x) :
    HasDerivAt (g ∘ f) (g' f') x := by
  first
  | exact hg.comp_hasDerivAt (x := x) hf
  | exact hg.comp_hasDerivAt x hf
  | exact hg.comp_hasDerivAt hf

/-- `fderiv ℝ V z` is the tuple of the differentials of the components. -/
lemma fderiv_eq_pi {m : ℕ} (V : (Fin m → ℝ) → (Fin (m - 1) → ℝ)) (hV : ContDiff ℝ 1 V)
    (z : Fin m → ℝ) :
    fderiv ℝ V z = ContinuousLinearMap.pi (fun i => fderiv ℝ (fun w => V w i) z) := by
  have hcomp : ∀ i : Fin (m - 1),
      HasStrictFDerivAt (fun w => V w i) (fderiv ℝ (fun w => V w i) z) z :=
    fun i => (contDiffAt_pi.mp hV.contDiffAt i).hasStrictFDerivAt (by norm_num)
  have hst : HasStrictFDerivAt V (fderiv ℝ V z) z :=
    hV.contDiffAt.hasStrictFDerivAt (by norm_num)
  exact hst.hasFDerivAt.unique (hasStrictFDerivAt_pi.mpr hcomp).hasFDerivAt

/-- A surjective `D : ℝᵐ → ℝ^{m-1}` has one-dimensional kernel. -/
lemma smul_eq_of_range_top {m : ℕ} (D : (Fin m → ℝ) →L[ℝ] (Fin (m - 1) → ℝ))
    (hD : D.range = ⊤) {u v : Fin m → ℝ} (hu : D u = 0) (hv : D v = 0) (hu0 : u ≠ 0) :
    ∃ c : ℝ, v = c • u := by
  obtain ⟨M, hM1, hM2⟩ := exists_linearEquiv_fst_eq_of_ker D u hD hu hu0
  have hkey : ∀ x : Fin m → ℝ, D x = 0 → x ∈ Submodule.span ℝ {u} := by
    intro x hx
    set q : ℝ × (Fin (m-1) → ℝ) := M.symm x with hq
    obtain ⟨a, y, hay⟩ : ∃ (a : ℝ) (y : Fin (m-1) → ℝ), q = (a, y) := ⟨q.1, q.2, rfl⟩
    have hMq : M q = x := by rw [hq]; exact M.apply_symm_apply x
    have hMx : M (a, y) = x := by rw [← hay]; exact hMq
    have hsplit : M (a, y) = a • M (1, 0) + M (0, y) := by
      have e1 : (a, y) = a • (1, 0) + (0, y) := by ext <;> simp
      rw [e1, map_add, map_smul]
    have hy : y = 0 := by
      have h1 : D (M (a, y)) = y := by
        rw [hsplit, map_add, map_smul, hM1, hu, hM2 y]
        simp
      rw [hMx, hx] at h1
      exact h1.symm
    rw [Submodule.mem_span_singleton]
    refine ⟨a, ?_⟩
    rw [hMx.symm, hy]
    have e2 : (a, (0 : Fin (m-1) → ℝ)) = a • (1, 0) := by ext <;> simp
    rw [e2, map_smul, hM1]
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hkey v hv)
  exact ⟨c, hc.symm⟩

/-- The velocity of a curve lying in the zero set of `V` is tangent to that zero set. -/
lemma curve_fderiv_eq_zero {m : ℕ} (V : (Fin m → ℝ) → (Fin (m - 1) → ℝ)) (hV : ContDiff ℝ 1 V)
    {ψ : ℝ → (Fin m → ℝ)} {s : ℝ} (hsd : HasFDerivAt ψ (fderiv ℝ ψ s) s)
    (hVs : ∀ᶠ t in nhds s, V (ψ t) = 0) :
    (fderiv ℝ V (ψ s)) ((fderiv ℝ ψ s) 1) = 0 := by
  have h1 : HasFDerivAt (fun t : ℝ => V (ψ t))
      ((fderiv ℝ V (ψ s)).comp (fderiv ℝ ψ s)) s := by
    have hVd : HasFDerivAt V (fderiv ℝ V (ψ s)) (ψ s) :=
      (hV.contDiffAt.hasStrictFDerivAt (by norm_num : (1:ℕ∞ω) ≠ 0)).hasFDerivAt
    first
    | exact hVd.comp (x := s) hsd
    | exact hVd.comp s hsd
    | exact hVd.comp hsd
  have h2 : HasFDerivAt (fun t : ℝ => V (ψ t)) (0 : ℝ →L[ℝ] (Fin (m-1) → ℝ)) s := by
    have hconst : HasFDerivAt (fun _ : ℝ => (0 : Fin (m-1) → ℝ))
        (0 : ℝ →L[ℝ] (Fin (m-1) → ℝ)) s := hasFDerivAt_const (0 : Fin (m-1) → ℝ) s
    refine hconst.congr_of_eventuallyEq ?_
    filter_upwards [hVs] with t ht
    simpa using ht
  have h3 : (fderiv ℝ V (ψ s)).comp (fderiv ℝ ψ s) = 0 := h1.unique h2
  simpa using congrArg (fun (f : ℝ →L[ℝ] (Fin (m-1) → ℝ)) => f 1) h3

/-- Along the parametrisation, `ℓ` of the velocity is `1`. -/
lemma fderiv_apply_one_eq_one {m : ℕ} (ℓ : (Fin m → ℝ) →L[ℝ] ℝ)
    {ψ : ℝ → (Fin m → ℝ)} {p : Fin m → ℝ} {s : ℝ} (hsd : HasFDerivAt ψ (fderiv ℝ ψ s) s)
    (hℓ : ∀ᶠ t in nhds s, ℓ (ψ t - p) = t) :
    ℓ ((fderiv ℝ ψ s) 1) = 1 := by
  have h1 : HasDerivAt (fun t : ℝ => ℓ (ψ t - p)) (ℓ ((fderiv ℝ ψ s) 1)) s := by
    have ha : HasDerivAt (fun t : ℝ => ψ t - p) ((fderiv ℝ ψ s) 1) s :=
      hsd.hasDerivAt.sub_const p
    exact hasDerivAt_comp
      (ContinuousLinearMap.hasFDerivAt ℓ : HasFDerivAt ℓ ℓ (ψ s - p)) ha
  have h2 : HasDerivAt (fun t : ℝ => ℓ (ψ t - p)) 1 s := by
    have hid : HasDerivAt (fun t : ℝ => t) 1 s := by
      first
      | exact hasDerivAt_id' s
      | exact hasDerivAt_id s
    have heq : (fun t : ℝ => t) =ᶠ[nhds s] (fun t : ℝ => ℓ (ψ t - p)) :=
      hℓ.mono (fun t ht => ht.symm)
    first
    | exact hid.congr_of_eventuallyEq heq
    | exact hid.congr_of_eventuallyEq heq.symm
  exact h1.unique h2

theorem tangent_of_param_self {m : ℕ} (V : (Fin m → ℝ) → (Fin (m - 1) → ℝ))
    (X : (Fin m → ℝ) → (Fin m → ℝ)) (hV : ContDiff ℝ 1 V)
    (hgrad : ∀ z, V z = 0 → LinearIndependent ℝ (fun i => fderiv ℝ (fun w => V w i) z))
    (hX0 : ∀ z, V z = 0 → X z ≠ 0)
    (htan : ∀ z, V z = 0 → ∀ i, fderiv ℝ (fun w => V w i) z (X z) = 0)
    (p : Fin m → ℝ) (ℓ : (Fin m → ℝ) →L[ℝ] ℝ) (ψ : ℝ → (Fin m → ℝ))
    (hψdiff : ContDiffAt ℝ 1 ψ 0)
    (hψM : ∀ᶠ s : ℝ in nhds 0, V (ψ s) = 0)
    (hℓψ : ∀ᶠ s : ℝ in nhds 0, ℓ (ψ s - p) = s) :
    ∀ᶠ s : ℝ in nhds 0, X (ψ s) = fderiv ℝ ψ s (ℓ (X (ψ s))) := by
  have hψloc : ∀ᶠ s : ℝ in nhds 0, HasFDerivAt ψ (fderiv ℝ ψ s) s := by
    obtain ⟨u, hu, hucd⟩ := hψdiff.contDiffOn (m := 1) le_rfl (fun h => absurd h (by decide))
    obtain ⟨u', hu'sub, hu'open, h0u'⟩ := mem_nhds_iff.mp hu
    filter_upwards [hu'open.mem_nhds h0u'] with s hs
    exact (((hucd.mono hu'sub).differentiableOn_one).differentiableAt
      (hu'open.mem_nhds hs)).hasFDerivAt
  obtain ⟨δ₁, hδ₁, hδ₁P⟩ := exists_pos_abs_lt_of_eventually hψloc
  obtain ⟨δ₂, hδ₂, hδ₂P⟩ := exists_pos_abs_lt_of_eventually hψM
  obtain ⟨δ₃, hδ₃, hδ₃P⟩ := exists_pos_abs_lt_of_eventually hℓψ
  set δ : ℝ := min δ₁ (min δ₂ δ₃) / 2 with hδdef
  have hminpos : 0 < min δ₁ (min δ₂ δ₃) := lt_min hδ₁ (lt_min hδ₂ hδ₃)
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  have hlt₁ : δ < δ₁ := by rw [hδdef]; linarith [min_le_left δ₁ (min δ₂ δ₃)]
  have hlt₂ : δ < δ₂ := by
    rw [hδdef]; linarith [min_le_right δ₁ (min δ₂ δ₃), min_le_left δ₂ δ₃]
  have hlt₃ : δ < δ₃ := by
    rw [hδdef]; linarith [min_le_right δ₁ (min δ₂ δ₃), min_le_right δ₂ δ₃]
  have hball : ∀ t, |t| < δ → HasFDerivAt ψ (fderiv ℝ ψ t) t :=
    fun t ht => hδ₁P t (lt_trans ht hlt₁)
  have hballV : ∀ t, |t| < δ → V (ψ t) = 0 := fun t ht => hδ₂P t (lt_trans ht hlt₂)
  have hballℓ : ∀ t, |t| < δ → ℓ (ψ t - p) = t := fun t ht => hδ₃P t (lt_trans ht hlt₃)
  filter_upwards [isOpen_Ioo.mem_nhds
    (show (0:ℝ) ∈ Set.Ioo (-δ) δ from ⟨by linarith, hδpos⟩)] with s hs
  have hmem : s ∈ Set.Ioo (-δ) δ := hs
  have hlt : |s| < δ := by rw [abs_lt]; exact ⟨hmem.1, hmem.2⟩
  have hnb : ∀ᶠ t in nhds s, t ∈ Set.Ioo (-δ) δ := isOpen_Ioo.mem_nhds hmem
  have hsd : HasFDerivAt ψ (fderiv ℝ ψ s) s := hball s hlt
  have hVs : ∀ᶠ t in nhds s, V (ψ t) = 0 :=
    hnb.mono (fun t ht => hballV t (by rw [abs_lt]; exact ⟨ht.1, ht.2⟩))
  have hℓs : ∀ᶠ t in nhds s, ℓ (ψ t - p) = t :=
    hnb.mono (fun t ht => hballℓ t (by rw [abs_lt]; exact ⟨ht.1, ht.2⟩))
  have hψ's : (fderiv ℝ ψ s) 1 ≠ 0 := by
    have h := fderiv_apply_one_eq_one ℓ hsd hℓs
    intro h0
    rw [h0, map_zero] at h
    exact zero_ne_one h
  have htan_ψ' : (fderiv ℝ V (ψ s)) ((fderiv ℝ ψ s) 1) = 0 :=
    curve_fderiv_eq_zero V hV hsd hVs
  have htanX : (fderiv ℝ V (ψ s)) (X (ψ s)) = 0 := by
    rw [fderiv_eq_pi V hV (ψ s)]
    funext i
    simpa using htan (ψ s) (hballV s hlt) i
  have htop : (fderiv ℝ V (ψ s)).range = ⊤ :=
    fderiv_range_top V hV (ψ s) (hgrad (ψ s) (hballV s hlt))
  obtain ⟨c, hc⟩ := smul_eq_of_range_top (fderiv ℝ V (ψ s)) htop htan_ψ' htanX hψ's
  have hℓ1 : ℓ ((fderiv ℝ ψ s) 1) = 1 := fderiv_apply_one_eq_one ℓ hsd hℓs
  have hℓc : ℓ (X (ψ s)) = c := by
    rw [hc, map_smul, hℓ1, smul_eq_mul, mul_one]
  calc X (ψ s) = c • (fderiv ℝ ψ s) 1 := hc
    _ = ℓ (X (ψ s)) • (fderiv ℝ ψ s) 1 := by rw [hℓc]
    _ = fderiv ℝ ψ s (ℓ (X (ψ s))) := by
        rw [← ContinuousLinearMap.map_smul, smul_eq_mul, mul_one]

theorem exists_ift_param_self {m : ℕ} (V : (Fin m → ℝ) → (Fin (m - 1) → ℝ)) (hV : ContDiff ℝ 1 V)
    (hgrad : ∀ z, V z = 0 → LinearIndependent ℝ (fun i => fderiv ℝ (fun w => V w i) z))
    (p v : Fin m → ℝ) (hp : V p = 0) (hv : v ≠ 0) (hvker : fderiv ℝ V p v = 0) :
    ∃ (ℓ : (Fin m → ℝ) →L[ℝ] ℝ) (ψ : ℝ → (Fin m → ℝ)),
      ℓ v = 1 ∧ ψ 0 = p ∧ ContDiffAt ℝ 1 ψ 0 ∧
      (∀ᶠ s : ℝ in nhds 0, V (ψ s) = 0 ∧ ℓ (ψ s - p) = s) ∧
      (∀ᶠ x : Fin m → ℝ in nhds p, V x = 0 → ψ (ℓ (x - p)) = x) := by
  classical
  have hD : (fderiv ℝ V p).range = ⊤ := fderiv_range_top V hV p (hgrad p hp)
  obtain ⟨M, hM1, hM2⟩ := exists_linearEquiv_fst_eq_of_ker (fderiv ℝ V p) v hD hvker hv
  let MC : (ℝ × (Fin (m-1) → ℝ)) →L[ℝ] (Fin m → ℝ) :=
    (M : (ℝ × (Fin (m-1) → ℝ)) →L[ℝ] (Fin m → ℝ))
  let Msym : (Fin m → ℝ) →L[ℝ] (ℝ × (Fin (m-1) → ℝ)) :=
    (M.symm : (Fin m → ℝ) →L[ℝ] (ℝ × (Fin (m-1) → ℝ)))
  let u : ℝ × (Fin (m-1) → ℝ) := 0
  have hMu : M u = 0 := by simp [u]
  let F : ℝ × (Fin (m-1) → ℝ) → (Fin (m-1) → ℝ) := fun q => V (p + M q)
  have hFu : F u = 0 := by simp [F, hMu, hp]
  -- derivative of F
  have hderiv : fderiv ℝ F u = (fderiv ℝ V p) ∘L MC := by
    have h2 : HasFDerivAt (fun q : ℝ × (Fin (m-1) → ℝ) => p + M q) MC u := by
      have h3 : HasFDerivAt (fun q : ℝ × (Fin (m-1) → ℝ) => M q) MC u := by
        first
        | exact ContinuousLinearMap.hasFDerivAt MC
        | simpa only [MC] using (ContinuousLinearMap.hasFDerivAt MC : HasFDerivAt MC MC u)
      simpa using h3.const_add p
    have h4 : HasFDerivAt V (fderiv ℝ V p) (p + M u) := by
      rw [hMu, add_zero]
      exact (hV.contDiffAt.hasStrictFDerivAt (by norm_num : (1:ℕ∞ω) ≠ 0)).hasFDerivAt
    have h5 : HasFDerivAt F ((fderiv ℝ V p) ∘L MC) u := by
      have h6 : HasFDerivAt (V ∘ fun q : ℝ × (Fin (m-1) → ℝ) => p + M q)
          ((fderiv ℝ V p) ∘L MC) u := by
        first
        | exact h4.comp (x := u) h2
        | exact h4.comp u h2
        | exact h4.comp h2
      simpa [F, Function.comp_def] using h6
    exact h5.fderiv
  -- C^1 of F at u
  have hFdiff : ContDiffAt ℝ 1 F u := by
    have h3 : ContDiffAt ℝ 1 (fun q : ℝ × (Fin (m-1) → ℝ) => p + M q) u := by
      have h4 : ContDiff ℝ 1 (fun q : ℝ × (Fin (m-1) → ℝ) => M q) := MC.contDiff
      have h5 : ContDiffAt ℝ 1 (fun q : ℝ × (Fin (m-1) → ℝ) => M q) u := h4.contDiffAt
      exact (contDiffAt_const (c := p)).add h5
    exact hV.contDiffAt.comp u h3
  -- the second partial derivative is the identity
  have hcomp : fderiv ℝ F u ∘L ContinuousLinearMap.inr ℝ ℝ (Fin (m-1) → ℝ)
      = ContinuousLinearMap.id ℝ (Fin (m-1) → ℝ) := by
    refine ContinuousLinearMap.ext (fun y => ?_)
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, hderiv,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
    exact hM2 y
  have hif : (fderiv ℝ F u ∘L ContinuousLinearMap.inr ℝ ℝ (Fin (m-1) → ℝ)).IsInvertible := by
    rw [hcomp]
    exact ⟨ContinuousLinearEquiv.refl ℝ (Fin (m-1) → ℝ), rfl⟩
  have hn : (1 : ℕ∞ω) ≠ 0 := by simp
  let φ : ℝ → (Fin (m-1) → ℝ) := hFdiff.implicitFunction hn hif
  have hφ0 : φ 0 = 0 := hFdiff.implicitFunction_apply_self hn hif
  have hφcd : ContDiffAt ℝ 1 φ 0 := hFdiff.contDiffAt_implicitFunction hn hif
  have hI1 : ∀ᶠ a : ℝ in nhds 0, F (a, φ a) = F u :=
    hFdiff.eventually_apply_implicitFunction hn hif
  have hI2 : ∀ᶠ q : ℝ × (Fin (m-1) → ℝ) in nhds u, (F q = F u ↔ φ q.1 = q.2) :=
    hFdiff.eventually_apply_eq_iff_implicitFunction hn hif
  -- final objects
  let ℓ : (Fin m → ℝ) →L[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ (Fin (m-1) → ℝ)) ∘L Msym
  let Ψ : ℝ → (Fin m → ℝ) := fun a => p + M (a, φ a)
  have hℓM : ∀ x : ℝ × (Fin (m-1) → ℝ), ℓ (M x) = x.1 := by
    intro x
    change (ContinuousLinearMap.fst ℝ ℝ (Fin (m-1) → ℝ)) (Msym (M x)) = x.1
    rw [show Msym (M x) = x from M.symm_apply_apply x]
    rfl
  have hℓv : ℓ v = 1 := by
    rw [← hM1, hℓM (1, 0)]
  refine ⟨ℓ, Ψ, hℓv, ?_, ?_, ?_, ?_⟩
  · simp [Ψ, hφ0]
  · have hpcd : ContDiffAt ℝ 1 (fun a : ℝ => (a, φ a)) 0 :=
      ContDiffAt.prodMk contDiffAt_id hφcd
    have h3 : ContDiffAt ℝ 1 (fun q : ℝ × (Fin (m-1) → ℝ) => M q) (0, φ 0) :=
      MC.contDiff.contDiffAt
    have h4 : ContDiffAt ℝ 1 (fun a : ℝ => M (a, φ a)) 0 := h3.comp 0 hpcd
    have h5 : ContDiffAt ℝ 1 (fun a : ℝ => p + M (a, φ a)) 0 :=
      (contDiffAt_const (c := p)).add h4
    simpa [Ψ] using h5
  · filter_upwards [hI1] with a ha
    constructor
    · show V (Ψ a) = 0
      rw [show V (Ψ a) = F (a, φ a) from rfl, ha, hFu]
    · have hΨa : Ψ a - p = M (a, φ a) := by simp only [Ψ]; abel
      rw [hΨa, hℓM (a, φ a)]
  · have htend : Tendsto (fun x : Fin m → ℝ => M.symm (x - p)) (nhds p) (nhds u) := by
      have h1 : Tendsto (fun x : Fin m → ℝ => x - p) (nhds p) (nhds (0:Fin m → ℝ)) := by
        have hc : Continuous (fun x : Fin m → ℝ => x - p) :=
          continuous_id.sub (continuous_const : Continuous (fun _ : Fin m → ℝ => p))
        simpa using hc.tendsto p
      have h2 : Tendsto Msym (nhds (0:Fin m → ℝ)) (nhds (Msym 0)) := Msym.continuous.continuousAt
      have h3 := h2.comp h1
      have hu0 : Msym (0 : Fin m → ℝ) = u := by simp [u]
      rwa [hu0] at h3
    filter_upwards [htend.eventually hI2] with x hx hxV
    set q : ℝ × (Fin (m-1) → ℝ) := M.symm (x - p) with hq
    have hMq : M q = x - p := by rw [hq]; exact M.apply_symm_apply (x - p)
    have hFq : F q = F u := by
      have h1 : F q = V x := by
        simp only [F]
        rw [hMq]
        congr 1
        abel
      rw [h1, hxV, hFu]
    have hφq : φ q.1 = q.2 := hx.mp hFq
    have hxq : x = p + M q := by rw [hMq]; abel
    have hℓx : ℓ (x - p) = q.1 := by
      have h2 : Msym (x - p) = q := by rw [hq]; rfl
      change (ContinuousLinearMap.fst ℝ ℝ (Fin (m-1) → ℝ)) (Msym (x - p)) = q.1
      rw [h2]
      rfl
    have hΨ : Ψ (ℓ (x - p)) = p + M q := by
      rw [hℓx]
      simp only [Ψ]
      rw [hφq]
    rw [hΨ, hxq]



lemma eq_zero_of_eventually_hasDerivAt_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {z z' : ℝ → E} {C : ℝ} (hz0 : z 0 = 0)
    (hdiff : ∀ᶠ t in nhds (0:ℝ), HasDerivAt z (z' t) t)
    (hbound : ∀ᶠ t in nhds (0:ℝ), ‖z' t‖ ≤ C * ‖z t‖) :
    ∀ᶠ t in nhds (0:ℝ), z t = 0 := by
  obtain ⟨δ, hδ, hδP⟩ := exists_pos_abs_lt_of_eventually hdiff
  obtain ⟨δ', hδ', hδ'P⟩ := exists_pos_abs_lt_of_eventually hbound
  have hmin : 0 < min δ δ' := lt_min hδ hδ'
  have hlt1 : min δ δ' / 2 < δ := by linarith [min_le_left δ δ']
  have hlt2 : min δ δ' / 2 < δ' := by linarith [min_le_right δ δ']
  have hr0 : (0:ℝ) < min δ δ' / 2 := by linarith
  have key : ∀ (w w' : ℝ → E), w 0 = 0 →
      (∀ t, |t| ≤ min δ δ' / 2 → HasDerivAt w (w' t) t) →
      (∀ t, |t| ≤ min δ δ' / 2 → ‖w' t‖ ≤ C * ‖w t‖) →
      ∀ t ∈ Set.Icc (0:ℝ) (min δ δ' / 2), w t = 0 := by
    intro w w' hw0 hwd hwb
    apply eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    · apply DifferentiableOn.continuousOn (𝕜 := ℝ)
      intro t ht
      have h1 : |t| ≤ min δ δ' / 2 := by rw [abs_of_nonneg ht.1]; exact ht.2
      exact ((hwd t h1).differentiableAt).differentiableWithinAt
    · intro t ht
      have h1 : |t| ≤ min δ δ' / 2 := by rw [abs_of_nonneg ht.1]; exact le_of_lt ht.2
      exact (hwd t h1).hasDerivWithinAt
    · simpa using hw0
    · intro t ht
      have h1 : |t| ≤ min δ δ' / 2 := by rw [abs_of_nonneg ht.1]; exact le_of_lt ht.2
      exact hwb t h1
  have hfwd : ∀ t ∈ Set.Icc (0:ℝ) (min δ δ' / 2), z t = 0 :=
    key z z' hz0 (fun t ht => hδP t (lt_of_le_of_lt ht hlt1))
      (fun t ht => hδ'P t (lt_of_le_of_lt ht hlt2))
  have hbwd : ∀ t ∈ Set.Icc (-(min δ δ' / 2)) 0, z t = 0 := by
    intro t ht
    have hneg := key (z ∘ Neg.neg) (fun u : ℝ => -z' (-u))
      (by simp [Function.comp_apply, hz0])
      (fun u hu => by
        have h1 : |(-u)| ≤ min δ δ' / 2 := by rw [abs_neg]; exact hu
        simpa using hasDerivAt_comp (hδP (-u) (lt_of_le_of_lt h1 hlt1)) (hasDerivAt_neg' u))
      (fun u hu => by
        have h1 : |(-u)| ≤ min δ δ' / 2 := by rw [abs_neg]; exact hu
        have h2 := hδ'P (-u) (lt_of_le_of_lt h1 hlt2)
        simpa [Function.comp_apply, norm_neg] using h2)
    have ht' : -t ∈ Set.Icc (0:ℝ) (min δ δ' / 2) := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    simpa [Function.comp_apply] using hneg (-t) ht'
  rw [Filter.eventually_iff_exists_mem]
  refine ⟨Set.Ioo (-(min δ δ' / 2)) (min δ δ' / 2),
    isOpen_Ioo.mem_nhds ⟨by linarith, hr0⟩, ?_⟩
  intro t ht
  rcases le_total t 0 with h | h
  · exact hbwd t ⟨le_of_lt ht.1, h⟩
  · exact hfwd t ⟨h, le_of_lt ht.2⟩

/-- If all component derivatives of `V` vanish on `w`, then `fderiv ℝ V z w = 0`. -/
lemma fderiv_eq_zero_of_components {m : ℕ} (V : (Fin m → ℝ) → (Fin (m - 1) → ℝ)) (hV : ContDiff ℝ 1 V)
    (z w : Fin m → ℝ) (h : ∀ i, fderiv ℝ (fun y => V y i) z w = 0) :
    fderiv ℝ V z w = 0 := by
  have hcomp : ∀ i : Fin (m - 1),
      HasStrictFDerivAt (fun y => V y i) (fderiv ℝ (fun y => V y i) z) z :=
    fun i => (contDiffAt_pi.mp hV.contDiffAt i).hasStrictFDerivAt (by norm_num)
  have hst : HasStrictFDerivAt V (fderiv ℝ V z) z := hV.contDiffAt.hasStrictFDerivAt (by norm_num)
  have hpi : (fderiv ℝ V z) = ContinuousLinearMap.pi (fun i => fderiv ℝ (fun y => V y i) z) := by
    have h' := hasStrictFDerivAt_pi.mpr hcomp
    exact hst.hasFDerivAt.unique h'.hasFDerivAt
  rw [hpi]
  funext i
  simpa using h i

theorem local_orbit_covers_eps {m : ℕ} (V : (Fin m → ℝ) → (Fin (m - 1) → ℝ)) (X : (Fin m → ℝ) → (Fin m → ℝ)) (hV : ContDiff ℝ 1 V) (hX : ContDiff ℝ 1 X) (hgrad : ∀ z, V z = 0 → LinearIndependent ℝ (fun i => fderiv ℝ (fun w => V w i) z)) (hX0 : ∀ z, V z = 0 → X z ≠ 0) (htan : ∀ z, V z = 0 → ∀ i, fderiv ℝ (fun w => V w i) z (X z) = 0) : ∀ p, V p = 0 → ∃ (U : Set (Fin m → ℝ)) (ε : ℝ), IsOpen U ∧ p ∈ U ∧ 0 < ε ∧ ∀ γ : ℝ → Fin m → ℝ, γ 0 = p → (∀ t, HasDerivAt γ (X (γ t)) t) → U ∩ {z | V z = 0} ⊆ γ '' Set.Ioo (-ε) ε := by
  intro p hp
  by_cases hsol : ∃ γ : ℝ → Fin m → ℝ, γ 0 = p ∧ (∀ t, HasDerivAt γ (X (γ t)) t)
  · obtain ⟨γ₀, hγ₀0, hγ₀d⟩ := hsol
    have hv : X p ≠ 0 := hX0 p hp
    have hvker : fderiv ℝ V p (X p) = 0 := fderiv_eq_zero_of_components V hV p (X p) (htan p hp)
    obtain ⟨ℓ, ψ, hℓv, hψ0, hψdiff, hψM, hgraph⟩ :=
      exists_ift_param_self V hV hgrad p (X p) hp hv hvker
    have htang : ∀ᶠ s : ℝ in nhds 0, X (ψ s) = fderiv ℝ ψ s (ℓ (X (ψ s))) :=
      tangent_of_param_self V X hV hgrad hX0 htan p ℓ ψ hψdiff
        (hψM.mono fun s hs => hs.1) (hψM.mono fun s hs => hs.2)
    -- ### the flow parameter s
    set s : ℝ → ℝ := fun t => ℓ (γ₀ t - p) with hsdef
    have hs0 : s 0 = 0 := by simp [hsdef, hγ₀0]
    have hsd : ∀ t, HasDerivAt s (ℓ (X (γ₀ t))) t := by
      intro t
      have h1 : HasDerivAt (fun u : ℝ => ℓ (γ₀ u) - ℓ p) (ℓ (X (γ₀ t))) t :=
        (hasDerivAt_comp (ContinuousLinearMap.hasFDerivAt ℓ : HasFDerivAt ℓ ℓ (γ₀ t))
          (hγ₀d t)).sub_const (ℓ p)
      simpa [hsdef, map_sub] using h1
    have hs_tend : Tendsto s (nhds (0:ℝ)) (nhds 0) := by
      have h : Tendsto s (nhds (0:ℝ)) (nhds (s 0)) := (hsd 0).continuousAt
      rwa [hs0] at h
    have hs_cont : Continuous s := continuous_iff_continuousAt.mpr (fun t => (hsd t).continuousAt)
    -- ### ψ is differentiable near 0
    obtain ⟨u, hu, hucd⟩ := hψdiff.contDiffOn (m := 1) le_rfl (fun h => absurd h (by decide))
    obtain ⟨u', hu'sub, hu'open, h0u'⟩ := mem_nhds_iff.mp hu
    have hψloc : ∀ᶠ r : ℝ in nhds 0, DifferentiableAt ℝ ψ r :=
      Filter.mem_of_superset (hu'open.mem_nhds h0u') (fun r hr =>
        ((hucd.mono hu'sub).differentiableOn_one).differentiableAt (hu'open.mem_nhds hr))
    -- ### bound on ‖fderiv ψ‖ near 0
    set M : ℝ := ‖fderiv ℝ ψ 0‖ + 1 with hMdef
    have hbddψ : ∀ᶠ r : ℝ in nhds 0, ‖fderiv ℝ ψ r‖ ≤ M := by
      have h1 : ∀ᶠ r in nhds (0:ℝ), dist (fderiv ℝ ψ r) (fderiv ℝ ψ 0) < 1 :=
        (hψdiff.continuousAt_fderiv one_ne_zero).eventually
          (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self one_pos))
      filter_upwards [h1] with r hr
      have h2 : ‖fderiv ℝ ψ r - fderiv ℝ ψ 0‖ < 1 := by rwa [dist_eq_norm] at hr
      have h3 : ‖fderiv ℝ ψ r‖ ≤ ‖fderiv ℝ ψ 0‖ + ‖fderiv ℝ ψ r - fderiv ℝ ψ 0‖ := by
        calc ‖fderiv ℝ ψ r‖ = ‖fderiv ℝ ψ 0 + (fderiv ℝ ψ r - fderiv ℝ ψ 0)‖ := by
              congr 1; abel
          _ ≤ ‖fderiv ℝ ψ 0‖ + ‖fderiv ℝ ψ r - fderiv ℝ ψ 0‖ := norm_add_le _ _
      rw [hMdef]; linarith
    -- ### the derivative of z and its bound
    have hzderiv : ∀ᶠ t : ℝ in nhds 0,
        HasDerivAt (fun u : ℝ => γ₀ u - ψ (s u))
          (X (γ₀ t) - fderiv ℝ ψ (s t) (ℓ (X (γ₀ t)))) t := by
      filter_upwards [hs_tend.eventually hψloc] with t ht
      exact (hγ₀d t).sub (hasDerivAt_comp ht.hasFDerivAt (hsd t))
    have hz0 : (fun u : ℝ => γ₀ u - ψ (s u)) 0 = 0 := by simp [hsdef, hγ₀0, hψ0]
    -- Lipschitz data for X
    obtain ⟨K, W, hWmem, hKW⟩ := hX.locallyLipschitz p
    set C : ℝ := (K:ℝ) * (1 + M * ‖ℓ‖) with hCdef
    have hγW : ∀ᶠ t : ℝ in nhds 0, γ₀ t ∈ W := by
      have h : Tendsto γ₀ (nhds (0:ℝ)) (nhds (γ₀ 0)) := (hγ₀d 0).continuousAt
      have h2 : Tendsto γ₀ (nhds (0:ℝ)) (nhds p) := by rwa [hγ₀0] at h
      exact h2.eventually hWmem
    have hψW : ∀ᶠ t : ℝ in nhds 0, ψ (s t) ∈ W := by
      have h : Tendsto ψ (nhds (0:ℝ)) (nhds (ψ 0)) := hψdiff.continuousAt
      have h2 : Tendsto (fun t => ψ (s t)) (nhds (0:ℝ)) (nhds p) := by
        have h3 := h.comp hs_tend
        rwa [hψ0] at h3
      exact h2.eventually hWmem
    have hzbound : ∀ᶠ t : ℝ in nhds 0,
        ‖X (γ₀ t) - fderiv ℝ ψ (s t) (ℓ (X (γ₀ t)))‖ ≤ C * ‖γ₀ t - ψ (s t)‖ := by
      filter_upwards [hs_tend.eventually htang, hs_tend.eventually hbddψ, hγW, hψW]
        with t htan_t hMbdd hγtW hψtW
      have hkey : X (γ₀ t) - fderiv ℝ ψ (s t) (ℓ (X (γ₀ t)))
          = (X (γ₀ t) - X (ψ (s t)))
            - fderiv ℝ ψ (s t) (ℓ (X (γ₀ t) - X (ψ (s t)))) := by
        simp only [map_sub]
        rw [← htan_t]
        abel
      have hMnn : (0:ℝ) ≤ M := by rw [hMdef]; positivity
      have h1 : ‖X (γ₀ t) - X (ψ (s t))‖ ≤ (K:ℝ) * ‖γ₀ t - ψ (s t)‖ := by
        have h := hKW.dist_le_mul (γ₀ t) hγtW (ψ (s t)) hψtW
        simpa [dist_eq_norm] using h
      have hB : ‖ℓ (X (γ₀ t) - X (ψ (s t)))‖ ≤ ‖ℓ‖ * ‖X (γ₀ t) - X (ψ (s t))‖ :=
        ContinuousLinearMap.le_opNorm ℓ _
      have hD : ‖fderiv ℝ ψ (s t) (ℓ (X (γ₀ t) - X (ψ (s t))))‖
          ≤ M * ‖ℓ (X (γ₀ t) - X (ψ (s t)))‖ :=
        le_trans (ContinuousLinearMap.le_opNorm _ _)
          (mul_le_mul_of_nonneg_right hMbdd (norm_nonneg _))
      have hE : M * ‖ℓ (X (γ₀ t) - X (ψ (s t)))‖
          ≤ M * (‖ℓ‖ * ‖X (γ₀ t) - X (ψ (s t))‖) :=
        mul_le_mul_of_nonneg_left hB hMnn
      have hF : M * (‖ℓ‖ * ‖X (γ₀ t) - X (ψ (s t))‖)
          ≤ M * (‖ℓ‖ * ((K:ℝ) * ‖γ₀ t - ψ (s t)‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)) hMnn
      have hG : ‖(X (γ₀ t) - X (ψ (s t)))
            - fderiv ℝ ψ (s t) (ℓ (X (γ₀ t) - X (ψ (s t))))‖
          ≤ (K:ℝ) * ‖γ₀ t - ψ (s t)‖ + M * (‖ℓ‖ * ((K:ℝ) * ‖γ₀ t - ψ (s t)‖)) :=
        calc ‖(X (γ₀ t) - X (ψ (s t)))
              - fderiv ℝ ψ (s t) (ℓ (X (γ₀ t) - X (ψ (s t))))‖
            ≤ ‖X (γ₀ t) - X (ψ (s t))‖
              + ‖fderiv ℝ ψ (s t) (ℓ (X (γ₀ t) - X (ψ (s t))))‖ := norm_sub_le _ _
          _ ≤ (K:ℝ) * ‖γ₀ t - ψ (s t)‖ + M * (‖ℓ‖ * ((K:ℝ) * ‖γ₀ t - ψ (s t)‖)) :=
              add_le_add h1 (le_trans hD (le_trans hE hF))
      rw [hkey]
      calc ‖(X (γ₀ t) - X (ψ (s t)))
            - fderiv ℝ ψ (s t) (ℓ (X (γ₀ t) - X (ψ (s t))))‖
          ≤ (K:ℝ) * ‖γ₀ t - ψ (s t)‖ + M * (‖ℓ‖ * ((K:ℝ) * ‖γ₀ t - ψ (s t)‖)) := hG
        _ = C * ‖γ₀ t - ψ (s t)‖ := by rw [hCdef]; ring
    have hzfinal := eq_zero_of_eventually_hasDerivAt_bound hz0 hzderiv hzbound
    obtain ⟨r₁, hr₁, hr₁P⟩ :=
      exists_pos_abs_lt_of_eventually (hzfinal.mono fun t ht => sub_eq_zero.mp ht)
    -- ### |s t - t| ≤ |t|/2 near 0
    have hs0' : HasDerivAt s 1 0 := by
      have h := hsd 0
      rwa [hγ₀0, hℓv] at h
    have hsbound : ∀ᶠ t : ℝ in nhds 0, |s t - t| ≤ (1/2) * |t| := by
      have hlit0 := (hasDerivAt_iff_isLittleO_nhds_zero.mp hs0')
      have hlit : (fun h : ℝ => s h - h) =o[nhds (0:ℝ)] (fun h : ℝ => h) := by
        simpa [hs0] using hlit0
      filter_upwards [hlit.def (by norm_num : (0:ℝ) < 1/2)] with t ht
      simpa using ht
    obtain ⟨r₂, hr₂, hr₂P⟩ := exists_pos_abs_lt_of_eventually hsbound
    -- ### the open set and the final covering
    obtain ⟨O, hO_mem, hO⟩ := hgraph.exists_mem
    obtain ⟨O', hO'sub, hO'open, hpO'⟩ := mem_nhds_iff.mp hO_mem
    set r : ℝ := min r₁ r₂ with hrdef
    have hrpos : 0 < r := by rw [hrdef]; exact lt_min hr₁ hr₂
    have hrle1 : r ≤ r₁ := by rw [hrdef]; exact min_le_left _ _
    have hrle2 : r ≤ r₂ := by rw [hrdef]; exact min_le_right _ _
    refine ⟨{x : Fin m → ℝ | x ∈ O' ∧ ℓ (x - p) ∈ Set.Ioo (-(r / 4)) (r / 4)}, r,
      ?_, ?_, hrpos, ?_⟩
    · have hcont : Continuous (fun x : Fin m → ℝ => ℓ (x - p)) := by fun_prop
      exact hO'open.inter (isOpen_Ioo.preimage hcont)
    · refine ⟨hpO', ?_⟩
      have : ℓ (p - p) = 0 := by simp
      rw [this]
      exact ⟨by linarith, by linarith⟩
    · intro γ hγ0 hγd
      have hγeq : γ = γ₀ := integral_curve_unique_global X hX hγd hγ₀d (by rw [hγ0, hγ₀0])
      rw [hγeq]
      rintro y ⟨hyU, hyM⟩
      obtain ⟨hyO', hyℓ⟩ := hyU
      have hψy : ψ (ℓ (y - p)) = y := hO y (hO'sub hyO') hyM
      have hsa : s (-(r/2)) ≤ -(r/4) := by
        have habs : |-(r/2)| < r₂ := by
          rw [abs_neg, abs_of_nonneg (by linarith [hrpos] : (0:ℝ) ≤ r/2)]
          linarith [hrpos, hrle2]
        have h := hr₂P (-(r/2)) habs
        have hR : |-(r/2)| = r/2 := by
          rw [abs_neg]; exact abs_of_nonneg (by linarith [hrpos] : (0:ℝ) ≤ r/2)
        rw [hR] at h
        have h2 : s (-(r/2)) - (-(r/2)) ≤ (1/2) * (r/2) := (abs_le.mp h).2
        linarith
      have hsb : r/4 ≤ s (r/2) := by
        have habs : |r/2| < r₂ := by
          rw [abs_of_nonneg (by linarith [hrpos] : (0:ℝ) ≤ r/2)]
          linarith [hrpos, hrle2]
        have h := hr₂P (r/2) habs
        have hR : |r/2| = r/2 := abs_of_nonneg (by linarith [hrpos] : (0:ℝ) ≤ r/2)
        rw [hR] at h
        have h2 : -((1/2) * (r/2)) ≤ s (r/2) - r/2 := (abs_le.mp h).1
        linarith
      have hyIcc : ℓ (y - p) ∈ Set.Icc (s (-(r/2))) (s (r/2)) :=
        ⟨by linarith [hsa, hyℓ.1], by linarith [hsb, hyℓ.2]⟩
      obtain ⟨t, htIcc, hst⟩ := intermediate_value_Icc (by linarith [hrpos] : -(r/2) ≤ r/2)
        hs_cont.continuousOn hyIcc
      refine ⟨t, ?_, ?_⟩
      · exact Set.mem_Ioo.mpr ⟨by linarith [htIcc.1, hrpos], by linarith [htIcc.2, hrpos]⟩
      · have htlt : |t| < r₁ := by
          rw [abs_lt]
          exact ⟨by linarith [htIcc.1, hrpos], by linarith [htIcc.2, hrpos, hrle1]⟩
        rw [hr₁P t htlt, hst, hψy]
  · refine ⟨Set.univ, 1, isOpen_univ, trivial, one_pos, ?_⟩
    intro γ hγ0 hγd
    exact absurd ⟨γ, hγ0, hγd⟩ hsol





end Work.WilE2
