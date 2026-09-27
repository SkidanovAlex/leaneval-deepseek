import Mathlib
import Submission.Work.Drive.Interfaces
import Submission.Work.Drive.boxParity
import Submission.Work.Sard.submersion_local_form
import Submission.Work.Sard.weak_interior_empty_open_prod

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


set_option maxHeartbeats 4000000

namespace Work.MetricSquare

open scoped ContDiff Topology
open Set Filter

noncomputable section

/-- The parameter space `ℝ^m`. -/
abbrev Pm (m : ℕ) : Type := EuclideanSpace ℝ (Fin m)
/-- The coordinate space `Amb 6 = ℝ^7`. -/
abbrev Cz : Type := EuclideanSpace ℝ (Fin 7)
/-- The target `Tgt 6 = ℝ^6`. -/
abbrev Tw : Type := EuclideanSpace ℝ (Fin 6)
/-- The `(m+1)`-dimensional space used for the chart. -/
abbrev Qm (m : ℕ) : Type := Fin (m+1) → ℝ

/-! ## Derivative identities for a map on a product -/

lemma fd_comp_inl {E Z W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (Φ : E × Z → W) (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ) (p : E) (z : Z) :
    (fderiv ℝ Φ (p, z)).comp (ContinuousLinearMap.inl ℝ E Z)
      = fderiv ℝ (fun p' : E => Φ (p', z)) p := by
  have hd : DifferentiableAt ℝ Φ (p, z) := (hΦ.differentiable (by simp)).differentiableAt
  have h2 : HasFDerivAt (fun p' : E => Φ (p', z))
      ((fderiv ℝ Φ (p, z)).comp (ContinuousLinearMap.inl ℝ E Z)) p := by
    have hin : HasFDerivAt (fun p' : E => (p', z)) (ContinuousLinearMap.inl ℝ E Z) p := by
      simpa using (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.inl ℝ E Z)).add_const (0, z)
    exact hd.hasFDerivAt.comp p hin
  exact h2.fderiv.symm

lemma fd_comp_inr {E Z W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (Φ : E × Z → W) (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ) (p : E) (z : Z) :
    (fderiv ℝ Φ (p, z)).comp (ContinuousLinearMap.inr ℝ E Z)
      = fderiv ℝ (fun z' : Z => Φ (p, z')) z := by
  have hd : DifferentiableAt ℝ Φ (p, z) := (hΦ.differentiable (by simp)).differentiableAt
  have h2 : HasFDerivAt (fun z' : Z => Φ (p, z'))
      ((fderiv ℝ Φ (p, z)).comp (ContinuousLinearMap.inr ℝ E Z)) z := by
    have hin : HasFDerivAt (fun z' : Z => (p, z')) (ContinuousLinearMap.inr ℝ E Z) z := by
      simpa using (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.inr ℝ E Z)).const_add (p, 0)
    exact hd.hasFDerivAt.comp z hin
  exact h2.fderiv.symm

/-- The full derivative at `(p,z)` applied to `(v,u)` splits as the sum of the two partial
derivatives. -/
lemma fderiv_apply_prod {E Z W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (Φ : E × Z → W) (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ) (p : E) (z : Z)
    (v : E) (u : Z) :
    (fderiv ℝ Φ (p, z)) (v, u)
      = (fderiv ℝ (fun p' : E => Φ (p', z)) p) v
        + (fderiv ℝ (fun z' : Z => Φ (p, z')) z) u := by
  have hsplit : (v, u) = (ContinuousLinearMap.inl ℝ E Z v) + (ContinuousLinearMap.inr ℝ E Z u) := by
    rw [ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply]
    simp
  rw [hsplit, map_add]
  congr 1
  · rw [show (fderiv ℝ Φ (p, z)) ((ContinuousLinearMap.inl ℝ E Z) v)
        = ((fderiv ℝ Φ (p, z)).comp (ContinuousLinearMap.inl ℝ E Z)) v from rfl,
      fd_comp_inl Φ hΦ p z]
  · rw [show (fderiv ℝ Φ (p, z)) ((ContinuousLinearMap.inr ℝ E Z) u)
        = ((fderiv ℝ Φ (p, z)).comp (ContinuousLinearMap.inr ℝ E Z)) u from rfl,
      fd_comp_inr Φ hΦ p z]

/-- If the partial derivative in the first variable is surjective, then the set of first coordinates
of the kernel of the full derivative is everything, exactly when the partial derivative in the second
variable is surjective. -/
lemma fst_image_ker_eq_univ_iff {E Z W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (Φ : E × Z → W) (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ) (x : E × Z)
    (hDp : Function.Surjective (fderiv ℝ (fun p' : E => Φ (p', x.2)) x.1)) :
    (ContinuousLinearMap.fst ℝ E Z) '' ((fderiv ℝ Φ x).ker : Set (E × Z)) = Set.univ
      ↔ Function.Surjective (fderiv ℝ (fun z' : Z => Φ (x.1, z')) x.2) := by
  constructor
  · intro hker w0
    obtain ⟨v, hv⟩ := hDp w0
    have hvmem : v ∈ (ContinuousLinearMap.fst ℝ E Z) '' ((fderiv ℝ Φ x).ker : Set (E × Z)) := by
      rw [hker]; exact Set.mem_univ v
    obtain ⟨y, hy, hyv⟩ := hvmem
    have hy0 : (fderiv ℝ Φ x) y = 0 := hy
    have hy1 : y.1 = v := hyv
    have hy_eq : y = (v, y.2) := Prod.ext hy1 rfl
    have hzero : (fderiv ℝ Φ x) (v, y.2) = 0 := by rw [← hy_eq]; exact hy0
    have hzero' : (fderiv ℝ (fun p' : E => Φ (p', x.2)) x.1) v
        + (fderiv ℝ (fun z' : Z => Φ (x.1, z')) x.2) y.2 = 0 := by
      rw [← fderiv_apply_prod Φ hΦ x.1 x.2 v y.2]
      exact hzero
    have hb : (fderiv ℝ (fun z' : Z => Φ (x.1, z')) x.2) y.2
        = -(fderiv ℝ (fun p' : E => Φ (p', x.2)) x.1) v := by
      have h1 := eq_neg_of_add_eq_zero_left hzero'
      rw [h1, neg_neg]
    refine ⟨-y.2, ?_⟩
    rw [map_neg, hb, neg_neg, hv]
  · intro hDz
    rw [Set.eq_univ_iff_forall]
    intro v
    obtain ⟨u, hu⟩ := hDz (-((fderiv ℝ (fun p' : E => Φ (p', x.2)) x.1) v))
    refine ⟨(v, u), ?_, rfl⟩
    show (fderiv ℝ Φ (x.1, x.2)) (v, u) = 0
    rw [fderiv_apply_prod Φ hΦ x.1 x.2 v u, hu]
    abel

/-! ## The parametrisation chart -/

/-- Differentiating `Φ (e y) = y.1` along the chart gives `DΦ (e y) ∘ De y = fst`. -/
lemma chart_comp_fst (m : ℕ) (Φ : Pm m × Cz → Tw)
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (e : OpenPartialHomeomorph (Tw × Qm m) (Pm m × Cz))
    (he_smooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (e : Tw × Qm m → Pm m × Cz) e.source)
    (he_Phi : ∀ y ∈ e.source, Φ (e y) = y.1)
    (w : Qm m) (hw : ((0 : Tw), w) ∈ e.source) :
    (fderiv ℝ Φ (e ((0 : Tw), w))).comp
        (fderiv ℝ (e : Tw × Qm m → Pm m × Cz) ((0 : Tw), w))
      = ContinuousLinearMap.fst ℝ Tw (Qm m) := by
  have hsource_open : IsOpen e.source := e.open_source
  have hfd_e : HasFDerivAt (e : Tw × Qm m → Pm m × Cz)
      (fderiv ℝ (e : Tw × Qm m → Pm m × Cz) ((0 : Tw), w)) ((0 : Tw), w) :=
    ((he_smooth.contDiffAt (hsource_open.mem_nhds hw)).differentiableAt (by simp)).hasFDerivAt
  have hfd_Phi : HasFDerivAt Φ (fderiv ℝ Φ (e ((0 : Tw), w))) (e ((0 : Tw), w)) :=
    (hΦ.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hcomp := hfd_Phi.comp ((0 : Tw), w) hfd_e
  have heq : (fun y : Tw × Qm m => Φ (e y)) =ᶠ[𝓝 ((0 : Tw), w)] (fun y => y.1) := by
    filter_upwards [hsource_open.mem_nhds hw] with y hy using he_Phi y hy
  have hfd_fst : HasFDerivAt (fun y : Tw × Qm m => y.1)
      (ContinuousLinearMap.fst ℝ Tw (Qm m)) ((0 : Tw), w) := hasFDerivAt_fst
  have h1 : fderiv ℝ (fun y : Tw × Qm m => Φ (e y)) ((0 : Tw), w)
      = ContinuousLinearMap.fst ℝ Tw (Qm m) := by
    rw [heq.fderiv_eq, hfd_fst.fderiv]
  have h2 : fderiv ℝ (fun y : Tw × Qm m => Φ (e y)) ((0 : Tw), w)
      = (fderiv ℝ Φ (e ((0 : Tw), w))).comp
          (fderiv ℝ (e : Tw × Qm m → Pm m × Cz) ((0 : Tw), w)) := hcomp.fderiv
  rw [← h2, h1]

/-- The range of `De 0 ∘ inr` is the kernel of `DΦ (e 0)`. -/
lemma chart_range (m : ℕ) (Φ : Pm m × Cz → Tw)
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (e : OpenPartialHomeomorph (Tw × Qm m) (Pm m × Cz))
    (he_smooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (e : Tw × Qm m → Pm m × Cz) e.source)
    (he_Phi : ∀ y ∈ e.source, Φ (e y) = y.1)
    (he_deriv : ∀ y ∈ e.source,
      Function.Bijective (fderivWithin ℝ (e : Tw × Qm m → Pm m × Cz) e.source y))
    (w : Qm m) (hw : ((0 : Tw), w) ∈ e.source) :
    (LinearMap.range ((fderiv ℝ (e : Tw × Qm m → Pm m × Cz) ((0 : Tw), w)).comp
        (ContinuousLinearMap.inr ℝ Tw (Qm m)) : Qm m →ₗ[ℝ] (Pm m × Cz)))
      = (fderiv ℝ Φ (e ((0 : Tw), w))).ker := by
  have hsource_open : IsOpen e.source := e.open_source
  have hderiv_eq : fderiv ℝ (e : Tw × Qm m → Pm m × Cz) ((0 : Tw), w)
      = fderivWithin ℝ (e : Tw × Qm m → Pm m × Cz) e.source ((0 : Tw), w) :=
    (fderivWithin_of_isOpen hsource_open hw).symm
  have hDe_bij : Function.Bijective (fderiv ℝ (e : Tw × Qm m → Pm m × Cz) ((0 : Tw), w)) := by
    rw [hderiv_eq]; exact he_deriv ((0 : Tw), w) hw
  have hchain := chart_comp_fst m Φ hΦ e he_smooth he_Phi w hw
  refine le_antisymm ?_ ?_
  · rintro v ⟨w', rfl⟩
    show (fderiv ℝ Φ (e ((0 : Tw), w)))
      ((fderiv ℝ (e : Tw × Qm m → Pm m × Cz) ((0 : Tw), w))
        (ContinuousLinearMap.inr ℝ Tw (Qm m) w')) = 0
    have hthis := congrArg (fun (T : (Tw × Qm m) →L[ℝ] Tw) =>
      T (ContinuousLinearMap.inr ℝ Tw (Qm m) w')) hchain
    simpa using hthis
  · intro v hv
    obtain ⟨z', hz'⟩ := hDe_bij.2 v
    have hv0 : (fderiv ℝ Φ (e ((0 : Tw), w))) v = 0 := hv
    have hfst : z'.1 = 0 := by
      have hthis := congrArg (fun (T : (Tw × Qm m) →L[ℝ] Tw) => T z') hchain
      rw [ContinuousLinearMap.comp_apply, hz', hv0] at hthis
      simpa using hthis.symm
    refine ⟨z'.2, ?_⟩
    have hinr : ContinuousLinearMap.inr ℝ Tw (Qm m) z'.2 = z' := by
      rw [ContinuousLinearMap.inr_apply]
      exact Prod.ext hfst.symm rfl
    show (fderiv ℝ (e : Tw × Qm m → Pm m × Cz) ((0 : Tw), w))
      (ContinuousLinearMap.inr ℝ Tw (Qm m) z'.2) = v
    rw [hinr, hz']

/-- The derivative of the parametrised projection `w ↦ (e (0,w)).1`. -/
lemma fderiv_chart_gamma (m : ℕ) (Φ : Pm m × Cz → Tw)
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (e : OpenPartialHomeomorph (Tw × Qm m) (Pm m × Cz))
    (he_smooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (e : Tw × Qm m → Pm m × Cz) e.source)
    (w : Qm m) (hw : ((0 : Tw), w) ∈ e.source) :
    fderiv ℝ (fun w' : Qm m => (e ((0 : Tw), w')).1) w
      = (ContinuousLinearMap.fst ℝ (Pm m) Cz).comp
          ((fderiv ℝ (e : Tw × Qm m → Pm m × Cz) ((0 : Tw), w)).comp
            (ContinuousLinearMap.inr ℝ Tw (Qm m))) := by
  have hsource_open : IsOpen e.source := e.open_source
  have hfd_e : HasFDerivAt (e : Tw × Qm m → Pm m × Cz)
      (fderiv ℝ (e : Tw × Qm m → Pm m × Cz) ((0 : Tw), w)) ((0 : Tw), w) :=
    ((he_smooth.contDiffAt (hsource_open.mem_nhds hw)).differentiableAt (by simp)).hasFDerivAt
  have hι : HasFDerivAt (fun w' : Qm m => ((0 : Tw), w'))
      (ContinuousLinearMap.inr ℝ Tw (Qm m)) w := by
    simpa using (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.inr ℝ Tw (Qm m))).const_add
      ((0 : Tw), 0)
  have h1 := hfd_e.comp w hι
  have h2 := (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.fst ℝ (Pm m) Cz)).comp w h1
  exact h2.fderiv

/-- The range of the derivative of the parametrised projection is the image of the kernel of the
full derivative under the first projection. -/
lemma chart_range_gamma (m : ℕ) (Φ : Pm m × Cz → Tw)
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (e : OpenPartialHomeomorph (Tw × Qm m) (Pm m × Cz))
    (he_smooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (e : Tw × Qm m → Pm m × Cz) e.source)
    (he_Phi : ∀ y ∈ e.source, Φ (e y) = y.1)
    (he_deriv : ∀ y ∈ e.source,
      Function.Bijective (fderivWithin ℝ (e : Tw × Qm m → Pm m × Cz) e.source y))
    (w : Qm m) (hw : ((0 : Tw), w) ∈ e.source) :
    Set.range (fderiv ℝ (fun w' : Qm m => (e ((0 : Tw), w')).1) w)
      = (ContinuousLinearMap.fst ℝ (Pm m) Cz) ''
          ((fderiv ℝ Φ (e ((0 : Tw), w))).ker : Set (Pm m × Cz)) := by
  have hrange := chart_range m Φ hΦ e he_smooth he_Phi he_deriv w hw
  rw [fderiv_chart_gamma m Φ hΦ e he_smooth w hw]
  ext v
  constructor
  · rintro ⟨w', rfl⟩
    refine ⟨((fderiv ℝ (e : Tw × Qm m → Pm m × Cz) ((0 : Tw), w)).comp
      (ContinuousLinearMap.inr ℝ Tw (Qm m))) w', ?_, rfl⟩
    rw [← hrange]
    exact ⟨w', rfl⟩
  · rintro ⟨y, hy, rfl⟩
    have hy' : y ∈ LinearMap.range ((fderiv ℝ (e : Tw × Qm m → Pm m × Cz) ((0 : Tw), w)).comp
        (ContinuousLinearMap.inr ℝ Tw (Qm m)) : Qm m →ₗ[ℝ] (Pm m × Cz)) := by
      rw [hrange]; exact hy
    obtain ⟨w', hw'⟩ := hy'
    exact ⟨w', congrArg (ContinuousLinearMap.fst ℝ (Pm m) Cz) hw'⟩

/-- On the chart, the surjectivity of the derivative of the projection `γ` is equivalent to the
surjectivity of the partial derivative in the coordinate direction. -/
lemma chart_surjective_iff (m : ℕ) (Φ : Pm m × Cz → Tw)
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (e : OpenPartialHomeomorph (Tw × Qm m) (Pm m × Cz))
    (he_smooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (e : Tw × Qm m → Pm m × Cz) e.source)
    (he_Phi : ∀ y ∈ e.source, Φ (e y) = y.1)
    (he_deriv : ∀ y ∈ e.source,
      Function.Bijective (fderivWithin ℝ (e : Tw × Qm m → Pm m × Cz) e.source y))
    (w : Qm m) (hw : ((0 : Tw), w) ∈ e.source)
    (hDp : Function.Surjective
      (fderiv ℝ (fun p' : Pm m => Φ (p', (e ((0 : Tw), w)).2)) (e ((0 : Tw), w)).1)) :
    Function.Surjective (fderiv ℝ (fun w' : Qm m => (e ((0 : Tw), w')).1) w)
      ↔ Function.Surjective
          (fderiv ℝ (fun z' : Cz => Φ ((e ((0 : Tw), w)).1, z')) (e ((0 : Tw), w)).2) := by
  have hrg := chart_range_gamma m Φ hΦ e he_smooth he_Phi he_deriv w hw
  have hker := fst_image_ker_eq_univ_iff Φ hΦ (e ((0 : Tw), w)) hDp
  rw [show Function.Surjective (fderiv ℝ (fun w' : Qm m => (e ((0 : Tw), w')).1) w)
      ↔ Set.range (fderiv ℝ (fun w' : Qm m => (e ((0 : Tw), w')).1) w) = Set.univ
      from Set.range_eq_univ.symm, hrg]
  exact hker

/-! ## The local statement -/

/-- **Local structure of the bad set.**  For a point `(p₀,z₀)` in the box at which `Φ` vanishes and
the parameter-derivative is surjective, there is a neighbourhood `U` of `(p₀,z₀)` and a compact set
`A` with empty interior such that every point of `U` which is a *bad* zero (a zero at which the
`z`-derivative fails to be surjective) has its first coordinate in `A`. -/
lemma exists_local_good (m : ℕ) (Φ : Pm m × Cz → Tw)
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (p₀ : Pm m) (z₀ : Cz) (h0 : Φ (p₀, z₀) = 0)
    (hsurjp : Function.Surjective (fderiv ℝ (fun p' : Pm m => Φ (p', z₀)) p₀)) :
    ∃ U : Set (Pm m × Cz), IsOpen U ∧ (p₀, z₀) ∈ U ∧
      ∃ A : Set (Pm m), IsCompact A ∧ interior A = ∅ ∧
        ∀ (p : Pm m) (z : Cz), (p, z) ∈ U →
          Function.Surjective (fderiv ℝ (fun p' : Pm m => Φ (p', z)) p) →
          Φ (p, z) = 0 →
          ¬ Function.Surjective (fderiv ℝ (fun z' : Cz => Φ (p, z')) z) → p ∈ A := by
  classical
  have hfull : Function.Surjective (fderiv ℝ Φ (p₀, z₀)) := by
    intro w
    obtain ⟨v, hv⟩ := hsurjp w
    refine ⟨ContinuousLinearMap.inl ℝ (Pm m) Cz v, ?_⟩
    have h1 : ((fderiv ℝ Φ (p₀, z₀)).comp (ContinuousLinearMap.inl ℝ (Pm m) Cz)) v
        = (fderiv ℝ (fun p' : Pm m => Φ (p', z₀)) p₀) v := by
      rw [fd_comp_inl Φ hΦ p₀ z₀]
    simpa using h1.trans hv
  set A0 : (Pm m × Cz) →L[ℝ] Tw := fderiv ℝ Φ (p₀, z₀) with hA0
  set K0 : Submodule ℝ (Pm m × Cz) := A0.ker with hK0
  obtain ⟨C0, hC0⟩ := K0.exists_isCompl
  have hXdim : Module.finrank ℝ (Pm m × Cz) = m + 7 := by
    rw [Module.finrank_prod, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]
  have hrange : Module.finrank ℝ (LinearMap.range (A0 : (Pm m × Cz) →ₗ[ℝ] Tw)) = 6 := by
    rw [LinearMap.range_eq_top.mpr hfull, finrank_top, finrank_euclideanSpace_fin]
  have hK0dim : Module.finrank ℝ K0 = m + 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker ((A0 : (Pm m × Cz) →ₗ[ℝ] Tw))
    rw [← hK0] at h
    rw [hrange, hXdim] at h
    omega
  obtain ⟨φ⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
      (R := ℝ) (M := K0) (M' := Qm m) (by rw [hK0dim]; simp)
  let lam : (Pm m × Cz) →L[ℝ] Qm m := LinearMap.toContinuousLinearMap
    ((φ : K0 →ₗ[ℝ] Qm m).comp (K0.projectionOnto C0 hC0))
  have hlamker : lam.ker = C0 := by
    change ((φ : K0 →ₗ[ℝ] Qm m).comp (K0.projectionOnto C0 hC0)).ker = C0
    rw [LinearMap.ker_comp]
    have hphi : (φ : K0 →ₗ[ℝ] Qm m).ker = ⊥ := LinearMap.ker_eq_bot.mpr φ.injective
    rw [hphi, Submodule.comap_bot, Submodule.ker_projectionOnto]
  have hlam : Disjoint (fderiv ℝ Φ (p₀, z₀)).ker lam.ker := by
    rw [← hA0, ← hK0, hlamker]
    exact hC0.disjoint
  have hdim : Module.finrank ℝ (Pm m × Cz) = Module.finrank ℝ Tw + (m+1) := by
    rw [hXdim, finrank_euclideanSpace_fin]; omega
  obtain ⟨e, hx0t, he_smooth, he_Phi, he_symm, he_deriv⟩ :=
    Work.Sard.submersion_local_form (m+1) hdim Φ hΦ (p₀, z₀) hfull lam hlam
  -- the parametrised projection and its critical set
  let γ : Qm m → Pm m := fun w => (e ((0 : Tw), w)).1
  let Uγ : Set (Qm m) := {w | ((0 : Tw), w) ∈ e.source}
  have hUγ_open : IsOpen Uγ := e.open_source.preimage (by fun_prop)
  have hγ_smooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) γ Uγ := by
    have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : Qm m => ((0 : Tw), w)) Uγ :=
      (contDiff_const.prodMk contDiff_id).contDiffOn
    have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : Qm m => e ((0 : Tw), w)) Uγ :=
      he_smooth.comp h1 (fun w hw => hw)
    simpa [γ, Function.comp_def] using
      contDiffOn_fst.comp h2 (fun _ _ => Set.mem_univ _)
  have hw₀ : lam (p₀, z₀) ∈ Uγ := by
    have h1 : e.symm (p₀, z₀) ∈ e.source := e.map_target hx0t
    rw [he_symm (p₀, z₀) hx0t, h0] at h1
    exact h1
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.mp (hUγ_open.mem_nhds hw₀)
  set Kc : Set (Qm m) := Metric.closedBall (lam (p₀, z₀)) (ρ/2) with hKc
  have hKc_sub : Kc ⊆ Uγ := by
    intro w hw
    exact hρsub (by rw [Metric.mem_ball]; have := Metric.mem_closedBall.mp hw; linarith [hρpos])
  have hKc_compact : IsCompact Kc := isCompact_closedBall _ _
  have hKc_int : lam (p₀, z₀) ∈ interior Kc := by
    refine interior_maximal Metric.ball_subset_closedBall Metric.isOpen_ball
      (Metric.mem_ball_self (by linarith [hρpos]))
  set Scrit : Set (Qm m) := {w | ¬ Function.Surjective (fderiv ℝ γ w)} with hScrit
  have hScrit_compact : IsCompact (Kc ∩ Scrit) := by
    rw [hScrit]
    exact Work.Sard.prod.isCompact_inter_crit hUγ_open γ hγ_smooth hKc_compact hKc_sub
  refine ⟨e.target ∩ lam ⁻¹' (interior Kc), e.open_target.inter (isOpen_interior.preimage lam.continuous),
    ⟨hx0t, hKc_int⟩, γ '' (Kc ∩ Scrit), ?_, ?_, ?_⟩
  · exact hScrit_compact.image_of_continuousOn
      (hγ_smooth.continuousOn.mono (fun w hw => hKc_sub hw.1))
  · refine le_bot_iff.mp ?_
    have hsub : Kc ∩ Scrit ⊆ Uγ ∩ {w : Qm m |
        ¬ Function.Surjective (fderivWithin ℝ γ Uγ w)} := by
      intro w hw
      refine ⟨hKc_sub hw.1, ?_⟩
      show ¬ Function.Surjective (fderivWithin ℝ γ Uγ w)
      rw [fderivWithin_of_isOpen hUγ_open (hKc_sub hw.1)]
      exact hw.2
    have hws := (Work.Sard.prod.weakSard_all m) (Qm m) (Pm m)
      (by rw [finrank_euclideanSpace_fin])
      (by rw [Module.finrank_fin_fun, finrank_euclideanSpace_fin]) Uγ hUγ_open γ hγ_smooth
    calc interior (γ '' (Kc ∩ Scrit))
        ≤ interior (γ '' (Uγ ∩ {w : Qm m |
            ¬ Function.Surjective (fderivWithin ℝ γ Uγ w)})) :=
          interior_mono (Set.image_mono hsub)
      _ = ∅ := hws
  · intro p z hx hDp hΦz hbad
    have hxt : (p, z) ∈ e.target := hx.1
    have hwK : lam (p, z) ∈ interior Kc := hx.2
    have hsymm : e.symm (p, z) = ((0 : Tw), lam (p, z)) := by
      rw [he_symm (p, z) hxt, hΦz]
    have hsource_w : ((0 : Tw), lam (p, z)) ∈ e.source := by
      rw [← hsymm]; exact e.map_target hxt
    have hx_eq : e ((0 : Tw), lam (p, z)) = (p, z) := by
      rw [← hsymm]; exact e.right_inv hxt
    have hww : (e ((0 : Tw), lam (p, z))).1 = p := by rw [hx_eq]
    have hww2 : (e ((0 : Tw), lam (p, z))).2 = z := by rw [hx_eq]
    have hDp' : Function.Surjective
        (fderiv ℝ (fun p' : Pm m => Φ (p', (e ((0 : Tw), lam (p, z))).2))
          (e ((0 : Tw), lam (p, z))).1) := by
      rw [hww, hww2]; exact hDp
    have hiff := chart_surjective_iff m Φ hΦ e he_smooth he_Phi he_deriv (lam (p, z)) hsource_w hDp'
    have hbadγ : ¬ Function.Surjective (fderiv ℝ γ (lam (p, z))) := by
      intro hsurj
      have hthis := hiff.mp hsurj
      rw [hww, hww2] at hthis
      exact hbad hthis
    have hp : p = γ (lam (p, z)) := by
      show p = (e ((0 : Tw), lam (p, z))).1
      rw [hww]
    rw [hp]
    exact Set.mem_image_of_mem γ ⟨interior_subset hwK, hbadγ⟩

/-! ## The global statement -/

/-- The set of bad parameter values has empty interior. -/
lemma bad_interior_empty (m : ℕ) (Φ : Pm m × Cz → Tw)
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hsurj : ∀ (p : Pm m) (z : Cz), z ∈ Submission.Drive.unitBox 6 → Φ (p, z) = 0 →
      Function.Surjective (fderiv ℝ (fun p' : Pm m => Φ (p', z)) p)) :
    interior {p : Pm m | ∃ z ∈ Submission.Drive.unitBox 6, Φ (p, z) = 0 ∧
      ¬ Function.Surjective (fderiv ℝ (fun z' : Cz => Φ (p, z')) z)} = ∅ := by
  classical
  by_contra hne
  set Bad : Set (Pm m) := {p | ∃ z ∈ Submission.Drive.unitBox 6, Φ (p, z) = 0 ∧
      ¬ Function.Surjective (fderiv ℝ (fun z' : Cz => Φ (p, z')) z)} with hBad
  obtain ⟨p₀, hp₀⟩ := Set.nonempty_iff_ne_empty.mpr hne
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hp₀)
  have hBsub : Metric.closedBall p₀ (ε/2) ⊆ Bad := by
    intro p hp
    have hp' : p ∈ Metric.closedBall p₀ (ε/2) := hp
    refine interior_subset (hεsub ?_)
    rw [Metric.mem_ball]
    have := Metric.mem_closedBall.mp hp'
    linarith [hε]
  have hBint : (interior (Metric.closedBall p₀ (ε/2))).Nonempty :=
    ⟨p₀, interior_maximal Metric.ball_subset_closedBall Metric.isOpen_ball
      (Metric.mem_ball_self (by linarith [hε]))⟩
  -- the compact set of bad points
  set K : Set (Pm m × Cz) := {x | x.1 ∈ Metric.closedBall p₀ (ε/2) ∧
      x.2 ∈ Submission.Drive.unitBox 6 ∧ Φ x = 0 ∧
      ¬ Function.Surjective (fderiv ℝ (fun z' : Cz => Φ (x.1, z')) x.2)} with hK
  have hcont : Continuous (fun x : Pm m × Cz =>
      (fderiv ℝ Φ x).comp (ContinuousLinearMap.inr ℝ (Pm m) Cz)) := by
    have h1 : Continuous (fun T : (Pm m × Cz) →L[ℝ] Tw =>
        T.comp (ContinuousLinearMap.inr ℝ (Pm m) Cz)) := by
      have h := (ContinuousLinearMap.compL ℝ Cz (Pm m × Cz) Tw).continuous.clm_apply
        (continuous_const : Continuous
          (fun _ : (Pm m × Cz) →L[ℝ] Tw => ContinuousLinearMap.inr ℝ (Pm m) Cz))
      simpa using h
    exact h1.comp (hΦ.continuous_fderiv (by simp))
  have hK_eq : K = ((Metric.closedBall p₀ (ε/2) ×ˢ Submission.Drive.unitBox 6)
      ∩ {x : Pm m × Cz | Φ x = 0})
      ∩ {x : Pm m × Cz | ¬ Function.Surjective
          ((fderiv ℝ Φ x).comp (ContinuousLinearMap.inr ℝ (Pm m) Cz))} := by
    rw [hK]
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_prod]
    rw [← fd_comp_inr Φ hΦ x.1 x.2]
    tauto
  have hKcompact : IsCompact K := by
    rw [hK_eq]
    have hc1 : IsClosed ((Metric.closedBall p₀ (ε/2) ×ˢ Submission.Drive.unitBox 6)
        ∩ {x : Pm m × Cz | Φ x = 0}) :=
      ((isCompact_closedBall p₀ (ε/2)).isClosed.prod (Work.Drive.isClosed_unitBox 6)).inter
        (isClosed_eq hΦ.continuous continuous_const)
    have hc2 : IsClosed {x : Pm m × Cz | ¬ Function.Surjective
        ((fderiv ℝ Φ x).comp (ContinuousLinearMap.inr ℝ (Pm m) Cz))} :=
      Work.Sard.prod.isClosed_setOf_not_surjective_clm'.preimage hcont
    exact IsCompact.of_isClosed_subset
      ((isCompact_closedBall p₀ (ε/2)).prod (Work.Drive.isCompact_unitBox 6))
      (hc1.inter hc2) (fun x hx => hx.1.1)
  -- the local neighbourhoods
  have hchoice : ∀ x : K, ∃ U : Set (Pm m × Cz), IsOpen U ∧ (x.1 : Pm m × Cz) ∈ U ∧
      ∃ A : Set (Pm m), IsCompact A ∧ interior A = ∅ ∧
        (∀ (p : Pm m) (z : Cz), (p, z) ∈ U →
          Function.Surjective (fderiv ℝ (fun p' : Pm m => Φ (p', z)) p) →
          Φ (p, z) = 0 →
          ¬ Function.Surjective (fderiv ℝ (fun z' : Cz => Φ (p, z')) z) → p ∈ A) :=
    fun x => exists_local_good m Φ hΦ x.1.1 x.1.2 x.2.2.2.1
      (hsurj x.1.1 x.1.2 x.2.2.1 x.2.2.2.1)
  choose U hU using hchoice
  obtain ⟨s, hs⟩ := hKcompact.elim_finite_subcover U (fun x => (hU x).1)
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, (hU ⟨x, hx⟩).2.1⟩)
  have hBsub2 : Metric.closedBall p₀ (ε/2) ⊆ ⋃ y : s, (hU (y : K)).2.2.choose := by
    intro p hp
    have hpBad : p ∈ Bad := hBsub hp
    obtain ⟨z, hzbox, hΦz, hbad⟩ := hpBad
    have hxK : (p, z) ∈ K := ⟨hp, hzbox, hΦz, hbad⟩
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs hxK)
    exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, (hU (y : K)).2.2.choose_spec.2.2 p z hxy
      (hsurj p z hzbox hΦz) hΦz hbad⟩
  -- Baire
  have hclosedA : ∀ y : s, IsClosed ((hU (y : K)).2.2.choose) :=
    fun y => (hU (y : K)).2.2.choose_spec.1.isClosed
  have hemptyA : ∀ y : s, interior ((hU (y : K)).2.2.choose) = ∅ :=
    fun y => (hU (y : K)).2.2.choose_spec.2.1
  have hBaire := Work.Sard.wp.interior_eq_empty_iUnion_isClosed hclosedA hemptyA
  have hsubInt : interior (Metric.closedBall p₀ (ε/2)) ⊆
      interior (⋃ y : s, (hU (y : K)).2.2.choose) := interior_mono hBsub2
  rw [hBaire] at hsubInt
  exact hBint.ne_empty (Set.Subset.antisymm hsubInt (Set.empty_subset _))

theorem generic_regularization_of_family (m : ℕ)
    (Φ : EuclideanSpace ℝ (Fin m) × Work.Drive.Amb 6 → Work.Drive.Tgt 6)
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hsurj : ∀ (p : EuclideanSpace ℝ (Fin m)) (z : Work.Drive.Amb 6),
      z ∈ Submission.Drive.unitBox 6 → Φ (p, z) = 0 →
      Function.Surjective (fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) => Φ (p', z)) p)) :
    ∃ p : EuclideanSpace ℝ (Fin m), ∀ z ∈ Submission.Drive.unitBox 6, Φ (p, z) = 0 →
      Function.Surjective (fderiv ℝ (fun z' : Work.Drive.Amb 6 => Φ (p, z')) z) := by
  haveI : Nonempty (Pm m) := ⟨0⟩
  have hBad := bad_interior_empty m Φ hΦ hsurj
  have hne : {p : Pm m | ∃ z ∈ Submission.Drive.unitBox 6, Φ (p, z) = 0 ∧
      ¬ Function.Surjective (fderiv ℝ (fun z' : Cz => Φ (p, z')) z)} ≠ Set.univ := by
    intro h
    have h1 : interior (Set.univ : Set (Pm m)) = ∅ := by rw [← h]; exact hBad
    rw [interior_univ] at h1
    exact Set.univ_nonempty.ne_empty h1
  obtain ⟨p, hp⟩ := (Set.ne_univ_iff_exists_notMem _).mp hne
  refine ⟨p, fun z hz hz0 => ?_⟩
  by_contra hcon
  exact hp ⟨z, hz, hz0, hcon⟩

end

end Work.MetricSquare
