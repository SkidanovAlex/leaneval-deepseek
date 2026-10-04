import Mathlib
import Submission.Work.Diff.C.HessLowerKit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle CovariantDerivative

/-! ## Auxiliary: the scalar Riccati comparison

Let `g ≥ 0`, `f`, `F`, `q` be functions on `(0,T)` with `g' = 2f`, `f' = F - q`, `f² ≤ F g` and
`q ≤ c² g`.  Put `W t = c * cot (c*t)` and `H = f - W * g`.  Then `H' ≥ H²/g` wherever `H < 0`, and
`H = 0` wherever `g = 0`; since `H → 0` at `0⁺` (hypothesis `hlim`), `H` can never be negative.
Hence `c * cot (c*d) * g d ≤ f d`.

This is the Sturm/Riccati comparison ("logarithmic derivative of the modulus") behind the Rauch
comparison theorem; it needs *no* positivity of `g`, which is what makes it applicable to Jacobi
fields vanishing at `0`. -/

/-- **Scalar Riccati comparison.**  See the section docstring. -/
theorem jml_cot_bound_of_data {g f F q : ℝ → ℝ} {c T d : ℝ} (hc : 0 < c) (hT : 0 < T)
    (hcT : c * T ≤ Real.pi) (hd : d ∈ Set.Ioo 0 T)
    (hg0 : ∀ t ∈ Set.Ioo 0 T, 0 ≤ g t)
    (hfg0 : ∀ t ∈ Set.Ioo 0 T, g t = 0 → f t = 0)
    (hgder : ∀ t ∈ Set.Ioo 0 T, HasDerivAt g (2 * f t) t)
    (hfder : ∀ t ∈ Set.Ioo 0 T, HasDerivAt f (F t - q t) t)
    (hCS : ∀ t ∈ Set.Ioo 0 T, (f t) ^ 2 ≤ F t * g t)
    (hq : ∀ t ∈ Set.Ioo 0 T, q t ≤ c ^ 2 * g t)
    (hsmall : ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Set.Ioo 0 δ, g t ≤ C * t ^ 2) :
    c * Real.cot (c * d) * g d ≤ f d := by
  set W : ℝ → ℝ := fun t => c * Real.cot (c * t) with hWdef
  set H : ℝ → ℝ := fun t => f t - W t * g t with hHdef
  set h : ℝ → ℝ := fun t => (F t - q t) + (c ^ 2 + (W t) ^ 2) * g t - 2 * W t * f t with hhdef
  -- `sin (c t) ≠ 0` on `(0,T)`
  have hsin : ∀ t ∈ Set.Ioo 0 T, Real.sin (c * t) ≠ 0 := by
    intro t ht
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by nlinarith [ht.1, hc])
      (by nlinarith [ht.2, hc, hcT]))
  -- `W' = -(c² + W²)`
  have hWd : ∀ t ∈ Set.Ioo 0 T, HasDerivAt W (-(c ^ 2 + (W t) ^ 2)) t := by
    intro t ht
    simpa only [hWdef] using hasDerivAt_cot_const_mul (c := c) (t := t) (hsin t ht)
  -- `H' = h`
  have hHd : ∀ t ∈ Set.Ioo 0 T, HasDerivAt H (h t) t := by
    intro t ht
    have hprod := (hWd t ht).mul (hgder t ht)
    have hsub := (hfder t ht).sub hprod
    refine hsub.congr_deriv ?_
    simp only [hhdef]
    ring
  -- the Riccati inequality `H² ≤ h * g`
  have hineq : ∀ t ∈ Set.Ioo 0 T, (H t) ^ 2 ≤ h t * g t := by
    intro t ht
    have hcs := hCS t ht
    have hq' := hq t ht
    have hgnn := hg0 t ht
    have hmul : q t * g t ≤ c ^ 2 * g t * g t := mul_le_mul_of_nonneg_right hq' hgnn
    simp only [hHdef, hWdef, hhdef]
    nlinarith [hcs, hmul]
  -- where `H < 0`, the function `g` is positive (this is where `hfg0` enters)
  have hgpos_of_neg : ∀ t ∈ Set.Ioo 0 T, H t < 0 → 0 < g t := by
    intro t ht hneg
    have hneg' : f t - W t * g t < 0 := by simpa only [hHdef] using hneg
    have hgne : g t ≠ 0 := by
      intro hz
      rw [hz, mul_zero, sub_zero] at hneg'
      exact absurd (hfg0 t ht hz) (ne_of_lt hneg')
    exact lt_of_le_of_ne (hg0 t ht) (Ne.symm hgne)
  -- and there the derivative of `H` is positive, so `H` is nondecreasing
  have hderivpos : ∀ t ∈ Set.Ioo 0 T, H t < 0 → 0 < h t := by
    intro t ht hneg
    have hgpos := hgpos_of_neg t ht hneg
    have h1 := hineq t ht
    have h2 : 0 < (H t) ^ 2 := sq_pos_of_ne_zero (ne_of_lt hneg)
    have h3 : (H t) ^ 2 / g t ≤ h t := by
      rw [div_le_iff₀ hgpos]
      linarith [h1]
    have h4 : 0 < (H t) ^ 2 / g t := div_pos h2 hgpos
    linarith
  -- main argument: `H d ≥ 0`
  have hmain : 0 ≤ H d := by
    by_contra hcon
    have hnegd : H d < 0 := not_le.mp hcon
    set A : Set ℝ := {s | 0 < s ∧ s < d ∧ ∀ r ∈ Set.Ioo s d, H r < 0} with hAdef
    have hmem : ∀ s, s ∈ A ↔ 0 < s ∧ s < d ∧ ∀ r ∈ Set.Ioo s d, H r < 0 := by
      intro s
      rw [hAdef, Set.mem_setOf_eq]
    have hAne : A.Nonempty := by
      have hcont : ContinuousAt H d := (hHd d hd).continuousAt
      have hnhds : {r : ℝ | H r < 0} ∈ 𝓝 d :=
        hcont.preimage_mem_nhds (IsOpen.mem_nhds isOpen_Iio hnegd)
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnhds
      set δ : ℝ := min (ε / 2) (d / 2) with hδdef
      have hδpos : 0 < δ := by rw [hδdef]; exact lt_min (by linarith) (by linarith [hd.1])
      have hδle : δ ≤ d / 2 := by rw [hδdef]; exact min_le_right _ _
      refine ⟨d - δ, (hmem _).mpr ⟨by linarith, by linarith, ?_⟩⟩
      intro r hr
      apply hball
      rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (by linarith [hr.2])]
      have hδle' : δ ≤ ε / 2 := by rw [hδdef]; exact min_le_left _ _
      linarith [hr.1, hδle']
    have hbdd : BddBelow A := ⟨0, fun b hb => le_of_lt ((hmem b).mp hb).1⟩
    set a : ℝ := sInf A with hadef
    have ha0 : 0 ≤ a := by
      rw [hadef]
      exact le_csInf hAne (fun b hb => le_of_lt ((hmem b).mp hb).1)
    have hAne2 : A.Nonempty := hAne
    obtain ⟨s0, hs0⟩ := hAne2
    have had : a < d := by
      have h1 : a ≤ s0 := by rw [hadef]; exact csInf_le hbdd hs0
      have h2 : s0 < d := ((hmem s0).mp hs0).2.1
      linarith
    have hneg : ∀ r ∈ Set.Ioo a d, H r < 0 := by
      intro r hr
      have hlt : sInf A < r := by rw [← hadef]; exact hr.1
      obtain ⟨s, hsA, hsr⟩ := exists_lt_of_csInf_lt hAne hlt
      exact ((hmem s).mp hsA).2.2 r ⟨hsr, hr.2⟩
    have hxT : ∀ x ∈ Set.Ioo a d, x ∈ Set.Ioo 0 T :=
      fun x hx => ⟨lt_of_le_of_lt ha0 hx.1, lt_trans hx.2 hd.2⟩
    have hmono : MonotoneOn H (Set.Ioo a d) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ioo a d) ?_ ?_ ?_
      · intro x hx
        exact (hHd x (hxT x hx)).continuousAt.continuousWithinAt
      · rw [interior_Ioo]
        intro x hx
        exact (hHd x (hxT x hx)).differentiableAt.differentiableWithinAt
      · rw [interior_Ioo]
        intro x hx
        rw [(hHd x (hxT x hx)).deriv]
        exact le_of_lt (hderivpos x (hxT x hx) (hneg x hx))
    rcases eq_or_lt_of_le ha0 with hza | hapos
    · -- `a = 0`: the negativity reaches `0`; the Riccati bound on `(0,r₀)` is impossible
      obtain ⟨C, hCpos, δ₀, hδ₀pos, hδ₀⟩ := hsmall
      set r₀ : ℝ := min d δ₀ with hr₀def
      have hr₀pos : 0 < r₀ := by rw [hr₀def]; exact lt_min hd.1 hδ₀pos
      have hr₀d : r₀ ≤ d := by rw [hr₀def]; exact min_le_left _ _
      have hr₀T : r₀ < T := lt_of_le_of_lt hr₀d hd.2
      have hneg₀ : ∀ t ∈ Set.Ioo 0 r₀, H t < 0 := by
        intro t ht
        exact hneg t ⟨by rw [← hza]; exact ht.1, lt_of_lt_of_le ht.2 hr₀d⟩
      have hr₀mem : ∀ t ∈ Set.Ioo 0 r₀, t ∈ Set.Ioo 0 T :=
        fun t ht => ⟨ht.1, lt_trans ht.2 hr₀T⟩
      have hgpos₀ : ∀ t ∈ Set.Ioo 0 r₀, 0 < g t :=
        fun t ht => hgpos_of_neg t (hr₀mem t ht) (hneg₀ t ht)
      have hricc := riccati_lower_bound (H := H) (h := h) (g := g) (T := r₀) (C := C) (δ := δ₀)
        hr₀pos (fun t ht => hHd t (hr₀mem t ht)) hgpos₀
        (fun t ht => hineq t (hr₀mem t ht)) hCpos hδ₀pos hδ₀
      have hhalf : r₀ / 2 ∈ Set.Ioo 0 r₀ := ⟨by linarith, by linarith⟩
      have := hricc (r₀ / 2) hhalf
      linarith [hneg₀ (r₀ / 2) hhalf]
    · -- `a > 0`: `H a = 0`, and monotonicity gives `H r ≥ H a = 0`
      have hamem : a ∈ Set.Ioo 0 T := ⟨hapos, lt_trans had hd.2⟩
      have hcont_a : ContinuousAt H a := (hHd a hamem).continuousAt
      have hlima : Filter.Tendsto H (nhdsWithin a (Set.Ioi a)) (nhds (H a)) :=
        hcont_a.tendsto.mono_left nhdsWithin_le_nhds
      have hHa_le : H a ≤ 0 := by
        refine le_of_tendsto hlima ?_
        filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds had)]
          with y hay hyd
        exact le_of_lt (hneg y ⟨hay, hyd⟩)
      have hHa_ge : 0 ≤ H a := by
        by_contra hlt
        have hlt' : H a < 0 := not_le.mp hlt
        have hnhds : {x : ℝ | H x < 0} ∈ 𝓝 a :=
          hcont_a.preimage_mem_nhds (IsOpen.mem_nhds isOpen_Iio hlt')
        obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnhds
        set δ : ℝ := min (ε / 2) (a / 2) with hδdef
        have hδpos : 0 < δ := by rw [hδdef]; exact lt_min (by linarith) (by linarith)
        have hδle : δ ≤ ε / 2 := by rw [hδdef]; exact min_le_left _ _
        have hδlea : δ ≤ a / 2 := by rw [hδdef]; exact min_le_right _ _
        have hsA : a - δ ∈ A := by
          refine (hmem _).mpr ⟨by linarith, by linarith, ?_⟩
          intro x hx
          rcases lt_or_ge x a with hxa | hxa
          · apply hball
            rw [Metric.mem_ball, Real.dist_eq, abs_of_nonpos (by linarith)]
            linarith [hx.1, hδle, hε]
          · rcases eq_or_lt_of_le hxa with hxa' | hxa'
            · rw [← hxa']; exact hlt'
            · exact hneg x ⟨hxa', hx.2⟩
        have := csInf_le hbdd hsA
        rw [← hadef] at this
        linarith
      obtain ⟨r, har, hrd⟩ : ∃ r : ℝ, a < r ∧ r < d := ⟨(a + d) / 2, by linarith, by linarith⟩
      have hev : ∀ᶠ y in (nhdsWithin a (Set.Ioi a)), H y ≤ H r := by
        filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds har)]
          with y hay hyr
        exact hmono ⟨hay, lt_trans hyr hrd⟩ ⟨har, hrd⟩ (le_of_lt hyr)
      have hle : H a ≤ H r := le_of_tendsto hlima hev
      have hHa0 : H a = 0 := le_antisymm hHa_le hHa_ge
      rw [hHa0] at hle
      linarith [hneg r ⟨har, hrd⟩]
  have hW : W d * g d ≤ f d := by
    have h1 : f d - W d * g d ≥ 0 := by simpa only [hHdef] using hmain
    linarith
  simpa only [hWdef] using hW

section Aux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [T2Space M] [CompactSpace M] [Nontrivial E]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [ContMDiffCovariantDerivative cov ∞]

/-! ## Auxiliary: derivatives of the scalar Sturm data along a Jacobi field

For a Jacobi field `J` along a curve `γ` (locally Jacobi near every time, with non-vanishing
velocity), the functions `g = ⟪J,J⟫` and `f = ⟪∇_{γ'}J, J⟫` satisfy `g' = 2f` and
`f' = ⟪∇J,∇J⟫ - ⟪R(J,γ')γ',J⟫`. -/

/-- **`d/dt ⟪J,J⟫ = 2⟪∇_{γ'}J,J⟫`.** -/
theorem jml_hasDerivAt_inner_self
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {γ : ℝ → M} {J : (t : ℝ) → TangentSpace I (γ t)}
    (hγ : ContMDiff 𝓘(ℝ) I ∞ γ) (hJ : ∀ t : ℝ, Submission.RauchGlobal.IsJacobiAt cov γ J t)
    (hne : ∀ t : ℝ, Submission.Geodesic.curveVelocity (I := I) γ t ≠ 0) :
    ∀ t : ℝ, HasDerivAt (fun s : ℝ => Inner.inner ℝ (J s) (J s))
      (2 * Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov J t) (J t)) t := by
  intro t
  have hγOn : ContMDiffOn 𝓘(ℝ) I ∞ γ (Set.Ioo (t - 1) (t + 1)) := hγ.contMDiffOn
  have hγmd : MDifferentiableAt 𝓘(ℝ) I γ t := hγ.contMDiffAt.mdifferentiableAt (by simp)
  have hVsm : Submission.JacobiGlobal.SmoothAlongAt (I := I) γ J t :=
    Submission.JacobiGlobal.smoothAlongAt_of_isJacobiAt (cov := cov) htor hJ hγOn
  obtain ⟨𝒱, h𝒱sm, h𝒱ev⟩ :=
    Submission.JacobiGlobal.exists_section_of_smoothAlongAt (I := I) hγOn (hne t) hVsm
  have hmain := Submission.Variation.hasDerivAt_inner_sections (cov := cov) hmet h𝒱sm h𝒱sm hγmd
  have hcov : cov 𝒱 (γ t) (Submission.Geodesic.curveVelocity (I := I) γ t)
      = Submission.JacobiGlobal.covAlong cov J t :=
    (Submission.JacobiGlobal.covAlong_eq_cov (cov := cov) htor hγOn (hne t) hVsm h𝒱sm h𝒱ev).symm
  have hval : Inner.inner ℝ
        (cov 𝒱 (γ t) (Submission.Geodesic.curveVelocity (I := I) γ t)) (𝒱 (γ t))
      + Inner.inner ℝ (𝒱 (γ t))
        (cov 𝒱 (γ t) (Submission.Geodesic.curveVelocity (I := I) γ t))
      = 2 * Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov J t) (J t) := by
    rw [hcov, h𝒱ev.self_of_nhds,
      real_inner_comm (Submission.JacobiGlobal.covAlong cov J t) (J t)]
    ring
  have hev : (fun s : ℝ => Inner.inner ℝ (𝒱 (γ s)) (𝒱 (γ s)))
      =ᶠ[𝓝 t] (fun s : ℝ => Inner.inner ℝ (J s) (J s)) := by
    filter_upwards [h𝒱ev] with s hs
    rw [hs]
  exact (hmain.congr_deriv hval).congr_of_eventuallyEq hev.symm

/-- **`d/dt ⟪∇_{γ'}J,J⟫ = ⟪∇J,∇J⟫ - ⟪R(J,γ')γ',J⟫`.** -/
theorem jml_hasDerivAt_inner_covAlong
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {γ : ℝ → M} {J : (t : ℝ) → TangentSpace I (γ t)}
    (hγ : ContMDiff 𝓘(ℝ) I ∞ γ) (hJ : ∀ t : ℝ, Submission.RauchGlobal.IsJacobiAt cov γ J t)
    (hne : ∀ t : ℝ, Submission.Geodesic.curveVelocity (I := I) γ t ≠ 0) :
    ∀ t : ℝ, HasDerivAt
      (fun s : ℝ => Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov J s) (J s))
      (Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov J t)
          (Submission.JacobiGlobal.covAlong cov J t)
        - Inner.inner ℝ (Submission.CurvatureVec.curvVec cov (γ t) (J t)
            (Submission.Geodesic.curveVelocity (I := I) γ t)
            (Submission.Geodesic.curveVelocity (I := I) γ t)) (J t)) t := by
  intro t
  obtain ⟨x₀, η, hηpos, hηle, hsrcIcc, hcdu, hcdy, hframe, hjacIcc⟩ :=
    Submission.JacobiCoordsEq.exists_chartCoords_contDiffOn_eq (cov := cov) htor (γ := γ) (J := J)
      (s := t) (ε := 1) one_pos hγ.contMDiffOn (hJ t)
  set u : ℝ → E := Submission.IntrinsicVariation.chartCoord (I := I) x₀ γ with hudef
  set y : ℝ → E := Submission.JacobiCoords.chartCoords (I := I) x₀ γ J with hydef
  have hUsub : Set.Ioo (t - η) (t + η) ⊆ Set.Icc (t - η) (t + η) := fun s hs => ⟨hs.1.le, hs.2.le⟩
  have htU : t ∈ Set.Ioo (t - η) (t + η) := ⟨by linarith, by linarith⟩
  have hUopen : IsOpen (Set.Ioo (t - η) (t + η)) := isOpen_Ioo
  have hcduO : ContDiffOn ℝ ∞ u (Set.Ioo (t - η) (t + η)) := by
    rw [hudef]; exact hcdu.mono hUsub
  have hcdyO : ContDiffOn ℝ ∞ y (Set.Ioo (t - η) (t + η)) := by
    rw [hydef]; exact hcdy.mono hUsub
  have hcduO' : ContDiffOn ℝ ∞ (deriv u) (Set.Ioo (t - η) (t + η)) :=
    hcduO.deriv_of_isOpen hUopen (le_of_eq (by simp))
  have hcdyO' : ContDiffOn ℝ ∞ (deriv y) (Set.Ioo (t - η) (t + η)) :=
    hcdyO.deriv_of_isOpen hUopen (le_of_eq (by simp))
  have hduEv : ∀ᶠ s in 𝓝 t, HasDerivAt u (deriv u s) s :=
    Submission.JacobiGlobal.eventually_hasDerivAt_of_contDiffOn hUopen htU hcduO
  have hdyEv : ∀ᶠ s in 𝓝 t, HasDerivAt y (deriv y s) s :=
    Submission.JacobiGlobal.eventually_hasDerivAt_of_contDiffOn hUopen htU hcdyO
  have hddu : HasDerivAt (deriv u) (deriv (deriv u) t) t :=
    (Submission.JacobiGlobal.eventually_hasDerivAt_of_contDiffOn hUopen htU hcduO').self_of_nhds
  have hddy : HasDerivAt (deriv y) (deriv (deriv y) t) t :=
    (Submission.JacobiGlobal.eventually_hasDerivAt_of_contDiffOn hUopen htU hcdyO').self_of_nhds
  have hsrcU : ∀ s ∈ Set.Ioo (t - η) (t + η), γ s ∈ (chartAt H x₀).source :=
    fun s hs => hsrcIcc s (hUsub hs)
  have hsrc : γ t ∈ (chartAt H x₀).source := hsrcU t htU
  have hsrcEv : ∀ᶠ s in 𝓝 t, γ s ∈ (chartAt H x₀).source :=
    Filter.eventually_of_mem (isOpen_Ioo.mem_nhds htU) hsrcU
  have hutgtAt : ∀ s ∈ Set.Ioo (t - η) (t + η), u s ∈ (extChartAt I x₀).target := by
    intro s hs
    rw [hudef, Submission.IntrinsicVariation.chartCoord]
    exact (extChartAt I x₀).map_source (by rw [extChartAt_source]; exact hsrcU s hs)
  have hutgtEv : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target :=
    Filter.eventually_of_mem (isOpen_Ioo.mem_nhds htU) hutgtAt
  have hγeqEv : γ =ᶠ[𝓝 t] fun s => (extChartAt I x₀).symm (u s) := by
    filter_upwards [isOpen_Ioo.mem_nhds htU] with s hs
    rw [hudef, Submission.IntrinsicVariation.chartCoord]
    exact (PartialEquiv.left_inv (extChartAt I x₀)
      (by rw [extChartAt_source]; exact hsrcU s hs)).symm
  have hframeEv : ∀ᶠ s in 𝓝 t, Submission.Geodesic.frameVector (I := I) x₀ (γ s) (y s) = J s := by
    filter_upwards [isOpen_Ioo.mem_nhds htU] with s hs
    rw [hydef]
    exact hframe s (hUsub hs)
  have hjac : Submission.BonnetMyers.DtDsP cov x₀ u y (deriv u) (deriv y) t
      + Submission.Rauch.chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (y t) (deriv u t) = 0 := by
    have h := hjacIcc t ⟨htU.1.le, htU.2.le⟩
    simpa only [hudef, hydef] using h
  have hZev : ∀ᶠ s in 𝓝 t, Submission.JacobiGlobal.covAlong cov J s
      = Submission.Geodesic.frameVector (I := I) x₀ (γ s)
        (Submission.BonnetMyers.DtQ cov x₀ u y (deriv u) (deriv y) s) := by
    refine Filter.eventually_of_mem (isOpen_Ioo.mem_nhds htU) (fun s hs => ?_)
    have hVsm : Submission.JacobiGlobal.SmoothAlongAt (I := I) γ J s :=
      Submission.JacobiGlobal.smoothAlongAt_of_isJacobiAt (cov := cov) htor hJ hγ.contMDiffOn
    have hsrcEv' : ∀ᶠ r in 𝓝 s, γ r ∈ (chartAt H x₀).source :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hs) hsrcU
    have hutgtEv' : ∀ᶠ r in 𝓝 s, u r ∈ (extChartAt I x₀).target :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hs) hutgtAt
    have hγeqEv' : γ =ᶠ[𝓝 s] fun r => (extChartAt I x₀).symm (u r) := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
      rw [hudef, Submission.IntrinsicVariation.chartCoord]
      exact (PartialEquiv.left_inv (extChartAt I x₀)
        (by rw [extChartAt_source]; exact hsrcU r hr)).symm
    have hduEv' : ∀ᶠ r in 𝓝 s, HasDerivAt u (deriv u r) r :=
      Submission.JacobiGlobal.eventually_hasDerivAt_of_contDiffOn hUopen hs hcduO
    have hdyEv' : ∀ᶠ r in 𝓝 s, HasDerivAt y (deriv y r) r :=
      Submission.JacobiGlobal.eventually_hasDerivAt_of_contDiffOn hUopen hs hcdyO
    have hframeEv' : ∀ᶠ r in 𝓝 s, Submission.Geodesic.frameVector (I := I) x₀ (γ r) (y r) = J r := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
      rw [hydef]
      exact hframe r (hUsub hr)
    exact Submission.JacobiGlobal.covAlong_eq_chart (cov := cov) htor (γ := γ) (V := J) (t := s)
      hγ.contMDiffOn (hne s) hVsm (x₀ := x₀) (u := u) (w := deriv u) (y := y) (y' := deriv y)
      (hsrcU s hs) hsrcEv' hutgtEv' hγeqEv' hduEv' hframeEv' hdyEv'
  have hγmd : MDifferentiableAt 𝓘(ℝ) I γ t := hγ.contMDiffAt.mdifferentiableAt (by simp)
  have hVev : J =ᶠ[𝓝 t]
      (fun s : ℝ => Submission.Geodesic.frameVector (I := I) x₀ (γ s) (y s)) := by
    filter_upwards [hframeEv] with s hs
    exact hs.symm
  have hZev' : (fun s : ℝ => Submission.JacobiGlobal.covAlong cov J s) =ᶠ[𝓝 t]
      (fun s : ℝ => Submission.Geodesic.frameVector (I := I) x₀ (γ s)
        (Submission.BonnetMyers.DtQ cov x₀ u y (deriv u) (deriv y) s)) := hZev
  have hres := Submission.IndexIntrinsic2.hasDerivAt_inner_idxAlong (cov := cov) hmet htor x₀
    (γ := γ) (V := J) (Z := Submission.JacobiGlobal.covAlong cov J)
    (u := u) (w := deriv u) (w' := deriv (deriv u))
    (J := y) (J' := deriv y) (J'' := deriv (deriv y)) (t := t)
    hsrc hutgtEv hγeqEv hduEv hγmd hddu hdyEv.self_of_nhds hddy hjac hVev hZev'
  simpa only [Submission.IndexIntrinsic.idxAlong] using hres


/-! ## Auxiliary: the quadratic vanishing of `⟪J,J⟫` at a zero of `J` -/

/-- **`⟪J t,J t⟫ = O(t²)` near `0` for a Jacobi field with `J 0 = 0`.** -/
theorem jml_inner_self_le_mul_sq
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {γ : ℝ → M} {J : (t : ℝ) → TangentSpace I (γ t)}
    (hγ : ContMDiff 𝓘(ℝ) I ∞ γ) (hJ : ∀ t : ℝ, Submission.RauchGlobal.IsJacobiAt cov γ J t)
    (hJ0 : J 0 = 0) :
    ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ t ∈ Set.Ioo 0 δ, Inner.inner ℝ (J t) (J t) ≤ C * t ^ 2 := by
  obtain ⟨x₀, u, w, y, ρ, hρ, hutgt, hu, hγeq, hframe, hunit, hy, hDy, hjac⟩ :=
    Submission.RauchGlobal.exists_local_data (cov := cov) (hJ 0)
  have h0mem : (0 : ℝ) ∈ Set.Ioo (0 - ρ) (0 + ρ) := ⟨by linarith, by linarith⟩
  -- the chart coordinates of `J` vanish at `0`
  have hsrc0 : γ 0 ∈ (chartAt H x₀).source := by
    rw [hγeq 0 h0mem]
    exact Submission.ChartConnection.mem_source_chartCurve (I := I) (hutgt 0 h0mem)
  have hy0 : y 0 = 0 := by
    have h1 : Submission.Geodesic.frameVector (I := I) x₀ (γ 0) (y 0) = 0 := by
      rw [hframe 0 h0mem, hJ0]
    exact (Submission.ChartBounds.frameVector_eq_zero_iff (I := I) hsrc0 (y 0)).mp h1
  -- the limit `√⟨y,y⟩ / t → L`
  have htend := Submission.RauchCompareK.tendsto_sqrt_chartGram_div (cov := cov) hmet
    (hu 0 h0mem) (hutgt 0 h0mem) (hy 0 h0mem) hy0
  set L : ℝ := Real.sqrt (Submission.ChartConnection.chartGram (I := I) x₀
    ((extChartAt I x₀).symm (u 0)) (deriv y 0) (deriv y 0)) with hLdef
  -- extract an eventual bound
  have hbound : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      Real.sqrt (Submission.ChartConnection.chartGram (I := I) x₀
        ((extChartAt I x₀).symm (u t)) (y t) (y t)) / t < L + 1 :=
    htend.eventually (eventually_lt_nhds (by linarith [Real.sqrt_nonneg (Submission.ChartConnection.chartGram
      (I := I) x₀ ((extChartAt I x₀).symm (u 0)) (deriv y 0) (deriv y 0))]))
  rw [eventually_nhdsWithin_iff] at hbound
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp hbound
  set δ : ℝ := min (ε / 2) (ρ / 2) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact lt_min (by linarith) (by linarith)
  have hδε : δ ≤ ε / 2 := by rw [hδdef]; exact min_le_left _ _
  have hδρ : δ ≤ ρ / 2 := by rw [hδdef]; exact min_le_right _ _
  refine ⟨(L + 1) ^ 2 + 1, by positivity, δ, hδpos, ?_⟩
  intro t ht
  have htmem : t ∈ Set.Ioo (0 - ρ) (0 + ρ) := ⟨by linarith [ht.1, hδρ], by linarith [ht.2, hδρ]⟩
  have htball : t ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht.1]
    linarith [ht.2, hδε]
  have hsqrt : Real.sqrt (Submission.ChartConnection.chartGram (I := I) x₀
      ((extChartAt I x₀).symm (u t)) (y t) (y t)) < (L + 1) * t := by
    have h1 := hεsub htball ht.1
    rw [div_lt_iff₀ ht.1] at h1
    linarith
  have hLnn : 0 ≤ L := Real.sqrt_nonneg _
  have hpos : 0 < (L + 1) * t := by nlinarith [ht.1, hLnn]
  have hlt : Submission.ChartConnection.chartGram (I := I) x₀
      ((extChartAt I x₀).symm (u t)) (y t) (y t) < ((L + 1) * t) ^ 2 :=
    (Real.sqrt_lt' hpos).mp hsqrt
  have hconv : Inner.inner ℝ (J t) (J t) = Submission.ChartConnection.chartGram (I := I) x₀
      ((extChartAt I x₀).symm (u t)) (y t) (y t) := by
    rw [Submission.ChartConnection.chartGram_apply]
    rw [← hγeq t htmem, hframe t htmem]
  rw [hconv]
  nlinarith [hlt, sq_nonneg t, sq_nonneg (L + 1)]


end Aux

/-- **The logarithmic derivative of the modulus of a Jacobi field is bounded below by the model
`√K * cot (√K * ·)`** (Rauch comparison, Riccati form). -/
theorem jacobi_modulus_log_deriv_lower
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [T2Space M] [CompactSpace M] [Nontrivial E]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {K d : ℝ} (hK : 0 < K) (hcurv : Submission.RauchK.CurvLe cov K)
    (hd : 0 < d) (hKd : Real.sqrt K * d < Real.pi)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ) I ∞ γ)
    (hunit : ∀ t, ‖Submission.Geodesic.curveVelocity (I := I) γ t‖ = 1)
    {Z : (t : ℝ) → TangentSpace I (γ t)}
    (hZs : ∀ t, Submission.JacobiGlobal.SmoothAlongAt (I := I) γ Z t)
    (hjac : ∀ t, Submission.RauchGlobal.IsJacobiAt cov γ Z t)
    (hZ0 : Z 0 = 0) :
    Real.sqrt K * Real.cot (Real.sqrt K * d) * Inner.inner ℝ (Z d) (Z d)
      ≤ Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov Z d) (Z d) := by
  have hc : 0 < Real.sqrt K := Real.sqrt_pos_of_pos hK
  have hne : ∀ t : ℝ, Submission.Geodesic.curveVelocity (I := I) γ t ≠ 0 :=
    fun t => norm_ne_zero_iff.mp (by rw [hunit t]; norm_num)
  -- the comparison runs on the slightly larger interval `(0, d + ε)`
  have hdπ : d < Real.pi / Real.sqrt K := by
    rw [lt_div_iff₀ hc]
    rwa [mul_comm] at hKd
  set ε : ℝ := (Real.pi / Real.sqrt K - d) / 2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  have hTpos : 0 < d + ε := by linarith
  have hcT : Real.sqrt K * (d + ε) ≤ Real.pi := by
    have h2 : Real.sqrt K * (d + ε) = (Real.pi + Real.sqrt K * d) / 2 := by
      rw [hεdef]
      field_simp
      ring
    rw [h2]
    linarith [hKd]
  by_cases hZd : Z d = 0
  · rw [hZd, inner_zero_left, inner_zero_right, mul_zero]
  · -- the curvature bound, in the form needed by the scalar Riccati comparison
    have hq : ∀ t ∈ Set.Ioo 0 (d + ε),
        Inner.inner ℝ (Submission.CurvatureVec.curvVec cov (γ t) (Z t)
          (Submission.Geodesic.curveVelocity (I := I) γ t)
          (Submission.Geodesic.curveVelocity (I := I) γ t)) (Z t)
        ≤ (Real.sqrt K) ^ 2 * Inner.inner ℝ (Z t) (Z t) := by
      intro t _
      have h1 := Submission.RauchK.curvFormVec_le_mul_of_curvLe (cov := cov)
        (inferInstance : ContMDiffCovariantDerivative cov ∞) hmet hcurv hK.le
        (γ t) (Z t) (Submission.Geodesic.curveVelocity (I := I) γ t)
      rw [hunit t] at h1
      have h2 : K * ‖Z t‖ ^ 2 * (1 : ℝ) ^ 2 = K * ‖Z t‖ ^ 2 := by ring
      rw [h2] at h1
      rw [← real_inner_self_eq_norm_sq (Z t)] at h1
      rw [← Submission.CurvatureVec.inner_curvVec_self (cov := cov)
        (inferInstance : ContMDiffCovariantDerivative cov ∞) (γ t) (Z t)
        (Submission.Geodesic.curveVelocity (I := I) γ t), ← Real.sq_sqrt hK.le] at h1
      exact h1
    have hcot := jml_cot_bound_of_data
      (g := fun t : ℝ => Inner.inner ℝ (Z t) (Z t))
      (f := fun t : ℝ => Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov Z t) (Z t))
      (F := fun t : ℝ => Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov Z t)
        (Submission.JacobiGlobal.covAlong cov Z t))
      (q := fun t : ℝ => Inner.inner ℝ (Submission.CurvatureVec.curvVec cov (γ t) (Z t)
        (Submission.Geodesic.curveVelocity (I := I) γ t)
        (Submission.Geodesic.curveVelocity (I := I) γ t)) (Z t))
      (c := Real.sqrt K) (T := d + ε) (d := d) hc hTpos hcT ⟨hd, by linarith⟩
      (fun t _ => real_inner_self_nonneg)
      (fun t _ hz => by rw [inner_self_eq_zero.mp hz, inner_zero_right])
      (fun t _ => jml_hasDerivAt_inner_self (cov := cov) hmet htor hγ hjac hne t)
      (fun t _ => jml_hasDerivAt_inner_covAlong (cov := cov) hmet htor hγ hjac hne t)
      (fun t _ => by rw [sq]; exact real_inner_mul_inner_self_le _ _)
      (fun t ht => hq t ht)
      (jml_inner_self_le_mul_sq (cov := cov) hmet htor hγ hjac hZ0)
    exact hcot

end Work.Diff.C
