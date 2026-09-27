import Mathlib
import Submission.Work.ManifoldParity.Defs
import Submission.Work.ManifoldParity.curve_tangent_chart
import Submission.Work.ManifoldParity.coord_fderiv_ne_zero
import Submission.Work.ManifoldParity.exists_Ioo_subset_image_of_hasStrictDerivAt
import Submission.Work.ManifoldParity.fderiv_eq_of_eq_of_periodic
import Submission.Work.ManifoldParity.isClosed_range_of_periodic

/-!
# A continuous non-vanishing tangent field from a family of closed curves

Let `K ⊆ ℝⁿ` be a set which is locally the graph of a smooth function over some coordinate axis
(`HasLocalGraphCharts K`), and suppose `K` is covered by finitely many smooth closed curves
`γ j : ℝ → ℝⁿ` with non-vanishing velocity, period `T j > 0`, and `γ j` injective modulo its
period.  Then `K` carries a continuous non-vanishing field which is tangent to `K` in the strong
chartwise sense (`IsTangentField K V`).

The field is built as follows.  Each curve `γ j` determines a field on its own range
(`curveField`): at `x = γ j t` put `γ j'(t)`.  This is well defined because two parameters of the
same point differ by an integer multiple of the period, and the derivative of a periodic function
is periodic; it is continuous on `range (γ j)` because the local structure of `K` along the curve
(`exists_open_nhds_param_of_range`) identifies `K` near a point of the curve with the image of a
neighbourhood of the parameter.  Finally each `x ∈ K` is assigned the field of the curve of
*least* index through `x`; the ranges of the curves are closed (compact), so that index is locally
constant, and the resulting field is continuous, non-vanishing, and tangent.
-/

namespace Work.ManifoldParity

noncomputable section

open Set Function Filter
open scoped Topology

attribute [local instance] Classical.propDecidable

variable {n m : ℕ}

/-- **The curve field of one closed curve.**  At a point `x` of the range of `γ j` this is the
velocity of `γ j` at a parameter of `x`; outside the range it is zero. -/
def curveField (γ : Fin m → ℝ → EuclideanSpace ℝ (Fin n)) (j : Fin m) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
  fun x => if hx : x ∈ Set.range (γ j) then fderiv ℝ (γ j) (Classical.choose hx) 1 else 0

theorem curveField_eq_of_mem (γ : Fin m → ℝ → EuclideanSpace ℝ (Fin n)) (j : Fin m)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Set.range (γ j)) :
    curveField γ j x = fderiv ℝ (γ j) (Classical.choose hx) 1 :=
  dif_pos hx

/-- The curve field is well defined: any parameter of `x` gives the same value. -/
theorem curveField_eq_fderiv (γ : Fin m → ℝ → EuclideanSpace ℝ (Fin n)) (T : Fin m → ℝ)
    (hper : ∀ j, Function.Periodic (γ j) (T j))
    (hsm : ∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (γ j))
    (hinj : ∀ j, ∀ a b : ℝ, γ j a = γ j b → ∃ k : ℤ, a = b + k * T j)
    (j : Fin m) (t : ℝ) : curveField γ j (γ j t) = fderiv ℝ (γ j) t 1 := by
  have hx : γ j t ∈ Set.range (γ j) := ⟨t, rfl⟩
  rw [curveField, dif_pos hx]
  have hch : γ j (Classical.choose hx) = γ j t := Classical.choose_spec hx
  obtain ⟨k, hk⟩ := hinj j _ _ hch
  have hd : ∀ s : ℝ, DifferentiableAt ℝ (γ j) s :=
    fun s => (hsm j).differentiable (by simp) s
  have h := fderiv_eq_of_eq_of_periodic (hper j) hd ⟨k, hk⟩
  exact congrArg (fun (L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin n)) => L 1) h

/-- The curve field does not vanish on the range of the curve. -/
theorem curveField_ne_zero (γ : Fin m → ℝ → EuclideanSpace ℝ (Fin n)) (j : Fin m)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Set.range (γ j))
    (hvel : ∀ t, fderiv ℝ (γ j) t 1 ≠ 0) : curveField γ j x ≠ 0 := by
  have h := curveField_eq_of_mem γ j hx
  rw [h]
  exact hvel _

/-- On the range of a curve `γ j` lying in `K`, the curve field is tangent to `K` in the
chartwise sense. -/
theorem curveField_tangent {K : Set (EuclideanSpace ℝ (Fin n))}
    (γ : Fin m → ℝ → EuclideanSpace ℝ (Fin n))
    (hsm : ∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (γ j))
    (hvel : ∀ j t, fderiv ℝ (γ j) t 1 ≠ 0)
    (hγK : ∀ j, ∀ t, γ j t ∈ K) (j : Fin m)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Set.range (γ j))
    (i : Fin n) (U : Set (EuclideanSpace ℝ (Fin n))) (η : ℝ → EuclideanSpace ℝ (Fin n))
    (hchart : IsGraphChart K i U η) (hxU : x ∈ U) :
    ∃ c : ℝ, c ≠ 0 ∧ curveField γ j x
      = c • (EuclideanSpace.single i (1 : ℝ) + (fderiv ℝ η (x i)) (1 : ℝ)) := by
  have hxs : γ j (Classical.choose hx) = x := Classical.choose_spec hx
  have hγU : γ j (Classical.choose hx) ∈ U := by rw [hxs]; exact hxU
  obtain ⟨c, hc, hce⟩ := curve_tangent_chart K i U η hchart (γ j) (hsm j) (hγK j)
    (Classical.choose hx) hγU (hvel j _)
  rw [curveField_eq_of_mem γ j hx, hce,
    show (γ j (Classical.choose hx)) i = x i from congrArg (fun v => v i) hxs]
  exact ⟨c, hc, rfl⟩

/-- **Local surjectivity of a curve in a locally-graph set, with control of the parameter.**
For every `t₀` and every `ε > 0` there is an open neighbourhood `O` of `γ t₀` such that every
`y ∈ K ∩ O` is `γ s` for some `s` with `|s - t₀| < ε`. -/
theorem exists_open_nhds_param_of_range {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hgra : HasLocalGraphCharts K) {γ : ℝ → EuclideanSpace ℝ (Fin n)}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hvel : ∀ t, fderiv ℝ γ t 1 ≠ 0) (hγK : ∀ t, γ t ∈ K) :
    ∀ t₀ : ℝ, ∀ ε > 0, ∃ O : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen O ∧ γ t₀ ∈ O ∧ ∀ y ∈ K ∩ O, ∃ s : ℝ, |s - t₀| < ε ∧ γ s = y := by
  intro t₀ ε hε
  obtain ⟨i, U, η, hchart, hxU⟩ := hgra (γ t₀) (hγK t₀)
  obtain ⟨c, hc, hceq⟩ :=
    curve_tangent_chart K i U η hchart γ hsm hγK t₀ hxU (hvel t₀)
  have hUo : IsOpen U := hchart.1
  have hηsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η := hchart.2.1
  have hηi : ∀ t, η t i = 0 := hchart.2.2.1
  have hgr : ∀ y ∈ U, (y ∈ K ↔ y = gmap i η (y i)) := hchart.2.2.2
  have hγc : Continuous γ := hsm.continuous
  set ℓ : ℝ → ℝ := fun s => (γ s) i with hℓdef
  -- near `t₀`, `γ` is the graph map composed with its `i`-th coordinate
  have hev : ∀ᶠ s in 𝓝 t₀, γ s = gmap i η (ℓ s) := by
    have h1 : ∀ᶠ s in 𝓝 t₀, γ s ∈ U := hγc.continuousAt (hUo.mem_nhds hxU)
    filter_upwards [h1] with s hs
    have h := (hgr (γ s) hs).mp (hγK s)
    simpa [hℓdef] using h
  obtain ⟨Vg, hVgmem, hVgsub⟩ := Filter.eventually_iff_exists_mem.mp hev
  obtain ⟨δ', hδ'pos, hδ'sub⟩ := Metric.mem_nhds_iff.mp hVgmem
  -- the chart coordinate is smooth with non-vanishing derivative at `t₀`
  have hℓsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ℓ := by
    have h1 : ℓ = (fun v : EuclideanSpace ℝ (Fin n) => v i) ∘ γ := by
      funext s; simp [hℓdef]
    rw [h1]
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i).contDiff.comp hsm
  have hℓderiv : deriv ℓ t₀ = ((fderiv ℝ γ t₀) 1) i := by
    have h1 : ℓ = (fun v : EuclideanSpace ℝ (Fin n) => v i) ∘ γ := by
      funext s; simp [hℓdef]
    have hproj_eq : (fun v : EuclideanSpace ℝ (Fin n) => v i)
        = ⇑(PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i) := by
      funext v; rw [PiLp.proj_apply]
    have h2 : fderiv ℝ ℓ t₀
        = (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i).comp (fderiv ℝ γ t₀) := by
      rw [h1, hproj_eq]
      exact ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i).hasFDerivAt.comp t₀
        ((hsm.contDiffAt).differentiableAt (by simp)).hasFDerivAt).fderiv
    rw [(fderiv_apply_one_eq_deriv (f := ℓ) (x := t₀)).symm, h2,
      ContinuousLinearMap.comp_apply, PiLp.proj_apply]
  have hne : deriv ℓ t₀ ≠ 0 := by
    rw [hℓderiv]
    exact coord_fderiv_ne_zero hchart hsm hγK hxU (hvel t₀)
  have hstr : HasStrictDerivAt ℓ (deriv ℓ t₀) t₀ := hℓsm.hasStrictDerivAt (by simp)
  -- `ℓ` maps a small interval around `t₀` onto a neighbourhood of `ℓ t₀`
  have hε'pos : 0 < min ε δ' := lt_min hε hδ'pos
  obtain ⟨δ, hδpos, hδsub⟩ :=
    exists_Ioo_subset_image_of_hasStrictDerivAt hstr hne hε'pos
  refine ⟨U ∩ {y : EuclideanSpace ℝ (Fin n) | y i ∈ Set.Ioo (ℓ t₀ - δ) (ℓ t₀ + δ)},
    hUo.inter (isOpen_Ioo.preimage (by fun_prop)), ⟨hxU, ?_⟩, ?_⟩
  · rw [hℓdef]
    exact ⟨by linarith, by linarith⟩
  · rintro y ⟨hyK, hyJ⟩
    obtain ⟨hyU, hyJ⟩ := hyJ
    obtain ⟨s, hsIoo, hsℓ⟩ := hδsub hyJ
    have habs : |s - t₀| < min ε δ' :=
      abs_lt.mpr ⟨by linarith [hsIoo.1], by linarith [hsIoo.2]⟩
    refine ⟨s, by linarith [habs, min_le_left ε δ'], ?_⟩
    have hsVg : s ∈ Vg := hδ'sub (by
      rw [Metric.mem_ball, Real.dist_eq]
      linarith [habs, min_le_right ε δ'])
    rw [hVgsub s hsVg, hsℓ]
    exact ((hgr y hyU).mp hyK).symm

/-- **The curve field is continuous on the range of the curve.** -/
theorem curveField_continuousOn {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hgra : HasLocalGraphCharts K) (γ : Fin m → ℝ → EuclideanSpace ℝ (Fin n))
    (T : Fin m → ℝ) (hper : ∀ j, Function.Periodic (γ j) (T j))
    (hsm : ∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (γ j))
    (hvel : ∀ j t, fderiv ℝ (γ j) t 1 ≠ 0)
    (hinj : ∀ j, ∀ a b : ℝ, γ j a = γ j b → ∃ k : ℤ, a = b + k * T j)
    (hγK : ∀ j, ∀ t, γ j t ∈ K) (j : Fin m) :
    ContinuousOn (curveField γ j) (Set.range (γ j)) := by
  intro x₀ hx₀
  obtain ⟨t₀, ht₀⟩ := hx₀
  have hx₀O₀ : x₀ ∈ Set.range (γ j) := ⟨t₀, ht₀⟩
  have hFcont : Continuous fun t : ℝ => fderiv ℝ (γ j) t 1 :=
    ((hsm j).continuous_fderiv (by simp)).clm_apply continuous_const
  rw [Metric.continuousWithinAt_iff']
  intro η hη
  obtain ⟨ε, hεpos, hεsub⟩ :=
    Metric.mem_nhds_iff.mp ((Metric.continuousAt_iff'.mp hFcont.continuousAt) η hη)
  obtain ⟨O, hOo, hx₀O, hOsub⟩ :=
    exists_open_nhds_param_of_range K hgra (hsm j) (hvel j) (hγK j) t₀ ε hεpos
  have hx₀O' : x₀ ∈ O := by rw [← ht₀]; exact hx₀O
  refine Filter.mem_of_superset (Filter.inter_mem self_mem_nhdsWithin
    (mem_nhdsWithin_of_mem_nhds (hOo.mem_nhds hx₀O'))) ?_
  rintro x ⟨hxrange, hxO⟩
  have hxK : x ∈ K := by
    obtain ⟨u, hu⟩ := hxrange
    rw [← hu]; exact hγK j u
  obtain ⟨s, hsε, hsr⟩ := hOsub x ⟨hxK, hxO⟩
  have h1 : curveField γ j x = fderiv ℝ (γ j) s 1 := by
    rw [← hsr]; exact curveField_eq_fderiv γ T hper hsm hinj j s
  have h2 : curveField γ j x₀ = fderiv ℝ (γ j) t₀ 1 := by
    rw [← ht₀]; exact curveField_eq_fderiv γ T hper hsm hinj j t₀
  change dist (curveField γ j x) (curveField γ j x₀) < η
  rw [h1, h2]
  exact hεsub (by rw [Metric.mem_ball, Real.dist_eq]; exact hsε)

variable {K : Set (EuclideanSpace ℝ (Fin n))}

/-- The least index of a curve through `x`. -/
theorem exists_min_curveIdx (γ : Fin m → ℝ → EuclideanSpace ℝ (Fin n))
    (hsurj : ∀ x ∈ K, ∃ j t, γ j t = x) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ K) :
    ∃ j : Fin m, x ∈ Set.range (γ j) ∧ ∀ j' : Fin m, x ∈ Set.range (γ j') → j ≤ j' := by
  have hne : (Finset.univ.filter (fun j : Fin m => x ∈ Set.range (γ j))).Nonempty := by
    obtain ⟨j, t, ht⟩ := hsurj x hx
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, ⟨t, ht⟩⟩⟩
  refine ⟨(Finset.univ.filter (fun j : Fin m => x ∈ Set.range (γ j))).min' hne, ?_, ?_⟩
  · simpa using (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2
  · intro j' hj'
    exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ j', hj'⟩)

/-- The index of a curve through `x`: the least `j` with `x ∈ range (γ j)`. -/
def curveIdx (γ : Fin m → ℝ → EuclideanSpace ℝ (Fin n))
    (hsurj : ∀ x ∈ K, ∃ j t, γ j t = x) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ K) : Fin m :=
  Classical.choose (exists_min_curveIdx γ hsurj x hx)

theorem curveIdx_mem (γ : Fin m → ℝ → EuclideanSpace ℝ (Fin n))
    (hsurj : ∀ x ∈ K, ∃ j t, γ j t = x) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ K) :
    x ∈ Set.range (γ (curveIdx γ hsurj x hx)) :=
  (Classical.choose_spec (exists_min_curveIdx γ hsurj x hx)).1

theorem curveIdx_le (γ : Fin m → ℝ → EuclideanSpace ℝ (Fin n))
    (hsurj : ∀ x ∈ K, ∃ j t, γ j t = x) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ K)
    {j : Fin m} (hj : x ∈ Set.range (γ j)) : curveIdx γ hsurj x hx ≤ j :=
  (Classical.choose_spec (exists_min_curveIdx γ hsurj x hx)).2 j hj

/-- The field obtained by choosing, at each point of `K`, the curve of least index through it. -/
def tanField (γ : Fin m → ℝ → EuclideanSpace ℝ (Fin n))
    (hsurj : ∀ x ∈ K, ∃ j t, γ j t = x) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
  fun x => if hx : x ∈ K then curveField γ (curveIdx γ hsurj x hx) x else 0

theorem tanField_eq (γ : Fin m → ℝ → EuclideanSpace ℝ (Fin n))
    (hsurj : ∀ x ∈ K, ∃ j t, γ j t = x) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ K) :
    tanField γ hsurj x = curveField γ (curveIdx γ hsurj x hx) x :=
  dif_pos hx

theorem tanField_ne_zero (γ : Fin m → ℝ → EuclideanSpace ℝ (Fin n))
    (hsurj : ∀ x ∈ K, ∃ j t, γ j t = x) (hvel : ∀ j t, fderiv ℝ (γ j) t 1 ≠ 0)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ K) : tanField γ hsurj x ≠ 0 := by
  rw [tanField_eq γ hsurj x hx]
  exact curveField_ne_zero γ _ (curveIdx_mem γ hsurj x hx) (hvel _)

/-- The chosen field is continuous on `K`. -/
theorem tanField_continuousOn (hgra : HasLocalGraphCharts K)
    (γ : Fin m → ℝ → EuclideanSpace ℝ (Fin n)) (T : Fin m → ℝ) (hT : ∀ j, 0 < T j)
    (hsm : ∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (γ j))
    (hper : ∀ j, Function.Periodic (γ j) (T j))
    (hvel : ∀ j t, fderiv ℝ (γ j) t 1 ≠ 0)
    (hinj : ∀ j, ∀ a b : ℝ, γ j a = γ j b → ∃ k : ℤ, a = b + k * T j)
    (hcover : ∀ j, ∀ t, γ j t ∈ K) (hsurj : ∀ x ∈ K, ∃ j t, γ j t = x) :
    ContinuousOn (tanField γ hsurj) K := by
  intro x₀ hx₀
  set j₀ : Fin m := curveIdx γ hsurj x₀ hx₀ with hj₀def
  have hx₀j : x₀ ∈ Set.range (γ j₀) := curveIdx_mem γ hsurj x₀ hx₀
  -- the open set avoiding the curves of index `< j₀`
  have hO₂open : IsOpen
      {y : EuclideanSpace ℝ (Fin n) | ∀ j : Fin m, j < j₀ → y ∉ Set.range (γ j)} := by
    have h1 : {y : EuclideanSpace ℝ (Fin n) | ∀ j : Fin m, j < j₀ → y ∉ Set.range (γ j)}
        = ⋂ j : Fin m, (if j < j₀ then (Set.range (γ j))ᶜ else Set.univ) := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      constructor
      · intro h j
        by_cases hj : j < j₀
        · simp only [hj, if_pos]; exact h j hj
        · simp only [hj, if_false]; exact Set.mem_univ y
      · intro h j hj
        have := h j
        rwa [if_pos hj] at this
    rw [h1]
    refine isOpen_iInter_of_finite fun j => ?_
    by_cases hj : j < j₀
    · rw [if_pos hj]
      exact (isClosed_range_of_periodic (hT j) (hsm j).continuous (hper j)).isOpen_compl
    · rw [if_neg hj]; exact isOpen_univ
  have hx₀O₂ : x₀ ∈
      {y : EuclideanSpace ℝ (Fin n) | ∀ j : Fin m, j < j₀ → y ∉ Set.range (γ j)} := by
    intro j hj hjmem
    have hle : curveIdx γ hsurj x₀ hx₀ ≤ j := curveIdx_le γ hsurj x₀ hx₀ hjmem
    rw [← hj₀def] at hle
    exact absurd hle (not_le.mpr hj)
  -- a neighbourhood of `x₀` inside the curve of index `j₀`
  obtain ⟨O₁, hO₁o, hx₀O₁, hO₁sub⟩ :=
    exists_open_nhds_param_of_range K hgra (hsm j₀) (hvel j₀) (hcover j₀)
      (Classical.choose hx₀j) 1 (by norm_num)
  have hx₀O₁' : x₀ ∈ O₁ := by rw [← Classical.choose_spec hx₀j]; exact hx₀O₁
  have hKO₁ : K ∩ O₁ ⊆ Set.range (γ j₀) := by
    rintro y ⟨hyK, hyO⟩
    obtain ⟨s, -, hsr⟩ := hO₁sub y ⟨hyK, hyO⟩
    exact ⟨s, hsr⟩
  set O : Set (EuclideanSpace ℝ (Fin n)) :=
    O₁ ∩ {y : EuclideanSpace ℝ (Fin n) | ∀ j : Fin m, j < j₀ → y ∉ Set.range (γ j)} with hOdef
  have hOo : IsOpen O := hO₁o.inter hO₂open
  have hx₀O : x₀ ∈ O := ⟨hx₀O₁', hx₀O₂⟩
  -- on `K ∩ O` the index is constantly `j₀`
  have heq : tanField γ hsurj =ᶠ[𝓝[K] x₀] curveField γ j₀ := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨K ∩ O, Filter.inter_mem self_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (hOo.mem_nhds hx₀O)), ?_⟩
    rintro y ⟨hyK, hyO⟩
    obtain ⟨hyO₁, hyO₂⟩ := hyO
    have hyj : curveIdx γ hsurj y hyK = j₀ := by
      obtain ⟨s, -, hsr⟩ := hO₁sub y ⟨hyK, hyO₁⟩
      refine le_antisymm (curveIdx_le γ hsurj y hyK ⟨s, hsr⟩) ?_
      by_contra hlt
      exact hyO₂ (curveIdx γ hsurj y hyK) (not_le.mp hlt) (curveIdx_mem γ hsurj y hyK)
    rw [tanField_eq γ hsurj y hyK, hyj]
  -- glue
  have hcont : ContinuousWithinAt (curveField γ j₀) K x₀ :=
    (curveField_continuousOn K hgra γ T hper hsm hvel hinj hcover j₀ x₀ hx₀j).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Filter.inter_mem self_mem_nhdsWithin
        (mem_nhdsWithin_of_mem_nhds (hO₁o.mem_nhds hx₀O₁'))) hKO₁)
  exact hcont.congr_of_eventuallyEq_of_mem heq hx₀

/-- The chosen field is tangent to `K` in the chartwise sense. -/
theorem tanField_isTangentField
    (γ : Fin m → ℝ → EuclideanSpace ℝ (Fin n))
    (hsm : ∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (γ j))
    (hvel : ∀ j t, fderiv ℝ (γ j) t 1 ≠ 0)
    (hcover : ∀ j, ∀ t, γ j t ∈ K) (hsurj : ∀ x ∈ K, ∃ j t, γ j t = x) :
    IsTangentField K (tanField γ hsurj) := by
  intro x hx i U η hchart hxU
  rw [tanField_eq γ hsurj x hx]
  exact curveField_tangent γ hsm hvel hcover (curveIdx γ hsurj x hx)
    (curveIdx_mem γ hsurj x hx) i U η hchart hxU

theorem exists_tangentField_of_closed_curves {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hgra : HasLocalGraphCharts K)
    {m : ℕ} (γ : Fin m → ℝ → EuclideanSpace ℝ (Fin n)) (T : Fin m → ℝ)
    (hT : ∀ j, 0 < T j) (hsm : ∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (γ j))
    (hper : ∀ j, Function.Periodic (γ j) (T j))
    (hvel : ∀ j t, fderiv ℝ (γ j) t 1 ≠ 0)
    (hinj : ∀ j, ∀ a b : ℝ, γ j a = γ j b → ∃ k : ℤ, a = b + k * T j)
    (hcover : ∀ j, ∀ t, γ j t ∈ K) (hsurj : ∀ x ∈ K, ∃ j t, γ j t = x) :
    ∃ U : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      ContinuousOn U K ∧ (∀ x ∈ K, U x ≠ 0) ∧ IsTangentField K U :=
  ⟨tanField γ hsurj,
    tanField_continuousOn hgra γ T hT hsm hper hvel hinj hcover hsurj,
    fun _ hx => tanField_ne_zero γ hsurj hvel _ hx,
    tanField_isTangentField γ hsm hvel hcover hsurj⟩

end

end Work.ManifoldParity
