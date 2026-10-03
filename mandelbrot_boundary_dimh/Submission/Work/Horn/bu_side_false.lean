import Mathlib
import Submission.Work.Horn.horn_chart
import Submission.Work.Horn.top_section_exists
import Submission.Work.Horn.pushdown_self

/-!
# `Work.Horn.bu_side_false`

The "upper side" data of Shishikura's §5 cannot hold.

Suppose `Bu` is open, simply connected and `T`-invariant, contains the upper half plane
`{η < Im}` and is contained in `{Im ≥ -η}`, lies in `d.DE`, the map `x ↦ d.E x` is a covering over
`ℂ ∖ (v + ℤ)`, the class `v + ℤ` misses `Bu` (so `Bu` sits inside the base of the covering), and
every `π`-fibre of `d.E` over `Bu` is infinite.  Then we get a contradiction:

* By `top_section_exists` there is a holomorphic section `s` of `E = d.E` over the simply connected
  base `Bu` which is `T`-equivariant and asymptotically the identity at the upper end
  (`s y - y → 0`).
* By `pushdown_self`, the pushdown `S = pushdown s` is holomorphic on the bounded domain
  `Ω = {0} ∪ π(Bu)` with `S 0 = 0` and `S'(0) = 1`, and it maps `Ω` into itself.
* The pushdown `g = pushdown d.E` of the horn map satisfies `g ∘ S = id` on `Ω`, and `g` maps `Ω`
  onto `ℂ` (infinite fibres).  Cartan's theorem at the fixed point `0` with `‖S'(0)‖ = 1` makes `S`
  surjective, so `g '' Ω ⊆ Ω`, hence `Ω = ℂ`; but `Ω` is bounded (it lies in `{|ζ| ≤ e^{2πη}}`),
  contradiction.
-/

noncomputable section

open MandelDim Filter Topology Metric Set
open scoped Topology

namespace Work.Horn

theorem bu_side_false (f₀ : ℂ → ℂ) (D₀ : Set ℂ) (d : MandelDim.ParabData f₀ D₀)
    (Bu : Set ℂ) (η : ℝ) (v : ℂ)
    (hη : 0 < η) (hBuO : IsOpen Bu) (hBuS : SimplyConnectedSpace Bu)
    (htBu : MandelDim.IsTInvariant Bu)
    (hup : {w : ℂ | η < w.im} ⊆ Bu) (hlow : ∀ w ∈ Bu, -η ≤ w.im)
    (hsub : Bu ⊆ d.DE)
    (hcov : IsCoveringMapOn (fun x : Bu => d.E x) {y | ∀ k : ℤ, y ≠ v + k})
    (hnoV : ∀ k : ℤ, v + k ∉ Bu)
    (hinf : ∀ y : ℂ, (MandelDim.piExp '' {w : ℂ | w ∈ Bu ∧ d.E w = y}).Infinite) :
    False := by
  -- the asymptotically identity, `T`-equivariant section of `E` over the simply connected `Bu`
  obtain ⟨s, hsdiff, hsec, hTeq, hasymp⟩ :=
    top_section_exists d Bu η v hη hBuO hBuS htBu hup hlow hsub hcov hnoV hinf
  have hsm : ∀ y ∈ Bu, s y ∈ Bu := fun y hy => (hsec y hy).1
  have hEs : ∀ y ∈ Bu, d.E (s y) = y := fun y hy => (hsec y hy).2
  -- the pushed-down section
  obtain ⟨hSdiff, hSderiv⟩ := pushdown_self hη hBuO htBu hup hsdiff hTeq hasymp
  set S : ℂ → ℂ := MandelDim.pushdown s with hSdef
  set Ω : Set ℂ := hornDu Bu with hΩdef
  have hS0 : S 0 = 0 := MandelDim.pushdown_zero s
  -- `S` is a self-map of `Ω = {0} ∪ π(Bu)`
  have hSmaps : MapsTo S Ω Ω := by
    intro ζ hζ
    rw [hΩdef] at hζ ⊢
    rcases Set.mem_insert_iff.mp hζ with rfl | ⟨y, hy, rfl⟩
    · rw [hS0]
      exact Set.mem_insert _ _
    · rw [hSdef, MandelDim.pushdown_piExp htBu (fun w hw _ => hTeq w hw) hy]
      exact Set.mem_insert_of_mem _ ⟨s y, hsm y hy, rfl⟩
  -- the pushdown `g = hornG d` of the horn map is a left inverse of `S` on `Ω`
  have hsecS : ∀ ζ ∈ Ω, hornG d (S ζ) = ζ := by
    intro ζ hζ
    rw [hΩdef] at hζ
    rcases Set.mem_insert_iff.mp hζ with rfl | ⟨y, hy, rfl⟩
    · rw [hS0]
      exact hornG_zero d
    · rw [hSdef, MandelDim.pushdown_piExp htBu (fun w hw _ => hTeq w hw) hy,
        hornG_piExp d htBu htBu (fun w hw => hsub (by rwa [Set.union_self] at hw)) (Or.inl (hsm y hy)),
        hEs y hy]
  -- `Ω` is open, bounded and preconnected, with `0 ∈ Ω`
  have hopen : IsOpen Ω := by
    rw [hΩdef]; exact isOpen_hornDu hBuO hup
  have hbdd : Bornology.IsBounded Ω := by
    rw [hΩdef, Metric.isBounded_iff_subset_closedBall (0 : ℂ)]
    refine ⟨Real.exp (2 * Real.pi * η), ?_⟩
    intro ζ hζ
    rcases Set.mem_insert_iff.mp hζ with rfl | ⟨w, hw, rfl⟩
    · exact mem_closedBall_self (Real.exp_pos _).le
    · rw [mem_closedBall_zero_iff, norm_piExp]
      exact Real.exp_le_exp.mpr (by have := hlow w hw; nlinarith [Real.pi_pos])
  have h0cl : (0 : ℂ) ∈ closure (MandelDim.piExp '' Bu) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hpi2 : (0 : ℝ) < 2 * Real.pi := by positivity
    set T : ℝ := max η 0 + max 1 (-(Real.log ε) / (2 * Real.pi)) + 1 with hTdef
    have hηT : η < T := by
      rw [hTdef]
      have h1 : η ≤ max η 0 := le_max_left _ _
      have h2 : (1 : ℝ) ≤ max 1 (-(Real.log ε) / (2 * Real.pi)) := le_max_left _ _
      linarith
    have hlogT : -(2 * Real.pi) * T < Real.log ε := by
      have h1 : -(Real.log ε) / (2 * Real.pi) ≤ max 1 (-(Real.log ε) / (2 * Real.pi)) :=
        le_max_right _ _
      have h2 : (0 : ℝ) ≤ max η 0 := le_max_right _ _
      have h3 : -(Real.log ε) / (2 * Real.pi) < T := by
        have hA : (0 : ℝ) ≤ max η 0 := le_max_right _ _
        have hB : -(Real.log ε) / (2 * Real.pi)
            ≤ max 1 (-(Real.log ε) / (2 * Real.pi)) := le_max_right _ _
        rw [hTdef]
        linarith
      have h4 : -(Real.log ε) < (2 * Real.pi) * T := by
        have h5 : 2 * Real.pi * (-(Real.log ε) / (2 * Real.pi)) < 2 * Real.pi * T :=
          mul_lt_mul_of_pos_left h3 hpi2
        rwa [mul_div_cancel₀ _ (ne_of_gt hpi2)] at h5
      linarith only [h4]
    refine ⟨MandelDim.piExp (((T : ℝ) : ℂ) * Complex.I), ⟨((T : ℝ) : ℂ) * Complex.I, ?_, rfl⟩, ?_⟩
    · -- the lift is in `Bu`
      have hmem : η < ((((T : ℝ) : ℂ) * Complex.I)).im := by
        rw [Complex.mul_I_im, Complex.ofReal_re]
        exact hηT
      exact hup hmem
    · -- and its image is close to `0`
      rw [dist_zero_left, norm_piExp, Complex.mul_I_im, Complex.ofReal_re]
      rw [← Real.exp_log (x := ε) hε]
      exact Real.exp_lt_exp.mpr hlogT
  have hpcImg : IsPreconnected (MandelDim.piExp '' Bu) := by
    haveI := hBuS
    have hbu : IsPreconnected Bu := by
      have h1 : IsPathConnected (univ : Set Bu) := isPathConnected_univ
      have h2 : IsPreconnected (Subtype.val '' (univ : Set Bu)) :=
        (h1.isConnected.isPreconnected).image Subtype.val continuous_subtype_val.continuousOn
      rwa [Subtype.coe_image_univ] at h2
    exact hbu.image _ (continuous_piExp.continuousOn)
  have hconn : IsPreconnected Ω := by
    rw [hΩdef]
    refine hpcImg.subset_closure (Set.subset_insert _ _) ?_
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact h0cl
    · exact subset_closure hz
  -- Cartan at the fixed point `0`, where `S'(0) = 1`
  have hcartan := Work.L62.cartan hopen hbdd hconn hSdiff hSmaps (Set.mem_insert _ _) hS0
  have hnorm : ‖deriv S 0‖ = 1 := by
    rw [hSdef, hSderiv.deriv]
    norm_num
  have hsurjS : SurjOn S Ω Ω := (hcartan.2 hnorm).1
  -- the pushdown of the horn map is onto
  have honto : hornG d '' Ω = univ := by
    rw [hΩdef]
    exact surjOn_hornG_hornDu d htBu htBu (fun w hw => hsub (by rwa [Set.union_self] at hw)) hinf
  -- hence it maps `Ω` into itself
  have hsubimg : hornG d '' Ω ⊆ Ω := by
    rintro ζ ⟨w, hw, rfl⟩
    have himg : S '' Ω = Ω := SurjOn.image_eq_of_mapsTo hsurjS (fun u hu => hSmaps hu)
    have hwΩ : w ∈ S '' Ω := by rw [himg]; exact hw
    obtain ⟨u, hu, huw⟩ := hwΩ
    rw [← huw, hsecS u hu]
    exact hu
  have huniv : Ω = univ := Set.eq_univ_of_univ_subset (by rw [← honto]; exact hsubimg)
  -- but `Ω` is bounded
  have hbdd' : Bornology.IsBounded (univ : Set ℂ) := by rw [← huniv]; exact hbdd
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hbdd'
  have h0r : (0 : ℝ) ≤ r := by
    have h := hr (Set.mem_univ (0 : ℂ))
    simpa [Metric.mem_closedBall, dist_eq_norm] using h
  have hmr : ‖((r + 1 : ℝ) : ℂ)‖ ≤ r := by
    have h := hr (Set.mem_univ ((r + 1 : ℝ) : ℂ))
    simpa [Metric.mem_closedBall, dist_eq_norm] using h
  have hpos : (0 : ℝ) < r + 1 := by linarith
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos] at hmr
  linarith

end Work.Horn
