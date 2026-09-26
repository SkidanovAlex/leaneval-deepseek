import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Submission.Commons.Topology.Jordan.local_split_transverse

/-
# Local sides of a transverse curve

Target: `Commons.Topology.Jordan.local_sides_of_transverse_curve`.

Helper lemmas proved here (all proved, with no placeholders):

* `eq_of_sub_lt_one` : a continuous `1`-periodic map injective on `[0,1)` is injective on any
  interval of length `< 1` (parameters differing by less than `1`).
* `local_structure` : if `γ` is continuous, `1`-periodic and injective on `[0,1)`, then there is
  `ρ > 0` such that any parameter `t` with `γ t` in the ball `B(γ t₀, ρ)` lies within `1/4` of
  `t₀ + k` for some integer `k`.
* `c1_control` : `ContDiffAt ℝ 1 γ t₀` implies `γ` is (differentiable and) `C¹` on a neighbourhood
  of `t₀`: there is `ε > 0` with `‖deriv γ (t₀+u) - v‖ ≤ ‖v‖/2` for `|u| ≤ ε`.
* `deriv_bound` : the little-o form of differentiability at `t₀`: for every `ε > 0` there is `δ > 0`
  with `‖γ (t₀+u) - γ t₀ - u • v‖ ≤ ε * |u|` for `|u| < δ`.

The remaining work is the local splitting argument (see the plan at the bottom of this file).
-/

open Set Metric
open scoped Topology

namespace Commons.Topology.Jordan

/-- A continuous periodic map, injective on `[0,1)`, separates parameters differing by less than
`1`: if `γ x = γ y` and `|x - y| < 1` then `x = y`. -/
lemma eq_of_sub_lt_one {γ : ℝ → ℂ} (hper : Function.Periodic γ 1)
    (hinj : Set.InjOn γ (Set.Ico (0:ℝ) 1)) {x y : ℝ} (h : γ x = γ y) (hxy : |x - y| < 1) :
    x = y := by
  have hfx : (Int.fract x : ℝ) ∈ Set.Ico (0:ℝ) 1 := ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩
  have hfy : (Int.fract y : ℝ) ∈ Set.Ico (0:ℝ) 1 := ⟨Int.fract_nonneg y, Int.fract_lt_one y⟩
  have hx : γ (Int.fract x) = γ x := by
    rw [← hper.sub_int_mul_eq (x := x) ⌊x⌋, mul_one, Int.self_sub_floor]
  have hy : γ (Int.fract y) = γ y := by
    rw [← hper.sub_int_mul_eq (x := y) ⌊y⌋, mul_one, Int.self_sub_floor]
  have hfe : Int.fract x = Int.fract y := hinj hfx hfy (by rw [hx, hy, h])
  have e1 : x = Int.fract x + (⌊x⌋ : ℝ) := (Int.fract_add_floor x).symm
  have e2 : y = Int.fract y + (⌊y⌋ : ℝ) := (Int.fract_add_floor y).symm
  have hdiff : x - y = (⌊x⌋ : ℝ) - (⌊y⌋ : ℝ) := by linarith
  by_contra hne
  have hfl : ⌊x⌋ ≠ ⌊y⌋ := by
    intro he
    apply hne
    have : x - y = 0 := by rw [hdiff, he]; ring
    linarith
  have ha : (1:ℝ) ≤ |(⌊x⌋ : ℝ) - (⌊y⌋ : ℝ)| := by
    have h2 : ((⌊x⌋ - ⌊y⌋ : ℤ) : ℝ) = (⌊x⌋ : ℝ) - (⌊y⌋ : ℝ) := by push_cast; ring
    have h3 : (1 : ℤ) ≤ |⌊x⌋ - ⌊y⌋| := Int.one_le_abs (sub_ne_zero.mpr hfl)
    have h4 : ((1:ℤ) : ℝ) ≤ ((|⌊x⌋ - ⌊y⌋| : ℤ) : ℝ) := by exact_mod_cast h3
    rw [Int.cast_abs, h2] at h4
    simpa using h4
  rw [hdiff] at hxy
  linarith [abs_nonneg ((⌊x⌋ : ℝ) - (⌊y⌋ : ℝ))]

/-- **Local structure.**  For a continuous `1`-periodic injection on `[0,1)` and a parameter `t₀`,
any parameter whose image lands in a sufficiently small ball around `γ t₀` lies within a fixed
small distance of `t₀ + k` for some integer `k`. -/
lemma local_structure {γ : ℝ → ℂ} (hcont : Continuous γ) (hper : Function.Periodic γ 1)
    (hinj : Set.InjOn γ (Set.Ico (0:ℝ) 1)) (t₀ : ℝ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ t : ℝ,
      γ t ∈ Metric.ball (γ t₀) ρ → ∃ k : ℤ, |t - t₀ - k| < (1/4:ℝ) := by
  classical
  by_contra hcon
  push_neg at hcon
  have hchoose : ∀ n : ℕ, ∃ t : ℝ, γ t ∈ Metric.ball (γ t₀) (1/((n:ℝ)+1)) ∧
      ∀ k : ℤ, (1/4:ℝ) ≤ |t - t₀ - k| := by
    intro n
    have hpos : (0:ℝ) < 1/((n:ℝ)+1) := by positivity
    obtain ⟨t, ht1, ht2⟩ := hcon (1/((n:ℝ)+1)) hpos
    exact ⟨t, ht1, fun k => by have := ht2 k; linarith [this]⟩
  choose t ht mem using hchoose
  set s : ℕ → ℝ := fun n => Int.fract (t n) with hsdef
  have hsIcc : ∀ n, s n ∈ Set.Icc (0:ℝ) 1 := fun n =>
    ⟨Int.fract_nonneg _, le_of_lt (Int.fract_lt_one _)⟩
  have hsval : ∀ n, γ (s n) = γ (t n) := by
    intro n
    rw [hsdef]
    show γ (Int.fract (t n)) = γ (t n)
    rw [← hper.sub_int_mul_eq (x := t n) ⌊t n⌋, mul_one, Int.self_sub_floor]
  obtain ⟨a, haIcc, φ, hφ, htend⟩ := IsCompact.tendsto_subseq isCompact_Icc hsIcc
  have hγa : γ a = γ t₀ := by
    have h1 : Filter.Tendsto (fun n => γ (s (φ n))) Filter.atTop (nhds (γ a)) :=
      (hcont.tendsto a).comp htend
    have h2 : Filter.Tendsto (fun n => γ (s (φ n))) Filter.atTop (nhds (γ t₀)) := by
      have hb : ∀ n, dist (γ (s (φ n))) (γ t₀) ≤ 1/(((φ n : ℕ) : ℝ) + 1) := by
        intro n
        rw [hsval (φ n)]
        exact le_of_lt (ht (φ n))
      have hb2 : Filter.Tendsto (fun n : ℕ => 1/(((φ n : ℕ) : ℝ) + 1)) Filter.atTop (nhds 0) := by
        have hmono : Filter.Tendsto φ Filter.atTop Filter.atTop := hφ.tendsto_atTop
        have hcontr : Filter.Tendsto (fun m : ℕ => 1/((m:ℝ)+1)) Filter.atTop (nhds 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        exact hcontr.comp hmono
      rw [tendsto_iff_dist_tendsto_zero]
      exact squeeze_zero (fun n => dist_nonneg) hb hb2
    exact tendsto_nhds_unique h1 h2
  have ht₀' : (Int.fract t₀ : ℝ) ∈ Set.Ico (0:ℝ) 1 := ⟨Int.fract_nonneg t₀, Int.fract_lt_one t₀⟩
  have hγt₀' : γ (Int.fract t₀) = γ t₀ := by
    rw [← hper.sub_int_mul_eq (x := t₀) ⌊t₀⌋, mul_one, Int.self_sub_floor]
  have hmod : ∃ m : ℤ, a - t₀ = (m : ℝ) := by
    rcases lt_or_eq_of_le haIcc.2 with ha_lt | ha_eq
    · have haIco : a ∈ Set.Ico (0:ℝ) 1 := ⟨haIcc.1, ha_lt⟩
      have hthis : a = Int.fract t₀ := hinj haIco ht₀' (by rw [hγa, hγt₀'])
      refine ⟨-⌊t₀⌋, ?_⟩
      rw [hthis]
      push_cast
      have h := Int.fract_add_floor t₀
      linarith [show (Int.fract t₀ + (⌊t₀⌋:ℝ)) = t₀ from h]
    · have h0eq : γ (0:ℝ) = γ (Int.fract t₀) := by
        rw [hγt₀', ← hγa, ha_eq]
        simpa using (hper 0).symm
      have h0 : (0:ℝ) ∈ Set.Ico (0:ℝ) 1 := ⟨le_refl 0, by norm_num⟩
      have hft : Int.fract t₀ = 0 := (hinj h0 ht₀' h0eq).symm
      refine ⟨1 - ⌊t₀⌋, ?_⟩
      rw [ha_eq]; push_cast
      have h := Int.fract_add_floor t₀
      linarith [show (Int.fract t₀ + (⌊t₀⌋:ℝ)) = t₀ from h]
  obtain ⟨m, hm⟩ := hmod
  have hev : ∀ᶠ n in Filter.atTop, (|s (φ n) - a| < (1/4:ℝ)) := by
    have h1 : Filter.Tendsto (fun n => |s (φ n) - a|) Filter.atTop (nhds 0) := by
      have h2 : Filter.Tendsto (fun n => s (φ n) - a) Filter.atTop (nhds 0) := by
        have := htend; simpa using this.sub_const a
      simpa using h2.abs
    exact (tendsto_order.1 h1).2 _ (by norm_num : (0:ℝ) < 1/4)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  have hk : ∀ n, |t (φ n) - t₀ - ((⌊t (φ n)⌋ + m : ℤ) : ℝ)| = |s (φ n) - a| := by
    intro n
    have e : (t (φ n) : ℝ) - t₀ - ((⌊t (φ n)⌋ + m : ℤ) : ℝ) = s (φ n) - a := by
      have h1 : (t (φ n) : ℝ) = s (φ n) + (⌊t (φ n)⌋ : ℝ) := by
        rw [hsdef]; exact (Int.fract_add_floor (t (φ n))).symm
      have h2 : (m : ℝ) = a - t₀ := hm.symm
      have h3 : ((⌊t (φ n)⌋ + m : ℤ) : ℝ) = (⌊t (φ n)⌋ : ℝ) + (m:ℝ) := by push_cast; ring
      linarith [h1, h2, h3]
    rw [e]
  have hfin := mem (φ N) (⌊t (φ N)⌋ + m)
  rw [hk N] at hfin
  linarith [hN N le_rfl]

/-- **`C¹` control near `t₀`.**  If `γ` is `C¹` at `t₀` with derivative `v ≠ 0`, then on a
neighbourhood of `t₀` the derivative of `γ` stays within `‖v‖/2` of `v`.  (Uses
`ContDiffAt.eventually`, i.e. `ContDiffAt ℝ 1` is a *local* condition.) -/
lemma c1_control {γ : ℝ → ℂ} {v : ℂ} {t₀ : ℝ}
    (hder : ContDiffAt ℝ 1 γ t₀) (hdv : deriv γ t₀ = v) (hv : v ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ (∀ u : ℝ, |u| ≤ ε → DifferentiableAt ℝ γ (t₀+u)) ∧
      (∀ u : ℝ, |u| ≤ ε → ‖deriv γ (t₀+u) - v‖ ≤ ‖v‖/2) := by
  have hev : ∀ᶠ y in nhds t₀, ContDiffAt ℝ 1 γ y := hder.eventually (by simp)
  obtain ⟨ε₀, hε₀pos, hε₀⟩ := Metric.eventually_nhds_iff.mp hev
  set s : Set ℝ := Set.Ioo (t₀ - ε₀) (t₀ + ε₀) with hs
  have hsopen : IsOpen s := isOpen_Ioo
  have hsnhds : s ∈ nhds t₀ := by
    rw [Metric.mem_nhds_iff]
    refine ⟨ε₀, hε₀pos, fun y hy => ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hy
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hcontOn : ContDiffOn ℝ 1 γ s := by
    intro x hx
    have hdist : dist x t₀ < ε₀ := by
      rw [Real.dist_eq, abs_lt]; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact (hε₀ hdist).contDiffWithinAt
  have huniq : UniqueDiffOn ℝ s := hsopen.uniqueDiffOn
  have h1 := (contDiffOn_one_iff_derivWithin huniq).mp hcontOn
  have hcont_deriv : ContinuousOn (deriv γ) s := by
    refine h1.2.congr ?_
    intro x hx
    exact (derivWithin_of_isOpen hsopen hx).symm
  have hcat : ContinuousAt (deriv γ) t₀ := hcont_deriv.continuousAt hsnhds
  have hlim : Filter.Tendsto (fun u : ℝ => deriv γ (t₀+u)) (nhds 0) (nhds (deriv γ t₀)) := by
    have h2 : Filter.Tendsto (fun u : ℝ => t₀ + u) (nhds 0) (nhds t₀) := by
      simpa using tendsto_const_nhds.add (continuous_id.tendsto (0:ℝ))
    exact hcat.tendsto.comp h2
  have h2 : ∀ᶠ u in nhds (0:ℝ), ‖deriv γ (t₀+u) - v‖ < ‖v‖/2 := by
    have hn : Filter.Tendsto (fun u : ℝ => ‖deriv γ (t₀+u) - v‖) (nhds 0) (nhds 0) := by
      have := hlim.sub_const v
      rw [hdv] at this
      simpa using this.norm
    exact (tendsto_order.1 hn).2 _ (by positivity)
  obtain ⟨ε₁, hε₁pos, hε₁⟩ := Metric.eventually_nhds_iff.mp h2
  refine ⟨min (ε₀/2) (ε₁/2), lt_min (by linarith) (by linarith), ?_, ?_⟩
  · intro u hu
    have hm : min (ε₀/2) (ε₁/2) < ε₀ := by
      have := min_le_left (ε₀/2) (ε₁/2); linarith
    have hu₀ : |u| < ε₀ := lt_of_le_of_lt hu hm
    have hdist : dist (t₀+u) t₀ < ε₀ := by rw [Real.dist_eq]; simpa using hu₀
    exact (hε₀ hdist).differentiableAt (by norm_num : (1:WithTop ℕ∞) ≠ 0)
  · intro u hu
    have hm : min (ε₀/2) (ε₁/2) < ε₁ := by
      have := min_le_right (ε₀/2) (ε₁/2); linarith
    have hu₁ : |u| < ε₁ := lt_of_le_of_lt hu hm
    have hd : dist u 0 < ε₁ := by rw [Real.dist_eq]; simpa using hu₁
    exact le_of_lt (hε₁ hd)

/-- **Little-o form of the derivative at `t₀`**: for every `ε > 0` there is `δ > 0` such that
`‖γ (t₀+u) - γ t₀ - u • v‖ ≤ ε * |u|` for `|u| < δ`. -/
lemma deriv_bound {γ : ℝ → ℂ} {v : ℂ} {t₀ : ℝ}
    (hder : ContDiffAt ℝ 1 γ t₀) (hdv : deriv γ t₀ = v) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ u : ℝ,
      |u| < δ → ‖γ (t₀ + u) - γ t₀ - (u:ℂ) * v‖ ≤ ε * |u| := by
  have hh : HasDerivAt γ v t₀ := by
    have h1 := hder.differentiableAt (by norm_num : (1:WithTop ℕ∞) ≠ 0)
    have h2 : HasDerivAt γ (deriv γ t₀) t₀ := h1.hasDerivAt
    rwa [hdv] at h2
  intro ε hε
  have hIo : (fun x => γ x - γ t₀ - (x - t₀) • v) =o[nhds t₀] (fun x => x - t₀) :=
    hh.isLittleO
  rw [Asymptotics.isLittleO_iff] at hIo
  have hev := hIo hε
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδpos, hδ⟩ := hev
  refine ⟨δ, hδpos, ?_⟩
  intro u hu
  have hdist : dist (t₀ + u) t₀ < δ := by rw [dist_eq_norm]; simpa [Real.norm_eq_abs] using hu
  have := hδ hdist
  have e1 : t₀ + u - t₀ = u := by ring
  rw [e1] at this
  have e2 : (u : ℝ) • v = (u:ℂ) * v := rfl
  have e3 : ‖(u:ℝ)‖ = |u| := Real.norm_eq_abs u
  rw [e2, e3] at this
  exact this

/-- **Abstract separation step** (reused from
`Commons.Topology.Jordan.local_sides_of_regular_point`).  Suppose `E ⊆ ℂ` is a set such that every
component of `Eᶜ` has frontier `E`, and `Eᶜ` has at least two components.  If an open set `W`
containing a point `r ∈ E` satisfies `W \ E = U ∪ V` with `U`, `V` preconnected, then the
components of `Eᶜ` through `U` and `V` are distinct. -/
lemma components_ne_of_local_split
    {E W U V : Set ℂ} {r p q : ℂ}
    (hfront : ∀ y : ℂ, y ∈ Eᶜ → frontier (connectedComponentIn Eᶜ y) = E)
    (htwo : ∃ a b : ℂ, a ∈ Eᶜ ∧ b ∈ Eᶜ ∧
      connectedComponentIn Eᶜ a ≠ connectedComponentIn Eᶜ b)
    (hrE : r ∈ E) (hWo : IsOpen W) (hrW : r ∈ W)
    (hUV : W \ E = U ∪ V) (hUpc : IsPreconnected U) (hVpc : IsPreconnected V)
    (hpU : p ∈ U) (hqV : q ∈ V) :
    connectedComponentIn Eᶜ p ≠ connectedComponentIn Eᶜ q := by
  rintro heq
  set C : Set ℂ := connectedComponentIn Eᶜ p with hC
  obtain ⟨a, b, haE, hbE, hab⟩ := htwo
  set Ca : Set ℂ := connectedComponentIn Eᶜ a with hCa
  set Cb : Set ℂ := connectedComponentIn Eᶜ b with hCb
  have hD : ∃ D : Set ℂ, (∃ w ∈ Eᶜ, D = connectedComponentIn Eᶜ w) ∧ D ≠ C := by
    by_cases hCaC : Ca = C
    · refine ⟨Cb, ⟨b, hbE, rfl⟩, ?_⟩
      intro h
      exact hab (hCaC.trans h.symm)
    · exact ⟨Ca, ⟨a, haE, rfl⟩, hCaC⟩
  obtain ⟨D, ⟨w, hwE, hDw⟩, hDC⟩ := hD
  have hfrontD : frontier D = E := by rw [hDw]; exact hfront w hwE
  have hrcl : r ∈ closure D :=
    frontier_subset_closure (by rw [hfrontD]; exact hrE)
  have hDsub : D ⊆ Eᶜ := hDw ▸ connectedComponentIn_subset Eᶜ w
  obtain ⟨z, hzW, hzD⟩ := (_root_.mem_closure_iff.mp hrcl) W hWo hrW
  have hzEc : z ∈ Eᶜ := hDsub hzD
  have hzUV : z ∈ U ∪ V := by
    have : z ∈ W \ E := ⟨hzW, by simpa using hzEc⟩
    rwa [hUV] at this
  have hUsub : U ⊆ C := by
    rw [hC]
    refine IsPreconnected.subset_connectedComponentIn hUpc hpU ?_
    intro y hy
    have : y ∈ W \ E := by rw [hUV]; exact Or.inl hy
    simpa using this.2
  have hpq : connectedComponentIn Eᶜ p = connectedComponentIn Eᶜ q := hC.symm.trans heq
  have hVsub : V ⊆ C := by
    rw [hC, hpq]
    refine IsPreconnected.subset_connectedComponentIn hVpc hqV ?_
    intro y hy
    have : y ∈ W \ E := by rw [hUV]; exact Or.inr hy
    simpa using this.2
  have hzC : z ∈ C := by
    rcases hzUV with h | h
    · exact hUsub h
    · exact hVsub h
  have hDz : D = connectedComponentIn Eᶜ z :=
    hDw.trans (connectedComponentIn_eq (hDw ▸ hzD))
  have hCz : C = connectedComponentIn Eᶜ z :=
    hC.trans (connectedComponentIn_eq (hC ▸ hzC))
  exact hDC (hDz.trans hCz.symm)

/-- If a parametrised curve crosses a Jordan curve transversally at a common point, then for small
positive parameters the two points of the crossing curve lie in different connected components of
the complement of the Jordan curve. -/
theorem local_sides_of_transverse_curve
    (γ : ℝ → ℂ) (hcont : Continuous γ) (hper : Function.Periodic γ 1)
    (hinj : Set.InjOn γ (Set.Ico (0:ℝ) 1))
    (hfront : ∀ y : ℂ, y ∈ (Set.range γ)ᶜ →
      frontier (connectedComponentIn (Set.range γ)ᶜ y) = Set.range γ)
    (hne : ∃ y : ℂ, y ∈ (Set.range γ)ᶜ ∧
      connectedComponentIn (Set.range γ)ᶜ y ≠ (Set.range γ)ᶜ)
    (t₀ : ℝ) (v : ℂ) (hv : v ≠ 0) (hder : ContDiffAt ℝ 1 γ t₀) (hdv : deriv γ t₀ = v)
    (η : ℝ → ℂ) (hη0 : η 0 = γ t₀) (w : ℂ) (hη : HasDerivAt η w 0)
    (hw : (w / v).im ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 0 < s → s < ε →
      η s ∉ Set.range γ ∧ η (-s) ∉ Set.range γ ∧
      connectedComponentIn (Set.range γ)ᶜ (η s) ≠
        connectedComponentIn (Set.range γ)ᶜ (η (-s)) := by
  obtain ⟨W, hWo, hWmem, U, V, hUo, hVo, hdisj, hWUV, hUpc, hVpc,
    ⟨ε₁, hε₁pos, hUmem⟩, ⟨ε₂, hε₂pos, hVmem⟩⟩ :=
    local_split_transverse γ hcont hper hinj t₀ v hv hder hdv η hη0 w hη hw
  obtain ⟨y, hyE, hyne⟩ := hne
  have htwo : ∃ a b : ℂ, a ∈ (Set.range γ)ᶜ ∧ b ∈ (Set.range γ)ᶜ ∧
      connectedComponentIn (Set.range γ)ᶜ a ≠ connectedComponentIn (Set.range γ)ᶜ b := by
    have hout : ∃ b, b ∈ (Set.range γ)ᶜ ∧ b ∉ connectedComponentIn (Set.range γ)ᶜ y := by
      by_contra hcon
      push Not at hcon
      exact hyne (Set.eq_of_subset_of_subset (connectedComponentIn_subset _ _) hcon)
    obtain ⟨b, hbE, hbnot⟩ := hout
    refine ⟨y, b, hyE, hbE, fun h => hbnot ?_⟩
    rw [h]
    exact mem_connectedComponentIn hbE
  refine ⟨min ε₁ ε₂, lt_min hε₁pos hε₂pos, ?_⟩
  intro s hs hlt
  have hs1 : s < ε₁ := lt_of_lt_of_le hlt (min_le_left _ _)
  have hs2 : s < ε₂ := lt_of_lt_of_le hlt (min_le_right _ _)
  have hpU : η s ∈ U := hUmem s hs hs1
  have hqV : η (-s) ∈ V := hVmem s hs hs2
  have hpE : η s ∉ Set.range γ := by
    have : η s ∈ W \ Set.range γ := by rw [hWUV]; exact Or.inl hpU
    exact this.2
  have hqE : η (-s) ∉ Set.range γ := by
    have : η (-s) ∈ W \ Set.range γ := by rw [hWUV]; exact Or.inr hqV
    exact this.2
  have hcomp := components_ne_of_local_split (E := Set.range γ) (W := W) (U := U) (V := V)
    (r := γ t₀) (p := η s) (q := η (-s))
    hfront htwo ⟨t₀, rfl⟩ hWo hWmem hWUV hUpc hVpc hpU hqV
  exact ⟨hpE, hqE, hcomp⟩

end Commons.Topology.Jordan