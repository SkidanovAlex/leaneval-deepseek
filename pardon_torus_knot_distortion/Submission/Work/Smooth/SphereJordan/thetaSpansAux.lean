import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.SphereJordan.planeArcSetup
import Submission.Work.Smooth.SphereJordan.disc_complement_preconnected
import Submission.Work.Smooth.SphereJordan.arcImageInteriorEmpty

/-!
# Auxiliary lemmas for `Work.Smooth.SphereJordan.thetaSpansOfPlane`

Three independent facts used by the main file:

* `spherePairOfPlanePair` — adjoining `∞` to the unbounded member of a pair of complementary
  plane pieces turns it into the corresponding sphere piece (openness, preconnectedness,
  disjointness, closure);
* `exists_notMem_theta` — a point of the Riemann sphere off the whole theta graph
  `D₁ ∪ D₂ ∪ α ∪ β` (this is what allows the configuration to be moved into the plane by a Möbius
  transformation);
* `exists_lift_of_avoids_infty` — a continuous map into the sphere avoiding `∞` is, uniquely, the
  coercion of a continuous map into `ℂ`.
-/

open Set

namespace Work.Smooth.SphereJordan

noncomputable section

/-! ## Adjoining `∞` to the unbounded plane piece -/

theorem spherePairOfPlanePair {R : ℝ} {P₁ P₂ : Set ℂ}
    (hP₁o : IsOpen P₁) (hP₂o : IsOpen P₂) (hd : Disjoint P₁ P₂)
    (hP₁c : IsPreconnected P₁) (hP₂c : IsPreconnected P₂)
    (hfar : ∀ z : ℂ, R < ‖z‖ → z ∈ P₁) :
    IsOpen (((↑) '' P₁) ∪ ({OnePoint.infty} : Set RiemannSphere)) ∧
    IsOpen (((↑) '' P₂) : Set RiemannSphere) ∧
    IsPreconnected (((↑) '' P₁) ∪ ({OnePoint.infty} : Set RiemannSphere)) ∧
    IsPreconnected (((↑) '' P₂) : Set RiemannSphere) ∧
    Disjoint (((↑) '' P₁) ∪ ({OnePoint.infty} : Set RiemannSphere))
      (((↑) '' P₂) : Set RiemannSphere) ∧
    closure (((↑) '' P₁) ∪ ({OnePoint.infty} : Set RiemannSphere)) =
      closure (((↑) '' P₁) : Set RiemannSphere) := by
  have hinfcl : OnePoint.infty ∈ closure (((↑) '' P₁) : Set RiemannSphere) := by
    rw [mem_closure_iff_nhds]
    intro V hV
    obtain ⟨K, ⟨hKcl, hKcomp⟩, hKV⟩ := OnePoint.hasBasis_nhds_infty.mem_iff.mp hV
    obtain ⟨R', hR'⟩ := hKcomp.isBounded.exists_norm_le
    set z : ℂ := ((max R (max R' 0) + 1 : ℝ) : ℂ) with hzdef
    have hznorm : ‖z‖ = max R (max R' 0) + 1 := by
      rw [hzdef, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0:ℝ) < max R (max R' 0) + 1)]
    have hzP : z ∈ P₁ := hfar z (by rw [hznorm]; linarith [le_max_left R (max R' 0)])
    have hzK : z ∈ Kᶜ := by
      intro hzK
      have h := hR' z hzK
      rw [hznorm] at h
      linarith [le_max_left R' 0, le_max_right R (max R' 0)]
    refine ⟨(↑z : RiemannSphere), hKV ?_, ⟨z, hzP, rfl⟩⟩
    exact Or.inl ⟨z, hzK, rfl⟩
  have hsub : (P₁ᶜ : Set ℂ) ⊆ Metric.closedBall (0:ℂ) R := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra h
    exact hz (hfar z (lt_of_not_ge h))
  have hQcompl : (((↑) '' P₁) ∪ ({OnePoint.infty} : Set RiemannSphere))ᶜ
      = (↑) '' (P₁ᶜ : Set ℂ) := by
    rw [Set.compl_union, OnePoint.compl_image_coe]
    ext x
    constructor
    · rintro ⟨hx | hx, hxne⟩
      · exact hx
      · exact absurd (hx ▸ Set.mem_singleton OnePoint.infty) hxne
    · rintro ⟨z, hz, rfl⟩
      exact ⟨Or.inl ⟨z, hz, rfl⟩, OnePoint.coe_ne_infty z⟩
  have hcomp : IsCompact (((↑) '' (P₁ᶜ : Set ℂ)) : Set RiemannSphere) :=
    ((isCompact_closedBall (0:ℂ) R).of_isClosed_subset hP₁o.isClosed_compl hsub).image
      OnePoint.continuous_coe
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← isClosed_compl_iff, hQcompl]; exact hcomp.isClosed
  · exact (OnePoint.isOpen_image_coe).mpr hP₂o
  · exact (hP₁c.image _ OnePoint.continuous_coe.continuousOn).subset_closure
      (by intro x hx; exact Or.inl hx)
      (by intro x hx; rcases hx with hx | rfl
          · exact subset_closure hx
          · exact hinfcl)
  · exact hP₂c.image _ OnePoint.continuous_coe.continuousOn
  · rw [Set.disjoint_left]
    rintro x hx hx'
    rcases hx with hx | rfl
    · obtain ⟨z, hz, rfl⟩ := hx
      obtain ⟨w, hw, hwz⟩ := hx'
      exact (Set.disjoint_left.mp hd) hz (OnePoint.coe_injective hwz.symm ▸ hw)
    · obtain ⟨w, hw, hwz⟩ := hx'
      exact (OnePoint.coe_ne_infty w) hwz
  · rw [closure_union, isClosed_singleton.closure_eq, Set.union_eq_left]
    exact Set.singleton_subset_iff.mpr hinfcl

/-! ## A point of the sphere off the theta graph -/

/-- **The image of a continuum joining the two discs, in the plane, is harmless.**  In the plane,
`{z | R < ‖z‖}` is preconnected (a scaling of the exterior of the unit ball). -/
theorem isPreconnected_far' {R : ℝ} (hR : 0 < R) : IsPreconnected {w : ℂ | R < ‖w‖} := by
  have hpre0 : IsPreconnected {w : ℂ | (1:ℝ) < ‖w‖} :=
    Work.Smooth.Jordan.isPreconnected_exterior_unitBall
  have himg := hpre0.image (fun w : ℂ => R * w) ((continuous_const.mul continuous_id).continuousOn)
  have heq : (fun w : ℂ => R * w) '' {w : ℂ | (1:ℝ) < ‖w‖} = {w : ℂ | R < ‖w‖} := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hnorm : ‖R * v‖ = R * ‖v‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
      rw [Set.mem_ofPred_eq, hnorm]
      simpa using mul_lt_mul_of_pos_left hv hR
    · intro hw
      refine ⟨R⁻¹ * w, ?_, ?_⟩
      · have hnorm : ‖R⁻¹ * w‖ = R⁻¹ * ‖w‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
        rw [Set.mem_ofPred_eq, hnorm, inv_mul_eq_div, one_lt_div hR]
        exact hw
      · have hRne : ((R : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hR)
        show (fun w : ℂ => R * w) (R⁻¹ * w) = w
        push_cast
        field_simp
  rwa [heq] at himg

/-- **A point of the Riemann sphere off the whole theta graph.** -/
theorem exists_notMem_theta {D₁ D₂ : Set RiemannSphere}
    (hD₁ : ∃ f : C(Disc, RiemannSphere), Function.Injective f ∧ Set.range f = D₁)
    (hD₂ : ∃ g : C(Disc, RiemannSphere), Function.Injective g ∧ Set.range g = D₂)
    (hdisj : Disjoint D₁ D₂)
    (α β : C(Set.Icc (0 : ℝ) 1, RiemannSphere))
    (hαinj : Function.Injective α) (hβinj : Function.Injective β)
    (hα₀ : α ⟨0, by norm_num⟩ ∈ D₁) (hα₁ : α ⟨1, by norm_num⟩ ∈ D₂)
    (hβ₀ : β ⟨0, by norm_num⟩ ∈ D₁) (hβ₁ : β ⟨1, by norm_num⟩ ∈ D₂)
    (hαint : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → α t ∉ D₁ ∪ D₂)
    (hβint : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → β t ∉ D₁ ∪ D₂)
    (hsep : ∀ s t : Set.Icc (0 : ℝ) 1, (s : ℝ) ∈ Set.Ioo 0 1 → (t : ℝ) ∈ Set.Ioo 0 1 →
      α s ≠ β t)
    (hαβ₀ : α ⟨0, by norm_num⟩ ≠ β ⟨0, by norm_num⟩)
    (hαβ₁ : α ⟨1, by norm_num⟩ ≠ β ⟨1, by norm_num⟩) :
    ∃ p : RiemannSphere, p ∉ D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β := by
  classical
  obtain ⟨f₁, hf₁inj, hf₁range⟩ := hD₁
  obtain ⟨f₂, hf₂inj, hf₂range⟩ := hD₂
  have hD₁closed : IsClosed D₁ := hf₁range ▸ (isCompact_range f₁.continuous).isClosed
  have hD₂closed : IsClosed D₂ := hf₂range ▸ (isCompact_range f₂.continuous).isClosed
  have hD₁proper : ∃ x : RiemannSphere, x ∉ D₁ := by
    obtain ⟨c, hc⟩ := exists_coe_notMem_range (f := f₁) hf₁inj
    exact ⟨↑c, fun h => hc (hf₁range ▸ h)⟩
  have hD₂proper : ∃ x : RiemannSphere, x ∉ D₂ := by
    obtain ⟨c, hc⟩ := exists_coe_notMem_range (f := f₂) hf₂inj
    exact ⟨↑c, fun h => hc (hf₂range ▸ h)⟩
  have hpre : IsPreconnected (Set.univ : Set RiemannSphere) := by
    have h1 : IsPreconnected (Set.range ((↑) : ℂ → RiemannSphere)) := by
      simpa [Set.image_univ] using
        (isPreconnected_univ (α := ℂ)).image _ OnePoint.continuous_coe.continuousOn
    rw [← OnePoint.denseRange_coe.closure_range]
    exact h1.closure
  have hne : D₁ ∪ D₂ ≠ Set.univ := by
    intro hU
    rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hpre D₁ D₂ hD₁closed hD₂closed
      (by rw [hU]) (by rw [Set.disjoint_iff_inter_eq_empty.mp hdisj, Set.inter_empty])) with h1 | h1
    · obtain ⟨x, hx⟩ := hD₁proper
      exact hx (h1 (Set.mem_univ x))
    · obtain ⟨x, hx⟩ := hD₂proper
      exact hx (h1 (Set.mem_univ x))
  by_contra hcon
  push_neg at hcon
  have hWopen : IsOpen (D₁ ∪ D₂)ᶜ := (hD₁closed.union hD₂closed).isOpen_compl
  have hWne : (D₁ ∪ D₂)ᶜ.Nonempty := Set.nonempty_compl.mpr hne
  obtain ⟨p, hp⟩ := hWne
  have hpX : p ∉ D₁ ∪ D₂ := hp
  obtain ⟨w, hw⟩ : ∃ w : ℂ, (w : RiemannSphere) ∈ (D₁ ∪ D₂)ᶜ := by
    by_cases hpinf : p = OnePoint.infty
    · have hinf : OnePoint.infty ∈ (D₁ ∪ D₂)ᶜ := hpinf ▸ hp
      have hcpt : IsCompact (((↑) ⁻¹' (D₁ ∪ D₂)ᶜ)ᶜ : Set ℂ) :=
        ((OnePoint.isOpen_iff_of_mem' hinf).mp hWopen).1
      obtain ⟨R, hR⟩ := hcpt.isBounded.exists_norm_le
      refine ⟨(((R + 1 : ℝ)) : ℂ), ?_⟩
      by_contra hmem
      have hmem' : (((R + 1 : ℝ)) : ℂ) ∈ (((↑) ⁻¹' (D₁ ∪ D₂)ᶜ)ᶜ : Set ℂ) := hmem
      have hthis := hR _ hmem'
      rw [Complex.norm_real, Real.norm_eq_abs] at hthis
      have h2 : 0 ≤ R := le_trans (abs_nonneg _) hthis
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ R + 1)] at hthis
      linarith
    · obtain ⟨w, hw'⟩ := OnePoint.ne_infty_iff_exists.mp hpinf
      exact ⟨w, hw' ▸ hp⟩
  have hpreopen : IsOpen ((↑) ⁻¹' (D₁ ∪ D₂)ᶜ : Set ℂ) := hWopen.preimage OnePoint.continuous_coe
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hpreopen w hw
  have hUne : (((↑) '' Metric.ball w ε) : Set RiemannSphere).Nonempty :=
    ⟨↑w, w, Metric.mem_ball_self hε, rfl⟩
  have hUpre : IsPreconnected ((↑) '' (Metric.ball w ε) : Set RiemannSphere) :=
    (convex_ball w ε).isPreconnected.image _ OnePoint.continuous_coe.continuousOn
  have hUopen : IsOpen (((↑) '' (Metric.ball w ε)) : Set RiemannSphere) :=
    (OnePoint.isOpen_image_coe).mpr (Metric.isOpen_ball)
  have hUsub : ((↑) '' Metric.ball w ε : Set RiemannSphere) ⊆ Set.range α ∪ Set.range β := by
    intro x hx
    have hxW : x ∈ (D₁ ∪ D₂)ᶜ := by
      obtain ⟨z, hz, rfl⟩ := hx
      exact hball hz
    have hxX := hcon x
    rcases hxX with h | h
    · rcases h with h | h
      · exact absurd h hxW
      · exact Or.inl h
    · exact Or.inr h
  have hdisjAB : Disjoint (Set.range α) (Set.range β) := by
    rw [Set.disjoint_left]
    rintro x ⟨s, hs⟩ ⟨t, ht⟩
    rw [← hs] at ht
    by_cases hsI : (s : ℝ) ∈ Set.Ioo 0 1
    · by_cases htI : (t : ℝ) ∈ Set.Ioo 0 1
      · exact hsep s t hsI htI ht.symm
      · rcases eq_endpoints_of_mem_Icc htI with h | h
        · rw [h] at ht; exact hαint s hsI (Or.inl (ht ▸ hβ₀))
        · rw [h] at ht; exact hαint s hsI (Or.inr (ht ▸ hβ₁))
    · rcases eq_endpoints_of_mem_Icc hsI with h | h
      · by_cases htI : (t : ℝ) ∈ Set.Ioo 0 1
        · rw [h] at ht; exact hβint t htI (Or.inl (ht.symm ▸ hα₀))
        · rcases eq_endpoints_of_mem_Icc htI with h2 | h2
          · rw [h, h2] at ht; exact hαβ₀ ht.symm
          · rw [h, h2] at ht
            exact (Set.disjoint_left.mp hdisj hα₀) (ht.symm ▸ hβ₁)
      · by_cases htI : (t : ℝ) ∈ Set.Ioo 0 1
        · rw [h] at ht; exact hβint t htI (Or.inr (ht.symm ▸ hα₁))
        · rcases eq_endpoints_of_mem_Icc htI with h2 | h2
          · rw [h, h2] at ht
            exact (Set.disjoint_left.mp hdisj hβ₀) (ht ▸ hα₁)
          · rw [h, h2] at ht; exact hαβ₁ ht.symm
  have hAclosed : IsClosed (Set.range α) := (isCompact_range α.continuous).isClosed
  have hBclosed : IsClosed (Set.range β) := (isCompact_range β.continuous).isClosed
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hUpre (Set.range α) (Set.range β)
      hAclosed hBclosed hUsub
      (by rw [Set.disjoint_iff_inter_eq_empty.mp hdisjAB, Set.inter_empty])) with h | h
  · obtain ⟨x, hx⟩ := hUne
    have h1 : x ∈ interior (Set.range α) := interior_maximal h hUopen hx
    rw [arcImageInteriorEmpty hαinj] at h1
    exact h1
  · obtain ⟨x, hx⟩ := hUne
    have h1 : x ∈ interior (Set.range β) := interior_maximal h hUopen hx
    rw [arcImageInteriorEmpty hβinj] at h1
    exact h1

/-! ## Lifting a map that avoids `∞` -/

theorem exists_lift_of_avoids_infty {X : Type*} [TopologicalSpace X] (g : C(X, RiemannSphere))
    (hne : ∀ x, g x ≠ infty) :
    ∃ g' : C(X, ℂ), (∀ x, ((g' x : ℂ) : RiemannSphere) = g x) ∧
      (Function.Injective g → Function.Injective g') := by
  choose gfun hgfun using fun x => OnePoint.ne_infty_iff_exists.mp (hne x)
  have hcont : Continuous gfun := by
    rw [Topology.IsInducing.continuous_iff OnePoint.isOpenEmbedding_coe.isEmbedding.isInducing]
    have h1 : ((↑) : ℂ → RiemannSphere) ∘ gfun = ⇑g := funext hgfun
    rw [h1]; exact g.continuous
  refine ⟨⟨gfun, hcont⟩, fun x => hgfun x, ?_⟩
  intro hinj x y hxy
  have hxy' : gfun x = gfun y := hxy
  exact hinj (by rw [← hgfun x, ← hgfun y, hxy'])

/-! ## Assembling the sphere statement from a plane pair -/

/-- **The transport step.**  Given a homeomorphism `Φ` of the sphere, a closed set `X` with
`∞ ∉ X`, and a pair of complementary plane pieces `P, Q` whose union with `∞` is the sphere
complement of `Φ⁻¹ '' X`, together with spanning discs for the closures, the two sphere pieces
`Φ '' (P ∪ {∞})` and `Φ '' Q` realise the theta-graph complement of `X`. -/
theorem sphereThetaSpansOfPlanePair (Φ : RiemannSphere ≃ₜ RiemannSphere) {X : Set RiemannSphere}
    {R : ℝ} {P Q : Set ℂ}
    (hPo : IsOpen P) (hQo : IsOpen Q) (hd : Disjoint P Q)
    (hPc : IsPreconnected P) (hQc : IsPreconnected Q)
    (hQne : Q.Nonempty)
    (hX : (↑) '' (P ∪ Q) ∪ {infty} = (Φ.symm '' X)ᶜ)
    (hspanP : ∃ Φ₁ : C(Disc, RiemannSphere),
      Function.Injective Φ₁ ∧ Set.range Φ₁ = closure ((↑) '' P))
    (hspanQ : ∃ Φ₂ : C(Disc, RiemannSphere),
      Function.Injective Φ₂ ∧ Set.range Φ₂ = closure ((↑) '' Q))
    (hfar : ∀ z : ℂ, R < ‖z‖ → z ∈ P) :
    ∃ P₁ P₂ : Set RiemannSphere,
      P₁.Nonempty ∧ P₂.Nonempty ∧ IsOpen P₁ ∧ IsOpen P₂ ∧ Disjoint P₁ P₂ ∧
      P₁ ∪ P₂ = Set.univ \ X ∧ IsPreconnected P₁ ∧ IsPreconnected P₂ ∧
      (∃ Ψ₁ : C(Disc, RiemannSphere), Function.Injective Ψ₁ ∧ Set.range Ψ₁ = closure P₁) ∧
      (∃ Ψ₂ : C(Disc, RiemannSphere), Function.Injective Ψ₂ ∧ Set.range Ψ₂ = closure P₂) := by
  obtain ⟨hO₁, hO₂, hC₁, hC₂, hD, hCl⟩ := spherePairOfPlanePair hPo hQo hd hPc hQc hfar
  refine ⟨Φ '' ((↑) '' P ∪ {infty}), Φ '' ((↑) '' Q), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨Φ infty, infty, Or.inr rfl, rfl⟩
  · obtain ⟨q, hq⟩ := hQne
    exact ⟨Φ ↑q, ↑q, ⟨q, hq, rfl⟩, rfl⟩
  · exact Φ.isOpenMap _ hO₁
  · exact Φ.isOpenMap _ hO₂
  · rw [Set.disjoint_left]
    rintro x ⟨y, hy, rfl⟩ ⟨z, hz, hzy⟩
    exact (Set.disjoint_left.mp hD hy) (Φ.injective hzy ▸ hz)
  · have h1 : Φ '' ((↑) '' P ∪ {infty}) ∪ Φ '' ((↑) '' Q)
        = Φ '' ((↑) '' (P ∪ Q) ∪ {infty}) := by
      rw [← Set.image_union]
      congr 1
      rw [Set.image_union]
      ext x
      simp only [Set.mem_union, Set.mem_image, Set.mem_singleton_iff]
      constructor
      · rintro ((h | h) | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
        · exact Or.inl (Or.inr h)
      · rintro (h | h)
        · rcases h with h | h
          · exact Or.inl (Or.inl h)
          · exact Or.inr h
        · exact Or.inl (Or.inr h)
    rw [h1, hX, Set.image_compl_eq Φ.bijective, Set.image_image]
    simp [Set.compl_eq_univ_sdiff]
  · exact hC₁.image Φ Φ.continuous.continuousOn
  · exact hC₂.image Φ Φ.continuous.continuousOn
  · obtain ⟨Φ₁, hΦ₁inj, hΦ₁range⟩ := hspanP
    refine ⟨⟨fun z => Φ (Φ₁ z), Φ.continuous.comp Φ₁.continuous⟩, Φ.injective.comp hΦ₁inj, ?_⟩
    show Set.range (fun z : Disc => Φ (Φ₁ z)) = closure (Φ '' ((↑) '' P ∪ {infty}))
    calc Set.range (fun z : Disc => Φ (Φ₁ z)) = Φ '' Set.range Φ₁ := Set.range_comp _ _
      _ = Φ '' closure ((↑) '' P) := by rw [hΦ₁range]
      _ = closure (Φ '' ((↑) '' P)) := Φ.image_closure _
      _ = closure (Φ '' ((↑) '' P ∪ {infty})) := by
            rw [← Φ.image_closure, ← Φ.image_closure, hCl]
  · obtain ⟨Φ₂, hΦ₂inj, hΦ₂range⟩ := hspanQ
    refine ⟨⟨fun z => Φ (Φ₂ z), Φ.continuous.comp Φ₂.continuous⟩, Φ.injective.comp hΦ₂inj, ?_⟩
    show Set.range (fun z : Disc => Φ (Φ₂ z)) = closure (Φ '' ((↑) '' Q))
    calc Set.range (fun z : Disc => Φ (Φ₂ z)) = Φ '' Set.range Φ₂ := Set.range_comp _ _
      _ = Φ '' closure ((↑) '' Q) := by rw [hΦ₂range]
      _ = closure (Φ '' ((↑) '' Q)) := Φ.image_closure _

end

end Work.Smooth.SphereJordan
