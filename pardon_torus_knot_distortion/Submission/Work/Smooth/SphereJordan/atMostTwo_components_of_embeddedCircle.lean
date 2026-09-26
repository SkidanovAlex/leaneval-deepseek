import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.SphereJordan.twoComponentsAux
import Submission.Work.Smooth.SphereJordan.mobiusAddInv
import Submission.Work.Smooth.SphereJordan.Transport
import Submission.Work.Smooth.SphereJordan.disc_complement_preconnected

/-!
# At most two components of the complement of an embedded circle on the Riemann sphere

`Work.Smooth.SphereJordan.atMostTwo_components_of_embeddedCircle`: for a continuous `2π`-periodic
curve `γ : ℝ → ℂ ∪ {∞}` which is injective on one period `[0, 2π)`, of any three points of the
Riemann sphere outside the trace of `γ`, two lie in the same connected component of the complement
of the trace.

## The route

* `atMostTwo_of_two_preconnected` (elementary): if the complement of a set `M` is covered by two
  preconnected sets disjoint from `M`, then of any three points off `M` two lie in the same
  component — plain pigeonhole, using that a preconnected subset of `Mᶜ` is contained in a
  component.

* `exists_two_preconnected_cover_of_misses_infty` (the geometric heart): a simple closed curve of
  `ℂ ∪ {∞}` which misses `∞` is a plane curve `γ'`, and the *planar* Jordan curve theorem
  (`Work.Topology.PlaneCurve.compl_jordan_atMostTwo`, Maehara's proof) says that the complement
  `K = (range γ')ᶜ` of its trace has at most two connected components.  We take
  `U := connectedComponentIn K u` for a point `u` on a ray escaping to infinity (so that `U` is
  unbounded and hence `↑''U ∪ {∞}` is preconnected) and `V := K \ U`, which — by the plane
  theorem — is preconnected (a single component) or empty.  These two preconnected sets cover
  `(range γ)ᶜ = ↑''K ∪ {∞}`.

* The general curve is moved off `∞` by a Möbius transformation `Φ` with `Φ x = ∞`
  (`exists_homeomorph_infty_eq`), where `x` is one of the three given points; the two preconnected
  sets are pulled back along `Φ⁻¹` and the pigeonhole of the first step concludes.
-/

namespace Work.Smooth.SphereJordan

noncomputable section

open Set

/-! ## A two-set cover of the complement gives at most two components -/

theorem atMostTwo_of_two_preconnected {α : Type*} [TopologicalSpace α] {M A B : Set α}
    (hA : IsPreconnected A) (hB : IsPreconnected B) (hAc : A ⊆ Mᶜ) (hBc : B ⊆ Mᶜ)
    (hcover : Mᶜ ⊆ A ∪ B) {x y z : α} (hx : x ∉ M) (hy : y ∉ M) (hz : z ∉ M) :
    connectedComponentIn Mᶜ x = connectedComponentIn Mᶜ y ∨
      connectedComponentIn Mᶜ x = connectedComponentIn Mᶜ z ∨
      connectedComponentIn Mᶜ y = connectedComponentIn Mᶜ z := by
  have keyA : ∀ p q : α, p ∈ A → q ∈ A →
      connectedComponentIn Mᶜ p = connectedComponentIn Mᶜ q := fun p q hp hq =>
    connectedComponentIn_eq ((IsPreconnected.subset_connectedComponentIn hA hp hAc) hq)
  have keyB : ∀ p q : α, p ∈ B → q ∈ B →
      connectedComponentIn Mᶜ p = connectedComponentIn Mᶜ q := fun p q hp hq =>
    connectedComponentIn_eq ((IsPreconnected.subset_connectedComponentIn hB hp hBc) hq)
  have hxAB := hcover hx
  have hyAB := hcover hy
  have hzAB := hcover hz
  rcases hxAB with hxA | hxB
  · rcases hyAB with hyA | hyB
    · exact Or.inl (keyA x y hxA hyA)
    · rcases hzAB with hzA | hzB
      · exact Or.inr (Or.inl (keyA x z hxA hzA))
      · exact Or.inr (Or.inr (keyB y z hyB hzB))
  · rcases hyAB with hyA | hyB
    · rcases hzAB with hzA | hzB
      · exact Or.inr (Or.inr (keyA y z hyA hzA))
      · exact Or.inr (Or.inl (keyB x z hxB hzB))
    · exact Or.inl (keyB x y hxB hyB)

/-! ## A curve missing `∞` has a two-set cover of the complement of its trace -/

theorem exists_two_preconnected_cover_of_misses_infty {γ : ℝ → RiemannSphere}
    (hcont : Continuous γ) (hper : Function.Periodic γ (2 * Real.pi))
    (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi))) (hinf : ∀ t, γ t ≠ infty) :
    ∃ A B : Set RiemannSphere, IsPreconnected A ∧ IsPreconnected B ∧
      A ⊆ (Set.range γ)ᶜ ∧ B ⊆ (Set.range γ)ᶜ ∧ (Set.range γ)ᶜ ⊆ A ∪ B := by
  obtain ⟨γ', hcont', hper', hinj', hcoe⟩ :=
    exists_planeCurve_of_avoids_infty ⟨hcont, hper, hinj⟩ hinf
  -- the trace of `γ` is the coercion of the plane trace
  have hrange : Set.range γ = (↑) '' (Set.range γ') := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨γ' t, ⟨t, rfl⟩, (hcoe t).symm⟩
    · rintro ⟨w, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, hcoe t⟩
  have hcompl : (Set.range γ)ᶜ = (↑) '' ((Set.range γ')ᶜ) ∪ {infty} := by
    rw [hrange, OnePoint.compl_image_coe]
  -- a bound on the trace of the plane curve
  obtain ⟨R, hR⟩ :=
    (Work.Topology.PlaneCurve.isCompact_range_of_periodic hcont' hper').isBounded.exists_norm_le
  have hR0 : 0 ≤ R := le_trans (norm_nonneg (γ' 0)) (hR _ ⟨0, rfl⟩)
  set u : ℂ := ((R + 1 : ℝ) : ℂ) with hudef
  have hunorm : ‖u‖ = R + 1 := by
    rw [hudef, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have huK : u ∈ (Set.range γ')ᶜ := by
    rintro ⟨t, ht⟩
    have h1 := hR (γ' t) ⟨t, rfl⟩
    rw [ht, hunorm] at h1
    linarith
  -- points of the ray `[R+1, ∞)` lie in the component of `u`
  have hray : ∀ y : ℝ, R + 1 ≤ y →
      ((y : ℝ) : ℂ) ∈ connectedComponentIn (Set.range γ')ᶜ u := by
    intro y hy
    have hpre : IsPreconnected ((fun r : ℝ => ((r : ℝ) : ℂ)) '' Set.Icc (R + 1) y) :=
      isPreconnected_Icc.image _ Complex.continuous_ofReal.continuousOn
    have hsub : ((fun r : ℝ => ((r : ℝ) : ℂ)) '' Set.Icc (R + 1) y) ⊆ (Set.range γ')ᶜ := by
      rintro c ⟨r, hr, rfl⟩
      rintro ⟨t, ht⟩
      have hb := hR (γ' t) ⟨t, rfl⟩
      rw [ht] at hb
      have hn : ‖((r : ℝ) : ℂ)‖ = r := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hr.1, hR0])]
      rw [hn] at hb
      linarith [hr.1]
    exact IsPreconnected.subset_connectedComponentIn hpre
      ⟨R + 1, ⟨le_refl _, hy⟩, hudef.symm⟩ hsub ⟨y, ⟨hy, le_refl _⟩, rfl⟩
  -- hence the component of `u` is unbounded
  have hUunb : ∀ M : ℝ, ∃ c ∈ connectedComponentIn (Set.range γ')ᶜ u, M ≤ ‖c‖ := by
    intro M
    refine ⟨((max (R + 1) (max M 0) : ℝ) : ℂ), hray _ (le_max_left _ _), ?_⟩
    have hnn : (0 : ℝ) ≤ max (R + 1) (max M 0) :=
      le_trans (by linarith : (0 : ℝ) ≤ R + 1) (le_max_left _ _)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
    exact le_trans (le_max_left M 0) (le_max_right (R + 1) (max M 0))
  -- and therefore `∞` lies in the closure of its image
  have hUcl : infty ∈ closure ((↑) '' connectedComponentIn (Set.range γ')ᶜ u) := by
    rw [mem_closure_iff_nhds]
    intro N hN
    obtain ⟨K₀, ⟨hK₀cl, hK₀comp⟩, hK₀N⟩ := OnePoint.hasBasis_nhds_infty.mem_iff.mp hN
    obtain ⟨R₀, hR₀⟩ := hK₀comp.isBounded.exists_norm_le
    obtain ⟨c, hcU, hcn⟩ := hUunb (R₀ + 1)
    have hcK₀ : c ∉ K₀ := by
      intro hmem
      have := hR₀ c hmem
      linarith
    exact ⟨(↑c : RiemannSphere), hK₀N (Or.inl ⟨c, hcK₀, rfl⟩), ⟨c, hcU, rfl⟩⟩
  -- the second plane piece: the remaining part of the plane complement
  have hVpre : IsPreconnected ((Set.range γ')ᶜ \ connectedComponentIn (Set.range γ')ᶜ u) := by
    have key : ∀ p q : ℂ, p ∈ (Set.range γ')ᶜ \ connectedComponentIn (Set.range γ')ᶜ u →
        q ∈ (Set.range γ')ᶜ \ connectedComponentIn (Set.range γ')ᶜ u →
        connectedComponentIn (Set.range γ')ᶜ p = connectedComponentIn (Set.range γ')ᶜ q := by
      intro p q hp hq
      by_contra hne
      have hpu : connectedComponentIn (Set.range γ')ᶜ p ≠
          connectedComponentIn (Set.range γ')ᶜ u := by
        intro hcon
        exact hp.2 (by rw [← hcon]; exact mem_connectedComponentIn hp.1)
      have hqu : connectedComponentIn (Set.range γ')ᶜ q ≠
          connectedComponentIn (Set.range γ')ᶜ u := by
        intro hcon
        exact hq.2 (by rw [← hcon]; exact mem_connectedComponentIn hq.1)
      rcases Work.Topology.PlaneCurve.compl_jordan_atMostTwo hcont' hper' hinj' huK hp.1 hq.1
        with h | h | h
      · exact hpu h.symm
      · exact hqu h.symm
      · exact hne h
    rcases Set.eq_empty_or_nonempty ((Set.range γ')ᶜ \ connectedComponentIn (Set.range γ')ᶜ u)
      with hempty | ⟨x₀, hx₀⟩
    · rw [hempty]; exact isPreconnected_empty
    · have hVeq : (Set.range γ')ᶜ \ connectedComponentIn (Set.range γ')ᶜ u
          = connectedComponentIn (Set.range γ')ᶜ x₀ := by
        apply Subset.antisymm
        · intro x hx
          rw [← key x x₀ hx hx₀]
          exact mem_connectedComponentIn hx.1
        · intro z hz
          have hzK : z ∈ (Set.range γ')ᶜ := connectedComponentIn_subset _ _ hz
          have hcc : connectedComponentIn (Set.range γ')ᶜ z
              = connectedComponentIn (Set.range γ')ᶜ x₀ := (connectedComponentIn_eq hz).symm
          have hzU : z ∉ connectedComponentIn (Set.range γ')ᶜ u := by
            intro hzU
            have h1 : connectedComponentIn (Set.range γ')ᶜ u
                = connectedComponentIn (Set.range γ')ᶜ z := connectedComponentIn_eq hzU
            have h2 : connectedComponentIn (Set.range γ')ᶜ u
                = connectedComponentIn (Set.range γ')ᶜ x₀ := h1.trans hcc
            exact hx₀.2 (by rw [h2]; exact mem_connectedComponentIn hx₀.1)
          exact ⟨hzK, hzU⟩
      rw [hVeq]; exact isPreconnected_connectedComponentIn
  refine ⟨insert infty ((↑) '' connectedComponentIn (Set.range γ')ᶜ u),
    (↑) '' ((Set.range γ')ᶜ \ connectedComponentIn (Set.range γ')ᶜ u), ?_, ?_, ?_, ?_, ?_⟩
  · -- the outer set is preconnected
    refine IsPreconnected.subset_closure ?_ (subset_insert _ _) ?_
    · exact isPreconnected_connectedComponentIn.image _ OnePoint.continuous_coe.continuousOn
    · intro x hx
      rcases hx with rfl | hx
      · exact hUcl
      · exact subset_closure hx
  · exact hVpre.image _ OnePoint.continuous_coe.continuousOn
  · -- `insert ∞ (↑''U) ⊆ (range γ)ᶜ`
    intro x hx
    rw [hcompl]
    rcases hx with rfl | hx
    · exact Or.inr (Set.mem_singleton_iff.mpr rfl)
    · rcases hx with ⟨c, hcU, rfl⟩
      exact Or.inl ⟨c, connectedComponentIn_subset _ _ hcU, rfl⟩
  · -- `↑''V ⊆ (range γ)ᶜ`
    intro x hx
    rw [hcompl]
    rcases hx with ⟨c, hcV, rfl⟩
    exact Or.inl ⟨c, hcV.1, rfl⟩
  · -- the cover
    intro x hx
    rw [hcompl] at hx
    rcases hx with ⟨c, hcK, rfl⟩ | hx
    · by_cases hcU : c ∈ connectedComponentIn (Set.range γ')ᶜ u
      · exact Or.inl (Or.inr ⟨c, hcU, rfl⟩)
      · exact Or.inr ⟨c, ⟨hcK, hcU⟩, rfl⟩
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact Or.inl (Set.mem_insert _ _)

/-! ## The target -/

theorem atMostTwo_components_of_embeddedCircle {γ : ℝ → Work.Smooth.SphereJordan.RiemannSphere}
    (hγ : Continuous γ) (hper : Function.Periodic γ (2 * Real.pi))
    (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi)))
    {x y z : Work.Smooth.SphereJordan.RiemannSphere}
    (hx : x ∉ Set.range γ) (hy : y ∉ Set.range γ) (hz : z ∉ Set.range γ) :
    connectedComponentIn (Set.range γ)ᶜ x = connectedComponentIn (Set.range γ)ᶜ y ∨
    connectedComponentIn (Set.range γ)ᶜ x = connectedComponentIn (Set.range γ)ᶜ z ∨
    connectedComponentIn (Set.range γ)ᶜ y = connectedComponentIn (Set.range γ)ᶜ z := by
  obtain ⟨Φ, hΦ⟩ := exists_homeomorph_infty_eq x
  set Ψ : RiemannSphere ≃ₜ RiemannSphere := Φ.symm with hΨdef
  have hΨx : Ψ x = infty := by
    rw [hΨdef, ← hΦ]
    exact Φ.symm_apply_apply infty
  set γ₁ : ℝ → RiemannSphere := fun t => Ψ (γ t) with hγ₁def
  have hγ₁cont : Continuous γ₁ := Ψ.continuous.comp hγ
  have hγ₁per : Function.Periodic γ₁ (2 * Real.pi) := fun t => by
    change Ψ (γ (t + 2 * Real.pi)) = Ψ (γ t)
    rw [hper t]
  have hγ₁inj : Set.InjOn γ₁ (Set.Ico 0 (2 * Real.pi)) :=
    fun a ha b hb hab => hinj ha hb (Ψ.injective hab)
  have hγ₁inf : ∀ t, γ₁ t ≠ infty := by
    intro t ht
    have ht' : Ψ (γ t) = infty := ht
    have h1 : Ψ (γ t) = Ψ x := by rw [ht', hΨx]
    exact hx ⟨t, Ψ.injective h1⟩
  obtain ⟨A, B, hApre, hBpre, hAc, hBc, hcov⟩ :=
    exists_two_preconnected_cover_of_misses_infty hγ₁cont hγ₁per hγ₁inj hγ₁inf
  refine atMostTwo_of_two_preconnected (M := Set.range γ)
    (A := Ψ.symm '' A) (B := Ψ.symm '' B) ?_ ?_ ?_ ?_ ?_ hx hy hz
  · exact hApre.image _ Ψ.symm.continuous.continuousOn
  · exact hBpre.image _ Ψ.symm.continuous.continuousOn
  · rintro p ⟨a, ha, rfl⟩ ⟨t, ht⟩
    refine hAc ha ⟨t, ?_⟩
    change Ψ (γ t) = a
    rw [ht]
    exact Ψ.apply_symm_apply a
  · rintro p ⟨a, ha, rfl⟩ ⟨t, ht⟩
    refine hBc ha ⟨t, ?_⟩
    change Ψ (γ t) = a
    rw [ht]
    exact Ψ.apply_symm_apply a
  · intro p hp
    have hp₁ : Ψ p ∉ Set.range γ₁ := by
      rintro ⟨t, ht⟩
      have ht' : Ψ (γ t) = Ψ p := ht
      exact hp ⟨t, Ψ.injective ht'⟩
    rcases hcov hp₁ with h | h
    · exact Or.inl ⟨Ψ p, h, Ψ.symm_apply_apply p⟩
    · exact Or.inr ⟨Ψ p, h, Ψ.symm_apply_apply p⟩

end

end Work.Smooth.SphereJordan
