import Mathlib
import Submission.Work.KT.ExtGen.TripleBdry

namespace Work.KT.ExtGen

set_option maxHeartbeats 800000

/-- The subalgebra `bdryKernel = bdryProj⁻¹(ℂ·1) ⊆ tripleAlg V W Z` (see
`Submission.Work.KT.ExtGen.TripleBdry`) consists exactly of the elements of `tripleAlg` that are
constant on the whole boundary sphere `∂(D_{V×(W×Z)})`, i.e. it is the range of
`tripleIncl V W Z : Kpair (V × (W × Z)) →ₐ[ℂ] tripleAlg V W Z`.  Since `tripleIncl` is injective it
induces an algebra isomorphism onto `bdryKernel`, compatible with the inclusions. -/
theorem exists_bdryKernel_iso (V W Z : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    (v0 : Ball V) (hv0 : v0 ∈ bdry V) (w0 : Ball W) (hw0 : w0 ∈ bdry W)
    (z0 : Ball Z) (hz0 : z0 ∈ bdry Z) :
    ∃ ψ : Kpair (V × (W × Z)) ≃ₐ[ℂ] bdryKernel V W Z v0 hv0 w0 hw0 z0 hz0,
      (bdryKernel V W Z v0 hv0 w0 hw0 z0 hz0).val.comp ψ.toAlgHom
        = tripleIncl V W Z := by
  -- ## Step 1: `tripleIncl` lands in `bdryKernel`
  --
  -- A function `F` constant on the whole boundary sphere is constant on each of the three
  -- chart slices `v = v₀`, `w = w₀`, `z = z₀`, with one and the same constant value, because
  -- each of these slices is contained in the boundary.
  have hmem : ∀ F : Kpair (V × (W × Z)),
      tripleIncl V W Z F ∈ bdryKernel V W Z v0 hv0 w0 hw0 z0 hz0 := by
    intro F
    let p0 : Ball (W × Z) := ⟨((w0 : W), (z0 : Z)), by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Prod.norm_def, hw0, hz0]
      simp⟩
    refine ⟨(F : C(Ball (V × (W × Z)), ℂ)) (sliceMapV0 V W Z v0 hv0 p0), ?_⟩
    have hy0 : sliceMapV0 V W Z v0 hv0 p0 ∈ bdry (V × (W × Z)) := mem_bdry_of_fst V W Z hv0
    apply Subtype.ext
    simp only [Subalgebra.coe_algebraMap, bdryProj_apply]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · apply Subtype.ext
      apply ContinuousMap.ext
      intro p
      show (F : C(Ball (V × (W × Z)), ℂ)) (sliceMapV0 V W Z v0 hv0 p) = _
      rw [F.2 (sliceMapV0 V W Z v0 hv0 p)
        (mem_bdry_of_fst V W Z hv0) (sliceMapV0 V W Z v0 hv0 p0) hy0]
      simp
    · apply Subtype.ext
      apply ContinuousMap.ext
      intro p
      show (F : C(Ball (V × (W × Z)), ℂ)) (sliceMapW0 V W Z w0 hw0 p) = _
      rw [F.2 (sliceMapW0 V W Z w0 hw0 p)
        (mem_bdry_of_w V W Z hw0) (sliceMapV0 V W Z v0 hv0 p0) hy0]
      simp
    · apply Subtype.ext
      apply ContinuousMap.ext
      intro p
      show (F : C(Ball (V × (W × Z)), ℂ)) (sliceMapZ0 V W Z z0 hz0 p) = _
      rw [F.2 (sliceMapZ0 V W Z z0 hz0 p)
        (mem_bdry_of_z V W Z hz0) (sliceMapV0 V W Z v0 hv0 p0) hy0]
      simp
  -- ## Step 2: every element of `bdryKernel` is in the range of `tripleIncl`
  --
  -- An element `u` of `bdryKernel` has all three slices equal to one constant `c`.  On the
  -- boundary the norm is a maximum, so at a boundary point one of the three coordinates lies on
  -- its own sphere; `tripleAlg`'s defining property then moves that coordinate to `v₀`, `w₀`
  -- resp. `z₀`, where the value is `c`.  Hence `u` is constant on the boundary with value `c`,
  -- i.e. `u ∈ Kpair (V × (W × Z))` and `tripleIncl u = u`.
  have hrange : ∀ u : bdryKernel V W Z v0 hv0 w0 hw0 z0 hz0,
      ∃ F : Kpair (V × (W × Z)), tripleIncl V W Z F = u := by
    intro u
    obtain ⟨c, hc⟩ := u.2
    have hV : ∀ p : Ball (W × Z),
        (u.val : C(Ball (V × (W × Z)), ℂ)) (sliceMapV0 V W Z v0 hv0 p) = c := by
      intro p
      rw [← sliceV0_apply V W Z v0 hv0 (u.val : tripleAlg V W Z) p]
      have h1 := congrArg Subtype.val hc
      simp only [Subalgebra.coe_algebraMap] at h1
      rw [bdryProj_apply] at h1
      have h2 := congrArg Prod.fst h1
      simp only at h2
      rw [h2]
      simp
    have hW : ∀ p : Ball (V × Z),
        (u.val : C(Ball (V × (W × Z)), ℂ)) (sliceMapW0 V W Z w0 hw0 p) = c := by
      intro p
      rw [← sliceW0_apply V W Z w0 hw0 (u.val : tripleAlg V W Z) p]
      have h1 := congrArg Subtype.val hc
      simp only [Subalgebra.coe_algebraMap] at h1
      rw [bdryProj_apply] at h1
      have h2 := congrArg (fun t => t.2.1) h1
      simp only at h2
      rw [h2]
      simp
    have hZ : ∀ p : Ball (V × W),
        (u.val : C(Ball (V × (W × Z)), ℂ)) (sliceMapZ0 V W Z z0 hz0 p) = c := by
      intro p
      rw [← sliceZ0_apply V W Z z0 hz0 (u.val : tripleAlg V W Z) p]
      have h1 := congrArg Subtype.val hc
      simp only [Subalgebra.coe_algebraMap] at h1
      rw [bdryProj_apply] at h1
      have h2 := congrArg (fun t => t.2.2) h1
      simp only at h2
      rw [h2]
      simp
    have hbdry : ∀ y : Ball (V × (W × Z)), y ∈ bdry (V × (W × Z)) →
        (u.val : C(Ball (V × (W × Z)), ℂ)) y = c := by
      intro y hy
      have hy : ‖(y : V × (W × Z))‖ = 1 := hy
      have hmax : max ‖(y : V × (W × Z)).1‖ ‖(y : V × (W × Z)).2‖ = 1 := by
        rwa [Prod.norm_def] at hy
      rcases max_eq_iff.mp hmax with ⟨h1, _⟩ | ⟨h2, _⟩
      · have hpt : (u.val : C(Ball (V × (W × Z)), ℂ))
            (sliceMapV0 V W Z v0 hv0 (prSnd V (W × Z) y)) = c := hV _
        rw [← hpt]
        exact u.val.2.1 y _ h1 hv0 rfl rfl
      · have hmax2 : max ‖(y : V × (W × Z)).2.1‖ ‖(y : V × (W × Z)).2.2‖ = 1 := by
          rwa [Prod.norm_def] at h2
        rcases max_eq_iff.mp hmax2 with ⟨h3, _⟩ | ⟨h4, _⟩
        · let q : Ball (V × Z) := ⟨((y : V × (W × Z)).1, (y : V × (W × Z)).2.2), by
            rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Prod.norm_def]
            exact max_le (norm_fst_le' V W Z y) (norm_zc_le V W Z y)⟩
          have hpt : (u.val : C(Ball (V × (W × Z)), ℂ)) (sliceMapW0 V W Z w0 hw0 q) = c := hW q
          rw [← hpt]
          exact u.val.2.2.1 y _ h3 hw0 rfl rfl
        · let q : Ball (V × W) := ⟨((y : V × (W × Z)).1, (y : V × (W × Z)).2.1), by
            rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Prod.norm_def]
            exact max_le (norm_fst_le' V W Z y) (norm_w_le V W Z y)⟩
          have hpt : (u.val : C(Ball (V × (W × Z)), ℂ)) (sliceMapZ0 V W Z z0 hz0 q) = c := hZ q
          rw [← hpt]
          exact u.val.2.2.2 y _ h4 hz0 rfl rfl
    refine ⟨⟨(u.val : C(Ball (V × (W × Z)), ℂ)), ?_⟩, ?_⟩
    · intro y hy y' hy'
      rw [hbdry y hy, hbdry y' hy']
    · exact Subtype.ext rfl
  -- ## Step 3: assemble the isomorphism
  let Φ : Kpair (V × (W × Z)) →ₐ[ℂ] bdryKernel V W Z v0 hv0 w0 hw0 z0 hz0 :=
    AlgHom.codRestrict (tripleIncl V W Z) _ hmem
  have hcoe : ∀ F : Kpair (V × (W × Z)), ((Φ F : bdryKernel V W Z v0 hv0 w0 hw0 z0 hz0) :
      tripleAlg V W Z) = tripleIncl V W Z F := fun F => rfl
  have hinj : Function.Injective Φ := by
    intro a b hab
    have h : tripleIncl V W Z a = tripleIncl V W Z b := by
      rw [← hcoe a, ← hcoe b, hab]
    have h2' : (a : C(Ball (V × (W × Z)), ℂ)) = (b : C(Ball (V × (W × Z)), ℂ)) := by
      simpa using congrArg (fun x : tripleAlg V W Z => (x : C(Ball (V × (W × Z)), ℂ))) h
    exact Subtype.ext h2'
  have hsurj : Function.Surjective Φ := by
    intro u
    obtain ⟨F, hF⟩ := hrange u
    exact ⟨F, Subtype.ext (by rw [hcoe F]; exact hF)⟩
  refine ⟨AlgEquiv.ofBijective Φ ⟨hinj, hsurj⟩, ?_⟩
  apply AlgHom.ext
  intro F
  show ((AlgEquiv.ofBijective Φ ⟨hinj, hsurj⟩) F : tripleAlg V W Z) = tripleIncl V W Z F
  have hFcoe := congrFun (AlgEquiv.coe_ofBijective Φ ⟨hinj, hsurj⟩) F
  rw [show (AlgEquiv.ofBijective Φ ⟨hinj, hsurj⟩) F = Φ F from hFcoe]
  exact hcoe F

end Work.KT.ExtGen
