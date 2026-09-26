import Mathlib
import Submission.Work.Drive.Mono.frontier_inter_halfspace_2d_aux
import Submission.Work.Drive.Mono.mem_interior_of_slice_ball

namespace Work.Drive.Mono

open Set

noncomputable section

/-- **The frontier of a compact convex body of `ℝ³` cut by a plane and a halfspace is
preconnected** (assembly of the `2`-dimensional case and the relative-interior input).

If the plane `P = {f = t}` misses the interior of `K`, then `K ∩ P ⊆ frontier K` and the claim
reduces to the convexity of `K ∩ P ∩ {ℓ ≤ lam}`.  Otherwise pick `u ∈ P ∩ interior K` and slice
by `P ≅ ker f`: the frontier of the slice is the slice of the frontier
(`Work.Drive.Mono.mem_interior_of_slice_ball`), so
`Work.Drive.Mono.isPreconnected_frontier_inter_halfspace_2d` applies to `Φ ⁻¹' K ⊆ ker f`. -/
theorem isPreconnected_frontier_inter_hyperplane_inter_halfspace_assembly
    {K : Set (EuclideanSpace ℝ (Fin 3))}
    (hKc : Convex ℝ K) (hKcomp : IsCompact K) (hKint : (interior K).Nonempty)
    {f : (EuclideanSpace ℝ (Fin 3)) →L[ℝ] ℝ} (hf : f ≠ 0) (t : ℝ)
    {ℓ : (EuclideanSpace ℝ (Fin 3)) →L[ℝ] ℝ} (lam : ℝ) :
    IsPreconnected (frontier K ∩ {y : EuclideanSpace ℝ (Fin 3) | f y = t}
      ∩ {y : EuclideanSpace ℝ (Fin 3) | ℓ y ≤ lam}) := by
  classical
  set P : Set (EuclideanSpace ℝ (Fin 3)) := {y | f y = t} with hP
  have hPc : Convex ℝ P := (convex_singleton t).linear_preimage f.toLinearMap
  by_cases hne : (P ∩ interior K).Nonempty
  · obtain ⟨u, huP, huInt⟩ := hne
    have huf : f u = t := huP
    -- the kernel of `f` is a `2`-dimensional space
    set V : Submodule ℝ (EuclideanSpace ℝ (Fin 3)) := LinearMap.ker f.toLinearMap with hV
    have hmemV : ∀ x : EuclideanSpace ℝ (Fin 3), x ∈ V ↔ f x = 0 := by
      intro x
      rw [hV]
      exact LinearMap.mem_ker
    have hVfin : Module.finrank ℝ V = 2 := by
      have hsurj : Function.Surjective f := by
        obtain ⟨v₀, hv₀⟩ : ∃ v₀ : EuclideanSpace ℝ (Fin 3), f v₀ ≠ 0 := by
          by_contra h
          push_neg at h
          exact hf (ContinuousLinearMap.ext h)
        intro s
        exact ⟨(s / f v₀) • v₀, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hv₀]⟩
      have hrange : LinearMap.range f.toLinearMap = ⊤ := LinearMap.range_eq_top.mpr hsurj
      have h1 : Module.finrank ℝ (LinearMap.range f.toLinearMap) = 1 := by
        rw [hrange]
        exact (LinearEquiv.finrank_eq (Submodule.topEquiv (R := ℝ) (M := ℝ))).trans
          (Module.finrank_self ℝ)
      have h2 := LinearMap.finrank_range_add_finrank_ker f.toLinearMap
      have h3 : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
      rw [← hV] at h2
      rw [h1, h3] at h2
      omega
    -- the parametrisation of the affine plane `P` by the kernel
    set Φ : V → EuclideanSpace ℝ (Fin 3) := fun v => u + (v : EuclideanSpace ℝ (Fin 3)) with hΦ
    have hΦcont : Continuous Φ := by
      rw [hΦ]
      fun_prop
    have hΦmem : ∀ v : V, f (Φ v) = t := by
      intro v
      have hv : f (v : EuclideanSpace ℝ (Fin 3)) = 0 := (hmemV _).mp v.2
      rw [hΦ]
      simp only [map_add, huf, hv, add_zero]
    have hΦiso : ∀ v w : V, ‖Φ v - Φ w‖ = ‖v - w‖ := by
      intro v w
      have h1 : Φ v - Φ w = ((v - w : V) : EuclideanSpace ℝ (Fin 3)) := by
        rw [hΦ]
        rw [add_sub_add_left_eq_sub, Submodule.coe_sub]
      rw [h1, Submodule.norm_coe]
    -- the image of a ball in `V` is the trace of a ball in `P`
    have hball_img : ∀ (w : V) (ε : ℝ), Φ '' {v : V | ‖v - w‖ < ε}
        = {y : EuclideanSpace ℝ (Fin 3) | f y = t ∧ ‖y - Φ w‖ < ε} := by
      intro w ε
      ext y
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact ⟨hΦmem v, by rw [hΦiso v w]; exact hv⟩
      · rintro ⟨hyf, hyε⟩
        have hyV : y - u ∈ V := (hmemV _).mpr (by rw [map_sub, hyf, huf, sub_self])
        refine ⟨⟨y - u, hyV⟩, ?_, ?_⟩
        · show ‖(⟨y - u, hyV⟩ : V) - w‖ < ε
          rw [← hΦiso ⟨y - u, hyV⟩ w]
          have h1 : Φ ⟨y - u, hyV⟩ = y := by
            rw [hΦ]
            simp
          rw [h1]
          exact hyε
        · rw [hΦ]
          simp
    -- the slice of `K`
    set K' : Set V := Φ ⁻¹' K with hK'
    have hK'c : Convex ℝ K' := by
      intro v hv w hw a b ha hb hab
      have hvK : u + (v : EuclideanSpace ℝ (Fin 3)) ∈ K := hv
      have hwK : u + (w : EuclideanSpace ℝ (Fin 3)) ∈ K := hw
      have hkey : u + ((a • v + b • w : V) : EuclideanSpace ℝ (Fin 3))
          = a • (u + (v : EuclideanSpace ℝ (Fin 3))) + b • (u + (w : EuclideanSpace ℝ (Fin 3))) := by
        simp only [Submodule.coe_add, Submodule.coe_smul]
        rw [show u + (a • (v : EuclideanSpace ℝ (Fin 3)) + b • (w : EuclideanSpace ℝ (Fin 3)))
            = (a + b) • u
              + (a • (v : EuclideanSpace ℝ (Fin 3)) + b • (w : EuclideanSpace ℝ (Fin 3)))
            from by rw [hab, one_smul]]
        rw [add_smul, smul_add, smul_add]
        abel
      show u + ((a • v + b • w : V) : EuclideanSpace ℝ (Fin 3)) ∈ K
      rw [hkey]
      exact hKc hvK hwK ha hb hab
    have hK'k : IsCompact K' := by
      refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨hKcomp.isClosed.preimage hΦcont, ?_⟩
      rw [Metric.isBounded_iff]
      obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp hKcomp.isBounded
      refine ⟨C, ?_⟩
      intro v hv w hw
      rw [hK', Set.mem_preimage] at hv hw
      rw [dist_eq_norm, ← hΦiso v w, ← dist_eq_norm]
      exact hC hv hw
    have hK'int : (interior K').Nonempty := by
      obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp huInt)
      refine ⟨0, ?_⟩
      rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
      refine ⟨ε, hε, ?_⟩
      intro v hv
      rw [hK', Set.mem_preimage, hΦ]
      apply hεsub
      rw [Metric.mem_ball]
      have h1 : (u + (v : EuclideanSpace ℝ (Fin 3))) - u = (v : EuclideanSpace ℝ (Fin 3)) := by
        abel
      rw [dist_eq_norm, h1]
      have hv' : ‖v‖ < ε := by
        rw [Metric.mem_ball, dist_zero_right] at hv
        exact hv
      rw [Submodule.norm_coe]
      exact hv'
    -- the wall functional on the slice
    set ℓ' : V →L[ℝ] ℝ := ℓ.comp (Submodule.subtypeL V) with hℓ'
    have hℓ'apply : ∀ v : V, ℓ' v = ℓ (v : EuclideanSpace ℝ (Fin 3)) := fun v => by
      rw [hℓ', ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
    have hwall : ∀ v : V, ℓ' v ≤ lam - ℓ u ↔ ℓ (Φ v) ≤ lam := by
      intro v
      rw [hℓ'apply, hΦ]
      simp only [map_add]
      constructor <;> intro h <;> linarith
    -- the two halves of the frontier identification
    have hfront_sub : Φ '' (frontier K' ∩ {v : V | ℓ' v ≤ lam - ℓ u})
        ⊆ frontier K ∩ P ∩ {y : EuclideanSpace ℝ (Fin 3) | ℓ y ≤ lam} := by
      rintro y ⟨w, ⟨hwfr, hwℓ⟩, rfl⟩
      rw [Set.mem_ofPred_eq] at hwℓ
      have hwK : w ∈ K' := hK'k.isClosed.frontier_subset hwfr
      have hwInt : w ∉ interior K' := by
        rw [hK'k.isClosed.frontier_eq] at hwfr
        exact hwfr.2
      refine ⟨⟨?_, hΦmem w⟩, ?_⟩
      · rw [hKcomp.isClosed.frontier_eq]
        refine ⟨hwK, ?_⟩
        intro hInt
        obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hInt)
        exact hwInt (by
          rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
          refine ⟨ε, hε, ?_⟩
          intro v hv
          rw [hK', Set.mem_preimage]
          apply hεsub
          rw [Metric.mem_ball, dist_eq_norm, hΦiso v w, ← dist_eq_norm]
          exact hv)
      · show ℓ (Φ w) ≤ lam
        rw [← hwall w]
        exact hwℓ
    have hfront_sup : frontier K ∩ P ∩ {y : EuclideanSpace ℝ (Fin 3) | ℓ y ≤ lam}
        ⊆ Φ '' (frontier K' ∩ {v : V | ℓ' v ≤ lam - ℓ u}) := by
      rintro y ⟨⟨hyfr, hyP⟩, hyℓ⟩
      rw [Set.mem_ofPred_eq] at hyℓ
      have hyK : y ∈ K := hKcomp.isClosed.frontier_subset hyfr
      have hyInt : y ∉ interior K := by
        rw [hKcomp.isClosed.frontier_eq] at hyfr
        exact hyfr.2
      have hyV : y - u ∈ V := (hmemV _).mpr (by rw [map_sub, hyP, huf, sub_self])
      have hΦy : Φ ⟨y - u, hyV⟩ = y := by
        rw [hΦ]
        simp
      refine ⟨⟨y - u, hyV⟩, ⟨?_, ?_⟩, hΦy⟩
      · rw [hK'k.isClosed.frontier_eq]
        refine ⟨by rw [hK', Set.mem_preimage, hΦy]; exact hyK, ?_⟩
        intro hInt
        obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hInt)
        refine hyInt (mem_interior_of_slice_ball hKc hf huf huInt hyP ⟨ε, hε, ?_⟩)
        intro v hvf hvd
        have hvV : v - u ∈ V := (hmemV _).mpr (by rw [map_sub, hvf, huf, sub_self])
        have hvb : (⟨v - u, hvV⟩ : V) ∈ Metric.ball (⟨y - u, hyV⟩ : V) ε := by
          rw [Metric.mem_ball, dist_eq_norm, ← hΦiso ⟨v - u, hvV⟩ ⟨y - u, hyV⟩]
          have h1 : Φ ⟨v - u, hvV⟩ = v := by rw [hΦ]; simp
          rw [h1, hΦy]
          exact hvd
        have hmem : (⟨v - u, hvV⟩ : V) ∈ K' := hεsub hvb
        rw [hK', Set.mem_preimage] at hmem
        have h1 : Φ ⟨v - u, hvV⟩ = v := by rw [hΦ]; simp
        rwa [h1] at hmem
      · show ℓ' (⟨y - u, hyV⟩ : V) ≤ lam - ℓ u
        rw [hwall]
        rw [hΦy]
        exact hyℓ
    have hfront_eq : Φ '' (frontier K' ∩ {v : V | ℓ' v ≤ lam - ℓ u})
        = frontier K ∩ P ∩ {y : EuclideanSpace ℝ (Fin 3) | ℓ y ≤ lam} :=
      Set.Subset.antisymm hfront_sub hfront_sup
    rw [← hfront_eq]
    exact (isPreconnected_frontier_inter_halfspace_2d_aux hVfin hK'c hK'k hK'int
      (ℓ := ℓ') (lam := lam - ℓ u)).image Φ hΦcont.continuousOn
  · -- the plane misses the interior: the slice lies in the frontier
    have hsub : K ∩ P ⊆ frontier K := by
      intro x ⟨hxK, hxP⟩
      rw [hKcomp.isClosed.frontier_eq]
      exact ⟨hxK, fun hxInt => hne ⟨x, hxP, hxInt⟩⟩
    have hset : frontier K ∩ P ∩ {y : EuclideanSpace ℝ (Fin 3) | ℓ y ≤ lam}
        = K ∩ P ∩ {y : EuclideanSpace ℝ (Fin 3) | ℓ y ≤ lam} := by
      refine Set.Subset.antisymm ?_ ?_
      · rintro y ⟨⟨hyfr, hyP⟩, hyℓ⟩
        exact ⟨⟨hKcomp.isClosed.frontier_subset hyfr, hyP⟩, hyℓ⟩
      · rintro y ⟨⟨hyK, hyP⟩, hyℓ⟩
        exact ⟨⟨hsub ⟨hyK, hyP⟩, hyP⟩, hyℓ⟩
    rw [hset]
    exact ((hKc.inter hPc).inter
      (convex_halfSpace_le ℓ.toLinearMap.isLinear lam)).isPreconnected

end

end Work.Drive.Mono
