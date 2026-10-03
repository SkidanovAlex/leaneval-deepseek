import Mathlib
import Submission.Work.Rep.Ore.denseRange_of_injective

namespace Work.Rep.Ore

open Work.ORVonNeumann

/-- For `v h ∈ N(G)`: if `v * h` is injective then so is `v`.

Route: let `q ∈ N(G)` be the orthogonal projection onto `ker v`
(`Work.Rep.starProjection_ker_orthogonal_mem_groupVonNeumann`, applied to the operator `v`), so
`ran q = ker v` (`Submodule.range_starProjection`) and, if `q ≠ 0`, `ran (1 - q) = (ker v)ᗮ` is a
proper closed subspace.  `T := (1 - q) * h ∈ N(G)` is not injective, because if it were,
`Work.Rep.Ore.denseRange_of_injective` (imported via `depends_on`) would give it dense range,
contradicting `ran T ⊆ ran (1 - q) ⊊ ⊤`.  So there is `y ≠ 0` with `(1 - q) (h y) = 0`, i.e.
`h y ∈ ker (1 - q) = ran q = ker v` (use `Submodule.ker_starProjection` and read `1 - q` as the
projection onto `(ran q)ᗮ`), whence `(v * h) y = 0` and injectivity of `v * h` forces `y = 0`,
a contradiction.-/
theorem injective_of_mul_injective {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] (v h : ↥(Work.ORVonNeumann.groupVonNeumann G)) (hv : Function.Injective ((v * h : ↥(Work.ORVonNeumann.groupVonNeumann G)) : Work.ORVonNeumann.boundedEnd G)) : Function.Injective (v : Work.ORVonNeumann.boundedEnd G) := by
  classical
  -- The orthogonal projection onto `ker v`, viewed as an element `Q ∈ N(G)`.
  have hqmem : (v : boundedEnd G).ker.starProjection ∈ groupVonNeumann G :=
    Work.Rep.starProjection_ker_orthogonal_mem_groupVonNeumann (v : boundedEnd G) v.2
  let qq : boundedEnd G := (v : boundedEnd G).ker.starProjection
  have hqmem' : qq ∈ groupVonNeumann G := hqmem
  let Q : ↥(groupVonNeumann G) := ⟨qq, hqmem'⟩
  -- `T := (1 - Q) * h` has operator form `(ker v)ᗮ.starProjection * h`.
  have hTcoe : (((1 - Q) * h : ↥(groupVonNeumann G)) : boundedEnd G)
      = ((v : boundedEnd G).kerᗮ).starProjection * (h : boundedEnd G) := by
    rw [Subalgebra.coe_mul, Subalgebra.coe_sub, Subalgebra.coe_one]
    rw [show (1 : boundedEnd G) - (Q : boundedEnd G)
        = ((v : boundedEnd G).kerᗮ).starProjection from
      (Submodule.starProjection_orthogonal' ((v : boundedEnd G).ker)).symm]
  -- If the kernel projection is zero, `v` is injective.
  have hkey : Q = 0 → Function.Injective (v : boundedEnd G) := by
    intro hQ x y hxy
    have hq0 : qq = 0 := congrArg Subtype.val hQ
    have hxy' : (v : boundedEnd G) x - (v : boundedEnd G) y = 0 := sub_eq_zero.mpr hxy
    have hz : x - y ∈ (v : boundedEnd G).ker := by
      rw [LinearMap.mem_ker, map_sub]
      exact hxy'
    have hfix : qq (x - y) = x - y := Submodule.starProjection_eq_self_iff.mpr hz
    have hfix' : x - y = 0 := by
      have := hfix
      rw [hq0] at this
      simpa using this.symm
    exact sub_eq_zero.mp hfix'
  by_cases hQ : Q = 0
  · exact hkey hQ
  · exfalso
    -- `T := (1 - Q) * h ∈ N(G)` is not injective.
    have hTnotinj : ¬ Function.Injective
        (((1 - Q) * h : ↥(groupVonNeumann G)) : boundedEnd G) := by
      intro hTinj
      have hdense : DenseRange (((1 - Q) * h : ↥(groupVonNeumann G)) : boundedEnd G) :=
        denseRange_of_injective _ hTinj
      -- `ker v ≠ ⊥`, because `Q ≠ 0`
      have hkerne : (v : boundedEnd G).ker ≠ ⊥ := by
        intro hb
        apply hQ
        refine Subtype.ext ?_
        show qq = 0
        refine ContinuousLinearMap.ext fun x => ?_
        have hmemx : qq x ∈ (v : boundedEnd G).ker :=
          Submodule.starProjection_apply_mem ((v : boundedEnd G).ker) x
        rw [hb, Submodule.mem_bot] at hmemx
        simpa using hmemx
      -- `(ker v)ᗮ` is a proper subspace
      have hWne : (v : boundedEnd G).kerᗮ ≠ ⊤ := by
        intro hW
        apply hkerne
        refine bot_unique ?_
        exact (Submodule.le_orthogonal_orthogonal ((v : boundedEnd G).ker)).trans
          (le_of_eq (by rw [hW]; simp))
      -- the range of `T` lies in `(ker v)ᗮ`
      have hrange : (((1 - Q) * h : ↥(groupVonNeumann G)) : boundedEnd G).range
          ≤ (v : boundedEnd G).kerᗮ := by
        rintro z ⟨y, rfl⟩
        change (((1 - Q) * h : ↥(groupVonNeumann G)) : boundedEnd G) y
          ∈ (v : boundedEnd G).kerᗮ
        have hzy : (((1 - Q) * h : ↥(groupVonNeumann G)) : boundedEnd G) y
            = ((v : boundedEnd G).kerᗮ).starProjection ((h : boundedEnd G) y) := by
          rw [hTcoe]
          exact mul_apply_eq_comp _ _ _
        rw [hzy]
        exact Submodule.starProjection_apply_mem _ _
      have hcl : closure (Set.range (((1 - Q) * h : ↥(groupVonNeumann G)) : boundedEnd G))
          ⊆ ((v : boundedEnd G).kerᗮ : Set (l2 G)) :=
        closure_minimal (by rintro z ⟨y, rfl⟩; exact hrange ⟨y, rfl⟩)
          (Submodule.isClosed_orthogonal _)
      have htop : (⊤ : Submodule ℂ (l2 G)) ≤ (v : boundedEnd G).kerᗮ := by
        intro z _
        have hz : z ∈ closure (Set.range
            (((1 - Q) * h : ↥(groupVonNeumann G)) : boundedEnd G)) := by
          rw [hdense.closure_range]; trivial
        exact hcl hz
      exact hWne (le_antisymm le_top htop)
    -- extract `y ≠ 0` with `T y = 0`
    obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp hTnotinj
    have hT0 : (((1 - Q) * h : ↥(groupVonNeumann G)) : boundedEnd G) (a - b) = 0 := by
      rw [map_sub, hab, sub_self]
    have hne' : a - b ≠ 0 := sub_ne_zero.mpr hne
    -- `h (a - b) ∈ ker v`
    have hW0 : ((v : boundedEnd G).kerᗮ).starProjection ((h : boundedEnd G) (a - b)) = 0 := by
      have hT0' := hT0
      rw [hTcoe] at hT0'
      exact hT0'
    have h1 : (1 - qq) ((h : boundedEnd G) (a - b)) = 0 := by
      have := hW0
      rwa [Submodule.starProjection_orthogonal' ((v : boundedEnd G).ker)] at this
    have hfix : qq ((h : boundedEnd G) (a - b)) = (h : boundedEnd G) (a - b) := by
      have h2 : (h : boundedEnd G) (a - b) - qq ((h : boundedEnd G) (a - b)) = 0 := by
        simpa only [sub_apply, one_apply_eq_self] using h1
      exact (sub_eq_zero.mp h2).symm
    have hmemker : (h : boundedEnd G) (a - b) ∈ (v : boundedEnd G).ker :=
      Submodule.starProjection_eq_self_iff.mp hfix
    have hV0 : (v : boundedEnd G) ((h : boundedEnd G) (a - b)) = 0 :=
      LinearMap.mem_ker.mp hmemker
    have hvh0 : ((v * h : ↥(groupVonNeumann G)) : boundedEnd G) (a - b) = 0 := by
      have hc : ((v * h : ↥(groupVonNeumann G)) : boundedEnd G) (a - b)
          = (v : boundedEnd G) ((h : boundedEnd G) (a - b)) := by
        rw [Subalgebra.coe_mul]
        exact mul_apply_eq_comp _ _ _
      rw [hc, hV0]
    exact hne' (hv (by rw [hvh0, map_zero]))

end Work.Rep.Ore
