import Mathlib.LinearAlgebra.FiniteDimensional.Defs

namespace Commons.LinearAlgebra.Submodule

/-- **`lem:Establishing that the compositition of derivatives behaves nicely` of
arXiv:2209.04243 (Appendix).** For `V₂ ≤ V₁ ≤ V`, `W₁ ≤ W₂ ≤ W` and `X : W → V`, the
condition `range X ⊇ V₁` and `X⁻¹(V₁) ≤ W₁` is equivalent to: `range X ⊇ V₂`,
`X⁻¹(V₂) ≤ W₂`, and, with `Y = X(W₂,V/V₂) : W₂ → V/V₂`, `range Y ⊇ V₁/V₂` and
`Y⁻¹(V₁/V₂) ≤ W₁`. -/
theorem range_le_range_iff_restrict_quotient {K : Type*} [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (X : W →ₗ[K] V) (V₁ V₂ : Submodule K V) (W₁ W₂ : Submodule K W)
    (hV : V₂ ≤ V₁) (hW : W₁ ≤ W₂) :
    (V₁ ≤ LinearMap.range X ∧ Submodule.comap X V₁ ≤ W₁) ↔
      (V₂ ≤ LinearMap.range X ∧ Submodule.comap X V₂ ≤ W₂ ∧
        Submodule.map (Submodule.mkQ V₂) V₁ ≤
          LinearMap.range ((Submodule.mkQ V₂).comp (X.comp W₂.subtype)) ∧
        Submodule.comap ((Submodule.mkQ V₂).comp (X.comp W₂.subtype))
          (Submodule.map (Submodule.mkQ V₂) V₁) ≤ Submodule.comap W₂.subtype W₁) := by
  set q : V →ₗ[K] V ⧸ V₂ := Submodule.mkQ V₂ with hq
  set Y : W₂ →ₗ[K] V ⧸ V₂ := q.comp (X.comp W₂.subtype) with hY
  have hY_apply : ∀ w : W₂, Y w = q (X (w : W)) := by
    intro w; simp [hY, LinearMap.comp_apply]
  have hq_apply : ∀ v : V, q v = Submodule.Quotient.mk v := by
    intro v; rw [hq]; exact Submodule.mkQ_apply V₂ v
  have hq_eq : ∀ {a b : V}, q a = q b ↔ a - b ∈ V₂ := by
    intro a b
    rw [hq_apply a, hq_apply b, Submodule.Quotient.eq]
  constructor
  · rintro ⟨hrange, hcomap⟩
    refine ⟨hV.trans hrange, (Submodule.comap_mono hV).trans (hcomap.trans hW), ?_, ?_⟩
    · -- range Y ⊇ V₁/V₂
      rintro x hx
      rw [Submodule.mem_map] at hx
      obtain ⟨v, hv, rfl⟩ := hx
      rw [LinearMap.mem_range]
      obtain ⟨w, hw⟩ := LinearMap.mem_range.mp (hrange hv)
      have hw1 : w ∈ Submodule.comap X V₁ := Submodule.mem_comap.mpr (by rw [hw]; exact hv)
      have hw2 : w ∈ W₂ := hW (hcomap hw1)
      refine ⟨⟨w, hw2⟩, ?_⟩
      rw [hY_apply]
      simp [hw]
    · -- Y⁻¹(V₁/V₂) ≤ W₁
      intro w2 hw2
      rw [Submodule.mem_comap] at hw2 ⊢
      rw [Submodule.mem_map] at hw2
      obtain ⟨v, hv, hvY⟩ := hw2
      have hXY : q (X (w2 : W)) = q v := (hY_apply w2).symm.trans hvY.symm
      have hmem2 : X (w2 : W) - v ∈ V₂ := (hq_eq).mp hXY
      have hXw2 : X (w2 : W) ∈ V₁ := by
        have hvX : v - X (w2 : W) ∈ V₂ := by
          have h := Submodule.neg_mem V₂ hmem2
          rwa [neg_sub] at h
        rw [← sub_sub_cancel v (X (w2 : W))]
        exact Submodule.sub_mem V₁ hv (hV hvX)
      have hw1 : (w2 : W) ∈ Submodule.comap X V₁ := Submodule.mem_comap.mpr hXw2
      exact hcomap hw1
  · rintro ⟨hrange₂, hcomap₂, hrangeY, hcomapY⟩
    constructor
    · -- V₁ ≤ range X
      intro v hv
      have hqmem : q v ∈ Submodule.map q V₁ := Submodule.mem_map.mpr ⟨v, hv, rfl⟩
      have hthis := hrangeY hqmem
      rw [LinearMap.mem_range] at hthis
      obtain ⟨w2, hw2⟩ := hthis
      have hXY : q (X (w2 : W)) = q v := (hY_apply w2).symm.trans hw2
      have hmem2 : X (w2 : W) - v ∈ V₂ := (hq_eq).mp hXY
      have h1 : X (w2 : W) ∈ LinearMap.range X := LinearMap.mem_range.mpr ⟨(w2 : W), rfl⟩
      have h2 : X (w2 : W) - v ∈ LinearMap.range X := hrange₂ hmem2
      have h3 : X (w2 : W) - (X (w2 : W) - v) ∈ LinearMap.range X :=
        Submodule.sub_mem _ h1 h2
      rw [sub_sub_cancel] at h3
      exact h3
    · -- comap X V₁ ≤ W₁
      intro w hw
      rw [Submodule.mem_comap] at hw
      have hqmem : q (X w) ∈ Submodule.map q V₁ := Submodule.mem_map.mpr ⟨X w, hw, rfl⟩
      have hthis := hrangeY hqmem
      rw [LinearMap.mem_range] at hthis
      obtain ⟨w2, hw2⟩ := hthis
      have hXY : q (X (w2 : W)) = q (X w) := (hY_apply w2).symm.trans hw2
      have hmem2 : X (w2 : W) - X w ∈ V₂ := (hq_eq).mp hXY
      have hcw : (w2 : W) - w ∈ Submodule.comap X V₂ :=
        Submodule.mem_comap.mpr (by rw [map_sub]; exact hmem2)
      have hW2 : (w2 : W) - w ∈ W₂ := hcomap₂ hcw
      have hwW2 : w ∈ W₂ := by
        have heq : w = (w2 : W) - ((w2 : W) - w) := by rw [sub_sub_cancel]
        rw [heq]
        exact Submodule.sub_mem W₂ w2.2 hW2
      have hmemY : Y ⟨w, hwW2⟩ ∈ Submodule.map q V₁ := by
        rw [hY_apply]
        exact Submodule.mem_map.mpr ⟨X w, hw, rfl⟩
      have hmemY' : (⟨w, hwW2⟩ : W₂) ∈ Submodule.comap Y (Submodule.map q V₁) :=
        Submodule.mem_comap.mpr hmemY
      have hfin := hcomapY hmemY'
      rw [Submodule.mem_comap] at hfin
      simpa using hfin

end Commons.LinearAlgebra.Submodule