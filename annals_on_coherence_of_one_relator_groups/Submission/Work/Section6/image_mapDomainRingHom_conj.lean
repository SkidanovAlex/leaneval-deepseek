import Mathlib

namespace Work.Section6

/-- Conjugation by `single t 1` on the image of `mapDomainRingHom K N.subtype` stays inside that
image, when `N` is normal in `H`.  Concretely: for every `f : MonoidAlgebra K N` there is
`h : MonoidAlgebra K N` with
`single t 1 * (K[N] ↪ K[H]) f * single t⁻¹ 1 = (K[N] ↪ K[H]) h`.

This holds because conjugation by `t` permutes the basis elements `single n 1` (`n ∈ N`) to
`single (t * n * t⁻¹) 1`, and `t * n * t⁻¹ ∈ N` by normality; both sides are additive in `f`,
so the identity follows by linear induction on `f`. -/
private lemma keyMapDomain {K : Type} [Field K] {H : Type} [Group H]
    (N : Subgroup H) (hN : N.Normal) (t : H) (f : MonoidAlgebra K N) :
    ∃ h : MonoidAlgebra K N,
      MonoidAlgebra.single t (1 : K) * MonoidAlgebra.mapDomainRingHom K N.subtype f
        * MonoidAlgebra.single t⁻¹ (1 : K)
      = MonoidAlgebra.mapDomainRingHom K N.subtype h := by
  induction f using MonoidAlgebra.induction_linear with
  | zero => exact ⟨0, by simp⟩
  | add f₁ f₂ ih₁ ih₂ =>
      obtain ⟨h₁, hh₁⟩ := ih₁
      obtain ⟨h₂, hh₂⟩ := ih₂
      refine ⟨h₁ + h₂, ?_⟩
      rw [map_add, mul_add, add_mul, hh₁, hh₂, map_add]
  | single n c =>
      refine ⟨MonoidAlgebra.single ⟨t * ↑n * t⁻¹, hN.conj_mem n n.2 t⟩ c, ?_⟩
      rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single,
          MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single,
          MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single]
      simp

theorem image_mapDomainRingHom_conj {K : Type} [Field K] {H : Type} [Group H]
    {U : Type} [Ring U] (φ : MonoidAlgebra K H →+* U)
    (N : Subgroup H) (hN : N.Normal) (t : H) {x : U}
    (hx : x ∈ Set.range (φ.comp (MonoidAlgebra.mapDomainRingHom K N.subtype))) :
    ∃ y ∈ Set.range (φ.comp (MonoidAlgebra.mapDomainRingHom K N.subtype)),
      φ (MonoidAlgebra.single t (1 : K)) * x
        = y * φ (MonoidAlgebra.single t (1 : K)) := by
  obtain ⟨f, rfl⟩ := hx
  obtain ⟨h, hh⟩ := keyMapDomain N hN t f
  refine ⟨φ (MonoidAlgebra.single t (1 : K) * MonoidAlgebra.mapDomainRingHom K N.subtype f
      * MonoidAlgebra.single t⁻¹ (1 : K)), ?_, ?_⟩
  · refine ⟨h, ?_⟩
    change φ (MonoidAlgebra.mapDomainRingHom K N.subtype h) =
      φ (MonoidAlgebra.single t 1 * MonoidAlgebra.mapDomainRingHom K N.subtype f
        * MonoidAlgebra.single t⁻¹ 1)
    rw [hh]
  · change φ (MonoidAlgebra.single t (1 : K)) * φ (MonoidAlgebra.mapDomainRingHom K N.subtype f)
      = φ (MonoidAlgebra.single t 1 * MonoidAlgebra.mapDomainRingHom K N.subtype f
          * MonoidAlgebra.single t⁻¹ 1) * φ (MonoidAlgebra.single t (1 : K))
    rw [← map_mul, ← map_mul]
    congr 1
    have hvu : MonoidAlgebra.single t⁻¹ (1 : K) * MonoidAlgebra.single t (1 : K) = 1 := by
      rw [MonoidAlgebra.single_mul_single, inv_mul_cancel, one_mul, MonoidAlgebra.one_def]
    rw [mul_assoc, hvu, mul_one]

end Work.Section6
