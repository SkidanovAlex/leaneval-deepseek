import Mathlib

-- The statement (fixed by the requester) keeps the abelianness hypothesis `hcomm`, which is
-- not needed for this particular argument; silence the "unused variable" linter rather than
-- rename a hypothesis of the requested statement.
set_option linter.unusedVariables false

namespace Work.BSW.Cases

/-- The bijection underlying Bender's `InvertM` (Bender 1974, §3.2): if `F` is abelian,
`k ∈ N_G(F)`, `C_G(k) = K` and `F ⊓ K = ⊥`, then the map `d ↦ d⁻¹ * k * d * k⁻¹` is a bijection
of the finite group `F` onto itself, i.e. every element of `F` is `F`-conjugate (up to `k⁻¹`) to
an element of the form `d⁻¹ * k * d`. -/
theorem bswS32Bijection {G : Type} [Group G] [Finite G] {F K : Subgroup G} {k : G}
    (hcomm : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a)
    (hkN : k ∈ Subgroup.normalizer (F : Set G))
    (hCk : Subgroup.centralizer ({k} : Set G) = K)
    (hd : F ⊓ K = ⊥) :
    ∀ c ∈ F, ∃ d ∈ F, d⁻¹ * k * d * k⁻¹ = c := by
  intro c hc
  -- The map `d ↦ d⁻¹ * k * d * k⁻¹` is a self-map of `F`.
  let f : F → F := fun d =>
    ⟨(d : G)⁻¹ * k * (d : G) * k⁻¹, by
      have hkd : k * (d : G) * k⁻¹ ∈ F :=
        (Subgroup.mem_set_normalizer_iff.mp hkN (d : G)).mp d.2
      have hmul : (d : G)⁻¹ * (k * (d : G) * k⁻¹) ∈ F :=
        mul_mem (inv_mem d.2) hkd
      rwa [show ((d : G)⁻¹ * k * (d : G) * k⁻¹)
            = (d : G)⁻¹ * (k * (d : G) * k⁻¹) by group]⟩
  -- It is injective: the kernel element `d₂ * d₁⁻¹` lies in `F ⊓ C_G(k) = ⊥`.
  have hf : Function.Injective f := by
    intro d1 d2 h
    have hval : (d1 : G)⁻¹ * k * (d1 : G) * k⁻¹
        = (d2 : G)⁻¹ * k * (d2 : G) * k⁻¹ := congrArg Subtype.val h
    have h1 : (d1 : G)⁻¹ * k * (d1 : G) = (d2 : G)⁻¹ * k * (d2 : G) :=
      mul_right_cancel hval
    have hx : (d2 : G) * (d1 : G)⁻¹ * k = k * ((d2 : G) * (d1 : G)⁻¹) := by
      have key : (d2 : G) * (d1 : G)⁻¹ * k * (d1 : G) = k * (d2 : G) := by
        calc (d2 : G) * (d1 : G)⁻¹ * k * (d1 : G)
            = (d2 : G) * ((d1 : G)⁻¹ * k * (d1 : G)) := by group
          _ = (d2 : G) * ((d2 : G)⁻¹ * k * (d2 : G)) := by rw [h1]
          _ = k * (d2 : G) := by group
      calc (d2 : G) * (d1 : G)⁻¹ * k
          = (d2 : G) * (d1 : G)⁻¹ * k * (d1 : G) * (d1 : G)⁻¹ := by group
        _ = k * (d2 : G) * (d1 : G)⁻¹ := by rw [key]
        _ = k * ((d2 : G) * (d1 : G)⁻¹) := by group
    have hxF : (d2 : G) * (d1 : G)⁻¹ ∈ F := mul_mem d2.2 (inv_mem d1.2)
    have hxK : (d2 : G) * (d1 : G)⁻¹ ∈ K := by
      rw [← hCk]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hx
    have hone : (d2 : G) * (d1 : G)⁻¹ = 1 := by
      have hbot : (d2 : G) * (d1 : G)⁻¹ ∈ (⊥ : Subgroup G) := by
        rw [← hd]; exact ⟨hxF, hxK⟩
      simpa using hbot
    apply Subtype.ext
    have hd21 : (d2 : G) = (d1 : G) := by
      calc (d2 : G) = (d2 : G) * (d1 : G)⁻¹ * (d1 : G) := by group
        _ = 1 * (d1 : G) := by rw [hone]
        _ = (d1 : G) := by group
    exact hd21.symm
  -- A self-map of a finite type that is injective is surjective.
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hf
  obtain ⟨d, hd'⟩ := hsurj ⟨c, hc⟩
  exact ⟨d, d.2, by simpa using congrArg Subtype.val hd'⟩

end Work.BSW.Cases
