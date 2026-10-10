import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FFResidual.Eisenstein

/-- **`1 - π * z` is a unit in a finite algebra over a local ring, for `π` in the maximal ideal.**
(Nakayama: put `a := 1 - algebraMap R S π * z` and `M := S ⧸ Ideal.span {a}`; in `M` the element
`1 = algebraMap R S π * z` lies in `I • ⊤` for `I := Ideal.span {π}`, so `⊤ = I • ⊤` there, and
`Submodule.eq_bot_of_le_smul_of_le_jacobson_bot` with `IsLocalRing.maximalIdeal_le_jacobson` gives
`⊤ = ⊥` in `M`, i.e. `Ideal.span {a} = ⊤`.) -/
theorem isUnit_one_sub_algebraMap_mul {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [Module.Finite R S] {π : R} (hπ : π ∈ IsLocalRing.maximalIdeal R) (z : S) :
    IsUnit (1 - algebraMap R S π * z) := by
  classical
  -- `a` is a unit iff it generates the unit ideal.
  rw [← Ideal.span_singleton_eq_top]
  set J : Ideal S := Ideal.span {1 - algebraMap R S π * z}
  let M := S ⧸ J
  -- In `M := S ⧸ J` the class of `a` vanishes, hence `π` acts invertibly on `M`.
  have hmul : algebraMap R M π * algebraMap S M z = 1 := by
    have h1 : algebraMap S M (1 - algebraMap R S π * z) = 0 := by
      rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton_self _
    have h2 : algebraMap S M 1 - algebraMap S M (algebraMap R S π * z) = 0 := by
      simpa using h1
    simp only [map_mul, map_one, ← IsScalarTower.algebraMap_apply R S M π] at h2
    exact (sub_eq_zero.mp h2).symm
  have hunit : IsUnit (algebraMap R M π) := by
    rw [isUnit_iff_exists_inv]
    exact ⟨algebraMap S M z, hmul⟩
  -- Consequently `𝔪 • ⊤ = ⊤` as `R`-submodules of `M`.
  have hmap : Ideal.map (algebraMap R M) (IsLocalRing.maximalIdeal R) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _
      (Ideal.mem_map_of_mem (algebraMap R M) hπ) hunit
  have htop : IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) = ⊤ := by
    rw [Ideal.smul_top_eq_map, hmap, Submodule.restrictScalars_top]
  -- Nakayama forces `M` to be the zero module.
  have hbot : (⊤ : Submodule R M) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal R) ⊤
      Module.Finite.fg_top (le_of_eq htop.symm) (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  have hsub : Subsingleton (S ⧸ J) :=
    ⟨fun x y => by
      have hx : x = 0 := by
        have hxm : x ∈ (⊥ : Submodule R M) := hbot ▸ Submodule.mem_top
        simpa using hxm
      have hy : y = 0 := by
        have hym : y ∈ (⊥ : Submodule R M) := hbot ▸ Submodule.mem_top
        simpa using hym
      rw [hx, hy]⟩
  exact Ideal.Quotient.subsingleton_iff.mp hsub

end Work.FFResidual.Eisenstein
