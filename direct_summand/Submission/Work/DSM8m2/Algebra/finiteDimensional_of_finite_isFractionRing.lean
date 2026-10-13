import Mathlib

namespace Work.DSM8m2.Algebra

/-- If `S` is a finite `B`-module and a domain, `L` a field of fractions of `S`, and `K` a field
through which the `B`-algebra structure on `L` factors, then `L` is finite dimensional over `K`.

Concretely: the images in `L` of a finite generating set of `S` over `B` are integral (hence
algebraic) over `K`; the intermediate field `E` they generate together with `K` is therefore
finite dimensional over `K`; since `L` is the field of fractions of the image of `S`, which is
contained in `E`, we get `E = ⊤`. -/
theorem finiteDimensional_of_finite_isFractionRing {B S K L : Type*} [CommRing B] [CommRing S]
    [IsDomain S] [Field K] [Field L] [Algebra B S] [Module.Finite B S] [Algebra B K]
    [Algebra K L] [Algebra B L] [Algebra S L] [IsScalarTower B K L] [IsScalarTower B S L]
    [IsFractionRing S L] : FiniteDimensional K L := by
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := B) (M := S)
  -- Each image of a module generator is integral over `K`.
  have hint : ∀ i, IsIntegral K (algebraMap S L (g i)) := by
    intro i
    have h1 : IsIntegral B (g i) := (Algebra.IsIntegral.of_finite B S).isIntegral (g i)
    have h2 : IsIntegral B (algebraMap S L (g i)) := h1.algebraMap
    exact h2.tower_top
  -- The intermediate field generated over `K` by the images of the generators.
  let E : IntermediateField K L := IntermediateField.adjoin K (Set.range fun i => algebraMap S L (g i))
  have hEfin : FiniteDimensional K E := by
    haveI : Finite (Set.range fun i => algebraMap S L (g i)) := (Set.finite_range _).to_subtype
    apply IntermediateField.finiteDimensional_adjoin
    rintro x ⟨i, rfl⟩
    exact hint i
  -- The image of every element of `S` lies in `E`.
  have hgE : ∀ s : S, algebraMap S L s ∈ E := by
    intro s
    have hs : s ∈ Submodule.span B (Set.range g) := by rw [hg]; trivial
    rw [Submodule.mem_span_range_iff_exists_fun] at hs
    obtain ⟨c, hc⟩ := hs
    rw [← hc, map_sum]
    apply IntermediateField.sum_mem
    intro i _
    have hterm : algebraMap S L (c i • g i)
        = algebraMap K L (algebraMap B K (c i)) * algebraMap S L (g i) := by
      rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply B S L,
        IsScalarTower.algebraMap_apply B K L]
    rw [hterm]
    exact IntermediateField.mul_mem E (IntermediateField.algebraMap_mem E _)
      (IntermediateField.subset_adjoin K _ ⟨i, rfl⟩)
  -- `L` is the field of fractions of the image of `S`, hence `E = ⊤`.
  have hEtop : E = ⊤ := by
    refine le_antisymm le_top ?_
    intro x _
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors S) x
    have hb0 : (b : S) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp b.2
    have hφb0 : algebraMap S L (b : S) ≠ 0 := fun h =>
      hb0 ((IsFractionRing.to_map_eq_zero_iff (R := S) (K := L)).mp h)
    have hx_eq : x = algebraMap S L a * (algebraMap S L (b : S))⁻¹ := by
      rw [← hab, mul_assoc, mul_inv_cancel₀ hφb0, mul_one]
    rw [hx_eq]
    exact IntermediateField.mul_mem E (hgE a) (IntermediateField.inv_mem E (hgE (b : S)))
  haveI : FiniteDimensional K (⊤ : IntermediateField K L) := by
    rw [← hEtop]; exact hEfin
  exact LinearEquiv.finiteDimensional (IntermediateField.topEquiv (F := K) (E := L)).toLinearEquiv

end Work.DSM8m2.Algebra
