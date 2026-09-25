import Mathlib
import Submission.Work.ClassFieldTower.Defs
import Submission.Work.ClassFieldTower.two_pow_classGroupTwoRank

/-!
# `Work.ClassFieldTower.classGroupTwoRank_eq_finrank_modN`

`classGroupTwoRank F` is the base-`2` logarithm of the cardinality of `Cl(F)/Cl(F)²`.
The same invariant can be presented as the `𝔽₂`-dimension of `ModN (Additive Cl(F)) 2`,
where `ModN G 2 = G ⧸ 2G` is Mathlib's quotient of an additive group by its doubles.

The two subgroups involved agree: for a commutative group `G`, the subgroup `G²` of squares
of `G`, transported to `Additive G`, is precisely the range of multiplication by `2` on
`Additive G`, i.e. the kernel of the quotient map defining `ModN (Additive G) 2`. Hence the
two quotients are *the same type*, and so the `𝔽₂`-dimension of `ModN (Additive G) 2`
(computed via `Nat.card = 2 ^ finrank` for a finite `𝔽₂`-vector space, together with
`2 ^ log₂ #(G/G²) = #(G/G²)` from the sibling file) is exactly
`Nat.log 2 #(Cl(F)/Cl(F)²) = classGroupTwoRank F`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Classical

noncomputable section

namespace Work.ClassFieldTower

/-! ## 1. The square subgroup is the subgroup `2 • ·` -/

/-- Auxiliary: the set of elements of `Additive G` whose multiplicative image is a square is
the range of doubling on `Additive G`. -/
private lemma toMul_preimage_range_sq (G : Type*) [CommGroup G] :
    (Additive.toMul ⁻¹' Set.range (fun x : G => x ^ 2)) = Set.range (fun a : Additive G => 2 • a) := by
  ext a
  simp only [Set.mem_preimage, Set.mem_range]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨Additive.ofMul y, by simpa [two_nsmul, pow_two] using congrArg Additive.ofMul hy⟩
  · rintro ⟨b, hb⟩
    refine ⟨Additive.toMul b, ?_⟩
    rw [← hb]
    simp [two_nsmul, toMul_add, pow_two]

/-- Auxiliary: the closure of the range of doubling is the range of the linear map `2 • ·`. -/
private lemma closure_range_two_smul (G : Type*) [CommGroup G] :
    AddSubgroup.closure (Set.range (fun a : Additive G => 2 • a))
      = (LinearMap.range (LinearMap.lsmul ℤ (Additive G) 2)).toAddSubgroup := by
  refine le_antisymm ?_ ?_
  · rw [AddSubgroup.closure_le]
    rintro x ⟨a, rfl⟩
    exact LinearMap.mem_range.mpr ⟨a, by rw [LinearMap.lsmul_apply]; exact natCast_zsmul a 2⟩
  · intro x hx
    rw [Submodule.mem_toAddSubgroup, LinearMap.mem_range] at hx
    obtain ⟨a, rfl⟩ := hx
    exact AddSubgroup.subset_closure ⟨a, by rw [LinearMap.lsmul_apply]; exact (natCast_zsmul a 2).symm⟩

/-- **The square subgroup transported to `Additive G` is the subgroup defining `ModN`.**

For a commutative group `G`, the subgroup `G²` of squares of `G`, viewed inside the additive
group `Additive G`, is the range of the multiplication-by-`2` map, i.e. the subgroup by which
`ModN (Additive G) 2 = Additive G ⧸ 2 • ⊤` is quotiented. -/
lemma sqSubgroup_toAddSubgroup_eq (G : Type*) [CommGroup G] :
    (Subgroup.closure (Set.range (fun x : G => x ^ 2))).toAddSubgroup
      = (LinearMap.range (LinearMap.lsmul ℤ (Additive G) 2)).toAddSubgroup := by
  rw [Subgroup.toAddSubgroup_closure, toMul_preimage_range_sq, closure_range_two_smul]

/-! ## 2. Cardinality of `ModN (Additive G) 2` -/

/-- `ModN (Additive G) 2` and the quotient `G ⧸ G²` are *the same type*, hence have the same
cardinality. -/
lemma natCard_modN_two_eq_natCard_sqQuotient (G : Type*) [CommGroup G] :
    Nat.card (ModN (Additive G) 2)
      = Nat.card (G ⧸ Subgroup.closure (Set.range (fun x : G => x ^ 2))) := by
  have h : ModN (Additive G) 2 = (G ⧸ Subgroup.closure (Set.range (fun x : G => x ^ 2))) := by
    show (Additive G ⧸ (LinearMap.range (LinearMap.lsmul ℤ (Additive G) 2)).toAddSubgroup) = _
    rw [← sqSubgroup_toAddSubgroup_eq]
    rfl
  rw [h]

/-! ## 3. The `𝔽₂`-dimension of `ModN (Additive G) 2` -/

/-- **The `𝔽₂`-dimension of `ModN (Additive G) 2` is the base-`2` logarithm of `#(G ⧸ G²)`.**

For a finite commutative group `G`, the `𝔽₂`-vector space `ModN (Additive G) 2 = G/2G` is
finite, so its cardinality is `2` to its dimension; and this cardinality is also the
cardinality of `G ⧸ G²`, whose base-`2` logarithm recovers it because `G ⧸ G²` has exponent
`2`. -/
lemma finrank_modN_two_eq_log_natCard_sqQuotient (G : Type*) [CommGroup G] [Finite G] :
    Module.finrank (ZMod 2) (ModN (Additive G) 2)
      = Nat.log 2 (Nat.card (G ⧸ Subgroup.closure (Set.range (fun x : G => x ^ 2)))) := by
  haveI : Finite (ModN (Additive G) 2) :=
    Finite.of_surjective (ModN.mkQ (G := Additive G) 2) (Submodule.mkQ_surjective _)
  haveI : Module.Finite (ZMod 2) (ModN (Additive G) 2) := Module.Finite.of_finite
  have h1 : 2 ^ Module.finrank (ZMod 2) (ModN (Additive G) 2)
      = Nat.card (ModN (Additive G) 2) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have h2 : Nat.card (ModN (Additive G) 2)
      = Nat.card (G ⧸ Subgroup.closure (Set.range (fun x : G => x ^ 2))) :=
    natCard_modN_two_eq_natCard_sqQuotient G
  have h3 : Nat.card (G ⧸ Subgroup.closure (Set.range (fun x : G => x ^ 2)))
      = 2 ^ Nat.log 2 (Nat.card (G ⧸ Subgroup.closure (Set.range (fun x : G => x ^ 2)))) :=
    (two_pow_log_card_sq_quotient (G := G)).symm
  exact Nat.pow_right_injective (by norm_num) (h1.trans (h2.trans h3))

/-! ## 4. The requested identification -/

/-- **`classGroupTwoRank F` is the `𝔽₂`-dimension of `ModN (Additive Cl(F)) 2`.**

`classGroupTwoRank F` is by definition `log₂ #(Cl(F)/Cl(F)²)`, and `ModN (Additive Cl(F)) 2`
is the same quotient as `Cl(F)/Cl(F)²`; its `𝔽₂`-dimension is that logarithm. -/
theorem classGroupTwoRank_eq_finrank_modN (F : Type*) [Field F] [NumberField F] :
    classGroupTwoRank F = Module.finrank (ZMod 2) (ModN (Additive (ClassGroup (NumberField.RingOfIntegers F))) 2) := by
  have h := finrank_modN_two_eq_log_natCard_sqQuotient (ClassGroup (NumberField.RingOfIntegers F))
  simpa [classGroupTwoRank] using h.symm

end Work.ClassFieldTower
