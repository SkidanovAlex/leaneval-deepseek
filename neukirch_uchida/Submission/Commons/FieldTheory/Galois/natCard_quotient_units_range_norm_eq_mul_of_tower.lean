import Mathlib
import Submission.Commons.FieldTheory.Galois.natCard_quotient_units_range_norm_le_mul_tower

namespace Commons.FieldTheory.Galois

open scoped Pointwise

/-- **Abstract group-theoretic core of the tower formula.**

Let `f : H →* G` and `g : J →* H` be group homomorphisms (all groups abelian here).
Assume every element of `H` killed by `f` lies in the range of `g`, i.e.
`ker f ≤ range g` (this is the "trivial `H¹`" hypothesis).  Then the quotient of the
range of `f` by the image of the range of `g` is in bijection with `H ⧸ range g`:

`|range f ⧸ (range g).map f| = |H ⧸ range g|`.

The bijection is induced by `h ↦ f h`: it is surjective onto `f.range`, and an element
`f h` lies in `(range g).map f` iff `f h = f k` for some `k ∈ range g`, in which case
`h * k⁻¹ ∈ ker f ≤ range g`, so `h ∈ range g`. -/
theorem natCard_range_subgroupOf_quotient_eq_natCard_quotient_range_of_ker_le
    {G H J : Type*} [CommGroup G] [CommGroup H] [CommGroup J]
    (f : H →* G) (g : J →* H) (hker : MonoidHom.ker f ≤ MonoidHom.range g) :
    Nat.card (↥(MonoidHom.range f) ⧸
        (MonoidHom.range (f.comp g)).subgroupOf (MonoidHom.range f)) =
      Nat.card (H ⧸ MonoidHom.range g) := by
  set K : Subgroup H := MonoidHom.range g with hK
  set Mf : Subgroup G := MonoidHom.range f with hMf
  set Mfg : Subgroup G := MonoidHom.range (f.comp g) with hMfg
  have hMfg_map : Mfg = K.map f := by
    rw [hMfg, hK, MonoidHom.range_comp]
  let φ : H →* ↥Mf := f.codRestrict Mf (fun x => MonoidHom.mem_range.mpr ⟨x, rfl⟩)
  have hφ : ∀ x : H, (φ x : G) = f x := fun x => rfl
  let Φ : H →* (↥Mf ⧸ Mfg.subgroupOf Mf) :=
    (QuotientGroup.mk' (Mfg.subgroupOf Mf)).comp φ
  have hΦ : ∀ x : H, Φ x = QuotientGroup.mk (φ x) :=
    fun x => QuotientGroup.mk'_apply (Mfg.subgroupOf Mf) (φ x)
  have hsurj : Function.Surjective Φ := by
    intro z
    obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective (Mfg.subgroupOf Mf) z
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp q.2
    refine ⟨x, ?_⟩
    have hφx : φ x = q := Subtype.ext (by rw [hφ]; exact hx)
    rw [hΦ, hφx]
    rw [← QuotientGroup.mk'_apply]
  have hkerΦ : Φ.ker = K := by
    ext x
    rw [MonoidHom.mem_ker, hΦ, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, hφ]
    constructor
    · intro hx
      rw [hMfg_map] at hx
      obtain ⟨y, hy_mem, hy⟩ := Subgroup.mem_map.mp hx
      have hxy : x * y⁻¹ ∈ MonoidHom.ker f := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hy, mul_inv_cancel]
      have hxyK : x * y⁻¹ ∈ K := hker hxy
      have : x = (x * y⁻¹) * y := by group
      rw [this]
      exact K.mul_mem hxyK hy_mem
    · intro hx
      rw [hMfg_map]
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  have e := QuotientGroup.quotientKerEquivOfSurjective Φ hsurj
  have e2 : H ⧸ Φ.ker ≃* H ⧸ K := QuotientGroup.quotientMulEquivOfEq hkerΦ
  exact ((Nat.card_congr e.toEquiv).symm.trans (Nat.card_congr e2.toEquiv))

/-- **Multiplicativity of the norm-unit quotient cardinality along a tower of fields.**

For a tower `F ⊆ M ⊆ E` of finite-dimensional field extensions, if every `M`-unit of
`F`-norm `1` is the `E/M`-norm of an `E`-unit (the "trivial `H¹`" hypothesis `h`), then the
cardinality of the cokernel of the norm `N_{E/F}` on units is the product of the cardinalities
of the cokernels of `N_{M/F}` and `N_{E/M}`:

`|Fˣ ⧸ N_{E/F}(Eˣ)| = |Fˣ ⧸ N_{M/F}(Mˣ)| · |Mˣ ⧸ N_{E/M}(Eˣ)|`.

The proof composes the abstract core lemma `natCard_range_subgroupOf_quotient_eq_natCard_quotient_range_of_ker_le`
(from which `|Mˣ ⧸ N_{E/M}(Eˣ)| = |N_{M/F}(Mˣ) ⧸ N_{E/F}(Eˣ)|`) with the subgroup index
multiplicativity `relIndex_mul_index` for `N_{E/F}(Eˣ) ≤ N_{M/F}(Mˣ)` inside `Fˣ`. It is the
`Nat.card` (no finiteness hypothesis) form of the Herbrand-quotient multiplicativity. -/
theorem natCard_quotient_units_range_norm_eq_mul_of_tower
    {F M E : Type*} [Field F] [Field M] [Field E] [Algebra F M] [Algebra F E] [Algebra M E]
    [IsScalarTower F M E] [FiniteDimensional F M] [FiniteDimensional M E]
    [FiniteDimensional F E]
    (h : ∀ m : Mˣ, Algebra.norm F (m : M) = 1 →
      ∃ w : Eˣ, Algebra.norm M (w : E) = (m : M)) :
    Nat.card (Fˣ ⧸ MonoidHom.range (Units.map (Algebra.norm F : E →* F))) =
      Nat.card (Fˣ ⧸ MonoidHom.range (Units.map (Algebra.norm F : M →* F))) *
        Nat.card (Mˣ ⧸ MonoidHom.range (Units.map (Algebra.norm M : E →* M))) := by
  let N1 : Eˣ →* Fˣ := Units.map (Algebra.norm F : E →* F)
  let N2 : Mˣ →* Fˣ := Units.map (Algebra.norm F : M →* F)
  let N3 : Eˣ →* Mˣ := Units.map (Algebra.norm M : E →* M)
  -- the unit norm is transitive on a tower
  have htower : N2.comp N3 = N1 := by
    show (Units.map (Algebra.norm F : M →* F)).comp (Units.map (Algebra.norm M : E →* M)) =
      Units.map (Algebra.norm F : E →* F)
    exact norm_unit_comp_norm_unit
  -- the "trivial H¹" hypothesis in the abstract form `ker N₂ ≤ range N₃`
  have hker : MonoidHom.ker N2 ≤ MonoidHom.range N3 := by
    intro m hm
    rw [MonoidHom.mem_ker] at hm
    have hm' : Algebra.norm F (m : M) = 1 := by
      have hc := congrArg (fun u : Fˣ => (u : F)) hm
      simpa [N2] using hc
    obtain ⟨w, hw⟩ := h m hm'
    exact MonoidHom.mem_range.mpr ⟨w, Units.ext (by simpa [N3] using hw)⟩
  -- hence `N_{E/F}(Eˣ) ≤ N_{M/F}(Mˣ)`, the two subgroups whose indices multiply
  have hle : MonoidHom.range N1 ≤ MonoidHom.range N2 := by
    rw [← htower, MonoidHom.range_comp]
    exact Subgroup.map_le_range N2 N3.range
  -- abstract core: `|N_{M/F}(Mˣ) ⧸ N_{E/F}(Eˣ)| = |Mˣ ⧸ N_{E/M}(Eˣ)|`
  have key := natCard_range_subgroupOf_quotient_eq_natCard_quotient_range_of_ker_le N2 N3 hker
  rw [htower] at key
  calc
    Nat.card (Fˣ ⧸ MonoidHom.range N1)
        = (MonoidHom.range N1).relIndex (MonoidHom.range N2) * (MonoidHom.range N2).index :=
          (Subgroup.relIndex_mul_index hle).symm
    _ = Nat.card (↥(MonoidHom.range N2) ⧸ (MonoidHom.range N1).subgroupOf (MonoidHom.range N2)) *
            Nat.card (Fˣ ⧸ MonoidHom.range N2) := rfl
    _ = Nat.card (Mˣ ⧸ MonoidHom.range N3) * Nat.card (Fˣ ⧸ MonoidHom.range N2) := by rw [key]
    _ = Nat.card (Fˣ ⧸ MonoidHom.range N2) * Nat.card (Mˣ ⧸ MonoidHom.range N3) := by rw [mul_comm]

end Commons.FieldTheory.Galois
