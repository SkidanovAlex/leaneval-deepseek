import Mathlib
import Submission.Work.Tower.FrattiniLayer.Basic
import Submission.Work.Tower.FrattiniLayer.kummer_cubic
import Submission.Work.Tower.FrattiniLayer.isCubeIdeal_of_unramified

/-!
# Finiteness of the set of cubic everywhere unramified extensions

Let `L` be a number field containing a primitive cube root of unity `ζ₃`, and let `Ω/L` be any
field extension.  This file proves that the set `cubicUnramifiedSet L Ω` of intermediate fields of
`Ω/L` which are Galois of degree `3` over `L` and unramified at every finite prime is finite,
provided that the parameter set `CubeIdealQuotient L = cubeIdealSubgroup L ⧸ (Lˣ)³` is finite.

The mathematics is classical Kummer theory for the first non-trivial case, in the form provided by
the two imported files:

* every `M ∈ cubicUnramifiedSet L Ω` is `L⟮β⟯` for some `β ∈ M` with `β ^ 3 = α ∈ Lˣ`
  (`kummer_cubic`), and since `M/L` is unramified, `α` lies in `cubeIdealSubgroup L`
  (`isCubeIdeal_of_unramified`);

* if two such generators `β, β'` satisfy `α = α' · c ^ 3` then `β / (β' · c)` is a cube root of
  `1` in `Ω`; as `L` already contains all cube roots of unity, this quotient lies in `L`, whence
  `L⟮β⟯ = L⟮β'⟯`.

Consequently the assignment `M ↦ [α]` is an injection `cubicUnramifiedSet L Ω → CubeIdealQuotient L`
(choices made classically), and finiteness follows.
-/

set_option linter.style.haveILetI false

open NumberField

namespace Work.Tower.FrattiniLayer

section KummerInjectivity

variable {L Ω : Type*} [Field L] [Field Ω] [Algebra L Ω]

/-- **A generator of `M` over `L` inside `↥M` generates `M` inside `Ω`.**  If `β : ↥M` is such that
`L⟮β⟯ = ⊤` in the intermediate field `↥M` of `Ω/L`, then `L⟮β⟯ = M` when `β` is viewed in `Ω`. -/
theorem adjoin_singleton_coe_eq_of_adjoin_eq_top (M : IntermediateField L Ω) (β : ↥M)
    (h : IntermediateField.adjoin L {β} = ⊤) :
    IntermediateField.adjoin L {(β : Ω)} = M := by
  have h1 : ((⊤ : IntermediateField L ↥M).map (IntermediateField.val M)) = M := by
    ext x
    rw [IntermediateField.mem_map]
    constructor
    · rintro ⟨y, -, rfl⟩; exact y.2
    · intro hx; exact ⟨⟨x, hx⟩, trivial, rfl⟩
  have hmap : IntermediateField.adjoin L {(β : Ω)}
      = (IntermediateField.adjoin L {β}).map (IntermediateField.val M) := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  rw [hmap, h, h1]

/-- **The cube roots of `1` in `Ω` all come from `L`.**  If `L` contains a primitive cube root of
unity and `u ^ 3 = 1` in the `L`-algebra `Ω`, then `u` is the image of an element of `L`.  Indeed
`u` is a root of `(X - 1)(X - ζ₃)(X - ζ₃²) = X ^ 3 - 1`, and the three roots `1, ζ₃, ζ₃²` are
already in `L`. -/
theorem exists_algebraMap_of_pow_three_eq_one (hζ : (primitiveRoots 3 L).Nonempty) {u : Ω}
    (hu : u ^ 3 = 1) : ∃ r : L, u = algebraMap L Ω r := by
  obtain ⟨ζ, hζmem⟩ := hζ
  have hζp : IsPrimitiveRoot ζ 3 := (mem_primitiveRoots (by norm_num)).1 hζmem
  have hζsum : 1 + ζ + ζ ^ 2 = 0 := by
    have h := hζp.geom_sum_eq_zero (by norm_num : 1 < 3)
    simpa [Finset.sum_range_succ] using h
  set ζΩ : Ω := algebraMap L Ω ζ with hζΩ
  have hζΩ3 : ζΩ ^ 3 = 1 := by rw [hζΩ, ← map_pow, hζp.pow_eq_one, map_one]
  have hζΩsum : 1 + ζΩ + ζΩ ^ 2 = 0 := by
    have h : algebraMap L Ω (1 + ζ + ζ ^ 2) = 0 := by rw [hζsum, map_zero]
    simpa [hζΩ] using h
  have key : (u - 1) * (u - ζΩ) * (u - ζΩ ^ 2) = u ^ 3 - 1 := by
    have hs : ζΩ + ζΩ ^ 2 = -1 := by linear_combination hζΩsum
    have hp : ζΩ * ζΩ ^ 2 = 1 := by rw [← hζΩ3]; ring
    linear_combination (-u ^ 2 + u) * hs + (u - 1) * hp
  have h0 : (u - 1) * (u - ζΩ) * (u - ζΩ ^ 2) = 0 := by rw [key, hu]; ring
  rcases mul_eq_zero.mp h0 with h | h
  · rcases mul_eq_zero.mp h with h1 | h2
    · exact ⟨1, by rw [map_one]; exact sub_eq_zero.mp h1⟩
    · exact ⟨ζ, by rw [← hζΩ]; exact sub_eq_zero.mp h2⟩
  · exact ⟨ζ ^ 2, by rw [map_pow, ← hζΩ]; exact sub_eq_zero.mp h⟩

/-- **`L⟮·⟯` only depends on the generator modulo `Lˣ`.**  If `x = y * r` with `r ∈ L`, `r ≠ 0`,
then `x` and `y` generate the same intermediate field over `L`. -/
theorem adjoin_singleton_eq_of_eq_mul_algebraMap {x y : Ω} {r : L} (hr : r ≠ 0)
    (h : x = y * algebraMap L Ω r) :
    IntermediateField.adjoin L {x} = IntermediateField.adjoin L {y} := by
  have hrne : algebraMap L Ω r ≠ 0 := fun h0 =>
    hr ((FaithfulSMul.algebraMap_injective L Ω) (by rw [h0, map_zero]))
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    rw [h]
    exact mul_mem (IntermediateField.subset_adjoin L {y} (Set.mem_singleton y))
      (IntermediateField.algebraMap_mem (IntermediateField.adjoin L {y}) r)
  · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    have hy : y = x * algebraMap L Ω r⁻¹ := by
      rw [h, map_inv₀, mul_assoc, mul_inv_cancel₀ hrne, mul_one]
    rw [hy]
    exact mul_mem (IntermediateField.subset_adjoin L {x} (Set.mem_singleton x))
      (IntermediateField.algebraMap_mem (IntermediateField.adjoin L {x}) r⁻¹)

/-- **Kummer classes determine the extension.**  Suppose `β ∈ M` and `β' ∈ M'` generate their
intermediate fields (`L⟮β⟯ = M`, `L⟮β'⟯ = M'`), with `β ^ 3 = a`, `β' ^ 3 = a'` for nonzero
`a, a' ∈ L`, and `a = a' · γ ^ 3` for some nonzero `γ ∈ L`.  Then `M = M'`.

The quotient `β / (β' · γ)` has cube `1`, hence lies in `L` by
`exists_algebraMap_of_pow_three_eq_one`; thus `β` and `β'` differ by a factor from `Lˣ` and
generate the same field. -/
theorem eq_of_pow_three_eq_of_ratio_cube (hζ : (primitiveRoots 3 L).Nonempty)
    {M M' : IntermediateField L Ω} {β : ↥M} {β' : ↥M'} {a a' γ : L}
    (ha : a ≠ 0) (ha' : a' ≠ 0) (hγ : γ ≠ 0)
    (hβ : (β : Ω) ^ 3 = algebraMap L Ω a)
    (hβ' : (β' : Ω) ^ 3 = algebraMap L Ω a')
    (hratio : a = a' * γ ^ 3)
    (hgen : IntermediateField.adjoin L {β} = ⊤)
    (hgen' : IntermediateField.adjoin L {β'} = ⊤) :
    M = M' := by
  have haM : algebraMap L Ω a ≠ 0 := fun h0 =>
    ha ((FaithfulSMul.algebraMap_injective L Ω) (by rw [h0, map_zero]))
  have ha'M : algebraMap L Ω a' ≠ 0 := fun h0 =>
    ha' ((FaithfulSMul.algebraMap_injective L Ω) (by rw [h0, map_zero]))
  have hγM : algebraMap L Ω γ ≠ 0 := fun h0 =>
    hγ ((FaithfulSMul.algebraMap_injective L Ω) (by rw [h0, map_zero]))
  have hβne : (β : Ω) ≠ 0 := fun h0 => haM (by rw [← hβ, h0, zero_pow (by norm_num)])
  have hβ'ne : (β' : Ω) ≠ 0 := fun h0 => ha'M (by rw [← hβ', h0, zero_pow (by norm_num)])
  have h1 : (β : Ω) ^ 3 = ((β' : Ω) * algebraMap L Ω γ) ^ 3 := by
    rw [hβ, hratio, map_mul, map_pow, ← hβ', mul_pow]
  have hd : (β' : Ω) * algebraMap L Ω γ ≠ 0 := mul_ne_zero hβ'ne hγM
  have hu3 : ((β : Ω) / ((β' : Ω) * algebraMap L Ω γ)) ^ 3 = 1 := by
    rw [div_pow, h1, div_self (pow_ne_zero 3 hd)]
  obtain ⟨s, hs⟩ := exists_algebraMap_of_pow_three_eq_one hζ hu3
  have hsne : s ≠ 0 := by
    intro h0
    have hz : (β : Ω) / ((β' : Ω) * algebraMap L Ω γ) = 0 := by rw [hs, h0, map_zero]
    rcases div_eq_zero_iff.mp hz with h | h
    · exact hβne h
    · exact hd h
  have hβeq : (β : Ω) = (β' : Ω) * algebraMap L Ω (γ * s) := by
    rw [map_mul]
    have h2 : (β : Ω) = algebraMap L Ω s * ((β' : Ω) * algebraMap L Ω γ) := by
      rw [← hs, div_mul_cancel₀ _ hd]
    rw [h2]; ring
  rw [← adjoin_singleton_coe_eq_of_adjoin_eq_top M β hgen,
    ← adjoin_singleton_coe_eq_of_adjoin_eq_top M' β' hgen', hβeq]
  exact adjoin_singleton_eq_of_eq_mul_algebraMap (mul_ne_zero hγ hsne) rfl

end KummerInjectivity

/-- **The set of cubic everywhere unramified extensions injects into the finite parameter set.**
If `L` contains a primitive cube root of unity and `CubeIdealQuotient L` is finite, then
`cubicUnramifiedSet L Ω` is finite, for every `L`-algebra `Ω`. -/
theorem finite_cubicUnramifiedSet_of_zeta_of_finite_quotient {L Ω : Type*} [Field L] [NumberField L]
    [Field Ω] [Algebra L Ω] (hζ : (primitiveRoots 3 L).Nonempty)
    (hfin : Finite (Work.Tower.FrattiniLayer.CubeIdealQuotient L)) :
    (Work.Tower.FrattiniLayer.cubicUnramifiedSet L Ω).Finite := by
  classical
  -- Kummer theory attaches to each `M` a generator `βOf M` over `L` with `(βOf M) ^ 3 = αOf M`,
  -- and `αOf M` lies in `cubeIdealSubgroup L` because `M/L` is unramified.
  have key : ∀ M : cubicUnramifiedSet L Ω, ∃ (α : Lˣ) (β : ↥(M : IntermediateField L Ω)),
      β ^ 3 = algebraMap L ↥(M : IntermediateField L Ω) (α : L) ∧
      IntermediateField.adjoin L {β} = ⊤ ∧ α ∈ cubeIdealSubgroup L := by
    intro M
    obtain ⟨hf3, hgal, hunr⟩ := M.2
    haveI : FiniteDimensional L ↥(M : IntermediateField L Ω) :=
      FiniteDimensional.of_finrank_pos (by rw [hf3]; norm_num)
    haveI : IsGalois L ↥(M : IntermediateField L Ω) := hgal
    obtain ⟨α, β, hβ, hadj⟩ :=
      kummer_cubic (L := L) (M := ↥(M : IntermediateField L Ω)) hf3 hζ
    haveI : NumberField ↥(M : IntermediateField L Ω) := NumberField.of_module_finite L _
    exact ⟨α, β, hβ, hadj,
      isCubeIdeal_of_unramified (L := L) (M := ↥(M : IntermediateField L Ω)) α β hβ hunr⟩
  choose αOf βOf hβOf hadjOf hαOf using key
  -- the Kummer relation transported to `Ω`
  have hβΩ : ∀ M : cubicUnramifiedSet L Ω,
      ((βOf M : ↥(M : IntermediateField L Ω)) : Ω) ^ 3 = algebraMap L Ω (αOf M : L) := by
    intro M
    rw [IsScalarTower.algebraMap_apply L ↥(M : IntermediateField L Ω) Ω, ← hβOf M, map_pow,
        IntermediateField.algebraMap_apply]
  -- the map `M ↦ [αOf M]` into `CubeIdealQuotient L` is injective
  have hinj : Function.Injective (fun M : cubicUnramifiedSet L Ω =>
      (QuotientGroup.mk (⟨αOf M, hαOf M⟩ : cubeIdealSubgroup L) : CubeIdealQuotient L)) := by
    intro M M' hMM'
    dsimp only at hMM'
    rw [QuotientGroup.eq] at hMM'
    rw [Subgroup.mem_subgroupOf] at hMM'
    rw [mem_cubePow] at hMM'
    obtain ⟨γ, hγ⟩ := hMM'
    have hγ' : γ ^ 3 = (αOf M)⁻¹ * αOf M' := by simpa using hγ
    have hunit : αOf M = αOf M' * (γ⁻¹) ^ 3 := by
      have h1 : αOf M' = αOf M * γ ^ 3 := by rw [hγ']; group
      rw [h1, inv_pow]; group
    have hratio : (αOf M : L) = (αOf M' : L) * ((γ⁻¹ : Lˣ) : L) ^ 3 := by
      have h := congrArg (fun u : Lˣ => (u : L)) hunit
      simpa using h
    apply Subtype.ext
    exact eq_of_pow_three_eq_of_ratio_cube hζ (a := (αOf M : L)) (a' := (αOf M' : L))
      (γ := ((γ⁻¹ : Lˣ) : L)) (Units.ne_zero _) (Units.ne_zero _) (Units.ne_zero _)
      (hβΩ M) (hβΩ M') hratio (hadjOf M) (hadjOf M')
  exact Set.finite_coe_iff.mp (Finite.of_injective _ hinj)

end Work.Tower.FrattiniLayer
