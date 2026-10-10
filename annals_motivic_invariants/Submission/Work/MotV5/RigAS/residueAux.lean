import Mathlib
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Pointwise

/-!
# Auxiliary residue-field lemmas for the residue lifting argument

Given a field extension `F → L` and a valuation `V` of `L`, we write `O_F ⊆ O_V` for the two
valuation rings, `κ(V) = O_V/𝔪_V` for the residue field of `V`, and `κ(v) ⊆ κ(V)` for the image of
`O_F` (the residue field of the restricted valuation).

The two technical statements proved here are

* `linearIndependent_of_lift`: `κ(v)`-linearly independent residue classes lift to `F`-linearly
  independent elements of `L` (clear denominators, then reduce);
* `residueDegree_le`: consequently `[κ(V) : κ(v)] ≤ [L : F]`.
-/

namespace ResidueAux

/-- For an element `y` of the valuation ring of `v`, being a unit is equivalent to `v y = 1`. -/
theorem isUnit_iff_val_eq_one {K : Type*} [Field K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (y : ↥(v.valuationSubring)) : IsUnit y ↔ v (y : K) = 1 := by
  have hle : v (y : K) ≤ 1 := (Valuation.mem_valuationSubring_iff v _).mp y.2
  have h1 : IsUnit y ↔ (IsLocalRing.residue ↥(v.valuationSubring)) y ≠ 0 :=
    (IsLocalRing.residue_ne_zero_iff_isUnit y).symm
  rw [h1]
  constructor
  · intro h
    exact le_antisymm hle (not_lt.mp fun hlt => h ((IsLocalRing.residue_eq_zero_iff y).mpr
      ((Valuation.mem_maximalIdeal_iff K v).mpr hlt)))
  · intro h h0
    rw [IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff K v, h] at h0
    exact lt_irrefl _ h0

/-- The valuation ring of `F` induced by `V` along `F → L`. -/
noncomputable def baseVS (F : Type*) [Field F] {L : Type*} [Field L] [Algebra F L] {Γ : Type*}
    [LinearOrderedCommGroupWithZero Γ] (V : Valuation L Γ) : ValuationSubring F :=
  (V.comap (algebraMap F L : F →+* L)).valuationSubring

theorem mem_baseVS {F : Type*} [Field F] {L : Type*} [Field L] [Algebra F L] {Γ : Type*}
    [LinearOrderedCommGroupWithZero Γ] (V : Valuation L Γ) (x : F) :
    x ∈ baseVS F V ↔ V (algebraMap F L x) ≤ 1 := by
  rw [baseVS, Valuation.mem_valuationSubring_iff, Valuation.comap_apply]

/-- The inclusion of the base valuation ring into `V.valuationSubring`. -/
noncomputable def baseIncl (F : Type*) [Field F] {L : Type*} [Field L] [Algebra F L] {Γ : Type*}
    [LinearOrderedCommGroupWithZero Γ] (V : Valuation L Γ) :
    ↥(baseVS F V) →+* ↥(V.valuationSubring) where
  toFun x := ⟨algebraMap F L (x : F), (mem_baseVS V (x : F)).mp x.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ _ _)

@[simp]
theorem baseIncl_apply {F : Type*} [Field F] {L : Type*} [Field L] [Algebra F L] {Γ : Type*}
    [LinearOrderedCommGroupWithZero Γ] (V : Valuation L Γ) (x : ↥(baseVS F V)) :
    ((baseIncl F V x : ↥(V.valuationSubring)) : L) = algebraMap F L (x : F) := rfl

instance baseIncl_localHom (F : Type*) [Field F] {L : Type*} [Field L] [Algebra F L]
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (V : Valuation L Γ) :
    IsLocalHom (baseIncl F V) where
  map_nonunit x hx := by
    have h1 : V (algebraMap F L (x : F)) = 1 := by
      have h2 := (isUnit_iff_val_eq_one V (baseIncl F V x)).mp hx
      rwa [baseIncl_apply] at h2
    refine (isUnit_iff_val_eq_one (V.comap (algebraMap F L : F →+* L)) x).mpr ?_
    rw [Valuation.comap_apply]
    exact h1

/-- The residue field `κ(v)` of the base, as a subfield of `κ(V)`. -/
noncomputable def kappaBase (F : Type*) [Field F] {L : Type*} [Field L] [Algebra F L] {Γ : Type*}
    [LinearOrderedCommGroupWithZero Γ] (V : Valuation L Γ) :
    Subfield (IsLocalRing.ResidueField ↥(V.valuationSubring)) :=
  (IsLocalRing.ResidueField.map (baseIncl F V)).fieldRange

/-- Membership in `κ(v)`: a residue class comes from an integral element of `F`. -/
theorem mem_kappaBase {F : Type*} [Field F] {L : Type*} [Field L] [Algebra F L] {Γ : Type*}
    [LinearOrderedCommGroupWithZero Γ] (V : Valuation L Γ)
    (c : IsLocalRing.ResidueField ↥(V.valuationSubring)) :
    c ∈ kappaBase F V ↔ ∃ x : ↥(baseVS F V), IsLocalRing.residue _ (baseIncl F V x) = c := by
  constructor
  · intro hc
    obtain ⟨d, hd⟩ := RingHom.mem_fieldRange.mp hc
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective (R := ↥(baseVS F V)) d
    refine ⟨y, ?_⟩
    rw [← hd]
    exact congrFun (congrArg DFunLike.coe (IsLocalRing.ResidueField.map_comp_residue (baseIncl F V))) y
  · rintro ⟨y, rfl⟩
    exact RingHom.mem_fieldRange.mpr ⟨IsLocalRing.residue _ y,
      congrFun (congrArg DFunLike.coe (IsLocalRing.ResidueField.map_comp_residue (baseIncl F V))) y⟩

/-- **Lifting of linearly independent residue classes.**  If `b` is a `κ(v)`-linearly independent
family in `κ(V)` and `z` is a family of `V`-integral lifts of `b`, then `z` is `F`-linearly
independent in `L`. -/
theorem linearIndependent_of_lift {F : Type*} [Field F] {L : Type*} [Field L] [Algebra F L]
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (V : Valuation L Γ) {ι : Type*}
    (b : ι → IsLocalRing.ResidueField ↥(V.valuationSubring))
    (z : ι → ↥(V.valuationSubring)) (hz : ∀ i, IsLocalRing.residue _ (z i) = b i)
    (hb : LinearIndependent ↥(kappaBase F V) b) :
    LinearIndependent F (fun i => ((z i : ↥(V.valuationSubring)) : L)) := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum i₀ hi₀
  by_contra hcon
  have hne : (s.filter fun i => g i ≠ 0).Nonempty :=
    ⟨i₀, Finset.mem_filter.mpr ⟨hi₀, hcon⟩⟩
  obtain ⟨j, hjmem, hmax⟩ := Finset.exists_max_image (s.filter fun i => g i ≠ 0)
    (fun i => V (algebraMap F L (g i))) hne
  obtain ⟨hjs, hjnz⟩ := Finset.mem_filter.mp hjmem
  have hgj : algebraMap F L (g j) ≠ 0 := by simp [hjnz]
  have hposj : 0 < V (algebraMap F L (g j)) :=
    lt_of_le_of_ne' (zero_le) ((Valuation.ne_zero_iff V).mpr hgj)
  have hbound : ∀ i ∈ s, V (algebraMap F L (g i)) ≤ V (algebraMap F L (g j)) := by
    intro i his
    rcases eq_or_ne (g i) 0 with h | h
    · rw [h, map_zero, map_zero]; exact zero_le
    · exact hmax i (Finset.mem_filter.mpr ⟨his, h⟩)
  set d : ι → F := fun i => if i ∈ s then g i / g j else 0 with hd
  have hdi : ∀ i ∈ s, d i = g i / g j := by
    intro i hi; rw [hd]; simp only [hi, if_pos]
  have hdj : d j = 1 := by rw [hdi j hjs, div_self hjnz]
  have hdmem : ∀ i, d i ∈ baseVS F V := by
    intro i
    by_cases hi : i ∈ s
    · rw [mem_baseVS, hdi i hi, map_div₀, Valuation.map_div, div_le_one₀ hposj]
      exact hbound i hi
    · rw [hd]; simp only [hi, if_neg, not_false_eq_true]
      rw [mem_baseVS, map_zero, map_zero]
      exact zero_le
  set c : ι → ↥(V.valuationSubring) := fun i => baseIncl F V ⟨d i, hdmem i⟩ with hcdef
  have hcval : ∀ i, ((c i : ↥(V.valuationSubring)) : L) = algebraMap F L (d i) := by
    intro i; simp [hcdef]
  have hsumzero : (∑ i ∈ s, c i * z i) = 0 := by
    apply Subtype.ext
    change ((∑ i ∈ s, c i * z i : ↥(V.valuationSubring)) : L) = 0
    have h1 : ((∑ i ∈ s, c i * z i : ↥(V.valuationSubring)) : L)
        = ∑ i ∈ s, algebraMap F L (d i) * (z i : L) := by
      refine (map_sum (Subring.subtype (V.valuationSubring).toSubring) (fun i => c i * z i) s).trans ?_
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [map_mul]
      exact congrArg₂ (· * ·) (hcval i) rfl
    rw [h1]
    have h2 : ∑ i ∈ s, algebraMap F L (d i) * (z i : L)
        = ∑ i ∈ s, (g j)⁻¹ • (g i • ((z i : ↥(V.valuationSubring)) : L)) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hdi i hi, Algebra.smul_def, Algebra.smul_def, map_div₀, map_inv₀, div_eq_mul_inv]
      first | refl_ring1 | ring
    rw [h2, ← Finset.smul_sum, hsum, smul_zero]
  have hmemc : ∀ i, IsLocalRing.residue _ (c i) ∈ kappaBase F V := by
    intro i
    rw [mem_kappaBase]
    exact ⟨⟨d i, hdmem i⟩, rfl⟩
  have hres : (∑ i ∈ s, IsLocalRing.residue _ (c i) * b i) = 0 := by
    have h := congrArg (IsLocalRing.residue ↥(V.valuationSubring)) hsumzero
    rw [map_zero] at h
    calc (∑ i ∈ s, IsLocalRing.residue _ (c i) * b i)
        = ∑ i ∈ s, IsLocalRing.residue _ (c i * z i) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [map_mul, hz i]
      _ = IsLocalRing.residue _ (∑ i ∈ s, c i * z i) :=
          (map_sum (IsLocalRing.residue ↥(V.valuationSubring)) (fun i => c i * z i) s).symm
      _ = 0 := h
  have hres' : (∑ i ∈ s, (⟨IsLocalRing.residue _ (c i), hmemc i⟩ : ↥(kappaBase F V)) • b i) = 0 := by
    rw [← hres]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Algebra.smul_def, Subfield.algebraMap_ofSubfield]
    rfl
  have hlin := hb
  rw [linearIndependent_iff'] at hlin
  have key := hlin s (fun i => ⟨IsLocalRing.residue _ (c i), hmemc i⟩) hres' j hjs
  have hcj1 : IsLocalRing.residue _ (c j) = 1 := by
    have h1 : (⟨d j, hdmem j⟩ : ↥(baseVS F V)) = 1 := Subtype.ext hdj
    have h2 : c j = 1 := by simp [hcdef, h1]
    rw [h2, map_one]
  have h0 : IsLocalRing.residue _ (c j) = 0 := by
    simpa using congrArg Subtype.val key
  rw [hcj1] at h0
  exact one_ne_zero h0

/-- **The residue degree bound.**  If `L/F` is a finite extension of degree `n` (`n ≠ 0`), then the
residue field extension `κ(V)/κ(v)` has degree at most `n`. -/
theorem residueDegree_le {F : Type*} [Field F] {L : Type*} [Field L] [Algebra F L] {Γ : Type*}
    [LinearOrderedCommGroupWithZero Γ] (V : Valuation L Γ) {n : ℕ} (hn : n ≠ 0)
    (hFL : Module.finrank F L = n) :
    Module.finrank ↥(kappaBase F V) (IsLocalRing.ResidueField ↥(V.valuationSubring)) ≤ n := by
  have hrank : Module.rank F L = (n : Cardinal) := (Cardinal.toNat_eq_iff hn).mp hFL
  haveI : Module.Finite F L := Module.finite_of_rank_eq_nat hrank
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨b, hb⟩ := exists_linearIndependent_of_le_finrank (R := ↥(kappaBase F V))
    (M := IsLocalRing.ResidueField ↥(V.valuationSubring)) (n := n + 1) (by omega)
  choose z hz using fun i => IsLocalRing.residue_surjective (b i)
  have hzlin := linearIndependent_of_lift (F := F) V b z hz hb
  have hle := hzlin.fintype_card_le_finrank
  rw [hFL] at hle
  simp only [Fintype.card_fin] at hle
  omega

end ResidueAux
