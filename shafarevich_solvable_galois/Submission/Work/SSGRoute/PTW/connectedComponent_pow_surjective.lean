import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.Work.SSGRoute.PTW.abs_ideleClassGroup_pow_surjective
import Submission.Work.SSGRoute.PTW.archDefs
import Submission.Work.SSGRoute.PTW.compactSpace_ker_abs
import Submission.Work.SSGRoute.PTW.compact_connected_abelian_pow_surjective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The identity component of the idèle class group is `p`-divisible

The identity component `C_K⁰` of the idèle class group of a number field is `p`-divisible.

The proof uses the content (idèle norm) `|·| : C_K →* ℝˣ`, whose kernel `ker |·|` is compact.
Writing `D := C_K⁰` and `H := D ⊓ ker |·|`:

* the archimedean idèle section `archSec w₀ c` (with content `c`) gives, at every positive unit
  `c`, an element of `D` (its class is in the identity component because the section is continuous
  on the connected set of positive units), and hence a splitting of the content direction of `D`;
* consequently every `z ∈ D` can be written as `z = π(archSec w₀ (|z|)) · j` with `j ∈ H`;
* `H` is connected: it is the image of the connected group `D` under the continuous map
  `z ↦ z · π(archSec w₀ |z|)⁻¹` (which fixes `H` pointwise since `|h| = 1` and `archSec w₀ 1 = 1`);
* `H` is compact (it is closed in `ker |·|`, which is compact since `C¹_K` is compact), so the
  general theorem `compact_connected_abelian_pow_surjective` gives the `p`-th root inside `H`;
* the content direction is handled by `pos_units_pow_surjective`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct Pointwise
open NumberField IsDedekindDomain

noncomputable section

namespace Work.SSGRoute.PTW

open NK.GlobalCFT

/-- **The content of an idèle class is positive.** -/
theorem abs_val_pos (K : Type) [Field K] [NumberField K] (z : IdeleClassGroup K) :
    0 < ((IdeleClassGroup.abs K z : ℝˣ) : ℝ) := by
  obtain ⟨a, rfl⟩ := IdeleClassGroup.mk_surjective K z
  rw [IdeleClassGroup.abs_mk]
  exact idele_abs_pos K a

/-- **The content `C_K →* ℝˣ` is continuous.** -/
theorem continuous_absClass' (K : Type) [Field K] [NumberField K] :
    Continuous (IdeleClassGroup.abs K) := by
  refine (QuotientGroup.isQuotientMap_mk (N := Idele.principalSubgroup K)).continuous_iff.mpr ?_
  have h : (⇑(IdeleClassGroup.abs K) ∘ (QuotientGroup.mk : Idele K → IdeleClassGroup K))
      = ⇑(Idele.abs K) := by
    funext a
    simpa only [Function.comp_apply, IdeleClassGroup.mk_apply, QuotientGroup.mk'_apply] using
      (IdeleClassGroup.abs_mk (K := K) a)
  rw [h]
  exact IdeleClassGroup.continuous_abs_aux

/-- **The idèle class group is Hausdorff.** -/
theorem t2Space_ideleClassGroup' (K : Type) [Field K] [NumberField K] :
    T2Space (IdeleClassGroup K) := by
  rw [IsTopologicalGroup.t2Space_iff_one_closed]
  rw [← (QuotientGroup.isQuotientMap_mk (N := Idele.principalSubgroup K)).isClosed_preimage]
  have h : (QuotientGroup.mk ⁻¹' ({1} : Set (IdeleClassGroup K)))
      = (Idele.principalSubgroup K : Set (Idele K)) := by
    ext a
    rw [Set.mem_preimage, Set.mem_singleton_iff, QuotientGroup.eq_one_iff]
    rfl
  rw [h]
  exact NK.GlobalCFT.Ideles.globalCFT_principalSubgroup_isClosed

theorem connectedComponent_pow_surjective (K : Type) [Field K] [NumberField K] (p : ℕ)
    [Fact (Nat.Prime p)] (x : NK.GlobalCFT.IdeleClassGroup K)
    (hx : x ∈ Subgroup.connectedComponentOfOne (NK.GlobalCFT.IdeleClassGroup K)) :
    ∃ y : NK.GlobalCFT.IdeleClassGroup K, y ^ p = x := by
  classical
  -- an infinite place
  obtain ⟨w₀⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace K))
  have hcont : Continuous (IdeleClassGroup.abs K) := continuous_absClass' K
  haveI : T2Space (IdeleClassGroup K) := t2Space_ideleClassGroup' K
  -- the compact connected subgroup `H = C_K⁰ ⊓ ker |·|`
  set H : Subgroup (IdeleClassGroup K) :=
    Subgroup.connectedComponentOfOne (IdeleClassGroup K) ⊓ (IdeleClassGroup.abs K).ker with hH
  -- the map `z ↦ z * π(archSec |z|)⁻¹`
  set φ : IdeleClassGroup K → IdeleClassGroup K := fun z =>
    z * (IdeleClassGroup.mk K (archSec K w₀ (IdeleClassGroup.abs K z)))⁻¹ with hφ
  have hφcont : Continuous φ := by
    have hg : Continuous (fun z : IdeleClassGroup K =>
        IdeleClassGroup.mk K (archSec K w₀ (IdeleClassGroup.abs K z))) :=
      (QuotientGroup.continuous_mk (N := Idele.principalSubgroup K)).comp
        ((continuous_archSec K w₀).comp hcont)
    have hgi : Continuous (fun z : IdeleClassGroup K =>
        (IdeleClassGroup.mk K (archSec K w₀ (IdeleClassGroup.abs K z)))⁻¹) :=
      continuous_inv.comp hg
    show Continuous fun z : IdeleClassGroup K =>
      z * (IdeleClassGroup.mk K (archSec K w₀ (IdeleClassGroup.abs K z)))⁻¹
    exact continuous_id.mul hgi
  -- `φ` maps `C_K⁰` onto `H`
  have hφmem : ∀ z ∈ Subgroup.connectedComponentOfOne (IdeleClassGroup K), φ z ∈ H := by
    intro z hz
    have hzpos : 0 < ((IdeleClassGroup.abs K z : ℝˣ) : ℝ) := abs_val_pos K z
    have hgoal : φ z ∈ Subgroup.connectedComponentOfOne (IdeleClassGroup K) ⊓
        (IdeleClassGroup.abs K).ker := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · -- `φ z ∈ C_K⁰`
        have h1 : IdeleClassGroup.mk K (archSec K w₀ (IdeleClassGroup.abs K z))
            ∈ Subgroup.connectedComponentOfOne (IdeleClassGroup K) :=
          mk_archSec_mem_connectedComponentOfOne K w₀ (IdeleClassGroup.abs K z) hzpos
        exact Subgroup.mul_mem _ hz (Subgroup.inv_mem _ h1)
      · -- `|φ z| = 1`
        show IdeleClassGroup.abs K
          (z * (IdeleClassGroup.mk K (archSec K w₀ (IdeleClassGroup.abs K z)))⁻¹) = 1
        rw [map_mul, map_inv, IdeleClassGroup.abs_mk, abs_archSec K w₀ hzpos, mul_inv_cancel]
    exact hgoal
  -- `H` is the image of the connected set `C_K⁰`
  have hHpre : IsPreconnected ((H : Set (IdeleClassGroup K))) := by
    have himg : (H : Set (IdeleClassGroup K)) =
        φ '' (Subgroup.connectedComponentOfOne (IdeleClassGroup K) :
          Set (IdeleClassGroup K)) := by
      ext w
      constructor
      · intro hw
        have hw' : w ∈ Subgroup.connectedComponentOfOne (IdeleClassGroup K) ⊓
            (IdeleClassGroup.abs K).ker := hw
        obtain ⟨hwcc, hwker⟩ := Subgroup.mem_inf.mp hw'
        refine ⟨w, hwcc, ?_⟩
        have hw1 : IdeleClassGroup.abs K w = 1 := MonoidHom.mem_ker.mp hwker
        show w * (IdeleClassGroup.mk K (archSec K w₀ (IdeleClassGroup.abs K w)))⁻¹ = w
        rw [hw1, archSec_one, map_one, inv_one, mul_one]
      · rintro ⟨a, ha, rfl⟩
        exact hφmem a ha
    rw [himg]
    exact (isPreconnected_connectedComponent (x := (1 : IdeleClassGroup K))).image φ
      hφcont.continuousOn
  haveI hHconn : ConnectedSpace ↥H :=
    Subtype.connectedSpace ⟨⟨1, H.one_mem⟩, hHpre⟩
  -- `H` is compact
  have hkercompact : IsCompact
      (((IdeleClassGroup.abs K).ker : Subgroup (IdeleClassGroup K)) :
        Set (IdeleClassGroup K)) :=
    isCompact_iff_compactSpace.mpr (compactSpace_ker_abs K)
  have hHclosed : IsClosed ((H : Subgroup (IdeleClassGroup K)) :
      Set (IdeleClassGroup K)) := by
    have hker : IsClosed
        (((IdeleClassGroup.abs K).ker : Subgroup (IdeleClassGroup K)) :
          Set (IdeleClassGroup K)) := by
      rw [MonoidHom.coe_ker]
      exact isClosed_singleton.preimage hcont
    have hcc : IsClosed
        ((Subgroup.connectedComponentOfOne (IdeleClassGroup K) :
          Subgroup (IdeleClassGroup K)) : Set (IdeleClassGroup K)) :=
      isClosed_connectedComponent
    have hthis : IsClosed
        (((Subgroup.connectedComponentOfOne (IdeleClassGroup K) ⊓
          (IdeleClassGroup.abs K).ker : Subgroup (IdeleClassGroup K)) :
            Set (IdeleClassGroup K))) := hcc.inter hker
    rw [hH]
    exact hthis
  haveI hHcompact : CompactSpace ↥H :=
    isCompact_iff_compactSpace.mp (hkercompact.of_isClosed_subset hHclosed inf_le_right)
  -- the roots of the elements of `H`
  have hHroot : ∀ j : ↥H, ∃ u : ↥H, u ^ p = j := fun j =>
    compact_connected_abelian_pow_surjective ↥H p (Fact.out : Nat.Prime p).ne_zero j
  -- the content direction
  obtain ⟨d, hdpos, hd⟩ := pos_units_pow_surjective p (Fact.out : Nat.Prime p).ne_zero
    (IdeleClassGroup.abs K x) (abs_val_pos K x)
  -- write `x = m * j` with `j ∈ H`
  set m : IdeleClassGroup K := IdeleClassGroup.mk K (archSec K w₀ (IdeleClassGroup.abs K x))
    with hm
  set j : IdeleClassGroup K := m⁻¹ * x with hj
  have hjH : j ∈ H := by
    rw [hj]
    rw [mul_comm m⁻¹ x]
    exact hφmem x hx
  obtain ⟨u, hu⟩ := hHroot ⟨j, hjH⟩
  -- the two factors are `p`-th powers, hence so is `x`
  have hfac1 : m = (IdeleClassGroup.mk K (archSec K w₀ d)) ^ p := by
    rw [hm, ← hd, archSec_pow K w₀ d hdpos p, map_pow]
  have hfac2 : j = (u : IdeleClassGroup K) ^ p := by
    have h := congrArg (fun w : ↥H => (w : IdeleClassGroup K)) hu
    simpa using h.symm
  have hx_eq : x = m * j := by
    rw [hj]
    rw [mul_inv_cancel_left]
  refine ⟨IdeleClassGroup.mk K (archSec K w₀ d) * (u : IdeleClassGroup K), ?_⟩
  rw [mul_pow, ← hfac1, ← hfac2, ← hx_eq]

end Work.SSGRoute.PTW
