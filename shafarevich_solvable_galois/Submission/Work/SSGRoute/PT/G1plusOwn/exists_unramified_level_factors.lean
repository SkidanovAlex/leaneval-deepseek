import Mathlib
import Submission.Work.SSGRoute.PT.G1plusOwn.levelFree
import Submission.Work.SSGRoute.PT.G1plusOwn.exists_level_unramified_mul_dvd
import Submission.Work.SSGRoute.PT.levelPair_unramified_eq_zero
import Submission.Work.SSGRoute.primeOfLevel_mem_iff_k
import Submission.Work.SSGRoute.inertiaSub_image_eq_levelInertia
import Submission.Work.SSGRoute.InertiaDefs
import Submission.Work.SSGRoute.PT.G1plusOwn.mem_inertia_of_fixes_levels
import Submission.Work.SSGRoute.PT.G1plusOwn.exists_level_unramified_le_of_isOpen
import Submission.Work.SSGRoute.PT.G1plusOwn.isInertiaAt_finQW_eq_one
import Submission.Work.SSGRoute.PT.G1plusOwn.exists_factors_of_vanishing_level
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT.G1plusOwn

open scoped TensorProduct

/-! ## The vanishing subgroup of a cocycle on a decomposition group

For a number field `k`, an algebraic closure `Ω`, a finite Galois level `K ≤ Ω`, a finite place `A`
of `Ω` and a `1`-cocycle `b` on the decomposition group `D_A = decomp k A` with values in the
`Gal(K/k)`-module `DualMod p (M ⊗ T)`, the set

  `Z = {σ ∈ D_A | b σ = 0}`

is a subgroup of `G_k = Ω ≃ₐ[k] Ω`, it contains the inertia `I_A` whenever `b` vanishes on the
inertia, and it contains `W ⊓ D_A` for the constancy subgroup `W` of any locally constant `b`.
These are the two inputs of the compactness step
`Work.SSGRoute.PT.G1plusOwn.exists_level_unramified_le_of_isOpen`. -/

section ZeroSub

variable (p : ℕ) [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
  (A : ValuationSubring Ω)

/-- **The value of a `1`-cocycle at `1` vanishes** (the cocycle identity at `(1, 1)`). -/
lemma cocycle_apply_one
    (b : (Ω ≃ₐ[k] Ω) → DualMod p (TensorProduct (ZMod p) M T))
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b) :
    b 1 = 0 := by
  have h := hb 1 (one_mem _) 1 (one_mem _)
  rw [mul_one, map_one, one_smul] at h
  exact (add_left_cancel (show b 1 + 0 = b 1 + b 1 by rw [add_zero]; exact h)).symm

/-- **The vanishing subgroup of the cocycle `b` on the decomposition group**: the elements of
`D_A = decomp k A` at which `b` vanishes.  It is a subgroup by the cocycle identity
`b (σ * τ) = b σ + res(σ) • b τ` and `b 1 = 0`. -/
noncomputable def zeroSub
    (b : (Ω ≃ₐ[k] Ω) → DualMod p (TensorProduct (ZMod p) M T))
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b) :
    Subgroup (Ω ≃ₐ[k] Ω) where
  carrier := {σ | σ ∈ SSGRoute.decomp k A ∧ b σ = 0}
  one_mem' := ⟨one_mem _, cocycle_apply_one p K T M A b hb⟩
  mul_mem' := by
    intro a b ha hb'
    exact ⟨mul_mem ha.1 hb'.1,
      by rw [hb _ ha.1 _ hb'.1, ha.2, hb'.2, smul_zero, add_zero]⟩
  inv_mem' := by
    intro a ha
    refine ⟨inv_mem ha.1, ?_⟩
    have h := hb _ (inv_mem ha.1) _ ha.1
    rw [inv_mul_cancel, ha.2, smul_zero, add_zero] at h
    exact h.symm.trans (cocycle_apply_one p K T M A b hb)

@[simp] lemma mem_zeroSub
    (b : (Ω ≃ₐ[k] Ω) → DualMod p (TensorProduct (ZMod p) M T))
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (σ : Ω ≃ₐ[k] Ω) :
    σ ∈ zeroSub p K T M A b hb ↔ σ ∈ SSGRoute.decomp k A ∧ b σ = 0 := Iff.rfl

/-- **The inertia lies in the vanishing subgroup** if `b` vanishes on the inertia. -/
lemma inertiaSub_le_zeroSub
    (b : (Ω ≃ₐ[k] Ω) → DualMod p (TensorProduct (ZMod p) M T))
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (hiner : ∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k A σ → b σ = 0) :
    Work.SSGRoute.inertiaSub k Ω A ≤ zeroSub p K T M A b hb := by
  intro σ hσ
  have hI : SSGRoute.IsInertia k A σ := (Work.SSGRoute.mem_inertiaSub k Ω A σ).mp hσ
  exact ⟨hI.1, hiner σ hI⟩

/-- **The constancy subgroup of a locally constant `b` meets `D_A` inside the vanishing
subgroup.** -/
lemma exists_isOpen_le_zeroSub
    (b : (Ω ≃ₐ[k] Ω) → DualMod p (TensorProduct (ZMod p) M T))
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (hl : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b) :
    ∃ W : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (W : Set (Ω ≃ₐ[k] Ω)) ∧
      W ⊓ SSGRoute.decomp k A ≤ zeroSub p K T M A b hb := by
  obtain ⟨U, hUopen, hU⟩ := hl
  refine ⟨U, hUopen, fun σ hσ => ?_⟩
  obtain ⟨hσU, hσD⟩ := Subgroup.mem_inf.mp hσ
  refine ⟨hσD, ?_⟩
  have h := hU 1 (one_mem _) σ hσU hσD
  rw [one_mul, cocycle_apply_one p K T M A b hb] at h
  exact h

end ZeroSub

/-- **A finite Galois level, unramified at the place `A`, at which a locally constant cocycle
vanishing on the inertia of `A` factors.**

`k` a number field, `Ω` an algebraic closure of `k`, `K/k` finite Galois unramified at the finite
place `A` of `Ω` (`hramA`), and `b` a locally constant `1`-cocycle on the decomposition group
`D_A = decomp k A` vanishing on the inertia `I_A`.  Then there is a finite Galois level `L ⊇ K` on
which `b|_D_A` factors, and which is unramified at `A`.  (Consumer:
`Work.SSGRoute.PT.G1plusOwn.g1FinHalf_unramified` in the same directory already contains the rest of
the proof and imports this module.)

Route (compactness; only two on-disk inputs, both available).
1. `Z := {σ ∈ D_A | b σ = 0}` is a *subgroup* of `D_A` (closure via the cocycle identity
   `b (σ * τ) = b σ + σ • b τ`); `hiner` gives `I_A ≤ Z`, and `hl : IsLocConstOn (decomp k A) b`
   gives an open (take it normal) `W ≤ G_k` with `W ⊓ D_A ≤ Z` (take `g = 1` in `IsLocConstOn`, and
   `b 1 = 0` from the cocycle identity at `(1,1)`).
2. `Work.SSGRoute.PT.G1plusOwn.inertiaSub_normalClosure_inf_decomp` (being proved in parallel; it
   states `closure (normalClosure I_A) ⊓ D_A ≤ I_A`) gives `closure (normalClosure I_A) ⊓ D_A ≤ Z`.
3. `𝒱 := {V ◁ G_k : IsOpen V, I_A ≤ V}` is non-empty and directed downward with
   `⋂ 𝒱 = closure (normalClosure I_A)`; hence `⋂_{V ∈ 𝒱} (V ⊓ D_A) ⊆ Z` and, since `D_A` is compact
   (closed in the compact Krull topology) and the sets `(V ⊓ D_A) \ Z` are closed and decreasing,
   the finite intersection property gives `V ∈ 𝒱` with `V ⊓ D_A ≤ Z`.
4. `L := Ω^V` (the fixed field of the normal open `V`, via the Galois correspondence for the Krull
   topology) is finite, normal and a number field over `k`, contains `K` (intersect `V` with
   `Gal(Ω/K)` first if necessary), is unramified at `A` (`I_A ≤ V`), and `b` factors on `D_A` since
   `Gal(Ω/L) ∩ D_A = V ⊓ D_A ≤ Z`: for `υ ∈ Z` and `σ ∈ D_A` one has
   `b (σ * υ) = b σ + σ • b υ = b σ`, so `b` is constant on the fibres of `restrictNormalHom L`
   (use the `Classical.choose` pattern of `Work.SSGRoute.PT.exists_level_factors_locConstOn`).
5. The `hunr` spelling (`IsInertiaAt (finQW L A hA) σ → σ = 1`) follows from `I_A ≤ L.fixingSubgroup`
   plus `Work.SSGRoute.inertiaSub_image_eq_levelInertia` (the level inertia is the image of `I_A`),
   identifying `finQW L A hA` with `levelPrime k Ω A hA L` (both are the prime of `𝓞 L` below `A`:
   `finQW_spec`, `NK.Reconstruct.primeOfLevel_spec`, `NK.ResidueFrob.primeOfLevel_liesOver`) and
   `Work.SSGRoute.PTExt.isInertiaAt_iff_mem_inertia_local`.

Alternative (residue degrees, if the compactness step is awkward): with
`Work.SSGRoute.PT.G1plusOwn.exists_level_unramified_mul_dvd` (on disk: `e = 1` and `N ∣ f` for any
`N ≠ 0`) take `M' ≥ K` unramified at `A` with `2 * W.index ∣ f M'`; then
`H₁ := (Gal(Ω/M')).comap (Subgroup.subtype (decomp k A))` has index `f M'`
(`Work.SSGRoute.levelSub_comap_index_eq_inertiaDeg`) and
`H₂ := ((inertiaSub k Ω A) ⊔ W).comap (Subgroup.subtype (decomp k A))` has index dividing
`W.index` with `H₂ ≤ Z`; the index/chain comparison of open subgroups of `D_A` containing the
inertia then gives `H₁ ≤ H₂ ≤ Z`.

Splitting into several lemmas in the same file is fine. -/
theorem exists_unramified_level_factors
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hramA : ¬ SSGRoute.IsRamifiedIn k K A)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (hl : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b)
    (hiner : ∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k A σ → b σ = 0) :
    ∃ (L : IntermediateField k Ω), ∃ (_ : NumberField ↥L) (_ : FiniteDimensional k L)
      (_ : IsGalois k L), K ≤ L ∧
      (∀ σ : ↥L ≃ₐ[k] ↥L, SSGRoute.PTExt.IsInertiaAt (Work.SSGRoute.PT.finQW L A hA) σ → σ = 1) ∧
      ∃ b₀ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
        ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ) := by
  classical
  -- the cocycle vanishes on the inertia, so the inertia lies in the vanishing subgroup `Z`
  have hIZ : Work.SSGRoute.inertiaSub k Ω A ≤ zeroSub p K T M A b hb :=
    inertiaSub_le_zeroSub p K T M A b hb hiner
  -- locally constant `b` gives an open constancy subgroup whose trace on `D_A` lies in `Z`
  have hW : ∃ W : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (W : Set (Ω ≃ₐ[k] Ω)) ∧
      W ⊓ SSGRoute.decomp k A ≤ zeroSub p K T M A b hb :=
    exists_isOpen_le_zeroSub p K T M A b hb hl
  -- compactness produces a finite Galois level `L ⊇ K`, unramified at `A`, with
  -- `D_A ⊓ Gal(Ω/L) ≤ Z`
  obtain ⟨L, hLfin, hLgal, hKL, hIunr, hLZ⟩ :=
    exists_level_unramified_le_of_isOpen k Ω K A hA hramA (zeroSub p K T M A b hb) hW hIZ
      (fun δ hδD hfix => mem_inertia_of_fixes_levels k Ω K A hA hramA δ hδD hfix)
  haveI : FiniteDimensional k L := hLfin
  haveI : IsGalois k L := hLgal
  haveI : Normal k L := hLgal.to_normal
  haveI hNF : NumberField ↥L := NumberField.of_module_finite k ↥L
  refine ⟨L, hNF, hLfin, hLgal, hKL, ?_, ?_⟩
  · -- the level is unramified at `A`, so its inertia at the level prime is trivial
    exact fun σ hσ => isInertiaAt_finQW_eq_one k Ω L A hA hIunr σ hσ
  · -- `b` vanishes on `D_A ⊓ L.fixingSubgroup`, hence factors through the restriction to `L`
    refine exists_factors_of_vanishing_level p k Ω K T M A b hb L (fun σ hσ hσL => ?_)
    have hmem : σ ∈ SSGRoute.decomp k A ∧ b σ = 0 :=
      (mem_zeroSub p K T M A b hb σ).mp (hLZ σ hσ hσL)
    exact hmem.2

end Work.SSGRoute.PT.G1plusOwn
