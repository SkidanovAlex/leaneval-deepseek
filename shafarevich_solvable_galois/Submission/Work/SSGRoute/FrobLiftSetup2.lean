import Mathlib
import Submission.Work.SSGRoute.FrobLiftSetup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Basic properties of the Frobenius-lift family

Continuing `Work.SSGRoute.FrobLiftSetup`: here we record that `frobV A L` is open,
that its trace `frobK A L` on the decomposition group is open and normal, and that `frobS A L`
(the set of elements generating `D_A ⧸ frobK A L`) is closed — it is the preimage of the set of
generators of the (finite) quotient under the quotient map, hence a union of cosets of an open
subgroup.
-/

open scoped Pointwise

namespace Work.SSGRoute

open _root_.SSGRoute

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

/-- **A general topological-group fact.**  If `K ≤ H` is an open normal subgroup of a topological
group `H`, then the set of elements of `H` whose image in `H ⧸ K` generates `H ⧸ K` is closed: it is
a union of right `K`-cosets, and so is its complement, while every `K`-coset is open. -/
theorem isClosed_preimage_zpowers_top {H : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] (K : Subgroup H) [K.Normal] (hK : IsOpen (K : Set H)) :
    IsClosed ((fun x : H => (QuotientGroup.mk x : H ⧸ K)) ⁻¹'
      {g : H ⧸ K | Subgroup.zpowers g = ⊤}) := by
  set Z : Set H := (fun x : H => (QuotientGroup.mk x : H ⧸ K)) ⁻¹'
      {g : H ⧸ K | Subgroup.zpowers g = ⊤} with hZdef
  have key : ∀ x k, k ∈ K → (x * k ∈ Z ↔ x ∈ Z) := by
    intro x k hk
    have hmk : (QuotientGroup.mk (x * k) : H ⧸ K) = QuotientGroup.mk x := by
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff k).mpr hk, mul_one]
    simp only [Z, Set.mem_preimage, hmk]
  rw [← isOpen_compl_iff]
  rw [isOpen_iff_mem_nhds]
  intro y hy
  have hyK : y ∈ y • (K : Set H) := by
    rw [Set.mem_smul_set]
    exact ⟨1, K.one_mem, by simp⟩
  refine Filter.mem_of_superset ((hK.smul y).mem_nhds hyK) ?_
  intro x hx
  obtain ⟨k, hk, hkxy⟩ := Set.mem_smul_set.mp hx
  rw [Set.mem_compl_iff] at hy ⊢
  rw [← hkxy, smul_eq_mul]
  exact fun hcon => hy ((key y k hk).mp hcon)

/-- `frobV A L` is open in the Krull topology: it contains the open fixing subgroup of `L`. -/
theorem frobV_isOpen (A : ValuationSubring Ω) (i : FrobIndex k Ω) :
    IsOpen (frobV A i : Set (Ω ≃ₐ[k] Ω)) := by
  haveI := i.2.1
  exact Subgroup.isOpen_mono le_sup_right (IntermediateField.fixingSubgroup_isOpen i.1)

/-- `frobK A L` is open in `↥D_A`, being the trace of the open subgroup `frobV A L`. -/
theorem frobK_isOpen (A : ValuationSubring Ω) (i : FrobIndex k Ω) :
    IsOpen (frobK A i : Set ↥(decomp k A)) := by
  have h1 : ((frobK A i : Set ↥(decomp k A))) =
      Subtype.val ⁻¹' (frobV A i : Set (Ω ≃ₐ[k] Ω)) := by
    ext x; rfl
  rw [h1]
  exact (frobV_isOpen A i).preimage continuous_subtype_val

/-- The decomposition group normalises `frobV A L`: conjugation by `d ∈ D_A` permutes the two
factors `I_A` (normal in `D_A`) and `G_L` (the kernel of the restriction map to `L`). -/
theorem frobV_conj_mem (A : ValuationSubring Ω) (i : FrobIndex k Ω)
    {d : Ω ≃ₐ[k] Ω} (hd : d ∈ decomp k A) :
    ∀ v ∈ frobV A i, d * v * d⁻¹ ∈ frobV A i := by
  haveI := i.2.2
  have hmap : (frobV A i).map (MulAut.conj d).toMonoidHom ≤ frobV A i := by
    rw [frobV, Subgroup.map_sup]
    refine sup_le (le_trans ?_ le_sup_left) (le_trans ?_ le_sup_right)
    · rw [Subgroup.map_le_iff_le_comap]
      intro u hu
      rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact inertiaSub_normal k Ω A d hd u hu
    · rw [Subgroup.map_le_iff_le_comap]
      intro u hu
      rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [← IntermediateField.restrictNormalHom_ker (K := k) (L := Ω) i.1, MonoidHom.mem_ker] at hu
      rw [← IntermediateField.restrictNormalHom_ker (K := k) (L := Ω) i.1, MonoidHom.mem_ker]
      rw [map_mul, map_mul, map_inv, hu, mul_one, mul_inv_cancel]
  intro v hv
  have hv' : (MulAut.conj d).toMonoidHom v ∈ (frobV A i).map (MulAut.conj d).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hv
  have h2 := hmap hv'
  rwa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h2

/-- `frobK A L = D_A ⊓ frobV A L` is normal in `D_A`. -/
theorem frobK_normal (A : ValuationSubring Ω) (i : FrobIndex k Ω) :
    (frobK A i).Normal := by
  refine Subgroup.Normal.mk ?_
  intro n hn g
  have hn' : (n : Ω ≃ₐ[k] Ω) ∈ frobV A i := by
    simpa only [frobK, Subgroup.mem_subgroupOf] using hn
  have hgoal : ((g * n * g⁻¹ : ↥(decomp k A)) : Ω ≃ₐ[k] Ω) ∈ frobV A i := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact frobV_conj_mem A i g.2 (n : Ω ≃ₐ[k] Ω) hn'
  simpa only [frobK, Subgroup.mem_subgroupOf] using hgoal

/-- The normality instance, so that the quotient `↥D_A ⧸ frobK A L` is a group. -/
instance frobK_instNormal (A : ValuationSubring Ω) (i : FrobIndex k Ω) :
    (frobK A i).Normal :=
  frobK_normal A i

/-- **`frobS A L` is the preimage of the set of generators of the quotient `D_A ⧸ frobK A L`.** -/
theorem frobS_eq_preimage (A : ValuationSubring Ω) (i : FrobIndex k Ω) :
    frobS A i = (QuotientGroup.mk) ⁻¹'
      {g : ↥(decomp k A) ⧸ frobK A i | Subgroup.zpowers g = ⊤} := by
  ext x
  show (∀ δ : ↥(decomp k A), ∃ m : ℤ, δ⁻¹ * x ^ m ∈ frobK A i) ↔
    Subgroup.zpowers (QuotientGroup.mk x : ↥(decomp k A) ⧸ frobK A i) = ⊤
  constructor
  · intro hx
    rw [Subgroup.eq_top_iff']
    intro y
    obtain ⟨δ, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨m, hm⟩ := hx δ
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨m, ?_⟩
    have h1 : (QuotientGroup.mk x : ↥(decomp k A) ⧸ frobK A i) ^ m
        = QuotientGroup.mk (x ^ m) := by
      rw [← QuotientGroup.mk'_apply (frobK A i) x, ← QuotientGroup.mk'_apply (frobK A i) (x ^ m),
        map_zpow]
    rw [h1, QuotientGroup.eq (s := frobK A i)]
    simpa [mul_inv_rev] using (frobK A i).inv_mem hm
  · intro hx δ
    have hmem : (QuotientGroup.mk δ : ↥(decomp k A) ⧸ frobK A i) ∈
        Subgroup.zpowers (QuotientGroup.mk x : ↥(decomp k A) ⧸ frobK A i) := by
      rw [hx]; exact Subgroup.mem_top _
    rw [Subgroup.mem_zpowers_iff] at hmem
    obtain ⟨m, hm⟩ := hmem
    refine ⟨m, ?_⟩
    have h1 : (QuotientGroup.mk x : ↥(decomp k A) ⧸ frobK A i) ^ m
        = QuotientGroup.mk (x ^ m) := by
      rw [← QuotientGroup.mk'_apply (frobK A i) x, ← QuotientGroup.mk'_apply (frobK A i) (x ^ m),
        map_zpow]
    rw [h1] at hm
    have h2 := (QuotientGroup.eq (s := frobK A i)).mp hm
    simpa [mul_inv_rev] using (frobK A i).inv_mem h2

/-- **`frobS A L` is closed in `↥D_A`.** -/
theorem frobS_isClosed (A : ValuationSubring Ω) (i : FrobIndex k Ω) :
    IsClosed (frobS A i) := by
  haveI := frobK_normal A i
  rw [frobS_eq_preimage A i]
  exact isClosed_preimage_zpowers_top (frobK A i) (frobK_isOpen A i)

end Work.SSGRoute
