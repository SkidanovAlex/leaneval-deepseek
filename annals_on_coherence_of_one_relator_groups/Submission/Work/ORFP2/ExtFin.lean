/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Finitely many relators spanning the kernel's `k`-module

Given that the relation module of `φ : F(Fin n) →* G` is a finitely generated `k[G]`-module, we
produce a *finite* set `R₀ ⊆ ker φ` such that every element of the relation module is a `k`-linear
combination of the classes `foxGamma x`, `x ∈ normalClosure R₀`.
-/
import Mathlib
import Submission.Work.ORFP2.ExtGamma

set_option autoImplicit false

namespace Work.ORFP2.Ext

open MonoidAlgebra

universe u

variable (k : Type*) [CommRing k] {n : ℕ} {G : Type u} [Group G]

section Expansion

variable (φ : FreeGroup (Fin n) →* G) (hφ : Function.Surjective φ)

lemma ker_conj_mem {r : FreeGroup (Fin n)} (hr : r ∈ φ.ker) (g : FreeGroup (Fin n)) :
    g * r * g⁻¹ ∈ φ.ker := by
  rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, MonoidHom.mem_ker.mp hr, mul_one,
    mul_inv_cancel]

lemma sec_conj_mem {r : FreeGroup (Fin n)} (hr : r ∈ φ.ker) (g : G) :
    sec φ hφ g * r * (sec φ hφ g)⁻¹ ∈ φ.ker :=
  ker_conj_mem φ hr (sec φ hφ g)

/-- `b • foxGamma r` is the `k`-linear combination of the classes of the conjugates of `r`
given by the coefficients of `b` along a transversal. -/
lemma smul_foxGamma_expansion (hbasis : FreeGroupAugIdealBasis k)
    (b : MonoidAlgebra k G) (r : FreeGroup (Fin n)) (hr : r ∈ φ.ker) :
    b • foxGamma k hbasis n φ r
      = ∑ g ∈ b.coeff.support, b.coeff g •
          foxGamma k hbasis n φ (sec φ hφ g * r * (sec φ hφ g)⁻¹) := by
  have hb : b = ∑ g ∈ b.coeff.support,
      b.coeff g • (MonoidAlgebra.single g (1 : k) : MonoidAlgebra k G) :=
    Work.ORFP2.eq_sum_smul_single k G b
  conv_lhs => rw [hb]
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro g _
  have hgg : (MonoidAlgebra.single g (1 : k) : MonoidAlgebra k G)
      = MonoidAlgebra.single (φ (sec φ hφ g)) 1 := by rw [phi_sec]
  rw [smul_assoc, hgg, ← foxGamma_conj k hbasis n φ _ _ hr]

lemma conj_mem_normalClosure (R : Set (FreeGroup (Fin n))) {r : FreeGroup (Fin n)} (hr : r ∈ R)
    (g : FreeGroup (Fin n)) : g * r * g⁻¹ ∈ Subgroup.normalClosure R :=
  Subgroup.normalClosure_normal.conj_mem r (Subgroup.subset_normalClosure hr) g

lemma conj_mem_normalClosure' (R : Set (FreeGroup (Fin n))) {r : FreeGroup (Fin n)}
    (hr : r ∈ Subgroup.normalClosure R) (g : FreeGroup (Fin n)) :
    g * r * g⁻¹ ∈ Subgroup.normalClosure R :=
  Subgroup.normalClosure_normal.conj_mem r hr g

lemma normalClosure_le_ker (R : Set (FreeGroup (Fin n))) (hR : R ⊆ φ.ker) :
    Subgroup.normalClosure R ≤ φ.ker :=
  Subgroup.normalClosure_le_normal hR

end Expansion

section Finiteness

variable (hbasis : FreeGroupAugIdealBasis k) (φ : FreeGroup (Fin n) →* G)

/-- There are finitely many relators `R₀ ⊆ ker φ` such that every element of the relation module
is a `k`-linear combination of the classes of elements of the normal closure of `R₀`. -/
theorem exists_finset_relators (hφ : Function.Surjective φ)
    (hKfg : (relationModule k G φ).FG) :
    ∃ R₀ : Finset (FreeGroup (Fin n)), (R₀ : Set (FreeGroup (Fin n))) ⊆ φ.ker ∧
      ∀ y ∈ relationModule k G φ,
        ∃ (ι : Type u) (_ : Fintype ι) (x : ι → ↥(φ.ker)) (d : ι → k),
          (∀ i, (x i : FreeGroup (Fin n)) ∈ Subgroup.normalClosure (R₀ : Set (FreeGroup (Fin n)))) ∧
          y = ∑ i, d i • foxGamma k hbasis n φ (x i : FreeGroup (Fin n)) := by
  classical
  obtain ⟨S, hSfin, hSspan⟩ := Submodule.fg_def.mp hKfg
  -- coefficients for each generator, given by the key lemma
  let C : (Fin n →₀ MonoidAlgebra k G) → ↥(φ.ker) →₀ MonoidAlgebra k G := fun v =>
    if hv : v ∈ relationModule k G φ then
      Classical.choose (relationModule_eq_span_foxGamma k hbasis n φ hφ v hv) else 0
  have hC : ∀ v (hv : v ∈ relationModule k G φ),
      v = (C v).sum (fun r b => b • foxGamma k hbasis n φ (r : FreeGroup (Fin n))) := by
    intro v hv
    simp only [C, dif_pos hv]
    exact Classical.choose_spec (relationModule_eq_span_foxGamma k hbasis n φ hφ v hv)
  -- the set of relators
  let Rf : Set (FreeGroup (Fin n)) :=
    ⋃ v ∈ S, (fun r : ↥(φ.ker) => (r : FreeGroup (Fin n))) '' ((C v).support : Set ↥(φ.ker))
  have hRffin : Rf.Finite := by
    refine hSfin.biUnion fun v _ => ?_
    exact ((C v).support.finite_toSet.image _)
  let R₀ : Finset (FreeGroup (Fin n)) := hRffin.toFinset
  have hR₀coe : (R₀ : Set (FreeGroup (Fin n))) = Rf := hRffin.coe_toFinset
  have hRf_mem : ∀ (v : Fin n →₀ MonoidAlgebra k G), v ∈ S → ∀ (r : ↥(φ.ker)),
      r ∈ (C v).support → (r : FreeGroup (Fin n)) ∈ Rf := by
    intro v hv r hr
    refine Set.mem_iUnion.mpr ⟨v, Set.mem_iUnion.mpr ⟨hv, ?_⟩⟩
    exact Set.mem_image_of_mem _ hr
  have hRfker : Rf ⊆ φ.ker := by
    intro r hr
    obtain ⟨v, hr2⟩ := Set.mem_iUnion.mp hr
    obtain ⟨hv, hr3⟩ := Set.mem_iUnion.mp hr2
    obtain ⟨r', hr', rfl⟩ := hr3
    exact r'.2
  -- the predicate
  let Q : (Fin n →₀ MonoidAlgebra k G) → Prop := fun y =>
    ∃ (ι : Type u) (_ : Fintype ι) (x : ι → ↥(φ.ker)) (d : ι → k),
      (∀ i, (x i : FreeGroup (Fin n)) ∈ Subgroup.normalClosure Rf) ∧
      y = ∑ i, d i • foxGamma k hbasis n φ (x i : FreeGroup (Fin n))
  have hQker : ∀ i : ↥(φ.ker), (i : FreeGroup (Fin n)) ∈ Subgroup.normalClosure Rf →
      (i : FreeGroup (Fin n)) ∈ φ.ker :=
    fun i hi => Subgroup.normalClosure_le_normal hRfker hi
  have hQzero : Q 0 := by
    refine ⟨PEmpty.{u+1}, inferInstance, PEmpty.elim, PEmpty.elim, ?_, ?_⟩
    · intro i; exact PEmpty.elim i
    · simp
  have hQsingle : ∀ (r : ↥(φ.ker)), (r : FreeGroup (Fin n)) ∈ Subgroup.normalClosure Rf →
      Q (foxGamma k hbasis n φ (r : FreeGroup (Fin n))) := by
    intro r hr
    refine ⟨PUnit.{u+1}, inferInstance, fun _ => r, fun _ => 1, fun _ => hr, ?_⟩
    simp
  have hQadd : ∀ y z, Q y → Q z → Q (y + z) := by
    rintro y z ⟨ι₁, _, x₁, d₁, h₁, rfl⟩ ⟨ι₂, _, x₂, d₂, h₂, rfl⟩
    refine ⟨ι₁ ⊕ ι₂, inferInstance, Sum.elim x₁ x₂, Sum.elim d₁ d₂, ?_, ?_⟩
    · rintro (i | i)
      · simpa using h₁ i
      · simpa using h₂ i
    · rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
  have hQsmul : ∀ (a : MonoidAlgebra k G) (y : Fin n →₀ MonoidAlgebra k G), Q y → Q (a • y) := by
    rintro a y ⟨ι, _, x, d, hx, rfl⟩
    have hmem : ∀ (i : ι) (g : G), g ∈ a.coeff.support →
        (sec φ hφ g * (x i : FreeGroup (Fin n)) * (sec φ hφ g)⁻¹) ∈ φ.ker :=
      fun i g _ => sec_conj_mem (φ := φ) (hφ := hφ) (r := (x i : FreeGroup (Fin n)))
        (hQker (x i) (hx i)) g
    refine ⟨ι × ↥(a.coeff.support), inferInstance,
      fun p => ⟨sec φ hφ (p.2 : G) * (x p.1 : FreeGroup (Fin n)) * (sec φ hφ (p.2 : G))⁻¹,
        hmem p.1 (p.2 : G) p.2.2⟩,
      fun p => d p.1 * a.coeff (p.2 : G), ?_, ?_⟩
    · intro p
      exact conj_mem_normalClosure' (Rf) (hx p.1) (sec φ hφ (p.2 : G))
    · have hterm : ∀ i : ι, d i • (a • foxGamma k hbasis n φ (x i : FreeGroup (Fin n)))
          = ∑ g : ↥(a.coeff.support),
              (d i * a.coeff (g : G)) • foxGamma k hbasis n φ
                (sec φ hφ (g : G) * (x i : FreeGroup (Fin n)) * (sec φ hφ (g : G))⁻¹) := by
        intro i
        rw [smul_foxGamma_expansion (k := k) (hbasis := hbasis) (φ := φ) (hφ := hφ) a
          (x i : FreeGroup (Fin n)) (hQker (x i) (hx i)), Finset.smul_sum]
        rw [Finset.sum_subtype (a.coeff.support) (fun g => Iff.rfl)
          (fun g => d i • (a.coeff g • foxGamma k hbasis n φ
            (sec φ hφ g * (x i : FreeGroup (Fin n)) * (sec φ hφ g)⁻¹)))]
        exact Finset.sum_congr rfl fun g _ => by rw [← mul_smul]
      rw [Finset.smul_sum]
      rw [Finset.sum_congr rfl (fun i _ => smul_comm a (d i)
        (foxGamma k hbasis n φ (x i : FreeGroup (Fin n))))]
      rw [Finset.sum_congr rfl (fun i _ => hterm i)]
      rw [Fintype.sum_prod_type]
  have hQfinsum : ∀ (c : ↥(φ.ker) →₀ MonoidAlgebra k G),
      (∀ r ∈ c.support, Q (c r • foxGamma k hbasis n φ (r : FreeGroup (Fin n)))) →
      Q (c.sum (fun r b => b • foxGamma k hbasis n φ (r : FreeGroup (Fin n)))) := by
    intro c
    induction c using Finsupp.induction with
    | zero => intro _; simpa using hQzero
    | single_add a b f hnotmem hb ih =>
        intro h
        have hsplit : (Finsupp.single a b + f).sum
            (fun r b => b • foxGamma k hbasis n φ (r : FreeGroup (Fin n)))
          = b • foxGamma k hbasis n φ (a : FreeGroup (Fin n))
            + f.sum (fun r b => b • foxGamma k hbasis n φ (r : FreeGroup (Fin n))) := by
          rw [Finsupp.sum_add_index (fun r _ => by simp) (fun r _ m₁ m₂ => by simp [add_smul]),
            Finsupp.sum_single_index (by simp)]
        rw [hsplit]
        refine hQadd _ _ ?_ (ih ?_)
        · have hfa : f a = 0 := by
            by_contra hne
            exact hnotmem (Finsupp.mem_support_iff.mpr hne)
          have ha : (Finsupp.single a b + f) a = b := by
            rw [Finsupp.add_apply, Finsupp.single_eq_same, hfa, add_zero]
          have hh := h a (by rw [Finsupp.mem_support_iff, ha]; exact hb)
          rwa [ha] at hh
        · intro r hr
          have hra : r ≠ a := by rintro rfl; exact hnotmem hr
          have hr' : r ∈ (Finsupp.single a b + f).support := by
            rw [Finsupp.mem_support_iff] at hr ⊢
            rwa [Finsupp.add_apply, Finsupp.single_eq_of_ne hra, zero_add]
          have hh := h r hr'
          rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hra, zero_add] at hh
          exact hh
  have hQgen : ∀ v ∈ S, Q v := by
    intro v hv
    have hvK : v ∈ relationModule k G φ := hSspan ▸ Submodule.subset_span hv
    rw [hC v hvK]
    refine hQfinsum _ fun r hr => ?_
    exact hQsmul _ _ (hQsingle r (Subgroup.subset_normalClosure (hRf_mem v hv r hr)))
  have hspan : ∀ y ∈ Submodule.span (MonoidAlgebra k G)
      (S : Set (Fin n →₀ MonoidAlgebra k G)), Q y := by
    intro y hy
    refine Submodule.span_induction (p := fun y _ => Q y) ?_ ?_ ?_ ?_ hy
    · intro x hx; exact hQgen x hx
    · exact hQzero
    · intro x y _ _ ihx ihy; exact hQadd x y ihx ihy
    · intro a x _ ih; exact hQsmul a x ih
  refine ⟨R₀, ?_, ?_⟩
  · rw [hR₀coe]; exact hRfker
  · intro y hy
    obtain ⟨ι, hι, x, d, hx, hy'⟩ := hspan y (hSspan ▸ hy)
    exact ⟨ι, hι, x, d, fun i => by rw [hR₀coe]; exact hx i, hy'⟩

end Finiteness

end Work.ORFP2.Ext
