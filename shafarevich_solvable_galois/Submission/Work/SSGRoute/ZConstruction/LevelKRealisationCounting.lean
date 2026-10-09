import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.ZDataMup.LocalData
import Submission.Work.SSGRoute.ZDataMup.sumPairing_bilinForm
import Submission.Work.SSGRoute.ZDataMup.sum_pair_eq_zero_impEqZero
import Submission.Work.SSGRoute.ZDataMup.finite_localDataSpace_quotient
import Submission.Work.SSGRoute.ZDataMup.orthogonal_le_sup_of_ker_le_quotient
import Submission.Work.SSGRoute.ZDataMup.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The level-`K` degree-one realisation, from the counting inequality

This module re-establishes, in a form that is *sound* (no `sorry` and no false standing assumption),
the formal layer of the level-`K` Tate--Poitou degree-one realisation which used to live in
`Submission/Work/SSGRoute/ZDataMup/tatePoitou_h1_realisation.lean` and was removed from the
workspace after its standing assumption `counting_localisation_le` was shown to be false without an
`hSram`-type hypothesis on the place set `T` (see `ZDataMup/TATEPOITOU_STATUS.md`, the section
"The counterexample").

Here the counting inequality is an **explicit hypothesis** `hcount` of the theorem, so that

* nothing false is assumed: the theorem is a genuine implication,
* the statement becomes the *correct* gate as soon as `hcount` is supplied for a place set `T`
  which covers the places above `p` and the places ramified in the auxiliary field (the
  `hSram`-type hypothesis of the siblings, Milne ADT I.4.10).

The main statement is

  `Work.SSGRoute.ZConstruction.levelK_realisation_of_counting`:

local data `f` at a finite level-`K`-nonsingular set `T` of finite places which is orthogonal
(`ZDataMup.IsOrthogonalToDual`) to every global cocycle unramified outside the level-`K` classes of
`T` is the localisation of a global locally constant cocycle `z` on `G_K`, provided the level-`K`
counting inequality holds.  The conclusion is in the *coboundary* form used by
`Work.SSGRoute.ZDataMup`'s `IsOrthogonalToDual`; it is converted into pointwise agreement on the
local groups in `ZConstruction/AuxRealisationHonest.lean`.
-/

open scoped Pointwise BigOperators

open Classical

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

/-- The `Finset`-sum over a `Finset` and the sum over its subtype agree. -/
theorem sum_subtype_eq_sum_finset {Ω : Type} [Field Ω] {M : Type} [AddCommMonoid M]
    (T : Finset (ValuationSubring Ω)) (g : ValuationSubring Ω → M) :
    (∑ A : {A : ValuationSubring Ω // A ∈ T}, g A.1) = ∑ A ∈ T, g A :=
  (Finset.sum_subtype (s := T) (p := fun A => A ∈ T) (by intro A; simp) g).symm

/-- **The level-`K` degree-one realisation from the counting inequality.**  See the module
docstring: the counting inequality is an explicit hypothesis, so nothing false is assumed. -/
theorem levelK_realisation_of_counting (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (k Ω : Type)
    [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p)
    (hpair : Work.SSGRoute.ZDataMup.IsLocalTateSystem p k Ω K pair)
    (hrec : Work.SSGRoute.ZDataMup.IsProductFormula p k Ω K pair)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T,
      (∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) → A = B)
    (f : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p)
    (hf : ∀ A ∈ T, SSGRoute.IsCocycleOn (SSGRoute.res k K)
        (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A) ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A))
    (horth : Work.SSGRoute.ZDataMup.IsOrthogonalToDual p k Ω K pair T f)
    (hcount : Module.finrank (ZMod p)
        (↥(Work.SSGRoute.ZDataMup.localDataSpace (p := p) K T) ⧸
          Work.SSGRoute.ZDataMup.localVanish (p := p) K T) ≤
      2 * Module.finrank (ZMod p)
        (((Work.SSGRoute.ZDataMup.localImageIn (p := p) K T) ⊔
            Work.SSGRoute.ZDataMup.localVanish (p := p) K T).map
          (Submodule.mkQ (Work.SSGRoute.ZDataMup.localVanish (p := p) K T)))) :
    ∃ z : (Ω ≃ₐ[k] Ω) → ZMod p,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup z ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ A ∈ T, SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A ⊓ K.fixingSubgroup)
        (fun σ => z σ - f A σ)) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ T, ¬ ∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) := by
  classical
  haveI hfinQ : Module.Finite (ZMod p)
      (↥(Work.SSGRoute.ZDataMup.localDataSpace (p := p) K T) ⧸
        Work.SSGRoute.ZDataMup.localVanish (p := p) K T) :=
    Work.SSGRoute.ZDataMup.finite_localDataSpace_quotient (p := p) (K := K) T hTfin
  obtain ⟨B, hB⟩ := Work.SSGRoute.ZDataMup.sumPairing_bilinForm (p := p) (K := K) hpair T hTfin
  have hHA : ∀ A : {A : ValuationSubring Ω // A ∈ T},
      ∃ A' : ValuationSubring Ω, IsFinPlace k A' ∧
        decomp k A.1 ⊓ K.fixingSubgroup = decomp k A' ⊓ K.fixingSubgroup :=
    fun A => ⟨A.1, hTfin A.1 A.2, rfl⟩
  let F : ↥(Work.SSGRoute.ZDataMup.localDataSpace (p := p) K T) :=
    ⟨fun A => f A.1, fun A => ⟨(hf A.1 A.2).1, (hf A.1 A.2).2⟩⟩
  -- (1) the left radical of the sum pairing lies in the vanishing submodule
  have hkerL : B.ker ≤ Work.SSGRoute.ZDataMup.localVanish (p := p) K T := by
    intro x hx
    show x.1 ∈ Work.SSGRoute.ZDataMup.productVanish (p := p) K T
    refine Work.SSGRoute.ZDataMup.sum_pair_eq_zero_impEqZero (p := p) (K := K)
      (pair := pair) hpair hTfin (a := x.1) x.2 ?_
    intro b hb
    have hx0 : B x ⟨b, hb⟩ = 0 := by
      have h0 : B x = 0 := LinearMap.mem_ker.mp hx
      simpa using LinearMap.congr_fun h0 ⟨b, hb⟩
    rw [← hB x ⟨b, hb⟩]
    exact hx0
  -- (2) the vanishing submodule lies in both radicals of `B`
  have hkerL' : Work.SSGRoute.ZDataMup.localVanish (p := p) K T ≤ B.ker := by
    intro x hx
    rw [LinearMap.mem_ker]
    ext y
    rw [hB x y]
    refine Finset.sum_eq_zero (fun A _ => ?_)
    have hxvan : ∀ g ∈ decomp k A.1 ⊓ K.fixingSubgroup, x.1 A g = 0 := by
      have h := hx
      rw [Work.SSGRoute.ZDataMup.localVanish, Submodule.mem_comap] at h
      exact h A
    have h01 : IsCocycleOn (res k K) (decomp k A.1 ⊓ K.fixingSubgroup)
          (0 : (Ω ≃ₐ[k] Ω) → ZMod p) ∧
        IsLocConstOn (decomp k A.1 ⊓ K.fixingSubgroup) (0 : (Ω ≃ₐ[k] Ω) → ZMod p) :=
      ⟨Work.SSGRoute.ZDataMup.isCocycleOn_zero _, Work.SSGRoute.ZDataMup.isLocConstOn_zero _⟩
    have h0b : pair (decomp k A.1 ⊓ K.fixingSubgroup) 0 (y.1 A) = 0 :=
      hpair.vanishes_coboundary (decomp k A.1 ⊓ K.fixingSubgroup) (hHA A) 0 (y.1 A)
        h01 (y.2 A) (Or.inl ⟨0, fun g hg => by simp⟩)
    exact (Work.SSGRoute.ZDataMup.pair_congr_of_eqOn_left (K := K) hpair (hHA A) (x.2 A)
      h01 (y.2 A) hxvan).trans h0b
  have hkerR : Work.SSGRoute.ZDataMup.localVanish (p := p) K T ≤ B.orthogonal ⊤ := by
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y _
    rw [hB y x]
    refine Finset.sum_eq_zero (fun A _ => ?_)
    have hxvan : ∀ g ∈ decomp k A.1 ⊓ K.fixingSubgroup, x.1 A g = 0 := by
      have h := hx
      rw [Work.SSGRoute.ZDataMup.localVanish, Submodule.mem_comap] at h
      exact h A
    have h0 : pair (decomp k A.1 ⊓ K.fixingSubgroup) (y.1 A) (x.1 A) =
        pair (decomp k A.1 ⊓ K.fixingSubgroup) (y.1 A) 0 :=
      Work.SSGRoute.ZDataMup.pair_congr_of_eqOn_right (K := K) hpair (hHA A) (y.2 A) (x.2 A)
        ⟨Work.SSGRoute.ZDataMup.isCocycleOn_zero _, Work.SSGRoute.ZDataMup.isLocConstOn_zero _⟩ hxvan
    rw [h0]
    exact Work.SSGRoute.ZDataMup.pair_zero_right_of_isLocalTateSystem (K := K) hpair (hHA A) (y.2 A)
  -- (3) the localisation image is isotropic (the product formula)
  have hisoF : Work.SSGRoute.ZDataMup.localImageIn (p := p) K T ≤
      (B.flip).orthogonal (Work.SSGRoute.ZDataMup.localImageIn (p := p) K T) := by
    intro w hw
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w' hw'
    obtain ⟨z, hz⟩ := LinearMap.mem_range.mp hw
    obtain ⟨z', hz'⟩ := LinearMap.mem_range.mp hw'
    rw [LinearMap.BilinForm.flip_apply, hB w w']
    have hw1 : w.1 = fun A : {A : ValuationSubring Ω // A ∈ T} =>
        (z : (Ω ≃ₐ[k] Ω) → ZMod p) := by rw [← hz]; rfl
    have hw1' : w'.1 = fun A : {A : ValuationSubring Ω // A ∈ T} =>
        (z' : (Ω ≃ₐ[k] Ω) → ZMod p) := by rw [← hz']; rfl
    rw [hw1, hw1']
    show (∑ A : {A : ValuationSubring Ω // A ∈ T},
        pair (decomp k A.1 ⊓ K.fixingSubgroup)
          ((z : (Ω ≃ₐ[k] Ω) → ZMod p)) ((z' : (Ω ≃ₐ[k] Ω) → ZMod p))) = 0
    rw [sum_subtype_eq_sum_finset T
      (fun A => pair (decomp k A ⊓ K.fixingSubgroup)
        ((z : (Ω ≃ₐ[k] Ω) → ZMod p)) ((z' : (Ω ≃ₐ[k] Ω) → ZMod p)))]
    exact Work.SSGRoute.ZDataMup.sum_pair_selmer_eq_zero (p := p) (K := K) hrec hTfin hTdisj z.2 z'.2
  -- (4) the datum lies in the left annihilator of the image
  have hF : F ∈ (B.flip).orthogonal (Work.SSGRoute.ZDataMup.localImageIn (p := p) K T) := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    obtain ⟨z, hz⟩ := LinearMap.mem_range.mp hw
    rw [LinearMap.BilinForm.flip_apply, hB F w]
    have hw1 : w.1 = fun A : {A : ValuationSubring Ω // A ∈ T} =>
        (z : (Ω ≃ₐ[k] Ω) → ZMod p) := by rw [← hz]; rfl
    rw [hw1]
    show (∑ A : {A : ValuationSubring Ω // A ∈ T},
        pair (decomp k A.1 ⊓ K.fixingSubgroup) (f A.1)
          ((z : (Ω ≃ₐ[k] Ω) → ZMod p))) = 0
    rw [sum_subtype_eq_sum_finset T
      (fun A => pair (decomp k A ⊓ K.fixingSubgroup) (f A)
        ((z : (Ω ≃ₐ[k] Ω) → ZMod p)))]
    exact horth z.1 z.2.1 z.2.2.1 (fun Q hQ hnot σ hσK hσI => z.2.2.2 Q hQ hnot σ hσI)
  -- (5) maximality, and the conclusion
  have hFmem : F ∈ Work.SSGRoute.ZDataMup.localImageIn (p := p) K T ⊔
      Work.SSGRoute.ZDataMup.localVanish (p := p) K T :=
    Work.SSGRoute.ZDataMup.orthogonal_le_sup_of_ker_le_quotient
      (Work.SSGRoute.ZDataMup.localVanish (p := p) K T) B
      (Work.SSGRoute.ZDataMup.localImageIn (p := p) K T)
      hkerL hkerL' hkerR hisoF hcount hF
  obtain ⟨w, hw, v, hv, hwv⟩ := (Submodule.mem_sup).mp hFmem
  obtain ⟨z, hz⟩ := LinearMap.mem_range.mp hw
  refine ⟨z.1, z.2.1, z.2.2.1, ?_, ?_⟩
  · intro A hA
    refine (Work.SSGRoute.ZDataMup.sub_isCoboundaryOn_iff_eqOn (p := p) inf_le_right z.1 (f A)).mpr ?_
    intro g hg
    have hvA : v.1 ⟨A, hA⟩ g = 0 := by
      have hv' : v.1 ∈ Work.SSGRoute.ZDataMup.productVanish (p := p) K T := by
        have h := hv
        rw [Work.SSGRoute.ZDataMup.localVanish, Submodule.mem_comap] at h
        exact h
      exact hv' ⟨A, hA⟩ g hg
    have hw1 : w.1 ⟨A, hA⟩ = z.1 := by rw [← hz]; rfl
    have key : f A g = z.1 g + 0 := by
      calc f A g = F.1 ⟨A, hA⟩ g := rfl
        _ = (w.1 + v.1) ⟨A, hA⟩ g := by
              rw [show F.1 = w.1 + v.1 from by rw [show F = w + v from hwv.symm]; rfl]
        _ = w.1 ⟨A, hA⟩ g + v.1 ⟨A, hA⟩ g := rfl
        _ = z.1 g + 0 := by rw [hw1, hvA]
    rw [key, add_zero]
  · intro Q hQ hnot σ hσK hσI
    exact z.2.2.2 Q hQ hnot σ hσI

end Work.SSGRoute.ZConstruction
