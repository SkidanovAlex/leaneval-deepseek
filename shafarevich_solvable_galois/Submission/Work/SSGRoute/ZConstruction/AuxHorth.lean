import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.ZConstruction.AuxInterface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Isolating the orthogonality content of the p. 18 chase

`Work.SSGRoute.AuxRealisationGate` (gate (R), `ZConstruction/AuxInterface.lean`) consumes the
*orthogonality of the prescribed datum*

  `∑_{A ∈ T} pair (decomp k A ⊓ K.fixingSubgroup) (auxDatum K S y₁ A) b = 0`

against every relaxed dual class `b` of a place set `T` that contains the places of
`cs(S') ∖ cs(S)` (where the prescribed datum is `0`) as well as representatives of `cs(S)` (where it
is `y₁`).

This file proves the elementary reduction which separates that statement from the arithmetic: the
orthogonality of the *prescribed* datum follows from

* the orthogonality of the *global* datum `y₁` over the same `T` — i.e.
  `∑_{A ∈ T} pair _ y₁ b = 0`, which is what Hilbert reciprocity supplies — together with
* the vanishing of the datum on the local groups of the places of `T` outside `cs(S)`.

The second input is the `hνS₀` of `ZSplit/levelK_datum_orthogonality.lean` ("the datum of `ν` has no
component at `S₀ ∖ T`"), which that file's docstring identifies as the genuine content of the p. 18
diagram chase; it is needed because the terms of `T ∖ cs(S)` enter the reciprocity sum with the
*global* datum `y₁`, whereas the prescribed datum has `0` there.  With it, the two sums differ only
by terms in which one of the two arguments is a coboundary, hence vanish.
-/

open scoped Pointwise BigOperators

namespace Work.SSGRoute

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]

/-- **The orthogonality content of the p. 18 chase, isolated.**  For a place set `T` of pairwise
non-`K`-conjugate finite places, a cochain `y₁` which vanishes on the local groups of the places of
`T` outside `cs(S)`, a relaxed dual class `b`, and any local Tate system: if the *global* datum `y₁`
satisfies the orthogonality over `T`, then so does the *prescribed* datum `auxDatum K S y₁`. -/
theorem auxDatum_orthogonal_of_part {K Λ M : IntermediateField k Ω} [FiniteDimensional k K]
    [IsGalois k K] [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (S T : Finset (ValuationSubring Ω))
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p)
    (hpair : ZDataMup.IsLocalTateSystem p k Ω K pair)
    (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (y₁ b : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hy₁ : SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup y₁)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup b)
    (hy₁lc : SSGRoute.IsLocConstOn K.fixingSubgroup y₁)
    (hblc : SSGRoute.IsLocConstOn K.fixingSubgroup b)
    (hνS₀ : ∀ A ∈ T, (∀ A' ∈ S, ¬ SSGRoute.IsConjPlace k A' A) →
      ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, y₁ σ = 0)
    (hpart : ∑ A ∈ T, pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) y₁ b = 0) :
    ∑ A ∈ T, pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (auxDatum (p := p) K S y₁ A) b = 0 := by
  classical
  -- restriction of the cocycle/locally-constant conditions to the level-`K` local groups
  have cocy₁ : ∀ A : ValuationSubring Ω, SSGRoute.IsCocycleOn (SSGRoute.res k K)
      (SSGRoute.decomp k A ⊓ K.fixingSubgroup) y₁ :=
    fun A g hg h hh => hy₁ g (Subgroup.mem_inf.mp hg).2 h (Subgroup.mem_inf.mp hh).2
  have loc₁ : ∀ A : ValuationSubring Ω,
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A ⊓ K.fixingSubgroup) y₁ := by
    intro A
    obtain ⟨U, hUo, hUc⟩ := hy₁lc
    exact ⟨U, hUo, fun g hg u hu huH =>
      hUc g (Subgroup.mem_inf.mp hg).2 u hu (Subgroup.mem_inf.mp huH).2⟩
  have cocyb : ∀ A : ValuationSubring Ω, SSGRoute.IsCocycleOn (SSGRoute.res k K)
      (SSGRoute.decomp k A ⊓ K.fixingSubgroup) b :=
    fun A g hg h hh => hb g (Subgroup.mem_inf.mp hg).2 h (Subgroup.mem_inf.mp hh).2
  have locb : ∀ A : ValuationSubring Ω,
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A ⊓ K.fixingSubgroup) b := by
    intro A
    obtain ⟨U, hUo, hUc⟩ := hblc
    exact ⟨U, hUo, fun g hg u hu huH =>
      hUc g (Subgroup.mem_inf.mp hg).2 u hu (Subgroup.mem_inf.mp huH).2⟩
  have cocy0 : ∀ A : ValuationSubring Ω, SSGRoute.IsCocycleOn (SSGRoute.res k K)
      (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (0 : (Ω ≃ₐ[k] Ω) → ZMod p) :=
    fun A g hg h hh => by simp
  have loc0 : ∀ A : ValuationSubring Ω,
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A ⊓ K.fixingSubgroup)
        (0 : (Ω ≃ₐ[k] Ω) → ZMod p) :=
    fun A => ⟨⊤, isOpen_univ, fun g hg u hu huH => rfl⟩
  -- split `T` into the places conjugate into `S` and the others
  set P : ValuationSubring Ω → Prop := fun A => ∃ A' ∈ S, SSGRoute.IsConjPlace k A' A with hP
  have hsplit : ∑ A ∈ T, pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup)
        (auxDatum (p := p) K S y₁ A) b
      = ∑ A ∈ T.filter P, pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) y₁ b := by
    rw [← Finset.sum_filter_add_sum_filter_not T P (fun A =>
      pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (auxDatum (p := p) K S y₁ A) b)]
    have hout : (T.filter (fun A => ¬ P A)).sum (fun A =>
        pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (auxDatum (p := p) K S y₁ A) b) = 0 := by
      refine Finset.sum_eq_zero fun A hA => ?_
      have hnotP : ¬ P A := (Finset.mem_filter.mp hA).2
      have hzero : auxDatum (p := p) K S y₁ A = 0 := by
        simp only [auxDatum, hP] at hnotP ⊢
        rw [if_neg hnotP]
      rw [hzero]
      exact hpair.vanishes_coboundary _ ⟨A, hTfin A (Finset.mem_filter.mp hA).1, rfl⟩ _ b
        ⟨cocy0 A, loc0 A⟩ ⟨cocyb A, locb A⟩
        (Or.inl ⟨0, fun g hg => by simp⟩)
    have hin : (T.filter P).sum (fun A =>
        pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (auxDatum (p := p) K S y₁ A) b)
        = (T.filter P).sum (fun A =>
          pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) y₁ b) := by
      refine Finset.sum_congr rfl fun A hA => ?_
      have hP' : P A := (Finset.mem_filter.mp hA).2
      have : auxDatum (p := p) K S y₁ A = y₁ := by
        simp only [auxDatum, hP] at hP' ⊢
        rw [if_pos hP']
      rw [this]
    rw [hin, hout, add_zero]
  rw [hsplit]
  -- the same splitting for the global datum; the terms outside `cs(S)` vanish by `hνS₀`
  have hsplit' : ∑ A ∈ T, pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) y₁ b
      = ∑ A ∈ T.filter P, pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) y₁ b := by
    rw [← Finset.sum_filter_add_sum_filter_not T P (fun A =>
      pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) y₁ b)]
    have hout : (T.filter (fun A => ¬ P A)).sum (fun A =>
        pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) y₁ b) = 0 := by
      refine Finset.sum_eq_zero fun A hA => ?_
      have hmem := (Finset.mem_filter.mp hA)
      have hnotP : ¬ P A := hmem.2
      have hvan : ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, y₁ σ = 0 :=
        hνS₀ A hmem.1 (by simpa [hP] using hnotP)
      have hcob : SSGRoute.IsCoboundaryOn (SSGRoute.res k K)
          (SSGRoute.decomp k A ⊓ K.fixingSubgroup) y₁ :=
        ⟨0, fun g hg => by rw [hvan g hg]; simp⟩
      exact hpair.vanishes_coboundary _ ⟨A, hTfin A hmem.1, rfl⟩ y₁ b
        ⟨cocy₁ A, loc₁ A⟩ ⟨cocyb A, locb A⟩ (Or.inl hcob)
    rw [hout, add_zero]
  rw [← hsplit']
  exact hpart

end Work.SSGRoute
