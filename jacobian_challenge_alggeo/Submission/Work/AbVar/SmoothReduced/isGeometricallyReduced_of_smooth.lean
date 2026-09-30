/-
Smooth algebras over a field are geometrically reduced.

The mathematical content of this file is the classical theorem (Stacks, tag 00TT/00TV and
tag 00T7) that a smooth algebra over a field is geometrically reduced, together with the
local structure theorem for smooth algebras (Stacks, tag 00UE): a smooth algebra at a prime
`p` is, after inverting some `f ∉ p`, *standard étale* over a polynomial ring
(`Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial`).

The proof runs as follows. Smoothness is stable under base change, so it suffices to prove
that a smooth algebra `B` over a field `K` is reduced, and this we prove for `B` itself
(the statement `IsGeometricallyReduced` is then obtained by base changing to the algebraic
closure of the ground field). Reducedness is a local property, so it suffices to show
`IsReduced B_f` for a *family* of elements `f` generating the unit ideal (see
`isReduced_of_forall_isReduced_away`). For each maximal ideal `m` of `B` the local structure
theorem provides `f ∉ m` such that `B_f` is standard étale over `K[X₁,…,Xₙ]`; hence it
suffices to prove that a standard étale algebra over a polynomial ring over a field is
reduced (`isReduced_of_isStandardEtale_mvPolynomial`). For the latter we use that such an
algebra `S` is étale (hence flat) over the domain `C = K[X₁,…,Xₙ]`, so that `S` embeds into
its generic fibre `S ⊗[C] FractionRing C`; that generic fibre is an étale algebra over the
field `FractionRing C`, hence reduced, so `S` is reduced.
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.AbVar.SmoothReduced

open Polynomial
open scoped TensorProduct

set_option linter.style.haveILetI false

noncomputable section

/-- If `R` is reduced away from a family of elements generating the unit ideal, then `R` is
reduced. (Being reduced is a property that is local for the Zariski topology.) -/
lemma isReduced_of_forall_isReduced_away {R : Type*} [CommRing R] {ι : Type*} (f : ι → R)
    (hspan : Ideal.span (Set.range f) = ⊤) (h : ∀ i, IsReduced (Localization.Away (f i))) :
    IsReduced R := by
  refine ⟨fun x hx => ?_⟩
  -- Each `f i` lies in the radical of the annihilator of `x`.
  have key : ∀ i, f i ∈ (Submodule.annihilator (R ∙ x)).radical := by
    intro i
    have hnil : IsNilpotent (algebraMap R (Localization.Away (f i)) x) := hx.map _
    have hz : algebraMap R (Localization.Away (f i)) x = 0 := (h i).eq_zero _ hnil
    obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (f i)) _ x).mp hz
    obtain ⟨n, hn⟩ := m.2
    refine Ideal.mem_radical_iff.mpr ⟨n, ?_⟩
    rw [Submodule.mem_annihilator_span_singleton]
    simpa [hn, smul_eq_mul] using hm
  -- Since the `f i` generate the unit ideal, `1` lies in that radical, hence `1 * x = 0`.
  have hle : (⊤ : Ideal R) ≤ (Submodule.annihilator (R ∙ x)).radical := by
    rw [← hspan]
    exact Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact key i)
  have h1 : (1 : R) ∈ (Submodule.annihilator (R ∙ x)).radical := hle trivial
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp h1
  rw [Submodule.mem_annihilator_span_singleton] at hn
  simpa using hn

section

attribute [local instance] Algebra.TensorProduct.leftAlgebra

/-- A standard étale algebra over a polynomial ring over a field is reduced.

The algebra is flat over the polynomial ring `C` (standard étale algebras are étale, in
particular smooth, hence flat), so it embeds into its generic fibre over the fraction field
of `C`; that generic fibre is étale over a field, hence reduced. -/
lemma isReduced_of_isStandardEtale_mvPolynomial {K : Type*} [Field K] {n : ℕ} {S : Type*}
    [CommRing S] (a : Algebra (MvPolynomial (Fin n) K) S)
    (h : @Algebra.IsStandardEtale (MvPolynomial (Fin n) K) S _ _ a) : IsReduced S := by
  letI := a
  haveI := h
  have hfib : IsReduced (FractionRing (MvPolynomial (Fin n) K) ⊗[MvPolynomial (Fin n) K] S) :=
    Algebra.FormallyUnramified.isReduced_of_field (FractionRing (MvPolynomial (Fin n) K))
      (FractionRing (MvPolynomial (Fin n) K) ⊗[MvPolynomial (Fin n) K] S)
  exact isReduced_of_injective
    (Algebra.TensorProduct.includeRight (R := MvPolynomial (Fin n) K)
      (A := FractionRing (MvPolynomial (Fin n) K)))
    (Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective _ _))

end

/-- A smooth algebra over a field is reduced. -/
lemma isReduced_of_smooth_of_field (K : Type*) [Field K] (B : Type*) [CommRing B] [Algebra K B]
    [Algebra.Smooth K B] : IsReduced B := by
  classical
  -- Locally at each maximal ideal, `B` is standard étale over a polynomial ring.
  have key : ∀ (m : Ideal B) (hm : m.IsMaximal), ∃ f : B, f ∉ m ∧ IsReduced (Localization.Away f) := by
    intro m hm
    haveI : m.IsPrime := hm.isPrime
    obtain ⟨f, hf, n, instAlg, _hST, hSE⟩ :=
      Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := K) (S := B) (p := m)
    exact ⟨f, hf, isReduced_of_isStandardEtale_mvPolynomial (K := K) (n := n)
      (S := Localization.Away f) instAlg hSE⟩
  let f : {m : Ideal B // m.IsMaximal} → B := fun m => (key m.1 m.2).choose
  have hf_mem : ∀ m, f m ∉ m.1 := fun m => (key m.1 m.2).choose_spec.1
  have hf_red : ∀ m, IsReduced (Localization.Away (f m)) := fun m => (key m.1 m.2).choose_spec.2
  refine isReduced_of_forall_isReduced_away f ?_ hf_red
  -- The chosen elements generate the unit ideal: no maximal ideal contains all of them.
  by_contra h
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
  exact hf_mem ⟨m, hm⟩ (hle (Ideal.subset_span ⟨⟨m, hm⟩, rfl⟩))

theorem isGeometricallyReduced_of_smooth {k A : Type*} [Field k] [CommRing A] [Algebra k A]
    [Algebra.Smooth k A] : Algebra.IsGeometricallyReduced k A := by
  rw [Algebra.isGeometricallyReduced_field_iff]
  exact isReduced_of_smooth_of_field (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] A)

end

end Work.AbVar.SmoothReduced
