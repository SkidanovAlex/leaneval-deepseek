/-
# Area BG: Bender–Glauberman 1981, Lemma 2.4 (`Work.GW2.C16.Lemma24Prop`), p. 207

Source: H. Bender and G. Glauberman, *Characters of finite groups with dihedral Sylow
2-subgroups*, J. Algebra **70** (1981) 200–215.  The paper's statement (p. 207) is

  **LEMMA 2.4.** Let `χ ∈ ±Irr(G)`.  Then `χ = Σ_{ν ∈ 𝒮(χ)} (χ, ν̃)_G ν` on `T`
  and `χ ≡ Σ_{ν ∈ 𝒮(χ)} ν (mod 2)` on `U`,

where `𝒮(χ) = {ν ∈ Irr(H₁) | (χ, ν̃) ≠ 0}` and `ν̃` is the coherent extension of `ν`
(BG Theorem 2.3).  The formal statement `Work.GW2.C16.Lemma24Prop C` additionally
asserts that `𝒮(χ)` is finite.

Route (the paper's own, "It follows directly from Lemmas 1.6 and 1.7 (choose the
`νᵢ` subject to `(χ, ν̃ᵢ)_G = 0`)"):

* **Identity on `T`.**  BG Lemma 1.7 (`Work.BG.s02_lemma17T`) with a transversal `rep`
  of the `Λ`-orbits gives `χ(g) = Σ_ν (χ, (ν − rep ν)^G) ν(g)` for `g ∈ T`;  coherence
  (BG 2.3(iii)) rewrites `(ν − rep ν)^G = f ν − f (rep ν)`.  The `rep`-part
  `Σ_ν (χ, f (rep ν)) ν(g)` is constant on `Λ`-orbits and hence vanishes on `T`
  (`Work.BG.s02_orbitConstant_sum_eq_zero`, a weighted form of BG 1.7(i)).  What is
  left is `Σ_{ν ∈ Irr(H₀)} (χ, ν̃) ν(g)`, and restricting to the non-zero coefficients
  gives the finsum over `𝒮(χ) = bset C f χ`
  (`Work.BG.s02_sum_irr_eq_finsum_bset`).
* **Congruence on `U`.**  For `u ∈ U` the element `t·u` lies in `T`, so the identity on
  `T` computes `χ(tu)`;  BG Lemma 1.6 (`Work.BG.lemma16_mod_two`, as packaged in
  `Work.BG.s02_char16_t_mul` and `Work.BG.s02_char16_val_t_mul`) gives
  `χ(tu) ≡ χ(u)` and `ν(tu) ≡ ν(u)` for every `ν ∈ Irr(H₀)`;  finally
  `(χ, ν̃) ∈ {±1}` for `ν ∈ 𝒮(χ)` (`Work.BG.inner_pmIrr_eq_pm_one`), so each coefficient
  may be replaced by `1` modulo two.

The helper `Work.BG.orbitRep` (a `Λ`-orbit transversal of `Irr(H₀)`, built from the
quotient by `LamEquiv`) is the `rep` used in Lemma 1.7.
-/

import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.lemma16_mod_two
import Submission.Work.BG.s02_lemma17T
import Submission.Work.BG.s02_lemma22Sq
import Submission.Work.BG.s02_assemblyCore
import Submission.Work.BG.s02_orbitConstant_sum_eq_zero
import Submission.Work.BG.s02_bset_finite
import Submission.Work.BG.s02_sum_irr_eq_finsum_bset
import Submission.Work.BG.inner_pmIrr_eq_pm_one
import Submission.Work.BG.s02_char16_t_mul
import Submission.Work.BG.s02_char16_val_t_mul
import Submission.OddOrder.Algebra.GaloisRationalInteger

namespace Work.BG

open OddOrder.RepresentationTheory

/-! ## 1. A `Λ`-orbit transversal of `Irr(H₀)` -/

section OrbitRep

variable {G : Type} [Group G] [Finite G]

/-- The `Λ`-equivalence relation on `Irr(H₀)` (`Λ`-orbits, BG p. 205). -/
def irrLamSetoid (C : Sec2Ctx G) : Setoid (IrreducibleCharacter ↥C.P.H0) where
  r μ ν := LamEquiv C (μ : ClassFunction ↥C.P.H0 ℂ) (ν : ClassFunction ↥C.P.H0 ℂ)
  iseqv := ⟨fun μ => s02c_LamEquiv_refl C _,
    fun h => s02c_LamEquiv_symm C h,
    fun h1 h2 => s02c_LamEquiv_trans C h1 h2⟩

/-- A representative of the `Λ`-orbit of `ν`;  constant on `Λ`-orbits. -/
noncomputable def orbitRep (C : Sec2Ctx G) (ν : IrreducibleCharacter ↥C.P.H0) :
    IrreducibleCharacter ↥C.P.H0 :=
  Quotient.out (Quotient.mk (irrLamSetoid C) ν)

/-- The representative is `Λ`-equivalent to `ν`. -/
theorem orbitRep_mem (C : Sec2Ctx G) (ν : IrreducibleCharacter ↥C.P.H0) :
    LamEquiv C (ν : ClassFunction ↥C.P.H0 ℂ) (orbitRep C ν : ClassFunction ↥C.P.H0 ℂ) := by
  have h := Quotient.out_eq (Quotient.mk (irrLamSetoid C) ν)
  exact s02c_LamEquiv_symm C (Quotient.exact h)

/-- Equivalent irreducibles have the same representative. -/
theorem orbitRep_eq_of_lamEquiv {C : Sec2Ctx G} {μ ν : IrreducibleCharacter ↥C.P.H0}
    (h : LamEquiv C (μ : ClassFunction ↥C.P.H0 ℂ) (ν : ClassFunction ↥C.P.H0 ℂ)) :
    orbitRep C μ = orbitRep C ν :=
  congrArg Quotient.out (Quotient.sound h)

end OrbitRep

/-! ## 2. Elementary calculus of `≡ (mod 2)` for algebraic integers -/

namespace AlgIntModTwo

/-- A finite sum of componentwise congruences. -/
theorem sum {ι : Type} (s : Finset ι) {a b : ι → ℂ}
    (h : ∀ i ∈ s, AlgIntModTwo (a i) (b i)) :
    AlgIntModTwo (∑ i ∈ s, a i) (∑ i ∈ s, b i) := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨0, isIntegral_zero, by simp⟩
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (h i (Finset.mem_insert_self i s)).add
        (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- Multiplication of a congruence by an algebraic integer. -/
theorem mul {c a b : ℂ} (hc : IsIntegral ℤ c) (h : AlgIntModTwo a b) :
    AlgIntModTwo (c * a) (c * b) := by
  obtain ⟨z, hz, hzab⟩ := h
  exact ⟨c * z, hc.mul hz, by linear_combination c * hzab⟩

/-- `-a ≡ a (mod 2)` for an algebraic integer `a`. -/
theorem neg_self {a : ℂ} (ha : IsIntegral ℤ a) : AlgIntModTwo (-a) a :=
  ⟨-a, ha.neg, by ring⟩

/-- A finite sum (over a set) of componentwise congruences. -/
theorem finsum_mem {α : Type} {s : Set α} (hs : s.Finite) {a b : α → ℂ}
    (h : ∀ i ∈ s, AlgIntModTwo (a i) (b i)) :
    AlgIntModTwo (∑ᶠ i ∈ s, a i) (∑ᶠ i ∈ s, b i) := by
  rw [finsum_mem_eq_finite_toFinset_sum a hs, finsum_mem_eq_finite_toFinset_sum b hs]
  exact sum hs.toFinset fun i hi => h i ((Set.Finite.mem_toFinset hs).mp hi)

end AlgIntModTwo

/-- Signed irreducible characters are virtual characters. -/
theorem mem_ZIrr_of_isPmIrr {K : Type} [Group K] {φ : ClassFunction K ℂ}
    (h : IsPmIrr φ) : φ ∈ ZIrr K := by
  rcases h with h | h
  · exact IsIrreducibleCharacter.mem_ZIrr h
  · simpa using Submodule.neg_mem (p := ZIrr K) (IsIrreducibleCharacter.mem_ZIrr h)

/-! ## 3. BG Lemma 2.4 -/

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem lemma24 {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.GW2.C16.Lemma24Prop C := by
  classical
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  intro f hf χ hχ
  -- coherence data at an irreducible character of `H₀`
  have hgood : ∀ (ν : ClassFunction ↥C.P.H0 ℂ), IsIrreducibleCharacter ν →
      f ν ∈ ZIrr G ∧
        (ClassFunction.inner (f ν) (f ν) = 1 ∨ ClassFunction.inner (f ν) (f ν) = 2) := by
    intro ν hν
    have hG := (hf.1 ν hν) ν (Or.inl (s02c_LamEquiv_refl C ν)) ν
      (Or.inl (s02c_LamEquiv_refl C ν)) hν hν
    refine ⟨hG.1, ?_⟩
    have h := hG.2.2.1
    by_cases hss : sconj C ν = ν
    · exact Or.inr (by simpa [hss] using h)
    · exact Or.inl (by simpa [hss] using h)
  -- the `Λ`-orbit transversal, lifted to all class functions
  let rep : ClassFunction ↥C.P.H0 ℂ → ClassFunction ↥C.P.H0 ℂ := fun ξ =>
    if h : IsIrreducibleCharacter ξ then
      (orbitRep C ⟨ξ, h⟩ : ClassFunction ↥C.P.H0 ℂ) else ξ
  have hrep_val : ∀ ν : IrreducibleCharacter ↥C.P.H0,
      rep (ν : ClassFunction ↥C.P.H0 ℂ) =
        (orbitRep C ⟨(ν : ClassFunction ↥C.P.H0 ℂ), ν.2⟩ : ClassFunction ↥C.P.H0 ℂ) := by
    intro ν
    simp only [rep, dif_pos ν.2]
  have hrep_irr : ∀ ν : IrreducibleCharacter ↥C.P.H0,
      IsIrreducibleCharacter (rep (ν : ClassFunction ↥C.P.H0 ℂ)) := by
    intro ν
    rw [hrep_val ν]
    exact (orbitRep C ⟨(ν : ClassFunction ↥C.P.H0 ℂ), ν.2⟩).2
  have hrep_lam : ∀ ν : IrreducibleCharacter ↥C.P.H0,
      LamEquiv C (ν : ClassFunction ↥C.P.H0 ℂ) (rep (ν : ClassFunction ↥C.P.H0 ℂ)) := by
    intro ν
    rw [hrep_val ν]
    exact orbitRep_mem C ⟨(ν : ClassFunction ↥C.P.H0 ℂ), ν.2⟩
  have hrep_const : ∀ ν ν' : IrreducibleCharacter ↥C.P.H0,
      LamEquiv C (ν : ClassFunction ↥C.P.H0 ℂ) (ν' : ClassFunction ↥C.P.H0 ℂ) →
      rep (ν : ClassFunction ↥C.P.H0 ℂ) = rep (ν' : ClassFunction ↥C.P.H0 ℂ) := by
    intro ν ν' h
    rw [hrep_val ν, hrep_val ν']
    exact congrArg (fun x : IrreducibleCharacter ↥C.P.H0 => (x : ClassFunction ↥C.P.H0 ℂ))
      (orbitRep_eq_of_lamEquiv (C := C) h)
  -- **(i)** the identity on `T = H₀ ∖ U`
  have hT : ∀ g : ↥C.P.H0, (g : G) ∉ C.P.U →
      χ (g : G) = ∑ᶠ ν ∈ Work.GW2.C16.bset C f χ,
        ClassFunction.inner χ (f ν) * ν g := by
    intro g hg
    -- BG Lemma 1.7 with the chosen transversal
    have h17 : χ (g : G) = ∑ ν : IrreducibleCharacter ↥C.P.H0,
        ClassFunction.inner χ
            (ind C ((ν : ClassFunction ↥C.P.H0 ℂ) - rep (ν : ClassFunction ↥C.P.H0 ℂ))) *
          (ν : ClassFunction ↥C.P.H0 ℂ) g :=
      s02_lemma17T C χ rep (fun ν => ⟨hrep_irr ν, hrep_lam ν⟩) hrep_const g hg
    -- coherence: `(ν − rep ν)^{H₀→G} = f ν − f (rep ν)`
    have hstep : ∀ ν : IrreducibleCharacter ↥C.P.H0,
        ClassFunction.inner χ
            (ind C ((ν : ClassFunction ↥C.P.H0 ℂ) - rep (ν : ClassFunction ↥C.P.H0 ℂ))) =
          ClassFunction.inner χ (f (ν : ClassFunction ↥C.P.H0 ℂ)) -
            ClassFunction.inner χ (f (rep (ν : ClassFunction ↥C.P.H0 ℂ))) := by
      intro ν
      have hG := (hf.1 (ν : ClassFunction ↥C.P.H0 ℂ) ν.2)
        (ν : ClassFunction ↥C.P.H0 ℂ) (Or.inl (s02c_LamEquiv_refl C _))
        (rep (ν : ClassFunction ↥C.P.H0 ℂ)) (Or.inl (hrep_lam ν)) ν.2 (hrep_irr ν)
      have hind : ind C ((ν : ClassFunction ↥C.P.H0 ℂ) -
          rep (ν : ClassFunction ↥C.P.H0 ℂ)) =
          f (ν : ClassFunction ↥C.P.H0 ℂ) - f (rep (ν : ClassFunction ↥C.P.H0 ℂ)) :=
        hG.2.2.2.1 (hrep_lam ν)
      rw [hind, ClassFunction.inner_sub_right]
    -- the `rep`-part vanishes on `T`
    have hzero : (∑ ν : IrreducibleCharacter ↥C.P.H0,
        ClassFunction.inner χ (f (rep (ν : ClassFunction ↥C.P.H0 ℂ))) *
          (ν : ClassFunction ↥C.P.H0 ℂ) g) = 0 :=
      s02_orbitConstant_sum_eq_zero C
        (fun ν : IrreducibleCharacter ↥C.P.H0 =>
          ClassFunction.inner χ (f (rep (ν : ClassFunction ↥C.P.H0 ℂ))))
        (fun μ ν h => by rw [hrep_const μ ν h]) hg
    have hsplit : (∑ ν : IrreducibleCharacter ↥C.P.H0,
          ClassFunction.inner χ
              (ind C ((ν : ClassFunction ↥C.P.H0 ℂ) - rep (ν : ClassFunction ↥C.P.H0 ℂ))) *
            (ν : ClassFunction ↥C.P.H0 ℂ) g) =
        (∑ ν : IrreducibleCharacter ↥C.P.H0,
            ClassFunction.inner χ (f (ν : ClassFunction ↥C.P.H0 ℂ)) *
              (ν : ClassFunction ↥C.P.H0 ℂ) g) -
          ∑ ν : IrreducibleCharacter ↥C.P.H0,
            ClassFunction.inner χ (f (rep (ν : ClassFunction ↥C.P.H0 ℂ))) *
              (ν : ClassFunction ↥C.P.H0 ℂ) g := by
      have h1 : (∑ ν : IrreducibleCharacter ↥C.P.H0,
            ClassFunction.inner χ
                (ind C ((ν : ClassFunction ↥C.P.H0 ℂ) - rep (ν : ClassFunction ↥C.P.H0 ℂ))) *
              (ν : ClassFunction ↥C.P.H0 ℂ) g) =
          ∑ ν : IrreducibleCharacter ↥C.P.H0,
            (ClassFunction.inner χ (f (ν : ClassFunction ↥C.P.H0 ℂ)) *
                (ν : ClassFunction ↥C.P.H0 ℂ) g -
              ClassFunction.inner χ (f (rep (ν : ClassFunction ↥C.P.H0 ℂ))) *
                (ν : ClassFunction ↥C.P.H0 ℂ) g) :=
        Finset.sum_congr rfl fun ν _ => by rw [hstep ν, sub_mul]
      rw [h1, Finset.sum_sub_distrib]
    have hmain : χ (g : G) = ∑ ν : IrreducibleCharacter ↥C.P.H0,
        ClassFunction.inner χ (f (ν : ClassFunction ↥C.P.H0 ℂ)) *
          (ν : ClassFunction ↥C.P.H0 ℂ) g := by
      rw [h17, hsplit, hzero, sub_zero]
    rw [hmain]
    exact s02_sum_irr_eq_finsum_bset C f χ
      (fun ξ => ClassFunction.inner χ (f ξ) * ξ g)
      (fun ν hν => by
        have hzero' : ClassFunction.inner χ (f (ν : ClassFunction ↥C.P.H0 ℂ)) = 0 := by
          by_contra hc
          exact hν ⟨ν.2, hc⟩
        rw [hzero', zero_mul])
  refine ⟨s02_bset_finite C f χ, hT, ?_⟩
  -- **(ii)** the congruence on `U`
  intro u hu
  have htu : (((C.t * u : ↥C.P.H0)) : G) ∉ C.P.U := by
    intro hmem
    have h1 : ((C.t : G) * (u : G)) * (u : G)⁻¹ ∈ C.P.U := by
      have h2 := C.P.U.mul_mem hmem (C.P.U.inv_mem hu)
      simpa [Subgroup.coe_mul, map_inv] using h2
    have h3 : (C.t : G) ∈ C.P.U := by
      have h1' : (C.t : G) * ((u : G) * (u : G)⁻¹) ∈ C.P.U := by
        simpa only [mul_assoc] using h1
      simpa using h1'
    exact C.t_not_mem_U h3
  have hcoe : (((C.t * u : ↥C.P.H0)) : G) = (C.t : G) * (u : G) := rfl
  have hkey := hT (C.t * u) htu
  -- `χ(tu) ≡ χ(u)`
  have h1 : AlgIntModTwo (χ (u : G)) (χ ((C.t : G) * (u : G))) :=
    (s02_char16_t_mul C hu χ (mem_ZIrr_of_isPmIrr hχ)).symm
  -- `χ(tu) = Σ_{ν ∈ 𝒮(χ)} (χ, ν̃) ν(tu)`
  have h2 : AlgIntModTwo (χ ((C.t : G) * (u : G)))
      (∑ᶠ ν ∈ Work.GW2.C16.bset C f χ,
        ClassFunction.inner χ (f ν) * ν (C.t * u)) := by
    rw [← hcoe, hkey]
    exact ⟨0, isIntegral_zero, by ring⟩
  -- the pointwise congruences
  have hpoint : ∀ ν ∈ Work.GW2.C16.bset C f χ,
      AlgIntModTwo (ClassFunction.inner χ (f ν) * ν (C.t * u)) (ν u) := by
    intro ν hν
    obtain ⟨hirr, hne⟩ := hν
    have hcoef : ClassFunction.inner χ (f ν) = 1 ∨ ClassFunction.inner χ (f ν) = -1 :=
      inner_pmIrr_eq_pm_one (hgood ν hirr).1 (hgood ν hirr).2 hχ hne
    have hval : AlgIntModTwo (ν (C.t * u)) (ν u) := by
      have h := s02_char16_val_t_mul C hu (⟨ν, hirr⟩ : IrreducibleCharacter ↥C.P.H0)
      simpa using h
    rcases hcoef with hc | hc
    · rw [hc, one_mul]
      exact hval
    · rw [hc, neg_one_mul]
      have hint : IsIntegral ℤ (ν u) :=
        OddOrder.Algebra.isIntegral_apply_of_mem_ZIrr
          (G := ↥C.P.H0) (φ := ν) (IsIrreducibleCharacter.mem_ZIrr hirr) u
      exact (hval.neg).trans (AlgIntModTwo.neg_self hint)
  have hsum : AlgIntModTwo
      (∑ᶠ ν ∈ Work.GW2.C16.bset C f χ, ClassFunction.inner χ (f ν) * ν (C.t * u))
      (∑ᶠ ν ∈ Work.GW2.C16.bset C f χ, ν u) :=
    AlgIntModTwo.finsum_mem (s02_bset_finite C f χ) hpoint
  exact h1.trans (h2.trans hsum)

end Work.BG
