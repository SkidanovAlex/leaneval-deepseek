/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# AREA AUTL2 / Normalizer : `N(PSL(2,q)) = PΓL(2,q)`

The main computation of step A3 of the AUTL2 design:

* `Work.AUTL2.Normalizer.le_pgammaL` : every permutation of `ℙ¹(F)`, `F = GF(p^k)` (`p` odd),
  normalizing the image of `PSL(2,F)` lies in `PΓL(2,F)`.

The proof is the classical one: a normalizing permutation `π` is first moved (by an element of
`PSL`) to a permutation `π₁` fixing `∞`, i.e. normalizing the Borel subgroup `B`.  Inside `B`
the translation subgroup `U = {x ↦ x + b}` is characterized by "no fixed point in `F`", hence is
`π₁`-invariant, and conjugation gives an additive bijection `s` of `(F,+)` with
`π₁ ∘ transl b = transl (s b) ∘ π₁`.  From this, `π₁` is affine, `π₁ x = c + s x`; conjugating the
diagonal elements `dil a` (fixed points `0,∞`) gives the square-linearity `s(a²x) = b² s x`, which
(using that every element of `F` is a difference of two squares, char `≠ 2`) makes
`σ := s / s 1` an automorphism of `F` and `s x = s 1 · σ x`.  Hence
`π₁ = transl c ∘ (x ↦ s 1 · x) ∘ galHom σ ∈ PΓL(2,F)`, and so is `π`.

The only two ingredients that are not elementary are supplied as separate lemmas:
`Work.AUTL2.Normalizer.mem_translSub_of_pslImage_of_fpf` (the fixed-point characterization of
translations) and `Work.AUTL2.Normalizer.exists_fieldAut_of_sq_smul` (the square-linearity ⟹
semi-linearity step).
-/
import Mathlib
import Submission.Work.AUTL2.Defs
import Submission.Work.AUTL2.Mobius
import Submission.Work.AUTL2.Stabilizer
import Submission.Work.AUTL2.Normalizer.Defs
import Submission.Work.AUTL2.Normalizer.mem_translSub_of_pslImage_of_fpf
import Submission.Work.AUTL2.Normalizer.exists_fieldAut_of_sq_smul

open scoped MatrixGroups LinearAlgebra.Projectivization
open OnePoint

namespace Work.AUTL2.Normalizer

variable (F : Type*) [Field F] [DecidableEq F]

/-- Conjugation by an element of the normalizer of `pslImage F` that fixes `∞` preserves the
translation subgroup `U = translSub F`. -/
lemma conj_mem_translSub {π : Equiv.Perm (P1 F)}
    (hπ : π ∈ Subgroup.normalizer (pslImage F : Set _)) (hpiinf : π (∞ : P1 F) = ∞)
    {g : Equiv.Perm (P1 F)} (hg : g ∈ translSub F) : π * g * π⁻¹ ∈ translSub F := by
  rcases (mem_translSub_iff F).mp hg with ⟨b, rfl⟩
  rcases eq_or_ne b 0 with rfl | hb
  · rw [transl_zero, mul_one, mul_inv_cancel]
    exact Subgroup.one_mem _
  · refine mem_translSub_of_pslImage_of_fpf F (π * transl F b * π⁻¹) ?_ ?_ ?_
    · exact conj_mem_pslImage F hπ (transl_mem F b)
    · have hinv : π⁻¹ (∞ : P1 F) = ∞ := by
        have h := Equiv.symm_apply_apply π (∞ : P1 F)
        rwa [hpiinf] at h
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hinv, transl_infty, hpiinf]
    · intro x hx
      have hxn : π⁻¹ ((x : F) : P1 F) ≠ ∞ := by
        intro h
        have h' : ((x : F) : P1 F) = ∞ := by
          calc ((x : F) : P1 F) = π (π⁻¹ ((x : F) : P1 F)) :=
                (Equiv.apply_symm_apply π ((x : F) : P1 F)).symm
            _ = π ∞ := by rw [h]
            _ = ∞ := hpiinf
        exact OnePoint.coe_ne_infty x h'
      rcases hy : π⁻¹ ((x : F) : P1 F) with _ | y
      · exact hxn hy
      · exfalso
        have hfix : Work.AUTL2.transl F b (y : P1 F) = (y : P1 F) := by
          have h1 : π (Work.AUTL2.transl F b (π⁻¹ ((x : F) : P1 F))) = ((x : F) : P1 F) := by
            simpa only [Equiv.Perm.mul_apply] using hx
          rw [hy] at h1
          have h4 : ((x : F) : P1 F) = π (y : P1 F) := by
            calc ((x : F) : P1 F) = π (π⁻¹ ((x : F) : P1 F)) :=
                  (Equiv.apply_symm_apply π ((x : F) : P1 F)).symm
              _ = π (y : P1 F) := congrArg π hy
          rw [h4] at h1
          exact π.injective h1
        exact OnePoint.coe_ne_infty y (transl_fixed F b hb (y : P1 F) hfix)

/-- **Step A3, main direction.**  For a field `F` of characteristic `≠ 2`, every permutation of
`ℙ¹(F)` normalizing `pslImage F` lies in `PΓL(2,F) = pglImage F ⊔ galSub F`. -/
theorem le_pgammaL_of_two_ne_zero (h2 : (2 : F) ≠ 0) (π : Equiv.Perm (P1 F))
    (h : π ∈ Subgroup.normalizer (pslImage F : Set _)) : π ∈ pgammaL F := by
  classical
  -- ## Step 1 : move `π` by an element of `PSL` so that it fixes `∞`
  obtain ⟨γ, hγ, hγπ⟩ := exists_pslImage_map_to_infty F (π (∞ : P1 F))
  obtain ⟨π₁, hπ₁def⟩ : ∃ π₁ : Equiv.Perm (P1 F), π₁ = γ * π := ⟨γ * π, rfl⟩
  have hπ₁N : π₁ ∈ Subgroup.normalizer (pslImage F : Set _) := by
    have hγN : γ ∈ Subgroup.normalizer (pslImage F : Set _) :=
      (Subgroup.le_normalizer (H := pslImage F)) hγ
    rw [hπ₁def]
    exact Subgroup.mul_mem _ hγN h
  have hpi1inf : π₁ (∞ : P1 F) = ∞ := by
    rw [hπ₁def, Equiv.Perm.mul_apply]; exact hγπ
  -- ## Step 2 : `π₁` preserves the translation subgroup `U`
  have hU1 : ∀ b : F, π₁ * Work.AUTL2.transl F b * π₁⁻¹ ∈ translSub F :=
    fun b => conj_mem_translSub F hπ₁N hpi1inf (transl_mem_translSub F b)
  have hπ₁invN : π₁⁻¹ ∈ Subgroup.normalizer (pslImage F : Set _) := Subgroup.inv_mem _ hπ₁N
  have hpi1invinf : π₁⁻¹ (∞ : P1 F) = ∞ := by
    have h := Equiv.symm_apply_apply π₁ (∞ : P1 F)
    rwa [hpi1inf] at h
  have hU2 : ∀ b : F, π₁⁻¹ * Work.AUTL2.transl F b * π₁ ∈ translSub F :=
    fun b => conj_mem_translSub F hπ₁invN hpi1invinf (transl_mem_translSub F b)
  -- ## Step 3 : the induced additive bijection `s` of `(F,+)`
  choose s hs using fun b => (mem_translSub_iff F).mp (hU1 b)
  have hconj : ∀ b : F, π₁ * Work.AUTL2.transl F b = Work.AUTL2.transl F (s b) * π₁ := by
    intro b
    rw [hs b]
    group
  have hs_add : ∀ b c : F, s (b + c) = s b + s c := by
    intro b c
    apply transl_injective F
    rw [hs (b + c)]
    calc π₁ * Work.AUTL2.transl F (b + c) * π₁⁻¹
        = π₁ * (Work.AUTL2.transl F b * Work.AUTL2.transl F c) * π₁⁻¹ := by rw [transl_add]
      _ = (π₁ * Work.AUTL2.transl F b * π₁⁻¹) * (π₁ * Work.AUTL2.transl F c * π₁⁻¹) := by
          group
      _ = Work.AUTL2.transl F (s b) * Work.AUTL2.transl F (s c) := by rw [hs b, hs c]
      _ = Work.AUTL2.transl F (s b + s c) := transl_add F (s b) (s c)
  have hs_inj : Function.Injective s := by
    intro b c hbc
    refine transl_injective F ?_
    have h1 : π₁ * Work.AUTL2.transl F b * π₁⁻¹ = π₁ * Work.AUTL2.transl F c * π₁⁻¹ := by
      rw [← hs b, ← hs c, hbc]
    exact mul_left_cancel (mul_right_cancel h1)
  have hs_surj : Function.Surjective s := by
    intro y
    obtain ⟨x, hx⟩ := (mem_translSub_iff F).mp (hU2 y)
    refine ⟨x, ?_⟩
    apply transl_injective F
    rw [hs x, hx]
    group
  have hs_bij : Function.Bijective s := ⟨hs_inj, hs_surj⟩
  have hs1 : s 1 ≠ 0 := by
    intro hz
    have h1 : (1 : Equiv.Perm (P1 F)) = π₁ * Work.AUTL2.transl F 1 * π₁⁻¹ := by
      rw [← hs 1, hz, transl_zero]
    have h2 : Work.AUTL2.transl F 1 = (1 : Equiv.Perm (P1 F)) := by
      calc Work.AUTL2.transl F 1
          = π₁⁻¹ * (π₁ * Work.AUTL2.transl F 1 * π₁⁻¹) * π₁ := by group
        _ = π₁⁻¹ * 1 * π₁ := by rw [← h1]
        _ = 1 := by group
    have h3 : (1 : F) = 0 := transl_injective F (by rw [h2, transl_zero])
    exact one_ne_zero h3
  have hs0 : s 0 = 0 := by
    have hh : s 0 + 0 = s 0 + s 0 := by rw [add_zero]; simpa using hs_add 0 0
    exact (add_left_cancel hh).symm
  -- ## Step 4 : `π₁` is affine, `π₁ x = c + s x`
  have hπ₁0ne : π₁ ((0 : F) : P1 F) ≠ ∞ := by
    intro hc'
    have h' : ((0 : F) : P1 F) = ∞ := by
      calc ((0 : F) : P1 F) = π₁.symm (π₁ ((0 : F) : P1 F)) :=
            (Equiv.symm_apply_apply π₁ ((0 : F) : P1 F)).symm
        _ = π₁.symm ∞ := by rw [hc']
        _ = ∞ := hpi1invinf
    exact OnePoint.coe_ne_infty 0 h'
  obtain ⟨c, hc⟩ : ∃ c : F, π₁ ((0 : F) : P1 F) = (c : P1 F) := by
    rcases h : π₁ ((0 : F) : P1 F) with _ | c
    · exact absurd h hπ₁0ne
    · exact ⟨c, rfl⟩
  have haff : ∀ x : F, π₁ (x : P1 F) = ((c + s x : F) : P1 F) := by
    intro x
    have h' := congrArg (fun f : Equiv.Perm (P1 F) => f ((0 : F) : P1 F)) (hconj x)
    simp only [Equiv.Perm.mul_apply] at h'
    rw [transl_formula, hc, transl_formula, zero_add] at h'
    exact h'
  -- ## Step 5 : square-linearity of `s`
  have hsq : ∀ a : Fˣ, ∃ b : Fˣ, ∀ x : F, s (↑a ^ 2 * x) = ↑b ^ 2 * s x := by
    intro a
    obtain ⟨g, hgdef⟩ : ∃ g : Equiv.Perm (P1 F), g = π₁ * Work.AUTL2.dil F a * π₁⁻¹ :=
      ⟨π₁ * Work.AUTL2.dil F a * π₁⁻¹, rfl⟩
    have hgG : g ∈ pslImage F := by
      rw [hgdef]; exact conj_mem_pslImage F hπ₁N (dil_mem F a)
    have hginf : g (∞ : P1 F) = ∞ := by
      rw [hgdef, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hpi1invinf, dil_infty, hpi1inf]
    obtain ⟨β, b', hβ⟩ := element_fixing_infty F g hgG hginf
    have hgc : g (c : P1 F) = (c : P1 F) := by
      rw [hgdef, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
      have hcinv : π₁⁻¹ (c : P1 F) = ((0 : F) : P1 F) := by
        rw [← hc]; exact Equiv.symm_apply_apply π₁ ((0 : F) : P1 F)
      rw [hcinv, dil_formula, mul_zero]
      exact hc
    have hb' : b' = c - (↑β : F) ^ 2 * c := by
      have h' : (↑β : F) ^ 2 * c + b' = c := by
        have h1 := hβ c
        rw [hgc] at h1
        exact (OnePoint.coe_eq_coe.mp h1).symm
      linear_combination h'
    have hmul : π₁ * Work.AUTL2.dil F a = g * π₁ := by rw [hgdef]; group
    refine ⟨β, fun x => ?_⟩
    have h3 : π₁ ((↑a ^ 2 * x : F) : P1 F) = ((c + s (↑a ^ 2 * x) : F) : P1 F) :=
      haff (↑a ^ 2 * x)
    have h1 : π₁ ((↑a ^ 2 * x : F) : P1 F) = (g * π₁) (x : P1 F) := by
      rw [← hmul, Equiv.Perm.mul_apply, dil_formula]
    have h2 : (g * π₁) (x : P1 F) = ((c + (↑β : F) ^ 2 * ((c + s x) - c) : F) : P1 F) := by
      rw [Equiv.Perm.mul_apply, haff x, hβ (c + s x), hb']
      congr 1
      ring
    have h4 : (c + s (↑a ^ 2 * x) : F) = c + (↑β : F) ^ 2 * ((c + s x) - c) := by
      apply OnePoint.coe_eq_coe.mp
      rw [← h3, h1, h2]
    have h5 : s (↑a ^ 2 * x) = (↑β : F) ^ 2 * s x := by
      have hh := add_left_cancel h4
      rw [hh]; ring
    exact h5
  -- ## Step 6 : `s = s 1 · σ` for a field automorphism `σ`
  obtain ⟨σ, hσ⟩ := exists_fieldAut_of_sq_smul F h2 s hs0 hs_add hs_bij hs1 hsq
  -- ## Step 7 : `π₁ = transl c ∘ (x ↦ s 1 · x) ∘ galHom σ`
  have hπ₁eq : π₁ = Work.AUTL2.transl F c * smulPerm F (s 1) hs1 * Work.AUTL2.galHom F σ := by
    rw [Equiv.ext_iff, OnePoint.forall]
    refine ⟨?_, fun x => ?_⟩
    · rw [hpi1inf, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, galHom_apply_infty,
        smulPerm_infty, transl_infty]
    · rw [haff x, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, galHom_apply_coe, smulPerm_some,
        transl_formula, hσ x]
      congr 1
      ring
  -- ## Step 8 : assembly
  have hπ₁mem : π₁ ∈ pgammaL F := by
    rw [hπ₁eq, pgammaL]
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_
    · exact Subgroup.mem_sup_left (pslImage_le_pglImage F (transl_mem F c))
    · exact Subgroup.mem_sup_left (smulPerm_mem_pglImage F (s 1) hs1)
    · exact Subgroup.mem_sup_right ⟨σ, rfl⟩
  have hγmem : γ⁻¹ ∈ pgammaL F := by
    rw [pgammaL]
    exact Subgroup.mem_sup_left (pslImage_le_pglImage F (Subgroup.inv_mem _ hγ))
  have hπeq : π = γ⁻¹ * π₁ := by rw [hπ₁def]; group
  rw [hπeq]
  exact Subgroup.mul_mem _ hγmem hπ₁mem

/-- **Step A3, main direction (Galois field form)**: `N(P S L(2,q)) ≤ PΓL(2,q)` for `q = p^k`,
`p` odd.  The hypothesis `5 ≤ p ^ k` is not needed for this inclusion. -/
theorem le_pgammaL (p k : ℕ) [Fact p.Prime] [Fintype (GaloisField p k)]
    (hp : Odd p) (hq : 5 ≤ p ^ k) [DecidableEq (GaloisField p k)]
    (π : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)))
    (h : π ∈ Subgroup.normalizer (Work.AUTL2.pslImage (GaloisField p k) : Set _)) :
    π ∈ Work.AUTL2.pgammaL (GaloisField p k) := by
  have h2 : (2 : GaloisField p k) ≠ 0 := by
    intro hz
    have hd : p ∣ 2 := (CharP.cast_eq_zero_iff (GaloisField p k) p 2).mp hz
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hd
    have hgt : 1 < p := (Fact.out : p.Prime).one_lt
    obtain ⟨m, hm⟩ := hp
    omega
  exact le_pgammaL_of_two_ne_zero (GaloisField p k) h2 π h

end Work.AUTL2.Normalizer
