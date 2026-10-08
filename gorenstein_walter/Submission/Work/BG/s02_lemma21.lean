import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.centralValue
import Submission.Work.BG.Lambda
import Submission.Work.BG.CharBridge
import Submission.Work.BG.s02_lemma21_aux
import Submission.Work.BG.s02_lemma21_kerSq
import Submission.Work.BG.s02_lemma21_halves

set_option linter.style.haveILetI false

namespace Work.BG

open OddOrder.RepresentationTheory
open Subgroup

variable {G : Type} [Group G] [Finite G]

/-- Conversion between a `Finset` filter over `univ` and the cardinality of the subtype. -/
theorem finset_filter_card {α : Type} [Fintype α] (p : α → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card = Nat.card {x : α // p x} := by
  rw [← Fintype.card_eq_nat_card, Fintype.card_subtype]

/-! ## 7. The stabiliser of `ν` and the fixed points of `s` -/

/-- The stabiliser `Λ_ν` of `ν` in `Λ`, as a subgroup. -/
noncomputable def stabLam (C : Sec2Ctx G) (ν : ClassFunction ↥C.P.H0 ℂ) :
    Subgroup (Lam C) where
  carrier := {β | lamCF C β * ν = ν}
  one_mem' := s02c_lamCF_one_mul C ν
  mul_mem' := by
    intro a b ha hb
    show lamCF C (a * b) * ν = ν
    rw [s02c_lamCF_mul, s02c_cf_mul_assoc, hb, ha]
  inv_mem' := by
    intro a ha
    show lamCF C a⁻¹ * ν = ν
    have h : lamCF C a⁻¹ * (lamCF C a * ν) = lamCF C a⁻¹ * ν := by rw [ha]
    simp only [← s02c_cf_mul_assoc, ← s02c_lamCF_mul, lam_inv_mul_cancel,
      s02c_lamCF_one_mul] at h
    exact h.symm

theorem mem_stabLam (C : Sec2Ctx G) (ν : ClassFunction ↥C.P.H0 ℂ)
    {β : Lam C} : β ∈ stabLam C ν ↔ lamCF C β * ν = ν := Iff.rfl

/-- `ν(t) ≠ 0` for irreducible `ν` (`t` is an involution). -/
theorem value_t_ne_zero (C : Sec2Ctx G) (ν : ClassFunction ↥C.P.H0 ℂ)
    (hν : IsIrreducibleCharacter ν) : ν C.t ≠ 0 := by
  have hc := centralValue C ν hν
  rcases hc.1 with h | h
  · rw [h]; exact hc.2
  · rw [h]; exact neg_ne_zero.mpr hc.2

/-- If `ν^s = λ_{βμ} ν` then `λ_{βμ}(t) = 1`. -/
theorem sconj_eq_mul_apply_t (C : Sec2Ctx G) (ν : ClassFunction ↥C.P.H0 ℂ)
    (hν : IsIrreducibleCharacter ν) {βμ : Lam C} (hβμ : sconj C ν = lamCF C βμ * ν) :
    lamCF C βμ C.t = 1 := by
  have h := congrArg (fun f : ClassFunction ↥C.P.H0 ℂ => f C.t) hβμ
  rw [sconj_apply_t, ClassFunction.mul_apply] at h
  have h1 : (1 : ℂ) * ν C.t = lamCF C βμ C.t * ν C.t := by rw [one_mul]; exact h
  exact (mul_right_cancel₀ (value_t_ne_zero C ν hν) h1).symm

/-- An element `λ` of `Λ` with `λν = ν` is trivial at `t`. -/
theorem mul_eq_self_apply_t_eq_one (C : Sec2Ctx G) (ν : ClassFunction ↥C.P.H0 ℂ)
    (hν : IsIrreducibleCharacter ν) {β : Lam C} (hβ : lamCF C β * ν = ν) :
    lamCF C β C.t = 1 := by
  have h := congrArg (fun f : ClassFunction ↥C.P.H0 ℂ => f C.t) hβ
  rw [ClassFunction.mul_apply] at h
  have h1 : (1 : ℂ) * ν C.t = lamCF C β C.t * ν C.t := by rw [one_mul]; exact h.symm
  exact (mul_right_cancel₀ (value_t_ne_zero C ν hν) h1).symm

/-- The stabiliser `Λ_ν` is contained in `ker(ev_t)`. -/
theorem stabLam_subset_kerSet (C : Sec2Ctx G) (ν : ClassFunction ↥C.P.H0 ℂ)
    (hν : IsIrreducibleCharacter ν) :
    (stabLam C ν : Set (Lam C)) ⊆ kerSet C := by
  intro β hβ
  rw [mem_kerSet]
  exact mul_eq_self_apply_t_eq_one C ν hν hβ

/-- `(λ_β ν)^s = λ_{β⁻¹} λ_{βμ} ν` when `ν^s = λ_{βμ} ν`. -/
theorem sconj_mul_lam (C : Sec2Ctx G) (ν : ClassFunction ↥C.P.H0 ℂ)
    {βμ β : Lam C} (hβμ : sconj C ν = lamCF C βμ * ν) :
    sconj C (lamCF C β * ν) = lamCF C (β⁻¹ * βμ) * ν := by
  rw [sconjLam C β ν, hβμ, ← s02c_cf_mul_assoc, ← s02c_lamCF_mul]

/-- The fixed points of `s` in the orbit correspond to the `β` with `β² ∈ βμ · Λ_ν`. -/
theorem sconj_fixed_iff (C : Sec2Ctx G) (ν : ClassFunction ↥C.P.H0 ℂ)
    {βμ : Lam C} (hβμ : sconj C ν = lamCF C βμ * ν) (β : Lam C) :
    sconj C (lamCF C β * ν) = lamCF C β * ν ↔
      β * β ∈ ({x : Lam C | ∃ k ∈ stabLam C ν, x = βμ * k} : Set (Lam C)) := by
  rw [sconj_mul_lam C ν hβμ, Set.mem_ofPred_eq]
  have key : (lamCF C (β⁻¹ * βμ) * ν = lamCF C β * ν) ↔
      ((β⁻¹ * βμ)⁻¹ * β ∈ stabLam C ν) := by
    constructor
    · intro h
      have h2 := congrArg (fun z : ClassFunction ↥C.P.H0 ℂ =>
        lamCF C ((β⁻¹ * βμ)⁻¹) * z) h
      simp only [← s02c_cf_mul_assoc, ← s02c_lamCF_mul, lam_inv_mul_cancel,
        s02c_lamCF_one_mul] at h2
      rw [mem_stabLam]
      exact h2.symm
    · intro h
      rw [mem_stabLam] at h
      have h2 := congrArg (fun z : ClassFunction ↥C.P.H0 ℂ =>
        lamCF C (β⁻¹ * βμ) * z) h
      have he : (β⁻¹ * βμ) * ((β⁻¹ * βμ)⁻¹ * β) = β := lam_conj C (β⁻¹ * βμ) β
      simp only [← s02c_cf_mul_assoc, ← s02c_lamCF_mul, he] at h2
      exact h2.symm
  rw [key]
  constructor
  · intro hk
    refine ⟨βμ⁻¹ * (β * β), ?_, ?_⟩
    · have he : βμ⁻¹ * (β * β) = (β⁻¹ * βμ)⁻¹ * β := by
        simp only [lam_mul_inv_rev, lam_inv_inv, lam_mul_assoc]
      rwa [he]
    · rw [← lam_mul_assoc, lam_mul_inv_cancel, lam_one_mul]
  · rintro ⟨k, hk, hkβ⟩
    have hmem : βμ⁻¹ * (β * β) ∈ stabLam C ν := by
      rw [hkβ, ← lam_mul_assoc, lam_inv_mul_cancel, lam_one_mul]
      exact hk
    have heq : (β⁻¹ * βμ)⁻¹ * β = βμ⁻¹ * (β * β) := by
      simp only [lam_mul_inv_rev, lam_inv_inv, lam_mul_assoc]
    rwa [heq]

/-! ## 8. The fibre of the squaring map over a square -/

/-- The solutions of `x² = y` for a square `y` form a coset of the `2`-torsion of `Λ`,
so there are exactly two of them. -/
theorem card_sqFiber (C : Sec2Ctx G) {y : Lam C} (hy : y ∈ sqSet C) :
    Nat.card {x : Lam C // x * x = y} = 2 := by
  classical
  obtain ⟨w, hw⟩ := hy
  have hconv : Nat.card {x : Lam C // x * x = y} =
      (Finset.univ.filter (fun x : Lam C => x * x = y)).card := (finset_filter_card _).symm
  rw [hconv]
  have himg : (Finset.univ.filter (fun x : Lam C => x * x = y)) =
      (Finset.univ.filter (fun z : Lam C => z * z = 1)).image (fun z => w * z) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hx
      refine ⟨w⁻¹ * x, ?_, ?_⟩
      · have he : (w⁻¹ * x) * (w⁻¹ * x) = w⁻¹ * w⁻¹ * (x * x) :=
          lam_mul_mul_mul_comm C w⁻¹ x w⁻¹ x
        rw [he, hx, ← hw, lam_mul_mul_mul_comm C w⁻¹ w⁻¹ w w]
        simp only [lam_inv_mul_cancel, lam_one_mul]
      · rw [lam_conj C w x]
    · rintro ⟨z, hz, rfl⟩
      have he : (w * z) * (w * z) = w * w * (z * z) := lam_mul_mul_mul_comm C w z w z
      rw [he, hz, lam_mul_one, hw]
  rw [himg, Finset.card_image_of_injOn (fun a _ b _ h => lam_mul_left_cancel C h)]
  rw [finset_filter_card (fun z : Lam C => z * z = 1)]
  have : Nat.card {z : Lam C // z * z = 1} = (torsionSet C).ncard := rfl
  rw [this, ncard_torsionSet]

/-! ## 9. The coset `βμ · Λ_ν` -/

/-- The coset `βμ · Λ_ν` of `Λ`. -/
noncomputable def cosetK (C : Sec2Ctx G) (ν : ClassFunction ↥C.P.H0 ℂ) (βμ : Lam C) :
    Set (Lam C) := {x | ∃ k ∈ stabLam C ν, x = βμ * k}

theorem mem_cosetK (C : Sec2Ctx G) (ν : ClassFunction ↥C.P.H0 ℂ) (βμ : Lam C)
    {x : Lam C} : x ∈ cosetK C ν βμ ↔ ∃ k ∈ stabLam C ν, x = βμ * k := Iff.rfl

/-- The coset `βμ · Λ_ν` has as many elements as `Λ_ν`. -/
theorem card_cosetK (C : Sec2Ctx G) (ν : ClassFunction ↥C.P.H0 ℂ) (βμ : Lam C) :
    Nat.card {x : Lam C // x ∈ cosetK C ν βμ} = Nat.card ↥(stabLam C ν) :=
  (Nat.card_congr (Equiv.subtypeEquiv (lamMulLeft C βμ) (fun k => by
    show (k ∈ stabLam C ν) ↔ ((lamMulLeft C βμ) k ∈ cosetK C ν βμ)
    rw [lamMulLeft_apply, mem_cosetK]
    constructor
    · intro hk; exact ⟨k, hk, rfl⟩
    · rintro ⟨k', hk', hkk'⟩
      have : k = k' := lam_mul_left_cancel C hkk'
      rwa [this]))).symm

/-! ## 10. The number of `s`-fixed points in an `s`-stable orbit -/

theorem card_fixed (C : Sec2Ctx G) (ν : ClassFunction ↥C.P.H0 ℂ)
    (hν : IsIrreducibleCharacter ν) {βμ : Lam C} (hβμ : sconj C ν = lamCF C βμ * ν) :
    {χ ∈ lamOrbit C ν | sconj C χ = χ}.ncard = 2 := by
  classical
  -- `βμ` is a square
  have hβμ_sq : ∃ a : Lam C, a * a = βμ := by
    have hker : βμ ∈ kerSet C := by
      rw [mem_kerSet]
      exact sconj_eq_mul_apply_t C ν hν hβμ
    rwa [← s02_lemma21_kerSq C] at hker
  obtain ⟨a, ha⟩ := hβμ_sq
  -- elements of `Λ_ν` are squares
  have hK_sq : ∀ k ∈ stabLam C ν, ∃ w : Lam C, w * w = k := by
    intro k hk
    have hker : k ∈ kerSet C := stabLam_subset_kerSet C ν hν hk
    rwa [← s02_lemma21_kerSq C] at hker
  set Ψ : Lam C → ClassFunction ↥C.P.H0 ℂ := fun β => lamCF C β * ν with hΨ
  set Sol : Finset (Lam C) :=
    Finset.univ.filter (fun β : Lam C => β * β ∈ cosetK C ν βμ) with hSol
  set cosF : Finset (Lam C) :=
    Finset.univ.filter (fun x : Lam C => x ∈ cosetK C ν βμ) with hcosF
  set imF : Finset (ClassFunction ↥C.P.H0 ℂ) := Sol.image Ψ with himF
  have hterm1 : ∀ y ∈ cosF, (Finset.univ.filter (fun β : Lam C => β * β = y)).card = 2 := by
    intro y hy
    have hyc : y ∈ cosetK C ν βμ := by
      rw [hcosF, Finset.mem_filter] at hy; exact hy.2
    rw [mem_cosetK] at hyc
    obtain ⟨k, hk, hky⟩ := hyc
    obtain ⟨w, hw⟩ := hK_sq k hk
    have hysq : y ∈ sqSet C := by
      refine ⟨a * w, ?_⟩
      have he : (a * w) * (a * w) = a * a * (w * w) := lam_mul_mul_mul_comm C a w a w
      rw [he, ha, hw, ← hky]
    rw [finset_filter_card (fun β : Lam C => β * β = y)]
    exact card_sqFiber C hysq
  have hsum1 : Sol.card =
      ∑ y ∈ cosF, (Finset.univ.filter (fun β : Lam C => β * β = y)).card := by
    rw [hSol]
    have hfil : (Finset.univ.filter (fun β : Lam C => β * β ∈ cosetK C ν βμ)) =
        (Finset.univ.filter (fun β : Lam C => β * β ∈ cosF)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hcosF]
      simp
    rw [hfil, ← Finset.sum_card_fiberwise_eq_card_filter]
  have hcosFcard : cosF.card = Nat.card ↥(stabLam C ν) := by
    have h1 : cosF.card = Nat.card {x : Lam C // x ∈ cosetK C ν βμ} := by
      rw [hcosF, finset_filter_card]
    rw [h1]
    exact card_cosetK C ν βμ
  have h1 : Sol.card = 2 * Nat.card ↥(stabLam C ν) := by
    rw [hsum1, Finset.sum_congr rfl hterm1]
    rw [Finset.sum_const_nat (f := fun _ : Lam C => (2 : ℕ)) (fun _ _ => rfl)]
    rw [hcosFcard, Nat.mul_comm]
  -- the fibres of `Ψ` over its image
  have hterm2 : ∀ y ∈ imF,
      (Sol.filter (fun β : Lam C => Ψ β = y)).card = Nat.card ↥(stabLam C ν) := by
    intro y hy
    obtain ⟨β₀, hβ₀, hβ₀y⟩ := Finset.mem_image.mp (by rwa [himF] at hy)
    rw [← hβ₀y]
    rw [show Nat.card ↥(stabLam C ν) =
        (Finset.univ.filter (fun k : Lam C => k ∈ stabLam C ν)).card from
      (finset_filter_card (fun k : Lam C => k ∈ stabLam C ν)).symm]
    rw [Finset.card_bij (fun b _ => β₀⁻¹ * b)]
    · intro b hb
      rw [Finset.mem_filter] at hb
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [mem_stabLam]
      have hb2 : lamCF C b * ν = lamCF C β₀ * ν := by
        rw [hΨ] at hb
        exact hb.2
      have h := congrArg (fun z : ClassFunction ↥C.P.H0 ℂ => lamCF C (β₀⁻¹) * z) hb2
      simp only [← s02c_cf_mul_assoc, ← s02c_lamCF_mul, lam_inv_mul_cancel,
        s02c_lamCF_one_mul] at h
      exact h
    · intro b₁ _ b₂ _ h
      exact lam_mul_left_cancel C h
    · intro k hk
      rw [Finset.mem_filter] at hk
      have hkK : k ∈ stabLam C ν := hk.2
      refine ⟨β₀ * k, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨?_, ?_⟩
        · rw [hSol, Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          have hβ₀c : β₀ * β₀ ∈ cosetK C ν βμ := by
            rw [hSol, Finset.mem_filter] at hβ₀; exact hβ₀.2
          rw [mem_cosetK] at hβ₀c
          obtain ⟨k₁, hk₁, hk₁eq⟩ := hβ₀c
          rw [mem_cosetK]
          exact ⟨k₁ * (k * k),
            ⟨Subgroup.mul_mem _ hk₁ (Subgroup.mul_mem _ hkK hkK),
              by rw [lam_mul_mul_mul_comm C β₀ k β₀ k, hk₁eq, lam_mul_assoc C βμ k₁ (k * k)]⟩⟩
        · rw [hΨ]
          show lamCF C (β₀ * k) * ν = lamCF C β₀ * ν
          rw [s02c_lamCF_mul, s02c_cf_mul_assoc]
          rw [mem_stabLam] at hkK
          rw [hkK]
      · rw [lam_conj' C β₀ k]
  have hsum2 : Sol.card =
      ∑ y ∈ imF, (Sol.filter (fun β : Lam C => Ψ β = y)).card := by
    rw [himF]
    exact Finset.card_eq_sum_card_fiberwise (fun x hx => Finset.mem_image_of_mem Ψ hx)
  have h2 : Sol.card = imF.card * Nat.card ↥(stabLam C ν) := by
    rw [hsum2, Finset.sum_congr rfl hterm2]
    rw [Finset.sum_const_nat
      (f := fun _ : ClassFunction ↥C.P.H0 ℂ => Nat.card ↥(stabLam C ν)) (fun _ _ => rfl)]
  have h3 : (imF : Set (ClassFunction ↥C.P.H0 ℂ)) = {χ ∈ lamOrbit C ν | sconj C χ = χ} := by
    rw [himF]
    ext χ
    rw [Finset.mem_coe, Finset.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨β, hβ, rfl⟩
      rw [hSol, Finset.mem_filter] at hβ
      exact ⟨⟨β, rfl⟩, (sconj_fixed_iff C ν hβμ β).mpr hβ.2⟩
    · rintro ⟨horb, hfix⟩
      obtain ⟨β, hβ⟩ := horb
      refine ⟨β, ?_, hβ.symm⟩
      rw [hSol, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      refine (sconj_fixed_iff C ν hβμ β).mp ?_
      rw [← hβ]
      exact hfix
  have hfin : 2 * Nat.card ↥(stabLam C ν) = imF.card * Nat.card ↥(stabLam C ν) := by
    rw [← h1, h2]
  have himF : imF.card = 2 :=
    (Nat.eq_of_mul_eq_mul_right Nat.card_pos hfin).symm
  rw [← himF, ← h3]
  exact Set.ncard_coe_finset imF

/-! ## 11. The orbit is finite, and the "first half" of Lemma 2.1 -/

/-- The `Λ`-orbit `Λν` is the image of the finite group `Λ`. -/
theorem orbit_finite (C : Sec2Ctx G) (ν : ClassFunction ↥C.P.H0 ℂ) :
    (lamOrbit C ν).Finite := by
  have h : lamOrbit C ν = Set.range (fun β : Lam C => lamCF C β * ν) := by
    ext χ
    constructor
    · rintro ⟨β, hβ⟩; exact ⟨β, hβ.symm⟩
    · rintro ⟨β, hβ⟩; exact ⟨β, hβ.symm⟩
  rw [h]
  exact Set.finite_range _

/-- The "first half" of BG Lemma 2.1: exactly half of the orbit has `t` in the kernel. -/
theorem part1 (C : Sec2Ctx G) (ν : ClassFunction ↥C.P.H0 ℂ)
    (hν : IsIrreducibleCharacter ν) :
    2 * {χ ∈ lamOrbit C ν | χ C.t = χ 1}.ncard = (lamOrbit C ν).ncard := by
  classical
  set A : Set (ClassFunction ↥C.P.H0 ℂ) := {χ ∈ lamOrbit C ν | χ C.t = χ 1} with hA
  set B : Set (ClassFunction ↥C.P.H0 ℂ) := {χ ∈ lamOrbit C ν | χ C.t = -χ 1} with hB
  have hfin : (lamOrbit C ν).Finite := orbit_finite C ν
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro χ ⟨hχ, h1⟩ ⟨-, h2⟩
    have h0 : χ 1 = 0 := by
      have ht : χ C.t = -χ 1 := h2
      rw [h1] at ht
      have h2' : (2 : ℂ) * χ 1 = 0 := by
        rw [two_mul]
        linear_combination ht
      exact (mul_eq_zero.mp h2').resolve_left two_ne_zero
    exact (centralValue C χ (irreducible_of_mem_lamOrbit C hχ hν)).2 h0
  have hunion : A ∪ B = lamOrbit C ν := by
    ext χ
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hχ
      have hirr := irreducible_of_mem_lamOrbit C hχ hν
      rcases (centralValue C χ hirr).1 with h | h
      · exact Or.inl ⟨hχ, h⟩
      · exact Or.inr ⟨hχ, h⟩
  have hsum : (lamOrbit C ν).ncard = A.ncard + B.ncard := by
    rw [← hunion]
    exact Set.ncard_union_eq hdisj (hfin.subset (fun _ h => h.1))
      (hfin.subset (fun _ h => h.1))
  have heq : A.ncard = B.ncard := s02_lemma21_halves C ν hν
  rw [hsum, ← heq, two_mul]

/-! ## 12. BG Lemma 2.1 -/

theorem lemma21 {G : Type} [Group G] [Finite G] (C : Sec2Ctx G) : Lemma21Prop C := by
  intro ν hν
  refine ⟨part1 C ν hν, ?_⟩
  intro hS
  have hsν : sconj C ν ∈ lamOrbit C ν := by
    have hmem : sconj C ν ∈ sconj C '' lamOrbit C ν :=
      ⟨ν, mem_lamOrbit_self C ν, rfl⟩
    rwa [hS] at hmem
  obtain ⟨βμ, hβμ⟩ := hsν
  exact card_fixed C ν hν hβμ

/-- **Bender–Glauberman 1981, Lemma 2.1** (p. 204), in the form stated in `Work.BG.S02`:
for `ν ∈ Irr(H₀)`, exactly half of the characters in the orbit `Λν` have `t` in their
kernel, and if the orbit is `s`-stable then exactly two of its members are fixed by `s`. -/
theorem s02_lemma21 {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] (C : Work.BG.Sec2Ctx G) :
    Work.BG.Lemma21Prop C :=
  lemma21 C

end Work.BG
