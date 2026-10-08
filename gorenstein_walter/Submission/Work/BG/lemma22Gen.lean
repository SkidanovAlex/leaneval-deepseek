import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.H0Conj
import Submission.Work.BG.Lemma13
import Submission.Work.BG.CharBridge
import Submission.Work.BG.s02_lemma22Sq
import Submission.Work.BG.s02_involutionPair
import Submission.Work.BG.classMult
import Submission.Work.BG.conjClassCard

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

variable {G : Type} [Group G] [Finite G]

/-! ## Small structural helpers -/

/-- The involutions of `H ∖ H₀` in either presentation (`invJ` lists the same elements as
`XH`, only the order of the predicates in the filter differs). -/
theorem invJ_eq_XH (C : Sec2Ctx G) [Fintype ↥C.P.H] : invJ C = XH C := by
  classical
  ext x
  simp only [invJ, XH, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h2, -, h0⟩; exact ⟨h0, h2⟩
  · rintro ⟨h0, h2⟩; exact ⟨h2, fun h => h0 (h ▸ C.P.H0.one_mem), h0⟩

/-- `H = C_G(t)`: this is not part of `Sec2Ctx` (`t_comm_H` gives only `H ≤ C_G(t)`), but
follows from the TI condition applied to `t ∈ T`. -/
theorem centralizer_t_eq_H (C : Sec2Ctx G) :
    Subgroup.centralizer ({(C.t : G)} : Set G) = C.P.H := by
  refine le_antisymm ?_ ?_
  · intro g hg
    have ht : (C.t : G) ∈ Tset C.P.H0 C.P.U := ⟨C.t.2, C.t_not_mem_U⟩
    have hg1 : g * (C.t : G) = (C.t : G) * g := Subgroup.mem_centralizer_singleton_iff.mp hg
    refine C.P.mem_H_of_conj_mem ht ?_
    rw [show g * (C.t : G) * g⁻¹ = (C.t : G) from by
      rw [hg1, mul_assoc, mul_inv_cancel, mul_one]]
    exact ht
  · intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact C.t_comm_H g hg

/-- The `G`-class of `t` has one element per coset of `H = C_G(t)`. -/
theorem tClass_card (C : Sec2Ctx G) [Fintype G] : (tClass C).card = C.P.H.index := by
  classical
  have h1 : (tClass C).card = Nat.card {y : G // IsConj y (C.t : G)} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rfl
  rw [h1, conjClassCard, centralizer_t_eq_H]

/-- `indH` and `dcf` are the same induction `H₀ → H`. -/
theorem indH_eq_dcf (C : Sec2Ctx G) [Fintype G] [Fintype ↥C.P.H]
    [Invertible (Nat.card ↥(H0in C.P) : ℂ)] (μ : ClassFunction ↥C.P.H0 ℂ) :
    indH C μ = dcf C μ := rfl

/-- `indH` is additive: `indH C μ - indH C ν = dcf C (μ - ν)`. -/
theorem indH_sub_eq_dcf (C : Sec2Ctx G) [Fintype G] [Fintype ↥C.P.H]
    [Invertible (Nat.card ↥(H0in C.P) : ℂ)] (μ ν : ClassFunction ↥C.P.H0 ℂ) :
    indH C μ - indH C ν = dcf C (μ - ν) := by
  rw [indH_eq_dcf C μ, indH_eq_dcf C ν, ← l22c1_dcf_sub C μ ν]

/-! ## The pure character-theoretic expansion behind the right-hand side -/

/-- **Expansion of the right-hand side.**  For a conjugation-invariant `Finset` `X` of a
finite group `K` and any class function `δ` of `K`,

`∑_{θ ∈ Irr K} (∑_{x ∈ X} θ(x))² / θ(1) · (δ, θ) = ∑_{x,y ∈ X} δ(xy)`.

Indeed `(∑_{x ∈ X} θ(x))² = θ(1) · ∑_{x,y ∈ X} θ(xy)` (BG Lemma 2.2-a,
`Work.BG.s02_classSumSquare`) and `δ = ∑_θ (δ, θ) θ` (Fourier). -/
theorem classSum_expansion {K : Type} [Group K] [Fintype K] [Invertible (Nat.card K : ℂ)]
    [Fintype (IrreducibleCharacter K)] (X : Finset K)
    (hX : ∀ g x : K, x ∈ X → g * x * g⁻¹ ∈ X) (δ : ClassFunction K ℂ) :
    ∑ θ : IrreducibleCharacter K,
        (∑ x ∈ X, (θ : ClassFunction K ℂ) x) ^ 2 / ((θ : ClassFunction K ℂ) 1) *
          ClassFunction.inner δ (θ : ClassFunction K ℂ)
      = ∑ x ∈ X, ∑ y ∈ X, δ (x * y) := by
  have key : ∀ θ : IrreducibleCharacter K,
      (∑ x ∈ X, (θ : ClassFunction K ℂ) x) ^ 2 / ((θ : ClassFunction K ℂ) 1)
        = ∑ x ∈ X, ∑ y ∈ X, (θ : ClassFunction K ℂ) (x * y) := by
    intro θ
    have hsq := s02_classSumSquare X hX (θ : ClassFunction K ℂ) (Or.inl θ.2)
    have h1 : ((θ : ClassFunction K ℂ) 1) ≠ 0 := pmIrr_apply_one_ne_zero (Or.inl θ.2)
    rw [div_eq_iff h1, mul_comm]
    rw [hsq]
  have hδ : δ = ∑ θ : IrreducibleCharacter K,
      ClassFunction.inner δ (θ : ClassFunction K ℂ) • (θ : ClassFunction K ℂ) :=
    (OddOrder.RepresentationTheory.sum_inner_irreducibleCharacter_smul δ).symm
  have hR : (∑ x ∈ X, ∑ y ∈ X, δ (x * y)) =
      ∑ θ : IrreducibleCharacter K, ClassFunction.inner δ (θ : ClassFunction K ℂ) *
        (∑ x ∈ X, ∑ y ∈ X, (θ : ClassFunction K ℂ) (x * y)) := by
    have h := congrArg (cfMulSum X) hδ
    rw [map_sum] at h
    simp only [map_smul, smul_eq_mul] at h
    exact h
  rw [hR]
  refine Finset.sum_congr rfl (fun θ _ => ?_)
  rw [key θ]; ring

/-! ## The two halves of the identity -/

/-- **Step B**: the pair sums over the class `t^G` and over the involutions of `H ∖ H₀` differ
by the index `|G : H|`.  This is the Frobenius-reciprocity + pair-count argument of
Bender–Glauberman 1981, p. 205. -/
theorem lemma22Gen_stepB (C : Sec2Ctx G) [Fintype G] [Invertible (Nat.card G : ℂ)]
    [Invertible (Nat.card ↥C.P.H0 : ℂ)] [Fintype ↥C.P.H]
    [Invertible (Nat.card ↥C.P.H : ℂ)]
    [Invertible (Nat.card ↥(H0in C.P) : ℂ)] :
    ∀ {μ ν : ClassFunction ↥C.P.H0 ℂ}, LamEquiv C μ ν →
    ∑ x ∈ tClass C, ∑ y ∈ tClass C, ind C (μ - ν) (x * y)
      = (C.P.H.index : ℂ) * ∑ x ∈ invJ C, ∑ y ∈ invJ C, dcf C (μ - ν) (x * y) := by
  classical
  intro μ ν hlam
  -- The pair-count class function on `G`: `f(g) = #{(x,y) ∈ t^G × t^G : xy = g}`.
  have hFconj : ∀ g h : G,
      ((pairSet (tClass C) (h * g * h⁻¹)).card : ℂ) = ((pairSet (tClass C) g).card : ℂ) := by
    intro g h
    have h := s02_pairCount_conj (X := tClass C) (l22c1_tClass_conj C) g h
    exact_mod_cast h
  let F : ClassFunction G ℂ :=
    ⟨fun g => ((pairSet (tClass C) g).card : ℂ), hFconj⟩
  have hFapply : ∀ g : G, F g = ((pairSet (tClass C) g).card : ℂ) := fun g => rfl
  have hFstar : ∀ g : G, star (F g) = F g := by
    intro g; rw [hFapply g]; exact star_natCast _
  -- Step 1: rewrite the double sum as a single sum against the pair count.
  have hS1 : (∑ x ∈ tClass C, ∑ y ∈ tClass C, ind C (μ - ν) (x * y)) =
      ∑ g : G, F g * ind C (μ - ν) g := by
    have h := s02_pairCount_sum (X := tClass C) (ψ := ind C (μ - ν))
    rw [h]
  -- Step 2: `Σ_g F g * χ g = |G| * ⟨χ, F⟩` (`F` is real-valued, so `star` disappears).
  have hS2 : (∑ g : G, F g * ind C (μ - ν) g) =
      (Nat.card G : ℂ) * ClassFunction.inner (ind C (μ - ν)) F := by
    have h1 : ClassFunction.innerSum (ind C (μ - ν)) F =
        ∑ g : G, F g * ind C (μ - ν) g := by
      rw [ClassFunction.innerSum]
      exact Finset.sum_congr rfl (fun g _ => by rw [hFstar g, mul_comm])
    rw [ClassFunction.card_mul_inner, h1]
  -- Step 3: Frobenius reciprocity (induction in stages `H₀ → H → G`).
  have hrec : ClassFunction.inner (ind C (μ - ν)) F =
      ClassFunction.inner (dcf C (μ - ν)) (ClassFunction.restrict C.P.H F) := by
    rw [ind_eq_induce_dcf C (μ - ν)]
    exact ClassFunction.inner_induce_eq_inner_restrict C.P.H (dcf C (μ - ν)) F
  -- Step 4: expand the `H`-inner product.
  have hinner : ClassFunction.inner (dcf C (μ - ν)) (ClassFunction.restrict C.P.H F) =
      ⅟(Nat.card ↥C.P.H : ℂ) *
        ∑ h : ↥C.P.H, dcf C (μ - ν) h * F (h : G) := by
    rw [ClassFunction.inner_eq_inv_card_mul_innerSum, ClassFunction.innerSum]
    refine congrArg (fun z => ⅟(Nat.card ↥C.P.H : ℂ) * z) ?_
    exact Finset.sum_congr rfl (fun h _ => by
      rw [ClassFunction.restrict_apply, hFstar (h : G)])
  -- Step 5: on `T` the pair count may be computed inside `H` (TI argument), and `dcf` is
  -- supported on `T`, so the `H`-sum is the double sum over the involutions of `H ∖ H₀`.
  have hkey : (∑ h : ↥C.P.H, dcf C (μ - ν) h * F (h : G)) =
      ∑ x ∈ XH C, ∑ y ∈ XH C, dcf C (μ - ν) (x * y) := by
    have hpoint : ∀ h : ↥C.P.H, dcf C (μ - ν) h * F (h : G) =
        dcf C (μ - ν) h * ((pairSet (XH C) h).card : ℂ) := by
      intro h
      by_cases hh : (h : G) ∈ Tset C.P.H0 C.P.U
      · rw [hFapply (h : G), s02_pairCount_T_card C h hh]
      · rw [dcf_eq_zero_of_not_mem_T C hlam h hh, zero_mul, zero_mul]
    calc (∑ h : ↥C.P.H, dcf C (μ - ν) h * F (h : G))
        = ∑ h : ↥C.P.H, dcf C (μ - ν) h * ((pairSet (XH C) h).card : ℂ) :=
          Finset.sum_congr rfl (fun h _ => hpoint h)
      _ = ∑ h : ↥C.P.H, ((pairSet (XH C) h).card : ℂ) * dcf C (μ - ν) h :=
          Finset.sum_congr rfl (fun h _ => mul_comm _ _)
      _ = ∑ x ∈ XH C, ∑ y ∈ XH C, dcf C (μ - ν) (x * y) :=
          (s02_pairCount_sum (X := XH C) (ψ := dcf C (μ - ν))).symm
  -- Combine, and replace `XH` by `invJ`.
  have hGH : (Nat.card G : ℂ) * ⅟(Nat.card ↥C.P.H : ℂ) = (C.P.H.index : ℂ) := by
    have hh := Subgroup.index_mul_card C.P.H
    have hcard : ((C.P.H.index : ℕ) : ℂ) * (Nat.card ↥C.P.H : ℂ) = (Nat.card G : ℂ) := by
      rw [← hh]; push_cast; ring
    have hH0 : (Nat.card ↥C.P.H : ℂ) ≠ 0 := by
      rw [Nat.cast_ne_zero]
      exact (Nat.card_pos (α := ↥C.P.H)).ne'
    rw [← hcard, mul_assoc, mul_invOf_self, mul_one]
  rw [hS1, hS2, hrec, hinner, hkey, invJ_eq_XH C, ← hGH]
  rw [mul_assoc]

/-- **Step A**: the left-hand side `|G:H| ∑_χ χ(t)²/χ(1)(χ, (μ-ν)^G)` rewritten as
`|G:H|⁻¹` times the double sum over the class of `t` (Gorenstein 4.2.12, `ClassMultProp`). -/
theorem lemma22Gen_stepA (C : Sec2Ctx G) [Fintype G] [Invertible (Nat.card G : ℂ)]
    [Invertible (Nat.card ↥C.P.H0 : ℂ)] [Fintype ↥C.P.H]
    [Invertible (Nat.card ↥C.P.H : ℂ)]
    [Invertible (Nat.card ↥(H0in C.P) : ℂ)]
    [Fintype (IrreducibleCharacter G)] :
    ∀ {μ ν : ClassFunction ↥C.P.H0 ℂ},
    (C.P.H.index : ℂ) * ∑ χ : IrreducibleCharacter G,
        (χ : ClassFunction G ℂ) (C.t : G) ^ 2 / (χ : ClassFunction G ℂ) 1 *
          ClassFunction.inner (ind C (μ - ν)) (χ : ClassFunction G ℂ)
      = ((C.P.H.index : ℂ))⁻¹ *
          ∑ x ∈ tClass C, ∑ y ∈ tClass C, ind C (μ - ν) (x * y) := by
  intro μ ν
  classical
  have hA : (C.P.H.index : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Subgroup.index_ne_zero_of_finite
  have hX : ∀ x : G, x ∈ tClass C ↔ IsConj x (C.t : G) := fun x => by simp [tClass]
  have hcm := classMult (tClass C) (C.t : G) hX (ind C (μ - ν))
  have hcm' : (∑ x ∈ tClass C, ∑ y ∈ tClass C, ind C (μ - ν) (x * y))
      = (C.P.H.index : ℂ) ^ 2 * ∑ χ : IrreducibleCharacter G,
          (χ : ClassFunction G ℂ) (C.t : G) ^ 2 / (χ : ClassFunction G ℂ) 1 *
            ClassFunction.inner (ind C (μ - ν)) (χ : ClassFunction G ℂ) := by
    rw [hcm, tClass_card C]
    congr 1
    refine Finset.sum_congr rfl (fun χ _ => ?_)
    ring
  rw [hcm']
  field_simp

/-! ## The main theorem -/

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem lemma22Gen {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] [Fintype ↥C.P.H]
    [Invertible (Nat.card ↥C.P.H : ℂ)] [Invertible (Nat.card ↥(Work.BG.H0in C.P) : ℂ)]
    [Fintype (OddOrder.RepresentationTheory.IrreducibleCharacter G)]
    [Fintype (OddOrder.RepresentationTheory.IrreducibleCharacter ↥C.P.H)] :
    Work.GW2.C16.Lemma22GenProp C := by
  intro μ ν hμ hν hlam
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  haveI : Fintype ↥(H0in C.P) := Fintype.ofFinite _
  -- The right-hand side is the double sum over `J`, expanded in `Irr(H)`.
  have hXinv : ∀ g x : ↥C.P.H, x ∈ invJ C → g * x * g⁻¹ ∈ invJ C := by
    intro g x hx
    rw [invJ_eq_XH C] at hx ⊢
    exact l22c1_XH_conj C g x hx
  have hR := classSum_expansion (K := ↥C.P.H) (invJ C) hXinv (dcf C (μ - ν))
  have hA := lemma22Gen_stepA (C := C) (μ := μ) (ν := ν)
  have hB := lemma22Gen_stepB (C := C) (μ := μ) (ν := ν) hlam
  have hδeq : indH C μ - indH C ν = dcf C (μ - ν) := indH_sub_eq_dcf C μ ν
  have hA0 : (C.P.H.index : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Subgroup.index_ne_zero_of_finite
  rw [hδeq, hR, hA, hB, ← mul_assoc, inv_mul_cancel₀ hA0, one_mul]

end Work.BG
