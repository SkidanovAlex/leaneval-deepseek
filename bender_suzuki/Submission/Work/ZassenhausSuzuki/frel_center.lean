import Mathlib
import Submission.Work.ZassenhausSuzuki.frel_center_aux
import Submission.Work.ZassenhausSuzuki.TitsAux
import Submission.Work.ZassenhausSuzuki.SzASymmIso
import Submission.Work.ZassenhausSuzuki.TitsTerminal
import Submission.Work.ZassenhausSuzuki.structPair_value_two_aux
import Submission.Work.ZassenhausSuzuki.tits_of_normalised_general
import Submission.Work.ZassenhausSuzuki.odd_orderOf_of_isTitsTheta

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `frel_center`: the book's map `f` on the central involutions of `Q`

BG 5.20 (a) / HB XI 11.12.  In a split rank-one Zassenhaus configuration `H = Q ⋊ D`, `t`
with `Q ≃* A(K,θ)` (`θ` a Tits endomorphism, `D` acting through the standard torus `Λ`),
the map `f` defined by the relation `FRel H t x y` (`t x t = m · t · y`, `m ∈ H`)
sends the central involutions `⟨0,b⟩` (`b ≠ 0`) of `A(K,θ)` to

  `f ⟨0,b⟩ = ⟨ν · b / θ b, 0⟩`

for a **single** `ν ∈ Kˣ`.

The reduction to the value of `f` at the *structure element* `ρ`
(`t s t = ρ t ρ⁻¹`, `s = ρ²`; `frel_center_of_structure`, `structure_value_of_normalized`)
lives in `Submission/Work/ZassenhausSuzuki/frel_center_aux.lean`.

The remaining step is the present `normalized_structure_value`: in coordinates in which the
structure involution is `⟨0,1⟩`, the structure element is `⟨1,1⟩`.  The proof is the
`θ ↔ θ⁻¹` argument of HB XI 11.12–11.14:

* in normalised coordinates `e ρ = ⟨1,q⟩` (`Work.ZassenhausSuzuki.structPair_value_two_aux`,
  HB XI 11.11–11.12) for some `q`, and `ρ² = s` follows;
* the case `q = 1` is the claim; the case `q = 0` is transferred, through the explicit
  isomorphism `szASymm θ : A(K,θ) ≃* A(K,θ⁻¹)`, to coordinates *with field parameter
  `θ⁻¹`* in which the structure element is `⟨1,1⟩`; the terminal computation
  (`tits_of_normalised_general`, Suzuki 1962 §5 / HB XI 11.13–11.14) then makes `θ⁻¹` a Tits
  endomorphism, which contradicts the hypothesis `IsTitsTheta θ`
  (`not_isTitsTheta_symm`).

Everything is stated over an arbitrary field `K` of characteristic two (the finiteness needed
by the terminal computation is derived from `Q ≃* A(K,θ)`).
-/

namespace Work.ZassenhausSuzuki

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-- A field of characteristic two admits no Tits endomorphism `θ` for which also `θ⁻¹` is
Tits: `IsTitsTheta θ` gives `θ(θ x) = x²`, `IsTitsTheta θ.symm` gives `x = θ⁻¹(θ⁻¹ x)`, and
applying `θ²` to the latter yields `x = x⁴`; so every non-zero `x` satisfies `x³ = 1`, `Kˣ` is
contained in the root set of `X² + X + 1`, and `|K| ≤ 4`.  For `|K| ≤ 4` no such `θ` exists:
`|K| = 2` forces `θ = 1`, and `|K| = 4` forces `θ ∈ {1, Frob}` while `θ² = Frob ≠ 1 = Frob²`. -/
theorem not_isTitsTheta_symm {K : Type} [Field K] [CharP K 2] {θ : K ≃+* K}
    (hθ : IsTitsTheta θ) : ¬ IsTitsTheta θ.symm := by
  have h2K : (2 : K) = 0 := CharP.cast_eq_zero K 2
  intro hθ'
  have h4 : ∀ x : K, x ^ 4 = x := by
    intro x
    have h1 : θ.symm (θ.symm x) = x ^ 2 := hθ'.2 x
    have h2 : θ (θ (θ.symm (θ.symm x))) = θ (θ (x ^ 2)) :=
      congrArg (fun y : K => θ (θ y)) h1
    have h3 : θ (θ (θ.symm (θ.symm x))) = x := by
      simp only [RingEquiv.apply_symm_apply]
    rw [h3] at h2
    have h5 : θ (θ (x ^ 2)) = x ^ 4 := by
      rw [map_pow θ x 2, map_pow θ (θ x) 2, hθ.2 x]
      ring_nf
    rw [h5] at h2
    exact h2.symm
  obtain ⟨y, hy⟩ : ∃ y : K, θ y ≠ y := by
    by_contra h
    push Not at h
    exact hθ.1 (RingEquiv.ext h)
  have hy0 : y ≠ 0 := by rintro rfl; exact hy (map_zero θ)
  have hy1 : y ≠ 1 := by rintro rfl; exact hy (map_one θ)
  have hy3 : y ^ 3 = 1 := by
    have h := h4 y
    rw [show (4:ℕ) = 3 + 1 from rfl, pow_succ] at h
    exact mul_right_cancel₀ hy0 (by rw [h, one_mul])
  have hyroot : y * y + y + 1 = 0 := by
    have h1 : (y + 1) * (y * y + y + 1) = 0 := by
      have he : (y + 1) * (y * y + y + 1) = y ^ 3 + 1 := by
        ring_nf; simp only [h2K, mul_zero, add_zero, zero_add]
      rw [he, hy3]; exact CharTwo.add_self_eq_zero 1
    rcases mul_eq_zero.mp h1 with h | h
    · rw [add_eq_zero_iff_eq_neg] at h
      exact absurd (by rwa [CharTwo.neg_eq] at h : y = 1) hy1
    · exact h
  have htheta_ne_one : θ y ≠ 1 := by
    intro hc
    have h : y * y = 1 := by
      have h0 : θ (θ y) = 1 := by rw [hc, map_one]
      rw [hθ.2 y] at h0
      rw [← pow_two]; exact h0
    have h1 : (y + 1) * (y + 1) = 0 := by
      have he : (y + 1) * (y + 1) = y * y + 1 := by
        ring_nf; simp only [h2K, mul_zero, add_zero, zero_add]
      rw [he, h]; exact CharTwo.add_self_eq_zero 1
    have h2 : y + 1 = 0 := mul_self_eq_zero.mp h1
    rw [add_eq_zero_iff_eq_neg] at h2
    exact hy1 (by rwa [CharTwo.neg_eq] at h2)
  have hθy3 : (θ y) ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
  have hroot : (θ y) * (θ y) + θ y + 1 = 0 := by
    have h1 : (θ y + 1) * ((θ y) * (θ y) + θ y + 1) = 0 := by
      have he : (θ y + 1) * ((θ y) * (θ y) + θ y + 1) = (θ y) ^ 3 + 1 := by
        ring_nf; simp only [h2K, mul_zero, add_zero, zero_add]
      rw [he, hθy3]; exact CharTwo.add_self_eq_zero 1
    rcases mul_eq_zero.mp h1 with h | h
    · rw [add_eq_zero_iff_eq_neg] at h
      exact absurd (by rwa [CharTwo.neg_eq] at h : θ y = 1) htheta_ne_one
    · exact h
  have hfac : (θ y + y) * (θ y + y + 1) = 0 := by
    have he : (θ y + y) * (θ y + y + 1)
        = ((θ y) * (θ y) + θ y + 1) + (y * y + y + 1) := by
      ring_nf; simp only [h2K, mul_zero, add_zero, zero_add]
    rw [he, hroot, hyroot, add_zero]
  rcases mul_eq_zero.mp hfac with h | h
  · rw [add_eq_zero_iff_eq_neg] at h
    exact hy (by rwa [CharTwo.neg_eq] at h)
  · have hsq : y ^ 2 = y := by
      have h1 : θ (θ y) = y := by
        have hyy : θ y = y + 1 := by
          have h3 : θ y = 1 - y := eq_sub_iff_add_eq.mpr (by
            have h2 := add_eq_zero_iff_eq_neg.mp h
            rwa [CharTwo.neg_eq] at h2)
          rw [h3, sub_eq_add_neg, CharTwo.neg_eq, add_comm]
        calc θ (θ y) = θ (y + 1) := by rw [hyy]
          _ = θ y + 1 := by rw [map_add, map_one]
          _ = (y + 1) + 1 := by rw [hyy]
          _ = y := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      rw [hθ.2 y] at h1
      exact h1
    rcases eq_zero_or_eq_one_of_sq_eq_self hsq with h0 | h1
    · exact hy0 h0
    · exact hy1 h1

/-- The admissible coordinate change of HB XI 11.12: composing with the explicit isomorphism
`szASymm θ : A(K,θ) ≃* A(K,θ⁻¹)` (`(a,b) ↦ (θ a, b + a·θa)`) turns the field parameter `θ`
into `θ⁻¹` and preserves the hypothesis `TorusCoords` (the tori correspond under
`szASymm_hLam`). -/
theorem torusCoords_szASymm {K : Type} [Field K] [CharP K 2] {θ : K ≃+* K}
    {e : Q ≃* SzA K θ} (h : TorusCoords K θ H Q t e) :
    TorusCoords K θ.symm H Q t (e.trans (szASymm θ)) := by
  intro d hd
  obtain ⟨lam, hlam⟩ := h d hd
  refine ⟨Units.map θ.toMonoidHom lam, fun x => ?_⟩
  obtain ⟨y, hy, hye⟩ := hlam x
  refine ⟨y, hy, ?_⟩
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, hye, szASymm_hLam]
  simp

/-- **HB XI 11.13–11.14 in normalised form.**

In coordinates in which the structure involution is `⟨0,1⟩`, the structure element `ρ` (whose
square is `s`) is `⟨1,1⟩`.  The proof uses HB XI 11.11–11.12
(`Work.ZassenhausSuzuki.structPair_value_two_aux`: `e ρ = ⟨1,q⟩` with `q ∈ {0,1}`); the case
`q = 1` is the claim, and the case `q = 0` is transported by `szASymm θ` to coordinates in
which the field parameter is `θ⁻¹` and the structure element is `⟨1,1⟩`, where the terminal
computation (`Work.ZassenhausSuzuki.tits_of_normalised_general`) forces `θ⁻¹` to be Tits —
contradicting the hypothesis `IsTitsTheta θ`. -/
theorem normalized_structure_value {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : IsSplitRankOne H Q t) (hzass : IsZassenhaus H)
    {K : Type} [Field K] [CharP K 2] {θ : K ≃+* K} (hθ : IsTitsTheta θ)
    (e : Q ≃* SzA K θ) (htorus : TorusCoords K θ H Q t e)
    (hs : e (⟨(structPair hsplit).1, (structPair_spec hsplit).1⟩ : Q)
      = (⟨0, 1⟩ : SzA K θ)) :
    e (⟨(structPair hsplit).2, (structPair_spec hsplit).2.2.1⟩ : Q) = (⟨1, 1⟩ : SzA K θ) := by
  classical
  obtain ⟨hsQ, hs2, hρQ, hstruct⟩ := structPair_spec hsplit
  haveI hQfin : Finite Q := Subtype.finite
  haveI hSzAfin : Finite (SzA K θ) := Finite.of_equiv Q e.toEquiv
  haveI hKfin : Finite K := Finite.of_injective (fun k : K => (⟨k, 0⟩ : SzA K θ))
    (fun a b h => by simpa using congrArg SzA.a h)
  have h2 : IsPGroup 2 Q := isPGroup_two_of_mulEquiv θ e
  set sQ : Q := ⟨(structPair hsplit).1, hsQ⟩ with hsQdef
  set ρQ : Q := ⟨(structPair hsplit).2, hρQ⟩ with hρQdef
  have hsv : e sQ = (⟨0, 1⟩ : SzA K θ) := by rw [hsQdef]; exact hs
  obtain ⟨q, hq, hρval0⟩ := structPair_value_two_aux hsplit hzass hθ e htorus hs
  have hρval : e ρQ = (⟨1, q⟩ : SzA K θ) := by rw [hρQdef]; exact hρval0
  -- `ρ² = s`: both sides square to the central involution `⟨0,1⟩`
  have hsq : e (ρQ * ρQ) = (⟨0, 1⟩ : SzA K θ) := by
    rw [map_mul, hρval]
    ext <;> simp [SzA.mul_a, SzA.mul_b, CharTwo.add_self_eq_zero]
  have hρsqQ : ρQ * ρQ = sQ := by
    apply e.injective
    rw [hsq, hsv]
  have hstruct' : t * (((ρQ ^ 2 : Q)) : G) * t = (ρQ : G) * t * (((ρQ⁻¹ : Q)) : G) := by
    have hp : (ρQ ^ 2 : Q) = sQ := by rw [pow_two]; exact hρsqQ
    have hx2 : (((ρQ ^ 2 : Q)) : G) = (structPair hsplit).1 := by rw [hp, hsQdef]
    have hx1 : (ρQ : G) = (structPair hsplit).2 := by rw [hρQdef]
    have hx0 : (((ρQ⁻¹ : Q)) : G) = ((structPair hsplit).2)⁻¹ := by
      simp only [hρQdef, Subgroup.coe_inv]
    rw [hx2, hx1, hx0, ← hstruct, inv_eq_of_mul_eq_one_right (ht_mul_self hsplit)]
  rcases hq with hq0 | hq1
  · -- the case `q = 0` contradicts the Tits property of `θ`, through the `θ ↦ θ⁻¹` twist
    exfalso
    have hsymm : ∀ (φ : K ≃+* K), φ.symm = φ⁻¹ := fun φ => by ext x; simp
    have hθsymm_ne : θ.symm ≠ 1 := by
      intro h
      refine hθ.1 ?_
      calc θ = (θ.symm).symm := (RingEquiv.symm_symm θ).symm
        _ = (1 : K ≃+* K).symm := by rw [h]
        _ = 1 := by rw [hsymm 1, inv_one]
    have hθsymm_odd : Odd (orderOf θ.symm) := by
      rw [hsymm θ, orderOf_inv]
      exact odd_orderOf_of_isTitsTheta hθ
    have htorus' : TorusCoords K θ.symm H Q t (e.trans (szASymm θ)) :=
      torusCoords_szASymm htorus
    have hg' : (e.trans (szASymm θ)) ρQ = (⟨1, 1⟩ : SzA K θ.symm) := by
      rw [MulEquiv.trans_apply, hρval, hq0, szASymm_one_zero]
    exact not_isTitsTheta_symm hθ
      (tits_of_normalised_general hθsymm_ne hθsymm_odd hsplit hzass h2 htorus'
        (g := ρQ) hg' hstruct')
  · rw [hρval, hq1]

/-- **BG 5.20 (a) / HB XI 11.12.**  The structure-identity element `ρ` of the configuration
(`t s t = ρ t ρ⁻¹`) has coordinates in the `Λ`-orbit of `⟨1,1⟩ = ⟨1,0⟩⁻¹`. -/
theorem structure_value (hsplit : IsSplitRankOne H Q t) (hzass : IsZassenhaus H)
    {K : Type} [Field K] [CharP K 2] {θ : K ≃+* K} (hθ : IsTitsTheta θ)
    (e : Q ≃* SzA K θ) (htorus : TorusCoords K θ H Q t e) :
    ∃ μ : Kˣ, e (⟨(structPair hsplit).2, (structPair_spec hsplit).2.2.1⟩ : Q)
      = SzA.hLam θ (μ : K) (⟨1, 1⟩ : SzA K θ) :=
  structure_value_of_normalized hsplit hzass hθ e htorus
    (fun e' htorus' hs' => normalized_structure_value hsplit hzass hθ e' htorus' hs')

theorem frel_center {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H)
    {K : Type} [Field K] [CharP K 2] {θ : K ≃+* K} (hθ : Work.ZassenhausSuzuki.IsTitsTheta θ)
    (e : Q ≃* Work.ZassenhausSuzuki.SzA K θ)
    (htorus : Work.ZassenhausSuzuki.TorusCoords K θ H Q t e) :
    ∃ ν : Kˣ, ∀ b : K, b ≠ 0 →
      Work.RankOneUniqueness.FRel H t
        (((e.symm (⟨0, b⟩ : Work.ZassenhausSuzuki.SzA K θ)) : Q) : G)
        (((e.symm (⟨(ν : K) * b / θ b, 0⟩ : Work.ZassenhausSuzuki.SzA K θ)) : Q) : G) :=
  frel_center_of_structure hsplit hzass hθ e htorus (structure_value hsplit hzass hθ e htorus)

end Work.ZassenhausSuzuki
