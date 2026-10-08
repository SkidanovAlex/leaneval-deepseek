import Mathlib
import Submission.Work.BG.CharBridge

/-!
# The index-two Mackey formula

Let `H₀ ⊴ H` be a normal subgroup of index two and `s ∉ H₀`.  For any class function
`ν : ClassFunction ↥H₀ ℂ` the restriction to `H₀` of the induced class function splits as

  `Res_{H₀}^{H} (Ind_{H₀}^{H} ν) = ν + ν^s`,

where `ν^s = conjBy s ν` is the `H`-conjugate of `ν`.

This is the index-two case of the Mackey restriction formula, in the form needed for
Bender–Glauberman 1981, §1 (the "Mackey" step of the Clifford theory used there).

The proof only uses the general Mackey restriction formula in its unnormalized
"sum over the whole group" form
(`OddOrder.RepresentationTheory.card_smul_restrict_induce`)

  `|H₀| • Res_{H₀}^{H}(Ind_{H₀}^{H} ν) = ∑_{x : H} ν^{x⁻¹}`,

together with the elementary fact that an index-two subgroup has exactly two cosets:
`H = H₀ ⊔ H₀ s⁻¹`.  Every `x ∈ H₀` contributes `ν^{x⁻¹} = ν`, and every `x ∉ H₀`
contributes `ν^{x⁻¹} = ν^s`; the sum therefore equals `|H₀| • (ν + ν^s)`, and the
scalar `|H₀|` cancels because it is invertible in `ℂ`.

## Main results

* `Work.BG.sum_conjBy_indexTwo` — the collapse of the Mackey sum;
* `Work.BG.indexTwoMackey` — the index-two Mackey formula.
-/

namespace Work.BG

open OddOrder.RepresentationTheory

/-- **Collapse of the index-two Mackey sum.**  For `H₀ ⊴ H` of index two, `s ∉ H₀`, and any
class function `ν` on `H₀`:

  `∑_{x : H} ν^{x⁻¹} = |H₀| • (ν + ν^s)`.

Indeed `H` is the disjoint union of the two cosets `H₀` and `H₀ s⁻¹`; conjugation by every
element of the first fixes `ν`, and conjugation by every element of the second acts as
`conjBy s`. -/
lemma sum_conjBy_indexTwo {H : Type*} [Group H] [Fintype H] (H0 : Subgroup H) [H0.Normal]
    (hind : H0.index = 2) (s : H) (hs : s ∉ H0) (ν : ClassFunction ↥H0 ℂ) :
    ∑ x : H, ClassFunction.conjBy (H := H0) x⁻¹ ν
      = (Nat.card ↥H0 : ℂ) • (ν + ClassFunction.conjBy (H := H0) s ν) := by
  classical
  -- There are `|H₀|` elements of `H` inside `H₀` ...
  have hcard1 : (Finset.univ.filter (fun x : H => x ∈ H0)).card = Nat.card ↥H0 := by
    have himg : (Finset.univ.filter (fun x : H => x ∈ H0))
        = (Finset.univ : Finset ↥H0).image (fun t : ↥H0 => (t : H)) := by
      ext x
      simp
    rw [himg, Finset.card_image_of_injective _ Subtype.coe_injective, Finset.card_univ,
        Nat.card_eq_fintype_card]
  -- ... and, since `[H : H₀] = 2`, exactly `|H₀|` elements outside `H₀`.
  have hH : Nat.card H = 2 * Nat.card ↥H0 := by
    rw [← Subgroup.index_mul_card (H := H0), hind]
  have huniv : (Finset.univ : Finset H).card = 2 * Nat.card ↥H0 := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hH]
  have hcard2 : (Finset.univ.filter (fun x : H => x ∉ H0)).card = Nat.card ↥H0 := by
    have hsum := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset H)) (fun x : H => x ∈ H0)
    rw [hcard1, huniv] at hsum
    omega
  -- Pointwise description of the summand: it is `ν` on `H₀` and `ν^s` off `H₀`.
  have hpt : ∀ x : H, ClassFunction.conjBy (H := H0) x⁻¹ ν
      = if x ∈ H0 then ν else ClassFunction.conjBy (H := H0) s ν := by
    intro x
    by_cases hx : x ∈ H0
    · rw [ite_eq_left hx]
      exact ClassFunction.conjBy_eq_self_of_mem (H0.inv_mem hx) ν
    · rw [ite_eq_right hx]
      -- `x ∉ H₀` puts `x` in the coset `H₀ s⁻¹`: `x * s ∈ H₀`, and `x = (x * s) * s⁻¹`.
      have hxs : x * s ∈ H0 := by
        rw [Subgroup.mul_mem_iff_of_index_two hind]
        simp [hx, hs]
      have hxinv : x⁻¹ = s * (x * s)⁻¹ := by group
      rw [hxinv, ClassFunction.conjBy_mul,
        ClassFunction.conjBy_eq_self_of_mem (H0.inv_mem hxs)
          (ClassFunction.conjBy (H := H0) s ν)]
  calc ∑ x : H, ClassFunction.conjBy (H := H0) x⁻¹ ν
      = ∑ x : H, (if x ∈ H0 then ν else ClassFunction.conjBy (H := H0) s ν) :=
        Finset.sum_congr rfl (fun x _ => hpt x)
    _ = ∑ x ∈ (Finset.univ : Finset H) with (x ∈ H0), ν
          + ∑ x ∈ (Finset.univ : Finset H) with ¬(x ∈ H0), ClassFunction.conjBy (H := H0) s ν :=
        Finset.sum_ite _ _
    _ = (Nat.card ↥H0 : ℂ) • ν + (Nat.card ↥H0 : ℂ) • ClassFunction.conjBy (H := H0) s ν := by
        simp only [Finset.sum_const, hcard1, hcard2, Nat.cast_smul_eq_nsmul]
    _ = (Nat.card ↥H0 : ℂ) • (ν + ClassFunction.conjBy (H := H0) s ν) := (smul_add _ _ _).symm

theorem indexTwoMackey {H : Type*} [Group H] [Finite H] [Fintype H] (H0 : Subgroup H)
    [H0.Normal] (hind : H0.index = 2) (s : H) (hs : s ∉ H0)
    [Invertible (Nat.card H0 : ℂ)]
    (ν : OddOrder.RepresentationTheory.ClassFunction ↥H0 ℂ) :
    OddOrder.RepresentationTheory.ClassFunction.restrict H0
        (OddOrder.RepresentationTheory.ClassFunction.induce H0 ν) =
      ν + OddOrder.RepresentationTheory.ClassFunction.conjBy s ν := by
  -- Mackey restriction, in the unnormalized form `|H₀| • Res(Ind ν) = ∑_x ν^{x⁻¹}`.
  have hmackey := card_smul_restrict_induce (G := H) (H := H0) (k := ℂ) ν
  have hsum := sum_conjBy_indexTwo (H := H) H0 hind s hs ν
  have hmain : (Nat.card ↥H0 : ℂ) • ClassFunction.restrict H0 (ClassFunction.induce H0 ν)
      = (Nat.card ↥H0 : ℂ) • (ν + ClassFunction.conjBy (H := H0) s ν) := by
    rw [hmackey, hsum]
  -- Cancel the invertible scalar `|H₀|`.
  have hcancel := congrArg (fun z => ⅟(Nat.card ↥H0 : ℂ) • z) hmain
  simpa [smul_smul, invOf_mul_self] using hcancel

end Work.BG
