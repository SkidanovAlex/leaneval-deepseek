import Mathlib
import Submission.Work.LinnikAreas.SiegelBase
import Submission.Work.LinnikAreas.boxMaxZero
import Submission.Work.LinnikAreas.finset_sum_snd_le_finsum
import Submission.Work.LinnikAreas.support_pairCountHeight_finite

namespace Work.LinnikAreas

open scoped Classical BigOperators

/-- **Domination of `pairCountHeight`.**  A finite set `S` of pairs `(χ, ρ)` whose members all
satisfy the four defining conditions of `Siegel.pairCountHeight` (nonzero multiplicity,
`λ(ρ) ≤ t`, `|Im ρ|·log q ≤ T`, and none of them the exceptional pair `(χ₁, β₁)`) contributes at
most its full multiplicity-weighted counting function: the terms of the counting function being
nonnegative, and each pair of `S` occurring at most once in the finset, the sum over `S` is a
sub-sum of the finsum over all pairs.

Each character's fibre of `S` is a finset of pairs with a *fixed* first coordinate, so its second
coordinate is injective, and the multiplicity sum over such a fibre is at most the (finitely
supported, by `support_pairCountHeight_finite`) `∑ᶠ` over all `ρ`. -/
theorem pairCountHeight_dom {q : ℕ} [NeZero q] (hq : 1 < q) (χ₁ : DirichletCharacter ℂ q)
    (β₁ : ℂ) {t T : ℝ}
    (S : Finset (DirichletCharacter ℂ q × ℂ))
    (hzm : ∀ z ∈ S, Work.LinnikContract.zeroMult z.1 z.2 ≠ 0)
    (hlam : ∀ z ∈ S, Work.LinnikContract.lamOf q z.2 ≤ t)
    (him : ∀ z ∈ S, |z.2.im| * Real.log q ≤ T)
    (hexc : ∀ z ∈ S, ¬(z.1 = χ₁ ∧ z.2 = β₁)) :
    (∑ z ∈ S, (Work.LinnikContract.zeroMult z.1 z.2 : ℝ))
      ≤ Work.LinnikAreas.Siegel.pairCountHeight χ₁ β₁ t T := by
  classical
  -- the summand of `pairCountHeight`, as a function of the character and of the zero
  let Pc : DirichletCharacter ℂ q → ℂ → Prop := fun χ ρ =>
    Work.LinnikContract.zeroMult χ ρ ≠ 0 ∧ Work.LinnikContract.lamOf q ρ ≤ t
      ∧ |ρ.im| * Real.log q ≤ T ∧ ¬(χ = χ₁ ∧ ρ = β₁)
  let gfun : DirichletCharacter ℂ q → ℂ → ℝ := fun χ ρ =>
    if Pc χ ρ then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0
  -- on `S` the summand agrees with the plain multiplicity
  have hL : (∑ z ∈ S, (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)) = ∑ z ∈ S, gfun z.1 z.2 := by
    refine Finset.sum_congr rfl (fun z hz => ?_)
    have h : Pc z.1 z.2 := ⟨hzm z hz, hlam z hz, him z hz, hexc z hz⟩
    simp only [gfun, if_pos h]
  -- split `S` into the fibres of the first coordinate
  have h2 : (∑ z ∈ S, gfun z.1 z.2)
      ≤ ∑ χ : DirichletCharacter ℂ q, ∑ᶠ ρ : ℂ, gfun χ ρ := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := S) (t := Finset.univ)
      (g := fun z : DirichletCharacter ℂ q × ℂ => z.1) (fun z _ => Finset.mem_univ z.1)
      (fun z => gfun z.1 z.2)]
    refine Finset.sum_le_sum (fun χ _ => ?_)
    have hinj : ∀ z ∈ S.filter (fun z => z.1 = χ), z.1 = χ :=
      fun z hz => (Finset.mem_filter.mp hz).2
    have hcong : (∑ z ∈ S.filter (fun z => z.1 = χ), gfun z.1 z.2)
        = ∑ z ∈ S.filter (fun z => z.1 = χ), gfun χ z.2 :=
      Finset.sum_congr rfl (fun z hz => by rw [(Finset.mem_filter.mp hz).2])
    rw [hcong]
    refine finset_sum_snd_le_finsum _ χ (gfun χ) hinj ?_
      (support_pairCountHeight_finite hq χ₁ β₁ χ)
    intro ρ
    by_cases h : Pc χ ρ
    · simp only [gfun, if_pos h]; positivity
    · simp only [gfun, if_neg h]; exact le_refl 0
  -- the double sum is `pairCountHeight` by definition
  have hRHS : (∑ χ : DirichletCharacter ℂ q, ∑ᶠ ρ : ℂ, gfun χ ρ)
      = Work.LinnikAreas.Siegel.pairCountHeight χ₁ β₁ t T := rfl
  calc (∑ z ∈ S, (Work.LinnikContract.zeroMult z.1 z.2 : ℝ))
      = ∑ z ∈ S, gfun z.1 z.2 := hL
    _ ≤ ∑ χ : DirichletCharacter ℂ q, ∑ᶠ ρ : ℂ, gfun χ ρ := h2
    _ = Work.LinnikAreas.Siegel.pairCountHeight χ₁ β₁ t T := hRHS

end Work.LinnikAreas
