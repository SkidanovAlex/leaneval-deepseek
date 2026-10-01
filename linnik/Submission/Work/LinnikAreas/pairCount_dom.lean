import Mathlib
import Submission.Work.LinnikAreas.SiegelBase
import Submission.Work.LinnikAreas.boxMaxZero
import Submission.Work.LinnikAreas.siegelRestHigh

namespace Work.LinnikAreas

open scoped Classical BigOperators

/-- **A finite set of zero-pairs of bounded height is dominated by the counting function
`pairCount`.**  If every pair `z = (χ, ρ)` in a finite set `S` has `zeroMult χ ρ ≠ 0`,
`lamOf q ρ ≤ t`, `|Im ρ| ≤ 1` and `(χ,ρ)` different from the exceptional pair `(χ₁,β₁)`, then the
multiplicity-weighted cardinality of `S` is at most `pairCount χ₁ β₁ t` (which counts *all* such
pairs, with `lamOf q ρ ≤ t`, over all characters mod `q`).

(This is the plain (no-height) analogue of `Work.LinnikAreas.pairCountHeight_dom`, which is at
`Submission/Work/LinnikAreas/pairCountHeight_dom.lean`: unfold `pairCount` as
`∑ χ, ∑ᶠ ρ, ...`; the inner `finsum` has finite support because
`{ρ | zeroMult χ ρ ≠ 0 ∧ |Im ρ| ≤ 1}` is contained in the finite set of
`Work.LinnikAreas.boxMaxZeroAux.finite_zeroMult_box χ 0 1` (with
`zeroMult_re_pos` from `Submission/Work/LinnikAreas/siegelRestHigh.lean` and
`boxMaxZeroAux.zeroMult_re_lt_one`), so it may be rewritten with
`finsum_eq_sum_of_support_subset` and compared termwise with the finset sum over `S`, grouped by
the first coordinate.) -/
theorem pairCount_dom {q : ℕ} [NeZero q] (hq : 1 < q) (χ₁ : DirichletCharacter ℂ q) (β₁ : ℂ)
    {t : ℝ} (S : Finset (DirichletCharacter ℂ q × ℂ))
    (hzm : ∀ z ∈ S, Work.LinnikContract.zeroMult z.1 z.2 ≠ 0)
    (hlam : ∀ z ∈ S, Work.LinnikContract.lamOf q z.2 ≤ t)
    (him : ∀ z ∈ S, |z.2.im| ≤ 1)
    (hexc : ∀ z ∈ S, ¬(z.1 = χ₁ ∧ z.2 = β₁)) :
    (∑ z ∈ S, (Work.LinnikContract.zeroMult z.1 z.2 : ℝ))
      ≤ Work.LinnikAreas.Siegel.pairCount χ₁ β₁ t := by
  classical
  rw [Siegel.pairCount]
  -- group the left-hand side by the character (first coordinate)
  rw [(Finset.sum_fiberwise S (fun z : DirichletCharacter ℂ q × ℂ => z.1)
        (fun z => (Work.LinnikContract.zeroMult z.1 z.2 : ℝ))).symm]
  refine Finset.sum_le_sum fun χ _ => ?_
  -- the finite set of zeros of `χ` in the box `0 ≤ Re ≤ 1`, `|Im| ≤ 1`
  set F : Finset ℂ := (boxMaxZeroAux.finite_zeroMult_box χ 0 1).toFinset with hF
  set g : ℂ → ℝ := fun ρ => if Work.LinnikContract.zeroMult χ ρ ≠ 0 ∧
      Work.LinnikContract.lamOf q ρ ≤ t ∧ |ρ.im| ≤ 1 ∧ ¬(χ = χ₁ ∧ ρ = β₁)
      then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0 with hg
  have hmemF : ∀ ρ : ℂ, ρ ∈ F ↔ Work.LinnikContract.zeroMult χ ρ ≠ 0 ∧ 0 ≤ ρ.re ∧
      ρ.re ≤ 1 ∧ |ρ.im| ≤ 1 := by
    intro ρ
    simp only [hF, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  -- every point where `g` does not vanish lies in the box
  have hsupp : Function.support g ⊆ ↑F := by
    intro ρ hρ
    simp only [Function.mem_support] at hρ
    have hc : Work.LinnikContract.zeroMult χ ρ ≠ 0 ∧ Work.LinnikContract.lamOf q ρ ≤ t ∧
        |ρ.im| ≤ 1 ∧ ¬(χ = χ₁ ∧ ρ = β₁) := by
      by_contra hcon
      exact hρ (by rw [hg]; exact if_neg hcon)
    obtain ⟨hz, -, hi, -⟩ := hc
    exact (hmemF ρ).mpr ⟨hz, le_of_lt (zeroMult_re_pos χ hz),
      le_of_lt (boxMaxZeroAux.zeroMult_re_lt_one χ hz), hi⟩
  rw [finsum_eq_sum_of_support_subset g hsupp]
  -- compare the fibre sum over `S` with the sum of `g` over the box `F`
  set T : Finset (DirichletCharacter ℂ q × ℂ) := S.filter (fun z => z.1 = χ) with hT
  have hterm : ∀ z ∈ T, (Work.LinnikContract.zeroMult z.1 z.2 : ℝ) = g z.2 := by
    intro z hz
    have hzS : z ∈ S := (Finset.mem_filter.mp hz).1
    have hz1 : z.1 = χ := (Finset.mem_filter.mp hz).2
    have hc : Work.LinnikContract.zeroMult χ z.2 ≠ 0 ∧ Work.LinnikContract.lamOf q z.2 ≤ t ∧
        |z.2.im| ≤ 1 ∧ ¬(χ = χ₁ ∧ z.2 = β₁) := by
      refine ⟨by rw [← hz1]; exact hzm z hzS, hlam z hzS, him z hzS, ?_⟩
      rintro ⟨h1, h2⟩
      exact hexc z hzS ⟨by rw [hz1]; exact h1, h2⟩
    rw [hg]
    simp only [if_pos hc, hz1]
  have hinj : Set.InjOn (fun z : DirichletCharacter ℂ q × ℂ => z.2) ↑T := by
    intro z1 hz1 z2 hz2 heq
    have h1 : z1.1 = χ := (Finset.mem_filter.mp hz1).2
    have h2 : z2.1 = χ := (Finset.mem_filter.mp hz2).2
    exact Prod.ext (by rw [h1, h2]) heq
  have himage : ∑ ρ ∈ T.image (fun z => z.2), g ρ = ∑ z ∈ T, g z.2 :=
    Finset.sum_image hinj
  have hsub : T.image (fun z => z.2) ⊆ F := by
    intro ρ hρ
    obtain ⟨z, hzT, rfl⟩ := Finset.mem_image.mp hρ
    have hzS : z ∈ S := (Finset.mem_filter.mp hzT).1
    have hz1 : z.1 = χ := (Finset.mem_filter.mp hzT).2
    have hz : Work.LinnikContract.zeroMult χ z.2 ≠ 0 := by
      rw [← hz1]; exact hzm z hzS
    exact (hmemF z.2).mpr ⟨hz, le_of_lt (zeroMult_re_pos χ hz),
      le_of_lt (boxMaxZeroAux.zeroMult_re_lt_one χ hz), him z hzS⟩
  have hnonneg : ∀ ρ ∈ F, ρ ∉ T.image (fun z => z.2) → 0 ≤ g ρ := by
    intro ρ _ _
    by_cases hcon : Work.LinnikContract.zeroMult χ ρ ≠ 0 ∧ Work.LinnikContract.lamOf q ρ ≤ t ∧
        |ρ.im| ≤ 1 ∧ ¬(χ = χ₁ ∧ ρ = β₁)
    · have hz : g ρ = (Work.LinnikContract.zeroMult χ ρ : ℝ) := by
        rw [hg]; exact if_pos hcon
      rw [hz]; exact Nat.cast_nonneg _
    · have hz : g ρ = 0 := by rw [hg]; exact if_neg hcon
      rw [hz]
  calc ∑ z ∈ T, (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
      = ∑ z ∈ T, g z.2 := Finset.sum_congr rfl hterm
    _ = ∑ ρ ∈ T.image (fun z => z.2), g ρ := himage.symm
    _ ≤ ∑ ρ ∈ F, g ρ := Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg

end Work.LinnikAreas
