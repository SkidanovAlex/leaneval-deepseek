import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.Sector.jointProj_orthogonal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.Sector.secProj_orthogonal`

The **`n₊`-sectors of a state are mutually orthogonal** in `L²(Λ(ℓ)ᴺ)`:

    ∫_{abox n ℓ} (1_{n₊=i}Φ)(x) · (1_{n₊=j}Φ)(x) dx = 0      for `i ≠ j`.

This is the diagonal part of the FS §6 (`lem:LocMatrices`, `final_v2.tex`
ll. 1365–1445) projection algebra: the sectors `1_{n₊=k}Ψ` form an orthogonal
family because

    `secProj ℓ k Φ = ∑_{S ∈ psC k} E_S Φ`,   `E_S = ∏_{i∈S}Q_i ∏_{j∉S}P_j`,

and two *different* joint sectors `E_S`, `E_T` are orthogonal over the box
(`jointProj_orthogonal`, already proved in the sibling file).

## The argument

Expand the product of the two sums and integrate term by term
(`MeasureTheory.integral_finsetSum` applied twice; every summand is continuous
on the compact box, hence integrable by `integrableOn_abox_of_continuous`):

    ∫ (∑_S E_S Φ)(∑_T E_T Φ) = ∑_S ∑_T ∫ (E_S Φ)(E_T Φ).

For `S ∈ psC i` and `T ∈ psC j` we have `S ⊆ range n` and `T ⊆ range n`, hence
`S ∩ range n = S`, `T ∩ range n = T`, and `S ≠ T` because their cardinalities
are `i ≠ j`. So the hypothesis `S ∩ range n ≠ T ∩ range n` of
`jointProj_orthogonal` is met and **every** term of the double sum vanishes.
-/

namespace Work.BoseFixB2.Sector

open Submission.BoseGases Work.BoseFixB2
open MeasureTheory
open scoped BigOperators

set_option maxHeartbeats 800000

theorem secProj_orthogonal {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {i j : ℕ} (hij : i ≠ j) {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ) : (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseFixB2.secProj ℓ i Φ x * Work.BoseFixB2.secProj ℓ j Φ x) = 0 := by
  -- 1. Expand both sectors: pointwise, the product is the double sum of the
  --    cross terms `E_S Φ · E_T Φ`.
  have hfun : (fun x : X n => secProj ℓ i Φ x * secProj ℓ j Φ x)
      = fun x : X n => ∑ S ∈ (Finset.range n).powersetCard i,
          ∑ T ∈ (Finset.range n).powersetCard j,
            jointProj ℓ S Φ x * jointProj ℓ T Φ x := by
    funext x
    simp only [secProj, Finset.sum_apply]
    rw [Finset.sum_mul_sum]
  -- 2. Every cross term is integrable on the box: it is continuous.
  have hint : ∀ S T : Finset ℕ,
      IntegrableOn (fun x : X n => jointProj ℓ S Φ x * jointProj ℓ T Φ x) (abox n ℓ) volume :=
    fun S T => integrableOn_abox_of_continuous hℓ
      ((jointProj_continuous hℓ S hΦ).mul (jointProj_continuous hℓ T hΦ))
  -- 3. Integrate the double sum term by term (twice).
  have hstep1 : (∫ x in abox n ℓ, ∑ S ∈ (Finset.range n).powersetCard i,
        ∑ T ∈ (Finset.range n).powersetCard j,
          jointProj ℓ S Φ x * jointProj ℓ T Φ x)
      = ∑ S ∈ (Finset.range n).powersetCard i,
          ∫ x in abox n ℓ, (∑ T ∈ (Finset.range n).powersetCard j,
            jointProj ℓ S Φ x * jointProj ℓ T Φ x) :=
    integral_finsetSum _
      (f := fun S x => ∑ T ∈ (Finset.range n).powersetCard j,
        jointProj ℓ S Φ x * jointProj ℓ T Φ x)
      (fun S _ => integrable_finsetSum _ (fun T _ => hint S T))
  have hstep2 : ∀ S ∈ (Finset.range n).powersetCard i,
      (∫ x in abox n ℓ, (∑ T ∈ (Finset.range n).powersetCard j,
          jointProj ℓ S Φ x * jointProj ℓ T Φ x))
      = ∑ T ∈ (Finset.range n).powersetCard j,
          ∫ x in abox n ℓ, jointProj ℓ S Φ x * jointProj ℓ T Φ x := by
    intro S _
    exact integral_finsetSum _
      (f := fun T x => jointProj ℓ S Φ x * jointProj ℓ T Φ x)
      (fun T _ => hint S T)
  -- 4. Sectors with different cardinalities are different subsets of `range n`.
  have hST : ∀ S ∈ (Finset.range n).powersetCard i,
      ∀ T ∈ (Finset.range n).powersetCard j, S ∩ Finset.range n ≠ T ∩ Finset.range n := by
    intro S hS T hT h
    obtain ⟨hSr, hSc⟩ := Finset.mem_powersetCard.mp hS
    obtain ⟨hTr, hTc⟩ := Finset.mem_powersetCard.mp hT
    rw [Finset.inter_eq_left.mpr hSr, Finset.inter_eq_left.mpr hTr] at h
    exact hij (by rw [← hSc, ← hTc, h])
  -- 5. Assemble: every term of the double sum vanishes.
  rw [hfun, hstep1]
  apply Finset.sum_eq_zero
  intro S hS
  rw [hstep2 S hS]
  apply Finset.sum_eq_zero
  intro T hT
  exact jointProj_orthogonal hℓ (hST S hS T hT) Φ Φ hΦ hΦ

end Work.BoseFixB2.Sector
