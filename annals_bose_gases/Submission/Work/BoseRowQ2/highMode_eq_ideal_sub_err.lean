import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.BoseRowQ2.chatTailAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseRowQ2

open Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Z3" => Fin 3 → ℤ

set_option linter.unusedVariables false

/-! ## Auxiliary analytic facts

The three lemmas below are the lattice/Parseval inputs of the coefficient decomposition.
They are the shifted form of `Work.BoseRowQ2.chiLatticeParseval`:

    `∑_{u ∈ ℤ³} χ̂(vec u)·χ̂(vec (D − u)) = χ̂²(vec D)`,

together with the summability of the summand (Schwartz decay of `χ̂`), which is what makes
the interchange of the finite `i`-sum with the `k`-sum legitimate. -/

/-- **Summability of the shifted `χ̂`-majorant.**  For every lattice shift `a : ℤ³` the shifted
decay majorant `m ↦ (1 + ‖vec (m − a)‖²)⁻⁵²` is summable: it is the translate of the summable
family `n ↦ (1 + ‖vec n‖²)⁻⁵²` (`Work.BoseK15.sum_inv_one_add_norm_le`). -/
private theorem summable_shift_majorant' (a : Z3) :
    Summable (fun m : Z3 => (((1 : ℝ) + ‖Work.BoseB4.vec (m - a)‖ ^ 2) ^ 52)⁻¹) := by
  obtain ⟨C0, _hC0nn, hC0⟩ := Work.BoseK15.sum_inv_one_add_norm_le 52 (by norm_num)
  have hbase : Summable (fun n : Z3 => (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹) :=
    summable_of_sum_le (fun n => by positivity) hC0
  have h := (Equiv.summable_iff (Equiv.subRight a)
    (f := fun n : Z3 => (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹)).mpr hbase
  exact h.congr (fun m => by simp [Function.comp, Equiv.subRight_apply])

/-- **Summability of the Parseval summand.**  For every pair of lattice shifts `a, D : ℤ³` the
family `k ↦ χ̂(vec (k − a))·χ̂(vec (D − k))` is summable: with the Schwartz decay
`|χ̂(p)| ≤ Cchi·(1 + ‖p‖²)⁻⁵²` (`Work.BoseK15.ChiReg_corpus`) and `|χ̂| ≤ 1`
(`Work.BoseRowQ2.chiHat_abs_le_one`) it is dominated by `Cchi·(1 + ‖vec (k − a)‖²)⁻⁵²`,
which is summable by `summable_shift_majorant'`. -/
private theorem summable_chiHat_mul' (a D : Z3) :
    Summable (fun k : Z3 => chiHat (Work.BoseB4.vec (k - a)) * chiHat (Work.BoseB4.vec (D - k))) := by
  obtain ⟨Cchi, hCchi0, hChi⟩ := Work.BoseK15.ChiReg_corpus 52
  have hChat_le : ∀ p : E3,
      |chiHat p| ≤ Cchi * (((1 : ℝ) + ‖p‖ ^ 2) ^ 52)⁻¹ := by
    intro p
    have hD : 0 < (1 + ‖p‖ ^ 2) ^ 52 := by positivity
    rw [chiHat]
    calc |Work.BoseK15.corpusBox.hatChi p|
        = |Work.BoseK15.corpusBox.hatChi p| * (1 + ‖p‖ ^ 2) ^ 52
            * ((1 + ‖p‖ ^ 2) ^ 52)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hD), mul_one]
      _ ≤ Cchi * ((1 + ‖p‖ ^ 2) ^ 52)⁻¹ :=
          mul_le_mul_of_nonneg_right (hChi.1 p) (inv_nonneg.mpr hD.le)
  refine Summable.of_norm_bounded (g := fun k : Z3 =>
    Cchi * (((1 : ℝ) + ‖Work.BoseB4.vec (k - a)‖ ^ 2) ^ 52)⁻¹)
    ((summable_shift_majorant' a).mul_left Cchi) ?_
  intro k
  rw [Real.norm_eq_abs, abs_mul]
  calc |chiHat (Work.BoseB4.vec (k - a))| * |chiHat (Work.BoseB4.vec (D - k))|
      ≤ (Cchi * (((1 : ℝ) + ‖Work.BoseB4.vec (k - a)‖ ^ 2) ^ 52)⁻¹) * 1 :=
        mul_le_mul (hChat_le _) (chiHat_abs_le_one _) (abs_nonneg _)
          (mul_nonneg hCchi0 (inv_nonneg.mpr (by positivity)))
    _ = Cchi * (((1 : ℝ) + ‖Work.BoseB4.vec (k - a)‖ ^ 2) ^ 52)⁻¹ := by ring

/-- **The convolution form of the lattice Parseval identity.**  For every `D : ℤ³`,
`∑_{u ∈ ℤ³} χ̂(vec u)·χ̂(vec (D − u)) = χ̂²(vec D)`.

This is `Work.BoseRowQ2.chiLatticeParseval` after the substitution `u ↦ D − u` (evenness of
`χ̂`), i.e. Parseval for the pair `(χ, χ·e^{-i⟪vec D,·⟫})`. -/
private theorem chiHat_conv_base (D : Z3) :
    (∑' u : Z3, chiHat (Work.BoseB4.vec u) * chiHat (Work.BoseB4.vec (D - u)))
      = chiHatSq (Work.BoseB4.vec D) := by
  have hpt : ∀ u : Z3, Work.BoseB4.vec (D - u) = -(Work.BoseB4.vec (u + (-D))) := by
    intro u
    rw [Work.BoseRowQ2.vec_add, Work.BoseRowQ2.vec_sub, Work.BoseBoxFock.vec_neg]
    abel
  calc (∑' u : Z3, chiHat (Work.BoseB4.vec u) * chiHat (Work.BoseB4.vec (D - u)))
      = ∑' u : Z3, chiHat (Work.BoseB4.vec u) * chiHat (Work.BoseB4.vec (u + (-D))) := by
        refine tsum_congr fun u => ?_
        rw [hpt u, chiHat_neg]
    _ = chiHatSq (Work.BoseB4.vec (-D)) := chiLatticeParseval (-D)
    _ = chiHatSq (Work.BoseB4.vec D) := by
        rw [Work.BoseBoxFock.vec_neg, chiHatSq_neg]

/-- **The shifted convolution form of the lattice Parseval identity.**  For every `a, D : ℤ³`,
`∑_{k ∈ ℤ³} χ̂(vec (k − a))·χ̂(vec (D − k)) = χ̂²(vec (D − a))`.

This is `chiHat_conv_base` after the reindexing `k ↦ k + a`. -/
private theorem chiHat_conv (a D : Z3) :
    (∑' k : Z3, chiHat (Work.BoseB4.vec (k - a)) * chiHat (Work.BoseB4.vec (D - k)))
      = chiHatSq (Work.BoseB4.vec (D - a)) := by
  calc (∑' k : Z3, chiHat (Work.BoseB4.vec (k - a)) * chiHat (Work.BoseB4.vec (D - k)))
      = ∑' u : Z3,
          chiHat (Work.BoseB4.vec u) * chiHat (Work.BoseB4.vec ((D - a) - u)) := by
        rw [← Equiv.tsum_eq (Equiv.addRight a)
          (fun k : Z3 => chiHat (Work.BoseB4.vec (k - a)) * chiHat (Work.BoseB4.vec (D - k)))]
        refine tsum_congr fun u => ?_
        have h1 : (u + a) - a = u := by
          funext i; simp only [Pi.add_apply, Pi.sub_apply]; ring
        have h2 : D - (u + a) = (D - a) - u := by
          funext i; simp only [Pi.add_apply, Pi.sub_apply]; ring
        simp only [Equiv.coe_addRight, h1, h2]
    _ = chiHatSq (Work.BoseB4.vec (D - a)) := chiHat_conv_base (D - a)

/-- **The coefficient decomposition** of the high-mode coefficient of `χ·W`, `W(x) = ∑_i w i e^{i⟪K i,x⟫}`:
for every `m : ℤ³`,

    `highMode N w m = highIdeal N w m − highErr N w m`,

i.e. `∑_{k ∈ Lab N} F̂(K k) χ̂(vec (m − K k)) = ∑_i w i χ̂²(vec (m − K i)) − ∑_{k ∉ cube N} F̂(k) χ̂(vec (m − k))`,
where `Fhat N w k = ∑_i w i χ̂(vec (k − K i))` are the Fourier coefficients of `χW` on the
full lattice.  Route: identify the `Lab N`-indexed sum with the `cube N`-indexed sum
(`Work.BoseRowQ2.image_labVec_eq_cube`, `ChatW_eq_Fhat`), split the full-lattice sum
`∑_{k : ℤ³} F̂(k) χ̂(vec (m − k))` into the cube part and its complement, and evaluate the full
sum by the convolution identity
`∑_{k : ℤ³} (∑_i w i χ̂(vec (k − K i))) χ̂(vec (m − k)) = ∑_i w i χ̂²(vec (m − K i))`,
which is `Work.BoseRowQ2.chiLatticeParseval` (shifted form, see `chatTail_eq_highMode`) followed by
exchanging the finite `i`-sum with the `k`-sum (justified by absolute convergence from the Schwartz
decay of `χ̂`). -/
theorem highMode_eq_ideal_sub_err (N : ℕ) (w : Work.BoseBoxFock.Lab N → ℝ) (m : Fin 3 → ℤ) :
    Work.BoseRowQ2.highMode N w m
      = Work.BoseRowQ2.highIdeal N w m - Work.BoseRowQ2.highErr N w m := by
  set g : Z3 → ℝ := fun k => Fhat N w k * chiHat (Work.BoseB4.vec (m - k)) with hg
  -- ### The summand expands as a finite sum over the labels
  have hgp : ∀ k : Z3, g k = ∑ i : Lab N, w i *
      (chiHat (Work.BoseB4.vec (k - labVec N i)) * chiHat (Work.BoseB4.vec (m - k))) := by
    intro k
    simp only [hg, Fhat]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  -- ### Each `i`-summand has sum `χ̂²(vec (m − K i))` (shifted lattice Parseval)
  have hhas_i : ∀ i : Lab N, HasSum
      (fun k : Z3 =>
        chiHat (Work.BoseB4.vec (k - labVec N i)) * chiHat (Work.BoseB4.vec (m - k)))
      (chiHatSq (Work.BoseB4.vec (m - labVec N i))) := by
    intro i
    have hsumm := summable_chiHat_mul' (labVec N i) m
    have htsum := chiHat_conv (labVec N i) m
    exact htsum ▸ hsumm.hasSum
  -- ### The full lattice sum of `g` is `highIdeal`
  have hHasSum : HasSum g (highIdeal N w m) := by
    have hsummand : ∀ i : Lab N, HasSum (fun k : Z3 => w i *
        (chiHat (Work.BoseB4.vec (k - labVec N i)) * chiHat (Work.BoseB4.vec (m - k))))
        (w i * chiHatSq (Work.BoseB4.vec (m - labVec N i))) :=
      fun i => (hhas_i i).mul_left (w i)
    have hmain : HasSum (fun k : Z3 => ∑ i : Lab N, w i *
        (chiHat (Work.BoseB4.vec (k - labVec N i)) * chiHat (Work.BoseB4.vec (m - k))))
        (∑ i : Lab N, w i * chiHatSq (Work.BoseB4.vec (m - labVec N i))) :=
      hasSum_sum (s := Finset.univ) (fun i _ => hsummand i)
    simpa [highIdeal] using hmain.congr_fun hgp
  have hsumm_g : Summable g := hHasSum.summable
  -- ### The cube part of the full sum is `highMode`
  have hcube : (∑ k ∈ cube N, g k) = highMode N w m := by
    rw [← image_labVec_eq_cube N, Finset.sum_image]
    · refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hg]
      rw [← ChatW_eq_Fhat N w k]
    · intro x _ y _ hxy
      exact labVec_inj' N hxy
  -- ### The complement of the cube is `highErr`
  have herr : (∑' k : {k : Z3 // k ∉ cube N}, g k.val) = highErr N w m := by
    rw [highErr]
  -- ### Assemble
  have hsplit := hsumm_g.sum_add_tsum_subtype_compl (s := cube N)
  rw [hcube, herr, hHasSum.tsum_eq] at hsplit
  linarith

end Work.BoseRowQ2
