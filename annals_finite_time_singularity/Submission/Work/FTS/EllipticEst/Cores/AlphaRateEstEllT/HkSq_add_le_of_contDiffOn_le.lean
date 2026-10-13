/-
Copyright: work module for the Elgindi finite-time singularity project.

# Subadditivity of the weighted `ℋ^k`-norm for data of *finite* smoothness

`Work.FTS.EllipticEst.HkNorm_add_le` proves

`HkSq α k (f + g) ≤ 2 · HkSq α k f + 2 · HkSq α k g`

for two functions that are `C^∞` on the *open* quadrant `(0,∞) × (0,π/2)`, by the pointwise
inequality for the integrands (`Work.FTS.EllipticEst.HkSq_add_le_of_pointwise`) plus the honest
additivity of the iterated operators `D_z^i`, `D_z^j D_θ^i` there.  This module records the
*honest* (`C^k` / `C^{k-1}`) form of the same statement, which is what a summand that is only
smooth to order `k-1` can be fed.

## Why the weaker hypothesis `g ∈ C^{k-1}` is enough

`HkIntegrand α k` contains the slots `D_z^i` with `i ≤ k` and `D_z^j D_θ^i` with `i + j ≤ k`, so
the *totalised* iterates of a merely `C^{k-1}` summand are junk at the top order and the naive
identity `D_z^k (f+g) = D_z^k f + D_z^k g` can genuinely fail there.  It fails harmlessly: at a
point where `D_z^{k-1} g` is not differentiable the junk value `D_z^k g` is `0` *and*, since
`D_z^{k-1} f` **is** differentiable (`f` having one more order of smoothness), the sum
`D_z^{k-1}(f+g)` is not differentiable either, so `D_z^k (f+g) = 0` as well; the left-hand side
of the slot inequality is `0` and the inequality is trivial.  Where the `g`-piece is
differentiable the identity holds and `(a+b)² ≤ 2a² + 2b²` finishes.  This two-case analysis is
the content of the one-variable lemma `Work.FTS.EllipticEst.RegQ.SliceD.dopIter_sq_le`
(levels `≤ n-1`: honest linearity of the totalised operator; level `n`: the split on
`DifferentiableAt (D^{n-1} w) x`), which is applied to the `θ`-slices when `j = 0` and to the
`z`-slices of the `D_θ^i`'s when `j ≥ 1` — exactly the route of
`Work.FTS.EllipticEst.RegQ.Q2.slot_sq_le` for the linear combination `-3f - αg`, here in the
form `f + g`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.HkNorm_add_le
import Submission.Work.FTS.EllipticEst.RegQ.pthU_slot_alg

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.AlphaRateEstEllT

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The open quadrant `(0,∞) × (0,π/2)` of the smoothness hypotheses. -/
private abbrev quadV : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)

/-! ## The `θ`-identity for the sum at levels `≤ k-1`

Both summands are `C^{k-1}` there, so the honest linearity of the totalised `D_θ^i` applies. -/

/-- **The `θ`-identity for the sum.**  For `E = f + g` on the open quadrant, `f` of class `C^k`
and `g` of class `C^{k-1}` there, and `i ≤ k-1`,

  `D_θ^i E = D_θ^i f + D_θ^i g`   on `(0,∞) × (0,π/2)`.

This is the honest linearity of `D_θ^i` for `C^i` data, applied to the `θ`-slices. -/
private theorem DthIter_lin_sum {k : ℕ} {E f g : ℝ → ℝ → ℝ}
    (hE : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → E z θ = f z θ + g z θ)
    (hf : ContDiffOn ℝ k (Function.uncurry f) quadV)
    (hg : ContDiffOn ℝ (k - 1) (Function.uncurry g) quadV)
    {i : ℕ} (hi : i ≤ k - 1) :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DthIter i E z θ
        = Work.Spaces.DthIter i f z θ + Work.Spaces.DthIter i g z θ := by
  intro z θ hz hθ0 hθ1
  have hU : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  have hmem : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hzmem : z ∈ Set.Ioi (0 : ℝ) := hz
  have huf : ContDiffOn ℝ i (fun θ' => f z θ') (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.RegQ.contDiffOn_of_le_nat
      (Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_slice_θ_fin hf hzmem) (by omega)
  have hug : ContDiffOn ℝ i (fun θ' => g z θ') (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.RegQ.contDiffOn_of_le_nat
      (Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_slice_θ_fin hg hzmem) (by omega)
  have hv : ∀ θ' ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      E z θ' = (1 : ℝ) * f z θ' + (1 : ℝ) * g z θ' := by
    intro θ' hθ'
    rw [hE z θ' hz hθ'.1 hθ'.2]; ring
  rw [Work.FTS.EllipticEst.RegQ.Q2.DthIter_slice_eq E i z θ,
    Work.FTS.EllipticEst.RegQ.Q2.DthIter_slice_eq f i z θ,
    Work.FTS.EllipticEst.RegQ.Q2.DthIter_slice_eq g i z θ]
  rw [Work.FTS.EllipticEst.RegQ.SliceD.dopIter_congr hU hv i θ hmem]
  rw [Work.FTS.EllipticEst.RegQ.SliceD.dopIter_lin hU
    (Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_wT i) huf hug (1 : ℝ) (1 : ℝ) i le_rfl θ hmem]
  ring

/-! ## The pointwise slot estimate -/

/-- **The pointwise slot estimate.**  For `i + j ≤ k` and `(z,θ)` in the open quadrant,

  `(D_z^j D_θ^i E)² ≤ 2 (D_z^j D_θ^i f)² + 2 (D_z^j D_θ^i g)²`.

For `j = 0` this is the one-variable slot lemma in the `θ`-direction (`ω = sin 2·`) applied to
the `θ`-slices; for `j ≥ 1` (so that `i ≤ k-1` and the `θ`-identity is available) it is the same
lemma in the `z`-direction (`ω = id`) applied to the `z`-slices of the `D_θ^i`'s. -/
private theorem slot_sq_le_sum {k : ℕ} {E f g : ℝ → ℝ → ℝ}
    (hE : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → E z θ = f z θ + g z θ)
    (hf : ContDiffOn ℝ k (Function.uncurry f) quadV)
    (hg : ContDiffOn ℝ (k - 1) (Function.uncurry g) quadV)
    {i j : ℕ} (hij : i + j ≤ k) {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ)
    (hθ1 : θ < Real.pi / 2) :
    (Work.Spaces.DzIter j (Work.Spaces.DthIter i E) z θ) ^ 2
      ≤ 2 * (Work.Spaces.DzIter j (Work.Spaces.DthIter i f) z θ) ^ 2
        + 2 * (Work.Spaces.DzIter j (Work.Spaces.DthIter i g) z θ) ^ 2 := by
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · -- `j = 0`: the `θ`-direction
    rw [hj0]
    simp only [Work.Spaces.DzIter_zero]
    have hU : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
    have hmem : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
    have hzmem : z ∈ Set.Ioi (0 : ℝ) := hz
    have huf : ContDiffOn ℝ i (fun θ' => f z θ') (Set.Ioo 0 (Real.pi / 2)) :=
      Work.FTS.EllipticEst.RegQ.contDiffOn_of_le_nat
        (Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_slice_θ_fin hf hzmem) (by omega)
    have hug : ContDiffOn ℝ (i - 1 : ℕ) (fun θ' => g z θ') (Set.Ioo 0 (Real.pi / 2)) :=
      Work.FTS.EllipticEst.RegQ.contDiffOn_of_le_nat
        (Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_slice_θ_fin hg hzmem) (by omega)
    have hv : ∀ θ' ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        E z θ' = (1 : ℝ) * f z θ' + (1 : ℝ) * g z θ' := by
      intro θ' hθ'
      rw [hE z θ' hz hθ'.1 hθ'.2]; ring
    have key := Work.FTS.EllipticEst.RegQ.SliceD.dopIter_sq_le
      (ω := Work.FTS.EllipticEst.RegQ.Q2.wT) (U := Set.Ioo (0 : ℝ) (Real.pi / 2)) hU
      (Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_wT i) huf hug (1 : ℝ) (1 : ℝ) hv i le_rfl θ hmem
    rw [← Work.FTS.EllipticEst.RegQ.Q2.DthIter_slice_eq E i z θ,
      ← Work.FTS.EllipticEst.RegQ.Q2.DthIter_slice_eq f i z θ,
      ← Work.FTS.EllipticEst.RegQ.Q2.DthIter_slice_eq g i z θ] at key
    nlinarith [key]
  · -- `j ≥ 1`, hence `i ≤ k - 1` and the `θ`-identity is available
    have hi : i ≤ k - 1 := by omega
    have hid := DthIter_lin_sum hE hf hg hi
    have hU : IsOpen (Set.Ioi (0 : ℝ)) := isOpen_Ioi
    have hzmem : z ∈ Set.Ioi (0 : ℝ) := hz
    have hθmem : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
    have huf : ContDiffOn ℝ j (fun z' => Work.Spaces.DthIter i f z' θ) (Set.Ioi 0) :=
      Work.FTS.EllipticEst.RegQ.contDiffOn_of_le_nat
        (Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_slice_z_fin
          (Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DthIter_fin
            Work.FTS.EllipticEst.RegQ.Q2.isOpen_Qd hf i (by omega)) hθmem)
        (by omega)
    have hug : ContDiffOn ℝ (j - 1 : ℕ)
        (fun z' => Work.Spaces.DthIter i g z' θ) (Set.Ioi 0) :=
      Work.FTS.EllipticEst.RegQ.contDiffOn_of_le_nat
        (Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_slice_z_fin
          (Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DthIter_fin
            Work.FTS.EllipticEst.RegQ.Q2.isOpen_Qd hg i (by omega)) hθmem)
        (by omega)
    have hv : ∀ z' ∈ Set.Ioi (0 : ℝ),
        Work.Spaces.DthIter i E z' θ
          = (1 : ℝ) * Work.Spaces.DthIter i f z' θ
            + (1 : ℝ) * Work.Spaces.DthIter i g z' θ := by
      intro z' hz'
      rw [hid z' θ hz' hθ0 hθ1]; ring
    have key := Work.FTS.EllipticEst.RegQ.SliceD.dopIter_sq_le
      (ω := Work.FTS.EllipticEst.RegQ.Q2.wZ) (U := Set.Ioi (0 : ℝ)) hU
      (Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_wZ j) huf hug (1 : ℝ) (1 : ℝ) hv j le_rfl z hzmem
    rw [← Work.FTS.EllipticEst.RegQ.Q2.DzIter_slice_eq (Work.Spaces.DthIter i E) j z θ,
      ← Work.FTS.EllipticEst.RegQ.Q2.DzIter_slice_eq (Work.Spaces.DthIter i f) j z θ,
      ← Work.FTS.EllipticEst.RegQ.Q2.DzIter_slice_eq (Work.Spaces.DthIter i g) j z θ] at key
    nlinarith [key]

/-! ## The pointwise integrand estimate -/

/-- **The pointwise integrand estimate.**  For `E = f + g` pointwise on the open quadrant, `f` of
class `C^k` and `g` of class `C^{k-1}` there,

  `HkIntegrand α k E ≤ 2 HkIntegrand α k f + 2 HkIntegrand α k g`

on `Iz × Iθ`.  This is the slot estimate `slot_sq_le_sum` assembled over the finitely many slots
of the integrand. -/
private theorem HkIntegrand_sum_le (α : ℝ) (k : ℕ) {E f g : ℝ → ℝ → ℝ}
    (hE : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → E z θ = f z θ + g z θ)
    (hf : ContDiffOn ℝ k (Function.uncurry f) quadV)
    (hg : ContDiffOn ℝ (k - 1) (Function.uncurry g) quadV) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k E z θ
        ≤ 2 * Work.Spaces.HkIntegrand α k f z θ
          + 2 * Work.Spaces.HkIntegrand α k g z θ := by
  intro z hz θ hθ
  by_cases hz0 : z = 0
  · rw [hz0, Work.FTS.EllipticEst.RegQ.HkIntegrand_zero_z_fts α k E θ,
      Work.FTS.EllipticEst.RegQ.HkIntegrand_zero_z_fts α k f θ,
      Work.FTS.EllipticEst.RegQ.HkIntegrand_zero_z_fts α k g θ]
    norm_num
  by_cases hs : Real.sin (2 * θ) = 0
  · rw [Work.FTS.EllipticEst.RegQ.HkIntegrand_zero_sin_fts α k E hs z,
      Work.FTS.EllipticEst.RegQ.HkIntegrand_zero_sin_fts α k f hs z,
      Work.FTS.EllipticEst.RegQ.HkIntegrand_zero_sin_fts α k g hs z]
    norm_num
  · have hzpos : 0 < z := lt_of_le_of_ne (Set.mem_Ici.mp hz) (Ne.symm hz0)
    have hbnd : 0 ≤ θ ∧ θ ≤ Real.pi / 2 := Set.mem_Icc.mp hθ
    have hθ0 : 0 < θ := by
      rcases eq_or_lt_of_le hbnd.1 with h' | h'
      · exact absurd (by rw [← h']; simp) hs
      · exact h'
    have hθ1 : θ < Real.pi / 2 := by
      rcases lt_or_eq_of_le hbnd.2 with h' | h'
      · exact h'
      · exact absurd (by rw [h', show (2 : ℝ) * (Real.pi / 2) = Real.pi from by ring,
          Real.sin_pi]) hs
    -- the slot estimate on the individual slots
    have hslot : ∀ i j : ℕ, i + j ≤ k →
        (Work.Spaces.DzIter j (Work.Spaces.DthIter i E) z θ) ^ 2
          ≤ 2 * (Work.Spaces.DzIter j (Work.Spaces.DthIter i f) z θ) ^ 2
            + 2 * (Work.Spaces.DzIter j (Work.Spaces.DthIter i g) z θ) ^ 2 := by
      intro i j hij
      exact slot_sq_le_sum hE hf hg hij hzpos hθ0 hθ1
    simp only [Work.Spaces.HkIntegrand, Work.Spaces.mixed]
    set ρ : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hρdef
    set Wtα : ℝ := Work.Spaces.Wt α z θ with hWtdef
    have hZle : (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i E z θ * ρ) ^ 2)
        ≤ 2 * (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i f z θ * ρ) ^ 2)
          + 2 * (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i g z θ * ρ) ^ 2) := by
      calc (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i E z θ * ρ) ^ 2)
          ≤ ∑ i ∈ Finset.range (k + 1),
              (2 * (Work.Spaces.DzIter i f z θ * ρ) ^ 2
                + 2 * (Work.Spaces.DzIter i g z θ * ρ) ^ 2) := by
            refine Finset.sum_le_sum fun i hi => ?_
            have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
            have hb := hslot 0 i (by omega)
            simp only [Work.Spaces.DthIter_zero, Work.Spaces.DzIter_zero, Nat.zero_add] at hb
            rw [mul_pow, mul_pow, mul_pow]
            nlinarith [hb, sq_nonneg ρ]
        _ = 2 * (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i f z θ * ρ) ^ 2)
              + 2 * (∑ i ∈ Finset.range (k + 1),
                  (Work.Spaces.DzIter i g z θ * ρ) ^ 2) :=
            Work.FTS.EllipticEst.RegQ.sum_mul_add _ _ _ 2 2
    have hMle : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k
            then (Work.Spaces.DzIter j (Work.Spaces.DthIter i E) z θ * Wtα) ^ 2 else 0))
        ≤ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k
              then (Work.Spaces.DzIter j (Work.Spaces.DthIter i f) z θ * Wtα) ^ 2 else 0))
          + 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k
              then (Work.Spaces.DzIter j (Work.Spaces.DthIter i g) z θ * Wtα) ^ 2 else 0)) := by
      calc (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k
              then (Work.Spaces.DzIter j (Work.Spaces.DthIter i E) z θ * Wtα) ^ 2 else 0))
          ≤ ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              (2 * (if 1 ≤ i ∧ i + j ≤ k
                  then (Work.Spaces.DzIter j (Work.Spaces.DthIter i f) z θ * Wtα) ^ 2
                  else 0)
                + 2 * (if 1 ≤ i ∧ i + j ≤ k
                  then (Work.Spaces.DzIter j (Work.Spaces.DthIter i g) z θ * Wtα) ^ 2
                  else 0)) := by
            refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
            by_cases hc : 1 ≤ i ∧ i + j ≤ k
            · rw [if_pos hc, if_pos hc, if_pos hc]
              have hb := hslot i j hc.2
              nlinarith [hb, sq_nonneg Wtα]
            · rw [if_neg hc, if_neg hc, if_neg hc]; norm_num
        _ = 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              (if 1 ≤ i ∧ i + j ≤ k
                then (Work.Spaces.DzIter j (Work.Spaces.DthIter i f) z θ * Wtα) ^ 2 else 0))
            + 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              (if 1 ≤ i ∧ i + j ≤ k
                then (Work.Spaces.DzIter j (Work.Spaces.DthIter i g) z θ * Wtα) ^ 2 else 0)) :=
            Work.FTS.EllipticEst.RegQ.sum_sum_mul_add _ _ _ 2 2
    linarith [hZle, hMle]

/-! ## The statement -/

theorem HkSq_add_le_of_contDiffOn_le {α : ℝ} {k : ℕ} (hk : 1 ≤ k) {f g : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ k (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hg : ContDiffOn ℝ (k - 1) (Function.uncurry g)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hmf : Work.Spaces.HkMem α k f) (hmg : Work.Spaces.HkMem α k g) :
    Work.Spaces.HkSq α k (fun z θ => f z θ + g z θ)
      ≤ 2 * Work.Spaces.HkSq α k f + 2 * Work.Spaces.HkSq α k g :=
  Work.FTS.EllipticEst.HkSq_add_le_of_pointwise α k hmf hmg
    (HkIntegrand_sum_le α k (fun _ _ _ _ _ => rfl) hf hg)

end Work.FTS.EllipticEst.Cores.AlphaRateEstEllT
