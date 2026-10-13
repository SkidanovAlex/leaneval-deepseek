import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.VocabO2
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.PhiStar.wlInf_of_zeroOff
import Submission.Work.FTS.PhiStar.pzIter_DthIter_leibniz
import Submission.Work.FTS.PhiStar.sin_rpow_slack
import Submission.Work.FTS.PhiStar.CoreAux.AngSlot.sfun_Lop_iter_le
import Submission.Work.FTS.H2.STFacts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.SP6

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The angular slot bound at order `l`, on the closed domain, from the flat data.**

For a datum `f` which is `C^∞` on the open quadrant and vanishes off it, the flat bounds
`FlatW l f K` extend to the weighted angular slots of `Work.Spaces.WlInf α l`:

`|(z+1)^k ∂_z^k D_θ^j f · sin(2θ)^{-α/5}/(α + sin 2θ)| ≤ C·K`   (`1 ≤ j`, `k + j ≤ l`),

on the whole closed rectangle `[0,∞) × [0,π/2]`, with `C` a universal constant (depending on
`l` only).

The three regions:

* **the open quadrant**: the Leibniz expansion of `D_θ = sin(2·)∂_θ`,
  `D_θ^j f = Σ_{a<j} C(j-1,a) (D_θ^a sin 2·) (D_θ^{j-1-a} ∂_θ f)`, whose `z`-derivative form is
  `Work.FTS.PhiStar.pzIter_DthIter_leibniz`.  The coefficient iterates of `sin 2·` carry a
  factor `sin(2θ)` (`sfun_Lop_iter_le`), while `(z+1)^k ∂_z^k D_θ^{j-1-a}(∂_θf)` is one of the
  quantities bounded by `K` in `FlatW`'s second clause.  The surviving `sin(2θ)` is exactly what
  `sin_rpow_slack` consumes: `sin(2θ)·sin(2θ)^{-α/5}/(α + sin 2θ) ≤ 2`.
* **the angular endpoints** `θ = 0, π/2`: the weight vanishes (`0^{-α/5} = 0`).
* **the origin** `z = 0`: the whole `z`-slice vanishes (here `zeroOff` is used), so every
  iterated `z`-derivative of it at `0` is `0`. -/
theorem angSlot_le_flatW_general (l : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (K : ℝ), 0 < α → α ≤ 1 → 0 ≤ K →
        (∀ z θ : ℝ, (z, θ) ∉ Work.FTS.EllipticEst.Q0 → f z θ = 0) →
        Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.VocabO2.FlatW l f K →
        ∀ (j k : ℕ), 1 ≤ j → k + j ≤ l → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
          |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ
            * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))| ≤ C * K := by
  obtain ⟨A, hApos, hAb⟩ := Work.FTS.PhiStar.CoreAux.AngSlot.sfun_Lop_iter_le l
  have hCpos : (0 : ℝ) < (2 : ℝ) ^ (l + 1) * A := mul_pos (by positivity) hApos
  refine ⟨(2 : ℝ) ^ (l + 1) * A, hCpos, ?_⟩
  intro α f K hα0 hα1 hK hzero hf hF j k hj hjk z hz θ hθ
  have hsin_nn : 0 ≤ Real.sin (2 * θ) := Work.FTS.PhiStar.sin_two_nonneg_Iθ hθ
  have hCnn : (0 : ℝ) ≤ (2 : ℝ) ^ (l + 1) * A := hCpos.le
  rcases lt_or_eq_of_le (show (0 : ℝ) ≤ z from hz) with hzpos | hz0eq
  · by_cases hθI : θ ∈ Set.Ioo 0 (Real.pi / 2)
    · -- the open quadrant: the Leibniz expansion plus the flat bound
      have hsin_pos : 0 < Real.sin (2 * θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hθI.1]) (by linarith [hθI.2, Real.pi_pos])
      have hden_nn : 0 ≤ α + Real.sin (2 * θ) := by linarith
      have hleib := Work.FTS.PhiStar.pzIter_DthIter_leibniz (f := f) (k := k) hf hj hzpos hθI
      have hmain : |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ|
          ≤ (A * (2 : ℝ) ^ l) * K * Real.sin (2 * θ) := by
        have hsum : |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ|
            ≤ (∑ a ∈ Finset.range j, ((j - 1).choose a : ℝ) * A) * K * Real.sin (2 * θ) := by
          rw [hleib, Finset.mul_sum]
          calc |∑ a ∈ Finset.range j, (z + 1) ^ k * (((j - 1).choose a : ℝ) *
                  (Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ *
                    Work.Spaces.pzIter k (Work.Spaces.DthIter (j - 1 - a)
                      (Work.Spaces.pth f)) z θ))|
              = |∑ a ∈ Finset.range j, ((j - 1).choose a : ℝ) *
                  ((z + 1) ^ k * (Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ *
                    Work.Spaces.pzIter k (Work.Spaces.DthIter (j - 1 - a)
                      (Work.Spaces.pth f)) z θ))| := by
                congr 1
                exact Finset.sum_congr rfl fun a _ => by ring
            _ ≤ ∑ a ∈ Finset.range j, |((j - 1).choose a : ℝ) *
                  ((z + 1) ^ k * (Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ *
                    Work.Spaces.pzIter k (Work.Spaces.DthIter (j - 1 - a)
                      (Work.Spaces.pth f)) z θ))| := Finset.abs_sum_le_sum_abs _ _
            _ = ∑ a ∈ Finset.range j, ((j - 1).choose a : ℝ) *
                  |(z + 1) ^ k * (Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ *
                    Work.Spaces.pzIter k (Work.Spaces.DthIter (j - 1 - a)
                      (Work.Spaces.pth f)) z θ)| := by
                exact Finset.sum_congr rfl fun a _ => by
                  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
            _ ≤ ∑ a ∈ Finset.range j, ((j - 1).choose a : ℝ) * (A * Real.sin (2 * θ) * K) := by
                refine Finset.sum_le_sum fun a ha => ?_
                refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
                have haj : a ≤ j - 1 := by rw [Finset.mem_range] at ha; omega
                have hAterm : |Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ|
                    ≤ A * Real.sin (2 * θ) := by
                  have h2 : Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ
                      = (Work.Spaces.Lop^[a]) (fun θ' => Real.sin (2 * θ')) θ := by
                    have hfun : (fun θ' => Work.FTS.H2.Sfun z θ')
                        = (fun θ' => Real.sin (2 * θ')) := by funext θ'; rfl
                    rw [Work.Spaces.DthIter_eq_iterate_Lop a Work.FTS.H2.Sfun z, hfun]
                  rw [h2]
                  exact hAb a (by omega) θ hθ
                have hKterm : |(z + 1) ^ k * Work.Spaces.pzIter k
                      (Work.Spaces.DthIter (j - 1 - a) (Work.Spaces.pth f)) z θ| ≤ K :=
                  (hF z θ hzpos hθI.1 hθI.2).2 k (j - 1 - a) (by omega)
                calc |(z + 1) ^ k * (Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ *
                      Work.Spaces.pzIter k (Work.Spaces.DthIter (j - 1 - a)
                        (Work.Spaces.pth f)) z θ)|
                    = |Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ| *
                        |(z + 1) ^ k * Work.Spaces.pzIter k
                          (Work.Spaces.DthIter (j - 1 - a) (Work.Spaces.pth f)) z θ| := by
                      rw [show (z + 1) ^ k * (Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ *
                            Work.Spaces.pzIter k (Work.Spaces.DthIter (j - 1 - a)
                              (Work.Spaces.pth f)) z θ)
                          = Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ *
                            ((z + 1) ^ k * Work.Spaces.pzIter k
                              (Work.Spaces.DthIter (j - 1 - a)
                                (Work.Spaces.pth f)) z θ) from by ring, abs_mul]
                  _ ≤ (A * Real.sin (2 * θ)) * K :=
                      mul_le_mul hAterm hKterm (abs_nonneg _)
                        (mul_nonneg hApos.le hsin_nn)
                  _ = A * Real.sin (2 * θ) * K := by ring
            _ = (∑ a ∈ Finset.range j, ((j - 1).choose a : ℝ) * A) * (K * Real.sin (2 * θ)) := by
                rw [Finset.sum_mul]
                exact Finset.sum_congr rfl fun a _ => by ring
            _ = (∑ a ∈ Finset.range j, ((j - 1).choose a : ℝ) * A) * K
                  * Real.sin (2 * θ) := by ring
        have hjsum : (∑ a ∈ Finset.range j, ((j - 1).choose a : ℝ) * A)
            ≤ A * (2 : ℝ) ^ l := by
          have hchoose : (∑ a ∈ Finset.range j, ((j - 1).choose a : ℝ))
              = (2 : ℝ) ^ (j - 1) := by
            have hrange : Finset.range j = Finset.range ((j - 1) + 1) := by congr 1; omega
            rw [hrange]
            exact_mod_cast Nat.sum_range_choose (n := j - 1)
          calc (∑ a ∈ Finset.range j, ((j - 1).choose a : ℝ) * A)
              = (∑ a ∈ Finset.range j, ((j - 1).choose a : ℝ)) * A := (Finset.sum_mul ..).symm
            _ = (2 : ℝ) ^ (j - 1) * A := by rw [hchoose]
            _ ≤ (2 : ℝ) ^ l * A := by
                refine mul_le_mul_of_nonneg_right ?_ hApos.le
                exact pow_le_pow_right₀ (by norm_num) (by omega)
            _ = A * (2 : ℝ) ^ l := by ring
        calc |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ|
              ≤ (∑ a ∈ Finset.range j, ((j - 1).choose a : ℝ) * A) * K
                * Real.sin (2 * θ) := hsum
          _ ≤ (A * (2 : ℝ) ^ l) * K * Real.sin (2 * θ) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hjsum hK) hsin_nn
      -- multiply by the angular weight
      have hrpow : Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-(α / 5))
          = (Real.sin (2 * θ)) ^ (1 - α / 5) := by
        have h : (1 : ℝ) - α / 5 = 1 + -(α / 5) := by ring
        rw [h, Real.rpow_add hsin_pos, Real.rpow_one]
      have hw_nn : 0 ≤ (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) :=
        div_nonneg (Real.rpow_nonneg hsin_nn _) hden_nn
      calc |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ
            * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))|
          = |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ|
              * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) := by
            rw [abs_div, abs_mul, abs_of_nonneg (Real.rpow_nonneg hsin_nn _),
              abs_of_nonneg hden_nn]
            ring
        _ ≤ ((A * (2 : ℝ) ^ l) * K * Real.sin (2 * θ))
              * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) :=
            mul_le_mul_of_nonneg_right hmain hw_nn
        _ = (A * (2 : ℝ) ^ l) * K * (Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-(α / 5))
              / (α + Real.sin (2 * θ))) := by ring
        _ = (A * (2 : ℝ) ^ l) * K * ((Real.sin (2 * θ)) ^ (1 - α / 5)
              / (α + Real.sin (2 * θ))) := by rw [hrpow]
        _ ≤ (A * (2 : ℝ) ^ l) * K * 2 := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact Work.FTS.PhiStar.sin_rpow_slack hα0 hα1 hsin_nn (Real.sin_le_one _)
        _ ≤ ((2 : ℝ) ^ (l + 1) * A) * K := by
            have h : (A * (2 : ℝ) ^ l) * K * 2 = ((2 : ℝ) ^ (l + 1) * A) * K := by
              rw [pow_succ]; ring
            exact le_of_eq h
    · -- `θ = 0` or `θ = π / 2`: the angular weight vanishes
      rw [Work.Spaces.Iθ] at hθ
      have hcases : θ = 0 ∨ θ = Real.pi / 2 := by
        rcases eq_or_lt_of_le hθ.1 with h | h
        · exact Or.inl h.symm
        · exact Or.inr (le_antisymm hθ.2 (not_lt.mp fun hlt => hθI ⟨h, hlt⟩))
      have hsin0 : Real.sin (2 * θ) = 0 := by
        rcases hcases with h | h
        · rw [h]; norm_num
        · rw [h, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
      have hrpow : (Real.sin (2 * θ)) ^ (-(α / 5)) = 0 := by
        rw [hsin0]
        exact Real.zero_rpow (by linarith : -(α / 5) ≠ 0)
      rw [hrpow, mul_zero, zero_div, abs_zero]
      exact mul_nonneg hCnn hK
  · -- `z = 0`: the whole `z`-slice `z' ↦ D_θ^j f z' θ` vanishes on `(-∞,0]`
    have hz0 : z = 0 := hz0eq.symm
    subst hz0
    have hsd : Work.Spaces.pzIter k (Work.Spaces.DthIter j f) 0 θ = 0 := by
      rw [Work.Spaces.pzIter_eq_iteratedDeriv]
      refine Work.FTS.PhiStar.iteratedDeriv_eq_zero_of_eqOn_Iic
        (g := fun z' => Work.Spaces.DthIter j f z' θ) ?_ k 0 le_rfl
      intro z' hz'
      exact Work.FTS.PhiStar.DthIter_eq_zero_of_slice_zero (u := f) (z := z')
        (fun θ' => hzero z' θ' (by
          intro hmem
          have h1 : (0 : ℝ) < z' := (Work.FTS.EllipticEst.mem_Q0.mp hmem).1
          linarith)) j θ
    rw [hsd]
    simp only [mul_zero, zero_mul, zero_div, abs_zero]
    exact mul_nonneg hCnn hK

theorem AngSlot6 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (K : ℝ),
    0 < α → α ≤ 1 → 0 ≤ K →
    (∀ z θ : ℝ, (z, θ) ∉ Work.FTS.EllipticEst.Q0 → f z θ = 0) →
    Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.VocabO2.FlatW 6 f K →
    ∀ (j k : ℕ), 1 ≤ j → k + j ≤ 6 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))| ≤ C * K := by
  obtain ⟨C, hC, h⟩ := angSlot_le_flatW_general 6
  exact ⟨C, hC, fun α f K hα0 hα1 hK hzero hf hF j k hj hjk z hz θ hθ =>
    h α f K hα0 hα1 hK hzero hf hF j k hj hjk z hz θ hθ⟩

end Work.FTS.StrongPersist.SP6
