/-
# `angmul_field_smoothInt` — angular multiplication in `ℋ⁴`, with the interface's `SmoothInt`
profile hypothesis

The interface field `angmul` (`Submission/Work/FTS/Nonlinear/Interface.lean`) carries the
hypothesis `Work.Spaces.SmoothInt (fun _ θ => a θ)` on the angular profile, i.e. `a` is `C^∞`
on the open strip `(-1,∞) × (0,π/2)` together with `z`-smoothness down to `z = 0` at every
angle.  This is *weaker* than the analyticity hypothesis `∀ θ, ContDiffAt ℝ ⊤ a θ` of
`Work.FTS.Nonlinear.N4Fields.angmul_field_smooth`: since `uncurry (fun _ θ => a θ) = a ∘ snd`,
it yields `ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => a p.2) Q0`, and that (plus
`ContDiffOn ℝ Work.Stability.smoothOrder a (Ioo 0 (π/2))`) is all the estimates use.  The
conversion lemmas live in `AngSmoothIntHelpers.lean`
(`contDiffOn_snd_of_smoothInt`, `contDiffOn_ang_of_Q0`, `smoothOpen_angMul_On`,
`DthIter_angular_mul_expand_On`).

The proof below is the proof of `angmul_field_smooth` with two changes: the reference pointwise
bound `HkIntegrand_ang_mul_unit_le` is replaced by its open-interval variant
`HkIntegrand_ang_mul_unit_le_Int` (proved here, a verbatim copy of the reference lemma with the
analyticity hypothesis weakened), and the rescaling `a = B·a'` uses `SmoothInt` of the rescaled
profile (`smoothInt_angDiv`) instead of pointwise analyticity.
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Nonlinear.Interface
import Submission.Work.FTS.Nonlinear.N4Fields.angmul_field_smooth
import Submission.Work.FTS.Nonlinear.N4Fields.AngSmoothIntHelpers

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.N4Fields

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The unit-profile pointwise `ℋ^k`-bound with open-interval smoothness

This is `Work.FTS.EllipticEst.Blocks.HkIntegrand_ang_mul_unit_le` (in
`Submission/Work/FTS/Nonlinear/N4Fields/angmul_field_smooth.lean`) with its analyticity
hypothesis `∀ θ : ℝ, ContDiffAt ℝ ⊤ a θ` replaced by
`ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => a p.2) Q0`.  The proof is a verbatim
copy of the reference proof: the only two uses of the analyticity hypothesis are the smoothness
of the product `(z,θ) ↦ a θ · f z θ` (now `smoothOpen_angMul_On`) and the Leibniz expansion
`D_θ^i (a · D_z^j f)` (now `DthIter_angular_mul_expand_On`, whose hypothesis on `a` is the
open-interval one supplied by `contDiffOn_ang_of_Q0`). -/
theorem HkIntegrand_ang_mul_unit_le_Int (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ → ℝ), (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |a θ| ≤ 1) →
      ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => a p.2)
        Work.FTS.EllipticEst.Q0 →
      (∀ m : ℕ, 1 ≤ m → m ≤ k → ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        (Work.FTS.EllipticEst.LopIter m a θ) ^ 2 ≤ (Real.sin (2 * θ)) ^ 2) →
      ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
        Work.FTS.EllipticEst.SmoothOpen f →
        ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          Work.Spaces.HkIntegrand α k (fun z θ => a θ * f z θ) z θ
            ≤ C * Work.Spaces.HkIntegrand α k f z θ := by
  set K : ℕ → ℝ := fun _ => 1 with hKdef
  have hK : ∀ m : ℕ, 0 ≤ K m := fun m => by rw [hKdef]; exact zero_le_one
  set KB : ℝ := ∑ m ∈ Finset.range (k + 1), (K m + 1) with hKBdef
  have hKBpos : 0 < KB := by
    rw [hKBdef]
    exact Finset.sum_pos (fun m _ => by linarith [hK m])
      ⟨0, Finset.mem_range.mpr (Nat.succ_pos k)⟩
  set CB : ℝ := ((2 : ℝ) ^ k) ^ 2 with hCBdef
  have hCBnonneg : 0 ≤ CB := by rw [hCBdef]; positivity
  set Cpair : ℝ := ((k : ℝ) + 1) * CB * KB with hCpairdef
  have hCpairnonneg : 0 ≤ Cpair := by rw [hCpairdef]; positivity
  set C1 : ℝ := ((k : ℝ) + 1) ^ 2 * Cpair with hC1def
  refine ⟨((k : ℝ) + 1) + C1, by positivity, ?_⟩
  intro a ha1 hha hKb0 α f hα hα1 hf z θ hz hθ0 hθ1
  have hKb : ∀ m : ℕ, 1 ≤ m → m ≤ k → ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Work.FTS.EllipticEst.LopIter m a θ) ^ 2 ≤ K m * (Real.sin (2 * θ)) ^ 2 := by
    intro m hm1 hmk θ hθ
    rw [hKdef]
    simpa using hKb0 m hm1 hmk θ hθ
  have hθIoo : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hHe : 0 ≤ Work.Spaces.HkIntegrand α k f z θ := Work.Spaces.HkIntegrand_nonneg α k f z θ
  have hZi : (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i (fun z θ => a θ * f z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ ((k : ℝ) + 1) * Work.Spaces.HkIntegrand α k f z θ := by
    have hterm : ∀ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i (fun z θ => a θ * f z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ Work.Spaces.HkIntegrand α k f z θ := by
      intro i hi
      have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [Work.FTS.EllipticEst.Blocks.DzIter_angular_mul i a f]
      have ha2 : (a θ) ^ 2 ≤ 1 := by
        have h := pow_le_pow_left₀ (abs_nonneg (a θ)) (ha1 θ hθIoo) 2
        rwa [sq_abs, one_pow] at h
      calc (a θ * Work.Spaces.DzIter i f z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          = (a θ) ^ 2 * (Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by ring
        _ ≤ 1 * (Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
            mul_le_mul_of_nonneg_right ha2 (sq_nonneg _)
        _ = (Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := one_mul _
        _ ≤ Work.Spaces.HkIntegrand α k f z θ := Work.Spaces.sq_le_HkIntegrand_z α k f z θ i hik
    calc (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i (fun z θ => a θ * f z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ ∑ _i ∈ Finset.range (k + 1), Work.Spaces.HkIntegrand α k f z θ :=
          Finset.sum_le_sum hterm
      _ = ((k : ℝ) + 1) * Work.Spaces.HkIntegrand α k f z θ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  have hMi : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k then
          (Work.Spaces.mixed j i (fun z θ => a θ * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0)
      ≤ C1 * Work.Spaces.HkIntegrand α k f z θ := by
    have hpair : ∀ i ∈ Finset.range (k + 1), ∀ j ∈ Finset.range (k + 1),
        (1 ≤ i ∧ i + j ≤ k) →
        (Work.Spaces.mixed j i (fun z θ => a θ * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ Cpair * Work.Spaces.HkIntegrand α k f z θ := by
      intro i hi j hj hc
      obtain ⟨hi1, hij⟩ := hc
      have hik : i ≤ k := by omega
      have hjk : j ≤ k := by omega
      have hexp : Work.Spaces.mixed j i (fun z θ => a θ * f z θ) z θ
          = ∑ m ∈ Finset.range (i + 1), (i.choose m : ℝ)
              * Work.FTS.EllipticEst.LopIter m a θ
              * Work.Spaces.mixed j (i - m) f z θ := by
        have hag : Work.FTS.EllipticEst.SmoothOpen (fun z θ => a θ * f z θ) :=
          smoothOpen_angMul_On hha hf
        rw [← Work.FTS.EllipticEst.SmoothOpen.DthIter_DzIter_eq_mixed hag j i hz hθIoo]
        rw [Work.FTS.EllipticEst.Blocks.DzIter_angular_mul j a f]
        rw [DthIter_angular_mul_expand_On (contDiffOn_ang_of_Q0 hha) hf i j hz hθIoo]
        exact Finset.sum_congr rfl fun m _ => by
          rw [Work.FTS.EllipticEst.SmoothOpen.DthIter_DzIter_eq_mixed hf j (i - m) hz hθIoo]
      rw [hexp]
      have hstep : (∑ m ∈ Finset.range (i + 1), (i.choose m : ℝ)
              * Work.FTS.EllipticEst.LopIter m a θ
              * Work.Spaces.mixed j (i - m) f z θ) * Work.Spaces.Wt α z θ
          = ∑ m ∈ Finset.range (i + 1), ((i.choose m : ℝ)
              * Work.FTS.EllipticEst.LopIter m a θ
              * Work.Spaces.mixed j (i - m) f z θ * Work.Spaces.Wt α z θ) := by
        rw [Finset.sum_mul]
      rw [hstep]
      have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1))
        (f := fun m => (i.choose m : ℝ) * Work.FTS.EllipticEst.LopIter m a θ
          * Work.Spaces.mixed j (i - m) f z θ * Work.Spaces.Wt α z θ)
      have hbound : ∑ m ∈ Finset.range (i + 1), ((i.choose m : ℝ)
            * Work.FTS.EllipticEst.LopIter m a θ
            * Work.Spaces.mixed j (i - m) f z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ CB * KB * Work.Spaces.HkIntegrand α k f z θ := by
        have hchoose : ∀ m ∈ Finset.range (i + 1), (i.choose m : ℝ) ^ 2 ≤ CB := by
          intro m hm
          have h1 : (i.choose m : ℝ) ≤ (2 : ℝ) ^ k := by
            have h2 : i.choose m ≤ 2 ^ k := le_trans (Nat.choose_le_two_pow i m)
              (Nat.pow_le_pow_right (by norm_num) hik)
            exact_mod_cast h2
          calc (i.choose m : ℝ) ^ 2 ≤ ((2 : ℝ) ^ k) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
            _ = CB := by rw [hCBdef]
        have hsumKB : ∑ m ∈ Finset.range (i + 1), (i.choose m : ℝ) ^ 2 * (K m + 1)
            ≤ CB * KB := by
          have hstep1 : ∑ m ∈ Finset.range (i + 1), (i.choose m : ℝ) ^ 2 * (K m + 1)
              ≤ ∑ m ∈ Finset.range (i + 1), CB * (K m + 1) := by
            refine Finset.sum_le_sum fun m hm => ?_
            exact mul_le_mul_of_nonneg_right (hchoose m hm) (by linarith [hK m])
          have hstep2 : ∑ m ∈ Finset.range (i + 1), CB * (K m + 1)
              = CB * ∑ m ∈ Finset.range (i + 1), (K m + 1) := by
            rw [Finset.mul_sum]
          have hstep3 : ∑ m ∈ Finset.range (i + 1), (K m + 1) ≤ KB := by
            rw [hKBdef]
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
            · intro m hm
              simp only [Finset.mem_range] at hm ⊢
              omega
            · intro m _ _
              linarith [hK m]
          calc _ ≤ ∑ m ∈ Finset.range (i + 1), CB * (K m + 1) := hstep1
            _ = CB * ∑ m ∈ Finset.range (i + 1), (K m + 1) := hstep2
            _ ≤ CB * KB := mul_le_mul_of_nonneg_left hstep3 hCBnonneg
        calc ∑ m ∈ Finset.range (i + 1), ((i.choose m : ℝ)
              * Work.FTS.EllipticEst.LopIter m a θ
              * Work.Spaces.mixed j (i - m) f z θ * Work.Spaces.Wt α z θ) ^ 2
            ≤ ∑ m ∈ Finset.range (i + 1), (i.choose m : ℝ) ^ 2 * (K m + 1)
                * Work.Spaces.HkIntegrand α k f z θ := by
              refine Finset.sum_le_sum fun m hm => ?_
              have hmi : m ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
              exact Work.FTS.EllipticEst.Blocks.angular_summand_sq_le_le_unit k a K ha1 hK hKb
                α f i j m hα1 hi1 hij hmi z θ hθ0 hθ1
          _ = Work.Spaces.HkIntegrand α k f z θ
                * ∑ m ∈ Finset.range (i + 1), (i.choose m : ℝ) ^ 2 * (K m + 1) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun m _ => by ring
          _ ≤ Work.Spaces.HkIntegrand α k f z θ * (CB * KB) :=
              mul_le_mul_of_nonneg_left hsumKB hHe
          _ = CB * KB * Work.Spaces.HkIntegrand α k f z θ := by ring
      have hcard : (((Finset.range (i + 1)).card : ℕ) : ℝ) = (i : ℝ) + 1 := by
        rw [Finset.card_range]
        push_cast
        ring
      calc (∑ m ∈ Finset.range (i + 1), (i.choose m : ℝ)
              * Work.FTS.EllipticEst.LopIter m a θ
              * Work.Spaces.mixed j (i - m) f z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ (((Finset.range (i + 1)).card : ℕ) : ℝ) * ∑ m ∈ Finset.range (i + 1),
              ((i.choose m : ℝ) * Work.FTS.EllipticEst.LopIter m a θ
                * Work.Spaces.mixed j (i - m) f z θ * Work.Spaces.Wt α z θ) ^ 2 := hcs
        _ ≤ (((i : ℝ) + 1)) * (CB * KB * Work.Spaces.HkIntegrand α k f z θ) := by
            rw [hcard]
            exact mul_le_mul_of_nonneg_left hbound (by positivity)
        _ ≤ ((k : ℝ) + 1) * (CB * KB * Work.Spaces.HkIntegrand α k f z θ) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            have : (i : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hik
            linarith
        _ = Cpair * Work.Spaces.HkIntegrand α k f z θ := by
            rw [hCpairdef]
            ring
    calc (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i (fun z θ => a θ * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0)
        ≤ ∑ _i ∈ Finset.range (k + 1), ∑ _j ∈ Finset.range (k + 1),
            Cpair * Work.Spaces.HkIntegrand α k f z θ := by
          refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
          by_cases hc : 1 ≤ i ∧ i + j ≤ k
          · rw [if_pos hc]
            exact hpair i hi j hj hc
          · rw [if_neg hc]
            exact mul_nonneg hCpairnonneg hHe
      _ = C1 * Work.Spaces.HkIntegrand α k f z θ := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          rw [hC1def]
          push_cast
          ring
  rw [Work.Spaces.HkIntegrand]
  refine le_trans (add_le_add hZi hMi) (le_of_eq ?_)
  ring

/-! ## The interface field -/

/-- **The `angmul` field of the repaired `N4Norm`, in the exact form of the interface.**

The interface (revision of 07:49) carries the hypothesis `Work.Spaces.SmoothInt
(fun _ θ => a θ)` — analyticity of the (constant-in-`z`) profile on the strip
`(-1,∞) × (0,π/2)`.  This is *weaker* than the hypothesis `∀ θ, ContDiffAt ℝ ⊤ a θ` of
`Work.FTS.Nonlinear.N4Fields.angmul_field_smooth`: since `uncurry (fun _ θ => a θ) = a ∘ snd`,
it gives `ContDiffAt ℝ ⊤ a θ` for every `θ ∈ Ioo 0 (π/2)`, and that is all the estimates use
(the `z`-slice conjunct of `SmoothInt` is automatic for a `z`-independent profile).

Route: reproduce the proof of `angmul_field_smooth`
(`Submission/Work/FTS/Nonlinear/N4Fields/angmul_field_smooth.lean`), replacing its hypothesis
`∀ θ, ContDiffAt ℝ ⊤ a θ`: extract `ContDiffOn ℝ smoothOrder a (Ioo 0 (π/2))` from `h.1`
(`h : SmoothInt (fun _ θ => a θ)`), feed it to the local variant of `smoothOpen_angMul` needed
for `SmoothOpen (fun z θ => a θ * f z θ)`, and use `DthIter_angular_mul_expand` (whose proof
already restricts to the open interval) for the Leibniz expansion.  The pointwise bounds
`angular_summand_sq_le_le_unit` and `HkIntegrand_ang_mul_unit_le` in that file need no
smoothness of `a` at all. -/
theorem angmul_field_smoothInt {α₂ : ℝ} (hα₂ : 0 < α₂) (hα₂1 : α₂ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ (a : ℝ → ℝ) (B : ℝ) (f : Work.FTS.Galerkin.Fn),
      0 ≤ B →
      Work.Spaces.SmoothInt (fun _ (θ : ℝ) => a θ) →
      (∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ B) →
      (∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ| ≤ B * Real.sin (2 * θ)) →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      Work.Spaces.HkMem α 4 (fun z θ => a θ * f z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => a θ * f z θ) ≤ C * B * Work.FTS.Nonlin.Xn α f := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := HkIntegrand_ang_mul_unit_le_Int 4
  refine ⟨1 + Real.sqrt C₁, by positivity, ?_⟩
  intro α hα a B f hB hInt haB haIt hf hmem
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := le_trans hα.2 hα₂1
  rcases eq_or_lt_of_le hB with hB0 | hBpos
  · -- ## `B = 0`
    have ha0 : ∀ θ ∈ Work.Spaces.Iθ, a θ = 0 := by
      intro θ hθ
      have h1 := haB θ hθ
      rw [← hB0] at h1
      exact abs_eq_zero.mp (le_antisymm h1 (abs_nonneg _))
    have hzero : ∀ z θ : ℝ, θ ∈ Work.Spaces.Iθ →
        Work.Spaces.HkIntegrand α 4 (fun z θ => a θ * f z θ) z θ = 0 := by
      intro z θ hθ
      rw [Work.Spaces.HkIntegrand]
      have h1 : (∑ i ∈ Finset.range (4 + 1),
          (Work.Spaces.DzIter i (fun z θ => a θ * f z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        simp only [Work.FTS.EllipticEst.Blocks.DzIter_angular_mul i a f]
        simp [ha0 θ hθ]
      have h2 : (∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
          if 1 ≤ i ∧ i + j ≤ 4 then
            (Work.Spaces.mixed j i (fun z θ => a θ * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0) = 0 := by
        refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
        split_ifs with hc
        · rw [Work.Spaces.mixed]
          rw [Work.Coercivity.DzIter_eq_zero_of_forall_eq_zero
            (Work.Spaces.DthIter i (fun z θ => a θ * f z θ)) θ
            (fun z' => DthIter_angmul_eq_zero a f ha0 i hc.1 z' θ hθ) j z,
            zero_mul, sq, mul_zero]
        · rfl
      rw [h1, h2, add_zero]
    have hmem' : Work.Spaces.HkMem α 4 (fun z θ => a θ * f z θ) := by
      refine Work.FTS.LocData.HkMem_of_majorant (M := fun _ _ => (0 : ℝ)) α 4 ?_ ?_ ?_ ?_
      · have h0 : ContinuousOn (fun _ : ℝ × ℝ => (0 : ℝ)) Work.FTS.EllipticEst.Q0 :=
          continuousOn_const
        refine h0.congr ?_
        intro p hp
        exact hzero p.1 p.2 ⟨le_of_lt hp.2.1, le_of_lt hp.2.2⟩
      · intro z hz; exact integrableOn_zero
      · have hthis : (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, (fun _ _ => (0 : ℝ)) z θ)
            = fun _ => (0 : ℝ) := by
          funext z; simp
        rw [hthis]
        exact integrableOn_zero
      · intro z hz θ hθ; rw [hzero z θ hθ]
    refine ⟨hmem', ?_⟩
    have hsq : Work.Spaces.HkSq α 4 (fun z θ => a θ * f z θ) = 0 := by
      rw [Work.Spaces.HkSq]
      have hinner : ∀ z : ℝ,
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 (fun z θ => a θ * f z θ) z θ)
            = 0 := by
        intro z
        rw [MeasureTheory.integral_eq_zero_of_ae]
        exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ hθ => hzero z θ hθ)
      simp only [hinner, integral_zero]
    rw [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm, hsq, Real.sqrt_zero, ← hB0]
    simp
  · -- ## `B > 0`: rescale to `a' = a/B` and use the uniform unit bound
    set a' : ℝ → ℝ := fun θ => a θ / B with ha'def
    have hBne : B ≠ 0 := hBpos.ne'
    have ha'1 : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |a' θ| ≤ 1 := by
      intro θ hθ
      have h1 := haB θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      have h2 : |a' θ| = |a θ| / B := by
        rw [ha'def, abs_div, abs_of_pos hBpos]
      rw [h2]
      exact (div_le_one hBpos).mpr h1
    have ha'Int : Work.Spaces.SmoothInt (fun _ (θ : ℝ) => a' θ) := by
      have h := smoothInt_angDiv hInt B
      simpa only [ha'def] using h
    have ha'CD : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => a' p.2)
        Work.FTS.EllipticEst.Q0 :=
      contDiffOn_snd_of_smoothInt ha'Int
    have ha'It : ∀ m : ℕ, 1 ≤ m → m ≤ 4 → ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        (Work.FTS.EllipticEst.LopIter m a' θ) ^ 2 ≤ (Real.sin (2 * θ)) ^ 2 := by
      intro m hm1 hm4 θ hθ
      -- the `Lop`-iterate of the rescaled profile
      have hlin : ∀ θ' : ℝ,
          Work.FTS.EllipticEst.LopIter m a' θ'
            = B⁻¹ * Work.FTS.EllipticEst.LopIter m a θ' := by
        have h1 : a' = fun θ => B⁻¹ * a θ := by
          funext θ'; rw [ha'def]; field_simp
        intro θ'
        rw [h1, congrFun (Work.FTS.EllipticEst.Blocks.LopIter_const_mul B⁻¹ m a) θ']
      -- the interface hypothesis, in `Lop`-form
      have hbound : |Work.FTS.EllipticEst.LopIter m a θ| ≤ B * Real.sin (2 * θ) := by
        have h2 : Work.FTS.EllipticEst.LopIter m a θ
            = Work.Spaces.DthIter m (fun _ (θ' : ℝ) => a θ') 0 θ := by
          rw [Work.Spaces.DthIter_eq_iterate_Lop]
          rfl
        rw [h2]
        exact haIt m hm1 (by omega) θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      have hsq : (Work.FTS.EllipticEst.LopIter m a θ) ^ 2
          ≤ (B * Real.sin (2 * θ)) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hbound 2
      rw [hlin θ]
      calc (B⁻¹ * Work.FTS.EllipticEst.LopIter m a θ) ^ 2
          = B⁻¹ ^ 2 * (Work.FTS.EllipticEst.LopIter m a θ) ^ 2 := by ring
        _ ≤ B⁻¹ ^ 2 * (B * Real.sin (2 * θ)) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
        _ = (Real.sin (2 * θ)) ^ 2 := by
            field_simp
    -- the pointwise bound for the rescaled profile, on the open and then the closed quadrant
    have hopen : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        Work.Spaces.HkIntegrand α 4 (fun z θ => a' θ * f z θ) z θ
          ≤ C₁ * Work.Spaces.HkIntegrand α 4 f z θ :=
      hC₁ a' ha'1 ha'CD ha'It α f hα0 hα1 hf
    have hclosed := closed_of_interior (k := 4) (a := a') (C := C₁)
      (fun α' f' hα' hα'1 hf' => hC₁ a' ha'1 ha'CD ha'It α' f' hα' hα'1 hf') α f hα0 hα1 hf
    -- transport back to `a·f = B · (a'·f)`
    have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 (fun z θ => a θ * f z θ) z θ
          ≤ (B ^ 2 * C₁) * Work.Spaces.HkIntegrand α 4 f z θ := by
      intro z hz θ hθ
      have hrew : (fun z θ => a θ * f z θ) = fun z θ => B * (a' θ * f z θ) := by
        funext z' θ'
        have hBmul : B * (a θ' / B) = a θ' := by field_simp
        rw [ha'def]
        calc a θ' * f z' θ' = (B * (a θ' / B)) * f z' θ' := by rw [hBmul]
          _ = B * (a θ' / B * f z' θ') := by ring
      rw [hrew, Work.FTS.LocData.HkIntegrand_const_mul]
      calc B ^ 2 * Work.Spaces.HkIntegrand α 4 (fun z θ => a' θ * f z θ) z θ
          ≤ B ^ 2 * (C₁ * Work.Spaces.HkIntegrand α 4 f z θ) :=
            mul_le_mul_of_nonneg_left (hclosed z hz θ hθ) (sq_nonneg B)
        _ = (B ^ 2 * C₁) * Work.Spaces.HkIntegrand α 4 f z θ := by ring
    have hcont : ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.HkIntegrand α 4 (fun z θ => a θ * f z θ) p.1 p.2)
        Work.FTS.EllipticEst.Q0 :=
      (smoothOpen_angMul_On (contDiffOn_snd_of_smoothInt hInt) hf).continuousOn_HkIntegrand α 4
    have hmem' : Work.Spaces.HkMem α 4 (fun z θ => a θ * f z θ) := by
      refine Work.FTS.LocData.HkMem_of_majorant α 4 hcont ?_ ?_ hpt
      · intro z hz
        exact (hmem.1 z hz).const_mul (B ^ 2 * C₁)
      · have h2 := hmem.2.const_mul (B ^ 2 * C₁)
        have heq : (fun z => ∫ θ in Work.Spaces.Iθ,
              (B ^ 2 * C₁) * Work.Spaces.HkIntegrand α 4 f z θ)
            = fun z => (B ^ 2 * C₁) * ∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α 4 f z θ := by
          funext z
          rw [MeasureTheory.integral_const_mul]
        rw [heq]
        exact h2
    have hsq : Work.Spaces.HkSq α 4 (fun z θ => a θ * f z θ)
        ≤ (B ^ 2 * C₁) * Work.Spaces.HkSq α 4 f :=
      HkSq_le_of_integrand_le α 4 (B ^ 2 * C₁) hmem hpt
    refine ⟨hmem', ?_⟩
    have hsqrt : Work.Spaces.HkNorm α 4 (fun z θ => a θ * f z θ)
        ≤ (B * Real.sqrt C₁) * Work.FTS.Nonlin.Xn α f := by
      have h1 : Real.sqrt (B ^ 2 * C₁) = B * Real.sqrt C₁ := by
        rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ B ^ 2), Real.sqrt_sq_eq_abs,
          abs_of_nonneg hB]
      have h2 : Work.FTS.Nonlin.Xn α f = Real.sqrt (Work.Spaces.HkSq α 4 f) := rfl
      rw [Work.Spaces.HkNorm, h2]
      calc Real.sqrt (Work.Spaces.HkSq α 4 (fun z θ => a θ * f z θ))
          ≤ Real.sqrt ((B ^ 2 * C₁) * Work.Spaces.HkSq α 4 f) := Real.sqrt_le_sqrt hsq
        _ = Real.sqrt (B ^ 2 * C₁) * Real.sqrt (Work.Spaces.HkSq α 4 f) :=
            Real.sqrt_mul (by positivity) (Work.Spaces.HkSq α 4 f)
        _ = (B * Real.sqrt C₁) * Real.sqrt (Work.Spaces.HkSq α 4 f) := by rw [h1]
    have hXnnn : 0 ≤ Work.FTS.Nonlin.Xn α f := by
      rw [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm]
      exact Real.sqrt_nonneg _
    calc Work.FTS.Nonlin.Xn α (fun z θ => a θ * f z θ)
        ≤ (B * Real.sqrt C₁) * Work.FTS.Nonlin.Xn α f := hsqrt
      _ ≤ (1 + Real.sqrt C₁) * B * Work.FTS.Nonlin.Xn α f := by
          refine mul_le_mul_of_nonneg_right ?_ hXnnn
          nlinarith [hB, Real.sqrt_nonneg C₁]

end Work.FTS.Nonlinear.N4Fields
