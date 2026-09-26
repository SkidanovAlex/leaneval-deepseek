import Mathlib
import Submission.Work.Asymptotics.HalfFunnel.lowBad_Kaxis_bound_aux
import Submission.Work.Asymptotics.differentiableAt_Kfun_tau

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section

namespace Work.LayerCont

open UpperHalfPlane MeasureTheory Filter
open scoped Topology

/-- **The `d = 8` coincidence value.**  For `d = 8` the scalar of `UpsilonPlus` carries the factor
`(j τ - j z)`, so at a coincidence `j τ = j z` the whole matrix vanishes (Lean's `0⁻¹ = 0`), and
with it `KPlus`; the same holds for `UpsilonMinus` and `KMinus`.  Hence Lean's value of
`Kfun ℓ 8 τ z` at a coincidence is `0` — which is what makes the closure transfer of
`Work.Asymptotics.HalfFunnel.lowBad_Kaxis_bound_aux` easy in eight dimensions.  (In twenty-four
dimensions the factor `j τ - j z` sits *inside* the middle matrix, and the value is a nonzero
definitional object — see the entry `The transfer, sharpened` of `Submission/ROADMAP.md`.) -/
theorem UpsilonPlus_eight_eq_zero {τ z : UpperHalfPlane}
    (h : Work.Kernels.jInvariantFun τ = Work.Kernels.jInvariantFun z) :
    Work.Kernels.UpsilonPlus 8 τ z = 0 := by
  simp only [Work.Kernels.UpsilonPlus, h, sub_self]
  split_ifs <;> simp only [mul_zero, inv_zero, zero_smul]

theorem UpsilonMinus_eight_eq_zero {τ z : UpperHalfPlane}
    (h : Work.Kernels.jInvariantFun τ = Work.Kernels.jInvariantFun z) :
    Work.Kernels.UpsilonMinus 8 τ z = 0 := by
  simp only [Work.Kernels.UpsilonMinus, h, sub_self]
  split_ifs <;> simp only [mul_zero, inv_zero, zero_smul]

/-- **`Kaxis` vanishes at coincidences in eight dimensions.** -/
theorem Kaxis_eight_eq_zero (ℓ : Work.Kernels.LogLambdaData) {τ z : UpperHalfPlane} (t : ℝ)
    (ht : 0 < t) (hz : z = Work.Kernels.imagAxis t ht)
    (h : Work.Kernels.jInvariantFun τ = Work.Kernels.jInvariantFun z) :
    Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 8) τ t = 0 := by
  subst hz
  rw [Work.Kernels.Kaxis, dif_pos ht]
  have hU : ∀ i j : Fin 3, Work.Kernels.UpsilonPlus 8 τ (Work.Kernels.imagAxis t ht) i j = 0 :=
    fun i j => by
      have := congr_fun (congr_fun (UpsilonPlus_eight_eq_zero h) i) j
      simpa using this
  have hV : ∀ i j : Fin 3, Work.Kernels.UpsilonMinus 8 τ (Work.Kernels.imagAxis t ht) i j = 0 :=
    fun i j => by
      have := congr_fun (congr_fun (UpsilonMinus_eight_eq_zero h) i) j
      simpa using this
  have hP : Work.Kernels.KPlus 8 τ (Work.Kernels.imagAxis t ht) = 0 := by
    rw [Work.Kernels.KPlus]
    refine Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => ?_))
    rw [hU i j]; ring
  have hM : Work.Kernels.KMinus ℓ 8 τ (Work.Kernels.imagAxis t ht) = 0 := by
    rw [Work.Kernels.KMinus]
    refine Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => ?_))
    rw [hV i j]; ring
  rw [Work.Kernels.Kfun, hP, hM]
  norm_num

/-- **The closure transfer, eight dimensions.**  The guarded bound of
`Work.Asymptotics.HalfFunnel.lowBad_Kaxis_bound_aux` on `lowBadSet` passes to the closure, because
at the boundary the map `τ ↦ Kaxis (Kfun ℓ 8) τ t` is continuous away from the (guard-excluded)
translate pole and takes the value `0` at the remaining coincidences. -/
theorem LowBadClosureEight (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      τ ∈ closure Work.Asymptotics.HalfFunnel.lowBadSet → 0 < t →
      t ≤ Work.Asymptotics.HalfFunnel.lowT → (1 / 8 : ℝ) < |t - τ.im| →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 8) τ t‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := Work.Asymptotics.HalfFunnel.lowBad_Kaxis_bound_aux ℓ 8 (Or.inl rfl)
  refine ⟨C, hC, fun τ₀ t hτ₀ ht htT hsep => ?_⟩
  by_cases hJ : Work.Kernels.jInvariantFun τ₀ = Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)
  · rw [Kaxis_eight_eq_zero ℓ t ht rfl hJ, norm_zero]
    exact hC
  · have hdiff : MDifferentiableAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (fun τ : UpperHalfPlane => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 8) τ t) τ₀ := by
      rw [UpperHalfPlane.mdifferentiableAt_iff]
      have hfun : ((fun τ : UpperHalfPlane => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 8) τ t)
            ∘ (UpperHalfPlane.ofComplex : ℂ → UpperHalfPlane))
          = fun w : ℂ => Work.Kernels.Kfun ℓ 8 (UpperHalfPlane.ofComplex w)
              (Work.Kernels.imagAxis t ht) := by
        funext w
        simp only [Function.comp_apply]
        rw [Work.Kernels.Kaxis, dif_pos ht]
      rw [hfun]
      exact Work.Asymptotics.differentiableAt_Kfun_tau (ℓ := ℓ) (d := 8) (Or.inl rfl)
        (τ := τ₀) (z := Work.Kernels.imagAxis t ht) hJ
    have hcont : ContinuousAt
        (fun τ : UpperHalfPlane => ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 8) τ t‖) τ₀ :=
      (continuous_norm.continuousAt).comp hdiff.continuousAt
    haveI : NeBot (𝓝[Work.Asymptotics.HalfFunnel.lowBadSet] τ₀) :=
      mem_closure_iff_nhdsWithin_neBot.mp hτ₀
    have htend : Tendsto (fun τ : UpperHalfPlane =>
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 8) τ t‖)
        (𝓝[Work.Asymptotics.HalfFunnel.lowBadSet] τ₀)
        (𝓝 ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 8) τ₀ t‖) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    have himcont : Continuous (fun τ : UpperHalfPlane => |t - τ.im|) := by fun_prop
    have hopen : IsOpen {τ : UpperHalfPlane | (1 / 8 : ℝ) < |t - τ.im|} :=
      isOpen_lt continuous_const himcont
    have hev : ∀ᶠ τ in 𝓝 τ₀, (1 / 8 : ℝ) < |t - τ.im| := hopen.mem_nhds hsep
    have hfreq : ∀ᶠ τ in 𝓝[Work.Asymptotics.HalfFunnel.lowBadSet] τ₀,
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 8) τ t‖ ≤ C := by
      filter_upwards [hev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with τ hsep' hτ
      exact hb τ t hτ ht htT hsep'.le
    exact le_of_tendsto htend hfreq

end Work.LayerCont
