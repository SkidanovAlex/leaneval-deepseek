import Mathlib
import Submission.Work.CNum.C2_clockwise
import Submission.Work.CNum.C2_mem
import Submission.Work.CNum.AlpBound
import Submission.Work.CPsi.psiC_continuous

/-!
# `Work.CNum.C2VofClosed`

`C2_ratio_eq` and `C2_Vof_explicit` give the identity

  `Vof θ = -exp (I · C2Psi (θ/2))`

on the **open** cusp arc `θ ∈ (α, 2π - α)`.  Here we extend it to the **closed** arc
`θ ∈ [α, 2π - α]` (`α = alpR`).

The extension is by continuity.  Both sides are continuous at the two endpoints:

* the right hand side is continuous everywhere, `C2Psi t = t - π/2 + arcsin (cos t / C)`
  being a composition of continuous functions evaluated at `t = θ/2`;
* for `Vof` the only delicate point is `√(Ra (e^{iθ}))`.  At the two endpoints one has
  `Ra (e^{iθ}) = 0` (this is `Ra_exp` together with `cos α = γ`, `cos (2π - α) = γ`),
  and `Complex.sqrt` is continuous at `0` (`Complex.continuousAt_sqrt`), so `Vof`
  is continuous there as a composition.

Finally, on the closed arc the endpoint `α` is in the closure of the open arc `(α, 2π-α)`,
which is a neighbourhood of `α` inside `𝓝[>] α`; comparing one sided limits of the two
(continuous) sides gives the value at the endpoints.

The constants are `c = 23/10`, `γ = gamR = 8c²/(1+c²)²` and `α = alpR = arccos γ`.
-/

namespace Work.CNum

open Complex Filter
open scoped Topology

/-- `Ra (e^{iα}) = 0`: the radicand vanishes at the left end of the cusp arc. -/
lemma Ra_exp_alpR : Ra (Complex.exp (Complex.I * (alpR : ℂ))) = 0 := by
  rw [Ra_exp, cos_alpR]
  simp

/-- `Ra (e^{i(2π-α)}) = 0`: the radicand vanishes at the right end of the cusp arc. -/
lemma Ra_exp_two_pi_sub_alpR :
    Ra (Complex.exp (Complex.I * ((2 * Real.pi - alpR : ℝ) : ℂ))) = 0 := by
  rw [Ra_exp, Real.cos_two_pi_sub, cos_alpR]
  simp

/-- `Vof` is continuous at any point `θ₀` where the radicand `Ra (e^{iθ₀})` vanishes. -/
lemma continuousAt_Vof_of_Ra_exp_eq_zero {θ₀ : ℝ}
    (hθ₀ : Ra (Complex.exp (Complex.I * (θ₀ : ℂ))) = 0) : ContinuousAt Vof θ₀ := by
  have hsqrt0 : ContinuousAt Complex.sqrt (Ra (Complex.exp (Complex.I * (θ₀ : ℂ)))) :=
    Complex.continuousAt_sqrt (Or.inl (by rw [hθ₀]; simp))
  have hRa : ContinuousAt (fun z : ℂ => Ra z) (Complex.exp (Complex.I * (θ₀ : ℂ))) :=
    (show Continuous (fun z : ℂ => Ra z) from by unfold Ra; fun_prop).continuousAt
  have hexp : ContinuousAt (fun θ : ℝ => Complex.exp (Complex.I * (θ : ℂ))) θ₀ :=
    (show Continuous (fun θ : ℝ => Complex.exp (Complex.I * (θ : ℂ))) from
      Complex.continuous_exp.comp (Complex.continuous_ofReal.const_mul Complex.I)).continuousAt
  have hA : ContinuousAt (fun z : ℂ => Complex.sqrt (Ra z))
      (Complex.exp (Complex.I * (θ₀ : ℂ))) :=
    ContinuousAt.comp (f := fun z : ℂ => Ra z) hsqrt0 hRa
  have hcomp : ContinuousAt (fun θ : ℝ => Complex.sqrt (Ra (Complex.exp (Complex.I * (θ : ℂ)))))
      θ₀ :=
    ContinuousAt.comp (f := fun θ : ℝ => Complex.exp (Complex.I * (θ : ℂ))) hA hexp
  have hW : ContinuousAt (fun θ : ℝ => Wfun (Complex.exp (Complex.I * (θ : ℂ)))) θ₀ := by
    change ContinuousAt (fun θ : ℝ =>
      -(((1 + (cR : ℂ) ^ 2) * (Complex.exp (Complex.I * (θ : ℂ)) - 1) +
          Complex.sqrt (Ra (Complex.exp (Complex.I * (θ : ℂ))))) / (dR : ℂ))) θ₀
    exact ((((hexp.sub continuousAt_const).const_mul (1 + (cR : ℂ) ^ 2)).add hcomp).div_const
      (dR : ℂ)).neg
  change ContinuousAt (fun θ : ℝ => ((3 / 4 : ℂ) * Wfun (Complex.exp (Complex.I * (θ : ℂ))) -
      (cenC2 : ℂ)) / (Real.sqrt rho2sq : ℂ)) θ₀
  exact ((hW.const_mul (3 / 4 : ℂ)).sub
    (continuousAt_const : ContinuousAt (fun _ : ℝ => (cenC2 : ℂ)) θ₀)).div_const _

/-- Two continuous functions `ℝ → ℂ` agreeing on `(a,b)` agree at the left endpoint `a`. -/
lemma eq_of_eqOn_Ioo_of_continuousAt_left {f g : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousAt f a) (hg : ContinuousAt g a) (h : Set.EqOn f g (Set.Ioo a b)) :
    f a = g a := by
  have hmem : Set.Ioo a b ∈ 𝓝[Set.Ioi a] a := Ioo_mem_nhdsGT hab
  have hev : f =ᶠ[𝓝[Set.Ioi a] a] g := Filter.eventually_of_mem hmem h
  have ht_f : Filter.Tendsto f (𝓝[Set.Ioi a] a) (𝓝 (f a)) :=
    hf.tendsto.mono_left nhdsWithin_le_nhds
  have ht_g : Filter.Tendsto g (𝓝[Set.Ioi a] a) (𝓝 (g a)) :=
    hg.tendsto.mono_left nhdsWithin_le_nhds
  exact (tendsto_nhds_unique ht_g (Filter.Tendsto.congr' hev ht_f)).symm

/-- Two continuous functions `ℝ → ℂ` agreeing on `(a,b)` agree at the right endpoint `b`. -/
lemma eq_of_eqOn_Ioo_of_continuousAt_right {f g : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousAt f b) (hg : ContinuousAt g b) (h : Set.EqOn f g (Set.Ioo a b)) :
    f b = g b := by
  have hmem : Set.Ioo a b ∈ 𝓝[Set.Iio b] b := Ioo_mem_nhdsLT hab
  have hev : f =ᶠ[𝓝[Set.Iio b] b] g := Filter.eventually_of_mem hmem h
  have ht_f : Filter.Tendsto f (𝓝[Set.Iio b] b) (𝓝 (f b)) :=
    hf.tendsto.mono_left nhdsWithin_le_nhds
  have ht_g : Filter.Tendsto g (𝓝[Set.Iio b] b) (𝓝 (g b)) :=
    hg.tendsto.mono_left nhdsWithin_le_nhds
  exact (tendsto_nhds_unique ht_g (Filter.Tendsto.congr' hev ht_f)).symm

theorem C2VofClosed {θ : ℝ} (h1 : Work.CNum.alpR ≤ θ)
    (h2 : θ ≤ 2 * Real.pi - Work.CNum.alpR) :
    Work.CNum.Vof θ = -Complex.exp (Complex.I * (Work.CNum.C2Psi (θ / 2) : ℂ)) := by
  -- the cusp arc is nonempty
  have hlt : alpR < 2 * Real.pi - alpR := by
    have hb := AlpBound
    have hp := Real.pi_gt_d4
    linarith [hb.1, hb.2, hp]
  -- the two sides of the identity
  set G : ℝ → ℂ := fun θ => -Complex.exp (Complex.I * (C2Psi (θ / 2) : ℂ)) with hG
  have hcontG : Continuous G := by
    have hpsi : Continuous C2Psi := by
      unfold C2Psi
      exact (continuous_id.sub continuous_const).add
        (Real.continuous_arcsin.comp (Real.continuous_cos.div_const _))
    have hpsi2 : Continuous (fun θ : ℝ => C2Psi (θ / 2)) := hpsi.comp (continuous_id.div_const 2)
    have h3 : Continuous (fun θ : ℝ => (C2Psi (θ / 2) : ℂ)) := Complex.continuous_ofReal.comp hpsi2
    exact (Complex.continuous_exp.comp (h3.const_mul Complex.I)).neg
  -- the identity holds on the open arc
  have hEqOn : Set.EqOn Vof G (Set.Ioo alpR (2 * Real.pi - alpR)) := by
    intro θ hθ
    rw [hG]
    rw [C2_Vof_explicit hθ, C2_ratio_eq hθ]
  -- conclude at the endpoints by one-sided limits
  rcases lt_or_eq_of_le h1 with h1' | h1'
  · rcases lt_or_eq_of_le h2 with h2' | h2'
    · exact hEqOn ⟨h1', h2'⟩
    · rw [h2']
      exact eq_of_eqOn_Ioo_of_continuousAt_right (f := Vof) (g := G) hlt
        (continuousAt_Vof_of_Ra_exp_eq_zero Ra_exp_two_pi_sub_alpR) hcontG.continuousAt hEqOn
  · rw [← h1']
    exact eq_of_eqOn_Ioo_of_continuousAt_left (f := Vof) (g := G) hlt
      (continuousAt_Vof_of_Ra_exp_eq_zero Ra_exp_alpR) hcontG.continuousAt hEqOn

end Work.CNum
