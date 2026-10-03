import Mathlib
import Submission.Work.KMTAreas.A7Hi.sublatticeReproL2Band
import Submission.Commons.Analysis.Fourier.schwartz_lattice_sum_bound

/-!
# The `ℓ²`-sublattice Shannon reproduction on the quarter arc `β q ≤ 1/4`

This file proves `Work.KMTAreas.A7Hi.sublatticeReproL2Quarter`: there is a universal constant `C`
such that for every `β > 0`, `q ≥ 1` with `β q ≤ 1/4` and every `r₀ : ℤ` there is a summable
kernel `K : ℤ → ℂ` with

* `∑'_l ‖K (q * l + s)‖ ≤ C` for every `s : ℤ` (uniformly in `s`, `β`, `q`, `r₀`), and
* `G x = ∑'_m G (q * m + r₀) · K (x - (q * m + r₀))` for every `G ∈ ℓ²(ℤ)` whose Fourier
  transform vanishes off `arcSet 0 β` — the samples of `G` on the coset `qℤ + r₀` reproduce `G`.

## Relation to the `1/8` version

`Work.KMTAreas.A7Hi.sublatticeReproL2Band` proves the same statement under the *stronger*
hypothesis `β q ≤ 1/8`.  The threshold `1/4` is the correct one for the kernel of that file: its
multiplier is `χ_q(ξ) = q · ψ(2qξ)` with `ψ = 1` on `[-1/2,1/2]` and `0` off `(-1,1)`, so
`χ_q ≡ q` on `|ξ| ≤ 1/(4q)` (this is what the band hypothesis needs) while `χ_q` vanishes at all
the aliases `η - j/q`, `j ≠ 0`, `|η| ≤ β`, precisely when `β ≤ 1/(2q)` (with room to spare:
`|η - j/q| ≥ 1/q - β ≥ 3/(4q) > 1/(2q)` when `β q ≤ 1/4`).  Indeed the key identity
`srb_key_circle` of that file already carries the hypothesis `β q ≤ 1/4`.

The only step of the `1/8` proof that used the hypothesis was the call to `srb_key_circle`; we
therefore isolate the (hypothesis-free) `L²`/dominated-convergence part of the argument as
`srb_repro_of_key` and instantiate it with `srb_key_circle` at `β q ≤ 1/4`.
-/

namespace Work.KMTAreas.A7Hi

open MeasureTheory Filter
open scoped FourierTransform Topology SchwartzMap BigOperators ENNReal

noncomputable section

/-- **The `ℓ²`-reproduction from the pointwise sampling identity.**
If the sampled kernel reproduces every character `θ ↦ e^{2πi x θ}` on the frequency arc
`arcSet 0 β`, then it reproduces every `ℓ²`-function whose Fourier transform is supported there.

This is the `L²`/dominated-convergence half of the sublattice Shannon reproduction: the Fourier
coefficients of `G` are the circle integrals `G n = ∫_𝕋 𝓕G(θ) conj(e^{2πinθ}) dθ`, the defining
series is exchanged with the circle integral by dominated convergence, and the resulting
pointwise identity is exactly the hypothesis `hkey`. -/
lemma srb_repro_of_key {β : ℝ} {q : ℕ} (hq : 0 < q) (r₀ : ℤ)
    (hKsumm : Summable (fun n : ℤ => ‖srbKernel q n‖))
    (hkey : ∀ (x : ℤ) (θ : Circ),
      θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 β →
      (∑' m : ℤ, star (fourier (T := 1) (q * m + r₀) θ) * srbKernel q (x - (q * m + r₀)))
        = star (fourier (T := 1) x θ))
    (G : ℤ → ℂ) (hG : Memℓp G 2)
    (hsupp : Work.BourgainPlan.IonescuWainger.HasFreqSupport G hG
      (Work.BourgainPlan.IonescuWainger.arcSet 0 β)) (x : ℤ) :
    G x = ∑' m : ℤ, G (q * m + r₀) * srbKernel q (x - (q * m + r₀)) := by
  set μ := AddCircle.haarAddCircle (T := 1) with hμdef
  set F : Circ → ℂ := (Work.BourgainPlan.IonescuWainger.ftLp G hG : Circ → ℂ) with hFdef
  have hsupp' : ∀ᵐ θ ∂μ, θ ∉ Work.BourgainPlan.IonescuWainger.arcSet 0 β → F θ = 0 := by
    rw [hμdef, hFdef]
    exact hsupp
  have hcoeff : ∀ n : ℤ, G n = ∫ θ : Circ, F θ * star (fourier (T := 1) n θ) ∂μ := by
    intro n
    rw [hFdef, hμdef]
    exact Work.BourgainPlan.IonescuWainger.ftLp_coeff_integral hG n
  have hFmem : MemLp F 2 μ := by
    rw [hFdef, hμdef]
    exact Lp.memLp (Work.BourgainPlan.IonescuWainger.ftLp G hG)
  have hFasm : AEStronglyMeasurable F μ := hFmem.aestronglyMeasurable
  have hFint : Integrable F μ := hFmem.integrable (by norm_num)
  have hFnint : Integrable (fun θ => ‖F θ‖) μ := hFint.norm
  have hshift : Summable (fun m : ℤ => ‖srbKernel q (x - (q * m + r₀))‖) := by
    have hinj1 : Function.Injective (fun m : ℤ => (q : ℤ) * m + r₀) := by
      intro a b hab
      have h1 : (q : ℤ) * a = (q : ℤ) * b := add_right_cancel hab
      exact mul_left_cancel₀ (by exact_mod_cast hq.ne' : ((q : ℤ)) ≠ 0) h1
    have hinj2 : Function.Injective (fun y : ℤ => x - y) := by
      intro a b hab
      exact sub_right_inj.mp hab
    exact hKsumm.comp_injective (hinj2.comp hinj1)
  have hsumm_arc : ∀ θ : Circ, θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 β →
      Summable (fun m : ℤ =>
        star (fourier (T := 1) (q * m + r₀) θ) * srbKernel q (x - (q * m + r₀))) := by
    intro θ hθ
    refine Summable.of_norm_bounded hshift (fun m => ?_)
    rw [norm_mul, norm_star, Work.BourgainPlan.IonescuWainger.norm_fourier_apply', one_mul]
  have hpointwise : ∀ᵐ θ ∂μ, HasSum (fun m : ℤ =>
      F θ * star (fourier (T := 1) (q * m + r₀) θ) * srbKernel q (x - (q * m + r₀)))
      (F θ * star (fourier (T := 1) x θ)) := by
    filter_upwards [hsupp'] with θ hθ
    by_cases hmem : θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 β
    · have hk := hkey x θ hmem
      have hscaled : Summable (fun m : ℤ =>
          F θ * star (fourier (T := 1) (q * m + r₀) θ) * srbKernel q (x - (q * m + r₀))) := by
        rw [show (fun m : ℤ => F θ * star (fourier (T := 1) (q * m + r₀) θ)
              * srbKernel q (x - (q * m + r₀)))
            = fun m : ℤ => F θ * (star (fourier (T := 1) (q * m + r₀) θ)
              * srbKernel q (x - (q * m + r₀))) from funext fun m => (mul_assoc _ _ _)]
        exact (hsumm_arc θ hmem).mul_left (F θ)
      have htsum : (∑' m : ℤ, F θ * star (fourier (T := 1) (q * m + r₀) θ)
          * srbKernel q (x - (q * m + r₀))) = F θ * star (fourier (T := 1) x θ) := by
        rw [show (fun m : ℤ => F θ * star (fourier (T := 1) (q * m + r₀) θ)
              * srbKernel q (x - (q * m + r₀)))
            = fun m : ℤ => F θ * (star (fourier (T := 1) (q * m + r₀) θ)
              * srbKernel q (x - (q * m + r₀))) from funext fun m => (mul_assoc _ _ _)]
        rw [tsum_mul_left, hk]
      rw [← htsum]
      exact hscaled.hasSum
    · rw [hθ hmem]
      simp only [zero_mul]
      exact hasSum_zero
  have hmain : HasSum (fun m : ℤ => ∫ θ, F θ * star (fourier (T := 1) (q * m + r₀) θ)
        * srbKernel q (x - (q * m + r₀)) ∂μ)
      (∫ θ, F θ * star (fourier (T := 1) x θ) ∂μ) :=
    hasSum_integral_of_dominated_convergence
      (fun (m : ℤ) (θ : Circ) => ‖F θ‖ * ‖srbKernel q (x - (q * m + r₀))‖)
      (fun m => ((hFasm.mul ((continuous_star.comp
        (fourier (T := 1) (q * m + r₀)).continuous)).aestronglyMeasurable)).mul_const _)
      (fun m => Filter.Eventually.of_forall (fun θ => by
        rw [norm_mul, norm_mul, norm_star,
          Work.BourgainPlan.IonescuWainger.norm_fourier_apply', mul_one]))
      (Filter.Eventually.of_forall (fun θ => hshift.mul_left ‖F θ‖))
      (by
        have h : (fun θ : Circ => ∑' m : ℤ, ‖F θ‖ * ‖srbKernel q (x - (q * m + r₀))‖)
            = fun θ => ‖F θ‖ * (∑' m : ℤ, ‖srbKernel q (x - (q * m + r₀))‖) := by
          funext θ; rw [tsum_mul_left]
        rw [h]
        exact hFnint.mul_const _)
      hpointwise
  have hgoal : (∑' m : ℤ, G (q * m + r₀) * srbKernel q (x - (q * m + r₀))) = G x := by
    rw [hcoeff x, ← hmain.tsum_eq]
    apply tsum_congr
    intro m
    rw [hcoeff (q * m + r₀), integral_mul_const]
  rw [hgoal]

theorem sublatticeReproL2Quarter :
    ∃ C : ℝ, 0 < C ∧
      ∀ (β : ℝ) (hβ : 0 < β) (q : ℕ) (hq : 0 < q) (hβq : β * (q : ℝ) ≤ 1 / 4) (r₀ : ℤ),
        ∃ K : ℤ → ℂ, Summable (fun m : ℤ => ‖K m‖) ∧
          (∀ s : ℤ, (∑' l : ℤ, ‖K (q * l + s)‖) ≤ C) ∧
          ∀ (G : ℤ → ℂ) (hG : Memℓp G 2)
            (hsupp : Work.BourgainPlan.IonescuWainger.HasFreqSupport G hG
              (Work.BourgainPlan.IonescuWainger.arcSet 0 β)) (x : ℤ),
            G x = ∑' m : ℤ, G (q * m + r₀) * K (x - (q * m + r₀)) := by
  obtain ⟨S, hSpos, hScoset⟩ := srb_coset_bound
  obtain ⟨C₂, hC₂, hC₂bd⟩ := Work.KMTAreas.A7.shannon_schwartz_bound (𝓕⁻ srbPsi)
  have hC2pos : 0 ≤ C₂ / 2 := by linarith
  refine ⟨S * (C₂ / 2) + 1, by nlinarith [hSpos, hC2pos], ?_⟩
  intro β hβ q hq hβq r₀
  have hdecay := srbKernel_decay q hq hC₂bd
  obtain ⟨hKsumm, hKcosetall⟩ := hScoset (C₂ / 2) hC2pos q hq (srbKernel q) hdecay
  refine ⟨srbKernel q, hKsumm, fun s => ?_, ?_⟩
  · have := (hKcosetall s).2
    linarith
  · intro G hG hsupp x
    exact srb_repro_of_key (β := β) hq r₀ hKsumm
      (fun x θ hθ => srb_key_circle (β := β) (q := q) hq hβq r₀ x hθ) G hG hsupp x

end

end Work.KMTAreas.A7Hi
