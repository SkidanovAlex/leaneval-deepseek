import Mathlib
import Submission.CDTPlan.Interfaces
import Submission.Work.CPhi.phiC_analytic
import Submission.Work.CPull.defs
import Submission.Work.CPull.phiC_K_data
import Submission.Work.CPull.linear_ode_extend
import Submission.Work.CPull.evp_B2_ode

/-!
# Area CPull — the meromorphic pullback of `B₂` along `φ_C`

`Submission.CDTPlan.PullbackMero B₂ φ_C`: the pullback germ `z ↦ Σₙ cₙ φ_C(z)ⁿ`
(`cₙ = coeff n B₂`, `B₂ = Σ_{n≥2} 2(n-2)!n!/(2n)! yⁿ`, radius of convergence `4`) extends to a
holomorphic function of `z` on the unit disc.

The proof is a single continuation argument, using the two structural facts on
`φ = φ_C = h ∘ ψ_C`:

* `φ - 4 = K²` for a holomorphic `K` on the disc (`K = k ∘ ψ_C`, `k² = h - 4` from
  `HauptFacts`), with `K 0 = ±2i ≠ 0`.  This is exactly the statement that `φ` has *even
  ramification* over the orbifold point `y = 4`, where `B₂` has its (order two) branch point.
* `φ⁻¹(0) = {0}` and `φ'(0) ≠ 0`.

On the small ball `|z| < r` where `|φ| ≤ 3/4 < 4` the pullback germ is `u = U ∘ φ` with
`U = Σ cₙ yⁿ` the sum of the `B₂`-series, which satisfies the ODE `y(4-y)U' = (2-y)U + y²`.
Pushing this through the chain rule gives for `u`:
`φ(4-φ) u' = (2-φ)φ' u + φ² φ'`, i.e. `u' = A u + B` with `A = K'/K + KK'/φ`, `B = -2φK'/K`,
which has poles exactly at the preimages of `4` (the zeros of `K`).

The substitution `V := (u - 2φ)/K` removes these poles: a short computation gives

  `V' = (K K'/φ) · V - 2 K'`,

an ODE whose coefficients are holomorphic on the *punctured* unit disc (since `φ ≠ 0` off `0`),
while `V` is holomorphic on `|z| < r`.  Hence `V` extends holomorphically to the whole disc
(`Submission.CDTPlan.OdeContinuation`, area `Work.OdeCont`), and

  `N := 2φ + K·V`

is holomorphic on the disc and agrees with the pullback germ `u` near `0`.
-/

namespace Work.CPull

open Complex Metric Filter
open scoped Topology

/-- The algebraic identity underlying the ODE for `V = (u - 2φ)/K`: writing `p = φ`, `k = K`,
`p' = φ' = 2 K K'` (from `φ - 4 = K²`) and `p(4-p)u' = ((2-p)u + p²)p'`, the derivative
`V' = ((u'-2p')k - (u-2p)k')/k²` equals `(k k'/p)·((u-2p)/k) - 2k'`. -/
private lemma v_ode_alg (u u' p p' k k' : ℂ) (hk : k ≠ 0) (hp : p ≠ 0)
    (hk2 : k ^ 2 = p - 4) (hp' : p' = 2 * k * k')
    (hu' : u' = -p' * ((2 - p) * u + p ^ 2) / (p * k ^ 2)) :
    (u' - 2 * p') * k - (u - 2 * p) * k' =
      ((k * k' / p) * ((u - 2 * p) / k) - 2 * k') * k ^ 2 := by
  have hp4 : p = k ^ 2 + 4 := by linear_combination -hk2
  subst hp4
  subst hp'
  subst hu'
  field_simp
  ring

theorem pullbackMero_B2 (hM : Submission.CDTPlan.HauptFacts) (hP : Submission.CDTPlan.PsiCFacts) :
    Submission.CDTPlan.PullbackMero Submission.CDTPlan.B2 Submission.CDTPlan.phiC := by
  -- ## the two functional hypotheses, unpacked
  obtain ⟨K, r₀, hr₀pos, hr₀le1, hKdiff, hKdiff', hK0, hKsq, hφzero, hφ0, hφle, hKne⟩ :=
    (phiC_K_data hM hP)
  obtain ⟨hUdiff, hUsum, hUode⟩ := evp_B2_ode
  have hφdiff : DifferentiableOn ℂ Submission.CDTPlan.phiC (Metric.ball (0 : ℂ) 1) :=
    Work.CPhi.phiC_differentiableOn hM hP
  -- ## local abbreviations
  let φ : ℂ → ℂ := Submission.CDTPlan.phiC
  let U : ℂ → ℂ := fun y : ℂ => evp Submission.CDTPlan.B2 y
  let u : ℂ → ℂ := fun z => U (φ z)
  let r : ℝ := r₀ / 2
  have hφdef : φ = Submission.CDTPlan.phiC := rfl
  have hUdef : U = fun y : ℂ => evp Submission.CDTPlan.B2 y := rfl
  have hudef : u = fun z => U (φ z) := rfl
  have hrdef : r = r₀ / 2 := rfl
  have hrpos : 0 < r := by rw [hrdef]; linarith
  have hrlt1 : r < 1 := by rw [hrdef]; linarith
  have hrle : r ≤ r₀ := by rw [hrdef]; linarith
  have hφd : DifferentiableOn ℂ φ (Metric.ball (0 : ℂ) r) :=
    hφdiff.mono (Metric.ball_subset_ball (le_of_lt hrlt1))
  have hKd : DifferentiableOn ℂ K (Metric.ball (0 : ℂ) r) :=
    hKdiff.mono (Metric.ball_subset_ball (le_of_lt hrlt1))
  have hle' : ∀ z ∈ Metric.ball (0 : ℂ) r, ‖φ z‖ ≤ 3 / 4 :=
    fun z hz => hφle z (Metric.ball_subset_ball hrle hz)
  have hne' : ∀ z ∈ Metric.ball (0 : ℂ) r, K z ≠ 0 :=
    fun z hz => hKne z (Metric.ball_subset_ball hrle hz)
  have hmem' : ∀ z ∈ Metric.ball (0 : ℂ) r, φ z ∈ Metric.ball (0 : ℂ) 4 := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt (hle' z hz) (by norm_num)
  -- ## `u = U ∘ φ` is holomorphic on `|z| < r`
  have hud : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) r) := by
    have h := hUdiff.comp hφd (fun z hz => hmem' z hz)
    have hfun : u = (fun y : ℂ => evp Submission.CDTPlan.B2 y) ∘ φ := by
      funext z; rfl
    rw [hfun]
    exact h
  -- ## `V = (u - 2φ)/K`
  let V : ℂ → ℂ := fun z => (u z - 2 * φ z) / K z
  have hVdef : V = fun z => (u z - 2 * φ z) / K z := rfl
  have hVd : DifferentiableOn ℂ V (Metric.ball (0 : ℂ) r) := by
    have h2 : DifferentiableOn ℂ (fun z => (u z - 2 * φ z) / K z) (Metric.ball (0 : ℂ) r) :=
      (hud.sub (hφd.const_mul 2)).div hKd hne'
    rw [hVdef]
    exact h2
  -- ## the ODE solved by `V`
  have hVode : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < r →
      HasDerivAt V ((K z * deriv K z / φ z) * V z + (-2 * deriv K z)) z := by
    intro z hzpos hzr
    have hz1 : z ∈ Metric.ball (0 : ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right]; linarith
    have hzr' : z ∈ Metric.ball (0 : ℂ) r := by
      rw [Metric.mem_ball, dist_zero_right]; exact hzr
    have hKz : K z ≠ 0 := hne' z hzr'
    have hKd1 : DifferentiableAt ℂ K z := hKdiff.differentiableAt (Metric.isOpen_ball.mem_nhds hz1)
    have hKat : HasDerivAt K (deriv K z) z := hKd1.hasDerivAt
    have hφz : φ z ≠ 0 := by
      intro h0
      have hz0 : z = 0 := hφzero z hz1 (by simpa [hφdef] using h0)
      rw [hz0] at hzpos
      simp at hzpos
    have hk2 : (K z) ^ 2 = φ z - 4 := by
      have h : Submission.CDTPlan.phiC z - 4 = K z ^ 2 := hKsq z hz1
      rw [hφdef]
      exact h.symm
    have h4φ : 4 - φ z = -(K z) ^ 2 := by rw [hk2]; ring
    have hp' : deriv φ z = 2 * K z * deriv K z := by
      have heq : φ =ᶠ[𝓝 z] fun w => 4 + K w * K w := by
        filter_upwards [Metric.isOpen_ball.mem_nhds hz1] with w hw
        have h : Submission.CDTPlan.phiC w - 4 = K w ^ 2 := hKsq w hw
        show Submission.CDTPlan.phiC w = 4 + K w * K w
        linear_combination h
      have hdd : HasDerivAt (fun w : ℂ => K w * K w) (deriv K z * K z + K z * deriv K z) z :=
        hKat.mul hKat
      have hd2 : HasDerivAt (fun w : ℂ => 4 + K w * K w) (deriv K z * K z + K z * deriv K z) z :=
        hdd.const_add 4
      have hd3 : HasDerivAt φ (deriv K z * K z + K z * deriv K z) z :=
        hd2.congr_of_eventuallyEq heq
      rw [hd3.deriv]
      ring
    have hφmem : φ z ∈ Metric.ball (0 : ℂ) 4 := hmem' z hzr'
    have hUat : HasDerivAt U (deriv U (φ z)) (φ z) :=
      (hUdiff.differentiableAt (Metric.isOpen_ball.mem_nhds hφmem)).hasDerivAt
    have hφat : HasDerivAt φ (deriv φ z) z :=
      (hφd.differentiableAt (Metric.isOpen_ball.mem_nhds hzr')).hasDerivAt
    have huat : HasDerivAt u (deriv U (φ z) * deriv φ z) z := by
      have h := hUat.comp z hφat
      have hfun : u = U ∘ φ := by funext w; rfl
      rw [hfun]
      exact h
    -- the pulled back `B₂`-ODE in product form
    have hprod : φ z * (4 - φ z) * (deriv U (φ z) * deriv φ z)
        = ((2 - φ z) * U (φ z) + (φ z) ^ 2) * deriv φ z := by
      have h : φ z * (4 - φ z) * deriv U (φ z) = (2 - φ z) * U (φ z) + (φ z) ^ 2 :=
        hUode (φ z) hφmem
      linear_combination h * deriv φ z
    have hprod' : φ z * (-(K z) ^ 2) * (deriv U (φ z) * deriv φ z)
        = ((2 - φ z) * U (φ z) + (φ z) ^ 2) * deriv φ z := by
      rw [← h4φ]; exact hprod
    have hu' : deriv U (φ z) * deriv φ z
        = -deriv φ z * ((2 - φ z) * U (φ z) + (φ z) ^ 2) / (φ z * (K z) ^ 2) := by
      rw [eq_div_iff (mul_ne_zero hφz (pow_ne_zero 2 hKz))]
      linear_combination -hprod'
    -- the quotient rule for `V = (u - 2φ)/K`
    have hnum : HasDerivAt (fun w : ℂ => u w - 2 * φ w)
        (deriv U (φ z) * deriv φ z - 2 * deriv φ z) z := by
      have h := huat.sub (hφat.const_mul 2)
      have hfun : (fun w : ℂ => u w - 2 * φ w) = u - fun y => 2 * φ y := by
        funext w; rfl
      rw [hfun]
      exact h
    have hdiv : HasDerivAt (fun w : ℂ => (u w - 2 * φ w) / K w)
        (((deriv U (φ z) * deriv φ z - 2 * deriv φ z) * K z - (u z - 2 * φ z) * deriv K z)
          / (K z) ^ 2) z := hnum.div hKat hKz
    have hgoal : ((deriv U (φ z) * deriv φ z - 2 * deriv φ z) * K z
            - (u z - 2 * φ z) * deriv K z) / (K z) ^ 2
        = (K z * deriv K z / φ z) * ((u z - 2 * φ z) / K z) + (-2 * deriv K z) := by
      rw [div_eq_iff (pow_ne_zero 2 hKz)]
      have key := v_ode_alg (u := U (φ z)) (u' := deriv U (φ z) * deriv φ z) (p := φ z)
        (p' := deriv φ z) (k := K z) (k' := deriv K z) hKz hφz hk2 hp' hu'
      rw [key]
      ring
    rw [hVdef]
    exact hdiv.congr_deriv hgoal
  -- ## continuation: `V` extends holomorphically to the whole disc
  have ha : DifferentiableOn ℂ (fun z => K z * deriv K z / φ z)
      {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < 1} := by
    have h1 : DifferentiableOn ℂ (fun z => K z * deriv K z) {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < 1} :=
      (hKdiff.mul hKdiff').mono (fun z hz => by
        rw [Metric.mem_ball, dist_zero_right]; exact hz.2)
    have h2 : DifferentiableOn ℂ φ {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < 1} :=
      hφdiff.mono (fun z hz => by rw [Metric.mem_ball, dist_zero_right]; exact hz.2)
    have hne : ∀ z ∈ {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < 1}, φ z ≠ 0 := by
      intro z hz h0
      have hz1 : z ∈ Metric.ball (0 : ℂ) 1 := by
        rw [Metric.mem_ball, dist_zero_right]; exact hz.2
      have hz0 : z = 0 := hφzero z hz1 (by simpa [hφdef] using h0)
      rw [hz0] at hz
      simp at hz
    have h3 : DifferentiableOn ℂ ((fun z => K z * deriv K z) / φ)
        {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < 1} := h1.div h2 hne
    have h4 : ((fun z => K z * deriv K z) / φ) = fun z => K z * deriv K z / φ z := by
      funext z; rfl
    rw [h4] at h3
    exact h3
  have hb : DifferentiableOn ℂ (fun z => -2 * deriv K z) {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < 1} :=
    (hKdiff'.const_mul (-2)).mono (fun z hz => by
      rw [Metric.mem_ball, dist_zero_right]; exact hz.2)
  obtain ⟨Y, hYdiff, hYeq⟩ :=
    linear_ode_extend (a := fun z => K z * deriv K z / φ z) (b := fun z => -2 * deriv K z)
      (V := V) (r := r) hrpos hrlt1 ha hb hVd hVode
  -- ## assemble
  refine ⟨1, fun z => 2 * φ z + K z * Y z, ?_, ?_, ?_⟩
  · simp
  · have h1 : DifferentiableOn ℂ (fun z => 2 * φ z) (Metric.ball (0 : ℂ) 1) := by
      simpa only [hφdef] using hφdiff.const_mul 2
    have h2 : DifferentiableOn ℂ (fun z => K z * Y z) (Metric.ball (0 : ℂ) 1) :=
      hKdiff.mul hYdiff
    show DifferentiableOn ℂ ((fun z => 2 * φ z) + fun z => K z * Y z) (Metric.ball (0 : ℂ) 1)
    exact h1.add h2
  · filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hrpos] with z hz
    have hYz : Y z = V z := hYeq hz
    have hKz : K z ≠ 0 := hne' z hz
    have hφmem : φ z ∈ Metric.ball (0 : ℂ) 4 := hmem' z hz
    have hNz : (2 * φ z + K z * Y z) / (1 : Polynomial ℂ).eval z = u z := by
      rw [Polynomial.eval_one, div_one, hYz]
      show 2 * φ z + K z * ((u z - 2 * φ z) / K z) = u z
      field_simp
      ring
    rw [hNz]
    simpa only [hudef, hUdef] using hUsum (φ z) hφmem

end Work.CPull
