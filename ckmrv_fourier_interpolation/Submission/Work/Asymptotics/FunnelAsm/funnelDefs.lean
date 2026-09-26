/-
# The `r`-seminorm bound for the CKMRV contour transform on the funnel

Target (this file): `Work.Asymptotics.kernelTransform_seminorm_funnel`, the cusp-`i∞` half of
CKMRV (Ann. of Math. 196 (2022), Theorem 1.9 / Proposition 4.6 + Corollary 4.1).

## The mathematics

For `τ` in the funnel `𝓕 = {τ ∈ 𝒟 : 2 ≤ Im τ}` and `r ∈ ℝ`, the contour transform is
`kernelTransform K τ r = 4 sin²(πr²/2) · ∫_0^∞ K(τ,it) e^{-πr²t} dt` (the Bochner integral, `0`
when the integrand is not integrable).  Writing `K = Kaxis (Kfun ℓ d) τ ·`, `A = Aexp (Gcusp ℓ d) τ ·`,
`Y = τ.im` and `λ = πr²`, the paper's layer

  `paperLayer (Gcusp ℓ d) ℓ d τ r = layerLow + layerTrunc + highPart`

of CKMRV (5.3) rearranges, **on the convergence region** `r ≠ 0 ∧ (d = 8 ∨ 2 < r²)`, as

  `paperLayer τ r = layerLow ℓ d τ r + sinSq r · (preT + spikeT + tailT)(r²) + highTailClosed τ r`,

where

* `preT` is the contour integral over the window `1 ≤ t ≤ Im τ - 1`,
* `spikeT` is the contour integral over `|t - Im τ| ≤ 1` (the two translate poles `z = τ ∓ 1`),
* `tailT = ∫_{Im τ + 1}^∞ (K - A) e^{-λt} dt`,
* `highTailClosed` is the regularised closed form of `sinSq r ∫_{Im τ+1}^∞ A e^{-λt} dt`.

Each of the five pieces is bounded by `c (scale τ)^N` on the funnel:

* `layerLow`: flatness of the kernel at the cusp `0` (`Work.Asymptotics.HalfFunnel.funnelFlat`);
* `preT`: `Work.Asymptotics.funnelPreSeminorm`;
* `spikeT`: `Work.Asymptotics.funnelSpikeSeminorm` (signed model integral);
* `tailT`: `Work.Asymptotics.funnelTailSeminorm`;
* `highTailClosed`: the `psi1`-regularised closed form, exactly like `highPart_seminorm`.

The **truncated layer** `funnelLayer` is `paperLayer` on the convergence region and `0` off it:
this makes it have the *same* zero set as the naive contour integral (Mathlib's integral is `0`
off the convergence region, and the region is a threshold set in `|r|`), so the restricted
transfer lemma `funnel_transfer` (`τ`-dependent bound version of
`kernelTransform_seminorm_of_layer`) applies.  Finally `scale τ ^ N ≤ 3 ^ N ((Im τ)^{-N} + ‖τ‖^N)`
converts the bound to the requested form.

## Structure of this file

* `Funnel`, `preT`, `spikeT`, `tailT`, `funnelLayer`, `highTailClosed`, `PSum`;
* `funnel_transfer` / `funnel_transfer_aux` — the restricted transfer of a seminorm bound from a
  layer to the naive contour integral (a copy of
  `Work.Asymptotics.kernelTransform_seminorm_of_layer_moderate_aux`, re-stated here because the
  original lives behind an import (`MiddleRange/Main`) incompatible with the funnel estimates);
* `funnelLayer_seminorm` — the seminorm bound of `funnelLayer` from the two bundles
  `PSum`-bound and decomposition;
* `funnel_target_of_pieces` — the assembly, from four bundles;
* `kernelTransform_seminorm_funnel` — the target.
-/
import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Asymptotics.GcuspDefs
import Submission.Work.Asymptotics.kernelTransform_seminorm_of_layer
import Submission.Work.Asymptotics.punctured_iteratedDeriv
import Submission.Work.Asymptotics.FunnelAsm.tailGcuspW
import Submission.Work.Asymptotics.FunnelAsm.pair_gate_farA

namespace Work.Asymptotics

open UpperHalfPlane Work.Kernels MeasureTheory Filter Topology
open scoped Topology ContDiff

noncomputable section

/-- The **funnel** `𝓕 = {τ ∈ 𝒟 : 2 ≤ Im τ}` (the definition is `Work.Asymptotics.Funnel`,
from `Submission/Work/Asymptotics/funnelTailBasic.lean`): the cusp-`i∞` neighbourhood of the
CKMRV fundamental domain `𝒟`. -/
lemma mem_Funnel {τ : UpperHalfPlane} :
    τ ∈ {τ : UpperHalfPlane | Funnel τ} ↔ τ ∈ DomainD ∧ 2 ≤ τ.im := Iff.rfl

/-- The Gaussian weight `e^{-π x t}` of the contour transform, with `x = r²` (so that, for the
`r`-seminorms, the relevant variable is `x = r²` and the exponent is `λ = π x`). -/
def wgt (x t : ℝ) : ℂ := Complex.exp (-(Real.pi * x * t : ℝ))

lemma wgt_apply (x t : ℝ) : wgt x t = Complex.exp (-(Real.pi * x * t : ℝ)) := rfl

lemma wgt_eq_exp (x t : ℝ) :
    wgt x t = Complex.exp (-(Real.pi * x : ℂ) * (t : ℂ)) := by
  rw [wgt_apply]
  congr 1
  push_cast
  ring

/-- The `pre` piece of the funnel layer: the contour integral over the window
`1 ≤ t ≤ Im τ - 1`, where the poles `z = τ ∓ 1` stay at distance `≥ 1`. -/
def preT (ℓ : LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) (x : ℝ) : ℂ :=
  ∫ t in (1 : ℝ)..(τ.im - 1), Kaxis (Kfun ℓ d) τ t * wgt x t

/-- The `spike` piece of the funnel layer: the contour integral over `|t - Im τ| ≤ 1`, whose
integrand has the two translate poles `z = τ ∓ 1` of `z ↦ K(τ,z)` in its interior. -/
def spikeT (ℓ : LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) (x : ℝ) : ℂ :=
  ∫ t in (τ.im - 1)..(τ.im + 1), Kaxis (Kfun ℓ d) τ t * wgt x t

/-- The `tail` piece of the funnel layer: the contour integral over `t ≥ Im τ + 1`, with the
non-decaying part `Aexp` of the cusp expansion subtracted. -/
def tailT (ℓ : LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) (x : ℝ) : ℂ :=
  ∫ t in Set.Ioi (τ.im + 1),
    (Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t) * wgt x t

/-- The **regularised closed form of the `Aexp`-tail** `sinSq r · ∫_{Im τ + 1}^∞ Aexp(Gcusp ℓ d) τ t
· e^{-πr²t} dt`, written with `psi1` so that the apparent poles at `λ = πr² = 0` and
`μ = λ - 2π = 0` are cancelled by the double zeros of `sinSq`:

  `λ·psi1 λ·e^{-λ(Y+1)}G₀₀ + i·psi1 λ·(1+λ(Y+1))e^{-λ(Y+1)}G₀₁
   + μ·psi1 μ·e^{-μ(Y+1)}G₁₀ + i·psi1 μ·(1+μ(Y+1))e^{-μ(Y+1)}G₁₁`,

with `Y = τ.im`.  This is `Work.Asymptotics.highPart` with the lower limit `1` replaced by
`Im τ + 1`; it is the piece of the telescoping that is *not* covered by `preT`/`spikeT`/`tailT`. -/
def highTailClosed (ℓ : LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) (r : ℝ) : ℂ :=
  let Y : ℝ := τ.im + 1
  let l : ℂ := ((Real.pi * r ^ 2 : ℝ) : ℂ)
  let m : ℂ := ((Real.pi * r ^ 2 - 2 * Real.pi : ℝ) : ℂ)
  l * (psi1 (Real.pi * r ^ 2) : ℂ) * Complex.exp (-(l * (Y : ℂ))) * Gcusp ℓ d 0 0 τ +
    Complex.I * (psi1 (Real.pi * r ^ 2) : ℂ) * (1 + l * (Y : ℂ)) * Complex.exp (-(l * (Y : ℂ)))
      * Gcusp ℓ d 0 1 τ +
    m * (psi1 (Real.pi * r ^ 2 - 2 * Real.pi) : ℂ) * Complex.exp (-(m * (Y : ℂ)))
      * Gcusp ℓ d 1 0 τ +
    Complex.I * (psi1 (Real.pi * r ^ 2 - 2 * Real.pi) : ℂ) * (1 + m * (Y : ℂ))
      * Complex.exp (-(m * (Y : ℂ))) * Gcusp ℓ d 1 1 τ

/-- **The right-hand side of the funnel decomposition of the layer**: the sum of the `low` piece,
of `sinSq r` times the three contour pieces, and of the regularised `Aexp`-tail.

`funnel_target_of_pieces` consumes its seminorm bound, and the telescoping identity
`paperLayer = PSum` on the convergence region. -/
def PSum (ℓ : LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) (s : ℝ) : ℂ :=
  layerLow ℓ d τ s
    + sinSq s * (preT ℓ d τ (s ^ 2) + spikeT ℓ d τ (s ^ 2) + tailT ℓ d τ (s ^ 2))
    + highTailClosed ℓ d τ s

/-- The **truncated CKMRV layer on the funnel**: the paper's layer `paperLayer (Gcusp ℓ d)`
(equivalently `layerLow + layerTrunc + highPart`) on the region where the naive contour integral
converges, and `0` outside it.  This is the function whose `r`-seminorms are bounded on the funnel
and which agrees with `kernelTransform (Kfun ℓ d) τ ·` wherever the latter is determined. -/
def funnelLayer (ℓ : LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) (r : ℝ) : ℂ :=
  if r ≠ 0 ∧ (d = 8 ∨ 2 < r ^ 2) then paperLayer (Gcusp ℓ d) ℓ d τ r else 0

lemma funnelLayer_of_mem (ℓ : LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) {r : ℝ}
    (h : r ≠ 0 ∧ (d = 8 ∨ 2 < r ^ 2)) :
    funnelLayer ℓ d τ r = paperLayer (Gcusp ℓ d) ℓ d τ r := by
  rw [funnelLayer]; exact if_pos h

lemma funnelLayer_of_not_mem (ℓ : LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) {r : ℝ}
    (h : ¬ (r ≠ 0 ∧ (d = 8 ∨ 2 < r ^ 2))) : funnelLayer ℓ d τ r = 0 := by
  rw [funnelLayer]; exact if_neg h

/-- The region `{r ≠ 0 : d = 8 ∨ 2 < r²}` of convergence of the naive contour integral is open. -/
lemma isOpen_convergenceRegion (d : ℕ) :
    IsOpen {r : ℝ | r ≠ 0 ∧ (d = 8 ∨ 2 < r ^ 2)} := by
  by_cases h8 : d = 8
  · have hset : {r : ℝ | r ≠ 0 ∧ (d = 8 ∨ 2 < r ^ 2)} = {r : ℝ | r ≠ 0} := by
      ext r; constructor
      · rintro ⟨h, -⟩; exact h
      · intro h; exact ⟨h, Or.inl h8⟩
    rw [hset]; exact isOpen_ne
  · have hset : {r : ℝ | r ≠ 0 ∧ (d = 8 ∨ 2 < r ^ 2)} = {r : ℝ | 2 < r ^ 2} := by
      ext r; constructor
      · rintro ⟨-, h | h⟩
        · exact absurd h h8
        · exact h
      · intro h
        exact ⟨fun h0 => by rw [h0] at h; norm_num at h, Or.inr h⟩
    rw [hset]
    exact isOpen_lt continuous_const (continuous_id.pow 2)

/-- The scale comparison, copied from `Work.Asymptotics.paperLayer_scale_rpow_le`:
`(scale τ)^M ≤ 3^M ((Im τ)^{-M} + ‖τ‖^M)` for `M ≥ 0`. -/
lemma scale_rpow_le {τ : UpperHalfPlane} {M : ℝ} (hM : 0 ≤ M) :
    (scale τ) ^ M ≤ 3 ^ M * ((τ.im) ^ (-M) + ‖(τ : ℂ)‖ ^ M) := by
  set u : ℝ := (τ.im)⁻¹ with hudef
  set v : ℝ := ‖(τ : ℂ)‖ with hvdef
  have hu0 : 0 ≤ u := by rw [hudef]; exact inv_nonneg.mpr τ.im_pos.le
  have hv0 : 0 ≤ v := by rw [hvdef]; exact norm_nonneg _
  have hmax1 : 1 ≤ max u v := by
    by_contra h
    rw [not_le, max_lt_iff] at h
    obtain ⟨h1, h2⟩ := h
    have him : 1 < τ.im := by
      rcases (inv_lt_one_iff₀.mp (by rw [← hudef]; exact h1)) with h3 | h3
      · exact absurd h3 (not_le.mpr τ.im_pos)
      · exact h3
    have hle : τ.im ≤ v := by rw [hvdef]; exact im_le_coe_norm τ
    linarith
  have hsc : scale τ ≤ 3 * max u v := by
    rw [scale, ← hudef, ← hvdef]
    linarith [le_max_left u v, le_max_right u v]
  have hstep1 : scale τ ^ M ≤ (3 * max u v) ^ M :=
    Real.rpow_le_rpow (scale_pos τ).le hsc hM
  have hstep2 : (3 * max u v) ^ M = 3 ^ M * (max u v) ^ M :=
    Real.mul_rpow (by norm_num) (le_trans hu0 (le_max_left u v))
  have hstep3 : (max u v) ^ M = max (u ^ M) (v ^ M) := Real.rpow_max hu0 hv0 hM
  have hstep4 : max (u ^ M) (v ^ M) ≤ u ^ M + v ^ M :=
    max_le (le_add_of_nonneg_right (Real.rpow_nonneg hv0 M))
      (le_add_of_nonneg_left (Real.rpow_nonneg hu0 M))
  have huM : u ^ M = (τ.im) ^ (-M) := by
    rw [hudef, Real.inv_rpow τ.im_pos.le, Real.rpow_neg τ.im_pos.le]
  have hvM : v ^ M = ‖(τ : ℂ)‖ ^ M := by rw [hvdef]
  calc scale τ ^ M ≤ (3 * max u v) ^ M := hstep1
    _ = 3 ^ M * (max u v) ^ M := hstep2
    _ = 3 ^ M * max (u ^ M) (v ^ M) := by rw [hstep3]
    _ ≤ 3 ^ M * (u ^ M + v ^ M) :=
        mul_le_mul_of_nonneg_left hstep4 (Real.rpow_nonneg (by norm_num) M)
    _ = 3 ^ M * ((τ.im) ^ (-M) + ‖(τ : ℂ)‖ ^ M) := by rw [huM, hvM]


/-! ## The restricted transfer of a seminorm bound from a layer to the naive integral

This is a verbatim copy of `Work.Asymptotics.kernelTransform_seminorm_of_layer_moderate_aux`
(`Submission/Work/Asymptotics/kernelTransform_seminorm_of_layer_moderate.lean`), re-stated here
because the original module imports `MiddleRange/Main`, which clashes with `KPlusXiDefs`
(`continuous_jInvariantFun`) and therefore cannot be imported together with the funnel estimates.
The only inputs it needs -- `integrableOn_kaxis_exp_mono_abs` and the one-sided vanishing lemmas
for `iteratedDeriv` -- are all in the (compatible) module
`Work.Asymptotics.kernelTransform_seminorm_of_layer`. -/

theorem funnel_transfer_aux
    (Kf : UpperHalfPlane → UpperHalfPlane → ℂ) (F₂ : UpperHalfPlane → ℝ → ℂ)
    (R : UpperHalfPlane → ℝ) (k l : ℕ) {K : Set UpperHalfPlane}
    (hR : ∀ τ ∈ K, 0 ≤ R τ)
    (h0 : ∀ τ ∈ K, F₂ τ 0 = Work.Kernels.kernelTransform Kf τ 0)
    (hagr : ∀ τ ∈ K, ∀ r : ℝ, r ≠ 0 →
      MeasureTheory.IntegrableOn (fun t : ℝ => Work.Kernels.Kaxis Kf τ t
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0) →
      F₂ τ r = Work.Kernels.kernelTransform Kf τ r)
    (hsemi : ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ K →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => F₂ τ s) r‖ ≤ R τ) :
    ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ K →
      (|r| ^ k) * ‖iteratedDeriv l
        (fun s : ℝ => Work.Kernels.kernelTransform Kf τ s) r‖ ≤ R τ := by
  intro τ r hτ
  set G : ℝ → ℂ := fun s => F₂ τ s with hG
  set gg : ℝ → ℂ := fun s => Work.Kernels.kernelTransform Kf τ s with hgg
  set P : ℝ → Prop := fun s => MeasureTheory.IntegrableOn
      (fun t : ℝ => Work.Kernels.Kaxis Kf τ t
        * Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0) with hP
  have hPdef : ∀ s, P s = MeasureTheory.IntegrableOn
      (fun t : ℝ => Work.Kernels.Kaxis Kf τ t
        * Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0) := fun s => rfl
  have hRnn : (0:ℝ) ≤ R τ := hR τ hτ
  have hboundG : ∀ s : ℝ, (|s| ^ k) * ‖iteratedDeriv l G s‖ ≤ R τ :=
    fun s => hsemi τ s hτ
  have hP0 : ∀ s, ¬ P s → gg s = 0 := by
    intro s hs
    have hI : ¬ MeasureTheory.IntegrableOn
        (fun t : ℝ => Work.Kernels.Kaxis Kf τ t
          * Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0) := by
      rwa [hPdef s] at hs
    have hz : (∫ t in Set.Ioi (0:ℝ), Work.Kernels.Kaxis Kf τ t
        * Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ)))) = 0 :=
      integral_undef hI
    rw [hgg]
    simp only [Work.Kernels.kernelTransform, hz, mul_zero]
  have hP1 : ∀ s, s ≠ 0 → P s → gg s = G s := by
    intro s hs0 hs
    rw [hgg, hG]
    exact (hagr τ hτ s hs0 (by rwa [hPdef s] at hs)).symm
  have hgg0 : gg 0 = G 0 := by
    rw [hgg, hG]
    exact (h0 τ hτ).symm
  have hmono : ∀ s s', P s → |s| ≤ |s'| → P s' := by
    intro s s' hs hsle
    rw [hPdef s']
    exact integrableOn_kaxis_exp_mono_abs (K := Kf) τ hsle (by rwa [hPdef s] at hs)
  by_cases hne : ∃ s, P s
  · set S : Set ℝ := {b | ∃ s, P s ∧ b = |s|} with hS
    have hSne : S.Nonempty := by obtain ⟨s, hs⟩ := hne; exact ⟨|s|, s, hs, rfl⟩
    have hSbdd : BddBelow S := ⟨0, by rintro b ⟨s, _, rfl⟩; positivity⟩
    set ρ : ℝ := sInf S with hρ
    have hρnn : 0 ≤ ρ := by
      rw [hρ]; exact le_csInf hSne (by rintro b ⟨s, _, rfl⟩; positivity)
    have hbig : ∀ s, ρ < |s| → P s := by
      intro s hs
      have hlt : sInf S < |s| := by rw [← hρ]; exact hs
      obtain ⟨b, hbS, hblt⟩ := (csInf_lt_iff hSbdd hSne).mp hlt
      obtain ⟨s₀, hPs₀, hb_eq⟩ := hbS
      exact hmono s₀ s hPs₀ (le_of_lt (by rw [hb_eq] at hblt; exact hblt))
    have hsmall : ∀ s, |s| < ρ → ¬ P s := by
      intro s hs hPs
      have hle : ρ ≤ |s| := by
        rw [hρ]; exact csInf_le hSbdd ⟨s, hPs, rfl⟩
      linarith
    have hzero : ∀ s, |s| < ρ → gg s = 0 := fun s hs => hP0 s (hsmall s hs)
    have hgood : ∀ s, ρ < |s| → gg s = G s := by
      intro s hs
      have hs0 : s ≠ 0 := by
        intro h; subst h; rw [abs_zero] at hs; linarith
      exact hP1 s hs0 (hbig s hs)
    rcases eq_or_lt_of_le hρnn with hρ0 | hρpos
    · have hggG : gg = G := by
        funext s
        rcases eq_or_ne s 0 with h | h
        · subst h; exact hgg0
        · exact hgood s (by rw [← hρ0]; exact abs_pos.mpr h)
      rw [hggG]
      exact hboundG r
    · rcases lt_trichotomy r ρ with hr | hr | hr
      · rcases lt_trichotomy r (-ρ) with hr' | hr' | hr'
        · have habs : ρ < |r| := by rw [abs_of_neg (by linarith)]; linarith
          have hGG : gg =ᶠ[𝓝 r] G := by
            refine Filter.eventually_of_mem ?_ (fun s hs => hgood s hs)
            exact IsOpen.mem_nhds (isOpen_lt continuous_const continuous_abs) habs
          rw [iteratedDeriv_congr_of_eventuallyEq hGG l]
          exact hboundG r
        · subst hr'
          rcases l with _ | l'
          · simp only [iteratedDeriv_zero]
            by_cases hP : P (-ρ)
            · rw [hP1 (-ρ) (by linarith) hP]
              simpa only [iteratedDeriv_zero] using hboundG (-ρ)
            · rw [hP0 (-ρ) hP, norm_zero, mul_zero]
              exact hRnn
          · have hz : iteratedDeriv (l' + 1) gg (-ρ) = 0 :=
              iteratedDeriv_succ_eq_zero_of_eqOn_Ioo_right (by linarith : -ρ < ρ)
                (fun y hy => hzero y (by rw [abs_lt]; exact ⟨by linarith [hy.1], hy.2⟩)) l'
            rw [hz, norm_zero, mul_zero]
            exact hRnn
        · have habs : |r| < ρ := by rw [abs_lt]; exact ⟨by linarith, hr⟩
          have hGG : gg =ᶠ[𝓝 r] (fun _ => (0:ℂ)) := by
            refine Filter.eventually_of_mem ?_ (fun s hs => hzero s hs)
            exact IsOpen.mem_nhds (isOpen_lt continuous_abs continuous_const) habs
          rw [iteratedDeriv_congr_of_eventuallyEq hGG l, iteratedDeriv_zeroFun]
          simp only [norm_zero, mul_zero]
          exact hRnn
      · subst hr
        rcases l with _ | l'
        · simp only [iteratedDeriv_zero]
          by_cases hP : P ρ
          · rw [hP1 ρ hρpos.ne' hP]
            simpa only [iteratedDeriv_zero] using hboundG ρ
          · rw [hP0 ρ hP, norm_zero, mul_zero]
            exact hRnn
        · have hz : iteratedDeriv (l' + 1) gg ρ = 0 :=
            iteratedDeriv_succ_eq_zero_of_eqOn_Ioo_left hρpos
              (fun y hy => hzero y (by rw [abs_of_pos hy.1]; exact hy.2)) l'
          rw [hz, norm_zero, mul_zero]
          exact hRnn
      · have habs : ρ < |r| := by rw [abs_of_pos (by linarith)]; linarith
        have hGG : gg =ᶠ[𝓝 r] G := by
          refine Filter.eventually_of_mem ?_ (fun s hs => hgood s hs)
          exact IsOpen.mem_nhds (isOpen_lt continuous_const continuous_abs) habs
        rw [iteratedDeriv_congr_of_eventuallyEq hGG l]
        exact hboundG r
  · have hnone : ∀ s, ¬ P s := fun s hs => hne ⟨s, hs⟩
    have hg0 : gg = fun _ => (0:ℂ) := funext (fun s => hP0 s (hnone s))
    rw [hg0, iteratedDeriv_zeroFun]
    simp only [norm_zero, mul_zero]
    exact hRnn


/-! ## Evenness of the pieces and of `PSum` -/

lemma funnel_sinSq_neg (s : ℝ) : sinSq (-s) = sinSq s := by
  simp only [sinSq, Complex.ofReal_neg, neg_sq]

lemma funnel_layerLow_neg (ℓ : LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) (s : ℝ) :
    layerLow ℓ d τ (-s) = layerLow ℓ d τ s := by
  have hsq : (((-s : ℝ)) : ℂ) ^ 2 = ((s : ℝ) : ℂ) ^ 2 := by
    rw [Complex.ofReal_neg, neg_sq]
  simp only [layerLow, hsq, funnel_sinSq_neg]

lemma funnel_highTailClosed_neg (ℓ : LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) (s : ℝ) :
    highTailClosed ℓ d τ (-s) = highTailClosed ℓ d τ s := by
  have hsq : ((-s : ℝ)) ^ 2 = s ^ 2 := by ring
  simp only [highTailClosed, hsq]

lemma PSum_neg (ℓ : LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) :
    ∀ s : ℝ, PSum ℓ d τ (-s) = PSum ℓ d τ s := by
  intro s
  have hsq : ((-s : ℝ)) ^ 2 = s ^ 2 := by ring
  simp only [PSum, funnel_layerLow_neg, funnel_sinSq_neg, funnel_highTailClosed_neg, hsq]

/-- `funnelLayer` vanishes where `r ^ 2 ≤ 2` in dimension `24`. -/
lemma funnelLayer_eq_zero_of_sq_le {ℓ : LogLambdaData} {d : ℕ} (hd : d = 24)
    {τ : UpperHalfPlane} {s : ℝ} (h : s ^ 2 ≤ 2) : funnelLayer ℓ d τ s = 0 := by
  refine funnelLayer_of_not_mem ℓ d τ ?_
  rintro ⟨-, h8 | h2⟩
  · exact absurd (h8.symm.trans hd) (by decide)
  · exact absurd h2 (not_lt.mpr h)

/-- The naive contour transform vanishes at `r = 0` (`sinSq 0 = 0`). -/
lemma kernelTransform_zero (K : UpperHalfPlane → UpperHalfPlane → ℂ) (τ : UpperHalfPlane) :
    kernelTransform K τ 0 = 0 := by
  rw [kernelTransform]
  simp

/-! ## The pair gate and the vanishing of the transform for `r ^ 2 ≤ 2` in dimension `24` -/

/-- **The pair gate on the funnel**: the two coefficients of the `e^{2πt}`-part of the
dimension-`24` kernel never vanish simultaneously on `{τ ∈ 𝒟 : 2 ≤ Im τ}`.

This is `Work.Asymptotics.pair_gate_far` (proved in the sibling module
`Submission/Work/Asymptotics/pair_gate_far.lean`, whose proof is independent of the
`KPlusXiDefs` world), transported across the import-world boundary by the verified copies in
`Submission/Work/Asymptotics/FunnelAsm/`. -/
lemma funnel_pair_gate (ℓ : LogLambdaData) {τ : UpperHalfPlane} (hτ : Funnel τ) :
    (Gcusp ℓ 24 1 0 τ, Gcusp ℓ 24 1 1 τ) ≠ (0, 0) :=
  Work.Asymptotics.pair_gate_far ℓ τ hτ.2

/-- **Exponential beats polynomial** (a copy of `Work.Asymptotics.tail_domination_exp`): for
`K > 0`, `N ≥ 0`, `c > 0` and `2π + b > 0` there is a tail on which
`K (1+t)^N e^{-bt} ≤ c e^{2πt}`. -/
theorem exp_domination (K N : ℝ) (hK : 0 < K) (hN : 0 ≤ N) (b c : ℝ) (hc : 0 < c)
    (hb : 0 < 2 * Real.pi + b) :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
      K * (1 + t) ^ N * Real.exp (-(b * t)) ≤ Real.exp (2 * Real.pi * t) * c := by
  set a : ℝ := 2 * Real.pi + b with ha_def
  have ha : 0 < a := hb
  have ha2 : 0 < a / 2 := by linarith
  -- Polynomial growth is `o` of the exponential of half the rate.
  have hO : (fun x : ℝ => x ^ N) =o[atTop] (fun x : ℝ => Real.exp ((a / 2) * x)) :=
    isLittleO_rpow_exp_pos_mul_atTop N ha2
  have hbound := hO.bound one_pos
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp hbound
  have hpoly : ∀ x : ℝ, max X₁ 0 ≤ x → x ^ N ≤ Real.exp ((a / 2) * x) := by
    intro x hx
    have hx0 : 0 ≤ x := le_trans (le_max_right _ _) hx
    have h1 : ‖x ^ N‖ ≤ 1 * ‖Real.exp ((a / 2) * x)‖ :=
      hX₁ x (le_trans (le_max_left _ _) hx)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hx0 N),
        Real.norm_of_nonneg (Real.exp_pos _).le, one_mul] at h1
    exact h1
  -- Eventually the exponential of half the rate dominates the constant `K * 2^N / c`.
  have hlin : Tendsto (fun t : ℝ => Real.exp ((a / 2) * t)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop ha2)
  obtain ⟨X₃, hX₃⟩ := eventually_atTop.mp (hlin.eventually_ge_atTop (K * 2 ^ N / c))
  refine ⟨max (max X₁ 0) (max 1 X₃), ?_⟩
  intro t ht
  have ht1 : (1 : ℝ) ≤ t :=
    le_trans (le_max_left 1 X₃) (le_trans (le_max_right (max X₁ 0) (max 1 X₃)) ht)
  have htx1 : max X₁ 0 ≤ t := le_trans (le_max_left (max X₁ 0) (max 1 X₃)) ht
  have htx3 : X₃ ≤ t :=
    le_trans (le_max_right 1 X₃) (le_trans (le_max_right (max X₁ 0) (max 1 X₃)) ht)
  have htN : t ^ N ≤ Real.exp ((a / 2) * t) := hpoly t htx1
  have ht0 : 0 ≤ t := by linarith
  have hexpnn : 0 ≤ Real.exp ((a / 2) * t) := (Real.exp_pos _).le
  have hK2 : K * 2 ^ N ≤ c * Real.exp ((a / 2) * t) := by
    have h := (div_le_iff₀ hc).mp (hX₃ t htx3)
    rw [mul_comm (Real.exp ((a / 2) * t)) c] at h
    exact h
  -- `(1+t)^N ≤ 2^N t^N` on the tail `t ≥ 1`.
  have hpow : (1 + t) ^ N ≤ 2 ^ N * t ^ N := by
    have h1 : 0 ≤ 1 + t := by linarith
    have h2 : 1 + t ≤ 2 * t := by linarith
    have h3 : (1 + t) ^ N ≤ (2 * t) ^ N := Real.rpow_le_rpow h1 h2 hN
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) ht0] at h3
    exact h3
  have hstep1 : K * (1 + t) ^ N ≤ (K * 2 ^ N) * t ^ N := by
    have h := mul_le_mul_of_nonneg_left hpow hK.le
    rwa [← mul_assoc] at h
  have hstep2 : (K * 2 ^ N) * t ^ N ≤
      (c * Real.exp ((a / 2) * t)) * Real.exp ((a / 2) * t) :=
    mul_le_mul hK2 htN (Real.rpow_nonneg ht0 N) (mul_nonneg hc.le hexpnn)
  have hEq : (c * Real.exp ((a / 2) * t)) * Real.exp ((a / 2) * t) = c * Real.exp (a * t) := by
    rw [mul_assoc, ← Real.exp_add, show (a / 2) * t + (a / 2) * t = a * t by ring]
  have hmain : K * (1 + t) ^ N ≤ c * Real.exp (a * t) :=
    le_trans hstep1 (le_trans hstep2 (le_of_eq hEq))
  -- Multiply by `exp (-(b*t))` and identify the two sides.
  have hfin : K * (1 + t) ^ N * Real.exp (-(b * t)) ≤
      c * Real.exp (a * t) * Real.exp (-(b * t)) :=
    mul_le_mul_of_nonneg_right hmain (Real.exp_pos _).le
  have hRHS : c * Real.exp (a * t) * Real.exp (-(b * t)) = Real.exp (2 * Real.pi * t) * c := by
    have harg : a * t + (-(b * t)) = 2 * Real.pi * t := by rw [ha_def]; ring
    rw [mul_assoc, ← Real.exp_add, harg]
    exact mul_comm _ _
  rw [hRHS] at hfin
  exact hfin

/-- `‖a + t·i·b‖` is bounded below by a positive constant on a tail whenever `(a,b) ≠ (0,0)`. -/
lemma norm_add_mul_I_ge_of_pair_ne_zero (a b : ℂ) (h : (a, b) ≠ (0, 0)) :
    ∃ c T : ℝ, 0 < c ∧ ∀ t : ℝ, T ≤ t → c ≤ ‖a + (t : ℂ) * Complex.I * b‖ := by
  by_cases hb : b = 0
  · have ha : a ≠ 0 := fun ha => h (by simp [ha, hb])
    refine ⟨‖a‖ / 2, 0, by positivity, fun t _ => ?_⟩
    have : a + (t : ℂ) * Complex.I * b = a := by rw [hb]; ring
    rw [this]
    linarith [norm_pos_iff.mpr ha]
  · have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hb
    refine ⟨‖b‖ / 2, (‖a‖ + ‖b‖) / ‖b‖, by positivity, fun t ht => ?_⟩
    have htnn : 0 ≤ t := le_trans (by positivity) ht
    have hnorm : ‖(t : ℂ) * Complex.I * b‖ = t * ‖b‖ := by
      rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg htnn]
    have hkey : ‖(t : ℂ) * Complex.I * b‖ - ‖a‖ ≤ ‖a + (t : ℂ) * Complex.I * b‖ := by
      have := norm_sub_norm_le ((t : ℂ) * Complex.I * b) (-a)
      simpa [sub_neg_eq_add, add_comm, norm_neg] using this
    have htb : ‖a‖ + ‖b‖ ≤ t * ‖b‖ := by
      rw [div_le_iff₀ hbpos] at ht
      linarith [ht]
    rw [hnorm] at hkey
    linarith

/-- A function whose norm is bounded below by a positive constant on the tail `[T', ∞)` is not
integrable on any set containing that tail. -/
lemma not_integrableOn_Ioi_of_const_le {f : ℝ → ℂ} {T T' c : ℝ} (hc : 0 < c) (hTT' : T ≤ T')
    (h : ∀ t : ℝ, T' ≤ t → c ≤ ‖f t‖) :
    ¬ IntegrableOn f (Set.Ioi T) := by
  intro hf
  have htail : IntegrableOn f (Set.Ioi T') := hf.mono_set (Set.Ioi_subset_Ioi hTT')
  have hnorm : IntegrableOn (fun t : ℝ => ‖f t‖) (Set.Ioi T') := htail.norm
  have hnormnn : 0 ≤ᵐ[volume.restrict (Set.Ioi T')] (fun t : ℝ => ‖f t‖) :=
    Filter.Eventually.of_forall (fun t => norm_nonneg _)
  have hmono : ∀ n : ℕ, (∫ t in Set.Ioc T' (T' + n), ‖f t‖) ≤ ∫ t in Set.Ioi T', ‖f t‖ := by
    intro n
    refine MeasureTheory.setIntegral_mono_set hnorm hnormnn ?_
    exact Filter.Eventually.of_forall (fun x hx => hx.1)
  have hlow : ∀ n : ℕ, c * (n : ℝ) ≤ ∫ t in Set.Ioc T' (T' + n), ‖f t‖ := by
    intro n
    have hIntConst : IntegrableOn (fun _ : ℝ => (c : ℝ)) (Set.Ioc T' (T' + n)) := by
      refine integrableOn_const ?_
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_ne_top
    have hIntNorm : IntegrableOn (fun t : ℝ => ‖f t‖) (Set.Ioc T' (T' + n)) :=
      hnorm.mono_set (fun t ht => ht.1)
    have hle : (∫ t in Set.Ioc T' (T' + n), (c : ℝ)) ≤ ∫ t in Set.Ioc T' (T' + n), ‖f t‖ := by
      refine MeasureTheory.integral_mono_ae hIntConst hIntNorm ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
      exact h t (le_of_lt ht.1)
    rw [MeasureTheory.setIntegral_const] at hle
    have hvol : volume.real (Set.Ioc T' (T' + n)) = (n : ℝ) := by
      rw [MeasureTheory.measureReal_def, Real.volume_Ioc]
      rw [show T' + (n : ℝ) - T' = (n : ℝ) by ring]
      simp
    rw [hvol, smul_eq_mul] at hle
    calc c * (n : ℝ) = (n : ℝ) * c := by ring
      _ ≤ ∫ t in Set.Ioc T' (T' + n), ‖f t‖ := hle
  set M : ℝ := ∫ t in Set.Ioi T', ‖f t‖ with hM
  have hbdd : ∀ n : ℕ, c * (n : ℝ) ≤ M := fun n => le_trans (hlow n) (hmono n)
  obtain ⟨n, hn⟩ := exists_nat_gt (M / c)
  have h1 : (n : ℝ) * c ≤ M := by linarith [hbdd n]
  have h2 : M < (n : ℝ) * c := by
    have := mul_lt_mul_of_pos_right hn hc
    rwa [div_mul_cancel₀ M hc.ne'] at this
  linarith

/-- On the funnel the contour kernel of dimension `24` grows at least like `e^{2π t}` along a
tail of the contour: `Aexp` contains the term `e^{2πt}·(G_{1,0} + it·G_{1,1})` whose coefficient
is bounded below by the pair gate, and the remainder `K - Aexp` is exponentially small
(`funnelKernelTailGcuspW`). -/
lemma funnel_expLower (ℓ : LogLambdaData) {τ : UpperHalfPlane} (hτ : Funnel τ) :
    ∃ c T : ℝ, 0 < c ∧ ∀ t : ℝ, T ≤ t →
      c * Real.exp (2 * Real.pi * t) ≤ ‖Kaxis (Kfun ℓ 24) τ t‖ := by
  obtain ⟨c₀, T₀, hc₀, hT₀⟩ :=
    norm_add_mul_I_ge_of_pair_ne_zero (Gcusp ℓ 24 1 0 τ) (Gcusp ℓ 24 1 1 τ)
      (fun h => funnel_pair_gate ℓ hτ h)
  obtain ⟨C, N, M, hC, hN, hM, hb₁⟩ := funnelKernelTailGcuspW ℓ 24 (Or.inr rfl)
  have hA0 : 0 ≤ ‖Gcusp ℓ 24 0 0 τ‖ := norm_nonneg _
  have hA1 : 0 ≤ ‖Gcusp ℓ 24 0 1 τ‖ := norm_nonneg _
  have hS : 0 ≤ (scale τ) ^ N * Real.exp (Real.pi * τ.im) :=
    mul_nonneg (Real.rpow_nonneg (scale_pos τ).le N) (Real.exp_nonneg _)
  have hpi : 0 < Real.pi := Real.pi_pos
  obtain ⟨T₂, hT₂⟩ := exp_domination (‖Gcusp ℓ 24 0 0 τ‖ + ‖Gcusp ℓ 24 0 1 τ‖ + 1) 1
    (by positivity) (by norm_num) 0 (c₀ / 4) (by linarith) (by linarith)
  obtain ⟨T₃, hT₃⟩ := exp_domination ((C + 1) * (scale τ) ^ N * Real.exp (Real.pi * τ.im)) M
    (mul_pos (mul_pos (by linarith) (Real.rpow_pos_of_pos (scale_pos τ) N))
      (Real.exp_pos _)) hM Real.pi (c₀ / 4) (by linarith) (by linarith)
  have hev : ∀ᶠ t : ℝ in Filter.atTop,
      T₀ ≤ t ∧ T₂ ≤ t ∧ T₃ ≤ t ∧ τ.im + 1 ≤ t ∧ (1 : ℝ) ≤ t := by
    filter_upwards [Filter.eventually_ge_atTop T₀, Filter.eventually_ge_atTop T₂,
      Filter.eventually_ge_atTop T₃, Filter.eventually_ge_atTop (τ.im + 1),
      Filter.eventually_ge_atTop (1 : ℝ)] with t h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hev
  refine ⟨c₀ / 2, T, by linarith, ?_⟩
  intro t ht
  obtain ⟨hT₀', hT₂', hT₃', him1, ht1⟩ := hT t ht
  have htpos : 0 < t := lt_of_lt_of_le one_pos ht1
  have hpair := hT₀ t hT₀'
  have hexpnn : 0 ≤ Real.exp (2 * Real.pi * t) := (Real.exp_pos _).le
  have hAexp : Aexp (Gcusp ℓ 24) τ t
      = (Gcusp ℓ 24 0 0 τ + ((t : ℂ) * Complex.I) * Gcusp ℓ 24 0 1 τ)
        + Complex.exp (2 * Real.pi * t)
            * (Gcusp ℓ 24 1 0 τ + ((t : ℂ) * Complex.I) * Gcusp ℓ 24 1 1 τ) := by
    rw [Aexp]
  have hexpnorm : ‖Complex.exp (2 * Real.pi * t)‖ = Real.exp (2 * Real.pi * t) := by
    have harg : (2 : ℂ) * (Real.pi : ℂ) * (t : ℂ) = ((2 * Real.pi * t : ℝ) : ℂ) := by
      push_cast; ring
    rw [harg, Complex.norm_exp_ofReal]
  have hbig : c₀ * Real.exp (2 * Real.pi * t)
      ≤ ‖Complex.exp (2 * Real.pi * t)
          * (Gcusp ℓ 24 1 0 τ + ((t : ℂ) * Complex.I) * Gcusp ℓ 24 1 1 τ)‖ := by
    rw [norm_mul, hexpnorm, mul_comm c₀ (Real.exp (2 * Real.pi * t))]
    exact mul_le_mul_of_nonneg_left hpair hexpnn
  have hdom1 : ‖Gcusp ℓ 24 0 0 τ‖ + t * ‖Gcusp ℓ 24 0 1 τ‖
      ≤ (c₀ / 4) * Real.exp (2 * Real.pi * t) := by
    have h2 := hT₂ t hT₂'
    simp only [zero_mul, neg_zero, Real.exp_zero, mul_one, Real.rpow_one] at h2
    have hp : ‖Gcusp ℓ 24 0 0 τ‖ + t * ‖Gcusp ℓ 24 0 1 τ‖
        ≤ (‖Gcusp ℓ 24 0 0 τ‖ + ‖Gcusp ℓ 24 0 1 τ‖ + 1) * (1 + t) := by
      nlinarith [hA0, hA1, ht1, mul_nonneg hA1 (le_of_lt htpos)]
    linarith
  have hdom2 : ‖Kaxis (Kfun ℓ 24) τ t - Aexp (Gcusp ℓ 24) τ t‖
      ≤ (c₀ / 4) * Real.exp (2 * Real.pi * t) := by
    have heq3 : Real.exp (-(Real.pi * (t - τ.im)))
        = Real.exp (Real.pi * τ.im) * Real.exp (-(Real.pi * t)) := by
      rw [← Real.exp_add]; congr 1; ring
    have h1nn : 0 ≤ (1 + t) ^ M * Real.exp (-(Real.pi * t)) := by positivity
    have h3b : ‖Kaxis (Kfun ℓ 24) τ t - Aexp (Gcusp ℓ 24) τ t‖
        ≤ (C * ((scale τ) ^ N * Real.exp (Real.pi * τ.im))) * (1 + t) ^ M
            * Real.exp (-(Real.pi * t)) := by
      have h3 := hb₁ τ t hτ him1
      rw [heq3] at h3
      rw [show C * (scale τ) ^ N * (1 + t) ^ M
            * (Real.exp (Real.pi * τ.im) * Real.exp (-(Real.pi * t)))
          = (C * ((scale τ) ^ N * Real.exp (Real.pi * τ.im))) * (1 + t) ^ M
            * Real.exp (-(Real.pi * t)) by ring] at h3
      exact h3
    have hCS : C * ((scale τ) ^ N * Real.exp (Real.pi * τ.im))
        ≤ (C + 1) * ((scale τ) ^ N * Real.exp (Real.pi * τ.im)) :=
      mul_le_mul_of_nonneg_right (by linarith) hS
    have hkey := mul_le_mul_of_nonneg_right hCS h1nn
    have h4 := hT₃ t hT₃'
    have h4' : ((C + 1) * ((scale τ) ^ N * Real.exp (Real.pi * τ.im))) * ((1 + t) ^ M
          * Real.exp (-(Real.pi * t)))
        ≤ Real.exp (2 * Real.pi * t) * (c₀ / 4) := by
      rw [show (C + 1) * (scale τ) ^ N * Real.exp (Real.pi * τ.im) * (1 + t) ^ M
            * Real.exp (-(Real.pi * t))
          = ((C + 1) * ((scale τ) ^ N * Real.exp (Real.pi * τ.im))) * ((1 + t) ^ M
            * Real.exp (-(Real.pi * t))) by ring] at h4
      exact h4
    calc ‖Kaxis (Kfun ℓ 24) τ t - Aexp (Gcusp ℓ 24) τ t‖
        ≤ (C * ((scale τ) ^ N * Real.exp (Real.pi * τ.im))) * (1 + t) ^ M
            * Real.exp (-(Real.pi * t)) := h3b
      _ = (C * ((scale τ) ^ N * Real.exp (Real.pi * τ.im))) * ((1 + t) ^ M
            * Real.exp (-(Real.pi * t))) := by ring
      _ ≤ ((C + 1) * ((scale τ) ^ N * Real.exp (Real.pi * τ.im))) * ((1 + t) ^ M
            * Real.exp (-(Real.pi * t))) := hkey
      _ ≤ Real.exp (2 * Real.pi * t) * (c₀ / 4) := h4'
      _ = (c₀ / 4) * Real.exp (2 * Real.pi * t) := by ring
  have hAle : c₀ * Real.exp (2 * Real.pi * t)
      - (‖Gcusp ℓ 24 0 0 τ‖ + t * ‖Gcusp ℓ 24 0 1 τ‖)
      ≤ ‖Aexp (Gcusp ℓ 24) τ t‖ := by
    have hpoly : ‖(Gcusp ℓ 24 0 0 τ + ((t : ℂ) * Complex.I) * Gcusp ℓ 24 0 1 τ)‖
        ≤ ‖Gcusp ℓ 24 0 0 τ‖ + t * ‖Gcusp ℓ 24 0 1 τ‖ := by
      refine le_trans (norm_add_le _ _) ?_
      have htn : ‖((t : ℝ) : ℂ)‖ = t := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
      rw [norm_mul, norm_mul, Complex.norm_I, mul_one, htn]
    have hpoly' : Aexp (Gcusp ℓ 24) τ t
          - (Gcusp ℓ 24 0 0 τ + ((t : ℂ) * Complex.I) * Gcusp ℓ 24 0 1 τ)
        = Complex.exp (2 * Real.pi * t)
            * (Gcusp ℓ 24 1 0 τ + ((t : ℂ) * Complex.I) * Gcusp ℓ 24 1 1 τ) := by
      rw [hAexp]; ring
    have h3 : ‖Complex.exp (2 * Real.pi * t)
          * (Gcusp ℓ 24 1 0 τ + ((t : ℂ) * Complex.I) * Gcusp ℓ 24 1 1 τ)‖
        ≤ ‖Aexp (Gcusp ℓ 24) τ t‖
          + ‖Gcusp ℓ 24 0 0 τ + ((t : ℂ) * Complex.I) * Gcusp ℓ 24 0 1 τ‖ := by
      rw [← hpoly']
      exact norm_sub_le _ _
    linarith
  have hsub : ‖Aexp (Gcusp ℓ 24) τ t‖ - ‖Kaxis (Kfun ℓ 24) τ t - Aexp (Gcusp ℓ 24) τ t‖
      ≤ ‖Kaxis (Kfun ℓ 24) τ t‖ := by
    have h := (abs_le.mp (abs_norm_sub_norm_le (Aexp (Gcusp ℓ 24) τ t)
      (Kaxis (Kfun ℓ 24) τ t))).2
    rw [norm_sub_rev] at h
    linarith
  have hfinal : c₀ * Real.exp (2 * Real.pi * t)
      - (c₀ / 4) * Real.exp (2 * Real.pi * t) - (c₀ / 4) * Real.exp (2 * Real.pi * t)
      ≤ ‖Kaxis (Kfun ℓ 24) τ t‖ := by
    linarith
  have hval : c₀ * Real.exp (2 * Real.pi * t)
      - (c₀ / 4) * Real.exp (2 * Real.pi * t) - (c₀ / 4) * Real.exp (2 * Real.pi * t)
      = (c₀ / 2) * Real.exp (2 * Real.pi * t) := by ring
  linarith [hfinal, hval]

/-- **The naive contour integral vanishes for `r ^ 2 ≤ 2` in dimension `24` on the funnel.**
The integrand grows like `e^{π(2 - r²)t}`, hence is not integrable for `r ^ 2 ≤ 2`; Mathlib's
Bochner integral is then `0`. -/
theorem funnel_kernelTransform_zero (ℓ : LogLambdaData) :
    ∀ (τ : UpperHalfPlane) (r : ℝ), Funnel τ → r ≠ 0 → r ^ 2 ≤ 2 →
      kernelTransform (Kfun ℓ 24) τ r = 0 := by
  intro τ r hτ hr hr2
  obtain ⟨c, T, hc, hT⟩ := funnel_expLower ℓ hτ
  set L : ℝ := Real.pi * r ^ 2 with hL
  have hLle : L ≤ 2 * Real.pi := by rw [hL]; nlinarith [Real.pi_pos, hr2]
  have hni : ¬ IntegrableOn (fun t : ℝ => Kaxis (Kfun ℓ 24) τ t
      * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0) := by
    refine not_integrableOn_Ioi_of_const_le (f := fun t : ℝ => Kaxis (Kfun ℓ 24) τ t
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (T := 0) (T' := max T 0) hc
      (le_max_right _ _) ?_
    intro t ht
    have htT : T ≤ t := le_trans (le_max_left _ _) ht
    have ht0 : 0 ≤ t := le_trans (le_max_right _ _) ht
    have h1 : c * Real.exp (2 * Real.pi * t) ≤ ‖Kaxis (Kfun ℓ 24) τ t‖ := hT t htT
    have hre : (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))).re = -(L * t) := by
      have hcast : -(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)) = -(((Real.pi * r ^ 2 * t : ℝ)) : ℂ) := by
        push_cast; ring
      rw [hcast, Complex.neg_re, Complex.ofReal_re, hL]
    have hnorm : ‖Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))‖ = Real.exp (-(L * t)) := by
      rw [Complex.norm_exp, hre]
    have hexp : Real.exp (-(L * t)) * Real.exp (2 * Real.pi * t)
        = Real.exp ((2 * Real.pi - L) * t) := by
      rw [← Real.exp_add]; congr 1; ring
    have hge1 : 1 ≤ Real.exp ((2 * Real.pi - L) * t) :=
      Real.one_le_exp (by nlinarith [hLle, ht0])
    have hstep : c ≤ Real.exp (-(L * t)) * (c * Real.exp (2 * Real.pi * t)) := by
      have key : Real.exp (-(L * t)) * (c * Real.exp (2 * Real.pi * t))
          = c * Real.exp ((2 * Real.pi - L) * t) := by
        calc Real.exp (-(L * t)) * (c * Real.exp (2 * Real.pi * t))
            = (Real.exp (-(L * t)) * c) * Real.exp (2 * Real.pi * t) := by ring
          _ = (c * Real.exp (-(L * t))) * Real.exp (2 * Real.pi * t) := by
                rw [mul_comm (Real.exp (-(L * t))) c]
          _ = c * (Real.exp (-(L * t)) * Real.exp (2 * Real.pi * t)) := by ring
          _ = c * Real.exp ((2 * Real.pi - L) * t) := by rw [hexp]
      rw [key]
      nlinarith [hge1, hc]
    calc c ≤ Real.exp (-(L * t)) * (c * Real.exp (2 * Real.pi * t)) := hstep
      _ ≤ Real.exp (-(L * t)) * ‖Kaxis (Kfun ℓ 24) τ t‖ :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_nonneg _)
      _ = ‖Kaxis (Kfun ℓ 24) τ t
            * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))‖ := by
          rw [norm_mul, hnorm]; ring
  rw [kernelTransform]
  have hz : (∫ t in Set.Ioi (0 : ℝ), Kaxis (Kfun ℓ 24) τ t
      * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) = 0 :=
    MeasureTheory.integral_undef hni
  rw [hz]
  ring

/-! ## The restricted transfer -/

/-- **Restricted transfer of a seminorm bound from a layer to the naive contour integral.**

If `F₂` agrees with `kernelTransform Kf τ ·` at `0` and at every `r ≠ 0` where the contour
integrand is integrable, and its `(k,l)`-seminorms are bounded by `c (scale τ)^N` on the funnel,
then so are the seminorms of the naive integral. -/
theorem funnel_transfer (ℓ : LogLambdaData) (d : ℕ) (F₂ : UpperHalfPlane → ℝ → ℂ)
    (h0 : ∀ (τ : UpperHalfPlane), Funnel τ → F₂ τ 0 = kernelTransform (Kfun ℓ d) τ 0)
    (hagr : ∀ (τ : UpperHalfPlane), Funnel τ → ∀ r : ℝ, r ≠ 0 →
      IntegrableOn (fun t : ℝ => Kaxis (Kfun ℓ d) τ t
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0) →
      F₂ τ r = kernelTransform (Kfun ℓ d) τ r)
    (hsemi : ∀ k l : ℕ, ∃ c N : ℝ, 0 ≤ c ∧ 0 ≤ N ∧ ∀ (τ : UpperHalfPlane) (r : ℝ), Funnel τ →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => F₂ τ s) r‖ ≤ c * (scale τ) ^ N) :
    ∀ k l : ℕ, ∃ c N : ℝ, 0 ≤ c ∧ 0 ≤ N ∧ ∀ (τ : UpperHalfPlane) (r : ℝ), Funnel τ →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => kernelTransform (Kfun ℓ d) τ s) r‖
        ≤ c * (scale τ) ^ N := by
  intro k l
  obtain ⟨c, N, hc, hN, hb⟩ := hsemi k l
  refine ⟨c, N, hc, hN, ?_⟩
  have hR : ∀ τ ∈ {τ : UpperHalfPlane | Funnel τ}, 0 ≤ c * (scale τ) ^ N := by
    intro τ _
    exact mul_nonneg hc (Real.rpow_nonneg (scale_pos τ).le N)
  intro τ r hτ
  exact funnel_transfer_aux (Kfun ℓ d) F₂ (fun τ => c * (scale τ) ^ N) k l hR
    (fun τ hτ => h0 τ hτ) (fun τ hτ r hr h => hagr τ hτ r hr h)
    (fun τ r hτ => hb τ r hτ) τ r hτ

/-! ## The seminorm bound of the truncated layer -/

/-- **The `r`-seminorm bound of the truncated layer `funnelLayer` on the funnel**, assembled
from the `PSum`-bundle and the decomposition `paperLayer = PSum` on the convergence region.

Off the convergence region the truncated layer is either `0` (dimension `24`, `r ^ 2 ≤ 2`, where it
vanishes on a whole interval, so that all its iterated derivatives vanish by the one-sided
vanishing lemmas) or agrees with `paperLayer` off `r = 0` (dimension `8`), where the single
puncture at `0` is handled by `punctured_iteratedDeriv` (the layer is even in `r`, and `PSum` is
differentiable). -/
theorem funnelLayer_seminorm (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hPSum : ∀ k l : ℕ, ∃ c N : ℝ, 0 ≤ c ∧ 0 ≤ N ∧
      ∀ (τ : UpperHalfPlane) (r : ℝ), Funnel τ → (d = 8 ∨ 2 ≤ r ^ 2) →
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => PSum ℓ d τ s) r‖ ≤ c * (scale τ) ^ N)
    (hDecomp : ∀ (τ : UpperHalfPlane) (r : ℝ), Funnel τ → r ≠ 0 → (d = 8 ∨ 2 < r ^ 2) →
      paperLayer (Gcusp ℓ d) ℓ d τ r = PSum ℓ d τ r)
    (hDiff : ∀ (τ : UpperHalfPlane), Funnel τ → Differentiable ℝ (fun s : ℝ => PSum ℓ d τ s)) :
    ∀ k l : ℕ, ∃ c N : ℝ, 0 ≤ c ∧ 0 ≤ N ∧ ∀ (τ : UpperHalfPlane) (r : ℝ), Funnel τ →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => funnelLayer ℓ d τ s) r‖
        ≤ c * (scale τ) ^ N := by
  intro k l
  obtain ⟨c, N, hc, hN, hbound⟩ := hPSum k l
  refine ⟨c, N, hc, hN, ?_⟩
  intro τ r hτ
  have hcN : 0 ≤ c * (scale τ) ^ N :=
    mul_nonneg hc (Real.rpow_nonneg (scale_pos τ).le N)
  by_cases hreg : r ≠ 0 ∧ (d = 8 ∨ 2 < r ^ 2)
  · have hreg' : d = 8 ∨ 2 ≤ r ^ 2 := by
      rcases hreg.2 with h | h
      · exact Or.inl h
      · exact Or.inr (le_of_lt h)
    have hev1 : (fun s : ℝ => funnelLayer ℓ d τ s)
        =ᶠ[𝓝 r] (fun s : ℝ => paperLayer (Gcusp ℓ d) ℓ d τ s) := by
      refine Filter.eventually_of_mem ((isOpen_convergenceRegion d).mem_nhds hreg) ?_
      intro s hs
      exact funnelLayer_of_mem ℓ d τ hs
    have hev2 : (fun s : ℝ => paperLayer (Gcusp ℓ d) ℓ d τ s)
        =ᶠ[𝓝 r] (fun s : ℝ => PSum ℓ d τ s) := by
      refine Filter.eventually_of_mem ((isOpen_convergenceRegion d).mem_nhds hreg) ?_
      intro s hs
      exact hDecomp τ s hτ hs.1 hs.2
    rw [iteratedDeriv_congr_of_eventuallyEq hev1 l, iteratedDeriv_congr_of_eventuallyEq hev2 l]
    exact hbound τ r hτ hreg'
  · rcases hd with h8 | h24
    · -- dimension `8`: off the region means `r = 0`
      have hr : r = 0 := by
        by_contra h
        exact hreg ⟨h, Or.inl h8⟩
      subst hr
      rcases Nat.eq_zero_or_pos l with hl | hl
      · subst hl
        rw [iteratedDeriv_zero, funnelLayer_of_not_mem ℓ d τ hreg, norm_zero, mul_zero]
        exact hcN
      · obtain ⟨l', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl.ne'
        have hfun : (fun s : ℝ => funnelLayer ℓ d τ s)
            = fun s : ℝ => if s = 0 then 0 else PSum ℓ d τ s := by
          funext s
          rcases eq_or_ne s 0 with hs | hs
          · subst hs
            rw [if_pos rfl]
            exact funnelLayer_of_not_mem ℓ d τ hreg
          · rw [if_neg hs, funnelLayer_of_mem ℓ d τ ⟨hs, Or.inl h8⟩,
              hDecomp τ s hτ hs (Or.inl h8)]
        rw [hfun, punctured_iteratedDeriv (PSum_neg ℓ d τ) (hDiff τ hτ) (l' + 1) (by omega)]
        exact hbound τ 0 hτ (Or.inl h8)
    · -- dimension `24`
      have hd24 : d = 24 := h24
      have hr2 : r ^ 2 ≤ 2 := by
        by_contra h
        simp only [not_le] at h
        exact hreg ⟨fun h0 => by rw [h0] at h; norm_num at h, Or.inr h⟩
      rcases lt_or_eq_of_le hr2 with hlt | heq
      · -- `r ^ 2 < 2`: the truncated layer vanishes on a neighbourhood
        have hev : (fun s : ℝ => funnelLayer ℓ d τ s) =ᶠ[𝓝 r] (fun _ : ℝ => (0 : ℂ)) := by
          refine Filter.eventually_of_mem
            ((isOpen_lt (continuous_id.pow 2) continuous_const).mem_nhds hlt) ?_
          intro s hs
          exact funnelLayer_eq_zero_of_sq_le hd24 hs.le
        rw [iteratedDeriv_congr_of_eventuallyEq hev l, iteratedDeriv_zeroFun l r,
          norm_zero, mul_zero]
        exact hcN
      · -- `r ^ 2 = 2`
        have hrne : r ≠ 0 := fun h0 => by rw [h0] at heq; norm_num at heq
        rcases Nat.eq_zero_or_pos l with hl | hl
        · subst hl
          rw [iteratedDeriv_zero, funnelLayer_of_not_mem ℓ d τ hreg, norm_zero, mul_zero]
          exact hcN
        · obtain ⟨l', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl.ne'
          have hvanish : ∀ y : ℝ, y ^ 2 < 2 → funnelLayer ℓ d τ y = 0 :=
            fun y hy => funnelLayer_eq_zero_of_sq_le hd24 hy.le
          have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
          have hsnn : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
          rcases lt_or_gt_of_ne hrne with hlt0 | hgt0
          · -- `r < 0`, so `r = -√2`
            have hrneg : r = -(Real.sqrt 2) := by
              have hsq : r ^ 2 = (Real.sqrt 2) ^ 2 := by rw [hs2]; exact heq
              rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
              · exfalso; rw [h] at hlt0; linarith [hsnn]
              · exact h
            subst hrneg
            have hz : iteratedDeriv (l' + 1) (fun s : ℝ => funnelLayer ℓ d τ s)
                (-(Real.sqrt 2)) = 0 :=
              iteratedDeriv_succ_eq_zero_of_eqOn_Ioo_right (by linarith [hsnn])
                (fun y hy => hvanish y (by nlinarith [hy.1, hy.2, hs2, hsnn])) l'
            rw [hz, norm_zero, mul_zero]
            exact hcN
          · -- `r > 0`, so `r = √2`
            have hrsqrt : r = Real.sqrt 2 := by
              have hsq : r ^ 2 = (Real.sqrt 2) ^ 2 := by rw [hs2]; exact heq
              rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
              · exact h
              · exfalso; rw [h] at hgt0; linarith [hsnn]
            subst hrsqrt
            have hz : iteratedDeriv (l' + 1) (fun s : ℝ => funnelLayer ℓ d τ s)
                (Real.sqrt 2) = 0 :=
              iteratedDeriv_succ_eq_zero_of_eqOn_Ioo_left (Real.sqrt_pos.mpr (by norm_num))
                (fun y hy => hvanish y (by
                  nlinarith [hy.1, hy.2, hs2, hsnn])) l'
            rw [hz, norm_zero, mul_zero]
            exact hcN

theorem funnel_target_of_pieces (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hPSumDiff : ∀ (τ : UpperHalfPlane), Funnel τ → Differentiable ℝ (fun s : ℝ => PSum ℓ d τ s))
    (hPSumBd : ∀ k l : ℕ, ∃ c N : ℝ, 0 ≤ c ∧ 0 ≤ N ∧
      ∀ (τ : UpperHalfPlane) (r : ℝ), Funnel τ → (d = 8 ∨ 2 ≤ r ^ 2) →
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => PSum ℓ d τ s) r‖ ≤ c * (scale τ) ^ N)
    (hDecomp : ∀ (τ : UpperHalfPlane) (r : ℝ), Funnel τ → r ≠ 0 → (d = 8 ∨ 2 < r ^ 2) →
      paperLayer (Gcusp ℓ d) ℓ d τ r = PSum ℓ d τ r)
    (hAgree : ∀ (τ : UpperHalfPlane) (r : ℝ), Funnel τ → r ≠ 0 → (d = 8 ∨ 2 < r ^ 2) →
      IntegrableOn (fun t : ℝ => Kaxis (Kfun ℓ d) τ t
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0) →
      paperLayer (Gcusp ℓ d) ℓ d τ r = kernelTransform (Kfun ℓ d) τ r)
    (hZero : ∀ (τ : UpperHalfPlane) (r : ℝ), Funnel τ → r ≠ 0 →
      ¬ (d = 8 ∨ 2 < r ^ 2) → kernelTransform (Kfun ℓ d) τ r = 0) :
    ∀ k l : ℕ, ∃ α β γ δ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ 0 ≤ δ ∧
      ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ DomainD → 2 ≤ τ.im →
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          kernelTransform (Kfun ℓ d) τ s) r‖
          ≤ α * (τ.im) ^ (-β) + γ * (‖(τ : ℂ)‖) ^ δ := by
  have hsemi := funnelLayer_seminorm ℓ d hd hPSumBd hDecomp hPSumDiff
  have htr := funnel_transfer ℓ d (funnelLayer ℓ d)
    (fun τ _ => by
      rw [funnelLayer_of_not_mem ℓ d τ (by
        rintro ⟨h, -⟩; exact h rfl), kernelTransform_zero])
    (fun τ hτ r hr hint => by
      by_cases hcase : d = 8 ∨ 2 < r ^ 2
      · rw [funnelLayer_of_mem ℓ d τ ⟨hr, hcase⟩]
        exact hAgree τ r hτ hr hcase hint
      · rw [funnelLayer_of_not_mem ℓ d τ (fun h => hcase h.2), hZero τ r hτ hr hcase])
    hsemi
  intro k l
  obtain ⟨c, N, hc, hN, hb⟩ := htr k l
  refine ⟨c * 3 ^ N, N, c * 3 ^ N, N, by positivity, hN, by positivity, hN, ?_⟩
  intro τ r hτ hτ2
  have h1 := hb τ r ⟨hτ, hτ2⟩
  have h2 := scale_rpow_le (τ := τ) hN
  calc (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => kernelTransform (Kfun ℓ d) τ s) r‖
      ≤ c * (scale τ) ^ N := h1
    _ ≤ c * (3 ^ N * ((τ.im) ^ (-N) + ‖(τ : ℂ)‖ ^ N)) := mul_le_mul_of_nonneg_left h2 hc
    _ = c * 3 ^ N * (τ.im) ^ (-N) + c * 3 ^ N * ‖(τ : ℂ)‖ ^ N := by ring


end

end Work.Asymptotics
