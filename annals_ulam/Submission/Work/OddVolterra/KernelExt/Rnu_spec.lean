import Mathlib
import Submission.Work.OddVolterra.KernelExt.Defs

/-!
# The defining property of the Bell numerator `Rnu`

`Work.OddVolterra.KernelExt.Rnu` is the recursion

`R_0 = init`,   `R_{m+1} = Z·∂_s R_m + (ν - m)·(∂_s Z)·R_m`

(where `∂_s` is the derivative in the first coordinate of the triple `(s,σ,t)`), which is
the classical recursion for the polynomial `(∂/∂s)^m[Z^ν · init] · Z^{m-ν}`.  This file
proves that this is exactly what `Rnu` computes, on the region where the radicand
`Z = Zrad h (s,σ,t)` is positive:

`Rnu ν h init m (s,σ,t) = ∂_s^m (u ↦ Zrad h (u,σ,t)^ν · init (u,σ,t)) · Zrad h (s,σ,t)^{m-ν}`.

The only place where the hypothesis `0 < Z` is used is the local differentiability of
`u ↦ Z^ν` (`Real.rpow` is nice exactly where the base is non-zero), together with the
exponent bookkeeping `Z^{ν-m}·Z^{m-ν} = Z^0 = 1`.

## The induction

The identity is proved by induction on `m` at every point `u` where `Z(u) > 0`, in the form

`∂_s^m F (u) = Rnu … m u · Z(u)^{ν-m}`   (`F u = Z(u)^ν · init u`).

For the induction step, `deriv` is local: the induction hypothesis, valid on the open
neighbourhood `{Z > 0}` of `u`, identifies `∂_s^m F` with `u ↦ Rnu … m u · Z(u)^{ν-m}` near
`u`, so the product rule (with `Real.hasDerivAt_rpow_const` for the second factor) computes
the next derivative.  `Z^{ν-m} = Z · Z^{ν-m-1}` converts the two sides into each other.
-/

namespace Work.OddVolterra.KernelExt

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

open Work.OddVolterra.KernelExt
open Work.OddVolterra (line)

noncomputable section

/-- `Zrad` is smooth whenever `h` is. -/
theorem Zrad_contDiff_aux {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) : ContDiff ℝ (⊤ : ℕ∞) (Zrad h) := by
  unfold Zrad line
  fun_prop

/-- `Rnu` is smooth whenever `h` and `init` are: the recursion only uses `fderiv` of
already smooth functions and evaluation against the constant vector `(1,0,0)`. -/
theorem Rnu_contDiff_aux (ν : ℝ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {init : ℝ × ℝ × ℝ → ℝ} (hinit : ContDiff ℝ (⊤ : ℕ∞) init) :
    ∀ m, ContDiff ℝ (⊤ : ℕ∞) (Rnu ν h init m) := by
  intro m
  induction m with
  | zero => rw [Rnu]; exact hinit
  | succ m ih =>
    rw [Rnu]
    have hZ : ContDiff ℝ (⊤ : ℕ∞) (Zrad h) := Zrad_contDiff_aux hh
    have hZf : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × ℝ => (fderiv ℝ (Zrad h) p) (1, 0, 0)) :=
      (hZ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    have hmf : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × ℝ => (fderiv ℝ (Rnu ν h init m) p) (1, 0, 0)) :=
      (ih.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    exact (hZ.mul hmf).add ((contDiff_const.mul hZf).mul ih)

/-- The derivative along the first coordinate of the triple is the derivative of the
section `u ↦ F (u, σ, t)`. -/
theorem hasDerivAt_section {F : ℝ × ℝ × ℝ → ℝ} (p : ℝ × ℝ × ℝ)
    (hF : DifferentiableAt ℝ F p) :
    HasDerivAt (fun u : ℝ => F (u, p.2.1, p.2.2)) ((fderiv ℝ F p) (1, 0, 0)) p.1 := by
  have hg : HasDerivAt (fun u : ℝ => (u, p.2.1, p.2.2)) (1, 0, 0) p.1 :=
    HasDerivAt.prodMk (hasDerivAt_id p.1) (hasDerivAt_const p.1 (p.2.1, p.2.2))
  simpa [Function.comp_def] using hF.hasFDerivAt.comp_hasDerivAt p.1 hg

/-- **The defining property of `Rnu`.**  On the region where the radicand is positive,
`Rnu ν h init m` is the `m`-th `s`-derivative of `Z^ν · init` multiplied by `Z^{m-ν}`. -/
theorem Rnu_spec (ν : ℝ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {init : ℝ × ℝ × ℝ → ℝ} (hinit : ContDiff ℝ (⊤ : ℕ∞) init) (m : ℕ) (s σ t : ℝ)
    (hz : 0 < Work.OddVolterra.KernelExt.Zrad h (s, σ, t)) :
    Work.OddVolterra.KernelExt.Rnu ν h init m (s, σ, t) =
      iteratedDeriv m
          (fun u : ℝ => (Work.OddVolterra.KernelExt.Zrad h (u, σ, t)) ^ ν * init (u, σ, t)) s
        * (Work.OddVolterra.KernelExt.Zrad h (s, σ, t)) ^ ((m : ℝ) - ν) := by
  have hcontZ : Continuous (fun v : ℝ => Zrad h (v, σ, t)) := by
    unfold Zrad line; fun_prop
  -- The identity at every point where the radicand is positive.
  have key : ∀ m : ℕ, ∀ u : ℝ, 0 < Zrad h (u, σ, t) →
      iteratedDeriv m (fun u : ℝ => (Zrad h (u, σ, t)) ^ ν * init (u, σ, t)) u =
        Rnu ν h init m (u, σ, t) * (Zrad h (u, σ, t)) ^ (ν - (m : ℝ)) := by
    intro m
    induction m with
    | zero =>
      intro u _
      simp only [iteratedDeriv_zero, Rnu, Nat.cast_zero, sub_zero]
      rw [mul_comm]
    | succ m ih =>
      intro u hu
      rw [iteratedDeriv_succ]
      -- `{Z > 0}` is an open neighbourhood of `u`, and there the induction hypothesis
      -- identifies `∂_s^m F` with `u ↦ Rnu … m u · Z(u)^{ν-m}`.
      have hopen : IsOpen {v : ℝ | 0 < Zrad h (v, σ, t)} :=
        isOpen_lt continuous_const hcontZ
      have hmem : {v : ℝ | 0 < Zrad h (v, σ, t)} ∈ 𝓝 u := hopen.mem_nhds hu
      have heq : iteratedDeriv m (fun u : ℝ => (Zrad h (u, σ, t)) ^ ν * init (u, σ, t))
          =ᶠ[𝓝 u] (fun v : ℝ => Rnu ν h init m (v, σ, t) *
            (Zrad h (v, σ, t)) ^ (ν - (m : ℝ))) := by
        filter_upwards [hmem] with v hv
        exact ih v hv
      rw [Filter.EventuallyEq.deriv_eq heq]
      -- Smoothness gives the two derivatives occurring in the product rule.
      have hRmd : DifferentiableAt ℝ (Rnu ν h init m) (u, σ, t) :=
        ((Rnu_contDiff_aux ν hh hinit m).contDiffAt).differentiableAt (by simp)
      have hZd : DifferentiableAt ℝ (Zrad h) (u, σ, t) :=
        ((Zrad_contDiff_aux hh).contDiffAt).differentiableAt (by simp)
      have h1 : HasDerivAt (fun v : ℝ => Rnu ν h init m (v, σ, t))
          ((fderiv ℝ (Rnu ν h init m) (u, σ, t)) (1, 0, 0)) u := hasDerivAt_section _ hRmd
      have h2 : HasDerivAt (fun v : ℝ => Zrad h (v, σ, t))
          ((fderiv ℝ (Zrad h) (u, σ, t)) (1, 0, 0)) u := hasDerivAt_section _ hZd
      have h3 : HasDerivAt (fun v : ℝ => (Zrad h (v, σ, t)) ^ (ν - (m : ℝ)))
          (((fderiv ℝ (Zrad h) (u, σ, t)) (1, 0, 0)) * (ν - (m : ℝ)) *
            (Zrad h (u, σ, t)) ^ (ν - (m : ℝ) - 1)) u :=
        h2.rpow_const (Or.inl (ne_of_gt hu))
      -- Put the goal's function into the product form produced by `HasDerivAt.mul`.
      have hfun : (fun v : ℝ => Rnu ν h init m (v, σ, t) * Zrad h (v, σ, t) ^ (ν - (m : ℝ)))
          = ((fun v : ℝ => Rnu ν h init m (v, σ, t)) *
              (fun v : ℝ => Zrad h (v, σ, t) ^ (ν - (m : ℝ)))) := rfl
      rw [hfun, (h1.mul h3).deriv, Rnu]
      -- Exponent bookkeeping: `Z^{ν-m} = Z·Z^{ν-m-1}` and `ν-(m+1) = ν-m-1`.
      have hexp : ν - ((m + 1 : ℕ) : ℝ) = ν - (m : ℝ) - 1 := by push_cast; ring
      rw [hexp]
      have hAw : (Zrad h (u, σ, t)) ^ (ν - (m : ℝ)) =
          Zrad h (u, σ, t) * (Zrad h (u, σ, t)) ^ (ν - (m : ℝ) - 1) := by
        conv_lhs => rw [show ν - (m : ℝ) = (ν - (m : ℝ) - 1) + 1 from by ring]
        rw [Real.rpow_add hu, Real.rpow_one]
        ring
      rw [hAw]
      ring
  -- Apply the identity at `u = s` and absorb `Z^{ν-m}·Z^{m-ν} = Z^0 = 1`.
  have hmain := key m s hz
  rw [hmain, mul_assoc, ← Real.rpow_add hz]
  have hexp : (ν - (m : ℝ)) + ((m : ℝ) - ν) = 0 := by ring
  rw [hexp, Real.rpow_zero, mul_one]

end

end Work.OddVolterra.KernelExt
