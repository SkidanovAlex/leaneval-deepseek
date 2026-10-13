import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Bootstrap of the angular regularity for the ODE `Lzero u = h`

The `α = 0` part of the elliptic operator of Elgindi's elliptic section,
`Work.Elliptic.Lzero Ψ = -∂_θθΨ + ∂_θ(tan θ · Ψ) - 6Ψ`, is an *ordinary* differential
operator of order two in `θ` for functions that do not depend on the radial variable `z`:
for `Ψ = fun _ θ' => f θ'` one has

  `Lzero Ψ z θ = -f''(θ) + (tan θ · f)'(θ) - 6 f(θ)`.

Hence the equation `Lzero Ψ 0 · = h` can be solved for `f''`,

  `f'' = (tan · f)' - 6 f - h`   on `(0, π/2)`,

and since the right hand side is `C^{m-1}` as soon as `f` is `C^m` and `h` is `C^{m-1}`
(`tan` being smooth on `(0, π/2)`), one gets one more derivative for free: `f` is `C^{m+1}`.
This is the `LzeroBootstrap` below.  It is the standard gain of regularities used to read off
regularity of an angular profile from the regularity of its `Lzero`-image, and it is what lets
downstream arguments replace `h` by `Lzero` of a smooth function without losing control.

The statement does not need the assumption `2 ≤ m` in full strength: `m ≥ 1` suffices
(`m ≥ 2` is what the hypotheses of the original statement give).  We keep the hypothesis as
requested.
-/

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.FlatWAux.MomentChiaAux

/-- The `θ`-slice of `Lzero` on functions that do not depend on `z`: for `Ψ = fun _ θ' => f θ'`
and any `z` (in particular `z = 0`),

  `Lzero Ψ z θ = -f''(θ) + (tan θ · f)'(θ) - 6 f(θ)`. -/
theorem Lzero_of_thetaOnly (f : ℝ → ℝ) (z θ : ℝ) :
    Work.Elliptic.Lzero (fun _ θ' => f θ') z θ
      = -deriv (deriv f) θ + deriv (fun t => Real.tan t * f t) θ - 6 * f θ := by
  simp only [Work.Elliptic.Lzero, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero,
    Work.Spaces.pth]

/-- `tan` is smooth on the angular interval `(0, π/2)`. -/
theorem contDiffOn_tan_Ioo : ContDiffOn ℝ ⊤ Real.tan (Set.Ioo 0 (Real.pi / 2)) := by
  intro x hx
  rw [contDiffWithinAt_iff_contDiffAt (isOpen_Ioo.mem_nhds hx)]
  exact Real.contDiffAt_tan.2
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hx.1], hx.2⟩).ne'

/-- **Bootstrap of angular regularity.**  If `f` is `C^m` on `(0, π/2)` and
`θ ↦ Lzero (fun _ θ' => f θ') 0 θ` is `C^{m-1}` there, then `f` is `C^{m+1}`.

The point is that the equation can be solved for the second derivative,

`f'' = (tan · f)' - 6 f - h`  on `(0, π/2)`,

and the right hand side is one order more regular than `f`, so the second derivative of `f` is
`C^{m-1}` while `f` itself is already `C^m`. -/
theorem LzeroBootstrap {f h : ℝ → ℝ} {m : ℕ} (hm : 2 ≤ m)
    (hf : ContDiffOn ℝ m f (Set.Ioo 0 (Real.pi / 2)))
    (hh : ContDiffOn ℝ (m - 1) h (Set.Ioo 0 (Real.pi / 2)))
    (heq : ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Elliptic.Lzero (fun _ θ' => f θ') 0 θ = h θ) :
    ContDiffOn ℝ (m + 1) f (Set.Ioo 0 (Real.pi / 2)) := by
  set s : Set ℝ := Set.Ioo 0 (Real.pi / 2) with hs
  have hs_open : IsOpen s := isOpen_Ioo
  have hm1 : 1 ≤ m := by omega
  -- the coercion `ℕ → ℕ∞ω` is additive, and `(m - 1) + 1 = m` since `m ≥ 1`
  have hcast : (((m - 1 : ℕ)) : ℕ∞ω) + 1 = (m : ℕ∞ω) := by
    have h : m - 1 + 1 = m := Nat.sub_add_cancel hm1
    exact_mod_cast h
  -- **Step 1.**  The equation, solved for the second derivative of `f`.
  have hpt : ∀ θ ∈ s, deriv (deriv f) θ
      = deriv (fun t => Real.tan t * f t) θ - 6 * f θ - h θ := by
    intro θ hθ
    have h1 := heq θ hθ
    rw [Lzero_of_thetaOnly f 0 θ] at h1
    linarith
  -- **Step 2.**  The right hand side is `C^{m-1}` on `s`.
  have htan : ContDiffOn ℝ m Real.tan s := contDiffOn_tan_Ioo.of_le le_top
  have htf : ContDiffOn ℝ m (fun θ => Real.tan θ * f θ) s := htan.mul hf
  have hdtf : ContDiffOn ℝ (m - 1) (deriv (fun θ => Real.tan θ * f θ)) s :=
    ContDiffOn.deriv_of_isOpen htf hs_open (le_of_eq hcast)
  have hf_le : ContDiffOn ℝ (m - 1) f s := hf.of_le (by
    calc (((m - 1 : ℕ)) : ℕ∞ω) ≤ (((m - 1 : ℕ)) : ℕ∞ω) + 1 := le_self_add
      _ = (m : ℕ∞ω) := hcast)
  have h6f : ContDiffOn ℝ (m - 1) (fun θ => (6 : ℝ) * f θ) s :=
    contDiffOn_const.mul hf_le
  have hg : ContDiffOn ℝ (m - 1)
      (fun θ => deriv (fun t => Real.tan t * f t) θ - 6 * f θ - h θ) s :=
    ((hdtf.sub h6f).sub hh).congr (fun _ _ => rfl)
  -- **Step 3.**  Transfer to the actual second derivative of `f`.
  have hdd : ContDiffOn ℝ (m - 1) (deriv (deriv f)) s :=
    hg.congr (fun θ hθ => hpt θ hθ)
  -- **Step 4.**  `deriv f` is `C^m`.
  have hdf' : ContDiffOn ℝ (m - 1) (deriv f) s :=
    ContDiffOn.deriv_of_isOpen hf hs_open (le_of_eq hcast)
  have hdiff : DifferentiableOn ℝ (deriv f) s := by
    refine hdf'.differentiableOn ?_
    have h : (((m - 1 : ℕ)) : ℕ∞ω) ≠ 0 := by
      exact_mod_cast (by omega : (m - 1) ≠ 0)
    exact h
  have hderivf : ContDiffOn ℝ m (deriv f) s := by
    have hmain : ContDiffOn ℝ ((((m - 1 : ℕ)) : ℕ∞ω) + 1) (deriv f) s :=
      (contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ) (f := deriv f) (s := s)
        (n := (((m - 1 : ℕ)) : ℕ∞ω)) hs_open).mpr
        ⟨hdiff, (fun hc => absurd hc WithTop.coe_ne_top), hdd⟩
    rw [hcast] at hmain
    exact hmain
  -- **Step 5.**  `f` itself is `C^{m+1}`.
  have hfin : ContDiffOn ℝ ((m : ℕ∞ω) + 1) f s :=
    (contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ) (f := f) (s := s)
      (n := (m : ℕ∞ω)) hs_open).mpr
      ⟨hf.differentiableOn (by exact_mod_cast (by omega : m ≠ 0)),
        (fun hc => absurd hc WithTop.coe_ne_top), hderivf⟩
  exact hfin

end Work.FTS.PhiStar.FlatWAux.MomentChiaAux
