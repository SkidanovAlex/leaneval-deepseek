import Mathlib
import Submission.Work.Repel.V10.fN_lift_eq
import Submission.Work.Repel.V10.chain_v9_src
import Submission.Work.Repel.V10.chain_v9_diff
import Submission.Work.Repel.V10.chain_v9_walk
import Submission.Work.Repel.V10.SrcC_isConnected
import Submission.Work.Repel.V10.SrcC_sub_Dflat
import Submission.Work.Repel.V10.uOf_differentiableOn
import Submission.Work.L62.chain
import Submission.Work.Repel.walk_of_sub

/-!
# `Work.Repel.deriv_relation` : the derivative of the §6 composite

Shishikura's §6 composite for a cell `q = (j,k,n)` is

  `z --(φ₀|box)⁻¹--> w₀ --s·π--> ζ --(φ₁|Dsm)⁻¹--> u ∈ W j + k --ĥ^j--> u' ∈ W 0
     --π⁻¹--> w₁ --φ₀--> z'`,

and `V.SrcC_uniform_iterate` supplies a single iterate `N` with `f^[N] (φ₀ w) = φ₀ (wOfCell q w)`
on the whole source region `SrcC q`.  Differentiating that identity along the explicit lift
`V.lift q : fib j k → SrcC q` gives an identity of two products of derivatives: on the source
side the chain rule for `w ↦ f^[N] (φ₀ (lift w))`, on the target side the chain rule for
`w ↦ φ₀ (wOf (ĥ^[j] w - k))` (the two functions agree on the fibre `fib j k`, an open set).

The two composites agree on a *neighbourhood* of `u`: `fib j k = W j + k` is open, contains `u`,
and for `w ∈ fib j k` the lift `lift w` lies in `SrcC q`, where the uniform iterate identity holds;
moreover `uOf (s·π (lift w)) = w` because `π (lift w) = φ₁ w / s`, so that
`wOfCell q (lift w) = wOf (ĥ^[j] w - k)` (`wOfCell` is `wOf ∘ uOfSrc`).
-/

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology

noncomputable section

/-- The explicit lift `V.lift j k n = w_c + n + log (φ₁ u / φ₁ (u_c+k)) / (2πi)` is complex
differentiable at every point of the fibre `V.fib j k` (where `φ₁` does not vanish and the ratio
`φ₁ u / φ₁(u_c+k)` lies in the slit plane). -/
lemma lift_differentiableAt (V : Work.Repel.V10) {j : ℕ} {k n : ℤ} (hSm : V.fib j k ⊆ V.Sm1)
    {u : ℂ} (hu : u ∈ V.fib j k) : DifferentiableAt ℂ (V.lift j k n) u := by
  have hmem : V.P₁.φ u / V.P₁.φ (V.uc j + ((k : ℤ) : ℂ)) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    have h1 : ‖V.P₁.φ u / V.P₁.φ (V.uc j + ((k : ℤ) : ℂ)) - 1‖ ≤ 1 / 2 :=
      V10.phi_div_sub_one_le V hSm hu (V.uc_fib j k)
    have h2 : -(‖V.P₁.φ u / V.P₁.φ (V.uc j + ((k : ℤ) : ℂ)) - 1‖)
        ≤ (V.P₁.φ u / V.P₁.φ (V.uc j + ((k : ℤ) : ℂ)) - 1).re :=
      (abs_le.mp (Complex.abs_re_le_norm _)).1
    simp only [Complex.sub_re, Complex.one_re] at h2
    linarith
  have hdφ : HasDerivAt V.P₁.φ (deriv V.P₁.φ u) u :=
    (V.P₁.φ_holo.differentiableAt (V.P₁.Dφ_open.mem_nhds (V.Sm1_sub_Dφ (hSm hu)))).hasDerivAt
  have h2 : HasDerivAt (fun u => Complex.log (V.P₁.φ u / V.P₁.φ (V.uc j + ((k : ℤ) : ℂ))))
      ((deriv V.P₁.φ u / V.P₁.φ (V.uc j + ((k : ℤ) : ℂ))) /
        (V.P₁.φ u / V.P₁.φ (V.uc j + ((k : ℤ) : ℂ)))) u :=
    (hdφ.div_const _).clog hmem
  have h3 := h2.div_const (2 * Real.pi * Complex.I)
  have h4 : HasDerivAt (V.lift j k n)
      (((deriv V.P₁.φ u / V.P₁.φ (V.uc j + ((k : ℤ) : ℂ))) /
        (V.P₁.φ u / V.P₁.φ (V.uc j + ((k : ℤ) : ℂ)))) / (2 * Real.pi * Complex.I)) u := by
    have hsum : HasDerivAt ((fun _ : ℂ => V.wc j k + ((n : ℤ) : ℂ)) +
        fun x => Complex.log (V.P₁.φ x / V.P₁.φ (V.uc j + ((k : ℤ) : ℂ))) /
          (2 * Real.pi * Complex.I))
        (0 + ((deriv V.P₁.φ u / V.P₁.φ (V.uc j + ((k : ℤ) : ℂ))) /
          (V.P₁.φ u / V.P₁.φ (V.uc j + ((k : ℤ) : ℂ)))) / (2 * Real.pi * Complex.I)) u :=
      (hasDerivAt_const (x := u) (V.wc j k + ((n : ℤ) : ℂ))).add h3
    have hfun : V.lift j k n = (fun _ : ℂ => V.wc j k + ((n : ℤ) : ℂ)) +
        fun x => Complex.log (V.P₁.φ x / V.P₁.φ (V.uc j + ((k : ℤ) : ℂ))) /
          (2 * Real.pi * Complex.I) := by
      ext x
      simp [V10.lift, Pi.add_apply]
    rw [hfun]
    simpa only [zero_add] using hsum
  exact h4.differentiableAt

theorem deriv_relation (V : Work.Repel.V10) {j : ℕ} (hj : 1 ≤ j) {k n : ℤ} (hSm : V.fib j k ⊆ V.Sm1)
    (hn : |((n : ℤ) : ℝ)| ≤ V.η / 10 + 1) {N : ℕ}
    (hN : ∀ w ∈ V.SrcC j k n, V.f ^[N] (V.P₀.φ w) = V.P₀.φ (V.wOfCell (j, k, n) w))
    {u : ℂ} (hu : u ∈ V.fib j k) :
    deriv (V.f ^[N]) (V.P₀.φ (V.lift j k n u)) * deriv V.P₀.φ (V.lift j k n u)
        * deriv (V.lift j k n) u
      = deriv V.P₀.φ (V.wOf (((fun x : ℂ => V.R x - V.β)^[j] u) - ((k : ℤ) : ℂ)))
        * deriv V.wOf (((fun x : ℂ => V.R x - V.β)^[j] u) - ((k : ℤ) : ℂ))
        * deriv ((fun x : ℂ => V.R x - V.β)^[j]) u := by
  -- the source point of the cell, and its level-1 target
  have hw₀ : V.lift j k n u ∈ V.SrcC j k n := by
    rw [V10.SrcC_eq_image_lift V hSm]
    exact ⟨u, hu, rfl⟩
  have hv : (fun x : ℂ => V.R x - V.β)^[j] u - ((k : ℤ) : ℂ) ∈ V.W 0 :=
    chain_image_mem V hu
  -- differentiability of the individual factors
  have hdφ₀ : DifferentiableAt ℂ V.P₀.φ (V.lift j k n u) :=
    V.P₀.φ_holo.differentiableAt (V.P₀.Dφ_open.mem_nhds (V.SrcC_sub_Dφ hSm hn hw₀))
  have hdlift : DifferentiableAt ℂ (V.lift j k n) u := lift_differentiableAt V hSm hu
  have hdN : DifferentiableAt ℂ (V.f ^[N]) (V.P₀.φ (V.lift j k n u)) :=
    (V.hfdiff.iterate N).differentiableAt
  have hcomp : DifferentiableAt ℂ (fun w : ℂ => V.P₀.φ (V.lift j k n w)) u :=
    hdφ₀.comp (x := u) hdlift
  have hdwOf : DifferentiableAt ℂ V.wOf ((fun x : ℂ => V.R x - V.β)^[j] u - ((k : ℤ) : ℂ)) := by
    have hWopen : V.W 0 ∈ 𝓝 ((fun x : ℂ => V.R x - V.β)^[j] u - ((k : ℤ) : ℂ)) := by
      rw [V.hbase]
      exact Metric.isOpen_ball.mem_nhds (by rwa [V.hbase] at hv)
    exact V.wOf_differentiableOn.differentiableAt hWopen
  have hdφ₀wOf : DifferentiableAt ℂ V.P₀.φ
      (V.wOf ((fun x : ℂ => V.R x - V.β)^[j] u - ((k : ℤ) : ℂ))) :=
    V.P₀.φ_holo.differentiableAt
      (V.P₀.Dφ_open.mem_nhds (V.hsub₀ (V.wOf_spec hv).1))
  have hditer : DifferentiableAt ℂ ((fun x : ℂ => V.R x - V.β)^[j]) u :=
    wOfCell_differentiableAt_iterate V.hRdiff
      (fun i hi => V.hDRopen.mem_nhds (wOfCell_walk_mem_DR V.hIsChain V.hReq hu i hi))
  have hdsub : DifferentiableAt ℂ
      (fun w : ℂ => (fun x : ℂ => V.R x - V.β)^[j] w - ((k : ℤ) : ℂ)) u :=
    hditer.sub_const _
  have hdwOfsub : DifferentiableAt ℂ
      (fun w : ℂ => V.wOf ((fun x : ℂ => V.R x - V.β)^[j] w - ((k : ℤ) : ℂ))) u := by
    have hh := hdwOf.comp (x := u) hdsub
    simpa only [Function.comp_def] using hh
  -- the two composites agree on the (open) fibre
  have hfibopen : IsOpen (V.fib j k) :=
    (Homeomorph.isOpen_image (Homeomorph.addRight ((k : ℤ) : ℂ))).mpr
      (V.hIsChain.open_conn j).1
  have heq : (fun w : ℂ => V.f ^[N] (V.P₀.φ (V.lift j k n w)))
      =ᶠ[𝓝 u] fun w : ℂ =>
        V.P₀.φ (V.wOf ((fun x : ℂ => V.R x - V.β)^[j] w - ((k : ℤ) : ℂ))) := by
    filter_upwards [hfibopen.mem_nhds hu] with w hw
    have hwsrc : V.lift j k n w ∈ V.SrcC j k n := by
      rw [V10.SrcC_eq_image_lift V hSm]
      exact ⟨w, hw, rfl⟩
    rw [hN (V.lift j k n w) hwsrc]
    congr 1
    rw [V10.wOfCell, V10.uOfSrc]
    congr 2
    have hpi : V.s * MandelDim.piExp (V.lift j k n w) = V.P₁.φ w := by
      rw [V.lift_piExp (n := n) hSm hw, mul_div_cancel₀ _ V.hs]
    rw [hpi, V.uOf_unique (hSm hw) rfl]
  -- the chain rule on the source side
  have hF : deriv (fun w : ℂ => V.f ^[N] (V.P₀.φ (V.lift j k n w))) u
      = deriv (V.f ^[N]) (V.P₀.φ (V.lift j k n u)) * deriv V.P₀.φ (V.lift j k n u)
        * deriv (V.lift j k n) u := by
    have h1 : deriv (fun w : ℂ => V.P₀.φ (V.lift j k n w)) u
        = deriv V.P₀.φ (V.lift j k n u) * deriv (V.lift j k n) u := by
      show deriv (V.P₀.φ ∘ fun w : ℂ => V.lift j k n w) u = _
      rw [deriv_comp u hdφ₀ hdlift]
    show deriv ((V.f ^[N]) ∘ fun w : ℂ => V.P₀.φ (V.lift j k n w)) u = _
    rw [deriv_comp u hdN hcomp, h1]
    ring
  -- the chain rule on the target side
  have hG : deriv (fun w : ℂ =>
        V.P₀.φ (V.wOf ((fun x : ℂ => V.R x - V.β)^[j] w - ((k : ℤ) : ℂ)))) u
      = deriv V.P₀.φ (V.wOf ((fun x : ℂ => V.R x - V.β)^[j] u - ((k : ℤ) : ℂ)))
        * deriv V.wOf ((fun x : ℂ => V.R x - V.β)^[j] u - ((k : ℤ) : ℂ))
        * deriv ((fun x : ℂ => V.R x - V.β)^[j]) u := by
    have h1 : deriv (fun w : ℂ =>
          V.wOf ((fun x : ℂ => V.R x - V.β)^[j] w - ((k : ℤ) : ℂ))) u
        = deriv V.wOf ((fun x : ℂ => V.R x - V.β)^[j] u - ((k : ℤ) : ℂ))
          * deriv ((fun x : ℂ => V.R x - V.β)^[j]) u := by
      show deriv (V.wOf ∘ fun w : ℂ =>
          (fun x : ℂ => V.R x - V.β)^[j] w - ((k : ℤ) : ℂ)) u = _
      rw [deriv_comp u hdwOf hdsub, deriv_sub_const]
    show deriv (V.P₀.φ ∘ fun w : ℂ =>
        V.wOf ((fun x : ℂ => V.R x - V.β)^[j] w - ((k : ℤ) : ℂ))) u = _
    rw [deriv_comp u hdφ₀wOf hdwOfsub, h1]
    ring
  rw [← hF, ← hG]
  exact heq.deriv_eq

end

end Work.Repel
