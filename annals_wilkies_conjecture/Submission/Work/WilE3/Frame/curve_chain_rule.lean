import Mathlib
import Submission.Work.WilE3.Frame.Setup
import Submission.Work.WilE3.Frame.Vcoef
import Submission.Work.WilE3.API.eaEvalC_fderiv_analytic

namespace Work.WilE3.Frame

set_option autoImplicit false
noncomputable section
open Classical Topology Matrix
open WilkiesDesign.E
open Work.WilE3 (jacDet)

variable {k r j : ℕ}

/-! ## §3. The chain rule: `edir` along the curve is `Vdir` -/

/-- The `Pi.single` basis expansion of a vector under a continuous linear functional. -/
theorem clm_apply_pi (L : (Fin k → ℂ) →L[ℂ] ℂ) (V : Fin k → ℂ) :
    L V = ∑ i, V i * L (Pi.single i (1 : ℂ)) := by
  conv_lhs => rw [pi_eq_sum_univ' V]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [ContinuousLinearMap.map_smul, smul_eq_mul]

/-- **One step of the chain rule.**  If `cur` is differentiable at `u` with tangent vector
`VcoefC c h ι l (cur u)` in the direction `e_l`, then the derivative of `K ∘ cur` along `e_l` is the
frame derivative of `K`. -/
theorem edir_comp_eq_Vdir (c : EAChain k r) (h : Fin j → EAPoly k r) (ι : Fin j → Fin k)
    (l : Fin k) (cur : (Fin k → ℂ) → (Fin k → ℂ)) (K : (Fin k → ℂ) → ℂ) (u : Fin k → ℂ)
    (hK : AnalyticAt ℂ K (cur u)) (hcur : HasFDerivAt cur (fderiv ℂ cur u) u)
    (htang : fderiv ℂ cur u (Pi.single l 1) = VcoefC c h ι l (cur u)) :
    edir l (K ∘ cur) u = Vdir c h ι l K (cur u) := by
  have hcomp : HasFDerivAt (K ∘ cur) ((fderiv ℂ K (cur u)) ∘SL (fderiv ℂ cur u)) u :=
    (hK.differentiableAt.hasFDerivAt).comp u hcur
  have hline : HasLineDerivAt ℂ (K ∘ cur)
      (((fderiv ℂ K (cur u)) ∘SL (fderiv ℂ cur u)) (Pi.single l 1)) u (Pi.single l 1) :=
    hcomp.hasLineDerivAt (Pi.single l 1)
  have hderiv : deriv (fun t : ℂ => (K ∘ cur) (u + t • Pi.single l 1)) 0
      = fderiv ℂ K (cur u) (fderiv ℂ cur u (Pi.single l 1)) := by
    rw [hline.deriv, ContinuousLinearMap.comp_apply]
  show deriv (fun t : ℂ => (K ∘ cur) (u + t • Pi.single l 1)) 0 = Vdir c h ι l K (cur u)
  rw [hderiv, htang]
  show fderiv ℂ K (cur u) (VcoefC c h ι l (cur u))
      = ∑ i, VcoefC c h ι l (cur u) i * fderiv ℂ K (cur u) (Pi.single i 1)
  exact clm_apply_pi (fderiv ℂ K (cur u)) (VcoefC c h ι l (cur u))

/-- `edir` only depends on the germ: functions that agree on a neighbourhood have the same `edir`. -/
theorem edir_congr (l : Fin k) {A B : (Fin k → ℂ) → ℂ} {u : Fin k → ℂ}
    (hAB : A =ᶠ[𝓝 u] B) : edir l A u = edir l B u := by
  have hφ : Filter.Tendsto (fun t : ℂ => u + t • (Pi.single l (1 : ℂ) : Fin k → ℂ)) (𝓝 0) (𝓝 u) := by
    have hc : Continuous fun t : ℂ => u + t • (Pi.single l (1 : ℂ) : Fin k → ℂ) := by fun_prop
    simpa using hc.tendsto 0
  have h1 : (fun t : ℂ => A (u + t • (Pi.single l (1 : ℂ) : Fin k → ℂ))) =ᶠ[𝓝 (0 : ℂ)]
      (fun t : ℂ => B (u + t • (Pi.single l (1 : ℂ) : Fin k → ℂ))) :=
    hAB.comp_tendsto hφ
  show deriv (fun t : ℂ => A (u + t • (Pi.single l (1 : ℂ) : Fin k → ℂ))) 0
      = deriv (fun t : ℂ => B (u + t • (Pi.single l (1 : ℂ) : Fin k → ℂ))) 0
  exact h1.deriv_eq

/-- Functions that agree on an open set have the same iterated `edir` on that set. -/
theorem edir_iterate_congr_on (l : Fin k) (n : ℕ) {U : Set (Fin k → ℂ)} (hU : IsOpen U)
    {A B : (Fin k → ℂ) → ℂ} (hAB : ∀ u ∈ U, A u = B u) :
    ∀ u ∈ U, (edir l)^[n] A u = (edir l)^[n] B u := by
  induction n with
  | zero => intro u hu; rw [Function.iterate_zero_apply, Function.iterate_zero_apply]; exact hAB u hu
  | succ n ih =>
      intro u hu
      have hmem : ∀ᶠ u' in 𝓝 u, u' ∈ U := hU.mem_nhds hu
      have hcongr : (edir l)^[n] A =ᶠ[𝓝 u] (edir l)^[n] B :=
        hmem.mono fun u' hu' => ih u' hu'
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact edir_congr l hcongr

/-- **Iterated chain rule along the curve.**  On an open set `U` on which `cur` has tangent
`VcoefC c h ι l` in the direction `e_l` and on which all the `Vdir`-iterates of `K` are analytic,
the iterated `edir`-derivative of `K ∘ cur` is the `Vdir`-word applied to `K`. -/
theorem edir_iterate_comp_eq_Vdir_iterate (c : EAChain k r) (h : Fin j → EAPoly k r)
    (ι : Fin j → Fin k) (l : Fin k) (hl : l ∉ Set.range ι)
    (cur : (Fin k → ℂ) → (Fin k → ℂ)) (U : Set (Fin k → ℂ)) (hUo : IsOpen U)
    (hUd : ∀ u ∈ U, HasFDerivAt cur (fderiv ℂ cur u) u)
    (hUt : ∀ u ∈ U, fderiv ℂ cur u (Pi.single l 1) = VcoefC c h ι l (cur u))
    (K : (Fin k → ℂ) → ℂ)
    (hKa : ∀ n, ∀ u ∈ U, AnalyticAt ℂ ((Vdir c h ι l)^[n] K) (cur u)) :
    ∀ n, ∀ u ∈ U, (edir l)^[n] (K ∘ cur) u = ((Vdir c h ι l)^[n] K) (cur u) := by
  intro n
  induction n with
  | zero => intro u _; simp only [Function.iterate_zero_apply]; rfl
  | succ n ih =>
      intro u hu
      have h0 : (fun u' => (edir l)^[n] (K ∘ cur) u') =ᶠ[𝓝 u]
          fun u' => ((Vdir c h ι l)^[n] K) (cur u') := by
        have hmem : ∀ᶠ u' in 𝓝 u, u' ∈ U := hUo.mem_nhds hu
        exact hmem.mono fun u' hu' => ih u' hu'
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      trans edir l (fun u' => ((Vdir c h ι l)^[n] K) (cur u')) u
      · exact edir_congr l h0
      · exact edir_comp_eq_Vdir c h ι l cur ((Vdir c h ι l)^[n] K) u
          (hKa n u hu) (hUd u hu) (hUt u hu)


end

end Work.WilE3.Frame
