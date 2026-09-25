import Mathlib

namespace Work.RHContract.B

open MeasureTheory Filter Asymptotics
open scoped Topology

/-- Second derivative of `z ↦ mellin f (c - z)`.

Since `mellin f (c - z) = ∫_{0}^{∞} t^{c - z - 1} • f t dt`, differentiating twice under the
integral sign multiplies the integrand by `(log t)^2`, giving the stated identity.  The
hypotheses are exactly the ones ensuring convergence of the Mellin integral in the vertical
strip `b < re (c - z) < a` around `z = s`. -/
theorem deriv_deriv_mellin_const_sub {f : ℝ → ℂ} {a b : ℝ} {c s : ℂ}
    (hfc : MeasureTheory.LocallyIntegrableOn f (Set.Ioi 0))
    (hf_top : Asymptotics.IsBigO Filter.atTop f (fun x : ℝ => x ^ (-a)))
    (hs_top : (c - s).re < a)
    (hf_bot : Asymptotics.IsBigO (nhdsWithin 0 (Set.Ioi 0)) f (fun x : ℝ => x ^ (-b)))
    (hs_bot : b < (c - s).re) :
    deriv (deriv (fun z : ℂ => mellin f (c - z))) s
      = mellin (fun t : ℝ => (Real.log t) ^ 2 • f t) (c - s) := by
  -- `log • f` is again locally integrable on `(0, ∞)`.
  have hli : LocallyIntegrableOn (fun t : ℝ => Real.log t • f t) (Set.Ioi 0) :=
    hfc.continuousOn_smul isOpen_Ioi.isLocallyClosed
      (Real.continuousOn_log.mono (fun t ht => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact ne_of_gt ht))
  -- Exponents shifted slightly so that `log • f` still falls off fast enough.
  obtain ⟨a', ha'1, ha'2⟩ := exists_between hs_top
  obtain ⟨b', hb'1, hb'2⟩ := exists_between hs_bot
  have hlog_top : (fun t : ℝ => Real.log t • f t) =O[atTop] (fun x : ℝ => x ^ (-a')) :=
    isBigO_rpow_top_log_smul ha'2 hf_top
  have hlog_bot : (fun t : ℝ => Real.log t • f t) =O[𝓝[>] 0] (fun x : ℝ => x ^ (-b')) :=
    isBigO_rpow_zero_log_smul hb'1 hf_bot
  -- The vertical strip on which all the Mellin integrals converge.
  let U : Set ℂ := {z | b < (c - z).re ∧ (c - z).re < a}
  have hUopen : IsOpen U := by
    have hcont : Continuous fun z : ℂ => (c - z).re := by fun_prop
    exact isOpen_Ioo.preimage hcont
  have hsU : s ∈ U := ⟨hs_bot, hs_top⟩
  have chain : ∀ z ∈ U, HasDerivAt (fun w : ℂ => mellin f (c - w))
      (-(mellin (fun t : ℝ => Real.log t • f t) (c - z))) z := by
    intro z hz
    have hm := (mellin_hasDerivAt_of_isBigO_rpow hfc hf_top hz.2 hf_bot hz.1).2
    have hi : HasDerivAt (fun w : ℂ => c - w) (-1) z := (hasDerivAt_id z).const_sub c
    have h := HasDerivAt.comp z hm hi
    have h' : HasDerivAt (fun w : ℂ => mellin f (c - w))
        (mellin (fun t : ℝ => Real.log t • f t) (c - z) * -1) z := h
    rw [mul_neg_one] at h'
    exact h'
  -- The derivative of `z ↦ mellin (log • f) (c - z)` is `z ↦ -mellin (log • log • f) (c - z)`.
  have hd2 : HasDerivAt (fun z : ℂ => mellin (fun t : ℝ => Real.log t • f t) (c - z))
      (-(mellin (fun t : ℝ => Real.log t • (Real.log t • f t)) (c - s))) s := by
    have hm : HasDerivAt (mellin (fun t : ℝ => Real.log t • f t))
        (mellin (fun t : ℝ => Real.log t • (Real.log t • f t)) (c - s)) (c - s) :=
      (mellin_hasDerivAt_of_isBigO_rpow hli hlog_top ha'1 hlog_bot hb'2).2
    have hi : HasDerivAt (fun z : ℂ => c - z) (-1) s := (hasDerivAt_id s).const_sub c
    have h := HasDerivAt.comp s hm hi
    have h' : HasDerivAt (fun z : ℂ => mellin (fun t : ℝ => Real.log t • f t) (c - z))
        (mellin (fun t : ℝ => Real.log t • (Real.log t • f t)) (c - s) * -1) s := h
    rw [mul_neg_one] at h'
    exact h'
  -- On the strip, `deriv (z ↦ mellin f (c - z))` is the explicit negative Mellin transform.
  have hEq : deriv (fun z : ℂ => mellin f (c - z)) =ᶠ[𝓝 s]
      (fun z : ℂ => -(mellin (fun t : ℝ => Real.log t • f t) (c - z))) := by
    filter_upwards [hUopen.mem_nhds hsU] with z hz
    rw [(chain z hz).deriv]
  have key : deriv (fun z : ℂ => -(mellin (fun t : ℝ => Real.log t • f t) (c - z))) s
      = mellin (fun t : ℝ => Real.log t • (Real.log t • f t)) (c - s) := by
    have hd2' : HasDerivAt (fun z : ℂ => -(mellin (fun t : ℝ => Real.log t • f t) (c - z)))
        (-(-(mellin (fun t : ℝ => Real.log t • (Real.log t • f t)) (c - s)))) s := hd2.neg
    rw [hd2'.deriv]
    simp
  rw [Filter.EventuallyEq.deriv_eq hEq, key]
  congr 1
  ext t
  rw [smul_smul, sq]

end Work.RHContract.B
