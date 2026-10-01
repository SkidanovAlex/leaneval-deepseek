import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.LinnikAreas.A5.Baux_lim_ratio
import Submission.Work.LinnikAreas.A5.Baux_lim_quad
import Submission.Work.LinnikAreas.A5.Baux_deriv_nonpos

namespace Work.LinnikAreas.A5

open Filter Topology Set
open scoped Topology

noncomputable section

/-
Basic properties of the per-character bound B(λ) of HB 13.3 (`Work.LinnikContract.Bfun`): it is
continuous on [0,∞) (the two branches agree at λ = 0 with value 1/(3K)+1, since
(1-e^{-2Kλ})/(6K²λ) → 1/(3K) and (2Kλ-1+e^{-2Kλ})/(2K²λ²) → 1), and it is antitone (decreasing)
on [0,∞).  Monotonicity is used for the λ-discretisation.

The proof goes through the substitution `t = 2Kλ`, which turns the closed form of `B` for `λ ≠ 0`
into the elementary function `Baux K t = (1-e^{-t})/(3Kt) + 2(t-1+e^{-t})/t²`; this has the finite
two-sided limit `1/(3K) + 1` at `t = 0`, which is exactly the value that `Bfun` assigns at `λ = 0`,
so the extension `Baux` is continuous at `0`, and its derivative on `(0,∞)` is nonpositive.
-/

/-- The closed form of HB's per-character bound `B(λ)` after the substitution `t = 2Kλ`, extended
to `t = 0` by the limiting value `1/(3K) + 1`.  `Bfun K λ = Baux K (2Kλ)` for all `λ`. -/
def Baux (K t : ℝ) : ℝ :=
  if t = 0 then 1 / (3 * K) + 1
  else (1 - Real.exp (-t)) / (3 * K * t) + 2 * (t - 1 + Real.exp (-t)) / t ^ 2

lemma Baux_zero (K : ℝ) : Baux K 0 = 1 / (3 * K) + 1 := by simp [Baux]

/-- The substitution `t = 2Kλ` identifies `Bfun K` with `Baux K` along `λ ↦ 2Kλ`. -/
lemma Bfun_eq_Baux {K : ℝ} (hK : 0 < K) (lam : ℝ) :
    Work.LinnikContract.Bfun K lam = Baux K (2 * K * lam) := by
  rcases eq_or_ne lam 0 with rfl | hne
  · simp [Work.LinnikContract.Bfun, Baux]
  · have h2 : 2 * K * lam ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt hK)) hne
    rw [Work.LinnikContract.Bfun, if_neg hne, Baux, if_neg h2]
    simp only [show -2 * K * lam = -(2 * K * lam) by ring]
    field_simp
    ring

/-- Away from `0`, `Baux K` agrees with the explicit closed form. -/
lemma Baux_eventuallyEq (K : ℝ) {t : ℝ} (ht : t ≠ 0) :
    Baux K =ᶠ[𝓝 t]
      (fun s : ℝ => (1 - Real.exp (-s)) / (3 * K * s) + 2 * (s - 1 + Real.exp (-s)) / s ^ 2) := by
  filter_upwards [(isOpen_ne (x := (0 : ℝ))).mem_nhds ht] with s hs
  rw [Baux, if_neg hs]

lemma differentiableAt_closed (K : ℝ) (hK : 0 < K) {t : ℝ} (ht : 0 < t) :
    DifferentiableAt ℝ
      (fun s : ℝ => (1 - Real.exp (-s)) / (3 * K * s) + 2 * (s - 1 + Real.exp (-s)) / s ^ 2) t := by
  have hnum1 : DifferentiableAt ℝ (fun s : ℝ => 1 - Real.exp (-s)) t := by fun_prop
  have hden1 : DifferentiableAt ℝ (fun s : ℝ => 3 * K * s) t := by fun_prop
  have hnum2 : DifferentiableAt ℝ (fun s : ℝ => 2 * (s - 1 + Real.exp (-s))) t := by fun_prop
  have hden2 : DifferentiableAt ℝ (fun s : ℝ => s ^ 2) t := by fun_prop
  have h1 : 3 * K * t ≠ 0 := by positivity
  have h2 : t ^ 2 ≠ 0 := by positivity
  exact (hnum1.div hden1 h1).add (hnum2.div hden2 h2)

lemma Baux_differentiableAt (K : ℝ) (hK : 0 < K) {t : ℝ} (ht : 0 < t) :
    DifferentiableAt ℝ (Baux K) t :=
  ((Baux_eventuallyEq K (ne_of_gt ht)).differentiableAt_iff).2 (differentiableAt_closed K hK ht)

/-- `Baux K` tends to `1/(3K) + 1` as `t → 0⁺`, the two one-sided limits being `1/(3K)` for the
first summand and `1` for the second. -/
lemma Baux_tendsto_zero (K : ℝ) (hK : 0 < K) :
    Tendsto (Baux K) (nhdsWithin 0 (Ioi 0)) (nhds (1 / (3 * K) + 1)) := by
  have hfield : ∀ t : ℝ,
      (1 - Real.exp (-t)) / (3 * K * t) = (1 / (3 * K)) * ((1 - Real.exp (-t)) / t) := by
    intro t
    by_cases ht : t = 0
    · subst ht; simp
    · field_simp
  have hU : Tendsto (fun t : ℝ => (1 / (3 * K)) * ((1 - Real.exp (-t)) / t))
      (nhdsWithin 0 (Ioi 0)) (nhds ((1 / (3 * K)) * 1)) := Baux_lim_ratio.const_mul _
  have hV : Tendsto (fun t : ℝ => 2 * ((t - 1 + Real.exp (-t)) / t ^ 2))
      (nhdsWithin 0 (Ioi 0)) (nhds (2 * (1 / 2))) := Baux_lim_quad.const_mul 2
  have hsum : Tendsto (fun t : ℝ => (1 / (3 * K)) * ((1 - Real.exp (-t)) / t)
        + 2 * ((t - 1 + Real.exp (-t)) / t ^ 2)) (nhdsWithin 0 (Ioi 0))
      (nhds (1 / (3 * K) + 1)) := by
    simpa using hU.add hV
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htne : t ≠ 0 := ne_of_gt ht
  rw [Baux, if_neg htne, hfield t, mul_div_assoc]

lemma Baux_continuousWithinAt_zero (K : ℝ) (hK : 0 < K) :
    ContinuousWithinAt (Baux K) (Ici 0) 0 := by
  refine continuousWithinAt_Ioi_iff_Ici.1 ?_
  show Tendsto (Baux K) (nhdsWithin 0 (Ioi 0)) (nhds (Baux K 0))
  rw [Baux_zero]
  exact Baux_tendsto_zero K hK

lemma Baux_continuousOn (K : ℝ) (hK : 0 < K) : ContinuousOn (Baux K) (Ici 0) := by
  intro t ht
  have ht0 : (0 : ℝ) ≤ t := ht
  rcases eq_or_lt_of_le ht0 with h0 | hlt
  · subst h0
    exact Baux_continuousWithinAt_zero K hK
  · exact (Baux_differentiableAt K hK hlt).continuousAt.continuousWithinAt

lemma Baux_antitoneOn (K : ℝ) (hK : 0 < K) : AntitoneOn (Baux K) (Ici 0) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ici 0) (Baux_continuousOn K hK) ?_ ?_
  · intro t ht
    rw [interior_Ici] at ht
    exact (Baux_differentiableAt K hK ht).differentiableWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    rw [(Baux_eventuallyEq K (ne_of_gt ht)).deriv_eq]
    exact Baux_deriv_nonpos K t hK ht

theorem Bfun_facts (K : ℝ) (hK : 0 < K) :
    ContinuousOn (Work.LinnikContract.Bfun K) (Set.Ici 0) ∧
    Work.LinnikContract.Bfun K 0 = 1/(3*K) + 1 ∧
    AntitoneOn (Work.LinnikContract.Bfun K) (Set.Ici 0) := by
  have hfun : Work.LinnikContract.Bfun K = fun lam => Baux K (2 * K * lam) :=
    funext (Bfun_eq_Baux hK)
  refine ⟨?_, ?_, ?_⟩
  · rw [hfun]
    exact (Baux_continuousOn K hK).comp (continuous_const.mul continuous_id).continuousOn
      (fun x hx => by
        have hx0 : (0 : ℝ) ≤ x := hx
        show (0 : ℝ) ≤ 2 * K * x
        positivity)
  · rw [hfun]
    simpa using Baux_zero K
  · rw [hfun]
    intro x hx y hy hxy
    have hx0 : (0 : ℝ) ≤ x := hx
    have hy0 : (0 : ℝ) ≤ y := hy
    exact Baux_antitoneOn K hK (mem_Ici.mpr (by positivity)) (mem_Ici.mpr (by positivity))
      (by nlinarith)

end

end Work.LinnikAreas.A5
