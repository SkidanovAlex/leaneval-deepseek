/-
# `radPsi_iteratedDeriv` — the iterated `z`-derivatives of the outer piece `Ψ`

For `c` of class `C^22` on `(0,∞)` with the first `22` derivatives bounded by `K`,

  `radPsi α m c z = ∫_{u > 1} c (z u) u^{-p-1} du`      (`p = radP α m`)

and for every `k ≤ 22` with `k < p` the `k`-th `z`-derivative is obtained by differentiating
under the integral sign `k` times:

  `(d/dz)^k (radPsi α m c) z = ∫_{u > 1} c^{(k)}(z u) u^{k-p-1} du`.

The only two ingredients are (i) differentiability of `iteratedDeriv k c` on `(0,∞)` with
derivative `iteratedDeriv (k+1) c` (which follows from `ContDiffOn ℝ 22 c (Ioi 0)`), and
(ii) the domination `|c^{(k+1)}(z u) u^{k-p}| ≤ K u^{k-p}` with `u^{k-p}` integrable on
`(Ioi 1)` because `k - p < -1`.  The induction is guarded by `k < p`: this is exactly the
range in which the differentiated integral still converges.
-/
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PhiStar.RadialWAux.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.RadialWAux

/-- On `(0,∞)` a `C^22` function has continuous `k`-th iterated derivative, `k ≤ 22`. -/
lemma radPsiAux_continuousOn_iteratedDeriv {c : ℝ → ℝ}
    (hc : ContDiffOn ℝ 22 c (Set.Ioi 0)) {k : ℕ} (hk : k ≤ 22) :
    ContinuousOn (iteratedDeriv k c) (Set.Ioi 0) := by
  have h1 : ContinuousOn (iteratedDerivWithin k c (Set.Ioi 0)) (Set.Ioi 0) :=
    hc.continuousOn_iteratedDerivWithin (by exact_mod_cast hk) isOpen_Ioi.uniqueDiffOn
  exact h1.congr fun x hx => (iteratedDerivWithin_of_isOpen isOpen_Ioi hx).symm

/-- The `(k+1)`-st iterated derivative is the derivative of the `k`-th one. -/
lemma radPsiAux_hasDerivAt_iteratedDeriv {c : ℝ → ℝ} {x : ℝ} {k : ℕ}
    (hc : ContDiffAt ℝ 22 c x) (hk : k < 22) :
    HasDerivAt (iteratedDeriv k c) (iteratedDeriv (k + 1) c x) x := by
  have hd : DifferentiableAt ℝ (iteratedDeriv k c) x := by
    have h' := hc.contDiffWithinAt.differentiableWithinAt_iteratedDerivWithin (m := k)
      (show ((k : ℕ) : WithTop ℕ∞) < ((22 : ℕ) : WithTop ℕ∞) by exact_mod_cast hk)
      (show UniqueDiffOn ℝ (insert x (Set.univ : Set ℝ)) from by
        simpa using (uniqueDiffOn_univ (𝕜 := ℝ) (E := ℝ)))
    rw [differentiableWithinAt_univ] at h'
    simpa using h'
  have h1 : HasDerivAt (iteratedDeriv k c) (deriv (iteratedDeriv k c) x) x := hd.hasDerivAt
  simpa [iteratedDeriv_succ] using h1

/-- **Differentiation under the integral sign for the `Ψ`-kernel.**  If `c` is `C^22` on
`(0,∞)` with `|c^{(j)}| ≤ K` there, `k + 1 ≤ 22` and `k + 1 < p`, then at every `z > 0`

  `z ↦ ∫_{u > 1} c^{(k)}(z u) u^{k-p-1} du` has derivative `∫_{u>1} c^{(k+1)}(z u) u^{k-p} du`.

(The dominating function at this step is `K u^{k-p}`, integrable on `(Ioi 1)` because
`k - p < -1`.) -/
theorem radPsiAux_kernel_hasDerivAt {c : ℝ → ℝ} {K p : ℝ}
    (hc : ContDiffOn ℝ 22 c (Set.Ioi 0)) (hb : Work.FTS.PhiStar.BddDeriv 22 c K)
    {k : ℕ} (hk22 : k + 1 ≤ 22) (hkp : (k : ℝ) + 1 < p) {z : ℝ} (hz : 0 < z) :
    HasDerivAt
      (fun x : ℝ => ∫ u in Set.Ioi 1, iteratedDeriv k c (x * u) * u ^ ((k : ℝ) - p - 1))
      (∫ u in Set.Ioi 1,
        iteratedDeriv (k + 1) c (z * u) * u ^ (((k + 1 : ℕ) : ℝ) - p - 1)) z := by
  have hk22' : k ≤ 22 := by omega
  have hlt : (k : ℝ) - p < -1 := by linarith
  have hlt' : (k : ℝ) - p - 1 < -1 := by linarith
  have hcont_k : ContinuousOn (iteratedDeriv k c) (Set.Ioi 0) :=
    radPsiAux_continuousOn_iteratedDeriv hc hk22'
  have hcont_k1 : ContinuousOn (iteratedDeriv (k + 1) c) (Set.Ioi 0) :=
    radPsiAux_continuousOn_iteratedDeriv hc hk22
  have hne : ∀ u ∈ Set.Ioi (1 : ℝ), u ≠ 0 := fun u hu => ne_of_gt (lt_trans zero_lt_one hu)
  have hrpow : ContinuousOn (fun u : ℝ => u ^ ((k : ℝ) - p - 1)) (Set.Ioi 1) :=
    continuousOn_id.rpow continuousOn_const (fun u hu => Or.inl (hne u hu))
  have hrpow1 : ContinuousOn (fun u : ℝ => u ^ (((k + 1 : ℕ) : ℝ) - p - 1)) (Set.Ioi 1) :=
    continuousOn_id.rpow continuousOn_const (fun u hu => Or.inl (hne u hu))
  have hcomp : ∀ x : ℝ, 0 < x →
      ContinuousOn (fun u : ℝ => iteratedDeriv k c (x * u)) (Set.Ioi 1) :=
    fun x hx => hcont_k.comp ((continuousOn_const.mul continuousOn_id).mono (Set.subset_univ _))
      (fun u hu => mul_pos hx (lt_trans zero_lt_one hu))
  have hcomp1 : ∀ x : ℝ, 0 < x →
      ContinuousOn (fun u : ℝ => iteratedDeriv (k + 1) c (x * u)) (Set.Ioi 1) :=
    fun x hx => hcont_k1.comp ((continuousOn_const.mul continuousOn_id).mono (Set.subset_univ _))
      (fun u hu => mul_pos hx (lt_trans zero_lt_one hu))
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi 1)) (s := Set.Ioi (0 : ℝ)) (x₀ := z)
    (F := fun x u : ℝ => iteratedDeriv k c (x * u) * u ^ ((k : ℝ) - p - 1))
    (F' := fun x u : ℝ => iteratedDeriv (k + 1) c (x * u) * u ^ (((k + 1 : ℕ) : ℝ) - p - 1))
    (bound := fun u : ℝ => K * u ^ ((k : ℝ) - p))
    (isOpen_Ioi.mem_nhds hz)
    (by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with x hx
      exact ((hcomp x hx).mul hrpow).aestronglyMeasurable measurableSet_Ioi)
    (by
      refine MeasureTheory.Integrable.mono'
        ((integrableOn_Ioi_rpow_of_lt hlt' zero_lt_one).const_mul K)
        (((hcomp z hz).mul hrpow).aestronglyMeasurable measurableSet_Ioi) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu' : 0 < u := lt_trans zero_lt_one hu
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hu' _)]
      exact mul_le_mul_of_nonneg_right (hb k hk22' (z * u) (mul_pos hz hu'))
        (le_of_lt (Real.rpow_pos_of_pos hu' _)))
    (by exact ((hcomp1 z hz).mul hrpow1).aestronglyMeasurable measurableSet_Ioi)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha x hx
      have ha' : 0 < a := lt_trans zero_lt_one ha
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ha' _),
        show (((k + 1 : ℕ) : ℝ) - p - 1) = (k : ℝ) - p from by push_cast; ring]
      exact mul_le_mul_of_nonneg_right (hb (k + 1) hk22 (x * a) (mul_pos hx ha'))
        (le_of_lt (Real.rpow_pos_of_pos ha' _)))
    (by exact (integrableOn_Ioi_rpow_of_lt hlt zero_lt_one).const_mul K)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha x hx
      have ha' : 0 < a := lt_trans zero_lt_one ha
      have hid : HasDerivAt (fun y : ℝ => y * a) a x := by
        simpa using (hasDerivAt_id x).mul_const a
      have hca : ContDiffAt ℝ 22 c (x * a) :=
        hc.contDiffAt (isOpen_Ioi.mem_nhds (mul_pos hx ha'))
      have hd := radPsiAux_hasDerivAt_iteratedDeriv hca (by omega : k < 22)
      have hc' := hd.comp x hid
      have hfun : (iteratedDeriv k c ∘ fun y : ℝ => y * a) =
          fun y : ℝ => iteratedDeriv k c (y * a) := rfl
      rw [hfun] at hc'
      have hres := hc'.mul_const (a ^ ((k : ℝ) - p - 1))
      have hval : ((iteratedDeriv (k + 1) c (x * a) * a) * a ^ ((k : ℝ) - p - 1))
          = iteratedDeriv (k + 1) c (x * a) * a ^ (((k + 1 : ℕ) : ℝ) - p - 1) := by
        rw [show (((k + 1 : ℕ) : ℝ) - p - 1) = 1 + ((k : ℝ) - p - 1) from by push_cast; ring,
          Real.rpow_add ha', Real.rpow_one]
        ring
      rw [hval] at hres
      exact hres)
  exact hmain.2

theorem radPsi_iteratedDeriv {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hc : ContDiffOn ℝ 22 c (Set.Ioi 0))
    (hb : Work.FTS.PhiStar.BddDeriv 22 c K) :
    ∀ k : ℕ, k ≤ 22 → (k : ℝ) < Work.FTS.PhiStar.RadialWAux.radP α m → ∀ z : ℝ, 0 < z →
      iteratedDeriv k (Work.FTS.PhiStar.RadialWAux.radPsi α m c) z
        = ∫ u in Set.Ioi 1,
            iteratedDeriv k c (z * u)
              * u ^ ((k : ℝ) - Work.FTS.PhiStar.RadialWAux.radP α m - 1) := by
  intro k
  induction k with
  | zero =>
    intro _ _ z _
    simp only [iteratedDeriv_zero, Nat.cast_zero, zero_sub]
    rfl
  | succ k ih =>
    intro h22 hp z hz
    have hk22 : k ≤ 22 := by omega
    have hkp : (k : ℝ) + 1 < radP α m := by
      push_cast at hp ⊢
      exact hp
    have hkp' : (k : ℝ) < radP α m := by linarith
    have hstep := radPsiAux_kernel_hasDerivAt (p := radP α m) (K := K) hc hb h22 hkp hz
    have hev : iteratedDeriv k (radPsi α m c) =ᶠ[𝓝 z]
        (fun x : ℝ => ∫ u in Set.Ioi 1,
          iteratedDeriv k c (x * u) * u ^ ((k : ℝ) - radP α m - 1)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with x hx
      exact ih hk22 hkp' x hx
    rw [iteratedDeriv_succ, hev.deriv_eq]
    exact hstep.deriv

end Work.FTS.PhiStar.RadialWAux
