import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PhiStar.RadialWAux.Defs
import Submission.Work.FTS.PhiStar.StarDefs
import Submission.Work.FTS.PhiStar.RadialWAux.radPsi_iteratedDeriv
import Submission.Work.FTS.PhiStar.RadialWAux.Aux3

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.PhiStar.RadialWAux

namespace Work.FTS.PhiStar.Series.SmoothAux.Deleg

set_option autoImplicit false

/-! ### General-order versions of the analytic input

The order-`22` statements of `RadialWAux/radPsi_iteratedDeriv.lean` and the tail
integration by parts `RadialWAux/Aux3.radPsi_tail_ibp_aux` are restated here for an
arbitrary order `N`, which is what `radPsi_rec` needs. -/

/-- On `(0,∞)` a `C^N` function has continuous `k`-th iterated derivative, `k ≤ N`. -/
lemma rpr_contDiffOn_iteratedDeriv {c : ℝ → ℝ} {N : ℕ}
    (hc : ContDiffOn ℝ N c (Set.Ioi 0)) {k : ℕ} (hk : k ≤ N) :
    ContinuousOn (iteratedDeriv k c) (Set.Ioi 0) := by
  have h1 : ContinuousOn (iteratedDerivWithin k c (Set.Ioi 0)) (Set.Ioi 0) :=
    hc.continuousOn_iteratedDerivWithin (by exact_mod_cast hk) isOpen_Ioi.uniqueDiffOn
  exact h1.congr fun x hx => (iteratedDerivWithin_of_isOpen isOpen_Ioi hx).symm

/-- The `(k+1)`-st iterated derivative is the derivative of the `k`-th one. -/
lemma rpr_hasDerivAt_iteratedDeriv {c : ℝ → ℝ} {x : ℝ} {N k : ℕ}
    (hc : ContDiffAt ℝ N c x) (hk : k < N) :
    HasDerivAt (iteratedDeriv k c) (iteratedDeriv (k + 1) c x) x := by
  have hd : DifferentiableAt ℝ (iteratedDeriv k c) x := by
    have h' := hc.contDiffWithinAt.differentiableWithinAt_iteratedDerivWithin (m := k)
      (show ((k : ℕ) : WithTop ℕ∞) < ((N : ℕ) : WithTop ℕ∞) by exact_mod_cast hk)
      (show UniqueDiffOn ℝ (insert x (Set.univ : Set ℝ)) from by
        simpa using (uniqueDiffOn_univ (𝕜 := ℝ) (E := ℝ)))
    rw [differentiableWithinAt_univ] at h'
    simpa using h'
  have h1 : HasDerivAt (iteratedDeriv k c) (deriv (iteratedDeriv k c) x) x := hd.hasDerivAt
  simpa [iteratedDeriv_succ] using h1

/-- **Differentiation under the integral sign for the `Ψ`-kernel**, at order `N`: if `c` is
`C^N` on `(0,∞)` with `|c^{(j)}| ≤ K` there, `k + 1 ≤ N` and `k + 1 < p`, then at every `z > 0`

  `z ↦ ∫_{u > 1} c^{(k)}(z u) u^{k-p-1} du` has derivative `∫_{u>1} c^{(k+1)}(z u) u^{k-p} du`. -/
theorem rpr_kernel_hasDerivAt {c : ℝ → ℝ} {K p : ℝ} {N : ℕ}
    (hc : ContDiffOn ℝ N c (Set.Ioi 0)) (hb : Work.FTS.PhiStar.BddDeriv N c K)
    {k : ℕ} (hkN : k + 1 ≤ N) (hkp : (k : ℝ) + 1 < p) {z : ℝ} (hz : 0 < z) :
    HasDerivAt
      (fun x : ℝ => ∫ u in Set.Ioi 1, iteratedDeriv k c (x * u) * u ^ ((k : ℝ) - p - 1))
      (∫ u in Set.Ioi 1,
        iteratedDeriv (k + 1) c (z * u) * u ^ (((k + 1 : ℕ) : ℝ) - p - 1)) z := by
  have hkN' : k ≤ N := by omega
  have hlt : (k : ℝ) - p < -1 := by linarith
  have hlt' : (k : ℝ) - p - 1 < -1 := by linarith
  have hcont_k : ContinuousOn (iteratedDeriv k c) (Set.Ioi 0) :=
    rpr_contDiffOn_iteratedDeriv hc hkN'
  have hcont_k1 : ContinuousOn (iteratedDeriv (k + 1) c) (Set.Ioi 0) :=
    rpr_contDiffOn_iteratedDeriv hc hkN
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
      exact mul_le_mul_of_nonneg_right (hb k hkN' (z * u) (mul_pos hz hu'))
        (le_of_lt (Real.rpow_pos_of_pos hu' _)))
    (by exact ((hcomp1 z hz).mul hrpow1).aestronglyMeasurable measurableSet_Ioi)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha x hx
      have ha' : 0 < a := lt_trans zero_lt_one ha
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ha' _),
        show (((k + 1 : ℕ) : ℝ) - p - 1) = (k : ℝ) - p from by push_cast; ring]
      exact mul_le_mul_of_nonneg_right (hb (k + 1) hkN (x * a) (mul_pos hx ha'))
        (le_of_lt (Real.rpow_pos_of_pos ha' _)))
    (by exact (integrableOn_Ioi_rpow_of_lt hlt zero_lt_one).const_mul K)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha x hx
      have ha' : 0 < a := lt_trans zero_lt_one ha
      have hid : HasDerivAt (fun y : ℝ => y * a) a x := by
        simpa using (hasDerivAt_id x).mul_const a
      have hca : ContDiffAt ℝ N c (x * a) :=
        hc.contDiffAt (isOpen_Ioi.mem_nhds (mul_pos hx ha'))
      have hd := rpr_hasDerivAt_iteratedDeriv hca (by omega : k < N)
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

/-! ### The bounding sequence of the recursion -/

/-- The auxiliary sequence bounding the formal derivatives of `Ψ`:
`Bnd p z₀ 0 = 1/p` and `Bnd p z₀ (j+1) = ((p + j) * Bnd p z₀ j + 1)/z₀`. -/
def Bnd (p z₀ : ℝ) : ℕ → ℝ :=
  fun n => Nat.rec (1 / p) (fun j bj => ((p + (j : ℝ)) * bj + 1) / z₀) n

lemma Bnd_zero (p z₀ : ℝ) : Bnd p z₀ 0 = 1 / p := rfl

lemma Bnd_succ (p z₀ : ℝ) (j : ℕ) :
    Bnd p z₀ (j + 1) = ((p + (j : ℝ)) * Bnd p z₀ j + 1) / z₀ := rfl

/-! ### The base case of the recursion -/

/-- The value of the first formal derivative: `psiF 1 z = (p Ψ z - c z)/z`. -/
lemma rpr_psiF_one (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (z : ℝ) :
    psiF α m c 1 z = (radP α m * radPsi α m c z - c z) / z := by
  have h : psiF α m c (0 + 1) =
      fun w => (radP α m * radPsi α m c w - c w) / w := by
    rw [psiF_succ]
    simp only [psiF_zero, iteratedDeriv_zero, Nat.cast_zero, sub_zero]
  rw [show (0 : ℕ) + 1 = 1 from rfl] at h
  exact congrFun h z

/-- The crude integral bound for `Ψ`: `|Ψ z| ≤ K/p` for `z > 0`. -/
lemma rpr_base_bound {α : ℝ} (m : ℕ) {c : ℝ → ℝ} {K : ℝ} {N : ℕ}
    (_hK : 0 ≤ K) (hb : Work.FTS.PhiStar.BddDeriv N c K) (hp : 0 < radP α m) :
    ∀ z : ℝ, 0 < z → |radPsi α m c z| ≤ K / radP α m := by
  intro z hz
  have hlt : -(radP α m) - 1 < -1 := by linarith
  have hbnd : ∀ᵐ u ∂(volume.restrict (Set.Ioi 1)),
      ‖c (z * u) * u ^ (-(radP α m) - 1)‖ ≤ K * u ^ (-(radP α m) - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := lt_trans zero_lt_one hu
    have hrpow : 0 ≤ u ^ (-(radP α m) - 1) := Real.rpow_nonneg hu0.le _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hrpow]
    exact mul_le_mul_of_nonneg_right
      (by simpa only [iteratedDeriv_zero] using hb 0 (Nat.zero_le N) (z * u) (mul_pos hz hu0))
      hrpow
  have hInt : ∫ u in Set.Ioi 1, u ^ (-(radP α m) - 1) = 1 / radP α m := by
    rw [integral_Ioi_rpow_of_lt (a := -(radP α m) - 1) hlt (c := 1) zero_lt_one, Real.one_rpow,
      show (-(radP α m) - 1) + 1 = -(radP α m) from by ring]
    rw [div_eq_div_iff (by linarith : (-(radP α m)) ≠ 0) (ne_of_gt hp)]
    ring
  have hmain : |∫ u in Set.Ioi 1, c (z * u) * u ^ (-(radP α m) - 1)| ≤ K / radP α m := by
    calc |∫ u in Set.Ioi 1, c (z * u) * u ^ (-(radP α m) - 1)|
        = ‖∫ u in Set.Ioi 1, c (z * u) * u ^ (-(radP α m) - 1)‖ := by rw [Real.norm_eq_abs]
      _ ≤ ∫ u in Set.Ioi 1, K * u ^ (-(radP α m) - 1) :=
          norm_integral_le_of_norm_le
            ((integrableOn_Ioi_rpow_of_lt hlt zero_lt_one).const_mul K) hbnd
      _ = K * (∫ u in Set.Ioi 1, u ^ (-(radP α m) - 1)) := by rw [integral_const_mul]
      _ = K / radP α m := by rw [hInt]; ring
  simpa only [radPsi] using hmain

/-- The base case of the recursion, in the form of a `HasDerivAt` statement:
`z ↦ Ψ z` has derivative `(p Ψ z - c z)/z`.  This is the integration by parts of
`d/du (c(zu) u^{-p})` over `(1,∞)` together with differentiation under the integral sign. -/
lemma rpr_deriv_value {α : ℝ} (m : ℕ) {c : ℝ → ℝ} {K : ℝ} {N : ℕ}
    (hN : 1 ≤ N) (hK : 0 ≤ K) (hc : ContDiffOn ℝ N c (Set.Ioi 0))
    (hb : Work.FTS.PhiStar.BddDeriv N c K) (hp : 1 < radP α m) :
    ∀ z : ℝ, 0 < z →
      HasDerivAt (radPsi α m c) ((radP α m * radPsi α m c z - c z) / z) z := by
  intro z hz
  have hker := rpr_kernel_hasDerivAt (c := c) (K := K) (p := radP α m) (N := N) hc hb
    (k := 0) (by omega) (by push_cast; linarith) hz
  have hΨeq : (fun x : ℝ => ∫ u in Set.Ioi 1,
      iteratedDeriv 0 c (x * u) * u ^ (((0 : ℕ) : ℝ) - radP α m - 1)) = radPsi α m c := by
    funext x
    show (∫ u in Set.Ioi 1, iteratedDeriv 0 c (x * u) * u ^ (((0 : ℕ) : ℝ) - radP α m - 1))
        = ∫ u in Set.Ioi 1, c (x * u) * u ^ (-(radP α m) - 1)
    rw [show iteratedDeriv 0 c = c from iteratedDeriv_zero]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with u
    rw [show (((0 : ℕ)) : ℝ) - radP α m - 1 = -(radP α m) - 1 from by push_cast; ring]
  have hVeq : (∫ u in Set.Ioi 1,
        iteratedDeriv (0 + 1) c (z * u) * u ^ (((0 + 1 : ℕ) : ℝ) - radP α m - 1))
      = ∫ u in Set.Ioi 1, deriv c (z * u) * u ^ (-(radP α m)) := by
    rw [show iteratedDeriv (0 + 1) c = deriv c from by
      rw [iteratedDeriv_succ, iteratedDeriv_zero]]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with u
    rw [show (((0 + 1 : ℕ)) : ℝ) - radP α m - 1 = -(radP α m) from by push_cast; ring]
  have hker' : HasDerivAt (radPsi α m c)
      (∫ u in Set.Ioi 1, deriv c (z * u) * u ^ (-(radP α m))) z := by
    rw [hΨeq, hVeq] at hker
    exact hker
  have hbnd : ∀ j : ℕ, j ≤ 1 → ∀ t : ℝ, 0 < t → |iteratedDeriv j c t| ≤ K := by
    intro j hj t ht
    exact hb j (by omega) t ht
  have hcont1 : ContDiffOn ℝ 1 c (Set.Ioi 0) := hc.of_le (by exact_mod_cast hN)
  have hIBP := radPsi_tail_ibp_aux (c := c) (k := 1) (K := K) (s := -(radP α m)) (z := z)
    le_rfl hz hK (by linarith) hcont1 hbnd
  rw [show (1 : ℕ) - 1 = 0 from rfl, iteratedDeriv_zero] at hIBP
  have hIBP' : (∫ u in Set.Ioi (1 : ℝ), deriv c (z * u) * u ^ (-(radP α m)))
      = -(1 / z) * c z
        - ((-(radP α m)) / z)
            * (∫ u in Set.Ioi (1 : ℝ), c (z * u) * u ^ (-(radP α m) - 1)) := by
    rw [← hIBP]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with u
    rw [iteratedDeriv_one]
  have hode : z * (∫ u in Set.Ioi (1 : ℝ), deriv c (z * u) * u ^ (-(radP α m)))
      = radP α m * radPsi α m c z - c z := by
    rw [hIBP']
    rw [show radPsi α m c z
        = ∫ u in Set.Ioi (1 : ℝ), c (z * u) * u ^ (-(radP α m) - 1) from rfl]
    field_simp
    ring
  have hkey : (∫ u in Set.Ioi (1 : ℝ), deriv c (z * u) * u ^ (-(radP α m)))
      = (radP α m * radPsi α m c z - c z) / z := by
    rw [eq_div_iff (ne_of_gt hz), mul_comm]
    exact hode
  rwa [hkey] at hker'

/-- The base case for the formal-derivative recursion of `Ψ`. -/
lemma rpr_base {α : ℝ} (m : ℕ) {c : ℝ → ℝ} {K : ℝ} {N : ℕ}
    (hN : 1 ≤ N) (hK : 0 ≤ K) (hc : ContDiffOn ℝ N c (Set.Ioi 0))
    (hb : Work.FTS.PhiStar.BddDeriv N c K) (hp : 1 < radP α m) :
    ∀ z : ℝ, 0 < z → HasDerivAt (radPsi α m c) (psiF α m c 1 z) z := by
  intro z hz
  have h := rpr_deriv_value (α := α) m hN hK hc hb hp z hz
  rw [rpr_psiF_one]
  exact h

/-! ### The recursion -/

/-- From the base case, the formal derivatives `psiF j` really are the successive derivatives
of `Ψ`. -/
lemma rpr_psiF_hasDerivAt {α : ℝ} {m : ℕ} {c : ℝ → ℝ} {N : ℕ}
    (hc : ContDiffOn ℝ N c (Set.Ioi 0))
    (hbase : ∀ z : ℝ, 0 < z → HasDerivAt (radPsi α m c) (psiF α m c 1 z) z) :
    ∀ j : ℕ, j + 1 ≤ N → ∀ z : ℝ, 0 < z →
      HasDerivAt (psiF α m c j) (psiF α m c (j + 1) z) z := by
  intro j
  induction j with
  | zero =>
    intro _ z hz
    rw [psiF_zero]
    exact hbase z hz
  | succ j ih =>
    intro hj z hz
    show HasDerivAt (psiF α m c (j + 1)) (psiF α m c (j + 1 + 1) z) z
    have hjN : j + 1 ≤ N := by omega
    have hdF : HasDerivAt (psiF α m c j) (psiF α m c (j + 1) z) z := ih hjN z hz
    have hcderiv : HasDerivAt (iteratedDeriv j c) (iteratedDeriv (j + 1) c z) z :=
      rpr_hasDerivAt_iteratedDeriv (hc.contDiffAt (isOpen_Ioi.mem_nhds hz)) (by omega)
    have hnum : HasDerivAt
        (fun w : ℝ => (radP α m - (j : ℝ)) * psiF α m c j w - iteratedDeriv j c w)
        ((radP α m - (j : ℝ)) * psiF α m c (j + 1) z - iteratedDeriv (j + 1) c z) z :=
      (hdF.const_mul (radP α m - (j : ℝ))).sub hcderiv
    have hdiv := hnum.div (hasDerivAt_id z) (ne_of_gt hz)
    have hv : (((radP α m - (j : ℝ)) * psiF α m c (j + 1) z - iteratedDeriv (j + 1) c z) * z
          - ((radP α m - (j : ℝ)) * psiF α m c j z - iteratedDeriv j c z) * 1) / z ^ 2
        = psiF α m c (j + 1 + 1) z := by
      have hrec := psiF_rec (α := α) (m := m) (c := c) j (z := z) (ne_of_gt hz)
      rw [psiF_succ (α := α) (m := m) (c := c) (j + 1)]
      rw [← hrec]
      field_simp
      push_cast
      ring
    rw [psiF_succ (α := α) (m := m) (c := c) j, ← hv]
    exact hdiv

/-- The formal derivatives `psiF k` coincide with the true iterated derivatives of `Ψ`. -/
lemma rpr_iteratedDeriv_eq_psiF {α : ℝ} {m : ℕ} {c : ℝ → ℝ} {N : ℕ}
    (hc : ContDiffOn ℝ N c (Set.Ioi 0))
    (hbase : ∀ z : ℝ, 0 < z → HasDerivAt (radPsi α m c) (psiF α m c 1 z) z) :
    ∀ k : ℕ, k ≤ N → ∀ z : ℝ, 0 < z →
      iteratedDeriv k (radPsi α m c) z = psiF α m c k z := by
  have hsa := rpr_psiF_hasDerivAt (α := α) (m := m) (c := c) (N := N) hc hbase
  intro k
  induction k with
  | zero =>
    intro _ z _
    rw [psiF_zero]
    rfl
  | succ j ih =>
    intro hk z hz
    show iteratedDeriv (j + 1) (radPsi α m c) z = psiF α m c (j + 1) z
    have hjN : j + 1 ≤ N := by omega
    have hd := hsa j hjN z hz
    have hev : iteratedDeriv j (radPsi α m c) =ᶠ[𝓝 z] psiF α m c j := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with x hx
      exact ih (by omega) x hx
    rw [iteratedDeriv_succ, hev.deriv_eq, hd.deriv]

/-! ### The bounds -/

/-- The arithmetic of the bounding sequence: `Bnd p z₀ j ≤ 2 * M ^ j`. -/
lemma Bnd_le {p z₀ M : ℝ} {N : ℕ} (hp : 1 < p) (hz₀ : 0 < z₀) (hM : 1 ≤ M)
    (hMz : (p + (N : ℝ) + 1) / z₀ ≤ M) :
    ∀ j : ℕ, j ≤ N → Bnd p z₀ j ≤ 2 * M ^ j := by
  intro j
  induction j with
  | zero =>
    intro _
    show 1 / p ≤ 2 * M ^ 0
    rw [pow_zero]
    have h1 : 1 / p ≤ 1 := by
      rw [div_le_one (by linarith : (0 : ℝ) < p)]
      linarith
    linarith
  | succ j ih =>
    intro hj
    have hjN : j ≤ N := by omega
    have hMz' : p + (j : ℝ) + 1 ≤ M * z₀ := by
      have h1 : p + (N : ℝ) + 1 ≤ M * z₀ := (div_le_iff₀ hz₀).mp hMz
      have h2 : (j : ℝ) ≤ (N : ℝ) := by exact_mod_cast hjN
      linarith
    have hpj : (0 : ℝ) ≤ p + (j : ℝ) := by linarith
    have h1e : (1 : ℝ) ≤ M ^ j := one_le_pow₀ hM
    have h2e : (1 : ℝ) ≤ 2 * M ^ j := by linarith
    show ((p + (j : ℝ)) * Bnd p z₀ j + 1) / z₀ ≤ 2 * M ^ (j + 1)
    have ihb : Bnd p z₀ j ≤ 2 * M ^ j := ih hjN
    have step1 : (p + (j : ℝ)) * Bnd p z₀ j + 1 ≤ (p + (j : ℝ)) * (2 * M ^ j) + 1 := by
      have h := mul_le_mul_of_nonneg_left ihb hpj
      linarith
    have stepA : (p + (j : ℝ)) * (2 * M ^ j) + 1 ≤ 2 * M ^ j * (p + (j : ℝ) + 1) := by
      calc (p + (j : ℝ)) * (2 * M ^ j) + 1 ≤ (p + (j : ℝ)) * (2 * M ^ j) + 2 * M ^ j := by
            linarith
        _ = 2 * M ^ j * (p + (j : ℝ) + 1) := by ring
    have stepB : 2 * M ^ j * (p + (j : ℝ) + 1) ≤ 2 * M ^ j * (M * z₀) :=
      mul_le_mul_of_nonneg_left hMz' (by positivity)
    have stepC : 2 * M ^ j * (M * z₀) = 2 * M ^ (j + 1) * z₀ := by
      rw [pow_succ]
      ring
    rw [div_le_iff₀ hz₀]
    linarith

/-- The bound on the formal derivatives of `Ψ` in terms of the sequence `Bnd`. -/
lemma psiF_le_Bnd {α : ℝ} (m : ℕ) {c : ℝ → ℝ} {K : ℝ} {N : ℕ}
    (hK : 0 ≤ K) (hb : Work.FTS.PhiStar.BddDeriv N c K) (hp : 1 < radP α m) {z₀ : ℝ}
    (hz₀ : 0 < z₀) :
    ∀ j : ℕ, j ≤ N → ∀ z : ℝ, z₀ ≤ z → |psiF α m c j z| ≤ Bnd (radP α m) z₀ j * K := by
  intro j
  induction j with
  | zero =>
    intro _ z hz
    have hzpos : 0 < z := lt_of_lt_of_le hz₀ hz
    rw [psiF_zero]
    have hbb := rpr_base_bound (α := α) m (c := c) (K := K) (N := N) hK hb
      (lt_trans zero_lt_one hp) z hzpos
    calc |radPsi α m c z| ≤ K / radP α m := hbb
      _ = (1 / radP α m) * K := by ring
      _ = Bnd (radP α m) z₀ 0 * K := by rw [Bnd_zero]
  | succ j ih =>
    intro hj z hz
    have hjN : j ≤ N := by omega
    have hzpos : 0 < z := lt_of_lt_of_le hz₀ hz
    have hrec := psiF_rec (α := α) (m := m) (c := c) j (z := z) (ne_of_gt hzpos)
    have hval : psiF α m c (j + 1) z
        = ((radP α m - (j : ℝ)) * psiF α m c j z - iteratedDeriv j c z) / z := by
      rw [eq_div_iff (ne_of_gt hzpos), mul_comm]
      exact hrec
    rw [hval]
    have hnum : |(radP α m - (j : ℝ)) * psiF α m c j z - iteratedDeriv j c z|
        ≤ (radP α m + (j : ℝ)) * (Bnd (radP α m) z₀ j * K) + K := by
      have h1 : |(radP α m - (j : ℝ)) * psiF α m c j z - iteratedDeriv j c z|
          ≤ |(radP α m - (j : ℝ)) * psiF α m c j z| + |iteratedDeriv j c z| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le ((radP α m - (j : ℝ)) * psiF α m c j z) (-(iteratedDeriv j c z))
      have habs : |radP α m - (j : ℝ)| ≤ radP α m + (j : ℝ) := by
        have hp0 : 0 < radP α m := lt_trans zero_lt_one hp
        have hj0 : (0 : ℝ) ≤ (j : ℝ) := by positivity
        rw [abs_le]
        constructor <;> linarith
      have hpsi_j : |psiF α m c j z| ≤ Bnd (radP α m) z₀ j * K := ih hjN z hz
      have h2 : |(radP α m - (j : ℝ)) * psiF α m c j z|
          ≤ (radP α m + (j : ℝ)) * (Bnd (radP α m) z₀ j * K) := by
        rw [abs_mul]
        refine mul_le_mul habs hpsi_j (abs_nonneg _) ?_
        have hp0 : 0 < radP α m := lt_trans zero_lt_one hp
        have hj0 : (0 : ℝ) ≤ (j : ℝ) := by positivity
        linarith
      have h3 : |iteratedDeriv j c z| ≤ K := hb j hjN z hzpos
      linarith
    have hbK : 0 ≤ (radP α m + (j : ℝ)) * (Bnd (radP α m) z₀ j * K) + K := by
      have hp0 : 0 < radP α m := lt_trans zero_lt_one hp
      have hj0 : (0 : ℝ) ≤ (j : ℝ) := by positivity
      have hbj := ih hjN z hz
      have h0 : 0 ≤ Bnd (radP α m) z₀ j * K := le_trans (abs_nonneg _) hbj
      nlinarith [hp0, hj0, h0, hK]
    calc |((radP α m - (j : ℝ)) * psiF α m c j z - iteratedDeriv j c z) / z|
        = |(radP α m - (j : ℝ)) * psiF α m c j z - iteratedDeriv j c z| / |z| := abs_div _ _
      _ = |(radP α m - (j : ℝ)) * psiF α m c j z - iteratedDeriv j c z| / z := by
            rw [abs_of_pos hzpos]
      _ ≤ ((radP α m + (j : ℝ)) * (Bnd (radP α m) z₀ j * K) + K) / z :=
            div_le_div_of_nonneg_right hnum hzpos.le
      _ ≤ ((radP α m + (j : ℝ)) * (Bnd (radP α m) z₀ j * K) + K) / z₀ :=
            div_le_div_of_nonneg_left hbK hz₀ hz
      _ = Bnd (radP α m) z₀ (j + 1) * K := by rw [Bnd_succ]; ring

/-- The ODE recursion bound for `radPsi`.  The proof template (order `22` only) is
`Submission/Work/FTS/PhiStar/RadialWAux/radPsi_recursion.lean`: define the formal derivatives
`F_0 = Ψ`, `F_{j+1} z = ((p - j) F_j z - c^{(j)} z)/z` (`p = radP α m`), show
`HasDerivAt (F_j) (F_{j+1} z) z` and `iteratedDeriv j Ψ z = F_j z` on `Ioi 0` (the base case
`z Ψ' = p Ψ - c` comes from differentiating `∫_{Ioi 1} c(zu)u^{-p-1}du` under the integral sign
and integrating `d/du(c(zu)u^{-p})` over `(1,∞)` by parts), and then propagate the bound
`B 0 = 1/p`, `B (j+1) = ((p + j) * B j + 1)/z₀`, which satisfies `B j ≤ 2 * M ^ j`. -/
theorem radPsi_rec {α : ℝ} (hα : 0 < α) (m : ℕ) (N : ℕ) {c : ℝ → ℝ} {K M z₀ : ℝ}
    (hK : 0 ≤ K) (hc : ContDiffOn ℝ N c (Set.Ioi 0)) (hb : Work.FTS.PhiStar.BddDeriv N c K)
    (hp : 1 < Work.FTS.PhiStar.RadialWAux.radP α m) (hz₀ : 0 < z₀) (hM : 1 ≤ M)
    (hMz : (Work.FTS.PhiStar.RadialWAux.radP α m + (N : ℝ) + 1) / z₀ ≤ M) :
    (∀ j : ℕ, j ≤ N → ∀ z : ℝ, z₀ ≤ z →
        |iteratedDeriv j (Work.FTS.PhiStar.RadialWAux.radPsi α m c) z| ≤ 2 * M ^ j * K)
    ∧ (∀ j : ℕ, j + 1 ≤ N → ∀ z : ℝ, 0 < z →
        HasDerivAt (iteratedDeriv j (Work.FTS.PhiStar.RadialWAux.radPsi α m c))
          (iteratedDeriv (j + 1) (Work.FTS.PhiStar.RadialWAux.radPsi α m c) z) z) := by
  have hbound := psiF_le_Bnd (α := α) (m := m) (c := c) (K := K) (N := N) hK hb hp hz₀
  have hB := Bnd_le (p := radP α m) (z₀ := z₀) (M := M) (N := N) hp hz₀ hM hMz
  by_cases hN1 : 1 ≤ N
  · have hbase := rpr_base (α := α) (m := m) (c := c) (K := K) (N := N) hN1 hK hc hb hp
    have hiter := rpr_iteratedDeriv_eq_psiF (α := α) (m := m) (c := c) (N := N) hc hbase
    have hder := rpr_psiF_hasDerivAt (α := α) (m := m) (c := c) (N := N) hc hbase
    refine ⟨?_, ?_⟩
    · intro j hj z hz
      have hzpos : 0 < z := lt_of_lt_of_le hz₀ hz
      calc |iteratedDeriv j (radPsi α m c) z| = |psiF α m c j z| := by rw [hiter j hj z hzpos]
        _ ≤ Bnd (radP α m) z₀ j * K := hbound j hj z hz
        _ ≤ 2 * M ^ j * K := mul_le_mul_of_nonneg_right (hB j hj) hK
    · intro j hj z hz
      have hjN : j ≤ N := by omega
      have h1 : HasDerivAt (psiF α m c j) (psiF α m c (j + 1) z) z := hder j hj z hz
      have hev : iteratedDeriv j (radPsi α m c) =ᶠ[𝓝 z] psiF α m c j := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
        exact hiter j hjN w hw
      have h2 : HasDerivAt (iteratedDeriv j (radPsi α m c)) (psiF α m c (j + 1) z) z :=
        h1.congr_of_eventuallyEq hev
      have h3 : psiF α m c (j + 1) z = iteratedDeriv (j + 1) (radPsi α m c) z :=
        (hiter (j + 1) hj z hz).symm
      rwa [h3] at h2
  · have hN0 : N = 0 := by omega
    subst hN0
    refine ⟨?_, ?_⟩
    · intro j hj z hz
      have hj0 : j = 0 := by omega
      subst hj0
      have h1 := hbound 0 (by omega) z hz
      rw [psiF_zero, Bnd_zero] at h1
      have h3 : 1 / radP α m ≤ 2 := by
        have h2 := hB 0 (by omega)
        rw [Bnd_zero, pow_zero] at h2
        linarith
      have h5 : (1 / radP α m) * K ≤ 2 * M ^ 0 * K := by
        rw [pow_zero]
        calc (1 / radP α m) * K ≤ 2 * K := mul_le_mul_of_nonneg_right h3 hK
          _ = 2 * 1 * K := by ring
      rw [iteratedDeriv_zero]
      exact le_trans h1 h5
    · intro j hj z hz
      exact absurd hj (by omega)

end Work.FTS.PhiStar.Series.SmoothAux.Deleg
