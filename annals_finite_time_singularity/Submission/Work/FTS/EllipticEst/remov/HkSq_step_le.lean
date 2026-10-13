import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.H2.T2Aesm
import Submission.Work.FTS.EllipticEst.remov.EllEstUnifStepAux
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.Spaces.aesm_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false

/-!
# Integrating the pointwise induction step for `HkSq`

`Step.HkIntegrand_step_le` (in `EllEstUnifStepAux`) is the *pointwise* statement that the
level-`k` integrand `HkIntegrand α k f` is dominated on the open quadrant by the level-`(k-1)`
integrand, the level-`(k-1)` integrand of `D_z f` and the single top angular slot
`(mixed 0 k f · Wt)²`.

This file performs the (measure-theoretic) passage to the corresponding statement for the
squared norms `HkSq α k f = ∫∫ HkIntegrand α k f`.  Three things have to be supplied.

* The existing pointwise lemmas are stated for `ContDiffOn ℝ ⊤`, which in this Mathlib is
  *analyticity* (`ContDiffOn 𝕜 ⊤ f s → AnalyticOn 𝕜 f s`), while the hypothesis of the target
  is only `∀ n : ℕ, ContDiffOn ℝ n`, i.e. `C^∞` (`Work.Stability.smoothOrder`).  So the
  pointwise machinery is re-derived here at the genuine smooth order: the commutation
  `D_z (D_θ^i g) = D_θ^i (D_z g)` on the open quadrant (`DzDthIterCommOn_smooth`, using the
  `C^∞`-calculus `Work.FTS.LocData.contDiffOn_DzIter` of `SmoothChain`), and the two pointwise
  bounds `HkIntegrand_step_le_smooth` and `HkIntegrand_shift_le_smooth`.
* *Almost everywhere*: the pointwise bound only holds on the open quadrant `Qd`, which is
  co-null for the measure `(volume.restrict Iz).prod (volume.restrict Iθ)`.
* *Integrability* of the right-hand side: the level-`(k-1)` integrand of `D_z f` is a.e.
  dominated by a multiple of the level-`k` integrand of `f`, which is integrable by
  hypothesis, and the remaining two summands are honest slots of `HkIntegrand α k f`; joint
  measurability comes from the smoothness of `f` on the open quadrant
  (`Work.Spaces.aesm_of_continuousOn_Qd`).

All the bookkeeping is done on the product measure, where the iterated integrals of `HkSq`
are rewritten with `MeasureTheory.setIntegral_prod`.
-/

/-- The open quadrant `(0,∞) × (0,π/2)`, the set on which the pointwise step holds. -/
private def Qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)

private lemma isOpen_Qd : IsOpen Qd := isOpen_Ioi.prod isOpen_Ioo

private lemma sin_two_pos_Qd {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Real.sin (2 * θ) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · linarith [hθ.1]
  · linarith [hθ.2, Real.pi_pos]

/-! ## Continuity of the pieces of the integrand on the open quadrant -/

private lemma continuousOn_DzIter_Qd (g : ℝ → ℝ → ℝ)
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) Qd) (i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter i g p.1 p.2) Qd :=
  (Work.FTS.LocData.contDiffOn_DzIter isOpen_Qd hg i).continuousOn

private lemma continuousOn_mixed_Qd (g : ℝ → ℝ → ℝ)
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) Qd) (j i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i g p.1 p.2) Qd :=
  (Work.FTS.LocData.contDiffOn_mixed isOpen_Qd hg j i).continuousOn

private lemma continuousOn_w_Qd : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Qd := by
  simp only [Work.Spaces.w]
  refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => ?_)
  exact pow_ne_zero 2 (ne_of_gt hp.1)

private lemma continuousOn_sinpow_Qd (c : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c) Qd :=
  ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun _p hp => Or.inl (ne_of_gt (sin_two_pos_Qd hp.2)))

private lemma continuousOn_Wt_Qd (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Qd := by
  simp only [Work.Spaces.Wt, Work.Spaces.wTheta]
  exact continuousOn_w_Qd.mul (continuousOn_sinpow_Qd (-(Work.Spaces.gam α / 2)))

private lemma continuousOn_wdivsin_Qd :
    ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))
      Qd :=
  continuousOn_w_Qd.div (continuousOn_sinpow_Qd (Work.Spaces.eta / 2))
    (fun _p hp => ne_of_gt (Real.rpow_pos_of_pos (sin_two_pos_Qd hp.2) _))

/-- The `H^k` integrand is continuous on the open quadrant. -/
private lemma continuousOn_HkIntegrand_Qd (α : ℝ) (m : ℕ) (g : ℝ → ℝ → ℝ)
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) Qd) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α m g p.1 p.2) Qd := by
  simp only [Work.Spaces.HkIntegrand]
  refine ContinuousOn.add ?_ ?_
  · refine continuousOn_finsetSum (Finset.range (m + 1)) (fun i _ => ?_)
    exact (((continuousOn_DzIter_Qd g hg i).mul continuousOn_wdivsin_Qd).pow 2)
  · refine continuousOn_finsetSum (Finset.range (m + 1)) (fun i _ =>
      continuousOn_finsetSum (Finset.range (m + 1)) (fun j _ => ?_))
    split_ifs with h
    · exact (((continuousOn_mixed_Qd g hg j i).mul (continuousOn_Wt_Qd α)).pow 2)
    · exact continuousOn_const

/-- A single weighted mixed slot is continuous on the open quadrant. -/
private lemma continuousOn_mixed_sq_Wt_Qd (α : ℝ) (j i : ℕ) (g : ℝ → ℝ → ℝ)
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) Qd) :
    ContinuousOn
      (fun p : ℝ × ℝ => (Work.Spaces.mixed j i g p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      Qd :=
  (((continuousOn_mixed_Qd g hg j i).mul (continuousOn_Wt_Qd α)).pow 2)

/-! ## `D_z` commutes with the iterates of `D_θ` at the genuine smooth order -/

/-- `D_z (D_θ^i g) = D_θ^i (D_z g)` on an open set on which `g` is `C^∞`.  This is the
analogue of `Work.Spaces.DzDthIterCommOn` for the genuine smooth order
`Work.Stability.smoothOrder = ((⊤ : ℕ∞) : WithTop ℕ∞)`, which is the order supplied by the
hypothesis `∀ n, ContDiffOn ℝ n` of `HkSq_step_le`. -/
private theorem DzDthIterCommOn_smooth {g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) V) (i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DthIter i g)))
      (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.Dz g))) V := by
  induction i with
  | zero => intro y hy; rfl
  | succ i ih =>
      intro y hy
      have hF : ContDiffAt ℝ Work.Stability.smoothOrder
          (Function.uncurry (Work.Spaces.DthIter i g)) y :=
        (Work.FTS.LocData.contDiffOn_DthIter hV hg i).contDiffAt (hV.mem_nhds hy)
      have hcomm : Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DthIter i g)) y.1 y.2
          = Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DthIter i g)) y.1 y.2 :=
        Work.Spaces.Dz_Dth_comm (f := Work.Spaces.DthIter i g)
          (hF.of_le (by simp [Work.Stability.smoothOrder]))
      show Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DthIter i g)) y.1 y.2
        = Work.Spaces.Dth (Work.Spaces.DthIter i (Work.Spaces.Dz g)) y.1 y.2
      rw [hcomm]
      show Real.sin (2 * y.2) * Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.DthIter i g)) y.1 y.2
          = Real.sin (2 * y.2)
              * Work.Spaces.pth (Work.Spaces.DthIter i (Work.Spaces.Dz g)) y.1 y.2
      rw [Work.Spaces.pth_congr_of_isOpen hV ih hy]

/-- **The diagonal slots shift**: for `1 ≤ i` and `i ≤ k - 1` the slot `D_z^{k-i}D_θ^i f` of
level `k` is the slot `D_z^{k-1-i}D_θ^i (D_z f)` of the shifted integrand. -/
private lemma mixed_diag_apply_smooth {k i : ℕ} (hi : 1 ≤ i) (hik : i ≤ k - 1)
    (f : ℝ → ℝ → ℝ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) Qd) :
    Work.Spaces.mixed (k - i) i f z θ
      = Work.Spaces.mixed (k - 1 - i) i (Work.Spaces.Dz f) z θ := by
  have h1 : k - i = k - 1 - i + 1 := by omega
  have hcomm : Set.EqOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DthIter i f)))
      (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.Dz f))) Qd :=
    DzDthIterCommOn_smooth isOpen_Qd hg i
  have hpt : (z, θ) ∈ Qd := ⟨hz, hθ⟩
  show Work.Spaces.DzIter (k - i) (Work.Spaces.DthIter i f) z θ
    = Work.Spaces.DzIter (k - 1 - i) (Work.Spaces.DthIter i (Work.Spaces.Dz f)) z θ
  rw [h1, ← Step.DzIter_Dz (k - 1 - i) (Work.Spaces.DthIter i f)]
  exact Step.DzIter_congr_of_isOpen isOpen_Qd hcomm (k - 1 - i) hpt

/-- The shifted mixed slots: `D_z^j D_θ^i (D_z f) = D_z^{j+1}D_θ^i f` on the open quadrant. -/
private lemma mixed_shift_apply_smooth {j i : ℕ} (f : ℝ → ℝ → ℝ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) Qd) :
    Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ = Work.Spaces.mixed (j + 1) i f z θ := by
  have hcomm : Set.EqOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DthIter i f)))
      (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.Dz f))) Qd :=
    DzDthIterCommOn_smooth isOpen_Qd hg i
  have hpt : (z, θ) ∈ Qd := ⟨hz, hθ⟩
  have hcongr : Work.Spaces.DzIter j (Work.Spaces.DthIter i (Work.Spaces.Dz f)) z θ
      = Work.Spaces.DzIter j (Work.Spaces.Dz (Work.Spaces.DthIter i f)) z θ :=
    Step.DzIter_congr_of_isOpen isOpen_Qd hcomm.symm j hpt
  show Work.Spaces.DzIter j (Work.Spaces.DthIter i (Work.Spaces.Dz f)) z θ
    = Work.Spaces.DzIter (j + 1) (Work.Spaces.DthIter i f) z θ
  rw [hcongr, Step.DzIter_Dz j (Work.Spaces.DthIter i f)]

/-! ## The two pointwise bounds at the genuine smooth order -/

/-- **The pointwise step**: the level-`k` integrand is bounded by the level-`(k-1)`
integrand, the level-`(k-1)` integrand of `D_z f` and the single top angular slot. -/
private theorem HkIntegrand_step_le_smooth {k : ℕ} (hk : 1 ≤ k) (α : ℝ) (f : ℝ → ℝ → ℝ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) Qd) :
    Work.Spaces.HkIntegrand α k f z θ ≤
      Work.Spaces.HkIntegrand α (k - 1) f z θ
        + ((k : ℝ) + 1) * Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) z θ
        + (Work.Spaces.mixed 0 k f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
  have hHnn : 0 ≤ Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) z θ :=
    Work.Spaces.HkIntegrand_nonneg α (k - 1) (Work.Spaces.Dz f) z θ
  have hzterm : (Work.Spaces.DzIter k f z θ * Step.Zu z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) z θ := by
    rw [Step.DzIter_eq_DzIter_Dz hk f]
    exact Work.Spaces.sq_le_HkIntegrand_z α (k - 1) (Work.Spaces.Dz f) z θ (k - 1) le_rfl
  have hD : (∑ i ∈ Finset.range k,
        (if 1 ≤ i then (Work.Spaces.mixed (k - i) i f z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0))
      ≤ (k : ℝ) * Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) z θ := by
    have hterm : ∀ i ∈ Finset.range k,
        (if 1 ≤ i then (Work.Spaces.mixed (k - i) i f z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0)
          ≤ Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) z θ := by
      intro i hi
      have hik : i ≤ k - 1 := by
        have := Finset.mem_range.mp hi
        omega
      by_cases hi1 : 1 ≤ i
      · rw [if_pos hi1]
        rw [mixed_diag_apply_smooth hi1 hik f hz hθ hg]
        exact Work.Spaces.sq_le_HkIntegrand_mixed α (k - 1) (Work.Spaces.Dz f) z θ i
          (k - 1 - i) hi1 (by omega)
      · rw [if_neg hi1]
        exact hHnn
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hkey : (Work.Spaces.DzIter k f z θ * Step.Zu z θ) ^ 2
      + (∑ i ∈ Finset.range k,
          (if 1 ≤ i then (Work.Spaces.mixed (k - i) i f z θ * Work.Spaces.Wt α z θ) ^ 2
            else 0))
      ≤ ((k : ℝ) + 1) * Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) z θ := by
    nlinarith [hzterm, hD, hHnn]
  rw [Step.HkIntegrand_eq α k f, Step.HkIntegrand_eq α (k - 1) f,
    Step.Zsum_succ hk f z θ, Step.Msum_succ hk α f z θ]
  linarith [hkey]

/-- **The shifted integrand is dominated by the level-`k` integrand** (every slot of the
shifted integrand is a slot of the level-`k` integrand, and each single slot is dominated by
the whole integrand). -/
private theorem HkIntegrand_shift_le_smooth (α : ℝ) {k : ℕ} (hk : 1 ≤ k) (f : ℝ → ℝ → ℝ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) Qd) :
    Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) z θ
      ≤ ((k : ℝ) + (k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ := by
  have hHnn : 0 ≤ Work.Spaces.HkIntegrand α k f z θ :=
    Work.Spaces.HkIntegrand_nonneg α k f z θ
  have hZ : Step.Zsum (k - 1) (Work.Spaces.Dz f) z θ
      ≤ (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ := by
    have hterm : ∀ i ∈ Finset.range k,
        (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * Step.Zu z θ) ^ 2
          ≤ Work.Spaces.HkIntegrand α k f z θ := by
      intro i hi
      have hik : i + 1 ≤ k := by
        have := Finset.mem_range.mp hi
        omega
      rw [Step.DzIter_Dz i f]
      exact Work.Spaces.sq_le_HkIntegrand_z α k f z θ (i + 1) hik
    have h1 : Step.Zsum (k - 1) (Work.Spaces.Dz f) z θ
        = ∑ i ∈ Finset.range k,
            (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * Step.Zu z θ) ^ 2 := by
      unfold Step.Zsum
      exact Finset.sum_congr (by rw [show k - 1 + 1 = k from by omega])
        (fun i _ => rfl)
    rw [h1]
    calc (∑ i ∈ Finset.range k,
          (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * Step.Zu z θ) ^ 2)
        ≤ ∑ _i ∈ Finset.range k, Work.Spaces.HkIntegrand α k f z θ :=
          Finset.sum_le_sum hterm
      _ = (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hM : Step.Msum α (k - 1) (Work.Spaces.Dz f) z θ
      ≤ ((k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ := by
    rw [Step.Msum_eq_rows, show k - 1 + 1 = k from by omega]
    have hterm : ∀ i ∈ Finset.range k,
        (∑ j ∈ Finset.range (k - i),
          (if 1 ≤ i then (Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ := by
      intro i hi
      have hstep : (∑ j ∈ Finset.range (k - i),
          (if 1 ≤ i then (Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ ∑ _j ∈ Finset.range (k - i), Work.Spaces.HkIntegrand α k f z θ := by
        refine Finset.sum_le_sum (fun j hj => ?_)
        by_cases hi1 : 1 ≤ i
        · rw [if_pos hi1]
          rw [mixed_shift_apply_smooth f hz hθ hg]
          have hj' : i + (j + 1) ≤ k := by
            have := Finset.mem_range.mp hj
            omega
          exact Work.Spaces.sq_le_HkIntegrand_mixed α k f z θ i (j + 1) hi1 hj'
        · rw [if_neg hi1]
          exact hHnn
      refine le_trans hstep ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hcast : ((k - i : ℕ) : ℝ) ≤ (k : ℝ) := by
        have : k - i ≤ k := by omega
        exact_mod_cast this
      have hci : (0 : ℝ) ≤ ((k - i : ℕ) : ℝ) := by positivity
      nlinarith [hHnn, hcast, hci]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    have hsum : (∑ _i ∈ Finset.range k, (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ)
        = ((k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    exact hsum.le
  rw [Step.HkIntegrand_eq α k f z θ] at hZ hM ⊢
  rw [Step.HkIntegrand_eq α (k - 1) (Work.Spaces.Dz f) z θ]
  have hnn : 0 ≤ Step.Zsum k f z θ + Step.Msum α k f z θ :=
    Work.Spaces.HkIntegrand_nonneg α k f z θ
  nlinarith [hZ, hM, hnn]

/-! ## Almost everywhere statements on the product measure -/

/-- A pointwise inequality on the open quadrant holds almost everywhere for the measure
`(volume.restrict Iz).prod (volume.restrict Iθ)`, since the open quadrant agrees with
`Iz ×ˢ Iθ` up to a null set. -/
private lemma ae_le_of_forall_on_Qd {F G : ℝ × ℝ → ℝ} (h : ∀ p ∈ Qd, F p ≤ G p) :
    F ≤ᵐ[(volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)] G := by
  have hprod : (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ)) =ᵐ[volume.prod volume] Qd :=
    MeasureTheory.Measure.set_prod_ae_eq
      (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm
      (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := Real.pi / 2)).symm
  rw [MeasureTheory.Measure.prod_restrict, Measure.restrict_congr_set hprod]
  exact MeasureTheory.ae_restrict_of_forall_mem isOpen_Qd.measurableSet h

/-- Monotonicity of the `H^k` integrand in the regularity index. -/
private lemma HkIntegrand_le_of_le (α : ℝ) {m n : ℕ} (hmn : m ≤ n) (f : ℝ → ℝ → ℝ)
    (z θ : ℝ) :
    Work.Spaces.HkIntegrand α m f z θ ≤ Work.Spaces.HkIntegrand α n f z θ :=
  Nat.le_induction le_rfl
    (fun l _ ih => le_trans ih (Work.Spaces.HkIntegrand_mono α l f z θ)) n hmn

/-- Integrability of a nonnegative function that is a.e. dominated by an integrable one. -/
private lemma integrable_of_le_of_nonneg {F G : ℝ × ℝ → ℝ} {ν : Measure (ℝ × ℝ)}
    (hF : ∀ p, 0 ≤ F p) (hG : Integrable G ν) (hFG : ∀ᵐ p ∂ν, F p ≤ G p)
    (hmeas : AEStronglyMeasurable F ν) : Integrable F ν :=
  hG.mono' hmeas (hFG.mono fun p hp => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hF p)]
    exact hp)

/-! ## The induction step for `HkSq` -/

theorem HkSq_step_le {k : ℕ} (hk : 1 ≤ k) (α : ℝ) (f : ℝ → ℝ → ℝ)
    (hcd : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hmem : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkSq α k f ≤ Work.Spaces.HkSq α (k - 1) f
      + ((k : ℝ) + 1) * Work.Spaces.HkSq α (k - 1) (Work.Spaces.Dz f)
      + ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed 0 k f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
  have hcdtop : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) Qd := by
    have h' : ContDiffOn ℝ (((⊤ : ℕ∞)) : WithTop ℕ∞) (Function.uncurry f) Qd := by
      rw [contDiffOn_iff_forall_nat_le]
      exact fun m _ => hcd m
    exact h'
  have hDz : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.Dz f)) Qd :=
    Work.FTS.LocData.contDiffOn_Dz isOpen_Qd hcdtop
  have hk1 : k - 1 ≤ k := by omega
  -- the four integrands and the bounding function, on the product space
  set A : ℝ × ℝ → ℝ := fun p => Work.Spaces.HkIntegrand α k f p.1 p.2 with eA
  set A1 : ℝ × ℝ → ℝ := fun p => Work.Spaces.HkIntegrand α (k - 1) f p.1 p.2 with eA1
  set A2 : ℝ × ℝ → ℝ :=
    fun p => Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) p.1 p.2 with eA2
  set A3 : ℝ × ℝ → ℝ :=
    fun p => (Work.Spaces.mixed 0 k f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2 with eA3
  set F1 : ℝ × ℝ → ℝ := fun p => A1 p + ((k : ℝ) + 1) * A2 p with eF1
  set B : ℝ × ℝ → ℝ := fun p => F1 p + A3 p with eB
  set μ : Measure (ℝ × ℝ) :=
    (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) with eMu
  -- strong measurability, from continuity on the open quadrant
  have hA_aesm : AEStronglyMeasurable A μ := by
    rw [eA, eMu]
    exact Work.Spaces.aesm_of_continuousOn_Qd _
      (continuousOn_HkIntegrand_Qd α k f hcdtop)
  have hA1_aesm : AEStronglyMeasurable A1 μ := by
    rw [eA1, eMu]
    exact Work.Spaces.aesm_of_continuousOn_Qd _
      (continuousOn_HkIntegrand_Qd α (k - 1) f hcdtop)
  have hA2_aesm : AEStronglyMeasurable A2 μ := by
    rw [eA2, eMu]
    exact Work.Spaces.aesm_of_continuousOn_Qd _
      (continuousOn_HkIntegrand_Qd α (k - 1) (Work.Spaces.Dz f) hDz)
  have hA3_aesm : AEStronglyMeasurable A3 μ := by
    rw [eA3, eMu]
    exact Work.Spaces.aesm_of_continuousOn_Qd _
      (continuousOn_mixed_sq_Wt_Qd α 0 k f hcdtop)
  -- integrability of the level-`k` integrand, from the hypothesis `HkMem α k f`
  have hA_prod : Integrable A μ := by
    rw [eMu]
    rw [integrable_prod_iff hA_aesm]
    constructor
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => ?_)
      rw [eA]
      exact hmem.1 z hz
    · refine hmem.2.congr ?_
      filter_upwards with z
      rw [eA]
      exact integral_congr_ae (Eventually.of_forall fun θ => by
        simp only [Real.norm_eq_abs, abs_of_nonneg (Work.Spaces.HkIntegrand_nonneg α k f z θ)])
  -- the three summands of the right-hand side
  have hA1_le : ∀ p, A1 p ≤ A p := fun p => by
    rw [eA1, eA]
    exact HkIntegrand_le_of_le α hk1 f p.1 p.2
  have hA1_int : Integrable A1 μ :=
    integrable_of_le_of_nonneg
      (fun p => by rw [eA1]; exact Work.Spaces.HkIntegrand_nonneg α (k - 1) f p.1 p.2)
      hA_prod (Eventually.of_forall hA1_le) hA1_aesm
  have hA3_le : ∀ p, A3 p ≤ A p := fun p => by
    rw [eA3, eA]
    exact Work.Spaces.sq_le_HkIntegrand_mixed α k f p.1 p.2 k 0 hk (by omega)
  have hA3_int : Integrable A3 μ :=
    integrable_of_le_of_nonneg
      (fun p => by rw [eA3]; exact sq_nonneg _)
      hA_prod (Eventually.of_forall hA3_le) hA3_aesm
  have hA2_le : ∀ p ∈ Qd, A2 p ≤ ((k : ℝ) + (k : ℝ) * (k : ℝ)) * A p := by
    rintro ⟨z, θ⟩ ⟨hz, hθ⟩
    rw [eA2, eA]
    exact HkIntegrand_shift_le_smooth α hk f hz hθ hcdtop
  have hA2_bound : A2 ≤ᵐ[μ] fun p => ((k : ℝ) + (k : ℝ) * (k : ℝ)) * A p := by
    rw [eMu]
    exact ae_le_of_forall_on_Qd hA2_le
  have hA2_int : Integrable A2 μ :=
    integrable_of_le_of_nonneg
      (fun p => by
        rw [eA2]; exact Work.Spaces.HkIntegrand_nonneg α (k - 1) (Work.Spaces.Dz f) p.1 p.2)
      (hA_prod.const_mul _) hA2_bound hA2_aesm
  have hCA2_int : Integrable (fun p => ((k : ℝ) + 1) * A2 p) μ := hA2_int.const_mul _
  have hF1_int : Integrable F1 μ := by
    rw [eF1]
    exact hA1_int.add hCA2_int
  have hB_int : Integrable B μ := by
    rw [eB]
    exact hF1_int.add hA3_int
  -- the pointwise step, integrated
  have hA_le_B_pt : ∀ p ∈ Qd, A p ≤ B p := by
    rintro ⟨z, θ⟩ ⟨hz, hθ⟩
    rw [eA, eB, eF1, eA1, eA2, eA3]
    exact HkIntegrand_step_le_smooth hk α f hz hθ hcdtop
  have hA_le_B : A ≤ᵐ[μ] B := by
    rw [eMu]
    exact ae_le_of_forall_on_Qd hA_le_B_pt
  have hA_nn : 0 ≤ᵐ[μ] A := Eventually.of_forall fun p => by
    rw [eA]; exact Work.Spaces.HkIntegrand_nonneg α k f p.1 p.2
  have hmain : ∫ p, A p ∂μ ≤ ∫ p, B p ∂μ :=
    integral_mono_of_nonneg hA_nn hB_int hA_le_B
  -- splitting the right-hand side
  have hsplitF1 : ∫ p, F1 p ∂μ
      = ∫ p, A1 p ∂μ + ∫ p, ((k : ℝ) + 1) * A2 p ∂μ := by
    rw [eF1]
    exact integral_add hA1_int hCA2_int
  have hsplit : ∫ p, B p ∂μ
      = (∫ p, A1 p ∂μ) + ((k : ℝ) + 1) * (∫ p, A2 p ∂μ) + ∫ p, A3 p ∂μ := by
    have h1 : ∫ p, B p ∂μ = ∫ p, F1 p ∂μ + ∫ p, A3 p ∂μ := by
      rw [eB]
      exact integral_add hF1_int hA3_int
    have h2 : ∫ p, F1 p ∂μ
        = (∫ p, A1 p ∂μ) + ((k : ℝ) + 1) * (∫ p, A2 p ∂μ) := by
      rw [hsplitF1, integral_const_mul]
    rw [h1, h2]
  -- product integrability of the pieces, and the conversion of the integrals
  have hA_prod' : Integrable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k f p.1 p.2)
      ((volume.prod volume).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := by
    rw [← MeasureTheory.Measure.prod_restrict, ← eMu]
    exact hA_prod
  have hA1_prod' : Integrable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α (k - 1) f p.1 p.2)
      ((volume.prod volume).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := by
    rw [← MeasureTheory.Measure.prod_restrict, ← eMu]
    exact hA1_int
  have hA2_prod' : Integrable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) p.1 p.2)
      ((volume.prod volume).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := by
    rw [← MeasureTheory.Measure.prod_restrict, ← eMu]
    exact hA2_int
  have hA3_prod' : Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.mixed 0 k f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      ((volume.prod volume).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := by
    rw [← MeasureTheory.Measure.prod_restrict, ← eMu]
    exact hA3_int
  have hA_eq : ∫ p, A p ∂μ
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
    rw [eA, eMu, MeasureTheory.Measure.prod_restrict]
    exact MeasureTheory.setIntegral_prod
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k f p.1 p.2) hA_prod'
  have hA1_eq : ∫ p, A1 p ∂μ = Work.Spaces.HkSq α (k - 1) f := by
    rw [eA1, eMu, MeasureTheory.Measure.prod_restrict]
    exact MeasureTheory.setIntegral_prod
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α (k - 1) f p.1 p.2) hA1_prod'
  have hA2_eq : ∫ p, A2 p ∂μ = Work.Spaces.HkSq α (k - 1) (Work.Spaces.Dz f) := by
    rw [eA2, eMu, MeasureTheory.Measure.prod_restrict]
    exact MeasureTheory.setIntegral_prod
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) p.1 p.2)
      hA2_prod'
  have hA3_eq : ∫ p, A3 p ∂μ
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed 0 k f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
    rw [eA3, eMu, MeasureTheory.Measure.prod_restrict]
    exact MeasureTheory.setIntegral_prod
      (fun p : ℝ × ℝ => (Work.Spaces.mixed 0 k f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      hA3_prod'
  calc Work.Spaces.HkSq α k f
      = ∫ p, A p ∂μ := hA_eq.symm
    _ ≤ ∫ p, B p ∂μ := hmain
    _ = (∫ p, A1 p ∂μ) + ((k : ℝ) + 1) * (∫ p, A2 p ∂μ) + ∫ p, A3 p ∂μ := hsplit
    _ = Work.Spaces.HkSq α (k - 1) f
          + ((k : ℝ) + 1) * Work.Spaces.HkSq α (k - 1) (Work.Spaces.Dz f)
          + ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.mixed 0 k f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
        rw [hA1_eq, hA2_eq, hA3_eq]

end Work.FTS.EllipticEst.remov
