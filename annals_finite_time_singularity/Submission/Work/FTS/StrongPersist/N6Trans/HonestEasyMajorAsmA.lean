/-
The slot-pairing helpers of the open-class (honest) assembly.
Part of the auxiliary module `HonestEasyMajorAux` for
`HonestEasyMajorLem`; see the aggregator file for the full description.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.H2.T1EasyBound
import Submission.Work.FTS.H2.T2Aesm
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.H2.T1Q.Basic
import Submission.Work.FTS.H2.HQ.HardyZQ
import Submission.Work.FTS.H2.MinLeAvg
import Submission.Work.FTS.H2.OscSqLe
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.H2.HQ.DthDzIterComm
import Submission.Work.Spaces.bt_aux
import Submission.Work.H2.T1Q.SlotOpen
import Submission.Work.H2.T1Q.SlotPtQ
import Submission.Work.H2.T1Q.ExpandQ
import Submission.Work.H2.T1Q.T1EasyContQ
import Submission.Work.H2.T1Q.ExcBoundQ
import Submission.Work.H2.T1Q.SupThetaIntQ
import Submission.Work.H2.T1Q.SliceSupOpen
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter
open Work.Spaces
open Work.FTS.H2
open Work.H2.T1Q

namespace Work.FTS.StrongPersist.N6Trans.HonestEasyMajorAux

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-! ## Open-class twins of the two continuity lemmas used below -/

/-- Continuity of the `i`-th pure `D_z`-slot on the open quadrant, in the open class
(`Work.H2.T1Q.continuousOn_dzIter_qd` with `SmoothQuad` replaced by `SmoothOpen`; the domain
`quadQ = Ioi 0 ×ˢ Ioo 0 (π/2)` is exactly `SmoothOpen`'s domain). -/
theorem continuousOn_dzIter_qd_open (u : ℝ → ℝ → ℝ) (hu : Work.FTS.EllipticEst.SmoothOpen u)
    (i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter i u p.1 p.2) Work.FTS.H2.HQ.quadQ :=
  (hu.DzIter i).continuousOn

/-- Continuity of the `(j,i)`-th mixed slot on the open quadrant, in the open class. -/
theorem continuousOn_mixed_qd_open (u : ℝ → ℝ → ℝ) (hu : Work.FTS.EllipticEst.SmoothOpen u)
    (j i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i u p.1 p.2) Work.FTS.H2.HQ.quadQ :=
  (hu.mixed j i).continuousOn


set_option autoImplicit false
set_option maxHeartbeats 1600000

open Work.FTS.H2

/-! ## The `2`-dimensional assembly of the interior `T1Easy` estimate

This file assembles the interior (`SmoothQuad`) version of the pointwise majorant bound of
`Submission/Work/FTS/H2/T1EasyBound.lean` (`EMS_int_and_le`), replacing

* the closed-quadrant slot bounds `xDKf_bound`/`xDKg_bound`/`yMKf_bound`/`yMKg_bound` by
  bounds whose pointwise comparison is the *open-quadrant* `SlotPtQ` estimate
  (`xD_Kf_pt`, `xD_Kg_pt`, `yM_Kf_pt`, `yM_Kg_mixed_pt`) and whose integral is bounded by
  `Work.H2.T1Q.term_of_slot_open` (`slotIntBoundQ_o` below);
* the closed-quadrant `V`-bound of `term_of_slot` by the open-quadrant one;
* the exceptional summand `(i,j,a,b) = (1,3,0,3)` by `Work.H2.T1Q.ExcBoundOpen`. -/

/-! ## Almost-everywhere positivity of the radial variable -/

/-- Almost every point of the product measure `pm` has a positive radial coordinate: the
radial measure is `volume.restrict Iz`, and `{0}` is null for it. -/
theorem ae_pm_z_pos_o : ∀ᵐ p ∂Work.FTS.H2.pm, 0 < p.1 := by
  rw [Work.FTS.H2.pm, MeasureTheory.ae_iff]
  have hset : {p : ℝ × ℝ | ¬ (0 < p.1)} = Set.Iic (0 : ℝ) ×ˢ Set.univ := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_Iic, Set.mem_univ, and_true,
      Set.mem_setOf_eq, not_lt]
  rw [hset, MeasureTheory.Measure.prod_prod]
  have h0 : (MeasureTheory.volume.restrict Work.Spaces.Iz) (Set.Iic (0 : ℝ)) = 0 := by
    rw [MeasureTheory.Measure.restrict_apply measurableSet_Iic]
    have hz : Set.Iic (0 : ℝ) ∩ Work.Spaces.Iz = {0} := by
      ext x
      simp only [Work.Spaces.Iz, Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ici,
        Set.mem_singleton_iff]
      constructor
      · intro h; exact le_antisymm h.1 h.2
      · intro h; simp [h]
    rw [hz]
    exact MeasureTheory.measure_singleton 0
  rw [h0, zero_mul]

/-! ## Measurability of the Leibniz summands -/

/-- A.e. strong measurability of the `D_z`-slot summand for `SmoothQuad` data. -/
theorem xD_aesm_q_o (f g : ℝ → ℝ → ℝ) (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (i b : ℕ) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => xD f g i b p.1 p.2) Work.FTS.H2.pm := by
  have h1 := continuousOn_dzIter_qd_open f hf b
  have h2 := continuousOn_mixed_qd_open g hg (i - b) 1
  have h3 := continuousOn_dzIter_qd_open g hg i
  refine aesm_of_Qd ?_
  simp only [xD]
  exact continuousOn_const.mul (((h1.mul h2).mul h3).mul (continuousOn_Whz_quad.pow 2))

/-- A.e. strong measurability of the mixed-slot summand for `SmoothQuad` data. -/
theorem yM_aesm_q_o (α : ℝ) (f g : ℝ → ℝ → ℝ) (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (i j a b : ℕ) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => yM α f g i j a b p.1 p.2) Work.FTS.H2.pm := by
  have h1 := continuousOn_mixed_qd_open f hf b a
  have h2 := continuousOn_mixed_qd_open g hg (j - b) (i - a + 1)
  have h3 := continuousOn_mixed_qd_open g hg j i
  refine aesm_of_Qd ?_
  simp only [yM]
  exact continuousOn_const.mul (((h1.mul h2).mul h3).mul ((continuousOn_Wm_quad α).pow 2))

/-! ## The generic slot pairing -/

/-- **Slot pairing with a bounded third factor.**  If `A`, `B` are nonnegative and their squares
are dominated by the `ℋ⁴`-integrands of `u`, `v`, and if `K ≥ 0`, then `K·(A·B)` is integrable
on `pm` with integral at most `K·|u|_{ℋ⁴}·|v|_{ℋ⁴}`.

This is `Work.H2.T1Q.term_of_slot_open` with the third factor `V` equal to the constant `K`
(so that `V`'s open-quadrant bound `|K| ≤ K` is `hK`). -/
theorem slotIntBoundQ_o (α : ℝ) (u v : ℝ → ℝ → ℝ) (hmu : Work.Spaces.HkMem α 4 u)
    (hmv : Work.Spaces.HkMem α 4 v) (A B : ℝ → ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hA0 : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ A z θ)
    (hB0 : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ B z θ)
    (hA : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      (A z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 u z θ)
    (hB : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      (B z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 v z θ)
    (hAcont : ContinuousOn (Function.uncurry A) Work.FTS.H2.Qd)
    (hBcont : ContinuousOn (Function.uncurry B) Work.FTS.H2.Qd)
    (hA0z : ∀ θ : ℝ, A 0 θ = 0) (hB0z : ∀ θ : ℝ, B 0 θ = 0) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => K * (A p.1 p.2 * B p.1 p.2))
        Work.FTS.H2.pm ∧
      ∫ p, K * (A p.1 p.2 * B p.1 p.2) ∂Work.FTS.H2.pm
        ≤ K * Work.Spaces.HkNorm α 4 u * Work.Spaces.HkNorm α 4 v := by
  have hAmeas : ∀ z ∈ Work.Spaces.Iz,
      AEStronglyMeasurable (fun θ => A z θ) (volume.restrict Work.Spaces.Iθ) := by
    intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h | h
    · subst h
      exact aestronglyMeasurable_const.congr (Eventually.of_forall fun θ => (hA0z θ).symm)
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry A) hAcont h
  have hBmeas : ∀ z ∈ Work.Spaces.Iz,
      AEStronglyMeasurable (fun θ => B z θ) (volume.restrict Work.Spaces.Iθ) := by
    intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h | h
    · subst h
      exact aestronglyMeasurable_const.congr (Eventually.of_forall fun θ => (hB0z θ).symm)
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry B) hBcont h
  have hVABmeas : AEStronglyMeasurable
      (Function.uncurry (fun z θ => |K * A z θ * B z θ|)) Work.FTS.H2.pm :=
    aesm_of_Qd (((continuousOn_const.mul hAcont).mul hBcont).abs)
  obtain ⟨hint, hbd⟩ := term_of_slot_open α u v hmu hmv A B (fun _ _ => K) K hK
    (fun z hz θ hθ => by simp [abs_of_nonneg hK]) hA0 hB0 hA hB hAmeas hBmeas hVABmeas
  have hae : (fun p : ℝ × ℝ => |K * A p.1 p.2 * B p.1 p.2|)
      =ᵐ[Work.FTS.H2.pm] (fun p : ℝ × ℝ => K * (A p.1 p.2 * B p.1 p.2)) := by
    filter_upwards [Work.FTS.H2.ae_pm_mem] with p hp
    rw [abs_of_nonneg
      (mul_nonneg (mul_nonneg hK (hA0 p.1 hp.1 p.2 hp.2)) (hB0 p.1 hp.1 p.2 hp.2))]
    ring
  exact ⟨hint.congr hae, by rw [← integral_congr_ae hae]; exact hbd⟩

/-! ## The four per-summand slot bounds -/

/-- The `D_z`-slot with an `f`-factor of order `≤ 2`: the `g`-factors are the two `ℋ⁴`-slots
and the `f`-factor is bounded by the constant `Kf`. -/
theorem xD_Kf_int_q_o (α : ℝ) (g : ℝ → ℝ → ℝ) (Kf : ℝ) (hKf0 : 0 ≤ Kf)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hmemg : Work.Spaces.HkMem α 4 g)
    (i b : ℕ) (hi : i ≤ 4) (hib : i - b ≤ 3) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => Kf *
        ((|Work.Spaces.mixed (i - b) 1 g p.1 p.2| * Wm α p.1 p.2)
          * (|Work.Spaces.DzIter i g p.1 p.2| * Whz p.1 p.2))) Work.FTS.H2.pm ∧
      ∫ p, Kf * ((|Work.Spaces.mixed (i - b) 1 g p.1 p.2| * Wm α p.1 p.2)
          * (|Work.Spaces.DzIter i g p.1 p.2| * Whz p.1 p.2)) ∂Work.FTS.H2.pm
        ≤ Kf * Work.Spaces.HkNorm α 4 g * Work.Spaces.HkNorm α 4 g :=
  slotIntBoundQ_o α g g hmemg hmemg
    (fun z θ => |Work.Spaces.mixed (i - b) 1 g z θ| * Wm α z θ)
    (fun z θ => |Work.Spaces.DzIter i g z θ| * Whz z θ) Kf hKf0
    (fun z hz θ hθ => mul_nonneg (abs_nonneg _) (Wm_nonneg α hθ))
    (fun z hz θ hθ => mul_nonneg (abs_nonneg _) (Whz_nonneg hθ))
    (fun z hz θ hθ => by
      simpa only [Wm, mul_pow, sq_abs] using
        Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ 1 (i - b) (le_refl 1) (by omega))
    (fun z hz θ hθ => by
      simpa only [Whz, mul_pow, sq_abs] using Work.Spaces.sq_le_HkIntegrand_z α 4 g z θ i hi)
    ((continuousOn_mixed_qd_open g hg (i - b) 1).abs.mul (continuousOn_Wm_quad α))
    ((continuousOn_dzIter_qd_open g hg i).abs.mul continuousOn_Whz_quad)
    (fun θ => by rw [Wm, Work.Spaces.Wt, w_zero, zero_mul, mul_zero])
    (fun θ => by rw [Whz, w_zero, zero_div, mul_zero])

/-- The `D_z`-slot with the `g`-factor `D_z^{i-b}D_θg` of order `≤ 2` (i.e. `b ≥ 3`): the
`f`- and `g`-slots are the two `ℋ⁴`-slots and the remaining `g`-factor is bounded by `Kg`. -/
theorem xD_Kg_int_q_o (α : ℝ) (f g : ℝ → ℝ → ℝ) (Kg : ℝ) (hKg0 : 0 ≤ Kg)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hmemf : Work.Spaces.HkMem α 4 f) (hmemg : Work.Spaces.HkMem α 4 g)
    (i b : ℕ) (hi : i ≤ 4) (hb3 : 3 ≤ b) (hbi : b ≤ i) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => Kg *
        ((|Work.Spaces.DzIter b f p.1 p.2| * Whz p.1 p.2)
          * (|Work.Spaces.DzIter i g p.1 p.2| * Whz p.1 p.2))) Work.FTS.H2.pm ∧
      ∫ p, Kg * ((|Work.Spaces.DzIter b f p.1 p.2| * Whz p.1 p.2)
          * (|Work.Spaces.DzIter i g p.1 p.2| * Whz p.1 p.2)) ∂Work.FTS.H2.pm
        ≤ Kg * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g :=
  slotIntBoundQ_o α f g hmemf hmemg
    (fun z θ => |Work.Spaces.DzIter b f z θ| * Whz z θ)
    (fun z θ => |Work.Spaces.DzIter i g z θ| * Whz z θ) Kg hKg0
    (fun z hz θ hθ => mul_nonneg (abs_nonneg _) (Whz_nonneg hθ))
    (fun z hz θ hθ => mul_nonneg (abs_nonneg _) (Whz_nonneg hθ))
    (fun z hz θ hθ => by
      simpa only [Whz, mul_pow, sq_abs] using Work.Spaces.sq_le_HkIntegrand_z α 4 f z θ b
        (by omega))
    (fun z hz θ hθ => by
      simpa only [Whz, mul_pow, sq_abs] using Work.Spaces.sq_le_HkIntegrand_z α 4 g z θ i hi)
    ((continuousOn_dzIter_qd_open f hf b).abs.mul continuousOn_Whz_quad)
    ((continuousOn_dzIter_qd_open g hg i).abs.mul continuousOn_Whz_quad)
    (fun θ => by rw [Whz, w_zero, zero_div, mul_zero])
    (fun θ => by rw [Whz, w_zero, zero_div, mul_zero])

/-- The mixed slot with an `f`-factor of order `≤ 2`: the two `g`-factors are the `ℋ⁴`-slots
and the `f`-factor is bounded by `Kf`. -/
theorem yM_Kf_int_q_o (α : ℝ) (g : ℝ → ℝ → ℝ) (Kf : ℝ) (hKf0 : 0 ≤ Kf)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hmemg : Work.Spaces.HkMem α 4 g)
    (i j a b : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) (hai : a ≤ i) (hbj : b ≤ j)
    (hnh : ¬(a = 0 ∧ b = 0 ∧ i + j = 4)) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => Kf *
        ((|Work.Spaces.mixed (j - b) (i - a + 1) g p.1 p.2| * Wm α p.1 p.2)
          * (|Work.Spaces.mixed j i g p.1 p.2| * Wm α p.1 p.2))) Work.FTS.H2.pm ∧
      ∫ p, Kf * ((|Work.Spaces.mixed (j - b) (i - a + 1) g p.1 p.2| * Wm α p.1 p.2)
          * (|Work.Spaces.mixed j i g p.1 p.2| * Wm α p.1 p.2)) ∂Work.FTS.H2.pm
        ≤ Kf * Work.Spaces.HkNorm α 4 g * Work.Spaces.HkNorm α 4 g := by
  have hord : (i - a + 1) + (j - b) ≤ 4 := by
    by_cases hab0 : a + b = 0
    · have ha0 : a = 0 := by omega
      have hb0 : b = 0 := by omega
      have hij3 : i + j ≤ 3 := by
        by_contra hcon
        exact hnh ⟨ha0, hb0, by omega⟩
      omega
    · omega
  exact slotIntBoundQ_o α g g hmemg hmemg
    (fun z θ => |Work.Spaces.mixed (j - b) (i - a + 1) g z θ| * Wm α z θ)
    (fun z θ => |Work.Spaces.mixed j i g z θ| * Wm α z θ) Kf hKf0
    (fun z hz θ hθ => mul_nonneg (abs_nonneg _) (Wm_nonneg α hθ))
    (fun z hz θ hθ => mul_nonneg (abs_nonneg _) (Wm_nonneg α hθ))
    (fun z hz θ hθ => by
      simpa only [Wm, mul_pow, sq_abs] using
        Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ (i - a + 1) (j - b) (by omega) hord)
    (fun z hz θ hθ => by
      simpa only [Wm, mul_pow, sq_abs] using
        Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ i j hi hij)
    ((continuousOn_mixed_qd_open g hg (j - b) (i - a + 1)).abs.mul (continuousOn_Wm_quad α))
    ((continuousOn_mixed_qd_open g hg j i).abs.mul (continuousOn_Wm_quad α))
    (fun θ => by rw [Wm, Work.Spaces.Wt, w_zero, zero_mul, mul_zero])
    (fun θ => by rw [Wm, Work.Spaces.Wt, w_zero, zero_mul, mul_zero])

/-- The mixed slot whose `g`-factor `D_z^{j-b}D_θ^{i-a+1}g` has `θ`-order `≥ 1` and total order
`≤ 2`: the `f`- and `g`-slots are the two `ℋ⁴`-slots and the remaining `g`-factor is bounded
by `Kg`. -/
theorem yM_Kg_int_q_o (α : ℝ) (f g : ℝ → ℝ → ℝ) (Kg : ℝ) (hKg0 : 0 ≤ Kg)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hmemf : Work.Spaces.HkMem α 4 f) (hmemg : Work.Spaces.HkMem α 4 g)
    (i j a b : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) (hai : a ≤ i) (hbj : b ≤ j)
    (ha1 : 1 ≤ a) (hab3 : 3 ≤ a + b) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => Kg *
        ((|Work.Spaces.mixed b a f p.1 p.2| * Wm α p.1 p.2)
          * (|Work.Spaces.mixed j i g p.1 p.2| * Wm α p.1 p.2))) Work.FTS.H2.pm ∧
      ∫ p, Kg * ((|Work.Spaces.mixed b a f p.1 p.2| * Wm α p.1 p.2)
          * (|Work.Spaces.mixed j i g p.1 p.2| * Wm α p.1 p.2)) ∂Work.FTS.H2.pm
        ≤ Kg * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g :=
  slotIntBoundQ_o α f g hmemf hmemg
    (fun z θ => |Work.Spaces.mixed b a f z θ| * Wm α z θ)
    (fun z θ => |Work.Spaces.mixed j i g z θ| * Wm α z θ) Kg hKg0
    (fun z hz θ hθ => mul_nonneg (abs_nonneg _) (Wm_nonneg α hθ))
    (fun z hz θ hθ => mul_nonneg (abs_nonneg _) (Wm_nonneg α hθ))
    (fun z hz θ hθ => by
      simpa only [Wm, mul_pow, sq_abs] using
        Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ a b ha1 (by omega))
    (fun z hz θ hθ => by
      simpa only [Wm, mul_pow, sq_abs] using
        Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ i j hi hij)
    ((continuousOn_mixed_qd_open f hf b a).abs.mul (continuousOn_Wm_quad α))
    ((continuousOn_mixed_qd_open g hg j i).abs.mul (continuousOn_Wm_quad α))
    (fun θ => by rw [Wm, Work.Spaces.Wt, w_zero, zero_mul, mul_zero])
    (fun θ => by rw [Wm, Work.Spaces.Wt, w_zero, zero_mul, mul_zero])


end Work.FTS.StrongPersist.N6Trans.HonestEasyMajorAux
