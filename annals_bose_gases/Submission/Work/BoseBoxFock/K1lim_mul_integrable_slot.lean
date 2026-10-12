import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseBoxFock.K1lim_ae_congr
import Submission.Work.BoseBoxFock.K1lim_meas_bdd
import Submission.Work.BoseBoxFock.lintegral_boxPow_eval_snd
import Submission.Work.BoseBoxFock.lintegral_tsum_translate_boxL_le
import Submission.Work.BoseBoxFock.pairRowDirDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.K1lim_mul_integrable_slot`

The `Q₂`-row limit kernel `K1lim ℓ W` (`pinQLimDefs`) against a bounded, box-supported test
function `H` on the `n`-particle configuration space `Xn n × E3`: the product is `L¹`.

The weight `W` is only assumed **integrable** (the honest hypothesis of the `Q₂` row against the
potential `W = W1fun`, which is only `L¹`).  The four rows of `K1lim` are then controlled as
follows:

* the three `χ̂`-rows `pinQBl/pinQCl/pinQDl` are **uniformly bounded** for *every* weight
  (`errBdd_pinQBl_bdd` etc.), and the cutoffs `chiScale`, `thetaFun` are bounded too;
* the `χχ`-row carries the periodisation `latPer3 ℓ W (w − y) = ℓ³ ∑_m W (w − y + ℓ•latVec m)`,
  which is *not* bounded, but whose `lintegral` over the box is controlled by the `L¹` mass of `W`
  through the covering multiplicity of the lattice translates of the box
  (`Work.BoseBoxFock.lintegral_tsum_translate_boxL_le`).

The file also provides the measure-theoretic transport from the two-particle box to the
`n`-particle box: the box-restricted `lintegral` factorises along the projection
`z ↦ (z.1 p.2, z.2)` (`lintegral_boxPow_eval_snd`), and that projection is
quasi-measure-preserving (`quasiMeasurePreserving_eval_pair`).
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-! ## 0. Elementary measurability vocabulary -/

/-- The sharp box indicator `θ_Λ` is measurable (it is the indicator of the measurable box
`boxL ℓ`). -/
theorem thetaFun_measurable (ℓ : ℝ) :
    Measurable (Work.BoseK15.corpusBox.thetaFun ℓ) := by
  have h : Work.BoseK15.corpusBox.thetaFun ℓ
      = Set.indicator (Work.BoseK15.corpusBox.boxL ℓ) (fun _ : E3 => (1 : ℂ)) := by
    funext z
    rw [Work.BoseB4.BoxData.thetaFun_apply]
    by_cases hz : z ∈ Work.BoseK15.corpusBox.boxL ℓ <;> simp [hz]
  rw [h]
  exact measurable_const.indicator (Work.BoseB4.BoxData.boxL_measurableSet _ ℓ)

/-- The periodisation `latPer ℓ U` is measurable when `U` is. -/
theorem measurable_latPer {ℓ : ℝ} {U : E3 → ℝ} (hU : Measurable U) :
    Measurable (LatFourier.latPer ℓ U) := by
  change Measurable (fun z : E3 => LatFourier.latPer ℓ U z)
  have hterm : ∀ m : Fin 3 → ℤ,
      Measurable (fun z : E3 => (U (z + ℓ • latVec m) : ℂ)) := by
    intro m
    exact Complex.continuous_ofReal.measurable.comp
      (hU.comp (by fun_prop : Measurable fun z : E3 => z + ℓ • latVec m))
  have h := Measurable.tsum (L := SummationFilter.unconditional (Fin 3 → ℤ)) hterm
  simpa only [LatFourier.latPer] using h

/-- The limit `χχ`-row `latPer3 ℓ U = ℓ³ · latPer ℓ U` is measurable when `U` is. -/
theorem measurable_latPer3 {ℓ : ℝ} {U : E3 → ℝ} (hU : Measurable U) :
    Measurable (latPer3 ℓ U) := by
  change Measurable (fun z : E3 => latPer3 ℓ U z)
  have h : Measurable (fun z : E3 => (((ℓ ^ 3 : ℝ)) : ℂ) * LatFourier.latPer ℓ U z) :=
    measurable_const.mul (measurable_latPer hU)
  simpa only [latPer3] using h

/-- The limit `χ̂`-row `pinQBl` is measurable — for *every* weight (each summand is continuous). -/
theorem measurable_pinQBl (ℓ : ℝ) (U : E3 → ℝ) : Measurable (pinQBl ℓ U) := by
  change Measurable (fun w : E3 => pinQBl ℓ U w)
  have hterm : ∀ n : Fin 3 → ℤ, Measurable (fun w : E3 =>
      ((Work.BoseFixR.chat U (kmomInt ℓ n) : ℝ) : ℂ)
        * ((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)
        * Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) w : ℝ) : ℂ))) := by
    intro n
    refine Continuous.measurable ?_
    refine Continuous.mul (Continuous.mul continuous_const continuous_const) ?_
    refine Complex.continuous_exp.comp (Continuous.mul continuous_const ?_)
    exact Complex.continuous_ofReal.comp (Continuous.inner continuous_const continuous_id)
  have h := Measurable.tsum (L := SummationFilter.unconditional (Fin 3 → ℤ)) hterm
  simpa only [pinQBl] using h

/-- The limit `χ̂`-row `pinQCl` is measurable — for *every* weight. -/
theorem measurable_pinQCl (ℓ : ℝ) (U : E3 → ℝ) : Measurable (pinQCl ℓ U) := by
  change Measurable (fun y : E3 => pinQCl ℓ U y)
  have hterm : ∀ n : Fin 3 → ℤ, Measurable (fun y : E3 =>
      ((Work.BoseFixR.chat U (kmomInt ℓ n) : ℝ) : ℂ)
        * ((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)
        * Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) y : ℝ) : ℂ)))) := by
    intro n
    refine Continuous.measurable ?_
    refine Continuous.mul (Continuous.mul continuous_const continuous_const) ?_
    refine Complex.continuous_exp.comp (Continuous.neg ?_)
    refine Continuous.mul continuous_const ?_
    exact Complex.continuous_ofReal.comp (Continuous.inner continuous_const continuous_id)
  have h := Measurable.tsum (L := SummationFilter.unconditional (Fin 3 → ℤ)) hterm
  simpa only [pinQCl] using h

/-- **Measurability of the limit pair kernel** for a measurable weight. -/
theorem measurable_uncurry_K1lim {ℓ : ℝ} {U : E3 → ℝ} (hU : Measurable U) :
    Measurable (Function.uncurry (K1lim ℓ U)) := by
  have hun : Function.uncurry (K1lim ℓ U) = fun p : E3 × E3 => K1lim ℓ U p.1 p.2 := rfl
  rw [hun]
  have hchi1 : Measurable (fun p : E3 × E3 => (((Submission.BoseGases.chiScale ℓ p.1 : ℝ)) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp
      ((Submission.BoseGases.chiScale_continuous ℓ).measurable.comp continuous_fst.measurable)
  have hchi2 : Measurable (fun p : E3 × E3 => (((Submission.BoseGases.chiScale ℓ p.2 : ℝ)) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp
      ((Submission.BoseGases.chiScale_continuous ℓ).measurable.comp continuous_snd.measurable)
  have hth1 : Measurable (fun p : E3 × E3 => Work.BoseK15.corpusBox.thetaFun ℓ p.1) :=
    (thetaFun_measurable ℓ).comp continuous_fst.measurable
  have hth2 : Measurable (fun p : E3 × E3 => Work.BoseK15.corpusBox.thetaFun ℓ p.2) :=
    (thetaFun_measurable ℓ).comp continuous_snd.measurable
  have hlat : Measurable (fun p : E3 × E3 => latPer3 ℓ U (p.1 - p.2)) :=
    (measurable_latPer3 hU).comp (by fun_prop)
  have hB : Measurable (fun p : E3 × E3 => pinQBl ℓ U p.1) :=
    (measurable_pinQBl ℓ U).comp continuous_fst.measurable
  have hC : Measurable (fun p : E3 × E3 => pinQCl ℓ U p.2) :=
    (measurable_pinQCl ℓ U).comp continuous_snd.measurable
  have hD : Measurable (fun _ : E3 × E3 => pinQDl ℓ U) := measurable_const
  have h1 : Measurable (fun p : E3 × E3 =>
      (((Submission.BoseGases.chiScale ℓ p.1 : ℝ)) : ℂ)
        * (((Submission.BoseGases.chiScale ℓ p.2 : ℝ)) : ℂ)
        * latPer3 ℓ U (p.1 - p.2)) := (hchi1.mul hchi2).mul hlat
  have h2 : Measurable (fun p : E3 × E3 =>
      (((Submission.BoseGases.chiScale ℓ p.1 : ℝ)) : ℂ)
        * Work.BoseK15.corpusBox.thetaFun ℓ p.2 * pinQBl ℓ U p.1) :=
    (hchi1.mul hth2).mul hB
  have h3 : Measurable (fun p : E3 × E3 =>
      Work.BoseK15.corpusBox.thetaFun ℓ p.1
        * (((Submission.BoseGases.chiScale ℓ p.2 : ℝ)) : ℂ) * pinQCl ℓ U p.2) :=
    (hth1.mul hchi2).mul hC
  have h4 : Measurable (fun p : E3 × E3 =>
      Work.BoseK15.corpusBox.thetaFun ℓ p.1
        * Work.BoseK15.corpusBox.thetaFun ℓ p.2 * pinQDl ℓ U) := (hth1.mul hth2).mul hD
  have hmain : Measurable (fun p : E3 × E3 =>
      (((Submission.BoseGases.chiScale ℓ p.1 : ℝ)) : ℂ)
          * (((Submission.BoseGases.chiScale ℓ p.2 : ℝ)) : ℂ)
          * latPer3 ℓ U (p.1 - p.2)
        - (((Submission.BoseGases.chiScale ℓ p.1 : ℝ)) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun ℓ p.2 * pinQBl ℓ U p.1
        - Work.BoseK15.corpusBox.thetaFun ℓ p.1
          * (((Submission.BoseGases.chiScale ℓ p.2 : ℝ)) : ℂ) * pinQCl ℓ U p.2
        + Work.BoseK15.corpusBox.thetaFun ℓ p.1
          * Work.BoseK15.corpusBox.thetaFun ℓ p.2 * pinQDl ℓ U) :=
    ((h1.sub h2).sub h3).add h4
  have hc : Measurable (fun _ : E3 × E3 => (((ℓ ^ 3)⁻¹ : ℝ) : ℂ)) := measurable_const
  exact hc.mul hmain

/-! ## 1. The limit pair kernel only depends on the a.e. class of the weight -/

/-- The pair kernel is invariant under an a.e. change of the weight (the proof of
`K1lim_ae_congr` works verbatim; the boundedness/compact-support hypotheses of that statement are
not used). -/
theorem K1lim_ae_congr' {ℓ : ℝ} {W₁ W₂ : E3 → ℝ} (h : W₁ =ᵐ[volume] W₂) :
    (fun p : E3 × E3 => K1lim ℓ W₁ p.1 p.2) =ᵐ[volume.prod volume]
      (fun p : E3 × E3 => K1lim ℓ W₂ p.1 p.2) := by
  have hchat : ∀ k : E3, Work.BoseFixR.chat W₁ k = Work.BoseFixR.chat W₂ k :=
    fun k => chat_congr h k
  have hB : pinQBl ℓ W₁ = pinQBl ℓ W₂ := by
    funext w
    apply tsum_congr
    intro n
    rw [hchat (kmomInt ℓ n)]
  have hC : pinQCl ℓ W₁ = pinQCl ℓ W₂ := by
    funext y
    apply tsum_congr
    intro n
    rw [hchat (kmomInt ℓ n)]
  have hD : pinQDl ℓ W₁ = pinQDl ℓ W₂ := by
    apply tsum_congr
    intro n
    rw [hchat (kmomInt ℓ n)]
  filter_upwards [latPer_ae_congr_sub (ℓ := ℓ) h] with p hp
  simp only [K1lim, latPer3, hB, hC, hD, hp]

/-- The uncurried limit pair kernel is a.e. strongly measurable for an integrable weight. -/
theorem aesm_uncurry_K1lim_of_integrable {ℓ : ℝ} {W : E3 → ℝ}
    (hW : MeasureTheory.Integrable W) :
    AEStronglyMeasurable (Function.uncurry (K1lim ℓ W)) (volume.prod volume) := by
  obtain ⟨U, hUm, hWU⟩ : ∃ U : E3 → ℝ, Measurable U ∧ W =ᵐ[volume] U :=
    ⟨AEStronglyMeasurable.mk W hW.aestronglyMeasurable,
      (hW.aestronglyMeasurable.stronglyMeasurable_mk).measurable,
      hW.aestronglyMeasurable.ae_eq_mk⟩
  exact ((measurable_uncurry_K1lim (ℓ := ℓ) hUm).aestronglyMeasurable).congr
    (K1lim_ae_congr' (ℓ := ℓ) hWU).symm

/-! ## 2. The pointwise comparison of the periodisation with the sum of norms -/

/-- `‖latPer ℓ U z‖ ≤ ∑_m ‖U (z + ℓ • latVec m)‖`, in `ℝ≥0∞` (so that the divergent case is
handled automatically). -/
theorem enorm_latPer_le (ℓ : ℝ) (U : E3 → ℝ) (z : E3) :
    ‖LatFourier.latPer ℓ U z‖ₑ ≤ ∑' m : Fin 3 → ℤ, ‖(U (z + ℓ • latVec m) : ℂ)‖ₑ := by
  have h := enorm_tsum_le_tsum_enorm (f := fun m : Fin 3 → ℤ => (U (z + ℓ • latVec m) : ℂ))
  simpa only [LatFourier.latPer] using h

/-! ## 3. The projection `z ↦ (z.1 p, z.2)` is quasi-measure-preserving -/

/-- The projection `z ↦ (z.1 p, z.2)` from `Xn (d+1) × E3` to `E3 × E3` is
quasi-measure-preserving (the fibres over the remaining `d` coordinates have infinite — or, for
`d = 0`, singleton — measure). -/
theorem quasiMeasurePreserving_eval_pair {d : ℕ} (p : Fin (d + 1)) :
    Measure.QuasiMeasurePreserving
      (fun z : Work.BoseDict.Xn (d + 1) × E3 => (z.1 p, z.2))
      (volume : Measure (Work.BoseDict.Xn (d + 1) × E3))
      (volume.prod volume) := by
  have h1 : Measure.QuasiMeasurePreserving (fun x : Work.BoseDict.Xn (d + 1) => x p)
      (volume : Measure (Work.BoseDict.Xn (d + 1))) (volume : Measure E3) := by
    rw [volume_pi]
    exact Measure.quasiMeasurePreserving_eval (fun _ : Fin (d + 1) => (volume : Measure E3)) p
  have h2 : Measure.QuasiMeasurePreserving (fun y : E3 => y) (volume : Measure E3)
      (volume : Measure E3) :=
    (MeasurePreserving.id (volume : Measure E3)).quasiMeasurePreserving
  have h := QuasiMeasurePreserving.prodMap h1 h2
  have hfun : (fun z : Work.BoseDict.Xn (d + 1) × E3 => (z.1 p, z.2))
      = Prod.map (fun x : Work.BoseDict.Xn (d + 1) => x p) (fun y : E3 => y) := rfl
  rw [hfun]
  exact h

/-- The `χχ`-row of the limit pair kernel over the two-particle box: the periodisation is
controlled by the covering multiplicity of the lattice translates of the box. -/
theorem lintegral_latPer3_pair_le {ℓ : ℝ} (hℓ : 0 < ℓ) {U : E3 → ℝ} (hUm : Measurable U) :
    ∫⁻ q : E3 × E3, (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => 1) q.1
        * (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => 1) q.2 * ‖latPer3 ℓ U (q.1 - q.2)‖ₑ
      ≤ (ENNReal.ofReal |ℓ|) ^ 3
        * (MeasureTheory.volume (Work.BoseK15.corpusBox.boxL ℓ)
            * ((((2 + 1 : ℕ) : ENNReal) ^ 3) * ∫⁻ z, ‖(U z : ℂ)‖ₑ)) := by
  set L : Set E3 := Work.BoseK15.corpusBox.boxL ℓ with hL
  set L2 : Set E3 := Work.BoseK15.corpusBox.boxL (2 * ℓ) with hL2
  set g : E3 → ENNReal := fun z => ‖(U z : ℂ)‖ₑ with hg
  set Phi : E3 → ENNReal := fun z => ∑' m : Fin 3 → ℤ, g (z + ℓ • latVec m) with hPhi
  have hgfun : (fun z : E3 => ‖((U z : ℝ) : ℂ)‖ₑ) = fun z : E3 => ENNReal.ofReal ‖((U z : ℝ) : ℂ)‖ :=
    funext fun z => (ofReal_norm _).symm
  have hgm : Measurable g := by
    rw [hg]
    rw [show (fun z : E3 => ‖(U z : ℂ)‖ₑ) = (fun z : E3 => ENNReal.ofReal ‖((U z : ℝ) : ℂ)‖) from hgfun]
    exact ENNReal.measurable_ofReal.comp
      (continuous_norm.measurable.comp (Complex.continuous_ofReal.measurable.comp hUm))
  have hLmeas : MeasurableSet L := by
    rw [hL]; exact Work.BoseB4.BoxData.boxL_measurableSet _ ℓ
  have hL2meas : MeasurableSet L2 := by
    rw [hL2]; exact Work.BoseB4.BoxData.boxL_measurableSet _ (2 * ℓ)
  have hindL : Measurable (L.indicator (fun _ : E3 => (1 : ENNReal))) :=
    measurable_const.indicator hLmeas
  have hindL2 : Measurable (L2.indicator (fun _ : E3 => (1 : ENNReal))) :=
    measurable_const.indicator hL2meas
  have hPhim : Measurable Phi := by
    rw [hPhi]
    refine Measurable.tsum (L := SummationFilter.unconditional (Fin 3 → ℤ))
      (fun m : Fin 3 → ℤ => ?_)
    exact hgm.comp (by fun_prop : Measurable fun z : E3 => z + ℓ • latVec m)
  -- pointwise: the periodisation against the sum of the norms
  have hpt : ∀ v : E3, ‖latPer3 ℓ U v‖ₑ ≤ (ENNReal.ofReal |ℓ|) ^ 3 * Phi v := by
    intro v
    have h1 : ‖latPer3 ℓ U v‖ₑ
        = ‖((((ℓ ^ 3) : ℝ) : ℂ))‖ₑ * ‖LatFourier.latPer ℓ U v‖ₑ := by
      rw [show latPer3 ℓ U v = (((ℓ ^ 3 : ℝ)) : ℂ) * LatFourier.latPer ℓ U v from rfl,
        enorm_mul]
    have h2 : ‖((((ℓ ^ 3) : ℝ) : ℂ))‖ₑ = (ENNReal.ofReal |ℓ|) ^ 3 := by
      rw [← ofReal_norm, errBdd_norm_ofReal, abs_pow, ENNReal.ofReal_pow (abs_nonneg ℓ)]
    rw [h1, h2, hPhi]
    simp only [hg]
    exact mul_le_mul_of_nonneg_left (enorm_latPer_le ℓ U v) (by positivity)
  -- the substitution `y ↦ w - y`
  have hsubst : ∀ w : E3, ∫⁻ y : E3, L.indicator (fun _ => 1) y * Phi (w - y)
      = ∫⁻ v : E3, L.indicator (fun _ => 1) (w - v) * Phi v := by
    intro w
    have h := lintegral_sub_left_eq_self (μ := (volume : Measure E3))
      (f := fun v : E3 => L.indicator (fun _ => 1) (w - v) * Phi v) w
    rw [← h]
    refine lintegral_congr fun v => ?_
    have hsub : w - (w - v) = v := by abel
    rw [hsub]
  -- the pointwise geometric comparison `w ∈ boxL ℓ`, `w - v ∈ boxL ℓ ⟹ v ∈ boxL (2ℓ)`
  have hpoint : ∀ w v : E3, L.indicator (fun _ => 1) w
        * (L.indicator (fun _ => 1) (w - v) * Phi v)
      ≤ L.indicator (fun _ => 1) w * (L2.indicator (fun _ => 1) v * Phi v) := by
    intro w v
    by_cases hw : w ∈ L
    · rw [Set.indicator_of_mem hw, one_mul, one_mul]
      by_cases hwv : w - v ∈ L
      · have hv2 : v ∈ L2 := by
          rw [hL2, mem_corpusBox_boxL (ℓ := 2 * ℓ) (by linarith)]
          intro i
          have h1' : |w i| ≤ ℓ / 2 := (mem_corpusBox_boxL hℓ w).mp (by rwa [hL] at hw) i
          have h2' : |(w - v) i| ≤ ℓ / 2 :=
            (mem_corpusBox_boxL hℓ (w - v)).mp (by rwa [hL] at hwv) i
          have hbnd : |v i| ≤ ℓ := by
            have h4 : v i = w i - (w - v) i := by simp
            rw [h4]
            rw [abs_sub_le_iff]
            constructor <;> linarith [(abs_le.mp h1').1, (abs_le.mp h1').2,
              (abs_le.mp h2').1, (abs_le.mp h2').2]
          linarith
        rw [Set.indicator_of_mem hwv, Set.indicator_of_mem hv2]
      · rw [Set.indicator_of_notMem hwv, zero_mul]
        exact zero_le
    · rw [Set.indicator_of_notMem hw, zero_mul]
      exact zero_le
  have hmain : ∫⁻ q : E3 × E3,
        L.indicator (fun _ => 1) q.1 * L.indicator (fun _ => 1) q.2 * Phi (q.1 - q.2)
      ≤ MeasureTheory.volume L * ((((2 + 1 : ℕ) : ENNReal) ^ 3) * ∫⁻ z, g z) := by
    have hfmeas : AEMeasurable (fun q : E3 × E3 =>
        L.indicator (fun _ => 1) q.1 * L.indicator (fun _ => 1) q.2 * Phi (q.1 - q.2))
        (volume.prod volume) :=
      (((hindL.comp measurable_fst).mul (hindL.comp measurable_snd)).mul
        (hPhim.comp (by fun_prop : Measurable fun q : E3 × E3 => q.1 - q.2))).aemeasurable
    change ∫⁻ q : E3 × E3, L.indicator (fun _ => 1) q.1 * L.indicator (fun _ => 1) q.2
        * Phi (q.1 - q.2) ∂(volume.prod volume)
      ≤ MeasureTheory.volume L * ((((2 + 1 : ℕ) : ENNReal) ^ 3) * ∫⁻ z, g z)
    rw [lintegral_prod (f := fun q : E3 × E3 =>
      L.indicator (fun _ => 1) q.1 * L.indicator (fun _ => 1) q.2 * Phi (q.1 - q.2)) hfmeas]
    calc ∫⁻ w : E3, ∫⁻ y : E3, L.indicator (fun _ => 1) w * L.indicator (fun _ => 1) y * Phi (w - y)
        = ∫⁻ w : E3, L.indicator (fun _ => 1) w
            * ∫⁻ y : E3, L.indicator (fun _ => 1) y * Phi (w - y) := by
          refine lintegral_congr fun w => ?_
          rw [← lintegral_const_mul'' (L.indicator (fun _ => 1) w)
            (f := fun y : E3 => L.indicator (fun _ => 1) y * Phi (w - y))
            ((hindL.mul (hPhim.comp (by fun_prop : Measurable fun y : E3 => w - y))).aemeasurable)]
          exact lintegral_congr fun y => by rw [mul_assoc]
      _ = ∫⁻ w : E3, L.indicator (fun _ => 1) w
            * ∫⁻ v : E3, L.indicator (fun _ => 1) (w - v) * Phi v := by
          refine lintegral_congr fun w => ?_
          rw [hsubst w]
      _ = ∫⁻ w : E3, ∫⁻ v : E3, L.indicator (fun _ => 1) w
            * (L.indicator (fun _ => 1) (w - v) * Phi v) := by
          refine lintegral_congr fun w => ?_
          rw [lintegral_const_mul'' (L.indicator (fun _ => 1) w)
            (f := fun v : E3 => L.indicator (fun _ => 1) (w - v) * Phi v)
            (((hindL.comp (by fun_prop : Measurable fun v : E3 => w - v)).mul hPhim).aemeasurable)]
      _ ≤ ∫⁻ w : E3, ∫⁻ v : E3, L.indicator (fun _ => 1) w
            * (L2.indicator (fun _ => 1) v * Phi v) :=
          lintegral_mono fun w => lintegral_mono fun v => hpoint w v
      _ = ∫⁻ w : E3, L.indicator (fun _ => 1) w
            * ∫⁻ v : E3, L2.indicator (fun _ => 1) v * Phi v := by
          refine lintegral_congr fun w => ?_
          rw [lintegral_const_mul'' (L.indicator (fun _ => 1) w)
            (f := fun v : E3 => L2.indicator (fun _ => 1) v * Phi v)
            ((hindL2.mul hPhim).aemeasurable)]
      _ = (∫⁻ w : E3, L.indicator (fun _ => 1) w)
            * ∫⁻ v : E3, L2.indicator (fun _ => 1) v * Phi v :=
          lintegral_mul_const _ hindL
      _ = MeasureTheory.volume L * ∫⁻ v : E3, L2.indicator (fun _ => 1) v * Phi v := by
          rw [show (∫⁻ w : E3, L.indicator (fun _ => 1) w) = MeasureTheory.volume L from
            lintegral_indicator_one (μ := (volume : Measure E3)) hLmeas]
      _ ≤ MeasureTheory.volume L * ((((2 + 1 : ℕ) : ENNReal) ^ 3) * ∫⁻ z, g z) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [hL2, hPhi]
          exact lintegral_tsum_translate_boxL_le (l := ℓ) hℓ 2 hgm
  calc ∫⁻ q : E3 × E3, (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => 1) q.1
        * (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => 1) q.2 * ‖latPer3 ℓ U (q.1 - q.2)‖ₑ
      = ∫⁻ q : E3 × E3, L.indicator (fun _ => 1) q.1 * L.indicator (fun _ => 1) q.2
          * ‖latPer3 ℓ U (q.1 - q.2)‖ₑ := by rw [hL]
    _ ≤ ∫⁻ q : E3 × E3, L.indicator (fun _ => 1) q.1 * L.indicator (fun _ => 1) q.2
          * ((ENNReal.ofReal |ℓ|) ^ 3 * Phi (q.1 - q.2)) :=
        lintegral_mono fun q => mul_le_mul_of_nonneg_left (hpt _) (by positivity)
    _ = (ENNReal.ofReal |ℓ|) ^ 3 * ∫⁻ q : E3 × E3, L.indicator (fun _ => 1) q.1
          * L.indicator (fun _ => 1) q.2 * Phi (q.1 - q.2) := by
        rw [← lintegral_const_mul'' ((ENNReal.ofReal |ℓ|) ^ 3)
          (f := fun q : E3 × E3 => L.indicator (fun _ => 1) q.1 * L.indicator (fun _ => 1) q.2
            * Phi (q.1 - q.2))
          ((((hindL.comp measurable_fst).mul (hindL.comp measurable_snd)).mul
            (hPhim.comp (by fun_prop : Measurable fun q : E3 × E3 => q.1 - q.2))).aemeasurable)]
        exact lintegral_congr fun q => by ring
    _ ≤ (ENNReal.ofReal |ℓ|) ^ 3
          * (MeasureTheory.volume L * ((((2 + 1 : ℕ) : ENNReal) ^ 3) * ∫⁻ z, g z)) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = (ENNReal.ofReal |ℓ|) ^ 3
          * (MeasureTheory.volume (Work.BoseK15.corpusBox.boxL ℓ)
              * ((((2 + 1 : ℕ) : ENNReal) ^ 3) * ∫⁻ z, ‖(U z : ℂ)‖ₑ)) := by
        rw [hL, hg]



/-! ## The pair box: `K1lim` is `L¹` over it -/

/-- The limit pair kernel is `L¹` over the two-particle box, for a weight with finite `L¹` mass. -/
theorem K1lim_pair_box_lt_top {ℓ : ℝ} (hℓ : 0 < ℓ) {U : E3 → ℝ} (hUm : Measurable U)
    (hUfin : ∫⁻ z, ‖(U z : ℂ)‖ₑ < ⊤) :
    ∫⁻ q : E3 × E3, (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => 1) q.1
        * (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => 1) q.2 * ‖K1lim ℓ U q.1 q.2‖ₑ < ⊤ := by
  obtain ⟨CB, hCB0, hCB⟩ := errBdd_pinQBl_bdd (ℓ := ℓ) hℓ U
  obtain ⟨CC, hCC0, hCC⟩ := errBdd_pinQCl_bdd (ℓ := ℓ) hℓ U
  obtain ⟨CD, hCD0, hCD⟩ := errBdd_pinQDl_bdd (ℓ := ℓ) hℓ U
  have hchi : ∀ z : E3, ‖(((Submission.BoseGases.chiScale ℓ z : ℝ)) : ℂ)‖
      ≤ (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ := by
    intro z
    have hnn : 0 ≤ Submission.BoseGases.chiScale ℓ z :=
      Submission.BoseGases.chi_nonneg ((ℓ⁻¹) • z)
    rw [errBdd_norm_ofReal, abs_of_nonneg hnn]
    exact Submission.BoseGases.chi_le_sqrt_inv ((ℓ⁻¹) • z)
  have hth : ∀ z : E3, ‖Work.BoseK15.corpusBox.thetaFun ℓ z‖ₑ ≤ 1 := by
    intro z
    rw [Work.BoseB4.BoxData.thetaFun_apply]
    split <;> simp
  set Mχ : ENNReal := ENNReal.ofReal ((Real.sqrt Submission.BoseGases.chiNormSq)⁻¹) with hMχ
  have hMχlt : Mχ < ⊤ := ENNReal.ofReal_lt_top
  have hchie : ∀ z : E3, ‖(((Submission.BoseGases.chiScale ℓ z : ℝ)) : ℂ)‖ₑ ≤ Mχ := by
    intro z
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hchi z)
  set C1 : ENNReal := ‖((((ℓ ^ 3)⁻¹ : ℝ) : ℂ))‖ₑ with hC1
  have hC1lt : C1 < ⊤ := by rw [hC1, ← ofReal_norm]; exact ENNReal.ofReal_lt_top
  set K2 : ENNReal := Mχ * ENNReal.ofReal CB + Mχ * ENNReal.ofReal CC + ENNReal.ofReal CD with hK2
  have hK2lt : K2 < ⊤ := by
    rw [hK2]
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr
      ⟨ENNReal.mul_lt_top hMχlt ENNReal.ofReal_lt_top,
       ENNReal.mul_lt_top hMχlt ENNReal.ofReal_lt_top⟩, ENNReal.ofReal_lt_top⟩
  have hBl : ∀ w : E3, ‖pinQBl ℓ U w‖ₑ ≤ ENNReal.ofReal CB := by
    intro w; rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hCB w)
  have hCl : ∀ y : E3, ‖pinQCl ℓ U y‖ₑ ≤ ENNReal.ofReal CC := by
    intro y; rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hCC y)
  have hDl : ‖pinQDl ℓ U‖ₑ ≤ ENNReal.ofReal CD := by
    rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal hCD
  -- the pointwise bound on the four rows of `K1lim`
  have hpt : ∀ q : E3 × E3,
      ‖K1lim ℓ U q.1 q.2‖ₑ ≤ C1 * (Mχ * Mχ * ‖latPer3 ℓ U (q.1 - q.2)‖ₑ + K2) := by
    intro q
    have hA : ‖(((Submission.BoseGases.chiScale ℓ q.1 : ℝ)) : ℂ)
          * (((Submission.BoseGases.chiScale ℓ q.2 : ℝ)) : ℂ) * latPer3 ℓ U (q.1 - q.2)‖ₑ
        ≤ Mχ * Mχ * ‖latPer3 ℓ U (q.1 - q.2)‖ₑ := by
      rw [enorm_mul, enorm_mul]
      exact mul_le_mul (mul_le_mul (hchie q.1) (hchie q.2) (by positivity) (by positivity))
        le_rfl (by positivity) (by positivity)
    have hB : ‖(((Submission.BoseGases.chiScale ℓ q.1 : ℝ)) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun ℓ q.2 * pinQBl ℓ U q.1‖ₑ
        ≤ Mχ * ENNReal.ofReal CB := by
      rw [enorm_mul, enorm_mul]
      calc ‖(((Submission.BoseGases.chiScale ℓ q.1 : ℝ)) : ℂ)‖ₑ
              * ‖Work.BoseK15.corpusBox.thetaFun ℓ q.2‖ₑ * ‖pinQBl ℓ U q.1‖ₑ
          ≤ Mχ * 1 * ENNReal.ofReal CB :=
            mul_le_mul (mul_le_mul (hchie q.1) (hth q.2) (by positivity) (by positivity))
              (hBl q.1) (by positivity) (by positivity)
        _ = Mχ * ENNReal.ofReal CB := by ring
    have hC : ‖Work.BoseK15.corpusBox.thetaFun ℓ q.1
          * (((Submission.BoseGases.chiScale ℓ q.2 : ℝ)) : ℂ) * pinQCl ℓ U q.2‖ₑ
        ≤ Mχ * ENNReal.ofReal CC := by
      rw [enorm_mul, enorm_mul]
      calc ‖Work.BoseK15.corpusBox.thetaFun ℓ q.1‖ₑ
              * ‖(((Submission.BoseGases.chiScale ℓ q.2 : ℝ)) : ℂ)‖ₑ * ‖pinQCl ℓ U q.2‖ₑ
          ≤ 1 * Mχ * ENNReal.ofReal CC :=
            mul_le_mul (mul_le_mul (hth q.1) (hchie q.2) (by positivity) (by positivity))
              (hCl q.2) (by positivity) (by positivity)
        _ = Mχ * ENNReal.ofReal CC := by ring
    have hD : ‖Work.BoseK15.corpusBox.thetaFun ℓ q.1
          * Work.BoseK15.corpusBox.thetaFun ℓ q.2 * pinQDl ℓ U‖ₑ ≤ ENNReal.ofReal CD := by
      rw [enorm_mul, enorm_mul]
      calc ‖Work.BoseK15.corpusBox.thetaFun ℓ q.1‖ₑ
              * ‖Work.BoseK15.corpusBox.thetaFun ℓ q.2‖ₑ * ‖pinQDl ℓ U‖ₑ
          ≤ 1 * 1 * ENNReal.ofReal CD :=
            mul_le_mul (mul_le_mul (hth q.1) (hth q.2) (by positivity) (by positivity))
              hDl (by positivity) (by positivity)
        _ = ENNReal.ofReal CD := by ring
    have hbr : ‖(((Submission.BoseGases.chiScale ℓ q.1 : ℝ)) : ℂ)
            * (((Submission.BoseGases.chiScale ℓ q.2 : ℝ)) : ℂ) * latPer3 ℓ U (q.1 - q.2)
          - (((Submission.BoseGases.chiScale ℓ q.1 : ℝ)) : ℂ)
            * Work.BoseK15.corpusBox.thetaFun ℓ q.2 * pinQBl ℓ U q.1
          - Work.BoseK15.corpusBox.thetaFun ℓ q.1
            * (((Submission.BoseGases.chiScale ℓ q.2 : ℝ)) : ℂ) * pinQCl ℓ U q.2
          + Work.BoseK15.corpusBox.thetaFun ℓ q.1
            * Work.BoseK15.corpusBox.thetaFun ℓ q.2 * pinQDl ℓ U‖ₑ
        ≤ Mχ * Mχ * ‖latPer3 ℓ U (q.1 - q.2)‖ₑ + K2 := by
      have h1 : ‖(((Submission.BoseGases.chiScale ℓ q.1 : ℝ)) : ℂ)
              * (((Submission.BoseGases.chiScale ℓ q.2 : ℝ)) : ℂ) * latPer3 ℓ U (q.1 - q.2)
            - (((Submission.BoseGases.chiScale ℓ q.1 : ℝ)) : ℂ)
              * Work.BoseK15.corpusBox.thetaFun ℓ q.2 * pinQBl ℓ U q.1
            - Work.BoseK15.corpusBox.thetaFun ℓ q.1
              * (((Submission.BoseGases.chiScale ℓ q.2 : ℝ)) : ℂ) * pinQCl ℓ U q.2
            + Work.BoseK15.corpusBox.thetaFun ℓ q.1
              * Work.BoseK15.corpusBox.thetaFun ℓ q.2 * pinQDl ℓ U‖ₑ
          ≤ ((Mχ * Mχ * ‖latPer3 ℓ U (q.1 - q.2)‖ₑ + Mχ * ENNReal.ofReal CB)
              + Mχ * ENNReal.ofReal CC) + ENNReal.ofReal CD := by
        calc ‖(((Submission.BoseGases.chiScale ℓ q.1 : ℝ)) : ℂ)
                * (((Submission.BoseGases.chiScale ℓ q.2 : ℝ)) : ℂ) * latPer3 ℓ U (q.1 - q.2)
              - (((Submission.BoseGases.chiScale ℓ q.1 : ℝ)) : ℂ)
                * Work.BoseK15.corpusBox.thetaFun ℓ q.2 * pinQBl ℓ U q.1
              - Work.BoseK15.corpusBox.thetaFun ℓ q.1
                * (((Submission.BoseGases.chiScale ℓ q.2 : ℝ)) : ℂ) * pinQCl ℓ U q.2
              + Work.BoseK15.corpusBox.thetaFun ℓ q.1
                * Work.BoseK15.corpusBox.thetaFun ℓ q.2 * pinQDl ℓ U‖ₑ
            ≤ ‖(((Submission.BoseGases.chiScale ℓ q.1 : ℝ)) : ℂ)
                * (((Submission.BoseGases.chiScale ℓ q.2 : ℝ)) : ℂ) * latPer3 ℓ U (q.1 - q.2)
              - (((Submission.BoseGases.chiScale ℓ q.1 : ℝ)) : ℂ)
                * Work.BoseK15.corpusBox.thetaFun ℓ q.2 * pinQBl ℓ U q.1
              - Work.BoseK15.corpusBox.thetaFun ℓ q.1
                * (((Submission.BoseGases.chiScale ℓ q.2 : ℝ)) : ℂ) * pinQCl ℓ U q.2‖ₑ
              + ‖Work.BoseK15.corpusBox.thetaFun ℓ q.1
                * Work.BoseK15.corpusBox.thetaFun ℓ q.2 * pinQDl ℓ U‖ₑ := enorm_add_le _ _
          _ ≤ (‖(((Submission.BoseGases.chiScale ℓ q.1 : ℝ)) : ℂ)
                * (((Submission.BoseGases.chiScale ℓ q.2 : ℝ)) : ℂ) * latPer3 ℓ U (q.1 - q.2)
              - (((Submission.BoseGases.chiScale ℓ q.1 : ℝ)) : ℂ)
                * Work.BoseK15.corpusBox.thetaFun ℓ q.2 * pinQBl ℓ U q.1‖ₑ
              + ‖Work.BoseK15.corpusBox.thetaFun ℓ q.1
                * (((Submission.BoseGases.chiScale ℓ q.2 : ℝ)) : ℂ) * pinQCl ℓ U q.2‖ₑ)
              + ‖Work.BoseK15.corpusBox.thetaFun ℓ q.1
                * Work.BoseK15.corpusBox.thetaFun ℓ q.2 * pinQDl ℓ U‖ₑ :=
                add_le_add enorm_sub_le le_rfl
          _ ≤ ((‖(((Submission.BoseGases.chiScale ℓ q.1 : ℝ)) : ℂ)
                * (((Submission.BoseGases.chiScale ℓ q.2 : ℝ)) : ℂ) * latPer3 ℓ U (q.1 - q.2)‖ₑ
              + ‖(((Submission.BoseGases.chiScale ℓ q.1 : ℝ)) : ℂ)
                * Work.BoseK15.corpusBox.thetaFun ℓ q.2 * pinQBl ℓ U q.1‖ₑ)
              + ‖Work.BoseK15.corpusBox.thetaFun ℓ q.1
                * (((Submission.BoseGases.chiScale ℓ q.2 : ℝ)) : ℂ) * pinQCl ℓ U q.2‖ₑ)
              + ‖Work.BoseK15.corpusBox.thetaFun ℓ q.1
                * Work.BoseK15.corpusBox.thetaFun ℓ q.2 * pinQDl ℓ U‖ₑ :=
                add_le_add (add_le_add enorm_sub_le le_rfl) le_rfl
          _ ≤ ((Mχ * Mχ * ‖latPer3 ℓ U (q.1 - q.2)‖ₑ + Mχ * ENNReal.ofReal CB)
              + Mχ * ENNReal.ofReal CC) + ENNReal.ofReal CD :=
              add_le_add (add_le_add (add_le_add hA hB) hC) hD
      calc _ ≤ _ := h1
        _ = Mχ * Mχ * ‖latPer3 ℓ U (q.1 - q.2)‖ₑ + K2 := by rw [hK2]; ring
    calc ‖K1lim ℓ U q.1 q.2‖ₑ
        = C1 * ‖(((Submission.BoseGases.chiScale ℓ q.1 : ℝ)) : ℂ)
            * (((Submission.BoseGases.chiScale ℓ q.2 : ℝ)) : ℂ) * latPer3 ℓ U (q.1 - q.2)
          - (((Submission.BoseGases.chiScale ℓ q.1 : ℝ)) : ℂ)
            * Work.BoseK15.corpusBox.thetaFun ℓ q.2 * pinQBl ℓ U q.1
          - Work.BoseK15.corpusBox.thetaFun ℓ q.1
            * (((Submission.BoseGases.chiScale ℓ q.2 : ℝ)) : ℂ) * pinQCl ℓ U q.2
          + Work.BoseK15.corpusBox.thetaFun ℓ q.1
            * Work.BoseK15.corpusBox.thetaFun ℓ q.2 * pinQDl ℓ U‖ₑ := by
          rw [show K1lim ℓ U q.1 q.2 = (((ℓ ^ 3)⁻¹ : ℝ) : ℂ) *
            ((((Submission.BoseGases.chiScale ℓ q.1 : ℝ)) : ℂ)
                * (((Submission.BoseGases.chiScale ℓ q.2 : ℝ)) : ℂ) * latPer3 ℓ U (q.1 - q.2)
              - (((Submission.BoseGases.chiScale ℓ q.1 : ℝ)) : ℂ)
                * Work.BoseK15.corpusBox.thetaFun ℓ q.2 * pinQBl ℓ U q.1
              - Work.BoseK15.corpusBox.thetaFun ℓ q.1
                * (((Submission.BoseGases.chiScale ℓ q.2 : ℝ)) : ℂ) * pinQCl ℓ U q.2
              + Work.BoseK15.corpusBox.thetaFun ℓ q.1
                * Work.BoseK15.corpusBox.thetaFun ℓ q.2 * pinQDl ℓ U) from rfl, enorm_mul, hC1]
      _ ≤ C1 * (Mχ * Mχ * ‖latPer3 ℓ U (q.1 - q.2)‖ₑ + K2) :=
          mul_le_mul_of_nonneg_left hbr (by positivity)
  set J : E3 × E3 → ENNReal := fun q =>
    (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => 1) q.1
      * (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => 1) q.2 with hJ
  set Cst : ENNReal := max (C1 * Mχ * Mχ) (C1 * K2) with hCst
  have hCstlt : Cst < ⊤ := by
    rw [hCst]
    exact max_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top hC1lt hMχlt) hMχlt)
      (ENNReal.mul_lt_top hC1lt hK2lt)
  have hLm : Measurable (fun q : E3 × E3 => ‖latPer3 ℓ U (q.1 - q.2)‖ₑ) := by
    have h1 : Measurable (fun q : E3 × E3 => ENNReal.ofReal ‖latPer3 ℓ U (q.1 - q.2)‖) :=
      ENNReal.measurable_ofReal.comp (((measurable_latPer3 hUm).norm).comp (by fun_prop))
    rwa [show (fun q : E3 × E3 => ENNReal.ofReal ‖latPer3 ℓ U (q.1 - q.2)‖)
        = (fun q : E3 × E3 => ‖latPer3 ℓ U (q.1 - q.2)‖ₑ) from
      funext fun q => ofReal_norm _] at h1
  have hJm : Measurable J := by
    rw [hJ]
    exact (measurable_const.indicator (by
        rw [show Work.BoseK15.corpusBox.boxL ℓ = Work.BoseB4.BoxData.boxL Work.BoseK15.corpusBox ℓ
          from rfl]
        exact Work.BoseB4.BoxData.boxL_measurableSet _ ℓ)).comp measurable_fst
      |>.mul ((measurable_const.indicator (by
        rw [show Work.BoseK15.corpusBox.boxL ℓ = Work.BoseB4.BoxData.boxL Work.BoseK15.corpusBox ℓ
          from rfl]
        exact Work.BoseB4.BoxData.boxL_measurableSet _ ℓ)).comp measurable_snd)
  have hAfin : ∫⁻ q : E3 × E3, (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => 1) q.1
      * (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => 1) q.2
      * ‖latPer3 ℓ U (q.1 - q.2)‖ₑ < ⊤ := by
    have hF := lintegral_latPer3_pair_le (ℓ := ℓ) hℓ hUm
    have hvol : MeasureTheory.volume (Work.BoseK15.corpusBox.boxL ℓ) < ⊤ :=
      (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ).measure_lt_top
    have hpow : (ENNReal.ofReal |ℓ|) ^ 3 < ⊤ := by
      rw [← ENNReal.ofReal_pow (abs_nonneg ℓ)]
      exact ENNReal.ofReal_lt_top
    exact lt_of_le_of_lt hF (ENNReal.mul_lt_top hpow
      (ENNReal.mul_lt_top hvol (ENNReal.mul_lt_top (by norm_num) hUfin)))
  have hJfin : ∫⁻ q : E3 × E3, J q < ⊤ := by
    rw [hJ]
    have hvol : MeasureTheory.volume (Work.BoseK15.corpusBox.boxL ℓ) < ⊤ :=
      (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ).measure_lt_top
    have hmeasL : MeasurableSet (Work.BoseK15.corpusBox.boxL ℓ) :=
      Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ
    have hindL : Measurable ((Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ : E3 => (1 : ENNReal))) :=
      measurable_const.indicator hmeasL
    have hm : AEMeasurable (fun q : E3 × E3 =>
        (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ : E3 => (1 : ENNReal)) q.1
          * (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ : E3 => (1 : ENNReal)) q.2)
        (volume.prod volume) :=
      Measurable.aemeasurable (μ := (volume.prod volume))
        ((hindL.comp measurable_fst).mul (hindL.comp measurable_snd))
    change (∫⁻ q : E3 × E3, (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ : E3 => (1 : ENNReal)) q.1
        * (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ : E3 => (1 : ENNReal)) q.2
        ∂(volume.prod volume)) < ⊤
    rw [lintegral_prod (μ := (volume : Measure E3)) (ν := (volume : Measure E3))
      (f := fun q : E3 × E3 => (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ : E3 => (1 : ENNReal)) q.1
        * (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ : E3 => (1 : ENNReal)) q.2) hm]
    have hstep : (∫⁻ w : E3, ∫⁻ y : E3,
        (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ : E3 => (1 : ENNReal)) w
          * (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ : E3 => (1 : ENNReal)) y)
        = MeasureTheory.volume (Work.BoseK15.corpusBox.boxL ℓ)
          * MeasureTheory.volume (Work.BoseK15.corpusBox.boxL ℓ) := by
      calc ∫⁻ w : E3, ∫⁻ y : E3, (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ : E3 => (1 : ENNReal)) w
              * (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ : E3 => (1 : ENNReal)) y
          = ∫⁻ w : E3, (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ : E3 => (1 : ENNReal)) w
              * ∫⁻ y : E3, (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ : E3 => (1 : ENNReal)) y := by
            refine lintegral_congr fun w => ?_
            rw [lintegral_const_mul'' (μ := (volume : Measure E3))
              (f := fun y : E3 => (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ : E3 => (1 : ENNReal)) y)
              ((Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ : E3 => (1 : ENNReal)) w) hindL.aemeasurable]
        _ = ∫⁻ w : E3, (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ : E3 => (1 : ENNReal)) w
              * MeasureTheory.volume (Work.BoseK15.corpusBox.boxL ℓ) := by
            refine lintegral_congr fun w => ?_
            rw [show (∫⁻ y : E3, (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ : E3 => (1 : ENNReal)) y)
                = MeasureTheory.volume (Work.BoseK15.corpusBox.boxL ℓ) from
              lintegral_indicator_one (μ := (volume : Measure E3)) hmeasL]
        _ = (∫⁻ w : E3, (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ : E3 => (1 : ENNReal)) w)
              * MeasureTheory.volume (Work.BoseK15.corpusBox.boxL ℓ) :=
            lintegral_mul_const (μ := (volume : Measure E3)) _ hindL
        _ = MeasureTheory.volume (Work.BoseK15.corpusBox.boxL ℓ)
              * MeasureTheory.volume (Work.BoseK15.corpusBox.boxL ℓ) := by
            rw [show (∫⁻ w : E3, (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ : E3 => (1 : ENNReal)) w)
                = MeasureTheory.volume (Work.BoseK15.corpusBox.boxL ℓ) from
              lintegral_indicator_one (μ := (volume : Measure E3)) hmeasL]
    rw [hstep]
    exact ENNReal.mul_lt_top hvol hvol
  have hpt2 : ∀ q : E3 × E3, J q * ‖K1lim ℓ U q.1 q.2‖ₑ
      ≤ Cst * (J q * ‖latPer3 ℓ U (q.1 - q.2)‖ₑ + J q) := by
    intro q
    calc J q * ‖K1lim ℓ U q.1 q.2‖ₑ
        ≤ J q * (C1 * (Mχ * Mχ * ‖latPer3 ℓ U (q.1 - q.2)‖ₑ + K2)) :=
          mul_le_mul_of_nonneg_left (hpt q) (by positivity)
      _ = (C1 * Mχ * Mχ) * (J q * ‖latPer3 ℓ U (q.1 - q.2)‖ₑ) + (C1 * K2) * J q := by ring
      _ ≤ Cst * (J q * ‖latPer3 ℓ U (q.1 - q.2)‖ₑ) + Cst * J q :=
          add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
            (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
      _ = Cst * (J q * ‖latPer3 ℓ U (q.1 - q.2)‖ₑ + J q) := by ring
  have hfin : ∫⁻ q : E3 × E3, Cst * (J q * ‖latPer3 ℓ U (q.1 - q.2)‖ₑ + J q) < ⊤ := by
    rw [lintegral_const_mul'' (f := fun q : E3 × E3 =>
        J q * ‖latPer3 ℓ U (q.1 - q.2)‖ₑ + J q) Cst (((hJm.mul hLm).add hJm).aemeasurable)]
    refine ENNReal.mul_lt_top hCstlt ?_
    rw [lintegral_add_left (f := fun q : E3 × E3 =>
      J q * ‖latPer3 ℓ U (q.1 - q.2)‖ₑ) (hJm.mul hLm)]
    exact ENNReal.add_lt_top.mpr ⟨by
      rw [hJ]
      exact hAfin, by rw [hJ]; exact hJfin⟩
  exact lt_of_le_of_lt (lintegral_mono hpt2) hfin

/-! ## The target -/

/-- A.e. strong measurability of a two-slot kernel transported to the `n`-particle space.
Stated with the kernel as a *variable* so that nothing is unfolded at the use site. -/
theorem aesm_comp_eval_gen {d : ℕ} (p : Fin (d + 1)) {φ : E3 → E3 → ℂ}
    (hφ : AEStronglyMeasurable (fun q : E3 × E3 => φ q.1 q.2) (volume.prod volume)) :
    AEStronglyMeasurable (fun z : Work.BoseDict.Xn (d + 1) × E3 => φ (z.1 p) z.2)
      (volume : Measure (Work.BoseDict.Xn (d + 1) × E3)) :=
  hφ.comp_quasiMeasurePreserving (quasiMeasurePreserving_eval_pair (d := d) p)

/-- A.e. congruence of a two-slot kernel transported to the `n`-particle space. -/
theorem ae_eq_comp_eval_gen {d : ℕ} (p : Fin (d + 1)) {φ φ' : E3 → E3 → ℂ}
    (h : (fun q : E3 × E3 => φ q.1 q.2) =ᵐ[volume.prod volume] (fun q => φ' q.1 q.2)) :
    (fun z : Work.BoseDict.Xn (d + 1) × E3 => φ (z.1 p) z.2)
      =ᵐ[volume] (fun z : Work.BoseDict.Xn (d + 1) × E3 => φ' (z.1 p) z.2) :=
  (quasiMeasurePreserving_eval_pair (d := d) p).ae_eq h

theorem K1lim_mul_integrable_slot {n : ℕ} {l : ℝ} (hl : 0 < l) (p : Fin n × Fin n)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hWi : MeasureTheory.Integrable W)
    {H : Work.BoseDict.Xn n × EuclideanSpace ℝ (Fin 3) → ℂ}
    (hHm : MeasureTheory.AEStronglyMeasurable H MeasureTheory.volume)
    (hHb : ∃ C : ℝ, ∀ z, ‖H z‖ ≤ C)
    (hHs : Function.support H ⊆ Set.prod (Work.MB.boxPow n l)
      (Work.BoseK15.corpusBox.boxL l)) :
    MeasureTheory.Integrable (fun z : Work.BoseDict.Xn n × EuclideanSpace ℝ (Fin 3) =>
      Work.BoseBoxFock.K1lim l W (z.1 p.2) z.2 * H z)
      (MeasureTheory.volume : MeasureTheory.Measure
        (Work.BoseDict.Xn n × EuclideanSpace ℝ (Fin 3))) := by
  rcases n with _ | d
  · exact Fin.elim0 p.1
  obtain ⟨U, hUm, hWU⟩ : ∃ U : E3 → ℝ, Measurable U ∧ W =ᵐ[volume] U :=
    ⟨AEStronglyMeasurable.mk W hWi.aestronglyMeasurable,
      (hWi.aestronglyMeasurable.stronglyMeasurable_mk).measurable,
      hWi.aestronglyMeasurable.ae_eq_mk⟩
  have hUfin : ∫⁻ z : E3, ‖(U z : ℂ)‖ₑ < ⊤ := by
    have h1 : ∫⁻ z : E3, ‖(U z : ℂ)‖ₑ = ∫⁻ z : E3, ‖(W z : ℂ)‖ₑ :=
      lintegral_congr_ae (hWU.mono fun z hz => by
        show ‖(U z : ℂ)‖ₑ = ‖(W z : ℂ)‖ₑ
        rw [hz])
    have h2 : ∫⁻ z : E3, ‖(W z : ℂ)‖ₑ = ∫⁻ z : E3, ‖(W z : ℝ)‖ₑ := by
      refine lintegral_congr fun z => ?_
      rw [← ofReal_norm, ← ofReal_norm]
      congr 1
      rw [errBdd_norm_ofReal, Real.norm_eq_abs]
    rw [h1, h2]
    exact hWi.hasFiniteIntegral
  have hqmp : Measure.QuasiMeasurePreserving
      (fun z : Work.BoseDict.Xn (d + 1) × E3 => (z.1 p.2, z.2))
      (volume : Measure (Work.BoseDict.Xn (d + 1) × E3)) (volume.prod volume) :=
    quasiMeasurePreserving_eval_pair (d := d) (p := p.2)
  have hae : (fun z : Work.BoseDict.Xn (d + 1) × E3 => K1lim l U (z.1 p.2) z.2)
      =ᵐ[volume] (fun z : Work.BoseDict.Xn (d + 1) × E3 => K1lim l W (z.1 p.2) z.2) :=
    ae_eq_comp_eval_gen (d := d) p.2 (φ := fun w y => K1lim l U w y) (φ' := fun w y => K1lim l W w y)
      (K1lim_ae_congr' (ℓ := l) hWU).symm
  have hpair : AEStronglyMeasurable (Function.uncurry (K1lim l U)) (volume.prod volume) :=
    (measurable_uncurry_K1lim (ℓ := l) hUm).aestronglyMeasurable
  constructor
  · have hcomp : AEStronglyMeasurable (fun z : Work.BoseDict.Xn (d + 1) × E3 =>
        K1lim l U (z.1 p.2) z.2) (volume : Measure (Work.BoseDict.Xn (d + 1) × E3)) :=
      aesm_comp_eval_gen (d := d) p.2 (φ := fun w y => K1lim l U w y)
        (measurable_uncurry_K1lim (ℓ := l) hUm).aestronglyMeasurable
    exact (hcomp.congr hae).mul hHm
  · obtain ⟨C, hC⟩ := hHb
    set C' : ENNReal := ENNReal.ofReal (max C 0) with hC'
    have hC'fin : C' < ⊤ := ENNReal.ofReal_lt_top
    have hHbd : ∀ z : Work.BoseDict.Xn (d + 1) × E3,
        ‖H z‖ₑ ≤ C' * ((Work.MB.boxPow (d + 1) l).indicator (fun _ => 1) z.1
          * (Work.BoseK15.corpusBox.boxL l).indicator (fun _ => 1) z.2) := by
      intro z
      by_cases hz : z ∈ Set.prod (Work.MB.boxPow (d + 1) l) (Work.BoseK15.corpusBox.boxL l)
      · have hzm := Set.mem_prod.mp hz
        rw [Set.indicator_of_mem hzm.1, Set.indicator_of_mem hzm.2, mul_one, mul_one]
        rw [hC', ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (le_trans (hC z) (le_max_left C 0))
      · have hz0 : H z = 0 := by
          by_contra hne
          exact hz (hHs (Function.mem_support.mpr hne))
        rw [hz0]
        simp
    have hpt : ∀ z : Work.BoseDict.Xn (d + 1) × E3,
        ‖K1lim l W (z.1 p.2) z.2 * H z‖ₑ
          ≤ C' * ((Work.MB.boxPow (d + 1) l).indicator (fun _ => 1) z.1
            * (Work.BoseK15.corpusBox.boxL l).indicator (fun _ => 1) z.2
            * ‖K1lim l W (z.1 p.2) z.2‖ₑ) := by
      intro z
      rw [enorm_mul]
      calc ‖K1lim l W (z.1 p.2) z.2‖ₑ * ‖H z‖ₑ
          ≤ ‖K1lim l W (z.1 p.2) z.2‖ₑ
            * (C' * ((Work.MB.boxPow (d + 1) l).indicator (fun _ => 1) z.1
              * (Work.BoseK15.corpusBox.boxL l).indicator (fun _ => 1) z.2)) :=
            mul_le_mul_of_nonneg_left (hHbd z) (by positivity)
        _ = C' * ((Work.MB.boxPow (d + 1) l).indicator (fun _ => 1) z.1
              * (Work.BoseK15.corpusBox.boxL l).indicator (fun _ => 1) z.2
              * ‖K1lim l W (z.1 p.2) z.2‖ₑ) := by ring
    have hm : Measurable (Function.uncurry (fun w y : E3 => ENNReal.ofReal ‖K1lim l U w y‖)) :=
      ENNReal.measurable_ofReal.comp
        (continuous_norm.measurable.comp (measurable_uncurry_K1lim (ℓ := l) hUm))
    refine lt_of_le_of_lt (lintegral_mono hpt) ?_
    rw [lintegral_const_mul' C' (fun z : Work.BoseDict.Xn (d + 1) × E3 =>
        (Work.MB.boxPow (d + 1) l).indicator (fun _ => 1) z.1
          * (Work.BoseK15.corpusBox.boxL l).indicator (fun _ => 1) z.2
          * ‖K1lim l W (z.1 p.2) z.2‖ₑ) (ne_of_lt hC'fin)]
    refine ENNReal.mul_lt_top hC'fin ?_
    have htr : (∫⁻ z : Work.BoseDict.Xn (d + 1) × E3,
          (Work.MB.boxPow (d + 1) l).indicator (fun _ => 1) z.1
            * (Work.BoseK15.corpusBox.boxL l).indicator (fun _ => 1) z.2
            * ‖K1lim l W (z.1 p.2) z.2‖ₑ)
        = ∫⁻ z : Work.BoseDict.Xn (d + 1) × E3,
          (Work.MB.boxPow (d + 1) l).indicator (fun _ => 1) z.1
            * (Work.BoseK15.corpusBox.boxL l).indicator (fun _ => 1) z.2
            * ENNReal.ofReal ‖K1lim l U (z.1 p.2) z.2‖ := by
      refine lintegral_congr_ae (hae.mono fun z hz => ?_)
      simp only [] at hz
      show (Work.MB.boxPow (d + 1) l).indicator (fun _ => 1) z.1
            * (Work.BoseK15.corpusBox.boxL l).indicator (fun _ => 1) z.2
            * ‖K1lim l W (z.1 p.2) z.2‖ₑ
        = (Work.MB.boxPow (d + 1) l).indicator (fun _ => 1) z.1
            * (Work.BoseK15.corpusBox.boxL l).indicator (fun _ => 1) z.2
            * ENNReal.ofReal ‖K1lim l U (z.1 p.2) z.2‖
      rw [← hz, ← ofReal_norm]
    rw [htr]
    rw [lintegral_boxPow_eval_snd (d := d) (p := p.2) (l := l)
      (F := fun w y : E3 => ENNReal.ofReal ‖K1lim l U w y‖) hm]
    refine ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr (Work.MB.volume_boxPow_lt_top d l)) ?_
    have hconv : (∫⁻ q : E3 × E3, (Work.BoseK15.corpusBox.boxL l).indicator (fun _ => 1) q.1
          * (Work.BoseK15.corpusBox.boxL l).indicator (fun _ => 1) q.2
          * ENNReal.ofReal ‖K1lim l U q.1 q.2‖)
        = ∫⁻ q : E3 × E3, (Work.BoseK15.corpusBox.boxL l).indicator (fun _ => 1) q.1
          * (Work.BoseK15.corpusBox.boxL l).indicator (fun _ => 1) q.2
          * ‖K1lim l U q.1 q.2‖ₑ := by
      refine lintegral_congr fun q => ?_
      rw [ofReal_norm]
    rw [hconv]
    exact K1lim_pair_box_lt_top (ℓ := l) hl hUm hUfin


end Work.BoseBoxFock
