import ChallengeDeps
import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.CubeGap
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Layer 5, brick B5 — the sector projections Pᵢ, Qᵢ and the condensate gap

The Fournais--Solovej box analysis splits the potential energy by writing
`1 = P + Q` where `P` is the projection onto the condensate.  In the box of
side `L` the condensate is the *constant* function (FS `def:projections`
with `θ_u = 1_{Λ(u)}`), so `P` is the mean over the box and `Q` removes the
mean.  On the `N`-particle space (`X N := Fin N → ℝ³`, box `box N L`), with
`cube L := {y : ℝ³ | ∀k, y k ∈ Icc 0 L}` (volume `L³`), this module defines

    (PᵢΦ)(x) := (1/L³)·∫_{y ∈ cube L} Φ (x with xᵢ := y)     (mean over particle i)
    Qᵢ := 1 − Pᵢ

and proves the elementary projection algebra that any version of the sector
calculation needs (all integrals over `box N L` with the product volume):

  * `sectP_idem` — `Pᵢ(PᵢΦ) = PᵢΦ`;
  * `sectP_sym`  — self-adjointness `⟨Φ, PᵢΨ⟩ = ⟨PᵢΦ, Ψ⟩`;
  * `sectQ_ortho` — `⟨PᵢΦ, QᵢΦ⟩ = 0`;
  * `sectP_integral_eq` — `∫ PᵢΦ = ∫ Φ` (total mass is preserved);
  * `sectP_sq_le` — `‖PᵢΦ‖² ≤ ‖Φ‖²` (contractivity; via Jensen);
  * `cube_gap` — the Neumann gap above constants in the cube: for a smooth
    `φ : ℝ³ → ℝ` with mean `m := (1/L³)∫_{cube L} φ`,
    `∫_{cube L} (φ − m)² ≤ 36·L²·∫_{cube L} Σ_k (∂_k φ)²` (iterate the 1D
    `NeumannPoincare.mean_zero_poincare_interval` along the three axes with
    successive averaging `A₁φ, A₂A₁φ, A₃A₂A₁φ` and Jensen, triangle
    inequality; the explicit constant may be replaced by any fixed one);
  * `sectQ_gap` — the N-particle version:
    `∫_{box N L} (QᵢΦ)² ≤ 36·L²·∫_{box N L} Σ_k (∂_{ik}Φ)²`, where the
    right side is the kinetic energy of particle `i` in the corpus sense
    (`fderiv` along `kcDir N i k`, cf. `Neumann.kinNeu`).

This is the exact ingredient behind FS's statement that "constant functions
have zero kinetic energy and there is a gap above the zero energy" — it gives
`⟨Φ, QᵢΦ⟩`-type control from the kinetic energy, the starting point of the
a priori bounds on the number of excited particles `n₊ = ΣQᵢ`.

## Proof-route notes for the child

* `sectP` is the composition of the one-particle mean operator with the
  coordinate-restriction; all the integral identities are Fubini splittings
  of `box N L` into the cube of particle `i` and the box of the other
  `N−1` particles — the corpus already contains the coordinate-split
  machinery (`Potential` measure-preserving cube decompositions,
  `KineticChild.kcInsN`, `PSDefs.integral_box1`, translations `y ↦ xᵢ−y`,
  ...).  Smoothness `ContDiff ℝ ∞ Φ` guarantees all integrands are
  continuous on the compact box, hence integrable; state hypotheses `hΦc`,
  `hΨc` and supply them at use sites.
* `cube_gap` uses `mean_zero_poincare_interval` (1D, `ContDiff ℝ 1`) with
  the interval `0..L` written in interval-integral form, plus Jensen
  `(mean g)² ≤ mean (g²)` for the averaged derivatives; the final constant
  `36` is arbitrary (any fixed constant works).
-/

noncomputable section

open MeasureTheory
open scoped ContDiff Topology Real

namespace Submission.BoseGases

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The projection onto functions constant in coordinate `i` (the condensate
mean over the box): `(PᵢΦ)(x) := (1/L³)·∫_{cube L} Φ (x with xᵢ := y) dy`. -/
noncomputable def sectP (L : ℝ) {N : ℕ} (i : Fin N) (Φ : X N → ℝ) (x : X N) : ℝ :=
  (1 / L ^ 3) * ∫ y in cube L, Φ (Function.update x i y)

/-- The complement projection `Qᵢ := 1 − Pᵢ` (removes the mean in
coordinate `i`). -/
noncomputable def sectQ (L : ℝ) {N : ℕ} (i : Fin N) (Φ : X N → ℝ) (x : X N) : ℝ :=
  Φ x - sectP L i Φ x

/-! ## Cube/function-space transport facts (for the cube measure on E3) -/

def cgCI (L : ℝ) : Set ℝ := Set.Icc (0 : ℝ) L

def cgCubeF (d : ℕ) (L : ℝ) : Set (Fin d → ℝ) := {x | ∀ k, x k ∈ cgCI L}

abbrev cgFd (d : ℕ) := Fin d → ℝ

lemma cgCubeF_eq_pi (d : ℕ) (L : ℝ) : cgCubeF d L = Set.univ.pi (fun _ : Fin d => cgCI L) := by
  ext x
  rw [Set.mem_pi]
  simp [cgCubeF, cgCI]

lemma cgCubeF_measurable (d : ℕ) (L : ℝ) : MeasurableSet (cgCubeF d L) := by
  rw [cgCubeF_eq_pi]
  exact MeasurableSet.pi (s := (Set.univ : Set (Fin d))) (t := fun _ : Fin d => cgCI L)
    Set.countable_univ (by intro i hi; exact measurableSet_Icc)

lemma cgRestrictCubeF_eq_pi (d : ℕ) (L : ℝ) :
    (volume : Measure (Fin d → ℝ)).restrict (cgCubeF d L) =
      Measure.pi (fun _ : Fin d => (volume : Measure ℝ).restrict (cgCI L)) := by
  rw [cgCubeF_eq_pi]
  change (Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict
      (Set.univ.pi (fun _ : Fin d => cgCI L)) = Measure.pi (fun _ : Fin d => (volume : Measure ℝ).restrict (cgCI L))
  rw [Measure.restrict_pi_pi]

lemma cgVolumeCubeF (d : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    (volume : Measure (Fin d → ℝ)) (cgCubeF d L) = ENNReal.ofReal (L ^ d) := by
  rw [← Measure.restrict_apply_univ, cgRestrictCubeF_eq_pi, Measure.pi_univ]
  simp [cgCI, Real.volume_Icc, ENNReal.ofReal_pow hL, Finset.prod_const, Fintype.card_fin]

noncomputable def cgEuc3 : cgFd 3 ≃ᵐ EuclideanSpace ℝ (Fin 3) := MeasurableEquiv.toLp 2 (cgFd 3)

lemma cgEuc3_mp : MeasurePreserving (⇑cgEuc3) (volume : Measure (cgFd 3))
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) := by
  dsimp [cgEuc3]
  simpa [MeasurableEquiv.coe_toLp] using (PiLp.volume_preserving_toLp (Fin 3))

lemma cgCube_eq_image (L : ℝ) : cube L = cgEuc3 '' cgCubeF 3 L := by
  ext y
  constructor
  · intro hy
    refine ⟨cgEuc3.symm y, ?_, ?_⟩
    · intro k
      have hyk : y k ∈ cgCI L := hy k
      simpa [cgEuc3, cgCubeF, cgCI] using hyk
    · simp [cgEuc3]
  · rintro ⟨x, hx, rfl⟩
    intro k
    simpa [cgEuc3, cgCubeF, cgCI] using hx k

lemma cgRestrictCube_eq_map (L : ℝ) :
    (volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (cube L) =
      Measure.map (⇑cgEuc3) ((volume : Measure (cgFd 3)).restrict (cgCubeF 3 L)) := by
  have hmap := cgEuc3_mp.map_eq
  rw [← hmap, cgCube_eq_image]
  have hs : MeasurableSet (cgEuc3 '' cgCubeF 3 L) := (cgEuc3.measurableSet_image).2 (cgCubeF_measurable 3 L)
  rw [Measure.restrict_map (by measurability : Measurable (⇑cgEuc3)) hs]
  rw [Set.preimage_image_eq _ (MeasurableEquiv.injective cgEuc3)]

/-- cube volume in E3 as ENNReal -/
lemma volume_cube {L : ℝ} (hL : 0 ≤ L) :
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) (cube L) = ENNReal.ofReal (L ^ 3) := by
  have hcube : MeasurableSet (cube L) := cube_measurable L
  rw [← (cgEuc3_mp.map_eq)]
  rw [Measure.map_apply (by measurability : Measurable (⇑cgEuc3)) hcube]
  rw [cgCube_eq_image, Set.preimage_image_eq _ (MeasurableEquiv.injective cgEuc3)]
  exact cgVolumeCubeF 3 L hL

/-! ## Box integral toolbox (particle peel) -/

lemma integrableOn_box_of_continuousOn {N : ℕ} {L : ℝ} (hL : 0 < L) {F : X N → ℝ}
    (hF : ContinuousOn F (box N L)) : IntegrableOn F (box N L) volume := by
  exact ContinuousOn.integrableOn_compact (box_compact hL) hF

lemma integrableOn_box_of_continuous {N : ℕ} {L : ℝ} (hL : 0 < L) {F : X N → ℝ}
    (hF : Continuous F) : IntegrableOn F (box N L) volume := by
  exact integrableOn_box_of_continuousOn hL hF.continuousOn

lemma integrableOn_cube_of_continuousOn {L : ℝ} (hL : 0 < L) {F : ℝ³ → ℝ}
    (hF : ContinuousOn F (cube L)) : IntegrableOn F (cube L) volume := by
  exact ContinuousOn.integrableOn_compact (cube_compact hL) hF

lemma integrableOn_cube_of_continuous {L : ℝ} (hL : 0 < L) {F : ℝ³ → ℝ}
    (hF : Continuous F) : IntegrableOn F (cube L) volume := by
  exact integrableOn_cube_of_continuousOn hL hF.continuousOn

/-- real measure of the cube -/
lemma real_volume_cube {L : ℝ} (hL : 0 ≤ L) :
    ((volume : Measure ℝ³).restrict (cube L)).real Set.univ = L ^ 3 := by
  rw [MeasureTheory.measureReal_def]
  rw [Measure.restrict_apply_univ, volume_cube hL]
  simp [hL]

/-- integral of a constant over the cube -/
lemma integral_const_cube {L : ℝ} (hL : 0 < L) (c : ℝ) :
    (∫ y : ℝ³ in cube L, c) = c * L ^ 3 := by
  have h1 : (∫ y : ℝ³ in cube L, c) = (((volume : Measure ℝ³).restrict (cube L)).real Set.univ) • c := by
    simpa using (MeasureTheory.integral_const (μ := (volume : Measure ℝ³).restrict (cube L)) (c := c))
  rw [h1, real_volume_cube hL.le]
  ring

/-- The peel of the box restricted measure isolating particle `i`. -/
lemma box_peel_mp (n : ℕ) (L : ℝ) (i : Fin (n + 1)) :
    MeasurePreserving (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ³) i))
      ((volume : Measure (X (n + 1))).restrict (box (n + 1) L))
      (((volume : Measure ℝ³).restrict (cube L)).prod
        ((volume : Measure (X n)).restrict (box n L))) := by
  have h1 := measurePreserving_coordSplitFin (n := n) L i
  simpa [restrict_box_eq_pi] using h1

/-- Real integral peel of the box: `∫_{x ∈ box} F = ∫_r (∫_y F (insert i y r))`. -/
lemma box_integral_peel {n : ℕ} {L : ℝ} (i : Fin (n + 1)) (F : X (n + 1) → ℝ)
    (hF : IntegrableOn F (box (n + 1) L) volume) :
    (∫ x in box (n + 1) L, F x) =
      ∫ r : X n, (∫ y : ℝ³ in cube L, F (kcInsN n i (y, r)))
        ∂((volume : Measure (X n)).restrict (box n L)) := by
  let μ' : Measure ℝ³ := (volume : Measure ℝ³).restrict (cube L)
  let ν : Measure (X n) := (volume : Measure (X n)).restrict (box n L)
  have hmp2 : MeasurePreserving (⇑(kcInsN n i)) (μ'.prod ν)
      ((volume : Measure (X (n + 1))).restrict (box (n + 1) L)) := by
    have h := MeasurePreserving.symm (e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ³) i))
      (box_peel_mp (n := n) L i)
    simpa [kcInsN, μ', ν] using h
  have hpeel : Integrable (fun p : (ℝ³ × X n) => F (kcInsN n i p)) (μ'.prod ν) := by
    change Integrable (fun p : kcE3 × X n => F (kcInsN n i p)) (μ'.prod ν)
    exact (hmp2.integrable_comp (hg := hF.aestronglyMeasurable)).mpr hF
  calc
    (∫ x in box (n + 1) L, F x) = ∫ x : X (n + 1), F x ∂((volume : Measure (X (n+1))).restrict (box (n + 1) L)) := by rfl
    _ = ∫ p : ℝ³ × X n, F (kcInsN n i p) ∂(μ'.prod ν) := by
      simpa [μ', ν] using (hmp2.integral_comp' F).symm
    _ = ∫ r : X n, (∫ y : ℝ³, F (kcInsN n i (y, r)) ∂μ') ∂ν := by
      exact MeasureTheory.integral_prod_symm (f := fun p : ℝ³ × X n => F (kcInsN n i p)) hpeel
    _ = ∫ r : X n, (∫ y : ℝ³ in cube L, F (kcInsN n i (y, r))) ∂ν := by rfl


/-- updating coordinate `i` to a cube point keeps a box point in the box -/
lemma update_mem_box {N : ℕ} {L : ℝ} {x : X N} (i : Fin N) {z : ℝ³}
    (hx : x ∈ box N L) (hz : z ∈ cube L) : Function.update x i z ∈ box N L := by
  intro j k
  by_cases hj : j = i
  · subst j
    simp [hz k]
  · have hxjk : (x j) k ∈ Set.Icc 0 L := hx j k
    simpa [hj] using hxjk

/-- `|PᵢΦ x|` is bounded by a bound of `|Φ|` on the box -/
lemma sectP_abs_le {N : ℕ} {L : ℝ} (hL : 0 < L) (i : Fin N) {Φ : X N → ℝ}
    (hΦc : Continuous Φ) {B : ℝ} (hB : 0 ≤ B) (hΦB : ∀ x ∈ box N L, |Φ x| ≤ B) :
    ∀ x ∈ box N L, |sectP L i Φ x| ≤ B := by
  intro x hx
  let μ' : Measure ℝ³ := (volume : Measure ℝ³).restrict (cube L)
  have hInt1 : Integrable (fun y : ℝ³ => |Φ (Function.update x i y)|) μ' := by
    exact integrableOn_cube_of_continuous hL (by
      have hc : Continuous (fun y : ℝ³ => Φ (Function.update x i y)) := by
        exact hΦc.comp (by fun_prop : Continuous (fun y : ℝ³ => Function.update x i y))
      exact hc.norm)
  have hInt2 : Integrable (fun _ : ℝ³ => B) μ' := by
    exact (integrableOn_const (μ := volume) (s := cube L) (C := B)
      (hs := ne_of_lt (measure_cube_lt_top hL)) (hC := by simp))
  have hmono : (∫ y : ℝ³, |Φ (Function.update x i y)| ∂μ') ≤ (∫ y : ℝ³, B ∂μ') := by
    refine integral_mono_ae hInt1 hInt2 ?_
    change ∀ᵐ y ∂μ', |Φ (Function.update x i y)| ≤ B
    rw [ae_restrict_iff' (cube_measurable L)]
    exact ae_of_all volume (by
      intro y hy
      exact hΦB (Function.update x i y) (update_mem_box i hx hy))
  have hIntB : (∫ y : ℝ³, B ∂μ') = B * L ^ 3 := by
    rw [MeasureTheory.integral_const]
    rw [real_volume_cube hL.le]
    simp
    ring
  have hmain : |(1 / L ^ 3) * (∫ y in cube L, Φ (Function.update x i y))| ≤ B := by
    have hnon : 0 ≤ 1 / L ^ 3 := by positivity
    calc
      |(1 / L ^ 3) * (∫ y : ℝ³, Φ (Function.update x i y) ∂μ')|
          = (1 / L ^ 3) * |(∫ y : ℝ³, Φ (Function.update x i y) ∂μ')| := by
            rw [abs_mul, abs_of_nonneg hnon]
      _ ≤ (1 / L ^ 3) * (∫ y : ℝ³, |Φ (Function.update x i y)| ∂μ') := by
            exact mul_le_mul_of_nonneg_left (abs_integral_le_integral_abs
              (f := fun y : ℝ³ => Φ (Function.update x i y)) (μ := μ')) hnon
      _ ≤ (1 / L ^ 3) * (∫ y : ℝ³, B ∂μ') := by
            exact mul_le_mul_of_nonneg_left hmono hnon
      _ ≤ B := by
            rw [hIntB]
            field_simp [ne_of_gt hL]
            exact le_rfl
  change |sectP L i Φ x| ≤ B
  unfold sectP
  simpa using hmain

/-- `sectP L i Φ` is (strongly) measurable in `x` -/
lemma sectP_aestronglyMeasurable {N : ℕ} {L : ℝ} (hL : 0 < L) (i : Fin N) {Φ : X N → ℝ}
    (hΦc : Continuous Φ) : AEStronglyMeasurable (sectP L i Φ) (volume.restrict (box N L)) := by
  have hf : AEStronglyMeasurable (fun x : X N => ∫ y : ℝ³, Φ (Function.update x i y)
      ∂((volume : Measure ℝ³).restrict (cube L))) (volume : Measure (X N)) := by
    have hfc : AEStronglyMeasurable (fun p : X N × ℝ³ => Φ (Function.update p.1 i p.2))
        ((volume : Measure (X N)).prod ((volume : Measure ℝ³).restrict (cube L))) := by
      exact (hΦc.comp (by fun_prop : Continuous (fun p : X N × ℝ³ => Function.update p.1 i p.2))).aestronglyMeasurable
    haveI : SigmaFinite ((volume : Measure ℝ³).restrict (cube L)) := by
      infer_instance
    exact hfc.integral_prod_right'
  have hconst : AEStronglyMeasurable (fun _ : X N => (1 / L ^ 3 : ℝ)) (volume : Measure (X N)) := by
    exact aestronglyMeasurable_const
  exact (hconst.mul hf).restrict

/-- zero configuration lies in the box -/
lemma zero_mem_box {N : ℕ} {L : ℝ} (hL : 0 ≤ L) : (0 : X N) ∈ box N L := by
  intro i k
  simp [hL]

/-- `sectP L i Φ` is integrable over the box -/
lemma sectP_integrableOn {N : ℕ} {L : ℝ} (hL : 0 < L) (i : Fin N) {Φ : X N → ℝ}
    (hΦc : Continuous Φ) : IntegrableOn (sectP L i Φ) (box N L) volume := by
  obtain ⟨C, hC⟩ := (box_compact hL).exists_bound_of_continuousOn (s := box N L) (f := Φ) hΦc.continuousOn
  have hC0 : 0 ≤ C := by
    have hb := hC (0 : X N) (zero_mem_box hL.le)
    exact le_trans (norm_nonneg (Φ (0 : X N))) hb
  refine IntegrableOn.of_bound ?hs ?hf C ?hb
  · exact (box_compact hL).measure_lt_top
  · exact sectP_aestronglyMeasurable hL i hΦc
  · change ∀ᵐ x ∂(volume.restrict (box N L)), ‖sectP L i Φ x‖ ≤ C
    rw [ae_restrict_iff' (IsClosed.measurableSet (box_closed L))]
    exact ae_of_all volume (by
      intro x hx
      have hle := sectP_abs_le hL i hΦc hC0 (by intro y hy; simpa [Real.norm_eq_abs] using hC y hy) x hx
      simpa using hle)

/-- changing only slot `i` of an inserted config re-inserts -/
lemma update_kcInsN {n : ℕ} (i : Fin (n + 1)) (y z : ℝ³) (r : X n) :
    Function.update (kcInsN n i (y, r)) i z = kcInsN n i (z, r) := by
  ext j
  by_cases hj : j = i
  · subst j
    simp [kc_insN_apply_same]
  · rcases Fin.exists_succAbove_eq hj with ⟨j', rfl⟩
    rw [Function.update_apply]
    simp [kc_insN_apply_succ, Fin.succAbove_ne]

/-- `Pᵢ` of an inserted configuration equals the cube mean of the fibre -/
lemma sectP_kcInsN {n : ℕ} {L : ℝ} (i : Fin (n + 1)) {Φ : X (n + 1) → ℝ}
    (y : ℝ³) (r : X n) :
    sectP L i Φ (kcInsN n i (y, r)) =
      (1 / L ^ 3) * (∫ z in cube L, Φ (kcInsN n i (z, r))) := by
  unfold sectP
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  congr 1
  exact update_kcInsN i y z r

/-- inserting `y` at slot `i` with rest `r` equals updating the zero-slot config -/
lemma kcInsN_update_zero {n : ℕ} (i : Fin (n + 1)) (y : ℝ³) (r : X n) :
    kcInsN n i (y, r) = Function.update (kcInsN n i (0, r)) i y := by
  ext j
  by_cases hj : j = i
  · subst j
    simp [kc_insN_apply_same]
  · rcases Fin.exists_succAbove_eq hj with ⟨j', rfl⟩
    rw [Function.update_apply]
    simp [kc_insN_apply_succ, Fin.succAbove_ne]

/-- smoothness of the fibre map `y ↦ Φ (insert y r)` -/
lemma fiber_contDiff {n : ℕ} (i : Fin (n + 1)) {Φ : X (n + 1) → ℝ}
    (hΦc : ContDiff ℝ ∞ Φ) (r : X n) :
    ContDiff ℝ ∞ (fun y : ℝ³ => Φ (kcInsN n i (y, r))) := by
  have hT : ContDiff ℝ ∞ (fun y : ℝ³ => kcInsN n i (y, r)) := by
    rw [show (fun y : ℝ³ => kcInsN n i (y, r)) = fun y : ℝ³ => Function.update (kcInsN n i (0, r)) i y by
      funext y
      exact kcInsN_update_zero i y r]
    exact contDiff_update ∞ (kcInsN n i (0, r)) i
  exact hΦc.comp hT

/-- derivative of the fibre equals the master derivative along the insertion -/
lemma fiber_fderiv {n : ℕ} (i : Fin (n + 1)) {Φ : X (n + 1) → ℝ}
    (hΦc : ContDiff ℝ ∞ Φ) (r : X n) (y : ℝ³) (v : ℝ³) :
    fderiv ℝ (fun y : ℝ³ => Φ (kcInsN n i (y, r))) y v =
      fderiv ℝ Φ (kcInsN n i (y, r)) (Function.update (0 : X (n + 1)) i v) := by
  have hT : ContDiff ℝ ∞ (fun y : ℝ³ => kcInsN n i (y, r)) := by
    rw [show (fun y : ℝ³ => kcInsN n i (y, r)) = fun y : ℝ³ => Function.update (kcInsN n i (0, r)) i y by
      funext y
      exact kcInsN_update_zero i y r]
    exact contDiff_update ∞ (kcInsN n i (0, r)) i
  have h1 : DifferentiableAt ℝ (fun y : ℝ³ => kcInsN n i (y, r)) y :=
    hT.differentiable (by norm_num) y
  have h2 : DifferentiableAt ℝ Φ (kcInsN n i (y, r)) :=
    hΦc.differentiable (by norm_num) (kcInsN n i (y, r))
  have hcomp := (h2.hasFDerivAt.comp y h1.hasFDerivAt).fderiv
  -- hcomp : fderiv ℝ (Φ ∘ fun y : ℝ³ => kcInsN n i (y, r)) y =
  --           (fderiv ℝ Φ (kcInsN n i (y, r)) ∘L fderiv ℝ (fun y : ℝ³ => kcInsN n i (y, r)) y)
  have hdfT : fderiv ℝ (fun y : ℝ³ => kcInsN n i (y, r)) y =
      ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ (ℝ³))) := by
    rw [show (fun y : ℝ³ => kcInsN n i (y, r)) = fun y : ℝ³ => Function.update (kcInsN n i (0, r)) i y by
      funext y
      exact kcInsN_update_zero i y r]
    exact fderiv_update (kcInsN n i (0, r)) y
  have hpi : ((ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ (ℝ³)))) v)
      = Function.update (0 : X (n + 1)) i v := by
    ext j
    simp [ContinuousLinearMap.pi, Pi.single_apply]
    by_cases hj : j = i
    · subst j
      simp
    · simp [hj]
  have hdv : (fderiv ℝ Φ (kcInsN n i (y, r)) ∘L fderiv ℝ (fun y : ℝ³ => kcInsN n i (y, r)) y) v =
      fderiv ℝ Φ (kcInsN n i (y, r)) (Function.update (0 : X (n + 1)) i v) := by
    rw [hdfT]
    simp only [ContinuousLinearMap.comp_apply]
    exact congrArg (fderiv ℝ Φ (kcInsN n i (y, r))) hpi
  calc
    fderiv ℝ (fun y : ℝ³ => Φ (kcInsN n i (y, r))) y v
        = (fderiv ℝ (Φ ∘ fun y : ℝ³ => kcInsN n i (y, r)) y) v := by rfl
    _ = (fderiv ℝ Φ (kcInsN n i (y, r)) ∘L fderiv ℝ (fun y : ℝ³ => kcInsN n i (y, r)) y) v := by
          rw [hcomp]
    _ = fderiv ℝ Φ (kcInsN n i (y, r)) (Function.update (0 : X (n + 1)) i v) := hdv

/-- Cauchy--Schwarz `(∫ f)² ≤ M·∫ f²` on a finite measure space (bounded a.e. `f`). -/
lemma cs_finite_measure {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → ℝ} (hm : AEStronglyMeasurable f μ) {C : ℝ} (hb : ∀ᵐ x ∂μ, |f x| ≤ C) :
    (∫ x, f x ∂μ) ^ 2 ≤ μ.real Set.univ * (∫ x, (f x) ^ 2 ∂μ) := by
  have hmem : MemLp (fun x : α => |f x|) (ENNReal.ofReal 2) μ :=
    MemLp.of_bound hm.norm C (by
      filter_upwards [hb] with x hx
      simpa using hx)
  have hmem1 : MemLp (fun _ : α => (1 : ℝ)) (ENNReal.ofReal 2) μ := memLp_const (1 : ℝ)
  have hnon1 : 0 ≤ᵐ[μ] (fun x : α => |f x|) := ae_of_all _ (fun _ => abs_nonneg _)
  have hnon2 : 0 ≤ᵐ[μ] (fun _ : α => (1 : ℝ)) := ae_of_all _ (fun _ => by norm_num)
  have hmain := integral_mul_le_Lp_mul_Lq_of_nonneg (p := 2) (q := 2) (μ := μ)
    Real.HolderConjugate.two_two hnon1 hnon2 hmem hmem1
  have hc1 : (∫ x : α, |f x| * 1 ∂μ) = ∫ x : α, |f x| ∂μ := by
    apply integral_congr_ae
    filter_upwards with x
    ring
  have hsq1 : (fun x : α => |f x| ^ (2 : ℝ)) = fun x : α => (f x) ^ 2 := by
    funext x
    rw [Real.rpow_two, sq_abs]
  have hc2 : (∫ x : α, (1 : ℝ) ^ (2 : ℝ) ∂μ) = μ.real Set.univ := by
    have h1 : (fun x : α => (1 : ℝ) ^ (2 : ℝ)) = fun _ : α => (1 : ℝ) := by
      funext x
      rw [Real.rpow_two]
      norm_num
    rw [h1, MeasureTheory.integral_const]
    simp
  have hB0 : 0 ≤ ∫ x : α, (f x) ^ 2 ∂μ := integral_nonneg (fun _ => sq_nonneg (f _))
  have hR : (∫ x : α, |f x| ∂μ) ≤ Real.sqrt (∫ x : α, (f x) ^ 2 ∂μ) * Real.sqrt (μ.real Set.univ) := by
    rw [hc1, hsq1, hc2] at hmain
    simpa [Real.sqrt_eq_rpow] using hmain
  have hsquared : (∫ x : α, |f x| ∂μ) ^ 2 ≤ (∫ x : α, (f x) ^ 2 ∂μ) * μ.real Set.univ := by
    have h1 : |∫ x : α, |f x| ∂μ| ≤
        |Real.sqrt (∫ x : α, (f x) ^ 2 ∂μ) * Real.sqrt (μ.real Set.univ)| := by
      calc
        |∫ x : α, |f x| ∂μ| = ∫ x : α, |f x| ∂μ := abs_of_nonneg (integral_nonneg (fun _ => abs_nonneg _))
        _ ≤ Real.sqrt (∫ x : α, (f x) ^ 2 ∂μ) * Real.sqrt (μ.real Set.univ) := hR
        _ = |Real.sqrt (∫ x : α, (f x) ^ 2 ∂μ) * Real.sqrt (μ.real Set.univ)| :=
          (abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).symm
    calc
      (∫ x : α, |f x| ∂μ) ^ 2 ≤ (Real.sqrt (∫ x : α, (f x) ^ 2 ∂μ) * Real.sqrt (μ.real Set.univ)) ^ 2 :=
        (sq_le_sq.mpr h1)
      _ = (∫ x : α, (f x) ^ 2 ∂μ) * μ.real Set.univ := by
        rw [mul_pow, Real.sq_sqrt hB0, Real.sq_sqrt (measureReal_nonneg : 0 ≤ μ.real Set.univ)]
  have hmain2 : |∫ x : α, f x ∂μ| ≤ ∫ x : α, |f x| ∂μ := abs_integral_le_integral_abs (μ := μ) (f := f)
  have hnn : 0 ≤ ∫ x : α, |f x| ∂μ := integral_nonneg (fun _ => abs_nonneg _)
  have h1 : |∫ x : α, f x ∂μ| ≤ |∫ x : α, |f x| ∂μ| := by
    calc
      |∫ x : α, f x ∂μ| ≤ ∫ x : α, |f x| ∂μ := hmain2
      _ = |∫ x : α, |f x| ∂μ| := (abs_of_nonneg hnn).symm
  calc
    (∫ x : α, f x ∂μ) ^ 2 ≤ (∫ x : α, |f x| ∂μ) ^ 2 := sq_le_sq.mpr h1
    _ ≤ (∫ x : α, (f x) ^ 2 ∂μ) * μ.real Set.univ := hsquared
    _ = μ.real Set.univ * (∫ x : α, (f x) ^ 2 ∂μ) := by rw [mul_comm]


/-- Cauchy--Schwarz on the cube: `(∫ f)² ≤ L³·∫ f²` for a continuous `f`. -/
lemma cs_cube {L : ℝ} (hL : 0 < L) {f : ℝ³ → ℝ} (hf : Continuous f) :
    (∫ y in cube L, f y) ^ 2 ≤ L ^ 3 * (∫ y in cube L, (f y) ^ 2) := by
  let μ' : Measure ℝ³ := (volume : Measure ℝ³).restrict (cube L)
  have hfin : IsFiniteMeasure μ' := by
    refine ⟨?set⟩
    rw [Measure.restrict_apply_univ]
    exact measure_cube_lt_top hL
  letI : IsFiniteMeasure μ' := hfin
  have hm : AEStronglyMeasurable f μ' := hf.aestronglyMeasurable
  obtain ⟨C, hC⟩ := (cube_compact hL).exists_bound_of_continuousOn (s := cube L) (f := f) hf.continuousOn
  have hb : ∀ᵐ y ∂μ', |f y| ≤ C := by
    rw [ae_restrict_iff' (cube_measurable L)]
    exact ae_of_all volume (fun y hy => by
      have hb' := hC y hy
      simpa [Real.norm_eq_abs] using hb')
  have hcs := cs_finite_measure (μ := μ') (f := f) hm hb
  have hvol : μ'.real Set.univ = L ^ 3 := by
    dsimp [μ']
    rw [MeasureTheory.measureReal_def, Measure.restrict_apply_univ]
    rw [volume_cube hL.le]
    rw [ENNReal.toReal_ofReal (pow_nonneg hL.le 3)]
  rw [hvol] at hcs
  simpa using hcs

/-- fibre Cauchy--Schwarz: the square of the fibre mean is at most the fibre mean square -/
lemma fibre_cs {n : ℕ} {L : ℝ} (hL : 0 < L) (i : Fin (n + 1)) {Φ : X (n + 1) → ℝ}
    (hΦ : Continuous Φ) (r : X n) :
    (∫ y in cube L, Φ (kcInsN n i (y, r))) ^ 2 ≤
      L ^ 3 * (∫ y in cube L, (Φ (kcInsN n i (y, r))) ^ 2) := by
  have hT : Continuous (fun y : ℝ³ => kcInsN n i (y, r)) := by
    rw [show (fun y : ℝ³ => kcInsN n i (y, r)) = fun y : ℝ³ => Function.update (kcInsN n i (0, r)) i y by
      funext y
      exact kcInsN_update_zero i y r]
    fun_prop
  exact cs_cube hL (hf := hΦ.comp hT)


/-- the box inner (peeled) integral of an integrable function is integrable in `r` -/
lemma box_peel_inner_integrable {n : ℕ} {L : ℝ} (i : Fin (n + 1)) (F : X (n + 1) → ℝ)
    (hF : IntegrableOn F (box (n + 1) L) volume) :
    Integrable (fun r : X n => ∫ y in cube L, F (kcInsN n i (y, r)))
      ((volume : Measure (X n)).restrict (box n L)) := by
  let μ' : Measure ℝ³ := (volume : Measure ℝ³).restrict (cube L)
  let ν : Measure (X n) := (volume : Measure (X n)).restrict (box n L)
  have hmp : MeasurePreserving (⇑(kcInsN n i)) (μ'.prod ν)
      ((volume : Measure (X (n + 1))).restrict (box (n + 1) L)) := by
    have h := MeasurePreserving.symm (e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ³) i))
      (box_peel_mp (n := n) L i)
    simpa [kcInsN, μ', ν] using h
  have hpeel : Integrable (fun p : ℝ³ × X n => F (kcInsN n i p)) (μ'.prod ν) := by
    exact (hmp.integrable_comp (hg := hF.aestronglyMeasurable)).mpr hF
  have hsw : MeasurePreserving (fun p : X n × ℝ³ => (p.2, p.1)) (ν.prod μ') (μ'.prod ν) := by
    refine MeasurePreserving.mk (by measurability) ?_
    exact (MeasureTheory.Measure.prod_swap (μ := ν) (ν := μ'))
  have hswap : Integrable (fun p : X n × ℝ³ => F (kcInsN n i (p.2, p.1))) (ν.prod μ') := by
    exact (hsw.integrable_comp (hg := hpeel.aestronglyMeasurable)).mpr hpeel
  exact (hswap.integral_prod_left (μ := ν) (ν := μ'))

/-- square of `QᵢΦ` is integrable over the box -/
lemma integrableOn_sq_sectQ {N : ℕ} {L : ℝ} (hL : 0 < L) (i : Fin N) {Φ : X N → ℝ}
    (hΦc : Continuous Φ) : IntegrableOn (fun x : X N => (sectQ L i Φ x) ^ 2) (box N L) volume := by
  obtain ⟨B, hB⟩ := (box_compact hL).exists_bound_of_continuousOn (s := box N L) (f := Φ) hΦc.continuousOn
  have hB0 : 0 ≤ B := by
    have hb := hB (0 : X N) (zero_mem_box hL.le)
    exact le_trans (norm_nonneg (Φ (0 : X N))) hb
  have hbndP : ∀ x ∈ box N L, |sectP L i Φ x| ≤ B :=
    sectP_abs_le hL i hΦc hB0 (by intro y hy; simpa [Real.norm_eq_abs] using hB y hy)
  have hbndΦ : ∀ x ∈ box N L, |Φ x| ≤ B := by
    intro x hx
    simpa [Real.norm_eq_abs] using hB x hx
  refine IntegrableOn.of_bound ?hs ?hf ((2 * B) ^ 2) ?hb
  · exact (box_compact hL).measure_lt_top
  · have hq : AEStronglyMeasurable (sectQ L i Φ) (volume.restrict (box N L)) := by
      change AEStronglyMeasurable (fun x : X N => Φ x - sectP L i Φ x) (volume.restrict (box N L))
      exact (hΦc.aestronglyMeasurable.restrict (s := box N L)).sub
        (sectP_aestronglyMeasurable hL i hΦc)
    exact hq.pow 2
  · change ∀ᵐ x ∂(volume.restrict (box N L)), ‖(sectQ L i Φ x) ^ 2‖ ≤ (2 * B) ^ 2
    rw [ae_restrict_iff' (IsClosed.measurableSet (box_closed L))]
    exact ae_of_all volume (by
      intro x hx
      have h1 : |Φ x| ≤ B := hbndΦ x hx
      have h2 : |sectP L i Φ x| ≤ B := hbndP x hx
      have hq : |sectQ L i Φ x| ≤ 2 * B := by
        unfold sectQ
        have htri : |Φ x - sectP L i Φ x| ≤ |Φ x| + |sectP L i Φ x| := by
          simpa using (norm_sub_le (Φ x) (sectP L i Φ x))
        nlinarith
      calc
        ‖(sectQ L i Φ x) ^ 2‖ = (sectQ L i Φ x) ^ 2 := by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        _ = |sectQ L i Φ x| ^ 2 := by rw [sq_abs]
        _ ≤ (2 * B) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hq 2)

/-- squared kinetic sum of particle `i` is integrable over the box -/
lemma integrableOn_kinSum {N : ℕ} {L : ℝ} (hL : 0 < L) (i : Fin N) {Φ : X N → ℝ}
    (hΦc : ContDiff ℝ ∞ Φ) :
    IntegrableOn (fun x : X N => ∑ k : Fin 3, (fderiv ℝ Φ x (kcDir N i k)) ^ 2) (box N L) volume := by
  have hsum : Integrable (fun x : X N => ∑ k : Fin 3, (fderiv ℝ Φ x (kcDir N i k)) ^ 2)
      (volume.restrict (box N L)) := by
    exact integrable_finsetSum (s := Finset.univ) (μ := (volume : Measure (X N)).restrict (box N L))
      (f := fun k : Fin 3 => fun x : X N => (fderiv ℝ Φ x (kcDir N i k)) ^ 2) (by
        intro k hk
        have hc : Continuous (fun x : X N => (fderiv ℝ Φ x (kcDir N i k)) ^ 2) := by
          exact (firstDir_contDiff (f := Φ) hΦc (kcDir N i k)).continuous.pow 2
        exact integrableOn_box_of_continuous hL hc)
  exact hsum

/-- the sum over the reindexed standard ONB equals the sum over the coordinate basis -/
lemma sum_fderiv_onb_eq_coord {φ : ℝ³ → ℝ} (y : ℝ³) :
    (∑ k : Fin 3, (fderiv ℝ φ y (euclBasis3 k)) ^ 2) =
      (∑ k : Fin 3, (fderiv ℝ φ y (kcStdBasis k)) ^ 2) := by
  have h1 := cg_onb_sum_eq (φ := φ) y
  calc
    (∑ k : Fin 3, (fderiv ℝ φ y (euclBasis3 k)) ^ 2)
        = (∑ k : Fin 3, (fderiv ℝ φ y (EuclideanSpace.basisFun (Fin 3) ℝ k)) ^ 2) := h1
    _ = (∑ k : Fin 3, (fderiv ℝ φ y (kcStdBasis k)) ^ 2) := by
          apply Finset.sum_congr rfl
          intro k hk
          congr 1
          rw [EuclideanSpace.basisFun_apply]
          rfl

/-- fibre derivative along the coordinate `k` of the inserted config -/
lemma fiber_fderiv_kcDir {n : ℕ} (i : Fin (n + 1)) {Φ : X (n + 1) → ℝ}
    (hΦc : ContDiff ℝ ∞ Φ) (r : X n) (y : ℝ³) (k : Fin 3) :
    fderiv ℝ (fun y : ℝ³ => Φ (kcInsN n i (y, r))) y (kcStdBasis k) =
      fderiv ℝ Φ (kcInsN n i (y, r)) (kcDir (n + 1) i k) := by
  have h := fiber_fderiv (i := i) (Φ := Φ) hΦc r y (kcStdBasis k)
  simpa [kcDir] using h

/-- `Pᵢ` is idempotent: `Pᵢ(PᵢΦ) = PᵢΦ`. -/
theorem sectP_idem {N : ℕ} (L : ℝ) (hL : 0 < L) (i : Fin N) {Φ : X N → ℝ}
    (hΦc : ContDiff ℝ ∞ Φ) : sectP L i (sectP L i Φ) = sectP L i Φ := by
  funext x
  have hinv : ∀ y : ℝ³, sectP L i Φ (Function.update x i y) = sectP L i Φ x := by
    intro y
    unfold sectP
    congr 1
    apply integral_congr_ae
    filter_upwards with z
    congr 1
    ext j
    by_cases hj : j = i
    · subst j
      simp
    · simp [hj]
  calc
    sectP L i (sectP L i Φ) x = (1 / L ^ 3) * (∫ y : ℝ³ in cube L, sectP L i Φ x) := by
      unfold sectP
      congr 1
      apply integral_congr_ae
      filter_upwards with y
      exact hinv y
    _ = sectP L i Φ x := by
      rw [integral_const_cube hL]
      field_simp [ne_of_gt hL]

/-- continuity of the insertion map -/
lemma kcInsN_cont {n : ℕ} (i : Fin (n + 1)) :
    Continuous (fun p : ℝ³ × X n => kcInsN n i p) := by
  rw [continuous_pi_iff]
  intro j
  by_cases hj : j = i
  · subst j
    have hEq : (fun p : ℝ³ × X n => (kcInsN n i p) i) = fun p : ℝ³ × X n => p.1 := by
      funext p
      exact kc_insN_apply_same n i p.1 p.2
    rw [hEq]
    fun_prop
  · rcases Fin.exists_succAbove_eq hj with ⟨j', rfl⟩
    have hEq : (fun p : ℝ³ × X n => (kcInsN n i p) (i.succAbove j')) = fun p : ℝ³ × X n => p.2 j' := by
      funext p
      exact kc_insN_apply_succ n i p.1 p.2 j'
    rw [hEq]
    fun_prop

/-- `sectP L i Φ` multiplied by a continuous function is integrable over the box -/
lemma integrableOn_mul_sectP {N : ℕ} {L : ℝ} (hL : 0 < L) (i : Fin N) {Φ Ψ : X N → ℝ}
    (hΦc : Continuous Φ) (hΨc : Continuous Ψ) :
    IntegrableOn (fun x : X N => Φ x * sectP L i Ψ x) (box N L) volume := by
  obtain ⟨B, hB⟩ := (box_compact hL).exists_bound_of_continuousOn (s := box N L) (f := Ψ) hΨc.continuousOn
  have hB0 : 0 ≤ B := by
    have hb := hB (0 : X N) (zero_mem_box hL.le)
    exact le_trans (norm_nonneg (Ψ (0 : X N))) hb
  have hf : AEStronglyMeasurable (fun x : X N => Φ x * sectP L i Ψ x)
      (volume.restrict (box N L)) := by
    exact ((hΦc.aestronglyMeasurable.restrict (s := box N L)).mul
      (sectP_aestronglyMeasurable hL i hΨc))
  have hg : Integrable (fun x : X N => |Φ x| * B) (volume.restrict (box N L)) := by
    have hΦabs : Integrable (fun x : X N => |Φ x|) (volume.restrict (box N L)) :=
      integrableOn_box_of_continuous hL hΦc.norm
    exact hΦabs.mul_const B
  refine Integrable.mono' hg hf ?_
  change ∀ᵐ x ∂(volume.restrict (box N L)), ‖Φ x * sectP L i Ψ x‖ ≤ |Φ x| * B
  rw [ae_restrict_iff' (IsClosed.measurableSet (box_closed L))]
  exact ae_of_all volume (by
    intro x hx
    have hbndP : |sectP L i Ψ x| ≤ B :=
      sectP_abs_le hL i hΨc hB0 (by intro y hy; simpa [Real.norm_eq_abs] using hB y hy) x hx
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left hbndP (abs_nonneg _))

lemma integrableOn_sq_sectP {N : ℕ} {L : ℝ} (hL : 0 < L) (i : Fin N) {Φ : X N → ℝ}
    (hΦc : Continuous Φ) : IntegrableOn (fun x : X N => (sectP L i Φ x) ^ 2) (box N L) volume := by
  obtain ⟨B, hB⟩ := (box_compact hL).exists_bound_of_continuousOn (s := box N L) (f := Φ) hΦc.continuousOn
  have hB0 : 0 ≤ B := by
    have hb := hB (0 : X N) (zero_mem_box hL.le)
    exact le_trans (norm_nonneg (Φ (0 : X N))) hb
  refine IntegrableOn.of_bound ?hs ?hf (B ^ 2) ?hbnd
  · exact (box_compact hL).measure_lt_top
  · exact (sectP_aestronglyMeasurable hL i hΦc).pow 2
  · change ∀ᵐ x ∂(volume.restrict (box N L)), ‖(sectP L i Φ x) ^ 2‖ ≤ B ^ 2
    rw [ae_restrict_iff' (IsClosed.measurableSet (box_closed L))]
    exact ae_of_all volume (by
      intro x hx
      have hle : |sectP L i Φ x| ≤ B :=
        sectP_abs_le hL i hΦc hB0 (by intro y hy; simpa [Real.norm_eq_abs] using hB y hy) x hx
      calc
        ‖(sectP L i Φ x) ^ 2‖ = (sectP L i Φ x) ^ 2 := by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        _ = |sectP L i Φ x| ^ 2 := by rw [sq_abs]
        _ ≤ B ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hle 2)

/-- peeled form of the squared projection: `∫(PΦ)² = (1/L³)·∫ₓ A(r)²`. -/
lemma peel_sq_sectP {n : ℕ} {L : ℝ} (hL : 0 < L) (i : Fin (n + 1)) {Φ : X (n + 1) → ℝ}
    (hΦc : Continuous Φ) :
    (∫ x in box (n + 1) L, (sectP L i Φ x) ^ 2) =
      ∫ r : X n, (1 / L ^ 3) * (∫ y in cube L, Φ (kcInsN n i (y, r))) ^ 2
        ∂((volume : Measure (X n)).restrict (box n L)) := by
  have hP := box_integral_peel (i := i)
    (F := fun x : X (n + 1) => (sectP L i Φ x) ^ 2) (integrableOn_sq_sectP hL i hΦc)
  have hpoint : ∀ r : X n,
      (∫ y in cube L, (sectP L i Φ (kcInsN n i (y, r))) ^ 2)
        = (1 / L ^ 3) * (∫ y in cube L, Φ (kcInsN n i (y, r))) ^ 2 := by
    intro r
    calc
      (∫ y in cube L, (sectP L i Φ (kcInsN n i (y, r))) ^ 2)
          = ∫ y in cube L, ((1 / L ^ 3) * (∫ z in cube L, Φ (kcInsN n i (z, r)))) ^ 2 := by
            apply integral_congr_ae
            filter_upwards with y
            rw [sectP_kcInsN (L := L) (Φ := Φ) i y r]
      _ = L ^ 3 * ((1 / L ^ 3) * (∫ z in cube L, Φ (kcInsN n i (z, r)))) ^ 2 := by
            rw [integral_const_cube hL]
            ring
      _ = (1 / L ^ 3) * (∫ y in cube L, Φ (kcInsN n i (y, r))) ^ 2 := by
            field_simp [ne_of_gt hL]
  calc
    (∫ x in box (n + 1) L, (sectP L i Φ x) ^ 2)
        = ∫ r : X n, (∫ y in cube L, (sectP L i Φ (kcInsN n i (y, r))) ^ 2)
            ∂((volume : Measure (X n)).restrict (box n L)) := hP
    _ = ∫ r : X n, (1 / L ^ 3) * (∫ y in cube L, Φ (kcInsN n i (y, r))) ^ 2
            ∂((volume : Measure (X n)).restrict (box n L)) := by
          apply integral_congr_ae
          filter_upwards with r
          exact hpoint r

/-- peeled form of `⟨Φ, PᵢΦ⟩` -/
lemma Phi_mul_sectP_integral {n : ℕ} {L : ℝ} (hL : 0 < L) (i : Fin (n + 1)) {Φ : X (n + 1) → ℝ}
    (hΦc : Continuous Φ) :
    (∫ x in box (n + 1) L, Φ x * sectP L i Φ x) =
      ∫ r : X n, (1 / L ^ 3) * (∫ y in cube L, Φ (kcInsN n i (y, r))) ^ 2
        ∂((volume : Measure (X n)).restrict (box n L)) := by
  have hP := box_integral_peel (i := i)
    (F := fun x : X (n + 1) => Φ x * sectP L i Φ x)
    (integrableOn_mul_sectP hL i hΦc hΦc)
  have hpoint : ∀ r : X n,
      (∫ y in cube L, Φ (kcInsN n i (y, r)) * sectP L i Φ (kcInsN n i (y, r)))
        = (1 / L ^ 3) * (∫ y in cube L, Φ (kcInsN n i (y, r))) ^ 2 := by
    intro r
    calc
      (∫ y in cube L, Φ (kcInsN n i (y, r)) * sectP L i Φ (kcInsN n i (y, r)))
          = ∫ y in cube L, Φ (kcInsN n i (y, r)) *
              ((1 / L ^ 3) * (∫ z in cube L, Φ (kcInsN n i (z, r)))) := by
            apply integral_congr_ae
            filter_upwards with y
            exact congrArg (fun t : ℝ => Φ (kcInsN n i (y, r)) * t)
              (sectP_kcInsN (L := L) (Φ := Φ) i y r)
      _ = (∫ y in cube L, Φ (kcInsN n i (y, r))) *
              ((1 / L ^ 3) * (∫ z in cube L, Φ (kcInsN n i (z, r)))) := by
            rw [MeasureTheory.integral_mul_const]
      _ = (1 / L ^ 3) * (∫ y in cube L, Φ (kcInsN n i (y, r))) ^ 2 := by
            ring
  calc
    (∫ x in box (n + 1) L, Φ x * sectP L i Φ x)
        = ∫ r : X n, (∫ y in cube L, Φ (kcInsN n i (y, r)) * sectP L i Φ (kcInsN n i (y, r)))
            ∂((volume : Measure (X n)).restrict (box n L)) := hP
    _ = ∫ r : X n, (1 / L ^ 3) * (∫ y in cube L, Φ (kcInsN n i (y, r))) ^ 2
            ∂((volume : Measure (X n)).restrict (box n L)) := by
          apply integral_congr_ae
          filter_upwards with r
          exact hpoint r

/-- `Pᵢ` and `Qᵢ` are orthogonal: `⟨PᵢΦ, QᵢΦ⟩ = 0`. -/
theorem sectQ_ortho {N : ℕ} (L : ℝ) (hL : 0 < L) (i : Fin N) {Φ : X N → ℝ}
    (hΦc : ContDiff ℝ ∞ Φ) :
    (∫ x in box N L, sectP L i Φ x * sectQ L i Φ x) = 0 := by
  cases N with
  | zero =>
      exfalso
      exact Nat.not_lt_zero i.1 i.isLt
  | succ n =>
      have hInt1 : IntegrableOn (fun x : X (n + 1) => sectP L i Φ x * Φ x) (box (n + 1) L) volume := by
        have hEq : (fun x : X (n + 1) => sectP L i Φ x * Φ x) = fun x : X (n + 1) => Φ x * sectP L i Φ x := by
          funext x
          rw [mul_comm]
        rw [hEq]
        exact integrableOn_mul_sectP hL i hΦc.continuous hΦc.continuous
      have hInt2 : IntegrableOn (fun x : X (n + 1) => (sectP L i Φ x) ^ 2) (box (n + 1) L) volume :=
        integrableOn_sq_sectP hL i hΦc.continuous
      have hpeel1 := peel_sq_sectP hL i hΦc.continuous
      have hpeel2 := Phi_mul_sectP_integral hL i hΦc.continuous
      -- ∫ PΦ·Φ = ∫ (PΦ)²
      have hmain : (∫ x in box (n + 1) L, sectP L i Φ x * Φ x)
          = (∫ x in box (n + 1) L, (sectP L i Φ x) ^ 2) := by
        calc
          (∫ x in box (n + 1) L, sectP L i Φ x * Φ x)
              = ∫ x in box (n + 1) L, Φ x * sectP L i Φ x := by
                apply integral_congr_ae
                filter_upwards with x
                rw [mul_comm]
          _ = (∫ x in box (n + 1) L, (sectP L i Φ x) ^ 2) := by
                rw [hpeel1, hpeel2]
      calc
        (∫ x in box (n + 1) L, sectP L i Φ x * sectQ L i Φ x)
            = ∫ x in box (n + 1) L, sectP L i Φ x * Φ x - (sectP L i Φ x) ^ 2 := by
              apply integral_congr_ae
              filter_upwards with x
              unfold sectQ
              ring
        _ = (∫ x in box (n + 1) L, sectP L i Φ x * Φ x) -
              (∫ x in box (n + 1) L, (sectP L i Φ x) ^ 2) := by
              exact integral_sub (μ := (volume : Measure (X (n + 1))).restrict (box (n + 1) L)) hInt1 hInt2
        _ = 0 := by rw [hmain]; ring

/-- Total mass is preserved by `Pᵢ`: `∫ PᵢΦ = ∫ Φ` over the box. -/
theorem sectP_integral_eq {N : ℕ} (L : ℝ) (hL : 0 < L) (i : Fin N) {Φ : X N → ℝ}
    (hΦc : ContDiff ℝ ∞ Φ) :
    (∫ x in box N L, sectP L i Φ x) = (∫ x in box N L, Φ x) := by
  cases N with
  | zero =>
      exfalso
      exact Nat.not_lt_zero i.1 i.isLt
  | succ n =>
      have hΦint : IntegrableOn Φ (box (n + 1) L) volume :=
        integrableOn_box_of_continuous hL hΦc.continuous
      have hPl := box_integral_peel (i := i)
        (F := fun x : X (n + 1) => sectP L i Φ x) (sectP_integrableOn hL i hΦc.continuous)
      have hPR := box_integral_peel (i := i) (F := Φ) hΦint
      calc
        (∫ x in box (n + 1) L, sectP L i Φ x)
            = ∫ r : X n, (∫ y : ℝ³ in cube L, sectP L i Φ (kcInsN n i (y, r)))
                ∂((volume : Measure (X n)).restrict (box n L)) := hPl
        _ = ∫ r : X n, (∫ z : ℝ³ in cube L, Φ (kcInsN n i (z, r)))
                ∂((volume : Measure (X n)).restrict (box n L)) := by
              apply integral_congr_ae
              filter_upwards with r
              have h1 : (∫ y : ℝ³ in cube L, sectP L i Φ (kcInsN n i (y, r)))
                  = ∫ y : ℝ³ in cube L, (1 / L ^ 3) * (∫ z in cube L, Φ (kcInsN n i (z, r))) := by
                apply integral_congr_ae
                filter_upwards with y
                exact sectP_kcInsN i y r
              rw [h1]
              rw [integral_const_cube hL]
              field_simp [ne_of_gt hL]
        _ = (∫ x in box (n + 1) L, Φ x) := by
              exact hPR.symm

/-- Contractivity: `‖PᵢΦ‖² ≤ ‖Φ‖²` on the box. -/
theorem sectP_sq_le {N : ℕ} (L : ℝ) (hL : 0 < L) (i : Fin N) {Φ : X N → ℝ}
    (hΦc : ContDiff ℝ ∞ Φ) :
    (∫ x in box N L, (sectP L i Φ x) ^ 2) ≤ (∫ x in box N L, (Φ x) ^ 2) := by
  cases N with
  | zero =>
      exfalso
      exact Nat.not_lt_zero i.1 i.isLt
  | succ n =>
      obtain ⟨B, hB⟩ := (box_compact hL).exists_bound_of_continuousOn (s := box (n + 1) L) (f := Φ)
        hΦc.continuous.continuousOn
      have hB0 : 0 ≤ B := by
        have hb := hB (0 : X (n + 1)) (zero_mem_box hL.le)
        exact le_trans (norm_nonneg (Φ (0 : X (n + 1)))) hb
      have hswap : Continuous (fun p : X n × ℝ³ => (p.2, p.1)) := by fun_prop
      let F1 : X n → ℝ := fun r => (1 / L ^ 3) * (∫ y in cube L, Φ (kcInsN n i (y, r))) ^ 2
      let F2 : X n → ℝ := fun r => ∫ y in cube L, (Φ (kcInsN n i (y, r))) ^ 2
      have hg2aem : AEStronglyMeasurable F2 (volume : Measure (X n)) := by
        have hf : AEStronglyMeasurable (fun p : X n × ℝ³ => (Φ (kcInsN n i (p.2, p.1))) ^ 2)
            ((volume : Measure (X n)).prod ((volume : Measure ℝ³).restrict (cube L))) := by
          exact ((hΦc.continuous.comp ((kcInsN_cont i).comp hswap)).pow 2).aestronglyMeasurable
        haveI : SigmaFinite ((volume : Measure ℝ³).restrict (cube L)) := by infer_instance
        exact (hf.integral_prod_right' : AEStronglyMeasurable (fun r : X n =>
          ∫ y : ℝ³, (Φ (kcInsN n i (y, r))) ^ 2 ∂(volume.restrict (cube L))) (volume : Measure (X n)))
      have hF2_aem : AEStronglyMeasurable F2 (volume.restrict (box n L)) := by
        change AEStronglyMeasurable (fun r : X n => ∫ y in cube L, (Φ (kcInsN n i (y, r))) ^ 2)
          (volume.restrict (box n L))
        exact hg2aem.restrict
      have hF2_bnd : ∀ᵐ r ∂(volume.restrict (box n L)), ‖F2 r‖ ≤ B ^ 2 * L ^ 3 := by
        change ∀ᵐ r ∂(volume.restrict (box n L)),
            ‖∫ y in cube L, (Φ (kcInsN n i (y, r))) ^ 2‖ ≤ B ^ 2 * L ^ 3
        rw [ae_restrict_iff' (IsClosed.measurableSet (box_closed L))]
        exact ae_of_all volume (by
          intro r hr
          have hbnd : ∀ᵐ y ∂(volume.restrict (cube L)), (Φ (kcInsN n i (y, r))) ^ 2 ≤ B ^ 2 := by
            rw [ae_restrict_iff' (cube_measurable L)]
            exact ae_of_all volume (by
              intro y hy
              have hb' := hB (kcInsN n i (y, r)) (by
                intro j k
                by_cases hj : j = i
                · subst j
                  rw [kc_insN_apply_same]
                  exact hy k
                · rcases Fin.exists_succAbove_eq hj with ⟨j', rfl⟩
                  rw [kc_insN_apply_succ]
                  exact hr j' k)
              have hb2 : |Φ (kcInsN n i (y, r))| ≤ B := by simpa [Real.norm_eq_abs] using hb'
              calc
                (Φ (kcInsN n i (y, r))) ^ 2 = |Φ (kcInsN n i (y, r))| ^ 2 := by rw [sq_abs]
                _ ≤ B ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb2 2)
          have hIntY : Integrable (fun y : ℝ³ => (Φ (kcInsN n i (y, r))) ^ 2)
              (volume.restrict (cube L)) := by
            have hc : Continuous (fun y : ℝ³ => (Φ (kcInsN n i (y, r))) ^ 2) := by
              exact ((hΦc.continuous.comp ((kcInsN_cont i).comp
                (by fun_prop : Continuous (fun y : ℝ³ => (y, r))))).pow 2)
            exact integrableOn_cube_of_continuous hL hc
          have hIntC : Integrable (fun _ : ℝ³ => B ^ 2) (volume.restrict (cube L)) :=
            integrableOn_const (s := cube L) (C := B ^ 2) (hs := ne_of_lt (measure_cube_lt_top hL)) (hC := by simp)
          have hle1 : (∫ y in cube L, (Φ (kcInsN n i (y, r))) ^ 2) ≤ (∫ y in cube L, B ^ 2) := by
            exact integral_mono_ae hIntY hIntC hbnd
          have hineq : (∫ y in cube L, (Φ (kcInsN n i (y, r))) ^ 2) ≤ B ^ 2 * L ^ 3 := by
            calc
              (∫ y in cube L, (Φ (kcInsN n i (y, r))) ^ 2) ≤ (∫ y in cube L, B ^ 2) := hle1
              _ = B ^ 2 * L ^ 3 := by rw [integral_const_cube hL]
          have habs : ‖∫ y in cube L, (Φ (kcInsN n i (y, r))) ^ 2‖
              = ∫ y in cube L, (Φ (kcInsN n i (y, r))) ^ 2 := by
            rw [Real.norm_eq_abs, abs_of_nonneg]
            exact integral_nonneg (fun _ => sq_nonneg _)
          rw [habs]
          exact hineq)
      have hg2_int : Integrable F2 (volume.restrict (box n L)) := by
        exact IntegrableOn.of_bound (s := box n L) (f := F2) (C := B ^ 2 * L ^ 3)
          (hs := (box_compact hL).measure_lt_top) (hf := hF2_aem) (hfC := hF2_bnd)
      have hpt : ∀ r : X n, F1 r ≤ F2 r := by
        intro r
        have hcs := fibre_cs hL i hΦc.continuous r
        have hmul : (1 / L ^ 3) * L ^ 3 = 1 := by field_simp [ne_of_gt hL]
        calc
          F1 r = (1 / L ^ 3) * (∫ y in cube L, Φ (kcInsN n i (y, r))) ^ 2 := by rfl
          _ ≤ (1 / L ^ 3) * (L ^ 3 * (∫ y in cube L, (Φ (kcInsN n i (y, r))) ^ 2)) := by
                exact mul_le_mul_of_nonneg_left hcs (by positivity)
          _ = ∫ y in cube L, (Φ (kcInsN n i (y, r))) ^ 2 := by
                rw [← mul_assoc, hmul, one_mul]
          _ = F2 r := by rfl
      have hF1_aem : AEStronglyMeasurable F1 (volume.restrict (box n L)) := by
        change AEStronglyMeasurable (fun r : X n => (1 / L ^ 3) * (∫ y in cube L, Φ (kcInsN n i (y, r))) ^ 2)
          (volume.restrict (box n L))
        have hA : AEStronglyMeasurable (fun r : X n => ∫ y in cube L, Φ (kcInsN n i (y, r)))
            (volume : Measure (X n)) := by
          have hf : AEStronglyMeasurable (fun p : X n × ℝ³ => Φ (kcInsN n i (p.2, p.1)))
              ((volume : Measure (X n)).prod ((volume : Measure ℝ³).restrict (cube L))) := by
            exact (hΦc.continuous.comp ((kcInsN_cont i).comp hswap)).aestronglyMeasurable
          haveI : SigmaFinite ((volume : Measure ℝ³).restrict (cube L)) := by infer_instance
          exact (hf.integral_prod_right' : AEStronglyMeasurable (fun r : X n =>
            ∫ y : ℝ³, Φ (kcInsN n i (y, r)) ∂(volume.restrict (cube L))) (volume : Measure (X n)))
        exact ((hA.restrict).pow 2).const_mul (1 / L ^ 3)
      have hF1_bnd : ∀ᵐ r ∂(volume.restrict (box n L)), ‖F1 r‖ ≤ F2 r := by
        filter_upwards with r
        rw [Real.norm_eq_abs, abs_of_nonneg]
        · exact hpt r
        · positivity
      have hg1_int : Integrable F1 (volume.restrict (box n L)) :=
        Integrable.mono' hg2_int hF1_aem hF1_bnd
      have hP := peel_sq_sectP hL i hΦc.continuous
      have hPR := box_integral_peel (i := i)
        (F := fun x : X (n + 1) => (Φ x) ^ 2) (integrableOn_box_of_continuous hL (hΦc.continuous.pow 2))
      calc
        (∫ x in box (n + 1) L, (sectP L i Φ x) ^ 2)
            = ∫ r : X n, (1 / L ^ 3) * (∫ y in cube L, Φ (kcInsN n i (y, r))) ^ 2
                ∂(volume.restrict (box n L)) := hP
        _ ≤ ∫ r : X n, (∫ y in cube L, (Φ (kcInsN n i (y, r))) ^ 2)
                ∂(volume.restrict (box n L)) := by
              refine integral_mono_ae (μ := (volume : Measure (X n)).restrict (box n L)) hg1_int hg2_int ?_
              filter_upwards with r
              exact hpt r
        _ = (∫ x in box (n + 1) L, (Φ x) ^ 2) := hPR.symm

/-- `Pᵢ` fixes functions that are constant in coordinate `i` (i.e. do not
depend on `x i`): `Φ(update x i y) = Φ x` for all `x, y` implies `PᵢΦ = Φ`.
(NB: the earlier draft `Φ = g ∘ xᵢ` was wrong — that says Φ depends *only*
on `x i`, and `Pᵢ` averages it to a constant.) -/
theorem sectP_of_const_in_coord {N : ℕ} (L : ℝ) (hL : 0 < L) (i : Fin N) {Φ : X N → ℝ}
    (hΦc : ContDiff ℝ ∞ Φ) (hind : ∀ x : X N, ∀ y : ℝ³, Φ (Function.update x i y) = Φ x) :
    sectP L i Φ = Φ := by
  funext x
  calc
    sectP L i Φ x = (1 / L ^ 3) * (∫ y : ℝ³ in cube L, Φ x) := by
      unfold sectP
      congr 1
      apply integral_congr_ae
      filter_upwards with y
      exact hind x y
    _ = Φ x := by
      rw [integral_const_cube hL]
      field_simp [ne_of_gt hL]

/-- **Gap above the condensate, particle form**: for an `N`-particle state,
`∫_{box N L} (QᵢΦ)² ≤ 36·L²·∫_{box N L} Σ_k (∂_{ik}Φ)²` — the excited part of
particle `i` costs kinetic energy (the right side is particle-`i`'s kinetic
term in `Neumann.kinNeu`). -/
theorem sectQ_gap {N : ℕ} (L : ℝ) (hL : 0 < L) (i : Fin N) {Φ : X N → ℝ}
    (hΦc : ContDiff ℝ ∞ Φ) :
    (∫ x in box N L, (sectQ L i Φ x) ^ 2) ≤
      (36 : ℝ) * L ^ 2 *
        (∫ x in box N L, ∑ k : Fin 3,
          (fderiv ℝ Φ x (kcDir N i k)) ^ 2) := by
  cases N with
  | zero =>
      exfalso
      exact Nat.not_lt_zero i.1 i.isLt
  | succ n =>
      let ν : Measure (X n) := (volume : Measure (X n)).restrict (box n L)
      let fib : X n → ℝ³ → ℝ := fun r y => Φ (kcInsN n i (y, r))
      let I1 : X n → ℝ := fun r => ∫ y in cube L, (sectQ L i Φ (kcInsN n i (y, r))) ^ 2
      let I2 : X n → ℝ := fun r => ∫ y in cube L,
          ∑ k : Fin 3, (fderiv ℝ Φ (kcInsN n i (y, r)) (kcDir (n + 1) i k)) ^ 2
      have hident : ∀ r y, sectQ L i Φ (kcInsN n i (y, r))
          = fib r y - (1 / L ^ 3) * (∫ z in cube L, fib r z) := by
        intro r y
        dsimp [fib]
        unfold sectQ
        simp [sectP_kcInsN (L := L) (Φ := Φ) i y r]
      have hfibc : ∀ r : X n, ContDiff ℝ ∞ (fib r) := by
        intro r
        dsimp [fib]
        exact fiber_contDiff i hΦc r
      -- pointwise inequality: I1 ≤ 36 L² · I2
      have hpt : ∀ r : X n, I1 r ≤ (36 : ℝ) * L ^ 2 * I2 r := by
        intro r
        have hc := cube_gap L hL (φ := fib r) (hfibc r)
        have hcL : I1 r = (∫ y in cube L,
            ((fib r y) - (1 / L ^ 3) * (∫ z in cube L, fib r z)) ^ 2) := by
          dsimp [I1]
          apply integral_congr_ae
          filter_upwards with y
          rw [hident r y]
        have hcR : I2 r = (∫ y in cube L,
            ∑ k : Fin 3, (fderiv ℝ (fib r) y (euclBasis3 k)) ^ 2) := by
          dsimp [I2]
          apply integral_congr_ae
          filter_upwards with y
          -- Σ over euclBasis3 = Σ over master kcDir-terms
          calc
            (∑ k : Fin 3, (fderiv ℝ Φ (kcInsN n i (y, r)) (kcDir (n + 1) i k)) ^ 2)
                = (∑ k : Fin 3, (fderiv ℝ (fib r) y (kcStdBasis k)) ^ 2) := by
                  apply Finset.sum_congr rfl
                  intro k hk
                  congr 1
                  dsimp [fib]
                  exact (fiber_fderiv_kcDir i hΦc r y k).symm
            _ = (∑ k : Fin 3, (fderiv ℝ (fib r) y (euclBasis3 k)) ^ 2) := by
                  exact (sum_fderiv_onb_eq_coord (φ := fib r) y).symm
        have hI : I1 r ≤ (36 : ℝ) * L ^ 2 * I2 r := by
          rw [hcL, hcR]
          simpa using hc
        exact hI
      -- integrability of the peeled fibres
      have hI1_int : Integrable I1 ν := by
        exact box_peel_inner_integrable (i := i)
          (F := fun x : X (n + 1) => (sectQ L i Φ x) ^ 2) (integrableOn_sq_sectQ hL i hΦc.continuous)
      have hI2_int : Integrable I2 ν := by
        exact box_peel_inner_integrable (i := i)
          (F := fun x : X (n + 1) => ∑ k : Fin 3, (fderiv ℝ Φ x (kcDir (n + 1) i k)) ^ 2)
          (integrableOn_kinSum hL i hΦc)
      have hI2m_int : Integrable (fun r : X n => (36 : ℝ) * L ^ 2 * I2 r) ν := by
        exact (hI2_int.mul_const ((36 : ℝ) * L ^ 2)).congr (by
          filter_upwards with r
          ring)
      -- peel equalities
      have hPeelL : (∫ x in box (n + 1) L, (sectQ L i Φ x) ^ 2) = ∫ r : X n, I1 r ∂ν := by
        exact box_integral_peel (i := i)
          (F := fun x : X (n + 1) => (sectQ L i Φ x) ^ 2) (integrableOn_sq_sectQ hL i hΦc.continuous)
      have hPeelR : (∫ x in box (n + 1) L, ∑ k : Fin 3, (fderiv ℝ Φ x (kcDir (n + 1) i k)) ^ 2) =
          ∫ r : X n, I2 r ∂ν := by
        exact box_integral_peel (i := i)
          (F := fun x : X (n + 1) => ∑ k : Fin 3, (fderiv ℝ Φ x (kcDir (n + 1) i k)) ^ 2)
          (integrableOn_kinSum hL i hΦc)
      calc
        (∫ x in box (n + 1) L, (sectQ L i Φ x) ^ 2) = ∫ r : X n, I1 r ∂ν := hPeelL
        _ ≤ ∫ r : X n, ((36 : ℝ) * L ^ 2 * I2 r) ∂ν := by
              exact integral_mono_ae (μ := ν) hI1_int hI2m_int (by filter_upwards with r; exact hpt r)
        _ = (36 : ℝ) * L ^ 2 * (∫ r : X n, I2 r ∂ν) := by
              rw [MeasureTheory.integral_const_mul]
        _ = (36 : ℝ) * L ^ 2 * (∫ x in box (n + 1) L,
              ∑ k : Fin 3, (fderiv ℝ Φ x (kcDir (n + 1) i k)) ^ 2) := by
              rw [hPeelR]

end BoseGases

end Submission
