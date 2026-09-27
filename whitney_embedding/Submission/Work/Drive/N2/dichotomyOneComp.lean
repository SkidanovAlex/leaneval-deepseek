import Mathlib
import Submission.Work.Drive.Morse
import Submission.Work.Drive.N2.windowDatum
import Submission.Work.Drive.N2.exists_levelComponentCurves
import Submission.Work.Drive.N2C.levelCurves_ofComponentCurves
import Submission.Work.Drive.N2.flowRows_of_chartODE
import Submission.Work.Drive.N2Lead.pinSetup
import Submission.Work.Drive.N2Lead.pinFlow
import Submission.Work.Drive.N2Lead.landingWide_band
import Submission.Work.Drive.N2Lead.exists_arcLift
import Submission.Work.Drive.N2Lead.range_eq_connectedComponentIn
import Submission.Work.Drive.N2Lead.saddlePinDefs
import Submission.Work.Drive.N2Lead.saddleArcs
import Submission.Work.Drive.N2Lead.levelCurvesReparam

/-!
# Auxiliary bricks for the D2 endgame, and a guide to what is left

**This module is imported by the shadow-core attempt; its docstring is meant as a map.**  Nothing here
imports `Submission.Work.Drive.N2.levelSeparatingMap`, and its cone contains no `N2h`/`N2pc` twin, so
it is safe to import from any lane module.

## What is proved here (all axiom-clean)

* `span_lt_one_of_exists_notMem` — **the discharge of the `hspan` hypothesis of the topological core
  of the saddle-pin dichotomy** (`Work.Drive.N2Lead.isPreconnected_sdiff_arc_of_strictMonoOn`).  The
  recipe: let `x ∈ Set.range γ` be a point of the level component **outside the marked model ball**
  `Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)` (the component leaves the ball, while every arc point
  `S.arcU ηs w`, `|w| ≤ 2`, lies in it by `SaddleChart.arcU_mem_pin`); then `x ∉ α '' Icc (-u) u` and
  the lemma gives `τ u - τ (-u) < 1`.  (A witness that misses only the *open* arc is not enough: for
  `τ u - τ (-u) = 1` the open arc's image is the whole component minus the single point
  `α (-u) = α (u)`.)  See `NOTES_dichotomy_hspan_and_packet.md` §1.
* `exists_local_piece_of_cont`, `exists_cont_lift_mono` — the lift engine with *continuity* instead of
  smoothness (`Work.Drive.N2Lead.exists_continuous_arcLift` covers the same ground).
* `pin_eq_arcs_upper` — the upper-pin characterisation in the normalised chart `SaddleChart`.
* `level_noCrit` — the anchor level `f p - lam0² ηs` is critical-free when `lam0² ηs < 2 ηd`.
* `image_subset_component_of_cont` — a continuous curve in a level lies in one component.

## Where the D2 endgame stands

The target `Work.Drive.N2.levelSeparatingMap` is wired to
`Work.Drive.N2C.exists_levelSeparatingMap_of_certifiedCases` with
* the extremum provider `Work.N2C.exists_certifiedWindow_extremum` — **PROVED**;
* the saddle provider `Work.Drive.N2C.certifiedWindowSaddle_of_core` — proved modulo
  `Work.Drive.N2Lead.exists_certifiedWindow_saddle_oneComp` (the **core**) plus the dichotomy
  `Work.Drive.N2Lead.saddlePin_oneComp_or` (being finished in `N2Lead/saddlePin_split_imp_upper.lean`).

Design of record: `N2Lead/NOTES_LEAD_saddlePacket.md`; current state:
`N2Lead/NOTES_S_packet_and_arcs_DONE.md`, `N2C/NOTES_H7_ROADMAP_D2.md`,
`N2C/NOTES_H7_lowerCert_DONE.md`, `Drive/N2/NOTES_dichotomy_hspan_and_packet.md`.

The core needs, in the engine's vocabulary (`N2Lead/saddleWindow_of_packet_band_off`, PROVED):

| engine row | where it is / state |
|---|---|
| `hlev`, `hZsm`, `hZinj`, `hZimm`, `U` | `Work.Drive.N2.saddlePack` / `SaddleChart` |
| `hfootval`, `hlandFr`, `hfrU`, `hseam`, `hcolFr`, `hbig`, `hfootFrint` | `N2Lead/saddleFlowRowsWide.lean` (seven rows; the corrected statement needs `c₀ < 99/50`, take `c₀ := 39/20`) |
| `hAsm`, `hAinj`, `hAimm` | `N2Lead/saddlePacket.lean` (`packetCurves`, `packetPicture`) + `saddleMarkedCurve` |
| `hApin`, `hAoff` | **owed**: the packet assembly (design §3.2); `mobius_park_off`, `norm_sq_cE3_saddlePsi_of_band` are on disk |
| `0 ≤ θ ≤ 1` | `N2Lead/saddlePinFunction.lean` (PROVED, `θ := pinTheta D Z (99/50)`) |
| the angle `Θ` | **owed**: design §3.2 step 1 (`angleFunction_periodOne` + `exists_strictMono_extension` + the arc lifts); see `NOTES_dichotomy_hspan_and_packet.md` §3 for the sign-convention trap |
| lower certificate | **PROVED** (`N2C/lowerCert.lean`, `N2Lead/saddleLowerCertified.lean`) |
| upper certificate | **in progress** (`N2Lead/upperRegionRate{,Neg}.lean`, `N2C/polarBridgeRate.lean`, `N2C/upperPinArcs.lean`) |
| the assembly | **owed** (`N2Lead/saddleCertWindowOneCompHolder.lean`): design §5 order — `saddlePack` → `η₁` → the seven rows → the packet → `saddleWindow_of_packet_band_off` → `certifiedTransferOnLevel` + the two certificates |

-/

/-!
# The one-component dichotomy for the saddle pin

`Work.Drive.N2.oneCompOr`: for every sufficiently small `η`, at least one of the two levels
`f p ∓ 3η/2` has its *pin* (the two branches of the anchor hyperbola of the marked saddle chart,
truncated at `|Im (Z ·)²| ≤ 99/50`) on a single connected component of the level.

## The proof plan (for the proof of `oneCompOr` below)

Work in the *normalised* saddle chart `S : Work.Drive.N2Lead.SaddleChart D`
(`Work.Drive.N2Lead.saddleChart_exists`), where the level law is `f = f p + Re (Zc ·)²` on the
chart source: the anchor level `f p - lam0² ηs` carries the hyperbola `Zc² = -lam0² (ηs - I w)`
whose branches are the arcs `S.arcU`/`S.arcD`, and the upper level `f p + lam0² ηs` the hyperbola
`Zc² = lam0² (ηs + I w)` with the arcs `S.arcR`/`S.arcL`.

With `lam0 := ρ j / 8`, `ηs := (3η/2)/lam0²`, `ηb := 4ηs/3`, `δ := 1/20`, `c₀ := 39/20`,
`m := 99/50` (all numeric rows for `η ≤ min D.ηd (lam0²/40)`).

1. `pin_eq_arcs`/`pin_eq_arcs_upper`: every pin point at the anchor (resp. upper) level is
   `S.arcU`/`S.arcD` (resp. `S.arcR`/`S.arcL`) at `w` with `|w| ≤ m`.
2. Assume the anchor pin is *not* on one component.  The image of `S.arcU` (resp. `S.arcD`) over
   `Icc (-m) m` is connected and lies in the anchor level, hence in one component `K` (resp. `K₂`);
   `K ≠ K₂`.
3. `exists_levelComponentCurves` + `levelCurves_ofComponentCurves` give `L : LevelCurves f a n`;
   with `i` the index of `S.arcU 0 ∈ range (L.γ i)` one has `range (L.γ i) = K`
   (`range_eq_connectedComponentIn`).
4. The arc image lies in `range (L.γ i)` (`exists_arc_image_subset`), so the *continuous* lift
   `exists_cont_lift_mono` gives `τ` with `L.γ i (τ w) = S.arcU ηs w` for `|w| < 2`, continuous, and
   injective; it is strictly monotone on `Icc (-c₀) c₀` (`strictMonoOn_or_strictAntiOn_Icc_of_cont_inj`).
5. Connectivity: `K ∖ P` is connected, where
   `P := {x ∈ K | x ∈ modelBall (D.φ D.j) (D.ρ D.j) ∧ |(S.Zc x)²).im| < c₀ * lam0²}`.  Indeed
   `P = S.arcU '' Ioo (-c₀) c₀` (`strip_eq_arc_image`), and with `I` the complementary closed
   interval of parameters (`Icc (τ c₀) (τ (-c₀) + 1)` if `τ` is monotone, mirrored if antitone) the
   set `Sarc := (L.γ i) '' I` is connected, contains `S.arcU ηs (±c₀)` and misses `P`
   (`arc_image_misses_strip`).
6. The flow `Φ (3η, ·)` lands on the upper level at every point of `Sarc` (`landingWide_band`; the
   points of `Sarc` are box points by step 5), so the image is a connected subset of the upper level
   containing `S.arcR ηs c₀` and `S.arcL ηs (-c₀)` (`flow_arcIds`), which are therefore in one
   component.
7. The images of `S.arcR` and `S.arcL` over `Icc (-m) m` are connected in the upper level and contain
   `S.arcR ηs c₀`, `S.arcL ηs (-c₀)`, so the whole upper pin is in one component: `OnOneComponent`.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set Filter

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M] [SecondCountableTopology M]
  [CompactSpace M]

section Helpers

/-- **The local piece of the continuous lift**, with the smoothness of `α` replaced by continuity.
This is `Work.Drive.N2C.exists_local_piece_of_on` with `hα : ∀ w ∈ J, ContMDiffAt ... α w` replaced
by `hαc : ContinuousOn α J`; the proof uses the smoothness of `α` only through continuity. -/
lemma exists_local_piece_of_cont {γ α : ℝ → M} {J : Set ℝ}
    (hγsm : ContMDiff 𝓘(ℝ,ℝ) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγimm : ∀ t : ℝ, mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ t 1 ≠ 0)
    (hγper : ∀ x : ℝ, γ (x + 1) = γ x)
    (hγmod : ∀ x y : ℝ, γ x = γ y → ∃ k : ℤ, x = y + k)
    (hαc : ContinuousOn α J) (hJ : IsOpen J) (hJc : IsPreconnected J)
    (hJα : ∀ w ∈ J, α w ∈ Set.range γ) (w : ℝ) (hw : w ∈ J) (t : ℝ)
    (ht : γ t = α w) :
    ∃ (V : Set ℝ) (τ_V : ℝ → ℝ), V ⊆ J ∧ IsOpen V ∧ V.OrdConnected ∧ w ∈ V ∧
      ContinuousOn τ_V V ∧ (∀ u ∈ V, γ (τ_V u) = α u) ∧ τ_V w = t := by
  obtain ⟨U, φ, hUopen, htU, hφsm, δ, hδpos, hφ⟩ :=
    Work.Drive.N2C.exists_localPhase_of_immersed_curve γ hγsm hγimm t
  obtain ⟨W, hWopen, htW, hW⟩ :=
    Work.Drive.N2Lead.exists_local_rightInverse hγsm.continuous hγper hγmod t hδpos hφ
  have hWUopen : IsOpen (W ∩ U) := hWopen.inter hUopen
  have htWU : γ t ∈ W ∩ U := ⟨htW, htU⟩
  have hV₀open : IsOpen (α ⁻¹' (W ∩ U) ∩ J) := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    exact Filter.inter_mem
      (((hαc.continuousAt (hJ.mem_nhds hx.2)).preimage_mem_nhds (hWUopen.mem_nhds hx.1)))
      (hJ.mem_nhds hx.2)
  have hwV₀ : w ∈ α ⁻¹' (W ∩ U) ∩ J := ⟨by change α w ∈ W ∩ U; rw [← ht]; exact htWU, hw⟩
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.isOpen_iff.mp hV₀open w hwV₀
  refine ⟨J ∩ Ioo (w - ε) (w + ε), fun u => φ (α u), inter_subset_left, hJ.inter isOpen_Ioo,
    ?_, ⟨hw, by rw [mem_Ioo]; exact ⟨by linarith, by linarith⟩⟩, ?_, ?_, ?_⟩
  · exact (convex_iff_ordConnected.mpr hJc.ordConnected).ordConnected.inter
      (convex_Ioo _ _).ordConnected
  · refine ContinuousOn.comp (t := W ∩ U) (hφsm.continuousOn.mono inter_subset_right) ?_
      (fun u hu => ?_)
    · intro u hu
      exact (hαc.continuousAt (hJ.mem_nhds hu.1)).continuousWithinAt
    · have hu' : u ∈ Metric.ball w ε := by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        exact ⟨by linarith [(mem_Ioo.mp hu.2).1], by linarith [(mem_Ioo.mp hu.2).2]⟩
      exact Set.mem_preimage.mp (hεsub hu').1
  · intro u hu
    have hu' : u ∈ Metric.ball w ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [(mem_Ioo.mp hu.2).1], by linarith [(mem_Ioo.mp hu.2).2]⟩
    have huW : α u ∈ W := (Set.mem_preimage.mp (hεsub hu').1).1
    exact hW (α u) huW (hJα u hu.1)
  · change φ (α w) = t
    rw [← ht]
    exact hφ t ⟨by linarith [hδpos], by linarith [hδpos]⟩

/-- **The continuous lift of a continuous injective curve into a component of a level curve**,
together with the injectivity of the lift (which yields strict monotonicity on any interval). -/
lemma exists_cont_lift_mono {γ α : ℝ → M} {J : Set ℝ}
    (hγsm : ContMDiff 𝓘(ℝ,ℝ) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγimm : ∀ t : ℝ, mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ t 1 ≠ 0)
    (hγper : ∀ x : ℝ, γ (x + 1) = γ x)
    (hγmod : ∀ x y : ℝ, γ x = γ y → ∃ k : ℤ, x = y + k)
    (hαc : ContinuousOn α J) (hJ : IsOpen J) (hJc : IsPreconnected J)
    (hJα : ∀ w ∈ J, α w ∈ Set.range γ)
    (hαinj : ∀ w ∈ J, ∀ w' ∈ J, α w = α w' → w = w') :
    ∃ τ : ℝ → ℝ, ContinuousOn τ J ∧ (∀ w ∈ J, γ (τ w) = α w) ∧
      (∀ w ∈ J, ∀ w' ∈ J, τ w = τ w' → w = w') := by
  have hpiece : ∀ (w : ℝ) (hw : w ∈ J) (t : ℝ), γ t = α w →
      ∃ (V : Set ℝ) (τ_V : ℝ → ℝ), V ⊆ J ∧ IsOpen V ∧ V.OrdConnected ∧ w ∈ V ∧
        ContinuousOn τ_V V ∧ (∀ u ∈ V, γ (τ_V u) = α u) ∧ τ_V w = t :=
    fun w hw t ht => exists_local_piece_of_cont hγsm hγimm hγper hγmod hαc hJ hJc hJα w hw t ht
  obtain ⟨τ, hτc, hτγ⟩ :=
    Work.Drive.N2Lead.exists_continuous_lift hJ hJc hJα hγmod hγper hpiece
  refine ⟨τ, hτc, hτγ, ?_⟩
  intro w hw w' hw' h
  exact hαinj w hw w' hw' (by rw [← hτγ w hw, ← hτγ w' hw', h])

/-- A continuous injective function on a closed interval is strictly monotone or strictly antitone. -/
lemma strictMonoOn_or_strictAntiOn_Icc_of_cont_inj {τ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn τ (Icc a b)) (hi : Set.InjOn τ (Icc a b)) :
    StrictMonoOn τ (Icc a b) ∨ StrictAntiOn τ (Icc a b) :=
  ContinuousOn.strictMonoOn_of_injOn_Icc' hab hc hi

end Helpers

section MoreHelpers

/-- **The upper pin characterisation** (the counterpart of `Work.Drive.N2Lead.SaddleChart.pin_eq_arcs`):
every point of the pin at the *upper* level `f p + lam0² ηs` is one of the two upper arc points
`S.arcR ηs w`, `S.arcL ηs w`. -/
lemma pin_eq_arcs_upper {f : M → ℝ} {p : M} {D : WindowDatum f p}
    (S : Work.Drive.N2Lead.SaddleChart D) {ηs m : ℝ}
    (hηs : 0 < ηs) (hηs1 : ηs ≤ 1) (hm0 : 0 ≤ m) (hm2 : m ≤ 2)
    {x : M} (hx : x ∈ Work.Drive.N2Lead.saddlePin D (f p + (D.ρ D.j / 8) ^ 2 * ηs) m) :
    ∃ w : ℝ, |w| ≤ m ∧ (x = S.arcR ηs w ∨ x = S.arcL ηs w) := by
  obtain ⟨hsrc, hn, hv, him⟩ := hx
  have hlam0 : 0 < D.ρ D.j / 8 := by
    have := D.hρ D.j; positivity
  have hsrc' : x ∈ S.φ'.source := by rw [S.source_eq]; exact hsrc
  have hre : ((S.Zc x) ^ 2).re = (D.ρ D.j / 8) ^ 2 * ηs := by
    have h := S.level_eq x hsrc'
    rw [hv] at h
    linarith
  have himle : |((S.Zc x) ^ 2).im| ≤ m * (D.ρ D.j / 8) ^ 2 := by
    rw [S.Zc_sq_im_abs hsrc']
    exact him
  set w : ℝ := ((S.Zc x) ^ 2).im / (D.ρ D.j / 8) ^ 2 with hwdef
  have hw2 : |w| ≤ m := by
    rw [hwdef, abs_div, abs_of_pos (show (0:ℝ) < (D.ρ D.j / 8) ^ 2 by positivity),
      div_le_iff₀ (show (0:ℝ) < (D.ρ D.j / 8) ^ 2 by positivity)]
    linarith [himle]
  have hwabs : |w| ≤ 2 := le_trans hw2 hm2
  refine ⟨w, hw2, ?_⟩
  have hlamC : ((D.ρ D.j / 8 : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt hlam0
  have hwne : ((D.ρ D.j / 8 : ℝ)) ^ 2 ≠ 0 := by positivity
  have hwim : ((S.Zc x) ^ 2).im = (D.ρ D.j / 8) ^ 2 * w := by
    rw [hwdef]
    exact (mul_div_cancel₀ _ (show ((D.ρ D.j / 8 : ℝ)) ^ 2 ≠ 0 by positivity)).symm
  have hsq : (S.Zc x) ^ 2
      = (((D.ρ D.j / 8 : ℝ) : ℂ) * Complex.sqrt ((ηs : ℂ) + (w : ℂ) * Complex.I)) ^ 2 := by
    rw [mul_pow, Work.Drive.N2Lead.complex_sqrt_sq', ← Complex.ofReal_pow]
    refine Complex.ext ?_ ?_
    · rw [hre, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, mul_one, sub_zero]
      ring
    · rw [hwim, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_im,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_one, mul_zero, add_zero]
      ring
  have hR : S.Zc (S.arcR ηs w) = ((D.ρ D.j / 8 : ℝ) : ℂ)
      * Complex.sqrt ((ηs : ℂ) + (w : ℂ) * Complex.I) :=
    S.arcR_Zc hηs.le hηs1 hwabs
  have hL : S.Zc (S.arcL ηs w) = -(((D.ρ D.j / 8 : ℝ) : ℂ)
      * Complex.sqrt ((ηs : ℂ) + (w : ℂ) * Complex.I)) := by
    rw [S.arcL_Zc hηs.le hηs1 hwabs]; ring
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exact Or.inl (S.injOn_Zc hsrc' (S.arcR_source hηs.le hηs1 hwabs)
      (by rw [hR]; exact h))
  · exact Or.inr (S.injOn_Zc hsrc' (S.arcL_source hηs.le hηs1 hwabs)
      (by rw [hL]; exact h))

/-- The image of a continuous curve lying in a level is contained in one component of that level. -/
lemma image_subset_component_of_cont {f : M → ℝ} {α : ℝ → M} {m v : ℝ}
    (hm0 : 0 ≤ m) (hαc : ContinuousOn α (Icc (-m) m))
    (hαv : ∀ w ∈ Icc (-m) m, f (α w) = v) :
    ∀ w ∈ Icc (-m) m, α w ∈ connectedComponentIn {z : M | f z = v} (α 0) := by
  have h0 : (0 : ℝ) ∈ Icc (-m) m := ⟨by linarith, by linarith⟩
  have himg : IsPreconnected (α '' Icc (-m) m) := isPreconnected_Icc.image α hαc
  have hsub : α '' Icc (-m) m ⊆ {z : M | f z = v} := by
    rintro _ ⟨w, hw, rfl⟩
    exact hαv w hw
  intro w hw
  exact himg.subset_connectedComponentIn ⟨0, h0, rfl⟩ hsub ⟨w, hw, rfl⟩

/-- **The anchor level is critical-free.**  For a value at distance `lam0² ηs` below `f p` with
`lam0² ηs < 2 ηd` there is no critical point on the level (the separation `hsep` excludes all other
critical points, and the marked one has the value `f p ≠ f p - lam0² ηs`). -/
lemma level_noCrit {f : M → ℝ} {p : M} (D : WindowDatum f p) {ηs : ℝ}
    (hηs : 0 < ηs) (hsmall : (D.ρ D.j / 8) ^ 2 * ηs < 2 * D.ηd) :
    ∀ x : M, f x = f p - (D.ρ D.j / 8) ^ 2 * ηs → ¬ Work.Drive.Morse.IsCritical f x := by
  intro x hx hc
  obtain ⟨i, hi⟩ := D.hcover x hc
  have hlam : 0 < D.ρ D.j / 8 := by
    have := D.hρ D.j; positivity
  rcases eq_or_ne i D.j with rfl | hne
  · have hp : p = x := by rw [← D.hxj]; exact hi
    have hfx : f x = f p := by rw [← hp]
    rw [hfx] at hx
    have h0 : (D.ρ D.j / 8) ^ 2 * ηs = 0 := by linarith [hx]
    have := mul_pos (pow_pos hlam 2) hηs
    linarith
  · have h := D.hsep i D.j hne
    rw [hi, D.hxj, hx] at h
    have : |f p - (D.ρ D.j / 8) ^ 2 * ηs - f p| = (D.ρ D.j / 8) ^ 2 * ηs := by
      rw [show f p - (D.ρ D.j / 8) ^ 2 * ηs - f p = -((D.ρ D.j / 8) ^ 2 * ηs) by ring,
        abs_neg, abs_of_pos (by positivity)]
    rw [this] at h
    linarith

end MoreHelpers

section Span

/-- **The parameter span of a lift is `< 1`.**  If the image of a strictly monotone lift `τ` of an arc
`α` on `Icc (-u) u` misses a point of `Set.range γ` entirely (in the D2 applications: the arc's image
lies in the marked model ball of radius `ρ j`, while the connected component `range γ` of the level
leaves that ball), then `τ u - τ (-u) < 1`.

This is the hypothesis `hspan` of
`Work.Drive.N2Lead.isPreconnected_sdiff_arc_of_strictMonoOn` (the topological core of the saddle-pin
dichotomy `Work.Drive.N2Lead.saddlePin_split_imp_upper`).

*Proof.*  Suppose `τ u - τ (-u) ≥ 1` and let `x = γ t` miss the closed arc.  Then
`θ := τ (-u) + fract (t - τ (-u))` satisfies `τ (-u) ≤ θ < τ (-u) + 1 ≤ τ u` and `γ θ = γ t`.
If `θ = τ (-u)` then `γ t = α (-u)`; otherwise `θ ∈ Ioo (τ (-u)) (τ u)` and the intermediate value
theorem on `Icc (-u) u` (with `τ` monotone) produces `w ∈ Ioo (-u) u` with `τ w = θ`, so
`γ t = γ (τ w) = α w`.  Either way `γ t` lies in the *closed* arc `α '' Icc (-u) u`, a contradiction. -/
lemma span_lt_one_of_exists_notMem {γ α : ℝ → M} {τ : ℝ → ℝ} {u : ℝ}
    (hγper : ∀ x : ℝ, γ (x + 1) = γ x)
    (hγα : ∀ w ∈ Icc (-u) u, γ (τ w) = α w)
    (hτc : ContinuousOn τ (Icc (-u) u)) (hmono : StrictMonoOn τ (Icc (-u) u)) (hu : 0 < u)
    (hx : ∃ x ∈ Set.range γ, x ∉ α '' Icc (-u) u) :
    τ u - τ (-u) < 1 := by
  obtain ⟨x, ⟨t, rfl⟩, hxnot⟩ := hx
  by_contra hcon
  push_neg at hcon
  have hule : -u ≤ u := le_of_lt (by linarith)
  set θ : ℝ := τ (-u) + Int.fract (t - τ (-u)) with hθdef
  have hθ1 : τ (-u) ≤ θ := by
    rw [hθdef]; have := Int.fract_nonneg (t - τ (-u)); linarith
  have hθ2 : θ < τ (-u) + 1 := by
    rw [hθdef]; have := Int.fract_lt_one (t - τ (-u)); linarith
  have hγθ : γ θ = γ t := by
    have hkey : θ = t + (-(⌊t - τ (-u)⌋ : ℤ) : ℝ) := by
      rw [hθdef, Int.fract]; push_cast; ring
    rw [hkey]
    simpa using Work.Drive.N2Lead.eq_of_add_intCast_of_periodic hγper t (-(⌊t - τ (-u)⌋ : ℤ))
  have hθlt : θ < τ u := lt_of_lt_of_le hθ2 (by linarith)
  have F2 : ∀ θ' ∈ Ioo (τ (-u)) (τ u), ∃ w ∈ Ioo (-u) u, τ w = θ' := by
    intro θ' hθ'
    obtain ⟨w, hw, hwθ⟩ := intermediate_value_Icc hule hτc
      (show τ (-u) ≤ θ' ∧ θ' ≤ τ u from ⟨le_of_lt hθ'.1, le_of_lt hθ'.2⟩)
    have hw2 : w ∈ Ioo (-u) u := by
      constructor
      · by_contra hc
        push_neg at hc
        have hwe : w = -u := le_antisymm hc hw.1
        rw [hwe] at hwθ
        linarith [hwθ, hθ'.1]
      · by_contra hc
        push_neg at hc
        have hwe : w = u := le_antisymm hw.2 hc
        rw [hwe] at hwθ
        linarith [hwθ, hθ'.2]
    exact ⟨w, hw2, hwθ⟩
  have hmem : γ t ∈ α '' Icc (-u) u := by
    rcases eq_or_lt_of_le hθ1 with heq | hlt
    · refine ⟨-u, ⟨le_rfl, hule⟩, ?_⟩
      rw [← hγα (-u) ⟨le_rfl, hule⟩]
      rw [← hγθ, heq]
    · obtain ⟨w, hw, hwθ⟩ := F2 θ ⟨hlt, hθlt⟩
      exact ⟨w, ⟨le_of_lt hw.1, le_of_lt hw.2⟩,
        by rw [← hγα w ⟨le_of_lt hw.1, le_of_lt hw.2⟩, hwθ, hγθ]⟩
  exact hxnot hmem

end Span

end Work.Drive.N2
