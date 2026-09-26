import Mathlib
import Submission.Work.Drive.Mono.tiltData_window_of_dir_export_axis
import Submission.Work.Drive.Mono.noGraze_witness_robust
import Submission.Work.Drive.Mono.ae_exists_goodV
import Submission.Work.Drive.Mono.NoBend
import Submission.Work.Drive.Mono.encard_tiltedCrossings_le_flat
import Submission.Work.Drive.Mono.finite_facePts_tilted
import Submission.Work.Drive.Mono.junctionGoodAux

/-!
# The data of a thin tilted sweep, with a wall functional that kills no coordinate direction

`Work.Drive.Mono.sweepData_exists_partial` is the "partial" form of the tilt-data existence
`Work.Drive.Mono.sweepGoodData_exists`: it asks for the *analytic* package (the tilt data
`TiltData`, the seven no-grazing clauses of the sweep, `SlabCutsBox`, the window containing the
`ℓ`-range of the closed box, `ℓ (e_{σ i}) ≠ 0` for the three coordinate directions, and the face
regularity), but **not** for the junction bundle `JunctionGenC` and not for `GoodSweepData2`.

## What the proof does

At almost every cut level `u` (`ae_exists_goodV_near` for the no-grazing threshold and
`ae_noBendCrossing` for the no-bend genericity) the robust no-grazing witness
`Work.Drive.Mono.noGraze_witness_robust` provides a tilt `v`, a Morse normal `n ⊥ v`, a half-width
`hw` and a radius `ρw` with the geometric clauses 2--5 at the tilt direction `v`.

The witness's own tilt `v` **cannot** be used as the answer: `TiltData` requires `ℓ v = 0` while the
conclusion requires `ℓ (e_{σ i}) ≠ 0` for all `i`, so `v` must be parallel to no coordinate axis —
which is *not* derivable from the witness's conclusion (`v = shiftVσ σ 1` is consistent with it, and
in that case no `ℓ` with `ℓ v = 0` can kill no coordinate direction).  The proof therefore perturbs
`v` by at most `εv` to a unit vector `v'` off the axes (`sweepData_axis_perturb`, with `εv` chosen
in terms of `hw`, `ρh`, `ρw`, `ε₀`, `εg` so that the perturbation stays inside the witness's
transversality ball and inside the window), pushes `n` into `(v')^⊥`
(`sweepData_orth_near`, staying within `2 εv`), and then runs the exported thin-slab band data
`Work.Drive.Mono.tiltData_window_of_dir_export_axis` at the pair `(v', n')`.  The transport of the
witness's clauses 2 and 4 to the perturbed tilt is the elementary inequality `sweepData_slab_le`;
clauses 3 and 5 come from the a.e. no-grazing statement at `v'` (which is legitimate because
`‖v' - shiftVσ σ 1‖ < εg`); the count is `encard_tiltedCrossings_le_flat`, and the exceptional set
`exc` is enlarged by the finitely many `ℓ`-values of the knot's slab-face points
(`finite_facePts_tilted`), `TiltedGenericity` being monotone in `exc`.
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set
open scoped ENNReal Topology RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-! ## Helper lemmas for `Work.Drive.Mono.sweepData_exists_partial` -/

/-- **The slab height differs from the height in another direction by the inner product with the
difference of the directions.** -/
private lemma sweepData_slab_diff (v v' x c : R3) :
    inner ℝ v x - inner ℝ v c
      = (inner ℝ v' x - inner ℝ v' c) + inner ℝ (v - v') (x - c) := by
  rw [← inner_sub_right, ← inner_sub_right, ← inner_add_left]
  congr 1
  abel

/-- **The two slab heights differ by at most `εv * R` on a ball of radius `R`.** -/
private lemma sweepData_slab_le {v v' x c : R3} {εv R u : ℝ} (h : ‖v' - v‖ ≤ εv)
    (hx : ‖x - c‖ ≤ R) :
    |inner ℝ v x - (inner ℝ v c + u)| ≤ |inner ℝ v' x - (inner ℝ v' c + u)| + εv * R := by
  have hkey : inner ℝ v x - (inner ℝ v c + u)
      = (inner ℝ v' x - (inner ℝ v' c + u)) + inner ℝ (v - v') (x - c) := by
    have h1 : inner ℝ (v - v') (x - c) = inner ℝ v (x - c) - inner ℝ v' (x - c) :=
      inner_sub_left _ _ _
    have h2 : inner ℝ v (x - c) = inner ℝ v x - inner ℝ v c := inner_sub_right _ _ _
    have h3 : inner ℝ v' (x - c) = inner ℝ v' x - inner ℝ v' c := inner_sub_right _ _ _
    rw [h1, h2, h3]
    ring
  rw [hkey]
  refine le_trans (abs_add_le _ _) ?_
  have hεv0 : 0 ≤ εv := le_trans (norm_nonneg _) h
  refine add_le_add le_rfl ?_
  calc |inner ℝ (v - v') (x - c)| ≤ ‖v - v'‖ * ‖x - c‖ := abs_real_inner_le_norm _ _
    _ = ‖v' - v‖ * ‖x - c‖ := by rw [norm_sub_rev]
    _ ≤ εv * R := mul_le_mul h hx (norm_nonneg _) hεv0

/-- **A vector with two non-zero coordinates is parallel to no coordinate axis.** -/
private theorem sweepData_ne_smul_single {v : R3} {j j' : Fin 3} (hjj : j ≠ j')
    (hj : v j ≠ 0) (hj' : v j' ≠ 0) :
    ∀ i : Fin 3, ∀ a : ℝ, EuclideanSpace.single i (1 : ℝ) ≠ a • v := by
  intro i a hcon
  have hsingle : ∀ m : Fin 3, (EuclideanSpace.single i (1 : ℝ)) m = if m = i then 1 else 0 := by
    intro m; rw [PiLp.single_apply]
  have hai : a * v i = 1 := by
    have h2 := congrArg (fun x : R3 => x i) hcon.symm
    rw [hsingle i, if_pos rfl] at h2
    simpa [PiLp.smul_apply, smul_eq_mul] using h2
  have ha0 : a ≠ 0 := fun h0 => by rw [h0, zero_mul] at hai; norm_num at hai
  have hzero : ∀ m : Fin 3, m ≠ i → v m = 0 := by
    intro m hm
    have h2 := congrArg (fun x : R3 => x m) hcon.symm
    rw [hsingle m, if_neg hm] at h2
    have h3 : a * v m = 0 := by simpa [PiLp.smul_apply, smul_eq_mul] using h2.symm
    exact (mul_eq_zero.mp h3).resolve_left ha0
  rcases eq_or_ne j i with hji | hji
  · exact hj' (hzero j' (fun hc => hjj (by rw [hji, hc])))
  · exact hj (hzero j hji)

/-- **A vector with two non-zero coordinates is not the standard axis vector `e_{σ 2}`.** -/
private theorem sweepData_ne_shiftVσ {v : R3} {σ : Equiv.Perm (Fin 3)} {j j' : Fin 3}
    (hjj : j ≠ j') (hj : v j ≠ 0) (hj' : v j' ≠ 0) : v ≠ Work.BoxShrink.shiftVσ σ 1 := by
  intro hcon
  have hsingle : ∀ m : Fin 3, (Work.BoxShrink.shiftVσ σ 1) m = if m = σ 2 then 1 else 0 := by
    intro m; rw [Work.BoxShrink.shiftVσ_apply]
  have hzero : ∀ m : Fin 3, m ≠ σ 2 → v m = 0 := by
    intro m hm
    have h2 := congrArg (fun x : R3 => x m) hcon
    rw [hsingle m, if_neg hm] at h2
    exact h2
  rcases eq_or_ne j (σ 2) with h1 | h1
  · exact hj' (hzero j' (fun hc => hjj (by rw [h1, hc])))
  · exact hj (hzero j h1)

/-- **A unit vector can be perturbed by at most `ε` to a unit vector off the coordinate axes.** -/
private theorem sweepData_axis_perturb {σ : Equiv.Perm (Fin 3)} {v : R3} (hv : ‖v‖ = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v' : R3, ‖v'‖ = 1 ∧ ‖v' - v‖ ≤ ε ∧
      (∀ i : Fin 3, ∀ a : ℝ, EuclideanSpace.single (σ i) (1 : ℝ) ≠ a • v') ∧
      v' ≠ Work.BoxShrink.shiftVσ σ 1 := by
  classical
  have hsum : ∑ i : Fin 3, (v i) ^ 2 = 1 := by
    have h1 := Work.Drive.Mono.inner_eq_sum v v
    rw [real_inner_self_eq_norm_sq, hv] at h1
    have h2 : ∑ j : Fin 3, v j * v j = ∑ j : Fin 3, (v j) ^ 2 :=
      Finset.sum_congr rfl fun j _ => by ring
    rw [h2] at h1
    simpa using h1.symm
  obtain ⟨m, hm⟩ : ∃ m : Fin 3, v m ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 : (∑ i : Fin 3, (v i) ^ 2) = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [hcon i]; ring
    rw [hsum] at h0
    norm_num at h0
  set m' : Fin 3 := if m = 0 then 1 else 0 with hm'def
  have hm'ne : m' ≠ m := by
    rw [hm'def]; split_ifs with h0
    · rw [h0]; decide
    · exact fun hc => h0 hc.symm
  set δ : ℝ := min ε 1 / 2 with hδdef
  have hδ0 : 0 < δ := by
    rw [hδdef]; exact div_pos (lt_min hε zero_lt_one) (by norm_num)
  have hδle : 2 * δ ≤ ε := by
    rw [hδdef]; have := min_le_left ε 1; linarith
  set t : ℝ := if v m' + δ = 0 then δ / 2 else δ with htdef
  have ht0 : 0 < t := by rw [htdef]; split_ifs <;> linarith
  have htle : t ≤ δ := by rw [htdef]; split_ifs <;> linarith
  have hvt : v m' + t ≠ 0 := by
    rw [htdef]; split_ifs with h1
    · linarith [hδ0]
    · exact h1
  set w : R3 := v + t • EuclideanSpace.single m' (1 : ℝ) with hwdef
  have hwm : w m = v m := by
    rw [hwdef]; simp [hm'ne]
  have hwm' : w m' = v m' + t := by rw [hwdef]; simp
  have hwne : w ≠ 0 := by
    intro h0
    have h1 := congrArg (fun x : R3 => x m) h0
    rw [hwm] at h1
    exact hm h1
  have hwv : ‖w - v‖ ≤ δ := by
    have h1 : w - v = t • EuclideanSpace.single m' (1 : ℝ) := by rw [hwdef]; abel
    rw [h1, norm_smul, PiLp.norm_single 2]
    simp only [Real.norm_eq_abs, norm_one, mul_one]
    rw [abs_of_pos ht0]
    exact htle
  have hwnorm : 0 < ‖w‖ := norm_pos_iff.mpr hwne
  have hw'm0 : ((‖w‖)⁻¹ • w) m ≠ 0 := by
    rw [PiLp.smul_apply, hwm]
    exact mul_ne_zero (inv_ne_zero (ne_of_gt hwnorm)) hm
  have hw'm1 : ((‖w‖)⁻¹ • w) m' ≠ 0 := by
    rw [PiLp.smul_apply, hwm']
    exact mul_ne_zero (inv_ne_zero (ne_of_gt hwnorm)) hvt
  refine ⟨(‖w‖)⁻¹ • w, ?_, ?_, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg w),
      inv_mul_cancel₀ (ne_of_gt hwnorm)]
  · have h1 : ‖(‖w‖)⁻¹ • w - w‖ = |1 - ‖w‖| := by
      have h0 : (‖w‖)⁻¹ • w - w = ((‖w‖)⁻¹ - 1) • w := by rw [sub_smul, one_smul]
      have hs : |((‖w‖)⁻¹ - 1) * ‖w‖| = |(‖w‖)⁻¹ - 1| * ‖w‖ := by
        rw [abs_mul, abs_of_nonneg (norm_nonneg w)]
      rw [h0, norm_smul, Real.norm_eq_abs, ← hs]
      congr 1
      rw [sub_mul, inv_mul_cancel₀ (ne_of_gt hwnorm), one_mul]
    have h2 : |1 - ‖w‖| ≤ ‖w - v‖ := by
      have h3 : |‖w‖ - ‖v‖| ≤ ‖w - v‖ := abs_norm_sub_norm_le w v
      rw [hv] at h3
      rwa [abs_sub_comm] at h3
    have h4 : ‖(‖w‖)⁻¹ • w - v‖ ≤ ‖(‖w‖)⁻¹ • w - w‖ + ‖w - v‖ := by
      have h5 : (‖w‖)⁻¹ • w - v = ((‖w‖)⁻¹ • w - w) + (w - v) := by abel
      rw [h5]; exact norm_add_le _ _
    rw [h1] at h4
    linarith [h4, h2, hwv, hδle]
  · intro i a
    exact sweepData_ne_smul_single (j := m') (j' := m) hm'ne hw'm1 hw'm0 (σ i) a
  · exact sweepData_ne_shiftVσ (j := m') (j' := m) hm'ne hw'm1 hw'm0

/-- **A unit vector orthogonal to `v` can be pushed into `(v')^⊥`, staying close to itself.** -/
private theorem sweepData_orth_near {v v' n : R3} (hv' : ‖v'‖ = 1) (hn : ‖n‖ = 1)
    (hvn : inner ℝ v n = 0) {ε : ℝ} (hv'v : ‖v' - v‖ ≤ ε) (hε : ε ≤ 1 / 4) :
    ∃ n' : R3, ‖n'‖ = 1 ∧ inner ℝ v' n' = 0 ∧ ‖n' - n‖ ≤ 2 * ε := by
  set n'' : R3 := n - (inner ℝ v' n) • v' with hn''def
  have horth : inner ℝ v' n'' = 0 := by
    rw [hn''def, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hv']
    ring
  have hclose : ‖n'' - n‖ ≤ ε := by
    have h1 : n'' - n = -((inner ℝ v' n) • v') := by rw [hn''def]; abel
    rw [h1, norm_neg, norm_smul, hv', mul_one, Real.norm_eq_abs]
    have h2 : inner ℝ v' n = inner ℝ (v' - v) n := by rw [inner_sub_left, hvn, sub_zero]
    rw [h2]
    calc |inner ℝ (v' - v) n| ≤ ‖v' - v‖ * ‖n‖ := abs_real_inner_le_norm _ _
      _ = ‖v' - v‖ := by rw [hn, mul_one]
      _ ≤ ε := hv'v
  have hpos : 0 < ‖n''‖ := by
    have h3 : ‖n - n''‖ = ‖n'' - n‖ := norm_sub_rev _ _
    have h4 : ‖n‖ - ‖n''‖ ≤ ‖n - n''‖ := (abs_le.mp (abs_norm_sub_norm_le n n'')).2
    rw [hn, h3] at h4
    linarith [h4, hclose, hε]
  refine ⟨(‖n''‖)⁻¹ • n'', ?_, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg n''),
      inv_mul_cancel₀ (ne_of_gt hpos)]
  · rw [real_inner_smul_right, horth, mul_zero]
  · have h1 : ‖(‖n''‖)⁻¹ • n'' - n''‖ = |1 - ‖n''‖| := by
      have h0 : (‖n''‖)⁻¹ • n'' - n'' = ((‖n''‖)⁻¹ - 1) • n'' := by rw [sub_smul, one_smul]
      have hs : |((‖n''‖)⁻¹ - 1) * ‖n''‖| = |(‖n''‖)⁻¹ - 1| * ‖n''‖ := by
        rw [abs_mul, abs_of_nonneg (norm_nonneg n'')]
      rw [h0, norm_smul, Real.norm_eq_abs, ← hs]
      congr 1
      rw [sub_mul, inv_mul_cancel₀ (ne_of_gt hpos), one_mul]
    have h2 : |1 - ‖n''‖| ≤ ‖n'' - n‖ := by
      have h3 : |‖n''‖ - ‖n‖| ≤ ‖n'' - n‖ := abs_norm_sub_norm_le n'' n
      rw [hn] at h3
      rwa [abs_sub_comm] at h3
    have h4 : ‖(‖n''‖)⁻¹ • n'' - n‖ ≤ ‖(‖n''‖)⁻¹ • n'' - n''‖ + ‖n'' - n‖ := by
      have h5 : (‖n''‖)⁻¹ • n'' - n = ((‖n''‖)⁻¹ • n'' - n'') + (n'' - n) := by abel
      rw [h5]; exact norm_add_le _ _
    rw [h1] at h4
    linarith [h4, h2, hclose]



theorem sweepData_exists_partial
    (ψ : Submission.Diffeo) (K : LeanEval.KnotTheory.PardonDistortion.Knot) {r s : ℝ}
    (hr : 0 < r) (hrs : r < s) (c : LeanEval.KnotTheory.PardonDistortion.R3)
    (σ : Equiv.Perm (Fin 3)) (B : ℕ) (hBG : Work.Drive.Mono.BoxGen ψ c σ s)
    (hcorner : {z : LeanEval.KnotTheory.PardonDistortion.R3 |
        z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier ∧
        ∃ i j : Fin 3, i ≠ j ∧ |z (σ i) - c (σ i)| = Submission.boxSide i * s ∧
          |z (σ j) - c (σ j)| = Submission.boxSide j * s}.Finite) :
    ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      |u| < Submission.eps * r →
      Work.Drive.Mono.CutTransverse K s c σ u →
      (∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
          deriv (fun r : ℝ => (K.curve r) (σ 2)) t = 0 →
          δ ≤ |(K.curve t) (σ 2) - (c (σ 2) + u)|) →
      ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
          K.curve t ∈ Submission.PBox s c σ ∧
          (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal) ≤ (B : ENNReal)) →
      ∃ (v : LeanEval.KnotTheory.PardonDistortion.R3) (h R : ℝ)
        (ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ) (lam0 lam1 : ℝ) (exc : Finset ℝ),
        Work.Drive.Mono.TiltData ψ s c σ u v h R ℓ exc lam0 lam1 ∧
        (∀ t : ℝ, Submission.boxNorm c σ (K.curve t) = s →
            h ≤ |inner ℝ v (K.curve t) - (inner ℝ v c + u)|) ∧
        (∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
            deriv (fun r : ℝ => inner ℝ v (K.curve r)) t = 0 →
            h ≤ |inner ℝ v (K.curve t) - (inner ℝ v c + u)|) ∧
        (∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
            |inner ℝ v (K.curve t) - (inner ℝ v c + u)| ≤ h →
            deriv (fun r : ℝ => ℓ (K.curve r)) t ≠ 0) ∧
        (∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
            |inner ℝ v (K.curve t) - (inner ℝ v c + u)| = h →
            deriv (fun r : ℝ => inner ℝ v (K.curve r)) t ≠ 0) ∧
        (∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
            |inner ℝ v (K.curve t) - (inner ℝ v c + u)| = h →
            ℓ (K.curve t) ∈ (exc : Set ℝ)) ∧
        Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
            K.curve t ∈ Submission.PBox s c σ ∧
            inner ℝ v (K.curve t) = inner ℝ v c + u} ≤ B ∧
        Work.Drive.Mono.SlabCutsBox s c σ (inner ℝ v c + u) h v ∧
        (∀ y ∈ closure (Submission.PBox s c σ), lam0 < ℓ y ∧ ℓ y < lam1) ∧
        (∀ i : Fin 3, ℓ (EuclideanSpace.single (σ i) (1 : ℝ)) ≠ 0) ∧
        (∀ z : LeanEval.KnotTheory.PardonDistortion.R3,
          z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier → z ∈ Submission.PBox s c σ →
          |inner ℝ v z - (inner ℝ v c + u)| = h →
          ∃ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z ∧
            fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0) := by
  classical
  have hs : 0 < s := lt_trans hr hrs
  have hs0 : 0 ≤ s := le_of_lt hs
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  filter_upwards [Work.Drive.Mono.ae_exists_goodV_near K hs c σ (θ := 1 / 16) (by norm_num),
      Work.Drive.Mono.ae_noBendCrossing K (Work.BoxShrink.shiftVσ σ 1) c σ s] with u hV hBnd
  intro hu hcut hflat hcount
  -- ## 1. the a.e. data of the analysis
  obtain ⟨εg, δg, hεg0, hδg0, _hεgθ, _hδgθ, hnog⟩ := hV
  obtain ⟨δf, hδf0, hδf⟩ := hflat
  obtain ⟨mbox, hmbox0, hmboxmem⟩ := Work.Drive.Mono.exists_margin_boxSphere K c σ hs hcut
  -- ## 2. the numerical constants
  set R1 : ℝ := 5 / 2 * s with hR1def
  have hR1pos : 0 < R1 := by rw [hR1def]; linarith
  have hR1b : ∀ y ∈ Submission.PBox s c σ, ‖y - c‖ ≤ R1 := by
    intro y hy; rw [hR1def]; exact Work.Drive.Mono.norm_sub_le_of_mem_PBox hs0 hy
  have hR1cl : ∀ y ∈ closure (Submission.PBox s c σ), ‖y - c‖ ≤ R1 := by
    intro y hy; rw [hR1def]; exact Work.Drive.Mono.norm_sub_le_of_mem_closure_PBox hs0 hy
  set ε₀ : ℝ := min δf (min mbox δg) / 4 with hε₀def
  have hε₀0 : 0 < ε₀ := by
    rw [hε₀def]; exact div_pos (lt_min hδf0 (lt_min hmbox0 hδg0)) (by norm_num)
  have hε₀δf : ε₀ ≤ δf := by
    rw [hε₀def]; have h := min_le_left δf (min mbox δg); linarith
  have hε₀mbox : ε₀ ≤ mbox := by
    rw [hε₀def]; have h := min_le_right δf (min mbox δg); have h2 := min_le_left mbox δg
    linarith
  have hε₀δg : ε₀ ≤ δg := by
    rw [hε₀def]; have h := min_le_right δf (min mbox δg); have h2 := min_le_right mbox δg
    linarith
  have hε₀δg4 : ε₀ ≤ δg / 4 := by
    rw [hε₀def]
    have h := min_le_right δf (min mbox δg)
    have h2 := min_le_right mbox δg
    linarith
  set θ' : ℝ := min (1 / 32) (min (εg / 4) ((ε₀ / 4) / (R1 + 1))) with hθ'def
  have hθ'0 : 0 < θ' := by
    rw [hθ'def]
    exact lt_min (by norm_num) (lt_min (by linarith) (div_pos (by linarith) (by linarith)))
  have hθ'32 : θ' ≤ 1 / 32 := by rw [hθ'def]; exact min_le_left _ _
  have hθ'εg : θ' ≤ εg / 4 := by
    rw [hθ'def]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hθ'R1 : θ' * R1 < ε₀ / 4 := by
    have h1 : θ' ≤ (ε₀ / 4) / (R1 + 1) := by
      rw [hθ'def]; exact le_trans (min_le_right _ _) (min_le_right _ _)
    have h2 : θ' * R1 ≤ ((ε₀ / 4) / (R1 + 1)) * R1 :=
      mul_le_mul_of_nonneg_right h1 (le_of_lt hR1pos)
    have h3 : ((ε₀ / 4) / (R1 + 1)) * R1 < ε₀ / 4 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith : (0 : ℝ) < R1 + 1)]
      nlinarith
    linarith
  -- ## 3. the robust no-grazing witness
  obtain ⟨v, n, hw, ρw, hv1, hn1, hvn, hgood, hθ'v, _hvεg, hhw0, hρw0, hhwsize,
    hcl1, _hcl2, hcl3, _hcl4⟩ :=
    Work.Drive.Mono.noGraze_witness_robust ψ K hr hrs hu c σ hcut hεg0 hδg0 hθ'0 hnog hBnd
  obtain ⟨ρh, hρh0, hρhgood⟩ := Work.Drive.Mono.Band.heightGood_open ψ hgood
  -- ## 4. the perturbation size
  set εv : ℝ := min (min (ε₀ / (8 * R1)) (hw / (100 * R1)))
      (min (min (ρh / 8) (ρw / 8)) (min (εg / 4) (1 / 128))) with hεvdef
  have hεva : εv ≤ ε₀ / (8 * R1) := by
    rw [hεvdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hεvb : εv ≤ hw / (100 * R1) := by
    rw [hεvdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hεvc : εv ≤ ρh / 8 := by
    rw [hεvdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hεvd : εv ≤ ρw / 8 := by
    rw [hεvdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hεve : εv ≤ εg / 4 := by
    rw [hεvdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hεvf : εv ≤ 1 / 128 := by
    rw [hεvdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hεv0 : 0 < εv := by
    rw [hεvdef]
    exact lt_min (lt_min (div_pos hε₀0 (by linarith)) (div_pos hhw0 (by linarith)))
      (lt_min (lt_min (div_pos hρh0 (by norm_num)) (div_pos hρw0 (by norm_num)))
        (lt_min (div_pos hεg0 (by norm_num)) (by norm_num)))
  have hεvε₀ : εv * R1 ≤ ε₀ / 8 := by
    have h2 : εv * R1 ≤ (ε₀ / (8 * R1)) * R1 := mul_le_mul_of_nonneg_right hεva (le_of_lt hR1pos)
    have h3 : (ε₀ / (8 * R1)) * R1 = ε₀ / 8 := by field_simp
    rwa [h3] at h2
  have hεvhw : εv * R1 ≤ hw / 100 := by
    have h2 : εv * R1 ≤ (hw / (100 * R1)) * R1 := mul_le_mul_of_nonneg_right hεvb (le_of_lt hR1pos)
    have h3 : (hw / (100 * R1)) * R1 = hw / 100 := by field_simp
    rwa [h3] at h2
  -- ## 5. the perturbed tilt and the new normal
  obtain ⟨v', hv'1, hv'v, haxis', hv'e0⟩ := sweepData_axis_perturb (σ := σ) hv1 hεv0
  have hv'e_le : ‖v' - Work.BoxShrink.shiftVσ σ 1‖ ≤ θ' + εv := by
    have h1 : v' - Work.BoxShrink.shiftVσ σ 1
        = (v' - v) + (v - Work.BoxShrink.shiftVσ σ 1) := by abel
    calc ‖v' - Work.BoxShrink.shiftVσ σ 1‖
        ≤ ‖v' - v‖ + ‖v - Work.BoxShrink.shiftVσ σ 1‖ := by
          rw [h1]; exact norm_add_le _ _
      _ ≤ εv + θ' := add_le_add hv'v hθ'v
      _ = θ' + εv := by ring
  have hv'e18 : ‖v' - Work.BoxShrink.shiftVσ σ 1‖ ≤ 1 / 8 := by
    linarith [hv'e_le, hθ'32, hεvf]
  have hv'e_eps : ‖v' - Work.BoxShrink.shiftVσ σ 1‖ < εg := by
    linarith [hv'e_le, hθ'εg, hεve, hεg0]
  obtain ⟨n', hn'1, hv'n', hn'close⟩ := sweepData_orth_near hv'1 hn1 hvn hv'v (by linarith [hεvf])
  have hgood' : Work.Drive.Mono.Band.HeightGood ψ n' :=
    hρhgood n' (by linarith [hn'close, hεvc, hρh0])
  have hn'n : ‖n' - n‖ ≤ ρw / 4 := by linarith [hn'close, hεvd, hρw0]
  -- ## 6. the window of half-widths
  set A : ℝ := ‖v' - Work.BoxShrink.shiftVσ σ 1‖ * R1 with hAdef
  have hApos : 0 < A := by
    rw [hAdef]; exact mul_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hv'e0)) hR1pos
  have hwin0 : ‖v' - Work.BoxShrink.shiftVσ σ 1‖ * (5 / 2 * s)
      < boxWidth s σ v' - |u| :=
    Work.Drive.Mono.Band.window_nondegenerate s hs σ hv'e18 hrs hu
  have hA_win : A < boxWidth s σ v' - |u| := by rw [hAdef, hR1def]; exact hwin0
  have hA_hw : A < hw - εv * R1 := by
    have h1 : ‖v' - Work.BoxShrink.shiftVσ σ 1‖ ≤ ‖v - Work.BoxShrink.shiftVσ σ 1‖ + εv := by
      have h1' : v' - Work.BoxShrink.shiftVσ σ 1
          = (v' - v) + (v - Work.BoxShrink.shiftVσ σ 1) := by abel
      calc ‖v' - Work.BoxShrink.shiftVσ σ 1‖
          ≤ ‖v' - v‖ + ‖v - Work.BoxShrink.shiftVσ σ 1‖ := by rw [h1']; exact norm_add_le _ _
        _ ≤ εv + ‖v - Work.BoxShrink.shiftVσ σ 1‖ := by linarith [hv'v]
        _ = ‖v - Work.BoxShrink.shiftVσ σ 1‖ + εv := by ring
    have h2 : A ≤ (‖v - Work.BoxShrink.shiftVσ σ 1‖ + εv) * R1 := by
      rw [hAdef]; exact mul_le_mul_of_nonneg_right h1 (le_of_lt hR1pos)
    have h3 : ‖v - Work.BoxShrink.shiftVσ σ 1‖ * R1 < hw / 2 := by
      have h4 := hhwsize
      rw [hR1def]; nlinarith
    nlinarith [h2, h3, hεvhw, hhw0, hεv0, hR1pos]
  have hA_δg : A < δg := by
    have h1 : A ≤ (θ' + εv) * R1 := by
      rw [hAdef]; exact mul_le_mul_of_nonneg_right hv'e_le (le_of_lt hR1pos)
    have h2 : (θ' + εv) * R1 = θ' * R1 + εv * R1 := by ring
    linarith [h1, h2, hθ'R1, hεvε₀, hε₀δg, hε₀0]
  set Bm : ℝ := min (hw - εv * R1) (min (boxWidth s σ v' - |u|) δg) with hBmdef
  have hBm_hw : Bm ≤ hw - εv * R1 := by rw [hBmdef]; exact min_le_left _ _
  have hBm_win : Bm ≤ boxWidth s σ v' - |u| := by
    rw [hBmdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hBm_δg : Bm ≤ δg := by
    rw [hBmdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hAB : A < Bm := lt_min hA_hw (lt_min hA_win hA_δg)
  -- ## 7. the exported thin-slab band data at the perturbed tilt
  obtain ⟨h, nf, exc₁, hAh, hhBm, hboxw, hnf_n', hnf1, hv'nf, hnf_coord, hgen₁, hfaceReg⟩ :=
    Work.Drive.Mono.tiltData_window_of_dir_export_axis ψ s c σ u A Bm (ρw / 4) v' n'
      hApos hAB hBm_win (by linarith) hv'1 hn'1 hv'n' haxis' hgood'
  have hposh : 0 < h := lt_trans hApos hAh
  have hhhw : h + εv * R1 < hw := by
    have := lt_of_lt_of_le hhBm hBm_hw
    linarith
  have hhδg : h < δg := lt_of_lt_of_le hhBm hBm_δg
  have hnfn : ‖nf - n‖ < ρw := by
    have h1 : ‖nf - n‖ ≤ ‖nf - n'‖ + ‖n' - n‖ := by
      have h2 : nf - n = (nf - n') + (n' - n) := by abel
      rw [h2]; exact norm_add_le _ _
    linarith
  -- ## 8. the face set and the enlarged exceptional set
  have hderiv_face : ∀ t : ℝ, Submission.boxNorm c σ (K.curve t) ≤ s →
      |inner ℝ v' (K.curve t) - (inner ℝ v' c + u)| = h →
      deriv (fun r : ℝ => inner ℝ v' (K.curve r)) t ≠ 0 := by
    intro t hbox hface hd
    by_cases hbs : Submission.boxNorm c σ (K.curve t) = s
    · have h1 := hcl1 t hbs
      have h2 := sweepData_slab_le (u := u) hv'v
        (hR1cl _ (Work.Step2.closedBox_subset_closure_PBox hs c σ (le_of_eq hbs)))
      have h3 : hw ≤ h + εv * R1 := by
        have h4 := le_trans h1 h2
        rwa [hface] at h4
      exact absurd hhhw (not_lt.mpr h3)
    · have hlt : Submission.boxNorm c σ (K.curve t) < s := lt_of_le_of_ne hbox hbs
      have hmem : K.curve t ∈ Submission.PBox s c σ :=
        (Submission.mem_PBox_iff s c σ (K.curve t)).mpr hlt
      have h2 := hnog v' hv'1 hv'e_eps t hmem hd
      rw [hface] at h2
      exact absurd hhδg (not_lt.mpr h2)
  have hfaceF : ({t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
      Submission.boxNorm c σ (K.curve t) ≤ s ∧
      |inner ℝ v' (K.curve t) - (inner ℝ v' c + u)| = h}).Finite :=
    Work.Drive.Mono.finite_facePts_tilted K s c σ u v' h hderiv_face
  set Fex : Finset ℝ := hfaceF.toFinset.image (fun t : ℝ => (innerSL ℝ) nf (K.curve t)) with hFexdef
  set exc : Finset ℝ := exc₁ ∪ Fex with hexcdef
  have hgen : Work.Drive.Final.TiltedGenericity ψ s c σ u v' h ((innerSL ℝ) nf) exc := by
    obtain ⟨g1, g2, g3, g4⟩ := hgen₁
    refine ⟨?_, ?_, ?_, g4⟩
    · intro lam hlam p hp1 hp2 hp3
      exact g1 lam (fun hmem => hlam (Finset.mem_union_left Fex hmem)) p hp1 hp2 hp3
    · intro lam hlam p hp1 hp2 hp3 t
      exact g2 lam (fun hmem => hlam (Finset.mem_union_left Fex hmem)) p hp1 hp2 hp3 t
    · intro p hp1 hp2 hp3
      exact ⟨(g3 p hp1 hp2 hp3).1, Finset.mem_union_left Fex (g3 p hp1 hp2 hp3).2⟩
  -- ## 9. the window bookkeeping
  set q : ℝ := |(innerSL ℝ) nf c| + ‖(innerSL ℝ) nf‖ * R1 + 1 with hqdef
  set mw : ℝ := 1 + ∑ t ∈ exc, |t| with hmwdef
  have hq1 : 1 ≤ q := by
    rw [hqdef]
    nlinarith [abs_nonneg ((innerSL ℝ) nf c), norm_nonneg ((innerSL ℝ) nf), le_of_lt hR1pos]
  have hmw1 : 1 ≤ mw := by
    rw [hmwdef]; linarith [Finset.sum_nonneg (fun t (_ : t ∈ exc) => abs_nonneg t)]
  have hℓy : ∀ y ∈ closure (Submission.PBox s c σ), |(innerSL ℝ) nf y| ≤ q - 1 := by
    intro y hy
    have h1 : ‖y - c‖ ≤ R1 := hR1cl y hy
    have h2 : (innerSL ℝ) nf y - (innerSL ℝ) nf c = (innerSL ℝ) nf (y - c) := by rw [map_sub]
    have h3 : |(innerSL ℝ) nf (y - c)| ≤ ‖(innerSL ℝ) nf‖ * ‖y - c‖ := by
      have := ContinuousLinearMap.le_opNorm ((innerSL ℝ) nf) (y - c)
      rwa [Real.norm_eq_abs] at this
    have h4 : |(innerSL ℝ) nf y| ≤ |(innerSL ℝ) nf y - (innerSL ℝ) nf c|
        + |(innerSL ℝ) nf c| := by
      have h5 : (innerSL ℝ) nf y = ((innerSL ℝ) nf y - (innerSL ℝ) nf c)
          + (innerSL ℝ) nf c := by ring
      calc |(innerSL ℝ) nf y|
          = |((innerSL ℝ) nf y - (innerSL ℝ) nf c) + (innerSL ℝ) nf c| :=
            congrArg (fun z : ℝ => |z|) h5
        _ ≤ _ := abs_add_le _ _
    rw [h2] at h4
    have h6 : ‖(innerSL ℝ) nf‖ * ‖y - c‖ ≤ ‖(innerSL ℝ) nf‖ * R1 :=
      mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    have h7 : |(innerSL ℝ) nf y| ≤ ‖(innerSL ℝ) nf‖ * R1 + |(innerSL ℝ) nf c| := by
      linarith
    rw [hqdef]
    linarith
  have hexcw : ∀ t ∈ exc, |t| ≤ mw - 1 := by
    intro t ht
    have h1 : |t| ≤ ∑ t' ∈ exc, |t'| :=
      Finset.single_le_sum (fun t' (_ : t' ∈ exc) => abs_nonneg t') ht
    rw [hmwdef]
    linarith
  -- ## 10. the clauses
  have hclause2 : ∀ t : ℝ, Submission.boxNorm c σ (K.curve t) = s →
      h ≤ |inner ℝ v' (K.curve t) - (inner ℝ v' c + u)| := by
    intro t hbs
    have h1 := hcl1 t hbs
    have h2 := sweepData_slab_le (u := u) hv'v
      (hR1cl _ (Work.Step2.closedBox_subset_closure_PBox hs c σ (le_of_eq hbs)))
    linarith [h1, h2, hhhw]
  have hclause3 : ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
      deriv (fun r : ℝ => inner ℝ v' (K.curve r)) t = 0 →
      h ≤ |inner ℝ v' (K.curve t) - (inner ℝ v' c + u)| := by
    intro t htmem hd
    have h1 := hnog v' hv'1 hv'e_eps t htmem hd
    linarith [h1, hhδg]
  have hclause4 : ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
      |inner ℝ v' (K.curve t) - (inner ℝ v' c + u)| ≤ h →
      deriv (fun r : ℝ => (innerSL ℝ) nf (K.curve r)) t ≠ 0 := by
    intro t htmem hle
    have h1 : |inner ℝ v (K.curve t) - (inner ℝ v c + u)| ≤ hw := by
      have h2 := sweepData_slab_le (u := u) hv'v (hR1b _ htmem)
      linarith [h2, hle, hhhw]
    have h3 := hcl3 nf hnf1 hnfn t htmem h1
    simpa only [innerSL_apply_apply] using h3
  have hclause5 : ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
      |inner ℝ v' (K.curve t) - (inner ℝ v' c + u)| = h →
      deriv (fun r : ℝ => inner ℝ v' (K.curve r)) t ≠ 0 := by
    intro t htmem heq hd
    have h1 := hnog v' hv'1 hv'e_eps t htmem hd
    rw [heq] at h1
    exact absurd hhδg (not_lt.mpr h1)
  have hclause6 : ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
      |inner ℝ v' (K.curve t) - (inner ℝ v' c + u)| = h →
      (innerSL ℝ) nf (K.curve t) ∈ (exc : Set ℝ) := by
    intro t htmem hface
    obtain ⟨t', ht'I, hKt', _⟩ := Work.Drive.Mono.exists_period_reduce K t
    have hKbox : K.curve t' ∈ Submission.PBox s c σ := by rw [hKt']; exact htmem
    have hlt_s : Submission.boxNorm c σ (K.curve t') < s :=
      (Submission.mem_PBox_iff s c σ (K.curve t')).mp hKbox
    have hface' : |inner ℝ v' (K.curve t') - (inner ℝ v' c + u)| = h := by
      rw [hKt']; exact hface
    rcases lt_or_eq_of_le ht'I.2 with hlt' | heq'
    · have hmem : (innerSL ℝ) nf (K.curve t) ∈ Fex := by
        rw [hFexdef, Finset.mem_image]
        refine ⟨t', ?_, ?_⟩
        · rw [hfaceF.mem_toFinset]
          exact ⟨⟨ht'I.1, hlt'⟩, le_of_lt hlt_s, hface'⟩
        · rw [hKt']
      rw [hexcdef]
      exact Finset.mem_union_right exc₁ hmem
    · have h0 : K.curve 0 = K.curve t' := by
        rw [heq']; simpa using (K.periodic 0).symm
      have hmem : (innerSL ℝ) nf (K.curve t) ∈ Fex := by
        rw [hFexdef, Finset.mem_image]
        refine ⟨0, ?_, ?_⟩
        · rw [hfaceF.mem_toFinset]
          exact ⟨⟨le_refl 0, hpi⟩, by rw [h0]; exact le_of_lt hlt_s, by rw [h0]; exact hface'⟩
        · rw [h0, hKt']
      rw [hexcdef]
      exact Finset.mem_union_right exc₁ hmem
  have hclause7 : Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
      K.curve t ∈ Submission.PBox s c σ ∧
      inner ℝ v' (K.curve t) = inner ℝ v' c + u} ≤ B := by
    refine Work.Drive.Mono.encard_tiltedCrossings_le_flat K hε₀0
      (ENat.toENNReal_le.mp hcount) ?_ ?_ ?_ ?_
    · intro t htmem
      have hconv : inner ℝ v' (K.curve t) - (inner ℝ v' c + u)
          - ((K.curve t) (σ 2) - (c (σ 2) + u))
          = inner ℝ (v' - Work.BoxShrink.shiftVσ σ 1) (K.curve t - c) := by
        rw [← Work.Drive.Mono.slabHeight_apply K c u v' t,
          ← Work.Drive.Mono.flatHeight_apply K c σ u t]
        exact Work.Drive.Mono.slabHeight_sub_flatHeight K c σ u v' t
      rw [hconv]
      have h2 : |inner ℝ (v' - Work.BoxShrink.shiftVσ σ 1) (K.curve t - c)| ≤ (θ' + εv) * R1 := by
        refine le_trans (abs_real_inner_le_norm _ _) ?_
        exact mul_le_mul hv'e_le (hR1b _ htmem) (norm_nonneg _) (by linarith [hθ'0, hεv0])
      have h3 : (θ' + εv) * R1 < ε₀ := by
        have h4 : (θ' + εv) * R1 = θ' * R1 + εv * R1 := by ring
        linarith [h4, hθ'R1, hεvε₀, hε₀0]
      linarith [h2, h3]
    · intro t htmem hd
      have h1 := hδf t htmem hd
      linarith [h1, hε₀δf]
    · intro t htbox
      have h1 := hmboxmem t htbox
      linarith [h1, hε₀mbox]
    · intro t htmem hlt hd
      have h1 := hnog v' hv'1 hv'e_eps t htmem hd
      have hsplit : inner ℝ v' (K.curve t) - (inner ℝ v' c + u)
          = ((K.curve t) (σ 2) - (c (σ 2) + u))
            + inner ℝ (v' - Work.BoxShrink.shiftVσ σ 1) (K.curve t - c) := by
        have h2 := Work.Drive.Mono.slabHeight_sub_flatHeight K c σ u v' t
        rw [Work.Drive.Mono.slabHeight_apply, Work.Drive.Mono.flatHeight_apply] at h2
        linarith
      have h3 : |inner ℝ (v' - Work.BoxShrink.shiftVσ σ 1) (K.curve t - c)| ≤ (θ' + εv) * R1 := by
        refine le_trans (abs_real_inner_le_norm _ _) ?_
        exact mul_le_mul hv'e_le (hR1b _ htmem) (norm_nonneg _) (by linarith [hθ'0, hεv0])
      have h4 : (θ' + εv) * R1 < ε₀ := by
        have h5 : (θ' + εv) * R1 = θ' * R1 + εv * R1 := by ring
        linarith [h5, hθ'R1, hεvε₀, hε₀0]
      have h6 : |inner ℝ v' (K.curve t) - (inner ℝ v' c + u)| < δg := by
        rw [hsplit]
        have h7 := abs_add_le ((K.curve t) (σ 2) - (c (σ 2) + u))
          (inner ℝ (v' - Work.BoxShrink.shiftVσ σ 1) (K.curve t - c))
        linarith [h7, h3, h4, hlt, hε₀δg4]
      exact absurd h6 (not_lt.mpr h1)
  -- ## 11. the final datum
  refine ⟨v', h, R1, (innerSL ℝ) nf, -(q + mw), q + mw, exc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · -- `TiltData`
    refine ⟨hgen, hv'1, ?_, ?_, ?_, hposh, hR1b, ?_, ?_, ?_, ?_⟩
    · intro h0
      have h1 : (innerSL ℝ) nf nf = 0 := by rw [h0]; rfl
      rw [innerSL_apply_apply, real_inner_self_eq_norm_sq, hnf1] at h1
      norm_num at h1
    · rw [innerSL_apply_apply, real_inner_comm]
      exact hv'nf
    · rw [hAdef] at hAh
      exact hAh
    · intro y hy
      have h1 := hℓy y (subset_closure hy)
      have h2 : -(q - 1) ≤ (innerSL ℝ) nf y := by
        have := neg_abs_le ((innerSL ℝ) nf y)
        linarith
      linarith
    · intro y hy
      have h1 := hℓy y (subset_closure hy)
      have h2 : (innerSL ℝ) nf y ≤ |(innerSL ℝ) nf y| := le_abs_self _
      linarith
    · linarith
    · intro t ht
      have h1 := hexcw t ht
      have h2 : -(mw - 1) ≤ t := by
        have := neg_abs_le t
        linarith
      have h3 : t ≤ mw - 1 := by
        have := le_abs_self t
        linarith
      constructor <;> linarith
  · exact hclause2
  · exact hclause3
  · exact hclause4
  · exact hclause5
  · exact hclause6
  · exact hclause7
  · exact Work.Drive.Mono.slabCutsBox_of_width hs hposh hboxw
  · intro y hy
    have h1 := hℓy y hy
    constructor
    · have h2 : -(q - 1) ≤ (innerSL ℝ) nf y := by
        have := neg_abs_le ((innerSL ℝ) nf y)
        linarith
      linarith
    · have h2 : (innerSL ℝ) nf y ≤ |(innerSL ℝ) nf y| := le_abs_self _
      linarith
  · exact hnf_coord
  · exact hfaceReg
