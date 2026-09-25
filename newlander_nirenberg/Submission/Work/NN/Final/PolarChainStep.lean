/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The one-step estimate for the radial extension, in a clash-free dependency closure

This is a verbatim copy of `Submission/Work/NN/Final/radialExt_holderNorm_est_step.lean` with the
two changes that the Seeley region estimate is taken from `PolarChainSeeley.lean` (which belongs to
the `flatOneSidedExtension` dependency closure) and the main theorem is renamed
`radialExt_holderNorm_est_stepNG`.  See `PolarChainSeeley.lean` for the reason (the clash between
the duplicated gluing lemma of `SeeleyLoc_glue.lean` and that of `flatOneSidedExtension.lean`).
-/
import Mathlib
import Submission.Work.NN.Final.PolarDefs
import Submission.Work.NN.Final.PolarRegions
import Submission.Work.NN.Final.PolarGlob
import Submission.Work.NN.Final.HolderCongr
import Submission.Work.NN.Final.radialExt_seeleyExt_flat
import Submission.Work.NN.Final.holderNorm_comp_polarChart
import Submission.Work.NN.Final.holderNorm_comp_flatPoint
import Submission.Work.NN.Final.holderNorm_union_le_of_separated
import Submission.Work.NN.Final.PolarChainSeeley

/-!
# The `C^{k,α}` estimate for one step of the polar (iterated radial) Seeley extension

`radialExt n ρ a b j G` is the one-coordinate radial reflection extension in the `j`-th
coordinate: it agrees with `G` on the region `inRegion n ρ j` (where `‖z j‖ < ρ j`) and on the
annulus `ρ j ≤ ‖z j‖ < 2 ρ j` it is the flat Seeley extension evaluated in the logarithmic chart
(`radialExt_seeleyExt_flat`).  This file proves the accompanying `C^{k,α}` estimate: the
`C^{k,α}`-Hölder norm of `radialExt n ρ a b j G` on the outer region `outRegion n ρ j` is bounded
by a constant times the norm of `G` on the inner region `inRegion n ρ j`, for a `G` which is
`C^k` (one-sidedly on the faces `‖z i‖ = ρ i`, `i ≤ j`) on `oneSidedRegion n ρ (j : ℕ)`.

The proof decomposes `outRegion n ρ j` into the two *open* pieces

* `inRegion n ρ j` (where `radialExt = G`), and
* `outRegion n ρ j ∩ {z | ρ j / 2 < ‖z j‖}` (an annulus on which `z j ≠ 0`, so that
  `radialExt = seeleyExt a b (flatPull n ρ j G) ∘ polarChart n ρ j`),

which are at distance `≥ ρ j / 2` from one another outside their intersection; the union lemma
`holderNorm_union_le_of_separated` combines the two estimates.  On the annulus one transports the
estimates of `seeleyRegionEstimate` (flat Seeley extension on a slab) and
`holderNorm_comp_polarChart`/`holderNorm_comp_flatPoint` (composition with the logarithmic chart
and with the fibre map `flatPoint`) along the identity `radialExt = seeleyExt ∘ polarChart`.

The auxiliary statement `radialExt_holderNorm_est_step_aux` isolates the argument from the flat
Seeley estimate `seeleyRegionEstimate`, which is applied at the very end.
-/

noncomputable section
open scoped NNReal ENNReal ContDiff Topology
open Set Filter

namespace Work.NN.Final

/-! ## Helper lemmas for the one-coordinate Hölder estimate -/

lemma radialEst_flatGlob_eq_flatPoint {n : ℕ} {ρ : Fin n → ℝ} {j : Fin n} {ε : ℝ} (hε : 0 < ε)
    {p : (Fin n → ℂ) × ℝ} (hp : p.1 ∈ flatRegion n ρ j ε) :
    flatGlob n ρ j ε p = flatPoint n ρ j p := by
  rw [mem_flatRegion] at hp
  obtain ⟨h1, ⟨hεw, hw3⟩, h3⟩ := hp
  rw [flatGlob, flatPoint]
  congr 1
  have hstep : radialStep ((3 * ε) / 8) ((3 * ε) / 3) ‖p.1 j‖ = 1 := by
    refine radialStep_of_ge (by linarith) ?_
    linarith
  rw [ChartComp.u0, hstep, Complex.ofReal_one, one_mul, ChartComp.dirn, Complex.ofReal_div]
  ring

lemma radialEst_contDiffOn_flatPoint {n : ℕ} {ρ : Fin n → ℝ} {j : Fin n} {ε : ℝ} (hε : 0 < ε)
    (k : ℕ) :
    ContDiffOn ℝ (k : WithTop ENat) (flatPoint n ρ j)
      (flatRegion n ρ j ε ×ˢ {t : ℝ | 0 ≤ t}) := by
  have h1 : ContDiffOn ℝ (k : WithTop ENat) (flatGlob n ρ j ε)
      (flatRegion n ρ j ε ×ˢ {t : ℝ | 0 ≤ t}) :=
    (contDiff_flatGlob (n := n) (ρ := ρ) (j := j) hε).contDiffOn.of_le
      (ChartComp.natCast_le_top_nat k)
  exact h1.congr (fun p hp => (radialEst_flatGlob_eq_flatPoint hε hp.1).symm)

lemma radialEst_mapsTo_flatPoint {n : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i) (j : Fin n) {ε : ℝ}
    (hε : 0 < ε) :
    Set.MapsTo (flatPoint n ρ j) (flatRegion n ρ j ε ×ˢ {t : ℝ | 0 ≤ t})
      (oneSidedRegion n ρ (j : ℕ)) := by
  intro p hp
  obtain ⟨hpw, hpt⟩ := Set.mem_prod.mp hp
  rw [mem_flatRegion] at hpw
  obtain ⟨h1, ⟨hεw, hw3⟩, h3⟩ := hpw
  rw [mem_oneSidedRegion]
  constructor
  · intro i hi
    rcases eq_or_lt_of_le hi with heq | hlt
    · have hji : i = j := Fin.ext heq
      rw [hji, flatPoint, Function.update_self]
      have hwpos : 0 < ‖p.1 j‖ := lt_trans hε hεw
      have hnorm : ‖((ρ j * Real.exp (-p.2) / ‖p.1 j‖ : ℝ) : ℂ) * p.1 j‖
          = ρ j * Real.exp (-p.2) := by
        rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div,
          abs_of_pos (mul_pos (hρ j) (Real.exp_pos _)), abs_of_pos hwpos,
          div_mul_cancel₀ _ (ne_of_gt hwpos)]
      rw [hnorm]
      have hpt' : (0:ℝ) ≤ p.2 := hpt
      have hexp : Real.exp (-p.2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      nlinarith [hρ j, Real.exp_pos (-p.2)]
    · rw [flatPoint, Function.update_apply,
        if_neg (fun (h : i = j) => (ne_of_lt hlt) (congrArg Fin.val h))]
      exact le_of_lt (h1 i (by simpa using hlt))
  · intro i hi
    rw [flatPoint, Function.update_apply,
      if_neg (fun (h : i = j) => (ne_of_lt hi) (congrArg Fin.val h).symm)]
    exact h3 i (by simpa using hi)

lemma radialEst_contDiffOn_union_of_isOpen {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {A B : Set X} (hA : IsOpen A) (hB : IsOpen B) {f : X → ℂ} {n : WithTop ℕ∞}
    (h1 : ContDiffOn ℝ n f A) (h2 : ContDiffOn ℝ n f B) : ContDiffOn ℝ n f (A ∪ B) := by
  intro x hx
  rcases hx with hx | hx
  · refine (h1 x hx).congr_set ?_
    filter_upwards [hA.mem_nhds hx] with y hy
    exact propext ⟨fun h => Or.inl h, fun h => h.elim id (fun _ => hy)⟩
  · refine (h2 x hx).congr_set ?_
    filter_upwards [hB.mem_nhds hx] with y hy
    exact propext ⟨fun h => Or.inr h, fun h => h.elim (fun _ => hy) id⟩

lemma radialEst_inRegion_subset_oneSidedRegion {n : ℕ} {ρ : Fin n → ℝ} {j : Fin n} :
    inRegion n ρ j ⊆ oneSidedRegion n ρ (j : ℕ) := by
  intro z hz
  rw [mem_inRegion] at hz
  obtain ⟨h1, hj, h3⟩ := hz
  rw [mem_oneSidedRegion]
  refine ⟨fun i hi => ?_, fun i hi => h3 i (by simpa using hi)⟩
  rcases eq_or_lt_of_le hi with heq | hlt
  · have hji : i = j := Fin.ext heq
    rw [hji]; exact le_of_lt hj
  · exact le_of_lt (h1 i (by simpa using hlt))

lemma radialEst_contDiffOn_polarChart {n : ℕ} {ρ : Fin n → ℝ} {j : Fin n} {ε : ℝ} (hε : 0 < ε)
    (hρj : 0 < ρ j) (k : ℕ) :
    ContDiffOn ℝ (k : WithTop ENat) (polarChart n ρ j)
      (outRegion n ρ j ∩ {z : Fin n → ℂ | ε < ‖z j‖}) := by
  have h1 : ContDiffOn ℝ (k : WithTop ENat) (polarGlob n ρ j ε)
      (outRegion n ρ j ∩ {z : Fin n → ℂ | ε < ‖z j‖}) :=
    (contDiff_polarGlob (n := n) (ρ := ρ) (j := j) hε).contDiffOn.of_le
      (ChartComp.natCast_le_top_nat k)
  refine h1.congr (fun z hz => ?_)
  exact (polarGlob_eq_polarChart hε hρj (le_of_lt hz.2)).symm

lemma radialEst_mapsTo_polarChart {n : ℕ} {ρ : Fin n → ℝ} {j : Fin n} {ε : ℝ} (hε : 0 < ε)
    (hρj : 0 < ρ j) :
    Set.MapsTo (polarChart n ρ j) (outRegion n ρ j ∩ {z : Fin n → ℂ | ε < ‖z j‖})
      (flatRegion n ρ j ε ×ˢ {t : ℝ | -(1:ℝ) < t}) := by
  intro z hz
  obtain ⟨hzout, hzj⟩ := hz
  rw [mem_outRegion] at hzout
  obtain ⟨h1, h2, h3⟩ := hzout
  have hr : 0 < ‖z j‖ := lt_trans hε hzj
  refine Set.mem_prod.mpr ⟨?_, ?_⟩
  · show z ∈ flatRegion n ρ j ε
    rw [mem_flatRegion]
    exact ⟨h1, ⟨hzj, by linarith⟩, h3⟩
  · show -(1:ℝ) < Real.log (ρ j / ‖z j‖)
    have hdown : ρ j / ‖z j‖ > 1 / 2 := by
      rw [gt_iff_lt, lt_div_iff₀ hr]
      linarith
    have hl : Real.log ((1:ℝ) / 2) < Real.log (ρ j / ‖z j‖) :=
      Real.log_lt_log (by norm_num) hdown
    have hinv : Real.log ((1:ℝ) / 2) = -Real.log 2 := by
      rw [show ((1:ℝ) / 2) = (2:ℝ)⁻¹ by norm_num, Real.log_inv]
    have h2' : Real.log 2 < 1 := by
      have := Real.log_lt_sub_one_of_pos (show (0:ℝ) < 2 by norm_num) (by norm_num)
      linarith
    linarith

lemma radialEst_ofReal_algebra (c1 c2 c3 c4 : ℝ) (h1 : 0 ≤ c1) (h2 : 0 ≤ c2) (h3 : 0 ≤ c3)
    (h4 : 0 ≤ c4) (N : ℝ≥0∞) :
    ENNReal.ofReal c1 * (N + ENNReal.ofReal c2 * (ENNReal.ofReal c3 * (ENNReal.ofReal c4 * N)))
      = ENNReal.ofReal (c1 * (1 + (c2 * c3) * c4)) * N := by
  have h23 : 0 ≤ c2 * c3 := mul_nonneg h2 h3
  have h234 : 0 ≤ (c2 * c3) * c4 := mul_nonneg h23 h4
  rw [show ENNReal.ofReal c2 * (ENNReal.ofReal c3 * (ENNReal.ofReal c4 * N))
      = (ENNReal.ofReal c2 * ENNReal.ofReal c3) * (ENNReal.ofReal c4 * N) from by ring]
  rw [← ENNReal.ofReal_mul h2, ← mul_assoc, ← ENNReal.ofReal_mul h23]
  rw [show N + ENNReal.ofReal ((c2 * c3) * c4) * N
      = (1 + ENNReal.ofReal ((c2 * c3) * c4)) * N from by ring]
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one h234]
  rw [← mul_assoc, ← ENNReal.ofReal_mul h1]


/-! ## The auxiliary form of the one-step estimate -/

theorem radialExt_holderNorm_est_step_auxNG {n : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) {a b : ℕ → ℝ} (hb : ∀ m, 2 ≤ b m)
    (hbT : Filter.Tendsto b Filter.atTop Filter.atTop)
    (ha : ∀ j : ℕ, ∑' m, a m * (-(b m)) ^ j = 1)
    (hsum : ∀ j : ℕ, Summable fun m => |a m| * (b m) ^ j)
    (C0 : ℕ → ℝ) (hC00 : ∀ k, 0 < C0 k)
    (hC0 : ∀ (k : ℕ) (δ : ℝ), 0 < δ → ∀ (W : Set (Fin n → ℂ)) (g : (Fin n → ℂ) × ℝ → ℂ),
      IsOpen W →
      ContDiffOn ℝ (k : WithTop ENat) g (W ×ˢ {t : ℝ | 0 ≤ t}) →
      Work.CR.Flat.holderNorm k α g (W ×ˢ {t : ℝ | 0 < t}) ≠ ⊤ →
      ContDiffOn ℝ (k : WithTop ENat) (seeleyExt a b g) (W ×ˢ {t : ℝ | -δ < t}) ∧
      Work.CR.Flat.holderNorm k α (seeleyExt a b g) (W ×ˢ {t : ℝ | -δ < t})
        ≤ ENNReal.ofReal (C0 k) * Work.CR.Flat.holderNorm k α g (W ×ˢ {t : ℝ | 0 < t})) :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧
      ∀ (k : ℕ) (j : Fin n) (G : (Fin n → ℂ) → ℂ),
        ContDiffOn ℝ (k : WithTop ENat) G (oneSidedRegion n ρ (j : ℕ)) →
        Work.CR.Flat.holderNorm k α G (inRegion n ρ j) ≠ ⊤ →
        Work.CR.Flat.holderNorm k α (radialExt n ρ a b j G) (outRegion n ρ j)
          ≤ ENNReal.ofReal (C k) * Work.CR.Flat.holderNorm k α G (inRegion n ρ j) := by
  classical
  have hCfex : ∀ j : Fin n, ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧
      ∀ (k : ℕ) (G : (Fin n → ℂ) → ℂ),
        ContDiffOn ℝ (k : WithTop ENat) G (inRegion n ρ j) →
        Work.CR.Flat.holderNorm k α (flatPull n ρ j G)
            (flatRegion n ρ j (ρ j / 2) ×ˢ {t : ℝ | 0 < t})
          ≤ ENNReal.ofReal (C k) * Work.CR.Flat.holderNorm k α G (inRegion n ρ j) :=
    fun j => holderNorm_comp_flatPoint (n := n) (ρ := ρ) hρ hα0 hα1 j
      (ε := ρ j / 2) (by linarith [hρ j]) (by linarith [hρ j])
  choose Cf hCf0 hCf using hCfex
  have hCpex : ∀ j : Fin n, ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧
      ∀ (k : ℕ) (u : (Fin n → ℂ) × ℝ → ℂ),
        ContDiffOn ℝ (k : WithTop ENat) u (flatRegion n ρ j (ρ j / 2) ×ˢ {t : ℝ | -(1:ℝ) < t}) →
        Work.CR.Flat.holderNorm k α (fun z => u (polarChart n ρ j z))
            (outRegion n ρ j ∩ {z : Fin n → ℂ | ρ j / 2 < ‖z j‖})
          ≤ ENNReal.ofReal (C k) *
            Work.CR.Flat.holderNorm k α u (flatRegion n ρ j (ρ j / 2) ×ˢ {t : ℝ | -(1:ℝ) < t}) :=
    fun j => holderNorm_comp_polarChart (n := n) (ρ := ρ) hρ hα0 hα1 j
      (ε := ρ j / 2) (by linarith [hρ j]) (by linarith [hρ j])
  choose Cp hCp0 hCp using hCpex
  have hCuex : ∀ j : Fin n, ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧
      ∀ (k : ℕ) (f : (Fin n → ℂ) → ℂ) (A B : Set (Fin n → ℂ)),
        IsOpen A → IsOpen B → ContDiffOn ℝ (k : WithTop ENat) f (A ∪ B) →
        (∀ x ∈ A, x ∉ B → ∀ y ∈ B, y ∉ A → ρ j / 2 ≤ ‖x - y‖) →
        Work.CR.Flat.holderNorm k α f (A ∪ B)
          ≤ ENNReal.ofReal (C k) *
            (Work.CR.Flat.holderNorm k α f A + Work.CR.Flat.holderNorm k α f B) :=
    fun j => holderNorm_union_le_of_separated (E := Fin n → ℂ) hα0 (η := ρ j / 2)
      (by linarith [hρ j])
  choose Cu hCu0 hCu using hCuex
  refine ⟨fun k => (∑ j : Fin n, Cu j k * (1 + (Cp j k * C0 k) * Cf j k)) + 1, ?_, ?_⟩
  · intro k
    have h0 : 0 ≤ ∑ j : Fin n, Cu j k * (1 + (Cp j k * C0 k) * Cf j k) :=
      Finset.sum_nonneg fun j _ => by
        have h1 : 0 < Cu j k := hCu0 j k
        have h2 : 0 < Cp j k := hCp0 j k
        have h3 : 0 < Cf j k := hCf0 j k
        have h4 : 0 < C0 k := hC00 k
        positivity
    linarith
  · intro k j G hG hfin
    set ε : ℝ := ρ j / 2 with hεdef
    have hρj : 0 < ρ j := hρ j
    have hε : 0 < ε := by rw [hεdef]; linarith
    have hερ : ε < ρ j := by rw [hεdef]; linarith
    set B : Set (Fin n → ℂ) := outRegion n ρ j ∩ {z : Fin n → ℂ | ε < ‖z j‖} with hBdef
    have hAopen : IsOpen (inRegion n ρ j) := isOpen_inRegion n (hρ := hρ) j
    have hBopen : IsOpen B := by
      rw [hBdef]
      exact (isOpen_outRegion n (hρ := hρ) j).inter
        (isOpen_lt continuous_const (continuous_norm.comp (continuous_apply j)))
    have hGin : ContDiffOn ℝ (k : WithTop ENat) G (inRegion n ρ j) :=
      hG.mono radialEst_inRegion_subset_oneSidedRegion
    -- the flat pullback is `C^k` on the closed half space
    have hmapsΦ : Set.MapsTo (flatPoint n ρ j) (flatRegion n ρ j ε ×ˢ {t : ℝ | 0 ≤ t})
        (oneSidedRegion n ρ (j : ℕ)) := radialEst_mapsTo_flatPoint hρ j hε
    have hΦ : ContDiffOn ℝ (k : WithTop ENat) (flatPoint n ρ j)
        (flatRegion n ρ j ε ×ˢ {t : ℝ | 0 ≤ t}) := radialEst_contDiffOn_flatPoint hε k
    have hgclosed : ContDiffOn ℝ (k : WithTop ENat) (flatPull n ρ j G)
        (flatRegion n ρ j ε ×ˢ {t : ℝ | 0 ≤ t}) := hG.comp hΦ hmapsΦ
    have hgfin : Work.CR.Flat.holderNorm k α (flatPull n ρ j G)
        (flatRegion n ρ j ε ×ˢ {t : ℝ | 0 < t}) ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) (hCf j k G hGin)
    -- the flat Seeley estimate on the slab
    have hsee := hC0 k 1 (by norm_num) (flatRegion n ρ j ε) (flatPull n ρ j G)
      (isOpen_flatRegion n (hρ := hρ) j ε) hgclosed hgfin
    -- smoothness of the pulled back extension on the annulus
    have hLam : ContDiffOn ℝ (k : WithTop ENat)
        (fun z => seeleyExt a b (flatPull n ρ j G) (polarChart n ρ j z)) B := by
      rw [hBdef]
      exact hsee.1.comp (radialEst_contDiffOn_polarChart hε hρj k) (radialEst_mapsTo_polarChart hε hρj)
    have hrad_cont : ContDiffOn ℝ (k : WithTop ENat) (radialExt n ρ a b j G)
        (inRegion n ρ j ∪ B) := by
      refine radialEst_contDiffOn_union_of_isOpen hAopen hBopen ?_ ?_
      · exact hGin.congr (fun z hz => radialExt_of_le (le_of_lt (mem_inRegion.mp hz).2.1))
      · refine hLam.congr (fun z hz => ?_)
        rw [hBdef] at hz
        obtain ⟨hzout, hzj⟩ := hz
        exact radialExt_seeleyExt_flat j hρj a b G (norm_pos_iff.mp (lt_trans hε hzj))
    -- the separation
    have hsep : ∀ x ∈ inRegion n ρ j, x ∉ B → ∀ y ∈ B, y ∉ inRegion n ρ j → ε ≤ ‖x - y‖ := by
      intro x hx hxB y hy hyA
      have hxj : ‖x j‖ ≤ ε := by
        by_contra hcon
        exact hxB (by
          rw [hBdef]
          exact ⟨inRegion_subset_outRegion hx, lt_of_not_ge hcon⟩)
      have hyge : ρ j ≤ ‖y j‖ := by
        by_contra hcon
        rw [hBdef] at hy
        obtain ⟨hyout, hyj⟩ := hy
        obtain ⟨h1, h2, h3⟩ := mem_outRegion.mp hyout
        exact hyA (by rw [mem_inRegion]; exact ⟨h1, lt_of_not_ge hcon, h3⟩)
      have h1 : ‖y j - x j‖ ≤ ‖y - x‖ := by
        simpa only [Pi.sub_apply] using norm_le_pi_norm (y - x) j
      have h2 : ε ≤ ‖y j - x j‖ := by
        have h3 : ‖y j‖ - ‖x j‖ ≤ ‖y j - x j‖ :=
          le_trans (le_abs_self _) (abs_norm_sub_norm_le (y j) (x j))
        rw [hεdef] at hxj ⊢
        linarith
      exact le_trans h2 (by rw [← norm_sub_rev y x]; exact h1)
    have hunion := hCu j k (radialExt n ρ a b j G) (inRegion n ρ j) B hAopen hBopen hrad_cont hsep
    have hAeq : Work.CR.Flat.holderNorm k α (radialExt n ρ a b j G) (inRegion n ρ j)
        = Work.CR.Flat.holderNorm k α G (inRegion n ρ j) :=
      holderNorm_congr_of_isOpen hAopen
        (fun z hz => radialExt_of_le (le_of_lt (mem_inRegion.mp hz).2.1)) k α
    have hBeq : Work.CR.Flat.holderNorm k α (radialExt n ρ a b j G) B
        = Work.CR.Flat.holderNorm k α
            (fun z => seeleyExt a b (flatPull n ρ j G) (polarChart n ρ j z)) B :=
      holderNorm_congr_of_isOpen hBopen (fun z hz => by
        rw [hBdef] at hz
        obtain ⟨hzout, hzj⟩ := hz
        exact radialExt_seeleyExt_flat j hρj a b G (norm_pos_iff.mp (lt_trans hε hzj))) k α
    have hBnd : Work.CR.Flat.holderNorm k α
          (fun z => seeleyExt a b (flatPull n ρ j G) (polarChart n ρ j z)) B
        ≤ ENNReal.ofReal (Cp j k) * (ENNReal.ofReal (C0 k) * (ENNReal.ofReal (Cf j k)
            * Work.CR.Flat.holderNorm k α G (inRegion n ρ j))) := by
      have hCpe := hCp j k (seeleyExt a b (flatPull n ρ j G)) hsee.1
      calc Work.CR.Flat.holderNorm k α
              (fun z => seeleyExt a b (flatPull n ρ j G) (polarChart n ρ j z)) B
          = Work.CR.Flat.holderNorm k α
              (fun z => seeleyExt a b (flatPull n ρ j G) (polarChart n ρ j z))
              (outRegion n ρ j ∩ {z : Fin n → ℂ | ρ j / 2 < ‖z j‖}) := by rw [hBdef, hεdef]
        _ ≤ ENNReal.ofReal (Cp j k) * Work.CR.Flat.holderNorm k α (seeleyExt a b (flatPull n ρ j G))
              (flatRegion n ρ j (ρ j / 2) ×ˢ {t : ℝ | -(1:ℝ) < t}) := hCpe
        _ ≤ ENNReal.ofReal (Cp j k) * (ENNReal.ofReal (C0 k)
              * Work.CR.Flat.holderNorm k α (flatPull n ρ j G)
                  (flatRegion n ρ j (ρ j / 2) ×ˢ {t : ℝ | 0 < t})) :=
            mul_le_mul' le_rfl hsee.2
        _ ≤ ENNReal.ofReal (Cp j k) * (ENNReal.ofReal (C0 k) * (ENNReal.ofReal (Cf j k)
              * Work.CR.Flat.holderNorm k α G (inRegion n ρ j))) :=
            mul_le_mul' le_rfl (mul_le_mul' le_rfl (hCf j k G hGin))
    have hAB : inRegion n ρ j ∪ B = outRegion n ρ j := by
      rw [hBdef]
      refine Set.Subset.antisymm ?_ ?_
      · exact Set.union_subset inRegion_subset_outRegion Set.inter_subset_left
      · intro z hz
        obtain ⟨h1, hj, h3⟩ := mem_outRegion.mp hz
        rcases lt_or_ge ‖z j‖ (ρ j) with hlt | hge
        · exact Or.inl (by rw [mem_inRegion]; exact ⟨h1, hlt, h3⟩)
        · refine Or.inr ⟨?_, ?_⟩
          · rw [mem_outRegion]; exact ⟨h1, hj, h3⟩
          · exact lt_of_lt_of_le hερ hge
    calc Work.CR.Flat.holderNorm k α (radialExt n ρ a b j G) (outRegion n ρ j)
        = Work.CR.Flat.holderNorm k α (radialExt n ρ a b j G) (inRegion n ρ j ∪ B) := by
            rw [hAB]
      _ ≤ ENNReal.ofReal (Cu j k) * (Work.CR.Flat.holderNorm k α (radialExt n ρ a b j G)
              (inRegion n ρ j) + Work.CR.Flat.holderNorm k α (radialExt n ρ a b j G) B) := hunion
      _ = ENNReal.ofReal (Cu j k) * (Work.CR.Flat.holderNorm k α G (inRegion n ρ j)
              + Work.CR.Flat.holderNorm k α
                  (fun z => seeleyExt a b (flatPull n ρ j G) (polarChart n ρ j z)) B) := by
            rw [hAeq, hBeq]
      _ ≤ ENNReal.ofReal (Cu j k) * (Work.CR.Flat.holderNorm k α G (inRegion n ρ j)
              + ENNReal.ofReal (Cp j k) * (ENNReal.ofReal (C0 k) * (ENNReal.ofReal (Cf j k)
                * Work.CR.Flat.holderNorm k α G (inRegion n ρ j)))) :=
            mul_le_mul' le_rfl (add_le_add le_rfl hBnd)
      _ = ENNReal.ofReal (Cu j k * (1 + (Cp j k * C0 k) * Cf j k))
            * Work.CR.Flat.holderNorm k α G (inRegion n ρ j) :=
            radialEst_ofReal_algebra (Cu j k) (Cp j k) (C0 k) (Cf j k) (le_of_lt (hCu0 j k))
              (le_of_lt (hCp0 j k)) (le_of_lt (hC00 k)) (le_of_lt (hCf0 j k)) _
      _ ≤ ENNReal.ofReal ((∑ j' : Fin n, Cu j' k * (1 + (Cp j' k * C0 k) * Cf j' k)) + 1)
            * Work.CR.Flat.holderNorm k α G (inRegion n ρ j) := by
            refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
            refine le_trans (Finset.single_le_sum
              (f := fun j' : Fin n => Cu j' k * (1 + (Cp j' k * C0 k) * Cf j' k)) ?_
              (Finset.mem_univ j)) (le_add_of_nonneg_right (by norm_num))
            intro j' _
            have h1 : 0 < Cu j' k := hCu0 j' k
            have h2 : 0 < Cp j' k := hCp0 j' k
            have h3 : 0 < Cf j' k := hCf0 j' k
            have h4 : 0 < C0 k := hC00 k
            positivity


/-! ## The one-step `C^{k,α}` estimate -/

theorem radialExt_holderNorm_est_stepNG {n : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) {a b : ℕ → ℝ} (hb : ∀ m, 2 ≤ b m)
    (hbT : Filter.Tendsto b Filter.atTop Filter.atTop)
    (ha : ∀ j : ℕ, ∑' m, a m * (-(b m)) ^ j = 1)
    (hsum : ∀ j : ℕ, Summable fun m => |a m| * (b m) ^ j) :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧
      ∀ (k : ℕ) (j : Fin n) (G : (Fin n → ℂ) → ℂ),
        ContDiffOn ℝ (k : WithTop ENat) G (Work.NN.Final.oneSidedRegion n ρ (j : ℕ)) →
        Work.CR.Flat.holderNorm k α G (Work.NN.Final.inRegion n ρ j) ≠ ⊤ →
        Work.CR.Flat.holderNorm k α (Work.NN.Final.radialExt n ρ a b j G)
            (Work.NN.Final.outRegion n ρ j)
          ≤ ENNReal.ofReal (C k) * Work.CR.Flat.holderNorm k α G
              (Work.NN.Final.inRegion n ρ j) := by
  obtain ⟨C0, hC00, hC0⟩ :=
    seeleyRegionEstimateNoGlue (E := Fin n → ℂ) (α := α) hα0 hα1 hb hbT ha hsum
  exact radialExt_holderNorm_est_step_auxNG hρ hα0 hα1 hb hbT ha hsum C0 hC00 hC0

end Work.NN.Final
