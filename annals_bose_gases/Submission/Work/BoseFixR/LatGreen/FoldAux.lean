import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixR.LatGreen.FoldDefs
import Submission.Work.BoseFixR.SamplingSqSumLeChiR0
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.LatGreen.FoldAux` — elementary facts about the folding map

Vocabulary for `PeriodEqFold`: the folding `foldMap ℓ` is invariant under lattice translations
and is the identity on the half-open fundamental domain `cellI ℓ`; the periodisation
`period W ℓ` of a charge supported in `ball 0 ℓ` agrees on the cell with a *finite* lattice sum
`periodFin W ℓ` (so it is measurable and nonnegative there).
-/

noncomputable section
open scoped Real Topology BigOperators Pointwise
open MeasureTheory Filter Metric Set

namespace Work.BoseFixR.LatGreen

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The folding map -/

/-- The folding is invariant under lattice translations. -/
lemma foldMap_add_lat {ℓ : ℝ} (hℓ : ℓ ≠ 0) (x : E3) (n : Fin 3 → ℤ) :
    foldMap ℓ (x + Work.BoseFixR.lat ℓ n) = foldMap ℓ x := by
  ext i
  rw [foldMap_apply, foldMap_apply]
  have hx : (x + Work.BoseFixR.lat ℓ n) i = x i + ℓ * (n i : ℝ) := by
    simp [Work.BoseFixR.lat_apply]
  rw [hx]
  have hdiv : (x i + ℓ * (n i : ℝ)) / ℓ = x i / ℓ + (n i : ℝ) := by
    rw [add_div, mul_div_cancel_left₀ _ hℓ]
  rw [hdiv, round_add_intCast]
  push_cast
  ring

/-- On the half-open fundamental domain the folding is the identity. -/
lemma foldMap_eq_self_of_mem_cellI {ℓ : ℝ} (hℓ : 0 < ℓ) {x : E3}
    (hx : x ∈ Work.BoseFixR.cellI ℓ) : foldMap ℓ x = x := by
  ext i
  rw [foldMap_apply]
  have hxi : x i ∈ Ico (-(ℓ / 2)) (ℓ / 2) := hx i
  rw [mem_Ico] at hxi
  have hround : round (x i / ℓ) = 0 := by
    rw [round_eq_zero_iff, mem_Ico]
    exact ⟨by rw [le_div_iff₀ hℓ]; linarith [hxi.1],
      by rw [div_lt_iff₀ hℓ]; linarith [hxi.2]⟩
  rw [hround]
  simp

/-- The folding is measurable. -/
lemma measurable_foldMap (ℓ : ℝ) : Measurable (foldMap ℓ) := by
  have hround : Measurable fun y : ℝ => round y := by
    have h : Measurable fun y : ℝ => (⌊y + 1 / 2⌋ : ℤ) :=
      Int.measurable_floor.comp (measurable_id.add_const (1 / 2))
    convert h using 1
    funext y
    simp [round_eq]
  have hco : Measurable
      (fun f : Fin 3 → ℝ => fun i : Fin 3 => f i - ℓ * (round (f i / ℓ) : ℝ)) := by
    rw [measurable_pi_iff]
    intro i
    have h1 : Measurable fun f : Fin 3 → ℝ => f i := measurable_pi_apply i
    have h2 : Measurable fun f : Fin 3 → ℝ => round (f i / ℓ) := hround.comp (h1.div_const ℓ)
    exact h1.sub (measurable_const.mul
      ((Measurable.of_discrete (f := fun n : ℤ => (n : ℝ))).comp h2))
  exact (WithLp.measurable_toLp 2 (Fin 3 → ℝ)).comp
    (hco.comp (WithLp.measurable_ofLp 2 (Fin 3 → ℝ)))

/-! ## 2. The finite lattice sum representing the periodisation on the cell -/

/-- `latBox 1` is symmetric under negation. -/
lemma neg_mem_latBox_one_iff {n : Fin 3 → ℤ} :
    -n ∈ Work.BoseFixR.latBox 1 ↔ n ∈ Work.BoseFixR.latBox 1 := by
  rw [Work.BoseFixR.mem_latBox, Work.BoseFixR.mem_latBox]
  exact forall_congr' fun i => by simp

/-- The **finite** lattice sum representing the periodisation `period W ℓ` on the cell `cell ℓ`,
for a charge `W` supported in the ball of radius `ℓ`. -/
noncomputable def periodFin (W : E3 → ℝ) (ℓ : ℝ) (x : E3) : ℝ :=
  ∑ n ∈ Work.BoseFixR.latBox 1, W (x - Work.BoseFixR.lat ℓ n)

/-- On the closed cell the periodisation is the finite sum `periodFin`. -/
lemma period_eq_periodFin_on_cell {ℓ : ℝ} (hℓ : 0 < ℓ) {W : E3 → ℝ}
    (hsupp : tsupport W ⊆ Metric.ball (0 : E3) ℓ) {x : E3}
    (hx : x ∈ Work.BoseFixR.cell ℓ) :
    period W ℓ x = periodFin W ℓ x := by
  have hzero : ∀ n : Fin 3 → ℤ, n ∉ Work.BoseFixR.latBox 1 →
      W (x - Work.BoseFixR.lat ℓ n) = 0 := by
    intro n hn
    have hn' : -n ∉ Work.BoseFixR.latBox 1 := fun h => hn (neg_mem_latBox_one_iff.mp h)
    have hlat : Work.BoseFixR.lat ℓ (-n) = -Work.BoseFixR.lat ℓ n := by
      simpa using map_neg (Work.BoseFixR.latHom ℓ) n
    rw [show x - Work.BoseFixR.lat ℓ n = x + Work.BoseFixR.lat ℓ (-n) by
      rw [hlat, sub_eq_add_neg]]
    exact Work.BoseFixR.eq_zero_of_notMem_latBox hℓ (le_of_eq (mul_one ℓ).symm) hsupp hn' hx
  simp only [period, periodFin]
  exact tsum_eq_sum (s := Work.BoseFixR.latBox 1) hzero

/-- On the closed cell the periodisation is the finite lattice sum with `+` signs. -/
lemma period_eq_sum_add_on_cell {ℓ : ℝ} (hℓ : 0 < ℓ) {W : E3 → ℝ}
    (hsupp : tsupport W ⊆ Metric.ball (0 : E3) ℓ) {x : E3}
    (hx : x ∈ Work.BoseFixR.cell ℓ) :
    period W ℓ x = ∑ n ∈ Work.BoseFixR.latBox 1, W (x + Work.BoseFixR.lat ℓ n) := by
  rw [period_eq_periodFin_on_cell hℓ hsupp hx]
  simp only [periodFin]
  refine Finset.sum_bij (fun n _ => -n) (fun n hn => neg_mem_latBox_one_iff.mpr hn)
    (fun a _ b _ hab => by simpa using hab)
    (fun b hb => ⟨-b, neg_mem_latBox_one_iff.mpr hb, by simp⟩) ?_
  intro n hn
  have hlat : Work.BoseFixR.lat ℓ (-n) = -Work.BoseFixR.lat ℓ n := by
    simpa using map_neg (Work.BoseFixR.latHom ℓ) n
  rw [hlat, sub_eq_add_neg]

/-- The finite lattice sum is nonnegative for a nonnegative charge. -/
lemma periodFin_nonneg {ℓ : ℝ} {W : E3 → ℝ} (hWnn : ∀ x, 0 ≤ W x) (x : E3) :
    0 ≤ periodFin W ℓ x :=
  Finset.sum_nonneg fun n _ => hWnn _

/-! ## 3. Almost-everywhere measurability of the periodisation on the cell -/

/-- A function of the first factor of a product is a.e. measurable. -/
lemma aemeasurable_comp_fst {β : Type*} [MeasurableSpace β] {g : E3 → β}
    {μ ν : Measure E3} (hg : AEMeasurable g μ) [SFinite μ] [SFinite ν] :
    AEMeasurable (fun p : E3 × E3 => g p.1) (μ.prod ν) := by
  obtain ⟨g', hg'm, hgg'⟩ := hg
  refine ⟨fun p => g' p.1, hg'm.comp measurable_fst, ?_⟩
  rw [Filter.EventuallyEq, ae_iff] at hgg' ⊢
  have hset : {p : E3 × E3 | ¬g p.1 = g' p.1} = {a : E3 | ¬g a = g' a} ×ˢ Set.univ := by
    ext p; simp
  rw [hset, Measure.prod_prod, hgg', zero_mul]

/-- A function of the second factor of a product is a.e. measurable. -/
lemma aemeasurable_comp_snd {β : Type*} [MeasurableSpace β] {g : E3 → β}
    {μ ν : Measure E3} (hg : AEMeasurable g ν) [SFinite μ] [SFinite ν] :
    AEMeasurable (fun p : E3 × E3 => g p.2) (μ.prod ν) := by
  obtain ⟨g', hg'm, hgg'⟩ := hg
  refine ⟨fun p => g' p.2, hg'm.comp measurable_snd, ?_⟩
  rw [Filter.EventuallyEq, ae_iff] at hgg' ⊢
  have hset : {p : E3 × E3 | ¬g p.2 = g' p.2} = Set.univ ×ˢ {a : E3 | ¬g a = g' a} := by
    ext p; simp
  rw [hset, Measure.prod_prod, hgg', mul_zero]

/-- The finite lattice sum of an a.e. measurable charge is a.e. measurable. -/
lemma aemeasurable_periodFin {ℓ : ℝ} {W : E3 → ℝ} (hW : AEMeasurable W volume) :
    AEMeasurable (fun x : E3 => periodFin W ℓ x) volume := by
  have hterm : ∀ n : Fin 3 → ℤ,
      AEMeasurable (fun x : E3 => W (x - Work.BoseFixR.lat ℓ n)) volume := fun n => by
    have hmap : Measure.map (fun x : E3 => x - Work.BoseFixR.lat ℓ n) volume = volume := by
      have h := MeasureTheory.map_add_right_eq_self volume (-Work.BoseFixR.lat ℓ n)
      simpa only [sub_eq_add_neg] using h
    have hf : AEMeasurable (fun x : E3 => x - Work.BoseFixR.lat ℓ n) volume :=
      (measurable_id.sub_const _).aemeasurable
    have hg : AEMeasurable W
        (Measure.map (fun x : E3 => x - Work.BoseFixR.lat ℓ n) volume) := by
      rw [hmap]; exact hW
    simpa only [Function.comp_def] using AEMeasurable.comp_aemeasurable (g := W) hg hf
  have := Finset.aemeasurable_fun_sum (Work.BoseFixR.latBox 1)
    (fun n _ => (hterm n))
  simpa only [periodFin] using this

/-! ## 4. The pushforward identity -/

/-- **The periodisation is the pushforward of the folding.** For a nonnegative charge `W`
supported in the ball of radius `ℓ`, the integral of any measurable test function `φ` against the
`ℓ`-periodisation `period W ℓ` over one cell equals the integral of `φ ∘ foldMap ℓ` against `W`
over `ℝ³`. -/
theorem period_fold_lintegral {ℓ : ℝ} (hℓ : 0 < ℓ) {W : E3 → ℝ}
    (hWnn : ∀ x, 0 ≤ W x) (hW : AEMeasurable W volume)
    (hsupp : tsupport W ⊆ Metric.ball (0 : E3) ℓ)
    (φ : E3 → ENNReal) (hφ : AEMeasurable φ volume) :
    ∫⁻ x in Work.BoseFixR.cell ℓ, ENNReal.ofReal (period W ℓ x) * φ x
      = ∫⁻ u, ENNReal.ofReal (W u) * φ (foldMap ℓ u) := by
  classical
  have hne : ℓ ≠ 0 := ne_of_gt hℓ
  have hcellI : MeasurableSet (Work.BoseFixR.cellI ℓ) := Work.BoseFixR.measurableSet_cellI ℓ
  haveI : Countable (Work.BoseFixR.latHom ℓ).range := Work.BoseFixR.countable_range_latHom hne
  have hRℓ : ℓ ≤ ℓ * 1 := by rw [mul_one]
  have hWtrans : ∀ c : E3, AEMeasurable (fun x : E3 => W (x + c)) volume := by
    intro c
    have hmap : Measure.map (fun x : E3 => x + c) volume = volume :=
      map_add_right_eq_self volume c
    have hf : AEMeasurable (fun x : E3 => x + c) volume := (measurable_id.add_const c).aemeasurable
    have hg : AEMeasurable W (Measure.map (fun x : E3 => x + c) volume) := by
      rw [hmap]; exact hW
    simpa only [Function.comp_def] using AEMeasurable.comp_aemeasurable (g := W) hg hf
  have hterm0 : ∀ n : Fin 3 → ℤ,
      AEMeasurable (fun x : E3 =>
        ENNReal.ofReal (W (x + Work.BoseFixR.lat ℓ n)) * φ x) volume := fun n =>
    ((hWtrans (Work.BoseFixR.lat ℓ n)).ennreal_ofReal).mul hφ
  -- Step 1: the fundamental-domain tiling
  have hstep1 : (∫⁻ u, ENNReal.ofReal (W u) * φ (foldMap ℓ u))
      = ∑' n : Fin 3 → ℤ, ∫⁻ x in Work.BoseFixR.cellI ℓ,
          ENNReal.ofReal (W (x + Work.BoseFixR.lat ℓ n)) * φ (foldMap ℓ x) := by
    rw [(Work.BoseFixR.isAddFundamentalDomain_cellI hℓ).lintegral_eq_tsum''
        (fun u => ENNReal.ofReal (W u) * φ (foldMap ℓ u)),
      ← (Work.BoseFixR.latEquiv hne).tsum_eq (fun g : (Work.BoseFixR.latHom ℓ).range =>
        ∫⁻ x in Work.BoseFixR.cellI ℓ,
          (fun u : E3 => ENNReal.ofReal (W u) * φ (foldMap ℓ u)) (g +ᵥ x))]
    refine tsum_congr fun n => ?_
    have hpt : ∀ x : E3,
        ((Work.BoseFixR.latEquiv hne n : (Work.BoseFixR.latHom ℓ).range) +ᵥ x)
          = x + Work.BoseFixR.lat ℓ n := by
      intro x
      simp [Work.BoseFixR.latEquiv, AddSubgroup.vadd_def, add_comm]
    congr 1 with x
    rw [hpt x]
    simp only [Work.BoseFixR.LatGreen.foldMap_add_lat hne]
  -- Step 2: on the fundamental domain the folding is the identity
  have hterm : ∀ n : Fin 3 → ℤ,
      (∫⁻ x in Work.BoseFixR.cellI ℓ,
          ENNReal.ofReal (W (x + Work.BoseFixR.lat ℓ n)) * φ (foldMap ℓ x))
        = ∫⁻ x in Work.BoseFixR.cellI ℓ,
            ENNReal.ofReal (W (x + Work.BoseFixR.lat ℓ n)) * φ x := fun n =>
    setLIntegral_congr_fun hcellI fun x hx => by rw [foldMap_eq_self_of_mem_cellI hℓ hx]
  -- Step 3: the terms with `n ∉ latBox 1` vanish
  have hzero : ∀ n : Fin 3 → ℤ, n ∉ Work.BoseFixR.latBox 1 →
      (∫⁻ x in Work.BoseFixR.cellI ℓ,
          ENNReal.ofReal (W (x + Work.BoseFixR.lat ℓ n)) * φ x) = 0 := by
    intro n hn
    refine setLIntegral_eq_zero hcellI fun x hx => ?_
    have hx0 : W (x + Work.BoseFixR.lat ℓ n) = 0 :=
      Work.BoseFixR.eq_zero_of_notMem_latBox hℓ hRℓ hsupp hn
        (Work.BoseFixR.cellI_subset_cell ℓ hx)
    rw [hx0]; simp
  -- Step 4: sum/integral exchange over the finite lattice box
  have hstep5 : (∫⁻ x in Work.BoseFixR.cellI ℓ,
          (∑ n ∈ Work.BoseFixR.latBox 1,
            ENNReal.ofReal (W (x + Work.BoseFixR.lat ℓ n))) * φ x)
        = ∑ n ∈ Work.BoseFixR.latBox 1,
            ∫⁻ x in Work.BoseFixR.cellI ℓ,
              ENNReal.ofReal (W (x + Work.BoseFixR.lat ℓ n)) * φ x := by
    rw [show (fun x : E3 => (∑ n ∈ Work.BoseFixR.latBox 1,
            ENNReal.ofReal (W (x + Work.BoseFixR.lat ℓ n))) * φ x)
          = fun x : E3 => ∑ n ∈ Work.BoseFixR.latBox 1,
              ENNReal.ofReal (W (x + Work.BoseFixR.lat ℓ n)) * φ x from
        funext fun x => Finset.sum_mul _ _ _]
    exact lintegral_finsetSum' _ fun n _ => (hterm0 n).restrict
  -- Step 5: rewrite the finite sum as the periodisation
  have hstep6 : (∫⁻ x in Work.BoseFixR.cellI ℓ,
          (∑ n ∈ Work.BoseFixR.latBox 1,
            ENNReal.ofReal (W (x + Work.BoseFixR.lat ℓ n))) * φ x)
        = ∫⁻ x in Work.BoseFixR.cellI ℓ, ENNReal.ofReal (period W ℓ x) * φ x := by
    refine setLIntegral_congr_fun hcellI fun x hx => ?_
    rw [period_eq_sum_add_on_cell hℓ hsupp (Work.BoseFixR.cellI_subset_cell ℓ hx),
      ENNReal.ofReal_sum_of_nonneg (fun n _ => hWnn _)]
  -- Step 6: half-open to closed cell
  have hstep7 : (∫⁻ x in Work.BoseFixR.cellI ℓ, ENNReal.ofReal (period W ℓ x) * φ x)
      = ∫⁻ x in Work.BoseFixR.cell ℓ, ENNReal.ofReal (period W ℓ x) * φ x :=
    setLIntegral_congr (Work.BoseFixR.cellI_ae_eq_cell ℓ)
  rw [hstep1, tsum_congr hterm, tsum_eq_sum hzero, ← hstep5, hstep6, hstep7]

/-! ## 5. Measurability of the folded potential -/

/-- The folded potential `x ↦ ∫⁻ v, W v · (4π‖x − foldMap ℓ v‖)⁻¹` is a.e. measurable. -/
theorem phi_aemeasurable {ℓ : ℝ} {W : E3 → ℝ} (hW : AEMeasurable W volume) :
    AEMeasurable (fun x : E3 => ∫⁻ v : E3, ENNReal.ofReal (W v) *
      ENNReal.ofReal ((4 * Real.pi * ‖x - foldMap ℓ v‖)⁻¹)) volume := by
  have hG : AEMeasurable (fun p : E3 × E3 => ENNReal.ofReal (W p.2) *
      ENNReal.ofReal ((4 * Real.pi * ‖p.1 - foldMap ℓ p.2‖)⁻¹)) (volume.prod volume) := by
    refine AEMeasurable.mul (aemeasurable_comp_snd hW |>.ennreal_ofReal) ?_
    have h1 : Measurable fun p : E3 × E3 => p.1 - foldMap ℓ p.2 :=
      measurable_fst.sub ((measurable_foldMap ℓ).comp measurable_snd)
    exact ((measurable_const.mul h1.norm).inv.ennreal_ofReal).aemeasurable
  exact hG.lintegral_prod_right

end Work.BoseFixR.LatGreen
