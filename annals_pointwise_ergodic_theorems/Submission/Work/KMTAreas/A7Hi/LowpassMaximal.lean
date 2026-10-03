import Mathlib
import Submission.Work.KMTAreas.A7Hi2.supPieceClean
import Submission.Port.Aesm

namespace Work.KMTAreas.A7Hi

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators

noncomputable section

/-! ## The reduction of the values-supremum to the partial-sum maximal function

For `T_m := lpf ρ l₁ m₀ m = kmtProj ρ l₁ (-(m₀+m))` the telescoping
`∑_{i<K} (T_{i+1} − T_i) = T_K − T_0` gives, pointwise in `x`,

  `sup_m ‖T_m f x‖ ≤ ‖T_0 f x‖ + sup_K ‖∑_{i<K}(T_{i+1} − T_i) f x‖`,

and hence `LowpassMaximal` follows from the *uniform single-scale bound* (PROVED:
`Work.KMTAreas.A7.kmtProj_lp_bound_uniform`), the *band square-function bound* (PROVED:
`Work.KMTAreas.A7Lpd.bandSquareUnif`) and the **Men'shov / lacunary-maximal input**

  `‖ sup_K ‖∑_{i<K}(T_{i+1} − T_i) f‖ₑ ‖_{ℓᵖ} ≤ C‖ sqFun ρ l₁ m₀ f ‖_{ℓᵖ}`,

which is the single remaining gap of this chapter (see
`NOTES_A7Hi_LowpassMaximal_SESSION8.md` §1–§4 and `NOTES_A7Hi2_P2_chapter_DESIGN.md`). -/

/-- The partial-sum maximal function of the annuli of the low-pass family. -/
noncomputable def partSumSup (ρ : ℝ) (l₁ m₀ : ℕ) (f : ℤ → ℂ) (x : ℤ) : ℝ≥0∞ :=
  ⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
      (lpf ρ l₁ m₀ (i + 1) f x - lpf ρ l₁ m₀ i f x))‖ₑ

/-- **The values supremum is dominated by the first value plus the partial-sum maximal
function of the annuli** (the telescoping `T_K = T_0 + ∑_{i<K}(T_{i+1} − T_i)`). -/
lemma supPart_le_norm_zero_add_partSumSup (r : NNReal) (ρ : ℝ) (l₁ m₀ : ℕ) (f : ℤ → ℂ)
    (x : ℤ) :
    supPart r (fun m : ℕ => lpf ρ l₁ m₀ m f x)
      ≤ ‖lpf ρ l₁ m₀ 0 f x‖ₑ + partSumSup ρ l₁ m₀ f x := by
  refine iSup_le fun K => ?_
  change ‖lpf ρ l₁ m₀ K f x‖ₑ
    ≤ ‖lpf ρ l₁ m₀ 0 f x‖ₑ + partSumSup ρ l₁ m₀ f x
  have htel : (∑ i ∈ Finset.range K,
        (lpf ρ l₁ m₀ (i + 1) f x - lpf ρ l₁ m₀ i f x))
      = lpf ρ l₁ m₀ K f x - lpf ρ l₁ m₀ 0 f x :=
    Finset.sum_range_sub (fun i : ℕ => lpf ρ l₁ m₀ i f x) K
  have h1 : lpf ρ l₁ m₀ K f x
      = lpf ρ l₁ m₀ 0 f x
        + ∑ i ∈ Finset.range K, (lpf ρ l₁ m₀ (i + 1) f x - lpf ρ l₁ m₀ i f x) := by
    rw [htel]; ring
  rw [h1]
  refine (enorm_add_le _ _).trans (add_le_add le_rfl ?_)
  exact le_iSup (fun K : ℕ => ‖(∑ i ∈ Finset.range K,
      (lpf ρ l₁ m₀ (i + 1) f x - lpf ρ l₁ m₀ i f x))‖ₑ) K

/-- **The target from the lacunary-maximal (Men'shov) input.**  The hypothesis `hL` is the
statement proved in the sibling module `Submission.Work.KMTAreas.A7Hi2.lacunaryMaxPiece`. -/
theorem lowpassMaximal_of_lacunaryMaxPiece
    (hL : ∀ (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤),
      ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
        Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
        MeasureTheory.eLpNorm (partSumSup ρ l₁ m₀ f) p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C *
            MeasureTheory.eLpNorm (sqFun ρ l₁ m₀ f) p MeasureTheory.Measure.count
          + ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤)
    (r : NNReal) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ => supPart r (fun m : ℕ => lpf ρ l₁ m₀ m f x))
        p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * (1 + (l₁ : ℝ)) ^ 2) *
            MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  obtain ⟨CρL, hCρLpos, CL, hCLpos, hLb⟩ := hL ρ hρ hρ1 p hp hptop
  obtain ⟨CρB, hCρBpos, CB, hCBpos, hBb⟩ :=
    Work.KMTAreas.A7Lpd.bandSquareUnif ρ hρ hρ1 p hp hptop
  have hp1 : (1 : ℝ) < p.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top (ne_of_lt hptop)).mpr hp
  obtain ⟨CρS, hCρSpos, CS, hCSpos, hSb⟩ :=
    Work.KMTAreas.A7.kmtProj_lp_bound_uniform ρ hρ hρ1 p.toReal hp1
  have hpne0 : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp)
  have hpnetop : p ≠ ⊤ := ne_of_lt hptop
  have hpeq : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal hpnetop
  refine ⟨max CρL (max CρB CρS), lt_max_of_lt_left hCρLpos, CS + CL * CB + CL,
    by positivity, ?_⟩
  intro l₁ m₀ hgood f
  have hgL : Work.Analysis.IonescuWainger.GoodMajorArcs ρ CρL l₁ (-(m₀ : ℤ)) :=
    goodMajorArcs_mono (le_max_left _ _) hgood
  have hgB : Work.Analysis.IonescuWainger.GoodMajorArcs ρ CρB l₁ (-(m₀ : ℤ)) :=
    goodMajorArcs_mono (le_trans (le_max_left _ _) (le_max_right _ _)) hgood
  have hgS : Work.Analysis.IonescuWainger.GoodMajorArcs ρ CρS l₁ (-(m₀ : ℤ)) :=
    goodMajorArcs_mono (le_trans (le_max_right _ _) (le_max_right _ _)) hgood
  -- step 1: pointwise domination, in `ℓᵖ`
  have hstep : MeasureTheory.eLpNorm (fun x : ℤ => supPart r
        (fun m : ℕ => lpf ρ l₁ m₀ m f x)) p MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ => ‖lpf ρ l₁ m₀ 0 f x‖ₑ)
          p MeasureTheory.Measure.count
        + MeasureTheory.eLpNorm (partSumSup ρ l₁ m₀ f) p MeasureTheory.Measure.count := by
    refine (Work.KMTAreas.A7.eLpNorm_mono_ennreal (q := p)
      (fun x => supPart_le_norm_zero_add_partSumSup r ρ l₁ m₀ f x) hpne0 hpnetop).trans ?_
    exact Work.KMTAreas.A7.eLpNorm_add_le_ennreal (le_of_lt hp) hpnetop
  -- step 2: the first value (uniform single-scale bound)
  have hfirst : MeasureTheory.eLpNorm (fun x : ℤ => ‖lpf ρ l₁ m₀ 0 f x‖ₑ)
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal CS * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
    have h := hSb l₁ (-(m₀ : ℤ)) hgS f
    rw [hpeq] at h
    have h0 : lpf ρ l₁ m₀ 0 f = Work.KMTContract.kmtProj ρ l₁ (-(m₀ : ℤ)) f := by
      funext y
      simp only [lpf]
      norm_num
    rw [MeasureTheory.eLpNorm_enorm (hf := by pw_aesm), h0]
    exact h
  -- step 3: the lacunary maximal piece, then the band square function
  have hpm : MeasureTheory.eLpNorm (partSumSup ρ l₁ m₀ f) p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (CL * CB + CL) * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
    have h1 := hLb l₁ m₀ hgL f
    have h2 := hBb l₁ m₀ hgB f
    calc MeasureTheory.eLpNorm (partSumSup ρ l₁ m₀ f) p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal CL *
              MeasureTheory.eLpNorm (sqFun ρ l₁ m₀ f) p MeasureTheory.Measure.count
            + ENNReal.ofReal CL * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := h1
      _ ≤ ENNReal.ofReal CL * (ENNReal.ofReal CB *
              MeasureTheory.eLpNorm f p MeasureTheory.Measure.count)
            + ENNReal.ofReal CL * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count :=
          add_le_add (mul_le_mul_of_nonneg_left h2 bot_le) le_rfl
      _ = ENNReal.ofReal (CL * CB + CL) * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hCLpos.le, ← add_mul,
            ← ENNReal.ofReal_add (mul_nonneg hCLpos.le hCBpos.le) hCLpos.le]
  -- step 4: the constant arithmetic
  refine hstep.trans ?_
  have hCS0 : (0 : ℝ) ≤ CS := hCSpos.le
  have hCL0 : (0 : ℝ) ≤ CL := hCLpos.le
  have hCB0 : (0 : ℝ) ≤ CB := hCBpos.le
  have hl0 : (0 : ℝ) ≤ (l₁ : ℝ) := Nat.cast_nonneg l₁
  calc MeasureTheory.eLpNorm (fun x : ℤ => ‖lpf ρ l₁ m₀ 0 f x‖ₑ)
          p MeasureTheory.Measure.count
        + MeasureTheory.eLpNorm (partSumSup ρ l₁ m₀ f) p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal CS * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count
        + ENNReal.ofReal (CL * CB + CL) * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count :=
          add_le_add hfirst hpm
    _ = ENNReal.ofReal (CS + (CL * CB + CL)) *
          MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
          rw [← add_mul, ← ENNReal.ofReal_add hCS0 (by positivity)]
    _ ≤ ENNReal.ofReal ((CS + CL * CB + CL) * (1 + (l₁ : ℝ)) ^ 2) *
          MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
          refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
          have heq : CS + (CL * CB + CL) = CS + CL * CB + CL := by ring
          rw [heq]
          have h1 : (1 : ℝ) ≤ (1 + (l₁ : ℝ)) ^ 2 := by nlinarith
          exact le_mul_of_one_le_right (by positivity) h1

end

/-- **The target from the `l`-free values-maximal estimate** — the paper's `(lin-1)`, i.e. the crux
in its shortest form.  The target is *literally the same statement* with the relaxed constant
`C(1+l₁)²` in place of `C`, so this is the shortest known bridge from a crux statement to the
assignment (and it shows that the `(1+l₁)²` in the target's constant is a red herring: the real
content is `l`-uniformity). -/
theorem lowpassMaximal_of_valuesMaximal
    (hVM : ∀ (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤),
      ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
        Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
        MeasureTheory.eLpNorm (fun x : ℤ => supPart 2 (fun m : ℕ => lpf ρ l₁ m₀ m f x))
          p MeasureTheory.Measure.count
          ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤)
    (r : NNReal) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ => supPart r (fun m : ℕ => lpf ρ l₁ m₀ m f x))
        p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * (1 + (l₁ : ℝ)) ^ 2) *
            MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  obtain ⟨Cρ, hCρ, C, hC, hb⟩ := hVM ρ hρ hρ1 p hp hptop
  refine ⟨Cρ, hCρ, C, hC, ?_⟩
  intro l₁ m₀ hgood f
  refine (hb l₁ m₀ hgood f).trans ?_
  refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
  have hl : (0 : ℝ) ≤ (l₁ : ℝ) := Nat.cast_nonneg _
  have h1 : (1 : ℝ) ≤ (1 + (l₁ : ℝ)) ^ 2 := by nlinarith
  exact le_mul_of_one_le_right hC.le h1

/-- **The target from the `l`-free values-maximal estimate for `ℓᵖ` inputs.**  All the proved
machinery of this chapter (the uniform single-scale bound, the band square function, the per-block
reverse Littlewood--Paley `A7Hi2.perKLeSqFun_of_memLp`, the chain/variational chapters) is stated
for inputs in `ℓᵖ`, so the crux should be formulated that way; and that is *enough* for the
target: if `f ∉ ℓᵖ` then `eLpNorm f p count = ⊤` (every function on `(ℤ, count)` is measurable, so
`¬ MemLp` forces `eLpNorm = ⊤`) and the target's right-hand side is `⊤`. -/
theorem lowpassMaximal_of_valuesMaximalLp
    (hVM : ∀ (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤),
      ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
        Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
        MeasureTheory.MemLp f p MeasureTheory.Measure.count →
        MeasureTheory.eLpNorm (fun x : ℤ => supPart 2 (fun m : ℕ => lpf ρ l₁ m₀ m f x))
          p MeasureTheory.Measure.count
          ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤)
    (r : NNReal) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ => supPart r (fun m : ℕ => lpf ρ l₁ m₀ m f x))
        p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * (1 + (l₁ : ℝ)) ^ 2) *
            MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  obtain ⟨Cρ, hCρ, C, hC, hb⟩ := hVM ρ hρ hρ1 p hp hptop
  refine ⟨Cρ, hCρ, C, hC, ?_⟩
  intro l₁ m₀ hgood f
  by_cases hf : MeasureTheory.MemLp f p MeasureTheory.Measure.count
  · refine (hb l₁ m₀ hgood f hf).trans ?_
    refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
    have hl : (0 : ℝ) ≤ (l₁ : ℝ) := Nat.cast_nonneg _
    have h1 : (1 : ℝ) ≤ (1 + (l₁ : ℝ)) ^ 2 := by nlinarith
    exact le_mul_of_one_le_right hC.le h1
  · have htop : MeasureTheory.eLpNorm f p MeasureTheory.Measure.count = ⊤ := by
      have haesm : MeasureTheory.AEStronglyMeasurable f (MeasureTheory.Measure.count : Measure ℤ) :=
        (measurable_of_countable f).aestronglyMeasurable
      exact top_le_iff.mp (le_of_not_gt fun hlt => hf hlt)
    have hD : ENNReal.ofReal (C * (1 + (l₁ : ℝ)) ^ 2) ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos hC (by positivity)))
    rw [htop, ENNReal.mul_top hD]
    exact le_top

/-- **The values-supremum (maximal) estimate for the low-pass Ionescu--Wainger projections on the
good major arcs**, uniformly in the arithmetic height `l₁` and in the base level `m₀`.

**State of this file (session 10).**  The target is *reduced* to a single named statement of the
workspace, in two *independent* ways:

* `lowpassMaximal_of_lacunaryMaxPiece` above: the target follows from
  `Work.KMTAreas.A7Hi2.lacunaryMaxPiece` (the `sqFun` form with the extra additive `C‖f‖_p` term)
  together with the PROVED `A7.kmtProj_lp_bound_uniform` and the PROVED `A7Lpd.bandSquareUnif`;
* the proof below: the target follows from the PROVED `Work.KMTAreas.A7Lpd.maximal`, i.e. from
  `Work.KMTAreas.A7Lpd.lacunaryMaxFun` (the `sqFun` form *without* the additive term) + the PROVED
  `A7Lpd.bandSquareUnif` + the PROVED `A7.kmtProj_lp_bound_uniform` — this is the `A7Lpd` chapter's
  assembly, and it delivers the *stronger* constant `C(1+l₁)` (so `C(1+l₁) ≤ C(1+l₁)²` is free).

So the remaining mathematical content of the target is exactly the **Ionescu--Wainger maximal
estimate** for the low-pass family on the good major arcs, with the polynomial loss `(1+l₁)²`.
That content is **proved** in `Submission/Work/KMTAreas/A7Hi2/supPieceClean.lean`, i.e.
`Work.KMTAreas.A7Hi2.supPieceClean : Work.KMTAreas.A7Hi2.SupPiece`, whose statement unfolds to
*verbatim* the statement below; the proof of the target is therefore the one-line transport of that
theorem (see the proof term).  The mathematics of `supPieceClean` is the **deep/shallow split** at
the cut level

  `Work.KMTAreas.A7Hi2.cutLevel ρ l₁ = clog 2 (3 · iwQl ρ l₁) + 2`,

the level at which the low-pass bump becomes narrower than the lattice spacing `1/iwQl ρ l₁`:

* **deep range** (`cutLevel ρ l₁ ≤ m₀ + m`): the Magyar--Stein--Wainger decimation factorisation
  `Work.KMTAreas.A7Hi.lpf_decim_fact` identifies the projection with `Q = iwQl ρ l₁` times a
  *decimated dilation family* of the fixed coarse projection `Π_{≤l₁,≤-C₀}f`, whose variational norm
  is bounded by `(C/Q)‖g‖_{ℓᵖ}` with an **absolute** constant
  (`Work.A7Hi2.decimDilVarUnif`); the factor `Q` cancels, and the coarse projection is controlled by
  the `l₁`-free single-scale bound `Work.KMTAreas.A7.kmtProj_lp_bound_uniform`
  (`Work.KMTAreas.A7Hi2.supDeepLe`, proved in `A7Hi2/supDeepAux.lean`);
* **shallow range** (`m₀ + m < cutLevel ρ l₁`): only `O(1 + l₁)` levels occur, so the truncated
  `2`-variation is decomposed by the one-dimensional Rademacher--Men'shov inequality into
  `log₂ (cutLevel ρ l₁) + 1 = O(1 + l₁)` dyadic blocks, each of which is bounded by the per-block band
  square function `Work.KMTAreas.A7Lpd.singleChain_blockSqSum_le` with an `l₁`-free constant.  This
  logarithmic count of scales is exactly where the target's `(1+l₁)²` is spent
  (`Work.KMTAreas.A7Hi2.supShallowLe`, proved in `A7Hi2/supShallowLe.lean`).

The two halves are assembled by `Work.KMTAreas.A7Hi2.supPiece_of_supDeep_supShallow`.  The
reductions proved in this file *below* the target's statement
(`lowpassMaximal_of_lacunaryMaxPiece`, `lowpassMaximal_of_valuesMaximal`,
`lowpassMaximal_of_valuesMaximalLp`, all axiom-clean) remain as the documented links
from the `A7Lpd` Men'shov/chainPart variational chapter to this statement; they are no longer needed
for the target itself.

`#print axioms Work.KMTAreas.A7Hi.LowpassMaximal` is `[propext, Classical.choice, Quot.sound]`. -/
theorem LowpassMaximal (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p)
    (hptop : p < ⊤) (r : NNReal) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ => supPart r (fun m : ℕ => lpf ρ l₁ m₀ m f x))
        p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * (1 + (l₁ : ℝ)) ^ 2) *
            MeasureTheory.eLpNorm f p MeasureTheory.Measure.count :=
  Work.KMTAreas.A7Hi2.supPieceClean ρ hρ hρ1 p hp hptop r

end Work.KMTAreas.A7Hi
