import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Gates
import Submission.Work.Pert.Qm_slice
import Submission.Work.Pert.DE_open
import Submission.Work.L62.basin_iface
import Submission.Work.Pert.pert2v2.equiv_transport
import Submission.Work.Pert.pert2v2.HsegRow
import Submission.Work.Pert.pert2v2.EfFloorDiffV2.EfFloor_sub_id_differentiableOn
import Submission.Work.Pert.pert2v2.HdiffRow.EfFloor_hdiff_of_step
import Submission.Work.Pert.MaxDom
import Submission.Work.Pert.pert2v2.EfFloorDiffV2.Prelim
import Submission.Work.Pert.RBlock4.retOf_holo
import Submission.Work.Parab.inversion.deriv_ne_zero_of_injOn

/-!
# `Work.Pert.pert2v2.RBlockCharts` — the window arithmetic of the two gates

The two-piece return map of `pert2v2` needs two elementary geometric facts about the gates
`Qm Ξ α`, `Qp Ξ α` (`Work.Pert.Setup`) at **high height with bounded real part**:

* **(window)** a point with `|Re| ≤ B` and `Im ≥ y` (with `y` linear in `B`, `Ξ`, `|1/α|`) lies in
  **both** gates (`window_subset_gates`); this is what makes "the same points" usable in either
  gate;
* **(near-translation)** if `F` is a near-translation on `Qm Ξ α` (`MandelDim.NearTranslationOn`)
  and `ς ∈ Qm Ξ α` has bounded real part and high imaginary part, then `F ς` still lies in **both**
  gates (`F_mem_gates`); this is the gate-invariance used by `herb1`/`hdiff` and by the
  `+1`-relation of the low chart.

Also here: the `ℤ`-equivariance of the datum's horn map `d.E` along the *whole* invariant domain
`d.DE` (`E_add_int_DE`), which is what the transport of `R_close` uses
(`basin_iface` gives `IsTInvariant d.DE` and `d.E (w+1) = d.E w + 1` on `d.DE`).
-/

namespace Work.Pert.pert2v2

open _root_.MandelDim Complex Set Metric
open scoped Topology

noncomputable section

variable {f₀ : ℂ → ℂ} {D₀ : Set ℂ}

/-- **The `ℤ`-equivariance of the datum's horn map on its domain.**  `d.E (w + k) = d.E w + k` for
every `w ∈ d.DE` and every `k : ℤ` (whence, by `basin_iface`, for the whole `T`-invariant `d.DE`). -/
theorem E_add_int_DE (d : MandelDim.ParabData f₀ D₀) (hd : MandelDim.IsParabolicGerm f₀ D₀) :
    ∀ (k : ℤ) (w : ℂ), w ∈ d.DE → d.E (w + (k : ℂ)) = d.E w + (k : ℂ) := by
  obtain ⟨-, -, -, hTinv, hE1, -⟩ :=
    Work.L62.basin_iface f₀ D₀ d hd (fun z hz n => d.orbit_avoid z hz n)
  exact E_add_int hTinv (fun w hw _ => hE1 w hw)

/-- **The window of the two gates.**  Any point of the half plane `{Im ≥ y}` whose real part is
bounded by `B` lies in both gates `Qm Ξ α` and `Qp Ξ α`, provided `y` is at least
`4 * (B + Ξ) + |Re (1/α)| + |Im (1/α)| + 4`. -/
theorem window_subset_gates {Ξ B y : ℝ} {α : ℂ} (hΞ : 0 ≤ Ξ) (hB : 0 ≤ B)
    (hy : 4 * (B + Ξ) + |(1 / α).re| + |(1 / α).im| + 4 ≤ y) :
    {w : ℂ | |w.re| ≤ B ∧ y ≤ w.im} ⊆ Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α := by
  intro w hw
  obtain ⟨hre, him⟩ := hw
  have hy0 : 0 ≤ y := by linarith [abs_nonneg (1 / α).re, abs_nonneg (1 / α).im]
  have him0 : 0 ≤ w.im := le_trans hy0 him
  have habs : |w.im| = w.im := abs_of_nonneg him0
  rw [Set.mem_inter_iff, Work.Pert.Qm_mem_iff, Work.Pert.Qp_mem_iff]
  have h3 : w.im ≥ 4 * (B + Ξ) + |(1 / α).re| + |(1 / α).im| + 4 := le_trans hy him
  have hAre : (0 : ℝ) ≤ |(1 / α).re| := abs_nonneg _
  have hAim : (0 : ℝ) ≤ |(1 / α).im| := abs_nonneg _
  have hreL : -B ≤ w.re := (abs_le.mp hre).1
  have hreR : w.re ≤ B := (abs_le.mp hre).2
  -- the two triangle inequalities in the coordinates of `1/α`
  have htri1 : w.im - |(1 / α).im| ≤ |w.im + (1 / α).im| := by
    have h := abs_sub_abs_le_abs_sub w.im (-(1 / α).im)
    rw [abs_neg, sub_neg_eq_add] at h
    rwa [habs] at h
  have htri2 : w.im - |(1 / α).im| ≤ |w.im - (1 / α).im| := by
    have h := abs_sub_abs_le_abs_sub w.im (1 / α).im
    rwa [habs] at h
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · -- `Ξ - Re (1/α) - |Im w + Im (1/α)| < Re w`
    have h4 : -|(1 / α).re| ≤ (1 / α).re := neg_abs_le _
    linarith
  · -- `Re w < |Im w| - Ξ`
    rw [habs]
    linarith
  · -- `Ξ - |Im w| < Re w`
    rw [habs]
    linarith
  · -- `Re w < Re (1/α) - Ξ + |Im w - Im (1/α)|`
    have h4 : -|(1 / α).re| ≤ (1 / α).re := neg_abs_le _
    linarith

/-- **`F` preserves both gates on the window.**  If `F` is a near-translation on the lower gate and
`ς ∈ Qm Ξ α` has `|Re ς| ≤ B` and high imaginary part, then `F ς` is still in *both* gates.  The
point of having both: the return map's low piece uses the lower gate while the walk conditions and
the Abel equations are proved on the upper one. -/
theorem F_mem_gates {Ξ B y : ℝ} {α : ℂ} {F : ℂ → ℂ} {ς : ℂ}
    (hΞ : 0 ≤ Ξ) (hB : 0 ≤ B)
    (hy : 4 * ((B + 2) + Ξ) + |(1 / α).re| + |(1 / α).im| + 4 ≤ y)
    (hNT : MandelDim.NearTranslationOn F (Work.Pert.Qm Ξ α))
    (hς : ς ∈ Work.Pert.Qm Ξ α) (hre : |ς.re| ≤ B) (him : y + 2 ≤ ς.im) :
    F ς ∈ Work.Pert.Qm Ξ α ∧ F ς ∈ Work.Pert.Qp Ξ α := by
  have hclose := (hNT.2 ς hς).1
  have h1 : |(F ς - (ς + 1)).re| ≤ 1 / 32 :=
    le_trans (Complex.abs_re_le_norm _) hclose
  have h2 : |(F ς - (ς + 1)).im| ≤ 1 / 32 :=
    le_trans (Complex.abs_im_le_norm _) hclose
  have hreF : |(F ς).re| ≤ B + 2 := by
    have h3 : (F ς).re - (ς.re + 1) = (F ς - (ς + 1)).re := by simp
    have h4 : |(F ς).re - (ς.re + 1)| ≤ 1 / 32 := by rw [h3]; exact h1
    have h5 : |(F ς).re| ≤ |(F ς).re - (ς.re + 1)| + |ς.re + 1| := by
      calc |(F ς).re| = |((F ς).re - (ς.re + 1)) + (ς.re + 1)| := by ring_nf
        _ ≤ |(F ς).re - (ς.re + 1)| + |ς.re + 1| := abs_add_le _ _
    have h6 : |ς.re + 1| ≤ B + 1 := by
      calc |ς.re + 1| ≤ |ς.re| + |(1 : ℝ)| := abs_add_le _ _
        _ = |ς.re| + 1 := by simp
        _ ≤ B + 1 := by linarith
    linarith
  have himF : y ≤ (F ς).im := by
    have h3 : (F ς).im - ς.im = (F ς - (ς + 1)).im := by simp
    have h4 : |(F ς).im - ς.im| ≤ 1 / 32 := by rw [h3]; exact h2
    have h5 := (abs_le.mp h4).1
    linarith
  have := window_subset_gates (Ξ := Ξ) (B := B + 2) (y := y) (α := α) hΞ (by linarith) hy
  exact this ⟨hreF, himF⟩

/-! ## The canonical-representative walk step (the `hstep` data of `hdiff`)

`pert2v2.herb1_hlvl_of_step` / `HdiffRow.EfFloor_hdiff_of_step` need, at the canonical
representative `r w := w - ⌊Re w⌋` of every point of the half plane, the *one-step* data

* `ς w := invOn Φm Q (r w) ∈ Qm Ξ α ∩ Qp Ξ α` (the gate point is in both gates),
* `F (ς w) ∈ Qm Ξ α ∩ Qp Ξ α` (the walk step stays in both gates).

Both are pure consequences of the window geometry above and the *deviation* of the gate
coordinate from the identity in the window (`‖Φm z - z‖ ≤ C` at heights `≥ y`), which the
upper-end asymptotics `pert2v2.gate_coord_end_asymptotic_Qm` provides. -/

/-- **The window deviation bound** from the upper-end asymptotics of a gate coordinate: there are
`Y` and (implicitly) `C` such that `‖Φm z - z‖ ≤ C` on the window `|Re z| ≤ 2` at heights `≥ Y`. -/
theorem exists_dev_bound_of_end {Ξ : ℝ} {α : ℂ} {Φm : ℂ → ℂ} {c : ℂ}
    (hEnd : ∀ x : ℝ, ∀ ε > 0, ∃ Y' : ℝ, ∀ z ∈ Work.Pert.Qm Ξ α, Y' < z.im → |z.re - x| ≤ 2 →
      ‖Φm z - z - c‖ < ε) :
    ∃ Y C : ℝ, 0 ≤ C ∧ ∀ z ∈ Work.Pert.Qm Ξ α, Y ≤ z.im → |z.re| ≤ 2 → ‖Φm z - z‖ ≤ C := by
  obtain ⟨Y', hY'⟩ := hEnd 0 1 one_pos
  refine ⟨max Y' 0 + 1, ‖c‖ + 1, by positivity, fun z hz him hre => ?_⟩
  have hlt : Y' < z.im := by
    have h : max Y' 0 < z.im := by linarith
    exact lt_of_le_of_lt (le_max_left Y' 0) h
  have h1 := hY' z hz hlt (by simpa using hre)
  have h2 : ‖Φm z - z‖ ≤ ‖Φm z - z - c‖ + ‖c‖ := by
    calc ‖Φm z - z‖ = ‖(Φm z - z - c) + c‖ := by ring_nf
      _ ≤ ‖Φm z - z - c‖ + ‖c‖ := norm_add_le _ _
  linarith

/-- **The one-step data of the canonical representative.**  For `w` at height `≥ y` with the
canonical representative `r w := w - ⌊Re w⌋` a gate value (`herb` = the cover), the gate point
`ς w := invOn Φm Q (r w)` and its `F`-image both lie in **both** gates.

The two localisation inputs are the *only* analytic content:

* `hpre_re` — the `Re`-confinement of the gate preimage (for the canonical representatives it is
  `pert2v2.GatePreimageReBound.gate_preimage_re_bound`, at the window `0 ≤ Re < 1`);
* `hpre_im` — its height: the preimage of a point at height `≥ y` is at height `≥ Z` (the walk to
  the window costs only a bounded amount of height, `Z = y - O(1)`). -/
theorem canon_step_data {Ξ Z B y : ℝ} {α : ℂ} {Φm F : ℂ → ℂ}
    (hΞ : 0 ≤ Ξ) (hB : 0 ≤ B)
    (hy : 4 * ((B + 2) + Ξ) + |(1 / α).re| + |(1 / α).im| + 4 ≤ Z - 2)
    (hNT : MandelDim.NearTranslationOn F (Work.Pert.Qm Ξ α))
    (hpre_re : ∀ w : ℂ, y ≤ w.im → w - (((⌊w.re⌋ : ℤ)) : ℂ) ∈ Φm '' Work.Pert.Qm Ξ α →
      |(Work.Pert.invOn Φm (Work.Pert.Qm Ξ α) (w - (((⌊w.re⌋ : ℤ)) : ℂ))).re| ≤ B)
    (hpre_im : ∀ w : ℂ, y ≤ w.im → w - (((⌊w.re⌋ : ℤ)) : ℂ) ∈ Φm '' Work.Pert.Qm Ξ α →
      Z ≤ (Work.Pert.invOn Φm (Work.Pert.Qm Ξ α) (w - (((⌊w.re⌋ : ℤ)) : ℂ))).im) :
    ∀ w : ℂ, y ≤ w.im →
      w - (((⌊w.re⌋ : ℤ)) : ℂ) ∈ Φm '' Work.Pert.Qm Ξ α →
      (Work.Pert.invOn Φm (Work.Pert.Qm Ξ α) (w - (((⌊w.re⌋ : ℤ)) : ℂ))
          ∈ Work.Pert.Qm Ξ α ∧
        Work.Pert.invOn Φm (Work.Pert.Qm Ξ α) (w - (((⌊w.re⌋ : ℤ)) : ℂ))
          ∈ Work.Pert.Qp Ξ α ∧
        F (Work.Pert.invOn Φm (Work.Pert.Qm Ξ α) (w - (((⌊w.re⌋ : ℤ)) : ℂ)))
          ∈ Work.Pert.Qm Ξ α ∧
        F (Work.Pert.invOn Φm (Work.Pert.Qm Ξ α) (w - (((⌊w.re⌋ : ℤ)) : ℂ)))
          ∈ Work.Pert.Qp Ξ α) := by
  intro w hw hmem
  set ς : ℂ := Work.Pert.invOn Φm (Work.Pert.Qm Ξ α) (w - (((⌊w.re⌋ : ℤ)) : ℂ)) with hς
  have hςQ : ς ∈ Work.Pert.Qm Ξ α := Work.Pert.invOn_mem hmem
  have hreς : |ς.re| ≤ B := hpre_re w hw hmem
  have himς : Z ≤ ς.im := hpre_im w hw hmem
  have hZ : 0 ≤ Z := by
    have h1 : (0 : ℝ) ≤ |(1 / α).re| := abs_nonneg _
    have h2 : (0 : ℝ) ≤ |(1 / α).im| := abs_nonneg _
    linarith
  -- `ς` itself lies in both gates
  have hwin : ς ∈ Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α :=
    window_subset_gates (Ξ := Ξ) (B := B) (y := Z) (α := α) hΞ hB (by linarith) ⟨hreς, himς⟩
  -- and so does `F ς`
  have hF : F ς ∈ Work.Pert.Qm Ξ α ∧ F ς ∈ Work.Pert.Qp Ξ α :=
    F_mem_gates (Ξ := Ξ) (B := B) (y := Z - 2) (α := α) hΞ hB hy hNT hςQ hreς (by linarith)
  exact ⟨hςQ, hwin.2, hF.1, hF.2⟩

/-! ## The `hdiff` row of (A.4.4) from the canonical-representative step data

`HdiffRow.EfFloor_hdiff_of_step` needs the walk step of the canonical representative; combining it
with `canon_step_data` gives the `hdiff` input of `pert2v2.a44_row` directly.  The same data
produces `herb1`/`hlvl` (`pert2v2.herb1_hlvl_of_step`), the hypotheses of
`EfFloorDiffV2.EfFloor_sub_id_differentiableOn`. -/

/-- **`hdiff` for the `(A.4.4)` row** — `EfFloor Φm Φp (Qm Ξ α) - id` is holomorphic on the half
plane `{y ≤ Im}`, assuming the cover (`herb`) and the two localisation inputs for the canonical
representative. -/
theorem EfFloor_hdiff_of_pre {Ξ Z B y : ℝ} {α : ℂ} {Φm Φp F : ℂ → ℂ}
    (hΞ : 0 ≤ Ξ) (hB : 0 ≤ B) (hy : 4 * ((B + 2) + Ξ) + |(1 / α).re| + |(1 / α).im| + 4 ≤ Z - 2)
    (hNT : MandelDim.NearTranslationOn F (Work.Pert.Qm Ξ α))
    (hΦm : MandelDim.IsFatouCoordOn F Φm (Work.Pert.Qm Ξ α))
    (hΦp : MandelDim.IsFatouCoordOn F Φp (Work.Pert.Qp Ξ α))
    (hpre_re : ∀ w : ℂ, y ≤ w.im → w - (((⌊w.re⌋ : ℤ)) : ℂ) ∈ Φm '' Work.Pert.Qm Ξ α →
      |(Work.Pert.invOn Φm (Work.Pert.Qm Ξ α) (w - (((⌊w.re⌋ : ℤ)) : ℂ))).re| ≤ B)
    (hpre_im : ∀ w : ℂ, y ≤ w.im → w - (((⌊w.re⌋ : ℤ)) : ℂ) ∈ Φm '' Work.Pert.Qm Ξ α →
      Z ≤ (Work.Pert.invOn Φm (Work.Pert.Qm Ξ α) (w - (((⌊w.re⌋ : ℤ)) : ℂ))).im)
    (herb : ∀ w : ℂ, y ≤ w.im → w - (((⌊w.re⌋ : ℤ)) : ℂ) ∈ Φm '' Work.Pert.Qm Ξ α) :
    DifferentiableOn ℂ
      (fun w : ℂ => Work.Pert.pert2v2.EfFloor Φm Φp (Work.Pert.Qm Ξ α) w - w)
      {w : ℂ | y ≤ w.im} := by
  have hQopen : IsOpen (Work.Pert.Qm Ξ α) := Work.Pert.RBlock4.isOpen_Qm Ξ α
  have hQpopen : IsOpen (Work.Pert.Qp Ξ α) := by
    unfold Work.Pert.Qp; exact Work.Fatou.Qreg.isOpen_Qreg _ _
  have hder : ∀ z ∈ Work.Pert.Qm Ξ α, deriv Φm z ≠ 0 :=
    Work.Parab.inversion.deriv_ne_zero_of_injOn hQopen hΦm.1 hΦm.2.1
  have hstep : ∀ w : ℂ, y ≤ w.im →
      F (Work.Pert.invOn Φm (Work.Pert.Qm Ξ α) (w - (((⌊w.re⌋ : ℤ)) : ℂ)))
        ∈ Work.Pert.Qm Ξ α :=
    fun w hw => (canon_step_data hΞ hB hy hNT hpre_re hpre_im w hw (herb w hw)).2.2.1
  have hςP : ∀ w : ℂ, y ≤ w.im →
      Work.Pert.invOn Φm (Work.Pert.Qm Ξ α) (w - (((⌊w.re⌋ : ℤ)) : ℂ))
        ∈ Work.Pert.Qp Ξ α :=
    fun w hw => (canon_step_data hΞ hB hy hNT hpre_re hpre_im w hw (herb w hw)).2.1
  have hstepP : ∀ w : ℂ, y ≤ w.im →
      F (Work.Pert.invOn Φm (Work.Pert.Qm Ξ α) (w - (((⌊w.re⌋ : ℤ)) : ℂ)))
        ∈ Work.Pert.Qp Ξ α :=
    fun w hw => (canon_step_data hΞ hB hy hNT hpre_re hpre_im w hw (herb w hw)).2.2.2
  exact Work.Pert.pert2v2.HdiffRow.EfFloor_hdiff_of_step (Q := Work.Pert.Qm Ξ α)
    (Qp := Work.Pert.Qp Ξ α) (F := F) hQopen hQpopen hΦm.1 hder hΦm.2.1 hΦp.1 herb hstep
    hΦm.2.2 hςP hstepP hΦp.2.2

/-- **`herb1` and the level-1 value relation** from the same canonical-representative data (the
hypotheses of `EfFloorDiffV2.EfFloor_sub_id_differentiableOn`). -/
theorem herb1_hlvl_of_pre {Ξ Z B y : ℝ} {α : ℂ} {Φm Φp F : ℂ → ℂ}
    (hΞ : 0 ≤ Ξ) (hB : 0 ≤ B) (hy : 4 * ((B + 2) + Ξ) + |(1 / α).re| + |(1 / α).im| + 4 ≤ Z - 2)
    (hNT : MandelDim.NearTranslationOn F (Work.Pert.Qm Ξ α))
    (hΦm : MandelDim.IsFatouCoordOn F Φm (Work.Pert.Qm Ξ α))
    (hΦp : MandelDim.IsFatouCoordOn F Φp (Work.Pert.Qp Ξ α))
    (hpre_re : ∀ w : ℂ, y ≤ w.im → w - (((⌊w.re⌋ : ℤ)) : ℂ) ∈ Φm '' Work.Pert.Qm Ξ α →
      |(Work.Pert.invOn Φm (Work.Pert.Qm Ξ α) (w - (((⌊w.re⌋ : ℤ)) : ℂ))).re| ≤ B)
    (hpre_im : ∀ w : ℂ, y ≤ w.im → w - (((⌊w.re⌋ : ℤ)) : ℂ) ∈ Φm '' Work.Pert.Qm Ξ α →
      Z ≤ (Work.Pert.invOn Φm (Work.Pert.Qm Ξ α) (w - (((⌊w.re⌋ : ℤ)) : ℂ))).im)
    (herb : ∀ w : ℂ, y ≤ w.im → w - (((⌊w.re⌋ : ℤ)) : ℂ) ∈ Φm '' Work.Pert.Qm Ξ α) :
    (∀ w : ℂ, y ≤ w.im → (w - (((⌊w.re⌋ : ℤ)) : ℂ)) + 1 ∈ Φm '' Work.Pert.Qm Ξ α) ∧
      (∀ w : ℂ, y ≤ w.im → w - (((⌊w.re⌋ : ℤ)) : ℂ) + 1 ∈ Φm '' Work.Pert.Qm Ξ α →
        Φp (Work.Pert.invOn Φm (Work.Pert.Qm Ξ α) (w - (((⌊w.re⌋ : ℤ)) : ℂ) + 1))
          = Φp (Work.Pert.invOn Φm (Work.Pert.Qm Ξ α) (w - (((⌊w.re⌋ : ℤ)) : ℂ))) + 1) :=
  herb1_hlvl_of_step hΦm.2.1 hΦm.2.2
    (fun w hw => (canon_step_data hΞ hB hy hNT hpre_re hpre_im w hw (herb w hw)).2.2.1)
    hΦp.2.2
    (fun w hw => (canon_step_data hΞ hB hy hNT hpre_re hpre_im w hw (herb w hw)).2.1)
    (fun w hw => (canon_step_data hΞ hB hy hNT hpre_re hpre_im w hw (herb w hw)).2.2.2)
    herb


/-- **Continuity of the chosen preimage `Work.Pert.invOn τ Q` at a value `τ z`**, for holomorphic
injective `τ` on an open `Q ∋ z` with `deriv τ z ≠ 0`.  (Near `τ z` the chosen preimage *is* the
holomorphic local inverse of `τ`, by `Work.Pert.invOn_eventuallyEq_localInverse`.) -/
theorem invOn_continuousAt {τ : ℂ → ℂ} {Q : Set ℂ} (hQ : IsOpen Q)
    (hτ : DifferentiableOn ℂ τ Q) (hinj : Set.InjOn τ Q) {z : ℂ} (hz : z ∈ Q)
    (hder : deriv τ z ≠ 0) :
    ContinuousAt (fun v : ℂ => Work.Pert.invOn τ Q v) (τ z) := by
  obtain ⟨g, hga, -, hev⟩ := Work.Pert.invOn_eventuallyEq_localInverse hQ hτ hinj hz hder
  have himg : τ '' Q ∈ 𝓝 (τ z) :=
    Work.Pert.pert2v2.EfFloorDiffV2.mem_nhds_image_of_deriv_ne_zero hQ hτ hz hder
  refine hga.continuousAt.congr ?_
  filter_upwards [hev, himg] with v hv hvv
  exact (hv hvv).symm


end

end Work.Pert.pert2v2
