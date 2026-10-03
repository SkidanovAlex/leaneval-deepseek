import Mathlib
import Submission.Work.Horn.fatouQ_defs
import Submission.Work.Horn.petal_mapsTo
import Submission.Work.Horn.injOn_ball

/-!
# The chart dictionary for the general-`q` Leau–Fatou construction

Elementary consequences of `Flower.PetalFacts` used in the assembly of
`Work.Horn.exists_petal_fatouCoord_q`:

* `cc q a / w ∈ DM q a M ↔ M < w.re` (the chart maps `DM` onto the half plane `{Re w > M}`);
* the inverse chart `zBranch j` is a two-sided inverse of `chartQ` on the `j`-th petal;
* `chartQ` is injective on each petal.
-/

namespace Work.Horn.FatouQ

open Work.Horn.Flower Work.Horn

noncomputable section

/-- `cc / w` lies in the root disc `DM` exactly when `M < Re w`. -/
theorem cc_div_mem_DM_iff {q : ℕ} {a : ℂ} {M : ℝ} {w : ℂ} (hcc : cc q a ≠ 0) (hw : w ≠ 0) :
    cc q a / w ∈ DM q a M ↔ M < w.re := by
  have hne : cc q a / w ≠ 0 := div_ne_zero hcc hw
  have h1 : cc q a / (cc q a / w) = w := by field_simp
  rw [mem_DM_iff hne, h1]

/-- The chart of the inverse chart is the identity on the half plane `{Re w > M}`. -/
theorem chartQ_zBranch {q : ℕ} {a : ℂ} {M : ℝ} (hgeo : PetalFacts q a M) (hM : 0 < M)
    (j : Fin q) {w : ℂ} (hw : M < w.re) : chartQ q a (zBranch q a j w) = w := by
  have hcc : cc q a ≠ 0 := hgeo.cc_ne_zero
  have hw0 : w ≠ 0 := fun h => by rw [h] at hw; simp at hw; linarith
  have hmem : cc q a / w ∈ DM q a M := (cc_div_mem_DM_iff hcc hw0).mpr hw
  have hpow : (rootFun q a j (cc q a / w)) ^ q = cc q a / w := hgeo.rootFun_pow j (cc q a / w) hmem
  have hne : cc q a / w ≠ 0 := div_ne_zero hcc hw0
  show cc q a / (zBranch q a j w) ^ q = w
  rw [zBranch, hpow]
  field_simp

/-- The inverse chart of the chart is the identity on the `j`-th petal. -/
theorem zBranch_chartQ {q : ℕ} {a : ℂ} {M : ℝ} (hgeo : PetalFacts q a M) (j : Fin q)
    {z : ℂ} (hz : z ∈ petal q a M j) : zBranch q a j (chartQ q a z) = z := by
  obtain ⟨hzpos, hzq, hroot⟩ := (hgeo.mem_petal_iff j z).mp hz
  have hz0 : z ≠ 0 := norm_pos_iff.mp hzpos
  have hcc : cc q a ≠ 0 := hgeo.cc_ne_zero
  have hzq0 : z ^ q ≠ 0 := pow_ne_zero q hz0
  have h1 : cc q a / (cc q a / z ^ q) = z ^ q := by field_simp
  show rootFun q a j (cc q a / (cc q a / z ^ q)) = z
  rw [h1]
  exact hroot

/-- `chartQ` is injective on each petal. -/
theorem chartQ_injOn_petal {q : ℕ} {a : ℂ} {M : ℝ} (hgeo : PetalFacts q a M) (j : Fin q) :
    Set.InjOn (chartQ q a) (petal q a M j) := by
  intro z hz z' hz' h
  rw [← zBranch_chartQ hgeo j hz, ← zBranch_chartQ hgeo j hz', h]

end

end Work.Horn.FatouQ
