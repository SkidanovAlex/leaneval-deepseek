import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.RowIdentity.odd_rowH_aux
import Submission.Work.OddVolterra.Existence.hquot_contDiff

namespace Work.OddVolterra.RowIdentity

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

/-!
# Smoothness of the swept coefficient `AH`

`AH n h x y u σ` is the coefficient of the swept (Abel) integral of the odd centroid row: the
smooth factor obtained from the two frozen endpoint radicands `QyH`, `QxH` raised to the
half-integer power `n - 1/2` and multiplied by the two endpoint slope factors.

The point is that on the rectangle

`(s - δ, s + δ) × (s - δ, 1 + δ)`

every ingredient is smooth in the two variables `(u, σ)`: `h` is globally `C^∞`, `hquot` is the
divided difference of `h` hence jointly `C^∞`, `y` and `x` are `C^∞` on `Ioi 0` (which contains
the whole `σ`-range because `s - δ > 0`, so both they and their derivatives are `C^∞` there), and
the two radicands are *strictly positive* on the rectangle by hypothesis, which makes the
`rpow` with the non-integer exponent `n - 1/2` smooth as well.
-/

/-- The family `(u,σ) ↦ QyH h y u σ` is `C^∞` at `(p.1, p.2)` as soon as `h` is globally `C^∞`
and `y` is `C^∞` at `p.2`. -/
private lemma contDiffAt_QyH_family {h y : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) {p : ℝ × ℝ}
    (hy : ContDiffAt ℝ ∞ y p.2) :
    ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => QyH h y q.1 q.2) p := by
  have hq : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => hquot h q.1 q.2) p :=
    (Work.OddVolterra.Existence.hquot_contDiff hh).contDiffAt
  have hy2 : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => y q.2) p := by
    simpa only [Function.comp_def] using hy.comp p contDiffAt_snd
  have hh1 : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => h q.1) p := by
    simpa only [Function.comp_def] using hh.contDiffAt.comp p contDiffAt_fst
  have hh2 : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => h q.2) p := by
    simpa only [Function.comp_def] using hh.contDiffAt.comp p contDiffAt_snd
  have h1 : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => y q.2 + hquot h q.1 q.2) p := hy2.add hq
  have h2 : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => line h q.2 (y q.2)) p := by
    unfold line
    exact (contDiffAt_snd.mul hy2).add hh2
  have h3 : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => line h q.1 (y q.2)) p := by
    unfold line
    exact (contDiffAt_fst.mul hy2).add hh1
  unfold QyH
  exact h1.mul (h2.add h3)

/-- The same for `QxH h x`, since `QxH h x u σ = QyH h (fun σ => -(x σ)) u σ`. -/
private lemma contDiffAt_QxH_family {h x : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) {p : ℝ × ℝ}
    (hx : ContDiffAt ℝ ∞ x p.2) :
    ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => QxH h x q.1 q.2) p := by
  have hneg : ContDiffAt ℝ ∞ (fun σ : ℝ => -(x σ)) p.2 := hx.neg
  exact contDiffAt_QyH_family (y := fun σ => -(x σ)) hh hneg

/-- The family `(u,σ) ↦ lineSlope h u (y σ) = y σ + h'(u)` is `C^∞` at `(p.1, p.2)`. -/
private lemma contDiffAt_lineSlope_family {h y : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) {p : ℝ × ℝ}
    (hy : ContDiffAt ℝ ∞ y p.2) :
    ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => lineSlope h q.1 (y q.2)) p := by
  have hdh : ContDiff ℝ ∞ (deriv h) := by
    simpa [Function.iterate_one] using hh.iterate_deriv 1
  have hd1 : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => deriv h q.1) p := by
    simpa only [Function.comp_def] using hdh.contDiffAt.comp p contDiffAt_fst
  have hy2 : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => y q.2) p := by
    simpa only [Function.comp_def] using hy.comp p contDiffAt_snd
  unfold lineSlope
  exact hy2.add hd1

/-- The family `(u,σ) ↦ deriv g σ` is `C^∞` at `(p.1, p.2)` when `g` is `C^∞` at `p.2`. -/
private lemma contDiffAt_deriv_family {g : ℝ → ℝ} {p : ℝ × ℝ}
    (hg : ContDiffAt ℝ ∞ g p.2) :
    ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => deriv g q.2) p := by
  have h1 : ContDiffAt ℝ ∞ (deriv g) p.2 := hg.derivWithin (le_of_eq (by simp))
  simpa only [Function.comp_def] using h1.comp p contDiffAt_snd

/-- **Smoothness of the swept coefficient `AH`.**  On the rectangle
`(s - δ, s + δ) × (s - δ, 1 + δ)` the coefficient `AH n h x y` of the odd centroid row is `C^∞`.

The hypotheses are exactly the ones available in the row identity: `h` is globally `C^∞`, the
curve coordinates `x`, `y` are `C^∞` on `Ioi 0` — and the whole `σ`-range lies in `Ioi 0`
because `s - δ > 0` — while the two frozen radicands `QyH`, `QxH` are strictly positive on the
rectangle, so that the non-integer powers `(n - 1/2)` are smooth. -/
theorem contDiffOn_AH {n : ℕ} {s δ : ℝ} (hsδ : 0 < s - δ) {h x y : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hx : ContDiffOn ℝ (⊤ : ℕ∞) x (Set.Ioi 0)) (hy : ContDiffOn ℝ (⊤ : ℕ∞) y (Set.Ioi 0))
    (hQ : ∀ u σ : ℝ, u ∈ Set.Ioo (s - δ) (s + δ) → σ ∈ Set.Ioo (s - δ) (1 + δ) →
      0 < QyH h y u σ ∧ 0 < QxH h x u σ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => AH n h x y p.1 p.2)
      (Set.Ioo (s - δ) (s + δ) ×ˢ Set.Ioo (s - δ) (1 + δ)) := by
  intro p hp
  -- `σ = p.2` lies in `Ioi 0`, where `x` and `y` are smooth.
  have hp2pos : 0 < p.2 := by linarith [hp.2.1, hsδ]
  have hy_at : ContDiffAt ℝ ∞ y p.2 := hy.contDiffAt (isOpen_Ioi.mem_nhds hp2pos)
  have hx_at : ContDiffAt ℝ ∞ x p.2 := hx.contDiffAt (isOpen_Ioi.mem_nhds hp2pos)
  have hQp := hQ p.1 p.2 hp.1 hp.2
  -- the two frozen radicands, as `C^∞` families
  have hQy : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => QyH h y q.1 q.2) p :=
    contDiffAt_QyH_family hh hy_at
  have hQx : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => QxH h x q.1 q.2) p :=
    contDiffAt_QxH_family hh hx_at
  -- their half-integer powers, well defined since both are strictly positive
  have hPy : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => (QyH h y q.1 q.2) ^ ((n : ℝ) - 1 / 2)) p :=
    hQy.rpow (contDiffAt_const (c := (n : ℝ) - 1 / 2)) (ne_of_gt hQp.1)
  have hPx : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => (QxH h x q.1 q.2) ^ ((n : ℝ) - 1 / 2)) p :=
    hQx.rpow (contDiffAt_const (c := (n : ℝ) - 1 / 2)) (ne_of_gt hQp.2)
  -- the four remaining factors
  have hLy : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => lineSlope h q.1 (y q.2)) p :=
    contDiffAt_lineSlope_family hh hy_at
  have hLx : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => lineSlope h q.1 (-(x q.2))) p := by
    have hneg : ContDiffAt ℝ ∞ (fun σ : ℝ => -(x σ)) p.2 := hx_at.neg
    exact contDiffAt_lineSlope_family hh hneg
  have hdy : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => deriv y q.2) p := contDiffAt_deriv_family hy_at
  have hdx : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => deriv x q.2) p := contDiffAt_deriv_family hx_at
  have hgoal : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ =>
      (QyH h y p.1 p.2) ^ ((n : ℝ) - 1 / 2) * lineSlope h p.1 (y p.2) * (-(deriv y p.2)) +
      (QxH h x p.1 p.2) ^ ((n : ℝ) - 1 / 2) * lineSlope h p.1 (-(x p.2))
        * (-(deriv x p.2))) p :=
    ((hPy.mul hLy).mul hdy.neg).add ((hPx.mul hLx).mul hdx.neg)
  simpa only [AH] using hgoal.contDiffWithinAt

end

end Work.OddVolterra.RowIdentity
