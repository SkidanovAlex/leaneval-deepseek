import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBox.Nodes
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory

/-! ## The box-locality toolbox

`n₊ = Σᵢ aQ ℓ i` is *box local*: for `x ∈ abox n ℓ` the slot-`i` fibre `x[i↦z]` with `z ∈ acube ℓ`
is again a point of `abox n ℓ`, so `aP ℓ i Ψ x` — the box mean of the fibre — and hence `aQ ℓ i Ψ x`
and every iterate `nPlusPow ℓ n m Ψ x` depend only on the values of `Ψ` *on the box*.  These four
lemmas are that statement, in increasing generality; none of them needs `0 < ℓ`. -/

/-- Updating one coordinate of a point of `abox n ℓ` by a point of `acube ℓ` keeps it in the box. -/
private lemma update_mem_abox {n : ℕ} {ℓ : ℝ} {x : Submission.BoseGases.X n}
    (hx : x ∈ Submission.BoseGases.abox n ℓ) (i : Fin n) {z : EuclideanSpace ℝ (Fin 3)}
    (hz : z ∈ Submission.BoseGases.acube ℓ) :
    Function.update x i z ∈ Submission.BoseGases.abox n ℓ := by
  rw [Submission.BoseGases.mem_abox_iff] at hx ⊢
  intro j
  rw [Function.update_apply]
  split
  · exact hz
  · exact hx j

/-- **`aP` is box local**: two states agreeing on `abox n ℓ` have the same box-fibre mean there. -/
private lemma aP_congr_of_eqOn_abox {n : ℕ} {ℓ : ℝ} {Ψ Φ : Submission.BoseGases.X n → ℝ}
    (h : ∀ x ∈ Submission.BoseGases.abox n ℓ, Ψ x = Φ x) {x : Submission.BoseGases.X n}
    (hx : x ∈ Submission.BoseGases.abox n ℓ) (i : Fin n) :
    Submission.BoseGases.aP ℓ i Ψ x = Submission.BoseGases.aP ℓ i Φ x := by
  have hint : (∫ y in Submission.BoseGases.acube ℓ, Ψ (Function.update x i y))
      = (∫ y in Submission.BoseGases.acube ℓ, Φ (Function.update x i y)) :=
    setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
      (fun z hz => h _ (update_mem_abox hx i hz))
  simp only [Submission.BoseGases.aP]
  rw [hint]

/-- **`aQ = 1 − aP` is box local** (the difference of two box-local functions). -/
private lemma aQ_congr_of_eqOn_abox {n : ℕ} {ℓ : ℝ} {Ψ Φ : Submission.BoseGases.X n → ℝ}
    (h : ∀ x ∈ Submission.BoseGases.abox n ℓ, Ψ x = Φ x) {x : Submission.BoseGases.X n}
    (hx : x ∈ Submission.BoseGases.abox n ℓ) (i : Fin n) :
    Submission.BoseGases.aQ ℓ i Ψ x = Submission.BoseGases.aQ ℓ i Φ x := by
  simp only [Submission.BoseGases.aQ, h x hx, aP_congr_of_eqOn_abox h hx i]

/-- **`n₊ = Σᵢ aQ ℓ i` is box local**: a finite sum of box-local slots. -/
private lemma nPlusFun_congr_of_eqOn_abox {n : ℕ} {ℓ : ℝ} {Ψ Φ : Submission.BoseGases.X n → ℝ}
    (h : ∀ x ∈ Submission.BoseGases.abox n ℓ, Ψ x = Φ x) {x : Submission.BoseGases.X n}
    (hx : x ∈ Submission.BoseGases.abox n ℓ) :
    Work.BoseBox.nPlusFun ℓ Ψ x = Work.BoseBox.nPlusFun ℓ Φ x := by
  simp only [Work.BoseBox.nPlusFun]
  exact Finset.sum_congr rfl (fun i _ => aQ_congr_of_eqOn_abox h hx i)

/-- **Every iterate `n₊^m` is box local** (induction on `m`, the step being the preceding lemma). -/
private lemma nPlusPow_congr_of_eqOn_abox {n : ℕ} {ℓ : ℝ} {Ψ Φ : Submission.BoseGases.X n → ℝ}
    (h : ∀ x ∈ Submission.BoseGases.abox n ℓ, Ψ x = Φ x) (m : ℕ) :
    ∀ x ∈ Submission.BoseGases.abox n ℓ,
      Work.BoseBox.nPlusPow ℓ n m Ψ x = Work.BoseBox.nPlusPow ℓ n m Φ x := by
  induction m with
  | zero => intro x hx; exact h x hx
  | succ m ih => intro x hx; exact nPlusFun_congr_of_eqOn_abox (fun y hy => ih y hy) hx

/-- **The state-class repair of the BF3c selection chain, step 2** (the window/spectral hypothesis
of the selection is preserved by the box restriction).

The BF3c selection consumes `hmom : SpectralNPlusLe ℓ M Φ` (FS `eq:LocalizedNPlus`: the `n₊`-spectrum
of `Φ` lies in `[0,M]`, rendered as the all-moments condition
`∀ m, ∫_{abox} n₊^m Φ · Φ ≤ M^m ∫_{abox} Φ²`).  The honest state is fed to the chain as its box
restriction `Φ·1_{abox}` (see `Work.BoseBoxFock.boxRestrictState`), a different function, so the
hypothesis has to be transferred.

This holds because `n₊ = Σ_i aQ ℓ i` is **box local**: `aQ ℓ i Ψ x = Ψ x − aP ℓ i Ψ x` is `Ψ`'s value
at `x` minus the box-mean of the fibre, and for `x ∈ abox` the fibre points `x[i↦z]` with
`z ∈ boxL ℓ` are again in the box `abox n ℓ`; so for `x ∈ abox` both `aQ` and (by induction) every
iterate `nPlusPow ℓ n m` depend only on the values of the state on `abox n ℓ`, where `Φ·1_{abox}`
agrees with `Φ`.  Hence the two integrands agree on `abox n ℓ`, and so do the box integrals in every
moment inequality. -/
theorem spectralNPlus_boxRestrict {n : ℕ} {ℓ M : ℝ} {Φ : Submission.BoseGases.X n → ℝ}
    (hmom : Work.BoseBox.SpectralNPlusLe ℓ M Φ) :
    Work.BoseBox.SpectralNPlusLe ℓ M
      (fun x => Φ x * (Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) x) := by
  set Ψ : Submission.BoseGases.X n → ℝ :=
    fun x => Φ x * (Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) x with hΨdef
  change Work.BoseBox.SpectralNPlusLe ℓ M Ψ
  -- the restriction agrees with `Φ` on the box
  have hΨΦ : ∀ x ∈ Submission.BoseGases.abox n ℓ, Ψ x = Φ x := by
    intro x hx
    rw [hΨdef]
    simp [Set.indicator_of_mem hx]
  intro m
  -- on the box the two integrands coincide, by box locality of `n₊^m`
  have hL : (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseBox.nPlusPow ℓ n m Ψ x * Ψ x)
      = (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseBox.nPlusPow ℓ n m Φ x * Φ x) :=
    setIntegral_congr_fun (Submission.BoseGases.abox_measurable n ℓ) (fun x hx => by
      rw [nPlusPow_congr_of_eqOn_abox hΨΦ m x hx, hΨΦ x hx])
  have hR : (∫ x in Submission.BoseGases.abox n ℓ, (Ψ x) ^ 2)
      = (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) :=
    setIntegral_congr_fun (Submission.BoseGases.abox_measurable n ℓ) (fun x hx => by
      rw [hΨΦ x hx])
  rw [hL, hR]
  exact hmom m

end Work.BoseBoxFock
