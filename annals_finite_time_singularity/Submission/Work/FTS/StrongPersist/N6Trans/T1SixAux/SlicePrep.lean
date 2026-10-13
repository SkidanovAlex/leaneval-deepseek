/-
Copyright: work module for the Elgindi finite-time singularity project.

# Level-six `T1` assembly prerequisites

Elementary pieces of the assembly of `Work.FTS.StrongPersist.N6Trans.slotT1Six` that do not
depend on the analytic per-term estimates:

* `eta_le_gam`, `gam_nonneg` — the range facts for the two exponents;
* `leafW_canon_cases` — **the leaf weight of a slot is exactly a canonical weight, with the
  exponent in the admissible range** (`IsLeafW α a ρ` ⟹ `∃ q, ρ = canonW q ∧ 0 ≤ q ∧ q ≤ γ ∧
  (a = 0 → q ≤ η)`).  This is the form in which the weight is consumed: the estimates are run
  with the *exact* exponent of `ρ`, so that no pointwise weight comparison is ever needed
  (a comparison `∫_θ ρ|X||Y| ≤ ∫_θ canonW q|X||Y|` is not available in general, see
  `NOTES_slotT1Six.md` §5);
* `DthIter_shift`, `leibniz_Dth` — the `D_θ`-form of the Leibniz rule: the expansion of
  `mixed b a (f · Dth g)` as `Σ_{i≤a, j≤b} C(a,i)C(b,j) · mixed j i f · mixed (b-j)(a-i+1) g`,
  whose `(i,j) = (0,0)` summand is `f · Dth (mixed b a g)` (the angular transport term).

All declarations here are `sorry`-free.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.TransportS.T2Sup.Final
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed
import Submission.Work.Spaces.mixed_comm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.T1SixAux

open Work.FTS.TransportS.SlotT2 (canonW)

set_option autoImplicit false

/-! ## The exponent range -/

theorem eta_le_gam {α : ℝ} (hα : 0 < α) : Work.Spaces.eta ≤ Work.Spaces.gam α := by
  rw [Work.Spaces.gam]
  have := Work.Spaces.eta_lt_one
  linarith

theorem gam_nonneg {α : ℝ} (hα : 0 < α) : 0 ≤ Work.Spaces.gam α := by
  rw [Work.Spaces.gam]; linarith

/-! ## The exact canonical exponent of a leaf weight -/

/-- **Every leaf weight is a canonical weight at an admissible exponent.**  The exponent is
`η` for `leafEta`, `0` for `leafOne` and `γ` for `leafGam α`, and the range conditions
`0 ≤ q`, `q ≤ γ`, `a = 0 → q ≤ η` are exactly what the per-term estimates need (a mixed
slot may be priced up to `γ`, a pure `D_z`-slot only up to `η`). -/
theorem leafW_canon_cases {α : ℝ} (hα : 0 < α) {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ) :
    ∃ q : ℝ, ρ = canonW q ∧ 0 ≤ q ∧ q ≤ Work.Spaces.gam α
      ∧ (a = 0 → q ≤ Work.Spaces.eta) := by
  rcases hρ with rfl | rfl | ⟨ha1, rfl⟩
  · exact ⟨Work.Spaces.eta, Work.FTS.TransportS.T2Sup.leafWeight_eq_canon.1,
      Work.Spaces.eta_pos.le, eta_le_gam hα, fun _ => le_rfl⟩
  · exact ⟨0, Work.FTS.TransportS.T2Sup.leafWeight_eq_canon.2.1, le_rfl,
      gam_nonneg hα, fun _ => Work.Spaces.eta_pos.le⟩
  · exact ⟨Work.Spaces.gam α, Work.FTS.TransportS.T2Sup.leafWeight_eq_canon.2.2 α,
      gam_nonneg hα, le_rfl, fun ha0 => absurd ha0 (by omega)⟩

/-! ## The Leibniz rule in `D_θ`-form -/

/-- `mixed j i (Dth h) = mixed j (i+1) h`: the `D_θ`-iterate of a `D_θ`-derivative is the next
`D_θ`-iterate. -/
theorem mixed_Dth_shift (j i : ℕ) (h : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed j i (Work.Spaces.Dth h) = Work.Spaces.mixed j (i + 1) h := by
  show Work.Spaces.DzIter j (Work.Spaces.DthIter i (Work.Spaces.DthIter 1 h))
      = Work.Spaces.DzIter j (Work.Spaces.DthIter (i + 1) h)
  congr 1
  exact Work.Spaces.DthIter_add_right i 1 h

/-- **The Leibniz rule for `mixed b a (f · D_θ g)`**, on the open quadrant: the `D_θ`-derivative
of `g` produces the `(i,j) = (0,0)` summand `f · D_θ (mixed b a g)` (the transport term) and
`(a+1)(b+1) - 1` further summands. -/
theorem leibniz_Dth {f g : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen f)
    (hG : Work.FTS.EllipticEst.SmoothOpen g) (b a : ℕ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.mixed b a (fun z θ => f z θ * Work.Spaces.Dth g z θ) z θ
        = ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
            ((a.choose i : ℝ) * (b.choose j : ℝ))
              * (Work.Spaces.mixed j i f z θ
                  * Work.Spaces.mixed (b - j) (a - i + 1) g z θ) := by
  intro z θ hz hθ0 hθ1
  rw [Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed b a f (Work.Spaces.Dth g) hF hG.Dth
    z θ hz hθ0 hθ1]
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
  rw [mixed_Dth_shift]

end Work.FTS.StrongPersist.N6Trans.T1SixAux
