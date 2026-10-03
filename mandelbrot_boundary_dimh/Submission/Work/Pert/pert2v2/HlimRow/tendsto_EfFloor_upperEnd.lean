import Mathlib
import Submission.Work.Pert.pert2v2.TendstoFloorRep.tendsto_upperEnd_of_floor_rep
import Submission.Work.Pert.pert2v2.EfFloor
import Submission.Work.Pert.Setup
import Submission.Work.Pert.pert2v2.HlimRow.floor_rep_window
import Submission.Work.Pert.pert2v2.HlimRow.tendsto_upperEnd_of_floor_rep_no_posB

/-!
# `Work.Pert.pert2v2.HlimRow.tendsto_EfFloor_upperEnd`

The upper-end limit of the floor extension `EfFloor` of the horn map:

`EfFloor Φm Φp (Qm Ξ α) w - w → cp - cm`  as  `Im w → +∞`.

This is the assembly of the H-limit row, stated for the floor-based `ℤ`-extension
`pert2v2.EfFloor` (which uses the *canonical* representative `w - ⌊Re w⌋` with real part in `[0,1)`).

The abstract limit statement is the general lemma (proved in the sibling module)
`HlimRow.tendsto_upperEnd_of_floor_rep_no_posB`; here we only have to supply its four
pointwise hypotheses from the cover hypothesis `hcover`.  Everything is fed through the same point:
for `w` in the half plane `{y ≤ Im}`, the canonical representative `w - ⌊Re w⌋` has imaginary part
`Im w ≥ y` and real part in `[0,1)` (`HlimRow.floor_rep_window`), so the cover applies at it:

* `w - ⌊Re w⌋ ∈ Φm '' (Qm Ξ α ∩ Qp Ξ α)`  (`hrep`'s membership, `hQp`), and
* `Im (invOn Φm Qm (w - ⌊Re w⌋)) ≥ (3 Im w + Ξ)/4`, which diverges (`hIm`).

Injectivity of `Φm` on `Qm Ξ α` (`hinj`) is what pins `invOn Φm (Qm Ξ α) (w - ⌊Re w⌋)` to the gate
point `ζ ∈ Qm Ξ α ∩ Qp Ξ α` producing `w - ⌊Re w⌋`, hence puts it in `Qp Ξ α`.

Note on the hypothesis `hB : 0 ≤ B`: the abstract lemma
`TendstoFloorRep.tendsto_upperEnd_of_floor_rep` requires `0 < B`, but `B` enters its proof only
through `hRe`, `hEndm`, `hEndp` — positivity is never used.  This is why the statement here is
discharged through the hypothesis-free variant `…_no_posB`, and it covers `B = 0`.
-/

namespace Work.Pert.pert2v2.HlimRow

theorem tendsto_EfFloor_upperEnd {Ξ : ℝ} {α : ℂ} {Φm Φp : ℂ → ℂ} {cm cp y B : ℝ}
    (hΞy : Ξ < y) (hB : 0 ≤ B)
    (hinj : Set.InjOn Φm (Work.Pert.Qm Ξ α))
    (hcover : ∀ t : ℝ, y ≤ t → ∀ x ∈ Set.Ico (0 : ℝ) 1,
      (x : ℂ) + (t : ℂ) * Complex.I ∈ Φm '' (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) ∧
      (3 * t + Ξ) / 4 ≤ (Work.Pert.invOn Φm (Work.Pert.Qm Ξ α)
        ((x : ℂ) + (t : ℂ) * Complex.I)).im)
    (hRe : ∀ w : ℂ, y ≤ w.im →
      |Complex.re (Work.Pert.invOn Φm (Work.Pert.Qm Ξ α) (w - (((⌊w.re⌋ : ℤ)) : ℂ)))| ≤ B)
    (hEndm : ∀ ε > 0, ∃ Y' : ℝ, ∀ z ∈ Work.Pert.Qm Ξ α, Y' < z.im → |z.re| ≤ B →
      ‖Φm z - z - cm‖ < ε)
    (hEndp : ∀ ε > 0, ∃ Y' : ℝ, ∀ z ∈ Work.Pert.Qp Ξ α, Y' < z.im → |z.re| ≤ B →
      ‖Φp z - z - cp‖ < ε) :
    Filter.Tendsto
      (fun w : ℂ => Work.Pert.pert2v2.EfFloor Φm Φp (Work.Pert.Qm Ξ α) w - w)
      MandelDim.upperEnd (nhds (cp - cm)) := by
  -- `B ≥ 0` and `Ξ < y` are part of the interface but are not needed by the argument.
  have _hB := hB
  have _hΞy := hΞy
  -- `Im w → +∞` along `upperEnd`, which is `comap im atTop` by definition.
  have himT : Filter.Tendsto (fun w : ℂ => w.im) MandelDim.upperEnd Filter.atTop := by
    rw [MandelDim.upperEnd]; exact Filter.tendsto_comap
  refine tendsto_upperEnd_of_floor_rep_no_posB
    (Ef := Work.Pert.pert2v2.EfFloor Φm Φp (Work.Pert.Qm Ξ α))
    (Φm := Φm) (Φp := Φp) (Q := Work.Pert.Qm Ξ α) (Qp := Work.Pert.Qp Ξ α)
    (cm := cm) (cp := cp) (y := y) (B := B) ?_ ?_ ?_ ?_ hEndm hEndp
  ·
    -- the canonical representative `w - ⌊Re w⌋` is a gate value, and `EfFloor` reads it off
    intro w hyl
    obtain ⟨hpt, hIco, -⟩ := floor_rep_window w
    obtain ⟨hmem, -⟩ := hcover w.im hyl (w - (((⌊w.re⌋ : ℤ)) : ℂ)).re hIco
    rw [hpt] at hmem
    obtain ⟨z, hz, hzΦ⟩ := hmem
    have hcond : w - (((⌊w.re⌋ : ℤ)) : ℂ) ∈ Φm '' Work.Pert.Qm Ξ α := ⟨z, hz.1, hzΦ⟩
    refine ⟨⟨z, hz.1, hzΦ⟩, ?_⟩
    unfold Work.Pert.pert2v2.EfFloor
    rw [ite_eq_left hcond]
  ·
    -- `Im (invOn Φm Qm (w - ⌊Re w⌋)) ≥ (3 Im w + Ξ)/4 → +∞`
    rw [Filter.tendsto_atTop]
    intro b
    have hbig : ∀ᶠ w in MandelDim.upperEnd, max y ((4 * b - Ξ) / 3) < w.im :=
      himT.eventually (Filter.eventually_gt_atTop _)
    filter_upwards [hbig] with w hw
    have hwy : y ≤ w.im := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hw)
    have hb : b < (3 * w.im + Ξ) / 4 := by
      have h : (4 * b - Ξ) / 3 < w.im := lt_of_le_of_lt (le_max_right _ _) hw
      linarith
    obtain ⟨hpt, hIco, -⟩ := floor_rep_window w
    obtain ⟨-, himb⟩ := hcover w.im hwy (w - (((⌊w.re⌋ : ℤ)) : ℂ)).re hIco
    rw [hpt] at himb
    exact le_trans (le_of_lt hb) himb
  ·
    exact hRe
  ·
    -- injectivity of `Φm` on `Qm` puts the chosen preimage inside `Qm ∩ Qp`
    intro w hyl
    obtain ⟨hpt, hIco, -⟩ := floor_rep_window w
    obtain ⟨hmem, -⟩ := hcover w.im hyl (w - (((⌊w.re⌋ : ℤ)) : ℂ)).re hIco
    rw [hpt] at hmem
    obtain ⟨z, hz, hzΦ⟩ := hmem
    have hex : ∃ ζ ∈ Work.Pert.Qm Ξ α, Φm ζ = w - (((⌊w.re⌋ : ℤ)) : ℂ) := ⟨z, hz.1, hzΦ⟩
    rw [Work.Pert.invOn_eq hinj hex hz.1 hzΦ]
    exact hz.2

end Work.Pert.pert2v2.HlimRow
