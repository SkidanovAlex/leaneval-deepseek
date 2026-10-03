import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Pert.pert2v2.EfChain
import Submission.Work.Pert.pert2v2.HsegRow
import Submission.Work.Pert.pert2v2.end_const_le_seg

/-!
# `Work.Pert.pert2v2.A44Row` — the paper's (A.4.4) `‖cm - cp‖ < δ` from the floor-based `Ef`

`pert2v2.end_const_le_seg` turns a segment estimate (`hseg`) plus periodicity/differentiability/
upper-end-limit data into the constant estimate (A.4.4).  This file assembles the two inputs that the
design produces from the cover:

* `hper` — the `+1` relation of `EfFloor Φm Φp (Qm Ξ' α)` on the half plane `{y₀ ≤ Im}`;
* `hseg` — the segment estimate, via `pert2v2.hseg_of_level0_cover` (which uses `E_add_int_band`,
  the level-`0` value at the cover's gate points, and the residual `hres` at those points).

The two remaining inputs are the ones whose producers are the *analytic* content of the row
(`EfFloor_sub_id_differentiableOn` for `hdiff` — needing `herb1`/`hlvl`, i.e. the level-`1`
translate of the canonical representative being a gate value, which the **disc cover**
`waist_cover_disc` supplies; and `tendsto_upperEnd_of_floor_rep` for `hlim` — needing the
localisation `hIm`/`hRe`/`hQp` of the cover's preimage and the two strip end-asymptotics).  They are
kept as hypotheses here so that the row is a single, checkable assembly step.
-/

namespace Work.Pert.pert2v2

open MandelDim Complex Set

noncomputable section

/-- **The (A.4.4) row.**  With the pointwise cover of the gate line by `Φm '' (Qm Ξ' α)`, the
residual `hres` at the cover's gate points, and the two analytic inputs `hdiff`/`hlim` for the
floor-based extended horn map, the constants `cm`, `cp` of the end asymptotics differ by less
than `δ`. -/
theorem a44_row {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {Ξ' : ℝ} {α : ℂ} {Φm Φp : ℂ → ℂ} {y₀ δ : ℝ} {cm cp : ℂ}
    (hδ : 0 < δ) (hy : d.η₀ < y₀)
    (hinj : Set.InjOn Φm (Work.Pert.Qm Ξ' α))
    (hcover : ∀ y x : ℝ, y₀ ≤ y → x ∈ Set.Ico (0 : ℝ) 1 →
      (x : ℂ) + (y : ℂ) * Complex.I ∈ Φm '' (Work.Pert.Qm Ξ' α))
    (hres : ∀ x ∈ Set.Ico (0 : ℝ) 1, ∀ ς ∈ Work.Pert.Qm Ξ' α,
      Φm ς = (x : ℂ) + (y₀ : ℂ) * Complex.I →
      ‖Φp ς - d.E ((x : ℂ) + (y₀ : ℂ) * Complex.I)‖ < δ / 2)
    (hdiff : DifferentiableOn ℂ
      (fun w : ℂ => EfFloor Φm Φp (Work.Pert.Qm Ξ' α) w - w) {w : ℂ | y₀ ≤ w.im})
    (hlim : Filter.Tendsto
      (fun w : ℂ => EfFloor Φm Φp (Work.Pert.Qm Ξ' α) w - w)
      MandelDim.upperEnd (nhds (cp - cm))) :
    ‖cm - cp‖ < δ := by
  -- the canonical representative is a gate value, hence `EfFloor`'s `+1` relation holds
  have herb : ∀ w : ℂ, y₀ ≤ w.im → w - (((⌊w.re⌋ : ℤ)) : ℂ) ∈ Φm '' (Work.Pert.Qm Ξ' α) :=
    EfFloor_canon_mem_of_cover (Q := Work.Pert.Qm Ξ' α) (Y := y₀) hcover
  have hper : ∀ u : ℂ, y₀ ≤ u.im →
      EfFloor Φm Φp (Work.Pert.Qm Ξ' α) (u + 1) = EfFloor Φm Φp (Work.Pert.Qm Ξ' α) u + 1 :=
    EfFloor_per_of_canon (Q := Work.Pert.Qm Ξ' α) (y := y₀) herb
  have hEf_int : ∀ (k : ℤ) (u : ℂ), y₀ ≤ u.im →
      EfFloor Φm Φp (Work.Pert.Qm Ξ' α) (u + (k : ℂ))
        = EfFloor Φm Φp (Work.Pert.Qm Ξ' α) u + (k : ℂ) :=
    EfFloor_add_int_of_per (Q := Work.Pert.Qm Ξ' α) (y := y₀) hper
  have hEint : ∀ (k : ℤ) (u : ℂ), y₀ ≤ |u.im| →
      d.E (u + (k : ℂ)) = d.E u + (k : ℂ) := E_add_int_band d hy
  -- the cover, in the `∃ ς ∈ Q` form consumed by `hseg_of_level0_cover`
  have hcover' : ∀ x ∈ Set.Ico (0 : ℝ) 1,
      ∃ ς ∈ Work.Pert.Qm Ξ' α, Φm ς = (x : ℂ) + (y₀ : ℂ) * Complex.I := by
    intro x hx
    have hmem := hcover y₀ x le_rfl hx
    exact ⟨Work.Pert.invOn Φm (Work.Pert.Qm Ξ' α) ((x : ℂ) + (y₀ : ℂ) * Complex.I),
      Work.Pert.invOn_mem hmem, Work.Pert.invOn_spec hmem⟩
  -- the level-`0` value, from the cover's window `Re = x ∈ [0,1)`
  have hlvl : ∀ ς ∈ Work.Pert.Qm Ξ' α, 0 ≤ (Φm ς).re → (Φm ς).re < 1 →
      EfFloor Φm Φp (Work.Pert.Qm Ξ' α) (Φm ς) = Φp ς :=
    fun ς hς h0 h1 => EfFloor_level_of_re_mem hinj hς h0 h1
  have hseg0 := hseg_of_level0_cover d (Ef := EfFloor Φm Φp (Work.Pert.Qm Ξ' α))
    (Φm := Φm) (Φp := Φp) (Q := Work.Pert.Qm Ξ' α) (y₀ := y₀) (δ := δ)
    hEf_int hEint hcover' hlvl hres
  -- `end_const_le_seg`'s `hseg` is the same estimate written with the shifts displayed
  have hseg : ∀ x : ℝ,
      ‖(EfFloor Φm Φp (Work.Pert.Qm Ξ' α) ((x : ℂ) + (y₀ : ℂ) * Complex.I)
          - ((x : ℂ) + (y₀ : ℂ) * Complex.I))
        - (d.E ((x : ℂ) + (y₀ : ℂ) * Complex.I) - ((x : ℂ) + (y₀ : ℂ) * Complex.I))‖
        < δ / 2 := by
    intro x
    have h := hseg0 x
    have h2 : EfFloor Φm Φp (Work.Pert.Qm Ξ' α) ((x : ℂ) + (y₀ : ℂ) * Complex.I)
          - ((x : ℂ) + (y₀ : ℂ) * Complex.I)
        - (d.E ((x : ℂ) + (y₀ : ℂ) * Complex.I) - ((x : ℂ) + (y₀ : ℂ) * Complex.I))
        = EfFloor Φm Φp (Work.Pert.Qm Ξ' α) ((x : ℂ) + (y₀ : ℂ) * Complex.I)
          - d.E ((x : ℂ) + (y₀ : ℂ) * Complex.I) := by ring
    rw [h2]
    exact h
  exact end_const_le_seg d hδ hy hper hdiff hlim hseg

end

end Work.Pert.pert2v2
