/-
  WilG4c / GoodCellCover — the cell-cover assembly of the §5.3 reduction (`StepLip`).

  Given a cell `κ` of the cylindrical decomposition of the `(λ,s)`-space and the family `Ψ` of
  charts of the *piece family*

      `pieceFam (yPullback F ψ) (chartFun χ)`

  that `ε/2`-covers it on the cube, this file transports the cover back to `F` itself: the
  selected charts `sel ψ'` (`Φ`) `ε`-cover `F` at every point `x` of the cube whose distinguished
  coordinate `x 0` lies in the fibre of `κ` over `l`.

  The two auxiliary hypotheses are exactly the covers of the two charts used in the transport:

  * `hχcov` — the `1`-dimensional chart `χ` attains the distinguished coordinate `x 0` at some
    interior point `τ ∈ (0,1)`; this is what lets the piece family be evaluated at the point
    whose first coordinate is `x 0` rather than `χ 0 l (x 0)`;
  * `hψcov` — the cylindrical chart `ψ` `ε/2`-covers the `x 0`-fibre of `F`, which identifies
    the piece family at the auxiliary point with `F` at a point `ε/2`-close to `x`.

  Everything here is `sorry`-free.
-/
import Mathlib
import Submission.Work.WilG4c.StepLipPieces
import Submission.Work.WilG4c.ExactChartDeriv
import Submission.Work.WilG4c.PieceChartsToF

namespace Work.WilG4c

open WilkiesDesign

/-- The piece family `pieceFam (yPullback F ψ) (chartFun χ)` is `F` evaluated at the point whose
distinguished coordinate is the `χ`-chart value `chartFun χ l (z 0)` and whose remaining
coordinates are the `ψ`-chart values at the parameter `Fin.snoc l (chartFun χ l (z 0))` of the
tail of `z`. -/
theorem pieceFam_yPullback_chartFun {k p n : ℕ} (F : Work.WilkG4c.Family k p (n + 1))
    (ψ : Work.WilkG4c.ChartTuple (p + 1) n) (χ : Work.WilkG4c.ChartTuple p 1)
    (i : Fin k) (l : Fin p → ℝ) (z : Fin (n + 1) → ℝ) :
    Work.WilkG4c.pieceFam (Work.WilkG4c.yPullback F ψ) (Work.WilG4c.chartFun χ) i l z
      = F i l (Fin.cons (Work.WilG4c.chartFun χ l (z 0))
          (fun j => ψ j (Fin.snoc l (Work.WilG4c.chartFun χ l (z 0))) (Fin.tail z))) := by
  simp only [Work.WilkG4c.pieceFam, Work.WilkG4c.yPullback, Work.WilkG4c.pullbackMap,
    Work.WilG4c.chartFun, Fin.cons_zero, Fin.tail_cons]

/-- **The cell-cover assembly.**  A finite family `Ψ` of charts that `ε/2`-covers the piece
family `pieceFam (yPullback F ψ) (chartFun χ)` on the cube, together with a selection map
`sel` that realises, at chart points, the value of `F` (`hΦid`), produces for every point `x`
of the cube whose distinguished coordinate lies in the `(λ,s)`-fibre of the cell `κ` a chart
`φ = sel ψ'` of `Φ` and a cube point `t` with `|F i l (φ l t) - F i l x| < ε`. -/
theorem GoodCellCover {p n k : ℕ} (Λ : Set (Fin p → ℝ))
    (F : Work.WilkG4c.Family k p (n + 1)) (ψ : Work.WilkG4c.ChartTuple (p + 1) n)
    (χ : Work.WilkG4c.ChartTuple p 1) (κ : Set (Fin (p + 1) → ℝ))
    (Ψ Φ : Finset (Work.WilkG4c.ChartTuple p (n + 1)))
    (sel : Work.WilkG4c.ChartTuple p (n + 1) → Work.WilkG4c.ChartTuple p (n + 1))
    (ε : ℝ)
    (hψcube : ∀ l : Fin p → ℝ, ∀ x ∈ Work.WilkG4c.I, ∀ u ∈ WilkiesDesign.openCube n,
      (fun j => ψ j (Fin.snoc l x) u) ∈ WilkiesDesign.openCube n)
    (hψcov : ∀ l ∈ Λ, ∀ x ∈ Work.WilkG4c.I, ∀ y ∈ WilkiesDesign.openCube n,
      ∃ t ∈ WilkiesDesign.openCube n, ∀ i,
        |F i l (Fin.cons x (fun j => ψ j (Fin.snoc l x) t)) - F i l (Fin.cons x y)| < ε / 2)
    (hχcov : ∀ l : Fin p → ℝ, (∃ s : ℝ, Fin.snoc l s ∈ κ) → ∀ s ∈ Work.WilkG4c.I,
      Fin.snoc l s ∈ κ → ∃ t ∈ WilkiesDesign.openCube 1, χ 0 l t = s)
    (hΨcov : ∀ l : Fin p → ℝ, (∃ s : ℝ, Fin.snoc l s ∈ κ) →
      ∀ z ∈ WilkiesDesign.openCube (n + 1),
      ∃ ψ' ∈ Ψ, ∃ t ∈ WilkiesDesign.openCube (n + 1), ∀ i,
        |Work.WilkG4c.pieceFam (Work.WilkG4c.yPullback F ψ) (Work.WilG4c.chartFun χ) i l
            (fun j => ψ' j l t)
          - Work.WilkG4c.pieceFam (Work.WilkG4c.yPullback F ψ) (Work.WilG4c.chartFun χ) i l z|
          < ε / 2)
    (hΦmem : ∀ ψ' ∈ Ψ, sel ψ' ∈ Φ)
    (hΦid : ∀ ψ' ∈ Ψ, ∀ l : Fin p → ℝ, (∃ s : ℝ, Fin.snoc l s ∈ κ) →
      ∀ t : Fin (n + 1) → ℝ, ∀ i,
      F i l (fun j => sel ψ' j l t)
        = Work.WilkG4c.pieceFam (Work.WilkG4c.yPullback F ψ) (Work.WilG4c.chartFun χ) i l
            (fun j => ψ' j l t)) :
    ∀ l ∈ Λ, ∀ x ∈ WilkiesDesign.openCube (n + 1), Fin.snoc l (x 0) ∈ κ →
      ∃ φ ∈ Φ, ∃ t ∈ WilkiesDesign.openCube (n + 1),
        ∀ i, |F i l (fun j => φ j l t) - F i l x| < ε := by
  intro l hl x hx hκx
  have _hψcube := hψcube
  -- the cell is nonempty over `l`
  have hκex : ∃ s : ℝ, Fin.snoc l s ∈ κ := ⟨x 0, hκx⟩
  have hx0I : x 0 ∈ Work.WilkG4c.I := hx 0
  have hxt : Fin.tail x ∈ WilkiesDesign.openCube n := fun j => hx j.succ
  -- (1) the `1`-dimensional chart attains the distinguished coordinate `x 0` at an interior point
  obtain ⟨tχ, htχ, hχtχ⟩ := hχcov l hκex (x 0) hx0I hκx
  have hτI : tχ 0 ∈ Work.WilkG4c.I := htχ 0
  have hχval : Work.WilG4c.chartFun χ l (tχ 0) = x 0 := by
    have h1 : (fun _ : Fin 1 => tχ 0) = tχ := by funext j; rw [Fin.eq_zero j]
    simp only [Work.WilG4c.chartFun, h1]
    exact hχtχ
  -- (2) the cylindrical chart `ε/2`-covers the fibre of `F` at `x 0`
  obtain ⟨tψ, htψ, hψap⟩ := hψcov l hl (x 0) hx0I (Fin.tail x) hxt
  have hψap' : ∀ i, |F i l (Fin.cons (x 0) (fun j => ψ j (Fin.snoc l (x 0)) tψ)) - F i l x|
      < ε / 2 := by
    intro i
    rw [← Fin.cons_self_tail x]
    exact hψap i
  -- (3) the auxiliary cube point of the piece family
  set z : Fin (n + 1) → ℝ := Fin.cons (tχ 0) tψ with hzdef
  have hz0 : z 0 = tχ 0 := by rw [hzdef, Fin.cons_zero]
  have hzt : Fin.tail z = tψ := by rw [hzdef, Fin.tail_cons]
  have hz : z ∈ WilkiesDesign.openCube (n + 1) := by
    intro j
    induction j using Fin.cases with
    | zero => rw [hz0]; exact hτI
    | succ k => simpa [hzdef] using htψ k
  -- the piece family at `z` is `F` at the `ψ`-approximation of the fibre of `x`
  have hpiece : ∀ i, Work.WilkG4c.pieceFam (Work.WilkG4c.yPullback F ψ)
        (Work.WilG4c.chartFun χ) i l z
      = F i l (Fin.cons (x 0) (fun j => ψ j (Fin.snoc l (x 0)) tψ)) := by
    intro i
    rw [pieceFam_yPullback_chartFun, hz0, hzt, hχval]
  -- (4) the piece-family cover at the auxiliary point
  obtain ⟨ψ', hψ'mem, t', ht', hcov⟩ := hΨcov l hκex z hz
  refine ⟨sel ψ', hΦmem ψ' hψ'mem, t', ht', ?_⟩
  intro i
  have hz_i : |Work.WilkG4c.pieceFam (Work.WilkG4c.yPullback F ψ) (Work.WilG4c.chartFun χ) i l z
      - F i l x| < ε / 2 := by
    rw [hpiece i]
    exact hψap' i
  have hid := hΦid ψ' hψ'mem l hκex t' i
  calc |F i l (fun j => sel ψ' j l t') - F i l x|
      = |Work.WilkG4c.pieceFam (Work.WilkG4c.yPullback F ψ) (Work.WilG4c.chartFun χ) i l
            (fun j => ψ' j l t') - F i l x| := by rw [hid]
    _ ≤ |Work.WilkG4c.pieceFam (Work.WilkG4c.yPullback F ψ) (Work.WilG4c.chartFun χ) i l
            (fun j => ψ' j l t')
          - Work.WilkG4c.pieceFam (Work.WilkG4c.yPullback F ψ) (Work.WilG4c.chartFun χ) i l z|
        + |Work.WilkG4c.pieceFam (Work.WilkG4c.yPullback F ψ) (Work.WilG4c.chartFun χ) i l z
            - F i l x| := abs_sub_le _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hcov i) hz_i
    _ = ε := by ring

end Work.WilG4c
