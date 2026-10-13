/-
  WilG4c / GoodCellCoverL — the Λ-restricted cell-cover assembly of the §5.3 reduction
  (`StepLip`).

  This is the `Λ`-restricted twin of `Work.WilG4c.GoodCellCover`: the hypotheses `hχcov`,
  `hΨcov` and `hΦid` are only assumed at parameters `l ∈ Λ` (and the unused `hψcube` of
  `GoodCellCover` is dropped).  The conclusion is produced at parameters `l ∈ Λ`, so the
  proof is the same transport of the piece-family cover back to `F`:

  * `hχcov` produces `tχ ∈ (0,1)` with `chartFun χ l (tχ 0) = x 0`;
  * `hψcov` produces `tψ ∈ (0,1)^n` with `F` at the `ψ`-chart point of the `x 0`-fibre
    `ε/2`-close to `F i l x`;
  * the auxiliary cube point `z = (tχ 0, tψ)` evaluates the piece family exactly at that
    `ψ`-chart point of the fibre, and `hΨcov` covers it by a chart `ψ' ∈ Ψ`;
  * `hΦid` converts `sel ψ'` back to the piece family, and the triangle inequality closes.

  Everything here is `sorry`-free.
-/
import Mathlib
import Submission.Work.WilG4c.StepLipPieces
import Submission.Work.WilG4c.ExactChartDeriv
import Submission.Work.WilG4c.PieceChartsToF
import Submission.Work.WilG4c.GoodCellCover

namespace Work.WilG4c

theorem GoodCellCoverL {p n k : ℕ} (Λ : Set (Fin p → ℝ))
    (F : Work.WilkG4c.Family k p (n + 1)) (ψ : Work.WilkG4c.ChartTuple (p + 1) n)
    (χ : Work.WilkG4c.ChartTuple p 1) (κ : Set (Fin (p + 1) → ℝ))
    (Ψ Φ : Finset (Work.WilkG4c.ChartTuple p (n + 1)))
    (sel : Work.WilkG4c.ChartTuple p (n + 1) → Work.WilkG4c.ChartTuple p (n + 1))
    (ε : ℝ)
    (hψcov : ∀ l ∈ Λ, ∀ x ∈ Work.WilkG4c.I, ∀ y ∈ WilkiesDesign.openCube n,
      ∃ t ∈ WilkiesDesign.openCube n, ∀ i,
        |F i l (Fin.cons x (fun j => ψ j (Fin.snoc l x) t)) - F i l (Fin.cons x y)| < ε / 2)
    (hχcov : ∀ l ∈ Λ, (∃ s : ℝ, Fin.snoc l s ∈ κ) → ∀ s ∈ Work.WilkG4c.I,
      Fin.snoc l s ∈ κ → ∃ t ∈ WilkiesDesign.openCube 1, χ 0 l t = s)
    (hΨcov : ∀ l ∈ Λ, (∃ s : ℝ, Fin.snoc l s ∈ κ) →
      ∀ z ∈ WilkiesDesign.openCube (n + 1),
      ∃ ψ' ∈ Ψ, ∃ t ∈ WilkiesDesign.openCube (n + 1), ∀ i,
        |Work.WilkG4c.pieceFam (Work.WilkG4c.yPullback F ψ) (Work.WilG4c.chartFun χ) i l
            (fun j => ψ' j l t)
          - Work.WilkG4c.pieceFam (Work.WilkG4c.yPullback F ψ) (Work.WilG4c.chartFun χ) i l z|
          < ε / 2)
    (hΦmem : ∀ ψ' ∈ Ψ, sel ψ' ∈ Φ)
    (hΦid : ∀ ψ' ∈ Ψ, ∀ l ∈ Λ, (∃ s : ℝ, Fin.snoc l s ∈ κ) →
      ∀ t ∈ WilkiesDesign.openCube (n + 1), ∀ i,
      F i l (fun j => sel ψ' j l t)
        = Work.WilkG4c.pieceFam (Work.WilkG4c.yPullback F ψ) (Work.WilG4c.chartFun χ) i l
            (fun j => ψ' j l t)) :
    ∀ l ∈ Λ, ∀ x ∈ WilkiesDesign.openCube (n + 1), Fin.snoc l (x 0) ∈ κ →
      ∃ φ ∈ Φ, ∃ t ∈ WilkiesDesign.openCube (n + 1),
        ∀ i, |F i l (fun j => φ j l t) - F i l x| < ε := by
  intro l hl x hx hκx
  -- the cell has a point over `l`
  have hκex : ∃ s : ℝ, Fin.snoc l s ∈ κ := ⟨x 0, hκx⟩
  have hx0I : x 0 ∈ Work.WilkG4c.I := hx 0
  have hxt : Fin.tail x ∈ WilkiesDesign.openCube n := fun j => hx j.succ
  -- (1) the `1`-dimensional chart attains the distinguished coordinate `x 0` at an interior point
  obtain ⟨tχ, htχ, hχtχ⟩ := hχcov l hl hκex (x 0) hx0I hκx
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
  obtain ⟨ψ', hψ'mem, t', ht', hcov⟩ := hΨcov l hl hκex z hz
  refine ⟨sel ψ', hΦmem ψ' hψ'mem, t', ht', ?_⟩
  intro i
  have hz_i : |Work.WilkG4c.pieceFam (Work.WilkG4c.yPullback F ψ) (Work.WilG4c.chartFun χ) i l z
      - F i l x| < ε / 2 := by
    rw [hpiece i]
    exact hψap' i
  have hid := hΦid ψ' hψ'mem l hl hκex t' ht' i
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
