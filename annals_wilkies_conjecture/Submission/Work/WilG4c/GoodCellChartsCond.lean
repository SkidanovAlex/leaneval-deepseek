import Mathlib
import Submission.Work.WilG4c.GoodCellChartsG
import Submission.Work.WilG4c.StepLipHighGlue
import Submission.Work.WilG4c.GoodCellCoverL

set_option maxHeartbeats 1600000
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-- **`GoodCellCoverL` with the `ψ`-cover hypothesis moved into the conclusion.**

The assembly of `Work.WilG4c.GoodCellCoverL` only ever uses the fibre-cover hypothesis at the
single fibre point `(x 0, Fin.tail x)` that is being covered, so the hypothesis can be replaced
by the (weaker) pointwise condition, delivered as the last argument below. -/
theorem GoodCellCoverLCond {p n k : ℕ} (Λ : Set (Fin p → ℝ))
    (F : Work.WilkG4c.Family k p (n + 1)) (ψ : Work.WilkG4c.ChartTuple (p + 1) n)
    (χ : Work.WilkG4c.ChartTuple p 1) (κ : Set (Fin (p + 1) → ℝ))
    (Ψ Φ : Finset (Work.WilkG4c.ChartTuple p (n + 1)))
    (sel : Work.WilkG4c.ChartTuple p (n + 1) → Work.WilkG4c.ChartTuple p (n + 1))
    (ε : ℝ)
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
      (∃ t ∈ WilkiesDesign.openCube n, ∀ i,
        |F i l (Fin.cons (x 0) (fun j => ψ j (Fin.snoc l (x 0)) t)) - F i l x| < ε / 2) →
      ∃ φ ∈ Φ, ∃ t ∈ WilkiesDesign.openCube (n + 1),
        ∀ i, |F i l (fun j => φ j l t) - F i l x| < ε := by
  intro l hl x hx hκx hfib
  -- the cell has a point over `l`
  have hκex : ∃ s : ℝ, Fin.snoc l s ∈ κ := ⟨x 0, hκx⟩
  have hx0I : x 0 ∈ Work.WilkG4c.I := hx 0
  -- (1) the `1`-dimensional chart attains the distinguished coordinate `x 0` at an interior point
  obtain ⟨tχ, htχ, hχtχ⟩ := hχcov l hl hκex (x 0) hx0I hκx
  have hτI : tχ 0 ∈ Work.WilkG4c.I := htχ 0
  have hχval : Work.WilG4c.chartFun χ l (tχ 0) = x 0 := by
    have h1 : (fun _ : Fin 1 => tχ 0) = tχ := by funext j; rw [Fin.eq_zero j]
    simp only [Work.WilG4c.chartFun, h1]
    exact hχtχ
  -- (2) the cylindrical chart `ε/2`-covers the fibre of `F` at `x 0`
  obtain ⟨tψ, htψ, hψap'⟩ := hfib
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

/-- **The good-cell branch of `§5.3`, with the corrected `ψ`-interface.**

This is `Work.WilG4c.GoodCellChartsG` (PROVED) with one change: the cover hypothesis
`hψcov : ∀ l ∈ Λ, ∀ x ∈ I, ∀ y ∈ openCube n, ∃ t ∈ openCube n, ∀ i, |F i l (cons x (ψ … t)) - F i l (cons x y)| < ε/2`
is *removed*, and the condition on the target that it expresses is moved into the conclusion.

Why: `hψcov` says the *single* chart `ψ` covers the whole value fibre at every `(l,x) ∈ Λ × I`.
That is not supplyable. `YbCharts` (the `n`-dimensional F-rule applied to the pinned family)
delivers its `ε/2`-cover only as `∀ l x y, ∃ ψ ∈ Ξ, ∃ t, …`, and a chart of the `n`-dimensional
F-rule is a parametrisation of *one cell* of a cylindrical decomposition of the `n`-cube, so for a
typical `ψ ∈ Ξ` the hypothesis above is false. Every consumer uses `hψcov` only at the *one* fibre
point being covered (`Work.WilG4c.GoodCellCoverL`, called at line 378 of `GoodCellChartsG`, does
`obtain ⟨tψ, htψ, hψap⟩ := hψcov l hl (x 0) hx0I (Fin.tail x) hxt`), so the same proof gives this
statement. See `Submission/Work/WilG4c/StepLipHighOuter_NOTES.md`.-/
theorem GoodCellChartsCond (S : WilkiesDesign.SOMin) (n p : ℕ)
    (hP1 : Work.WilkG4c.FLemP S p (n + 1) (Work.WilkG4c.PYLip p n)) :
    ∀ (aψ Ag Ftup F0 F1 : ℕ) (bψ dg dtup dc : MvPolynomial (Fin 2) ℕ),
      ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : MvPolynomial (Fin 4) ℝ),
      ∀ (D r k : ℕ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hr : 1 ≤ r)
        (Λ : Set (Fin p → ℝ)) (F : Work.WilkG4c.Family k p (n + 1))
        (hΩg : ∀ i, WilkiesDesign.CG.famGraph (F i) ∈ S.Ω F0 D (p + (n + 1) + 1))
        (hPY : Work.WilkG4c.PY p n r k F)
        (hval : Work.WilkG4c.ValuesIn01 Λ F)
        (ψ : Work.WilkG4c.ChartTuple (p + 1) n)
        (hψg : ∀ j, WilkiesDesign.CG.famGraph (ψ j) ∈
          S.Ω aψ (MvPolynomial.eval ![D, r] bψ) ((p + 1) + n + 1))
        (hψcube : ∀ l, ∀ x ∈ Work.WilkG4c.I, ∀ t ∈ WilkiesDesign.openCube n,
          (fun j => ψ j (Fin.snoc l x) t) ∈ WilkiesDesign.openCube n)
        (hψsm : ∀ i, ∀ l, ∀ x ∈ Work.WilkG4c.I,
          ContDiffOn ℝ r (fun t => F i l (Fin.cons x (fun j => ψ j (Fin.snoc l x) t)))
            (WilkiesDesign.openCube n))
        (hψnm : ∀ i, ∀ l, ∀ x ∈ Work.WilkG4c.I, ∀ m, m ≤ r →
          ∀ t ∈ WilkiesDesign.openCube n,
            ‖iteratedFDeriv ℝ m (fun t => F i l (Fin.cons x (fun j => ψ j (Fin.snoc l x) t))) t‖ ≤ 1)
        (γ : Fin k → (Fin p → ℝ) → ℝ → (Fin n → ℝ))
        (hγg : ∀ i j, WilkiesDesign.graphOf
          (fun w : Fin (p + 1) → ℝ => γ i (Fin.init w) (w (Fin.last p)) j) ∈
            S.Ω Ag (MvPolynomial.eval ![D, r] dg) (p + 1 + 1))
        (hγmax : ∀ i l x, Work.WilkG4c.NearMax (Work.WilkG4c.yPullback F ψ i) l x →
          γ i l x ∈ WilkiesDesign.openCube n ∧
          Work.WilkG4c.xPt l x (γ i l x) ∈
            interior {z | ContDiffAt ℝ 1 (Work.WilkG4c.famFunHat (Work.WilkG4c.yPullback F ψ i)) z} ∧
          ∀ y' ∈ WilkiesDesign.openCube n,
            Work.WilkG4c.xPt l x y' ∈
              interior {z | ContDiffAt ℝ 1 (Work.WilkG4c.famFunHat (Work.WilkG4c.yPullback F ψ i)) z} →
            |Work.WilkG4c.xDeriv (Work.WilkG4c.yPullback F ψ i) l x y'| ≤
              2 * |Work.WilkG4c.xDeriv (Work.WilkG4c.yPullback F ψ i) l x (γ i l x)|)
        (C : Finset (Set (Fin (p + 1) → ℝ))) (hCdec : WilkiesDesign.IsCylDecomp (p + 1) C)
        (κ : Set (Fin (p + 1) → ℝ)) (hκC : κ ∈ C)
        (hκΩ : κ ∈ S.Ω F1 (MvPolynomial.eval ![D, r] dc) (p + 1))
        (hκcube : κ ⊆ Work.WilG4c.inCubeSet p 1)
        (hκbad : ∀ i, Disjoint κ (Work.WilkG4c.badCurve (Work.WilkG4c.yPullback F ψ i)))
        (hκC1 : ∀ i, κ ⊆ Work.WilkG4c.C1All (Work.WilkG4c.yPullback F ψ i))
        (hκfib : ∀ l ∈ Λ, ∃ s : ℝ, Fin.snoc l s ∈ κ)
        (kt : ℕ) (Tm : Fin kt → (Fin p → ℝ) → (Fin 1 → ℝ) → ℝ)
        (hTmΩ : ∀ a, WilkiesDesign.CG.famGraph (Tm a) ∈
          S.Ω Ftup (MvPolynomial.eval ![D, r] dtup) (p + 1 + 1))
        (hid : ∃ a : Fin kt, ∀ l u, Tm a l u = u 0)
        (hγx : ∀ i j, ∃ a : Fin kt, ∀ l u, Tm a l u = γ i l (u 0) j)
        (hcx : ∀ i, ∃ a : Fin kt, ∀ l u,
          Tm a l u = Work.WilkG4c.yPullback F ψ i l (Fin.cons (u 0) (γ i l (u 0))))
        (hTsm : ∀ a : Fin kt, ∀ w ∈ κ,
          ContDiffAt ℝ 1 (fun z : Fin (p + 1) → ℝ => Tm a (Fin.init z) (fun _ => z (Fin.last p))) w)
        (hTval : ∀ a : Fin kt, ∀ w ∈ κ,
          Tm a (Fin.init w) (fun _ => w (Fin.last p)) ∈ Set.Ioo (0 : ℝ) 1)
        (hdich : ∀ a b : Fin kt,
          κ ⊆ {w : Fin (p + 1) → ℝ |
              |fderiv ℝ (fun z : Fin (p + 1) → ℝ => Tm a (Fin.init z) (fun _ => z (Fin.last p))) w
                (Pi.single (Fin.last p) 1)|
            = |fderiv ℝ (fun z : Fin (p + 1) → ℝ => Tm b (Fin.init z) (fun _ => z (Fin.last p))) w
                (Pi.single (Fin.last p) 1)|} ∨
          Disjoint κ {w : Fin (p + 1) → ℝ |
              |fderiv ℝ (fun z : Fin (p + 1) → ℝ => Tm a (Fin.init z) (fun _ => z (Fin.last p))) w
                (Pi.single (Fin.last p) 1)|
            = |fderiv ℝ (fun z : Fin (p + 1) → ℝ => Tm b (Fin.init z) (fun _ => z (Fin.last p))) w
                (Pi.single (Fin.last p) 1)|})
        (hγd : ∀ i j, ∀ w ∈ κ, DifferentiableAt ℝ (fun s : ℝ => γ i (Fin.init w) s j) (w (Fin.last p))),
        ∃ Φ : Finset (Work.WilkG4c.ChartTuple p (n + 1)),
          (Φ.card : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c ∧
          Work.WilkG4c.ChartsOK S a (MvPolynomial.eval ![D, r] b) r Λ F Φ ∧
          (∀ l ∈ Λ, ∀ x ∈ WilkiesDesign.openCube (n + 1), Fin.snoc l (x 0) ∈ κ →
            (∃ t ∈ WilkiesDesign.openCube n, ∀ i,
              |F i l (Fin.cons (x 0) (fun j => ψ j (Fin.snoc l (x 0)) t)) - F i l x| < ε / 2) →
            ∃ φ ∈ Φ, ∃ t ∈ WilkiesDesign.openCube (n + 1),
              ∀ i, |F i l (fun j => φ j l t) - F i l x| < ε) := by
  classical
  intro aψ Ag Ftup F0 F1 bψ dg dtup dc
  -- ## witnesses fixed before `D, r, k, ε`
  obtain ⟨aec, bec, hEC⟩ := Work.WilkG4c.ChartsExactCell S p Ftup F1
  obtain ⟨Apg, Tpg, hPG⟩ := Work.WilG4c.PieceFamGraphMem S p n
  obtain ⟨A0, C0, hz0⟩ := Work.WilG4c.selPieceChart_zero_mem S p n
  obtain ⟨A1, C1, hs1⟩ := Work.WilG4c.selPieceChart_succ_mem S p n
  set Cpc : ℝ := max (2 * ((n : ℝ) + 1)) 1 * ((n : ℝ) + 1) with hCpcdef
  have hCpc_ge : max (2 * ((n : ℝ) + 1)) 1 * ((n : ℝ) + 1) ≤ Cpc := by rw [hCpcdef]
  have hCpc0 : 0 ≤ Cpc := by
    have h1 : (1 : ℝ) ≤ max (2 * ((n : ℝ) + 1)) 1 := le_max_right _ _
    have h2 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
    calc (0 : ℝ) = 0 * 1 := by ring
      _ ≤ max (2 * ((n : ℝ) + 1)) 1 * ((n : ℝ) + 1) :=
          mul_le_mul (by norm_num) h2 zero_le_one (by positivity)
      _ = Cpc := hCpcdef
  have hCpc1 : 1 ≤ Cpc := by
    rw [hCpcdef]
    have h1 : (1 : ℝ) ≤ max (2 * ((n : ℝ) + 1)) 1 := le_max_right _ _
    have h2 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ max (2 * ((n : ℝ) + 1)) 1 * ((n : ℝ) + 1) :=
          mul_le_mul h1 h2 zero_le_one (by positivity)
  have hLR := Work.WilG4c.LipRescale S n p hP1 Cpc hCpc1
  rw [Work.WilkG4c.FLemP_iff] at hLR
  obtain ⟨aL, bL, cL, hL⟩ :=
    hLR ((F0 + aψ + aec + Apg) + (F1 + 1) + 3 * (p + (n + 1) + 1) + 3 * p + 6)
  set becs : MvPolynomial (Fin 2) ℕ := MvPolynomial.aeval ![dtup, dc] bec with hbecsdef
  set qG : MvPolynomial (Fin 2) ℕ :=
      (MvPolynomial.X 0
          + MvPolynomial.C (p + (n + 1))
              * (bψ + MvPolynomial.C ((p + 1) + n)
                    * (becs + MvPolynomial.C (p + 1) + MvPolynomial.C Tpg)
                  + MvPolynomial.C Tpg + MvPolynomial.C 1)
          + MvPolynomial.C Tpg)
      + MvPolynomial.C 2 * dc + MvPolynomial.C 5 with hqGdef
  set bpL : MvPolynomial (Fin 2) ℕ := MvPolynomial.aeval ![qG, MvPolynomial.X 1] bL
    with hbpLdef
  set bfin : MvPolynomial (Fin 2) ℕ :=
      (becs + MvPolynomial.C (p + 1) * bpL + MvPolynomial.C C0)
      + (bψ + MvPolynomial.C ((p + 1) + n)
          * (becs + MvPolynomial.C (p + 1) * bpL + MvPolynomial.C C1) + MvPolynomial.C C1)
    with hbfindef
  set cp : MvPolynomial (Fin 4) ℝ :=
      MvPolynomial.eval₂ MvPolynomial.C
        (fun i : Fin 4 => if i = 3 then MvPolynomial.X 3 + MvPolynomial.C (Real.log 2)
          else MvPolynomial.X i) cL with hcpdef
  obtain ⟨cfin, hcfin0⟩ := Work.WilG4c.PolySubstFirst4 qG cp
  set aΦ : ℕ := aec + aL + A0 + (aψ + (aec + aL + A1)) with haΦdef
  refine ⟨aΦ + (F1 + 1) + 3 * (p + (n + 1) + 1) + 3 * p + 6,
      bfin + MvPolynomial.C 2 * dc + MvPolynomial.C 5, cfin, ?_⟩
  intro D r k ε hε hε1 hr Λ F hΩg hPY hval ψ hψg hψcube hψsm hψnm γ hγg hγmax C hCdec κ
    hκC hκΩ hκcube hκbad hκC1 hκfib kt Tm hTmΩ hid hγx hcx hTsm hTval hdich hγd
  -- ## the parameter projection of the cell
  set PK : Set (Fin p → ℝ) := {l | ∃ s : ℝ, Fin.snoc l s ∈ κ} with hPKdef
  have hPKmem : ∀ l : Fin p → ℝ, l ∈ PK ↔ ∃ s : ℝ, Fin.snoc l s ∈ κ := by
    intro l; simp [hPKdef]
  -- ## the degree of the `y`-pullback graph, fixed as a number
  set Dgp : ℕ := D + (p + (n + 1))
        * (MvPolynomial.eval ![D, r] bψ
            + ((p + 1) + n) * (MvPolynomial.eval ![D, r] becs + (p + 1) + Tpg)
            + Tpg + 1)
      + Tpg with hDgpdef
  have hqGe : MvPolynomial.eval ![D, r] qG = Dgp + 2 * MvPolynomial.eval ![D, r] dc + 5 := by
    rw [hDgpdef, hqGdef]
    simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_X,
      MvPolynomial.eval_C]
    simp
  have hbecs : MvPolynomial.eval ![D, r] becs
      = MvPolynomial.eval ![MvPolynomial.eval ![D, r] dtup, MvPolynomial.eval ![D, r] dc] bec := by
    rw [hbecsdef, Work.WilG4c.eval_aeval_eq]
    have hfun : (fun i : Fin 2 => MvPolynomial.eval ![D, r] (![dtup, dc] i))
        = ![MvPolynomial.eval ![D, r] dtup, MvPolynomial.eval ![D, r] dc] := by
      funext i
      fin_cases i <;> simp
    rw [hfun]
  set DgL : ℕ := MvPolynomial.eval ![Dgp + 2 * MvPolynomial.eval ![D, r] dc + 5, r] bL
    with hDgLdef
  set DgΦ : ℕ := (MvPolynomial.eval ![D, r] becs + (p + 1) * DgL + C0)
      + (MvPolynomial.eval ![D, r] bψ + ((p + 1) + n)
          * (MvPolynomial.eval ![D, r] becs + (p + 1) * DgL + C1) + C1) with hDgΦdef
  have hbpL : MvPolynomial.eval ![D, r] bpL
      = MvPolynomial.eval ![Dgp + 2 * MvPolynomial.eval ![D, r] dc + 5, r] bL := by
    rw [hbpLdef, Work.WilG4c.eval_aeval_eq]
    have hfun : (fun i : Fin 2 => MvPolynomial.eval ![D, r] (![qG, MvPolynomial.X 1] i))
        = ![MvPolynomial.eval ![D, r] qG, r] := by
      funext i
      fin_cases i <;> simp
    rw [hfun, hqGe]
  have hbfin : MvPolynomial.eval ![D, r] bfin = DgΦ := by
    rw [hbfindef, hDgΦdef]
    simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C, hbecs, hbpL]
    ring
  have hcfine : MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cfin
      = MvPolynomial.eval ![((Dgp + 2 * MvPolynomial.eval ![D, r] dc + 5 : ℕ) : ℝ), (r : ℝ),
          (k : ℝ), -Real.log (ε / 2)] cL := by
    rw [hcfin0 D r k (-Real.log ε)]
    have hX : ((MvPolynomial.eval ![D, r] qG : ℕ) : ℝ)
        = ((Dgp + 2 * MvPolynomial.eval ![D, r] dc + 5 : ℕ) : ℝ) := by rw [hqGe]
    rw [hX, hcpdef, Work.WilkG4c.eval_eval₂_C_real]
    have hfun : (fun i : Fin 4 => MvPolynomial.eval
        ![((Dgp + 2 * MvPolynomial.eval ![D, r] dc + 5 : ℕ) : ℝ), (r : ℝ), (k : ℝ), -Real.log ε]
        (if i = 3 then MvPolynomial.X 3 + MvPolynomial.C (Real.log 2) else MvPolynomial.X i))
        = ![((Dgp + 2 * MvPolynomial.eval ![D, r] dc + 5 : ℕ) : ℝ), (r : ℝ), (k : ℝ),
            -Real.log (ε / 2)] := by
      funext i
      fin_cases i <;>
        simp [Real.log_div hε.ne' (by norm_num : (2 : ℝ) ≠ 0)] <;> ring
    rw [hfun]
  -- ## the cell chart
  have hk1 : 1 ≤ kt := by
    obtain ⟨a0, _⟩ := hid
    have := a0.isLt
    omega
  have hdec := (IsCylDecomp.eq_2 p C).mp hCdec
  have hcellpc : IsPreconnected κ := Work.WilE7.isPreconnected_of_isCell (hdec.1 κ hκC).1
  have hcellne : κ.Nonempty := (hdec.1 κ hκC).2
  obtain ⟨iD, hdom⟩ :=
    Work.WilkG4c.DominatingCell S p kt hk1 ({κ} : Finset (Set (Fin (p + 1) → ℝ))) Tm
      (fun κ' hκ' => by
        rw [Finset.mem_singleton] at hκ'; subst hκ'; exact hcellpc)
      (fun κ' hκ' => by
        rw [Finset.mem_singleton] at hκ'; subst hκ'; exact hcellne)
      (fun κ' hκ' i w hw => by
        rw [Finset.mem_singleton] at hκ'; subst hκ'; exact hTsm i w hw)
      (fun a b κ' hκ' => by
        rw [Finset.mem_singleton] at hκ'; subst hκ'; exact hdich a b)
      κ (Finset.mem_singleton_self κ)
  obtain ⟨χ, hχg, hχmem, hχdiff, hχsurj⟩ :=
    hEC (MvPolynomial.eval ![D, r] dtup) (MvPolynomial.eval ![D, r] dc) kt PK C κ Tm
      hid (fun a => hTmΩ a) hκΩ hTval hCdec hκC hκcube hTsm ⟨iD, hdom⟩
      (fun l hl => (hPKmem l).mp hl)
  have hχg' : ∀ j : Fin 1, WilkiesDesign.CG.famGraph (χ j) ∈
      S.Ω aec (MvPolynomial.eval ![D, r] becs) (p + 1 + 1) := by
    intro j
    rw [hbecs]
    exact hχg j
  -- ## the piece data (the per-cell analytic core)
  obtain ⟨hYpiece, hLpiece⟩ :=
    Work.WilG4c.GoodCellPieceData S n p Cpc hCpc_ge κ PK k kt r D hr F ψ χ Tm γ hψnm hχmem
      hχdiff hid hγmax hκbad hκC1 hTsm hcx hγx hγd
  -- ## the patched family
  set G : Work.WilkG4c.Family k p (n + 1) := fun i l z =>
      if l ∈ PK then Work.WilkG4c.pieceFam (Work.WilkG4c.yPullback F ψ)
        (Work.WilG4c.chartFun χ) i l z else (1 / 2 : ℝ) with hGdef
  have hGmem : ∀ i l z, l ∈ PK → G i l z
      = Work.WilkG4c.pieceFam (Work.WilkG4c.yPullback F ψ) (Work.WilG4c.chartFun χ) i l z := by
    intro i l z hl
    rw [hGdef]
    simp [hl]
  have hGout : ∀ i l z, l ∉ PK → G i l z = (1 / 2 : ℝ) := by
    intro i l z hl
    rw [hGdef]
    simp [hl]
  have hhalf : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by norm_num
  obtain ⟨hYbG, hLipG⟩ :=
    iteFam_ybound_lip PK
      (Work.WilkG4c.pieceFam (Work.WilkG4c.yPullback F ψ) (Work.WilG4c.chartFun χ)) G (1 / 2)
      hhalf r Cpc hCpc0 hYpiece hLpiece hGmem hGout
  have hvalG : Work.WilkG4c.ValuesIn01 (Λ ∩ PK) G := by
    intro i l hl x hx
    rw [hGmem i l x hl.2, Work.WilkG4c.pieceFam_apply, Work.WilkG4c.yPullback_cons]
    set y : Fin (n + 1) → ℝ := Fin.cons (Work.WilG4c.chartFun χ l (x 0))
      (fun j => ψ j (Fin.snoc l (Work.WilG4c.chartFun χ l (x 0))) (Fin.tail x)) with hydef
    have hx0I : Work.WilG4c.chartFun χ l (x 0) ∈ Work.WilkG4c.I :=
      (hχmem l hl.2 (fun _ : Fin 1 => x 0) (by intro j; exact hx 0)).1
    have hycube : y ∈ WilkiesDesign.openCube (n + 1) := by
      intro j
      induction j using Fin.cases with
      | zero => rw [hydef]; simpa [Work.WilkG4c.I, Set.mem_Ioo] using hx0I
      | succ k =>
          rw [hydef]
          simpa using hψcube l (Work.WilG4c.chartFun χ l (x 0)) hx0I (Fin.tail x)
            (fun j => hx j.succ) k
    exact hval i l hl.1 y hycube
  have hpieceg : ∀ i, WilkiesDesign.CG.famGraph
      (Work.WilkG4c.pieceFam (Work.WilkG4c.yPullback F ψ) (Work.WilG4c.chartFun χ) i) ∈
      S.Ω (F0 + aψ + aec + Apg) Dgp (p + (n + 1) + 1) := by
    intro i
    rw [hDgpdef]
    exact hPG F0 D aψ (MvPolynomial.eval ![D, r] bψ) aec (MvPolynomial.eval ![D, r] becs)
      F ψ χ hΩg hψg hχg' i
  have hPKΩ : PK ∈ S.Ω (F1 + 1) (MvPolynomial.eval ![D, r] dc) p := by
    rw [hPKdef]
    exact S.proj hκΩ
  have hΩG : ∀ i, WilkiesDesign.CG.famGraph (G i) ∈ S.Ω
      ((F0 + aψ + aec + Apg) + (F1 + 1) + 3 * (p + (n + 1) + 1) + 3 * p + 6)
      (Dgp + 2 * MvPolynomial.eval ![D, r] dc + 5) (p + (n + 1) + 1) := by
    intro i
    exact IteFamGraphMem S PK (1 / 2)
      (Work.WilkG4c.pieceFam (Work.WilkG4c.yPullback F ψ) (Work.WilG4c.chartFun χ)) G i
      (F1 + 1) (MvPolynomial.eval ![D, r] dc) (F0 + aψ + aec + Apg) Dgp hPKΩ (hpieceg i)
      (fun l t hl => hGmem i l t hl) (fun l t hl => hGout i l t hl)
  -- ## the `hP1` application to the patched family
  obtain ⟨Ψ, hΨcard, hΨok, hΨcov⟩ :=
    hL (Dgp + 2 * MvPolynomial.eval ![D, r] dc + 5) r k (ε / 2) (by linarith) (by linarith)
      (Λ ∩ PK) G ⟨hYbG, hLipG⟩ hΩG hvalG
  have hΨcard' : (Ψ.card : ℝ)
      ≤ MvPolynomial.eval ![((Dgp + 2 * MvPolynomial.eval ![D, r] dc + 5 : ℕ) : ℝ), (r : ℝ),
          (k : ℝ), -Real.log (ε / 2)] cL := hΨcard
  have hΨokP : Work.WilkG4c.ChartsOK S aL
      (MvPolynomial.eval ![(Dgp + 2 * MvPolynomial.eval ![D, r] dc + 5), r] bL) r (Λ ∩ PK)
      (Work.WilkG4c.pieceFam (Work.WilkG4c.yPullback F ψ) (Work.WilG4c.chartFun χ)) Ψ :=
    ChartsOK_congr (fun i l hl t => hGmem i l t hl.2) hΨok
  have hΨokP' : Work.WilkG4c.ChartsOK S aL DgL r (Λ ∩ PK)
      (Work.WilkG4c.pieceFam (Work.WilkG4c.yPullback F ψ) (Work.WilG4c.chartFun χ)) Ψ := by
    rw [hDgLdef]; exact hΨokP
  -- ## the transport of the piece charts to `F`
  obtain ⟨Φ, sel, hΦcard, hΦok, hΦmem, hΦid⟩ :=
    PieceChartsToFGiven S p n k r F ψ χ (Λ ∩ PK) aψ
      (MvPolynomial.eval ![D, r] bψ) aec (MvPolynomial.eval ![D, r] becs) A0 C0 A1 C1
      hψg (hχg' 0)
      (fun a Dg χ' hχ' => hz0 aec (MvPolynomial.eval ![D, r] becs) a Dg χ χ'
        (hχg' 0) hχ')
      (fun a Dg χ' j hχ' => hs1 aψ (MvPolynomial.eval ![D, r] bψ) aec
        (MvPolynomial.eval ![D, r] becs) a Dg ψ χ χ' j hψg (hχg' 0) hχ')
      (fun l hl t ht => (hχmem l hl.2 t ht).1)
      (fun l hl τ hτ u hu => hψcube l τ hτ u hu)
      aL DgL Ψ hΨokP'
  have hΦok' : Work.WilkG4c.ChartsOK S aΦ DgΦ r (Λ ∩ PK) F Φ := by
    rw [haΦdef, hDgΦdef]
    exact hΦok
  -- ## clamping the charts to the whole parameter set
  have hhalfCube : (fun _ : Fin (n + 1) => (1 / 2 : ℝ)) ∈ WilkiesDesign.openCube (n + 1) := by
    intro j; norm_num
  set mod : Work.WilkG4c.ChartTuple p (n + 1) → Work.WilkG4c.ChartTuple p (n + 1) :=
    fun φ j l t => if l ∈ PK then φ j l t else (1 / 2 : ℝ) with hmoddef
  have hmodin : ∀ φ j l, l ∈ PK → ∀ t : Fin (n + 1) → ℝ, mod φ j l t = φ j l t := by
    intro φ j l hl t; rw [hmoddef]; simp [hl]
  have hmodout : ∀ φ j l, l ∉ PK → ∀ t : Fin (n + 1) → ℝ, mod φ j l t = (1 / 2 : ℝ) := by
    intro φ j l hl t; rw [hmoddef]; simp [hl]
  have hΩmod : ∀ φ ∈ Φ, ∀ j : Fin (n + 1), WilkiesDesign.CG.famGraph ((mod φ) j) ∈
      S.Ω (aΦ + (F1 + 1) + 3 * (p + (n + 1) + 1) + 3 * p + 6)
        (DgΦ + 2 * MvPolynomial.eval ![D, r] dc + 5) (p + (n + 1) + 1) := by
    intro φ hφ j
    have hφmem : WilkiesDesign.CG.famGraph (φ j) ∈ S.Ω aΦ DgΦ (p + (n + 1) + 1) :=
      (hΦok' φ hφ).1 j
    exact IteFamGraphMemGen S PK (1 / 2) (fun _ : Fin 1 => φ j)
      (fun _ : Fin 1 => (mod φ) j) 0 (F1 + 1) (MvPolynomial.eval ![D, r] dc) aΦ DgΦ hPKΩ
      hφmem (fun l t hl => by simp only [hmodin φ j l hl])
      (fun l t hl => by simp only [hmodout φ j l hl])
  have hΦokU : ∀ φ ∈ Φ, ∀ l, l ∈ Λ ∩ PK →
      (∀ t ∈ WilkiesDesign.openCube (n + 1),
        (fun j => φ j l t) ∈ WilkiesDesign.openCube (n + 1)) ∧
      ∀ i, ContDiffOn ℝ r (fun t => F i l (fun j => φ j l t))
          (WilkiesDesign.openCube (n + 1)) ∧
        ∀ m, m ≤ r → ∀ t ∈ WilkiesDesign.openCube (n + 1),
          ‖iteratedFDeriv ℝ m (fun t => F i l (fun j => φ j l t)) t‖ ≤ 1 :=
    fun φ hφ l hl => (hΦok' φ hφ).2 l hl
  obtain ⟨Φ', hΦ'mem, hΦ'card, hΦ'ok⟩ :=
    Work.WilkG4c.ChartsOK_clamp_aux (S := S) (p := p) (n := n + 1) (k := k) (r := r)
      (Λ := Λ) (Λ' := PK) (F := F) (Φ := Φ) (c := fun _ : Fin (n + 1) => (1 / 2 : ℝ))
      hhalfCube hval mod hmodin hmodout hΩmod hΦokU
  refine ⟨Φ', ?_, ?_, ?_⟩
  · calc (Φ'.card : ℝ) ≤ (Φ.card : ℝ) := by exact_mod_cast hΦ'card
      _ ≤ (Ψ.card : ℝ) := by exact_mod_cast hΦcard
      _ ≤ MvPolynomial.eval ![((Dgp + 2 * MvPolynomial.eval ![D, r] dc + 5 : ℕ) : ℝ),
            (r : ℝ), (k : ℝ), -Real.log (ε / 2)] cL := hΨcard'
      _ = MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cfin := hcfine.symm
  · rw [show MvPolynomial.eval ![D, r] (bfin + MvPolynomial.C 2 * dc + MvPolynomial.C 5)
        = DgΦ + 2 * MvPolynomial.eval ![D, r] dc + 5 from by
      simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C, hbfin]]
    exact hΦ'ok
  · -- the `ε`-cover, conditional on the `ψ`-cover of the fibre at the point
    intro l hl x hx hmem hfib
    obtain ⟨φ, hφmem, t, ht, hlt⟩ :=
      Work.WilG4c.GoodCellCoverLCond Λ F ψ χ κ Ψ Φ sel ε
        (fun l hl _ s hs hsnoc => hχsurj l ((hPKmem l).mpr ⟨s, hsnoc⟩) s hs hsnoc)
        (fun l hl hPKex z hz => by
          obtain ⟨ψ', hψ'mem, t', ht', hlt'⟩ :=
            hΨcov l ⟨hl, (hPKmem l).mpr hPKex⟩ z hz
          refine ⟨ψ', hψ'mem, t', ht', fun i => ?_⟩
          have hPKl : l ∈ PK := (hPKmem l).mpr hPKex
          simpa [hGmem i l (fun j => ψ' j l t') hPKl, hGmem i l z hPKl] using hlt' i)
        hΦmem
        (fun ψ' hψ' l hl hPKex t' ht' i =>
          hΦid ψ' hψ' l ⟨hl, (hPKmem l).mpr hPKex⟩ t' ht' i)
        l hl x hx hmem hfib
    refine ⟨mod φ, hΦ'mem φ hφmem, t, ht, fun i => ?_⟩
    have hPKl : l ∈ PK := (hPKmem l).mpr ⟨x 0, hmem⟩
    have hpt : (fun j => mod φ j l t) = (fun j => φ j l t) :=
      funext fun j => hmodin φ j l hPKl t
    rw [hpt]
    exact hlt i

end Work.WilG4c
