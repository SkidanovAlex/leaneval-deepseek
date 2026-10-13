import Mathlib
import Submission.Work.WilG4c.GoodCellChartsCond
import Submission.Work.WilG4c.BadCellCharts
import Submission.Work.WilG4c.CurveFam
import Submission.Work.WilG4c.YPullback
import Submission.Work.WilkG4c.StepTupleMem
import Submission.Work.WilG4c.StepCleanDefs
import Submission.Work.WilG4c.FLemAPI
import Submission.Work.WilG4c.StepLipAux
import Submission.Work.WilG4c.BadLocusThin
import Submission.Work.WilG4c.badCurveStrip_interior_empty
import Submission.Work.WilG4c.badCurveStrip_interior_emptyW
import Submission.Work.WilG4a.F1AffineW
import Submission.Work.WilG4c.ChartsOK_clamp
import Submission.Work.WilkG4c.YPullbackBound
import Submission.Work.WilkG4c.YPullbackGraph
import Submission.Work.WilG4c.C1AllComplThinClean
import Submission.Work.WilG4c.IteFamGraphMemGen
import Submission.Work.WilkG4c.eval_mono

set_option maxHeartbeats 1600000

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-- `z ∈ inCubeSet p 1` is the statement that the last coordinate lies in `I`. -/
theorem mem_inCubeSet_one {p : ℕ} {z : Fin (p + 1) → ℝ} :
    z ∈ Work.WilG4c.inCubeSet p 1 ↔ z (Fin.last p) ∈ Work.WilkG4c.I := by
  rw [Work.WilG4c.inCubeSet]
  simp only [Set.mem_ofPred_eq]
  have h0 : Fin.natAdd p (0 : Fin 1) = Fin.last p := by ext; simp [Fin.natAdd, Fin.last]
  simp only [WilkiesDesign.openCube, Work.WilkG4c.I, Set.mem_ofPred_eq, Set.mem_Ioo]
  constructor
  · intro h; rw [← h0]; exact h 0
  · intro h j; rw [Fin.eq_zero j, h0]; exact h

/-- `Fin.snoc l s` lies in the slab `inCubeSet p 1` whenever `s ∈ I`. -/
theorem snoc_mem_inCubeSet {p : ℕ} {l : Fin p → ℝ} {s : ℝ}
    (hs : s ∈ Work.WilkG4c.I) : Fin.snoc l s ∈ Work.WilG4c.inCubeSet p 1 := by
  rw [mem_inCubeSet_one]; simpa using hs

/-- **One cell of the `§5.3` three-way dispatch.**

`κ` is a cell of the cylindrical decomposition `C` of the `(λ,x)`-space `ℝ^{p+1}`, already tested
against the three families of bad sets (`badCurve (yPullback F ψ i)`, `C1All (yPullback F ψ i)`,
`inCubeSet p 1`) by the refinement step, and carrying the `C¹`/value/comparison data of the §5.3
tuple `Tm` and of the near-maximising curve `γ`.  Then `F` admits charts valid on all of `Λ` with
the `FLemP` per-chart conditions, covering to within `ε` every cube point whose distinguished
coordinate lies in `κ` for which the `y`-chart `ψ` already approximates the value fibre.

The value bound is taken **globally** (`ValuesIn01 Set.univ F`): the thinness of
`badCurve (yPullback F ψ i) ∩ inCubeSet` (`badCurveStrip_interior_empty`) needs the value bound
at every parameter.  (In the intended application the family is first clamped outside `Λ`, so
`Λ` is arbitrary and `hκfib` of `GoodCellChartsCond` is supplied on `Λ ∩ PK` and re-clamped.)

The three mechanisms: a **good** cell (disjoint from `badCurve` and contained in `C1All` and in
`inCubeSet`) is handled by `GoodCellChartsCond`; a **bad** cell has empty interior
(`badCurveStrip_interior_empty`, `C1AllComplThin`, `badLoc_thin`) and is a graph cell in the last
coordinate (pin, `ih`) or a band over a thin base (section, `hind`), i.e. `BadCellCharts`. -/
theorem PerCellDispatch (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv)
    (n p : ℕ) (hn : 1 ≤ n) (h1 : ∀ q, Work.WilG4a.F1AffineW S q)
    (ih : ∀ q, WilkiesDesign.CG.FLem S q n) (hchoice : Work.WilkG4c.ChoiceHyp S)
    (hbdd : Work.WilkG4c.BddDxHyp S)
    (hP1 : Work.WilkG4c.FLemP S p (n + 1) (Work.WilkG4c.PYLip p n))
    (hind : ∀ q : ℕ, q < p → Work.WilkG4c.FLemPHigh S q (n + 1) (Work.WilkG4c.PY q n))
    (F0 Ag : ℕ) (Bg : MvPolynomial (Fin 2) ℕ) (aψ : ℕ) (bψ Ftup : ℕ)
    (dtup : MvPolynomial (Fin 2) ℕ) (F1 : ℕ) (dc : MvPolynomial (Fin 2) ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : MvPolynomial (Fin 4) ℝ),
    ∀ (D r k : ℕ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hr : 1 ≤ r)
      (Λ : Set (Fin p → ℝ)) (F : Work.WilkG4c.Family k p (n + 1))
      (hΩg : ∀ i, WilkiesDesign.CG.famGraph (F i) ∈ S.Ω F0 D (p + (n + 1) + 1))
      (hPY : Work.WilkG4c.PY p n r k F) (hvalU : Work.WilkG4c.ValuesIn01 Set.univ F)
      (ψ : Work.WilkG4c.ChartTuple (p + 1) n)
      (hψg : ∀ j, WilkiesDesign.CG.famGraph (ψ j) ∈
        S.Ω aψ (MvPolynomial.eval ![D, r] bψ) ((p + 1) + n + 1))
      (hψcube : ∀ l, ∀ x ∈ Work.WilkG4c.I, ∀ t ∈ WilkiesDesign.openCube n,
        (fun j => ψ j (Fin.snoc l x) t) ∈ WilkiesDesign.openCube n)
      (hψsm : ∀ i, ∀ l, ∀ x ∈ Work.WilkG4c.I,
        ContDiffOn ℝ r (fun t => F i l (Fin.cons x (fun j => ψ j (Fin.snoc l x) t)))
          (WilkiesDesign.openCube n))
      (hψnm : ∀ i, ∀ l, ∀ x ∈ Work.WilkG4c.I, ∀ m, m ≤ r → ∀ t ∈ WilkiesDesign.openCube n,
        ‖iteratedFDeriv ℝ m (fun t => F i l (Fin.cons x (fun j => ψ j (Fin.snoc l x) t))) t‖ ≤ 1)
      (γ : Fin k → (Fin p → ℝ) → ℝ → (Fin n → ℝ))
      (hγg : ∀ i j, WilkiesDesign.graphOf (fun w : Fin (p + 1) → ℝ =>
        γ i (Fin.init w) (w (Fin.last p)) j) ∈
        S.Ω Ag (MvPolynomial.eval ![D, 0] Bg) (p + 1 + 1))
      (hγmax : ∀ i l x, Work.WilkG4c.NearMax (Work.WilkG4c.yPullback F ψ i) l x →
        γ i l x ∈ WilkiesDesign.openCube n ∧
        Work.WilkG4c.xPt l x (γ i l x) ∈
          interior {z | ContDiffAt ℝ 1 (Work.WilkG4c.famFunHat (Work.WilkG4c.yPullback F ψ i)) z} ∧
        ∀ y' ∈ WilkiesDesign.openCube n,
          Work.WilkG4c.xPt l x y' ∈
            interior {z | ContDiffAt ℝ 1 (Work.WilkG4c.famFunHat (Work.WilkG4c.yPullback F ψ i)) z} →
          |Work.WilkG4c.xDeriv (Work.WilkG4c.yPullback F ψ i) l x y'| ≤
            2 * |Work.WilkG4c.xDeriv (Work.WilkG4c.yPullback F ψ i) l x (γ i l x)|)
      (kt : ℕ) (Tm : Fin kt → (Fin p → ℝ) → (Fin 1 → ℝ) → ℝ)
      (hTmΩ : ∀ a, WilkiesDesign.CG.famGraph (Tm a) ∈
        S.Ω Ftup (MvPolynomial.eval ![D, r] dtup) (p + 1 + 1))
      (hid : ∃ a : Fin kt, ∀ l u, Tm a l u = u 0)
      (hγx : ∀ i j, ∃ a : Fin kt, ∀ l u, Tm a l u = γ i l (u 0) j)
      (hcx : ∀ i, ∃ a : Fin kt, ∀ l u,
        Tm a l u = Work.WilkG4c.yPullback F ψ i l (Fin.cons (u 0) (γ i l (u 0))))
      (C : Finset (Set (Fin (p + 1) → ℝ))) (hCdec : WilkiesDesign.IsCylDecomp (p + 1) C)
      (κ : Set (Fin (p + 1) → ℝ)) (hκC : κ ∈ C)
      (hκΩ : κ ∈ S.Ω F1 (MvPolynomial.eval ![D, r] dc) (p + 1))
      (hκcube : κ ⊆ Work.WilG4c.inCubeSet p 1 ∨ Disjoint κ (Work.WilG4c.inCubeSet p 1))
      (hκbad : ∀ i, Disjoint κ (Work.WilkG4c.badCurve (Work.WilkG4c.yPullback F ψ i)) ∨
        κ ⊆ Work.WilkG4c.badCurve (Work.WilkG4c.yPullback F ψ i))
      (hκC1 : ∀ i, κ ⊆ Work.WilkG4c.C1All (Work.WilkG4c.yPullback F ψ i) ∨
        Disjoint κ (Work.WilkG4c.C1All (Work.WilkG4c.yPullback F ψ i)))
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
      (hγd : ∀ i j, ∀ w ∈ κ,
        DifferentiableAt ℝ (fun s : ℝ => γ i (Fin.init w) s j) (w (Fin.last p))),
      ∃ Φ : Finset (Work.WilkG4c.ChartTuple p (n + 1)),
        (Φ.card : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c ∧
        Work.WilkG4c.ChartsOK S a (MvPolynomial.eval ![D, r] b) r Λ F Φ ∧
        (∀ l ∈ Λ, ∀ x ∈ WilkiesDesign.openCube (n + 1), Fin.snoc l (x 0) ∈ κ →
          (∃ t ∈ WilkiesDesign.openCube n, ∀ i,
            |F i l (Fin.cons (x 0) (fun j => ψ j (Fin.snoc l (x 0)) t)) - F i l x| < ε / 2) →
          ∃ φ ∈ Φ, ∃ t ∈ WilkiesDesign.openCube (n + 1),
            ∀ i, |F i l (fun j => φ j l t) - F i l x| < ε) := by
  classical
  obtain ⟨ag, bg, cg, hGg⟩ :=
    Work.WilG4c.GoodCellChartsCond S n p hP1 aψ Ag Ftup F0 F1 bψ Bg dtup dc
  obtain ⟨ab, bb, cb, hBg⟩ :=
    BadCellCharts S hcd hder n p hn hchoice ih hind F0 F1 dc
  refine ⟨max (ag + (F1 + 1) + 3 * (p + (n + 1) + 1) + 3 * p + 6) ab,
    (bg + MvPolynomial.C 2 * dc + MvPolynomial.C 5) + bb,
    (cg * cg + cb * cb) + (cg + cb) + 1, ?_⟩
  intro D r k ε hε hε1 hr Λ F hΩg hPY hvalU ψ hψg hψcube hψsm hψnm γ hγg hγmax
    kt Tm hTmΩ hid hγx hcx C hCdec κ hκC hκΩ hκcube hκbad hκC1 hTsm hTval hdich hγd
  have hvalΛ : Work.WilkG4c.ValuesIn01 Λ F :=
    fun i l _ x hx => hvalU i l (Set.mem_univ l) x hx
  -- the degree `eval ![D,r] Bg` dominates the degree `eval ![D,0] Bg` of the curve graphs
  have hγg' : ∀ i j, WilkiesDesign.graphOf (fun w : Fin (p + 1) → ℝ =>
      γ i (Fin.init w) (w (Fin.last p)) j) ∈ S.Ω Ag (MvPolynomial.eval ![D, r] Bg) (p + 1 + 1) := by
    intro i j
    refine Work.WilkG4c.Omega_mono_D_le S ?_ (hγg i j)
    exact Work.WilkG4c.eval_mono Bg (fun i => by fin_cases i <;> simp)
  -- the projection of the cell onto the parameter space
  set PK : Set (Fin p → ℝ) := {l | ∃ s : ℝ, Fin.snoc l s ∈ κ} with hPKdef
  have hPKmem : ∀ l : Fin p → ℝ, l ∈ PK ↔ ∃ s : ℝ, Fin.snoc l s ∈ κ := fun l => by simp [hPKdef]
  have hPKΩ : PK ∈ S.Ω (F1 + 1) (MvPolynomial.eval ![D, r] dc) p := by
    rw [hPKdef]; exact S.proj hκΩ
  by_cases hB1 : κ ⊆ Work.WilG4c.inCubeSet p 1
  · by_cases hgood : (∀ i, Disjoint κ (Work.WilkG4c.badCurve (Work.WilkG4c.yPullback F ψ i))) ∧
        (∀ i, κ ⊆ Work.WilkG4c.C1All (Work.WilkG4c.yPullback F ψ i))
    · -- ## the good cell
      obtain ⟨hB2, hB3⟩ := hgood
      obtain ⟨Φg, hcardg, hokg, hcovg⟩ :=
        hGg D r k ε hε hε1 hr (Λ ∩ PK) F hΩg hPY
          (fun i l hl x hx => hvalΛ i l hl.1 x hx) ψ hψg hψcube hψsm hψnm γ
          hγg' hγmax C hCdec κ hκC hκΩ hB1 hB2 hB3
          (fun l hl => (hPKmem l).mp hl.2) kt Tm hTmΩ hid hγx hcx hTsm hTval hdich hγd
      have hc : (fun _ : Fin (n + 1) => (1 / 2 : ℝ)) ∈ WilkiesDesign.openCube (n + 1) :=
        fun _ => by norm_num
      set mod : Work.WilkG4c.ChartTuple p (n + 1) → Work.WilkG4c.ChartTuple p (n + 1) :=
        fun φ j l t => if l ∈ PK then φ j l t else (1 / 2 : ℝ) with hmoddef
      have hmodin : ∀ φ j l, l ∈ PK → ∀ t : Fin (n + 1) → ℝ, mod φ j l t = φ j l t := by
        intro φ j l hl t; rw [hmoddef]; simp [hl]
      have hmodout : ∀ φ j l, l ∉ PK → ∀ t : Fin (n + 1) → ℝ, mod φ j l t = (1 / 2 : ℝ) := by
        intro φ j l hl t; rw [hmoddef]; simp [hl]
      have hΩmod : ∀ φ ∈ Φg, ∀ j : Fin (n + 1), WilkiesDesign.CG.famGraph ((mod φ) j) ∈
          S.Ω (ag + (F1 + 1) + 3 * (p + (n + 1) + 1) + 3 * p + 6)
            (MvPolynomial.eval ![D, r] bg + 2 * MvPolynomial.eval ![D, r] dc + 5)
            (p + (n + 1) + 1) := by
        intro φ hφ j
        have hφmem : WilkiesDesign.CG.famGraph (φ j) ∈
            S.Ω ag (MvPolynomial.eval ![D, r] bg) (p + (n + 1) + 1) := (hokg φ hφ).1 j
        exact Work.WilG4c.IteFamGraphMemGen S PK (1 / 2) (fun _ : Fin 1 => φ j)
          (fun _ : Fin 1 => (mod φ) j) 0 (F1 + 1) (MvPolynomial.eval ![D, r] dc) ag
          (MvPolynomial.eval ![D, r] bg) hPKΩ hφmem
          (fun l t hl => by simp only [hmodin φ j l hl])
          (fun l t hl => by simp only [hmodout φ j l hl])
      obtain ⟨Φ', hΦ'mem, hΦ'card, hΦ'ok⟩ :=
        Work.WilG4c.ChartsOK_clamp (S := S) (p := p) (n := n + 1) (k := k) (r := r)
          (a := ag + (F1 + 1) + 3 * (p + (n + 1) + 1) + 3 * p + 6)
          (Dg := MvPolynomial.eval ![D, r] bg + 2 * MvPolynomial.eval ![D, r] dc + 5)
          (Λ := Λ) (Λ' := PK) (F := F) (Φ := Φg) (c := fun _ : Fin (n + 1) => (1 / 2 : ℝ))
          hc hvalΛ mod hmodin hmodout hΩmod (fun φ hφ l hl => (hokg φ hφ).2 l hl)
      refine ⟨Φ', ?_, ?_, ?_⟩
      · have h1' : (Φ'.card : ℝ) ≤ (Φg.card : ℝ) := by exact_mod_cast hΦ'card
        have h2' : (Φg.card : ℝ) ≤
            MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cg := hcardg
        have h3' := Work.WilkG4c.le_mergePoly_left (Φ'.card : ℝ)
          (MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cg)
          (MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cb) (le_trans h1' h2')
        simpa only [MvPolynomial.eval_add, MvPolynomial.eval_mul, map_one] using h3'
      · refine Work.WilkG4c.ChartsOK_mono hΦ'ok (le_max_left _ _) ?_
        simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C]
        omega
      · intro l hl x hx hmem hfib
        have hlPK : l ∈ PK := (hPKmem l).mpr ⟨x 0, hmem⟩
        obtain ⟨φ, hφmem, t, ht, hlt⟩ := hcovg l ⟨hl, hlPK⟩ x hx hmem hfib
        refine ⟨mod φ, hΦ'mem φ hφmem, t, ht, fun i => ?_⟩
        have hpt : (fun j => mod φ j l t) = (fun j => φ j l t) :=
          funext (fun j => hmodin φ j l hlPK t)
        rw [hpt]
        exact hlt i
    · -- ## the bad cell
      have hκint : interior κ = ∅ := by
        rcases not_and_or.mp hgood with h2 | h3
        · obtain ⟨i0, hi0⟩ : ∃ i0, ¬ Disjoint κ
              (Work.WilkG4c.badCurve (Work.WilkG4c.yPullback F ψ i0)) := by
            by_contra hcon
            exact h2 (fun i => by by_contra hc; exact hcon ⟨i, hc⟩)
          have hsub : κ ⊆ Work.WilkG4c.badCurve (Work.WilkG4c.yPullback F ψ i0) :=
            (hκbad i0).resolve_left hi0
          have hval' : ∀ l : Fin p → ℝ, ∀ z ∈ WilkiesDesign.openCube (n + 1),
              Work.WilkG4c.yPullback F ψ i0 l z ∈ Set.Ioo (0 : ℝ) 1 := by
            intro l z hz
            rw [Work.WilkG4c.yPullback_apply]
            refine hvalU i0 l (Set.mem_univ l) _ ?_
            intro j
            induction j using Fin.cases with
            | zero => simpa using hz 0
            | succ k =>
                simpa using hψcube l (z 0) (hz 0) (Fin.tail z) (fun i => hz i.succ) k
          obtain ⟨apb, cpb, -, hpb⟩ := Work.WilkG4c.YPullbackGraph S F ψ F0 D aψ
            (MvPolynomial.eval ![D, r] bψ) hΩg hψg
          have hYall := (Work.WilkG4c.YPullbackBound F ψ Set.univ hr
            (fun l _ s hs t ht => hψcube l s hs t ht)
            (fun i l _ s hs => hψsm i l s hs)
            (fun i l _ s hs => hψnm i l s hs)).1
          have hY' : ∀ l : Fin p → ℝ, ∀ x ∈ Work.WilkG4c.I, ∀ m, m ≤ r →
              ∀ y ∈ WilkiesDesign.openCube n,
              ‖iteratedFDeriv ℝ m (Work.WilkG4c.slice (Work.WilkG4c.yPullback F ψ i0 l) x) y‖ ≤ 1 :=
            fun l x hx m hm y hy => hYall i0 l (Set.mem_univ l) x hx m hm y hy
          have hthin := Work.WilG4c.badCurveStrip_interior_emptyW S hcd hder hchoice h1 hr
            (hpb i0) hval' hY'
          refine Set.eq_empty_of_subset_empty ?_
          calc interior κ ⊆ interior {w : Fin (p + 1) → ℝ | w (Fin.last p) ∈ Work.WilkG4c.I ∧
                w ∈ Work.WilkG4c.badCurve (Work.WilkG4c.yPullback F ψ i0)} :=
                interior_mono (fun w hw => ⟨mem_inCubeSet_one.mp (hB1 hw), hsub hw⟩)
            _ = ∅ := hthin
        · obtain ⟨i0, hi0⟩ : ∃ i0, ¬ κ ⊆
              Work.WilkG4c.C1All (Work.WilkG4c.yPullback F ψ i0) := by
            by_contra hcon
            exact h3 (fun i => by by_contra hc; exact hcon ⟨i, hc⟩)
          have hdisj : Disjoint κ (Work.WilkG4c.C1All (Work.WilkG4c.yPullback F ψ i0)) :=
            (hκC1 i0).resolve_left hi0
          have hthin := Work.WilG4c.C1AllComplThinClean S hcd p n k r hr F ψ i0 F0 D aψ
            (MvPolynomial.eval ![D, r] bψ) (hΩg i0) hψg hψcube (hψsm i0) (hψnm i0)
          refine Set.eq_empty_of_subset_empty ?_
          calc interior κ ⊆ interior {w : Fin (p + 1) → ℝ | w (Fin.last p) ∈ Work.WilkG4c.I ∧
                w ∉ Work.WilkG4c.C1All (Work.WilkG4c.yPullback F ψ i0)} :=
                interior_mono (fun w hw => ⟨mem_inCubeSet_one.mp (hB1 hw), Set.disjoint_left.mp hdisj hw⟩)
            _ = ∅ := hthin
      obtain ⟨Φb, hcardb, hokb, hcovb⟩ :=
        hBg D r k ε hε hε1 hr Λ F hΩg hPY hvalΛ C hCdec κ hκC hκΩ hB1 hκint
      refine ⟨Φb, ?_, ?_, ?_⟩
      · have h3' := Work.WilkG4c.le_mergePoly_right (Φb.card : ℝ)
          (MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cg)
          (MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cb) hcardb
        simpa only [MvPolynomial.eval_add, MvPolynomial.eval_mul, map_one] using h3'
      · refine Work.WilkG4c.ChartsOK_mono hokb (le_max_right _ _) ?_
        simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C]
        omega
      · intro l hl x hx hmem _
        exact hcovb l hl x hx hmem
  · -- ## the cell is disjoint from the slab: vacuous
    have hB1d : Disjoint κ (Work.WilG4c.inCubeSet p 1) := hκcube.resolve_left hB1
    refine ⟨∅, ?_, ?_, ?_⟩
    · have hnn : (0 : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε]
          ((cg * cg + cb * cb) + (cg + cb) + 1) := by
        simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, map_one]
        nlinarith [
          sq_nonneg (MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cg + 1 / 2),
          sq_nonneg (MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cb + 1 / 2)]
      simpa using hnn
    · exact fun φ hφ => (Finset.notMem_empty φ hφ).elim
    · intro l hl x hx hmem _
      exact (Set.disjoint_left.mp hB1d hmem (snoc_mem_inCubeSet (hx 0))).elim

end Work.WilG4c
