/-
  WilG4c / `StepLipHighPsiCell` — the *per-cell* step of the §5.3 dispatch.

  This module holds the per-cell step `Work.WilG4c.psiCellDispatch` of the `§5.3` assembly: for a
  cell `κ` of a cylindrical decomposition of the `(λ,x)`-space refined against

  * the slab `inCubeSet p 1`,
  * the bad curves `badCurve (yPullback Fc ψ i)`,
  * the sets `C1All (yPullback Fc ψ i)`,
  * the `C¹`-loci of the members of the §5.3 tuple `Tm`,
  * the comparison sets `{|∂_s Tm a| = |∂_s Tm b|}`,

  the family `Fc` admits a `Finset` of chart tuples with the `FLemP` per-chart conditions, the
  count bound `eval ![Dc,r,k,-log ε] cMerge` and the *conditional* cover (the case in which the
  single `y`-chart `ψ` already `ε/2`-approximates the value fibre).

  The dispatch is the three-way one of the design of record:

  * **good cell** (in the slab, disjoint from the bad curves, contained in the `C1All`'s and in
    the `C¹`-loci of the tuple): `GoodCellChartsCond`, followed by clamping the charts off the
    parameter projection (so that the resulting family is valid on all of `Λ`);
  * **bad cell** (empty interior, because the cell then lies inside one of the thin sets):
    `BadCellCharts`;
  * **cell disjoint from the slab**: vacuous (the empty chart family).

  It is a separate module only because the `StepLipHighPsiCond` assembly together with this
  dispatch exceeds the per-file build limit.
-/
import Mathlib
import Submission.Work.WilG4c.StepLipHighAux
import Submission.Work.WilG4c.StepLipHighPsiAux2
import Submission.Work.WilG4c.GoodCellChartsCond
import Submission.Work.WilG4c.BadCellCharts
import Submission.Work.WilG4c.C1AllComplThinClean
import Submission.Work.WilG4c.badCurveStrip_interior_emptyW
import Submission.Work.WilG4c.ChartsOK_clamp
import Submission.Work.WilG4c.IteFamGraphMemGen
import Submission.Work.WilG4c.BadLocusThin
import Submission.Work.WilG4c.YPullback
import Submission.Work.WilkG4c.hasDerivAt_snoc
import Submission.Work.WilkG4c.eval_mono
import Submission.Work.WilG4a.F1AffineW

set_option autoImplicit false
set_option maxHeartbeats 3200000
noncomputable section
open Classical
open scoped BigOperators

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-- The §5.3 tuple, as a function of the reindexing type. -/
def psiTfun {k p n : ℕ} (Fc : Work.WilkG4c.Family k p (n + 1))
    (ψ : Work.WilkG4c.ChartTuple (p + 1) n)
    (γ : Fin k → (Fin p → ℝ) → ℝ → (Fin n → ℝ)) :
    (Fin 1 ⊕ (Fin k × Fin n) ⊕ Fin k) → (Fin p → ℝ) → (Fin 1 → ℝ) → ℝ :=
  fun s => match s with
    | Sum.inl _ => fun _ (u : Fin 1 → ℝ) => u 0
    | Sum.inr (Sum.inl ij) => fun l u => γ ij.1 l (u 0) ij.2
    | Sum.inr (Sum.inr i) => fun l u =>
        Work.WilkG4c.yPullback Fc ψ i l (Fin.cons (u 0) (γ i l (u 0)))

/-- The §5.3 tuple reindexed by `eIx`. -/
abbrev psiTm {k p n : ℕ} (Fc : Work.WilkG4c.Family k p (n + 1))
    (ψ : Work.WilkG4c.ChartTuple (p + 1) n)
    (γ : Fin k → (Fin p → ℝ) → ℝ → (Fin n → ℝ))
    {kt : ℕ} (eIx : (Fin 1 ⊕ (Fin k × Fin n) ⊕ Fin k) ≃ Fin kt) :
    Fin kt → (Fin p → ℝ) → (Fin 1 → ℝ) → ℝ :=
  fun a => psiTfun Fc ψ γ (eIx.symm a)

/-- The index family of the sets the §5.3 cell decomposition is refined against. -/
def psiXfun {k p n : ℕ} (Fc : Work.WilkG4c.Family k p (n + 1))
    (ψ : Work.WilkG4c.ChartTuple (p + 1) n) {kt : ℕ}
    (Tm : Fin kt → (Fin p → ℝ) → (Fin 1 → ℝ) → ℝ) :
    Fin 1 ⊕ Fin k ⊕ Fin k ⊕ Fin kt ⊕ (Fin kt × Fin kt) → Set (Fin (p + 1) → ℝ) :=
  fun s => match s with
    | Sum.inl _ => Work.WilG4c.inCubeSet p 1
    | Sum.inr (Sum.inl i) => Work.WilkG4c.badCurve (Work.WilkG4c.yPullback Fc ψ i)
    | Sum.inr (Sum.inr (Sum.inl i)) => Work.WilkG4c.C1All (Work.WilkG4c.yPullback Fc ψ i)
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl a))) => {w : Fin (p + 1) → ℝ | ContDiffAt ℝ 1
        (fun z : Fin (p + 1) → ℝ => Tm a (Fin.init z) (fun _ => z (Fin.last p))) w}
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr ab))) => {w : Fin (p + 1) → ℝ |
        |(fderiv ℝ (fun z : Fin (p + 1) → ℝ =>
            Tm ab.1 (Fin.init z) (fun _ => z (Fin.last p))) w) (Pi.single (Fin.last p) 1)|
        = |(fderiv ℝ (fun z : Fin (p + 1) → ℝ =>
            Tm ab.2 (Fin.init z) (fun _ => z (Fin.last p))) w) (Pi.single (Fin.last p) 1)|}

/-- **The per-cell step of the §5.3 dispatch.**

`C` is a cylindrical decomposition of `ℝ^{p+1}` refining each of the sets
`psiXfun Fc ψ Tm s` (`hXdisj`); the conclusion produces, uniformly over `κ ∈ C`, the chart
family of that cell, its count bound (`cMerge`) and its conditional cover.

The witnesses `aFin`, `bFin`, `cMerge` are chosen before `D, r, k, ε`: they only depend on the
polynomial data `bψ, dG, dtup, dc` and on the format data.  (`dFam` is the polynomial `3D+…`
of the parameter clamp and `hdFam` records that it dominates `D`.) -/
theorem psiCellDispatch
    (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv) (n p : ℕ)
    (hn : 1 ≤ n)
    (hP1 : Work.WilkG4c.FLemP S p (n + 1) (Work.WilkG4c.PYLip p n))
    (hchoice : Work.WilkG4c.ChoiceHyp S) (ih : ∀ q, WilkiesDesign.CG.FLem S q n)
    (hind : ∀ q : ℕ, q < p → Work.WilkG4c.FLemPHigh S q (n + 1) (Work.WilkG4c.PY q n))
    (h1 : ∀ q, Work.WilG4a.F1AffineW S q)
    (F0c F1 At aψ Ag : ℕ) (bψ dG dtup dc dFam : MvPolynomial (Fin 2) ℕ) :
    ∃ (aFin : ℕ) (bFin : MvPolynomial (Fin 2) ℕ) (cMerge : MvPolynomial (Fin 4) ℝ),
    ∀ (D r k : ℕ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hr : 1 ≤ r)
      (Λ : Set (Fin p → ℝ)) (Fc : Work.WilkG4c.Family k p (n + 1))
      (ψ : Work.WilkG4c.ChartTuple (p + 1) n)
      (γ : Fin k → (Fin p → ℝ) → ℝ → (Fin n → ℝ))
      (kt : ℕ) (eIx : (Fin 1 ⊕ (Fin k × Fin n) ⊕ Fin k) ≃ Fin kt)
      (F0pb Dc : ℕ) (qPb : MvPolynomial (Fin 2) ℕ)
      (hdFam : ∀ D r : ℕ, D ≤ MvPolynomial.eval ![D, r] dFam)
      (hΩFc : ∀ i, WilkiesDesign.CG.famGraph (Fc i) ∈ S.Ω F0c Dc (p + (n + 1) + 1))
      (hPYc : Work.WilkG4c.PY p n r k Fc)
      (hvalU : Work.WilkG4c.ValuesIn01 (Set.univ : Set (Fin p → ℝ)) Fc)
      (hψgD : ∀ j, WilkiesDesign.CG.famGraph (ψ j) ∈
        S.Ω aψ (MvPolynomial.eval ![Dc, r] bψ) ((p + 1) + n + 1))
      (hψcube : ∀ l, ∀ x ∈ Work.WilkG4c.I, ∀ t ∈ WilkiesDesign.openCube n,
        (fun j => ψ j (Fin.snoc l x) t) ∈ WilkiesDesign.openCube n)
      (hψsmc : ∀ i, ∀ l, ∀ x ∈ Work.WilkG4c.I,
        ContDiffOn ℝ r (fun t => Fc i l (Fin.cons x (fun j => ψ j (Fin.snoc l x) t)))
          (WilkiesDesign.openCube n))
      (hψnmc : ∀ i, ∀ l, ∀ x ∈ Work.WilkG4c.I, ∀ m, m ≤ r →
        ∀ t ∈ WilkiesDesign.openCube n,
          ‖iteratedFDeriv ℝ m (fun t => Fc i l (Fin.cons x (fun j => ψ j (Fin.snoc l x) t))) t‖
            ≤ 1)
      (hγgD : ∀ i j, WilkiesDesign.graphOf (fun w : Fin (p + 1) → ℝ =>
        γ i (Fin.init w) (w (Fin.last p)) j) ∈
          S.Ω Ag (MvPolynomial.eval ![Dc, r] dG) (p + 1 + 1))
      (hγmax : ∀ i l x, Work.WilkG4c.NearMax (Work.WilkG4c.yPullback Fc ψ i) l x →
        γ i l x ∈ WilkiesDesign.openCube n ∧
        Work.WilkG4c.xPt l x (γ i l x) ∈
          interior {z | ContDiffAt ℝ 1
            (Work.WilkG4c.famFunHat (Work.WilkG4c.yPullback Fc ψ i)) z} ∧
        ∀ y' ∈ WilkiesDesign.openCube n,
          Work.WilkG4c.xPt l x y' ∈
            interior {z | ContDiffAt ℝ 1
              (Work.WilkG4c.famFunHat (Work.WilkG4c.yPullback Fc ψ i)) z} →
          |Work.WilkG4c.xDeriv (Work.WilkG4c.yPullback Fc ψ i) l x y'| ≤
            2 * |Work.WilkG4c.xDeriv (Work.WilkG4c.yPullback Fc ψ i) l x (γ i l x)|)
      (hTmΩ : ∀ a : Fin kt, WilkiesDesign.CG.famGraph (psiTm Fc ψ γ eIx a) ∈
        S.Ω At (MvPolynomial.eval ![Dc, r] dtup) (p + 1 + 1))
      (hidT : ∃ a : Fin kt, ∀ (l : Fin p → ℝ) (u : Fin 1 → ℝ), psiTm Fc ψ γ eIx a l u = u 0)
      (hγxT : ∀ i j, ∃ a : Fin kt, ∀ (l : Fin p → ℝ) (u : Fin 1 → ℝ),
        psiTm Fc ψ γ eIx a l u = γ i l (u 0) j)
      (hcxT : ∀ i, ∃ a : Fin kt, ∀ (l : Fin p → ℝ) (u : Fin 1 → ℝ),
        psiTm Fc ψ γ eIx a l u =
          Work.WilkG4c.yPullback Fc ψ i l (Fin.cons (u 0) (γ i l (u 0))))
      (hGpmem : ∀ i, WilkiesDesign.CG.famGraph (Work.WilkG4c.yPullback Fc ψ i) ∈
        S.Ω F0pb (MvPolynomial.eval ![Dc, r] qPb) (p + (n + 1) + 1))
      (C : Finset (Set (Fin (p + 1) → ℝ))) (hCdec : WilkiesDesign.IsCylDecomp (p + 1) C)
      (hCΩ : ∀ κ ∈ C, κ ∈ S.Ω F1 (MvPolynomial.eval ![Dc, r] dc) (p + 1))
      (hXdisj : ∀ s : Fin 1 ⊕ Fin k ⊕ Fin k ⊕ Fin kt ⊕ (Fin kt × Fin kt), ∀ κ ∈ C,
        κ ⊆ psiXfun Fc ψ (psiTm Fc ψ γ eIx) s ∨
          Disjoint κ (psiXfun Fc ψ (psiTm Fc ψ γ eIx) s)),
      ∀ κ ∈ C, ∃ Φκ : Finset (Work.WilkG4c.ChartTuple p (n + 1)),
        (Φκ.card : ℝ) ≤
            MvPolynomial.eval ![(Dc : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cMerge ∧
        Work.WilkG4c.ChartsOK S aFin (MvPolynomial.eval ![Dc, r] bFin) r Λ Fc Φκ ∧
        (∀ l ∈ Λ, ∀ x' ∈ WilkiesDesign.openCube (n + 1), Fin.snoc l (x' 0) ∈ κ →
          (∃ t ∈ WilkiesDesign.openCube n, ∀ i,
            |Fc i l (Fin.cons (x' 0) (fun j => ψ j (Fin.snoc l (x' 0)) t)) - Fc i l x'|
              < ε / 2) →
          ∃ φ ∈ Φκ, ∃ t ∈ WilkiesDesign.openCube (n + 1),
            ∀ i, |Fc i l (fun j => φ j l t) - Fc i l x'| < ε) := by
  obtain ⟨aGg, bgGg, cGg, hGg⟩ :=
    GoodCellChartsCond S n p hP1 aψ Ag At F0c F1 bψ dG dtup dc
  obtain ⟨a_bc, b_bc, c_bc, hBCC⟩ :=
    BadCellCharts S hcd hder n p hn hchoice ih hind F0c F1 dc
  set aFin : ℕ := max (aGg + (F1 + 1) + 3 * (p + (n + 1) + 1) + 3 * p + 6) a_bc with haFin
  obtain ⟨bGg', hbGg'⟩ := Work.WilG4c.PolySubstFirst dFam bgGg
  obtain ⟨b_bc', hb_bc'⟩ := Work.WilG4c.PolySubstFirst dFam b_bc
  set bFin : MvPolynomial (Fin 2) ℕ := bGg' + b_bc' + (2 * dc + MvPolynomial.C 5) with hbFin
  set cMerge : MvPolynomial (Fin 4) ℝ := (cGg * cGg + c_bc * c_bc) + (cGg + c_bc) + 1
    with hcMerge
  refine ⟨aFin, bFin, cMerge, ?_⟩
  intro D r k ε hε hε1 hr Λ Fc ψ γ kt eIx F0pb Dc qPb hdFam hΩFc hPYc hvalU hψgD hψcube
    hψsmc hψnmc hγgD hγmax hTmΩ hidT hγxT hcxT hGpmem C hCdec hCΩ hXdisj
  intro κ hκC
  have hvalΛ : Work.WilkG4c.ValuesIn01 Λ Fc :=
    fun i l _ x hx => hvalU i l (Set.mem_univ l) x hx
  let Tm : Fin kt → (Fin p → ℝ) → (Fin 1 → ℝ) → ℝ := psiTm Fc ψ γ eIx
  let Xfun : Fin 1 ⊕ Fin k ⊕ Fin k ⊕ Fin kt ⊕ (Fin kt × Fin kt) → Set (Fin (p + 1) → ℝ) :=
    psiXfun Fc ψ Tm
  by_cases hB1 : κ ⊆ Work.WilG4c.inCubeSet p 1
  · by_cases hgood : (∀ i, Disjoint κ (Work.WilkG4c.badCurve (Work.WilkG4c.yPullback Fc ψ i))) ∧
        (∀ i, κ ⊆ Work.WilkG4c.C1All (Work.WilkG4c.yPullback Fc ψ i)) ∧
        (∀ a : Fin kt, κ ⊆ Xfun (Sum.inr (Sum.inr (Sum.inr (Sum.inl a)))))
    · -- ## the good cell
      obtain ⟨hgbad, hgC1, hgGs⟩ := hgood
      set PK : Set (Fin p → ℝ) := {l | ∃ s : ℝ, Fin.snoc l s ∈ κ} with hPK
      have hPKmem : ∀ l : Fin p → ℝ, l ∈ PK ↔ ∃ s : ℝ, Fin.snoc l s ∈ κ := fun l => Iff.rfl
      have hPKΩ : PK ∈ S.Ω (F1 + 1) (MvPolynomial.eval ![Dc, r] dc) p :=
        S.proj (hCΩ κ hκC)
      have hTsm : ∀ a : Fin kt, ∀ w ∈ κ, ContDiffAt ℝ 1
          (fun z : Fin (p + 1) → ℝ => Tm a (Fin.init z) (fun _ => z (Fin.last p))) w :=
        fun a w hw => hgGs a hw
      have hdich : ∀ a b : Fin kt, κ ⊆ Xfun (Sum.inr (Sum.inr (Sum.inr (Sum.inr (a, b))))) ∨
          Disjoint κ (Xfun (Sum.inr (Sum.inr (Sum.inr (Sum.inr (a, b)))))) :=
        fun a b => hXdisj (Sum.inr (Sum.inr (Sum.inr (Sum.inr (a, b))))) κ hκC
      have hnm : ∀ i, ∀ w ∈ κ, Work.WilkG4c.NearMax (Work.WilkG4c.yPullback Fc ψ i)
          (Fin.init w) (w (Fin.last p)) := by
        intro i w hw
        have hd := Set.disjoint_left.mp (hgbad i) hw
        simpa only [Work.WilkG4c.badCurve, Set.mem_ofPred_eq, not_not, Fin.init_def] using hd
      have hTval : ∀ a : Fin kt, ∀ w ∈ κ,
          Tm a (Fin.init w) (fun _ => w (Fin.last p)) ∈ Set.Ioo (0 : ℝ) 1 := by
        intro a w hw
        have hwI : w (Fin.last p) ∈ Work.WilkG4c.I :=
          (Work.WilkG4c.mem_inCubeSet_one').mp (hB1 hw)
        obtain ⟨s, rfl⟩ : ∃ s, a = eIx s :=
          ⟨eIx.symm a, (Equiv.apply_symm_apply eIx a).symm⟩
        rcases s with x | (s | i)
        · show psiTfun Fc ψ γ (eIx.symm (eIx (Sum.inl x))) (Fin.init w)
            (fun _ => w (Fin.last p)) ∈ Set.Ioo (0 : ℝ) 1
          rw [Equiv.symm_apply_apply]
          simpa only [psiTfun, Work.WilkG4c.I] using hwI
        · obtain ⟨i, j⟩ := s
          show psiTfun Fc ψ γ (eIx.symm (eIx (Sum.inr (Sum.inl (i, j))))) (Fin.init w)
            (fun _ => w (Fin.last p)) ∈ Set.Ioo (0 : ℝ) 1
          rw [Equiv.symm_apply_apply]
          simpa only [psiTfun] using
            (hγmax i (Fin.init w) (w (Fin.last p)) (hnm i w hw)).1 j
        · show psiTfun Fc ψ γ (eIx.symm (eIx (Sum.inr (Sum.inr i)))) (Fin.init w)
            (fun _ => w (Fin.last p)) ∈ Set.Ioo (0 : ℝ) 1
          rw [Equiv.symm_apply_apply]
          simp only [psiTfun]
          have hγc := (hγmax i (Fin.init w) (w (Fin.last p)) (hnm i w hw)).1
          refine hvalU i (Fin.init w) (Set.mem_univ _) _ ?_
          intro j
          rcases Fin.eq_zero_or_eq_succ j with h | ⟨j', rfl⟩
          · rw [h, Work.WilkG4c.pullbackMap_zero, Fin.cons_zero]; exact hwI
          · rw [Work.WilkG4c.pullbackMap_succ, Fin.cons_zero, Fin.tail_cons,
              Fin.snoc_init_self]
            simpa only [Fin.snoc_init_self] using hψcube (Fin.init w) (w (Fin.last p)) hwI
              (γ i (Fin.init w) (w (Fin.last p))) hγc j'
      have hγd : ∀ i j, ∀ w ∈ κ, DifferentiableAt ℝ
          (fun s : ℝ => γ i (Fin.init w) s j) (w (Fin.last p)) := by
        intro i j w hw
        obtain ⟨aγ, haγ⟩ := hγxT i j
        have hsm := hTsm aγ w hw
        have hflat : (fun z : Fin (p + 1) → ℝ =>
            Tm aγ (Fin.init z) (fun _ => z (Fin.last p)))
            = fun z => γ i (Fin.init z) (z (Fin.last p)) j := by
          funext z
          exact haγ (Fin.init z) (fun _ => z (Fin.last p))
        rw [hflat] at hsm
        have hd : DifferentiableAt ℝ
            (fun z : Fin (p + 1) → ℝ => γ i (Fin.init z) (z (Fin.last p)) j) w :=
          hsm.differentiableAt (by norm_num)
        have hd' : DifferentiableAt ℝ
            (fun z : Fin (p + 1) → ℝ => γ i (Fin.init z) (z (Fin.last p)) j)
            (Fin.snoc (Fin.init w) (w (Fin.last p))) := by
          rw [Fin.snoc_init_self]; exact hd
        have hslice : (fun s' : ℝ => γ i (Fin.init w) s' j)
            = (fun s' : ℝ => (fun z : Fin (p + 1) → ℝ =>
                γ i (Fin.init z) (z (Fin.last p)) j) (Fin.snoc (Fin.init w) s')) := by
          funext s'
          simp [Fin.init_snoc, Fin.snoc_last]
        rw [hslice]
        exact (Work.WilkG4c.hasDerivAt_snoc hd').differentiableAt
      obtain ⟨Φg, hGgcard, hGgok, hGgcov⟩ := hGg Dc r k ε hε hε1 hr (Λ ∩ PK) Fc hΩFc hPYc
        (fun i l _ x hx => hvalU i l (Set.mem_univ l) x hx) ψ hψgD hψcube hψsmc hψnmc γ
        hγgD hγmax C hCdec κ hκC (hCΩ κ hκC) hB1 hgbad hgC1 (fun l hl => (hPKmem l).mp hl.2)
        kt Tm hTmΩ hidT hγxT hcxT hTsm hTval hdich hγd
      have hc : (fun _ : Fin (n + 1) => (1 / 2 : ℝ)) ∈ WilkiesDesign.openCube (n + 1) :=
        fun _ => by norm_num
      set mod : Work.WilkG4c.ChartTuple p (n + 1) → Work.WilkG4c.ChartTuple p (n + 1) :=
        fun φ j l t => if l ∈ PK then φ j l t else (1 / 2 : ℝ) with hmod
      have hmodin : ∀ φ j l, l ∈ PK → ∀ t : Fin (n + 1) → ℝ, mod φ j l t = φ j l t := by
        intro φ j l hl t; rw [hmod]; simp [hl]
      have hmodout : ∀ φ j l, l ∉ PK → ∀ t : Fin (n + 1) → ℝ, mod φ j l t = (1 / 2 : ℝ) := by
        intro φ j l hl t; rw [hmod]; simp [hl]
      have hΩmod : ∀ φ ∈ Φg, ∀ j : Fin (n + 1), WilkiesDesign.CG.famGraph ((mod φ) j) ∈
          S.Ω (aGg + (F1 + 1) + 3 * (p + (n + 1) + 1) + 3 * p + 6)
            (MvPolynomial.eval ![Dc, r] bgGg + 2 * MvPolynomial.eval ![Dc, r] dc + 5)
            (p + (n + 1) + 1) := by
        intro φ hφ j
        have hφmem : WilkiesDesign.CG.famGraph (φ j) ∈
            S.Ω aGg (MvPolynomial.eval ![Dc, r] bgGg) (p + (n + 1) + 1) :=
          (hGgok φ hφ).1 j
        exact Work.WilG4c.IteFamGraphMemGen S PK (1 / 2) (fun _ : Fin 1 => φ j)
          (fun _ : Fin 1 => (mod φ) j) 0 (F1 + 1) (MvPolynomial.eval ![Dc, r] dc)
          aGg (MvPolynomial.eval ![Dc, r] bgGg) hPKΩ hφmem
          (fun l t hl => by simp only [hmodin φ j l hl])
          (fun l t hl => by simp only [hmodout φ j l hl])
      obtain ⟨Φ', hΦ'mem, hΦ'card, hΦ'ok⟩ :=
        Work.WilG4c.ChartsOK_clamp (S := S) (p := p) (n := n + 1) (k := k) (r := r)
          (Λ := Λ) (Λ' := PK) (F := Fc) (Φ := Φg) (c := fun _ : Fin (n + 1) => (1 / 2 : ℝ))
          hc (fun i l _ x hx => hvalU i l (Set.mem_univ l) x hx) mod hmodin hmodout hΩmod
          (fun φ hφ l hl => (hGgok φ hφ).2 l hl)
      refine ⟨Φ', ?_, ?_, ?_⟩
      · have hcard1 : (Φ'.card : ℝ) ≤ (Φg.card : ℝ) := by exact_mod_cast hΦ'card
        have hcard2 : (Φg.card : ℝ) ≤
            MvPolynomial.eval ![(Dc : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cGg := hGgcard
        have h3 := Work.WilkG4c.le_mergePoly_left (Φ'.card : ℝ)
          (MvPolynomial.eval ![(Dc : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cGg)
          (MvPolynomial.eval ![(Dc : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c_bc)
          (le_trans hcard1 hcard2)
        simpa only [hcMerge, MvPolynomial.eval_add, MvPolynomial.eval_mul, map_one] using h3
      · refine Work.WilkG4c.ChartsOK_mono hΦ'ok ?_ ?_
        · rw [haFin]; omega
        · rw [hbFin]
          simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C,
            map_ofNat]
          have hb : MvPolynomial.eval ![Dc, r] bgGg ≤ MvPolynomial.eval ![Dc, r] bGg' := by
            rw [hbGg' Dc r]
            refine Work.WilkG4c.eval_mono bgGg (fun i => ?_)
            fin_cases i
            · simpa using hdFam Dc r
            · simp
          omega
      · intro l hl x' hx' hmem hhyp
        obtain ⟨φ, hφ, t, ht, hlt⟩ :=
          hGgcov l ⟨hl, (hPKmem l).mpr ⟨x' 0, hmem⟩⟩ x' hx' hmem hhyp
        refine ⟨mod φ, hΦ'mem φ hφ, t, ht, fun i => ?_⟩
        have hpt : (fun j => mod φ j l t) = (fun j => φ j l t) :=
          funext (fun j => hmodin φ j l ((hPKmem l).mpr ⟨x' 0, hmem⟩) t)
        rw [hpt]
        exact hlt i
    · -- ## the bad cell
      have hκint : interior κ = ∅ := by
        rcases not_and_or.mp hgood with hA | hBC
        · obtain ⟨i0, hi0⟩ : ∃ i0, ¬ Disjoint κ
              (Work.WilkG4c.badCurve (Work.WilkG4c.yPullback Fc ψ i0)) := by
            by_contra hcon
            exact hA (fun i => by by_contra hc; exact hcon ⟨i, hc⟩)
          have hsub : κ ⊆ Work.WilkG4c.badCurve (Work.WilkG4c.yPullback Fc ψ i0) :=
            (hXdisj (Sum.inr (Sum.inl i0)) κ hκC).resolve_right hi0
          have hthin := Work.WilG4c.badCurveStrip_interior_emptyW S hcd hder hchoice h1 hr
            (hGpmem i0)
            (fun l z hz => by
              rw [Work.WilkG4c.yPullback_apply]
              exact hvalU i0 l (Set.mem_univ l) _ (by
                intro j
                refine Fin.cases ?_ ?_ j
                · simpa using hz 0
                · intro j'
                  simpa using hψcube l (z 0) (hz 0) (Fin.tail z) (fun k => hz k.succ) j'))
            (fun l x hx m hm y hy => by
              rw [Work.WilkG4c.slice_yPullback]
              exact hψnmc i0 l x hx m hm y hy)
          refine Set.eq_empty_of_subset_empty ?_
          calc interior κ ⊆ interior {w : Fin (p + 1) → ℝ | w (Fin.last p) ∈ Work.WilkG4c.I ∧
                w ∈ Work.WilkG4c.badCurve (Work.WilkG4c.yPullback Fc ψ i0)} :=
                interior_mono (fun w hw =>
                  ⟨(Work.WilkG4c.mem_inCubeSet_one').mp (hB1 hw), hsub hw⟩)
            _ = ∅ := hthin
        · rcases not_and_or.mp hBC with hB | hC
          · obtain ⟨i0, hi0⟩ : ∃ i0, ¬ κ ⊆
                Work.WilkG4c.C1All (Work.WilkG4c.yPullback Fc ψ i0) := by
              by_contra hcon
              exact hB (fun i => by by_contra hc; exact hcon ⟨i, hc⟩)
            have hdisj : Disjoint κ (Work.WilkG4c.C1All (Work.WilkG4c.yPullback Fc ψ i0)) :=
              (hXdisj (Sum.inr (Sum.inr (Sum.inl i0))) κ hκC).resolve_left hi0
            have hthin := Work.WilG4c.C1AllComplThinClean S hcd p n k r hr Fc ψ i0 F0c
              Dc aψ (MvPolynomial.eval ![Dc, r] bψ)
              (hΩFc i0) hψgD hψcube (hψsmc i0) (hψnmc i0)
            refine Set.eq_empty_of_subset_empty ?_
            calc interior κ ⊆ interior {w : Fin (p + 1) → ℝ | w (Fin.last p) ∈ Work.WilkG4c.I ∧
                  w ∉ Work.WilkG4c.C1All (Work.WilkG4c.yPullback Fc ψ i0)} :=
                  interior_mono (fun w hw => ⟨(Work.WilkG4c.mem_inCubeSet_one').mp (hB1 hw),
                    Set.disjoint_left.mp hdisj hw⟩)
              _ = ∅ := hthin
          · obtain ⟨a0, ha0⟩ : ∃ a0 : Fin kt, ¬ κ ⊆
                Xfun (Sum.inr (Sum.inr (Sum.inr (Sum.inl a0)))) := by
              by_contra hcon
              exact hC (fun a => by by_contra hc; exact hcon ⟨a, hc⟩)
            have hdisj : Disjoint κ (Xfun (Sum.inr (Sum.inr (Sum.inr (Sum.inl a0))))) :=
              (hXdisj (Sum.inr (Sum.inr (Sum.inr (Sum.inl a0)))) κ hκC).resolve_left ha0
            have hf : WilkiesDesign.graphOf (Work.WilkG4c.flatFam (Tm a0)) ∈
                S.Ω At (MvPolynomial.eval ![Dc, r] dtup) (p + 1 + 1) := by
              rw [← Work.WilkG4c.famGraph_eq_graphOf_flatFam]
              exact hTmΩ a0
            refine Set.eq_empty_of_subset_empty ?_
            calc interior κ ⊆ interior {w : Fin (p + 1) → ℝ |
                  ¬ ContDiffAt ℝ 1 (Work.WilkG4c.flatFam (Tm a0)) w} :=
                  interior_mono (fun w hw => Set.disjoint_left.mp hdisj hw)
              _ = ∅ := Work.WilkG4c.interior_compl_contDiffAt S hcd (k := 1)
                  (Work.WilkG4c.flatFam (Tm a0)) hf
      obtain ⟨Φb, hbcard, hbok, hbcov⟩ := hBCC Dc r k ε hε hε1 hr Λ Fc hΩFc hPYc hvalΛ
        C hCdec κ hκC (hCΩ κ hκC) hB1 hκint
      refine ⟨Φb, ?_, ?_, ?_⟩
      · have h3 := Work.WilkG4c.le_mergePoly_right (Φb.card : ℝ)
          (MvPolynomial.eval ![(Dc : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cGg)
          (MvPolynomial.eval ![(Dc : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c_bc) hbcard
        simpa only [hcMerge, MvPolynomial.eval_add, MvPolynomial.eval_mul, map_one] using h3
      · refine Work.WilkG4c.ChartsOK_mono hbok ?_ ?_
        · rw [haFin]; omega
        · rw [hbFin]
          simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C,
            map_ofNat]
          have hb : MvPolynomial.eval ![Dc, r] b_bc ≤ MvPolynomial.eval ![Dc, r] b_bc' := by
            rw [hb_bc' Dc r]
            refine Work.WilkG4c.eval_mono b_bc (fun i => ?_)
            fin_cases i
            · simpa using hdFam Dc r
            · simp
          omega
      · intro l hl x' hx' hmem _
        exact hbcov l hl x' hx' hmem
  · -- ## the cell is disjoint from the slab: vacuous
    have hB1d : Disjoint κ (Work.WilG4c.inCubeSet p 1) :=
      (hXdisj (Sum.inl 0) κ hκC).resolve_left hB1
    refine ⟨∅, ?_, ?_, ?_⟩
    · have hnn : (0 : ℝ) ≤
          MvPolynomial.eval ![(Dc : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cMerge := by
        rw [hcMerge]
        simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C, map_one]
        nlinarith [sq_nonneg (MvPolynomial.eval ![(Dc : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cGg
              + 1 / 2),
          sq_nonneg (MvPolynomial.eval ![(Dc : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c_bc
              + 1 / 2)]
      simpa using hnn
    · exact fun φ hφ => (Finset.notMem_empty φ hφ).elim
    · intro l hl x' hx' hmem
      exact (Set.disjoint_left.mp hB1d hmem
        ((Work.WilkG4c.mem_inCubeSet_one').mpr
          (by simpa only [Work.WilkG4c.I, Set.mem_Ioo, Fin.snoc_last] using (hx' 0)))).elim

end Work.WilG4c
