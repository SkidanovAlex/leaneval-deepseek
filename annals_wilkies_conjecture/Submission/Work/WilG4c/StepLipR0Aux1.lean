/-
  WilG4c / StepLipR0 — the `r = 0` case of the §5.3 reduction of BNZ.
-/
import Mathlib
import Submission.Work.WilG4c.StepCleanDefs
import Submission.Work.WilG4c.StepCellParam
import Submission.Work.WilG4c.FLemAPI
import Submission.Work.WilG4c.Hyps
import Submission.Work.WilG4c.StepCellGraph
import Submission.Work.WilG4c.YbddAux
import Submission.Work.WilG4c.StepBadLoc
import Submission.Work.WilG4c.ClampDefs
import Submission.Work.WilG4c.clampFamGraph
import Submission.Work.WilG4a.ite_graph_mem
import Submission.Work.WilG1.Basic
import Submission.Work.WilG1.Calc.pos_mem
import Submission.Work.WilG0.Main
import Submission.Work.WilG5.Basic

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG
open Work.WilkG4c
open Work.WilG1

/-! ## 0. Elementary bookkeeping -/

/-- `YBound F 0` bounds the family on the open cube: the order-`0` iterated derivative of a
function of `0` variables is the value itself. -/
theorem abs_le_one_of_YBound_zero {k p n : ℕ} {F : Family k p (n + 1)}
    (h : YBound F 0) {i : Fin k} {l : Fin p → ℝ} {z : Fin (n + 1) → ℝ}
    (hz : z ∈ openCube (n + 1)) : |F i l z| ≤ 1 := by
  have hx : z 0 ∈ I := hz 0
  have hy : Fin.tail z ∈ openCube n := fun j => hz j.succ
  have h0 := h i l (z 0) hx 0 le_rfl (Fin.tail z) hy
  rw [norm_iteratedFDeriv_zero, slice_apply] at h0
  have hz' : pt (z 0) (Fin.tail z) = z := pt_eta z
  rw [hz'] at h0
  simpa using h0

/-- A coordinate half-space `{x | 0 < x i}` is `Ω`-bounded. -/
theorem halfspace_pos_mem (S : SOMin) (m : ℕ) (i : Fin m) :
    {x : Fin m → ℝ | 0 < x i} ∈ S.Ω (m + 2) 3 m := by
  have h := Work.WilG1.Calc.pos_mem (S := S) 0 (MvPolynomial.X i : MvPolynomial (Fin m) ℝ)
  have hset : {x : Fin m → ℝ |
      0 < MvPolynomial.eval x (MvPolynomial.X i : MvPolynomial (Fin m) ℝ)}
      = {x : Fin m → ℝ | 0 < x i} := by
    ext x; simp
  rw [← hset]
  refine Work.WilG1.Omega.mono h le_rfl ?_
  norm_num [Polynomial.eval_C, MvPolynomial.totalDegree_X]

/-- A coordinate half-space `{x | x i < 1}` is `Ω`-bounded. -/
theorem halfspace_lt_one_mem (S : SOMin) (m : ℕ) (i : Fin m) :
    {x : Fin m → ℝ | x i < 1} ∈ S.Ω (m + 2) 3 m := by
  have h := Work.WilG1.Calc.pos_mem (S := S) 0
    ((1 : MvPolynomial (Fin m) ℝ) - MvPolynomial.X i)
  have hset : {x : Fin m → ℝ |
      0 < MvPolynomial.eval x ((1 : MvPolynomial (Fin m) ℝ) - MvPolynomial.X i)}
      = {x : Fin m → ℝ | x i < 1} := by
    ext x; simp [MvPolynomial.eval_sub]
  rw [← hset]
  refine Work.WilG1.Omega.mono h le_rfl ?_
  rw [Polynomial.eval_C]
  have htd : ((1 : MvPolynomial (Fin m) ℝ) - MvPolynomial.X i).totalDegree ≤ 1 := by
    refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
    rw [MvPolynomial.totalDegree_one, MvPolynomial.totalDegree_X]
    omega
  omega

/-- The set of points whose fibre coordinates all lie in `(0,1)` is `Ω`-bounded, with a
format and a degree independent of the degree parameter `D`. -/
theorem inCubeSet_mem (S : SOMin) (p N : ℕ) :
    inCubeSet p N ∈ S.Ω (p + N + 4) (6 * N) (p + N) := by
  set B : Fin N → Set (Fin (p + N) → ℝ) := fun j =>
    {x : Fin (p + N) → ℝ | 0 < x (Fin.natAdd p j)} ∩
      {x : Fin (p + N) → ℝ | x (Fin.natAdd p j) < 1} with hB
  have hB2 : ∀ j, B j ∈ S.Ω (p + N + 3) 6 (p + N) := by
    intro j
    rw [hB]
    have h1 := halfspace_pos_mem S (p + N) (Fin.natAdd p j)
    have h2 := halfspace_lt_one_mem S (p + N) (Fin.natAdd p j)
    have h3 := Work.WilG0.Omega_inter2 h1 h2
    exact h3
  have hinter := S.inter (D := fun _ : Fin N => 6) (A := B) hB2
  have hsum : (∑ _ : Fin N, 6) = 6 * N := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  rw [hsum] at hinter
  have hset : (⋂ j, B j) = inCubeSet p N := by
    ext z
    rw [Set.mem_iInter, mem_inCubeSet_iff]
    constructor
    · intro h j
      have hj := h j
      rw [hB] at hj
      exact hj
    · intro h j
      rw [hB]
      exact h j
  rw [hset] at hinter
  exact hinter

/-! ## 1. The per-cell chart in the continuous case

For a cell `κ` whose members' definitions are continuous on it (i.e. `κ` is contained in the
interior of the `C^0`-locus of every member), the nested-interpolation parametrisation `Ψ` of
`StepCellGraph`/`CellTowerCont` (a surjection onto each fibre, continuous on the cube, with
`Ω`-bounded coordinate graphs) is turned into a legitimate chart of the F-lemma at `r = 0` by

* replacing its value off the cell's parameter set `Λκ` by the harmless constant
  `(1/2,…,1/2)` (this keeps the image inside the cube and makes the composite constant in `t`
  there), and
* hitting the target point *exactly*: the surjectivity of `Ψ` means that the value of every
  member at the target is reproduced with error `0 < ε`. -/

/-- The `j`-th coordinate of the chart attached to a cell: the parametrisation on the cell's
parameter set, the constant `1/2` outside. -/
def cellChartFun {p N : ℕ} (Λκ : Set (Fin p → ℝ))
    (Ψ : (Fin p → ℝ) → (Fin N → ℝ) → (Fin N → ℝ)) :
    (Fin p → ℝ) → (Fin N → ℝ) → (Fin N → ℝ) :=
  fun l t => if l ∈ Λκ then Ψ l t else fun _ => (1 / 2 : ℝ)

@[simp] theorem cellChartFun_of_mem {p N : ℕ} {Λκ : Set (Fin p → ℝ)}
    {Ψ : (Fin p → ℝ) → (Fin N → ℝ) → (Fin N → ℝ)} {l : Fin p → ℝ} (h : l ∈ Λκ)
    (t : Fin N → ℝ) : cellChartFun Λκ Ψ l t = Ψ l t := by
  simp [cellChartFun, h]

@[simp] theorem cellChartFun_of_not_mem {p N : ℕ} {Λκ : Set (Fin p → ℝ)}
    {Ψ : (Fin p → ℝ) → (Fin N → ℝ) → (Fin N → ℝ)} {l : Fin p → ℝ} (h : l ∉ Λκ)
    (t : Fin N → ℝ) : cellChartFun Λκ Ψ l t = fun _ => (1 / 2 : ℝ) := by
  simp [cellChartFun, h]

/-- The constant `(1/2,…,1/2)` lies in the open cube. -/
theorem const_half_mem_openCube (N : ℕ) : (fun _ : Fin N => (1 / 2 : ℝ)) ∈ openCube N := by
  intro i
  exact ⟨by norm_num, by norm_num⟩

/-- A point of the fibre of a cell inside `inCubeSet` lies in the cube. -/
theorem mem_openCube_of_mem_inCubeSet {p N : ℕ} {κ : Set (Fin (p + N) → ℝ)}
    (hsub : κ ⊆ inCubeSet p N) {l : Fin p → ℝ} {y : Fin N → ℝ} (hy : Fin.append l y ∈ κ) :
    y ∈ openCube N := by
  have h := hsub hy
  simpa [mem_inCubeSet_iff, openCube, Fin.append_right] using h

/-- The case split of two `Ω`-graphs, with the format `F + 4` and the degree `4 * D`
exhibited (a variant of `Work.WilG4a.ite_graph_mem`, whose increments are existential). -/
theorem ite_graph_mem4 (S : SOMin) (m F D : ℕ) {P : Set (Fin m → ℝ)} {f g : (Fin m → ℝ) → ℝ}
    (hP : P ∈ S.Ω F D m) (hf : graphOf f ∈ S.Ω F D (m + 1)) (hg : graphOf g ∈ S.Ω F D (m + 1)) :
    graphOf (Work.WilG4a.iteFun P f g) ∈ S.Ω (F + 4) (4 * D) (m + 1) := by
  have hproj : {z : Fin (m + 1) → ℝ | Fin.init z ∈ P} ∈ S.Ω (F + 1) D (m + 1) :=
    S.prod_right hP
  have hprojC : ({z : Fin (m + 1) → ℝ | Fin.init z ∈ P})ᶜ ∈ S.Ω (F + 2) D (m + 1) :=
    Work.WilG5.mem_mono (S.compl hproj) (F + 2) D (by omega) (le_refl D)
  have hf1 : graphOf f ∈ S.Ω (F + 1) D (m + 1) :=
    Work.WilG5.mem_mono hf (F + 1) D (by omega) (le_refl D)
  have hg2 : graphOf g ∈ S.Ω (F + 2) D (m + 1) :=
    Work.WilG5.mem_mono hg (F + 2) D (by omega) (le_refl D)
  have hA : graphOf f ∩ {z : Fin (m + 1) → ℝ | Fin.init z ∈ P} ∈
      S.Ω (F + 4) (D + D) (m + 1) :=
    Work.WilG5.mem_mono (Work.WilG4a.inter_mem_ite hf1 hproj) (F + 4) (D + D) (by omega) (le_refl _)
  have hB : graphOf g ∩ ({z : Fin (m + 1) → ℝ | Fin.init z ∈ P})ᶜ ∈
      S.Ω (F + 4) (D + D) (m + 1) :=
    Work.WilG5.mem_mono (Work.WilG4a.inter_mem_ite hg2 hprojC) (F + 4) (D + D) (by omega) (le_refl _)
  have hU : (graphOf f ∩ {z : Fin (m + 1) → ℝ | Fin.init z ∈ P}) ∪
      (graphOf g ∩ ({z : Fin (m + 1) → ℝ | Fin.init z ∈ P})ᶜ) ∈
      S.Ω (F + 4) ((D + D) + (D + D)) (m + 1) := Work.WilG4a.union_mem hA hB
  rw [← Work.WilG4a.graphOf_iteFun_eq] at hU
  have hdeg : (D + D) + (D + D) = 4 * D := by omega
  rw [← hdeg]
  exact hU

/-- **The per-cell chart, continuous case.** -/
theorem cell_chart_clean (S : SOMin) {p N k : ℕ}
    (F : Family k p N) (Λ : Set (Fin p → ℝ)) (κ : Set (Fin (p + N) → ℝ))
    (Λκ : Set (Fin p → ℝ)) (hΛκ : Λκ = {l | ∃ y : Fin N → ℝ, Fin.append l y ∈ κ})
    (aΛ dΛ : ℕ) (hΛmem : Λκ ∈ S.Ω aΛ dΛ p)
    (aT : ℕ) (bT : MvPolynomial (Fin 2) ℕ) {D : ℕ}
    (Ψ : (Fin p → ℝ) → (Fin N → ℝ) → (Fin N → ℝ))
    (hΨg : ∀ j, famGraph (fun l t => Ψ l t j) ∈
      S.Ω aT (MvPolynomial.eval ![D, 1] bT) (p + N + 1))
    (hΨc : ∀ l ∈ Λκ, ∀ t ∈ openCube N, Ψ l t ∈ openCube N)
    (hΨκ : ∀ l ∈ Λκ, ∀ t ∈ openCube N, Fin.append l (Ψ l t) ∈ κ)
    (hΨs : ∀ l ∈ Λκ, ∀ y, Fin.append l y ∈ κ → ∃ t ∈ openCube N, Ψ l t = y)
    (hΨcont : ∀ l ∈ Λκ, ContinuousOn (fun t => Ψ l t) (openCube N))
    (hsub : κ ⊆ inCubeSet p N)
    (hclean : ∀ i, κ ⊆ cLoc (F i) 0)
    (hval : ∀ (i : Fin k) (l : Fin p → ℝ), l ∈ Λ → ∀ z ∈ openCube N, F i l z ∈ Set.Ioo (0 : ℝ) 1)
    (hone : ∀ i l, ∀ z ∈ openCube N, |F i l z| ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ Φ : Finset (ChartTuple p N),
      ChartsOK S (max (max (aT + 4) (p + N + 4))
              (max (aΛ + (p + N) + (p + N) + 1 + p + 4) 5))
          (MvPolynomial.eval ![D, 0]
            (MvPolynomial.C 4 * (MvPolynomial.eval₂ MvPolynomial.C
              (fun i : Fin 2 => if i = 0 then MvPolynomial.X 0 else 1) bT
              + MvPolynomial.C (dΛ + 2 + 3)))) 0 Λ F Φ ∧
      (∀ l ∈ Λ, ∀ x : Fin N → ℝ, x ∈ openCube N → Fin.append l x ∈ κ →
        ∃ φ ∈ Φ, ∃ t ∈ openCube N, ∀ i, |F i l (fun j => φ j l t) - F i l x| < ε) := by
  classical
  refine ⟨{fun j l t => cellChartFun Λκ Ψ l t j}, ?_, ?_⟩
  · intro φ hφ
    rw [Finset.mem_singleton] at hφ
    subst hφ
    constructor
    · intro j
      set P : Set (Fin (p + N) → ℝ) := {z | (fun i : Fin p => z (Fin.castAdd N i)) ∈ Λκ} with hP
      have hPmem : P ∈ S.Ω (max (aΛ + (p + N)) ((p + N) + p) + 1 + p) (dΛ + 2) (p + N) := by
        have h := Work.WilG4c.Subst (S := S) (σ := fun i : Fin p => Fin.castAdd N i) hΛmem
        rw [hP]
        simpa [Function.comp_def] using h
      have hconst : graphOf (fun _ : Fin (p + N) → ℝ => (1 / 2 : ℝ)) ∈
          S.Ω (p + N + 1) 1 (p + N + 1) := by
        have h := S.hyp (p + N + 1)
          ((MvPolynomial.X (Fin.last (p + N)) : MvPolynomial (Fin (p + N + 1)) ℝ)
            - MvPolynomial.C (1 / 2))
        have hset : {z : Fin (p + N + 1) → ℝ |
            MvPolynomial.eval z ((MvPolynomial.X (Fin.last (p + N)) :
              MvPolynomial (Fin (p + N + 1)) ℝ) - MvPolynomial.C (1 / 2)) = 0}
            = graphOf (fun _ : Fin (p + N) → ℝ => (1 / 2 : ℝ)) := by
          ext z
          simp only [Set.mem_setOf_eq, MvPolynomial.eval_sub, MvPolynomial.eval_X,
            MvPolynomial.eval_C, graphOf, sub_eq_zero]
        rw [hset] at h
        refine Work.WilG1.Omega.mono h le_rfl ?_
        have htd : ((MvPolynomial.X (Fin.last (p + N)) :
            MvPolynomial (Fin (p + N + 1)) ℝ) - MvPolynomial.C (1 / 2)).totalDegree ≤ 1 := by
          refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
          rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C]
          omega
        omega
      have htower : graphOf (flatFun (fun l t => Ψ l t j)) ∈
          S.Ω aT (MvPolynomial.eval ![D, 1] bT) (p + N + 1) := by
        have h := hΨg j
        rwa [famGraph_eq_graphOf_flatFun] at h
      set Fc : ℕ := max (max aT (p + N)) (max (max (aΛ + (p + N)) ((p + N) + p) + 1 + p) 1)
        with hFc
      set Dc : ℕ := max (max (MvPolynomial.eval ![D, 1] bT) 1) (dΛ + 2) with hDc
      have hPmem' : P ∈ S.Ω Fc Dc (p + N) :=
        Work.WilG1.Omega.mono hPmem (by rw [hFc]; omega) (by rw [hDc]; omega)
      have hconst' : graphOf (fun _ : Fin (p + N) → ℝ => (1 / 2 : ℝ)) ∈
          S.Ω Fc Dc (p + N + 1) :=
        Work.WilG1.Omega.mono hconst (by rw [hFc]; omega) (by rw [hDc]; omega)
      have htower' : graphOf (flatFun (fun l t => Ψ l t j)) ∈ S.Ω Fc Dc (p + N + 1) :=
        Work.WilG1.Omega.mono htower (by rw [hFc]; omega) (by rw [hDc]; omega)
      have hmain := ite_graph_mem4 S (p + N) Fc Dc hPmem' htower' hconst'
      have hset : graphOf (Work.WilG4a.iteFun P (flatFun (fun l t => Ψ l t j))
          (fun _ : Fin (p + N) → ℝ => (1 / 2 : ℝ))) =
          famGraph (fun l t => (fun j l t => cellChartFun Λκ Ψ l t j) j l t) := by
        rw [famGraph_eq_graphOf_flatFun]
        congr 1
        funext z
        simp only [Work.WilG4a.iteFun, flatFun, cellChartFun, hP]
        by_cases h : (fun i : Fin p => z (Fin.castAdd N i)) ∈ Λκ <;> simp [h]
      rw [hset] at hmain
      refine Work.WilG1.Omega.mono hmain ?_ ?_
      · rw [hFc]
        omega
      · have hsub : MvPolynomial.eval ![D, 0] (MvPolynomial.eval₂ MvPolynomial.C
            (fun i : Fin 2 => if i = 0 then MvPolynomial.X 0 else 1) bT)
            = MvPolynomial.eval ![D, 1] bT := by
          rw [Work.WilkG4c.eval_eval₂_C_nat]
          have hfun : (fun s : Fin 2 => MvPolynomial.eval ![D, 0]
              (if s = 0 then MvPolynomial.X 0 else 1)) = ![D, 1] := by
            funext i
            fin_cases i <;> simp
          rw [hfun]
        rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_add,
          MvPolynomial.eval_C, hsub, hDc]
        omega
    · intro l hl
      constructor
      · intro t ht
        change cellChartFun Λκ Ψ l t ∈ openCube N
        by_cases h : l ∈ Λκ
        · rw [cellChartFun_of_mem h t]
          exact hΨc l h t ht
        · rw [cellChartFun_of_not_mem h t]
          exact const_half_mem_openCube N
      · intro i
        constructor
        · by_cases h : l ∈ Λκ
          · have hslice : ContinuousOn (fun z : Fin N → ℝ => F i l z)
                {z : Fin N → ℝ | Fin.append l z ∈ κ} := by
              intro z hz
              have hz' : Fin.append l z ∈ cLoc (F i) 0 := hclean i hz
              have hc : ContinuousAt (famFun (F i)) (Fin.append l z) := by
                obtain ⟨u, hu, hcont⟩ := contDiffAt_zero.mp (interior_subset hz')
                obtain ⟨w, hwu, hwopen, hxw⟩ := mem_nhds_iff.mp hu
                exact (hcont.mono hwu).continuousAt (hwopen.mem_nhds hxw)
              have hcomp : ContinuousAt (fun z' : Fin N → ℝ => famFun (F i) (Fin.append l z')) z :=
                hc.comp (by fun_prop)
              refine (hcomp.congr ?_).continuousWithinAt
              filter_upwards with z'
              simp [famFun, Fin.append_left, Fin.append_right]
            have hcomp := hslice.comp (hΨcont l h) (fun t ht => hΨκ l h t ht)
            refine contDiffOn_zero.mpr (hcomp.congr (fun t ht => ?_))
            change F i l (fun j => cellChartFun Λκ Ψ l t j) = F i l (Ψ l t)
            congr 1
            exact cellChartFun_of_mem h t
          · have hconst : ContinuousOn (fun t : Fin N → ℝ =>
                F i l (fun j => cellChartFun Λκ Ψ l t j)) (openCube N) := by
              refine (continuousOn_const (c := F i l (fun _ => (1 / 2 : ℝ)))).congr
                (fun t ht => ?_)
              change F i l (fun j => cellChartFun Λκ Ψ l t j) = F i l (fun _ => (1 / 2 : ℝ))
              congr 1
              exact cellChartFun_of_not_mem h t
            exact contDiffOn_zero.mpr hconst
        · intro m hm t ht
          have hm0 : m = 0 := by omega
          subst hm0
          rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
          apply hone i l
          change cellChartFun Λκ Ψ l t ∈ openCube N
          by_cases h : l ∈ Λκ
          · rw [cellChartFun_of_mem h t]
            exact hΨc l h t ht
          · rw [cellChartFun_of_not_mem h t]
            exact const_half_mem_openCube N
  · intro l hl x hx hmem
    have hlx : l ∈ Λκ := by
      rw [hΛκ]
      exact ⟨x, hmem⟩
    obtain ⟨t, ht, htx⟩ := hΨs l hlx x hmem
    refine ⟨fun j l t => cellChartFun Λκ Ψ l t j, Finset.mem_singleton_self _, t, ht, ?_⟩
    intro i
    have hval' : (fun j => cellChartFun Λκ Ψ l t j) = x := by
      rw [cellChartFun_of_mem hlx t]
      exact htx
    rw [hval']
    simpa using hε

end Work.WilG4c
