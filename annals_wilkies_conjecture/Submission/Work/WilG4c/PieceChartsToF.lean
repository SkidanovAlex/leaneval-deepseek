/-
  WilG4c / PieceChartsToF — transporting the per-cell charts of the piece family back to `F`.

  The §5.3 reduction (`StepLip`) proceeds by pulling the family back in the `y`-direction
  (`Work.WilkG4c.yPullback`, via the induction hypothesis `ih`), cutting the resulting family
  by the exact-cover charts of the `(λ,s)`-cells (`Work.WilkG4c.pieceFam`) and then producing,
  for each piece, a finite family of charts of the `(n+1)`-cube.

  This file performs the *last* step of that transport: given a finite family `Ψ` of charts of
  the piece family
  `G := pieceFam (yPullback F ψ) (fun l τ => φ 0 l (fun _ => τ))`
  satisfying the per-chart conditions `ChartsOK` on a parameter set `P`, it produces a finite
  family `Φ` of charts of `F` itself, of the same cardinality at most, still satisfying
  `ChartsOK` (at a larger format and degree, as always), together with the selection map
  `sel : Ψ → Φ` which *realises the piece family's chart point*:

      `sel ψ' l t = pullbackMap ψ l (Fin.cons (φ 0 l (fun _ => ψ' 0 l t))
                                  (Fin.tail (fun j => ψ' j l t)))`

  so that the composite of `F` with `sel ψ'` is *literally* the composite of `G` with `ψ'`
  (`selPieceChart_apply` below).  Hence the analytic part of `ChartsOK` (`ContDiffOn` and the
  unit jet bounds) transfers verbatim, while the cube-membership and the `Ω`-bounds of the
  chart coordinates are proved here.

  The chart `sel ψ'` is `selPieceChart ψ φ ψ'`, whose coordinates are

  * `selPieceChart ψ φ χ 0 = fun l t => φ 0 l (fun _ => χ 0 l t)`, and
  * `selPieceChart ψ φ χ k.succ = fun l t => ψ k (Fin.snoc l (φ 0 l (fun _ => χ 0 l t)))
                                              (Fin.tail (fun i => χ i l t))`,

  i.e. the `x`-coordinate is the `1`-dimensional chart `φ 0` evaluated at `χ 0 l t`, and the
  remaining coordinates are the cylindrical chart `ψ` at the parameter `Fin.snoc l (φ 0 l …)`
  and the `y`-point `Fin.tail (χ l t)`.  Their `Ω`-bounds are the two composition lemmas
  `selPieceChart_zero_mem` and `selPieceChart_succ_mem` (`graphOfCompGen`, rectangular case).
-/
import Mathlib
import Submission.Work.WilG4c.StepLipPieces
import Submission.Work.WilG4c.YPullback
import Submission.Work.WilG4c.FLemAPI
import Submission.Work.WilG4c.YbddAux
import Submission.Work.WilG4c.graphOfCompGen

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG
open Work.WilkG4c

/-! ## 1. The combined chart -/

/-- The chart of the `(n+1)`-cube attached to a chart `χ` of the piece family: the
`1`-dimensional chart `φ 0` is applied to the distinguished coordinate and the cylindrical
chart `ψ` is applied to the remaining coordinates at the parameter `Fin.snoc l (φ 0 l (χ 0 l t))`. -/
def selPieceChart {p n : ℕ} (ψ : ChartTuple (p + 1) n) (φ : ChartTuple p 1) :
    ChartTuple p (n + 1) → ChartTuple p (n + 1) :=
  fun χ j => Fin.cases (fun l t => φ 0 l (fun _ => χ 0 l t))
    (fun k l t => ψ k (Fin.snoc l (φ 0 l (fun _ => χ 0 l t))) (Fin.tail (fun i => χ i l t))) j

theorem selPieceChart_zero {p n : ℕ} (ψ : ChartTuple (p + 1) n) (φ : ChartTuple p 1)
    (χ : ChartTuple p (n + 1)) :
    selPieceChart ψ φ χ 0 = fun l t => φ 0 l (fun _ => χ 0 l t) := rfl

theorem selPieceChart_succ {p n : ℕ} (ψ : ChartTuple (p + 1) n) (φ : ChartTuple p 1)
    (χ : ChartTuple p (n + 1)) (k : Fin n) :
    selPieceChart ψ φ χ k.succ
      = fun l t => ψ k (Fin.snoc l (φ 0 l (fun _ => χ 0 l t)))
          (Fin.tail (fun i => χ i l t)) := rfl

/-- The point of the combined chart is the image of the chart point of `χ` under
`pullbackMap ψ l`. -/
theorem selPieceChart_toPt {p n : ℕ} (ψ : ChartTuple (p + 1) n) (φ : ChartTuple p 1)
    (χ : ChartTuple p (n + 1)) (l : Fin p → ℝ) (t : Fin (n + 1) → ℝ) :
    (fun j => selPieceChart ψ φ χ j l t)
      = pullbackMap ψ l (Fin.cons (φ 0 l (fun _ => χ 0 l t))
          (Fin.tail (fun i => χ i l t))) := by
  funext j
  induction j using Fin.cases with
  | zero => rfl
  | succ k =>
      simp only [selPieceChart, Fin.cases_succ, pullbackMap, Fin.cons_zero, Fin.tail_cons,
        Fin.cons_succ]

/-- **The key identity.**  Composing `F` with the combined chart of `χ` is composing the piece
family `pieceFam (yPullback F ψ) (fun l τ => φ 0 l (fun _ => τ))` with `χ`. -/
theorem selPieceChart_apply {k p n : ℕ} (F : Family k p (n + 1))
    (ψ : ChartTuple (p + 1) n) (φ : ChartTuple p 1) (χ : ChartTuple p (n + 1))
    (i : Fin k) (l : Fin p → ℝ) (t : Fin (n + 1) → ℝ) :
    F i l (fun j => selPieceChart ψ φ χ j l t)
      = pieceFam (yPullback F ψ) (fun l τ => φ 0 l (fun _ => τ)) i l (fun j => χ j l t) := by
  rw [selPieceChart_toPt]
  rfl

/-! ## 2. The combined chart maps the cube into itself -/

/-- A variant of `pullbackMap_mem_openCube` in which the chart is only assumed to send the cube
into itself at the *interior* values `τ ∈ I = (0,1)` (which is all the reductions have). -/
theorem pullbackMap_mem_openCube_I {p n : ℕ} (ψ : ChartTuple (p + 1) n) {l : Fin p → ℝ}
    (hψ : ∀ τ ∈ I, ∀ u ∈ openCube n, (fun j => ψ j (Fin.snoc l τ) u) ∈ openCube n)
    {v : Fin (n + 1) → ℝ} (hv0 : v 0 ∈ I) (hvt : Fin.tail v ∈ openCube n) :
    pullbackMap ψ l v ∈ openCube (n + 1) := by
  intro j
  induction j using Fin.cases with
  | zero => rw [pullbackMap, Fin.cons_zero]; exact hv0
  | succ k => rw [pullbackMap, Fin.cons_succ]; exact hψ (v 0) hv0 (Fin.tail v) hvt k

/-- The combined chart sends the open cube into itself, provided `φ 0` maps `(0,1)` into `I`,
`ψ` maps the cube into itself at every parameter `Fin.snoc l τ` with `τ ∈ I`, and `χ` sends
the cube into itself. -/
theorem selPieceChart_mem_openCube {p n : ℕ} (ψ : ChartTuple (p + 1) n) (φ : ChartTuple p 1)
    (χ : ChartTuple p (n + 1)) {l : Fin p → ℝ}
    (hφI : ∀ t ∈ openCube 1, φ 0 l t ∈ I)
    (hψcube : ∀ τ ∈ I, ∀ u ∈ openCube n, (fun j => ψ j (Fin.snoc l τ) u) ∈ openCube n)
    (hχ : ∀ t ∈ openCube (n + 1), (fun j => χ j l t) ∈ openCube (n + 1)) :
    ∀ t ∈ openCube (n + 1), (fun j => selPieceChart ψ φ χ j l t) ∈ openCube (n + 1) := by
  intro t ht
  have hχt := hχ t ht
  rw [selPieceChart_toPt]
  refine pullbackMap_mem_openCube_I ψ hψcube ?_ (fun k => hχt k.succ)
  exact hφI (fun _ => χ 0 l t) (fun i => by fin_cases i; exact hχt 0)

/-! ## 3. The `Ω`-bounds of the coordinates of the combined chart -/

/-- **The `Ω`-bound of the first coordinate** of the combined chart: the graph of
`(l,t) ↦ φ 0 l (fun _ => χ l t)` over `p + (n+1)` variables is `Ω`-bounded, obtained from the
rectangular composition `graphOfCompGen` applied to `flatFun (φ 0)` and the coordinate map
`(l,t) ↦ Fin.snoc l (χ l t)`. -/
theorem selPieceChart_zero_mem (S : SOMin) (p n : ℕ) :
    ∃ A C : ℕ, ∀ (aφ Dgφ a Dg : ℕ) (φ : ChartTuple p 1)
      (χ : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ),
      famGraph (φ 0) ∈ S.Ω aφ Dgφ (p + 1 + 1) →
      famGraph χ ∈ S.Ω a Dg (p + (n + 1) + 1) →
      famGraph (fun l t => φ 0 l (fun _ => χ l t)) ∈
        S.Ω (aφ + a + A) (Dgφ + (p + 1) * Dg + C) (p + (n + 1) + 1) := by
  obtain ⟨C₁, C₂, hcomp⟩ := Work.WilG4c.graphOfCompGen S (p + 1) (p + (n + 1))
  refine ⟨(p + (n + 1) + 1) + C₁, (p + 1) + C₂, ?_⟩
  intro aφ Dgφ a Dg φ χ hφ hχ
  let Φ : (Fin (p + (n + 1)) → ℝ) → (Fin (p + 1) → ℝ) :=
    fun x => Fin.snoc (fun i : Fin p => x (Fin.castAdd (n + 1) i))
      (χ (fun i : Fin p => x (Fin.castAdd (n + 1) i))
        (fun j : Fin (n + 1) => x (Fin.natAdd p j)))
  have hcoord : ∀ i : Fin (p + 1),
      graphOf (fun x : Fin (p + (n + 1)) → ℝ => Φ x i) ∈
        S.Ω (max (p + (n + 1) + 1) a) (max 1 Dg) (p + (n + 1) + 1) := by
    intro i
    refine Fin.lastCases ?_ ?_ i
    · have heq : (fun x : Fin (p + (n + 1)) → ℝ => Φ x (Fin.last p))
          = flatFun χ := by
        funext x
        simp only [Φ, Fin.snoc_last, flatFun]
      rw [heq]
      exact Omega_mono_le S (le_max_right _ _) (le_max_right _ _) hχ
    · intro i'
      have heq : (fun x : Fin (p + (n + 1)) → ℝ => Φ x (Fin.castSucc i'))
          = (fun x : Fin (p + (n + 1)) → ℝ => x (Fin.castAdd (n + 1) i')) := by
        funext x
        simp only [Φ, Fin.snoc_castSucc]
      rw [heq]
      exact Omega_mono_le S (le_max_left _ _) (le_max_left _ _)
        (graphOf_coord_mem S (Fin.castAdd (n + 1) i'))
  have hmain := hcomp aφ (max (p + (n + 1) + 1) a) Dgφ (max 1 Dg) (flatFun (φ 0)) Φ hφ hcoord
  have hid : (flatFun (φ 0)) ∘ Φ = flatFun (fun l t => φ 0 l (fun _ => χ l t)) := by
    funext x
    simp only [Function.comp_apply, flatFun]
    have h1 : (fun i : Fin p => Φ x (Fin.castAdd 1 i))
        = (fun i : Fin p => x (Fin.castAdd (n + 1) i)) := by
      funext i
      simp only [Φ]
      rw [show (Fin.castAdd 1 i : Fin (p + 1)) = Fin.castSucc i from by
        apply Fin.ext; simp [Fin.castAdd], Fin.snoc_castSucc]
    have h2 : (fun j : Fin 1 => Φ x (Fin.natAdd p j))
        = (fun _ : Fin 1 => χ (fun i : Fin p => x (Fin.castAdd (n + 1) i))
            (fun j : Fin (n + 1) => x (Fin.natAdd p j))) := by
      funext j
      rw [Fin.eq_zero j]
      simp only [Φ]
      rw [show (Fin.natAdd p (0 : Fin 1) : Fin (p + 1)) = Fin.last p from by
        apply Fin.ext; simp [Fin.natAdd], Fin.snoc_last]
    rw [h1, h2]
  rw [hid] at hmain
  rw [famGraph_eq_graphOf_flatFun]
  refine Omega_mono_le S ?_ ?_ hmain
  · omega
  · have h2 : max 1 Dg ≤ Dg + 1 := by omega
    have h3 : (p + 1) * max 1 Dg ≤ (p + 1) * (Dg + 1) := Nat.mul_le_mul_left _ h2
    have h4 : (p + 1) * (Dg + 1) = (p + 1) * Dg + (p + 1) := by ring
    omega

/-- **The `Ω`-bound of the remaining coordinates** of the combined chart: the graph of
`(l,t) ↦ ψ k (Fin.snoc l (φ 0 l (fun _ => χ 0 l t))) (Fin.tail (fun i => χ i l t))` over
`p + (n+1)` variables, again by `graphOfCompGen` (applied to `flatFun (ψ k)` and the
coordinate map `x ↦ Fin.append (Fin.snoc l (φ 0 l …)) (Fin.tail (χ l …))`). -/
theorem selPieceChart_succ_mem (S : SOMin) (p n : ℕ) :
    ∃ A C : ℕ, ∀ (aψ Dgψ aφ Dgφ a Dg : ℕ) (ψ : ChartTuple (p + 1) n)
      (φ : ChartTuple p 1) (χ : ChartTuple p (n + 1)) (k : Fin n),
      (∀ i, famGraph (ψ i) ∈ S.Ω aψ Dgψ ((p + 1) + n + 1)) →
      famGraph (φ 0) ∈ S.Ω aφ Dgφ (p + 1 + 1) →
      (∀ i, famGraph (χ i) ∈ S.Ω a Dg (p + (n + 1) + 1)) →
      famGraph (fun l t => ψ k (Fin.snoc l (φ 0 l (fun _ => χ 0 l t)))
          (Fin.tail (fun i => χ i l t))) ∈
        S.Ω (aψ + (aφ + a + A)) (Dgψ + ((p + 1) + n) * (Dgφ + (p + 1) * Dg + C) + C)
          (p + (n + 1) + 1) := by
  obtain ⟨A₀, C₀, hz⟩ := selPieceChart_zero_mem S p n
  obtain ⟨C₁, C₂, hcomp⟩ := Work.WilG4c.graphOfCompGen S ((p + 1) + n) (p + (n + 1))
  refine ⟨A₀ + (p + (n + 1) + 1) + C₁, C₀ + C₂ + 1, ?_⟩
  intro aψ Dgψ aφ Dgφ a Dg ψ φ χ k hψ hφ hχ
  let lof : (Fin (p + (n + 1)) → ℝ) → (Fin p → ℝ) := fun x i => x (Fin.castAdd (n + 1) i)
  let tof : (Fin (p + (n + 1)) → ℝ) → (Fin (n + 1) → ℝ) := fun x j => x (Fin.natAdd p j)
  let Φ : (Fin (p + (n + 1)) → ℝ) → (Fin ((p + 1) + n) → ℝ) := fun x => Fin.append
      (Fin.snoc (lof x) (φ 0 (lof x) (fun _ => χ 0 (lof x) (tof x))))
      (fun i : Fin n => χ i.succ (lof x) (tof x))
  have hcoord : ∀ i : Fin ((p + 1) + n),
      graphOf (fun x : Fin (p + (n + 1)) → ℝ => Φ x i) ∈
        S.Ω (max (max (p + (n + 1) + 1) (aφ + a + A₀)) a)
          (max (max 1 (Dgφ + (p + 1) * Dg + C₀)) Dg) (p + (n + 1) + 1) := by
    intro i
    refine Fin.addCases (fun i' => ?_) (fun k' => ?_) i
    · refine Fin.lastCases ?_ ?_ i'
      · have heq : (fun x : Fin (p + (n + 1)) → ℝ => Φ x (Fin.castAdd n (Fin.last p)))
            = flatFun (fun l t => φ 0 l (fun _ => χ 0 l t)) := by
          funext x
          simp only [Φ, Fin.append_left, Fin.snoc_last, flatFun, lof, tof]
        rw [heq]
        exact Omega_mono_le S (le_trans (le_max_right _ _) (le_max_left _ _))
          (le_trans (le_max_right _ _) (le_max_left _ _))
          (by simpa only [famGraph_eq_graphOf_flatFun] using
            hz aφ Dgφ a Dg φ (fun l t => χ 0 l t) hφ (hχ 0))
      · intro i''
        have heq : (fun x : Fin (p + (n + 1)) → ℝ => Φ x (Fin.castAdd n (Fin.castSucc i'')))
            = (fun x : Fin (p + (n + 1)) → ℝ => x (Fin.castAdd (n + 1) i'')) := by
          funext x
          simp only [Φ, Fin.append_left, Fin.snoc_castSucc, lof]
        rw [heq]
        exact Omega_mono_le S (le_trans (le_max_left _ _) (le_max_left _ _))
          (le_trans (le_max_left _ _) (le_max_left _ _))
          (graphOf_coord_mem S (Fin.castAdd (n + 1) i''))
    · have heq : (fun x : Fin (p + (n + 1)) → ℝ => Φ x (Fin.natAdd (p + 1) k'))
          = flatFun (χ k'.succ) := by
        funext x
        simp only [Φ, Fin.append_right, flatFun, lof, tof]
      rw [heq]
      exact Omega_mono_le S (le_max_right _ _) (le_max_right _ _) (hχ k'.succ)
  have hmain := hcomp aψ (max (max (p + (n + 1) + 1) (aφ + a + A₀)) a)
      Dgψ (max (max 1 (Dgφ + (p + 1) * Dg + C₀)) Dg) (flatFun (ψ k)) Φ
      (by simpa only [famGraph_eq_graphOf_flatFun] using hψ k) hcoord
  have hid : (flatFun (ψ k)) ∘ Φ
      = flatFun (fun l t => ψ k (Fin.snoc l (φ 0 l (fun _ => χ 0 l t)))
          (Fin.tail (fun i => χ i l t))) := by
    funext x
    simp only [Function.comp_apply, flatFun, Φ, lof, tof, Fin.append_left, Fin.append_right]
    rfl
  rw [hid] at hmain
  rw [famGraph_eq_graphOf_flatFun]
  refine Omega_mono_le S ?_ ?_ hmain
  · have h2 : max (max (p + (n + 1) + 1) (aφ + a + A₀)) a
        ≤ aφ + a + (A₀ + (p + (n + 1) + 1) + C₁) := by omega
    omega
  · have h2 : max (max 1 (Dgφ + (p + 1) * Dg + C₀)) Dg
        ≤ Dgφ + (p + 1) * Dg + (C₀ + C₂ + 1) := by
      have h3 : Dg ≤ (p + 1) * Dg := by
        have := Nat.mul_le_mul_right Dg (show 1 ≤ p + 1 by omega)
        simpa using this
      omega
    have h4 : ((p + 1) + n) * max (max 1 (Dgφ + (p + 1) * Dg + C₀)) Dg
        ≤ ((p + 1) + n) * (Dgφ + (p + 1) * Dg + (C₀ + C₂ + 1)) :=
      Nat.mul_le_mul_left _ h2
    omega

/-! ## 4. The transport of the piece family's charts to `F` -/

theorem PieceChartsToF (S : WilkiesDesign.SOMin) (p n k r : ℕ)
    (F : Work.WilkG4c.Family k p (n + 1))
    (ψ : Work.WilkG4c.ChartTuple (p + 1) n) (φ : Work.WilkG4c.ChartTuple p 1)
    (P : Set (Fin p → ℝ)) (aψ Dgψ aφ Dgφ : ℕ)
    (hψg : ∀ j, WilkiesDesign.CG.famGraph (ψ j) ∈ S.Ω aψ Dgψ ((p + 1) + n + 1))
    (hφg : WilkiesDesign.CG.famGraph (φ 0) ∈ S.Ω aφ Dgφ (p + 1 + 1))
    (hφI : ∀ l ∈ P, ∀ t ∈ WilkiesDesign.openCube 1, φ 0 l t ∈ Work.WilkG4c.I)
    (hψcube : ∀ l ∈ P, ∀ τ ∈ Work.WilkG4c.I, ∀ u ∈ WilkiesDesign.openCube n,
      (fun j => ψ j (Fin.snoc l τ) u) ∈ WilkiesDesign.openCube n)
    (a Dg : ℕ) (Ψ : Finset (Work.WilkG4c.ChartTuple p (n + 1)))
    (hΨ : Work.WilkG4c.ChartsOK S a Dg r P
      (Work.WilkG4c.pieceFam (Work.WilkG4c.yPullback F ψ) (fun l τ => φ 0 l (fun _ => τ))) Ψ) :
    ∃ (Φ : Finset (Work.WilkG4c.ChartTuple p (n + 1))) (a' Dg' : ℕ)
      (sel : Work.WilkG4c.ChartTuple p (n + 1) → Work.WilkG4c.ChartTuple p (n + 1)),
      Φ.card ≤ Ψ.card ∧
      Work.WilkG4c.ChartsOK S a' Dg' r P F Φ ∧
      (∀ ψ' ∈ Ψ, sel ψ' ∈ Φ) ∧
      (∀ ψ' ∈ Ψ, ∀ l ∈ P, ∀ t ∈ WilkiesDesign.openCube (n + 1), ∀ i,
        F i l (fun j => sel ψ' j l t) =
          Work.WilkG4c.pieceFam (Work.WilkG4c.yPullback F ψ)
            (fun l τ => φ 0 l (fun _ => τ)) i l (fun j => ψ' j l t)) := by
  classical
  obtain ⟨A₀, C₀, hz⟩ := selPieceChart_zero_mem S p n
  obtain ⟨A₁, C₁, hs⟩ := selPieceChart_succ_mem S p n
  refine ⟨Ψ.image (selPieceChart ψ φ),
    (aφ + a + A₀) + (aψ + (aφ + a + A₁)),
    (Dgφ + (p + 1) * Dg + C₀) + (Dgψ + ((p + 1) + n) * (Dgφ + (p + 1) * Dg + C₁) + C₁),
    selPieceChart ψ φ, Finset.card_image_le, ?_, ?_, ?_⟩
  · -- the per-chart conditions for `F`
    intro φ' hφ'
    obtain ⟨ψ', hψ'Ψ, rfl⟩ := Finset.mem_image.mp hφ'
    obtain ⟨hψ'g, hψ'cube⟩ := hΨ ψ' hψ'Ψ
    refine ⟨?_, fun l hl => ⟨?_, ?_⟩⟩
    · -- the `Ω`-bounds of the coordinates of the combined chart
      intro j
      refine Fin.cases ?_ ?_ j
      · rw [selPieceChart_zero]
        refine Omega_mono_le S ?_ ?_ (hz aφ Dgφ a Dg φ (fun l t => ψ' 0 l t) hφg (hψ'g 0))
        · omega
        · omega
      · intro k
        rw [selPieceChart_succ]
        refine Omega_mono_le S ?_ ?_ (hs aψ Dgψ aφ Dgφ a Dg ψ φ ψ' k hψg hφg hψ'g)
        · omega
        · omega
    · -- the combined chart maps the cube into itself
      intro t ht
      exact selPieceChart_mem_openCube ψ φ ψ' (hφI l hl) (hψcube l hl) (hψ'cube l hl).1 t ht
    · -- the composite with `F` is the composite of the piece family with `ψ'`
      intro i
      obtain ⟨hC1, hC2⟩ := (hψ'cube l hl).2 i
      have hfe : (fun t => F i l (fun j => selPieceChart ψ φ ψ' j l t)) =
          (fun t => pieceFam (yPullback F ψ) (fun l τ => φ 0 l (fun _ => τ)) i l
            (fun j => ψ' j l t)) := by
        funext t
        exact selPieceChart_apply F ψ φ ψ' i l t
      refine ⟨?_, ?_⟩
      · rw [hfe]; exact hC1
      · intro m hm t ht
        rw [hfe]; exact hC2 m hm t ht
  · -- the chart point of `ψ'` is realised by the combined chart
    intro ψ' hψ'
    exact Finset.mem_image_of_mem _ hψ'
  · -- the composite identity
    intro ψ' hψ' l hl t ht i
    exact selPieceChart_apply F ψ φ ψ' i l t

end Work.WilG4c
