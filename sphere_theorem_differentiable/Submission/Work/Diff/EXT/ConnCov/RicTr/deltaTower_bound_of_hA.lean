import Mathlib
import Submission.Work.Diff.EXT.ConnCov.RicTowerKit
import Submission.Work.Diff.EXT.LocalExtDefs
import Submission.Work.Diff.EXT.ConnCov.RicTr.twoConnKit
import Submission.Work.Diff.EXT.ConnCov.RicTr.DT.HAuxMain
import Submission.Work.Diff.EXT.ConnCov.RicTr.DTB.BndVDeltaTower
import Submission.Work.Diff.EXT.ConnCov.RicTr.sharpMovement_of_bndV
import Submission.Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM_bndV

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.ConnCov.RicTr

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-! ## Bridges between the `DT` copy and the `RicTowerKit` vocabulary

The `δ`-tower chapter (the `deltaTower` chain, copied into the `Work.Diff.EXT.ConnCov.DT`
namespace under `RicTr/DT/` so that it can be imported together with `RicTowerKit`) uses the
*connection-indexed* recursion `DT.vtower cov base`; the target statement uses the
*metric-indexed* `vtower g base` of `RicTowerKit`.  The two recursions have the same body
(modulo `lcOf`), so they agree. -/

/-- The two `(1,2)`-tensor recursion steps agree definitionally. -/
theorem DT_vstep_eq (g : SMet I M) {k : ℕ}
    (τ : Work.Diff.EXT.ConnCov.DT.VOp (I := I) (M := M) k) :
    Work.Diff.EXT.ConnCov.DT.vstep (I := I) (M := M) (Submission.Diff.lcOf g) τ
      = Work.Diff.EXT.ConnCov.vstep (I := I) (M := M) g τ := rfl

/-- The two `(1,2)`-tensor towers agree. -/
theorem DT_vtower_eq (g : SMet I M) (base : Work.Diff.EXT.ConnCov.DT.VOp (I := I) (M := M) 0)
    (c : ℕ) :
    Work.Diff.EXT.ConnCov.DT.vtower (I := I) (M := M) (Submission.Diff.lcOf g) base c
      = Work.Diff.EXT.ConnCov.vtower (I := I) (M := M) g base c := by
  induction c with
  | zero => rfl
  | succ c ih =>
      rw [show Work.Diff.EXT.ConnCov.DT.vtower (I := I) (M := M) (Submission.Diff.lcOf g)
              base (c + 1)
            = Work.Diff.EXT.ConnCov.DT.vstep (I := I) (M := M) (Submission.Diff.lcOf g)
                (Work.Diff.EXT.ConnCov.DT.vtower (I := I) (M := M) (Submission.Diff.lcOf g)
                  base c) from rfl,
        show Work.Diff.EXT.ConnCov.vtower (I := I) (M := M) g base (c + 1)
            = Work.Diff.EXT.ConnCov.vstep (I := I) (M := M) g
                (Work.Diff.EXT.ConnCov.vtower (I := I) (M := M) g base c) from rfl,
        ih]
      rfl

/-- The `DT`-`δ`-tower of `G` at `t` is the `RicTowerKit` tower of the connection difference
`deltaOf (G 0) (G t)`. -/
theorem DT_deltaTower_eq (G : ℝ → SMet I M) (t : ℝ) (c : ℕ) :
    Work.Diff.EXT.ConnCov.DT.deltaTower (I := I) (M := M) G t c
      = Work.Diff.EXT.ConnCov.vtower (I := I) (M := M) (G 0)
          (fun _ X Y => Work.Diff.EXT.ConnCov.deltaOf (I := I) (M := M) (G 0) (G t) X Y) c := by
  rw [show Work.Diff.EXT.ConnCov.DT.deltaTower (I := I) (M := M) G t c
        = Work.Diff.EXT.ConnCov.DT.vtower (I := I) (M := M) (Submission.Diff.lcOf (G 0))
            (fun (_ : Fin 0 → Work.Diff.EXT.ATower.TF (I := I) (M := M)) X Y =>
              Work.Diff.EXT.ConnCov.covDiff G t X Y) c from rfl,
    DT_vtower_eq]
  rfl

/-! ## The first conjunct of the target

The bound on the `∇^{G 0}`-tower of the connection difference is `exists_TB` (the `hAaux` chapter of
the `δ`-tower development, copied into `RicTr/DT/`), transported along the bridges above. -/

theorem deltaTower_fixed_bound_of_hA
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (T : ℝ) (hT : 0 < T)
    (k : ℕ) (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j)
    (hA : ∀ j, j < k → ∀ t ∈ Set.Ico (T / 2) T,
      Work.Diff.EXT.ATower.ValBound G t j
        (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
          (fun _ => Work.Diff.EXT.aOf G t) j) (B j)) :
    ∃ D : ℕ → ℝ, (∀ c, 0 ≤ D c) ∧ ∀ c, c < k → ∀ t ∈ Set.Ico (T / 2) T,
      (∀ (x : M) (v : Fin c → TangentSpace I x) (X Y : TangentSpace I x),
        Work.Diff.EXT.ConnCov.dvVal (G t)
            (Work.Diff.EXT.ConnCov.vtower (G 0)
              (fun _ X Y => Work.Diff.EXT.ConnCov.deltaOf (G 0) (G t) X Y) c) x v X Y
          ≤ D c * (Work.Diff.EXT.ConnCov.oneAddSqrtProd (G t) x v
              * Real.sqrt ((G t).inner x X X) * Real.sqrt ((G t).inner x Y Y))) := by
  cases k with
  | zero =>
      exact ⟨fun _ => 0, fun _ => le_rfl, fun c hc => absurd hc (by omega)⟩
  | succ k' =>
      have hA' : ∀ j, j ≤ k' → ∀ t ∈ Set.Ico (T / 2) T,
          Work.Diff.EXT.ATower.ValBound G t j
            (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
              (fun _ => Work.Diff.EXT.aOf G t) j) (B j) :=
        fun j hj => hA j (by omega)
      obtain ⟨D, hD0, hDB⟩ := Work.Diff.EXT.ConnCov.DT.exists_TB (I := I) (M := M)
        hLC G T hT k' B hB hA'
      refine ⟨fun c => if c ≤ k' then D c else 0, ?_, ?_⟩
      · intro c
        dsimp only
        by_cases hc : c ≤ k'
        · rw [if_pos hc]; exact hD0 c hc
        · rw [if_neg hc]
      · intro c hc t ht x v X Y
        have hc' : c ≤ k' := by omega
        dsimp only
        rw [if_pos hc']
        have hb := hDB c hc' t ht (fun p => Submission.Diff.smoothExt x (v p))
          (Submission.Diff.smoothExt x X) (Submission.Diff.smoothExt x Y) x
          (fun p => Work.Diff.GE.smoothExt_cmdiff x (v p))
          (Work.Diff.GE.smoothExt_cmdiff x X) (Work.Diff.GE.smoothExt_cmdiff x Y)
        rw [DT_deltaTower_eq] at hb
        simp only [Work.Diff.GE.smoothExt_apply, Work.Diff.EXT.ConnCov.dvVal,
          Work.Diff.EXT.ConnCov.oneAddSqrtProd] at hb ⊢
        simpa only [mul_assoc] using hb

/-! ## Bridges to the `DTB` copy of the `δ`-tower chapter -/

/-- The `DTB`-copy of the `(1,2)`-tensor tower agrees with the `DT`-copy. -/
theorem DTB_vtower_eq_DT (g : SMet I M)
    (base : Work.Diff.EXT.ConnCov.DTB.VOp (I := I) (M := M) 0) (c : ℕ) :
    Work.Diff.EXT.ConnCov.DTB.vtower (I := I) (M := M) (Submission.Diff.lcOf g) base c
      = Work.Diff.EXT.ConnCov.DT.vtower (I := I) (M := M) (Submission.Diff.lcOf g) base c := by
  induction c with
  | zero => rfl
  | succ c ih =>
      rw [show Work.Diff.EXT.ConnCov.DTB.vtower (I := I) (M := M) (Submission.Diff.lcOf g)
              base (c + 1)
            = Work.Diff.EXT.ConnCov.DTB.vstep (I := I) (M := M) (Submission.Diff.lcOf g)
                (Work.Diff.EXT.ConnCov.DTB.vtower (I := I) (M := M) (Submission.Diff.lcOf g)
                  base c) from rfl,
        show Work.Diff.EXT.ConnCov.DT.vtower (I := I) (M := M) (Submission.Diff.lcOf g)
              base (c + 1)
            = Work.Diff.EXT.ConnCov.DT.vstep (I := I) (M := M) (Submission.Diff.lcOf g)
                (Work.Diff.EXT.ConnCov.DT.vtower (I := I) (M := M) (Submission.Diff.lcOf g)
                  base c) from rfl,
        ih]
      rfl

/-- The `DTB`-`δ`-tower of `G` at `t` is the `DT` one. -/
theorem DTB_deltaTower_eq_DT (G : ℝ → SMet I M) (t : ℝ) (c : ℕ) :
    Work.Diff.EXT.ConnCov.DTB.deltaTower (I := I) (M := M) G t c
      = Work.Diff.EXT.ConnCov.DT.deltaTower (I := I) (M := M) G t c := by
  rw [show Work.Diff.EXT.ConnCov.DTB.deltaTower (I := I) (M := M) G t c
        = Work.Diff.EXT.ConnCov.DTB.vtower (I := I) (M := M) (Submission.Diff.lcOf (G 0))
            (fun (_ : Fin 0 → Work.Diff.EXT.ATower.TF (I := I) (M := M)) X Y =>
              Work.Diff.EXT.ConnCov.covDiff G t X Y) c from rfl,
    show Work.Diff.EXT.ConnCov.DT.deltaTower (I := I) (M := M) G t c
        = Work.Diff.EXT.ConnCov.DT.vtower (I := I) (M := M) (Submission.Diff.lcOf (G 0))
            (fun (_ : Fin 0 → Work.Diff.EXT.ATower.TF (I := I) (M := M)) X Y =>
              Work.Diff.EXT.ConnCov.covDiff G t X Y) c from rfl,
    DTB_vtower_eq_DT]

/-- Monotonicity of `ValBound` in its constant. -/
theorem valBound_mono (G : ℝ → SMet I M) (t : ℝ) {k : ℕ}
    (τ : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) k) {C C' : ℝ}
    (h : Work.Diff.EXT.ATower.ValBound G t k τ C) (hC : C ≤ C') :
    Work.Diff.EXT.ATower.ValBound G t k τ C' := by
  intro x v a b c
  have h1 : 0 ≤ ∏ i : Fin k, Real.sqrt ((G t).inner x (v i) (v i)) :=
    Finset.prod_nonneg (fun i _ => Real.sqrt_nonneg _)
  have h2 : 0 ≤ Real.sqrt ((G t).inner x a a) := Real.sqrt_nonneg _
  have h3 : 0 ≤ Real.sqrt ((G t).inner x b b) := Real.sqrt_nonneg _
  have h4 : 0 ≤ Real.sqrt ((G t).inner x c c) := Real.sqrt_nonneg _
  have hP : 0 ≤ (∏ i : Fin k, Real.sqrt ((G t).inner x (v i) (v i)))
      * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b)
      * Real.sqrt ((G t).inner x c c) := mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4
  have hstep : C * ((∏ i : Fin k, Real.sqrt ((G t).inner x (v i) (v i)))
        * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b)
        * Real.sqrt ((G t).inner x c c))
      ≤ C' * ((∏ i : Fin k, Real.sqrt ((G t).inner x (v i) (v i)))
        * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b)
        * Real.sqrt ((G t).inner x c c)) := mul_le_mul_of_nonneg_right hC hP
  exact le_trans (h x v a b c) (by simpa only [mul_assoc] using hstep)

/-- Monotonicity of `AMB.BndV` in its constant. -/
theorem bndV_mono (G : ℝ → SMet I M) (t : ℝ) {c : ℕ}
    (Θ : (Fin c → Work.Diff.EXT.ATower.TF (I := I) (M := M)) →
      Work.Diff.EXT.ATower.TF (I := I) (M := M) →
      Work.Diff.EXT.ATower.TF (I := I) (M := M) →
      Work.Diff.EXT.ATower.TF (I := I) (M := M)) {C C' : ℝ}
    (h : Work.Diff.EXT.ConnCov.AMB.BndV G t Θ C) (hC : C ≤ C') :
    Work.Diff.EXT.ConnCov.AMB.BndV G t Θ C' := by
  intro v X Z hv hX hZ x
  have h1 : 0 ≤ ∏ i : Fin c, (1 + Real.sqrt ((G t).inner x (v i x) (v i x))) :=
    Finset.prod_nonneg (fun i _ => by
      have h := Real.sqrt_nonneg ((G t).inner x (v i x) (v i x)); linarith)
  have h2 : 0 ≤ 1 + Real.sqrt ((G t).inner x (X x) (X x)) := by
    have h := Real.sqrt_nonneg ((G t).inner x (X x) (X x)); linarith
  have h3 : 0 ≤ 1 + Real.sqrt ((G t).inner x (Z x) (Z x)) := by
    have h := Real.sqrt_nonneg ((G t).inner x (Z x) (Z x)); linarith
  have hP : 0 ≤ (∏ i : Fin c, (1 + Real.sqrt ((G t).inner x (v i x) (v i x))))
      * (1 + Real.sqrt ((G t).inner x (X x) (X x)))
      * (1 + Real.sqrt ((G t).inner x (Z x) (Z x))) := mul_nonneg (mul_nonneg h1 h2) h3
  have hstep : C * ((∏ i : Fin c, (1 + Real.sqrt ((G t).inner x (v i x) (v i x))))
        * (1 + Real.sqrt ((G t).inner x (X x) (X x)))
        * (1 + Real.sqrt ((G t).inner x (Z x) (Z x))))
      ≤ C' * ((∏ i : Fin c, (1 + Real.sqrt ((G t).inner x (v i x) (v i x))))
        * (1 + Real.sqrt ((G t).inner x (X x) (X x)))
        * (1 + Real.sqrt ((G t).inner x (Z x) (Z x)))) := mul_le_mul_of_nonneg_right hC hP
  exact le_trans (h v X Z hv hX hZ x) (by simpa only [mul_assoc] using hstep)

/-! ## The second conjunct of the target

`∇^{G t, c}δ` is bounded through: the `AMB.BndV` bounds on the *fixed* `δ`-tower (`DTB`, proved
independently of `hA`), the *flip* `movingATower_of_fixed` (the moving `aOf`-tower from the fixed
one), `RicFlip.deltaTowerM_bndV` (the moving `δ`-tower from the moving `aOf`-tower) and the
sharpening `sharpMovement_of_bndV`. -/

theorem deltaTower_moving_bound_of_hA
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (T : ℝ) (hT : 0 < T)
    (k : ℕ) (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j)
    (hA : ∀ j, j < k → ∀ t ∈ Set.Ico (T / 2) T,
      Work.Diff.EXT.ATower.ValBound G t j
        (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
          (fun _ => Work.Diff.EXT.aOf G t) j) (B j)) :
    ∃ D : ℕ → ℝ, (∀ c, 0 ≤ D c) ∧ ∀ c, c < k → ∀ t ∈ Set.Ico (T / 2) T,
      (∀ (x : M) (v : Fin c → TangentSpace I x) (X Y : TangentSpace I x),
        Work.Diff.EXT.ConnCov.dvVal (G t)
            (Work.Diff.EXT.ConnCov.vtower (G t)
              (fun _ X Y => Work.Diff.EXT.ConnCov.deltaOf (G 0) (G t) X Y) c) x v X Y
          ≤ D c * (Work.Diff.EXT.ConnCov.oneAddSqrtProd (G t) x v
              * Real.sqrt ((G t).inner x X X) * Real.sqrt ((G t).inner x Y Y))) := by
  cases k with
  | zero => exact ⟨fun _ => 0, fun _ => le_rfl, fun c hc => absurd hc (by omega)⟩
  | succ k' =>
      have hA' : ∀ j, j ≤ k' → ∀ t ∈ Set.Ico (T / 2) T,
          Work.Diff.EXT.ATower.ValBound G t j
            (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
              (fun _ => Work.Diff.EXT.aOf G t) j) (B j) := fun j hj => hA j (by omega)
      -- `AMB.BndV` bounds on the fixed `δ`-tower
      obtain ⟨Bv, hBv0, hBv⟩ := Work.Diff.EXT.ConnCov.DTB.bndV_deltaTower (I := I) (M := M)
        hLC (G := G) hT k' B hB hA'
      -- combine the two constants, so that the flip (whose statement uses one constant for both
      -- hypotheses) can be applied
      set Bmax : ℕ → ℝ := fun j => max (B j) (Bv j)
      have hBmax : ∀ j, 0 ≤ Bmax j :=
        fun j => le_trans (hB j) (le_max_left _ _)
      -- THE REMAINING OBLIGATION of the moving half: the *flip*
      -- `Work.Diff.EXT.ConnCov.RicTr.movingATower_of_fixed` (bounds on the `∇^{G t}`-tower of
      -- `aOf` from the bounds `hA` on the `∇^{G 0}`-tower and on the fixed `δ`-tower) has been
      -- PROVED in `Submission/Work/Diff/EXT/ConnCov/RicTr/movingATower_of_fixed.lean`, but that
      -- file's proof imports the *original* `Submission.Work.Diff.EXT.ConnCov.deltaTower` chain,
      -- which declares `Work.Diff.EXT.ConnCov.vstep` and therefore clashes with `RicTowerKit`
      -- (imported by this file): the two cannot coexist.  To use it here, either
      --   (a) re-prove the same statement with `depends_on` restricted to the `DT.*` copies
      --       (`Diff/EXT/ConnCov/RicTr/DT/HAuxMain` etc.) and NO import of
      --       `Submission.Work.Diff.EXT.ConnCov.deltaTower`, or
      --   (b) re-prove it on the `RicFlip.towerEqLoweringDeltaTowerM` side (which *is* compatible
      --       with `RicTowerKit`), using `RicFlip.vtowerM`/`deltaTowerM` for the `∇^{G 0}`-towers.
      -- The statement itself is correct as reviewed; only the import chain of the existing proof
      -- is incompatible.  (The constants below are irrelevant until then: `Bm` is arbitrary.)
      obtain ⟨Bm, hBm0, hBm⟩ : ∃ Bm : ℕ → ℝ, (∀ j, 0 ≤ Bm j) ∧ ∀ j, j ≤ k' →
          ∀ t ∈ Set.Ico (T / 2) T,
          Work.Diff.EXT.ATower.ValBound G t j
            (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G t))
              (fun _ => Work.Diff.EXT.aOf G t) j) (Bm j) := by
        sorry
      -- the moving `δ`-tower bounds
      have hBndV : ∀ c, c < k' + 1 → ∀ t ∈ Set.Ico (T / 2) T,
          Work.Diff.EXT.ConnCov.AMB.BndV G t
            (Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM G t c) (Bm c) :=
        fun c hc t ht => Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM_bndV (I := I) (M := M)
          hLC G t (k' + 1) Bm hBm0 (fun j hj => hBm j (by omega) t ht) c hc
      obtain ⟨E, hE0, hE⟩ := sharpMovement_of_bndV (I := I) (M := M) hLC G T hT (k' + 1) Bm hBm0 hBndV
      exact ⟨E, hE0, fun c hc t ht => hE c (by omega) t ht⟩

theorem deltaTower_bound_of_hA
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (T C : ℝ) (hT : 0 < T) (hC : 0 ≤ C)
    (hflow : Submission.Diff.IsRicciFlow G T)
    (hbound : ∀ t ∈ Set.Ico 0 T, Submission.Diff.CurvBound (G t) C)
    (hmet : ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ u : TangentSpace I x,
      (G t).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G 0).inner x u u ∧
      (G 0).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G t).inner x u u)
    (hShi : Work.Diff.EXT.ShiBounds (I := I) (M := M))
    (k : ℕ) (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j)
    (hA : ∀ j, j < k → ∀ t ∈ Set.Ico (T / 2) T,
      Work.Diff.EXT.ATower.ValBound G t j
        (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
          (fun _ => Work.Diff.EXT.aOf G t) j) (B j)) :
    ∃ D : ℕ → ℝ, (∀ c, 0 ≤ D c) ∧ ∀ c, c < k → ∀ t ∈ Set.Ico (T / 2) T,
      (∀ (x : M) (v : Fin c → TangentSpace I x) (X Y : TangentSpace I x),
        Work.Diff.EXT.ConnCov.dvVal (G t)
            (Work.Diff.EXT.ConnCov.vtower (G 0)
              (fun _ X Y => Work.Diff.EXT.ConnCov.deltaOf (G 0) (G t) X Y) c) x v X Y
          ≤ D c * (Work.Diff.EXT.ConnCov.oneAddSqrtProd (G t) x v
              * Real.sqrt ((G t).inner x X X) * Real.sqrt ((G t).inner x Y Y)))
      ∧ (∀ (x : M) (v : Fin c → TangentSpace I x) (X Y : TangentSpace I x),
        Work.Diff.EXT.ConnCov.dvVal (G t)
            (Work.Diff.EXT.ConnCov.vtower (G t)
              (fun _ X Y => Work.Diff.EXT.ConnCov.deltaOf (G 0) (G t) X Y) c) x v X Y
          ≤ D c * (Work.Diff.EXT.ConnCov.oneAddSqrtProd (G t) x v
              * Real.sqrt ((G t).inner x X X) * Real.sqrt ((G t).inner x Y Y))) := by
  obtain ⟨D₁, hD₁⟩ := deltaTower_fixed_bound_of_hA (I := I) (M := M) hLC G T hT k B hB hA
  obtain ⟨D₂, hD₂⟩ := deltaTower_moving_bound_of_hA (I := I) (M := M) hLC G T hT k B hB hA
  refine ⟨fun c => max (D₁ c) (D₂ c),
    fun c => le_trans (hD₁.1 c) (le_max_left _ _), ?_⟩
  intro c hc t ht
  constructor
  · intro x v X Y
    refine le_trans (hD₁.2 c hc t ht x v X Y)
      (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
    refine mul_nonneg (mul_nonneg ?_ (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    simp only [Work.Diff.EXT.ConnCov.oneAddSqrtProd]
    exact Finset.prod_nonneg (fun i _ => by
      have h := Real.sqrt_nonneg ((G t).inner x (v i) (v i)); linarith)
  · intro x v X Y
    refine le_trans (hD₂.2 c hc t ht x v X Y)
      (mul_le_mul_of_nonneg_right (le_max_right _ _) ?_)
    refine mul_nonneg (mul_nonneg ?_ (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    simp only [Work.Diff.EXT.ConnCov.oneAddSqrtProd]
    exact Finset.prod_nonneg (fun i _ => by
      have h := Real.sqrt_nonneg ((G t).inner x (v i) (v i)); linarith)

end Work.Diff.EXT.ConnCov.RicTr
