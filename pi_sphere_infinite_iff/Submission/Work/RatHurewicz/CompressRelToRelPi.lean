import Mathlib
import Submission.Work.RatHurewicz.CubeToPinched
import Submission.Work.RatHurewicz.attachIncl_isOpenMap_range
import Submission.Work.RatHurewicz.AttachRange.AttachInclInj
import Submission.Work.Stems.mulEquiv_of_homotopyEquiv
import Submission.Work.RatHurewicz.subsingleton_zerothHomotopy_of_homotopyEquiv

/-!
# From the compression property to the vanishing of the relative homotopy groups

Area **RATHUREWICZ**.  This file proves the implication "(2) ⟹ (1)" of tom Dieck's Proposition
6.7.5 in the form needed by `Work.RatHurewicz.subsingleton_relPi_of_compressRel_range`:

* `homotopy_cube_homotopic_const_of_paths_mem` — a based cube in the homotopy fibre whose paths have
  image in `A` is null-homotopic (shrink the paths towards their initial point);
* `homotopyRel_cubeToPinched_of_compress` — a compression homotopy of the pinched map
  `cubeToPinched a₀ j p`, relative to the boundary, curries back to a homotopy of based cubes;
* `subsingleton_relPi_of_compressRel` — the compression property in dimensions `≤ n+1` implies the
  vanishing of the relative homotopy groups in degrees `≤ n`;
* `subsingleton_relPi_attachIncl_of_range` — the transport of that statement from the inclusion of
  the range of `attachIncl` to `attachIncl` itself (the two homotopy fibres are homeomorphic).
-/

open scoped Topology Topology.Homotopy unitInterval
open Work.StemsB (PathSpace evalOne)

namespace Work.RatHurewicz

noncomputable section

variable {Y : Type} [TopologicalSpace Y] {A : Set Y}

/-- The shrinking parameter `σ v s = clamp (s (1-v))`. -/
def shrink (v s : unitInterval) : unitInterval := clampI ((s : ℝ) * (1 - (v : ℝ)))

@[simp] theorem shrink_zero_left (s : unitInterval) : shrink 0 s = s := by
  show clampI ((s : ℝ) * (1 - ((0 : unitInterval) : ℝ))) = s
  rw [show ((0 : unitInterval) : ℝ) = 0 by rfl, sub_zero, mul_one]
  exact clampI_of_mem s.2.1 s.2.2

@[simp] theorem shrink_one_left (s : unitInterval) : shrink 1 s = 0 := by
  show clampI ((s : ℝ) * (1 - ((1 : unitInterval) : ℝ))) = 0
  rw [show ((1 : unitInterval) : ℝ) = 1 by rfl, sub_self, mul_zero]
  exact clampI_of_mem le_rfl zero_le_one

@[simp] theorem shrink_zero_right (v : unitInterval) : shrink v 0 = 0 := by
  show clampI (((0 : unitInterval) : ℝ) * (1 - (v : ℝ))) = 0
  rw [show ((0 : unitInterval) : ℝ) = 0 by rfl, zero_mul]
  exact clampI_of_mem le_rfl zero_le_one

theorem continuous_shrink : Continuous fun p : unitInterval × unitInterval => shrink p.1 p.2 :=
  continuous_clampI.comp ((continuous_subtype_val.comp continuous_snd).mul
    (continuous_const.sub (continuous_subtype_val.comp continuous_fst)))

theorem homotopy_cube_homotopic_const_of_paths_mem (a₀ : ↥A) (j : ℕ)
    (q : GenLoop (Fin j) (homotopyFibre (setIncl A) a₀) (homotopyFibreBasepoint (setIncl A) a₀))
    (hall : ∀ (u : ICube j) (s : unitInterval), fibreCM (q u) s ∈ A) :
    GenLoop.Homotopic q GenLoop.const := by
  have hinner : ∀ z : unitInterval × ICube j, Continuous fun s : I =>
      fibreCM (q z.2) (shrink z.1 s) := fun z =>
    (fibreCM (q z.2)).continuous.comp
      (continuous_shrink.comp (Continuous.prodMk continuous_const continuous_id))
  have hval_cont : Continuous fun z : unitInterval × ICube j =>
      fibreCM (q z.2) (shrink z.1 1) :=
    continuous_apply_comp ((fibreCMFamily a₀).continuous.comp (q.1.continuous.comp continuous_snd))
      (continuous_shrink.comp (Continuous.prodMk continuous_fst continuous_const))
  have hpath_cont : Continuous fun w : (unitInterval × ICube j) × I =>
      fibreCM (q w.1.2) (shrink w.1.1 w.2) :=
    continuous_apply_comp ((fibreCMFamily a₀).continuous.comp
        (q.1.continuous.comp (continuous_snd.comp continuous_fst)))
      (continuous_shrink.comp (Continuous.prodMk (continuous_fst.comp continuous_fst) continuous_snd))
  have hγ : Continuous fun z : unitInterval × ICube j =>
      (⟨fun s => fibreCM (q z.2) (shrink z.1 s), hinner z⟩ : C(I, Y)) :=
    ContinuousMap.continuous_of_continuous_uncurry
      (fun z : unitInterval × ICube j =>
        (⟨fun s => fibreCM (q z.2) (shrink z.1 s), hinner z⟩ : C(I, Y))) hpath_cont
  have hPath : Continuous fun z : unitInterval × ICube j =>
      (⟨(⟨fun s => fibreCM (q z.2) (shrink z.1 s), hinner z⟩ : C(I, Y)),
        (by
          show fibreCM (q z.2) (shrink z.1 0) = setIncl A a₀
          rw [shrink_zero_right]
          exact fibreCM_zero (q z.2))⟩ : PathSpace Y (setIncl A a₀)) :=
    Continuous.subtype_mk hγ (fun z => by
      show fibreCM (q z.2) (shrink z.1 0) = setIncl A a₀
      rw [shrink_zero_right]
      exact fibreCM_zero (q z.2))
  have hA' : Continuous fun z : unitInterval × ICube j =>
      (⟨fibreCM (q z.2) (shrink z.1 1), hall z.2 (shrink z.1 1)⟩ : ↥A) :=
    Continuous.subtype_mk hval_cont (fun z => hall z.2 (shrink z.1 1))
  have hPair : Continuous fun z : unitInterval × ICube j =>
      ((⟨fibreCM (q z.2) (shrink z.1 1), hall z.2 (shrink z.1 1)⟩ : ↥A),
        (⟨(⟨fun s => fibreCM (q z.2) (shrink z.1 s), hinner z⟩ : C(I, Y)),
          (by
            show fibreCM (q z.2) (shrink z.1 0) = setIncl A a₀
            rw [shrink_zero_right]
            exact fibreCM_zero (q z.2))⟩ : PathSpace Y (setIncl A a₀))) :=
    Continuous.prodMk hA' hPath
  have hFinal : Continuous fun z : unitInterval × ICube j =>
      (⟨((⟨fibreCM (q z.2) (shrink z.1 1), hall z.2 (shrink z.1 1)⟩ : ↥A),
        (⟨(⟨fun s => fibreCM (q z.2) (shrink z.1 s), hinner z⟩ : C(I, Y)),
          (by
            show fibreCM (q z.2) (shrink z.1 0) = setIncl A a₀
            rw [shrink_zero_right]
            exact fibreCM_zero (q z.2))⟩ : PathSpace Y (setIncl A a₀))),
        (by
          show fibreCM (q z.2) (shrink z.1 1) =
            setIncl A (⟨fibreCM (q z.2) (shrink z.1 1), hall z.2 (shrink z.1 1)⟩ : ↥A)
          rfl)⟩ : homotopyFibre (setIncl A) a₀) :=
    Continuous.subtype_mk hPair (fun z => by
      show fibreCM (q z.2) (shrink z.1 1) =
        setIncl A (⟨fibreCM (q z.2) (shrink z.1 1), hall z.2 (shrink z.1 1)⟩ : ↥A)
      rfl)
  refine ⟨{
    toFun := fun z : unitInterval × ICube j =>
      (⟨((⟨fibreCM (q z.2) (shrink z.1 1), hall z.2 (shrink z.1 1)⟩ : ↥A),
        (⟨(⟨fun s => fibreCM (q z.2) (shrink z.1 s), hinner z⟩ : C(I, Y)),
          (by
            show fibreCM (q z.2) (shrink z.1 0) = setIncl A a₀
            rw [shrink_zero_right]
            exact fibreCM_zero (q z.2))⟩ : PathSpace Y (setIncl A a₀))),
        (by
          show fibreCM (q z.2) (shrink z.1 1) =
            setIncl A (⟨fibreCM (q z.2) (shrink z.1 1), hall z.2 (shrink z.1 1)⟩ : ↥A)
          rfl)⟩ : homotopyFibre (setIncl A) a₀)
    continuous_toFun := hFinal
    map_zero_left := by
      intro u
      refine Subtype.ext (Prod.ext (Subtype.ext ?_) (Subtype.ext (ContinuousMap.ext (fun s => ?_))))
      · show fibreCM (q u) (shrink 0 1) = ((q u).1.1 : Y)
        rw [shrink_zero_left]
        exact fibreCM_one (q u)
      · show fibreCM (q u) (shrink 0 s) = fibreCM (q u) s
        rw [shrink_zero_left]
    map_one_left := by
      intro u
      refine Subtype.ext (Prod.ext (Subtype.ext ?_) (Subtype.ext (ContinuousMap.ext (fun s => ?_))))
      · show fibreCM (q u) (shrink 1 1) = ((homotopyFibreBasepoint (setIncl A) a₀).1.1 : Y)
        rw [shrink_one_left]
        exact fibreCM_zero (q u)
      · show fibreCM (q u) (shrink 1 s) = (homotopyFibreBasepoint (setIncl A) a₀).1.2.1 s
        rw [shrink_one_left]
        exact fibreCM_zero (q u)
    prop' := by
      intro v u hu
      refine Subtype.ext (Prod.ext (Subtype.ext ?_) (Subtype.ext (ContinuousMap.ext (fun s => ?_))))
      · show fibreCM (q u) (shrink v 1) = ((q u).1.1 : Y)
        rw [show q u = homotopyFibreBasepoint (setIncl A) a₀ from q.2 u hu]
        rfl
      · show fibreCM (q u) (shrink v s) = fibreCM (q u) s
        rw [show q u = homotopyFibreBasepoint (setIncl A) a₀ from q.2 u hu]
        rfl }⟩


theorem homotopyRel_cubeToPinched_of_compress (a₀ : ↥A) (j : ℕ)
    (p : GenLoop (Fin j) (homotopyFibre (setIncl A) a₀) (homotopyFibreBasepoint (setIncl A) a₀))
    (G : C(ICube (j + 1) × unitInterval, Y))
    (hG0 : ∀ x, G (x, 0) = cubeToPinched a₀ j p x)
    (hGbd : ∀ x, x ∈ Cube.boundary (Fin (j + 1)) →
      ∀ t, G (x, t) = cubeToPinched a₀ j p x)
    (hG1 : ∀ x, G (x, 1) ∈ A) :
    ∃ p₁ : GenLoop (Fin j) (homotopyFibre (setIncl A) a₀)
        (homotopyFibreBasepoint (setIncl A) a₀),
      GenLoop.Homotopic p p₁ ∧ ∀ (u : ICube j) (s : unitInterval), fibreCM (p₁ u) s ∈ A := by
  -- the top and bottom faces of `I^{j+1}`
  have hbot : ∀ u : ICube j, (Fin.snoc u 0 : ICube (j + 1)) ∈ Cube.boundary (Fin (j + 1)) :=
    fun u => ⟨Fin.last j, Or.inl (Fin.snoc_last ..)⟩
  have htop : ∀ u : ICube j, (Fin.snoc u 1 : ICube (j + 1)) ∈ Cube.boundary (Fin (j + 1)) :=
    fun u => ⟨Fin.last j, Or.inr (Fin.snoc_last ..)⟩
  have hside : ∀ (u : ICube j) (s : unitInterval), u ∈ Cube.boundary (Fin j) →
      (Fin.snoc u s : ICube (j + 1)) ∈ Cube.boundary (Fin (j + 1)) := by
    rintro u s ⟨i, hi⟩
    exact ⟨Fin.castSucc i, by rw [Fin.snoc_castSucc]; exact hi⟩
  -- the values of the compression homotopy on the faces
  have hGbot : ∀ (u : ICube j) (t : unitInterval), G (Fin.snoc u 0, t) = setIncl A a₀ := by
    intro u t
    rw [hGbd (Fin.snoc u 0) (hbot u) t, cubeToPinched_snoc_zero]
  have hGtop : ∀ (u : ICube j) (t : unitInterval),
      G (Fin.snoc u 1, t) = setIncl A ((p u).1.1) := by
    intro u t
    rw [hGbd (Fin.snoc u 1) (htop u) t, cubeToPinched_snoc_one]
  -- continuity of the uncurried family of paths of the endpoint cube
  have hcont1 : Continuous fun w : ICube j × I => G (Fin.snoc w.1 w.2, 1) :=
    G.continuous.comp (Continuous.prodMk (continuous_snocTuple j) continuous_const)
  have hinner1 : ∀ z : ICube j, Continuous fun s : I => G (Fin.snoc z s, 1) := fun z =>
    G.continuous.comp (Continuous.prodMk
      ((continuous_snocTuple j).comp (Continuous.prodMk continuous_const continuous_id))
      continuous_const)
  have hγ1 : Continuous fun z : ICube j =>
      (⟨fun s => G (Fin.snoc z s, 1), hinner1 z⟩ : C(I, Y)) :=
    ContinuousMap.continuous_of_continuous_uncurry
      (fun z : ICube j => (⟨fun s => G (Fin.snoc z s, 1), hinner1 z⟩ : C(I, Y))) hcont1
  have hPath1 : Continuous fun z : ICube j =>
      (⟨(⟨fun s => G (Fin.snoc z s, 1), hinner1 z⟩ : C(I, Y)),
        (by
          show G (Fin.snoc z 0, 1) = setIncl A a₀
          exact hGbot z 1)⟩ : PathSpace Y (setIncl A a₀)) :=
    Continuous.subtype_mk hγ1 (fun z => by
      show G (Fin.snoc z 0, 1) = setIncl A a₀
      exact hGbot z 1)
  have hA1 : Continuous fun z : ICube j => ((p z).1.1 : ↥A) :=
    (continuous_fst.comp continuous_subtype_val).comp p.1.continuous
  have hPair1 : Continuous fun z : ICube j =>
      (((p z).1.1 : ↥A),
        (⟨(⟨fun s => G (Fin.snoc z s, 1), hinner1 z⟩ : C(I, Y)),
          (by
            show G (Fin.snoc z 0, 1) = setIncl A a₀
            exact hGbot z 1)⟩ : PathSpace Y (setIncl A a₀))) :=
    Continuous.prodMk hA1 hPath1
  have hFinal1 : Continuous fun z : ICube j =>
      (⟨(((p z).1.1 : ↥A),
        (⟨(⟨fun s => G (Fin.snoc z s, 1), hinner1 z⟩ : C(I, Y)),
          (by
            show G (Fin.snoc z 0, 1) = setIncl A a₀
            exact hGbot z 1)⟩ : PathSpace Y (setIncl A a₀))),
        (by
          show G (Fin.snoc z 1, 1) = setIncl A ((p z).1.1)
          exact hGtop z 1)⟩ : homotopyFibre (setIncl A) a₀) :=
    Continuous.subtype_mk hPair1 (fun z => by
      show G (Fin.snoc z 1, 1) = setIncl A ((p z).1.1)
      exact hGtop z 1)
  have hbase1 : ∀ u ∈ Cube.boundary (Fin j),
      (⟨(((p u).1.1 : ↥A),
        (⟨(⟨fun s => G (Fin.snoc u s, 1), hinner1 u⟩ : C(I, Y)),
          (by
            show G (Fin.snoc u 0, 1) = setIncl A a₀
            exact hGbot u 1)⟩ : PathSpace Y (setIncl A a₀))),
        (by
          show G (Fin.snoc u 1, 1) = setIncl A ((p u).1.1)
          exact hGtop u 1)⟩ : homotopyFibre (setIncl A) a₀)
      = homotopyFibreBasepoint (setIncl A) a₀ := by
    intro u hu
    refine Subtype.ext (Prod.ext (Subtype.ext ?_) (Subtype.ext (ContinuousMap.ext (fun s => ?_))))
    · show (((p u).1.1 : ↥A) : Y) = ((homotopyFibreBasepoint (setIncl A) a₀).1.1 : Y)
      rw [show p u = homotopyFibreBasepoint (setIncl A) a₀ from p.2 u hu]
    · show G (Fin.snoc u s, 1) =
        (homotopyFibreBasepoint (setIncl A) a₀).1.2.1 s
      rw [hGbd (Fin.snoc u s) (hside u s hu) 1, cubeToPinched_snoc,
        show p u = homotopyFibreBasepoint (setIncl A) a₀ from p.2 u hu]
      rfl
  refine ⟨⟨⟨fun z : ICube j =>
      (⟨(((p z).1.1 : ↥A),
        (⟨(⟨fun s => G (Fin.snoc z s, 1), hinner1 z⟩ : C(I, Y)),
          (by
            show G (Fin.snoc z 0, 1) = setIncl A a₀
            exact hGbot z 1)⟩ : PathSpace Y (setIncl A a₀))),
        (by
          show G (Fin.snoc z 1, 1) = setIncl A ((p z).1.1)
          exact hGtop z 1)⟩ : homotopyFibre (setIncl A) a₀),
      hFinal1⟩, hbase1⟩, ?_, ?_⟩
  · -- the homotopy from `p` to `p₁`
    have hcont2 : Continuous fun w : (unitInterval × ICube j) × I =>
        G (Fin.snoc w.1.2 w.2, w.1.1) :=
      G.continuous.comp (Continuous.prodMk
        ((continuous_snocTuple j).comp
          (Continuous.prodMk (continuous_snd.comp continuous_fst) continuous_snd))
        (continuous_fst.comp continuous_fst))
    have hinner2 : ∀ z : unitInterval × ICube j, Continuous fun s : I =>
        G (Fin.snoc z.2 s, z.1) := fun z =>
      G.continuous.comp (Continuous.prodMk
        ((continuous_snocTuple j).comp (Continuous.prodMk continuous_const continuous_id))
        continuous_const)
    have hγ2 : Continuous fun z : unitInterval × ICube j =>
        (⟨fun s => G (Fin.snoc z.2 s, z.1), hinner2 z⟩ : C(I, Y)) :=
      ContinuousMap.continuous_of_continuous_uncurry
        (fun z : unitInterval × ICube j =>
          (⟨fun s => G (Fin.snoc z.2 s, z.1), hinner2 z⟩ : C(I, Y))) hcont2
    have hPath2 : Continuous fun z : unitInterval × ICube j =>
        (⟨(⟨fun s => G (Fin.snoc z.2 s, z.1), hinner2 z⟩ : C(I, Y)),
          (by
            show G (Fin.snoc z.2 0, z.1) = setIncl A a₀
            exact hGbot z.2 z.1)⟩ : PathSpace Y (setIncl A a₀)) :=
      Continuous.subtype_mk hγ2 (fun z => by
        show G (Fin.snoc z.2 0, z.1) = setIncl A a₀
        exact hGbot z.2 z.1)
    have hA2 : Continuous fun z : unitInterval × ICube j => ((p z.2).1.1 : ↥A) :=
      (continuous_fst.comp continuous_subtype_val).comp (p.1.continuous.comp continuous_snd)
    have hPair2 : Continuous fun z : unitInterval × ICube j =>
        (((p z.2).1.1 : ↥A),
          (⟨(⟨fun s => G (Fin.snoc z.2 s, z.1), hinner2 z⟩ : C(I, Y)),
            (by
              show G (Fin.snoc z.2 0, z.1) = setIncl A a₀
              exact hGbot z.2 z.1)⟩ : PathSpace Y (setIncl A a₀))) :=
      Continuous.prodMk hA2 hPath2
    have hFinal2 : Continuous fun z : unitInterval × ICube j =>
        (⟨(((p z.2).1.1 : ↥A),
          (⟨(⟨fun s => G (Fin.snoc z.2 s, z.1), hinner2 z⟩ : C(I, Y)),
            (by
              show G (Fin.snoc z.2 0, z.1) = setIncl A a₀
              exact hGbot z.2 z.1)⟩ : PathSpace Y (setIncl A a₀))),
          (by
            show G (Fin.snoc z.2 1, z.1) = setIncl A ((p z.2).1.1)
            exact hGtop z.2 z.1)⟩ : homotopyFibre (setIncl A) a₀) :=
      Continuous.subtype_mk hPair2 (fun z => by
        show G (Fin.snoc z.2 1, z.1) = setIncl A ((p z.2).1.1)
        exact hGtop z.2 z.1)
    refine ⟨{
      toFun := fun z : unitInterval × ICube j =>
        (⟨(((p z.2).1.1 : ↥A),
          (⟨(⟨fun s => G (Fin.snoc z.2 s, z.1), hinner2 z⟩ : C(I, Y)),
            (by
              show G (Fin.snoc z.2 0, z.1) = setIncl A a₀
              exact hGbot z.2 z.1)⟩ : PathSpace Y (setIncl A a₀))),
          (by
            show G (Fin.snoc z.2 1, z.1) = setIncl A ((p z.2).1.1)
            exact hGtop z.2 z.1)⟩ : homotopyFibre (setIncl A) a₀)
      continuous_toFun := hFinal2
      map_zero_left := by
        intro u
        refine Subtype.ext (Prod.ext (Subtype.ext ?_) (Subtype.ext (ContinuousMap.ext (fun s => ?_))))
        · show (((p u).1.1 : ↥A) : Y) = (((p u).1.1 : ↥A) : Y)
          rfl
        · show G (Fin.snoc u s, 0) = fibreCM (p u) s
          rw [hG0 (Fin.snoc u s), cubeToPinched_snoc]
      map_one_left := by
        intro u
        refine Subtype.ext (Prod.ext (Subtype.ext ?_) (Subtype.ext (ContinuousMap.ext (fun s => ?_))))
        · show (((p u).1.1 : ↥A) : Y) = (((p u).1.1 : ↥A) : Y)
          rfl
        · show G (Fin.snoc u s, 1) = G (Fin.snoc u s, 1)
          rfl
      prop' := by
        intro t u hu
        refine Subtype.ext (Prod.ext (Subtype.ext ?_) (Subtype.ext (ContinuousMap.ext (fun s => ?_))))
        · show (((p u).1.1 : ↥A) : Y) = (((p u).1.1 : ↥A) : Y)
          rfl
        · show G (Fin.snoc u s, t) = fibreCM (p u) s
          rw [hGbd (Fin.snoc u s) (hside u s hu) t, cubeToPinched_snoc] }⟩
  · -- the paths of `p₁` have image in `A`
    intro u s
    show G (Fin.snoc u s, 1) ∈ A
    exact hG1 (Fin.snoc u s)


/-- **The compression property of the pair `(Y, A)` in dimensions `≤ n+1` implies the vanishing of
the relative homotopy groups of the pair in degrees `≤ n`** — the implication (2) ⟹ (1) of tom
Dieck, *Algebraic Topology*, Proposition 6.7.5.

A based cube `p` in the homotopy fibre of `A ↪ Y` unwraps to the pinched map of pairs
`cubeToPinched a₀ j p`; the compression homotopy of that map (which is fixed on the whole boundary
of `I^{j+1}`, hence on the pinched part) curries back to a homotopy of based cubes from `p` to a
cube whose paths all lie in `A`; the latter is null-homotopic by shrinking the paths. -/
theorem subsingleton_relPi_of_compressRel (n : ℕ) (a₀ : ↥A)
    (hcomp : ∀ d, d ≤ n + 1 → CompressRel Y A d) :
    ∀ j, j ≤ n → Subsingleton (RelHomotopyGroup (setIncl A) a₀ j) := by
  intro j hj
  have hstep : ∀ p : GenLoop (Fin j) (homotopyFibre (setIncl A) a₀)
      (homotopyFibreBasepoint (setIncl A) a₀), GenLoop.Homotopic p GenLoop.const := by
    intro p
    obtain ⟨G, hG0, hGbd, hG1⟩ :=
      hcomp (j + 1) (by omega) (cubeToPinched a₀ j p) (cubeToPinched_bdry_mem a₀ j p)
    obtain ⟨p₁, hhom, hall⟩ := homotopyRel_cubeToPinched_of_compress a₀ j p G hG0 hGbd hG1
    exact GenLoop.Homotopic.trans hhom (homotopy_cube_homotopic_const_of_paths_mem a₀ j p₁ hall)
  refine ⟨fun a b => ?_⟩
  refine Quotient.inductionOn₂ a b (fun p q => Quotient.sound ?_)
  exact GenLoop.Homotopic.trans (hstep p) (GenLoop.Homotopic.symm (hstep q))

/-! ## Transport from the inclusion of the range of `attachIncl` to `attachIncl` -/

/-- **`attachIncl` is a homeomorphism onto its range.**  The map `Y → ↥(range attachIncl)`,
`y ↦ ⟨attachIncl y, y, rfl⟩`, is a bijection which is continuous and open (the latter is
`Work.RatHurewicz.attachIncl_isOpenMap_range`, i.e. the range of `attachIncl` carries the topology
of `Y`). -/
def rangeHomeo (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphere n, Y)) : Y ≃ₜ ↥(Set.range (attachIncl n Y ι f)) :=
  Equiv.toHomeomorphOfContinuousOpen
    { toFun := fun y => ⟨attachIncl n Y ι f y, y, rfl⟩
      invFun := fun a => a.2.choose
      left_inv := fun y =>
        AttachRange.attachIncl_injective n Y ι f
          (show attachIncl n Y ι f (⟨attachIncl n Y ι f y, y, rfl⟩ :
              ↥(Set.range (attachIncl n Y ι f))).2.choose = attachIncl n Y ι f y from
            (⟨attachIncl n Y ι f y, y, rfl⟩ :
              ↥(Set.range (attachIncl n Y ι f))).2.choose_spec)
      right_inv := fun a => Subtype.ext a.2.choose_spec }
    (Continuous.subtype_mk (attachIncl n Y ι f).continuous (fun y => ⟨y, rfl⟩))
    (attachIncl_isOpenMap_range n Y ι f)

/-- **The homotopy fibres of `attachIncl` and of the inclusion of its range are homeomorphic.**
Both are spaces of pairs `(point, path)` with the *same* path space (the two base points
`attachIncl y₀` and `setIncl (range attachIncl) ⟨attachIncl y₀, y₀, rfl⟩` are the same point of the
attachment), and the first coordinates are identified by `rangeHomeo`. -/
def attachFibreHomeo (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphere n, Y)) (y₀ : Y) :
    (homotopyFibre (attachIncl n Y ι f) y₀) ≃ₜ
    (homotopyFibre (setIncl (Set.range (attachIncl n Y ι f)))
      ⟨attachIncl n Y ι f y₀, y₀, rfl⟩) where
  toFun p :=
    ⟨(⟨attachIncl n Y ι f p.1.1, p.1.1, rfl⟩, p.1.2), by
      show (evalOne (attachCells n Y ι f) (attachIncl n Y ι f y₀)) p.1.2
        = setIncl (Set.range (attachIncl n Y ι f))
          ⟨attachIncl n Y ι f p.1.1, p.1.1, rfl⟩
      have h1 : (setIncl (Set.range (attachIncl n Y ι f))
          ⟨attachIncl n Y ι f p.1.1, p.1.1, rfl⟩ : attachCells n Y ι f)
          = attachIncl n Y ι f p.1.1 := rfl
      rw [h1]
      exact p.2⟩
  invFun q := ⟨((rangeHomeo n Y ι f).symm q.1.1, q.1.2), by
    show (evalOne (attachCells n Y ι f) (attachIncl n Y ι f y₀)) q.1.2
      = attachIncl n Y ι f ((rangeHomeo n Y ι f).symm q.1.1)
    have h1 : attachIncl n Y ι f ((rangeHomeo n Y ι f).symm q.1.1)
        = ((rangeHomeo n Y ι f) ((rangeHomeo n Y ι f).symm q.1.1) :
            attachCells n Y ι f) := rfl
    rw [h1, (rangeHomeo n Y ι f).apply_symm_apply q.1.1]
    exact q.2⟩
  left_inv p := by
    refine Subtype.ext (Prod.ext ?_ rfl)
    exact (rangeHomeo n Y ι f).symm_apply_apply p.1.1
  right_inv q := by
    refine Subtype.ext (Prod.ext (Subtype.ext ?_) rfl)
    exact congrArg Subtype.val ((rangeHomeo n Y ι f).apply_symm_apply q.1.1)
  continuous_toFun := Continuous.subtype_mk
    (Continuous.prodMk
      (Continuous.subtype_mk
        ((attachIncl n Y ι f).continuous.comp (continuous_fst.comp continuous_subtype_val))
        (fun p => ⟨p.1.1, rfl⟩))
      (continuous_snd.comp continuous_subtype_val))
    (fun p => by
      show (evalOne (attachCells n Y ι f) (attachIncl n Y ι f y₀)) p.1.2
        = setIncl (Set.range (attachIncl n Y ι f))
          ⟨attachIncl n Y ι f p.1.1, p.1.1, rfl⟩
      have h1 : (setIncl (Set.range (attachIncl n Y ι f))
          ⟨attachIncl n Y ι f p.1.1, p.1.1, rfl⟩ : attachCells n Y ι f)
          = attachIncl n Y ι f p.1.1 := rfl
      rw [h1]
      exact p.2)
  continuous_invFun := Continuous.subtype_mk
    (Continuous.prodMk
      ((rangeHomeo n Y ι f).symm.continuous.comp (continuous_fst.comp continuous_subtype_val))
      (continuous_snd.comp continuous_subtype_val))
    (fun q => by
      show (evalOne (attachCells n Y ι f) (attachIncl n Y ι f y₀)) q.1.2
        = attachIncl n Y ι f ((rangeHomeo n Y ι f).symm q.1.1)
      have h1 : attachIncl n Y ι f ((rangeHomeo n Y ι f).symm q.1.1)
          = ((rangeHomeo n Y ι f) ((rangeHomeo n Y ι f).symm q.1.1) :
              attachCells n Y ι f) := rfl
      rw [h1, (rangeHomeo n Y ι f).apply_symm_apply q.1.1]
      exact q.2)

/-- **The relative groups of `attachIncl` are those of the inclusion of its range.** -/
theorem subsingleton_relPi_attachIncl_of_range (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphere n, Y)) (y₀ : Y) (j : ℕ)
    (h : Subsingleton (RelHomotopyGroup
      (setIncl (Set.range (attachIncl n Y ι f))) ⟨attachIncl n Y ι f y₀, y₀, rfl⟩ j)) :
    Subsingleton (RelHomotopyGroup (attachIncl n Y ι f) y₀ j) := by
  have hbase : (attachFibreHomeo n Y ι f y₀) (homotopyFibreBasepoint (attachIncl n Y ι f) y₀)
      = homotopyFibreBasepoint (setIncl (Set.range (attachIncl n Y ι f)))
        ⟨attachIncl n Y ι f y₀, y₀, rfl⟩ := rfl
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    have hZ : Subsingleton (ZerothHomotopy (homotopyFibre
        (setIncl (Set.range (attachIncl n Y ι f))) ⟨attachIncl n Y ι f y₀, y₀, rfl⟩)) := by
      haveI := h
      refine ⟨fun u v => ?_⟩
      let ex := homotopyGroupEquivZerothHomotopyOfIsEmpty (N := Fin 0)
        (X := homotopyFibre (setIncl (Set.range (attachIncl n Y ι f)))
          ⟨attachIncl n Y ι f y₀, y₀, rfl⟩)
        (homotopyFibreBasepoint (setIncl (Set.range (attachIncl n Y ι f)))
          ⟨attachIncl n Y ι f y₀, y₀, rfl⟩)
      exact ex.symm.injective (Subsingleton.elim (ex.symm u) (ex.symm v))
    have hZ' : Subsingleton (ZerothHomotopy (homotopyFibre (attachIncl n Y ι f) y₀)) :=
      subsingleton_zerothHomotopy_of_homotopyEquiv (attachFibreHomeo n Y ι f y₀).toHomotopyEquiv hZ
    haveI := hZ'
    refine ⟨fun u v => ?_⟩
    let ex := homotopyGroupEquivZerothHomotopyOfIsEmpty (N := Fin 0)
      (X := homotopyFibre (attachIncl n Y ι f) y₀)
      (homotopyFibreBasepoint (attachIncl n Y ι f) y₀)
    exact ex.injective (Subsingleton.elim (ex u) (ex v))
  · haveI : Nonempty (Fin j) := ⟨⟨0, hj⟩⟩
    obtain ⟨me⟩ := Work.Stems.mulEquiv_of_homotopyEquiv (N := Fin j)
      (attachFibreHomeo n Y ι f y₀).toHomotopyEquiv (homotopyFibreBasepoint (attachIncl n Y ι f) y₀)
    have hbase' : (attachFibreHomeo n Y ι f y₀).toHomotopyEquiv.toFun
        (homotopyFibreBasepoint (attachIncl n Y ι f) y₀)
        = homotopyFibreBasepoint (setIncl (Set.range (attachIncl n Y ι f)))
          ⟨attachIncl n Y ι f y₀, y₀, rfl⟩ := hbase
    have h' : Subsingleton (HomotopyGroup (Fin j)
        (homotopyFibre (setIncl (Set.range (attachIncl n Y ι f)))
          ⟨attachIncl n Y ι f y₀, y₀, rfl⟩)
        ((attachFibreHomeo n Y ι f y₀).toHomotopyEquiv.toFun
          (homotopyFibreBasepoint (attachIncl n Y ι f) y₀))) :=
      hbase' ▸ h
    haveI := h'
    exact ⟨fun a b => me.injective (Subsingleton.elim (me a) (me b))⟩

end

end Work.RatHurewicz
