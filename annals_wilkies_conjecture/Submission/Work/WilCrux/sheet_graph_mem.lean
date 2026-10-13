/-
  `Work.WilCrux.sheet_graph_mem` — the definability of the coordinate graphs of the sheet of a
  cell (the `Ω`-bookkeeping step of `Work.WilCrux.IsolatedSheet`).

  Let `κ ⊆ ℝ^{m+N}` be an `Ω`-definable set (format `F`, degree `D`) with type word
  `w := word m N κ`, and let `T ⊆ ℝ^{m+nBand}` be the projection of `κ` onto the coordinates of
  the *band* levels (`selBand m w`), i.e. the set of "band coordinates" of points of `κ`.
  Let `φ` be any function on `T` whose `j`-th coordinate, on a point `v = p ∘ selBand m w`
  with `p ∈ κ`, is the `j`-th graph coordinate `p (Fin.natAdd m (graphIdx w j))` of `p`, and let
  `φ` be `0` off `T`.  Then each coordinate graph `graphOf (fun v => φ v j)` is `Ω`-definable,
  with format and degree bounded uniformly in `j`.

  The proof is the decomposition

      graphOf (fun v => φ v j) = sheetImg m w κ j ∪ junkSet T,

  where `sheetImg m w κ j` is the *coordinate image* of `κ` under the index map `sheetCoord m w j`
  (the band coordinates together with the single graph coordinate `graphIdx w j`, placed last)
  and `junkSet T` is the hyperplane `{y | y (Fin.last ·) = 0}` cut down to the parameters
  outside `T`.  The first piece is `Ω`-definable by `Work.WilG4b.projCoords_mem` (used here in
  the uniform form `projCoordsMem_uniform`, where the format and degree constants do not depend
  on the index map — this is what makes the bound uniform in `j`), the second by
  `prod_right`/`compl`/`hyp`; the two are glued with `Work.WilG1.Omega.union₂`.

  This file is complete.
-/
import Mathlib
import Submission.Work.WilCrux.SheetDefs
import Submission.Work.WilG4b.projCoords_mem
import Submission.Work.WilG4a.trivial_fallback

namespace Work.WilCrux

open WilkiesDesign

/-! ## 1. The index map of one graph coordinate, and the two pieces of the graph -/

/-- The index map of the `j`-th graph level of the sheet: the parameters and the band
coordinates, followed (in the last coordinate) by the `j`-th graph coordinate. -/
def sheetCoord (m : ℕ) {N : ℕ} (w : Fin N → CellType) (j : Fin (nGraph N w)) :
    Fin (m + nBand N w + 1) → Fin (m + N) :=
  Fin.addCases (selBand m w) (fun _ : Fin 1 => Fin.natAdd m (graphIdx w j))

@[simp] theorem sheetCoord_castAdd (m : ℕ) {N : ℕ} (w : Fin N → CellType)
    (j : Fin (nGraph N w)) (i : Fin (m + nBand N w)) :
    sheetCoord m w j (Fin.castAdd 1 i) = selBand m w i :=
  Fin.addCases_left _

@[simp] theorem sheetCoord_last (m : ℕ) {N : ℕ} (w : Fin N → CellType)
    (j : Fin (nGraph N w)) :
    sheetCoord m w j (Fin.last (m + nBand N w)) = Fin.natAdd m (graphIdx w j) := by
  rw [show Fin.last (m + nBand N w) = Fin.natAdd (m + nBand N w) (0 : Fin 1) from
    Fin.ext (by simp [Fin.natAdd])]
  exact Fin.addCases_right _

/-- The coordinate image of `κ` under `sheetCoord m w j`: the set of points `(v, y)` whose
`v`-part is a point of `T` (the band projection of `κ`) and whose last coordinate is the `j`-th
graph coordinate of the corresponding point of `κ`. -/
def sheetImg (m : ℕ) {N : ℕ} (w : Fin N → CellType) (κ : Set (Fin (m + N) → ℝ))
    (j : Fin (nGraph N w)) : Set (Fin (m + nBand N w + 1) → ℝ) :=
  {y | ∃ p : Fin (m + N) → ℝ, p ∈ κ ∧ y = p ∘ sheetCoord m w j}

/-- The junk part of the `j`-th coordinate graph: parameters outside `T`, with value `0`. -/
def junkSet (r : ℕ) (T : Set (Fin r → ℝ)) : Set (Fin (r + 1) → ℝ) :=
  {y | Fin.init y ∉ T ∧ y (Fin.last r) = 0}

/-! ## 2. The uniform coordinate-image lemma

`Work.WilG4b.projCoords_mem` quantifies the index map `e` *before* producing the format and the
degree polynomial, so its constants may a priori depend on `e`.  For the sheet we need them
uniform in `j`, hence in `e = sheetCoord m w j`; the proof of `projCoords_mem` in fact never uses
`e` to choose its constants, and serialises verbatim. -/

theorem projCoordsMem_uniform (S : WilkiesDesign.SOMin) (m N : ℕ) :
    ∃ (K : ℕ) (p : Polynomial ℕ), ∀ (e : Fin N → Fin m) (F D : ℕ) (X : Set (Fin m → ℝ)),
      X ∈ S.Ω F D m →
      {y : Fin N → ℝ | ∃ x : Fin m → ℝ, x ∈ X ∧ y = x ∘ e} ∈ S.Ω (F + K) (p.eval D) N := by
  refine ⟨N + (4 * (N + m) + 8) + 1 + m,
    Polynomial.C 2 * Polynomial.X + Polynomial.C (4 * N + 8), ?_⟩
  intro e F D X hX
  have hblk0 : Work.WilG4b.lastBlk m N X ∈ S.Ω (F + N) D (N + m) :=
    Work.WilG4b.lastBlk_mem (S := S) hX
  have hblk : Work.WilG4b.lastBlk m N X ∈
      S.Ω (F + (N + (4 * (N + m) + 8))) (D + (2 * N + 4)) (N + m) := by
    refine Work.WilG5.mem_mono hblk0 _ _ ?_ ?_ <;> omega
  have hrel0 : Work.WilG5.relSet (p := N) (q := m) e ∈
      S.Ω (4 * (N + m) + 8) (2 * N + 4) (N + m) :=
    Work.WilG5.relSet_mem (S := S) (p := N) (q := m) e
  have hrel : Work.WilG5.relSet (p := N) (q := m) e ∈
      S.Ω (F + (N + (4 * (N + m) + 8))) (D + (2 * N + 4)) (N + m) := by
    refine Work.WilG5.mem_mono hrel0 _ _ ?_ ?_ <;> omega
  have hJ := S.inter (fun _ : Fin 2 => D + (2 * N + 4))
    (fun i : Fin 2 => if i = 0 then Work.WilG4b.lastBlk m N X
      else Work.WilG5.relSet (p := N) (q := m) e)
    (by intro i
        fin_cases i
        · simpa using hblk
        · simpa using hrel)
  rw [show (∑ _ : Fin 2, (D + (2 * N + 4))) = 2 * D + (4 * N + 8) from by
    rw [Fin.sum_univ_two]; ring] at hJ
  rw [show (⋂ i : Fin 2,
      (if i = 0 then Work.WilG4b.lastBlk m N X
        else Work.WilG5.relSet (p := N) (q := m) e))
      = Work.WilG4b.lastBlk m N X ∩ Work.WilG5.relSet (p := N) (q := m) e from by
    ext z; simp [Fin.forall_fin_two]] at hJ
  have hproj := Work.WilG5.projN_mem (S := S) (n := N) m _ _ hJ
  have hset := Work.WilG4b.projN_lastBlk_rel (m := m) (N := N) e X
  rw [hset] at hproj
  have hp : (Polynomial.C 2 * Polynomial.X + Polynomial.C (4 * N + 8)).eval D
      = 2 * D + (4 * N + 8) := by simp
  rw [hp]
  refine Work.WilG5.mem_mono hproj _ _ ?_ le_rfl
  show F + (N + (4 * (N + m) + 8)) + 1 + m ≤ F + (N + (4 * (N + m) + 8) + 1 + m)
  omega

/-! ## 3. The graph is the union of the two pieces -/

theorem graphOf_eq_sheetImg_union_junk (m N : ℕ) (w : Fin N → CellType)
    (κ : Set (Fin (m + N) → ℝ)) (T : Set (Fin (m + nBand N w) → ℝ))
    (φ : (Fin (m + nBand N w) → ℝ) → Fin (nGraph N w) → ℝ)
    (hT : ∀ v, v ∈ T ↔ ∃ p : Fin (m + N) → ℝ, p ∈ κ ∧ v = p ∘ selBand m w)
    (hφT : ∀ (v : Fin (m + nBand N w) → ℝ), v ∈ T → ∀ (p : Fin (m + N) → ℝ), p ∈ κ →
      v = p ∘ selBand m w → ∀ j : Fin (nGraph N w),
        φ v j = p (Fin.natAdd m (graphIdx w j)))
    (hφ0 : ∀ (v : Fin (m + nBand N w) → ℝ), v ∉ T → ∀ j : Fin (nGraph N w), φ v j = 0)
    (j : Fin (nGraph N w)) :
    WilkiesDesign.graphOf (fun v => φ v j) =
      sheetImg m w κ j ∪ junkSet (m + nBand N w) T := by
  ext z
  constructor
  · intro hz
    have hz' : z (Fin.last (m + nBand N w)) = φ (Fin.init z) j := by
      simpa only [WilkiesDesign.graphOf, Set.mem_ofPred_eq] using hz
    by_cases hv : Fin.init z ∈ T
    · obtain ⟨p, hpκ, hpv⟩ := (hT (Fin.init z)).mp hv
      left
      refine ⟨p, hpκ, ?_⟩
      funext i
      refine Fin.addCases (motive := fun i => z i = (p ∘ sheetCoord m w j) i) ?_ ?_ i
      · intro i'
        have h1 : z (Fin.castAdd 1 i') = (Fin.init z) i' := rfl
        rw [h1, congrFun hpv i']
        simp
      · intro i''
        have hcast : Fin.natAdd (m + nBand N w) i'' = Fin.last (m + nBand N w) := by
          ext
          simp only [Fin.val_natAdd, Fin.val_last]
          have := i''.isLt
          omega
        rw [hcast, hz']
        simp only [Function.comp_apply, sheetCoord_last]
        exact hφT (Fin.init z) hv p hpκ hpv j
    · right
      refine ⟨hv, ?_⟩
      rw [hz']
      exact hφ0 (Fin.init z) hv j
  · intro hz
    rcases hz with hz | hz
    · obtain ⟨p, hpκ, hzeq⟩ := hz
      have hvEq : Fin.init z = p ∘ selBand m w := by
        funext i
        have h1 : (Fin.init z) i = z (Fin.castAdd 1 i) := rfl
        rw [h1, hzeq]
        simp
      have hvT : Fin.init z ∈ T := (hT (Fin.init z)).mpr ⟨p, hpκ, hvEq⟩
      show z (Fin.last (m + nBand N w)) = φ (Fin.init z) j
      rw [hφT (Fin.init z) hvT p hpκ hvEq j, hzeq]
      simp
    · obtain ⟨hzinit, hzlast⟩ := hz
      show z (Fin.last (m + nBand N w)) = φ (Fin.init z) j
      rw [hzlast, hφ0 (Fin.init z) hzinit j]

/-! ## 4. The target -/

theorem sheet_graph_mem (S : WilkiesDesign.SOMin) {m N F D : ℕ} {κ : Set (Fin (m + N) → ℝ)}
    (hκ : κ ∈ S.Ω F D (m + N))
    (T : Set (Fin (m + Work.WilCrux.nBand N (Work.WilCrux.word m N κ)) → ℝ))
    (φ : (Fin (m + Work.WilCrux.nBand N (Work.WilCrux.word m N κ)) → ℝ) →
      (Fin (Work.WilCrux.nGraph N (Work.WilCrux.word m N κ)) → ℝ))
    (hT : ∀ v, v ∈ T ↔ ∃ p : Fin (m + N) → ℝ, p ∈ κ ∧
      v = p ∘ Work.WilCrux.selBand m (Work.WilCrux.word m N κ))
    (hφT : ∀ (v : Fin (m + Work.WilCrux.nBand N (Work.WilCrux.word m N κ)) → ℝ), v ∈ T →
      ∀ (p : Fin (m + N) → ℝ), p ∈ κ → v = p ∘ Work.WilCrux.selBand m (Work.WilCrux.word m N κ) →
      ∀ j : Fin (Work.WilCrux.nGraph N (Work.WilCrux.word m N κ)),
        φ v j = p (Fin.natAdd m (Work.WilCrux.graphIdx (Work.WilCrux.word m N κ) j)))
    (hφ0 : ∀ v ∉ T, ∀ j, φ v j = 0) :
    ∃ (F' : ℕ) (b' : Polynomial ℕ), ∀ j : Fin (Work.WilCrux.nGraph N (Work.WilCrux.word m N κ)),
      WilkiesDesign.graphOf (fun v => φ v j) ∈
        S.Ω F' (b'.eval D) (m + Work.WilCrux.nBand N (Work.WilCrux.word m N κ) + 1) := by
  obtain ⟨K1, p1, h1⟩ := Work.WilG4b.projCoords_mem (S := S) (m := m + N)
    (e := selBand m (word m N κ))
  obtain ⟨K2, p2, h2⟩ := projCoordsMem_uniform (S := S) (m + N)
    (m + nBand N (word m N κ) + 1)
  refine ⟨max (F + K2) (max (F + K1 + 2) (m + nBand N (word m N κ) + 1) + 1),
    p2 + (p1 + 1), ?_⟩
  intro j
  -- the band projection `T` of `κ` is the coordinate image of `κ` under `selBand m w`
  have hTmem : T ∈ S.Ω (F + K1) (p1.eval D) (m + nBand N (word m N κ)) := by
    have hset : T = {y : Fin (m + nBand N (word m N κ)) → ℝ |
        ∃ x : Fin (m + N) → ℝ, x ∈ κ ∧ y = x ∘ selBand m (word m N κ)} := by
      ext v; exact hT v
    rw [hset]
    exact h1 F D κ hκ
  -- the coordinate image of `κ` under `sheetCoord m w j`
  have hG : sheetImg m (word m N κ) κ j ∈
      S.Ω (F + K2) (p2.eval D) (m + nBand N (word m N κ) + 1) :=
    h2 (sheetCoord m (word m N κ) j) F D κ hκ
  -- the junk part: `Tᶜ × {0}`
  have hH : junkSet (m + nBand N (word m N κ)) T ∈
      S.Ω (max (F + K1 + 2) (m + nBand N (word m N κ) + 1) + 1) ((p1 + 1).eval D)
        (m + nBand N (word m N κ) + 1) := by
    have hc : Tᶜ ∈ S.Ω (F + K1 + 1) (p1.eval D) (m + nBand N (word m N κ)) := S.compl hTmem
    have hA1 : {y : Fin (m + nBand N (word m N κ) + 1) → ℝ | Fin.init y ∈ Tᶜ} ∈
        S.Ω (F + K1 + 2) (p1.eval D) (m + nBand N (word m N κ) + 1) := by
      have := S.prod_right hc
      simpa using this
    have hA2e : WilkiesDesign.graphOf
        (fun _ : Fin (m + nBand N (word m N κ)) → ℝ => (0 : ℝ)) =
        {y : Fin (m + nBand N (word m N κ) + 1) → ℝ |
          y (Fin.last (m + nBand N (word m N κ))) = 0} := by
      ext y; simp [WilkiesDesign.graphOf]
    have hA2 : {y : Fin (m + nBand N (word m N κ) + 1) → ℝ |
        y (Fin.last (m + nBand N (word m N κ))) = 0} ∈
        S.Ω (m + nBand N (word m N κ) + 1) ((1 : Polynomial ℕ).eval D)
          (m + nBand N (word m N κ) + 1) := by
      rw [← hA2e]
      simpa using Work.WilG4a.graphOf_const_mem S (m + nBand N (word m N κ)) (0 : ℝ)
    exact Work.WilG1.Omega.inter₂ hA1 hA2
  have hunion := Work.WilG1.Omega.union₂ hG hH
  rw [graphOf_eq_sheetImg_union_junk m N (word m N κ) κ T φ hT hφT hφ0 j]
  exact hunion

end Work.WilCrux
