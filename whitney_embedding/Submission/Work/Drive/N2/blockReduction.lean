import Mathlib
import Submission.Work.Drive.Morse
import Submission.Work.Drive.N2.GoodDrawingFamily
import Submission.Work.Drive.N2.levelSeparatingMap_of_blocks

/-!
# The block-cover endgame of the compact `n = 2` movie, reduced to the windows

`Work.Drive.N2.levelSeparatingMap_of_blocks` supplies the value-axis bookkeeping of the compact
`n = 2` movie: it covers the value axis by the `4n` blocks

| index | block | values |
|---|---|---|
| `(j, 0)` | lower collar of `s j` | `(s j - η, s j - η/2)` |
| `(j, 1)` | window of `s j`      | `(s j - 5η/8, s j + 5η/8)` |
| `(j, 2)` | upper collar of `s j`| `(s j + η/2, s j + η)` |
| `(j, 3)` | band above `s j`     | `(s j + 3η/4, s (j+1) - 3η/4)` |

and reduces the target to a good drawing on every block together with the agreements of pairs of
*consecutive* blocks.

This file removes the bookkeeping from the residual: the three *collars/bands* of a critical value
are all contained in one **gap band** `gapValueBand s η j` (the `j`-th critical-free slab, cut back from
both ends by `η/2`), so

* the `3n` non-window block rows all follow from one good drawing per gap band, and
* all agreements of the block cover *except the two involving the window of a critical value* are
  automatically satisfied, because the two blocks involved are literally the same drawing.

The residual of the compact `n = 2` movie is therefore, at each critical value `s j`:

* a good drawing `gw j` of the window band `Ioo (s j - 5η/8) (s j + 5η/8)`, and
* the two *collar agreements*: on the lower collar `Ioo (s j - η) (s j - η/2)` the window piece
  agrees with the parked drawing of the gap band below `s j`, and on the upper collar
  `Ioo (s j + η/2) (s j + η)` it agrees with the parked drawing of the gap band above.

Nothing else about the windows is used: the agreement of the window with the band above it is
*not* required here (the block `(j, 3)` is the gap band of `s j`, not of `s (j+1)`), which is what
makes the two pieces of a component window separable by the sign of a coordinate.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff
open Set

/-- The critical-free "gap bands" attached to the critical values `s`: the `j`-th gap is the value
interval of the `j`-th critical-free slab `f ⁻¹' Ioo (s (j-1)) (s j)`, cut back from both ends by
`η/2` (with a sentinel below `s 0` for `j = 0`). -/
noncomputable def gapValueBand {n : ℕ} (s : Fin (n + 1) → ℝ) (η : ℝ) : Fin (n + 1) → Set ℝ :=
  Fin.cases (Set.Ioo (s 0 - η) (s 0 - η / 2))
    (fun i => Set.Ioo (s (Fin.castSucc i) + η / 2) (s (Fin.succ i) - η / 2))

@[simp] lemma gapValueBand_zero {n : ℕ} (s : Fin (n + 1) → ℝ) (η : ℝ) :
    gapValueBand s η 0 = Set.Ioo (s 0 - η) (s 0 - η / 2) := Fin.cases_zero

@[simp] lemma gapValueBand_succ {n : ℕ} (s : Fin (n + 1) → ℝ) (η : ℝ) (i : Fin n) :
    gapValueBand s η (Fin.succ i) = Set.Ioo (s (Fin.castSucc i) + η / 2) (s (Fin.succ i) - η / 2) :=
  Fin.cases_succ i

lemma blockSet_zero_subset_gapValueBand_castSucc {n : ℕ} {s : Fin (n + 1) → ℝ} {η : ℝ}
    (_hη : 0 < η) (hgap : ∀ j : Fin n, s (Fin.castSucc j) + 4 * η < s (Fin.succ j)) (j : Fin n) :
    blockSet s η (j, 0) ⊆ gapValueBand s η (Fin.castSucc j) := by
  rw [blockSet_zero]
  by_cases hj : Fin.castSucc j = 0
  · rw [hj, gapValueBand_zero]
  · have hpred : (Fin.pred (Fin.castSucc j) hj).succ = Fin.castSucc j := Fin.succ_pred _ hj
    have hb : gapValueBand s η (Fin.castSucc j) = Set.Ioo
        (s (Fin.castSucc (Fin.pred (Fin.castSucc j) hj)) + η / 2)
        (s (Fin.castSucc j) - η / 2) := by
      conv_lhs => rw [← hpred]
      rw [gapValueBand_succ, hpred]
    rw [hb]
    intro t ht
    obtain ⟨h1, h2⟩ := ht
    have hg := hgap (Fin.pred (Fin.castSucc j) hj)
    rw [hpred] at hg
    exact ⟨by linarith, by linarith⟩

lemma blockSet_two_subset_gapValueBand_succ {n : ℕ} {s : Fin (n + 1) → ℝ} {η : ℝ}
    (_hη : 0 < η) (hgap : ∀ j : Fin n, s (Fin.castSucc j) + 4 * η < s (Fin.succ j)) (j : Fin n) :
    blockSet s η (j, 2) ⊆ gapValueBand s η (Fin.succ j) := by
  rw [blockSet_two, gapValueBand_succ]
  intro t ht
  obtain ⟨h1, h2⟩ := ht
  have hg := hgap j
  exact ⟨by linarith, by linarith⟩

lemma blockSet_three_subset_gapValueBand_succ {n : ℕ} {s : Fin (n + 1) → ℝ} {η : ℝ}
    (_hη : 0 < η) (hgap : ∀ j : Fin n, s (Fin.castSucc j) + 4 * η < s (Fin.succ j)) (j : Fin n) :
    blockSet s η (j, 3) ⊆ gapValueBand s η (Fin.succ j) := by
  rw [blockSet_three, gapValueBand_succ]
  intro t ht
  obtain ⟨h1, h2⟩ := ht
  have hg := hgap j
  exact ⟨by linarith, by linarith⟩

open scoped Manifold ContDiff in
open Work.Drive.Morse in
/-- **The target from the window data of the block cover.**

The endgame of the compact `n = 2` movie only needs, at each of the `n` critical values `s j`:

* a good drawing `gw j` of the window band `Ioo (s j - 5η/8) (s j + 5η/8)` around it (the *model*
  piece, glued to the parked picture);
* the two *collar agreements*: on the lower collar `Ioo (s j - η) (s j - η/2)` the window piece
  agrees with the parked drawing `gG (j)` of the critical-free gap below `s j`, and on the upper
  collar `Ioo (s j + η/2) (s j + η)` it agrees with the parked drawing `gG (j+1)` of the gap above.

Everything else is bookkeeping: the parked drawings `gG j` of the `n + 1` critical-free gap bands
carry the remaining `3n` block rows, and the agreements of the block cover away from the windows are
automatic because the two blocks involved are the *same* parked drawing. -/
theorem levelSeparatingMap_of_collarWindows {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
    {n : ℕ} (hn : 0 < n) (f : M → ℝ) (hf : Work.Drive.Morse.IsMorseDistinct f)
    (s : Fin (n + 1) → ℝ) (hs : StrictMono s) (η : ℝ) (hη : 0 < η)
    (hlo : ∀ x : M, s 0 ≤ f x)
    (hhi : ∀ x : M, f x ≤ s (Fin.castSucc ⟨n - 1, by omega⟩))
    (hgap : ∀ j : Fin n, s (Fin.castSucc j) + 4 * η < s (Fin.succ j))
    (gG : Fin (n + 1) → M → EuclideanSpace ℝ (Fin 3))
    (hG : ∀ j : Fin (n + 1), GoodDrawingOn f (gapValueBand s η j) (gG j))
    (gw : Fin n → M → EuclideanSpace ℝ (Fin 3))
    (hw : ∀ j : Fin n, GoodDrawingOn f (blockSet s η (j, 1)) (gw j))
    (hLo : ∀ j : Fin n, ∀ x : M, f x ∈ blockSet s η (j, 0) → gw j x = gG (Fin.castSucc j) x)
    (hHi : ∀ j : Fin n, ∀ x : M, f x ∈ blockSet s η (j, 2) → gw j x = gG (Fin.succ j) x) :
    ∃ G : M → EuclideanSpace ℝ (Fin 3),
      ContMDiff (𝓡 2) (𝓡 3) ∞ G ∧
      (∀ x : M, ∀ v : TangentSpace (𝓡 2) x,
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 → mfderiv (𝓡 2) (𝓡 3) G x v = 0 → v = 0) ∧
      (∀ x y : M, f x = f y → G x = G y → x = y) := by
  classical
  let g : Fin n × Fin 4 → M → EuclideanSpace ℝ (Fin 3) := fun q =>
    if q.2 = 0 then gG (Fin.castSucc q.1) else if q.2 = 1 then gw q.1 else gG (Fin.succ q.1)
  have hg0 : ∀ j : Fin n, g (j, 0) = gG (Fin.castSucc j) := by intro j; simp [g]
  have hg1 : ∀ j : Fin n, g (j, 1) = gw j := by intro j; simp [g]
  have hg2 : ∀ j : Fin n, g (j, 2) = gG (Fin.succ j) := by intro j; simp [g]
  have hg3 : ∀ j : Fin n, g (j, 3) = gG (Fin.succ j) := by intro j; simp [g]
  have h4 : ∀ c : Fin 4, c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by
    intro c; fin_cases c <;> simp
  refine levelSeparatingMap_of_blocks hn f hf s hs η hη hlo hhi g ?_ hgap ?_
  · rintro ⟨j, c⟩
    rcases h4 c with hc | hc | hc | hc <;> subst hc
    · rw [hg0 j]
      exact (hG (Fin.castSucc j)).mono (blockSet_zero_subset_gapValueBand_castSucc hη hgap j)
    · rw [hg1 j]; exact hw j
    · rw [hg2 j]
      exact (hG (Fin.succ j)).mono (blockSet_two_subset_gapValueBand_succ hη hgap j)
    · rw [hg3 j]
      exact (hG (Fin.succ j)).mono (blockSet_three_subset_gapValueBand_succ hη hgap j)
  · rintro ⟨j, c⟩ ⟨j', c'⟩ hcon x hx hx'
    rcases h4 c with hc | hc | hc | hc <;> subst hc <;>
      rcases h4 c' with hc' | hc' | hc' | hc' <;> subst hc' <;>
      simp only [Consecutive, blkIndex] at hcon
    · exfalso; omega
    · rcases hcon with h | h
      · have hjj : j = j' := Fin.ext (by omega)
        subst hjj
        simp only [hg0, hg1]
        exact (hLo _ x hx).symm
      · exfalso; omega
    · exfalso; omega
    · rcases hcon with h | h
      · exfalso; omega
      · have hfin : (Fin.succ j' : Fin (n + 1)) = Fin.castSucc j :=
          Fin.ext (by simp only [Fin.val_succ, Fin.val_castSucc]; omega)
        rw [hg0 j, hg3 j', hfin]
    · rcases hcon with h | h
      · exfalso; omega
      · have hjj : j' = j := Fin.ext (by omega)
        subst hjj
        simp only [hg1, hg0]
        exact hLo _ x hx'
    · exfalso; omega
    · rcases hcon with h | h
      · have hjj : j = j' := Fin.ext (by omega)
        subst hjj
        simp only [hg1, hg2]
        exact hHi _ x hx'
      · exfalso; omega
    · exfalso; omega
    · exfalso; omega
    · rcases hcon with h | h
      · exfalso; omega
      · have hjj : j' = j := Fin.ext (by omega)
        subst hjj
        simp only [hg2, hg1]
        exact (hHi _ x hx).symm
    · exfalso; omega
    · rcases hcon with h | h
      · have hjj : j = j' := Fin.ext (by omega)
        subst hjj
        simp only [hg2, hg3]
      · exfalso; omega
    · rcases hcon with h | h
      · have hfin : (Fin.succ j : Fin (n + 1)) = Fin.castSucc j' :=
          Fin.ext (by simp only [Fin.val_succ, Fin.val_castSucc]; omega)
        rw [hg3 j, hg0 j', hfin]
      · exfalso; omega
    · exfalso; omega
    · rcases hcon with h | h
      · exfalso; omega
      · have hjj : j' = j := Fin.ext (by omega)
        subst hjj
        simp only [hg3, hg2]
    · exfalso; omega


open scoped Manifold ContDiff in
open Work.Drive.Morse in
/-- **The target from the windows of the block cover.**

The clean interface of the compact `n = 2` movie: it is enough to provide, at every critical value
`s j`,

* a good drawing `gw j` of the window band `Ioo (s j - 5η/8) (s j + 5η/8)`, and
* a single family `gG` of parked drawings of the critical-free gap bands, whose rows hold and which
  agrees with `gw j` on the two collars `Ioo (s j - η) (s j - η/2)` and `Ioo (s j + η/2) (s j + η)`.

The rows of `gG` on the gap bands are *satisfiable* without any use of the windows (they are the
transports of the pictures of one regular level per critical-free interval along the level flows
supplied by the target's own `hflow`); see `Work.Drive.N2.exists_gapBands`. -/
theorem levelSeparatingMap_of_windows {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
    {n : ℕ} (hn : 0 < n) (f : M → ℝ) (hf : Work.Drive.Morse.IsMorseDistinct f)
    (s : Fin (n + 1) → ℝ) (hs : StrictMono s) (η : ℝ) (hη : 0 < η)
    (hlo : ∀ x : M, s 0 ≤ f x)
    (hhi : ∀ x : M, f x ≤ s (Fin.castSucc ⟨n - 1, by omega⟩))
    (hgap : ∀ j : Fin n, s (Fin.castSucc j) + 4 * η < s (Fin.succ j))
    (gw : Fin n → M → EuclideanSpace ℝ (Fin 3))
    (hw : ∀ j : Fin n, GoodDrawingOn f (blockSet s η (j, 1)) (gw j))
    (hglue : ∃ gG : Fin (n + 1) → M → EuclideanSpace ℝ (Fin 3),
      (∀ j : Fin (n + 1), GoodDrawingOn f (gapValueBand s η j) (gG j)) ∧
      (∀ (j : Fin n) (x : M), f x ∈ blockSet s η (j, 0) →
        gw j x = gG (Fin.castSucc j) x) ∧
      (∀ (j : Fin n) (x : M), f x ∈ blockSet s η (j, 2) →
        gw j x = gG (Fin.succ j) x)) :
    ∃ G : M → EuclideanSpace ℝ (Fin 3),
      ContMDiff (𝓡 2) (𝓡 3) ∞ G ∧
      (∀ x : M, ∀ v : TangentSpace (𝓡 2) x,
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 → mfderiv (𝓡 2) (𝓡 3) G x v = 0 → v = 0) ∧
      (∀ x y : M, f x = f y → G x = G y → x = y) := by
  obtain ⟨gG, h1, h2, h3⟩ := hglue
  exact levelSeparatingMap_of_collarWindows hn f hf s hs η hη hlo hhi hgap gG h1 gw hw h2 h3

/-- **The residual obligation of the compact `n = 2` movie**, as a single predicate.

At each of the `n` critical values `s j` one produces the *window piece* `gw j` (a good drawing of the
window band around `s j`) and the *parked drawings* `gG` of the `n + 1` critical-free gap bands, with
the rows of both and the two *collar agreements*.  `Work.Drive.N2.levelSeparatingMap_of_windows`
turns this into the target's conclusion; `Work.Drive.N2.exists_gapBands` shows that the rows of `gG`
alone are free (they are transports of level pictures along the level flows of the target's own
`hflow`), so the mathematical content of `HasWindowData` is the window pieces and their two collar
agreements. -/
def HasWindowData {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
    {n : ℕ} (f : M → ℝ) (s : Fin (n + 1) → ℝ) (η : ℝ) : Prop :=
  ∃ (gw : Fin n → M → EuclideanSpace ℝ (Fin 3))
    (gG : Fin (n + 1) → M → EuclideanSpace ℝ (Fin 3)),
    (∀ j : Fin n, GoodDrawingOn f (blockSet s η (j, 1)) (gw j)) ∧
    (∀ j : Fin (n + 1), GoodDrawingOn f (gapValueBand s η j) (gG j)) ∧
    (∀ (j : Fin n) (x : M), f x ∈ blockSet s η (j, 0) → gw j x = gG (Fin.castSucc j) x) ∧
    (∀ (j : Fin n) (x : M), f x ∈ blockSet s η (j, 2) → gw j x = gG (Fin.succ j) x)

open scoped Manifold ContDiff in
open Work.Drive.Morse in
/-- **The target from `HasWindowData`.** -/
theorem levelSeparatingMap_of_hasWindowData {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
    {n : ℕ} (hn : 0 < n) (f : M → ℝ) (hf : Work.Drive.Morse.IsMorseDistinct f)
    (s : Fin (n + 1) → ℝ) (hs : StrictMono s) (η : ℝ) (hη : 0 < η)
    (hlo : ∀ x : M, s 0 ≤ f x)
    (hhi : ∀ x : M, f x ≤ s (Fin.castSucc ⟨n - 1, by omega⟩))
    (hgap : ∀ j : Fin n, s (Fin.castSucc j) + 4 * η < s (Fin.succ j))
    (h : HasWindowData f s η) :
    ∃ G : M → EuclideanSpace ℝ (Fin 3),
      ContMDiff (𝓡 2) (𝓡 3) ∞ G ∧
      (∀ x : M, ∀ v : TangentSpace (𝓡 2) x,
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 → mfderiv (𝓡 2) (𝓡 3) G x v = 0 → v = 0) ∧
      (∀ x y : M, f x = f y → G x = G y → x = y) := by
  obtain ⟨gw, gG, h1, h2, h3, h4⟩ := h
  exact levelSeparatingMap_of_windows hn f hf s hs η hη hlo hhi hgap gw h1 ⟨gG, h2, h3, h4⟩

open scoped Manifold ContDiff in
open Work.Drive.Morse in
/-- **The target from the collar form of the window data.**

The collar agreements stated as *equalities of functions* on the whole gap bands: the window piece of
`s j` coincides with the parked drawing of the gap band below `s j` on that entire band, and with the
parked drawing of the gap band above `s j` on that entire band.  This is the form in which a
construction of the windows naturally produces the agreements (one defines the window piece off the
critical value to *be* the parked drawing). -/
theorem levelSeparatingMap_of_windowCollars {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
    {n : ℕ} (hn : 0 < n) (f : M → ℝ) (hf : Work.Drive.Morse.IsMorseDistinct f)
    (s : Fin (n + 1) → ℝ) (hs : StrictMono s) (η : ℝ) (hη : 0 < η)
    (hlo : ∀ x : M, s 0 ≤ f x)
    (hhi : ∀ x : M, f x ≤ s (Fin.castSucc ⟨n - 1, by omega⟩))
    (hgap : ∀ j : Fin n, s (Fin.castSucc j) + 4 * η < s (Fin.succ j))
    (gw : Fin n → M → EuclideanSpace ℝ (Fin 3))
    (gG : Fin (n + 1) → M → EuclideanSpace ℝ (Fin 3))
    (hw : ∀ j : Fin n, GoodDrawingOn f (blockSet s η (j, 1)) (gw j))
    (hG : ∀ j : Fin (n + 1), GoodDrawingOn f (gapValueBand s η j) (gG j))
    (heqLo : ∀ (j : Fin n) (x : M), f x ∈ gapValueBand s η (Fin.castSucc j) →
      gw j x = gG (Fin.castSucc j) x)
    (heqHi : ∀ (j : Fin n) (x : M), f x ∈ gapValueBand s η (Fin.succ j) →
      gw j x = gG (Fin.succ j) x) :
    ∃ G : M → EuclideanSpace ℝ (Fin 3),
      ContMDiff (𝓡 2) (𝓡 3) ∞ G ∧
      (∀ x : M, ∀ v : TangentSpace (𝓡 2) x,
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 → mfderiv (𝓡 2) (𝓡 3) G x v = 0 → v = 0) ∧
      (∀ x y : M, f x = f y → G x = G y → x = y) := by
  refine levelSeparatingMap_of_collarWindows hn f hf s hs η hη hlo hhi hgap gG hG gw hw ?_ ?_
  · intro j x hx
    exact heqLo j x (blockSet_zero_subset_gapValueBand_castSucc hη hgap j hx)
  · intro j x hx
    exact heqHi j x (blockSet_two_subset_gapValueBand_succ hη hgap j hx)

end Work.Drive.N2
