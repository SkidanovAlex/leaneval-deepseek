import Mathlib
import Submission.Work.OddBound.polygonValue.balancing.Defs
import Submission.Work.OddBound.polygonValue.balancing.Book
import Submission.Work.OddBound.polygonValue.balancing.continuousOn_sideLen
import Submission.Work.OddBound.polygonValue.balancing.distLeCurveLengthOfContMDiffOn
import Submission.Work.OddBound.polygonValue.edist_eq_ofReal_riemannianDist

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval

namespace Work.OddBound.polygonValue.balancing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
  [IsManifold I (WithTop.some (⊤ : ENat)) M]
  [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I (WithTop.some (⊤ : ENat)) E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]

section Aux

variable {p : M} {N : ℕ} {w : ℝ → Fin (N - 1) → M} {S : Fin N → ℝ → ℝ → M}

/-! ## Bounds in the arclength variable -/

/-- **The side index of an arclength strictly inside the side `m` is `m`.** -/
theorem gIdx_eq_of_lt_cumLen' {τ A : ℝ} {m : ℕ}
    (hm : m + 1 ≤ N) (hA0 : cumLen (I := I) p w τ m ≤ A)
    (hA1 : A < cumLen (I := I) p w τ (m + 1)) :
    gIdx (I := I) p w τ A = m := by
  have hset : (Finset.range N).filter (fun j => cumLen (I := I) p w τ j ≤ A)
      = Finset.range (m + 1) := by
    apply Finset.ext
    intro j
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_range]
    constructor
    · rintro ⟨hjN, hj⟩
      by_contra hcon
      have hmj : m + 1 ≤ j := by omega
      have h2 : cumLen (I := I) p w τ (m + 1) ≤ cumLen (I := I) p w τ j :=
        cumLen_mono (I := I) p w τ hmj
      linarith
    · intro hj
      exact ⟨by omega, le_trans (cumLen_mono (I := I) p w τ (Nat.le_of_lt_succ hj)) hA0⟩
  rw [gIdx_def, hset, Finset.card_range]
  omega

/-- **On a side the broken geodesic is the side curve.**  For `A` between the two breakpoints of
the side `i` (inclusive), `gPt τ A` is `S i` at the (clamped) fraction of the side. -/
theorem gPt_eq_side' {τ A : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (hSsm : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 (fun r : ℝ => S i r τ)
        (Set.Icc (0 : ℝ) 1))
    (hS0 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 0 τ = Work.OddBound.gonVert p (w τ) (i : ℕ))
    (hS1 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 1 τ = Work.OddBound.gonVert p (w τ) ((i : ℕ) + 1))
    (hSlen : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 → ∀ a b : ℝ,
      0 ≤ a → a ≤ b → b ≤ 1 →
      Submission.Length.curveLength (I := I) (fun r : ℝ => S i r τ) a b
        = (b - a) * Work.OddBound.gonSideLen (I := I) p (w τ) (i : ℕ))
    (hN : 0 < N) {i : Fin N} (hA0 : cumLen (I := I) p w τ (i : ℕ) ≤ A)
    (hA1 : A ≤ cumLen (I := I) p w τ ((i : ℕ) + 1)) :
    gPt (I := I) p hN w S τ A
      = S i (clamp01 ((A - cumLen (I := I) p w τ (i : ℕ))
          / sideLen (I := I) p w τ (i : ℕ))) τ := by
  rcases lt_or_eq_of_le hA1 with hlt | heq
  · have hidx : gIdx (I := I) p w τ A = (i : ℕ) :=
      gIdx_eq_of_lt_cumLen' (I := I) (by omega) hA0 hlt
    have hfin : gFin (I := I) p hN w τ A = i := by
      apply Fin.ext
      rw [gFin_val, hidx]
    rw [gPt_def, hfin, gPrm_def, hidx]
  · rw [heq]
    rcases eq_or_lt_of_le (sideLen_nonneg (I := I) p w τ (i : ℕ)) with h0 | hpos
    · have h0' : sideLen (I := I) p w τ (i : ℕ) = 0 := h0.symm
      have hv : Work.OddBound.gonVert p (w τ) (i : ℕ)
          = Work.OddBound.gonVert p (w τ) ((i : ℕ) + 1) :=
        eq_gonVert_of_sideLen_eq_zero (I := I) hτ hSsm hS0 hS1 hSlen (k := (i : ℕ)) (by omega) h0'
      rw [h0', div_zero, clamp01_eq_zero_of_nonpos le_rfl, hS0 i τ hτ,
        gPt_cumLen_eq_gonVert (I := I) hτ hSsm hS0 hS1 hSlen hN (by omega : (i : ℕ) + 1 ≤ N)]
      exact hv.symm
    · have hcum : cumLen (I := I) p w τ ((i : ℕ) + 1)
          = cumLen (I := I) p w τ (i : ℕ) + sideLen (I := I) p w τ (i : ℕ) :=
        cumLen_succ (I := I) p w τ (i : ℕ)
      have hq : (cumLen (I := I) p w τ ((i : ℕ) + 1) - cumLen (I := I) p w τ (i : ℕ))
          / sideLen (I := I) p w τ (i : ℕ) = 1 := by
        rw [hcum, add_sub_cancel_left, div_self (ne_of_gt hpos)]
      rw [hq, clamp01_eq_one_of_one_le le_rfl, hS1 i τ hτ,
        gPt_cumLen_eq_gonVert (I := I) hτ hSsm hS0 hS1 hSlen hN (by omega : (i : ℕ) + 1 ≤ N)]

/-- **The single side bound**: two arclengths on the same side are at distance at most their
difference. -/
theorem gPt_side_dist_le {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (hSsm : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 (fun r : ℝ => S i r τ)
        (Set.Icc (0 : ℝ) 1))
    (hS0 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 0 τ = Work.OddBound.gonVert p (w τ) (i : ℕ))
    (hS1 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 1 τ = Work.OddBound.gonVert p (w τ) ((i : ℕ) + 1))
    (hSlen : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 → ∀ a b : ℝ,
      0 ≤ a → a ≤ b → b ≤ 1 →
      Submission.Length.curveLength (I := I) (fun r : ℝ => S i r τ) a b
        = (b - a) * Work.OddBound.gonSideLen (I := I) p (w τ) (i : ℕ))
    (hN : 0 < N) (i : Fin N) {x y : ℝ}
    (hx0 : cumLen (I := I) p w τ (i : ℕ) ≤ x)
    (hx1 : x ≤ cumLen (I := I) p w τ ((i : ℕ) + 1))
    (hy0 : cumLen (I := I) p w τ (i : ℕ) ≤ y)
    (hy1 : y ≤ cumLen (I := I) p w τ ((i : ℕ) + 1))
    (hxy : x ≤ y) :
    Submission.Distance.riemannianDist (I := I) (gPt (I := I) p hN w S τ x)
      (gPt (I := I) p hN w S τ y) ≤ y - x := by
  rcases eq_or_lt_of_le (sideLen_nonneg (I := I) p w τ (i : ℕ)) with h0 | hpos
  · have hcum : cumLen (I := I) p w τ ((i : ℕ) + 1) = cumLen (I := I) p w τ (i : ℕ) := by
      rw [cumLen_succ (I := I) p w τ (i : ℕ), ← h0]
      ring
    have hxe : x = cumLen (I := I) p w τ (i : ℕ) :=
      le_antisymm (le_trans hx1 (le_of_eq hcum)) hx0
    have hye : y = cumLen (I := I) p w τ (i : ℕ) :=
      le_antisymm (le_trans hy1 (le_of_eq hcum)) hy0
    rw [hxe, hye, sub_self]
    exact le_of_eq (Submission.Distance.riemannianDist_self (I := I) _)
  · set rx : ℝ :=
      clamp01 ((x - cumLen (I := I) p w τ (i : ℕ)) / sideLen (I := I) p w τ (i : ℕ)) with hrx
    set ry : ℝ :=
      clamp01 ((y - cumLen (I := I) p w τ (i : ℕ)) / sideLen (I := I) p w τ (i : ℕ)) with hry
    have hwx : (x - cumLen (I := I) p w τ (i : ℕ)) / sideLen (I := I) p w τ (i : ℕ)
        ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg (by linarith) hpos.le
      · rw [div_le_one hpos]
        have hsub := sideLen_eq_sub (I := I) p w τ (i : ℕ)
        linarith
    have hwy : (y - cumLen (I := I) p w τ (i : ℕ)) / sideLen (I := I) p w τ (i : ℕ)
        ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg (by linarith) hpos.le
      · rw [div_le_one hpos]
        have hsub := sideLen_eq_sub (I := I) p w τ (i : ℕ)
        linarith
    have hrx' : rx = (x - cumLen (I := I) p w τ (i : ℕ)) / sideLen (I := I) p w τ (i : ℕ) :=
      clamp01_eq_self hwx.1 hwx.2
    have hry' : ry = (y - cumLen (I := I) p w τ (i : ℕ)) / sideLen (I := I) p w τ (i : ℕ) :=
      clamp01_eq_self hwy.1 hwy.2
    have hrxy : rx ≤ ry := by
      rw [hrx', hry']
      exact div_le_div_of_nonneg_right (by linarith) hpos.le
    have hmemx : rx ∈ Set.Icc (0 : ℝ) 1 := ⟨clamp01_nonneg _, clamp01_le_one _⟩
    have hmem : ry ∈ Set.Icc (0 : ℝ) 1 := ⟨clamp01_nonneg _, clamp01_le_one _⟩
    have hside := distLeCurveLengthOfContMDiffOn (I := I) (hSsm i τ hτ)
      (a := rx) (b := ry) hmemx.1 hrxy hmem.2
    rw [hSlen i τ hτ rx ry hmemx.1 hrxy hmem.2] at hside
    have hside' : Submission.Distance.riemannianDist (I := I) (S i rx τ) (S i ry τ)
        ≤ (ry - rx) * sideLen (I := I) p w τ (i : ℕ) := hside
    have key : (ry - rx) * sideLen (I := I) p w τ (i : ℕ) = y - x := by
      rw [hrx', hry']
      field_simp
      ring
    rw [key] at hside'
    rw [gPt_eq_side' (I := I) hτ hSsm hS0 hS1 hSlen hN hx0 hx1,
      gPt_eq_side' (I := I) hτ hSsm hS0 hS1 hSlen hN hy0 hy1, ← hrx, ← hry]
    exact hside'

/-- **The vertex chain bound**: two vertices of the slice are at distance at most the arclength
between them. -/
theorem gonVert_dist_le_cumLen {τ : ℝ} {k l : ℕ} (hkl : k ≤ l) :
    Submission.Distance.riemannianDist (I := I) (Work.OddBound.gonVert p (w τ) k)
      (Work.OddBound.gonVert p (w τ) l) ≤ cumLen (I := I) p w τ l - cumLen (I := I) p w τ k := by
  induction l, hkl using Nat.le_induction with
  | base => rw [sub_self, Submission.Distance.riemannianDist_self]
  | succ l hl ih =>
    have hside : Submission.Distance.riemannianDist (I := I)
        (Work.OddBound.gonVert p (w τ) l) (Work.OddBound.gonVert p (w τ) (l + 1))
        = sideLen (I := I) p w τ l := rfl
    calc Submission.Distance.riemannianDist (I := I) (Work.OddBound.gonVert p (w τ) k)
          (Work.OddBound.gonVert p (w τ) (l + 1))
        ≤ Submission.Distance.riemannianDist (I := I) (Work.OddBound.gonVert p (w τ) k)
            (Work.OddBound.gonVert p (w τ) l)
          + Submission.Distance.riemannianDist (I := I) (Work.OddBound.gonVert p (w τ) l)
            (Work.OddBound.gonVert p (w τ) (l + 1)) :=
          riemannianDist_triangle_pathConnected (I := I) _ _ _
      _ ≤ (cumLen (I := I) p w τ l - cumLen (I := I) p w τ k) + sideLen (I := I) p w τ l := by
          rw [hside]
          linarith
      _ = cumLen (I := I) p w τ (l + 1) - cumLen (I := I) p w τ k := by
          rw [cumLen_succ (I := I) p w τ l]
          ring

/-- **The lower endpoint bound**: the point of the broken geodesic at arclength `a` is within
`a - cumLen τ (gIdx τ a)` of the vertex `gIdx τ a`. -/
theorem gPt_dist_gIdx_le {τ A : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (hSsm : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 (fun r : ℝ => S i r τ)
        (Set.Icc (0 : ℝ) 1))
    (hS0 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 0 τ = Work.OddBound.gonVert p (w τ) (i : ℕ))
    (hS1 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 1 τ = Work.OddBound.gonVert p (w τ) ((i : ℕ) + 1))
    (hSlen : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 → ∀ a b : ℝ,
      0 ≤ a → a ≤ b → b ≤ 1 →
      Submission.Length.curveLength (I := I) (fun r : ℝ => S i r τ) a b
        = (b - a) * Work.OddBound.gonSideLen (I := I) p (w τ) (i : ℕ))
    (hN : 0 < N) (ha0 : 0 ≤ A) (haT : A ≤ totLen (I := I) p w τ) :
    Submission.Distance.riemannianDist (I := I) (gPt (I := I) p hN w S τ A)
      (Work.OddBound.gonVert p (w τ) (gIdx (I := I) p w τ A))
      ≤ A - cumLen (I := I) p w τ (gIdx (I := I) p w τ A) := by
  set m : ℕ := gIdx (I := I) p w τ A with hm
  have hmN : m < N := gIdx_lt (I := I) p hN w τ A
  have hlow : cumLen (I := I) p w τ m ≤ A := cumLen_gIdx_le (I := I) p hN w τ A ha0
  have hhigh : A ≤ cumLen (I := I) p w τ (m + 1) := by
    have h := le_cumLen_gIdx_succ (I := I) p hN w τ A haT
    rwa [← hm] at h
  have hv : Work.OddBound.gonVert p (w τ) m
      = gPt (I := I) p hN w S τ (cumLen (I := I) p w τ m) :=
    (gPt_cumLen_eq_gonVert (I := I) hτ hSsm hS0 hS1 hSlen hN (by omega)).symm
  rw [hv]
  rw [show Submission.Distance.riemannianDist (I := I) (gPt (I := I) p hN w S τ A)
        (gPt (I := I) p hN w S τ (cumLen (I := I) p w τ m))
      = Submission.Distance.riemannianDist (I := I)
        (gPt (I := I) p hN w S τ (cumLen (I := I) p w τ m)) (gPt (I := I) p hN w S τ A)
      from riemannianDist_comm_toReal (I := I) _ _]
  exact gPt_side_dist_le (I := I) hτ hSsm hS0 hS1 hSlen hN (i := ⟨m, hmN⟩)
    (x := cumLen (I := I) p w τ m) (y := A) (le_refl _)
    (cumLen_mono (I := I) p w τ (Nat.le_succ m)) hlow hhigh hlow

/-- **The upper endpoint bound**: the point of the broken geodesic at arclength `a` is within
`cumLen τ (gIdx τ a + 1) - a` of the next vertex. -/
theorem gPt_dist_gIdx_succ_le {τ A : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (hSsm : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 (fun r : ℝ => S i r τ)
        (Set.Icc (0 : ℝ) 1))
    (hS0 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 0 τ = Work.OddBound.gonVert p (w τ) (i : ℕ))
    (hS1 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 1 τ = Work.OddBound.gonVert p (w τ) ((i : ℕ) + 1))
    (hSlen : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 → ∀ a b : ℝ,
      0 ≤ a → a ≤ b → b ≤ 1 →
      Submission.Length.curveLength (I := I) (fun r : ℝ => S i r τ) a b
        = (b - a) * Work.OddBound.gonSideLen (I := I) p (w τ) (i : ℕ))
    (hN : 0 < N) (ha0 : 0 ≤ A) (haT : A ≤ totLen (I := I) p w τ) :
    Submission.Distance.riemannianDist (I := I) (gPt (I := I) p hN w S τ A)
      (Work.OddBound.gonVert p (w τ) (gIdx (I := I) p w τ A + 1))
      ≤ cumLen (I := I) p w τ (gIdx (I := I) p w τ A + 1) - A := by
  set m : ℕ := gIdx (I := I) p w τ A with hm
  have hmN : m < N := gIdx_lt (I := I) p hN w τ A
  have hlow : cumLen (I := I) p w τ m ≤ A := cumLen_gIdx_le (I := I) p hN w τ A ha0
  have hhigh : A ≤ cumLen (I := I) p w τ (m + 1) := by
    have h := le_cumLen_gIdx_succ (I := I) p hN w τ A haT
    rwa [← hm] at h
  have hv : Work.OddBound.gonVert p (w τ) (m + 1)
      = gPt (I := I) p hN w S τ (cumLen (I := I) p w τ (m + 1)) :=
    (gPt_cumLen_eq_gonVert (I := I) hτ hSsm hS0 hS1 hSlen hN (by omega)).symm
  rw [show gIdx (I := I) p w τ A + 1 = m + 1 from by rw [← hm], hv]
  exact gPt_side_dist_le (I := I) hτ hSsm hS0 hS1 hSlen hN ⟨m, hmN⟩ hlow hhigh
    (cumLen_mono (I := I) p w τ (Nat.le_succ m)) (le_refl _) hhigh

/-- **Same-slice bound.**  Two points of the broken geodesic of the same slice are at distance at
most their arclength difference. -/
theorem gPt_dist_le_of_le {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (hSsm : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 (fun r : ℝ => S i r τ)
        (Set.Icc (0 : ℝ) 1))
    (hS0 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 0 τ = Work.OddBound.gonVert p (w τ) (i : ℕ))
    (hS1 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 1 τ = Work.OddBound.gonVert p (w τ) ((i : ℕ) + 1))
    (hSlen : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 → ∀ a b : ℝ,
      0 ≤ a → a ≤ b → b ≤ 1 →
      Submission.Length.curveLength (I := I) (fun r : ℝ => S i r τ) a b
        = (b - a) * Work.OddBound.gonSideLen (I := I) p (w τ) (i : ℕ))
    (hN : 0 < N) {x y : ℝ} (hx0 : 0 ≤ x) (hxT : x ≤ totLen (I := I) p w τ)
    (hy0 : 0 ≤ y) (hyT : y ≤ totLen (I := I) p w τ) (hxy : x ≤ y) :
    Submission.Distance.riemannianDist (I := I) (gPt (I := I) p hN w S τ x)
      (gPt (I := I) p hN w S τ y) ≤ y - x := by
  rcases eq_or_lt_of_le hxy with h | hlt
  · rw [h, sub_self]
    exact le_of_eq (Submission.Distance.riemannianDist_self (I := I) _)
  · set m : ℕ := gIdx (I := I) p w τ x with hm
    set m' : ℕ := gIdx (I := I) p w τ y with hm'
    have hmN : m < N := gIdx_lt (I := I) p hN w τ x
    have hm'N : m' < N := gIdx_lt (I := I) p hN w τ y
    have hxlo : cumLen (I := I) p w τ m ≤ x := cumLen_gIdx_le (I := I) p hN w τ x hx0
    have hxhi : x ≤ cumLen (I := I) p w τ (m + 1) := by
      have h := le_cumLen_gIdx_succ (I := I) p hN w τ x hxT
      rwa [← hm] at h
    have hylo : cumLen (I := I) p w τ m' ≤ y := cumLen_gIdx_le (I := I) p hN w τ y hy0
    have hyhi : y ≤ cumLen (I := I) p w τ (m' + 1) := by
      have h := le_cumLen_gIdx_succ (I := I) p hN w τ y hyT
      rwa [← hm'] at h
    have hmm' : m ≤ m' := by
      by_contra hcon
      have h1 : m' + 1 ≤ m := by omega
      have h2 : cumLen (I := I) p w τ (m' + 1) ≤ cumLen (I := I) p w τ m :=
        cumLen_mono (I := I) p w τ h1
      linarith
    rcases eq_or_lt_of_le hmm' with heq | hlt2
    · refine gPt_side_dist_le (I := I) hτ hSsm hS0 hS1 hSlen hN (i := ⟨m, hmN⟩)
        (x := x) (y := y) hxlo hxhi ?_ ?_ hlt.le
      · rw [← heq] at hylo; exact hylo
      · rw [← heq] at hyhi; exact hyhi
    · have htri1 : Submission.Distance.riemannianDist (I := I) (gPt (I := I) p hN w S τ x)
            (gPt (I := I) p hN w S τ y)
          ≤ Submission.Distance.riemannianDist (I := I) (gPt (I := I) p hN w S τ x)
              (Work.OddBound.gonVert p (w τ) (m + 1))
            + Submission.Distance.riemannianDist (I := I) (Work.OddBound.gonVert p (w τ) (m + 1))
              (gPt (I := I) p hN w S τ y) :=
        riemannianDist_triangle_pathConnected (I := I) _ _ _
      have htri2 : Submission.Distance.riemannianDist (I := I)
            (Work.OddBound.gonVert p (w τ) (m + 1)) (gPt (I := I) p hN w S τ y)
          ≤ Submission.Distance.riemannianDist (I := I) (Work.OddBound.gonVert p (w τ) (m + 1))
              (Work.OddBound.gonVert p (w τ) m')
            + Submission.Distance.riemannianDist (I := I) (Work.OddBound.gonVert p (w τ) m')
              (gPt (I := I) p hN w S τ y) :=
        riemannianDist_triangle_pathConnected (I := I) _ _ _
      have hP4 : Submission.Distance.riemannianDist (I := I) (gPt (I := I) p hN w S τ x)
          (Work.OddBound.gonVert p (w τ) (m + 1)) ≤ cumLen (I := I) p w τ (m + 1) - x := by
        have h := gPt_dist_gIdx_succ_le (I := I) hτ hSsm hS0 hS1 hSlen hN hx0 hxT
        rwa [← hm] at h
      have hP2 : Submission.Distance.riemannianDist (I := I) (Work.OddBound.gonVert p (w τ) (m + 1))
          (Work.OddBound.gonVert p (w τ) m')
          ≤ cumLen (I := I) p w τ m' - cumLen (I := I) p w τ (m + 1) :=
        gonVert_dist_le_cumLen (I := I) (by omega)
      have hP3 : Submission.Distance.riemannianDist (I := I) (Work.OddBound.gonVert p (w τ) m')
          (gPt (I := I) p hN w S τ y) ≤ y - cumLen (I := I) p w τ m' := by
        have h := gPt_dist_gIdx_le (I := I) hτ hSsm hS0 hS1 hSlen hN hy0 hyT
        rw [← hm'] at h
        rwa [riemannianDist_comm_toReal (I := I)] at h
      linarith

/-- **Same-slice bound, absolute value form.** -/
theorem gPt_dist_le_abs {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (hSsm : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 (fun r : ℝ => S i r τ)
        (Set.Icc (0 : ℝ) 1))
    (hS0 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 0 τ = Work.OddBound.gonVert p (w τ) (i : ℕ))
    (hS1 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 1 τ = Work.OddBound.gonVert p (w τ) ((i : ℕ) + 1))
    (hSlen : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 → ∀ a b : ℝ,
      0 ≤ a → a ≤ b → b ≤ 1 →
      Submission.Length.curveLength (I := I) (fun r : ℝ => S i r τ) a b
        = (b - a) * Work.OddBound.gonSideLen (I := I) p (w τ) (i : ℕ))
    (hN : 0 < N) {x y : ℝ} (hx0 : 0 ≤ x) (hxT : x ≤ totLen (I := I) p w τ)
    (hy0 : 0 ≤ y) (hyT : y ≤ totLen (I := I) p w τ) :
    Submission.Distance.riemannianDist (I := I) (gPt (I := I) p hN w S τ x)
      (gPt (I := I) p hN w S τ y) ≤ |y - x| := by
  rcases le_total x y with hxy | hyx
  · rw [abs_of_nonneg (by linarith)]
    exact gPt_dist_le_of_le (I := I) hτ hSsm hS0 hS1 hSlen hN hx0 hxT hy0 hyT hxy
  · rw [riemannianDist_comm_toReal (I := I), abs_sub_comm, abs_of_nonneg (by linarith)]
    exact gPt_dist_le_of_le (I := I) hτ hSsm hS0 hS1 hSlen hN hy0 hyT hx0 hxT hyx

end Aux
section Main

variable {p : M} {N : ℕ} {w : ℝ → Fin (N - 1) → M} {S : Fin N → ℝ → ℝ → M}

/-- **The broken geodesic at a nonpositive arclength is the base point.** -/
theorem gPt_eq_p_of_le_zero {τ a : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (hSsm : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 (fun r : ℝ => S i r τ)
        (Set.Icc (0 : ℝ) 1))
    (hS0 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 0 τ = Work.OddBound.gonVert p (w τ) (i : ℕ))
    (hS1 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 1 τ = Work.OddBound.gonVert p (w τ) ((i : ℕ) + 1))
    (hSlen : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 → ∀ a b : ℝ,
      0 ≤ a → a ≤ b → b ≤ 1 →
      Submission.Length.curveLength (I := I) (fun r : ℝ => S i r τ) a b
        = (b - a) * Work.OddBound.gonSideLen (I := I) p (w τ) (i : ℕ))
    (hN : 0 < N) (ha : a ≤ 0) :
    gPt (I := I) p hN w S τ a = p := by
  rcases lt_or_eq_of_le ha with hlt | heq
  · have hidx : gIdx (I := I) p w τ a = 0 := by
      have hfilter : (Finset.range N).filter (fun j => cumLen (I := I) p w τ j ≤ a) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro j hj
        rw [Finset.mem_range] at hj
        exact not_le.mpr (lt_of_lt_of_le hlt (cumLen_nonneg (I := I) p w τ j))
      rw [gIdx_def, hfilter, Finset.card_empty]
    have hfin : gFin (I := I) p hN w τ a = ⟨0, hN⟩ := by
      apply Fin.ext
      rw [gFin_val, hidx]
    have hprm : gPrm (I := I) p w τ a = 0 := by
      rw [gPrm_def, hidx]
      refine clamp01_eq_zero_of_nonpos ?_
      rcases eq_or_lt_of_le (sideLen_nonneg (I := I) p w τ 0) with h0 | h0
      · rw [← h0, div_zero]
      · exact div_nonpos_of_nonpos_of_nonneg (by rw [cumLen_zero]; linarith) h0.le
    rw [gPt_def, hfin, hprm, hS0 ⟨0, hN⟩ τ hτ, Work.OddBound.gonVert_zero]
  · rw [heq]
    exact gPt_zero_eq_p (I := I) hτ hSsm hS0 hS1 hSlen hN

/-- **The broken geodesic at an arclength at least the total length is the base point.** -/
theorem gPt_eq_p_of_totLen_le {τ a : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (hSsm : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 (fun r : ℝ => S i r τ)
        (Set.Icc (0 : ℝ) 1))
    (hS0 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 0 τ = Work.OddBound.gonVert p (w τ) (i : ℕ))
    (hS1 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 1 τ = Work.OddBound.gonVert p (w τ) ((i : ℕ) + 1))
    (hSlen : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 → ∀ a b : ℝ,
      0 ≤ a → a ≤ b → b ≤ 1 →
      Submission.Length.curveLength (I := I) (fun r : ℝ => S i r τ) a b
        = (b - a) * Work.OddBound.gonSideLen (I := I) p (w τ) (i : ℕ))
    (hN : 0 < N) (ha : totLen (I := I) p w τ ≤ a) :
    gPt (I := I) p hN w S τ a = p := by
  have hfilter : (Finset.range N).filter (fun j => cumLen (I := I) p w τ j ≤ a)
      = Finset.range N := by
    apply Finset.filter_true_of_mem
    intro j hj
    rw [Finset.mem_range] at hj
    calc cumLen (I := I) p w τ j ≤ cumLen (I := I) p w τ N :=
          cumLen_mono (I := I) p w τ (le_of_lt hj)
      _ = totLen (I := I) p w τ := (totLen_eq_cumLen (I := I) p w τ).symm
      _ ≤ a := ha
  have hidx : gIdx (I := I) p w τ a = N - 1 := by
    rw [gIdx_def, hfilter, Finset.card_range]
  have hfin : gFin (I := I) p hN w τ a = ⟨N - 1, by omega⟩ := by
    apply Fin.ext
    rw [gFin_val, hidx]
  rw [gPt_def, hfin]
  rcases eq_or_lt_of_le (sideLen_nonneg (I := I) p w τ (N - 1)) with h0 | hpos
  · have h0' : sideLen (I := I) p w τ (N - 1) = 0 := h0.symm
    have hcv : Work.OddBound.gonVert p (w τ) (N - 1) = Work.OddBound.gonVert p (w τ) N := by
      have h := eq_gonVert_of_sideLen_eq_zero (I := I) hτ hSsm hS0 hS1 hSlen (k := N - 1)
        (by omega) h0'
      rwa [show N - 1 + 1 = N from by omega] at h
    rw [gPrm_def, hidx, h0', div_zero, clamp01_eq_zero_of_nonpos le_rfl,
      hS0 ⟨N - 1, by omega⟩ τ hτ, hcv]
    exact Work.OddBound.gonVert_of_le p (w τ) le_rfl
  · have h1 : 1 ≤ (a - cumLen (I := I) p w τ (N - 1)) / sideLen (I := I) p w τ (N - 1) := by
      rw [le_div_iff₀ hpos, one_mul]
      have hsub : sideLen (I := I) p w τ (N - 1)
          = cumLen (I := I) p w τ N - cumLen (I := I) p w τ (N - 1) := by
        rw [sideLen_eq_sub, show N - 1 + 1 = N from by omega]
      have htot := totLen_eq_cumLen (I := I) p w τ
      linarith
    have hval : ((⟨N - 1, by omega⟩ : Fin N) : ℕ) + 1 = N := by
      rw [Fin.val_mk]
      omega
    rw [gPrm_def, hidx, clamp01_eq_one_of_one_le h1, hS1 ⟨N - 1, by omega⟩ τ hτ, hval]
    exact Work.OddBound.gonVert_of_le p (w τ) le_rfl

/-- **The broken geodesic only depends on the arclength clamped to `[0, totLen τ]`.** -/
theorem gPt_clamp {τ a : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (hSsm : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 (fun r : ℝ => S i r τ)
        (Set.Icc (0 : ℝ) 1))
    (hS0 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 0 τ = Work.OddBound.gonVert p (w τ) (i : ℕ))
    (hS1 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 1 τ = Work.OddBound.gonVert p (w τ) ((i : ℕ) + 1))
    (hSlen : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 → ∀ a b : ℝ,
      0 ≤ a → a ≤ b → b ≤ 1 →
      Submission.Length.curveLength (I := I) (fun r : ℝ => S i r τ) a b
        = (b - a) * Work.OddBound.gonSideLen (I := I) p (w τ) (i : ℕ))
    (hN : 0 < N) :
    gPt (I := I) p hN w S τ a
      = gPt (I := I) p hN w S τ (max 0 (min a (totLen (I := I) p w τ))) := by
  rcases le_or_gt a 0 with ha | ha
  · have h0 : max 0 (min a (totLen (I := I) p w τ)) = 0 := by
      rw [max_eq_left (le_trans (min_le_left _ _) ha)]
    rw [h0, gPt_eq_p_of_le_zero (I := I) hτ hSsm hS0 hS1 hSlen hN ha,
      gPt_zero_eq_p (I := I) hτ hSsm hS0 hS1 hSlen hN]
  · rcases le_or_gt (totLen (I := I) p w τ) a with hT | hT
    · have h0 : max 0 (min a (totLen (I := I) p w τ)) = totLen (I := I) p w τ := by
        rw [min_eq_right hT, max_eq_right (totLen_nonneg (I := I) p w τ)]
      rw [h0, gPt_eq_p_of_totLen_le (I := I) hτ hSsm hS0 hS1 hSlen hN hT,
        gPt_totLen_eq_p (I := I) hτ hSsm hS0 hS1 hSlen hN]
    · have h0 : max 0 (min a (totLen (I := I) p w τ)) = a := by
        rw [min_eq_left hT.le, max_eq_right ha.le]
      rw [h0]

/-! ## Continuity in the slice parameter -/

/-- The first projection, from the closed strip to the unit interval. -/
theorem tendsto_fst_Icc {x₀ : ℝ × ℝ} :
    Filter.Tendsto (fun x : ℝ × ℝ => x.1) (𝓝[Set.Icc (0 : ℝ) 1 ×ˢ Set.univ] x₀)
      (𝓝[Set.Icc (0 : ℝ) 1] x₀.1) := by
  rw [tendsto_nhdsWithin_iff]
  exact ⟨continuous_fst.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,
    Filter.eventually_of_mem self_mem_nhdsWithin (fun x hx => hx.1)⟩

/-- The cumulative side lengths are continuous in the slice parameter. -/
theorem continuousOn_cumLen'
    (hScont : ∀ i : Fin N, ContinuousOn (fun u : ℝ × ℝ => S i u.1 u.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1))
    (hS0 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 0 τ = Work.OddBound.gonVert p (w τ) (i : ℕ))
    (hS1 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 1 τ = Work.OddBound.gonVert p (w τ) ((i : ℕ) + 1))
    {k : ℕ} (hk : k ≤ N) :
    ContinuousOn (fun τ : ℝ => cumLen (I := I) p w τ k) (Set.Icc (0 : ℝ) 1) := by
  have hfun : (fun τ : ℝ => cumLen (I := I) p w τ k)
      = fun τ : ℝ => ∑ j ∈ Finset.range k, sideLen (I := I) p w τ j := by
    funext τ
    rfl
  rw [hfun]
  refine continuousOn_finsetSum (Finset.range k) (fun j hj => ?_)
  rw [Finset.mem_range] at hj
  exact continuousOn_sideLen (I := I) hScont hS0 hS1 ⟨j, lt_of_lt_of_le hj hk⟩

/-- The total length is continuous in the slice parameter. -/
theorem continuousOn_totLen'
    (hScont : ∀ i : Fin N, ContinuousOn (fun u : ℝ × ℝ => S i u.1 u.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1))
    (hS0 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 0 τ = Work.OddBound.gonVert p (w τ) (i : ℕ))
    (hS1 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 1 τ = Work.OddBound.gonVert p (w τ) ((i : ℕ) + 1)) :
    ContinuousOn (fun τ : ℝ => totLen (I := I) p w τ) (Set.Icc (0 : ℝ) 1) := by
  have hfun : (fun τ : ℝ => totLen (I := I) p w τ)
      = fun τ : ℝ => cumLen (I := I) p w τ N := by
    funext τ
    exact totLen_eq_cumLen (I := I) p w τ
  rw [hfun]
  exact continuousOn_cumLen' (I := I) hScont hS0 hS1 le_rfl

theorem tendsto_totLen_fst
    (hScont : ∀ i : Fin N, ContinuousOn (fun u : ℝ × ℝ => S i u.1 u.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1))
    (hS0 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 0 τ = Work.OddBound.gonVert p (w τ) (i : ℕ))
    (hS1 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 1 τ = Work.OddBound.gonVert p (w τ) ((i : ℕ) + 1))
    {x₀ : ℝ × ℝ} (hx₀ : x₀.1 ∈ Set.Icc (0 : ℝ) 1) :
    Filter.Tendsto (fun x : ℝ × ℝ => totLen (I := I) p w x.1)
      (𝓝[Set.Icc (0 : ℝ) 1 ×ˢ Set.univ] x₀) (𝓝 (totLen (I := I) p w x₀.1)) :=
  ((continuousOn_totLen' (I := I) hScont hS0 hS1).continuousWithinAt hx₀).tendsto.comp
    (tendsto_fst_Icc (x₀ := x₀))

theorem tendsto_cumLen_fst
    (hScont : ∀ i : Fin N, ContinuousOn (fun u : ℝ × ℝ => S i u.1 u.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1))
    (hS0 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 0 τ = Work.OddBound.gonVert p (w τ) (i : ℕ))
    (hS1 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 1 τ = Work.OddBound.gonVert p (w τ) ((i : ℕ) + 1))
    {x₀ : ℝ × ℝ} (hx₀ : x₀.1 ∈ Set.Icc (0 : ℝ) 1) (k : ℕ) (hk : k ≤ N) :
    Filter.Tendsto (fun x : ℝ × ℝ => cumLen (I := I) p w x.1 k)
      (𝓝[Set.Icc (0 : ℝ) 1 ×ˢ Set.univ] x₀) (𝓝 (cumLen (I := I) p w x₀.1 k)) :=
  ((continuousOn_cumLen' (I := I) hScont hS0 hS1 hk).continuousWithinAt hx₀).tendsto.comp
    (tendsto_fst_Icc (x₀ := x₀))

theorem tendsto_sideLen_fst
    (hScont : ∀ i : Fin N, ContinuousOn (fun u : ℝ × ℝ => S i u.1 u.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1))
    (hS0 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 0 τ = Work.OddBound.gonVert p (w τ) (i : ℕ))
    (hS1 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 1 τ = Work.OddBound.gonVert p (w τ) ((i : ℕ) + 1))
    {x₀ : ℝ × ℝ} (hx₀ : x₀.1 ∈ Set.Icc (0 : ℝ) 1) (i : Fin N) :
    Filter.Tendsto (fun x : ℝ × ℝ => sideLen (I := I) p w x.1 (i : ℕ))
      (𝓝[Set.Icc (0 : ℝ) 1 ×ˢ Set.univ] x₀) (𝓝 (sideLen (I := I) p w x₀.1 (i : ℕ))) :=
  ((continuousOn_sideLen (I := I) hScont hS0 hS1 i).continuousWithinAt hx₀).tendsto.comp
    (tendsto_fst_Icc (x₀ := x₀))

theorem tendsto_a_fst
    (hScont : ∀ i : Fin N, ContinuousOn (fun u : ℝ × ℝ => S i u.1 u.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1))
    (hS0 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 0 τ = Work.OddBound.gonVert p (w τ) (i : ℕ))
    (hS1 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 1 τ = Work.OddBound.gonVert p (w τ) ((i : ℕ) + 1))
    {x₀ : ℝ × ℝ} (hx₀ : x₀.1 ∈ Set.Icc (0 : ℝ) 1) :
    Filter.Tendsto (fun x : ℝ × ℝ => totLen (I := I) p w x.1 * x.2)
      (𝓝[Set.Icc (0 : ℝ) 1 ×ˢ Set.univ] x₀)
      (𝓝 (totLen (I := I) p w x₀.1 * x₀.2)) :=
  (tendsto_totLen_fst (I := I) hScont hS0 hS1 hx₀).mul
    (continuous_snd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)

/-- The Riemannian distance of a fixed vertex to the moving one tends to `0`. -/
theorem tendsto_dist_gonVert
    (hN : 0 < N)
    (hScont : ∀ i : Fin N, ContinuousOn (fun u : ℝ × ℝ => S i u.1 u.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1))
    (hS0 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 0 τ = Work.OddBound.gonVert p (w τ) (i : ℕ))
    {x₀ : ℝ × ℝ} (hx₀ : x₀.1 ∈ Set.Icc (0 : ℝ) 1) (m : ℕ) :
    Filter.Tendsto (fun x : ℝ × ℝ => Submission.Distance.riemannianDist (I := I)
        (Work.OddBound.gonVert p (w x.1) m) (Work.OddBound.gonVert p (w x₀.1) m))
      (𝓝[Set.Icc (0 : ℝ) 1 ×ˢ Set.univ] x₀) (𝓝 0) := by
  have hc := continuousOn_riemannianDist_pair (I := I)
    (A := fun τ : ℝ => Work.OddBound.gonVert p (w τ) m)
    (B := fun τ : ℝ => Work.OddBound.gonVert p (w x₀.1) m)
    (continuousOn_gonVert_of_continuousOn hN hScont hS0 m)
    continuousOn_const
  have h := (hc.continuousWithinAt hx₀).tendsto.comp (tendsto_fst_Icc (x₀ := x₀))
  rw [Submission.Distance.riemannianDist_self] at h
  exact h

/-- **Continuity of a single side curve, reparametrised by arclength.** -/
theorem tendsto_sideCurve
    (hScont : ∀ i : Fin N, ContinuousOn (fun u : ℝ × ℝ => S i u.1 u.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1))
    (hS0 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 0 τ = Work.OddBound.gonVert p (w τ) (i : ℕ))
    (hS1 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 1 τ = Work.OddBound.gonVert p (w τ) ((i : ℕ) + 1))
    {x₀ : ℝ × ℝ} (hx₀ : x₀.1 ∈ Set.Icc (0 : ℝ) 1) {j : Fin N}
    (hp : 0 < sideLen (I := I) p w x₀.1 (j : ℕ)) :
    Filter.Tendsto (fun x : ℝ × ℝ => S j
        (clamp01 ((totLen (I := I) p w x.1 * x.2 - cumLen (I := I) p w x.1 (j : ℕ))
          / sideLen (I := I) p w x.1 (j : ℕ))) x.1)
      (𝓝[Set.Icc (0 : ℝ) 1 ×ˢ Set.univ] x₀)
      (𝓝 (S j (clamp01 ((totLen (I := I) p w x₀.1 * x₀.2
          - cumLen (I := I) p w x₀.1 (j : ℕ))
          / sideLen (I := I) p w x₀.1 (j : ℕ))) x₀.1)) := by
  have hmap : Filter.Tendsto (fun x : ℝ × ℝ =>
        (clamp01 ((totLen (I := I) p w x.1 * x.2 - cumLen (I := I) p w x.1 (j : ℕ))
          / sideLen (I := I) p w x.1 (j : ℕ)), x.1))
      (𝓝[Set.Icc (0 : ℝ) 1 ×ˢ Set.univ] x₀)
      (𝓝[Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1]
        (clamp01 ((totLen (I := I) p w x₀.1 * x₀.2 - cumLen (I := I) p w x₀.1 (j : ℕ))
          / sideLen (I := I) p w x₀.1 (j : ℕ)), x₀.1)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · rw [nhds_prod_eq]
      refine (clamp01_continuous.continuousAt.tendsto.comp ?_).prodMk ?_
      · exact (((tendsto_a_fst (I := I) hScont hS0 hS1 hx₀).sub
          (tendsto_cumLen_fst (I := I) hScont hS0 hS1 hx₀ (j : ℕ) (le_of_lt j.isLt))).div
          (tendsto_sideLen_fst (I := I) hScont hS0 hS1 hx₀ j) (ne_of_gt hp))
      · exact continuous_fst.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact ⟨clamp01_mem _, hx.1⟩
  exact ((hScont j).continuousWithinAt ⟨clamp01_mem _, hx₀⟩).tendsto.comp hmap

/-! ## From a bound on the Riemannian distance to convergence -/

/-- The `ℝ≥0∞` criterion for convergence in `M` by the extended Riemannian distance. -/
theorem tendsto_nhds_iff_riemannianEDist {α : Type*} {l : Filter α} {f : α → M} {y : M} :
    Filter.Tendsto f l (𝓝 y) ↔
      ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ x in l, Manifold.riemannianEDist I (f x) y < ε := by
  haveI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  letI : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  have h : ∀ a b : M, edist a b = Manifold.riemannianEDist I a b := fun a b =>
    Submission.EDist.edist_eq_riemannianEDist (I := I) a b
  constructor
  · intro H ε hε
    filter_upwards [EMetric.tendsto_nhds.mp H ε hε] with x hx
    rwa [h] at hx
  · intro H
    refine EMetric.tendsto_nhds.mpr fun ε hε => ?_
    filter_upwards [H ε hε] with x hx
    rwa [← h] at hx

/-- Every positive extended real is above `ofReal η` for some positive real `η`. -/
theorem exists_ofReal_lt_of_pos {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ENNReal.ofReal η < ε := by
  rcases eq_or_ne ε ⊤ with h | h
  · exact ⟨1, one_pos, h ▸ ENNReal.ofReal_lt_top⟩
  · have hpos : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' h
    exact ⟨ε.toReal / 2, by linarith, by
      calc ENNReal.ofReal (ε.toReal / 2) < ENNReal.ofReal ε.toReal :=
            (ENNReal.ofReal_lt_ofReal_iff hpos).mpr (by linarith)
        _ = ε := ENNReal.ofReal_toReal h⟩

/-- **A bound of the Riemannian distance by a quantity tending to `0` gives convergence.** -/
theorem tendsto_of_dist_le_zero {α : Type*} {l : Filter α} {f : α → M} {y : M} {g : α → ℝ}
    (hg : Filter.Tendsto g l (𝓝 0))
    (h : ∀ᶠ x in l, Submission.Distance.riemannianDist (I := I) (f x) y ≤ g x) :
    Filter.Tendsto f l (𝓝 y) := by
  rw [tendsto_nhds_iff_riemannianEDist (I := I)]
  intro ε hε
  obtain ⟨η, hηpos, hηε⟩ := exists_ofReal_lt_of_pos hε
  have hg' : ∀ᶠ x in l, g x < η := hg.eventually (isOpen_Iio.mem_nhds hηpos)
  filter_upwards [h, hg'] with x hx hxη
  rw [edist_eq_ofReal_riemannianDist (I := I)]
  have h1 : ENNReal.ofReal (Submission.Distance.riemannianDist (I := I) (f x) y)
      ≤ ENNReal.ofReal (g x) := ENNReal.ofReal_le_ofReal hx
  have h2 : ENNReal.ofReal (g x) < ENNReal.ofReal η :=
    (ENNReal.ofReal_lt_ofReal_iff hηpos).mpr hxη
  exact lt_of_le_of_lt h1 (lt_trans h2 hηε)


/-! ## Continuity of the balanced loop on the strip `[0,1] × ℝ` -/

theorem continuousOn_gLoop_strip (hN : 0 < N)
    (hScont : ∀ i : Fin N, ContinuousOn (fun u : ℝ × ℝ => S i u.1 u.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1))
    (hSsm : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 (fun r : ℝ => S i r τ)
        (Set.Icc (0 : ℝ) 1))
    (hS0 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 0 τ = Work.OddBound.gonVert p (w τ) (i : ℕ))
    (hS1 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 1 τ = Work.OddBound.gonVert p (w τ) ((i : ℕ) + 1))
    (hSlen : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 → ∀ a b : ℝ,
      0 ≤ a → a ≤ b → b ≤ 1 →
      Submission.Length.curveLength (I := I) (fun r : ℝ => S i r τ) a b
        = (b - a) * Work.OddBound.gonSideLen (I := I) p (w τ) (i : ℕ)) :
    ContinuousOn (fun x : ℝ × ℝ => gLoop (I := I) p hN w S x.1 x.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
  intro x₀ hx₀
  obtain ⟨σ, u⟩ := x₀
  simp only [Set.mem_prod, Set.mem_univ, and_true] at hx₀
  rw [ContinuousWithinAt]
  set l : Filter (ℝ × ℝ) := 𝓝[Set.Icc (0 : ℝ) 1 ×ˢ Set.univ] (σ, u) with hl
  set a₀ : ℝ := totLen (I := I) p w σ * u with ha₀
  have hstrip : ∀ᶠ x in l, x.1 ∈ Set.Icc (0 : ℝ) 1 :=
    Filter.eventually_of_mem self_mem_nhdsWithin (fun x hx => hx.1)
  have hTa : Filter.Tendsto (fun x : ℝ × ℝ => totLen (I := I) p w x.1 * x.2) l (𝓝 a₀) :=
    tendsto_a_fst (I := I) hScont hS0 hS1 hx₀
  rcases lt_or_ge a₀ 0 with hneg | hnonneg
  · -- the arclength is negative: the loop is constant at the base point
    have hev : ∀ᶠ x in l, totLen (I := I) p w x.1 * x.2 < 0 :=
      hTa.eventually (isOpen_Iio.mem_nhds hneg)
    have hval : gLoop (I := I) p hN w S σ u = p := by
      rw [gLoop_def]
      exact gPt_eq_p_of_le_zero (I := I) hx₀ hSsm hS0 hS1 hSlen hN hneg.le
    have heq : (fun x : ℝ × ℝ => gLoop (I := I) p hN w S x.1 x.2) =ᶠ[l] fun _ => p := by
      filter_upwards [hev, hstrip] with x hx hxS
      rw [gLoop_def]
      exact gPt_eq_p_of_le_zero (I := I) hxS hSsm hS0 hS1 hSlen hN hx.le
    rw [hval]
    exact Filter.Tendsto.congr' heq.symm tendsto_const_nhds
  · rcases lt_or_ge (totLen (I := I) p w σ) a₀ with hbig | hle
    · -- the arclength exceeds the total length: the loop is constant at the base point
      have hd : Filter.Tendsto (fun x : ℝ × ℝ =>
            totLen (I := I) p w x.1 * x.2 - totLen (I := I) p w x.1) l
          (𝓝 (a₀ - totLen (I := I) p w σ)) :=
        hTa.sub (tendsto_totLen_fst (I := I) hScont hS0 hS1 hx₀)
      have hev : ∀ᶠ x in l, totLen (I := I) p w x.1 < totLen (I := I) p w x.1 * x.2 := by
        have hpos : 0 < a₀ - totLen (I := I) p w σ := by linarith
        filter_upwards [hd.eventually (isOpen_Ioi.mem_nhds hpos)] with x hx
        linarith
      have hval : gLoop (I := I) p hN w S σ u = p := by
        rw [gLoop_def]
        exact gPt_eq_p_of_totLen_le (I := I) hx₀ hSsm hS0 hS1 hSlen hN hbig.le
      have heq : (fun x : ℝ × ℝ => gLoop (I := I) p hN w S x.1 x.2) =ᶠ[l] fun _ => p := by
        filter_upwards [hev, hstrip] with x hx hxS
        rw [gLoop_def]
        exact gPt_eq_p_of_totLen_le (I := I) hxS hSsm hS0 hS1 hSlen hN hx.le
      rw [hval]
      exact Filter.Tendsto.congr' heq.symm tendsto_const_nhds
    · -- `0 ≤ a₀ ≤ totLen σ`
      by_cases hC1 : ∃ j : Fin N,
        cumLen (I := I) p w σ (j : ℕ) < a₀ ∧ a₀ < cumLen (I := I) p w σ ((j : ℕ) + 1)
      · -- the arclength is in the interior of a side
        obtain ⟨j, hj1, hj2⟩ := hC1
        have hlt1 : ∀ᶠ x in l, cumLen (I := I) p w x.1 (j : ℕ)
            < totLen (I := I) p w x.1 * x.2 := by
          have hpair : Filter.Tendsto (fun x : ℝ × ℝ =>
                (cumLen (I := I) p w x.1 (j : ℕ), totLen (I := I) p w x.1 * x.2)) l
              (𝓝 (cumLen (I := I) p w σ (j : ℕ), a₀)) := by
            rw [nhds_prod_eq]
            exact (tendsto_cumLen_fst (I := I) hScont hS0 hS1 hx₀ (j : ℕ) (le_of_lt j.isLt)).prodMk
              hTa
          exact hpair.eventually ((isOpen_lt continuous_fst continuous_snd).mem_nhds hj1)
        have hlt2 : ∀ᶠ x in l, totLen (I := I) p w x.1 * x.2
            < cumLen (I := I) p w x.1 ((j : ℕ) + 1) := by
          have hpair : Filter.Tendsto (fun x : ℝ × ℝ =>
                (totLen (I := I) p w x.1 * x.2, cumLen (I := I) p w x.1 ((j : ℕ) + 1))) l
              (𝓝 (a₀, cumLen (I := I) p w σ ((j : ℕ) + 1))) := by
            rw [nhds_prod_eq]
            exact hTa.prodMk (tendsto_cumLen_fst (I := I) hScont hS0 hS1 hx₀ ((j : ℕ) + 1) j.isLt)
          exact hpair.eventually ((isOpen_lt continuous_fst continuous_snd).mem_nhds hj2)
        have hp : 0 < sideLen (I := I) p w σ (j : ℕ) := by
          have hsub := sideLen_eq_sub (I := I) p w σ (j : ℕ)
          linarith
        have hval : gLoop (I := I) p hN w S σ u
            = S j (clamp01 ((a₀ - cumLen (I := I) p w σ (j : ℕ))
                / sideLen (I := I) p w σ (j : ℕ))) σ := by
          rw [gLoop_def]
          have hidx : gIdx (I := I) p w σ a₀ = (j : ℕ) :=
            gIdx_eq_of_lt_cumLen' (I := I) (by omega) hj1.le hj2
          have hfin : gFin (I := I) p hN w σ a₀ = j := by
            apply Fin.ext
            rw [gFin_val, hidx]
          rw [gPt_def, hfin, gPrm_def, hidx]
        have heq : (fun x : ℝ × ℝ => S j
              (clamp01 ((totLen (I := I) p w x.1 * x.2 - cumLen (I := I) p w x.1 (j : ℕ))
                / sideLen (I := I) p w x.1 (j : ℕ))) x.1)
            =ᶠ[l] fun x : ℝ × ℝ => gLoop (I := I) p hN w S x.1 x.2 := by
          filter_upwards [hlt1, hlt2, hstrip] with x hx1 hx2 hxS
          rw [gLoop_def]
          have hidx : gIdx (I := I) p w x.1 (totLen (I := I) p w x.1 * x.2) = (j : ℕ) :=
            gIdx_eq_of_lt_cumLen' (I := I) (by omega) hx1.le hx2
          have hfin : gFin (I := I) p hN w x.1 (totLen (I := I) p w x.1 * x.2) = j := by
            apply Fin.ext
            rw [gFin_val, hidx]
          rw [gPt_def, hfin, gPrm_def, hidx]
        rw [hval]
        exact Filter.Tendsto.congr' heq (tendsto_sideCurve (I := I) hScont hS0 hS1 hx₀ hp)
      · -- the arclength is a breakpoint: the loop tends to the corresponding vertex
        have hmN : gIdx (I := I) p w σ a₀ < N := gIdx_lt (I := I) p hN w σ a₀
        have hlo : cumLen (I := I) p w σ (gIdx (I := I) p w σ a₀) ≤ a₀ :=
          cumLen_gIdx_le (I := I) p hN w σ a₀ hnonneg
        have hhi : a₀ ≤ cumLen (I := I) p w σ (gIdx (I := I) p w σ a₀ + 1) :=
          le_cumLen_gIdx_succ (I := I) p hN w σ a₀ hle
        have hnot : ¬ (cumLen (I := I) p w σ (gIdx (I := I) p w σ a₀) < a₀ ∧
            a₀ < cumLen (I := I) p w σ (gIdx (I := I) p w σ a₀ + 1)) := fun hcon =>
          hC1 ⟨⟨gIdx (I := I) p w σ a₀, hmN⟩, hcon⟩
        have hm_exists : ∃ m : ℕ, m ≤ N ∧ a₀ = cumLen (I := I) p w σ m := by
          rcases not_and_or.mp hnot with h | h
          · exact ⟨gIdx (I := I) p w σ a₀, le_of_lt hmN, le_antisymm (not_lt.mp h) hlo⟩
          · exact ⟨gIdx (I := I) p w σ a₀ + 1, by omega, le_antisymm hhi (not_lt.mp h)⟩
        obtain ⟨m, hmNle, hm_eq⟩ := hm_exists
        have hval : gLoop (I := I) p hN w S σ u = Work.OddBound.gonVert p (w σ) m := by
          rw [gLoop_def, ← ha₀, hm_eq]
          exact gPt_cumLen_eq_gonVert (I := I) hx₀ hSsm hS0 hS1 hSlen hN hmNle
        rw [hval]
        refine tendsto_of_dist_le_zero (I := I)
          (f := fun x : ℝ × ℝ => gLoop (I := I) p hN w S x.1 x.2)
          (y := Work.OddBound.gonVert p (w σ) m)
          (g := fun x : ℝ × ℝ => |max 0 (min (totLen (I := I) p w x.1 * x.2)
              (totLen (I := I) p w x.1)) - cumLen (I := I) p w x.1 m|
            + Submission.Distance.riemannianDist (I := I)
              (Work.OddBound.gonVert p (w x.1) m) (Work.OddBound.gonVert p (w σ) m)) ?_ ?_
        · -- the bound tends to `0`
          have haC : Filter.Tendsto (fun x : ℝ × ℝ => max 0 (min (totLen (I := I) p w x.1 * x.2)
                (totLen (I := I) p w x.1))) l (𝓝 (max 0 (min a₀ (totLen (I := I) p w σ)))) :=
            tendsto_const_nhds.max (hTa.min (tendsto_totLen_fst (I := I) hScont hS0 hS1 hx₀))
          have hca : max 0 (min a₀ (totLen (I := I) p w σ)) = a₀ := by
            rw [min_eq_left hle, max_eq_right hnonneg]
          have hlim : Filter.Tendsto (fun x : ℝ × ℝ => max 0 (min (totLen (I := I) p w x.1 * x.2)
                (totLen (I := I) p w x.1))) l (𝓝 a₀) := by
            rw [← hca]
            exact haC
          have hdiff : Filter.Tendsto (fun x : ℝ × ℝ => max 0 (min (totLen (I := I) p w x.1 * x.2)
                (totLen (I := I) p w x.1)) - cumLen (I := I) p w x.1 m) l
              (𝓝 (a₀ - cumLen (I := I) p w σ m)) :=
            hlim.sub (tendsto_cumLen_fst (I := I) hScont hS0 hS1 hx₀ m hmNle)
          have hzero : a₀ - cumLen (I := I) p w σ m = 0 := by rw [hm_eq]; ring
          have h1 : Filter.Tendsto (fun x : ℝ × ℝ => |max 0 (min (totLen (I := I) p w x.1 * x.2)
                (totLen (I := I) p w x.1)) - cumLen (I := I) p w x.1 m|) l (𝓝 0) := by
            have hh := hdiff.abs
            rwa [hzero, abs_zero] at hh
          have hsum := h1.add (tendsto_dist_gonVert (I := I) hN hScont hS0 hx₀ m)
          simpa using hsum
        · -- the bound holds pointwise
          filter_upwards [hstrip] with x hxS
          have hclamp : gLoop (I := I) p hN w S x.1 x.2
              = gPt (I := I) p hN w S x.1 (max 0 (min (totLen (I := I) p w x.1 * x.2)
                  (totLen (I := I) p w x.1))) := by
            rw [gLoop_def]
            exact gPt_clamp (I := I) hxS hSsm hS0 hS1 hSlen hN
          rw [hclamp]
          have hvertex : Work.OddBound.gonVert p (w x.1) m
              = gPt (I := I) p hN w S x.1 (cumLen (I := I) p w x.1 m) :=
            (gPt_cumLen_eq_gonVert (I := I) hxS hSsm hS0 hS1 hSlen hN hmNle).symm
          have htri := riemannianDist_triangle_pathConnected (I := I)
            (gPt (I := I) p hN w S x.1 (max 0 (min (totLen (I := I) p w x.1 * x.2)
              (totLen (I := I) p w x.1))))
            (Work.OddBound.gonVert p (w x.1) m) (Work.OddBound.gonVert p (w σ) m)
          have hbound := gPt_dist_le_abs (I := I) hxS hSsm hS0 hS1 hSlen hN
            (x := cumLen (I := I) p w x.1 m)
            (y := max 0 (min (totLen (I := I) p w x.1 * x.2) (totLen (I := I) p w x.1)))
            (cumLen_nonneg (I := I) p w x.1 m)
            (le_trans (cumLen_mono (I := I) p w x.1 hmNle)
              (le_of_eq (totLen_eq_cumLen (I := I) p w x.1).symm))
            (le_max_left _ _)
            (max_le (totLen_nonneg (I := I) p w x.1) (min_le_right _ _))
          rw [riemannianDist_comm_toReal (I := I)] at hbound
          rw [← hvertex] at hbound
          linarith [htri, hbound]

end Main

theorem continuousOn_gLoop
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I (WithTop.some (⊤ : ENat)) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I (WithTop.some (⊤ : ENat)) E
      (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {p : M} {N : ℕ} (hN : 0 < N) {w : ℝ → Fin (N - 1) → M} {S : Fin N → ℝ → ℝ → M}
    (hScont : ∀ i : Fin N, ContinuousOn (fun u : ℝ × ℝ => S i u.1 u.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1))
    (hSsm : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 (fun r : ℝ => S i r τ)
        (Set.Icc (0 : ℝ) 1))
    (hS0 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 0 τ = Work.OddBound.gonVert p (w τ) (i : ℕ))
    (hS1 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 1 τ = Work.OddBound.gonVert p (w τ) ((i : ℕ) + 1))
    (hSlen : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 → ∀ a b : ℝ,
      0 ≤ a → a ≤ b → b ≤ 1 →
      Submission.Length.curveLength (I := I) (fun r : ℝ => S i r τ) a b
        = (b - a) * Work.OddBound.gonSideLen (I := I) p (w τ) (i : ℕ)) :
    Continuous (fun q : ℝ × ℝ =>
      Work.OddBound.polygonValue.gLoop (I := I) p hN w S
        (Work.OddBound.polygonValue.clamp01 q.1) q.2) := by
  have hG := continuousOn_gLoop_strip (I := I) hN hScont hSsm hS0 hS1 hSlen
  have hφ : Continuous (fun q : ℝ × ℝ => (clamp01 q.1, q.2)) :=
    (clamp01_continuous.comp continuous_fst).prodMk continuous_snd
  have hmaps : Set.MapsTo (fun q : ℝ × ℝ => (clamp01 q.1, q.2)) Set.univ
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := fun q _ => ⟨clamp01_mem _, trivial⟩
  have hcomp : ContinuousOn ((fun x : ℝ × ℝ => gLoop (I := I) p hN w S x.1 x.2) ∘
      (fun q : ℝ × ℝ => (clamp01 q.1, q.2))) Set.univ :=
    hG.comp hφ.continuousOn hmaps
  rw [continuousOn_univ] at hcomp
  simpa only [Function.comp_def] using hcomp

end Work.OddBound.polygonValue.balancing
