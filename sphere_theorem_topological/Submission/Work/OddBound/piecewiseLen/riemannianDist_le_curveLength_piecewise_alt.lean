import Mathlib
import Submission.Work.OddBound.piecewiseDist
import Submission.Work.OddBound.polygon.riemannianDist_eq_toReal
import Submission.Work.OddBound.liftPiecewise.exists_lift_of_piecewise_short

/-!
# Backup proof: distance ≤ length for a piecewise `C¹` curve

A second, self-contained proof of `Work.OddBound.piecewiseLen.riemannianDist_le_curveLength_piecewise`
(the version requested from the fleet), written while that request is in flight.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set MeasureTheory
open scoped MeasureTheory Interval

namespace Work.OddBound.piecewiseLen

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I (WithTop.some (⊤ : ENat)) M]
  [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I (WithTop.some (⊤ : ENat)) E
    (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]

theorem riemannianDist_le_curveLength_piecewise_alt
    {f : ℝ → M} {k : ℕ} {a : Fin (k + 1) → ℝ}
    (hamono : StrictMono a) (ha0 : a 0 = 0) (ha1 : a (Fin.last k) = 1)
    (hpiece : ∀ j : Fin k, ContMDiffOn 𝓘(ℝ) I 1 f (Set.Icc (a j.castSucc) (a j.succ)))
    {c d : ℝ} (hc : 0 ≤ c) (hcd : c ≤ d) (hd : d ≤ 1) :
    Submission.Distance.riemannianDist (I := I) (f c) (f d)
      ≤ Submission.Length.curveLength (I := I) f c d := by
  have htri := fun x y z : M => Submission.Distance.riemannianDist_triangle (I := I)
    (Work.OddBound.polygon.PwLengthSet_nonempty (I := I) x y)
    (Work.OddBound.polygon.PwLengthSet_nonempty (I := I) y z)
  have hint : ∀ c d : ℝ, 0 ≤ c → c ≤ d → d ≤ 1 →
      IntervalIntegrable (Submission.Length.curveSpeed (I := I) f) MeasureTheory.volume c d :=
    fun c d hc hcd hd =>
      Work.OddBound.liftPiecewise.intervalIntegrable_curveSpeed_piecewise
        (I := I) (h := f) (S := 1) (k := k) (a := a) hamono ha0 ha1 hpiece c d hc hcd hd
  set T : ℝ → ℝ → Finset (Fin (k + 1)) :=
    fun c d => Finset.univ.filter (fun j => c < a j ∧ a j < d) with hTdef
  have hmemT : ∀ c d : ℝ, ∀ j : Fin (k + 1), j ∈ T c d ↔ c < a j ∧ a j < d := by
    intro c d j
    simp only [hTdef, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases eq_or_lt_of_le hcd with heq | hcdlt
  · rw [heq, Submission.Distance.riemannianDist_self, Submission.Length.curveLength_self]
  -- base case: no breakpoint strictly inside `(c,d)`
  have hbase : ∀ c d : ℝ, 0 ≤ c → c < d → d ≤ 1 → (T c d).card = 0 →
      Submission.Distance.riemannianDist (I := I) (f c) (f d)
        ≤ Submission.Length.curveLength (I := I) f c d := by
    intro c d hc hclt hd hcard
    obtain ⟨j₀, hj₀mem, hj₀max⟩ := Set.exists_max_image
      (s := {j : Fin (k + 1) | a j ≤ c}) (f := a)
      (Set.finite_univ.subset (Set.subset_univ _)) ⟨0, by show a 0 ≤ c; rw [ha0]; exact hc⟩
    have hilt : j₀.val < k := by
      have h1 : a j₀ < a (Fin.last k) := by
        rw [ha1]
        exact lt_of_le_of_lt hj₀mem (lt_of_lt_of_le hclt hd)
      have h2 : j₀ < Fin.last k := hamono.lt_iff_lt.mp h1
      simpa [Fin.lt_def] using h2
    have hjcast : (⟨j₀.val, hilt⟩ : Fin k).castSucc = j₀ := Fin.ext rfl
    have hjsucc : d ≤ a (⟨j₀.val, hilt⟩ : Fin k).succ := by
      by_contra hcon
      push_neg at hcon
      have hgt : c < a (⟨j₀.val, hilt⟩ : Fin k).succ := by
        by_contra hcon2
        push_neg at hcon2
        have hle := hj₀max _ hcon2
        have hlt2 : a j₀ < a (⟨j₀.val, hilt⟩ : Fin k).succ := by
          have hlt' := hamono (show (⟨j₀.val, hilt⟩ : Fin k).castSucc
            < (⟨j₀.val, hilt⟩ : Fin k).succ from Fin.castSucc_lt_succ_iff.mpr le_rfl)
          rwa [hjcast] at hlt'
        linarith
      have hmem : (⟨j₀.val, hilt⟩ : Fin k).succ ∈ T c d := (hmemT c d _).mpr ⟨hgt, hcon⟩
      rw [Finset.card_eq_zero] at hcard
      rw [hcard] at hmem
      exact absurd hmem (by simp)
    have hltab : a (⟨j₀.val, hilt⟩ : Fin k).castSucc
        < a (⟨j₀.val, hilt⟩ : Fin k).succ :=
      hamono (Fin.castSucc_lt_succ_iff.mpr le_rfl)
    exact Work.OddBound.piecewiseDist.dist_le_curveLength_of_contMDiffOn_Icc
      (I := I) (h := f) (α := a (⟨j₀.val, hilt⟩ : Fin k).castSucc)
      (β := a (⟨j₀.val, hilt⟩ : Fin k).succ) hltab.le (hpiece _) (by rwa [hjcast]) hclt.le hjsucc
  -- induction on the number of interior breakpoints
  have main : ∀ n : ℕ, ∀ c d : ℝ, 0 ≤ c → c < d → d ≤ 1 → (T c d).card ≤ n →
      Submission.Distance.riemannianDist (I := I) (f c) (f d)
        ≤ Submission.Length.curveLength (I := I) f c d := by
    intro n
    induction n with
    | zero =>
      intro c d hc hclt hd hcard
      exact hbase c d hc hclt hd (Nat.le_zero.mp hcard)
    | succ m ih =>
      intro c d hc hclt hd hcard
      by_cases hcard0 : (T c d).card = 0
      · exact hbase c d hc hclt hd hcard0
      · obtain ⟨j₀, hj₀mem⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hcard0)
        have hj₀c : c < a j₀ := ((hmemT c d j₀).mp hj₀mem).1
        have hj₀d : a j₀ < d := ((hmemT c d j₀).mp hj₀mem).2
        have hlt1 : (T c (a j₀)).card < (T c d).card := by
          refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩)
          · intro j hj
            obtain ⟨h1, h2⟩ := (hmemT c (a j₀) j).mp hj
            exact (hmemT c d j).mpr ⟨h1, lt_trans h2 hj₀d⟩
          · intro heq
            have hmem : j₀ ∈ T c (a j₀) := heq ▸ ((hmemT c d j₀).mpr ⟨hj₀c, hj₀d⟩)
            exact absurd ((hmemT c (a j₀) j₀).mp hmem).2 (lt_irrefl _)
        have hlt2 : (T (a j₀) d).card < (T c d).card := by
          refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩)
          · intro j hj
            obtain ⟨h1, h2⟩ := (hmemT (a j₀) d j).mp hj
            exact (hmemT c d j).mpr ⟨lt_trans hj₀c h1, h2⟩
          · intro heq
            have hmem : j₀ ∈ T (a j₀) d := heq ▸ ((hmemT c d j₀).mpr ⟨hj₀c, hj₀d⟩)
            exact absurd ((hmemT (a j₀) d j₀).mp hmem).1 (lt_irrefl _)
        have hle1 : (T c (a j₀)).card ≤ m := by omega
        have hle2 : (T (a j₀) d).card ≤ m := by omega
        have h1 := ih c (a j₀) hc hj₀c (le_trans hj₀d.le hd) hle1
        have h2 := ih (a j₀) d (le_trans hc hj₀c.le) hj₀d hd hle2
        have htri' := htri (f c) (f (a j₀)) (f d)
        have hadd := Submission.Length.curveLength_add_of_integrable (I := I) f
          (hint c (a j₀) hc hj₀c.le (le_trans hj₀d.le hd))
          (hint (a j₀) d (le_trans hc hj₀c.le) hj₀d.le hd)
        linarith
  exact main (T c d).card c d hc hcdlt hd le_rfl

end Work.OddBound.piecewiseLen
