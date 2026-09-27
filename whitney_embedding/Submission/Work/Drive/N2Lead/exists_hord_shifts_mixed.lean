import Mathlib
import Submission.Work.Drive.N2.windowDatum
import Submission.Work.Drive.N2C.defs
import Submission.Work.Drive.N2Lead.saddleArcs
import Submission.Work.Drive.N2Lead.saddlePinDefs

namespace Work.Drive.N2Lead

/-!
# The horizontal order of the two arcs of the anchor level (mixed monotonicities)

The two model arcs `arcUpPt` / `arcDnPt` appear on a component `γ i` of the anchor level through two
reparametrisations `τU`, `τL` on the window `[-m, m]`: `τU` strictly *antitone* (as for
`exists_hord_shifts_anti`) and `τL` strictly *monotone* (the mixed case).  The two arcs are disjoint
as point sets, and — because `γ i` is periodic of period `1` and `γ i` is injective on `Ico 0 1`
(the row `modOne` of `LevelCurves`) — the difference `τU w - τL w'` is never an integer.

Consequently no integer lies in the closed interval
`[τU m - τL m, τU (-m) - τL (-m)]`, and `⌈τU m - τL m⌉` is an integer shift `kL` which places the
lower arc strictly above the upper arc's start and strictly below the upper arc's end shifted by
`1`:

  `τU (-m) < τL (-m) + kL`  and  `τL m + kL < τU m + 1`.

Taking `kU = 0` gives the four interleaving inequalities of the statement.
-/

/-- **The periodicity of a `LevelCurves` component at integer shifts.** -/
theorem levelCurves_gamma_add_int {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {b : ℝ} {n : ℕ} (L : Work.Drive.N2C.LevelCurves f b n) (i : Fin n) (k : ℤ)
    (x : ℝ) : L.γ i (x + (k : ℝ)) = L.γ i x := by
  have h : Function.Periodic (L.γ i) (1 : ℝ) := L.per i
  simpa using h.int_mul k x

theorem exists_hord_shifts_mixed {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {lam0 η m : ℝ} (hm : 0 < m)
    {n : ℕ} {L : Work.Drive.N2C.LevelCurves f (f p - lam0 ^ 2 * η) n} {i : Fin n}
    {τU τL : ℝ → ℝ}
    (hτUcont : ContinuousOn τU (Set.Icc (-m) m))
    (hτUanti : StrictAntiOn τU (Set.Icc (-m) m))
    (hτUspan : τU (-m) - τU m < 1)
    (hτUval : ∀ w ∈ Set.Icc (-m) m, L.γ i (τU w) = Work.Drive.N2Lead.arcUpPt D lam0 η w)
    (hτLcont : ContinuousOn τL (Set.Icc (-m) m))
    (hτLmono : StrictMonoOn τL (Set.Icc (-m) m))
    (hτLspan : τL m - τL (-m) < 1)
    (hτLval : ∀ w ∈ Set.Icc (-m) m, L.γ i (τL w) = Work.Drive.N2Lead.arcDnPt D lam0 η w)
    (hdisj : ∀ w ∈ Set.Icc (-m) m, ∀ w' ∈ Set.Icc (-m) m,
      Work.Drive.N2Lead.arcUpPt D lam0 η w ≠ Work.Drive.N2Lead.arcDnPt D lam0 η w') :
    ∃ kU kL : ℤ, τU m + kU < τU (-m) + kU ∧ τU (-m) + kU < τL (-m) + kL ∧
      τL (-m) + kL < τL m + kL ∧ τL m + kL < τU m + kU + 1 := by
  have hmle : -m ≤ m := by linarith
  have hmneg : -m ∈ Set.Icc (-m) m := ⟨le_refl _, hmle⟩
  have hmpos : m ∈ Set.Icc (-m) m := ⟨hmle, le_refl _⟩
  -- the two arcs are strictly ordered, inside each arc
  have hUm : τU m < τU (-m) := hτUanti hmneg hmpos (by linarith)
  have hLm : τL (-m) < τL m := hτLmono hmneg hmpos (by linarith)
  -- periodicity at integer shifts
  have hper : ∀ (k : ℤ) (x : ℝ), L.γ i (x + (k : ℝ)) = L.γ i x :=
    fun k x => levelCurves_gamma_add_int L i k x
  -- no integer lies in the closed interval `[τU m - τL m, τU (-m) - τL (-m)]`
  have hno : ∀ k : ℤ,
      ¬ (τU m - τL m ≤ (k : ℝ) ∧ (k : ℝ) ≤ τU (-m) - τL (-m)) := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := hk
    -- the strictly antitone `w ↦ τU w - τL w` sweeps out that interval
    have hcont : ContinuousOn (fun w : ℝ => τU w - τL w) (Set.Icc (-m) m) :=
      hτUcont.sub hτLcont
    have hdiff : (k : ℝ) ∈ Set.Icc ((fun w : ℝ => τU w - τL w) m)
        ((fun w : ℝ => τU w - τL w) (-m)) := ⟨hk1, hk2⟩
    obtain ⟨w, hw, hwv⟩ :=
      (intermediate_value_Icc' hmle hcont hdiff
        : ∃ c ∈ Set.Icc (-m) m, τU c - τL c = (k : ℝ))
    have heq : Work.Drive.N2Lead.arcUpPt D lam0 η w
        = Work.Drive.N2Lead.arcDnPt D lam0 η w := by
      have htw : τU w = τL w + (k : ℝ) := by linarith
      rw [← hτUval w hw, ← hτLval w hw, htw, hper k (τL w)]
    exact hdisj w hw w hw heq
  refine ⟨0, ⌈τU m - τL m⌉, ?_, ?_, ?_, ?_⟩
  · simpa using hUm
  · have hle : τU m - τL m ≤ (⌈τU m - τL m⌉ : ℝ) := Int.le_ceil _
    have hlt : τU (-m) - τL (-m) < (⌈τU m - τL m⌉ : ℝ) := by
      by_contra hcon
      push Not at hcon
      exact hno ⌈τU m - τL m⌉ ⟨hle, hcon⟩
    simp only [Int.cast_zero, add_zero]
    linarith
  · simpa using hLm
  · have hlt : (⌈τU m - τL m⌉ : ℝ) < τU m - τL m + 1 := Int.ceil_lt_add_one _
    simp only [Int.cast_zero, add_zero]
    linarith

end Work.Drive.N2Lead
