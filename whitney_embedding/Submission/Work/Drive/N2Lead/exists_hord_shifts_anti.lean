import Mathlib
import Submission.Work.Drive.N2.windowDatum
import Submission.Work.Drive.N2C.defs
import Submission.Work.Drive.N2Lead.saddleArcs
import Submission.Work.Drive.N2Lead.saddlePinDefs

/-!
# The horizontal-order shifts of the two saddle arcs (antitone case)

This is the antitone companion of `exists_hord_shifts_mixed`: if the two anchor arcs of the saddle are
parametrised by *strictly antitone* continuous reparametrisations `τU`, `τL` of the level component
`L.γ i` (with spans `< 1`), and if the two arcs are disjoint, then the two parametrisation intervals
can be placed, by integer shifts `kU`, `kL`, so that the `τL`-interval sits strictly below the
`τU`-interval and its lower end is less than one above the upper end of the `τU`-interval.

The mathematical content is the following.  `L.per` says that `L.γ i` is `1`-periodic, so
`L.γ i (τU w) = L.γ i (τL w' + j)` for every integer `j`.  Hence, if `τU w - τL w'` were an integer,
the disjointness `hdisj` together with `hτUval`/`hτLval` would be contradicted.  So the function
`F (w, w') = τU w - τL w'` takes **no integer value** on the preconnected square
`Icc (-m) m × Icc (-m) m`; its image is therefore a preconnected subset of `ℝ` avoiding `ℤ`, i.e. it
lies in a single gap `(k, k+1)`.  With that integer `k` the conclusion holds for `kU = -k`, `kL = 0`.
-/

namespace Work.Drive.N2Lead

open Set

theorem exists_hord_shifts_anti {M : Type*} [TopologicalSpace M]
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
    (hτLanti : StrictAntiOn τL (Set.Icc (-m) m))
    (hτLspan : τL (-m) - τL m < 1)
    (hτLval : ∀ w ∈ Set.Icc (-m) m, L.γ i (τL w) = Work.Drive.N2Lead.arcDnPt D lam0 η w)
    (hdisj : ∀ w ∈ Set.Icc (-m) m, ∀ w' ∈ Set.Icc (-m) m,
      Work.Drive.N2Lead.arcUpPt D lam0 η w ≠ Work.Drive.N2Lead.arcDnPt D lam0 η w') :
    ∃ kU kL : ℤ, τL m + kL < τL (-m) + kL ∧ τL (-m) + kL < τU m + kU ∧
      τU m + kU < τU (-m) + kU ∧ τU (-m) + kU < τL m + kL + 1 := by
  have hlt : -m < m := by linarith
  have hmemm : m ∈ Set.Icc (-m) m := ⟨by linarith, le_rfl⟩
  have hmemM : -m ∈ Set.Icc (-m) m := ⟨le_rfl, by linarith⟩
  have hmem0 : (0 : ℝ) ∈ Set.Icc (-m) m := ⟨by linarith, by linarith⟩
  -- the parameter square is preconnected, and `F` is continuous on it
  have hD : IsPreconnected (Set.Icc (-m) m ×ˢ Set.Icc (-m) m) :=
    isPreconnected_Icc.prod isPreconnected_Icc
  have hcontU : ContinuousOn (fun q : ℝ × ℝ => τU q.1)
      (Set.Icc (-m) m ×ˢ Set.Icc (-m) m) :=
    hτUcont.comp continuous_fst.continuousOn (fun q hq => hq.1)
  have hcontL : ContinuousOn (fun q : ℝ × ℝ => τL q.2)
      (Set.Icc (-m) m ×ˢ Set.Icc (-m) m) :=
    hτLcont.comp continuous_snd.continuousOn (fun q hq => hq.2)
  have hcontF : ContinuousOn (fun q : ℝ × ℝ => τU q.1 - τL q.2)
      (Set.Icc (-m) m ×ˢ Set.Icc (-m) m) := hcontU.sub hcontL
  -- the image is an interval (ordConnected)
  have hSord : (Set.image (fun q : ℝ × ℝ => τU q.1 - τL q.2)
      (Set.Icc (-m) m ×ˢ Set.Icc (-m) m)).OrdConnected :=
    (hD.image _ hcontF).ordConnected
  -- **no difference of the two parametrisations is an integer**
  have hnoInt : ∀ w ∈ Set.Icc (-m) m, ∀ w' ∈ Set.Icc (-m) m, ∀ j : ℤ,
      τU w - τL w' ≠ (j : ℝ) := by
    intro w hw w' hw' j hj
    have hγ : L.γ i (τU w) = L.γ i (τL w') := by
      have h1 : τU w = τL w' + (j : ℝ) * 1 := by push_cast; linarith
      rw [h1, Function.Periodic.int_mul (L.per i) j (τL w')]
    rw [hτUval w hw, hτLval w' hw'] at hγ
    exact hdisj w hw w' hw' hγ
  -- **all the differences lie in one gap `(k, k+1)`**
  have hgap : ∃ k : ℤ, ∀ q ∈ Set.Icc (-m) m ×ˢ Set.Icc (-m) m,
      (k : ℝ) < τU q.1 - τL q.2 ∧ τU q.1 - τL q.2 < (k : ℝ) + 1 := by
    refine ⟨⌊τU 0 - τL 0⌋, ?_⟩
    have hklo : ((⌊τU 0 - τL 0⌋ : ℤ) : ℝ) < τU 0 - τL 0 :=
      lt_of_le_of_ne (Int.floor_le _) (Ne.symm (hnoInt 0 hmem0 0 hmem0 ⌊τU 0 - τL 0⌋))
    have hkhi : τU 0 - τL 0 < ((⌊τU 0 - τL 0⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
    intro q hq
    have hqS : τU q.1 - τL q.2 ∈ Set.image (fun q : ℝ × ℝ => τU q.1 - τL q.2)
        (Set.Icc (-m) m ×ˢ Set.Icc (-m) m) := ⟨q, hq, rfl⟩
    have h0S : τU 0 - τL 0 ∈ Set.image (fun q : ℝ × ℝ => τU q.1 - τL q.2)
        (Set.Icc (-m) m ×ˢ Set.Icc (-m) m) := ⟨(0, 0), ⟨hmem0, hmem0⟩, rfl⟩
    constructor
    · by_contra hc
      rw [not_lt] at hc
      obtain ⟨q', hq', hq'eq⟩ := hSord.out hqS h0S ⟨hc, hklo.le⟩
      exact hnoInt q'.1 hq'.1 q'.2 hq'.2 ⌊τU 0 - τL 0⌋ hq'eq
    · by_contra hc
      rw [not_lt] at hc
      obtain ⟨q', hq', hq'eq⟩ := hSord.out h0S hqS ⟨hkhi.le, hc⟩
      refine hnoInt q'.1 hq'.1 q'.2 hq'.2 (⌊τU 0 - τL 0⌋ + 1) ?_
      show τU q'.1 - τL q'.2 = (((⌊τU 0 - τL 0⌋ + 1 : ℤ)) : ℝ)
      rw [show (((⌊τU 0 - τL 0⌋ + 1 : ℤ)) : ℝ) = ((⌊τU 0 - τL 0⌋ : ℤ) : ℝ) + 1 from by
        push_cast; ring]
      exact hq'eq
  obtain ⟨k, hbound⟩ := hgap
  refine ⟨-k, 0, ?_, ?_, ?_, ?_⟩
  · simpa using hτLanti hmemM hmemm hlt
  · have hb := (hbound (m, -m) ⟨hmemm, hmemM⟩).1
    push_cast
    linarith
  · have hb := hτUanti hmemM hmemm hlt
    linarith
  · have hb := (hbound (-m, m) ⟨hmemM, hmemm⟩).2
    push_cast
    linarith

end Work.Drive.N2Lead
