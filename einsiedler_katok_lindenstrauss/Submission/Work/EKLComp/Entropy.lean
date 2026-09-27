import Submission.Work.EKLComp.Core

/-!
# C3 — `joinSets`, subadditivity of `Hfam ∘ joinSets`, Fekete, and the `hPart` API
-/

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

noncomputable section

set_option maxHeartbeats 2000000

namespace Work.EKLComp.Core

open Work.EKLContract

variable {X : Type*} [mX : MeasurableSpace X]

/-! ## 6. The finite partitions `joinSets T P N` -/

theorem iterate_comm_apply (T : X → X) (m n : ℕ) (x : X) :
    T^[n] (T^[m] x) = T^[m + n] x := by
  rw [← Function.iterate_add_apply, Nat.add_comm m n]

theorem joinSets_measurable {T : X → X} (hT : Measurable T) (P : FinPart X) (N : ℕ)
    (w : Fin N → Fin P.n) : MeasurableSet (joinSets T P N w) := by
  rw [joinSets]
  exact MeasurableSet.iInter fun k => (P.measurable (w k)).preimage (hT.iterate (k : ℕ))

theorem joinSets_disjoint (T : X → X) (P : FinPart X) (N : ℕ) :
    Pairwise (fun u v => Disjoint (joinSets T P N u) (joinSets T P N v)) := by
  intro u v huv
  obtain ⟨k, hk⟩ : ∃ k : Fin N, u k ≠ v k := Function.ne_iff.mp huv
  refine Set.disjoint_left.mpr fun x hxu hxv => ?_
  have h1 : T^[(k:ℕ)] x ∈ P.parts (u k) := by
    have := hxu
    simp only [joinSets, Set.mem_iInter, Set.mem_preimage] at this
    exact this k
  have h2 : T^[(k:ℕ)] x ∈ P.parts (v k) := by
    have := hxv
    simp only [joinSets, Set.mem_iInter, Set.mem_preimage] at this
    exact this k
  exact Set.disjoint_left.mp (P.disjoint hk) h1 h2

theorem joinSets_iUnion (T : X → X) (P : FinPart X) (N : ℕ) :
    (⋃ w : Fin N → Fin P.n, joinSets T P N w) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  have h : ∀ k : Fin N, ∃ i : Fin P.n, T^[(k:ℕ)] x ∈ P.parts i := by
    intro k
    have hmem : T^[(k:ℕ)] x ∈ ⋃ i, P.parts i := by rw [P.cover]; trivial
    simpa only [Set.mem_iUnion] using hmem
  choose w hw using h
  exact ⟨w, by simpa only [joinSets, Set.mem_iInter, Set.mem_preimage] using hw⟩

theorem joinSets_succ_subset (T : X → X) (P : FinPart X) (N : ℕ)
    (v : Fin (N+1) → Fin P.n) :
    joinSets T P (N+1) v ⊆ joinSets T P N (fun k => v (Fin.castSucc k)) := by
  intro x hx
  simp only [joinSets, Set.mem_iInter, Set.mem_preimage] at hx ⊢
  intro k
  exact hx (Fin.castSucc k)

theorem joinSets_one (T : X → X) (P : FinPart X) (v : Fin 1 → Fin P.n) :
    joinSets T P 1 v = P.parts (v 0) := by
  ext x
  simp only [joinSets, Set.mem_iInter, Set.mem_preimage]
  constructor
  · intro h; simpa using h 0
  · intro h k
    fin_cases k
    simpa using h

theorem joinSets_zero (T : X → X) (P : FinPart X) (w : Fin 0 → Fin P.n) :
    joinSets T P 0 w = Set.univ := by
  ext x
  simp [joinSets]

theorem joinSets_isMPart {T : X → X} (hT : Measurable T) (P : FinPart X) (N : ℕ) :
    IsMPart (joinSets T P N) :=
  ⟨joinSets_measurable hT P N, joinSets_disjoint T P N, joinSets_iUnion T P N⟩

/-- Splitting a `joinSets` atom along `Fin (m + n) = Fin m ⊕ Fin n`. -/
theorem joinSets_append (T : X → X) (P : FinPart X) (m n : ℕ)
    (u : Fin m → Fin P.n) (v : Fin n → Fin P.n) :
    joinSets T P (m + n) (Fin.append u v) =
      joinSets T P m u ∩ T^[m] ⁻¹' joinSets T P n v := by
  ext x
  simp only [joinSets, Set.mem_iInter, Set.mem_preimage, Set.mem_inter_iff]
  rw [Fin.forall_fin_add (P := fun k : Fin (m + n) =>
    T^[k.val] x ∈ P.parts (Fin.append u v k))]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ?_, fun j => ?_⟩
    · have := h1 i
      rw [Fin.val_castAdd, Fin.append_left] at this
      exact this
    · have := h2 j
      rw [Fin.val_natAdd, Fin.append_right] at this
      rw [← iterate_comm_apply T m j.val x] at this
      exact this
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ?_, fun j => ?_⟩
    · have := h1 i
      rw [Fin.val_castAdd, Fin.append_left]
      exact this
    · have := h2 j
      rw [Fin.val_natAdd, Fin.append_right, ← iterate_comm_apply T m j.val x]
      exact this

/-! ## 7. Subadditivity of `N ↦ Hfam μ (joinSets T P N)` -/

theorem Hfam_joinSets_add_le (μ : Measure X) [IsProbabilityMeasure μ] {T : X → X}
    (hmp : MeasurePreserving T μ μ) (P : FinPart X) (m n : ℕ) :
    Hfam μ (joinSets T P (m + n)) ≤ Hfam μ (joinSets T P m) + Hfam μ (joinSets T P n) := by
  have hT : Measurable T := hmp.measurable
  have hBmp : IsMPart (fun v : Fin n → Fin P.n => T^[m] ⁻¹' joinSets T P n v) := by
    refine ⟨fun v => ?_, ?_, ?_⟩
    · exact (joinSets_measurable hT P n v).preimage (hT.iterate m)
    · intro u v huv
      refine Set.disjoint_left.mpr fun x hx hy => ?_
      exact Set.disjoint_left.mp (joinSets_disjoint T P n huv) hx hy
    · ext x
      constructor
      · intro _; exact Set.mem_univ x
      · intro _
        have h : T^[m] x ∈ (⋃ v, joinSets T P n v) := by rw [joinSets_iUnion]; trivial
        obtain ⟨v, hv⟩ := Set.mem_iUnion.mp h
        exact Set.mem_iUnion.mpr ⟨v, hv⟩
  have hBeq : Hfam μ (fun v : Fin n → Fin P.n => T^[m] ⁻¹' joinSets T P n v)
      = Hfam μ (joinSets T P n) := by
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [MeasurePreserving.measure_preimage (hmp.iterate m)
      (joinSets_measurable hT P n v).nullMeasurableSet]
  have hsplit : Hfam μ (joinSets T P (m + n)) =
      Hfam μ (fun q : (Fin m → Fin P.n) × (Fin n → Fin P.n) =>
        joinSets T P m q.1 ∩ T^[m] ⁻¹' joinSets T P n q.2) := by
    rw [← Hfam_equiv μ (Fin.appendEquiv (α := Fin P.n) m n) (joinSets T P (m + n))]
    refine Finset.sum_congr rfl fun q _ => ?_
    dsimp only
    rw [show joinSets T P (m + n) (Fin.appendEquiv (α := Fin P.n) m n q) =
        joinSets T P m q.1 ∩ T^[m] ⁻¹' joinSets T P n q.2 from
      joinSets_append T P m n q.1 q.2]
  calc Hfam μ (joinSets T P (m + n))
      = Hfam μ (fun q : (Fin m → Fin P.n) × (Fin n → Fin P.n) =>
          joinSets T P m q.1 ∩ T^[m] ⁻¹' joinSets T P n q.2) := hsplit
    _ ≤ Hfam μ (joinSets T P m) + Hfam μ (fun v => T^[m] ⁻¹' joinSets T P n v) :=
        Hfam_inter_le μ (joinSets_isMPart hT P m) hBmp
    _ = Hfam μ (joinSets T P m) + Hfam μ (joinSets T P n) := by rw [hBeq]

theorem Hfam_joinSets_mono (μ : Measure X) [IsProbabilityMeasure μ] {T : X → X}
    (hT : Measurable T) (P : FinPart X) (N : ℕ) :
    Hfam μ (joinSets T P N) ≤ Hfam μ (joinSets T P (N + 1)) :=
  Hfam_mono μ (joinSets_isMPart hT P N) (joinSets_isMPart hT P (N+1))
    (fun v => fun k => v (Fin.castSucc k)) (fun v => joinSets_succ_subset T P N v)

/-! ## 8. Fekete's lemma for `hPart` -/

theorem hPart_eq_lim (μ : Measure X) [IsProbabilityMeasure μ] {T : X → X}
    (hmp : MeasurePreserving T μ μ) (P : FinPart X)
    (hsub : Subadditive (fun N => Hfam μ (joinSets T P N))) :
    hPart μ T P = Subadditive.lim hsub := by
  have hbdd : BddBelow (Set.range fun n : ℕ => Hfam μ (joinSets T P n) / n) := by
    refine ⟨0, ?_⟩
    rintro y ⟨n, rfl⟩
    rcases eq_or_ne n 0 with h | h
    · simp [h]
    · exact div_nonneg (Hfam_nonneg μ _) (Nat.cast_nonneg n)
  have hlim := hsub.tendsto_lim hbdd
  have hbdd' : BddBelow (Set.range fun N : ℕ =>
      Hfam μ (joinSets T P (N + 1)) / ((N : ℝ) + 1)) := by
    refine ⟨0, ?_⟩
    rintro y ⟨N, rfl⟩
    exact div_nonneg (Hfam_nonneg μ _) (by positivity)
  refine le_antisymm ?_ ?_
  · by_contra hcon
    rw [not_le] at hcon
    set δ : ℝ := (hPart μ T P - Subadditive.lim hsub) / 2 with hδ
    have hδpos : 0 < δ := by rw [hδ]; linarith
    have hev : ∀ᶠ n : ℕ in atTop,
        Hfam μ (joinSets T P n) / n < Subadditive.lim hsub + δ :=
      hlim.eventually (isOpen_Iio.mem_nhds
        (lt_add_of_pos_right (Subadditive.lim hsub) hδpos))
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hev
    have h1 : hPart μ T P ≤ Hfam μ (joinSets T P (N₀ + 1)) / ((N₀ : ℝ) + 1) :=
      ciInf_le hbdd' N₀
    have h2 : Hfam μ (joinSets T P (N₀ + 1)) / ((N₀ : ℝ) + 1)
        < Subadditive.lim hsub + δ := by
      have := hN₀ (N₀ + 1) (by omega)
      simpa [Nat.cast_add, Nat.cast_one] using this
    rw [hδ] at h2
    linarith
  · refine le_ciInf fun N => ?_
    have := hsub.lim_le_div hbdd (show N + 1 ≠ 0 by omega)
    simpa [Nat.cast_add, Nat.cast_one] using this

theorem hPart_nonneg (μ : Measure X) [IsProbabilityMeasure μ] (T : X → X) (P : FinPart X) :
    0 ≤ hPart μ T P :=
  le_ciInf fun N => div_nonneg (Hfam_nonneg μ _) (by positivity)

theorem hPart_le_avg (μ : Measure X) [IsProbabilityMeasure μ] (T : X → X) (P : FinPart X)
    (N : ℕ) : hPart μ T P ≤ Hfam μ (joinSets T P (N + 1)) / ((N : ℝ) + 1) := by
  refine ciInf_le ?_ N
  refine ⟨0, ?_⟩
  rintro y ⟨M, rfl⟩
  exact div_nonneg (Hfam_nonneg μ _) (by positivity)

end Work.EKLComp.Core
