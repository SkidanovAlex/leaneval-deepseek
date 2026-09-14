import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Order.CompletePartialOrder

/-!
# Analytic sets have measurable hulls with null complement

The main result is `analyticSet_exists_measurable_hull`: in a Polish space, an analytic set
admits a Borel superset which differs from it by a null set.

The proof follows the classical route: analytic sets are the results of the Suslin operation
applied to a (decreasing) scheme of Borel sets, and the μ-completion of the Borel σ-algebra is
closed under the Suslin operation (Szpilrajn–Marczewski).
-/

open MeasureTheory Set
open scoped ENNReal Topology

set_option linter.unusedSimpArgs false

namespace Commons.Measure.Analytic

variable {α : Type*}

/-! ## The Suslin operation on `List ℕ`-indexed schemes -/

/-- The prefix of length `n` of a sequence, as a list. -/
def pre (x : ℕ → ℕ) (n : ℕ) : List ℕ := List.ofFn (fun i : Fin n => x i)

@[simp] lemma pre_zero (x : ℕ → ℕ) : pre x 0 = [] := rfl

lemma pre_succ (x : ℕ → ℕ) (n : ℕ) : pre x (n + 1) = x 0 :: pre (fun k => x (k + 1)) n := by
  simp [pre, List.ofFn_succ]

lemma pre_succ_last (x : ℕ → ℕ) : ∀ n, pre x (n + 1) = pre x n ++ [x n]
  | 0 => by simp [pre]
  | (n + 1) => by
    rw [pre_succ x (n + 1), pre_succ x n, pre_succ_last (fun k => x (k + 1)) n,
      List.cons_append]

/-- The cylinder of a list `s`: the set of sequences whose `s.length`-prefix equals `s`. -/
def cyl (s : List ℕ) : Set (ℕ → ℕ) := {x | pre x s.length = s}

lemma cyl_pre (x : ℕ → ℕ) (n : ℕ) : cyl (pre x n) = PiNat.cylinder x n := by
  have hlen : (pre x n).length = n := List.length_ofFn
  ext y
  rw [PiNat.mem_cylinder_iff]
  constructor
  · intro h i hi
    have h' : pre y n = pre x n := by
      simpa only [cyl, Set.mem_ofPred_eq, hlen] using h
    exact congrFun (List.ofFn_inj.mp h') ⟨i, hi⟩
  · intro h
    have h' : (fun i : Fin n => y i) = (fun i : Fin n => x i) := funext fun i => h i i.isLt
    have : pre y n = pre x n := List.ofFn_inj.mpr h'
    simpa only [cyl, Set.mem_ofPred_eq, hlen] using this

/-- The Suslin operation applied to a scheme `P`. -/
def suslin (P : List ℕ → Set α) : Set α :=
  ⋃ x : ℕ → ℕ, ⋂ n : ℕ, P (pre x n)

lemma suslin_mono {P Q : List ℕ → Set α} (h : ∀ s, P s ⊆ Q s) : suslin P ⊆ suslin Q := by
  intro y hy
  simp only [suslin, mem_iUnion, mem_iInter] at hy ⊢
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, fun n => h _ (hx n)⟩

lemma suslin_subset_apply (P : List ℕ → Set α) : suslin P ⊆ P [] := by
  intro y hy
  simp only [suslin, mem_iUnion, mem_iInter] at hy
  obtain ⟨x, hx⟩ := hy
  simpa using hx 0

/-- If `P s = ⋃ i, P (s ++ [i])` for all `s`, then the Suslin operation of `P` is `P []`. -/
lemma suslin_eq_of_append (P : List ℕ → Set α)
    (h : ∀ s : List ℕ, P s = ⋃ i : ℕ, P (s ++ [i])) :
    suslin P = P [] := by
  apply Subset.antisymm
  · exact suslin_subset_apply P
  · intro y hy
    simp only [suslin, mem_iUnion, mem_iInter]
    classical
    have child : ∀ s : List ℕ, y ∈ P s → ∃ i : ℕ, y ∈ P (s ++ [i]) := by
      intro s hs
      have h1 : y ∈ ⋃ i : ℕ, P (s ++ [i]) := by rw [← h s]; exact hs
      exact mem_iUnion.mp h1
    let step : {s : List ℕ // y ∈ P s} → {s : List ℕ // y ∈ P s} :=
      fun ih => ⟨ih.1 ++ [Classical.choose (child ih.1 ih.2)],
        Classical.choose_spec (child ih.1 ih.2)⟩
    let G : ℕ → {s : List ℕ // y ∈ P s} :=
      fun n => Nat.rec ⟨[], by simpa using hy⟩ (fun _ ih => step ih) n
    let x : ℕ → ℕ := fun n => Classical.choose (child (G n).1 (G n).2)
    have hGx : ∀ n, (G n).1 = pre x n := by
      intro n
      induction n with
      | zero => simp [G, pre]
      | succ k ih =>
        have : (G (k+1)).1 = (G k).1 ++ [x k] := rfl
        rw [this, ih, pre_succ_last]
    exact ⟨x, fun n => by rw [← hGx n]; exact (G n).2⟩

/-- Every continuous image of the Baire space is the Suslin operation, over the decreasing scheme
of closures of images of cylinders, of closed (hence Borel) sets. -/
theorem range_eq_suslin_closure [TopologicalSpace α] [T2Space α]
    (f : (ℕ → ℕ) → α) (hf : Continuous f) :
    range f = suslin (fun s => closure (f '' cyl s)) := by
  apply Subset.antisymm
  · rintro y ⟨x, rfl⟩
    simp only [suslin, mem_iUnion, mem_iInter]
    refine ⟨x, fun n => ?_⟩
    exact subset_closure ⟨x, by simp [cyl, pre], rfl⟩
  · intro y hy
    simp only [suslin, mem_iUnion, mem_iInter] at hy
    obtain ⟨x, hx⟩ := hy
    by_contra hne
    rw [mem_range] at hne
    push Not at hne
    obtain ⟨uf, uy, hufo, huyo, hfxu, hyuy, hdisj⟩ := t2_separation (hne x)
    have hfxn : f ⁻¹' uf ∈ 𝓝 x := hf.continuousAt (IsOpen.mem_nhds hufo hfxu)
    obtain ⟨w, hwsub, hwopen, hxw⟩ := mem_nhds_iff.mp hfxn
    obtain ⟨t, ht, hxt, htw⟩ :=
      (PiNat.isTopologicalBasis_cylinders (fun _ : ℕ => ℕ)).exists_subset_of_mem_open hxw hwopen
    obtain ⟨z, n, rfl⟩ := ht
    have hzx : PiNat.cylinder z n = PiNat.cylinder x n := PiNat.mem_cylinder_iff_eq.mp hxt |>.symm
    rw [hzx] at htw
    have hsub : f '' PiNat.cylinder x n ⊆ uf := image_subset_iff.mpr (htw.trans hwsub)
    have hcl : closure (f '' PiNat.cylinder x n) ⊆ uyᶜ := by
      refine closure_minimal ?_ huyo.isClosed_compl
      intro a ha hay
      exact Set.disjoint_left.mp hdisj (hsub ha) hay
    have : y ∉ closure (f '' PiNat.cylinder x n) := fun hyc => hcl hyc hyuy
    apply this
    have h2 := hx n
    rw [cyl_pre x n] at h2
    exact h2

lemma pre_add (x : ℕ → ℕ) (n : ℕ) (m : ℕ) :
    pre x (n + m) = pre x n ++ pre (fun k => x (n + k)) m := by
  induction m with
  | zero => simp [pre]
  | succ m ih =>
    rw [Nat.add_succ, pre_succ_last x (n + m), ih, pre_succ_last (fun k => x (n + k)) m]
    simp [List.append_assoc]

lemma cyl_append_subset (t : List ℕ) (i : ℕ) : cyl (t ++ [i]) ⊆ cyl t := by
  intro x hx
  simp only [cyl, Set.mem_ofPred_eq] at hx ⊢
  rw [List.length_append, List.length_singleton, pre_succ_last] at hx
  have h := congrArg List.dropLast hx
  simp only [List.dropLast_append, List.isEmpty_cons, Bool.false_eq_true, if_false,
    List.dropLast_singleton, List.append_nil] at h
  exact h

/-- An analytic set in a Hausdorff space is the Suslin operation of a decreasing scheme of
closed sets. -/
lemma exists_suslin_eq_of_analytic {s : Set α} [TopologicalSpace α] [T2Space α]
    (hs : MeasureTheory.AnalyticSet s) :
    ∃ P : List ℕ → Set α, (∀ t, IsClosed (P t)) ∧ (∀ t i, P (t ++ [i]) ⊆ P t) ∧
      suslin P = s := by
  rcases MeasureTheory.analyticSet_iff_exists_polishSpace_range.mp hs with
    ⟨β, tβ, hpol, f, hfc, hfr⟩
  letI := tβ
  haveI := hpol
  rcases isEmpty_or_nonempty β with hem | hne
  · have hrange : range f = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      rintro x ⟨b, -⟩
      exact (hem.false b).elim
    refine ⟨fun _ => (∅ : Set α), fun t => isClosed_empty, fun t i => by simp, ?_⟩
    rw [← hfr, hrange]
    ext y
    simp [suslin]
  · obtain ⟨g, hgc, hgsurj⟩ := PolishSpace.exists_nat_nat_continuous_surjective β
    refine ⟨fun t => closure ((f ∘ g) '' cyl t), fun t => isClosed_closure, fun t i => ?_, ?_⟩
    · exact closure_mono (Set.image_mono (cyl_append_subset t i))
    · rw [← range_eq_suslin_closure (f ∘ g) (hfc.comp hgc), hgsurj.range_comp, hfr]


section Measure

variable [MeasurableSpace α]

/-- `B` is a `μ`-envelope of `A` if it is null measurable, contains `A`, and every null
measurable subset of `B \ A` is null. -/
def IsEnvelope (μ : Measure α) (A B : Set α) : Prop :=
  NullMeasurableSet B μ ∧ A ⊆ B ∧ ∀ C, C ⊆ B \ A → NullMeasurableSet C μ → μ C = 0

/-- `toMeasurable μ A` is a `μ`-envelope of `A` for a finite measure `μ`. -/
lemma isEnvelope_toMeasurable (μ : Measure α) [IsFiniteMeasure μ] (A : Set α) :
    IsEnvelope μ A (toMeasurable μ A) := by
  refine ⟨(measurableSet_toMeasurable μ A).nullMeasurableSet, subset_toMeasurable μ A, ?_⟩
  intro C hC hCnm
  have hAC : A ⊆ toMeasurable μ A \ C := fun x hx => ⟨subset_toMeasurable μ A hx, fun hxC => hC hxC |>.2 hx⟩
  have hge : μ (toMeasurable μ A) ≤ μ (toMeasurable μ A \ C) := by
    rw [measure_toMeasurable]
    exact measure_mono hAC
  have hle : μ (toMeasurable μ A \ C) ≤ μ (toMeasurable μ A) := measure_mono sdiff_subset
  have heq : μ (toMeasurable μ A \ C) = μ (toMeasurable μ A) := le_antisymm hle hge
  have hadd := measure_inter_add_sdiff₀ (toMeasurable μ A) hCnm
  rw [Set.inter_eq_right.mpr (hC.trans sdiff_subset), heq] at hadd
  have hBne : μ (toMeasurable μ A) ≠ ⊤ := (measure_lt_top _ _).ne
  exact (ENNReal.add_left_inj hBne).mp (hadd.trans (zero_add _).symm)

/-- Envelopes of the same set have the same measure up to a null difference. -/
lemma IsEnvelope.sdiff_null {μ : Measure α} {A B₁ B₂ : Set α}
    (h₁ : IsEnvelope μ A B₁) (h₂ : IsEnvelope μ A B₂) : μ (B₁ \ B₂) = 0 := by
  refine h₁.2.2 (B₁ \ B₂) ?_ (h₁.1.diff h₂.1)
  exact fun x hx => ⟨hx.1, fun hxA => hx.2 (h₂.2.1 hxA)⟩

lemma IsEnvelope.symmDiff_null {μ : Measure α} {A B₁ B₂ : Set α}
    (h₁ : IsEnvelope μ A B₁) (h₂ : IsEnvelope μ A B₂) : μ (symmDiff B₁ B₂) = 0 := by
  have hsymm : symmDiff B₁ B₂ = (B₁ \ B₂) ∪ (B₂ \ B₁) := by rw [symmDiff_def]; rfl
  rw [hsymm]
  refine le_antisymm ?_ bot_le
  refine (measure_union_le _ _).trans ?_
  rw [h₁.sdiff_null h₂, h₂.sdiff_null h₁, add_zero]

/-- **Szpilrajn–Marczewski**: for a finite measure, the `μ`-completion of a σ-algebra is closed
under the Suslin operation applied to a decreasing scheme of null measurable sets. -/
theorem suslin_nullMeasurable_of_decreasing (μ : Measure α) [IsFiniteMeasure μ]
    (P : List ℕ → Set α) (hP : ∀ s, NullMeasurableSet (P s) μ)
    (hdec : ∀ s i, P (s ++ [i]) ⊆ P s) :
    NullMeasurableSet (suslin P) μ := by
  classical
  let Ptil : List ℕ → Set α := fun s => suslin (fun t => P (s ++ t))
  have hPtil_sub : ∀ s, Ptil s ⊆ P s := by
    intro s
    simpa [Ptil] using suslin_subset_apply (fun t => P (s ++ t))
  have hPtil_dec : ∀ s i, Ptil (s ++ [i]) ⊆ Ptil s := by
    intro s i y hy
    simp only [Ptil, suslin, mem_iUnion, mem_iInter] at hy ⊢
    obtain ⟨z, hz⟩ := hy
    refine ⟨fun n => match n with | 0 => i | (k + 1) => z k, ?_⟩
    intro n
    cases n with
    | zero =>
      have h0 : y ∈ P (s ++ [i]) := by simpa [pre] using hz 0
      simpa [pre] using hdec s i h0
    | succ k =>
      have hpre : pre (fun n => match n with | 0 => i | (k + 1) => z k) (k + 1)
          = i :: pre z k := by
        rw [pre_succ]
      rw [hpre]
      have hk := hz k
      simpa only [List.append_assoc, List.singleton_append] using hk
  have hPtil_union : ∀ s, Ptil s ⊆ ⋃ i, Ptil (s ++ [i]) := by
    intro s y hy
    simp only [Ptil, suslin, mem_iUnion, mem_iInter] at hy ⊢
    obtain ⟨x, hx⟩ := hy
    refine ⟨x 0, fun k => x (k + 1), fun n => ?_⟩
    have h := hx (n + 1)
    rw [pre_succ] at h
    simpa only [List.append_assoc, List.singleton_append] using h
  let Q : List ℕ → Set α := fun s => toMeasurable μ (Ptil s) ∩ P s
  have hQ_nm : ∀ s, NullMeasurableSet (Q s) μ := fun s =>
    ((measurableSet_toMeasurable μ (Ptil s)).nullMeasurableSet).inter (hP s)
  have hQ_env : ∀ s, IsEnvelope μ (Ptil s) (Q s) := by
    intro s
    refine ⟨hQ_nm s, fun x hx => ⟨subset_toMeasurable μ (Ptil s) hx, hPtil_sub s hx⟩, ?_⟩
    intro C hC hCnm
    refine (isEnvelope_toMeasurable μ (Ptil s)).2.2 C ?_ hCnm
    exact fun x hx => ⟨(hC hx).1.1, (hC hx).2⟩
  have hUnionEnv : ∀ s, IsEnvelope μ (Ptil s) (⋃ i, Q (s ++ [i])) := by
    intro s
    refine ⟨NullMeasurableSet.iUnion (fun i => hQ_nm _), ?_, ?_⟩
    · intro x hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hPtil_union s hx)
      exact mem_iUnion.mpr ⟨i, (hQ_env (s ++ [i])).2.1 hi⟩
    · intro C hC hCnm
      have hCeq : C = ⋃ i, (C ∩ Q (s ++ [i])) := by
        ext x
        constructor
        · intro hx
          obtain ⟨i, hi⟩ := mem_iUnion.mp (hC hx).1
          exact mem_iUnion.mpr ⟨i, ⟨hx, hi⟩⟩
        · intro hx
          obtain ⟨i, hi⟩ := mem_iUnion.mp hx
          exact hi.1
      rw [hCeq]
      refine le_antisymm ?_ bot_le
      calc μ (⋃ i, (C ∩ Q (s ++ [i]))) ≤ ∑' i, μ (C ∩ Q (s ++ [i])) := measure_iUnion_le _
        _ = 0 := by
          rw [ENNReal.tsum_eq_zero]
          intro i
          exact (hQ_env (s ++ [i])).2.2 (C ∩ Q (s ++ [i]))
            (fun x hx => ⟨hx.2, fun hxP => (hC hx.1).2 (hPtil_dec s i hxP)⟩)
            (hCnm.inter (hQ_nm _))
  let N : Set α := ⋃ s : List ℕ, symmDiff (Q s) (⋃ i, Q (s ++ [i]))
  have hNnm : NullMeasurableSet N μ :=
    NullMeasurableSet.iUnion fun s => (hQ_nm s).symmDiff (NullMeasurableSet.iUnion fun i => hQ_nm _)
  have hNzero : μ N = 0 :=
    measure_iUnion_null fun s => (hQ_env s).symmDiff_null (hUnionEnv s)
  let Q' : List ℕ → Set α := fun s => Q s ∩ Nᶜ
  have hQ'nm : ∀ s, NullMeasurableSet (Q' s) μ := fun s => (hQ_nm s).inter hNnm.compl
  have hQ'eq : ∀ s, Q' s = ⋃ i, Q' (s ++ [i]) := by
    intro s
    ext x
    by_cases hxN : x ∈ N
    · exact ⟨fun hx => absurd hxN hx.2, fun hx => by
        obtain ⟨i, hi⟩ := mem_iUnion.mp hx; exact absurd hxN hi.2⟩
    · have hiff : x ∈ Q s ↔ x ∈ ⋃ i, Q (s ++ [i]) := by
        have hmem : x ∉ symmDiff (Q s) (⋃ i, Q (s ++ [i])) :=
          fun h => hxN (mem_iUnion.mpr ⟨s, h⟩)
        rw [mem_symmDiff] at hmem
        tauto
      exact ⟨fun hx => by
          obtain ⟨i, hi⟩ := mem_iUnion.mp (hiff.mp hx.1)
          exact mem_iUnion.mpr ⟨i, hi, hx.2⟩,
        fun hx => by
          obtain ⟨i, hi, hiN⟩ := mem_iUnion.mp hx
          exact ⟨hiff.mpr (mem_iUnion.mpr ⟨i, hi⟩), hiN⟩⟩
  have hsuslinQ' : NullMeasurableSet (suslin Q') μ := by
    rw [suslin_eq_of_append Q' hQ'eq]
    exact hQ'nm []
  have hsub : suslin P ⊆ suslin Q' ∪ N := by
    intro y hy
    simp only [suslin, mem_iUnion, mem_iInter] at hy
    obtain ⟨x, hx⟩ := hy
    by_cases hxN : y ∈ N
    · exact Or.inr hxN
    · refine Or.inl ?_
      simp only [suslin, mem_iUnion, mem_iInter]
      refine ⟨x, fun n => ?_⟩
      have hPtilmem : y ∈ Ptil (pre x n) := by
        simp only [Ptil, suslin, mem_iUnion, mem_iInter]
        refine ⟨fun k => x (n + k), fun m => ?_⟩
        have h := hx (n + m)
        rwa [pre_add x n m] at h
      exact ⟨(hQ_env (pre x n)).2.1 hPtilmem, hxN⟩
  have hQ'subP : ∀ s, Q' s ⊆ P s := fun s x hx => hx.1.2
  have hsub2 : suslin Q' ⊆ suslin P := suslin_mono hQ'subP
  have hfin : suslin P = suslin Q' ∪ (suslin P \ suslin Q') :=
    (Set.union_sdiff_cancel hsub2).symm
  rw [hfin]
  refine NullMeasurableSet.union_null hsuslinQ' ?_
  refine le_antisymm ?_ bot_le
  calc μ (suslin P \ suslin Q') ≤ μ N := measure_mono fun x hx => (hsub hx.1).resolve_left hx.2
    _ = 0 := hNzero

/-- From a null measurable set one extracts a measurable superset differing by a null set. -/
lemma nullMeasurable_exists_hull (μ : Measure α) {s : Set α} (hs : NullMeasurableSet s μ) :
    ∃ t, MeasurableSet t ∧ s ⊆ t ∧ μ (t \ s) = 0 := by
  obtain ⟨t, hst, htm, hae⟩ := hs.exists_measurable_superset_ae_eq
  exact ⟨t, htm, hst, (ae_eq_set.mp hae).1⟩


end Measure

theorem analyticSet_exists_measurable_hull {α : Type*} [TopologicalSpace α] [PolishSpace α]
    [MeasurableSpace α] [BorelSpace α] (μ : MeasureTheory.Measure α) [MeasureTheory.SigmaFinite μ]
    {s : Set α} (hs : MeasureTheory.AnalyticSet s) :
    ∃ t, MeasurableSet t ∧ s ⊆ t ∧ μ (t \ s) = 0 := by
  classical
  obtain ⟨P, hclosed, hdec, hsuslin⟩ := exists_suslin_eq_of_analytic hs
  have hex : ∀ n, ∃ u : Set α, MeasurableSet u ∧ s ⊆ u ∧
      (μ.restrict (spanningSets μ n)) (u \ s) = 0 := by
    intro n
    haveI : IsFiniteMeasure (μ.restrict (spanningSets μ n)) :=
      isFiniteMeasure_restrict.2 (measure_spanningSets_lt_top μ n).ne
    have hnm : NullMeasurableSet (suslin P) (μ.restrict (spanningSets μ n)) :=
      suslin_nullMeasurable_of_decreasing (μ.restrict (spanningSets μ n)) P
        (fun t => (hclosed t).measurableSet.nullMeasurableSet) hdec
    rw [hsuslin] at hnm
    exact nullMeasurable_exists_hull _ hnm
  choose u hu using hex
  refine ⟨⋃ n, (u n ∩ spanningSets μ n),
    MeasurableSet.iUnion fun n => (hu n).1.inter (measurableSet_spanningSets μ n), ?_, ?_⟩
  · intro x hx
    have hxU : x ∈ ⋃ n, spanningSets μ n := by rw [iUnion_spanningSets]; exact mem_univ x
    obtain ⟨n, hn⟩ := mem_iUnion.mp hxU
    exact mem_iUnion.mpr ⟨n, ⟨(hu n).2.1 hx, hn⟩⟩
  · rw [Set.iUnion_sdiff]
    refine le_antisymm ?_ bot_le
    calc μ (⋃ n, (u n ∩ spanningSets μ n) \ s)
        ≤ ∑' n, μ ((u n ∩ spanningSets μ n) \ s) := measure_iUnion_le _
      _ = 0 := by
        rw [ENNReal.tsum_eq_zero]
        intro n
        have hset : (u n ∩ spanningSets μ n) \ s = (u n \ s) ∩ spanningSets μ n := by
          ext x; simp only [mem_sdiff, mem_inter_iff]; tauto
        rw [hset, ← Measure.restrict_apply' (measurableSet_spanningSets μ n)]
        exact (hu n).2.2

end Commons.Measure.Analytic