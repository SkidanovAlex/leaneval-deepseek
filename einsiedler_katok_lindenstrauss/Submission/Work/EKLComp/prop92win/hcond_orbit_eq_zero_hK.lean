import Mathlib
import Submission.Work.EKLComp.prop92defs
import Submission.Work.EKLComp.uniform_inj_of_isCompact
import Submission.Work.EKLComp.orbitSigma_countable
import Submission.Work.EKLComp.recurrence_family
import Submission.Work.EKLComp.ball_nhds
import Submission.Work.EKLComp.tube_open
import Submission.Work.EKLComp.Hcond_eq_zero_of_atom_subset
import Submission.Work.EKLComp.inv_mem_V
import Submission.Work.EKLComp.dense_Csub_seq
import Submission.Work.EKLC6Core.Hcond_mono
import Submission.Work.EKLComp.hPart_le_add_Hcond

/-!
# EKL Prop. 9.2, Step 4: the relative entropy vanishes

`hcond_orbit_eq_zero_hK`: for an `aDiag t`-invariant probability `ν` with `ν K = 1`, a partition
`P` whose atoms are `V δ`-small on the bi-invariant compact set `K`, and a partition `Q` with
`ν`-null frontiers, the relative entropy `H_ν(Q | orbitΣ P ∨ pastΣ Q)` vanishes:
the atoms of the bigger σ-algebra refine the `Q`-parts.

The proof is EKL §9 (the Poincaré-recurrence argument): two points `x, y ∈ K` in a common atom
differ by `c ∈ C_{SL₃}(aDiag t)` (the core claim `sameItin_central_gen`); a rational approximation
`g` of `c` (with `g⁻¹ c` as small as we like) and Poincaré recurrence for the countable family of
sets "the whole `V θ`-ball around `z` lies in `int Q_i` and its `g`-image in `int Q_j`" then force
the two parts to coincide.
-/

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal

noncomputable section

namespace Work.EKLComp

open Work.EKLContract


/-- If every set in `S` is `ν`-null or `ν`-conull, then every set measurable for
`(orbitSigma t P ⊔ pastSig t Q) ⊔ generateFrom S` is a.e. equal to a
`orbitSigma t P ⊔ pastSig t Q`-measurable set.  (The two σ-algebras only differ by a.e. trivial
sets.) -/
theorem ae_eq_measurableSet_of_generate_X3 (t : Fin 3 → ℝ) (P Q : FinPart X3)
    (ν : Measure X3) [IsProbabilityMeasure ν] {S : Set (Set X3)}
    (hS : ∀ s ∈ S, MeasurableSet s ∧ (ν s = 0 ∨ ν s = 1)) {s : Set X3}
    (hs : @MeasurableSet X3 ((orbitSigma t P ⊔ pastSig t Q) ⊔ MeasurableSpace.generateFrom S) s) :
    ∃ u : Set X3, @MeasurableSet X3 (orbitSigma t P ⊔ pastSig t Q) u ∧ s =ᵐ[ν] u := by
  set C : Set (Set X3) := {u : Set X3 | @MeasurableSet X3 (orbitSigma t P ⊔ pastSig t Q) u} ∪ S
    with hCdef
  have hgen : MeasurableSpace.generateFrom C
      = (orbitSigma t P ⊔ pastSig t Q) ⊔ MeasurableSpace.generateFrom S := by
    rw [hCdef, ← MeasurableSpace.generateFrom_sup_generateFrom,
      @MeasurableSpace.generateFrom_measurableSet X3 (orbitSigma t P ⊔ pastSig t Q)]
  have hs' : @MeasurableSet X3 (MeasurableSpace.generateFrom C) s := hgen.symm ▸ hs
  refine MeasurableSpace.generateFrom_induction C
    (fun s _ => ∃ u : Set X3,
      @MeasurableSet X3 (orbitSigma t P ⊔ pastSig t Q) u ∧ s =ᵐ[ν] u) ?_ ?_ ?_ ?_ s hs'
  · intro u hu _
    rcases hu with hu | hu
    · exact ⟨u, hu, Filter.EventuallyEq.rfl⟩
    · rcases (hS u hu).2 with h | h
      · exact ⟨∅, @MeasurableSet.empty X3 (orbitSigma t P ⊔ pastSig t Q),
          MeasureTheory.ae_eq_empty.mpr h⟩
      · refine ⟨Set.univ, @MeasurableSet.univ X3 (orbitSigma t P ⊔ pastSig t Q),
          MeasureTheory.ae_eq_univ.mpr ?_⟩
        rw [MeasureTheory.prob_compl_eq_one_sub (μ := ν) (s := u) (hS u hu).1, h]
        simp
  · exact ⟨∅, @MeasurableSet.empty X3 (orbitSigma t P ⊔ pastSig t Q),
      MeasureTheory.ae_eq_refl (μ := ν) (∅ : Set X3)⟩
  · rintro u _ ⟨w, hw, huw⟩
    exact ⟨wᶜ, hw.compl, MeasureTheory.ae_eq_set_compl_compl.mpr huw⟩
  · rintro f _ hPf
    choose u hu hua using hPf
    exact ⟨⋃ n, u n, MeasurableSet.iUnion hu, Filter.EventuallyEq.countable_iUnion hua⟩

/-- Adding an a.e. trivial σ-algebra to `orbitSigma t P ⊔ pastSig t Q` does not change the
conditional expectation. -/
theorem condExp_sup_eq_condExp_of_trivial_gens_X3 (t : Fin 3 → ℝ) (P Q : FinPart X3)
    (ν : Measure X3) [IsProbabilityMeasure ν] {S : Set (Set X3)}
    (hS : ∀ s ∈ S, MeasurableSet s ∧ (ν s = 0 ∨ ν s = 1)) (f : X3 → ℝ) (hf : Integrable f ν) :
    MeasureTheory.condExp ((orbitSigma t P ⊔ pastSig t Q) ⊔ MeasurableSpace.generateFrom S) ν f
      =ᵐ[ν] MeasureTheory.condExp (orbitSigma t P ⊔ pastSig t Q) ν f := by
  have hm : orbitSigma t P ⊔ pastSig t Q ≤ instMeasurableSpaceX3 :=
    sup_le (orbitSigma_le_ambient t P) (pastSig_le_ambient t Q)
  have hle : (orbitSigma t P ⊔ pastSig t Q) ⊔ MeasurableSpace.generateFrom S
      ≤ instMeasurableSpaceX3 :=
    sup_le hm (MeasurableSpace.generateFrom_le fun s hs => (hS s hs).1)
  haveI : SigmaFinite (ν.trim hle) := inferInstance
  haveI : SigmaFinite (ν.trim hm) := inferInstance
  refine (MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq (μ := ν)
    (m := (orbitSigma t P ⊔ pastSig t Q) ⊔ MeasurableSpace.generateFrom S) hle (f := f)
    (g := MeasureTheory.condExp (orbitSigma t P ⊔ pastSig t Q) ν f) hf ?_ ?_ ?_).symm
  · intro s _ _
    exact MeasureTheory.integrable_condExp.integrableOn
  · intro s hs _
    obtain ⟨u, hu, hsu⟩ := ae_eq_measurableSet_of_generate_X3 t P Q ν hS hs
    calc ∫ x in s, MeasureTheory.condExp (orbitSigma t P ⊔ pastSig t Q) ν f x ∂ν
        = ∫ x in u, MeasureTheory.condExp (orbitSigma t P ⊔ pastSig t Q) ν f x ∂ν :=
          MeasureTheory.setIntegral_congr_set hsu
      _ = ∫ x in u, f x ∂ν := MeasureTheory.setIntegral_condExp hm hf hu
      _ = ∫ x in s, f x ∂ν := (MeasureTheory.setIntegral_congr_set hsu).symm
  · have h1 : StronglyMeasurable[((orbitSigma t P ⊔ pastSig t Q)
        ⊔ MeasurableSpace.generateFrom S)]
        (MeasureTheory.condExp (orbitSigma t P ⊔ pastSig t Q) ν f) :=
      (MeasureTheory.stronglyMeasurable_condExp (m := orbitSigma t P ⊔ pastSig t Q) (μ := ν)
        (f := f)).mono (le_sup_left :
          orbitSigma t P ⊔ pastSig t Q ≤ ((orbitSigma t P ⊔ pastSig t Q)
            ⊔ MeasurableSpace.generateFrom S))
    exact h1.aestronglyMeasurable

/-- Adjoining the σ-algebra generated by `ν`-trivial sets does not change `Hcond`. -/
theorem Hcond_sup_trivial_gens_X3 (t : Fin 3 → ℝ) (P Q : FinPart X3) (ν : Measure X3)
    [IsProbabilityMeasure ν] {S : Set (Set X3)}
    (hS : ∀ s ∈ S, MeasurableSet s ∧ (ν s = 0 ∨ ν s = 1)) :
    @Hcond X3 instMeasurableSpaceX3 ν Q
        ((orbitSigma t P ⊔ pastSig t Q) ⊔ MeasurableSpace.generateFrom S)
      = @Hcond X3 instMeasurableSpaceX3 ν Q (orbitSigma t P ⊔ pastSig t Q) := by
  simp only [Hcond]
  refine MeasureTheory.integral_congr_ae ?_
  have hfi : ∀ i : Fin Q.n, Integrable ((Q.parts i).indicator (fun _ => (1 : ℝ))) ν :=
    fun i => (integrable_const (1 : ℝ)).indicator (Q.measurable i)
  have hB' : ∀ i : Fin Q.n,
      MeasureTheory.condExp ((orbitSigma t P ⊔ pastSig t Q) ⊔ MeasurableSpace.generateFrom S)
          ν ((Q.parts i).indicator (fun _ => (1 : ℝ)))
        =ᵐ[ν] MeasureTheory.condExp (orbitSigma t P ⊔ pastSig t Q) ν
          ((Q.parts i).indicator (fun _ => (1 : ℝ))) :=
    fun i => condExp_sup_eq_condExp_of_trivial_gens_X3 t P Q ν hS _ (hfi i)
  filter_upwards [Filter.eventually_all.2 hB'] with x hx
  exact Finset.sum_congr rfl (fun i _ => by rw [hx i])

variable {t : Fin 3 → ℝ}

namespace vanish

/-! ## 1. Small helpers -/

/-- `Hcond` is nonnegative. -/
theorem Hcond_nonneg {X : Type*} {m : MeasurableSpace X} [mX : MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (P : @FinPart X mX) (hm : m ≤ mX) :
    0 ≤ @Hcond X mX μ P m := by
  rw [Work.EKLC6Core.Hcond_eq_sum_integral (μ := μ) (m := m) P]
  have hPT : ∀ (j : Fin P.n) (x : X),
      (@FinPart.parts X mX P j).indicator (fun _ => (1 : ℝ)) x ∈ Set.Icc 0 1 := by
    intro j x
    by_cases h : x ∈ @FinPart.parts X mX P j
    · rw [Set.indicator_of_mem h]
      norm_num
    · rw [Set.indicator_of_notMem h]
      norm_num
  refine Finset.sum_nonneg fun i _ => integral_nonneg_of_ae ?_
  have hPi : MeasurableSet (@FinPart.parts X mX P i) := P.measurable i
  filter_upwards [Work.EKLC6Core.condExp_mem_Icc (μ := μ) (m := m) hm
    (f := (@FinPart.parts X mX P i).indicator (fun _ => (1 : ℝ)))
    (Filter.Eventually.of_forall fun x => (hPT i x).1)
    (Filter.Eventually.of_forall fun x => (hPT i x).2)
    ((integrable_const (1 : ℝ)).indicator hPi)] with x hx
  exact Real.negMulLog_nonneg hx.1 hx.2

/-- `aDiag (-t) •` is `shiftZ t (-1)`. -/
theorem aDiag_neg_eq_shiftZ (t : Fin 3 → ℝ) :
    (fun x : X3 => aDiag (-t) • x) = shiftZ t (-1) := by
  funext x
  have h : aZ t (-1) = aDiag (-t) := by
    rw [aZ]
    congr 1
    ext i
    simp
  simp only [shiftZ]
  rw [h]

/-- Integer iterates of `shiftZ t 1` are `aZ t n`. -/
theorem shiftZ_iterate_eq' (t : Fin 3 → ℝ) (n : ℕ) :
    (shiftZ t 1)^[n] = fun x : X3 => aZ t (n : ℤ) • x := by
  induction n with
  | zero =>
    funext x
    simp only [Function.iterate_zero, Nat.cast_zero, aZ_zero, one_smul]
    rfl
  | succ k ih =>
    funext x
    rw [Function.iterate_succ_apply',
      show ((shiftZ t 1)^[k]) x = aZ t (k : ℤ) • x from congrFun ih x]
    show aZ t 1 • (aZ t (k : ℤ) • x) = aZ t (((k + 1 : ℕ)) : ℤ) • x
    rw [← mul_smul, ← aZ_add]
    congr 2
    push_cast
    ring

/-- Conjugation and the action. -/
theorem aZ_smul_conj' (t : Fin 3 → ℝ) (n : ℤ) (f : SL3) (x : X3) :
    aZ t n • (f • x) = conjZ t n f • (aZ t n • x) := by
  rw [conjZ]
  calc aZ t n • (f • x) = (aZ t n * f) • x := (mul_smul _ _ _).symm
    _ = ((aZ t n * f * (aZ t n)⁻¹) * aZ t n) • x := by
        congr 1
        group
    _ = (aZ t n * f * (aZ t n)⁻¹) • (aZ t n • x) := mul_smul _ _ _

/-- An element of the centraliser commutes with all iterates of `shiftZ t 1`. -/
theorem Csub_smul_shiftZ_iterate (t : Fin 3 → ℝ) {c : SL3} (hc : c ∈ Csub t) (n : ℕ) (x : X3) :
    c • ((shiftZ t 1)^[n] x) = (shiftZ t 1)^[n] (c • x) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    show c • (aZ t 1 • ((shiftZ t 1)^[k] x)) = aZ t 1 • (c • ((shiftZ t 1)^[k] x))
    rw [← mul_smul, ← mul_smul,
      show c * aZ t 1 = aZ t 1 * c from (Csub_comm t hc 1).symm]

/-! ## 2. The closed box and the recurrence sets -/

/-- The closed entrywise box of radius `θ` around the identity (compact). -/
def cbox (θ : ℝ) : Set SL3 := {g : SL3 | ∀ i j, |g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ θ}

theorem isCompact_cbox (θ : ℝ) : IsCompact (cbox θ) := by
  have heq : cbox θ = {g : SL3 | ∀ i j, ((1 : Matrix (Fin 3) (Fin 3) ℝ) i j - θ) ≤ g i j ∧
      g i j ≤ ((1 : Matrix (Fin 3) (Fin 3) ℝ) i j + θ)} := by
    ext g
    constructor
    · intro h i j
      have h' := h i j
      rw [abs_le] at h'
      exact ⟨by linarith [h'.1], by linarith [h'.2]⟩
    · intro h i j
      have h' := h i j
      rw [abs_le]
      exact ⟨by linarith [h'.1], by linarith [h'.2]⟩
  rw [heq]
  exact Work.EKLProd.sl3EntryBox_compact _ _

theorem V_subset_cbox (θ : ℝ) : V θ ⊆ cbox θ := fun g hg i j => le_of_lt (hg i j)

theorem one_mem_cbox {θ : ℝ} (hθ : 0 ≤ θ) : (1 : SL3) ∈ cbox θ := by
  intro i j
  have h1 : (1 : SL3) i j = (1 : Matrix (Fin 3) (Fin 3) ℝ) i j := rfl
  rw [h1, sub_self, abs_zero]
  exact hθ

/-- The recurrence sets: the whole `cbox θ`-ball around `z` stays in `interior (Q.parts i)`, and
its image under `g` stays in `interior (Q.parts j)`. -/
def Bset (Q : FinPart X3) (i j : Fin Q.n) (g : SL3) (θ : ℝ) : Set X3 :=
  {z | (∀ h ∈ cbox θ, h • z ∈ interior (Q.parts i)) ∧
       (∀ h ∈ cbox θ, (g * h) • z ∈ interior (Q.parts j))}

theorem isOpen_Bset (Q : FinPart X3) (i j : Fin Q.n) (g : SL3) (θ : ℝ) :
    IsOpen (Bset Q i j g θ) := by
  have h1 : IsOpen {z : X3 | ∀ h ∈ cbox θ, h • z ∈ interior (Q.parts i)} :=
    tube_open (isCompact_cbox θ) isOpen_interior
  have himg : {z : X3 | ∀ h ∈ cbox θ, (g * h) • z ∈ interior (Q.parts j)}
      = {z : X3 | ∀ l ∈ (fun h : SL3 => g * h) '' (cbox θ), l • z ∈ interior (Q.parts j)} := by
    ext z
    constructor
    · rintro hz l ⟨h, hh, rfl⟩
      exact hz h hh
    · intro hz h hh
      exact hz (g * h) ⟨h, hh, rfl⟩
  have h2 : IsOpen {z : X3 | ∀ h ∈ cbox θ, (g * h) • z ∈ interior (Q.parts j)} := by
    rw [himg]
    exact tube_open ((isCompact_cbox θ).image (by fun_prop)) isOpen_interior
  exact h1.inter h2

theorem measurableSet_Bset (Q : FinPart X3) (i j : Fin Q.n) (g : SL3) (θ : ℝ) :
    MeasurableSet (Bset Q i j g θ) :=
  (isOpen_Bset Q i j g θ).measurableSet

/-! ## 3. The atom of the past σ-algebra gives the itinerary -/

theorem mem_same_part_of_mem_pastSig_atomG (t : Fin 3 → ℝ) (Q : FinPart X3) {x y : X3}
    (h : y ∈ atomGen (pastSig t Q) x) (n : ℕ) :
    ∃ i : Fin Q.n, (shiftZ t 1)^[n+1] x ∈ Q.parts i ∧ (shiftZ t 1)^[n+1] y ∈ Q.parts i := by
  have hle : MeasurableSpace.comap ((shiftZ t 1)^[n+1]) (partSigma Q) ≤ pastSig t Q :=
    le_iSup (fun n : ℕ => MeasurableSpace.comap ((shiftZ t 1)^[n+1]) (partSigma Q)) n
  have hy : y ∈ atomGen (MeasurableSpace.comap ((shiftZ t 1)^[n+1]) (partSigma Q)) x :=
    atomGen_anti hle x h
  have hy2 : ((shiftZ t 1)^[n+1]) y ∈ atomGen (partSigma Q) (((shiftZ t 1)^[n+1]) x) := by
    refine Set.mem_sInter.mpr ?_
    rintro s ⟨hs, hxs⟩
    exact Set.mem_sInter.mp hy (((shiftZ t 1)^[n+1]) ⁻¹' s)
      ⟨(MeasurableSpace.measurableSet_comap).mpr ⟨s, hs, rfl⟩, hxs⟩
  obtain ⟨i, hi⟩ : ∃ i : Fin Q.n, (shiftZ t 1)^[n+1] x ∈ Q.parts i := by
    have hcover : (shiftZ t 1)^[n+1] x ∈ ⋃ i, Q.parts i := by rw [Q.cover]; exact trivial
    exact Set.mem_iUnion.mp hcover
  refine ⟨i, hi, ?_⟩
  have hsub : atomGen (partSigma Q) ((shiftZ t 1)^[n+1] x) ⊆ Q.parts i := fun w hw =>
    Set.mem_sInter.mp hw (Q.parts i)
      ⟨MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self i), hi⟩
  exact hsub hy2

/-! ## 4. Auxiliary topological fact -/

theorem mem_interior_of_mem_of_notMem_frontier {α : Type*} [TopologicalSpace α] {s : Set α} {x : α}
    (hx : x ∈ s) (h : x ∉ frontier s) : x ∈ interior s := by
  by_contra hc
  have hc' : x ∈ closure sᶜ := by
    by_contra h2
    exact hc (by rw [interior_eq_compl_closure_compl]; exact h2)
  have : x ∈ frontier s := by
    rw [frontier_eq_closure_inter_closure]
    exact ⟨subset_closure hx, hc'⟩
  exact h this

theorem cbox_subset_V {θ Δ : ℝ} (h : θ < Δ) : cbox θ ⊆ V Δ := fun g hg i j => lt_of_le_of_lt (hg i j) h


/-- Any set in the σ-algebra generated by sets of measure `0` or `1` has measure `0` or `1`. -/
theorem trivial_of_generateFrom {X : Type} [mX : MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] {S : Set (Set X)}
    (hS : ∀ s ∈ S, MeasurableSet s ∧ (μ s = 0 ∨ μ s = 1)) :
    ∀ A : Set X, MeasurableSet[MeasurableSpace.generateFrom S] A → μ A = 0 ∨ μ A = 1 := by
  let mtriv : MeasurableSpace X :=
    { MeasurableSet' := fun A => MeasurableSet A ∧ (μ A = 0 ∨ μ A = 1)
      measurableSet_empty := ⟨MeasurableSet.empty, Or.inl measure_empty⟩
      measurableSet_compl := by
        rintro A ⟨hA, h | h⟩
        · refine ⟨hA.compl, Or.inr ?_⟩
          rw [measure_compl hA (by rw [h]; exact ENNReal.zero_ne_top), h, measure_univ,
            tsub_zero]
        · refine ⟨hA.compl, Or.inl ?_⟩
          rw [measure_compl hA (by rw [h]; exact ENNReal.one_ne_top), h, measure_univ, tsub_self]
      measurableSet_iUnion := by
        intro f hf
        by_cases hex : ∃ n, μ (f n) = 1
        · obtain ⟨n, hn⟩ := hex
          refine ⟨MeasurableSet.iUnion fun m => (hf m).1, Or.inr (le_antisymm ?_ ?_)⟩
          · exact Work.EKLComp.Core.prob_measure_le_one μ _
          · calc (1 : ℝ≥0∞) = μ (f n) := hn.symm
              _ ≤ μ (⋃ m, f m) := measure_mono (Set.subset_iUnion f n)
        · push Not at hex
          refine ⟨MeasurableSet.iUnion fun m => (hf m).1, Or.inl ?_⟩
          exact measure_iUnion_null fun m => by
            rcases (hf m).2 with h | h
            · exact h
            · exact absurd h (hex m) }
  have hle : MeasurableSpace.generateFrom S ≤ mtriv := by
    refine MeasurableSpace.generateFrom_le ?_
    intro s hs
    exact hS s hs
  intro A hA
  exact (hle A hA).2



end vanish

open vanish
/-! ## 5. The vanishing lemma -/

theorem hcond_orbit_eq_zero_hK (t : Fin 3 → ℝ) (ht : ∃ i j : Fin 3, t i ≠ t j)
    {K : Set X3} (hK : IsCompact K)
    (hfwd : ∀ x ∈ K, shiftZ t 1 x ∈ K) (hbwd : ∀ x ∈ K, shiftZ t (-1) x ∈ K)
    {ν : Measure X3} [IsProbabilityMeasure ν]
    (hmp : MeasurePreserving (shiftZ t 1) ν ν) (hKν : ν K = 1)
    {P : FinPart X3} {δ r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1/2)
    (hinj : ∀ x ∈ K, ∀ g h : SL3, g ∈ V r → h ∈ V r → g • x = h • x → g = h)
    (hδr : δ ≤ r) (hδexp : δ ≤ r * Real.exp (-(tsum t)) / 2) (hδ0 : 0 < δ)
    (hsmall : AtomSmall K δ P) (Q : FinPart X3) (hQ : ∀ i, ν (frontier (Q.parts i)) = 0) :
    Hcond ν Q (orbitSigma t P ⊔ pastSig t Q) = 0 := by
  classical
  -- bridge to `aDiag t •`
  have hdiag : (fun x : X3 => aDiag t • x) = shiftZ t 1 := by
    funext x; simp [shiftZ, aZ_one]
  have hfwd' : ∀ x ∈ K, aDiag t • x ∈ K := fun x hx => by
    have h : shiftZ t 1 x = aDiag t • x := by
      show aZ t 1 • x = aDiag t • x
      rw [aZ_one]
    rw [← h]; exact hfwd x hx
  have hbwd' : ∀ x ∈ K, aDiag (-t) • x ∈ K := fun x hx => by
    have h : aDiag (-t) • x = shiftZ t (-1) x := congrFun (aDiag_neg_eq_shiftZ t) x
    rw [h]; exact hbwd x hx
  -- the exceptional null sets
  set N₀ : Set X3 := ⋃ i : Fin Q.n, frontier (Q.parts i) with hN₀def
  have hN₀null : ν N₀ = 0 := by
    rw [hN₀def]
    exact measure_iUnion_null fun i => hQ i
  -- measurability facts (computed before the local σ-algebra comes into scope)
  have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
  have hfrmeas : ∀ i : Fin Q.n, MeasurableSet (frontier (Q.parts i)) :=
    fun i => isClosed_frontier.measurableSet
  -- the atom σ-algebra
  set 𝔐 : MeasurableSpace X3 := orbitSigma t P ⊔ pastSig t Q ⊔
    MeasurableSpace.generateFrom ({K} ∪ Set.range (fun i : Fin Q.n => frontier (Q.parts i)))
    with h𝔐def
  letI : MeasurableSpace X3 := instMeasurableSpaceX3
  have hgenle : MeasurableSpace.generateFrom
      ({K} ∪ Set.range (fun i : Fin Q.n => frontier (Q.parts i))) ≤ 𝔐 := by
    rw [h𝔐def]; exact le_sup_right
  have hK𝔐 : MeasurableSet[𝔐] K :=
    hgenle K (MeasurableSpace.measurableSet_generateFrom (Or.inl rfl))
  have hfr𝔐 : ∀ i : Fin Q.n, MeasurableSet[𝔐] (frontier (Q.parts i)) := fun i =>
    hgenle _ (MeasurableSpace.measurableSet_generateFrom (Or.inr ⟨i, rfl⟩))
  have hN₀𝔐 : MeasurableSet[𝔐] N₀ := by
    rw [hN₀def]; exact MeasurableSet.iUnion hfr𝔐
  -- countable generation and measurability of 𝔐
  have h𝔐gen : ∃ b : Set (Set X3), b.Countable ∧ 𝔐 = MeasurableSpace.generateFrom b := by
    obtain ⟨b, hbcnt, hbgen⟩ := orbitSigma_countable t P Q K
    refine ⟨b, hbcnt, ?_⟩
    have hps : pastSig t Q = negOrbitSigma t Q := pastSig_eq_negOrbitSigma t Q
    rw [h𝔐def, hps, ← hbgen]
    ac_rfl
  have h𝔐le : 𝔐 ≤ instMeasurableSpaceX3 := by
    rw [h𝔐def]
    refine sup_le (sup_le (orbitSigma_le_ambient t P) (pastSig_le_ambient t Q)) ?_
    refine MeasurableSpace.generateFrom_le ?_
    rintro s (hs | ⟨i, rfl⟩)
    · rw [Set.mem_singleton_iff] at hs
      subst hs
      exact hKmeas
    · exact hfrmeas i
  -- the recurrence family
  obtain ⟨grat, hgratC, hgratdense⟩ := dense_Csub_seq t
  set Bfam : (Fin Q.n × Fin Q.n) × (ℕ × ℕ) → Set X3 :=
    fun p => Bset Q p.1.1 p.1.2 (grat p.2.1) (1 / ((p.2.2 : ℝ) + 1)) with hBfamdef
  have hBfammeas : ∀ p, MeasurableSet (Bfam p) := fun p => measurableSet_Bset ..
  obtain ⟨N₁, hN₁null, hN₁rec⟩ := recurrence_family hmp Bfam hBfammeas
  -- the bad set
  set Bad : Set X3 := N₀ ∪ N₁ ∪ Kᶜ with hBaddef
  have hBadnull : ν Bad = 0 := by
    rw [hBaddef]
    refine measure_union_null (measure_union_null hN₀null hN₁null) ?_
    rw [measure_compl hKmeas (measure_ne_top ν _), hKν, measure_univ, tsub_self]
  -- the pointwise atom criterion
  have hcrit' : ∀ x ∉ Bad, ∀ i, x ∈ Q.parts i → ∀ y, y ∈ atomGen 𝔐 x → y ∈ Q.parts i := by
    intro x hxBad i hxi y hy
    have hxK : x ∈ K := by
      by_contra h
      exact hxBad (Or.inr (by simpa using h))
    have hxN₀ : x ∉ N₀ := fun h => hxBad (Or.inl (Or.inl h))
    have hxN₁ : x ∉ N₁ := fun h => hxBad (Or.inl (Or.inr h))
    have hyK : y ∈ K := Set.mem_sInter.mp hy K ⟨hK𝔐, hxK⟩
    have hyN₀ : y ∉ N₀ := by
      have hcompl : MeasurableSet[𝔐] N₀ᶜ := hN₀𝔐.compl
      exact Set.mem_sInter.mp hy N₀ᶜ ⟨hcompl, hxN₀⟩
    have hxint : x ∈ interior (Q.parts i) :=
      mem_interior_of_mem_of_notMem_frontier hxi (fun h => hxN₀ (Set.mem_iUnion.mpr ⟨i, h⟩))
    obtain ⟨j, hyj⟩ : ∃ j : Fin Q.n, y ∈ Q.parts j := by
      have hcover : y ∈ ⋃ j, Q.parts j := by rw [Q.cover]; exact trivial
      exact Set.mem_iUnion.mp hcover
    have hyint : y ∈ interior (Q.parts j) :=
      mem_interior_of_mem_of_notMem_frontier hyj (fun h => hyN₀ (Set.mem_iUnion.mpr ⟨j, h⟩))
    -- the core claim: y = c x with c in the centraliser
    have hyorbit : y ∈ Work.EKLContract.atom (orbitSigma t P) x :=
      atomGen_anti (by rw [h𝔐def]; exact le_sup_left.trans le_sup_left) x hy
    obtain ⟨c, hcC, hcxy⟩ :=
      sameItin_central_gen hfwd' hbwd' hinj hr0 hr1 hδr hδexp hsmall hxK hyK hyorbit
    -- the neighbourhood estimates
    obtain ⟨ε₁, hε₁, δ₁, hδ₁, hball₁⟩ :=
      ball_nhds (hU := isOpen_interior) x c (by rw [← hcxy]; exact hyint)
    obtain ⟨ε₂, hε₂, δ₂, hδ₂, hball₂⟩ :=
      ball_nhds (hU := isOpen_interior) x 1 (by simpa using hxint)
    obtain ⟨ε₃, hε₃, hconj⟩ := Work.EKLComp.exists_V_conj (c := c) hε₁
    -- the radius θ = 1/(ℓ+1)
    obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℕ, 1 / ((ℓ : ℝ) + 1) ≤ min δ₁ δ₂ / 2 := by
      have hpos : 0 < min δ₁ δ₂ / 2 := by positivity
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / (min δ₁ δ₂ / 2))
      rw [div_lt_iff₀ hpos] at hN
      refine ⟨N, ?_⟩
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) + 1)]
      nlinarith [hN, hpos]
    set θ : ℝ := 1 / ((ℓ : ℝ) + 1) with hθdef
    have hθ0 : 0 < θ := by rw [hθdef]; positivity
    have hθ₀ : θ * 2 ≤ min δ₁ δ₂ := by
      rw [hθdef]
      linarith [hℓ]
    have hθ1 : θ < δ₁ := by linarith [hθ₀, min_le_left δ₁ δ₂, hθ0]
    have hθ2 : θ < δ₂ := by linarith [hθ₀, min_le_right δ₁ δ₂, hθ0]
    have hcbox₁ : cbox θ ⊆ V δ₁ := cbox_subset_V hθ1
    have hcbox₂ : cbox θ ⊆ V δ₂ := cbox_subset_V hθ2
    -- the rational approximation
    set ε : ℝ := min θ ε₃ / 10 with hεdef
    have hε0 : 0 < ε := by rw [hεdef]; positivity
    have hεθ : ε ≤ θ := by
      rw [hεdef]
      have := min_le_left θ ε₃
      linarith
    have h10εθ : 10 * ε ≤ θ := by
      rw [hεdef]
      have := min_le_left θ ε₃
      linarith
    have h10εε₃ : 10 * ε ≤ ε₃ := by
      rw [hεdef]
      have := min_le_right θ ε₃
      linarith
    have hε1 : ε ≤ 1 := le_trans hεθ (by rw [hθdef]; rw [one_div]; exact inv_le_one_of_one_le₀ (by linarith))
    obtain ⟨m, hm⟩ := hgratdense c hcC ε hε0
    set g : SL3 := grat m with hgdef
    set k : SL3 := g⁻¹ * c with hkdef
    have hkV : k ∈ V ε := by simpa [hgdef] using hm
    have hkmem : k⁻¹ ∈ V (10 * ε) := inv_mem_V hε0 hε1 hkV
    have hkθ : k ∈ V θ := V_mono hεθ hkV
    have hkε₃ : k⁻¹ ∈ V ε₃ := V_mono h10εε₃ hkmem
    have hgc : g * c⁻¹ ∈ V ε₁ := by
      have hge : g = c * k⁻¹ := by rw [hkdef, hgdef]; group
      rw [hge]
      simpa only [mul_assoc] using hconj k⁻¹ hkε₃
    -- membership of x in the recurrence set
    have hxB : x ∈ Bset Q i j g θ := by
      constructor
      · intro h hh
        simpa using hball₂ 1 h (by simpa using one_mem_V hε₂) (hcbox₂ hh)
      · intro h hh
        exact hball₁ g h hgc (hcbox₁ hh)
    -- the recurrence
    have hmemBfam : x ∈ Bfam ((i, j), (m, ℓ)) := by
      show x ∈ Bset Q i j (grat m) (1 / ((ℓ : ℝ) + 1))
      rw [← hgdef, ← hθdef]
      exact hxB
    obtain ⟨n, hn1, hnB⟩ := hN₁rec x hxN₁ ((i, j), (m, ℓ)) hmemBfam
    -- the two membership conclusions
    have hTnx : (shiftZ t 1)^[n] x ∈ Q.parts i :=
      interior_subset (by simpa using hnB.1 1 (one_mem_cbox hθ0.le))
    have hTny : (shiftZ t 1)^[n] y ∈ Q.parts j := by
      have hcomm : c • ((shiftZ t 1)^[n] x) = (shiftZ t 1)^[n] (c • x) :=
        Csub_smul_shiftZ_iterate t hcC n x
      have h2 : (shiftZ t 1)^[n] y = c • ((shiftZ t 1)^[n] x) := by
        rw [hcxy, hcomm]
      rw [h2]
      have h3 : c = g * k := by rw [hkdef, hgdef]; group
      rw [h3]
      exact interior_subset (hnB.2 k (V_subset_cbox θ hkθ))
    -- the atom relation at time n
    have hynAtom : y ∈ atomGen (pastSig t Q) x :=
      atomGen_anti (by rw [h𝔐def]; exact le_sup_right.trans le_sup_left) x hy
    obtain ⟨i', hi'x, hi'y⟩ := mem_same_part_of_mem_pastSig_atomG t Q hynAtom (n - 1)
    rw [Nat.sub_add_cancel hn1] at hi'x hi'y
    have hii' : i = i' := by
      by_contra hne
      exact Set.disjoint_left.mp (Q.disjoint hne) hTnx hi'x
    have hi'Q : (shiftZ t 1)^[n] y ∈ Q.parts i := by rw [hii']; exact hi'y
    have hij : i = j := by
      by_contra hne
      exact Set.disjoint_left.mp (Q.disjoint hne) hi'Q hTny
    rw [hij]
    exact hyj
  -- assemble
  have hcrit : ∀ᵐ x ∂ν, ∀ i, x ∈ Q.parts i → ∀ y, y ∈ atomGen 𝔐 x → y ∈ Q.parts i := by
    rw [MeasureTheory.ae_iff]
    refine measure_mono_null (fun x hx => ?_) hBadnull
    by_contra hxBad
    exact hx (hcrit' x hxBad)
  have h1 : @Hcond X3 instMeasurableSpaceX3 ν Q 𝔐 = 0 :=
    Hcond_eq_zero_of_atom_subset ν Q 𝔐 h𝔐le h𝔐gen hcrit
  -- `𝔐` is `σ ⊔ generateFrom S` where every `S`-set is `ν`-null or `ν`-conull
  have htriv : ∀ s ∈ ({K} ∪ Set.range (fun i : Fin Q.n => frontier (Q.parts i)) : Set (Set X3)),
      @MeasurableSet X3 instMeasurableSpaceX3 s ∧ (ν s = 0 ∨ ν s = 1) := by
    rintro s (hs | ⟨i, rfl⟩)
    · rw [Set.mem_singleton_iff] at hs
      subst hs
      exact ⟨hKmeas, Or.inr hKν⟩
    · exact ⟨hfrmeas i, Or.inl (hQ i)⟩
  have h2 : @Hcond X3 instMeasurableSpaceX3 ν Q 𝔐 =
      @Hcond X3 instMeasurableSpaceX3 ν Q (orbitSigma t P ⊔ pastSig t Q) := by
    have h := Hcond_sup_trivial_gens_X3 t P Q ν htriv
    rw [h𝔐def]
    exact h
  rw [← h2]
  exact h1

end Work.EKLComp

end
