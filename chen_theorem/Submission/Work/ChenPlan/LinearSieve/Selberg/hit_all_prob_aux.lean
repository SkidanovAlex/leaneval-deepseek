import Mathlib
import Submission.Work.ChenPlan.LinearSieve.Selberg.Alt.PiSplit

/-!
# The splitting (strong Markov) computation for the exponential product measure

We work on `ℝ^ℕ` with the product measure `PiN μ` of the standard exponential law.  The main
results are

* `lintegral_mkSeq`, `lintegral_splitSeq` : change-of-variables along the two splittings;
* `HasExpLaw.lintegral_shift` : the memorylessness identity in integral form;
* `core` : the fundamental `Σ_k`-decomposition of the first-hit interval;
* `splitting` : the event that an interval `(a,t]` is hit is independent of the post-`t` future;
* `hit_single` : `ν (Hit a b) = 1 - exp (-(b - a))`.
-/

open MeasureTheory
open scoped ENNReal

open Work.ChenPlan.LinearSieve.Selberg.Alt

namespace Work.ChenPlan.LinearSieve.Selberg.HitAux

noncomputable abbrev PiN (μ : Measure ℝ) : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => μ)

noncomputable abbrev PiFin (μ : Measure ℝ) (k : ℕ) : Measure (Fin k → ℝ) :=
  Measure.pi (fun _ : Fin k => μ)

/-- `Pk k y = y 0 + y 1 + ... + y (k-1)` for `y : Fin k → ℝ`. -/
def Pk (k : ℕ) (y : Fin k → ℝ) : ℝ := ∑ i : Fin k, y i

lemma Tf_eq_Pk (k : ℕ) (x : ℕ → ℝ) : Tf k x = Pk k (fun i : Fin k => x i) := by
  rw [Tf, Pk, Finset.sum_range]

lemma Pk_splitSeq (k : ℕ) (p : (Fin k → ℝ) × (ℕ → ℝ)) : Pk k p.1 = Tf k (splitSeq k p) :=
  (Tf_splitSeq k p).symm

lemma measurable_Pk (k : ℕ) : Measurable (Pk k) := by
  show Measurable fun y : Fin k → ℝ => ∑ i : Fin k, y i
  fun_prop

/-- The event that the `k`-th gap crosses `t`. -/
def Ev (t : ℝ) (k : ℕ) : Set (ℕ → ℝ) := {x | Tf k x ≤ t ∧ t < Tf (k+1) x}

/-- The event that some partial sum lies in `(a,b]`. -/
def Hit (a b : ℝ) : Set (ℕ → ℝ) := {x | ∃ k, Tf k x ∈ Set.Ioc a b}

/-- The event that every interval of a family is hit. -/
def AllHit {ι : Type*} (a b : ι → ℝ) : Set (ℕ → ℝ) := {x | ∀ i, Hit (a i) (b i) x}

lemma measurable_Tf (k : ℕ) : Measurable (Tf k : (ℕ → ℝ) → ℝ) := by
  show Measurable fun x : ℕ → ℝ => ∑ i ∈ Finset.range k, x i
  fun_prop

lemma measurable_Ev (t : ℝ) (k : ℕ) : MeasurableSet (Ev t k) :=
  (measurableSet_le (measurable_Tf k) measurable_const).inter
    (measurableSet_lt measurable_const (measurable_Tf (k+1)))

lemma measurableSet_Hit {a b : ℝ} : MeasurableSet (Hit a b) := by
  have h : Hit a b = ⋃ k : ℕ, (fun x : ℕ → ℝ => Tf k x) ⁻¹' Set.Ioc a b := by
    ext x; simp [Hit]
  rw [h]
  exact MeasurableSet.iUnion fun k => measurableSet_Ioc.preimage (measurable_Tf k)

lemma measurableSet_AllHit {ι : Type*} [Countable ι] {a b : ι → ℝ} :
    MeasurableSet (AllHit a b) := by
  have h : AllHit a b = ⋂ i : ι, Hit (a i) (b i) := by
    ext x
    simp only [AllHit, Set.mem_setOf_eq, Set.mem_iInter]
    exact ⟨fun h i => h i, fun h i => h i⟩
  rw [h]
  exact MeasurableSet.iInter fun i => measurableSet_Hit


lemma lintegral_mkSeq {μ : Measure ℝ} [IsProbabilityMeasure μ] (f : (ℕ → ℝ) → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ x, f x ∂(PiN μ) = ∫⁻ p : ℝ × (ℕ → ℝ), f (mkSeq p) ∂(μ.prod (PiN μ)) := by
  have hmap : PiN μ = (μ.prod (PiN μ)).map mkSeq := (mkSeq_map (μ := μ)).symm
  conv_lhs => rw [hmap]
  rw [lintegral_map hf measurable_mkSeq]

lemma lintegral_splitSeq {μ : Measure ℝ} [IsProbabilityMeasure μ] (k : ℕ)
    (f : (ℕ → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f x ∂(PiN μ) = ∫⁻ p : (Fin k → ℝ) × (ℕ → ℝ), f (splitSeq k p) ∂
      (PiFin μ k).prod (PiN μ) := by
  have hmap : PiN μ = ((PiFin μ k).prod (PiN μ)).map (splitSeq k) :=
    (splitSeq_map (μ := μ) k).symm
  conv_lhs => rw [hmap]
  rw [lintegral_map hf (measurable_splitSeq k)]

/-- Memorylessness in integral form. -/
lemma HasExpLaw.lintegral_shift {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : HasExpLaw μ)
    {c : ℝ} (hc : 0 ≤ c) (Ψ : ℝ → ℝ≥0∞) (hΨ : Measurable Ψ) :
    ∫⁻ u, Set.indicator (Set.Ioi c) (fun u => Ψ (u - c)) u ∂μ
      = ENNReal.ofReal (Real.exp (-c)) * ∫⁻ r, Ψ r ∂μ := by
  rw [lintegral_indicator measurableSet_Ioi]
  rw [← lintegral_map hΨ (by fun_prop : Measurable fun u : ℝ => u - c)]
  rw [HasExpLaw.shift hμ hc, lintegral_smul_measure, smul_eq_mul]


/-- The inner computation: integrating over the tail `z` after the first coordinate has been
`cons`-ed off. -/
lemma inner_computation {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : HasExpLaw μ)
    {t : ℝ} (k : ℕ) (Φ : (Fin k → ℝ) → ℝ → (ℕ → ℝ) → ℝ≥0∞)
    (hΦ : Measurable fun q : ((Fin k → ℝ) × ℝ) × (ℕ → ℝ) => Φ q.1.1 q.1.2 q.2)
    (y : Fin k → ℝ) :
    ∫⁻ z, Set.indicator {z : ℕ → ℝ | Pk k y ≤ t ∧ t < Pk k y + z 0}
        (fun z => Φ y (Pk k y + z 0 - t) (fun j : ℕ => z (j+1))) z ∂(PiN μ)
      = if Pk k y ≤ t then ENNReal.ofReal (Real.exp (-(t - Pk k y))) *
          (∫⁻ q : ℝ × (ℕ → ℝ), Φ y q.1 q.2 ∂(μ.prod (PiN μ))) else 0 := by
  have hΦy : Measurable fun q : ℝ × (ℕ → ℝ) => Φ y q.1 q.2 := by
    have h1 : Measurable fun q : ℝ × (ℕ → ℝ) => (y, q.1) := by fun_prop
    exact hΦ.comp (h1.prodMk measurable_snd)
  set S1 : Set (ℕ → ℝ) := {z : ℕ → ℝ | Pk k y ≤ t ∧ t < Pk k y + z 0} with hS1
  set H1 : (ℕ → ℝ) → ℝ≥0∞ := fun z => Φ y (Pk k y + z 0 - t) (fun j : ℕ => z (j+1))
    with hH1
  set S2 : Set (ℝ × (ℕ → ℝ)) := {q : ℝ × (ℕ → ℝ) | Pk k y ≤ t ∧ t < Pk k y + q.1} with hS2
  set H2 : (ℝ × (ℕ → ℝ)) → ℝ≥0∞ := fun q => Φ y (Pk k y + q.1 - t) q.2 with hH2
  set T : Set ℝ := {u : ℝ | Pk k y ≤ t ∧ t < Pk k y + u} with hT
  set Θ : ℝ → ℝ≥0∞ := fun r => ∫⁻ ζ, Φ y r ζ ∂(PiN μ) with hΘ
  have hΘmeas : Measurable Θ := hΦy.lintegral_prod_right'
  have hΘeq : ∫⁻ r, Θ r ∂μ = ∫⁻ q : ℝ × (ℕ → ℝ), Φ y q.1 q.2 ∂(μ.prod (PiN μ)) :=
    (lintegral_prod _ hΦy.aemeasurable).symm
  have hS1meas : MeasurableSet S1 := by
    rw [hS1]
    exact MeasurableSet.inter
      (measurableSet_le (measurable_const : Measurable fun _ : ℕ → ℝ => Pk k y)
        (measurable_const : Measurable fun _ : ℕ → ℝ => t))
      (measurableSet_lt (measurable_const : Measurable fun _ : ℕ → ℝ => t)
        ((measurable_pi_apply (0:ℕ)).const_add _))
  have hH1meas : Measurable H1 := by
    rw [hH1]
    have hg : Measurable fun z : ℕ → ℝ => (Pk k y + z 0 - t, (fun j : ℕ => z (j + 1))) := by
      refine Measurable.prodMk ?_ ?_
      · exact ((measurable_pi_apply (0:ℕ)).const_add _).sub measurable_const
      · exact Measurable.of_eval fun j => measurable_pi_apply (j+1)
    exact hΦy.comp hg
  have hS2meas : MeasurableSet S2 := by
    rw [hS2]
    exact MeasurableSet.inter
      (measurableSet_le (measurable_const : Measurable fun _ : ℝ × (ℕ → ℝ) => Pk k y)
        (measurable_const : Measurable fun _ : ℝ × (ℕ → ℝ) => t))
      (measurableSet_lt (measurable_const : Measurable fun _ : ℝ × (ℕ → ℝ) => t)
        (measurable_fst.const_add _))
  have hH2meas : Measurable H2 := by
    rw [hH2]
    have hg : Measurable fun q : ℝ × (ℕ → ℝ) => (Pk k y + q.1 - t, q.2) := by
      exact (measurable_fst.const_add _).sub measurable_const |>.prodMk measurable_snd
    exact hΦy.comp hg
  -- Step A: change of variables `z = mkSeq q`.
  rw [lintegral_mkSeq _ (hH1meas.indicator hS1meas)]
  have hcongr2 : ∀ q : ℝ × (ℕ → ℝ), Set.indicator S1 H1 (mkSeq q) = Set.indicator S2 H2 q := by
    intro q
    have hmem : mkSeq q ∈ S1 ↔ q ∈ S2 := by
      rw [hS1, hS2]; simp only [Set.mem_setOf_eq, mkSeq_zero]
    have hval : H1 (mkSeq q) = H2 q := by
      rw [hH1, hH2]; simp only [mkSeq_zero, mkSeq_succ]
    by_cases hq : q ∈ S2
    · rw [Set.indicator_of_mem (s := S1) (a := mkSeq q) (hmem.mpr hq),
        Set.indicator_of_mem (s := S2) (a := q) hq, hval]
    · rw [Set.indicator_of_notMem (s := S1) (a := mkSeq q) (fun h => hq (hmem.mp h)),
        Set.indicator_of_notMem (s := S2) (a := q) hq]
  rw [lintegral_congr hcongr2]
  -- Step B: Tonelli.
  rw [lintegral_prod _ (hH2meas.indicator hS2meas).aemeasurable]
  -- Step C: the inner integral over `ζ`.
  have hpt : ∀ u : ℝ, ∫⁻ ζ, Set.indicator S2 H2 (u, ζ) ∂(PiN μ)
      = Set.indicator T (fun u => Θ (Pk k y + u - t)) u := by
    intro u
    have hinner : ∀ ζ : ℕ → ℝ, Set.indicator S2 H2 (u, ζ)
        = Set.indicator T (fun _ : ℝ => (1:ℝ≥0∞)) u * Φ y (Pk k y + u - t) ζ := by
      intro ζ
      have hmem : (u, ζ) ∈ S2 ↔ u ∈ T := by
        rw [hS2, hT]; simp only [Set.mem_setOf_eq]
      by_cases hu : (u, ζ) ∈ S2
      · rw [Set.indicator_of_mem (s := S2) (a := (u,ζ)) hu,
          Set.indicator_of_mem (s := T) (a := u) (hmem.mp hu), hH2, one_mul]
      · rw [Set.indicator_of_notMem (s := S2) (a := (u,ζ)) hu,
          Set.indicator_of_notMem (s := T) (a := u) (fun h => hu (hmem.mpr h)), zero_mul]
    rw [lintegral_congr hinner,
      lintegral_const_mul (Set.indicator T (fun _ : ℝ => (1:ℝ≥0∞)) u) ?_]
    · by_cases hu : u ∈ T
      · rw [Set.indicator_of_mem (s := T) (a := u) hu, Set.indicator_of_mem (s := T) (a := u) hu,
          one_mul]
      · rw [Set.indicator_of_notMem (s := T) (a := u) hu,
          Set.indicator_of_notMem (s := T) (a := u) hu, zero_mul]
    · exact hΦy.comp (Measurable.prodMk measurable_const measurable_id)
  rw [lintegral_congr hpt]
  -- Step D: evaluate.
  by_cases hyt : Pk k y ≤ t
  · rw [if_pos hyt]
    have hT' : T = Set.Ioi (t - Pk k y) := by
      rw [hT]
      ext u; simp only [Set.mem_setOf_eq, Set.mem_Ioi]
      exact ⟨fun hh => by linarith, fun hh => ⟨hyt, by linarith⟩⟩
    rw [hT']
    have hfun : (fun u : ℝ => Θ (Pk k y + u - t)) = fun u => Θ (u - (t - Pk k y)) := by
      funext u; congr 1; ring
    rw [hfun, HasExpLaw.lintegral_shift hμ (by linarith) Θ hΘmeas, hΘeq]
  · rw [if_neg hyt]
    have hT' : T = ∅ := by
      rw [hT]
      ext u; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro h1; exact absurd h1 hyt
    rw [hT']; simp


/-- The fundamental decomposition: the event that the `k`-th gap crosses `t` is integrated by
splitting off the first `k` coordinates and then the `k`-th coordinate. -/
theorem core {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : HasExpLaw μ)
    {t : ℝ} (ht : 0 ≤ t) (k : ℕ)
    (Φ : (Fin k → ℝ) → ℝ → (ℕ → ℝ) → ℝ≥0∞)
    (hΦ : Measurable fun q : ((Fin k → ℝ) × ℝ) × (ℕ → ℝ) => Φ q.1.1 q.1.2 q.2) :
    ∫⁻ x, Set.indicator (Ev t k)
        (fun x : ℕ → ℝ => Φ (fun i : Fin k => x i) (Tf (k+1) x - t)
          (fun j : ℕ => x (k+1+j))) x ∂(PiN μ)
      = ∫⁻ y : Fin k → ℝ, Set.indicator {y : Fin k → ℝ | Pk k y ≤ t}
          (fun y => ENNReal.ofReal (Real.exp (-(t - Pk k y))) *
            (∫⁻ q : ℝ × (ℕ → ℝ), Φ y q.1 q.2 ∂(μ.prod (PiN μ)))) y ∂(PiFin μ k) := by
  have hPk1 : Measurable fun p : (Fin k → ℝ) × (ℕ → ℝ) => Pk k p.1 :=
    (measurable_Pk k).comp measurable_fst
  have hx0 : Measurable fun p : (Fin k → ℝ) × (ℕ → ℝ) => p.2 0 :=
    (measurable_pi_apply (0:ℕ)).comp measurable_snd
  set E : Set ((Fin k → ℝ) × (ℕ → ℝ)) := {p | Pk k p.1 ≤ t ∧ t < Pk k p.1 + p.2 0} with hE
  set G : ((Fin k → ℝ) × (ℕ → ℝ)) → ℝ≥0∞ :=
    fun p => Φ p.1 (Pk k p.1 + p.2 0 - t) (fun j => p.2 (j+1)) with hG
  have hmeasL : Measurable fun x : ℕ → ℝ =>
      Φ (fun i : Fin k => x i) (Tf (k+1) x - t) (fun j : ℕ => x (k+1+j)) := by
    have hg : Measurable fun x : ℕ → ℝ =>
        (((fun i : Fin k => x i), Tf (k+1) x - t), (fun j : ℕ => x (k+1+j))) := by
      refine Measurable.prodMk ?_ ?_
      · exact Measurable.prodMk
          (Measurable.of_eval fun i : Fin k => measurable_pi_apply (i : ℕ))
          ((measurable_Tf (k+1)).sub measurable_const)
      · exact Measurable.of_eval fun j => measurable_pi_apply (k+1+j)
    exact hΦ.comp hg
  have hG_eq : ∀ p : (Fin k → ℝ) × (ℕ → ℝ),
      G p = Φ p.1 (Pk k p.1 + p.2 0 - t) (fun j => p.2 (j+1)) := fun p => rfl
  have hEmeas : MeasurableSet E := by
    rw [hE]
    exact MeasurableSet.inter
      (measurableSet_le hPk1 measurable_const)
      (measurableSet_lt measurable_const (hPk1.add hx0))
  have hGmeas : Measurable G := by
    rw [hG]
    have hg : Measurable fun p : (Fin k → ℝ) × (ℕ → ℝ) =>
        ((p.1, Pk k p.1 + p.2 0 - t), (fun j : ℕ => p.2 (j+1))) := by
      refine Measurable.prodMk ?_ ?_
      · exact Measurable.prodMk measurable_fst ((hPk1.add hx0).sub measurable_const)
      · exact Measurable.of_eval fun j => (measurable_pi_apply (j+1)).comp measurable_snd
    exact hΦ.comp hg
  -- Step 1: split off the first `k` coordinates.
  rw [lintegral_splitSeq k _ (hmeasL.indicator (measurable_Ev t k))]
  have hstep2 : ∀ p : (Fin k → ℝ) × (ℕ → ℝ),
      Set.indicator (Ev t k)
        (fun x : ℕ → ℝ => Φ (fun i : Fin k => x i) (Tf (k+1) x - t)
          (fun j : ℕ => x (k+1+j))) (splitSeq k p) = Set.indicator E G p := by
    intro p
    have hT1 : Tf (k+1) (splitSeq k p) = Pk k p.1 + p.2 0 := by
      rw [Tf_succ, Tf_splitSeq, Pk, splitSeq_apply_ge (lt_irrefl k), Nat.sub_self]
    have hEv : splitSeq k p ∈ Ev t k ↔ p ∈ E := by
      rw [Ev, hE]
      simp only [Set.mem_setOf_eq, Tf_splitSeq, Pk, hT1]
    have hval : Φ (fun i : Fin k => splitSeq k p i) (Tf (k+1) (splitSeq k p) - t)
        (fun j : ℕ => splitSeq k p (k+1+j)) = G p := by
      change Φ (fun i : Fin k => splitSeq k p i) (Tf (k+1) (splitSeq k p) - t)
        (fun j : ℕ => splitSeq k p (k+1+j)) = Φ p.1 (Pk k p.1 + p.2 0 - t) fun j => p.2 (j+1)
      have h1 : (fun i : Fin k => splitSeq k p i) = p.1 := by
        funext i; rw [splitSeq_apply_lt i.isLt]
      have h3 : (fun j : ℕ => splitSeq k p (k+1+j)) = fun j : ℕ => p.2 (j+1) := by
        funext j
        rw [splitSeq_apply_ge (by omega), show k + 1 + j - k = j + 1 by omega]
      rw [h1, hT1, h3]
    by_cases hp : p ∈ E
    · rw [Set.indicator_of_mem (s := Ev t k) (a := splitSeq k p) (hEv.mpr hp),
        Set.indicator_of_mem (s := E) (a := p) hp, hval]
    · rw [Set.indicator_of_notMem (s := Ev t k) (a := splitSeq k p) (fun h => hp (hEv.mp h)),
        Set.indicator_of_notMem (s := E) (a := p) hp]
  rw [lintegral_congr hstep2]
  -- Step 3: Tonelli.
  rw [lintegral_prod _ (hGmeas.indicator hEmeas).aemeasurable]
  -- Step 4: the inner integral, pointwise in `y`.
  refine lintegral_congr fun y => ?_
  have hmem : ∀ z : ℕ → ℝ, (y, z) ∈ E ↔ Pk k y ≤ t ∧ t < Pk k y + z 0 := by
    intro z
    rw [hE]; simp only [Set.mem_setOf_eq]
  have hpt : ∀ z : ℕ → ℝ, Set.indicator E G (y, z)
      = Set.indicator {z : ℕ → ℝ | Pk k y ≤ t ∧ t < Pk k y + z 0}
          (fun z => Φ y (Pk k y + z 0 - t) (fun j : ℕ => z (j+1))) z := by
    intro z
    by_cases hz : (y, z) ∈ E
    · rw [Set.indicator_of_mem (s := E) (a := (y,z)) hz,
        Set.indicator_of_mem (s := {z : ℕ → ℝ | Pk k y ≤ t ∧ t < Pk k y + z 0}) (a := z)
          (hmem z |>.mp hz)]
    · rw [Set.indicator_of_notMem (s := E) (a := (y,z)) hz,
        Set.indicator_of_notMem (s := {z : ℕ → ℝ | Pk k y ≤ t ∧ t < Pk k y + z 0}) (a := z)
          (fun h => hz (hmem z |>.mpr h))]
  rw [lintegral_congr hpt, inner_computation hμ k Φ hΦ y]
  by_cases hyt : Pk k y ≤ t
  · rw [if_pos hyt, Set.indicator_of_mem (s := {y : Fin k → ℝ | Pk k y ≤ t}) (a := y) hyt]
  · rw [if_neg hyt, Set.indicator_of_notMem (s := {y : Fin k → ℝ | Pk k y ≤ t}) (a := y) hyt]


/-- The set of nonnegative sequences. -/
def Nneg : Set (ℕ → ℝ) := {x | ∀ j, 0 ≤ x j}

lemma hasExpLaw_Ici_zero {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : HasExpLaw μ) :
    μ (Set.Ici 0) = 1 := by
  have hset : Set.Ici (0:ℝ) = Set.Ioi 0 ∪ {0} := by
    ext x
    simp only [Set.mem_Ici, Set.mem_union, Set.mem_Ioi, Set.mem_singleton_iff]
    constructor
    · intro hx
      rcases eq_or_lt_of_le hx with h | h
      · exact Or.inr h.symm
      · exact Or.inl h
    · rintro (h | h)
      · exact le_of_lt h
      · rw [h]
  rw [hset, measure_union ?_ (measurableSet_singleton 0), hμ.Ioi_zero, hμ.singleton_zero,
    add_zero]
  rw [Set.disjoint_left]
  rintro x hx hy
  simp only [Set.mem_Ioi] at hx
  simp only [Set.mem_singleton_iff] at hy
  linarith

lemma PiN_Nneg {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : HasExpLaw μ) :
    PiN μ Nneg = 1 := by
  have hset : Nneg = Set.univ.pi (fun _ : ℕ => Set.Ici (0:ℝ)) := by
    ext x
    simp only [Nneg, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ici]
  rw [hset, Measure.infinitePi_pi_univ (fun _ : ℕ => μ) (fun _ => measurableSet_Ici)]
  simp only [hasExpLaw_Ici_zero hμ]
  exact tprod_one

lemma Tf_add (m n : ℕ) (x : ℕ → ℝ) : Tf (m+n) x = Tf m x + Tf n (fun i => x (m+i)) := by
  simp only [Tf, Finset.sum_range_add]

lemma Tf_mkSeq_succ (m : ℕ) (r : ℝ) (ζ : ℕ → ℝ) :
    Tf (m+1) (mkSeq (r, ζ)) = r + Tf m ζ := by
  rw [Tf_mkSeq m (r, ζ)]; ring


/-- The shift identity: on the (a.e. full measure) set of nonnegative sequences, the future after
the first gap crossing `t` is described by the shifted sequence. -/
lemma hit_shift_iff {ι : Type*} {t : ℝ} {k : ℕ} (A B : ι → ℝ) (hA : ∀ i, t ≤ A i)
    {x : ℕ → ℝ} (hxN : ∀ j < k, 0 ≤ x j) (hxE : x ∈ Ev t k) :
    (x ∈ AllHit A B) ↔ mkSeq (Tf (k+1) x - t, fun j => x (k+1+j))
      ∈ AllHit (fun i => A i - t) (fun i => B i - t) := by
  have hmono : ∀ m, m ≤ k → Tf m x ≤ Tf k x := by
    intro m hm
    obtain ⟨d, rfl⟩ : ∃ d, k = m + d := ⟨k - m, by omega⟩
    rw [Tf_add]
    have h2 : 0 ≤ Tf d (fun i => x (m+i)) :=
      Finset.sum_nonneg fun j hj => hxN (m+j) (by have := Finset.mem_range.mp hj; omega)
    linarith
  constructor
  · intro hx i
    obtain ⟨m, hm⟩ := hx i
    have hmk : k < m := by
      by_contra h
      have h1 : Tf m x ≤ Tf k x := hmono m (not_lt.mp h)
      have h2 : Tf k x ≤ t := hxE.1
      have h4 := hA i
      linarith [hm.1]
    obtain ⟨m', rfl⟩ : ∃ m', m = k + 1 + m' := ⟨m - k - 1, by omega⟩
    refine ⟨m' + 1, ?_⟩
    rw [Tf_mkSeq_succ]
    have hkey : Tf (k+1) x - t + Tf m' (fun j => x (k+1+j)) = Tf (k+1+m') x - t := by
      rw [Tf_add (k+1) m' x]; ring
    rw [hkey]
    exact ⟨by linarith [hm.1], by linarith [hm.2]⟩
  · intro hx i
    obtain ⟨m', hm'⟩ := hx i
    have h2 : ∀ m : ℕ, Tf (m+1) (mkSeq (Tf (k+1) x - t, fun j => x (k+1+j))) =
        Tf (k+1+m) x - t := by
      intro m
      rw [Tf_mkSeq_succ]
      have hkey : Tf (k+1) x - t + Tf m (fun j => x (k+1+j)) = Tf (k+1+m) x - t := by
        rw [Tf_add (k+1) m x]; ring
      rw [hkey]
    rcases Nat.eq_zero_or_pos m' with h | h
    · rw [h, Tf_zero] at hm'
      have hAt := hA i
      exact absurd hm'.1 (by linarith)
    · obtain ⟨n, rfl⟩ : ∃ n, m' = n + 1 := ⟨m' - 1, by omega⟩
      refine ⟨k + 1 + n, ?_⟩
      have h3 := hm'
      rw [h2 n] at h3
      exact ⟨by linarith [h3.1], by linarith [h3.2]⟩


lemma measure_inter_eq_of_compl_eq_zero {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {N : Set α} (hN : ν Nᶜ = 0) (A : Set α) : ν (A ∩ N) = ν A := by
  refine le_antisymm (measure_mono Set.inter_subset_left) ?_
  have h : A ⊆ (A ∩ N) ∪ Nᶜ := by
    intro x hx
    by_cases hx' : x ∈ N
    · exact Or.inl ⟨hx, hx'⟩
    · exact Or.inr hx'
  calc ν A ≤ ν ((A ∩ N) ∪ Nᶜ) := measure_mono h
    _ ≤ ν (A ∩ N) + ν Nᶜ := @measure_union_le α (Measure α) _ _ ν (A ∩ N) Nᶜ
    _ = ν (A ∩ N) := by rw [hN, add_zero]

lemma measurableSet_Nneg : MeasurableSet (Nneg : Set (ℕ → ℝ)) := by
  have hset : Nneg = Set.univ.pi (fun _ : ℕ => Set.Ici (0:ℝ)) := by
    ext x
    simp only [Nneg, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ici]
  rw [hset]
  exact MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Ici

lemma Tf_mono {x : ℕ → ℝ} (hx : ∀ j, 0 ≤ x j) {m n : ℕ} (hmn : m ≤ n) : Tf m x ≤ Tf n x := by
  obtain ⟨d, rfl⟩ : ∃ d, n = m + d := ⟨n - m, by omega⟩
  rw [Tf_add]
  have h2 : 0 ≤ Tf d (fun i => x (m+i)) := Finset.sum_nonneg fun j _ => hx (m+j)
  linarith

/-- Per-`k` splitting: the event that the interval `(a,t]` is hit by the `k`-th gap is
independent of the future after `t`. -/
lemma splitting_k {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : HasExpLaw μ)
    {t : ℝ} (ht : 0 ≤ t) {a : ℝ} (hat : a < t) (k : ℕ)
    {ι : Type*} [Countable ι] (A B : ι → ℝ) (hA : ∀ i, t ≤ A i) :
    (PiN μ) (Hit a t ∩ Ev t k ∩ AllHit A B)
      = (PiN μ) (Hit a t ∩ Ev t k)
        * (PiN μ) (AllHit (fun i => A i - t) (fun i => B i - t)) := by
  set F : Set (ℕ → ℝ) := AllHit (fun i => A i - t) (fun i => B i - t) with hF
  set Yset : Set (Fin k → ℝ) := {y : Fin k → ℝ | a < Pk k y ∧ Pk k y ≤ t} with hYset
  set T1 : Set (ℕ → ℝ) :=
    {x : ℕ → ℝ | a < Tf k x ∧ Tf k x ≤ t ∧ t < Tf (k+1) x} with hT1
  set ξ : (ℕ → ℝ) → (ℕ → ℝ) :=
    fun x => mkSeq (Tf (k+1) x - t, fun j => x (k+1+j)) with hξ
  set Φ1 : (Fin k → ℝ) → ℝ → (ℕ → ℝ) → ℝ≥0∞ :=
    fun y _ _ => Set.indicator Yset (fun _ => (1:ℝ≥0∞)) y with hΦ1
  set Φ2 : (Fin k → ℝ) → ℝ → (ℕ → ℝ) → ℝ≥0∞ :=
    fun y r ζ => Set.indicator Yset (fun _ => (1:ℝ≥0∞)) y *
      Set.indicator F (fun _ => (1:ℝ≥0∞)) (mkSeq (r, ζ)) with hΦ2
  set A1 : ℝ≥0∞ := ∫⁻ y : Fin k → ℝ, Set.indicator {y : Fin k → ℝ | Pk k y ≤ t}
      (fun y => ENNReal.ofReal (Real.exp (-(t - Pk k y))) *
        Set.indicator Yset (fun _ => (1:ℝ≥0∞)) y) y ∂(PiFin μ k) with hA1
  have hT1_mem : ∀ x : ℕ → ℝ, x ∈ T1 ↔ (a < Tf k x ∧ Tf k x ≤ t ∧ t < Tf (k+1) x) :=
    fun x => Iff.rfl
  have hY_mem : ∀ y : Fin k → ℝ, y ∈ Yset ↔ (a < Pk k y ∧ Pk k y ≤ t) := fun y => Iff.rfl
  have hξ_eq : ∀ x : ℕ → ℝ, ξ x = mkSeq (Tf (k+1) x - t, fun j => x (k+1+j)) := fun x => rfl
  have hΦ1_eq : ∀ (y : Fin k → ℝ) r ζ, Φ1 y r ζ = Set.indicator Yset (fun _ => (1:ℝ≥0∞)) y :=
    fun y r ζ => rfl
  have hΦ2_eq : ∀ (y : Fin k → ℝ) r ζ, Φ2 y r ζ = Set.indicator Yset (fun _ => (1:ℝ≥0∞)) y *
      Set.indicator F (fun _ => (1:ℝ≥0∞)) (mkSeq (r, ζ)) := fun y r ζ => rfl
  have hFmeas : MeasurableSet F := hF ▸ measurableSet_AllHit
  have hYmeas : MeasurableSet Yset := by
    rw [hYset]
    exact MeasurableSet.inter (measurableSet_lt measurable_const (measurable_Pk k))
      (measurableSet_le (measurable_Pk k) measurable_const)
  have hT1meas : MeasurableSet T1 := by
    rw [hT1]
    exact MeasurableSet.inter (measurableSet_lt measurable_const (measurable_Tf k))
      (MeasurableSet.inter (measurableSet_le (measurable_Tf k) measurable_const)
        (measurableSet_lt measurable_const (measurable_Tf (k+1))))
  have hΦ1meas : Measurable fun q : ((Fin k → ℝ) × ℝ) × (ℕ → ℝ) => Φ1 q.1.1 q.1.2 q.2 := by
    have h1 : Measurable fun q : ((Fin k → ℝ) × ℝ) × (ℕ → ℝ) =>
        Set.indicator Yset (fun _ => (1:ℝ≥0∞)) q.1.1 :=
      (measurable_const.indicator hYmeas).comp (measurable_fst.comp measurable_fst)
    simpa only [hΦ1] using h1
  have hΦ2meas : Measurable fun q : ((Fin k → ℝ) × ℝ) × (ℕ → ℝ) => Φ2 q.1.1 q.1.2 q.2 := by
    have h1 : Measurable fun q : ((Fin k → ℝ) × ℝ) × (ℕ → ℝ) =>
        Set.indicator Yset (fun _ => (1:ℝ≥0∞)) q.1.1 :=
      (measurable_const.indicator hYmeas).comp (measurable_fst.comp measurable_fst)
    have h2 : Measurable fun q : ((Fin k → ℝ) × ℝ) × (ℕ → ℝ) =>
        Set.indicator F (fun _ => (1:ℝ≥0∞)) (mkSeq (q.1.2, q.2)) :=
      (measurable_const.indicator hFmeas).comp (measurable_mkSeq.comp (by fun_prop))
    rw [hΦ2]
    exact h1.mul h2
  -- the nonnegativity null set
  have hNc : (PiN μ) (Nnegᶜ : Set (ℕ → ℝ)) = 0 := by
    rw [measure_compl measurableSet_Nneg (by rw [PiN_Nneg hμ]; exact ENNReal.one_ne_top),
      measure_univ, PiN_Nneg hμ, tsub_self]
  -- Step 1a: `Hit a t ∩ Ev t k` has the same measure as `T1`.
  have hstep1a : (PiN μ) (Hit a t ∩ Ev t k) = (PiN μ) T1 := by
    rw [← measure_inter_eq_of_compl_eq_zero hNc (Hit a t ∩ Ev t k),
      ← measure_inter_eq_of_compl_eq_zero hNc T1]
    congr 1
    ext x
    constructor
    · rintro ⟨⟨hxH, hxE⟩, hxN⟩
      obtain ⟨m, hm⟩ := hxH
      have hmk : m ≤ k := by
        by_contra h
        have h1 : Tf (k+1) x ≤ Tf m x := Tf_mono hxN (by omega)
        linarith [hm.2, hxE.2]
      have h3 : Tf m x ≤ Tf k x := Tf_mono hxN hmk
      exact ⟨⟨by linarith [hm.1], hxE.1, hxE.2⟩, hxN⟩
    · rintro ⟨hx, hxN⟩
      simp only [hT1_mem] at hx
      exact ⟨⟨⟨k, ⟨hx.1, hx.2.1⟩⟩, ⟨hx.2.1, hx.2.2⟩⟩, hxN⟩
  -- Step 1b: `Hit a t ∩ Ev t k ∩ AllHit A B` has the same measure as `T1 ∩ ξ ⁻¹' F`.
  have hstep1b : (PiN μ) (Hit a t ∩ Ev t k ∩ AllHit A B) = (PiN μ) (T1 ∩ ξ ⁻¹' F) := by
    rw [← measure_inter_eq_of_compl_eq_zero hNc (Hit a t ∩ Ev t k ∩ AllHit A B),
      ← measure_inter_eq_of_compl_eq_zero hNc (T1 ∩ ξ ⁻¹' F)]
    congr 1
    ext x
    constructor
    · rintro ⟨⟨⟨hxH, hxE⟩, hxG⟩, hxN⟩
      obtain ⟨m, hm⟩ := hxH
      have hmk : m ≤ k := by
        by_contra h
        have h1 : Tf (k+1) x ≤ Tf m x := Tf_mono hxN (by omega)
        linarith [hm.2, hxE.2]
      have h3 : Tf m x ≤ Tf k x := Tf_mono hxN hmk
      have hxT1 : x ∈ T1 := by
        simp only [hT1_mem]; exact ⟨by linarith [hm.1], hxE.1, hxE.2⟩
      have hsh : ξ x ∈ F := by
        simp only [hF, hξ_eq]
        exact (hit_shift_iff A B hA (fun j _ => hxN j) hxE).mp hxG
      exact ⟨⟨hxT1, hsh⟩, hxN⟩
    · rintro ⟨⟨hxT1, hxF⟩, hxN⟩
      simp only [hT1_mem] at hxT1
      have hxE : x ∈ Ev t k := ⟨hxT1.2.1, hxT1.2.2⟩
      have hxG : x ∈ AllHit A B := by
        simp only [hF] at hxF
        simp only [Set.mem_preimage, hξ_eq] at hxF
        exact (hit_shift_iff A B hA (fun j _ => hxN j) hxE).mpr hxF
      exact ⟨⟨⟨⟨k, ⟨hxT1.1, hxT1.2.1⟩⟩, hxE⟩, hxG⟩, hxN⟩
  -- Step 2: the core computation for `T1`.
  have hcore1 := core hμ ht k Φ1 hΦ1meas
  have hξmeas : Measurable ξ := by
    rw [hξ]
    exact measurable_mkSeq.comp (Measurable.prodMk ((measurable_Tf (k+1)).sub measurable_const)
      (Measurable.of_eval fun j => measurable_pi_apply (k+1+j)))
  have hYmem : ∀ (x : ℕ → ℝ), (fun i : Fin k => x i) ∈ Yset ↔ a < Tf k x ∧ Tf k x ≤ t := by
    intro x
    simp only [hY_mem]
    rw [← Tf_eq_Pk]
  have hstep2 : (PiN μ) T1 = A1 := by
    have h1 : (PiN μ) T1 = ∫⁻ x, Set.indicator (Ev t k)
        (fun x : ℕ → ℝ => Φ1 (fun i : Fin k => x i) (Tf (k+1) x - t)
          (fun j : ℕ => x (k+1+j))) x ∂(PiN μ) := by
      rw [← lintegral_indicator_one hT1meas]
      refine lintegral_congr fun x => ?_
      simp only [hΦ1_eq]
      have hT1x : x ∈ T1 ↔ (a < Tf k x ∧ Tf k x ≤ t ∧ t < Tf (k+1) x) := hT1_mem x
      by_cases hx : x ∈ Ev t k
      · by_cases ha : a < Tf k x
        · rw [Set.indicator_of_mem (s := T1) (a := x) (hT1x.mpr ⟨ha, hx.1, hx.2⟩),
            Set.indicator_of_mem (s := Ev t k) (a := x) hx,
            Set.indicator_of_mem (s := Yset) (a := fun i : Fin k => x i) ((hYmem x).mpr ⟨ha, hx.1⟩)] <;> simp
        · rw [Set.indicator_of_notMem (s := T1) (a := x) (fun h => ha (hT1x.mp h).1),
            Set.indicator_of_mem (s := Ev t k) (a := x) hx,
            Set.indicator_of_notMem (s := Yset) (a := fun i : Fin k => x i)
              (fun h => ha ((hYmem x).mp h).1)] <;> simp
      · rw [Set.indicator_of_notMem (s := Ev t k) (a := x) hx,
          Set.indicator_of_notMem (s := T1) (a := x)
            (fun h => hx (by exact ⟨(hT1x.mp h).2.1, (hT1x.mp h).2.2⟩))]
    have h2 : ∫⁻ x, Set.indicator (Ev t k)
        (fun x : ℕ → ℝ => Φ1 (fun i : Fin k => x i) (Tf (k+1) x - t)
          (fun j : ℕ => x (k+1+j))) x ∂(PiN μ) = A1 := by
      rw [hcore1, hA1]
      refine lintegral_congr fun y => ?_
      by_cases hy : y ∈ {y : Fin k → ℝ | Pk k y ≤ t}
      · rw [Set.indicator_of_mem (s := {y : Fin k → ℝ | Pk k y ≤ t}) (a := y) hy,
          Set.indicator_of_mem (s := {y : Fin k → ℝ | Pk k y ≤ t}) (a := y) hy]
        simp only [hΦ1_eq, lintegral_const, measure_univ, mul_one]
      · rw [Set.indicator_of_notMem (s := {y : Fin k → ℝ | Pk k y ≤ t}) (a := y) hy,
          Set.indicator_of_notMem (s := {y : Fin k → ℝ | Pk k y ≤ t}) (a := y) hy]
    rw [h1, h2]
  -- Step 3: the core computation for `T1 ∩ ξ ⁻¹' F`.
  have hcore2 := core hμ ht k Φ2 hΦ2meas
  have hstep3 : (PiN μ) (T1 ∩ ξ ⁻¹' F) = A1 * (PiN μ) F := by
    have h1 : (PiN μ) (T1 ∩ ξ ⁻¹' F) = ∫⁻ x, Set.indicator (Ev t k)
        (fun x : ℕ → ℝ => Φ2 (fun i : Fin k => x i) (Tf (k+1) x - t)
          (fun j : ℕ => x (k+1+j))) x ∂(PiN μ) := by
      rw [← lintegral_indicator_one (hT1meas.inter (hFmeas.preimage hξmeas))]
      refine lintegral_congr fun x => ?_
      simp only [hΦ2_eq]
      have hT1x : x ∈ T1 ↔ (a < Tf k x ∧ Tf k x ≤ t ∧ t < Tf (k+1) x) := hT1_mem x
      have hξx : x ∈ ξ ⁻¹' F ↔ mkSeq (Tf (k+1) x - t, fun j => x (k+1+j)) ∈ F := by
        simp only [Set.mem_preimage, hξ_eq]
      by_cases hxT : x ∈ T1 ∩ ξ ⁻¹' F
      · rw [Set.indicator_of_mem (s := T1 ∩ ξ ⁻¹' F) (a := x) hxT]
        have hxE : x ∈ Ev t k := by
          have := (hT1x.mp hxT.1); exact ⟨this.2.1, this.2.2⟩
        have hx1 := (hT1x.mp hxT.1)
        rw [Set.indicator_of_mem (s := Ev t k) (a := x) hxE,
          Set.indicator_of_mem (s := Yset) (a := fun i : Fin k => x i)
            ((hYmem x).mpr ⟨hx1.1, hx1.2.1⟩),
          Set.indicator_of_mem (s := F) (a := mkSeq (Tf (k+1) x - t, fun j => x (k+1+j)))
            ((hξx.mp hxT.2))] <;> simp
      · rw [Set.indicator_of_notMem (s := T1 ∩ ξ ⁻¹' F) (a := x) hxT]
        by_cases hxE : x ∈ Ev t k
        · rw [Set.indicator_of_mem (s := Ev t k) (a := x) hxE]
          by_cases ha : a < Tf k x
          · rw [Set.indicator_of_mem (s := Yset) (a := fun i : Fin k => x i)
                ((hYmem x).mpr ⟨ha, hxE.1⟩),
              Set.indicator_of_notMem (s := F) (a := mkSeq (Tf (k+1) x - t, fun j => x (k+1+j)))
                (fun h => hxT ⟨hT1x.mpr ⟨ha, hxE.1, hxE.2⟩, hξx.mpr h⟩)] <;> simp
          · rw [Set.indicator_of_notMem (s := Yset) (a := fun i : Fin k => x i)
                (fun h => ha ((hYmem x).mp h).1)] <;> simp
        · rw [Set.indicator_of_notMem (s := Ev t k) (a := x) hxE] <;> simp
    have h2 : ∫⁻ x, Set.indicator (Ev t k)
        (fun x : ℕ → ℝ => Φ2 (fun i : Fin k => x i) (Tf (k+1) x - t)
          (fun j : ℕ => x (k+1+j))) x ∂(PiN μ) = A1 * (PiN μ) F := by
      rw [hcore2, hA1]
      have hνF : (PiN μ) F = ∫⁻ q : ℝ × (ℕ → ℝ),
          Set.indicator F (fun _ => (1:ℝ≥0∞)) (mkSeq (q.1, q.2)) ∂(μ.prod (PiN μ)) := by
        rw [← lintegral_indicator_one hFmeas]
        change ∫⁻ a : ℕ → ℝ, Set.indicator F (fun _ => (1:ℝ≥0∞)) a ∂(PiN μ) = _
        rw [lintegral_mkSeq _ (measurable_const.indicator hFmeas)]
      have hpt : ∀ y : Fin k → ℝ, Set.indicator {y : Fin k → ℝ | Pk k y ≤ t}
            (fun y => ENNReal.ofReal (Real.exp (-(t - Pk k y))) *
              (∫⁻ q : ℝ × (ℕ → ℝ), Φ2 y q.1 q.2 ∂(μ.prod (PiN μ)))) y
          = Set.indicator {y : Fin k → ℝ | Pk k y ≤ t}
              (fun y => ENNReal.ofReal (Real.exp (-(t - Pk k y))) *
                Set.indicator Yset (fun _ => (1:ℝ≥0∞)) y) y * (PiN μ) F := by
        intro y
        by_cases hy : y ∈ {y : Fin k → ℝ | Pk k y ≤ t}
        · rw [Set.indicator_of_mem (s := {y : Fin k → ℝ | Pk k y ≤ t}) (a := y) hy,
            Set.indicator_of_mem (s := {y : Fin k → ℝ | Pk k y ≤ t}) (a := y) hy]
          simp only [hΦ2_eq]
          have hfm : Measurable fun q : ℝ × (ℕ → ℝ) =>
              Set.indicator F (fun _ => (1:ℝ≥0∞)) (mkSeq (q.1, q.2)) :=
            (measurable_const.indicator hFmeas).comp
              (measurable_mkSeq.comp (measurable_fst.prodMk measurable_snd))
          rw [lintegral_const_mul (Set.indicator Yset (fun _ => (1:ℝ≥0∞)) y) hfm, hνF] <;> ring
        · rw [Set.indicator_of_notMem (s := {y : Fin k → ℝ | Pk k y ≤ t}) (a := y) hy,
            Set.indicator_of_notMem (s := {y : Fin k → ℝ | Pk k y ≤ t}) (a := y) hy,
            zero_mul]
      rw [lintegral_congr hpt, lintegral_mul_const ((PiN μ) F) (by
        refine Measurable.indicator ?_ ?_
        · refine Measurable.mul ?_ ?_
          · exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
              (measurable_const.sub (measurable_Pk k)).neg)
          · exact measurable_const.indicator hYmeas
        · exact measurableSet_le (measurable_Pk k) measurable_const)]
    rw [h1, h2]
  rw [hstep1a, hstep1b, hstep3, hstep2]


/-- The splitting (strong Markov) property at time `t`: the event that `(a,t]` is hit is
independent of the future after `t`. -/
theorem splitting {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : HasExpLaw μ)
    {t : ℝ} (ht : 0 ≤ t) {a : ℝ} (hat : a < t)
    {ι : Type*} [Countable ι] (A B : ι → ℝ) (hA : ∀ i, t ≤ A i) :
    (PiN μ) (Hit a t ∩ AllHit A B)
      = (PiN μ) (Hit a t) * (PiN μ) (AllHit (fun i => A i - t) (fun i => B i - t)) := by
  set F : Set (ℕ → ℝ) := AllHit (fun i => A i - t) (fun i => B i - t) with hF
  have hFmeas : MeasurableSet F := hF ▸ measurableSet_AllHit
  have hNc : (PiN μ) (Nnegᶜ : Set (ℕ → ℝ)) = 0 := by
    rw [measure_compl measurableSet_Nneg (by rw [PiN_Nneg hμ]; exact ENNReal.one_ne_top),
      measure_univ, PiN_Nneg hμ, tsub_self]
  have hEv_meas : ∀ k : ℕ, MeasurableSet (Ev t k) := measurable_Ev t
  have hEv_compl : (⋃ k : ℕ, Ev t k)ᶜ = {x : ℕ → ℝ | ∀ k, Tf k x ≤ t} := by
    ext x
    constructor
    · intro hx k
      induction k with
      | zero => simpa using ht
      | succ k ih =>
        by_contra hk
        exact hx (Set.mem_iUnion.mpr ⟨k, ⟨ih, not_le.mp hk⟩⟩)
    · intro hx
      rw [Set.mem_compl_iff, Set.mem_iUnion]
      rintro ⟨k, hk1, hk2⟩
      exact absurd (hx (k+1)) (not_le.mpr hk2)
  have hcoverall : (PiN μ) (⋃ k : ℕ, Ev t k) = 1 := by
    have hcompl : (PiN μ) ((⋃ k : ℕ, Ev t k)ᶜ) = 0 := by
      rw [hEv_compl]; exact ae_divergence hμ t
    have h := measure_compl (μ := PiN μ) (s := (⋃ k : ℕ, Ev t k)ᶜ)
      (MeasurableSet.iUnion hEv_meas).compl (by rw [hcompl]; exact ENNReal.zero_ne_top)
    rw [compl_compl, measure_univ, hcompl, tsub_zero] at h
    exact h
  have hEvN_disj : Pairwise (Function.onFun Disjoint fun k : ℕ => Ev t k ∩ Nneg) := by
    intro j k hjk
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨hxj, hxN⟩ ⟨hxk, _⟩
    simp only [Nneg, Set.mem_setOf_eq] at hxN
    simp only [Ev, Set.mem_setOf_eq] at hxj hxk
    rcases lt_or_gt_of_ne hjk with h | h
    · have := Tf_mono hxN (show j + 1 ≤ k by omega)
      linarith [hxj.2, hxk.1]
    · have := Tf_mono hxN (show k + 1 ≤ j by omega)
      linarith [hxk.2, hxj.1]
  have hEvN_meas : ∀ k : ℕ, MeasurableSet (Ev t k ∩ Nneg) := fun k =>
    (hEv_meas k).inter measurableSet_Nneg
  have hEvN_cover : (PiN μ) (⋃ k : ℕ, (Ev t k ∩ Nneg)) = 1 := by
    rw [← Set.iUnion_inter]
    exact (measure_inter_eq_of_compl_eq_zero hNc (⋃ k : ℕ, Ev t k)).trans hcoverall
  have hEvNc : (PiN μ) ((⋃ k : ℕ, (Ev t k ∩ Nneg))ᶜ) = 0 := by
    rw [measure_compl (MeasurableSet.iUnion hEvN_meas)
      (by rw [hEvN_cover]; exact ENNReal.one_ne_top), measure_univ, hEvN_cover, tsub_self]
  -- each summand
  have hterm : ∀ k : ℕ, (PiN μ) ((Hit a t ∩ AllHit A B) ∩ (Ev t k ∩ Nneg))
      = (PiN μ) (Hit a t ∩ Ev t k) * (PiN μ) F := by
    intro k
    rw [show (Hit a t ∩ AllHit A B) ∩ (Ev t k ∩ Nneg)
        = ((Hit a t ∩ Ev t k) ∩ AllHit A B) ∩ Nneg from by
      ext x; simp only [Set.mem_inter_iff]; tauto]
    rw [measure_inter_eq_of_compl_eq_zero hNc]
    rw [show (Hit a t ∩ Ev t k) ∩ AllHit A B = Hit a t ∩ Ev t k ∩ AllHit A B from by
      ext x; tauto]
    rw [show (Hit a t ∩ Ev t k ∩ AllHit A B) = (Hit a t ∩ Ev t k ∩ AllHit A B) from rfl]
    rw [splitting_k hμ ht hat k A B hA]
  -- the sum of `ν (Hit ∩ Ev k)`
  have hterm2 : ∀ k : ℕ, (PiN μ) (Hit a t ∩ Ev t k ∩ Nneg) = (PiN μ) (Hit a t ∩ Ev t k) := by
    intro k
    exact measure_inter_eq_of_compl_eq_zero hNc (Hit a t ∩ Ev t k)
  have hsum2 : (∑' k : ℕ, (PiN μ) (Hit a t ∩ Ev t k)) = (PiN μ) (Hit a t) := by
    rw [← measure_inter_eq_of_compl_eq_zero hEvNc (Hit a t), Set.inter_iUnion,
      measure_iUnion]
    · refine tsum_congr fun k => ?_
      rw [show Hit a t ∩ (Ev t k ∩ Nneg) = Hit a t ∩ Ev t k ∩ Nneg from by
        ext x; simp only [Set.mem_inter_iff]; tauto]
      exact (hterm2 k).symm
    · intro j k hjk
      rw [Function.onFun]
      exact (hEvN_disj hjk).mono Set.inter_subset_right Set.inter_subset_right
    · intro k
      exact measurableSet_Hit.inter (hEvN_meas k)
  rw [← measure_inter_eq_of_compl_eq_zero hEvNc (Hit a t ∩ AllHit A B), Set.inter_iUnion,
    measure_iUnion]
  · rw [show (∑' k : ℕ, (PiN μ) ((Hit a t ∩ AllHit A B) ∩ (Ev t k ∩ Nneg)))
        = ∑' k : ℕ, (PiN μ) (Hit a t ∩ Ev t k) * (PiN μ) F from tsum_congr hterm,
      ENNReal.tsum_mul_right, hsum2]
  · intro j k hjk
    rw [Function.onFun]
    exact (hEvN_disj hjk).mono Set.inter_subset_right Set.inter_subset_right
  · intro k
    exact (measurableSet_Hit.inter measurableSet_AllHit).inter (hEvN_meas k)


lemma measure_eq_one_of_compl_eq_zero {α : Type*} [MeasurableSpace α] {ν : Measure α}
    [IsProbabilityMeasure ν] {s : Set α} (h : ν sᶜ = 0) : ν s = 1 := by
  refine le_antisymm prob_le_one ?_
  calc (1 : ℝ≥0∞) = ν (Set.univ : Set α) := measure_univ.symm
    _ ≤ ν (s ∪ sᶜ) := measure_mono fun x _ => by by_cases hx : x ∈ s <;> simp [hx]
    _ ≤ ν s + ν sᶜ := @measure_union_le α (Measure α) _ _ ν s sᶜ
    _ = ν s := by rw [h, add_zero]

/-- The measure of the event that `(0,b]` is hit. -/
lemma hit_zero {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : HasExpLaw μ) {b : ℝ}
    (hb : 0 ≤ b) : (PiN μ) (Hit 0 b) = ENNReal.ofReal (1 - Real.exp (-b)) := by
  have hnull0 : (PiN μ) {x : ℕ → ℝ | x 0 = 0} = 0 := by
    change (PiN μ) ((fun x : ℕ → ℝ => x 0) ⁻¹' ({0} : Set ℝ)) = 0
    rw [← Measure.map_apply (measurable_pi_apply (0:ℕ)) (measurableSet_singleton 0),
      Measure.infinitePi_map_eval (fun _ : ℕ => μ) 0, hμ.singleton_zero]
  have hNc : (PiN μ) (Nnegᶜ : Set (ℕ → ℝ)) = 0 := by
    rw [measure_compl measurableSet_Nneg (by rw [PiN_Nneg hμ]; exact ENNReal.one_ne_top),
      measure_univ, PiN_Nneg hμ, tsub_self]
  have hae : (Hit 0 b)ᶜ =ᵐ[PiN μ] {x : ℕ → ℝ | b < x 0} := by
    filter_upwards [show ∀ᵐ x ∂(PiN μ), x ∈ Nneg from MeasureTheory.ae_iff.mpr (by
        rw [show {a : ℕ → ℝ | ¬ a ∈ Nneg} = (Nnegᶜ : Set (ℕ → ℝ)) from rfl]; exact hNc),
      show ∀ᵐ x ∂(PiN μ), x 0 ≠ 0 from MeasureTheory.ae_iff.mpr (by
        rw [show {a : ℕ → ℝ | ¬ a 0 ≠ 0} = {x : ℕ → ℝ | x 0 = 0} from by ext x; simp]
        exact hnull0)] with x hxN hx0
    have hxN' : ∀ j, 0 ≤ x j := hxN
    refine propext ⟨?_, ?_⟩
    · intro hx
      by_contra hb'
      have hb'' : x 0 ≤ b := not_lt.mp hb'
      have hpos : 0 < x 0 := lt_of_le_of_ne (hxN' 0) (Ne.symm hx0)
      exact hx ⟨1, by simp only [Tf, Finset.sum_range_one]; exact ⟨hpos, hb''⟩⟩
    · intro hb'
      have hb'' : b < x 0 := hb'
      rw [Hit]
      rintro ⟨k, hk⟩
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h
        simp only [Tf_zero, Set.mem_Ioc] at hk
        linarith [hk.1]
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        have hle : x 0 ≤ Tf (j+1) x := by
          rw [show j+1 = 1+j by omega, Tf_add 1 j x,
            show Tf 1 x = x 0 from by simp only [Tf, Finset.sum_range_one]]
          have h2 : 0 ≤ Tf j (fun i => x (1+i)) :=
            Finset.sum_nonneg fun i _ => hxN' (1+i)
          linarith
        linarith [hk.2, hb'', hle]
  have hcompl : (PiN μ) (Hit 0 b)ᶜ = ENNReal.ofReal (Real.exp (-b)) := by
    have h1 : (PiN μ) (Hit 0 b)ᶜ = (PiN μ) {x : ℕ → ℝ | b < x 0} := measure_congr hae
    rw [h1]
    change (PiN μ) ((fun x : ℕ → ℝ => x 0) ⁻¹' Set.Ioi b) = ENNReal.ofReal (Real.exp (-b))
    rw [← Measure.map_apply (measurable_pi_apply (0:ℕ)) measurableSet_Ioi,
      Measure.infinitePi_map_eval (fun _ : ℕ => μ) 0, hμ.Ioi hb]
  have h := measure_compl (μ := PiN μ) (s := (Hit 0 b)ᶜ) (measurableSet_Hit.compl)
    (by rw [hcompl]; exact ENNReal.ofReal_ne_top)
  rw [compl_compl, measure_univ, hcompl] at h
  rw [h, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (Real.exp_nonneg (-b))]

/-- The measure of the event that `(a,b]` is hit. -/
lemma hit_single {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : HasExpLaw μ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (PiN μ) (Hit a b) = ENNReal.ofReal (1 - Real.exp (-(b - a))) := by
  rcases eq_or_lt_of_le hab with h | h
  · subst h
    have hnil : Hit a a = ∅ := by
      ext x; simp only [Hit, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists]
      exact fun k => by rw [Set.Ioc_self]; exact Set.notMem_empty _
    rw [hnil, measure_empty]
    norm_num
  · rcases eq_or_lt_of_le ha with ha0 | ha0
    · subst ha0
      rw [sub_zero]
      exact hit_zero hμ (le_trans le_rfl hab)
    · have hb : 0 ≤ b := le_trans ha hab
      have h0b := hit_zero hμ hb
      have h0a := hit_zero hμ ha
      have h0c := hit_zero hμ (sub_nonneg.mpr hab)
      have hunion : Hit (0:ℝ) b = Hit 0 a ∪ Hit a b := by
        ext x
        simp only [Hit, Set.mem_union, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨k, hk⟩
          rcases le_or_gt (Tf k x) a with h' | h'
          · exact Or.inl ⟨k, ⟨hk.1, h'⟩⟩
          · exact Or.inr ⟨k, ⟨h', hk.2⟩⟩
        · rintro (⟨k, hk⟩ | ⟨k, hk⟩)
          · exact ⟨k, ⟨hk.1, le_trans hk.2 hab⟩⟩
          · exact ⟨k, ⟨lt_of_le_of_lt ha hk.1, hk.2⟩⟩
      have hinter : (PiN μ) (Hit (0:ℝ) a ∩ Hit a b)
          = (PiN μ) (Hit 0 a) * (PiN μ) (Hit 0 (b - a)) := by
        have hs := splitting (μ := μ) hμ ha ha0 (fun _ : Fin 1 => a) (fun _ : Fin 1 => b)
          (fun _ => le_rfl)
        rwa [show AllHit (fun _ : Fin 1 => a) (fun _ : Fin 1 => b) = Hit a b from by
              ext x; simp only [AllHit, Set.mem_ofPred_eq]
              exact ⟨fun h => h 0, fun h _ => h⟩,
             show AllHit (fun _ : Fin 1 => a - a) (fun _ : Fin 1 => b - a) = Hit 0 (b - a)
               from by
              ext x; simp only [AllHit, Set.mem_ofPred_eq, sub_self]
              exact ⟨fun h => h 0, fun h _ => h⟩] at hs
      have huai := measure_union_add_inter (μ := PiN μ) (t := Hit a b) (Hit (0:ℝ) a)
        (measurableSet_Hit (a := a) (b := b))
      rw [← hunion] at huai
      have hfin1 : (PiN μ) (Hit 0 b) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top prob_le_one
      have hfin2 : (PiN μ) (Hit 0 a) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top prob_le_one
      have hfin3 : (PiN μ) (Hit a b) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top prob_le_one
      have hfin4 : (PiN μ) (Hit (0:ℝ) a ∩ Hit a b) ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.one_ne_top prob_le_one
      have hnnb : 0 ≤ 1 - Real.exp (-b) := by
        have h1 : Real.exp (-b) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
        linarith
      have hnna : 0 ≤ 1 - Real.exp (-a) := by
        have h1 : Real.exp (-a) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
        linarith
      have hnnc : 0 ≤ 1 - Real.exp (-(b - a)) := by
        have h1 : Real.exp (-(b - a)) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
        linarith
      have hreal : ((PiN μ) (Hit 0 b)).toReal + ((PiN μ) (Hit (0:ℝ) a ∩ Hit a b)).toReal
          = ((PiN μ) (Hit 0 a)).toReal + ((PiN μ) (Hit a b)).toReal := by
        rw [← ENNReal.toReal_add hfin1 hfin4, huai, ENNReal.toReal_add hfin2 hfin3]
      rw [h0b, hinter, ENNReal.toReal_mul, h0a, h0c, ENNReal.toReal_ofReal hnnb,
        ENNReal.toReal_ofReal hnna, ENNReal.toReal_ofReal hnnc] at hreal
      have hexp : Real.exp (-b) = Real.exp (-a) * Real.exp (-(b - a)) := by
        rw [← Real.exp_add]; congr 1; ring
      have hgoal : ((PiN μ) (Hit a b)).toReal = 1 - Real.exp (-(b - a)) := by
        rw [hexp] at hreal
        linarith
      refine (ENNReal.toReal_eq_toReal_iff' hfin3 ENNReal.ofReal_ne_top).mp ?_
      rw [ENNReal.toReal_ofReal hnnc]
      exact hgoal

end Work.ChenPlan.LinearSieve.Selberg.HitAux
