import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Commons.Probability.Independence.iIndepFun_curry_flat_real

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Commons.Probability.Bernoulli

/-- The Rademacher (symmetric Bernoulli) measure on `ℝ`: mass `1/2` at `1` and `1/2` at `-1`. -/
private noncomputable def rademacherR : Measure ℝ :=
  bernoulliMeasure (1 : ℝ) (-1) (⟨1 / 2, by norm_num⟩ : unitInterval)

private lemma rademacherR_real_one : rademacherR.real {1} = 1 / 2 := by
  rw [rademacherR]
  rw [bernoulliMeasure_real_apply_of_mem_of_notMem (p := (⟨1 / 2, by norm_num⟩ : unitInterval))
    (x := (1 : ℝ)) (y := (-1 : ℝ)) (s := ({(1 : ℝ)} : Set ℝ))
    (by measurability) (by simp) (by norm_num)]

private lemma rademacherR_real_neg_one : rademacherR.real {-1} = 1 / 2 := by
  rw [rademacherR]
  rw [bernoulliMeasure_real_apply_of_notMem_of_mem (p := (⟨1 / 2, by norm_num⟩ : unitInterval))
    (x := (1 : ℝ)) (y := (-1 : ℝ)) (s := ({( -1 : ℝ)} : Set ℝ))
    (by measurability) (by norm_num) (by simp)]
  norm_num

/-- **Measurable form.**  If `M` has independent Rademacher entries *and* every entry is
measurable, then the probability that `M` is singular is at least `(1/2)^n`. -/
private theorem rademacher_det_lower_measurable {n : ℕ} (hn : 2 ≤ n) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (M : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hMmeas : ∀ i j : Fin n, Measurable (fun ω => M ω i j))
    (hMind : ProbabilityTheory.iIndepFun (fun p : Fin n × Fin n => (M · p.1 p.2)) P)
    (hMlaw : ∀ i j : Fin n, ProbabilityTheory.HasLaw (M · i j) rademacherR P) :
    (1 / 2) ^ n ≤ P.real {ω | (M ω).det = 0} := by
  classical
  -- two distinct row indices
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  have hab : a ≠ b := by
    intro h
    have h2 := Fin.ext_iff.mp h
    simp [a, b] at h2
  -- transpose of the flat family is independent
  have htrans : ProbabilityTheory.iIndepFun
      (fun p : Fin n × Fin n => (fun ω => M ω p.2 p.1)) P := by
    have h := hMind.precomp (g := fun p : Fin n × Fin n => (p.2, p.1)) (by
      intro p q hpq
      simp only [Prod.mk.injEq] at hpq
      exact Prod.ext hpq.2 hpq.1)
    simpa using h
  -- columns of `M` are independent
  have hcol : ProbabilityTheory.iIndepFun
      (fun j : Fin n => fun ω => fun i : Fin n => M ω i j) P :=
    Commons.Probability.Independence.iIndepFun_curry_flat_real
      (X := fun j i => fun ω => M ω i j) (fun j i => hMmeas i j) htrans
  -- pairs `(M a j, M b j)` are independent over `j`
  let g : Fin n → Ω → ℝ × ℝ := fun j ω => (M ω a j, M ω b j)
  have hpair : ProbabilityTheory.iIndepFun g P := by
    have h := hcol.comp (fun _ : Fin n => fun v : Fin n → ℝ => (v a, v b))
      (fun _ => by fun_prop)
    simpa [g, Function.comp_def] using h
  -- the events of interest
  let E : Fin n → Set Ω := fun j => {ω | M ω a j = M ω b j}
  have hEmeas : ∀ j : Fin n,
      MeasurableSet[(inferInstance : MeasurableSpace (ℝ × ℝ)).comap (g j)] (E j) := by
    intro j
    have hset : E j = (g j) ⁻¹' ({q : ℝ × ℝ | q.1 = q.2}) := rfl
    rw [hset]
    exact (MeasurableSpace.measurableSet_comap).2
      ⟨{q : ℝ × ℝ | q.1 = q.2},
        (isClosed_eq continuous_fst continuous_snd).measurableSet, rfl⟩
  have hInter : P (⋂ j, E j) = ∏ j, P (E j) := hpair.meas_iInter hEmeas
  -- each factor is at least `1/2`
  have hfactor : ∀ j : Fin n, (1 / 2 : ℝ) ≤ P.real (E j) := by
    intro j
    let A1 : Set Ω := {ω | M ω a j = 1}
    let B1 : Set Ω := {ω | M ω b j = 1}
    let Am : Set Ω := {ω | M ω a j = -1}
    let Bm : Set Ω := {ω | M ω b j = -1}
    have hindep : (fun ω => M ω a j) ⟂ᵢ[P] (fun ω => M ω b j) :=
      hMind.indepFun (i := (a, j)) (j := (b, j)) (by
        intro h
        exact hab (Prod.ext_iff.mp h).1)
    have hA1meas : MeasurableSet A1 := by
      show MeasurableSet ((fun ω => M ω a j) ⁻¹' {1})
      exact (hMmeas a j) (measurableSet_singleton 1)
    have hB1meas : MeasurableSet B1 := by
      show MeasurableSet ((fun ω => M ω b j) ⁻¹' {1})
      exact (hMmeas b j) (measurableSet_singleton 1)
    have hAmmeas : MeasurableSet Am := by
      show MeasurableSet ((fun ω => M ω a j) ⁻¹' {-1})
      exact (hMmeas a j) (measurableSet_singleton (-1))
    have hBmmeas : MeasurableSet Bm := by
      show MeasurableSet ((fun ω => M ω b j) ⁻¹' {-1})
      exact (hMmeas b j) (measurableSet_singleton (-1))
    have hPA1 : P.real A1 = 1 / 2 := by
      have h := (hMlaw a j).measureReal_eq (p := fun x : ℝ => x = 1)
        (by measurability)
      rw [show {x : ℝ | x = 1} = ({1} : Set ℝ) from rfl, rademacherR_real_one] at h
      simpa [A1] using h
    have hPB1 : P.real B1 = 1 / 2 := by
      have h := (hMlaw b j).measureReal_eq (p := fun x : ℝ => x = 1)
        (by measurability)
      rw [show {x : ℝ | x = 1} = ({1} : Set ℝ) from rfl, rademacherR_real_one] at h
      simpa [B1] using h
    have hPAm : P.real Am = 1 / 2 := by
      have h := (hMlaw a j).measureReal_eq (p := fun x : ℝ => x = -1)
        (by measurability)
      rw [show {x : ℝ | x = -1} = ({-1} : Set ℝ) from rfl, rademacherR_real_neg_one] at h
      simpa [Am] using h
    have hPBm : P.real Bm = 1 / 2 := by
      have h := (hMlaw b j).measureReal_eq (p := fun x : ℝ => x = -1)
        (by measurability)
      rw [show {x : ℝ | x = -1} = ({-1} : Set ℝ) from rfl, rademacherR_real_neg_one] at h
      simpa [Bm] using h
    have hI1enn : P (A1 ∩ B1) = P A1 * P B1 :=
      hindep.measure_inter_preimage_eq_mul ({1} : Set ℝ) ({1} : Set ℝ)
        (measurableSet_singleton 1) (measurableSet_singleton 1)
    have hImenn : P (Am ∩ Bm) = P Am * P Bm :=
      hindep.measure_inter_preimage_eq_mul ({-1} : Set ℝ) ({-1} : Set ℝ)
        (measurableSet_singleton (-1)) (measurableSet_singleton (-1))
    have hI1 : P.real (A1 ∩ B1) = 1 / 4 := by
      rw [measureReal_def, hI1enn, ENNReal.toReal_mul, ← measureReal_def, ← measureReal_def,
        hPA1, hPB1]
      norm_num
    have hIm : P.real (Am ∩ Bm) = 1 / 4 := by
      rw [measureReal_def, hImenn, ENNReal.toReal_mul, ← measureReal_def, ← measureReal_def,
        hPAm, hPBm]
      norm_num
    have hsub : (A1 ∩ B1) ∪ (Am ∩ Bm) ⊆ E j := by
      intro ω hω
      rcases hω with hω | hω
      · rw [Set.mem_inter_iff] at hω
        simp only [A1, B1, Set.mem_ofPred_eq] at hω
        simp only [E, Set.mem_ofPred_eq]
        rw [hω.1, hω.2]
      · rw [Set.mem_inter_iff] at hω
        simp only [Am, Bm, Set.mem_ofPred_eq] at hω
        simp only [E, Set.mem_ofPred_eq]
        rw [hω.1, hω.2]
    have hdisj : Disjoint (A1 ∩ B1) (Am ∩ Bm) := by
      rw [Set.disjoint_left]
      intro ω h1 h2
      rw [Set.mem_inter_iff] at h1 h2
      simp only [A1, B1, Set.mem_ofPred_eq] at h1
      simp only [Am, Bm, Set.mem_ofPred_eq] at h2
      rw [h1.1] at h2
      norm_num at h2
    have hmeasBm : MeasurableSet (Am ∩ Bm) := hAmmeas.inter hBmmeas
    have hunion : P.real ((A1 ∩ B1) ∪ (Am ∩ Bm)) =
        P.real (A1 ∩ B1) + P.real (Am ∩ Bm) :=
      measureReal_union hdisj hmeasBm
    calc (1 / 2 : ℝ) = 1 / 4 + 1 / 4 := by norm_num
      _ = P.real (A1 ∩ B1) + P.real (Am ∩ Bm) := by rw [hI1, hIm]
      _ = P.real ((A1 ∩ B1) ∪ (Am ∩ Bm)) := hunion.symm
      _ ≤ P.real (E j) := measureReal_mono hsub (by finiteness)
  -- assemble
  have hInter_ge : (1 / 2 : ENNReal) ^ n ≤ P (⋂ j, E j) := by
    rw [hInter]
    calc (1 / 2 : ENNReal) ^ n = ∏ _j : Fin n, (1 / 2 : ENNReal) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ ∏ j : Fin n, P (E j) := by
          refine Finset.prod_le_prod (fun j _ => by positivity) (fun j _ => ?_)
          calc (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2) := by simp
            _ ≤ ENNReal.ofReal (P.real (E j)) := ENNReal.ofReal_le_ofReal (hfactor j)
            _ ≤ P (E j) := ENNReal.ofReal_toReal_le
  have hInter_real : (1 / 2 : ℝ) ^ n ≤ P.real (⋂ j, E j) := by
    have hne : P (⋂ j, E j) ≠ ∞ := by finiteness
    have hhalf : ((1 / 2 : ENNReal)).toReal = 1 / 2 := by norm_num
    have h := ENNReal.toReal_mono hne hInter_ge
    rw [ENNReal.toReal_pow, hhalf] at h
    rwa [measureReal_def]
  -- the event of equal rows implies singularity
  have hsub2 : (⋂ j, E j) ⊆ {ω | (M ω).det = 0} := by
    intro ω hω
    rw [Set.mem_iInter] at hω
    simp only [E, Set.mem_ofPred_eq] at hω
    exact Matrix.det_zero_of_row_eq hab (funext fun j => hω j)
  calc (1 / 2) ^ n = (1 / 2 : ℝ) ^ n := rfl
    _ ≤ P.real (⋂ j, E j) := hInter_real
    _ ≤ P.real {ω | (M ω).det = 0} := measureReal_mono hsub2 (by finiteness)

theorem rademacher_det_lower {n : ℕ} (hn : 2 ≤ n) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (M : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hMind : ProbabilityTheory.iIndepFun (fun p : Fin n × Fin n => (M · p.1 p.2)) P)
    (hMlaw : ∀ i j : Fin n, ProbabilityTheory.HasLaw (M · i j)
      (ProbabilityTheory.bernoulliMeasure 1 (-1) ⟨1/2, by norm_num⟩) P) :
    (1 / 2) ^ n ≤ P.real {ω | (M ω).det = 0} := by
  classical
  -- replace `M` by a measurable version `N`, equal to `M` almost everywhere
  let N : Ω → Matrix (Fin n) (Fin n) ℝ :=
    fun ω i j => (hMlaw i j).aemeasurable.mk (M · i j) ω
  have hNmeas : ∀ i j : Fin n, Measurable (fun ω => N ω i j) :=
    fun i j => (hMlaw i j).aemeasurable.measurable_mk
  have hNae : ∀ i j : Fin n, (fun ω => N ω i j) =ᵐ[P] (fun ω => M ω i j) :=
    fun i j => (hMlaw i j).aemeasurable.ae_eq_mk.symm
  have hMindN : ProbabilityTheory.iIndepFun (fun p : Fin n × Fin n => (N · p.1 p.2)) P :=
    hMind.congr (fun p => (hNae p.1 p.2).symm)
  have hMlawN : ∀ i j : Fin n,
      ProbabilityTheory.HasLaw (N · i j) rademacherR P :=
    fun i j => (hMlaw i j).congr (hNae i j)
  have hmain := rademacher_det_lower_measurable hn P N hNmeas hMindN hMlawN
  -- transfer the bound from `N` back to `M`
  have hNae_all : ∀ᶠ ω in ae P, N ω = M ω := by
    have h1 : ∀ᶠ ω in ae P, ∀ i : Fin n, ∀ j : Fin n, N ω i j = M ω i j :=
      Filter.eventually_all.2 (fun i => Filter.eventually_all.2 (fun j => hNae i j))
    exact h1.mono (fun ω hω => funext fun i => funext fun j => hω i j)
  have hZ : P.real {ω | N ω ≠ M ω} = 0 := by
    have h0 : P {ω | ¬ (N ω = M ω)} = 0 := (MeasureTheory.ae_iff).mp hNae_all
    rw [show {ω : Ω | N ω ≠ M ω} = {ω | ¬ (N ω = M ω)} from by ext ω; simp [ne_eq]]
    simp [Measure.real, h0]
  have hle : P.real {ω | (N ω).det = 0} ≤ P.real {ω | (M ω).det = 0} :=
    calc P.real {ω | (N ω).det = 0}
        ≤ P.real ({ω | (M ω).det = 0} ∪ {ω | N ω ≠ M ω}) :=
          measureReal_mono (by
            intro ω hω
            by_cases h : N ω = M ω
            · left
              simp only [Set.mem_ofPred_eq] at hω ⊢
              rwa [h] at hω
            · right; exact h) (measure_ne_top P _)
      _ ≤ P.real {ω | (M ω).det = 0} + P.real {ω | N ω ≠ M ω} := measureReal_union_le _ _
      _ = P.real {ω | (M ω).det = 0} := by rw [hZ, add_zero]
  exact hmain.trans hle

end Commons.Probability.Bernoulli