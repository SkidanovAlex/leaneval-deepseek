import Mathlib
import Submission.Work.EKLComp.ErgMax.Basic
import Submission.Work.EKLComp.ErgMax.Face
import Submission.Work.EKLComp.ErgMax.avg_prob
import Submission.Work.EKLComp.ErgMax.avg_a0
import Submission.Work.EKLComp.ErgMax.ent_avg
import Submission.Work.EKLComp.ErgMax.isCompactProb_massDrho
import Submission.Work.EKLComp.ErgMax.isClosedProb_isAInvariant
import Submission.Work.EKLComp.ErgMax.exists_split_ae_invariant
import Submission.Work.EKLComp.ErgMax.avg_shift_integral
import Submission.Work.EKLComp.ErgMax.ent_avg_clause
import Submission.Work.EKLComp.ErgMax.P_X3_assembly
import Submission.Work.EKLComp.ent_conj
import Submission.Work.EKLComp.ent_affine
import Submission.Work.EKLComp.ErgMax.USC

/-!
# C4c — the ergodic maximiser (Bauer / Krein–Milman)

Assembly of `Work.EKLContract.P_ErgodicMax` (component C4c of the frozen EKL contract).
-/

open MeasureTheory Topology Filter
open scoped ENNReal BoundedContinuousFunction

namespace Work.EKLComp

open Work.EKLContract
open Work.EKLComp.ErgMax

noncomputable section

/-! ## `aDiag t = aPlus r s`: centring a general diagonal element -/

theorem aDiag_const_add (t : Fin 3 → ℝ) (c : ℝ) :
    aDiag (t + fun _ : Fin 3 => c) = aDiag t := by
  apply ext_toMat
  rw [toMat_aDiag, toMat_aDiag]
  congr 1
  funext i
  rw [Real.exp_eq_exp]
  simp only [Pi.add_apply]
  have hsum : (∑ j : Fin 3, (t j + c)) = (∑ j : Fin 3, t j) + 3 * c := by
    simp only [Fin.sum_univ_three]
    ring
  rw [hsum]
  ring

theorem aDiag_eq_aPlus (t : Fin 3 → ℝ) :
    aDiag t = aPlus (t 1 - (∑ j : Fin 3, t j) / 3) (t 2 - (∑ j : Fin 3, t j) / 3) := by
  have hconst : aDiag (t + fun _ : Fin 3 => -((∑ j : Fin 3, t j) / 3)) = aDiag t :=
    aDiag_const_add t _
  rw [← hconst, aPlus]
  congr 1
  funext i
  fin_cases i <;> simp [Fin.sum_univ_three] <;> ring

/-- `a0v = ![-2,1,1]` is non-constant, so `aDiag a0v ≠ 1`. -/
theorem a0v_ne : ∃ i j : Fin 3, a0v i ≠ a0v j := by
  refine ⟨0, 1, ?_⟩
  norm_num [a0v, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-! ## Entropy at `a₀` -/

/-- Clause (1) of `P_USC`: uniform finiteness on measures carried by `Drho ρ`. -/
theorem exists_ent_a0_bound (h2 : P_X3) (h4b : P_USC') {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ μ : Measure X3, IsProbabilityMeasure μ → μ (Drho ρ) = 1 →
      MeasurePreserving (act a0) μ μ → ent μ (fun x : X3 => aDiag a0v • x) ≤ C :=
  (h4b a0v a0v_ne (Drho ρ) (isCompact_Drho h2 hρ) (fun x hx => a0_maps_Drho hx)).1

/-- Clause (2) of `P_USC` in the `Efun` form needed for the maximal-entropy argument. -/
theorem Efun_limsup_le (h4b : P_USC') {ρ : ℝ} (hKcomp : IsCompact (Drho ρ)) {C : ℝ≥0∞}
    (hCtop : C < ⊤)
    (hT : ∀ μ : Measure X3, IsProbabilityMeasure μ → μ (Drho ρ) = 1 →
      MeasurePreserving (act a0) μ μ → ent μ (fun x : X3 => aDiag a0v • x) ≤ C)
    {νseq : ℕ → Measure X3} {νlim : Measure X3} (hprob : ∀ n, IsProbabilityMeasure (νseq n))
    (hlimprob : IsProbabilityMeasure νlim) (hK : ∀ n, νseq n (Drho ρ) = 1)
    (hmp : ∀ n, MeasurePreserving (act a0) (νseq n) (νseq n))
    (hconv : ∀ f : X3 →ᵇ ℝ,
      Tendsto (fun n => ∫ x, f x ∂(νseq n)) atTop (𝓝 (∫ x, f x ∂νlim)))
    (hKlim : νlim (Drho ρ) = 1) (hmplim : MeasurePreserving (act a0) νlim νlim) :
    Filter.limsup (fun n => Efun (νseq n)) Filter.atTop ≤ Efun νlim := by
  have husc := (h4b a0v a0v_ne (Drho ρ) hKcomp (fun x hx => a0_maps_Drho hx)).2 νseq νlim hprob
    hlimprob hK hmp hconv
  have hfin : ∀ᶠ n in Filter.atTop, ent (νseq n) (fun x : X3 => aDiag a0v • x) ≠ ⊤ :=
    Filter.Eventually.of_forall fun n =>
      ne_top_of_le_ne_top hCtop.ne (hT _ (hprob n) (hK n) (hmp n))
  have hbdd : IsBoundedUnder (· ≤ ·) (Filter.atTop : Filter ℕ)
      (fun n => (ent (νseq n) (fun x : X3 => aDiag a0v • x)).toReal) := by
    exact ⟨C.toReal, Filter.mem_map.2 (Filter.Eventually.of_forall fun n =>
      ENNReal.toReal_mono hCtop.ne (hT _ (hprob n) (hK n) (hmp n)))⟩
  have hlimfin : ent νlim (fun x : X3 => aDiag a0v • x) ≠ ⊤ :=
    ne_top_of_le_ne_top hCtop.ne (hT _ hlimprob hKlim hmplim)
  calc Filter.limsup (fun n => Efun (νseq n)) Filter.atTop
      = (Filter.limsup (fun n => ent (νseq n) (fun x : X3 => aDiag a0v • x))
          Filter.atTop).toReal := by
        rw [ENNReal.toReal_limsup hfin hbdd]
        rfl
    _ ≤ (ent νlim (fun x : X3 => aDiag a0v • x)).toReal := ENNReal.toReal_mono hlimfin husc
    _ = Efun νlim := rfl

/-- Affinity of the entropy, in the real-valued form used for the maximal-entropy step. -/
theorem Efun_add (hE3 : E3c) {μ₁ μ₂ : Measure X3} [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] (hT1 : MeasurePreserving (act a0) μ₁ μ₁)
    (hT2 : MeasurePreserving (act a0) μ₂ μ₂)
    (hfin1 : ent μ₁ (act a0) ≠ ⊤) (hfin2 : ent μ₂ (act a0) ≠ ⊤)
    {a b : ℝ≥0∞} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    Efun (a • μ₁ + b • μ₂) = a.toReal * Efun μ₁ + b.toReal * Efun μ₂ := by
  have haf : a ≠ ⊤ := by
    intro h; rw [h, top_add] at hab; exact ENNReal.one_ne_top hab.symm
  have hbf : b ≠ ⊤ := by
    intro h; rw [h, add_top] at hab; exact ENNReal.one_ne_top hab.symm
  have h1a : 1 - a = b := ENNReal.sub_eq_of_eq_add haf (by rw [← hab, add_comm])
  have hale : a ≤ 1 := by rw [← hab]; exact le_add_right le_rfl
  have haff := hE3 μ₁ ‹IsProbabilityMeasure μ₁› μ₂ ‹IsProbabilityMeasure μ₂› (act a0) a hale
    (measurable_act a0) hT1 hT2
  have hmix : a • μ₁ + b • μ₂ = a • μ₁ + (1 - a) • μ₂ := by rw [h1a]
  rw [Efun, hmix, haff, h1a,
    ENNReal.toReal_add (ENNReal.mul_ne_top haf hfin1) (ENNReal.mul_ne_top hbf hfin2),
    ENNReal.toReal_mul, ENNReal.toReal_mul, Efun, Efun]

/-- The superlevel sets of `Efun` on `Mset ρ` are closed (upper semicontinuity). -/
theorem isClosedProb_Efun_ge (h2 : P_X3) (h4b : P_USC') {ρ : ℝ} (hρ : 0 < ρ) {c : ℝ} :
    IsClosedProb {μ : Measure X3 | IsProbabilityMeasure μ ∧ IsAInvariant μ ∧
      μ (Drho ρ) = 1 ∧ c ≤ Efun μ} := by
  haveI : T2Space X3 := h2.1
  haveI : PolishSpace X3 := h2.2.1
  haveI : HasOuterApproxClosed X3 := inferInstance
  haveI : T2Space (ProbabilityMeasure X3) := inferInstance
  haveI : SequentialSpace (ProbabilityMeasure X3) := inferInstance
  obtain ⟨C, hCtop, hC⟩ := exists_ent_a0_bound h2 h4b hρ
  rw [IsClosedProb, ← isSeqClosed_iff_isClosed]
  intro u x hu hux
  have hsc1 : IsSeqClosed {μ : ProbabilityMeasure X3 |
      (μ : Measure X3) ∈ {ν : Measure X3 | IsAInvariant ν}} :=
    isSeqClosed_iff_isClosed.2 (isClosedProb_isAInvariant h2)
  have hAinv : IsAInvariant (x : Measure X3) :=
    hsc1 (x := u) (p := x) (fun n => (hu n).2.1) hux
  have hsc2 : IsSeqClosed {μ : ProbabilityMeasure X3 |
      (μ : Measure X3) ∈ {ν : Measure X3 | ν (Drho ρ) = 1}} :=
    isSeqClosed_iff_isClosed.2 (isCompactProb_massDrho h2 hρ).isClosed
  have hmass : (x : Measure X3) (Drho ρ) = 1 :=
    hsc2 (x := u) (p := x) (fun n => (hu n).2.2.1) hux
  have hconv : ∀ f : X3 →ᵇ ℝ,
      Tendsto (fun n => ∫ y, f y ∂(u n : Measure X3)) atTop
        (𝓝 (∫ y, f y ∂(x : Measure X3))) :=
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hux
  have husc := Efun_limsup_le h4b (isCompact_Drho h2 hρ) hCtop hC (fun n => (u n).2) x.2
    (fun n => (hu n).2.2.1) (fun n => (hu n).2.1 a0v) hconv hmass (hAinv a0v)
  have hbddE : IsBoundedUnder (· ≤ ·) (Filter.atTop : Filter ℕ)
      (fun n => Efun (u n)) :=
    ⟨C.toReal, Filter.mem_map.2 (Filter.Eventually.of_forall fun n =>
      ENNReal.toReal_mono hCtop.ne (hC _ (hu n).1 (hu n).2.2.1 ((hu n).2.1 a0v)))⟩
  have h1 : c ≤ Filter.limsup (fun n => Efun (u n)) Filter.atTop := by
    refine le_limsup_of_le hbddE ?_
    intro b hb
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (Filter.mem_map.1 hb)
    exact le_trans ((hu N).2.2.2) (hN N le_rfl)
  exact ⟨x.2, hAinv, hmass, le_trans h1 husc⟩

/-! ## A basic real-analysis lemma for the maximal-entropy argument -/

theorem eq_of_le_of_affine {s x y a' b' : ℝ} (ha : 0 < a') (hb : 0 < b') (hab : a' + b' = 1)
    (hs : s = a' * x + b' * y) (hx : x ≤ s) (hy : y ≤ s) : x = s := by
  by_contra hne
  have hlt : x < s := lt_of_le_of_ne hx hne
  have h1 : a' * x < a' * s := by nlinarith
  have h2 : b' * y ≤ b' * s := by nlinarith
  have h3 : a' * x + b' * y < a' * s + b' * s := add_lt_add_of_lt_of_le h1 h2
  have h4 : a' * s + b' * s = s := by rw [← add_mul, hab, one_mul]
  linarith [hs, h3, h4]

/-! ## The `A`-invariant limit of the `A⁺`-averages -/

theorem exists_limit (h2 : P_X3) (h4b : P_USC') {ρ : ℝ} (hρ : 0 < ρ)
    (hshift : ∀ (ν : Measure X3) [IsProbabilityMeasure ν], ν (Drho ρ) = 1 →
      IsCompact (Drho ρ) → ∀ (f : X3 →ᵇ ℝ) (r s : ℝ), 0 ≤ r → 0 ≤ s →
      Tendsto (fun N : ℕ => |(∫ x, f x ∂(Measure.map (act (aPlus r s)) (avg ν N)))
        - (∫ x, f x ∂(avg ν N))|) atTop (𝓝 0))
    (hent : ∀ (ν : Measure X3) [IsProbabilityMeasure ν], MeasurePreserving (act a0) ν ν →
      ∀ N : ℕ, 1 ≤ N → ent (avg ν N) (act a0) = ent ν (act a0))
    {ν : Measure X3} [IsProbabilityMeasure ν] (hKν : ν (Drho ρ) = 1)
    (hmpν : MeasurePreserving (act a0) ν ν) :
    ∃ μ : Measure X3, μ ∈ Mset ρ ∧ ent ν (act a0) ≤ ent μ (act a0) := by
  haveI : T2Space X3 := h2.1
  haveI : PolishSpace X3 := h2.2.1
  haveI : HasOuterApproxClosed X3 := inferInstance
  haveI : T2Space (ProbabilityMeasure X3) := inferInstance
  haveI : FirstCountableTopology (ProbabilityMeasure X3) := inferInstance
  have hK : IsCompact (Drho ρ) := isCompact_Drho h2 hρ
  obtain ⟨C, hCtop, hC⟩ := exists_ent_a0_bound h2 h4b hρ
  let u : ℕ → ProbabilityMeasure X3 := fun N =>
    ⟨avg ν (N + 1), (avg_prob ν hKν (Nat.le_add_left 1 N)).1⟩
  have humem : ∀ N : ℕ, u N ∈ {μ : ProbabilityMeasure X3 |
      (μ : Measure X3) ∈ {ν' : Measure X3 | ν' (Drho ρ) = 1}} := fun N =>
    (avg_prob ν hKν (Nat.le_add_left 1 N)).2
  obtain ⟨μlim, hμlim, φ, hφmono, hφtend⟩ :=
    (isCompactProb_massDrho h2 hρ).tendsto_subseq (x := u) humem
  have hφ1 : Tendsto (fun k : ℕ => φ k + 1) atTop atTop := by
    refine tendsto_atTop.2 fun M => ?_
    filter_upwards [eventually_ge_atTop M] with k hk
    exact le_trans hk (le_trans (hφmono.id_le k) (Nat.le_succ _))
  have hsub : ∀ k : ℕ, ((u (φ k) : ProbabilityMeasure X3) : Measure X3) = avg ν (φ k + 1) :=
    fun k => rfl
  have hAinv_aPlus : ∀ r s : ℝ, 0 ≤ r → 0 ≤ s →
      MeasurePreserving (act (aPlus r s)) (μlim : Measure X3) (μlim : Measure X3) := by
    intro r s hr hs
    have key : ∀ f : X3 →ᵇ ℝ, ∫ x, f x ∂(Measure.map (act (aPlus r s)) (μlim : Measure X3))
        = ∫ x, f x ∂(μlim : Measure X3) := by
      intro f
      have hmap := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous (u ∘ φ) μlim
        hφtend (continuous_act (aPlus r s))
      have h1 : Tendsto (fun k : ℕ => ∫ x, f x ∂(Measure.map (act (aPlus r s))
          (avg ν (φ k + 1)))) atTop
          (𝓝 (∫ x, f x ∂(Measure.map (act (aPlus r s)) (μlim : Measure X3)))) := by
        have h := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hmap f
        simpa only [Function.comp_apply, hsub, ProbabilityMeasure.toMeasure_map] using h
      have h2 : Tendsto (fun k : ℕ => ∫ x, f x ∂(avg ν (φ k + 1))) atTop
          (𝓝 (∫ x, f x ∂(μlim : Measure X3))) := by
        have h := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hφtend f
        simpa only [Function.comp_apply, hsub] using h
      have h3 : Tendsto (fun k : ℕ => |(∫ x, f x ∂(Measure.map (act (aPlus r s))
          (avg ν (φ k + 1)))) - (∫ x, f x ∂(avg ν (φ k + 1)))|) atTop (𝓝 0) :=
        (hshift ν hKν hK f r s hr hs).comp hφ1
      have h4 : Tendsto (fun k : ℕ =>
          (∫ x, f x ∂(Measure.map (act (aPlus r s)) (avg ν (φ k + 1))))
            - (∫ x, f x ∂(avg ν (φ k + 1)))) atTop (𝓝 0) := by
        have h3' : Tendsto (fun k : ℕ => -|(∫ x, f x ∂(Measure.map (act (aPlus r s))
            (avg ν (φ k + 1)))) - (∫ x, f x ∂(avg ν (φ k + 1)))|) atTop (𝓝 0) := by
          simpa using h3.neg
        exact tendsto_of_tendsto_of_tendsto_of_le_of_le h3' h3
          (fun k => neg_abs_le _) (fun k => le_abs_self _)
      have h5 : (∫ x, f x ∂(Measure.map (act (aPlus r s)) (μlim : Measure X3)))
          - (∫ x, f x ∂(μlim : Measure X3)) = 0 :=
        tendsto_nhds_unique (h1.sub h2) h4
      linarith
    refine ⟨measurable_act (aPlus r s), ?_⟩
    exact MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure key
  have hmul : ∀ g h : SL3,
      MeasurePreserving (act g) (μlim : Measure X3) (μlim : Measure X3) →
      MeasurePreserving (act h) (μlim : Measure X3) (μlim : Measure X3) →
      MeasurePreserving (act (g * h)) (μlim : Measure X3) (μlim : Measure X3) := by
    intro g h hg hh
    refine ⟨measurable_act (g * h), ?_⟩
    rw [act_mul, ← Measure.map_map (measurable_act g) (measurable_act h), hh.map_eq, hg.map_eq]
  have hinv : ∀ g : SL3, MeasurePreserving (act g) (μlim : Measure X3) (μlim : Measure X3) →
      MeasurePreserving (act g⁻¹) (μlim : Measure X3) (μlim : Measure X3) := by
    intro g hg
    refine ⟨measurable_act g⁻¹, ?_⟩
    have h2 : Measure.map (act g⁻¹) (μlim : Measure X3)
        = Measure.map (act g⁻¹) (Measure.map (act g) (μlim : Measure X3)) := by
      rw [hg.map_eq]
    rw [h2, Measure.map_map (measurable_act g⁻¹) (measurable_act g), ← act_mul,
      inv_mul_cancel, act_one]
    simp
  have hgen : ∀ r s : ℝ, MeasurePreserving (act (aPlus r s)) (μlim : Measure X3)
      (μlim : Measure X3) := by
    intro r s
    have hdec : aPlus r s = aPlus (max r 0) (max s 0) * aPlus (min r 0) (min s 0) := by
      rw [aPlus_add]
      congr 1
      · rcases le_total (0:ℝ) r with h | h
        · rw [max_eq_left h, min_eq_right h, add_zero]
        · rw [max_eq_right h, min_eq_left h, zero_add]
      · rcases le_total (0:ℝ) s with h | h
        · rw [max_eq_left h, min_eq_right h, add_zero]
        · rw [max_eq_right h, min_eq_left h, zero_add]
    rw [hdec]
    refine hmul _ _ (hAinv_aPlus _ _ (le_max_right _ _) (le_max_right _ _)) ?_
    have hneg : aPlus (min r 0) (min s 0)
        = (aPlus (-(min r 0)) (-(min s 0)))⁻¹ := by
      have h1 : aPlus (-(min r 0)) (-(min s 0)) * aPlus (min r 0) (min s 0) = 1 := by
        have hr' : -(min r 0) + min r 0 = 0 := by
          rcases le_total (0:ℝ) r with h | h
          · rw [min_eq_right h]; ring
          · rw [min_eq_left h]; ring
        have hs' : -(min s 0) + min s 0 = 0 := by
          rcases le_total (0:ℝ) s with h | h
          · rw [min_eq_right h]; ring
          · rw [min_eq_left h]; ring
        rw [aPlus_add, hr', hs', aPlus_zero]
      exact eq_inv_of_mul_eq_one_right h1
    rw [hneg]
    exact hinv _ (hAinv_aPlus _ _ (by linarith [min_le_right r 0])
      (by linarith [min_le_right s 0]))
  have hAinv_all : IsAInvariant (μlim : Measure X3) := by
    intro t
    rw [aDiag_eq_aPlus]
    exact hgen _ _
  have hfun : (fun k : ℕ => Efun (((u ∘ φ) k) : Measure X3)) = fun _ : ℕ => Efun ν := by
    funext k
    simp only [Efun, Function.comp_apply, hsub]
    rw [hent ν hmpν (φ k + 1) (Nat.le_add_left 1 (φ k))]
  have hconstE : Filter.limsup (fun k : ℕ => Efun (((u ∘ φ) k) : Measure X3)) Filter.atTop
      = Efun ν := by
    rw [hfun, Filter.limsup_const]
  have husc := Efun_limsup_le h4b hK hCtop hC
    (νseq := fun k : ℕ => (((u ∘ φ) k) : Measure X3))
    (hprob := fun k => (((u ∘ φ) k)).2) (hlimprob := μlim.2)
    (hK := fun k => humem (φ k)) (hmp := fun k => avg_a0 ν (Nat.le_add_left 1 (φ k)) hmpν)
    (hconv := fun f => ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hφtend f)
    (hKlim := hμlim) (hmplim := hAinv_all a0v)
  have hentE : Efun ν ≤ Efun (μlim : Measure X3) := by
    rw [← hconstE]
    exact husc
  have hfinν : ent ν (act a0) ≠ ⊤ :=
    ne_top_of_le_ne_top hCtop.ne (hC _ ‹IsProbabilityMeasure ν› hKν hmpν)
  have hfinlim : ent (μlim : Measure X3) (act a0) ≠ ⊤ :=
    ne_top_of_le_ne_top hCtop.ne (hC _ μlim.2 hμlim (hAinv_all a0v))
  exact ⟨(μlim : Measure X3), ⟨μlim.2, hAinv_all, hμlim⟩,
    (ENNReal.toReal_le_toReal hfinν hfinlim).mp hentE⟩


/-! ## The maximal-entropy ergodic measure -/

theorem exists_ergodic_maximiser (h2 : P_X3) (hE3 : E3c) (h4b : P_USC') {ρ : ℝ}
    (hρ : 0 < ρ) (hpos : ∃ μ ∈ Mset ρ, 0 < ent μ (act a0)) :
    ∃ μ : Measure X3, IsProbabilityMeasure μ ∧ IsAErgodic μ ∧ μ (Drho ρ) = 1 ∧
      0 < ent μ (act a0) := by
  haveI : T2Space X3 := h2.1
  haveI : PolishSpace X3 := h2.2.1
  haveI : HasOuterApproxClosed X3 := inferInstance
  haveI : T2Space (ProbabilityMeasure X3) := inferInstance
  obtain ⟨C, hCtop, hC⟩ := exists_ent_a0_bound h2 h4b hρ
  have hMprob : ∀ μ ∈ Mset ρ, IsProbabilityMeasure μ := fun μ hμ => hμ.1
  obtain ⟨μ₀, hμ₀M, hμ₀pos⟩ := hpos
  have hMcomp : IsCompactProb (Mset ρ) := by
    have h1 : IsCompactProb ({μ : Measure X3 | μ (Drho ρ) = 1} ∩
        {μ : Measure X3 | IsAInvariant μ}) :=
      IsCompactProb.inter (isCompactProb_massDrho h2 hρ) (isClosedProb_isAInvariant h2)
    unfold IsCompactProb at h1 ⊢
    convert h1 using 2
    ext μ
    exact ⟨fun h => ⟨h.2.2, h.2.1⟩, fun h => ⟨μ.2, h.2, h.1⟩⟩
  have hEfun_bound : ∀ μ ∈ Mset ρ, Efun μ ≤ C.toReal := fun μ hμ =>
    ENNReal.toReal_mono hCtop.ne (hC _ hμ.1 hμ.2.2 (hμ.2.1 a0v))
  set s : ℝ := sSup (Efun '' Mset ρ) with hsdef
  set Ms : Set (Measure X3) := {μ ∈ Mset ρ | Efun μ = s} with hMsdef
  have hsne : (Efun '' Mset ρ).Nonempty := ⟨Efun μ₀, μ₀, hμ₀M, rfl⟩
  have hbdd : BddAbove (Efun '' Mset ρ) :=
    ⟨C.toReal, fun y ⟨μ, hμ, hy⟩ => hy ▸ hEfun_bound μ hμ⟩
  have hfin₀ : ent μ₀ (act a0) ≠ ⊤ :=
    ne_top_of_le_ne_top hCtop.ne (hC _ hμ₀M.1 hμ₀M.2.2 (hμ₀M.2.1 a0v))
  have hμ₀E : 0 < Efun μ₀ := ENNReal.toReal_pos hμ₀pos.ne' hfin₀
  have hs_pos : 0 < s := lt_of_lt_of_le hμ₀E (le_csSup hbdd ⟨μ₀, hμ₀M, rfl⟩)
  have hMsface : IsFace (Mset ρ) Ms := by
    refine ⟨fun μ hμ => hμ.1, ?_⟩
    intro μ₁ h₁ μ₂ h₂ a b ha hb hab hcomb
    obtain ⟨hcombM, hcombs⟩ := hcomb
    have hfin1 : ent μ₁ (act a0) ≠ ⊤ :=
      ne_top_of_le_ne_top hCtop.ne (hC _ h₁.1 h₁.2.2 (h₁.2.1 a0v))
    have hfin2 : ent μ₂ (act a0) ≠ ⊤ :=
      ne_top_of_le_ne_top hCtop.ne (hC _ h₂.1 h₂.2.2 (h₂.2.1 a0v))
    have haf : a ≠ ⊤ := by
      intro h; rw [h, top_add] at hab; exact ENNReal.one_ne_top hab.symm
    have hbf : b ≠ ⊤ := by
      intro h; rw [h, add_top] at hab; exact ENNReal.one_ne_top hab.symm
    have hsum : a.toReal + b.toReal = 1 := by
      rw [← ENNReal.toReal_add haf hbf, hab, ENNReal.toReal_one]
    haveI : IsProbabilityMeasure μ₁ := h₁.1
    haveI : IsProbabilityMeasure μ₂ := h₂.1
    have hlin := Efun_add hE3 (h₁.2.1 a0v) (h₂.2.1 a0v) hfin1 hfin2 ha hb hab
    have hs' : s = a.toReal * Efun μ₁ + b.toReal * Efun μ₂ := by rw [← hcombs, hlin]
    refine ⟨h₁, ?_⟩
    exact eq_of_le_of_affine (ENNReal.toReal_pos ha.ne' haf) (ENNReal.toReal_pos hb.ne' hbf)
      hsum hs' (le_csSup hbdd ⟨μ₁, h₁, rfl⟩) (le_csSup hbdd ⟨μ₂, h₂, rfl⟩)
  have hMscl : IsClosedProb Ms := by
    have h1 : Ms = {μ : Measure X3 | IsProbabilityMeasure μ ∧ IsAInvariant μ ∧
        μ (Drho ρ) = 1 ∧ s ≤ Efun μ} := by
      ext μ
      constructor
      · intro h
        exact ⟨h.1.1, h.1.2.1, h.1.2.2, le_of_eq h.2.symm⟩
      · intro h
        exact ⟨⟨h.1, h.2.1, h.2.2.1⟩,
          le_antisymm (le_csSup hbdd ⟨μ, ⟨h.1, h.2.1, h.2.2.1⟩, rfl⟩) h.2.2.2⟩
    rw [h1]
    exact isClosedProb_Efun_ge h2 h4b hρ
  have hMsne : Ms.Nonempty := by
    have hA : ∀ n : ℕ, ∃ μ ∈ Mset ρ, s - (1 / ((n : ℝ) + 1)) ≤ Efun μ := by
      intro n
      have hlt : s - (1 / ((n : ℝ) + 1)) < s := by
        have hpos' : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
        linarith
      obtain ⟨y, hy, hylt⟩ := (lt_csSup_iff hbdd hsne).1 hlt
      obtain ⟨μ, hμ, rfl⟩ := hy
      exact ⟨μ, hμ, le_of_lt hylt⟩
    have hnest : ∀ n : ℕ, s - (1 / ((n : ℝ) + 1)) ≤ s - (1 / (((n + 1 : ℕ) : ℝ) + 1)) := by
      intro n
      have h1 : (1 : ℝ) / (((n + 1 : ℕ) : ℝ) + 1) ≤ (1 : ℝ) / ((n : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        push_cast
        linarith
      linarith
    have hclA : ∀ n : ℕ, IsClosedProb {μ : Measure X3 | μ ∈ Mset ρ ∧
        s - (1 / ((n : ℝ) + 1)) ≤ Efun μ} := by
      intro n
      have h1 : {μ : Measure X3 | μ ∈ Mset ρ ∧ s - (1 / ((n : ℝ) + 1)) ≤ Efun μ}
          = {μ : Measure X3 | IsProbabilityMeasure μ ∧ IsAInvariant μ ∧
              μ (Drho ρ) = 1 ∧ s - (1 / ((n : ℝ) + 1)) ≤ Efun μ} := by
        ext μ
        exact ⟨fun h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩,
          fun h => ⟨⟨h.1, h.2.1, h.2.2.1⟩, h.2.2.2⟩⟩
      rw [h1]
      exact isClosedProb_Efun_ge h2 h4b hρ
    obtain ⟨μ, hμ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      (t := fun n : ℕ => {μ : ProbabilityMeasure X3 | (μ : Measure X3) ∈
        {ν : Measure X3 | ν ∈ Mset ρ ∧ s - (1 / ((n : ℝ) + 1)) ≤ Efun ν}})
      (htd := fun n => fun μ hμ => ⟨hμ.1, le_trans (hnest n) hμ.2⟩)
      (htn := fun n => by
        obtain ⟨ν, hνM, hνE⟩ := hA n
        exact ⟨⟨ν, hνM.1⟩, hνM, hνE⟩)
      (ht0 := IsCompactProb.of_isClosedProb_subset (hclA 0) (fun μ hμ => hμ.1) hMcomp)
      (htcl := fun n => hclA n)
    have hμn : ∀ n : ℕ, (μ : Measure X3) ∈ {ν : Measure X3 |
        ν ∈ Mset ρ ∧ s - (1 / ((n : ℝ) + 1)) ≤ Efun ν} := fun n => Set.mem_iInter.1 hμ n
    refine ⟨(μ : Measure X3), ⟨(hμn 0).1, le_antisymm ?_ ?_⟩⟩
    · exact le_csSup hbdd ⟨(μ : Measure X3), (hμn 0).1, rfl⟩
    · refine le_of_forall_pos_le_add fun ε hε => ?_
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
      linarith [(hμn n).2, hn]
  obtain ⟨F, hFne, hFsub, hFcl, hFface, hFmin⟩ :=
    exists_minimal_closed_face hMprob hMsne (fun μ hμ => hμ.1) hMscl hMsface hMcomp
  obtain ⟨μ, hFsingle, hext⟩ := exists_extreme_of_minimal_face h2 hMprob hFne
    (hFsub.trans (fun μ hμ => hμ.1)) hFcl hFface hMcomp hFmin
  have hμMs : μ ∈ Ms := hFsub (hFsingle.symm ▸ Set.mem_singleton_iff.2 rfl)
  have hμM : μ ∈ Mset ρ := hμMs.1
  have hμs : Efun μ = s := hμMs.2
  refine ⟨μ, hμM.1, ⟨hμM.2.1, ?_⟩, hμM.2.2, ?_⟩
  · intro E hE hinv
    by_contra hcontr
    rw [not_or] at hcontr
    obtain ⟨h0, h1⟩ := hcontr
    haveI : IsProbabilityMeasure μ := hμM.1
    obtain ⟨ν₁, ν₂, hν₁prob, hν₂prob, hν₁A, hν₂A, hν₁Ec, hν₂E, hν₁T, hν₂T, hν₁ne, hsplit⟩ :=
      exists_split_ae_invariant μ hμM.2.1 hE hinv h0 h1 ρ hμM.2.2
    have hfin1 : ent ν₁ (act a0) ≠ ⊤ :=
      ne_top_of_le_ne_top hCtop.ne (hC _ hν₁prob hν₁T (hν₁A a0v))
    have hfin2 : ent ν₂ (act a0) ≠ ⊤ :=
      ne_top_of_le_ne_top hCtop.ne (hC _ hν₂prob hν₂T (hν₂A a0v))
    have ha : 0 < μ E := pos_iff_ne_zero.2 h0
    have hb : 0 < μ Eᶜ := pos_iff_ne_zero.2 h1
    have hab : μ E + μ Eᶜ = 1 := by
      rw [measure_add_measure_compl hE, measure_univ]
    have hν₁M : ν₁ ∈ Mset ρ := ⟨hν₁prob, hν₁A, hν₁T⟩
    have hν₂M : ν₂ ∈ Mset ρ := ⟨hν₂prob, hν₂A, hν₂T⟩
    have haf : μ E ≠ ⊤ := by
      have hle : μ E ≤ 1 := by
        rw [← measure_univ (μ := μ)]; exact measure_mono (Set.subset_univ E)
      exact ne_of_lt (lt_of_le_of_lt hle ENNReal.one_lt_top)
    have hbf : μ Eᶜ ≠ ⊤ := by
      have hle : μ Eᶜ ≤ 1 := by
        rw [← measure_univ (μ := μ)]; exact measure_mono (Set.subset_univ Eᶜ)
      exact ne_of_lt (lt_of_le_of_lt hle ENNReal.one_lt_top)
    have hsum : (μ E).toReal + (μ Eᶜ).toReal = 1 := by
      rw [← ENNReal.toReal_add haf hbf, hab, ENNReal.toReal_one]
    haveI : IsProbabilityMeasure ν₁ := hν₁prob
    haveI : IsProbabilityMeasure ν₂ := hν₂prob
    have hlin := Efun_add hE3 (hν₁A a0v) (hν₂A a0v) hfin1 hfin2 ha hb hab
    have hs' : s = (μ E).toReal * Efun ν₁ + (μ Eᶜ).toReal * Efun ν₂ := by
      rw [← hμs, congrArg Efun hsplit, hlin]
    have hν₁s : Efun ν₁ = s :=
      eq_of_le_of_affine (ENNReal.toReal_pos ha.ne' haf) (ENNReal.toReal_pos hb.ne' hbf)
        hsum hs' (le_csSup hbdd ⟨ν₁, hν₁M, rfl⟩) (le_csSup hbdd ⟨ν₂, hν₂M, rfl⟩)
    have hmem : μ E • ν₁ + μ Eᶜ • ν₂ ∈ F := by
      rw [← hsplit]
      exact hFsingle.symm ▸ Set.mem_singleton_iff.2 rfl
    have hν₁F : ν₁ ∈ F := hFface.mem_of_smul_add ν₁ hν₁M ν₂ hν₂M (μ E) (μ Eᶜ) ha hb hab hmem
    exact hν₁ne (Set.mem_singleton_iff.1 (hFsingle ▸ hν₁F))
  · have hposE : 0 < Efun μ := by rw [hμs]; exact hs_pos
    have hne : ent μ (act a0) ≠ 0 := by
      intro h
      simp only [Efun] at hposE
      rw [h] at hposE
      simp at hposE
    exact pos_iff_ne_zero.2 hne

/-! ## Assembly -/

theorem ergodicMax_of (h2 : P_X3) (hE3 : E3c) (h4b : P_USC')
    (hshift : ∀ (ρ : ℝ) (ν : Measure X3) [IsProbabilityMeasure ν], ν (Drho ρ) = 1 →
      IsCompact (Drho ρ) → ∀ (f : X3 →ᵇ ℝ) (r s : ℝ), 0 ≤ r → 0 ≤ s →
      Tendsto (fun N : ℕ => |(∫ x, f x ∂(Measure.map (act (aPlus r s)) (avg ν N)))
        - (∫ x, f x ∂(avg ν N))|) atTop (𝓝 0))
    (hent : ∀ (ρ : ℝ) (ν : Measure X3) [IsProbabilityMeasure ν], MeasurePreserving (act a0) ν ν →
      ∀ N : ℕ, 1 ≤ N → ent (avg ν N) (act a0) = ent ν (act a0)) :
    P_ErgodicMax := by
  intro ρ hρ ν hprob hKν hmpν hpos
  obtain ⟨μ₀, hμ₀M, hμ₀ent⟩ := exists_limit h2 h4b hρ
    (fun ν' inst h1 hK f r s hr hs => hshift ρ ν' h1 hK f r s hr hs)
    (fun ν' inst hmp N hN => hent ρ ν' hmp N hN) hKν hmpν
  exact exists_ergodic_maximiser h2 hE3 h4b hρ ⟨μ₀, hμ₀M, lt_of_lt_of_le hpos hμ₀ent⟩

/-! ## The two entropy clauses from the C3 development -/

theorem E2c_of_ent_conj : E2c := by
  intro X mX μ hμ T φ ψ hT hφ hψ hmp hl hr hcomm
  haveI := hμ
  exact Work.EKLComp.ent_conj μ T φ ψ hT hφ hψ hmp hl hr hcomm

theorem E3c_of_ent_affine : E3c := by
  intro X mX μ hμ ν hν T c hc hT hmpμ hmpν
  haveI := hμ
  haveI := hν
  exact Work.EKLComp.ent_affine μ ν T c hc hT hmpμ hmpν

/-! ## Assembly of the frozen component `P_ErgodicMax` -/

theorem prove_ErgodicMax : Work.EKLContract.P_ErgodicMax :=
  ergodicMax_of P_X3_assembly E3c_of_ent_affine P_USC'_proof
    (fun ρ ν inst h1 hK f r s hr hs => by
      haveI := inst
      exact avg_shift_integral ν h1 hK f hr hs)
    (fun ρ ν inst hmp N hN => by
      haveI := inst
      exact ent_avg_clause E2c_of_ent_conj E3c_of_ent_affine ν hmp hN)

end

end Work.EKLComp
