/-
  Work.WilCrux.AsmDerivCont — continuity of the derivative of `famFun G` at the sheet (N4e).

  With the sheet `S := {y | parProj y ∈ Q6 ∧ ‖fibProj y‖ < r1}` and at the sheet point
  `Fin.append w₀ 0`, the two block derivatives

  * `parDerivMap G y = fderiv ℝ (fun w' => G w' (fibProj y)) (parProj y)` (parameter block),
  * `fibDerivMap G y = fderiv ℝ (G (parProj y)) (fibProj y)` (fibre block),

  are continuous, hence so is their pairing `pairCLM`.  The fibre block is handled with `hz`
  (uniform closeness of the slice derivative to its value at the sheet) and `hb` (continuity of
  `w ↦ fderiv ℝ (G w) 0`).  For the parameter block, off the sheet the chain rule identifies
  `parDerivMap G y (e_i)` with the parameter partial of `famFun G`, so `hw` applies; on the
  sheet (`fibProj y = 0`) the parameter derivative is literally the derivative of `a(w) = G w 0`,
  and `ha` gives its continuity.
-/
import Mathlib
import Submission.Work.WilCrux.C1AsmDefs
import Submission.Work.WilG4c.PuncturedAux.Basic

set_option autoImplicit false
open Classical
open scoped Topology
open Filter

namespace Work.WilCrux

set_option maxHeartbeats 4000000

/-! ## Auxiliary lemmas -/

/-- `famFun G` on a glued vector is `G` applied to the two blocks. -/
theorem famFun_append_eq {a b : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (w : Fin a → ℝ) (z : Fin b → ℝ) :
    Work.WilG4c.famFun G (Fin.append w z) = G w z := by
  simp only [Work.WilG4c.famFun, Fin.append_left, Fin.append_right]

/-- The chain rule in the parameter direction: off the sheet, the parameter partial of
`famFun G` is the derivative of the slice `w' ↦ G w' z`. -/
theorem fderiv_famFun_append_par {a b : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (w : Fin a → ℝ) (z : Fin b → ℝ) (h : Fin a → ℝ)
    (hd : DifferentiableAt ℝ (Work.WilG4c.famFun G) (Fin.append w z)) :
    fderiv ℝ (Work.WilG4c.famFun G) (Fin.append w z) (Fin.append h 0)
      = fderiv ℝ (fun w' : Fin a → ℝ => G w' z) w h := by
  have happa : HasFDerivAt (fun w' : Fin a → ℝ => Fin.append w' z) (parIncl a b) w := by
    have hfun : (fun w' : Fin a → ℝ => Fin.append w' z)
        = fun w' => parIncl a b w' + fibIncl a b z := by
      funext w'; rw [append_eq_parIncl_add_fibIncl]
    rw [hfun]
    exact (parIncl a b).hasFDerivAt.add_const _
  have hcomp := hd.hasFDerivAt.comp (x := w) happa
  have hfun : Work.WilG4c.famFun G ∘ (fun w' : Fin a → ℝ => Fin.append w' z)
      = fun w' => G w' z := funext fun w' => famFun_append_eq G w' z
  rw [hfun] at hcomp
  have hpar : fderiv ℝ (fun w' : Fin a → ℝ => G w' z) w
      = (fderiv ℝ (Work.WilG4c.famFun G) (Fin.append w z)).comp (parIncl a b) := hcomp.fderiv
  rw [hpar, ContinuousLinearMap.comp_apply, parIncl_eq]

/-- The parameter projection is `1`-Lipschitz. -/
theorem dist_parProj_le {a b : ℕ} (u v : Fin (a+b) → ℝ) :
    dist (parProj a b u) (parProj a b v) ≤ dist u v := by
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  exact norm_parProj_le a b (u - v)

/-- The fibre projection is `1`-Lipschitz. -/
theorem dist_fibProj_le {a b : ℕ} (u v : Fin (a+b) → ℝ) :
    dist (fibProj a b u) (fibProj a b v) ≤ dist u v := by
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  exact norm_fibProj_le a b (u - v)

/-- The standard basis vector `e_i` has norm at most `1`. -/
theorem norm_single_le_one {a : ℕ} (i : Fin a) :
    ‖(Pi.single i (1:ℝ) : Fin a → ℝ)‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro j
  simp only [Pi.single_apply]
  split_ifs with h <;> simp

/-! ## The two block derivatives -/

/-- The parameter-block derivative of `famFun G` at `y`. -/
noncomputable def parDerivMap {a b : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) :
    (Fin (a+b) → ℝ) → (Fin a → ℝ) →L[ℝ] ℝ :=
  fun y => fderiv ℝ (fun w' : Fin a → ℝ => G w' (fibProj a b y)) (parProj a b y)

/-- The fibre-block derivative of `famFun G` at `y`. -/
noncomputable def fibDerivMap {a b : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) :
    (Fin (a+b) → ℝ) → (Fin b → ℝ) →L[ℝ] ℝ :=
  fun y => fderiv ℝ (G (parProj a b y)) (fibProj a b y)

/-- The sheet over `Q6` with fibre radius `r1`. -/
def sheetSet {a b : ℕ} (Q6 : Set (Fin a → ℝ)) (r1 : ℝ) : Set (Fin (a+b) → ℝ) :=
  {y | parProj a b y ∈ Q6 ∧ ‖fibProj a b y‖ < r1}

/-! ## Continuity of the fibre block -/

theorem fibDerivMap_continuousWithinAt {a b : ℕ}
    (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (Q6 : Set (Fin a → ℝ)) (w₀ : Fin a → ℝ) (hw₀ : w₀ ∈ Q6) (r1 : ℝ)
    (hz : ∀ w₀ ∈ Q6, ∀ ε > 0, ∃ η > 0, ∀ (w : Fin a → ℝ) (z : Fin b → ℝ),
      dist w w₀ < η → z ≠ 0 → ‖z‖ < η → ‖fderiv ℝ (G w) z - fderiv ℝ (G w) 0‖ < ε)
    (hb : ∀ w ∈ Q6, ContinuousWithinAt (fun w' => fderiv ℝ (G w') 0) Q6 w) :
    ContinuousWithinAt (fibDerivMap G) (sheetSet Q6 r1) (Fin.append w₀ 0) := by
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨η1, hη1, hη1'⟩ := hz w₀ hw₀ (ε/2) hε2
  obtain ⟨η2, hη2, hη2'⟩ := (Metric.continuousWithinAt_iff.mp (hb w₀ hw₀)) (ε/2) hε2
  refine ⟨min η1 η2, lt_min hη1 hη2, ?_⟩
  intro y hy hdy
  rw [dist_eq_norm]
  simp only [fibDerivMap, parProj_append, fibProj_append]
  have hdy' : dist y (Fin.append w₀ 0) < min η1 η2 := hdy
  have hdw1 : dist (parProj a b y) w₀ < η1 := by
    have h := dist_parProj_le y (Fin.append w₀ 0)
    rw [parProj_append] at h
    exact lt_of_le_of_lt h (lt_of_lt_of_le hdy' (min_le_left _ _))
  have hdw2 : dist (parProj a b y) w₀ < η2 := by
    have h := dist_parProj_le y (Fin.append w₀ 0)
    rw [parProj_append] at h
    exact lt_of_le_of_lt h (lt_of_lt_of_le hdy' (min_le_right _ _))
  have hdz1 : ‖fibProj a b y‖ < η1 := by
    have h : ‖fibProj a b y‖ ≤ dist y (Fin.append w₀ 0) := by
      simpa only [fibProj_append, dist_zero_right] using dist_fibProj_le y (Fin.append w₀ 0)
    exact lt_of_le_of_lt h (lt_of_lt_of_le hdy' (min_le_left _ _))
  have hterm : ‖fderiv ℝ (G (parProj a b y)) (fibProj a b y)
      - fderiv ℝ (G (parProj a b y)) 0‖ < ε/2 := by
    rcases eq_or_ne (fibProj a b y) 0 with h0 | h0
    · rw [h0, sub_self, norm_zero]; exact hε2
    · exact hη1' (parProj a b y) (fibProj a b y) hdw1 h0 hdz1
  have hterm2 : ‖fderiv ℝ (G (parProj a b y)) 0 - fderiv ℝ (G w₀) 0‖ < ε/2 := by
    simpa only [dist_eq_norm] using hη2' hy.1 hdw2
  calc ‖fderiv ℝ (G (parProj a b y)) (fibProj a b y) - fderiv ℝ (G w₀) 0‖
      = ‖(fderiv ℝ (G (parProj a b y)) (fibProj a b y) - fderiv ℝ (G (parProj a b y)) 0)
        + (fderiv ℝ (G (parProj a b y)) 0 - fderiv ℝ (G w₀) 0)‖ := by
          rw [sub_add_sub_cancel]
    _ ≤ ‖fderiv ℝ (G (parProj a b y)) (fibProj a b y) - fderiv ℝ (G (parProj a b y)) 0‖
        + ‖fderiv ℝ (G (parProj a b y)) 0 - fderiv ℝ (G w₀) 0‖ := norm_add_le _ _
    _ < ε := by linarith

/-! ## Continuity of the parameter block -/

theorem parDerivMap_continuousWithinAt {a b : ℕ}
    (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (Q6 : Set (Fin a → ℝ)) (hQ6 : IsOpen Q6) (w₀ : Fin a → ℝ) (hw₀ : w₀ ∈ Q6)
    (r0 r1 : ℝ) (_hr0 : 0 < r0) (_hr1 : 0 < r1) (hr1r0 : r1 ≤ r0)
    (hoff : ∀ w ∈ Q6, ∀ z : Fin b → ℝ, z ≠ 0 → ‖z‖ < r0 →
      ContDiffAt ℝ 1 (Work.WilG4c.famFun G) (Fin.append w z))
    (ha : ContDiffOn ℝ 1 (fun w => G w 0) Q6)
    (hw : ∀ i : Fin a, Filter.Tendsto
      (fun p : (Fin a → ℝ) × (Fin b → ℝ) =>
        fderiv ℝ (Work.WilG4c.famFun G) (Fin.append p.1 p.2) (Fin.append (Pi.single i 1) 0)
          - fderiv ℝ (fun w' => G w' 0) p.1 (Pi.single i 1))
      (nhdsWithin (w₀, 0) {p : (Fin a → ℝ) × (Fin b → ℝ) | p.2 ≠ 0}) (nhds 0)) :
    ContinuousWithinAt (parDerivMap G) (sheetSet Q6 r1) (Fin.append w₀ 0) := by
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  by_cases ha0 : a = 0
  · refine ⟨1, one_pos, fun y hy hdy => ?_⟩
    rw [dist_eq_norm]
    have hle := Work.WilG4c.PuncturedAux.NormSubLeSumSingle (parDerivMap G y)
      (parDerivMap G (Fin.append w₀ 0))
    have hzero : (∑ i : Fin a,
        ‖(parDerivMap G y - parDerivMap G (Fin.append w₀ 0)) (Pi.single i 1)‖) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact absurd i.isLt (by omega)
    rw [hzero] at hle
    linarith [norm_nonneg (parDerivMap G y - parDerivMap G (Fin.append w₀ 0))]
  · have ha_pos : (0:ℝ) < (a:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero ha0
    set t : ℝ := ε / (2 * ((a:ℝ) + 1)) with htdef
    have ht : 0 < t := by rw [htdef]; exact div_pos hε (by positivity)
    have hha : ∃ η > 0, ∀ w ∈ Q6, dist w w₀ < η →
        ‖fderiv ℝ (fun w' : Fin a → ℝ => G w' 0) w
          - fderiv ℝ (fun w' : Fin a → ℝ => G w' 0) w₀‖ < t := by
      have hcont : ContinuousWithinAt (fderiv ℝ (fun w => G w 0)) Q6 w₀ :=
        (ha.continuousOn_fderiv_of_isOpen hQ6 (le_refl 1)).continuousWithinAt hw₀
      obtain ⟨η, hη, hη'⟩ := (Metric.continuousWithinAt_iff.mp hcont) t ht
      exact ⟨η, hη, fun w hw hd => by simpa only [dist_eq_norm] using hη' hw hd⟩
    have hhw : ∃ η > 0, ∀ p : (Fin a → ℝ) × (Fin b → ℝ), dist p (w₀, 0) < η → p.2 ≠ 0 →
        ∀ i : Fin a, ‖fderiv ℝ (Work.WilG4c.famFun G) (Fin.append p.1 p.2)
            (Fin.append (Pi.single i 1) 0)
          - fderiv ℝ (fun w' : Fin a → ℝ => G w' 0) p.1 (Pi.single i 1)‖ < t := by
      have h : ∀ᶠ p in nhdsWithin (w₀, 0) {p : (Fin a → ℝ) × (Fin b → ℝ) | p.2 ≠ 0},
          ∀ i : Fin a, ‖fderiv ℝ (Work.WilG4c.famFun G) (Fin.append p.1 p.2)
              (Fin.append (Pi.single i 1) 0)
            - fderiv ℝ (fun w' : Fin a → ℝ => G w' 0) p.1 (Pi.single i 1)‖ < t := by
        rw [Filter.eventually_all]
        intro i
        have := (Metric.tendsto_nhds.mp (hw i)) t ht
        simpa only [dist_zero_right] using this
      rw [Filter.eventually_iff, Metric.mem_nhdsWithin_iff] at h
      obtain ⟨η, hη, hsub⟩ := h
      exact ⟨η, hη, fun p hp hpz => hsub ⟨hp, hpz⟩⟩
    obtain ⟨η1, hη1, hη1'⟩ := hhw
    obtain ⟨η2, hη2, hη2'⟩ := hha
    refine ⟨min η1 η2, lt_min hη1 hη2, ?_⟩
    intro y hy hdy
    rw [dist_eq_norm]
    have hdw1 : dist (parProj a b y) w₀ < η1 := by
      have h := dist_parProj_le y (Fin.append w₀ 0)
      rw [parProj_append] at h
      exact lt_of_le_of_lt h (lt_of_lt_of_le hdy (min_le_left _ _))
    have hdw2 : dist (parProj a b y) w₀ < η2 := by
      have h := dist_parProj_le y (Fin.append w₀ 0)
      rw [parProj_append] at h
      exact lt_of_le_of_lt h (lt_of_lt_of_le hdy (min_le_right _ _))
    have hdz1 : dist (fibProj a b y) 0 < η1 := by
      have h : dist (fibProj a b y) 0 ≤ dist y (Fin.append w₀ 0) := by
        simpa only [fibProj_append] using dist_fibProj_le y (Fin.append w₀ 0)
      exact lt_of_le_of_lt h (lt_of_lt_of_le hdy (min_le_left _ _))
    have hcoord : ∀ i : Fin a,
        ‖(parDerivMap G y - parDerivMap G (Fin.append w₀ 0)) (Pi.single i 1)‖ < 2 * t := by
      intro i
      have hAy0 : parDerivMap G (Fin.append w₀ 0) (Pi.single i 1)
          = fderiv ℝ (fun w' : Fin a → ℝ => G w' 0) w₀ (Pi.single i 1) := by
        simp only [parDerivMap, parProj_append, fibProj_append]
      have hsplit : (parDerivMap G y - parDerivMap G (Fin.append w₀ 0)) (Pi.single i 1)
          = (parDerivMap G y (Pi.single i 1)
              - fderiv ℝ (fun w' : Fin a → ℝ => G w' 0) (parProj a b y) (Pi.single i 1))
            + (fderiv ℝ (fun w' : Fin a → ℝ => G w' 0) (parProj a b y) (Pi.single i 1)
              - fderiv ℝ (fun w' : Fin a → ℝ => G w' 0) w₀ (Pi.single i 1)) := by
        rw [sub_apply, hAy0]; ring
      have hb1 : ‖parDerivMap G y (Pi.single i 1)
            - fderiv ℝ (fun w' : Fin a → ℝ => G w' 0) (parProj a b y) (Pi.single i 1)‖ < t := by
        rcases eq_or_ne (fibProj a b y) 0 with hz0 | hz0
        · have heq : parDerivMap G y (Pi.single i 1)
              = fderiv ℝ (fun w' : Fin a → ℝ => G w' 0) (parProj a b y) (Pi.single i 1) := by
            simp only [parDerivMap, hz0]
          rw [heq, sub_self, norm_zero]; exact ht
        · have hchain : parDerivMap G y (Pi.single i 1)
              = fderiv ℝ (Work.WilG4c.famFun G)
                  (Fin.append (parProj a b y) (fibProj a b y)) (Fin.append (Pi.single i 1) 0) := by
            have hd : DifferentiableAt ℝ (Work.WilG4c.famFun G)
                (Fin.append (parProj a b y) (fibProj a b y)) :=
              (hoff (parProj a b y) hy.1 (fibProj a b y) hz0 (lt_of_lt_of_le hy.2 hr1r0)).differentiableAt
                (by norm_num)
            exact (fderiv_famFun_append_par G (parProj a b y) (fibProj a b y) (Pi.single i 1) hd).symm
          rw [hchain]
          have hp : dist (parProj a b y, fibProj a b y) (w₀, 0) < η1 := by
            rw [Prod.dist_eq]
            exact max_lt hdw1 hdz1
          exact hη1' (parProj a b y, fibProj a b y) hp hz0 i
      have hb2 : ‖fderiv ℝ (fun w' : Fin a → ℝ => G w' 0) (parProj a b y) (Pi.single i 1)
            - fderiv ℝ (fun w' : Fin a → ℝ => G w' 0) w₀ (Pi.single i 1)‖ < t := by
        have hA := hη2' (parProj a b y) hy.1 hdw2
        rw [← sub_apply]
        calc ‖(fderiv ℝ (fun w' : Fin a → ℝ => G w' 0) (parProj a b y)
                - fderiv ℝ (fun w' : Fin a → ℝ => G w' 0) w₀) (Pi.single i 1)‖
            ≤ ‖fderiv ℝ (fun w' : Fin a → ℝ => G w' 0) (parProj a b y)
                - fderiv ℝ (fun w' : Fin a → ℝ => G w' 0) w₀‖ * ‖(Pi.single i 1 : Fin a → ℝ)‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ ‖fderiv ℝ (fun w' : Fin a → ℝ => G w' 0) (parProj a b y)
                - fderiv ℝ (fun w' : Fin a → ℝ => G w' 0) w₀‖ * 1 :=
              mul_le_mul_of_nonneg_left (norm_single_le_one i) (norm_nonneg _)
          _ = ‖fderiv ℝ (fun w' : Fin a → ℝ => G w' 0) (parProj a b y)
                - fderiv ℝ (fun w' : Fin a → ℝ => G w' 0) w₀‖ := mul_one _
          _ < t := hA
      rw [hsplit]
      calc ‖(parDerivMap G y (Pi.single i 1)
              - fderiv ℝ (fun w' : Fin a → ℝ => G w' 0) (parProj a b y) (Pi.single i 1))
            + (fderiv ℝ (fun w' : Fin a → ℝ => G w' 0) (parProj a b y) (Pi.single i 1)
              - fderiv ℝ (fun w' : Fin a → ℝ => G w' 0) w₀ (Pi.single i 1))‖
          ≤ ‖parDerivMap G y (Pi.single i 1)
              - fderiv ℝ (fun w' : Fin a → ℝ => G w' 0) (parProj a b y) (Pi.single i 1)‖
            + ‖fderiv ℝ (fun w' : Fin a → ℝ => G w' 0) (parProj a b y) (Pi.single i 1)
              - fderiv ℝ (fun w' : Fin a → ℝ => G w' 0) w₀ (Pi.single i 1)‖ := norm_add_le _ _
        _ < 2 * t := by linarith
    have hle := Work.WilG4c.PuncturedAux.NormSubLeSumSingle (parDerivMap G y)
      (parDerivMap G (Fin.append w₀ 0))
    have hsum2 : (∑ i : Fin a,
        ‖(parDerivMap G y - parDerivMap G (Fin.append w₀ 0)) (Pi.single i 1)‖) ≤ (a:ℝ) * (2*t) := by
      calc (∑ i : Fin a, ‖(parDerivMap G y - parDerivMap G (Fin.append w₀ 0)) (Pi.single i 1)‖)
          ≤ ∑ _i : Fin a, (2*t) := Finset.sum_le_sum (fun i _ => le_of_lt (hcoord i))
        _ = (a:ℝ) * (2*t) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hbound : (a:ℝ) * (2*t) < ε := by
      have h2t : 2 * t = ε / ((a:ℝ) + 1) := by
        rw [htdef]; field_simp
      rw [h2t]
      have hden : (0:ℝ) < (a:ℝ) + 1 := by positivity
      have hfrac : (a:ℝ) / ((a:ℝ) + 1) < 1 := by
        rw [div_lt_one hden]; linarith
      calc (a:ℝ) * (ε / ((a:ℝ) + 1)) = ((a:ℝ) / ((a:ℝ) + 1)) * ε := by ring
        _ < 1 * ε := mul_lt_mul_of_pos_right hfrac hε
        _ = ε := one_mul ε
    linarith

/-! ## The assembly -/

set_option maxHeartbeats 4000000 in
theorem continuous_pairCLM {a b : ℕ} :
    Continuous (fun p : ((Fin a → ℝ) →L[ℝ] ℝ) × ((Fin b → ℝ) →L[ℝ] ℝ) => pairCLM a b p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨ε/2, by linarith, ?_⟩
  intro q hq
  rw [dist_eq_norm, pairCLM_sub]
  have hd1 : ‖q.1 - p.1‖ ≤ dist q p := by
    rw [dist_eq_norm]; exact norm_fst_le (q - p)
  have hd2 : ‖q.2 - p.2‖ ≤ dist q p := by
    rw [dist_eq_norm]; exact norm_snd_le (q - p)
  calc ‖pairCLM a b (q.1 - p.1) (q.2 - p.2)‖ ≤ ‖q.1 - p.1‖ + ‖q.2 - p.2‖ :=
        norm_pairCLM_le a b _ _
    _ ≤ dist q p + dist q p := add_le_add hd1 hd2
    _ < ε := by linarith

set_option maxHeartbeats 4000000 in
theorem continuousWithinAt_pairCLM {a b : ℕ} {α : Type*} [TopologicalSpace α]
    {u : α → (Fin a → ℝ) →L[ℝ] ℝ} {v : α → (Fin b → ℝ) →L[ℝ] ℝ} {s : Set α} {x : α}
    (hu : ContinuousWithinAt u s x) (hv : ContinuousWithinAt v s x) :
    ContinuousWithinAt (fun y => pairCLM a b (u y) (v y)) s x := by
  have h1 : Filter.Tendsto (fun y => (u y, v y)) (nhdsWithin x s) (nhds (u x, v x)) := by
    rw [nhds_prod_eq]
    exact hu.tendsto.prodMk hv.tendsto
  have h2 : Filter.Tendsto (fun p : ((Fin a → ℝ) →L[ℝ] ℝ) × ((Fin b → ℝ) →L[ℝ] ℝ) =>
      pairCLM a b p.1 p.2) (nhds (u x, v x)) (nhds (pairCLM a b (u x) (v x))) :=
    (continuous_pairCLM (a := a) (b := b)).tendsto _
  exact h2.comp h1

/-! ## The target -/

theorem AsmDerivCont {a b : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (Q6 : Set (Fin a → ℝ)) (hQ6 : IsOpen Q6) (w₀ : Fin a → ℝ) (hw₀ : w₀ ∈ Q6)
    (r0 r1 : ℝ) (hr0 : 0 < r0) (hr1 : 0 < r1) (hr1r0 : r1 ≤ r0)
    (hoff : ∀ w ∈ Q6, ∀ z : Fin b → ℝ, z ≠ 0 → ‖z‖ < r0 →
      ContDiffAt ℝ 1 (Work.WilG4c.famFun G) (Fin.append w z))
    (ha : ContDiffOn ℝ 1 (fun w => G w 0) Q6)
    (hz : ∀ w₀ ∈ Q6, ∀ ε > 0, ∃ η > 0, ∀ (w : Fin a → ℝ) (z : Fin b → ℝ),
      dist w w₀ < η → z ≠ 0 → ‖z‖ < η → ‖fderiv ℝ (G w) z - fderiv ℝ (G w) 0‖ < ε)
    (hw : ∀ i : Fin a, Filter.Tendsto
      (fun p : (Fin a → ℝ) × (Fin b → ℝ) =>
        fderiv ℝ (Work.WilG4c.famFun G) (Fin.append p.1 p.2) (Fin.append (Pi.single i 1) 0)
          - fderiv ℝ (fun w' => G w' 0) p.1 (Pi.single i 1))
      (nhdsWithin (w₀, 0) {p : (Fin a → ℝ) × (Fin b → ℝ) | p.2 ≠ 0}) (nhds 0))
    (hb : ∀ w ∈ Q6, ContinuousWithinAt (fun w' => fderiv ℝ (G w') 0) Q6 w) :
    ContinuousWithinAt (fun y : Fin (a + b) → ℝ =>
        pairCLM a b
          (fderiv ℝ (fun w' : Fin a → ℝ => G w' (fibProj a b y)) (parProj a b y))
          (fderiv ℝ (G (parProj a b y)) (fibProj a b y)))
      {y : Fin (a + b) → ℝ | parProj a b y ∈ Q6 ∧ ‖fibProj a b y‖ < r1}
      (Fin.append w₀ 0) := by
  show ContinuousWithinAt (fun y => pairCLM a b (parDerivMap G y) (fibDerivMap G y))
    (sheetSet Q6 r1) (Fin.append w₀ 0)
  exact continuousWithinAt_pairCLM
    (parDerivMap_continuousWithinAt G Q6 hQ6 w₀ hw₀ r0 r1 hr0 hr1 hr1r0 hoff ha hw)
    (fibDerivMap_continuousWithinAt G Q6 w₀ hw₀ r1 hz hb)

end Work.WilCrux
