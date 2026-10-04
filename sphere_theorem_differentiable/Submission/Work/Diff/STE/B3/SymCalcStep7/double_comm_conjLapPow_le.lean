import Mathlib
import Submission.Work.Diff.STE.B3.SymCalcStep7.mul_CSq_le
import Submission.Work.Diff.STE.B3.SymCalcStep7.flatCut_CSq_le
import Submission.Work.Diff.STE.B3.SymCalcStep6.conj_cut_comm_lapPow_le
import Submission.Work.Diff.STE.B3.SymCalcStep6.conjLapPow_mul_comm_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3.SymCalcStep7

open MeasureTheory BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Two elementary tools for the assembly -/

/-- `fourierCoeff` is linear over a four-term combination `p + q - r - t`. -/
lemma fourierCoeff_add_sub_four (p q r t : (ι → ℝ) → ℂ) (hp : Continuous p) (hq : Continuous q)
    (hr : Continuous r) (ht : Continuous t) (k : ι → ℤ) :
    Work.Diff.STE.fourierCoeff (fun x => p x + q x - r x - t x) k
      = Work.Diff.STE.fourierCoeff p k + Work.Diff.STE.fourierCoeff q k
        - Work.Diff.STE.fourierCoeff r k - Work.Diff.STE.fourierCoeff t k := by
  have h1 : (fun x : ι → ℝ => p x + q x - r x - t x)
      = (fun x : ι → ℝ => (p + q) x - (r + t) x) := by
    funext x; simp only [Pi.add_apply]; ring
  calc Work.Diff.STE.fourierCoeff (fun x => p x + q x - r x - t x) k
      = Work.Diff.STE.fourierCoeff (p + q) k - Work.Diff.STE.fourierCoeff (r + t) k := by
        rw [h1, Work.Diff.STE.flat.fourierCoeff_sub_of_continuous _ _ (hp.add hq) (hr.add ht) k]
    _ = (Work.Diff.STE.fourierCoeff p k + Work.Diff.STE.fourierCoeff q k)
          - (Work.Diff.STE.fourierCoeff r k + Work.Diff.STE.fourierCoeff t k) := by
        rw [Work.Diff.STE.B3.SymCalcStep1.fourierCoeff_add_of_continuous _ _ hp hq k,
          Work.Diff.STE.B3.SymCalcStep1.fourierCoeff_add_of_continuous _ _ hr ht k]
    _ = Work.Diff.STE.fourierCoeff p k + Work.Diff.STE.fourierCoeff q k
          - Work.Diff.STE.fourierCoeff r k - Work.Diff.STE.fourierCoeff t k := by ring

/-- `CSq` of a four-term combination of coefficient families. -/
lemma CSq_add_sub_four_le (s : ℕ) (p q r t : (ι → ℤ) → ℂ)
    (hp : Summable fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s * ‖p k‖ ^ 2)
    (hq : Summable fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s * ‖q k‖ ^ 2)
    (hr : Summable fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s * ‖r k‖ ^ 2)
    (ht : Summable fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s * ‖t k‖ ^ 2) :
    Work.Diff.STE.CSq s (fun k => p k + q k - r k - t k)
      ≤ 4 * (Work.Diff.STE.CSq s p + Work.Diff.STE.CSq s q
              + Work.Diff.STE.CSq s r + Work.Diff.STE.CSq s t) := by
  have hsum_aux : ∀ (a b : (ι → ℤ) → ℂ),
      Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s * ‖a k‖ ^ 2) →
      Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s * ‖b k‖ ^ 2) →
      Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s * ‖a k + b k‖ ^ 2) := by
    intro a b ha hb
    have hpt : ∀ k : ι → ℤ, (Work.Diff.STE.wt k) ^ s * ‖a k + b k‖ ^ 2
        ≤ 2 * ((Work.Diff.STE.wt k) ^ s * ‖a k‖ ^ 2 + (Work.Diff.STE.wt k) ^ s * ‖b k‖ ^ 2) := by
      intro k
      have h1 : ‖a k + b k‖ ^ 2 ≤ 2 * (‖a k‖ ^ 2 + ‖b k‖ ^ 2) := by
        have h3 : ‖a k + b k‖ ^ 2 ≤ (‖a k‖ + ‖b k‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
        nlinarith [sq_nonneg (‖a k‖ - ‖b k‖), norm_nonneg (a k), norm_nonneg (b k)]
      calc (Work.Diff.STE.wt k) ^ s * ‖a k + b k‖ ^ 2
          ≤ (Work.Diff.STE.wt k) ^ s * (2 * (‖a k‖ ^ 2 + ‖b k‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left h1 (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) s)
        _ = 2 * ((Work.Diff.STE.wt k) ^ s * ‖a k‖ ^ 2
              + (Work.Diff.STE.wt k) ^ s * ‖b k‖ ^ 2) := by ring
    exact Summable.of_nonneg_of_le
      (fun k => mul_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) s) (sq_nonneg _))
      hpt ((ha.add hb).mul_left 2)
  have hpq : Summable fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s * ‖p k + q k‖ ^ 2 :=
    hsum_aux p q hp hq
  have hrt : Summable fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s * ‖r k + t k‖ ^ 2 :=
    hsum_aux r t hr ht
  have hneg : Summable fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s * ‖-(r k + t k)‖ ^ 2 :=
    hrt.congr (fun k => by rw [norm_neg])
  have hcongr : Work.Diff.STE.CSq s (fun k => p k + q k - r k - t k)
      = Work.Diff.STE.CSq s (fun k => (p k + q k) + (-(r k + t k))) := by
    apply Work.Diff.STE.B3.SymCalcStep6.CSq_congr_norm
    intro k; congr 1; ring
  rw [hcongr]
  calc Work.Diff.STE.CSq s (fun k => (p k + q k) + (-(r k + t k)))
      ≤ 2 * (Work.Diff.STE.CSq s (fun k => p k + q k)
              + Work.Diff.STE.CSq s (fun k => -(r k + t k))) :=
        Work.Diff.STE.B3.SymCalcStep1.CSq_add_le s _ _ hpq hneg
    _ = 2 * (Work.Diff.STE.CSq s (fun k => p k + q k)
              + Work.Diff.STE.CSq s (fun k => r k + t k)) := by
        rw [Work.Diff.STE.B3.SymCalcStep6.CSq_congr_norm s
          (c := fun k => -(r k + t k)) (d := fun k => r k + t k) (fun k => by rw [norm_neg])]
    _ ≤ 2 * (2 * (Work.Diff.STE.CSq s p + Work.Diff.STE.CSq s q)
              + 2 * (Work.Diff.STE.CSq s r + Work.Diff.STE.CSq s t)) := by
        have h1 := Work.Diff.STE.B3.SymCalcStep1.CSq_add_le s p q hp hq
        have h2 := Work.Diff.STE.B3.SymCalcStep1.CSq_add_le s r t hr ht
        linarith
    _ = 4 * (Work.Diff.STE.CSq s p + Work.Diff.STE.CSq s q
              + Work.Diff.STE.CSq s r + Work.Diff.STE.CSq s t) := by ring

/-- The Friedrichs cutoff is `1`-Lipschitz for differences: subtracting two functions before or
after cutting costs nothing. -/
lemma flatCut_sub_CSQ_le (ρ : (ι → ℝ) → ℝ) (hρ : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1) (ε : ℝ) (s : ℕ)
    (u v : (ι → ℝ) → ℂ) (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hup : Work.Diff.STE.Periodic1 u)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hvp : Work.Diff.STE.Periodic1 v) :
    Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff
        (fun x => Work.Diff.STE.B3.SymCalc.flatCut ρ ε u x
          - Work.Diff.STE.B3.SymCalc.flatCut ρ ε v x))
      ≤ Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun x => u x - v x)) := by
  have hSUc : Continuous (Work.Diff.STE.B3.SymCalc.flatCut ρ ε u) :=
    (Work.Diff.STE.B3.SymCalcStep1.flatCut_contDiff ρ hρ ε hu hup).continuous
  have hSVc : Continuous (Work.Diff.STE.B3.SymCalc.flatCut ρ ε v) :=
    (Work.Diff.STE.B3.SymCalcStep1.flatCut_contDiff ρ hρ ε hv hvp).continuous
  have h1 : Work.Diff.STE.fourierCoeff
      (fun x => Work.Diff.STE.B3.SymCalc.flatCut ρ ε u x
        - Work.Diff.STE.B3.SymCalc.flatCut ρ ε v x)
      = Work.Diff.STE.trunc ρ ε
          (fun k => Work.Diff.STE.fourierCoeff u k - Work.Diff.STE.fourierCoeff v k) := by
    funext k
    rw [Work.Diff.STE.flat.fourierCoeff_sub_of_continuous _ _ hSUc hSVc k,
      Work.Diff.STE.B3.SymCalcStep1.fourierCoeff_flatCut ρ hρ ε hu hup k,
      Work.Diff.STE.B3.SymCalcStep1.fourierCoeff_flatCut ρ hρ ε hv hvp k]
    simp only [Work.Diff.STE.trunc]
    ring
  have h2 : Work.Diff.STE.fourierCoeff (fun x => u x - v x)
      = fun k => Work.Diff.STE.fourierCoeff u k - Work.Diff.STE.fourierCoeff v k :=
    funext fun k => Work.Diff.STE.flat.fourierCoeff_sub_of_continuous _ _ hu.continuous hv.continuous k
  have hc : Summable (fun k : ι → ℤ =>
      (Work.Diff.STE.wt k) ^ s
        * ‖Work.Diff.STE.fourierCoeff u k - Work.Diff.STE.fourierCoeff v k‖ ^ 2) :=
    (Work.Diff.STE.B3.SymCalcStep1.summable_CSq_fourierCoeff s (hu.sub hv)
      (Work.Diff.STE.B3.SymCalcStep1.Periodic1_sub' hup hvp)).congr
      (fun k => by rw [congrFun h2 k])
  rw [h1, h2]
  exact Work.Diff.STE.CSq_trunc_le ρ hρ ε s _ hc

/-! ## The double commutator estimate -/

/-- **The double commutator `[[M_e, S], P]` is of order `2k−1`**, `P := conjLapPow k T T'`, `S := flatCut ρ ε`.  The identity `[[M_e,S],P] = M_e[S,P] + [M_e,P]S − S[M_e,P] − [S,P]M_e` (verified pointwise by expanding both sides) exhibits the four terms as compositions of the order-`2k−1` operators `[S,P]` and `[M_e,P]` with the bounded operators `M_e`, `S` (and an outer multiplier `M_f`), so each term is bounded by `C · CSq (s + 2k − 1) (fourierCoeff w)`; the certificates are `Work.Diff.STE.B3.SymCalcStep6.W_bound` (`[S,P] = −W`), `Work.Diff.STE.B3.SymCalcStep6.conjLapPow_mul_comm_le` (`[M_e,P] = −[P,M_e]`), `mul_CSq_le` (the multipliers `f`, `e`) and `flatCut_CSq_le` (`S`), together with linearity of `fourierCoeff` under sums/differences and `Work.Diff.STE.B3.SymCalcStep1.CSq_add_le`. -/
theorem double_comm_conjLapPow_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : (ι → ℝ) → ℝ) (hρb : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (hdiam : ∀ y : ι → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (L : ℝ) (hL : 0 ≤ L) (hρlip : ∀ y z : ι → ℝ, ‖ρ y - ρ z‖ ≤ L * ‖y - z‖)
    (T T' : (ι → ℝ) → (ι → ℝ)) (hT : ContDiff ℝ (⊤ : ℕ∞) T) (hT' : ContDiff ℝ (⊤ : ℕ∞) T')
    (hTinv1 : ∀ x : ι → ℝ, T' (T x) = x) (hTinv2 : ∀ y : ι → ℝ, T (T' y) = y)
    (hTper : ∀ (i : ι) (x : ι → ℝ), T (x + Pi.single i 1) = T x + Pi.single i 1)
    (f e : (ι → ℝ) → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfp : Work.Diff.STE.Periodic1 f)
    (he : ContDiff ℝ (⊤ : ℕ∞) e) (hep : Work.Diff.STE.Periodic1 e)
    (k : ℕ) (hk : 1 ≤ k) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ w : (ι → ℝ) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) w → Work.Diff.STE.Periodic1 w →
      Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun x => f x * (
            (e x * (Work.Diff.STE.B3.SymCalc.flatCut ρ ε
                (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' w) x
              - Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
                (Work.Diff.STE.B3.SymCalc.flatCut ρ ε w) x))
          + (e x * Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
                (Work.Diff.STE.B3.SymCalc.flatCut ρ ε w) x
              - Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
                (fun y => e y * Work.Diff.STE.B3.SymCalc.flatCut ρ ε w y) x)
          - (Work.Diff.STE.B3.SymCalc.flatCut ρ ε
                (fun y => e y * Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' w y) x
              - Work.Diff.STE.B3.SymCalc.flatCut ρ ε
                (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
                  (fun y => e y * w y)) x)
          - (Work.Diff.STE.B3.SymCalc.flatCut ρ ε
                (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
                  (fun y => e y * w y)) x
              - Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
                (Work.Diff.STE.B3.SymCalc.flatCut ρ ε (fun y => e y * w y)) x))))
        ≤ C * Work.Diff.STE.CSq (s + 2 * k - 1) (Work.Diff.STE.fourierCoeff w) := by
  classical
  -- ## The three `ε`-free certificates, and the three multiplier bounds
  obtain ⟨C1, hC10, hC1b⟩ :=
    Work.Diff.STE.B3.SymCalcStep6.W_bound ρ hρb hdiam L hL hρlip T T' hT hT' hTper hTinv1 hTinv2
      k hk s
  obtain ⟨C2, hC20, hC2b⟩ :=
    Work.Diff.STE.B3.SymCalcStep6.conjLapPow_mul_comm_le e he hep T T' hT hT' hTinv1 hTinv2 hTper
      k hk s
  obtain ⟨Cf, hCf0, hCfb⟩ := mul_CSq_le s f hf hfp
  obtain ⟨Cfe, hCfe0, hCfeab⟩ :=
    mul_CSq_le s (fun x => f x * e x) (hf.mul he)
      (Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hfp hep)
  obtain ⟨Ce, hCe0, hCeab⟩ := mul_CSq_le (s + 2 * k - 1) e he hep
  refine ⟨4 * (Cfe * C1 + Cf * C2 + Cf * C2 + Cf * C1 * Ce), by positivity, ?_⟩
  intro ε hε hε1 w hw hwp
  -- ## Abbreviations
  let S : ((ι → ℝ) → ℂ) → (ι → ℝ) → ℂ := fun u => Work.Diff.STE.B3.SymCalc.flatCut ρ ε u
  let P : ((ι → ℝ) → ℂ) → (ι → ℝ) → ℂ :=
    fun u => Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' u
  let h4 : (ι → ℝ) → ℂ := fun y => e y * w y
  have h4sm : ContDiff ℝ (⊤ : ℕ∞) h4 := he.mul hw
  have h4p : Work.Diff.STE.Periodic1 h4 := Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hep hwp
  have hSsm : ∀ u : (ι → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) u → Work.Diff.STE.Periodic1 u →
      ContDiff ℝ (⊤ : ℕ∞) (S u) :=
    fun u hu hup => Work.Diff.STE.B3.SymCalcStep1.flatCut_contDiff ρ hρb ε hu hup
  have hSp : ∀ u : (ι → ℝ) → ℂ, Work.Diff.STE.Periodic1 (S u) :=
    fun u => Work.Diff.STE.B3.SymCalcStep1.flatCut_periodic ρ ε u
  have hPsm : ∀ u : (ι → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) u → Work.Diff.STE.Periodic1 u →
      ContDiff ℝ (⊤ : ℕ∞) (P u) :=
    fun u hu hup =>
      Work.Diff.STE.B3.SymCalcStep6.conjLapPow_contDiff T T' hT hT' hTper hTinv1 hTinv2 k hu hup
  have hPp : ∀ u : (ι → ℝ) → ℂ, Work.Diff.STE.Periodic1 (P u) :=
    fun u => Work.Diff.STE.B3.SymCalcStep6.conjLapPow_periodic T T' hTper k u
  have hWsm : ∀ u : (ι → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) u → Work.Diff.STE.Periodic1 u →
      ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalcStep6.W ρ T T' k ε u) :=
    fun u hu hup =>
      Work.Diff.STE.B3.SymCalcStep6.W_contDiff ρ hρb T T' hT hT' hTper hTinv1 hTinv2 k ε hu hup
  have hWp : ∀ u : (ι → ℝ) → ℂ,
      Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalcStep6.W ρ T T' k ε u) :=
    fun u => Work.Diff.STE.B3.SymCalcStep6.W_periodic ρ T T' hTper k ε u
  -- ## The four summands of the double commutator, each multiplied by `f`
  let B1 : (ι → ℝ) → ℂ := fun x => e x * (S (P w) x - P (S w) x)
  let B2 : (ι → ℝ) → ℂ := fun x => e x * P (S w) x - P (fun y => e y * S w y) x
  let B3 : (ι → ℝ) → ℂ := fun x => S (fun y => e y * P w y) x - S (P h4) x
  let B4 : (ι → ℝ) → ℂ := fun x => S (P h4) x - P (S h4) x
  let A1 : (ι → ℝ) → ℂ := f * B1
  let A2 : (ι → ℝ) → ℂ := f * B2
  let A3 : (ι → ℝ) → ℂ := f * B3
  let A4 : (ι → ℝ) → ℂ := f * B4
  -- the target integrand, named
  set FF : (ι → ℝ) → ℂ := (fun x => f x * (
            (e x * (Work.Diff.STE.B3.SymCalc.flatCut ρ ε
                (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' w) x
              - Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
                (Work.Diff.STE.B3.SymCalc.flatCut ρ ε w) x))
          + (e x * Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
                (Work.Diff.STE.B3.SymCalc.flatCut ρ ε w) x
              - Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
                (fun y => e y * Work.Diff.STE.B3.SymCalc.flatCut ρ ε w y) x)
          - (Work.Diff.STE.B3.SymCalc.flatCut ρ ε
                (fun y => e y * Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' w y) x
              - Work.Diff.STE.B3.SymCalc.flatCut ρ ε
                (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
                  (fun y => e y * w y)) x)
          - (Work.Diff.STE.B3.SymCalc.flatCut ρ ε
                (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
                  (fun y => e y * w y)) x
              - Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
                (Work.Diff.STE.B3.SymCalc.flatCut ρ ε (fun y => e y * w y)) x))) with hFF
  -- ## Smoothness and periodicity of the four summands
  have hB1sm : ContDiff ℝ (⊤ : ℕ∞) B1 :=
    he.mul ((hSsm (P w) (hPsm w hw hwp) (hPp w)).sub (hPsm (S w) (hSsm w hw hwp) (hSp w)))
  have hB1p : Work.Diff.STE.Periodic1 B1 :=
    Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hep
      (Work.Diff.STE.B3.SymCalcStep1.Periodic1_sub' (hSp (P w)) (hPp (S w)))
  have hB2sm : ContDiff ℝ (⊤ : ℕ∞) B2 :=
    (he.mul (hPsm (S w) (hSsm w hw hwp) (hSp w))).sub
      (hPsm (fun y => e y * S w y) (he.mul (hSsm w hw hwp))
        (Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hep (hSp w)))
  have hB2p : Work.Diff.STE.Periodic1 B2 :=
    Work.Diff.STE.B3.SymCalcStep1.Periodic1_sub'
      (Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hep (hPp (S w)))
      (hPp (fun y => e y * S w y))
  have hB3sm : ContDiff ℝ (⊤ : ℕ∞) B3 :=
    (hSsm (fun y => e y * P w y) (he.mul (hPsm w hw hwp))
        (Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hep (hPp w))).sub
      (hSsm (P h4) (hPsm h4 h4sm h4p) (hPp h4))
  have hB3p : Work.Diff.STE.Periodic1 B3 :=
    Work.Diff.STE.B3.SymCalcStep1.Periodic1_sub'
      (hSp (fun y => e y * P w y)) (hSp (P h4))
  have hB4sm : ContDiff ℝ (⊤ : ℕ∞) B4 :=
    (hSsm (P h4) (hPsm h4 h4sm h4p) (hPp h4)).sub (hPsm (S h4) (hSsm h4 h4sm h4p) (hSp h4))
  have hB4p : Work.Diff.STE.Periodic1 B4 :=
    Work.Diff.STE.B3.SymCalcStep1.Periodic1_sub' (hSp (P h4)) (hPp (S h4))
  have hA1sm : ContDiff ℝ (⊤ : ℕ∞) A1 := hf.mul hB1sm
  have hA1p : Work.Diff.STE.Periodic1 A1 := Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hfp hB1p
  have hA2sm : ContDiff ℝ (⊤ : ℕ∞) A2 := hf.mul hB2sm
  have hA2p : Work.Diff.STE.Periodic1 A2 := Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hfp hB2p
  have hA3sm : ContDiff ℝ (⊤ : ℕ∞) A3 := hf.mul hB3sm
  have hA3p : Work.Diff.STE.Periodic1 A3 := Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hfp hB3p
  have hA4sm : ContDiff ℝ (⊤ : ℕ∞) A4 := hf.mul hB4sm
  have hA4p : Work.Diff.STE.Periodic1 A4 := Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hfp hB4p
  -- ## Bound 1: `M_f M_e [S,P] w` (with `[S,P] w = -W k ε w`)
  have hA1 : Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff A1)
      ≤ (Cfe * C1) * Work.Diff.STE.CSq (s + 2 * k - 1) (Work.Diff.STE.fourierCoeff w) := by
    let WF : (ι → ℝ) → ℂ := Work.Diff.STE.B3.SymCalcStep6.W ρ T T' k ε w
    have hWFsm : ContDiff ℝ (⊤ : ℕ∞) WF := hWsm w hw hwp
    have hWFp : Work.Diff.STE.Periodic1 WF := hWp w
    have heq1 : A1 = fun x => -((f x * e x) * WF x) := by
      funext x
      simp only [A1, B1, S, P, WF, Work.Diff.STE.B3.SymCalcStep6.W, Pi.mul_apply, Pi.sub_apply]
      ring
    calc Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff A1)
        = Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff
            (fun x => -((f x * e x) * WF x))) := by rw [heq1]
      _ = Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff
            (fun x => (f x * e x) * WF x)) :=
          Work.Diff.STE.B3.SymCalcStep6.CSq_fourierCoeff_neg s _
      _ ≤ Cfe * Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff WF) := hCfeab WF hWFsm hWFp
      _ ≤ Cfe * (C1 * Work.Diff.STE.CSq (s + 2 * k - 1) (Work.Diff.STE.fourierCoeff w)) :=
          mul_le_mul_of_nonneg_left (hC1b ε hε hε1 w hw hwp) hCfe0
      _ = (Cfe * C1) * Work.Diff.STE.CSq (s + 2 * k - 1) (Work.Diff.STE.fourierCoeff w) := by
          ring
  -- ## Bound 2: `M_f [M_e,P] (S w)`
  have hA2 : Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff A2)
      ≤ (Cf * C2) * Work.Diff.STE.CSq (s + 2 * k - 1) (Work.Diff.STE.fourierCoeff w) := by
    let Z2 : (ι → ℝ) → ℂ := fun x => P (fun y => e y * S w y) x - e x * P (S w) x
    have hZ2sm : ContDiff ℝ (⊤ : ℕ∞) Z2 :=
      (hPsm (fun y => e y * S w y) (he.mul (hSsm w hw hwp))
        (Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hep (hSp w))).sub
        (he.mul (hPsm (S w) (hSsm w hw hwp) (hSp w)))
    have hZ2p : Work.Diff.STE.Periodic1 Z2 :=
      Work.Diff.STE.B3.SymCalcStep1.Periodic1_sub' (hPp (fun y => e y * S w y))
        (Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hep (hPp (S w)))
    have heq2 : A2 = fun x => -(f x * Z2 x) := by
      funext x
      simp only [A2, B2, Z2, S, P, Pi.mul_apply, Pi.sub_apply]
      ring
    calc Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff A2)
        = Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun x => -(f x * Z2 x))) := by
          rw [heq2]
      _ = Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun x => f x * Z2 x)) :=
          Work.Diff.STE.B3.SymCalcStep6.CSq_fourierCoeff_neg s _
      _ ≤ Cf * Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff Z2) := hCfb Z2 hZ2sm hZ2p
      _ ≤ Cf * (C2 * Work.Diff.STE.CSq (s + 2 * k - 1)
            (Work.Diff.STE.fourierCoeff (S w))) :=
          mul_le_mul_of_nonneg_left (hC2b (S w) (hSsm w hw hwp) (hSp w)) hCf0
      _ ≤ Cf * (C2 * Work.Diff.STE.CSq (s + 2 * k - 1) (Work.Diff.STE.fourierCoeff w)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (flatCut_CSq_le ρ hρb ε (s + 2 * k - 1) w hw hwp) hC20)
            hCf0
      _ = (Cf * C2) * Work.Diff.STE.CSq (s + 2 * k - 1) (Work.Diff.STE.fourierCoeff w) := by
          ring
  -- ## Bound 3: `M_f S [M_e,P] w`
  have hA3 : Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff A3)
      ≤ (Cf * C2) * Work.Diff.STE.CSq (s + 2 * k - 1) (Work.Diff.STE.fourierCoeff w) := by
    let v3 : (ι → ℝ) → ℂ := P h4
    let u3 : (ι → ℝ) → ℂ := fun y => e y * P w y
    have hv3sm : ContDiff ℝ (⊤ : ℕ∞) v3 := hPsm h4 h4sm h4p
    have hv3p : Work.Diff.STE.Periodic1 v3 := hPp h4
    have hu3sm : ContDiff ℝ (⊤ : ℕ∞) u3 := he.mul (hPsm w hw hwp)
    have hu3p : Work.Diff.STE.Periodic1 u3 :=
      Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hep (hPp w)
    have hDsm : ContDiff ℝ (⊤ : ℕ∞) (fun x => S v3 x - S u3 x) :=
      (hSsm v3 hv3sm hv3p).sub (hSsm u3 hu3sm hu3p)
    have hDp : Work.Diff.STE.Periodic1 (fun x => S v3 x - S u3 x) :=
      Work.Diff.STE.B3.SymCalcStep1.Periodic1_sub' (hSp v3) (hSp u3)
    have heq3 : A3 = fun x => -(f x * (S v3 x - S u3 x)) := by
      funext x
      simp only [A3, B3, v3, u3, S, P, h4, Pi.mul_apply, Pi.sub_apply]
      ring
    calc Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff A3)
        = Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff
            (fun x => -(f x * (S v3 x - S u3 x)))) := by rw [heq3]
      _ = Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff
            (fun x => f x * (S v3 x - S u3 x))) :=
          Work.Diff.STE.B3.SymCalcStep6.CSq_fourierCoeff_neg s _
      _ ≤ Cf * Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun x => S v3 x - S u3 x)) :=
          hCfb (fun x => S v3 x - S u3 x) hDsm hDp
      _ ≤ Cf * Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun x => v3 x - u3 x)) :=
          mul_le_mul_of_nonneg_left
            (flatCut_sub_CSQ_le ρ hρb ε s v3 u3 hv3sm hv3p hu3sm hu3p) hCf0
      _ ≤ Cf * (C2 * Work.Diff.STE.CSq (s + 2 * k - 1) (Work.Diff.STE.fourierCoeff w)) :=
          mul_le_mul_of_nonneg_left (hC2b w hw hwp) hCf0
      _ = (Cf * C2) * Work.Diff.STE.CSq (s + 2 * k - 1) (Work.Diff.STE.fourierCoeff w) := by
          ring
  -- ## Bound 4: `M_f [S,P] (M_e w)`
  have hA4 : Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff A4)
      ≤ (Cf * C1 * Ce) * Work.Diff.STE.CSq (s + 2 * k - 1) (Work.Diff.STE.fourierCoeff w) := by
    have heq4 : A4 = fun x => -(f x * Work.Diff.STE.B3.SymCalcStep6.W ρ T T' k ε h4 x) := by
      funext x
      simp only [A4, B4, S, P, h4, Work.Diff.STE.B3.SymCalcStep6.W, Pi.mul_apply, Pi.sub_apply]
      ring
    calc Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff A4)
        = Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff
            (fun x => -(f x * Work.Diff.STE.B3.SymCalcStep6.W ρ T T' k ε h4 x))) := by
          rw [heq4]
      _ = Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff
            (fun x => f x * Work.Diff.STE.B3.SymCalcStep6.W ρ T T' k ε h4 x)) :=
          Work.Diff.STE.B3.SymCalcStep6.CSq_fourierCoeff_neg s _
      _ ≤ Cf * Work.Diff.STE.CSq s
            (Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.SymCalcStep6.W ρ T T' k ε h4)) :=
          hCfb _ (hWsm h4 h4sm h4p) (hWp h4)
      _ ≤ Cf * (C1 * Work.Diff.STE.CSq (s + 2 * k - 1) (Work.Diff.STE.fourierCoeff h4)) :=
          mul_le_mul_of_nonneg_left (hC1b ε hε hε1 h4 h4sm h4p) hCf0
      _ ≤ Cf * (C1 * (Ce * Work.Diff.STE.CSq (s + 2 * k - 1)
            (Work.Diff.STE.fourierCoeff w))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hCeab w hw hwp) hC10) hCf0
      _ = (Cf * C1 * Ce) * Work.Diff.STE.CSq (s + 2 * k - 1) (Work.Diff.STE.fourierCoeff w) := by
          ring
  -- ## Assembly
  have hsplit : FF = fun x => A1 x + A2 x - A3 x - A4 x := by
    rw [hFF]
    funext x
    simp only [A1, A2, A3, A4, B1, B2, B3, B4, S, P, h4, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
    ring
  have hfc : Work.Diff.STE.fourierCoeff (fun x => A1 x + A2 x - A3 x - A4 x)
      = fun k => Work.Diff.STE.fourierCoeff A1 k + Work.Diff.STE.fourierCoeff A2 k
          - Work.Diff.STE.fourierCoeff A3 k - Work.Diff.STE.fourierCoeff A4 k :=
    funext fun k => fourierCoeff_add_sub_four A1 A2 A3 A4 hA1sm.continuous hA2sm.continuous
      hA3sm.continuous hA4sm.continuous k
  have hsum := CSq_add_sub_four_le s (Work.Diff.STE.fourierCoeff A1) (Work.Diff.STE.fourierCoeff A2)
    (Work.Diff.STE.fourierCoeff A3) (Work.Diff.STE.fourierCoeff A4)
    (Work.Diff.STE.B3.SymCalcStep1.summable_CSq_fourierCoeff s hA1sm hA1p)
    (Work.Diff.STE.B3.SymCalcStep1.summable_CSq_fourierCoeff s hA2sm hA2p)
    (Work.Diff.STE.B3.SymCalcStep1.summable_CSq_fourierCoeff s hA3sm hA3p)
    (Work.Diff.STE.B3.SymCalcStep1.summable_CSq_fourierCoeff s hA4sm hA4p)
  calc Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff FF)
      = Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff
          (fun x => A1 x + A2 x - A3 x - A4 x)) := by rw [hsplit]
    _ = Work.Diff.STE.CSq s (fun k => Work.Diff.STE.fourierCoeff A1 k
          + Work.Diff.STE.fourierCoeff A2 k
          - Work.Diff.STE.fourierCoeff A3 k - Work.Diff.STE.fourierCoeff A4 k) := by rw [hfc]
    _ ≤ 4 * (Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff A1)
          + Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff A2)
          + Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff A3)
          + Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff A4)) := hsum
    _ ≤ 4 * ((Cfe * C1 + Cf * C2 + Cf * C2 + Cf * C1 * Ce)
          * Work.Diff.STE.CSq (s + 2 * k - 1) (Work.Diff.STE.fourierCoeff w)) := by
        nlinarith [hA1, hA2, hA3, hA4]
    _ = (4 * (Cfe * C1 + Cf * C2 + Cf * C2 + Cf * C1 * Ce))
          * Work.Diff.STE.CSq (s + 2 * k - 1) (Work.Diff.STE.fourierCoeff w) := by ring

end Work.Diff.STE.B3.SymCalcStep7
