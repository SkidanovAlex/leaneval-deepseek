import Mathlib
import Submission.Work.Diff.STE.B3.SymCalcStep7.Defs
import Submission.Work.Diff.STE.B3.SymCalcStep7.mul_CSq_le
import Submission.Work.Diff.STE.B3.SymCalcStep7.flatCut_CSq_le
import Submission.Work.Diff.STE.B3.SymCalcStep7.conjCut_CSq_le
import Submission.Work.Diff.STE.B3.SymCalcStep7.rho_lipschitz
import Submission.Work.Diff.STE.B3.SymCalcStep7.double_comm_conjLapPow_le
import Submission.Work.Diff.STE.B3.SymCalcStep7.mixed_piece_b_le
import Submission.Work.Diff.STE.B3.SymCalcStep7.mixed_piece_v_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# B3 symbol calculus, step 7: the two-chart transfer pair is of order `2k − 1`

With `Λ = lapPow k`, `S = flatCut ρ ε`, `V = conjCut ρ ε T T'`, `P = conjLapPow k T T'` and the
four pointwise multipliers `a,b,c,d` (`a·b = c·d`), the operator of `Defs.lean` is

  `pairOp = M_a (Λ M_b V − S M_b P) + M_c (P M_d S − V M_d Λ)`,

and expanding the products by the definition of the commutators gives the *exact* splitting
(no analysis, no sign condition)

  `pairOp = M_{ab}([Λ,V] + [P,S]) + M_a[Λ,M_b]V + M_a[M_b,S]P + M_c[P,M_d]S − M_c[V,M_d]Λ`,

where `a·b = c·d` is used **only** to combine the two leading products `M_aM_b = M_{ab} = M_cM_d`.
The six pieces are of order `2k, 2k, 2k−1, 2k−1, 2k−1, 2k−1`; the first two are handled by the
Step-6 certificates `conj_cut_comm_lapPow_le` (`[Λ,V]`) and `W_bound` (`[P,S] = W`), the third and
fifth by the flat Leibniz estimates (`dB3_flat_comm_le`, `conjLapPow_mul_comm_le`) composed with the
order-`0` bounds for `V` (`conjCut_CSq_le`) and `S` (`flatCut_CSq_le`), and the fourth and sixth
(the "mixed" pieces, where a Friedrichs gain of order `−1` is composed with an order-`2k`
operator) by splitting off the commutator and treating the remainder with the double commutator
certificate `double_comm_conjLapPow_le` or by an explicit four-term expansion
(`[[V,M_d],Λ] = V[M_d,Λ] + [V,Λ]M_d − M_d[V,Λ] − [M_d,Λ]V`), whose pieces are again of order
`2k−1`.  Every constant is independent of `ε ∈ (0,1]` and of `g`.
-/

namespace Work.Diff.STE.B3.SymCalcStep7

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The exact decomposition of `pairOp` into its six pieces -/

/-- **The algebraic core of the decomposition.**  With `a·b = c·d`,

  `a(A₁−A₂) + c(A₃−A₄) = ab(u₁−u₂) + ab(u₃−u₄) + a(A₁−bu₁) + a(bu₄−A₂) + c(A₃−du₃) − c(A₄−du₂)`

for arbitrary `A₁,…,u₄ : ℂ`.  (Before the substitution `cd = ab` both sides differ by
`(ab − cd)(u₃ − u₂)`.) -/
lemma piece_decomp_alg (A1 A2 A3 A4 u1 u2 u3 u4 a b c d : ℂ) (h : a * b = c * d) :
    a * (A1 - A2) + c * (A3 - A4)
      = (a * b) * (u1 - u2) + (a * b) * (u3 - u4) + a * (A1 - b * u1) + a * (b * u4 - A2)
        + c * (A3 - d * u3) + (-(c * (A4 - d * u2))) := by
  ring_nf
  have e1 : c * u2 * d = a * b * u2 := by
    rw [mul_assoc c u2 d, mul_comm u2 d, ← mul_assoc, h]
  have e2 : c * u3 * d = a * b * u3 := by
    rw [mul_assoc c u3 d, mul_comm u3 d, ← mul_assoc, h]
  rw [e1, e2]
  ring

/-- **The pointwise decomposition of `pairOp` into its six pieces.** -/
lemma pairOp_eq_pieces (k : ℕ) (ρ : (ι → ℝ) → ℝ) (ε : ℝ) (T T' : (ι → ℝ) → (ι → ℝ))
    (a b c d g : (ι → ℝ) → ℂ) (hrel : ∀ x : ι → ℝ, a x * b x = c x * d x) :
    pairOp k ρ ε T T' a b c d g
      = fun x => (a x * b x) * (Work.Diff.STE.B3.SymCalcStep5.lapPow k
              (Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' g) x
            - Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T'
              (Work.Diff.STE.B3.SymCalcStep5.lapPow k g) x)
        + (a x * b x) * (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
              (Work.Diff.STE.B3.SymCalc.flatCut ρ ε g) x
            - Work.Diff.STE.B3.SymCalc.flatCut ρ ε
              (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' g) x)
        + a x * (Work.Diff.STE.B3.SymCalcStep5.lapPow k
              (fun y => b y * Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' g y) x
            - b x * Work.Diff.STE.B3.SymCalcStep5.lapPow k
              (Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' g) x)
        + a x * (b x * Work.Diff.STE.B3.SymCalc.flatCut ρ ε
              (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' g) x
            - Work.Diff.STE.B3.SymCalc.flatCut ρ ε
              (fun y => b y * Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' g y) x)
        + c x * (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
              (fun y => d y * Work.Diff.STE.B3.SymCalc.flatCut ρ ε g y) x
            - d x * Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
              (Work.Diff.STE.B3.SymCalc.flatCut ρ ε g) x)
        + -(c x * (Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T'
              (fun y => d y * Work.Diff.STE.B3.SymCalcStep5.lapPow k g y) x
            - d x * Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T'
              (Work.Diff.STE.B3.SymCalcStep5.lapPow k g) x)) := by
  funext x
  rw [pairOp]
  exact piece_decomp_alg _ _ _ _ _ _ _ _ _ _ _ _ (hrel x)

/-- `conjCut ρ ε T T' w = compMap T' (flatCut ρ ε (compMap T w))` is smooth for smooth `1`-periodic
`w`, without any hypothesis on `ε`. -/
lemma conjCut_contDiff (ρ : (ι → ℝ) → ℝ) (hρ : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (T T' : (ι → ℝ) → (ι → ℝ)) (hT : ContDiff ℝ (⊤ : ℕ∞) T) (hT' : ContDiff ℝ (⊤ : ℕ∞) T')
    (hTper : ∀ (i : ι) (x : ι → ℝ), T (x + Pi.single i 1) = T x + Pi.single i 1)
    (ε : ℝ) {w : (ι → ℝ) → ℂ} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwp : Work.Diff.STE.Periodic1 w) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' w) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalc.compMap T w) := hw.comp hT
  have h1p : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalc.compMap T w) := by
    intro i x
    show w (T (x + Pi.single i 1)) = w (T x)
    rw [hTper i x]
    exact hwp i (T x)
  have h2 : ContDiff ℝ (⊤ : ℕ∞)
      (Work.Diff.STE.B3.SymCalc.flatCut ρ ε (Work.Diff.STE.B3.SymCalc.compMap T w)) :=
    Work.Diff.STE.B3.SymCalcStep1.flatCut_contDiff ρ hρ ε h1 h1p
  exact h2.comp hT'

/-- `conjCut ρ ε T T' w` is `1`-periodic for `1`-periodic `w`. -/
lemma conjCut_periodic (ρ : (ι → ℝ) → ℝ) (T T' : (ι → ℝ) → (ι → ℝ))
    (hTper : ∀ (i : ι) (x : ι → ℝ), T (x + Pi.single i 1) = T x + Pi.single i 1)
    (hTinv1 : ∀ x : ι → ℝ, T' (T x) = x) (hTinv2 : ∀ y : ι → ℝ, T (T' y) = y)
    (ε : ℝ) (w : (ι → ℝ) → ℂ) (hwp : Work.Diff.STE.Periodic1 w) :
    Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' w) := by
  intro i x
  show Work.Diff.STE.B3.SymCalc.flatCut ρ ε (Work.Diff.STE.B3.SymCalc.compMap T w)
      (T' (x + Pi.single i 1))
    = Work.Diff.STE.B3.SymCalc.flatCut ρ ε (Work.Diff.STE.B3.SymCalc.compMap T w) (T' x)
  rw [Work.Diff.STE.B3.SymCalcStep1.shift_T' T T' hTper hTinv1 hTinv2 i x]
  exact Work.Diff.STE.B3.SymCalcStep1.flatCut_periodic ρ ε _ i _

theorem flat_pair_transfer_le {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) (hk : 1 ≤ k) (s : ℕ)
    (ρ : (ι → ℝ) → ℝ) (hρ : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (hρ0 : ∀ y : ι → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (hρs : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρ1 : ρ 0 = 1)
    (T T' : (ι → ℝ) → (ι → ℝ))
    (hT : ContDiff ℝ (⊤ : ℕ∞) T) (hT' : ContDiff ℝ (⊤ : ℕ∞) T')
    (hTinv1 : ∀ x : ι → ℝ, T' (T x) = x) (hTinv2 : ∀ y : ι → ℝ, T (T' y) = y)
    (hTper : ∀ (i : ι) (x : ι → ℝ), T (x + Pi.single i 1) = T x + Pi.single i 1)
    (a b c d : (ι → ℝ) → ℂ)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hd : ContDiff ℝ (⊤ : ℕ∞) d)
    (hap : Work.Diff.STE.Periodic1 a) (hbp : Work.Diff.STE.Periodic1 b)
    (hcp : Work.Diff.STE.Periodic1 c) (hdp : Work.Diff.STE.Periodic1 d)
    (hrel : ∀ x : ι → ℝ, a x * b x = c x * d x) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ g : (ι → ℝ) → ℂ,
        ContDiff ℝ (⊤ : ℕ∞) g → Work.Diff.STE.Periodic1 g →
        Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff
            (Work.Diff.STE.B3.SymCalcStep7.pairOp k ρ ε T T' a b c d g))
          ≤ K * Work.Diff.STE.CSq (s + 2 * k - 1) (Work.Diff.STE.fourierCoeff g) := by
  classical
  -- ## the Lipschitz constant of `ρ` and the `ε`-independent certificates
  obtain ⟨L, hL, hρlip⟩ := rho_lipschitz ρ hρs hρ0
  obtain ⟨CA, hCAnn, hCAb⟩ :=
    Work.Diff.STE.B3.SymCalcStep6.conj_cut_comm_lapPow_le ρ hρ hρ0 hρ1 L hL hρlip
      T T' hT hT' hTinv1 hTinv2 hTper k hk s
  obtain ⟨CB, hCBnn, hCBb⟩ :=
    Work.Diff.STE.B3.SymCalcStep6.W_bound ρ hρ hρ0 L hL hρlip
      T T' hT hT' hTper hTinv1 hTinv2 k hk s
  obtain ⟨CC, hCCnn, hCCb⟩ :=
    Work.Diff.STE.B3.SymCalcStep6.dB3_flat_comm_le b hb hbp k hk s
  obtain ⟨CD, hCDnn, hCDb⟩ :=
    Work.Diff.STE.B3.SymCalcStep6.conjLapPow_mul_comm_le d hd hdp
      T T' hT hT' hTinv1 hTinv2 hTper k hk s
  obtain ⟨Ma, hMann, hMab⟩ := mul_CSq_le s a ha hap
  obtain ⟨Mc, hMcnn, hMcb⟩ := mul_CSq_le s c hc hcp
  obtain ⟨Mab, hMabnn, hMabb⟩ :=
    mul_CSq_le s (fun x => a x * b x) (ha.mul hb)
      (Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hap hbp)
  obtain ⟨CVl, hCVlnn, hCVlb⟩ :=
    conjCut_CSq_le ρ hρ T T' hT hT' hTinv1 hTinv2 hTper (s + 2 * k - 1)
  -- the two mixed pieces (delegated certificates)
  obtain ⟨CB4, hCB4nn, hCB4b⟩ :=
    mixed_piece_b_le ρ hρ hρ0 hρ1 L hL hρlip T T' hT hT' hTinv1 hTinv2 hTper
      a b ha hap hb hbp k hk s
  obtain ⟨CB6, hCB6nn, hCB6b⟩ :=
    mixed_piece_v_le ρ hρ hρ0 hρ1 L hL hρlip T T' hT hT' hTinv1 hTinv2 hTper
      c d hc hcp hd hdp k hk s
  -- ## the constant
  let Kfun : Fin 6 → ℝ := ![Mab * CA, Mab * CB, Ma * CC * CVl, CB4, Mc * CD, CB6]
  refine ⟨6 * ∑ i : Fin 6, Kfun i, ?_, ?_⟩
  · refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => ?_)
    fin_cases i
    · show (0 : ℝ) ≤ Mab * CA; positivity
    · show (0 : ℝ) ≤ Mab * CB; positivity
    · show (0 : ℝ) ≤ Ma * CC * CVl; positivity
    · show (0 : ℝ) ≤ CB4; exact hCB4nn
    · show (0 : ℝ) ≤ Mc * CD; positivity
    · show (0 : ℝ) ≤ CB6; exact hCB6nn
  · intro ε hε hε1 g hg hgp
    -- ## smoothness / periodicity of the atomic functions
    have hVsm : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' g) :=
      conjCut_contDiff ρ hρ T T' hT hT' hTper ε hg hgp
    have hVp : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' g) :=
      conjCut_periodic ρ T T' hTper hTinv1 hTinv2 ε g hgp
    have hΛsm : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalcStep5.lapPow k g) :=
      (Work.Diff.STE.B3.SymCalcStep6.lapPow_toolbox (ι := ι) k 0).2.2.1 g hg hgp
    have hΛp : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalcStep5.lapPow k g) :=
      (Work.Diff.STE.B3.SymCalcStep6.lapPow_toolbox (ι := ι) k 0).2.2.2 g
    have hPsm : ContDiff ℝ (⊤ : ℕ∞)
        (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' g) :=
      Work.Diff.STE.B3.SymCalcStep6.conjLapPow_contDiff T T' hT hT' hTper hTinv1 hTinv2 k hg hgp
    have hPp : Work.Diff.STE.Periodic1
        (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' g) :=
      Work.Diff.STE.B3.SymCalcStep6.conjLapPow_periodic T T' hTper k g
    have hSsm : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalc.flatCut ρ ε g) :=
      Work.Diff.STE.B3.SymCalcStep1.flatCut_contDiff ρ hρ ε hg hgp
    have hSp : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalc.flatCut ρ ε g) :=
      Work.Diff.STE.B3.SymCalcStep1.flatCut_periodic ρ ε g
    have hΛVsm : ContDiff ℝ (⊤ : ℕ∞)
        (Work.Diff.STE.B3.SymCalcStep5.lapPow k (Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' g)) :=
      (Work.Diff.STE.B3.SymCalcStep6.lapPow_toolbox (ι := ι) k 0).2.2.1 _ hVsm hVp
    have hVΛsm : ContDiff ℝ (⊤ : ℕ∞)
        (Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T'
          (Work.Diff.STE.B3.SymCalcStep5.lapPow k g)) :=
      conjCut_contDiff ρ hρ T T' hT hT' hTper ε hΛsm hΛp
    have hPSsm : ContDiff ℝ (⊤ : ℕ∞)
        (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
          (Work.Diff.STE.B3.SymCalc.flatCut ρ ε g)) :=
      Work.Diff.STE.B3.SymCalcStep6.conjLapPow_contDiff T T' hT hT' hTper hTinv1 hTinv2 k hSsm hSp
    have hSPsm : ContDiff ℝ (⊤ : ℕ∞)
        (Work.Diff.STE.B3.SymCalc.flatCut ρ ε
          (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' g)) :=
      Work.Diff.STE.B3.SymCalcStep1.flatCut_contDiff ρ hρ ε hPsm hPp
    have hSbPsm : ContDiff ℝ (⊤ : ℕ∞)
        (Work.Diff.STE.B3.SymCalc.flatCut ρ ε
          (fun y => b y * Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' g y)) :=
      Work.Diff.STE.B3.SymCalcStep1.flatCut_contDiff ρ hρ ε (hb.mul hPsm)
        (Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hbp hPp)
    have hPdSsm : ContDiff ℝ (⊤ : ℕ∞)
        (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
          (fun y => d y * Work.Diff.STE.B3.SymCalc.flatCut ρ ε g y)) :=
      Work.Diff.STE.B3.SymCalcStep6.conjLapPow_contDiff T T' hT hT' hTper hTinv1 hTinv2 k
        (hd.mul hSsm) (Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hdp hSp)
    have hVdLsm : ContDiff ℝ (⊤ : ℕ∞)
        (Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T'
          (fun y => d y * Work.Diff.STE.B3.SymCalcStep5.lapPow k g y)) :=
      conjCut_contDiff ρ hρ T T' hT hT' hTper ε (hd.mul hΛsm)
        (Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hdp hΛp)
    -- ## the six pieces of the decomposition, as local definitions
    set LV : (ι → ℝ) → ℂ := Work.Diff.STE.B3.SymCalcStep5.lapPow k
      (Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' g) with hLV
    set VL : (ι → ℝ) → ℂ := Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T'
      (Work.Diff.STE.B3.SymCalcStep5.lapPow k g) with hVL
    set PS : (ι → ℝ) → ℂ := Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
      (Work.Diff.STE.B3.SymCalc.flatCut ρ ε g) with hPS
    set SP : (ι → ℝ) → ℂ := Work.Diff.STE.B3.SymCalc.flatCut ρ ε
      (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' g) with hSP
    set LbV : (ι → ℝ) → ℂ := Work.Diff.STE.B3.SymCalcStep5.lapPow k
      (fun y => b y * Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' g y) with hLbV
    set SbP : (ι → ℝ) → ℂ := Work.Diff.STE.B3.SymCalc.flatCut ρ ε
      (fun y => b y * Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' g y) with hSbP
    set PdS : (ι → ℝ) → ℂ := Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
      (fun y => d y * Work.Diff.STE.B3.SymCalc.flatCut ρ ε g y) with hPdS
    set VdL : (ι → ℝ) → ℂ := Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T'
      (fun y => d y * Work.Diff.STE.B3.SymCalcStep5.lapPow k g y) with hVdL
    set FA : (ι → ℝ) → ℂ := fun x => (a x * b x) * (LV x - VL x) with hFA
    set FB : (ι → ℝ) → ℂ := fun x => (a x * b x) * (PS x - SP x) with hFB
    set FC : (ι → ℝ) → ℂ := fun x => a x * (LbV x - b x * LV x) with hFC
    set FD : (ι → ℝ) → ℂ := fun x => a x * (b x * SP x - SbP x) with hFD
    set FE : (ι → ℝ) → ℂ := fun x => c x * (PdS x - d x * PS x) with hFE
    set FF : (ι → ℝ) → ℂ := fun x => -(c x * (VdL x - d x * VL x)) with hFF
    have hLVp : Work.Diff.STE.Periodic1 LV := by
      rw [hLV]; exact (Work.Diff.STE.B3.SymCalcStep6.lapPow_toolbox (ι := ι) k 0).2.2.2 _
    have hVLp : Work.Diff.STE.Periodic1 VL := by
      rw [hVL]
      exact conjCut_periodic ρ T T' hTper hTinv1 hTinv2 ε _
        ((Work.Diff.STE.B3.SymCalcStep6.lapPow_toolbox (ι := ι) k 0).2.2.2 g)
    have hPSp : Work.Diff.STE.Periodic1 PS := by
      rw [hPS]
      exact Work.Diff.STE.B3.SymCalcStep6.conjLapPow_periodic T T' hTper k _
    have hSPp : Work.Diff.STE.Periodic1 SP := by
      rw [hSP]; exact Work.Diff.STE.B3.SymCalcStep1.flatCut_periodic ρ ε _
    have hLbVp : Work.Diff.STE.Periodic1 LbV := by
      rw [hLbV]; exact (Work.Diff.STE.B3.SymCalcStep6.lapPow_toolbox (ι := ι) k 0).2.2.2 _
    have hSbPp : Work.Diff.STE.Periodic1 SbP := by
      rw [hSbP]; exact Work.Diff.STE.B3.SymCalcStep1.flatCut_periodic ρ ε _
    have hPdSp : Work.Diff.STE.Periodic1 PdS := by
      rw [hPdS]; exact Work.Diff.STE.B3.SymCalcStep6.conjLapPow_periodic T T' hTper k _
    have hVdLp : Work.Diff.STE.Periodic1 VdL := by
      rw [hVdL]
      exact conjCut_periodic ρ T T' hTper hTinv1 hTinv2 ε _
        (Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hdp hΛp)
    have hFAsm : ContDiff ℝ (⊤ : ℕ∞) FA := by
      rw [hFA]
      exact (ha.mul hb).mul (hΛVsm.sub hVΛsm)
    have hFAp : Work.Diff.STE.Periodic1 FA := by
      rw [hFA]
      exact Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul'
        (Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hap hbp)
        (Work.Diff.STE.B3.SymCalcStep1.Periodic1_sub' hLVp hVLp)
    have hFBsm : ContDiff ℝ (⊤ : ℕ∞) FB := by
      rw [hFB]
      exact (ha.mul hb).mul (hPSsm.sub hSPsm)
    have hFBp : Work.Diff.STE.Periodic1 FB := by
      rw [hFB]
      exact Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul'
        (Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hap hbp)
        (Work.Diff.STE.B3.SymCalcStep1.Periodic1_sub' hPSp hSPp)
    have hFCsm : ContDiff ℝ (⊤ : ℕ∞) FC := by
      rw [hFC]
      exact ha.mul (((Work.Diff.STE.B3.SymCalcStep6.lapPow_toolbox (ι := ι) k 0).2.2.1 _
          (hb.mul hVsm) (Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hbp hVp)).sub (hb.mul hΛVsm))
    have hFCp : Work.Diff.STE.Periodic1 FC := by
      rw [hFC]
      exact Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hap
        (Work.Diff.STE.B3.SymCalcStep1.Periodic1_sub' hLbVp
          (Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hbp hLVp))
    have hFDsm : ContDiff ℝ (⊤ : ℕ∞) FD := by
      rw [hFD]
      exact ha.mul ((hb.mul hSPsm).sub hSbPsm)
    have hFDp : Work.Diff.STE.Periodic1 FD := by
      rw [hFD]
      exact Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hap
        (Work.Diff.STE.B3.SymCalcStep1.Periodic1_sub'
          (Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hbp hSPp) hSbPp)
    have hFEsm : ContDiff ℝ (⊤ : ℕ∞) FE := by
      rw [hFE]
      exact hc.mul (hPdSsm.sub (hd.mul hPSsm))
    have hFEp : Work.Diff.STE.Periodic1 FE := by
      rw [hFE]
      exact Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hcp
        (Work.Diff.STE.B3.SymCalcStep1.Periodic1_sub' hPdSp
          (Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hdp hPSp))
    have hFFsm : ContDiff ℝ (⊤ : ℕ∞) FF := by
      rw [hFF]
      exact ContDiff.neg (hc.mul (hVdLsm.sub (hd.mul hVΛsm)))
    have hFFp : Work.Diff.STE.Periodic1 FF := by
      rw [hFF]
      intro i x
      show -(c (x + Pi.single i 1) * (VdL (x + Pi.single i 1)
            - d (x + Pi.single i 1) * VL (x + Pi.single i 1)))
        = -(c x * (VdL x - d x * VL x))
      rw [hcp i x, hdp i x, hVdLp i x, hVLp i x]
    -- ## piece 1: `M_{ab}[Λ,V]`
    have hA : Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun x => (a x * b x) *
          (Work.Diff.STE.B3.SymCalcStep5.lapPow k
              (Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' g) x
            - Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T'
              (Work.Diff.STE.B3.SymCalcStep5.lapPow k g) x)))
        ≤ (Mab * CA) * Work.Diff.STE.CSq (s + 2 * k - 1) (Work.Diff.STE.fourierCoeff g) := by
      have h1sm := hΛVsm.sub hVΛsm
      have h1p : Work.Diff.STE.Periodic1 (fun x => Work.Diff.STE.B3.SymCalcStep5.lapPow k
              (Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' g) x
            - Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T'
              (Work.Diff.STE.B3.SymCalcStep5.lapPow k g) x) :=
        Work.Diff.STE.B3.SymCalcStep1.Periodic1_sub'
          ((Work.Diff.STE.B3.SymCalcStep6.lapPow_toolbox (ι := ι) k 0).2.2.2 _)
          (conjCut_periodic ρ T T' hTper hTinv1 hTinv2 ε _ hΛp)
      calc Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun x => (a x * b x) *
            (Work.Diff.STE.B3.SymCalcStep5.lapPow k
                (Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' g) x
              - Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T'
                (Work.Diff.STE.B3.SymCalcStep5.lapPow k g) x)))
          ≤ Mab * Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun x =>
              Work.Diff.STE.B3.SymCalcStep5.lapPow k
                  (Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' g) x
                - Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T'
                  (Work.Diff.STE.B3.SymCalcStep5.lapPow k g) x)) := hMabb _ h1sm h1p
        _ ≤ Mab * (CA * Work.Diff.STE.CSq (s + 2 * k - 1) (Work.Diff.STE.fourierCoeff g)) :=
            mul_le_mul_of_nonneg_left
              (hCAb ε hε hε1 g hg hgp
                (Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff g hg hgp
                  (s + 2 * k - 1))) hMabnn
        _ = (Mab * CA) * Work.Diff.STE.CSq (s + 2 * k - 1)
              (Work.Diff.STE.fourierCoeff g) := by ring
    -- ## piece 2: `M_{ab}[P,S] = M_{ab} W`
    have hB : Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun x => (a x * b x) *
          (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
              (Work.Diff.STE.B3.SymCalc.flatCut ρ ε g) x
            - Work.Diff.STE.B3.SymCalc.flatCut ρ ε
              (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' g) x)))
        ≤ (Mab * CB) * Work.Diff.STE.CSq (s + 2 * k - 1) (Work.Diff.STE.fourierCoeff g) := by
      have hWsm : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalcStep6.W ρ T T' k ε g) :=
        Work.Diff.STE.B3.SymCalcStep6.W_contDiff ρ hρ T T' hT hT' hTper hTinv1 hTinv2 k ε hg hgp
      have hWp : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalcStep6.W ρ T T' k ε g) :=
        Work.Diff.STE.B3.SymCalcStep6.W_periodic ρ T T' hTper k ε g
      calc Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun x => (a x * b x) *
            (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
                (Work.Diff.STE.B3.SymCalc.flatCut ρ ε g) x
              - Work.Diff.STE.B3.SymCalc.flatCut ρ ε
                (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' g) x)))
          = Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun x => (a x * b x) *
              Work.Diff.STE.B3.SymCalcStep6.W ρ T T' k ε g x)) := rfl
        _ ≤ Mab * Work.Diff.STE.CSq s
              (Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.SymCalcStep6.W ρ T T' k ε g)) :=
            hMabb _ hWsm hWp
        _ ≤ Mab * (CB * Work.Diff.STE.CSq (s + 2 * k - 1) (Work.Diff.STE.fourierCoeff g)) :=
            mul_le_mul_of_nonneg_left (hCBb ε hε hε1 g hg hgp) hMabnn
        _ = (Mab * CB) * Work.Diff.STE.CSq (s + 2 * k - 1)
              (Work.Diff.STE.fourierCoeff g) := by ring
    -- ## piece 3: `M_a [Λ,M_b] V`
    have hC : Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun x => a x *
          (Work.Diff.STE.B3.SymCalcStep5.lapPow k
              (fun y => b y * Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' g y) x
            - b x * Work.Diff.STE.B3.SymCalcStep5.lapPow k
              (Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' g) x)))
        ≤ (Ma * CC * CVl) * Work.Diff.STE.CSq (s + 2 * k - 1) (Work.Diff.STE.fourierCoeff g) := by
      have hbsm : ContDiff ℝ (⊤ : ℕ∞) (fun y => b y * Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' g y) :=
        hb.mul hVsm
      have hbp' : Work.Diff.STE.Periodic1 (fun y => b y * Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' g y) :=
        Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hbp hVp
      have h1sm : ContDiff ℝ (⊤ : ℕ∞) (fun x => Work.Diff.STE.B3.SymCalcStep5.lapPow k
              (fun y => b y * Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' g y) x
            - b x * Work.Diff.STE.B3.SymCalcStep5.lapPow k
              (Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' g) x) :=
        ((Work.Diff.STE.B3.SymCalcStep6.lapPow_toolbox (ι := ι) k 0).2.2.1 _ hbsm hbp').sub
          (hb.mul hΛVsm)
      have h1p : Work.Diff.STE.Periodic1 (fun x => Work.Diff.STE.B3.SymCalcStep5.lapPow k
              (fun y => b y * Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' g y) x
            - b x * Work.Diff.STE.B3.SymCalcStep5.lapPow k
              (Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' g) x) :=
        Work.Diff.STE.B3.SymCalcStep1.Periodic1_sub'
          ((Work.Diff.STE.B3.SymCalcStep6.lapPow_toolbox (ι := ι) k 0).2.2.2 _)
          (Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hbp
            ((Work.Diff.STE.B3.SymCalcStep6.lapPow_toolbox (ι := ι) k 0).2.2.2 _))
      calc Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun x => a x *
            (Work.Diff.STE.B3.SymCalcStep5.lapPow k
                (fun y => b y * Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' g y) x
              - b x * Work.Diff.STE.B3.SymCalcStep5.lapPow k
                (Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' g) x)))
          ≤ Ma * Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun x =>
              Work.Diff.STE.B3.SymCalcStep5.lapPow k
                  (fun y => b y * Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' g y) x
                - b x * Work.Diff.STE.B3.SymCalcStep5.lapPow k
                  (Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' g) x)) := hMab _ h1sm h1p
        _ ≤ Ma * (CC * Work.Diff.STE.CSq (s + 2 * k - 1)
              (Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' g))) :=
            mul_le_mul_of_nonneg_left (hCCb _ hVsm hVp) hMann
        _ ≤ Ma * (CC * (CVl * Work.Diff.STE.CSq (s + 2 * k - 1)
              (Work.Diff.STE.fourierCoeff g))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (hCVlb ε hε hε1 g hg hgp) hCCnn) hMann
        _ = (Ma * CC * CVl) * Work.Diff.STE.CSq (s + 2 * k - 1)
              (Work.Diff.STE.fourierCoeff g) := by ring
    -- ## piece 4: `M_a [M_b,S] P` (delegated)
    have hD : Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun x => a x *
          (b x * Work.Diff.STE.B3.SymCalc.flatCut ρ ε
              (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' g) x
            - Work.Diff.STE.B3.SymCalc.flatCut ρ ε
              (fun y => b y * Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' g y) x)))
        ≤ CB4 * Work.Diff.STE.CSq (s + 2 * k - 1) (Work.Diff.STE.fourierCoeff g) :=
      hCB4b ε hε hε1 g hg hgp
    -- ## piece 5: `M_c [P,M_d] S`
    have hE : Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun x => c x *
          (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
              (fun y => d y * Work.Diff.STE.B3.SymCalc.flatCut ρ ε g y) x
            - d x * Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
              (Work.Diff.STE.B3.SymCalc.flatCut ρ ε g) x)))
        ≤ (Mc * CD) * Work.Diff.STE.CSq (s + 2 * k - 1) (Work.Diff.STE.fourierCoeff g) := by
      have hdsm : ContDiff ℝ (⊤ : ℕ∞) (fun y => d y * Work.Diff.STE.B3.SymCalc.flatCut ρ ε g y) :=
        hd.mul hSsm
      have hdp' : Work.Diff.STE.Periodic1 (fun y => d y * Work.Diff.STE.B3.SymCalc.flatCut ρ ε g y) :=
        Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hdp hSp
      have h1sm : ContDiff ℝ (⊤ : ℕ∞) (fun x => Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
              (fun y => d y * Work.Diff.STE.B3.SymCalc.flatCut ρ ε g y) x
            - d x * Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
              (Work.Diff.STE.B3.SymCalc.flatCut ρ ε g) x) :=
        (Work.Diff.STE.B3.SymCalcStep6.conjLapPow_contDiff T T' hT hT' hTper hTinv1 hTinv2 k
          hdsm hdp').sub (hd.mul hPSsm)
      have h1p : Work.Diff.STE.Periodic1 (fun x => Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
              (fun y => d y * Work.Diff.STE.B3.SymCalc.flatCut ρ ε g y) x
            - d x * Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
              (Work.Diff.STE.B3.SymCalc.flatCut ρ ε g) x) :=
        Work.Diff.STE.B3.SymCalcStep1.Periodic1_sub'
          (Work.Diff.STE.B3.SymCalcStep6.conjLapPow_periodic T T' hTper k _)
          (Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hdp
            (Work.Diff.STE.B3.SymCalcStep6.conjLapPow_periodic T T' hTper k _))
      calc Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun x => c x *
            (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
                (fun y => d y * Work.Diff.STE.B3.SymCalc.flatCut ρ ε g y) x
              - d x * Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
                (Work.Diff.STE.B3.SymCalc.flatCut ρ ε g) x)))
          ≤ Mc * Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun x =>
              Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
                  (fun y => d y * Work.Diff.STE.B3.SymCalc.flatCut ρ ε g y) x
                - d x * Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
                  (Work.Diff.STE.B3.SymCalc.flatCut ρ ε g) x)) := hMcb _ h1sm h1p
        _ ≤ Mc * (CD * Work.Diff.STE.CSq (s + 2 * k - 1)
              (Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.SymCalc.flatCut ρ ε g))) :=
            mul_le_mul_of_nonneg_left (hCDb _ hSsm hSp) hMcnn
        _ ≤ Mc * (CD * (1 * Work.Diff.STE.CSq (s + 2 * k - 1)
              (Work.Diff.STE.fourierCoeff g))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left
                (by simpa using flatCut_CSq_le ρ hρ ε (s + 2 * k - 1) g hg hgp) hCDnn) hMcnn
        _ = (Mc * CD) * Work.Diff.STE.CSq (s + 2 * k - 1)
              (Work.Diff.STE.fourierCoeff g) := by ring
    -- ## piece 6: `M_c [V,M_d] Λ` (delegated, up to a sign)
    have hF : Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun x => -(c x *
          (Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T'
              (fun y => d y * Work.Diff.STE.B3.SymCalcStep5.lapPow k g y) x
            - d x * Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T'
              (Work.Diff.STE.B3.SymCalcStep5.lapPow k g) x))))
        ≤ CB6 * Work.Diff.STE.CSq (s + 2 * k - 1) (Work.Diff.STE.fourierCoeff g) := by
      rw [Work.Diff.STE.B3.SymCalcStep6.CSq_fourierCoeff_neg]
      exact hCB6b ε hε hε1 g hg hgp
    -- ## the six-piece decomposition and the sum bound
    have hvec : (fun x : ι → ℝ => FA x + FB x + FC x + FD x + FE x + FF x)
        = fun x => ∑ i : Fin 6, (![FA, FB, FC, FD, FE, FF] : Fin 6 → (ι → ℝ) → ℂ) i x := by
      funext x
      rw [Fin.sum_univ_six]
      rw [show (![FA, FB, FC, FD, FE, FF] : Fin 6 → (ι → ℝ) → ℂ) 1 = FB from rfl,
        show (![FA, FB, FC, FD, FE, FF] : Fin 6 → (ι → ℝ) → ℂ) 2 = FC from rfl,
        show (![FA, FB, FC, FD, FE, FF] : Fin 6 → (ι → ℝ) → ℂ) 3 = FD from rfl,
        show (![FA, FB, FC, FD, FE, FF] : Fin 6 → (ι → ℝ) → ℂ) 4 = FE from rfl,
        show (![FA, FB, FC, FD, FE, FF] : Fin 6 → (ι → ℝ) → ℂ) 5 = FF from rfl]
      rfl
    have hcont : ∀ i : Fin 6, Continuous ((![FA, FB, FC, FD, FE, FF] : Fin 6 → (ι → ℝ) → ℂ) i) := by
      intro i
      fin_cases i
      · show Continuous FA; exact hFAsm.continuous
      · show Continuous FB; exact hFBsm.continuous
      · show Continuous FC; exact hFCsm.continuous
      · show Continuous FD; exact hFDsm.continuous
      · show Continuous FE; exact hFEsm.continuous
      · show Continuous FF; exact hFFsm.continuous
    have hsumm : ∀ i : Fin 6, Summable (fun m : ι → ℤ => (Work.Diff.STE.wt m) ^ s *
        ‖Work.Diff.STE.fourierCoeff ((![FA, FB, FC, FD, FE, FF] : Fin 6 → (ι → ℝ) → ℂ) i) m‖ ^ 2) := by
      intro i
      fin_cases i
      · show Summable (fun m : ι → ℤ => (Work.Diff.STE.wt m) ^ s * ‖Work.Diff.STE.fourierCoeff FA m‖ ^ 2)
        exact Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff FA hFAsm hFAp s
      · show Summable (fun m : ι → ℤ => (Work.Diff.STE.wt m) ^ s * ‖Work.Diff.STE.fourierCoeff FB m‖ ^ 2)
        exact Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff FB hFBsm hFBp s
      · show Summable (fun m : ι → ℤ => (Work.Diff.STE.wt m) ^ s * ‖Work.Diff.STE.fourierCoeff FC m‖ ^ 2)
        exact Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff FC hFCsm hFCp s
      · show Summable (fun m : ι → ℤ => (Work.Diff.STE.wt m) ^ s * ‖Work.Diff.STE.fourierCoeff FD m‖ ^ 2)
        exact Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff FD hFDsm hFDp s
      · show Summable (fun m : ι → ℤ => (Work.Diff.STE.wt m) ^ s * ‖Work.Diff.STE.fourierCoeff FE m‖ ^ 2)
        exact Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff FE hFEsm hFEp s
      · show Summable (fun m : ι → ℤ => (Work.Diff.STE.wt m) ^ s * ‖Work.Diff.STE.fourierCoeff FF m‖ ^ 2)
        exact Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff FF hFFsm hFFp s
    have hKi : ∀ i : Fin 6, Work.Diff.STE.CSq s
          (Work.Diff.STE.fourierCoeff ((![FA, FB, FC, FD, FE, FF] : Fin 6 → (ι → ℝ) → ℂ) i))
        ≤ Kfun i * Work.Diff.STE.CSq (s + 2 * k - 1) (Work.Diff.STE.fourierCoeff g) := by
      intro i
      fin_cases i
      · show Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff FA) ≤ (Mab * CA) * _
        exact hA
      · show Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff FB) ≤ (Mab * CB) * _
        exact hB
      · show Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff FC) ≤ (Ma * CC * CVl) * _
        exact hC
      · show Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff FD) ≤ CB4 * _
        exact hD
      · show Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff FE) ≤ (Mc * CD) * _
        exact hE
      · show Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff FF) ≤ CB6 * _
        exact hF
    have hcoeff : Work.Diff.STE.fourierCoeff
          (fun x : ι → ℝ => ∑ i : Fin 6, (![FA, FB, FC, FD, FE, FF] : Fin 6 → (ι → ℝ) → ℂ) i x)
        = fun m : ι → ℤ => ∑ i : Fin 6,
            Work.Diff.STE.fourierCoeff ((![FA, FB, FC, FD, FE, FF] : Fin 6 → (ι → ℝ) → ℂ) i) m := by
      funext m
      exact Work.Diff.STE.B3.SymCalcStep1.fourierCoeff_ftype_sum_of_continuous _ hcont m
    have hdecomp : Work.Diff.STE.B3.SymCalcStep7.pairOp k ρ ε T T' a b c d g
        = fun x => FA x + FB x + FC x + FD x + FE x + FF x := by
      rw [pairOp_eq_pieces k ρ ε T T' a b c d g hrel]
    calc Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff
            (Work.Diff.STE.B3.SymCalcStep7.pairOp k ρ ε T T' a b c d g))
        = Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff
            (fun x : ι → ℝ => ∑ i : Fin 6, (![FA, FB, FC, FD, FE, FF] : Fin 6 → (ι → ℝ) → ℂ) i x)) := by
          rw [hdecomp, hvec]
      _ = Work.Diff.STE.CSq s (fun m : ι → ℤ => ∑ i : Fin 6,
            Work.Diff.STE.fourierCoeff ((![FA, FB, FC, FD, FE, FF] : Fin 6 → (ι → ℝ) → ℂ) i) m) := by
          rw [hcoeff]
      _ ≤ 6 * ∑ i : Fin 6, Work.Diff.STE.CSq s
            (Work.Diff.STE.fourierCoeff ((![FA, FB, FC, FD, FE, FF] : Fin 6 → (ι → ℝ) → ℂ) i)) :=
          Work.Diff.STE.B3.SymCalcStep1.CSq_fintype_sum_le s _ hsumm
      _ ≤ 6 * ∑ i : Fin 6, (Kfun i * Work.Diff.STE.CSq (s + 2 * k - 1)
            (Work.Diff.STE.fourierCoeff g)) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hKi i) (by norm_num)
      _ = 6 * ((∑ i : Fin 6, Kfun i) * Work.Diff.STE.CSq (s + 2 * k - 1)
            (Work.Diff.STE.fourierCoeff g)) := by rw [Finset.sum_mul]
      _ = (6 * ∑ i : Fin 6, Kfun i) * Work.Diff.STE.CSq (s + 2 * k - 1)
            (Work.Diff.STE.fourierCoeff g) := by ring

end Work.Diff.STE.B3.SymCalcStep7
