import Mathlib
import Submission.Work.Diff.STE.B3.SymCalcStep7.mul_CSq_le
import Submission.Work.Diff.STE.B3.SymCalcStep7.flatCut_CSq_le
import Submission.Work.Diff.STE.B3.SymCalcStep7.double_comm_conjLapPow_le
import Submission.Work.Diff.STE.B3.SymCalcStep7.conjLapPow_sub
import Submission.Work.Diff.STE.B3.SymCalcStep6.conj_cut_comm_lapPow_le
import Submission.Work.Diff.STE.B3.SymCalcStep6.conjLapPow_mul_comm_le
import Submission.Work.Diff.STE.B3.SymCalcStep6.conjCut_multiplier_gain
import Submission.Work.Diff.STE.B3.SymCalcStep6.lapPow_toolbox
import Submission.Work.Diff.STE.B3.SymCalcStep6.lapPow_algebra
import Submission.Work.Diff.STE.B3.SymCalcStep1.conj_cut_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3.SymCalcStep7

/-- The `b`-mixed piece: the Friedrichs commutator `[M_b, S_ε]` (order `−1`) composed with the order-`2k` operator `P = conjLapPow k T T'`, multiplied by `a`.  The gain is taken before `P` via the identity `X = Y + (X − Y)` with `X = [M_b,S](P g)`, `Y = P([M_b,S]g)`: (i) `M_a P ([M_b,S] g)` is bounded by the `T = T' = id` instance of `conjCut_multiplier_gain` with multiplier `b`, instantiated at parameter `s+2k−1` (output level `s+2k`, input level `s+2k−1`), followed by the order-`2k` cost of `P` (`conjLapPow_CSq_le`), and (ii) `M_a ([[M_b,S],P] g)` is bounded by `double_comm_conjLapPow_le` with `f := a`, `e := b`, `w := g` after checking pointwise that `[[M_b,S],P]g` equals the four-term sum occurring there.  Identifying `Y` with `P` applied to the difference `(M_b ∘ S) g − S (M_b g)` uses the additivity of `P` (`conjLapPow_add`, and `P u = P((u−v)+v)` for the `u−v` form). -/
theorem mixed_piece_b_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : (ι → ℝ) → ℝ) (hρ : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (hdiam : ∀ y : ι → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (hρ0 : ρ 0 = 1)
    (L : ℝ) (hL : 0 ≤ L) (hρlip : ∀ y z : ι → ℝ, ‖ρ y - ρ z‖ ≤ L * ‖y - z‖)
    (T T' : (ι → ℝ) → (ι → ℝ)) (hT : ContDiff ℝ (⊤ : ℕ∞) T) (hT' : ContDiff ℝ (⊤ : ℕ∞) T')
    (hTinv1 : ∀ x : ι → ℝ, T' (T x) = x) (hTinv2 : ∀ y : ι → ℝ, T (T' y) = y)
    (hTper : ∀ (i : ι) (x : ι → ℝ), T (x + Pi.single i 1) = T x + Pi.single i 1)
    (a b : (ι → ℝ) → ℂ) (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hap : Work.Diff.STE.Periodic1 a)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hbp : Work.Diff.STE.Periodic1 b)
    (k : ℕ) (hk : 1 ≤ k) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ g : (ι → ℝ) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) g → Work.Diff.STE.Periodic1 g →
      Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun x => a x *
          (b x * Work.Diff.STE.B3.SymCalc.flatCut ρ ε
              (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' g) x
            - Work.Diff.STE.B3.SymCalc.flatCut ρ ε
              (fun y => b y * Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' g y) x)))
        ≤ C * Work.Diff.STE.CSq (s + 2 * k - 1) (Work.Diff.STE.fourierCoeff g) := by
  classical
  -- ## The three `ε`-free certificates
  obtain ⟨C2, hC20, hC2⟩ :=
    double_comm_conjLapPow_le ρ hρ hdiam L hL hρlip T T' hT hT' hTinv1 hTinv2 hTper
      a b ha hap hb hbp k hk s
  obtain ⟨Ca, hCa0, hCa⟩ := mul_CSq_le s a ha hap
  obtain ⟨Cb, hCb0, hCb⟩ :=
    Work.Diff.STE.B3.SymCalcStep6.conjCut_multiplier_gain ρ hρ hdiam hρ0 L hL hρlip
      id id (contDiff_id : ContDiff ℝ (⊤ : ℕ∞) (id : (ι → ℝ) → (ι → ℝ)))
      (contDiff_id : ContDiff ℝ (⊤ : ℕ∞) (id : (ι → ℝ) → (ι → ℝ)))
      (fun x => rfl) (fun y => rfl) (fun i x => rfl) b hb hbp (s + 2 * k - 1)
  -- ## Injectivity and non-vanishing Jacobian of `T`, `T'`
  have hinjT : Function.Injective T := fun x y hxy => by rw [← hTinv1 x, hxy, hTinv1 y]
  have hinjT' : Function.Injective T' := fun x y hxy => by rw [← hTinv2 x, hxy, hTinv2 y]
  have hdet_of : ∀ (A B : (ι → ℝ) →L[ℝ] (ι → ℝ)), A.comp B = 1 → B.det ≠ 0 := by
    intro A B hcomp hz
    have hinj : Function.Injective B := fun u v huv => by
      have h1 := congrArg (fun (Lh : (ι → ℝ) →L[ℝ] (ι → ℝ)) => Lh u) hcomp
      have h2 := congrArg (fun (Lh : (ι → ℝ) →L[ℝ] (ι → ℝ)) => Lh v) hcomp
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at h1 h2
      rw [huv] at h1
      exact h1.symm.trans h2
    have hz' : LinearMap.det ((B : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))) = 0 := hz
    exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hz') (by rw [LinearMap.ker_eq_bot]; exact hinj)
  have hdetT : ∀ z : ι → ℝ, (fderiv ℝ T z).det ≠ 0 := by
    intro z
    have hcomp : fderiv ℝ (fun x => T' (T x)) z = (fderiv ℝ T' (T z)).comp (fderiv ℝ T z) :=
      fderiv_comp z ((hT'.differentiable (by simp)).differentiableAt)
        ((hT.differentiable (by simp)).differentiableAt)
    have h1 : fderiv ℝ (fun x => T' (T x)) z = 1 := by
      rw [show (fun x : ι → ℝ => T' (T x)) = id from funext hTinv1]
      exact fderiv_id
    have h2 : (fderiv ℝ T' (T z)).comp (fderiv ℝ T z) = 1 := by rw [← hcomp]; exact h1
    exact hdet_of _ _ h2
  have hdetT' : ∀ z : ι → ℝ, (fderiv ℝ T' z).det ≠ 0 := by
    intro z
    have hcomp : fderiv ℝ (fun y => T (T' y)) z = (fderiv ℝ T (T' z)).comp (fderiv ℝ T' z) :=
      fderiv_comp z ((hT.differentiable (by simp)).differentiableAt)
        ((hT'.differentiable (by simp)).differentiableAt)
    have h1 : fderiv ℝ (fun y => T (T' y)) z = 1 := by
      rw [show (fun y : ι → ℝ => T (T' y)) = id from funext hTinv2]
      exact fderiv_id
    have h2 : (fderiv ℝ T (T' z)).comp (fderiv ℝ T' z) = 1 := by rw [← hcomp]; exact h1
    exact hdet_of _ _ h2
  obtain ⟨K, hK0, hK⟩ :=
    Work.Diff.STE.B3.SymCalcStep6.conjLapPow_CSq_le T T' hT hT' hTper hTinv1 hTinv2
      hinjT hinjT' hdetT hdetT' k s
  refine ⟨2 * (Ca * (K * Cb) + C2), ?_, ?_⟩
  · exact mul_nonneg (by norm_num) (add_nonneg (mul_nonneg hCa0 (mul_nonneg hK0 hCb0)) hC20)
  intro ε hε hε1 g hg hgp
  -- ## Abbreviations for the two cutoff operators
  let S : ((ι → ℝ) → ℂ) → (ι → ℝ) → ℂ := fun u => Work.Diff.STE.B3.SymCalc.flatCut ρ ε u
  let P : ((ι → ℝ) → ℂ) → (ι → ℝ) → ℂ :=
    fun u => Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' u
  have hSsm : ∀ u : (ι → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) u → Work.Diff.STE.Periodic1 u →
      ContDiff ℝ (⊤ : ℕ∞) (S u) :=
    fun u hu hup => Work.Diff.STE.B3.SymCalcStep1.flatCut_contDiff ρ hρ ε hu hup
  have hSp : ∀ u : (ι → ℝ) → ℂ, Work.Diff.STE.Periodic1 (S u) :=
    fun u => Work.Diff.STE.B3.SymCalcStep1.flatCut_periodic ρ ε u
  have hPsm : ∀ u : (ι → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) u → Work.Diff.STE.Periodic1 u →
      ContDiff ℝ (⊤ : ℕ∞) (P u) :=
    fun u hu hup =>
      Work.Diff.STE.B3.SymCalcStep6.conjLapPow_contDiff T T' hT hT' hTper hTinv1 hTinv2 k hu hup
  have hPp : ∀ u : (ι → ℝ) → ℂ, Work.Diff.STE.Periodic1 (P u) :=
    fun u => Work.Diff.STE.B3.SymCalcStep6.conjLapPow_periodic T T' hTper k u
  -- ## `conjCut ρ ε id id = S`
  have hcid : ∀ w : (ι → ℝ) → ℂ, Work.Diff.STE.B3.SymCalc.conjCut ρ ε id id w = S w := by
    intro w
    rfl
  -- ## The multiplier commutator `u = [M_b, S] g`
  let uf : (ι → ℝ) → ℂ := fun y => b y * S g y - S (fun y => b y * g y) y
  have hbsm : ContDiff ℝ (⊤ : ℕ∞) (fun y => b y * S g y) := hb.mul (hSsm g hg hgp)
  have hbp' : Work.Diff.STE.Periodic1 (fun y => b y * S g y) :=
    Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hbp (hSp g)
  have hbgsm : ContDiff ℝ (⊤ : ℕ∞) (fun y => b y * g y) := hb.mul hg
  have hbgp : Work.Diff.STE.Periodic1 (fun y => b y * g y) :=
    Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hbp hgp
  have hSbgp : Work.Diff.STE.Periodic1 (S (fun y => b y * g y)) := hSp (fun y => b y * g y)
  have hSbg_sm : ContDiff ℝ (⊤ : ℕ∞) (S (fun y => b y * g y)) :=
    hSsm (fun y => b y * g y) hbgsm hbgp
  have huf_sm : ContDiff ℝ (⊤ : ℕ∞) uf := hbsm.sub hSbg_sm
  have huf_p : Work.Diff.STE.Periodic1 uf :=
    Work.Diff.STE.B3.SymCalcStep1.Periodic1_sub' hbp' hSbgp
  have hPuf_sm : ContDiff ℝ (⊤ : ℕ∞) (P uf) := hPsm uf huf_sm huf_p
  have hPuf_p : Work.Diff.STE.Periodic1 (P uf) := hPp uf
  -- ## The subtraction identity for `P`
  have hPu : P uf = P (fun y => b y * S g y) - P (S (fun y => b y * g y)) :=
    Work.Diff.STE.B3.SymCalcStep7.conjLapPow_sub T T' hT' hTper hTinv1 hTinv2 k
      (u := fun y => b y * S g y) (v := S (fun y => b y * g y))
      hbsm hSbg_sm hbp' hSbgp
  -- ## The two pieces `Y` and `Z`
  set YF : (ι → ℝ) → ℂ := (fun x => a x * P uf x) with hYF
  let hb4 : (ι → ℝ) → ℂ := fun y => b y * g y
  let B1 : (ι → ℝ) → ℂ := fun x => b x * (S (P g) x - P (S g) x)
  let B2 : (ι → ℝ) → ℂ := fun x => b x * P (S g) x - P (fun y => b y * S g y) x
  let B3 : (ι → ℝ) → ℂ := fun x => S (fun y => b y * P g y) x - S (P hb4) x
  let B4 : (ι → ℝ) → ℂ := fun x => S (P hb4) x - P (S hb4) x
  let A1 : (ι → ℝ) → ℂ := a * B1
  let A2 : (ι → ℝ) → ℂ := a * B2
  let A3 : (ι → ℝ) → ℂ := a * B3
  let A4 : (ι → ℝ) → ℂ := a * B4
  set ZF : (ι → ℝ) → ℂ := (fun x => a x * (
        (b x * (Work.Diff.STE.B3.SymCalc.flatCut ρ ε
              (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' g) x
            - Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
              (Work.Diff.STE.B3.SymCalc.flatCut ρ ε g) x))
        + (b x * Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
              (Work.Diff.STE.B3.SymCalc.flatCut ρ ε g) x
            - Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
              (fun y => b y * Work.Diff.STE.B3.SymCalc.flatCut ρ ε g y) x)
        - (Work.Diff.STE.B3.SymCalc.flatCut ρ ε
              (fun y => b y * Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' g y) x
            - Work.Diff.STE.B3.SymCalc.flatCut ρ ε
              (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
                (fun y => b y * g y)) x)
        - (Work.Diff.STE.B3.SymCalc.flatCut ρ ε
              (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
                (fun y => b y * g y)) x
            - Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
              (Work.Diff.STE.B3.SymCalc.flatCut ρ ε (fun y => b y * g y)) x))) with hZF
  -- ## Smoothness and periodicity of `Y`
  have hYFsm : ContDiff ℝ (⊤ : ℕ∞) YF := by
    rw [hYF]
    exact ha.mul hPuf_sm
  have hYFp : Work.Diff.STE.Periodic1 YF := by
    rw [hYF]
    exact Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hap hPuf_p
  -- ## Smoothness and periodicity of `Z`, via the four-summand expansion
  have hb4sm : ContDiff ℝ (⊤ : ℕ∞) hb4 := hb.mul hg
  have hb4p : Work.Diff.STE.Periodic1 hb4 :=
    Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hbp hgp
  have hB1sm : ContDiff ℝ (⊤ : ℕ∞) B1 :=
    hb.mul ((hSsm (P g) (hPsm g hg hgp) (hPp g)).sub (hPsm (S g) (hSsm g hg hgp) (hSp g)))
  have hB1p : Work.Diff.STE.Periodic1 B1 :=
    Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hbp
      (Work.Diff.STE.B3.SymCalcStep1.Periodic1_sub' (hSp (P g)) (hPp (S g)))
  have hB2sm : ContDiff ℝ (⊤ : ℕ∞) B2 :=
    (hb.mul (hPsm (S g) (hSsm g hg hgp) (hSp g))).sub
      (hPsm (fun y => b y * S g y) hbsm hbp')
  have hB2p : Work.Diff.STE.Periodic1 B2 :=
    Work.Diff.STE.B3.SymCalcStep1.Periodic1_sub'
      (Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hbp (hPp (S g))) (hPp (fun y => b y * S g y))
  have hB3sm : ContDiff ℝ (⊤ : ℕ∞) B3 :=
    (hSsm (fun y => b y * P g y) (hb.mul (hPsm g hg hgp))
        (Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hbp (hPp g))).sub
      (hSsm (P hb4) (hPsm hb4 hb4sm hb4p) (hPp hb4))
  have hB3p : Work.Diff.STE.Periodic1 B3 :=
    Work.Diff.STE.B3.SymCalcStep1.Periodic1_sub'
      (hSp (fun y => b y * P g y)) (hSp (P hb4))
  have hB4sm : ContDiff ℝ (⊤ : ℕ∞) B4 :=
    (hSsm (P hb4) (hPsm hb4 hb4sm hb4p) (hPp hb4)).sub
      (hPsm (S hb4) (hSsm hb4 hb4sm hb4p) (hSp hb4))
  have hB4p : Work.Diff.STE.Periodic1 B4 :=
    Work.Diff.STE.B3.SymCalcStep1.Periodic1_sub' (hSp (P hb4)) (hPp (S hb4))
  have hA1sm : ContDiff ℝ (⊤ : ℕ∞) A1 := ha.mul hB1sm
  have hA1p : Work.Diff.STE.Periodic1 A1 :=
    Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hap hB1p
  have hA2sm : ContDiff ℝ (⊤ : ℕ∞) A2 := ha.mul hB2sm
  have hA2p : Work.Diff.STE.Periodic1 A2 :=
    Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hap hB2p
  have hA3sm : ContDiff ℝ (⊤ : ℕ∞) A3 := ha.mul hB3sm
  have hA3p : Work.Diff.STE.Periodic1 A3 :=
    Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hap hB3p
  have hA4sm : ContDiff ℝ (⊤ : ℕ∞) A4 := ha.mul hB4sm
  have hA4p : Work.Diff.STE.Periodic1 A4 :=
    Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hap hB4p
  have hZFsum : ZF = fun x : ι → ℝ => A1 x + A2 x - A3 x - A4 x := by
    rw [hZF]
    funext x
    simp only [A1, A2, A3, A4, B1, B2, B3, B4, S, P, hb4, Pi.add_apply, Pi.sub_apply,
      Pi.mul_apply]
    ring
  have hZFsm : ContDiff ℝ (⊤ : ℕ∞) ZF := by
    rw [hZFsum]
    exact ((hA1sm.add hA2sm).sub hA3sm).sub hA4sm
  have hZFp : Work.Diff.STE.Periodic1 ZF := by
    rw [hZFsum]
    exact Work.Diff.STE.B3.SymCalcStep1.Periodic1_sub'
      (Work.Diff.STE.B3.SymCalcStep1.Periodic1_sub'
        (Work.Diff.STE.B3.SymCalcStep1.Periodic1_add' hA1p hA2p) hA3p) hA4p
  -- ## The pointwise splitting `X = Y + Z`
  have hsplit : (fun x : ι → ℝ => a x * (b x * Work.Diff.STE.B3.SymCalc.flatCut ρ ε
          (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' g) x
        - Work.Diff.STE.B3.SymCalc.flatCut ρ ε
          (fun y => b y * Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' g y) x))
      = fun x : ι → ℝ => YF x + ZF x := by
    rw [hYF, hZF]
    funext x
    dsimp only
    rw [hPu]
    simp only [S, P, Pi.sub_apply]
    ring
  -- ## Piece (i): the gain before `P`, then the order-`2k` cost of `P`
  have hCb' : Work.Diff.STE.CSq (s + 2 * k) (Work.Diff.STE.fourierCoeff uf)
      ≤ Cb * Work.Diff.STE.CSq (s + 2 * k - 1) (Work.Diff.STE.fourierCoeff g) := by
    have h := hCb ε hε hε1 g hg hgp
    have hidx : s + 2 * k - 1 + 1 = s + 2 * k := by omega
    have hfun : (fun x : ι → ℝ => b x * Work.Diff.STE.B3.SymCalc.conjCut ρ ε id id g x
          - Work.Diff.STE.B3.SymCalc.conjCut ρ ε id id (fun y => b y * g y) x) = uf := by
      funext x
      simp only [uf]
      rw [hcid g, hcid (fun y => b y * g y)]
    rw [hfun, hidx] at h
    exact h
  have hY : Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff YF)
      ≤ (Ca * (K * Cb)) * Work.Diff.STE.CSq (s + 2 * k - 1) (Work.Diff.STE.fourierCoeff g) := by
    rw [hYF]
    calc Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun x : ι → ℝ => a x * P uf x))
        ≤ Ca * Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (P uf)) :=
          hCa (P uf) hPuf_sm hPuf_p
      _ ≤ Ca * (K * Work.Diff.STE.CSq (s + 2 * k) (Work.Diff.STE.fourierCoeff uf)) :=
          mul_le_mul_of_nonneg_left (hK uf huf_sm huf_p) hCa0
      _ ≤ Ca * (K * (Cb * Work.Diff.STE.CSq (s + 2 * k - 1) (Work.Diff.STE.fourierCoeff g))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hCb' hK0) hCa0
      _ = (Ca * (K * Cb)) * Work.Diff.STE.CSq (s + 2 * k - 1)
            (Work.Diff.STE.fourierCoeff g) := by ring
  -- ## Piece (ii): the double commutator
  have hZ : Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff ZF)
      ≤ C2 * Work.Diff.STE.CSq (s + 2 * k - 1) (Work.Diff.STE.fourierCoeff g) := by
    rw [hZF]
    exact hC2 ε hε hε1 g hg hgp
  -- ## Assembly
  have hfc : Work.Diff.STE.fourierCoeff (fun x : ι → ℝ => YF x + ZF x)
      = fun m : ι → ℤ => Work.Diff.STE.fourierCoeff YF m
          + Work.Diff.STE.fourierCoeff ZF m := by
    funext m
    exact Work.Diff.STE.B3.SymCalcStep1.fourierCoeff_add_of_continuous YF ZF
      hYFsm.continuous hZFsm.continuous m
  calc Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun x => a x *
          (b x * Work.Diff.STE.B3.SymCalc.flatCut ρ ε
              (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' g) x
            - Work.Diff.STE.B3.SymCalc.flatCut ρ ε
              (fun y => b y * Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' g y) x)))
      = Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun x : ι → ℝ => YF x + ZF x)) := by
        rw [hsplit]
    _ = Work.Diff.STE.CSq s (fun m : ι → ℤ => Work.Diff.STE.fourierCoeff YF m
          + Work.Diff.STE.fourierCoeff ZF m) := by rw [hfc]
    _ ≤ 2 * (Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff YF)
          + Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff ZF)) :=
        Work.Diff.STE.B3.SymCalcStep1.CSq_add_le s _ _
          (Work.Diff.STE.B3.SymCalcStep1.summable_CSq_fourierCoeff s hYFsm hYFp)
          (Work.Diff.STE.B3.SymCalcStep1.summable_CSq_fourierCoeff s hZFsm hZFp)
    _ ≤ 2 * ((Ca * (K * Cb)) * Work.Diff.STE.CSq (s + 2 * k - 1)
            (Work.Diff.STE.fourierCoeff g)
          + C2 * Work.Diff.STE.CSq (s + 2 * k - 1) (Work.Diff.STE.fourierCoeff g)) := by
        linarith [hY, hZ]
    _ = (2 * (Ca * (K * Cb) + C2)) * Work.Diff.STE.CSq (s + 2 * k - 1)
          (Work.Diff.STE.fourierCoeff g) := by ring

end Work.Diff.STE.B3.SymCalcStep7
