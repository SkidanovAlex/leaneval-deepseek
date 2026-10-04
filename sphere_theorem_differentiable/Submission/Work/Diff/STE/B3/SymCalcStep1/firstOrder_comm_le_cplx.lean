import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.B3.SymCalc
import Submission.Work.Diff.STE.B3.SymCalcStep1.friedrichs_commutator_supp
import Submission.Work.Diff.STE.B3.SymCalcStep1.firstOrder_comm_trunc_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3.SymCalcStep1

/-!
# The first-order commutator estimate with a **complex** multiplier

This is the complex-coefficient form of `firstOrder_comm_trunc_le`, and it is the shape in which
the order reduction of the symbol-calculus layer is actually consumed: for the Friedrichs cutoff
`S_ε = flatCut ρ ε` and a smooth `1`-periodic **complex** multiplier `M`, the commutator

  `[M · ∂_p, S_ε] u = M · ∂_p (S_ε u) − S_ε (M · ∂_p u)`

is bounded on `H^s` **uniformly in `ε ∈ (0,1]`** (its naive order is one, the commutator has
order zero).

Two differences with `firstOrder_comm_trunc_le` are worth recording.

* The multiplier is complex valued and only *one* partial derivative `∂_p` occurs, so no finite
  sum over `ι` is taken and no `card ι` factor appears.
* There is **no** hypothesis `ρ 0 = 1` (and no bound on `M` resp. on `∂M`) in the statement.  The
  profile hypotheses are only `‖ρ‖ ≤ 1`, the support condition
  `2 < Σ yᵢ² ⟹ ρ y = 0` and Lipschitz continuity — exactly the hypotheses under which the
  coefficient-level Friedrichs commutator `friedrichs_commutator_supp` is proved (the identity
  case `ρ 0 = 1` is never used in the Friedrichs commutator argument: the pointwise increment
  `|ρ (εm) − ρ (εk)|` is bounded by `min 2 (L ε ‖m − k‖)` together with the support of the
  difference, which forces `min ⟨m⟩ ⟨k⟩ ≲ 1/ε`).  The boundedness of `M` and of its derivatives
  is *not* assumed either: smoothness and periodicity alone give rapid decay of `fourierCoeff M`,
  which is all the estimate uses.

The proof is on the Fourier side and follows `firstOrder_comm_trunc_le` with the finite sum
removed.  With `c = û`, `σ = trunc ρ ε c = Û(S_ε u)` and `D = ẐM`, the product rule
`fourierCoeff (M · seriesFun c) = conv c D`, the multiplier identity
`pd p (seriesFun c) = seriesFun (dmul p c)` and its commutation with the cutoff
`dmul p (trunc ρ ε c) = trunc ρ ε (dmul p c)` give the *exact* identity

  `fourierCoeff ([M ∂_p, S_ε] u) k = conv D (trunc ρ ε (dmul p c)) k − trunc ρ ε (conv D (dmul p c)) k`,

which is precisely the family of `friedrichs_commutator_supp` (no order is lost there because the
derivative `dmul p` is already inside).
-/

theorem firstOrder_comm_le_cplx
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : (ι → ℝ) → ℝ)
    (hρb : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (hdiam : ∀ y : ι → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (L : ℝ) (hL : 0 ≤ L) (hρlip : ∀ y z : ι → ℝ, ‖ρ y - ρ z‖ ≤ L * ‖y - z‖)
    (M : (ι → ℝ) → ℂ) (hMsm : ContDiff ℝ (⊤ : ℕ∞) M) (hMper : Work.Diff.STE.Periodic1 M)
    (p : ι) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ u : (ι → ℝ) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) u → Work.Diff.STE.Periodic1 u →
      Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun x =>
          M x * Work.Diff.STE.pd p (Work.Diff.STE.B3.SymCalc.flatCut ρ ε u) x
            - Work.Diff.STE.B3.SymCalc.flatCut ρ ε (fun x => M x * Work.Diff.STE.pd p u x) x))
        ≤ C * Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff u) := by
  classical
  -- ## Step 0: the coefficient-level Friedrichs commutator (one order gain, `ε`-uniform)
  have hDl1 : ∀ N : ℕ, Summable (fun k : ι → ℤ =>
      (Work.Diff.STE.wt k) ^ N * ‖Work.Diff.STE.fourierCoeff M k‖) :=
    fun N => summable_wt_pow_mul_fourierCoeff N M hMsm hMper
  obtain ⟨C, hCnn, hC⟩ := friedrichs_commutator_supp ρ hρb hdiam L hL hρlip
    (Work.Diff.STE.fourierCoeff M) hDl1 s p
  refine ⟨C, hCnn, ?_⟩
  intro ε hε hε1 u hu huper
  -- ## Step 1: the coefficient families and their weighted summability
  set c : (ι → ℤ) → ℂ := Work.Diff.STE.fourierCoeff u with hc
  set σ : (ι → ℤ) → ℂ := Work.Diff.STE.trunc ρ ε c with hσ
  have hcl1 : ∀ N : ℕ, Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ N * ‖c k‖) := by
    intro N
    rw [hc]
    exact summable_wt_pow_mul_fourierCoeff N u hu huper
  have hCsq : Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s * ‖c k‖ ^ 2) := by
    rw [hc]
    exact Work.Diff.STE.Comp.summable_wt_fourierCoeff s u
      (hu.of_le (WithTop.coe_le_coe.mpr le_top)) huper
  have hσl1 : ∀ N : ℕ, Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ N * ‖σ k‖) := by
    intro N
    refine Summable.of_nonneg_of_le
      (fun k => mul_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) N) (norm_nonneg _))
      (fun k => mul_le_mul_of_nonneg_left (norm_trunc_le ρ hρb ε c k)
        (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) N)) (hcl1 N)
  have hwc : Summable (fun k : ι → ℤ => 2 * Real.pi * (Work.Diff.STE.wt k * ‖c k‖)) :=
    ((hcl1 1).congr (fun k => by rw [pow_one])).mul_left (2 * Real.pi)
  have hdmulc : Summable (fun k : ι → ℤ => ‖Work.Diff.STE.dmul p c k‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => norm_dmul_le_wt p c k) hwc
  have hdmulσ : Summable (fun k : ι → ℤ => ‖Work.Diff.STE.dmul p σ k‖) := by
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) hwc
    calc ‖Work.Diff.STE.dmul p σ k‖ ≤ 2 * Real.pi * (Work.Diff.STE.wt k * ‖σ k‖) :=
          norm_dmul_le_wt p σ k
      _ ≤ 2 * Real.pi * (Work.Diff.STE.wt k * ‖c k‖) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left (norm_trunc_le ρ hρb ε c k)
            (le_of_lt (Work.Diff.STE.wt_pos k))
  -- ## Step 2: the series identities
  have hflat : Work.Diff.STE.B3.SymCalc.flatCut ρ ε u = Work.Diff.STE.seriesFun σ := by
    simp only [Work.Diff.STE.B3.SymCalc.flatCut, hσ, hc]
  have huser : ∀ x : ι → ℝ, Work.Diff.STE.seriesFun c x = u x := by
    intro x
    rw [hc]
    exact Work.Diff.STE.flat.seriesFun_fourierCoeff u hu huper x
  have hpdσ : Work.Diff.STE.pd p (Work.Diff.STE.B3.SymCalc.flatCut ρ ε u)
      = Work.Diff.STE.seriesFun (Work.Diff.STE.dmul p σ) := funext fun x => by
    rw [hflat]
    exact Work.Diff.STE.pd_seriesFun p σ hσl1 x
  have hpdu : Work.Diff.STE.pd p u = Work.Diff.STE.seriesFun (Work.Diff.STE.dmul p c) :=
    funext fun x => by
      rw [show u = Work.Diff.STE.seriesFun c from funext fun x => (huser x).symm]
      exact Work.Diff.STE.pd_seriesFun p c hcl1 x
  -- ## Step 3: `M · ∂_p (S_ε u)` and its Fourier coefficients
  have hMcont : Continuous M := hMsm.continuous
  have hMint : MeasureTheory.Integrable M
      (MeasureTheory.volume.restrict (Work.Diff.STE.unitCube (ι := ι))) :=
    Work.Diff.STE.integrableOn_unitCube_of_continuous hMcont
  have hcont1 : Continuous (fun x : ι → ℝ =>
      M x * Work.Diff.STE.pd p (Work.Diff.STE.B3.SymCalc.flatCut ρ ε u) x) := by
    have hEq : (fun x : ι → ℝ =>
          M x * Work.Diff.STE.pd p (Work.Diff.STE.B3.SymCalc.flatCut ρ ε u) x)
        = fun x : ι → ℝ => M x * Work.Diff.STE.seriesFun (Work.Diff.STE.dmul p σ) x :=
      funext fun x => congrArg (fun g => M x * g x) hpdσ
    rw [hEq]
    exact hMcont.mul (Work.Diff.STE.flat.continuous_seriesFun_of_summable _ hdmulσ)
  have hF1 : ∀ k : ι → ℤ, Work.Diff.STE.fourierCoeff (fun x : ι → ℝ =>
      M x * Work.Diff.STE.pd p (Work.Diff.STE.B3.SymCalc.flatCut ρ ε u) x) k
      = Work.Diff.STE.conv (Work.Diff.STE.fourierCoeff M)
          (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.dmul p c)) k := by
    intro k
    have hEq : (fun x : ι → ℝ =>
          M x * Work.Diff.STE.pd p (Work.Diff.STE.B3.SymCalc.flatCut ρ ε u) x)
        = fun x : ι → ℝ => M x * Work.Diff.STE.seriesFun (Work.Diff.STE.dmul p σ) x :=
      funext fun x => congrArg (fun g => M x * g x) hpdσ
    rw [hEq, Work.Diff.STE.fourierCoeff_mul_seriesFun M (Work.Diff.STE.dmul p σ) k hMint hdmulσ,
      conv_comm (Work.Diff.STE.dmul p σ) (Work.Diff.STE.fourierCoeff M) k]
    refine congrArg (fun v => Work.Diff.STE.conv (Work.Diff.STE.fourierCoeff M) v k) ?_
    rw [hσ]
    exact trunc_dmul ρ ε p c
  -- ## Step 4: `S_ε (M · ∂_p u)` and its Fourier coefficients
  have he_eq : Work.Diff.STE.fourierCoeff (fun x : ι → ℝ => M x * Work.Diff.STE.pd p u x)
      = Work.Diff.STE.conv (Work.Diff.STE.fourierCoeff M) (Work.Diff.STE.dmul p c) := by
    funext k
    have hEq : (fun x : ι → ℝ => M x * Work.Diff.STE.pd p u x)
        = fun x : ι → ℝ => M x * Work.Diff.STE.seriesFun (Work.Diff.STE.dmul p c) x :=
      funext fun x => congrArg (fun g => M x * g x) hpdu
    rw [hEq, Work.Diff.STE.fourierCoeff_mul_seriesFun M (Work.Diff.STE.dmul p c) k hMint hdmulc]
    exact conv_comm (Work.Diff.STE.dmul p c) (Work.Diff.STE.fourierCoeff M) k
  have hG_eq : Work.Diff.STE.B3.SymCalc.flatCut ρ ε (fun x => M x * Work.Diff.STE.pd p u x)
      = Work.Diff.STE.seriesFun (Work.Diff.STE.trunc ρ ε
          (Work.Diff.STE.conv (Work.Diff.STE.fourierCoeff M) (Work.Diff.STE.dmul p c))) := by
    rw [Work.Diff.STE.B3.SymCalc.flatCut]
    rw [he_eq]
  have hel1 : Summable (fun k : ι → ℤ =>
      ‖Work.Diff.STE.conv (Work.Diff.STE.fourierCoeff M) (Work.Diff.STE.dmul p c) k‖) :=
    Work.Diff.STE.summable_conv_norm (Work.Diff.STE.fourierCoeff M) (Work.Diff.STE.dmul p c)
      ((hDl1 0).congr (fun k => by rw [pow_zero, one_mul])) hdmulc
  have htel1 : Summable (fun k : ι → ℤ => ‖Work.Diff.STE.trunc ρ ε
      (Work.Diff.STE.conv (Work.Diff.STE.fourierCoeff M) (Work.Diff.STE.dmul p c)) k‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _)
      (fun k => norm_trunc_le ρ hρb ε
        (Work.Diff.STE.conv (Work.Diff.STE.fourierCoeff M) (Work.Diff.STE.dmul p c)) k) hel1
  have hcont2 : Continuous (Work.Diff.STE.B3.SymCalc.flatCut ρ ε
      (fun x => M x * Work.Diff.STE.pd p u x)) := by
    rw [hG_eq]
    exact Work.Diff.STE.flat.continuous_seriesFun_of_summable _ htel1
  have hG1 : ∀ k : ι → ℤ, Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.SymCalc.flatCut ρ ε
      (fun x => M x * Work.Diff.STE.pd p u x)) k
      = Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv (Work.Diff.STE.fourierCoeff M)
          (Work.Diff.STE.dmul p c)) k := by
    intro k
    rw [hG_eq]
    exact Work.Diff.STE.flat.fourierCoeff_seriesFun _ htel1 k
  -- ## Step 5: the exact identity for the Fourier coefficients of the commutator
  have hcoe : Work.Diff.STE.fourierCoeff (fun x : ι → ℝ =>
        M x * Work.Diff.STE.pd p (Work.Diff.STE.B3.SymCalc.flatCut ρ ε u) x
          - Work.Diff.STE.B3.SymCalc.flatCut ρ ε (fun x => M x * Work.Diff.STE.pd p u x) x)
      = fun k => Work.Diff.STE.conv (Work.Diff.STE.fourierCoeff M)
            (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.dmul p c)) k
          - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv (Work.Diff.STE.fourierCoeff M)
            (Work.Diff.STE.dmul p c)) k := by
    funext k
    have hsub := Work.Diff.STE.flat.fourierCoeff_sub_of_continuous
      (fun x : ι → ℝ => M x * Work.Diff.STE.pd p (Work.Diff.STE.B3.SymCalc.flatCut ρ ε u) x)
      (fun x : ι → ℝ => Work.Diff.STE.B3.SymCalc.flatCut ρ ε
        (fun x => M x * Work.Diff.STE.pd p u x) x) hcont1 hcont2 k
    rw [hF1 k, hG1 k] at hsub
    exact hsub
  -- ## Step 6: the estimate
  rw [hcoe]
  exact hC ε hε hε1 c hCsq

end Work.Diff.STE.B3.SymCalcStep1
