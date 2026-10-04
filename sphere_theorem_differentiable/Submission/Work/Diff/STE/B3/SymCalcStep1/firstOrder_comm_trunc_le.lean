import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.B3.SymCalc
import Submission.Work.Diff.STE.Comp.summable_wt_fourierCoeff
import Submission.Work.Diff.STE.summable_norm_of_CSq
import Submission.Work.Diff.STE.flat.seriesFun_fourierCoeff
import Submission.Work.Diff.STE.flat.fourierCoeff_seriesFun
import Submission.Work.Diff.STE.pd_seriesFun
import Submission.Work.Diff.STE.fourierCoeff_mul_seriesFun
import Submission.Work.Diff.STE.summable_conv_norm
import Submission.Work.Diff.STE.CSq_trunc_le
import Submission.Work.Diff.STE.B3.SymCalcStep1.friedrichs_commutator_supp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3.SymCalcStep1

/-!
# Step 1 of the symbol calculus: the first-order commutator estimate

`firstOrder_comm_trunc_le` is the function-level form of the order reduction: for the first-order
operator `P g = Σᵢ Mᵢ · ∂ᵢ g` with smooth `1`-periodic coefficients `Mᵢ` and the Friedrichs cutoff
`S_ε = flatCut ρ ε`, the commutator `[P, S_ε]` has order `0`, uniformly in `ε ∈ (0,1]`:

  `CSq s (fourierCoeff ([P,S_ε] g)) ≤ C · CSq s (fourierCoeff g)`.

Everything is done on the Fourier side.  With `c = û`, `σ = trunc ρ ε c` (the coefficient family of
`S_ε g`) and `Dᵢ = ûᵢ` (that of `Mᵢ`), the product rule
`fourierCoeff (f · seriesFun c) = conv c (fourierCoeff f)`, the multiplier identity
`pd i (seriesFun c) = seriesFun (dmul i c)` and `dmul i (trunc ρ ε c) = trunc ρ ε (dmul i c)` give
the *exact* identity

  `fourierCoeff ([P,S_ε] g) = fun k => Σᵢ (conv (Dᵢ) (trunc ρ ε (dmul i c)) k
                                        - trunc ρ ε (conv (Dᵢ) (dmul i c)) k)`,

the sum over `i` of coefficient-level Friedrichs commutators.  For those the one-order-gain estimate
`friedrichs_commutator_supp` (support-only form of the profile) gives, uniformly in `ε`,
`CSq s ≤ Cᵢ · CSq s c`; the finite sum over `i` costs `card ι`, and the summability needed to
interchange `∑'` with that finite sum comes from `CSq_conv_le` at the level `s + s₀`.

Note the convention of `wt`: `wt k = ⟨k⟩² = 1 + Σ kᵢ²`, so `CSq s` is the square of the `Hˢ` norm.
-/

/-- `ℓ¹`-summability with an arbitrary weight `⟨k⟩^{2N}` of the Fourier coefficients of a smooth
`1`-periodic function: `Σ_k ⟨k⟩^{2N} ‖û(k)‖ < ∞`.  Obtained from the weighted `ℓ²` summability
(`Comp.summable_wt_fourierCoeff`) and `summable_norm_of_CSq` at a level with `card ι < 2 s₀`. -/
lemma summable_wt_pow_mul_fourierCoeff {ι : Type*} [Fintype ι] [DecidableEq ι] (N : ℕ)
    (f : (ι → ℝ) → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hper : Work.Diff.STE.Periodic1 f) :
    Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ N * ‖Work.Diff.STE.fourierCoeff f k‖) := by
  obtain ⟨s0, hs0⟩ : ∃ s0 : ℕ, Fintype.card ι < 2 * s0 := ⟨Fintype.card ι + 1, by omega⟩
  have hf' : ContDiff ℝ ((s0 + 2 * N : ℕ) : ℕ∞) f := hf.of_le (WithTop.coe_le_coe.mpr le_top)
  have hnrm : ∀ k : ι → ℤ, ‖(Work.Diff.STE.wt k : ℂ)‖ = Work.Diff.STE.wt k := fun k =>
    Complex.norm_of_nonneg (le_of_lt (Work.Diff.STE.wt_pos k))
  have hcsq : Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s0
      * ‖(Work.Diff.STE.wt k : ℂ) ^ N * Work.Diff.STE.fourierCoeff f k‖ ^ 2) := by
    refine (Work.Diff.STE.Comp.summable_wt_fourierCoeff (s0 + 2 * N) f hf' hper).congr
      (fun k => ?_)
    rw [norm_mul, norm_pow, hnrm k]
    ring
  have hfin := Work.Diff.STE.summable_norm_of_CSq s0 hs0
    (fun k : ι → ℤ => (Work.Diff.STE.wt k : ℂ) ^ N * Work.Diff.STE.fourierCoeff f k) hcsq
  refine hfin.congr (fun k => ?_)
  rw [norm_mul, norm_pow, hnrm k]

/-- Complexification preserves `C^∞`-smoothness. -/
lemma contDiff_ofReal_comp {ι : Type*} [Fintype ι] (M : (ι → ℝ) → ℝ)
    (hM : ContDiff ℝ (⊤ : ℕ∞) M) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : ι → ℝ => ((M x : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp hM

/-- Complexification preserves `1`-periodicity. -/
lemma periodic1_ofReal {ι : Type*} [DecidableEq ι] {M : (ι → ℝ) → ℝ}
    (h : Work.Diff.STE.Periodic1 M) :
    Work.Diff.STE.Periodic1 (fun x : ι → ℝ => ((M x : ℝ) : ℂ)) := by
  intro i x
  show ((M (x + Pi.single i 1) : ℝ) : ℂ) = ((M x : ℝ) : ℂ)
  rw [h i x]

/-- The convolution of coefficient families is commutative (reindex `l ↦ k - l`). -/
lemma conv_comm {ι : Type*} [Fintype ι] [DecidableEq ι] (u v : (ι → ℤ) → ℂ) (k : ι → ℤ) :
    Work.Diff.STE.conv u v k = Work.Diff.STE.conv v u k := by
  let e : (ι → ℤ) ≃ (ι → ℤ) :=
    { toFun := fun l => k - l
      invFun := fun m => k - m
      left_inv := fun l => by simp
      right_inv := fun m => by simp }
  rw [Work.Diff.STE.conv, Work.Diff.STE.conv,
    ← Equiv.tsum_eq e (fun m => v m * u (k - m))]
  refine tsum_congr fun l => ?_
  have h1 : e l = k - l := rfl
  rw [h1, show k - (k - l) = l by abel]
  ring

/-- The Fourier multiplier of `∂ᵢ` commutes with the Friedrichs cutoff. -/
lemma trunc_dmul {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : (ι → ℝ) → ℝ) (ε : ℝ)
    (i : ι) (c : (ι → ℤ) → ℂ) :
    Work.Diff.STE.dmul i (Work.Diff.STE.trunc ρ ε c) = Work.Diff.STE.trunc ρ ε
      (Work.Diff.STE.dmul i c) := by
  funext k
  simp only [Work.Diff.STE.dmul, Work.Diff.STE.trunc]
  ring

/-- Linearity of `fourierCoeff` over a finite sum. -/
lemma fourierCoeff_fintype_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ι → (ι → ℝ) → ℂ) (k : ι → ℤ)
    (hF : ∀ i, MeasureTheory.Integrable (fun x => Work.Diff.STE.fourierExp (-k) x * F i x)
      (MeasureTheory.volume.restrict (Work.Diff.STE.unitCube (ι := ι)))) :
    Work.Diff.STE.fourierCoeff (fun x => ∑ i, F i x) k
      = ∑ i, Work.Diff.STE.fourierCoeff (F i) k := by
  simp only [Work.Diff.STE.fourierCoeff]
  have hpt : ∀ x : ι → ℝ, Work.Diff.STE.fourierExp (-k) x * (∑ i, F i x)
      = ∑ i, Work.Diff.STE.fourierExp (-k) x * F i x := fun x => Finset.mul_sum _ _ _
  rw [funext hpt, MeasureTheory.integral_finsetSum _ (fun i _ => hF i)]

/-- Cauchy–Schwarz for a finite sum: `‖Σᵢ zᵢ‖² ≤ card ι · Σᵢ ‖zᵢ‖²`. -/
lemma sq_norm_finset_sum_le {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℂ) :
    ‖∑ i, f i‖ ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, ‖f i‖ ^ 2 := by
  have h1 : ‖∑ i, f i‖ ≤ ∑ i, ‖f i‖ := norm_sum_le _ _
  have h2 : (∑ i, ‖f i‖) ^ 2 ≤ ((Finset.univ : Finset ι).card : ℝ) * ∑ i, ‖f i‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  rw [Finset.card_univ] at h2
  calc ‖∑ i, f i‖ ^ 2 ≤ (∑ i, ‖f i‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

/-- The norm of the multiplier `2πi kᵢ` times a complex number. -/
lemma norm_two_pi_I_mul {ι : Type*} (k : ι → ℤ) (i : ι) (z : ℂ) :
    ‖(2 * Real.pi * Complex.I * (((k i : ℤ)) : ℂ)) * z‖
      = 2 * Real.pi * ‖((((k i : ℤ)) : ℂ))‖ * ‖z‖ := by
  rw [norm_mul]
  congr 1
  have h : (2 * Real.pi * Complex.I * (((k i : ℤ)) : ℂ))
      = ((2 * Real.pi : ℝ) : ℂ) * (Complex.I * (((k i : ℤ)) : ℂ)) := by push_cast; ring
  rw [h, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
    norm_mul, Complex.norm_I, one_mul]

/-- The Fourier multiplier `dmul i` costs one power of the weight. -/
lemma norm_dmul_le_wt {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) (u : (ι → ℤ) → ℂ)
    (k : ι → ℤ) :
    ‖Work.Diff.STE.dmul i u k‖ ≤ 2 * Real.pi * (Work.Diff.STE.wt k * ‖u k‖) := by
  rw [Work.Diff.STE.dmul, norm_two_pi_I_mul k i (u k), Complex.norm_intCast]
  have h := Work.Diff.STE.abs_intCast_le_wt k i
  calc 2 * Real.pi * |(((k i : ℤ) : ℝ))| * ‖u k‖
      ≤ 2 * Real.pi * Work.Diff.STE.wt k * ‖u k‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_left h (by positivity)
    _ = 2 * Real.pi * (Work.Diff.STE.wt k * ‖u k‖) := by ring

/-- Summability of a weighted family at a lower weight. -/
lemma summable_of_le_level {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → ℤ) → ℂ)
    {a b : ℕ} (hab : a ≤ b)
    (h : Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ b * ‖f k‖ ^ 2)) :
    Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ a * ‖f k‖ ^ 2) := by
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) a) (sq_nonneg _))
    (fun k => ?_) h
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  exact pow_le_pow_right₀ (Work.Diff.STE.wt_one_le k) hab

/-- The Friedrichs cutoff does not increase the norm, for a profile bounded by `1`. -/
lemma norm_trunc_le {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : (ι → ℝ) → ℝ)
    (hρb : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1) (ε : ℝ) (u : (ι → ℤ) → ℂ) (k : ι → ℤ) :
    ‖Work.Diff.STE.trunc ρ ε u k‖ ≤ ‖u k‖ := by
  have h1 : ‖((ρ (ε • fun i => ((k i : ℤ) : ℝ)) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    have h := hρb (ε • fun i => ((k i : ℤ) : ℝ))
    rwa [Real.norm_eq_abs] at h
  calc ‖Work.Diff.STE.trunc ρ ε u k‖
      = ‖((ρ (ε • fun i => ((k i : ℤ) : ℝ)) : ℝ) : ℂ)‖ * ‖u k‖ := by
        simp only [Work.Diff.STE.trunc, norm_mul]
    _ ≤ 1 * ‖u k‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = ‖u k‖ := one_mul _

theorem firstOrder_comm_trunc_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : (ι → ℝ) → ℝ)
    (hρb : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (hdiam : ∀ y : ι → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (hρ0 : ρ 0 = 1)
    (L : ℝ) (hL : 0 ≤ L) (hρlip : ∀ y z : ι → ℝ, ‖ρ y - ρ z‖ ≤ L * ‖y - z‖)
    (M : ι → (ι → ℝ) → ℝ)
    (hMsm : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (M i))
    (hMper : ∀ i, Work.Diff.STE.Periodic1 (M i))
    (CM : ℝ) (hCM : ∀ (i : ι) (x : ι → ℝ), ‖M i x‖ ≤ CM)
    (CM1 : ℝ) (hCM1 : ∀ (i : ι) (x : ι → ℝ),
      ‖Work.Diff.STE.pdR i (M i) x‖ ≤ CM1)
    (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ g : (ι → ℝ) → ℂ,
        ContDiff ℝ (⊤ : ℕ∞) g → Work.Diff.STE.Periodic1 g → Summable (fun k : ι → ℤ =>
            (Work.Diff.STE.wt k) ^ s * ‖Work.Diff.STE.fourierCoeff g k‖ ^ 2) →
        Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff
            ((fun x => ∑ i, ((M i x : ℝ) : ℂ) * Work.Diff.STE.pd i
                (Work.Diff.STE.B3.SymCalc.flatCut ρ ε g) x)
              - Work.Diff.STE.B3.SymCalc.flatCut ρ ε (fun x =>
                  ∑ i, ((M i x : ℝ) : ℂ) * Work.Diff.STE.pd i g x)))
          ≤ C * Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff g) := by
  classical
  -- ## Step 0: the coefficient-level commutator estimate, one constant for each `i`
  have hdMl1 : ∀ i : ι, ∀ N : ℕ, Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ N *
      ‖Work.Diff.STE.fourierCoeff (fun x : ι → ℝ => ((M i x : ℝ) : ℂ)) k‖) :=
    fun i N => summable_wt_pow_mul_fourierCoeff N _
      (contDiff_ofReal_comp (M i) (hMsm i)) (periodic1_ofReal (hMper i))
  have hcomm : ∀ i : ι, ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ c : (ι → ℤ) → ℂ,
      Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s * ‖c k‖ ^ 2) →
      Work.Diff.STE.CSq s (fun k =>
          Work.Diff.STE.conv (Work.Diff.STE.fourierCoeff
              (fun x : ι → ℝ => ((M i x : ℝ) : ℂ)))
            (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.dmul i c)) k
          - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv (Work.Diff.STE.fourierCoeff
              (fun x : ι → ℝ => ((M i x : ℝ) : ℂ))) (Work.Diff.STE.dmul i c)) k)
        ≤ C * Work.Diff.STE.CSq s c :=
    fun i => friedrichs_commutator_supp ρ hρb hdiam L hL hρlip _ (hdMl1 i) s i
  choose Cm hCm using hcomm
  refine ⟨(Fintype.card ι : ℝ) * ∑ i, Cm i,
    mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun i _ => (hCm i).1)), ?_⟩
  intro ε hε hε1 g hg hgper hCSq
  -- ## Step 1: the coefficient families and their weighted summability
  set c : (ι → ℤ) → ℂ := Work.Diff.STE.fourierCoeff g with hc
  set σ : (ι → ℤ) → ℂ := Work.Diff.STE.trunc ρ ε c with hσ
  set D : ι → (ι → ℤ) → ℂ :=
    fun i => Work.Diff.STE.fourierCoeff (fun x : ι → ℝ => ((M i x : ℝ) : ℂ)) with hD
  have hcl1 : ∀ N : ℕ, Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ N * ‖c k‖) :=
    fun N => summable_wt_pow_mul_fourierCoeff N g hg hgper
  have hDl1 : ∀ i : ι, ∀ N : ℕ,
      Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ N * ‖D i k‖) := hdMl1
  have hσl1 : ∀ N : ℕ, Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ N * ‖σ k‖) := by
    intro N
    exact Summable.of_nonneg_of_le
      (fun k => mul_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) N) (norm_nonneg _))
      (fun k => mul_le_mul_of_nonneg_left (norm_trunc_le ρ hρb ε c k)
        (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) N)) (hcl1 N)
  have hCsqC : ∀ N : ℕ, Summable (fun k : ι → ℤ =>
      (Work.Diff.STE.wt k) ^ N * ‖c k‖ ^ 2) := fun N =>
    Work.Diff.STE.Comp.summable_wt_fourierCoeff N g
      (hg.of_le (WithTop.coe_le_coe.mpr le_top)) hgper
  have hwc : Summable (fun k : ι → ℤ =>
      2 * Real.pi * (Work.Diff.STE.wt k * ‖c k‖)) :=
    ((hcl1 1).congr (fun k => by rw [pow_one])).mul_left (2 * Real.pi)
  have hdmulc_l1 : ∀ i : ι, Summable (fun k : ι → ℤ => ‖Work.Diff.STE.dmul i c k‖) :=
    fun i => Summable.of_nonneg_of_le (fun k => norm_nonneg _)
      (fun k => norm_dmul_le_wt i c k) hwc
  have hdmulσ_l1 : ∀ i : ι, Summable (fun k : ι → ℤ => ‖Work.Diff.STE.dmul i σ k‖) := by
    intro i
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) hwc
    calc ‖Work.Diff.STE.dmul i σ k‖ ≤ 2 * Real.pi * (Work.Diff.STE.wt k * ‖σ k‖) :=
          norm_dmul_le_wt i σ k
      _ ≤ 2 * Real.pi * (Work.Diff.STE.wt k * ‖c k‖) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left (norm_trunc_le ρ hρb ε c k)
            (le_of_lt (Work.Diff.STE.wt_pos k))
  -- ## Step 2: the series identities
  have hflat : Work.Diff.STE.B3.SymCalc.flatCut ρ ε g = Work.Diff.STE.seriesFun σ := by
    simp only [Work.Diff.STE.B3.SymCalc.flatCut, hσ, hc]
  have hgser : ∀ x : ι → ℝ, Work.Diff.STE.seriesFun c x = g x :=
    Work.Diff.STE.flat.seriesFun_fourierCoeff g hg hgper
  have hg_eq : g = Work.Diff.STE.seriesFun c := funext fun x => (hgser x).symm
  have hpdσ : ∀ i : ι, Work.Diff.STE.pd i (Work.Diff.STE.B3.SymCalc.flatCut ρ ε g)
      = Work.Diff.STE.seriesFun (Work.Diff.STE.dmul i σ) := fun i =>
    funext fun x => by
      rw [hflat]
      exact Work.Diff.STE.pd_seriesFun i σ hσl1 x
  have hpdg : ∀ i : ι, Work.Diff.STE.pd i g
      = Work.Diff.STE.seriesFun (Work.Diff.STE.dmul i c) := fun i =>
    funext fun x => by
      rw [hg_eq]
      exact Work.Diff.STE.pd_seriesFun i c hcl1 x
  -- ## Step 3: continuity and integrability of the summands
  have hMcont : ∀ i : ι, Continuous (fun x : ι → ℝ => ((M i x : ℝ) : ℂ)) :=
    fun i => Complex.continuous_ofReal.comp (hMsm i).continuous
  have hInt1 : ∀ (k : ι → ℤ) (i : ι), MeasureTheory.Integrable
      (fun x => Work.Diff.STE.fourierExp (-k) x
        * (((M i x : ℝ) : ℂ) * Work.Diff.STE.pd i (Work.Diff.STE.B3.SymCalc.flatCut ρ ε g) x))
      (MeasureTheory.volume.restrict (Work.Diff.STE.unitCube (ι := ι))) := by
    intro k i
    refine Work.Diff.STE.integrableOn_unitCube_of_continuous ?_
    rw [show (fun x => Work.Diff.STE.fourierExp (-k) x
        * (((M i x : ℝ) : ℂ) * Work.Diff.STE.pd i (Work.Diff.STE.B3.SymCalc.flatCut ρ ε g) x))
      = fun x => Work.Diff.STE.fourierExp (-k) x
        * (((M i x : ℝ) : ℂ) * Work.Diff.STE.seriesFun (Work.Diff.STE.dmul i σ) x) from by
        funext x; rw [hpdσ i]]
    exact (Work.Diff.STE.continuous_fourierExp (-k)).mul
      ((hMcont i).mul (Work.Diff.STE.flat.continuous_seriesFun_of_summable _
        (hdmulσ_l1 i)))
  have hInt2 : ∀ (k : ι → ℤ) (i : ι), MeasureTheory.Integrable
      (fun x => Work.Diff.STE.fourierExp (-k) x
        * (((M i x : ℝ) : ℂ) * Work.Diff.STE.pd i g x))
      (MeasureTheory.volume.restrict (Work.Diff.STE.unitCube (ι := ι))) := by
    intro k i
    refine Work.Diff.STE.integrableOn_unitCube_of_continuous ?_
    rw [show (fun x => Work.Diff.STE.fourierExp (-k) x
        * (((M i x : ℝ) : ℂ) * Work.Diff.STE.pd i g x))
      = fun x => Work.Diff.STE.fourierExp (-k) x
        * (((M i x : ℝ) : ℂ) * Work.Diff.STE.seriesFun (Work.Diff.STE.dmul i c) x) from by
        funext x; rw [hpdg i]]
    exact (Work.Diff.STE.continuous_fourierExp (-k)).mul
      ((hMcont i).mul (Work.Diff.STE.flat.continuous_seriesFun_of_summable _
        (hdmulc_l1 i)))
  -- ## Step 4: the product rules
  have hprod1 : ∀ (i : ι) (k : ι → ℤ),
      Work.Diff.STE.fourierCoeff (fun x => ((M i x : ℝ) : ℂ)
          * Work.Diff.STE.pd i (Work.Diff.STE.B3.SymCalc.flatCut ρ ε g) x) k
        = Work.Diff.STE.conv (D i) (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.dmul i c)) k := by
    intro i k
    rw [hpdσ i]
    rw [Work.Diff.STE.fourierCoeff_mul_seriesFun (fun x : ι → ℝ => ((M i x : ℝ) : ℂ))
      (Work.Diff.STE.dmul i σ) k (Work.Diff.STE.integrableOn_unitCube_of_continuous (hMcont i))
      (hdmulσ_l1 i)]
    rw [conv_comm]
    refine congrArg (fun u => Work.Diff.STE.conv (D i) u k) ?_
    exact trunc_dmul ρ ε i c
  have hprod2 : ∀ (i : ι) (k : ι → ℤ),
      Work.Diff.STE.fourierCoeff (fun x => ((M i x : ℝ) : ℂ) * Work.Diff.STE.pd i g x) k
        = Work.Diff.STE.conv (D i) (Work.Diff.STE.dmul i c) k := by
    intro i k
    rw [hpdg i]
    rw [Work.Diff.STE.fourierCoeff_mul_seriesFun (fun x : ι → ℝ => ((M i x : ℝ) : ℂ))
      (Work.Diff.STE.dmul i c) k (Work.Diff.STE.integrableOn_unitCube_of_continuous (hMcont i))
      (hdmulc_l1 i)]
    exact conv_comm _ _ k
  -- ## Step 5: the Fourier coefficients of `P (S_ε g)` and of `S_ε (P g)`
  have hF1 : ∀ k : ι → ℤ,
      Work.Diff.STE.fourierCoeff (fun x => ∑ i, ((M i x : ℝ) : ℂ)
          * Work.Diff.STE.pd i (Work.Diff.STE.B3.SymCalc.flatCut ρ ε g) x) k
        = ∑ i, Work.Diff.STE.conv (D i)
            (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.dmul i c)) k := by
    intro k
    rw [fourierCoeff_fintype_sum (fun i x => ((M i x : ℝ) : ℂ)
      * Work.Diff.STE.pd i (Work.Diff.STE.B3.SymCalc.flatCut ρ ε g) x) k (hInt1 k)]
    exact Finset.sum_congr rfl (fun i _ => hprod1 i k)
  have hF2 : ∀ k : ι → ℤ,
      Work.Diff.STE.fourierCoeff (fun x => ∑ i, ((M i x : ℝ) : ℂ)
          * Work.Diff.STE.pd i g x) k
        = ∑ i, Work.Diff.STE.conv (D i) (Work.Diff.STE.dmul i c) k := by
    intro k
    rw [fourierCoeff_fintype_sum (fun i x => ((M i x : ℝ) : ℂ) * Work.Diff.STE.pd i g x)
      k (hInt2 k)]
    exact Finset.sum_congr rfl (fun i _ => hprod2 i k)
  set e : (ι → ℤ) → ℂ := fun k => ∑ i, Work.Diff.STE.conv (D i) (Work.Diff.STE.dmul i c) k
    with he
  have heF : Work.Diff.STE.fourierCoeff (fun x => ∑ i, ((M i x : ℝ) : ℂ)
      * Work.Diff.STE.pd i g x) = e := funext fun k => hF2 k
  have hconv_l1 : ∀ i : ι, Summable (fun k : ι → ℤ =>
      ‖Work.Diff.STE.conv (D i) (Work.Diff.STE.dmul i c) k‖) := fun i =>
    Work.Diff.STE.summable_conv_norm (D i) (Work.Diff.STE.dmul i c)
      ((hDl1 i 0).congr (fun k => by rw [pow_zero, one_mul])) (hdmulc_l1 i)
  have hel1 : Summable (fun k : ι → ℤ => ‖e k‖) := by
    have h := summable_sum (f := fun (i : ι) (k : ι → ℤ) =>
      ‖Work.Diff.STE.conv (D i) (Work.Diff.STE.dmul i c) k‖) (s := Finset.univ)
      (fun i _ => hconv_l1 i)
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) h
    exact norm_sum_le _ _
  have htel1 : Summable (fun k : ι → ℤ => ‖Work.Diff.STE.trunc ρ ε e k‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _)
      (fun k => norm_trunc_le ρ hρb ε e k) hel1
  have hG_eq : Work.Diff.STE.B3.SymCalc.flatCut ρ ε
      (fun x => ∑ i, ((M i x : ℝ) : ℂ) * Work.Diff.STE.pd i g x)
      = Work.Diff.STE.seriesFun (Work.Diff.STE.trunc ρ ε e) := by
    have h1 : Work.Diff.STE.trunc ρ ε (Work.Diff.STE.fourierCoeff
        (fun x => ∑ i, ((M i x : ℝ) : ℂ) * Work.Diff.STE.pd i g x))
        = Work.Diff.STE.trunc ρ ε e := by
      rw [heF]
    simp only [Work.Diff.STE.B3.SymCalc.flatCut]
    rw [h1]
  have hG1 : ∀ k : ι → ℤ,
      Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.SymCalc.flatCut ρ ε
          (fun x => ∑ i, ((M i x : ℝ) : ℂ) * Work.Diff.STE.pd i g x)) k
        = ∑ i, Work.Diff.STE.trunc ρ ε
            (Work.Diff.STE.conv (D i) (Work.Diff.STE.dmul i c)) k := by
    intro k
    rw [hG_eq, Work.Diff.STE.flat.fourierCoeff_seriesFun (Work.Diff.STE.trunc ρ ε e) htel1 k]
    rw [show Work.Diff.STE.trunc ρ ε e k
        = ((ρ (ε • fun j => ((k j : ℤ) : ℝ)) : ℝ) : ℂ) * e k from rfl]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => rfl)
  -- ## Step 6: continuity of the two sides
  have hFc : Continuous (fun x => ∑ i, ((M i x : ℝ) : ℂ)
      * Work.Diff.STE.pd i (Work.Diff.STE.B3.SymCalc.flatCut ρ ε g) x) := by
    have hEq : (fun x => ∑ i, ((M i x : ℝ) : ℂ)
        * Work.Diff.STE.pd i (Work.Diff.STE.B3.SymCalc.flatCut ρ ε g) x)
        = fun x => ∑ i, ((M i x : ℝ) : ℂ)
            * Work.Diff.STE.seriesFun (Work.Diff.STE.dmul i σ) x := by
      funext x
      exact Finset.sum_congr rfl (fun i _ => by rw [hpdσ i])
    rw [hEq]
    exact continuous_finsetSum _ (fun i _ =>
      (hMcont i).mul (Work.Diff.STE.flat.continuous_seriesFun_of_summable _
        (hdmulσ_l1 i)))
  have hGc : Continuous (Work.Diff.STE.B3.SymCalc.flatCut ρ ε
      (fun x => ∑ i, ((M i x : ℝ) : ℂ) * Work.Diff.STE.pd i g x)) := by
    rw [hG_eq]
    exact Work.Diff.STE.flat.continuous_seriesFun_of_summable _ htel1
  -- ## Step 7: the exact identity for the Fourier coefficients of the commutator
  have hcoe : Work.Diff.STE.fourierCoeff
      ((fun x => ∑ i, ((M i x : ℝ) : ℂ) * Work.Diff.STE.pd i
          (Work.Diff.STE.B3.SymCalc.flatCut ρ ε g) x)
        - Work.Diff.STE.B3.SymCalc.flatCut ρ ε (fun x =>
            ∑ i, ((M i x : ℝ) : ℂ) * Work.Diff.STE.pd i g x))
      = fun k => ∑ i, (Work.Diff.STE.conv (D i)
            (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.dmul i c)) k
          - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv (D i) (Work.Diff.STE.dmul i c)) k) := by
    funext k
    rw [show ((fun x => ∑ i, ((M i x : ℝ) : ℂ) * Work.Diff.STE.pd i
            (Work.Diff.STE.B3.SymCalc.flatCut ρ ε g) x)
          - Work.Diff.STE.B3.SymCalc.flatCut ρ ε (fun x =>
              ∑ i, ((M i x : ℝ) : ℂ) * Work.Diff.STE.pd i g x))
        = fun x => (∑ i, ((M i x : ℝ) : ℂ) * Work.Diff.STE.pd i
              (Work.Diff.STE.B3.SymCalc.flatCut ρ ε g) x)
            - Work.Diff.STE.B3.SymCalc.flatCut ρ ε (fun x =>
                ∑ i, ((M i x : ℝ) : ℂ) * Work.Diff.STE.pd i g x) x from rfl]
    rw [Work.Diff.STE.flat.fourierCoeff_sub_of_continuous _ _ hFc hGc k, hF1 k, hG1 k,
      Finset.sum_sub_distrib]
  -- ## Step 8: summability of the commutator families
  obtain ⟨s0, hs0⟩ : ∃ s0 : ℕ, Fintype.card ι < 2 * s0 := ⟨Fintype.card ι + 1, by omega⟩
  have hs0' : Fintype.card ι < 2 * (s + s0) := by omega
  have hDcsq : ∀ i : ι, Summable (fun k : ι → ℤ =>
      (Work.Diff.STE.wt k) ^ (s + s0) * ‖D i k‖ ^ 2) := fun i =>
    Work.Diff.STE.Comp.summable_wt_fourierCoeff (s + s0) _
      ((contDiff_ofReal_comp (M i) (hMsm i)).of_le (WithTop.coe_le_coe.mpr le_top))
      (periodic1_ofReal (hMper i))
  have hucsq : ∀ i : ι, Summable (fun k : ι → ℤ =>
      (Work.Diff.STE.wt k) ^ (s + s0) * ‖Work.Diff.STE.dmul i c k‖ ^ 2) := by
    intro i
    refine Summable.of_nonneg_of_le
      (fun k => mul_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) _) (sq_nonneg _))
      (fun k => ?_) ((hCsqC (s + s0 + 2)).mul_left ((2 * Real.pi) ^ 2))
    have h := norm_dmul_le_wt i c k
    have hw : (Work.Diff.STE.wt k) ^ (s + s0 + 2)
        = (Work.Diff.STE.wt k) ^ (s + s0) * (Work.Diff.STE.wt k) ^ 2 := by rw [pow_add]
    calc (Work.Diff.STE.wt k) ^ (s + s0) * ‖Work.Diff.STE.dmul i c k‖ ^ 2
        ≤ (Work.Diff.STE.wt k) ^ (s + s0)
            * (2 * Real.pi * (Work.Diff.STE.wt k * ‖c k‖)) ^ 2 :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg _) h 2)
            (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) _)
      _ = (2 * Real.pi) ^ 2 * ((Work.Diff.STE.wt k) ^ (s + s0 + 2) * ‖c k‖ ^ 2) := by
          rw [hw]; ring
  have htdcsq : ∀ i : ι, Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ (s + s0)
      * ‖Work.Diff.STE.trunc ρ ε (Work.Diff.STE.dmul i c) k‖ ^ 2) := by
    intro i
    refine Summable.of_nonneg_of_le
      (fun k => mul_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) _) (sq_nonneg _))
      (fun k => ?_) (hucsq i)
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) _)
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_trunc_le ρ hρb ε (Work.Diff.STE.dmul i c) k) 2
  have hconvbig : ∀ i : ι, Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ (s + s0)
      * ‖Work.Diff.STE.conv (D i) (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.dmul i c)) k‖ ^ 2) :=
    fun i => (Work.Diff.STE.CSq_conv_le (s + s0) hs0').choose_spec.2
      (D i) (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.dmul i c)) (hDcsq i) (htdcsq i) |>.1
  have hconv2big : ∀ i : ι, Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ (s + s0)
      * ‖Work.Diff.STE.conv (D i) (Work.Diff.STE.dmul i c) k‖ ^ 2) :=
    fun i => (Work.Diff.STE.CSq_conv_le (s + s0) hs0').choose_spec.2
      (D i) (Work.Diff.STE.dmul i c) (hDcsq i) (hucsq i) |>.1
  have hconv_summ : ∀ i : ι, Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s
      * ‖Work.Diff.STE.conv (D i) (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.dmul i c)) k‖ ^ 2) :=
    fun i => summable_of_le_level _ (Nat.le_add_right s s0) (hconvbig i)
  have hconv2_summ : ∀ i : ι, Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s
      * ‖Work.Diff.STE.conv (D i) (Work.Diff.STE.dmul i c) k‖ ^ 2) :=
    fun i => summable_of_le_level _ (Nat.le_add_right s s0) (hconv2big i)
  have htrunc_summ : ∀ i : ι, Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s
      * ‖Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv (D i) (Work.Diff.STE.dmul i c)) k‖ ^ 2) := by
    intro i
    refine Summable.of_nonneg_of_le
      (fun k => mul_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) s) (sq_nonneg _))
      (fun k => ?_) (hconv2_summ i)
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) s)
    exact pow_le_pow_left₀ (norm_nonneg _)
      (norm_trunc_le ρ hρb ε (Work.Diff.STE.conv (D i) (Work.Diff.STE.dmul i c)) k) 2
  have hcommS : ∀ i : ι, Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s *
      ‖Work.Diff.STE.conv (D i) (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.dmul i c)) k
        - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv (D i) (Work.Diff.STE.dmul i c)) k‖ ^ 2) := by
    intro i
    refine Summable.of_nonneg_of_le
      (fun k => mul_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) s) (sq_nonneg _))
      (fun k => ?_) (((hconv_summ i).add (htrunc_summ i)).mul_left 2)
    have h1 : ‖Work.Diff.STE.conv (D i) (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.dmul i c)) k
        - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv (D i) (Work.Diff.STE.dmul i c)) k‖ ^ 2
        ≤ 2 * ‖Work.Diff.STE.conv (D i) (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.dmul i c)) k‖ ^ 2
          + 2 * ‖Work.Diff.STE.trunc ρ ε
              (Work.Diff.STE.conv (D i) (Work.Diff.STE.dmul i c)) k‖ ^ 2 := by
      have h2 : ‖Work.Diff.STE.conv (D i) (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.dmul i c)) k
          - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv (D i) (Work.Diff.STE.dmul i c)) k‖
          ≤ ‖Work.Diff.STE.conv (D i) (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.dmul i c)) k‖
            + ‖Work.Diff.STE.trunc ρ ε
                (Work.Diff.STE.conv (D i) (Work.Diff.STE.dmul i c)) k‖ := norm_sub_le _ _
      nlinarith [norm_nonneg (Work.Diff.STE.conv (D i)
            (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.dmul i c)) k),
        norm_nonneg (Work.Diff.STE.trunc ρ ε
            (Work.Diff.STE.conv (D i) (Work.Diff.STE.dmul i c)) k),
        norm_nonneg (Work.Diff.STE.conv (D i) (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.dmul i c)) k
          - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv (D i) (Work.Diff.STE.dmul i c)) k), h2,
        sq_nonneg (‖Work.Diff.STE.conv (D i) (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.dmul i c)) k‖
          - ‖Work.Diff.STE.trunc ρ ε
              (Work.Diff.STE.conv (D i) (Work.Diff.STE.dmul i c)) k‖)]
    calc (Work.Diff.STE.wt k) ^ s * ‖Work.Diff.STE.conv (D i)
            (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.dmul i c)) k
          - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv (D i) (Work.Diff.STE.dmul i c)) k‖ ^ 2
        ≤ (Work.Diff.STE.wt k) ^ s * (2 * ‖Work.Diff.STE.conv (D i)
              (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.dmul i c)) k‖ ^ 2
            + 2 * ‖Work.Diff.STE.trunc ρ ε
                (Work.Diff.STE.conv (D i) (Work.Diff.STE.dmul i c)) k‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h1
            (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) s)
      _ = 2 * ((Work.Diff.STE.wt k) ^ s * ‖Work.Diff.STE.conv (D i)
              (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.dmul i c)) k‖ ^ 2
            + (Work.Diff.STE.wt k) ^ s * ‖Work.Diff.STE.trunc ρ ε
              (Work.Diff.STE.conv (D i) (Work.Diff.STE.dmul i c)) k‖ ^ 2) := by ring
  -- ## Step 9: the final estimate
  rw [hcoe]
  have hsum_all : Summable (fun k : ι → ℤ => ∑ i, (Work.Diff.STE.wt k) ^ s *
      ‖Work.Diff.STE.conv (D i) (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.dmul i c)) k
        - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv (D i) (Work.Diff.STE.dmul i c)) k‖ ^ 2) :=
    summable_sum (fun i _ => hcommS i)
  have hpt : ∀ k : ι → ℤ, (Work.Diff.STE.wt k) ^ s
      * ‖∑ i, (Work.Diff.STE.conv (D i) (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.dmul i c)) k
          - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv (D i) (Work.Diff.STE.dmul i c)) k)‖ ^ 2
      ≤ (Fintype.card ι : ℝ) * ∑ i, (Work.Diff.STE.wt k) ^ s *
        ‖Work.Diff.STE.conv (D i) (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.dmul i c)) k
          - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv (D i) (Work.Diff.STE.dmul i c)) k‖ ^ 2 := by
    intro k
    set g : ι → ℂ := fun i =>
      Work.Diff.STE.conv (D i) (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.dmul i c)) k
        - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv (D i) (Work.Diff.STE.dmul i c)) k
      with hg
    have h1 : ‖∑ i, g i‖ ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, ‖g i‖ ^ 2 :=
      sq_norm_finset_sum_le g
    have hstep : (Work.Diff.STE.wt k) ^ s * ((Fintype.card ι : ℝ) * ∑ i, ‖g i‖ ^ 2)
        = (Fintype.card ι : ℝ) * ∑ i, (Work.Diff.STE.wt k) ^ s * ‖g i‖ ^ 2 := by
      rw [← mul_assoc, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    calc (Work.Diff.STE.wt k) ^ s * ‖∑ i, g i‖ ^ 2
        ≤ (Work.Diff.STE.wt k) ^ s * ((Fintype.card ι : ℝ) * ∑ i, ‖g i‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) s)
      _ = (Fintype.card ι : ℝ) * ∑ i, (Work.Diff.STE.wt k) ^ s * ‖g i‖ ^ 2 := hstep
  have hsumL : Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s
      * ‖∑ i, (Work.Diff.STE.conv (D i) (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.dmul i c)) k
          - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv (D i) (Work.Diff.STE.dmul i c)) k)‖ ^ 2) :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) s) (sq_nonneg _))
      hpt (hsum_all.mul_left _)
  rw [Work.Diff.STE.CSq]
  calc ∑' k : ι → ℤ, (Work.Diff.STE.wt k) ^ s
        * ‖∑ i, (Work.Diff.STE.conv (D i) (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.dmul i c)) k
            - Work.Diff.STE.trunc ρ ε
                (Work.Diff.STE.conv (D i) (Work.Diff.STE.dmul i c)) k)‖ ^ 2
      ≤ ∑' k : ι → ℤ, (Fintype.card ι : ℝ) * ∑ i, (Work.Diff.STE.wt k) ^ s *
          ‖Work.Diff.STE.conv (D i) (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.dmul i c)) k
            - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv (D i) (Work.Diff.STE.dmul i c)) k‖ ^ 2 :=
        Summable.tsum_le_tsum hpt hsumL (hsum_all.mul_left _)
    _ = (Fintype.card ι : ℝ) * ∑' k : ι → ℤ, ∑ i, (Work.Diff.STE.wt k) ^ s *
          ‖Work.Diff.STE.conv (D i) (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.dmul i c)) k
            - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv (D i) (Work.Diff.STE.dmul i c)) k‖ ^ 2 :=
        tsum_mul_left
    _ = (Fintype.card ι : ℝ) * ∑ i, ∑' k : ι → ℤ, (Work.Diff.STE.wt k) ^ s *
          ‖Work.Diff.STE.conv (D i) (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.dmul i c)) k
            - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv (D i) (Work.Diff.STE.dmul i c)) k‖ ^ 2 := by
        rw [Summable.tsum_finsetSum (fun i _ => hcommS i)]
    _ = (Fintype.card ι : ℝ) * ∑ i, Work.Diff.STE.CSq s (fun k =>
          Work.Diff.STE.conv (D i) (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.dmul i c)) k
            - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv (D i) (Work.Diff.STE.dmul i c)) k) := rfl
    _ ≤ (Fintype.card ι : ℝ) * ∑ i, Cm i * Work.Diff.STE.CSq s c := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact Finset.sum_le_sum (fun i _ => (hCm i).2 ε hε hε1 c hCSq)
    _ = ((Fintype.card ι : ℝ) * ∑ i, Cm i) * Work.Diff.STE.CSq s c := by
        rw [← Finset.sum_mul]; ring

end Work.Diff.STE.B3.SymCalcStep1
