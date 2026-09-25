import Mathlib
import Submission.Work.Maximal.mstWide_defs
import Submission.Work.Maximal.mstBump_radius_lt_sep
import Submission.Work.BourgainPlan.Maximal.mst_major_defs
import Submission.Work.BourgainPlan.Maximal.mst_scalar_defs
import Submission.Work.BourgainPlan.Maximal.mst_err1_bump_defs
import Submission.Work.BourgainPlan.Maximal.mstEta_arcSum_le
import Submission.Work.BourgainPlan.Maximal.mstU_card_le_exp
import Submission.Work.BourgainPlan.Maximal.khatZMult_coeFn_star_mstWeyl
import Submission.Work.BourgainPlan.Maximal.mst_lvl_approx_pointwise
import Submission.Work.BourgainPlan.IonescuWainger.iwPN_le_exp
import Submission.Work.BourgainPlan.IonescuWainger.OpArcDefs

/-!
# Auxiliary vocabulary for the weighted wide arc multiplier `Π̃^G_s`

This module fixes the objects of the proof of `Work.Maximal.mstWidePiG_lr_bound`
(MST arXiv:1512.07518, eq. (79)) and the elementary structural facts about the wide bump
`ϱ_s(ξ) = η(c_s · iwRep ξ)`, `c_s = mstWideC P s`, that the estimate uses:

* `mstLrJ s = ⌊exp √(s+1)⌋` — the global Weyl scale `J` of MST eq. (95);
* `mstLrPiCls` / `mstLrPiGCls` — the `L^∞`-classes of the two wide arc sums `Π̃_s` and `Π̃^G_s`;
* `mstLrBump_arcSum_le` — `Σ_{β ∈ 𝒰(s+1)∖𝒰(s)} ‖ϱ_s(ξ−β)‖ ≤ M` uniformly in `s` and `ξ`
  (the annulus points are `2 exp(−(s+1)^{1/10})`-separated, the bump radius is `1/(2 c_s)`);
* `mstLrBump_abs_iwRep` — for large `s`, `ϱ_s ζ ≠ 0` forces `|iwRep ζ| ≤ ½·2^{−s(d−χ)}`, the
  quantitative form of "`ϱ_s` is narrower than the level bump `η_s`" (the *support* of `η_s` need
  not contain the support of `ϱ_s`, since `η` may vanish inside `[−1/2,1/2]`; only the quantitative
  bound on `iwRep` is true and needed);
* `mstLrWeyl_approx_of_abs` — MST eq. (95) in the quantitative form actually used: on each arc of
  `𝒰(s+1)` the Weyl kernel `m_J` differs from `G β` by `≤ C exp(−√(s+1)/2)` on the whole ball
  `|iwRep (ξ−β)| ≤ ½·2^{−s(d−χ)}`.  This is `mst_lvl_approx_pointwise` applied to the *flat* bump
  `1_{[−1/2,1/2]}` (whose level bump is nonzero exactly on that ball), so no new analysis is
  needed: the conclusion of `mst_lvl_approx_pointwise` does not involve `η` at all.
-/

namespace Work.Maximal

open MeasureTheory Finset
open scoped BigOperators ENNReal

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle
local notation "haarT" => (AddCircle.haarAddCircle (T := 1))

noncomputable section

open Work.BourgainPlan.Maximal (mstQ' mstScale mstScale_apply mstScale_pos mstLevel mstLevel_succ
  mstLevel_zero mstU mstWeyl mstG mstEta mstEta_apply mstRho one_le_mstQ' mst_lvl_approx_pointwise
  iwRep)

/-- The global Weyl scale `J = ⌊exp √(s+1)⌋` of MST eq. (95). -/
def mstLrJ (s : ℕ) : ℕ := ⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊

@[simp] theorem mstLrJ_apply (s : ℕ) :
    mstLrJ s = ⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊ := rfl

/-! ## The scale comparison `2^{s(d−χ)} ≤ c_s` -/

/-- `2^n ≤ (n+1)!`. -/
theorem mstLr_two_pow_le_factorial (n : ℕ) : 2 ^ n ≤ (n + 1).factorial := by
  induction n with
  | zero => simp
  | succ k ih =>
      have h2 : (2 : ℕ) ≤ k + 2 := by omega
      have ih' : 2 ^ k ≤ (k + 1).factorial := ih
      have hstep : (k + 1).factorial * 2 ≤ (k + 1).factorial * (k + 2) :=
        Nat.mul_le_mul_left _ h2
      have hfac : (k + 1).factorial * (k + 2) = (k + 2).factorial := by
        conv_rhs => rw [show k + 2 = (k + 1) + 1 by omega, Nat.factorial_succ]
        ring
      calc 2 ^ (k + 1) = 2 ^ k * 2 := by ring
        _ ≤ (k + 1).factorial * 2 := Nat.mul_le_mul_right _ ih'
        _ ≤ (k + 1).factorial * (k + 2) := hstep
        _ = (k + 2).factorial := hfac

/-- `2^n ≤ 4 · n!` over the reals. -/
theorem mstLr_two_pow_le_four_factorial (n : ℕ) : (2 : ℝ) ^ n ≤ 4 * (n.factorial : ℝ) := by
  induction n with
  | zero => norm_num
  | succ k ih =>
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; norm_num
      · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
        calc (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by ring
          _ ≤ 2 * (4 * (k.factorial : ℝ)) := by linarith
          _ ≤ 4 * ((k + 1) * (k.factorial : ℝ)) := by
              have h2 : (2 : ℝ) ≤ (k : ℝ) + 1 := by linarith
              nlinarith
          _ = 4 * ((k + 1).factorial : ℝ) := by rw [Nat.factorial_succ]; push_cast; ring

/-- **`c_s = (mstQ' s)^{3d}` dominates `2^{s d}`** for large `s`.  Since
`mstQ' s = (⌈exp((s+1)^{1/10})⌉)! ≥ 2^{⌈exp((s+1)^{1/10})⌉-1}` and `log s ≤ s^{1/10}`, the
factorial of the (nearly) exponentially large `⌈exp((s+1)^{1/10})⌉` beats every fixed power of `s`. -/
theorem mstLr_two_pow_le_mstWideC (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) :
    ∃ S₀ : ℕ, ∀ s : ℕ, S₀ ≤ s → (2 : ℝ) ^ (s * P.natDegree) ≤ mstWideC P s := by
  obtain ⟨C₁, hC₁3, hC₁⟩ :=
    Work.BourgainPlan.IonescuWainger.exists_log_le_rpow 1 (1 / 10) (by norm_num) (by norm_num)
  refine ⟨max ⌈C₁⌉₊ 4, fun s hs => ?_⟩
  have hsC : C₁ ≤ (s : ℝ) := by
    have h : ⌈C₁⌉₊ ≤ s := le_trans (le_max_left _ _) hs
    have h2 : (⌈C₁⌉₊ : ℝ) ≤ (s : ℝ) := by exact_mod_cast h
    linarith [Nat.le_ceil C₁]
  have hs4 : 4 ≤ s := le_trans (le_max_right _ _) hs
  have hsRpos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast (by omega : 0 < s)
  -- `log s ≤ (s+1)^{1/10}`
  have hlog : Real.log (s : ℝ) ≤ ((s : ℝ) + 1) ^ (1 / 10 : ℝ) := by
    have h1 : 1 * Real.log (s : ℝ) ≤ (s : ℝ) ^ (1 / 10 : ℝ) := hC₁ s hsC
    have h2 : (s : ℝ) ^ (1 / 10 : ℝ) ≤ ((s : ℝ) + 1) ^ (1 / 10 : ℝ) :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
    linarith
  set σ : ℝ := ((s : ℝ) + 1) ^ (1 / 10 : ℝ) with hσdef
  have hσpos : 0 < σ := by rw [hσdef]; exact Real.rpow_pos_of_pos (by linarith) _
  set N : ℕ := ⌈Real.exp σ⌉₊ with hNdef
  have hNge : Real.exp σ ≤ (N : ℝ) := Nat.le_ceil _
  have hsRle : (s : ℝ) ≤ Real.exp σ := by
    rw [← Real.exp_log hsRpos]
    exact Real.exp_le_exp.mpr hlog
  have hN4 : 4 ≤ N := by
    have h1 : (4 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs4
    have h2 : (4 : ℝ) ≤ (N : ℝ) := le_trans (le_trans h1 hsRle) hNge
    exact_mod_cast h2
  have hsN : s ≤ N := by
    have h : (s : ℝ) ≤ (N : ℝ) := le_trans hsRle hNge
    exact_mod_cast h
  have hQeq : mstQ' s = N.factorial := by
    rw [Work.BourgainPlan.Maximal.mstQ']
  have hQ1 : (1 : ℝ) ≤ (mstQ' s : ℝ) := by exact_mod_cast one_le_mstQ' s
  have hQ4 : (4 : ℝ) ≤ (mstQ' s : ℝ) := by
    have h4 : 4 ≤ N.factorial := le_trans hN4 (Nat.self_le_factorial N)
    rw [hQeq]
    exact_mod_cast h4
  -- `2^N ≤ (mstQ' s)^2`
  have hQ2 : (2 : ℝ) ^ N ≤ (mstQ' s : ℝ) ^ 2 := by
    have h1 : (2 : ℝ) ^ N ≤ 4 * (mstQ' s : ℝ) := by
      have h := mstLr_two_pow_le_four_factorial N
      rw [hQeq]
      exact h
    nlinarith [h1, hQ4]
  -- assemble
  have hgoal1 : (2 : ℝ) ^ (s * P.natDegree) ≤ (2 : ℝ) ^ (N * P.natDegree) :=
    pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_right _ hsN)
  have hgoal2 : (2 : ℝ) ^ (N * P.natDegree) = ((2 : ℝ) ^ N) ^ P.natDegree := by
    rw [← pow_mul]
  have hgoal3 : ((2 : ℝ) ^ N) ^ P.natDegree ≤ ((mstQ' s : ℝ) ^ 2) ^ P.natDegree :=
    pow_le_pow_left₀ (by positivity) hQ2 _
  have hgoal4 : ((mstQ' s : ℝ) ^ 2) ^ P.natDegree = (mstQ' s : ℝ) ^ (2 * P.natDegree) := by
    rw [← pow_mul]
  have hgoal5 : (mstQ' s : ℝ) ^ (2 * P.natDegree) ≤ (mstQ' s : ℝ) ^ (3 * P.natDegree) :=
    pow_le_pow_right₀ hQ1 (by omega)
  have hgoal6 : (mstQ' s : ℝ) ^ (3 * P.natDegree) = mstWideC P s := by rw [mstWideC]
  linarith [hgoal1, hgoal2, hgoal3, hgoal4, hgoal5, hgoal6]

/-- `2^{s(d−χ)} ≤ c_s` for large `s`, whenever `0 ≤ χ ≤ d`. -/
theorem mstLr_mstScale_le_mstWideC (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) {χ : ℝ}
    (hχ0 : 0 ≤ χ) (hχd : χ ≤ (P.natDegree : ℝ)) :
    ∃ S₀ : ℕ, ∀ s : ℕ, S₀ ≤ s → mstScale P.natDegree χ s ≤ mstWideC P s := by
  obtain ⟨S₁, hS₁⟩ := mstLr_two_pow_le_mstWideC P hd
  refine ⟨S₁, fun s hs => ?_⟩
  have h2 : (2 : ℝ) ^ (s * P.natDegree) ≤ mstWideC P s := hS₁ s hs
  have hcmp : mstScale P.natDegree χ s ≤ (2 : ℝ) ^ (s * P.natDegree) := by
    rw [mstScale_apply, ← Real.rpow_natCast (2 : ℝ) (s * P.natDegree)]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hsnn : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
    have hcast : ((s * P.natDegree : ℕ) : ℝ) = (s : ℝ) * (P.natDegree : ℝ) := by push_cast; ring
    rw [hcast]
    nlinarith [hχ0, hχd, hsnn]
  exact le_trans hcmp h2

/-! ## The classes of the two arc sums -/

/-- The wide bump is a.e. bounded. -/
theorem mstLrBump_memLp (P : Polynomial ℤ) (χ : ℝ) (η : ℝ → ℂ) (hηc : Continuous η)
    (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0) (s : ℕ) :
    MemLp (mstWideBump P χ η s) ⊤ haarT :=
  (mstWideBump_memLp_and_narrow P χ η hηc hηsup s).1

/-- The `L^∞`-class of the unweighted wide arc sum `Π̃_s`. -/
def mstLrPiCls (P : Polynomial ℤ) (l : ℕ) (χ : ℝ) (η : ℝ → ℂ) (hηc : Continuous η)
    (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0) (s : ℕ) : Lp ℂ ⊤ haarT :=
  Work.BourgainPlan.IonescuWainger.arcSymbolLp (mstWideBump P χ η s)
    (mstLrBump_memLp P χ η hηc hηsup s) (mstAnnulus l s)

theorem mstLrPiCls_coeFn (P : Polynomial ℤ) (l : ℕ) (χ : ℝ) (η : ℝ → ℂ) (hηc : Continuous η)
    (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0) (s : ℕ) :
    (mstLrPiCls P l χ η hηc hηsup s : Circ → ℂ) =ᵐ[haarT] mstWidePi P l χ η s := by
  refine (Work.BourgainPlan.IonescuWainger.arcSymbolLp_coeFn _ _ _).trans ?_
  filter_upwards with ξ
  exact (mstWidePi_apply P l χ η s ξ).symm

/-- The `L^∞`-class of the weighted wide arc sum `Π̃^G_s`, as a weighted arc symbol. -/
def mstLrPiGCls (P : Polynomial ℤ) (l : ℕ) (χ : ℝ) (η : ℝ → ℂ) (hηc : Continuous η)
    (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0) (s : ℕ) : Lp ℂ ⊤ haarT :=
  Work.BourgainPlan.Maximal.arcSymbolWLp (fun β : Circ => β)
    (fun β => star (Work.BourgainPlan.Maximal.mstG P β)) (mstAnnulus l s)
    (mstWideBump P χ η s) (mstLrBump_memLp P χ η hηc hηsup s)

theorem mstLrPiGCls_coeFn (P : Polynomial ℤ) (l : ℕ) (χ : ℝ) (η : ℝ → ℂ) (hηc : Continuous η)
    (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0) (s : ℕ) :
    (mstLrPiGCls P l χ η hηc hηsup s : Circ → ℂ) =ᵐ[haarT] mstWidePiG P l χ η s := by
  refine (Work.BourgainPlan.Maximal.arcSymbolWLp_coeFn _ _ _ _ _).trans ?_
  filter_upwards with ξ
  rw [Work.BourgainPlan.Maximal.arcSymbolW_apply, mstWidePiG_apply]

/-- The class attached to an arbitrary `MemLp` proof of `mstWidePiG` is `mstLrPiGCls`. -/
theorem mstWidePiG_toLp_eq (P : Polynomial ℤ) (l : ℕ) (χ : ℝ) (η : ℝ → ℂ) (hηc : Continuous η)
    (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0) (s : ℕ)
    {hπ : MemLp (mstWidePiG P l χ η s) ⊤ haarT} :
    hπ.toLp (mstWidePiG P l χ η s) = mstLrPiGCls P l χ η hηc hηsup s :=
  Lp.ext ((MemLp.coeFn_toLp hπ).trans
    (mstLrPiGCls_coeFn P l χ η hηc hηsup s).symm)

/-- The a.e. value of the class of the frozen term `μ_J · Π̃_s` (`μ_J = mstWeyl P J`). -/
theorem khatZMult_smul_mstLrPiCls_coeFn (P : Polynomial ℤ) (l : ℕ) (χ : ℝ) (η : ℝ → ℂ)
    (hηc : Continuous η) (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0) (J s : ℕ) :
    ((Work.BourgainPlan.Maximal.khatZMult P J • mstLrPiCls P l χ η hηc hηsup s :
        Lp ℂ ⊤ haarT) : Circ → ℂ)
      =ᵐ[haarT] fun ξ => star (mstWeyl P J ξ) * mstWidePi P l χ η s ξ := by
  have hK : (↑↑(Work.BourgainPlan.Maximal.khatZMult P J) : Circ → ℂ)
      =ᵐ[haarT] fun ξ => star (mstWeyl P J ξ) :=
    Work.BourgainPlan.Maximal.khatZMult_coeFn_star_mstWeyl P J
  have hC : (↑↑(mstLrPiCls P l χ η hηc hηsup s) : Circ → ℂ)
      =ᵐ[haarT] fun ξ => mstWidePi P l χ η s ξ :=
    mstLrPiCls_coeFn P l χ η hηc hηsup s
  refine (Lp.coeFn_lpSMul (p := ⊤) (q := ⊤) (r := ⊤)
    (Work.BourgainPlan.Maximal.khatZMult P J)
    (mstLrPiCls P l χ η hηc hηsup s)).trans ?_
  filter_upwards [hK, hC] with ξ h1 h2
  show (↑↑(Work.BourgainPlan.Maximal.khatZMult P J) : Circ → ℂ) ξ
      * (↑↑(mstLrPiCls P l χ η hηc hηsup s) : Circ → ℂ) ξ
    = star (mstWeyl P J ξ) * mstWidePi P l χ η s ξ
  rw [h1, h2]

/-- The frozen term `μ_J · Π̃_s` acts as the density average composed with the unweighted arc
operator: `opMul (khatZMult P J • mstLrPiCls) = discAvgZC P J ∘ opMul (mstLrPiCls)`. -/
theorem opMul_khatZMult_smul_mstLrPiCls (P : Polynomial ℤ) (l : ℕ) (χ : ℝ) (η : ℝ → ℂ)
    (hηc : Continuous η) (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0) (J s : ℕ)
    (f : ℤ → ℂ) (hf : Memℓp f 2) :
    Work.BourgainPlan.IonescuWainger.opMul
        (Work.BourgainPlan.Maximal.khatZMult P J • mstLrPiCls P l χ η hηc hηsup s) f hf
      = Work.BourgainPlan.Maximal.discAvgZC P J
          (Work.BourgainPlan.IonescuWainger.opMul
            (mstLrPiCls P l χ η hηc hηsup s) f hf) := by
  rw [mstLrPiCls]
  exact (Work.BourgainPlan.Maximal.discAvgZC_opArc_eq_opMul_smul P J (mstWideBump P χ η s)
    (mstLrBump_memLp P χ η hηc hηsup s) (mstAnnulus l s) f hf).symm

/-! ## Narrowness and the arc-sum bound -/

/-- **The quantitative narrowness of the wide bump**: for large `s`, on the support of `ϱ_s` the
canonical lift is bounded by `½ · 2^{−s(d−χ)}`, i.e. `ϱ_s` sits inside the level-`s` ball. -/
theorem mstLrBump_abs_iwRep (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) {χ : ℝ}
    (hχ0 : 0 ≤ χ) (hχd : χ ≤ (P.natDegree : ℝ)) (η : ℝ → ℂ)
    (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0) :
    ∃ S₀ : ℕ, ∀ s : ℕ, S₀ ≤ s → ∀ ζ : Circ, mstWideBump P χ η s ζ ≠ 0 →
      |iwRep ζ| ≤ (1 / 2) * (2 : ℝ) ^ (-((s : ℝ) * ((P.natDegree : ℝ) - χ))) := by
  obtain ⟨S₁, hS₁⟩ := mstLr_mstScale_le_mstWideC P hd hχ0 hχd
  refine ⟨max S₁ 1, fun s hs ζ hne => ?_⟩
  have hscale : mstScale P.natDegree χ s ≤ mstWideC P s := hS₁ s (le_trans (le_max_left _ _) hs)
  have hc1 : 1 ≤ mstWideC P s := one_le_mstWideC P s
  have hcpos : 0 < mstWideC P s := lt_of_lt_of_le one_pos hc1
  have hlt : |iwRep ζ| < 1 / (2 * mstWideC P s) := by
    by_contra hcon
    have h3 : 1 / (2 * mstWideC P s) ≤ |iwRep ζ| := not_lt.mp hcon
    have h4 : (1 : ℝ) / 2 ≤ |mstWideC P s * iwRep ζ| := by
      rw [abs_mul, abs_of_pos hcpos]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * mstWideC P s)] at h3
      linarith
    have h5 : η (mstWideC P s * iwRep ζ) = 0 := hηsup _ h4
    exact hne (by rw [mstWideBump_apply]; exact h5)
  have hspos : 0 < mstScale P.natDegree χ s := mstScale_pos _ _ _
  calc |iwRep ζ| ≤ 1 / (2 * mstWideC P s) := le_of_lt hlt
    _ ≤ 1 / (2 * mstScale P.natDegree χ s) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
    _ = (1 / 2) * (2 : ℝ) ^ (-((s : ℝ) * ((P.natDegree : ℝ) - χ))) := by
        rw [mstScale_apply, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
          div_eq_mul_inv, one_div, mul_inv_rev]
        ring

/-- **The uniform arc-sum bound for the wide bump**:
`Σ_{β ∈ 𝒰(s+1)∖𝒰(s)} ‖ϱ_s(ξ − β)‖ ≤ M`, uniformly in the level `s` and the frequency `ξ`. -/
theorem mstLrBump_arcSum_le (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) {χ : ℝ}
    (hχ1 : χ < 1 / 10) (l : ℕ) (hl : 1 ≤ l) (η : ℝ → ℂ) (M : ℝ) (hM : 0 < M)
    (hηc : Continuous η) (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M)
    (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0) :
    ∃ M' : ℝ, 0 < M' ∧ ∀ (s : ℕ) (ξ : Circ),
      ∑ β ∈ mstAnnulus l s, ‖mstWideBump P χ η s (ξ - β)‖ ≤ M' := by
  obtain ⟨s₁, hs₁⟩ := Work.BourgainPlan.Maximal.mstU_separated l hl
  obtain ⟨s₂, hs₂⟩ := mstBump_radius_lt_sep P hd hχ1
  set T : ℕ := s₁ + s₂ + 1 with hT
  have hsum_nonneg : ∀ n : ℕ, 0 ≤ ∑ i ∈ Finset.range n,
      (((mstU l (i + 1)).card : ℝ) * M) :=
    fun n => Finset.sum_nonneg (fun i _ => mul_nonneg (Nat.cast_nonneg _) hM.le)
  refine ⟨(∑ i ∈ Finset.range T, (((mstU l (i + 1)).card : ℝ) * M)) + M + 1, ?_, ?_⟩
  · linarith [hsum_nonneg T]
  · intro s ξ
    have hsub : mstAnnulus l s ⊆ mstU l (s + 1) := by
      intro β hβ
      have h : β ∈ mstLevel l (s + 1) \ mstLevel l s := hβ
      rw [mstLevel_succ] at h
      exact (Finset.mem_sdiff.mp h).1
    rcases lt_or_ge s T with hs | hs
    · have hmem : s ∈ Finset.range T := Finset.mem_range.mpr hs
      have hsingle := Finset.single_le_sum
        (f := fun i : ℕ => (((mstU l (i + 1)).card : ℝ) * M))
        (fun i _ => mul_nonneg (Nat.cast_nonneg _) hM.le) hmem
      have hbound : ∑ β ∈ mstAnnulus l s, ‖mstWideBump P χ η s (ξ - β)‖
          ≤ ((mstU l (s + 1)).card : ℝ) * M := by
        calc ∑ β ∈ mstAnnulus l s, ‖mstWideBump P χ η s (ξ - β)‖
            ≤ ∑ _β ∈ mstAnnulus l s, M := Finset.sum_le_sum (fun β _ => by
                rw [mstWideBump_apply]
                exact hηbd _)
          _ = ((mstAnnulus l s).card : ℝ) * M := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ ((mstU l (s + 1)).card : ℝ) * M := by
              have hcard : (mstAnnulus l s).card ≤ (mstU l (s + 1)).card :=
                Finset.card_le_card hsub
              have h2 : ((mstAnnulus l s).card : ℝ) ≤ ((mstU l (s + 1)).card : ℝ) :=
                Nat.cast_le.mpr hcard
              nlinarith [hM.le]
      linarith
    · have hs₁le : s₁ ≤ s := by rw [hT] at hs; omega
      have hs₂le : s₂ ≤ s := by rw [hT] at hs; omega
      have hδε : 2 * (1 / (2 * mstWideC P s))
          < 2 * Real.exp (-(((s : ℝ) + 1) ^ (1 / 10 : ℝ))) := by
        have h := (hs₂ s hs₂le).2
        linarith
      have hbound := Work.BourgainPlan.Maximal.sum_norm_le_of_support_sep
        (φ := mstWideBump P χ η s) (E := mstAnnulus l s)
        (ε := 1 / (2 * mstWideC P s))
        (δ := 2 * Real.exp (-(((s : ℝ) + 1) ^ (1 / 10 : ℝ)))) (M := M)
        (fun z => by rw [mstWideBump_apply]; exact hηbd _)
        (fun z hz => (mstWideBump_memLp_and_narrow P χ η hηc hηsup s).2 z hz)
        (fun β hβ β' hβ' hne => hs₁ s hs₁le β (hsub hβ) β' (hsub hβ') hne)
        hδε ξ
      linarith [hbound, hsum_nonneg T]

/-! ## MST eq. (95) in the quantitative form used for the wide bump -/

/-- The flat bump `1_{[−1/2,1/2]}`: its level-`s` bump `mstEta d χ · s` is nonzero exactly on the
closed ball of radius `½·2^{−s(d−χ)}`. -/
def mstLrFlatBump : ℝ → ℂ := fun x => if |x| ≤ 1 / 2 then 1 else 0

theorem mstLrFlatBump_supp : ∀ x : ℝ, 1 / 2 < |x| → mstLrFlatBump x = 0 := by
  intro x hx
  rw [mstLrFlatBump, if_neg (not_le.mpr hx)]

theorem mstLrEta_flat_ne_zero {d : ℕ} {χ : ℝ} {s : ℕ} {ζ : Circ}
    (h : |iwRep ζ| ≤ (1 / 2) * (2 : ℝ) ^ (-((s : ℝ) * ((d : ℝ) - χ)))) :
    mstEta d χ mstLrFlatBump s ζ ≠ 0 := by
  have hscale : 0 < (2 : ℝ) ^ ((s : ℝ) * ((d : ℝ) - χ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hinv : (2 : ℝ) ^ (-((s : ℝ) * ((d : ℝ) - χ)))
      = ((2 : ℝ) ^ ((s : ℝ) * ((d : ℝ) - χ)))⁻¹ :=
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) _
  have hle : |(2 : ℝ) ^ ((s : ℝ) * ((d : ℝ) - χ)) * iwRep ζ| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_pos hscale]
    calc (2 : ℝ) ^ ((s : ℝ) * ((d : ℝ) - χ)) * |iwRep ζ|
        ≤ (2 : ℝ) ^ ((s : ℝ) * ((d : ℝ) - χ))
            * ((1 / 2) * ((2 : ℝ) ^ ((s : ℝ) * ((d : ℝ) - χ)))⁻¹) := by
          refine mul_le_mul_of_nonneg_left ?_ hscale.le
          rw [hinv] at h
          exact h
      _ = 1 / 2 := by field_simp
  rw [mstEta_apply, mstLrFlatBump, if_pos hle]
  norm_num

/-- **MST eq. (95) on the whole level-`s` ball**: for large `s`, on the ball of radius
`½·2^{−s(d−χ)}` around an arc `β ∈ 𝒰(s+1)`, the Weyl kernel `m_J` (`J = ⌊exp √(s+1)⌋`) differs from
the complete sum `G β` by `≤ C exp(−√(s+1)/2)`.

This is `mst_lvl_approx_pointwise` applied to the flat bump `1_{[−1/2,1/2]}`: its conclusion does
not involve `η`, only its hypothesis `mstEta … (ξ−β) ≠ 0` does, and for the flat bump that
hypothesis is exactly `|iwRep (ξ−β)| ≤ ½·2^{−s(d−χ)}`. -/
theorem mstLrWeyl_approx_of_abs (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (hc : 0 < P.leadingCoeff)
    {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10) (l : ℕ) (hl : 1 ≤ l) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₁ : ℕ, ∀ s : ℕ, N₁ ≤ s →
      ∀ (β ξ : Circ), β ∈ mstU l (s + 1) →
      |iwRep (ξ - β)| ≤ (1 / 2) * (2 : ℝ) ^ (-((s : ℝ) * ((P.natDegree : ℝ) - χ))) →
      ‖mstWeyl P (mstLrJ s) ξ - mstG P β‖
        ≤ C * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2)) := by
  obtain ⟨C, hC, N₁, hN₁⟩ := mst_lvl_approx_pointwise P hd hc hχ0 hχ1 mstLrFlatBump
    mstLrFlatBump_supp l hl
  refine ⟨C, hC, N₁, fun s hs β ξ hβ habs => ?_⟩
  exact hN₁ s hs β ξ hβ (mstLrEta_flat_ne_zero (d := P.natDegree) (χ := χ) (s := s) habs)

end

end Work.Maximal
