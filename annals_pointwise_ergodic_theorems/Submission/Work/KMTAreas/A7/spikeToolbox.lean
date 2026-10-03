import Mathlib
import Submission.Work.KMTPlan.A6.LowSmallSymDefs
import Submission.Work.KMTPlan.A6.M0_iteratedDeriv
import Submission.Work.KMTAreas.A7.M0DerivBound
import Submission.Work.A7.ModelApproxCore_M0_deriv_bound
import Submission.Work.KMTAreas.A7.varphiNt_bounds
import Submission.Work.KMTAreas.A7.fourierDecay_varphitildeN

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTPlan.A6.SpikeToolbox

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger
open Work.KMTAreas.A7

noncomputable section
/-! ## The finite window of representatives of the aliasing fibre -/

/-- The window `[-5,5]` of representatives of the aliasing fibre. -/
def mWindow : Finset ℤ := Finset.Icc (-5) 5

theorem mem_mWindow (m : ℤ) : m ∈ mWindow ↔ -5 ≤ m ∧ m ≤ 5 := by
  simp [mWindow]

theorem six_le_or_le_neg_six_of_notMem_mWindow {m : ℤ} (h : m ∉ mWindow) :
    (6 : ℤ) ≤ m ∨ m ≤ -6 := by
  rw [mem_mWindow] at h
  push Not at h
  omega

/-! ## The support radius of the bumps -/

theorem logN_nonneg (N : ℕ) : 0 ≤ Work.Analysis.EndVar.logN N := by
  unfold Work.Analysis.EndVar.logN
  exact Int.natCast_nonneg _

theorem toNat_logN_le (N : ℕ) :
    (((Work.Analysis.EndVar.logN N).toNat : ℕ) : ℤ) ≤ Work.Analysis.EndVar.logN N := by
  rw [Int.toNat_of_nonneg (logN_nonneg N)]

/-- If `k + 3 ≤ Log N` then the support radius `2^{k - Log N}` of the bump is at most `1/8`. -/
theorem rpow_two_logN_le_eighth (N k : ℕ)
    (h : k + 3 ≤ (Work.Analysis.EndVar.logN N).toNat) :
    (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) ≤ 1 / 8 := by
  have h1 : ((k : ℤ) + 3) ≤ Work.Analysis.EndVar.logN N := by
    have h2 : ((k + 3 : ℕ) : ℤ) ≤ ((Work.Analysis.EndVar.logN N).toNat : ℤ) := by
      exact_mod_cast h
    push_cast at h2
    linarith [h2, toNat_logN_le N]
  have h2 : ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) ≤ -3 := by
    have h1' : (k : ℝ) + 3 ≤ (Work.Analysis.EndVar.logN N : ℝ) := by exact_mod_cast h1
    linarith
  have h3 : (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) ≤ (2 : ℝ) ^ (-3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) h2
  have h4 : ((2 : ℝ) ^ (-3 : ℝ)) = 1 / 8 := by
    rw [show (-3 : ℝ) = ((-3 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
    norm_num
  rw [h4] at h3
  exact h3

theorem abs_six_le_abs_of_notMem {m : ℤ} (hm : m ∉ mWindow) :
    (6 : ℝ) ≤ |((m : ℤ) : ℝ)| := by
  rcases six_le_or_le_neg_six_of_notMem_mWindow hm with hm' | hm'
  · rw [abs_of_nonneg (by exact_mod_cast (by omega : (0 : ℤ) ≤ m))]
    exact_mod_cast hm'
  · rw [abs_of_nonpos (by exact_mod_cast (by omega : m ≤ 0))]
    exact_mod_cast (by omega : (6 : ℤ) ≤ -m)

/-- For `m` outside the window and `|u| ≤ 5`, the point `u + m` is at distance at least `1` from
the origin. -/
theorem one_le_abs_add_of_notMem {u : ℝ} (hu : |u| ≤ 5) {m : ℤ} (hm : m ∉ mWindow) :
    (1 : ℝ) ≤ |u + (m : ℤ)| := by
  have hm6 : (6 : ℝ) ≤ |((m : ℤ) : ℝ)| := abs_six_le_abs_of_notMem hm
  have htri : |(-((m : ℤ) : ℝ))| - |u| ≤ |(-((m : ℤ) : ℝ)) - u| := abs_sub_abs_le_abs_sub _ _
  rw [abs_neg] at htri
  have harg : -((m : ℤ) : ℝ) - u = -(u + (m : ℤ)) := by ring
  rw [harg, abs_neg] at htri
  linarith

theorem varphiN_eq_zero_of_lt {N k : ℕ} {ξ : ℝ}
    (h : (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) < |ξ|) :
    Work.KMTAreas.A7.varphiN N k ξ = 0 := by
  by_contra hne
  exact absurd (Work.KMTAreas.A7.varphiN_support N k ξ hne) (not_le.mpr h)

/-- **`φ_N` vanishes away from the window `[-5,5]`.** -/
theorem varphiN_eq_zero_of_window {N k : ℕ} (h : k + 3 ≤ (Work.Analysis.EndVar.logN N).toNat)
    {c x : ℝ} (hc : |c| ≤ 1) (hx : |x| ≤ 4) {m : ℤ} (hm : m ∉ mWindow) :
    Work.KMTAreas.A7.varphiN N k (x - c + m) = 0 := by
  have hrad : (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) ≤ 1 / 8 :=
    rpow_two_logN_le_eighth N k h
  have hxc : |x - c| ≤ 5 := by
    rw [abs_sub_le_iff]
    constructor <;> linarith [le_abs_self x, neg_le_abs x, le_abs_self c, neg_le_abs c]
  exact varphiN_eq_zero_of_lt (lt_of_le_of_lt hrad (by linarith [one_le_abs_add_of_notMem hxc hm]))

/-- **`φ̃_N` vanishes outside its sharp support radius** `2^{d(k - Log N)}`. -/
theorem varphitildeN_ne_zero_abs_le (d N k : ℕ) (hd : 1 ≤ d) {ξ : ℝ}
    (h : Work.KMTAreas.A7.varphitildeN d N k ξ ≠ 0) :
    |ξ| ≤ (2 : ℝ) ^ ((d : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) := by
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := by positivity
  have key : ∀ (a : ℝ), Work.KMTContract.kmtEta ((2 : ℝ) ^ a * ξ) ≠ 0 →
      |ξ| ≤ (2 : ℝ) ^ (-a) := by
    intro a ha
    have h2 : (0 : ℝ) < (2 : ℝ) ^ a := Real.rpow_pos_of_pos (by norm_num) a
    have hlt : (2 : ℝ) ^ a * |ξ| < 1 := by
      have h1 : ¬ (1 ≤ |(2 : ℝ) ^ a * ξ|) := fun hc => ha (Work.KMTContract.kmtEta_zero hc)
      have h2' : |(2 : ℝ) ^ a * ξ| < 1 := lt_of_not_ge h1
      rwa [abs_mul, abs_of_pos h2] at h2'
    have hb := Work.KMTAreas.A7.abs_le_of_rpow_mul_lt_one (L := a) (k := 0) (by simpa using hlt)
    simpa using hb
  by_cases hk : k = 0
  · subst hk
    rw [Work.KMTAreas.A7.varphitildeN, if_pos rfl] at h
    have hb := key ((d : ℝ) * (Work.Analysis.EndVar.logN N : ℝ)) h
    have he : -((d : ℝ) * (Work.Analysis.EndVar.logN N : ℝ))
        = (d : ℝ) * ((0 : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) := by ring
    rw [he] at hb
    simpa using hb
  · rw [Work.KMTAreas.A7.varphitildeN, if_neg hk] at h
    have hbor : Work.KMTContract.kmtEta
          ((2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * ξ) ≠ 0 ∨
        Work.KMTContract.kmtEta
          ((2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)) * ξ) ≠ 0 := by
      by_contra hc
      push Not at hc
      exact h (by rw [hc.1, hc.2, sub_zero])
    rcases hbor with hc | hc
    · have hb := key ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) hc
      have he : -((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)))
          = (d : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) := by ring
      rw [he] at hb
      exact hb
    · have hb := key ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)) hc
      have he : -((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1))
          = (d : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) - (d : ℝ) := by ring
      rw [he] at hb
      refine hb.trans ?_
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

/-- **`φ̃_N` vanishes away from the window `[-5,5]`.** -/
theorem varphitildeN_eq_zero_of_window (P : ℤ[X]) (hd : 1 ≤ P.natDegree) {N k : ℕ}
    (h : k + 3 ≤ (Work.Analysis.EndVar.logN N).toNat)
    {c y : ℝ} (hc : |c| ≤ 1) (hy : |y| ≤ 4) {m : ℤ} (hm : m ∉ mWindow) :
    Work.KMTAreas.A7.varphitildeN P.natDegree N k (y - c + m) = 0 := by
  have hyc : |y - c| ≤ 5 := by
    rw [abs_sub_le_iff]
    constructor <;> linarith [le_abs_self y, neg_le_abs y, le_abs_self c, neg_le_abs c]
  have harg : (1 : ℝ) ≤ |y - c + (m : ℤ)| := one_le_abs_add_of_notMem hyc hm
  by_contra hne
  have hb := varphitildeN_ne_zero_abs_le P.natDegree N k hd hne
  have hle : (2 : ℝ) ^ ((P.natDegree : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))
      ≤ 1 / 8 := by
    have hkd : (k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ) ≤ 0 := by
      have h1 : ((k : ℤ) + 3) ≤ Work.Analysis.EndVar.logN N := by
        have h2 : ((k + 3 : ℕ) : ℤ) ≤ ((Work.Analysis.EndVar.logN N).toNat : ℤ) := by
          exact_mod_cast h
        push_cast at h2
        linarith [h2, toNat_logN_le N]
      have h1' : (k : ℝ) + 3 ≤ (Work.Analysis.EndVar.logN N : ℝ) := by exact_mod_cast h1
      linarith
    have hd1 : (1 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd
    have hexp : (P.natDegree : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))
        ≤ (k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ) := by
      have := mul_nonpos_of_nonneg_of_nonpos (by linarith : (0 : ℝ) ≤ (P.natDegree : ℝ) - 1) hkd
      linarith
    calc (2 : ℝ) ^ ((P.natDegree : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))
        ≤ (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ ≤ 1 / 8 := rpow_two_logN_le_eighth N k h
  linarith

/-! ## The arithmetic frequencies and the period `perQ` -/

theorem perQ_smul_left (γ₁ γ₂ : Analysis.IonescuWainger.Circle) : perQ γ₁ γ₂ • γ₁ = 0 :=
  addOrderOf_dvd_iff_nsmul_eq_zero.mp (Nat.dvd_lcm_left _ _)

theorem perQ_smul_right (γ₁ γ₂ : Analysis.IonescuWainger.Circle) : perQ γ₁ γ₂ • γ₂ = 0 :=
  addOrderOf_dvd_iff_nsmul_eq_zero.mp (Nat.dvd_lcm_right _ _)

theorem perQ_pos {γ₁ γ₂ : Analysis.IonescuWainger.Circle} (h₁ : IsOfFinAddOrder γ₁) (h₂ : IsOfFinAddOrder γ₂) :
    0 < perQ γ₁ γ₂ := by
  rw [perQ]
  exact Nat.lcm_pos (addOrderOf_pos_iff.mpr h₁) (addOrderOf_pos_iff.mpr h₂)

theorem gamR_abs_le_one (γ : Analysis.IonescuWainger.Circle) : |gamR γ| ≤ 1 := by
  have h : (0 : ℝ) ≤ (AddCircle.equivIco (1 : ℝ) 0 γ).val
      ∧ (AddCircle.equivIco (1 : ℝ) 0 γ).val < 1 := by
    have h0 := (AddCircle.equivIco (1 : ℝ) 0 γ).2
    rw [Set.mem_Ico] at h0
    simpa using h0
  have hg : gamR γ = (AddCircle.equivIco (1 : ℝ) 0 γ).val := rfl
  rw [hg, abs_of_nonneg h.1]
  exact h.2.le

/-! ## The finite-sum form of `symD`

`symD` is by definition a double `tsum` over the representatives `m₁,m₂ ∈ ℤ` of the aliasing
fibres.  Because the bumps `φ_N`, `φ̃_N` are supported in `|ξ| ≤ 1/8`, all but the terms with
`m₁,m₂` in the window `[-5,5]` vanish on any bounded region; this section states that reduction.
-/

/-- The term of the aliasing sum of `symD` at the pair `(γ₁,γ₂,m₁,m₂)`. -/
def symDTerm (P : ℤ[X]) (N k₁ k₂ : ℕ) (γ₁ γ₂ : Analysis.IonescuWainger.Circle)
    (m₁ m₂ : ℤ) (x y : ℝ) : ℂ :=
  M0 P N (perQ γ₁ γ₂) γ₁ γ₂ (x - gamR γ₁ + (m₁ : ℝ)) (y - gamR γ₂ + (m₂ : ℝ))
    * varphiN N k₁ (x - gamR γ₁ + (m₁ : ℝ))
    * varphitildeN P.natDegree N k₂ (y - gamR γ₂ + (m₂ : ℝ))

theorem symDTerm_eq (P : ℤ[X]) (N k₁ k₂ : ℕ) (γ₁ γ₂ : Analysis.IonescuWainger.Circle)
    (m₁ m₂ : ℤ) (x y : ℝ) :
    symDTerm P N k₁ k₂ γ₁ γ₂ m₁ m₂ x y
      = M0 P N (perQ γ₁ γ₂) γ₁ γ₂ (x - gamR γ₁ + (m₁ : ℝ)) (y - gamR γ₂ + (m₂ : ℝ))
        * varphiN N k₁ (x - gamR γ₁ + (m₁ : ℝ))
        * varphitildeN P.natDegree N k₂ (y - gamR γ₂ + (m₂ : ℝ)) := rfl

/-- The term vanishes when the second representative is outside the window. -/
theorem symDTerm_eq_zero_right (P : ℤ[X]) (hd : 1 ≤ P.natDegree) {N k₁ k₂ : ℕ}
    (hk₂ : k₂ + 3 ≤ (Work.Analysis.EndVar.logN N).toNat)
    {γ₁ γ₂ : Analysis.IonescuWainger.Circle} (hc₂ : |gamR γ₂| ≤ 1)
    {m₁ m₂ : ℤ} (hm₂ : m₂ ∉ mWindow) {x y : ℝ} (hy : |y| ≤ 4) :
    symDTerm P N k₁ k₂ γ₁ γ₂ m₁ m₂ x y = 0 := by
  have hz : varphitildeN P.natDegree N k₂ (y - gamR γ₂ + (m₂ : ℝ)) = 0 :=
    varphitildeN_eq_zero_of_window P hd hk₂ hc₂ hy hm₂
  rw [symDTerm_eq]
  rw [mul_eq_zero_of_right _ hz]

/-- The term vanishes when the first representative is outside the window. -/
theorem symDTerm_eq_zero_left (P : ℤ[X]) {N k₁ k₂ : ℕ}
    (hk₁ : k₁ + 3 ≤ (Work.Analysis.EndVar.logN N).toNat)
    {γ₁ γ₂ : Analysis.IonescuWainger.Circle} (hc₁ : |gamR γ₁| ≤ 1)
    {m₁ m₂ : ℤ} (hm₁ : m₁ ∉ mWindow) {x y : ℝ} (hx : |x| ≤ 4) :
    symDTerm P N k₁ k₂ γ₁ γ₂ m₁ m₂ x y = 0 := by
  have hz : varphiN N k₁ (x - gamR γ₁ + (m₁ : ℝ)) = 0 :=
    varphiN_eq_zero_of_window hk₁ hc₁ hx hm₁
  rw [symDTerm_eq]
  rw [show (M0 P N (perQ γ₁ γ₂) γ₁ γ₂ (x - gamR γ₁ + (m₁ : ℝ)) (y - gamR γ₂ + (m₂ : ℝ))
        * varphiN N k₁ (x - gamR γ₁ + (m₁ : ℝ))
        * varphitildeN P.natDegree N k₂ (y - gamR γ₂ + (m₂ : ℝ)))
      = (M0 P N (perQ γ₁ γ₂) γ₁ γ₂ (x - gamR γ₁ + (m₁ : ℝ)) (y - gamR γ₂ + (m₂ : ℝ))
        * varphitildeN P.natDegree N k₂ (y - gamR γ₂ + (m₂ : ℝ)))
        * varphiN N k₁ (x - gamR γ₁ + (m₁ : ℝ)) from by ring,
    hz, mul_zero]

/-- **The finite-window form of `symD`.** -/
theorem symD_eq_window (ρ : ℝ) (P : ℤ[X]) (N l₁ l₂ k₁ k₂ : ℕ) (hd : 1 ≤ P.natDegree)
    (hk₁ : k₁ + 3 ≤ (Work.Analysis.EndVar.logN N).toNat)
    (hk₂ : k₂ + 3 ≤ (Work.Analysis.EndVar.logN N).toNat)
    {x y : ℝ} (hx : |x| ≤ 4) (hy : |y| ≤ 4) :
    symD ρ P N l₁ l₂ k₁ k₂ x y =
      ∑ γ₁ ∈ diffFreqs ρ l₁, ∑ γ₂ ∈ diffFreqs ρ l₂,
        ∑ m₁ ∈ mWindow, ∑ m₂ ∈ mWindow, symDTerm P N k₁ k₂ γ₁ γ₂ m₁ m₂ x y := by
  change (∑ γ₁ ∈ diffFreqs ρ l₁, ∑ γ₂ ∈ diffFreqs ρ l₂, ∑' m₁ : ℤ, ∑' m₂ : ℤ,
      symDTerm P N k₁ k₂ γ₁ γ₂ m₁ m₂ x y) = _
  refine Finset.sum_congr rfl (fun γ₁ hγ₁ => Finset.sum_congr rfl (fun γ₂ hγ₂ => ?_))
  have hc₁ : |gamR γ₁| ≤ 1 := gamR_abs_le_one γ₁
  have hc₂ : |gamR γ₂| ≤ 1 := gamR_abs_le_one γ₂
  have hinner : ∀ m₁ : ℤ, (∑' m₂ : ℤ, symDTerm P N k₁ k₂ γ₁ γ₂ m₁ m₂ x y)
      = ∑ m₂ ∈ mWindow, symDTerm P N k₁ k₂ γ₁ γ₂ m₁ m₂ x y := by
    intro m₁
    refine tsum_eq_sum (fun m₂ hm₂ => ?_)
    exact symDTerm_eq_zero_right P hd hk₂ hc₂ hm₂ hy
  rw [tsum_congr hinner]
  refine tsum_eq_sum (fun m₁ hm₁ => ?_)
  refine Finset.sum_eq_zero (fun m₂ hm₂ => ?_)
  exact symDTerm_eq_zero_left P hk₁ hc₁ hm₁ hx

/-! ## The product-finset form -/

/-- The index set of the finite sum representing `symD`. -/
def symIdx (ρ : ℝ) (l₁ l₂ : ℕ) :
    Finset (((Analysis.IonescuWainger.Circle × Analysis.IonescuWainger.Circle) × ℤ) × ℤ) :=
  ((diffFreqs ρ l₁ ×ˢ diffFreqs ρ l₂) ×ˢ mWindow) ×ˢ mWindow

/-- The `M₀`-factor of a term of `symD`. -/
def symDF (P : ℤ[X]) (N : ℕ)
    (k : ((Analysis.IonescuWainger.Circle × Analysis.IonescuWainger.Circle) × ℤ) × ℤ) :
    ℝ → ℝ → ℂ :=
  fun a b => M0 P N (perQ k.1.1.1 k.1.1.2) k.1.1.1 k.1.1.2
    (a - gamR k.1.1.1 + (k.1.2 : ℝ)) (b - gamR k.1.1.2 + (k.2 : ℝ))

/-- The `φ_N`-factor of a term of `symD`. -/
def symDPhi (N k₁ : ℕ)
    (k : ((Analysis.IonescuWainger.Circle × Analysis.IonescuWainger.Circle) × ℤ) × ℤ) : ℝ → ℂ :=
  fun a => varphiN N k₁ (a - gamR k.1.1.1 + (k.1.2 : ℝ))

/-- The `φ̃_N`-factor of a term of `symD`. -/
def symDPsi (P : ℤ[X]) (N k₂ : ℕ)
    (k : ((Analysis.IonescuWainger.Circle × Analysis.IonescuWainger.Circle) × ℤ) × ℤ) : ℝ → ℂ :=
  fun b => varphitildeN P.natDegree N k₂ (b - gamR k.1.1.2 + (k.2 : ℝ))

theorem symDF_apply (P : ℤ[X]) (N k₁ k₂ : ℕ) (γ₁ γ₂ : Analysis.IonescuWainger.Circle)
    (m₁ m₂ : ℤ) (x y : ℝ) :
    symDF P N (((γ₁, γ₂), m₁), m₂) x y * symDPhi N k₁ (((γ₁, γ₂), m₁), m₂) x
      * symDPsi P N k₂ (((γ₁, γ₂), m₁), m₂) y
      = symDTerm P N k₁ k₂ γ₁ γ₂ m₁ m₂ x y := rfl

/-- **The finite-window form of `symD`, indexed by the product finset.** -/
theorem symD_eq_window_finset (ρ : ℝ) (P : ℤ[X]) (N l₁ l₂ k₁ k₂ : ℕ) (hd : 1 ≤ P.natDegree)
    (hk₁ : k₁ + 3 ≤ (Work.Analysis.EndVar.logN N).toNat)
    (hk₂ : k₂ + 3 ≤ (Work.Analysis.EndVar.logN N).toNat)
    {x y : ℝ} (hx : |x| ≤ 4) (hy : |y| ≤ 4) :
    symD ρ P N l₁ l₂ k₁ k₂ x y =
      ∑ k ∈ symIdx ρ l₁ l₂, symDF P N k x y * symDPhi N k₁ k x * symDPsi P N k₂ k y := by
  rw [symD_eq_window ρ P N l₁ l₂ k₁ k₂ hd hk₁ hk₂ hx hy]
  simp only [symIdx, Finset.sum_product]
  refine Finset.sum_congr rfl (fun γ₁ h₁ => Finset.sum_congr rfl (fun γ₂ h₂ =>
    Finset.sum_congr rfl (fun m₁ h₃ => Finset.sum_congr rfl (fun m₂ h₄ => ?_))))
  exact (symDF_apply P N k₁ k₂ γ₁ γ₂ m₁ m₂ x y).symm

/-! ## Smoothness of the differentiated symbol along the two coordinate axes -/

/-- `M0deriv` at `(0,0)` is `M0` itself. -/
theorem M0deriv_zero_zero (P : Polynomial ℤ) (N q : ℕ)
    (α₁ α₂ : Analysis.IonescuWainger.Circle) (x y : ℝ) :
    M0deriv P N q α₁ α₂ x y 0 0 = M0 P N q α₁ α₂ x y := by
  have hsum : (∑ n ∈ Finset.Ioc (N / 2) N, momPhaseDeriv P N α₁ α₂ x y (n : ℤ) 0 0)
      = ∑ n ∈ Finset.Ioc (N / 2) N, momPhase P N α₁ α₂ x y (n : ℤ) := by
    refine Finset.sum_congr rfl (fun n _ => ?_)
    simp only [momPhaseDeriv, pow_zero, mul_one]
  have hint : mTildeDeriv P N x y 0 0 = mTilde P N x y := by
    rw [mTildeDeriv, mTilde]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    simp only [pow_zero, mul_one]
  rw [M0deriv, M0, weylAvg, hsum, hint]

theorem deriv_M0deriv_fst (P : Polynomial ℤ) (N q : ℕ) (α₁ α₂ : Analysis.IonescuWainger.Circle)
    (y : ℝ) (i₁ i₂ : ℕ) :
    deriv (fun a : ℝ => M0deriv P N q α₁ α₂ a y i₁ i₂)
      = fun a : ℝ => M0deriv P N q α₁ α₂ a y (i₁ + 1) i₂ := by
  funext a
  have hfun : (fun a' : ℝ => M0deriv P N q α₁ α₂ a' y i₁ i₂)
      = (fun a' : ℝ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
            momPhaseDeriv P N α₁ α₂ a' y (n : ℤ) i₁ i₂)
        - (fun a' : ℝ => mZ P q α₁ α₂ * mTildeDeriv P N a' y i₁ i₂) := rfl
  have h1 : HasDerivAt (fun a' : ℝ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
        momPhaseDeriv P N α₁ α₂ a' y (n : ℤ) i₁ i₂)
      ((N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
        momPhaseDeriv P N α₁ α₂ a y (n : ℤ) (i₁ + 1) i₂) a :=
    HasDerivAt.const_mul _ (HasDerivAt.fun_sum (u := Finset.Ioc (N / 2) N)
      (fun n _ => M0Aux.hasDerivAt_momPhaseDeriv_fst P N α₁ α₂ y (n : ℤ) i₁ i₂ a))
  have h2 : HasDerivAt (fun a' : ℝ => mZ P q α₁ α₂ * mTildeDeriv P N a' y i₁ i₂)
      (mZ P q α₁ α₂ * mTildeDeriv P N a y (i₁ + 1) i₂) a :=
    (M0Aux.hasDerivAt_mTildeDeriv_fst P N y i₁ i₂ a).const_mul _
  have h := h1.sub h2
  have hval : ((N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
        momPhaseDeriv P N α₁ α₂ a y (n : ℤ) (i₁ + 1) i₂)
      - mZ P q α₁ α₂ * mTildeDeriv P N a y (i₁ + 1) i₂
      = M0deriv P N q α₁ α₂ a y (i₁ + 1) i₂ := rfl
  rw [hfun]
  rw [← hval]
  exact h.deriv

theorem iteratedDeriv_M0deriv_fst (P : Polynomial ℤ) (N q : ℕ)
    (α₁ α₂ : Analysis.IonescuWainger.Circle) (y : ℝ) (i₁ i₂ m : ℕ) :
    iteratedDeriv m (fun a : ℝ => M0deriv P N q α₁ α₂ a y i₁ i₂)
      = fun a : ℝ => M0deriv P N q α₁ α₂ a y (i₁ + m) i₂ := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [iteratedDeriv_succ, ih, deriv_M0deriv_fst]
      simp [Nat.add_assoc]

theorem differentiable_M0deriv_fst (P : Polynomial ℤ) (N q : ℕ)
    (α₁ α₂ : Analysis.IonescuWainger.Circle) (y : ℝ) (i₁ i₂ : ℕ) :
    Differentiable ℝ (fun a : ℝ => M0deriv P N q α₁ α₂ a y i₁ i₂) := by
  have hfun : (fun a : ℝ => M0deriv P N q α₁ α₂ a y i₁ i₂)
      = (fun a : ℝ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
            momPhaseDeriv P N α₁ α₂ a y (n : ℤ) i₁ i₂)
        - (fun a : ℝ => mZ P q α₁ α₂ * mTildeDeriv P N a y i₁ i₂) := rfl
  rw [hfun]
  refine Differentiable.sub ?_ ?_
  · exact (Differentiable.fun_sum (u := Finset.Ioc (N / 2) N)
      (fun n _ => M0Aux.differentiable_momPhaseDeriv_fst P N α₁ α₂ y (n : ℤ) i₁ i₂)).const_mul _
  · exact (M0Aux.differentiable_mTildeDeriv_fst P N y i₁ i₂).const_mul _

theorem differentiable_M0deriv_snd_zero (P : Polynomial ℤ) (N q : ℕ)
    (α₁ α₂ : Analysis.IonescuWainger.Circle) (a : ℝ) (i₂ : ℕ) :
    Differentiable ℝ (fun b : ℝ => M0deriv P N q α₁ α₂ a b 0 i₂) := by
  have hfun : (fun b : ℝ => M0deriv P N q α₁ α₂ a b 0 i₂)
      = (fun b : ℝ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
            momPhaseDeriv P N α₁ α₂ a b (n : ℤ) 0 i₂)
        - (fun b : ℝ => mZ P q α₁ α₂ * mTildeDeriv P N a b 0 i₂) := rfl
  rw [hfun]
  refine Differentiable.sub ?_ ?_
  · exact (Differentiable.fun_sum (u := Finset.Ioc (N / 2) N)
      (fun n _ => M0Aux.differentiable_momPhaseDeriv_snd P N α₁ α₂ a (n : ℤ) 0 i₂)).const_mul _
  · exact (M0Aux.differentiable_mTildeDeriv_snd P N a i₂).const_mul _

theorem M0deriv_contDiff_two_fst (P : Polynomial ℤ) (N q : ℕ)
    (α₁ α₂ : Analysis.IonescuWainger.Circle) (y : ℝ) (i₁ i₂ : ℕ) :
    ContDiff ℝ 2 (fun a : ℝ => M0deriv P N q α₁ α₂ a y i₁ i₂) := by
  refine contDiff_of_differentiable_iteratedDeriv (fun m hm => ?_)
  rw [iteratedDeriv_M0deriv_fst]
  exact differentiable_M0deriv_fst P N q α₁ α₂ y (i₁ + m) i₂

theorem deriv_M0deriv_snd_zero (P : Polynomial ℤ) (N q : ℕ)
    (α₁ α₂ : Analysis.IonescuWainger.Circle) (a : ℝ) (j : ℕ) :
    deriv (fun b : ℝ => M0deriv P N q α₁ α₂ a b 0 j)
      = fun b : ℝ => M0deriv P N q α₁ α₂ a b 0 (j + 1) := by
  funext b
  have hfun : (fun b' : ℝ => M0deriv P N q α₁ α₂ a b' 0 j)
      = (fun b' : ℝ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
            momPhaseDeriv P N α₁ α₂ a b' (n : ℤ) 0 j)
        - (fun b' : ℝ => mZ P q α₁ α₂ * mTildeDeriv P N a b' 0 j) := rfl
  have h1 : HasDerivAt (fun b' : ℝ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
        momPhaseDeriv P N α₁ α₂ a b' (n : ℤ) 0 j)
      ((N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
        momPhaseDeriv P N α₁ α₂ a b (n : ℤ) 0 (j + 1)) b :=
    HasDerivAt.const_mul _ (HasDerivAt.fun_sum (u := Finset.Ioc (N / 2) N)
      (fun n _ => M0Aux.hasDerivAt_momPhaseDeriv_snd P N α₁ α₂ a (n : ℤ) 0 j b))
  have h2 : HasDerivAt (fun b' : ℝ => mZ P q α₁ α₂ * mTildeDeriv P N a b' 0 j)
      (mZ P q α₁ α₂ * mTildeDeriv P N a b 0 (j + 1)) b :=
    (M0Aux.hasDerivAt_mTildeDeriv_snd P N a j b).const_mul _
  have h := h1.sub h2
  have hval : ((N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
        momPhaseDeriv P N α₁ α₂ a b (n : ℤ) 0 (j + 1))
      - mZ P q α₁ α₂ * mTildeDeriv P N a b 0 (j + 1)
      = M0deriv P N q α₁ α₂ a b 0 (j + 1) := rfl
  rw [hfun]
  rw [← hval]
  exact h.deriv

/-- The iterated derivative of `M0` in its *second* variable is `M0deriv` with first index `0`. -/
theorem iteratedDeriv_M0_snd (P : Polynomial ℤ) (N q : ℕ)
    (α₁ α₂ : Analysis.IonescuWainger.Circle) (a : ℝ) (m : ℕ) :
    iteratedDeriv m (fun b : ℝ => M0 P N q α₁ α₂ a b)
      = fun b : ℝ => M0deriv P N q α₁ α₂ a b 0 m := by
  induction m with
  | zero =>
      funext b
      rw [iteratedDeriv_zero]
      exact (M0deriv_zero_zero P N q α₁ α₂ a b).symm
  | succ m ih =>
      rw [iteratedDeriv_succ, ih, deriv_M0deriv_snd_zero]

theorem M0_contDiff_two_snd (P : Polynomial ℤ) (N q : ℕ)
    (α₁ α₂ : Analysis.IonescuWainger.Circle) (a : ℝ) :
    ContDiff ℝ 2 (fun b : ℝ => M0 P N q α₁ α₂ a b) := by
  refine contDiff_of_differentiable_iteratedDeriv (n := (2 : ℕ∞)) (fun m hm => ?_)
  rw [iteratedDeriv_M0_snd P N q α₁ α₂ a m]
  exact differentiable_M0deriv_snd_zero P N q α₁ α₂ a m

/-- The iterated derivatives of a shift of `M0deriv` in its first variable. -/
theorem M0deriv_contDiff_two_fst_comp (P : Polynomial ℤ) (N q : ℕ)
    (α₁ α₂ : Analysis.IonescuWainger.Circle) (y s : ℝ) (i₁ i₂ : ℕ) :
    ContDiff ℝ 2 (fun a : ℝ => M0deriv P N q α₁ α₂ (a + s) y i₁ i₂) := by
  have h1 : ContDiff ℝ 2 (fun a : ℝ => M0deriv P N q α₁ α₂ a y i₁ i₂) :=
    M0deriv_contDiff_two_fst P N q α₁ α₂ y i₁ i₂
  have h2 : ContDiff ℝ 2 (fun a : ℝ => a + s) := by fun_prop
  simpa [Function.comp_def] using h1.comp h2

/-! ## The Leibniz expansion of `dp` on the finite sum forms of `symD` -/

lemma fun_sum_eq {ι : Type*} (S : Finset ι) (g : ι → ℝ → ℂ) :
    (fun b : ℝ => ∑ k ∈ S, g k b) = ∑ k ∈ S, g k := by
  funext b
  simp [Finset.sum_apply]

theorem dp_finset_sum_mul_three {ι : Type*} (S : Finset ι) (F : ι → ℝ → ℝ → ℂ)
    (φ ψ : ι → ℝ → ℂ)
    (j₁ j₂ : ℕ) (hj₁ : j₁ ≤ 2) (hj₂ : j₂ ≤ 2) (y : ℝ) (x : ℝ)
    (hFb : ∀ k ∈ S, ∀ a : ℝ, ContDiff ℝ 2 (fun b : ℝ => F k a b))
    (hFc : ∀ k ∈ S, ∀ i₂ : ℕ, i₂ ≤ j₂ →
      ContDiff ℝ 2 (fun a : ℝ => iteratedDeriv i₂ (fun b : ℝ => F k a b) y))
    (hφ : ∀ k ∈ S, ContDiff ℝ 2 (φ k)) (hψ : ∀ k ∈ S, ContDiff ℝ 2 (ψ k)) :
    dp j₁ j₂ (fun a b => ∑ k ∈ S, F k a b * φ k a * ψ k b) x y
      = ∑ k ∈ S, ∑ i₂ ∈ Finset.range (j₂ + 1), ∑ i₁ ∈ Finset.range (j₁ + 1),
          ((j₂.choose i₂ : ℂ) * (j₁.choose i₁ : ℂ))
            * (iteratedDeriv i₁ (φ k) x)
            * (iteratedDeriv (j₁ - i₁) (fun a => iteratedDeriv i₂ (fun b => F k a b) y) x)
            * (iteratedDeriv (j₂ - i₂) (ψ k) y) := by
  have hj₂' : (j₂ : WithTop ℕ∞) ≤ 2 := by exact_mod_cast hj₂
  have hj₁' : (j₁ : WithTop ℕ∞) ≤ 2 := by exact_mod_cast hj₁
  have hstep1 : (fun a : ℝ => iteratedDeriv j₂ (fun b : ℝ => ∑ k ∈ S, F k a b * φ k a * ψ k b) y)
      = fun a : ℝ => ∑ k ∈ S, φ k a * (∑ i₂ ∈ Finset.range (j₂ + 1),
          (j₂.choose i₂ : ℂ) * iteratedDeriv i₂ (fun b : ℝ => F k a b) y
            * iteratedDeriv (j₂ - i₂) (ψ k) y) := by
    funext a
    rw [fun_sum_eq S (fun k b => F k a b * φ k a * ψ k b)]
    rw [iteratedDeriv_sum (f := fun k b => F k a b * φ k a * ψ k b) (I := S) (x := y)
      (fun k hk => ((((hFb k hk a).contDiffAt).of_le hj₂').mul contDiffAt_const).mul
        (((hψ k hk).contDiffAt).of_le hj₂'))]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hA : ContDiffAt ℝ (j₂ : WithTop ℕ∞) (fun b : ℝ => F k a b) y :=
      ((hFb k hk a).contDiffAt).of_le hj₂'
    have hB : ContDiffAt ℝ (j₂ : WithTop ℕ∞) (ψ k) y := ((hψ k hk).contDiffAt).of_le hj₂'
    have hfun : (fun b : ℝ => F k a b * φ k a * ψ k b)
        = fun b : ℝ => φ k a * (F k a b * ψ k b) := by
      funext b; ring
    rw [hfun, iteratedDeriv_const_mul (φ k a) (hA.mul hB)]
    rw [show (fun b : ℝ => F k a b * ψ k b) = (fun b : ℝ => F k a b) * (ψ k) from rfl,
      iteratedDeriv_mul hA hB]
  change iteratedDeriv j₁
    (fun a : ℝ => iteratedDeriv j₂ (fun b : ℝ => ∑ k ∈ S, F k a b * φ k a * ψ k b) y) x = _
  rw [hstep1]
  rw [fun_sum_eq S (fun k a => φ k a * (∑ i₂ ∈ Finset.range (j₂ + 1),
          (j₂.choose i₂ : ℂ) * iteratedDeriv i₂ (fun b : ℝ => F k a b) y
            * iteratedDeriv (j₂ - i₂) (ψ k) y))]
  rw [iteratedDeriv_sum (f := fun k a => φ k a * (∑ i₂ ∈ Finset.range (j₂ + 1),
          (j₂.choose i₂ : ℂ) * iteratedDeriv i₂ (fun b : ℝ => F k a b) y
            * iteratedDeriv (j₂ - i₂) (ψ k) y)) (I := S) (x := x)
      (fun k hk => (((hφ k hk).contDiffAt).of_le hj₁').mul (by
        refine ContDiffAt.sum (fun i₂ hi₂ => ?_)
        exact ((contDiffAt_const (c := (j₂.choose i₂ : ℂ))).mul
          (((hFc k hk i₂ (by have := Finset.mem_range.mp hi₂; omega)).contDiffAt).of_le
            hj₁')).mul contDiffAt_const))]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hkeq : (fun a : ℝ => φ k a * (∑ i₂ ∈ Finset.range (j₂ + 1),
        (j₂.choose i₂ : ℂ) * iteratedDeriv i₂ (fun b : ℝ => F k a b) y
          * iteratedDeriv (j₂ - i₂) (ψ k) y))
      = ∑ i₂ ∈ Finset.range (j₂ + 1), (fun a : ℝ => ((j₂.choose i₂ : ℂ)
          * iteratedDeriv (j₂ - i₂) (ψ k) y)
          * (φ k a * iteratedDeriv i₂ (fun b : ℝ => F k a b) y)) := by
    funext a
    rw [Finset.sum_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i₂ _ => by ring)
  rw [hkeq]
  rw [iteratedDeriv_sum (f := fun i₂ a => ((j₂.choose i₂ : ℂ)
        * iteratedDeriv (j₂ - i₂) (ψ k) y) * (φ k a * iteratedDeriv i₂ (fun b : ℝ => F k a b) y))
      (I := Finset.range (j₂ + 1)) (x := x) (fun i₂ hi₂ => contDiffAt_const.mul
        ((((hφ k hk).contDiffAt).of_le hj₁').mul
          (((hFc k hk i₂ (by have := Finset.mem_range.mp hi₂; omega)).contDiffAt).of_le hj₁')))]
  refine Finset.sum_congr rfl (fun i₂ hi₂ => ?_)
  have hi₂' : i₂ ≤ j₂ := by have := Finset.mem_range.mp hi₂; omega
  have hA : ContDiffAt ℝ (j₁ : WithTop ℕ∞) (fun a : ℝ => φ k a) x :=
    ((hφ k hk).contDiffAt).of_le hj₁'
  have hB : ContDiffAt ℝ (j₁ : WithTop ℕ∞)
      (fun a : ℝ => iteratedDeriv i₂ (fun b : ℝ => F k a b) y) x :=
    ((hFc k hk i₂ hi₂').contDiffAt).of_le hj₁'
  rw [iteratedDeriv_const_mul (f := fun a : ℝ => φ k a * iteratedDeriv i₂ (fun b : ℝ => F k a b) y)
    ((j₂.choose i₂ : ℂ) * iteratedDeriv (j₂ - i₂) (ψ k) y) (hA.mul hB)]
  rw [show (fun a : ℝ => φ k a * iteratedDeriv i₂ (fun b : ℝ => F k a b) y)
        = (φ k) * (fun a : ℝ => iteratedDeriv i₂ (fun b : ℝ => F k a b) y) from rfl,
      iteratedDeriv_mul hA hB]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i₁ _ => ?_)
  ring

/-! ## The mixed partials of the terms of `symD` -/

theorem iteratedDeriv_symDPhi (N k₁ : ℕ)
    (k : ((Analysis.IonescuWainger.Circle × Analysis.IonescuWainger.Circle) × ℤ) × ℤ) (m : ℕ) :
    iteratedDeriv m (symDPhi N k₁ k)
      = fun x : ℝ => iteratedDeriv m (varphiN N k₁) (x - gamR k.1.1.1 + (k.1.2 : ℝ)) := by
  have hfun : symDPhi N k₁ k
      = fun a : ℝ => varphiN N k₁ (a + ((k.1.2 : ℝ) - gamR k.1.1.1)) := by
    funext a
    simp only [symDPhi]
    rw [show a - gamR k.1.1.1 + (k.1.2 : ℝ) = a + ((k.1.2 : ℝ) - gamR k.1.1.1) from by ring]
  rw [hfun, iteratedDeriv_comp_add_const]
  funext x
  rw [show x + ((k.1.2 : ℝ) - gamR k.1.1.1) = x - gamR k.1.1.1 + (k.1.2 : ℝ) from by ring]

theorem iteratedDeriv_symDPsi (P : ℤ[X]) (N k₂ : ℕ)
    (k : ((Analysis.IonescuWainger.Circle × Analysis.IonescuWainger.Circle) × ℤ) × ℤ) (m : ℕ) :
    iteratedDeriv m (symDPsi P N k₂ k)
      = fun x : ℝ => iteratedDeriv m (varphitildeN P.natDegree N k₂)
          (x - gamR k.1.1.2 + (k.2 : ℝ)) := by
  have hfun : symDPsi P N k₂ k
      = fun a : ℝ => varphitildeN P.natDegree N k₂ (a + ((k.2 : ℝ) - gamR k.1.1.2)) := by
    funext a
    simp only [symDPsi]
    rw [show a - gamR k.1.1.2 + (k.2 : ℝ) = a + ((k.2 : ℝ) - gamR k.1.1.2) from by ring]
  rw [hfun, iteratedDeriv_comp_add_const]
  funext x
  rw [show x + ((k.2 : ℝ) - gamR k.1.1.2) = x - gamR k.1.1.2 + (k.2 : ℝ) from by ring]

theorem symDF_iteratedDeriv (P : ℤ[X]) (N k₁ k₂ : ℕ)
    (k : ((Analysis.IonescuWainger.Circle × Analysis.IonescuWainger.Circle) × ℤ) × ℤ)
    (i₁ i₂ : ℕ) (hi₁ : i₁ ≤ 2) (hi₂ : i₂ ≤ 2) (x y : ℝ) :
    iteratedDeriv i₁ (fun a : ℝ => iteratedDeriv i₂ (fun b : ℝ => symDF P N k a b) y) x
      = M0deriv P N (perQ k.1.1.1 k.1.1.2) k.1.1.1 k.1.1.2
          (x - gamR k.1.1.1 + (k.1.2 : ℝ)) (y - gamR k.1.1.2 + (k.2 : ℝ)) i₁ i₂ := by
  have hstep : (fun a : ℝ => iteratedDeriv i₂ (fun b : ℝ => symDF P N k a b) y)
      = fun a : ℝ => iteratedDeriv i₂
          (fun b : ℝ => M0 P N (perQ k.1.1.1 k.1.1.2) k.1.1.1 k.1.1.2
            (a + ((k.1.2 : ℝ) - gamR k.1.1.1)) b) (y + ((k.2 : ℝ) - gamR k.1.1.2)) := by
    funext a
    have hfe : (fun b : ℝ => symDF P N k a b)
        = fun b : ℝ => (fun b' : ℝ => M0 P N (perQ k.1.1.1 k.1.1.2) k.1.1.1 k.1.1.2
            (a + ((k.1.2 : ℝ) - gamR k.1.1.1)) b') (b + ((k.2 : ℝ) - gamR k.1.1.2)) := by
      funext b
      simp only [symDF]
      rw [show a - gamR k.1.1.1 + (k.1.2 : ℝ) = a + ((k.1.2 : ℝ) - gamR k.1.1.1) from by ring,
        show b - gamR k.1.1.2 + (k.2 : ℝ) = b + ((k.2 : ℝ) - gamR k.1.1.2) from by ring]
    rw [hfe, iteratedDeriv_comp_add_const]
  rw [hstep]
  have hgoal : iteratedDeriv i₁ (fun a : ℝ => iteratedDeriv i₂
        (fun b : ℝ => M0 P N (perQ k.1.1.1 k.1.1.2) k.1.1.1 k.1.1.2
          (a + ((k.1.2 : ℝ) - gamR k.1.1.1)) b) (y + ((k.2 : ℝ) - gamR k.1.1.2))) x
      = iteratedDeriv i₁ (fun u : ℝ => iteratedDeriv i₂
        (fun b : ℝ => M0 P N (perQ k.1.1.1 k.1.1.2) k.1.1.1 k.1.1.2 u b)
          (y + ((k.2 : ℝ) - gamR k.1.1.2))) (x + ((k.1.2 : ℝ) - gamR k.1.1.1)) :=
    congrFun (iteratedDeriv_comp_add_const i₁ (fun u : ℝ => iteratedDeriv i₂
      (fun b : ℝ => M0 P N (perQ k.1.1.1 k.1.1.2) k.1.1.1 k.1.1.2 u b)
        (y + ((k.2 : ℝ) - gamR k.1.1.2))) ((k.1.2 : ℝ) - gamR k.1.1.1)) x
  rw [hgoal]
  have h := M0_iteratedDeriv P N (perQ k.1.1.1 k.1.1.2) k.1.1.1 k.1.1.2 hi₁ hi₂
    (x + ((k.1.2 : ℝ) - gamR k.1.1.1)) (y + ((k.2 : ℝ) - gamR k.1.1.2))
  rw [h]
  rw [show x + ((k.1.2 : ℝ) - gamR k.1.1.1) = x - gamR k.1.1.1 + (k.1.2 : ℝ) from by ring,
    show y + ((k.2 : ℝ) - gamR k.1.1.2) = y - gamR k.1.1.2 + (k.2 : ℝ) from by ring]

/-! ## Support of the derivatives of the bumps -/

theorem iteratedDeriv_varphiN_eq_zero_of_radius (N k m : ℕ) {ξ : ℝ}
    (h : (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) < |ξ|) :
    iteratedDeriv m (varphiN N k) ξ = 0 := by
  have hpos : 0 < (|ξ| - (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) / 2 := by
    linarith
  have heq : (varphiN N k) =ᶠ[𝓝 ξ] (fun _ => (0 : ℂ)) := by
    filter_upwards [Metric.ball_mem_nhds ξ hpos] with x hx
    refine varphiN_eq_zero_of_lt ?_
    have h1 : dist x ξ < (|ξ| - (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) / 2 := hx
    rw [dist_eq_norm, Real.norm_eq_abs] at h1
    have h2 : |ξ| - |x| ≤ |x - ξ| := by
      have h3 := abs_sub_abs_le_abs_sub ξ x
      rw [abs_sub_comm] at h3
      exact h3
    linarith
  rw [Filter.EventuallyEq.iteratedDeriv_eq m heq]
  simp

theorem varphitildeN_eq_zero_of_lt {d N k : ℕ} (hd : 1 ≤ d) {ξ : ℝ}
    (h : (2 : ℝ) ^ ((d : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) < |ξ|) :
    varphitildeN d N k ξ = 0 := by
  by_contra hne
  exact absurd (varphitildeN_ne_zero_abs_le d N k hd hne) (not_le.mpr h)

theorem iteratedDeriv_varphitildeN_eq_zero_of_radius (d N k m : ℕ) (hd : 1 ≤ d) {ξ : ℝ}
    (h : (2 : ℝ) ^ ((d : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) < |ξ|) :
    iteratedDeriv m (varphitildeN d N k) ξ = 0 := by
  have hpos : 0 < (|ξ| - (2 : ℝ) ^ ((d : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))) / 2 := by
    linarith
  have heq : (varphitildeN d N k) =ᶠ[𝓝 ξ] (fun _ => (0 : ℂ)) := by
    filter_upwards [Metric.ball_mem_nhds ξ hpos] with x hx
    refine varphitildeN_eq_zero_of_lt hd ?_
    have h1 : dist x ξ < (|ξ|
        - (2 : ℝ) ^ ((d : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))) / 2 := hx
    rw [dist_eq_norm, Real.norm_eq_abs] at h1
    have h2 : |ξ| - |x| ≤ |x - ξ| := by
      have h3 := abs_sub_abs_le_abs_sub ξ x
      rw [abs_sub_comm] at h3
      exact h3
    linarith
  rw [Filter.EventuallyEq.iteratedDeriv_eq m heq]
  simp

/-! ## The pointwise bound for the derivatives of `symD` -/

theorem uScale_pos {ρ : ℝ} (hρ : 0 ≤ ρ) (L : ℕ) : 1 ≤ Work.KMTAreas.A7.uScale ρ L := by
  rw [Work.KMTAreas.A7.uScale, Work.Analysis.EndVar.scaleCount]
  have hpow : ((1 : ℤ) : ℝ) ≤ ((1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * ρ * (L : ℝ)) := by
    rw [Nat.cast_one, Int.cast_one, one_mul]
    exact Real.one_le_rpow (by norm_num) (by positivity)
  have hfl : (1 : ℤ) ≤ ⌊((1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋ :=
    Int.le_floor.mpr hpow
  have h0 : (0 : ℤ) ≤ ⌊((1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋ :=
    le_trans (by norm_num) hfl
  have h3 : (1 : ℤ) ≤ ((⌊((1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋.toNat : ℕ) : ℤ) := by
    rw [Int.toNat_of_nonneg h0]
    exact hfl
  exact_mod_cast h3

theorem le_logN_toNat (N l₁ l₂ k₁ k₂ : ℕ) {ρ : ℝ} (hρ : 0 < ρ)
    (hC2 : max k₁ k₂ + 2 * Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂) + 1
      ≤ (Work.Analysis.EndVar.logN N).toNat) {k : ℕ} (hk : k ≤ max k₁ k₂) :
    k + 3 ≤ (Work.Analysis.EndVar.logN N).toNat := by
  have hu : 1 ≤ Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂) := uScale_pos (le_of_lt hρ) _
  omega

/-! ## Smoothness of the pieces of a term of `symD` -/

theorem contDiff_symDPhi (N k₁ : ℕ)
    (k : ((Analysis.IonescuWainger.Circle × Analysis.IonescuWainger.Circle) × ℤ) × ℤ) :
    ContDiff ℝ 2 (symDPhi N k₁ k) := by
  have h : ContDiff ℝ 2 (fun a : ℝ => a - gamR k.1.1.1 + (k.1.2 : ℝ)) := by fun_prop
  exact (contDiff_varphiN N k₁).comp h

theorem contDiff_symDPsi (P : ℤ[X]) (N k₂ : ℕ)
    (k : ((Analysis.IonescuWainger.Circle × Analysis.IonescuWainger.Circle) × ℤ) × ℤ) :
    ContDiff ℝ 2 (symDPsi P N k₂ k) := by
  have h : ContDiff ℝ 2 (fun b : ℝ => b - gamR k.1.1.2 + (k.2 : ℝ)) := by fun_prop
  exact (contDiff_varphitildeN P.natDegree N k₂).comp h

theorem contDiff_symDF_snd (P : ℤ[X]) (N : ℕ)
    (k : ((Analysis.IonescuWainger.Circle × Analysis.IonescuWainger.Circle) × ℤ) × ℤ) (a : ℝ) :
    ContDiff ℝ 2 (fun b : ℝ => symDF P N k a b) := by
  have h1 : ContDiff ℝ 2 (fun b : ℝ => M0 P N (perQ k.1.1.1 k.1.1.2) k.1.1.1 k.1.1.2
      (a - gamR k.1.1.1 + (k.1.2 : ℝ)) b) :=
    M0_contDiff_two_snd P N (perQ k.1.1.1 k.1.1.2) k.1.1.1 k.1.1.2
      (a - gamR k.1.1.1 + (k.1.2 : ℝ))
  have h2 : ContDiff ℝ 2 (fun b : ℝ => M0 P N (perQ k.1.1.1 k.1.1.2) k.1.1.1 k.1.1.2
      (a - gamR k.1.1.1 + (k.1.2 : ℝ)) (b - gamR k.1.1.2 + (k.2 : ℝ))) :=
    h1.comp (by fun_prop)
  simpa [symDF] using h2

theorem contDiff_iteratedDeriv_symDF (P : ℤ[X]) (N k₁ k₂ : ℕ)
    (k : ((Analysis.IonescuWainger.Circle × Analysis.IonescuWainger.Circle) × ℤ) × ℤ)
    (i₂ : ℕ) (hi₂ : i₂ ≤ 2) (y : ℝ) :
    ContDiff ℝ 2 (fun a : ℝ => iteratedDeriv i₂ (fun b : ℝ => symDF P N k a b) y) := by
  have hgoal : (fun a : ℝ => iteratedDeriv i₂ (fun b : ℝ => symDF P N k a b) y)
      = (fun a : ℝ => M0deriv P N (perQ k.1.1.1 k.1.1.2) k.1.1.1 k.1.1.2
          (a + ((k.1.2 : ℝ) - gamR k.1.1.1))
          (y + ((k.2 : ℝ) - gamR k.1.1.2)) 0 i₂) := by
    funext a
    have h := symDF_iteratedDeriv P N k₁ k₂ k 0 i₂ (by norm_num) hi₂ a y
    rw [iteratedDeriv_zero] at h
    rw [h]
    congr 1 <;> ring
  rw [hgoal]
  exact M0deriv_contDiff_two_fst_comp P N (perQ k.1.1.1 k.1.1.2) k.1.1.1 k.1.1.2
      (y + ((k.2 : ℝ) - gamR k.1.1.2)) ((k.1.2 : ℝ) - gamR k.1.1.1) 0 i₂

/-! ## The Leibniz identity for `symD` -/

theorem dp_symD_eq_leibniz (ρ : ℝ) (P : ℤ[X]) (N l₁ l₂ k₁ k₂ : ℕ) (hd : 2 ≤ P.natDegree)
    (hk₁ : k₁ + 3 ≤ (Work.Analysis.EndVar.logN N).toNat)
    (hk₂ : k₂ + 3 ≤ (Work.Analysis.EndVar.logN N).toNat)
    (j₁ j₂ : ℕ) (hj₁ : j₁ ≤ 2) (hj₂ : j₂ ≤ 2) {x y : ℝ} (hx : |x| < 4) (hy : |y| < 4) :
    dp j₁ j₂ (symD ρ P N l₁ l₂ k₁ k₂) x y
      = ∑ k ∈ symIdx ρ l₁ l₂, ∑ i₂ ∈ Finset.range (j₂ + 1), ∑ i₁ ∈ Finset.range (j₁ + 1),
          ((j₂.choose i₂ : ℂ) * (j₁.choose i₁ : ℂ))
            * (iteratedDeriv i₁ (symDPhi N k₁ k) x)
            * (iteratedDeriv (j₁ - i₁) (fun a => iteratedDeriv i₂ (fun b => symDF P N k a b) y) x)
            * (iteratedDeriv (j₂ - i₂) (symDPsi P N k₂ k) y) := by
  have h2 : ∀ a : ℝ, |a| < 4 → (fun b : ℝ => symD ρ P N l₁ l₂ k₁ k₂ a b)
      =ᶠ[𝓝 y] (fun b : ℝ => ∑ k ∈ symIdx ρ l₁ l₂,
        symDF P N k a b * symDPhi N k₁ k a * symDPsi P N k₂ k b) := by
    intro a ha
    filter_upwards [Metric.ball_mem_nhds y (by linarith : (0 : ℝ) < 4 - |y|)] with b hb
    have hb4 : |b| < 4 := by
      have h1 : dist b y < 4 - |y| := hb
      rw [dist_eq_norm, Real.norm_eq_abs] at h1
      have h3 := abs_sub_abs_le_abs_sub b y
      linarith
    exact symD_eq_window_finset ρ P N l₁ l₂ k₁ k₂ (by omega) hk₁ hk₂ (le_of_lt ha) (le_of_lt hb4)
  have h3 : (fun a : ℝ => dp2 j₂ (symD ρ P N l₁ l₂ k₁ k₂) a y)
      =ᶠ[𝓝 x] (fun a : ℝ => dp2 j₂ (fun a b => ∑ k ∈ symIdx ρ l₁ l₂,
        symDF P N k a b * symDPhi N k₁ k a * symDPsi P N k₂ k b) a y) := by
    filter_upwards [Metric.ball_mem_nhds x (by linarith : (0 : ℝ) < 4 - |x|)] with a ha
    have ha4 : |a| < 4 := by
      have h1 : dist a x < 4 - |x| := ha
      rw [dist_eq_norm, Real.norm_eq_abs] at h1
      have h3 := abs_sub_abs_le_abs_sub a x
      linarith
    exact Filter.EventuallyEq.iteratedDeriv_eq j₂ (h2 a ha4)
  have h4 := Filter.EventuallyEq.iteratedDeriv_eq j₁ h3
  change iteratedDeriv j₁ (fun a : ℝ => dp2 j₂ (symD ρ P N l₁ l₂ k₁ k₂) a y) x = _
  rw [h4]
  change dp j₁ j₂ (fun a b => ∑ k ∈ symIdx ρ l₁ l₂,
    symDF P N k a b * symDPhi N k₁ k a * symDPsi P N k₂ k b) x y = _
  exact dp_finset_sum_mul_three (symIdx ρ l₁ l₂) (fun k => symDF P N k) (fun k => symDPhi N k₁ k)
    (fun k => symDPsi P N k₂ k) j₁ j₂ hj₁ hj₂ y x
    (fun k hk a => contDiff_symDF_snd P N k a)
    (fun k hk i₂ hi₂ => contDiff_iteratedDeriv_symDF P N k₁ k₂ k i₂ (le_trans hi₂ hj₂) y)
    (fun k hk => contDiff_symDPhi N k₁ k)
    (fun k hk => contDiff_symDPsi P N k₂ k)

/-! ## The pointwise bound -/

theorem choose_le_four {j i : ℕ} (hj : j ≤ 2) : ((j.choose i : ℕ) : ℝ) ≤ 4 := by
  have h1 : j.choose i ≤ 2 ^ j := Nat.choose_le_two_pow j i
  have h2 : 2 ^ j ≤ 4 := by interval_cases j <;> norm_num
  have h3 : j.choose i ≤ 4 := le_trans h1 h2
  exact_mod_cast h3

theorem le_pow_div_of_abs_le {N k : ℕ} (hN : 1 ≤ N) {ξ : ℝ}
    (hξ : |ξ| ≤ (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) :
    |ξ| ≤ (2 : ℝ) ^ (k + 1) / (N : ℝ) := by
  have hNle : (N : ℝ) ≤ (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) + 1) := by
    have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (max N 2)
    have h' : N ≤ 2 ^ (Nat.log 2 (max N 2) + 1) := le_trans (le_max_left _ _) (le_of_lt h)
    have h'' : ((N : ℕ) : ℝ) ≤ ((2 ^ (Nat.log 2 (max N 2) + 1) : ℕ) : ℝ) := by exact_mod_cast h'
    rw [Nat.cast_pow] at h''
    simp only [Nat.cast_ofNat] at h''
    rw [show ((2 : ℝ) ^ (Nat.log 2 (max N 2) + 1))
        = (2 : ℝ) ^ ((Nat.log 2 (max N 2) + 1 : ℕ) : ℝ) from
      (Real.rpow_natCast 2 (Nat.log 2 (max N 2) + 1)).symm] at h''
    have hL : ((Nat.log 2 (max N 2) + 1 : ℕ) : ℝ)
        = (Work.Analysis.EndVar.logN N : ℝ) + 1 := by
      rw [Work.Analysis.EndVar.logN]; push_cast; ring
    rwa [hL] at h''
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hk1 : (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) * (N : ℝ)
      ≤ (2 : ℝ) ^ ((k + 1 : ℕ) : ℝ) := by
    calc (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) * (N : ℝ)
        ≤ (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))
            * (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hNle (le_of_lt h2pos)
      _ = (2 : ℝ) ^ ((k + 1 : ℕ) : ℝ) := by
          rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
          congr 1
          push_cast
          ring
  have hk : (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) * (N : ℝ)
      ≤ (2 : ℝ) ^ (k + 1) := by
    rw [Real.rpow_natCast] at hk1
    exact hk1
  rw [le_div_iff₀ (by positivity : (0:ℝ) < (N:ℝ))]
  exact le_trans (mul_le_mul_of_nonneg_right hξ (by positivity)) hk

theorem le_pow_div_pow_of_abs_le {N k d : ℕ} (hN : 1 ≤ N) {ξ : ℝ}
    (hξ : |ξ| ≤ (2 : ℝ) ^ ((d : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))) :
    |ξ| ≤ (2 : ℝ) ^ (d * (k + 1)) / (N : ℝ) ^ d := by
  have hNle : (N : ℝ) ≤ (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) + 1) := by
    have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (max N 2)
    have h' : N ≤ 2 ^ (Nat.log 2 (max N 2) + 1) := le_trans (le_max_left _ _) (le_of_lt h)
    have h'' : ((N : ℕ) : ℝ) ≤ ((2 ^ (Nat.log 2 (max N 2) + 1) : ℕ) : ℝ) := by exact_mod_cast h'
    rw [Nat.cast_pow] at h''
    simp only [Nat.cast_ofNat] at h''
    rw [show ((2 : ℝ) ^ (Nat.log 2 (max N 2) + 1))
        = (2 : ℝ) ^ ((Nat.log 2 (max N 2) + 1 : ℕ) : ℝ) from
      (Real.rpow_natCast 2 (Nat.log 2 (max N 2) + 1)).symm] at h''
    have hL : ((Nat.log 2 (max N 2) + 1 : ℕ) : ℝ)
        = (Work.Analysis.EndVar.logN N : ℝ) + 1 := by
      rw [Work.Analysis.EndVar.logN]; push_cast; ring
    rwa [hL] at h''
  have hNd : (N : ℝ) ^ d ≤ ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) + 1)) ^ d :=
    pow_le_pow_left₀ (by positivity) hNle d
  have hexp : (2 : ℝ) ^ ((d : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))
        * ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) + 1)) ^ d
      = (2 : ℝ) ^ ((d * (k + 1) : ℕ) : ℝ) := by
    rw [show ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) + 1)) ^ d
        = (2 : ℝ) ^ (((Work.Analysis.EndVar.logN N : ℝ) + 1) * (d : ℝ)) by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) + 1)) d,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    push_cast
    ring
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) ^ d)]
  calc |ξ| * (N : ℝ) ^ d
      ≤ (2 : ℝ) ^ ((d : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) * (N : ℝ) ^ d :=
        mul_le_mul_of_nonneg_right hξ (by positivity)
    _ ≤ (2 : ℝ) ^ ((d : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))
          * ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) + 1)) ^ d :=
        mul_le_mul_of_nonneg_left hNd (by positivity)
    _ = (2 : ℝ) ^ ((d * (k + 1) : ℕ) : ℝ) := hexp
    _ = (2 : ℝ) ^ (d * (k + 1)) := by rw [Real.rpow_natCast]

theorem dp_symD_pointwise_le (ρ : ℝ) (P : ℤ[X]) (N l₁ l₂ k₁ k₂ : ℕ) (hd : 2 ≤ P.natDegree)
    (hN : 1 ≤ N) (hk₁ : k₁ + 3 ≤ (Work.Analysis.EndVar.logN N).toNat)
    (hk₂ : k₂ + 3 ≤ (Work.Analysis.EndVar.logN N).toNat)
    (j₁ j₂ : ℕ) (hj₁ : j₁ ≤ 2) (hj₂ : j₂ ≤ 2) {x y : ℝ} (hx : |x| < 4) (hy : |y| < 4)
    {C_M : ℝ} (hC_M : 0 ≤ C_M)
    (hM0 : ∀ (N q j₁ j₂ k₁ k₂ : ℕ) (α₁ α₂ : Analysis.IonescuWainger.Circle) (ξ₁ ξ₂ : ℝ),
      j₁ ≤ 2 → j₂ ≤ 2 → 1 ≤ N → 0 < q → q • α₁ = 0 → q • α₂ = 0 →
      |ξ₁| ≤ (2 : ℝ) ^ (k₁ + 1) / (N : ℝ) →
      |ξ₂| ≤ (2 : ℝ) ^ (P.natDegree * (k₂ + 1)) / (N : ℝ) ^ P.natDegree →
      ‖Work.KMTAreas.A7.M0deriv P N q α₁ α₂ ξ₁ ξ₂ j₁ j₂‖
        ≤ C_M * (q : ℝ) ^ 2
          * (1 + ((2 : ℝ) ^ k₁ + (2 : ℝ) ^ (P.natDegree * k₂)) ^ 2 / (N : ℝ))
          * (N : ℝ) ^ ((j₁ : ℤ) + (P.natDegree : ℤ) * (j₂ : ℤ) - 1)) :
    ‖dp j₁ j₂ (symD ρ P N l₁ l₂ k₁ k₂) x y‖
      ≤ ∑ k ∈ symIdx ρ l₁ l₂, ∑ i₂ ∈ Finset.range (j₂ + 1), ∑ i₁ ∈ Finset.range (j₁ + 1),
          (16 * (C_M * (perQ k.1.1.1 k.1.1.2) ^ 2
              * (1 + ((2 : ℝ) ^ k₁ + (2 : ℝ) ^ (P.natDegree * k₂)) ^ 2 / (N : ℝ))
              * (N : ℝ) ^ (((j₁ : ℤ) - (i₁ : ℤ)) + (P.natDegree : ℤ) * (i₂ : ℤ) - 1)))
          * ‖iteratedDeriv i₁ (symDPhi N k₁ k) x‖
          * ‖iteratedDeriv (j₂ - i₂) (symDPsi P N k₂ k) y‖ := by
  rw [dp_symD_eq_leibniz ρ P N l₁ l₂ k₁ k₂ hd hk₁ hk₂ j₁ j₂ hj₁ hj₂ hx hy]
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum (fun k hk => ?_)
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum (fun i₂ hi₂ => ?_)
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum (fun i₁ hi₁ => ?_)
  have hi₁' : i₁ ≤ j₁ := by have := Finset.mem_range.mp hi₁; omega
  have hi₂' : i₂ ≤ j₂ := by have := Finset.mem_range.mp hi₂; omega
  have hC : ‖((j₂.choose i₂ : ℂ) * (j₁.choose i₁ : ℂ))‖ ≤ 16 := by
    rw [norm_mul]
    have h1 := choose_le_four (j := j₂) (i := i₂) hj₂
    have h2 := choose_le_four (j := j₁) (i := i₁) hj₁
    rw [Complex.norm_natCast, Complex.norm_natCast]
    nlinarith [abs_of_nonneg (show (0:ℝ) ≤ ((j₂.choose i₂ : ℕ) : ℝ) by positivity),
      abs_of_nonneg (show (0:ℝ) ≤ ((j₁.choose i₁ : ℕ) : ℝ) by positivity)]
  have hsupp₁ : ‖iteratedDeriv i₁ (symDPhi N k₁ k) x‖ ≠ 0 →
      |x - gamR k.1.1.1 + (k.1.2 : ℝ)|
        ≤ (2 : ℝ) ^ ((k₁ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) := by
    intro h1
    by_contra hlt
    rw [not_le] at hlt
    refine h1 ?_
    simp only [iteratedDeriv_symDPhi N k₁ k i₁, iteratedDeriv_varphiN_eq_zero_of_radius N k₁ i₁ hlt,
      norm_zero]
  have hsupp₂ : ‖iteratedDeriv (j₂ - i₂) (symDPsi P N k₂ k) y‖ ≠ 0 →
      |y - gamR k.1.1.2 + (k.2 : ℝ)|
        ≤ (2 : ℝ) ^ ((P.natDegree : ℝ) * ((k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) := by
    intro h1
    by_contra hlt
    rw [not_le] at hlt
    refine h1 ?_
    simp only [iteratedDeriv_symDPsi P N k₂ k (j₂ - i₂),
      iteratedDeriv_varphitildeN_eq_zero_of_radius P.natDegree N k₂ (j₂ - i₂) (by omega) hlt,
      norm_zero]
  rw [norm_mul, norm_mul, norm_mul,
    symDF_iteratedDeriv P N k₁ k₂ k (j₁ - i₁) i₂ (by omega) (by omega) x y]
  by_cases h1 : ‖iteratedDeriv i₁ (symDPhi N k₁ k) x‖ = 0
  · rw [h1]; simp
  by_cases h2 : ‖iteratedDeriv (j₂ - i₂) (symDPsi P N k₂ k) y‖ = 0
  · rw [h2]; simp
  have hmem : k.1.1.1 ∈ iwArithFreqs ρ l₁ ∧ k.1.1.2 ∈ iwArithFreqs ρ l₂ := by
    have h1 := Finset.mem_product.mp hk
    have h2 := Finset.mem_product.mp h1.1
    have h3 := Finset.mem_product.mp h2.1
    have hsub : ∀ l : ℕ, diffFreqs ρ l ⊆ iwArithFreqs ρ l := by
      intro l γ hγ
      unfold diffFreqs at hγ
      split_ifs at hγ with h
      · rw [h]; exact hγ
      · exact (Finset.mem_sdiff.mp hγ).1
    exact ⟨hsub l₁ h3.1, hsub l₂ h3.2⟩
  have hper : 0 < perQ k.1.1.1 k.1.1.2 := by
    obtain ⟨q₁, hq₁, hγ₁⟩ := mem_iwArithFreqs.mp hmem.1
    obtain ⟨q₂, hq₂, hγ₂⟩ := mem_iwArithFreqs.mp hmem.2
    have ho₁ : addOrderOf k.1.1.1 ≠ 0 :=
      (Nat.pos_of_dvd_of_pos (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hγ₁) (pos_of_mem_iwP hq₁)).ne'
    have ho₂ : addOrderOf k.1.1.2 ≠ 0 :=
      (Nat.pos_of_dvd_of_pos (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hγ₂) (pos_of_mem_iwP hq₂)).ne'
    rw [perQ]
    exact Nat.lcm_pos (Nat.pos_of_ne_zero ho₁) (Nat.pos_of_ne_zero ho₂)
  have hξ₁ := le_pow_div_of_abs_le hN (hsupp₁ h1)
  have hξ₂ : |y - gamR k.1.1.2 + (k.2 : ℝ)|
      ≤ (2 : ℝ) ^ (P.natDegree * (k₂ + 1)) / (N : ℝ) ^ P.natDegree := by
    refine le_pow_div_pow_of_abs_le hN (hsupp₂ h2)
  have hM := hM0 N (perQ k.1.1.1 k.1.1.2) (j₁ - i₁) i₂ k₁ k₂ k.1.1.1 k.1.1.2
    (x - gamR k.1.1.1 + (k.1.2 : ℝ)) (y - gamR k.1.1.2 + (k.2 : ℝ))
    (by omega) (by omega) hN hper (perQ_smul_left _ _) (perQ_smul_right _ _) hξ₁ hξ₂
  have hK : ‖Work.KMTAreas.A7.M0deriv P N (perQ k.1.1.1 k.1.1.2) k.1.1.1 k.1.1.2
      (x - gamR k.1.1.1 + (k.1.2 : ℝ)) (y - gamR k.1.1.2 + (k.2 : ℝ)) (j₁ - i₁) i₂‖
      ≤ C_M * (perQ k.1.1.1 k.1.1.2 : ℝ) ^ 2
        * (1 + ((2 : ℝ) ^ k₁ + (2 : ℝ) ^ (P.natDegree * k₂)) ^ 2 / (N : ℝ))
        * (N : ℝ) ^ (((j₁ : ℤ) - (i₁ : ℤ)) + (P.natDegree : ℤ) * (i₂ : ℤ) - 1) := by
    have hexp : ((j₁ - i₁ : ℕ) : ℤ) = (j₁ : ℤ) - (i₁ : ℤ) := by omega
    calc ‖Work.KMTAreas.A7.M0deriv P N (perQ k.1.1.1 k.1.1.2) k.1.1.1 k.1.1.2
          (x - gamR k.1.1.1 + (k.1.2 : ℝ)) (y - gamR k.1.1.2 + (k.2 : ℝ)) (j₁ - i₁) i₂‖
        ≤ C_M * (perQ k.1.1.1 k.1.1.2 : ℝ) ^ 2
          * (1 + ((2 : ℝ) ^ k₁ + (2 : ℝ) ^ (P.natDegree * k₂)) ^ 2 / (N : ℝ))
          * (N : ℝ) ^ (((j₁ - i₁ : ℕ) : ℤ) + (P.natDegree : ℤ) * (i₂ : ℤ) - 1) := hM
      _ = C_M * (perQ k.1.1.1 k.1.1.2 : ℝ) ^ 2
          * (1 + ((2 : ℝ) ^ k₁ + (2 : ℝ) ^ (P.natDegree * k₂)) ^ 2 / (N : ℝ))
          * (N : ℝ) ^ (((j₁ : ℤ) - (i₁ : ℤ)) + (P.natDegree : ℤ) * (i₂ : ℤ) - 1) := by
          rw [hexp]
  calc ‖((j₂.choose i₂ : ℂ) * (j₁.choose i₁ : ℂ))‖ * ‖iteratedDeriv i₁ (symDPhi N k₁ k) x‖
        * ‖Work.KMTAreas.A7.M0deriv P N (perQ k.1.1.1 k.1.1.2) k.1.1.1 k.1.1.2
            (x - gamR k.1.1.1 + (k.1.2 : ℝ)) (y - gamR k.1.1.2 + (k.2 : ℝ)) (j₁ - i₁) i₂‖
        * ‖iteratedDeriv (j₂ - i₂) (symDPsi P N k₂ k) y‖
      ≤ (16 * ‖iteratedDeriv i₁ (symDPhi N k₁ k) x‖
          * (C_M * (perQ k.1.1.1 k.1.1.2 : ℝ) ^ 2
            * (1 + ((2 : ℝ) ^ k₁ + (2 : ℝ) ^ (P.natDegree * k₂)) ^ 2 / (N : ℝ))
            * (N : ℝ) ^ (((j₁ : ℤ) - (i₁ : ℤ)) + (P.natDegree : ℤ) * (i₂ : ℤ) - 1)))
        * ‖iteratedDeriv (j₂ - i₂) (symDPsi P N k₂ k) y‖ := by
        refine mul_le_mul (mul_le_mul ?_ hK (norm_nonneg _) (by positivity)) le_rfl
          (norm_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_right hC (norm_nonneg _)
    _ = (16 * (C_M * (perQ k.1.1.1 k.1.1.2) ^ 2
            * (1 + ((2 : ℝ) ^ k₁ + (2 : ℝ) ^ (P.natDegree * k₂)) ^ 2 / (N : ℝ))
            * (N : ℝ) ^ (((j₁ : ℤ) - (i₁ : ℤ)) + (P.natDegree : ℤ) * (i₂ : ℤ) - 1)))
          * ‖iteratedDeriv i₁ (symDPhi N k₁ k) x‖
          * ‖iteratedDeriv (j₂ - i₂) (symDPsi P N k₂ k) y‖ := by ring

end

end Work.KMTPlan.A6.SpikeToolbox
