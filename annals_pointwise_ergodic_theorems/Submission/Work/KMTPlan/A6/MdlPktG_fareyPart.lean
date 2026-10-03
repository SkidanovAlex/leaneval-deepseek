import Mathlib
import Submission.Work.KMTPlan.A6.MdlDefs
import Submission.Work.KMTAreas.A7Hi.Gblock

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Finset Filter Topology
open scoped ENNReal NNReal BigOperators Topology
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier
open Work.KMTAreas.A7

/-! ## §1.  The vanishing of the `d`-fold bump near the origin

This is the `d`-fold analogue of `Work.KMTPlan.A6.varphiN_eq_zero_of_abs_le`: for `k ≠ 0` the
`d`-fold bump `φ̃_N` is the difference `η(2^{d(Log N-k)}ξ) - η(2^{d(Log N-k)+1}ξ)` of two rescalings
of the cutoff `η`, which is `1` on `[-1/2,1/2]`; hence `φ̃_N` vanishes on a ball around `0`.  This
is what makes the *negative* powers `ξ ↦ ξ^{j}`, `j < 0`, of the modified bump smooth: away from
the origin they are smooth inverses, near the origin the whole expression vanishes identically. -/

/-- **`φ̃_N` vanishes on the ball of radius `2^{-(d(Log N - k) + d + 1)}` around the origin** when
`k ≠ 0`. -/
lemma varphitildeN_eq_zero_of_abs_lt (d N k : ℕ) (hk : k ≠ 0) {ξ : ℝ}
    (h : |ξ| < (2:ℝ) ^ (-((d:ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k:ℝ)) + ((d:ℝ) + 1)))) :
    Work.KMTAreas.A7.varphitildeN d N k ξ = 0 := by
  rw [Work.KMTAreas.A7.varphitildeN, if_neg hk]
  have h2pos : (0:ℝ) < 2 := by norm_num
  have hone1 : Work.KMTContract.kmtEta
      ((2:ℝ) ^ ((d:ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k:ℝ))) * ξ) = 1 := by
    apply Work.KMTContract.kmtEta_one
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos h2pos _)]
    have hlt := mul_lt_mul_of_pos_left h
      (Real.rpow_pos_of_pos h2pos ((d:ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k:ℝ))))
    have hstep : (2:ℝ) ^ ((d:ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k:ℝ))) *
        (2:ℝ) ^ (-((d:ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k:ℝ)) + ((d:ℝ) + 1))) =
        (2:ℝ) ^ (-((d:ℝ) + 1)) := by
      rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      congr 1; ring
    rw [hstep] at hlt
    have hle : (2:ℝ) ^ (-((d:ℝ) + 1)) ≤ 1/2 := by
      have h1 : -((d:ℝ) + 1) ≤ (-1:ℝ) := by
        have : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d
        linarith
      calc (2:ℝ) ^ (-((d:ℝ) + 1)) ≤ (2:ℝ) ^ (-1:ℝ) :=
            (Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mpr h1
        _ = 1/2 := by norm_num [Real.rpow_neg_one]
    linarith [hle, hlt]
  have hone2 : Work.KMTContract.kmtEta
      ((2:ℝ) ^ ((d:ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k:ℝ) + 1)) * ξ) = 1 := by
    apply Work.KMTContract.kmtEta_one
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos h2pos _)]
    have hlt := mul_lt_mul_of_pos_left h
      (Real.rpow_pos_of_pos h2pos ((d:ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k:ℝ) + 1)))
    have hstep : (2:ℝ) ^ ((d:ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k:ℝ) + 1)) *
        (2:ℝ) ^ (-((d:ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k:ℝ)) + ((d:ℝ) + 1))) =
        (2:ℝ) ^ (-1:ℝ) := by
      rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      congr 1; ring
    rw [hstep] at hlt
    have h2 : (2:ℝ) ^ (-1:ℝ) = 1/2 := by norm_num [Real.rpow_neg_one]
    rw [h2] at hlt
    exact le_of_lt hlt
  rw [hone1, hone2, sub_self]

/-- The eventual vanishing of `φ̃_N` at the origin, in filter form. -/
lemma varphitildeN_eventually_eq_zero (d N k : ℕ) (hk : k ≠ 0) :
    ∀ᶠ ξ : ℝ in 𝓝 0, Work.KMTAreas.A7.varphitildeN d N k ξ = 0 := by
  have hpos : (0:ℝ) <
      (2:ℝ) ^ (-((d:ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k:ℝ)) + ((d:ℝ) + 1))) :=
    Real.rpow_pos_of_pos (by norm_num) _
  refine Filter.mem_of_superset (Metric.ball_mem_nhds (0:ℝ) hpos) ?_
  intro ξ hξ
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hξ
  exact varphitildeN_eq_zero_of_abs_lt d N k hk hξ

/-- The modulated bump `φ̃_{N,t}` vanishes eventually at the origin when `k ≠ 0`. -/
lemma varphitildeNt_eventually_eq_zero (P : Polynomial ℤ) (d N k : ℕ) (t : ℝ)
    (hk : k ≠ 0) :
    ∀ᶠ ξ : ℝ in 𝓝 0, Work.KMTAreas.A7.varphitildeNt P d N k t ξ = 0 := by
  filter_upwards [varphitildeN_eventually_eq_zero d N k hk] with ξ hξ
  simp only [Work.KMTAreas.A7.varphitildeNt]
  rw [hξ, zero_mul]

/-! ## §2.  The weight `ξ ↦ (c ξ)^j` -/

/-- The weight `ξ ↦ (c ξ)^j` is `C^∞` for every `j ≥ 0` (it is a polynomial in `ξ`). -/
lemma contDiff_zpow_const_mul_of_nonneg (c : ℝ) (j : ℤ) (hj : 0 ≤ j) :
    ContDiff ℝ (⊤ : ℕ∞) (fun ξ : ℝ => (((c * ξ : ℝ)) : ℂ) ^ j) := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hj
  have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ)) :=
    (Complex.ofRealCLM.contDiff (n := (⊤ : ℕ∞))).comp (contDiff_const.mul contDiff_id)
  simpa only [zpow_natCast] using hlin.pow n

/-- The weight `ξ ↦ (c ξ)^j` is smooth at every point where `ξ ↦ c ξ` does not vanish. -/
lemma contDiffAt_zpow_const_mul (c : ℝ) (j : ℤ) {x : ℝ} (h : 0 ≤ j ∨ c * x ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun ξ : ℝ => (((c * ξ : ℝ)) : ℂ) ^ j) x := by
  by_cases hj : 0 ≤ j
  · exact (contDiff_zpow_const_mul_of_nonneg c j hj).contDiffAt
  · obtain ⟨m, rfl⟩ := Int.eq_negSucc_of_lt_zero (not_le.mp hj)
    have hcx : c * x ≠ 0 := h.resolve_left hj
    have hfun : (fun ξ : ℝ => (((c * ξ : ℝ)) : ℂ) ^ (Int.negSucc m))
        = fun ξ : ℝ => ((((c * ξ : ℝ) ^ (m + 1) : ℝ)) : ℂ)⁻¹ := by
      funext ξ
      rw [zpow_negSucc, Complex.ofReal_pow]
    rw [hfun]
    have hpoly : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : ℝ => ((((c * ξ : ℝ) ^ (m + 1) : ℝ)) : ℂ)) :=
      (Complex.ofRealCLM.contDiff (n := (⊤ : ℕ∞))).comp
        ((contDiff_const.mul contDiff_id).pow (m + 1))
    refine hpoly.contDiffAt.inv ?_
    simp only [Complex.ofReal_ne_zero]
    exact pow_ne_zero _ hcx

/-! ## §3.  Smoothness and compact support of the modified bump -/

/-- The modified bump as the product of the weight `ξ ↦ (c ξ)^j` and the unmodified bump. -/
lemma varphitildeNtj_eq_weight_mul (P : Polynomial ℤ) (N k : ℕ) (j : ℤ) (t : ℝ) :
    varphitildeNtj P N k j t = fun ξ : ℝ =>
      ((((2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * ((N : ℝ)) ^ P.natDegree * ξ : ℝ)) : ℂ) ^ j
        * Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t ξ := rfl

/-- A non-zero value of the modified bump forces a non-zero value of the unmodified bump. -/
lemma varphitildeNt_ne_zero_of_varphitildeNtj_ne_zero (P : Polynomial ℤ) (N k : ℕ) (j : ℤ)
    (t : ℝ) {ξ : ℝ} (h : varphitildeNtj P N k j t ξ ≠ 0) :
    Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t ξ ≠ 0 := by
  intro hzero
  refine h ?_
  rw [congrFun (varphitildeNtj_eq_weight_mul P N k j t) ξ, hzero, mul_zero]

/-- **The modified bump `φ̃_{N,t,j}` is `C^∞`** in the allowed cases (`k ≠ 0`, or `j ≥ 0`). -/
theorem contDiff_varphitildeNtj_all (P : Polynomial ℤ) (N k : ℕ) (j : ℤ) (t : ℝ)
    (hk : k ≠ 0 ∨ 0 ≤ j) :
    ContDiff ℝ (⊤ : ℕ∞) (varphitildeNtj P N k j t) := by
  have hψ : ContDiff ℝ (⊤ : ℕ∞) (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t) :=
    Work.KMTAreas.A7Hi.contDiff_varphitildeNt_g P P.natDegree N k t
  rw [varphitildeNtj_eq_weight_mul]
  by_cases hj : 0 ≤ j
  · exact (contDiff_zpow_const_mul_of_nonneg
      ((2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * ((N : ℝ)) ^ P.natDegree) j hj).mul hψ
  · obtain ⟨m, rfl⟩ := Int.eq_negSucc_of_lt_zero (not_le.mp hj)
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x = 0
    · subst hx
      have hkne : k ≠ 0 := hk.resolve_right hj
      have hev : (fun ξ : ℝ =>
            ((((2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * ((N : ℝ)) ^ P.natDegree * ξ : ℝ))
                : ℂ) ^ (Int.negSucc m)
              * Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t ξ)
          =ᶠ[𝓝 (0:ℝ)] (fun _ => (0:ℂ)) := by
        filter_upwards [varphitildeNt_eventually_eq_zero P P.natDegree N k t hkne] with ξ hξ
        rw [hξ, mul_zero]
      exact ContDiffAt.congr_of_eventuallyEq (n := (⊤ : ℕ∞)) contDiffAt_const hev
    · by_cases hc : (2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * ((N : ℝ)) ^ P.natDegree = 0
      · have hzero : (fun ξ : ℝ =>
              ((((2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * ((N : ℝ)) ^ P.natDegree * ξ : ℝ))
                : ℂ) ^ (Int.negSucc m)
                * Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t ξ)
            = fun _ => (0:ℂ) := by
          funext ξ
          have hξ0 : (2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * ((N : ℝ)) ^ P.natDegree * ξ
              = 0 := by rw [hc, zero_mul]
          rw [hξ0, Complex.ofReal_zero, zpow_negSucc, zero_pow (n := m + 1) (by omega), inv_zero,
            zero_mul]
        rw [hzero]
        exact contDiffAt_const
      · have hcx : (2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * ((N : ℝ)) ^ P.natDegree * x
            ≠ 0 := mul_ne_zero hc hx
        refine ContDiffAt.mul ?_ hψ.contDiffAt
        exact contDiffAt_zpow_const_mul _ _ (Or.inr hcx)

/-- **The modified bump `φ̃_{N,t,j}` has compact support** (that of the unmodified bump). -/
lemma hasCompactSupport_varphitildeNtj_all (P : Polynomial ℤ) (N k : ℕ) (j : ℤ) (t : ℝ) :
    HasCompactSupport (varphitildeNtj P N k j t) := by
  rw [varphitildeNtj_eq_weight_mul]
  exact (Work.KMTAreas.A7Hi.hasCompactSupport_varphitildeNt_g P P.natDegree N k t).mul_left

/-! ## §4.  The modified bump as a Schwartz function -/

/-- The modified bump `φ̃_{N,t,j}` packaged as a Schwartz function (and `0` in the forbidden
case `k = 0`, `j < 0`, where it is not smooth); the callers only use the cases with
`k ≠ 0 ∨ 0 ≤ j`, where the coercion is the bump itself. -/
noncomputable def varphitildeNtjSch (P : Polynomial ℤ) (N k : ℕ) (j : ℤ) (t : ℝ) :
    SchwartzMap ℝ ℂ :=
  if h : k ≠ 0 ∨ 0 ≤ j then
    (hasCompactSupport_varphitildeNtj_all P N k j t).toSchwartzMap
      (contDiff_varphitildeNtj_all P N k j t h)
  else 0

lemma varphitildeNtjSch_apply (P : Polynomial ℤ) (N k : ℕ) (j : ℤ) (t : ℝ)
    (h : k ≠ 0 ∨ 0 ≤ j) (ξ : ℝ) :
    varphitildeNtjSch P N k j t ξ = varphitildeNtj P N k j t ξ := by
  rw [varphitildeNtjSch, dif_pos h]
  exact HasCompactSupport.toSchwartzMap_toFun _ _ ξ

lemma varphitildeNtjSch_coe (P : Polynomial ℤ) (N k : ℕ) (j : ℤ) (t : ℝ)
    (h : k ≠ 0 ∨ 0 ≤ j) :
    (varphitildeNtjSch P N k j t : ℝ → ℂ) = varphitildeNtj P N k j t :=
  funext (varphitildeNtjSch_apply P N k j t h)

/-! ## §5.  The clipped modified-bump family -/

/-- The `g`-side family of modified bumps clipped at the core-and-Farey scales. -/
noncomputable def fareyClippedSchJ (P : Polynomial ℤ) (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal)
    (Cρc : ℝ) (l₁ l₂ k₁ k₂ : ℕ) (j₂ : ℤ) (t : ℝ) (n : ℕ) : SchwartzMap ℝ ℂ :=
  if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cρc ρ l₂ k₂ a n then
    varphitildeNtjSch P (Nat.floor (a n)) k₂ j₂ t else 0

lemma fareyClippedSchJ_apply (P : Polynomial ℤ) (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal)
    (Cρc : ℝ) (l₁ l₂ k₁ k₂ : ℕ) (j₂ : ℤ) (t : ℝ) (n : ℕ) (ξ : ℝ)
    (h : k₂ ≠ 0 ∨ 0 ≤ j₂) :
    (fareyClippedSchJ P ρ C₀ a Cρc l₁ l₂ k₁ k₂ j₂ t n : ℝ → ℂ) ξ
      = if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cρc ρ l₂ k₂ a n
        then varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t ξ else 0 := by
  rw [fareyClippedSchJ]
  by_cases hc : core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cρc ρ l₂ k₂ a n
  · rw [if_pos hc, if_pos hc]
    exact congrFun (varphitildeNtjSch_coe P (Nat.floor (a n)) k₂ j₂ t h) ξ
  · rw [if_neg hc, if_neg hc]
    simp

lemma fareyClippedSchJ_coe (P : Polynomial ℤ) (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal)
    (Cρc : ℝ) (l₁ l₂ k₁ k₂ : ℕ) (j₂ : ℤ) (t : ℝ) (n : ℕ)
    (h : k₂ ≠ 0 ∨ 0 ≤ j₂) :
    (fareyClippedSchJ P ρ C₀ a Cρc l₁ l₂ k₁ k₂ j₂ t n : ℝ → ℂ)
      = fun ξ : ℝ => if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cρc ρ l₂ k₂ a n
          then varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t ξ else 0 :=
  funext (fun ξ => fareyClippedSchJ_apply P ρ C₀ a Cρc l₁ l₂ k₁ k₂ j₂ t n ξ h)

/-- Farey (narrow-scale) part of the modified-bump `(lin-2)` estimate (Krause--Mirek--Tao §8).

Copy of the PROVED `Work.KMTAreas.A7Hi.lacunaryBumpFareyPartBoundG`
(`Submission/Work/KMTAreas/A7Hi/Gblock.lean`) with the *unmodified* bump
`varphitildeNt P P.natDegree ⌊a n⌋ k₂ t` replaced by the *modified* bump
`Work.KMTPlan.A6.varphitildeNtj P ⌊a n⌋ k₂ j₂ t`, and with the concrete
`multBound_varphitildeNt_two_endpoints` replaced by the hypothesis `hMult`; as in `Gblock` the
conclusion keeps the multiplier constant `M` (the caller instantiates it with the concrete
`C(1+dk₂)` of `MdlPktG_multBound`).

Route, identical to `Gblock`: on the Farey scales the clipped family is narrow
(`Farey Cρc ρ l₂ k₂ a n` puts the support of `varphitildeNtj P ⌊a n⌋ k₂ j₂ t` inside
`realArc (fareyK Cρc ρ l₂)`, because that bump has the same support as `varphitildeNt` and
`ζ ↦ ζ^{j₂}Q(ζ)` is supported in the support of `Q ⊆ [-1,1]`); `hMult` is the uniform-in-signs
two-endpoint bound; and `Work.KMTAreas.A7.varEst_of_narrow_symbols_twoEndpoints` turns the two into
the variational estimate with constant `Kvar (1+l) M`. -/
theorem MdlPktG_fareyPart (P : Polynomial ℤ) (d : ℕ) (hd : 2 ≤ d) (hdP : P.natDegree ≤ d)
    (hd2 : 2 ≤ P.natDegree)
    (C₀ : ℕ) (r : NNReal) (hr : 2 < r) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (Λ : NNReal) (hΛ : 1 < Λ) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤)
    (k₀ : ℕ) (hk₀ : 2 ≤ k₀) (hpmax : p.toReal ≤ 2 * (k₀ : ℝ))
    (hpd : p.toReal / (p.toReal - 1) ≤ 2 * (k₀ : ℝ)) :
    ∃ Cρc : ℝ, 3 ≤ Cρc ∧ ∃ K : ℝ, 0 < K ∧
      ∀ (k₂ : ℕ) (j₂ : ℤ) (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ)) (hk : 1 ≤ k₂ ∨ j₂ = 1)
        (l l₁ l₂ k₁ : ℕ) (hl : l ≤ l₂) (t : ℝ) (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1)
        (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
        (M : NNReal) (hM : 0 < M)
        (hMult : ∀ (U : Finset ℕ) (ω : ℕ → Bool),
          Work.Analysis.IWMultiplier.IsLqMultiplierBound 2
              (fun ξ : ℝ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
                Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t ξ) M ∧
            Work.Analysis.IWMultiplier.IsLqMultiplierBound (ENNReal.ofReal (2 * (k₀ : ℝ)))
              (fun ξ : ℝ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
                Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t ξ) M)
        (f : ℤ → ℂ),
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l (fun ξ : ℝ =>
            if Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n
              ∧ Work.KMTAreas.A7.Farey Cρc ρ l₂ k₂ a n
            then Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t ξ else 0) f x))
          p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (K * (1 + (l₂ : ℝ)) * (M : ℝ)) *
            MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  classical
  obtain ⟨Cρ, hCρpos, Kvar, hKvarpos, hmain⟩ :=
    Work.KMTAreas.A7.varEst_of_narrow_symbols_twoEndpoints ρ hρ hρ1 r hr p hp hptop k₀ hk₀
      hpmax hpd
  refine ⟨max 3 Cρ, le_max_left _ _, Kvar, hKvarpos, ?_⟩
  intro k₂ j₂ hj₂ hk l l₁ l₂ k₁ hl t ht a ha ha1 M hM hMult f
  set Cc : ℝ := max 3 Cρ with hCcdef
  have hCc3 : 3 ≤ Cc := by rw [hCcdef]; exact le_max_left _ _
  have hCc1 : 1 < Cc := lt_of_lt_of_le (by norm_num) hCc3
  have hCρle : Cρ ≤ Cc := by rw [hCcdef]; exact le_max_right _ _
  have hCρ0 : (0 : ℝ) ≤ Cρ := hCρpos.le
  have hCc0 : (0 : ℝ) ≤ Cc := le_trans hCρ0 hCρle
  have hkj : k₂ ≠ 0 ∨ 0 ≤ j₂ := by
    rcases hk with h1 | h1
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  -- ## narrowness of the clipped family
  have hnarrow : ∀ n ξ, (fareyClippedSchJ P ρ C₀ a Cc l₁ l₂ k₁ k₂ j₂ t n : ℝ → ℂ) ξ ≠ 0 →
      ξ ∈ Work.Analysis.IonescuWainger.realArc (fareyK Cc ρ l₂) := by
    intro n ξ hξ
    rw [fareyClippedSchJ_apply P ρ C₀ a Cc l₁ l₂ k₁ k₂ j₂ t n ξ hkj] at hξ
    by_cases hc : core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cc ρ l₂ k₂ a n
    · rw [if_pos hc] at hξ
      have hNt : Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t ξ ≠ 0 :=
        varphitildeNt_ne_zero_of_varphitildeNtj_ne_zero P (Nat.floor (a n)) k₂ j₂ t hξ
      exact Work.KMTAreas.A7Hi.narrow_of_farey_g P P.natDegree (by omega) hCc0 hc.2 ξ hNt
    · rw [if_neg hc] at hξ
      exact absurd rfl hξ
  -- ## the two-endpoint multiplier bound for the clipped family
  have hMult' : ∀ (U : Finset ℕ) (ω : ℕ → Bool),
      Work.Analysis.IWMultiplier.IsLqMultiplierBound 2
          (fun ξ : ℝ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
            (fareyClippedSchJ P ρ C₀ a Cc l₁ l₂ k₁ k₂ j₂ t n : ℝ → ℂ) ξ) M ∧
      Work.Analysis.IWMultiplier.IsLqMultiplierBound (ENNReal.ofReal (2 * (k₀ : ℝ)))
          (fun ξ : ℝ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
            (fareyClippedSchJ P ρ C₀ a Cc l₁ l₂ k₁ k₂ j₂ t n : ℝ → ℂ) ξ) M := by
    intro U ω
    have hU : (fun ξ : ℝ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
            (fareyClippedSchJ P ρ C₀ a Cc l₁ l₂ k₁ k₂ j₂ t n : ℝ → ℂ) ξ)
        = (fun ξ : ℝ => ∑ n ∈ U.filter (fun n => core ρ C₀ l₁ l₂ k₁ k₂ a n ∧
              Farey Cc ρ l₂ k₂ a n),
            (if ω n then (1 : ℂ) else -1) *
              Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t ξ) := by
      funext ξ
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [fareyClippedSchJ_apply P ρ C₀ a Cc l₁ l₂ k₁ k₂ j₂ t n ξ hkj]
      by_cases hc : core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cc ρ l₂ k₂ a n <;> simp [hc]
    obtain ⟨h1, h2⟩ := hMult (U.filter (fun n => core ρ C₀ l₁ l₂ k₁ k₂ a n ∧
      Farey Cc ρ l₂ k₂ a n)) ω
    exact ⟨by rw [hU]; exact h1, by rw [hU]; exact h2⟩
  -- ## the narrow-symbol variational estimate
  have hgood : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l (fareyK Cc ρ l₂) :=
    Work.KMTAreas.A7.goodMajorArcs_fareyK hCρle hCρ0 hρ.le hl
  have hk' : (2 : ℝ) ^ (fareyK Cc ρ l₂) < 1 / 2 :=
    Work.KMTAreas.A7.two_rpow_fareyK_lt_half hCc1 hρ.le l₂
  have hres := hmain l (fareyK Cc ρ l₂) hgood hk' M hM
    (fareyClippedSchJ P ρ C₀ a Cc l₁ l₂ k₁ k₂ j₂ t) hnarrow hMult' f
  -- ## rewriting the clipped family back to the explicit `if`
  have hInt : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l (fun ξ : ℝ =>
          if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cc ρ l₂ k₂ a n
          then varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t ξ else 0) f x))
      = (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l
          (fareyClippedSchJ P ρ C₀ a Cc l₁ l₂ k₁ k₂ j₂ t n : ℝ → ℂ) f x)) := by
    funext x
    refine congrArg (fun u : ℕ → ℂ => PointwiseErgodicTheorems.variationalNorm r u) ?_
    funext n
    exact congrArg (fun φ : ℝ → ℂ => Work.KMTAreas.A7.Tle ρ l φ f x)
      (fareyClippedSchJ_coe P ρ C₀ a Cc l₁ l₂ k₁ k₂ j₂ t n hkj).symm
  rw [hInt]
  -- ## the constant bookkeeping
  refine hres.trans ?_
  refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
  have hlR : (1 + (l : ℝ)) ≤ (1 + (l₂ : ℝ)) := by
    have hl' : (l : ℝ) ≤ (l₂ : ℝ) := by exact_mod_cast hl
    linarith
  have hMnn : (0 : ℝ) ≤ (M : ℝ) := M.coe_nonneg
  calc Kvar * (1 + (l : ℝ)) * (M : ℝ)
      ≤ Kvar * (1 + (l₂ : ℝ)) * (M : ℝ) := by
        refine mul_le_mul_of_nonneg_right ?_ hMnn
        exact mul_le_mul_of_nonneg_left hlR hKvarpos.le

end

end Work.KMTPlan.A6
