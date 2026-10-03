import Mathlib
import Submission.Work.KMTPlan.A6.MdlSliceLinF

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped ENNReal NNReal BigOperators

/-!
# The difference family `φ_{N,t} − φ_N` at the bottom height (area A6, §7)

This module proves `Work.KMTPlan.A6.PieceBoundedH.mdlDiffFamilyAll`, the *global-height* form (for
`0 < ρ ≤ 1`, with no `ρ ≤ ρ₀` restriction) of `Work.KMTPlan.A6.mdlDiffFamily`, the half of the *low* (bottom height `k₁ = 0`)
linear model estimate of §7 of Krause--Mirek--Tao in which the modulated bump `φ_{N,t}` is replaced
by the difference `φ_{N,t} − φ_N`.

Two structural facts make this a *vanishing* symbol (i.e. an instance of `mdlVanishingCase`):

* `φ_{N,t} − φ_N = η(2^{Log N}·)·(e(Nt·) − 1)` vanishes at the frequency origin, and its support is
  still the shrinking arc `[-2^{−Log N}, 2^{−Log N}]` (`varphiNt_support_le_all`,
  `varphiN_support`), so the family is *narrow* on the core;
* the signed sums are uniformly bounded **independently of `t`** by `varphiNtDiffSupBound` — this is
  exactly the point of subtracting `φ_N`, since the un-subtracted family has signed sums of size
  `≍ 2^{Log N}` at the origin.

Together with `mdlComposite_uniformSigns_le` (the narrow-symbol single-scale `ℓ²` bound) and
`varEst_of_uniformSigns_of_measurable` (Marcinkiewicz--Zygmund: uniform signed `ℓ²` bounds give the
`r`-variational `ℓ²` bound), the estimate follows exactly as for `varphiNtj` in
`mdlVanishingCaseUnif`; the only differences are that the narrowness level is `−Log N_{m₀}` with `m₀`
the first core index, and that the uniform bound `M` is supplied by `varphiNtDiffSupBound`.
-/

/-- The modulated bump `varphiNt N k t` is measurable in the frequency variable. -/
theorem measurable_varphiNt_self_dfa (N k : ℕ) (t : ℝ) :
    Measurable (Work.KMTAreas.A7.varphiNt N k t) := by
  show Measurable (fun ξ : ℝ =>
    Work.KMTAreas.A7.varphiN N k ξ * Work.KMTAreas.A7.ee ((N : ℝ) * t * ξ))
  exact (measurable_varphiN_self N k).mul
    (Complex.continuous_exp.measurable.comp (by fun_prop))

/-- **Narrowness of the difference `φ_{N,t} − φ_N`.**  For `m₀ ≤ n` the difference of the two
bottom-height bumps at the scale `⌊a n⌋` is supported in the arc `[-2^{−Log N_{m₀}}, 2^{−Log N_{m₀}}]`:
both terms are supported in `|ξ| ≤ 2^{−Log N_n}`, and `Log N_{m₀} ≤ Log N_n`. -/
theorem varphiNt_diff_support_dfa {a : ℕ → NNReal} {m₀ n : ℕ}
    (hfloor : Monotone fun n => Nat.floor (a n)) (hn : m₀ ≤ n) (t : ℝ) :
    ∀ ξ : ℝ, Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
        - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ ≠ 0 →
      ξ ∈ Work.Analysis.IonescuWainger.realArc
        (-(Work.Analysis.EndVar.logN (Nat.floor (a m₀)))) := by
  intro ξ hξ
  have hnm : Nat.floor (a m₀) ≤ Nat.floor (a n) := hfloor hn
  have hlog : Work.Analysis.EndVar.logN (Nat.floor (a m₀))
      ≤ Work.Analysis.EndVar.logN (Nat.floor (a n)) := Work.Analysis.EndVar.logN_mono hnm
  have hne : Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ ≠ 0
      ∨ Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hξ (by rw [hc.1, hc.2, sub_zero])
  have hsupp : |ξ| ≤ (2 : ℝ) ^ (((0 : ℕ) : ℝ)
      - (Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℝ)) := by
    rcases hne with h | h
    · exact Work.KMTAreas.A7.varphiNt_support_le_all 0 (Nat.floor (a n)) t ξ h
    · exact Work.KMTAreas.A7.varphiN_support (Nat.floor (a n)) 0 ξ h
  have hExp : ((0 : ℕ) : ℝ) - (Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℝ)
      ≤ ((-(Work.Analysis.EndVar.logN (Nat.floor (a m₀))) : ℤ) : ℝ) := by
    have h1 : (Work.Analysis.EndVar.logN (Nat.floor (a m₀)) : ℝ)
        ≤ (Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℝ) := by exact_mod_cast hlog
    push_cast
    linarith
  have hb' : |ξ| ≤ (2 : ℝ) ^ (((-(Work.Analysis.EndVar.logN (Nat.floor (a m₀)))) : ℤ) : ℝ) :=
    hsupp.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hExp)
  have hb : |ξ| ≤ (2 : ℝ) ^ (-(Work.Analysis.EndVar.logN (Nat.floor (a m₀)))) := by
    rw [← Real.rpow_intCast]
    exact hb'
  rw [Work.Analysis.IonescuWainger.realArc, Set.mem_Icc]
  exact ⟨by linarith [(abs_le.mp hb).1], (abs_le.mp hb).2⟩

theorem mdlDiffFamilyAll (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (R : NNReal) (hR : 2 < R)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ K : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₂ : ℕ) (t : ℝ) (f : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        t ∈ Set.Icc (1 / 2 : ℝ) 1 →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ =>
            if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
              Work.KMTAreas.A7.Tle ρ l₁ (fun ξ : ℝ =>
                  Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
                    - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ)
                (Work.KMTPlan.A6.mdlF ρ (Work.KMTAreas.A7.uScale ρ
                  (max (max l₁ l₂) (max 0 k₂))) l₁ f) x
            else 0)) 2 MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) *
              ENNReal.ofReal (Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ 0 k₂) *
              MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
  classical
  obtain ⟨Qc, hQcpos, hQcelem⟩ := Work.Analysis.IonescuWainger.iwP_element_le hρ
  obtain ⟨Ck, hCkpos, hCk⟩ := two_pow_core_bound ρ hρ hρ1 Qc hQcpos
  obtain ⟨Cu, hCupos, hCu⟩ := two_pow_neg_scale_mul_Q_bound ρ hρ Qc hQcpos
  obtain ⟨KMZ, hKMZpos, hKMZ⟩ :=
    Work.KMTAreas.A7.varEst_of_uniformSigns_of_measurable 2 (by norm_num) R hR
  -- the uniform bound `M(Λ)` for the signed sums of the difference family
  set Mof : NNReal → ℝ := fun Λ => if h : 1 < Λ then
      max 1 (Classical.choose (varphiNtDiffSupBound Λ h)) else 1 with hMofdef
  have hMof1 : ∀ Λ : NNReal, 1 ≤ Mof Λ := by
    intro Λ
    simp only [hMofdef]
    split_ifs with h
    · exact le_max_left _ _
    · exact le_rfl
  have hMofsup : ∀ (Λ : NNReal) (hΛ : 1 < Λ) (t : ℝ)
      (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1) (a : ℕ → NNReal),
      PointwiseErgodicTheorems.Lacunary Λ a → (∀ n : ℕ, 1 ≤ a n) →
      ∀ (U : Finset ℕ) (ω : ℕ → Bool) (ξ : ℝ),
      ‖∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
        (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
          - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ)‖ ≤ Mof Λ := by
    intro Λ hΛ t ht a ha ha1 U ω ξ
    have hspec :=
      (Classical.choose_spec (varphiNtDiffSupBound Λ hΛ)).2 t ht a ha ha1 U ω ξ
    have heq : Mof Λ = max 1 (Classical.choose (varphiNtDiffSupBound Λ hΛ)) := by
      simp only [hMofdef, dif_pos hΛ]
    rw [heq]
    exact le_trans hspec (le_max_right _ _)
  -- the constant of the target
  set Kf : NNReal → NNReal := fun Λ =>
      ⟨max 1 (KMZ * ((1 + 2 * (4 * Ck)) * Mof Λ * (2 * (1 + 2 * Cu)))),
        le_trans zero_le_one (le_max_left _ _)⟩ with hKfdef
  refine ⟨Kf, ?_⟩
  intro a Λ l₁ l₂ k₂ t f hΛ ha ha1 ht
  have hKfval : (Kf Λ : ENNReal) = ENNReal.ofReal (max 1 (KMZ *
      ((1 + 2 * (4 * Ck)) * Mof Λ * (2 * (1 + 2 * Cu))))) := by
    rw [ENNReal.coe_nnreal_eq]
    congr 1
  set Q : ℕ := Nat.ceil ((2 : ℝ) ^ (Qc * 2 ^ (ρ * (l₁ : ℝ)))) with hQdef
  have hQb : ∀ q ∈ Work.Analysis.IonescuWainger.iwP ρ l₁, q ≤ Q := by
    intro q hq
    have h := hQcelem l₁ q hq
    have h2 : (2 : ℝ) ^ (Qc * 2 ^ (ρ * (l₁ : ℝ))) ≤ ((Q : ℕ) : ℝ) := by
      rw [hQdef]; exact Nat.le_ceil _
    exact_mod_cast le_trans h h2
  set u : ℕ := Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max 0 k₂)) with hudef
  set Kc : ℝ := (1 + 2 * (4 * Ck)) * Mof Λ * (2 * (1 + 2 * Cu)) with hKcdef
  have hKcpos : 0 < Kc := by
    rw [hKcdef]
    have h1 : (0 : ℝ) < 1 + 2 * (4 * Ck) := by linarith
    have h2 : (0 : ℝ) < 2 * (1 + 2 * Cu) := by linarith
    have h3 : (0 : ℝ) < Mof Λ := lt_of_lt_of_le zero_lt_one (hMof1 Λ)
    exact mul_pos (mul_pos h1 h3) h2
  have hgoal : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
        (fun n : ℕ =>
          if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
            Work.KMTAreas.A7.Tle ρ l₁ (fun ξ : ℝ =>
                Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
                  - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ)
              (Work.KMTPlan.A6.mdlF ρ u l₁ f) x
          else 0)) 2 MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (KMZ * Kc) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
    by_cases hcore : ∃ n, mdlCore ρ C₀ a l₁ l₂ 0 k₂ n
    · -- the core is nonempty: the narrowness level is the scale of the first core index
      set m₀ : ℕ := Nat.find hcore with hm₀def
      have hm₀ : mdlCore ρ C₀ a l₁ l₂ 0 k₂ m₀ := Nat.find_spec hcore
      have hmin : ∀ n, mdlCore ρ C₀ a l₁ l₂ 0 k₂ n → m₀ ≤ n :=
        fun n hn => Nat.find_min' hcore hn
      have hfloor : Monotone fun n => Nat.floor (a n) := monotone_floor_lacunary hΛ ha ha1
      set k : ℤ := - (Work.Analysis.EndVar.logN (Nat.floor (a m₀))) with hkdef
      have hk2 : k ≤ (-2 : ℤ) := by
        obtain ⟨-, -, hmain⟩ := hm₀
        have hu1 : 1 ≤ Work.KMTAreas.A7.uScale ρ (max 0 k₂) := one_le_uScale ρ hρ _
        have hlog : (2 : ℤ) ≤ Work.Analysis.EndVar.logN (Nat.floor (a m₀)) := by
          have htoNat : ((0 + 2 * Work.KMTAreas.A7.uScale ρ (max 0 k₂) : ℕ) : ℤ)
              ≤ Work.Analysis.EndVar.logN (Nat.floor (a m₀)) := by
            have h1 : ((0 + 2 * Work.KMTAreas.A7.uScale ρ (max 0 k₂) : ℕ) : ℤ)
                ≤ (((Work.Analysis.EndVar.logN (Nat.floor (a m₀))).toNat : ℕ) : ℤ) := by
              exact_mod_cast hmain.1
            rwa [Int.toNat_of_nonneg (Work.Analysis.EndVar.logN_nonneg _)] at h1
          have hcastL : ((0 + 2 * Work.KMTAreas.A7.uScale ρ (max 0 k₂) : ℕ) : ℤ)
              = (2 : ℤ) * ((Work.KMTAreas.A7.uScale ρ (max 0 k₂) : ℕ) : ℤ) := by
            push_cast; ring
          rw [hcastL] at htoNat
          have hu1z : (1 : ℤ) ≤ ((Work.KMTAreas.A7.uScale ρ (max 0 k₂) : ℕ) : ℤ) := by
            exact_mod_cast hu1
          linarith
        rw [hkdef]
        linarith
      have hk : (2 : ℝ) ^ k < 1 / 2 := by
        calc (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (-2 : ℤ) := zpow_le_zpow_right₀ (by norm_num) hk2
          _ = 1 / 4 := by norm_num
          _ < 1 / 2 := by norm_num
      -- the clipped difference family
      set Φ : ℕ → ℝ → ℂ := fun n ξ =>
          if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
            Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
              - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ
          else 0 with hΦdef
      have hΦm : ∀ n, Measurable (Φ n) := by
        intro n
        by_cases h : Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n
        · have hfun : Φ n = fun ξ : ℝ =>
              Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
                - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ := by
            funext ξ; rw [hΦdef]; simp [h]
          rw [hfun]
          exact (measurable_varphiNt_self_dfa _ _ _).sub (measurable_varphiN_self _ _)
        · have hfun : Φ n = 0 := by funext ξ; rw [hΦdef]; simp [h]
          rw [hfun]; exact measurable_const
      have hΦsupp : ∀ n ξ, Φ n ξ ≠ 0 → ξ ∈ Work.Analysis.IonescuWainger.realArc k := by
        intro n ξ hξ
        have hc : Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n := by
          by_contra h
          exact hξ (by rw [hΦdef]; simp [h])
        have hneq : Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
            - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ ≠ 0 := by
          intro h0
          exact hξ (by rw [hΦdef]; simp [hc, h0])
        rw [hkdef]
        exact varphiNt_diff_support_dfa hfloor (hmin n hc) t ξ hneq
      have hΦsup : ∀ (U : Finset ℕ) (ω : ℕ → Bool) (ξ : ℝ),
          ‖∑ n ∈ U, (if ω n then (1 : ℂ) else -1) * Φ n ξ‖ ≤ Mof Λ := by
        intro U ω ξ
        have hterm : ∀ n, (if ω n then (1 : ℂ) else -1) * Φ n ξ
            = (if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
                (if ω n then (1 : ℂ) else -1) *
                  (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
                    - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ) else 0) := by
          intro n
          by_cases h : Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n <;>
            rw [hΦdef] <;> simp [h]
        have h1 : (∑ n ∈ U, (if ω n then (1 : ℂ) else -1) * Φ n ξ)
            = ∑ n ∈ U.filter (fun n => Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n),
                (if ω n then (1 : ℂ) else -1) *
                  (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
                    - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ) := by
          rw [Finset.sum_filter]
          exact Finset.sum_congr rfl (fun n _ => hterm n)
        rw [h1]
        exact hMofsup Λ hΛ t ht a ha ha1 _ ω ξ
      -- the uniform bounds on the two factors of the composite constant
      have hkQ : (2 : ℝ) ^ k * ((Q : ℕ) : ℝ) ^ 2 ≤ 4 * Ck := by
        have hQ2 : ((Q : ℕ) : ℝ) ^ 2
            ≤ 4 * (2 : ℝ) ^ (2 * Qc * (2 : ℝ) ^ (ρ * (l₁ : ℝ))) := by
          have hQceil : ((Q : ℕ) : ℝ)
              ≤ 2 * (2 : ℝ) ^ (Qc * (2 : ℝ) ^ (ρ * (l₁ : ℝ))) := by
            rw [hQdef]
            have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (Qc * (2 : ℝ) ^ (ρ * (l₁ : ℝ))) :=
              Real.one_le_rpow (by norm_num) (by positivity)
            have h2 := Nat.ceil_lt_add_one
              (show (0 : ℝ) ≤ (2 : ℝ) ^ (Qc * (2 : ℝ) ^ (ρ * (l₁ : ℝ))) by positivity)
            linarith
          have h3 : ((Q : ℕ) : ℝ) ^ 2
              ≤ (2 * (2 : ℝ) ^ (Qc * (2 : ℝ) ^ (ρ * (l₁ : ℝ)))) ^ 2 :=
            pow_le_pow_left₀ (by positivity) hQceil 2
          have h4 : (2 * (2 : ℝ) ^ (Qc * (2 : ℝ) ^ (ρ * (l₁ : ℝ)))) ^ 2
              = 4 * (2 : ℝ) ^ (2 * Qc * (2 : ℝ) ^ (ρ * (l₁ : ℝ))) := by
            rw [mul_pow]
            have hsq : ((2 : ℝ) ^ (Qc * (2 : ℝ) ^ (ρ * (l₁ : ℝ)))) ^ 2
                = (2 : ℝ) ^ (2 * (Qc * (2 : ℝ) ^ (ρ * (l₁ : ℝ)))) := by
              rw [sq, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
              congr 1; ring
            rw [hsq]; norm_num; congr 1; ring
          linarith [h3, h4]
        have hkr : (2 : ℝ) ^ k
            = (2 : ℝ) ^ (((0 : ℕ) : ℝ)
              - (Work.Analysis.EndVar.logN (Nat.floor (a m₀)) : ℝ)) := by
          rw [← Real.rpow_intCast]
          congr 1
          rw [hkdef]
          push_cast
          ring
        have hkey := hCk (Nat.floor (a m₀)) 0 k₂ l₁ (max (max l₁ l₂) (max 0 k₂))
          (le_trans (le_max_left l₁ l₂) (le_max_left (max l₁ l₂) (max 0 k₂)))
          (Nat.zero_le _)
          (le_trans (le_max_right 0 k₂) (le_max_right (max l₁ l₂) (max 0 k₂)))
          hm₀.2.1 hm₀.2.2.1
        rw [hkr]
        calc (2 : ℝ) ^ (((0 : ℕ) : ℝ)
                - (Work.Analysis.EndVar.logN (Nat.floor (a m₀)) : ℝ))
              * ((Q : ℕ) : ℝ) ^ 2
            ≤ (2 : ℝ) ^ (((0 : ℕ) : ℝ)
                - (Work.Analysis.EndVar.logN (Nat.floor (a m₀)) : ℝ))
              * (4 * (2 : ℝ) ^ (2 * Qc * (2 : ℝ) ^ (ρ * (l₁ : ℝ)))) :=
              mul_le_mul_of_nonneg_left hQ2 (by positivity)
          _ = 4 * (2 : ℝ) ^ (((0 : ℕ) : ℝ)
                - (Work.Analysis.EndVar.logN (Nat.floor (a m₀)) : ℝ)
                + 2 * Qc * (2 : ℝ) ^ (ρ * (l₁ : ℝ))) := by
              rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
              ring
          _ ≤ 4 * Ck := by linarith [hkey]
      have huQ : (2 : ℝ) ^ (-(u : ℤ)) * ((Q : ℕ) : ℝ) ^ 2 ≤ Cu := by
        have h := hCu l₁ (max (max l₁ l₂) (max 0 k₂))
          (le_trans (le_max_left l₁ l₂) (le_max_left (max l₁ l₂) (max 0 k₂)))
        simpa only [hudef, hQdef] using h
      -- the composite constant
      set M' : ℝ := (1 + 2 * (2 : ℝ) ^ k * (Q : ℝ) ^ 2) * Mof Λ
          * (2 * (1 + 2 * (2 : ℝ) ^ (-(u : ℤ)) * (Q : ℝ) ^ 2)) with hM'def
      have hcomp : ∀ (U : Finset ℕ) (ω : ℕ → Bool) (g : ℤ → ℂ),
          MeasureTheory.eLpNorm (fun x : ℤ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
              Work.KMTAreas.A7.Tle ρ l₁ (Φ n) (Work.KMTPlan.A6.mdlF ρ u l₁ g) x)
            2 MeasureTheory.Measure.count
            ≤ ENNReal.ofReal M' * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
        intro U ω g
        have h := mdlComposite_uniformSigns_le ρ l₁ u k hk Q hQb Φ hΦm hΦsupp
          (Mof Λ) (le_trans zero_le_one (hMof1 Λ)) hΦsup U ω g
        simpa only [hM'def] using h
      have hM'le : M' ≤ Kc := by
        rw [hM'def, hKcdef]
        have hA : 1 + 2 * (2 : ℝ) ^ k * ((Q : ℕ) : ℝ) ^ 2 ≤ 1 + 2 * (4 * Ck) := by
          nlinarith [hkQ]
        have hB : 2 * (1 + 2 * (2 : ℝ) ^ (-(u : ℤ)) * ((Q : ℕ) : ℝ) ^ 2)
            ≤ 2 * (1 + 2 * Cu) := by
          nlinarith [huQ]
        have hM0 : 0 < Mof Λ := lt_of_lt_of_le zero_lt_one (hMof1 Λ)
        exact mul_le_mul (mul_le_mul hA le_rfl hM0.le (by positivity)) hB
          (by positivity) (by positivity)
      have hcell := hKMZ (fun n g => Work.KMTAreas.A7.Tle ρ l₁ (Φ n)
          (Work.KMTPlan.A6.mdlF ρ u l₁ g))
        (fun n g => (measurable_of_countable _).aemeasurable) Kc hKcpos.le ?_ f
      · -- rewrite the family and conclude
        have hpt : ∀ (x : ℤ) (n : ℕ),
            (if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
                Work.KMTAreas.A7.Tle ρ l₁ (fun ξ : ℝ =>
                    Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
                      - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ)
                  (Work.KMTPlan.A6.mdlF ρ u l₁ f) x else 0)
              = Work.KMTAreas.A7.Tle ρ l₁ (Φ n) (Work.KMTPlan.A6.mdlF ρ u l₁ f) x := by
          intro x n
          by_cases h : Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n
          · simp only [h, if_true, hΦdef]
          · rw [hΦdef]
            simp only [h, if_false]
            exact congrFun (Tle_zero_symbol ρ l₁ (Work.KMTPlan.A6.mdlF ρ u l₁ f)).symm x
        have hfamily : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
              (fun n : ℕ =>
                if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
                  Work.KMTAreas.A7.Tle ρ l₁ (fun ξ : ℝ =>
                      Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
                        - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ)
                    (Work.KMTPlan.A6.mdlF ρ u l₁ f) x else 0))
            = fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
                (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l₁ (Φ n)
                  (Work.KMTPlan.A6.mdlF ρ u l₁ f) x) := by
          funext x
          congr 1
          funext n
          exact hpt x n
        rw [hfamily]
        rw [show ENNReal.ofReal 2 = (2 : ENNReal) from by norm_num] at hcell
        exact hcell
      · -- the uniform-in-signs lintegral bound
        intro U ω g
        by_cases hg : ∃ B : ℝ, ∀ m : ℤ, ‖g m‖ ≤ B
        · have hb := hcomp U ω g
          have hb0 : MeasureTheory.eLpNorm (fun x : ℤ => ∑ n ∈ U,
                (if ω n then (1 : ℂ) else -1) *
                  Work.KMTAreas.A7.Tle ρ l₁ (Φ n) (Work.KMTPlan.A6.mdlF ρ u l₁ g) x)
                (ENNReal.ofReal 2) MeasureTheory.Measure.count
              ≤ ENNReal.ofReal M' * MeasureTheory.eLpNorm g (ENNReal.ofReal 2)
                  MeasureTheory.Measure.count := by
            simpa only [show ENNReal.ofReal (2 : ℝ) = (2 : ENNReal) from by norm_num] using hb
          have hb' : MeasureTheory.eLpNorm (fun x : ℤ => ∑ n ∈ U,
                (if ω n then (1 : ℂ) else -1) *
                  Work.KMTAreas.A7.Tle ρ l₁ (Φ n) (Work.KMTPlan.A6.mdlF ρ u l₁ g) x)
                (ENNReal.ofReal 2) MeasureTheory.Measure.count
              ≤ ENNReal.ofReal Kc * MeasureTheory.eLpNorm g (ENNReal.ofReal 2)
                  MeasureTheory.Measure.count :=
            le_trans hb0 (mul_le_mul' (ENNReal.ofReal_le_ofReal hM'le) le_rfl)
          calc ∫⁻ x : ℤ, ‖∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
                Work.KMTAreas.A7.Tle ρ l₁ (Φ n) (Work.KMTPlan.A6.mdlF ρ u l₁ g) x‖ₑ ^ (2 : ℝ)
                ∂MeasureTheory.Measure.count
              = (MeasureTheory.eLpNorm (fun x : ℤ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
                  Work.KMTAreas.A7.Tle ρ l₁ (Φ n) (Work.KMTPlan.A6.mdlF ρ u l₁ g) x)
                  (ENNReal.ofReal 2) MeasureTheory.Measure.count) ^ (2 : ℝ) := by
                  rw [Work.BourgainPlan.Maximal.lintegral_enorm_rpow_eq_eLpNorm_rpow _
                    (by norm_num)]
            _ ≤ (ENNReal.ofReal Kc * MeasureTheory.eLpNorm g (ENNReal.ofReal 2)
                  MeasureTheory.Measure.count) ^ (2 : ℝ) :=
                  ENNReal.rpow_le_rpow hb' (by norm_num)
            _ = ENNReal.ofReal (Kc ^ (2 : ℝ)) *
                  (MeasureTheory.eLpNorm g (ENNReal.ofReal 2)
                    MeasureTheory.Measure.count) ^ (2 : ℝ) := by
                  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
                    ENNReal.ofReal_rpow_of_nonneg hKcpos.le (by norm_num)]
            _ = ENNReal.ofReal (Kc ^ (2 : ℝ)) *
                  ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count := by
                  rw [Work.BourgainPlan.Maximal.lintegral_enorm_rpow_eq_eLpNorm_rpow g
                    (by norm_num)]
        · -- `g` is unbounded: both sides are `⊤`
          have htop : (∫⁻ x : ℤ, ‖g x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count) = ⊤ := by
            by_contra hne
            have hne2 : (MeasureTheory.eLpNorm g (ENNReal.ofReal 2)
                MeasureTheory.Measure.count) ^ (2 : ℝ) ≠ ⊤ := by
              rwa [← Work.BourgainPlan.Maximal.lintegral_enorm_rpow_eq_eLpNorm_rpow g
                (by norm_num)]
            have hlt : MeasureTheory.eLpNorm g (ENNReal.ofReal 2)
                MeasureTheory.Measure.count < ⊤ := by
              rw [lt_top_iff_ne_top]
              intro hcon
              exact hne2 (by rw [hcon]; simp)
            obtain ⟨C, hC⟩ :=
              Work.KMTAreas.A7.eLpNorm_finite_bounded (ENNReal.ofReal 2) (by norm_num) g hlt
            exact hg ⟨C, hC⟩
          rw [htop, ENNReal.mul_top]
          · exact le_top
          · rw [ENNReal.ofReal_ne_zero_iff]
            positivity
    · -- the core is empty: the family vanishes identically
      have hr1 : (1 : NNReal) ≤ R := le_of_lt (lt_trans (by norm_num) hR)
      have hvn0 : PointwiseErgodicTheorems.variationalNorm R (0 : ℕ → ℂ) = 0 := by
        have h := Submission.PointwiseErgodicTheorems.variationalNorm_smul (r := R) hr1
          (0 : ℂ) (0 : ℕ → ℂ)
        simpa using h
      have hfun : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
            (fun n : ℕ =>
              if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
                Work.KMTAreas.A7.Tle ρ l₁ (fun ξ : ℝ =>
                    Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
                      - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ)
                  (Work.KMTPlan.A6.mdlF ρ u l₁ f) x else 0))
          = fun _ : ℤ => 0 := by
        funext x
        have hz : (fun n : ℕ =>
              if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
                Work.KMTAreas.A7.Tle ρ l₁ (fun ξ : ℝ =>
                    Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
                      - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ)
                  (Work.KMTPlan.A6.mdlF ρ u l₁ f) x else 0) = (0 : ℕ → ℂ) := by
          funext n
          rw [if_neg (fun h => hcore ⟨n, h⟩)]
          rfl
        rw [hz, hvn0]
      rw [hfun]
      simp
  -- the loss weight is absorbed into the constant
  have hKB_le : ENNReal.ofReal (KMZ * Kc) ≤ (Kf Λ : ENNReal) := by
    rw [hKfval, hKcdef]
    exact ENNReal.ofReal_le_ofReal (le_max_right 1 _)
  have hloss : (1 : ENNReal)
      ≤ ENNReal.ofReal (Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ 0 k₂) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (one_le_lossWeight_two hρ.le l₁ l₂ 0 k₂)
  calc MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
        (fun n : ℕ =>
          if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
            Work.KMTAreas.A7.Tle ρ l₁ (fun ξ : ℝ =>
                Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
                  - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ)
              (Work.KMTPlan.A6.mdlF ρ u l₁ f) x
          else 0)) 2 MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (KMZ * Kc) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count :=
        hgoal
    _ ≤ (Kf Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count :=
        mul_le_mul' hKB_le le_rfl
    _ ≤ (Kf Λ : ENNReal) *
          ENNReal.ofReal (Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ 0 k₂) *
          MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
        calc (Kf Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
            = (Kf Λ : ENNReal) * 1 * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
              rw [mul_one]
          _ ≤ (Kf Λ : ENNReal) *
                ENNReal.ofReal (Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ 0 k₂) *
                MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count :=
              mul_le_mul' (mul_le_mul' le_rfl hloss) le_rfl

end Work.KMTPlan.A6
