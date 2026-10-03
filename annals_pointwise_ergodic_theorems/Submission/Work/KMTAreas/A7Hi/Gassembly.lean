/-
# The assembly of the linear lacunary variational estimate (Area A7)

This module assembles the proof of `Work.KMTAreas.A7.lacunaryBumpVarEstimate` from its four
component estimates:

* `Work.KMTAreas.A7.lacunaryBumpFareyPartBound` (the narrow/Farey part at the heights `k₁ ≥ 1`);
* `Work.KMTAreas.A7.lacunaryBumpFareyDiffPartBound` (the narrow part of the low-frequency
  difference at `k₁ = 0`);
* `Work.KMTAreas.A7.lacunaryIWProjLowpassVar` (the unmodulated low-pass family at `k₁ = 0`);
* `Work.KMTAreas.A7.exists_Lnat_le_of_bad` (the boundedness of the multi-index on the bad scales)
  together with the single-scale estimate `Work.KMTAreas.A7.Tle_varphiNt_single_scale` and the
  lacunary counting bound `Work.KMTAreas.A7.lacunary_index_bound`.

They are taken as *hypotheses* here (`hFarey`, `hFareyDiff`, `hLowpass`, `hBad`) so that this
module builds independently of them; the final wiring (supplying the proved lemmas) is done in
`Submission/Work/KMTAreas/A7/lacunaryBumpVarEstimate`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.lacunaryBumpAssembly
import Submission.Work.KMTAreas.A7Hi.Gclip
import Submission.Work.KMTAreas.A7Hi.Gdiff
import Submission.Work.KMTAreas.A7Hi.Gbad
import Submission.Work.KMTPlan.A6.MdlKerVarphitildeNt
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 20000000

namespace Work.KMTAreas.A7Hi

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier Work.KMTContract Work.Analysis.EndVar
open Work.KMTAreas.A7

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-! ## §1. Elementary helpers -/

/-- `iwConv` with the empty frequency set vanishes (its symbol is identically zero). -/
theorem iwConv_empty_eq_zero (Φ : Circ → ℂ) (f : ℤ → ℂ) :
    iwConv (∅ : Finset Circ) Φ f = 0 := by
  funext n
  simp only [iwConv_apply]
  have hsym : iwSymbolSet (∅ : Finset Circ) Φ = (0 : Circ → ℂ) := by
    funext ξ
    simp [iwSymbolSet]
  rw [hsym]
  simp [iwKernel, fourierCoeff]

/-- **The exact-height multiplier at level `0` vanishes**: `iwArithFreqsNew ρ 0 = ∅` because
`(0 : ℕ) - 1 = 0`. -/
theorem Tex_zero_level (ρ : ℝ) (φ : ℝ → ℂ) (f : ℤ → ℂ) : Tex ρ 0 φ f = 0 := by
  have h01 : (0 : ℕ) - 1 = 0 := by omega
  have h : iwArithFreqsNew ρ 0 = (∅ : Finset Circ) := by
    simp only [iwArithFreqsNew, h01, Finset.sdiff_self]
  rw [Tex, h]
  exact iwConv_empty_eq_zero _ _

/-- The narrowness level `fareyK` is antitone in the constant `Cρc`. -/
theorem fareyK_anti {Cρc Cρc' ρ : ℝ} (h : Cρc' ≤ Cρc) (l₁ : ℕ) :
    fareyK Cρc ρ l₁ ≤ fareyK Cρc' ρ l₁ := by
  rw [fareyK, fareyK]
  refine Int.floor_mono ?_
  have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (ρ * (l₁ : ℝ)) := Real.rpow_nonneg (by norm_num) _
  nlinarith

/-- `Farey` is monotone in the constant `Cρc` (a larger constant gives a smaller set). -/
theorem farey_mono_const {Cρc Cρc' ρ : ℝ} (h : Cρc' ≤ Cρc) {l₁ k₁ : ℕ} {a : ℕ → NNReal}
    {n : ℕ} (hn : Farey Cρc ρ l₁ k₁ a n) : Farey Cρc' ρ l₁ k₁ a n :=
  le_trans hn (fareyK_anti h l₁)

/-- Additivity of the exact-height multiplier in the symbol, for bounded input. -/
theorem Tex_add_of_bounded (ρ : ℝ) (l : ℕ) {φ ψ : ℝ → ℂ}
    (hφ : Adm (iwArithFreqsNew ρ l) φ) (hψ : Adm (iwArithFreqsNew ρ l) ψ)
    {f : ℤ → ℂ} {B : ℝ} (hf : ∀ m : ℤ, ‖f m‖ ≤ B) :
    Tex ρ l (φ + ψ) f = Tex ρ l φ f + Tex ρ l ψ f := by
  have hper : periodize (φ + ψ) = periodize φ + periodize ψ := periodize_add hφ.1 hψ.1
  simp only [Tex, hper]
  exact iwConv_add_of_bounded hf hφ.2.1 hψ.2.1 hφ.2.2 hψ.2.2

/-- The modulated `d`-fold bump at the bottom height `k₂ = 0` splits into the unmodulated bump
and the low-frequency difference. -/
theorem Tex_varphitildeNt_split_of_bounded (P : Polynomial ℤ) (d : ℕ) (ρ : ℝ) (l N : ℕ) (t : ℝ)
    {f : ℤ → ℂ} {B : ℝ} (hf : ∀ m : ℤ, ‖f m‖ ≤ B) :
    Tex ρ l (varphitildeNt P P.natDegree N 0 t) f
      = Tex ρ l (varphitildeN P.natDegree N 0) f
        + Tex ρ l (fun ξ : ℝ => varphitildeNt P P.natDegree N 0 t ξ
            - varphitildeN P.natDegree N 0 ξ) f := by
  have hD : (fun ξ : ℝ => varphitildeNt P P.natDegree N 0 t ξ - varphitildeN P.natDegree N 0 ξ)
      = (fun ξ : ℝ => varphitildeN P.natDegree N 0 ξ * (ee (PevalR P ((N : ℝ) * t) * ξ) - 1)) := by
    funext ξ
    rw [show varphitildeNt P P.natDegree N 0 t ξ
        = varphitildeN P.natDegree N 0 ξ * ee (PevalR P ((N : ℝ) * t) * ξ) from rfl]
    ring
  have hsum : (varphitildeNt P P.natDegree N 0 t)
      = (fun ξ : ℝ => varphitildeN P.natDegree N 0 ξ)
        + (fun ξ : ℝ => varphitildeN P.natDegree N 0 ξ * (ee (PevalR P ((N : ℝ) * t) * ξ) - 1)) := by
    funext ξ
    rw [show varphitildeNt P P.natDegree N 0 t ξ
        = varphitildeN P.natDegree N 0 ξ * ee (PevalR P ((N : ℝ) * t) * ξ) from rfl]
    simp only [Pi.add_apply]
    ring
  rw [hD, hsum]
  refine Tex_add_of_bounded ρ l ?_ ?_ hf
  · exact adm_of_bump ((contDiff_varphitildeN P.natDegree N 0))
      (hasCompactSupport_varphitildeN P.natDegree N 0)
  · refine adm_of_bump ?_ ((hasCompactSupport_varphitildeN P.natDegree N 0).mul_right)
    exact (contDiff_varphitildeN P.natDegree N 0).mul
      ((contDiff_ee_const_mul 2 (PevalR P ((N : ℝ) * t))).sub contDiff_const)

/-! ## §2. Weight arithmetic -/

theorem natCast_le_lmaxR_left (l₁ l₂ k₁ k₂ : ℕ) :
    (l₁ : ℝ) ≤ lmaxR l₁ l₂ k₁ k₂ := by
  rw [lmaxR, Work.Analysis.EndVar.lmax]
  have h : (l₁ : ℤ) ≤ max (max (l₁ : ℤ) (l₂ : ℤ)) (max (k₁ : ℤ) (k₂ : ℤ)) :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  exact_mod_cast h

theorem natCast_le_lmaxR_k₁ (l₁ l₂ k₁ k₂ : ℕ) :
    (k₁ : ℝ) ≤ lmaxR l₁ l₂ k₁ k₂ := by
  rw [lmaxR, Work.Analysis.EndVar.lmax]
  have h : (k₁ : ℤ) ≤ max (max (l₁ : ℤ) (l₂ : ℤ)) (max (k₁ : ℤ) (k₂ : ℤ)) :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  exact_mod_cast h

theorem natCast_le_lmaxR_l₂ (l₁ l₂ k₁ k₂ : ℕ) :
    (l₂ : ℝ) ≤ lmaxR l₁ l₂ k₁ k₂ := by
  rw [lmaxR, Work.Analysis.EndVar.lmax]
  have h : (l₂ : ℤ) ≤ max (max (l₁ : ℤ) (l₂ : ℤ)) (max (k₁ : ℤ) (k₂ : ℤ)) :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  exact_mod_cast h

theorem natCast_le_lmaxR_k₂ (l₁ l₂ k₁ k₂ : ℕ) :
    (k₂ : ℝ) ≤ lmaxR l₁ l₂ k₁ k₂ := by
  rw [lmaxR, Work.Analysis.EndVar.lmax]
  have h : (k₂ : ℤ) ≤ max (max (l₁ : ℤ) (l₂ : ℤ)) (max (k₁ : ℤ) (k₂ : ℤ)) :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  exact_mod_cast h

/-- The `g`-side analogue of `Work.KMTAreas.A7.core_and_farey_iff_le`: here the Farey
(narrowness) condition sits at the *second* variable's indices `(l₂, k₂)`, so the level/height
slots of `core` and `Farey` do not coincide and the `A7` version cannot be applied directly. -/
theorem core_and_farey_iff_le_G {ρ : ℝ} {C₀ : ℕ} {Cρc : ℝ} {l₁ l₂ k₁ k₂ : ℕ} {a : ℕ → NNReal}
    (hamono : Monotone a) (h : ∃ n, core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cρc ρ l₂ k₂ a n) :
    ∃ n₀ : ℕ, ∀ n : ℕ, (core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cρc ρ l₂ k₂ a n) ↔ n₀ ≤ n := by
  classical
  refine ⟨Nat.find h, fun n => ⟨fun hn => ?_, fun hn => ?_⟩⟩
  · by_contra hcon
    rw [not_le] at hcon
    exact Nat.find_min h hcon hn
  · exact ⟨core_mono hamono hn (Nat.find_spec h).1, farey_mono hamono hn (Nat.find_spec h).2⟩

theorem assembly_one_le_lossWeight {c ρ : ℝ} (hc : 0 ≤ c) (hρ : 0 ≤ ρ) (l₁ l₂ k₁ k₂ : ℕ) :
    (1 : ℝ) ≤ lossWeight c ρ l₁ l₂ k₁ k₂ := by
  rw [lossWeight]
  have hL := lmaxR_nonneg l₁ l₂ k₁ k₂
  have h1 : (1 : ℝ) ≤ (1 + lmaxR l₁ l₂ k₁ k₂) ^ c :=
    Real.one_le_rpow (by linarith) hc
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (c * ρ * lmaxR l₁ l₂ k₁ k₂) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  nlinarith

theorem lossWeight_four_ge_sq {ρ : ℝ} (hρ : 0 ≤ ρ) (l₁ l₂ k₁ k₂ : ℕ) :
    (1 + (l₂ : ℝ)) ^ 2 ≤ lossWeight 4 ρ l₁ l₂ k₁ k₂ := by
  rw [lossWeight]
  have hL := lmaxR_nonneg l₁ l₂ k₁ k₂
  set X : ℝ := 1 + lmaxR l₁ l₂ k₁ k₂ with hX
  have hX1 : (1 : ℝ) ≤ X := by rw [hX]; linarith
  have e1 : (1 + (l₂ : ℝ)) ≤ X := by
    rw [hX]; linarith [natCast_le_lmaxR_l₂ l₁ l₂ k₁ k₂]
  have e2 : (0 : ℝ) ≤ 1 + (l₁ : ℝ) := by positivity
  have hsq : (1 + (l₂ : ℝ)) ^ 2 ≤ X ^ 2 := by nlinarith
  have hp4 : X ^ 2 ≤ X ^ 4 := by
    have := pow_le_pow_right₀ hX1 (by norm_num : (2 : ℕ) ≤ 4)
    simpa using this
  have hrw : X ^ (4 : ℝ) = X ^ 4 := Real.rpow_natCast X 4
  have h3 : (1 : ℝ) ≤ (2 : ℝ) ^ (4 * ρ * lmaxR l₁ l₂ k₁ k₂) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  calc (1 + (l₂ : ℝ)) ^ 2 ≤ X ^ 2 := hsq
    _ ≤ X ^ 4 := hp4
    _ = X ^ (4 : ℝ) := hrw.symm
    _ ≤ X ^ (4 : ℝ) * (2 : ℝ) ^ (4 * ρ * lmaxR l₁ l₂ k₁ k₂) :=
        le_mul_of_one_le_right (by positivity) h3
    _ = (1 + lmaxR l₁ l₂ k₁ k₂) ^ (4 : ℝ) * (2 : ℝ) ^ (4 * ρ * lmaxR l₁ l₂ k₁ k₂) := by
        rw [hX]

theorem one_add_le_lossWeight {ρ : ℝ} (hρ : 0 ≤ ρ) (l₁ l₂ k₁ k₂ : ℕ) :
    (1 + (l₂ : ℝ)) ≤ lossWeight 4 ρ l₁ l₂ k₁ k₂ := by
  have h := lossWeight_four_ge_sq hρ l₁ l₂ k₁ k₂
  have h0 : (1 : ℝ) ≤ 1 + (l₁ : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) l₁]
  nlinarith [h, h0]

theorem lossWeight_four_ge_mul {ρ : ℝ} (hρ : 0 ≤ ρ) (l₁ l₂ k₁ k₂ : ℕ) :
    (1 + (l₂ : ℝ)) * (1 + (k₂ : ℝ)) ≤ lossWeight 4 ρ l₁ l₂ k₁ k₂ := by
  rw [lossWeight]
  have hL := lmaxR_nonneg l₁ l₂ k₁ k₂
  set X : ℝ := 1 + lmaxR l₁ l₂ k₁ k₂ with hX
  have hX1 : (1 : ℝ) ≤ X := by rw [hX]; linarith
  have e1 : (1 + (l₂ : ℝ)) ≤ X := by
    rw [hX]; linarith [natCast_le_lmaxR_l₂ l₁ l₂ k₁ k₂]
  have e2 : (1 + (k₂ : ℝ)) ≤ X := by
    rw [hX]; linarith [natCast_le_lmaxR_k₂ l₁ l₂ k₁ k₂]
  have hsq : (1 + (l₂ : ℝ)) * (1 + (k₂ : ℝ)) ≤ X ^ 2 := by nlinarith
  have hp4 : X ^ 2 ≤ X ^ 4 := by
    have := pow_le_pow_right₀ hX1 (by norm_num : (2 : ℕ) ≤ 4)
    simpa using this
  have hrw : X ^ (4 : ℝ) = X ^ 4 := Real.rpow_natCast X 4
  have h3 : (1 : ℝ) ≤ (2 : ℝ) ^ (4 * ρ * lmaxR l₁ l₂ k₁ k₂) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  calc (1 + (l₂ : ℝ)) * (1 + (k₂ : ℝ)) ≤ X ^ 2 := hsq
    _ ≤ X ^ 4 := hp4
    _ = X ^ (4 : ℝ) := hrw.symm
    _ ≤ X ^ (4 : ℝ) * (2 : ℝ) ^ (4 * ρ * lmaxR l₁ l₂ k₁ k₂) :=
        le_mul_of_one_le_right (by positivity) h3
    _ = (1 + lmaxR l₁ l₂ k₁ k₂) ^ (4 : ℝ) * (2 : ℝ) ^ (4 * ρ * lmaxR l₁ l₂ k₁ k₂) := by
        rw [hX]

/-! ## §3. The single-scale side conditions coming from `core` -/

theorem two_le_splitCut (ρ : ℝ) (L : ℕ) : 2 ≤ splitCut ρ L := by
  rw [splitCut]
  calc (2 : ℕ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (2 ^ scaleCount 1 ρ L) :=
        pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (Nat.one_le_two_pow)

/-- On the core the physical scale exceeds `2`. -/
theorem two_lt_floor_of_core {ρ : ℝ} {C₀ : ℕ} {l₁ l₂ k₁ k₂ : ℕ} {a : ℕ → NNReal} {n : ℕ}
    (h : core ρ C₀ l₁ l₂ k₁ k₂ a n) : 2 < Nat.floor (a n) :=
  lt_of_le_of_lt (two_le_splitCut ρ (max (max l₁ l₂) (max k₁ k₂))) h.2.1

/-- On the core the height `k₁` is at most `Log N`, hence `2 ^ k₁ ≤ N`. -/
theorem two_pow_le_floor_of_core {ρ : ℝ} {C₀ : ℕ} {l₁ l₂ k₁ k₂ : ℕ} {a : ℕ → NNReal} {n : ℕ}
    (h : core ρ C₀ l₁ l₂ k₁ k₂ a n) : 2 ^ k₁ ≤ Nat.floor (a n) := by
  obtain ⟨hin, hcut, hmain⟩ := h
  have hN : 2 < Nat.floor (a n) := lt_of_le_of_lt (two_le_splitCut ρ _) hcut
  have hk₂ : k₁ ≤ (logN (Nat.floor (a n))).toNat :=
    le_trans (Nat.le_add_right k₁ _) hmain.1
  have hlog : (logN (Nat.floor (a n))).toNat = Nat.log 2 (max (Nat.floor (a n)) 2) := by
    simp [logN]
  have hne : max (Nat.floor (a n)) 2 ≠ 0 := by
    have : 2 ≤ max (Nat.floor (a n)) 2 := le_max_right _ _
    omega
  have hpow : 2 ^ Nat.log 2 (max (Nat.floor (a n)) 2) ≤ max (Nat.floor (a n)) 2 :=
    Nat.pow_log_le_self 2 hne
  have hmax : max (Nat.floor (a n)) 2 = Nat.floor (a n) := max_eq_left (le_of_lt hN)
  calc 2 ^ k₁ ≤ 2 ^ (logN (Nat.floor (a n))).toNat :=
        pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) hk₂
    _ = 2 ^ Nat.log 2 (max (Nat.floor (a n)) 2) := by rw [hlog]
    _ ≤ max (Nat.floor (a n)) 2 := hpow
    _ = Nat.floor (a n) := hmax


/-! ## §4. The assembly of the target theorem -/

/-- **Clipping a family at a tail costs a factor `3`.**  If `E` agrees with `D` on the tail
`{m, m+1, ...}` and vanishes below `m`, then the `ℓᵖ` variational norm of `E` is at most `3` times
that of `D`. -/
theorem eLpNorm_variationalNorm_clip_le {r : NNReal} (hr1 : 1 ≤ r) (p : ENNReal)
    (m : ℕ) (D E : ℕ → ℤ → ℂ) (h0 : ∀ n, n < m → E n = 0)
    (h1 : ∀ n, m ≤ n → E n = D n) :
    MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => E n x)) p MeasureTheory.Measure.count
      ≤ 3 * MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => D n x)) p MeasureTheory.Measure.count := by
  have hpt : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => E n x)
      ≤ 3 * PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => D n x) := by
    intro x
    have hE : (fun n : ℕ => E n x)
        = (fun n : ℕ => if n < m then 0 else (fun k => D (k + m) x) (n - m)) := by
      funext n
      by_cases hn : n < m
      · rw [if_pos hn, h0 n hn]
        simp
      · rw [if_neg hn]
        simp only [Nat.sub_add_cancel (not_lt.mp hn)]
        exact congrFun (h1 n (not_lt.mp hn)) x
    rw [hE]
    exact (Submission.PointwiseErgodicTheorems.variationalNorm_prependZeros_le hr1 m
        (fun k => D (k + m) x)).trans
      (mul_le_mul_of_nonneg_left (Work.KMTAreas.A7.variationalNorm_tail_le m (fun k => D k x))
        (by norm_num))
  exact (eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => by
      rw [enorm_eq_self, enorm_eq_self]
      exact hpt x)).trans
    (eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' (hf := by pw_aesm)
      (f := fun x : ℤ => (3 : ℝ≥0∞) * PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => D n x))
      (g := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => D n x))
      (c := 3) (Eventually.of_forall (fun x => by
        rw [enorm_eq_self, enorm_eq_self]
        exact le_rfl)) p)



/-- The `ℓᵖ` norm of the variational norm of the zero family vanishes. -/
theorem eLpNorm_variationalNorm_zero {r : NNReal} (hr1 : 1 ≤ r) (p : ENNReal) :
    MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun _ : ℕ => (0 : ℂ))) p MeasureTheory.Measure.count = 0 := by
  have h0 : PointwiseErgodicTheorems.variationalNorm r (fun _ : ℕ => (0 : ℂ)) = 0 := by
    have h := variationalNorm_smul (r := r) hr1 (0 : ℂ) (0 : ℕ → ℂ)
    rw [zero_smul, enorm_zero, zero_mul] at h
    exact h
  rw [show (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun _ : ℕ => (0 : ℂ)))
      = (0 : ℤ → ℝ≥0∞) from funext (fun x => h0)]
  exact MeasureTheory.eLpNorm_zero

theorem lacunaryBumpVarEstimate_assemblyG (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree)
    (hLowpass : ∀ (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal) (hr : 2 < r)
      (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) (Λ : NNReal) (hΛ : 1 < Λ),
      ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧
        ∀ (k : ℤ) (l₂ : ℕ) (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a)
          (ha1 : ∀ n, 1 ≤ a n) (f : ℤ → ℂ),
          Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₂ k →
          (∀ n : ℕ, -((P.natDegree : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a n))) ≤ k) →
          MeasureTheory.eLpNorm (fun x : ℤ => variationalNorm r
            (fun n : ℕ => Tle ρ l₂ (varphitildeN P.natDegree (Nat.floor (a n)) 0) f x))
            p MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (C * (1 + (l₂ : ℝ)) ^ 2) *
              MeasureTheory.eLpNorm f p MeasureTheory.Measure.count)
    (hLowClip : ∀ (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (C₀ : ℕ) (Cρc Cρ : ℝ) (hCρpos : 0 < Cρ)
      (hCρc : Cρ ≤ Cρc) (Λ : NNReal) (hΛ : 1 < Λ) (r : NNReal) (hr : 2 < r) (p : ENNReal)
      (hp : 1 < p) (hptop : p < ⊤) (C : ℝ) (hCpos : 0 < C),
      (∀ (k : ℤ) (l₂ : ℕ) (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a)
        (ha1 : ∀ n, 1 ≤ a n) (f : ℤ → ℂ),
        Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₂ k →
        (∀ n : ℕ, -((P.natDegree : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a n))) ≤ k) →
        MeasureTheory.eLpNorm (fun x : ℤ => variationalNorm r
          (fun n : ℕ => Tle ρ l₂ (varphitildeN P.natDegree (Nat.floor (a n)) 0) f x)) p MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (C * (1 + (l₂ : ℝ)) ^ 2) *
              MeasureTheory.eLpNorm f p MeasureTheory.Measure.count) →
      ∀ (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
        (l l₁ l₂ k₁ k₂ : ℕ) (hl : l ≤ l₂) (f : ℤ → ℂ),
        MeasureTheory.eLpNorm (fun x : ℤ => variationalNorm r
          (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cρc ρ l₂ 0 a n
            then Tle ρ l (varphitildeN P.natDegree (Nat.floor (a n)) 0) f x else 0))
          p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (3 * C * (1 + (l₂ : ℝ)) ^ 2) *
            MeasureTheory.eLpNorm f p MeasureTheory.Measure.count)
    (hBadPart : ∀ (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (C₀ : ℕ) (hC₀ : 1 ≤ C₀)
      (hρC : ρ ≤ 1 / (2 * (C₀ : ℝ))) (Cρc : ℝ) (hCρc : 3 ≤ Cρc) (Λ : NNReal) (hΛ : 1 < Λ)
      (r : NNReal) (hr : 2 < r) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤),
      ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a)
        (ha1 : ∀ n, 1 ≤ a n) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (1/2 : ℝ) 1)
        (f : ℤ → ℂ) (Bf : ℝ) (hBf : ∀ m : ℤ, ‖f m‖ ≤ Bf),
        MeasureTheory.eLpNorm (fun x : ℤ => variationalNorm r
          (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ ¬ Farey Cρc ρ l₂ k₂ a n
            then Tex ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) f x else 0))
          p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count) :
    ∀ (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (r : NNReal) (hr : 2 < r),
      ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∀ (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤),
        ∃ C : NNReal → NNReal,
          ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (f : ℤ → ℂ),
            1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
            t ∈ Set.Icc (1/2 : ℝ) 1 →
            MeasureTheory.eLpNorm (fun x : ℤ => variationalNorm r
                (fun n : ℕ => Gcl ρ P C₀ a l₁ l₂ k₁ k₂ t f n x)) p MeasureTheory.Measure.count
              ≤ (C Λ : ENNReal) * ENNReal.ofReal (lossWeight A ρ l₁ l₂ k₁ k₂) *
                  MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  intro C₀ hC₀ r hr
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num : (1 : NNReal) ≤ 2) hr.le
  refine ⟨4, by norm_num, min 1 (1 / (2 * (C₀ : ℝ))), lt_min one_pos (by positivity), ?_⟩
  intro ρ hρ hρρ₀
  have hρ1 : ρ ≤ 1 := le_trans hρρ₀ (min_le_left _ _)
  have hρC : ρ ≤ 1 / (2 * (C₀ : ℝ)) := le_trans hρρ₀ (min_le_right _ _)
  have hρ0 : (0 : ℝ) ≤ ρ := hρ.le
  intro p hp hptop
  have hp1 : (1 : ENNReal) ≤ p := le_of_lt hp
  have hsub : ∀ u w : ℕ → ℂ,
      variationalNorm r (u - w)
        ≤ variationalNorm r u
          + variationalNorm r w := by
    intro u w
    rw [sub_eq_add_neg]
    refine (variationalNorm_add_le hr1 u (-w)).trans ?_
    have h2 : variationalNorm r (-w)
        = variationalNorm r w := by
      have h3 : (-1 : ℂ) • w = -w := by funext n; simp
      rw [← h3, variationalNorm_smul (r := r) hr1 (-1 : ℂ) w]
      simp
    rw [h2]
  have key : ∀ Λ : NNReal, ∃ c : NNReal,
      ∀ (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (f : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        t ∈ Set.Icc (1/2 : ℝ) 1 →
        MeasureTheory.eLpNorm (fun x : ℤ => variationalNorm r
            (fun n : ℕ => Gcl ρ P C₀ a l₁ l₂ k₁ k₂ t f n x)) p MeasureTheory.Measure.count
          ≤ (c : ENNReal) * ENNReal.ofReal (lossWeight 4 ρ l₁ l₂ k₁ k₂) *
              MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
    intro Λ
    by_cases hΛ : 1 < Λ
    · obtain ⟨CρcF, hCρcF3, KF, hKFpos, hF⟩ :=
        lacunaryBumpFareyPartBoundG P P.natDegree hdeg le_rfl C₀ r hr ρ hρ hρ1 Λ hΛ p hp hptop
      obtain ⟨CρcD, hCρcD3, KD, hKDpos, hD⟩ :=
        lacunaryBumpFareyDiffPartBoundG P P.natDegree hdeg le_rfl C₀ r hr ρ hρ hρ1 Λ hΛ p hp hptop
      obtain ⟨Cρlow, hCρlowpos, Clow, hClowpos, hLow⟩ := hLowpass ρ hρ hρ1 r hr p hp hptop Λ hΛ
      obtain ⟨CbadF, hCbadFpos, hBadF⟩ :=
        hBadPart ρ hρ hρ1 C₀ hC₀ hρC CρcF hCρcF3 Λ hΛ r hr p hp hptop
      set Cρc₀ : ℝ := max CρcD Cρlow with hCρc₀def
      have h3₀ : 3 ≤ Cρc₀ := le_trans hCρcD3 (le_max_left _ _)
      have hDC₀ : CρcD ≤ Cρc₀ := le_max_left _ _
      have hLC₀ : Cρlow ≤ Cρc₀ := le_max_right _ _
      obtain ⟨Cbad0, hCbad0pos, hBad0⟩ :=
        hBadPart ρ hρ hρ1 C₀ hC₀ hρC Cρc₀ h3₀ Λ hΛ r hr p hp hptop
      set Ktot : ℝ := max 1 (max (2 * (KF : ℝ) + CbadF)
        (6 * (KD : ℝ) + 6 * (Clow : ℝ) + Cbad0)) with hKtotdef
      have hKtot1 : (1 : ℝ) ≤ Ktot := le_max_left _ _
      have hKtotF : 2 * (KF : ℝ) + CbadF ≤ Ktot :=
        le_trans (le_max_left _ _) (le_max_right _ _)
      have hKtotD : 6 * (KD : ℝ) + 6 * (Clow : ℝ) + Cbad0 ≤ Ktot :=
        le_trans (le_max_right _ _) (le_max_right _ _)
      have hKtotpos : (0 : ℝ) < Ktot := lt_of_lt_of_le zero_lt_one hKtot1
      refine ⟨ENNReal.toNNReal (ENNReal.ofReal Ktot + 1), ?_⟩
      intro a l₁ l₂ k₁ k₂ t f hΛ' ha ha1 ht
      have hmain : MeasureTheory.eLpNorm (fun x : ℤ =>
            variationalNorm r
              (fun n : ℕ => Gcl ρ P C₀ a l₁ l₂ k₁ k₂ t f n x)) p MeasureTheory.Measure.count
          ≤ ENNReal.ofReal Ktot * ENNReal.ofReal (lossWeight 4 ρ l₁ l₂ k₁ k₂) *
              MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
        by_cases hl₂0 : l₂ = 0
        · subst hl₂0
          have hz : Gcl ρ P C₀ a l₁ 0 k₁ k₂ t f = 0 := by
            funext n
            simp only [Gcl]
            by_cases hc : core ρ C₀ l₁ 0 k₁ k₂ a n
            · rw [if_pos hc]
              exact Tex_zero_level ρ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) f
            · simp [hc]
          have h0 : variationalNorm r (0 : ℕ → ℂ) = 0 := by
            have h := variationalNorm_smul (r := r) hr1 (0 : ℂ) (0 : ℕ → ℂ)
            rw [zero_smul, enorm_zero, zero_mul] at h
            exact h
          have hz0 : (fun x : ℤ => variationalNorm r
              (fun n : ℕ => (0 : ℕ → ℤ → ℂ) n x)) = (0 : ℤ → ℝ≥0∞) := by
            funext x
            have h1 : (fun n : ℕ => (0 : ℕ → ℤ → ℂ) n x) = (0 : ℕ → ℂ) := by
              funext n; simp
            rw [h1]
            exact h0
          rw [hz, hz0, MeasureTheory.eLpNorm_zero]
          exact bot_le
        · have hl₂ : 1 ≤ l₂ := Nat.one_le_iff_ne_zero.mpr hl₂0
          rcases Nat.eq_zero_or_pos k₂ with hk₂0 | hk₂pos
          · subst hk₂0
            set D1 : ℕ → ℤ → ℂ := fun n x => Tle ρ l₂ (fun ξ : ℝ =>
              if core ρ C₀ l₁ l₂ k₁ 0 a n ∧ Farey CρcD ρ l₂ 0 a n
              then varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t ξ - varphitildeN P.natDegree (Nat.floor (a n)) 0 ξ else 0) f x
              with hD1def
            set D2 : ℕ → ℤ → ℂ := fun n x => Tle ρ (l₂ - 1) (fun ξ : ℝ =>
              if core ρ C₀ l₁ l₂ k₁ 0 a n ∧ Farey CρcD ρ l₂ 0 a n
              then varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t ξ - varphitildeN P.natDegree (Nat.floor (a n)) 0 ξ else 0) f x
              with hD2def
            set Alp : ℕ → ℤ → ℂ := fun n x =>
              if core ρ C₀ l₁ l₂ k₁ 0 a n ∧ Farey Cρc₀ ρ l₂ 0 a n
              then Tex ρ l₂ (varphitildeN P.natDegree (Nat.floor (a n)) 0) f x else 0 with hAlpdef
            set Adp : ℕ → ℤ → ℂ := fun n x =>
              if core ρ C₀ l₁ l₂ k₁ 0 a n ∧ Farey Cρc₀ ρ l₂ 0 a n
              then Tex ρ l₂ (fun ξ : ℝ => varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t ξ
                - varphitildeN P.natDegree (Nat.floor (a n)) 0 ξ) f x else 0 with hAdpdef
            set A : ℕ → ℤ → ℂ := fun n x =>
              if core ρ C₀ l₁ l₂ k₁ 0 a n ∧ Farey Cρc₀ ρ l₂ 0 a n
              then Tex ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t) f x else 0 with hAdef
            set Bp : ℕ → ℤ → ℂ := fun n x =>
              if core ρ C₀ l₁ l₂ k₁ 0 a n ∧ ¬ Farey Cρc₀ ρ l₂ 0 a n
              then Tex ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t) f x else 0 with hBpdef
            set L1 : ℕ → ℤ → ℂ := fun n x =>
              if core ρ C₀ l₁ l₂ k₁ 0 a n ∧ Farey Cρc₀ ρ l₂ 0 a n
              then Tle ρ l₂ (varphitildeN P.natDegree (Nat.floor (a n)) 0) f x else 0 with hL1def
            set L2 : ℕ → ℤ → ℂ := fun n x =>
              if core ρ C₀ l₁ l₂ k₁ 0 a n ∧ Farey Cρc₀ ρ l₂ 0 a n
              then Tle ρ (l₂ - 1) (varphitildeN P.natDegree (Nat.floor (a n)) 0) f x else 0 with hL2def
            set M1 : ℕ → ℤ → ℂ := fun n x =>
              if core ρ C₀ l₁ l₂ k₁ 0 a n ∧ Farey Cρc₀ ρ l₂ 0 a n
              then Tle ρ l₂ (fun ξ : ℝ => varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t ξ
                - varphitildeN P.natDegree (Nat.floor (a n)) 0 ξ) f x else 0 with hM1def
            set M2 : ℕ → ℤ → ℂ := fun n x =>
              if core ρ C₀ l₁ l₂ k₁ 0 a n ∧ Farey Cρc₀ ρ l₂ 0 a n
              then Tle ρ (l₂ - 1) (fun ξ : ℝ => varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t ξ
                - varphitildeN P.natDegree (Nat.floor (a n)) 0 ξ) f x else 0 with hM2def
            have hsplit : Gcl ρ P C₀ a l₁ l₂ k₁ 0 t f = A + Bp := by
              funext n x
              simp only [Gcl, hAdef, hBpdef, Pi.add_apply]
              by_cases hc : core ρ C₀ l₁ l₂ k₁ 0 a n
              · by_cases hF : Farey Cρc₀ ρ l₂ 0 a n
                · rw [if_pos hc, if_pos ⟨hc, hF⟩, if_neg (fun h => h.2 hF)]
                  simp
                · rw [if_pos hc, if_neg (fun h => hF h.2), if_pos ⟨hc, hF⟩]
                  simp
              · rw [if_neg hc, if_neg (fun h => hc h.1), if_neg (fun h => hc h.1)]
                simp
            by_cases hfin : ∃ Bf : ℝ, ∀ m : ℤ, ‖f m‖ ≤ Bf
            · obtain ⟨Bf, hBf⟩ := hfin
              have hXteL : ∀ n : ℕ, Tex ρ l₂ (varphitildeN P.natDegree (Nat.floor (a n)) 0) f
                  = Tle ρ l₂ (varphitildeN P.natDegree (Nat.floor (a n)) 0) f
                    - Tle ρ (l₂ - 1) (varphitildeN P.natDegree (Nat.floor (a n)) 0) f := by
                intro n
                exact Tex_eq_Tle_sub_of_bounded ρ hρ hρ1 hl₂
                  (adm_of_bump (contDiff_varphitildeN P.natDegree (Nat.floor (a n)) 0)
                    (hasCompactSupport_varphitildeN P.natDegree (Nat.floor (a n)) 0))
                  (adm_of_bump (contDiff_varphitildeN P.natDegree (Nat.floor (a n)) 0)
                    (hasCompactSupport_varphitildeN P.natDegree (Nat.floor (a n)) 0)) hBf
              have hXteD : ∀ n : ℕ, Tex ρ l₂ (fun ξ : ℝ => varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t ξ
                    - varphitildeN P.natDegree (Nat.floor (a n)) 0 ξ) f
                  = Tle ρ l₂ (fun ξ : ℝ => varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t ξ
                      - varphitildeN P.natDegree (Nat.floor (a n)) 0 ξ) f
                    - Tle ρ (l₂ - 1) (fun ξ : ℝ => varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t ξ
                      - varphitildeN P.natDegree (Nat.floor (a n)) 0 ξ) f := by
                intro n
                have hfun : (fun ξ : ℝ => varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t ξ
                      - varphitildeN P.natDegree (Nat.floor (a n)) 0 ξ)
                    = (fun ξ : ℝ => varphitildeN P.natDegree (Nat.floor (a n)) 0 ξ
                        * (ee (PevalR P ((Nat.floor (a n) : ℝ) * t) * ξ) - 1)) := by
                  funext ξ
                  rw [show varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t ξ
                      = varphitildeN P.natDegree (Nat.floor (a n)) 0 ξ
                        * ee (PevalR P ((Nat.floor (a n) : ℝ) * t) * ξ) from rfl]
                  ring
                rw [hfun]
                refine Tex_eq_Tle_sub_of_bounded ρ hρ hρ1 hl₂ ?_ ?_ hBf
                · exact adm_of_bump ((contDiff_varphitildeN P.natDegree (Nat.floor (a n)) 0).mul
                      ((contDiff_ee_const_mul 2 (PevalR P ((Nat.floor (a n) : ℝ) * t))).sub contDiff_const))
                    ((hasCompactSupport_varphitildeN P.natDegree (Nat.floor (a n)) 0).mul_right)
                · exact adm_of_bump ((contDiff_varphitildeN P.natDegree (Nat.floor (a n)) 0).mul
                      ((contDiff_ee_const_mul 2 (PevalR P ((Nat.floor (a n) : ℝ) * t))).sub contDiff_const))
                    ((hasCompactSupport_varphitildeN P.natDegree (Nat.floor (a n)) 0).mul_right)
              have hXf : ∀ n : ℕ, Tex ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t) f
                  = Tex ρ l₂ (varphitildeN P.natDegree (Nat.floor (a n)) 0) f
                    + Tex ρ l₂ (fun ξ : ℝ => varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t ξ
                      - varphitildeN P.natDegree (Nat.floor (a n)) 0 ξ) f :=
                fun n => Tex_varphitildeNt_split_of_bounded P P.natDegree ρ l₂ (Nat.floor (a n)) t hBf
              have hbp : MeasureTheory.eLpNorm (fun x : ℤ =>
                    variationalNorm r (fun n : ℕ => Bp n x))
                    p MeasureTheory.Measure.count
                  ≤ ENNReal.ofReal Cbad0 * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
                rw [hBpdef]
                exact hBad0 a ha ha1 l₁ l₂ k₁ 0 t ht f Bf hBf
              have hD1b : MeasureTheory.eLpNorm (fun x : ℤ =>
                    variationalNorm r (fun n : ℕ => D1 n x))
                    p MeasureTheory.Measure.count
                  ≤ ENNReal.ofReal (KD * (1 + (l₂ : ℝ))) *
                      MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
                rw [hD1def]
                exact hD l₂ l₁ l₂ k₁ 0 le_rfl t ht a ha ha1 f
              have hD2b : MeasureTheory.eLpNorm (fun x : ℤ =>
                    variationalNorm r (fun n : ℕ => D2 n x))
                    p MeasureTheory.Measure.count
                  ≤ ENNReal.ofReal (KD * (1 + (l₂ : ℝ))) *
                      MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
                rw [hD2def]
                exact hD (l₂ - 1) l₁ l₂ k₁ 0 (Nat.pred_le _) t ht a ha ha1 f
              have hL1b : MeasureTheory.eLpNorm (fun x : ℤ =>
                    variationalNorm r (fun n : ℕ => L1 n x))
                    p MeasureTheory.Measure.count
                  ≤ ENNReal.ofReal (3 * Clow * (1 + (l₂ : ℝ)) ^ 2) *
                      MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
                rw [hL1def]
                exact hLowClip ρ hρ hρ1 C₀ Cρc₀ Cρlow hCρlowpos hLC₀ Λ hΛ r hr p hp hptop
                  Clow hClowpos hLow a ha ha1 l₂ l₁ l₂ k₁ 0 le_rfl f
              have hL2b : MeasureTheory.eLpNorm (fun x : ℤ =>
                    variationalNorm r (fun n : ℕ => L2 n x))
                    p MeasureTheory.Measure.count
                  ≤ ENNReal.ofReal (3 * Clow * (1 + (l₂ : ℝ)) ^ 2) *
                      MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
                rw [hL2def]
                exact hLowClip ρ hρ hρ1 C₀ Cρc₀ Cρlow hCρlowpos hLC₀ Λ hΛ r hr p hp hptop
                  Clow hClowpos hLow a ha ha1 (l₂ - 1) l₁ l₂ k₁ 0 (Nat.pred_le _) f
              have hD1val : ∀ n : ℕ, core ρ C₀ l₁ l₂ k₁ 0 a n → Farey CρcD ρ l₂ 0 a n →
                  ∀ x : ℤ, D1 n x = Tle ρ l₂ (fun ξ : ℝ => varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t ξ
                    - varphitildeN P.natDegree (Nat.floor (a n)) 0 ξ) f x := by
                intro n hc hF x
                simp only [hD1def, Tle_ite,
                  if_pos (show core ρ C₀ l₁ l₂ k₁ 0 a n ∧ Farey CρcD ρ l₂ 0 a n
                    from ⟨hc, hF⟩)]
              have hD2val : ∀ n : ℕ, core ρ C₀ l₁ l₂ k₁ 0 a n → Farey CρcD ρ l₂ 0 a n →
                  ∀ x : ℤ, D2 n x = Tle ρ (l₂ - 1) (fun ξ : ℝ => varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t ξ
                    - varphitildeN P.natDegree (Nat.floor (a n)) 0 ξ) f x := by
                intro n hc hF x
                simp only [hD2def, Tle_ite,
                  if_pos (show core ρ C₀ l₁ l₂ k₁ 0 a n ∧ Farey CρcD ρ l₂ 0 a n
                    from ⟨hc, hF⟩)]
              have hM1b : MeasureTheory.eLpNorm (fun x : ℤ =>
                    variationalNorm r (fun n : ℕ => M1 n x)) p MeasureTheory.Measure.count
                  ≤ 3 * MeasureTheory.eLpNorm (fun x : ℤ =>
                      variationalNorm r (fun n : ℕ => D1 n x))
                        p MeasureTheory.Measure.count := by
                by_cases hS : ∃ n, core ρ C₀ l₁ l₂ k₁ 0 a n ∧ Farey Cρc₀ ρ l₂ 0 a n
                · obtain ⟨m, hm⟩ := core_and_farey_iff_le_G (monotone_of_lacunary hΛ ha ha1) hS
                  refine eLpNorm_variationalNorm_clip_le hr1 p m D1 M1 ?_ ?_
                  · intro n hn
                    funext x
                    simp only [hM1def, Pi.zero_apply,
                      if_neg (fun hcon => absurd ((hm n).mp hcon) (not_le.mpr hn))]
                  · intro n hn
                    have hcn := (hm n).mpr hn
                    funext x
                    simp only [hM1def, if_pos hcn]
                    exact (hD1val n hcn.1 (farey_mono_const hDC₀ hcn.2) x).symm
                · have hz : M1 = 0 := by
                    funext n x
                    simp only [hM1def, Pi.zero_apply, if_neg (fun hcon => hS ⟨n, hcon⟩)]
                  rw [hz]
                  have hz2 : (fun x : ℤ => variationalNorm r (fun n : ℕ => (0 : ℕ → ℤ → ℂ) n x))
                      = (fun x : ℤ => variationalNorm r (fun _ : ℕ => (0 : ℂ))) := by
                    funext x
                    congr 1
                  rw [hz2, eLpNorm_variationalNorm_zero hr1 p]
                  exact bot_le
              have hM1d : MeasureTheory.eLpNorm (fun x : ℤ =>
                    variationalNorm r (fun n : ℕ => M1 n x)) p MeasureTheory.Measure.count
                  ≤ ENNReal.ofReal (3 * (KD : ℝ) * (1 + (l₂ : ℝ)))
                      * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
                refine hM1b.trans ?_
                refine (mul_le_mul_of_nonneg_left hD1b (show (0 : ℝ≥0∞) ≤ 3 by norm_num)).trans (le_of_eq ?_)
                rw [show (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) by norm_num, ← mul_assoc,
                  ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
                  show (3 : ℝ) * (KD * (1 + (l₂ : ℝ))) = 3 * KD * (1 + (l₂ : ℝ)) by ring]
              have hM2b : MeasureTheory.eLpNorm (fun x : ℤ =>
                    variationalNorm r (fun n : ℕ => M2 n x)) p MeasureTheory.Measure.count
                  ≤ 3 * MeasureTheory.eLpNorm (fun x : ℤ =>
                      variationalNorm r (fun n : ℕ => D2 n x))
                        p MeasureTheory.Measure.count := by
                by_cases hS : ∃ n, core ρ C₀ l₁ l₂ k₁ 0 a n ∧ Farey Cρc₀ ρ l₂ 0 a n
                · obtain ⟨m, hm⟩ := core_and_farey_iff_le_G (monotone_of_lacunary hΛ ha ha1) hS
                  refine eLpNorm_variationalNorm_clip_le hr1 p m D2 M2 ?_ ?_
                  · intro n hn
                    funext x
                    simp only [hM2def, Pi.zero_apply,
                      if_neg (fun hcon => absurd ((hm n).mp hcon) (not_le.mpr hn))]
                  · intro n hn
                    have hcn := (hm n).mpr hn
                    funext x
                    simp only [hM2def, if_pos hcn]
                    exact (hD2val n hcn.1 (farey_mono_const hDC₀ hcn.2) x).symm
                · have hz : M2 = 0 := by
                    funext n x
                    simp only [hM2def, Pi.zero_apply, if_neg (fun hcon => hS ⟨n, hcon⟩)]
                  rw [hz]
                  have hz2 : (fun x : ℤ => variationalNorm r (fun n : ℕ => (0 : ℕ → ℤ → ℂ) n x))
                      = (fun x : ℤ => variationalNorm r (fun _ : ℕ => (0 : ℂ))) := by
                    funext x
                    congr 1
                  rw [hz2, eLpNorm_variationalNorm_zero hr1 p]
                  exact bot_le
              have hAleq : Alp = L1 - L2 := by
                funext n x
                simp only [hAlpdef, hL1def, hL2def, Pi.sub_apply]
                by_cases hcn : core ρ C₀ l₁ l₂ k₁ 0 a n ∧ Farey Cρc₀ ρ l₂ 0 a n
                · rw [if_pos hcn, if_pos hcn, if_pos hcn]
                  exact congrFun (hXteL n) x
                · rw [if_neg hcn, if_neg hcn, if_neg hcn]
                  simp
              have hMpeq : Adp = M1 - M2 := by
                funext n x
                simp only [hAdpdef, hM1def, hM2def, Pi.sub_apply]
                by_cases hcn : core ρ C₀ l₁ l₂ k₁ 0 a n ∧ Farey Cρc₀ ρ l₂ 0 a n
                · rw [if_pos hcn, if_pos hcn, if_pos hcn]
                  exact congrFun (hXteD n) x
                · rw [if_neg hcn, if_neg hcn, if_neg hcn]
                  simp
              have hM2d : MeasureTheory.eLpNorm (fun x : ℤ =>
                    variationalNorm r (fun n : ℕ => M2 n x)) p MeasureTheory.Measure.count
                  ≤ ENNReal.ofReal (3 * (KD : ℝ) * (1 + (l₂ : ℝ)))
                      * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
                refine hM2b.trans ?_
                refine (mul_le_mul_of_nonneg_left hD2b (show (0 : ℝ≥0∞) ≤ 3 by norm_num)).trans (le_of_eq ?_)
                rw [show (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) by norm_num, ← mul_assoc,
                  ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
                  show (3 : ℝ) * (KD * (1 + (l₂ : ℝ))) = 3 * KD * (1 + (l₂ : ℝ)) by ring]
              have hAadd : A = Alp + Adp := by
                funext n x
                simp only [hAdef, hAlpdef, hAdpdef, Pi.add_apply]
                by_cases hcn : core ρ C₀ l₁ l₂ k₁ 0 a n ∧ Farey Cρc₀ ρ l₂ 0 a n
                · rw [if_pos hcn, if_pos hcn, if_pos hcn]
                  exact congrFun (hXf n) x
                · rw [if_neg hcn, if_neg hcn, if_neg hcn]
                  simp
              have hAlpB : MeasureTheory.eLpNorm (fun x : ℤ =>
                    variationalNorm r (fun n : ℕ => Alp n x))
                    p MeasureTheory.Measure.count
                  ≤ ENNReal.ofReal (6 * (Clow : ℝ) * (1 + (l₂ : ℝ)) ^ 2)
                      * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
                rw [hAleq]
                refine (eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => ?_)).trans
                  ((eLpNorm_add_le (f := fun x : ℤ => variationalNorm r (fun n : ℕ => L1 n x))
                    (g := fun x : ℤ => variationalNorm r (fun n : ℕ => L2 n x))
                    hp1).trans ?_)
                · rw [enorm_eq_self, enorm_eq_self]
                  exact hsub _ _
                · refine (add_le_add hL1b hL2b).trans (le_of_eq ?_)
                  rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
                  congr 2
                  ring
              have hAdpB : MeasureTheory.eLpNorm (fun x : ℤ =>
                    variationalNorm r (fun n : ℕ => Adp n x))
                    p MeasureTheory.Measure.count
                  ≤ ENNReal.ofReal (6 * (KD : ℝ) * (1 + (l₂ : ℝ)))
                      * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
                rw [hMpeq]
                refine (eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => ?_)).trans
                  ((eLpNorm_add_le (f := fun x : ℤ => variationalNorm r (fun n : ℕ => M1 n x))
                    (g := fun x : ℤ => variationalNorm r (fun n : ℕ => M2 n x))
                    hp1).trans ?_)
                · rw [enorm_eq_self, enorm_eq_self]
                  exact hsub _ _
                · refine (add_le_add hM1d hM2d).trans (le_of_eq ?_)
                  rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity),
                    show 3 * (KD : ℝ) * (1 + (l₂ : ℝ)) + 3 * (KD : ℝ) * (1 + (l₂ : ℝ))
                      = 6 * (KD : ℝ) * (1 + (l₂ : ℝ)) by ring]
              have hAb : MeasureTheory.eLpNorm (fun x : ℤ =>
                    variationalNorm r (fun n : ℕ => A n x))
                    p MeasureTheory.Measure.count
                  ≤ ENNReal.ofReal (6 * (KD : ℝ) * (1 + (l₂ : ℝ))
                      + 6 * (Clow : ℝ) * (1 + (l₂ : ℝ)) ^ 2)
                      * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
                rw [hAadd]
                refine (eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => ?_)).trans
                  ((eLpNorm_add_le (f := fun x : ℤ => variationalNorm r (fun n : ℕ => Alp n x))
                    (g := fun x : ℤ => variationalNorm r (fun n : ℕ => Adp n x))
                    hp1).trans ?_)
                · rw [enorm_eq_self, enorm_eq_self]
                  exact variationalNorm_add_le hr1 _ _
                · refine (add_le_add hAlpB hAdpB).trans (le_of_eq ?_)
                  rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
                  congr 2
                  ring
              have hstep : MeasureTheory.eLpNorm (fun x : ℤ =>
                    variationalNorm r
                      (fun n : ℕ => Gcl ρ P C₀ a l₁ l₂ k₁ 0 t f n x)) p MeasureTheory.Measure.count
                  ≤ ENNReal.ofReal (6 * (KD : ℝ) * (1 + (l₂ : ℝ))
                        + 6 * (Clow : ℝ) * (1 + (l₂ : ℝ)) ^ 2)
                      * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count
                    + ENNReal.ofReal Cbad0 * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
                rw [hsplit]
                refine (eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => ?_)).trans
                  ((eLpNorm_add_le (f := fun x : ℤ => variationalNorm r (fun n : ℕ => A n x))
                    (g := fun x : ℤ => variationalNorm r (fun n : ℕ => Bp n x))
                    hp1).trans ?_)
                · rw [enorm_eq_self, enorm_eq_self]
                  have h1 : (fun n : ℕ => (A + Bp) n x)
                      = (fun n : ℕ => A n x) + (fun n : ℕ => Bp n x) := by
                    funext n; simp
                  rw [h1]
                  exact variationalNorm_add_le hr1 _ _
                · exact add_le_add hAb hbp
              refine hstep.trans ?_
              rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
              rw [← ENNReal.ofReal_mul (le_of_lt hKtotpos)]
              refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
              · have hlw1 : (1 : ℝ) ≤ lossWeight 4 ρ l₁ l₂ k₁ 0 :=
                  assembly_one_le_lossWeight (by norm_num) hρ0 l₁ l₂ k₁ 0
                have hlw0 : (0 : ℝ) ≤ lossWeight 4 ρ l₁ l₂ k₁ 0 := le_trans zero_le_one hlw1
                have h1 : 6 * (KD : ℝ) * (1 + (l₂ : ℝ))
                    ≤ 6 * (KD : ℝ) * lossWeight 4 ρ l₁ l₂ k₁ 0 :=
                  mul_le_mul_of_nonneg_left (one_add_le_lossWeight hρ0 l₁ l₂ k₁ 0) (by positivity)
                have h2 : 6 * (Clow : ℝ) * (1 + (l₂ : ℝ)) ^ 2
                    ≤ 6 * (Clow : ℝ) * lossWeight 4 ρ l₁ l₂ k₁ 0 :=
                  mul_le_mul_of_nonneg_left (lossWeight_four_ge_sq hρ0 l₁ l₂ k₁ 0) (by positivity)
                have h4 : Cbad0 ≤ Cbad0 * lossWeight 4 ρ l₁ l₂ k₁ 0 := by
                  nlinarith [hCbad0pos, hlw1]
                have h5 : 6 * (KD : ℝ) * (1 + (l₂ : ℝ))
                      + 6 * (Clow : ℝ) * (1 + (l₂ : ℝ)) ^ 2 + Cbad0
                    ≤ Ktot * lossWeight 4 ρ l₁ l₂ k₁ 0 := by
                  nlinarith [h1, h2, h4, hKtotD, hlw0]
                exact h5
            · have htop : MeasureTheory.eLpNorm f p MeasureTheory.Measure.count = ⊤ := by
                by_contra hne
                exact hfin (eLpNorm_finite_bounded p hp1 f (lt_top_iff_ne_top.mpr hne))
              have hKne : ENNReal.ofReal Ktot ≠ 0 :=
                ENNReal.ofReal_ne_zero_iff.mpr hKtotpos
              have hlwne : ENNReal.ofReal (lossWeight 4 ρ l₁ l₂ k₁ 0) ≠ 0 :=
                ENNReal.ofReal_ne_zero_iff.mpr (lt_of_lt_of_le zero_lt_one
                  (assembly_one_le_lossWeight (by norm_num) hρ0 l₁ l₂ k₁ 0))
              rw [htop, ENNReal.mul_top (mul_ne_zero hKne hlwne)]
              exact le_top
          · set A : ℕ → ℤ → ℂ := fun n x =>
              if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey CρcF ρ l₂ k₂ a n
              then Tex ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) f x else 0 with hAdef
            set Bp : ℕ → ℤ → ℂ := fun n x =>
              if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ ¬ Farey CρcF ρ l₂ k₂ a n
              then Tex ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) f x else 0 with hBpdef
            set G1 : ℕ → ℤ → ℂ := fun n x => Tle ρ l₂ (fun ξ : ℝ =>
              if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey CρcF ρ l₂ k₂ a n
              then varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t ξ else 0) f x with hG1def
            set G2 : ℕ → ℤ → ℂ := fun n x => Tle ρ (l₂ - 1) (fun ξ : ℝ =>
              if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey CρcF ρ l₂ k₂ a n
              then varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t ξ else 0) f x with hG2def
            have hsplit : Gcl ρ P C₀ a l₁ l₂ k₁ k₂ t f = A + Bp := by
              funext n x
              simp only [Gcl, hAdef, hBpdef, Pi.add_apply]
              by_cases hc : core ρ C₀ l₁ l₂ k₁ k₂ a n
              · by_cases hF : Farey CρcF ρ l₂ k₂ a n
                · rw [if_pos hc, if_pos ⟨hc, hF⟩, if_neg (fun h => h.2 hF)]
                  simp
                · rw [if_pos hc, if_neg (fun h => hF h.2), if_pos ⟨hc, hF⟩]
                  simp
              · rw [if_neg hc, if_neg (fun h => hc h.1), if_neg (fun h => hc h.1)]
                simp
            by_cases hfin : ∃ Bf : ℝ, ∀ m : ℤ, ‖f m‖ ≤ Bf
            · obtain ⟨Bf, hBf⟩ := hfin
              have hXte : ∀ n : ℕ, Tex ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) f
                  = Tle ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) f
                    - Tle ρ (l₂ - 1) (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) f := by
                intro n
                exact Tex_eq_Tle_sub_of_bounded ρ hρ hρ1 hl₂
                  (adm_of_bump (Work.KMTPlan.A6.contDiff_varphitildeNt_aux P P.natDegree (Nat.floor (a n)) k₂ t)
                    (Work.KMTPlan.A6.hasCompactSupport_varphitildeNt_aux P P.natDegree (Nat.floor (a n)) k₂ t))
                  (adm_of_bump (Work.KMTPlan.A6.contDiff_varphitildeNt_aux P P.natDegree (Nat.floor (a n)) k₂ t)
                    (Work.KMTPlan.A6.hasCompactSupport_varphitildeNt_aux P P.natDegree (Nat.floor (a n)) k₂ t)) hBf
              have hbpF : MeasureTheory.eLpNorm (fun x : ℤ =>
                    variationalNorm r (fun n : ℕ => Bp n x))
                    p MeasureTheory.Measure.count
                  ≤ ENNReal.ofReal CbadF * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
                rw [hBpdef]
                exact hBadF a ha ha1 l₁ l₂ k₁ k₂ t ht f Bf hBf
              have hG1b : MeasureTheory.eLpNorm (fun x : ℤ =>
                    variationalNorm r (fun n : ℕ => G1 n x))
                    p MeasureTheory.Measure.count
                  ≤ ENNReal.ofReal (KF * (1 + (l₂ : ℝ)) * (1 + (k₂ : ℝ))) *
                      MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
                rw [hG1def]
                exact hF k₂ hk₂pos l₂ l₁ l₂ k₁ le_rfl t ht a ha ha1 f
              have hG2b : MeasureTheory.eLpNorm (fun x : ℤ =>
                    variationalNorm r (fun n : ℕ => G2 n x))
                    p MeasureTheory.Measure.count
                  ≤ ENNReal.ofReal (KF * (1 + (l₂ : ℝ)) * (1 + (k₂ : ℝ))) *
                      MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
                rw [hG2def]
                exact hF k₂ hk₂pos (l₂ - 1) l₁ l₂ k₁ (Nat.pred_le _) t ht a ha ha1 f
              have hAeq : A = G1 - G2 := by
                funext n x
                simp only [hAdef, hG1def, hG2def, Pi.sub_apply]
                by_cases hcn : core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey CρcF ρ l₂ k₂ a n
                · rw [if_pos hcn]
                  have e1 := congrFun (Tle_ite ρ l₂
                    (core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey CρcF ρ l₂ k₂ a n)
                    (φ := varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) (f := f)) x
                  rw [if_pos hcn] at e1
                  have e2 := congrFun (Tle_ite ρ (l₂ - 1)
                    (core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey CρcF ρ l₂ k₂ a n)
                    (φ := varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) (f := f)) x
                  rw [if_pos hcn] at e2
                  rw [e1, e2]
                  exact congrFun (hXte n) x
                · rw [if_neg hcn]
                  have e1 := congrFun (Tle_ite ρ l₂
                    (core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey CρcF ρ l₂ k₂ a n)
                    (φ := varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) (f := f)) x
                  rw [if_neg hcn] at e1
                  have e2 := congrFun (Tle_ite ρ (l₂ - 1)
                    (core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey CρcF ρ l₂ k₂ a n)
                    (φ := varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) (f := f)) x
                  rw [if_neg hcn] at e2
                  rw [e1, e2]
                  simp
              have hAb : MeasureTheory.eLpNorm (fun x : ℤ =>
                    variationalNorm r (fun n : ℕ => A n x))
                    p MeasureTheory.Measure.count
                  ≤ ENNReal.ofReal (2 * (KF : ℝ) * (1 + (l₂ : ℝ)) * (1 + (k₂ : ℝ)))
                      * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
                rw [hAeq]
                refine (eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => ?_)).trans
                  ((eLpNorm_add_le (f := fun x : ℤ => variationalNorm r (fun n : ℕ => G1 n x))
                    (g := fun x : ℤ => variationalNorm r (fun n : ℕ => G2 n x))
                    hp1).trans ?_)
                · rw [enorm_eq_self, enorm_eq_self]
                  exact hsub _ _
                · refine (add_le_add hG1b hG2b).trans (le_of_eq ?_)
                  rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
                  congr 2
                  ring
              have hstep : MeasureTheory.eLpNorm (fun x : ℤ =>
                    variationalNorm r
                      (fun n : ℕ => Gcl ρ P C₀ a l₁ l₂ k₁ k₂ t f n x)) p MeasureTheory.Measure.count
                  ≤ ENNReal.ofReal (2 * (KF : ℝ) * (1 + (l₂ : ℝ)) * (1 + (k₂ : ℝ)))
                        * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count
                    + ENNReal.ofReal CbadF * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
                rw [hsplit]
                refine (eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => ?_)).trans
                  ((eLpNorm_add_le (f := fun x : ℤ => variationalNorm r (fun n : ℕ => A n x))
                    (g := fun x : ℤ => variationalNorm r (fun n : ℕ => Bp n x))
                    hp1).trans ?_)
                · rw [enorm_eq_self, enorm_eq_self]
                  have h1 : (fun n : ℕ => (A + Bp) n x)
                      = (fun n : ℕ => A n x) + (fun n : ℕ => Bp n x) := by
                    funext n; simp
                  rw [h1]
                  exact variationalNorm_add_le hr1 _ _
                · exact add_le_add hAb hbpF
              refine hstep.trans ?_
              rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
              rw [← ENNReal.ofReal_mul (le_of_lt hKtotpos)]
              refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
              · have hlw1 : (1 : ℝ) ≤ lossWeight 4 ρ l₁ l₂ k₁ k₂ :=
                  assembly_one_le_lossWeight (by norm_num) hρ0 l₁ l₂ k₁ k₂
                have hlw0 : (0 : ℝ) ≤ lossWeight 4 ρ l₁ l₂ k₁ k₂ := le_trans zero_le_one hlw1
                have h1 : 2 * (KF : ℝ) * (1 + (l₂ : ℝ)) * (1 + (k₂ : ℝ))
                    ≤ 2 * (KF : ℝ) * lossWeight 4 ρ l₁ l₂ k₁ k₂ := by
                  nlinarith [lossWeight_four_ge_mul hρ0 l₁ l₂ k₁ k₂, hKFpos]
                have h4 : CbadF ≤ CbadF * lossWeight 4 ρ l₁ l₂ k₁ k₂ := by
                  nlinarith [hCbadFpos, hlw1]
                have h5 : 2 * (KF : ℝ) * (1 + (l₂ : ℝ)) * (1 + (k₂ : ℝ)) + CbadF
                    ≤ Ktot * lossWeight 4 ρ l₁ l₂ k₁ k₂ := by
                  nlinarith [h1, h4, hKtotF, hlw0]
                exact h5
            · have htop : MeasureTheory.eLpNorm f p MeasureTheory.Measure.count = ⊤ := by
                by_contra hne
                exact hfin (eLpNorm_finite_bounded p hp1 f (lt_top_iff_ne_top.mpr hne))
              have hKne : ENNReal.ofReal Ktot ≠ 0 :=
                ENNReal.ofReal_ne_zero_iff.mpr hKtotpos
              have hlwne : ENNReal.ofReal (lossWeight 4 ρ l₁ l₂ k₁ k₂) ≠ 0 :=
                ENNReal.ofReal_ne_zero_iff.mpr (lt_of_lt_of_le zero_lt_one
                  (assembly_one_le_lossWeight (by norm_num) hρ0 l₁ l₂ k₁ k₂))
              rw [htop, ENNReal.mul_top (mul_ne_zero hKne hlwne)]
              exact le_top

      refine hmain.trans ?_
      have hcoe : ((ENNReal.toNNReal (ENNReal.ofReal Ktot + 1) : NNReal) : ENNReal)
          = ENNReal.ofReal Ktot + 1 := ENNReal.coe_toNNReal (by
            simp only [ne_eq, ENNReal.add_eq_top, not_or]
            exact ⟨ENNReal.ofReal_ne_top, ENNReal.one_ne_top⟩)
      rw [hcoe]
      exact mul_le_mul' (mul_le_mul' (le_add_right le_rfl) le_rfl) le_rfl
    · exact ⟨1, fun a l₁ l₂ k₁ k₂ t f hΛ' _ _ _ => absurd hΛ' hΛ⟩
  refine ⟨fun Λ => Classical.choose (key Λ), ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ t f hΛ ha ha1 ht
  exact Classical.choose_spec (key Λ) a l₁ l₂ k₁ k₂ t f hΛ ha ha1 ht

end

end Work.KMTAreas.A7Hi
