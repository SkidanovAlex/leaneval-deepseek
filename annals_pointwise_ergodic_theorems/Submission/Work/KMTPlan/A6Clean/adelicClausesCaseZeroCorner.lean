import Mathlib
import Submission.Work.KMTPlan.A6Clean.AdelicClausesAt
import Submission.Work.KMTPlan.A6Clean.mdlLiftZeroOfMdlCore
import Submission.Work.A6Clean.PacketFamFZeroUniform
import Submission.Work.A6Clean.PacketFamGZeroUniform
import Submission.Work.KMTAreas.A7Rep.fiberResidueMaxRephaseL2
import Submission.Work.KMTPlan.A6Clean.MdlPacketsStructuralND

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.KMTPlan.A6Clean

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators
open Work.KMTAreas.A7
open Work.KMTAreas.A7Rep
open Work.KMTPlan.A6

local notation "Circ" => Work.Analysis.IonescuWainger.Circle
local notation "logN" => Work.Analysis.EndVar.logN

noncomputable section

/-! ## Elementary helpers -/

/-- The `eLpNorm` of a constant against the probability measure `zmodProb Q`, at any exponent
`p ≠ 0`. -/
lemma eLpNorm_const_zmodProb_gen {Q : ℕ} [NeZero Q] {p : ENNReal} (hp : p ≠ 0) (c : ℂ) :
    eLpNorm (fun _ : ZMod Q => c) p (zmodProb Q) = ‖c‖ₑ := by
  have hμ : zmodProb Q ≠ 0 := by
    intro h0
    have h1 := zmodProb_univ (Q := Q)
    rw [h0] at h1
    simp at h1
  rw [eLpNorm_const c hp hμ, zmodProb_univ, ENNReal.one_rpow, mul_one]

/-- On a one-point `ZMod Q` (i.e. under `Subsingleton (ZMod Q)`), `zmodAvg` is a constant and the
`L^r`-bound of the arithmetic-bilinear package holds with the absolute constant `1`. -/
theorem cornerSubsingletonAvg {Q : ℕ} [NeZero Q] [Subsingleton (ZMod Q)]
    (P : Polynomial ℤ) {r : NNReal} (hr : 0 < r) (u v : ZMod Q → ℂ) :
    eLpNorm (fun ρ' : ZMod Q => zmodAvg P Q u v ρ') (r : ENNReal) (zmodProb Q)
      ≤ ENNReal.ofReal 1 * eLpNorm u 2 (zmodProb Q) * eLpNorm v 2 (zmodProb Q) := by
  have hQne : (Q : ℂ) ≠ 0 := by
    have hQ0 : (Q : ℕ) ≠ 0 := NeZero.ne Q
    exact_mod_cast hQ0
  have huv : ∀ θ : ZMod Q, zmodAvg P Q u v θ = u 0 * v 0 := by
    intro θ
    rw [zmodAvg]
    have hterm : ∀ y ∈ Finset.range Q,
        u (θ + (y : ZMod Q)) * v (θ + (((P.eval (y : ℤ) : ℤ)) : ZMod Q)) = u 0 * v 0 := by
      intro y _
      rw [Subsingleton.elim (θ + (y : ZMod Q)) 0,
        Subsingleton.elim (θ + (((P.eval (y : ℤ) : ℤ)) : ZMod Q)) 0]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ hQne, one_mul]
  have hfun : (fun ρ' : ZMod Q => zmodAvg P Q u v ρ') = fun _ : ZMod Q => u 0 * v 0 :=
    funext huv
  have hu : eLpNorm u 2 (zmodProb Q) = ‖u 0‖ₑ := by
    rw [show u = fun _ : ZMod Q => u 0 from funext (fun θ => by
      rw [Subsingleton.elim θ 0])]
    exact Work.A6Clean.eLpNorm_const_zmodProb (u 0)
  have hv : eLpNorm v 2 (zmodProb Q) = ‖v 0‖ₑ := by
    rw [show v = fun _ : ZMod Q => v 0 from funext (fun θ => by
      rw [Subsingleton.elim θ 0])]
    exact Work.A6Clean.eLpNorm_const_zmodProb (v 0)
  have hp : (r : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hr.ne'
  refine le_of_eq ?_
  rw [hfun, hu, hv, eLpNorm_const_zmodProb_gen (p := (r : ENNReal)) hp (u 0 * v 0),
    enorm_mul, ENNReal.ofReal_one, one_mul]

/-- On the core condition the two band radii of the §8 packets are `≤ 1/4` (a form of
`mainRegime`, one of the conjuncts of `mdlCore`). -/
theorem cornerBandQuarter (ρ : ℝ) (hρ : 0 < ρ) (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ n : ℕ)
    (hmc : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n) :
    (2 : ℝ) ^ ((k₁ : ℝ) - ((logN (Nat.floor (a n)) : ℤ) : ℝ)) ≤ 1 / 4 ∧
    (2 : ℝ) ^ ((P.natDegree : ℝ) *
        ((k₂ : ℝ) - ((logN (Nat.floor (a n)) : ℤ) : ℝ))) ≤ 1 / 4 := by
  have hmain := ((mdlCore_iff ρ C₀ a l₁ l₂ k₁ k₂ n).mp hmc).2.2
  obtain ⟨h1, h2⟩ := hmain
  have hlog0 : (0 : ℤ) ≤ logN (Nat.floor (a n)) := Work.Analysis.EndVar.logN_nonneg _
  have ht : ((logN (Nat.floor (a n))).toNat : ℤ) = logN (Nat.floor (a n)) :=
    Int.toNat_of_nonneg hlog0
  have hu : (1 : ℤ) ≤ (uScale ρ (max k₁ k₂) : ℤ) := by
    exact_mod_cast one_le_uScale ρ hρ.le (max k₁ k₂)
  have hexp₁ : (k₁ : ℤ) - logN (Nat.floor (a n)) ≤ -2 := by
    have h : (k₁ : ℤ) + 2 * (uScale ρ (max k₁ k₂) : ℤ) ≤ logN (Nat.floor (a n)) := by
      rw [← ht]; exact_mod_cast h1
    omega
  have hexp₂ : (P.natDegree : ℤ) * ((k₂ : ℤ) - logN (Nat.floor (a n))) ≤ -4 := by
    have h : (k₂ : ℤ) + 2 * (uScale ρ (max k₁ k₂) : ℤ) ≤ logN (Nat.floor (a n)) := by
      rw [← ht]; exact_mod_cast h2
    have hk : (k₂ : ℤ) - logN (Nat.floor (a n)) ≤ -2 := by omega
    have hd2 : (0 : ℤ) ≤ (P.natDegree : ℤ) := by
      have : 0 < P.natDegree := lt_of_lt_of_le (by norm_num) hd
      omega
    have h3 := mul_le_mul_of_nonneg_left hk hd2
    have hd3 : (2 : ℤ) ≤ (P.natDegree : ℤ) := by exact_mod_cast hd
    nlinarith
  constructor
  · have hcast : ((k₁ : ℝ) - ((logN (Nat.floor (a n)) : ℤ) : ℝ))
        = ((((k₁ : ℤ) - logN (Nat.floor (a n))) : ℤ) : ℝ) := by push_cast; ring
    rw [hcast]
    calc (2 : ℝ) ^ ((((k₁ : ℤ) - logN (Nat.floor (a n))) : ℤ) : ℝ)
        ≤ (2 : ℝ) ^ (((-2 : ℤ)) : ℝ) := by
          refine (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr ?_
          exact_mod_cast hexp₁
      _ = 1 / 4 := by norm_num
  · have hcast : ((P.natDegree : ℝ) * ((k₂ : ℝ) - ((logN (Nat.floor (a n)) : ℤ) : ℝ)))
        = ((((P.natDegree : ℤ) * ((k₂ : ℤ) - logN (Nat.floor (a n)))) : ℤ) : ℝ) := by
      push_cast; ring
    rw [hcast]
    calc (2 : ℝ) ^ ((((P.natDegree : ℤ) * ((k₂ : ℤ) - logN (Nat.floor (a n)))) : ℤ) : ℝ)
        ≤ (2 : ℝ) ^ (((-2 : ℤ)) : ℝ) := by
          refine (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr ?_
          exact_mod_cast (le_trans hexp₂ (by norm_num : (-4 : ℤ) ≤ -2))
      _ = 1 / 4 := by norm_num

/-! ## The structural clauses with explicit packets -/

/-- **The structural clauses** (band, diagonal identity, measurability) of the §8 adelic form, for
the explicit packet families `packetFamF ⋯ W₁` and `packetFamG ⋯ W₂`.  This is verbatim
`structuralClauses_explicit` of `adelicClausesCaseA`, reproduced here (the height-`0` sibling uses
it with the height-`0` lifts). -/
private theorem cornerStructExp
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal)
    (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ) (j₁ j₂ : ℤ) (t : ℝ)
    (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ)) (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ))
    (hk₁ : k₁ = 0 → j₁ ≠ -1) (hk₂ : k₂ = 0 → j₂ ≠ -1)
    (W₁ W₂ : ℕ → Circ → ℝ → ℂ) (δ₁ δ₂ : ℕ → ℝ) (β : ℝ)
    (hβ : ∀ n, goodScale (arithQ ρ (max l₁ l₂)) (lcL l₁ l₂ k₁ k₂) (Nat.floor (a n)) →
      δ₁ n + δ₂ n ≤ β)
    (hW₁b : ∀ (n : ℕ) (α : Circ), HasRealFreqSupport (W₁ n α) (Set.Icc (-(δ₁ n)) (δ₁ n)))
    (hW₂b : ∀ (n : ℕ) (α : Circ), HasRealFreqSupport (W₂ n α) (Set.Icc (-(δ₂ n)) (δ₂ n)))
    (hW₁c : ∀ (n : ℕ) (α : Circ), Measurable (W₁ n α))
    (hW₂c : ∀ (n : ℕ) (α : Circ), Measurable (W₂ n α))
    (hW₁s : ∀ (n : ℕ) (α : Circ), α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁ → ∀ x : ℤ,
      W₁ n α (x : ℝ) = winConvR (mStarF (uScale ρ (lcL l₁ l₂ k₁ k₂)))
        (winModR (-α) (mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n)) x)
    (hW₂s : ∀ (n : ℕ) (α : Circ), α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂ → ∀ x : ℤ,
      W₂ n α (x : ℝ) = winConvR (mStargF P.natDegree (uScale ρ (lcL l₁ l₂ k₁ k₂)))
        (winModR (-α) (mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n)) x)
    (hW₁sum : ∀ (n : ℕ) (z : ℤ), Summable (fun j : ℤ =>
      cw (mStarF (uScale ρ (lcL l₁ l₂ k₁ k₂))) j *
        mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n (z - j)))
    (hW₂sum : ∀ (n : ℕ) (z : ℤ), Summable (fun j : ℤ =>
      cw (mStargF P.natDegree (uScale ρ (lcL l₁ l₂ k₁ k₂))) j *
        mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n (z - j))) :
    (∀ (n : ℕ) (ρ' : ℤ), HasRealFreqSupport (fun X : ℝ =>
        zmodAvg (negReflect P) (arithQ ρ (max l₁ l₂))
          (packetFamF ρ a l₁ l₂ k₁ k₂ W₁ n X) (packetFamG ρ a l₁ l₂ k₁ k₂ W₂ n X)
          (((ρ' : ℤ)) : ZMod (arithQ ρ (max l₁ l₂)))) (Set.Icc (-β) β)) ∧
    (∀ (n : ℕ) (x : ℤ), zmodAvg (negReflect P) (arithQ ρ (max l₁ l₂))
        (packetFamF ρ a l₁ l₂ k₁ k₂ W₁ n (x : ℝ))
        (packetFamG ρ a l₁ l₂ k₁ k₂ W₂ n (x : ℝ))
        (((x % ((arithQ ρ (max l₁ l₂) : ℕ) : ℤ) : ℤ)) : ZMod (arithQ ρ (max l₁ l₂)))
      = (if goodScale (arithQ ρ (max l₁ l₂)) (lcL l₁ l₂ k₁ k₂) (Nat.floor (a n)) then
          mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x else 0)) ∧
    (∀ (n : ℕ) (θ : ZMod (arithQ ρ (max l₁ l₂))),
        AEMeasurable (fun X : ℝ => packetFamF ρ a l₁ l₂ k₁ k₂ W₁ n X θ)) ∧
    (∀ (n : ℕ) (θ : ZMod (arithQ ρ (max l₁ l₂))),
        AEMeasurable (fun X : ℝ => packetFamG ρ a l₁ l₂ k₁ k₂ W₂ n X θ)) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n ρ'
    by_cases hg : goodScale (arithQ ρ (max l₁ l₂)) (lcL l₁ l₂ k₁ k₂) (Nat.floor (a n))
    · have hb₁ : ∀ θ : ZMod (arithQ ρ (max l₁ l₂)),
          HasRealFreqSupport (fun X : ℝ => packetFamF ρ a l₁ l₂ k₁ k₂ W₁ n X θ)
            (Set.Icc (-(δ₁ n)) (δ₁ n)) := by
        intro θ
        simpa only [packetFamF_apply] using
          hasRealFreqSupport_gatedProfile_nd ρ C₀ a l₁ l₂ k₁ k₂ l₁ W₁ hW₁b n θ
      have hb₂ : ∀ θ : ZMod (arithQ ρ (max l₁ l₂)),
          HasRealFreqSupport (fun X : ℝ => packetFamG ρ a l₁ l₂ k₁ k₂ W₂ n X θ)
            (Set.Icc (-(δ₂ n)) (δ₂ n)) := by
        intro θ
        simpa only [packetFamG_apply] using
          hasRealFreqSupport_gatedProfile_nd ρ C₀ a l₁ l₂ k₁ k₂ l₂ W₂ hW₂b n θ
      exact hasRealFreqSupport_zmodAvg_packets P (arithQ ρ (max l₁ l₂))
        (fun θ X => packetFamF ρ a l₁ l₂ k₁ k₂ W₁ n X θ)
        (fun θ X => packetFamG ρ a l₁ l₂ k₁ k₂ W₂ n X θ)
        hb₁ hb₂ (hβ n hg) (((ρ' : ℤ)) : ZMod (arithQ ρ (max l₁ l₂)))
    · have hz : (fun X : ℝ => zmodAvg (negReflect P) (arithQ ρ (max l₁ l₂))
            (packetFamF ρ a l₁ l₂ k₁ k₂ W₁ n X) (packetFamG ρ a l₁ l₂ k₁ k₂ W₂ n X)
            (((ρ' : ℤ)) : ZMod (arithQ ρ (max l₁ l₂)))) = fun _ : ℝ => 0 := by
        funext X
        have hF0 : packetFamF ρ a l₁ l₂ k₁ k₂ W₁ n X =
            fun _ : ZMod (arithQ ρ (max l₁ l₂)) => (0 : ℂ) := by
          funext θ
          rw [packetFamF_apply, if_neg hg]
        have hG0 : packetFamG ρ a l₁ l₂ k₁ k₂ W₂ n X =
            fun _ : ZMod (arithQ ρ (max l₁ l₂)) => (0 : ℂ) := by
          funext θ
          rw [packetFamG_apply, if_neg hg]
        rw [hF0, hG0]
        simp [zmodAvg]
      rw [hz]
      exact hasRealFreqSupport_zero _
  · intro n x
    rw [intCast_emod_eq (arithQ ρ (max l₁ l₂)) x]
    have h₁ : packetFamF ρ a l₁ l₂ k₁ k₂ W₁ n (x : ℝ) =
        fun θ : ZMod (arithQ ρ (max l₁ l₂)) =>
          if goodScale (arithQ ρ (max l₁ l₂)) (lcL l₁ l₂ k₁ k₂) (Nat.floor (a n)) then
            ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁,
              fourier (T := 1) (-(θ.val : ℤ)) α * W₁ n α (x : ℝ)
          else 0 := by
      funext θ
      rw [packetFamF_apply]
    have h₂ : packetFamG ρ a l₁ l₂ k₁ k₂ W₂ n (x : ℝ) =
        fun θ : ZMod (arithQ ρ (max l₁ l₂)) =>
          if goodScale (arithQ ρ (max l₁ l₂)) (lcL l₁ l₂ k₁ k₂) (Nat.floor (a n)) then
            ∑ β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂,
              fourier (T := 1) (-(θ.val : ℤ)) β * W₂ n β (x : ℝ)
          else 0 := by
      funext θ
      rw [packetFamG_apply]
    rw [h₁, h₂]
    exact zmodAvg_gated_packets_eq_slice ρ hρ hρ1 P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x
      hj₁ hj₂ hk₁ hk₂ (W₁ n) (W₂ n)
      (fun α hα => hW₁s n α hα x) (fun β hβ' => hW₂s n β hβ' x) (hW₁sum n) (hW₂sum n)
  · intro n θ
    simpa only [packetFamF_apply] using
      aemeasurable_packetProfile_nd ρ C₀ a l₁ l₂ k₁ k₂ l₁ W₁ hW₁c n θ
  · intro n θ
    simpa only [packetFamG_apply] using
      aemeasurable_packetProfile_nd ρ C₀ a l₁ l₂ k₁ k₂ l₂ W₂ hW₂c n θ

/-! ## The main producer -/

theorem adelicClausesCaseZeroCorner (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (hI : Work.KMTContract.ImprovKMT P) (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (R : NNReal) (hR : 2 < R) (r : NNReal) (hr : 2 < r) (hrT : (r : ℝ) < Work.KMTPlan.A6.adelicRTop P) (j₁ j₂ : ℤ) (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ)) (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ)) :
    ∃ c : ℝ, 0 < c ∧ ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ Cin : NNReal → NNReal, ∀ (a : ℕ → NNReal) (Λ : NNReal) (k₁ k₂ : ℕ) (t : ℝ) (f g : ℤ → ℂ),
      1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) → t ∈ Set.Icc (1 / 2 : ℝ) 1 → (k₁ = 0 → j₁ ≠ -1) → (k₂ = 0 → j₂ ≠ -1) → MeasureTheory.MemLp f 2 MeasureTheory.Measure.count → MeasureTheory.MemLp g 2 MeasureTheory.Measure.count → Work.KMTPlan.A6Clean.AdelicClausesAt P ρ R r a Λ 0 0 k₁ k₂ t j₁ j₂ f g C₀ c A Cin := by
  classical
  obtain ⟨AF, hAF, ρF, hρF, hKF⟩ := Work.A6Clean.PacketFamFZeroUniform C₀ hC₀ R hR j₁ hj₁
  obtain ⟨AG, hAG, ρG, hρG, hKG⟩ := Work.A6Clean.PacketFamGZeroUniform P hd C₀ hC₀ R hR j₂ hj₂
  refine ⟨1, one_pos, max AF AG, le_trans hAF (le_max_left _ _),
    min 1 (min ρF ρG), lt_min one_pos (lt_min hρF hρG), ?_⟩
  intro ρ hρ hρle
  have hρ1 : ρ ≤ 1 := le_trans hρle (min_le_left _ _)
  have hρF' : ρ ≤ ρF := le_trans hρle (le_trans (min_le_right _ _) (min_le_left _ _))
  have hρG' : ρ ≤ ρG := le_trans hρle (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨KF, hKF'⟩ := hKF ρ hρ hρF'
  obtain ⟨KG, hKG'⟩ := hKG ρ hρ hρG'
  let Cin : NNReal → NNReal := fun Λ => max (max (KF Λ) (KG Λ)) 2
  refine ⟨Cin, ?_⟩
  intro a Λ k₁ k₂ t f g hΛ ha ha1 ht hk₁ hk₂ hf hg
  -- ### the two height-`0` lift families
  obtain ⟨W₁, hW₁meas, hW₁band, hW₁zero, hW₁samp, hW₁sum, hW₁zeroCore⟩ :=
    exists_liftFamilyFZero ρ hρ hρ1 P hd C₀ a f hf 0 k₁ k₂ j₁ hj₁ hk₁ t ha1
  obtain ⟨W₂, hW₂meas, hW₂band, hW₂zero, hW₂samp, hW₂sum, hW₂zeroCore⟩ :=
    exists_liftFamilyGZero ρ hρ hρ1 P hd C₀ a g hg 0 k₁ k₂ j₂ hj₂ hk₂ t ha1
  -- ### the structural clauses
  let δ₁ : ℕ → ℝ := fun n => (2 : ℝ) ^ ((k₁ : ℝ) - ((logN (Nat.floor (a n)) : ℤ) : ℝ))
  let δ₂ : ℕ → ℝ := fun n =>
    (2 : ℝ) ^ ((P.natDegree : ℝ) * ((k₂ : ℝ) - ((logN (Nat.floor (a n)) : ℤ) : ℝ)))
  let β : ℝ := 1 / (8 * (arithQ ρ (max 0 0) : ℝ))
  have hβ : ∀ n, goodScale (arithQ ρ (max 0 0)) (lcL 0 0 k₁ k₂) (Nat.floor (a n)) →
      δ₁ n + δ₂ n ≤ β := by
    intro n hn
    simp only [δ₁, δ₂, β]
    exact goodScale_two_pow_bands_le (arithQ ρ (max 0 0)) (lcL 0 0 k₁ k₂)
      (Nat.floor (a n)) k₁ k₂ P.natDegree hd (one_le_arithQ ρ (max 0 0)) hn
      (le_trans (le_max_left k₁ k₂) (le_max_right _ _))
      (le_trans (le_max_right k₁ k₂) (le_max_right _ _))
  obtain ⟨hband, hdiag, humeas, hvmeas⟩ :=
    cornerStructExp ρ hρ hρ1 P C₀ a f g 0 0 k₁ k₂ j₁ j₂ t hj₁ hj₂ hk₁ hk₂
      W₁ W₂ δ₁ δ₂ β hβ hW₁band hW₂band hW₁meas hW₂meas
      (fun n α hα x => hW₁samp n α hα x) (fun n α hα x => hW₂samp n α hα x)
      (fun n z => hW₁sum n z) (fun n z => hW₂sum n z)
  -- ### the `f`-side `(lin-1)` datum bound
  have hband₁4 : ∀ (n : ℕ) (α : Circ),
      HasRealFreqSupport (W₁ n α) (Set.Icc (-(1 / 4 : ℝ)) (1 / 4)) := by
    intro n α
    by_cases hc : mdlCore ρ C₀ a 0 0 k₁ k₂ n
    · have hquarter := (cornerBandQuarter ρ hρ P hd C₀ a 0 0 k₁ k₂ n hc).1
      refine hasRealFreqSupport_mono (fun x hx => ?_) (hW₁band n α)
      simp only [Set.mem_Icc] at hx ⊢
      exact ⟨by linarith [hx.1, hquarter], by linarith [hx.2, hquarter]⟩
    · rw [hW₁zeroCore n hc]
      exact hasRealFreqSupport_zero _
  have hlwA : (0 : ℝ) ≤ lossWeight (max AF AG) ρ 0 0 k₁ k₂ :=
    le_trans zero_le_one
      (Work.KMTAreas.A7Hi.one_le_lossWeight_of_nonneg (max AF AG) ρ
        (le_trans hAF (le_max_left _ _)) hρ.le 0 0 k₁ k₂)
  have hKFi : ENNReal.ofReal (lossWeight AF ρ 0 0 k₁ k₂)
      ≤ ENNReal.ofReal (lossWeight (max AF AG) ρ 0 0 k₁ k₂) :=
    ENNReal.ofReal_le_ofReal
      (Work.KMTAreas.A7Hi.lossWeight_mono (le_max_left _ _) hAF hρ.le 0 0 k₁ k₂)
  have hpowF : (ENNReal.ofReal (lossWeight AF ρ 0 0 k₁ k₂)) ^ (2 : ℕ)
      ≤ (ENNReal.ofReal (lossWeight (max AF AG) ρ 0 0 k₁ k₂)) ^ (2 : ℕ) :=
    pow_le_pow_left₀ zero_le hKFi 2
  have hFint : ∫⁻ X : ℝ, (VrLiftDataP (R : ℝ) (arithQ ρ (max 0 0))
        (fun n : ℕ => packetFamF ρ a 0 0 k₁ k₂ W₁ n X)) ^ (2 : ℕ)
      ≤ (KF Λ : ENNReal) ^ (2 : ℕ)
        * (ENNReal.ofReal (lossWeight (max AF AG) ρ 0 0 k₁ k₂)) ^ (2 : ℕ)
        * (MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count) ^ (2 : ℕ) := by
    refine le_trans (hKF' a Λ 0 k₁ k₂ t f W₁ hΛ ha ha1 hf ht hk₁ hband₁4
      (fun n α hα x => hW₁samp n α hα x)) ?_
    exact mul_le_mul' (mul_le_mul_right hpowF ((KF Λ : ENNReal) ^ (2 : ℕ))) le_rfl
  let F₂ : ℝ := (MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count).toReal
  have hF₂ : ENNReal.ofReal F₂ = MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
    simp only [F₂, ENNReal.ofReal_toReal (MeasureTheory.MemLp.eLpNorm_lt_top hf).ne]
  let Ku : ℝ := ((KF Λ : NNReal) : ℝ) * lossWeight (max AF AG) ρ 0 0 k₁ k₂ * F₂
  have hKu_nn : 0 ≤ Ku := by
    simp only [Ku]
    exact mul_nonneg (mul_nonneg (NNReal.coe_nonneg _) hlwA) (ENNReal.toReal_nonneg)
  have hKu_eq : ENNReal.ofReal Ku = (KF Λ : ENNReal)
      * ENNReal.ofReal (lossWeight (max AF AG) ρ 0 0 k₁ k₂)
      * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
    rw [show Ku = ((KF Λ : NNReal) : ℝ) * lossWeight (max AF AG) ρ 0 0 k₁ k₂ * F₂ from rfl,
      ENNReal.ofReal_mul (mul_nonneg (NNReal.coe_nonneg _) hlwA),
      ENNReal.ofReal_mul (NNReal.coe_nonneg _), hF₂, ENNReal.ofReal_coe_nnreal]
  have hKu_bound : ENNReal.ofReal Ku ≤ (Cin Λ : ENNReal)
      * ENNReal.ofReal (lossWeight (max AF AG) ρ 0 0 k₁ k₂)
      * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
    have hstep : (KF Λ : ENNReal) ≤ (Cin Λ : ENNReal) := by
      have h1 : ((KF Λ : NNReal) : ℝ) ≤ ((Cin Λ : NNReal) : ℝ) := by
        dsimp only [Cin]
        exact le_trans (le_max_left _ _) (le_max_left _ _)
      calc (KF Λ : ENNReal) = ENNReal.ofReal ((KF Λ : NNReal) : ℝ) :=
            (ENNReal.ofReal_coe_nnreal (p := KF Λ)).symm
        _ ≤ ENNReal.ofReal ((Cin Λ : NNReal) : ℝ) := ENNReal.ofReal_le_ofReal h1
        _ = (Cin Λ : ENNReal) := ENNReal.ofReal_coe_nnreal
    rw [hKu_eq]
    exact mul_le_mul'
      (mul_le_mul_left hstep (ENNReal.ofReal (lossWeight (max AF AG) ρ 0 0 k₁ k₂))) le_rfl
  have hKu_int : ∫⁻ X : ℝ, (VrLiftDataP (R : ℝ) (arithQ ρ (max 0 0))
        (fun n : ℕ => packetFamF ρ a 0 0 k₁ k₂ W₁ n X)) ^ (2 : ℕ)
      ≤ ENNReal.ofReal (Ku ^ 2) := by
    rw [ENNReal.ofReal_pow hKu_nn, hKu_eq, mul_pow, mul_pow]
    exact hFint
  -- ### the `g`-side `(lin-2)` datum bound
  have hband₂4 : ∀ (n : ℕ) (α : Circ),
      HasRealFreqSupport (W₂ n α) (Set.Icc (-(1 / 4 : ℝ)) (1 / 4)) := by
    intro n α
    by_cases hc : mdlCore ρ C₀ a 0 0 k₁ k₂ n
    · have hquarter := (cornerBandQuarter ρ hρ P hd C₀ a 0 0 k₁ k₂ n hc).2
      refine hasRealFreqSupport_mono (fun x hx => ?_) (hW₂band n α)
      simp only [Set.mem_Icc] at hx ⊢
      exact ⟨by linarith [hx.1, hquarter], by linarith [hx.2, hquarter]⟩
    · rw [hW₂zeroCore n hc]
      exact hasRealFreqSupport_zero _
  have hKGi : ENNReal.ofReal (lossWeight AG ρ 0 0 k₁ k₂)
      ≤ ENNReal.ofReal (lossWeight (max AF AG) ρ 0 0 k₁ k₂) :=
    ENNReal.ofReal_le_ofReal
      (Work.KMTAreas.A7Hi.lossWeight_mono (le_max_right _ _) hAG hρ.le 0 0 k₁ k₂)
  have hpowG : (ENNReal.ofReal (lossWeight AG ρ 0 0 k₁ k₂)) ^ (2 : ℕ)
      ≤ (ENNReal.ofReal (lossWeight (max AF AG) ρ 0 0 k₁ k₂)) ^ (2 : ℕ) :=
    pow_le_pow_left₀ zero_le hKGi 2
  have hGint : ∫⁻ X : ℝ, (VrLiftDataP (R : ℝ) (arithQ ρ (max 0 0))
        (fun n : ℕ => packetFamG ρ a 0 0 k₁ k₂ W₂ n X)) ^ (2 : ℕ)
      ≤ (KG Λ : ENNReal) ^ (2 : ℕ)
        * (ENNReal.ofReal (lossWeight (max AF AG) ρ 0 0 k₁ k₂)) ^ (2 : ℕ)
        * (MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) ^ (2 : ℕ) := by
    refine le_trans (hKG' a Λ 0 k₁ k₂ t g W₂ hΛ ha ha1 hg ht hk₂ hband₂4
      (fun n α hα x => hW₂samp n α hα x)) ?_
    exact mul_le_mul' (mul_le_mul_right hpowG ((KG Λ : ENNReal) ^ (2 : ℕ))) le_rfl
  let G₂ : ℝ := (MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count).toReal
  have hG₂ : ENNReal.ofReal G₂ = MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
    simp only [G₂, ENNReal.ofReal_toReal (MeasureTheory.MemLp.eLpNorm_lt_top hg).ne]
  let Kv : ℝ := ((KG Λ : NNReal) : ℝ) * lossWeight (max AF AG) ρ 0 0 k₁ k₂ * G₂
  have hKv_nn : 0 ≤ Kv := by
    simp only [Kv]
    exact mul_nonneg (mul_nonneg (NNReal.coe_nonneg _) hlwA) (ENNReal.toReal_nonneg)
  have hKv_eq : ENNReal.ofReal Kv = (KG Λ : ENNReal)
      * ENNReal.ofReal (lossWeight (max AF AG) ρ 0 0 k₁ k₂)
      * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
    rw [show Kv = ((KG Λ : NNReal) : ℝ) * lossWeight (max AF AG) ρ 0 0 k₁ k₂ * G₂ from rfl,
      ENNReal.ofReal_mul (mul_nonneg (NNReal.coe_nonneg _) hlwA),
      ENNReal.ofReal_mul (NNReal.coe_nonneg _), hG₂, ENNReal.ofReal_coe_nnreal]
  have hKv_bound : ENNReal.ofReal Kv ≤ (Cin Λ : ENNReal)
      * ENNReal.ofReal (lossWeight (max AF AG) ρ 0 0 k₁ k₂)
      * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
    have hstep : (KG Λ : ENNReal) ≤ (Cin Λ : ENNReal) := by
      have h1 : ((KG Λ : NNReal) : ℝ) ≤ ((Cin Λ : NNReal) : ℝ) := by
        dsimp only [Cin]
        exact le_trans (le_max_right _ _) (le_max_left _ _)
      calc (KG Λ : ENNReal) = ENNReal.ofReal ((KG Λ : NNReal) : ℝ) :=
            (ENNReal.ofReal_coe_nnreal (p := KG Λ)).symm
        _ ≤ ENNReal.ofReal ((Cin Λ : NNReal) : ℝ) := ENNReal.ofReal_le_ofReal h1
        _ = (Cin Λ : ENNReal) := ENNReal.ofReal_coe_nnreal
    rw [hKv_eq]
    exact mul_le_mul'
      (mul_le_mul_left hstep (ENNReal.ofReal (lossWeight (max AF AG) ρ 0 0 k₁ k₂))) le_rfl
  have hKv_int : ∫⁻ X : ℝ, (VrLiftDataP (R : ℝ) (arithQ ρ (max 0 0))
        (fun n : ℕ => packetFamG ρ a 0 0 k₁ k₂ W₂ n X)) ^ (2 : ℕ)
      ≤ ENNReal.ofReal (Kv ^ 2) := by
    rw [ENNReal.ofReal_pow hKv_nn, hKv_eq, mul_pow, mul_pow]
    exact hGint
  -- ### the arithmetic bilinear clauses at the one-point modulus
  haveI : NeZero (arithQ ρ (max 0 0)) :=
    ⟨Nat.pos_iff_ne_zero.mp (arithQ_pos ρ (max 0 0))⟩
  haveI : Subsingleton (ZMod (arithQ ρ (max 0 0))) := by
    rw [max_self, arithQ_zero]
    infer_instance
  have hMr : (0 : ℝ) < r := lt_trans (by norm_num) hr
  have hMbase : ∀ (X : ℝ) (n : ℕ),
      eLpNorm (fun ρ' : ZMod (arithQ ρ (max 0 0)) =>
          zmodAvg (negReflect P) (arithQ ρ (max 0 0))
            (packetFamF ρ a 0 0 k₁ k₂ W₁ n X) (packetFamG ρ a 0 0 k₁ k₂ W₂ n X) ρ')
        (r : ENNReal) (zmodProb (arithQ ρ (max 0 0)))
      ≤ ENNReal.ofReal 1
        * eLpNorm (packetFamF ρ a 0 0 k₁ k₂ W₁ n X) 2 (zmodProb (arithQ ρ (max 0 0)))
        * eLpNorm (packetFamG ρ a 0 0 k₁ k₂ W₂ n X) 2 (zmodProb (arithQ ρ (max 0 0))) :=
    fun X n => cornerSubsingletonAvg (negReflect P) hMr _ _
  have hM1 : ∀ (X : ℝ) (m n l : ℕ),
      eLpNorm (fun ρ' : ZMod (arithQ ρ (max 0 0)) =>
          zmodAvg (negReflect P) (arithQ ρ (max 0 0))
            (packetFamF ρ a 0 0 k₁ k₂ W₁ m X - packetFamF ρ a 0 0 k₁ k₂ W₁ n X)
            (packetFamG ρ a 0 0 k₁ k₂ W₂ l X) ρ')
        (r : ENNReal) (zmodProb (arithQ ρ (max 0 0)))
      ≤ ENNReal.ofReal 1
        * eLpNorm (packetFamF ρ a 0 0 k₁ k₂ W₁ m X - packetFamF ρ a 0 0 k₁ k₂ W₁ n X) 2
            (zmodProb (arithQ ρ (max 0 0)))
        * eLpNorm (packetFamG ρ a 0 0 k₁ k₂ W₂ l X) 2 (zmodProb (arithQ ρ (max 0 0))) :=
    fun X m n l => cornerSubsingletonAvg (negReflect P) hMr _ _
  have hM2 : ∀ (X : ℝ) (m n l : ℕ),
      eLpNorm (fun ρ' : ZMod (arithQ ρ (max 0 0)) =>
          zmodAvg (negReflect P) (arithQ ρ (max 0 0))
            (packetFamF ρ a 0 0 k₁ k₂ W₁ l X)
            (packetFamG ρ a 0 0 k₁ k₂ W₂ m X - packetFamG ρ a 0 0 k₁ k₂ W₂ n X) ρ')
        (r : ENNReal) (zmodProb (arithQ ρ (max 0 0)))
      ≤ ENNReal.ofReal 1
        * eLpNorm (packetFamF ρ a 0 0 k₁ k₂ W₁ l X) 2 (zmodProb (arithQ ρ (max 0 0)))
        * eLpNorm (packetFamG ρ a 0 0 k₁ k₂ W₂ m X - packetFamG ρ a 0 0 k₁ k₂ W₂ n X) 2
            (zmodProb (arithQ ρ (max 0 0))) :=
    fun X m n l => cornerSubsingletonAvg (negReflect P) hMr _ _
  -- ### the constant clauses
  have hMbound : ENNReal.ofReal (1 : ℝ) ≤ (Cin Λ : ENNReal)
      * ENNReal.ofReal ((2 : ℝ) ^ (-(1 * max ((0 : ℕ) : ℝ) ((0 : ℕ) : ℝ)))) := by
    have h2 : (1 : ENNReal) ≤ (Cin Λ : ENNReal) := by
      have h1 : (1 : ℝ) ≤ ((Cin Λ : NNReal) : ℝ) := by
        have h3 : (2 : NNReal) ≤ Cin Λ := by
          dsimp only [Cin]
          exact le_max_right _ _
        calc (1 : ℝ) ≤ (2 : ℝ) := by norm_num
          _ = ((2 : NNReal) : ℝ) := by norm_num
          _ ≤ ((Cin Λ : NNReal) : ℝ) := by exact_mod_cast h3
      calc (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) := ENNReal.ofReal_one.symm
        _ ≤ ENNReal.ofReal ((Cin Λ : NNReal) : ℝ) := ENNReal.ofReal_le_ofReal h1
        _ = (Cin Λ : ENNReal) := ENNReal.ofReal_coe_nnreal
    have hpow : ENNReal.ofReal ((2 : ℝ) ^ (-(1 * max ((0 : ℕ) : ℝ) ((0 : ℕ) : ℝ)))) = 1 := by
      have hp : (2 : ℝ) ^ (-(1 * max ((0 : ℕ) : ℝ) ((0 : ℕ) : ℝ))) = 1 := by
        have h0 : max ((0 : ℕ) : ℝ) ((0 : ℕ) : ℝ) = 0 := by simp
        rw [h0, mul_zero, neg_zero, Real.rpow_zero]
      rw [hp, ENNReal.ofReal_one]
    rw [hpow, mul_one, ENNReal.ofReal_one]
    exact h2
  -- ### the assembly
  refine ⟨fun n X ρ' => zmodAvg (negReflect P) (arithQ ρ (max 0 0))
      (packetFamF ρ a 0 0 k₁ k₂ W₁ n X) (packetFamG ρ a 0 0 k₁ k₂ W₂ n X)
      ((ρ' : ℤ) : ZMod (arithQ ρ (max 0 0))),
    packetFamF ρ a 0 0 k₁ k₂ W₁, packetFamG ρ a 0 0 k₁ k₂ W₂, 1, Ku, Kv,
    hband, hdiag, ?_, ⟨by norm_num, hMbound⟩, ⟨hKu_nn, hKu_bound⟩, ⟨hKv_nn, hKv_bound⟩,
    hKu_int, hKv_int, humeas, hvmeas, hMbase, hM1, hM2⟩
  intro n X ρ'
  rfl

end

end Work.KMTPlan.A6Clean
