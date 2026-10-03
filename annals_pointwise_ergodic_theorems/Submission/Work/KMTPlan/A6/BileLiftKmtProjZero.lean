/-
# The Ionescu--Wainger projection kills the lifted minor-arc packet

Krause--Mirek--Tao, *Pointwise ergodic theorems for non-conventional bilinear polynomial
averages*, Annals 195 (2022).  This file proves

`Work.KMTPlan.A6.BileLiftKmtProjZero`:

if `u : ZMod Q → ℂ` satisfies the Ionescu--Wainger minor-arc condition at height `l`
(`MdlIwMinorArc ρ l Q u`), `ψ : 𝒮(ℝ)` has Fourier transform supported in `[-1,1]`, and the scales
satisfy `2^k · Q · Q_{≤l} < 1/4` and `4 · Q · Q_{≤l} < R`, then the IW projection `Π_{≤l,≤k}`
of the "lift" `n ↦ R^{-1/2} ψ(n/R) u(n mod Q)` vanishes.

The proof has three layers.

1. **Character expansion of `u`.**  `u x = ∑_i (Q⁻¹ · dft u i) · e(i x/Q)`, and `dft u i = 0`
   for the Ionescu--Wainger low frequencies `i ∈ iwLowFreqs ρ l Q`.  Since `kmtProj` is linear on
   bounded functions (`Work.KMTAreas.A5.piHat`), it suffices to treat a single character:
   `n ↦ A · ψ(n/R) · fourier n β`, `β = ZMod.toAddCircle i`, with `i` minor.

2. **The core vanishing `kmtProj_schwartz_char_zero`.**  The symbol of `Π_{≤l,≤k}` is supported
   in the `2^k`-neighbourhood of `(ℚ/ℤ)_{≤l}` (`supportedInArc_periodize_etaCut`), whereas the
   ℤ-Fourier transform of `n ↦ ψ(n/R)e(2πi n β)` is, by Poisson summation
   (`PoissonModulatedZero`), supported in the `1/R`-neighbourhood of `β + ℤ`.  The two supports
   are disjoint: because `i` is a minor frequency, `β` is at distance at least
   `1/(Q · Q_{≤l})` from `(ℚ/ℤ)_{≤l}` (`IwSeparation`, proved here as `iwSeparation_aux`), and
   `2^k + 1/R < 1/(Q · Q_{≤l})` by the two scale hypotheses.

3. **Assembly.**  `Π` is realised as the ℓ² multiplier `projCLM`, the vanishing of the pointwise
   product of its symbol with the Fourier transform of the lift gives `Π(lift) = 0`.

Auxiliary lemmas proved here: `zmod_dft_expansion`, `fourier_add_var`,
`norm_coe_addCircle_one_le`, `iwArithFreqs_neg`, `mem_iwLowFreqs_iff`,
`nsmul_toAddCircle_eq_zero_iff`, `iwSeparation_aux`, `kmtProj_schwartz_char_zero`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlIwLow
import Submission.Work.KMTAreas.A4.fourierZCoeFnEqTsum
import Submission.Work.KMTPlan.A6.multiplierOfPlancherel
import Submission.Work.KMTAreas.A5.Basic
import Submission.Work.KMTPlan.A6.projVanishingF
import Submission.Work.KMTPlan.A6.PoissonModulatedZero
import Submission.Work.KMTPlan.A6.SchwartzLiftSummable
import Submission.Work.KMTPlan.A6.StdAddCharFourier

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators FourierTransform
open Work.Analysis.IonescuWainger
open Work.KMTContract
open Work.KMTAreas.A5

namespace Work.KMTPlan.A6

noncomputable section

/-! ### small helpers -/

theorem zmod_dft_expansion {Q : ℕ} [NeZero Q] (u : ZMod Q → ℂ) (x : ZMod Q) :
    u x = ∑ i : ZMod Q, ((Q : ℂ)⁻¹ * ZMod.dft u i) * ZMod.stdAddChar (i * x) := by
  conv_lhs => rw [← LinearEquiv.symm_apply_apply ZMod.dft u]
  rw [ZMod.invDFT_apply]
  rw [smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by rw [smul_eq_mul]; ring)

theorem fourier_add_var {T : ℝ} (n : ℤ) (x y : AddCircle T) :
    fourier n (x + y) = fourier n x * fourier n y := by
  rw [fourier_apply, fourier_apply, fourier_apply, zsmul_add, AddCircle.toCircle_add,
    Circle.coe_mul]

theorem norm_coe_addCircle_one_le (x : ℝ) : ‖(x : AddCircle (1 : ℝ))‖ ≤ |x| := by
  by_cases h : (1 / 2 : ℝ) ≤ |x|
  · refine le_trans ?_ h
    simpa using AddCircle.norm_le_half_period (p := (1:ℝ)) one_ne_zero
  · have hx2 : |x| ≤ (1 : ℝ) / 2 := by
      have := not_le.mp h; linarith
    exact le_of_eq ((AddCircle.norm_coe_eq_abs_iff (p := (1:ℝ)) one_ne_zero).mpr (by simpa using hx2))

theorem iwArithFreqs_neg {ρ : ℝ} {l : ℕ} {α : AddCircle (1 : ℝ)}
    (h : α ∈ iwArithFreqs ρ l) : -α ∈ iwArithFreqs ρ l := by
  obtain ⟨q, hq, hqα⟩ := mem_iwArithFreqs.mp h
  exact mem_iwArithFreqs.mpr ⟨q, hq, by rw [smul_neg, hqα, neg_zero]⟩

theorem intCast_circle_eq_zero (m : ℤ) : ((m : ℝ) : AddCircle (1 : ℝ)) = 0 := by
  rw [AddCircle.coe_eq_zero_iff]
  exact ⟨m, by simp⟩

theorem mem_iwLowFreqs_iff {ρ : ℝ} {l Q : ℕ} [NeZero Q] (i : ZMod Q) :
    i ∈ iwLowFreqs ρ l Q ↔ ∃ q ∈ iwP ρ l, q • i = 0 := by
  rw [iwLowFreqs, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem nsmul_toAddCircle_eq_zero_iff {Q : ℕ} [NeZero Q] (q : ℕ) (i : ZMod Q) :
    q • i = 0 ↔ q • (ZMod.toAddCircle i : AddCircle (1 : ℝ)) = 0 := by
  constructor
  · intro h
    rw [← map_nsmul (ZMod.toAddCircle (N := Q)) q i, h, map_zero]
  · intro h
    rw [← map_nsmul (ZMod.toAddCircle (N := Q)) q i,
      ← map_zero (ZMod.toAddCircle (N := Q))] at h
    exact (ZMod.toAddCircle_inj (N := Q)).mp h

theorem iwSeparation_aux {ρ : ℝ} {Q : ℕ} [NeZero Q] {l : ℕ}
    {α : AddCircle (1 : ℝ)} (hα : α ∈ iwArithFreqs ρ l) {i : ZMod Q}
    (hi : i ∉ iwLowFreqs ρ l Q) :
    (1 : ℝ) / ((Q : ℝ) * (iwQl ρ l : ℝ)) ≤ ‖α + (ZMod.toAddCircle i : AddCircle (1 : ℝ))‖ := by
  have hq : 0 < Q * iwQl ρ l := Nat.mul_pos (NeZero.pos Q) (iwQl_pos (ρ := ρ) (l := l))
  have hαq : (Q * iwQl ρ l) • α = 0 := by
    calc (Q * iwQl ρ l) • α = Q • ((iwQl ρ l) • α) := by rw [mul_nsmul']
      _ = 0 := by rw [iwQl_nsmul_eq_zero hα, smul_zero]
  have hQ : (Q : ℕ) • (ZMod.toAddCircle i : AddCircle (1 : ℝ)) = 0 := by
    have h1 : (Q : ℕ) • i = 0 := by rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    exact (nsmul_toAddCircle_eq_zero_iff Q i).mp h1
  have hβq : (Q * iwQl ρ l) • (-(ZMod.toAddCircle i : AddCircle (1 : ℝ))) = 0 := by
    calc (Q * iwQl ρ l) • (-(ZMod.toAddCircle i : AddCircle (1 : ℝ)))
        = (iwQl ρ l * Q) • (-(ZMod.toAddCircle i : AddCircle (1 : ℝ))) := by rw [mul_comm]
      _ = (iwQl ρ l) • (Q • (-(ZMod.toAddCircle i : AddCircle (1 : ℝ)))) := by rw [mul_nsmul']
      _ = (iwQl ρ l) • (-(Q • (ZMod.toAddCircle i : AddCircle (1 : ℝ)))) := by rw [smul_neg]
      _ = 0 := by rw [hQ, neg_zero, smul_zero]
  have hne : α ≠ -(ZMod.toAddCircle i : AddCircle (1 : ℝ)) := by
    intro h
    apply hi
    have hβ : (ZMod.toAddCircle i : AddCircle (1 : ℝ)) ∈ iwArithFreqs ρ l := by
      have heq : (ZMod.toAddCircle i : AddCircle (1 : ℝ)) = -α := by rw [h, neg_neg]
      rw [heq]
      exact iwArithFreqs_neg hα
    obtain ⟨q, hqP, hqβ⟩ := mem_iwArithFreqs.mp hβ
    exact (mem_iwLowFreqs_iff i).mpr ⟨q, hqP, (nsmul_toAddCircle_eq_zero_iff q i).mpr hqβ⟩
  have hfin := one_div_le_norm_of_ne hq hαq hβq hne
  rw [sub_neg_eq_add] at hfin
  simpa [Nat.cast_mul] using hfin


/-! ### the core vanishing -/

theorem kmtProj_schwartz_char_zero (ψ : SchwartzMap ℝ ℂ) {ρ : ℝ} {l : ℕ} {k : ℤ} {R : ℝ}
    (hR : 0 < R) (hψ : ∀ ξ : ℝ, 1 < |ξ| → (𝓕 (ψ : ℝ → ℂ)) ξ = 0)
    (A : ℂ) (β : AddCircle (1 : ℝ))
    (hsep : ∀ α ∈ iwArithFreqs ρ l, (2 : ℝ) ^ k + 1 / R < ‖α + β‖) :
    kmtProj ρ l k (fun n : ℤ => A * (ψ : ℝ → ℂ) ((n : ℝ) / R) * fourier n β) = 0 := by
  classical
  set f : ℤ → ℂ := fun n => A * (ψ : ℝ → ℂ) ((n : ℝ) / R) * fourier n β with hf
  obtain ⟨hgs, hgm⟩ := SchwartzLiftSummable ψ hR β
  have hfs : Summable (fun n : ℤ => ‖f n‖) := by
    have h1 : (fun n : ℤ => ‖f n‖)
        = fun n : ℤ => ‖A‖ * ‖(ψ : ℝ → ℂ) ((n : ℝ) / R) * fourier n β‖ := by
      funext n
      rw [hf]
      simp only [norm_mul]
      ring
    rw [h1]
    exact hgs.mul_left ‖A‖
  have hfm : Memℓp f 2 := by
    have h1 : f = A • (fun n : ℤ => (ψ : ℝ → ℂ) ((n : ℝ) / R) * fourier n β) := by
      funext n
      rw [hf]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [h1]
    rw [memℓp_gen_iff (p := 2) (by norm_num)]
    rw [memℓp_gen_iff (p := 2) (by norm_num)] at hgm
    refine Summable.congr (hgm.mul_left (‖A‖ ^ ((2 : ℝ≥0∞).toReal))) (fun n => ?_)
    rw [Pi.smul_apply, norm_smul, Real.mul_rpow (norm_nonneg A) (norm_nonneg _)]
  have hSmem : MemLp
      (iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta k))) ⊤ circleMeasure :=
    memLp_iwSymbolSet_etaCut (iwArithFreqs ρ l) k
  have h1 : kmtProj ρ l k (fun n : ℤ => A * (ψ : ℝ → ℂ) ((n : ℝ) / R) * fourier n β)
      = ⇑(iwOpSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta k)) hSmem ⟨f, hfm⟩) :=
    iwConvEqIwOpSetMemlp hSmem ⟨f, hfm⟩
  have hpoint : ∀ ξ : Circle, iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta k)) ξ *
      (∑' x : ℤ, f x * fourier (-x) (-ξ)) = 0 := by
    intro ξ
    by_cases hξ : iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta k)) ξ = 0
    · rw [hξ, zero_mul]
    · obtain ⟨α, hα, hφα⟩ : ∃ α ∈ iwArithFreqs ρ l,
          periodize (etaCut kmtEta k) (ξ - α) ≠ 0 := by
        by_contra hc
        push Not at hc
        exact hξ (by rw [iwSymbolSet]; exact Finset.sum_eq_zero (fun α hα => hc α hα))
      obtain ⟨θ, hθarc, hθeq⟩ := supportedInArc_periodize_etaCut k (ξ - α) hφα
      have hdist : ‖ξ - α‖ ≤ (2 : ℝ) ^ k := by
        rw [← hθeq]
        exact le_trans (norm_coe_addCircle_one_le θ) (abs_le.mpr ⟨hθarc.1, hθarc.2⟩)
      have hnorm : 1 / R < ‖β + ξ‖ := by
        have htri : ‖α + β‖ ≤ ‖α - ξ‖ + ‖β + ξ‖ := by
          have h := norm_add_le (α - ξ) (β + ξ)
          rwa [show (α - ξ) + (β + ξ) = α + β by abel] at h
        have h3 : ‖α - ξ‖ = ‖ξ - α‖ := norm_sub_rev _ _
        have h2 : (2 : ℝ) ^ k + 1 / R < ‖α + β‖ := hsep α hα
        rw [h3] at htri
        linarith
      have hseries : (∑' x : ℤ, f x * fourier (-x) (-ξ)) =
          A * ∑' x : ℤ, (ψ : ℝ → ℂ) ((x : ℝ) / R) * fourier x (β + ξ) := by
        rw [← tsum_mul_left]
        refine tsum_congr (fun x => ?_)
        rw [hf]
        simp only [Work.KMTAreas.A4.fourier_neg_neg_apply, fourier_add_var]
        ring
      obtain ⟨t, ht⟩ : ∃ t : ℝ, (t : AddCircle (1 : ℝ)) = β + ξ :=
        ⟨(AddCircle.equivIco (1 : ℝ) 0 (β + ξ)).val, by simp⟩
      have ht2 : ∀ m : ℤ, 1 / R < |t + m| := by
        intro m
        have hkey : ‖((t + m : ℝ) : AddCircle (1 : ℝ))‖ = ‖β + ξ‖ := by
          rw [AddCircle.coe_add, ht, intCast_circle_eq_zero, add_zero]
        exact lt_of_lt_of_le hnorm (le_trans (le_of_eq hkey.symm) (norm_coe_addCircle_one_le _))
      have hP : (∑' x : ℤ, (ψ : ℝ → ℂ) ((x : ℝ) / R) * fourier x (β + ξ)) = 0 := by
        simpa [ht] using PoissonModulatedZero ψ hR hψ t ht2
      rw [hseries, hP, mul_zero, mul_zero]
  have hprod : hSmem.toLp (iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta k)))
      • fourierZ ⟨f, hfm⟩ = 0 := by
    have hAB : hSmem.toLp (iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta k)))
        • fourierZ ⟨f, hfm⟩ =ᵐ[circleMeasure] (fun _ : Circle => (0 : ℂ)) := by
      filter_upwards [Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2)
          (hSmem.toLp (iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta k))))
          (fourierZ ⟨f, hfm⟩),
        MemLp.coeFn_toLp hSmem,
        KMTAreas.A4.fourierZCoeFnEqTsum hfs hfm] with ξ h1 h2 h3
      simp only [h1, h2, h3, smul_eq_mul, Pi.mul_apply, hpoint ξ]
    exact Lp.ext (hAB.trans (Lp.coeFn_zero ℂ 2 circleMeasure).symm)
  have hzeroF : ⇑(iwOpSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta k)) hSmem
      ⟨f, hfm⟩) = 0 := by
    funext n
    rw [iwOpSet_apply_eq (iwArithFreqs ρ l) (periodize (etaCut kmtEta k)) hSmem ⟨f, hfm⟩ n,
      hprod]
    rw [fourierCoeff_congr_ae (Lp.coeFn_zero ℂ 2 circleMeasure)]
    simp [fourierCoeff]
  rw [h1, hzeroF]

/-! ### the main theorem -/

theorem BileLiftKmtProjZero (ψ : SchwartzMap ℝ ℂ) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {Q : ℕ} [NeZero Q] {l : ℕ} {k : ℤ} {R : ℕ} (hR : 0 < R)
    (hψ : ∀ ξ : ℝ, 1 < |ξ| → Work.Analysis.InverseTheory.realFourier (ψ : ℝ → ℂ) ξ = 0)
    (hk : (2 : ℝ) ^ k * ((Q : ℝ) * (Work.Analysis.IonescuWainger.iwQl ρ l : ℝ)) < 1 / 4)
    (hRl : 4 * ((Q : ℝ) * (Work.Analysis.IonescuWainger.iwQl ρ l : ℝ)) < (R : ℝ))
    (u : ZMod Q → ℂ) (hu : Work.KMTPlan.A6.MdlIwMinorArc ρ l Q u) :
    Work.KMTContract.kmtProj ρ l k (fun n : ℤ =>
        ((Real.sqrt (R : ℝ))⁻¹ : ℂ) * (ψ ((n : ℝ) / (R : ℝ)) : ℂ) * u (n : ZMod Q)) = 0 := by
  classical
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast NeZero.pos Q
  have hqi : (0 : ℝ) < (Q : ℝ) * (iwQl ρ l : ℝ) := by
    have h := iwQl_pos (ρ := ρ) (l := l)
    positivity
  have hψ' : ∀ ξ : ℝ, 1 < |ξ| → (𝓕 (ψ : ℝ → ℂ)) ξ = 0 := hψ
  have hR0 : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
  have hk' : (2 : ℝ) ^ k < 1 / (4 * ((Q : ℝ) * (iwQl ρ l : ℝ))) := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [hk]
  have hR' : 1 / (R : ℝ) < 1 / (4 * ((Q : ℝ) * (iwQl ρ l : ℝ))) := by
    rw [one_div_lt_one_div hR0 (by positivity)]
    linarith [hRl]
  have hsum : (2 : ℝ) ^ k + 1 / (R : ℝ) < 1 / ((Q : ℝ) * (iwQl ρ l : ℝ)) := by
    have h4 : 1 / (4 * ((Q : ℝ) * (iwQl ρ l : ℝ))) + 1 / (4 * ((Q : ℝ) * (iwQl ρ l : ℝ)))
        = 1 / (2 * ((Q : ℝ) * (iwQl ρ l : ℝ))) := by ring
    have h5 : 1 / (2 * ((Q : ℝ) * (iwQl ρ l : ℝ))) < 1 / ((Q : ℝ) * (iwQl ρ l : ℝ)) := by
      rw [one_div_lt_one_div (by positivity) hqi]
      linarith
    linarith [hk', hR', h4, h5]
  -- the character expansion of `u`
  have hdecomp : (fun n : ℤ => ((Real.sqrt (R : ℝ))⁻¹ : ℂ) *
        (ψ ((n : ℝ) / (R : ℝ)) : ℂ) * u (n : ZMod Q))
      = ∑ i : ZMod Q, (fun n : ℤ => ((Q : ℂ)⁻¹ * ZMod.dft u i) * ((Real.sqrt (R : ℝ))⁻¹ : ℂ) *
          (ψ ((n : ℝ) / (R : ℝ)) : ℂ) * fourier n (ZMod.toAddCircle i)) := by
    funext n
    rw [Finset.sum_apply, zmod_dft_expansion u (n : ZMod Q), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [StdAddCharFourier]
    ring
  -- boundedness
  have hbdd : ∀ i : ZMod Q, BoundedZ (fun n : ℤ => ((Q : ℂ)⁻¹ * ZMod.dft u i) *
      ((Real.sqrt (R : ℝ))⁻¹ : ℂ) * (ψ ((n : ℝ) / (R : ℝ)) : ℂ) *
      fourier n (ZMod.toAddCircle i)) := by
    intro i
    refine boundedZ_of_bound (C := ‖((Q : ℂ)⁻¹ * ZMod.dft u i) *
      ((Real.sqrt (R : ℝ))⁻¹ : ℂ)‖ * SchwartzMap.seminorm ℝ 0 0 ψ) (fun n => ?_)
    have h1 : ‖fourier n (ZMod.toAddCircle i)‖ = 1 := by
      rw [fourier_apply]; exact Circle.norm_coe _
    have h2 : ‖(ψ : ℝ → ℂ) ((n : ℝ) / (R : ℝ))‖ ≤ SchwartzMap.seminorm ℝ 0 0 ψ :=
      SchwartzMap.norm_le_seminorm ℝ ψ _
    rw [norm_mul, norm_mul, h1, mul_one]
    exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
  have hFbdd : BoundedZ (fun n : ℤ => ((Real.sqrt (R : ℝ))⁻¹ : ℂ) *
      (ψ ((n : ℝ) / (R : ℝ)) : ℂ) * u (n : ZMod Q)) := by
    refine boundedZ_of_bound (C := ‖((Real.sqrt (R : ℝ))⁻¹ : ℂ)‖ *
      SchwartzMap.seminorm ℝ 0 0 ψ * ∑ i : ZMod Q, ‖u i‖) (fun n => ?_)
    have h2 : ‖(ψ : ℝ → ℂ) ((n : ℝ) / (R : ℝ))‖ ≤ SchwartzMap.seminorm ℝ 0 0 ψ :=
      SchwartzMap.norm_le_seminorm ℝ ψ _
    have h3 : ‖u (n : ZMod Q)‖ ≤ ∑ i : ZMod Q, ‖u i‖ :=
      Finset.single_le_sum (fun i _ => norm_nonneg _) (Finset.mem_univ _)
    rw [norm_mul, norm_mul]
    have hS : 0 ≤ SchwartzMap.seminorm ℝ 0 0 ψ := le_trans (norm_nonneg _) h2
    calc ‖((Real.sqrt (R : ℝ))⁻¹ : ℂ)‖ * ‖(ψ : ℝ → ℂ) ((n : ℝ) / (R : ℝ))‖ * ‖u (n : ZMod Q)‖
        ≤ ‖((Real.sqrt (R : ℝ))⁻¹ : ℂ)‖ * SchwartzMap.seminorm ℝ 0 0 ψ * ‖u (n : ZMod Q)‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (norm_nonneg _)) (norm_nonneg _)
      _ ≤ ‖((Real.sqrt (R : ℝ))⁻¹ : ℂ)‖ * SchwartzMap.seminorm ℝ 0 0 ψ * ∑ i : ZMod Q, ‖u i‖ :=
          mul_le_mul_of_nonneg_left h3 (mul_nonneg (norm_nonneg _) hS)
  have hlin : kmtProj ρ l k (fun n : ℤ => ((Real.sqrt (R : ℝ))⁻¹ : ℂ) *
        (ψ ((n : ℝ) / (R : ℝ)) : ℂ) * u (n : ZMod Q))
      = ∑ i : ZMod Q, kmtProj ρ l k (fun n : ℤ => ((Q : ℂ)⁻¹ * ZMod.dft u i) *
          ((Real.sqrt (R : ℝ))⁻¹ : ℂ) * (ψ ((n : ℝ) / (R : ℝ)) : ℂ) *
          fourier n (ZMod.toAddCircle i)) := by
    rw [← piHat_of_bounded ρ l k hFbdd, hdecomp, map_sum]
    exact Finset.sum_congr rfl (fun i _ => piHat_of_bounded ρ l k (hbdd i))
  rw [hlin]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  by_cases hi : i ∈ iwLowFreqs ρ l Q
  · have hdft : ZMod.dft u i = 0 := hu i hi
    have hzero : (fun n : ℤ => ((Q : ℂ)⁻¹ * ZMod.dft u i) * ((Real.sqrt (R : ℝ))⁻¹ : ℂ) *
        (ψ ((n : ℝ) / (R : ℝ)) : ℂ) * fourier n (ZMod.toAddCircle i)) = 0 := by
      funext n
      rw [hdft]
      simp
    rw [hzero, kmtProj_zero]
  · refine kmtProj_schwartz_char_zero ψ hR0 hψ' _ _ (fun α hα => ?_)
    have h1 : (1 : ℝ) / ((Q : ℝ) * (iwQl ρ l : ℝ)) ≤
        ‖α + (ZMod.toAddCircle i : AddCircle (1 : ℝ))‖ :=
      iwSeparation_aux hα hi
    linarith [hsum]

end

end Work.KMTPlan.A6
