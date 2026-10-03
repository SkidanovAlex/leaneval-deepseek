import Mathlib
import Submission.Work.KMTAreas.A7.fiberVarSamplingLargeLossAuxBdd
import Submission.Work.KMTAreas.A7.sublatticeCosetCompareBdd
import Submission.Work.KMTAreas.A7.fourier_cwR_band
import Submission.Work.KMTAreas.A7.lacunaryBump_mult_bound_k1pos
import Submission.Port.Aesm

namespace Work.KMTAreas.A7

open MeasureTheory Finset
open Work.Analysis.IonescuWainger
open scoped ENNReal NNReal BigOperators FourierTransform

noncomputable section

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-! ## Helper lemmas for the bounded large-loss fibre estimate -/

/-- Monotonicity of `NonAliasing` in the frequency set. -/
lemma nonAliasing_subset {k : ℤ} {A A' : Finset Circ} (h : NonAliasing k A) (hsub : A' ⊆ A) :
    NonAliasing k A' :=
  fun α hα β hβ θ hθ θ' hθ' hh => h α (hsub hα) β (hsub hβ) θ hθ θ' hθ' hh

/-- Splitting a sum over `ℤ` into the residue classes mod `q` (for `ℝ≥0∞`-valued families). -/
lemma tsum_int_split_ennreal (q : ℕ) (hq : 1 ≤ q) (f : ℤ → ENNReal) :
    ∑' j : ℤ, f j = ∑ y ∈ Finset.range q, ∑' k : ℤ, f ((y : ℤ) + (k : ℤ) * (q : ℤ)) := by
  haveI : NeZero q := ⟨by omega⟩
  let E : Fin q × ℤ ≃ ℤ := (Equiv.prodComm (Fin q) ℤ).trans (Int.divModEquiv q).symm
  have hE : ∀ (y : Fin q) (k : ℤ), E (y, k) = (y : ℤ) + (k : ℤ) * (q : ℤ) := by
    intro y k
    simp only [E, Equiv.trans_apply, Equiv.prodComm_apply, Int.divModEquiv_symm_apply,
      Prod.swap_prod_mk]
    ring
  rw [← Equiv.tsum_eq E f]
  rw [show (∑' c : Fin q × ℤ, f (E c)) = ∑' (y : Fin q) (k : ℤ), f (E (y, k)) from
    ENNReal.tsum_prod (f := fun y k => f (E (y, k)))]
  rw [tsum_fintype]
  rw [Finset.sum_range]
  simp only [hE]

/-- The shifted version of the residue-class splitting. -/
lemma tsum_int_split_shift_ennreal (q : ℕ) (hq : 1 ≤ q) (f : ℤ → ENNReal) (b : ℤ) :
    ∑' j : ℤ, f j = ∑ y ∈ Finset.range q, ∑' k : ℤ, f ((y : ℤ) + (k : ℤ) * (q : ℤ) + b) := by
  have h1 : (∑' j : ℤ, f (j + b)) = ∑' j : ℤ, f j := Equiv.tsum_eq (Equiv.addRight b) f
  rw [← h1]
  haveI : NeZero q := ⟨by omega⟩
  let E : Fin q × ℤ ≃ ℤ := (Equiv.prodComm (Fin q) ℤ).trans (Int.divModEquiv q).symm
  have hE : ∀ (y : Fin q) (k : ℤ), E (y, k) = (y : ℤ) + (k : ℤ) * (q : ℤ) := by
    intro y k
    simp only [E, Equiv.trans_apply, Equiv.prodComm_apply, Int.divModEquiv_symm_apply,
      Prod.swap_prod_mk]
    ring
  rw [← Equiv.tsum_eq E (fun j => f (j + b))]
  rw [show (∑' c : Fin q × ℤ, f (E c + b)) = ∑' (y : Fin q) (k : ℤ), f (E (y, k) + b) from
    ENNReal.tsum_prod (f := fun y k => f (E (y, k) + b))]
  rw [tsum_fintype]
  rw [Finset.sum_range]
  simp only [hE]

/-- The `p`-th power of the `ℓ^p` norm of an `ℝ≥0∞`-valued family is the sum of the `p`-th powers. -/
lemma eLpNorm_pow_eq_tsum_int (G : ℤ → ENNReal) (p : ENNReal) (hp : p ≠ 0) (hptop : p < ⊤) :
    (MeasureTheory.eLpNorm G p MeasureTheory.Measure.count) ^ p.toReal
      = ∑' y : ℤ, G y ^ p.toReal := by
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp hptop.ne
  have h1 := MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm)
    (μ := MeasureTheory.Measure.count) (f := G) (p := p) hp hptop.ne
  rw [h1, ← ENNReal.rpow_mul]
  simp only [enorm_eq_self]
  rw [show (1 / p.toReal) * p.toReal = 1 from by
    rw [one_div, inv_mul_cancel₀ hpr.ne']]
  rw [ENNReal.rpow_one, MeasureTheory.lintegral_count]

/-- `1 ≤ uScale ρ L`. -/
lemma one_le_uScale_bdd {ρ : ℝ} (hρ : 0 ≤ ρ) (L : ℕ) : 1 ≤ uScale ρ L := by
  rw [uScale, Work.Analysis.EndVar.scaleCount]
  simp only [Nat.cast_one, one_mul]
  rw [Nat.one_le_iff_ne_zero]
  exact ((Int.lt_toNat (m := 0)).mpr
    (Int.floor_pos.mpr (Real.one_le_rpow (by norm_num) (by positivity)))).ne'

/-- The carrier-free slice as a `tsum` against the coefficients `cw φ`, with an optional cut. -/
lemma sliceSumm_eq_tsum_cw_sliceInput (A : Finset Circ) (φ : ℝ → ℂ)
    (hφsum : Summable (fun j : ℤ => ‖cw φ j‖)) (f : ℤ → ℂ) (B : ℝ)
    (hB : ∀ x : ℤ, ‖f x‖ ≤ B) (y z : ℤ) (S : Prop) [Decidable S] :
    (∑' j : ℤ, cw φ j * (if S then sliceInput A f y (z - j) else 0))
      = if S then sliceSumm A φ f y z else 0 := by
  by_cases hS : S
  · simp only [hS, if_true]
    exact (sliceSumm_eq_conv A φ hφsum f B hB y z).symm
  · simp only [hS, if_false, mul_zero, tsum_zero]


/-- The fibre at residue `0` of a profile `φ` is the exact-height projection `Tex`. -/
lemma fiberOp_zero_eq_Tex (ρ : ℝ) (l : ℕ) (φ : ℝ → ℂ) (hφ : MeasureTheory.Integrable φ)
    (f : ℤ → ℂ) : fiberOp ρ l φ 0 f = Tex ρ l φ f :=
  fiberOp_zero_eq_iwConv ρ l φ hφ f

/-
**The bounded-input case of `FiberVarSamplingLargeLoss`** (the paper's setting: `f ∈ ℓ^p` implies
`f` bounded).  Same conclusion as the target, but with the extra hypothesis `∀ x, ‖f x‖ ≤ B` and
with the constant `C` in place of `C * lossWeight …` (which is stronger).

PROOF SPEC (use the pieces below; all the algebra and the support bounds are already done):

* `Submission.Work.KMTAreas.A7.fiberVarSamplingLargeLossAux` provides, in `Work.KMTAreas.A7`:
  `innerPiece`, `sliceInput`, `sliceSumm`, `summable_innerPiece`, `fiberOp_eq_innerPiece`,
  `fiberOp_residue_eq_slice` (`fiberOp ρ l φ n₀ f (q*u+r) = sliceSumm A φ f (n₀-r) (q*u+r)` for
  `q • α = 0`, `α ∈ A := iwArithFreqsNew ρ l`), `sliceSumm_eq_conv`
  (`sliceSumm A φ f y = ∑'_j cw φ j * sliceInput A f y (· - j)`), `two_pow_logN_gt`,
  `varphiNt_support_mul_le`, `varphiNt_support_le_quarter`
  (`φ_{N,t} ≠ 0 → |ξ| ≤ 1/(4q)` from the Farey hypothesis), `fiberOp_mStarF_Sclip`
  (`fiberOp ρ l (mStarF U) n₀ (if S then Tex ρ l φ f else 0) = if S then fiberOp ρ l φ n₀ f else 0`),
  and `Work.KMTAreas.A7.cw_varphiNt_summable` (`Summable (cw (varphiNt N k t))`).
* `Submission.Work.KMTAreas.A7.convSublatticeCosetCompare` (sibling, in flight) provides
  `∃ C, 0 < C ∧ ∀ β q, 0 < β → β*q ≤ 1/4 → ∀ κ kext, (band-β extensions of the κ n) →
  (∀ n, Summable (κ n)) → ∀ h B, (∀ n y z, ‖h n y z‖ ≤ B) → ∀ y c c',
  ∑'_u (V^r_n (∑'_j κ n j * h n y (q*u+c-j)))^p ≤ ofReal C * ∑'_u (V^r_n (…))^p`
  (the constant does not depend on `β, q, κ, h, y, c, c'`).

STRATEGY:
1. put `q := arithQ ρ (max l₁ l₂)` (`q ≥ 1`), `A := iwArithFreqsNew ρ l₁`,
   `U := uScale ρ (max (max l₁ l₂) (max k₁ k₂))`, `φ n := varphiNt (N n) k₁ t`,
   `w n := if S n then Tex ρ l₁ (φ n) f else 0`;
2. rewrite the left-hand family with `fiberOp_mStarF_Sclip` (its `hφsupp` for `U` comes from
   `varphiNt_support_le` + the *strict* hypothesis `k₁ + 2U + 1 ≤ logN (N n)`, its `hφsum` from
   `cw_varphiNt_summable`, its `hφ` from `lacBump_integrable_varphiNt`; `hU : 1 ≤ U` from the
   definition of `uScale`);
3. `eLpNormResidueLpEq` (`Work.KMTAreas.A7Hi.eLpNormResidueLpEq`) turns the left-hand side into
   `(q⁻¹ ∑_{n₀<q} (‖F · n₀‖_p)^{p})^{1/p}` with `F y n₀ := V^r_n (fiberOp … n₀ (w n) y)`;
   for the `count` measure, `(‖G‖_p)^p = ∑'_y (G y)^p`
   (`eLpNorm_eq_lintegral_rpow_enorm_toReal` + `lintegral_count`);
4. split `∑'_y` into residues `y = q*u + r`, `0 ≤ r < q`; by step 2
   `F (q*u+r) n₀ = V^r_n (sliceSumm A (φ n) f (n₀-r) (q*u+r))`;
5. apply `convSublatticeCosetCompare` with `β := 1/(4q)`, `kappa n j := cw (φ n) j`,
   `kext n := fun s => ∫ θ, φ n θ * ee (-(s*θ))`, `h n y z := if S n then sliceInput A f y z else 0`
   (bounded by `B * #A`), `y := n₀-r`, `c := r`, `c' := r-n₀`; the band hypothesis for `kext n`
   comes from `Submission.Work.KMTAreas.A7.fourier_cwR_band` and `varphiNt_support_le_quarter`,
   the identification of the left side with `sliceSumm` is `sliceSumm_eq_conv`, and of the right
   side with `w n (q*u + r - n₀)` is `fiberOp_residue_eq_slice` with `n₀ := 0` and residue class
   `r - n₀`;
6. summing over `n₀ < q` and `r < q` reindexes to `q * ∑'_x (V^r_n (w n x))^p`, cancelling the
   `q⁻¹` of `residueLp`; conclude with the same `eLpNorm` lemmas as in step 3.
The final constant may be `C^{1/p.toReal}` (or any `C' > 0` independent of the scales).  Note
`p.toReal > 0` and `ENNReal.ofReal p.toReal = p`.
-/
theorem fiberVarSamplingLargeLoss_bdd :
    ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∀ (p : ENNReal), 1 < p → p < ⊤ → ∀ (r : NNReal), 2 < r →
      ∃ C : ℝ, 0 < C ∧
        ∀ (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (f : ℤ → ℂ) (B : ℝ), (∀ x : ℤ, ‖f x‖ ≤ B) →
          ∀ (N : ℕ → ℕ) (S : ℕ → Prop) [DecidablePred S],
          t ∈ Set.Icc (1 / 2 : ℝ) 1 →
          (∀ n : ℕ, (2 : ℝ) ^ k₁ * (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) : ℝ) * 8 ≤ (N n : ℝ)) →
          (∀ n : ℕ, k₁ + 2 * Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)) + 1
              ≤ (Work.Analysis.EndVar.logN (N n)).toNat) →
          Work.Analysis.IonescuWainger.NonAliasing
            (-(2 * (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)) : ℤ)))
            (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁) →
          MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7.residueLp p.toReal
              (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
              (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
                Work.KMTAreas.A7.fiberOp ρ l₁
                  (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)))) n₀
                  (if S n then Work.KMTAreas.A7.Tex ρ l₁
                    (Work.KMTAreas.A7.varphiNt (N n) k₁ t) f else 0) y)) x)
            p MeasureTheory.Measure.count
          ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm (fun x : ℤ =>
              PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
                (if S n then Work.KMTAreas.A7.Tex ρ l₁
                  (Work.KMTAreas.A7.varphiNt (N n) k₁ t) f else 0) x))
            p MeasureTheory.Measure.count := by
  intro ρ hρ hρ1 p hp hptop r hr2
  have hpne : p ≠ 0 := (lt_trans zero_lt_one hp).ne'
  have hptop' : p ≠ ⊤ := hptop.ne
  have hppos : 0 < p.toReal := ENNReal.toReal_pos hpne hptop'
  have hpo : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal hptop'
  have hpr : (1 : ℝ) < p.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hptop').mpr hp
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num : (1 : NNReal) ≤ 2) (le_of_lt hr2)
  obtain ⟨Ccomp, hCcomp, hcomp⟩ := convSublatticeCosetCompareBdd p.toReal hpr r hr1
  refine ⟨Ccomp ^ (1 / p.toReal), Real.rpow_pos_of_pos hCcomp _, ?_⟩
  intro l₁ l₂ k₁ k₂ t f B hB N S hdec ht hfarey hstrict hna
  set U : ℕ := uScale ρ (max (max l₁ l₂) (max k₁ k₂)) with hU
  set q : ℕ := arithQ ρ (max l₁ l₂) with hq
  set κ : ℕ → ℤ → ℂ := fun n j => cw (varphiNt (N n) k₁ t) j with hκ
  set Hf : ℕ → ℤ → ℤ → ℂ :=
    fun n y z => if S n then sliceInput (iwArithFreqsNew ρ l₁) f y z else 0 with hHf
  set F : ℤ → ℕ → ENNReal := fun y n₀ => PointwiseErgodicTheorems.variationalNorm r
    (fun n : ℕ => fiberOp ρ l₁ (mStarF U) n₀
      (if S n then Tex ρ l₁ (varphiNt (N n) k₁ t) f else 0) y) with hF
  set W : ℤ → ENNReal := fun x => PointwiseErgodicTheorems.variationalNorm r
    (fun n : ℕ => (if S n then Tex ρ l₁ (varphiNt (N n) k₁ t) f else 0) x) with hW
  have hφint : ∀ n : ℕ, Integrable (varphiNt (N n) k₁ t) :=
    fun n => lacBump_integrable_varphiNt (N n) k₁ t
  have hφsum : ∀ n : ℕ, Summable (fun j : ℤ => ‖cw (varphiNt (N n) k₁ t) j‖) :=
    fun n => cw_varphiNt_summable (N n) k₁ t
  have hφsupp : ∀ n : ℕ, ∀ ξ : ℝ, varphiNt (N n) k₁ t ξ ≠ 0 →
      |ξ| ≤ (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1) :=
    fun n => varphiNt_support_strict (N n) k₁ t U (hstrict n)
  have hU1 : 1 ≤ U := one_le_uScale_bdd hρ.le _
  have hnaNew : NonAliasing (-(2 * (U : ℤ))) (iwArithFreqsNew ρ l₁) :=
    nonAliasing_subset hna (fun α hα => mem_iwArithFreqsNew_le hα)
  have hqpos : 0 < q := by
    rw [hq]
    exact arithQ_pos ρ (max l₁ l₂)
  have hq1 : 1 ≤ q := hqpos
  have hq0 : (q : ENNReal) ≠ 0 := by positivity
  have hqt : (q : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top q
  have hfareyU : ∀ n : ℕ, 8 * (2 : ℝ) ^ k₁ * (q : ℝ) ≤ (N n : ℝ) := by
    intro n
    have h := hfarey n
    have he : 8 * (2 : ℝ) ^ k₁ * (q : ℝ) = (2 : ℝ) ^ k₁ * (q : ℝ) * 8 := by ring
    rw [he]
    exact h
  have hqnsmul : ∀ α ∈ iwArithFreqsNew ρ l₁, q • α = 0 := by
    intro α hα
    rw [hq]
    exact arithQ_nsmul_eq_zero
      (iwArithFreqs_mono hρ hρ1 (le_max_left l₁ l₂) (mem_iwArithFreqsNew_le hα))
  have hβ : 0 < 1 / (4 * (q : ℝ)) := by positivity
  have hβq : (1 / (4 * (q : ℝ))) * (q : ℝ) ≤ 1 / 4 := by
    have h : (1 / (4 * (q : ℝ))) * (q : ℝ) = 1 / 4 := by
      have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
      field_simp
    rw [h]
  have hκsum : ∀ n : ℕ, Summable (fun j : ℤ => ‖κ n j‖) := by
    intro n
    simp only [hκ]
    exact hφsum n
  have hB0 : 0 ≤ B := le_trans (norm_nonneg (f 0)) (hB 0)
  have hHfb : ∀ n : ℕ, ∀ y z : ℤ, ‖Hf n y z‖ ≤ B * ((iwArithFreqsNew ρ l₁).card : ℝ) := by
    intro n y z
    simp only [hHf]
    by_cases hSn : S n
    · simp only [hSn, if_true]
      simp only [sliceInput]
      calc ‖f z * (∑ α ∈ iwArithFreqsNew ρ l₁, fourier (T := 1) (y + z) α)‖
          = ‖f z‖ * ‖∑ α ∈ iwArithFreqsNew ρ l₁, fourier (T := 1) (y + z) α‖ :=
            norm_mul _ _
        _ ≤ B * ((iwArithFreqsNew ρ l₁).card : ℝ) := by
            refine mul_le_mul (hB z) ?_ (norm_nonneg _) hB0
            calc ‖∑ α ∈ iwArithFreqsNew ρ l₁, fourier (T := 1) (y + z) α‖
                ≤ ∑ α ∈ iwArithFreqsNew ρ l₁, ‖fourier (T := 1) (y + z) α‖ :=
                  norm_sum_le _ _
              _ = ∑ α ∈ iwArithFreqsNew ρ l₁, (1 : ℝ) := by
                  refine Finset.sum_congr rfl (fun α _ => ?_)
                  rw [fourier_apply]
                  exact Circle.norm_coe _
              _ = ((iwArithFreqsNew ρ l₁).card : ℝ) := by simp
    · simp only [hSn, if_false, norm_zero]
      exact mul_nonneg hB0 (Nat.cast_nonneg _)
  set kext : ℕ → ℝ → ℂ := fun n s => ∫ θ, varphiNt (N n) k₁ t θ * ee (-(s * θ)) with hkext
  have hkextdata : ∀ n : ℕ,
      Integrable (kext n) ∧ Continuous (kext n) ∧
        (∀ m : ℤ, kext n (m : ℝ) = κ n m) ∧
        (∀ ξ : ℝ, ξ ∉ Set.Icc (-(1 / (4 * (q : ℝ)))) (1 / (4 * (q : ℝ))) →
          FourierTransform.fourier (kext n) ξ = 0) := by
    intro n
    have hfun : kext n = fun s : ℝ =>
        ∫ θ, (varphiNtSch (N n) k₁ t : ℝ → ℂ) θ * ee (-(s * θ)) := by
      funext s
      simp only [hkext, varphiNtSch_coe]
    have hfun2 : kext n = ⇑(𝓕 (varphiNtSch (N n) k₁ t) : SchwartzMap ℝ ℂ) := by
      rw [hfun]
      funext s
      exact cwR_eq_fourier _ s
    have hsupp : ∀ ξ : ℝ, (varphiNtSch (N n) k₁ t : ℝ → ℂ) ξ ≠ 0 →
        |ξ| ≤ 1 / (4 * (q : ℝ)) := by
      intro ξ hξ
      exact varphiNt_support_le_quarter q hq1 k₁ (N n) t (hfareyU n) ξ (by simpa using hξ)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hfun2]
      exact (𝓕 (varphiNtSch (N n) k₁ t)).integrable
    · rw [hfun2]
      exact (𝓕 (varphiNtSch (N n) k₁ t)).continuous
    · intro m
      rw [hfun2]
      simp only [hκ]
      rw [cw_varphiNt_eq_fourierSch]
    · intro ξ hξ
      rw [hfun]
      exact fourier_cwR_band (1 / (4 * (q : ℝ))) hβ (varphiNtSch (N n) k₁ t) hsupp ξ hξ
  have hpair : ∀ (n₀ r₀ : ℕ),
      (∑' u : ℤ, (F ((r₀ : ℤ) + (u : ℤ) * (q : ℤ)) n₀) ^ p.toReal)
        ≤ ENNReal.ofReal Ccomp *
          (∑' u : ℤ, (W ((q : ℤ) * u + ((r₀ : ℤ) - (n₀ : ℤ)))) ^ p.toReal) := by
    intro n₀ r₀
    have hL : ∀ u : ℤ, F ((r₀ : ℤ) + (u : ℤ) * (q : ℤ)) n₀
        = PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => ∑' j : ℤ, κ n j *
            Hf n ((n₀ : ℤ) - (r₀ : ℤ)) ((q : ℤ) * u + (r₀ : ℤ) - j)) := by
      intro u
      have hfun : (fun n : ℕ => fiberOp ρ l₁ (mStarF U) n₀
            (if S n then Tex ρ l₁ (varphiNt (N n) k₁ t) f else 0)
            ((r₀ : ℤ) + (u : ℤ) * (q : ℤ)))
          = fun n : ℕ => ∑' j : ℤ, κ n j * Hf n ((n₀ : ℤ) - (r₀ : ℤ))
              ((q : ℤ) * u + (r₀ : ℤ) - j) := by
        funext n
        simp only [hκ, hHf]
        rw [fiberOp_mStarF_Sclip ρ hρ hρ1 l₁ U hU1 hnaNew (varphiNt (N n) k₁ t)
          (hφint n) (hφsum n) (hφsupp n) f B hB (S n) n₀]
        simp only [ite_apply, Pi.zero_apply]
        have hpt : (r₀ : ℤ) + (u : ℤ) * (q : ℤ) = (q : ℤ) * (u : ℤ) + (r₀ : ℤ) := by ring
        rw [hpt]
        rw [fiberOp_residue_eq_slice ρ l₁ (varphiNt (N n) k₁ t) q (hφsum n) f B hB hqnsmul
          n₀ (r₀ : ℤ) (u : ℤ)]
        exact (sliceSumm_eq_tsum_cw_sliceInput (iwArithFreqsNew ρ l₁) (varphiNt (N n) k₁ t)
          (hφsum n) f B hB ((n₀ : ℤ) - (r₀ : ℤ)) ((q : ℤ) * (u : ℤ) + (r₀ : ℤ)) (S n)).symm
      simp only [hF]
      rw [hfun]
    have hR : ∀ u : ℤ, PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => ∑' j : ℤ,
            κ n j * Hf n ((n₀ : ℤ) - (r₀ : ℤ)) ((q : ℤ) * u + ((r₀ : ℤ) - (n₀ : ℤ)) - j))
        = W ((q : ℤ) * u + ((r₀ : ℤ) - (n₀ : ℤ))) := by
      intro u
      have hfun : (fun n : ℕ => ∑' j : ℤ, κ n j * Hf n ((n₀ : ℤ) - (r₀ : ℤ))
              ((q : ℤ) * u + ((r₀ : ℤ) - (n₀ : ℤ)) - j))
          = fun n : ℕ => (if S n then Tex ρ l₁ (varphiNt (N n) k₁ t) f else 0)
              ((q : ℤ) * u + ((r₀ : ℤ) - (n₀ : ℤ))) := by
        funext n
        simp only [hκ, hHf]
        rw [sliceSumm_eq_tsum_cw_sliceInput (iwArithFreqsNew ρ l₁) (varphiNt (N n) k₁ t)
          (hφsum n) f B hB ((n₀ : ℤ) - (r₀ : ℤ)) ((q : ℤ) * u + ((r₀ : ℤ) - (n₀ : ℤ))) (S n)]
        simp only [ite_apply, Pi.zero_apply]
        by_cases hSn : S n
        · simp only [hSn, if_true]
          rw [← fiberOp_zero_eq_Tex ρ l₁ (varphiNt (N n) k₁ t) (hφint n) f]
          have hy : ((n₀ : ℤ) - (r₀ : ℤ)) = 0 - ((r₀ : ℤ) - (n₀ : ℤ)) := by ring
          rw [hy]
          rw [← fiberOp_residue_eq_slice ρ l₁ (varphiNt (N n) k₁ t) q (hφsum n) f B hB hqnsmul
            0 ((r₀ : ℤ) - (n₀ : ℤ)) (u : ℤ)]
        · simp only [hSn, if_false]
      simp only [hW]
      rw [hfun]
    calc (∑' u : ℤ, (F ((r₀ : ℤ) + (u : ℤ) * (q : ℤ)) n₀) ^ p.toReal)
        = ∑' u : ℤ, (PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => ∑' j : ℤ, κ n j *
            Hf n ((n₀ : ℤ) - (r₀ : ℤ)) ((q : ℤ) * u + (r₀ : ℤ) - j))) ^ p.toReal :=
          tsum_congr (fun u => by rw [hL u])
      _ ≤ ENNReal.ofReal Ccomp * ∑' u : ℤ, (PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => ∑' j : ℤ, κ n j *
              Hf n ((n₀ : ℤ) - (r₀ : ℤ)) ((q : ℤ) * u + ((r₀ : ℤ) - (n₀ : ℤ)) - j))) ^ p.toReal :=
          hcomp (1 / (4 * (q : ℝ))) hβ q hqpos hβq κ kext hkextdata hκsum Hf
            (B * ((iwArithFreqsNew ρ l₁).card : ℝ)) hHfb ((n₀ : ℤ) - (r₀ : ℤ)) (r₀ : ℤ)
            ((r₀ : ℤ) - (n₀ : ℤ))
      _ = ENNReal.ofReal Ccomp *
            (∑' u : ℤ, (W ((q : ℤ) * u + ((r₀ : ℤ) - (n₀ : ℤ)))) ^ p.toReal) := by
          rw [tsum_congr (fun u => by rw [hR u])]
  have hreindex : ∀ n₀ : ℕ,
      (∑ r ∈ Finset.range q, ∑' u : ℤ, (W ((q : ℤ) * u + ((r : ℤ) - (n₀ : ℤ)))) ^ p.toReal)
        = ∑' x : ℤ, (W x) ^ p.toReal := by
    intro n₀
    rw [tsum_int_split_shift_ennreal q hq1 (fun x : ℤ => (W x) ^ p.toReal) (-(n₀ : ℤ))]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    refine tsum_congr (fun u => ?_)
    rw [show (q : ℤ) * u + ((r : ℤ) - (n₀ : ℤ)) = (r : ℤ) + (u : ℤ) * (q : ℤ) + (-(n₀ : ℤ))
      by ring]
  have hsplit : ∀ n₀ : ℕ,
      (MeasureTheory.eLpNorm (fun y : ℤ => F y n₀) p MeasureTheory.Measure.count) ^ p.toReal
        = ∑ r ∈ Finset.range q, ∑' u : ℤ, (F ((r : ℤ) + (u : ℤ) * (q : ℤ)) n₀) ^ p.toReal := by
    intro n₀
    rw [eLpNorm_pow_eq_tsum_int (fun y : ℤ => F y n₀) p hpne hptop]
    rw [tsum_int_split_ennreal q hq1 (fun y : ℤ => (F y n₀) ^ p.toReal)]
  have hSum : (∑ n₀ ∈ Finset.range q, (MeasureTheory.eLpNorm (fun y : ℤ => F y n₀)
        p MeasureTheory.Measure.count) ^ p.toReal)
      ≤ (q : ENNReal) * (ENNReal.ofReal Ccomp * (∑' x : ℤ, (W x) ^ p.toReal)) := by
    calc ∑ n₀ ∈ Finset.range q, (MeasureTheory.eLpNorm (fun y : ℤ => F y n₀)
            p MeasureTheory.Measure.count) ^ p.toReal
        = ∑ n₀ ∈ Finset.range q, ∑ r ∈ Finset.range q,
            ∑' u : ℤ, (F ((r : ℤ) + (u : ℤ) * (q : ℤ)) n₀) ^ p.toReal :=
          Finset.sum_congr rfl (fun n₀ _ => hsplit n₀)
      _ ≤ ∑ n₀ ∈ Finset.range q, ∑ r ∈ Finset.range q, ENNReal.ofReal Ccomp *
            (∑' u : ℤ, (W ((q : ℤ) * u + ((r : ℤ) - (n₀ : ℤ)))) ^ p.toReal) :=
          Finset.sum_le_sum (fun n₀ _ => Finset.sum_le_sum (fun r _ => hpair n₀ r))
      _ = ∑ n₀ ∈ Finset.range q, ENNReal.ofReal Ccomp *
            (∑ r ∈ Finset.range q,
              ∑' u : ℤ, (W ((q : ℤ) * u + ((r : ℤ) - (n₀ : ℤ)))) ^ p.toReal) := by
          refine Finset.sum_congr rfl (fun n₀ _ => ?_)
          rw [Finset.mul_sum]
      _ = ∑ n₀ ∈ Finset.range q, ENNReal.ofReal Ccomp * (∑' x : ℤ, (W x) ^ p.toReal) := by
          refine Finset.sum_congr rfl (fun n₀ _ => ?_)
          rw [hreindex n₀]
      _ = (q : ENNReal) * (ENNReal.ofReal Ccomp * (∑' x : ℤ, (W x) ^ p.toReal)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hWpow : (MeasureTheory.eLpNorm W p MeasureTheory.Measure.count) ^ p.toReal
      = ∑' x : ℤ, (W x) ^ p.toReal :=
    eLpNorm_pow_eq_tsum_int W p hpne hptop
  have hnorm : MeasureTheory.eLpNorm (fun x : ℤ => residueLp p.toReal q F x) p
        MeasureTheory.Measure.count
      = ENNReal.rpow (ENNReal.rpow (q : ENNReal) (-1) * ∑ n₀ ∈ Finset.range q,
          (MeasureTheory.eLpNorm (fun y : ℤ => F y n₀) p MeasureTheory.Measure.count) ^ p.toReal)
          (1 / p.toReal) := by
    have h := Work.KMTAreas.A7Hi.eLpNormResidueLpEq p.toReal hppos q F
    rw [hpo] at h
    change MeasureTheory.eLpNorm (residueLp p.toReal q F) p MeasureTheory.Measure.count
      = ENNReal.rpow (ENNReal.rpow (q : ENNReal) (-1) * ∑ n₀ ∈ Finset.range q,
          (MeasureTheory.eLpNorm (fun y : ℤ => F y n₀) p MeasureTheory.Measure.count) ^ p.toReal)
          (1 / p.toReal)
    exact h
  have hfinal : MeasureTheory.eLpNorm (fun x : ℤ => residueLp p.toReal q F x) p
        MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (Ccomp ^ (1 / p.toReal)) *
        MeasureTheory.eLpNorm W p MeasureTheory.Measure.count := by
    have hrpow : ENNReal.rpow (q : ENNReal) (-1) = (q : ENNReal)⁻¹ :=
      ENNReal.rpow_neg_one (q : ENNReal)
    calc MeasureTheory.eLpNorm (fun x : ℤ => residueLp p.toReal q F x) p MeasureTheory.Measure.count
        = ENNReal.rpow (ENNReal.rpow (q : ENNReal) (-1) * ∑ n₀ ∈ Finset.range q,
            (MeasureTheory.eLpNorm (fun y : ℤ => F y n₀) p MeasureTheory.Measure.count) ^ p.toReal)
            (1 / p.toReal) := hnorm
      _ ≤ ENNReal.rpow (ENNReal.rpow (q : ENNReal) (-1) * ((q : ENNReal) *
            (ENNReal.ofReal Ccomp * (∑' x : ℤ, (W x) ^ p.toReal)))) (1 / p.toReal) :=
          ENNReal.rpow_le_rpow (mul_le_mul' le_rfl hSum) (by positivity)
      _ = ENNReal.rpow (ENNReal.ofReal Ccomp * (∑' x : ℤ, (W x) ^ p.toReal))
            (1 / p.toReal) := by
          rw [hrpow, ← mul_assoc, ENNReal.inv_mul_cancel hq0 hqt, one_mul]
      _ = ENNReal.ofReal Ccomp ^ (1 / p.toReal)
            * (∑' x : ℤ, (W x) ^ p.toReal) ^ (1 / p.toReal) :=
          ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
      _ = ENNReal.ofReal (Ccomp ^ (1 / p.toReal)) *
            MeasureTheory.eLpNorm W p MeasureTheory.Measure.count := by
          rw [show (1 : ℝ) / p.toReal = (p.toReal)⁻¹ from one_div _]
          rw [← ENNReal.ofReal_rpow_of_nonneg hCcomp.le
            (by positivity : (0 : ℝ) ≤ (p.toReal)⁻¹)]
          rw [← hWpow]
          rw [ENNReal.rpow_rpow_inv hppos.ne'
            (MeasureTheory.eLpNorm W p MeasureTheory.Measure.count)]
  exact hfinal

end

end Work.KMTAreas.A7
