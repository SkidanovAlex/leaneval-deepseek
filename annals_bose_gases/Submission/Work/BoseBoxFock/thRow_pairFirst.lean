import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.boxFormContactChem
import Submission.Work.BoseBoxFock.chiRowDict
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.thRow_pairFirst` — the first orientation of the pinned `χ²`-row pair slot

The `θ`-row (`χ²`-row, FS's `ω`-row) of the FS `Q₁` contributes the two orientations
`n₀ ∘ |η_{C'}⟩⟨e₀|` and `|e₀⟩⟨η_{C'}| ∘ n₀` of its pair slot.  This module evaluates the
**first** orientation: for a box state `Φ` (continuous), a mode bundle `e` whose condensate mode
is pinned to the corpus box indicator (`e 0 =ᵐ (√ℓ³)⁻¹ θ_Λ`) and a superposed θ-mode vector `C'`
pinned to `thMode ℓ N = χ_Λ² − θ_Λ − thetaTail` (times `√ℓ³`), the pairing of the box restriction
with the nested slot word is the `n₀`-sandwich `pairHalfOne` at the position weight
`thW ℓ N = χ_Λ² − 1 − Re(thetaTail)`, i.e.

`(cIPn n (boxRestrictC ℓ Φ) (B (B' (boxRestrictC ℓ Φ)))).re = pairHalfOne n ℓ (thW ℓ N) Φ`,

`B  = boxSlotSum e (|e₀⟩⟨e₀|)`, `B' = boxSlotSum e (|C'⟩⟨e₀|)`.

## The proof

Everything is a.e. bookkeeping between the box slot calculus and the corpus slot means.

* `thRow_outer_dict`: the *outer* slot word collapses to the slot means of the middle function
  `∑_j thMode(x_j)·aPC_j` (the `θ`-row dictionary `thRow_thMode_dict` for the inner slot word,
  the condensate dictionary `uSlot_sum_ae_eq_aPC_sum` for the outer one);
* the middle function `Mid` is measurable (`thRow_aPC_measurable`) and globally bounded
  (`thRow_thMode_measurable`, `thRow_thMode_bound`, `norm_aPC_le`), so each of its fibres is
  integrable on the cube (`chiRow_integrableOn_update_of_bounded`) and `aPC_re` may be applied
  slot by slot, giving `Re (aPC_j Mid) = aP_j (Re ∘ Mid)`;
* `thRow_weight_dict`: on the box `Re Mid` is the `thW`-weight `∑_j thW(x_j)·aP_jΦ`;
* the slot mean is a.e. congruent on the box (`thRow_aP_ae_congr`, proved here from the complex
  congruence `aPC_congr_ae_abox_B`), which replaces `Re ∘ Mid` by the weight;
* `cIPn` against the box restriction is the real integral of `Φ·Re` over the box
  (`thRow_cIPn_re_self`), and `pairHalfOne` is its definitional form.

The main theorem is assembled from the five pieces by `thRow_pairFirst_of_pieces`, each piece
being proved in full in §5 below.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

local notation "Sp" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open Work.BoseDict

/-! ## 1. Regularity of the box restriction of a continuous state -/

/-- The complex box restriction of a continuous state is measurable. -/
theorem thRow_boxRestrictC_measurable {n : ℕ} (ℓ : ℝ) {Φ : X n → ℝ} (hΦc : Continuous Φ) :
    Measurable (boxRestrictC ℓ Φ) := by
  have h : boxRestrictC ℓ Φ = fun x : X n =>
      ((Φ x : ℝ) : ℂ) *
        (((abox n ℓ).indicator (fun _ => (1 : ℝ)) x : ℝ) : ℂ) := rfl
  rw [h]
  exact (Complex.continuous_ofReal.measurable.comp hΦc.measurable).mul
    (Complex.continuous_ofReal.measurable.comp
      (measurable_const.indicator (abox_measurable n ℓ)))

/-- The complex box restriction of a continuous state is globally bounded. -/
theorem thRow_boxRestrictC_bound {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X n → ℝ}
    (hΦc : Continuous Φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : X n, ‖boxRestrictC ℓ Φ x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (abox_compact n hℓ).exists_bound_of_continuousOn hΦc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  have hx : boxRestrictC ℓ Φ x = ((Φ x : ℝ) : ℂ) *
      (((abox n ℓ).indicator (fun _ => (1 : ℝ)) x : ℝ) : ℂ) := rfl
  rw [hx]
  by_cases h : x ∈ abox n ℓ
  · rw [Set.indicator_of_mem h]
    simp only [Complex.ofReal_one, mul_one, Complex.norm_real]
    exact (hC x h).trans (le_max_left _ _)
  · rw [Set.indicator_of_notMem h]
    simp

/-! ## 2. The real slot mean is a.e. congruent on the box -/

/-- Two real states agreeing a.e. on the box have equal real slot means a.e. on the box.  This is
the real version of `aPC_congr_ae_abox_B`, obtained by complexifying and taking real parts. -/
theorem thRow_aP_ae_congr {n : ℕ} {ℓ : ℝ} (i : Fin n) {f g : X n → ℝ}
    (h : f =ᵐ[volume.restrict (abox n ℓ)] g) :
    (fun x => aP ℓ i f x) =ᵐ[volume.restrict (abox n ℓ)] (fun x => aP ℓ i g x) := by
  have hc : (fun y : X n => ((f y : ℝ) : ℂ))
      =ᵐ[volume.restrict (abox n ℓ)] (fun y : X n => ((g y : ℝ) : ℂ)) := by
    filter_upwards [h] with y hy
    rw [hy]
  have h1 := aPC_congr_ae_abox_B (ℓ := ℓ) i hc
  rw [aPC_ofReal_re ℓ i f, aPC_ofReal_re ℓ i g] at h1
  filter_upwards [h1] with x hx
  exact_mod_cast hx

/-! ## 3. The complex slot mean of a measurable state is measurable -/

/-- The complex slot mean of a measurable state is measurable (a partial Bochner integral of a
jointly measurable function). -/
theorem thRow_aPC_measurable {n : ℕ} (ℓ : ℝ) (j : Fin n) {Ψ : X n → ℂ}
    (hΨ : Measurable Ψ) : Measurable (aPC ℓ j Ψ) := by
  have hjoint : Measurable (fun p : X n × Sp => Ψ (Function.update p.1 j p.2)) :=
    hΨ.comp (measurable_update_pair j)
  have hsm : StronglyMeasurable (fun x : X n => ∫ y : Sp,
      Ψ (Function.update x j y) ∂((volume : Measure Sp).restrict (acube ℓ))) :=
    hjoint.stronglyMeasurable.integral_prod_right'
  show Measurable (fun x : X n => ((1 / ℓ ^ 3 : ℝ) : ℂ) *
      ∫ y in acube ℓ, Ψ (Function.update x j y))
  exact hsm.measurable.const_mul _

/-! ## 4. The assembly, from the five pieces -/

/-- **The first orientation of the `θ`-row pair slot, assembled from its five pieces.**

* `hOuter` — the outer slot word collapses a.e. to the slot means of the middle function;
* `hWeight` — on the box the real part of the middle function is the `thW`-weight;
* `hCIPn` — the `cIPn` pairing against the box restriction is the real box integral;
* `hReg` — the nested slot word is measurable and globally bounded;
* `hMode` — `thMode` is measurable and uniformly bounded. -/
theorem thRow_pairFirst_of_pieces {n m : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ}
    {e : Fin m → Sp → ℂ} {C' : Fin m → ℝ} {Φ : X n → ℝ} (hΦc : Continuous Φ)
    (hOuter : (fun x => Work.BoseDict.boxSlotSum e (rankOne (evec0 m))
        (Work.BoseDict.boxSlotSum e (rankOnePair C' (evec0 m)) (boxRestrictC ℓ Φ)) x)
      =ᵐ[volume.restrict (abox n ℓ)]
      (fun x => ∑ i : Fin n, aPC ℓ i
        (fun y : X n => ∑ j : Fin n, thMode ℓ N (y j)
          * aPC ℓ j (boxRestrictC ℓ Φ) y) x))
    (hWeight : (fun y : X n =>
        (∑ j : Fin n, thMode ℓ N (y j) * aPC ℓ j (boxRestrictC ℓ Φ) y).re)
      =ᵐ[volume.restrict (abox n ℓ)]
      (fun y => ∑ j : Fin n, thW ℓ N (y j) * aP ℓ j Φ y))
    (hCIPn : ∀ {G : X n → ℂ}, Measurable G → (∃ C : ℝ, ∀ x, ‖G x‖ ≤ C) →
      (Work.BoseDict.cIPn n (boxRestrictC ℓ Φ) G).re
        = ∫ x in abox n ℓ, Φ x * (G x).re)
    (hReg : Measurable (Work.BoseDict.boxSlotSum e (rankOne (evec0 m))
          (Work.BoseDict.boxSlotSum e (rankOnePair C' (evec0 m)) (boxRestrictC ℓ Φ)))
        ∧ ∃ C : ℝ, ∀ x, ‖Work.BoseDict.boxSlotSum e (rankOne (evec0 m))
          (Work.BoseDict.boxSlotSum e (rankOnePair C' (evec0 m))
            (boxRestrictC ℓ Φ)) x‖ ≤ C)
    (hMode : (∀ (ℓ : ℝ) (N : ℕ), Measurable (thMode ℓ N))
      ∧ (∃ C : ℝ, 0 ≤ C ∧ ∀ (ℓ : ℝ), 0 < ℓ → ∀ (N : ℕ) (z : Sp),
          ‖thMode ℓ N z‖ ≤ C)) :
    (Work.BoseDict.cIPn n (boxRestrictC ℓ Φ)
        (Work.BoseDict.boxSlotSum e (rankOne (evec0 m))
          (Work.BoseDict.boxSlotSum e (rankOnePair C' (evec0 m))
            (boxRestrictC ℓ Φ)))).re
      = pairHalfOne n ℓ (thW ℓ N) Φ := by
  classical
  set A : X n → ℂ := Work.BoseDict.boxSlotSum e (rankOne (evec0 m))
      (Work.BoseDict.boxSlotSum e (rankOnePair C' (evec0 m)) (boxRestrictC ℓ Φ)) with hAdef
  set Mid : X n → ℂ := fun y : X n => ∑ j : Fin n, thMode ℓ N (y j)
      * aPC ℓ j (boxRestrictC ℓ Φ) y with hMiddef
  set Wt : X n → ℝ := fun y : X n => ∑ j : Fin n, thW ℓ N (y j) * aP ℓ j Φ y with hWtdef
  -- regularity of the middle function
  obtain ⟨Cth, hCth0, hCth⟩ := hMode.2
  obtain ⟨CΨ, hCΨ0, hCΨ⟩ := thRow_boxRestrictC_bound (n := n) hℓ hΦc
  have hΨm : Measurable (boxRestrictC ℓ Φ) := thRow_boxRestrictC_measurable ℓ hΦc
  have hTm : Measurable Mid := by
    rw [hMiddef]
    refine Finset.measurable_sum _ (fun j _ => ?_)
    exact ((hMode.1 ℓ N).comp (measurable_pi_apply j)).mul
      (thRow_aPC_measurable ℓ j hΨm)
  have hTb : ∀ y : X n, ‖Mid y‖ ≤ (n : ℝ) * (Cth * CΨ) := by
    intro y
    rw [hMiddef]
    calc ‖∑ j : Fin n, thMode ℓ N (y j) * aPC ℓ j (boxRestrictC ℓ Φ) y‖
        ≤ ∑ j : Fin n, ‖thMode ℓ N (y j) * aPC ℓ j (boxRestrictC ℓ Φ) y‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _j : Fin n, Cth * CΨ := Finset.sum_le_sum (fun j _ => by
            rw [norm_mul]
            exact mul_le_mul (hCth ℓ hℓ N (y j))
              (norm_aPC_le hℓ j hCΨ0 hCΨ y) (norm_nonneg _) hCth0)
      _ = (n : ℝ) * (Cth * CΨ) := by
            rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  have hfib : ∀ (i : Fin n) (x : X n),
      IntegrableOn (fun y : Sp => Mid (Function.update x i y)) (acube ℓ) volume :=
    fun i x => chiRow_integrableOn_update_of_bounded hℓ i hTm hTb x
  -- the spine: `Re A = Σ_i aP ℓ i Wt` a.e. on the box
  have hspine : (fun x => (A x).re) =ᵐ[volume.restrict (abox n ℓ)]
      (fun x => ∑ i : Fin n, aP ℓ i Wt x) := by
    have e1 : (fun x => (A x).re) =ᵐ[volume.restrict (abox n ℓ)]
        (fun x => (∑ i : Fin n, aPC ℓ i Mid x).re) := by
      filter_upwards [hOuter] with x hx
      rw [hx]
    have e2 : (fun x => (∑ i : Fin n, aPC ℓ i Mid x).re)
        = (fun x => ∑ i : Fin n, (aPC ℓ i Mid x).re) := by
      funext x
      exact map_sum Complex.reAddGroupHom (fun i => aPC ℓ i Mid x) Finset.univ
    have e3 : (fun x => ∑ i : Fin n, (aPC ℓ i Mid x).re)
        = (fun x => ∑ i : Fin n, aP ℓ i (fun y => (Mid y).re) x) := by
      funext x
      exact Finset.sum_congr rfl (fun i _ => aPC_re ℓ i Mid x (hfib i x))
    have hMidW : (fun y : X n => (Mid y).re) =ᵐ[volume.restrict (abox n ℓ)] Wt := by
      simpa only [hMiddef, hWtdef] using hWeight
    have e4 : (fun x => ∑ i : Fin n, aP ℓ i (fun y => (Mid y).re) x)
        =ᵐ[volume.restrict (abox n ℓ)] (fun x => ∑ i : Fin n, aP ℓ i Wt x) := by
      filter_upwards [(Finset.eventually_all Finset.univ).mpr
        (fun i _ => thRow_aP_ae_congr (ℓ := ℓ) i hMidW)] with x hx
      exact Finset.sum_congr rfl (fun i _ => hx i (Finset.mem_univ i))
    refine e1.trans ?_
    rw [e2, e3]
    exact e4
  -- assembly
  have hmain : (Work.BoseDict.cIPn n (boxRestrictC ℓ Φ) A).re
      = ∫ x in abox n ℓ, Φ x * (∑ i : Fin n, aP ℓ i Wt x) := by
    rw [hCIPn hReg.1 hReg.2]
    refine integral_congr_ae ?_
    filter_upwards [hspine] with x hx
    rw [hx]
  rw [pairHalfOne]
  simpa only [hWtdef, Finset.sum_apply] using hmain

/-! ## 5. The five pieces of the assembly, proved in full -/

/-- Set-integral version of `integral_re`, for an arbitrary measurable space. -/
theorem thRow_setIntegral_re_complex {α : Type*} [MeasureSpace α] (s : Set α)
    (f : α → ℂ) (hf : IntegrableOn f s (volume : Measure α)) :
    (∫ y in s, f y).re = ∫ y in s, (f y).re := by
  have h := integral_re (𝕜 := ℂ) (μ := (volume : Measure α).restrict s) (f := f) hf
  simpa using h.symm

/-! ## Fallback proofs of the delegated pieces -/

theorem thRow_thMode_measurable (ℓ : ℝ) (N : ℕ) : Measurable (thMode ℓ N) := by
  have hθm : Measurable (Work.BoseK15.corpusBox.thetaFun ℓ) := by
    have h : Work.BoseK15.corpusBox.thetaFun ℓ
        = Set.indicator (Work.BoseK15.corpusBox.boxL ℓ) (fun _ : Sp => (1 : ℂ)) := by
      funext z
      rw [Work.BoseB4.BoxData.thetaFun_apply]
      by_cases hz : z ∈ Work.BoseK15.corpusBox.boxL ℓ <;> simp [hz]
    rw [h]
    exact measurable_const.indicator
      (Work.BoseB4.BoxData.boxL_measurableSet (B := Work.BoseK15.corpusBox) ℓ)
  have hχm : Measurable (fun z : Sp =>
      ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp
      ((Work.BoseB4.BoxData.chiLam_cont (B := Work.BoseK15.corpusBox) ℓ).measurable)
  have hsqu : Measurable (fun z : Sp =>
      ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ) ^ 2) :=
    ((continuous_id (X := ℂ)).pow 2).measurable.comp hχm
  have hθEm : ∀ s : Sp, Measurable (Work.BoseK15.corpusBox.thetaExp ℓ s) := by
    intro s
    have h : Work.BoseK15.corpusBox.thetaExp ℓ s = fun z : Sp =>
        Complex.exp (Complex.I * ((inner ℝ s z : ℝ) : ℂ))
          * Work.BoseK15.corpusBox.thetaFun ℓ z :=
      funext fun z => Work.BoseB4.BoxData.thetaExp_apply (B := Work.BoseK15.corpusBox) ℓ s z
    rw [h]
    exact (Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp
        (Continuous.inner continuous_const continuous_id)))).measurable.mul hθm
  have htail : Measurable (fun z : Sp =>
      ∑ s ∈ (Finset.univ.filter (fun s : Lab N => s ≠ 0)),
        ((Work.BoseK15.corpusBox.hatChiSq (ℓ • kmomLab ℓ N s) : ℝ) : ℂ)
          * Work.BoseK15.corpusBox.thetaExp ℓ (kmomLab ℓ N s) z) :=
    Finset.measurable_sum _ (fun s _ => (hθEm (kmomLab ℓ N s)).const_mul _)
  have hθTm : Measurable (thetaTail ℓ N) := by
    unfold thetaTail
    exact Measurable.sub (Measurable.sub hsqu hθm) htail
  unfold thMode
  exact Measurable.sub (Measurable.sub hsqu hθm) hθTm

theorem thRow_thMode_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ℓ : ℝ), 0 < ℓ → ∀ (N : ℕ) (z : Sp),
      ‖thMode ℓ N z‖ ≤ C := by
  obtain ⟨Ct, hCt0, hCt⟩ := thetaTail_bound 0
  refine ⟨Real.sqrt (48 / Real.pi) ^ 2 + 1 + Ct, by positivity, fun ℓ hℓ N z => ?_⟩
  have hχ : |Work.BoseK15.corpusBox.chiLam ℓ z| ≤ Real.sqrt (48 / Real.pi) := by
    simp only [Work.BoseB4.BoxData.chiLam]
    exact abs_chiR_le _
  have h1 : ‖(((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ) ^ 2‖
      ≤ Real.sqrt (48 / Real.pi) ^ 2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hχ 2
  have h2 : ‖Work.BoseK15.corpusBox.thetaFun ℓ z‖ ≤ 1 := by
    rw [Work.BoseB4.BoxData.thetaFun_apply]
    split <;> simp
  have h3 : ‖thetaTail ℓ N z‖ ≤ Ct := by
    have := hCt ℓ hℓ N z
    simpa using this
  have hA : ‖(((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ) ^ 2
      - Work.BoseK15.corpusBox.thetaFun ℓ z‖
      ≤ Real.sqrt (48 / Real.pi) ^ 2 + 1 := by
    calc ‖(((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ) ^ 2
          - Work.BoseK15.corpusBox.thetaFun ℓ z‖
        ≤ ‖(((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ) ^ 2‖
            + ‖Work.BoseK15.corpusBox.thetaFun ℓ z‖ := norm_sub_le _ _
      _ ≤ Real.sqrt (48 / Real.pi) ^ 2 + 1 := add_le_add h1 h2
  calc ‖thMode ℓ N z‖
      = ‖(((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ) ^ 2
          - Work.BoseK15.corpusBox.thetaFun ℓ z - thetaTail ℓ N z‖ := rfl
    _ ≤ ‖(((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ) ^ 2
          - Work.BoseK15.corpusBox.thetaFun ℓ z‖ + ‖thetaTail ℓ N z‖ := norm_sub_le _ _
    _ ≤ Real.sqrt (48 / Real.pi) ^ 2 + 1 + Ct := add_le_add hA h3

theorem thRow_weight_dict {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    (fun y : Submission.BoseGases.X n =>
        (∑ j : Fin n, Work.BoseBoxFock.thMode ℓ N (y j)
          * Work.BoseBoxFock.aPC ℓ j (Work.BoseBoxFock.boxRestrictC ℓ Φ) y).re)
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)]
      (fun y => ∑ j : Fin n, Work.BoseBoxFock.thW ℓ N (y j)
        * Submission.BoseGases.aP ℓ j Φ y) := by
  filter_upwards [MeasureTheory.ae_restrict_mem (Submission.BoseGases.abox_measurable n ℓ)]
    with y hy
  rw [Complex.re_sum Finset.univ (fun j : Fin n =>
    Work.BoseBoxFock.thMode ℓ N (y j)
      * Work.BoseBoxFock.aPC ℓ j (Work.BoseBoxFock.boxRestrictC ℓ Φ) y)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hyj : y j ∈ Submission.BoseGases.acube ℓ :=
    (Submission.BoseGases.mem_abox_iff n ℓ y).mp hy j
  have haPC : Work.BoseBoxFock.aPC ℓ j (Work.BoseBoxFock.boxRestrictC ℓ Φ) y
      = (((Submission.BoseGases.aP ℓ j Φ y : ℝ)) : ℂ) :=
    (chiRow_aPC_dict hℓ).2.1 j Φ y hy
  have hth : (Work.BoseBoxFock.thMode ℓ N (y j)).re = Work.BoseBoxFock.thW ℓ N (y j) :=
    thMode_re_of_theta_eq_one ℓ N (thetaFun_eq_one_of_mem_acube hℓ hyj)
  rw [haPC, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, hth]

theorem thRow_cIPn_re_self {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ)
    {G : Submission.BoseGases.X n → ℂ} (hGm : Measurable G)
    (hGb : ∃ C : ℝ, ∀ x, ‖G x‖ ≤ C) :
    (Work.BoseDict.cIPn n (Work.BoseBoxFock.boxRestrictC ℓ Φ) G).re
      = ∫ x in Submission.BoseGases.abox n ℓ, Φ x * (G x).re := by
  obtain ⟨CΦ, hCΦ⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
    hΦc.continuousOn
  obtain ⟨CG, hCG⟩ := hGb
  have hfin := Submission.BoseGases.abox_lt_top n ℓ hℓ.le
  have hI : IntegrableOn (fun x : Submission.BoseGases.X n =>
      ((Φ x : ℝ) : ℂ) * G x) (Submission.BoseGases.abox n ℓ)
      (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)) := by
    refine MeasureTheory.IntegrableOn.of_bound hfin ?_ (max CΦ 0 * max CG 0) ?_
    · exact ((Complex.continuous_ofReal.measurable.comp hΦc.measurable).aestronglyMeasurable.mul
        hGm.aestronglyMeasurable).restrict
    · filter_upwards [MeasureTheory.self_mem_ae_restrict
        (Submission.BoseGases.abox_measurable n ℓ)] with x hx
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul ((hCΦ x hx).trans (le_max_left _ _))
        ((hCG x).trans (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _)
  have hpt : ∀ x : Submission.BoseGases.X n,
      (starRingEnd ℂ) (Work.BoseBoxFock.boxRestrictC ℓ Φ x) * G x
        = (Submission.BoseGases.abox n ℓ).indicator
            (fun x => ((Φ x : ℝ) : ℂ) * G x) x := by
    intro x
    rw [show Work.BoseBoxFock.boxRestrictC ℓ Φ x = ((Φ x : ℝ) : ℂ) *
        (((Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) x : ℝ) : ℂ)
        from rfl]
    by_cases hx : x ∈ Submission.BoseGases.abox n ℓ
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      simp
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
      simp
  rw [Work.BoseDict.cIPn,
    show (∫ x : Submission.BoseGases.X n,
          (starRingEnd ℂ) (Work.BoseBoxFock.boxRestrictC ℓ Φ x) * G x)
        = ∫ x : Submission.BoseGases.X n, (Submission.BoseGases.abox n ℓ).indicator
            (fun x => ((Φ x : ℝ) : ℂ) * G x) x from
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt),
    MeasureTheory.integral_indicator (Submission.BoseGases.abox_measurable n ℓ),
    thRow_setIntegral_re_complex (Submission.BoseGases.abox n ℓ)
      (fun x => ((Φ x : ℝ) : ℂ) * G x) hI]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  simp [Complex.mul_re]

theorem thRow_slotSum_reg {n m : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ)
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l))
    (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {C' : Fin m → ℝ} {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    Measurable (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOne (Work.BoseBoxFock.evec0 m))
        (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOnePair C' (Work.BoseBoxFock.evec0 m))
          (Work.BoseBoxFock.boxRestrictC ℓ Φ)))
      ∧ ∃ C : ℝ, ∀ x, ‖Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOne
            (Work.BoseBoxFock.evec0 m))
        (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOnePair C' (Work.BoseBoxFock.evec0 m))
          (Work.BoseBoxFock.boxRestrictC ℓ Φ)) x‖ ≤ C := by
  have hΨm : Measurable (Work.BoseBoxFock.boxRestrictC ℓ Φ) :=
    thRow_boxRestrictC_measurable ℓ hΦc
  obtain ⟨CΨ, hCΨ0, hCΨ⟩ := thRow_boxRestrictC_bound (n := n) hℓ hΦc
  have h1 := Work.MB.boxSlotSum_measurable_bounded_ae (ℓ := ℓ) hmeas hbdd hsupp
    (Work.BoseBoxFock.rankOnePair C' (Work.BoseBoxFock.evec0 m))
    (Work.BoseBoxFock.boxRestrictC ℓ Φ) hΨm ⟨CΨ, hCΨ⟩
  have h2 := Work.MB.boxSlotSum_measurable_bounded_ae (ℓ := ℓ) hmeas hbdd hsupp
    (Work.BoseBoxFock.rankOne (Work.BoseBoxFock.evec0 m))
    (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOnePair C' (Work.BoseBoxFock.evec0 m))
      (Work.BoseBoxFock.boxRestrictC ℓ Φ)) h1.1 h1.2
  exact h2

theorem thRow_outer_dict {n m : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ}
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hpin : e 0 =ᵐ[MeasureTheory.volume] fun z =>
      ((Real.sqrt (ℓ ^ 3))⁻¹ : ℂ) * Work.BoseK15.corpusBox.thetaFun ℓ z)
    (hmeas : ∀ l, Measurable (e l))
    (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {C' : Fin m → ℝ} (hC : (fun z => ((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ) * Work.BoseDict.etaOf e C' z)
      =ᵐ[MeasureTheory.volume] Work.BoseBoxFock.thMode ℓ N)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    (fun x => Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOne (Work.BoseBoxFock.evec0 m))
        (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOnePair C' (Work.BoseBoxFock.evec0 m))
          (Work.BoseBoxFock.boxRestrictC ℓ Φ)) x)
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)]
      (fun x => ∑ i : Fin n, Work.BoseBoxFock.aPC ℓ i
        (fun y : Submission.BoseGases.X n =>
          ∑ j : Fin n, Work.BoseBoxFock.thMode ℓ N (y j)
            * Work.BoseBoxFock.aPC ℓ j (Work.BoseBoxFock.boxRestrictC ℓ Φ) y) x) := by
  have hΨm : Measurable (Work.BoseBoxFock.boxRestrictC ℓ Φ) :=
    thRow_boxRestrictC_measurable ℓ hΦc
  obtain ⟨CΨ, hCΨ0, hCΨ⟩ := thRow_boxRestrictC_bound (n := n) hℓ hΦc
  -- the inner (θ-row) dictionary
  have hinner := thRow_thMode_dict (m := m) (d := n) (ℓ := ℓ) (N := N) (e := e)
    hℓ hpin hmeas hbdd hsupp hC (Work.BoseBoxFock.boxRestrictC ℓ Φ) hΨm ⟨CΨ, hCΨ⟩
  -- the outer (condensate) dictionary
  have hcc : (starRingEnd ℂ) (((Real.sqrt (ℓ ^ 3))⁻¹ : ℂ)) * (((Real.sqrt (ℓ ^ 3))⁻¹ : ℂ))
      = (ℓ ^ 3)⁻¹ := conj_inv_sqrt_mul_self hℓ
  have houter := uSlot_sum_ae_eq_aPC_sum (ℓ := ℓ) hℓ hpin hcc
    (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOnePair C' (Work.BoseBoxFock.evec0 m))
      (Work.BoseBoxFock.boxRestrictC ℓ Φ))
  have h1 : (fun x => Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOne
        (Work.BoseBoxFock.evec0 m))
        (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOnePair C' (Work.BoseBoxFock.evec0 m))
          (Work.BoseBoxFock.boxRestrictC ℓ Φ)) x)
      = (fun x => ∑ j : Fin n, Work.BoseBoxFock.uSlot (e 0) j
          (Work.BoseDict.boxSlotSum e
            (Work.BoseBoxFock.rankOnePair C' (Work.BoseBoxFock.evec0 m))
            (Work.BoseBoxFock.boxRestrictC ℓ Φ)) x) := by
    rw [Work.BoseBoxFock.boxSlotSum_rankOne_evec0_eq_proj0 e,
      Work.BoseBoxFock.boxSlotSum_proj0 e]
  have h3 : (fun x => ∑ j : Fin n, Work.BoseBoxFock.aPC ℓ j
        (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOnePair C' (Work.BoseBoxFock.evec0 m))
          (Work.BoseBoxFock.boxRestrictC ℓ Φ)) x)
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)]
      (fun x => ∑ j : Fin n, Work.BoseBoxFock.aPC ℓ j
        (fun y : Submission.BoseGases.X n =>
          ∑ i : Fin n, Work.BoseBoxFock.thMode ℓ N (y i)
            * Work.BoseBoxFock.aPC ℓ i (Work.BoseBoxFock.boxRestrictC ℓ Φ) y) x) := by
    filter_upwards [(Finset.eventually_all Finset.univ).mpr
      (fun j _ => aPC_congr_ae_abox_B (ℓ := ℓ) j hinner)] with x hx
    exact Finset.sum_congr rfl (fun j _ => hx j (Finset.mem_univ j))
  exact ((Filter.EventuallyEq.of_eq h1).trans houter).trans h3


/-! ## 6. The target -/


theorem thRow_pairFirst {n m : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ}
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hpin : e 0 =ᵐ[MeasureTheory.volume] fun z =>
      ((Real.sqrt (ℓ ^ 3))⁻¹ : ℂ) * Work.BoseK15.corpusBox.thetaFun ℓ z)
    (hmeas : ∀ l, Measurable (e l)) (hemem : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {C' : Fin m → ℝ} (hC : (fun z => ((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ) * Work.BoseDict.etaOf e C' z)
      =ᵐ[MeasureTheory.volume] Work.BoseBoxFock.thMode ℓ N)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    (Work.BoseDict.cIPn n (Work.BoseBoxFock.boxRestrictC ℓ Φ)
        (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOne (Work.BoseBoxFock.evec0 m))
          (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOnePair C' (Work.BoseBoxFock.evec0 m))
            (Work.BoseBoxFock.boxRestrictC ℓ Φ)))).re
      = Work.BoseBoxFock.pairHalfOne n ℓ (Work.BoseBoxFock.thW ℓ N) Φ := by
  refine thRow_pairFirst_of_pieces (n := n) (m := m) (ℓ := ℓ) (N := N) (e := e) (C' := C')
    (Φ := Φ) hℓ hΦc ?_ ?_ ?_ ?_ ?_
  · exact thRow_outer_dict (m := m) hℓ hpin hmeas hbdd hsupp hC hΦc
  · exact thRow_weight_dict hℓ hΦc
  · intro G hGm hGb
    exact thRow_cIPn_re_self hℓ hΦc hGm hGb
  · exact thRow_slotSum_reg hℓ hmeas hbdd hsupp hΦc
  · exact ⟨thRow_thMode_measurable, thRow_thMode_bound⟩

end Work.BoseBoxFock
