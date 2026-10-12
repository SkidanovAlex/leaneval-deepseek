import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.AVgenDictGen.AVgen_slice
import Submission.Work.BoseBoxFock.modelAssembly
import Submission.Work.MB.AVgen_add_I_smul_ae
import Submission.Work.MB.AVgen_slotFacts_ae
import Submission.Work.MB.boxRealise_weak_bdd
import Submission.Work.MB.cIPn_AVgen_gen_ae
import Submission.Work.MB.exists_slice_le_window_of_op_weak
import Submission.Work.MB.sliceModelWindow_deg_ae
import Submission.Work.MB.slotFacts_comp_slotSum_ae
import Submission.Work.MB.slotFacts_id_ae
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The weak-state twin of `Work.MB.modelAssemblyAVgen_ae`

The BF3c model assembly at the state class of the box restriction `Θ = Φ·1_abox`: the state
hypotheses `Continuous Φ` + `HasCompactSupport Φ` + `tsupport Φ ⊆ abox n ℓ` are replaced by
`Measurable Φ` + a global bound + `support Φ ⊆ abox n ℓ`, and `tsupport Φc ⊆ abox n ℓ` is
*derived* from `support Φ ⊆ abox n ℓ` by closedness of the box.  The only other change is the
sector selection, `Work.MB.exists_slice_le_window_of_op_ae` ⟶
`Work.MB.exists_slice_le_window_of_op_weak`.
-/

open MeasureTheory

namespace Work.MB

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

open Work.BoseB4 Work.BoseDict

theorem modelAssemblyAVgen_weak {m n : ℕ} [NeZero m] {ℓ M : ℝ}
    (hℓ : 0 < ℓ) (e : Fin m → Ω → ℂ)
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (horth : ∀ l l', (∫ z : Ω, star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (hint : ∀ l l', MeasureTheory.Integrable (fun z : Ω => star (e l z) * e l' z))
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (hpin : ∃ c : ℂ, (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹ ∧
      (∀ᵐ x ∂(volume : MeasureTheory.Measure Ω),
        e 0 x = c * Work.BoseK15.corpusBox.thetaFun ℓ x))
    {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (T_NH : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (PHs : Finset Mode)
    (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ)
    (Φ : Submission.BoseGases.X n → ℝ) (hΦm0 : Measurable Φ)
    (hΦb0 : ∃ C : ℝ, ∀ x, |Φ x| ≤ C)
    (hΦsupp : Function.support Φ ⊆ Submission.BoseGases.abox n ℓ)
    (hΦsym : ∀ σ : Equiv.Perm (Fin n),
      (fun x : Submission.BoseGases.X n => Φ (x ∘ σ)) = Φ)
    (hM : 0 ≤ M) (hmom : Work.BoseBox.SpectralNPlusLe ℓ M Φ)
    (c : ℝ) (hpos : 0 < Work.BoseBoxFock.massR (fun x => ((Φ x : ℝ) : ℂ)))
    (hcle : (∫ x : Submission.BoseGases.X n,
        star ((fun x : Submission.BoseGases.X n => ((Φ x : ℝ) : ℂ)) x)
          * Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
              (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ))
              f g T_NH PHs E gHat0 (fun x => ((Φ x : ℝ) : ℂ)) x).re
      ≤ c * Work.BoseBoxFock.massR (fun x => ((Φ x : ℝ) : ℂ))) :
    ∃ Ψ : Work.BoseB4.RealFock m, Ψ ≠ 0 ∧ Work.BoseBoxFock.ExcWindow M n Ψ ∧
      Work.BoseB4.bomb m Ψ (Work.BoseBoxFock.H2ndF f g (Work.BoseB4.dGamma m T_NH) PHs E gHat0 Ψ)
        ≤ c * Work.BoseB4.bomb m Ψ Ψ := by
  classical
  -- ## step 0: the complex box state `Φc` and its weak regularity
  set Φc : Submission.BoseGases.X n → ℂ := fun x => ((Φ x : ℝ) : ℂ) with hΦcdef
  have he : ∀ l l', (∫ x : Ω, (starRingEnd ℂ) (e l x) * e l' x)
      = (if l = l' then (1 : ℂ) else 0) := by
    intro l l'
    simpa only [starRingEnd_apply] using horth l l'
  have hΦcsym : ∀ σ : Equiv.Perm (Fin n),
      (fun x : Submission.BoseGases.X n => Φc (x ∘ σ)) = Φc := by
    intro σ
    funext x
    rw [hΦcdef]
    show ((Φ (x ∘ σ) : ℝ) : ℂ) = ((Φ x : ℝ) : ℂ)
    rw [show Φ (x ∘ σ) = Φ x from congrFun (hΦsym σ) x]
  have hΦcm : Measurable Φc := by
    rw [hΦcdef]
    exact Complex.continuous_ofReal.measurable.comp hΦm0
  have hΦcb : ∃ C, ∀ x, ‖Φc x‖ ≤ C := by
    obtain ⟨C, hC⟩ := hΦb0
    refine ⟨max C 0, fun x => ?_⟩
    rw [hΦcdef, Complex.norm_real, Real.norm_eq_abs]
    exact le_trans (hC x) (le_max_left C 0)
  have hsupp_eq : Function.support Φc = Function.support Φ := by
    rw [hΦcdef]
    ext x
    simp only [Function.mem_support, ne_eq, Complex.ofReal_eq_zero]
  have hts : tsupport Φc = tsupport Φ := by
    simp only [tsupport, hsupp_eq]
  have hΦcts : tsupport Φc ⊆ Submission.BoseGases.abox n ℓ := by
    rw [hts, tsupport]
    exact closure_minimal hΦsupp (Submission.BoseGases.abox_compact n hℓ).isClosed
  have hΦcsupp : Function.support Φc ⊆ boxPow n ℓ :=
    support_subset_boxPow_of_tsupport hΦcts
  -- ## step 1: the `SlotFacts` instance of `AVgen`
  have hFacts : Work.BoseBoxFock.SlotFacts e Φc
      (Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
        (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ)) f g T_NH PHs E gHat0)
      (fun S => Work.BoseBoxFock.AVgen (fun T => Work.BoseBoxFock.slotSumSub e T S)
        (fun Y => Y) f g T_NH PHs E gHat0) :=
    AVgen_slotFacts_ae (m := m) (n := n) (e := e) hmeas hbdE hsupp horth hint hΦcm hΦcb hΦcsupp
      (fun T => Work.BoseDict.boxSlotSum e T)
      (fun T S => Work.BoseBoxFock.slotSumSub e T S)
      (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ))
      (fun T => slotFacts_boxSlotSum_ae hℓ hmeas hbdE hsupp horth hint Φc hΦcm hΦcb hΦcts T)
      (fun T₁ T₂ => slotFacts_comp_slotSum_ae hmeas hbdE hsupp horth hint hΦcm hΦcb hΦcts T₁ T₂)
      (slotFacts_id_ae hmeas hbdE hsupp horth hΦcm hΦcb hΦcsupp)
      f g T_NH PHs E gHat0
  -- ## step 2: the derived fibre facts
  obtain ⟨hqint, hdec⟩ :=
    slotFacts_dec_fibre_ae hmeas hbdE hsupp horth Φc hΦcm hΦcb hΦcsupp hFacts
  -- ## step 3: the sector/slice selection with the window condition
  obtain ⟨S, y, hmass₀, hle₀, hwin₀⟩ :=
    exists_slice_le_window_of_op_weak hℓ hmeas hbdE horth hint hbdd hsupp hpin Φ hΦm0 hΦb0 hΦsupp
      hΦsym hM hmom Φc rfl
      (Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
        (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ)) f g T_NH PHs E gHat0)
      (fun S => Work.BoseBoxFock.AVgen (fun T => Work.BoseBoxFock.slotSumSub e T S)
        (fun Y => Y) f g T_NH PHs E gHat0)
      hFacts.split hdec hqint c hpos (by simpa only [hΦcdef] using hcle)
  -- ## step 4: the two real model vectors of the slice
  obtain ⟨Ψ₁, Ψ₂, hreal, hw₁, hw₂, hdeg₁, hdeg₂⟩ :=
    sliceModelWindow_deg_ae (M := M) (e := e) hmeas hbdE horth hbdd hsupp S Φc hΦcm hΦcb hΦcsupp
      hΦcsym y (fun α hα hb => by simpa only [hΦcdef] using hwin₀ α hα hb)
  -- ## step 5: the dictionary rows
  have hdict : ∀ Ψ Ψ' : Work.BoseB4.RealFock m,
      (∀ α ∈ Ψ.support, α.sum (fun _ k => k) = S.card) →
      (∀ α ∈ Ψ'.support, α.sum (fun _ k => k) = S.card) →
      Work.BoseDict.cIPn S.card (Work.BoseDict.boxRealise e S.card Ψ)
        (Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
          (id : (Work.BoseDict.Xn S.card → ℂ) → (Work.BoseDict.Xn S.card → ℂ))
          f g T_NH PHs E gHat0 (Work.BoseDict.boxRealise e S.card Ψ'))
        = ((Work.BoseB4.bomb m Ψ
            (Work.BoseBoxFock.H2ndF f g (Work.BoseB4.dGamma m T_NH) PHs E gHat0 Ψ') : ℝ) : ℂ) :=
    fun Ψ Ψ' hΨ hΨ' =>
      cIPn_AVgen_gen_ae (e := e) hℓ he hbdd hsupp f g T_NH PHs E gHat0 S.card Ψ Ψ' hΨ hΨ'
  have hiso : ∀ Ψ Ψ' : Work.BoseB4.RealFock m,
      (∀ α ∈ Ψ.support, α.sum (fun _ k => k) = S.card) →
      (∀ α ∈ Ψ'.support, α.sum (fun _ k => k) = S.card) →
      Work.BoseDict.cIPn S.card (Work.BoseDict.boxRealise e S.card Ψ)
        (Work.BoseDict.boxRealise e S.card Ψ')
        = ((Work.BoseB4.bomb m Ψ Ψ' : ℝ) : ℂ) :=
    fun Ψ Ψ' hΨ _ => Work.BoseDict.boxRealise_cIPn_gen he hbdd hsupp Ψ Ψ' hΨ
  -- ## step 6: weak regularity of the two vectors
  have hreg₁ : Measurable (Work.BoseDict.boxRealise e S.card Ψ₁) ∧
      (∃ C : ℝ, ∀ x, ‖Work.BoseDict.boxRealise e S.card Ψ₁ x‖ ≤ C) ∧
      Function.support (Work.BoseDict.boxRealise e S.card Ψ₁) ⊆ boxPow S.card ℓ :=
    boxRealise_weak_bdd (m := m) (d := S.card) (ℓ := ℓ) (e := e) hmeas hbdE hsupp Ψ₁
  have hreg₂ : Measurable (Work.BoseDict.boxRealise e S.card Ψ₂) ∧
      (∃ C : ℝ, ∀ x, ‖Work.BoseDict.boxRealise e S.card Ψ₂ x‖ ≤ C) ∧
      Function.support (Work.BoseDict.boxRealise e S.card Ψ₂) ⊆ boxPow S.card ℓ :=
    boxRealise_weak_bdd (m := m) (d := S.card) (ℓ := ℓ) (e := e) hmeas hbdE hsupp Ψ₂
  have hgood₁ : Work.BoseBoxFock.SlotGood (Work.BoseDict.boxRealise e S.card Ψ₁) :=
    ⟨hreg₁.1, hreg₁.2.1⟩
  have hgood₂ : Work.BoseBoxFock.SlotGood (Work.BoseDict.boxRealise e S.card Ψ₂) :=
    ⟨hreg₂.1, hreg₂.2.1⟩
  -- ## step 7: the additivity of `AVgen` at the two vectors
  have hAF := AVgen_add_I_smul_ae (m := m) (n := S.card) (e := e) hmeas hbdE hsupp
    f g T_NH PHs E gHat0 (Work.BoseDict.boxRealise e S.card Ψ₁)
    (Work.BoseDict.boxRealise e S.card Ψ₂) hgood₁ hgood₂
  -- ## step 7bis: `AVgen` at degree `S.card` preserves good states
  have hGenLin : Work.BoseBoxFock.GenLin
      (Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
        (id : (Work.BoseDict.Xn S.card → ℂ) → (Work.BoseDict.Xn S.card → ℂ))
        f g T_NH PHs E gHat0) :=
    Work.BoseBoxFock.GenLin_AVgen (fun T => Work.BoseDict.boxSlotSum e T)
      (fun T => GenLin_boxSlotSum_weak (d := S.card) hmeas hbdE hsupp T)
      (id : (Work.BoseDict.Xn S.card → ℂ) → (Work.BoseDict.Xn S.card → ℂ))
      f g T_NH PHs E gHat0
  -- ## step 8: the four `A_V`-pairings and the four norm pairings are integrable
  have hA00 : MeasureTheory.Integrable (fun x : Work.BoseDict.Xn S.card =>
      (starRingEnd ℂ) (Work.BoseDict.boxRealise e S.card Ψ₁ x)
        * (Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
            (id : (Work.BoseDict.Xn S.card → ℂ) → (Work.BoseDict.Xn S.card → ℂ))
            f g T_NH PHs E gHat0 (Work.BoseDict.boxRealise e S.card Ψ₁)) x) := by
    simpa only [starRingEnd_apply] using
      Work.BoseBoxFock.integrable_star_mul_of_box_support (n := S.card) (ℓ := ℓ)
        hreg₁.1 hreg₁.2.1 hreg₁.2.2 (hGenLin.good _ hgood₁).1 (hGenLin.good _ hgood₁).2
  have hA01 : MeasureTheory.Integrable (fun x : Work.BoseDict.Xn S.card =>
      (starRingEnd ℂ) (Work.BoseDict.boxRealise e S.card Ψ₁ x)
        * (Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
            (id : (Work.BoseDict.Xn S.card → ℂ) → (Work.BoseDict.Xn S.card → ℂ))
            f g T_NH PHs E gHat0 (Work.BoseDict.boxRealise e S.card Ψ₂)) x) := by
    simpa only [starRingEnd_apply] using
      Work.BoseBoxFock.integrable_star_mul_of_box_support (n := S.card) (ℓ := ℓ)
        hreg₁.1 hreg₁.2.1 hreg₁.2.2 (hGenLin.good _ hgood₂).1 (hGenLin.good _ hgood₂).2
  have hA10 : MeasureTheory.Integrable (fun x : Work.BoseDict.Xn S.card =>
      (starRingEnd ℂ) (Work.BoseDict.boxRealise e S.card Ψ₂ x)
        * (Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
            (id : (Work.BoseDict.Xn S.card → ℂ) → (Work.BoseDict.Xn S.card → ℂ))
            f g T_NH PHs E gHat0 (Work.BoseDict.boxRealise e S.card Ψ₁)) x) := by
    simpa only [starRingEnd_apply] using
      Work.BoseBoxFock.integrable_star_mul_of_box_support (n := S.card) (ℓ := ℓ)
        hreg₂.1 hreg₂.2.1 hreg₂.2.2 (hGenLin.good _ hgood₁).1 (hGenLin.good _ hgood₁).2
  have hA11 : MeasureTheory.Integrable (fun x : Work.BoseDict.Xn S.card =>
      (starRingEnd ℂ) (Work.BoseDict.boxRealise e S.card Ψ₂ x)
        * (Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
            (id : (Work.BoseDict.Xn S.card → ℂ) → (Work.BoseDict.Xn S.card → ℂ))
            f g T_NH PHs E gHat0 (Work.BoseDict.boxRealise e S.card Ψ₂)) x) := by
    simpa only [starRingEnd_apply] using
      Work.BoseBoxFock.integrable_star_mul_of_box_support (n := S.card) (ℓ := ℓ)
        hreg₂.1 hreg₂.2.1 hreg₂.2.2 (hGenLin.good _ hgood₂).1 (hGenLin.good _ hgood₂).2
  have hN00 : MeasureTheory.Integrable (fun x : Work.BoseDict.Xn S.card =>
      (starRingEnd ℂ) (Work.BoseDict.boxRealise e S.card Ψ₁ x)
        * Work.BoseDict.boxRealise e S.card Ψ₁ x) := by
    simpa only [starRingEnd_apply] using
      Work.BoseBoxFock.integrable_star_mul_of_box_support (n := S.card) (ℓ := ℓ)
        hreg₁.1 hreg₁.2.1 hreg₁.2.2 hreg₁.1 hreg₁.2.1
  have hN01 : MeasureTheory.Integrable (fun x : Work.BoseDict.Xn S.card =>
      (starRingEnd ℂ) (Work.BoseDict.boxRealise e S.card Ψ₁ x)
        * Work.BoseDict.boxRealise e S.card Ψ₂ x) := by
    simpa only [starRingEnd_apply] using
      Work.BoseBoxFock.integrable_star_mul_of_box_support (n := S.card) (ℓ := ℓ)
        hreg₁.1 hreg₁.2.1 hreg₁.2.2 hreg₂.1 hreg₂.2.1
  have hN10 : MeasureTheory.Integrable (fun x : Work.BoseDict.Xn S.card =>
      (starRingEnd ℂ) (Work.BoseDict.boxRealise e S.card Ψ₂ x)
        * Work.BoseDict.boxRealise e S.card Ψ₁ x) := by
    simpa only [starRingEnd_apply] using
      Work.BoseBoxFock.integrable_star_mul_of_box_support (n := S.card) (ℓ := ℓ)
        hreg₂.1 hreg₂.2.1 hreg₂.2.2 hreg₁.1 hreg₁.2.1
  have hN11 : MeasureTheory.Integrable (fun x : Work.BoseDict.Xn S.card =>
      (starRingEnd ℂ) (Work.BoseDict.boxRealise e S.card Ψ₂ x)
        * Work.BoseDict.boxRealise e S.card Ψ₂ x) := by
    simpa only [starRingEnd_apply] using
      Work.BoseBoxFock.integrable_star_mul_of_box_support (n := S.card) (ℓ := ℓ)
        hreg₂.1 hreg₂.2.1 hreg₂.2.2 hreg₂.1 hreg₂.2.1
  have hAinteg : ∀ i j : Fin 2, MeasureTheory.Integrable
      (fun x : Work.BoseDict.Xn S.card =>
        (starRingEnd ℂ) (![Work.BoseDict.boxRealise e S.card Ψ₁,
            Work.BoseDict.boxRealise e S.card Ψ₂] i x)
          * (Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
              (id : (Work.BoseDict.Xn S.card → ℂ) → (Work.BoseDict.Xn S.card → ℂ))
              f g T_NH PHs E gHat0 (![Work.BoseDict.boxRealise e S.card Ψ₁,
                Work.BoseDict.boxRealise e S.card Ψ₂] j)) x) := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact hA00
    · exact hA01
    · exact hA10
    · exact hA11
  have hNinteg : ∀ i j : Fin 2, MeasureTheory.Integrable
      (fun x : Work.BoseDict.Xn S.card =>
        (starRingEnd ℂ) (![Work.BoseDict.boxRealise e S.card Ψ₁,
            Work.BoseDict.boxRealise e S.card Ψ₂] i x)
          * ![Work.BoseDict.boxRealise e S.card Ψ₁,
              Work.BoseDict.boxRealise e S.card Ψ₂] j x) := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact hN00
    · exact hN01
    · exact hN10
    · exact hN11
  -- ## step 9: the two pairings
  have hν : 0 < (Work.BoseDict.cIPn S.card
        (Work.BoseDict.boxRealise e S.card Ψ₁ + Complex.I • Work.BoseDict.boxRealise e S.card Ψ₂)
        (Work.BoseDict.boxRealise e S.card Ψ₁
          + Complex.I • Work.BoseDict.boxRealise e S.card Ψ₂)).re := by
    rw [hreal, Work.BoseBoxFock.cIPn_sliceF_self_eq e S Φc y]
    exact hmass₀
  have hh : (Work.BoseDict.cIPn S.card
        (Work.BoseDict.boxRealise e S.card Ψ₁ + Complex.I • Work.BoseDict.boxRealise e S.card Ψ₂)
        (Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
          (id : (Work.BoseDict.Xn S.card → ℂ) → (Work.BoseDict.Xn S.card → ℂ))
          f g T_NH PHs E gHat0
          (Work.BoseDict.boxRealise e S.card Ψ₁
            + Complex.I • Work.BoseDict.boxRealise e S.card Ψ₂))).re
      ≤ c * (Work.BoseDict.cIPn S.card
        (Work.BoseDict.boxRealise e S.card Ψ₁
          + Complex.I • Work.BoseDict.boxRealise e S.card Ψ₂)
        (Work.BoseDict.boxRealise e S.card Ψ₁
          + Complex.I • Work.BoseDict.boxRealise e S.card Ψ₂)).re := by
    have hintAA : MeasureTheory.Integrable (fun x : Work.BoseDict.Xn S.card =>
        (starRingEnd ℂ) (Work.BoseBoxFock.sliceF e S Φc y x)
          * (Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
              (id : (Work.BoseDict.Xn S.card → ℂ) → (Work.BoseDict.Xn S.card → ℂ))
              f g T_NH PHs E gHat0 (Work.BoseBoxFock.sliceF e S Φc y)) x) := by
      rw [← hreal, hAF]
      have hcomb : MeasureTheory.Integrable (fun x : Work.BoseDict.Xn S.card =>
          (starRingEnd ℂ) (Work.BoseDict.boxRealise e S.card Ψ₁ x)
              * (Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
                  (id : (Work.BoseDict.Xn S.card → ℂ) → (Work.BoseDict.Xn S.card → ℂ))
                  f g T_NH PHs E gHat0 (Work.BoseDict.boxRealise e S.card Ψ₁)) x
            + (starRingEnd ℂ) (Work.BoseDict.boxRealise e S.card Ψ₂ x)
              * (Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
                  (id : (Work.BoseDict.Xn S.card → ℂ) → (Work.BoseDict.Xn S.card → ℂ))
                  f g T_NH PHs E gHat0 (Work.BoseDict.boxRealise e S.card Ψ₂)) x
            + Complex.I * ((starRingEnd ℂ) (Work.BoseDict.boxRealise e S.card Ψ₁ x)
                * (Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
                    (id : (Work.BoseDict.Xn S.card → ℂ) → (Work.BoseDict.Xn S.card → ℂ))
                    f g T_NH PHs E gHat0 (Work.BoseDict.boxRealise e S.card Ψ₂)) x
              - (starRingEnd ℂ) (Work.BoseDict.boxRealise e S.card Ψ₂ x)
                * (Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
                    (id : (Work.BoseDict.Xn S.card → ℂ) → (Work.BoseDict.Xn S.card → ℂ))
                    f g T_NH PHs E gHat0 (Work.BoseDict.boxRealise e S.card Ψ₁)) x)) :=
        ((hA00.add hA11).add ((hA01.sub hA10).const_mul Complex.I))
      refine hcomb.congr ?_
      refine Filter.Eventually.of_forall (fun x => ?_)
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact (Work.BoseBoxFock.conj_add_I_mul (Work.BoseDict.boxRealise e S.card Ψ₁ x)
        (Work.BoseDict.boxRealise e S.card Ψ₂ x)
        ((Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
            (id : (Work.BoseDict.Xn S.card → ℂ) → (Work.BoseDict.Xn S.card → ℂ))
            f g T_NH PHs E gHat0 (Work.BoseDict.boxRealise e S.card Ψ₁)) x)
        ((Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
            (id : (Work.BoseDict.Xn S.card → ℂ) → (Work.BoseDict.Xn S.card → ℂ))
            f g T_NH PHs E gHat0 (Work.BoseDict.boxRealise e S.card Ψ₂)) x)).symm
    rw [hreal, Work.BoseBoxFock.cIPn_sliceF_self_eq e S Φc y]
    have hstep1 : (∫ x : Work.BoseDict.Xn S.card,
          ((starRingEnd ℂ) (Work.BoseBoxFock.sliceF e S Φc y x)
            * (Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
                (id : (Work.BoseDict.Xn S.card → ℂ) → (Work.BoseDict.Xn S.card → ℂ))
                f g T_NH PHs E gHat0 (Work.BoseBoxFock.sliceF e S Φc y)) x).re)
        = ∫ x : Work.BoseDict.Xn S.card,
          (star (Work.BoseBoxFock.sectorSlice e S Φc y (Work.BoseBoxFock.sliceEquiv S x))
            * (Work.BoseBoxFock.AVgen (fun T => Work.BoseBoxFock.slotSumSub e T S) (fun Y => Y)
                f g T_NH PHs E gHat0 (Work.BoseBoxFock.sectorSlice e S Φc y))
                (Work.BoseBoxFock.sliceEquiv S x)).re := by
      have hslicefun : Work.BoseBoxFock.sliceF e S Φc y
          = fun w => Work.BoseBoxFock.sectorSlice e S Φc y (Work.BoseBoxFock.sliceEquiv S w) := by
        funext w
        rw [Work.BoseBoxFock.sliceEquiv_coe]
        rfl
      refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      beta_reduce
      have hslice : Work.BoseBoxFock.sliceF e S Φc y x
          = Work.BoseBoxFock.sectorSlice e S Φc y (Work.BoseBoxFock.sliceEquiv S x) := by
        rw [Work.BoseBoxFock.sliceEquiv_coe]
        rfl
      rw [starRingEnd_apply, hslice, hslicefun]
      rw [Work.BoseBoxFock.AVgenDictGen.AVgen_slice (e := e) f g T_NH PHs E gHat0 S
        (Work.BoseBoxFock.sectorSlice e S Φc y) x]
    have hstep2 : (∫ x : Work.BoseDict.Xn S.card,
          (star (Work.BoseBoxFock.sectorSlice e S Φc y (Work.BoseBoxFock.sliceEquiv S x))
            * (Work.BoseBoxFock.AVgen (fun T => Work.BoseBoxFock.slotSumSub e T S) (fun Y => Y)
                f g T_NH PHs E gHat0 (Work.BoseBoxFock.sectorSlice e S Φc y))
                (Work.BoseBoxFock.sliceEquiv S x)).re)
        = ∫ u : {i // i ∈ S} → Ω,
          (star (Work.BoseBoxFock.sectorSlice e S Φc y u)
            * (Work.BoseBoxFock.AVgen (fun T => Work.BoseBoxFock.slotSumSub e T S) (fun Y => Y)
                f g T_NH PHs E gHat0 (Work.BoseBoxFock.sectorSlice e S Φc y)) u).re :=
      MeasurePreserving.integral_comp' (f := Work.BoseBoxFock.sliceEquiv S)
        (Work.BoseBoxFock.measurePreserving_sliceEquiv S)
        (fun u : {i // i ∈ S} → Ω =>
          (star (Work.BoseBoxFock.sectorSlice e S Φc y u)
            * (Work.BoseBoxFock.AVgen (fun T => Work.BoseBoxFock.slotSumSub e T S) (fun Y => Y)
                f g T_NH PHs E gHat0 (Work.BoseBoxFock.sectorSlice e S Φc y)) u).re)
    rw [Work.BoseDict.cIPn, Work.BoseBoxFock.re_integral hintAA, hstep1, hstep2]
    exact hle₀
  -- ## step 10: the binary selection
  rcases Work.BoseBoxFock.exists_binary_le_apply e
      (Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
        (id : (Work.BoseDict.Xn S.card → ℂ) → (Work.BoseDict.Xn S.card → ℂ))
        f g T_NH PHs E gHat0)
      (Work.BoseBoxFock.H2ndF f g (Work.BoseB4.dGamma m T_NH) PHs E gHat0)
      Ψ₁ Ψ₂ hAF hdict hiso hdeg₁ hdeg₂ hAinteg hNinteg c hν hh with
    ⟨hpos₁, hle₁⟩ | ⟨hpos₂, hle₂⟩
  · refine ⟨Ψ₁, ?_, hw₁, hle₁⟩
    intro hzero
    rw [hzero] at hpos₁
    simp at hpos₁
  · refine ⟨Ψ₂, ?_, hw₂, hle₂⟩
    intro hzero
    rw [hzero] at hpos₂
    simp at hpos₂


end Work.MB
