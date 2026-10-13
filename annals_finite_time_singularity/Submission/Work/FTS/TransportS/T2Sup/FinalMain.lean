/-
Copyright: work module for the Elgindi finite-time singularity project.

# `TransportS/T2Sup/FinalMain`: the weighted per-slot estimate (assembly)

This module assembles the weighted per-slot estimate `SlotAbsProp` (`Final.SlotAbsProp`, the
input of the reduction `Final.T2Slot_of_slotAbs` to the frozen `T2Slot`) from

* the Leibniz expansion `FinalAux.Ssum_eq_leibniz` and the three-way split
  `FinalAux.Ssum_eq_Smain_Srest_Sdel`;
* `smainBound` (the `f · D_z(mixed b a g) · mixed b a g` summand: the radial integration by
  parts `topSlotBound` when `a + b = 4`, the pointwise slot domination otherwise);
* `srestBound` (the remaining Leibniz summands, pointwise dominated by `Maj1`);
* `hDel : DelicateProp` for the `(0,3)` summand at the slot `(1,3)`, `q = γ`.

All declarations here rest on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.TransportS.T2Sup.Final
import Submission.Work.FTS.TransportS.T2Sup.FinalAux
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.TransportS.T2Sup.GenSlot
import Submission.Work.FTS.TransportS.T2Sup.absIntegralAddLe
import Submission.Work.FTS.TransportS.T2Sup.integrableOnSliceDelicate
import Submission.Work.FTS.TransportS.T2Sup.delicateMargInt
import Submission.Work.FTS.TransportS.T2Sup.delicateBound
import Submission.Work.FTS.TransportS.T2Sup.Main
import Submission.Work.FTS.TransportS.T2Sup.smainBound
import Submission.Work.FTS.TransportS.T2Sup.srestBound
import Submission.Work.FTS.TransportS.t2SupF

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS.T2Sup

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Work.FTS.TransportS.SlotT2

/-- The delicate marginal: the `θ`-integral of `canonW q · |Sdel| · |Y|`. -/
def DelMarg (f g : ℝ → ℝ → ℝ) (a b : ℕ) (q : ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, canonW q z θ * |Sdel f g a b z θ| * |Work.Spaces.mixed b a g z θ|

/-- The majorant of the `(Srest + Sdel)` marginal. -/
def Marg (α : ℝ) (f g : ℝ → ℝ → ℝ) (a b : ℕ) (q Mf MK Mg : ℝ) (z : ℝ) : ℝ :=
  6400 * (∫ θ in Work.Spaces.Iθ, Maj1 α f g Mf MK Mg z θ) + DelMarg f g a b q z

theorem Marg_nonneg {α Mf MK Mg : ℝ} {f g : ℝ → ℝ → ℝ} {a b : ℕ} {q : ℝ} {z : ℝ}
    (hM : 0 ≤ Mf + MK) (hMg : 0 ≤ Mg) : 0 ≤ Marg α f g a b q Mf MK Mg z := by
  rw [Marg, DelMarg]
  refine add_nonneg (mul_nonneg (by norm_num) ?_) ?_
  · exact MeasureTheory.setIntegral_nonneg measurableSet_Icc fun θ hθ =>
      Maj1_nonneg hM hMg z θ
  · exact MeasureTheory.setIntegral_nonneg measurableSet_Icc fun θ hθ =>
      mul_nonneg (mul_nonneg (canonW_nonneg hθ) (abs_nonneg _)) (abs_nonneg _)

/-! ## The pointwise sup data -/

theorem supData {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {f g : ℝ → ℝ → ℝ} (hsf : Work.FTS.TransportS.T2SF α f) (hsg : Work.FTS.TransportS.T2SG α g)
    {Cs Cl Cg : ℝ}
    (hsupdz : ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      ∀ b : ℕ, b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
        |Work.Spaces.DzIter b f z θ| ≤ Cs / Real.sqrt (Work.Spaces.gam α - 1)
          * Work.FTS.Nonlin.Xn α f)
    (hflat : ∀ (f : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.SmoothOpen f → ∀ (K : ℝ), 0 ≤ K →
      (∀ b i : ℕ, b + i ≤ 1 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
        |Work.Spaces.mixed b i (Work.Spaces.pth f) z θ| ≤ K) →
      ∀ a b : ℕ, 1 ≤ a → a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
        |Work.Spaces.mixed b a f z θ| ≤ Cl * Real.sin (2 * θ) * K)
    (hsupQ : ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (b a : ℕ), 0 < α → α ≤ 1 → a + b ≤ 2 →
      Work.FTS.LocData.SmoothQuad f → Work.Spaces.DecayAll 4 f → Work.Spaces.HkMem α 4 f →
      ∀ z ∈ Set.Ioi 0, ∀ θ ∈ Set.Ioo 0 (π / 2),
        |Work.Spaces.mixed b a f z θ| ≤ Cg / Real.sqrt (Work.Spaces.gam α - 1)
          * Work.Spaces.HkNorm α 4 f) :
    (∀ j : ℕ, j ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
        |Work.Spaces.DzIter j f z θ|
          ≤ Cs / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α f) ∧
    (∀ j i : ℕ, 1 ≤ i → i + j ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
        |Work.Spaces.mixed j i f z θ|
          ≤ (Cl * Work.FTS.VocabO.CoefTh 1 f) * Real.sin (2 * θ)) ∧
    (∀ j i : ℕ, i + j ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
        |Work.Spaces.mixed j i g z θ|
          ≤ Cg / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α g) := by
  have hFsm : Work.FTS.EllipticEst.SmoothOpen f := hsf.1
  have hmf : Work.Spaces.HkMem α 4 f := hsf.2.1
  have hGq : Work.FTS.LocData.SmoothQuad g := hsg.1.1
  have hmg : Work.Spaces.HkMem α 4 g := hsg.1.2.1
  have hmg5 : Work.Spaces.HkMem α 5 g := hsg.2.1
  have hdec : Work.Spaces.DecayAll 4 g := hsg.2.2
  refine ⟨fun j hj z θ hz hθ hθ2 => hsupdz α f hα hα1 hFsm hmf j hj z θ hz hθ hθ2,
    ?_, ?_⟩
  · intro j i hi hij z θ hz hθ hθ2
    have hK : ∀ b i' : ℕ, b + i' ≤ 1 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
        |Work.Spaces.mixed b i' (Work.Spaces.pth f) z θ| ≤ Work.FTS.VocabO.CoefTh 1 f :=
      fun b i' hbi z θ hz hθ hθ2 => Work.FTS.TransportS.t2SupF_pth_le_coefTh hsf hbi hz hθ hθ2
    have h := hflat f hFsm (Work.FTS.VocabO.CoefTh 1 f) (coefTh_nonneg 1 f) hK i j hi hij
      z θ hz hθ hθ2
    calc |Work.Spaces.mixed j i f z θ|
        ≤ Cl * Real.sin (2 * θ) * Work.FTS.VocabO.CoefTh 1 f := h
      _ = (Cl * Work.FTS.VocabO.CoefTh 1 f) * Real.sin (2 * θ) := by ring
  · intro j i hij z θ hz hθ hθ2
    exact hsupQ α g j i hα hα1 hij hGq hdec hmg z hz θ ⟨hθ, hθ2⟩



/-! ## The `(0,3)` summand at exponent `q ≤ η` -/

/-- **The `(0,3)` summand is dominated by `Maj1`.**  For `q ≤ η` the pure `f`-slot `D_z³f` is a
canonical slot and the middle `g`-slot `mixed (b-2) a g` has order `≤ 2`, so `termPair_nd'`
applies to the pair `(a1,b1) = (0,3)` (whenever that pair is present; otherwise the summand
vanishes because `C(b,3) = 0`). -/
theorem canonW_Sdel_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {f g : ℝ → ℝ → ℝ} {a b : ℕ} {q Mf MK Mg : ℝ}
    (hMf : 0 ≤ Mf) (hMK : 0 ≤ MK) (hMg : 0 ≤ Mg)
    (hqnn : 0 ≤ q) (hab : a + b ≤ 4) (hq0 : a = 0 → q ≤ Work.Spaces.eta)
    (hqγ : q ≤ Work.Spaces.gam α) (hqη : q ≤ Work.Spaces.eta)
    (hFsup : ∀ j : ℕ, j ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.DzIter j f z θ| ≤ Mf)
    (hFσ : ∀ j i : ℕ, 1 ≤ i → i + j ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed j i f z θ| ≤ MK * Real.sin (2 * θ))
    (hGsup : ∀ j i : ℕ, i + j ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed j i g z θ| ≤ Mg) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      canonW q z θ * |Sdel f g a b z θ| * |Work.Spaces.mixed b a g z θ|
        ≤ 16 * Maj1 α f g Mf MK Mg z θ := by
  intro z θ hz hθ hθ2
  have hMaj : 0 ≤ Maj1 α f g Mf MK Mg z θ := Maj1_nonneg (by linarith) hMg z θ
  by_cases hb3 : 3 ≤ b
  · -- the pair `(0,3)` is present and not delicate (`q ≤ η < γ`)
    have hnd : ¬ ((0 : ℕ) = 0 ∧ (3 : ℕ) = 3 ∧ q = Work.Spaces.gam α) := by
      rintro ⟨-, -, h⟩
      exact absurd (h ▸ hqη : Work.Spaces.gam α ≤ Work.Spaces.eta)
        (not_le.mpr (eta_lt_gam_of_pos hα))
    have hp := termPair_nd' (α := α) hα hα1 (f := f) (g := g) (a := a) (b := b) (a1 := 0)
      (b1 := 3) (q := q) (Mf := Mf) (MK := MK) (Mg := Mg) hMf hMK hMg hqnn hab
      (Nat.zero_le a) hb3 (by omega) hq0 hqγ (Or.inl hqη) hnd hFsup hFσ hGsup z θ hz hθ hθ2
    have hbridge : canonW q z θ * |Work.Spaces.mixed 3 0 f z θ|
        * |Work.Spaces.mixed (b - 2) a g z θ| * |Work.Spaces.mixed b a g z θ|
        = canonW q z θ * |Work.Spaces.mixed 3 0 f z θ|
          * |Work.Spaces.mixed (b + 1 - 3) (a - 0) g z θ| * |Work.Spaces.mixed b a g z θ| := by
      rw [show b - 2 = b + 1 - 3 by omega, Nat.sub_zero]
    have hkey : canonW q z θ * |Work.Spaces.mixed 3 0 f z θ|
        * |Work.Spaces.mixed (b - 2) a g z θ| * |Work.Spaces.mixed b a g z θ|
        ≤ Maj1 α f g Mf MK Mg z θ := by
      rw [hbridge]
      simpa only [Maj1, Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right] using hp
    have hpow : (b.choose 3 : ℝ) ≤ 16 := by
      have h1 : b.choose 3 ≤ 2 ^ b := Nat.choose_le_two_pow b 3
      have h2 : 2 ^ b ≤ 16 := by
        calc 2 ^ b ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 16 := by norm_num
      exact_mod_cast le_trans h1 h2
    have hkey' : canonW q z θ * |Sdel f g a b z θ|
        = (b.choose 3 : ℝ) * (canonW q z θ * |Work.Spaces.mixed 3 0 f z θ|
            * |Work.Spaces.mixed (b - 2) a g z θ|) := by
      rw [Sdel, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (b.choose 3)), abs_mul]
      ring
    calc canonW q z θ * |Sdel f g a b z θ| * |Work.Spaces.mixed b a g z θ|
        = (b.choose 3 : ℝ) * (canonW q z θ * |Work.Spaces.mixed 3 0 f z θ|
            * |Work.Spaces.mixed (b - 2) a g z θ| * |Work.Spaces.mixed b a g z θ|) := by
          rw [hkey']; ring
      _ ≤ (b.choose 3 : ℝ) * Maj1 α f g Mf MK Mg z θ :=
          mul_le_mul_of_nonneg_left hkey (Nat.cast_nonneg _)
      _ ≤ 16 * Maj1 α f g Mf MK Mg z θ := mul_le_mul_of_nonneg_right hpow hMaj
  · -- `b < 3`: the summand vanishes
    have hzero : Sdel f g a b z θ = 0 := by
      rw [Sdel, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
    rw [hzero, abs_zero, mul_zero, zero_mul]
    exact mul_nonneg (by norm_num) hMaj

/-! ## The pointwise domination of the main summand -/

theorem canonW_Smain_le {α : ℝ} (hα : 0 < α)
    {f g : ℝ → ℝ → ℝ} {a b : ℕ} {q Mf : ℝ} (hMf : 0 ≤ Mf)
    (hqnn : 0 ≤ q) (hab : a + b ≤ 4) (hq0 : a = 0 → q ≤ Work.Spaces.eta)
    (hqγ : q ≤ Work.Spaces.gam α)
    (hf : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → |f z θ| ≤ Mf) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      canonW q z θ * |Smain f g a b z θ| * |Work.Spaces.mixed b a g z θ|
        ≤ Mf * Work.Spaces.HkIntegrand α 5 g z θ := by
  intro z θ hz hθ hθ2
  have hHI : 0 ≤ Work.Spaces.HkIntegrand α 5 g z θ := Work.Spaces.HkIntegrand_nonneg α 5 g z θ
  -- the two order-5 slots
  have hG5 : canonW q z θ * (Work.Spaces.mixed (b + 1) a g z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 5 g z θ := by
    rcases eq_or_ne a 0 with ha | ha
    · subst ha
      simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right] using
        canonW_z_slot_le_gen (α := α) 5 hqnn (hq0 rfl) g ⟨hθ, hθ2⟩ (b + 1) (by omega)
    · exact canonW_mixed_slot_le_gen hα 5 hqnn hqγ g ⟨hθ, hθ2⟩ (b + 1) a (by omega) (by omega)
  have hY5 : canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 5 g z θ := by
    rcases eq_or_ne a 0 with ha | ha
    · subst ha
      simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right] using
        canonW_z_slot_le_gen (α := α) 5 hqnn (hq0 rfl) g ⟨hθ, hθ2⟩ b (by omega)
    · exact canonW_mixed_slot_le_gen hα 5 hqnn hqγ g ⟨hθ, hθ2⟩ b a (by omega) (by omega)
  have hAM : |Work.Spaces.mixed (b + 1) a g z θ| * |Work.Spaces.mixed b a g z θ|
      ≤ ((Work.Spaces.mixed (b + 1) a g z θ) ^ 2 + (Work.Spaces.mixed b a g z θ) ^ 2) / 2 := by
    have h := Work.FTS.TransportS.T3BadAux.abs_mul_le_half_sq_add
      (Work.Spaces.mixed (b + 1) a g z θ) (Work.Spaces.mixed b a g z θ)
    rwa [abs_mul] at h
  have hcw : 0 ≤ canonW q z θ := canonW_nonneg ⟨hθ.le, hθ2.le⟩
  have h1 : canonW q z θ * |Smain f g a b z θ| * |Work.Spaces.mixed b a g z θ|
      = |f z θ| * (canonW q z θ * (|Work.Spaces.mixed (b + 1) a g z θ|
          * |Work.Spaces.mixed b a g z θ|)) := by
    rw [Smain, abs_mul]
    ring
  have h2 : canonW q z θ * (|Work.Spaces.mixed (b + 1) a g z θ|
      * |Work.Spaces.mixed b a g z θ|) ≤ Work.Spaces.HkIntegrand α 5 g z θ := by
    calc canonW q z θ * (|Work.Spaces.mixed (b + 1) a g z θ|
          * |Work.Spaces.mixed b a g z θ|)
        ≤ canonW q z θ * (((Work.Spaces.mixed (b + 1) a g z θ) ^ 2
            + (Work.Spaces.mixed b a g z θ) ^ 2) / 2) :=
          mul_le_mul_of_nonneg_left hAM hcw
      _ = (1 / 2) * (canonW q z θ * (Work.Spaces.mixed (b + 1) a g z θ) ^ 2)
          + (1 / 2) * (canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2) := by ring
      _ ≤ (1 / 2) * Work.Spaces.HkIntegrand α 5 g z θ
          + (1 / 2) * Work.Spaces.HkIntegrand α 5 g z θ := by linarith
      _ = Work.Spaces.HkIntegrand α 5 g z θ := by ring
  calc canonW q z θ * |Smain f g a b z θ| * |Work.Spaces.mixed b a g z θ|
      = |f z θ| * (canonW q z θ * (|Work.Spaces.mixed (b + 1) a g z θ|
          * |Work.Spaces.mixed b a g z θ|)) := h1
    _ ≤ Mf * Work.Spaces.HkIntegrand α 5 g z θ :=
        mul_le_mul (hf z θ hz hθ hθ2) h2
          (mul_nonneg hcw (mul_nonneg (abs_nonneg _) (abs_nonneg _))) hMf

/-! ## The `DelMarg` marginal -/

/-- `∫_θ Maj1 ≤ (Mf+MK)·∫_θ HI_g + Mg·√(∫_θ HI_f)·√(∫_θ HI_g)` (Cauchy–Schwarz in `θ`). -/
theorem integral_Maj1_le {α Mf MK Mg : ℝ} {f g : ℝ → ℝ → ℝ}
    (hmf : Work.Spaces.HkMem α 4 f) (hmg : Work.Spaces.HkMem α 4 g) (hMg : 0 ≤ Mg) {z : ℝ}
    (hz : z ∈ Work.Spaces.Iz) :
    (∫ θ in Work.Spaces.Iθ, Maj1 α f g Mf MK Mg z θ)
      ≤ (Mf + MK) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
        + Mg * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)) := by
  have hIθm : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hFf : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.HkIntegrand α 4 f z θ) Work.Spaces.Iθ := hmf.1 z hz
  have hGg : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.HkIntegrand α 4 g z θ) Work.Spaces.Iθ := hmg.1 z hz
  have hprod : MeasureTheory.IntegrableOn
      (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
        * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ)) Work.Spaces.Iθ :=
    integrable_sqrt_mul_sqrt_slice hFf hGg
      (fun θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ)
      (fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g z θ)
  have h1 : (∫ θ in Work.Spaces.Iθ, Maj1 α f g Mf MK Mg z θ)
      = (Mf + MK) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
        + Mg * (∫ θ in Work.Spaces.Iθ, Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
            * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ)) := by
    simp only [Maj1]
    rw [MeasureTheory.integral_add ((hmg.1 z hz).const_mul _) (hprod.const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [h1]
  refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hMg)
  exact cs_sqrt_le hFf hGg
    (fun θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ)
    (fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g z θ)

end Work.FTS.TransportS.T2Sup
