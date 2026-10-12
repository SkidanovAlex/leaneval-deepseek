import Mathlib.CategoryTheory.Countable
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.slotProj_idem_and_comm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.slotProj_adjoint` — the slot projection is self-adjoint

The slot projection `slotProj e S Φ` integrates the slots of `S` against the projection kernel
`PV e` (`PV e x y = Σ l, e l x * star (e l y)`).  With orthonormal modes `e` it is the orthogonal
projection onto `V^{⊗|S|}` on those slots, hence self-adjoint:

`∫ x, star (slotProj e S Φ x) * Ψ x = ∫ x, star (Φ x) * slotProj e S Ψ x`.

The proof is a change of variables.  Writing `u(x, z) = Function.updateFinset x S z` and
`K(x,z) = ∏_{i ∈ S} PV e (x_{i}) (z_{i})`, the left-hand side is the integral over
`(Fin n → Ω) × (↥S → Ω)` of
`star (K p) * star (Φ (u p)) * Ψ p.1`, while the right-hand side is the integral of
`star (Φ p.1) * K p * Ψ (u p)`.  The two integrands are exchanged by the measure preserving
involution `T (x,z) = (u (x,z), x|_S)` which swaps the coordinates of `S` with the fibre
coordinates; it is conjugated (through the product/`⊕` identification
`MeasurableEquiv.sumPiEquivProdPi`) to the permutation `slotPerm S` of the index type
`Fin n ⊕ ↥S` that swaps the two summands, whose measure preservation is
`volume_measurePreserving_piCongrLeft`.  The pointwise identity `G (T p) = H p` uses
`star (PV e y x) = PV e x y` (`star_PV_comm`) and `u (u(x,z), x|_S) = x`.
-/

noncomputable section

namespace Work.BoseBoxFock

open MeasureTheory

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

-- `horth` (orthonormality of the modes) is part of the requested statement but is *not* needed:
-- the kernel `PV e` is self-adjoint (`star_PV_comm`) for arbitrary modes, and the change of
-- variables that proves the adjointness identity never uses the orthonormality.
set_option linter.unusedVariables false

/-! ## 1. Small integral/star helpers -/

theorem slotStar_integral {X : Type*} [MeasurableSpace X] (μ : Measure X) (g : X → ℂ) :
    star (∫ v, g v ∂μ) = ∫ v, star (g v) ∂μ := by
  simpa [Complex.conjLIE_apply] using
    (LinearIsometry.integral_comp_comm Complex.conjLIE.toLinearIsometry g).symm

theorem slotStar_prod_finset {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    star (∏ i ∈ s, f i) = ∏ i ∈ s, star (f i) :=
  map_prod (starRingEnd ℂ) f s

/-! ## 2. The permutation of the index type and its measure preservation -/

/-- The permutation of the index type `Fin n ⊕ ↥S` which swaps the two summands over `S` and
fixes `Sum.inl i` for `i ∉ S`. -/
def slotSwapFun {n : ℕ} (S : Finset (Fin n)) :
    Fin n ⊕ {i : Fin n // i ∈ S} → Fin n ⊕ {i : Fin n // i ∈ S}
  | Sum.inl i => if h : i ∈ S then Sum.inr ⟨i, h⟩ else Sum.inl i
  | Sum.inr j => Sum.inl j.1

theorem slotSwapFun_invol {n : ℕ} (S : Finset (Fin n)) (q : Fin n ⊕ {i : Fin n // i ∈ S}) :
    slotSwapFun S (slotSwapFun S q) = q := by
  rcases q with i | j
  · by_cases h : i ∈ S
    · simp only [slotSwapFun, dif_pos h]
    · simp only [slotSwapFun, dif_neg h]
  · simp only [slotSwapFun, dif_pos j.2]

/-- The swap as an equivalence. -/
def slotSwapEquiv {n : ℕ} (S : Finset (Fin n)) :
    (Fin n ⊕ {i : Fin n // i ∈ S}) ≃ (Fin n ⊕ {i : Fin n // i ∈ S}) where
  toFun := slotSwapFun S
  invFun := slotSwapFun S
  left_inv := slotSwapFun_invol S
  right_inv := slotSwapFun_invol S

@[simp] theorem slotSwapEquiv_apply {n : ℕ} (S : Finset (Fin n))
    (q : Fin n ⊕ {i : Fin n // i ∈ S}) : slotSwapEquiv S q = slotSwapFun S q := rfl

/-- The induced (measure preserving) permutation of the configuration space. -/
def slotPerm {n : ℕ} (S : Finset (Fin n)) :
    (Fin n ⊕ {i : Fin n // i ∈ S} → Ω) ≃ᵐ (Fin n ⊕ {i : Fin n // i ∈ S} → Ω) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin n ⊕ {i : Fin n // i ∈ S} => Ω) (slotSwapEquiv S).symm

theorem slotPerm_apply {n : ℕ} (S : Finset (Fin n))
    (γ : Fin n ⊕ {i : Fin n // i ∈ S} → Ω) (q : Fin n ⊕ {i : Fin n // i ∈ S}) :
    slotPerm S γ q = γ (slotSwapEquiv S q) := by
  have h := MeasurableEquiv.piCongrLeft_apply_apply (e := (slotSwapEquiv S).symm)
    (β := fun _ : Fin n ⊕ {i : Fin n // i ∈ S} => Ω) γ (slotSwapEquiv S q)
  rwa [Equiv.symm_apply_apply] at h

theorem measurePreserving_slotPerm {n : ℕ} (S : Finset (Fin n)) :
    MeasurePreserving (slotPerm S) (volume : Measure (Fin n ⊕ {i : Fin n // i ∈ S} → Ω))
      (volume : Measure (Fin n ⊕ {i : Fin n // i ∈ S} → Ω)) :=
  volume_measurePreserving_piCongrLeft (fun _ : Fin n ⊕ {i : Fin n // i ∈ S} => Ω)
    (slotSwapEquiv S).symm

/-- The componentwise description of `slotPerm` on the configuration slots. -/
theorem slotPerm_apply_inl {n : ℕ} (S : Finset (Fin n))
    (γ : Fin n ⊕ {i : Fin n // i ∈ S} → Ω) :
    (fun i : Fin n => slotPerm S γ (Sum.inl i)) =
      Function.updateFinset (fun i : Fin n => γ (Sum.inl i)) S
        (fun j : {i : Fin n // i ∈ S} => γ (Sum.inr j)) := by
  funext i
  rw [slotPerm_apply, slotSwapEquiv_apply, slotSwapFun, Function.updateFinset_def]
  by_cases h : i ∈ S <;> simp [h]

/-- The componentwise description of `slotPerm` on the fibre slots. -/
theorem slotPerm_apply_inr {n : ℕ} (S : Finset (Fin n))
    (γ : Fin n ⊕ {i : Fin n // i ∈ S} → Ω) :
    (fun j : {i : Fin n // i ∈ S} => slotPerm S γ (Sum.inr j)) =
      (fun j : {i : Fin n // i ∈ S} => γ (Sum.inl j.1)) := by
  funext j
  rw [slotPerm_apply, slotSwapEquiv_apply, slotSwapFun]

/-! ## 3. The swap of the `S`-slots with the fibre variables on the product space -/

/-- The swap of the `S`-slots with the fibre variables, as a measure preserving automorphism of
the product space `(Fin n → Ω) × (↥S → Ω)`. -/
def slotSwapMeas {n : ℕ} (S : Finset (Fin n)) :
    ((Fin n → Ω) × ({i : Fin n // i ∈ S} → Ω)) ≃ᵐ
      ((Fin n → Ω) × ({i : Fin n // i ∈ S} → Ω)) :=
  ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ {i : Fin n // i ∈ S} => Ω)).symm.trans
      (slotPerm S)).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ {i : Fin n // i ∈ S} => Ω))

theorem measurePreserving_slotSwapMeas {n : ℕ} (S : Finset (Fin n)) :
    MeasurePreserving (slotSwapMeas S)
      (volume : Measure ((Fin n → Ω) × ({i : Fin n // i ∈ S} → Ω)))
      (volume : Measure ((Fin n → Ω) × ({i : Fin n // i ∈ S} → Ω))) := by
  have hE := volume_measurePreserving_sumPiEquivProdPi
    (fun _ : Fin n ⊕ {i : Fin n // i ∈ S} => Ω)
  have hperm := measurePreserving_slotPerm S
  have hEsymm := MeasurePreserving.symm
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ {i : Fin n // i ∈ S} => Ω)) hE
  have hcomp := hE.comp (hperm.comp hEsymm)
  simpa only [slotSwapMeas, MeasurableEquiv.coe_trans, Function.comp_apply] using hcomp

theorem slotSwap_sumPi_fst {δ δ' : Type*} (X : δ ⊕ δ' → Type*)
    [∀ i, MeasurableSpace (X i)] (z : (i : δ ⊕ δ') → X i) :
    ((MeasurableEquiv.sumPiEquivProdPi X) z).1 = fun i => z (Sum.inl i) := by
  rw [MeasurableEquiv.coe_sumPiEquivProdPi, Equiv.sumPiEquivProdPi_apply]

theorem slotSwap_sumPi_snd {δ δ' : Type*} (X : δ ⊕ δ' → Type*)
    [∀ i, MeasurableSpace (X i)] (z : (i : δ ⊕ δ') → X i) :
    ((MeasurableEquiv.sumPiEquivProdPi X) z).2 = fun i => z (Sum.inr i) := by
  rw [MeasurableEquiv.coe_sumPiEquivProdPi, Equiv.sumPiEquivProdPi_apply]

theorem slotSwap_sumPi_symm_apply {δ δ' : Type*} (X : δ ⊕ δ' → Type*)
    [∀ i, MeasurableSpace (X i)]
    (p : ((i : δ) → X (Sum.inl i)) × ((i' : δ') → X (Sum.inr i')))
    (t : δ ⊕ δ') :
    ((MeasurableEquiv.sumPiEquivProdPi X).symm p) t = Sum.rec p.1 p.2 t := by
  rw [MeasurableEquiv.coe_sumPiEquivProdPi_symm, Equiv.sumPiEquivProdPi_symm_apply]

/-- The first component of the swap: the `S`-slots are replaced by the fibre variables. -/
theorem slotSwapMeas_fst {n : ℕ} (S : Finset (Fin n))
    (p : (Fin n → Ω) × ({i : Fin n // i ∈ S} → Ω)) :
    (slotSwapMeas S p).1 = Function.updateFinset p.1 S p.2 := by
  funext i
  show (slotPerm S ((MeasurableEquiv.sumPiEquivProdPi
      (fun _ : Fin n ⊕ {i : Fin n // i ∈ S} => Ω)).symm p)) (Sum.inl i) = _
  rw [slotPerm_apply, slotSwapEquiv_apply, slotSwapFun]
  by_cases h : i ∈ S
  · rw [dif_pos h, slotSwap_sumPi_symm_apply]
    simp only [Function.updateFinset_def, dif_pos h]
  · rw [dif_neg h, slotSwap_sumPi_symm_apply]
    simp only [Function.updateFinset_def, dif_neg h]

/-- The second component of the swap: the fibre variables are replaced by the `S`-slots. -/
theorem slotSwapMeas_snd {n : ℕ} (S : Finset (Fin n))
    (p : (Fin n → Ω) × ({i : Fin n // i ∈ S} → Ω)) :
    (slotSwapMeas S p).2 = fun j : {i : Fin n // i ∈ S} => p.1 j.1 := by
  funext j
  show (slotPerm S ((MeasurableEquiv.sumPiEquivProdPi
      (fun _ : Fin n ⊕ {i : Fin n // i ∈ S} => Ω)).symm p)) (Sum.inr j) = _
  rw [slotPerm_apply, slotSwapEquiv_apply, slotSwapFun, slotSwap_sumPi_symm_apply]

/-- Replacing the slots of `S` twice returns the original configuration. -/
theorem slotUpdateFinset_updateFinset {n : ℕ} (S : Finset (Fin n))
    (x : Fin n → Ω) (z : ({i : Fin n // i ∈ S} → Ω)) :
    Function.updateFinset (Function.updateFinset x S z) S (fun i => x i.1) = x := by
  funext j
  rw [Function.updateFinset_def]
  by_cases h : j ∈ S <;> simp [h, Function.updateFinset_def]

/-- The `S`-slots of `Function.updateFinset x S z` are the fibre variables. -/
theorem slotUpdateFinset_apply_mem {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Ω)
    (z : {i : Fin n // i ∈ S} → Ω) (i : {i : Fin n // i ∈ S}) :
    Function.updateFinset x S z i.1 = z i := by
  simp only [Function.updateFinset_def, dif_pos i.2]

/-- The product of the kernels at the swapped configuration is the conjugate of the product at the
original one (`star_PV_comm`). -/
theorem slotSwap_prod_PV {m n : ℕ} (e : Fin m → Ω → ℂ) (S : Finset (Fin n))
    (p : (Fin n → Ω) × ({i : Fin n // i ∈ S} → Ω)) :
    (∏ i : {i : Fin n // i ∈ S}, PV e ((slotSwapMeas S p).1 i.1) ((slotSwapMeas S p).2 i)) =
      star (∏ i : {i : Fin n // i ∈ S}, PV e (p.1 i.1) (p.2 i)) := by
  rw [slotStar_prod_finset Finset.univ]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have h1 : (slotSwapMeas S p).1 i.1 = p.2 i := by
    rw [slotSwapMeas_fst S p, slotUpdateFinset_apply_mem S p.1 p.2 i]
  have h2 : (slotSwapMeas S p).2 i = p.1 i.1 := by
    simp only [slotSwapMeas_snd S p]
  rw [h1, h2, star_PV_comm]

/-! ## 4. Integrability of the slot kernel against a compactly supported state -/

theorem slotContinuous_updateFinset {n : ℕ} (S : Finset (Fin n)) :
    Continuous (fun p : (Fin n → Ω) × ({i : Fin n // i ∈ S} → Ω) =>
      Function.updateFinset p.1 S p.2) := by
  refine continuous_pi (fun i => ?_)
  simp only [Function.updateFinset_def]
  split_ifs with hi
  · exact (continuous_apply (⟨i, hi⟩ : {j : Fin n // j ∈ S})).comp continuous_snd
  · exact (continuous_apply i).comp continuous_fst

theorem integrable_slotKernel {m n : ℕ} (e : Fin m → Ω → ℂ) (he : ∀ l, Continuous (e l))
    (hec : ∀ l, HasCompactSupport (e l)) (S : Finset (Fin n))
    {f : (Fin n → Ω) → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    {g : (Fin n → Ω) → ℂ} (hg : Continuous g) {C : ℝ}
    (hgb : ∀ z, ‖g z‖ ≤ C) :
    Integrable (fun p : (Fin n → Ω) × ({i : Fin n // i ∈ S} → Ω) =>
      f p.1 * (∏ i : {i : Fin n // i ∈ S}, PV e (p.1 i.1) (p.2 i)) *
        g (Function.updateFinset p.1 S p.2))
      (volume : Measure ((Fin n → Ω) × ({i : Fin n // i ∈ S} → Ω))) := by
  classical
  have hsum_cont : Continuous (fun a : Ω => ∑ l : Fin m, ‖e l a‖) :=
    continuous_finsetSum _ (fun l _ => (he l).norm)
  have hsum_cs : HasCompactSupport (fun a : Ω => ∑ l : Fin m, ‖e l a‖) := by
    refine HasCompactSupport.intro (isCompact_iUnion (fun l : Fin m => (hec l).isCompact)) ?_
    intro a ha
    refine Finset.sum_eq_zero (fun l _ => ?_)
    rw [image_eq_zero_of_notMem_tsupport (fun h => ha (Set.mem_iUnion.mpr ⟨l, h⟩)), norm_zero]
  set h : Ω → ℝ := fun a => ∑ l : Fin m, ‖e l a‖ with hh
  have hcont : Continuous h := hsum_cont
  have hcs : HasCompactSupport h := hsum_cs
  have hnn : ∀ a, 0 ≤ h a := fun a => Finset.sum_nonneg (fun l _ => norm_nonneg _)
  have hPV : ∀ a b : Ω, ‖PV e a b‖ ≤ h a * h b := by
    intro a b
    calc ‖PV e a b‖ = ‖∑ l : Fin m, e l a * star (e l b)‖ := rfl
      _ ≤ ∑ l : Fin m, ‖e l a * star (e l b)‖ := norm_sum_le _ _
      _ = ∑ l : Fin m, ‖e l a‖ * ‖e l b‖ := by
            refine Finset.sum_congr rfl (fun l _ => ?_)
            rw [norm_mul, norm_star]
      _ ≤ (∑ l : Fin m, ‖e l a‖) * (∑ l : Fin m, ‖e l b‖) := by
            rw [Finset.sum_mul_sum]
            refine Finset.sum_le_sum (fun l _ => ?_)
            exact Finset.single_le_sum (f := fun j => ‖e l a‖ * ‖e j b‖)
              (fun j _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) (Finset.mem_univ l)
  set C₀ : ℝ := max C 0 with hC₀
  set b₁ : (Fin n → Ω) → ℝ := fun x => ‖f x‖ * ∏ i : {i : Fin n // i ∈ S}, h (x i.1) with hb₁
  set b₂ : ({i : Fin n // i ∈ S} → Ω) → ℝ :=
    fun z => C₀ * ∏ i : {i : Fin n // i ∈ S}, h (z i) with hb₂
  have hb₁c : Continuous b₁ := by
    rw [hb₁]
    exact (hf.norm).mul (continuous_finsetProd _ (fun i _ => hcont.comp (continuous_apply i.1)))
  have hb₁cs : HasCompactSupport b₁ := by
    refine HasCompactSupport.intro hfc.isCompact (fun x hx => ?_)
    simp only [hb₁, image_eq_zero_of_notMem_tsupport hx, norm_zero, zero_mul]
  have hb₂c : Continuous b₂ := by
    rw [hb₂]
    exact continuous_const.mul (continuous_finsetProd _ (fun i _ => hcont.comp (continuous_apply i)))
  have hb₂cs : HasCompactSupport b₂ := by
    refine HasCompactSupport.intro
      (isCompact_univ_pi (fun i : {i : Fin n // i ∈ S} => hcs.isCompact)) (fun z hz => ?_)
    have hex : ∃ i : {i : Fin n // i ∈ S}, z i ∉ tsupport h := by
      by_contra hcon
      exact hz (by rw [Set.mem_univ_pi]; intro i; exact not_not.mp (not_exists.mp hcon i))
    obtain ⟨i, hi⟩ := hex
    simp only [hb₂]
    rw [Finset.prod_eq_zero (Finset.mem_univ i)
      (image_eq_zero_of_notMem_tsupport (f := h) hi), mul_zero]
  have hint₁ : Integrable b₁ volume := hb₁c.integrable_of_hasCompactSupport hb₁cs
  have hint₂ : Integrable b₂ volume := hb₂c.integrable_of_hasCompactSupport hb₂cs
  have hprod : Integrable (fun p : (Fin n → Ω) × ({i : Fin n // i ∈ S} → Ω) =>
      b₁ p.1 * b₂ p.2) (volume : Measure ((Fin n → Ω) × ({i : Fin n // i ∈ S} → Ω))) :=
    hint₁.mul_prod hint₂
  have hintcont : Continuous (fun p : (Fin n → Ω) × ({i : Fin n // i ∈ S} → Ω) =>
      f p.1 * (∏ i : {i : Fin n // i ∈ S}, PV e (p.1 i.1) (p.2 i)) *
        g (Function.updateFinset p.1 S p.2)) :=
    ((hf.comp continuous_fst).mul (continuous_prod_PV_pair e he S)).mul
      (hg.comp (slotContinuous_updateFinset S))
  refine Integrable.mono' hprod hintcont.aestronglyMeasurable ?_
  filter_upwards with p
  rw [hb₁, hb₂]
  have hK : ‖∏ i : {i : Fin n // i ∈ S}, PV e (p.1 i.1) (p.2 i)‖ ≤
      (∏ i : {i : Fin n // i ∈ S}, h (p.1 i.1)) *
        (∏ i : {i : Fin n // i ∈ S}, h (p.2 i)) := by
    calc ‖∏ i : {i : Fin n // i ∈ S}, PV e (p.1 i.1) (p.2 i)‖
        ≤ ∏ i : {i : Fin n // i ∈ S}, ‖PV e (p.1 i.1) (p.2 i)‖ :=
          le_of_eq (norm_prod _ _)
      _ ≤ ∏ i : {i : Fin n // i ∈ S}, h (p.1 i.1) * h (p.2 i) :=
            Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hPV _ _)
      _ = (∏ i : {i : Fin n // i ∈ S}, h (p.1 i.1)) *
            (∏ i : {i : Fin n // i ∈ S}, h (p.2 i)) := Finset.prod_mul_distrib
  have hC0 : 0 ≤ C₀ := le_max_right C 0
  calc ‖f p.1 * (∏ i : {i : Fin n // i ∈ S}, PV e (p.1 i.1) (p.2 i)) *
        g (Function.updateFinset p.1 S p.2)‖
      = ‖f p.1‖ * ‖∏ i : {i : Fin n // i ∈ S}, PV e (p.1 i.1) (p.2 i)‖ *
          ‖g (Function.updateFinset p.1 S p.2)‖ := by rw [norm_mul, norm_mul]
    _ ≤ ‖f p.1‖ * ((∏ i : {i : Fin n // i ∈ S}, h (p.1 i.1)) *
          (∏ i : {i : Fin n // i ∈ S}, h (p.2 i))) * C₀ := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hK (norm_nonneg _))
            ((hgb _).trans (le_max_left C 0)) (norm_nonneg _) ?_
          exact mul_nonneg (norm_nonneg _)
            (mul_nonneg (Finset.prod_nonneg (fun i _ => hnn _))
              (Finset.prod_nonneg (fun i _ => hnn _)))
    _ = (‖f p.1‖ * ∏ i : {i : Fin n // i ∈ S}, h (p.1 i.1)) *
          (C₀ * ∏ i : {i : Fin n // i ∈ S}, h (p.2 i)) := by ring

/-! ## 5. The two integrands and the pointwise swap identity -/

/-- The integrand of the right-hand side of the adjointness identity, as a function on the product
space `(Fin n → Ω) × (↥S → Ω)`. -/
def slotKernelG {m n : ℕ} (e : Fin m → Ω → ℂ) (S : Finset (Fin n))
    (Φ Ψ : (Fin n → Ω) → ℂ) : ((Fin n → Ω) × ({i : Fin n // i ∈ S} → Ω)) → ℂ :=
  fun p => star (Φ p.1) * (∏ i : {i : Fin n // i ∈ S}, PV e (p.1 i.1) (p.2 i)) *
    Ψ (Function.updateFinset p.1 S p.2)

/-- The integrand of the left-hand side of the adjointness identity. -/
def slotKernelH {m n : ℕ} (e : Fin m → Ω → ℂ) (S : Finset (Fin n))
    (Φ Ψ : (Fin n → Ω) → ℂ) : ((Fin n → Ω) × ({i : Fin n // i ∈ S} → Ω)) → ℂ :=
  fun p => star (∏ i : {i : Fin n // i ∈ S}, PV e (p.1 i.1) (p.2 i)) *
    star (Φ (Function.updateFinset p.1 S p.2)) * Ψ p.1

theorem slotKernelG_integrable {m n : ℕ} (e : Fin m → Ω → ℂ) (he : ∀ l, Continuous (e l))
    (hec : ∀ l, HasCompactSupport (e l)) (S : Finset (Fin n))
    {Φ Ψ : (Fin n → Ω) → ℂ} (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ)
    (hΨ : Continuous Ψ) (hΨc : HasCompactSupport Ψ) :
    Integrable (slotKernelG e S Φ Ψ)
      (volume : Measure ((Fin n → Ω) × ({i : Fin n // i ∈ S} → Ω))) := by
  obtain ⟨CΨ, hCΨ⟩ := hΨ.bounded_above_of_compact_support hΨc
  exact integrable_slotKernel e he hec S (f := fun x => star (Φ x)) hΦ.star
    (hΦc.comp_left (g := star) (by simp : star (0 : ℂ) = 0)) hΨ (C := CΨ) hCΨ

/-- **The pointwise swap identity.**  The integrand of the right-hand side, evaluated at the
swapped configuration, is the integrand of the left-hand side. -/
theorem slotKernel_swap_pointwise {m n : ℕ} (e : Fin m → Ω → ℂ) (S : Finset (Fin n))
    (Φ Ψ : (Fin n → Ω) → ℂ)
    (p : (Fin n → Ω) × ({i : Fin n // i ∈ S} → Ω)) :
    slotKernelG e S Φ Ψ (slotSwapMeas S p) = slotKernelH e S Φ Ψ p := by
  have hupd : Function.updateFinset (slotSwapMeas S p).1 S (slotSwapMeas S p).2 = p.1 := by
    rw [slotSwapMeas_fst S p, slotSwapMeas_snd S p,
      slotUpdateFinset_updateFinset S p.1 p.2]
  simp only [slotKernelG, slotKernelH]
  rw [slotSwap_prod_PV e S p, hupd, slotSwapMeas_fst S p]
  ring

theorem slotKernelH_integrable {m n : ℕ} (e : Fin m → Ω → ℂ) (he : ∀ l, Continuous (e l))
    (hec : ∀ l, HasCompactSupport (e l)) (S : Finset (Fin n))
    {Φ Ψ : (Fin n → Ω) → ℂ} (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ)
    (hΨ : Continuous Ψ) (hΨc : HasCompactSupport Ψ) :
    Integrable (slotKernelH e S Φ Ψ)
      (volume : Measure ((Fin n → Ω) × ({i : Fin n // i ∈ S} → Ω))) :=
  (((measurePreserving_slotSwapMeas S).integrable_comp_emb
      (slotSwapMeas S).measurableEmbedding).mpr
    (slotKernelG_integrable e he hec S hΦ hΦc hΨ hΨc)).congr
    (Filter.Eventually.of_forall fun p => slotKernel_swap_pointwise e S Φ Ψ p)


/-! ## 6. Self-adjointness of the slot projection -/

theorem slotProj_adjoint {m n : ℕ} (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ)
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (horth : ∀ l l', ∫ z, star (e l z) * e l' z = (if l = l' then (1 : ℂ) else 0))
    (S : Finset (Fin n)) (Φ Ψ : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ)
    (hΨ : Continuous Ψ) (hΨc : HasCompactSupport Ψ) :
    ∫ x, star (slotProj e S Φ x) * Ψ x = ∫ x, star (Φ x) * slotProj e S Ψ x := by
  classical
  have hIntG := slotKernelG_integrable e he hec S hΦ hΦc hΨ hΨc
  have hIntH := slotKernelH_integrable e he hec S hΦ hΦc hΨ hΨc
  have hstep1 : (∫ x, star (slotProj e S Φ x) * Ψ x)
      = ∫ p, slotKernelH e S Φ Ψ p := by
    have h1 : (∫ x, star (slotProj e S Φ x) * Ψ x)
        = ∫ x, ∫ z : ({i : Fin n // i ∈ S} → Ω), slotKernelH e S Φ Ψ (x, z) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [slotKernelH]
      rw [slotProj, slotStar_integral volume, ← integral_mul_const]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [Function.updateFinset_def, star_mul]
      ring
    exact h1.trans (integral_prod (slotKernelH e S Φ Ψ) hIntH).symm
  have hstep2 : (∫ x, star (Φ x) * slotProj e S Ψ x)
      = ∫ p, slotKernelG e S Φ Ψ p := by
    have h1 : (∫ x, star (Φ x) * slotProj e S Ψ x)
        = ∫ x, ∫ z : ({i : Fin n // i ∈ S} → Ω), slotKernelG e S Φ Ψ (x, z) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [slotKernelG]
      rw [slotProj, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [Function.updateFinset_def]
      ring
    exact h1.trans (integral_prod (slotKernelG e S Φ Ψ) hIntG).symm
  have hswap : (∫ p, slotKernelH e S Φ Ψ p) = ∫ p, slotKernelG e S Φ Ψ p :=
    (integral_congr_ae (Filter.Eventually.of_forall fun p =>
      (slotKernel_swap_pointwise e S Φ Ψ p).symm)).trans
      (MeasurePreserving.integral_comp (measurePreserving_slotSwapMeas S)
        (slotSwapMeas S).measurableEmbedding (slotKernelG e S Φ Ψ))
  exact hstep1.trans (hswap.trans hstep2.symm)

end Work.BoseBoxFock
