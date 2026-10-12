import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.SliceBadAux
import Submission.Work.BoseBoxFock.jointProj_vanish
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.XSrpSector` — the real sector excited-count operator and its `L²` bound

The BF3c step-6 (`ExcWindow`) chain needs the *spectral* statement that the `S`-slot excited-count
operator `XS ℓ S = Σ_{i ∈ S} (1 − aPC ℓ i)` is bounded by `𝓜` on the `S`-sector
`slotExact e S Φ` of a box state `Φ` whose `n₊`-spectrum is confined to `[0, 𝓜]` by
`Work.BoseBox.SpectralNPlusLe ℓ 𝓜 Φ`.

This module supplies the *real* half of that statement, which needs **no** mode hypothesis at all:
the joint `θ`-sectors `jointProj ℓ W` (`Work.BoseFixB2`) are the spectral projections of `n₊`, and
a single occurrence of `XS` is diagonalised by them:

* `XSr`, `XSrp` — the real operators `Σ_{i∈S} aQ_i` and their iterates;
* `XS_ofReal`, `XSpow_ofReal` — the complex slot operators on a complexified real state are the
  complexifications of the real ones (via the existing `aPC_ofReal` of `slotCountsComplex`);
* `aP_jointProj_eq_zero_of_mem`, `aP_jointProj_eq_self_of_notMem`, `XSr_jointProj` — `XS` acts on
  the joint sector `E_W` by `sectorCount S W = #{i ∈ S : i ∈ W}`;
* `XSr_finset_sum`, `XSrp_sector_expansion` — linearity and the sector expansion;
* `XSr_sym_box`, `XSrp_succ_right`, `XSrp_comp`, `XSrp_sym_box` — self-adjointness over the box;
* `XSrp_moment`, `XSrp_parseval` — the moment and Parseval identities;
* **`XSrp_L2_le`** — the target: `∫_{abox} (XSrp j Φ)² ≤ 𝓜^{2j} ∫_{abox} Φ²`;
* **`XSpow_L2_le`** — its complex form at the complexified state.

Everything is `sorry`-free and rests on the standard axioms only.
-/

noncomputable section

open MeasureTheory
open Submission.BoseGases
open scoped BigOperators

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "Sp" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The real sector excited-count operator -/

/-- The real sector excited-count operator `XS ℓ S = Σ_{i ∈ S} (1 − aP_i)`. -/
noncomputable def XSr {n : ℕ} (ℓ : ℝ) (S : Finset (Fin n)) (Ψ : X n → ℝ) : X n → ℝ :=
  fun x => ∑ i ∈ S, (Ψ x - aP ℓ i Ψ x)

/-- The iterates of `XSr`. -/
noncomputable def XSrp {n : ℕ} (ℓ : ℝ) (S : Finset (Fin n)) : ℕ → (X n → ℝ) → (X n → ℝ)
  | 0, Ψ => Ψ
  | (j + 1), Ψ => XSr ℓ S (XSrp ℓ S j Ψ)

@[simp] lemma XSrp_zero {n : ℕ} (ℓ : ℝ) (S : Finset (Fin n)) (Ψ : X n → ℝ) :
    XSrp ℓ S 0 Ψ = Ψ := rfl

lemma XSrp_succ {n : ℕ} (ℓ : ℝ) (S : Finset (Fin n)) (j : ℕ) (Ψ : X n → ℝ) :
    XSrp ℓ S (j + 1) Ψ = XSr ℓ S (XSrp ℓ S j Ψ) := rfl

/-- **Complexification commutes with `XS`.** -/
lemma XS_ofReal {n : ℕ} (ℓ : ℝ) (S : Finset (Fin n)) (Ψ : X n → ℝ) :
    XS ℓ S (fun x => ((Ψ x : ℝ) : ℂ)) = fun x => ((XSr ℓ S Ψ x : ℝ) : ℂ) := by
  funext x
  have h : ∀ i : Fin n, aPC ℓ i (fun x => ((Ψ x : ℝ) : ℂ)) x = ((aP ℓ i Ψ x : ℝ) : ℂ) :=
    fun i => aPC_ofReal ℓ i Ψ x
  show (∑ i ∈ S, (((Ψ x : ℝ) : ℂ) - aPC ℓ i (fun y => ((Ψ y : ℝ) : ℂ)) x))
      = ((∑ i ∈ S, (Ψ x - aP ℓ i Ψ x) : ℝ) : ℂ)
  simp only [h, ← Complex.ofReal_sub]
  exact (Complex.ofReal_sum S (fun i => (Ψ x - aP ℓ i Ψ x))).symm

/-- **Complexification commutes with every iterate `XSpow`.** -/
lemma XSpow_ofReal {n : ℕ} (ℓ : ℝ) (S : Finset (Fin n)) :
    ∀ (j : ℕ) (Ψ : X n → ℝ),
      XSpow ℓ S j (fun x => ((Ψ x : ℝ) : ℂ)) = fun x => ((XSrp ℓ S j Ψ x : ℝ) : ℂ)
  | 0, Ψ => rfl
  | (j + 1), Ψ => by
      have ih := XSpow_ofReal ℓ S j Ψ
      rw [show XSpow ℓ S (j + 1) (fun x => ((Ψ x : ℝ) : ℂ))
            = XS ℓ S (XSpow ℓ S j (fun x => ((Ψ x : ℝ) : ℂ))) from rfl, ih,
        XS_ofReal ℓ S (XSrp ℓ S j Ψ)]
      rfl

/-! ## 2. The joint-sector eigenvalue of `XS` -/

/-- The eigenvalue of `XS` on the joint sector `E_W`: the number of slots of `S` excited in `W`. -/
noncomputable def sectorCount {n : ℕ} (S : Finset (Fin n)) (W : Finset ℕ) : ℝ :=
  (((S.filter (fun i : Fin n => (i : ℕ) ∈ W)).card : ℕ) : ℝ)

lemma sectorCount_nonneg {n : ℕ} (S : Finset (Fin n)) (W : Finset ℕ) :
    0 ≤ sectorCount S W := Nat.cast_nonneg _

lemma sectorCount_eq {n : ℕ} (S : Finset (Fin n)) (W : Finset ℕ) :
    sectorCount S W = (((S.filter (fun i : Fin n => (i : ℕ) ∈ W)).card : ℕ) : ℝ) := rfl

/-- The slot set counted by `sectorCount` has at most `W.card` elements. -/
lemma sectorCount_le_card {n : ℕ} (S : Finset (Fin n)) (W : Finset ℕ) :
    sectorCount S W ≤ (W.card : ℝ) := by
  have hinj : Function.Injective (fun i : Fin n => ((i : ℕ) : ℕ)) := fun a b h => Fin.ext h
  have h1 : (S.filter (fun i : Fin n => (i : ℕ) ∈ W)).card
      = ((S.filter (fun i : Fin n => (i : ℕ) ∈ W)).image (fun i : Fin n => (i : ℕ))).card :=
    (Finset.card_image_of_injective _ hinj).symm
  have h2 : ((S.filter (fun i : Fin n => (i : ℕ) ∈ W)).image (fun i : Fin n => (i : ℕ))).card
      ≤ W.card :=
    Finset.card_le_card (fun k hk => by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
      exact (Finset.mem_filter.mp hi).2)
  rw [sectorCount_eq]
  exact_mod_cast le_trans (le_of_eq h1) h2

/-- `aP_i` kills a joint sector in which the slot `i` is excited. -/
lemma aP_jointProj_eq_zero_of_mem {n : ℕ} (ℓ : ℝ) (hℓ : 0 < ℓ) {W : Finset ℕ} {k : ℕ}
    (hkW : k ∈ W) (hkn : k < n) {Φ : X n → ℝ} (hΦ : Continuous Φ) :
    aP ℓ ⟨k, hkn⟩ (Work.BoseFixB2.jointProj ℓ W Φ) = 0 := by
  funext x
  show aP ℓ ⟨k, hkn⟩ (Work.BoseFixB2.jointProj ℓ W Φ) x = 0
  have hx : aQ ℓ ⟨k, hkn⟩ (Work.BoseFixB2.jointProj ℓ W Φ) x
      = Work.BoseFixB2.jointProj ℓ W Φ x :=
    congrFun (Work.BoseFixB2.Sector.aQ_jointProj_of_mem (ℓ := ℓ) hℓ hkW hkn hΦ) x
  simp only [aQ] at hx
  linarith

/-- `aP_i` fixes a joint sector in which the slot `i` is not excited. -/
lemma aP_jointProj_eq_self_of_notMem {n : ℕ} (ℓ : ℝ) (hℓ : 0 < ℓ) {W : Finset ℕ} {k : ℕ}
    (hkW : k ∉ W) (hkn : k < n) {Φ : X n → ℝ} (hΦ : Continuous Φ) :
    aP ℓ ⟨k, hkn⟩ (Work.BoseFixB2.jointProj ℓ W Φ)
      = Work.BoseFixB2.jointProj ℓ W Φ := by
  funext x
  show aP ℓ ⟨k, hkn⟩ (Work.BoseFixB2.jointProj ℓ W Φ) x
      = Work.BoseFixB2.jointProj ℓ W Φ x
  have hx : aQ ℓ ⟨k, hkn⟩ (Work.BoseFixB2.jointProj ℓ W Φ) x = 0 := by
    have h := congrFun
      (Work.BoseFixB2.Sector.aQ_jointProj_of_notMem (ℓ := ℓ) hℓ hkW hkn hΦ) x
    simpa using h
  simp only [aQ] at hx
  linarith

/-- **The eigenvalue of `XS` on a joint sector.** -/
lemma XSr_jointProj {n : ℕ} (ℓ : ℝ) (hℓ : 0 < ℓ) (S : Finset (Fin n))
    {Φ : X n → ℝ} (hΦ : Continuous Φ) (W : Finset ℕ) :
    XSr ℓ S (Work.BoseFixB2.jointProj ℓ W Φ)
      = fun x => sectorCount S W * Work.BoseFixB2.jointProj ℓ W Φ x := by
  funext x
  have hterm : ∀ i ∈ S, (Work.BoseFixB2.jointProj ℓ W Φ x
        - aP ℓ i (Work.BoseFixB2.jointProj ℓ W Φ) x)
      = (if (i : ℕ) ∈ W then (1 : ℝ) else 0) * Work.BoseFixB2.jointProj ℓ W Φ x := by
    intro i _
    by_cases hW : (i : ℕ) ∈ W
    · rw [if_pos hW, one_mul]
      have h := congrFun (aP_jointProj_eq_zero_of_mem ℓ hℓ (W := W) hW i.isLt hΦ) x
      rw [h]
      simp
    · rw [if_neg hW, zero_mul]
      have h := congrFun (aP_jointProj_eq_self_of_notMem ℓ hℓ (W := W) hW i.isLt hΦ) x
      rw [h]
      ring
  show (∑ i ∈ S, (Work.BoseFixB2.jointProj ℓ W Φ x
        - aP ℓ i (Work.BoseFixB2.jointProj ℓ W Φ) x))
      = sectorCount S W * Work.BoseFixB2.jointProj ℓ W Φ x
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul,
    Finset.sum_boole (fun i : Fin n => (i : ℕ) ∈ W) S, sectorCount_eq]

/-! ## 3. Linearity and continuity -/

/-- **`XSr` is linear over a finite sum of continuous states.** -/
lemma XSr_finset_sum {n : ℕ} (ℓ : ℝ) (hℓ : 0 < ℓ) (S : Finset (Fin n)) {ι : Type*}
    (s : Finset ι) (c : ι → ℝ) (f : ι → X n → ℝ) (hf : ∀ W ∈ s, Continuous (f W)) (x : X n) :
    XSr ℓ S (fun y => ∑ W ∈ s, c W * f W y) x = ∑ W ∈ s, c W * XSr ℓ S (f W) x := by
  have h1 : ∀ i ∈ S, aP ℓ i (fun y => ∑ W ∈ s, c W * f W y) x
      = ∑ W ∈ s, c W * aP ℓ i (f W) x := fun i _ => aP_finset_sum hℓ i s c f hf x
  rw [XSr]
  calc ∑ i ∈ S, ((∑ W ∈ s, c W * f W x) - aP ℓ i (fun y => ∑ W ∈ s, c W * f W y) x)
      = ∑ i ∈ S, ∑ W ∈ s, (c W * f W x - c W * aP ℓ i (f W) x) := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        rw [h1 i hi, ← Finset.sum_sub_distrib]
    _ = ∑ W ∈ s, ∑ i ∈ S, (c W * f W x - c W * aP ℓ i (f W) x) := Finset.sum_comm
    _ = ∑ W ∈ s, c W * ∑ i ∈ S, (f W x - aP ℓ i (f W) x) := by
        refine Finset.sum_congr rfl (fun W _ => ?_)
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)
    _ = ∑ W ∈ s, c W * XSr ℓ S (f W) x := by
        refine Finset.sum_congr rfl (fun W _ => ?_)
        rw [XSr]

/-- `XSr` of a continuous state is continuous. -/
lemma XSr_continuous {n : ℕ} (ℓ : ℝ) (hℓ : 0 < ℓ) (S : Finset (Fin n)) {Ψ : X n → ℝ}
    (hΨ : Continuous Ψ) : Continuous (XSr ℓ S Ψ) := by
  show Continuous (fun x : X n => ∑ i ∈ S, (Ψ x - aP ℓ i Ψ x))
  exact continuous_finsetSum _ (fun i _ => hΨ.sub (aP_continuous hℓ i hΨ))

/-- The iterates of `XSr` preserve continuity. -/
lemma XSrp_continuous {n : ℕ} (ℓ : ℝ) (hℓ : 0 < ℓ) (S : Finset (Fin n)) :
    ∀ (j : ℕ) {Ψ : X n → ℝ}, Continuous Ψ → Continuous (XSrp ℓ S j Ψ)
  | 0, Ψ, hΨ => hΨ
  | (j + 1), Ψ, hΨ => XSr_continuous ℓ hℓ S (XSrp_continuous ℓ hℓ S j hΨ)

/-! ## 4. The joint-sector expansion of `XSrp` -/

/-- **The expansion of the iterated sector count in the joint sectors.** -/
lemma XSrp_sector_expansion {n : ℕ} (ℓ : ℝ) (hℓ : 0 < ℓ) (S : Finset (Fin n))
    {Φ : X n → ℝ} (hΦ : Continuous Φ) (j : ℕ) :
    XSrp ℓ S j Φ
      = fun x => ∑ W ∈ (Finset.range n).powerset,
          (sectorCount S W) ^ j * Work.BoseFixB2.jointProj ℓ W Φ x := by
  induction j with
  | zero =>
      funext x
      have hres : (∑ W ∈ (Finset.range n).powerset,
          (sectorCount S W) ^ 0 * Work.BoseFixB2.jointProj ℓ W Φ x) = Φ x := by
        rw [← congrFun (Work.BoseFixB2.Sector.jointProj_resolution hℓ Φ hΦ) x,
          Finset.sum_apply]
        exact (Finset.sum_congr rfl (fun W _ => by rw [pow_zero, one_mul])).symm
      exact hres.symm
  | succ j ih =>
      rw [show XSrp ℓ S (j + 1) Φ = XSr ℓ S (XSrp ℓ S j Φ) from rfl, ih]
      funext x
      rw [XSr_finset_sum ℓ hℓ S _ (fun W => (sectorCount S W) ^ j)
        (fun W => Work.BoseFixB2.jointProj ℓ W Φ)
        (fun W _ => Work.BoseFixB2.Sector.jointProj_continuous hℓ W hΦ) x]
      refine Finset.sum_congr rfl (fun W _ => ?_)
      rw [XSr_jointProj ℓ hℓ S hΦ W, pow_succ]
      ring

/-! ## 5. Self-adjointness over the box -/

/-- **`XSr` is self-adjoint over the box.** -/
lemma XSr_sym_box {n : ℕ} (ℓ : ℝ) (hℓ : 0 < ℓ) (S : Finset (Fin n)) {Φ Ψ : X n → ℝ}
    (hΦ : Continuous Φ) (hΨ : Continuous Ψ) :
    (∫ x in abox n ℓ, XSr ℓ S Φ x * Ψ x)
      = ∫ x in abox n ℓ, Φ x * XSr ℓ S Ψ x := by
  have hcontL : ∀ i ∈ S, IntegrableOn (fun x => aQ ℓ i Φ x * Ψ x) (abox n ℓ) := by
    intro i _
    have h1 : Continuous (fun x : X n => aQ ℓ i Φ x) := by
      show Continuous (fun x : X n => Φ x - aP ℓ i Φ x)
      exact hΦ.sub (aP_continuous hℓ i hΦ)
    exact integrableOn_abox_of_continuous hℓ (h1.mul hΨ)
  have hcontR : ∀ i ∈ S, IntegrableOn (fun x => Φ x * aQ ℓ i Ψ x) (abox n ℓ) := by
    intro i _
    have h1 : Continuous (fun x : X n => aQ ℓ i Ψ x) := by
      show Continuous (fun x : X n => Ψ x - aP ℓ i Ψ x)
      exact hΨ.sub (aP_continuous hℓ i hΨ)
    exact integrableOn_abox_of_continuous hℓ (hΦ.mul h1)
  have hL : (∫ x in abox n ℓ, XSr ℓ S Φ x * Ψ x)
      = ∑ i ∈ S, ∫ x in abox n ℓ, aQ ℓ i Φ x * Ψ x := by
    rw [show (fun x : X n => XSr ℓ S Φ x * Ψ x)
        = fun x => ∑ i ∈ S, aQ ℓ i Φ x * Ψ x from by
      funext x
      show (∑ i ∈ S, (Φ x - aP ℓ i Φ x)) * Ψ x = ∑ i ∈ S, (Φ x - aP ℓ i Φ x) * Ψ x
      rw [Finset.sum_mul]]
    rw [integral_finsetSum _ (fun i hi => hcontL i hi)]
  have hR : (∫ x in abox n ℓ, Φ x * XSr ℓ S Ψ x)
      = ∑ i ∈ S, ∫ x in abox n ℓ, Φ x * aQ ℓ i Ψ x := by
    rw [show (fun x : X n => Φ x * XSr ℓ S Ψ x)
        = fun x => ∑ i ∈ S, Φ x * aQ ℓ i Ψ x from by
      funext x
      show Φ x * (∑ i ∈ S, (Ψ x - aP ℓ i Ψ x)) = ∑ i ∈ S, Φ x * (Ψ x - aP ℓ i Ψ x)
      rw [Finset.mul_sum]]
    rw [integral_finsetSum _ (fun i hi => hcontR i hi)]
  rw [hL, hR]
  exact Finset.sum_congr rfl (fun i _ => Work.BoseFixB2.Sector.aQ_sym_box hℓ i hΦ hΨ)

/-- The iterates of `XSr` commute with one more `XSr`. -/
lemma XSrp_succ_right {n : ℕ} (ℓ : ℝ) (S : Finset (Fin n)) (j : ℕ) (Ψ : X n → ℝ) :
    XSrp ℓ S j (XSr ℓ S Ψ) = XSrp ℓ S (j + 1) Ψ := by
  induction j with
  | zero => rfl
  | succ j ih =>
      show XSr ℓ S (XSrp ℓ S j (XSr ℓ S Ψ)) = XSr ℓ S (XSrp ℓ S (j + 1) Ψ)
      rw [ih]

/-- The iterates of `XSr` compose. -/
lemma XSrp_comp {n : ℕ} (ℓ : ℝ) (S : Finset (Fin n)) (j k : ℕ) (Φ : X n → ℝ) :
    XSrp ℓ S (j + k) Φ = XSrp ℓ S k (XSrp ℓ S j Φ) := by
  induction k with
  | zero => simp only [Nat.add_zero, XSrp_zero]
  | succ k ih =>
      show XSr ℓ S (XSrp ℓ S (j + k) Φ) = XSr ℓ S (XSrp ℓ S k (XSrp ℓ S j Φ))
      rw [ih]

/-- **Self-adjointness of the iterates of `XSr` over the box.** -/
lemma XSrp_sym_box {n : ℕ} (ℓ : ℝ) (hℓ : 0 < ℓ) (S : Finset (Fin n)) (j : ℕ)
    {Φ Ψ : X n → ℝ} (hΦ : Continuous Φ) (hΨ : Continuous Ψ) :
    (∫ x in abox n ℓ, XSrp ℓ S j Φ x * Ψ x)
      = ∫ x in abox n ℓ, Φ x * XSrp ℓ S j Ψ x := by
  induction j generalizing Ψ with
  | zero =>
      simp only [XSrp_zero]
  | succ j ih =>
      have hΦj : Continuous (XSrp ℓ S j Φ) := XSrp_continuous ℓ hℓ S j hΦ
      have hXΨ : Continuous (XSr ℓ S Ψ) := XSr_continuous ℓ hℓ S hΨ
      rw [show (fun x : X n => XSrp ℓ S (j + 1) Φ x * Ψ x)
            = fun x => XSr ℓ S (XSrp ℓ S j Φ) x * Ψ x from rfl,
        XSr_sym_box ℓ hℓ S hΦj hΨ,
        ih (Ψ := XSr ℓ S Ψ) hXΨ]
      exact integral_congr_ae (Filter.Eventually.of_forall (fun x => by
        rw [XSrp_succ_right]))

/-! ## 6. The moment and Parseval identities -/

/-- **The moment identity**: pairing the joint-sector expansion of `XSrp k Φ` against the state. -/
lemma XSrp_moment {n : ℕ} (ℓ : ℝ) (hℓ : 0 < ℓ) (S : Finset (Fin n))
    {Φ : X n → ℝ} (hΦ : Continuous Φ) (k : ℕ) :
    (∫ x in abox n ℓ, XSrp ℓ S k Φ x * Φ x)
      = ∑ W ∈ (Finset.range n).powerset,
          (sectorCount S W) ^ k *
            ∫ x in abox n ℓ, (Work.BoseFixB2.jointProj ℓ W Φ x) ^ 2 := by
  have hfun : (fun x : X n => XSrp ℓ S k Φ x * Φ x)
      = fun x => (∑ W ∈ (Finset.range n).powerset,
            (sectorCount S W) ^ k * Work.BoseFixB2.jointProj ℓ W Φ x) * Φ x := by
    funext x
    rw [congrFun (XSrp_sector_expansion ℓ hℓ S hΦ k) x]
  rw [hfun]
  let g : Finset ℕ → X n → ℝ := fun W y =>
    (sectorCount S W) ^ k * (Work.BoseFixB2.jointProj ℓ W Φ y * Φ y)
  have hsum : (fun x : X n => (∑ W ∈ (Finset.range n).powerset,
          (sectorCount S W) ^ k * Work.BoseFixB2.jointProj ℓ W Φ x) * Φ x)
      = fun x => ∑ W ∈ (Finset.range n).powerset, g W x := by
    funext x
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun W _ => by simp only [g]; ring)
  rw [hsum]
  have hint : (∫ x in abox n ℓ, ∑ W ∈ (Finset.range n).powerset, g W x)
      = ∑ W ∈ (Finset.range n).powerset, ∫ x in abox n ℓ, g W x := by
    refine integral_finsetSum _ (fun W _ => ?_)
    show IntegrableOn (fun x : X n => (sectorCount S W) ^ k *
      (Work.BoseFixB2.jointProj ℓ W Φ x * Φ x)) (abox n ℓ)
    exact integrableOn_abox_of_continuous hℓ
      (continuous_const.mul ((Work.BoseFixB2.Sector.jointProj_continuous hℓ W hΦ).mul hΦ))
  rw [hint]
  refine Finset.sum_congr rfl (fun W hW => ?_)
  rw [show g W = fun y => (sectorCount S W) ^ k *
      (Work.BoseFixB2.jointProj ℓ W Φ y * Φ y) from rfl, integral_const_mul,
    sector_pairing ℓ hℓ hΦ (Finset.mem_powerset.mp hW)]

/-- **The Parseval identity** for the square of the iterated sector count. -/
lemma XSrp_parseval {n : ℕ} (ℓ : ℝ) (hℓ : 0 < ℓ) (S : Finset (Fin n))
    {Φ : X n → ℝ} (hΦ : Continuous Φ) (j : ℕ) :
    (∫ x in abox n ℓ, (XSrp ℓ S j Φ x) ^ 2)
      = ∑ W ∈ (Finset.range n).powerset,
          (sectorCount S W) ^ (2 * j) *
            ∫ x in abox n ℓ, (Work.BoseFixB2.jointProj ℓ W Φ x) ^ 2 := by
  have hcomp : XSrp ℓ S j (XSrp ℓ S j Φ) = XSrp ℓ S (2 * j) Φ := by
    rw [(XSrp_comp ℓ S j j Φ).symm]
    congr 1
    ring
  have hsq : (∫ x in abox n ℓ, (XSrp ℓ S j Φ x) ^ 2)
      = ∫ x in abox n ℓ, XSrp ℓ S (2 * j) Φ x * Φ x := by
    have h := XSrp_sym_box ℓ hℓ S j (Φ := Φ) (Ψ := XSrp ℓ S j Φ) hΦ
      (XSrp_continuous ℓ hℓ S j hΦ)
    rw [show (fun x : X n => (XSrp ℓ S j Φ x) ^ 2)
        = fun x => XSrp ℓ S j Φ x * XSrp ℓ S j Φ x from funext fun x => sq _]
    calc (∫ x in abox n ℓ, XSrp ℓ S j Φ x * XSrp ℓ S j Φ x)
        = ∫ x in abox n ℓ, Φ x * XSrp ℓ S j (XSrp ℓ S j Φ) x := h
      _ = ∫ x in abox n ℓ, Φ x * XSrp ℓ S (2 * j) Φ x := by rw [hcomp]
      _ = ∫ x in abox n ℓ, XSrp ℓ S (2 * j) Φ x * Φ x :=
          integral_congr_ae (Filter.Eventually.of_forall (fun x => mul_comm _ _))
  rw [hsq, XSrp_moment ℓ hℓ S hΦ (2 * j)]

/-! ## 7. The `L²` spectral bound -/

/-- **The `L²` bound for the real sector count**: on a state whose `n₊`-spectrum lies in `[0, 𝓜]`,
every iterate of `XS` is bounded by `𝓜`. -/
lemma XSrp_L2_le {n : ℕ} (ℓ : ℝ) (hℓ : 0 < ℓ) (S : Finset (Fin n))
    {Φ : X n → ℝ} (hΦ : Continuous Φ) {M : ℝ} (hM : 0 ≤ M)
    (hmom : Work.BoseBox.SpectralNPlusLe ℓ M Φ) (j : ℕ) :
    (∫ x in abox n ℓ, (XSrp ℓ S j Φ x) ^ 2)
      ≤ M ^ (2 * j) * (∫ x in abox n ℓ, (Φ x) ^ 2) := by
  have hbase : (∫ x in abox n ℓ, (Φ x) ^ 2)
      = ∑ W ∈ (Finset.range n).powerset,
          ∫ x in abox n ℓ, (Work.BoseFixB2.jointProj ℓ W Φ x) ^ 2 := by
    have h0 := XSrp_parseval ℓ hℓ S hΦ 0
    simpa only [XSrp_zero, Nat.mul_zero, pow_zero, one_mul] using h0
  rw [hbase, XSrp_parseval ℓ hℓ S hΦ j, Finset.mul_sum]
  refine Finset.sum_le_sum (fun W hW => ?_)
  have hI : 0 ≤ ∫ x in abox n ℓ, (Work.BoseFixB2.jointProj ℓ W Φ x) ^ 2 :=
    integral_nonneg fun x => sq_nonneg _
  by_cases hcard : (W.card : ℝ) ≤ M
  · have h1 : sectorCount S W ≤ M := le_trans (sectorCount_le_card S W) hcard
    have h2 : (sectorCount S W) ^ (2 * j) ≤ M ^ (2 * j) :=
      pow_le_pow_left₀ (sectorCount_nonneg S W) h1 _
    exact mul_le_mul_of_nonneg_right h2 hI
  · have hlt : M < (W.card : ℝ) := not_le.mp hcard
    have hz := jointProj_vanish ℓ hℓ hΦ hM hmom W (Finset.mem_powerset.mp hW) hlt
    rw [hz]
    simp

/-- **The `L²` bound in the complex form used by the `ExcWindow` chain**: at the complexified
state, the complex operator `XSpow ℓ S j` is bounded by `𝓜`. -/
lemma XSpow_L2_le {n : ℕ} (ℓ : ℝ) (hℓ : 0 < ℓ) (S : Finset (Fin n))
    {Φ : X n → ℝ} (hΦ : Continuous Φ) {M : ℝ} (hM : 0 ≤ M)
    (hmom : Work.BoseBox.SpectralNPlusLe ℓ M Φ) (j : ℕ) :
    (∫ x in abox n ℓ, ‖XSpow ℓ S j (fun x => ((Φ x : ℝ) : ℂ)) x‖ ^ 2)
      ≤ M ^ (2 * j) * (∫ x in abox n ℓ, (Φ x) ^ 2) := by
  have hpt : ∀ x : X n, ‖XSpow ℓ S j (fun x => ((Φ x : ℝ) : ℂ)) x‖ ^ 2
      = (XSrp ℓ S j Φ x) ^ 2 := by
    intro x
    rw [congrFun (XSpow_ofReal ℓ S j Φ) x, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_ofReal, sq]
  rw [show (∫ x in abox n ℓ, ‖XSpow ℓ S j (fun x => ((Φ x : ℝ) : ℂ)) x‖ ^ 2)
      = ∫ x in abox n ℓ, (XSrp ℓ S j Φ x) ^ 2 from
    integral_congr_ae (Filter.Eventually.of_forall hpt)]
  exact XSrp_L2_le ℓ hℓ S hΦ hM hmom j

end Work.BoseBoxFock
