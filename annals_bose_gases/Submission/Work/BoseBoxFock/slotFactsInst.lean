import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.slotFacts
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.slotFactsInst` — closure and base instances of `SlotFacts`

The three operator-side facts of `Work.BoseBoxFock.SlotFacts` (goodness, the pointwise decoupling
on a sector, and the sector splitting of the quadratic form) are *linear* in the operator, so the
structure is closed under finite real linear combinations.  This module records the closure and the
base instances

* `SlotFacts.boxSlotSum` — the one-body slot sum `boxSlotSum e T`, from the proved
  `slotSum_sector_split` and `boxSlotSum_pairCoord`;
* `SlotFacts.id` — the identity, whose sector splitting is the mass splitting of the sectors
  (`massR_eq_sum_slotExact`, proved here along the lines of the corresponding step of
  `exists_sector_le_of_slotSum`).

Everything here is `sorry`-free.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

open Work.BoseDict

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

variable {m n : ℕ}

/-- Goodness and compact support of the sector of a continuous compactly supported state. -/
theorem slotExact_slotGood {e : Fin m → Ω → ℂ} (he : ∀ l, Continuous (e l))
    (hec : ∀ l, HasCompactSupport (e l)) (S : Finset (Fin n)) (Φc : Xn n → ℂ)
    (hΦ : Continuous Φc) (hΦc : HasCompactSupport Φc) :
    SlotGood (slotExact e S Φc) ∧ HasCompactSupport (slotExact e S Φc) := by
  obtain ⟨hm, hb, hc⟩ := slotExact_measurable_bounded_compactSupport e he hec S Φc hΦ hΦc
  exact ⟨⟨hm, hb⟩, hc⟩

/-- **The mass splitting over the sectors.** -/
theorem massR_eq_sum_slotExact {e : Fin m → Ω → ℂ} (he : ∀ l, Continuous (e l))
    (hec : ∀ l, HasCompactSupport (e l))
    (horth : ∀ l l', (∫ z : Ω, star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0))
    (Φ : Xn n → ℂ) (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) :
    massR Φ = ∑ S : Finset (Fin n), massR (slotExact e S Φ) := by
  classical
  have hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C := hΦ.bounded_above_of_compact_support hΦc
  have hsec : ∀ S : Finset (Fin n), Measurable (slotExact e S Φ) ∧
      (∃ C, ∀ x, ‖slotExact e S Φ x‖ ≤ C) ∧ HasCompactSupport (slotExact e S Φ) :=
    fun S => slotExact_measurable_bounded_compactSupport e he hec S Φ hΦ hΦc
  have hintΦ : ∀ S : Finset (Fin n),
      MeasureTheory.Integrable (fun x => star (Φ x) * slotExact e S Φ x) :=
    fun S => integrable_mul_contCompact_of_bounded
      (continuous_star.comp hΦ) (hΦc.comp_left (by simp)) (hsec S).1 (hsec S).2.1
  have horthC : ∀ S : Finset (Fin n),
      (∫ x, star (Φ x) * slotExact e S Φ x)
        = (∫ x, star (slotExact e S Φ x) * slotExact e S Φ x) := by
    intro S
    have h := slotExact_orth_gen e he hec horth S S Φ hΦ hΦc Φ hΦ.measurable hΦb
    rw [if_pos rfl] at h
    exact h.symm
  rw [massR]
  have hpt : (fun x : Xn n => star (Φ x) * Φ x)
      = fun x => ∑ S : Finset (Fin n), star (Φ x) * slotExact e S Φ x := by
    funext x
    have hx : (∑ S : Finset (Fin n), slotExact e S Φ x) = Φ x := by
      simpa only [Finset.sum_apply] using congrFun (slotExact_sum_eq e Φ) x
    rw [← Finset.mul_sum, hx]
  rw [hpt, MeasureTheory.integral_finsetSum _ (fun S _ => hintΦ S),
    Finset.sum_congr rfl (fun S _ => horthC S)]
  simp [massR]

/-! ## 1. Closure of `SlotFacts` under real linear combinations -/

theorem SlotFacts.add {e : Fin m → Ω → ℂ} {Φc : Xn n → ℂ}
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (hΦcont : Continuous Φc) (hΦc : HasCompactSupport Φc)
    {Op1 Op2 : (Xn n → ℂ) → (Xn n → ℂ)}
    {OpS1 OpS2 : (S : Finset (Fin n)) → (({i // i ∈ S} → Ω) → ℂ)
      → (({i // i ∈ S} → Ω) → ℂ)}
    (h1 : SlotFacts e Φc Op1 OpS1) (h2 : SlotFacts e Φc Op2 OpS2) :
    SlotFacts e Φc (Op1 + Op2) (fun S X => OpS1 S X + OpS2 S X) := by
  have hΦ : SlotGood Φc := ⟨hΦcont.measurable, hΦcont.bounded_above_of_compact_support hΦc⟩
  have hsec := fun S => slotExact_slotGood he hec S Φc hΦcont hΦc
  refine ⟨RowGood.add h1.good h2.good, ?_, ?_⟩
  · intro S u y
    show Op1 (slotExact e S Φc) (pairCoord S u y) + Op2 (slotExact e S Φc) (pairCoord S u y)
      = OpS1 S (fun u' => slotExact e S Φc (pairCoord S u' y)) u
        + OpS2 S (fun u' => slotExact e S Φc (pairCoord S u' y)) u
    rw [h1.slice S u y, h2.slice S u y]
  · have hi1 : MeasureTheory.Integrable (fun x : Xn n => star (Φc x) * Op1 Φc x) :=
      integrable_star_mul_of_compact hΦc hΦ (h1.good Φc hΦ)
    have hi2 : MeasureTheory.Integrable (fun x : Xn n => star (Φc x) * Op2 Φc x) :=
      integrable_star_mul_of_compact hΦc hΦ (h2.good Φc hΦ)
    have hj1 : ∀ S : Finset (Fin n), MeasureTheory.Integrable (fun x : Xn n =>
        star (slotExact e S Φc x) * Op1 (slotExact e S Φc) x) := fun S =>
      integrable_star_mul_of_compact (hsec S).2 (hsec S).1 (h1.good _ (hsec S).1)
    have hj2 : ∀ S : Finset (Fin n), MeasureTheory.Integrable (fun x : Xn n =>
        star (slotExact e S Φc x) * Op2 (slotExact e S Φc) x) := fun S =>
      integrable_star_mul_of_compact (hsec S).2 (hsec S).1 (h2.good _ (hsec S).1)
    have hpt1 : (fun x : Xn n => star (Φc x) * (Op1 + Op2) Φc x)
        = fun x : Xn n => star (Φc x) * Op1 Φc x + star (Φc x) * Op2 Φc x := by
      funext x
      simp only [Pi.add_apply, mul_add]
    have hpt2 : ∀ S : Finset (Fin n),
        (fun x : Xn n => star (slotExact e S Φc x) * (Op1 + Op2) (slotExact e S Φc) x)
          = fun x : Xn n => star (slotExact e S Φc x) * Op1 (slotExact e S Φc) x
              + star (slotExact e S Φc x) * Op2 (slotExact e S Φc) x := by
      intro S
      funext x
      simp only [Pi.add_apply, mul_add]
    calc (∫ x : Xn n, star (Φc x) * (Op1 + Op2) Φc x).re
        = (∫ x : Xn n, (star (Φc x) * Op1 Φc x + star (Φc x) * Op2 Φc x)).re := by
          rw [hpt1]
      _ = ((∫ x : Xn n, star (Φc x) * Op1 Φc x)
            + (∫ x : Xn n, star (Φc x) * Op2 Φc x)).re := by
          rw [MeasureTheory.integral_add hi1 hi2]
      _ = (∫ x : Xn n, star (Φc x) * Op1 Φc x).re
            + (∫ x : Xn n, star (Φc x) * Op2 Φc x).re := Complex.add_re _ _
      _ = (∑ S : Finset (Fin n),
              (∫ x : Xn n, star (slotExact e S Φc x) * Op1 (slotExact e S Φc) x).re)
            + ∑ S : Finset (Fin n),
              (∫ x : Xn n, star (slotExact e S Φc x) * Op2 (slotExact e S Φc) x).re := by
          rw [h1.split, h2.split]
      _ = ∑ S : Finset (Fin n),
              ((∫ x : Xn n, star (slotExact e S Φc x) * Op1 (slotExact e S Φc) x).re
                + (∫ x : Xn n, star (slotExact e S Φc x) * Op2 (slotExact e S Φc) x).re) :=
          (Finset.sum_add_distrib).symm
      _ = ∑ S : Finset (Fin n),
              (∫ x : Xn n, star (slotExact e S Φc x) * (Op1 + Op2) (slotExact e S Φc) x).re := by
          refine Finset.sum_congr rfl (fun S _ => ?_)
          rw [hpt2 S, MeasureTheory.integral_add (hj1 S) (hj2 S), Complex.add_re]

/-- The zero operator satisfies the facts. -/
theorem SlotFacts.zero {e : Fin m → Ω → ℂ} {Φc : Xn n → ℂ} (hΦc : HasCompactSupport Φc)
    (hΦ : SlotGood Φc) :
    SlotFacts e Φc (fun _ : Xn n → ℂ => 0) (fun _ _ => 0) := by
  have h0 : (fun _ : Xn n → ℂ => (0 : Xn n → ℂ)) = fun _ => 0 := rfl
  refine ⟨?_, ?_, ?_⟩
  · intro X hX
    exact SlotGood.zero
  · intro S u y; rfl
  · simp

theorem SlotFacts.smul {e : Fin m → Ω → ℂ} {Φc : Xn n → ℂ}
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (hΦcont : Continuous Φc) (hΦc : HasCompactSupport Φc)
    (r : ℝ) {Op : (Xn n → ℂ) → (Xn n → ℂ)}
    {OpS : (S : Finset (Fin n)) → (({i // i ∈ S} → Ω) → ℂ) → (({i // i ∈ S} → Ω) → ℂ)}
    (h : SlotFacts e Φc Op OpS) :
    SlotFacts e Φc (r • Op) (fun S X => r • OpS S X) := by
  have hΦ : SlotGood Φc := ⟨hΦcont.measurable, hΦcont.bounded_above_of_compact_support hΦc⟩
  have hsec := fun S => slotExact_slotGood he hec S Φc hΦcont hΦc
  refine ⟨h.good.smul r, ?_, ?_⟩
  · intro S u y
    show r • (Op (slotExact e S Φc) (pairCoord S u y))
      = r • (OpS S (fun u' => slotExact e S Φc (pairCoord S u' y)) u)
    rw [h.slice S u y]
  · have hi : MeasureTheory.Integrable (fun x : Xn n => star (Φc x) * Op Φc x) :=
      integrable_star_mul_of_compact hΦc hΦ (h.good Φc hΦ)
    have hj : ∀ S : Finset (Fin n), MeasureTheory.Integrable (fun x : Xn n =>
        star (slotExact e S Φc x) * Op (slotExact e S Φc) x) := fun S =>
      integrable_star_mul_of_compact (hsec S).2 (hsec S).1 (h.good _ (hsec S).1)
    have hpt : (fun x : Xn n => star (Φc x) * (r • Op) Φc x)
        = fun x : Xn n => r • (star (Φc x) * Op Φc x) := by
      funext x
      simp only [Pi.smul_apply, Complex.real_smul]
      ring
    have hptS : ∀ S : Finset (Fin n),
        (fun x : Xn n => star (slotExact e S Φc x) * (r • Op) (slotExact e S Φc) x)
          = fun x : Xn n => r • (star (slotExact e S Φc x) * Op (slotExact e S Φc) x) := by
      intro S
      funext x
      simp only [Pi.smul_apply, Complex.real_smul]
      ring
    calc (∫ x : Xn n, star (Φc x) * (r • Op) Φc x).re
        = (∫ x : Xn n, r • (star (Φc x) * Op Φc x)).re := by rw [hpt]
      _ = (r • (∫ x : Xn n, star (Φc x) * Op Φc x)).re := by
          rw [MeasureTheory.integral_smul]
      _ = r * (∫ x : Xn n, star (Φc x) * Op Φc x).re := by
          simp
      _ = r * ∑ S : Finset (Fin n),
              (∫ x : Xn n, star (slotExact e S Φc x) * Op (slotExact e S Φc) x).re := by
          rw [h.split]
      _ = ∑ S : Finset (Fin n), r *
              (∫ x : Xn n, star (slotExact e S Φc x) * Op (slotExact e S Φc) x).re := by
          rw [Finset.mul_sum]
      _ = ∑ S : Finset (Fin n),
              (r • (∫ x : Xn n, star (slotExact e S Φc x) * Op (slotExact e S Φc) x)).re := by
          refine Finset.sum_congr rfl (fun S _ => ?_)
          simp
      _ = ∑ S : Finset (Fin n),
              (∫ x : Xn n, r • (star (slotExact e S Φc x) * Op (slotExact e S Φc) x)).re := by
          refine Finset.sum_congr rfl (fun S _ => ?_)
          rw [MeasureTheory.integral_smul]
      _ = ∑ S : Finset (Fin n),
              (∫ x : Xn n, star (slotExact e S Φc x) * (r • Op) (slotExact e S Φc) x).re := by
          refine Finset.sum_congr rfl (fun S _ => ?_)
          rw [hptS S]

/-- Finite real linear combinations of operators satisfying the facts also satisfy them. -/
theorem SlotFacts.finset_smul_sum {e : Fin m → Ω → ℂ} {Φc : Xn n → ℂ}
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (hΦcont : Continuous Φc) (hΦc : HasCompactSupport Φc)
    {κ : Type*} (s : Finset κ) (r : κ → ℝ)
    {Ops : κ → (Xn n → ℂ) → (Xn n → ℂ)}
    {OpsS : κ → (S : Finset (Fin n)) → (({i // i ∈ S} → Ω) → ℂ) → (({i // i ∈ S} → Ω) → ℂ)}
    (h : ∀ i, SlotFacts e Φc (Ops i) (OpsS i)) :
    SlotFacts e Φc (∑ i ∈ s, r i • Ops i)
      (fun S X => ∑ i ∈ s, r i • OpsS i S X) := by
  classical
  have hΦ : SlotGood Φc := ⟨hΦcont.measurable, hΦcont.bounded_above_of_compact_support hΦc⟩
  induction s using Finset.induction with
  | empty =>
      have h0 : (∑ i ∈ (∅ : Finset κ), r i • Ops i) = fun _ : Xn n → ℂ => 0 := by
        funext X x; simp
      have h0S : (fun S X => ∑ i ∈ (∅ : Finset κ), r i • OpsS i S X)
          = fun _ _ => 0 := by
        funext S X; simp
      rw [h0, h0S]
      exact SlotFacts.zero hΦc hΦ
  | insert a s ha ih =>
      have hsum : (∑ i ∈ insert a s, r i • Ops i) = r a • Ops a + ∑ i ∈ s, r i • Ops i :=
        Finset.sum_insert ha
      have hsumS : (fun S X => ∑ i ∈ insert a s, r i • OpsS i S X)
          = (fun S X => r a • OpsS a S X + ∑ i ∈ s, r i • OpsS i S X) := by
        funext S X
        rw [Finset.sum_insert ha]
      rw [hsum, hsumS]
      exact ((h a).smul he hec hΦcont hΦc (r a)).add he hec hΦcont hΦc ih

/-- **The identity operator** satisfies the facts (its splitting is the mass splitting). -/
theorem SlotFacts.id {e : Fin m → Ω → ℂ} (he : ∀ l, Continuous (e l))
    (hec : ∀ l, HasCompactSupport (e l))
    (horth : ∀ l l', (∫ z : Ω, star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0))
    {Φc : Xn n → ℂ} (hΦcont : Continuous Φc) (hΦc : HasCompactSupport Φc) :
    SlotFacts e Φc (id : (Xn n → ℂ) → (Xn n → ℂ)) (fun _ X => X) :=
  ⟨RowGood.id, (fun S u y => rfl),
    massR_eq_sum_slotExact (e := e) (he := he) (hec := hec) (horth := horth)
      (Φ := Φc) (hΦ := hΦcont) (hΦc := hΦc)⟩

/-- **The one-body slot sum** satisfies the facts: the splitting is the proved
`slotSum_sector_split` and the pointwise decoupling is the proved `boxSlotSum_pairCoord`. -/
theorem SlotFacts.boxSlotSumFacts {e : Fin m → Ω → ℂ} (he : ∀ l, Continuous (e l))
    (hec : ∀ l, HasCompactSupport (e l))
    (horth : ∀ l l', (∫ z : Ω, star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0))
    (hint : ∀ l l', MeasureTheory.Integrable (fun z : Ω => star (e l z) * e l' z))
    {Φc : Xn n → ℂ} (hΦcont : Continuous Φc) (hΦc : HasCompactSupport Φc)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) :
    SlotFacts e Φc (fun Θ : Xn n → ℂ => Work.BoseDict.boxSlotSum e T Θ)
      (fun S => slotSumSub e T S) := by
  refine ⟨(fun X hX => ?_),
    (fun S u y => boxSlotSum_pairCoord e T S Φc he hec horth hint hΦcont hΦc u y), ?_⟩
  · obtain ⟨hm, hb⟩ := boxSlotSum_measurable_bounded (e := e) (he := he) (hec := hec)
      (T := T) (Θ := X) (hΘm := hX.1) (hΘb := hX.2)
    exact ⟨hm, hb⟩
  · have h := congrArg Complex.re (slotSum_sector_split e he hec horth hint T Φc hΦcont hΦc)
    have hsum : (∑ S : Finset (Fin n),
          ∫ x : Xn n, star (slotExact e S Φc x)
            * Work.BoseDict.boxSlotSum e T (slotExact e S Φc) x).re
        = ∑ S : Finset (Fin n),
          (∫ x : Xn n, star (slotExact e S Φc x)
            * Work.BoseDict.boxSlotSum e T (slotExact e S Φc) x).re := by
      simp
    exact h.trans hsum

end Work.BoseBoxFock
