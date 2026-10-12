import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.slotAVgen
import Submission.Work.MB.slotFacts_boxSlotSum_ae
import Submission.Work.MB.slotFacts_dec_fibre_ae
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.MB.AVgen_slotFacts_ae` — `SlotFacts` for `AVgen`, at the weak (measurable/bounded) bundle

`Work.BoseBoxFock.AVgen B idop …` is an eleven-row nested sum in which every row is a real multiple
of a finite sum of one-body rows `B T`, pair rows `(B T₁) ∘ (B T₂)` and of the identity.  Given the
one-body facts `hB`, the pair facts `hBcomp` and the identity facts `hId`, the three fields of
`Work.BoseBoxFock.SlotFacts` therefore hold for the whole `AVgen`
(`Work.BoseBoxFock.AVgen_slotFacts`), *provided* the modes `e l` are continuous with compact
support and the state `Φc` is continuous with compact support — the *strong* bundle.

The strong bundle is **unsatisfiable** at the honest modes of the box ↔ model bridge
(`FINDING_continuous_hypotheses_UNSATISFIABLE.md`: the condensate mode is a.e. the box indicator),
so this module proves the very same theorem at the *weak* bundle of `Submission/Work/MB/`:

* `hmeas : ∀ l, Measurable (e l)`, `hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C`,
  `hsupp : ∀ l, support (e l) ⊆ boxL ℓ`;
* `hΦm : Measurable Φc`, `hΦb : ∃ C, ∀ x, ‖Φc x‖ ≤ C`, `hΦsupp : support Φc ⊆ boxPow n ℓ`.

The strong hypotheses enter the strong proof through exactly two steps, and each is replaced by its
weak twin:

* `slotExact_slotGood` (good *and* compactly supported sector) ↦ `slotAe_sector`
  (`Work.MB.slotExact_mb_weak`: measurable, bounded, and supported in the box — the box support is
  precisely what the compact support was used for);
* `integrable_star_mul_of_compact` ↦ `integrable_star_mul_of_box_support` (the box `boxPow n ℓ` has
  finite measure, so a bounded function supported in it is integrable).

Everything else — the closure of `SlotFacts` under sums, differences and real multiples, the
slice in operator-valued form, and the eleven-row chain — is a transcription of the strong proof
(`Work.BoseBoxFock.AVgen_slotFacts`: this is *not* circular, the hypothesis bundles differ).  The
weak closure lemmas `SlotFacts.{add,sub,smul,zero,finset_sum,finset_smul_sum}_w` and their
operator-valued forms `SlotFacts.…_op_w` are exactly the strong ones with the two replacements above.

Everything here is `sorry`-free.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

open Work.BoseB4 Work.BoseDict

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

variable {m n : ℕ}
variable {ℓ : ℝ}

/-- The weak (measurable, everywhere bounded, box-supported) hypothesis bundle of the mode/state
pair `(e, Φc)`.  It is exactly the bundle of `Submission/Work/MB/`: the modes `e l` are measurable,
everywhere bounded and supported in the corpus box `boxL ℓ`, and the state `Φc` is measurable,
everywhere bounded and supported in the `n`-particle box `boxPow n ℓ`. -/
structure AeWeakBundle (ℓ : ℝ) {m : ℕ} (e : Fin m → Ω → ℂ) {n : ℕ} (Φc : Xn n → ℂ) : Prop where
  hmeas : ∀ l, Measurable (e l)
  hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C
  hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ
  hΦm : Measurable Φc
  hΦb : ∃ C, ∀ x, ‖Φc x‖ ≤ C
  hΦsupp : Function.support Φc ⊆ Work.MB.boxPow n ℓ

/-- The state of a weak bundle is a good state. -/
theorem slotAe_state {e : Fin m → Ω → ℂ} {Φc : Xn n → ℂ} (hw : AeWeakBundle ℓ e Φc) :
    SlotGood Φc := ⟨hw.hΦm, hw.hΦb⟩

/-- The sector of the state of a weak bundle is a good state, and is supported in the box. -/
theorem slotAe_sector {e : Fin m → Ω → ℂ} {Φc : Xn n → ℂ} (hw : AeWeakBundle ℓ e Φc)
    (S : Finset (Fin n)) :
    SlotGood (slotExact e S Φc) ∧ Function.support (slotExact e S Φc) ⊆ Work.MB.boxPow n ℓ := by
  obtain ⟨hm, hb, hs⟩ := Work.MB.slotExact_mb_weak hw.hmeas hw.hbdE hw.hsupp S hw.hΦm hw.hΦb
  obtain ⟨C, -, hC⟩ := hb
  exact ⟨⟨hm, C, hC⟩, hs hw.hΦsupp⟩

/-- `star f * g` is integrable when `f` is measurable, everywhere bounded and supported in the box
`boxPow n ℓ` (of finite measure), and `g` is measurable and everywhere bounded.  This is the weak
replacement of `Work.BoseBoxFock.integrable_star_mul_of_compact` used throughout the closure
lemmas below. -/
theorem integrable_star_mul_of_box_support {n : ℕ} {ℓ : ℝ} {f g : (Fin n → Ω) → ℂ}
    (hfm : Measurable f) (hfb : ∃ C, ∀ x, ‖f x‖ ≤ C)
    (hfs : Function.support f ⊆ Work.MB.boxPow n ℓ)
    (hgm : Measurable g) (hgb : ∃ C, ∀ x, ‖g x‖ ≤ C) :
    Integrable (fun x => star (f x) * g x) := by
  obtain ⟨Cf, hCf⟩ := hfb
  obtain ⟨Cg, hCg⟩ := hgb
  refine Work.MB.integrable_of_bdd_of_support (Work.MB.measurableSet_boxPow n ℓ)
    (Work.MB.volume_boxPow_lt_top n ℓ)
    ((Complex.continuous_conj.measurable.comp hfm).mul hgm).aestronglyMeasurable
    (C := max Cf 0 * max Cg 0) ?_ ?_
  · intro x
    rw [norm_mul, norm_star]
    exact mul_le_mul ((hCf x).trans (le_max_left _ _)) ((hCg x).trans (le_max_left _ _))
      (norm_nonneg _) (le_max_right _ _)
  · intro x hx
    rw [Function.notMem_support.mp (fun h => hx (hfs h)), star_zero, zero_mul]

/-! ## 1. Closure of `SlotFacts` at the weak bundle -/

theorem SlotFacts.add_w {e : Fin m → Ω → ℂ} {Φc : Xn n → ℂ}
    (hw : AeWeakBundle ℓ e Φc)
    {Op1 Op2 : (Xn n → ℂ) → (Xn n → ℂ)}
    {OpS1 OpS2 : (S : Finset (Fin n)) → (({i // i ∈ S} → Ω) → ℂ)
      → (({i // i ∈ S} → Ω) → ℂ)}
    (h1 : SlotFacts e Φc Op1 OpS1) (h2 : SlotFacts e Φc Op2 OpS2) :
    SlotFacts e Φc (Op1 + Op2) (fun S X => OpS1 S X + OpS2 S X) := by
  have hΦ : SlotGood Φc := slotAe_state hw
  have hsec := fun S => slotAe_sector hw S
  refine ⟨RowGood.add h1.good h2.good, ?_, ?_⟩
  · intro S u y
    show Op1 (slotExact e S Φc) (pairCoord S u y) + Op2 (slotExact e S Φc) (pairCoord S u y)
      = OpS1 S (fun u' => slotExact e S Φc (pairCoord S u' y)) u
        + OpS2 S (fun u' => slotExact e S Φc (pairCoord S u' y)) u
    rw [h1.slice S u y, h2.slice S u y]
  · have hi1 : MeasureTheory.Integrable (fun x : Xn n => star (Φc x) * Op1 Φc x) :=
      integrable_star_mul_of_box_support hw.hΦm hw.hΦb hw.hΦsupp (h1.good Φc hΦ).1 (h1.good Φc hΦ).2
    have hi2 : MeasureTheory.Integrable (fun x : Xn n => star (Φc x) * Op2 Φc x) :=
      integrable_star_mul_of_box_support hw.hΦm hw.hΦb hw.hΦsupp (h2.good Φc hΦ).1 (h2.good Φc hΦ).2
    have hj1 : ∀ S : Finset (Fin n), MeasureTheory.Integrable (fun x : Xn n =>
        star (slotExact e S Φc x) * Op1 (slotExact e S Φc) x) := fun S =>
      integrable_star_mul_of_box_support (hsec S).1.1 (hsec S).1.2 (hsec S).2 (h1.good _ (hsec S).1).1 (h1.good _ (hsec S).1).2
    have hj2 : ∀ S : Finset (Fin n), MeasureTheory.Integrable (fun x : Xn n =>
        star (slotExact e S Φc x) * Op2 (slotExact e S Φc) x) := fun S =>
      integrable_star_mul_of_box_support (hsec S).1.1 (hsec S).1.2 (hsec S).2 (h2.good _ (hsec S).1).1 (h2.good _ (hsec S).1).2
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

theorem SlotFacts.zero_w {e : Fin m → Ω → ℂ} {Φc : Xn n → ℂ} (hw : AeWeakBundle ℓ e Φc) :
    SlotFacts e Φc (fun _ : Xn n → ℂ => 0) (fun _ _ => 0) := by
  have h0 : (fun _ : Xn n → ℂ => (0 : Xn n → ℂ)) = fun _ => 0 := rfl
  refine ⟨?_, ?_, ?_⟩
  · intro X hX
    exact SlotGood.zero
  · intro S u y; rfl
  · simp

theorem SlotFacts.smul_w {e : Fin m → Ω → ℂ} {Φc : Xn n → ℂ}
    (hw : AeWeakBundle ℓ e Φc)
    (r : ℝ) {Op : (Xn n → ℂ) → (Xn n → ℂ)}
    {OpS : (S : Finset (Fin n)) → (({i // i ∈ S} → Ω) → ℂ) → (({i // i ∈ S} → Ω) → ℂ)}
    (h : SlotFacts e Φc Op OpS) :
    SlotFacts e Φc (r • Op) (fun S X => r • OpS S X) := by
  have hΦ : SlotGood Φc := slotAe_state hw
  have hsec := fun S => slotAe_sector hw S
  refine ⟨h.good.smul r, ?_, ?_⟩
  · intro S u y
    show r • (Op (slotExact e S Φc) (pairCoord S u y))
      = r • (OpS S (fun u' => slotExact e S Φc (pairCoord S u' y)) u)
    rw [h.slice S u y]
  · have hi : MeasureTheory.Integrable (fun x : Xn n => star (Φc x) * Op Φc x) :=
      integrable_star_mul_of_box_support hw.hΦm hw.hΦb hw.hΦsupp (h.good Φc hΦ).1 (h.good Φc hΦ).2
    have hj : ∀ S : Finset (Fin n), MeasureTheory.Integrable (fun x : Xn n =>
        star (slotExact e S Φc x) * Op (slotExact e S Φc) x) := fun S =>
      integrable_star_mul_of_box_support (hsec S).1.1 (hsec S).1.2 (hsec S).2 (h.good _ (hsec S).1).1 (h.good _ (hsec S).1).2
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

theorem SlotFacts.finset_smul_sum_w {e : Fin m → Ω → ℂ} {Φc : Xn n → ℂ}
    (hw : AeWeakBundle ℓ e Φc)
    {κ : Type*} (s : Finset κ) (r : κ → ℝ)
    {Ops : κ → (Xn n → ℂ) → (Xn n → ℂ)}
    {OpsS : κ → (S : Finset (Fin n)) → (({i // i ∈ S} → Ω) → ℂ) → (({i // i ∈ S} → Ω) → ℂ)}
    (h : ∀ i, SlotFacts e Φc (Ops i) (OpsS i)) :
    SlotFacts e Φc (∑ i ∈ s, r i • Ops i)
      (fun S X => ∑ i ∈ s, r i • OpsS i S X) := by
  classical
  have hΦ : SlotGood Φc := slotAe_state hw
  induction s using Finset.induction with
  | empty =>
      have h0 : (∑ i ∈ (∅ : Finset κ), r i • Ops i) = fun _ : Xn n → ℂ => 0 := by
        funext X x; simp
      have h0S : (fun S X => ∑ i ∈ (∅ : Finset κ), r i • OpsS i S X)
          = fun _ _ => 0 := by
        funext S X; simp
      rw [h0, h0S]
      exact SlotFacts.zero_w hw
  | insert a s ha ih =>
      have hsum : (∑ i ∈ insert a s, r i • Ops i) = r a • Ops a + ∑ i ∈ s, r i • Ops i :=
        Finset.sum_insert ha
      have hsumS : (fun S X => ∑ i ∈ insert a s, r i • OpsS i S X)
          = (fun S X => r a • OpsS a S X + ∑ i ∈ s, r i • OpsS i S X) := by
        funext S X
        rw [Finset.sum_insert ha]
      rw [hsum, hsumS]
      exact ((h a).smul_w hw (r a)).add_w hw ih

theorem SlotFacts.sub_w {e : Fin m → Ω → ℂ} {Φc : Xn n → ℂ}
    (hw : AeWeakBundle ℓ e Φc)
    {Op1 Op2 : (Xn n → ℂ) → (Xn n → ℂ)}
    {OpS1 OpS2 : (S : Finset (Fin n)) → (({i // i ∈ S} → Ω) → ℂ)
      → (({i // i ∈ S} → Ω) → ℂ)}
    (h1 : SlotFacts e Φc Op1 OpS1) (h2 : SlotFacts e Φc Op2 OpS2) :
    SlotFacts e Φc (Op1 - Op2) (fun S X => OpS1 S X - OpS2 S X) := by
  have hΦ : SlotGood Φc := slotAe_state hw
  have hsec := fun S => slotAe_sector hw S
  refine ⟨?_, ?_, ?_⟩
  · intro X hX
    have h : (Op1 - Op2) X = Op1 X - Op2 X := rfl
    rw [h]
    exact (h1.good X hX).sub (h2.good X hX)
  · intro S u y
    show Op1 (slotExact e S Φc) (pairCoord S u y) - Op2 (slotExact e S Φc) (pairCoord S u y)
      = OpS1 S (fun u' => slotExact e S Φc (pairCoord S u' y)) u
        - OpS2 S (fun u' => slotExact e S Φc (pairCoord S u' y)) u
    rw [h1.slice S u y, h2.slice S u y]
  · have hi1 : MeasureTheory.Integrable (fun x : Xn n => star (Φc x) * Op1 Φc x) :=
      integrable_star_mul_of_box_support hw.hΦm hw.hΦb hw.hΦsupp (h1.good Φc hΦ).1 (h1.good Φc hΦ).2
    have hi2 : MeasureTheory.Integrable (fun x : Xn n => star (Φc x) * Op2 Φc x) :=
      integrable_star_mul_of_box_support hw.hΦm hw.hΦb hw.hΦsupp (h2.good Φc hΦ).1 (h2.good Φc hΦ).2
    have hj1 : ∀ S : Finset (Fin n), MeasureTheory.Integrable (fun x : Xn n =>
        star (slotExact e S Φc x) * Op1 (slotExact e S Φc) x) := fun S =>
      integrable_star_mul_of_box_support (hsec S).1.1 (hsec S).1.2 (hsec S).2 (h1.good _ (hsec S).1).1 (h1.good _ (hsec S).1).2
    have hj2 : ∀ S : Finset (Fin n), MeasureTheory.Integrable (fun x : Xn n =>
        star (slotExact e S Φc x) * Op2 (slotExact e S Φc) x) := fun S =>
      integrable_star_mul_of_box_support (hsec S).1.1 (hsec S).1.2 (hsec S).2 (h2.good _ (hsec S).1).1 (h2.good _ (hsec S).1).2
    have hpt1 : (fun x : Xn n => star (Φc x) * (Op1 - Op2) Φc x)
        = fun x : Xn n => star (Φc x) * Op1 Φc x - star (Φc x) * Op2 Φc x := by
      funext x
      simp only [Pi.sub_apply, mul_sub]
    have hpt2 : ∀ S : Finset (Fin n),
        (fun x : Xn n => star (slotExact e S Φc x) * (Op1 - Op2) (slotExact e S Φc) x)
          = fun x : Xn n => star (slotExact e S Φc x) * Op1 (slotExact e S Φc) x
              - star (slotExact e S Φc x) * Op2 (slotExact e S Φc) x := by
      intro S
      funext x
      simp only [Pi.sub_apply, mul_sub]
    calc (∫ x : Xn n, star (Φc x) * (Op1 - Op2) Φc x).re
        = (∫ x : Xn n, (star (Φc x) * Op1 Φc x - star (Φc x) * Op2 Φc x)).re := by
          rw [hpt1]
      _ = ((∫ x : Xn n, star (Φc x) * Op1 Φc x)
            - (∫ x : Xn n, star (Φc x) * Op2 Φc x)).re := by
          rw [MeasureTheory.integral_sub hi1 hi2]
      _ = (∫ x : Xn n, star (Φc x) * Op1 Φc x).re
            - (∫ x : Xn n, star (Φc x) * Op2 Φc x).re := Complex.sub_re _ _
      _ = (∑ S : Finset (Fin n),
              (∫ x : Xn n, star (slotExact e S Φc x) * Op1 (slotExact e S Φc) x).re)
            - ∑ S : Finset (Fin n),
              (∫ x : Xn n, star (slotExact e S Φc x) * Op2 (slotExact e S Φc) x).re := by
          rw [h1.split, h2.split]
      _ = ∑ S : Finset (Fin n),
              ((∫ x : Xn n, star (slotExact e S Φc x) * Op1 (slotExact e S Φc) x).re
                - (∫ x : Xn n, star (slotExact e S Φc x) * Op2 (slotExact e S Φc) x).re) :=
          (Finset.sum_sub_distrib _ _).symm
      _ = ∑ S : Finset (Fin n),
              (∫ x : Xn n, star (slotExact e S Φc x) * (Op1 - Op2) (slotExact e S Φc) x).re := by
          refine Finset.sum_congr rfl (fun S _ => ?_)
          rw [hpt2 S, MeasureTheory.integral_sub (hj1 S) (hj2 S), Complex.sub_re]

theorem SlotFacts.finset_sum_w {e : Fin m → Ω → ℂ} {Φc : Xn n → ℂ}
    (hw : AeWeakBundle ℓ e Φc)
    {κ : Type*} (s : Finset κ)
    {Ops : κ → (Xn n → ℂ) → (Xn n → ℂ)}
    {OpsS : κ → (S : Finset (Fin n)) → (({i // i ∈ S} → Ω) → ℂ) → (({i // i ∈ S} → Ω) → ℂ)}
    (h : ∀ i, SlotFacts e Φc (Ops i) (OpsS i)) :
    SlotFacts e Φc (∑ i ∈ s, Ops i) (fun S X => ∑ i ∈ s, OpsS i S X) := by
  classical
  induction s using Finset.induction with
  | empty =>
      have h0 : (∑ i ∈ (∅ : Finset κ), Ops i) = fun _ : Xn n → ℂ => 0 := by
        funext X x; simp
      have h0S : (fun S X => ∑ i ∈ (∅ : Finset κ), OpsS i S X) = fun _ _ => 0 := by
        funext S X; simp
      rw [h0, h0S]
      exact SlotFacts.zero_w hw
  | insert a s ha ih =>
      have hsum : (∑ i ∈ insert a s, Ops i) = Ops a + ∑ i ∈ s, Ops i := Finset.sum_insert ha
      have hsumS : (fun S X => ∑ i ∈ insert a s, OpsS i S X)
          = (fun S X => OpsS a S X + ∑ i ∈ s, OpsS i S X) := by
        funext S X
        rw [Finset.sum_insert ha]
      rw [hsum, hsumS]
      exact (h a).add_w hw ih


theorem SlotFacts.add_op_w {e : Fin m → Ω → ℂ} {Φc : Xn n → ℂ}
    (hw : AeWeakBundle ℓ e Φc)
    {Op1 Op2 : (Xn n → ℂ) → (Xn n → ℂ)}
    {OpS1 OpS2 : (S : Finset (Fin n)) → (({i // i ∈ S} → Ω) → ℂ)
      → (({i // i ∈ S} → Ω) → ℂ)}
    (h1 : SlotFacts e Φc Op1 OpS1) (h2 : SlotFacts e Φc Op2 OpS2) :
    SlotFacts e Φc (Op1 + Op2) (fun S => OpS1 S + OpS2 S) :=
  SlotFacts.congr (OpS := fun S X => OpS1 S X + OpS2 S X)
    (OpS' := fun S => OpS1 S + OpS2 S) rfl
    (by funext S X; rfl) (SlotFacts.add_w hw h1 h2)


theorem SlotFacts.sub_op_w {e : Fin m → Ω → ℂ} {Φc : Xn n → ℂ}
    (hw : AeWeakBundle ℓ e Φc)
    {Op1 Op2 : (Xn n → ℂ) → (Xn n → ℂ)}
    {OpS1 OpS2 : (S : Finset (Fin n)) → (({i // i ∈ S} → Ω) → ℂ)
      → (({i // i ∈ S} → Ω) → ℂ)}
    (h1 : SlotFacts e Φc Op1 OpS1) (h2 : SlotFacts e Φc Op2 OpS2) :
    SlotFacts e Φc (Op1 - Op2) (fun S => OpS1 S - OpS2 S) :=
  SlotFacts.congr (OpS := fun S X => OpS1 S X - OpS2 S X)
    (OpS' := fun S => OpS1 S - OpS2 S) rfl
    (by funext S X; rfl) (SlotFacts.sub_w hw h1 h2)


theorem SlotFacts.smul_op_w {e : Fin m → Ω → ℂ} {Φc : Xn n → ℂ}
    (hw : AeWeakBundle ℓ e Φc) (r : ℝ)
    {Op : (Xn n → ℂ) → (Xn n → ℂ)}
    {OpS : (S : Finset (Fin n)) → (({i // i ∈ S} → Ω) → ℂ) → (({i // i ∈ S} → Ω) → ℂ)}
    (h : SlotFacts e Φc Op OpS) :
    SlotFacts e Φc (r • Op) (fun S => r • OpS S) :=
  SlotFacts.congr (OpS := fun S X => r • OpS S X)
    (OpS' := fun S => r • OpS S) rfl
    (by funext S X; rfl) (SlotFacts.smul_w hw r h)


theorem SlotFacts.finset_sum_op_w {e : Fin m → Ω → ℂ} {Φc : Xn n → ℂ}
    (hw : AeWeakBundle ℓ e Φc)
    {κ : Type*} (s : Finset κ)
    {Ops : κ → (Xn n → ℂ) → (Xn n → ℂ)}
    {OpsS : κ → (S : Finset (Fin n)) → (({i // i ∈ S} → Ω) → ℂ) → (({i // i ∈ S} → Ω) → ℂ)}
    (h : ∀ i, SlotFacts e Φc (Ops i) (OpsS i)) :
    SlotFacts e Φc (∑ i ∈ s, Ops i) (fun S => ∑ i ∈ s, OpsS i S) :=
  SlotFacts.congr (OpS := fun S X => ∑ i ∈ s, OpsS i S X)
    (OpS' := fun S => ∑ i ∈ s, OpsS i S) rfl
    (by funext S X; simp only [Finset.sum_apply])
    (SlotFacts.finset_sum_w hw s h)


theorem SlotFacts.finset_smul_sum_op_w {e : Fin m → Ω → ℂ} {Φc : Xn n → ℂ}
    (hw : AeWeakBundle ℓ e Φc)
    {κ : Type*} (s : Finset κ) (r : κ → ℝ)
    {Ops : κ → (Xn n → ℂ) → (Xn n → ℂ)}
    {OpsS : κ → (S : Finset (Fin n)) → (({i // i ∈ S} → Ω) → ℂ) → (({i // i ∈ S} → Ω) → ℂ)}
    (h : ∀ i, SlotFacts e Φc (Ops i) (OpsS i)) :
    SlotFacts e Φc (∑ i ∈ s, r i • Ops i) (fun S => ∑ i ∈ s, r i • OpsS i S) :=
  SlotFacts.congr (OpS := fun S X => ∑ i ∈ s, r i • OpsS i S X)
    (OpS' := fun S => ∑ i ∈ s, r i • OpsS i S) rfl
    (by funext S X; simp only [Finset.sum_apply, Pi.smul_apply])
    (SlotFacts.finset_smul_sum_w hw s r h)


/-! ## 2. The weak twin of `AVgen_slotFacts` -/

theorem avgen_slotFacts_ae_aux {m n : ℕ} [NeZero m] {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    {Φc : Work.BoseDict.Xn n → ℂ}
    (hw : AeWeakBundle ℓ e Φc)
    (horth : ∀ l l', (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (hint : ∀ l l', MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) => star (e l z) * e l' z))
    {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (B : ((Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) → ((Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ)))
    (BS : ((Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) → (S : Finset (Fin n))
      → (({i // i ∈ S} → EuclideanSpace ℝ (Fin 3)) → ℂ)
      → (({i // i ∈ S} → EuclideanSpace ℝ (Fin 3)) → ℂ))
    (idop : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ))
    (hB : ∀ T, Work.BoseBoxFock.SlotFacts e Φc (B T) (BS T))
    (hBcomp : ∀ T₁ T₂, Work.BoseBoxFock.SlotFacts e Φc ((B T₁) ∘ (B T₂))
      (fun S X => BS T₁ S (BS T₂ S X)))
    (hId : Work.BoseBoxFock.SlotFacts e Φc idop (fun _ X => X))
    (f g : Mode → Fin m → ℝ) (T_NH : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (PHs : Finset Mode)
    (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) :
    Work.BoseBoxFock.SlotFacts e Φc
      (Work.BoseBoxFock.AVgen B idop f g T_NH PHs E gHat0)
      (fun S => Work.BoseBoxFock.AVgen (fun T => BS T S) (fun X => X) f g T_NH PHs E gHat0) := by
  let r0 : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ) := rankOne (evec0 m)
  -- the rows of `AVgen`
  have h1 := SlotFacts.finset_smul_sum_op_w (e := e) (Φc := Φc) hw
    (κ := Mode) (s := Finset.univ) (r := E.tau)
    (Ops := fun k => B (rankOne (f k))) (OpsS := fun k => BS (rankOne (f k)))
    (fun k : Mode => hB (rankOne (f k)))
  have h2 := SlotFacts.smul_op_w (e := e) (Φc := Φc) hw
    (E.b / (2 * E.ell ^ 2)) (hB (boxT0 m))
  have h3 := SlotFacts.smul_op_w (e := e) (Φc := Φc) hw
    (E.eT * E.b / (2 * E.d ^ 2 * E.ell ^ 2)) (hB T_NH)
  have h4 := SlotFacts.smul_op_w (e := e) (Φc := Φc) hw
    ((1 / 2 : ℝ) * E.ell ^ (-(3 : ℝ)) * (gHat0 + E.W1omega0))
    (SlotFacts.sub_op_w (e := e) (Φc := Φc) hw
      (hBcomp r0 r0) (hB (r0.comp r0)))
  have h5 := SlotFacts.smul_op_w (e := e) (Φc := Φc) hw
    (E.mu * gHat0) (hB r0)
  have h6 := SlotFacts.smul_op_w (e := e) (Φc := Φc) hw
    (E.ell ^ (-(3 : ℝ)))
    (SlotFacts.finset_smul_sum_op_w (e := e) (Φc := Φc) hw
      (κ := Mode) (s := Finset.univ) (r := fun k => E.W1 k + E.W1omega k)
      (fun k : Mode => SlotFacts.sub_op_w (e := e) (Φc := Φc) hw
        (hBcomp (rankOnePair (evec0 m) (f k)) (rankOnePair (f k) (evec0 m)))
        (hB ((rankOnePair (evec0 m) (f k)).comp (rankOnePair (f k) (evec0 m))))))
  have h7 := SlotFacts.smul_op_w (e := e) (Φc := Φc) hw
    ((1 / 2 : ℝ) * E.ell ^ (-(3 : ℝ)))
    (SlotFacts.finset_smul_sum_op_w (e := e) (Φc := Φc) hw
      (κ := Mode) (s := Finset.univ) (r := E.W1)
      (fun k : Mode => SlotFacts.add_op_w (e := e) (Φc := Φc) hw
        (SlotFacts.sub_op_w (e := e) (Φc := Φc) hw
          (hBcomp (rankOnePair (evec0 m) (f k)) (rankOnePair (evec0 m) (f (-k))))
          (hB ((rankOnePair (evec0 m) (f k)).comp (rankOnePair (evec0 m) (f (-k))))))
        (SlotFacts.sub_op_w (e := e) (Φc := Φc) hw
          (hBcomp (rankOnePair (f k) (evec0 m)) (rankOnePair (f (-k)) (evec0 m)))
          (hB ((rankOnePair (f k) (evec0 m)).comp (rankOnePair (f (-k)) (evec0 m)))))))
  have h8 := SlotFacts.finset_smul_sum_op_w (e := e) (Φc := Φc) hw
    (κ := Mode) (s := Finset.univ) (r := E.hatChi)
    (fun k : Mode => SlotFacts.add_op_w (e := e) (Φc := Φc) hw
      (SlotFacts.sub_op_w (e := e) (Φc := Φc) hw
        (SlotFacts.smul_op_w (e := e) (Φc := Φc) hw
          (E.ell ^ (-(3 : ℝ)) * E.W1 0)
          (hBcomp r0 (rankOnePair (f k) (evec0 m))))
        (SlotFacts.smul_op_w (e := e) (Φc := Φc) hw (E.mu * E.W1 0)
          (hB (rankOnePair (f k) (evec0 m)))))
      (SlotFacts.sub_op_w (e := e) (Φc := Φc) hw
        (SlotFacts.smul_op_w (e := e) (Φc := Φc) hw
          (E.ell ^ (-(3 : ℝ)) * E.W1 0)
          (hBcomp (rankOnePair (evec0 m) (f k)) r0))
        (SlotFacts.smul_op_w (e := e) (Φc := Φc) hw (E.mu * E.W1 0)
          (hB (rankOnePair (evec0 m) (f k))))))
  have h9 := SlotFacts.finset_smul_sum_op_w (e := e) (Φc := Φc) hw
    (κ := Mode) (s := Work.BoseB7.excited Mode) (r := E.hatChiSq)
    (fun s : Mode => SlotFacts.add_op_w (e := e) (Φc := Φc) hw
      (SlotFacts.smul_op_w (e := e) (Φc := Φc) hw
        (E.ell ^ (-(3 : ℝ)) * E.W1omega0)
        (hBcomp r0 (rankOnePair (g s) (evec0 m))))
      (SlotFacts.smul_op_w (e := e) (Φc := Φc) hw
        (E.ell ^ (-(3 : ℝ)) * E.W1omega0)
        (hBcomp (rankOnePair (evec0 m) (g s)) r0)))
  have h10 := SlotFacts.finset_sum_op_w (e := e) (Φc := Φc) hw
    (κ := Mode) (s := Finset.univ)
    (fun k : Mode => SlotFacts.sub_op_w (e := e) (Φc := Φc) hw
      (SlotFacts.smul_op_w (e := e) (Φc := Φc) hw
        (E.ell ^ (-(3 : ℝ)) * E.W1 0 + E.ell ^ (-(3 : ℝ)) * E.W1omega0)
        (hBcomp r0 (rankOne (f k))))
      (SlotFacts.smul_op_w (e := e) (Φc := Φc) hw (E.mu * E.W1 0)
        (hB (rankOne (f k)))))
  have h11 := SlotFacts.smul_op_w (e := e) (Φc := Φc) hw
    (E.ell ^ (-(3 : ℝ)))
    (SlotFacts.finset_sum_op_w (e := e) (Φc := Φc) hw
      (κ := Mode) (s := Work.BoseB7.excited Mode)
      (fun s : Mode => SlotFacts.finset_smul_sum_op_w (e := e) (Φc := Φc) hw
        (κ := Mode) (s := PHs) (r := fun k => E.fL s * E.W1 k)
        (fun k : Mode => SlotFacts.sub_op_w (e := e) (Φc := Φc) hw
          (SlotFacts.add_op_w (e := e) (Φc := Φc) hw
            (SlotFacts.sub_op_w (e := e) (Φc := Φc) hw
              (hBcomp (rankOnePair (evec0 m) (f (s - k))) (rankOnePair (g s) (f k)))
              (hB ((rankOnePair (evec0 m) (f (s - k))).comp (rankOnePair (g s) (f k)))))
            (hBcomp (rankOnePair (f k) (g s)) (rankOnePair (f (s - k)) (evec0 m))))
          (hB ((rankOnePair (f k) (g s)).comp (rankOnePair (f (s - k)) (evec0 m)))))))
  have hChain :=
    SlotFacts.add_op_w hw
     (SlotFacts.add_op_w hw
      (SlotFacts.add_op_w hw
       (SlotFacts.add_op_w hw
        (SlotFacts.add_op_w hw
         (SlotFacts.add_op_w hw
          (SlotFacts.sub_op_w hw
           (SlotFacts.add_op_w hw
            (SlotFacts.add_op_w hw
             (SlotFacts.add_op_w hw h1 h2) h3) h4) h5) h6) h7) h8) h9) h10) h11
  have hr0 : r0 = rankOne (evec0 m) := rfl
  rw [hr0] at hChain
  refine SlotFacts.congr ?_ ?_ hChain
  · simp only [AVgen]
  · funext S X
    simp only [AVgen, Finset.sum_apply, Pi.smul_apply, Pi.add_apply, Pi.sub_apply,
      Function.comp_apply]


end Work.BoseBoxFock

/-! ## 3. The requested theorem -/

namespace Work.MB


theorem AVgen_slotFacts_ae {m n : ℕ} [NeZero m] {ℓ : ℝ}
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    {Φc : Work.BoseDict.Xn n → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (hint : ∀ l l', MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) => star (e l z) * e l' z))
    (hΦm : Measurable Φc) (hΦb : ∃ C, ∀ x, ‖Φc x‖ ≤ C)
    (hΦsupp : Function.support Φc ⊆ Work.MB.boxPow n ℓ)
    {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (B : ((Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) → ((Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ)))
    (BS : ((Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) → (S : Finset (Fin n))
      → (({i // i ∈ S} → EuclideanSpace ℝ (Fin 3)) → ℂ)
      → (({i // i ∈ S} → EuclideanSpace ℝ (Fin 3)) → ℂ))
    (idop : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ))
    (hB : ∀ T, Work.BoseBoxFock.SlotFacts e Φc (B T) (BS T))
    (hBcomp : ∀ T₁ T₂, Work.BoseBoxFock.SlotFacts e Φc ((B T₁) ∘ (B T₂))
      (fun S X => BS T₁ S (BS T₂ S X)))
    (hId : Work.BoseBoxFock.SlotFacts e Φc idop (fun _ X => X))
    (f g : Mode → Fin m → ℝ) (T_NH : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (PHs : Finset Mode)
    (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) :
    Work.BoseBoxFock.SlotFacts e Φc
      (Work.BoseBoxFock.AVgen B idop f g T_NH PHs E gHat0)
      (fun S => Work.BoseBoxFock.AVgen (fun T => BS T S) (fun X => X) f g T_NH PHs E gHat0) := by
  exact Work.BoseBoxFock.avgen_slotFacts_ae_aux (ℓ := ℓ) ⟨hmeas, hbdE, hsupp, hΦm, hΦb, hΦsupp⟩
    horth hint B BS idop hB hBcomp hId f g T_NH PHs E gHat0

end Work.MB
