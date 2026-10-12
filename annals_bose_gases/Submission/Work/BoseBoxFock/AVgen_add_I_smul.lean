import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Submission.Work.BoseBoxFock.slotAVgen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.AVgen_add_I_smul` — `AVgen` is `ℂ`-linear on good states

`Work.BoseBoxFock.AVgen B idop` is a nested combination (sums, differences, real multiples and
compositions) of the one-body slot sums `B T`.  Its *atoms* — the operators `B T` — are defined by
Bochner integrals in the state, so they are additive and `ℂ`-homogeneous only on the *good* states
(measurable and pointwise bounded).

This file fixes the class `GenLin` of operators `s` that

* preserve good states (`RowGood`), and
* are additive and `ℂ`-homogeneous on good states,

proves that `GenLin` is closed under sums, differences, real multiples, compositions and finite
sums (mirroring the closure of `AVLin` in `Work.BoseBoxFock.AVGoodState`), proves the base instance
for `B T = boxSlotSum e T` (via the public `boxSlotSum_measurable_bounded` and
`boxSlotSum_finset_sum`), and assembles the eleven rows of `AVgen` (`GenLin_AVgen`).

**Import note.**  This module deliberately does **not** import `Work.BoseBoxFock.AVGoodState`: that
module re-declares `etaOf_continuous`/`etaOf_hasCompactSupport`, which
`Work.BoseBoxFock.boxSlotSum_measurable_bounded` (already in the cone of `slotFacts`, hence of this
module) also declares, so the two cannot coexist in one import cone.  The class of states is
therefore the one of `Work.BoseBoxFock.slotFacts`, `SlotGood`, and the linearity predicate is the
local `GenLin` (a `SlotGood`-analogue of `AVLin`).

Everything here is `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

open Work.BoseB4 Work.BoseDict

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

/-! ## 1. The linearity predicate `GenLin` -/

/-- An operator on states `((ι → Ω) → ℂ)` that preserves good states and is `ℂ`-linear on them.
This is the `SlotGood`-analogue of `Work.BoseBoxFock.AVLin` (which is stated for `AVGood`); it is
kept separate because `AVGoodState` cannot be imported next to `boxSlotSum_measurable_bounded`. -/
structure GenLin {ι : Type*} (s : ((ι → Ω) → ℂ) → ((ι → Ω) → ℂ)) : Prop where
  good : RowGood s
  add : ∀ X Y, SlotGood X → SlotGood Y → s (X + Y) = s X + s Y
  smul : ∀ (c : ℂ) X, SlotGood X → s (c • X) = c • s X

namespace GenLin

variable {ι : Type*} {s t : ((ι → Ω) → ℂ) → ((ι → Ω) → ℂ)}

protected lemma congrLin (h : s = t) (ht : GenLin t) : GenLin s := h ▸ ht

protected lemma idLin : GenLin (id : ((ι → Ω) → ℂ) → ((ι → Ω) → ℂ)) :=
  ⟨RowGood.id, fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩

protected lemma addLin (hs : GenLin s) (ht : GenLin t) : GenLin (s + t) := by
  refine ⟨RowGood.add hs.good ht.good, fun X Y hX hY => ?_, fun c X hX => ?_⟩
  · funext x
    simp only [Pi.add_apply, hs.add X Y hX hY, ht.add X Y hX hY]
    ring
  · funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hs.smul c X hX, ht.smul c X hX]
    ring

protected lemma subLin (hs : GenLin s) (ht : GenLin t) : GenLin (s - t) := by
  refine ⟨RowGood.sub hs.good ht.good, fun X Y hX hY => ?_, fun c X hX => ?_⟩
  · funext x
    simp only [Pi.add_apply, Pi.sub_apply, hs.add X Y hX hY, ht.add X Y hX hY]
    ring
  · funext x
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hs.smul c X hX, ht.smul c X hX]
    ring

protected lemma negLin (hs : GenLin s) : GenLin (-s) := by
  refine ⟨RowGood.neg hs.good, fun X Y hX hY => ?_, fun c X hX => ?_⟩
  · funext x
    simp only [Pi.add_apply, Pi.neg_apply, hs.add X Y hX hY]
    ring
  · funext x
    simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hs.smul c X hX]
    ring

protected lemma smulLin (hs : GenLin s) (c : ℂ) : GenLin (c • s) := by
  refine ⟨RowGood.smul c hs.good, fun X Y hX hY => ?_, fun e X hX => ?_⟩
  · funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hs.add X Y hX hY]
    ring
  · funext x
    simp only [Pi.smul_apply, smul_eq_mul, hs.smul e X hX]
    ring

/-- Real scalar multiples are `ℂ`-scalar multiples (on the `ℂ`-module of states). -/
protected lemma realSmulLin (hs : GenLin s) (r : ℝ) : GenLin (r • s) := by
  have h : (r • s) = ((r : ℂ) • s) := by
    funext X x
    simp only [Pi.smul_apply, Complex.real_smul, smul_eq_mul]
  exact GenLin.congrLin h (hs.smulLin (r : ℂ))

protected lemma compLin {g : ((ι → Ω) → ℂ) → ((ι → Ω) → ℂ)} (hg : GenLin g) (ht : GenLin t) :
    GenLin (g ∘ t) := by
  refine ⟨RowGood.comp hg.good ht.good, fun X Y hX hY => ?_, fun c X hX => ?_⟩
  · simp only [Function.comp_apply]
    rw [ht.add X Y hX hY, hg.add _ _ (ht.good X hX) (ht.good Y hY)]
  · simp only [Function.comp_apply]
    rw [ht.smul c X hX, hg.smul c _ (ht.good X hX)]

protected lemma sumLin {κ : Type*} [DecidableEq κ] (s : Finset κ)
    {Ops : κ → ((ι → Ω) → ℂ) → ((ι → Ω) → ℂ)} (h : ∀ i, GenLin (Ops i)) :
    GenLin (∑ i ∈ s, Ops i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      have h0 : (∑ i ∈ (∅ : Finset κ), Ops i)
          = (fun _ : (ι → Ω) → ℂ => fun _ : ι → Ω => (0 : ℂ)) := by
        funext X x
        simp
      rw [h0]
      exact ⟨RowGood.constFun 0, fun X Y _ _ => by funext x; simp, fun c X _ => by funext x; simp⟩
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (h a).addLin ih

protected lemma sumLin_univ {κ : Type*} [Fintype κ] [DecidableEq κ]
    {Ops : κ → ((ι → Ω) → ℂ) → ((ι → Ω) → ℂ)} (h : ∀ i, GenLin (Ops i)) :
    GenLin (∑ i, Ops i) :=
  GenLin.sumLin Finset.univ h

end GenLin

/-! ## 2. The base instance: `boxSlotSum` is `GenLin`

The atoms of `AVgen` are the one-body slot sums `boxSlotSum e T`.  Their regularity comes from the
public `Work.BoseBoxFock.boxSlotSum_measurable_bounded`, their linearity in the state from the
public `Work.BoseBoxFock.boxSlotSum_finset_sum`. -/

/-- `boxSlotSum e T` is `ℂ`-linear and good-preserving on good states. -/
theorem GenLin_boxSlotSum {m d : ℕ} {e : Fin m → Sp → ℂ}
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) :
    GenLin (fun Θ : Xn d → ℂ => Work.BoseDict.boxSlotSum e T Θ) := by
  refine ⟨fun Θ hΘ => boxSlotSum_measurable_bounded e he hec T Θ hΘ.1 hΘ.2, ?_, ?_⟩
  · intro Φ Ψ hΦ hΨ
    have h := boxSlotSum_finset_sum (e := e) he hec T (Finset.univ : Finset (Fin 2))
      (fun _ : Fin 2 => (1 : ℂ)) (fun i : Fin 2 => if i = 0 then Φ else Ψ)
      (fun i => by
        by_cases hi : i = 0
        · simpa [hi] using hΦ.1
        · simpa [hi] using hΨ.1)
      (fun i => by
        by_cases hi : i = 0
        · simpa [hi] using hΦ.2
        · simpa [hi] using hΨ.2)
    have h1 : (fun x : Xn d => Finset.sum Finset.univ
        (fun i : Fin 2 =>
          (fun _ : Fin 2 => (1 : ℂ)) i • (fun i : Fin 2 => if i = 0 then Φ else Ψ) i x))
        = Φ + Ψ := by
      funext x
      simp
    have h2 : (fun x : Xn d => Finset.sum Finset.univ
        (fun i : Fin 2 =>
          (fun _ : Fin 2 => (1 : ℂ)) i •
            Work.BoseDict.boxSlotSum e T ((fun i : Fin 2 => if i = 0 then Φ else Ψ) i) x))
        = Work.BoseDict.boxSlotSum e T Φ + Work.BoseDict.boxSlotSum e T Ψ := by
      funext x
      simp
    rw [← h1, h, h2]
  · intro c Φ hΦ
    have h := boxSlotSum_finset_sum (e := e) he hec T (Finset.univ : Finset (Fin 2))
      (fun i : Fin 2 => if i = 0 then c else 0) (fun _ : Fin 2 => Φ)
      (fun _ => hΦ.1) (fun _ => hΦ.2)
    have h1 : (fun x : Xn d => Finset.sum Finset.univ
        (fun i : Fin 2 =>
          (fun i : Fin 2 => if i = 0 then c else 0) i • (fun _ : Fin 2 => Φ) i x))
        = c • Φ := by
      funext x
      simp
    have h2 : (fun x : Xn d => Finset.sum Finset.univ
        (fun i : Fin 2 =>
          (fun i : Fin 2 => if i = 0 then c else 0) i •
            Work.BoseDict.boxSlotSum e T ((fun _ : Fin 2 => Φ) i) x))
        = c • Work.BoseDict.boxSlotSum e T Φ := by
      funext x
      simp
    rw [← h1, h, h2]

/-! ## 3. The eleven rows of `AVgen`

The body of `AVgen` is the left-associated chain
`R₁ + R₂ + R₃ + R₄ − R₅ + R₆ + R₇ + R₈ + R₉ + R₁₀ + R₁₁` of the eleven rows, each of which is a
real multiple of a one-body sum `B T`, of a composition `(B T₁) ∘ (B T₂)`, or of a difference of
the two; each is therefore `GenLin`, and the chain is `GenLin` by the closure lemmas. -/

/-- **`GenLin` for `AVgen`.**  Every row of `AVgen` is a real multiple of a one-body slot sum
`B T` or of a composition of two of them (possibly minus `B (T₁ ∘ₗ T₂)`), so the claim follows from
`hB` and the closure of `GenLin` under sums, differences, real multiples and compositions. -/
theorem GenLin_AVgen {m : ℕ} [NeZero m] {ι : Type*}
    (B : ((Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) → ((ι → Ω) → ℂ) → ((ι → Ω) → ℂ))
    (hB : ∀ T, GenLin (B T))
    (idop : ((ι → Ω) → ℂ) → ((ι → Ω) → ℂ))
    {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (T_NH : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (PHs : Finset Mode)
    (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) :
    GenLin (AVgen B idop f g T_NH PHs E gHat0) := by
  unfold AVgen
  refine GenLin.addLin ?_ ?_                                   -- R₁+…+R₁₀  vs  R₁₁
  · refine GenLin.addLin ?_ ?_                                 -- …+R₉ vs R₁₀
    · refine GenLin.addLin ?_ ?_                               -- …+R₈ vs R₉
      · refine GenLin.addLin ?_ ?_                             -- …+R₇ vs R₈
        · refine GenLin.addLin ?_ ?_                           -- …+R₆ vs R₇
          · refine GenLin.addLin ?_ ?_                         -- R₁+…−R₅ vs R₆
            · refine GenLin.subLin ?_ ?_                       -- R₁+…+R₄ vs R₅
              · refine GenLin.addLin ?_ ?_                     -- R₁+R₂+R₃ vs R₄
                · refine GenLin.addLin ?_ ?_                   -- R₁+R₂ vs R₃
                  · refine GenLin.addLin ?_ ?_                 -- R₁ vs R₂
                    · -- R₁: the kinetic row
                      refine GenLin.sumLin_univ (fun k => ?_)
                      exact (hB (rankOne (f k))).realSmulLin (E.tau k)
                    · -- R₂: the gap row
                      exact (hB (boxT0 m)).realSmulLin (E.b / (2 * E.ell ^ 2))
                  · -- R₃: the `n₊^H`-gap row
                    exact (hB T_NH).realSmulLin (E.eT * E.b / (2 * E.d ^ 2 * E.ell ^ 2))
                · -- R₄: the contact row
                  refine GenLin.realSmulLin ?_ _
                  refine GenLin.subLin ?_ ?_
                  · exact GenLin.compLin (hB (rankOne (evec0 m))) (hB (rankOne (evec0 m)))
                  · exact hB ((rankOne (evec0 m)).comp (rankOne (evec0 m)))
              · -- R₅: the chemical-potential row (subtracted)
                exact (hB (rankOne (evec0 m))).realSmulLin (E.mu * gHat0)
            · -- R₆: the `(Ŵ₁+Ŵ₁ω)a₀†a_k†a_ka₀` row
              refine GenLin.realSmulLin ?_ _
              refine GenLin.sumLin_univ (fun k => ?_)
              refine GenLin.realSmulLin ?_ _
              exact GenLin.subLin
                (GenLin.compLin (hB (rankOnePair (evec0 m) (f k)))
                  (hB (rankOnePair (f k) (evec0 m))))
                (hB ((rankOnePair (evec0 m) (f k)).comp (rankOnePair (f k) (evec0 m))))
          · -- R₇: the Bogoliubov-pair row
            refine GenLin.realSmulLin ?_ _
            refine GenLin.sumLin_univ (fun k => ?_)
            refine GenLin.realSmulLin ?_ _
            refine GenLin.addLin ?_ ?_
            · exact GenLin.subLin
                (GenLin.compLin (hB (rankOnePair (evec0 m) (f k)))
                  (hB (rankOnePair (evec0 m) (f (-k)))))
                (hB ((rankOnePair (evec0 m) (f k)).comp (rankOnePair (evec0 m) (f (-k)))))
            · exact GenLin.subLin
                (GenLin.compLin (hB (rankOnePair (f k) (evec0 m)))
                  (hB (rankOnePair (f (-k)) (evec0 m))))
                (hB ((rankOnePair (f k) (evec0 m)).comp (rankOnePair (f (-k)) (evec0 m))))
        · -- R₈: the `χ̂`-linear row
          refine GenLin.sumLin_univ (fun k => ?_)
          refine GenLin.realSmulLin ?_ _
          refine GenLin.addLin ?_ ?_
          · refine GenLin.subLin ?_ ?_
            · refine GenLin.realSmulLin ?_ _
              exact GenLin.compLin (hB (rankOne (evec0 m)))
                (hB (rankOnePair (f k) (evec0 m)))
            · exact (hB (rankOnePair (f k) (evec0 m))).realSmulLin (E.mu * E.W1 0)
          · refine GenLin.subLin ?_ ?_
            · refine GenLin.realSmulLin ?_ _
              exact GenLin.compLin (hB (rankOnePair (evec0 m) (f k)))
                (hB (rankOne (evec0 m)))
            · exact (hB (rankOnePair (evec0 m) (f k))).realSmulLin (E.mu * E.W1 0)
      · -- R₉: the `χ̂²`-linear row
        refine GenLin.sumLin (Work.BoseB7.excited Mode) (fun s => ?_)
        refine GenLin.realSmulLin ?_ _
        refine GenLin.addLin ?_ ?_
        · refine GenLin.realSmulLin ?_ _
          exact GenLin.compLin (hB (rankOne (evec0 m)))
            (hB (rankOnePair (g s) (evec0 m)))
        · refine GenLin.realSmulLin ?_ _
          exact GenLin.compLin (hB (rankOnePair (evec0 m) (g s)))
            (hB (rankOne (evec0 m)))
    · -- R₁₀: the `(L₀+L₁)∘Σ_k a_k†a_k` row
      refine GenLin.sumLin_univ (fun k => ?_)
      refine GenLin.subLin ?_ ?_
      · refine GenLin.realSmulLin ?_ _
        exact GenLin.compLin (hB (rankOne (evec0 m))) (hB (rankOne (f k)))
      · exact (hB (rankOne (f k))).realSmulLin (E.mu * E.W1 0)
  · -- R₁₁: the cubic `Q̃₃` row
    refine GenLin.realSmulLin ?_ _
    refine GenLin.sumLin (Work.BoseB7.excited Mode) (fun s => ?_)
    refine GenLin.sumLin PHs (fun k => ?_)
    refine GenLin.realSmulLin ?_ _
    refine GenLin.subLin ?_ ?_
    · refine GenLin.addLin ?_ ?_
      · exact GenLin.subLin
          (GenLin.compLin (hB (rankOnePair (evec0 m) (f (s - k))))
            (hB (rankOnePair (g s) (f k))))
          (hB ((rankOnePair (evec0 m) (f (s - k))).comp (rankOnePair (g s) (f k))))
      · exact GenLin.compLin (hB (rankOnePair (f k) (g s)))
          (hB (rankOnePair (f (s - k)) (evec0 m)))
    · exact hB ((rankOnePair (f k) (g s)).comp (rankOnePair (f (s - k)) (evec0 m)))

/-! ## 4. The target -/

/-- **`AVgen` is `ℂ`-linear on good states.**  This is the `hAF` input of
`Work.BoseBoxFock.exists_binary_le_apply`.  Every atom of `AVgen` is a real multiple of a one-body
slot sum `boxSlotSum e T` or of a composition of two of them; `boxSlotSum_finset_sum` gives
`ℂ`-linearity of `boxSlotSum e T` on finite *good*-state combinations, and a composition inherits it
(the inner image is good and measurable by `boxSlotSum_measurable_bounded`). -/
theorem AVgen_add_I_smul {m n : ℕ} [NeZero m] {e : Fin m → Work.BoseDict.Sp → ℂ}
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (T_NH : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (PHs : Finset Mode)
    (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ)
    (u v : Work.BoseDict.Xn n → ℂ) (hu : Work.BoseBoxFock.SlotGood u)
    (hv : Work.BoseBoxFock.SlotGood v) :
    Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
        (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ)) f g T_NH PHs E gHat0
        (u + Complex.I • v)
      = Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
          (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ)) f g T_NH PHs E gHat0 u
        + Complex.I • Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
          (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ)) f g T_NH PHs E gHat0 v := by
  have hlin : GenLin (AVgen (ι := Fin n) (fun T => Work.BoseDict.boxSlotSum e T)
      (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ))
      f g T_NH PHs E gHat0) :=
    GenLin_AVgen (fun T => Work.BoseDict.boxSlotSum e T)
      (fun T => GenLin_boxSlotSum (d := n) he hec T)
      (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ)) f g T_NH PHs E gHat0
  rw [hlin.add u (Complex.I • v) hu (SlotGood.smul Complex.I hv),
    hlin.smul Complex.I v hv]

end Work.BoseBoxFock
