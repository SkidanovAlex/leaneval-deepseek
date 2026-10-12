import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.boxRealise_H2ndF
import Submission.Work.BoseBoxFock.boxRealise_reg
import Submission.Work.BoseBoxFock.dGamma_pairWord
import Submission.Work.BoseBoxFock.slotAVgen
import Submission.Work.BoseDict.dGamma_degree
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.AVgenDictGen

/-! ## The general-degree halves of the `H2ndF` ↔ `AVgen` dictionary

`Work.BoseBoxFock.boxRealise_H2ndF` (and consequently `Work.BoseBoxFock.cIPn_AVgen`) is stated
only at degree `d + 2`, because `Work.BoseBoxFock.AVf` and its twins `bW2`, `bW4`, `L0box`,
`L1box` are attached to `Xn (d+2)`.  The slot twin `Work.BoseBoxFock.AVgen` of `H2ndF`
(`Work.BoseBoxFock.slotAVgen`), on the other hand, is *polymorphic* in the number of slots: its
atoms are one-body slot sums `Work.BoseDict.boxSlotSum e T` or compositions of two of them, and
those transport along `Work.BoseDict.boxRealise` at *every* degree by
`Work.BoseDict.boxRealise_dGamma` (which is stated for arbitrary `d`), applied twice for a pair
row after the normal-ordering identity `Work.BoseBoxFock.dGamma_pairWord`.

The lemmas in this section are exactly those general-degree leaves. -/

section LeafGen

open Work.BoseB4 Work.BoseDict Work.BoseBoxFock
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {m : ℕ} [NeZero m] {ℓ : ℝ} {e : Fin m → Sp → ℂ}

/-- `boxSlotSum e · Θ` is additive in the one-body operator: it is a finite sum of finitely many
`• boxSlotOf`, and the pointwise scalar is the evaluation of the operator. -/
theorem boxSlotSum_sub {d : ℕ} (T₁ T₂ : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (Θ : Xn d → ℂ) :
    boxSlotSum e (T₁ - T₂) Θ = boxSlotSum e T₁ Θ - boxSlotSum e T₂ Θ := by
  simp only [boxSlotSum, LinearMap.sub_apply, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]

/-- `boxT0 m = 1 - |e₀⟩⟨e₀|`: the one-body operator whose second quantisation is the excited
number `nExc = N - n₀` is the complement of the rank-one projector onto the coordinate mode. -/
theorem boxT0_eq_sub : boxT0 m = 1 - rankOne (evec0 m) := by
  have hsum : ∀ v : Fin m → ℝ, (∑ l : Fin m, (evec0 m) l * v l) = v 0 := by
    intro v
    rw [Finset.sum_eq_single (0 : Fin m)]
    · simp [evec0, evec]
    · intro b _ hb
      simp [evec0, evec, hb]
    · intro h0
      exact absurd (Finset.mem_univ (0 : Fin m)) h0
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.sub_apply, Module.End.one_apply, boxT0_apply, rankOne_eq_rankOnePair,
    rankOnePair_apply]
  rw [hsum v]
  simp only [evec0]

/-- **The one-body (`|w⟩⟨w|`) dictionary at an arbitrary degree.** -/
theorem boxRealise_leaf_bOB_gen {d : ℕ}
    (he : ∀ l l', (∫ x : Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w : Fin m → ℝ) (Ψ : RealFock m)
    (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = d) :
    boxRealise e d (creOf m w (annOf m w Ψ)) = boxSlotSum e (rankOne w) (boxRealise e d Ψ) := by
  rw [show creOf m w (annOf m w Ψ) = ((creOf m w).comp (annOf m w)) Ψ from rfl,
    ← dGamma_rankOne_eq w]
  exact boxRealise_dGamma he hbdd hsupp (rankOne w) Ψ hΨ

/-- **The two-letter (`|w⟩⟨v|`) dictionary at an arbitrary degree.** -/
theorem boxRealise_leaf_bV2_gen {d : ℕ}
    (he : ∀ l l', (∫ x : Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w v : Fin m → ℝ) (Ψ : RealFock m)
    (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = d) :
    boxRealise e d (creOf m w (annOf m v Ψ))
      = boxSlotSum e (rankOnePair w v) (boxRealise e d Ψ) := by
  rw [show creOf m w (annOf m v Ψ) = ((creOf m w).comp (annOf m v)) Ψ from rfl,
    ← dGamma_rankOnePair w v]
  exact boxRealise_dGamma he hbdd hsupp (rankOnePair w v) Ψ hΨ

/-- The two-letter word `creOf w ∘ annOf v` preserves the degree. -/
theorem deg_word2 {d : ℕ} (w v : Fin m → ℝ) (Ψ : RealFock m)
    (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = d) :
    ∀ α ∈ (creOf m w (annOf m v Ψ)).support, α.sum (fun _ k => k) = d := by
  rw [show creOf m w (annOf m v Ψ) = ((creOf m w).comp (annOf m v)) Ψ from rfl,
    ← dGamma_rankOnePair w v]
  exact dGamma_degree (rankOnePair w v) Ψ d hΨ

/-- The condensate number operator `n₀` preserves the degree. -/
theorem deg_n0 {d : ℕ} (Ψ : RealFock m)
    (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = d) :
    ∀ α ∈ (n0 Ψ).support, α.sum (fun _ k => k) = d := by
  rw [n0, LinearMap.comp_apply, cre_eq_creOf_evec0, ann_eq_annOf_evec0]
  exact deg_word2 (evec0 m) (evec0 m) Ψ hΨ

/-- **The `n₀` dictionary at an arbitrary degree.** -/
theorem boxRealise_n0_gen {d : ℕ}
    (he : ∀ l l', (∫ x : Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (X : RealFock m) (hX : ∀ α ∈ X.support, α.sum (fun _ k => k) = d) :
    boxRealise e d (n0 X) = boxSlotSum e (rankOne (evec0 m)) (boxRealise e d X) := by
  rw [n0, LinearMap.comp_apply, cre_eq_creOf_evec0, ann_eq_annOf_evec0]
  exact boxRealise_leaf_bOB_gen he hbdd hsupp (evec0 m) X hX

/-- **The four-letter dictionary at an arbitrary degree**, in the normal-ordered slot form

`B(|w₁⟩⟨v₁|) ∘ B(|w₂⟩⟨v₂|) − B(|w₁⟩⟨v₁| ∘ |w₂⟩⟨v₂|)`,

which is the shape of the pair rows of `Work.BoseBoxFock.AVgen`. -/
theorem boxRealise_leaf_bV4_gen {d : ℕ}
    (he : ∀ l l', (∫ x : Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w₁ w₂ v₁ v₂ : Fin m → ℝ) (Ψ : RealFock m)
    (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = d) :
    boxRealise e d (creOf m w₁ (creOf m w₂ (annOf m v₁ (annOf m v₂ Ψ))))
      = boxSlotSum e (rankOnePair w₁ v₁)
          (boxSlotSum e (rankOnePair w₂ v₂) (boxRealise e d Ψ))
        - boxSlotSum e ((rankOnePair w₁ v₁).comp (rankOnePair w₂ v₂)) (boxRealise e d Ψ) := by
  have h := congrArg (fun L : RealFock m →ₗ[ℝ] RealFock m => L Ψ)
    (dGamma_pairWord (m := m) w₁ w₂ v₁ v₂)
  simp only [LinearMap.sub_apply, LinearMap.comp_apply] at h
  rw [← h, map_sub,
    boxRealise_dGamma he hbdd hsupp (rankOnePair w₁ v₁) ((dGamma m (rankOnePair w₂ v₂)) Ψ)
      (dGamma_degree (rankOnePair w₂ v₂) Ψ d hΨ),
    boxRealise_dGamma he hbdd hsupp (rankOnePair w₂ v₂) Ψ hΨ,
    boxRealise_dGamma he hbdd hsupp ((rankOnePair w₁ v₁).comp (rankOnePair w₂ v₂)) Ψ hΨ]

/-- **The `L₀` dictionary**: the box realisation of `L₀ = ℓ⁻³Ŵ₁(0) n₀ − μŴ₁(0)` is the
corresponding combination of the slot sum of `|e₀⟩⟨e₀|` and the identity. -/
theorem boxRealise_rowL0F_gen {d : ℕ} {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (he : ∀ l l', (∫ x : Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (E : Work.BoseB7.Q3Env Mode) (X : RealFock m)
    (hX : ∀ α ∈ X.support, α.sum (fun _ k => k) = d) :
    boxRealise e d (L0F E X)
      = (E.ell ^ (-(3 : ℝ)) * E.W1 0) •
          boxSlotSum e (rankOne (evec0 m)) (boxRealise e d X)
        - (E.mu * E.W1 0) • boxRealise e d X := by
  simp only [L0F_eq, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub,
    map_smul, boxRealise_n0_gen he hbdd hsupp X hX]

/-- **The `L₁` dictionary**: the box realisation of `L₁ = ℓ⁻³Ŵ₁ω(0) n₀`. -/
theorem boxRealise_rowL1F_gen {d : ℕ} {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (he : ∀ l l', (∫ x : Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (E : Work.BoseB7.Q3Env Mode) (X : RealFock m)
    (hX : ∀ α ∈ X.support, α.sum (fun _ k => k) = d) :
    boxRealise e d (L1F E X)
      = (E.ell ^ (-(3 : ℝ)) * E.W1omega0) •
          boxSlotSum e (rankOne (evec0 m)) (boxRealise e d X) := by
  simp only [L1F_eq, LinearMap.smul_apply, map_smul, boxRealise_n0_gen he hbdd hsupp X hX]

/-- **The gap row.** The box realisation of `N − n₀ = dGamma m (boxT0 m)` is the slot sum of
`boxT0 m`: the degree-generic form of `Work.BoseBoxFock.boxRealise_totNum_sub_n0`. -/
theorem boxRealise_totNum_gen {d : ℕ}
    (he : ∀ l l', (∫ x : Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (Ψ : RealFock m) (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = d) :
    boxRealise e d (totNumOp m Ψ)
      = boxSlotSum e (1 : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (boxRealise e d Ψ) := by
  rw [← Work.BoseB4.DGamma_one]
  exact boxRealise_dGamma he hbdd hsupp 1 Ψ hΨ

end LeafGen

section Operator

open Work.BoseB4 Work.BoseDict Work.BoseBoxFock
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-- **The function-level dictionary of the slot twin `AVgen` at an arbitrary degree**: for every
model vector `Ψ` of degree `d`, the box realisation of `H2ndF f g (dGamma m T_NH) PHs E gHat0 Ψ`
is the slot twin applied to the realisation of `Ψ`.  The proof is row by row: `boxRealise` is
pushed to the leaves of `H2ndF`'s expression tree and each leaf is rewritten by the general-degree
dictionary lemmas above; the right-hand side is then unfolded and the two sides coincide
term by term. -/
theorem boxRealise_H2ndF_gen {m : ℕ} [NeZero m] {ℓ : ℝ} {e : Fin m → Sp → ℂ}
    (he : ∀ l l', (∫ x : Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (T_NH : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (PHs : Finset Mode)
    (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) (d : ℕ) (Ψ : RealFock m)
    (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = d) :
    boxRealise e d (H2ndF f g (dGamma m T_NH) PHs E gHat0 Ψ)
      = AVgen (fun T => boxSlotSum e T) (id : (Xn d → ℂ) → (Xn d → ℂ))
          f g T_NH PHs E gHat0 (boxRealise e d Ψ) := by
  have h1 : ∀ x : Mode, boxRealise e d (creOf m (f x) (annOf m (f x) Ψ)) =
      boxSlotSum e (rankOne (f x)) (boxRealise e d Ψ) :=
    fun x => boxRealise_leaf_bOB_gen he hbdd hsupp (f x) Ψ hΨ
  have h2 : boxRealise e d (totNumOp m Ψ) -
        boxSlotSum e (rankOne (evec0 m)) (boxRealise e d Ψ) =
      boxSlotSum e (boxT0 m) (boxRealise e d Ψ) := by
    rw [boxRealise_totNum_gen he hbdd hsupp Ψ hΨ, boxT0_eq_sub, boxSlotSum_sub]
  have h3 : boxRealise e d (dGamma m T_NH Ψ) = boxSlotSum e T_NH (boxRealise e d Ψ) :=
    boxRealise_dGamma he hbdd hsupp T_NH Ψ hΨ
  have h4 : boxRealise e d (cre m 0 (cre m 0 (ann m 0 (ann m 0 Ψ)))) =
      boxSlotSum e (rankOne (evec0 m)) (boxSlotSum e (rankOne (evec0 m)) (boxRealise e d Ψ)) -
        boxSlotSum e ((rankOne (evec0 m)).comp (rankOne (evec0 m))) (boxRealise e d Ψ) := by
    simp only [cre_eq_creOf_evec0, ann_eq_annOf_evec0]
    rw [boxRealise_leaf_bV4_gen he hbdd hsupp (evec0 m) (evec0 m) (evec0 m) (evec0 m) Ψ hΨ]
    simp only [← rankOne_eq_rankOnePair]
  have h5 : boxRealise e d (n0 Ψ) =
      boxSlotSum e (rankOne (evec0 m)) (boxRealise e d Ψ) :=
    boxRealise_n0_gen he hbdd hsupp Ψ hΨ
  have h6 : ∀ x : Mode, boxRealise e d (cre m 0 (creOf m (f x) (annOf m (f x) (ann m 0 Ψ)))) =
      boxSlotSum e (rankOnePair (evec0 m) (f x))
          (boxSlotSum e (rankOnePair (f x) (evec0 m)) (boxRealise e d Ψ)) -
        boxSlotSum e ((rankOnePair (evec0 m) (f x)).comp (rankOnePair (f x) (evec0 m)))
          (boxRealise e d Ψ) := by
    intro x
    simp only [cre_eq_creOf_evec0, ann_eq_annOf_evec0]
    exact boxRealise_leaf_bV4_gen he hbdd hsupp (evec0 m) (f x) (f x) (evec0 m) Ψ hΨ
  have h7a : ∀ x : Mode,
      boxRealise e d (cre m 0 (cre m 0 (annOf m (f x) (annOf m (f (-x)) Ψ)))) =
      boxSlotSum e (rankOnePair (evec0 m) (f x))
          (boxSlotSum e (rankOnePair (evec0 m) (f (-x))) (boxRealise e d Ψ)) -
        boxSlotSum e ((rankOnePair (evec0 m) (f x)).comp (rankOnePair (evec0 m) (f (-x))))
          (boxRealise e d Ψ) := by
    intro x
    simp only [cre_eq_creOf_evec0]
    exact boxRealise_leaf_bV4_gen he hbdd hsupp (evec0 m) (evec0 m) (f x) (f (-x)) Ψ hΨ
  have h7b : ∀ x : Mode,
      boxRealise e d (creOf m (f x) (creOf m (f (-x)) (ann m 0 (ann m 0 Ψ)))) =
      boxSlotSum e (rankOnePair (f x) (evec0 m))
          (boxSlotSum e (rankOnePair (f (-x)) (evec0 m)) (boxRealise e d Ψ)) -
        boxSlotSum e ((rankOnePair (f x) (evec0 m)).comp (rankOnePair (f (-x)) (evec0 m)))
          (boxRealise e d Ψ) := by
    intro x
    simp only [ann_eq_annOf_evec0]
    exact boxRealise_leaf_bV4_gen he hbdd hsupp (f x) (f (-x)) (evec0 m) (evec0 m) Ψ hΨ
  have h8a : ∀ x : Mode, boxRealise e d (L0F E (creOf m (f x) (ann m 0 Ψ))) =
      (E.ell ^ (-(3 : ℝ)) * E.W1 0) •
          boxSlotSum e (rankOne (evec0 m))
            (boxSlotSum e (rankOnePair (f x) (evec0 m)) (boxRealise e d Ψ)) -
        (E.mu * E.W1 0) • boxSlotSum e (rankOnePair (f x) (evec0 m)) (boxRealise e d Ψ) := by
    intro x
    have hdeg : ∀ α ∈ (creOf m (f x) (ann m 0 Ψ)).support, α.sum (fun _ k => k) = d := by
      simp only [ann_eq_annOf_evec0]
      exact deg_word2 (f x) (evec0 m) Ψ hΨ
    rw [boxRealise_rowL0F_gen he hbdd hsupp E (creOf m (f x) (ann m 0 Ψ)) hdeg]
    simp only [ann_eq_annOf_evec0,
      boxRealise_leaf_bV2_gen he hbdd hsupp (f x) (evec0 m) Ψ hΨ]
  have h8b : ∀ x : Mode, boxRealise e d (cre m 0 (annOf m (f x) (L0F E Ψ))) =
      (E.ell ^ (-(3 : ℝ)) * E.W1 0) •
          boxSlotSum e (rankOnePair (evec0 m) (f x))
            (boxSlotSum e (rankOne (evec0 m)) (boxRealise e d Ψ)) -
        (E.mu * E.W1 0) • boxSlotSum e (rankOnePair (evec0 m) (f x)) (boxRealise e d Ψ) := by
    intro x
    simp only [L0F_eq, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub,
      map_smul, cre_eq_creOf_evec0]
    simp only [boxRealise_leaf_bV2_gen he hbdd hsupp (evec0 m) (f x) (n0 Ψ) (deg_n0 Ψ hΨ),
      boxRealise_n0_gen he hbdd hsupp Ψ hΨ,
      boxRealise_leaf_bV2_gen he hbdd hsupp (evec0 m) (f x) Ψ hΨ]
  have h9a : ∀ x : Mode, boxRealise e d (L1F E (creOf m (g x) (ann m 0 Ψ))) =
      (E.ell ^ (-(3 : ℝ)) * E.W1omega0) •
          boxSlotSum e (rankOne (evec0 m))
            (boxSlotSum e (rankOnePair (g x) (evec0 m)) (boxRealise e d Ψ)) := by
    intro x
    have hdeg : ∀ α ∈ (creOf m (g x) (ann m 0 Ψ)).support, α.sum (fun _ k => k) = d := by
      simp only [ann_eq_annOf_evec0]
      exact deg_word2 (g x) (evec0 m) Ψ hΨ
    rw [boxRealise_rowL1F_gen he hbdd hsupp E (creOf m (g x) (ann m 0 Ψ)) hdeg]
    simp only [ann_eq_annOf_evec0,
      boxRealise_leaf_bV2_gen he hbdd hsupp (g x) (evec0 m) Ψ hΨ]
  have h9b : ∀ x : Mode, boxRealise e d (cre m 0 (annOf m (g x) (L1F E Ψ))) =
      (E.ell ^ (-(3 : ℝ)) * E.W1omega0) •
          boxSlotSum e (rankOnePair (evec0 m) (g x))
            (boxSlotSum e (rankOne (evec0 m)) (boxRealise e d Ψ)) := by
    intro x
    simp only [L1F_eq, LinearMap.smul_apply, map_smul, cre_eq_creOf_evec0]
    simp only [boxRealise_leaf_bV2_gen he hbdd hsupp (evec0 m) (g x) (n0 Ψ) (deg_n0 Ψ hΨ),
      boxRealise_n0_gen he hbdd hsupp Ψ hΨ]
  have h10 : (∑ x : Mode, (boxRealise e d (L0F E (creOf m (f x) (annOf m (f x) Ψ))) +
        boxRealise e d (L1F E (creOf m (f x) (annOf m (f x) Ψ))))) =
      ∑ x : Mode, ((E.ell ^ (-(3 : ℝ)) * E.W1 0 + E.ell ^ (-(3 : ℝ)) * E.W1omega0) •
            boxSlotSum e (rankOne (evec0 m))
              (boxSlotSum e (rankOne (f x)) (boxRealise e d Ψ)) -
          (E.mu * E.W1 0) • boxSlotSum e (rankOne (f x)) (boxRealise e d Ψ)) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    have hX : ∀ α ∈ (creOf m (f x) (annOf m (f x) Ψ)).support, α.sum (fun _ k => k) = d :=
      deg_word2 (f x) (f x) Ψ hΨ
    have h0 : boxRealise e d (L0F E (creOf m (f x) (annOf m (f x) Ψ))) =
        (E.ell ^ (-(3 : ℝ)) * E.W1 0) •
            boxSlotSum e (rankOne (evec0 m))
              (boxSlotSum e (rankOne (f x)) (boxRealise e d Ψ)) -
          (E.mu * E.W1 0) • boxSlotSum e (rankOne (f x)) (boxRealise e d Ψ) := by
      simp only [boxRealise_rowL0F_gen he hbdd hsupp E (creOf m (f x) (annOf m (f x) Ψ)) hX,
        boxRealise_leaf_bOB_gen he hbdd hsupp (f x) Ψ hΨ]
    have h0' : boxRealise e d (L1F E (creOf m (f x) (annOf m (f x) Ψ))) =
        (E.ell ^ (-(3 : ℝ)) * E.W1omega0) •
            boxSlotSum e (rankOne (evec0 m))
              (boxSlotSum e (rankOne (f x)) (boxRealise e d Ψ)) := by
      simp only [boxRealise_rowL1F_gen he hbdd hsupp E (creOf m (f x) (annOf m (f x) Ψ)) hX,
        boxRealise_leaf_bOB_gen he hbdd hsupp (f x) Ψ hΨ]
    rw [h0, h0', add_smul]
    abel
  have h11a : ∀ (x : Mode) (x_1 : Mode),
      boxRealise e d (cre m 0 (creOf m (g x) (annOf m (f (x - x_1)) (annOf m (f x_1) Ψ)))) =
      boxSlotSum e (rankOnePair (evec0 m) (f (x - x_1)))
          (boxSlotSum e (rankOnePair (g x) (f x_1)) (boxRealise e d Ψ)) -
        boxSlotSum e ((rankOnePair (evec0 m) (f (x - x_1))).comp (rankOnePair (g x) (f x_1)))
          (boxRealise e d Ψ) := by
    intro x x_1
    simp only [cre_eq_creOf_evec0]
    exact boxRealise_leaf_bV4_gen he hbdd hsupp (evec0 m) (g x) (f (x - x_1)) (f x_1) Ψ hΨ
  have h11b : ∀ (x : Mode) (x_1 : Mode),
      boxRealise e d (creOf m (f x_1) (creOf m (f (x - x_1)) (annOf m (g x) (ann m 0 Ψ)))) =
      boxSlotSum e (rankOnePair (f x_1) (g x))
          (boxSlotSum e (rankOnePair (f (x - x_1)) (evec0 m)) (boxRealise e d Ψ)) -
        boxSlotSum e ((rankOnePair (f x_1) (g x)).comp (rankOnePair (f (x - x_1)) (evec0 m)))
          (boxRealise e d Ψ) := by
    intro x x_1
    simp only [ann_eq_annOf_evec0]
    exact boxRealise_leaf_bV4_gen he hbdd hsupp (f x_1) (f (x - x_1)) (g x) (evec0 m) Ψ hΨ
  simp only [H2ndF, ← L0F_eq, ← L1F_eq, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    map_add, map_sub, map_smul, map_sum]
  simp only [h1, h2, h3, h4, h5, h6, h7a, h7b, h8a, h8b, h9a, h9b, h10, h11a, h11b]
  simp only [AVgen, Finset.sum_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    Function.comp_apply]
  simp only [add_sub_assoc]

end Operator

set_option linter.unusedVariables false

/-- **The all-degree sesquilinear dictionary of the slot twin `AVgen` of `H2ndF`.**

`Work.BoseBoxFock.cIPn_AVgen` proves
`cIPn (d+2) (boxRealise e (d+2) Ψ) (AVgen (boxSlotSum e) id … (boxRealise e (d+2) Ψ'))
   = ↑(bomb m Ψ (H2ndF f g (dGamma m T_NH) PHs E gHat0 Ψ'))`
only for model vectors of degree `d + 2`, since it goes through `AVgen_eq_AVf` and
`boxRealise_H2ndF`, both stated on `Xn (d+2)`.  The BF3c assembly needs the dictionary at the
degree `S.card` of the sector that `Work.BoseBoxFock.exists_slice_le_window_of_op` returns, which
may be `0` or `1`; this supplies all degrees.

Route: no `AVf`.  Every atom of `AVgen` is a one-body slot sum `Work.BoseDict.boxSlotSum e T` or a
composition of two of them, and both transport along `Work.BoseDict.boxRealise` at *every* degree
by `Work.BoseDict.boxRealise_dGamma` (already stated for arbitrary `d`, and already proved at
degree `0`) applied twice, with `Work.BoseDict.dGamma_degree` for the bookkeeping:
* one-body rows of `H2ndF` (`Σ τ_k creOf (f k) ∘ annOf (f k)`, `nExc = totNumOp − n0`,
  `NH = dGamma T_NH`, `n0`): rewrite with `Work.BoseBoxFock.dGamma_rankOne_eq`,
  `Work.BoseBoxFock.nExc_eq_dGamma_boxT0`, `Work.BoseBoxFock.cre_eq_creOf_evec0`,
  `Work.BoseBoxFock.ann_eq_annOf_evec0`, then `boxRealise_dGamma`;
* four-letter rows (`a₀†a₀†a₀a₀`, `(Ŵ₁+Ŵ₁ω)a₀†a_k†a_ka₀`, Bogoliubov pairs, `Q̃₃`): rewrite the
  ladder word with `Work.BoseBoxFock.dGamma_pairWord` (backwards) into
  `dGamma T₁ ∘ dGamma T₂ − dGamma (T₁∘T₂)`, `T_i = rankOnePair …`, then `boxRealise_dGamma`
  twice;
* redistributed `L₀`/`L₁` rows: `L0 = ℓ⁻³Ŵ₁(0)·n₀ − μŴ₁(0)·1` with `n₀ = dGamma (rankOne e₀)`, so
  `L0` transports to the matching combination of `boxSlotSum e (rankOne (evec0 m))` and the
  identity;
* conclude with `Work.BoseDict.boxRealise_cIPn_gen` (degree hypothesis on the *first* argument
  only).  Degenerate `d = 0`: `boxSlotSum e T` is the zero operator on `Xn 0` (empty sum over
  `Fin 0`), matching `dGamma T (vac) = 0`. -/
theorem cIPn_AVgen_gen {m : ℕ} [NeZero m] {ℓ : ℝ} {e : Fin m → Work.BoseDict.Sp → ℂ}
    (hℓ : 0 < ℓ) (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (heorth : ∀ l l', (∫ x : Work.BoseDict.Sp, (starRingEnd ℂ) (e l x) * e l' x)
      = (if l = l' then (1 : ℂ) else 0))
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (T_NH : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (PHs : Finset Mode)
    (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) (d : ℕ) (Ψ Ψ' : Work.BoseB4.RealFock m)
    (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = d)
    (hΨ' : ∀ α ∈ Ψ'.support, α.sum (fun _ k => k) = d) :
    Work.BoseDict.cIPn d (Work.BoseDict.boxRealise e d Ψ)
        (Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
          (id : (Work.BoseDict.Xn d → ℂ) → (Work.BoseDict.Xn d → ℂ))
          f g T_NH PHs E gHat0 (Work.BoseDict.boxRealise e d Ψ'))
      = ((Work.BoseB4.bomb m Ψ (Work.BoseBoxFock.H2ndF f g (Work.BoseB4.dGamma m T_NH)
          PHs E gHat0 Ψ') : ℝ) : ℂ) := by
  rw [← boxRealise_H2ndF_gen heorth hbdd hsupp f g T_NH PHs E gHat0 d Ψ' hΨ']
  exact Work.BoseDict.boxRealise_cIPn_gen heorth hbdd hsupp Ψ
    (Work.BoseBoxFock.H2ndF f g (Work.BoseB4.dGamma m T_NH) PHs E gHat0 Ψ') hΨ

end Work.BoseBoxFock.AVgenDictGen
