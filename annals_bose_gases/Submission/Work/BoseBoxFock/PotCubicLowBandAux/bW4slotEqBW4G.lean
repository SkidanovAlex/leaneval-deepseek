import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.PotCubicLowBandAux.selfPairG
import Submission.Work.BoseBoxFock.sum_boxSlotOf_symm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PotCubicLowBandAux.bW4slotEqBW4G` — the slot form of the pair word *is* the
ladder word, at the weak mode bundle, in a **clash-free** import cone

`Work.BoseBoxFock.bW4slot` (`Submission/Work/BoseBoxFock/slotPairDefs.lean`) is the
*first-quantised* form of the four-letter box word,

    `bW4slot e w₁ w₂ v₁ v₂ d = B(|w₁⟩⟨v₁|) ∘ B(|w₂⟩⟨v₂|) − B(|w₁⟩⟨v₁| ∘ |w₂⟩⟨v₂|)`,
    `B(T) = boxSlotSum e T`,

which is sector-local for the BF3c selection, while `Work.BoseBoxFock.bW4` is the **ladder** word

    `bW4 e w₁ w₂ v₁ v₂ d = C_{w₁} ∘ C_{w₂} ∘ A_{v₁} ∘ A_{v₂}`,
    `C_w = boxCreOf e w`, `A_v = boxAnnOf e v`,

in which the analytic row inequalities are stated.  This file proves that the two agree **on the
symmetric box states** (the physical ones) at the weak hypothesis bundle that the honest box ↔
model modes satisfy: the modes are only *measurable*, *everywhere bounded* and *supported in the
corpus box* `Work.BoseK15.corpusBox.boxL ℓ`, the state is only measurable and everywhere bounded,
and the modes are orthonormal.

## Why this copy exists (the import-cone blocker)

The proved weak twin `Work.BoseBoxFock.bW4slot_eq_bW4_weak`
(`Submission/Work/BoseBoxFock/bW4slot_eq_bW4_weak.lean`) lives in the `AVGoodState` cone: it
imports the weak rank-one slot sum `Work.BoseBoxFock.boxSlotSum_rankOnePair_weak`, whose weak twin
of the strong lemma imports `Work.BoseBoxFock.AVGoodState`.  `AVGoodState` declares
`Work.BoseBoxFock.etaOf_continuous` / `etaOf_hasCompactSupport`, which
`Work.BoseBoxFock.boxSlotSum_measurable_bounded` (in the cone of `frkCore`/`PotCubicHonest`, i.e.
of the cubic chapter that consumes this lemma) declares as well, so the two cones cannot be loaded
into one environment:

    error: import ... AVGoodState failed, environment already contains
    'Work.BoseBoxFock.etaOf_hasCompactSupport' from ... boxSlotSum_measurable_bounded

This module is therefore a **copy of that proof in the clash-free cone** (the `G`-suffix recipe of
`FINDING_PotCubicLowBandG_holds_session1.md` §5): it imports neither `AVGoodState` nor any module
that does, inlines the two weak dictionary lemmas it needs (`boxSlotSum_rankOnePair_weakG`,
`boxAnnOf_boxCreOf_ccr_weakG`), and replaces the `AVGood` class of the original by the local
predicate `Good` (measurable and everywhere bounded), which is all the argument uses.

## The argument (the box twin of `Work.BoseBoxFock.dGamma_pairWord`)

Write `C_w = boxCreOf e w`, `A_v = boxAnnOf e v` and `g = Σ_l v₁ l * w₂ l`.  With
`Λ = B(|w₂⟩⟨v₂|) Θ`, the chain is

    bW4slot Θ = B(|w₁⟩⟨v₁|) Λ − B(|w₁⟩⟨v₁| ∘ |w₂⟩⟨v₂|) Θ
              = C_{w₁} (A_{v₁} Λ) − g • C_{w₁} (A_{v₂} Θ)          (rank-one realisations)
              = C_{w₁} (C_{w₂} (A_{v₁} (A_{v₂} Θ))) = bW4 Θ,

using:

* **second = first quantisation for a rank-one pair**: for a symmetric good state `X`,
  `B(|w⟩⟨v|) X = Σ_j boxSlotOf e w v j X = C_w (A_v X)`
  (`boxSlotSum_rankOnePair_weakG`, the weak twin of `boxSlotSum_rankOnePair`, plus
  `Work.BoseDict.boxCreOf_boxAnnOf_slot`, which needs no mode hypotheses at all);
* the **symmetry of the slot sum** (`Work.BoseBoxFock.sum_boxSlotOf_symm`), which makes `Λ`
  symmetric and so allows the second realisation;
* the **box CCR** `A_v (C_w Z) = C_w (A_v Z) + g • Z` (`boxAnnOf_boxCreOf_ccr_weakG`), the weak
  twin of `Work.BoseBoxFock.boxAnnOf_boxCreOf_ccr`;
* the unconditional `ℂ`-linearity of `boxCreOf` in the state and the `ℝ`-homogeneity of
  `boxSlotSum` in the one-body operator.

Everything here is complete and axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock.PotCubicLowBandAux

open Work.BoseDict

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

/-! ## 0. The good-state predicate — measurable and everywhere bounded

This is the local replacement for `Work.BoseBoxFock.AVGood` (same `def`, different cone). -/

/-- A box state `Θ : Xn n → ℂ` is *good* if it is measurable and everywhere bounded.  These are
exactly the states on which the Bochner integrals defining the box ladder words are linear
(`Integrable.mul_bdd`). -/
def Good {n : ℕ} (Θ : Xn n → ℂ) : Prop :=
  Measurable Θ ∧ ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C

namespace Good

variable {n : ℕ}

protected lemma add {Θ Ψ : Xn n → ℂ} (hΘ : Good Θ) (hΨ : Good Ψ) : Good (Θ + Ψ) := by
  obtain ⟨C₁, h₁⟩ := hΘ.2
  obtain ⟨C₂, h₂⟩ := hΨ.2
  exact ⟨hΘ.1.add hΨ.1, C₁ + C₂, fun x => by
    rw [Pi.add_apply]
    exact (norm_add_le _ _).trans (add_le_add (h₁ x) (h₂ x))⟩

protected lemma smul {Θ : Xn n → ℂ} (c : ℂ) (hΘ : Good Θ) : Good (c • Θ) := by
  obtain ⟨C, hC⟩ := hΘ.2
  refine ⟨hΘ.1.const_smul c, ‖c‖ * C, fun x => ?_⟩
  rw [Pi.smul_apply, norm_smul]
  exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)

protected lemma finset_sum {ι : Type*} (s : Finset ι) {f : ι → Xn n → ℂ}
    (h : ∀ i, Good (f i)) : Good (∑ i ∈ s, f i) := by
  classical
  choose C hC using fun i => (h i).2
  refine ⟨?_, ∑ i ∈ s, C i, fun x => ?_⟩
  · rw [Finset.sum_fn]
    exact Finset.measurable_sum s (fun i _ => (h i).1)
  · rw [Finset.sum_apply]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => hC i x))

protected lemma finset_sum_univ {ι : Type*} [Fintype ι] {f : ι → Xn n → ℂ}
    (h : ∀ i, Good (f i)) : Good (∑ i, f i) :=
  Good.finset_sum Finset.univ h

end Good

/-! ## 1. The `L¹` toolbox of the superposition `η_w = Σ_l w_l e_l` -/

/-- The superposition `η_u` is integrable at the weak bundle. -/
private lemma etaOf_integrable_G {m : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (u : Fin m → ℝ) : Integrable (fun z : Ω => etaOf e u z) :=
  (Work.BoseBoxFock.integrable_etaOf_weakG hmeas hbdd hsupp u).1

/-- `‖η_u‖` is integrable at the weak bundle. -/
private lemma norm_etaOf_integrable_G {m : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (u : Fin m → ℝ) : Integrable (fun z : Ω => ‖etaOf e u z‖) :=
  (Work.BoseBoxFock.integrable_etaOf_weakG hmeas hbdd hsupp u).2

/-- `conj (η_u)` is integrable at the weak bundle. -/
private lemma conj_etaOf_integrable_G {m : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (u : Fin m → ℝ) : Integrable (fun z : Ω => (starRingEnd ℂ) (etaOf e u z)) :=
  Integrable.mono (etaOf_integrable_G hmeas hbdd hsupp u)
    ((continuous_star.measurable.comp
      (Work.MB.etaOf_weak_measurable hmeas u)).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun z => le_of_eq (norm_star _)))

/-! ## 2. The weak rank-one slot sum `B(|w⟩⟨v|) X = Σ_j boxSlotOf e w v j X`

This is the content of `Work.BoseBoxFock.boxSlotSum_rankOnePair_weak`, inlined here so that the
clashing import of its strong twin `boxSlotSum_rankOnePair` (and hence of
`Work.BoseBoxFock.AVGoodState`) is not needed. -/

/-! ### 2a. The coordinate-vector reductions -/

/-- `η` at the coordinate vector `evec m l` is the mode `e l`. -/
private lemma etaOf_evec_G {m : ℕ} (e : Fin m → Ω → ℂ) (l : Fin m) :
    etaOf e (Work.BoseB4.evec m l) = e l := by
  funext z
  simp only [etaOf, Work.BoseB4.evec, Pi.single_apply]
  rw [Finset.sum_eq_single l]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ l) h

/-- The slot at coordinate vectors, in explicit form. -/
private lemma boxSlotOf_evec_eq_G {m d : ℕ} (e : Fin m → Ω → ℂ) (l l' : Fin m) (j : Fin d)
    (Θ : Xn d → ℂ) :
    boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ
      = fun x => e l (x j) * ∫ z : Ω, (starRingEnd ℂ) (e l' z) * Θ (Function.update x j z) := by
  funext x
  simp only [boxSlotOf, etaOf_evec_G]

/-- The sum defining `η_v` at a coordinate vector. -/
private lemma sum_evec_mul_G {m : ℕ} (v : Fin m → ℝ) (l' : Fin m) :
    (∑ k : Fin m, v k * (Work.BoseB4.evec m l' k)) = v l' := by
  rw [Finset.sum_eq_single l']
  · simp [Work.BoseB4.evec]
  · intro b _ hb
    simp [Work.BoseB4.evec, Pi.single_eq_of_ne, hb]
  · intro h; exact absurd (Finset.mem_univ l') h

/-- `(|w⟩⟨v| (evec l'))_l = w_l v_{l'}`. -/
private lemma rankOnePair_evec_G {m : ℕ} (w v : Fin m → ℝ) (l l' : Fin m) :
    rankOnePair w v (Work.BoseB4.evec m l') l = w l * v l' := by
  simp only [rankOnePair_apply, Pi.smul_apply, smul_eq_mul, sum_evec_mul_G]
  ring

/-! ### 2b. Integrability of the slot integrand at the weak bundle -/

/-- The change of variable `z ↦ Function.update x j z` is measurable. -/
private lemma measurable_update_w {d : ℕ} (x : Xn d) (j : Fin d) :
    Measurable (fun z : Ω => Function.update x j z) := by
  refine measurable_pi_iff.mpr (fun i => ?_)
  by_cases hij : i = j
  · subst hij
    simp only [Function.update_apply]
    exact measurable_id
  · simp [hij]

/-- **The slot integrand is integrable at the weak bundle.**  It is measurable, it is bounded by
`max C 0 * max C_Θ 0`, and it is supported in `boxL ℓ`, which has finite measure; hence
`Work.MB.integrable_of_bdd_of_support` applies. -/
private lemma integrable_slotIntegrand_G {m d : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l))
    (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {Θ : Xn d → ℂ} (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (x : Xn d) (j : Fin d) (l : Fin m) :
    Integrable (fun z : Ω => (starRingEnd ℂ) (e l z) * Θ (Function.update x j z)) := by
  obtain ⟨C, hC⟩ := hbdd l
  obtain ⟨C', hC'⟩ := hΘb
  refine Work.MB.integrable_of_bdd_of_support (C := max C 0 * max C' 0)
    (Work.BoseK15.corpusBox.boxL_measurableSet ℓ)
    (Work.BoseK15.corpusBox.boxL_compact ℓ).measure_lt_top.ne
    ((Complex.continuous_conj.measurable.comp (hmeas l)).mul
      (hΘm.comp (measurable_update_w x j))).aestronglyMeasurable ?_ ?_
  · intro z
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul ((hC z).trans (le_max_left _ _)) ((hC' _).trans (le_max_left _ _))
      (norm_nonneg _) (le_max_right _ _)
  · intro z hz
    have hz0 : e l z = 0 := Function.notMem_support.mp (fun h => hz (hsupp l h))
    simp [hz0]

/-! ### 2c. The superposition `η_v` comes out of the integral -/

/-- `∫ z, conj (η_v z) · Θ (x[j ↦ z]) = Σ_{l'} v_{l'} ∫ z, conj (e_{l'} z) · Θ (x[j ↦ z])`. -/
private lemma slotIntegral_etaOf_eq_sum_G {m d : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l))
    (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (v : Fin m → ℝ) (j : Fin d) (x : Xn d) (Θ : Xn d → ℂ)
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) :
    (∫ z : Ω, (starRingEnd ℂ) (etaOf e v z) * Θ (Function.update x j z))
      = ∑ l' : Fin m, (v l' : ℂ) *
          ∫ z : Ω, (starRingEnd ℂ) (e l' z) * Θ (Function.update x j z) := by
  have key : (fun z : Ω => (starRingEnd ℂ) (etaOf e v z) * Θ (Function.update x j z))
      = fun z : Ω => ∑ l' : Fin m,
          (v l' : ℂ) * ((starRingEnd ℂ) (e l' z) * Θ (Function.update x j z)) := by
    funext z
    simp only [etaOf, map_sum, map_mul, Complex.conj_ofReal, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [key, integral_finsetSum _
    (fun l' _ => (integrable_slotIntegrand_G hmeas hbdd hsupp hΘm hΘb x j l').const_mul _)]
  refine Finset.sum_congr rfl (fun l' _ => ?_)
  rw [MeasureTheory.integral_const_mul]

/-! ### 2d. Expansion of a general slot in the coordinate basis -/

/-- **A single slot expands in the coordinate basis** (weak bundle): since `η_w = Σ_l w_l e_l` and
`η_v = Σ_{l'} v_{l'} e_{l'}`, the slot `boxSlotOf e w v j` is the finite linear combination
`Σ_{l,l'} (w_l v_{l'}) • boxSlotOf e (evec l) (evec l') j`. -/
private lemma boxSlotOf_expand_G {m d : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l))
    (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w v : Fin m → ℝ) (j : Fin d) (Θ : Xn d → ℂ)
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) :
    boxSlotOf e w v j Θ
      = ∑ l : Fin m, ∑ l' : Fin m, (w l * v l') •
          boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ := by
  funext x
  have hI := slotIntegral_etaOf_eq_sum_G hmeas hbdd hsupp v j x Θ hΘm hΘb
  have hL : boxSlotOf e w v j Θ x
      = (∑ i : Fin m, (w i : ℂ) * e i (x j)) *
          ∑ b : Fin m, (v b : ℂ) *
            ∫ z : Ω, (starRingEnd ℂ) (e b z) * Θ (Function.update x j z) := by
    rw [show boxSlotOf e w v j Θ x
        = etaOf e w (x j) * ∫ z : Ω, (starRingEnd ℂ) (etaOf e v z) *
            Θ (Function.update x j z) from rfl]
    rw [hI]
    simp only [etaOf]
  have hR : (∑ l : Fin m, ∑ l' : Fin m, (w l * v l') •
      boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ) x
      = ∑ a : Fin m, ∑ b : Fin m, ((w a : ℂ) * (v b : ℂ)) *
          (e a (x j) * ∫ z : Ω, (starRingEnd ℂ) (e b z) *
            Θ (Function.update x j z)) := by
    simp only [Finset.sum_apply, Pi.smul_apply, boxSlotOf_evec_eq_G, Complex.real_smul,
      Complex.ofReal_mul]
  rw [hL, hR, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by ring))

/-! ### 2e. The rank-one slot sum -/

theorem boxSlotSum_rankOnePair_weakG {m d : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l))
    (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w v : Fin m → ℝ) (Θ : Xn d → ℂ)
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) :
    boxSlotSum e (rankOnePair w v) Θ
      = ∑ j : Fin d, boxSlotOf e w v j Θ := by
  have hexp : ∀ j : Fin d, boxSlotOf e w v j Θ
      = ∑ l : Fin m, ∑ l' : Fin m, (w l * v l') •
          boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ :=
    fun j => boxSlotOf_expand_G hmeas hbdd hsupp w v j Θ hΘm hΘb
  simp only [boxSlotSum, rankOnePair_evec_G, hexp]

/-! ## 3. Regularity (the `Good` predicate) of the slot calculus -/

/-- The *joint* change of variable `(x, z) ↦ x[j ↦ z]` is measurable. -/
private lemma measurable_update_pair_G {d : ℕ} (j : Fin d) :
    Measurable (fun p : Xn d × Ω => Function.update p.1 j p.2) := by
  refine measurable_pi_iff.mpr (fun i => ?_)
  by_cases hij : i = j
  · subst hij
    have h : (fun p : Xn d × Ω => Function.update p.1 i p.2 i) = fun p => p.2 := by
      funext p
      rw [Function.update_apply, if_pos rfl]
    rw [h]
    exact measurable_snd
  · have h : (fun p : Xn d × Ω => Function.update p.1 j p.2 i) = fun p => p.1 i := by
      funext p
      rw [Function.update_apply, if_neg hij]
    rw [h]
    exact (measurable_pi_apply i).comp measurable_fst

/-- **A single slot preserves `Good`** at the weak bundle. -/
private lemma boxSlotOf_good_G {m d : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w v : Fin m → ℝ) (j : Fin d) {Θ : Xn d → ℂ} (hΘ : Good Θ) :
    Good (boxSlotOf e w v j Θ) := by
  obtain ⟨hΘm, CΘ, hCΘ⟩ := hΘ
  have hw : Measurable (etaOf e w) := Work.MB.etaOf_weak_measurable hmeas w
  have hv : Measurable (etaOf e v) := Work.MB.etaOf_weak_measurable hmeas v
  obtain ⟨Bw, hBwnn, hBw⟩ := Work.MB.etaOf_weak_bound hbdd w
  obtain ⟨Bv, hBvnn, hBv⟩ := Work.MB.etaOf_weak_bound hbdd v
  have hupd : Measurable (fun p : Xn d × Ω => Function.update p.1 j p.2) :=
    measurable_update_pair_G j
  have hjoint : Measurable (fun p : Xn d × Ω =>
      (starRingEnd ℂ) (etaOf e v p.2) * Θ (Function.update p.1 j p.2)) :=
    ((Complex.continuous_conj.measurable.comp (hv.comp measurable_snd))).mul (hΘm.comp hupd)
  have hres : StronglyMeasurable (fun x : Xn d =>
      ∫ z : Ω, (starRingEnd ℂ) (etaOf e v z) * Θ (Function.update x j z)) :=
    hjoint.stronglyMeasurable.integral_prod_right'
  refine ⟨?_, ?_⟩
  · exact (hw.comp (measurable_pi_apply j)).mul hres.measurable
  · refine ⟨Bw * (Bv * max CΘ 0 * (volume (Work.BoseK15.corpusBox.boxL ℓ)).toReal), fun x => ?_⟩
    have hSmeas : MeasurableSet (Work.BoseK15.corpusBox.boxL ℓ) :=
      Work.BoseK15.corpusBox.boxL_measurableSet ℓ
    have hSfin : (volume : Measure Ω) (Work.BoseK15.corpusBox.boxL ℓ) ≠ ⊤ :=
      (Work.BoseK15.corpusBox.boxL_compact ℓ).measure_lt_top.ne
    have hfx : ∀ z : Ω, ‖(starRingEnd ℂ) (etaOf e v z) * Θ (Function.update x j z)‖
        ≤ Bv * max CΘ 0 := by
      intro z
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul (hBv z) ((hCΘ _).trans (le_max_left _ _)) (norm_nonneg _) hBvnn
    have hpt : ∀ z : Ω, ‖(starRingEnd ℂ) (etaOf e v z) * Θ (Function.update x j z)‖
        ≤ Bv * max CΘ 0 * (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => (1 : ℝ)) z := by
      intro z
      by_cases hz : z ∈ Work.BoseK15.corpusBox.boxL ℓ
      · rw [Set.indicator_of_mem hz, mul_one]
        exact hfx z
      · rw [Set.indicator_of_notMem hz, mul_zero]
        have hzero : etaOf e v z = 0 := by
          by_contra hne
          exact hz (Work.MB.etaOf_weak_support hsupp v (Function.mem_support.mpr hne))
        rw [hzero, map_zero, zero_mul, norm_zero]
    have hmaj : Integrable (fun z : Ω =>
        Bv * max CΘ 0 * (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => (1 : ℝ)) z)
        (volume : Measure Ω) :=
      ((integrable_indicator_iff hSmeas).mpr (integrableOn_const hSfin)).const_mul _
    have hbnd : ‖∫ z : Ω, (starRingEnd ℂ) (etaOf e v z) * Θ (Function.update x j z)‖
        ≤ Bv * max CΘ 0 * (volume (Work.BoseK15.corpusBox.boxL ℓ)).toReal := by
      calc ‖∫ z : Ω, (starRingEnd ℂ) (etaOf e v z) * Θ (Function.update x j z)‖
          ≤ ∫ z : Ω, ‖(starRingEnd ℂ) (etaOf e v z) * Θ (Function.update x j z)‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ z : Ω, Bv * max CΘ 0 *
              (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => (1 : ℝ)) z :=
            integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => norm_nonneg _) hmaj
              (Filter.Eventually.of_forall hpt)
        _ = Bv * max CΘ 0 * (volume (Work.BoseK15.corpusBox.boxL ℓ)).toReal := by
            rw [MeasureTheory.integral_const_mul,
              MeasureTheory.integral_indicator_const (1 : ℝ)
                (Work.BoseK15.corpusBox.boxL_measurableSet ℓ),
              MeasureTheory.Measure.real, smul_eq_mul, mul_one]
    calc ‖boxSlotOf e w v j Θ x‖
        = ‖etaOf e w (x j)‖ *
            ‖∫ z : Ω, (starRingEnd ℂ) (etaOf e v z) * Θ (Function.update x j z)‖ := by
          rw [boxSlotOf, norm_mul]
      _ ≤ Bw * ‖∫ z : Ω, (starRingEnd ℂ) (etaOf e v z) * Θ (Function.update x j z)‖ :=
          mul_le_mul_of_nonneg_right (hBw _) (norm_nonneg _)
      _ ≤ Bw * (Bv * max CΘ 0 * (volume (Work.BoseK15.corpusBox.boxL ℓ)).toReal) :=
          mul_le_mul_of_nonneg_left hbnd hBwnn

/-- **`boxAnnOf` preserves `Good`** at the weak bundle (the twin of the strong
`Work.BoseBoxFock.AVLin_boxAnnOf`). -/
private lemma boxAnnOf_good_G {m d : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w : Fin m → ℝ) {Θ : Xn (d + 1) → ℂ} (hΘ : Good Θ) :
    Good (boxAnnOf e w d Θ) := by
  obtain ⟨hΘm, C, hC⟩ := hΘ
  have hηm : Measurable (etaOf e w) := Work.MB.etaOf_weak_measurable hmeas w
  have hint : ∀ y : Xn d,
      Integrable (fun z : Ω => (starRingEnd ℂ) (etaOf e w z) * Θ (Fin.cons z y)) := by
    intro y
    refine Integrable.mul_bdd (f := fun z : Ω => (starRingEnd ℂ) (etaOf e w z))
      (g := fun z : Ω => Θ (Fin.cons z y)) (c := max C 0)
      (conj_etaOf_integrable_G hmeas hbdd hsupp w)
      ((hΘm.comp (Work.BoseBoxFock.continuous_cons_fixed y).measurable).aestronglyMeasurable) ?_
    exact Filter.Eventually.of_forall (fun z => (hC _).trans (le_max_left _ _))
  refine ⟨?_, ?_⟩
  · have hjoint : Measurable (Function.uncurry
        (fun (y : Xn d) (z : Ω) => (starRingEnd ℂ) (etaOf e w z) * Θ (Fin.cons z y))) := by
      apply Measurable.mul
      · exact (Complex.continuous_conj.measurable.comp hηm).comp measurable_snd
      · exact hΘm.comp (Work.BoseBoxFock.continuous_cons_swap (d := d)).measurable
    exact ((hjoint.stronglyMeasurable.integral_prod_right
      (ν := (volume : Measure Ω))).measurable).const_mul _
  · refine ⟨‖(Real.sqrt ((d : ℝ) + 1) : ℂ)‖ *
        ((∫ z : Ω, ‖etaOf e w z‖) * max C 0), fun y => ?_⟩
    simp only [boxAnnOf]
    calc ‖(Real.sqrt ((d : ℝ) + 1) : ℂ)
            * ∫ z : Ω, (starRingEnd ℂ) (etaOf e w z) * Θ (Fin.cons z y)‖
        ≤ ‖(Real.sqrt ((d : ℝ) + 1) : ℂ)‖
            * ‖∫ z : Ω, (starRingEnd ℂ) (etaOf e w z) * Θ (Fin.cons z y)‖ := norm_mul_le _ _
      _ ≤ ‖(Real.sqrt ((d : ℝ) + 1) : ℂ)‖
            * ∫ z : Ω, ‖(starRingEnd ℂ) (etaOf e w z) * Θ (Fin.cons z y)‖ :=
          mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (norm_nonneg _)
      _ ≤ ‖(Real.sqrt ((d : ℝ) + 1) : ℂ)‖ * (∫ z : Ω, ‖etaOf e w z‖ * max C 0) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          apply integral_mono (hint y).norm
            ((norm_etaOf_integrable_G hmeas hbdd hsupp w).mul_const (max C 0))
          intro z
          show ‖(starRingEnd ℂ) (etaOf e w z) * Θ (Fin.cons z y)‖ ≤ ‖etaOf e w z‖ * max C 0
          rw [norm_mul, Complex.norm_conj]
          exact mul_le_mul_of_nonneg_left ((hC _).trans (le_max_left _ _)) (norm_nonneg _)
      _ = ‖(Real.sqrt ((d : ℝ) + 1) : ℂ)‖ * ((∫ z : Ω, ‖etaOf e w z‖) * max C 0) := by
          rw [integral_mul_const]

/-- **The slot sum preserves `Good`** at the weak bundle. -/
private lemma boxSlotSum_good_G {m d : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) {Θ : Xn d → ℂ} (hΘ : Good Θ) :
    Good (boxSlotSum e T Θ) := by
  classical
  have hfun : boxSlotSum e T Θ
      = fun x => ∑ j : Fin d, ∑ l : Fin m, ∑ l' : Fin m,
          T (Work.BoseB4.evec m l') l •
            boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ x := by
    funext x
    simp only [boxSlotSum, Finset.sum_apply, Pi.smul_apply]
  have hterm : ∀ (j : Fin d) (l l' : Fin m),
      Measurable (fun x : Xn d => T (Work.BoseB4.evec m l') l •
          boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ x) ∧
      ∃ B, ∀ x : Xn d, ‖T (Work.BoseB4.evec m l') l •
          boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ x‖ ≤ B := by
    intro j l l'
    obtain ⟨hm, hb⟩ := boxSlotOf_good_G hmeas hbdd hsupp
      (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j hΘ
    refine ⟨hm.const_smul (T (Work.BoseB4.evec m l') l), ?_⟩
    obtain ⟨B, hB⟩ := hb
    refine ⟨‖T (Work.BoseB4.evec m l') l‖ * max B 0, fun x => ?_⟩
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left ((hB x).trans (le_max_left _ _)) (norm_nonneg _)
  choose B hB using fun (j : Fin d) (l l' : Fin m) => (hterm j l l').2
  rw [hfun]
  refine ⟨?_, ⟨∑ j : Fin d, ∑ l : Fin m, ∑ l' : Fin m, max (B j l l') 0, fun x => ?_⟩⟩
  · refine Finset.measurable_sum _ (fun j _ =>
      Finset.measurable_sum _ (fun l _ =>
        Finset.measurable_sum _ (fun l' _ => (hterm j l l').1)))
  · calc ‖∑ j : Fin d, ∑ l : Fin m, ∑ l' : Fin m,
          T (Work.BoseB4.evec m l') l •
            boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ x‖
        ≤ ∑ j : Fin d, ‖∑ l : Fin m, ∑ l' : Fin m,
            T (Work.BoseB4.evec m l') l •
              boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ x‖ :=
          norm_sum_le _ _
      _ ≤ ∑ j : Fin d, ∑ l : Fin m, ‖∑ l' : Fin m,
            T (Work.BoseB4.evec m l') l •
              boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ x‖ :=
          Finset.sum_le_sum (fun j _ => norm_sum_le _ _)
      _ ≤ ∑ j : Fin d, ∑ l : Fin m, ∑ l' : Fin m,
            ‖T (Work.BoseB4.evec m l') l •
              boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ x‖ :=
          Finset.sum_le_sum (fun j _ =>
            Finset.sum_le_sum (fun l _ => norm_sum_le _ _))
      _ ≤ ∑ j : Fin d, ∑ l : Fin m, ∑ l' : Fin m, max (B j l l') 0 :=
          Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun l _ =>
            Finset.sum_le_sum (fun l' _ =>
              (hB j l l' x).trans (le_max_left _ _))))

/-! ## 4. The (unconditional) linearity of `boxCreOf` and `boxSlotSum` -/

/-- `boxCreOf` is additive in the state — no regularity hypothesis is needed: it is a finite sum. -/
private lemma boxCreOf_add_G {m d : ℕ} {e : Fin m → Ω → ℂ} (w : Fin m → ℝ) {Θ Ψ : Xn d → ℂ} :
    boxCreOf e w d (Θ + Ψ) = boxCreOf e w d Θ + boxCreOf e w d Ψ := by
  funext x
  simp only [boxCreOf, Pi.add_apply, mul_add, Finset.sum_add_distrib, Finset.mul_sum]

/-- `boxCreOf` is `ℂ`-homogeneous in the state. -/
private lemma boxCreOf_smul_G {m d : ℕ} {e : Fin m → Ω → ℂ} (w : Fin m → ℝ) (c : ℂ)
    (Θ : Xn d → ℂ) :
    boxCreOf e w d (c • Θ) = c • boxCreOf e w d Θ := by
  funext x
  simp only [boxCreOf, Pi.smul_apply, smul_eq_mul]
  have h1 : (∑ j : Fin (d + 1),
      etaOf e w (x j) * (c * Θ (fun i : Fin d => x (Fin.succAbove j i))))
      = c * ∑ j : Fin (d + 1),
          etaOf e w (x j) * Θ (fun i : Fin d => x (Fin.succAbove j i)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [h1]
  ring

/-- Homogeneity of `boxSlotSum` in the one-body operator (real scalars). -/
private lemma boxSlotSum_smul_real_G {m d : ℕ} (e : Fin m → Ω → ℂ) (r : ℝ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (Θ : Xn d → ℂ) :
    boxSlotSum e (r • T) Θ = (r : ℂ) • boxSlotSum e T Θ := by
  funext x
  simp only [boxSlotSum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    LinearMap.smul_apply]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l' _ => ?_
  simp
  rw [mul_assoc]

/-! ## 5. The rank-one slot sum is the two-letter ladder word -/

/-- The weak twin of `Work.BoseBoxFock.boxSlotSum_rankOnePair_creAnn`: the slot sum of a rank-one
operator is the two-letter ladder word, on any symmetric good state. -/
private lemma rankOne_creAnn_G {m d : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w v : Fin m → ℝ) (X : Xn (d + 1) → ℂ) (hX : Good X)
    (hXs : ∀ (σ : Equiv.Perm (Fin (d + 1))) (x : Xn (d + 1)), X (x ∘ σ) = X x) :
    boxSlotSum e (rankOnePair w v) X = boxCreOf e w d (boxAnnOf e v d X) := by
  rw [boxSlotSum_rankOnePair_weakG hmeas hbdd hsupp w v X hX.1 hX.2]
  exact (boxCreOf_boxAnnOf_slot (e := e) w v X hXs).symm

/-! ## 6. The box CCR `A_v (C_w Z) = C_w (A_v Z) + ⟨η_v, η_w⟩ • Z` at the weak bundle

This is the content of `Work.BoseBoxFock.boxAnnOf_boxCreOf_ccr_weak`, inlined here so that the
clashing import of its strong twin `boxAnnOf_boxCreOf_ccr` (and hence of
`Work.BoseBoxFock.AVGoodState`) is not needed. -/

/-- `z ↦ Fin.cons z y` is continuous. -/
private lemma continuous_cons_fun_G {d : ℕ} (y : Xn d) :
    Continuous (fun z : Ω => (Fin.cons z y : Xn (d+1))) :=
  Work.BoseBoxFock.continuous_cons_fixed y

/-- Moving `z` into the `(k+1)`-st slot is the same as first deleting slot `k+1` and then
putting `z` in front. -/
private lemma cons_succAbove_comp_G {n : ℕ} (z : Ω) (y : Xn (n+1)) (k : Fin (n+1)) :
    (fun i : Fin (n+1) => (Fin.cons z y : Xn ((n+1)+1)) (Fin.succAbove (Fin.succ k) i))
      = (Fin.cons z (fun i : Fin n => y (Fin.succAbove k i)) : Xn (n+1)) := by
  funext i
  cases i using Fin.cases with
  | zero => simp
  | succ i' => simp [Fin.cons_succ]

/-- The `j`-th summand of `boxCreOf e w · Z` along the slice `z ↦ (z, y)`, as a function of the
integration variable `z`. -/
private noncomputable def sliceW_G {m d : ℕ} (e : Fin m → Ω → ℂ) (w : Fin m → ℝ)
    (Z : Xn d → ℂ) (y : Xn d) (j : Fin (d+1)) : Ω → ℂ :=
  fun z => etaOf e w ((Fin.cons z y : Xn (d+1)) j)
    * Z (fun i : Fin d => (Fin.cons z y : Xn (d+1)) (Fin.succAbove j i))

/-- The slice integrand `conj(η_u z) · η_w((z,y)_j) · Z((z,y) ∖ j)` is integrable: a bounded
measurable factor times the integrable `conj(η_u)`. -/
private lemma integrable_ccr_slice_G {m d : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (u w : Fin m → ℝ) {Z : Xn d → ℂ} (hZm : Measurable Z) {CZ : ℝ} (hZ : ∀ x, ‖Z x‖ ≤ CZ)
    (y : Xn d) (j : Fin (d+1)) :
    Integrable (fun z : Ω => (starRingEnd ℂ) (etaOf e u z) * sliceW_G e w Z y j z) := by
  obtain ⟨Cη, hCη0, hCη⟩ := Work.MB.etaOf_weak_bound hbdd w
  refine Integrable.mul_bdd (f := fun z : Ω => (starRingEnd ℂ) (etaOf e u z))
    (g := fun z : Ω => etaOf e w ((Fin.cons z y : Xn (d+1)) j)
      * Z (fun i : Fin d => (Fin.cons z y : Xn (d+1)) (Fin.succAbove j i)))
    (c := Cη * CZ) (conj_etaOf_integrable_G hmeas hbdd hsupp u) ?_ ?_
  · refine (Measurable.mul ?_ ?_).aestronglyMeasurable
    · exact (Work.MB.etaOf_weak_measurable hmeas w).comp
        (((continuous_apply j).comp (continuous_cons_fun_G y)).measurable)
    · exact hZm.comp (((continuous_pi (fun i => continuous_apply (Fin.succAbove j i))).comp
        (continuous_cons_fun_G y)).measurable)
  · exact Filter.Eventually.of_forall (fun z => by
      rw [norm_mul]
      exact mul_le_mul (hCη _) (hZ _) (norm_nonneg _) hCη0)

/-- Pull the finite sum out of the integral against `conj(η_u)`. -/
private lemma integral_conj_etaOf_mul_sum_G {m : ℕ} {e : Fin m → Ω → ℂ}
    {ι : Type*} [Fintype ι] (u : Fin m → ℝ) (G : ι → Ω → ℂ)
    (hG : ∀ j, Integrable (fun z : Ω => (starRingEnd ℂ) (etaOf e u z) * G j z)) :
    (∫ z : Ω, (starRingEnd ℂ) (etaOf e u z) * ∑ j, G j z)
      = ∑ j, ∫ z : Ω, (starRingEnd ℂ) (etaOf e u z) * G j z := by
  rw [show (∫ z : Ω, (starRingEnd ℂ) (etaOf e u z) * ∑ j, G j z)
        = ∫ z : Ω, ∑ j, (starRingEnd ℂ) (etaOf e u z) * G j z from
      integral_congr_ae (Filter.Eventually.of_forall (fun z => Finset.mul_sum ..))]
  exact integral_finsetSum Finset.univ (fun j _ => hG j)

/-- Cancellation of the two `√`-factors: `a · (x · (a⁻¹ · s)) = x · s`. -/
private lemma mul_inv_mul_factor_G (a x s : ℂ) (ha : a ≠ 0) : a * (x * ((1/a) * s)) = x * s := by
  rw [show a * (x * ((1 / a) * s)) = (a * (1 / a)) * (x * s) from by ring,
      mul_one_div_cancel ha, one_mul]

/-- Cancellation of the two `√`-factors: `a⁻¹ · (x · (a · s)) = x · s`. -/
private lemma div_mul_factor_G (a x s : ℂ) (ha : a ≠ 0) : (1/a) * (x * (a * s)) = x * s := by
  rw [show (1 / a) * (x * (a * s)) = (1 / a * a) * (x * s) from by ring,
      div_mul_cancel₀ (1 : ℂ) ha, one_mul]

/-- The pairing `conj (e l) · e l'` is integrable: the product of two bounded measurable
functions supported in the compact box. -/
private lemma conjE_mul_E_integrable_G {m : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ) (l l' : Fin m) :
    Integrable (fun z : Ω => (starRingEnd ℂ) (e l z) * e l' z) := by
  choose C hC using hbdd
  have hCl : 0 ≤ C l := le_trans (norm_nonneg _) (hC l 0)
  have hCl' : 0 ≤ C l' := le_trans (norm_nonneg _) (hC l' 0)
  refine Work.MB.integrable_of_bdd_of_support (μ := volume) (C := C l * C l')
    (Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ)
    (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ).measure_lt_top.ne ?_ ?_ ?_
  · exact ((continuous_star.measurable.comp (hmeas l)).mul (hmeas l')).aestronglyMeasurable
  · intro z
    rw [norm_mul]
    have h1 : ‖(starRingEnd ℂ) (e l z)‖ ≤ C l := by
      rw [starRingEnd_apply, norm_star]
      exact hC l z
    exact mul_le_mul h1 (hC l' z) (norm_nonneg _) hCl
  · intro z hz
    have h1 : e l z = 0 := Function.notMem_support.mp (fun h => hz (hsupp l h))
    simp [h1]

/-- The one-particle pairing `⟨η_u, η_w⟩ = Σ_l u_l w_l` at the weak bundle. -/
private lemma integral_conj_etaOf_mul_etaOf_G {m : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : Ω, star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0))
    (u w : Fin m → ℝ) :
    (∫ z : Ω, (starRingEnd ℂ) (etaOf e u z) * etaOf e w z)
      = ((∑ l : Fin m, u l * w l : ℝ) : ℂ) := by
  have hint : ∀ l l' : Fin m, Integrable (fun z : Ω => star (e l z) * e l' z) := fun l l' =>
    conjE_mul_E_integrable_G hmeas hbdd hsupp l l'
  have horth' : ∀ l l' : Fin m, (∫ z : Ω, (starRingEnd ℂ) (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0) := fun l l' => by
    rw [← horth l l']
    exact integral_congr_ae (Filter.Eventually.of_forall (fun z => rfl))
  have key : ∀ z : Ω, (starRingEnd ℂ) (etaOf e u z) * etaOf e w z
      = ∑ l : Fin m, ∑ l' : Fin m,
          ((u l * w l' : ℝ) : ℂ) * ((starRingEnd ℂ) (e l z) * e l' z) := by
    intro z
    simp only [etaOf]
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l' _ => ?_)
    rw [map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
    ring
  have hInt : ∀ l l' : Fin m, Integrable (fun z : Ω => ((u l * w l' : ℝ) : ℂ)
      * ((starRingEnd ℂ) (e l z) * e l' z)) := fun l l' => (hint l l').const_mul _
  have hIntOuter : ∀ l : Fin m, Integrable (fun z : Ω => ∑ l' : Fin m,
      ((u l * w l' : ℝ) : ℂ) * ((starRingEnd ℂ) (e l z) * e l' z)) := fun l =>
    integrable_finsetSum Finset.univ (fun l' _ => hInt l l')
  calc (∫ z : Ω, (starRingEnd ℂ) (etaOf e u z) * etaOf e w z)
      = ∫ z : Ω, ∑ l : Fin m, ∑ l' : Fin m,
          ((u l * w l' : ℝ) : ℂ) * ((starRingEnd ℂ) (e l z) * e l' z) :=
        integral_congr_ae (Filter.Eventually.of_forall key)
    _ = ∑ l : Fin m, ∫ z : Ω, ∑ l' : Fin m,
          ((u l * w l' : ℝ) : ℂ) * ((starRingEnd ℂ) (e l z) * e l' z) :=
        integral_finsetSum Finset.univ (fun l _ => hIntOuter l)
    _ = ∑ l : Fin m, ∑ l' : Fin m,
          ((u l * w l' : ℝ) : ℂ) * (∫ z : Ω, (starRingEnd ℂ) (e l z) * e l' z) := by
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [integral_finsetSum Finset.univ (fun l' _ => hInt l l')]
        exact Finset.sum_congr rfl (fun l' _ => by rw [integral_const_mul])
    _ = ∑ l : Fin m, ∑ l' : Fin m,
          ((u l * w l' : ℝ) : ℂ) * (if l = l' then (1 : ℂ) else 0) := by
        refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun l' _ => ?_))
        rw [horth' l l']
    _ = ∑ l : Fin m, ((u l * w l : ℝ) : ℂ) := by
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [Finset.sum_eq_single l]
        · simp
        · intro l' _ hl'
          rw [if_neg (fun h => hl' h.symm), mul_zero]
        · intro hl
          exact absurd (Finset.mem_univ l) hl
    _ = ((∑ l : Fin m, u l * w l : ℝ) : ℂ) := by
        rw [Complex.ofReal_sum]

/-- The expansion of `boxAnnOf e v · boxCreOf e w`. -/
private lemma boxAnnOf_boxCreOf_apply_G {m n : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w v : Fin m → ℝ) {Z : Xn (n+1) → ℂ} (hZm : Measurable Z) {CZ : ℝ}
    (hZ : ∀ x, ‖Z x‖ ≤ CZ) (y : Xn (n+1)) :
    boxAnnOf e v (n+1) (boxCreOf e w (n+1) Z) y
      = (∫ z : Ω, (starRingEnd ℂ) (etaOf e v z) * etaOf e w z) * Z y
        + ∑ k : Fin (n+1), etaOf e w (y k)
            * ∫ z : Ω, (starRingEnd ℂ) (etaOf e v z)
                * Z (Fin.cons z (fun i : Fin n => y (Fin.succAbove k i))) := by
  simp only [boxAnnOf, boxCreOf]
  set a : ℂ := (Real.sqrt ((↑(n+1) : ℝ) + 1) : ℂ) with ha
  have ha0 : a ≠ 0 := by
    rw [ha]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos_of_pos (by positivity)))
  have h0 : (∫ z : Ω, (starRingEnd ℂ) (etaOf e v z) * sliceW_G e w Z y 0 z)
      = (∫ z : Ω, (starRingEnd ℂ) (etaOf e v z) * etaOf e w z) * Z y := by
    rw [show (∫ z : Ω, (starRingEnd ℂ) (etaOf e v z) * sliceW_G e w Z y 0 z)
          = ∫ z : Ω, (starRingEnd ℂ) (etaOf e v z) * (etaOf e w z * Z y) from
        integral_congr_ae (Filter.Eventually.of_forall (fun z => by
          simp only [sliceW_G, Fin.cons_zero, Fin.succAbove_zero, Fin.cons_succ]))]
    rw [← integral_mul_const]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun z => by ring))
  have hk : ∀ k : Fin (n+1),
      (∫ z : Ω, (starRingEnd ℂ) (etaOf e v z) * sliceW_G e w Z y (Fin.succ k) z)
      = etaOf e w (y k) * ∫ z : Ω, (starRingEnd ℂ) (etaOf e v z)
          * Z (Fin.cons z (fun i : Fin n => y (Fin.succAbove k i))) := by
    intro k
    rw [show (∫ z : Ω, (starRingEnd ℂ) (etaOf e v z) * sliceW_G e w Z y (Fin.succ k) z)
          = ∫ z : Ω, (starRingEnd ℂ) (etaOf e v z)
              * (etaOf e w (y k) * Z (Fin.cons z (fun i : Fin n => y (Fin.succAbove k i)))) from
        integral_congr_ae (Filter.Eventually.of_forall (fun z => by
          simp only [sliceW_G]
          rw [Fin.cons_succ, cons_succAbove_comp_G z y k]))]
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun z => by ring))
  calc a * (∫ z : Ω, (starRingEnd ℂ) (etaOf e v z)
        * ((1 / a) * ∑ j : Fin ((n+1)+1), sliceW_G e w Z y j z))
      = ∫ z : Ω, (starRingEnd ℂ) (etaOf e v z)
          * ∑ j : Fin ((n+1)+1), sliceW_G e w Z y j z := by
        rw [← integral_const_mul]
        exact integral_congr_ae
          (Filter.Eventually.of_forall (fun z => mul_inv_mul_factor_G a _ _ ha0))
    _ = ∑ j : Fin ((n+1)+1), ∫ z : Ω, (starRingEnd ℂ) (etaOf e v z) * sliceW_G e w Z y j z :=
        integral_conj_etaOf_mul_sum_G (u := v) (G := sliceW_G e w Z y)
          (fun j => integrable_ccr_slice_G hmeas hbdd hsupp v w hZm hZ y j)
    _ = (∫ z : Ω, (starRingEnd ℂ) (etaOf e v z) * etaOf e w z) * Z y
        + ∑ k : Fin (n+1), etaOf e w (y k)
            * ∫ z : Ω, (starRingEnd ℂ) (etaOf e v z)
                * Z (Fin.cons z (fun i : Fin n => y (Fin.succAbove k i))) := by
        rw [Fin.sum_univ_succ, h0]
        exact congrArg (fun s => (∫ z : Ω, (starRingEnd ℂ) (etaOf e v z) * etaOf e w z) * Z y
            + s) (Finset.sum_congr rfl (fun k _ => hk k))

/-- The expansion of `boxCreOf e w · boxAnnOf e v`. -/
private lemma boxCreOf_boxAnnOf_apply_G {m n : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w v : Fin m → ℝ) {Z : Xn (n+1) → ℂ} (hZm : Measurable Z) {CZ : ℝ}
    (hZ : ∀ x, ‖Z x‖ ≤ CZ) (y : Xn (n+1)) :
    boxCreOf e w n (boxAnnOf e v n Z) y
      = ∑ k : Fin (n+1), etaOf e w (y k)
          * ∫ z : Ω, (starRingEnd ℂ) (etaOf e v z)
              * Z (Fin.cons z (fun i : Fin n => y (Fin.succAbove k i))) := by
  simp only [boxCreOf, boxAnnOf]
  set b : ℂ := (Real.sqrt ((↑n : ℝ) + 1) : ℂ) with hb
  have hb0 : b ≠ 0 := by
    rw [hb]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos_of_pos (by positivity)))
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => div_mul_factor_G b _ _ hb0)

/-- **The box CCR at the weak mode bundle**: `A_v (C_w Z) = C_w (A_v Z) + ⟨η_v, η_w⟩ • Z`. -/
theorem boxAnnOf_boxCreOf_ccr_weakG {m n : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l))
    (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : Ω, star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (w v : Fin m → ℝ) (Z : Xn (n + 1) → ℂ)
    (hZm : Measurable Z) (hZb : ∃ C : ℝ, ∀ x, ‖Z x‖ ≤ C) :
    boxAnnOf e v (n + 1) (boxCreOf e w (n + 1) Z)
      = boxCreOf e w n (boxAnnOf e v n Z)
        + ((∑ l : Fin m, v l * w l : ℝ) : ℂ) • Z := by
  obtain ⟨CZ, hZ⟩ := hZb
  funext y
  rw [boxAnnOf_boxCreOf_apply_G hmeas hbdd hsupp w v hZm hZ y]
  rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [boxCreOf_boxAnnOf_apply_G hmeas hbdd hsupp w v hZm hZ y]
  rw [← integral_conj_etaOf_mul_etaOf_G hmeas hbdd hsupp horth v w]
  exact add_comm _ _

/-! ## 7. The target: the weak-bundle slot form of the pair word is the ladder word -/

theorem bW4slotEqBW4G {m : ℕ} {ℓ : ℝ} {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (w₁ w₂ v₁ v₂ : Fin m → ℝ) (d : ℕ) {Θ : Work.BoseDict.Xn (d + 2) → ℂ}
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘsym : ∀ (σ : Equiv.Perm (Fin (d + 2))) (x : Work.BoseDict.Xn (d + 2)), Θ (x ∘ σ) = Θ x) :
    Work.BoseBoxFock.bW4slot e w₁ w₂ v₁ v₂ d Θ
      = Work.BoseBoxFock.bW4 e w₁ w₂ v₁ v₂ d Θ := by
  have hgoodΘ : Good Θ := ⟨hΘm, hΘb⟩
  -- the inner two-letter word
  have hIn : boxSlotSum e (rankOnePair w₂ v₂) Θ
      = boxCreOf e w₂ (d + 1) (boxAnnOf e v₂ (d + 1) Θ) :=
    rankOne_creAnn_G hmeas hbdd hsupp w₂ v₂ Θ hgoodΘ hΘsym
  have hΛgood : Good (boxSlotSum e (rankOnePair w₂ v₂) Θ) := by
    rw [boxSlotSum_rankOnePair_weakG hmeas hbdd hsupp w₂ v₂ Θ hΘm hΘb]
    exact Good.finset_sum_univ (fun j =>
      boxSlotOf_good_G hmeas hbdd hsupp w₂ v₂ j hgoodΘ)
  have hΛsym : ∀ (σ : Equiv.Perm (Fin (d + 2))) (x : Xn (d + 2)),
      (boxSlotSum e (rankOnePair w₂ v₂) Θ) (x ∘ σ)
        = (boxSlotSum e (rankOnePair w₂ v₂) Θ) x := by
    intro σ x
    rw [boxSlotSum_rankOnePair_weakG hmeas hbdd hsupp w₂ v₂ Θ hΘm hΘb]
    exact Work.BoseBoxFock.sum_boxSlotOf_symm w₂ v₂ Θ hΘsym σ x
  -- the outer two-letter word
  have hOut : boxSlotSum e (rankOnePair w₁ v₁)
        (boxSlotSum e (rankOnePair w₂ v₂) Θ)
      = boxCreOf e w₁ (d + 1)
          (boxAnnOf e v₁ (d + 1) (boxSlotSum e (rankOnePair w₂ v₂) Θ)) :=
    rankOne_creAnn_G hmeas hbdd hsupp w₁ v₁ _ hΛgood hΛsym
  -- the contraction term
  have hCross : boxSlotSum e ((rankOnePair w₁ v₁).comp (rankOnePair w₂ v₂)) Θ
      = ((∑ l : Fin m, v₁ l * w₂ l : ℝ) : ℂ) •
          boxCreOf e w₁ (d + 1) (boxAnnOf e v₂ (d + 1) Θ) := by
    rw [rankOnePair_comp, boxSlotSum_smul_real_G,
      rankOne_creAnn_G hmeas hbdd hsupp w₁ v₂ Θ hgoodΘ hΘsym]
  -- the box CCR
  have hZgood : Good (boxAnnOf e v₂ (d + 1) Θ) :=
    boxAnnOf_good_G hmeas hbdd hsupp v₂ hgoodΘ
  have hccr : boxAnnOf e v₁ (d + 1)
        (boxCreOf e w₂ (d + 1) (boxAnnOf e v₂ (d + 1) Θ))
      = boxCreOf e w₂ d (boxAnnOf e v₁ d (boxAnnOf e v₂ (d + 1) Θ))
        + ((∑ l : Fin m, v₁ l * w₂ l : ℝ) : ℂ) • (boxAnnOf e v₂ (d + 1) Θ) :=
    boxAnnOf_boxCreOf_ccr_weakG hmeas hbdd hsupp horth w₂ v₁
      (boxAnnOf e v₂ (d + 1) Θ) hZgood.1 hZgood.2
  -- the middle step: `C (A (C Z)) = C (C (A Z)) + g • C Z` by the CCR
  have hmid : boxCreOf e w₁ (d + 1)
        (boxAnnOf e v₁ (d + 1)
          (boxCreOf e w₂ (d + 1) (boxAnnOf e v₂ (d + 1) Θ)))
      = boxCreOf e w₁ (d + 1)
          (boxCreOf e w₂ d (boxAnnOf e v₁ d (boxAnnOf e v₂ (d + 1) Θ)))
        + ((∑ l : Fin m, v₁ l * w₂ l : ℝ) : ℂ) •
            (boxCreOf e w₁ (d + 1) (boxAnnOf e v₂ (d + 1) Θ)) := by
    rw [hccr, boxCreOf_add_G, boxCreOf_smul_G]
  rw [bW4slot_apply, hOut, hIn, hCross, hmid, add_sub_cancel_right]
  rfl

/-- **Alias** of `bW4slotEqBW4G` under the name used by the `PotCubicLowBandG` chapter's own
assembly (`FINDING_PotCubicLowBandG_holds_session1.md`): the weak-bundle slot form of the pair
word is the ladder word. -/
theorem bW4slot_eq_bW4G {m : ℕ} {ℓ : ℝ} {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (w₁ w₂ v₁ v₂ : Fin m → ℝ) (d : ℕ) {Θ : Work.BoseDict.Xn (d + 2) → ℂ}
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘsym : ∀ (σ : Equiv.Perm (Fin (d + 2))) (x : Work.BoseDict.Xn (d + 2)), Θ (x ∘ σ) = Θ x) :
    Work.BoseBoxFock.bW4slot e w₁ w₂ v₁ v₂ d Θ
      = Work.BoseBoxFock.bW4 e w₁ w₂ v₁ v₂ d Θ :=
  bW4slotEqBW4G hmeas hbdd hsupp horth w₁ w₂ v₁ v₂ d hΘm hΘb hΘsym

end Work.BoseBoxFock.PotCubicLowBandAux
