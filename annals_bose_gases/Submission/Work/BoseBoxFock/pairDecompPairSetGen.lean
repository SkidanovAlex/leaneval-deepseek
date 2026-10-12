import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.PotGroupDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pairDecompPairSetGen` — the pair decomposition of two rank-one slots

The first-quantised slot sum `B(T) = boxSlotSum e T = Σ_j T^{(j)}` of a one-body operator `T` is
the sum of the `j`-th slot operators `Work.BoseDict.boxSlotOf e w v j`, so for the two rank-one
operators `T₁ = |w₁⟩⟨v₁|`, `T₂ = |w₂⟩⟨v₂|` the double sum `B(T₁) ∘ B(T₂) = Σ_{i,j} T₁^{(i)}T₂^{(j)}`
splits into

* a *diagonal* part `Σ_j T₁^{(j)}T₂^{(j)} = B(T₁ ∘ T₂)` — the two same-slot operators compose as
  rank-one operators (`Work.BoseBoxFock.rankOnePair_comp` plus the same-slot composition
  `boxSlotOf_comp_same_loc`, whose scalar is the mode pairing `Work.BoseB4.gram w₂ v₁`), and
* an *off-diagonal* part `Σ_{j≠j'} T₁^{(j)}T₂^{(j')}`, which is the `pairSet` sum of the target.

Hence

    `B(T₁)(B(T₂)Θ) − B(T₁∘T₂)Θ = Σ_{p ∈ pairSet n} boxSlotOf e w₁ v₁ p.1 (boxSlotOf e w₂ v₂ p.2 Θ)`,

a purely algebraic identity of functions `Xn n → ℂ` at a **general arity** `n` (it is the
general-arity replacement of `Work.BoseBoxFock.bW4slot_eq_pairSet`, which is stated only at the
arity `d + 2`; `boxSlotOf` and `pairSet` are indexed by the number of slots, so there is no
transport from `Xn (d+2)` to `Xn n`).

## Why the slot algebra is re-derived here

The identity is delivered in the workspace as `Work.BoseBoxFock.boxSlotSum_pair_decomp`, but that
module lies in the `Submission.Work.MB.SlotWeakBase` cone, which reaches
`Work.BoseBoxFock.AVGoodState`; that module declares `Work.BoseBoxFock.etaOf_hasCompactSupport`
(and `etaOf_continuous`) a second time with respect to
`Submission.Work.BoseBoxFock.boxSlotSum_measurable_bounded`, which the present file's cone already
reaches through `PotGroupDefs`.  The two cones therefore cannot be put in one environment (Lean:
*environment already contains*), and the slot algebra is re-derived locally, in the *weak* mode
bundle of the target (measurable / everywhere bounded / supported in the corpus box `boxL ℓ`) —
exactly the hypotheses the target carries.  The only imported helper outside `Mathlib` is the
generic `L¹` criterion `Work.MB.integrable_of_bdd_of_support` (and the weak `η`-facts of
`Work.MB.SlotWeakBase`), which is compatible with both cones.

Sections 1–4 below carry the local slot algebra (`boxSlotSum_rankOnePair_loc`,
`boxSlotOf_comp_same_loc`, `boxSlotOf_finset_sum_loc`, `boxSlotSum_pair_decomp_loc`,
`sum_pairSet_eq_univ_erase_loc`), and the target `pairDecompPairSetGen` is their two-line
combination.  Everything here is `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

open Work.BoseDict

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

private lemma etaOf_evec_loc {m : ℕ} (e : Fin m → Ω → ℂ) (l : Fin m) :
    etaOf e (Work.BoseB4.evec m l) = e l := by
  funext z
  simp only [etaOf, Work.BoseB4.evec, Pi.single_apply]
  rw [Finset.sum_eq_single l]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ l) h

/-- The slot at coordinate vectors, in the explicit form used by the expansion. -/
private lemma boxSlotOf_evec_eq_loc {m d : ℕ} (e : Fin m → Ω → ℂ) (l l' : Fin m) (j : Fin d)
    (Θ : Xn d → ℂ) :
    boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ
      = fun x => e l (x j) * ∫ z : Ω, (starRingEnd ℂ) (e l' z) * Θ (Function.update x j z) := by
  funext x
  simp only [boxSlotOf, etaOf_evec_loc]

/-- The sum defining `η_v` at a coordinate vector. -/
private lemma sum_evec_mul_loc {m : ℕ} (v : Fin m → ℝ) (l' : Fin m) :
    (∑ k : Fin m, v k * (Work.BoseB4.evec m l' k)) = v l' := by
  rw [Finset.sum_eq_single l']
  · simp [Work.BoseB4.evec]
  · intro b _ hb
    simp [Work.BoseB4.evec, Pi.single_eq_of_ne, hb]
  · intro h; exact absurd (Finset.mem_univ l') h

/-- `(|w⟩⟨v| (evec l'))_l = w_l v_{l'}`. -/
private lemma rankOnePair_evec_loc {m : ℕ} (w v : Fin m → ℝ) (l l' : Fin m) :
    rankOnePair w v (Work.BoseB4.evec m l') l = w l * v l' := by
  simp only [rankOnePair_apply, Pi.smul_apply, smul_eq_mul, sum_evec_mul_loc]
  ring

/-- The change of variable `z ↦ Function.update x j z` is measurable. -/
private lemma measurable_update_fixed_loc {d : ℕ} (x : Xn d) (j : Fin d) :
    Measurable (fun z : Ω => Function.update x j z) := by
  refine measurable_pi_iff.mpr (fun i => ?_)
  by_cases hij : i = j
  · subst hij
    simp only [Function.update_apply]
    exact measurable_id
  · simp [hij]

/-- **The slot integrand is integrable at the weak bundle.** -/
private lemma integrable_slotIntegrand_loc {m d : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
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
      (hΘm.comp (measurable_update_fixed_loc x j))).aestronglyMeasurable ?_ ?_
  · intro z
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul ((hC z).trans (le_max_left _ _)) ((hC' _).trans (le_max_left _ _))
      (norm_nonneg _) (le_max_right _ _)
  · intro z hz
    have hz0 : e l z = 0 := Function.notMem_support.mp (fun h => hz (hsupp l h))
    simp [hz0]

/-- `∫ z, conj (η_v z) · Θ (x[j ↦ z]) = Σ_{l'} v_{l'} ∫ z, conj (e_{l'} z) · Θ (x[j ↦ z])`. -/
private lemma slotIntegral_etaOf_eq_sum_loc {m d : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
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
    (fun l' _ => (integrable_slotIntegrand_loc hmeas hbdd hsupp hΘm hΘb x j l').const_mul _)]
  refine Finset.sum_congr rfl (fun l' _ => ?_)
  rw [MeasureTheory.integral_const_mul]

/-- **A single slot expands in the coordinate basis** (weak bundle). -/
private lemma boxSlotOf_expand_loc {m d : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l))
    (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w v : Fin m → ℝ) (j : Fin d) (Θ : Xn d → ℂ)
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) :
    boxSlotOf e w v j Θ
      = ∑ l : Fin m, ∑ l' : Fin m, (w l * v l') •
          boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ := by
  funext x
  have hI := slotIntegral_etaOf_eq_sum_loc hmeas hbdd hsupp v j x Θ hΘm hΘb
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
    simp only [Finset.sum_apply, Pi.smul_apply, boxSlotOf_evec_eq_loc, Complex.real_smul,
      Complex.ofReal_mul]
  rw [hL, hR, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by ring))

/-- **The rank-one slot sum at the weak bundle:**
`boxSlotSum e (|w⟩⟨v|) Θ = Σ_j boxSlotOf e w v j Θ`. -/
private theorem boxSlotSum_rankOnePair_loc {m d : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l))
    (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w v : Fin m → ℝ) (Θ : Xn d → ℂ)
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) :
    boxSlotSum e (rankOnePair w v) Θ = ∑ j : Fin d, boxSlotOf e w v j Θ := by
  have hexp : ∀ j : Fin d, boxSlotOf e w v j Θ
      = ∑ l : Fin m, ∑ l' : Fin m, (w l * v l') •
          boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ :=
    fun j => boxSlotOf_expand_loc hmeas hbdd hsupp w v j Θ hΘm hΘb
  simp only [boxSlotSum, rankOnePair_evec_loc, hexp]

/-! ## 2. The same-slot composition of two slots

(Re-derivation of `Work.BoseBoxFock.boxSlotOf_comp_same` inside the `PotGroupDefs` cone.) -/

/-- The pairing `conj (e l) · e l'` is integrable. -/
private lemma conjE_mul_E_integrable_loc {m : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ) (l l' : Fin m) :
    Integrable (fun z : Ω => (starRingEnd ℂ) (e l z) * e l' z) := by
  choose C hC using hbdd
  have hCl : 0 ≤ C l := le_trans (norm_nonneg _) (hC l 0)
  have hCl' : 0 ≤ C l' := le_trans (norm_nonneg _) (hC l' 0)
  refine Work.MB.integrable_of_bdd_of_support (C := C l * C l')
    (Work.BoseK15.corpusBox.boxL_measurableSet ℓ)
    (Work.BoseK15.corpusBox.boxL_compact ℓ).measure_lt_top.ne ?_ ?_ ?_
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

/-- The one-particle pairing of the superposed modes: `∫ conj (η_u) · η_w = gram w u`. -/
private lemma integral_conj_etaOf_mul_etaOf_gram_loc {m : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : Ω, star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0))
    (u w : Fin m → ℝ) :
    (∫ z : Ω, (starRingEnd ℂ) (etaOf e u z) * etaOf e w z)
      = ((Work.BoseB4.gram w u : ℝ) : ℂ) := by
  have hint : ∀ l l', Integrable (fun z : Ω => star (e l z) * e l' z) := fun l l' =>
    conjE_mul_E_integrable_loc hmeas hbdd hsupp l l'
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
      * ((starRingEnd ℂ) (e l z) * e l' z)) := by
    intro l l'
    exact (hint l l').const_mul _
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
    _ = ((Work.BoseB4.gram w u : ℝ) : ℂ) := by
        congr 1
        rw [Work.BoseB4.gram]
        exact Finset.sum_congr rfl (fun l _ => mul_comm _ _)

/-- Two updates at the same slot collapse. -/
private lemma update_update_self_loc {d : ℕ} (x : Xn d) (j : Fin d) (y z : Ω) :
    Function.update (Function.update x j y) j z = Function.update x j z := by
  funext i
  simp only [Function.update_apply]
  by_cases hi : i = j <;> simp [hi]

/-- The pointwise form of the composition. -/
private lemma boxSlotOf_comp_apply_loc {m d : ℕ} {e : Fin m → Ω → ℂ} (w₁ v₁ w₂ v₂ : Fin m → ℝ)
    (j : Fin d) (Θ : Xn d → ℂ) (x : Xn d) :
    boxSlotOf e w₁ v₁ j (boxSlotOf e w₂ v₂ j Θ) x
      = etaOf e w₁ (x j) *
          ((∫ y : Ω, (starRingEnd ℂ) (etaOf e v₁ y) * etaOf e w₂ y)
            * ∫ y : Ω, (starRingEnd ℂ) (etaOf e v₂ y) * Θ (Function.update x j y)) := by
  simp only [boxSlotOf]
  rw [← integral_mul_const (∫ y : Ω, (starRingEnd ℂ) (etaOf e v₂ y) * Θ (Function.update x j y))
        (fun y : Ω => (starRingEnd ℂ) (etaOf e v₁ y) * etaOf e w₂ y)]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
  simp only []
  simp only [update_update_self_loc]
  simp
  ring

/-- **The same-slot composition of two slots is the rank-one slot of the composed one-body
operator.** -/
private theorem boxSlotOf_comp_same_loc {m d : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l))
    (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : Ω, star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (w₁ v₁ w₂ v₂ : Fin m → ℝ) (j : Fin d) (Θ : Xn d → ℂ)
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) :
    boxSlotOf e w₁ v₁ j (boxSlotOf e w₂ v₂ j Θ)
      = (((Work.BoseB4.gram w₂ v₁ : ℝ)) : ℂ) • boxSlotOf e w₁ v₂ j Θ := by
  have hI := integral_conj_etaOf_mul_etaOf_gram_loc hmeas hbdd hsupp horth v₁ w₂
  funext x
  rw [boxSlotOf_comp_apply_loc]
  simp only [boxSlotOf, Pi.smul_apply, smul_eq_mul]
  rw [hI]
  ring

/-! ## 3. Additivity of a slot over finite sums of states

(Re-derivation of `Work.BoseBoxFock.boxSlotSum_pair_decomp` inside the `PotGroupDefs` cone, with
the `AVGood` interface of that module replaced by the local `Good`.) -/

/-- The local version of `AVGood`: measurable and everywhere bounded states. -/
private def Good {n : ℕ} (Θ : Xn n → ℂ) : Prop :=
  Measurable Θ ∧ ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C

/-- A finite sum of good states is good. -/
private lemma good_finset_sum {ι : Type*} [DecidableEq ι] {n : ℕ} (s : Finset ι)
    (Ψ : ι → Xn n → ℂ) (h : ∀ k ∈ s, Good (Ψ k)) : Good (∑ k ∈ s, Ψ k) := by
  classical
  induction s using Finset.induction_on with
  | empty => refine ⟨measurable_const, ⟨0, fun x => ?_⟩⟩; simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      have h1 : Good (Ψ a) := h a (Finset.mem_insert_self a s)
      have h2 : Good (∑ k ∈ s, Ψ k) := ih (fun k hk => h k (Finset.mem_insert_of_mem hk))
      obtain ⟨Ca, hCa⟩ := h1.2
      obtain ⟨Cb, hCb⟩ := h2.2
      refine ⟨h1.1.add h2.1, ⟨max Ca 0 + max Cb 0, fun x => ?_⟩⟩
      rw [Pi.add_apply]
      exact (norm_add_le _ _).trans (add_le_add ((hCa x).trans (le_max_left _ _))
        ((hCb x).trans (le_max_left _ _)))

/-- The *joint* change of variable `(x, z) ↦ Function.update x j z` is measurable. -/
private lemma measurable_update_pair_gd {d : ℕ} (j : Fin d) :
    Measurable (fun p : (Fin d → Ω) × Ω => Function.update p.1 j p.2) := by
  refine measurable_pi_iff.mpr (fun i => ?_)
  by_cases hij : i = j
  · subst hij
    have h : (fun p : (Fin d → Ω) × Ω => Function.update p.1 i p.2 i) = fun p => p.2 := by
      funext p
      rw [Function.update_apply, if_pos rfl]
    rw [h]
    exact measurable_snd
  · have h : (fun p : (Fin d → Ω) × Ω => Function.update p.1 j p.2 i) = fun p => p.1 i := by
      funext p
      rw [Function.update_apply, if_neg hij]
    rw [h]
    exact (measurable_pi_apply i).comp measurable_fst

/-- The slot integrand is integrable at the weak bundle (state version in terms of `Good`). -/
private lemma slotIntegrand_integrable_gd {m d : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (v : Fin m → ℝ) {Θ : Xn d → ℂ} (hΘ : Good Θ) (x : Xn d) (j : Fin d) :
    Integrable (fun z : Ω => (starRingEnd ℂ) (etaOf e v z) * Θ (Function.update x j z)) := by
  obtain ⟨hΘm, hΘb⟩ := hΘ
  obtain ⟨Bv, hBvnn, hBv⟩ := Work.MB.etaOf_weak_bound hbdd v
  obtain ⟨CΘ, hCΘ⟩ := hΘb
  have hvm : Measurable (etaOf e v) := Work.MB.etaOf_weak_measurable hmeas v
  have hjoint : Measurable (fun z : Ω =>
      (starRingEnd ℂ) (etaOf e v z) * Θ (Function.update x j z)) :=
    (Complex.continuous_conj.measurable.comp hvm).mul
      (hΘm.comp (measurable_update_fixed_loc x j))
  refine Work.MB.integrable_of_bdd_of_support (S := Work.BoseK15.corpusBox.boxL ℓ)
    (C := Bv * max CΘ 0)
    (Work.BoseK15.corpusBox.boxL_measurableSet ℓ)
    (Work.BoseK15.corpusBox.boxL_compact ℓ).measure_lt_top.ne
    hjoint.aestronglyMeasurable ?_ ?_
  · intro z
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hBv z) ((hCΘ _).trans (le_max_left _ _)) (norm_nonneg _) hBvnn
  · intro z hz
    have hzv : etaOf e v z = 0 :=
      Function.notMem_support.mp (fun h => hz (Work.MB.etaOf_weak_support hsupp v h))
    rw [hzv, map_zero, zero_mul]

/-- A single slot preserves good states. -/
private lemma boxSlotOf_good_gd {m d : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w v : Fin m → ℝ) (j : Fin d) {Θ : Xn d → ℂ} (hΘ : Good Θ) :
    Good (boxSlotOf e w v j Θ) := by
  obtain ⟨hΘm, hΘb⟩ := hΘ
  have hw : Measurable (etaOf e w) := Work.MB.etaOf_weak_measurable hmeas w
  have hv : Measurable (etaOf e v) := Work.MB.etaOf_weak_measurable hmeas v
  obtain ⟨Bw, hBwnn, hBw⟩ := Work.MB.etaOf_weak_bound hbdd w
  obtain ⟨Bv, hBvnn, hBv⟩ := Work.MB.etaOf_weak_bound hbdd v
  obtain ⟨CΘ, hCΘ⟩ := hΘb
  have hupd : Measurable (fun p : (Fin d → Ω) × Ω => Function.update p.1 j p.2) :=
    measurable_update_pair_gd j
  have hjoint : Measurable (fun p : (Fin d → Ω) × Ω =>
      (starRingEnd ℂ) (etaOf e v p.2) * Θ (Function.update p.1 j p.2)) :=
    (Complex.continuous_conj.measurable.comp (hv.comp measurable_snd)).mul (hΘm.comp hupd)
  have hres : StronglyMeasurable (fun x : Fin d → Ω =>
      ∫ z : Ω, (starRingEnd ℂ) (etaOf e v z) * Θ (Function.update x j z)) :=
    hjoint.stronglyMeasurable.integral_prod_right'
  refine ⟨?_, ?_⟩
  · exact (hw.comp (measurable_pi_apply j)).mul hres.measurable
  · refine ⟨Bw * (Bv * max CΘ 0 * (volume (Work.BoseK15.corpusBox.boxL ℓ)).toReal),
      fun x => ?_⟩
    have hSmeas : MeasurableSet (Work.BoseK15.corpusBox.boxL ℓ) :=
      Work.BoseK15.corpusBox.boxL_measurableSet ℓ
    have hSfin : (volume : Measure Ω) (Work.BoseK15.corpusBox.boxL ℓ) ≠ ⊤ :=
      (Work.BoseK15.corpusBox.boxL_compact ℓ).measure_lt_top.ne
    have hfx : ∀ z : Ω, ‖(starRingEnd ℂ) (etaOf e v z) *
        Θ (Function.update x j z)‖ ≤ Bv * max CΘ 0 := by
      intro z
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul (hBv z) ((hCΘ _).trans (le_max_left _ _)) (norm_nonneg _) hBvnn
    have hpt : ∀ z : Ω, ‖(starRingEnd ℂ) (etaOf e v z) *
        Θ (Function.update x j z)‖
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
    have hbnd : ‖∫ z : Ω, (starRingEnd ℂ) (etaOf e v z) *
        Θ (Function.update x j z)‖
        ≤ Bv * max CΘ 0 * (volume (Work.BoseK15.corpusBox.boxL ℓ)).toReal := by
      calc ‖∫ z : Ω, (starRingEnd ℂ) (etaOf e v z) *
              Θ (Function.update x j z)‖
          ≤ ∫ z : Ω, ‖(starRingEnd ℂ) (etaOf e v z) *
              Θ (Function.update x j z)‖ := norm_integral_le_integral_norm _
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
            ‖∫ z : Ω, (starRingEnd ℂ) (etaOf e v z) *
              Θ (Function.update x j z)‖ := by
          rw [boxSlotOf, norm_mul]
      _ ≤ Bw * ‖∫ z : Ω, (starRingEnd ℂ) (etaOf e v z) *
              Θ (Function.update x j z)‖ := mul_le_mul_of_nonneg_right (hBw _) (norm_nonneg _)
      _ ≤ Bw * (Bv * max CΘ 0 * (volume (Work.BoseK15.corpusBox.boxL ℓ)).toReal) :=
          mul_le_mul_of_nonneg_left hbnd hBwnn

/-- The Bochner integral defining a slot is additive over finite sums of states. -/
private lemma boxSlotOf_finset_sum_gd {m d : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w v : Fin m → ℝ) (j : Fin d) {ι : Type} [DecidableEq ι] (s : Finset ι)
    (Ψ : ι → Xn d → ℂ) (hΨ : ∀ k, Good (Ψ k)) :
    boxSlotOf e w v j (∑ k ∈ s, Ψ k) = ∑ k ∈ s, boxSlotOf e w v j (Ψ k) := by
  funext x
  simp only [boxSlotOf, Finset.sum_apply]
  have hcongr : (fun z : Ω => (starRingEnd ℂ) (etaOf e v z) *
        (∑ k ∈ s, Ψ k (Function.update x j z)))
      = fun z : Ω => ∑ k ∈ s, (starRingEnd ℂ) (etaOf e v z) * Ψ k (Function.update x j z) := by
    funext z
    rw [Finset.mul_sum]
  rw [hcongr, integral_finsetSum _ (fun k _ =>
    slotIntegrand_integrable_gd hmeas hbdd hsupp v (hΨ k) x j)]
  rw [Finset.mul_sum]

/-- `boxSlotSum` is homogeneous in the one-body operator (real scalars). -/
private lemma boxSlotSum_smul_real_gd {m d : ℕ} (e : Fin m → Ω → ℂ) (r : ℝ)
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

/-- Splitting a double sum into its off-diagonal part and its diagonal. -/
private lemma sum_sum_univ_eq_erase_add_gd {d : ℕ} {M : Type*} [AddCommMonoid M]
    (f : Fin d → Fin d → M) :
    (∑ j : Fin d, ∑ j' : Fin d, f j j')
      = (∑ j : Fin d, ∑ j' ∈ Finset.univ.erase j, f j j') + ∑ j : Fin d, f j j := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  exact (Finset.sum_erase_add _ _ (Finset.mem_univ j)).symm

/-- **The pair decomposition of two rank-one slots.** -/
private theorem boxSlotSum_pair_decomp_loc {m d : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l))
    (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : Ω, star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (w₁ v₁ w₂ v₂ : Fin m → ℝ) (Θ : Xn d → ℂ)
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) :
    boxSlotSum e (rankOnePair w₁ v₁) (boxSlotSum e (rankOnePair w₂ v₂) Θ)
      = boxSlotSum e ((rankOnePair w₁ v₁).comp (rankOnePair w₂ v₂)) Θ
        + ∑ j : Fin d, ∑ j' ∈ Finset.univ.erase j,
            boxSlotOf e w₁ v₁ j (boxSlotOf e w₂ v₂ j' Θ) := by
  classical
  have hΘ : Good Θ := ⟨hΘm, hΘb⟩
  have hΨ : Good (∑ j' : Fin d, boxSlotOf e w₂ v₂ j' Θ) :=
    good_finset_sum Finset.univ (fun j' => boxSlotOf e w₂ v₂ j' Θ)
      (fun j' _ => boxSlotOf_good_gd hmeas hbdd hsupp w₂ v₂ j' hΘ)
  have hL : boxSlotSum e (rankOnePair w₁ v₁) (boxSlotSum e (rankOnePair w₂ v₂) Θ)
      = ∑ j : Fin d, ∑ j' : Fin d,
          boxSlotOf e w₁ v₁ j (boxSlotOf e w₂ v₂ j' Θ) := by
    rw [boxSlotSum_rankOnePair_loc hmeas hbdd hsupp w₂ v₂ Θ hΘm hΘb]
    rw [boxSlotSum_rankOnePair_loc hmeas hbdd hsupp w₁ v₁
      (∑ j' : Fin d, boxSlotOf e w₂ v₂ j' Θ) hΨ.1 hΨ.2]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [boxSlotOf_finset_sum_gd hmeas hbdd hsupp w₁ v₁ j Finset.univ
      (fun j' => boxSlotOf e w₂ v₂ j' Θ)
      (fun j' => boxSlotOf_good_gd hmeas hbdd hsupp w₂ v₂ j' hΘ)]
  have hc : (∑ l : Fin m, v₁ l * w₂ l) = Work.BoseB4.gram w₂ v₁ := by
    rw [Work.BoseB4.gram]
    exact Finset.sum_congr rfl (fun l _ => mul_comm _ _)
  have hR1 : boxSlotSum e
        ((rankOnePair w₁ v₁).comp (rankOnePair w₂ v₂)) Θ
      = ∑ j : Fin d, boxSlotOf e w₁ v₁ j (boxSlotOf e w₂ v₂ j Θ) := by
    rw [rankOnePair_comp]
    rw [boxSlotSum_smul_real_gd]
    rw [boxSlotSum_rankOnePair_loc hmeas hbdd hsupp w₁ v₂ Θ hΘm hΘb]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [boxSlotOf_comp_same_loc hmeas hbdd hsupp horth w₁ v₁ w₂ v₂ j Θ hΘm hΘb, hc]
  have hsplit := sum_sum_univ_eq_erase_add_gd (fun (j j' : Fin d) =>
      boxSlotOf e w₁ v₁ j (boxSlotOf e w₂ v₂ j' Θ))
  rw [hL, hR1, hsplit]
  exact add_comm _ _

/-! ## 4. The `pairSet` form of the slot-form four-letter word -/

/-- **The `pairSet` sum is the sum over the erased rows.** -/
private lemma sum_pairSet_eq_univ_erase_loc {N : ℕ} {M : Type*} [AddCommMonoid M]
    (f : Fin N → Fin N → M) :
    (∑ p ∈ Submission.BoseGases.pairSet N, f p.1 p.2)
      = ∑ j : Fin N, ∑ j' ∈ Finset.univ.erase j, f j j' := by
  rw [Submission.BoseGases.pairSet, Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hfe : (Finset.univ.filter (fun j' : Fin N => j ≠ j')) = Finset.univ.erase j := by
    ext x
    simp [Finset.mem_erase, ne_comm]
  rw [← hfe, Finset.sum_filter]
/-! ## 5. The target -/

/-- **The pair decomposition of two rank-one slots, in `pairSet` form.**  The off-diagonal part of
`B(|w₁⟩⟨v₁|) ∘ B(|w₂⟩⟨v₂|)` — that is, `B(T₁)(B(T₂)Θ) − B(T₁∘T₂)Θ` — is the sum over the ordered
pairs of *distinct* slots.  This is the general-arity form of the slot decomposition used by the
cubic row of FS `lem:2ndQuand`. -/
theorem pairDecompPairSetGen {m n : ℕ} {ℓ : ℝ} {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l))
    (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (w₁ v₁ w₂ v₂ : Fin m → ℝ) (Θ : Work.BoseDict.Xn n → ℂ)
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) :
    Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOnePair w₁ v₁)
        (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOnePair w₂ v₂) Θ)
      - Work.BoseDict.boxSlotSum e
          ((Work.BoseBoxFock.rankOnePair w₁ v₁).comp (Work.BoseBoxFock.rankOnePair w₂ v₂)) Θ
      = ∑ p ∈ Submission.BoseGases.pairSet n,
          Work.BoseDict.boxSlotOf e w₁ v₁ p.1 (Work.BoseDict.boxSlotOf e w₂ v₂ p.2 Θ) := by
  rw [boxSlotSum_pair_decomp_loc hmeas hbdd hsupp horth w₁ v₁ w₂ v₂ Θ hΘm hΘb,
    add_sub_cancel_left]
  exact (sum_pairSet_eq_univ_erase_loc (fun j j' => boxSlotOf e w₁ v₁ j
    (boxSlotOf e w₂ v₂ j' Θ))).symm

end Work.BoseBoxFock
