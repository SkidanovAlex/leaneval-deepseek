import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.sliceFCRealise
import Submission.Work.MB.SlotSumSplitAux
import Submission.Work.MB.sliceF_mem_monSpan_weak
import Submission.Work.MB.slotInt_peelMB_weak
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.MB.exists_realFock_eq_sliceF_re_im_ae`

The **measurable/bounded** ("weak") twin of `Work.BoseBoxFock.exists_realFock_eq_sliceF_re_im`
(`Submission/Work/BoseBoxFock/sliceFCRealise.lean`): for a mode family `e` that is only
*measurable*, *everywhere bounded* and *supported in the corpus box* `boxL ℓ`
(`Work.BoseK15.corpusBox.boxL ℓ`), and a state `Φ` that is only *measurable*, *everywhere bounded*,
*box supported* (`Work.MB.boxPow n ℓ`) and *permutation symmetric*, the slice
`Work.BoseBoxFock.sliceF e S Φ y` of the sector `S` at the complement configuration `y` is the sum

    boxRealise e S.card Ψ₁ + I • boxRealise e S.card Ψ₂

of the realisations of **two real** model vectors `Ψ₁ Ψ₂ : Work.BoseB4.RealFock m`.

Why this module exists: the strong chain (`sliceFCRealise`) assumes the modes are `Continuous`
with `HasCompactSupport`, which the *honest* modes of the box ↔ model bridge **cannot** satisfy
(`Work.BoseBoxFock.no_continuous_mode_family`, see
`FINDING_continuous_hypotheses_UNSATISFIABLE.md`).  The honest mode bundle is exactly
`hmeas` + `hbdE` + `hsupp` (+ orthonormality/pinning, which are *not* needed here), so the
selection chain has to be re-run in this class; this module is the slice-realisation step (W4 of
the FINDING) of that re-run.

The proof is the same three-layer argument as the strong one, with the *only* change being how
integrability is obtained (boundedness + box support + finite measure of the box instead of
continuity + compact support):

* `Work.MB.slotInt_comp_perm_weak` / `Work.MB.slotExact_comp_perm_weak` — the slot calculus is
  permutation equivariant (through the weak peel lemma `Work.MB.slotInt_peelMB_weak`), hence the
  sector `slotExact e S Φ` of a symmetric state is invariant under slot permutations preserving
  `S`; composed with the (hypothesis-free) combinatorics `pairCoord_comp_sliceF` this gives
  `Work.MB.sliceF_symm_weak` — the slice is symmetric in its `Fin S.card` variables;
* **`Work.MB.sliceF_mem_monSpan_weak`** (delegated) — the slice lies in the `ℂ`-span of the mode
  monomials `∏_i e (l i) (u i)`;
* `Work.BoseBoxFock.symm_mem_span_range_boxRealiseC` — a *symmetric* element of that span is the
  `ℂ`-linear realisation `boxRealiseC e _ Ψ` of a complexified Fock vector, and
  `Work.BoseBoxFock.boxRealiseC_eq_re_add_im` splits it into the real and imaginary parts.

Nothing in this argument uses orthonormality of the modes or the pinning, so the statement is
strictly a statement about the sector algebra and the (algebraic) realisation.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.MB

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The slot calculus is permutation equivariant (weak class)

This is the weak twin of `Work.BoseBoxFock.slotInt_comp_perm`, obtained from the weak peel lemma
`Work.MB.slotInt_peelMB_weak` by induction on the slot set `T`. -/

/-- **The slot projection permutes its slots** (weak class).  For a symmetric, measurable, bounded
state `Φ`, projecting the slots of `T` in the permuted configuration `x ∘ τ` is the same as
projecting the slots of `τ '' T` in the configuration `x`. -/
theorem slotInt_comp_perm_weak {m n : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (Φ : (Fin n → E3) → ℂ)
    (hΦsym : ∀ τ : Equiv.Perm (Fin n), (fun x => Φ (x ∘ τ)) = Φ)
    (hΦm : Measurable Φ) (hΦb : ∃ C, ∀ y, ‖Φ y‖ ≤ C) :
    ∀ (T : Finset (Fin n)) (τ : Equiv.Perm (Fin n)) (x : Fin n → E3),
      Work.BoseBoxFock.slotInt e T Φ (x ∘ τ)
        = Work.BoseBoxFock.slotInt e (T.map τ.toEmbedding) Φ x := by
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro τ x
    rw [Finset.map_empty, Work.BoseBoxFock.slotInt_empty]
    exact congrFun (hΦsym τ) x
  | insert a s ha ih =>
    intro τ x
    have hins : insert a s = s ∪ {a} := by rw [Finset.insert_eq, Finset.union_comm]
    rw [hins]
    -- peel the slot `a`
    have hpeel : Work.BoseBoxFock.slotInt e (s ∪ {a}) Φ
        = Work.BoseBoxFock.slotProj1 e a (Work.BoseBoxFock.slotInt e s Φ) :=
      slotInt_peelMB_weak hmeas hbdE hsupp ha Φ hΦm hΦb
    -- the slot `a` peeled off the permuted set
    have hτa : τ a ∉ s.map τ.toEmbedding := by
      rw [Finset.mem_map]
      rintro ⟨b, hb, hba⟩
      exact ha (τ.injective hba ▸ hb)
    have hpeel2 : Work.BoseBoxFock.slotInt e (s.map τ.toEmbedding ∪ {τ a}) Φ
        = Work.BoseBoxFock.slotProj1 e (τ a)
            (Work.BoseBoxFock.slotInt e (s.map τ.toEmbedding) Φ) :=
      slotInt_peelMB_weak hmeas hbdE hsupp hτa Φ hΦm hΦb
    have hmap : Finset.map τ.toEmbedding (s ∪ {a}) = s.map τ.toEmbedding ∪ {τ a} := by
      rw [Finset.map_union, Finset.map_singleton, Equiv.toEmbedding_apply]
    rw [hmap, hpeel, hpeel2]
    simp only [Work.BoseBoxFock.slotProj1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [Function.comp_apply, Work.BoseBoxFock.permUpdate_comp τ x a w]
    rw [ih τ (Function.update x (τ a) w)]

/-- **The sector is invariant under permutations of the slots preserving `S`** (weak class).  For a
symmetric state `Φ` and a permutation `τ` of the slots with `i ∈ S ↔ τ i ∈ S`, the sector
`slotExact e S Φ` is unchanged by precomposing with `τ`. -/
theorem slotExact_comp_perm_weak {m n : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (Φ : (Fin n → E3) → ℂ)
    (hΦsym : ∀ τ : Equiv.Perm (Fin n), (fun x => Φ (x ∘ τ)) = Φ)
    (hΦm : Measurable Φ) (hΦb : ∃ C, ∀ y, ‖Φ y‖ ≤ C)
    (S : Finset (Fin n)) (τ : Equiv.Perm (Fin n)) (hτ : ∀ i, i ∈ S ↔ τ i ∈ S) :
    (fun x : Fin n → E3 => Work.BoseBoxFock.slotExact e S Φ (x ∘ τ))
      = Work.BoseBoxFock.slotExact e S Φ := by
  funext x
  simp only [Work.BoseBoxFock.slotExact, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_bij (fun T _ => T.map τ.toEmbedding) ?_ ?_ ?_ ?_
  · intro T hT
    rw [Finset.mem_filter] at hT ⊢
    exact ⟨Finset.mem_univ _, Work.BoseBoxFock.subset_map_perm hτ hT.2⟩
  · intro T₁ _ T₂ _ h
    exact Finset.map_inj.mp h
  · intro b hb
    rw [Finset.mem_filter] at hb
    refine ⟨b.map τ.symm.toEmbedding, ?_, Work.BoseBoxFock.map_symm_map_toEmbedding τ b⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, Work.BoseBoxFock.subset_map_perm ?_ hb.2⟩
    intro i
    have h := hτ (τ.symm i)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  · intro T _
    rw [Finset.card_map]
    simp only [Work.BoseBoxFock.slotProj_eq_slotInt]
    rw [slotInt_comp_perm_weak hmeas hbdE hsupp Φ hΦsym hΦm hΦb T τ x]

/-- **The slice of a sector is symmetric in its slots** (weak class).  The weak twin of
`Work.BoseBoxFock.sliceF_symm`. -/
theorem sliceF_symm_weak {m n : ℕ} {ℓ : ℝ} (e : Fin m → E3 → ℂ)
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (S : Finset (Fin n)) (Φ : (Fin n → E3) → ℂ)
    (hΦm : Measurable Φ) (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C)
    (hΦsym : ∀ σ : Equiv.Perm (Fin n), (fun x : Fin n → E3 => Φ (x ∘ σ)) = Φ)
    (y : {i // i ∉ S} → E3) :
    ∀ σ : Equiv.Perm (Fin S.card),
      (fun u : Fin S.card → E3 => Work.BoseBoxFock.sliceF e S Φ y (u ∘ σ)) =
        Work.BoseBoxFock.sliceF e S Φ y := by
  intro σ
  funext u
  show Work.BoseBoxFock.slotExact e S Φ
      (Work.BoseBoxFock.pairCoord S (fun i => u (σ (S.equivFin i))) y)
      = Work.BoseBoxFock.slotExact e S Φ
        (Work.BoseBoxFock.pairCoord S (fun i => u (S.equivFin i)) y)
  rw [Work.BoseBoxFock.pairCoord_comp_sliceF S σ u y]
  exact congrFun (slotExact_comp_perm_weak hmeas hbdE hsupp Φ hΦsym hΦm hΦb S _
    fun i => Work.BoseBoxFock.permExtend_mem) _

/-! ## 2. The slice realisation -/

/-- **The slice of a sector of a weak state is the sum of the realisations of two real model
vectors.**  This is the weak twin of `Work.BoseBoxFock.exists_realFock_eq_sliceF_re_im`, and the
form in which the BF3c fibre selection consumes it. -/
theorem exists_realFock_eq_sliceF_re_im_ae {m n : ℕ} {ℓ : ℝ}
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (S : Finset (Fin n)) (Φ : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ)
    (hΦm : Measurable Φ) (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C)
    (hΦsupp : Function.support Φ ⊆ Work.MB.boxPow n ℓ)
    (hΦsym : ∀ σ : Equiv.Perm (Fin n),
      (fun x : Fin n → EuclideanSpace ℝ (Fin 3) => Φ (x ∘ σ)) = Φ)
    (y : {i // i ∉ S} → EuclideanSpace ℝ (Fin 3)) :
    ∃ Ψ₁ Ψ₂ : Work.BoseB4.RealFock m,
      Work.BoseDict.boxRealise e S.card Ψ₁
        + Complex.I • Work.BoseDict.boxRealise e S.card Ψ₂
        = Work.BoseBoxFock.sliceF e S Φ y := by
  obtain ⟨Ψ, hΨ⟩ := Work.BoseBoxFock.symm_mem_span_range_boxRealiseC e
    (sliceF_symm_weak e hmeas hbdE hsupp S Φ hΦm hΦb hΦsym y)
    (sliceF_mem_monSpan_weak e hmeas hbdE hsupp S Φ hΦm hΦb y)
  exact ⟨Work.BoseBoxFock.realPart Ψ, Work.BoseBoxFock.imagPart Ψ, by
    rw [← Work.BoseBoxFock.boxRealiseC_eq_re_add_im e Ψ, hΨ]⟩

end Work.MB
