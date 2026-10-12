import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseDict.boxRealise_cIPn
import Submission.Work.BoseDict.boxRealise_dGamma
import Submission.Work.BoseDictC.modeProd_eq_zero_of_sum_ne
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseDict.bomb_dGamma_slot` — the one-body row of the box ↔ model dictionary

The target is the pairing identity that turns the *second quantisation* into the
*first quantisation* of a one-body operator, in the form in which the assembly consumes
it:

    `bomb m Ψ (dGamma m T Ψ) = re (cIPn d (boxRealise e d Ψ) (boxSlotSum e T (boxRealise e d Ψ)))`.

It is assembled from the two already-proved dictionary identities

* `Work.BoseDict.boxRealise_dGamma` — `boxRealise e d (dGamma m T Ψ)
  = boxSlotSum e T (boxRealise e d Ψ)`, and
* `Work.BoseDict.boxRealise_cIPn_gen` (below) — the isometry
  `cIPn d (boxRealise e d Ψ) (boxRealise e d Ψ') = ((bomb m Ψ Ψ' : ℝ) : ℂ)`,

where the *only* hypothesis on the first vector is the degree-`d` support condition (`Ψ`
must lie in the `d`-particle sector).  The second vector, `dGamma m T Ψ`, is not known
a priori to live in the degree-`d` sector — that is exactly why the general form is
needed: `boxRealise e d` kills every multi-index of degree `≠ d`, so the isometry holds
verbatim for an arbitrary second vector, with no degree hypothesis (the earlier
`boxRealise_cIPn` asked for one because its proof used the guarded expansion of
`boxRealise` on both arguments).

## Proof

* `boxRealise_eq_sum_gen` — the expansion of `boxRealise e d Ψ'` on `Ψ'.support` *without*
  the degree guard: on the multi-indices of degree `≠ d` the guard is irrelevant because
  the mode product itself vanishes (`Work.BoseDictC.modeProd_eq_zero_of_sum_ne`, since
  `modeProd e d β` is a sum over the labellings `σ : Fin d → Fin m`, all of which have
  total occupation `d`).
* `boxRealise_cIPn_gen` — the general isometry, by the same computation as
  `boxRealise_cIPn` (`cIPn_sum_sum` + orthonormality `modeProd_cIPn` + `coeff_arith2`);
  the single new point is that in the inner sum over `β ∈ Ψ'.support` one splits on
  `β.sum = d`: for `β.sum = d` the orthonormality `modeProd_cIPn` applies, while for
  `β.sum ≠ d` the vector `modeProd e d β` is the zero function, so the term vanishes —
  which is also what the diagonal formula `if α = β then … else 0` gives there, because
  `α ≠ β` for `α ∈ Ψ.support` (all of whose elements have degree `d`).
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseDict

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The unguarded expansion of the box realisation -/

/-- The realisation of the model on the box, expanded on the support of `Ψ` **without**
the degree guard: on multi-indices of total degree `≠ d` the guard can be dropped because
the mode product `modeProd e d β` vanishes there. -/
lemma boxRealise_eq_sum_gen {m d : ℕ} (e : Fin m → Sp → ℂ)
    (Ψ : Work.BoseB4.RealFock m) :
    boxRealise e d Ψ
      = fun x : Xn d => ∑ α ∈ Ψ.support,
          ((Ψ α * (Work.BoseB4.mfac α / Real.sqrt (d.factorial : ℝ)) : ℝ) : ℂ)
            * modeProd e d α x := by
  funext x
  rw [boxRealise, Finsupp.lsum_apply, Finsupp.sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun α _ => ?_
  by_cases h : α.sum (fun _ k => k) = d
  · rw [if_pos h]
    simp only [LinearMap.toSpanSingleton_apply, Pi.smul_apply, Complex.real_smul, smul_smul]
    push_cast
    ring
  · rw [if_neg h]
    rw [Work.BoseDictC.modeProd_eq_zero_of_sum_ne α h x]
    simp

/-! ## 2. The isometry with an arbitrary second vector -/

/-- **The box ↔ model isometry**, with the degree hypothesis only on the *first* vector:
for `Ψ` supported in the degree-`d` sector and an arbitrary `Ψ'`,

    `cIPn d (boxRealise e d Ψ) (boxRealise e d Ψ') = ((bomb m Ψ Ψ' : ℝ) : ℂ)`.

(`boxRealise e d` annihilates the components of `Ψ'` of degree `≠ d`, and so does `bomb`
against `Ψ`, whose support has degree `d` throughout.) -/
theorem boxRealise_cIPn_gen {m d : ℕ} {ℓ : ℝ} {e : Fin m → Sp → ℂ}
    (he : ∀ l l', (∫ x : Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (Ψ Ψ' : Work.BoseB4.RealFock m)
    (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = d) :
    cIPn d (boxRealise e d Ψ) (boxRealise e d Ψ') = ((Work.BoseB4.bomb m Ψ Ψ' : ℝ) : ℂ) := by
  classical
  have hA := boxRealise_eq_sum (e := e) (d := d) Ψ hΨ
  have hB := boxRealise_eq_sum_gen (e := e) (d := d) Ψ'
  have hmain : cIPn d (boxRealise e d Ψ) (boxRealise e d Ψ')
      = ∑ α ∈ Ψ.support, ∑ β ∈ Ψ'.support,
          (((Ψ α * (Work.BoseB4.mfac α / Real.sqrt (d.factorial : ℝ)) : ℝ) : ℂ)
            * ((Ψ' β * (Work.BoseB4.mfac β / Real.sqrt (d.factorial : ℝ)) : ℝ) : ℂ))
            * cIPn d (modeProd e d α) (modeProd e d β) := by
    rw [hA, hB]
    exact cIPn_sum_sum Ψ.support Ψ'.support
      (fun α => Ψ α * (Work.BoseB4.mfac α / Real.sqrt (d.factorial : ℝ)))
      (fun β => Ψ' β * (Work.BoseB4.mfac β / Real.sqrt (d.factorial : ℝ)))
      (fun α => modeProd e d α) (fun β => modeProd e d β)
      (fun α _ β _ => integrable_conj_modeProd_mul hbdd hsupp α β)
  rw [hmain]
  -- orthonormality of the mode products, with the degree hypothesis discharged by
  -- the vanishing of the mode product outside degree `d`.
  have hterm : ∀ α ∈ Ψ.support, ∀ β ∈ Ψ'.support,
      cIPn d (modeProd e d α) (modeProd e d β)
        = (if α = β then ((d.factorial : ℝ) / Work.BoseB4.mfac α : ℂ) else 0) := by
    intro α hα β _
    by_cases hd : β.sum (fun _ k => k) = d
    · exact modeProd_cIPn he hbdd hsupp (hΨ α hα) hd
    · rw [show modeProd e d β = 0 from
          funext (Work.BoseDictC.modeProd_eq_zero_of_sum_ne β hd),
        if_neg (fun h : α = β => hd (h ▸ hΨ α hα))]
      simp [cIPn]
  have hinner : ∀ α ∈ Ψ.support,
      (∑ β ∈ Ψ'.support,
          (((Ψ α * (Work.BoseB4.mfac α / Real.sqrt (d.factorial : ℝ)) : ℝ) : ℂ)
            * ((Ψ' β * (Work.BoseB4.mfac β / Real.sqrt (d.factorial : ℝ)) : ℝ) : ℂ))
            * cIPn d (modeProd e d α) (modeProd e d β))
        = ((Work.BoseB4.mfac α * Ψ α * Ψ' α : ℝ) : ℂ) := by
    intro α hα
    rw [Finset.sum_congr rfl (fun β hβ => by rw [hterm α hα β hβ])]
    have hs : Real.sqrt (d.factorial : ℝ) * Real.sqrt (d.factorial : ℝ) = (d.factorial : ℝ) := by
      rw [← sq, Real.sq_sqrt (by positivity)]
    have hD : (d.factorial : ℝ) ≠ 0 := ne_of_gt (by positivity)
    have hmf : Work.BoseB4.mfac α ≠ 0 := ne_of_gt (Work.BoseB4.BombSelf.mfac_pos α)
    have harith := coeff_arith2 (mf := Work.BoseB4.mfac α) (D := (d.factorial : ℝ))
      (s := Real.sqrt (d.factorial : ℝ)) (ψ := Ψ α) (ψ' := Ψ' α) hs hD hmf
    by_cases hmem : α ∈ Ψ'.support
    · rw [Finset.sum_eq_single α]
      · rw [if_pos rfl]
        have hcast : ((Ψ α * (Work.BoseB4.mfac α / Real.sqrt (d.factorial : ℝ)) : ℝ) : ℂ)
              * ((Ψ' α * (Work.BoseB4.mfac α / Real.sqrt (d.factorial : ℝ)) : ℝ) : ℂ)
              * ((d.factorial : ℝ) / Work.BoseB4.mfac α : ℂ)
            = (((Ψ α * (Work.BoseB4.mfac α / Real.sqrt (d.factorial : ℝ)))
                * (Ψ' α * (Work.BoseB4.mfac α / Real.sqrt (d.factorial : ℝ)))
                * ((d.factorial : ℝ) / Work.BoseB4.mfac α) : ℝ) : ℂ) := by
          push_cast
          ring
        rw [hcast, harith]
      · intro β _ hne
        rw [if_neg (fun h : α = β => hne h.symm)]
        ring
      · intro hnot
        exact absurd hmem hnot
    · rw [Finset.sum_eq_zero]
      · rw [Finsupp.notMem_support_iff.mp hmem]
        simp
      · intro β hβ
        rw [if_neg (fun h : α = β => hmem (h ▸ hβ))]
        ring
  rw [Finset.sum_congr rfl hinner]
  rw [Work.BoseB4.bomb_apply, Finsupp.sum]
  exact (Complex.ofReal_sum (s := Ψ.support)
    (f := fun a => Work.BoseB4.mfac a * Ψ a * Ψ' a)).symm

/-! ## 3. The one-body row of the dictionary -/

theorem bomb_dGamma_slot {m d : ℕ} {ℓ : ℝ} {e : Fin m → Work.BoseDict.Sp → ℂ}
    (he : ∀ l l', (∫ x : Work.BoseDict.Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (Ψ : Work.BoseB4.RealFock m)
    (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = d) :
    Work.BoseB4.bomb m Ψ (Work.BoseB4.dGamma m T Ψ)
      = (Work.BoseDict.cIPn d (Work.BoseDict.boxRealise e d Ψ)
          (Work.BoseDict.boxSlotSum e T (Work.BoseDict.boxRealise e d Ψ))).re := by
  rw [← boxRealise_dGamma he hbdd hsupp T Ψ hΨ]
  rw [boxRealise_cIPn_gen he hbdd hsupp Ψ (Work.BoseB4.dGamma m T Ψ) hΨ]
  simp

end Work.BoseDict
