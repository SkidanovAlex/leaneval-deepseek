/-
# Uniqueness of epic `∗`-regular envelopes ([JZLA20, Theorem 2.9] = [Jaikin, GAFA 2019, Thm 6.3])

The target of this file is `envelopeUniqueness_star`: two epic `∗`-regular `R`-rings inducing the
same rank function on the matrices over `R` are isomorphic, compatibly with the structure maps and
the rank functions.

## Proof structure

Let `φ₁ : R →+* U₁`, `φ₂ : R →+* U₂` be epic `∗`-homomorphisms into `∗`-regular rings with
faithful rank functions `rk₁`, `rk₂` which agree on matrices over `R`.

* `T := diagClosure φ₁ φ₂ h₁ h₂` is the `∗`-regular closure, inside `U₁ × U₂`, of the image `Δ` of
  the diagonal homomorphism `r ↦ (φ₁ r, φ₂ r)` (`DiagClosureDefs.lean`).
* The two projections `projFst`, `projSnd : ↥T →+* Uᵢ` are epic (because `projFst ∘ toClosure = φ₁`
  and `φ₁` is epic) and surjective ([`projFst_surjective_diagClosure`]).
* The inclusion `Δ ↪ T` is epic (this is [Jaikin, GAFA 2019, Proposition 6.1], the "if" direction
  of [JZLA20, Proposition 2.7]), and the two rank functions `rk₁ ∘ projFst`, `rk₂ ∘ projSnd` on
  `T` agree on matrices over `Δ` (`rank_eq_on_diag` below: matrices over `Δ` lift to matrices over
  `R` along the surjection `R ↠ Δ`); since `T` is von Neumann regular,
  [Jaikin, GAFA 2019, Proposition 5.11] (the regular case of Li's theorem) shows that they agree
  on *all* matrices over `T`.
* Specialising to the `1 × 1` matrices with entry in `ker projFst` gives `ker projFst = 0`
  (faithfulness of `rk₂`), and symmetrically; hence `projFst` is a ring isomorphism and
  `e := projFst.symm.trans projSnd` is the required isomorphism.

The inputs that are not proved in this file are imported from the sibling modules
`Section3/isStarRegular_prod`, `Section3/projFst_surjective_diagClosure`,
`Section3/projSnd_surjective_diagClosure`,
`Section3/isEpic_inclusion_diagStarSubring_diagClosure` (all proved there) and
`Section3/rk_eq_of_pullback_eq_of_isEpic_vnRegular`, which is [Jaikin, GAFA 2019,
Proposition 5.11] (the regular case of Li's theorem, [Li, Theorem 8.1]).
-/
import Mathlib
import Submission.Work.ORHughesFree.Section3.EnvelopeUniqueness
import Submission.Work.ORHughesFree.Section3.DiagClosureDefs
import Submission.Work.ORHughesFree.Epic
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.StarRegular.starRegularClosure_isStarRegular
import Submission.Work.Section3.isStarRegular_prod
import Submission.Work.Section3.projFst_surjective_diagClosure
import Submission.Work.Section3.projSnd_surjective_diagClosure
import Submission.Work.Section3.rk_eq_of_pullback_eq_of_isEpic_vnRegular
import Submission.Work.Section3.isEpic_inclusion_diagStarSubring_diagClosure

set_option autoImplicit false

universe u

namespace Work.ORHughesFree.Section3

open Work.ORHughesFree Matrix

variable {R : Type u} [Ring R] [StarRing R]

section Diagonal

variable {U₁ : Type u} [Ring U₁] [StarRing U₁] {U₂ : Type u} [Ring U₂] [StarRing U₂]

/-- The diagonal homomorphism, corestricted to `Δ`, as a ring homomorphism. -/
noncomputable def toDiag (φ₁ : R →+* U₁) (φ₂ : R →+* U₂)
    (h₁ : ∀ x : R, φ₁ (star x) = star (φ₁ x)) (h₂ : ∀ x : R, φ₂ (star x) = star (φ₂ x)) :
    R →+* ↥(diagStarSubring φ₁ φ₂ h₁ h₂).toSubring :=
  (diagHom φ₁ φ₂).codRestrict _ (fun r => ⟨r, rfl⟩)

@[simp]
theorem toDiag_apply (φ₁ : R →+* U₁) (φ₂ : R →+* U₂)
    (h₁ : ∀ x : R, φ₁ (star x) = star (φ₁ x)) (h₂ : ∀ x : R, φ₂ (star x) = star (φ₂ x))
    (r : R) :
    ((toDiag φ₁ φ₂ h₁ h₂ r : ↥(diagStarSubring φ₁ φ₂ h₁ h₂).toSubring) : U₁ × U₂) =
      (φ₁ r, φ₂ r) := rfl

theorem toDiag_surjective (φ₁ : R →+* U₁) (φ₂ : R →+* U₂)
    (h₁ : ∀ x : R, φ₁ (star x) = star (φ₁ x)) (h₂ : ∀ x : R, φ₂ (star x) = star (φ₂ x)) :
    Function.Surjective (toDiag φ₁ φ₂ h₁ h₂) := by
  intro d
  obtain ⟨r, hr⟩ := (mem_diagStarSubring_iff φ₁ φ₂ h₁ h₂).mp d.2
  exact ⟨r, Subtype.ext (by simpa using hr)⟩

/-- The inclusion `Δ ↪ T`, as a ring homomorphism. -/
noncomputable def inclDiag (φ₁ : R →+* U₁) (φ₂ : R →+* U₂)
    (h₁ : ∀ x : R, φ₁ (star x) = star (φ₁ x)) (h₂ : ∀ x : R, φ₂ (star x) = star (φ₂ x)) :
    ↥(diagStarSubring φ₁ φ₂ h₁ h₂).toSubring →+* ↥(diagClosure φ₁ φ₂ h₁ h₂) :=
  Subring.inclusion (Work.ORHughesFree.subset_starRegularClosure _)

theorem projFst_toDiag (φ₁ : R →+* U₁) (φ₂ : R →+* U₂)
    (h₁ : ∀ x : R, φ₁ (star x) = star (φ₁ x)) (h₂ : ∀ x : R, φ₂ (star x) = star (φ₂ x)) :
    (projFst φ₁ φ₂ h₁ h₂).comp ((inclDiag φ₁ φ₂ h₁ h₂).comp (toDiag φ₁ φ₂ h₁ h₂)) = φ₁ := by
  ext r
  rfl

theorem projSnd_toDiag (φ₁ : R →+* U₁) (φ₂ : R →+* U₂)
    (h₁ : ∀ x : R, φ₁ (star x) = star (φ₁ x)) (h₂ : ∀ x : R, φ₂ (star x) = star (φ₂ x)) :
    (projSnd φ₁ φ₂ h₁ h₂).comp ((inclDiag φ₁ φ₂ h₁ h₂).comp (toDiag φ₁ φ₂ h₁ h₂)) = φ₂ := by
  ext r
  rfl

/-- **The rank agreement on `Δ`**: the two projected rank functions on the closure ring agree on
every matrix which is the image of a matrix over the diagonal `∗`-subring; this is the hypothesis
of the theorem, transported along the surjection `R ↠ Δ`. -/
theorem rank_eq_on_diag (φ₁ : R →+* U₁) (φ₂ : R →+* U₂)
    (h₁ : ∀ x : R, φ₁ (star x) = star (φ₁ x)) (h₂ : ∀ x : R, φ₂ (star x) = star (φ₂ x))
    (rk₁ : SylvesterRank U₁) (rk₂ : SylvesterRank U₂)
    (hmat : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) R),
      rk₁.rk n m (A.map φ₁) = rk₂.rk n m (A.map φ₂))
    (n m : ℕ) (A : Matrix (Fin n) (Fin m) ↥(diagStarSubring φ₁ φ₂ h₁ h₂).toSubring) :
    rk₁.rk n m ((A.map (inclDiag φ₁ φ₂ h₁ h₂)).map (projFst φ₁ φ₂ h₁ h₂)) =
      rk₂.rk n m ((A.map (inclDiag φ₁ φ₂ h₁ h₂)).map (projSnd φ₁ φ₂ h₁ h₂)) := by
  classical
  choose lift hlift using fun i j =>
    (mem_diagStarSubring_iff φ₁ φ₂ h₁ h₂).mp (A i j).2
  have hA : A = Matrix.of (fun i j => toDiag φ₁ φ₂ h₁ h₂ (lift i j)) := by
    refine Matrix.ext fun i j => ?_
    rw [Matrix.of_apply]
    refine Subtype.ext (show (A i j : U₁ × U₂) = (toDiag φ₁ φ₂ h₁ h₂ (lift i j) : U₁ × U₂) by
      rw [toDiag_apply]
      exact (hlift i j).symm)
  have e1 : ((Matrix.of (fun i j => toDiag φ₁ φ₂ h₁ h₂ (lift i j))).map
        (inclDiag φ₁ φ₂ h₁ h₂)).map (projFst φ₁ φ₂ h₁ h₂)
      = (Matrix.of (fun i j => lift i j)).map φ₁ := by
    ext i j
    exact RingHom.congr_fun (projFst_toDiag φ₁ φ₂ h₁ h₂) (lift i j)
  have e2 : ((Matrix.of (fun i j => toDiag φ₁ φ₂ h₁ h₂ (lift i j))).map
        (inclDiag φ₁ φ₂ h₁ h₂)).map (projSnd φ₁ φ₂ h₁ h₂)
      = (Matrix.of (fun i j => lift i j)).map φ₂ := by
    ext i j
    exact RingHom.congr_fun (projSnd_toDiag φ₁ φ₂ h₁ h₂) (lift i j)
  rw [hA, e1, e2]
  exact hmat n m (Matrix.of fun i j => lift i j)

end Diagonal

/-! ### The two remaining inputs (being proved in parallel)

The first is the second projection analogue of
`Work.Section3.projFst_surjective_diagClosure` (delegated at
`Submission/Work/Section3/projSnd_surjective_diagClosure.lean`), the second is
[Jaikin, GAFA 2019, Proposition 5.11] / [Li, Theorem 8.1] in the von Neumann regular case
(delegated at `Submission/Work/Section3/rk_eq_of_pullback_eq_of_isEpic_vnRegular.lean`). -/

/-- The body of the uniqueness theorem, with the parameters explicit. -/
theorem envelopeUniqueness_aux {R : Type u} [Ring R] [StarRing R]
    {U₁ : Type u} [Ring U₁] [StarRing U₁] [IsStarRegular U₁]
    {U₂ : Type u} [Ring U₂] [StarRing U₂] [IsStarRegular U₂]
    (φ₁ : R →+* U₁) (φ₂ : R →+* U₂) (rk₁ : SylvesterRank U₁) (rk₂ : SylvesterRank U₂)
    (hc₁ : ∀ x : R, φ₁ (star x) = star (φ₁ x)) (hc₂ : ∀ x : R, φ₂ (star x) = star (φ₂ x))
    (hep₁ : IsEpic φ₁) (hep₂ : IsEpic φ₂) (hf₁ : rk₁.IsFaithful) (hf₂ : rk₂.IsFaithful)
    (hmat : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) R),
      rk₁.rk n m (A.map φ₁) = rk₂.rk n m (A.map φ₂)) :
    ∃ e : U₁ ≃+* U₂, (∀ x : R, e (φ₁ x) = φ₂ x) ∧
      (∀ x : U₁, rk₂.rk 1 1 (oneByOne (e x)) = rk₁.rk 1 1 (oneByOne x)) := by
  haveI hSRprod : IsStarRegular (U₁ × U₂) := Work.Section3.isStarRegular_prod
  haveI hSRT : IsStarRegular ↥(diagClosure φ₁ φ₂ hc₁ hc₂) :=
    StarRegular.starRegularClosure_isStarRegular _
  haveI hVNRT : VonNeumannRegularRing ↥(diagClosure φ₁ φ₂ hc₁ hc₂) := inferInstance
  let ρ₁ : SylvesterRank ↥(diagClosure φ₁ φ₂ hc₁ hc₂) :=
    SylvesterRank.pullback (projFst φ₁ φ₂ hc₁ hc₂) rk₁
  let ρ₂ : SylvesterRank ↥(diagClosure φ₁ φ₂ hc₁ hc₂) :=
    SylvesterRank.pullback (projSnd φ₁ φ₂ hc₁ hc₂) rk₂
  have hΔ : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) ↥(diagStarSubring φ₁ φ₂ hc₁ hc₂).toSubring),
      ρ₁.rk n m (A.map (inclDiag φ₁ φ₂ hc₁ hc₂)) = ρ₂.rk n m (A.map (inclDiag φ₁ φ₂ hc₁ hc₂)) :=
    fun n m A => rank_eq_on_diag φ₁ φ₂ hc₁ hc₂ rk₁ rk₂ hmat n m A
  have hT : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) ↥(diagClosure φ₁ φ₂ hc₁ hc₂)),
      ρ₁.rk n m A = ρ₂.rk n m A :=
    Work.Section3.rk_eq_of_pullback_eq_of_isEpic_vnRegular (inclDiag φ₁ φ₂ hc₁ hc₂)
      (Work.Section3.isEpic_inclusion_diagStarSubring_diagClosure φ₁ φ₂ hc₁ hc₂) ρ₁ ρ₂ hΔ
  have hker : ∀ t : ↥(diagClosure φ₁ φ₂ hc₁ hc₂), projFst φ₁ φ₂ hc₁ hc₂ t = 0 → t = 0 := by
    intro t ht
    have h1 : ρ₁.rk 1 1 (oneByOne t) = 0 := by
      show rk₁.rk 1 1 (oneByOne ((projFst φ₁ φ₂ hc₁ hc₂) t)) = 0
      rw [ht]
      exact rk₁.rk_zero 1 1
    have h2 : ρ₂.rk 1 1 (oneByOne t) = 0 := by rw [← hT 1 1 (oneByOne t)]; exact h1
    have h3 : rk₂.rk 1 1 (oneByOne ((projSnd φ₁ φ₂ hc₁ hc₂) t)) = 0 := h2
    have h4 : projSnd φ₁ φ₂ hc₁ hc₂ t = 0 := hf₂ _ h3
    refine Subtype.ext ?_
    show (t : U₁ × U₂) = 0
    rw [Prod.ext_iff]
    exact ⟨ht, h4⟩
  have hker₂ : ∀ t : ↥(diagClosure φ₁ φ₂ hc₁ hc₂), projSnd φ₁ φ₂ hc₁ hc₂ t = 0 → t = 0 := by
    intro t ht
    have h1 : ρ₂.rk 1 1 (oneByOne t) = 0 := by
      show rk₂.rk 1 1 (oneByOne ((projSnd φ₁ φ₂ hc₁ hc₂) t)) = 0
      rw [ht]
      exact rk₂.rk_zero 1 1
    have h2 : ρ₁.rk 1 1 (oneByOne t) = 0 := by rw [hT 1 1 (oneByOne t)]; exact h1
    have h3 : rk₁.rk 1 1 (oneByOne ((projFst φ₁ φ₂ hc₁ hc₂) t)) = 0 := h2
    have h4 : projFst φ₁ φ₂ hc₁ hc₂ t = 0 := hf₁ _ h3
    refine Subtype.ext ?_
    show (t : U₁ × U₂) = 0
    rw [Prod.ext_iff]
    exact ⟨h4, ht⟩
  have hinj₁ : Function.Injective (projFst φ₁ φ₂ hc₁ hc₂) := by
    intro t s hts
    have h : projFst φ₁ φ₂ hc₁ hc₂ (t - s) = 0 := by rw [map_sub, hts, sub_self]
    exact sub_eq_zero.mp (hker (t - s) h)
  have hinj₂ : Function.Injective (projSnd φ₁ φ₂ hc₁ hc₂) := by
    intro t s hts
    have h : projSnd φ₁ φ₂ hc₁ hc₂ (t - s) = 0 := by rw [map_sub, hts, sub_self]
    exact sub_eq_zero.mp (hker₂ (t - s) h)
  let e₁ : ↥(diagClosure φ₁ φ₂ hc₁ hc₂) ≃+* U₁ :=
    RingEquiv.ofBijective (projFst φ₁ φ₂ hc₁ hc₂)
      ⟨hinj₁, Work.Section3.projFst_surjective_diagClosure φ₁ φ₂ hc₁ hc₂ hep₁⟩
  let e₂ : ↥(diagClosure φ₁ φ₂ hc₁ hc₂) ≃+* U₂ :=
    RingEquiv.ofBijective (projSnd φ₁ φ₂ hc₁ hc₂)
      ⟨hinj₂, Work.Section3.projSnd_surjective_diagClosure φ₁ φ₂ hc₁ hc₂ hep₂⟩
  refine ⟨e₁.symm.trans e₂, ?_, ?_⟩
  · intro r
    have ht : e₁.symm (φ₁ r) = toClosure φ₁ φ₂ hc₁ hc₂ r := by
      apply e₁.injective
      rw [RingEquiv.apply_symm_apply]
      exact projFst_toClosure φ₁ φ₂ hc₁ hc₂ r
    show e₂ (e₁.symm (φ₁ r)) = φ₂ r
    rw [ht]
    exact projSnd_toClosure φ₁ φ₂ hc₁ hc₂ r
  · intro x
    have hx : projFst φ₁ φ₂ hc₁ hc₂ (e₁.symm x) = x := e₁.apply_symm_apply x
    show rk₂.rk 1 1 (oneByOne (e₂ (e₁.symm x))) = rk₁.rk 1 1 (oneByOne x)
    calc rk₂.rk 1 1 (oneByOne (e₂ (e₁.symm x)))
        = ρ₂.rk 1 1 (oneByOne (e₁.symm x)) := rfl
      _ = ρ₁.rk 1 1 (oneByOne (e₁.symm x)) := (hT 1 1 (oneByOne (e₁.symm x))).symm
      _ = rk₁.rk 1 1 (oneByOne (projFst φ₁ φ₂ hc₁ hc₂ (e₁.symm x))) := rfl
      _ = rk₁.rk 1 1 (oneByOne x) := by rw [hx]

theorem envelopeUniqueness_star (R : Type) [Ring R] [StarRing R] :
    Work.ORHughesFree.EpicEnvelopeUnique R := by
  intro U₁ _ _ _ U₂ _ _ _ φ₁ φ₂ rk₁ rk₂ hc₁ hc₂ hep₁ hep₂ hf₁ hf₂ hmat
  exact envelopeUniqueness_aux φ₁ φ₂ rk₁ rk₂ hc₁ hc₂ hep₁ hep₂ hf₁ hf₂ hmat

end Work.ORHughesFree.Section3
