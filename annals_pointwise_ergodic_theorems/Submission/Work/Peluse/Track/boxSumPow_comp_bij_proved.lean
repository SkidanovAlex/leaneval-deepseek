import Mathlib
import Submission.Work.Peluse.BoxNorm.boxSumPow_eq_boxNormPow

/-!
# The box-sum power is invariant under a permutation of the directions

Peluse's box norm `‖f‖_{□^t_{Q₁,…,Q_t}(S)}` (Definition 2.1 of S. Peluse, *Bounds for sets with no
polynomial progressions*, Forum of Math. Pi **8** (2020), e16) is a *symmetric* function of the
family of direction sets `Q₁, …, Q_t`: the defining average over the `2t` shifts `h_i, h_i' ∈ Q_i`
only refers to the index `i` through the pairing of `Q_i` with the `i`-th coordinate of the
`x`-shift.  Consequently a permutation `σ` of the index set `Fin t` leaves the `2^t`-th power
`boxSumPow` unchanged:

`boxSumPow t (fun i => Q (σ i)) S f = boxSumPow t Q S f`.

This is the statement of `Work.Peluse.Track.boxSumPow_comp_bij_proved`.  The proof goes through
the factorisation `boxSumPow t Q S f = boxScaling t Q S * rawSum t Q f`
(`Work.Peluse.BoxNorm.boxSumPow_eq_scaling`), the invariance of the (purely multiplicative)
scaling constant, and the reindexing of the double sum over the shift tuples

`∑_{h ∈ ∏_i {x // x ∈ Q_i}} ∑_{h' ∈ ∏_i {x // x ∈ Q_i}} (cube term)`,

which is performed with the equivalence
`(Equiv.piCongrLeft (fun i => {x // x ∈ Q i}) σ).symm`.

The combinatorial input is that the cube term only depends on the *values* of `h`, `h'` and on the
*set* of positions `ω` at which the conjugation `C^{|ω|}` is applied; both are permuted by `σ`,
which is what `weight_comp_equiv` and `cornerShift_comp_equiv` record.

## Reference

S. Peluse, *Bounds for sets with no polynomial progressions*, Definition 2.1.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.Track

open Finset

noncomputable section

/-- The `x`-sum of the cube term, as a function of the two shift tuples: the inner factor of
`Work.Peluse.BoxNorm.rawSum`. -/
def cubeTSum {t : ℕ} (Q : Fin t → Finset ℤ) (f : ℤ → ℂ)
    (h h' : (i : Fin t) → {x : ℤ // x ∈ Q i}) : ℂ :=
  ∑' x : ℤ, ∏ ω : Fin t → Bool,
    (star^[Work.Peluse.weight ω])
      (f (x + Work.Peluse.cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω))

/-- `rawSum` is the double sum over the shift tuples of the cube term `cubeTSum`. -/
lemma rawSum_eq_sum_cubeTSum {t : ℕ} (Q : Fin t → Finset ℤ) (f : ℤ → ℂ) :
    Work.Peluse.BoxNorm.rawSum t Q f
      = ∑ h : (i : Fin t) → {x : ℤ // x ∈ Q i},
        ∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q i}, cubeTSum Q f h h' := rfl

/-- The number of `1`'s in `ω : Fin t → Bool` is unchanged by precomposing with a bijection. -/
lemma weight_comp_equiv {t : ℕ} (e : Fin t ≃ Fin t) (ω : Fin t → Bool) :
    Work.Peluse.weight (fun i => ω (e i)) = Work.Peluse.weight ω := by
  have himg : (Finset.univ.filter (fun i : Fin t => ω (e i)))
      = (Finset.univ.filter (fun i : Fin t => ω i)).image e.symm := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      exact ⟨e i, h, e.symm_apply_apply i⟩
    · rintro ⟨a, ha, rfl⟩
      simpa using ha
  rw [Work.Peluse.weight, Work.Peluse.weight, himg,
    Finset.card_image_of_injective _ e.symm.injective]

/-- The corner shift `ω · h + (1 - ω) · h'` only depends on the values of `h`, `h'` and on the set
of positions `ω` is `true` at: precomposing `h`, `h'` with a bijection `e` and `ω` with `e.symm`
leaves it unchanged. -/
lemma cornerShift_comp_equiv {t : ℕ} (e : Fin t ≃ Fin t) (α β : Fin t → ℤ)
    (ω : Fin t → Bool) :
    Work.Peluse.cornerShift α β (fun i => ω (e.symm i))
      = Work.Peluse.cornerShift (fun i => α (e i)) (fun i => β (e i)) ω := by
  simp only [Work.Peluse.cornerShift]
  rw [← Equiv.sum_comp e (fun i => if ω (e.symm i) then α i else β i)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [Equiv.symm_apply_apply]

/-- The value of `Equiv.piCongrLeft`'s inverse on the underlying integers. -/
lemma piCongrLeft_symm_val {t : ℕ} (Q : Fin t → Finset ℤ) (e : Fin t ≃ Fin t)
    (g : (i : Fin t) → {x : ℤ // x ∈ Q i}) (a : Fin t) :
    (((Equiv.piCongrLeft (fun i => {x : ℤ // x ∈ Q i}) e).symm g) a).1 = (g (e a)).1 := by
  refine congrArg Subtype.val ?_
  have h := Equiv.piCongrLeft_apply_apply (fun i => {x : ℤ // x ∈ Q i}) e
    ((Equiv.piCongrLeft (fun i => {x : ℤ // x ∈ Q i}) e).symm g) a
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-- The product of the conjugated cube terms is unchanged when the shift values are precomposed
with a bijection `e` of the index set (the product is reindexed by `ω ↦ ω ∘ e.symm`). -/
lemma prod_cubeTerm_comp {t : ℕ} (e : Fin t ≃ Fin t) (f : ℤ → ℂ) (α β : Fin t → ℤ) (x : ℤ) :
    (∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
        (f (x + Work.Peluse.cornerShift (fun i => α (e i)) (fun i => β (e i)) ω)))
      = ∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
        (f (x + Work.Peluse.cornerShift α β ω)) := by
  conv_rhs => rw [← Equiv.prod_comp (Equiv.arrowCongr e (Equiv.refl Bool))
    (fun ω => (star^[Work.Peluse.weight ω]) (f (x + Work.Peluse.cornerShift α β ω)))]
  refine Finset.prod_congr rfl (fun ω _ => ?_)
  have hW : (Equiv.arrowCongr e (Equiv.refl Bool)) ω = (fun i => ω (e.symm i)) := by
    funext i
    simp [Equiv.arrowCongr_apply]
  have h1 : Work.Peluse.weight ((Equiv.arrowCongr e (Equiv.refl Bool)) ω)
      = Work.Peluse.weight ω := by
    rw [hW]
    exact weight_comp_equiv e.symm ω
  have h2 : Work.Peluse.cornerShift α β ((Equiv.arrowCongr e (Equiv.refl Bool)) ω)
      = Work.Peluse.cornerShift (fun i => α (e i)) (fun i => β (e i)) ω := by
    rw [hW]
    exact cornerShift_comp_equiv e α β ω
  rw [h1, h2]

/-- The cube term is unchanged by the reindexing of the shift tuples along a bijection. -/
lemma cubeTSum_bij_aux {t : ℕ} (Q : Fin t → Finset ℤ) (f : ℤ → ℂ) (e : Fin t ≃ Fin t)
    (g g' : (i : Fin t) → {x : ℤ // x ∈ Q i}) :
    cubeTSum (fun i => Q (e i)) f
        ((Equiv.piCongrLeft (fun i => {x : ℤ // x ∈ Q i}) e).symm g)
        ((Equiv.piCongrLeft (fun i => {x : ℤ // x ∈ Q i}) e).symm g')
      = cubeTSum Q f g g' := by
  rw [cubeTSum, cubeTSum]
  refine tsum_congr (fun x => ?_)
  rw [show (fun i => (((Equiv.piCongrLeft (fun i => {x : ℤ // x ∈ Q i}) e).symm g) i).1)
        = (fun i => (g (e i)).1) from funext (fun i => piCongrLeft_symm_val Q e g i),
    show (fun i => (((Equiv.piCongrLeft (fun i => {x : ℤ // x ∈ Q i}) e).symm g') i).1)
        = (fun i => (g' (e i)).1) from funext (fun i => piCongrLeft_symm_val Q e g' i)]
  exact prod_cubeTerm_comp e f (fun i => (g i).1) (fun i => (g' i).1) x

/-- The normalising constant `boxScaling` is invariant under a permutation of the directions. -/
lemma boxScaling_comp_equiv {t : ℕ} (e : Fin t ≃ Fin t) (Q : Fin t → Finset ℤ) (S : Finset ℤ) :
    Work.Peluse.BoxNorm.boxScaling t (fun i => Q (e i)) S
      = Work.Peluse.BoxNorm.boxScaling t Q S := by
  simp only [Work.Peluse.BoxNorm.boxScaling,
    Equiv.prod_comp e (fun i => (((Q i).card : ℝ))⁻¹)]

/-- The raw box sum is invariant under a permutation of the directions. -/
lemma rawSum_comp_equiv {t : ℕ} (e : Fin t ≃ Fin t) (Q : Fin t → Finset ℤ) (f : ℤ → ℂ) :
    Work.Peluse.BoxNorm.rawSum t (fun i => Q (e i)) f
      = Work.Peluse.BoxNorm.rawSum t Q f := by
  rw [rawSum_eq_sum_cubeTSum (fun i => Q (e i)) f, rawSum_eq_sum_cubeTSum Q f]
  rw [← Equiv.sum_comp ((Equiv.piCongrLeft (fun i => {x : ℤ // x ∈ Q i}) e).symm)
    (fun k => ∑ k' : (i : Fin t) → {x : ℤ // x ∈ Q (e i)},
      cubeTSum (fun i => Q (e i)) f k k')]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [← Equiv.sum_comp ((Equiv.piCongrLeft (fun i => {x : ℤ // x ∈ Q i}) e).symm)
    (fun k' => cubeTSum (fun i => Q (e i)) f
      ((Equiv.piCongrLeft (fun i => {x : ℤ // x ∈ Q i}) e).symm h) k')]
  exact Finset.sum_congr rfl (fun h' _ => cubeTSum_bij_aux Q f e h h')

theorem boxSumPow_comp_bij_proved {t : ℕ} (Q : Fin t → Finset ℤ) (S : Finset ℤ) (f : ℤ → ℂ)
    (σ : Fin t → Fin t) (hσ : Function.Bijective σ) :
    Work.Peluse.boxSumPow t (fun i => Q (σ i)) S f = Work.Peluse.boxSumPow t Q S f := by
  set e : Fin t ≃ Fin t := Equiv.ofBijective σ hσ with he
  have hQ : (fun i => Q (σ i)) = (fun i => Q (e i)) := by
    rw [he, Equiv.coe_ofBijective]
  rw [hQ, Work.Peluse.BoxNorm.boxSumPow_eq_scaling, Work.Peluse.BoxNorm.boxSumPow_eq_scaling,
    boxScaling_comp_equiv e Q S, rawSum_comp_equiv e Q f]

end

end Work.Peluse.Track
