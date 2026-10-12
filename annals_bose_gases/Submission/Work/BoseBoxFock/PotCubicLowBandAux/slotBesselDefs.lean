import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.XSpow_slotExact_compl_vanish
import Submission.Work.BoseBoxFock.slotPairDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PotCubicLowBandAux.slotBesselDefs` — the slicing vocabulary

The target of this auxiliary chapter (`slotBesselExcited`) is the **Bessel/frame bound in slot
form**: for an orthonormal family `e : Fin m → Sp → ℂ` supported in the box `boxL ℓ`, a family of
rank-one one-body operators `|f_k⟩⟨f_k|` whose frame constant is `C` and whose vectors are
orthogonal to the condensate mode (`f_k 0 = 0`), the box slot sum of `Σ_k |f_k⟩⟨f_k|` is dominated
by `C` times the slot sum of the excited-number operator `boxT0 m = 1 − |e_0⟩⟨e_0|`:

    ∫_{abox} ⟪Θ, boxSlotSum e (Σ_k|f_k⟩⟨f_k|) Θ⟫ ≤ C · ∫_{abox} ⟪Θ, boxSlotSum e boxT0 Θ⟫ .

Every slot operator `boxSlotOf e w v j` acts only on the `j`-th coordinate of the configuration,
so the proof of the target is *slot by slot*: at a fixed configuration of the remaining `n − 1`
coordinates, the `j`-th slot becomes a one-particle (finite-dimensional) inequality.  This module
supplies the vocabulary of that slicing:

* `sliceRestore j a ŷ` — the configuration of `n` coordinates that has `a` in slot `j` and `ŷ`
  (`ŷ : {i // i ≠ j} → Sp`) in all the other slots;
* the elementary lemmas that turn `sliceRestore` into `Function.update`
  (`update_sliceRestore`, `sliceRestore_self`), which is the form in which `boxSlotOf` is written.

The consumer of this vocabulary is the *slice/Fubini* reduction `integral_sliceRestore`: for an
integrable `F` on `Xn n`,

      ∫ x, F x = ∫ ŷ, ∫ a, F (sliceRestore j a ŷ) ;

its proof combines the measure preserving equivalence `MeasurableEquiv.piEquivPiSubtypeProd`
(which separates the coordinate `j` from the others), the collapse of the (unique) coordinate `j`
(`MeasurableEquiv.funUnique`) and the product Fubini theorem.

Everything here is `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock.PotCubicLowBandAux

set_option autoImplicit false

/-- The box `Λ(ℓ)` of the corpus, in coordinate form: `x ∈ boxL ℓ ↔ ∀ i, |x i| ≤ ℓ/2`
(`Work.BoseBoxFock.mem_corpusBox_boxL`). -/
abbrev bl (ℓ : ℝ) : Set (Work.BoseDict.Sp) := Work.BoseK15.corpusBox.boxL ℓ

/-- **The slice of a configuration**: the configuration of `n` coordinates which has `a` in
the slot `j` and `ŷ` in all the other slots. -/
def sliceRestore {n : ℕ} (j : Fin n) (a : Work.BoseDict.Sp)
    (ŷ : {i : Fin n // i ≠ j} → Work.BoseDict.Sp) : Work.BoseDict.Xn n :=
  fun i => if h : i = j then a else ŷ ⟨i, h⟩

@[simp]
theorem sliceRestore_apply_self {n : ℕ} (j : Fin n) (a : Work.BoseDict.Sp)
    (ŷ : {i : Fin n // i ≠ j} → Work.BoseDict.Sp) : sliceRestore j a ŷ j = a := by
  simp [sliceRestore]

theorem sliceRestore_apply_of_ne {n : ℕ} {i j : Fin n} (h : i ≠ j) (a : Work.BoseDict.Sp)
    (ŷ : {i : Fin n // i ≠ j} → Work.BoseDict.Sp) :
    sliceRestore j a ŷ i = ŷ ⟨i, h⟩ := by
  simp [sliceRestore, h]

/-- **The key compatibility with `Function.update`**: overwriting the `j`-th coordinate of
`sliceRestore j a ŷ` by `z` is `sliceRestore j z ŷ`. -/
@[simp]
theorem update_sliceRestore {n : ℕ} (j : Fin n) (a z : Work.BoseDict.Sp)
    (ŷ : {i : Fin n // i ≠ j} → Work.BoseDict.Sp) :
    Function.update (sliceRestore j a ŷ) j z = sliceRestore j z ŷ := by
  funext i
  by_cases h : i = j
  · subst h
    simp [sliceRestore]
  · rw [Function.update_of_ne h, sliceRestore_apply_of_ne h, sliceRestore_apply_of_ne h]

/-- **Reassembly**: every configuration is the slice with its own `j`-th coordinate in slot `j`. -/
@[simp]
theorem sliceRestore_self {n : ℕ} (j : Fin n) (x : Work.BoseDict.Xn n) :
    sliceRestore j (x j) (fun i : {i : Fin n // i ≠ j} => x i.1) = x := by
  funext i
  by_cases h : i = j
  · subst h
    simp [sliceRestore]
  · simp [sliceRestore, h]

/-- The `j`-th coordinate of `sliceRestore j a ŷ` is `a`: the "other" coordinates of the slice
are those of `ŷ`. -/
theorem sliceRestore_apply_ne_sliceRestore {n : ℕ} {i j : Fin n} (h : i ≠ j)
    (a b : Work.BoseDict.Sp) (ŷ : {i : Fin n // i ≠ j} → Work.BoseDict.Sp) :
    sliceRestore j a ŷ i = sliceRestore j b ŷ i := by
  rw [sliceRestore_apply_of_ne h, sliceRestore_apply_of_ne h]

/-! ## The single-slot form of the first-quantised sum

`Work.BoseDict.boxSlotSum e T Θ = Σ_j Σ_l Σ_{l'} (T e_{l'})_l • boxSlotOf e e_l e_{l'} j Θ` is a
sum over the slots `j` of the configuration, and a single summand is a *one-particle* expression
in the coordinate `x j`:

    (slotJ e T j Θ) x = Σ_l Σ_{l'} (T e_{l'})_l · e_l(x j) · ∫ z, conj(e_{l'} z) Θ(x[j ↦ z]) .

This is the form in which the Fubini/slice reduction is applied: after fixing the remaining
coordinates `ŷ`, the slot `j` becomes a one-particle (finite-dimensional) quadratic form in the
vector `U_l = ∫ z, conj(e_l z) Θ(σ z ŷ)`. -/

/-- **The `j`-th slot** of the first-quantised sum of the one-body operator `T`. -/
noncomputable def slotJ {m n : ℕ} (e : Fin m → Work.BoseDict.Sp → ℂ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (j : Fin n) (Θ : Work.BoseDict.Xn n → ℂ) :
    Work.BoseDict.Xn n → ℂ :=
  fun x => ∑ l : Fin m, ∑ l' : Fin m,
    ((T (Work.BoseB4.evec m l')) l : ℂ)
      * (e l (x j) * ∫ z : Work.BoseDict.Sp, star (e l' z) * Θ (Function.update x j z))

/-- The defining value of `slotJ`. -/
theorem slotJ_apply {m n : ℕ} (e : Fin m → Work.BoseDict.Sp → ℂ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (j : Fin n) (Θ : Work.BoseDict.Xn n → ℂ)
    (x : Work.BoseDict.Xn n) :
    slotJ e T j Θ x = ∑ l : Fin m, ∑ l' : Fin m,
      ((T (Work.BoseB4.evec m l')) l : ℂ)
        * (e l (x j) * ∫ z : Work.BoseDict.Sp, star (e l' z) * Θ (Function.update x j z)) :=
  rfl

/-- **The slot decomposition of the first-quantised sum.** -/
theorem boxSlotSum_eq_sum_slotJ {m n : ℕ} (e : Fin m → Work.BoseDict.Sp → ℂ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (Θ : Work.BoseDict.Xn n → ℂ) :
    Work.BoseDict.boxSlotSum e T Θ = ∑ j : Fin n, slotJ e T j Θ := by
  funext x
  simp only [slotJ, Work.BoseDict.boxSlotSum, Work.BoseDict.boxSlotOf, Finset.sum_apply,
    Pi.smul_apply, Work.BoseB4.evec, Work.BoseDict.etaOf_pi_single, Complex.real_smul,
    smul_eq_mul, starRingEnd_apply]

/-- `slotJ` is additive in the one-body operator. -/
theorem slotJ_add {m n : ℕ} (e : Fin m → Work.BoseDict.Sp → ℂ)
    (T T' : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (j : Fin n) (Θ : Work.BoseDict.Xn n → ℂ) :
    slotJ e (T + T') j Θ = slotJ e T j Θ + slotJ e T' j Θ := by
  funext x
  simp only [slotJ, LinearMap.add_apply, Pi.add_apply, Complex.ofReal_add, add_mul,
    Finset.sum_add_distrib, Pi.add_apply]

/-- `slotJ` is additive in the one-body operator (difference form). -/
theorem slotJ_sub {m n : ℕ} (e : Fin m → Work.BoseDict.Sp → ℂ)
    (T T' : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (j : Fin n) (Θ : Work.BoseDict.Xn n → ℂ) :
    slotJ e (T - T') j Θ = slotJ e T j Θ - slotJ e T' j Θ := by
  funext x
  simp only [slotJ, LinearMap.sub_apply, Pi.sub_apply, Complex.ofReal_sub, sub_mul,
    Finset.sum_sub_distrib, Pi.sub_apply]

/-- `slotJ` of the zero one-body operator vanishes. -/
theorem slotJ_zero {m n : ℕ} (e : Fin m → Work.BoseDict.Sp → ℂ) (j : Fin n)
    (Θ : Work.BoseDict.Xn n → ℂ) :
    slotJ e (0 : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) j Θ = 0 := by
  funext x
  simp only [slotJ, LinearMap.zero_apply, Complex.ofReal_zero, zero_mul, Finset.sum_const_zero,
    Pi.zero_apply]

/-- `slotJ` is additive over a finite sum of one-body operators. -/
theorem slotJ_finset_sum {m n : ℕ} {ι : Type*} (e : Fin m → Work.BoseDict.Sp → ℂ)
    (s : Finset ι) (T : ι → (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (j : Fin n)
    (Θ : Work.BoseDict.Xn n → ℂ) :
    slotJ e (∑ k ∈ s, T k) j Θ = ∑ k ∈ s, slotJ e (T k) j Θ := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, slotJ_zero]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, slotJ_add, ih]

/-- The slot of the identity one-body operator. -/
theorem slotJ_one {m n : ℕ} (e : Fin m → Work.BoseDict.Sp → ℂ) (j : Fin n)
    (Θ : Work.BoseDict.Xn n → ℂ) :
    slotJ e (1 : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) j Θ
      = fun x => ∑ l : Fin m,
          (e l (x j) * ∫ z : Work.BoseDict.Sp, star (e l z) * Θ (Function.update x j z)) := by
  funext x
  rw [slotJ_apply]
  have hcoef : ∀ l l' : Fin m,
      (1 : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (Work.BoseB4.evec m l') l
        = (if l = l' then (1 : ℝ) else 0) := by
    intro l l'
    rw [Module.End.one_apply, Work.BoseB4.evec, Pi.single_apply]
  simp only [hcoef]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single l]
  · rw [if_pos rfl]
    simp
  · intro b _ hb
    rw [if_neg (Ne.symm hb)]
    simp
  · intro h
    exact absurd (Finset.mem_univ l) h

/-- The matrix elements of a rank-one operator at the coordinate vectors. -/
theorem rankOnePair_evec {m : ℕ} (w v : Fin m → ℝ) (l l' : Fin m) :
    Work.BoseBoxFock.rankOnePair w v (Work.BoseB4.evec m l') l = w l * v l' := by
  rw [Work.BoseBoxFock.rankOnePair_apply]
  have hsum : (∑ l : Fin m, v l * (Work.BoseB4.evec m l') l) = v l' := by
    rw [Finset.sum_eq_single l']
    · change v l' * (Work.BoseB4.evec m l') l' = v l'
      rw [Work.BoseB4.evec, Pi.single_eq_same, mul_one]
    · intro b _ hb
      have h0 : (Work.BoseB4.evec m l') b = 0 := by
        simp only [Work.BoseB4.evec, Pi.single_apply]
        rw [if_neg hb]
      rw [h0, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ l') h
  rw [Pi.smul_apply, hsum, smul_eq_mul]
  ring

/-- **The rank-one slot factorises**: the slot of `|w⟩⟨v|` is the product of the two
one-particle sums `Σ_l w_l e_l(x j)` and `Σ_{l'} v_{l'} ∫ z, conj(e_{l'} z) Θ(x[j ↦ z])`. -/
theorem slotJ_rankOnePair {m n : ℕ} (e : Fin m → Work.BoseDict.Sp → ℂ) (w v : Fin m → ℝ)
    (j : Fin n) (Θ : Work.BoseDict.Xn n → ℂ) :
    slotJ e (Work.BoseBoxFock.rankOnePair w v) j Θ
      = fun x => (∑ l : Fin m, ((w l : ℝ) : ℂ) * e l (x j))
          * (∑ l' : Fin m, ((v l' : ℝ) : ℂ)
              * ∫ z : Work.BoseDict.Sp, star (e l' z) * Θ (Function.update x j z)) := by
  funext x
  simp only [slotJ]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
  rw [rankOnePair_evec, Complex.ofReal_mul]
  ring

/-- The slot of the condensate projector `|e_0⟩⟨e_0|` (the mode `e_0 = 1 · e_0`). -/
theorem slotJ_rankOne_evec_zero {m n : ℕ} [NeZero m] (e : Fin m → Work.BoseDict.Sp → ℂ)
    (j : Fin n) (Θ : Work.BoseDict.Xn n → ℂ) :
    slotJ e (Work.BoseBoxFock.rankOnePair (Work.BoseB4.evec m 0) (Work.BoseB4.evec m 0)) j Θ
      = fun x => e 0 (x j) * ∫ z : Work.BoseDict.Sp,
          star (e 0 z) * Θ (Function.update x j z) := by
  funext x
  rw [slotJ_rankOnePair]
  have h1 : (∑ l : Fin m, (((Work.BoseB4.evec m 0) l : ℝ) : ℂ) * e l (x j)) = e 0 (x j) := by
    rw [Finset.sum_eq_single (0 : Fin m)]
    · rw [Work.BoseB4.evec, Pi.single_eq_same]
      simp
    · intro b _ hb
      have h0 : (Work.BoseB4.evec m 0) b = 0 := by
        simp only [Work.BoseB4.evec, Pi.single_apply]
        rw [if_neg hb]
      rw [h0]
      simp
    · intro h
      exact absurd (Finset.mem_univ (0 : Fin m)) h
  have h2 : (∑ l : Fin m, (((Work.BoseB4.evec m 0) l : ℝ) : ℂ)
      * ∫ z : Work.BoseDict.Sp, star (e l z) * Θ (Function.update x j z))
      = ∫ z : Work.BoseDict.Sp, star (e 0 z) * Θ (Function.update x j z) := by
    rw [Finset.sum_eq_single (0 : Fin m)]
    · rw [Work.BoseB4.evec, Pi.single_eq_same]
      simp
    · intro b _ hb
      have h0 : (Work.BoseB4.evec m 0) b = 0 := by
        simp only [Work.BoseB4.evec, Pi.single_apply]
        rw [if_neg hb]
      rw [h0]
      simp
    · intro h
      exact absurd (Finset.mem_univ (0 : Fin m)) h
  simp only [h1, h2]

/-- **The slot of the excited-number operator** `boxT0 m = 1 − |e_0⟩⟨e_0|`: only the modes
`l ≠ 0` contribute. -/
theorem slotJ_boxT0 {m n : ℕ} [NeZero m] (e : Fin m → Work.BoseDict.Sp → ℂ) (j : Fin n)
    (Θ : Work.BoseDict.Xn n → ℂ) :
    slotJ e (Work.BoseBoxFock.boxT0 m) j Θ
      = fun x => ∑ l ∈ (Finset.univ.erase (0 : Fin m)),
          (e l (x j) * ∫ z : Work.BoseDict.Sp, star (e l z) * Θ (Function.update x j z)) := by
  have hbox : Work.BoseBoxFock.boxT0 m
      = (1 : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))
        - Work.BoseBoxFock.rankOnePair (Work.BoseB4.evec m 0) (Work.BoseB4.evec m 0) := by
    apply LinearMap.ext
    intro x
    funext i
    have hsum : (∑ l : Fin m, (Work.BoseB4.evec m 0) l * x l) = x 0 := by
      rw [Finset.sum_eq_single (0 : Fin m)]
      · rw [Work.BoseB4.evec, Pi.single_eq_same, one_mul]
      · intro b _ hb
        have h0 : (Work.BoseB4.evec m 0) b = 0 := by
          simp only [Work.BoseB4.evec, Pi.single_apply]
          rw [if_neg hb]
        rw [h0, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ (0 : Fin m)) h
    simp only [Work.BoseBoxFock.boxT0_apply, LinearMap.sub_apply, Pi.sub_apply,
      Module.End.one_apply, Work.BoseBoxFock.rankOnePair_apply, Pi.smul_apply, smul_eq_mul,
      hsum]
  funext x
  rw [hbox, slotJ_sub]
  simp only [Pi.sub_apply, slotJ_one, slotJ_rankOne_evec_zero]
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ (0 : Fin m))]

end Work.BoseBoxFock.PotCubicLowBandAux
