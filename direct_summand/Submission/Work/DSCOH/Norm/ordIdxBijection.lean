import Mathlib
import Submission.Work.DSCOH.Norm.Defs

namespace Work.DSCOH.Norm

/-!
## The bijection between strictly increasing tuples and subsets of a fixed cardinality

`OrdIdx ι n` is the type of strictly increasing `(n+1)`-tuples in the linear order `ι`; a
strictly increasing tuple is the same thing as an enumeration of a subset of `ι` of cardinality
`n+1`.  This file makes that bijection explicit, and records its compatibility with
`Finset.orderEmbOfFin`, with deletion of an entry, and with counting the entries below a given
one.  These are the bookkeeping facts used to identify the "ordered" Čech complex with the
subset-indexed alternating one.
-/

/-- The subset underlying a strictly increasing tuple: its set of values. -/
noncomputable def ordIdxToFinset {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (n : ℕ) (x : OrdIdx ι n) : {S : Finset ι // S.card = n + 1} :=
  ⟨Finset.univ.image x.val, by
    rw [Finset.card_image_of_injective _ x.property.injective, Finset.card_univ,
      Fintype.card_fin]⟩

/-- The strictly increasing `(n+1)`-tuple enumerating a subset of cardinality `n+1`. -/
noncomputable def finsetToOrdIdx {ι : Type*} [DecidableEq ι] [LinearOrder ι]
    (n : ℕ) (S : {S : Finset ι // S.card = n + 1}) : OrdIdx ι n :=
  ⟨S.1.orderEmbOfFin S.2, (S.1.orderEmbOfFin S.2).strictMono⟩

/-- `Finset.image_orderEmbOfFin_univ` with an explicit `DecidableEq` instance, so that it can be
matched against the instance chosen by the surrounding context. -/
lemma image_orderEmbOfFin_univ' {α : Type*} [DecidableEq α] [LinearOrder α]
    (s : Finset α) {k : ℕ} (h : s.card = k) :
    Finset.image (⇑(s.orderEmbOfFin h)) Finset.univ = s := by
  apply Finset.coe_injective
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  exact s.range_orderEmbOfFin h

/-- The increasing enumeration of the value set of a strictly increasing tuple is the tuple
itself. -/
lemma orderEmbOfFin_image_univ_self {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {n : ℕ} (x : Fin (n + 1) → ι) (hx : StrictMono x)
    {h : (Finset.univ.image x).card = n + 1} :
    (Finset.univ.image x).orderEmbOfFin h = x := by
  exact (Finset.orderEmbOfFin_unique h
    (fun i => Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩) hx).symm

/-- Deleting the `b`-th entry of a tuple amounts, on the level of value sets, to removing the
deleted value. -/
lemma image_comp_succAbove_erase {α : Type*} [DecidableEq α] {n : ℕ}
    (f : Fin (n + 2) → α) (hf : Function.Injective f) (b : Fin (n + 2)) :
    (Finset.univ.image (fun a : Fin (n + 1) => f (b.succAbove a)))
      = (Finset.univ.image f).erase (f b) := by
  rw [show (fun a : Fin (n + 1) => f (b.succAbove a)) = f ∘ b.succAbove from rfl,
      Finset.image_comp]
  rw [show Finset.image b.succAbove Finset.univ
        = (Finset.univ : Finset (Fin (n + 2))).erase b from ?_]
  · rw [Finset.image_erase hf]
  · ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    exact Fin.exists_succAbove_eq_iff

/-- For a strictly increasing tuple, the number of its values below the `b`-th one is `b`. -/
lemma card_filter_lt_strictMono {ι : Type*} [DecidableEq ι] [LinearOrder ι] {n : ℕ}
    (x : Fin (n + 2) → ι) (hx : StrictMono x) (b : Fin (n + 2)) :
    ((Finset.univ.image x).filter (fun j => j < x b)).card = (b : ℕ) := by
  rw [Finset.filter_image, Finset.card_image_of_injective _ hx.injective]
  have heq : (Finset.univ.filter (fun i : Fin (n + 2) => x i < x b))
      = (Finset.univ.filter (fun i : Fin (n + 2) => i < b)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hx.lt_iff_lt
  rw [heq, show (Finset.univ.filter (fun i : Fin (n + 2) => i < b)) = Finset.Iio b from by
        ext i; simp, Fin.card_Iio]

theorem ordIdxBijection {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] :
    ∃ (Φ : ∀ n : ℕ, Work.DSCOH.Norm.OrdIdx ι n → {S : Finset ι // S.card = n + 1})
      (Ψ : ∀ n : ℕ, {S : Finset ι // S.card = n + 1} → Work.DSCOH.Norm.OrdIdx ι n),
      (∀ (n : ℕ) (S : {S : Finset ι // S.card = n + 1}), Φ n (Ψ n S) = S) ∧
      (∀ (n : ℕ) (x : Work.DSCOH.Norm.OrdIdx ι n), Ψ n (Φ n x) = x) ∧
      (∀ (n : ℕ) (x : Work.DSCOH.Norm.OrdIdx ι n), (Φ n x).1 = Finset.univ.image x.val) ∧
      (∀ (n : ℕ) (S : {S : Finset ι // S.card = n + 1}),
        (Ψ n S).val = S.1.orderEmbOfFin S.2) ∧
      (∀ (n : ℕ) (x : Work.DSCOH.Norm.OrdIdx ι (n+1)) (b : Fin (n+2)),
        (Φ n ⟨Work.DSCOH.Norm.del x.val b,
            Work.DSCOH.Norm.strictMono_del x.val b x.property⟩).1
          = (Φ (n+1) x).1.erase (x.val b)) ∧
      (∀ (n : ℕ) (x : Work.DSCOH.Norm.OrdIdx ι (n+1)) (b : Fin (n+2)),
        (((Φ (n+1) x).1.filter (fun j => j < x.val b))).card = (b : ℕ)) := by
  classical
  refine ⟨ordIdxToFinset, finsetToOrdIdx, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n S
    apply Subtype.ext
    simp only [ordIdxToFinset, finsetToOrdIdx, Subtype.coe_mk]
    exact image_orderEmbOfFin_univ' S.1 S.2
  · intro n x
    apply Subtype.ext
    simp only [ordIdxToFinset, finsetToOrdIdx, Subtype.coe_mk]
    exact orderEmbOfFin_image_univ_self x.val x.property
  · intro n x
    simp only [ordIdxToFinset, Subtype.coe_mk]
  · intro n S
    simp only [finsetToOrdIdx, Subtype.coe_mk]
  · intro n x b
    simp only [ordIdxToFinset, Subtype.coe_mk]
    exact image_comp_succAbove_erase x.val x.property.injective b
  · intro n x b
    simp only [ordIdxToFinset, Subtype.coe_mk]
    exact card_filter_lt_strictMono x.val x.property b

end Work.DSCOH.Norm
