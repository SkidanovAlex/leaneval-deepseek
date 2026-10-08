import Mathlib
import Submission.Work.A7REC.Char.DegSqDeps

/-!
# Degree-6 irreducible characters lie in a full nontrivial degree range

The Burnside degree-sum identity `∑_{χ ∈ Irr G} χ(1)² = |G|` (available in the workspace as
`OddOrder.RepresentationTheory.sumIrreducibleDegreeSq`) says that the *whole* set of irreducible
characters exhausts the group order in squared degrees.  Consequently, if a set of pairwise
distinct nontrivial irreducible characters already realises the whole nontrivial degree budget
`|G| - 1 = 2519` (encoded here as `1 + ∑ i, (f i)² = 2520`), then that set must be *all* of them.

Since an irreducible character of degree `6` is nontrivial, it then has to occur in the range.

The proof route is:

* package the degree of an irreducible character as a positive natural number `auxIrrDegNat`
  (`irreducibleCharacter_apply_one_eq_pos_natCast`), with squared degrees summing to `Nat.card G`;
* a finite-set pigeonhole: a subset all of whose weights are `≥ 1` and whose weight sum equals
  the total must be everything (`aux_eq_univ_of_sum_eq_of_one_le`);
* apply it to `{trivial} ∪ range ι`; the degree-6 character is in the insert and is not trivial,
  hence lies in the range.
-/

namespace Work.A7REC.Char

open OddOrder.RepresentationTheory

/-- A finite set all of whose `g`-weights are `≥ 1` and whose weight sum equals the total
weight must be the whole type. -/
private theorem aux_eq_univ_of_sum_eq_of_one_le {α : Type*} [Fintype α] [DecidableEq α]
    (g : α → ℕ) (hg : ∀ x, 1 ≤ g x) (s : Finset α)
    (hs : ∑ x ∈ s, g x = ∑ x, g x) : s = Finset.univ := by
  have hsd := Finset.sum_sdiff (Finset.subset_univ s) (f := g)
  rw [hs] at hsd
  have hzero : ∑ x ∈ Finset.univ \ s, g x = 0 := by omega
  have hsub : Finset.univ ⊆ s := by
    intro x _
    by_contra hx
    have hxmem : x ∈ Finset.univ \ s := Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩
    have h0 : g x = 0 := (Finset.sum_eq_zero_iff.mp hzero) x hxmem
    have hgx := hg x
    clear hsd hs hzero
    omega
  exact Finset.Subset.antisymm (Finset.subset_univ s) hsub

/-- The degree of an irreducible character, as a natural number. -/
private noncomputable def auxIrrDegNat {G : Type*} [Group G]
    (χ : IrreducibleCharacter G) : ℕ :=
  (irreducibleCharacter_apply_one_eq_pos_natCast χ).choose

private theorem auxIrrDegNat_pos {G : Type*} [Group G] (χ : IrreducibleCharacter G) :
    0 < auxIrrDegNat χ :=
  (irreducibleCharacter_apply_one_eq_pos_natCast χ).choose_spec.1

private theorem auxIrrDegNat_cast {G : Type*} [Group G] (χ : IrreducibleCharacter G) :
    (χ : ClassFunction G ℂ) 1 = (auxIrrDegNat χ : ℂ) :=
  (irreducibleCharacter_apply_one_eq_pos_natCast χ).choose_spec.2

/-- The squared degrees of all irreducible characters of a finite group sum to the group order,
as an identity in `ℕ`. -/
private theorem aux_sum_sq_eq_card {G : Type*} [Group G] [Finite G] :
    ∑ χ : IrreducibleCharacter G, (auxIrrDegNat χ)^2 = Nat.card G := by
  have hC : ((∑ χ : IrreducibleCharacter G, (auxIrrDegNat χ)^2 : ℕ) : ℂ) =
      (Nat.card G : ℂ) := by
    push_cast
    calc ∑ χ : IrreducibleCharacter G, (auxIrrDegNat χ : ℂ)^2
        = ∑ χ : IrreducibleCharacter G, ((χ : ClassFunction G ℂ) 1)^2 := by
          refine Finset.sum_congr rfl (fun χ _ => ?_)
          rw [auxIrrDegNat_cast χ]
      _ = (Nat.card G : ℂ) := sumIrreducibleDegreeSq
  exact_mod_cast hC

theorem irr_deg_six_mem_range {G : Type} [Group G] [Finite G]
    (n : ℕ) (ι : Fin n → OddOrder.RepresentationTheory.IrreducibleCharacter G) (f : Fin n → ℕ)
    (hcard : Nat.card G = 2520)
    (hinj : Function.Injective ι)
    (hntriv : ∀ i, ι i ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter G)
    (hdeg : ∀ i, (ι i : OddOrder.RepresentationTheory.ClassFunction G ℂ) 1 = (f i : ℂ))
    (hsum : 1 + ∑ i, (f i) ^ 2 = 2520)
    (χ : OddOrder.RepresentationTheory.IrreducibleCharacter G)
    (hχ : (χ : OddOrder.RepresentationTheory.ClassFunction G ℂ) 1 = 6) :
    ∃ i, ι i = χ := by
  classical
  -- the prescribed degrees `f i` are exactly the natural degrees of `ι i`
  have hfN : ∀ i, f i = auxIrrDegNat (ι i) := by
    intro i
    have h1 : (f i : ℂ) = (auxIrrDegNat (ι i) : ℂ) := by
      rw [← hdeg i]; exact auxIrrDegNat_cast (ι i)
    exact Nat.cast_injective h1
  -- the prescribed degrees sum to the nontrivial degree budget
  have hsumF : ∑ i, (f i)^2 = 2519 := by omega
  -- the same sum, taken over the range of `ι`
  have hT : ∑ x ∈ Finset.univ.image ι, (auxIrrDegNat x)^2 = 2519 := by
    rw [Finset.sum_image (s := Finset.univ) (g := ι)
      (f := fun x => (auxIrrDegNat x)^2) hinj.injOn]
    rw [← hsumF]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hfN i]
  have htrivnot : trivialIrreducibleCharacter G ∉ Finset.univ.image ι := by
    rw [Finset.mem_image]
    rintro ⟨i, -, hi⟩
    exact hntriv i hi
  have htrivdeg : (auxIrrDegNat (trivialIrreducibleCharacter G))^2 = 1 := by
    have h1 := auxIrrDegNat_cast (trivialIrreducibleCharacter G)
    have h2 : (auxIrrDegNat (trivialIrreducibleCharacter G) : ℂ) = 1 := by
      rw [← h1]; simp
    have h3 : auxIrrDegNat (trivialIrreducibleCharacter G) = 1 := by exact_mod_cast h2
    simp [h3]
  -- adjoining the trivial character saturates the total degree budget
  have hs_sum : ∑ x ∈ insert (trivialIrreducibleCharacter G) (Finset.univ.image ι),
        (auxIrrDegNat x)^2
      = ∑ x : IrreducibleCharacter G, (auxIrrDegNat x)^2 := by
    rw [Finset.sum_insert htrivnot, htrivdeg, hT, aux_sum_sq_eq_card, hcard]
  have hs : insert (trivialIrreducibleCharacter G) (Finset.univ.image ι) = Finset.univ :=
    aux_eq_univ_of_sum_eq_of_one_le (fun χ => (auxIrrDegNat χ)^2)
      (fun χ => by have h := auxIrrDegNat_pos χ; exact Nat.one_le_pow 2 _ (by omega)) _ hs_sum
  have hχmem : χ ∈ insert (trivialIrreducibleCharacter G) (Finset.univ.image ι) := by
    rw [hs]; exact Finset.mem_univ χ
  rw [Finset.mem_insert] at hχmem
  rcases hχmem with h | h
  · -- `χ` is not the trivial character, since its degree is `6`
    exfalso
    have h1 : (χ : ClassFunction G ℂ) 1 = 1 := by rw [h]; simp
    rw [hχ] at h1
    norm_num at h1
  · -- hence it lies in the range of `ι`
    rw [Finset.mem_image] at h
    obtain ⟨i, -, hi⟩ := h
    exact ⟨i, hi⟩

end Work.A7REC.Char
