import Mathlib
import Submission.Work.DSM5b.HCF.Surj
import Submission.Work.DSEQ0.surjCech_vanishing

/-!
# Exactness of the surjection complex above its top degree

For a finite set `S₀ ⊆ Fin n` and an `R`-module `N`, let

  `SurjTerm S₀ N q = {τ : Fin (q+1) → Fin n // tupRng τ = S₀} → N`

be the `q`-th term of the (unnormalised) *surjection complex* supported on `S₀`, with the
differential `surjD` that drops the deletions which lose surjectivity onto `S₀`.

The present file proves that this complex is exact in every degree `≥ ♯S₀`, i.e. that every
cocycle `z` in degree `p+1` with `♯S₀ ≤ p+1` is a coboundary:

  `z ∈ range (surjD S₀ N p)`.

The proof identifies the complex with the `DSEQ0` "surjective tuples" complex over the index type
`↥S₀` (lifted to the universe of `N` by `ULift`, so that the `DSEQ0` vanishing theorem, which
requires the index type and the coefficients to live in the same universe, applies verbatim):

* `ext S₀ N z` extends a cochain on the surjective tuples to *all* tuples, by `0` off the
  surjective ones;
* `cob (ext z) = ext (surjD z)` (`cob_ext`), so `ext z` is a cocycle when `z` is;
* `Work.DSEQ0.surjCech_vanishing` then produces a supported cochain `b` of one degree less with
  `cob b = ext z`, which restricts back (`toSubs`) to a cochain whose `surjD` is `z`.
-/

universe u

namespace Work.DSM5b.HCF

open Classical

/-- Forget an element of the lifted subtype to `Fin n`. -/
def subsVal {n : ℕ} (S₀ : Finset (Fin n)) (x : ULift.{u, 0} ↥S₀) : Fin n := (x.down : Fin n)

/-- View a tuple `τ : Fin (q+1) → Fin n` with range `S₀` as a tuple into `ULift.{u, 0} ↥S₀`. -/
def toSubs {n : ℕ} (S₀ : Finset (Fin n)) {q : ℕ} (τ : Fin (q+1) → Fin n)
    (h : Work.DSM5b.tupRng τ = S₀) : Fin (q+1) → ULift.{u, 0} ↥S₀ :=
  fun i => ULift.up ⟨τ i, by rw [← h]; exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩

/-- The range of a tuple into `ULift.{u, 0} ↥S₀` equals `S₀` exactly when the tuple is surjective. -/
lemma tupRng_subsVal_eq {n : ℕ} (S₀ : Finset (Fin n)) {q : ℕ} (σ : Fin (q+1) → ULift.{u, 0} ↥S₀) :
    Work.DSM5b.tupRng (fun i => subsVal S₀ (σ i)) = S₀ ↔ Function.Surjective σ := by
  constructor
  · intro h b
    have hb : (b.down : Fin n) ∈ Work.DSM5b.tupRng (fun i => subsVal S₀ (σ i)) := by
      rw [h]; exact b.down.2
    rw [Work.DSM5b.tupRng, Finset.mem_image] at hb
    obtain ⟨i, -, hi⟩ := hb
    exact ⟨i, ULift.ext (Subtype.ext hi)⟩
  · intro h
    ext x
    constructor
    · intro hx
      rw [Work.DSM5b.tupRng, Finset.mem_image] at hx
      obtain ⟨i, -, rfl⟩ := hx
      exact (σ i).down.2
    · intro hx
      obtain ⟨i, hi⟩ := h (ULift.up ⟨x, hx⟩)
      rw [Work.DSM5b.tupRng, Finset.mem_image]
      exact ⟨i, Finset.mem_univ _, by rw [hi]; rfl⟩

/-- Forgetting `toSubs` recovers the original tuple. -/
lemma subsVal_toSubs {n : ℕ} (S₀ : Finset (Fin n)) {q : ℕ} (τ : Fin (q+1) → Fin n)
    (h : Work.DSM5b.tupRng τ = S₀) : (fun i => subsVal S₀ (toSubs S₀ τ h i)) = τ := by
  funext i; rfl

/-- `toSubs` of a tuple surjective onto `S₀` is a surjective tuple into `ULift.{u, 0} ↥S₀`. -/
lemma toSubs_surjective {n : ℕ} (S₀ : Finset (Fin n)) {q : ℕ} (τ : Fin (q+1) → Fin n)
    (h : Work.DSM5b.tupRng τ = S₀) : Function.Surjective (toSubs S₀ τ h) := by
  rw [← tupRng_subsVal_eq S₀ (toSubs S₀ τ h), subsVal_toSubs S₀ τ h]; exact h

/-- Deleting a coordinate commutes with `toSubs`. -/
lemma toSubs_succAbove {n : ℕ} (S₀ : Finset (Fin n)) {q : ℕ} (τ : Fin (q+2) → Fin n)
    (hτ : Work.DSM5b.tupRng τ = S₀) (i : Fin (q+2))
    (h : Work.DSM5b.tupRng (Work.DSM5b.tupDel i τ) = S₀) :
    toSubs S₀ (Work.DSM5b.tupDel i τ) h = toSubs S₀ τ hτ ∘ Fin.succAbove i := by
  funext j; apply ULift.ext; apply Subtype.ext; rfl

/-- If deleting the `i`-th coordinate destroys surjectivity onto `S₀`, then the corresponding
deletion of `toSubs τ` is not surjective either. -/
lemma not_surj_toSubs_comp {n : ℕ} (S₀ : Finset (Fin n)) {q : ℕ} (τ : Fin (q+2) → Fin n)
    (hτ : Work.DSM5b.tupRng τ = S₀) (i : Fin (q+2))
    (h : Work.DSM5b.tupRng (Work.DSM5b.tupDel i τ) ≠ S₀) :
    ¬ Function.Surjective (toSubs S₀ τ hτ ∘ Fin.succAbove i) := by
  intro hs
  have hkey : (fun j => subsVal S₀ ((toSubs S₀ τ hτ ∘ Fin.succAbove i) j))
      = Work.DSM5b.tupDel i τ := by
    funext j
    rw [Function.comp_apply]
    exact congrFun (subsVal_toSubs S₀ τ hτ) (Fin.succAbove i j)
  have hthis := (tupRng_subsVal_eq S₀ (toSubs S₀ τ hτ ∘ Fin.succAbove i)).mpr hs
  rw [hkey] at hthis
  exact h hthis

/-- Extend a cochain on the surjective tuples onto `S₀` to all tuples into `ULift.{u, 0} ↥S₀`, by `0` off
the surjective ones.  This is the identification of the surjection complex on `S₀` with the
`DSEQ0` subcomplex `F (♯S₀)` of the full tuple complex on `↥S₀`. -/
noncomputable def ext {n : ℕ} (S₀ : Finset (Fin n)) (N : Type u) [AddCommGroup N] {q : ℕ}
    (z : Work.DSM5b.SurjTerm S₀ N q) : (Fin (q+1) → ULift.{u, 0} ↥S₀) → N :=
  fun σ => if h : Function.Surjective σ then
    z ⟨fun i => subsVal S₀ (σ i), (tupRng_subsVal_eq S₀ σ).mpr h⟩ else 0

/-- `ext` of the zero cochain is zero. -/
lemma ext_zero {n : ℕ} (S₀ : Finset (Fin n)) (N : Type u) [AddCommGroup N] {q : ℕ} :
    ext S₀ N (0 : Work.DSM5b.SurjTerm S₀ N q) = 0 := by
  funext σ
  rw [ext]
  by_cases h : Function.Surjective σ
  · rw [dif_pos h]; simp
  · rw [dif_neg h]; simp

/-- The `R`-scalar `(-1)^j` and the `ℤ`-scalar `(-1)^j` act the same way. -/
lemma neg_one_smul_eq {R : Type u} [Ring R] {N : Type u} [AddCommGroup N] [Module R N]
    (j : ℕ) (y : N) : (-1 : R) ^ j • y = ((-1 : ℤ) ^ j) • y := by
  have h1 : (-1 : R) = (((-1 : ℤ)) : R) := by simp
  rw [h1, ← Int.cast_pow]
  exact Int.cast_smul_eq_zsmul R _ y

/-- Evaluation of `ext` on a deletion. -/
lemma ext_comp_succAbove {n : ℕ} (S₀ : Finset (Fin n)) (N : Type u) [AddCommGroup N]
    {q : ℕ} (z : Work.DSM5b.SurjTerm S₀ N q) (x : Fin (q+2) → ULift.{u, 0} ↥S₀) (j : Fin (q+2)) :
    ext S₀ N z (x ∘ Fin.succAbove j)
      = if h : Work.DSM5b.tupRng (Work.DSM5b.tupDel j (fun i => subsVal S₀ (x i))) = S₀
        then z ⟨Work.DSM5b.tupDel j (fun i => subsVal S₀ (x i)), h⟩ else 0 := by
  rw [ext]
  by_cases hc : Function.Surjective (x ∘ Fin.succAbove j)
  · rw [dif_pos hc]
    have hthis : Work.DSM5b.tupRng (Work.DSM5b.tupDel j (fun i => subsVal S₀ (x i))) = S₀ :=
      (tupRng_subsVal_eq S₀ (x ∘ Fin.succAbove j)).mpr hc
    rw [dif_pos hthis]
    exact congrArg z (Subtype.ext rfl)
  · rw [dif_neg hc]
    have hthis : Work.DSM5b.tupRng (Work.DSM5b.tupDel j (fun i => subsVal S₀ (x i))) ≠ S₀ :=
      fun h => hc ((tupRng_subsVal_eq S₀ (x ∘ Fin.succAbove j)).mp h)
    rw [dif_neg hthis]

/-- Surjectivity is preserved by deleting a coordinate. -/
lemma surj_of_comp_succAbove {n : ℕ} (S₀ : Finset (Fin n)) {q : ℕ} {x : Fin (q+2) → ULift.{u, 0} ↥S₀}
    (j : Fin (q+2)) (h : Function.Surjective (x ∘ Fin.succAbove j)) : Function.Surjective x := by
  intro b
  obtain ⟨i, hi⟩ := h b
  exact ⟨Fin.succAbove j i, hi⟩

/-- **The key identity**: `ext` intertwines the `DSEQ0` coboundary `cob` with the surjection
differential `surjD`, i.e. it is a chain map (into the `F (♯S₀)`-subcomplex). -/
lemma cob_ext {n : ℕ} (S₀ : Finset (Fin n)) (N : Type u) [AddCommGroup N] {R : Type u}
    [CommRing R] [Module R N] {q : ℕ} (z : Work.DSM5b.SurjTerm S₀ N q) :
    Work.DSEQ0.cob q (ext S₀ N z) = ext S₀ N (Work.DSM5b.surjD (R:=R) S₀ N q z) := by
  funext x
  rw [Work.DSEQ0.cob]
  have hterm : ∀ j : Fin (q+2),
      (-1 : ℤ) ^ (j:ℕ) • ext S₀ N z (x ∘ Fin.succAbove j)
      = if h : Work.DSM5b.tupRng (Work.DSM5b.tupDel j (fun i => subsVal S₀ (x i))) = S₀
        then (-1 : ℤ) ^ (j:ℕ) • z ⟨Work.DSM5b.tupDel j (fun i => subsVal S₀ (x i)), h⟩
        else 0 := by
    intro j
    rw [ext_comp_succAbove]
    by_cases h : Work.DSM5b.tupRng (Work.DSM5b.tupDel j (fun i => subsVal S₀ (x i))) = S₀
    · rw [dif_pos h, dif_pos h]
    · rw [dif_neg h, dif_neg h, smul_zero]
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  by_cases hsurj : Function.Surjective x
  · rw [ext, dif_pos hsurj]
    have hR : (Work.DSM5b.surjD (R:=R) S₀ N q z) ⟨fun i => subsVal S₀ (x i),
        (tupRng_subsVal_eq S₀ x).mpr hsurj⟩
        = ∑ i, (if h : Work.DSM5b.tupRng (Work.DSM5b.tupDel i (fun i => subsVal S₀ (x i))) = S₀
            then (-1:R)^(i:ℕ) • z ⟨Work.DSM5b.tupDel i (fun i => subsVal S₀ (x i)), h⟩ else 0)
        := rfl
    rw [hR]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases h : Work.DSM5b.tupRng (Work.DSM5b.tupDel i (fun i => subsVal S₀ (x i))) = S₀
    · rw [dif_pos h, dif_pos h, neg_one_smul_eq]
    · rw [dif_neg h, dif_neg h]
  · rw [ext, dif_neg hsurj]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    have hj : ¬ (Work.DSM5b.tupRng (Work.DSM5b.tupDel j (fun i => subsVal S₀ (x i))) = S₀) :=
      fun h => hsurj (surj_of_comp_succAbove S₀ j ((tupRng_subsVal_eq S₀ (x ∘ Fin.succAbove j)).mp h))
    rw [dif_neg hj]

/-- **Exactness of the surjection complex above its top degree.** For `♯S₀ ≤ p+1`, every cocycle
of `surjD S₀ N (p+1)` is in the range of `surjD S₀ N p`. -/
theorem surjD_exact_high {R : Type u} [CommRing R] {n : ℕ} (S₀ : Finset (Fin n)) (N : Type u)
    [AddCommGroup N] [Module R N] (p : ℕ) (hp : S₀.card ≤ p + 1)
    (z : Work.DSM5b.SurjTerm S₀ N (p + 1))
    (hz : Work.DSM5b.surjD (R := R) S₀ N (p + 1) z = 0) :
    z ∈ LinearMap.range (Work.DSM5b.surjD (R := R) S₀ N p) := by
  -- `ext z` vanishes off the surjective tuples
  have hsupp : ∀ g : Fin (p+2) → ULift.{u, 0} ↥S₀, ¬ Function.Surjective g → ext S₀ N z g = 0 := by
    intro g hg
    rw [ext, dif_neg hg]
  -- and is a cocycle, because `cob` commutes with `ext`
  have hcob0 : Work.DSEQ0.cob (p+1) (ext S₀ N z) = 0 := by
    rw [cob_ext (S₀ := S₀) (N := N) (R := R) (q := p+1) z, hz, ext_zero]
  have ha : ∀ x : Fin ((p+1)+2) → ULift.{u, 0} ↥S₀,
      ∑ k : Fin ((p+1)+2), (-1:ℤ)^(k:ℕ) • ext S₀ N z (x ∘ Fin.succAbove k) = 0 := by
    intro x
    have h := congrFun hcob0 x
    simp only [Work.DSEQ0.cob, Pi.zero_apply] at h
    exact h
  -- the vanishing theorem applies since `♯S₀ ≤ p+1`
  have hcard : Fintype.card (ULift.{u, 0} ↥S₀) ≤ p + 1 := by
    rw [Fintype.card_congr Equiv.ulift, Fintype.card_coe]
    exact hp
  obtain ⟨b, hbsupp, hbcob⟩ :=
    Work.DSEQ0.surjCech_vanishing (ι := ULift.{u, 0} ↥S₀) (M := N) (p+1) hcard (ext S₀ N z) hsupp ha
  -- restrict `b` back to a cochain on the surjective tuples of one degree less
  refine ⟨fun σ => b (toSubs S₀ σ.1 σ.2), ?_⟩
  funext τ
  have hsurjτ : Function.Surjective (toSubs S₀ τ.1 τ.2) := toSubs_surjective S₀ τ.1 τ.2
  have hzt : ext S₀ N z (toSubs S₀ τ.1 τ.2) = z τ := by
    rw [ext, dif_pos hsurjτ]
    have hsub : (fun i => subsVal S₀
        ((toSubs S₀ τ.1 τ.2 : Fin (p + 2) → ULift.{u, 0} ↥S₀) i)) = τ.1 := by
      funext i; rfl
    exact congrArg z (Subtype.ext hsub)
  have hb := hbcob (toSubs S₀ τ.1 τ.2)
  rw [hzt] at hb
  rw [← hb]
  show (∑ i : Fin (p+2), if h : Work.DSM5b.tupRng (Work.DSM5b.tupDel i τ.1) = S₀
      then (-1:R)^(i:ℕ) • b (toSubs S₀ (Work.DSM5b.tupDel i τ.1) h) else 0)
    = ∑ j : Fin (p+2), (-1:ℤ)^(j:ℕ) • b (toSubs S₀ τ.1 τ.2 ∘ Fin.succAbove j)
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases h : Work.DSM5b.tupRng (Work.DSM5b.tupDel i τ.1) = S₀
  · rw [dif_pos h]
    rw [toSubs_succAbove S₀ τ.1 τ.2 i h]
    exact neg_one_smul_eq (i:ℕ) _
  · rw [dif_neg h]
    have hns : ¬ Function.Surjective (toSubs S₀ τ.1 τ.2 ∘ Fin.succAbove i) :=
      not_surj_toSubs_comp S₀ τ.1 τ.2 i h
    rw [hbsupp _ hns, smul_zero]

end Work.DSM5b.HCF
