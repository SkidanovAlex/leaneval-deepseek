import Mathlib
import Submission.Work.DSM5b.HCF.GenSurj
import Submission.Work.DSM5b.HCF.surjD_exact_high
import Submission.Work.DSEQ0.surjCech_vanishing

/-!
# Exactness of the surjection complex over an arbitrary finset

`Work.DSM5b.HCF.GSurjTerm S₀ N q` is the `q`-th term of the surjection complex attached to an
*arbitrary* finset `S₀ : Finset ι` (see `Submission/Work/DSM5b/HCF/GenSurj.lean`), with
differential `gsurjD`; it is the honest tuple complex of the coefficient system supported on the
single subset `S₀`.

Here we prove that this complex is exact in every degree `≥ ♯S₀`: for `♯S₀ ≤ p+1` every cocycle
`z` of `gsurjD S₀ N (p+1)` is in the range of `gsurjD S₀ N p`.

The argument is the same as in `Submission/Work/DSM5b/HCF/surjD_exact_high.lean` (which treats
`S₀ : Finset (Fin n)`), transcribed to an arbitrary index type `ι`: the complex is identified
with the `DSEQ0` "surjective tuples" complex over the index type `↥S₀`, lifted by `ULift` so that
the `DSEQ0` vanishing theorem `Work.DSEQ0.surjCech_vanishing` — which requires the index type and
the coefficients to live in the same universe — applies verbatim.

* `gSubsVal S₀ x` forgets the lift of an element of `↥S₀`;
* `gToSubs S₀ τ h` views a tuple `τ : Fin (q+1) → ι` of range `S₀` as a tuple into `GULift S₀`;
* `gExt S₀ N z` extends a cochain on the surjective tuples to *all* tuples, by `0` off the
  surjective ones;
* `g_cob_ext` shows `cob (gExt z) = gExt (gsurjD z)`, so `gExt z` is a cocycle when `z` is;
* `Work.DSEQ0.surjCech_vanishing` then produces a supported cochain `b` of one degree less with
  `cob b = gExt z`, which restricts back (`gToSubs`) to a cochain whose `gsurjD` is `z`.
-/

universe u

namespace Work.DSM5b.HCF

open Classical

/-- The lift of a subtype of `ι` into the universe of the coefficients. -/
abbrev GULift {ι : Type u} (S₀ : Finset ι) : Type u := ULift.{u, u} ↥S₀

/-- Forget the lift of an element of a subtype. -/
def gSubsVal {ι : Type u} (S₀ : Finset ι) (x : GULift S₀) : ι := (x.down : ι)

/-- View a tuple `τ : Fin (q+1) → ι` with range `S₀` as a tuple into `GULift S₀`. -/
def gToSubs {ι : Type u} [DecidableEq ι] (S₀ : Finset ι) {q : ℕ} (τ : Fin (q+1) → ι)
    (h : Work.DSM5b.tupRng τ = S₀) : Fin (q+1) → GULift S₀ :=
  fun i => ULift.up ⟨τ i, by rw [← h]; exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩

/-- The range of a tuple into `GULift S₀` equals `S₀` exactly when the tuple is surjective. -/
lemma g_tupRng_subsVal_eq {ι : Type u} [DecidableEq ι] (S₀ : Finset ι) {q : ℕ}
    (σ : Fin (q+1) → GULift S₀) :
    Work.DSM5b.tupRng (fun i => gSubsVal S₀ (σ i)) = S₀ ↔ Function.Surjective σ := by
  constructor
  · intro h b
    have hb : (b.down : ι) ∈ Work.DSM5b.tupRng (fun i => gSubsVal S₀ (σ i)) := by
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

/-- Forgetting `gToSubs` recovers the original tuple. -/
lemma g_subsVal_toSubs {ι : Type u} [DecidableEq ι] (S₀ : Finset ι) {q : ℕ}
    (τ : Fin (q+1) → ι) (h : Work.DSM5b.tupRng τ = S₀) :
    (fun i => gSubsVal S₀ (gToSubs S₀ τ h i)) = τ := by
  funext i; rfl

/-- `gToSubs` of a tuple of range `S₀` is a surjective tuple into `GULift S₀`. -/
lemma g_toSubs_surjective {ι : Type u} [DecidableEq ι] (S₀ : Finset ι) {q : ℕ}
    (τ : Fin (q+1) → ι) (h : Work.DSM5b.tupRng τ = S₀) :
    Function.Surjective (gToSubs S₀ τ h) := by
  rw [← g_tupRng_subsVal_eq S₀ (gToSubs S₀ τ h), g_subsVal_toSubs S₀ τ h]; exact h

/-- Deleting a coordinate commutes with `gToSubs`. -/
lemma g_toSubs_succAbove {ι : Type u} [DecidableEq ι] (S₀ : Finset ι) {q : ℕ}
    (τ : Fin (q+2) → ι) (hτ : Work.DSM5b.tupRng τ = S₀) (i : Fin (q+2))
    (h : Work.DSM5b.tupRng (Work.DSM5b.tupDel i τ) = S₀) :
    gToSubs S₀ (Work.DSM5b.tupDel i τ) h = gToSubs S₀ τ hτ ∘ Fin.succAbove i := by
  funext j; apply ULift.ext; apply Subtype.ext; rfl

/-- If deleting the `i`-th coordinate destroys surjectivity onto `S₀`, then the corresponding
deletion of `gToSubs τ` is not surjective either. -/
lemma g_not_surj_toSubs_comp {ι : Type u} [DecidableEq ι] (S₀ : Finset ι) {q : ℕ}
    (τ : Fin (q+2) → ι) (hτ : Work.DSM5b.tupRng τ = S₀) (i : Fin (q+2))
    (h : Work.DSM5b.tupRng (Work.DSM5b.tupDel i τ) ≠ S₀) :
    ¬ Function.Surjective (gToSubs S₀ τ hτ ∘ Fin.succAbove i) := by
  intro hs
  have hkey : (fun j => gSubsVal S₀ ((gToSubs S₀ τ hτ ∘ Fin.succAbove i) j))
      = Work.DSM5b.tupDel i τ := by
    funext j
    rw [Function.comp_apply]
    exact congrFun (g_subsVal_toSubs S₀ τ hτ) (Fin.succAbove i j)
  have hthis := (g_tupRng_subsVal_eq S₀ (gToSubs S₀ τ hτ ∘ Fin.succAbove i)).mpr hs
  rw [hkey] at hthis
  exact h hthis

/-- Extend a cochain on the tuples of range `S₀` to all tuples into `GULift S₀`, by `0` off the
surjective ones.  This identifies the surjection complex on `S₀` with the `DSEQ0` subcomplex
`F (♯S₀)` of the full tuple complex on `↥S₀`. -/
noncomputable def gExt {ι : Type u} [DecidableEq ι] (S₀ : Finset ι) (N : Type u)
    [AddCommGroup N] {q : ℕ} (z : GSurjTerm S₀ N q) : (Fin (q+1) → GULift S₀) → N :=
  fun σ => if h : Function.Surjective σ then
    z ⟨fun i => gSubsVal S₀ (σ i), (g_tupRng_subsVal_eq S₀ σ).mpr h⟩ else 0

/-- `gExt` of the zero cochain is zero. -/
lemma g_ext_zero {ι : Type u} [DecidableEq ι] (S₀ : Finset ι) (N : Type u) [AddCommGroup N]
    {q : ℕ} : gExt S₀ N (0 : GSurjTerm S₀ N q) = 0 := by
  funext σ
  rw [gExt]
  by_cases h : Function.Surjective σ
  · rw [dif_pos h]; simp
  · rw [dif_neg h]; simp

/-- The `R`-scalar `(-1)^j` and the `ℤ`-scalar `(-1)^j` act the same way. -/
lemma g_neg_one_smul_eq {R : Type u} [Ring R] {N : Type u} [AddCommGroup N] [Module R N]
    (j : ℕ) (y : N) : (-1 : R) ^ j • y = ((-1 : ℤ) ^ j) • y := by
  have h1 : (-1 : R) = (((-1 : ℤ)) : R) := by simp
  rw [h1, ← Int.cast_pow]
  exact Int.cast_smul_eq_zsmul R _ y

/-- Evaluation of `gExt` on a deletion. -/
lemma g_ext_comp_succAbove {ι : Type u} [DecidableEq ι] (S₀ : Finset ι) (N : Type u)
    [AddCommGroup N] {q : ℕ} (z : GSurjTerm S₀ N q) (x : Fin (q+2) → GULift S₀)
    (j : Fin (q+2)) :
    gExt S₀ N z (x ∘ Fin.succAbove j)
      = if h : Work.DSM5b.tupRng (Work.DSM5b.tupDel j (fun i => gSubsVal S₀ (x i))) = S₀
        then z ⟨Work.DSM5b.tupDel j (fun i => gSubsVal S₀ (x i)), h⟩ else 0 := by
  rw [gExt]
  by_cases hc : Function.Surjective (x ∘ Fin.succAbove j)
  · rw [dif_pos hc]
    have hthis : Work.DSM5b.tupRng (Work.DSM5b.tupDel j (fun i => gSubsVal S₀ (x i))) = S₀ :=
      (g_tupRng_subsVal_eq S₀ (x ∘ Fin.succAbove j)).mpr hc
    rw [dif_pos hthis]
    exact congrArg z (Subtype.ext rfl)
  · rw [dif_neg hc]
    have hthis : Work.DSM5b.tupRng (Work.DSM5b.tupDel j (fun i => gSubsVal S₀ (x i))) ≠ S₀ :=
      fun h => hc ((g_tupRng_subsVal_eq S₀ (x ∘ Fin.succAbove j)).mp h)
    rw [dif_neg hthis]

/-- Surjectivity is preserved by deleting a coordinate. -/
lemma g_surj_of_comp_succAbove {ι : Type u} [DecidableEq ι] (S₀ : Finset ι) {q : ℕ}
    {x : Fin (q+2) → GULift S₀} (j : Fin (q+2))
    (h : Function.Surjective (x ∘ Fin.succAbove j)) : Function.Surjective x := by
  intro b
  obtain ⟨i, hi⟩ := h b
  exact ⟨Fin.succAbove j i, hi⟩

/-- **The key identity**: `gExt` intertwines the `DSEQ0` coboundary `cob` with the surjection
differential `gsurjD`, i.e. it is a chain map (into the `F (♯S₀)`-subcomplex). -/
lemma g_cob_ext {ι : Type u} [DecidableEq ι] (S₀ : Finset ι) (N : Type u) [AddCommGroup N]
    {R : Type u} [CommRing R] [Module R N] {q : ℕ} (z : GSurjTerm S₀ N q) :
    Work.DSEQ0.cob q (gExt S₀ N z) = gExt S₀ N (gsurjD (R:=R) S₀ N q z) := by
  funext x
  rw [Work.DSEQ0.cob]
  have hterm : ∀ j : Fin (q+2),
      (-1 : ℤ) ^ (j:ℕ) • gExt S₀ N z (x ∘ Fin.succAbove j)
      = if h : Work.DSM5b.tupRng (Work.DSM5b.tupDel j (fun i => gSubsVal S₀ (x i))) = S₀
        then (-1 : ℤ) ^ (j:ℕ) • z ⟨Work.DSM5b.tupDel j (fun i => gSubsVal S₀ (x i)), h⟩
        else 0 := by
    intro j
    rw [g_ext_comp_succAbove]
    by_cases h : Work.DSM5b.tupRng (Work.DSM5b.tupDel j (fun i => gSubsVal S₀ (x i))) = S₀
    · rw [dif_pos h, dif_pos h]
    · rw [dif_neg h, dif_neg h, smul_zero]
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  by_cases hsurj : Function.Surjective x
  · rw [gExt, dif_pos hsurj]
    have hR : (gsurjD (R:=R) S₀ N q z) ⟨fun i => gSubsVal S₀ (x i),
        (g_tupRng_subsVal_eq S₀ x).mpr hsurj⟩
        = ∑ i, (if h : Work.DSM5b.tupRng (Work.DSM5b.tupDel i (fun i => gSubsVal S₀ (x i))) = S₀
            then (-1:R)^(i:ℕ) • z ⟨Work.DSM5b.tupDel i (fun i => gSubsVal S₀ (x i)), h⟩ else 0)
        := rfl
    rw [hR]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases h : Work.DSM5b.tupRng (Work.DSM5b.tupDel i (fun i => gSubsVal S₀ (x i))) = S₀
    · rw [dif_pos h, dif_pos h, g_neg_one_smul_eq]
    · rw [dif_neg h, dif_neg h]
  · rw [gExt, dif_neg hsurj]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    have hj : ¬ (Work.DSM5b.tupRng (Work.DSM5b.tupDel j (fun i => gSubsVal S₀ (x i))) = S₀) :=
      fun h => hsurj (g_surj_of_comp_succAbove S₀ j ((g_tupRng_subsVal_eq S₀ (x ∘ Fin.succAbove j)).mp h))
    rw [dif_neg hj]

/-- **Exactness of the surjection complex over an arbitrary finset above its top degree.** For
`♯S₀ ≤ p+1`, every cocycle of `gsurjD S₀ N (p+1)` is in the range of `gsurjD S₀ N p`. -/
theorem gsurjD_exact_high {R : Type u} [CommRing R] {ι : Type u} [DecidableEq ι]
    (S₀ : Finset ι) (N : Type u) [AddCommGroup N] [Module R N] (p : ℕ)
    (hp : S₀.card ≤ p + 1) (z : Work.DSM5b.HCF.GSurjTerm S₀ N (p + 1))
    (hz : Work.DSM5b.HCF.gsurjD (R := R) S₀ N (p + 1) z = 0) :
    z ∈ LinearMap.range (Work.DSM5b.HCF.gsurjD (R := R) S₀ N p) := by
  -- `gExt z` vanishes off the surjective tuples
  have hsupp : ∀ g : Fin (p+2) → GULift S₀, ¬ Function.Surjective g → gExt S₀ N z g = 0 := by
    intro g hg
    rw [gExt, dif_neg hg]
  -- and is a cocycle, because `cob` commutes with `gExt`
  have hcob0 : Work.DSEQ0.cob (p+1) (gExt S₀ N z) = 0 := by
    rw [g_cob_ext (S₀ := S₀) (N := N) (R := R) (q := p+1) z, hz, g_ext_zero]
  have ha : ∀ x : Fin ((p+1)+2) → GULift S₀,
      ∑ k : Fin ((p+1)+2), (-1:ℤ)^(k:ℕ) • gExt S₀ N z (x ∘ Fin.succAbove k) = 0 := by
    intro x
    have h := congrFun hcob0 x
    simp only [Work.DSEQ0.cob, Pi.zero_apply] at h
    exact h
  -- the vanishing theorem applies since `♯S₀ ≤ p+1`
  have hcard : Fintype.card (GULift S₀) ≤ p + 1 := by
    rw [Fintype.card_congr Equiv.ulift, Fintype.card_coe]
    exact hp
  obtain ⟨b, hbsupp, hbcob⟩ :=
    Work.DSEQ0.surjCech_vanishing (ι := GULift S₀) (M := N) (p+1) hcard (gExt S₀ N z) hsupp ha
  -- restrict `b` back to a cochain on the tuples of range `S₀`, one degree lower
  refine ⟨fun σ => b (gToSubs S₀ σ.1 σ.2), ?_⟩
  funext τ
  have hsurjτ : Function.Surjective (gToSubs S₀ τ.1 τ.2) := g_toSubs_surjective S₀ τ.1 τ.2
  have hzt : gExt S₀ N z (gToSubs S₀ τ.1 τ.2) = z τ := by
    rw [gExt, dif_pos hsurjτ]
    have hsub : (fun i => gSubsVal S₀
        ((gToSubs S₀ τ.1 τ.2 : Fin (p + 2) → GULift S₀) i)) = τ.1 := by
      funext i; rfl
    exact congrArg z (Subtype.ext hsub)
  have hb := hbcob (gToSubs S₀ τ.1 τ.2)
  rw [hzt] at hb
  rw [← hb]
  show (∑ i : Fin (p+2), if h : Work.DSM5b.tupRng (Work.DSM5b.tupDel i τ.1) = S₀
      then (-1:R)^(i:ℕ) • b (gToSubs S₀ (Work.DSM5b.tupDel i τ.1) h) else 0)
    = ∑ j : Fin (p+2), (-1:ℤ)^(j:ℕ) • b (gToSubs S₀ τ.1 τ.2 ∘ Fin.succAbove j)
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases h : Work.DSM5b.tupRng (Work.DSM5b.tupDel i τ.1) = S₀
  · rw [dif_pos h]
    rw [g_toSubs_succAbove S₀ τ.1 τ.2 i h]
    exact g_neg_one_smul_eq (i:ℕ) _
  · rw [dif_neg h]
    have hns : ¬ Function.Surjective (gToSubs S₀ τ.1 τ.2 ∘ Fin.succAbove i) :=
      g_not_surj_toSubs_comp S₀ τ.1 τ.2 i h
    rw [hbsupp _ hns, smul_zero]

end Work.DSM5b.HCF
