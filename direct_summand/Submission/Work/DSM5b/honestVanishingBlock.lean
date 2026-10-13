import Mathlib
import Submission.Work.DSM5b.honestVanishingDefs
import Submission.Work.DSEQ0.surj_tuple_vanishing

/-!
# `Work.DSM5b.honestVanishingBlock`

The block lemma of the image-size filtration of the honest chart Čech complex
`HCX t m = ∀ τ : Fin (m+1) → ι, chartRing t (tupRng τ)`.

Let `S : Finset ι` with `S.card = j ≤ m+1`, and let `z : HCX t (m+1)` be a cocycle
(`HCd t (m+1) z = 0`) which vanishes on all tuples whose range has fewer than `j` elements
(`SuppAbove j z`).  The lemma produces a cochain `y : HCX t m` supported exactly on the
`S`-block (i.e. `y σ = 0` unless `tupRng σ = S`) with `(HCd t m y) τ = z τ` on the `S`-block.

The proof is the following elementary analysis.  Restricting to tuples with `tupRng τ = S`, the
complex is the *surjection complex* of `S` with **constant** coefficients `chartRing t S`; since
`|S| = j ≤ m+1`, that complex is acyclic in degree `m+1` (`Work.DSEQ0.surj_tuple_vanishing`), and
`z` restricted to the `S`-block is a cocycle there.  So there is a block cochain `b` in degree `m`
whose coboundary is the `S`-block of `z`, and the required `y` is `b` distributed over the tuples
of range `S` via `corestr`/`toI`.

Structure of the file: the cast toolkit (`hvb_cast_*`) for the identifications
`chartRing t S ≃ chartRing t T` induced by an equality of finsets, the two block definitions
`bloc`/`yOfBlock`, the two comparison lemmas `bloc_del`/`yOfBlock_del` (which identify the honest
differential with the block differential), the block-cocycle computation `bloc_cocycle`, and the
block-coboundary computation `yOfBlock_HCd`, followed by the assembly.
-/

namespace Work.DSM5b

open DSMap DSMap.Mix DSMap.Mix2

universe a

set_option linter.unusedSectionVars false

section Tools

variable {ι : Type a} [DecidableEq ι] {R : Type a} [CommRing R]

/-! ### The cast toolkit

If `e : S = T` is an equality of finsets, the transport `e ▸ ·` along the (propositional) equality
`chartRing t S = chartRing t T` behaves as a ring homomorphism respecting the `R`-action, sums and
composites; all of these are proved by `cases e`. -/

lemma hvb_cast_add (t : ι → R) {S T : Finset ι} (e : S = T) (x y : chartRing t S) :
    e ▸ (x + y) = e ▸ x + e ▸ y := by cases e; rfl

lemma hvb_cast_zero (t : ι → R) {S T : Finset ι} (e : S = T) :
    e ▸ (0 : chartRing t S) = 0 := by cases e; rfl

lemma hvb_cast_smul (t : ι → R) {S T : Finset ι} (e : S = T) (r : R) (x : chartRing t S) :
    e ▸ (r • x) = r • (e ▸ x) := by cases e; rfl

lemma hvb_cast_sum (t : ι → R) {S T : Finset ι} (e : S = T) {β : Type} (s : Finset β)
    (f : β → chartRing t S) : e ▸ (∑ i ∈ s, f i) = ∑ i ∈ s, e ▸ f i := by cases e; rfl

lemma hvb_cast_trans (t : ι → R) {S T V : Finset ι} (e₁ : S = T) (e₂ : T = V)
    (x : chartRing t S) : e₂ ▸ (e₁ ▸ x) = (e₁.trans e₂) ▸ x := by cases e₁; cases e₂; rfl

lemma hvb_cast_symm (t : ι → R) {S T : Finset ι} (e : S = T) (x : chartRing t S) :
    e.symm ▸ (e ▸ x) = x := by cases e; rfl

/-- The restriction map `rhoH` along an inclusion between *equal* finsets is the corresponding
transport. -/
lemma hvb_rhoH_eq_cast (t : ι → R) {S T : Finset ι} (h : S ⊆ T) (e : S = T)
    (x : chartRing t S) : rhoH t h x = e ▸ x := by
  cases e
  change rhoH t h x = x
  exact Subtype.ext (DFunLike.congr_fun (locRes_eq t h (AlgHom.id R _)) x.1).symm

/-- `(-1)`-powers: the integer cast of `(-1 : ℤ)^i` is `(-1 : R)^i`. -/
lemma hvb_intcast_pow {R : Type a} [Ring R] (i : ℕ) :
    ((↑((-1 : ℤ) ^ i) : R)) = (-1 : R) ^ i := by
  rw [Int.cast_pow, Int.cast_neg, Int.cast_one]

/-- Comparison of the integer- and the ring-multiple of `(-1)^i`. -/
lemma hvb_smul_eq_zsmul (t : ι → R) {S : Finset ι} (i : ℕ) (x : chartRing t S) :
    (-1 : R) ^ i • x = ((-1 : ℤ) ^ i) • x :=
  (congrArg (fun r : R => r • x) (hvb_intcast_pow (R := R) i).symm).trans
    (Int.cast_smul_eq_zsmul R ((-1 : ℤ) ^ i) x)

/-- The same comparison, for a transported element. -/
lemma hvb_zsmul_cast (t : ι → R) {S T : Finset ι} (e : S = T) (k : ℕ) (x : chartRing t S) :
    ((-1 : ℤ) ^ k) • (e ▸ x) = e ▸ ((-1 : R) ^ k • x) := by
  rw [← Int.cast_smul_eq_zsmul R ((-1 : ℤ) ^ k), Int.cast_pow, Int.cast_neg, Int.cast_one]
  exact (hvb_cast_smul t e ((-1 : R) ^ k) x).symm

end Tools

section Block

variable {ι : Type a} [DecidableEq ι] {R : Type a} [CommRing R]

/-- The `S`-block of a cochain `Z` of the honest chart Čech complex: a cochain of the surjection
complex on `S` with constant coefficients `chartRing t S`.  Values on tuples whose range is not
`S` are set to zero. -/
noncomputable def bloc (t : ι → R) {n : ℕ} (Z : HCX t n) (S : Finset ι) :
    (Fin (n + 1) → ↥S) → chartRing t S :=
  fun γ => if h : tupRng (toI S γ) = S then h ▸ Z (toI S γ) else 0

/-- The cochain of the honest complex in degree `m` whose only non-zero block is the `S`-block,
with block data `b : (Fin (m+1) → ↥S) → chartRing t S`. -/
noncomputable def yOfBlock (t : ι → R) {m : ℕ} (S : Finset ι)
    (b : (Fin (m + 1) → ↥S) → chartRing t S) : HCX t m :=
  fun σ => if h : tupRng σ = S then h.symm ▸ b (corestr S σ h) else 0

@[simp] lemma bloc_apply (t : ι → R) {n : ℕ} (Z : HCX t n) (S : Finset ι)
    (γ : Fin (n + 1) → ↥S) :
    bloc t Z S γ = if h : tupRng (toI S γ) = S then h ▸ Z (toI S γ) else 0 := rfl

@[simp] lemma yOfBlock_apply (t : ι → R) {m : ℕ} (S : Finset ι)
    (b : (Fin (m + 1) → ↥S) → chartRing t S) (σ : Fin (m + 1) → ι) :
    yOfBlock t S b σ = if h : tupRng σ = S then h.symm ▸ b (corestr S σ h) else 0 := rfl

/-- `toI` of a tuple with `succAbove k` deleted is the `k`-th deletion. -/
@[simp] lemma toI_comp_succAbove (S : Finset ι) {m : ℕ} (x : Fin (m + 2) → ↥S)
    (k : Fin (m + 2)) : toI S (x ∘ Fin.succAbove k) = tupDel k (toI S x) := rfl

/-- The same, for the canonical reindexing of a tuple with range `S`. -/
@[simp] lemma toI_corestr_comp (S : Finset ι) {m : ℕ} (τ : Fin (m + 2) → ι) (hτ : tupRng τ = S)
    (k : Fin (m + 2)) : toI S (corestr S τ hτ ∘ Fin.succAbove k) = tupDel k τ := rfl

/-- The same, for the canonical reindexing of a tuple with range `S`. -/
@[simp] lemma tupRng_toI_corestr_comp (S : Finset ι) {m : ℕ} (τ : Fin (m + 2) → ι)
    (hτ : tupRng τ = S) (k : Fin (m + 2)) :
    tupRng (toI S (corestr S τ hτ ∘ Fin.succAbove k)) = tupRng (tupDel k τ) := rfl

/-- Conversely, the canonical reindexing of `toI S x` is `x`. -/
@[simp] lemma corestr_toI (S : Finset ι) {m : ℕ} (x : Fin (m + 1) → ↥S)
    (h : tupRng (toI S x) = S) : corestr S (toI S x) h = x :=
  funext fun _ => Subtype.ext rfl

/-- A tuple `τ` with `tupRng τ = S` and its canonical reindexing have the same `k`-th deletion. -/
lemma corestr_del_eq (S : Finset ι) {m : ℕ} (τ : Fin (m + 2) → ι) (hτ : tupRng τ = S)
    (k : Fin (m + 2)) (h : tupRng (tupDel k τ) = S) :
    corestr S (tupDel k τ) h = corestr S τ hτ ∘ Fin.succAbove k :=
  funext fun _ => Subtype.ext rfl

/-! ### The comparison lemmas

`bloc_del` compares the block cochains with the honest differential: the block of `rhoH (Z ∘ del)`
is the transport of the block of `Z`.  `yOfBlock_del` is the corresponding statement for the
cochain produced by `yOfBlock`. -/

lemma bloc_del (t : ι → R) {n : ℕ} (Z : HCX t n) {S : Finset ι} (τ : Fin (n + 2) → ι)
    (hτ : tupRng τ = S) (k : Fin (n + 2))
    (hZ : ∀ σ : Fin (n + 1) → ι, (tupRng σ).card < S.card → Z σ = 0) :
    bloc t Z S (corestr S τ hτ ∘ Fin.succAbove k)
      = hτ ▸ rhoH t (tupRng_del_subset k τ) (Z (tupDel k τ)) := by
  rw [bloc_apply, toI_corestr_comp]
  by_cases h : tupRng (tupDel k τ) = S
  · rw [dif_pos h]
    rw [hvb_rhoH_eq_cast t (tupRng_del_subset k τ) (h.trans hτ.symm)]
    rw [hvb_cast_trans t (h.trans hτ.symm) hτ]
  · rw [dif_neg h]
    have hsub : tupRng (tupDel k τ) ⊆ S := by rw [← hτ]; exact tupRng_del_subset k τ
    have hlt : (tupRng (tupDel k τ)).card < S.card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, h⟩)
    rw [hZ _ hlt, map_zero, hvb_cast_zero]

lemma yOfBlock_del (t : ι → R) {m : ℕ} (S : Finset ι)
    (b : (Fin (m + 1) → ↥S) → chartRing t S)
    (hb : ∀ g : Fin (m + 1) → ↥S, ¬ Function.Surjective g → b g = 0)
    (τ : Fin (m + 2) → ι) (hτ : tupRng τ = S) (k : Fin (m + 2)) :
    rhoH t (tupRng_del_subset k τ) (yOfBlock t S b (tupDel k τ))
      = hτ.symm ▸ b (corestr S τ hτ ∘ Fin.succAbove k) := by
  rw [yOfBlock_apply]
  by_cases h : tupRng (tupDel k τ) = S
  · rw [dif_pos h]
    rw [hvb_rhoH_eq_cast t (tupRng_del_subset k τ) (h.trans hτ.symm)]
    rw [hvb_cast_trans t h.symm (h.trans hτ.symm)]
    rw [show b (corestr S (tupDel k τ) h) = b (corestr S τ hτ ∘ Fin.succAbove k) from
      congrArg b (corestr_del_eq S τ hτ k h)]
  · rw [dif_neg h, map_zero]
    rw [show b (corestr S τ hτ ∘ Fin.succAbove k) = 0 from
      hb _ (fun hs => h (by
        rw [← tupRng_toI_corestr_comp (S := S) τ hτ k]
        exact (tupRng_toI_eq_iff S _).mpr hs))]
    exact (hvb_cast_zero t hτ.symm).symm

/-- Unfolding of the block at the canonical representative of `τ`. -/
lemma bloc_corestr (t : ι → R) {m : ℕ} (z : HCX t (m + 1)) {S : Finset ι}
    (τ : Fin (m + 2) → ι) (hτ : tupRng τ = S) :
    bloc t z S (corestr S τ hτ) = hτ ▸ z τ := by
  rw [bloc_apply, toI_corestr, dif_pos hτ]

/-! ### The block cocycle and the block coboundary -/

/-- The `S`-block of a supported cocycle is a cocycle of the surjection complex on `S`. -/
lemma bloc_cocycle (t : ι → R) {m : ℕ} {S : Finset ι} (z : HCX t (m + 1))
    (hz : HCd t (m + 1) z = 0)
    (hZ : ∀ σ : Fin (m + 2) → ι, (tupRng σ).card < S.card → z σ = 0)
    (τ : Fin (m + 3) → ι) (hτ : tupRng τ = S) :
    ∑ k : Fin (m + 3), (-1 : ℤ) ^ (k : ℕ) • bloc t z S (corestr S τ hτ ∘ Fin.succAbove k) = 0 := by
  have hzτ : ∑ k : Fin (m + 3), (-1 : R) ^ (k : ℕ) •
      rhoH t (tupRng_del_subset k τ) (z (tupDel k τ)) = 0 := by
    have h := congrFun hz τ
    simp only [HCd_apply, Pi.zero_apply] at h
    exact h
  have hterm : ∀ k : Fin (m + 3),
      (-1 : ℤ) ^ (k : ℕ) • bloc t z S (corestr S τ hτ ∘ Fin.succAbove k)
        = hτ ▸ ((-1 : R) ^ (k : ℕ) • rhoH t (tupRng_del_subset k τ) (z (tupDel k τ))) := by
    intro k
    rw [bloc_del t z τ hτ k hZ]
    exact hvb_zsmul_cast t hτ k (rhoH t (tupRng_del_subset k τ) (z (tupDel k τ)))
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  rw [← hvb_cast_sum t hτ Finset.univ
    (fun k : Fin (m + 3) => (-1 : R) ^ (k : ℕ) • rhoH t (tupRng_del_subset k τ) (z (tupDel k τ)))]
  rw [hzτ, hvb_cast_zero]

/-- The honest differential of the block cochain `yOfBlock b` on the `S`-block is the block
coboundary of `b`. -/
lemma yOfBlock_HCd (t : ι → R) {m : ℕ} {S : Finset ι} (z : HCX t (m + 1))
    (b : (Fin (m + 1) → ↥S) → chartRing t S)
    (hb : ∀ g : Fin (m + 1) → ↥S, ¬ Function.Surjective g → b g = 0)
    (hcob : ∀ x : Fin (m + 2) → ↥S,
      ∑ k : Fin (m + 2), (-1 : ℤ) ^ (k : ℕ) • b (x ∘ Fin.succAbove k) = bloc t z S x)
    (τ : Fin (m + 2) → ι) (hτ : tupRng τ = S) :
    (HCd t m (yOfBlock t S b)) τ = z τ := by
  have h1 : ∀ i : Fin (m + 2),
      (-1 : R) ^ (i : ℕ) • rhoH t (tupRng_del_subset i τ) (yOfBlock t S b (tupDel i τ))
        = hτ.symm ▸ ((-1 : R) ^ (i : ℕ) • b (corestr S τ hτ ∘ Fin.succAbove i)) := by
    intro i
    rw [yOfBlock_del t S b hb τ hτ i]
    exact (hvb_cast_smul t hτ.symm ((-1 : R) ^ (i : ℕ)) _).symm
  rw [HCd_apply, Finset.sum_congr rfl (fun i _ => h1 i)]
  rw [← hvb_cast_sum t hτ.symm Finset.univ
    (fun i : Fin (m + 2) => (-1 : R) ^ (i : ℕ) • b (corestr S τ hτ ∘ Fin.succAbove i))]
  rw [Finset.sum_congr rfl (fun (i : Fin (m + 2)) _ =>
    hvb_smul_eq_zsmul t i (b (corestr S τ hτ ∘ Fin.succAbove i)))]
  rw [hcob (corestr S τ hτ), bloc_corestr t z τ hτ, hvb_cast_symm]

end Block

/-- **The vanishing block of the image-size filtration.**  If `S.card = j ≤ m+1`, `z` is a cocycle
of the honest chart Čech complex in degree `m+1` vanishing on tuples whose range has fewer than `j`
elements, then there is a cochain `y` in degree `m` supported exactly on the tuples of range `S`
whose differential reproduces `z` on the `S`-block. -/
lemma honestVanishingBlock {ι : Type a} [DecidableEq ι] {R : Type a} [CommRing R] (t : ι → R)
    {S : Finset ι} {j m : ℕ} (hS : S.card = j) (hj : j ≤ m + 1)
    (z : HCX t (m + 1)) (hsupp : SuppAbove j z) (hz : HCd t (m + 1) z = 0) :
    ∃ y : HCX t m,
      (∀ σ : Fin (m + 1) → ι, tupRng σ ≠ S → y σ = 0) ∧
      ∀ τ : Fin (m + 2) → ι, tupRng τ = S → (HCd t m y) τ = z τ := by
  classical
  haveI : Fintype ↥S := S.fintypeCoeSort
  have hcard : Fintype.card ↥S = j := by rw [Fintype.card_coe]; exact hS
  -- `z` vanishes on all tuples whose range has fewer elements than `S`
  have hZ : ∀ σ : Fin (m + 2) → ι, (tupRng σ).card < S.card → z σ = 0 := fun σ hσ =>
    hsupp σ (by rw [← hS]; exact hσ)
  -- the `S`-block of `z` is an `M`-valued supported cocycle on `↥S`
  have ha_supp : ∀ g : Fin (m + 2) → ↥S, ¬ Function.Surjective g → bloc t z S g = 0 := by
    intro g hg
    rw [bloc_apply]
    exact dif_neg (fun h => hg ((tupRng_toI_eq_iff S g).mp h))
  have ha_cob : ∀ x : Fin (m + 3) → ↥S,
      ∑ k : Fin (m + 3), (-1 : ℤ) ^ (k : ℕ) • bloc t z S (x ∘ Fin.succAbove k) = 0 := by
    intro x
    by_cases hx : Function.Surjective x
    · have hτ : tupRng (toI S x) = S := (tupRng_toI_eq_iff S x).mpr hx
      rw [← bloc_cocycle t z hz hZ (toI S x) hτ]
      exact Finset.sum_congr rfl (fun k _ => by
        rw [show corestr S (toI S x) hτ ∘ Fin.succAbove k = x ∘ Fin.succAbove k from
          congrArg (fun w : Fin (m + 3) → ↥S => w ∘ Fin.succAbove k) (corestr_toI S x hτ)])
    · refine Finset.sum_eq_zero (fun k _ => ?_)
      have hk : bloc t z S (x ∘ Fin.succAbove k) = 0 := by
        rw [bloc_apply]
        refine dif_neg (fun h => ?_)
        have h2 : (tupRng (toI S (x ∘ Fin.succAbove k))).card ≤ (tupRng (toI S x)).card := by
          rw [toI_comp_succAbove]
          exact Finset.card_le_card (tupRng_del_subset k (toI S x))
        have h3 : (tupRng (toI S x)).card < S.card := card_tupRng_toI_lt_of_not_surjective S hx
        rw [h] at h2
        omega
      rw [hk]
      simp
  -- acyclicity of the surjection complex on `S` in degree `m+1` (`|S| = j ≤ m+1`)
  obtain ⟨b, hb_supp, hb_cob⟩ :=
    Work.DSEQ0.surj_tuple_vanishing (ι := ↥S) (M := chartRing t S) (m + 1)
      (by rw [hcard]; exact hj) (bloc t z S) ha_supp ha_cob
  refine ⟨yOfBlock t S b, ?_, ?_⟩
  · intro σ hσ
    rw [yOfBlock_apply]
    exact dif_neg hσ
  · intro τ hτ
    exact yOfBlock_HCd t z b hb_supp hb_cob τ hτ

end Work.DSM5b
