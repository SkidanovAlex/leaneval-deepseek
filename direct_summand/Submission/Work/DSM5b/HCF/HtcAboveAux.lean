import Mathlib
import Submission.Work.DSM5b.HCF.Complex
import Submission.Work.DSM5b.HCF.GenSurj

/-!
# Auxiliary material for the exactness of the honest complex above the top degree

For the graded piece `ℰ = Work.DSM5b.CoeffSys.exactlyCoeff 𝒜 k` of the size filtration (the
coefficient system supported on the subsets of size exactly `k`), the honest tuple complex `Htc ℰ`
decomposes, in every degree, as the product — over the `k`-element subsets `S₀` — of the
"surjection complex" on `S₀` (`Work.DSM5b.HCF.GSurjTerm S₀ (ℰ.M S₀)` with differential
`Work.DSM5b.HCF.gsurjD`).

This file contains the elementary ingredients of that decomposition:

* `htcAbove_res_eq_cast` — a restriction map along an equality of finsets is the corresponding transport of
  the coefficients;
* `htcAbove_res_of_subset_self` — a restriction map along a self-inclusion is the identity;
* `subsingleton_coeff_exactlyCoeff` — the coefficient module at a set of size `≠ k` is a
  subsingleton, so the blocks other than the `k`-element ones are zero;
* `zBlk` — the restriction of a cochain of the honest complex to the tuples with a given range;
* `zBlk_self` — the block cochain at a tuple which is its own range;
* `gsurjD_zBlk_at` / `gsurjD_zBlk_eq_zero` — the block of a cocycle is a cocycle of the surjection
  complex;
* `htcAbove_cast_apply_y` — the transport of a value of a family of cochains indexed by finsets along an
  equality of finsets;
* `htcD_eq_of_block_prims` — **the assembly**: given, for every `k`-element block, a primitive of
  the block of `z`, the cochain of the honest complex assembled from them has differential `z`.

Everything is stated for an arbitrary index type `ι` with decidable equality (no order needed).
-/

namespace Work.DSM5b.HCF

open Work.DSM5b

universe u

variable {R : Type u} [CommRing R] {ι : Type u} [DecidableEq ι]

/-- A restriction map along an *equality* of finsets is the corresponding transport of the
coefficients: `𝒜.res (le_of_eq h) x = h ▸ x`. -/
lemma htcAbove_res_eq_cast (𝒜 : CoeffSys R ι) {S T : Finset ι} (h : S = T) (x : 𝒜.M S) :
    𝒜.res (le_of_eq h) x = h ▸ x := by
  cases h
  exact (𝒜.res_congr x).trans (𝒜.res_self_apply x)

/-- A restriction map along a self-inclusion is the identity. -/
lemma htcAbove_res_of_subset_self (𝒜 : CoeffSys R ι) {S : Finset ι} (h : S ⊆ S) (x : 𝒜.M S) :
    𝒜.res h x = x := (𝒜.res_congr x).trans (𝒜.res_self_apply x)

/-- The coefficient module of `exactlyCoeff 𝒜 k` at a set of size `≠ k` is a subsingleton: the
coefficient system is supported on the subsets of size exactly `k`. -/
lemma subsingleton_coeff_exactlyCoeff (𝒜 : CoeffSys R ι) (k : ℕ) {S : Finset ι}
    (h : S.card ≠ k) : Subsingleton ((CoeffSys.exactlyCoeff 𝒜 k).M S) := by
  by_cases hlt : S.card < k
  · haveI : Subsingleton ↥((CoeffSys.sizeSubSys 𝒜 k).N S) := by
      rw [show (CoeffSys.sizeSubSys 𝒜 k).N S = ⊥ from if_neg (by omega)]
      infer_instance
    exact Function.Surjective.subsingleton (Submodule.mkQ_surjective _)
  · have hNk1 : (CoeffSys.sizeSubSys 𝒜 (k+1)).N S = ⊤ := if_pos (by omega)
    change Subsingleton (↥((CoeffSys.sizeSubSys 𝒜 k).N S) ⧸
      (Submodule.inclusion (CoeffSys.sizeSubSys_mono 𝒜 k S)).range)
    rw [Submodule.Quotient.subsingleton_iff]
    apply Submodule.eq_top_iff'.mpr
    intro y
    refine ⟨⟨y.1, by rw [hNk1]; exact Submodule.mem_top⟩, ?_⟩
    exact Subtype.ext rfl

/-- The **block** of a cochain of the honest complex of `exactlyCoeff 𝒜 k`: the cochain of the
surjection complex on `S₀` obtained by restricting `z` to the tuples with range `S₀`. -/
noncomputable def zBlk (𝒜 : CoeffSys R ι) (k m : ℕ)
    (z : (CoeffSys.exactlyCoeff 𝒜 k).Htc (m + 1)) (S₀ : Finset ι) :
    GSurjTerm S₀ ((CoeffSys.exactlyCoeff 𝒜 k).M S₀) (m + 1) :=
  fun τ => @Eq.ndrec (Finset ι) (tupRng τ.1)
    (fun S => (CoeffSys.exactlyCoeff 𝒜 k).M S) (z τ.1) S₀ τ.2

/-- The block cochain at a tuple which is its own range. -/
lemma zBlk_self (𝒜 : CoeffSys R ι) (k m : ℕ) (z : (CoeffSys.exactlyCoeff 𝒜 k).Htc (m + 1))
    (σ : Fin (m + 2) → ι) :
    zBlk 𝒜 k m z (tupRng σ) ⟨σ, rfl⟩ = z σ := rfl

/-- **The block of a cocycle is a cocycle of the surjection complex**, evaluated at a tuple `σ`
whose range has `k` elements.

Every summand `i` either keeps the range (`tupRng (tupDel i σ) = tupRng σ`, in which case the
restriction map of `exactlyCoeff` is the transport along that equality by `htcAbove_res_eq_cast`) or lands in
a coefficient module which is a subsingleton (`subsingleton_coeff_exactlyCoeff`), hence contributes
`0`. -/
lemma gsurjD_zBlk_at (𝒜 : CoeffSys R ι) (k m : ℕ)
    (z : (CoeffSys.exactlyCoeff 𝒜 k).Htc (m + 1))
    (hz : (CoeffSys.exactlyCoeff 𝒜 k).htcD (m + 1) z = 0)
    (σ : Fin (m + 3) → ι) (hσ : (tupRng σ).card = k) :
    gsurjD (R := R) (tupRng σ) ((CoeffSys.exactlyCoeff 𝒜 k).M (tupRng σ)) (m + 1)
      (zBlk 𝒜 k m z (tupRng σ)) ⟨σ, rfl⟩ = 0 := by
  rw [gsurjD_apply]
  have hzσ : ∑ i : Fin (m + 3), ((-1 : R) ^ (i : ℕ)) •
      (CoeffSys.exactlyCoeff 𝒜 k).res (tupRng_del_subset i σ) (z (tupDel i σ)) = 0 := by
    have h := congrFun hz σ
    simpa using h
  have hsum : (∑ i : Fin (m + 3), (if h : tupRng (tupDel i σ) = tupRng σ then
        ((-1 : R) ^ (i : ℕ)) • zBlk 𝒜 k m z (tupRng σ) ⟨tupDel i σ, h⟩ else 0))
      = ∑ i : Fin (m + 3), ((-1 : R) ^ (i : ℕ)) •
        (CoeffSys.exactlyCoeff 𝒜 k).res (tupRng_del_subset i σ) (z (tupDel i σ)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : tupRng (tupDel i σ) = tupRng σ
    · rw [dif_pos h]
      congr 1
      show h ▸ z (tupDel i σ)
        = (CoeffSys.exactlyCoeff 𝒜 k).res (tupRng_del_subset i σ) (z (tupDel i σ))
      rw [show (CoeffSys.exactlyCoeff 𝒜 k).res (tupRng_del_subset i σ) (z (tupDel i σ))
          = h ▸ z (tupDel i σ) from
        ((CoeffSys.exactlyCoeff 𝒜 k).res_congr (z (tupDel i σ))).trans
          (htcAbove_res_eq_cast (CoeffSys.exactlyCoeff 𝒜 k) h (z (tupDel i σ)))]
    · rw [dif_neg h]
      have hlt : (tupRng (tupDel i σ)).card < k := by
        by_contra hcon
        have hle : (tupRng (tupDel i σ)).card ≤ k := by
          rw [← hσ]; exact Finset.card_le_card (tupRng_del_subset i σ)
        have heq : (tupRng (tupDel i σ)).card = k := by omega
        exact h (Finset.eq_of_subset_of_card_le (tupRng_del_subset i σ) (by rw [heq, hσ]))
      haveI : Subsingleton ((CoeffSys.exactlyCoeff 𝒜 k).M (tupRng (tupDel i σ))) :=
        subsingleton_coeff_exactlyCoeff 𝒜 k (by omega)
      rw [Subsingleton.elim (z (tupDel i σ)) 0, map_zero, smul_zero]
  exact hsum.trans hzσ

/-- **The block of a cocycle is a cocycle of the surjection complex**, in the form indexed by the
finset `S₀` (obtained from `gsurjD_zBlk_at` by substituting the equality `tupRng σ = S₀`). -/
lemma gsurjD_zBlk_eq_zero (𝒜 : CoeffSys R ι) (k m : ℕ)
    (z : (CoeffSys.exactlyCoeff 𝒜 k).Htc (m + 1))
    (hz : (CoeffSys.exactlyCoeff 𝒜 k).htcD (m + 1) z = 0)
    (S₀ : Finset ι) (hS : S₀.card = k) :
    gsurjD (R := R) S₀ ((CoeffSys.exactlyCoeff 𝒜 k).M S₀) (m + 1) (zBlk 𝒜 k m z S₀) = 0 := by
  funext τ
  obtain ⟨σ, hσ⟩ := τ
  cases hσ
  exact gsurjD_zBlk_at 𝒜 k m z hz σ hS

/-- **Transport of the values of a family of cochains indexed by finsets**: if `y S hc` is a
cochain of the surjection complex on the finset `S`, then the transport of a value of `y S hc`
along an equality of finsets `e : S = S₀` is the corresponding value of `y S₀`.  (Both the
cardinality witnesses and the range witnesses are proofs of propositions, hence irrelevant; the
content is the substitution of the equal finsets.) -/
lemma htcAbove_cast_apply_y (𝒜 : CoeffSys R ι) (k m : ℕ)
    (y : (S₀ : Finset ι) → (hS : S₀.card = k) →
      GSurjTerm S₀ ((CoeffSys.exactlyCoeff 𝒜 k).M S₀) m)
    {S S₀ : Finset ι} (e : S = S₀) (hc : S.card = k) (hσ : S₀.card = k)
    (ρ : Fin (m + 1) → ι) (hρ : tupRng ρ = S) (hρ' : tupRng ρ = S₀) :
    e ▸ (y S hc ⟨ρ, hρ⟩) = y S₀ hσ ⟨ρ, hρ'⟩ := by
  cases e
  rw [Subsingleton.elim hc hσ]

/-- **The assembly of the exactness above the top degree.**  If, for every `k`-element subset `S₀`,
`y S₀ hS` is a primitive of the block of `z` (i.e. a cochain of the surjection complex on `S₀`
whose differential is the restriction of `z` to the tuples with range `S₀`), then the cochain of the
honest complex obtained by assembling the `y S₀ hS` over the blocks has differential `z`.

The only two facts used are `htcAbove_cast_apply_y` (the assembled cochain is well defined: the value at a
tuple with `k`-element range is the value of the block primitive at that tuple, irrespective of the
presentation of the range) and `subsingleton_coeff_exactlyCoeff` (a summand whose deletion lands
outside the `k`-element blocks is `0`). -/
theorem htcD_eq_of_block_prims (𝒜 : CoeffSys R ι) (k m : ℕ) (_hm : k ≤ m + 1)
    (z : (CoeffSys.exactlyCoeff 𝒜 k).Htc (m + 1))
    (hz : (CoeffSys.exactlyCoeff 𝒜 k).htcD (m + 1) z = 0)
    (y : (S₀ : Finset ι) → (hS : S₀.card = k) →
      GSurjTerm S₀ ((CoeffSys.exactlyCoeff 𝒜 k).M S₀) m)
    (hy : ∀ S₀ hS, gsurjD (R := R) S₀ ((CoeffSys.exactlyCoeff 𝒜 k).M S₀) m (y S₀ hS)
      = zBlk 𝒜 k m z S₀) :
    ∃ w : (CoeffSys.exactlyCoeff 𝒜 k).Htc m,
      (CoeffSys.exactlyCoeff 𝒜 k).htcD m w = z := by
  refine ⟨fun τ => if h : (tupRng τ).card = k then y (tupRng τ) h ⟨τ, rfl⟩ else 0, ?_⟩
  funext σ
  rw [CoeffSys.htcD_apply]
  show (∑ i : Fin (m + 2), ((-1 : R) ^ (i : ℕ)) •
      (CoeffSys.exactlyCoeff 𝒜 k).res (tupRng_del_subset i σ)
        (if h : (tupRng (tupDel i σ)).card = k then
          y (tupRng (tupDel i σ)) h ⟨tupDel i σ, rfl⟩ else 0)) = z σ
  by_cases hσ : (tupRng σ).card = k
  · have hspec : (∑ i : Fin (m + 2), (if h : tupRng (tupDel i σ) = tupRng σ then
          ((-1 : R) ^ (i : ℕ)) • y (tupRng σ) hσ ⟨tupDel i σ, h⟩ else 0)) = z σ := by
      have h := congrFun (hy (tupRng σ) hσ) ⟨σ, rfl⟩
      rw [gsurjD_apply] at h
      rwa [zBlk_self] at h
    have hgoal : (∑ i : Fin (m + 2), ((-1 : R) ^ (i : ℕ)) •
          (CoeffSys.exactlyCoeff 𝒜 k).res (tupRng_del_subset i σ)
            (if h : (tupRng (tupDel i σ)).card = k then
              y (tupRng (tupDel i σ)) h ⟨tupDel i σ, rfl⟩ else 0))
        = ∑ i : Fin (m + 2), (if h : tupRng (tupDel i σ) = tupRng σ then
          ((-1 : R) ^ (i : ℕ)) • y (tupRng σ) hσ ⟨tupDel i σ, h⟩ else 0) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : tupRng (tupDel i σ) = tupRng σ
      · have hc : (tupRng (tupDel i σ)).card = k := by rw [h]; exact hσ
        rw [dif_pos hc, dif_pos h]
        congr 1
        have hres : (CoeffSys.exactlyCoeff 𝒜 k).res (tupRng_del_subset i σ)
            (y (tupRng (tupDel i σ)) hc ⟨tupDel i σ, rfl⟩)
            = h ▸ y (tupRng (tupDel i σ)) hc ⟨tupDel i σ, rfl⟩ :=
          ((CoeffSys.exactlyCoeff 𝒜 k).res_congr
            (y (tupRng (tupDel i σ)) hc ⟨tupDel i σ, rfl⟩)).trans
            (htcAbove_res_eq_cast (CoeffSys.exactlyCoeff 𝒜 k) h
              (y (tupRng (tupDel i σ)) hc ⟨tupDel i σ, rfl⟩))
        exact hres.trans (htcAbove_cast_apply_y 𝒜 k m y h hc hσ (tupDel i σ) rfl h)
      · have hc : (tupRng (tupDel i σ)).card ≠ k := by
          intro hc
          exact h (Finset.eq_of_subset_of_card_le (tupRng_del_subset i σ) (by rw [hc, hσ]))
        rw [dif_neg hc, dif_neg h, map_zero, smul_zero]
    exact hgoal.trans hspec
  · haveI : Subsingleton ((CoeffSys.exactlyCoeff 𝒜 k).M (tupRng σ)) :=
      subsingleton_coeff_exactlyCoeff 𝒜 k hσ
    exact Subsingleton.elim _ _

end Work.DSM5b.HCF
