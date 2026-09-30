import Mathlib
import Submission.Work.BW.mvpoly_local_regSeq
import Submission.Work.BW.regSeq_le_dim_of_ass
import Submission.Work.BW.regSeq_quotient
import Submission.Work.BW.unmixed_regSeq
import Submission.Work.BW.height_add_krullDim_quotient
import Submission.Work.BW.RB.exists_isRegular_ofList_le_prime


namespace Work.BW.RB

open Work.BW

/-!
# The dimension formula `ht p + dim (R ⧸ p) = dim R` for `R = ℂ[σ]_𝔪`, `𝔪` maximal

`R = ℂ[σ]_𝔪` (σ finite, 𝔪 maximal) is the local ring of a point of affine space; it is a regular
local ring, hence Cohen–Macaulay, so the dimension formula `dim (R ⧸ p) = dim R - ht p` holds for
every prime `p`.  Mathlib (pinned) has no Cohen–Macaulay theory, so the proof below uses the
elementary substitutes available in this workspace:

* `Work.BW.RB.exists_isRegular_ofList_le_prime`: `p` contains a regular sequence `f` with
  `(f).height = p.height`;
* `Ideal.mem_minimalPrimes_of_height_le`: then `p` is minimal over `(f)`;
* `Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes`
  (`Min ⊆ Ass` for `R ⧸ (f)`);
* `Work.BW.regSeq_quotient` (Rees): `R ⧸ (f)` carries a regular sequence of length `|σ| - ht p`;
* `Work.BW.regSeq_le_dim_of_ass` (Matsumura 17.2): every associated prime `P` of a module with a
  regular sequence of length `n` satisfies `n ≤ dim (A ⧸ P)`, which yields
  `|σ| - ht p ≤ dim (R ⧸ p)`;
* `Work.BW.height_add_krullDim_quotient`: the opposite inequality, valid in any commutative ring.
-/

/-- Assembly step: if `p` contains a regular sequence `f` with `ht (f) = ht p`, then
`ht p + dim (R ⧸ p) = dim R`. -/
private theorem height_add_ringKrullDim_quotient_eq_aux {σ : Type*} [Fintype σ]
    (𝔪 : Ideal (MvPolynomial σ ℂ)) [𝔪.IsMaximal]
    (p : Ideal (Localization.AtPrime 𝔪)) [p.IsPrime] {h : ℕ} (hp : p.height = h)
    (hex : ∃ f : List (Localization.AtPrime 𝔪), f.length = h ∧
      Ideal.ofList f ≤ p ∧ (Ideal.ofList f).height = h ∧
      RingTheory.Sequence.IsRegular (Localization.AtPrime 𝔪) f) :
    ((p.height : ℕ∞) : WithBot ℕ∞) + ringKrullDim (Localization.AtPrime 𝔪 ⧸ p)
      = ringKrullDim (Localization.AtPrime 𝔪) := by
  classical
  obtain ⟨f, hlen, hle, hht, hreg⟩ := hex
  obtain ⟨rs, hrslen, hrsmem, hrsreg⟩ := (mvpoly_local_regSeq 𝔪).1
  have hdimle : ringKrullDim (Localization.AtPrime 𝔪) ≤ ((Fintype.card σ : ℕ) : WithBot ℕ∞) :=
    (mvpoly_local_regSeq 𝔪).2
  have hheight_le : ((h : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime 𝔪) := by
    rw [← hp]; exact Ideal.height_le_ringKrullDim_of_isPrime
  have hle_n : h ≤ Fintype.card σ := by
    have h2 : (h : WithBot ℕ∞) ≤ (Fintype.card σ : WithBot ℕ∞) := by
      simpa using le_trans hheight_le hdimle
    exact_mod_cast h2
  haveI : p.FiniteHeight :=
    Ideal.finiteHeight_iff_lt.mpr (Or.inr (by rw [hp]; exact WithTop.coe_lt_top h))
  have hpmin : p ∈ (Ideal.ofList f).minimalPrimes :=
    Ideal.mem_minimalPrimes_of_height_le hle (by rw [hht, hp])
  have hass : p ∈ associatedPrimes (Localization.AtPrime 𝔪)
      (Localization.AtPrime 𝔪 ⧸ Ideal.ofList f) := by
    have h1 : p ∈ (Module.annihilator (Localization.AtPrime 𝔪)
        (Localization.AtPrime 𝔪 ⧸ Ideal.ofList f)).minimalPrimes := by
      rwa [Ideal.annihilator_quotient]
    exact Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes _ _ h1
  have hfmax : ∀ x ∈ f, x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime 𝔪) := by
    intro x hx
    exact IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top' (I := p))
      (hle (Ideal.subset_span hx))
  have hflen : f.length ≤ rs.length := by rw [hlen, hrslen]; exact hle_n
  obtain ⟨ss, hsslen, hssmax, hssreg⟩ :=
    regSeq_quotient (A := Localization.AtPrime 𝔪) rs f hrsmem hrsreg hfmax hreg hflen
  have hsslen' : ss.length = Fintype.card σ - h := by rw [hsslen, hrslen, hlen]
  have hlow : ((ss.length : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime 𝔪 ⧸ p) :=
    regSeq_le_dim_of_ass (Localization.AtPrime 𝔪 ⧸ Ideal.ofList f) ss hssmax hssreg p hass
  have hkey : ((Fintype.card σ : ℕ) : WithBot ℕ∞) ≤
      ((p.height : ℕ∞) : WithBot ℕ∞) + ringKrullDim (Localization.AtPrime 𝔪 ⧸ p) := by
    have h1 : ((Fintype.card σ : ℕ) : WithBot ℕ∞) =
        ((h : ℕ∞) : WithBot ℕ∞) + ((ss.length : ℕ∞) : WithBot ℕ∞) := by
      rw [hsslen', ← WithBot.coe_add, ← Nat.cast_add, Nat.add_sub_cancel' hle_n]
      simp
    rw [h1, ← hp]
    exact add_le_add le_rfl hlow
  have hup := height_add_krullDim_quotient p
  have hdim : ringKrullDim (Localization.AtPrime 𝔪) = ((Fintype.card σ : ℕ) : WithBot ℕ∞) :=
    le_antisymm hdimle (le_trans hkey hup)
  exact le_antisymm hup (by rw [hdim]; exact hkey)

theorem height_add_ringKrullDim_quotient_eq {σ : Type*} [Fintype σ]
    (𝔪 : Ideal (MvPolynomial σ ℂ)) [𝔪.IsMaximal]
    (p : Ideal (Localization.AtPrime 𝔪)) [p.IsPrime] :
    ((p.height : ℕ∞) : WithBot ℕ∞) + ringKrullDim (Localization.AtPrime 𝔪 ⧸ p)
      = ringKrullDim (Localization.AtPrime 𝔪) := by
  classical
  have hdimle : ringKrullDim (Localization.AtPrime 𝔪) ≤ ((Fintype.card σ : ℕ) : WithBot ℕ∞) :=
    (mvpoly_local_regSeq 𝔪).2
  have hne : p.height ≠ ⊤ := by
    refine fun htop => ?_
    have h1 : ((p.height : ℕ∞) : WithBot ℕ∞) ≤ ((Fintype.card σ : ℕ) : WithBot ℕ∞) :=
      le_trans (Ideal.height_le_ringKrullDim_of_isPrime (I := p)) hdimle
    rw [htop] at h1
    exact absurd h1 (not_le.mpr (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top (Fintype.card σ))))
  exact height_add_ringKrullDim_quotient_eq_aux 𝔪 p (ENat.natCast_toNat hne).symm
    (exists_isRegular_ofList_le_prime 𝔪 p (ENat.natCast_toNat hne).symm)

end Work.BW.RB
