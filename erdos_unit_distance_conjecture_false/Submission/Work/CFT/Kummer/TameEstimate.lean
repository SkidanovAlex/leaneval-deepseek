import Mathlib
import Submission.Work.CFT.Kummer.Defs
import Submission.Work.CFT.Kummer.Hypotheses
import Submission.Work.CFT.Kummer.finrank_range_le_of_sum_invariants

/-!
# The Hajir–Maire–Ramakrishna relation-rank bound from Kummer theory and Hilbert reciprocity

This file derives, from the Kummer-theoretic input `Work.CFT.Kummer.ShafarevichTame` (facts (a) and
(b) of Koch's Chapter 11 together with the local data and Hilbert reciprocity), the relation-rank
bound of Hajir–Maire–Ramakrishna, *Cutting towers of number fields*, §"Some set up":

`r(G_S) = dim_{𝔽_p} H²(G_S,𝔽_p) ≤ dim_{𝔽_p} 𝓒_S + (|S| - δ_{K,p})` (for tame `S`).

The ingredients are the localisation sequence
`0 → Ш²_S = ker loc → H²(G_S,𝔽_p) → ∏_{v∈S} H²(G_{K_v},𝔽_p)`
together with

* the injection `Ш²_S ↪ 𝓒_S` (Koch, Ch. 11, i.e. fact (a));
* Hilbert reciprocity, which puts the image of `loc` in the hyperplane of vectors whose local
  invariants sum to zero, whence `dim (range loc) ≤ |S| - δ_{K,p}`
  (`Work.CFT.Kummer.finrank_range_le_of_sum_invariants`).

## Main results

* `Work.CFT.Kummer.finrank_H2Fp_le_kummerDual_add_card` — `dim H²(G_S,𝔽_p) ≤ dim 𝓒_S + (|S|-δ)`.
* `Work.CFT.Kummer.finrank_H2Fp_add_le_H1Fp_add` — the same converted through the H¹ rank formula
  (b): `dim H²(G_S,𝔽_p) + Σ_{v∈S}δ_{K_v,p} ≤ dim H¹(G_S,𝔽_p) + (r₁+r₂-1) + δ_{K,p} + (|S|-δ_{K,p})`,
  which for `S = ∅` is Shafarevich's estimate of `Work.CFT.Kummer.finrank_H2Fp_le_H1Fp_add`.
-/

open scoped nonZeroDivisors
open NumberField

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Work.CFT.Kummer

variable (K : Type*) [Field K] [NumberField K] (p : ℕ) (G : Type) [Group G]

variable [Fact p.Prime]

/-- The product `∏_{v∈S} H²(G_{K_v},𝔽_p)` of the local groups has dimension `Σ_{v∈S} δ_{K_v,p}`. -/
theorem finrank_pi_H2loc (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    [h : ShafarevichTame K p S G] :
    Module.finrank (ZMod p) ((v : {v // v ∈ S}) → (h.H2loc v : Type)) =
      ∑ v : {v // v ∈ S}, deltaLocal K p v.1 := by
  haveI := h.h2locFinite
  haveI : ∀ v : {v // v ∈ S}, Module.Free (ZMod p) (h.H2loc v : Type) :=
    fun v => Module.Free.of_divisionRing (ZMod p) (h.H2loc v)
  rw [Module.finrank_pi_fintype]
  exact Finset.sum_congr rfl fun v _ => h.finrank_H2loc v

/-- **Hilbert reciprocity bounds the local terms**: for tame `S`, the image of the localisation map
`H²(G_S,𝔽_p) → ∏_{v∈S}H²(G_{K_v},𝔽_p)` has `𝔽_p`-dimension at most `|S| - δ_{K,p}`. -/
theorem finrank_range_loc_le (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    [h : ShafarevichTame K p S G] :
    Module.finrank (ZMod p) (LinearMap.range h.loc) ≤ S.card - deltaK K p := by
  haveI := h.h2locFinite
  have hcard : Fintype.card {v // v ∈ S} = S.card := by
    rw [← Finset.card_attach]
    rfl
  rcases eq_or_ne (deltaK K p) 0 with hδ0 | hδ0
  · -- no reciprocity: the image lies in the product, of dimension `Σ δ_{K_v,p} ≤ |S|`
    rw [hδ0, Nat.sub_zero]
    refine le_trans (Submodule.finrank_le (LinearMap.range h.loc)) ?_
    rw [finrank_pi_H2loc K p G S]
    calc (∑ v : {v // v ∈ S}, deltaLocal K p v.1) ≤ ∑ _v : {v // v ∈ S}, 1 :=
          Finset.sum_le_sum fun v _ => deltaLocal_le_one K p v.1
      _ = Fintype.card {v // v ∈ S} := by simp
      _ = S.card := hcard
  · -- reciprocity applies: the image lies in the hyperplane of vanishing total invariant
    have hδ1 : deltaK K p = 1 := by
      have := deltaK_le_one K p
      omega
    have hle := finrank_range_le_of_sum_invariants (p := p) (ι := {v // v ∈ S})
      (M := H2Fp p G) (N := fun v => (h.H2loc v : Type)) h.loc h.inv
      (fun v => by rw [h.finrank_H2loc]; exact deltaLocal_le_one K p v.1)
      (fun v hv => by
        intro hzero
        have hinj := h.inv_injective v (by rw [← h.finrank_H2loc]; exact hv)
        rw [hzero] at hinj
        have hsub : Subsingleton (h.H2loc v : Type) := ⟨fun a b => hinj (by simp)⟩
        rw [Module.finrank_zero_of_subsingleton] at hv
        exact one_ne_zero hv.symm)
      (fun x => h.reciprocity hδ1 x)
    rw [hcard] at hle
    rw [hδ1]
    exact hle

/-- **The Hajir–Maire–Ramakrishna relation-rank bound**: `dim H²(G_S,𝔽_p) ≤ dim 𝓒_S + (|S|-δ)`,
i.e. `r(G_S) ≤ d_p 𝓒_S + |S| - δ_{K,p}` for tame `S`. -/
theorem finrank_H2Fp_le_kummerDual_add_card (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    [h : ShafarevichTame K p S G] :
    Module.finrank (ZMod p) (H2Fp p G) ≤
      Module.finrank (ZMod p) (kummerDual K p S) + (S.card - deltaK K p) := by
  have hrange := finrank_range_loc_le K p G S
  have hsha : Module.finrank (ZMod p) ↥(LinearMap.ker h.loc) ≤
      Module.finrank (ZMod p) (kummerDual K p S) :=
    LinearMap.finrank_le_finrank_of_injective h.sha_injective
  have hrk := LinearMap.finrank_range_add_finrank_ker h.loc
  omega

/-- **Shafarevich's estimate through the tame H¹ rank formula**: converting
`Work.CFT.Kummer.finrank_H2Fp_le_kummerDual_add_card` with fact (b),
`dim 𝓒_S + Σ_{v∈S}δ_{K_v,p} = dim H¹(G_S,𝔽_p) + δ_{K,p} + (r₁+r₂-1)`, gives
`dim H²(G_S,𝔽_p) + Σ_{v∈S}δ_{K_v,p} ≤ dim H¹(G_S,𝔽_p) + (r₁+r₂-1) + δ_{K,p} + (|S|-δ_{K,p})`.
For `S = ∅` this is Shafarevich's estimate `dim H²(G_∅) ≤ dim H¹(G_∅) + (r₁+r₂-1) + δ_{K,p}`
(`Work.CFT.Kummer.finrank_H2Fp_le_H1Fp_add`). -/
theorem finrank_H2Fp_add_le_H1Fp_add (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    [h : ShafarevichTame K p S G] :
    Module.finrank (ZMod p) (H2Fp p G) + (∑ v ∈ S, deltaLocal K p v) ≤
      Module.finrank (ZMod p) (H1Fp p G) + NumberField.Units.rank K + deltaK K p +
        (S.card - deltaK K p) := by
  have h1 := finrank_H2Fp_le_kummerDual_add_card K p G S
  have h2 := h.rank_formula
  omega

/-- The `S = ∅` case of the tame structure reproduces Shafarevich's estimate at `S = ∅`. -/
theorem finrank_H2Fp_le_H1Fp_add_of_tame_empty [h : ShafarevichTame K p ∅ G] :
    Module.finrank (ZMod p) (H2Fp p G) ≤
      Module.finrank (ZMod p) (H1Fp p G) + NumberField.Units.rank K + deltaK K p := by
  have h1 := finrank_H2Fp_add_le_H1Fp_add K p G ∅
  simpa using h1

end Work.CFT.Kummer
