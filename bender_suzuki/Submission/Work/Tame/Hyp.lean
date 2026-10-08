import Submission.Work.Tame.Chapter10

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Tame.Hyp` — Feit–Thompson Hypotheses 10.1 and 10.2

* `Hyp10_2` (p. 814): `𝔎_i` is a supporting subgroup of `L̂` and every induced character
  `θ̃ = Ind_{𝔎_i}^{𝔑_i} θ` of a non-principal irreducible `θ` of `𝔎_i` is a sum of irreducible
  characters of `𝔑_i`, all of the same degree and with the same multiplicity.
* `Hyp10_1` (p. 811): the main hypothesis of the coherence theorem.
-/

noncomputable section

open Classical
open scoped Pointwise

namespace Work.Tame

universe u

variable {X : Type u} [Group X] [Fintype X]

/-- The canonical isomorphism `𝔎.subgroupOf (N 𝔎) ≃* 𝔎` (`𝔎 ≤ N(𝔎)`). -/
noncomputable def subEquiv (K : Subgroup X) : ↥(K.subgroupOf (Lgrp K)) ≃* ↥K :=
  Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer

/-- **Feit–Thompson Hypothesis 10.2** (p. 814).  `Lhat` is tamely imbedded with system of
supporting subgroups `Hs`, and for the supporting subgroup `Hs i`: if `θ` is any non-principal
irreducible character of `𝔎_i` and `θ̃` is the character of `𝔑_i = N(𝔎_i)` induced by `θ`, then
`θ̃` is a sum of irreducible characters of `𝔑_i`, all of which have the same degree and occur with
the same multiplicity in `θ̃`.

(Formally, the *one-way* form of FT's sentence: there are `d, m : ℕ` such that every irreducible
`χ` of `𝔑_i` with `⟨θ̃, χ⟩ ≠ 0` has `χ(1) = d` and `⟨θ̃, χ⟩ = m`.  The earlier formalisation
required the converse as well — that *every* irreducible of degree `d` occurs, i.e. an `iff` — which
is strictly stronger than FT's hypothesis and is false in FT's own type-I setting: for
`X = C₇ ⋊ C₃`, `𝔎 = C₇`, `θ̃ = Ind θ` is *one* of the two irreducibles of `X` of degree `3`, while
the other one is not a constituent.  See `Submission/Work/TypeI/NOTES_FALSE_Hyp10_2.md` and the
lead's `Submission/Work/NOTES_LEAD_ft_hyp102.md` §1.) -/
structure Hyp10_2 (Lhat : Set X) (n : ℕ) (Hs : Fin n → Subgroup X) (i : Fin n) : Prop where
  /-- (i) `L̂` is tamely imbedded in `X` and `𝔎_i` is a supporting subgroup. -/
  tamely : IsTamelyImbedded Lhat n Hs
  /-- the non-degeneracy normalisation `𝔇 ≠ ∅ ∨ n = 0` of Definition 9.1 (see
  `Submission/Work/Tame/NOTES.md` §1). -/
  tameData : HasTameData Lhat n Hs
  /-- (ii) the induced characters of non-principal irreducible characters of `𝔎_i` are
  homogeneous: all their constituents have the same degree and the same multiplicity. -/
  induced_homogeneous :
    ∀ θ : ↥(Hs i) → ℂ, θ ∈ CharCore.Irr ↥(Hs i) → θ ≠ (1 : ↥(Hs i) → ℂ) →
      ∃ d m : ℕ, ∀ χ ∈ CharCore.Irr ↥(Lgrp (Hs i : Set X)),
        Coherence.cfInner
            (Induction.indFun ((Hs i).subgroupOf (Lgrp (Hs i : Set X)))
              (fun y => θ (subEquiv (Hs i) y))) χ ≠ 0 →
          χ 1 = (d : ℂ) ∧
          Coherence.cfInner
            (Induction.indFun ((Hs i).subgroupOf (Lgrp (Hs i : Set X)))
              (fun y => θ (subEquiv (Hs i) y))) χ = (m : ℂ)

/-- **Feit–Thompson Hypothesis 10.1** (p. 811).  `Lhat` is tamely imbedded with supporting
subgroups `Hs`; `𝓢_1, …, 𝓢_k` (`k ≥ 1`) are subsets of `𝓘(L̂)` whose union `𝓢` is a set of pairwise
orthogonal characters; each `𝓢_i` is coherent with isometry `τ_i` and is partitioned into sets
`𝓢_{ij}`, each of which either consists of at least two irreducible characters of the same degree
or is subcoherent in `𝓢`; the degrees of the members of `𝓢_i` are `ℓ_{is}·λ_{11}(1)` with
`1 = ℓ_{11} ≤ ℓ_{21} ≤ …` and `ℓ_{i1} | ℓ_{is}`; `λ_{11}` is irreducible; and the inequality
(10.2) holds. -/
structure Hyp10_1 (Lhat : Set X) (n : ℕ) (Hs : Fin n → Subgroup X) where
  /-- (i) `L̂` is tamely imbedded in `X`. -/
  tamely : IsTamelyImbedded Lhat n Hs
  /-- the non-degeneracy normalisation `𝔇 ≠ ∅ ∨ n = 0` of Definition 9.1 (see
  `Submission/Work/Tame/NOTES.md` §1); it is what makes the Dade map `τ` of (9.4) well defined. -/
  tameData : HasTameData Lhat n Hs
  /-- the number `k` of coherent sets. -/
  k : ℕ
  /-- (ii) `k ≥ 1`. -/
  hk : 1 ≤ k
  /-- (ii) `𝓢_i = {λ_{is} | 1 ≤ s ≤ n_i} ⊆ 𝓘(L̂)`. -/
  S : (i : Fin k) → Finset (↥(Lgrp Lhat) → ℂ)
  S_nonempty : ∀ i, (S i).Nonempty
  S_vchar : ∀ i, ∀ χ ∈ S i, CharCore.IsVChar χ
  S_vanish : ∀ i, ∀ χ ∈ S i, ∀ l : ↥(Lgrp Lhat), (l : X) ∉ Lhat → χ l = 0
  /-- (ii) the sets `𝓢_i` are the parts of a partition of `𝓢`, hence pairwise disjoint. -/
  S_disjoint : ∀ i j : Fin k, i ≠ j → Disjoint (S i) (S j)
  /-- (iii) `𝓢 = ⋃_i 𝓢_i` consists of pairwise orthogonal characters (all pairs of *distinct*
members, including within a single `𝓢_i`). -/
  orth : ∀ i j : Fin k, ∀ χ ∈ S i, ∀ ψ ∈ S j, χ ≠ ψ → Coherence.cfInner χ ψ = 0
  /-- (iv) `𝓢_i` is coherent. -/
  τi_coherent : ∀ i, FTCoherent Lhat n Hs (S i)
  /-- (iv) `τ_i` is the isometry witnessing the coherence of `𝓢_i`. -/
  τi : (i : Fin k) → (↥(Lgrp Lhat) → ℂ) →ₗ[ℤ] (X → ℂ)
  τi_ext : ∀ i, IsExtension Lhat n Hs (S i) (τi i)
  /-- (iv) the number of parts of the partition of `𝓢_i`. -/
  npart : (i : Fin k) → ℕ
  /-- (iv) the parts `𝓢_{ij}`. -/
  part : (i : Fin k) → Fin (npart i) → Finset (↥(Lgrp Lhat) → ℂ)
  part_sub : ∀ i j, part i j ⊆ S i
  part_nonempty : ∀ i j, (part i j).Nonempty
  part_disjoint : ∀ i (j j' : Fin (npart i)), j ≠ j' → Disjoint (part i j) (part i j')
  part_cover : ∀ i, Finset.biUnion Finset.univ (part i) = S i
  /-- (iv) each part is either a set of at least two irreducible characters of the same degree, or
  is subcoherent in `𝓢` *for some* extension `τ'` of `τ` to it (the isometry of a block need not be
  the `τ_i` on the nose: extensions are only unique up to a `±` swap on a two-element block, by
  Lemma 10.1).  With this form the fields `τi i` (`i ≥ 2`) are constrained only by `τi_ext`, so
  Theorem 10.1 in this form (`ft10_1`) asserts coherence only; the source's anchored condition
  `τ_{ij} = τ_i` is `PartHyp h`, used by `ft10_1_of_source`. -/
  part_irr_or_sub : ∀ i j,
    (((part i j : Set (↥(Lgrp Lhat) → ℂ)) ⊆ CharCore.Irr ↥(Lgrp Lhat)) ∧ 2 ≤ (part i j).card ∧
        ∀ χ ∈ part i j, ∀ ψ ∈ part i j, χ 1 = ψ 1) ∨
      (∃ τ' : (↥(Lgrp Lhat) → ℂ) →ₗ[ℤ] (X → ℂ),
        Subcoherent Lhat n Hs (Finset.biUnion Finset.univ S) (part i j) τ')
  /-- (v) the distinguished member `λ_{i1}` of `𝓢_i`. -/
  first : (i : Fin k) → ↥(S i)
  /-- (v) the integers `ℓ_{is}`. -/
  ell : (i : Fin k) → ↥(S i) → ℕ
  ell_pos : ∀ i s, 1 ≤ ell i s
  ell_zero : ell ⟨0, hk⟩ (first ⟨0, hk⟩) = 1
  ell_mono : ∀ i j : Fin k, i ≤ j → ell i (first i) ≤ ell j (first j)
  /-- (v) `λ_{is}(1) = ℓ_{is}·λ_{11}(1)`. -/
  ell_deg : ∀ i (s : ↥(S i)),
    ((s : ↥(S i)) : ↥(Lgrp Lhat) → ℂ) 1 =
      (ell i s : ℂ) *
        (((first ⟨0, hk⟩ : ↥(S ⟨0, hk⟩)) : ↥(Lgrp Lhat) → ℂ) 1)
  ell_dvd : ∀ i (s : ↥(S i)), ell i (first i) ∣ ell i s
  /-- (vi) `λ_{11}` is an irreducible character of `𝔏`. -/
  lam11_irr : (((first ⟨0, hk⟩ : ↥(S ⟨0, hk⟩)) : ↥(Lgrp Lhat) → ℂ)) ∈
    CharCore.Irr ↥(Lgrp Lhat)
  /-- (vii) the inequality (10.2). -/
  ineq : ∀ (m : ℕ) (hm1 : 1 < m) (hm2 : m ≤ k),
    (∑ i : Fin k,
        if (i : ℕ) < m - 1 then
          ∑ s : ↥(S i), (((ell i s : ℝ)) ^ 2 / rwt ((s : ↥(S i)) : ↥(Lgrp Lhat) → ℂ))
        else 0)
      > 2 * (ell ⟨m - 1, by omega⟩ (first ⟨m - 1, by omega⟩))

end Work.Tame
