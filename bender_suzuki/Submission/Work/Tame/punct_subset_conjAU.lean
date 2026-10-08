import Mathlib
import Submission.Work.Tame.Defs
import Submission.Work.Tame.mem_AU_iff

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Tame

open Classical

/-! ## Two elementary conjugation facts for `𝔏 = N(L̂)`

The proof of Feit–Thompson's Lemma 9.1 (support, first half) needs to know that the sets `𝔏₀` and
`𝔇` of Definition 9.1 are well behaved under conjugation *by an element of `𝔏 = N(L̂)`*: an element
of `L̂` which is conjugate in `X` to an element of `𝔇` is again in `𝔇`.  Definition 9.1 (i) is what
upgrades `X`-conjugacy of two elements of `L̂` to `𝔏`-conjugacy, so that these invariance facts
apply. -/

variable {X : Type*} [Group X] {Lhat : Set X}

/-- An element of `𝔏 = N(L̂)` permutes `L̂` by conjugation. -/
theorem mem_conj_Lgrp {g x : X} (hg : g ∈ Lgrp Lhat) : g * x * g⁻¹ ∈ Lhat ↔ x ∈ Lhat :=
  ((mem_Lgrp.mp hg) x).symm

/-- If `g ∈ 𝔏 = N(L̂)` and `C(g x g⁻¹) ≤ 𝔏`, then `C(x) ≤ 𝔏`; indeed
`C(g x g⁻¹) = g C(x) g⁻¹` and `𝔏` is normal in itself (we only need the inclusion). -/
theorem centralizer_conj_le_Lgrp {g x : X} (hg : g ∈ Lgrp Lhat)
    (hle : Subgroup.centralizer ({g * x * g⁻¹} : Set X) ≤ Lgrp Lhat) :
    Subgroup.centralizer ({x} : Set X) ≤ Lgrp Lhat := by
  intro y hy
  have hy' : g * y * g⁻¹ ∈ Subgroup.centralizer ({g * x * g⁻¹} : Set X) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    calc (g * y * g⁻¹) * (g * x * g⁻¹) = g * (y * x) * g⁻¹ := by group
      _ = g * (x * y) * g⁻¹ := by rw [hy]
      _ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
  have hyL : g * y * g⁻¹ ∈ Lgrp Lhat := hle hy'
  have hgy : g⁻¹ * (g * y * g⁻¹) ∈ Lgrp Lhat :=
    Subgroup.mul_mem (Lgrp Lhat) (Subgroup.inv_mem (Lgrp Lhat) hg) hyL
  have h1 : (g⁻¹ * (g * y * g⁻¹)) * g = y := by group
  rw [← h1]
  exact Subgroup.mul_mem (Lgrp Lhat) hgy hg

/-- A conjugate of an element of `𝔇` lying in `L̂` is again in `𝔇`.

This is the "standard fact" of the proof route: `l` and `l'` both lie in `L̂`, so Definition 9.1 (i)
makes them conjugate already in `𝔏 = N(L̂)`, and `𝔇` is invariant under `𝔏`-conjugation
(`mem_conj_Lgrp` for membership in `L̂`, `centralizer_conj_le_Lgrp` for containment of the
centralizer in `𝔏`, and `1 ∉ 𝔇` transported along conjugacy for `l' ≠ 1`). -/
theorem mem_Dset_of_isConj {n : ℕ} {Hs : Fin n → Subgroup X} (h : IsTamelyImbedded Lhat n Hs)
    {l l' : X} (hl : l ∈ Dset Lhat) (hl' : l' ∈ Lhat) (hc : IsConj l l') :
    l' ∈ Dset Lhat := by
  refine ⟨hl', ?_, ?_⟩
  · intro h1
    exact hl.2.1 (isConj_one_right.mp (h1 ▸ hc.symm))
  · intro hle
    obtain ⟨m, hm, hm'⟩ := h.conj hl.1 hl' hc
    exact hl.2.2 (centralizer_conj_le_Lgrp hm (hm' ▸ hle))

/-- Feit–Thompson Lemma 9.1 (support, first half).  Every non-identity element `l` of a tamely
imbedded set `Lhat` (Definition 9.1) is conjugate in `X` to an element of `AU` — the set
`⋃_{i=0}^{n} ⋃_{L ∈ 𝔏_i} 𝔄_L` of p. 805, where `𝔏_0` is the set `L0set` of Definition 9.1 and
`𝔄_L = ALofIdx …` is `{L}` for `i = 0` and `L(𝔎_i ∩ C(L))` for `i ≥ 1`.

Proof route: if `l ∈ L0set Lhat` then `l ∈ AU` itself (index `none`). Otherwise `l ∈ Dset Lhat`
and Definition 9.1(iii) furnishes a conjugate `l' ∈ Lhat` of `l` with
`C(l') = C_{𝔎_i}(l')·C_𝔏(l') ⊆ 𝔑_i` for some `i`, whence `l' ∈ Lset Lhat (Hs i)` and
`l' = l' * 1 ∈ AL l' (Hs i) ⊆ AU`.  (`l' ∈ Dset` needs the standard fact that `L0set` is invariant
under `X`-conjugation of elements of `Lhat`, which follows from Definition 9.1 (i) and the
invariance of `L0set` under conjugation by `𝔏 = Lgrp Lhat`.)  Note the statement needs no
non-degeneracy hypothesis: (iii) is not guarded by `Dset ≠ ∅`. -/
theorem punct_subset_conjAU {X : Type*} [Group X] {Lhat : Set X} {n : ℕ}
    {Hs : Fin n → Subgroup X} (h : IsTamelyImbedded Lhat n Hs) {l : X} (hl : l ∈ Lhat)
    (hl1 : l ≠ 1) : ∃ a ∈ AU Lhat n Hs, IsConj l a := by
  by_cases h0 : l ∈ L0set Lhat
  · exact ⟨l, mem_AU_iff.mpr (Or.inl h0), IsConj.refl l⟩
  · have hld : l ∈ Dset Lhat := ⟨hl, hl1, fun hc => h0 ⟨hl, hl1, hc⟩⟩
    obtain ⟨l', hl', hc, i, _hcent, hle⟩ := h.cover l hld
    have hl'd : l' ∈ Dset Lhat := mem_Dset_of_isConj h hld hl' hc
    refine ⟨l' * 1, mem_AU_iff.mpr (Or.inr ⟨i, l', ⟨hl'd, hle⟩, 1, (Hs i).one_mem, ?_, rfl⟩), ?_⟩
    · rw [mul_one, one_mul]
    · simpa using hc

end Work.Tame
