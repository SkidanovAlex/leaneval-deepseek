import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic

namespace Work.CORE3

open Subgroup
open Work.GW2

/-- Design pass 4 §1 (`_design_gw/Core4.lean`), verbatim: local control gives a Sylow subgroup.
`R` is a nontrivial Sylow `r`-subgroup of `H` (`¬ r ∣ R.relIndex H`) and every nontrivial
subgroup of `R` has its normalizer inside `H`; then `R` is Sylow in `G`, i.e. `r ∤ |G : R|`.
Used for `(|K|, |G:H|) = 1` in the Theorem C application (subcase `Ĥ = H`), with `R = O_r(U)`.

Proof: if `r ∣ R.index` then a Sylow `r`-subgroup `P` of `G` with `R ≤ P` satisfies `R < P`
(proper `r`-subgroups of a finite `r`-group grow in their normalizer), so
`R < N_P(R) ≤ N_G(R) ≤ H` by `hN` at `X = R`, giving a strictly larger `r`-subgroup of `H`,
i.e. `r ∣ R.relIndex H` — contradiction. -/
theorem SylowFromLocalControl (G : Type) [Group G] [Finite G] (r : ℕ) [Fact r.Prime]
    (H R : Subgroup G) (hRH : R ≤ H) (hR : R ≠ ⊥) (hp : IsPGroup r R)
    (hSyl : ¬ r ∣ R.relIndex H)
    (hN : ∀ X : Subgroup G, X ≠ ⊥ → X ≤ R → normalizer (X : Set G) ≤ H) :
    ¬ r ∣ R.index := by
  intro hdiv
  -- A Sylow `r`-subgroup `P` of `G` containing `R`.
  obtain ⟨P, hRP⟩ := hp.exists_le_sylow
  -- `R` is a proper subgroup of `P`.
  have hRPne : R ≠ (P : Subgroup G) := by
    intro heq
    exact Sylow.not_dvd_index P (heq ▸ hdiv)
  have hltP : R < (P : Subgroup G) := lt_of_le_of_ne hRP hRPne
  -- Work inside the `r`-group `P`, where `R` is proper, hence grows in its normalizer.
  have hRsub_ne_top : R.subgroupOf (P : Subgroup G) ≠ ⊤ := by
    intro htop
    rw [Subgroup.subgroupOf_eq_top] at htop
    exact hRPne (le_antisymm hRP htop)
  have hRsub_lt : R.subgroupOf (P : Subgroup G) < ⊤ :=
    lt_top_iff_ne_top.mpr hRsub_ne_top
  haveI : Group.IsNilpotent ↥(P : Subgroup G) := P.isPGroup'.isNilpotent
  have hnc : NormalizerCondition ↥(P : Subgroup G) :=
    Group.normalizerCondition_of_isNilpotent
  have hlt' : R.subgroupOf (P : Subgroup G) <
      Subgroup.normalizer (R.subgroupOf (P : Subgroup G) : Set ↥(P : Subgroup G)) :=
    hnc _ hRsub_lt
  -- Identify that normalizer with `N_G(R) ∩ P`.
  have hnorm : Subgroup.normalizer (R.subgroupOf (P : Subgroup G) : Set ↥(P : Subgroup G))
      = (Subgroup.normalizer (R : Set G)).subgroupOf (P : Subgroup G) :=
    (Subgroup.subgroupOf_normalizer_eq hRP).symm
  set M : Subgroup G := Subgroup.normalizer (R : Set G) ⊓ (P : Subgroup G) with hM
  have hRM : R ≤ M := by
    rw [hM]; exact le_inf Subgroup.le_normalizer hRP
  have hMP : M ≤ (P : Subgroup G) := by rw [hM]; exact inf_le_right
  have hMH : M ≤ H := by
    rw [hM]; exact inf_le_left.trans (hN R hR le_rfl)
  have hMapR : Subgroup.map (P : Subgroup G).subtype (R.subgroupOf (P : Subgroup G)) = R := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hRP]
  have hMapN : Subgroup.map (P : Subgroup G).subtype
      (Subgroup.normalizer (R.subgroupOf (P : Subgroup G) : Set ↥(P : Subgroup G))) = M := by
    rw [hnorm, hM, Subgroup.subgroupOf_map_subtype]
  -- `R` is a proper subgroup of `M`.
  have hne : R ≠ M := by
    intro hEq
    have hmap : Subgroup.map (P : Subgroup G).subtype (R.subgroupOf (P : Subgroup G)) =
        Subgroup.map (P : Subgroup G).subtype
          (Subgroup.normalizer (R.subgroupOf (P : Subgroup G) : Set ↥(P : Subgroup G))) := by
      rw [hMapR, hMapN, hEq]
    have : R.subgroupOf (P : Subgroup G)
        = Subgroup.normalizer (R.subgroupOf (P : Subgroup G) : Set ↥(P : Subgroup G)) :=
      Subgroup.map_injective (Subgroup.subtype_injective (P : Subgroup G)) hmap
    exact (ne_of_lt hlt') this
  have hltRM : R < M := lt_of_le_of_ne hRM hne
  -- `M` is an `r`-group, so the index of `R` in `M` is divisible by `r`.
  have hMp : IsPGroup r M := IsPGroup.to_le (K := (P : Subgroup G)) P.isPGroup' hMP
  have hrelM : r ∣ R.relIndex M := by
    obtain ⟨n, hn⟩ := hMp.index (R.subgroupOf M)
    have hneidx : (R.subgroupOf M).index ≠ 1 := by
      intro h1
      rw [Subgroup.index_eq_one] at h1
      rw [Subgroup.subgroupOf_eq_top] at h1
      exact hne (le_antisymm hRM h1)
    have hdvd : r ∣ (R.subgroupOf M).index := by
      cases n with
      | zero => exact absurd (hn.trans (pow_zero r)) hneidx
      | succ k =>
          rw [hn]
          exact ⟨r ^ k, by rw [pow_succ, mul_comm]⟩
    exact hdvd
  -- Hence `r ∣ |H : R|`, contradicting the hypothesis.
  exact hSyl (by
    rw [← Subgroup.relIndex_mul_relIndex R M H hRM hMH]
    exact hrelM.mul_right _)

end Work.CORE3
