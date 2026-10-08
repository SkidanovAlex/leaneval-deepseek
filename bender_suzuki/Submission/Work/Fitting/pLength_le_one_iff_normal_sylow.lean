import Mathlib
import Submission.Work.Fitting.Defs
import Submission.Work.Fitting.pLength_le_iff
import Submission.Work.Fitting.pCoreSeries_three
import Submission.Work.Fitting.piCore_eq_top_iff
import Submission.Work.Fitting.pCore_le_sylow
import Submission.Work.Fitting.pPrimePCore_map_eq
import Submission.Work.Fitting.fitting_eq_iSup_pCore

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Fitting.pLength_le_one_iff_normal_sylow`

For a finite `p`-solvable group `G` with `p` prime, the `p`-length is at most one exactly
when the quotient `G/O_{p'}(G)` has a normal Sylow `p`-subgroup.

Both conditions turn out to be equivalent to "`G/O_{p',p}(G)` is a `p'`-group":

* `pLength p G ≤ 1` unfolds, via `pLength_le_iff` and `pCoreSeries_three`, to
  `O_{p'}(G/O_{p',p}(G)) = ⊤`, and `O_π(H) = ⊤` holds iff `|H|` is a `π`-number
  (`piCore_eq_top_iff`);
* `G/O_{p'}(G)` has a normal Sylow `p`-subgroup iff `O_p(G/O_{p'}(G))` has index prime to
  `p` (`exists_normal_sylow_iff_not_dvd_index_pCore`), and the corresponding quotient is
  `G/O_{p',p}(G)` by the third isomorphism theorem (`pPrimePCore_map_eq`).
-/

set_option linter.style.haveILetI false

noncomputable section

open Classical

namespace Work.Fitting

/-- For a prime `p`, a number all of whose prime divisors are `≠ p` is exactly a number that
is not divisible by `p`. -/
theorem isPiNat_ne_iff_not_dvd {p : ℕ} (hp : p.Prime) (n : ℕ) :
    IsPiNat (fun q => q ≠ p) n ↔ ¬ p ∣ n := by
  constructor
  · intro h hd
    exact (h p hp hd) rfl
  · intro h q hq hqd hqp
    exact h (hqp ▸ hqd)

/-- The preimage of a subgroup under a surjective homomorphism is everything exactly when the
subgroup is everything. -/
theorem comap_eq_top_iff_of_surjective {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) (N : Subgroup H) :
    Subgroup.comap f N = ⊤ ↔ N = ⊤ := by
  constructor
  · intro h
    have hrange : N ≤ f.range := by rw [MonoidHom.range_eq_top.mpr hf]; exact le_top
    have hmap := Subgroup.map_comap_eq_self hrange
    rw [h, Subgroup.map_top_of_surjective f hf] at hmap
    exact hmap.symm
  · rintro rfl
    exact Subgroup.comap_top f

/-- A finite group has a normal Sylow `p`-subgroup if and only if the index of `O_p(G)` is not
divisible by `p`.

* If `P` is a normal Sylow `p`-subgroup then `O_p(G) ≤ P` (every normal `p`-subgroup lies in
  every Sylow), and `P ≤ O_p(G)` because `P` is a normal `p`-subgroup, so `O_p(G) = P` and
  `[G : O_p(G)] = [G : P]` is prime to `p` (`Sylow.not_dvd_index`).
* Conversely if `[G : O_p(G)]` is prime to `p` then, `O_p(G)` being a `p`-subgroup
  (`isPGroup_pCore`), it is a Sylow subgroup (`IsPGroup.toSylow`), and it is normal. -/
theorem exists_normal_sylow_iff_not_dvd_index_pCore (p : ℕ) (G : Type*) [Group G] [Finite G]
    [Fact p.Prime] :
    (∃ P : Sylow p G, (P : Subgroup G).Normal) ↔ ¬ p ∣ Nat.card (G ⧸ pCore p G) := by
  constructor
  · rintro ⟨P, hP⟩
    haveI : (P : Subgroup G).Normal := hP
    have hle1 : pCore p G ≤ (P : Subgroup G) := pCore_le_sylow P
    have hle2 : (P : Subgroup G) ≤ pCore p G :=
      le_piCore (π := fun q => q = p) hP
        ((isPiNat_prime_iff_isPGroup Fact.out (P : Subgroup G)).mpr P.isPGroup')
    have heq : pCore p G = (P : Subgroup G) := le_antisymm hle1 hle2
    rw [heq, ← Subgroup.index_eq_card (P : Subgroup G)]
    exact P.not_dvd_index
  · intro h
    have hpg : IsPGroup p ↥(pCore p G) := isPGroup_pCore (p := p) Fact.out
    have hidx : ¬ p ∣ (pCore p G).index := by
      rwa [Subgroup.index_eq_card]
    refine ⟨hpg.toSylow hidx, ?_⟩
    rw [IsPGroup.toSylow_coe]
    infer_instance

theorem pLength_le_one_iff_normal_sylow (p : ℕ) (G : Type*) [Group G] [Finite G] [Fact p.Prime]
    [Work.Fitting.IsPSolvable p G] :
    Work.Fitting.pLength p G ≤ 1 ↔
      ∃ P : Sylow p (G ⧸ Work.Fitting.pPrimeCore p G),
        (P : Subgroup (G ⧸ Work.Fitting.pPrimeCore p G)).Normal := by
  haveI hfin1 : Finite (G ⧸ pPrimeCore p G) :=
    Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  haveI hfin2 : Finite (G ⧸ pPrimePCore p G) :=
    Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  -- The `p`-length is at most one exactly when `G/O_{p',p}(G)` is a `p'`-group.
  have hL : pLength p G ≤ 1 ↔ ¬ p ∣ Nat.card (G ⧸ pPrimePCore p G) := by
    have h1 : pLength p G ≤ 1 ↔ pCoreSeries p G 3 = ⊤ := by
      have h := pLength_le_iff p G (inferInstance : IsPSolvable p G) 1
      simpa using h
    rw [h1, pCoreSeries_three,
      comap_eq_top_iff_of_surjective _ (QuotientGroup.mk'_surjective _)]
    change piCore (fun q => q ≠ p) (G ⧸ pPrimePCore p G) = ⊤ ↔
      ¬ p ∣ Nat.card (G ⧸ pPrimePCore p G)
    rw [piCore_eq_top_iff]
    exact isPiNat_ne_iff_not_dvd Fact.out _
  -- `G/O_{p',p}(G) ≃* (G/O_{p'}(G))/O_p(G/O_{p'}(G))`.
  have hcard : Nat.card (G ⧸ pPrimePCore p G) =
      Nat.card ((G ⧸ pPrimeCore p G) ⧸ pCore p (G ⧸ pPrimeCore p G)) := by
    have hsub : Subgroup.map (QuotientGroup.mk' (pPrimeCore p G)) (pPrimePCore p G) =
        pCore p (G ⧸ pPrimeCore p G) := pPrimePCore_map_eq p G
    have e2 := QuotientGroup.quotientQuotientEquivQuotient (pPrimeCore p G) (pPrimePCore p G)
      (pPrimeCore_le_pPrimePCore p G)
    have e1 := QuotientGroup.quotientMulEquivOfEq hsub
    exact Nat.card_congr (e2.symm.trans e1).toEquiv
  -- `G/O_{p'}(G)` has a normal Sylow `p`-subgroup iff `O_p(G/O_{p'}(G))` has `p'`-index.
  have hR : (∃ P : Sylow p (G ⧸ pPrimeCore p G),
        (P : Subgroup (G ⧸ pPrimeCore p G)).Normal) ↔
      ¬ p ∣ Nat.card (G ⧸ pPrimePCore p G) := by
    rw [exists_normal_sylow_iff_not_dvd_index_pCore p (G ⧸ pPrimeCore p G), hcard]
  exact hL.trans hR.symm

end Work.Fitting
