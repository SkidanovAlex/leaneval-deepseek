/-
# BMAX — Bender 1970, §1.7, first paragraph: `[O_q(B) ∩ A, O^q(F*(A))] = ⊥` for `q ∉ π(F(A))`

This file proves

  `Work.BMAX.commutator_pCoreIn_inf_pResidualIn_fstarIn`

the first paragraph of Bender 1970, §1.7 (= Bender 1981, Lemma 2.3, the input `(ii)`),
in the form requested by the `BMAX` consumer `Bender17DGroupMain.pCoreIn_inf_coatom_eq_bot`:
for a finite simple group `G`, a coatomic subgroup `A` which is a `D`-group, a proper
subgroup `B ≠ ⊤`, a subgroup `X ≤ F(A)` with `N_G(X) ∩ F*(A) ≤ B` (so that `X` witnesses
Bender's relation `A ⇝ B`) with `E(A) ≤ N_G(X)`, and a prime `q ∉ π(F(A))`,

  `[O_q(B) ∩ A, O^q(F*(A))] = 1`.

## Mathematics

Since `q ∉ π(F(A))`, `F(A)` is a `q'`-group and `E(A) = layer A` is perfect, so
`F*(A) ≤ O^q(F*(A))`; it therefore suffices to show that `Q := O_q(B) ∩ A` centralises both
halves `F(A)` and `E(A)` of `F*(A) = F(A)·E(A)`.

* **The layer half.** `E(A) ≤ N(X) ∩ F*(A) ≤ B`, so `E(A)` normalises `F(B) ∩ A`, which is
  solvable (it lies in the nilpotent `F(B)`); moreover `F(B) ∩ A ≤ A` normalises `E(A)`.  By
  the companion lemma `layerIn_le_centralizer_of_solvable`, an `E(A)`-invariant solvable
  subgroup of `A` is centralised by `E(A)`.  Hence `Q ≤ F(B) ∩ A` centralises `E(A)`.

* **The Fitting half.** `[O_q(B) ∩ A, F(A)] = ⊥`: this is the companion statement
  `commutator_pCoreIn_inf_fittingIn_eq_bot`.

Finally `F*(A) = F(A) ⊔ E(A)` and a subgroup centralising both halves centralises their join.

## Provenance of the two halves

The two companion modules are the two independent halves of the argument; each is stated
separately because the layer half holds for arbitrary `B` with `E(A) ≤ B` (it is Bender's
"`E(A)` centralises the `E(A)`-invariant solvable `F(B) ∩ A`" line), while the Fitting half is
the only place where the `D`-group hypothesis on `A` enters.
-/
import Mathlib
import Submission.Work.BMAX.D17Defs
import Submission.Work.BMAX.Defs
import Submission.Work.BMAX.Basic
import Submission.Work.BMAX.LayerCentralizesFitting
import Submission.Work.BMAX.centralizer_pResidualIn_witness_le
import Submission.Work.BMAX.fstarIn_le_pResidualIn_of_notMem_primesOf
import Submission.Work.BMAX.Bender17i_dedekind_basic
import Submission.Work.BMAX.commutator_pCoreIn_inf_fittingIn_eq_bot
import Submission.Work.BMAX.layerIn_le_centralizer_of_solvable

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.BMAX

open Subgroup

/-- **The layer half.**  `O_q(B) ∩ A` centralises `E(A) = layer A`, provided `E(A) ≤ B`.

`F(B) ∩ A` is solvable (`F(B)` is nilpotent) and is normalised by `E(A)` and by `A ⊇ F(B) ∩ A`,
so Bender's "an `E(A)`-invariant solvable subgroup is centralised by `E(A)`"
(`layerIn_le_centralizer_of_solvable`) applies; and `O_q(B) ∩ A ≤ F(B) ∩ A`. -/
theorem commutator_pCoreIn_inf_layerIn_eq_bot {G : Type} [Group G] [Finite G]
    (hG : IsSimpleGroup G) {A B X : Subgroup G} (hA : IsCoatom A) (hB : B ≠ ⊤)
    (hA_D : Work.GW2.IsDGroup A) (hX : X ≤ Work.GW2.fittingIn A)
    (hSB : Subgroup.normalizer (X : Set G) ⊓ Work.GW2.fstarIn A ≤ B)
    (hSl : Work.GW2.layerIn A ≤ Subgroup.normalizer (X : Set G))
    {q : ℕ} (hq : q.Prime) (hqpi : q ∉ Work.GW2.primesOf (Work.GW2.fittingIn A)) :
    ⁅Work.GW2.pCoreIn q B ⊓ A, Work.GW2.layerIn A⁆ = ⊥ := by
  haveI : Fact q.Prime := ⟨hq⟩
  -- `E(A) ≤ B`
  have hEB : Work.GW2.layerIn A ≤ B :=
    le_trans (le_inf hSl (Work.GW2.layerIn_le_fstarIn A)) hSB
  -- `L := F(B) ∩ A` is nilpotent, hence solvable
  set L : Subgroup G := Work.GW2.fittingIn B ⊓ A with hL
  haveI hLnil : Group.IsNilpotent ↥L := by
    have h1 : L ≤ Work.GW2.fittingIn B := inf_le_left
    haveI : Group.IsNilpotent ↥(Work.GW2.fittingIn B) := isNilpotent_fittingIn B
    haveI : Group.IsNilpotent ↥(L.subgroupOf (Work.GW2.fittingIn B)) := inferInstance
    exact (Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe h1)).mp inferInstance
  -- normality hypotheses of Bender's solvable-centraliser lemma
  have hLn : L ≤ Subgroup.normalizer ((Work.GW2.layerIn A : Subgroup G) : Set G) :=
    le_trans inf_le_right (le_normalizer_layerIn A)
  have hEn : Work.GW2.layerIn A ≤ Subgroup.normalizer (L : Set G) := by
    rw [hL]
    rw [Subgroup.le_normalizer_iff]
    intro y hy x hx
    obtain ⟨hxF, hxA⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have hyB : y ∈ B := hEB hy
      exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_fittingIn B hyB) x).mp hxF
    · have hyA : y ∈ A := Work.GW2.layerIn_le_self A hy
      have hyN : y ∈ Subgroup.normalizer (A : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro z
        exact ⟨fun hz => A.mul_mem (A.mul_mem hyA hz) (A.inv_mem hyA), fun hz => by
          have h := A.mul_mem (A.mul_mem (A.inv_mem hyA) hz) hyA
          rwa [show y⁻¹ * (y * z * y⁻¹) * y = z from by group] at h⟩
      exact (Subgroup.mem_normalizer_iff.mp hyN x).mp hxA
  have hEcen : Work.GW2.layerIn A ≤
      Subgroup.centralizer (L : Set G) :=
    layerIn_le_centralizer_of_solvable (inferInstance : Group.IsSolvable ↥L) hLn hEn
  -- `Q ≤ L`, and `[E(A), L] = 1`
  have hQL : Work.GW2.pCoreIn q B ⊓ A ≤ L :=
    le_inf (le_trans inf_le_left (Work.BMAX.pCoreIn_le_fittingIn B hq)) inf_le_right
  refine le_bot_iff.mp ?_
  calc ⁅Work.GW2.pCoreIn q B ⊓ A, Work.GW2.layerIn A⁆
      ≤ ⁅L, Work.GW2.layerIn A⁆ := Subgroup.commutator_mono hQL le_rfl
    _ = ⁅Work.GW2.layerIn A, L⁆ := Subgroup.commutator_comm _ _
    _ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hEcen

/-- **Bender 1970, §1.7, first paragraph.**  For a prime `q ∉ π(F(A))` the `q`-core of `B`
commutes with `O^q(F*(A))`, when `X ≤ F(A)` witnesses `N_G(X) ∩ F*(A) ≤ B` and
`E(A) ≤ N_G(X)`. -/
theorem commutator_pCoreIn_inf_pResidualIn_fstarIn {G : Type} [Group G] [Finite G]
    (hG : IsSimpleGroup G) (A B X : Subgroup G) (hA : IsCoatom A) (hB : B ≠ ⊤)
    (hA_D : Work.GW2.IsDGroup A) (hX : X ≤ Work.GW2.fittingIn A)
    (hSB : Subgroup.normalizer (X : Set G) ⊓ Work.GW2.fstarIn A ≤ B)
    (hSl : Work.GW2.layerIn A ≤ Subgroup.normalizer (X : Set G))
    (q : ℕ) (hq : q.Prime) (hqpi : q ∉ Work.GW2.primesOf (Work.GW2.fittingIn A)) :
    ⁅Work.GW2.pCoreIn q B ⊓ A, Work.BMAX.pResidualIn q (Work.GW2.fstarIn A)⁆ = ⊥ := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hElayer := commutator_pCoreIn_inf_layerIn_eq_bot hG hA hB hA_D hX hSB hSl hq hqpi
  have hFit := commutator_pCoreIn_inf_fittingIn_eq_bot hG hA hB hA_D hX hSB hSl hq hqpi
  -- centraliser form of the two halves
  have h1 : Work.GW2.pCoreIn q B ⊓ A ≤
      Subgroup.centralizer ((Work.GW2.fittingIn A : Subgroup G) : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hFit
  have h2 : Work.GW2.pCoreIn q B ⊓ A ≤
      Subgroup.centralizer ((Work.GW2.layerIn A : Subgroup G) : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hElayer
  -- hence `Q` centralises `F*(A) = F(A) ⊔ E(A)`
  have hstar : ⁅Work.GW2.pCoreIn q B ⊓ A, Work.GW2.fstarIn A⁆ = ⊥ := by
    rw [Work.GW2.fstarIn_eq_sup]
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hsub : (Work.GW2.fittingIn A ⊔ Work.GW2.layerIn A : Subgroup G) ≤
        Subgroup.centralizer ({x} : Set G) := by
      refine sup_le ?_ ?_
      · intro z hz
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        rw [Set.mem_singleton_iff] at hw
        subst hw
        exact ((Subgroup.mem_centralizer_iff.mp (h1 hx)) z hz).symm
      · intro z hz
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        rw [Set.mem_singleton_iff] at hw
        subst hw
        exact ((Subgroup.mem_centralizer_iff.mp (h2 hx)) z hz).symm
    exact (hsub hy x (Set.mem_singleton x)).symm
  -- `O^q(F*(A)) ≤ F*(A)`, so the commutator with `O^q(F*(A))` is even smaller
  have hres_le : Work.BMAX.pResidualIn q (Work.GW2.fstarIn A) ≤ Work.GW2.fstarIn A :=
    Work.BMAX.pResidualIn.le _
  exact le_bot_iff.mp
    (le_trans (Subgroup.commutator_mono le_rfl hres_le) (le_of_eq hstar))

end Work.BMAX
