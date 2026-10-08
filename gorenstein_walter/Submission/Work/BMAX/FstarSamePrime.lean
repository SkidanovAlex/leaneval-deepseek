/-
# BMAX — the `π`-equality step of Bender 1970, 1.6 (`Work.BMAX.FstarSamePrime`)

Target (exactly as requested):

`theorem Work.BMAX.FstarSamePrime (T : Work.GW2.LocalToolkit) (hmain : Work.GW2.Bender17MainProp) :
  Work.GW2.FstarSamePrimeProp`

i.e. *if `A ≠ B` are coatomic `D`-groups of a finite simple group `G` with `A ⇝ B` and
`B ⇝ A`, and both `F*(A) ≠ 1` and `F*(B) ≠ 1` are `p`-groups (`p` and `q` prime respectively),
then `p = q`.*

## The argument

Suppose `p ≠ q`.  Let `π = π(F(B)) = primesOf (fittingIn B)`.

1. A non-trivial `p`-group has no non-trivial quasisimple subgroup: a quasisimple group is
   perfect, and a non-trivial perfect group is never nilpotent, while every subgroup of a
   `p`-group is nilpotent (`IsPGroup.isNilpotent`) — note `layer X ≤ F*(X)`, so a quasisimple
   `E ≤ layer X` is a subgroup of the `p`-group `F*(X)`.  Hence `IsPGroup p (fstarIn A)`
   forces `layerIn A = ⊥`, i.e. `F*(A) = F(A)`; likewise on the `B` side.
2. Since `F(B) ≤ F*(B)` is a `q`-group, `π ⊆ {q}`; as `p ≠ q`, `p ∉ π`.  Since `F(A)` is a
   `p`-group, all prime divisors of `|F(A)|` lie in `πᶜ`, so `F(A) ≤ F_{πᶜ}(A)`.
3. Bender 1.7(ii) (`hmain`) applied to the pair `(B, A)` gives `F_{πᶜ}(A) ∩ B = ⊥`, hence
   `F(A) ∩ B = ⊥`.
4. On the other hand `A ⇝ B` gives `Z(F*(A)) ≤ B` (`BRel.zcenter_le`), while `Z(F*(A)) ≤
   F*(A) = F(A)`, so `Z(F*(A)) ≤ F(A) ∩ B = ⊥`.  But `F*(A) ≠ ⊥` is a `p`-group, so it has a
   non-trivial centre — a contradiction.  Hence `p = q`.
-/
import Mathlib
import Submission.Work.BMAX.Defs
import Submission.Work.BMAX.Basic

set_option linter.style.haveILetI false

namespace Work.BMAX

open Subgroup

variable {G : Type*} [Group G]

/-! ## 0. `IsPGroup` plumbing between `K` and its image in the ambient group -/

/-- `IsPGroup p ↥(fstarIn X)` for the ambient subgroup determines `IsPGroup p ↥(fstar X)`. -/
theorem isPGroup_fstar_of_isPGroup_fstarIn {X : Subgroup G} {p : ℕ}
    (h : IsPGroup p ↥(Work.GW2.fstarIn X)) : IsPGroup p ↥(Work.GW2.fstar X) :=
  IsPGroup.of_equiv h
    (Subgroup.equivMapOfInjective (Work.GW2.fstar X) X.subtype X.subtype_injective).symm

/-- `F(X) ≤ F*(X)` transports `IsPGroup` from `F*(X)` to `F(X)`. -/
theorem isPGroup_fitting_of_isPGroup_fstarIn {X : Subgroup G} {p : ℕ}
    (h : IsPGroup p ↥(Work.GW2.fstarIn X)) : IsPGroup p ↥(Work.GW2.fitting X) :=
  IsPGroup.to_le (isPGroup_fstar_of_isPGroup_fstarIn h) le_sup_left

/-! ## 1. A `p`-group has no non-trivial quasisimple subgroup -/

/-- If `F*(X)` is a `p`-group then `E(X) = 1`.  Indeed `layer X ≤ F*(X)`, so a quasisimple
`E ≤ layer X` is a subgroup of the `p`-group `F*(X)`, hence nilpotent; but a quasisimple group
is perfect and a non-trivial perfect group is never nilpotent. -/
theorem layerIn_eq_bot_of_isPGroup_fstarIn [Finite G] {X : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hP : IsPGroup p ↥(Work.GW2.fstarIn X)) : Work.GW2.layerIn X = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hlay : Work.GW2.layer X = ⊥ := by
    rw [Work.GW2.layer]
    refine eq_bot_iff.mpr (sSup_le ?_)
    rintro E ⟨hEn, hEq⟩
    have hEle : E ≤ Work.GW2.fstar X :=
      le_trans (le_sSup (show E ∈ {F : Subgroup ↥X | F.Normal ∧ Work.GW2.IsQuasisimple F}
          from ⟨hEn, hEq⟩))
        (show Work.GW2.layer X ≤ Work.GW2.fstar X from le_sup_right)
    have hPE : IsPGroup p ↥E := by
      have h1 : E.map X.subtype ≤ Work.GW2.fstarIn X := Subgroup.map_mono hEle
      exact IsPGroup.of_equiv (IsPGroup.to_le hP h1)
        (Subgroup.equivMapOfInjective E X.subtype X.subtype_injective).symm
    refine le_bot_iff.mpr ?_
    by_contra hne
    haveI : Nontrivial ↥E := (Subgroup.nontrivial_iff_ne_bot E).mpr hne
    haveI : Finite ↥E := inferInstance
    haveI : Group.IsPerfect ↥E := Subgroup.isPerfect_iff.mpr hEq.1
    exact (Group.IsPerfect.not_isNilpotent ↥E) (IsPGroup.isNilpotent hPE)
  rw [Work.GW2.layerIn, hlay, Subgroup.map_bot]

/-- `F*(K) = F(K)` once the layer of `K` is trivial. -/
theorem fstarIn_eq_fittingIn_of_layerIn_eq_bot {K : Subgroup G} (hL : Work.GW2.layerIn K = ⊥) :
    Work.GW2.fstarIn K = Work.GW2.fittingIn K := by
  simp [Work.GW2.fstarIn_eq_sup K, hL]

/-! ## 2. The centre of a non-trivial `p`-group is non-trivial -/

/-- `Work.GW2.zcenterIn K` is the image of the centre of the group `↥K`. -/
theorem zcenterIn_eq_map_center (K : Subgroup G) :
    Work.GW2.zcenterIn K = (Subgroup.center ↥K).map K.subtype := by
  ext x
  constructor
  · rintro ⟨hxK, hx⟩
    exact ⟨⟨x, hxK⟩, Subgroup.mem_center_iff.mpr (fun y =>
      Subtype.ext_iff.mpr (by simpa using (hx (y : G) y.2).symm)), rfl⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, fun z hz => ?_⟩
    have h := Subgroup.mem_center_iff.mp hy (⟨z, hz⟩ : ↥K)
    simpa using (congrArg Subtype.val h).symm

/-- A non-trivial `p`-group of the shape `↥K` has `Z(K) ≠ ⊥` in the ambient group. -/
theorem zcenterIn_ne_bot_of_isPGroup [Finite G] {K : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hP : IsPGroup p ↥K) (hK : K ≠ ⊥) : Work.GW2.zcenterIn K ≠ ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).mpr hK
  have hcen : Nontrivial ↥(Subgroup.center ↥K) := IsPGroup.center_nontrivial hP
  have hcard : 1 < Nat.card ↥(Subgroup.center ↥K) :=
    Finite.one_lt_card_iff_nontrivial.mpr hcen
  intro hbot
  have h1 : Nat.card ↥(Work.GW2.zcenterIn K) = 1 := Subgroup.card_eq_one.mpr hbot
  rw [zcenterIn_eq_map_center, Subgroup.card_map_of_injective K.subtype_injective] at h1
  omega

/-! ## 3. `π(F(X))` inside a single prime -/

/-- If `F*(X)` is a `q`-group then every prime dividing `|F(X)|` equals `q`. -/
theorem primeFactors_fitting_subset_singleton [Finite G] {X : Subgroup G} {q : ℕ} (hq : q.Prime)
    (hP : IsPGroup q ↥(Work.GW2.fstarIn X)) :
    ∀ r ∈ (Nat.card ↥(Work.GW2.fitting X)).primeFactors, r = q := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hF : IsPGroup q ↥(Work.GW2.fitting X) := isPGroup_fitting_of_isPGroup_fstarIn hP
  intro r hr
  have hr' : r ∈ q.primeFactors :=
    (isPGroup_iff_primeFactors_card_subset hq.ne_zero).mp hF hr
  exact (Nat.prime_dvd_prime_iff_eq (Nat.mem_primeFactors.mp hr').1 hq).mp
    (Nat.mem_primeFactors.mp hr').2.1

/-! ## 4. `F_π(F(X)) = F(X)` when all prime divisors of `|F(X)|` lie in `π` -/

/-- `O_π(H) = H` for a finite group `H` all of whose prime divisors lie in `π`. -/
theorem piCore_eq_top_of_primeFactors_subset {H : Type*} [Group H] [Finite H] {π : Set ℕ}
    (h : ∀ q ∈ (Nat.card H).primeFactors, q ∈ π) : Work.GW2.piCore π H = ⊤ := by
  have hmem : (⊤ : Subgroup H) ∈
      {N : Subgroup H | N.Normal ∧ ∀ q ∈ (Nat.card ↥N).primeFactors, q ∈ π} := by
    refine ⟨Subgroup.normal_top, ?_⟩
    intro q hq
    rw [Subgroup.card_top] at hq
    exact h q hq
  have htop : sSup {N : Subgroup H | N.Normal ∧ ∀ q ∈ (Nat.card ↥N).primeFactors, q ∈ π} =
      ⊤ := top_le_iff.mp (le_sSup hmem)
  rw [Work.GW2.piCore, htop]
  exact Subgroup.normalCore_eq_self ⊤

/-- If every prime dividing `|F(K)|` lies in `π` then `F_π(K) = F(K)`. -/
theorem fittingPiIn_eq_fittingIn_of_primeFactors_subset [Finite G] {K : Subgroup G}
    {π : Set ℕ} (h : ∀ q ∈ (Nat.card ↥(Work.GW2.fitting K)).primeFactors, q ∈ π) :
    Work.GW2.fittingPiIn π K = Work.GW2.fittingIn K := by
  simp only [Work.GW2.fittingPiIn, Work.GW2.fittingIn, Work.GW2.fittingPi,
    piCore_eq_top_of_primeFactors_subset h, Subgroup.map_top, Subgroup.range_subtype]

/-! ## 5. The requested theorem -/

theorem FstarSamePrime (T : Work.GW2.LocalToolkit) (hmain : Work.GW2.Bender17MainProp) :
    Work.GW2.FstarSamePrimeProp := by
  intro _ G _ _ hG A B hAsyl hDA hBsyl hDB hcA hBne hrelAB hcB hrelBA hABne hfstarA hfstarB
    p q hp hq hpA hqB
  by_contra hpq
  -- Step 1: `F*(A) = F(A)` and `F*(B) = F(B)`
  have hfA : Work.GW2.fstarIn A = Work.GW2.fittingIn A :=
    fstarIn_eq_fittingIn_of_layerIn_eq_bot (layerIn_eq_bot_of_isPGroup_fstarIn hp hpA)
  have hfB : Work.GW2.fstarIn B = Work.GW2.fittingIn B :=
    fstarIn_eq_fittingIn_of_layerIn_eq_bot (layerIn_eq_bot_of_isPGroup_fstarIn hq hqB)
  -- Step 2: `π(F(B)) ⊆ {q}` and `p ∉ π(F(B))`
  have hπB : Work.GW2.primesOf (Work.GW2.fittingIn B) ⊆ {q} := by
    intro r hr
    rw [Work.GW2.mem_primesOf] at hr
    have h1 : Nat.card ↥(Work.GW2.fittingIn B) = Nat.card ↥(Work.GW2.fitting B) :=
      Subgroup.card_map_of_injective B.subtype_injective
    rw [h1] at hr
    exact Set.mem_singleton_iff.mpr (primeFactors_fitting_subset_singleton hq hqB r hr)
  have hp_notMem : p ∉ Work.GW2.primesOf (Work.GW2.fittingIn B) := fun hmem =>
    hpq (Set.eq_of_mem_singleton (hπB hmem))
  -- Step 3: `F(A) ≤ F_{π(F(B))ᶜ}(A)`
  have hFle : Work.GW2.fittingIn A ≤
      Work.GW2.fittingPiIn (Work.GW2.primesOf (Work.GW2.fittingIn B))ᶜ A := by
    refine le_of_eq (fittingPiIn_eq_fittingIn_of_primeFactors_subset (K := A) ?_).symm
    intro r hr
    have hr' : r ∈ p.primeFactors :=
      (isPGroup_iff_primeFactors_card_subset hp.ne_zero).mp
        (isPGroup_fitting_of_isPGroup_fstarIn (X := A) hpA) hr
    have hrp : r = p :=
      (Nat.prime_dvd_prime_iff_eq (Nat.mem_primeFactors.mp hr').1 hp).mp
        (Nat.mem_primeFactors.mp hr').2.1
    rw [Set.mem_compl_iff, hrp]
    exact hp_notMem
  -- Step 4: Bender 1.7(ii) applied to the pair `(B, A)`
  have hii : Work.GW2.fittingPiIn (Work.GW2.primesOf (Work.GW2.fittingIn B))ᶜ A ⊓ B = ⊥ :=
    (hmain T G hG B A hBsyl hDB hAsyl hDA hcB hcA.ne_top hrelBA).2
  have hfin : Work.GW2.fittingIn A ⊓ B = ⊥ :=
    le_bot_iff.mp (le_trans (inf_le_inf_right B hFle) (le_of_eq hii))
  -- Step 5: `Z(F*(A)) ≤ F(A) ∩ B = ⊥` but `Z(F*(A)) ≠ ⊥`
  have hZle : Work.GW2.zcenterIn (Work.GW2.fstarIn A) ≤ B := Work.GW2.BRel.zcenter_le hrelAB
  have hZleF : Work.GW2.zcenterIn (Work.GW2.fstarIn A) ≤ Work.GW2.fittingIn A := by
    rw [hfA]; exact Work.GW2.zcenterIn_le _
  have hZbot : Work.GW2.zcenterIn (Work.GW2.fstarIn A) = ⊥ :=
    le_bot_iff.mp (le_trans (le_inf hZleF hZle) (le_of_eq hfin))
  exact zcenterIn_ne_bot_of_isPGroup hp hpA hfstarA hZbot

end Work.BMAX
