import Mathlib
import Submission.Work.PSU3.StageB.Step1

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

-- Import note (proof-level only; the statement below is unchanged).
--
-- The requester's original import list also carried
-- `Submission.Work.PSU3.StageB.ncard_involutions_inf_H`.  That import is *not* needed here: the
-- statement and proof below use only `Work.PSU3.PSU3Hyp`, `Work.PSU3.StageB.centralizerOddResidual`
-- (both from `Step1`), `Submission.Blueprint.involutions`/`centD` (from `Submission.Blueprint`)
-- and `Work.ThmF.split_odd_card_twoPoint` (from `Work.ThmF.Setup`, re-exported by `Step1`), and in
-- particular nothing about `Q0sub`/`ChIIFourProp` that `ncard_involutions_inf_H` provides.  Keeping
-- the import would pull in the whole `Work.Higman` development via `SemiregVendored`
-- (~1700 modules) for no gain.  Consumers that want `ncard_involutions_inf_H` should import it
-- directly.  (Same reasoning as the note at the top of `Submission/Work/PSU3/StageB/card_map_sylow_eq.lean`.)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open LeanEval.GroupTheory.Defs

namespace Work.PSU3.StageB

/-!
# Elementary group-theoretic helpers

The proof of `ncard_involutions_map_inf` below rests on the following four facts, proved here in
full because the workspace library did not (at the time of writing) carry them in the exact form
needed.  Only the first two are about general finite groups; the last two reduce the target to the
abstract situation `φ : F →* Y` with `ker φ = Z(F)` of odd order.
-/

/-- An element of a finite group of odd order whose square is `1` is trivial. -/
theorem eq_one_of_sq_eq_one_of_odd {M : Type} [Group M] [Finite M]
    (hodd : Odd (Nat.card M)) {z : M} (hz : z ^ 2 = 1) : z = 1 := by
  have hdvd : orderOf z ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hz
  have hoddz : Odd (orderOf z) := Odd.of_dvd_nat hodd (orderOf_dvd_natCard z)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · rwa [orderOf_eq_one_iff] at h
  · exfalso
    obtain ⟨k, hk⟩ := hoddz
    rw [h] at hk
    omega

/-- In a finite group of odd order, squaring is surjective: every element is a square. -/
theorem exists_sq_eq_of_odd_natCard {M : Type} [Group M] [Finite M]
    (hodd : Odd (Nat.card M)) (w : M) : ∃ z : M, z ^ 2 = w := by
  obtain ⟨k, hk⟩ := hodd
  refine ⟨w ^ (k + 1), ?_⟩
  have hw : w ^ Nat.card M = 1 := orderOf_dvd_iff_pow_eq_one.mp (orderOf_dvd_natCard w)
  have hpow : w ^ ((k + 1) * 2) = w := by
    have hk' : (k + 1) * 2 = Nat.card M + 1 := by rw [hk]; ring
    rw [hk', pow_succ, hw, one_mul]
  rw [← pow_mul]
  exact hpow

/-- The involutions of `(F ⊓ S).subgroupOf F`, seen as a set of `↥F`, are exactly the involutions
of `F ⊓ S`, seen as a set of the ambient group `G`, along the coercion `↥F → G`. -/
theorem ncard_involutions_subgroupOf {G : Type} [Group G] [Finite G] (F S : Subgroup G) :
    (Submission.Blueprint.involutions (((F ⊓ S).subgroupOf F : Subgroup ↥F) : Set ↥F)).ncard
      = (Submission.Blueprint.involutions ((F ⊓ S : Subgroup G) : Set G)).ncard := by
  classical
  refine Set.ncard_congr (fun x (_ : x ∈ Submission.Blueprint.involutions
        (((F ⊓ S).subgroupOf F : Subgroup ↥F) : Set ↥F)) => (x : G)) ?_ ?_ ?_
  · intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    exact ⟨Subgroup.mem_subgroupOf.mp hx1, by rw [Subgroup.orderOf_coe, hx2]⟩
  · intro x y hx hy hxy
    exact Subtype.ext hxy
  · intro b hb
    obtain ⟨hb1, hb2⟩ := hb
    refine ⟨⟨b, (Subgroup.mem_inf.mp hb1).1⟩, ⟨?_, ?_⟩, rfl⟩
    · exact Subgroup.mem_subgroupOf.mpr hb1
    · have h := Subgroup.orderOf_coe (⟨b, (Subgroup.mem_inf.mp hb1).1⟩ : ↥F)
      rw [← h]
      exact hb2

/-- **Kernel-the-centre transfer.**  If `φ : F →* Y` has kernel the centre `Z(F)` and `Z(F)` has
odd order, then `x ↦ φ x` is a bijection from the involutions of any subgroup `S ≥ Z(F)` onto the
involutions of `S.map φ`.  This is the abstract content of `#Inv(B_Y) = #Inv(F ⊓ H)`.

* well defined: `(φ x)² = φ (x²) = 1`, and `φ x ≠ 1` because an involution `x` has order `2` and so
  cannot lie in `Z(F)`, of odd order;
* injective: if `φ x = φ y` then `x⁻¹ y ∈ Z(F)`; writing `y = x z`, since `Z(F)` is central we get
  `1 = y² = x² z² = z²`, hence `z = 1` (odd order) and `y = x`;
* surjective: if `v = φ y` is an involution, then `y² ∈ Z(F)`, so `y² = z²` for some `z ∈ Z(F)`
  (odd order, so squaring is surjective on `Z(F)`), and `y z⁻¹ ∈ S` is an involution with
  `φ (y z⁻¹) = v`. -/
theorem ncard_involutions_map_of_ker_center {F : Type} [Group F] [Finite F]
    {Y : Type} [Group Y] [Finite Y] (φ : F →* Y)
    (hker : φ.ker = Subgroup.center F) (hodd : Odd (Nat.card ↥(Subgroup.center F)))
    (S : Subgroup F) (hZS : Subgroup.center F ≤ S) :
    (Submission.Blueprint.involutions ((S.map φ : Subgroup Y) : Set Y)).ncard
      = (Submission.Blueprint.involutions (S : Set F)).ncard := by
  classical
  have hcen : ∀ {x : F}, x ∈ Subgroup.center F → x ^ 2 = 1 → x = 1 := by
    intro x hx hx2
    have h1 : (⟨x, hx⟩ : ↥(Subgroup.center F)) = 1 :=
      eq_one_of_sq_eq_one_of_odd hodd
        (Subtype.ext (by rw [Subgroup.coe_pow]; simpa using hx2))
    simpa using congrArg (Subtype.val) h1
  have hsq2 : ∀ (M : Type) [Group M] (x : M), orderOf x = 2 → x ^ 2 = 1 := by
    intro M _ x hx
    rw [← hx]; exact pow_orderOf_eq_one x
  have hord2 : ∀ (M : Type) [Group M] (v : M), v ≠ 1 → v ^ 2 = 1 → orderOf v = 2 := by
    intro M _ v hv hv2
    have hd : orderOf v ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hv2
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hv
    · exact h
  refine (Set.ncard_congr
    (fun x (_ : x ∈ Submission.Blueprint.involutions (S : Set F)) => φ x) ?_ ?_ ?_).symm
  · -- well defined
    intro x hx
    obtain ⟨hxS, hx2⟩ := hx
    have hx2' : x ^ 2 = 1 := hsq2 F x hx2
    have hxne : x ≠ 1 := by intro h; rw [h] at hx2; simp at hx2
    have hmem : φ x ∈ S.map φ := Subgroup.mem_map.mpr ⟨x, hxS, rfl⟩
    have hne : φ x ≠ 1 := by
      intro h1
      have hxk : x ∈ φ.ker := MonoidHom.mem_ker.mpr h1
      rw [hker] at hxk
      exact hxne (hcen hxk hx2')
    have h2 : (φ x) ^ 2 = 1 := by rw [← map_pow, hx2', map_one]
    exact ⟨hmem, hord2 Y (φ x) hne h2⟩
  · -- injective
    intro x y hx hy hf
    obtain ⟨hxS, hx2⟩ := hx
    obtain ⟨hyS, hy2⟩ := hy
    have hx2' : x ^ 2 = 1 := hsq2 F x hx2
    have hy2' : y ^ 2 = 1 := hsq2 F y hy2
    set z : F := x⁻¹ * y with hzdef
    have hzk : z ∈ Subgroup.center F := by
      have h1 : z ∈ φ.ker := by
        rw [MonoidHom.mem_ker, hzdef, map_mul, map_inv, ← hf, inv_mul_cancel]
      rwa [hker] at h1
    have hcomm : Commute x z := Subgroup.mem_center_iff.mp hzk x
    have hy_eq : y = x * z := by rw [hzdef]; group
    have hz2 : z ^ 2 = 1 := by
      rw [← hy2', hy_eq, hcomm.mul_pow, hx2', one_mul]
    have hz1 : z = 1 := hcen hzk hz2
    exact (show y = x by rw [hy_eq, hz1, mul_one]).symm
  · -- surjective
    intro b hb
    obtain ⟨hbmap, hb2⟩ := hb
    obtain ⟨y, hyS, hyφ⟩ := Subgroup.mem_map.mp hbmap
    have hb2' : b ^ 2 = 1 := hsq2 Y b hb2
    have hbne : b ≠ 1 := by intro h; rw [h] at hb2; simp at hb2
    have hwker : y ^ 2 ∈ Subgroup.center F := by
      have h1 : y ^ 2 ∈ φ.ker := by
        rw [MonoidHom.mem_ker, map_pow, hyφ, hb2']
      rwa [hker] at h1
    obtain ⟨zz, hzz⟩ :=
      exists_sq_eq_of_odd_natCard hodd (⟨y ^ 2, hwker⟩ : ↥(Subgroup.center F))
    have hz2 : (zz : F) ^ 2 = y ^ 2 := by
      have h := congrArg (Subtype.val) hzz
      simpa using h
    have hzmem : (zz : F) ∈ Subgroup.center F := zz.2
    have hzφ : φ (zz : F) = 1 := by
      have h1 : (zz : F) ∈ φ.ker := by rwa [hker]
      exact MonoidHom.mem_ker.mp h1
    have hxS : y * (zz : F)⁻¹ ∈ S := S.mul_mem hyS (S.inv_mem (hZS hzmem))
    have hx2 : (y * (zz : F)⁻¹) ^ 2 = 1 := by
      have hcomm : Commute y (zz : F)⁻¹ :=
        Commute.inv_right (Subgroup.mem_center_iff.mp hzmem y)
      rw [hcomm.mul_pow, inv_pow, hz2, mul_inv_cancel]
    have hxne : y * (zz : F)⁻¹ ≠ 1 := by
      intro h1
      apply hbne
      have hy : y = (zz : F) := by
        calc y = y * (zz : F)⁻¹ * (zz : F) := by group
          _ = 1 * (zz : F) := by rw [h1]
          _ = (zz : F) := by rw [one_mul]
      rw [← hyφ, hy, hzφ]
    exact ⟨y * (zz : F)⁻¹, ⟨hxS, hord2 F (y * (zz : F)⁻¹) hxne hx2⟩, by
      rw [map_mul, map_inv, hyφ, hzφ, inv_one, mul_one]⟩

/-
# Step 4 bookkeeping (iv): `#Inv(B_Y) = #Inv(F ⊓ H)`

`F := U = O^{2'}(C_G(P))`, `Z := Z(↥F)`, `φ : ↥F →* Y` with `φ.ker = Z` (so `Y = F/Z`), and
`B_Y := ((H ⊓ F).subgroupOf F).map φ`, the Borel of `Y`.  Because `Z ⊆ P` (hypothesis `hZP`, this
is `Work.PSU3.StageB.centralizerOddResidual_center_le_P`) and `P ≤ centD H t ≤ D ⊆ H`, the centre
sits inside `H ⊓ F` and has **odd** order.  Then the number of involutions of `B_Y` equals the
number of involutions of `F ⊓ H`:

    #Inv(B_Y) = #Inv(F ⊓ H).

With `Work.PSU3.StageB.ncard_involutions_inf_H` (`#Inv(F ⊓ H) + 1 = |C_{Q₀}(P)| = ℓ`) this gives
`#Inv(B_Y) + 1 = ℓ`, the count that pins the model index in step 5.

The argument is a bijection `x ↦ φ x` from the involutions of `F ⊓ H` onto those of `B_Y`:

* well defined: `(φ x)² = φ (x²) = 1`, and `φ x ≠ 1` because an involution `x` has order `2` and so
  cannot lie in `Z` (whose order divides `|P|`, odd, as `Z ≤ P ≤ D`);
* injective: if `φ x = φ y` then `x⁻¹ y ∈ Z`; writing `y = x z` with `z ∈ Z` (so `x`, `z`
  commute *because `Z` is central in `F`*) gives `1 = y² = x² z² = z²`, hence `z = 1` (odd order)
  and `y = x`;
* surjective: let `v ∈ B_Y` be an involution, `v = φ y` with `y ∈ H ⊓ F`; then `y² ∈ Z`, so
  `y² = z²` for some `z ∈ Z` (`Z` abelian of odd order, so squaring is surjective on `Z`), and
  `y z⁻¹ ∈ H ⊓ F` is an involution (`(y z⁻¹)² = y² z⁻² = 1`, `z` central) with
  `φ (y z⁻¹) = φ y = v`.  Here `z ∈ H` (supplied by `hZP` and `P ≤ H`) is used.

The bijection is `ncard_involutions_map_of_ker_center` applied to `F := ↥U` and
`S := (U ⊓ H).subgroupOf U` (whose `Z(↥U)`-containment is `hZS`, from `hZleH`), combined with
`ncard_involutions_subgroupOf`; the oddness `Odd (Nat.card (Z(↥U)))` is `hoddZ`, obtained from
`hZP`, `hPV` and `split_odd_card_twoPoint`.
-/
theorem ncard_involutions_map_inf {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) {P : Subgroup G}
    (hPV : P ≤ Submission.Blueprint.centD H t)
    (hZP : (Subgroup.center ↥(Work.PSU3.StageB.centralizerOddResidual P)).map
        (Work.PSU3.StageB.centralizerOddResidual P).subtype ≤ P)
    {Y : Type} [Group Y] [Finite Y]
    {φ : ↥(Work.PSU3.StageB.centralizerOddResidual P) →* Y}
    (hker : φ.ker = Subgroup.center ↥(Work.PSU3.StageB.centralizerOddResidual P)) :
    (Submission.Blueprint.involutions
        ((((H ⊓ Work.PSU3.StageB.centralizerOddResidual P).subgroupOf
            (Work.PSU3.StageB.centralizerOddResidual P)).map φ : Subgroup Y) : Set Y)).ncard
      = (Submission.Blueprint.involutions
        ((Work.PSU3.StageB.centralizerOddResidual P ⊓ H : Subgroup G) : Set G)).ncard := by
  classical
  let U : Subgroup G := Work.PSU3.StageB.centralizerOddResidual P
  change (Submission.Blueprint.involutions
      ((((H ⊓ U).subgroupOf U).map φ : Subgroup Y) : Set Y)).ncard
    = (Submission.Blueprint.involutions ((U ⊓ H : Subgroup G) : Set G)).ncard
  -- `V = centD H t ≤ D` has odd order, hence so do `P` and `Z(↥U)`
  have hoddCD : Odd (Nat.card ↥(Submission.Blueprint.centD H t)) :=
    Odd.of_dvd_nat (Work.ThmF.split_odd_card_twoPoint hS.split)
      (Subgroup.card_dvd_of_le inf_le_left)
  have hoddP : Odd (Nat.card ↥P) := Odd.of_dvd_nat hoddCD (Subgroup.card_dvd_of_le hPV)
  have hcardZ : Nat.card ↥((Subgroup.center ↥U).map U.subtype) = Nat.card ↥(Subgroup.center ↥U) :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective U)
  have hoddZ : Odd (Nat.card ↥(Subgroup.center ↥U)) := by
    rw [← hcardZ]
    exact Odd.of_dvd_nat hoddP (Subgroup.card_dvd_of_le hZP)
  -- `Z(↥U) ⊆ P ≤ centD H t ≤ D ⊆ H`
  have hZleH : ∀ z : ↥U, z ∈ Subgroup.center ↥U → (z : G) ∈ H := by
    intro z hz
    have h1 : (z : G) ∈ (Subgroup.center ↥U).map U.subtype := Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
    have h2 : (z : G) ∈ P := hZP h1
    have h3 : (z : G) ∈ Submission.Blueprint.centD H t := hPV h2
    exact (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp h3).1).1
  have hZS : Subgroup.center ↥U ≤ (U ⊓ H).subgroupOf U := by
    intro z hz
    rw [Subgroup.mem_subgroupOf]
    exact ⟨z.2, hZleH z hz⟩
  rw [inf_comm H U]
  rw [ncard_involutions_map_of_ker_center φ hker hoddZ ((U ⊓ H).subgroupOf U) hZS,
    ncard_involutions_subgroupOf U H]

end Work.PSU3.StageB
