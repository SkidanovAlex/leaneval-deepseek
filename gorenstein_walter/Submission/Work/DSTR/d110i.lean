import Mathlib
import Submission.Work.DSTR.Defs
import Submission.Work.ASM.oddCore_odd
import Submission.Work.DSTR.exists_mul_mem_centralizer

/-!
# DS9: Bender 1981, 1.10(i) (`Work.GW2.D110iProp`)

Given `DihOrCycSylow X` and `IsDGroup X`, the reduction to `Q := X ⧸ O(X)` goes as follows.

* `h1`/`h2` provide `DihOrCycSylow Q` and `O(Q) = 1`, and `IsDGroup X` *is* `DShape Q`.
* The image `P̄` of `P` in `Q` is an odd `p`-subgroup, and `h9a` (`DS9a`) applies to it once we
  know that `C_Q(t̄) ≤ N_Q(P̄)`.  The latter is the content of the reduction: the preimage of
  `C_Q(t̄)` is `C_X(t)·O(X)` (`Work.DSTR.exists_mul_mem_centralizer`, i.e. `H¹(⟨t⟩,O(X)) = 0`
  for `O(X)` of odd order), and `C_X(t) ≤ N_X(P)` by hypothesis; since `O(X) = ker π` the
  `O(X)`-part is invisible in `Q`.
* Hence `[P̄,t̄] = 1` in `Q`, i.e. `[P,t] ≤ O(X)`, and `h9b` (`DS9b`) upgrades this to
  `[P,t] ≤ O_p(X)`.
-/

namespace Work.DSTR

open scoped MatrixGroups
open scoped commutatorElement

/-- The image of an involution of odd order modulo an odd-order normal subgroup is again an
involution: `π t ≠ 1` because `t ∈ N` would force `2 ∣ |N|`, and `(π t)² = π(t²) = 1`. -/
private theorem orderOf_mk_eq_two {X : Type*} [Group X] {N : Subgroup X} [N.Normal]
    (hNodd : Odd (Nat.card N)) {t : X} (ht : orderOf t = 2) :
    orderOf (QuotientGroup.mk' N t) = 2 := by
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have hdvd : orderOf (QuotientGroup.mk' N t) ∣ 2 :=
    orderOf_dvd_iff_pow_eq_one.mpr (by rw [← map_pow, ht2, map_one])
  have hne : QuotientGroup.mk' N t ≠ 1 := by
    intro h
    have htN : t ∈ N := (QuotientGroup.eq_one_iff t).mp h
    have h2 : 2 ∣ Nat.card N := (by rw [ht] : 2 ∣ orderOf t).trans
      (Subgroup.orderOf_dvd_natCard N htN)
    exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr h2)
  have hne1 : orderOf (QuotientGroup.mk' N t) ≠ 1 := fun h =>
    hne (orderOf_eq_one_iff.mp h)
  have hle : orderOf (QuotientGroup.mk' N t) ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have hne0 : orderOf (QuotientGroup.mk' N t) ≠ 0 := by
    intro h
    rw [h] at hdvd
    norm_num at hdvd
  omega

/-- Commuting with `π t` in the quotient modulo `N` forces `⁅P, ⟨t⟩⁆ ≤ N`. -/
private theorem commutator_le_ker_of_map_le_centralizer {X : Type*} [Group X] {N : Subgroup X}
    [N.Normal] {t : X} {P : Subgroup X}
    (h : P.map (QuotientGroup.mk' N) ≤
      Subgroup.centralizer ({QuotientGroup.mk' N t} : Set (X ⧸ N))) :
    ⁅P, Subgroup.zpowers t⁆ ≤ N := by
  rw [← QuotientGroup.ker_mk' N, ← Subgroup.map_eq_bot_iff]
  rw [Subgroup.map_commutator, MonoidHom.map_zpowers]
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  rwa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

/-- **D110i** (`Work.GW2.D110iProp`, Bender 1981 1.10(i)): for a D-group `X`, an involution `t` and a `C_X(t)`-invariant odd `p`-subgroup `P` one has `[P,t] <= O_p(X)`.  Reduce to `Q = X/O(X)`: `h1`/`h2` give `DihOrCycSylow Q` and `O(Q) = 1`, the image `P̄` is `C_Q(t̄)`-invariant, `DS9a` gives `[P̄,t̄] = 1`, i.e. `[P,t] <= O(X)`, and `DS9b` finishes. -/
theorem d110i (h1 : Work.GW2.DihOrCycHeredProp) (h2 : Work.GW2.OddCoreQuotProp)
    (h9a : Work.GW2.D110iModelProp) (h9b : Work.GW2.D110iOddProp) :
    Work.GW2.D110iProp := by
  intro X instG instF hft hsy hd t ht p instP hp2 P hP hNorm
  let N : Subgroup X := Work.GW2.oddCore X
  have hNnorm : N.Normal := Work.GW2.oddCore_normal X
  have hNodd : Odd (Nat.card N) := Work.ASM.oddCore_odd X
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht] at h
    simpa only [pow_two] using h
  -- `Q = X/O(X)` is again a D-group with trivial odd core
  have hsyQ : Work.GW2.DihOrCycSylow (X ⧸ N) := (h1 X hsy).2 N
  have hcoreQ : Work.GW2.oddCore (X ⧸ N) = ⊥ := h2 X
  have hshapeQ : Work.GW2.DShape (X ⧸ N) := hd
  have htbar : orderOf (QuotientGroup.mk' N t) = 2 := orderOf_mk_eq_two hNodd ht
  -- The image `P̄` is `C_Q(t̄)`-invariant: the preimage of `C_Q(t̄)` is `C_X(t)·N`
  have hNormBar : Subgroup.centralizer ({QuotientGroup.mk' N t} : Set (X ⧸ N)) ≤
      Subgroup.normalizer ((P.map (QuotientGroup.mk' N) : Subgroup (X ⧸ N)) :
        Set (X ⧸ N)) := by
    intro y hy
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective N y
    -- `⁅u,t⁆ ∈ N`, since `π t` and `π u` commute
    have hcomm_mem : ⁅u, t⁆ ∈ N := by
      rw [← QuotientGroup.eq_one_iff (⁅u, t⁆)]
      have hct := (Subgroup.mem_centralizer_iff.mp hy) (QuotientGroup.mk' N t) (by simp)
      rw [← QuotientGroup.mk'_apply, map_commutatorElement, commutatorElement_def, ← hct]
      group
    -- so `u * m` centralizes `t` for some `m ∈ N`
    obtain ⟨m, hmN, hum⟩ := exists_mul_mem_centralizer hNnorm hNodd ht2 hcomm_mem
    have hm1 : (QuotientGroup.mk' N) m = 1 := (QuotientGroup.eq_one_iff m).mpr hmN
    have hkey : (QuotientGroup.mk' N) (u * m) = (QuotientGroup.mk' N) u := by
      rw [map_mul, hm1, mul_one]
    have hmem : (QuotientGroup.mk' N) (u * m) ∈
        (Subgroup.normalizer (P : Set X)).map (QuotientGroup.mk' N) :=
      Subgroup.mem_map.mpr ⟨u * m, hNorm hum, rfl⟩
    have hres := Subgroup.le_normalizer_map (H := P) (QuotientGroup.mk' N) hmem
    rwa [hkey] at hres
  -- `DS9a` in `Q`
  have hPbar : IsPGroup p (P.map (QuotientGroup.mk' N)) := hP.map (QuotientGroup.mk' N)
  have h9a' := h9a (X ⧸ N) hsyQ hcoreQ hshapeQ (QuotientGroup.mk' N t) htbar p hp2
    (P.map (QuotientGroup.mk' N)) hPbar hNormBar
  -- hence `[P,t] ≤ O(X)`, and `DS9b` upgrades this to `O_p(X)`
  have hcomm : ⁅P, Subgroup.zpowers t⁆ ≤ N :=
    commutator_le_ker_of_map_le_centralizer h9a'
  exact h9b X hft hsy hd t ht p hp2 P hP hNorm hcomm

end Work.DSTR
