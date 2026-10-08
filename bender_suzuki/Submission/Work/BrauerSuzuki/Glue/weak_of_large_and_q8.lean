import Mathlib
import Submission.Work.BrauerSuzuki.Defs
import Submission.Work.BrauerSuzuki.Quaternion.genQuaternionData_basic
import Submission.Work.BrauerSuzuki.Group.isConj_of_orderOf_eq_two
import Submission.Work.BrauerSuzuki.OddCore.oddCard_oddCore

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Glue: the weak Brauer–Suzuki form from the two cases `|S| ≥ 16` and `S ≅ Q₈`

`BrauerSuzukiWeak` (PNAS 1959, Theorem 1) asks that a finite group `G` whose Sylow
`2`-subgroups are generalized quaternion has a **proper** normal subgroup containing every
involution.  The work is split into the two published cases, and this file assembles them:

* `BrauerSuzukiWeakLarge` (Dade 1971, Theorem 6.8): the case `n ≥ 3` of the normal form
  `⟨τ, ρ | orderOf τ = 2ⁿ, ρ τ ρ⁻¹ = τ⁻¹, ρ² = τ^{2^{n-1}}⟩`, i.e. `|S| ≥ 16`;
* `BrauerSuzukiQ8Strong` (Glauberman 1974), stated in the strong quotient-free form: for
  `n = 2` (so `S ≅ Q₈`) every involution is central modulo `O(G)`.

Since `d.n ≥ 2` always, these two cases exhaust the possibilities.

## The `Q₈` case

Here the strong input says that every involution `t` satisfies
`t g t⁻¹ g⁻¹ ∈ O(G)` for all `g`; in other words every involution is central in the
quotient `G ⧸ O(G)`.  The proper normal subgroup is therefore forced:

  `N := (Z(G ⧸ O(G)))⁻¹`  (the preimage of the centre of `G ⧸ O(G)` under `G ↠ G ⧸ O(G)`).

* `N` is normal, being the preimage of a normal subgroup under a homomorphism;
* every involution lies in `N`, by the strong input
  (`mem_center_quotient_of_commutator_mem`);
* `N` is proper: the Sylow `2`-subgroup `S ≅ Q₈` supplies `τ, ρ` with `orderOf τ = 4` and
  `ρ τ ρ⁻¹ = τ⁻¹`; if `mk τ` were central then `mk τ = mk (ρτρ⁻¹) = mk τ⁻¹`, so `τ² ∈ O(G)`,
  contradicting `orderOf τ² = 2` and `|O(G)|` odd (`mk_tau_not_mem_center`).

The auxiliary lemma `mk_comm_of_commutator_mem` records the elementary fact that an element
whose commutator with `y` lies in the normal subgroup `O` commutes with `y` modulo `O`
(this is exactly `x y x⁻¹ y⁻¹ ∈ O ⟹ [x,y] ≡ 1`).
-/

set_option autoImplicit false

namespace Work.BrauerSuzuki.Glue

open Submission.Blueprint

/-- **Commutators and the quotient by a normal subgroup.**  If `x y x⁻¹ y⁻¹ ∈ O` for a normal
subgroup `O`, then the images of `x` and `y` in `G ⧸ O` commute.  (The commutator `[x,y]` lies
in the kernel of `G →* G ⧸ O`, which is `O`.) -/
theorem mk_comm_of_commutator_mem {G : Type*} [Group G] {O : Subgroup G} [O.Normal] {x y : G}
    (h : x * y * x⁻¹ * y⁻¹ ∈ O) :
    QuotientGroup.mk' O x * QuotientGroup.mk' O y = QuotientGroup.mk' O y * QuotientGroup.mk' O x := by
  rw [← map_mul (QuotientGroup.mk' O), ← map_mul (QuotientGroup.mk' O),
    QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  -- it remains to show `(x * y)⁻¹ * (y * x) = y⁻¹ * x⁻¹ * y * x ∈ O`
  have hd : y⁻¹ * x⁻¹ * y * x ∈ O := by
    have h1 : y⁻¹ * (x * y * x⁻¹ * y⁻¹)⁻¹ * y ∈ O := by
      have := (inferInstance : O.Normal).conj_mem (x * y * x⁻¹ * y⁻¹)⁻¹ (O.inv_mem h) y⁻¹
      simpa using this
    have h2 := (inferInstance : O.Normal).conj_mem (y⁻¹ * (x * y * x⁻¹ * y⁻¹)⁻¹ * y) h1 x⁻¹
    convert h2 using 1
    group
  convert hd using 1
  group

/-- **Elements whose commutator with everything lies in `O` are central modulo `O`.** -/
theorem mem_center_quotient_of_commutator_mem {G : Type*} [Group G] {O : Subgroup G} [O.Normal]
    {x : G} (h : ∀ g : G, x * g * x⁻¹ * g⁻¹ ∈ O) :
    QuotientGroup.mk' O x ∈ Subgroup.center (G ⧸ O) := by
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective O y
  exact (mk_comm_of_commutator_mem (h g)).symm

/-- **The `Q₈` non-centrality input.**  Let `P ≤ G` carry a generalized quaternion presentation
with `n = 2` (so `P ≅ Q₈`) and let `O ⊴ G` have odd order.  Then the image of `τ` in `G ⧸ O` is
**not** central: `ρ τ ρ⁻¹ = τ⁻¹` becomes `τ̄ = τ̄⁻¹` under centrality, forcing `τ² ∈ O`, which is
impossible because `orderOf τ² = 2` while `|O|` is odd. -/
theorem mk_tau_not_mem_center {G : Type*} [Group G] [Finite G] {O : Subgroup G} [O.Normal]
    (hOdd : Odd (Nat.card O)) {P : Subgroup G} (d : Work.BrauerSuzuki.GenQuaternionData P)
    (hn : d.n = 2) :
    QuotientGroup.mk' O (d.tau : G) ∉ Subgroup.center (G ⧸ O) := by
  intro hc
  rw [Subgroup.mem_center_iff] at hc
  -- centrality of `τ̄` gives `ρ̄ τ̄ ρ̄⁻¹ = τ̄` ...
  have h1 : QuotientGroup.mk' O (d.rho : G) * QuotientGroup.mk' O (d.tau : G) *
      (QuotientGroup.mk' O (d.rho : G))⁻¹ = QuotientGroup.mk' O (d.tau : G) := by
    rw [hc (QuotientGroup.mk' O (d.rho : G))]
    group
  -- ... while `ρ τ ρ⁻¹ = τ⁻¹` gives `ρ̄ τ̄ ρ̄⁻¹ = τ̄⁻¹`.
  have hconj : (d.rho : G) * (d.tau : G) * (d.rho : G)⁻¹ = (d.tau : G)⁻¹ := by
    have := congrArg (fun z : P => (z : G)) d.rho_conj
    simpa using this
  have h2 : QuotientGroup.mk' O (d.rho : G) * QuotientGroup.mk' O (d.tau : G) *
      (QuotientGroup.mk' O (d.rho : G))⁻¹ = (QuotientGroup.mk' O (d.tau : G))⁻¹ := by
    calc QuotientGroup.mk' O (d.rho : G) * QuotientGroup.mk' O (d.tau : G) *
            (QuotientGroup.mk' O (d.rho : G))⁻¹
        = QuotientGroup.mk' O ((d.rho : G) * (d.tau : G) * (d.rho : G)⁻¹) := by
          rw [map_mul, map_mul, map_inv]
      _ = QuotientGroup.mk' O ((d.tau : G)⁻¹) := by rw [hconj]
      _ = (QuotientGroup.mk' O (d.tau : G))⁻¹ := by rw [map_inv]
  have hself : QuotientGroup.mk' O (d.tau : G) = (QuotientGroup.mk' O (d.tau : G))⁻¹ :=
    h1.symm.trans h2
  have hsq : (QuotientGroup.mk' O (d.tau : G)) ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 1 [hself]
    exact inv_mul_cancel _
  -- `τ̄² = 1` means `τ² ∈ ker (G →* G ⧸ O) = O`.
  have hmem : (d.tau : G) ^ 2 ∈ O := by
    rw [← QuotientGroup.ker_mk' O, MonoidHom.mem_ker, map_pow, hsq]
  -- but `orderOf τ² = 2`, while every element of the odd-order group `O` has odd order.
  have hbase : orderOf (d.tau ^ (2 ^ (d.n - 1))) = 2 :=
    (Work.BrauerSuzuki.Quaternion.genQuaternionData_basic d).2.2.1
  have hpow : 2 ^ (d.n - 1) = 2 := by rw [hn]; norm_num
  have hbase2 : orderOf (d.tau ^ 2) = 2 := by simpa [hpow] using hbase
  have hord : orderOf ((d.tau : G) ^ 2) = 2 := by
    rw [← Subgroup.coe_pow P d.tau 2, Subgroup.orderOf_coe]
    exact hbase2
  have hnotmem : (d.tau : G) ^ 2 ∉ O := by
    intro hmem2
    have hdvd : orderOf ((d.tau : G) ^ 2) ∣ Nat.card O := by
      have h1' := orderOf_dvd_natCard (⟨(d.tau : G) ^ 2, hmem2⟩ : O)
      have h2' : orderOf (⟨(d.tau : G) ^ 2, hmem2⟩ : O) = orderOf ((d.tau : G) ^ 2) :=
        (Subgroup.orderOf_coe _).symm
      rwa [h2'] at h1'
    rw [hord] at hdvd
    exact (Nat.not_even_iff_odd.mpr hOdd) (even_iff_two_dvd.mpr hdvd)
  exact hnotmem hmem

/-- **Glue.**  The weak Brauer–Suzuki form follows from its two cases: Dade's theorem for
generalized quaternion Sylow `2`-subgroups of order `≥ 16` (`n ≥ 3`) and Glauberman's `Q₈`
case (`n = 2`), the latter in the strong form "every involution is central modulo `O(G)`". -/
theorem weak_of_large_and_q8 (hL : Work.BrauerSuzuki.BrauerSuzukiWeakLarge)
    (hQ : Work.BrauerSuzuki.BrauerSuzukiQ8Strong) : Work.BrauerSuzuki.BrauerSuzukiWeak := by
  intro G _instG _finG hgen
  obtain ⟨S, hS⟩ := hgen
  obtain ⟨d⟩ := hS
  by_cases hlarge : 3 ≤ d.n
  · -- the case `|S| ≥ 16` is Dade's theorem
    exact hL G S d hlarge
  · -- otherwise `n = 2`, i.e. `S ≅ Q₈`
    have hn : d.n = 2 := by have := d.hn; omega
    have hOddO : Odd (Nat.card (Submission.Blueprint.oddCore G)) :=
      Work.BrauerSuzuki.OddCore.oddCard_oddCore
    refine ⟨(Subgroup.center (G ⧸ Submission.Blueprint.oddCore G)).comap
      (QuotientGroup.mk' (Submission.Blueprint.oddCore G)), ?_, ?_, ?_⟩
    · exact Subgroup.Normal.comap (inferInstance : (Subgroup.center _).Normal) _
    · -- properness: the image of `τ` is outside the centre
      intro htop
      have hnc := mk_tau_not_mem_center hOddO d hn
      exact hnc (by
        have hmem : (d.tau : G) ∈ (Subgroup.center (G ⧸ Submission.Blueprint.oddCore G)).comap
            (QuotientGroup.mk' (Submission.Blueprint.oddCore G)) := by
          rw [htop]; exact Subgroup.mem_top _
        rwa [Subgroup.mem_comap] at hmem)
    · -- every involution is central modulo `O(G)` by the strong `Q₈` input
      intro t ht
      rw [Subgroup.mem_comap]
      exact mem_center_quotient_of_commutator_mem (fun g => hQ G S d hn t ht g)

end Work.BrauerSuzuki.Glue
