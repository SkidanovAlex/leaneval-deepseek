/-
# The involutions of `C_G(z)` in the `A₇`-configuration, with `U ⊴ C_G(z)`

The lemma `Work.A7REC.Char.cardInvolutionsCentralizer`
(`Submission/Work/A7REC/Char/cardInvolutionsCentralizer.lean`) claims that in every context
`h : Work.A7REC.Char.A7InvCtx G` the centralizer `h.C = C_G(z)` has exactly nine involutions.
**That statement is false as written**: an ambient group supplying the context can be the
permutation group `G = ⟨(5,6)(8,10), (2,3)(7,8)(9,10), (7,9)(8,10), (1,2,3), (4,5,6)⟩ ≤ Sym 10`
of order `72` (`SmallGroup(72,22) ≅ (C₆ × S₃) : C₂`) with
`S = ⟨(5,6)(8,10), (2,3)(7,8)(9,10), (7,9)(8,10)⟩ ≅ D₈` (a Sylow 2-subgroup),
`z = (7,9)(8,10)` (central, of order `2`), `U = ⟨(1,2,3)(4,5,6)⟩` (order `3`, `U ⊓ S = ⊥`,
`U ⊔ S = G = C_G(z)`) and `π = (2,3)(5,6)(7,8,9,10) ∈ S` of order `4` with `C_G(π) = ⟨π⟩`;
there `h.C = ⊤` has **13** involutions.  The failing step of the intended plan is the claim that
the conjugates of `S` in `C` are among `S, S^σ, S^{σ²}`: conjugation by `s ∈ S` sends `S^{σ^i}`
to `S^{s⁻¹σ^i s}`, which need only be one of the three when `s` normalizes `U`; in the example
above `n₂(C) = 9 = [C : S]`, and with `|C| = 72` there is no bound on the number of elements of
order `4` either (`G` has an `18`-element class of elements of order `4`).

The repair is to add the missing hypothesis, exactly the field `A7RecCtx.hUnorm` of the real
`A₇`-context: `U` is normal in `C_G(z)`.  Since `U ⊓ S = ⊥` (coprime orders), this makes
`C_G(z) = U ⋊ S` an internal semidirect product and the count becomes the elementary one below.
Writing `K = C_S(U)`:
* `|K| = 4`: the conjugation action of `S` on `U ≅ Z₃` has kernel `K`, so `[S : K] ≤ 2`, and
  `K ≠ S` because `π ∉ K` (else `σ ∈ C_G(π) = ⟨π⟩`, of order `4`);
* `K` contains no element of order `4` (the elements of order `4` of `S ≅ D₈` are `π, π⁻¹`), so
  `K` is a four-group: it has exactly `3` involutions, and `S ∖ K` has `5 - 3 = 2`;
* an element `u * s` (`u ∈ U`, `s ∈ S`) is an involution iff `s ^ 2 = 1` and (`u = 1` or
  `s ∉ K`), which gives `5 + 2 · 2 = 9` involutions.

With `|C| = 24` in place of the normality hypothesis the conclusion is also true — normality is
then a *consequence* of the counting (`Work.A7REC.Char.U_normal_of_card_centralizer_eq_24`).
-/
import Mathlib
import Submission.Work.A7REC.Char.a7InvolutionCounts

set_option linter.unusedSectionVars false

namespace Work.A7REC.Char

open Subgroup

open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

namespace A7InvCtx

variable (h : A7InvCtx G)

/-- The kernel `C_S(U)` of the conjugation action of `S` on `U`: the elements of `S` centralizing
`U`. -/
abbrev K : Subgroup G := h.Sg ⊓ Subgroup.centralizer (h.U : Set G)

/-- The subtype of a subgroup is equivalent to the corresponding subtype of the ambient group. -/
def subtypeSubgroupEquiv {H : Subgroup G} (p : G → Prop) :
    {x : ↥H // p (x : G)} ≃ {x : G // x ∈ H ∧ p x} where
  toFun x := ⟨(x.1 : G), x.1.2, x.2⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl

/-- Membership in `K`, in conjugation form. -/
theorem mem_K_iff {s : G} (hs : s ∈ h.Sg) : s ∈ h.K ↔ ∀ u ∈ h.U, s * u * s⁻¹ = u := by
  constructor
  · intro hsK u hu
    have h1 : u * s = s * u := (Subgroup.mem_centralizer_iff.mp hsK.2) u hu
    calc s * u * s⁻¹ = (u * s) * s⁻¹ := by rw [h1]
      _ = u := by group
  · intro hconj
    refine ⟨hs, Subgroup.mem_centralizer_iff.mpr (fun u hu => ?_)⟩
    calc u * s = (s * u * s⁻¹) * s := by rw [hconj u hu]
      _ = s * u := by group

/-- With `U ⊴ C`, the Sylow subgroup `S ≤ C` normalizes `U`. -/
theorem Sg_le_normalizer_U (hnorm : (h.U.subgroupOf h.C).Normal) :
    h.Sg ≤ Subgroup.normalizer (h.U : Set G) :=
  le_trans h.Sg_le_C ((Subgroup.normal_subgroupOf_iff_le_normalizer h.U_le_C).mp hnorm)

/-- Conjugation by an element of `S` preserves `U`. -/
theorem conj_mem_U (hnorm : (h.U.subgroupOf h.C).Normal) {s u : G} (hs : s ∈ h.Sg)
    (hu : u ∈ h.U) : s * u * s⁻¹ ∈ h.U :=
  ((Subgroup.mem_normalizer_iff.mp (Sg_le_normalizer_U h hnorm hs)) u).mp hu

/-- `x ^ 3 = 1` gives `x ^ 4 = x`. -/
theorem pow_four_eq_self {x : G} (h3 : x ^ 3 = 1) : x ^ 4 = x := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, pow_add, h3, one_mul, pow_one]

/-- `x ^ 3 = 1` gives `(x ^ 2)⁻¹ = x`. -/
theorem inv_sq_eq_self {x : G} (h3 : x ^ 3 = 1) : (x ^ 2)⁻¹ = x := by
  have h : x ^ 2 * x = 1 := by rw [← pow_succ, show 2 + 1 = 3 from rfl, h3]
  exact inv_eq_of_mul_eq_one_right h

/-- `x ^ 3 = 1` gives `x ^ 2 = x⁻¹`. -/
theorem sq_eq_inv {x : G} (h3 : x ^ 3 = 1) : x ^ 2 = x⁻¹ :=
  mul_eq_one_iff_eq_inv.mp (by rw [← pow_succ, show 2 + 1 = 3 from rfl, h3])

/-- The elements of the group `U` of order `3`. -/
theorem U_elements {u : G} (hu : u ∈ h.U) : u = 1 ∨ u = h.σ ∨ u = h.σ ^ 2 := by
  have hσ2ne : h.σ ^ 2 ≠ 1 := by
    intro h2
    have hdvd : orderOf h.σ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
    rw [h.orderOf_σ] at hdvd
    omega
  have hσ2σ : h.σ ^ 2 ≠ h.σ := by
    intro h2
    have h1 : h.σ * h.σ = h.σ * 1 := by rw [← pow_two, h2, mul_one]
    exact h.hσ1 (mul_left_cancel h1)
  have hset : ({1, h.σ, h.σ ^ 2} : Set G) = (h.U : Set G) := by
    refine Set.eq_of_subset_of_ncard_le ?_ ?_
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact Subgroup.one_mem _
      · exact h.hσU
      · exact Subgroup.pow_mem _ h.hσU 2
    · have hcardU : (h.U : Set G).ncard = 3 := by
        rw [show (h.U : Set G).ncard = Nat.card ↥h.U from rfl, h.hU3]
      have hcardS : ({1, h.σ, h.σ ^ 2} : Set G).ncard = 3 := by
        rw [Set.ncard_insert_of_notMem (by simp [Ne.symm h.hσ1, Ne.symm hσ2ne]),
          Set.ncard_insert_of_notMem (by simp [Ne.symm hσ2σ]), Set.ncard_singleton]
      rw [hcardU, hcardS]
  have hu' : u ∈ ({1, h.σ, h.σ ^ 2} : Set G) := by rw [hset]; exact hu
  simpa using hu'

/-- `u ∈ U`, `u ≠ 1` implies `orderOf u = 3`. -/
theorem orderOf_eq_three_of_mem {u : G} (hu : u ∈ h.U) (hu1 : u ≠ 1) : orderOf u = 3 := by
  have hdvd : orderOf u ∣ 3 := by
    have := Subgroup.orderOf_dvd_natCard h.U hu
    rwa [h.hU3] at this
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact absurd (orderOf_eq_one_iff.mp h1) hu1
  · exact h3

/-- `u ∈ U`, `u ≠ 1` implies `u * u ≠ 1`. -/
theorem sq_ne_one_of_mem {u : G} (hu : u ∈ h.U) (hu1 : u ≠ 1) : u * u ≠ 1 := by
  intro h2
  have h3 : u ^ 2 = 1 := by rw [pow_two]; exact h2
  have hdvd : orderOf u ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h3
  rw [orderOf_eq_three_of_mem h hu hu1] at hdvd
  omega

/-- **The conjugation action of `S` on `U` is trivial or inversion.** -/
theorem conj_dichotomy (hnorm : (h.U.subgroupOf h.C).Normal) {s : G} (hs : s ∈ h.Sg) :
    (∀ u ∈ h.U, s * u * s⁻¹ = u) ∨ (∀ u ∈ h.U, s * u * s⁻¹ = u⁻¹) := by
  have hσmem : s * h.σ * s⁻¹ ∈ h.U := conj_mem_U h hnorm hs h.hσU
  have hσord : orderOf (s * h.σ * s⁻¹) = 3 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, h.orderOf_σ]
  have hσ3 : h.σ ^ 3 = 1 := by
    rw [← h.orderOf_σ]; exact pow_orderOf_eq_one h.σ
  have hconj_sq : s * h.σ ^ 2 * s⁻¹ = (s * h.σ * s⁻¹) ^ 2 := by
    rw [pow_two, pow_two]; group
  rcases U_elements h hσmem with h1 | h2 | h3
  · rw [h1, orderOf_one] at hσord; exact absurd hσord (by norm_num)
  · refine Or.inl (fun u hu => ?_)
    rcases U_elements h hu with hu1 | hu2 | hu3
    · rw [hu1]; simp
    · rw [hu2, h2]
    · rw [hu3, hconj_sq, h2]
  · refine Or.inr (fun u hu => ?_)
    rcases U_elements h hu with hu1 | hu2 | hu3
    · rw [hu1]; simp
    · rw [hu2, h3, sq_eq_inv hσ3]
    · rw [hu3, hconj_sq, h3]
      rw [show (h.σ ^ 2) ^ 2 = h.σ from by
            rw [← pow_mul, show 2 * 2 = 4 from rfl, pow_four_eq_self hσ3],
        inv_sq_eq_self hσ3]

/-- An element of `S` outside `K` inverts `U`. -/
theorem conj_eq_inv_of_notMem_K (hnorm : (h.U.subgroupOf h.C).Normal) {s : G} (hs : s ∈ h.Sg)
    (hsK : s ∉ h.K) : ∀ u ∈ h.U, s * u * s⁻¹ = u⁻¹ := by
  rcases conj_dichotomy h hnorm hs with h1 | h2
  · exact absurd ((mem_K_iff h hs).mpr h1) hsK
  · exact h2

/-- `π ∉ C_S(U)`: `π` does not centralize `σ`, since `C_G(π) = ⟨π⟩` has order `4`. -/
theorem pi_notMem_K : h.π ∉ h.K := by
  intro hπK
  have hconj := (mem_K_iff h h.hπS).mp hπK
  have hcomm : h.π * h.σ = h.σ * h.π := by
    calc h.π * h.σ = (h.π * h.σ * h.π⁻¹) * h.π := by group
      _ = h.σ * h.π := by rw [hconj h.σ h.hσU]
  have hmem : h.σ ∈ Subgroup.zpowers h.π := by
    rw [← h.hCπ, Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact hcomm
  have hle : Subgroup.zpowers h.σ ≤ Subgroup.zpowers h.π := Subgroup.zpowers_le.mpr hmem
  have hdvd : 3 ∣ 4 := by
    have := Subgroup.card_dvd_of_le hle
    rwa [Nat.card_zpowers, Nat.card_zpowers, h.orderOf_σ, h.hπ4] at this
  omega

/-- The number of elements of order `4` of `S` is `2`. -/
theorem card_order_four_Sg : Nat.card {x : G // x ∈ h.Sg ∧ orderOf x = 4} = 2 := by
  obtain ⟨e⟩ := h.hSdih
  rw [← card_order_four_of_iso e]
  rw [show Nat.card {x : ↥h.Sg // orderOf x = 4}
      = Nat.card {x : ↥h.Sg // orderOf ((x : G)) = 4} from
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => by rw [Subgroup.orderOf_coe]))]
  exact (Nat.card_congr (subtypeSubgroupEquiv (H := h.Sg) (p := fun x => orderOf x = 4))).symm

/-- The elements of order `4` of `S` are `π` and `π⁻¹` (`S ≅ D₈`). -/
theorem Sg_order_four_eq {x : G} (hx : x ∈ h.Sg) (hx4 : orderOf x = 4) :
    x = h.π ∨ x = h.π⁻¹ := by
  have hsub : ({h.π, h.π⁻¹} : Set G) ⊆ {y : G | y ∈ h.Sg ∧ orderOf y = 4} := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact ⟨h.hπS, h.hπ4⟩
    · exact ⟨h.Sg.inv_mem h.hπS, by rw [orderOf_inv]; exact h.hπ4⟩
  have hne : h.π ≠ h.π⁻¹ := by
    intro hcon
    have h3 : h.π * h.π = 1 := by
      have h4 := mul_inv_cancel h.π
      rw [← hcon] at h4
      exact h4
    have h2 : h.π ^ 2 = 1 := by rw [pow_two]; exact h3
    have hdvd : orderOf h.π ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
    rw [h.hπ4] at hdvd
    omega
  have hn1 : ({h.π, h.π⁻¹} : Set G).ncard = 2 := Set.ncard_pair hne
  have hn2 : ({y : G | y ∈ h.Sg ∧ orderOf y = 4} : Set G).ncard = 2 := by
    rw [show ({y : G | y ∈ h.Sg ∧ orderOf y = 4} : Set G).ncard
        = Nat.card {y : G // y ∈ h.Sg ∧ orderOf y = 4} from rfl,
      card_order_four_Sg h]
  have heq : ({h.π, h.π⁻¹} : Set G) = {y : G | y ∈ h.Sg ∧ orderOf y = 4} :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hn2, hn1])
  have hxmem : x ∈ ({h.π, h.π⁻¹} : Set G) := by rw [heq]; exact ⟨hx, hx4⟩
  simpa using hxmem

/-- `|C_S(U)| = 4`. -/
theorem K_card (hnorm : (h.U.subgroupOf h.C).Normal) : Nat.card ↥h.K = 4 := by
  have hKle : h.K ≤ h.Sg := inf_le_left
  have hdvd : Nat.card ↥h.K ∣ 8 := by
    have := Subgroup.card_dvd_of_le hKle
    rwa [h.card_Sg] at this
  have hπinv : ∀ u ∈ h.U, h.π⁻¹ * u * h.π = u⁻¹ := by
    intro u hu
    have h1 : h.π * u⁻¹ * h.π⁻¹ = u := by
      rw [conj_eq_inv_of_notMem_K h hnorm h.hπS (pi_notMem_K h) u⁻¹
          (Subgroup.inv_mem _ hu), inv_inv]
    have h2 : u⁻¹ = h.π⁻¹ * u * h.π := by
      calc u⁻¹ = h.π⁻¹ * (h.π * u⁻¹ * h.π⁻¹) * h.π := by group
        _ = h.π⁻¹ * u * h.π := by rw [h1]
    exact h2.symm
  have hcover : (h.Sg : Set G) ⊆ (h.K : Set G) ∪ (fun k => h.π * k) '' (h.K : Set G) := by
    intro t ht
    by_cases htK : t ∈ h.K
    · exact Or.inl htK
    · refine Or.inr ⟨h.π⁻¹ * t, ?_, ?_⟩
      · refine (mem_K_iff h (h.Sg.mul_mem (h.Sg.inv_mem h.hπS) ht)).mpr (fun u hu => ?_)
        have ht' := conj_eq_inv_of_notMem_K h hnorm ht htK u hu
        calc (h.π⁻¹ * t) * u * (h.π⁻¹ * t)⁻¹ = h.π⁻¹ * (t * u * t⁻¹) * h.π := by group
          _ = h.π⁻¹ * u⁻¹ * h.π := by rw [ht']
          _ = u := by rw [hπinv u⁻¹ (Subgroup.inv_mem _ hu), inv_inv]
      · show h.π * (h.π⁻¹ * t) = t
        group
  have hcard_le : Nat.card ↥h.Sg ≤ 2 * Nat.card ↥h.K := by
    have h1 : (h.Sg : Set G).ncard
        ≤ ((h.K : Set G) ∪ (fun k => h.π * k) '' (h.K : Set G)).ncard :=
      Set.ncard_le_ncard hcover
    have h2 : ((h.K : Set G) ∪ (fun k => h.π * k) '' (h.K : Set G)).ncard
        ≤ (h.K : Set G).ncard + ((fun k => h.π * k) '' (h.K : Set G)).ncard :=
      Set.ncard_union_le _ _
    have h3 : ((fun k => h.π * k) '' (h.K : Set G)).ncard = (h.K : Set G).ncard :=
      Set.ncard_image_of_injective _ (fun a b hab => mul_left_cancel hab)
    rw [show (h.Sg : Set G).ncard = Nat.card ↥h.Sg from rfl] at h1
    rw [show (h.K : Set G).ncard = Nat.card ↥h.K from rfl] at h2 h3
    rw [h3] at h2
    have h4 : Nat.card ↥h.Sg ≤ Nat.card ↥h.K + Nat.card ↥h.K := le_trans h1 h2
    rw [h.card_Sg] at h4
    have : Nat.card ↥h.K + Nat.card ↥h.K = 2 * Nat.card ↥h.K := by ring
    omega
  have hge : 4 ≤ Nat.card ↥h.K := by
    have := hcard_le
    rw [h.card_Sg] at this
    omega
  have hne8 : Nat.card ↥h.K ≠ 8 := by
    intro h8
    have hKS : h.K = h.Sg := Subgroup.eq_of_le_of_card_ge hKle (by rw [h8, h.card_Sg])
    exact pi_notMem_K h (hKS ▸ h.hπS)
  obtain ⟨k, hk, hk2⟩ :=
    (Nat.dvd_prime_pow Nat.prime_two).mp (show Nat.card ↥h.K ∣ 2 ^ 3 by simpa using hdvd)
  have hkk : 2 ≤ k := by
    rw [hk2] at hge
    by_contra hcon
    have hk1 : k ≤ 1 := by omega
    interval_cases k <;> norm_num at hge
  have hk3 : k ≠ 3 := by
    intro h3
    exact hne8 (by rw [hk2, h3]; norm_num)
  have hk_eq : k = 2 := by omega
  rw [hk2, hk_eq]
  norm_num

/-- Every element of `K` is an involution. -/
theorem K_sq_eq_one (hnorm : (h.U.subgroupOf h.C).Normal) : ∀ x ∈ h.K, x ^ 2 = 1 := by
  intro x hxK
  have hxS : x ∈ h.Sg := hxK.1
  have hdvd : orderOf x ∣ 4 := by
    have := Subgroup.orderOf_dvd_natCard h.K hxK
    rwa [K_card h hnorm] at this
  have hx4 : orderOf x ≠ 4 := by
    intro h4
    rcases Sg_order_four_eq h hxS h4 with hx1 | hx2
    · exact pi_notMem_K h (hx1 ▸ hxK)
    · have hinv : h.π = x⁻¹ := by rw [hx2, inv_inv]
      exact pi_notMem_K h (hinv ▸ h.K.inv_mem hxK)
  have h2 : orderOf x ∣ 2 := by
    obtain ⟨k, hk, hk2⟩ :=
      (Nat.dvd_prime_pow Nat.prime_two).mp (show orderOf x ∣ 2 ^ 2 by simpa using hdvd)
    rw [hk2]
    interval_cases k
    · norm_num
    · norm_num
    · exact absurd (by rw [hk2]; norm_num) hx4
  exact orderOf_dvd_iff_pow_eq_one.mp h2

/-- The elements of `C` have a unique decomposition `u * s`, `u ∈ U`, `s ∈ S`. -/
theorem decomp (hnorm : (h.U.subgroupOf h.C).Normal) {x : G} (hx : x ∈ h.C) :
    ∃! p : G × G, p.1 ∈ h.U ∧ p.2 ∈ h.Sg ∧ x = p.1 * p.2 := by
  haveI := hnorm
  have hsup : (h.U ⊔ h.Sg).subgroupOf h.C = ⊤ := by
    rw [← h.hC, Subgroup.subgroupOf_self]
  have htop : (h.U.subgroupOf h.C) ⊔ (h.Sg.subgroupOf h.C) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup h.U_le_C h.Sg_le_C, hsup]
  have hmem : (⟨x, hx⟩ : ↥h.C) ∈
      ((h.U.subgroupOf h.C : Set ↥h.C) * (h.Sg.subgroupOf h.C : Set ↥h.C)) := by
    rw [← Subgroup.normal_mul (h.U.subgroupOf h.C) (h.Sg.subgroupOf h.C), htop]
    exact Subgroup.mem_top _
  rw [Set.mem_mul] at hmem
  obtain ⟨u, hu, s, hs, hus⟩ := hmem
  have huG : (u : G) ∈ h.U := Subgroup.mem_subgroupOf.mp hu
  have hsG : (s : G) ∈ h.Sg := Subgroup.mem_subgroupOf.mp hs
  have hxs : x = (u : G) * (s : G) := by
    have := congrArg (fun z : ↥h.C => (z : G)) hus
    simpa using this.symm
  refine ⟨((u : G), (s : G)), ⟨huG, hsG, hxs⟩, ?_⟩
  rintro ⟨u', s'⟩ ⟨hu', hs', hxs'⟩
  have heq : (u : G) * (s : G) = u' * s' := by rw [← hxs, hxs']
  have h1 : u'⁻¹ * (u : G) = s' * (s : G)⁻¹ := by
    calc u'⁻¹ * (u : G) = u'⁻¹ * ((u : G) * (s : G)) * (s : G)⁻¹ := by group
      _ = u'⁻¹ * (u' * s') * (s : G)⁻¹ := by rw [heq]
      _ = s' * (s : G)⁻¹ := by group
  have h2 : u'⁻¹ * (u : G) ∈ h.U := h.U.mul_mem (h.U.inv_mem hu') huG
  have h3 : u'⁻¹ * (u : G) ∈ h.Sg := by rw [h1]; exact h.Sg.mul_mem hs' (h.Sg.inv_mem hsG)
  have h4 : u'⁻¹ * (u : G) ∈ (⊥ : Subgroup G) := by
    rw [← h.U_inf_Sg]; exact ⟨h2, h3⟩
  have h5 : u'⁻¹ * (u : G) = 1 := Subgroup.mem_bot.mp h4
  have hu_eq : (u : G) = u' := (inv_mul_eq_one.mp h5).symm
  have hs_eq : (s : G) = s' := by
    have hh := heq
    rw [← hu_eq] at hh
    exact mul_left_cancel hh
  exact Prod.ext hu_eq.symm hs_eq.symm

/-! ## Counting -/

/-- Splitting a set by a further predicate. -/
theorem ncard_split {α : Type*} [Finite α] (P R : α → Prop) :
    ({a : α | P a} : Set α).ncard =
      ({a : α | P a ∧ R a} : Set α).ncard + ({a : α | P a ∧ ¬R a} : Set α).ncard := by
  have h1 : ({a : α | P a ∧ R a} : Set α) ∪ {a : α | P a ∧ ¬R a} = {a : α | P a} := by
    ext a
    constructor
    · rintro (hh | hh)
      · exact hh.1
      · exact hh.1
    · intro ha
      by_cases hR : R a
      · exact Or.inl ⟨ha, hR⟩
      · exact Or.inr ⟨ha, hR⟩
  have h2 : ({a : α | P a ∧ R a} : Set α) ∩ {a : α | P a ∧ ¬R a} = ∅ := by
    ext a
    constructor
    · rintro ⟨⟨-, hR⟩, ⟨-, hnR⟩⟩; exact absurd hR hnR
    · intro hh; exact absurd hh (Set.notMem_empty a)
  have h3 := Set.ncard_union_add_ncard_inter ({a : α | P a ∧ R a} : Set α)
    ({a : α | P a ∧ ¬R a} : Set α)
  rw [h1, h2, Set.ncard_empty, add_zero] at h3
  exact h3

/-- `Nat.card` version of `ncard_split`. -/
theorem card_split {α : Type*} [Finite α] (P R : α → Prop) :
    Nat.card {a : α // P a} =
      Nat.card {a : α // P a ∧ R a} + Nat.card {a : α // P a ∧ ¬R a} := by
  have := ncard_split P R
  rwa [show ({a : α | P a} : Set α).ncard = Nat.card {a : α // P a} from rfl,
    show ({a : α | P a ∧ R a} : Set α).ncard = Nat.card {a : α // P a ∧ R a} from rfl,
    show ({a : α | P a ∧ ¬R a} : Set α).ncard = Nat.card {a : α // P a ∧ ¬R a} from rfl] at this

/-- The involutions of `S`: there are `5`. -/
theorem card_involutions_Sg : Nat.card {s : G // s ∈ h.Sg ∧ orderOf s = 2} = 5 := by
  obtain ⟨e⟩ := h.hSdih
  rw [← card_involutions_of_iso e]
  rw [show Nat.card {x : ↥h.Sg // orderOf x = 2}
      = Nat.card {x : ↥h.Sg // orderOf ((x : G)) = 2} from
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => by rw [Subgroup.orderOf_coe]))]
  exact (Nat.card_congr (subtypeSubgroupEquiv (H := h.Sg) (p := fun x => orderOf x = 2))).symm

/-- The involutions of `K`: there are `3` (a four-group). -/
theorem card_involutions_K (hnorm : (h.U.subgroupOf h.C).Normal) :
    Nat.card {x : G // x ∈ h.K ∧ orderOf x = 2} = 3 := by
  rw [show Nat.card {x : G // x ∈ h.K ∧ orderOf x = 2}
      = Nat.card {y : ↥h.K // orderOf ((y : G)) = 2} from
    (Nat.card_congr (subtypeSubgroupEquiv (H := h.K) (p := fun x => orderOf x = 2))).symm]
  rw [show Nat.card {y : ↥h.K // orderOf ((y : G)) = 2} = Nat.card {y : ↥h.K // y ≠ 1} from
    Nat.card_congr (Equiv.subtypeEquivRight (fun y => ?_))]
  · calc Nat.card {y : ↥h.K // y ≠ 1} = ({y : ↥h.K | y ≠ 1} : Set ↥h.K).ncard := rfl
      _ = ((Set.univ : Set ↥h.K) \ {(1 : ↥h.K)}).ncard := by
          rw [show ({y : ↥h.K | y ≠ 1} : Set ↥h.K) = (Set.univ : Set ↥h.K) \ {(1 : ↥h.K)}
            from by ext y; simp]
      _ = (Set.univ : Set ↥h.K).ncard - ({(1 : ↥h.K)} : Set ↥h.K).ncard :=
          Set.ncard_sdiff (Set.subset_univ _)
      _ = Nat.card ↥h.K - 1 := by rw [Set.ncard_univ, Set.ncard_singleton]
      _ = 3 := by rw [K_card h hnorm]
  · constructor
    · rintro h2 h1
      rw [h1, Subgroup.coe_one, orderOf_one] at h2
      exact absurd h2 (by norm_num)
    · intro hy1
      rw [orderOf_eq_two_iff']
      refine ⟨fun h => hy1 (Subtype.ext (by rw [h, Subgroup.coe_one])), ?_⟩
      have hK := K_sq_eq_one h hnorm (y : G) y.2
      rw [pow_two] at hK
      exact hK

/-- The involutions of `S` outside `K`: there are `2`. -/
theorem card_involutions_Sg_notMem_K (hnorm : (h.U.subgroupOf h.C).Normal) :
    Nat.card {s : G // s ∈ h.Sg ∧ orderOf s = 2 ∧ s ∉ h.K} = 2 := by
  have hsplit := card_split (fun s : G => s ∈ h.Sg ∧ orderOf s = 2) (fun s => s ∈ h.K)
  have h1 : Nat.card {s : G // s ∈ h.Sg ∧ orderOf s = 2} = 5 := card_involutions_Sg h
  have h2 : Nat.card {s : G // (s ∈ h.Sg ∧ orderOf s = 2) ∧ s ∈ h.K} = 3 := by
    rw [show Nat.card {s : G // (s ∈ h.Sg ∧ orderOf s = 2) ∧ s ∈ h.K}
        = Nat.card {s : G // s ∈ h.K ∧ orderOf s = 2} from
      Nat.card_congr (Equiv.subtypeEquivRight (fun s => ?_))]
    · exact card_involutions_K h hnorm
    · constructor
      · rintro ⟨⟨-, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h3, h2⟩; exact ⟨⟨h3.1, h2⟩, h3⟩
  rw [show Nat.card {s : G // s ∈ h.Sg ∧ orderOf s = 2 ∧ s ∉ h.K}
      = Nat.card {s : G // (s ∈ h.Sg ∧ orderOf s = 2) ∧ ¬ (s ∈ h.K)} from
    Nat.card_congr (Equiv.subtypeEquivRight (fun s => ⟨
      fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩))]
  rw [h1, h2] at hsplit
  omega

/-- The nonidentity elements of `U`: there are `2`. -/
theorem card_nonid_U : Nat.card {u : G // u ∈ h.U ∧ u ≠ 1} = 2 := by
  rw [show Nat.card {u : G // u ∈ h.U ∧ u ≠ 1} = Nat.card {x : ↥h.U // (x : G) ≠ 1} from
    (Nat.card_congr (subtypeSubgroupEquiv (H := h.U) (p := fun x => x ≠ 1))).symm]
  rw [show Nat.card {x : ↥h.U // (x : G) ≠ 1} = Nat.card {x : ↥h.U // x ≠ 1} from
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => ⟨
      fun h h1 => h (by rw [h1, Subgroup.coe_one]),
      fun h h1 => h (Subtype.ext (by rw [h1, Subgroup.coe_one]))⟩))]
  calc Nat.card {x : ↥h.U // x ≠ 1} = ({x : ↥h.U | x ≠ 1} : Set ↥h.U).ncard := rfl
    _ = ((Set.univ : Set ↥h.U) \ {(1 : ↥h.U)}).ncard := by
        rw [show ({x : ↥h.U | x ≠ 1} : Set ↥h.U) = (Set.univ : Set ↥h.U) \ {(1 : ↥h.U)}
          from by ext y; simp]
    _ = (Set.univ : Set ↥h.U).ncard - ({(1 : ↥h.U)} : Set ↥h.U).ncard :=
        Set.ncard_sdiff (Set.subset_univ _)
    _ = Nat.card ↥h.U - 1 := by rw [Set.ncard_univ, Set.ncard_singleton]
    _ = 2 := by rw [h.hU3]

/-- **The criterion.**  `u * s` (`u ∈ U`, `s ∈ S`) is an involution iff `s` is an involution and
`u = 1` or `s` inverts `U`. -/
theorem orderOf_mul_eq_two_iff (hnorm : (h.U.subgroupOf h.C).Normal) {u s : G} (hu : u ∈ h.U)
    (hs : s ∈ h.Sg) :
    orderOf (u * s) = 2 ↔
      (u = 1 ∧ orderOf s = 2) ∨ (u ≠ 1 ∧ orderOf s = 2 ∧ s ∉ h.K) := by
  have hsq : (u * s) * (u * s) = u * (s * u * s⁻¹) * (s * s) := by group
  have hsq1 : ((u * s) * (u * s) = 1) ↔ (s * s = 1 ∧ (u = 1 ∨ s ∉ h.K)) := by
    rcases conj_dichotomy h hnorm hs with hcen | hinv
    · have hmem : s ∈ h.K := (mem_K_iff h hs).mpr hcen
      have hsq' : (u * s) * (u * s) = (u * u) * (s * s) := by rw [hsq, hcen u hu]
      by_cases hu1 : u = 1
      · subst hu1
        simp
      · have hL : ¬ ((u * s) * (u * s) = 1) := by
          intro h1
          have h2 : (u * u) * (s * s) = 1 := by rw [← hsq']; exact h1
          have heq : u * u = (s * s)⁻¹ := mul_eq_one_iff_eq_inv.mp h2
          have hmem2 : u * u ∈ h.U ⊓ h.Sg := by
            refine ⟨h.U.mul_mem hu hu, ?_⟩
            rw [heq]; exact h.Sg.inv_mem (h.Sg.mul_mem hs hs)
          have hbot : u * u ∈ (⊥ : Subgroup G) := by rw [← h.U_inf_Sg]; exact hmem2
          exact sq_ne_one_of_mem h hu hu1 (Subgroup.mem_bot.mp hbot)
        have hR : ¬ (s * s = 1 ∧ (u = 1 ∨ s ∉ h.K)) :=
          fun hc => hc.2.elim hu1 (fun hsK => hsK hmem)
        exact ⟨fun h => absurd h hL, fun h => absurd h hR⟩
    · have hsK' : s ∉ h.K := by
        intro hsK
        have h1 := (mem_K_iff h hs).mp hsK h.σ h.hσU
        have h2 := hinv h.σ h.hσU
        have h3 : s * h.σ * s⁻¹ = h.σ := h1
        rw [h2] at h3
        have heq : h.σ = h.σ⁻¹ := h3.symm
        have h4 : h.σ * h.σ = 1 := by
          have h5 := mul_inv_cancel h.σ
          rw [← heq] at h5
          exact h5
        exact sq_ne_one_of_mem h h.hσU h.hσ1 h4
      have hsq' : (u * s) * (u * s) = s * s := by rw [hsq, hinv u hu]; group
      rw [hsq']
      exact ⟨fun h => ⟨h, Or.inr hsK'⟩, fun h => h.1⟩
  rw [orderOf_eq_two_iff', hsq1]
  constructor
  · rintro ⟨hne, hs2, hdisj⟩
    by_cases hu1 : u = 1
    · refine Or.inl ⟨hu1, orderOf_eq_two_iff'.mpr ⟨?_, hs2⟩⟩
      intro hs1
      exact hne (by rw [hu1, hs1, mul_one])
    · refine Or.inr ⟨hu1, orderOf_eq_two_iff'.mpr ⟨?_, hs2⟩,
        hdisj.elim (fun h => absurd h hu1) id⟩
      intro hs1
      exact (hdisj.elim (fun h => absurd h hu1) id)
        (by rw [hs1]; exact ⟨h.Sg.one_mem, Subgroup.one_mem _⟩)
  · rintro (⟨hu1, hs2⟩ | ⟨hu1, hs2, hsK⟩)
    · subst hu1
      refine ⟨?_, (orderOf_eq_two_iff'.mp hs2).2, Or.inl rfl⟩
      intro h1
      exact (orderOf_eq_two_iff'.mp hs2).1 (by rw [one_mul] at h1; exact h1)
    · refine ⟨?_, (orderOf_eq_two_iff'.mp hs2).2, Or.inr hsK⟩
      intro h1
      have heq : u = s⁻¹ := mul_eq_one_iff_eq_inv.mp h1
      have hmem : u ∈ h.U ⊓ h.Sg := ⟨hu, by rw [heq]; exact h.Sg.inv_mem hs⟩
      have hbot : u ∈ (⊥ : Subgroup G) := by rw [← h.U_inf_Sg]; exact hmem
      exact hu1 (Subgroup.mem_bot.mp hbot)

/-- **The number of involutions of `C_G(z)`, assuming `U ⊴ C_G(z)`, is `9`.** -/
theorem cardInvolutionsCentralizer_of_normal (hnorm : (h.U.subgroupOf h.C).Normal) :
    Nat.card {x : G // x ∈ h.C ∧ orderOf x = 2} = 9 := by
  -- Step 1: the involutions of `C` are exactly the decompositions `u * s` that are involutions.
  have step1 : Nat.card {x : G // x ∈ h.C ∧ orderOf x = 2} =
      Nat.card {p : G × G // p.1 ∈ h.U ∧ p.2 ∈ h.Sg ∧ orderOf (p.1 * p.2) = 2} := by
    let f : {p : G × G // p.1 ∈ h.U ∧ p.2 ∈ h.Sg ∧ orderOf (p.1 * p.2) = 2} →
        {x : G // x ∈ h.C ∧ orderOf x = 2} := fun p =>
      ⟨p.1.1 * p.1.2, h.C.mul_mem (h.U_le_C p.2.1) (h.Sg_le_C p.2.2.1), p.2.2.2⟩
    refine (Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)).symm
    · intro p q hpq
      have h1 : p.1.1 * p.1.2 = q.1.1 * q.1.2 := congrArg Subtype.val hpq
      have h2 : q.1.1⁻¹ * p.1.1 = q.1.2 * p.1.2⁻¹ := by
        calc q.1.1⁻¹ * p.1.1 = q.1.1⁻¹ * (p.1.1 * p.1.2) * p.1.2⁻¹ := by group
          _ = q.1.1⁻¹ * (q.1.1 * q.1.2) * p.1.2⁻¹ := by rw [h1]
          _ = q.1.2 * p.1.2⁻¹ := by group
      have h3 : q.1.1⁻¹ * p.1.1 ∈ h.U := h.U.mul_mem (h.U.inv_mem q.2.1) p.2.1
      have h4 : q.1.1⁻¹ * p.1.1 ∈ h.Sg := by
        rw [h2]; exact h.Sg.mul_mem q.2.2.1 (h.Sg.inv_mem p.2.2.1)
      have h5 : q.1.1⁻¹ * p.1.1 = 1 := by
        have hmem : q.1.1⁻¹ * p.1.1 ∈ (⊥ : Subgroup G) := by
          rw [← h.U_inf_Sg]; exact ⟨h3, h4⟩
        exact Subgroup.mem_bot.mp hmem
      have h6 : p.1.1 = q.1.1 := (inv_mul_eq_one.mp h5).symm
      have h7 : p.1.2 = q.1.2 := by
        have hh := h1
        rw [← h6] at hh
        exact mul_left_cancel hh
      exact Subtype.ext (Prod.ext h6 h7)
    · intro x
      obtain ⟨p, hp, -⟩ := decomp h hnorm x.2.1
      refine ⟨⟨(p.1, p.2), hp.1, hp.2.1, ?_⟩, ?_⟩
      · rw [show (p.1, p.2).1 * (p.1, p.2).2 = p.1 * p.2 from rfl, ← hp.2.2]
        exact x.2.2
      · refine Subtype.ext ?_
        exact hp.2.2.symm
  -- Step 2: split off `u = 1`.
  have step2 : Nat.card {p : G × G // p.1 ∈ h.U ∧ p.2 ∈ h.Sg ∧ orderOf (p.1 * p.2) = 2} =
      Nat.card {p : G × G // p.1 ∈ h.U ∧ p.2 ∈ h.Sg ∧ orderOf (p.1 * p.2) = 2 ∧ p.1 = 1} +
      Nat.card {p : G × G // p.1 ∈ h.U ∧ p.2 ∈ h.Sg ∧ orderOf (p.1 * p.2) = 2 ∧ p.1 ≠ 1} :=
    by
      simpa only [and_assoc] using
        card_split (fun p : G × G => p.1 ∈ h.U ∧ p.2 ∈ h.Sg ∧ orderOf (p.1 * p.2) = 2)
          (fun p => p.1 = 1)
  -- The `u = 1` part: the involutions of `S` (there are `5`).
  have hP0 : Nat.card {p : G × G // p.1 ∈ h.U ∧ p.2 ∈ h.Sg ∧ orderOf (p.1 * p.2) = 2 ∧ p.1 = 1}
      = 5 := by
    rw [show Nat.card {p : G × G // p.1 ∈ h.U ∧ p.2 ∈ h.Sg ∧
          orderOf (p.1 * p.2) = 2 ∧ p.1 = 1} = Nat.card {s : G // s ∈ h.Sg ∧ orderOf s = 2}
        from Nat.card_congr ?_]
    · exact card_involutions_Sg h
    refine
      { toFun := fun p => ⟨p.1.2, p.2.2.1, by
          have h1 := p.2.2.2.1
          rw [p.2.2.2.2, one_mul] at h1
          exact h1⟩
        invFun := fun s => ⟨(1, s.1), h.U.one_mem, s.2.1, by rw [one_mul]; exact s.2.2, rfl⟩
        left_inv := fun p => Subtype.ext (Prod.ext p.2.2.2.2.symm rfl)
        right_inv := fun s => Subtype.ext rfl }
  -- The `u ≠ 1` part: `U ∖ {1}` times the involutions of `S ∖ K` (`2 · 2`).
  have hP1 : Nat.card {p : G × G // p.1 ∈ h.U ∧ p.2 ∈ h.Sg ∧ orderOf (p.1 * p.2) = 2 ∧ p.1 ≠ 1}
      = 2 * 2 := by
    rw [show Nat.card {p : G × G // p.1 ∈ h.U ∧ p.2 ∈ h.Sg ∧ orderOf (p.1 * p.2) = 2 ∧
          p.1 ≠ 1} = Nat.card ({u : G // u ∈ h.U ∧ u ≠ 1} ×
            {s : G // s ∈ h.Sg ∧ orderOf s = 2 ∧ s ∉ h.K}) from Nat.card_congr ?_]
    · rw [Nat.card_prod, card_nonid_U h, card_involutions_Sg_notMem_K h hnorm]
    have haux : ∀ (u s : G), u ∈ h.U → s ∈ h.Sg → u ≠ 1 → orderOf (u * s) = 2 →
        orderOf s = 2 ∧ s ∉ h.K := by
      intro u s hu' hs' hu1' hord
      rcases (orderOf_mul_eq_two_iff h hnorm hu' hs').mp hord with hh | hh
      · exact absurd hh.1 hu1'
      · exact ⟨hh.2.1, hh.2.2⟩
    refine
      { toFun := fun p => (⟨p.1.1, p.2.1, p.2.2.2.2⟩,
          ⟨p.1.2, p.2.2.1, haux p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2.2 p.2.2.2.1⟩)
        invFun := fun q => ⟨(q.1.1, q.2.1), q.1.2.1, q.2.2.1,
          (orderOf_mul_eq_two_iff h hnorm q.1.2.1 q.2.2.1).mpr
            (Or.inr ⟨q.1.2.2, q.2.2.2.1, q.2.2.2.2⟩), q.1.2.2⟩
        left_inv := fun p => Subtype.ext (Prod.ext rfl rfl)
        right_inv := fun q => Prod.ext rfl rfl }
  have hfinal : Nat.card {x : G // x ∈ h.C ∧ orderOf x = 2} = 5 + 2 * 2 := by
    rw [step1, step2, hP0, hP1]
  calc Nat.card {x : G // x ∈ h.C ∧ orderOf x = 2} = 5 + 2 * 2 := hfinal
    _ = 9 := by norm_num


/-! ## Companion count: the involutions of `C` inverting `σ` -/

/-- `U` is abelian. -/
theorem conj_eq_self_of_mem_U {u v : G} (hu : u ∈ h.U) (hv : v ∈ h.U) : u * v * u⁻¹ = v := by
  rw [h.U_eq_zpowers] at hu hv
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  group

/-- An element of `S` inverts `σ` iff it lies outside `K`. -/
theorem conj_σ_eq_inv_iff_notMem_K (hnorm : (h.U.subgroupOf h.C).Normal) {s : G}
    (hs : s ∈ h.Sg) : s * h.σ * s⁻¹ = h.σ⁻¹ ↔ s ∉ h.K := by
  have hσne : h.σ ≠ h.σ⁻¹ := by
    intro hcon
    have h3 : h.σ * h.σ = 1 := by
      have h4 := mul_inv_cancel h.σ
      rw [← hcon] at h4
      exact h4
    exact sq_ne_one_of_mem h h.hσU h.hσ1 h3
  constructor
  · intro hinv hsK
    have h1 := (mem_K_iff h hs).mp hsK h.σ h.hσU
    exact hσne (by rw [← hinv, h1])
  · intro hsK
    exact conj_eq_inv_of_notMem_K h hnorm hs hsK h.σ h.hσU

/-- An element `u * s` (`u ∈ U`, `s ∈ S`) inverts `σ` iff `s` does. -/
theorem conj_σ_inv_iff (hnorm : (h.U.subgroupOf h.C).Normal) {u s : G} (hu : u ∈ h.U)
    (hs : s ∈ h.Sg) :
    (u * s) * h.σ * (u * s)⁻¹ = h.σ⁻¹ ↔ s * h.σ * s⁻¹ = h.σ⁻¹ := by
  have h1 : (u * s) * h.σ * (u * s)⁻¹ = u * (s * h.σ * s⁻¹) * u⁻¹ := by group
  rw [h1, conj_eq_self_of_mem_U h hu (conj_mem_U h hnorm hs h.hσU)]

/-- **The number of involutions of `C` inverting `σ` is `6`.** -/
theorem card_involutions_inverting_σ (hnorm : (h.U.subgroupOf h.C).Normal) :
    Nat.card {a : G // a ∈ h.C ∧ orderOf a = 2 ∧ a * h.σ * a⁻¹ = h.σ⁻¹} = 6 := by
  -- Step 1: pass to the decomposition `u * s`.
  have step1 : Nat.card {a : G // a ∈ h.C ∧ orderOf a = 2 ∧ a * h.σ * a⁻¹ = h.σ⁻¹} =
      Nat.card {p : G × G // p.1 ∈ h.U ∧ p.2 ∈ h.Sg ∧ orderOf (p.1 * p.2) = 2 ∧
        (p.1 * p.2) * h.σ * (p.1 * p.2)⁻¹ = h.σ⁻¹} := by
    let f : {p : G × G // p.1 ∈ h.U ∧ p.2 ∈ h.Sg ∧ orderOf (p.1 * p.2) = 2 ∧
        (p.1 * p.2) * h.σ * (p.1 * p.2)⁻¹ = h.σ⁻¹} →
        {a : G // a ∈ h.C ∧ orderOf a = 2 ∧ a * h.σ * a⁻¹ = h.σ⁻¹} := fun p =>
      ⟨p.1.1 * p.1.2, h.C.mul_mem (h.U_le_C p.2.1) (h.Sg_le_C p.2.2.1), p.2.2.2.1, p.2.2.2.2⟩
    refine (Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)).symm
    · intro p q hpq
      have h1 : p.1.1 * p.1.2 = q.1.1 * q.1.2 := congrArg Subtype.val hpq
      have h2 : q.1.1⁻¹ * p.1.1 = q.1.2 * p.1.2⁻¹ := by
        calc q.1.1⁻¹ * p.1.1 = q.1.1⁻¹ * (p.1.1 * p.1.2) * p.1.2⁻¹ := by group
          _ = q.1.1⁻¹ * (q.1.1 * q.1.2) * p.1.2⁻¹ := by rw [h1]
          _ = q.1.2 * p.1.2⁻¹ := by group
      have h3 : q.1.1⁻¹ * p.1.1 ∈ h.U := h.U.mul_mem (h.U.inv_mem q.2.1) p.2.1
      have h4 : q.1.1⁻¹ * p.1.1 ∈ h.Sg := by
        rw [h2]; exact h.Sg.mul_mem q.2.2.1 (h.Sg.inv_mem p.2.2.1)
      have h5 : q.1.1⁻¹ * p.1.1 = 1 := by
        have hmem : q.1.1⁻¹ * p.1.1 ∈ (⊥ : Subgroup G) := by
          rw [← h.U_inf_Sg]; exact ⟨h3, h4⟩
        exact Subgroup.mem_bot.mp hmem
      have h6 : p.1.1 = q.1.1 := (inv_mul_eq_one.mp h5).symm
      have h7 : p.1.2 = q.1.2 := by
        have hh := h1
        rw [← h6] at hh
        exact mul_left_cancel hh
      exact Subtype.ext (Prod.ext h6 h7)
    · intro x
      obtain ⟨p, hp, -⟩ := decomp h hnorm x.2.1
      refine ⟨⟨(p.1, p.2), hp.1, hp.2.1, ?_, ?_⟩, ?_⟩
      · rw [show (p.1, p.2).1 * (p.1, p.2).2 = p.1 * p.2 from rfl, ← hp.2.2]
        exact x.2.2.1
      · rw [show (p.1, p.2).1 * (p.1, p.2).2 = p.1 * p.2 from rfl, ← hp.2.2]
        exact x.2.2.2
      · refine Subtype.ext ?_
        exact hp.2.2.symm
  -- Step 2: the pair condition is `u ∈ U`, `s ∈ S`, `s` an involution outside `K`.
  have step2 : Nat.card {p : G × G // p.1 ∈ h.U ∧ p.2 ∈ h.Sg ∧ orderOf (p.1 * p.2) = 2 ∧
        (p.1 * p.2) * h.σ * (p.1 * p.2)⁻¹ = h.σ⁻¹} =
      Nat.card ({u : G // u ∈ h.U} × {s : G // s ∈ h.Sg ∧ orderOf s = 2 ∧ s ∉ h.K}) := by
    refine Nat.card_congr ?_
    have haux : ∀ {u s : G}, u ∈ h.U → s ∈ h.Sg → orderOf (u * s) = 2 →
        (u * s) * h.σ * (u * s)⁻¹ = h.σ⁻¹ → orderOf s = 2 ∧ s ∉ h.K := by
      intro u s hu' hs' hord hinv
      have hsK : s ∉ h.K :=
        (conj_σ_eq_inv_iff_notMem_K h hnorm hs').mp
          ((conj_σ_inv_iff h hnorm hu' hs').mp hinv)
      have hsq' : (u * s) * (u * s) = s * s := by
        rw [show (u * s) * (u * s) = u * (s * u * s⁻¹) * (s * s) from by group,
          conj_eq_inv_of_notMem_K h hnorm hs' hsK u hu']
        group
      have hs2 : s * s = 1 := by
        have h1 := (orderOf_eq_two_iff'.mp hord).2
        rwa [hsq'] at h1
      refine ⟨orderOf_eq_two_iff'.mpr ⟨?_, hs2⟩, hsK⟩
      intro hs1
      exact hsK (by rw [hs1]; exact ⟨h.Sg.one_mem, Subgroup.one_mem _⟩)
    refine
      { toFun := fun p => (⟨p.1.1, p.2.1⟩,
          ⟨p.1.2, p.2.2.1, haux p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2⟩)
        invFun := fun q => by
          refine ⟨(q.1.1, q.2.1), q.1.2, q.2.2.1, ?_, ?_⟩
          · by_cases hu1 : q.1.1 = 1
            · exact (orderOf_mul_eq_two_iff h hnorm q.1.2 q.2.2.1).mpr
                (Or.inl ⟨hu1, q.2.2.2.1⟩)
            · exact (orderOf_mul_eq_two_iff h hnorm q.1.2 q.2.2.1).mpr
                (Or.inr ⟨hu1, q.2.2.2.1, q.2.2.2.2⟩)
          · exact (conj_σ_inv_iff h hnorm q.1.2 q.2.2.1).mpr
              ((conj_σ_eq_inv_iff_notMem_K h hnorm q.2.2.1).mpr q.2.2.2.2)
        left_inv := fun p => Subtype.ext (Prod.ext rfl rfl)
        right_inv := fun q => Prod.ext rfl rfl }
  have hval : Nat.card {a : G // a ∈ h.C ∧ orderOf a = 2 ∧ a * h.σ * a⁻¹ = h.σ⁻¹}
      = Nat.card {u : G // u ∈ h.U} * 2 := by
    rw [step1, step2, Nat.card_prod, card_involutions_Sg_notMem_K h hnorm]
  have hU3 : Nat.card {u : G // u ∈ h.U} = 3 := h.hU3
  calc Nat.card {a : G // a ∈ h.C ∧ orderOf a = 2 ∧ a * h.σ * a⁻¹ = h.σ⁻¹}
      = Nat.card {u : G // u ∈ h.U} * 2 := hval
    _ = 3 * 2 := by rw [hU3]
    _ = 6 := by norm_num

end A7InvCtx

end Work.A7REC.Char
