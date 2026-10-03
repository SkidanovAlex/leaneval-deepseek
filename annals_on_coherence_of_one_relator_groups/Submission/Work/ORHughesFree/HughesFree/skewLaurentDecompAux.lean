/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Auxiliary data for the skew Laurent decomposition `K[H] ≅ K[N][t^{±1}; τ]`

Let `N ⊴ H ≤ G`, `t : H`, and assume that every `h : H` can be written uniquely as
`h = n * t ^ k` with `n : N`, `k : ℤ` (i.e. `H = N ⋊ ⟨t⟩`).  Then `K[H]` is the skew
Laurent polynomial ring over `K[N]` with variable `t` and twist given by the action of
`Multiplicative ℤ` on `MonoidAlgebra K N`.

This file collects the two mutually inverse `K`-algebra homomorphisms

* `Phi : K[N][t^{±1}; τ] →ₐ[K] K[H]`  (the "evaluation" of the skew Laurent polynomial ring),
* `Psi : K[H] →ₐ[K] K[N][t^{±1}; τ]`  (the decomposition `n * t ^ k ↦ n t ^ k`)

together with their basic properties, so that a later file can assemble the ring equivalence.
-/
import Mathlib
import Submission.Work.ORHughesFree.HughesFree

set_option autoImplicit false

namespace Work.ORHughesFree.HughesFree

/-! ## The group-like element `t ^ k` of `K[H]` -/

/-- The monoid homomorphism `Multiplicative ℤ →* H`, `k ↦ t ^ k`. -/
noncomputable def zpowMonoidHom {G : Type} [Group G] {H : Subgroup G} (t : H) :
    Multiplicative ℤ →* H where
  toFun k := t ^ (Multiplicative.toAdd k)
  map_one' := by simp
  map_mul' x y := by
    show t ^ (Multiplicative.toAdd (x * y)) =
      t ^ (Multiplicative.toAdd x) * t ^ (Multiplicative.toAdd y)
    rw [toAdd_mul, zpow_add]

/-- The group-like element of `K[H]` corresponding to `t ^ k`. -/
noncomputable def genT (K : Type) [Field K] {G : Type} [Group G] {H : Subgroup G} (t : H) :
    Multiplicative ℤ →* MonoidAlgebra K H :=
  (MonoidAlgebra.of K H).comp (zpowMonoidHom t)

theorem genT_ofAdd (K : Type) [Field K] {G : Type} [Group G] {H : Subgroup G} (t : H) (k : ℤ) :
    genT K t (Multiplicative.ofAdd k) = MonoidAlgebra.single (t ^ k) (1 : K) := by
  simp [genT, zpowMonoidHom, MonoidAlgebra.of_apply]

/-! ## The two algebra homomorphisms -/

/-- The inclusion `K[N] →+* K[H]` induced by `N ≤ H`. -/
noncomputable def inclN (K : Type) [Field K] {G : Type} [Group G] (H : Subgroup G)
    (N : Subgroup H) : MonoidAlgebra K N →ₐ[K] MonoidAlgebra K H :=
  MonoidAlgebra.mapDomainAlgHom K K (Subgroup.subtype N)

/-- The inclusion `K[H] →+* K[G]` induced by `H ≤ G`. -/
noncomputable def inclH (K : Type) [Field K] {G : Type} [Group G] (H : Subgroup G) :
    MonoidAlgebra K H →ₐ[K] MonoidAlgebra K G :=
  MonoidAlgebra.mapDomainAlgHom K K (Subgroup.subtype H)

/-- The action of `Multiplicative ℤ` on `K[N]` is conjugation by `t ^ k`: this is the content of
the hypothesis `hact`, transported from the group-like generators to all of `K[N]`. -/
theorem inclN_smul {K : Type} [Field K] {G : Type} [Group G] {H : Subgroup G} {N : Subgroup H}
    {t : H} (htN : ∀ (k : ℤ) (n : N), t ^ k * (n : H) * t ^ (-k) ∈ N)
    [MulSemiringAction (Multiplicative ℤ) (MonoidAlgebra K N)]
    [SMulCommClass (Multiplicative ℤ) K (MonoidAlgebra K N)]
    (hact : ∀ (k : ℤ) (n : N), (Multiplicative.ofAdd k) • (MonoidAlgebra.single n (1 : K)) =
        MonoidAlgebra.single ⟨t ^ k * (n : H) * t ^ (-k), htN k n⟩ (1 : K))
    (k : ℤ) (x : MonoidAlgebra K N) :
    inclN K H N ((Multiplicative.ofAdd k) • x)
      = MonoidAlgebra.single (t ^ k) (1 : K) * inclN K H N x
        * MonoidAlgebra.single (t ^ (-k)) (1 : K) := by
  refine MonoidAlgebra.induction_on (motive := fun x => inclN K H N ((Multiplicative.ofAdd k) • x)
      = MonoidAlgebra.single (t ^ k) (1 : K) * inclN K H N x
        * MonoidAlgebra.single (t ^ (-k)) (1 : K)) x ?_ ?_ ?_
  · intro m
    simp only [inclN, MonoidAlgebra.of_apply, hact, MonoidAlgebra.mapDomainAlgHom_apply,
      MonoidAlgebra.mapDomain_single, MonoidAlgebra.single_mul_single, mul_one,
      Subgroup.subtype_apply]
  · intro x y ihx ihy
    rw [smul_add, map_add, ihx, ihy, map_add, mul_add, add_mul]
  · intro c x ih
    rw [smul_comm (Multiplicative.ofAdd k) c x, map_smul, ih, map_smul]
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]

/-- The commutation relation `τ(x) t = t x` which makes the evaluation map `Phi` multiplicative. -/
theorem hcomm {K : Type} [Field K] {G : Type} [Group G] {H : Subgroup G} {N : Subgroup H} {t : H}
    (htN : ∀ (k : ℤ) (n : N), t ^ k * (n : H) * t ^ (-k) ∈ N)
    [MulSemiringAction (Multiplicative ℤ) (MonoidAlgebra K N)]
    [SMulCommClass (Multiplicative ℤ) K (MonoidAlgebra K N)]
    (hact : ∀ (k : ℤ) (n : N), (Multiplicative.ofAdd k) • (MonoidAlgebra.single n (1 : K)) =
        MonoidAlgebra.single ⟨t ^ k * (n : H) * t ^ (-k), htN k n⟩ (1 : K)) :
    ∀ {x : MonoidAlgebra K N} {y : Multiplicative ℤ},
      inclN K H N (y • x) * genT K t y = genT K t y * inclN K H N x := by
  intro x y
  obtain ⟨k, hk⟩ : ∃ k : ℤ, y = Multiplicative.ofAdd k :=
    ⟨Multiplicative.toAdd y, (ofAdd_toAdd y).symm⟩
  rw [hk]
  have hCD : MonoidAlgebra.single (t ^ (-k)) (1 : K) * MonoidAlgebra.single (t ^ k) (1 : K) = 1 := by
    rw [MonoidAlgebra.single_mul_single, ← zpow_add, neg_add_cancel, zpow_zero]
    simp [MonoidAlgebra.one_def]
  rw [inclN_smul htN hact k x, genT_ofAdd K t k, mul_assoc, hCD, mul_one]

/-- The evaluation homomorphism `K[N][t^{±1}; τ] →ₐ[K] K[H]`, sending the variable `t` to the
group-like element `t` and `K[N]` to `K[H]` by inclusion. -/
noncomputable def Phi {K : Type} [Field K] {G : Type} [Group G] {H : Subgroup G} {N : Subgroup H}
    {t : H} (htN : ∀ (k : ℤ) (n : N), t ^ k * (n : H) * t ^ (-k) ∈ N)
    [MulSemiringAction (Multiplicative ℤ) (MonoidAlgebra K N)]
    [SMulCommClass (Multiplicative ℤ) K (MonoidAlgebra K N)]
    (hact : ∀ (k : ℤ) (n : N), (Multiplicative.ofAdd k) • (MonoidAlgebra.single n (1 : K)) =
        MonoidAlgebra.single ⟨t ^ k * (n : H) * t ^ (-k), htN k n⟩ (1 : K)) :
    SkewMonoidAlgebra (MonoidAlgebra K N) (Multiplicative ℤ) →ₐ[K] MonoidAlgebra K H :=
  SkewMonoidAlgebra.liftNCAlgHom (inclN K H N) (genT K t) (hcomm htN hact)

theorem Phi_apply {K : Type} [Field K] {G : Type} [Group G] {H : Subgroup G} {N : Subgroup H}
    {t : H} (htN : ∀ (k : ℤ) (n : N), t ^ k * (n : H) * t ^ (-k) ∈ N)
    [MulSemiringAction (Multiplicative ℤ) (MonoidAlgebra K N)]
    [SMulCommClass (Multiplicative ℤ) K (MonoidAlgebra K N)]
    (hact : ∀ (k : ℤ) (n : N), (Multiplicative.ofAdd k) • (MonoidAlgebra.single n (1 : K)) =
        MonoidAlgebra.single ⟨t ^ k * (n : H) * t ^ (-k), htN k n⟩ (1 : K))
    (x : SkewMonoidAlgebra (MonoidAlgebra K N) (Multiplicative ℤ)) :
    Phi htN hact x = SkewMonoidAlgebra.liftNC
      (((inclN K H N).toRingHom) : MonoidAlgebra K N →+ MonoidAlgebra K H) (genT K t) x :=
  rfl

theorem Phi_single {K : Type} [Field K] {G : Type} [Group G] {H : Subgroup G} {N : Subgroup H}
    {t : H} (htN : ∀ (k : ℤ) (n : N), t ^ k * (n : H) * t ^ (-k) ∈ N)
    [MulSemiringAction (Multiplicative ℤ) (MonoidAlgebra K N)]
    [SMulCommClass (Multiplicative ℤ) K (MonoidAlgebra K N)]
    (hact : ∀ (k : ℤ) (n : N), (Multiplicative.ofAdd k) • (MonoidAlgebra.single n (1 : K)) =
        MonoidAlgebra.single ⟨t ^ k * (n : H) * t ^ (-k), htN k n⟩ (1 : K))
    (a : Multiplicative ℤ) (b : MonoidAlgebra K N) :
    Phi htN hact (SkewMonoidAlgebra.single a b) = inclN K H N b * genT K t a := by
  rw [Phi_apply, SkewMonoidAlgebra.liftNC_single]
  simp

/-! ## The decomposition `h = n * t ^ k` -/

/-- Uniqueness of the decomposition `h = n * t ^ k` (`n : N`, `k : ℤ`), using that no non-trivial
power of `t` lies in `N`. -/
theorem decomp_unique {G : Type} [Group G] {H : Subgroup G} {N : Subgroup H} {t : H}
    (htinf : ∀ k : ℤ, k ≠ 0 → t ^ k ∉ N) {n n' : N} {k k' : ℤ}
    (h : (n : H) * t ^ k = (n' : H) * t ^ k') : k = k' ∧ n = n' := by
  have h2 : t ^ k * t ^ (-k') = ((n⁻¹ * n' : N) : H) := by
    have hh := congrArg (fun x : H => (n : H)⁻¹ * x * t ^ (-k')) h
    simpa [mul_assoc] using hh
  have h4 : t ^ (k - k') = ((n⁻¹ * n' : N) : H) := by
    rw [sub_eq_add_neg, zpow_add]
    exact h2
  have h3 : t ^ (k - k') ∈ N := h4 ▸ (n⁻¹ * n').2
  have hkk : k = k' := by
    by_contra hne
    exact htinf (k - k') (sub_ne_zero.mpr hne) h3
  subst hkk
  have hnn : (n : H) = (n' : H) := mul_right_cancel h
  exact ⟨rfl, Subtype.ext hnn⟩

/-- The `N`-component of the decomposition of `h : H` as `n * t ^ k`. -/
noncomputable def npart {G : Type} [Group G] {H : Subgroup G} (N : Subgroup H) (t : H)
    (hgen : ∀ h : H, ∃ (n : N) (k : ℤ), h = (n : H) * t ^ k) (h : H) : N :=
  Classical.choose (hgen h)

/-- The `ℤ`-component of the decomposition of `h : H` as `n * t ^ k`. -/
noncomputable def kpart {G : Type} [Group G] {H : Subgroup G} (N : Subgroup H) (t : H)
    (hgen : ∀ h : H, ∃ (n : N) (k : ℤ), h = (n : H) * t ^ k) (h : H) : ℤ :=
  Classical.choose (Classical.choose_spec (hgen h))

theorem npart_mul_kpart {G : Type} [Group G] {H : Subgroup G} (N : Subgroup H) (t : H)
    (hgen : ∀ h : H, ∃ (n : N) (k : ℤ), h = (n : H) * t ^ k) (h : H) :
    h = ((npart N t hgen h : N) : H) * t ^ (kpart N t hgen h) :=
  Classical.choose_spec (Classical.choose_spec (hgen h))

/-- The element of `K[N][t^{±1}; τ]` corresponding to `n * t ^ k`. -/
noncomputable def psiFun {K : Type} [Field K] {G : Type} [Group G] {H : Subgroup G}
    (N : Subgroup H) (t : H)
    (hgen : ∀ h : H, ∃ (n : N) (k : ℤ), h = (n : H) * t ^ k) (h : H) :
    SkewMonoidAlgebra (MonoidAlgebra K N) (Multiplicative ℤ) :=
  SkewMonoidAlgebra.single (Multiplicative.ofAdd (kpart N t hgen h))
    (MonoidAlgebra.single (npart N t hgen h) (1 : K))

theorem psiFun_one {K : Type} [Field K] {G : Type} [Group G] {H : Subgroup G} {N : Subgroup H}
    {t : H} (htinf : ∀ k : ℤ, k ≠ 0 → t ^ k ∉ N)
    (hgen : ∀ h : H, ∃ (n : N) (k : ℤ), h = (n : H) * t ^ k) :
    psiFun (K := K) N t hgen 1 = 1 := by
  have hdec : ((npart N t hgen (1 : H) : N) : H) * t ^ (kpart N t hgen 1)
      = ((1 : N) : H) * t ^ (0 : ℤ) := by
    rw [← npart_mul_kpart N t hgen (1 : H)]
    simp
  obtain ⟨hk, hn⟩ := decomp_unique htinf hdec
  rw [psiFun, hk, hn]
  rw [ofAdd_zero]
  exact SkewMonoidAlgebra.one_def.symm

theorem psiFun_mul {K : Type} [Field K] {G : Type} [Group G] {H : Subgroup G} {N : Subgroup H}
    {t : H} (htN : ∀ (k : ℤ) (n : N), t ^ k * (n : H) * t ^ (-k) ∈ N)
    [MulSemiringAction (Multiplicative ℤ) (MonoidAlgebra K N)]
    (hact : ∀ (k : ℤ) (n : N), (Multiplicative.ofAdd k) • (MonoidAlgebra.single n (1 : K)) =
        MonoidAlgebra.single ⟨t ^ k * (n : H) * t ^ (-k), htN k n⟩ (1 : K))
    (htinf : ∀ k : ℤ, k ≠ 0 → t ^ k ∉ N)
    (hgen : ∀ h : H, ∃ (n : N) (k : ℤ), h = (n : H) * t ^ k) (a b : H) :
    psiFun (K := K) N t hgen (a * b) =
      psiFun (K := K) N t hgen a * psiFun (K := K) N t hgen b := by
  rw [psiFun, psiFun, psiFun]
  set na := npart N t hgen a with hna
  set ka := kpart N t hgen a with hka
  set nb := npart N t hgen b with hnb
  set kb := kpart N t hgen b with hkb
  have ha : a = (na : H) * t ^ ka := npart_mul_kpart N t hgen a
  have hb : b = (nb : H) * t ^ kb := npart_mul_kpart N t hgen b
  have hdec : ((npart N t hgen (a * b) : N) : H) * t ^ (kpart N t hgen (a * b))
      = ((na * ⟨t ^ ka * (nb : H) * t ^ (-ka), htN ka nb⟩ : N) : H) * t ^ (ka + kb) := by
    rw [← npart_mul_kpart N t hgen (a * b), ha, hb]
    simp only [Subgroup.coe_mul, zpow_neg]
    rw [zpow_add]
    group
  obtain ⟨hk, hn⟩ := decomp_unique htinf hdec
  rw [hk, hn]
  rw [SkewMonoidAlgebra.single_mul_single, ← ofAdd_add, hact,
    MonoidAlgebra.single_mul_single, one_mul]

/-- The monoid homomorphism `H →* K[N][t^{±1}; τ]`, `h = n * t ^ k ↦ n t ^ k`. -/
noncomputable def psi {K : Type} [Field K] {G : Type} [Group G] {H : Subgroup G} {N : Subgroup H}
    {t : H} (htN : ∀ (k : ℤ) (n : N), t ^ k * (n : H) * t ^ (-k) ∈ N)
    [MulSemiringAction (Multiplicative ℤ) (MonoidAlgebra K N)]
    (hact : ∀ (k : ℤ) (n : N), (Multiplicative.ofAdd k) • (MonoidAlgebra.single n (1 : K)) =
        MonoidAlgebra.single ⟨t ^ k * (n : H) * t ^ (-k), htN k n⟩ (1 : K))
    (htinf : ∀ k : ℤ, k ≠ 0 → t ^ k ∉ N)
    (hgen : ∀ h : H, ∃ (n : N) (k : ℤ), h = (n : H) * t ^ k) :
    H →* SkewMonoidAlgebra (MonoidAlgebra K N) (Multiplicative ℤ) where
  toFun := psiFun N t hgen
  map_one' := psiFun_one htinf hgen
  map_mul' := psiFun_mul htN hact htinf hgen

/-- The decomposition homomorphism `K[H] →ₐ[K] K[N][t^{±1}; τ]`. -/
noncomputable def Psi {K : Type} [Field K] {G : Type} [Group G] {H : Subgroup G} {N : Subgroup H}
    {t : H} (htN : ∀ (k : ℤ) (n : N), t ^ k * (n : H) * t ^ (-k) ∈ N)
    [MulSemiringAction (Multiplicative ℤ) (MonoidAlgebra K N)]
    [SMulCommClass (Multiplicative ℤ) K (MonoidAlgebra K N)]
    (hact : ∀ (k : ℤ) (n : N), (Multiplicative.ofAdd k) • (MonoidAlgebra.single n (1 : K)) =
        MonoidAlgebra.single ⟨t ^ k * (n : H) * t ^ (-k), htN k n⟩ (1 : K))
    (htinf : ∀ k : ℤ, k ≠ 0 → t ^ k ∉ N)
    (hgen : ∀ h : H, ∃ (n : N) (k : ℤ), h = (n : H) * t ^ k) :
    MonoidAlgebra K H →ₐ[K] SkewMonoidAlgebra (MonoidAlgebra K N) (Multiplicative ℤ) :=
  MonoidAlgebra.lift K (SkewMonoidAlgebra (MonoidAlgebra K N) (Multiplicative ℤ)) H
    (psi htN hact htinf hgen)

theorem Psi_single {K : Type} [Field K] {G : Type} [Group G] {H : Subgroup G} {N : Subgroup H}
    {t : H} (htN : ∀ (k : ℤ) (n : N), t ^ k * (n : H) * t ^ (-k) ∈ N)
    [MulSemiringAction (Multiplicative ℤ) (MonoidAlgebra K N)]
    [SMulCommClass (Multiplicative ℤ) K (MonoidAlgebra K N)]
    (hact : ∀ (k : ℤ) (n : N), (Multiplicative.ofAdd k) • (MonoidAlgebra.single n (1 : K)) =
        MonoidAlgebra.single ⟨t ^ k * (n : H) * t ^ (-k), htN k n⟩ (1 : K))
    (htinf : ∀ k : ℤ, k ≠ 0 → t ^ k ∉ N)
    (hgen : ∀ h : H, ∃ (n : N) (k : ℤ), h = (n : H) * t ^ k) (h : H) :
    Psi htN hact htinf hgen (MonoidAlgebra.single h (1 : K))
      = psi htN hact htinf hgen h := by
  rw [Psi, MonoidAlgebra.lift_single, one_smul]

end Work.ORHughesFree.HughesFree
