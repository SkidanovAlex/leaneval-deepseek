import Mathlib
import Submission.NK.TameStructureDeep.Tame.tameAbelianization_mulEquiv_zhat_mul_mu
import Submission.NK.TameStructureDeep.Tame.wildInertiaSubgroup_eq_correctedWildInertia
import Submission.NK.TameStructureDeep.Tame.isProP_correctedWildInertia
import Submission.NK.TameStructureDeep.Degree.galoisGroup_unramifiedClosure_mulEquiv
import Submission.NK.TowerRank.isProCyclic_zhat
import Submission.NK.TameStructureDeep.Tame.Unconditional

namespace NK.TameStructureDeep.Tame

set_option linter.style.haveILetI false

noncomputable section

/-! ## Two elementary lemmas about `(ℤ/N)²` -/

/-- Every element of `(ℤ/N)²` has `N`-th power `1`: the exponent of `M(ZMod N) × M(ZMod N)`
divides `N`. -/
theorem zmodSq_pow_eq_one {N : ℕ} [NeZero N]
    (x : Multiplicative (ZMod N) × Multiplicative (ZMod N)) : x ^ N = 1 := by
  obtain ⟨a, b⟩ := x
  have ha : a ^ N = 1 := by
    have h : a ^ Nat.card (Multiplicative (ZMod N)) = 1 := pow_card_eq_one'
    rwa [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card] at h
  have hb : b ^ N = 1 := by
    have h : b ^ Nat.card (Multiplicative (ZMod N)) = 1 := pow_card_eq_one'
    rwa [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card] at h
  rw [Prod.pow_mk, ha, hb, Prod.mk_one_one]

/-- The cardinality of `(ℤ/N)²`. -/
theorem card_zmodSq (N : ℕ) [NeZero N] :
    Nat.card (Multiplicative (ZMod N) × Multiplicative (ZMod N)) = N * N := by
  rw [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

/-! ## The wild inertia dies in a prime-to-`p` finite quotient -/

/-- **A normal pro-`p` subgroup of `G` is killed by every homomorphism into a finite group of
order a power of a prime `ℓ ≠ p`.**

Indeed `V ⧸ (V ⊓ ker f) ≃ f '' V` is a finite quotient of the pro-`p` group `V`, hence has
`p`-power order `p^k`; but it also divides `|H| = ℓ^N`, and `p ≠ ℓ` forces `k = 0`.  No topology
is used: `IsProP` is the finite-index statement. -/
theorem le_ker_of_isProP_of_natCard_eq_pow {G H : Type*} [Group G] [Group H] [Fintype H]
    {p ℓ N : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime) (hne : p ≠ ℓ) (hcard : Nat.card H = ℓ ^ N)
    (V : Subgroup G) (hV : NK.LocalTame.IsProP p ↥V) (f : G →* H) : V ≤ f.ker := by
  let N' : Subgroup ↥V := (f.comp V.subtype).ker
  have hcardN : N'.index = Nat.card ↥((f.comp V.subtype).range) := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange (f.comp V.subtype)).toEquiv
  have hfin : Finite (↥V ⧸ N') := by
    have : Finite ↥((f.comp V.subtype).range) := inferInstance
    exact (Equiv.finite_iff (QuotientGroup.quotientKerEquivRange (f.comp V.subtype)).toEquiv).mpr
      this
  have hfi : N'.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨k, hk⟩ := hV N' hfi
  have hdvd : p ^ k ∣ ℓ ^ N := by
    rw [← hk, hcardN]
    have h1 : Nat.card ↥((f.comp V.subtype).range) ∣ Nat.card H :=
      Subgroup.card_subgroup_dvd_card _
    rwa [hcard] at h1
  have hk0 : k = 0 := by
    by_contra hkne
    have h2 : p ∣ p ^ k := dvd_pow_self p hkne
    have h3 : p ∣ ℓ ^ N := h2.trans hdvd
    have h4 : p ∣ ℓ := hp.dvd_of_dvd_pow h3
    exact hne ((hℓ.dvd_iff_eq hp.ne_one).mp h4).symm
  have hidx : N'.index = 1 := by rw [hk, hk0, pow_zero]
  have htop : N' = ⊤ := Subgroup.index_eq_one.mp hidx
  intro x hx
  have hmem : (f.comp V.subtype) (⟨x, hx⟩ : ↥V) = 1 := by
    have h1 : (⟨x, hx⟩ : ↥V) ∈ N' := by rw [htop]; exact Subgroup.mem_top _
    simpa only [N', MonoidHom.mem_ker] using h1
  simpa only [MonoidHom.comp_apply, Subgroup.coe_subtype, MonoidHom.mem_ker] using hmem

/-! ## The counting lemma -/

/-- **Counting: `Ẑ × μ_m` has no `(ℤ/ℓ^n)²`-quotient for `n = v_ℓ(m) + 1`.**

Let `Ψ : Ẑ × M(ℤ/m) ↠ (ℤ/ℓ^n)²` be surjective.  The image `A` of `Ẑ` is a finite quotient of
the pro-cyclic group `Ẑ`, hence *cyclic*, and every element of `(ℤ/ℓ^n)²` has order dividing
`ℓ^n`, so `|A| ≤ ℓ^n`.  The image `B` of `M(ℤ/m)` has order dividing both `m` (it is a quotient
of a cyclic group of order `m`) and `ℓ^{2n}` (it is a subgroup of `(ℤ/ℓ^n)²`), hence
`|B| ≤ ℓ^{v_ℓ(m)} = ℓ^{n-1}`.  As `(ℤ/ℓ^n)²` is the product `A B` of the two images, we get
`ℓ^{2n} = |(ℤ/ℓ^n)²| ≤ |A| |B| ≤ ℓ^{2n-1}`, a contradiction. -/
theorem not_surjective_zhat_mul_zmod_zmodSq (ℓ m : ℕ) (hℓ : ℓ.Prime) (hm : 0 < m) :
    ¬ ∃ Ψ : NK.LocalAnabelian.Zhat × Multiplicative (ZMod m) →*
        (Multiplicative (ZMod (ℓ ^ (m.factorization ℓ + 1))) ×
          Multiplicative (ZMod (ℓ ^ (m.factorization ℓ + 1)))),
      Function.Surjective Ψ := by
  rintro ⟨Ψ, hΨ⟩
  haveI : NeZero m := ⟨hm.ne'⟩
  haveI : NeZero (ℓ ^ (m.factorization ℓ + 1)) := ⟨pow_ne_zero _ hℓ.ne_zero⟩
  let Ψ₁ := Ψ.comp (MonoidHom.inl NK.LocalAnabelian.Zhat (Multiplicative (ZMod m)))
  let Ψ₂ := Ψ.comp (MonoidHom.inr NK.LocalAnabelian.Zhat (Multiplicative (ZMod m)))
  -- the image of `Ẑ` is cyclic of order at most `ℓ ^ n`
  have hA_le : Nat.card ↥Ψ₁.range ≤ ℓ ^ (m.factorization ℓ + 1) := by
    have hfin : Finite (NK.LocalAnabelian.Zhat ⧸ Ψ₁.ker) := by
      have : Finite ↥Ψ₁.range := inferInstance
      exact (Equiv.finite_iff (QuotientGroup.quotientKerEquivRange Ψ₁).toEquiv).mpr this
    have hfi : Ψ₁.ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    haveI : IsCyclic ↥Ψ₁.range :=
      (QuotientGroup.quotientKerEquivRange Ψ₁).isCyclic.mp
        (NK.TowerRank.isProCyclic_zhat Ψ₁.ker hfi)
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥Ψ₁.range)
    have hgen : Subgroup.zpowers g = ⊤ := (Subgroup.eq_top_iff' _).mpr hg
    have hcardA : Nat.card ↥Ψ₁.range = orderOf g := by
      rw [← Subgroup.card_top (G := ↥Ψ₁.range), ← hgen, Nat.card_zpowers]
    have hgpow : g ^ (ℓ ^ (m.factorization ℓ + 1)) = 1 := by
      apply Subtype.ext
      exact zmodSq_pow_eq_one _
    rw [hcardA]
    exact Nat.le_of_dvd (pow_pos hℓ.pos _) (orderOf_dvd_iff_pow_eq_one.mpr hgpow)
  -- the image of `M(ℤ/m)` has order dividing `m`
  have hB_dvd_m : Nat.card ↥Ψ₂.range ∣ m := by
    have h1 : Nat.card ↥Ψ₂.range = Ψ₂.ker.index := by
      rw [Subgroup.index_eq_card]
      exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange Ψ₂).toEquiv).symm
    rw [h1]
    have h2 := Subgroup.index_dvd_card Ψ₂.ker
    rwa [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card] at h2
  -- and dividing `ℓ ^ (2n)`
  have hB_dvd_pow : Nat.card ↥Ψ₂.range ∣ ℓ ^ (2 * (m.factorization ℓ + 1)) := by
    have h2 := Subgroup.card_subgroup_dvd_card Ψ₂.range
    rw [card_zmodSq] at h2
    rwa [show ℓ ^ (m.factorization ℓ + 1) * ℓ ^ (m.factorization ℓ + 1)
        = ℓ ^ (2 * (m.factorization ℓ + 1)) by rw [← pow_add, two_mul]] at h2
  obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow hℓ).mp hB_dvd_pow
  have hjle : j ≤ m.factorization ℓ := by
    have : ℓ ^ j ∣ m := hj ▸ hB_dvd_m
    exact (Nat.Prime.pow_dvd_iff_le_factorization hℓ hm.ne').mp this
  have hB_le : Nat.card ↥Ψ₂.range ≤ ℓ ^ m.factorization ℓ := by
    rw [hj]; exact Nat.pow_le_pow_right hℓ.one_lt.le hjle
  -- the target is the product of the two images
  have hsurj : Function.Surjective (fun x : ↥Ψ₁.range × ↥Ψ₂.range =>
      (x.1 : Multiplicative (ZMod (ℓ ^ (m.factorization ℓ + 1))) ×
        Multiplicative (ZMod (ℓ ^ (m.factorization ℓ + 1)))) * (x.2 : _)) := by
    rintro c
    obtain ⟨⟨z, u⟩, hzu⟩ := hΨ c
    refine ⟨(⟨Ψ₁ z, ⟨z, rfl⟩⟩, ⟨Ψ₂ u, ⟨u, rfl⟩⟩), ?_⟩
    show Ψ₁ z * Ψ₂ u = c
    rw [← hzu]
    show Ψ (z, 1) * Ψ (1, u) = Ψ (z, u)
    rw [← map_mul]
    congr 1
    simp [Prod.mk_mul_mk]
  have hcard_le : Nat.card (Multiplicative (ZMod (ℓ ^ (m.factorization ℓ + 1)))) *
        Nat.card (Multiplicative (ZMod (ℓ ^ (m.factorization ℓ + 1))))
      ≤ Nat.card ↥Ψ₁.range * Nat.card ↥Ψ₂.range := by
    calc Nat.card (Multiplicative (ZMod (ℓ ^ (m.factorization ℓ + 1)))) *
          Nat.card (Multiplicative (ZMod (ℓ ^ (m.factorization ℓ + 1))))
        = Nat.card (Multiplicative (ZMod (ℓ ^ (m.factorization ℓ + 1))) ×
            Multiplicative (ZMod (ℓ ^ (m.factorization ℓ + 1)))) :=
          (Nat.card_prod _ _).symm
      _ ≤ Nat.card (↥Ψ₁.range × ↥Ψ₂.range) := Nat.card_le_card_of_surjective _ hsurj
      _ = Nat.card ↥Ψ₁.range * Nat.card ↥Ψ₂.range := Nat.card_prod _ _
  have hle : ℓ ^ (m.factorization ℓ + 1) * ℓ ^ (m.factorization ℓ + 1)
      ≤ ℓ ^ (m.factorization ℓ + 1) * ℓ ^ m.factorization ℓ := by
    rw [← card_zmodSq, Nat.card_prod]
    exact hcard_le.trans (Nat.mul_le_mul hA_le hB_le)
  have h2 : ℓ ^ (m.factorization ℓ + 1) ≤ ℓ ^ m.factorization ℓ :=
    Nat.le_of_mul_le_mul_left hle (pow_pos hℓ.pos _)
  have h3 : m.factorization ℓ + 1 ≤ m.factorization ℓ :=
    (Nat.pow_le_pow_iff_right hℓ.one_lt).mp h2
  omega

/-! ## The main theorem -/

/-- **For every prime `ℓ ≠ p` the absolute Galois group of a `p`-adic field has no `ℤ_ℓ²`-quotient**
— the `ℓ ≠ p` half of Shimizu's residue-character detector, **unconditionally** at every place.

Route (no local class field theory, no openness of finite-index subgroups; use only the abstract
finite-index/quotient API — no topology is available on these groups here):

* Let `f : Gal(K'/κ) ↠ (ℤ/ℓ^n)²` be a surjection (κ = K_𝔭, `p = resCharAt 𝔭`, ℓ ≠ p).
* **`f` kills the wild inertia `V_κ`.**  `N := V_κ ⊓ f.ker` is normal in `V_κ` of finite index, so
  `V_κ ⧸ N ≃* f '' V_κ` by the first isomorphism theorem, and
  `NK.TameStructureDeep.Tame.isProP_correctedWildInertia` (transferred to the join by
  `NK.TameStructureDeep.Tame.wildInertiaSubgroup_eq_correctedWildInertia`, which needs a
  uniformizer `π`, available from `exists_isUniformizerAt`) says `[V_κ : N] = p^k`; but
  `[V_κ : N] = |f '' V_κ|` divides `ℓ^{2n}`, and `ℓ ≠ p`, so `k = 0` and `f '' V_κ = ⊥`.
  (Equivalently one may use `NK.LocalTame.wildInertiaSubgroup_isProP` for the pro-`p`-ness of
  the join — this is what the formalisation below does, so no uniformizer is needed at all.)
* Hence `f` factors as `Gal(K'/κ) → Gal(κ^{tr}/κ) → (ℤ/ℓ^n)²`, and since the target is abelian it
  factors further through the **abstract** abelianisation
  `tameAbelianization = Abelianization (Gal(K'/κ) ⧸ V_κ)`; composing with the proved
  `NK.TameStructureDeep.Tame.tameAbelianization_mulEquiv_zhat_mul_mu` gives a **surjection**
  `Ψ : NK.LocalAnabelian.Zhat × Multiplicative (ZMod (q-1)) ↠ (ℤ/ℓ^n)²`
  (`q = NK.LocalStructure.residueCard K 𝔭`).
* **Counting.**  Take `n = (q-1).factorization ℓ + 1`.  `Ψ '' Zhat` is a *cyclic* subgroup of
  `(ℤ/ℓ^n)²` (it is a finite quotient of `NK.LocalAnabelian.Zhat`, which is pro-cyclic —
  `NK.TowerRank.isProCyclic_zhat`), hence of order `≤ ℓ^n`; `Ψ '' (Multiplicative (ZMod (q-1)))`
  has order dividing `gcd (q-1) (ℓ^{2n}) = ℓ^{n-1}`.  As `(ℤ/ℓ^n)²` is the product of these two
  subgroups, `ℓ^{2n} = |(ℤ/ℓ^n)²| ≤ ℓ^n · ℓ^{n-1} = ℓ^{2n-1}` — contradiction.

This is the `ℓ ≠ p` direction of `NK.LocalTame.Zl2ResidueChar`; it needs *neither* openness of the
index-`ℓ` normal subgroups (the abstract abelianisation is used directly) *nor* the
units/reciprocity input. -/
theorem not_hasZl2Quotient_of_ne_resCharAt {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hne : ℓ ≠ NK.TameStructureDeep.Tame.resCharAt 𝔭) :
    ¬ NK.LocalTame.HasZl2Quotient ℓ (Gal(K'/(𝔭.adicCompletion K))) := by
  intro hZ
  have hp : (resCharAt 𝔭).Prime := NK.Mine.prime_ringChar_residueField_adicCompletion 𝔭
  have hq2 : 1 < NK.LocalStructure.residueCard K 𝔭 := one_lt_residueCard_adicCompletion 𝔭
  have hm : 0 < NK.LocalStructure.residueCard K 𝔭 - 1 := by omega
  -- the surjection onto `(ℤ/ℓ^n)²` at `n = v_ℓ(q-1) + 1`
  obtain ⟨f, hf⟩ := hZ ((NK.LocalStructure.residueCard K 𝔭 - 1).factorization ℓ + 1) (by omega)
  haveI : NeZero (ℓ ^ ((NK.LocalStructure.residueCard K 𝔭 - 1).factorization ℓ + 1)) :=
    ⟨pow_ne_zero _ hℓ.ne_zero⟩
  -- the wild inertia is killed
  have hVf : NK.LocalTame.wildInertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K')
      (resCharAt 𝔭) ≤ f.ker := by
    refine le_ker_of_isProP_of_natCard_eq_pow
      (N := 2 * ((NK.LocalStructure.residueCard K 𝔭 - 1).factorization ℓ + 1))
      hp hℓ (Ne.symm hne) ?_ _ (NK.LocalTame.wildInertiaSubgroup_isProP (resCharAt 𝔭)) f
    exact (card_zmodSq (ℓ ^ ((NK.LocalStructure.residueCard K 𝔭 - 1).factorization ℓ + 1))).trans
      (by rw [← pow_add, two_mul])
  -- hence `f` factors through the abelianised tame quotient
  let W : Subgroup (Gal(K'/(𝔭.adicCompletion K))) :=
    NK.LocalTame.wildInertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K') (resCharAt 𝔭)
  haveI : W.Normal := inferInstance
  let fbar : Gal(K'/(𝔭.adicCompletion K)) ⧸ W →*
      (Multiplicative (ZMod (ℓ ^ ((NK.LocalStructure.residueCard K 𝔭 - 1).factorization ℓ + 1))) ×
        Multiplicative (ZMod (ℓ ^ ((NK.LocalStructure.residueCard K 𝔭 - 1).factorization ℓ + 1)))) :=
    QuotientGroup.lift W f hVf
  have hΦsurj : Function.Surjective (Abelianization.lift fbar) := by
    intro c
    obtain ⟨g, hg⟩ := hf c
    refine ⟨Abelianization.of (QuotientGroup.mk' W g), ?_⟩
    rw [Abelianization.lift_apply_of]
    show QuotientGroup.lift W f hVf ((QuotientGroup.mk' W) g) = c
    rw [QuotientGroup.mk'_apply, QuotientGroup.lift_mk']
    exact hg
  obtain ⟨e⟩ := tameAbelianization_mulEquiv_zhat_mul_mu (K := K) (K' := K') 𝔭
  refine not_surjective_zhat_mul_zmod_zmodSq ℓ (NK.LocalStructure.residueCard K 𝔭 - 1)
    hℓ hm ⟨(Abelianization.lift fbar).comp e.symm.toMonoidHom,
      hΦsurj.comp e.symm.surjective⟩

end

end NK.TameStructureDeep.Tame
