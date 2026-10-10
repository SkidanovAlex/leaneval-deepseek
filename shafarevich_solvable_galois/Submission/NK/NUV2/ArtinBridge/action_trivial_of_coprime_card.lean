import Mathlib.FieldTheory.Finite.Basic
import Submission.NK.GlobalCFTdeep.H1All
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A prime-order quotient on which a coprime-order group acts is acted on trivially

Let `A` be an abelian group, `B ≤ A` a subgroup of *prime* index `p`, and let a finite group `Q`
(of order coprime to `p - 1`) act on `A` by multiplicative automorphisms preserving `B`.  Then the
induced action of `Q` on `A ⧸ B` is trivial, i.e. `q • a * a⁻¹ ∈ B` for all `q`, `a`.

The mathematical content is two classical facts:

* any automorphism `σ` of a group of prime order `p` satisfies `σ ^ (p - 1) = 1`
  (a generator of the group is sent to a fixed power, and Fermat's little theorem bounds the
  resulting exponent); consequently `orderOf σ ∣ p - 1`;
* therefore an element of `Q` — whose order divides `Nat.card Q`, coprime to `p - 1` — acts
  trivially on `A ⧸ B`.

We deliberately avoid constructing `Q →* MulAut (A ⧸ B)` as a bundled homomorphism: for the
argument we only need, for each `q`, the induced automorphism `quotActAut B hB q` together with the
formula `(quotActAut B hB q) ^ m (a ⧸ B) = (q ^ m • a) ⧸ B`.
-/

set_option linter.style.haveILetI false

namespace NK.NUV2.ArtinBridge

/-- Every automorphism of a finite group of prime order `p` has order dividing `p - 1`.

Proof: for `σ ≠ 1` choose `g` with `σ g ≠ g`; then `g ≠ 1` generates `G` (a finite group of prime
order).  Writing `σ g = g ^ k` one gets `σ ^ m g = g ^ (k ^ m)` by induction, and Fermat's little
theorem gives `k ^ (p - 1) ≡ 1 [MOD p]`, i.e. `σ ^ (p - 1) g = g`.  Since `g` generates `G`, this
forces `σ ^ (p - 1) = 1`. -/
private lemma mulAut_orderOf_dvd_sub_one_of_prime_card {G : Type*} [Group G] (p : ℕ)
    (hp : p.Prime) (hG : Nat.card G = p) (σ : MulAut G) : orderOf σ ∣ p - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite G := Nat.finite_of_card_ne_zero (hG ▸ hp.ne_zero)
  rcases eq_or_ne σ 1 with h | h
  · rw [h, orderOf_one]; exact one_dvd _
  · obtain ⟨g, hg⟩ : ∃ g, σ g ≠ g := by
      by_contra hc
      simp only [not_exists, not_not] at hc
      exact h (MulEquiv.ext hc)
    have hg1 : g ≠ 1 := fun h1 => hg (by rw [h1, map_one])
    have hsg1 : σ g ≠ 1 := fun h1 => hg1 (σ.injective (by rw [h1, map_one]))
    have hordg : orderOf g = p := by
      rcases (Nat.dvd_prime hp).mp (hG ▸ orderOf_dvd_natCard g) with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) hg1
      · exact h1
    obtain ⟨k, hk⟩ : ∃ k : ℕ, g ^ k = σ g := by
      have hmem : σ g ∈ Submonoid.powers g := mem_powers_of_prime_card hG hg1
      simpa using (Submonoid.mem_powers_iff (σ g) g).mp hmem
    have hpk : ¬ p ∣ k := by
      intro hd
      have hd' : orderOf g ∣ k := by rwa [hordg]
      exact hsg1 (by rw [← hk, orderOf_dvd_iff_pow_eq_one.mp hd'])
    have hmod : k ^ (p - 1) ≡ 1 [MOD p] :=
      Nat.ModEq.pow_card_sub_one_eq_one hp ((hp.coprime_iff_not_dvd.mpr hpk).symm)
    have hgp : (σ ^ (p - 1)) g = g := by
      have hpow : ∀ m : ℕ, (σ ^ m) g = g ^ (k ^ m) := by
        intro m
        induction m with
        | zero => simp
        | succ m ih =>
          calc (σ ^ (m + 1)) g = (σ ^ m) (σ g) := by rw [pow_succ, MulAut.mul_apply]
            _ = (σ ^ m) (g ^ k) := by rw [hk]
            _ = ((σ ^ m) g) ^ k := map_pow _ _ _
            _ = (g ^ (k ^ m)) ^ k := by rw [ih]
            _ = g ^ (k ^ m * k) := by rw [pow_mul]
            _ = g ^ (k ^ (m + 1)) := by rw [pow_succ]
      rw [hpow (p - 1)]
      have h1 : k ^ (p - 1) % p = 1 := by
        have hh := hmod
        rw [Nat.ModEq] at hh
        rw [hh, Nat.mod_eq_of_lt hp.one_lt]
      rw [← pow_mod_orderOf g (k ^ (p - 1)), hordg, h1, pow_one]
    have hσpow : σ ^ (p - 1) = 1 := by
      refine MulEquiv.ext (fun x => ?_)
      have hx : x ∈ Submonoid.powers g := by
        rw [powers_eq_top_of_prime_card hG hg1]; exact Submonoid.mem_top x
      obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff x g).mp hx
      rw [← hn]
      show (σ ^ (p - 1)) (g ^ n) = g ^ n
      rw [map_pow, hgp]
    exact orderOf_dvd_of_pow_eq_one hσpow

section QuotientAction

variable {Q A : Type*} [Group Q] [CommGroup A] [MulDistribMulAction Q A]

/-- The endomorphism of `A ⧸ B` induced by the action of `q : Q`, for a `Q`-invariant `B`. -/
private noncomputable def quotActHom (B : Subgroup A)
    (hB : ∀ (q : Q) {b : A}, b ∈ B → q • b ∈ B) (q : Q) : A ⧸ B →* A ⧸ B :=
  QuotientGroup.map B B (MulDistribMulAction.toMulAut Q A q)
    (fun _ hb => by simpa using hB q hb)

private lemma quotActHom_apply (B : Subgroup A)
    (hB : ∀ (q : Q) {b : A}, b ∈ B → q • b ∈ B) (q : Q) (a : A) :
    quotActHom B hB q (a : A ⧸ B) = ((q • a : A) : A ⧸ B) := by
  simp only [quotActHom, QuotientGroup.map_mk, MulDistribMulAction.toMulAut_apply]
  exact congrArg (fun x : A => (x : A ⧸ B)) (MulDistribMulAction.toMulEquiv_apply A q a)

/-- The automorphism of `A ⧸ B` induced by the action of `q : Q`, for a `Q`-invariant `B`. -/
private noncomputable def quotActAut (B : Subgroup A)
    (hB : ∀ (q : Q) {b : A}, b ∈ B → q • b ∈ B) (q : Q) : MulAut (A ⧸ B) :=
  MonoidHom.toMulEquiv (quotActHom B hB q) (quotActHom B hB q⁻¹)
    (MonoidHom.ext (fun x => by
      refine QuotientGroup.induction_on x fun a => ?_
      rw [MonoidHom.comp_apply, MonoidHom.id_apply, quotActHom_apply, quotActHom_apply,
        ← mul_smul, inv_mul_cancel, one_smul]))
    (MonoidHom.ext (fun x => by
      refine QuotientGroup.induction_on x fun a => ?_
      rw [MonoidHom.comp_apply, MonoidHom.id_apply, quotActHom_apply, quotActHom_apply,
        ← mul_smul, mul_inv_cancel, one_smul]))

@[simp] private lemma quotActAut_apply (B : Subgroup A)
    (hB : ∀ (q : Q) {b : A}, b ∈ B → q • b ∈ B) (q : Q) (a : A) :
    quotActAut B hB q (a : A ⧸ B) = ((q • a : A) : A ⧸ B) :=
  quotActHom_apply B hB q a

/-- The iterated action of `quotActAut B hB q` on a coset. -/
private lemma quotActAut_pow_apply (B : Subgroup A)
    (hB : ∀ (q : Q) {b : A}, b ∈ B → q • b ∈ B) (q : Q) :
    ∀ (m : ℕ) (a : A),
      ((quotActAut B hB q) ^ m) (a : A ⧸ B) = ((q ^ m • a : A) : A ⧸ B) := by
  intro m
  induction m with
  | zero => intro a; simp
  | succ m ih =>
    intro a
    calc (((quotActAut B hB q) ^ (m + 1)) (a : A ⧸ B))
        = ((quotActAut B hB q) ^ m) ((quotActAut B hB q) (a : A ⧸ B)) := by
          rw [pow_succ, MulAut.mul_apply]
      _ = ((quotActAut B hB q) ^ m) ((q • a : A) : A ⧸ B) := by rw [quotActAut_apply]
      _ = ((q ^ m • (q • a) : A) : A ⧸ B) := ih (q • a)
      _ = ((q ^ (m + 1) • a : A) : A ⧸ B) := by rw [pow_succ, mul_smul]

/-- The order of the induced automorphism divides the order of `q`. -/
private lemma orderOf_quotActAut_dvd_orderOf (B : Subgroup A)
    (hB : ∀ (q : Q) {b : A}, b ∈ B → q • b ∈ B) (q : Q) :
    orderOf (quotActAut B hB q) ∣ orderOf q := by
  rw [orderOf_dvd_iff_pow_eq_one]
  refine MulEquiv.ext (fun x => ?_)
  refine QuotientGroup.induction_on x fun a => ?_
  rw [quotActAut_pow_apply, pow_orderOf_eq_one, one_smul]
  simp

end QuotientAction

theorem action_trivial_of_coprime_card {Q A : Type} [Group Q] [Fintype Q] [CommGroup A]
    [MulDistribMulAction Q A] (B : Subgroup A) (hB : ∀ (q : Q) {b : A}, b ∈ B → q • b ∈ B)
    (p : ℕ) (hp : p.Prime) (hcard : Nat.card (A ⧸ B) = p)
    (hcop : (Nat.card Q).Coprime (p - 1)) :
    ∀ (q : Q) (a : A), q • a * a⁻¹ ∈ B := by
  have hmain : ∀ q : Q, quotActAut B hB q = 1 := by
    intro q
    have h2 : orderOf (quotActAut B hB q) ∣ Nat.card Q :=
      (orderOf_quotActAut_dvd_orderOf B hB q).trans (orderOf_dvd_natCard q)
    have h3 : orderOf (quotActAut B hB q) ∣ p - 1 :=
      mulAut_orderOf_dvd_sub_one_of_prime_card p hp hcard _
    have h4 : orderOf (quotActAut B hB q) = 1 := by
      have h5 : orderOf (quotActAut B hB q) ∣ Nat.gcd (Nat.card Q) (p - 1) := Nat.dvd_gcd h2 h3
      rw [Nat.Coprime.gcd_eq_one hcop] at h5
      exact Nat.dvd_one.mp h5
    exact orderOf_eq_one_iff.mp h4
  intro q a
  have hqa : ((q • a : A) : A ⧸ B) = (a : A ⧸ B) := by
    have hh := congrArg (fun f : MulAut (A ⧸ B) => f (a : A ⧸ B)) (hmain q)
    simpa using hh
  exact (QuotientGroup.eq_one_iff (q • a * a⁻¹)).mp (by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hqa, mul_inv_cancel])

end NK.NUV2.ArtinBridge
