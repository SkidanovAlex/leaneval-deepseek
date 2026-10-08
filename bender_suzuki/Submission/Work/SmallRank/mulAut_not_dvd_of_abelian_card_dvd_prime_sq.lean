import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.SmallRank

open scoped Classical

/-! ## Auxiliary equivalences

The automorphism group of an abelian group `A` of exponent `p` (i.e. `∀ a, a ^ p = 1`) is
isomorphic to the general linear group of the `ZMod p`-module `Additive A`: every additive map
between `ZMod p`-modules is `ZMod p`-linear (`AddMonoidHom.toZModLinearMap`). -/

/-- Additive automorphisms of a `ZMod n`-module are exactly its linear automorphisms. -/
noncomputable def addAutEquivLinearEquiv {p : ℕ} (V : Type*) [AddCommGroup V] [Module (ZMod p) V] :
    AddAut V ≃ (V ≃ₗ[ZMod p] V) where
  toFun e := LinearEquiv.ofBijective ((e : V →+ V).toZModLinearMap p) e.bijective
  invFun f := f.toAddEquiv
  left_inv e := by ext x; simp [LinearEquiv.ofBijective]
  right_inv f := by ext x; simp [LinearEquiv.ofBijective]

/-- A group of order `p ^ 2` all of whose elements have order dividing `p` (with `p` prime) has
exactly `(p ^ 2 - 1) * (p ^ 2 - p)` automorphisms.

Indeed in that case `A` is an elementary abelian `p`-group of order `p ^ 2`, so its automorphism
group is `GL₂(𝔽_p)`, whose order is `(p ^ 2 - 1) * (p ^ 2 - p)` (`Matrix.card_GL_field`). -/
theorem card_mulAut_of_exponent_prime_card_prime_sq {p : ℕ} (hp : p.Prime) {A : Type*}
    [Group A] [Finite A] (hcomm : IsMulCommutative A) (hcard : Nat.card A = p ^ 2)
    (hexp : ∀ a : A, a ^ p = 1) :
    Nat.card (MulAut A) = (p ^ 2 - 1) * (p ^ 2 - p) := by
  letI : CommGroup A := { ‹Group A› with mul_comm := fun a b => hcomm.is_comm.comm a b }
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype (Additive A) := Fintype.ofFinite _
  have hmod : ∀ x : Additive A, p • x = 0 := by
    intro x
    rw [← ofMul_toMul x, ← ofMul_pow]
    simp [hexp]
  haveI : Module (ZMod p) (Additive A) := AddCommGroup.zmodModule (n := p) hmod
  have hfr : Module.finrank (ZMod p) (Additive A) = 2 := by
    haveI : Module.Free (ZMod p) (Additive A) := Module.Free.of_divisionRing _ _
    haveI : Module.Finite (ZMod p) (Additive A) := Module.Finite.of_finite
    have h := Module.card_eq_pow_finrank (K := ZMod p) (V := Additive A)
    rw [ZMod.card, ← Nat.card_eq_fintype_card] at h
    rw [show Nat.card (Additive A) = p ^ 2 from hcard] at h
    exact Nat.pow_right_injective hp.two_le h.symm
  obtain ⟨e⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq (R := ZMod p)
    (M := Additive A) (M' := (Fin 2 → ZMod p)) (by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]; exact hfr)
  have h2 : Nat.card (Additive A ≃ₗ[ZMod p] Additive A) =
      Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) := by
    have a := Nat.card_congr
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) (Additive A)).toEquiv
    have b := Nat.card_congr (LinearMap.GeneralLinearGroup.congrLinearEquiv e).toEquiv
    have c := Nat.card_congr
      (Matrix.GeneralLinearGroup.toLin (n := Fin 2) (R := ZMod p)).symm.toEquiv
    exact (a.symm.trans b).trans c
  calc Nat.card (MulAut A)
      = Nat.card (AddAut (Additive A)) := by
        exact (Nat.card_congr (Additive.toMul (α := MulAut A))).symm.trans
          (Nat.card_congr (AddAutAdditive A).toEquiv).symm
    _ = Nat.card (Additive A ≃ₗ[ZMod p] Additive A) := by
        simpa using Nat.card_congr (addAutEquivLinearEquiv (p := p) (Additive A))
    _ = Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) := h2
    _ = (p ^ 2 - 1) * (p ^ 2 - p) := by
        rw [Matrix.card_GL_field (n := 2) (𝔽 := ZMod p), Fin.prod_univ_two]
        simp [ZMod.card]

/-! ## Two elementary arithmetic facts -/

/-- If `0 < m` divides `p ^ 2` for a prime `p`, then `p ^ 2` does not divide `m.totient`: indeed
`m.totient < m ≤ p ^ 2`. -/
lemma not_dvd_totient_of_dvd_prime_sq {p m : ℕ} (hp : p.Prime) (hm : m ∣ p ^ 2) (hm0 : 0 < m) :
    ¬ p ^ 2 ∣ m.totient := by
  intro hdiv
  have hpos : 0 < m.totient := Nat.totient_pos.mpr hm0
  have h1 : p ^ 2 ≤ m.totient := Nat.le_of_dvd hpos hdiv
  have h2 : m.totient ≤ m := Nat.totient_le m
  have h3 : m ≤ p ^ 2 := Nat.le_of_dvd (pow_pos hp.pos 2) hm
  have hm_eq : m = p ^ 2 := le_antisymm h3 (le_trans h1 h2)
  have hlt : m.totient < m :=
    Nat.totient_lt m (by rw [hm_eq]; exact one_lt_pow₀ hp.one_lt (by norm_num))
  omega

/-- For a prime `p`, `p ^ 2` does not divide `(p ^ 2 - 1) * (p ^ 2 - p)`: the second factor
contributes exactly one factor `p`, and `p` divides neither `p - 1` nor `p + 1`. -/
lemma prime_sq_not_dvd_mul_prime_sq_sub {p : ℕ} (hp : p.Prime) :
    ¬ p ^ 2 ∣ (p ^ 2 - 1) * (p ^ 2 - p) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hsub : p ^ 2 - 1 = (p - 1) * (p + 1) := by
    have := Nat.sq_sub_sq p 1
    rw [one_pow, mul_comm] at this
    exact this
  have hsub2 : p ^ 2 - p = p * (p - 1) := by
    rw [pow_two, Nat.mul_sub_left_distrib]
    simp
  have hX : ¬ p ∣ (p - 1) * (p + 1) * (p - 1) := by
    intro h
    rcases hp.dvd_mul.mp h with h | h
    · rcases hp.dvd_mul.mp h with h | h
      · have := Nat.le_of_dvd (by omega) h
        omega
      · have h2 : p ∣ (p + 1) - p := Nat.dvd_sub h (dvd_refl p)
        have h3 : p ∣ 1 := by simpa using h2
        exact hp.not_dvd_one h3
    · have := Nat.le_of_dvd (by omega) h
      omega
  intro hd
  rw [hsub, hsub2] at hd
  have hform : (p - 1) * (p + 1) * (p * (p - 1)) = p * ((p - 1) * (p + 1) * (p - 1)) := by ring
  rw [hform] at hd
  obtain ⟨k, hk⟩ := hd
  have : (p - 1) * (p + 1) * (p - 1) = p * k := by
    refine Nat.mul_left_cancel hp.pos ?_
    rw [hk]
    ring
  exact hX ⟨k, this⟩

/-- Let `A` be a finite abelian group of order dividing `p ^ 2` (`p` prime).  Then `p ^ 2` does not
divide the order of the automorphism group of `A`; equivalently, `Aut A` has no subgroup of order
`p ^ 2`.

Suggested route.  `Nat.card A ∣ p ^ 2` puts `Nat.card A` in `{1, p, p ^ 2}`.
* If `IsCyclic A`: `IsCyclic.card_mulAut` gives `Nat.card (MulAut A) = (Nat.card A).totient`, and
  `Nat.totient_prime (= p - 1)` / `Nat.totient_prime_pow (= p ^ (n-1) * (p - 1))` show that this is
  `1`, `p - 1` or `p * (p - 1)`, none divisible by `p ^ 2`.
* If `A` is not cyclic then `Nat.card A = p ^ 2` and every element has order dividing `p`
  (`orderOf a ∣ p ^ 2`, and `orderOf a = p ^ 2` would make `A = zpowers a` cyclic), i.e.
  `∀ a : A, a ^ p = 1`.  Two provable routes for this case:
  (a) counting generating pairs: pick `a ≠ 1` and `b ∉ Subgroup.zpowers a`; then `A = ⟨a, b⟩` and
      `φ ↦ (φ a, φ b)` embeds `MulAut A` into `{q : A × A // q.1 ≠ 1 ∧ q.2 ∉ Subgroup.zpowers q.1}`,
      whose cardinality is `(p ^ 2 - 1) * (p ^ 2 - p) = p * ((p - 1) ^ 2 * (p + 1))` (each `x ≠ 1`
      generates a subgroup of order `p`), and `p ^ 2 ∤ p * ((p - 1) ^ 2 * (p + 1))`;
  (b) via `GL (Fin 2) (ZMod p)`: `Additive A` is a `ZMod p`-module of `finrank` `2`
      (`Module.card_eq_pow_finrank`), `MulAut A` embeds into `V ≃ₗ[ZMod p] V`, which is
      `LinearMap.GeneralLinearGroup (ZMod p) V`, and `fintype.card (Matrix.GL (Fin 2) (ZMod p))`
      is `(p ^ 2 - 1) * (p ^ 2 - p)` by `Matrix.card_GL_field`.

(Formalisation note: the cyclic case is handled through `IsCyclic.card_mulAut` and
`not_dvd_totient_of_dvd_prime_sq`; the non-cyclic case is handled by `(b)` above, in the form of
`card_mulAut_of_exponent_prime_card_prime_sq`, whose hypothesis `∀ a, a ^ p = 1` is deduced from
`not_isCyclic_iff_exponent_eq_prime`.) -/
theorem mulAut_not_dvd_of_abelian_card_dvd_prime_sq {p : ℕ} (hp : p.Prime) {A : Type*} [Group A]
    [Finite A] (hcomm : IsMulCommutative A) (hcard : Nat.card A ∣ p ^ 2) :
    ¬ p ^ 2 ∣ Nat.card (MulAut A) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hAcard_pos : 0 < Nat.card A := Nat.card_pos
  -- `Nat.card A = p ^ k` for some `k ≤ 2`
  obtain ⟨k, hkle, hk⟩ := (Nat.dvd_prime_pow hp).mp hcard
  have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hk3 with rfl | rfl | rfl
  · -- `|A| = 1`: `Aut A` is trivial
    have h1 : Nat.card A = 1 := by simpa using hk
    haveI : Subsingleton A := (Nat.card_eq_one_iff_unique.mp h1).1
    haveI : IsCyclic A := inferInstance
    rw [IsCyclic.card_mulAut, h1, Nat.totient_one]
    intro hd
    have := Nat.le_of_dvd (by norm_num) hd
    have hp2 : 2 ≤ p := hp.two_le
    nlinarith
  · -- `|A| = p`: `A` is cyclic of prime order
    have h1 : Nat.card A = p := by simpa using hk
    haveI : IsCyclic A := isCyclic_of_prime_card h1
    rw [IsCyclic.card_mulAut]
    exact not_dvd_totient_of_dvd_prime_sq hp hcard hAcard_pos
  · -- `|A| = p ^ 2`
    have h2 : Nat.card A = p ^ 2 := by simpa using hk
    by_cases hcyc : IsCyclic A
    · haveI : IsCyclic A := hcyc
      rw [IsCyclic.card_mulAut]
      exact not_dvd_totient_of_dvd_prime_sq hp hcard hAcard_pos
    · -- `A` is elementary abelian of order `p ^ 2`, so `MulAut A ≃ GL₂(𝔽_p)`
      have hexp : ∀ a : A, a ^ p = 1 := by
        have h := (not_isCyclic_iff_exponent_eq_prime hp h2).mp hcyc
        intro a
        have := Monoid.pow_exponent_eq_one a
        rwa [h] at this
      rw [card_mulAut_of_exponent_prime_card_prime_sq hp hcomm h2 hexp]
      exact prime_sq_not_dvd_mul_prime_sq_sub hp

end Work.SmallRank
