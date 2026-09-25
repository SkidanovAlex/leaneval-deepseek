import Mathlib

/-!
# The kernel of a surjection `(ℤ/2^{n+1})^r ↠ (ℤ/2^n)^r` is the `2`-torsion

`NK.NUV2.TowerRank.ker_eq_twoTorsion`: for finite groups `G`, `H` isomorphic to
`(ℤ/2^{n+1})^r` and `(ℤ/2^n)^r` respectively, every surjection `q : G →* H` has
kernel equal to the `2`-torsion subgroup of `G`.

This is step (i) of the construction recorded in
`Submission/Work/NUV2/TowerRank/NOTES.md` (and of `towerIso.lean`): the kernel of
the reduction map of a tower of `(ℤ/2^n)^r`-quotients is *computed*, not chosen.

## Proof

`|ker q| = |G| / |H| = 2^r`.  On the other side the `2`-torsion of
`G ≅ (ℤ/2^{n+1})^r` is `(ℤ/2)^r`, of order `2^r`: coordinatewise an element `a`
of `ℤ/2^{n+1}` with `2a = 0` is `0` or `2^n`.  Finally every `2`-torsion element
`x` of `G` is a `2^n`-th power, `x = y^{2^n}` (coordinatewise again), and then
`q x = (q y)^{2^n} = 1` since `H` has exponent dividing `2^n`.  Hence the
`2`-torsion is contained in `ker q`, and the two finite sets have the same
cardinality `2^r`, so they are equal.
-/

namespace NK.NUV2.TowerRank

/-- Coordinatewise description of the `2`-torsion of `ℤ/2^{n+1}`:
`2a = 0` iff `a = 0` or `a = 2^n`. -/
lemma zmod_two_mul_eq_zero_iff (n : ℕ) (a : ZMod (2 ^ (n+1))) :
    2 * a = 0 ↔ a = 0 ∨ a = (2 ^ n : ZMod (2 ^ (n+1))) := by
  constructor
  · intro h
    have hlt : a.val < 2 ^ (n+1) := ZMod.val_lt a
    have h' : ((2 * a.val : ℕ) : ZMod (2 ^ (n+1))) = 0 := by
      have ha : a = (a.val : ZMod (2 ^ (n+1))) := (ZMod.natCast_zmod_val a).symm
      rw [ha] at h
      push_cast
      exact h
    have hdvd : 2 ^ (n+1) ∣ 2 * a.val :=
      (ZMod.natCast_eq_zero_iff (2 * a.val) (2 ^ (n+1))).mp h'
    obtain ⟨k, hk⟩ := hdvd
    have hk2 : k < 2 := by
      have hlt2' : 2^(n+1) * k < 2^(n+1) * 2 := by
        calc 2^(n+1) * k = 2 * a.val := hk.symm
          _ < 2 * 2^(n+1) := Nat.mul_lt_mul_of_pos_left hlt (by norm_num)
          _ = 2^(n+1) * 2 := by ring
      exact Nat.lt_of_mul_lt_mul_left hlt2'
    rcases (by omega : k = 0 ∨ k = 1) with hk0 | hk1
    · left
      have h0 : a.val = 0 := by
        have : 2 * a.val = 0 := by rw [hk, hk0, mul_zero]
        omega
      rw [← ZMod.natCast_zmod_val a, h0]; norm_num
    · right
      have h1 : a.val = 2 ^ n := by
        have h2 : 2 * a.val = 2 * 2 ^ n := by rw [hk, hk1, mul_one, pow_succ']
        exact Nat.mul_left_cancel (by norm_num) h2
      rw [← ZMod.natCast_zmod_val a, h1]; push_cast; rfl
  · rintro (h | h)
    · rw [h, mul_zero]
    · rw [h]
      have hc : (2 : ZMod (2 ^ (n+1))) * (2 ^ n : ZMod (2 ^ (n+1)))
          = ((2 * 2^n : ℕ) : ZMod (2^(n+1))) := by push_cast; ring
      rw [hc, ← pow_succ', ZMod.natCast_self]

/-- `2^n` is nonzero in `ℤ/2^{n+1}`. -/
lemma zmod_two_pow_ne_zero (n : ℕ) : (2^n : ZMod (2^(n+1))) ≠ 0 := by
  intro hz
  have hz' : ((2^n : ℕ) : ZMod (2^(n+1))) = 0 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hz
  have hdvd : 2^(n+1) ∣ 2^n := (ZMod.natCast_eq_zero_iff (2^n) (2^(n+1))).mp hz'
  have hlt : 2^n < 2^(n+1) := Nat.pow_lt_pow_succ (by norm_num : 1 < 2)
  exact Nat.not_dvd_of_pos_of_lt (by positivity) hlt hdvd

/-- A nonzero element of `ℤ/2` is `1`. -/
lemma zmod2_eq_one_of_ne_zero {x : ZMod 2} (hx : x ≠ 0) : x = 1 := by
  have h1 : x.val < 2 := ZMod.val_lt x
  have h2 : x.val ≠ 0 := fun h0 => hx ((ZMod.val_eq_zero x).mp h0)
  have : x.val = 1 := by omega
  exact (ZMod.val_eq_one (by norm_num) x).mp this

/-- The `2`-torsion of `(ℤ/2^{n+1})^r` has cardinality `2^r`. -/
lemma card_two_torsion_pi (r n : ℕ) :
    Fintype.card {a : Fin r → ZMod (2 ^ (n+1)) // 2 • a = 0} = 2 ^ r := by
  let Ψ : (Fin r → ZMod 2) → (Fin r → ZMod (2^(n+1))) :=
    fun b i => if b i = 0 then 0 else (2^n : ZMod (2^(n+1)))
  have hmem : ∀ b, 2 • Ψ b = 0 := by
    intro b
    funext i
    change 2 • (if b i = 0 then 0 else (2^n : ZMod (2^(n+1)))) = 0
    by_cases h : b i = 0
    · rw [if_pos h]; simp
    · rw [if_neg h, nsmul_eq_mul]
      exact (zmod_two_mul_eq_zero_iff n (2^n : ZMod (2^(n+1)))).mpr (Or.inr rfl)
  have hrange : Set.range Ψ = {a : Fin r → ZMod (2^(n+1)) | 2 • a = 0} := by
    ext a
    constructor
    · rintro ⟨b, rfl⟩; exact hmem b
    · intro ha
      have ha' : ∀ i, 2 * (a i) = 0 := by
        intro i
        have := congrFun ha i
        simpa [Pi.smul_apply, nsmul_eq_mul] using this
      refine ⟨fun i => if a i = 0 then 0 else 1, ?_⟩
      funext i
      by_cases h : a i = 0
      · simp [Ψ, h]
      · have hai : a i = (2^n : ZMod (2^(n+1))) :=
          ((zmod_two_mul_eq_zero_iff n (a i)).mp (ha' i)).resolve_left h
        change (if (if a i = 0 then (0 : ZMod 2) else 1) = 0 then 0
          else (2^n : ZMod (2^(n+1)))) = a i
        rw [if_neg h, if_neg (show ¬ ((1 : ZMod 2) = 0) from one_ne_zero), hai]
  have hinj : Function.Injective Ψ := by
    intro b c hbc
    funext i
    have hi := congrFun hbc i
    simp only [Ψ] at hi
    by_cases hb : b i = 0
    · have hc : c i = 0 := by
        by_contra hc
        rw [if_pos hb, if_neg hc] at hi
        exact zmod_two_pow_ne_zero n hi.symm
      rw [hb, hc]
    · have hc : c i ≠ 0 := by
        intro hc
        rw [if_neg hb, if_pos hc] at hi
        exact zmod_two_pow_ne_zero n hi
      rw [zmod2_eq_one_of_ne_zero hb, zmod2_eq_one_of_ne_zero hc]
  have hbij : Function.Bijective (fun b : Fin r → ZMod 2 =>
      (⟨Ψ b, hmem b⟩ : {a : Fin r → ZMod (2^(n+1)) // 2 • a = 0})) := by
    refine ⟨?_, ?_⟩
    · intro b c hbc
      exact hinj (Subtype.ext_iff.mp hbc)
    · rintro ⟨a, ha⟩
      have hmem' : a ∈ Set.range Ψ := hrange.symm ▸ ha
      obtain ⟨b, hb⟩ := Set.mem_range.mp hmem'
      exact ⟨b, Subtype.ext hb⟩
  have hcard : Fintype.card {a : Fin r → ZMod (2^(n+1)) // 2 • a = 0}
      = Fintype.card (Fin r → ZMod 2) :=
    (Fintype.card_congr (Equiv.ofBijective _ hbij)).symm
  rw [hcard, Fintype.card_fun, ZMod.card, Fintype.card_fin]

theorem ker_eq_twoTorsion {r n : ℕ} {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H]
    (q : G →* H) (hq : Function.Surjective q)
    (eG : G ≃* Multiplicative (Fin r → ZMod (2 ^ (n+1))))
    (eH : H ≃* Multiplicative (Fin r → ZMod (2 ^ n))) :
    ∀ x : G, q x = 1 ↔ x ^ 2 = 1 := by
  classical
  -- Cardinality of the two groups and of the kernel of `q`.
  have hcardG : Fintype.card G = 2 ^ (r * (n+1)) := by
    rw [Fintype.card_congr eG.toEquiv, Fintype.card_multiplicative, Fintype.card_fun,
      ZMod.card, Fintype.card_fin, ← pow_mul, Nat.mul_comm]
  have hcardH : Fintype.card H = 2 ^ (r * n) := by
    rw [Fintype.card_congr eH.toEquiv, Fintype.card_multiplicative, Fintype.card_fun,
      ZMod.card, Fintype.card_fin, ← pow_mul, Nat.mul_comm]
  have hcardK : Fintype.card (MonoidHom.ker q) = 2 ^ r := by
    have hcq : Nat.card (G ⧸ MonoidHom.ker q) = 2 ^ (r * n) := by
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective q hq).toEquiv,
        Nat.card_eq_fintype_card, hcardH]
    have hcardG' : Nat.card G = 2 ^ (r * (n+1)) := by
      rw [Nat.card_eq_fintype_card, hcardG]
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (MonoidHom.ker q)
    rw [hcardG', hcq] at h
    have hmul : 2 ^ (r * (n+1)) = 2 ^ (r * n) * 2 ^ r := by
      rw [mul_add, mul_one, pow_add]
    rw [hmul] at h
    rw [← Nat.card_eq_fintype_card]
    exact (Nat.mul_left_cancel (by positivity) h).symm
  -- `2`-torsion in coordinates.
  have hiff : ∀ x : G, x ^ 2 = 1 ↔ 2 • (eG x).toAdd = 0 := by
    intro x
    have h1 : eG (x ^ 2) = 1 ↔ x ^ 2 = 1 := MulEquiv.map_eq_one_iff eG
    rw [← h1, map_pow]
    rw [← toAdd_pow (eG x) 2, toAdd_eq_zero]
  -- Cardinality of the `2`-torsion subgroup of `G`.
  have hf : ∀ x : G, x ^ 2 = 1 ↔ (eG x) ^ 2 = 1 := by
    intro x
    have h1 : eG (x ^ 2) = 1 ↔ x ^ 2 = 1 := MulEquiv.map_eq_one_iff eG
    rw [← h1, map_pow]
  have hcard2 : Fintype.card {x : G // x ^ 2 = 1} = 2 ^ r := by
    have he1 : {x : G // x ^ 2 = 1} ≃
        {y : Multiplicative (Fin r → ZMod (2^(n+1))) // y ^ 2 = 1} :=
      Equiv.subtypeEquiv eG.toEquiv (fun x => hf x)
    have he2 : {y : Multiplicative (Fin r → ZMod (2^(n+1))) // y ^ 2 = 1} ≃
        {a : Fin r → ZMod (2^(n+1)) // 2 • a = 0} :=
      Equiv.subtypeEquiv Multiplicative.toAdd (fun y => by
        have h1 : y ^ 2 = Multiplicative.ofAdd (2 • y.toAdd) := by
          rw [← ofAdd_toAdd y]
          exact (ofAdd_nsmul 2 y.toAdd).symm
        rw [h1, ofAdd_eq_one])
    rw [Fintype.card_congr he1, Fintype.card_congr he2]
    exact card_two_torsion_pi r n
  -- Every `2`-torsion element is killed by `q`.
  have hsub : ∀ x : G, x ^ 2 = 1 → q x = 1 := by
    intro x hx
    have ha : 2 • (eG x).toAdd = 0 := (hiff x).mp hx
    have hcoord : ∀ i, (eG x).toAdd i = 0 ∨
        (eG x).toAdd i = (2^n : ZMod (2^(n+1))) := by
      intro i
      have hi : 2 * ((eG x).toAdd i) = 0 := by
        have h := congrFun ha i
        simpa [Pi.smul_apply, nsmul_eq_mul] using h
      exact (zmod_two_mul_eq_zero_iff n _).mp hi
    -- the exponent of `H` divides `2^n`.
    have hexpH : ∀ y : H, y ^ (2^n) = 1 := by
      intro y
      have hb : (eH y) ^ (2^n) = 1 := by
        rw [← ofAdd_toAdd (eH y), ← ofAdd_nsmul, ofAdd_eq_one]
        funext i
        simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
      calc y ^ (2^n) = (eH.symm (eH y)) ^ (2^n) := by rw [MulEquiv.symm_apply_apply]
        _ = eH.symm ((eH y) ^ (2^n)) := (map_pow eH.symm (eH y) (2^n)).symm
        _ = eH.symm 1 := by rw [hb]
        _ = 1 := map_one eH.symm
    -- the `0/1`-vector whose `2^n`-th power is `x`.
    let c : Fin r → ZMod (2^(n+1)) :=
      fun i => if (eG x).toAdd i = 0 then 0 else 1
    have hca : (2^n : ℕ) • c = (eG x).toAdd := by
      funext i
      simp only [Pi.smul_apply]
      rcases hcoord i with h0 | h2
      · rw [h0, show c i = 0 from by simp [c, h0], smul_zero]
      · have hne : ¬ ((eG x).toAdd i = 0) := by rw [h2]; exact zmod_two_pow_ne_zero n
        rw [show c i = 1 from by simp [c, hne], h2, nsmul_eq_mul, mul_one]
        push_cast
        rfl
    have hy : x = (eG.symm (Multiplicative.ofAdd c)) ^ (2^n) := by
      apply eG.injective
      rw [map_pow, MulEquiv.apply_symm_apply, ← ofAdd_nsmul, hca, ofAdd_toAdd]
    rw [hy, map_pow]
    exact hexpH (q (eG.symm (Multiplicative.ofAdd c)))
  -- Equal cardinalities force the `2`-torsion to be *all* of the kernel.
  intro x
  refine ⟨?_, hsub x⟩
  intro hx
  let f : {y : G // y ^ 2 = 1} → MonoidHom.ker q := fun y => ⟨y.1, hsub y.1 y.2⟩
  have hinj : Function.Injective f := by
    intro a b hab
    refine Subtype.ext ?_
    exact congrArg (fun z : MonoidHom.ker q => (z : G)) hab
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, by rw [hcard2, hcardK]⟩
  obtain ⟨y, hy⟩ := hbij.2 ⟨x, hx⟩
  have hyx : y.1 = x := congrArg (fun z : MonoidHom.ker q => (z : G)) hy
  rw [← hyx]
  exact y.2

end NK.NUV2.TowerRank
