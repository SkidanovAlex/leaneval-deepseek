import Mathlib
import Submission.Work.HP.NA.SumDefs
import Submission.Work.HP.NA.exists_lam_gcdMinors2

/-!
# Counting `v` with `p^e ∣ gcdMinors2 u (irep v)`

Let `p` be a prime, `e ≤ r`, and `u : (ℤ)^{n+1}` a vector with some coordinate not divisible
by `p`.  We bound the number of `v : (ZMod (p^r))^{n+1}` such that the `(p:ℤ)^e`-th power
divides the gcd of the `2×2` minors of the matrix with columns `u` and (the integer
representative of) `v`:

  `#{v} ≤ p^e * p^((r-e)*(n+1))`.

The mathematical content is the following.  By `exists_lam_gcdMinors2` the hypothesis
`(p:ℤ)^e ∣ gcdMinors2 u (irep v)` is equivalent to `irep v ≡ c·u (mod p^e)` for a single
integer `c`; i.e. the *reduction* of `v` modulo `p^e` lies in the span of `u` in
`(ZMod (p^e))^{n+1}`.  Since that span has at most `p^e` elements and the reduction
`(ZMod (p^r))^{n+1} → (ZMod (p^e))^{n+1}` has fibres of size `p^((r-e)*(n+1))`, the bound
follows.  The proof below makes this quantitative by an explicit injection
`v ↦ (canonical scalar, coordinates divided by p^e)`.

Because `u` has a coordinate `u i₀` invertible modulo `p^e`, the witness `c` of the
scalarity is *unique* (it is `irep v i₀ * (u i₀)^{-1}`), so the mapping is injective.
-/

noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.HP.NA

open Work.HP

/-- Monotonicity of `Nat.card` for subtypes under an implication. -/
private lemma natCard_subtype_le_of_imp {α : Type*} [Finite α] {P Q : α → Prop}
    (h : ∀ a, P a → Q a) : Nat.card {a // P a} ≤ Nat.card {a // Q a} := by
  refine Nat.card_le_card_of_injective
    (fun a : {a // P a} => (⟨a.1, h a.1 a.2⟩ : {a // Q a})) ?_
  intro x y hxy
  have h' : ((⟨x.1, h x.1 x.2⟩ : {a // Q a}) : α)
      = ((⟨y.1, h y.1 y.2⟩ : {a // Q a}) : α) :=
    congrArg (fun z : {a // Q a} => (z : α)) hxy
  exact Subtype.ext h'

/-- Counting lemma.  For `a : Fin (n+1) → ℤ` with a coordinate not divisible by the prime `p`,
the number of `b : (ZMod (p^r))^{n+1}` congruent modulo `p^e` to a scalar multiple of `a` is at
most `p^e * p^((r-e)*(n+1))`. -/
theorem scalar_lift_card_le (p r n e : ℕ) (hp : p.Prime) (he : e ≤ r) (a : Fin (n + 1) → ℤ)
    (ha : ∃ i, ¬ (p : ℤ) ∣ a i) :
    Nat.card {b : Fin (n + 1) → ZMod (p ^ r) //
        ∃ c : ZMod (p ^ e), ∀ i, ((b i).val : ZMod (p ^ e)) = c * ((a i : ℤ) : ZMod (p ^ e))}
      ≤ p ^ e * p ^ ((r - e) * (n + 1)) := by
  classical
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hpr : p ^ r = p ^ e * p ^ (r - e) := by rw [← pow_add]; congr 1; omega
  -- each coordinate has a well-defined quotient in `[0, p^(r-e))`
  have hdiv : ∀ x : ZMod (p ^ r), x.val / p ^ e < p ^ (r - e) := by
    intro x
    have hlt : x.val < p ^ e * p ^ (r - e) := by rw [← hpr]; exact x.val_lt
    exact Nat.div_lt_of_lt_mul hlt
  -- the residue modulo `p^e` together with the quotient by `p^e` determines the element
  have hval_eq : ∀ x x' : ZMod (p ^ r),
      ((x.val : ℕ) : ZMod (p ^ e)) = ((x'.val : ℕ) : ZMod (p ^ e)) →
        x.val / p ^ e = x'.val / p ^ e → x = x' := by
    intro x x' h1 h2
    apply ZMod.val_injective
    have e1 : x.val % p ^ e = x'.val % p ^ e := by
      have := congrArg ZMod.val h1
      rwa [ZMod.val_natCast, ZMod.val_natCast] at this
    calc x.val = p ^ e * (x.val / p ^ e) + x.val % p ^ e := (Nat.div_add_mod x.val (p ^ e)).symm
      _ = p ^ e * (x'.val / p ^ e) + x'.val % p ^ e := by rw [h2, e1]
      _ = x'.val := Nat.div_add_mod x'.val (p ^ e)
  obtain ⟨i0, hi0⟩ := ha
  -- the pivot coordinate is a unit modulo `p^e`
  have hunit : IsUnit (((a i0 : ℤ)) : ZMod (p ^ e)) := by
    rw [ZMod.coe_int_isUnit_iff_isCoprime, Int.isCoprime_iff_gcd_eq_one]
    simp only [Int.gcd, Int.natAbs_natCast]
    rw [← Nat.coprime_iff_gcd_eq_one]
    apply Nat.Coprime.pow_left
    rw [hp.coprime_iff_not_dvd]
    have hwd : p ∣ (a i0).natAbs ↔ (p : ℤ) ∣ a i0 := by
      have := Int.natAbs_dvd_natAbs (a := (p : ℤ)) (b := a i0)
      simpa using this
    rw [hwd]; exact hi0
  obtain ⟨u₀, hu₀⟩ := hunit
  -- canonical scalar attached to `b`
  let cb : (Fin (n + 1) → ZMod (p ^ r)) → ZMod (p ^ e) :=
    fun b => ((b i0).val : ZMod (p ^ e)) * ((u₀⁻¹ : (ZMod (p ^ e))ˣ) : ZMod (p ^ e))
  -- the witness scalar is unique, hence equal to the canonical one
  have cb_eq : ∀ (b : Fin (n + 1) → ZMod (p ^ r)) (c : ZMod (p ^ e)),
      (∀ i, ((b i).val : ZMod (p ^ e)) = c * ((a i : ℤ) : ZMod (p ^ e))) → c = cb b := by
    intro b c hc
    have h0 := hc i0
    rw [← hu₀] at h0
    change c = ((b i0).val : ZMod (p ^ e)) * ((u₀⁻¹ : (ZMod (p ^ e))ˣ) : ZMod (p ^ e))
    rw [h0, mul_assoc, Units.mul_inv, mul_one]
  -- the injection
  let Φ : {b : Fin (n + 1) → ZMod (p ^ r) //
        ∃ c : ZMod (p ^ e), ∀ i, ((b i).val : ZMod (p ^ e)) = c * ((a i : ℤ) : ZMod (p ^ e))} →
      ZMod (p ^ e) × (Fin (n + 1) → Fin (p ^ (r - e))) :=
    fun b => (cb b.1, fun i => ⟨(b.1 i).val / p ^ e, hdiv (b.1 i)⟩)
  have hΦ : Function.Injective Φ := by
    intro b b' h
    have hcb : cb b.1 = cb b'.1 := congrArg Prod.fst h
    have hidx : ∀ i, (b.1 i).val / p ^ e = (b'.1 i).val / p ^ e :=
      fun i => congrArg (fun z => (z.2 i).val) h
    have hres : ∀ i, ((b.1 i).val : ZMod (p ^ e)) = ((b'.1 i).val : ZMod (p ^ e)) := by
      intro i
      obtain ⟨c, hc⟩ := b.2
      obtain ⟨c', hc'⟩ := b'.2
      have hcc : c = c' := by
        rw [cb_eq b.1 c hc, cb_eq b'.1 c' hc', hcb]
      rw [hc i, hc' i, hcc]
    exact Subtype.ext (funext fun i => hval_eq (b.1 i) (b'.1 i) (hres i) (hidx i))
  have hcard := Nat.card_le_card_of_injective Φ hΦ
  rwa [Nat.card_prod, Nat.card_zmod, Nat.card_fun, Nat.card_fin, Nat.card_fin,
    ← pow_mul] at hcard

/-- Characterisation: if `u` has a coordinate not divisible by the prime `p`, then
`(p:ℤ)^e ∣ gcdMinors2 u (irep v)` holds exactly when `v` reduces modulo `p^e` to a scalar
multiple of `u`. -/
theorem dvd_gcdMinors2_irep_iff {n p r e : ℕ} (hp : p.Prime)
    (u : Fin (n + 1) → ℤ) (hu : ∃ i, ¬ (p : ℤ) ∣ u i) (v : Fin (n + 1) → ZMod (p ^ r)) :
    ((p : ℤ) ^ e ∣ Work.HP.gcdMinors2 u (Work.HP.NA.irep v)) ↔
      ∃ c : ZMod (p ^ e), ∀ i, ((v i).val : ZMod (p ^ e)) = c * ((u i : ℤ) : ZMod (p ^ e)) := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := exists_lam_gcdMinors2 hp u (irep v) hu h
    refine ⟨(c : ZMod (p ^ e)), fun i => ?_⟩
    have hci := hc i
    rw [← Nat.cast_pow] at hci
    have h0 : (((irep v i - c * u i : ℤ)) : ZMod (p ^ e)) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (irep v i - c * u i) (p ^ e)).mpr hci
    have h1 : ((irep v i : ℤ) : ZMod (p ^ e))
        = (c : ZMod (p ^ e)) * ((u i : ℤ) : ZMod (p ^ e)) := by
      rw [Int.cast_sub, Int.cast_mul, sub_eq_zero] at h0
      exact h0
    calc ((v i).val : ZMod (p ^ e)) = ((irep v i : ℤ) : ZMod (p ^ e)) := by
          simp [Work.HP.NA.irep]
      _ = (c : ZMod (p ^ e)) * ((u i : ℤ) : ZMod (p ^ e)) := h1
  · rintro ⟨c, hc⟩
    refine (Work.HP.NA.gcdMinors2_dvd_iff ((p : ℤ) ^ e) u (irep v)).mpr (fun i j => ?_)
    rw [← Nat.cast_pow]
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd
      (u i * irep v j - u j * irep v i) (p ^ e)).mp ?_
    have hi : ((irep v i : ℤ) : ZMod (p ^ e)) = c * ((u i : ℤ) : ZMod (p ^ e)) := by
      rw [show ((irep v i : ℤ) : ZMod (p ^ e)) = ((v i).val : ZMod (p ^ e)) by
        simp [Work.HP.NA.irep]]
      exact hc i
    have hj : ((irep v j : ℤ) : ZMod (p ^ e)) = c * ((u j : ℤ) : ZMod (p ^ e)) := by
      rw [show ((irep v j : ℤ) : ZMod (p ^ e)) = ((v j).val : ZMod (p ^ e)) by
        simp [Work.HP.NA.irep]]
      exact hc j
    simp only [Int.cast_sub, Int.cast_mul]
    rw [hi, hj]
    ring

theorem card_dvd_gcdMinors2_le {n p r e : ℕ} (hp : p.Prime) (he : e ≤ r)
    (u : Fin (n + 1) → ℤ) (hu : ∃ i, ¬ (p : ℤ) ∣ u i) :
    Nat.card {v : Fin (n + 1) → ZMod (p ^ r) //
        (p : ℤ) ^ e ∣ Work.HP.gcdMinors2 u (Work.HP.NA.irep v)}
      ≤ p ^ e * p ^ ((r - e) * (n + 1)) := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hmono := natCard_subtype_le_of_imp
    (P := fun v : Fin (n + 1) → ZMod (p ^ r) =>
      (p : ℤ) ^ e ∣ Work.HP.gcdMinors2 u (Work.HP.NA.irep v))
    (Q := fun b : Fin (n + 1) → ZMod (p ^ r) =>
      ∃ c : ZMod (p ^ e),
        ∀ i, ((b i).val : ZMod (p ^ e)) = c * ((u i : ℤ) : ZMod (p ^ e)))
    (fun v hv => (dvd_gcdMinors2_irep_iff hp u hu v).mp hv)
  exact le_trans hmono (scalar_lift_card_le p r n e hp he u hu)

end Work.HP.NA
