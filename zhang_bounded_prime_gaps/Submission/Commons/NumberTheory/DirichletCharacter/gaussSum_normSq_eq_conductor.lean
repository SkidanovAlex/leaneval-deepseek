import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.NumberTheory.DirichletCharacter.gaussSum_norm_sq_of_isPrimitive

/-!
# The squared norm of the Gauss sum of an arbitrary Dirichlet character

For a Dirichlet character `χ` of modulus `q` with conductor `d`, the Gauss sum of `χ⁻¹`
against the standard additive character has squared norm

`‖τ(χ⁻¹)‖² = d` if `d` is coprime to `q / d` and `q / d` is squarefree, and `0` otherwise.

The proof proceeds by writing `χ = changeLevel φ` with `φ = χ.primitiveCharacter` the primitive
character of conductor `d = χ.conductor`, and expanding the coprimality indicator via Möbius
inversion: `[Coprime n q] = ∑_{c | q} μ(c) [c | n]`.  Summing against `φ` and collecting terms
leaves only the contribution of `c = q / d`, since all other contributions either involve a
character value at a non-unit (when `(c, d) > 1`) or a vanishing additive-character average
(when `c | q/d`, `c ≠ q/d`).  The single remaining Gauss sum is that of the primitive character
`φ`, whose squared norm is `d` by `gaussSum_norm_sq_of_isPrimitive`.
-/

open Complex DirichletCharacter
open scoped Real BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

namespace Commons.NumberTheory.DirichletCharacter


lemma sum_moebius_divisors_eq_ite (n : ℕ) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℤ)) = if n = 1 then 1 else 0 := by
  have h : (↑ArithmeticFunction.moebius * ↑ArithmeticFunction.zeta : ArithmeticFunction ℤ) n
      = (1 : ArithmeticFunction ℤ) n := by
    rw [ArithmeticFunction.moebius_mul_coe_zeta]
  rw [ArithmeticFunction.coe_mul_zeta_apply] at h
  simpa [ArithmeticFunction.one_apply] using h

lemma sum_moebius_mul_ite_dvd (a n : ℕ) (hn : n ≠ 0) :
    (∑ c ∈ n.divisors, (ArithmeticFunction.moebius c : ℂ) * (if c ∣ a then 1 else 0))
      = if Nat.Coprime a n then 1 else 0 := by
  have h1 : (n.divisors.filter (fun c => c ∣ a)) = (a.gcd n).divisors := by
    ext c
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hc1, _⟩, hc2⟩
      exact ⟨Nat.dvd_gcd hc2 hc1, fun h => hn (Nat.eq_zero_of_gcd_eq_zero_right h)⟩
    · rintro ⟨h, -⟩
      exact ⟨⟨(Nat.dvd_gcd_iff.mp h).2, hn⟩, (Nat.dvd_gcd_iff.mp h).1⟩
  have h2 : ∀ c, (ArithmeticFunction.moebius c : ℂ) * (if c ∣ a then 1 else 0)
      = if c ∣ a then (ArithmeticFunction.moebius c : ℂ) else 0 := by
    intro c; split_ifs <;> simp
  simp_rw [h2]
  rw [← Finset.sum_filter, h1]
  rw [← Int.cast_sum, sum_moebius_divisors_eq_ite]
  by_cases h : Nat.Coprime a n
  · rw [if_pos h, if_pos (Nat.coprime_iff_gcd_eq_one.mp h)]; norm_num
  · rw [if_neg h, if_neg (fun hh => h (Nat.coprime_iff_gcd_eq_one.mpr hh))]; norm_num

lemma stdAddChar_mul_div {c k : ℕ} [NeZero k] [NeZero (c*k)] (b : ℕ) :
    ZMod.stdAddChar (N := c*k) ((c*b : ℕ) : ZMod (c*k)) = ZMod.stdAddChar (N := k) (b : ZMod k) := by
  have e1 : ZMod.stdAddChar (N := c*k) ((c*b : ℕ) : ZMod (c*k))
      = cexp (2 * π * I * ((c*b : ℕ) : ℂ) / ((c*k : ℕ) : ℂ)) := by
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_natCast]
  have e2 : ZMod.stdAddChar (N := k) (b : ZMod k)
      = cexp (2 * π * I * ((b : ℕ) : ℂ) / ((k : ℕ) : ℂ)) := by
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_natCast]
  rw [e1, e2]
  congr 1
  have hk : (k : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne k
  have hck : ((c*k : ℕ) : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne (c*k)
  rw [div_eq_div_iff hck hk]
  push_cast
  ring

lemma sum_stdAddChar_eq_zero {n : ℕ} [NeZero n] (hn : n ≠ 1) :
    (∑ x : ZMod n, ZMod.stdAddChar x) = 0 := by
  apply AddChar.sum_eq_zero_of_ne_one
  intro h
  apply hn
  have h1 : ZMod.stdAddChar (N := n) (1 : ZMod n) = ZMod.stdAddChar (N := n) 0 := by
    rw [h, AddChar.map_zero_eq_one, AddChar.one_apply]
  have h10 : (1 : ZMod n) = 0 := ZMod.injective_stdAddChar h1
  have h10' : ((1 : ℤ) : ZMod n) = 0 := by push_cast; exact h10
  have hdvd : (n : ℤ) ∣ (1 : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd 1 n).mp h10'
  have : n ∣ 1 := by exact_mod_cast hdvd
  exact Nat.dvd_one.mp this

lemma sum_zmod_eq_sum_range (q : ℕ) [NeZero q] (f : ZMod q → ℂ) :
    (∑ a : ZMod q, f a) = ∑ a ∈ Finset.range q, f (a : ZMod q) := by
  refine Finset.sum_bij (fun (a : ZMod q) (_ : a ∈ Finset.univ) => a.val) ?_ ?_ ?_ ?_
  · intro a _
    simp only [Finset.mem_range]
    exact ZMod.val_lt a
  · intro a _ b _ h
    exact ZMod.val_injective q h
  · intro b hb
    simp only [Finset.mem_range] at hb
    exact ⟨(b : ZMod q), Finset.mem_univ _, by simp [ZMod.val_natCast, Nat.mod_eq_of_lt hb]⟩
  · intro a _
    simp

lemma sum_range_mul_decomp {d m' : ℕ} (hd : 0 < d) (f : ℕ → ℂ) :
    ∑ b ∈ Finset.range (d * m'), f b
      = ∑ s ∈ Finset.range m', ∑ r ∈ Finset.range d, f (r + d * s) := by
  have hprod : (∑ p ∈ (Finset.range m').product (Finset.range d), f (p.2 + d * p.1))
      = ∑ s ∈ Finset.range m', ∑ r ∈ Finset.range d, f (r + d * s) := Finset.sum_product ..
  rw [← hprod]
  refine Finset.sum_bij (fun b (_ : b ∈ Finset.range (d*m')) => (b / d, b % d)) ?_ ?_ ?_ ?_
  · intro b hb
    simp only [Finset.mem_range] at hb
    simp only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_range]
    exact ⟨Nat.div_lt_of_lt_mul hb, Nat.mod_lt _ hd⟩
  · intro b1 hb1 b2 hb2 h
    have h1 : b1 / d = b2 / d := by simpa using congrArg Prod.fst h
    have h2 : b1 % d = b2 % d := by simpa using congrArg Prod.snd h
    rw [← Nat.mod_add_div b1 d, ← Nat.mod_add_div b2 d, h1, h2]
  · intro p hp
    obtain ⟨s, r⟩ := p
    simp only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_range] at hp
    obtain ⟨hs, hr⟩ := hp
    refine ⟨r + d * s, ?_, ?_⟩
    · rw [Finset.mem_range]
      calc r + d * s < d + d * s := by omega
        _ = d * (s+1) := by ring
        _ ≤ d * m' := by exact Nat.mul_le_mul_left d (by omega)
    · have h1 : (r + d*s)/d = s := by rw [Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt hr, zero_add]
      have h2 : (r + d*s) % d = r := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
      rw [h1, h2]
  · intro b hb
    rw [Nat.mod_add_div]

lemma inner_sum_vanish {c d m' N : ℕ} [NeZero m'] [NeZero N]
    (ψ : DirichletCharacter ℂ d) (hN : N = (c*d)*m') (hd : 0 < d) (hm' : 2 ≤ m') :
    (∑ b ∈ Finset.range (d*m'), ψ ((c*b : ℕ) : ZMod d)
        * ZMod.stdAddChar (N := N) ((c*b : ℕ) : ZMod N)) = 0 := by
  subst hN
  set f : ℕ → ℂ := fun b => ψ ((c*b : ℕ) : ZMod d)
        * ZMod.stdAddChar (N := (c*d)*m') ((c*b : ℕ) : ZMod ((c*d)*m')) with hfdef
  have hf : ∀ r s : ℕ, f (r + d*s) = f r * ZMod.stdAddChar (N := m') (s : ZMod m') := by
    intro r s
    have hcast : ((c*(r + d*s) : ℕ) : ZMod ((c*d)*m'))
        = ((c*r : ℕ) : ZMod ((c*d)*m')) + ((c*d*s : ℕ) : ZMod ((c*d)*m')) := by
      push_cast; ring
    have hpsi : ((c*(r + d*s) : ℕ) : ZMod d) = ((c*r : ℕ) : ZMod d) := by
      push_cast; rw [ZMod.natCast_self]; ring
    simp only [hfdef]
    rw [hpsi, hcast, AddChar.map_add_eq_mul, stdAddChar_mul_div (c := c*d) (k := m') s]
    ring
  rw [sum_range_mul_decomp hd f]
  calc ∑ s ∈ Finset.range m', ∑ r ∈ Finset.range d, f (r + d*s)
      = ∑ s ∈ Finset.range m', ∑ r ∈ Finset.range d, f r * ZMod.stdAddChar (N := m') (s : ZMod m') := by
        refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun r _ => ?_
        rw [hf]
    _ = ∑ s ∈ Finset.range m', (ZMod.stdAddChar (N := m') (s : ZMod m') * ∑ r ∈ Finset.range d, f r) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun r _ => ?_; ring
    _ = (∑ s ∈ Finset.range m', ZMod.stdAddChar (N := m') (s : ZMod m')) * (∑ r ∈ Finset.range d, f r) := by
        rw [Finset.sum_mul]
    _ = 0 := by
        have hsum : (∑ s ∈ Finset.range m', ZMod.stdAddChar (N := m') (s : ZMod m')) = 0 := by
          rw [← sum_zmod_eq_sum_range m' (fun x => ZMod.stdAddChar x)]
          exact sum_stdAddChar_eq_zero (by omega)
        rw [hsum, zero_mul]

lemma inner_sum_main {c d N : ℕ} [NeZero d] [NeZero N] (ψ : DirichletCharacter ℂ d) (hN : N = c*d) :
    (∑ b ∈ Finset.range d, ψ ((c*b : ℕ) : ZMod d) * ZMod.stdAddChar (N := N) ((c*b : ℕ) : ZMod N))
      = ψ (c : ZMod d) * gaussSum ψ (ZMod.stdAddChar (N := d)) := by
  subst hN
  have h1 : ∀ b, ψ ((c*b : ℕ) : ZMod d) = ψ (c : ZMod d) * ψ (b : ZMod d) := by
    intro b; rw [Nat.cast_mul, map_mul]
  have h2 : ∀ b, ZMod.stdAddChar (N := c*d) ((c*b : ℕ) : ZMod (c*d)) = ZMod.stdAddChar (N := d) (b : ZMod d) :=
    fun b => stdAddChar_mul_div (c := c) (k := d) b
  have key : (∑ x ∈ Finset.range d, ψ (x : ZMod d) * ZMod.stdAddChar (N := d) (x : ZMod d))
      = gaussSum ψ (ZMod.stdAddChar (N := d)) := by
    rw [gaussSum, sum_zmod_eq_sum_range d (fun x => ψ x * ZMod.stdAddChar x)]
  simp_rw [h1, h2]
  rw [← key, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

lemma inner_sum_zero_of_not_coprime {c d M N : ℕ} [NeZero M] (ψ : DirichletCharacter ℂ d)
    (h : ¬ Nat.Coprime c d) :
    (∑ b ∈ Finset.range N, ψ ((c*b : ℕ) : ZMod d) * ZMod.stdAddChar (N := M) ((c*b : ℕ) : ZMod M)) = 0 := by
  refine Finset.sum_eq_zero fun b _ => ?_
  have : ¬ IsUnit (((c*b : ℕ)) : ZMod d) := by
    rw [ZMod.isUnit_iff_coprime]
    intro hc
    exact h (hc.coprime_dvd_left (Nat.dvd_mul_right c b))
  rw [MulChar.map_nonunit ψ this, zero_mul]

lemma coe_char_eq (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (n : ℕ) :
    χ (n : ZMod q) = χ.primitiveCharacter (n : ZMod χ.conductor)
      * (if Nat.Coprime n q then 1 else 0) := by
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  by_cases h : Nat.Coprime n q
  · rw [if_pos h, mul_one]
    have hc : IsCoprime (n : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.mpr h
    have h2 := DirichletCharacter.changeLevel_eq_cast_of_dvd' χ.primitiveCharacter
      χ.conductor_dvd_level (a := (n : ℤ)) hc
    rw [DirichletCharacter.changeLevel_primitiveCharacter] at h2
    simpa using h2
  · rw [if_neg h, mul_zero]
    rw [MulChar.map_nonunit]
    rw [ZMod.isUnit_iff_coprime]
    exact h

lemma sum_ite_dvd_eq (q c : ℕ) (hc : c ∣ q) (hc0 : c ≠ 0) (g : ℕ → ℂ) :
    ∑ n ∈ Finset.range q, (if c ∣ n then g n else 0) = ∑ b ∈ Finset.range (q/c), g (c*b) := by
  rw [← Finset.sum_filter]
  have hcpos : 0 < c := Nat.pos_of_ne_zero hc0
  refine Finset.sum_bij (fun n (_ : n ∈ (Finset.range q).filter (fun n => c ∣ n)) => n / c) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    simp only [Finset.mem_range]
    obtain ⟨hnq, hcn⟩ := hn
    rw [Nat.div_lt_iff_lt_mul hcpos, Nat.mul_comm (q/c) c, Nat.mul_div_cancel' hc]
    exact hnq
  · intro n1 hn1 n2 hn2 h
    simp only [Finset.mem_filter, Finset.mem_range] at hn1 hn2
    rw [← Nat.mul_div_cancel' hn1.2, ← Nat.mul_div_cancel' hn2.2, h]
  · intro b hb
    simp only [Finset.mem_range] at hb
    refine ⟨c*b, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      have hlt : c * b < q := by
        have := (Nat.mul_lt_mul_left hcpos).mpr hb
        rwa [Nat.mul_div_cancel' hc] at this
      exact ⟨hlt, Nat.dvd_mul_right c b⟩
    · exact Nat.mul_div_cancel_left b hcpos
  · intro n hn
    simp only [Finset.mem_filter] at hn
    rw [Nat.mul_div_cancel' hn.2]

lemma nat_div_eq_of_mul_eq {a b q : ℕ} (hb : 0 < b) (h : a * b = q) : q / b = a := by
  rw [← h, Nat.mul_comm a b, Nat.mul_div_cancel_left a hb]

lemma nat_div_eq_of_eq {a b c d : ℕ} (hc : 0 < c) (h : a = b * (c * d)) : a / c = b * d := by
  rw [h, ← Nat.mul_assoc b c d, Nat.mul_comm b c, Nat.mul_assoc c b d,
    Nat.mul_div_cancel_left _ hc]

lemma nat_eq_mul_of_eq {a b c d : ℕ} (h : a = b * (c * d)) : a = (c * b) * d := by
  rw [h]; ring

-- MAIN
theorem gaussSum_eq_moebius_mul (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] :
    gaussSum χ (ZMod.stdAddChar (N := q))
      = (ArithmeticFunction.moebius (q / χ.conductor) : ℂ)
        * χ.primitiveCharacter ((q / χ.conductor : ℕ) : ZMod χ.conductor)
        * gaussSum χ.primitiveCharacter (ZMod.stdAddChar (N := χ.conductor)) := by
  have hdvd : χ.conductor ∣ q := χ.conductor_dvd_level
  have hq : χ.conductor * (q / χ.conductor) = q := Nat.mul_div_cancel' hdvd
  have hposd : 0 < χ.conductor := Nat.pos_of_ne_zero χ.conductor_ne_zero
  have hposq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hposm : 0 < q / χ.conductor := Nat.div_pos (Nat.le_of_dvd hposq hdvd) hposd
  set m : ℕ := q / χ.conductor with hmdef
  rw [gaussSum, sum_zmod_eq_sum_range q (fun x => χ x * ZMod.stdAddChar x)]
  have hstep2 : ∀ n : ℕ, χ (n : ZMod q) * ZMod.stdAddChar (N := q) (n : ZMod q)
      = χ.primitiveCharacter (n : ZMod χ.conductor) * ZMod.stdAddChar (N := q) (n : ZMod q)
          * (if Nat.Coprime n q then 1 else 0) := by
    intro n; rw [coe_char_eq q χ n]; ring
  simp_rw [hstep2]
  have hstep3 : ∀ n : ℕ, (if Nat.Coprime n q then (1:ℂ) else 0)
      = ∑ c ∈ q.divisors, (ArithmeticFunction.moebius c : ℂ) * (if c ∣ n then 1 else 0) :=
    fun n => (sum_moebius_mul_ite_dvd n q (NeZero.ne q)).symm
  simp_rw [hstep3]
  have hstep4 : ∀ n : ℕ,
      χ.primitiveCharacter (n : ZMod χ.conductor) * ZMod.stdAddChar (N := q) (n : ZMod q)
        * (∑ c ∈ q.divisors, (ArithmeticFunction.moebius c : ℂ) * (if c ∣ n then 1 else 0))
      = ∑ c ∈ q.divisors, (ArithmeticFunction.moebius c : ℂ)
          * (if c ∣ n then χ.primitiveCharacter (n : ZMod χ.conductor) * ZMod.stdAddChar (N := q) (n : ZMod q) else 0) := by
    intro n
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs <;> ring
  simp_rw [hstep4]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  -- evaluate each inner sum
  have hJ : ∀ c ∈ q.divisors,
      (∑ n ∈ Finset.range q, if c ∣ n then χ.primitiveCharacter (n : ZMod χ.conductor) * ZMod.stdAddChar (N := q) (n : ZMod q) else 0)
      = ∑ b ∈ Finset.range (q/c), χ.primitiveCharacter ((c*b : ℕ) : ZMod χ.conductor) * ZMod.stdAddChar (N := q) ((c*b : ℕ) : ZMod q) := by
    intro c hcmem
    rw [Nat.mem_divisors] at hcmem
    exact sum_ite_dvd_eq q c hcmem.1 (fun h => hcmem.2 (Nat.eq_zero_of_zero_dvd (h ▸ hcmem.1)))
      (fun n => χ.primitiveCharacter (n : ZMod χ.conductor) * ZMod.stdAddChar (N := q) (n : ZMod q))
  have hJc : ∀ c ∈ q.divisors, (ArithmeticFunction.moebius c : ℂ)
      * (∑ b ∈ Finset.range (q/c), χ.primitiveCharacter ((c*b : ℕ) : ZMod χ.conductor) * ZMod.stdAddChar (N := q) ((c*b : ℕ) : ZMod q))
      = if c = m then (ArithmeticFunction.moebius m : ℂ)
          * χ.primitiveCharacter (m : ZMod χ.conductor)
          * gaussSum χ.primitiveCharacter (ZMod.stdAddChar (N := χ.conductor)) else 0 := by
    intro c hcmem
    rw [Nat.mem_divisors] at hcmem
    by_cases hcm : c = m
    · subst hcm
      rw [if_pos rfl, mul_assoc]
      congr 1
      have hqmm : q / m = χ.conductor := nat_div_eq_of_mul_eq hposm hq
      have hN : q = m * χ.conductor := by rw [Nat.mul_comm]; exact hq.symm
      rw [hqmm]
      exact inner_sum_main (c := m) (d := χ.conductor) (N := q) χ.primitiveCharacter hN
    · rw [if_neg hcm]
      by_cases hcmdvd : c ∣ m
      · -- vanish
        have hc0 : c ≠ 0 := fun h => hcmem.2 (Nat.eq_zero_of_zero_dvd (h ▸ hcmem.1))
        have hcpos : 0 < c := Nat.pos_of_ne_zero hc0
        have hmdecomp : m = c * (m / c) := (Nat.mul_div_cancel' hcmdvd).symm
        have hmnz : m / c ≠ 0 := by
          intro h0; rw [h0, mul_zero] at hmdecomp; omega
        have hmc2 : 2 ≤ m / c := by
          have h2 : m / c ≠ 1 := by
            intro h0; rw [h0, mul_one] at hmdecomp; exact hcm hmdecomp.symm
          exact Nat.succ_le_of_lt (Nat.lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr hmnz) (Ne.symm h2))
        haveI : NeZero (m / c) := ⟨hmnz⟩
        have hh : q = χ.conductor * (c * (m / c)) := by rw [← hmdecomp]; exact hq.symm
        have hqc : q / c = χ.conductor * (m / c) := nat_div_eq_of_eq hcpos hh
        have hN : q = (c * χ.conductor) * (m / c) := nat_eq_mul_of_eq hh
        rw [hqc, inner_sum_vanish χ.primitiveCharacter hN hposd hmc2]
        ring
      · -- not coprime
        have hcdvd : c ∣ χ.conductor * m := by rw [hq]; exact hcmem.1
        have hcop : ¬ Nat.Coprime c χ.conductor := by
          intro hc
          exact hcmdvd (hc.dvd_of_dvd_mul_left hcdvd)
        rw [inner_sum_zero_of_not_coprime (ψ := χ.primitiveCharacter) (h := hcop)]
        ring
  rw [Finset.sum_congr rfl (fun c hcmem => by rw [hJ c hcmem]),
      Finset.sum_congr rfl hJc]
  rw [Finset.sum_ite_eq' q.divisors m (fun _ => (ArithmeticFunction.moebius m : ℂ)
      * χ.primitiveCharacter (m : ZMod χ.conductor)
      * gaussSum χ.primitiveCharacter (ZMod.stdAddChar (N := χ.conductor)))]
  rw [if_pos (Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hdvd, NeZero.ne q⟩)]

theorem gaussSum_normSq_eq_conductor (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) :
    ‖gaussSum (χ⁻¹) (ZMod.stdAddChar (N := q))‖ ^ 2
      = if Nat.Coprime χ.conductor (q / χ.conductor) ∧ Squarefree (q / χ.conductor)
          then (χ.conductor : ℝ) else 0 := by
  haveI hNc : NeZero (χ⁻¹).conductor := ⟨(χ⁻¹).conductor_ne_zero⟩
  rw [← DirichletCharacter.conductor_inv (χ := χ)]
  set A : ℂ := ((ArithmeticFunction.moebius (q / (χ⁻¹).conductor) : ℤ) : ℂ) with hAdef
  set ψ : DirichletCharacter ℂ (χ⁻¹).conductor := (χ⁻¹).primitiveCharacter with hψdef
  set G : ℂ := gaussSum ψ (ZMod.stdAddChar (N := (χ⁻¹).conductor)) with hGdef
  have hτ : gaussSum (χ⁻¹) (ZMod.stdAddChar (N := q))
      = A * ψ ((q / (χ⁻¹).conductor : ℕ) : ZMod (χ⁻¹).conductor) * G := by
    rw [gaussSum_eq_moebius_mul q (χ⁻¹)]
  have hstar : star (gaussSum (χ⁻¹) (ZMod.stdAddChar (N := q)))
      = A * ψ⁻¹ ((q / (χ⁻¹).conductor : ℕ) : ZMod (χ⁻¹).conductor) * star G := by
    rw [hτ, star_mul, star_mul]
    have hAstar : star A = A := by rw [hAdef]; simp
    rw [hAstar, MulChar.star_apply']
    ring
  have hA2 : A * A = ((if Squarefree (q / (χ⁻¹).conductor) then 1 else 0 : ℤ) : ℂ) := by
    rw [hAdef]
    rw [show ((ArithmeticFunction.moebius (q / (χ⁻¹).conductor) : ℤ) : ℂ)
        * ((ArithmeticFunction.moebius (q / (χ⁻¹).conductor) : ℤ) : ℂ)
        = ((ArithmeticFunction.moebius (q / (χ⁻¹).conductor) * ArithmeticFunction.moebius (q / (χ⁻¹).conductor) : ℤ) : ℂ) by
      push_cast; ring]
    rw [← pow_two, ArithmeticFunction.moebius_sq]
  have hψmul : ψ ((q / (χ⁻¹).conductor : ℕ) : ZMod (χ⁻¹).conductor)
        * ψ⁻¹ ((q / (χ⁻¹).conductor : ℕ) : ZMod (χ⁻¹).conductor)
      = ((if IsUnit ((q / (χ⁻¹).conductor : ℕ) : ZMod (χ⁻¹).conductor) then 1 else 0 : ℤ) : ℂ) := by
    have h1 : ψ * ψ⁻¹ = 1 := by rw [mul_comm]; exact MulChar.inv_mul ψ
    rw [← MulChar.mul_apply ψ ψ⁻¹, h1]
    by_cases hu : IsUnit ((q / (χ⁻¹).conductor : ℕ) : ZMod (χ⁻¹).conductor)
    · rw [if_pos hu, MulChar.one_apply hu]; norm_num
    · rw [if_neg hu, MulChar.map_nonunit _ hu]; norm_num
  have hG2 : G * star G = ((χ⁻¹).conductor : ℂ) := by
    have hprim : IsPrimitive ψ := by rw [hψdef]; exact (χ⁻¹).primitiveCharacter_isPrimitive
    have h1 : ‖G‖ ^ 2 = ((χ⁻¹).conductor : ℝ) := by
      rw [hGdef]; exact gaussSum_norm_sq_of_isPrimitive ψ hprim
    have h2 : Complex.normSq G = ((χ⁻¹).conductor : ℝ) := by rw [Complex.normSq_eq_norm_sq]; exact h1
    have h3 : (Complex.normSq G : ℂ) = ((χ⁻¹).conductor : ℂ) := by exact_mod_cast h2
    rw [Complex.normSq_eq_conj_mul_self] at h3
    simpa [mul_comm] using h3
  have hprod : gaussSum (χ⁻¹) (ZMod.stdAddChar (N := q))
        * star (gaussSum (χ⁻¹) (ZMod.stdAddChar (N := q)))
      = ((if Squarefree (q / (χ⁻¹).conductor) then 1 else 0 : ℤ) : ℂ)
        * ((if IsUnit ((q / (χ⁻¹).conductor : ℕ) : ZMod (χ⁻¹).conductor) then 1 else 0 : ℤ) : ℂ)
        * ((χ⁻¹).conductor : ℂ) := by
    rw [hstar, hτ]
    rw [show (A * ψ ((q / (χ⁻¹).conductor : ℕ) : ZMod (χ⁻¹).conductor) * G)
        * (A * ψ⁻¹ ((q / (χ⁻¹).conductor : ℕ) : ZMod (χ⁻¹).conductor) * star G)
        = (A * A) * (ψ ((q / (χ⁻¹).conductor : ℕ) : ZMod (χ⁻¹).conductor)
            * ψ⁻¹ ((q / (χ⁻¹).conductor : ℕ) : ZMod (χ⁻¹).conductor)) * (G * star G) from by ring,
      hA2, hψmul, hG2]
  have hnormSq : Complex.normSq (gaussSum (χ⁻¹) (ZMod.stdAddChar (N := q)))
      = (if Squarefree (q / (χ⁻¹).conductor)
            ∧ IsUnit ((q / (χ⁻¹).conductor : ℕ) : ZMod (χ⁻¹).conductor)
          then ((χ⁻¹).conductor : ℝ) else 0) := by
    have h3 : (Complex.normSq (gaussSum (χ⁻¹) (ZMod.stdAddChar (N := q))) : ℂ)
        = ((if Squarefree (q / (χ⁻¹).conductor)
            ∧ IsUnit ((q / (χ⁻¹).conductor : ℕ) : ZMod (χ⁻¹).conductor)
            then ((χ⁻¹).conductor : ℝ) else 0 : ℝ) : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self]
      have hconj : (starRingEnd ℂ) (gaussSum (χ⁻¹) (ZMod.stdAddChar (N := q)))
          = star (gaussSum (χ⁻¹) (ZMod.stdAddChar (N := q))) := rfl
      rw [hconj, mul_comm, hprod]
      by_cases h : Squarefree (q / (χ⁻¹).conductor)
          ∧ IsUnit ((q / (χ⁻¹).conductor : ℕ) : ZMod (χ⁻¹).conductor)
      · rw [if_pos h.1, if_pos h.2, if_pos h]; push_cast; ring
      · rw [if_neg h]
        rcases not_and_or.mp h with hs | hu
        · rw [if_neg hs]; simp
        · rw [if_neg hu]; simp
    exact_mod_cast h3
  have hnorm : ‖gaussSum (χ⁻¹) (ZMod.stdAddChar (N := q))‖ ^ 2
      = (if Squarefree (q / (χ⁻¹).conductor)
            ∧ IsUnit ((q / (χ⁻¹).conductor : ℕ) : ZMod (χ⁻¹).conductor)
          then ((χ⁻¹).conductor : ℝ) else 0) := by
    rw [← Complex.normSq_eq_norm_sq]; exact hnormSq
  rw [hnorm]
  by_cases h : Squarefree (q / (χ⁻¹).conductor)
      ∧ IsUnit ((q / (χ⁻¹).conductor : ℕ) : ZMod (χ⁻¹).conductor)
  · have h2 : Nat.Coprime (χ⁻¹).conductor (q / (χ⁻¹).conductor) ∧ Squarefree (q / (χ⁻¹).conductor) :=
      ⟨((ZMod.isUnit_iff_coprime (q / (χ⁻¹).conductor) (χ⁻¹).conductor).mp h.2).symm, h.1⟩
    rw [if_pos h, if_pos h2]
  · have h2 : ¬ (Nat.Coprime (χ⁻¹).conductor (q / (χ⁻¹).conductor)
        ∧ Squarefree (q / (χ⁻¹).conductor)) := by
      intro hc
      exact h ⟨hc.2, (ZMod.isUnit_iff_coprime (q / (χ⁻¹).conductor) (χ⁻¹).conductor).mpr hc.1.symm⟩
    rw [if_neg h, if_neg h2]

end Commons.NumberTheory.DirichletCharacter