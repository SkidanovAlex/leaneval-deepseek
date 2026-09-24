import Mathlib
import Submission.Commons.Analysis.ExponentialSums.arithmetic_large_sieve
import Submission.Commons.NumberTheory.DirichletCharacter.gaussSum_norm_sq_of_isPrimitive
import Submission.Commons.NumberTheory.DirichletCharacter.sum_char_mul_conj

namespace Commons.NumberTheory.BombieriVinogradov

open Filter
open scoped BigOperators Classical ComplexConjugate
open Classical

noncomputable section

lemma ch_div_eq_stdAddChar (q : ℕ) [NeZero q] (j : ℕ) :
    Commons.Analysis.ExponentialSums.ch ((j : ℝ) / (q : ℝ)) = ZMod.stdAddChar (j : ZMod q) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_natCast]
  simp only [Commons.Analysis.ExponentialSums.ch]
  congr 1
  push_cast
  ring

/-- Pointwise inverse Fourier expansion of a primitive character modulo `q`. -/
lemma chi_expansion {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (n : ZMod q) :
    χ n = (q : ℂ)⁻¹ * gaussSum χ (ZMod.stdAddChar (N := q)) *
      ∑ a : ZMod q, χ⁻¹ a * ZMod.stdAddChar (-(n * a)) := by
  set τ : ℂ := gaussSum χ (ZMod.stdAddChar (N := q)) with hτ
  have hdd : ∀ j : ZMod q, ZMod.dft (ZMod.dft (χ : ZMod q → ℂ)) j = (q : ℂ) * χ (-j) := by
    intro j
    have h := congr_fun (ZMod.dft_dft (Φ := (χ : ZMod q → ℂ))) j
    simpa using h
  have hkey : ∀ j : ZMod q, (q : ℂ) * χ (-j) =
      ∑ k : ZMod q, ZMod.stdAddChar (-(k * j)) * (χ⁻¹ (-k) * τ) := by
    intro j
    rw [← hdd j, ZMod.dft_apply]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [DirichletCharacter.IsPrimitive.fourierTransform_eq_inv_mul_gaussSum hχ k, hτ]
    simp [smul_eq_mul]
  have h1 := hkey (-n)
  rw [neg_neg] at h1
  -- h1 : q * χ n = ∑ k, e (-(k * -n)) * (χ⁻¹ (-k) * τ)
  have h2 : (∑ k : ZMod q, ZMod.stdAddChar (-(k * (-n))) * (χ⁻¹ (-k) * τ)) =
      τ * ∑ a : ZMod q, χ⁻¹ a * ZMod.stdAddChar (-(n * a)) := by
    have key : (∑ k : ZMod q, ZMod.stdAddChar (k * n) * (χ⁻¹ (-k) * τ)) =
        ∑ a : ZMod q, ZMod.stdAddChar ((-a) * n) * (χ⁻¹ a * τ) :=
      Fintype.sum_equiv (Equiv.neg (ZMod q))
        (fun k : ZMod q => ZMod.stdAddChar (k * n) * (χ⁻¹ (-k) * τ))
        (fun a : ZMod q => ZMod.stdAddChar ((-a) * n) * (χ⁻¹ a * τ))
        (fun k => by simp [neg_neg])
    have step1 : (∑ k : ZMod q, ZMod.stdAddChar (-(k * (-n))) * (χ⁻¹ (-k) * τ)) =
        ∑ k : ZMod q, ZMod.stdAddChar (k * n) * (χ⁻¹ (-k) * τ) := by
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [show -(k * (-n)) = k * n by ring]
    have step3 : (∑ a : ZMod q, ZMod.stdAddChar ((-a) * n) * (χ⁻¹ a * τ)) =
        τ * ∑ a : ZMod q, χ⁻¹ a * ZMod.stdAddChar (-(n * a)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro a _
      rw [show (-a) * n = -(n * a) by ring]
      ring
    rw [step1, key, step3]
  rw [h2] at h1
  have hq : (q : ℂ) ≠ 0 := by
    have := NeZero.ne q
    exact_mod_cast this
  rw [mul_assoc, ← h1, ← mul_assoc, inv_mul_cancel₀ hq, one_mul]

/-- The sum over the units of `ZMod q`, as a sum over `r ∈ [1,q]` coprime to `q`. -/
lemma sum_units_eq_sum_coprime (q : ℕ) [NeZero q] (F : ZMod q → ℂ) :
    (∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a), F a)
      = ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q), F (r : ZMod q) := by
  classical
  by_cases hq1 : q = 1
  · subst hq1
    have hIsUnit : ∀ a : ZMod 1, IsUnit a := fun a =>
      ⟨⟨a, a, Subsingleton.elim _ _, Subsingleton.elim _ _⟩, rfl⟩
    have hA : (Finset.univ : Finset (ZMod 1)).filter (fun a => IsUnit a) = {0} := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun _ => Subsingleton.elim a 0, fun _ => hIsUnit a⟩
    have hB : (Finset.Icc 1 1).filter (fun r => Nat.Coprime r 1) = {1} := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨h1, h2⟩, -⟩; omega
      · rintro rfl; exact ⟨⟨le_rfl, le_rfl⟩, Nat.coprime_one_right 1⟩
    rw [hA, hB, Finset.sum_singleton, Finset.sum_singleton]
    exact congrArg F (Subsingleton.elim _ _)
  refine Finset.sum_bij (fun (a : ZMod q) (_ : a ∈ (Finset.univ : Finset (ZMod q)).filter
      (fun a => IsUnit a)) => a.val) ?_ ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_filter] at ha
    obtain ⟨-, hunit⟩ := ha
    obtain ⟨u, rfl⟩ := hunit
    rw [Finset.mem_filter, Finset.mem_Icc]
    have hne : ((u : ZMod q)) ≠ 0 := by
      intro h0
      have h1 : ((1 : ℕ) : ZMod q) = 0 := by
        calc ((1 : ℕ) : ZMod q) = ((u * u⁻¹ : (ZMod q)ˣ) : ZMod q) := by simp
          _ = (u : ZMod q) * ((u⁻¹ : (ZMod q)ˣ) : ZMod q) := by simp
          _ = 0 := by rw [h0, zero_mul]
      have hdvd : q ∣ 1 := (ZMod.natCast_eq_zero_iff 1 q).1 h1
      have hq2 : 2 ≤ q := by have := NeZero.pos q; omega
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact Nat.pos_of_ne_zero (fun h0 => hne ((ZMod.val_eq_zero (u : ZMod q)).1 h0))
    · exact le_of_lt (ZMod.val_lt (u : ZMod q))
    · exact ZMod.val_coe_unit_coprime u
  · intro a ha b hb hab
    rw [← ZMod.natCast_zmod_val a, ← ZMod.natCast_zmod_val b, hab]
  · intro r hr
    rw [Finset.mem_filter, Finset.mem_Icc] at hr
    obtain ⟨⟨hr1, hrq⟩, hcop⟩ := hr
    have hrlt : r < q := by
      rcases lt_or_eq_of_le hrq with h | h
      · exact h
      · exfalso
        have hq1' : q = 1 := by
          have hg := hcop
          rw [Nat.Coprime, h, Nat.gcd_self] at hg
          exact hg
        exact hq1 hq1'
    refine ⟨(r : ZMod q), ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (ZMod.isUnit_iff_coprime r q).2 hcop⟩
    · exact ZMod.val_cast_of_lt hrlt
  · intro a ha
    exact congrArg F (ZMod.natCast_zmod_val a).symm

/-- Sums against a weight vanishing off the units may be restricted to the units. -/
lemma sum_eq_sum_units_of_eq_zero {q : ℕ} [NeZero q] (f : ZMod q → ℂ)
    (hf : ∀ a, ¬ IsUnit a → f a = 0) :
    (∑ a : ZMod q, f a) = ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a), f a := by
  classical
  have h := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (ZMod q)) (fun a => IsUnit a) f
  have hz : (∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => ¬ IsUnit a), f a) = 0 :=
    Finset.sum_eq_zero (fun a ha => hf a (Finset.mem_filter.mp ha).2)
  rw [hz, add_zero] at h
  rw [h]

/-- Conjugation inverts a character value: `conj ((χ⁻¹) x) = χ x`. -/
lemma conj_inv_char_apply {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ZMod q) :
    conj ((χ⁻¹) x : ℂ) = (χ x : ℂ) := by
  have h : conj (χ x) = ((χ x : ℂ)⁻¹) :=
    Commons.NumberTheory.DirichletCharacter.conj_char_apply_eq_inv χ x
  rw [MulChar.inv_apply_eq_inv, Ring.inverse_eq_inv, map_inv₀]
  rw [h, inv_inv]

/-- Inverse Fourier expansion with `e(+n·a)` and a `χ⁻¹(-1)` factor. -/
lemma chi_expansion_pos {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (n : ZMod q) :
    χ n = (q : ℂ)⁻¹ * gaussSum χ (ZMod.stdAddChar (N := q)) * χ⁻¹ (-1) *
      ∑ a : ZMod q, χ⁻¹ a * ZMod.stdAddChar (n * a) := by
  have h := chi_expansion χ hχ n
  have hmul : ∀ a : ZMod q, χ⁻¹ (-a) = χ⁻¹ (-1) * χ⁻¹ a := by
    intro a
    rw [← map_mul]
    congr 1
    ring
  have hneg2 : (∑ a : ZMod q, χ⁻¹ a * ZMod.stdAddChar (-(n * a))) =
      ∑ a : ZMod q, χ⁻¹ (-a) * ZMod.stdAddChar (n * a) :=
    Fintype.sum_equiv (Equiv.neg (ZMod q))
      (fun a : ZMod q => χ⁻¹ a * ZMod.stdAddChar (-(n * a)))
      (fun a : ZMod q => χ⁻¹ (-a) * ZMod.stdAddChar (n * a))
      (fun a => by
        show χ⁻¹ a * ZMod.stdAddChar (-(n * a)) =
          χ⁻¹ (-(-a)) * ZMod.stdAddChar (n * (-a))
        rw [neg_neg, show n * (-a) = -(n * a) by ring])
  have hneg3 : (∑ a : ZMod q, χ⁻¹ (-a) * ZMod.stdAddChar (n * a)) =
      χ⁻¹ (-1) * ∑ a : ZMod q, χ⁻¹ a * ZMod.stdAddChar (n * a) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro a _
    rw [hmul a]
    ring
  rw [h, hneg2, hneg3]
  ring


/-- **Per-character bound.**  For a primitive character `χ` modulo `q`, the character sum
of an arbitrary sequence is bounded by `q^{-1/2}` times the twisted Farey sum with `χ⁻¹`. -/
lemma norm_charSum_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (N : ℕ) (a : ℕ → ℂ) :
    ‖∑ n ∈ Finset.Icc 1 N, a n * χ (n : ZMod q)‖ ^ 2 ≤ (q : ℝ)⁻¹ *
      ‖∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
        χ⁻¹ (r : ZMod q) * (∑ n ∈ Finset.Icc 1 N, a n *
          Commons.Analysis.ExponentialSums.ch ((n : ℝ) * (r : ℝ) / (q : ℝ)))‖ ^ 2 := by
  classical
  set τ : ℂ := gaussSum χ (ZMod.stdAddChar (N := q)) with hτ
  set c : ℂ := (q : ℂ)⁻¹ * τ * χ⁻¹ (-1) with hc
  set U : ZMod q → ℂ := fun x => ∑ n ∈ Finset.Icc 1 N,
    a n * ZMod.stdAddChar ((n : ZMod q) * x) with hU
  have hA : (∑ n ∈ Finset.Icc 1 N, a n * χ (n : ZMod q)) =
      ∑ n ∈ Finset.Icc 1 N, ∑ x : ZMod q,
        (c * χ⁻¹ x) * (a n * ZMod.stdAddChar ((n : ZMod q) * x)) := by
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [chi_expansion_pos χ hχ (n : ZMod q), hc]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    ring
  have hB : (∑ n ∈ Finset.Icc 1 N, ∑ x : ZMod q,
        (c * χ⁻¹ x) * (a n * ZMod.stdAddChar ((n : ZMod q) * x))) =
      ∑ x : ZMod q, ∑ n ∈ Finset.Icc 1 N,
        (c * χ⁻¹ x) * (a n * ZMod.stdAddChar ((n : ZMod q) * x)) :=
    Finset.sum_comm
  have hC : (∑ x : ZMod q, ∑ n ∈ Finset.Icc 1 N,
        (c * χ⁻¹ x) * (a n * ZMod.stdAddChar ((n : ZMod q) * x))) =
      ∑ x : ZMod q, (c * χ⁻¹ x) * U x := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [hU]
    exact (Finset.mul_sum (s := Finset.Icc 1 N)
      (f := fun n => a n * ZMod.stdAddChar ((n : ZMod q) * x)) (a := c * χ⁻¹ x)).symm
  have hD : (∑ x : ZMod q, (c * χ⁻¹ x) * U x) = c * ∑ x : ZMod q, χ⁻¹ x * U x := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    ring
  have hS : (∑ n ∈ Finset.Icc 1 N, a n * χ (n : ZMod q)) =
      c * ∑ x : ZMod q, χ⁻¹ x * U x := by
    rw [hA, hB, hC, hD]
  have hunit : (∑ x : ZMod q, χ⁻¹ x * U x) =
      ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
        χ⁻¹ (r : ZMod q) * U (r : ZMod q) := by
    rw [sum_eq_sum_units_of_eq_zero (fun x => χ⁻¹ x * U x) (fun x hx => by
      rw [MulCharClass.map_nonunit (χ⁻¹) hx, zero_mul])]
    exact sum_units_eq_sum_coprime q (fun x => χ⁻¹ x * U x)
  have hbridge : (∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
        χ⁻¹ (r : ZMod q) * U (r : ZMod q))
      = ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
          χ⁻¹ (r : ZMod q) * (∑ n ∈ Finset.Icc 1 N, a n *
            Commons.Analysis.ExponentialSums.ch ((n : ℝ) * (r : ℝ) / (q : ℝ))) := by
    refine Finset.sum_congr rfl (fun r _ => ?_)
    simp only [hU]
    congr 1
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [show (n : ZMod q) * (r : ZMod q) = ((n * r : ℕ) : ZMod q) by push_cast; ring]
    rw [show (↑n : ℝ) * ↑r / ↑q = (↑(n * r) : ℝ) / ↑q by push_cast; ring]
    rw [ch_div_eq_stdAddChar]
  have hnormc : ‖c‖ ^ 2 = (q : ℝ)⁻¹ := by
    have h1 : ‖χ⁻¹ (-1 : ZMod q)‖ ^ 2 = 1 := by
      have hu : IsUnit (-1 : ZMod q) := ⟨⟨-1, -1, by ring, by ring⟩, rfl⟩
      obtain ⟨u, hu'⟩ := hu
      have h2 : ‖χ⁻¹ (-1 : ZMod q)‖ = 1 := by
        rw [← hu']; exact DirichletCharacter.unit_norm_eq_one (χ⁻¹) u
      rw [h2]; norm_num
    have hτ2 : ‖τ‖ ^ 2 = (q : ℝ) := by
      rw [hτ]
      exact Commons.NumberTheory.DirichletCharacter.gaussSum_norm_sq_of_isPrimitive χ hχ
    have hq2 : ‖((q : ℂ))⁻¹‖ ^ 2 = ((q : ℝ)⁻¹) ^ 2 := by
      rw [norm_inv, Complex.norm_natCast]
    rw [hc, norm_mul, norm_mul, mul_pow, mul_pow, hq2, hτ2, h1, mul_one]
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
    rw [sq, mul_assoc, inv_mul_cancel₀ hq0, mul_one]
  rw [hS, hunit, hbridge]
  exact le_of_eq (by rw [norm_mul, mul_pow, hnormc])


/-- For a unit `s`, `(χ⁻¹) s = conj (χ s)`. -/
lemma char_inv_apply_eq_conj {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ZMod q) :
    (χ⁻¹) s = conj (χ s) := by
  rw [MulChar.inv_apply_eq_inv, Ring.inverse_eq_inv]
  exact (Commons.NumberTheory.DirichletCharacter.conj_char_apply_eq_inv χ s).symm

/-- The cast `ℕ → ZMod q` is injective on `[1,q]`. -/
lemma zmod_natCast_inj_of_le {q : ℕ} [NeZero q] {r s : ℕ} (hr : 1 ≤ r) (hrq : r ≤ q)
    (hs : 1 ≤ s) (hsq : s ≤ q) : ((r : ZMod q) = (s : ZMod q)) ↔ r = s := by
  constructor
  · intro h
    have hmod : r % q = s % q := by
      have hh := congrArg ZMod.val h
      simpa only [ZMod.val_natCast] using hh
    rcases lt_or_eq_of_le hrq with hrlt | hrq'
    · rw [Nat.mod_eq_of_lt hrlt] at hmod
      rcases lt_or_eq_of_le hsq with hslt | hsq'
      · rwa [Nat.mod_eq_of_lt hslt] at hmod
      · subst hsq'
        rw [Nat.mod_self] at hmod
        omega
    · subst hrq'
      rw [Nat.mod_self] at hmod
      rcases lt_or_eq_of_le hsq with hslt | hsq'
      · rw [Nat.mod_eq_of_lt hslt] at hmod
        omega
      · subst hsq'
        rfl
  · intro h; rw [h]

/-- **Orthogonality / Parseval for the family of Dirichlet characters mod `q`.** -/
lemma sum_char_normSq (q : ℕ) [NeZero q] (N : ℕ) (a : ℕ → ℂ) :
    (∑ χ : DirichletCharacter ℂ q,
        ‖∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
            (χ⁻¹) (r : ZMod q) * (∑ n ∈ Finset.Icc 1 N, a n *
              Commons.Analysis.ExponentialSums.ch ((n : ℝ) * (r : ℝ) / (q : ℝ)))‖ ^ 2)
      = (q.totient : ℝ) * ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
          ‖∑ n ∈ Finset.Icc 1 N, a n *
            Commons.Analysis.ExponentialSums.ch ((n : ℝ) * (r : ℝ) / (q : ℝ))‖ ^ 2 := by
  classical
  set R := (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q) with hR
  set W : ℕ → ℂ := fun r => ∑ n ∈ Finset.Icc 1 N, a n *
    Commons.Analysis.ExponentialSums.ch ((n : ℝ) * (r : ℝ) / (q : ℝ)) with hW
  have hRunit : ∀ r ∈ R, IsUnit (r : ZMod q) := by
    intro r hr
    rw [hR, Finset.mem_filter] at hr
    exact (ZMod.isUnit_iff_coprime r q).2 hr.2
  apply Complex.ofReal_inj.mp
  have hterm : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = conj z * z := fun z => by
    rw [← Complex.normSq_eq_norm_sq]; exact Complex.normSq_eq_conj_mul_self
  rw [Complex.ofReal_sum]
  rw [Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_sum]
  simp only [hterm]
  -- goal: ∑ χ, conj (∑ r ∈ R, χ⁻¹ r * W r) * (∑ r ∈ R, χ⁻¹ r * W r) = φ * ∑ r ∈ R, conj (W r) * W r
  have hconj : ∀ χ : DirichletCharacter ℂ q,
      conj (∑ r ∈ R, (χ⁻¹) (r : ZMod q) * W r) =
        ∑ r ∈ R, χ (r : ZMod q) * conj (W r) := by
    intro χ
    rw [map_sum]
    refine Finset.sum_congr rfl (fun r hr => ?_)
    rw [map_mul, conj_inv_char_apply]
  have key : (∑ χ : DirichletCharacter ℂ q,
      conj (∑ r ∈ R, (χ⁻¹) (r : ZMod q) * W r) * (∑ r ∈ R, (χ⁻¹) (r : ZMod q) * W r))
      = (q.totient : ℂ) * ∑ r ∈ R, conj (W r) * W r := by
    calc (∑ χ : DirichletCharacter ℂ q,
          conj (∑ r ∈ R, (χ⁻¹) (r : ZMod q) * W r) * (∑ r ∈ R, (χ⁻¹) (r : ZMod q) * W r))
        = ∑ χ : DirichletCharacter ℂ q,
            (∑ r ∈ R, χ (r : ZMod q) * conj (W r)) *
              (∑ s ∈ R, (χ⁻¹) (s : ZMod q) * W s) := by
          refine Finset.sum_congr rfl (fun χ _ => ?_)
          rw [hconj χ]
      _ = ∑ χ : DirichletCharacter ℂ q, ∑ r ∈ R, ∑ s ∈ R,
            (χ (r : ZMod q) * conj (W r)) * ((χ⁻¹) (s : ZMod q) * W s) := by
          refine Finset.sum_congr rfl (fun χ _ => ?_)
          rw [Finset.sum_mul_sum]
      _ = ∑ r ∈ R, ∑ s ∈ R, ∑ χ : DirichletCharacter ℂ q,
            (χ (r : ZMod q) * conj (W r)) * ((χ⁻¹) (s : ZMod q) * W s) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun r _ => ?_)
          rw [Finset.sum_comm]
      _ = ∑ r ∈ R, ∑ s ∈ R, (conj (W r) * W s) *
            (∑ χ : DirichletCharacter ℂ q, χ (r : ZMod q) * (χ⁻¹) (s : ZMod q)) := by
          refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun s _ => ?_))
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun χ _ => ?_)
          ring
      _ = ∑ r ∈ R, ∑ s ∈ R, (conj (W r) * W s) *
            (if (r : ZMod q) = (s : ZMod q) then (q.totient : ℂ) else 0) := by
          refine Finset.sum_congr rfl (fun r hr => Finset.sum_congr rfl (fun s hs => ?_))
          congr 1
          have h1 : (∑ χ : DirichletCharacter ℂ q, χ (r : ZMod q) * (χ⁻¹) (s : ZMod q))
              = ∑ χ : DirichletCharacter ℂ q, χ (r : ZMod q) * conj (χ (s : ZMod q)) := by
            refine Finset.sum_congr rfl (fun χ _ => ?_)
            rw [char_inv_apply_eq_conj χ (s : ZMod q)]
          rw [h1]
          exact Commons.NumberTheory.DirichletCharacter.sum_char_mul_conj q (hRunit r hr) (s : ZMod q)
      _ = ∑ r ∈ R, (conj (W r) * W r) * (q.totient : ℂ) := by
          refine Finset.sum_congr rfl (fun r hr => ?_)
          rw [Finset.sum_eq_single r]
          · rw [if_pos rfl]
          · intro s hsR hsne
            rw [if_neg, mul_zero]
            intro hcoe
            rw [hR, Finset.mem_filter, Finset.mem_Icc] at hr hsR
            exact hsne ((zmod_natCast_inj_of_le hsR.1.1 hsR.1.2 hr.1.1 hr.1.2).1 hcoe.symm)
          · intro hnotin
            exact absurd hr hnotin
      _ = (q.totient : ℂ) * ∑ r ∈ R, conj (W r) * W r := by
          rw [← Finset.sum_mul, mul_comm]
  rw [key]


/-- **Large sieve for Dirichlet characters.**  The averaged second moment of the
Dirichlet-polynomial character sums is bounded by `N + Q²`. -/
theorem char_large_sieve (Q N : ℕ) (hQ : 1 ≤ Q) (a : ℕ → ℂ) :
    (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖∑ n ∈ Finset.Icc 1 N, a n * χ (n : ZMod q)‖ ^ 2)
      ≤ (N + Q ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  classical
  refine le_trans (Finset.sum_le_sum ?_)
    (Commons.Analysis.ExponentialSums.arithmetic_large_sieve Q N hQ a)
  intro q hq
  rw [Finset.mem_Icc] at hq
  haveI : NeZero q := ⟨by omega⟩
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hφpos : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q)
  have hprim : (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
        (fun χ => χ.IsPrimitive), ‖∑ n ∈ Finset.Icc 1 N, a n * χ (n : ZMod q)‖ ^ 2)
      ≤ (q : ℝ)⁻¹ * ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
        (fun χ => χ.IsPrimitive),
          ‖∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
            (χ⁻¹) (r : ZMod q) * (∑ n ∈ Finset.Icc 1 N, a n *
              Commons.Analysis.ExponentialSums.ch ((n : ℝ) * (r : ℝ) / (q : ℝ)))‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun χ hχ => ?_)
    rw [Finset.mem_filter] at hχ
    exact norm_charSum_le χ hχ.2 N a
  have hsub : (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
        (fun χ => χ.IsPrimitive),
          ‖∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
            (χ⁻¹) (r : ZMod q) * (∑ n ∈ Finset.Icc 1 N, a n *
              Commons.Analysis.ExponentialSums.ch ((n : ℝ) * (r : ℝ) / (q : ℝ)))‖ ^ 2)
      ≤ ∑ χ : DirichletCharacter ℂ q,
          ‖∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
            (χ⁻¹) (r : ZMod q) * (∑ n ∈ Finset.Icc 1 N, a n *
              Commons.Analysis.ExponentialSums.ch ((n : ℝ) * (r : ℝ) / (q : ℝ)))‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun x _ _ => by positivity)
  have hparseval := sum_char_normSq q N a
  have step1 : ((q : ℝ) / (q.totient : ℝ)) *
        (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖∑ n ∈ Finset.Icc 1 N, a n * χ (n : ZMod q)‖ ^ 2)
      ≤ ((q : ℝ) / (q.totient : ℝ)) * ((q : ℝ)⁻¹ *
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
            (χ⁻¹) (r : ZMod q) * (∑ n ∈ Finset.Icc 1 N, a n *
              Commons.Analysis.ExponentialSums.ch ((n : ℝ) * (r : ℝ) / (q : ℝ)))‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hprim (by positivity)
  have step2 : ((q : ℝ) / (q.totient : ℝ)) * ((q : ℝ)⁻¹ *
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
            (χ⁻¹) (r : ZMod q) * (∑ n ∈ Finset.Icc 1 N, a n *
              Commons.Analysis.ExponentialSums.ch ((n : ℝ) * (r : ℝ) / (q : ℝ)))‖ ^ 2)
      ≤ ((q : ℝ) / (q.totient : ℝ)) * ((q : ℝ)⁻¹ *
        ((q.totient : ℝ) * ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
          ‖∑ n ∈ Finset.Icc 1 N, a n *
            Commons.Analysis.ExponentialSums.ch ((n : ℝ) * (r : ℝ) / (q : ℝ))‖ ^ 2)) := by
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) (by positivity)
    rw [← hparseval]
    exact hsub
  have step3 : ((q : ℝ) / (q.totient : ℝ)) * ((q : ℝ)⁻¹ *
        ((q.totient : ℝ) * ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
          ‖∑ n ∈ Finset.Icc 1 N, a n *
            Commons.Analysis.ExponentialSums.ch ((n : ℝ) * (r : ℝ) / (q : ℝ))‖ ^ 2))
      = ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
          ‖∑ n ∈ Finset.Icc 1 N, a n *
            Commons.Analysis.ExponentialSums.ch ((n : ℝ) * (r : ℝ) / (q : ℝ))‖ ^ 2 := by
    have hφne : (q.totient : ℝ) ≠ 0 := ne_of_gt hφpos
    have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqpos
    rw [div_eq_mul_inv]
    field_simp
  exact le_trans step1 (le_trans step2 (le_of_eq step3))



end

end Commons.NumberTheory.BombieriVinogradov
