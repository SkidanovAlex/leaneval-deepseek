import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.interfaces
import Submission.Work.BMF.polyrel_basic
import Submission.Work.BMF.bezout_intValued

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliary machinery for `Work.BMF.quaddata_stage`

* invariance of `corr` under adding an integer-valued polynomial;
* the Chinese remainder theorem for integer-valued polynomials (`crt_intValued`), deduced from
  `bezout_intValued`;
* separation/uniqueness lemmas for `incPairs`.
-/

open Polynomial Finset Real Complex
open BoundedMultiplicativeFunctions

namespace Work.BMF

section Corr

private lemma eC_add (s t : ℝ) : eC (s + t) = eC s * eC t := by
  rw [eC, eC, eC, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma eC_int_neg (m : ℤ) : eC (-(m : ℝ)) = 1 := by
  rw [eC, Complex.exp_eq_one_iff]
  refine ⟨-m, ?_⟩
  push_cast
  ring

/-- Adding a polynomial that is integral on `ℤ` does not change the correlation. -/
lemma corr_add_integral (f : ℕ → ℂ) {P γ : ℝ[X]} {x L : ℝ} (h : IntegralOn 1 γ) :
    corr f (P + γ) x L = corr f P x L := by
  unfold corr
  refine Finset.sum_congr rfl fun n _ => ?_
  have hz : ∃ m : ℤ, γ.eval (n : ℝ) = (m : ℝ) := by
    obtain ⟨m, hm⟩ := h (n : ℤ)
    exact ⟨m, by simpa using hm⟩
  obtain ⟨m, hm⟩ := hz
  rw [eval_add, hm]
  have hone : eC (-(P.eval (n : ℝ)) + -(m : ℝ)) = eC (-(P.eval (n : ℝ))) := by
    rw [eC_add, eC_int_neg m, mul_one]
  rw [show -(P.eval ↑n + ↑m) = -(P.eval ↑n) + -(↑m) by ring, hone]

end Corr

section IntegralOnAux

lemma IntegralOn.one_of_inv {d : ℕ} (hd : 0 < d) {γ : ℝ[X]} (h : IntegralOn (1 / (d : ℝ)) γ) :
    IntegralOn 1 γ := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hdZ : ((d : ℤ) : ℝ) = (d : ℝ) := by simp
  have := h.int_mul (d : ℤ)
  rw [hdZ] at this
  convert this using 1
  field_simp

lemma IntegralOn.of_dvd {q A : ℕ} (hq : q ∣ A) (hA : A ≠ 0) {γ : ℝ[X]}
    (h : IntegralOn (1 / (A : ℝ)) γ) : IntegralOn (1 / (q : ℝ)) γ := by
  obtain ⟨c, hc⟩ := hq
  have hq0 : q ≠ 0 := fun h0 => hA (by rw [hc, h0, zero_mul])
  have hc0 : c ≠ 0 := fun h0 => hA (by rw [hc, h0, mul_zero])
  have hq0' : (q : ℝ) ≠ 0 := by exact_mod_cast hq0
  have hc0' : (c : ℝ) ≠ 0 := by exact_mod_cast hc0
  intro n
  have key : (1 / (q : ℝ)) * (n : ℝ) = (1 / (A : ℝ)) * ((n : ℝ) * (c : ℝ)) := by
    rw [hc]; push_cast; field_simp
  have hkey : ∃ m : ℤ, γ.eval ((1 / (A : ℝ)) * ((n : ℝ) * (c : ℝ))) = (m : ℝ) := by
    obtain ⟨m, hm⟩ := h (n * c)
    exact ⟨m, by rw [← hm]; congr 1; push_cast; ring⟩
  rw [key]
  exact hkey

end IntegralOnAux

section CRT

lemma prime_coprime_prod {p : ℕ} (hp : p.Prime) {P : Finset ℕ} (hP : ∀ q ∈ P, q.Prime)
    (hpP : p ∉ P) : Nat.Coprime p (∏ q ∈ P, q) := by
  refine Nat.Coprime.prod_right fun q hq => ?_
  rw [hp.coprime_iff_not_dvd]
  intro hdiv
  have hqeq : q = p := ((hP q hq).dvd_iff_eq hp.ne_one).mp hdiv
  exact hpP (hqeq ▸ hq)

/-- Chinese remainder theorem for integer-valued polynomials (MRTTZ Appendix B, Prop. `chinese`(i)). -/
theorem crt_intValued (k : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (γ : ℕ → ℝ[X]) (hdeg : ∀ p ∈ P, γ p ∈ degreeLE ℝ (k : WithBot ℕ))
    (hint : ∀ p ∈ P, IntegralOn 1 (γ p)) :
    ∃ γ₀ : ℝ[X], γ₀ ∈ degreeLE ℝ (k : WithBot ℕ) ∧ IntegralOn 1 γ₀ ∧
      ∀ p ∈ P, IntegralOn (1 / (p : ℝ)) (γ p - γ₀) := by
  classical
  revert hP γ hdeg hint
  refine Finset.induction_on P ?_ ?_
  · intro hP γ _ _
    exact ⟨0, Submodule.zero_mem _, IntegralOn.zero 1, by simp⟩
  · intro p P hp ih hP γ hdeg hint
    obtain ⟨γ₀, hdeg₀, hint₀, hrel₀⟩ := ih (fun q hq => hP q (Finset.mem_insert_of_mem hq)) γ
      (fun q hq => hdeg q (Finset.mem_insert_of_mem hq))
      (fun q hq => hint q (Finset.mem_insert_of_mem hq))
    have hpprime : p.Prime := hP p (Finset.mem_insert_self p P)
    have hPA : ∀ q ∈ P, q.Prime := fun q hq => hP q (Finset.mem_insert_of_mem hq)
    have hApos : 0 < ∏ q ∈ P, q := Finset.prod_pos fun q hq => (hPA q hq).pos
    have hcop : Nat.Coprime p (∏ q ∈ P, q) := prime_coprime_prod hpprime hPA hp
    obtain ⟨γa, γb, hda, hdb, hia, hib, heq⟩ :=
      bezout_intValued k p (∏ q ∈ P, q) hpprime.pos hApos hcop (γ p - γ₀)
        (Submodule.sub_mem _ (hdeg p (Finset.mem_insert_self p P)) hdeg₀)
        ((hint p (Finset.mem_insert_self p P)).sub hint₀)
    refine ⟨γ p - γa, Submodule.sub_mem _ (hdeg p (Finset.mem_insert_self p P)) hda, ?_, ?_⟩
    · have hsplit : γ p - γa = γ₀ + γb := by linear_combination heq
      rw [hsplit]
      exact hint₀.add (hib.one_of_inv hApos)
    · intro q hq
      rcases Finset.mem_insert.mp hq with hqp | hqP
      · rw [hqp]
        have hpp : γ p - (γ p - γa) = γa := by ring
        rw [hpp]; exact hia
      · have hqA : q ∣ ∏ q ∈ P, q := Finset.dvd_prod_of_mem _ hqP
        have h1 := (hrel₀ q hqP).sub (hib.of_dvd hqA (ne_of_gt hApos))
        have hpe : γ p = γ₀ + γa + γb := by linear_combination heq
        convert h1 using 1
        rw [hpe]; ring

end CRT

section Separation

lemma IsFam.eq_of_abs_sub_lt {X L : ℝ} {S : Finset ℝ} (hS : IsFam X L S) {x y : ℝ}
    (hx : x ∈ S) (hy : y ∈ S) (h : |x - y| < 500 * L) : x = y := by
  by_contra hne
  exact absurd (hS.2 x hx y hy hne) (not_le.mpr h)

/-- For a fixed target `x'` and a fixed prime, the source endpoint of a pair in `incPairs` is
unique. -/
lemma incPairs_fst_unique {k : ℕ} {X L C a b R L' : ℝ} {S : Finset ℝ} {pol : ℝ → ℝ[X]}
    {pol' pol'' : ℝ[X]} {x' : ℝ} (hS : IsFam X L S) (hR0 : 0 ≤ R) (hR : 2 * b * R < 500 * L)
    {q q' : ℝ × ℕ}
    (hq : q ∈ incPairs k C S a b L R L' pol pol' x')
    (hq' : q' ∈ incPairs k C S a b L R L' pol pol'' x')
    (hqq : q.2 = q'.2) (hb : (q.2 : ℝ) ≤ b) : q.1 = q'.1 := by
  classical
  obtain ⟨hmem, hcond⟩ := Finset.mem_filter.mp hq
  obtain ⟨hmem', hcond'⟩ := Finset.mem_filter.mp hq'
  obtain ⟨hsrc, hprime⟩ := Finset.mem_product.mp hmem
  obtain ⟨hsrc', hprime'⟩ := Finset.mem_product.mp hmem'
  have hp2 : q.2.Prime := (Finset.mem_filter.mp hprime).2
  have hq2pos : (0 : ℝ) < (q.2 : ℝ) := by
    have h2 : (2 : ℝ) ≤ (q.2 : ℝ) := by exact_mod_cast hp2.two_le
    linarith
  have h1 : |q.1 / (q.2 : ℝ) - x'| ≤ R := hcond.1
  have h2 : |q'.1 / (q'.2 : ℝ) - x'| ≤ R := hcond'.1
  have hqq' : q'.2 = q.2 := hqq.symm
  have h2' : |q'.1 / (q.2 : ℝ) - x'| ≤ R := by rwa [hqq'] at h2
  have hkey : q.1 - q'.1
      = (q.2 : ℝ) * (q.1 / (q.2 : ℝ) - x') - (q.2 : ℝ) * (q'.1 / (q.2 : ℝ) - x') := by
    field_simp
    ring
  have habs : |q.1 - q'.1| ≤ 2 * b * R := by
    rw [hkey]
    calc |(q.2 : ℝ) * (q.1 / (q.2 : ℝ) - x') - (q.2 : ℝ) * (q'.1 / (q.2 : ℝ) - x')|
        = (q.2 : ℝ) * |(q.1 / (q.2 : ℝ) - x') - (q'.1 / (q.2 : ℝ) - x')| := by
          rw [show (q.2 : ℝ) * (q.1 / (q.2 : ℝ) - x') - (q.2 : ℝ) * (q'.1 / (q.2 : ℝ) - x')
              = (q.2 : ℝ) * ((q.1 / (q.2 : ℝ) - x') - (q'.1 / (q.2 : ℝ) - x')) by ring,
            abs_mul, abs_of_pos hq2pos]
      _ ≤ (q.2 : ℝ) * (R + R) := by
          have h3 : |(q.1 / (q.2 : ℝ) - x') - (q'.1 / (q.2 : ℝ) - x')| ≤ R + R := by
            have h4 := abs_add_le (q.1 / (q.2 : ℝ) - x') (-(q'.1 / (q.2 : ℝ) - x'))
            rw [abs_neg] at h4
            have h5 : (q.1 / (q.2 : ℝ) - x') + -(q'.1 / (q.2 : ℝ) - x')
                = (q.1 / (q.2 : ℝ) - x') - (q'.1 / (q.2 : ℝ) - x') := by ring
            rw [h5] at h4
            linarith
          exact mul_le_mul_of_nonneg_left h3 hq2pos.le
      _ ≤ 2 * b * R := by nlinarith [hb, hq2pos.le, hR0]
  exact hS.eq_of_abs_sub_lt hsrc hsrc' (lt_of_le_of_lt habs hR)


/-- For a fixed source pair `(x,q.2)` and a fixed prime, the target endpoint `x'` of `incPairs`
is unique (uses separation of the *target* family). -/
lemma incPairs_target_unique {k : ℕ} {X' L' C a b R L : ℝ} {S' S : Finset ℝ} {pol : ℝ → ℝ[X]}
    {pol' pol'' : ℝ[X]} {x₁ x₂ : ℝ} (hS' : IsFam X' L' S') (hx₁ : x₁ ∈ S') (hx₂ : x₂ ∈ S')
    (hR0 : 0 ≤ R) (hR : 2 * R < 500 * L')
    {q : ℝ × ℕ} (h1 : q ∈ incPairs k C S a b L R L' pol pol' x₁)
    (h2 : q ∈ incPairs k C S a b L R L' pol pol'' x₂) : x₁ = x₂ := by
  classical
  have hcond1 := (Finset.mem_filter.mp h1).2
  have hcond2 := (Finset.mem_filter.mp h2).2
  have hb1 : |q.1 / (q.2 : ℝ) - x₁| ≤ R := hcond1.1
  have hb2 : |q.1 / (q.2 : ℝ) - x₂| ≤ R := hcond2.1
  refine hS'.eq_of_abs_sub_lt hx₁ hx₂ ?_
  calc |x₁ - x₂| ≤ |x₁ - q.1 / (q.2 : ℝ)| + |q.1 / (q.2 : ℝ) - x₂| := by
        rw [show x₁ - x₂ = (x₁ - q.1 / (q.2 : ℝ)) + (q.1 / (q.2 : ℝ) - x₂) by ring]
        exact abs_add_le _ _
    _ ≤ R + R := by rw [abs_sub_comm]; linarith
    _ < 500 * L' := by linarith


/-- Source uniqueness for two memberships with equal primes (convenient form). -/
lemma incPairs_fst_unique₂ {k : ℕ} {X L C a b R L' : ℝ} {S : Finset ℝ} {pol : ℝ → ℝ[X]}
    {pol' pol'' : ℝ[X]} {x' : ℝ} (hS : IsFam X L S) (hR0 : 0 ≤ R) (hR : 2 * b * R < 500 * L)
    {u v : ℝ} {p₁ p₂ : ℕ} (hp : p₁ = p₂)
    (h1 : (u, p₁) ∈ incPairs k C S a b L R L' pol pol' x')
    (h2 : (v, p₂) ∈ incPairs k C S a b L R L' pol pol'' x') (hb : (p₁ : ℝ) ≤ b) : u = v :=
  incPairs_fst_unique (q := (u, p₁)) (q' := (v, p₁)) hS hR0 hR h1 (by rwa [← hp] at h2) rfl hb

/-- Target uniqueness for two memberships of the same pair (convenient form). -/
lemma incPairs_target_unique₂ {k : ℕ} {X' L' C a b R L : ℝ} {S' S : Finset ℝ} {pol : ℝ → ℝ[X]}
    {pol' pol'' : ℝ[X]} {x₁ x₂ : ℝ} {u : ℝ} {p : ℕ}
    (hS' : IsFam X' L' S') (hx₁ : x₁ ∈ S') (hx₂ : x₂ ∈ S') (hR0 : 0 ≤ R)
    (hR : 2 * R < 500 * L')
    (h1 : (u, p) ∈ incPairs k C S a b L R L' pol pol' x₁)
    (h2 : (u, p) ∈ incPairs k C S a b L R L' pol pol'' x₂) : x₁ = x₂ :=
  incPairs_target_unique (q := (u, p)) hS' hx₁ hx₂ hR0 hR h1 h2


section Chain

/-- The two-step chaining of `~`-relations producing the edge relation of `QuadData`:
from the two `~_1` relations (first scaling, level 1) and the two `~_{1/p}` relations
(second scaling, level 2) one obtains the `~_{1/p}`-relation between the two level-2 phases
with the cross dilation `(1/p'₂)_*` and `(1/p'₁)_*`. -/
theorem polyrel_chain {k : ℕ} {Cᵢ H₁ L₁ L₂ : ℝ} {x X'₁ X'₂ Z₁ Z₂ : ℝ} {p'₁ p'₂ p : ℕ}
    {P : ℝ[X]} {P₁ P₂ : ℝ[X]} {g : ℝ → ℝ[X]} {C : ℝ}
    (hCᵢ : 0 < Cᵢ) (hp₁ : 0 < (p'₁ : ℝ)) (hp₂ : 0 < (p'₂ : ℝ)) (hpp : 0 < (p : ℝ))
    (hH₁ : 0 < H₁) (hL₁ : 0 < L₁) (hL₂ : 0 < L₂)
    (h1 : PolyRel k Cᵢ 1 (x / (p'₁ : ℝ)) (H₁ / (p'₁ : ℝ)) (dil (p'₁ : ℝ) P) X'₁ L₁ P₁)
    (h2 : PolyRel k Cᵢ 1 (x / (p'₂ : ℝ)) (H₁ / (p'₂ : ℝ)) (dil (p'₂ : ℝ) P) X'₂ L₁ P₂)
    (h3 : PolyRel k Cᵢ (1 / (p : ℝ)) (X'₁ / (p : ℝ)) (L₁ / (p : ℝ)) (dil (p : ℝ) P₁) Z₁ L₂ (g Z₁))
    (h4 : PolyRel k Cᵢ (1 / (p : ℝ)) (X'₂ / (p : ℝ)) (L₁ / (p : ℝ)) (dil (p : ℝ) P₂) Z₂ L₂ (g Z₂))
    (hC : transConst k (symmConst k (transConst k Cᵢ Cᵢ)) (transConst k Cᵢ Cᵢ) ≤ C) :
    PolyRel k C (1 / (p : ℝ)) (Z₁ / (p'₂ : ℝ)) (L₂ / (p'₂ : ℝ)) (dil (p'₂ : ℝ) (g Z₁))
      (Z₂ / (p'₁ : ℝ)) (L₂ / (p'₁ : ℝ)) (dil (p'₁ : ℝ) (g Z₂)) := by
  have hA : 0 < transConst k Cᵢ Cᵢ := transConst_pos hCᵢ hCᵢ
  have hB : 0 < symmConst k (transConst k Cᵢ Cᵢ) := symmConst_pos hA
  -- the polynomial sides of the two chains agree
  have hpoly : dil (p'₂ : ℝ) (dil (p : ℝ) (dil (p'₁ : ℝ) P))
      = dil (p'₁ : ℝ) (dil (p : ℝ) (dil (p'₂ : ℝ) P)) := by
    rw [dil_mul, dil_mul, dil_mul, dil_mul]
    congr 1
    ring
  -- step 1: chain the two relations at level 1 and level 2
  have s1 : PolyRel k (transConst k Cᵢ Cᵢ) (1 / (p : ℝ))
      (x / ((p'₁ : ℝ) * (p : ℝ))) (H₁ / ((p'₁ : ℝ) * (p : ℝ)))
      (dil (p : ℝ) (dil (p'₁ : ℝ) P)) Z₁ L₂ (g Z₁) := by
    have hsp := PolyRel.trans (h1.dilate hpp) h3 hCᵢ hCᵢ (by positivity) (by positivity)
      (by positivity)
    have hx : x / (p'₁ : ℝ) / (p : ℝ) = x / ((p'₁ : ℝ) * (p : ℝ)) := by ring
    have hL : H₁ / (p'₁ : ℝ) / (p : ℝ) = H₁ / ((p'₁ : ℝ) * (p : ℝ)) := by ring
    rw [hx, hL] at hsp
    exact hsp
  have s2 : PolyRel k (transConst k Cᵢ Cᵢ) (1 / (p : ℝ))
      (x / ((p'₂ : ℝ) * (p : ℝ))) (H₁ / ((p'₂ : ℝ) * (p : ℝ)))
      (dil (p : ℝ) (dil (p'₂ : ℝ) P)) Z₂ L₂ (g Z₂) := by
    have hsp := PolyRel.trans (h2.dilate hpp) h4 hCᵢ hCᵢ (by positivity) (by positivity)
      (by positivity)
    have hx : x / (p'₂ : ℝ) / (p : ℝ) = x / ((p'₂ : ℝ) * (p : ℝ)) := by ring
    have hL : H₁ / (p'₂ : ℝ) / (p : ℝ) = H₁ / ((p'₂ : ℝ) * (p : ℝ)) := by ring
    rw [hx, hL] at hsp
    exact hsp
  -- step 2: dilate by the other prime and sparsify back to `1/p`
  have d1 : PolyRel k (transConst k Cᵢ Cᵢ) (1 / (p : ℝ) / (p'₂ : ℝ))
      (x / ((p'₁ : ℝ) * (p : ℝ)) / (p'₂ : ℝ)) (H₁ / ((p'₁ : ℝ) * (p : ℝ)) / (p'₂ : ℝ))
      (dil (p'₂ : ℝ) (dil (p : ℝ) (dil (p'₁ : ℝ) P))) (Z₁ / (p'₂ : ℝ)) (L₂ / (p'₂ : ℝ))
      (dil (p'₂ : ℝ) (g Z₁)) := s1.dilate hp₂
  have d2 : PolyRel k (transConst k Cᵢ Cᵢ) (1 / (p : ℝ) / (p'₁ : ℝ))
      (x / ((p'₂ : ℝ) * (p : ℝ)) / (p'₁ : ℝ)) (H₁ / ((p'₂ : ℝ) * (p : ℝ)) / (p'₁ : ℝ))
      (dil (p'₁ : ℝ) (dil (p : ℝ) (dil (p'₂ : ℝ) P))) (Z₂ / (p'₁ : ℝ)) (L₂ / (p'₁ : ℝ))
      (dil (p'₁ : ℝ) (g Z₂)) := s2.dilate hp₁
  have sp1 : PolyRel k (transConst k Cᵢ Cᵢ) (1 / (p : ℝ))
      (x / (((p'₁ : ℝ) * (p : ℝ)) * (p'₂ : ℝ))) (H₁ / (((p'₁ : ℝ) * (p : ℝ)) * (p'₂ : ℝ)))
      (dil (p'₂ : ℝ) (dil (p : ℝ) (dil (p'₁ : ℝ) P))) (Z₁ / (p'₂ : ℝ)) (L₂ / (p'₂ : ℝ))
      (dil (p'₂ : ℝ) (g Z₁)) := by
    have hsp := PolyRel.sparsify p'₂ d1
    have hδ : (p'₂ : ℝ) * ((1 / (p : ℝ)) / (p'₂ : ℝ)) = 1 / (p : ℝ) := by field_simp
    have hx : x / ((p'₁ : ℝ) * (p : ℝ)) / (p'₂ : ℝ)
        = x / (((p'₁ : ℝ) * (p : ℝ)) * (p'₂ : ℝ)) := by ring
    have hL : H₁ / ((p'₁ : ℝ) * (p : ℝ)) / (p'₂ : ℝ)
        = H₁ / (((p'₁ : ℝ) * (p : ℝ)) * (p'₂ : ℝ)) := by ring
    rw [hδ, hx, hL] at hsp
    exact hsp
  have sp2 : PolyRel k (transConst k Cᵢ Cᵢ) (1 / (p : ℝ))
      (x / (((p'₁ : ℝ) * (p : ℝ)) * (p'₂ : ℝ))) (H₁ / (((p'₁ : ℝ) * (p : ℝ)) * (p'₂ : ℝ)))
      (dil (p'₂ : ℝ) (dil (p : ℝ) (dil (p'₁ : ℝ) P))) (Z₂ / (p'₁ : ℝ)) (L₂ / (p'₁ : ℝ))
      (dil (p'₁ : ℝ) (g Z₂)) := by
    have hsp := PolyRel.sparsify p'₁ d2
    have hδ : (p'₁ : ℝ) * ((1 / (p : ℝ)) / (p'₁ : ℝ)) = 1 / (p : ℝ) := by field_simp
    have hx : x / ((p'₂ : ℝ) * (p : ℝ)) / (p'₁ : ℝ)
        = x / (((p'₁ : ℝ) * (p : ℝ)) * (p'₂ : ℝ)) := by ring
    have hL : H₁ / ((p'₂ : ℝ) * (p : ℝ)) / (p'₁ : ℝ)
        = H₁ / (((p'₁ : ℝ) * (p : ℝ)) * (p'₂ : ℝ)) := by ring
    rw [hδ, hx, hL, ← hpoly] at hsp
    exact hsp
  -- step 3: symmetry and transitivity
  have fin : PolyRel k (transConst k (symmConst k (transConst k Cᵢ Cᵢ)) (transConst k Cᵢ Cᵢ))
      (1 / (p : ℝ)) (Z₁ / (p'₂ : ℝ)) (L₂ / (p'₂ : ℝ)) (dil (p'₂ : ℝ) (g Z₁))
      (Z₂ / (p'₁ : ℝ)) (L₂ / (p'₁ : ℝ)) (dil (p'₁ : ℝ) (g Z₂)) :=
    PolyRel.trans (sp1.symm hA (by positivity) (by positivity)) sp2 hB hA
      (by positivity) (by positivity) (by positivity)
  exact fin.mono hC (by positivity) (by positivity)

end Chain

end Separation

end Work.BMF
