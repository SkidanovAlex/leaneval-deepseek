import Mathlib

namespace Work.LinnikAreas.Density4

/-- The finset of primes dividing `r`, viewed as elements of `Nat.Primes`. -/
def primesDvd (r : ℕ) : Finset Nat.Primes :=
  r.primeFactors.attach.map ⟨fun x => ⟨x.1, (Nat.mem_primeFactors.mp x.2).1⟩,
    fun _ _ h => Subtype.ext (Subtype.mk.inj h)⟩

lemma mem_primesDvd {r : ℕ} {p : Nat.Primes} :
    p ∈ primesDvd r ↔ (p : ℕ) ∈ r.primeFactors := by
  unfold primesDvd
  rw [Finset.mem_map]
  constructor
  · rintro ⟨x, -, hxp⟩
    rw [← hxp]
    exact x.2
  · intro hp
    exact ⟨⟨p.1, hp⟩, Finset.mem_attach _ _, Subtype.ext rfl⟩

lemma dvd_iff_mem_primeFactors {r : ℕ} (hr : r ≠ 0) {p : Nat.Primes} :
    (p : ℕ) ∣ r ↔ (p : ℕ) ∈ r.primeFactors := by
  rw [Nat.mem_primeFactors]
  exact ⟨fun h => ⟨p.2, h, hr⟩, fun h => h.2.1⟩

/-- The product over the primes dividing `r` (as `Nat.Primes`) of the Euler factors agrees with
the product over `r.primeFactors`. -/
lemma prod_primesDvd (r : ℕ) :
    ∏ x ∈ primesDvd r, (1 - 1 / ((x : ℕ) : ℝ) ^ 2)
      = ∏ p ∈ r.primeFactors, (1 - 1 / (p : ℝ) ^ 2) := by
  classical
  refine Finset.prod_bij (fun x _ => (x : ℕ)) ?_ ?_ ?_ ?_
  · intro x hx; exact mem_primesDvd.mp hx
  · intro a _ b _ hab; exact Subtype.ext hab
  · intro b hb
    exact ⟨(⟨b, (Nat.mem_primeFactors.mp hb).1⟩ : Nat.Primes), mem_primesDvd.mpr hb, rfl⟩
  · intro a _; rfl

/-- The Euler product `∏'_p (1 - 1/p²)` over the primes is multipliable. -/
lemma multipliable_prime_euler :
    Multipliable (fun p : Nat.Primes => 1 - 1 / ((p : ℕ) : ℝ) ^ 2) := by
  have h1 : Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-2 : ℝ)) :=
    Nat.Primes.summable_rpow.mpr (by norm_num)
  have h2 : Summable (fun p : Nat.Primes => 1 / ((p : ℕ) : ℝ) ^ 2) := by
    refine h1.congr (fun p => ?_)
    rw [Real.rpow_neg (by positivity), Real.rpow_two, one_div]
  have h3 : Summable (fun p : Nat.Primes => -(1 / ((p : ℕ) : ℝ) ^ 2)) := h2.neg
  have h4 := Real.multipliable_one_add_of_summable h3
  simpa [sub_eq_add_neg] using h4

/-- Pulling a finite set of factors out of an infinite product: if `f` is multipliable and
nonzero on the finset `S`, then `∏'_x (if x ∈ S then 1 else f x) = (∏'_x f x) / ∏_{x∈S} f x`. -/
lemma tprod_ite_finset_mul_inv {β : Type*} [DecidableEq β] (f : β → ℝ) (S : Finset β)
    (hf : Multipliable f) (hne : ∀ x ∈ S, f x ≠ 0) :
    ∏' x, (if x ∈ S then (1 : ℝ) else f x)
      = (∏' x, f x) * (∏ x ∈ S, f x)⁻¹ := by
  classical
  have key : (fun x => if x ∈ S then (1 : ℝ) else f x)
      = fun x => f x * (if x ∈ S then (f x)⁻¹ else 1) := by
    funext x
    by_cases hx : x ∈ S
    · rw [if_pos hx, if_pos hx, mul_inv_cancel₀ (hne x hx)]
    · rw [if_neg hx, if_neg hx, mul_one]
  rw [key]
  have hθ : Multipliable (fun x => if x ∈ S then (f x)⁻¹ else 1) := by
    apply multipliable_of_hasFiniteMulSupport
    apply Set.Finite.subset (S.finite_toSet)
    intro x hx
    simp only [Function.mem_mulSupport] at hx
    by_contra hS
    exact hx (if_neg hS)
  rw [(hf.hasProd.mul hθ.hasProd).tprod_eq]
  have hprod : ∏' x, (if x ∈ S then (f x)⁻¹ else 1) = (∏ x ∈ S, f x)⁻¹ := by
    rw [tprod_eq_prod (s := S) (fun x hx => by simp [hx])]
    have h2 : (∏ b ∈ S, (if b ∈ S then (f b)⁻¹ else 1)) = ∏ b ∈ S, (f b)⁻¹ :=
      Finset.prod_congr rfl (fun b hb => by simp [hb])
    rw [h2, Finset.prod_inv_distrib]
  rw [hprod]

/-- Predicate form of `tprod_ite_finset_mul_inv`. -/
lemma tprod_ite_pred_mul_inv {β : Type*} (f : β → ℝ) (P : β → Prop) [DecidablePred P]
    (S : Finset β)
    (hPS : ∀ x, x ∈ S ↔ P x) (hf : Multipliable f) (hne : ∀ x ∈ S, f x ≠ 0) :
    ∏' x, (if P x then (1 : ℝ) else f x)
      = (∏' x, f x) * (∏ x ∈ S, f x)⁻¹ := by
  classical
  have h1 : (∏' x, (if P x then (1 : ℝ) else f x))
      = ∏' x, (if x ∈ S then (1 : ℝ) else f x) := by
    refine tprod_congr (fun x => ?_)
    by_cases h : x ∈ S
    · rw [if_pos h, if_pos ((hPS x).mp h)]
    · rw [if_neg h, if_neg (fun h' => h ((hPS x).mpr h'))]
  rw [h1]
  exact tprod_ite_finset_mul_inv f S hf hne

theorem tprod_dvd_ite_eq (r : ℕ) (hr : 1 ≤ r) :
    ∏' p : Nat.Primes, (if (p : ℕ) ∣ r then (1 : ℝ) else 1 - 1 / ((p : ℕ) : ℝ) ^ 2)
      = (∏' p : Nat.Primes, (1 - 1 / ((p : ℕ) : ℝ) ^ 2))
        * (∏ p ∈ r.primeFactors, (1 - 1 / (p : ℝ) ^ 2))⁻¹ := by
  classical
  have hr0 : r ≠ 0 := by omega
  have hne : ∀ p ∈ primesDvd r, (1 - 1 / ((p : ℕ) : ℝ) ^ 2) ≠ 0 := by
    intro p _
    have hp2 : 2 ≤ (p : ℕ) := p.2.two_le
    have hge : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast hp2
    have hpos : 0 < 1 - 1 / ((p : ℕ) : ℝ) ^ 2 := by
      rw [sub_pos, div_lt_one (by positivity)]
      nlinarith [hge]
    exact ne_of_gt hpos
  have hPS : ∀ p : Nat.Primes, p ∈ primesDvd r ↔ (p : ℕ) ∣ r := by
    intro p
    rw [mem_primesDvd, dvd_iff_mem_primeFactors hr0]
  rw [tprod_ite_pred_mul_inv (fun p : Nat.Primes => 1 - 1 / ((p : ℕ) : ℝ) ^ 2)
        (fun p => (p : ℕ) ∣ r) (primesDvd r) hPS multipliable_prime_euler hne]
  rw [prod_primesDvd r]

end Work.LinnikAreas.Density4
