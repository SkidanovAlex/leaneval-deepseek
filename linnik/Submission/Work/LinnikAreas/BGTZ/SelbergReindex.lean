import Mathlib
import Submission.Work.LinnikAreas.BGTZ.SelbergAux
import Submission.Work.Sieve.G_at_one_defs

open scoped BigOperators
open DirichletCharacter

namespace Work.LinnikAreas.BGTZ

variable {q : ℕ} [NeZero q]

/-- If `g` maps `s` injectively into `t` and `f ≥ 0` on `t`, then `Σ_{x∈s} f (g x) ≤ Σ_{y∈t} f y`. -/
lemma sum_le_of_injOn {α : Type*} (s : Finset α) (g : α → ℕ) (f : ℕ → ℝ) (t : Finset ℕ)
    (hinj : Set.InjOn g ↑s) (hmaps : ∀ x ∈ s, g x ∈ t) (hnn : ∀ y ∈ t, 0 ≤ f y) :
    ∑ x ∈ s, f (g x) ≤ ∑ y ∈ t, f y := by
  rw [← Finset.sum_image (f := f) hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun y hy => ?_) (fun y hy _ => hnn y hy)
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  exact hmaps x hx

/-- The lcm of two squarefree naturals is squarefree. -/
lemma squarefree_lcm' {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b) :
    Squarefree (Nat.lcm a b) := by
  rw [Nat.squarefree_iff_factorization_le_one (Nat.lcm_ne_zero ha.ne_zero hb.ne_zero)]
  intro p
  rw [Nat.factorization_lcm ha.ne_zero hb.ne_zero]
  exact max_le (ha.natFactorization_le_one p) (hb.natFactorization_le_one p)

/-- A product of distinct primes is squarefree. -/
lemma squarefree_prod_primes : ∀ (s : Finset ℕ), (∀ p ∈ s, p.Prime) → Squarefree (∏ p ∈ s, p) := by
  classical
  intro s
  induction s using Finset.cons_induction with
  | empty => intro _; simp
  | cons a s ha ih =>
    intro hs
    rw [Finset.prod_cons]
    have ha' : Nat.Prime a := hs a (Finset.mem_cons_self a s)
    have hs' : ∀ p ∈ s, p.Prime := fun p hp => hs p (Finset.mem_cons_of_mem hp)
    have hcop : Nat.Coprime a (∏ p ∈ s, p) := by
      rw [Nat.Prime.coprime_iff_not_dvd ha']
      intro hdvd
      obtain ⟨i, hi, hai⟩ := (Nat.prime_iff.mp ha').exists_mem_finset_dvd hdvd
      have haeq : a = i := (Nat.prime_dvd_prime_iff_eq ha' (hs' i hi)).mp hai
      exact ha (haeq.symm ▸ hi)
    exact (Nat.squarefree_mul hcop).mpr ⟨(Nat.prime_iff.mp ha').squarefree, ih hs'⟩

/-- **`Σ_k Z_k/g(k) ≤ V(R)`.** -/
theorem Zfun_sum_le_VFun (χ₁ : DirichletCharacter ℂ q) (hreal : χ₁ ^ 2 = 1) (R : ℕ) :
    (∑ k ∈ (Finset.Icc 1 R).filter (fun k => Nat.Coprime k q ∧ Squarefree k),
        (1 / Work.LinnikAreas.Sieve.gFun χ₁ k) * Work.Sieve.Zfun χ₁ R k)
      ≤ Work.LinnikAreas.Sieve.VFun χ₁ R := by
  obtain ⟨-, -, -, -, hgpos, hgmul, -⟩ := Work.Sieve.gFun_theory χ₁ hreal
  set K : Finset ℕ := (Finset.Icc 1 R).filter (fun k => Nat.Coprime k q ∧ Squarefree k) with hK
  set D : Finset (ℕ × ℕ) := (K ×ˢ Finset.Icc 1 R).filter
      (fun x => x.1 * x.2 ≤ R ∧ x.2 ∣ ∏ p ∈ q.primeFactors, p) with hD
  have hsrq : Squarefree (∏ p ∈ q.primeFactors, p) :=
    squarefree_prod_primes _ (fun p hp => Nat.prime_of_mem_primeFactors hp)
  have hrqdvd : (∏ p ∈ q.primeFactors, p) ∣ q := Nat.prod_primeFactors_dvd q
  have hmemD : ∀ x ∈ D, x.1 ∈ K ∧ x.2 ∈ Finset.Icc 1 R ∧ x.1 * x.2 ≤ R ∧
      x.2 ∣ ∏ p ∈ q.primeFactors, p := by
    intro x hx
    rw [hD] at hx
    obtain ⟨hmem, hle, hdvd⟩ := Finset.mem_filter.mp hx
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hmem
    exact ⟨h1, h2, hle, hdvd⟩
  have hxK1 : ∀ x ∈ D, x.1 ∈ Finset.Icc 1 R ∧ Nat.Coprime x.1 q ∧
      Squarefree x.1 := by
    intro x hx
    have h := (hmemD x hx).1
    rw [hK, Finset.mem_filter] at h
    exact ⟨h.1, h.2.1, h.2.2⟩
  have hmul : ∀ x ∈ D, (1 / Work.LinnikAreas.Sieve.gFun χ₁ x.1)
      * (1 / Work.LinnikAreas.Sieve.gFun χ₁ x.2)
      = 1 / Work.LinnikAreas.Sieve.gFun χ₁ (x.1 * x.2) := by
    intro x hx
    obtain ⟨-, -, -, hxdvd⟩ := hmemD x hx
    obtain ⟨hxKI, hxcop, hxsf⟩ := hxK1 x hx
    have hx2sf : Squarefree x.2 := hsrq.squarefree_of_dvd hxdvd
    have hcop : Nat.Coprime x.1 x.2 := hxcop.coprime_dvd_right (Nat.dvd_trans hxdvd hrqdvd)
    rw [div_mul_div_comm, one_mul, ← hgmul x.1 x.2 hxsf hx2sf hcop]
  have hinj : Set.InjOn (fun x : ℕ × ℕ => x.1 * x.2) ↑D := by
    intro x hx y hy hxy
    have hxy' : x.1 * x.2 = y.1 * y.2 := hxy
    obtain ⟨-, -, -, hxdvd⟩ := hmemD x hx
    obtain ⟨-, -, -, hydvd⟩ := hmemD y hy
    obtain ⟨-, hxcop, -⟩ := hxK1 x hx
    obtain ⟨-, hycop, -⟩ := hxK1 y hy
    have hx2sf : Squarefree x.2 := hsrq.squarefree_of_dvd hxdvd
    have hy2sf : Squarefree y.2 := hsrq.squarefree_of_dvd hydvd
    have hx20 : x.2 ≠ 0 := hx2sf.ne_zero
    have hy20 : y.2 ≠ 0 := hy2sf.ne_zero
    have step : ∀ {p : ℕ}, p.Prime → p ∣ x.2 → p ∣ y.2 := by
      intro p hpp hpx2
      have hpq : p ∣ q := Nat.dvd_trans (Nat.dvd_trans hpx2 hxdvd) hrqdvd
      have hpkm : p ∣ y.1 * y.2 := by rw [← hxy']; exact dvd_mul_of_dvd_right hpx2 x.1
      rcases hpp.dvd_mul.mp hpkm with h | h
      · exfalso
        have : p ∣ Nat.gcd y.1 q := Nat.dvd_gcd h hpq
        rw [show Nat.gcd y.1 q = 1 from hycop] at this
        exact hpp.not_dvd_one this
      · exact h
    have step' : ∀ {p : ℕ}, p.Prime → p ∣ y.2 → p ∣ x.2 := by
      intro p hpp hpy2
      have hpq : p ∣ q := Nat.dvd_trans (Nat.dvd_trans hpy2 hydvd) hrqdvd
      have hpkm : p ∣ x.1 * x.2 := by rw [hxy']; exact dvd_mul_of_dvd_right hpy2 y.1
      rcases hpp.dvd_mul.mp hpkm with h | h
      · exfalso
        have : p ∣ Nat.gcd x.1 q := Nat.dvd_gcd h hpq
        rw [show Nat.gcd x.1 q = 1 from hxcop] at this
        exact hpp.not_dvd_one this
      · exact h
    have hsubXY : x.2.primeFactors ⊆ y.2.primeFactors := fun p hp =>
      Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hp).1,
        step (Nat.mem_primeFactors.mp hp).1 (Nat.mem_primeFactors.mp hp).2.1, hy20⟩
    have hsubYX : y.2.primeFactors ⊆ x.2.primeFactors := fun p hp =>
      Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hp).1,
        step' (Nat.mem_primeFactors.mp hp).1 (Nat.mem_primeFactors.mp hp).2.1, hx20⟩
    have hx2eq : x.2 = y.2 := by
      rw [← Nat.prod_primeFactors_of_squarefree hx2sf,
        ← Nat.prod_primeFactors_of_squarefree hy2sf]
      congr 1
      exact Finset.Subset.antisymm hsubXY hsubYX
    have hx1eq : x.1 = y.1 := by
      have h := hxy'
      rw [hx2eq] at h
      exact mul_right_cancel₀ hy20 h
    exact Prod.ext hx1eq hx2eq
  have hL : (∑ k ∈ K, (1 / Work.LinnikAreas.Sieve.gFun χ₁ k) * Work.Sieve.Zfun χ₁ R k)
      = ∑ x ∈ D, (1 / Work.LinnikAreas.Sieve.gFun χ₁ x.1)
          * (1 / Work.LinnikAreas.Sieve.gFun χ₁ x.2) := by
    have h1 : (∑ k ∈ K, (1 / Work.LinnikAreas.Sieve.gFun χ₁ k) * Work.Sieve.Zfun χ₁ R k)
        = ∑ k ∈ K, ∑ m ∈ (Finset.Icc 1 R).filter
            (fun m => k * m ≤ R ∧ m ∣ ∏ p ∈ q.primeFactors, p),
            (1 / Work.LinnikAreas.Sieve.gFun χ₁ k) * (1 / Work.LinnikAreas.Sieve.gFun χ₁ m) := by
      apply Finset.sum_congr rfl; intro k hk
      rw [Work.Sieve.Zfun, Finset.mul_sum]
    rw [h1]
    have h2 : (∑ k ∈ K, ∑ m ∈ (Finset.Icc 1 R).filter
            (fun m => k * m ≤ R ∧ m ∣ ∏ p ∈ q.primeFactors, p),
            (1 / Work.LinnikAreas.Sieve.gFun χ₁ k) * (1 / Work.LinnikAreas.Sieve.gFun χ₁ m))
        = ∑ k ∈ K, ∑ m ∈ Finset.Icc 1 R, (if k * m ≤ R ∧ m ∣ ∏ p ∈ q.primeFactors, p
            then (1 / Work.LinnikAreas.Sieve.gFun χ₁ k) * (1 / Work.LinnikAreas.Sieve.gFun χ₁ m)
            else 0) := by
      apply Finset.sum_congr rfl; intro k hk
      rw [Finset.sum_filter]
    rw [h2]
    have h3 : (∑ k ∈ K, ∑ m ∈ Finset.Icc 1 R, (if k * m ≤ R ∧ m ∣ ∏ p ∈ q.primeFactors, p
          then (1 / Work.LinnikAreas.Sieve.gFun χ₁ k) * (1 / Work.LinnikAreas.Sieve.gFun χ₁ m)
          else 0))
        = ∑ x ∈ K ×ˢ Finset.Icc 1 R, (if x.1 * x.2 ≤ R ∧ x.2 ∣ ∏ p ∈ q.primeFactors, p
          then (1 / Work.LinnikAreas.Sieve.gFun χ₁ x.1) * (1 / Work.LinnikAreas.Sieve.gFun χ₁ x.2)
          else 0) :=
      (Finset.sum_product (s := K) (t := Finset.Icc 1 R)
        (f := fun x : ℕ × ℕ => if x.1 * x.2 ≤ R ∧ x.2 ∣ ∏ p ∈ q.primeFactors, p
          then (1 / Work.LinnikAreas.Sieve.gFun χ₁ x.1) * (1 / Work.LinnikAreas.Sieve.gFun χ₁ x.2)
          else 0)).symm
    rw [h3, hD, ← Finset.sum_filter]
  rw [hL, Finset.sum_congr rfl hmul]
  have hV : Work.LinnikAreas.Sieve.VFun χ₁ R
      = ∑ ℓ ∈ (Finset.Icc 1 R).filter (fun ℓ => Squarefree ℓ),
          1 / Work.LinnikAreas.Sieve.gFun χ₁ ℓ := by
    rw [Work.LinnikAreas.Sieve.VFun]
    rw [show (∑ ℓ ∈ Finset.Icc 1 R, (if Squarefree ℓ then (1 : ℝ) else 0)
            / Work.LinnikAreas.Sieve.gFun χ₁ ℓ)
          = ∑ ℓ ∈ Finset.Icc 1 R, (if Squarefree ℓ then 1 / Work.LinnikAreas.Sieve.gFun χ₁ ℓ else 0)
          from Finset.sum_congr rfl (fun ℓ _ => by by_cases h : Squarefree ℓ <;> simp [h])]
    rw [← Finset.sum_filter]
  rw [hV]
  refine sum_le_of_injOn D (fun x => x.1 * x.2) (fun ℓ => 1 / Work.LinnikAreas.Sieve.gFun χ₁ ℓ)
    ((Finset.Icc 1 R).filter (fun ℓ => Squarefree ℓ)) hinj ?_ ?_
  · intro x hx
    obtain ⟨-, hxI, hxle, hxdvd⟩ := hmemD x hx
    obtain ⟨hxKI, hxcop, hxsf⟩ := hxK1 x hx
    have hx10 : x.1 ≠ 0 := by have := (Finset.mem_Icc.mp hxKI).1; omega
    have hx20 : x.2 ≠ 0 := by have := (Finset.mem_Icc.mp hxI).1; omega
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hx10 hx20), hxle⟩,
      (Nat.squarefree_mul (hxcop.coprime_dvd_right (Nat.dvd_trans hxdvd hrqdvd))).mpr
        ⟨hxsf, hsrq.squarefree_of_dvd hxdvd⟩⟩
  · intro ℓ hℓ
    rw [Finset.mem_filter] at hℓ
    exact div_nonneg zero_le_one (le_of_lt (hgpos ℓ hℓ.2))

/-- If `g` maps `s` injectively into `t` and `f ≥ 0` on `t`, then `Σ_{x∈s} f (g x) ≤ Σ_{y∈t} f y`. -/
lemma sum_le_of_injOn' {α β : Type*} [DecidableEq β] (s : Finset α) (g : α → β) (f : β → ℝ)
    (t : Finset β) (hinj : Set.InjOn g ↑s) (hmaps : ∀ x ∈ s, g x ∈ t) (hnn : ∀ y ∈ t, 0 ≤ f y) :
    ∑ x ∈ s, f (g x) ≤ ∑ y ∈ t, f y := by
  rw [← Finset.sum_image (f := f) hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun y hy => ?_) (fun y hy _ => hnn y hy)
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  exact hmaps x hx

/-- **`V(R) = Σ_{ℓ ∈ Icc 1 R, squarefree} 1/g(ℓ)`.** -/
lemma VFun_eq_sum_filter (χ₁ : DirichletCharacter ℂ q) (R : ℕ) :
    Work.LinnikAreas.Sieve.VFun χ₁ R
      = ∑ ℓ ∈ (Finset.Icc 1 R).filter (fun ℓ => Squarefree ℓ),
          1 / Work.LinnikAreas.Sieve.gFun χ₁ ℓ := by
  rw [Work.LinnikAreas.Sieve.VFun]
  rw [show (∑ ℓ ∈ Finset.Icc 1 R, (if Squarefree ℓ then (1 : ℝ) else 0)
          / Work.LinnikAreas.Sieve.gFun χ₁ ℓ)
        = ∑ ℓ ∈ Finset.Icc 1 R, (if Squarefree ℓ then 1 / Work.LinnikAreas.Sieve.gFun χ₁ ℓ else 0)
        from Finset.sum_congr rfl (fun ℓ _ => by by_cases h : Squarefree ℓ <;> simp [h])]
  rw [← Finset.sum_filter]

/-- **`Σ_{n ≤ R} a(n)/n ≤ V(R)`.** -/
theorem VFun_ge_sum_aFun_div (χ₁ : DirichletCharacter ℂ q) (hreal : χ₁ ^ 2 = 1) (R : ℕ) :
    ∑ n ∈ Finset.Icc 1 R, Work.LinnikAreas.Sieve.aFun χ₁ n / (n : ℝ)
      ≤ Work.LinnikAreas.Sieve.VFun χ₁ R := by
  obtain ⟨-, -, -, hgsf, hgpos, hgmul, -⟩ := Work.Sieve.gFun_theory χ₁ hreal
  set B : Finset ℕ := (Finset.Icc 1 R).filter (fun ℓ => Squarefree ℓ) with hB
  have hrad : ∀ n ∈ Finset.Icc 1 R, (∏ p ∈ n.primeFactors, p) ∈ B := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    rw [hB, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, squarefree_prod_primes _ (fun p hp => Nat.prime_of_mem_primeFactors hp)⟩
    · exact Nat.one_le_iff_ne_zero.mpr
        (Finset.prod_ne_zero_iff.mpr (fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero))
    · exact le_trans (Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd n)) (Finset.mem_Icc.mp hn).2
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.Icc 1 R) (t := B)
    (g := fun n => ∏ p ∈ n.primeFactors, p)
    (f := fun n => Work.LinnikAreas.Sieve.aFun χ₁ n / (n : ℝ)) hrad]
  rw [VFun_eq_sum_filter χ₁ R]
  refine Finset.sum_le_sum (fun ℓ hℓ => ?_)
  obtain ⟨hℓI, hℓsf⟩ := Finset.mem_filter.mp hℓ
  -- the per-squarefree bound
  have hfib : (∑ n ∈ (Finset.Icc 1 R).filter (fun n => ∏ p ∈ n.primeFactors, p = ℓ),
        Work.LinnikAreas.Sieve.aFun χ₁ n / (n : ℝ))
      ≤ ∏ p ∈ ℓ.primeFactors, ∑' k : ℕ,
          Work.LinnikAreas.Sieve.aFun χ₁ (p ^ (k + 1)) / (p : ℝ) ^ (k + 1) := by
    have heq : (∑ n ∈ (Finset.Icc 1 R).filter (fun n => ∏ p ∈ n.primeFactors, p = ℓ),
          Work.LinnikAreas.Sieve.aFun χ₁ n / (n : ℝ))
        = ∑ n ∈ (Finset.Icc 1 R).filter (fun n => ∏ p ∈ n.primeFactors, p = ℓ),
            (fun v => ∏ x ∈ ℓ.primeFactors.attach, Work.LinnikAreas.Sieve.aFun χ₁
              (x.1 ^ (v x.1 x.2)) / ((x.1 : ℝ) ^ (v x.1 x.2)))
            (fun (p : ℕ) (hp : p ∈ ℓ.primeFactors) => n.factorization p) := by
      apply Finset.sum_congr rfl; intro n hn
      rw [Finset.mem_filter] at hn
      have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn.1).1; omega
      have hpf : n.primeFactors = ℓ.primeFactors := by
        rw [← hn.2, Nat.primeFactors_prod (fun p hp => Nat.prime_of_mem_primeFactors hp)]
      have h1 := aFun_prod_primeFactors χ₁ hreal n hn0
      have hden : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p := by
        conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hn0]
        rw [Nat.cast_prod]
        apply Finset.prod_congr rfl; intro p hp; push_cast; ring
      rw [h1, hden, ← Finset.prod_div_distrib, hpf]
      rw [show (∏ x ∈ ℓ.primeFactors, Work.LinnikAreas.Sieve.aFun χ₁ (x ^ n.factorization x)
              / ((x : ℝ) ^ n.factorization x))
            = (fun v => ∏ x ∈ ℓ.primeFactors.attach, Work.LinnikAreas.Sieve.aFun χ₁
                (x.1 ^ (v x.1 x.2)) / ((x.1 : ℝ) ^ (v x.1 x.2)))
              (fun (p : ℕ) (hp : p ∈ ℓ.primeFactors) => n.factorization p) from by
          show (∏ x ∈ ℓ.primeFactors, Work.LinnikAreas.Sieve.aFun χ₁ (x ^ n.factorization x)
              / ((x : ℝ) ^ n.factorization x))
            = ∏ x ∈ ℓ.primeFactors.attach, Work.LinnikAreas.Sieve.aFun χ₁
                (x.1 ^ n.factorization x.1) / ((x.1 : ℝ) ^ n.factorization x.1)
          rw [Finset.prod_attach ℓ.primeFactors (fun p =>
            Work.LinnikAreas.Sieve.aFun χ₁ (p ^ n.factorization p) / ((p : ℝ) ^ n.factorization p))]]
    rw [heq]
    have hstep : (∑ n ∈ (Finset.Icc 1 R).filter (fun n => ∏ p ∈ n.primeFactors, p = ℓ),
            (fun v => ∏ x ∈ ℓ.primeFactors.attach, Work.LinnikAreas.Sieve.aFun χ₁
              (x.1 ^ (v x.1 x.2)) / ((x.1 : ℝ) ^ (v x.1 x.2)))
            (fun (p : ℕ) (hp : p ∈ ℓ.primeFactors) => n.factorization p))
        ≤ ∑ v ∈ ℓ.primeFactors.pi (fun _ => Finset.Icc 1 R),
            ∏ x ∈ ℓ.primeFactors.attach, Work.LinnikAreas.Sieve.aFun χ₁
              (x.1 ^ (v x.1 x.2)) / ((x.1 : ℝ) ^ (v x.1 x.2)) := by
      refine sum_le_of_injOn'
        (s := (Finset.Icc 1 R).filter (fun n => ∏ p ∈ n.primeFactors, p = ℓ))
        (g := fun (n : ℕ) => fun (p : ℕ) (hp : p ∈ ℓ.primeFactors) => n.factorization p)
        (f := fun v => ∏ x ∈ ℓ.primeFactors.attach, Work.LinnikAreas.Sieve.aFun χ₁
          (x.1 ^ (v x.1 x.2)) / ((x.1 : ℝ) ^ (v x.1 x.2)))
        (t := ℓ.primeFactors.pi (fun _ => Finset.Icc 1 R)) ?_ ?_ ?_
      · intro x hx y hy hxy
        have hx2 : x ∈ (Finset.Icc 1 R).filter (fun n => ∏ p ∈ n.primeFactors, p = ℓ) := hx
        have hy2 : y ∈ (Finset.Icc 1 R).filter (fun n => ∏ p ∈ n.primeFactors, p = ℓ) := hy
        rw [Finset.mem_filter] at hx2 hy2
        have hxI : x ∈ Finset.Icc 1 R := hx2.1
        have hxrad : ∏ p ∈ x.primeFactors, p = ℓ := hx2.2
        have hyI : y ∈ Finset.Icc 1 R := hy2.1
        have hyrad : ∏ p ∈ y.primeFactors, p = ℓ := hy2.2
        have hx0 : x ≠ 0 := by have := (Finset.mem_Icc.mp hxI).1; omega
        have hy0 : y ≠ 0 := by have := (Finset.mem_Icc.mp hyI).1; omega
        have hxpf : x.primeFactors = ℓ.primeFactors := by
          rw [← hxrad, Nat.primeFactors_prod (fun p hp => Nat.prime_of_mem_primeFactors hp)]
        have hypf : y.primeFactors = ℓ.primeFactors := by
          rw [← hyrad, Nat.primeFactors_prod (fun p hp => Nat.prime_of_mem_primeFactors hp)]
        rw [Nat.prod_primeFactors_pow_factorization hx0,
          Nat.prod_primeFactors_pow_factorization hy0, hxpf, hypf]
        refine Finset.prod_congr rfl (fun p hp => ?_)
        rw [show x.factorization p = y.factorization p from congrFun (congrFun hxy p) hp]
      · intro n hn
        rw [Finset.mem_filter] at hn
        rw [Finset.mem_pi]
        intro p hp
        rw [Finset.mem_Icc]
        have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
        have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn.1).1; omega
        have hpn : p ∣ n := by
          have hpℓ : p ∣ ℓ := by
            rw [← Nat.prod_primeFactors_of_squarefree hℓsf]
            exact Finset.dvd_prod_of_mem (fun q => q) hp
          have h1 : p ∣ ∏ q ∈ n.primeFactors, q := by
            rw [hn.2]; exact hpℓ
          obtain ⟨q, hq, hpq⟩ :=
            (Prime.dvd_finsetProd_iff (Nat.prime_iff.mp hpp) (g := fun q => q)).mp h1
          have hqq : q.Prime := Nat.prime_of_mem_primeFactors hq
          have hpq' : p = q := (Nat.prime_dvd_prime_iff_eq hpp hqq).mp hpq
          rw [hpq']; exact (Nat.mem_primeFactors.mp hq).2.1
        have h1 : n.factorization p ≠ 0 := by
          apply Finsupp.mem_support_iff.mp
          rw [Nat.support_factorization]
          exact Nat.mem_primeFactors.mpr ⟨hpp, hpn, hn0⟩
        exact ⟨by rw [Nat.one_le_iff_ne_zero]; exact h1,
          le_trans (le_of_lt (Nat.factorization_lt p hn0)) (Finset.mem_Icc.mp hn.1).2⟩
      · intro v hv
        exact Finset.prod_nonneg (fun x hx => div_nonneg
          (Work.Sieve.aFun_nonneg_le_card χ₁ hreal _).1 (pow_nonneg (Nat.cast_nonneg x.1) _))
    refine le_trans hstep ?_
    rw [← Finset.prod_sum (s := ℓ.primeFactors) (t := fun _ => Finset.Icc 1 R)
      (f := fun (p : ℕ) (v : ℕ) => Work.LinnikAreas.Sieve.aFun χ₁ (p ^ v) / (p : ℝ) ^ v)]
    refine Finset.prod_le_prod₀ (fun p hp => Finset.sum_nonneg (s := Finset.Icc 1 R) (fun v _ =>
      div_nonneg (Work.Sieve.aFun_nonneg_le_card χ₁ hreal (p ^ v)).1
        (pow_nonneg (Nat.cast_nonneg p) v))) (fun p hp => ?_)
    have hp' : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hs : Summable (fun k : ℕ =>
        Work.LinnikAreas.Sieve.aFun χ₁ (p ^ (k + 1)) / (p : ℝ) ^ (k + 1)) :=
      Summable.of_nonneg_of_le (fun k => div_nonneg
        (Work.Sieve.aFun_nonneg_le_card χ₁ hreal (p ^ (k + 1))).1
          (pow_nonneg (Nat.cast_nonneg p) (k + 1))) (fun k => by
          rw [div_le_div_iff_of_pos_right (pow_pos (Nat.cast_pos.mpr hp'.pos) (k + 1))]
          calc Work.LinnikAreas.Sieve.aFun χ₁ (p ^ (k + 1))
              ≤ (((p ^ (k + 1)).divisors.card : ℕ) : ℝ) :=
                (Work.Sieve.aFun_nonneg_le_card χ₁ hreal (p ^ (k + 1))).2
            _ = (k : ℝ) + 2 := by
                rw [Nat.divisors_prime_pow hp' (k + 1), Finset.card_map, Finset.card_range]
                push_cast; ring)
        (Work.Sieve.summable_div_prime_pow p hp')
    rw [show (∑ v ∈ Finset.Icc 1 R, Work.LinnikAreas.Sieve.aFun χ₁ (p ^ v) / (p : ℝ) ^ v)
          = ∑ k ∈ Finset.range R,
              Work.LinnikAreas.Sieve.aFun χ₁ (p ^ (k + 1)) / (p : ℝ) ^ (k + 1) from by
        rw [show Finset.Icc 1 R = (Finset.range R).image (fun k => k + 1) from by
              ext v; simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
              constructor
              · rintro ⟨h1, h2⟩; exact ⟨v - 1, by omega, by omega⟩
              · rintro ⟨k, hk, rfl⟩; omega]
        rw [Finset.sum_image (f := fun v => Work.LinnikAreas.Sieve.aFun χ₁ (p ^ v) / (p : ℝ) ^ v)
          (g := fun k : ℕ => k + 1)
          (by intro a ha b hb hab; exact Nat.succ_injective hab)]]
    exact Summable.sum_le_tsum _ (fun k _ => div_nonneg
      (Work.Sieve.aFun_nonneg_le_card χ₁ hreal (p ^ (k + 1))).1
        (pow_nonneg (Nat.cast_nonneg p) (k + 1))) hs
  rw [show 1 / Work.LinnikAreas.Sieve.gFun χ₁ ℓ
        = ∏ p ∈ ℓ.primeFactors, ∑' k : ℕ,
            Work.LinnikAreas.Sieve.aFun χ₁ (p ^ (k + 1)) / (p : ℝ) ^ (k + 1) from by
      rw [hgsf ℓ hℓsf, one_div, ← Finset.prod_inv_distrib]
      apply Finset.prod_congr rfl; intro p hp
      rw [Work.LinnikAreas.Sieve.gPrime, inv_inv]]
  exact hfib

end Work.LinnikAreas.BGTZ
