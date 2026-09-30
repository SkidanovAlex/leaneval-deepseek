import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Definitions and elementary lemmas for the Kummer crux (`Work.BW.kummer_crux`).

We fix a field `K`, a ring hom `φ : K →+* ℂ`, elements `η : Fin r → K` and chosen square roots
`ρ : Fin r → ℂ` with `ρ i ^ 2 = φ (η i)`. Write `B_ε = ∏ i, ρ i ^ (ε i : ℕ)` for
`ε : Fin r → Fin 2`, and `T d = ∑ ε, φ (d ε) * B_ε` for a coefficient function `d`.

The main algebraic content is `Bfun_mul`: `B_ε * B_δ = φ (∏ i, η i ^ (ε i * δ i)) * B_{ε+δ}`,
which exhibits `T` as a ring homomorphism onto a `ℤ/2`-graded algebra: `cMul` is the induced
product on coefficient functions, and functions supported on `{ε | ε i = v}` multiply into
functions supported on `{γ | γ i = w + w'}`. -/

namespace Work.BW

open Finset

/-- `B_ε = ∏ i, ρ i ^ (ε i : ℕ)`. -/
noncomputable def Bfun {r : ℕ} (ρ : Fin r → ℂ) (ε : Fin r → Fin 2) : ℂ :=
  ∏ i, ρ i ^ (ε i : ℕ)

/-- `T d = ∑ ε, φ (d ε) * B_ε`. -/
noncomputable def Tfun {K : Type*} [Field K] {r : ℕ} (φ : K →+* ℂ) (ρ : Fin r → ℂ)
    (d : (Fin r → Fin 2) → K) : ℂ :=
  ∑ ε, φ (d ε) * Bfun ρ ε

/-- Coefficient-level product on the `2^r`-dimensional space: the coefficients of the product
`T d * T d'` are `(cMul η d d') γ = ∑_{ε+δ=γ} (∏ i, η i ^ (ε i * δ i)) d ε d' δ`. -/
noncomputable def cMul {K : Type*} [Field K] {r : ℕ} (η : Fin r → K)
    (d d' : (Fin r → Fin 2) → K) : (Fin r → Fin 2) → K :=
  fun γ => ∑ p ∈ ((Finset.univ : Finset ((Fin r → Fin 2) × (Fin r → Fin 2))).filter
      (fun p => p.1 + p.2 = γ)), (∏ i, η i ^ ((p.1 i : ℕ) * (p.2 i : ℕ))) * d p.1 * d' p.2

/-- `d` is supported on the "hyperplane" `{ε | ε i = v}`, i.e. it vanishes off it. -/
def Supp {K : Type*} [Field K] {r : ℕ} (i : Fin r) (v : Fin 2)
    (d : (Fin r → Fin 2) → K) : Prop :=
  ∀ ε, ε i ≠ v → d ε = 0

/-! ### Elementary `Fin 2` facts -/

theorem fin2_eq_zero_or_one (a : Fin 2) : a = 0 ∨ a = 1 := by fin_cases a <;> simp

theorem fin2_ne_one (a : Fin 2) (h : a ≠ 1) : a = 0 := by
  rcases fin2_eq_zero_or_one a with h0 | h1
  · exact h0
  · exact absurd h1 h

theorem fin2_ne_zero (a : Fin 2) (h : a ≠ 0) : a = 1 := by
  rcases fin2_eq_zero_or_one a with h0 | h1
  · exact absurd h0 h
  · exact h1

theorem fin2_zero_add_zero : (0 : Fin 2) + 0 = 0 := by decide
theorem fin2_one_add_one : (1 : Fin 2) + 1 = 0 := by decide
theorem fin2_zero_add_one : (0 : Fin 2) + 1 = 1 := by decide

/-- `(x ^ n) ^ 2 = (x ^ 2) ^ n`. -/
theorem pow_swap_two (x : ℂ) (n : ℕ) : (x ^ n) ^ 2 = (x ^ 2) ^ n := by
  rw [← pow_mul, Nat.mul_comm n 2, pow_mul]

/-! ### The product formula and linearity of `T` -/

theorem Bfun_mul {K : Type*} [Field K] {r : ℕ} (φ : K →+* ℂ) (η : Fin r → K)
    (ρ : Fin r → ℂ) (hρ : ∀ i, ρ i ^ 2 = φ (η i)) (ε δ : Fin r → Fin 2) :
    Bfun ρ ε * Bfun ρ δ
      = φ (∏ i, η i ^ ((ε i : ℕ) * (δ i : ℕ))) * Bfun ρ (ε + δ) := by
  unfold Bfun
  rw [← Finset.prod_mul_distrib]
  have key : ∀ i : Fin r, ρ i ^ (ε i : ℕ) * ρ i ^ (δ i : ℕ)
      = (φ (η i)) ^ ((ε i : ℕ) * (δ i : ℕ)) * ρ i ^ (((ε + δ) i : Fin 2) : ℕ) := by
    intro i
    rw [← pow_add]
    rw [← hρ i]
    have hkey : ∀ (a b : Fin 2), ρ i ^ ((a : ℕ) + (b : ℕ))
        = (ρ i ^ 2) ^ ((a : ℕ) * (b : ℕ)) * ρ i ^ (((a + b : Fin 2) : ℕ)) := by
      intro a b; fin_cases a <;> fin_cases b <;> simp
    rw [hkey (ε i) (δ i)]
    simp only [Pi.add_apply]
  rw [Finset.prod_congr rfl (fun i _ => key i)]
  rw [Finset.prod_mul_distrib]
  congr 1
  simp_rw [← map_pow]
  rw [← map_prod]

theorem Tfun_add {K : Type*} [Field K] {r : ℕ} (φ : K →+* ℂ) (ρ : Fin r → ℂ)
    (d d' : (Fin r → Fin 2) → K) :
    Tfun φ ρ (d + d') = Tfun φ ρ d + Tfun φ ρ d' := by
  unfold Tfun Bfun
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ε _
  rw [Pi.add_apply, map_add]
  ring

theorem Tfun_smul {K : Type*} [Field K] {r : ℕ} (φ : K →+* ℂ) (ρ : Fin r → ℂ)
    (c : K) (d : (Fin r → Fin 2) → K) :
    Tfun φ ρ (c • d) = φ c * Tfun φ ρ d := by
  unfold Tfun Bfun
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ε _
  rw [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

theorem Tfun_zero {K : Type*} [Field K] {r : ℕ} (φ : K →+* ℂ) (ρ : Fin r → ℂ) :
    Tfun φ ρ (0 : (Fin r → Fin 2) → K) = 0 := by
  unfold Tfun Bfun
  simp

theorem Tfun_neg {K : Type*} [Field K] {r : ℕ} (φ : K →+* ℂ) (ρ : Fin r → ℂ)
    (d : (Fin r → Fin 2) → K) : Tfun φ ρ (-d) = -Tfun φ ρ d := by
  have h : (-d : (Fin r → Fin 2) → K) = (-1 : K) • d := by
    funext ε; simp [Pi.smul_apply, Pi.neg_apply]
  rw [h, Tfun_smul]
  simp

theorem Tfun_sub {K : Type*} [Field K] {r : ℕ} (φ : K →+* ℂ) (ρ : Fin r → ℂ)
    (d d' : (Fin r → Fin 2) → K) :
    Tfun φ ρ (d - d') = Tfun φ ρ d - Tfun φ ρ d' := by
  rw [sub_eq_add_neg, Tfun_add, Tfun_neg, sub_eq_add_neg]

theorem Tfun_cMul {K : Type*} [Field K] {r : ℕ} (φ : K →+* ℂ) (η : Fin r → K)
    (ρ : Fin r → ℂ) (hρ : ∀ i, ρ i ^ 2 = φ (η i)) (d d' : (Fin r → Fin 2) → K) :
    Tfun φ ρ d * Tfun φ ρ d' = Tfun φ ρ (cMul η d d') := by
  have stepL : Tfun φ ρ d * Tfun φ ρ d'
      = ∑ p : (Fin r → Fin 2) × (Fin r → Fin 2),
          φ ((∏ i, η i ^ ((p.1 i : ℕ) * (p.2 i : ℕ))) * d p.1 * d' p.2) *
            Bfun ρ (p.1 + p.2) := by
    unfold Tfun
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun ε _ => ?_)
    refine Finset.sum_congr rfl (fun δ _ => ?_)
    calc (φ (d ε) * Bfun ρ ε) * (φ (d' δ) * Bfun ρ δ)
        = φ (d ε) * φ (d' δ) * (Bfun ρ ε * Bfun ρ δ) := by ring
      _ = φ (d ε) * φ (d' δ) * (φ (∏ i, η i ^ ((ε i : ℕ) * (δ i : ℕ))) * Bfun ρ (ε + δ)) := by
            rw [Bfun_mul φ η ρ hρ ε δ]
      _ = φ ((∏ i, η i ^ ((ε i : ℕ) * (δ i : ℕ))) * d ε * d' δ) * Bfun ρ (ε + δ) := by
            rw [map_mul, map_mul]; ring
  rw [stepL]
  unfold Tfun
  have hunfold : ∀ γ, cMul η d d' γ
      = ∑ p ∈ ((Finset.univ : Finset ((Fin r → Fin 2) × (Fin r → Fin 2))).filter
          (fun p => p.1 + p.2 = γ)),
          (∏ i, η i ^ ((p.1 i : ℕ) * (p.2 i : ℕ))) * d p.1 * d' p.2 := fun γ => rfl
  simp only [hunfold, map_sum]
  trans ∑ γ, ∑ p ∈ ((Finset.univ : Finset ((Fin r → Fin 2) × (Fin r → Fin 2))).filter
      (fun p => p.1 + p.2 = γ)),
        φ ((∏ i, η i ^ ((p.1 i : ℕ) * (p.2 i : ℕ))) * d p.1 * d' p.2) * Bfun ρ (p.1 + p.2)
  · rw [Finset.sum_fiberwise]
  · apply Finset.sum_congr rfl
    intro γ _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    rw [(Finset.mem_filter.mp hp).2]

/-! ### Support of `cMul`, and closure of `Supp` -/

theorem cMul_supp {K : Type*} [Field K] {r : ℕ} (η : Fin r → K) (i : Fin r)
    (d d' : (Fin r → Fin 2) → K) (vd vd' : Fin 2)
    (hd : Supp i vd d) (hd' : Supp i vd' d') :
    Supp i (vd + vd') (cMul η d d') := by
  intro γ hγ
  unfold cMul
  apply Finset.sum_eq_zero
  intro p hp
  have hp' : p.1 + p.2 = γ := (Finset.mem_filter.mp hp).2
  by_cases h1 : d p.1 = 0
  · rw [h1]; ring
  · have h1i : p.1 i = vd := by
      by_contra hc; exact h1 (hd p.1 hc)
    by_cases h2 : d' p.2 = 0
    · rw [h2]; ring
    · exfalso
      have h2i : p.2 i = vd' := by
        by_contra hc; exact h2 (hd' p.2 hc)
      apply hγ
      rw [← hp', Pi.add_apply, h1i, h2i]

theorem Supp.sub {K : Type*} [Field K] {r : ℕ} (i : Fin r) (v : Fin 2)
    {a b : (Fin r → Fin 2) → K} (ha : Supp i v a) (hb : Supp i v b) :
    Supp i v (a - b) := by
  intro ε hε
  rw [Pi.sub_apply, ha ε hε, hb ε hε, sub_zero]

theorem Supp.smul {K : Type*} [Field K] {r : ℕ} (i : Fin r) (v : Fin 2) (c : K)
    {a : (Fin r → Fin 2) → K} (ha : Supp i v a) : Supp i v (c • a) := by
  intro ε hε
  rw [Pi.smul_apply, ha ε hε, smul_zero]

/-- Functions supported on two distinct hyperplanes `{ε | ε i = v}` are zero. -/
theorem Supp_disjoint {K : Type*} [Field K] {r : ℕ} (i : Fin r) {v v' : Fin 2} (hvv : v ≠ v')
    {w : (Fin r → Fin 2) → K} (h0 : Supp i v w) (h1 : Supp i v' w) : w = 0 := by
  funext ε
  by_cases h : ε i = v
  · exact h1 ε (by rw [h]; exact hvv)
  · exact h0 ε h

/-! ### Evaluating `T` on a function supported at a single point -/

theorem Tfun_eq_single {K : Type*} [Field K] {r : ℕ} (φ : K →+* ℂ) (ρ : Fin r → ℂ)
    (d : (Fin r → Fin 2) → K) (γ : Fin r → Fin 2) (hd : ∀ ε, ε ≠ γ → d ε = 0) :
    Tfun φ ρ d = φ (d γ) * Bfun ρ γ := by
  unfold Tfun Bfun
  have : (∑ ε, φ (d ε) * ∏ i, ρ i ^ (ε i : ℕ))
      = ∑ ε ∈ Finset.univ,
          (if ε = γ then φ (d γ) * ∏ i, ρ i ^ (γ i : ℕ) else 0) := by
    apply Finset.sum_congr rfl
    intro ε _
    by_cases h : ε = γ
    · subst h; simp
    · simp [h, hd ε h]
  rw [this, Finset.sum_ite_eq']
  simp

/-- `T` of the "single coordinate" function `δ ↦ if δ = 0 then a0 else 0` is `φ a0`. -/
theorem Tfun_single {K : Type*} [Field K] {r : ℕ} (φ : K →+* ℂ) (ρ : Fin r → ℂ) (a0 : K) :
    Tfun φ ρ (fun ε : Fin r → Fin 2 => if ε = 0 then a0 else 0) = φ a0 := by
  have h0 : Bfun ρ (0 : Fin r → Fin 2) = 1 := by
    unfold Bfun; simp
  rw [Tfun_eq_single φ ρ _ (0 : Fin r → Fin 2)
      (by intro ε hε; simp [hε]), h0, mul_one]
  simp

/-- Squaring a product of square roots: `B_γ ^ 2 = φ (∏ i, η i ^ (γ i : ℕ))`. -/
theorem Bfun_sq {K : Type*} [Field K] {r : ℕ} (φ : K →+* ℂ) (η : Fin r → K)
    (ρ : Fin r → ℂ) (hρ : ∀ i, ρ i ^ 2 = φ (η i)) (γ : Fin r → Fin 2) :
    Bfun ρ γ ^ 2 = φ (∏ i, η i ^ (γ i : ℕ)) := by
  unfold Bfun
  rw [← Finset.prod_pow]
  have key : ∀ i : Fin r, (ρ i ^ (γ i : ℕ)) ^ 2 = φ (η i) ^ (γ i : ℕ) := by
    intro i
    rw [pow_swap_two, hρ i]
  rw [Finset.prod_congr rfl (fun i _ => key i)]
  simp_rw [← map_pow]
  rw [← map_prod]

end Work.BW
