/-
# Higman's Lemma 12: the case analysis in canonical coordinates

This file performs the *arithmetic* part of the case analysis of Higman's Lemma 12
(Higman, *Suzuki 2-groups*, Illinois J. Math. **7** (1963), 90--92), in the canonical form of the
pinned squaring form.

The pinned data (`Work.Higman.Q3.L12.pinned_form_axis_type`) gives additive coordinates in which
the squaring form is

    Q (α, β) = C * α ^ a + C' * β ^ a' + ∑_{k,l < n} e k l * α ^ (2 ^ k) * β ^ (2 ^ l),

with `ν ^ a = ν' ^ (a') = lam`, `ν, ν', lam` of order `2 ^ n - 1`, and the resonance
`e k l ≠ 0 → ν ^ (2 ^ k) * ν' ^ (2 ^ l) = lam`.

After the normalisation `(α, β) ↦ (α ^ (2 ^ t), β ^ (2 ^ u))` of `Q3/L12/dispatch.lean`, which
sends the diagonal into `C α ^ (1 + 2 ^ r) + C' β ^ (1 + 2 ^ s)`, the resonance becomes the pure
congruence

    (★)     g k l ≠ 0  →  (1 + 2 ^ s) * 2 ^ k + (1 + 2 ^ r) * 2 ^ l ≡ (1 + 2 ^ r) * (1 + 2 ^ s)

modulo `2 ^ n - 1`.  This file classifies all solutions of (★) (using
`res_ab_ab`, `res_rr`, `res_r_ab`, `d_case_congruence`) and infers the `B`/`C`/`D` normal form
from `reduce_ab_ab`, `reduce_r_r`, `reduce_ab_r`, `reduce_r_s`.

* `r = s = 0`: `B` (both axes abelian),
* `r = s ≠ 0`: `B(n, frob ^ r, ε)`,
* `r ≠ 0 = s`: `C`,
* `r, s ≠ 0`, `r ≢ ± s`: `D(n, frob ^ r, ε)`.
-/

import Mathlib
import Submission.Work.Higman.Q3.Defs
import Submission.Work.Higman.Family
import Submission.Work.Higman.family_anisotropic
import Submission.Work.Higman.Q3.reduce_ab_ab
import Submission.Work.Higman.Q3.reduce_ab_r
import Submission.Work.Higman.Q3.reduce_r_r
import Submission.Work.Higman.Q3.reduce_r_s
import Submission.Work.Higman.Q3.L12.res_ab_ab
import Submission.Work.Higman.Q3.L12.res_rr
import Submission.Work.Higman.Q3.L12.res_r_ab
import Submission.Work.Higman.Q3.L12.d_case_congruence
import Submission.Work.Higman.Q3.L12.c_case_congruence
import Submission.Work.Higman.Q3.L12.epsilon_B_of_anisotropic
import Submission.Work.Higman.Q3.L12.epsilon_C_of_anisotropic
import Submission.Work.Higman.gcd_two_pow
import Submission.Work.Higman.orderOf_frobeniusEquiv_pow

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Work.Higman.Q3.L12

open Work.Higman

open scoped BigOperators

/-- **The three Higman normal forms** for a squaring form `Q : 𝔽_{2ⁿ} × 𝔽_{2ⁿ} → 𝔽_{2ⁿ}`:
there are additive coordinate changes `Φ`, `Ψ` and data `θ`, `ε` with
`Ψ (Q (Φ v))` the squaring form of `bCocycle`, `cCocycle` or `dCocycle`, with the Column-III
conditions on `ε` and `Odd (orderOf θ)`. -/
def Good (n : ℕ) (Q : GaloisField 2 n × GaloisField 2 n → GaloisField 2 n) : Prop :=
  ∃ (θ : GaloisField 2 n ≃+* GaloisField 2 n) (ε : GaloisField 2 n)
    (Φ : GaloisField 2 n × GaloisField 2 n ≃+ GaloisField 2 n × GaloisField 2 n)
    (Ψ : GaloisField 2 n ≃+ GaloisField 2 n),
    Odd (orderOf θ) ∧
    ((ε ≠ 0 ∧ (∀ ρ : GaloisField 2 n, ε ≠ ρ⁻¹ + θ ρ) ∧
        ∀ v : GaloisField 2 n × GaloisField 2 n,
          Ψ (Q (Φ v)) = bCocycle (GaloisField 2 n) θ ε v v)
      ∨ ((∀ a : GaloisField 2 n, (θ (θ a)) ^ 2 = a) ∧
          (∀ ρ : GaloisField 2 n, ε ≠ ρ⁻¹ + θ ρ ^ 2 * ρ) ∧
          ∀ v : GaloisField 2 n × GaloisField 2 n,
            Ψ (Q (Φ v)) = cCocycle (GaloisField 2 n) θ ε v v)
      ∨ (θ ^ 5 = 1 ∧ θ ≠ RingEquiv.refl _ ∧ 5 ∣ n ∧
          (∀ ρ : GaloisField 2 n, ε ≠ ρ⁻¹ + θ (θ (θ (θ ρ))) * θ ρ * ρ⁻¹) ∧
          ∀ v : GaloisField 2 n × GaloisField 2 n,
            Ψ (Q (Φ v)) = dCocycle (GaloisField 2 n) θ ε v v))

variable {n : ℕ}

/-- Anisotropy transfers through an identification `Ψ (Q (Φ v)) = W v`. -/
lemma aniso_transfer {Q W : GaloisField 2 n × GaloisField 2 n → GaloisField 2 n}
    {Φ : GaloisField 2 n × GaloisField 2 n ≃+ GaloisField 2 n × GaloisField 2 n}
    {Ψ : GaloisField 2 n ≃+ GaloisField 2 n}
    (h : ∀ v, Ψ (Q (Φ v)) = W v) (hani : ∀ v, v ≠ 0 → Q v ≠ 0) :
    ∀ v, v ≠ 0 → W v ≠ 0 := by
  intro v hv h0
  have h1 : Q (Φ v) = 0 := Ψ.injective (by rw [h v, h0, map_zero])
  exact hani (Φ v) (fun h2 => hv (Φ.injective (by rw [h2, map_zero]))) h1

/-- `Q (Φ ·)` is anisotropic when `Q` is. -/
lemma aniso_comp {Q : GaloisField 2 n × GaloisField 2 n → GaloisField 2 n}
    (hani : ∀ v, v ≠ 0 → Q v ≠ 0)
    {Φ : GaloisField 2 n × GaloisField 2 n ≃+ GaloisField 2 n × GaloisField 2 n} :
    ∀ v, v ≠ 0 → Q (Φ v) ≠ 0 := by
  intro v hv h0
  exact hani (Φ v) (fun h2 => hv (Φ.injective (by rw [h2, map_zero]))) h0

/-- Collapsing a double sum whose support is contained in a single point `(k₀, l₀)`. -/
lemma sum_single {n : ℕ} {k₀ l₀ : ℕ} (hk₀ : k₀ < n) (hl₀ : l₀ < n)
    {g : ℕ → ℕ → GaloisField 2 n}
    (h : ∀ k l, k < n → l < n → g k l ≠ 0 → k = k₀ ∧ l = l₀) (α β : GaloisField 2 n) :
    (∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, g k l * α ^ (2 ^ k) * β ^ (2 ^ l))
      = g k₀ l₀ * α ^ (2 ^ k₀) * β ^ (2 ^ l₀) := by
  have hf : ∀ k ∈ Finset.range n, k ∉ ({k₀} : Finset ℕ) →
      (∑ l ∈ Finset.range n, g k l * α ^ (2 ^ k) * β ^ (2 ^ l)) = 0 := by
    intro k hk hk'
    rw [Finset.mem_singleton] at hk'
    refine Finset.sum_eq_zero (fun l hl => ?_)
    have hl' : l < n := Finset.mem_range.mp hl
    have hg : g k l = 0 := by
      by_contra hne
      exact hk' (h k l (Finset.mem_range.mp hk) hl' hne).1
    rw [hg, zero_mul, zero_mul]
  rw [← Finset.sum_subset (Finset.singleton_subset_iff.mpr (Finset.mem_range.mpr hk₀)) hf,
    Finset.sum_singleton]
  refine Finset.sum_eq_single l₀ (fun l hl hl' => ?_)
    (fun hmem => absurd (Finset.mem_range.mpr hl₀) hmem)
  have hl'2 : l < n := Finset.mem_range.mp hl
  have hg : g k₀ l = 0 := by
    by_contra hne
    exact hl' (h k₀ l hk₀ hl'2 hne).2
  rw [hg, zero_mul, zero_mul]

/-- Collapsing a double sum whose support is contained in two points
`(k₁, l₁)`, `(k₂, l₂)` with `k₁ ≠ k₂`. -/
lemma sum_pair {n : ℕ} {k₁ l₁ k₂ l₂ : ℕ} (hk₁ : k₁ < n) (hk₂ : k₂ < n)
    (hl₁ : l₁ < n) (hl₂ : l₂ < n) (hne : k₁ ≠ k₂)
    {g : ℕ → ℕ → GaloisField 2 n}
    (h : ∀ k l, k < n → l < n → g k l ≠ 0 → (k = k₁ ∧ l = l₁) ∨ (k = k₂ ∧ l = l₂))
    (α β : GaloisField 2 n) :
    (∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, g k l * α ^ (2 ^ k) * β ^ (2 ^ l))
      = g k₁ l₁ * α ^ (2 ^ k₁) * β ^ (2 ^ l₁)
        + g k₂ l₂ * α ^ (2 ^ k₂) * β ^ (2 ^ l₂) := by
  have hf : ∀ k ∈ Finset.range n, k ∉ ({k₁, k₂} : Finset ℕ) →
      (∑ l ∈ Finset.range n, g k l * α ^ (2 ^ k) * β ^ (2 ^ l)) = 0 := by
    intro k hk hk'
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk'
    refine Finset.sum_eq_zero (fun l hl => ?_)
    have hl' : l < n := Finset.mem_range.mp hl
    have hg : g k l = 0 := by
      by_contra hne2
      rcases h k l (Finset.mem_range.mp hk) hl' hne2 with ⟨he, -⟩ | ⟨he, -⟩
      · exact hk'.1 he
      · exact hk'.2 he
    rw [hg, zero_mul, zero_mul]
  have hsub : ({k₁, k₂} : Finset ℕ) ⊆ Finset.range n := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_range.mpr hk₁
    · exact Finset.mem_range.mpr hk₂
  have h1 : (∑ l ∈ Finset.range n, g k₁ l * α ^ (2 ^ k₁) * β ^ (2 ^ l))
      = g k₁ l₁ * α ^ (2 ^ k₁) * β ^ (2 ^ l₁) := by
    refine Finset.sum_eq_single l₁ (fun l hl hl' => ?_)
      (fun hmem => absurd (Finset.mem_range.mpr hl₁) hmem)
    have hl'2 : l < n := Finset.mem_range.mp hl
    have hg : g k₁ l = 0 := by
      by_contra hne2
      rcases h k₁ l hk₁ hl'2 hne2 with ⟨-, he⟩ | ⟨he, -⟩
      · exact hl' he
      · exact absurd he hne
    rw [hg, zero_mul, zero_mul]
  have h2 : (∑ l ∈ Finset.range n, g k₂ l * α ^ (2 ^ k₂) * β ^ (2 ^ l))
      = g k₂ l₂ * α ^ (2 ^ k₂) * β ^ (2 ^ l₂) := by
    refine Finset.sum_eq_single l₂ (fun l hl hl' => ?_)
      (fun hmem => absurd (Finset.mem_range.mpr hl₂) hmem)
    have hl'2 : l < n := Finset.mem_range.mp hl
    have hg : g k₂ l = 0 := by
      by_contra hne2
      rcases h k₂ l hk₂ hl'2 hne2 with ⟨he, -⟩ | ⟨-, he⟩
      · exact absurd he (Ne.symm hne)
      · exact hl' he
    rw [hg, zero_mul, zero_mul]
  rw [← Finset.sum_subset hsub hf, Finset.sum_pair hne, h1, h2]

/-! ## Auxiliary arithmetic -/

/-- `x * x ^ (2 ^ r) = x ^ (1 + 2 ^ r)`. -/
lemma mul_pow_two_pow_eq {n r : ℕ} (x : GaloisField 2 n) :
    x * x ^ (2 ^ r) = x ^ (1 + 2 ^ r) :=
  calc x * x ^ (2 ^ r) = x ^ 1 * x ^ (2 ^ r) := by rw [pow_one]
    _ = x ^ (1 + 2 ^ r) := by rw [← pow_add]

/-- Cancelling a factor `2` in a congruence modulo the odd number `2 ^ n - 1`. -/
lemma modEq_cancel_two {n : ℕ} (hn : 0 < n) {a b : ℕ}
    (h : 2 * a ≡ 2 * b [MOD 2 ^ n - 1]) : a ≡ b [MOD 2 ^ n - 1] := by
  have hM : (2 ^ n - 1).gcd 2 = 1 := Nat.coprime_two_right.mpr (odd_two_pow_sub_one hn)
  have h2 : 0 < 2 ^ n - 1 := by
    have h3 : 2 ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have h3 := Nat.ModEq.cancel_left_div_gcd (m := 2 ^ n - 1) (c := 2) h2 h
  rwa [hM, Nat.div_one] at h3

/-- `x ^ ((2 ^ n) ^ k) = x` in `𝔽_{2 ^ n}`. -/
lemma pow_pow_card {n : ℕ} (hn : 1 ≤ n) (x : GaloisField 2 n) (k : ℕ) :
    x ^ ((2 ^ n) ^ k) = x := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_mul, ih, pow_two_pow_card hn x]

/-- Reducing the exponent `2 ^ a` modulo `2 ^ n - 1`. -/
lemma pow_two_pow_mod {n : ℕ} (hn : 1 ≤ n) (x : GaloisField 2 n) (a : ℕ) :
    x ^ (2 ^ a) = x ^ (2 ^ (a % n)) := by
  have h : 2 ^ a = (2 ^ n) ^ (a / n) * 2 ^ (a % n) := by
    conv_lhs => rw [← Nat.div_add_mod a n]
    rw [pow_add, pow_mul]
  rw [h, pow_mul, pow_pow_card hn x (a / n)]

/-! ## The four cases of (★) -/

/-- **Case `r = s = 0`** (both axes abelian): the support of the squaring form is `{(0,0)}` and
`reduce_ab_ab` brings it to the `B` form with `θ = 1`. -/
theorem case_B_ab {n : ℕ} (hn : 2 ≤ n) {C C' : GaloisField 2 n} (hC : C ≠ 0) (hC' : C' ≠ 0)
    {g : ℕ → ℕ → GaloisField 2 n}
    (Q : GaloisField 2 n × GaloisField 2 n → GaloisField 2 n)
    (hQ : ∀ α β : GaloisField 2 n, Q (α, β) = C * α ^ (1 + 2 ^ 0) + C' * β ^ (1 + 2 ^ 0) +
        ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, g k l * α ^ (2 ^ k) * β ^ (2 ^ l))
    (hani : ∀ v : GaloisField 2 n × GaloisField 2 n, v ≠ 0 → Q v ≠ 0)
    (hres : ∀ k l : ℕ, k < n → l < n → g k l ≠ 0 →
        (1 + 2 ^ 0) * 2 ^ k + (1 + 2 ^ 0) * 2 ^ l ≡ (1 + 2 ^ 0) * (1 + 2 ^ 0)
          [MOD 2 ^ n - 1]) :
    Good n Q := by
  have hn1 : 0 < n := by omega
  have hsup : ∀ k l : ℕ, k < n → l < n → g k l ≠ 0 → k = 0 ∧ l = 0 := by
    intro k l hk hl hg
    refine res_ab_ab hn hk hl ?_
    have h := hres k l hk hl hg
    norm_num at h
    rw [← mul_add] at h
    exact modEq_cancel_two hn1 h
  have hQ' : ∀ α β : GaloisField 2 n, Q (α, β) = C * α ^ 2 + C' * β ^ 2 + g 0 0 * α * β := by
    intro α β
    rw [hQ α β, sum_single (by omega) (by omega) hsup α β]
    norm_num
  obtain ⟨Φ, Ψ, ε, hΦΨ⟩ :=
    reduce_ab_ab (n := n) (hn := by omega) (C := C) (C' := C') (f := g 0 0)
      (i := 1) (j := 1) hC hC' (by omega) (by omega)
  have hkey : ∀ v : GaloisField 2 n × GaloisField 2 n,
      Ψ (Q (Φ v)) = bCocycle (GaloisField 2 n) (RingEquiv.refl (GaloisField 2 n)) ε v v := by
    intro v
    rw [hQ']
    have h := hΦΨ v
    simp only [Nat.add_sub_cancel_left, Nat.mod_self, pow_one, pow_zero] at h
    simp only [bCocycle, RingEquiv.refl_apply]
    rw [h]
    ring
  have haniB : ∀ u : GaloisField 2 n × GaloisField 2 n, u ≠ 0 →
      bCocycle (GaloisField 2 n) (RingEquiv.refl (GaloisField 2 n)) ε u u ≠ 0 :=
    aniso_transfer hkey hani
  have hε := epsilon_B_of_anisotropic (RingEquiv.refl (GaloisField 2 n)) ε haniB
  have hodd : Odd (orderOf (RingEquiv.refl (GaloisField 2 n))) := by
    have : (RingEquiv.refl (GaloisField 2 n) : GaloisField 2 n ≃+* GaloisField 2 n) = 1 := rfl
    rw [this, orderOf_one]
    exact odd_one
  exact ⟨_, ε, Φ, Ψ, hodd, Or.inl ⟨hε.1, hε.2, hkey⟩⟩

/-- **Case `r = s ≠ 0`** (both axes of the same non-abelian type `r`): the support is
`{(0,r), (r,0)}` and `reduce_r_r` brings the form to `B(n, frob ^ r, ε)`. -/
theorem case_B_r {n r : ℕ} (hn : 2 ≤ n) (hr : r < n) (hr0 : r ≠ 0)
    (hcop : Nat.Coprime (1 + 2 ^ r) (2 ^ n - 1))
    {C C' : GaloisField 2 n} (hC : C ≠ 0) (hC' : C' ≠ 0)
    {g : ℕ → ℕ → GaloisField 2 n}
    (Q : GaloisField 2 n × GaloisField 2 n → GaloisField 2 n)
    (hQ : ∀ α β : GaloisField 2 n, Q (α, β) = C * α ^ (1 + 2 ^ r) + C' * β ^ (1 + 2 ^ r) +
        ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, g k l * α ^ (2 ^ k) * β ^ (2 ^ l))
    (hani : ∀ v : GaloisField 2 n × GaloisField 2 n, v ≠ 0 → Q v ≠ 0)
    (hres : ∀ k l : ℕ, k < n → l < n → g k l ≠ 0 →
        (1 + 2 ^ r) * 2 ^ k + (1 + 2 ^ r) * 2 ^ l ≡ (1 + 2 ^ r) * (1 + 2 ^ r)
          [MOD 2 ^ n - 1]) :
    Good n Q := by
  have hn1 : 0 < n := by omega
  have hsup : ∀ k l : ℕ, k < n → l < n → g k l ≠ 0 →
      (k = 0 ∧ l = r) ∨ (k = r ∧ l = 0) := by
    intro k l hk hl hg
    refine res_rr hn1 hr hr0 hk hl hcop ?_
    have h := hres k l hk hl hg
    simpa only [mul_comm ((1 : ℕ) + 2 ^ r) (2 ^ k), mul_comm ((1 : ℕ) + 2 ^ r) (2 ^ l)] using h
  have hQ' : ∀ α β : GaloisField 2 n, Q (α, β) = C * α ^ (1 + 2 ^ r) + C' * β ^ (1 + 2 ^ r) +
      (g 0 r * α * β ^ (2 ^ r) + g r 0 * α ^ (2 ^ r) * β) := by
    intro α β
    rw [hQ α β, sum_pair (n := n) (k₁ := 0) (l₁ := r) (k₂ := r) (l₂ := 0)
      (by omega) hr (by omega) (by omega) (Ne.symm hr0) hsup α β]
    simp
  obtain ⟨Φ, Ψ, ε, hΦΨ⟩ :=
    reduce_r_r (n := n) (hn := by omega) (r := r) (by omega) hr hcop (C := C) (C' := C')
      (f1 := g 0 r) (f2 := g r 0) hC hC' (fun v hv => by
        have h := hani v hv
        rw [hQ' v.1 v.2] at h
        simpa only [add_assoc] using h)
  have hkey : ∀ v : GaloisField 2 n × GaloisField 2 n,
      Ψ (Q (Φ v)) = bCocycle (GaloisField 2 n)
        ((frob n ^ r : GaloisField 2 n ≃+* GaloisField 2 n)) ε v v := by
    intro v
    have h1 : Ψ (Q (Φ v)) = v.1 ^ (1 + 2 ^ r) + ε * (v.1 * v.2 ^ (2 ^ r)) +
        v.2 ^ (1 + 2 ^ r) := by
      rw [hQ']
      have h := hΦΨ v
      simp only [add_assoc, mul_assoc] at h ⊢
      exact h
    rw [h1]
    simp only [bCocycle, frob_pow_apply]
    rw [mul_pow_two_pow_eq v.1, mul_pow_two_pow_eq v.2]
  have haniB : ∀ u : GaloisField 2 n × GaloisField 2 n, u ≠ 0 →
      bCocycle (GaloisField 2 n) ((frob n ^ r : GaloisField 2 n ≃+* GaloisField 2 n))
        ε u u ≠ 0 := aniso_transfer hkey hani
  have hε := epsilon_B_of_anisotropic (frob n ^ r) ε haniB
  have hodd : Odd (orderOf (frob n ^ r)) := by
    rw [orderOf_frobeniusEquiv_pow n r (by omega)]
    refine (gcd_two_pow n r (by omega)).mp ?_
    rw [Nat.add_comm (2 ^ r) 1, Nat.gcd_comm]
    exact hcop
  exact ⟨_, ε, Φ, Ψ, hodd, Or.inl ⟨hε.1, hε.2, hkey⟩⟩

end Work.Higman.Q3.L12
