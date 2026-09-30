import Mathlib
import ChallengeDeps
import Submission.Work.BW.kummer_state
import Submission.Work.BW.kummer_bh_cases
import Submission.Work.BW.BH_perm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Baker–Wüstholz §9: the Kummer reduction

See `Submission/Work/BW/kummer_state.lean` for the definitions (`KSt`, `Inv`, `hp`, `sig`) and the
descent step, and the main theorem `Work.BW.kummer_reduction` at the end of this file.
-/

namespace Work.BW

open Complex

variable {K : Type*} [Field K] [NumberField K]
variable {n : ℕ}


/-- The termination bound of BW §9: every state satisfying `Inv` has level bounded by
Minkowski's second inequality and the Lehmer bound. -/
theorem kummer_bound {φ : K →+* ℂ} {α : Fin n → K} (hn : 0 < n) (hα : ∀ i, α i ≠ 0)
    (hind : LinearIndependent ℚ (fun i => Complex.log (φ (α i))))
    (c' : ℝ) (hc' : 1 < c')
    (hLeh : ∀ (β : K) (ℓ : ℂ), β ≠ 0 → Complex.exp ℓ = φ β → ℓ ≠ 0 →
      1 < c' * max (Height.logHeight₁ β) ‖ℓ‖)
    {s : KSt K n} (hs : Inv φ α s) :
    (2:ℝ)^s.v ≤ ((n.factorial : ℝ)^2 / 2^(n-1)) * (c' * (Module.finrank ℚ K : ℝ))^n
      * ∏ i, hp φ (α i) := by
  obtain ⟨U, μ, hU, hμpos, hμdef, hμlow, hexp, hh, hprod⟩ :=
    kummer_minkowski_data hn hα hind c' hc' hLeh hs
  have hd : (0:ℝ) < (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
  have hcd : 0 < c' * (Module.finrank ℚ K : ℝ) := mul_pos (lt_trans zero_lt_one hc') hd
  have hlow : (1 / (c' * (Module.finrank ℚ K : ℝ)))^n ≤ ∏ j, μ j := by
    have h1 : ∏ _j : Fin n, (1 / (c' * (Module.finrank ℚ K : ℝ))) ≤ ∏ j : Fin n, μ j :=
      Finset.prod_le_prod₀ (fun j _ => by positivity) (fun j _ => le_of_lt (hμlow j))
    rwa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
  have h2 : (1 / (c' * (Module.finrank ℚ K : ℝ)))^n
      ≤ ((n.factorial : ℝ)^2 / 2^(n-1)) * (((2:ℝ)^s.v)⁻¹) * ∏ i, hp φ (α i) :=
    le_trans hlow hprod
  have h3 : 1 ≤ (c' * (Module.finrank ℚ K : ℝ))^n
      * (((n.factorial : ℝ)^2 / 2^(n-1)) * (((2:ℝ)^s.v)⁻¹) * ∏ i, hp φ (α i)) := by
    have h := mul_le_mul_of_nonneg_left h2 (le_of_lt (pow_pos hcd n))
    have h4 : (c' * (Module.finrank ℚ K : ℝ))^n * (1 / (c' * (Module.finrank ℚ K : ℝ)))^n = 1 := by
      rw [← mul_pow, mul_one_div, div_self (ne_of_gt hcd), one_pow]
    rw [h4] at h
    exact h
  have h4 : (2:ℝ)^s.v
      ≤ (2:ℝ)^s.v * ((c' * (Module.finrank ℚ K : ℝ))^n
        * (((n.factorial : ℝ)^2 / 2^(n-1)) * (((2:ℝ)^s.v)⁻¹) * ∏ i, hp φ (α i))) := by
    have h := mul_le_mul_of_nonneg_left h3 (by positivity : (0:ℝ) ≤ (2:ℝ)^s.v)
    simpa using h
  refine le_trans h4 (le_of_eq ?_)
  field_simp

/-- BW §9 in the sorted case: if `h'(α_1) ≤ ⋯ ≤ h'(α_n)` then the Kummer reduction terminates
with a state satisfying the basic hypothesis `BH` at `c = c'^n n!`. -/
theorem kummer_core (hn : 1 ≤ n) (φ : K →+* ℂ) (α : Fin n → K) (hα : ∀ i, α i ≠ 0)
    (hind : LinearIndependent ℚ (fun i => Complex.log (φ (α i))))
    (hsort : ∀ i j : Fin n, i ≤ j → hp φ (α i) ≤ hp φ (α j))
    (c' : ℝ) (hc' : 1 < c')
    (hLeh : ∀ (β : K) (ℓ : ℂ), β ≠ 0 → Complex.exp ℓ = φ β → ℓ ≠ 0 →
      1 < c' * max (Height.logHeight₁ β) ‖ℓ‖)
    (b : Fin n → ℤ) :
    ∃ (v : ℕ) (L : Fin n → Fin n → ℤ) (α' : Fin n → K) (σ : Fin n → ℝ),
      BH φ α b v (c' ^ n * n.factorial) n L α' σ := by
  classical
  have hn0 : 0 < n := hn
  -- one descent step, as a total function
  let next : KSt K n → KSt K n := fun s =>
    if KummerCond s.β then s
    else if h : ∃ s' : KSt K n, Inv φ α s' ∧ s'.v = s.v + 1 then Classical.choose h else s
  have hnext_of_not (s : KSt K n) (hs : Inv φ α s) (hK : ¬ KummerCond s.β) :
      Inv φ α (next s) ∧ (next s).v = s.v + 1 := by
    obtain ⟨s', hs', hv'⟩ := step_exists φ α hα hsort s hs hK
    have h : ∃ s' : KSt K n, Inv φ α s' ∧ s'.v = s.v + 1 := ⟨s', hs', hv'⟩
    simp only [next, hK, if_false, dif_pos h]
    exact Classical.choose_spec h
  have hnext_of (s : KSt K n) (hK : KummerCond s.β) : next s = s := by
    simp only [next, hK, if_true]
  let f : ℕ → KSt K n := fun k => Nat.rec (S0 α) (fun _ s => next s) k
  have hf_zero : f 0 = S0 α := rfl
  have hf_succ : ∀ k, f (k+1) = next (f k) := fun k => rfl
  have hf_inv : ∀ k, Inv φ α (f k) := by
    intro k
    induction k with
    | zero => rw [hf_zero]; exact inv_S0 φ α hα
    | succ k ih =>
        rw [hf_succ]
        by_cases hK : KummerCond (f k).β
        · rw [hnext_of _ hK]; exact ih
        · exact (hnext_of_not (f k) ih hK).1
  have hf_mono : ∀ k, ¬ KummerCond (f k).β → (f (k+1)).v = (f k).v + 1 := by
    intro k hK
    rw [hf_succ]
    exact (hnext_of_not (f k) (hf_inv k) hK).2
  -- the level bound
  set B : ℝ := ((n.factorial : ℝ)^2 / 2^(n-1)) * (c' * (Module.finrank ℚ K : ℝ))^n
      * ∏ i, hp φ (α i) with hBdef
  have hterm : ∀ k, (2:ℝ)^(f k).v ≤ B := fun k =>
    kummer_bound hn0 hα hind c' hc' hLeh (hf_inv k)
  set N : ℕ := ⌈B⌉₊ + 1 with hNdef
  -- the process stops
  have hstop : ∃ k ≤ N, KummerCond (f k).β := by
    by_contra hcon
    push_neg at hcon
    have hlev : ∀ k ≤ N, (f k).v = k := by
      intro k hk
      induction k with
      | zero => rw [hf_zero]; rfl
      | succ k ih =>
          have h1 : (f k).v = k := ih (Nat.le_of_succ_le hk)
          have h2 := hf_mono k (hcon k (Nat.le_of_succ_le hk))
          rw [h2, h1]
    have hlt := hterm N
    rw [hlev N le_rfl] at hlt
    have h1 : B ≤ (⌈B⌉₊ : ℝ) := Nat.le_ceil B
    have h2 : (⌈B⌉₊ : ℝ) < (N : ℝ) := by
      rw [hNdef]; push_cast; linarith
    have h3 : (N : ℝ) ≤ (2 : ℝ)^N := by
      exact_mod_cast le_of_lt (Nat.lt_two_pow_self (n := N))
    linarith
  obtain ⟨k, _hk, hK⟩ := hstop
  have hs : Inv φ α (f k) := hf_inv k
  by_cases hcase : (2:ℝ)^(f k).v ≤ c' ^ n * (n.factorial : ℝ)
  · obtain ⟨L, α', σ, hBH⟩ :=
      kummer_case1_state hn0 hα b hs hK (c' ^ n * (n.factorial : ℝ)) hcase
    exact ⟨(f k).v, L, α', σ, hBH⟩
  · obtain ⟨L, α', σ, hBH⟩ :=
      kummer_case2_state hn0 hα hind c' hc' hLeh b hs hK (not_le.mp hcase)
    exact ⟨(f k).v, L, α', σ, hBH⟩

/-- BW §9: from `ℚ`-independent principal logarithms and any Lehmer-type constant `c' > 1`,
build `v`, an invertible integer matrix `L`, and `α'_j ∈ K` with
`log α'_j = 2^{-v} L_j(log α)` satisfying the Kummer condition, i.e. the basic hypothesis
`BH` at `r = n` with `c = c'^n n!` (any `b`: the span condition is automatic). -/
theorem kummer_reduction {K : Type*} [Field K] [NumberField K] {n : ℕ} (hn : 1 ≤ n)
    (φ : K →+* ℂ) (α : Fin n → K) (hα : ∀ i, α i ≠ 0)
    (hind : LinearIndependent ℚ (fun i => Complex.log (φ (α i))))
    (c' : ℝ) (hc' : 1 < c')
    (hLeh : ∀ (β : K) (ℓ : ℂ), β ≠ 0 → Complex.exp ℓ = φ β → ℓ ≠ 0 →
      1 < c' * max (Height.logHeight₁ β) ‖ℓ‖)
    (b : Fin n → ℤ) :
    ∃ (v : ℕ) (L : Fin n → Fin n → ℤ) (α' : Fin n → K) (σ : Fin n → ℝ),
      BH φ α b v (c' ^ n * n.factorial) n L α' σ := by
  classical
  have hn0 : 0 < n := hn
  let π : Equiv.Perm (Fin n) := Tuple.sort (fun i => hp φ (α i))
  have hπ : ∀ i j : Fin n, i ≤ j → hp φ (α (π i)) ≤ hp φ (α (π j)) :=
    fun i j hij => Tuple.monotone_sort (fun i => hp φ (α i)) hij
  have hindπ : LinearIndependent ℚ (fun i => Complex.log (φ (α (π i)))) :=
    hind.comp π π.injective
  obtain ⟨v, L, α', σ, hBH⟩ :=
    kummer_core hn φ (fun i => α (π i)) (fun i => hα (π i)) hindπ hπ c' hc' hLeh b
  exact ⟨v, fun j i => L j (π.symm i), α', σ, BH_perm φ α b v _ L α' σ π hBH⟩

end Work.BW
