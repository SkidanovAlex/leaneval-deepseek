import Submission.ZagierHoffmanProof.AmbEll

/-!
# The multiple zeta value as an iterated Carlitz power sum (entries `≤ q`)

For tuple entries `≤ q` the per-degree power sum is *pure*: `P_d(n) = ℓ_d^{-n}`
(`StepL199.P_eq_pow_of_le_card` + `StepL195.Hsum_closed`).  Consequently the multiple zeta value
of such a tuple decomposes into the iterated (strictly decreasing) sum of the `ℓ_d`-powers:

  `ζ_A(s_0,…,s_{r-1}) = ∑'_{d_0} ℓ_{d_0}^{-s_0}·(∑_{d_1<d_0} ℓ_{d_1}^{-s_1}·(⋯))`,

the `K_∞`-counterpart of Dac's (4.2) with trivial `Γ`-factors.

The proof works level-wise on the block sums `S_d` of `PowerSum.lean`, using
`S_d_recursion` (`S_d = P_d(s_0)·S_{<d}`), `S_lt_eq_sum_levels` (`S_{<d} = ∑_{i<d} S_i`), the base
case `S_one_eq_P`, and the pure case `ambInfHom_P_eq_ambEll`.

## Main results

* `nestLvl` — the iterated power sum.
* ★★★ `ambInfHom_S_eq_nestLvl` — the level-wise identity.
* ★★★ `ambInfHom_zeta_A_eq_nestLvl` — the capstone.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Polynomial Finset
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## §1. The iterated power sum -/

/-- `nestLvl r 𝔰 d` is the sum of `∏_j ambEll(d_j)^{-(𝔰 j)}` over the strictly decreasing tuples
`d > d_0 > d_1 > ⋯ > d_{r-1} ≥ 0`. -/
noncomputable def nestLvl : (r : ℕ) → (Fin r → ℕ+) → ℕ → Ambient F
  | 0, _, _ => 1
  | (r + 1), 𝔰, d => ∑ i ∈ Finset.range d,
      (ambEll F i) ^ (-(𝔰 ⟨0, Nat.succ_pos r⟩ : ℤ))
        * nestLvl r (fun j : Fin r => 𝔰 ⟨j.1 + 1, by omega⟩) i

@[simp] lemma nestLvl_zero (𝔰 : Fin 0 → ℕ+) (d : ℕ) : nestLvl F 0 𝔰 d = 1 := rfl

lemma nestLvl_succ (r : ℕ) (𝔰 : Fin (r + 1) → ℕ+) (d : ℕ) :
    nestLvl F (r + 1) 𝔰 d = ∑ i ∈ Finset.range d,
      (ambEll F i) ^ (-(𝔰 ⟨0, Nat.succ_pos r⟩ : ℤ))
        * nestLvl F r (fun j : Fin r => 𝔰 ⟨j.1 + 1, by omega⟩) i :=
  rfl

/-! ## §2. The level-wise identity -/

/-- `ambInfHom` is additive over the finite level decomposition of `S_<d`. -/
lemma ambInfHom_S_lt (r : ℕ) (hr : 0 < r) (𝔰 : Fin r → ℕ+) (d : ℕ) :
    ambInfHom F (S_lt F r hr 𝔰 d)
      = ∑ i ∈ Finset.range d, ambInfHom F (S F r hr 𝔰 i) := by
  rw [S_lt_eq_sum_levels F r hr 𝔰 d, map_sum]

/-- ★★★ **The level-wise form of the MZV `↔` iterated power sum identity**: for `r + 1 ≥ 1`,
`ambInfHom (S_d(𝔰)) = ℓ_d^{-𝔰_0}·(the iterated sum over the tail)`. -/
theorem ambInfHom_S_eq_nestLvl (r : ℕ) (𝔰 : Fin (r + 1) → ℕ+)
    (h𝔰 : ∀ i, (𝔰 i : ℕ) ≤ Nat.card F) (d : ℕ) :
    ambInfHom F (S F (r + 1) (Nat.succ_pos r) 𝔰 d)
      = (ambEll F d) ^ (-(𝔰 ⟨0, Nat.succ_pos r⟩ : ℤ))
        * nestLvl F r (fun j : Fin r => 𝔰 ⟨j.1 + 1, by omega⟩) d := by
  induction r generalizing d with
  | zero =>
    rw [nestLvl_zero, mul_one, S_one_eq_P]
    exact ambInfHom_P_eq_ambEll F d (𝔰 0) (h𝔰 0)
  | succ r ih =>
    have hr : 1 < r + 1 + 1 := by omega
    have hr0 : 0 < r + 1 + 1 := by omega
    have hrT : 0 < r + 1 + 1 - 1 := by omega
    rw [S_d_recursion F (r + 1 + 1) hr hr0 hrT 𝔰 d, map_mul,
      ambInfHom_P_eq_ambEll F d (𝔰 ⟨0, hr0⟩) (h𝔰 ⟨0, hr0⟩), ambInfHom_S_lt,
      nestLvl_succ]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    exact ih (fun j : Fin (r + 1) => 𝔰 ⟨j.1 + 1, by omega⟩)
      (fun j => h𝔰 ⟨j.1 + 1, by omega⟩) i


/-! ## §3. The capstone -/

/-- ★★★ **The multiple zeta value of a tuple with all entries `≤ q` is the iterated sum of the
`ℓ`-powers** (the `K_∞`-side of Dac's (4.2) with trivial `Γ`-factors). -/
theorem ambInfHom_zeta_A_eq_nestLvl (r : ℕ) (𝔰 : Fin (r + 1) → ℕ+)
    (h𝔰 : ∀ i, (𝔰 i : ℕ) ≤ Nat.card F) :
    ambInfHom F (ζ_A F 𝔰)
      = ∑' d : ℕ, (ambEll F d) ^ (-(𝔰 0 : ℤ))
          * nestLvl F r (fun j : Fin r => 𝔰 ⟨j.1 + 1, by omega⟩) d := by
  have h := (summable_S F (Nat.succ_pos r) 𝔰).hasSum.map (ambInfHom F) (continuous_ambInfHom F)
  rw [← zeta_eq_tsum_block F (Nat.succ_pos r) 𝔰] at h
  rw [← h.tsum_eq]
  exact tsum_congr (fun d => ambInfHom_S_eq_nestLvl F r 𝔰 h𝔰 d)

end ZagierHoffmanPositiveChar
