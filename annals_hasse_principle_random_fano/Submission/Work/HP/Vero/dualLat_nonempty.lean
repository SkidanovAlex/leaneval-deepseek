import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero.SigmaDefs

/-!
# The dual lattice of `Γ_{x,y} = Λ_{ν₂(x)} ∩ Λ_{ν₂(y)}` is nonzero

For `n ≥ 2` and primitive, `ℤ`-linearly independent `x, y ∈ ℤ^{n+1}`, the dual lattice of the
realification of `Γ = Λ_{ν₂(x)} ∩ Λ_{ν₂(y)} ⊆ ℤ^{N_{2,n}}` contains a nonzero vector.

The argument is elementary and does not use primitivity or independence at all (they only enter via
the statement).  Two facts are needed.

* *A realified lattice is contained in its own dual.*  If `L = realify M` for an integral lattice
  `M`, then for `y = intCastPi c` with `c ∈ M` and `z = intCastPi d` with `d ∈ M` one has
  `∑ i, y i * z i = (∑ i, c i * d i : ℤ)`, an integer.  So every element of `L` is in `dualLat L`.

* *`Γ` is nonzero.*  Choose `u ≠ 0` with `⟨u,x⟩ = 0` and `v ≠ 0` with `⟨v,y⟩ = 0` (possible since
  `x, y ≠ 0` and `n + 1 ≥ 3`), and let `a = σ(u,v)` be the coefficient vector of the quadratic form
  `t ↦ ⟨t,u⟩⟨t,v⟩`.  By `dot_veronese_sigma`, `⟨ν(z), a⟩ = ⟨z,u⟩⟨z,v⟩`, which vanishes for `z = x`
  and `z = y`, so `a ∈ Γ`.  And `a ≠ 0`: if `σ(u,v) = 0` then evaluating at `z = u` gives
  `⟨u,v⟩ = 0` (as `⟨u,u⟩ ≠ 0`), and evaluating at `z = u + v` gives `⟨u,u⟩⟨v,v⟩ = 0`, contradicting
  `u, v ≠ 0`.

Since `intCastPi a ∈ realify Γ ⊆ dualLat (realify Γ)` and `intCastPi a ≠ 0`, the result follows.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace Work.HP.Vero

open Work.HP

/-! ## A realified lattice is contained in its own dual -/

/-- Every element of `realify M ⊆ ℝ^ι` pairs integrally with every element of `realify M`, and lies in
the real span of `realify M`; hence `realify M ≤ dualLat (realify M)`. -/
lemma realify_le_dualLat {ι : Type*} [Fintype ι] (M : Submodule ℤ (ι → ℤ)) :
    realify M ≤ dualLat (realify M) := by
  intro y hy
  obtain ⟨cy, hcy, hcy_eq⟩ := Submodule.mem_map.mp hy
  refine ⟨Submodule.subset_span hy, fun z hz => ?_⟩
  obtain ⟨cz, hcz, hcz_eq⟩ := Submodule.mem_map.mp hz
  refine ⟨∑ i, cy i * cz i, ?_⟩
  rw [← hcy_eq, ← hcz_eq]
  simp only [intCastPi_apply]
  push_cast
  rfl

/-! ## Positivity of a sum of squares over `ℤ` -/

/-- If `u ≠ 0` then `∑ i, u i * u i ≠ 0`. -/
lemma sum_mul_self_ne_zero {ι : Type*} [Fintype ι] {u : ι → ℤ} (hu : u ≠ 0) :
    (∑ i, u i * u i) ≠ 0 := by
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hu
  intro hsum
  have hle : u k * u k ≤ ∑ i, u i * u i :=
    Finset.single_le_sum (fun i _ => mul_self_nonneg (u i)) (Finset.mem_univ k)
  rw [hsum] at hle
  have hpos : 0 < u k * u k := mul_self_pos.mpr hk
  linarith

/-- Pairing against a single-coordinate vector. -/
lemma sum_single_mul_int {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι) (c : ℤ) (f : ι → ℤ) :
    ∑ i, (Pi.single a c : ι → ℤ) i * f i = c * f a := by
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb; rw [Pi.single_eq_of_ne hb, zero_mul]
  · intro h; exact absurd (Finset.mem_univ a) h

/-! ## A nonzero vector orthogonal to a nonzero vector -/

/-- For `n ≥ 2` and `x ≠ 0` there is a nonzero `u : Fin (n+1) → ℤ` with `⟨u,x⟩ = 0`.
If `x k ≠ 0` and `j ≠ k`, the vector `x j · e_k - x k · e_j` works. -/
lemma exists_ne_zero_orthogonal {n : ℕ} (hn : 2 ≤ n) {x : Fin (n+1) → ℤ} (hx : x ≠ 0) :
    ∃ u : Fin (n+1) → ℤ, u ≠ 0 ∧ ∑ i, u i * x i = 0 := by
  classical
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hx
  have hcard : 1 < Fintype.card (Fin (n+1)) := by simp only [Fintype.card_fin]; omega
  obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card hcard k
  refine ⟨(Pi.single k (x j) : Fin (n+1) → ℤ) + Pi.single j (-(x k)), ?_, ?_⟩
  · intro h
    have hh := congr_fun h j
    rw [Pi.add_apply, Pi.single_eq_of_ne hj, Pi.single_eq_same, zero_add, Pi.zero_apply] at hh
    exact hk (neg_eq_zero.mp hh)
  · simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, sum_single_mul_int]
    ring

/-! ## `σ(u,v)` is nonzero when `u, v ≠ 0` -/

/-- The coefficient vector `σ(u,v)` of `t ↦ ⟨t,u⟩⟨t,v⟩` is nonzero whenever `u ≠ 0` and `v ≠ 0`. -/
lemma sigma_ne_zero {n : ℕ} {u v : Fin (n+1) → ℤ} (hu : u ≠ 0) (hv : v ≠ 0) :
    sigma n u v ≠ 0 := by
  intro h
  -- For every `z`, the evaluation identity `dot_veronese_sigma` collapses to `⟨z,u⟩⟨z,v⟩ = 0`.
  have key : ∀ z : Fin (n+1) → ℤ, (∑ i, z i * u i) * (∑ j, z j * v j) = 0 := by
    intro z
    have hz := dot_veronese_sigma n z u v
    rw [h] at hz
    simpa using hz
  have huu : (∑ i, u i * u i) ≠ 0 := sum_mul_self_ne_zero hu
  have hvv : (∑ i, v i * v i) ≠ 0 := sum_mul_self_ne_zero hv
  -- Evaluating at `u` gives `⟨u,v⟩ = 0`.
  have huv : ∑ i, u i * v i = 0 := by
    have := key u
    exact (mul_eq_zero.mp this).resolve_left huu
  have hvu : ∑ i, v i * u i = 0 := by
    have h1 : ∑ i, v i * u i = ∑ i, u i * v i := Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    rw [h1, huv]
  have hsplit1 : ∑ i, (u i + v i) * u i = ∑ i, u i * u i + ∑ i, v i * u i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => add_mul _ _ _)
  have hsplit2 : ∑ j, (u j + v j) * v j = ∑ j, u j * v j + ∑ j, v j * v j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => add_mul _ _ _)
  -- Evaluating at `u + v` gives `⟨u,u⟩⟨v,v⟩ = 0`, a contradiction.
  have h3 := key (u + v)
  simp only [Pi.add_apply] at h3
  rw [hsplit1, hsplit2, hvu, huv, zero_add, add_zero] at h3
  exact (mul_eq_zero.mp h3).elim huu hvv

/-! ## The target -/

set_option linter.unusedVariables false in
theorem dualLat_nonempty {n : ℕ} (hn : 2 ≤ n) (x y : Fin (n + 1) → ℤ) (hx : IsPrim x)
    (hy : IsPrim y) (hxy : LinearIndependent ℤ ![x, y]) :
    ∃ a : Mon 2 n → ℝ, a ∈ dualLat (realify (Gam 2 n x y)) ∧ a ≠ 0 := by
  have hx0 : x ≠ 0 := by simpa using hxy.ne_zero 0
  have hy0 : y ≠ 0 := by simpa using hxy.ne_zero 1
  obtain ⟨u, hu_ne, hu_orth⟩ := exists_ne_zero_orthogonal hn hx0
  obtain ⟨v, hv_ne, hv_orth⟩ := exists_ne_zero_orthogonal hn hy0
  -- `σ(u,v)` vanishes at `x` and `y`, i.e. lies in `Γ`.
  have hux : ∑ i, x i * u i = 0 := by
    have h1 : ∑ i, x i * u i = ∑ i, u i * x i := Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    rw [h1, hu_orth]
  have hvy : ∑ i, y i * v i = 0 := by
    have h1 : ∑ i, y i * v i = ∑ i, v i * y i := Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    rw [h1, hv_orth]
  have hc_mem : sigma n u v ∈ Gam 2 n x y := by
    rw [Gam, Submodule.mem_inf]
    constructor
    · show sigma n u v ∈ latOrth (veronese 2 n x)
      rw [latOrth, LinearMap.mem_ker, Fintype.linearCombination_apply]
      simp only [smul_eq_mul]
      rw [show ∑ i, sigma n u v i * veronese 2 n x i = ∑ m, veronese 2 n x m * sigma n u v m from
            Finset.sum_congr rfl (fun i _ => mul_comm _ _),
          dot_veronese_sigma]
      simp [hux]
    · show sigma n u v ∈ latOrth (veronese 2 n y)
      rw [latOrth, LinearMap.mem_ker, Fintype.linearCombination_apply]
      simp only [smul_eq_mul]
      rw [show ∑ i, sigma n u v i * veronese 2 n y i = ∑ m, veronese 2 n y m * sigma n u v m from
            Finset.sum_congr rfl (fun i _ => mul_comm _ _),
          dot_veronese_sigma]
      simp [hvy]
  refine ⟨intCastPi (sigma n u v), ?_, ?_⟩
  · exact realify_le_dualLat (Gam 2 n x y)
      (Submodule.mem_map.mpr ⟨sigma n u v, hc_mem, rfl⟩)
  · intro h
    have hz : sigma n u v = 0 := by
      funext i
      have hi := congr_fun h i
      simp only [intCastPi_apply, Pi.zero_apply] at hi
      exact_mod_cast hi
    exact sigma_ne_zero hu_ne hv_ne hz

end Work.HP.Vero
