import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import ChallengeDeps
import Submission.KineticChild
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Cell cutoffs — the m³-grid partition of unity with quantified gradient

The bridge from the many-body IMS identity (`Submission.ManyBodyIMS`) to any
bracketing / box bound is an explicit partition of unity of the one-particle
cube `[0,L]³` into `m` cells per side: smooth cutoffs `χ_c` (one per cell
`c`) with

    Σ_c χ_c(y)² = 1           on the cube          (partition of unity), and
    Σ_c Σ_k (∂_k χ_c(y))² ≤ 3·C(ρ)/ℓ²   pointwise  (quantified error density),

where `ℓ = L/m` is the cell side.  Feeding these cutoffs into
`ManyBodyIMS.ims_pieces_le_whole_err` gives the explicit localization error
`(3·C(ρ)/ℓ²)·‖f‖²` for localizing a state.

This module develops the *abstract* construction, parameterised by a smooth
one-dimensional profile `ρ : ℝ → ℝ` with:

  * `hρ_supp`  — `ρ` vanishes off the open interval `(0,2)`;
  * `hρ_pu`    — two-term partition identity `ρ(θ)² + ρ(θ+1)² = 1`
                 for `θ ∈ [0,1]`  (the standard "shifted square" profile);
  * `hρ'_supp` — `ρ′` vanishes off `(0,2)` (flatness at the endpoints, so the
                 profile is smooth across the seams), and
  * a Lipschitz bound `|ρ′| ≤ A` for the quantified gradient estimate.

Concrete existence of such a profile (built from a flat smooth step, e.g. the
integral of a `ContDiffBump`) is a separate later piece.  Results:

  * the axis family `ξ_j(t) := ρ(t/ℓ + 1 − j)` for `j : Fin (m+2)` (the
    `m+2` overlapping cells covering `[0, m·ℓ]`, two ghost cells for the
    boundary), with:
  * `axis_support` — `ξ_j` is supported in `[(j−1)ℓ, (j+1)ℓ]`;
  * `axis_pu` — `Σ_j ξ_j(t)² = 1` on `[0, m·ℓ]` (exact partition of unity);
  * `axis_deriv` — the chain-rule derivative of `ξ_j`;
  * `axis_grad_sum_le` — `Σ_j (ξ_j′(t))² ≤ 2A²/ℓ²` on `[0, m·ℓ]`;
  * `axis_deriv_sq_pos`-style integrability helpers as needed.

The 3D cell family `χ_c` (product over the three coordinates of `ξ` for the
three axis-cells of `c`) and the resulting error-density bound
`Σ_c Σ_k (∂_k χ_c)² ≤ 3·2A²/ℓ²` are the immediate next piece.
-/

namespace Submission

open _root_.BoseGases
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

/-- The one-dimensional axis cell family: `m+2` overlapping cells of side `ℓ`
covering `[0, m·ℓ]` (with one ghost cell at each end). -/
noncomputable def axisFam (ρ : ℝ → ℝ) (ℓ : ℝ) (m : ℕ) (j : Fin (m + 2)) (t : ℝ) : ℝ :=
  ρ (t / ℓ + 1 - (j.val : ℝ))

/-- Support of the axis profile: `ξ_j` vanishes outside `[(j−1)ℓ, (j+1)ℓ]`. -/
lemma axis_support {ρ : ℝ → ℝ} (hρ_supp : ∀ t : ℝ, t ≤ 0 ∨ 2 ≤ t → ρ t = 0)
    {ℓ : ℝ} (hℓ : 0 < ℓ) {m : ℕ} (j : Fin (m + 2)) {t : ℝ}
    (ht : (axisFam ρ ℓ m j t) ≠ 0) :
    ((j.val : ℝ) - 1) * ℓ ≤ t ∧ t ≤ ((j.val : ℝ) + 1) * ℓ := by
  constructor
  · by_contra h
    have hlt : t < ((j.val : ℝ) - 1) * ℓ := lt_of_not_ge h
    have hdiv : t / ℓ < (j.val : ℝ) - 1 := by
      exact (div_lt_iff₀ hℓ).mpr hlt
    have harg : t / ℓ + 1 - (j.val : ℝ) < 0 := by linarith
    have hz : ρ (t / ℓ + 1 - (j.val : ℝ)) = 0 :=
      hρ_supp (t / ℓ + 1 - (j.val : ℝ)) (Or.inl (le_of_lt harg))
    exact ht (by simpa [axisFam] using hz)
  · by_contra h
    have hgt : ((j.val : ℝ) + 1) * ℓ < t := lt_of_not_ge h
    have hdiv : (j.val : ℝ) + 1 < t / ℓ := by
      exact (lt_div_iff₀ hℓ).mpr hgt
    have harg : 2 < t / ℓ + 1 - (j.val : ℝ) := by linarith
    have hz : ρ (t / ℓ + 1 - (j.val : ℝ)) = 0 :=
      hρ_supp (t / ℓ + 1 - (j.val : ℝ)) (Or.inr (le_of_lt harg))
    exact ht (by simpa [axisFam] using hz)


/-! ## Finite-sum and derivative helpers for the axis family -/

/-- A sum over `range (m+2)` collapses to the two terms at `k` and `k+1` when all
other terms vanish. -/
lemma range_pair_sum {m k : ℕ} (hkm : k ≤ m) {f : ℕ → ℝ}
    (hz : ∀ i : ℕ, i < m + 2 → i ≠ k → i ≠ k + 1 → f i = 0) :
    (∑ i ∈ Finset.range (m + 2), f i) = f k + f (k + 1) := by
  have hk_mem : k ∈ Finset.range (m + 2) := by
    simp [Finset.mem_range]
    omega
  have hk1_mem : k + 1 ∈ Finset.range (m + 2) := by
    simp [Finset.mem_range]
    omega
  let s := Finset.range (m + 2)
  have h1 : (∑ i ∈ s.erase (k + 1), f i) + f (k + 1) = ∑ i ∈ s, f i := by
    simpa [s] using (Finset.sum_erase_add s f hk1_mem)
  have h2 : (∑ i ∈ (s.erase (k + 1)).erase k, f i) + f k = ∑ i ∈ s.erase (k + 1), f i := by
    apply Finset.sum_erase_add
    simp [Finset.mem_erase]
    omega
  have hrem : ∑ i ∈ (s.erase (k + 1)).erase k, f i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hik : i ≠ k := (Finset.mem_erase.mp hi).1
    have hi2 : i ∈ s.erase (k + 1) := (Finset.mem_erase.mp hi).2
    have hik1 : i ≠ k + 1 := (Finset.mem_erase.mp hi2).1
    have hi_s : i ∈ s := (Finset.mem_erase.mp hi2).2
    exact hz i (by simpa [s] using hi_s) hik hik1
  calc
    (∑ i ∈ Finset.range (m + 2), f i) = ∑ i ∈ s, f i := rfl
    _ = (∑ i ∈ s.erase (k + 1), f i) + f (k + 1) := by rw [← h1]
    _ = ((∑ i ∈ (s.erase (k + 1)).erase k, f i) + f k) + f (k + 1) := by rw [← h2]
    _ = f k + f (k + 1) := by simp [hrem]

/-- On the grid `u + 1 − i` (`i = 0,…,m+1`) with `0 ≤ u ≤ m`, only the two indices
`⌊u⌋` and `⌊u⌋+1` can support `ρ`; every other term vanishes. -/
lemma axis_pair_collapse {ρ : ℝ → ℝ} (hkill : ∀ x : ℝ, x ≤ 0 ∨ 2 ≤ x → ρ x = 0)
    {m : ℕ} {u : ℝ} (hu0 : 0 ≤ u) (hum : u ≤ (m : ℝ)) :
    (∑ i ∈ Finset.range (m + 2), (ρ (u + 1 - (i : ℝ))) ^ 2) =
      (ρ (u + 1 - (Nat.floor u : ℝ))) ^ 2 + (ρ (u - (Nat.floor u : ℝ))) ^ 2 := by
  let k : ℕ := Nat.floor u
  have hku : (k : ℝ) ≤ u := by
    simpa [k] using Nat.floor_le hu0
  have huk : u < (k : ℝ) + 1 := by
    have hlt := (Nat.floor_lt hu0).1 (Nat.lt_succ_self (Nat.floor u))
    simpa [k] using hlt
  have hkm : k ≤ m := by
    have hmono : Nat.floor u ≤ Nat.floor (m : ℝ) := Nat.floor_mono hum
    simpa [k] using hmono
  have hz : ∀ i : ℕ, i < m + 2 → i ≠ k → i ≠ k + 1 → (ρ (u + 1 - (i : ℝ))) ^ 2 = 0 := by
    intro i hi_mem hi_k hi_k1
    have h : i < k ∨ k + 1 < i := by omega
    rcases h with hi_lt_k | hi_gt
    · have hi_le : (i : ℝ) + 1 ≤ (k : ℝ) := by
        have hn : i + 1 ≤ k := by omega
        exact_mod_cast hn
      have harg : 2 ≤ u + 1 - (i : ℝ) := by linarith
      simp [hkill (u + 1 - (i : ℝ)) (Or.inr harg)]
    · have hnat : k + 2 ≤ i := by omega
      have hi_ge : (k : ℝ) + 2 ≤ (i : ℝ) := by exact_mod_cast hnat
      have harg : u + 1 - (i : ℝ) < 0 := by linarith
      simp [hkill (u + 1 - (i : ℝ)) (Or.inl (le_of_lt harg))]
  calc
    (∑ i ∈ Finset.range (m + 2), (ρ (u + 1 - (i : ℝ))) ^ 2)
        = (ρ (u + 1 - (k : ℝ))) ^ 2 + (ρ (u + 1 - ((k + 1 : ℕ) : ℝ))) ^ 2 := by
          simpa using (range_pair_sum (m := m) (k := k) hkm hz)
    _ = (ρ (u + 1 - (k : ℝ))) ^ 2 + (ρ (u - (k : ℝ))) ^ 2 := by
          congr 1
          have h : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by norm_num
          rw [h]
          ring_nf
    _ = (ρ (u + 1 - (Nat.floor u : ℝ))) ^ 2 + (ρ (u - (Nat.floor u : ℝ))) ^ 2 := by
          simp [k]

/-- Derivative of a scalar multiple plus constant. -/
lemma deriv_affine (a b x : ℝ) : deriv (fun u : ℝ => a * u + b) x = a := by
  change deriv ((fun u : ℝ => a * u) + fun _ : ℝ => b) x = a
  rw [deriv_add]
  · have h1 : deriv (fun u : ℝ => a * u) x = a := by
      simp
    rw [h1]
    rw [deriv_const]
    ring_nf
  · fun_prop
  · fun_prop

/-- Chain rule for a composition with an invertible affine map, for an *arbitrary*
(not necessarily differentiable) profile: both sides vanish simultaneously when
`ρ` is not differentiable at the inner point. -/
lemma deriv_comp_affine {ρ : ℝ → ℝ} {a b : ℝ} (ha : a ≠ 0) (x : ℝ) :
    deriv (fun u : ℝ => ρ (a * u + b)) x = a * deriv ρ (a * x + b) := by
  by_cases hρ : DifferentiableAt ℝ ρ (a * x + b)
  · have hg_diff : DifferentiableAt ℝ (fun u : ℝ => a * u + b) x := by fun_prop
    have hdc := deriv_comp x hρ hg_diff
    have hdc' : deriv (fun u : ℝ => ρ (a * u + b)) x =
        deriv ρ (a * x + b) * deriv (fun u : ℝ => a * u + b) x := by
      simpa [Function.comp_def] using hdc
    rw [deriv_affine a b x] at hdc'
    rw [hdc']
    ring_nf
  · have hleft : deriv (fun u : ℝ => ρ (a * u + b)) x = 0 := by
      apply deriv_zero_of_not_differentiableAt
      intro hξ
      apply hρ
      let g0 : ℝ → ℝ := fun u => a * u + b
      let h : ℝ → ℝ := fun y => (y - b) / a
      have hh_x : h (a * x + b) = x := by
        simp [h]
        field_simp [ha]
      have hh_diff : DifferentiableAt ℝ h (a * x + b) := by fun_prop
      have hξ' : DifferentiableAt ℝ (ρ ∘ g0) x := by
        simpa [g0, Function.comp_def] using hξ
      have hres : DifferentiableAt ℝ ((ρ ∘ g0) ∘ h) (a * x + b) := by
        exact DifferentiableAt.comp (a * x + b) (by simpa [hh_x] using hξ') hh_diff
      have hfun : (ρ ∘ g0) ∘ h = ρ := by
        funext y
        simp [g0, h, Function.comp_def]
        congr 1
        field_simp [ha]
        ring_nf
      simpa [hfun] using hres
    rw [hleft]
    have hright : deriv ρ (a * x + b) = 0 := deriv_zero_of_not_differentiableAt hρ
    rw [hright]
    ring_nf

/-- The chain-rule identity `(ρ∘(·/ℓ+c))′ = (1/ℓ)·ρ′∘(·/ℓ+c)` without any regularity
assumption on `ρ` (both sides are zero when `ρ` is not differentiable inside). -/
lemma deriv_div_add_comp {ρ : ℝ → ℝ} {ℓ : ℝ} (hℓ0 : ℓ ≠ 0) (c x : ℝ) :
    deriv (fun u : ℝ => ρ (u / ℓ + c)) x = (1 / ℓ) * deriv ρ (x / ℓ + c) := by
  have hf : (fun u : ℝ => ρ (u / ℓ + c)) = (fun u : ℝ => ρ ((1 / ℓ) * u + c)) := by
    funext u
    have harg : u / ℓ + c = (1 / ℓ) * u + c := by
      rw [div_eq_mul_inv, one_div]
      ring_nf
    rw [harg]
  have h1ℓ : (1 : ℝ) / ℓ ≠ 0 := div_ne_zero (by norm_num : (1 : ℝ) ≠ 0) hℓ0
  have hda := deriv_comp_affine (ρ := ρ) (a := (1 : ℝ) / ℓ) (b := c) h1ℓ x
  calc
    deriv (fun u : ℝ => ρ (u / ℓ + c)) x
        = deriv (fun u : ℝ => ρ ((1 / ℓ) * u + c)) x := by rw [hf]
    _ = (1 / ℓ) * deriv ρ ((1 / ℓ) * x + c) := hda
    _ = (1 / ℓ) * deriv ρ (x / ℓ + c) := by
        have harg : (1 / ℓ) * x + c = x / ℓ + c := by
          rw [one_div, div_eq_mul_inv]
          ring_nf
        rw [harg]

/-- Exact partition of unity on `[0, m·ℓ]`: `Σ_{j<m+2} ξ_j(t)² = 1`. -/
lemma axis_pu {ρ : ℝ → ℝ} (hρ_supp : ∀ t : ℝ, t ≤ 0 ∨ 2 ≤ t → ρ t = 0)
    (hρ_pu : ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 → (ρ θ) ^ 2 + (ρ (θ + 1)) ^ 2 = 1)
    {ℓ : ℝ} (hℓ : 0 < ℓ) {m : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (htm : t ≤ (m : ℝ) * ℓ) :
    (∑ j : Fin (m + 2), (axisFam ρ ℓ m j t) ^ 2) = 1 := by
  let u : ℝ := t / ℓ
  have hu0 : 0 ≤ u := by
    dsimp [u]
    exact div_nonneg ht0 (le_of_lt hℓ)
  have hum : u ≤ (m : ℝ) := by
    dsimp [u]
    exact (div_le_iff₀ hℓ).mpr htm
  have hkill : ∀ x : ℝ, x ≤ 0 ∨ 2 ≤ x → ρ x = 0 := by
    intro x hx
    exact hρ_supp x hx
  have hmain : (∑ i ∈ Finset.range (m + 2), (ρ (u + 1 - (i : ℝ))) ^ 2) = 1 := by
    rw [axis_pair_collapse hkill hu0 hum]
    have hklo : (Nat.floor u : ℝ) ≤ u := Nat.floor_le hu0
    have hku_lt : u < (Nat.floor u : ℝ) + 1 := by
      have hlt := (Nat.floor_lt hu0).1 (Nat.lt_succ_self (Nat.floor u))
      simpa using hlt
    have hmem : u - (Nat.floor u : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> linarith
    have hpu := hρ_pu (u - (Nat.floor u : ℝ)) hmem
    have ha : (ρ (u + 1 - (Nat.floor u : ℝ))) ^ 2 = (ρ ((u - (Nat.floor u : ℝ)) + 1)) ^ 2 := by
      congr 1
      ring_nf
    calc
      (ρ (u + 1 - (Nat.floor u : ℝ))) ^ 2 + (ρ (u - (Nat.floor u : ℝ))) ^ 2
          = (ρ ((u - (Nat.floor u : ℝ)) + 1)) ^ 2 + (ρ (u - (Nat.floor u : ℝ))) ^ 2 := by
            rw [ha]
      _ = (ρ (u - (Nat.floor u : ℝ))) ^ 2 + (ρ ((u - (Nat.floor u : ℝ)) + 1)) ^ 2 := by ring
      _ = 1 := hpu
  calc
    (∑ j : Fin (m + 2), (axisFam ρ ℓ m j t) ^ 2)
        = (∑ j : Fin (m + 2), (ρ (u + 1 - (j.val : ℝ))) ^ 2) := by
          simp [axisFam, u]
    _ = (∑ i ∈ Finset.range (m + 2), (ρ (u + 1 - (i : ℝ))) ^ 2) := by
          simpa using (Fin.sum_univ_eq_sum_range (fun i : ℕ => (ρ (u + 1 - (i : ℝ))) ^ 2) (m + 2))
    _ = 1 := hmain

/-- The chain-rule derivative of the axis profile: `ξ_j′(t) = (1/ℓ)·ρ′(t/ℓ+1−j)`. -/
lemma axis_deriv {ρ : ℝ → ℝ} (hρ_cd : ContDiff ℝ 1 ρ)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (m : ℕ) (j : Fin (m + 2)) (t : ℝ) :
    deriv (fun u : ℝ => axisFam ρ ℓ m j u) t =
      (1 / ℓ) * deriv ρ (t / ℓ + 1 - (j.val : ℝ)) := by
  unfold axisFam
  have hf : (fun u : ℝ => ρ (u / ℓ + 1 - (j.val : ℝ))) =
      (fun u : ℝ => ρ (u / ℓ + (1 - (j.val : ℝ)))) := by
    funext u
    congr 1
    rw [div_eq_mul_inv]
    ring_nf
  rw [hf]
  have hd := deriv_div_add_comp (ρ := ρ) (hℓ0 := ne_of_gt hℓ) (1 - (j.val : ℝ)) t
  rw [hd]
  congr 1
  have harg : t / ℓ + (1 - (j.val : ℝ)) = t / ℓ + 1 - (j.val : ℝ) := by
    rw [div_eq_mul_inv]
    ring_nf
  rw [harg]

/-- Pointwise bound on the squared derivative of the axis profile:
`Σ_j (ξ_j′(t))² ≤ 2A²/ℓ²` on `[0, m·ℓ]`, when `|ρ′| ≤ A` and `ρ′` vanishes off
`(0,2)` (at most two cells overlap any point). -/
lemma axis_grad_sum_le {ρ : ℝ → ℝ} (hρ'_supp : ∀ t : ℝ, t ≤ 0 ∨ 2 ≤ t → deriv ρ t = 0)
    {A : ℝ} (hA0 : 0 ≤ A) (hA : ∀ t : ℝ, |deriv ρ t| ≤ A)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (m : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (htm : t ≤ (m : ℝ) * ℓ) :
    (∑ j : Fin (m + 2), (deriv (fun u : ℝ => axisFam ρ ℓ m j u) t) ^ 2) ≤
      (2 * A ^ 2) / ℓ ^ 2 := by
  let u : ℝ := t / ℓ
  have hℓ0 : ℓ ≠ 0 := ne_of_gt hℓ
  have hu0 : 0 ≤ u := by
    dsimp [u]
    exact div_nonneg ht0 (le_of_lt hℓ)
  have hum : u ≤ (m : ℝ) := by
    dsimp [u]
    exact (div_le_iff₀ hℓ).mpr htm
  let k : ℕ := Nat.floor u
  have hku : (k : ℝ) ≤ u := by
    simpa [k] using Nat.floor_le hu0
  have huk : u < (k : ℝ) + 1 := by
    have hlt := (Nat.floor_lt hu0).1 (Nat.lt_succ_self (Nat.floor u))
    simpa [k] using hlt
  have hkm : k ≤ m := by
    have hmono : Nat.floor u ≤ Nat.floor (m : ℝ) := Nat.floor_mono hum
    simpa [k] using hmono
  let d : ℕ → ℝ := fun i => deriv (fun w : ℝ => ρ (w / ℓ + 1 - (i : ℝ))) t
  have hd_formula : ∀ i : ℕ, d i = (1 / ℓ) * deriv ρ (u + 1 - (i : ℝ)) := by
    intro i
    unfold d
    have hdc := deriv_div_add_comp (ρ := ρ) (hℓ0 := hℓ0) (1 - (i : ℝ)) t
    have hf : (fun w : ℝ => ρ (w / ℓ + 1 - (i : ℝ))) =
        (fun w : ℝ => ρ (w / ℓ + (1 - (i : ℝ)))) := by
      funext w
      congr 1
      rw [div_eq_mul_inv]
      ring_nf
    rw [hf, hdc]
    congr 1
    have harg : t / ℓ + (1 - (i : ℝ)) = u + 1 - (i : ℝ) := by
      dsimp [u]
      rw [div_eq_mul_inv]
      ring_nf
    rw [harg]
  have hz_d : ∀ i : ℕ, i < m + 2 → i ≠ k → i ≠ k + 1 → d i = 0 := by
    intro i hi_mem hi_k hi_k1
    have h : i < k ∨ k + 1 < i := by omega
    have hdarg0 : deriv ρ (u + 1 - (i : ℝ)) = 0 := by
      rcases h with hi_lt_k | hi_gt
      · have hi_le : (i : ℝ) + 1 ≤ (k : ℝ) := by
          have hn : i + 1 ≤ k := by omega
          exact_mod_cast hn
        have harg : 2 ≤ u + 1 - (i : ℝ) := by linarith
        exact hρ'_supp (u + 1 - (i : ℝ)) (Or.inr harg)
      · have hnat : k + 2 ≤ i := by omega
        have hi_ge : (k : ℝ) + 2 ≤ (i : ℝ) := by exact_mod_cast hnat
        have harg : u + 1 - (i : ℝ) < 0 := by linarith
        exact hρ'_supp (u + 1 - (i : ℝ)) (Or.inl (le_of_lt harg))
    rw [hd_formula i, hdarg0]
    ring_nf
  have hz_e : ∀ i : ℕ, i < m + 2 → i ≠ k → i ≠ k + 1 → (d i) ^ 2 = 0 := by
    intro i hi hik hik1
    rw [hz_d i hi hik hik1]
    ring_nf
  have hcollapse : (∑ i ∈ Finset.range (m + 2), (d i) ^ 2) = (d k) ^ 2 + (d (k + 1)) ^ 2 := by
    exact range_pair_sum (m := m) (k := k) hkm hz_e
  have hd_bound : ∀ i : ℕ, |d i| ≤ A / ℓ := by
    intro i
    rw [hd_formula i]
    have hc : 0 ≤ 1 / ℓ := by positivity
    calc
      |(1 / ℓ) * deriv ρ (u + 1 - (i : ℝ))| = (1 / ℓ) * |deriv ρ (u + 1 - (i : ℝ))| := by
        rw [abs_mul, abs_of_nonneg hc]
      _ ≤ (1 / ℓ) * A := by
        exact mul_le_mul_of_nonneg_left (hA (u + 1 - (i : ℝ))) hc
      _ = A / ℓ := by
        rw [one_div, div_eq_mul_inv]
        ring_nf
  have hsq1 : (d k) ^ 2 ≤ (A / ℓ) ^ 2 := by
    apply sq_le_sq.mpr
    calc
      |d k| ≤ A / ℓ := hd_bound k
      _ = |A / ℓ| := by rw [abs_of_nonneg (div_nonneg hA0 (le_of_lt hℓ))]
  have hsq2 : (d (k + 1)) ^ 2 ≤ (A / ℓ) ^ 2 := by
    apply sq_le_sq.mpr
    calc
      |d (k + 1)| ≤ A / ℓ := hd_bound (k + 1)
      _ = |A / ℓ| := by rw [abs_of_nonneg (div_nonneg hA0 (le_of_lt hℓ))]
  have hsq_bound : (d k) ^ 2 + (d (k + 1)) ^ 2 ≤ (2 * A ^ 2) / ℓ ^ 2 := by
    calc
      (d k) ^ 2 + (d (k + 1)) ^ 2 ≤ (A / ℓ) ^ 2 + (A / ℓ) ^ 2 := add_le_add hsq1 hsq2
      _ = (2 * A ^ 2) / ℓ ^ 2 := by
        field_simp [hℓ0]
        ring_nf
  calc
    (∑ j : Fin (m + 2), (deriv (fun w : ℝ => axisFam ρ ℓ m j w) t) ^ 2)
        = (∑ j : Fin (m + 2), (d j.val) ^ 2) := by
          simp [axisFam, d]
    _ = (∑ i ∈ Finset.range (m + 2), (d i) ^ 2) := by
          simpa using (Fin.sum_univ_eq_sum_range (fun i : ℕ => (d i) ^ 2) (m + 2))
    _ = (d k) ^ 2 + (d (k + 1)) ^ 2 := hcollapse
    _ ≤ (2 * A ^ 2) / ℓ ^ 2 := hsq_bound

/-- The squared derivative of the axis profile is nonnegative. -/
lemma axis_grad_sq_nonneg {ρ : ℝ → ℝ} {ℓ : ℝ} (m : ℕ) (j : Fin (m + 2)) (t : ℝ) :
    0 ≤ (deriv (fun u : ℝ => axisFam ρ ℓ m j u) t) ^ 2 := by
  exact sq_nonneg _

end BoseGases

end Submission
