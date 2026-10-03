import Mathlib
import Submission.Work.Peluse.Crux.dualFn_tsum_norm_ge

/-!
# The dual function's `ℓ¹`-norm dominates the `ℓ¹`-norm of `f₁`

This module proves the elementary estimate

`δ N^{deg P} ≤ ∑_z ‖F₂ z‖  ⟹  δ N^{deg P} ≤ ∑_x ‖f₁ x‖`,

where `F₂ = dualFn N P f₀ f₁` is Peluse's dual function.  The content is that the averaging over
`y ∈ [N]` in `F₂` is a contraction in `ℓ¹` as soon as `‖f₀‖ ≤ 1`: `F₂` is a "convolution" of the
translated copies of `f₁` against bounded weights, so

`∑_z ‖F₂ z‖ ≤ N⁻¹ ∑_{y∈[N]} ∑_z ‖f₁ (z + y - P y)‖ = N⁻¹ · N · ∑_x ‖f₁ x‖ = ∑_x ‖f₁ x‖`.

Combined with `Work.Peluse.Crux.dualFn_tsum_norm_ge` (which turns the lower bound for the
multilinear average `Λ^{N₀,N}` into the lower bound for `∑_z ‖F₂ z‖`) this gives the requested
statement.

## Main result

* `Work.Peluse.Crux.dualFn_l1_ge_f1_l1`.
-/

set_option autoImplicit false

open scoped BigOperators
open Polynomial

namespace Work.Peluse.Crux

noncomputable section

/-! ## Elementary support lemmas -/

private lemma mem_symIcc_natAbs {L : ℕ} {x : ℤ} :
    x ∈ Work.Peluse.symIcc L ↔ x.natAbs ≤ L := by
  rw [Work.Peluse.symIcc, Finset.mem_Icc]
  constructor
  · intro h
    have h1 : |x| ≤ (L : ℤ) := abs_le.mpr h
    rw [← Int.natCast_natAbs] at h1
    exact_mod_cast h1
  · intro hx
    have h1 : (x.natAbs : ℤ) ≤ (L : ℤ) := by exact_mod_cast hx
    rw [Int.natCast_natAbs] at h1
    exact abs_le.mp h1

private lemma not_mem_symIcc_iff {L : ℕ} {x : ℤ} :
    x ∉ Work.Peluse.symIcc L ↔ L < x.natAbs := by
  rw [mem_symIcc_natAbs]; exact not_le

private lemma symIcc_mono {L M : ℕ} (h : L ≤ M) :
    Work.Peluse.symIcc L ⊆ Work.Peluse.symIcc M :=
  fun _ hx => mem_symIcc_natAbs.mpr ((mem_symIcc_natAbs.mp hx).trans h)

/-- Change of variables for an unconditional sum over `ℤ`: translating the argument is a
bijection of `ℤ`. -/
private lemma tsum_shift_real (G : ℤ → ℝ) (p : ℤ) :
    (∑' x : ℤ, G (x + p)) = ∑' x : ℤ, G x := by
  simpa using Equiv.tsum_eq (Equiv.addRight p) G

/-- Shifting the argument of a finitely supported function does not change its sum over a finite
set containing both the support and the shifted support:

`∑_{x ∈ S} G (x + p) = ∑_{z ∈ S} G z`

whenever `G` vanishes off `S` and off `S - p`. -/
private lemma sum_shift_of_support {S : Finset ℤ} {G : ℤ → ℝ} {p : ℤ}
    (hA : ∀ z, z ∉ S → G z = 0) (hB : ∀ z, z - p ∉ S → G z = 0) :
    ∑ x ∈ S, G (x + p) = ∑ z ∈ S, G z := by
  have h1 : (∑' x : ℤ, G (x + p)) = ∑ z ∈ S, G z := by
    rw [tsum_shift_real G p]
    exact tsum_eq_sum (s := S) hA
  rw [← h1]
  exact (tsum_eq_sum (s := S)
    (fun x hx => hB (x + p) (by rw [add_sub_cancel_right]; exact hx))).symm

/-! ## The dual function vanishes outside a large box -/

private lemma dualFn_eq_zero_of_not_mem {N₀ N : ℕ} (P : Polynomial ℤ) (f₀ f₁ : ℤ → ℂ)
    (hs0 : Work.Peluse.SupportIn f₀ N₀) {z : ℤ}
    (hz : z ∉ Work.Peluse.symIcc (N₀ + N + Work.Peluse.polySup P N)) :
    Work.Peluse.dualFn N P f₀ f₁ z = 0 := by
  have hzlt : N₀ + N + Work.Peluse.polySup P N < z.natAbs := not_mem_symIcc_iff.mp hz
  have hzabs : ((N₀ + N + Work.Peluse.polySup P N : ℕ) : ℤ) < |z| := by
    rw [← Int.natCast_natAbs z]; exact_mod_cast hzlt
  have hzabs' : (N₀ : ℤ) + (N : ℤ) + ((Work.Peluse.polySup P N : ℕ) : ℤ) < |z| := by
    have h := hzabs
    push_cast at h
    linarith
  simp only [Work.Peluse.dualFn]
  rw [Finset.sum_eq_zero (fun y hy => ?_), mul_zero]
  obtain ⟨-, hy2⟩ := Finset.mem_Icc.mp hy
  have hPy : |P.eval ((y : ℕ) : ℤ)| ≤ ((Work.Peluse.polySup P N : ℕ) : ℤ) :=
    Work.Peluse.Tools.eval_abs_le_polySup P (by positivity) (by exact_mod_cast hy2)
  have hlt : (N₀ : ℤ) < |z - P.eval ((y : ℕ) : ℤ)| := by
    have h1 : |z| - |P.eval ((y : ℕ) : ℤ)| ≤ |z - P.eval ((y : ℕ) : ℤ)| :=
      abs_sub_abs_le_abs_sub z _
    linarith
  have hnat : N₀ < (z - P.eval ((y : ℕ) : ℤ)).natAbs := by
    have hc : (N₀ : ℤ) < (((z - P.eval ((y : ℕ) : ℤ)).natAbs : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs]; exact hlt
    exact_mod_cast hc
  rw [hs0 _ hnat, zero_mul]

/-! ## The pointwise bound on the dual function -/

private lemma dualFn_norm_le {N : ℕ} (hN : 1 ≤ N) (P : Polynomial ℤ) (f₀ f₁ : ℤ → ℂ)
    (hb0 : ∀ x : ℤ, ‖f₀ x‖ ≤ 1) (z : ℤ) :
    ‖Work.Peluse.dualFn N P f₀ f₁ z‖
      ≤ (N : ℝ)⁻¹ * ∑ y ∈ Finset.Icc 1 N, ‖f₁ (z + (y : ℤ) - P.eval (y : ℤ))‖ := by
  have hdual : Work.Peluse.dualFn N P f₀ f₁ z
      = ((N : ℂ))⁻¹ * ∑ y ∈ Finset.Icc 1 N,
          f₀ (z - P.eval (y : ℤ)) * f₁ (z + (y : ℤ) - P.eval (y : ℤ)) := rfl
  rw [hdual, norm_mul, norm_inv, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc ‖∑ y ∈ Finset.Icc 1 N, f₀ (z - P.eval (y : ℤ)) * f₁ (z + (y : ℤ) - P.eval (y : ℤ))‖
      ≤ ∑ y ∈ Finset.Icc 1 N,
          ‖f₀ (z - P.eval (y : ℤ)) * f₁ (z + (y : ℤ) - P.eval (y : ℤ))‖ := norm_sum_le _ _
    _ ≤ ∑ y ∈ Finset.Icc 1 N, ‖f₁ (z + (y : ℤ) - P.eval (y : ℤ))‖ := by
        apply Finset.sum_le_sum
        intro y _
        rw [norm_mul]
        calc ‖f₀ (z - P.eval (y : ℤ))‖ * ‖f₁ (z + (y : ℤ) - P.eval (y : ℤ))‖
            ≤ 1 * ‖f₁ (z + (y : ℤ) - P.eval (y : ℤ))‖ :=
              mul_le_mul_of_nonneg_right (hb0 _) (norm_nonneg _)
          _ = ‖f₁ (z + (y : ℤ) - P.eval (y : ℤ))‖ := one_mul _

/-! ## Reindexing one translate -/

/-- For `y ≤ N` the translate `z ↦ z + (y - P y)` does not change the sum of `‖f₁‖` over the box
`symIcc D`, as long as `D ≥ N₀ + N + polySup P N`: the box contains both the support of `f₁` and
its translate by `y - P y`, whose size is at most `N + polySup P N`. -/
private lemma sum_shift_norm_f₁ {N₀ N D : ℕ} (P : Polynomial ℤ) (f₁ : ℤ → ℂ)
    (hs1 : Work.Peluse.SupportIn f₁ N₀) (hD : N₀ + N + Work.Peluse.polySup P N ≤ D)
    {y : ℕ} (hy : y ≤ N) :
    ∑ z ∈ Work.Peluse.symIcc D, ‖f₁ (z + (y : ℤ) - P.eval (y : ℤ))‖
      = ∑ x ∈ Work.Peluse.symIcc N₀, ‖f₁ x‖ := by
  set c : ℤ := (y : ℤ) - P.eval (y : ℤ) with hc
  have hbase : N₀ ≤ D := by omega
  have hsub : Work.Peluse.symIcc N₀ ⊆ Work.Peluse.symIcc D := symIcc_mono hbase
  have hD' : (N₀ : ℤ) + (N : ℤ) + ((Work.Peluse.polySup P N : ℕ) : ℤ) ≤ (D : ℤ) := by
    exact_mod_cast hD
  have hcabs : |c| ≤ (N : ℤ) + ((Work.Peluse.polySup P N : ℕ) : ℤ) := by
    have h1 : |c| ≤ |(y : ℤ)| + |P.eval (y : ℤ)| := by
      rw [hc, sub_eq_add_neg, ← abs_neg (P.eval (y : ℤ))]
      exact abs_add_le _ _
    have h2 : |(y : ℤ)| ≤ (N : ℤ) := by
      rw [abs_of_nonneg (by positivity : (0 : ℤ) ≤ (y : ℤ))]
      exact_mod_cast hy
    have h3 : |P.eval (y : ℤ)| ≤ ((Work.Peluse.polySup P N : ℕ) : ℤ) :=
      Work.Peluse.Tools.eval_abs_le_polySup P (by positivity) (by exact_mod_cast hy)
    linarith
  have hmem : ∀ z : ℤ, z.natAbs ≤ N₀ → (z - c).natAbs ≤ D := by
    intro z hzN
    have h4 : |z| ≤ (N₀ : ℤ) := by
      rw [← Int.natCast_natAbs z]; exact_mod_cast hzN
    have h5 : |z - c| ≤ |z| + |c| := by
      rw [sub_eq_add_neg, ← abs_neg c]
      exact abs_add_le _ _
    have h6 : ((z - c).natAbs : ℤ) ≤ (D : ℤ) := by
      rw [Int.natCast_natAbs]
      linarith
    exact_mod_cast h6
  have hcongr : ∀ z : ℤ, ‖f₁ (z + (y : ℤ) - P.eval (y : ℤ))‖ = ‖f₁ (z + c)‖ := by
    intro z
    have harg : z + (y : ℤ) - P.eval (y : ℤ) = z + c := by
      rw [hc]; exact add_sub_assoc _ _ _
    exact congrArg (fun w => ‖f₁ w‖) harg
  have hstep := sum_shift_of_support (S := Work.Peluse.symIcc D) (G := fun w => ‖f₁ w‖)
    (p := c) (fun z hz => ?_) (fun z hz => ?_)
  · rw [Finset.sum_congr rfl (fun z _ => hcongr z), hstep]
    exact (Finset.sum_subset hsub (fun x _ hx => by
      have hlt : N₀ < x.natAbs := not_le.mp (fun h => hx (mem_symIcc_natAbs.mpr h))
      rw [hs1 x hlt, norm_zero])).symm
  · have hlt : N₀ < z.natAbs := not_le.mp (fun h => hz (hsub (mem_symIcc_natAbs.mpr h)))
    rw [hs1 z hlt, norm_zero]
  · by_contra hG
    have hf1 : f₁ z ≠ 0 := by simpa [norm_eq_zero] using hG
    have hzN : z.natAbs ≤ N₀ := by
      by_contra h
      exact hf1 (hs1 z (not_le.mp h))
    exact hz (mem_symIcc_natAbs.mpr (hmem z hzN))

/-! ## The main theorem -/

theorem dualFn_l1_ge_f1_l1 {N₀ N : ℕ} (hN₀ : 1 ≤ N₀) (hN : 1 ≤ N) (P : Polynomial ℤ) (f₀ f₁ f₂ : ℤ → ℂ) (δ : ℝ)
    (hs0 : Work.Peluse.SupportIn f₀ N₀) (hs1 : Work.Peluse.SupportIn f₁ N₀) (hs2 : Work.Peluse.SupportIn f₂ N₀)
    (hb0 : ∀ x : ℤ, ‖f₀ x‖ ≤ 1) (hb2 : ∀ x : ℤ, ‖f₂ x‖ ≤ 1)
    (hmain : δ * (N : ℝ) ^ P.natDegree ≤ ‖Work.Peluse.LambdaZ N₀ N P f₀ f₁ f₂‖ * (N₀ : ℝ)) :
    δ * (N : ℝ) ^ P.natDegree ≤ ∑' x : ℤ, ‖f₁ x‖ := by
  have h1 : δ * (N : ℝ) ^ P.natDegree ≤ ∑' z : ℤ, ‖Work.Peluse.dualFn N P f₀ f₁ z‖ :=
    dualFn_tsum_norm_ge hN₀ hN P f₀ f₁ f₂ δ hs0 hs1 hs2 hb2 hmain
  refine le_trans h1 ?_
  have hzero : ∀ z : ℤ, z ∉ Work.Peluse.symIcc (N₀ + N + Work.Peluse.polySup P N) →
      Work.Peluse.dualFn N P f₀ f₁ z = 0 :=
    fun z hz => dualFn_eq_zero_of_not_mem P f₀ f₁ hs0 hz
  have htsum : (∑' z : ℤ, ‖Work.Peluse.dualFn N P f₀ f₁ z‖)
      = ∑ z ∈ Work.Peluse.symIcc (N₀ + N + Work.Peluse.polySup P N),
          ‖Work.Peluse.dualFn N P f₀ f₁ z‖ :=
    tsum_eq_sum (fun z hz => by rw [hzero z hz, norm_zero])
  rw [htsum]
  have hcard : (Finset.Icc 1 N).card = N := by
    rw [Nat.card_Icc]; omega
  calc ∑ z ∈ Work.Peluse.symIcc (N₀ + N + Work.Peluse.polySup P N),
        ‖Work.Peluse.dualFn N P f₀ f₁ z‖
      ≤ ∑ z ∈ Work.Peluse.symIcc (N₀ + N + Work.Peluse.polySup P N),
          (N : ℝ)⁻¹ * ∑ y ∈ Finset.Icc 1 N, ‖f₁ (z + (y : ℤ) - P.eval (y : ℤ))‖ :=
        Finset.sum_le_sum fun z _ => dualFn_norm_le hN P f₀ f₁ hb0 z
    _ = (N : ℝ)⁻¹ * ∑ z ∈ Work.Peluse.symIcc (N₀ + N + Work.Peluse.polySup P N),
          ∑ y ∈ Finset.Icc 1 N, ‖f₁ (z + (y : ℤ) - P.eval (y : ℤ))‖ := by
        rw [Finset.mul_sum]
    _ = (N : ℝ)⁻¹ * ∑ y ∈ Finset.Icc 1 N,
          ∑ z ∈ Work.Peluse.symIcc (N₀ + N + Work.Peluse.polySup P N),
            ‖f₁ (z + (y : ℤ) - P.eval (y : ℤ))‖ := by
        rw [Finset.sum_comm]
    _ = (N : ℝ)⁻¹ * ∑ y ∈ Finset.Icc 1 N, ∑ x ∈ Work.Peluse.symIcc N₀, ‖f₁ x‖ := by
        congr 1
        apply Finset.sum_congr rfl
        intro y hy
        exact sum_shift_norm_f₁ P f₁ hs1 (le_refl _) (Finset.mem_Icc.mp hy).2
    _ = (N : ℝ)⁻¹ * (N : ℝ) * ∑ x ∈ Work.Peluse.symIcc N₀, ‖f₁ x‖ := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]
        ring
    _ = ∑ x ∈ Work.Peluse.symIcc N₀, ‖f₁ x‖ := by
        have hNne : (N : ℝ) ≠ 0 := by positivity
        rw [inv_mul_cancel₀ hNne, one_mul]
    _ = ∑' x : ℤ, ‖f₁ x‖ := by
        exact (tsum_eq_sum (s := Work.Peluse.symIcc N₀) (fun x hx => by
          have hlt : N₀ < x.natAbs := not_le.mp (fun h => hx (mem_symIcc_natAbs.mpr h))
          rw [hs1 x hlt, norm_zero])).symm

end

end Work.Peluse.Crux
