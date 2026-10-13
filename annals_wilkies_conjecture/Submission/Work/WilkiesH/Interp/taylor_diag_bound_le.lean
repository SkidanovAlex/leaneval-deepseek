import Mathlib
import Submission.Work.WilkiesH.Interp.taylor_diag_bound

namespace Work.WilkiesH.Interp

open Set Filter
open scoped Topology

/-- Taylor's theorem with a sharp remainder bound along the segment from `x` to `y`, with a
`β`-bound on the jets at `x`.

Let `U` be open and convex, `F : ℝ^m → ℝ` be `C^{b+1}` on `U`, and `x, y ∈ U`.  Suppose all
iterated derivatives of `F` at `x` of order `j ≤ b` are bounded by `β * ‖y - x‖^j` when applied
to `y - x`, and that the `(b+1)`-st iterated derivative of `F` is bounded by `C` on the segment
`[x, y]`.  Then
`|F y| ≤ β * ∑_{j ≤ b} ‖y - x‖^j / j! + C / (b+1)! * ‖y - x‖^{b+1}`. -/
theorem taylor_diag_bound_le {m b : ℕ} {F : (Fin m → ℝ) → ℝ} {U : Set (Fin m → ℝ)}
    (hU : IsOpen U) (hconv : Convex ℝ U) (hF : ContDiffOn ℝ (b + 1 : ℕ) F U)
    {x y : Fin m → ℝ} (hx : x ∈ U) (hy : y ∈ U) {β C : ℝ} (hβ : 0 ≤ β)
    (hjet : ∀ j ≤ b, ‖iteratedFDeriv ℝ j F x (fun _ => y - x)‖ ≤ β * ‖y - x‖ ^ j)
    (hC : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ (b + 1) F (x + s • (y - x))‖ ≤ C) :
    |F y| ≤ β * (∑ j ∈ Finset.range (b + 1), ‖y - x‖ ^ j / ((j.factorial : ℕ) : ℝ))
      + C / (((b + 1).factorial : ℕ) : ℝ) * ‖y - x‖ ^ (b + 1) := by
  set v : Fin m → ℝ := y - x with hv
  set g : ℝ → ℝ := fun s => F (x + s • v) with hg
  have huIcc : Set.uIcc (0 : ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le (by norm_num)
  -- the segment from `x` to `y` lies in `U` (convexity)
  have hseg : ∀ s ∈ Set.Icc (0 : ℝ) 1, x + s • v ∈ U := by
    intro s hs
    have hmem : (1 - s) • x + s • y ∈ U :=
      (hconv.starConvex hx) hy (by linarith [hs.2]) hs.1 (by ring)
    have heq : x + s • v = (1 - s) • x + s • y := by
      rw [hv, smul_sub, sub_smul, one_smul]; abel
    rw [heq]; exact hmem
  -- smoothness of the parametrised curve
  have hGS : ContDiffOn ℝ (b + 1 : ℕ) g ((fun s : ℝ => x + s • v) ⁻¹' U) := by
    rw [hg]; exact hF.comp (by fun_prop) (fun s hs => hs)
  have hPathOn : ContDiffOn ℝ (b + 1 : ℕ) g (Set.uIcc (0 : ℝ) 1) := by
    rw [huIcc]; exact hGS.mono (fun s hs => hseg s hs)
  have hSopen : IsOpen ((fun s : ℝ => x + s • v) ⁻¹' U) := hU.preimage (by fun_prop)
  have h0S : (0 : ℝ) ∈ (fun s : ℝ => x + s • v) ⁻¹' U := by simpa using hx
  have hGAt : ContDiffAt ℝ (b + 1 : ℕ) g 0 := hGS.contDiffAt (hSopen.mem_nhds h0S)
  -- the jets of `g` at `0` are the jets of `F` at `x` evaluated at `v`
  have hdw : ∀ k ≤ b, iteratedDerivWithin k g (Set.uIcc (0 : ℝ) 1) 0
      = (iteratedFDeriv ℝ k F x) (fun _ => v) := by
    intro k hk
    have hcd : ContDiffAt ℝ (k : ℕ) g 0 := hGAt.of_le (by exact_mod_cast (by omega : k ≤ b + 1))
    rw [huIcc]
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1)) hcd
      ⟨le_refl 0, by norm_num⟩]
    rw [hg]
    show (iteratedFDeriv ℝ k (fun s : ℝ => F (x + s • v)) 0) (fun _ => (1 : ℝ))
        = (iteratedFDeriv ℝ k F x) (fun _ => v)
    rw [iteratedFDerivAlongLine (n := b + 1) hU hF (i := k) (by omega) (t := 0)
      (by simpa using hx)]
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    simp [ContinuousLinearMap.toSpanSingleton_apply]
  -- the jets of `F` at `x` applied to `v` obey the bound `β * ‖v‖ ^ k`
  have hjetk : ∀ k ≤ b, |(iteratedFDeriv ℝ k F x) (fun _ => v)| ≤ β * ‖v‖ ^ k := by
    intro k hk
    have h := hjet k hk
    rw [Real.norm_eq_abs] at h
    exact h
  -- value of the Taylor polynomial at `1`
  have hTW : taylorWithinEval g b (Set.uIcc (0 : ℝ) 1) 0 1
      = ∑ k ∈ Finset.range (b + 1), (k.factorial : ℝ)⁻¹ * ((iteratedFDeriv ℝ k F x) (fun _ => v)) := by
    rw [taylor_within_apply]
    refine Finset.sum_congr rfl ?_
    intro k hk
    rw [Finset.mem_range] at hk
    rw [hdw k (by omega)]
    simp [smul_eq_mul]
  -- bound on the Taylor polynomial
  have hTay_bound : |taylorWithinEval g b (Set.uIcc (0 : ℝ) 1) 0 1|
      ≤ ∑ k ∈ Finset.range (b + 1), β * ‖v‖ ^ k / ((k.factorial : ℕ) : ℝ) := by
    rw [hTW]
    refine (Finset.abs_sum_le_sum_abs
      (fun k => (k.factorial : ℝ)⁻¹ * ((iteratedFDeriv ℝ k F x) (fun _ => v)))
      (Finset.range (b + 1))).trans ?_
    apply Finset.sum_le_sum
    intro k hk
    rw [Finset.mem_range] at hk
    rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg k.factorial))]
    calc (k.factorial : ℝ)⁻¹ * |(iteratedFDeriv ℝ k F x) (fun _ => v)|
        ≤ (k.factorial : ℝ)⁻¹ * (β * ‖v‖ ^ k) :=
          mul_le_mul_of_nonneg_left (hjetk k (by omega))
            (inv_nonneg.mpr (Nat.cast_nonneg k.factorial))
      _ = β * ‖v‖ ^ k / ((k.factorial : ℕ) : ℝ) := by
          rw [div_eq_mul_inv]; ring
  -- Taylor's theorem with the Lagrange form of the remainder
  obtain ⟨ξ, hξ, hξeq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (f := g)
    (x := (1 : ℝ)) (x₀ := 0) (n := b) (by norm_num) hPathOn
  have hξI : ξ ∈ Set.Icc (0 : ℝ) 1 := by
    have h := hξ
    rw [Set.uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] at h
    exact ⟨le_of_lt h.1, le_of_lt h.2⟩
  have hfact : (0 : ℝ) < ((b + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (b + 1)
  -- bound on the last derivative of `g`
  have hbound : ‖iteratedDeriv (b + 1) g ξ‖ ≤ C * ‖v‖ ^ (b + 1) := by
    have hξU : x + ξ • v ∈ U := hseg ξ hξI
    have hchain := iteratedFDerivAlongLine (n := b + 1) hU hF (i := b + 1) le_rfl (t := ξ) hξU
    have hA : ‖iteratedDeriv (b + 1) g ξ‖
        = ‖(iteratedFDeriv ℝ (b + 1) F (x + ξ • v)) (fun _ : Fin (b + 1) => v)‖ := by
      rw [iteratedDeriv, hg]
      rw [hchain, ContinuousMultilinearMap.compContinuousLinearMap_apply]
      simp [ContinuousLinearMap.toSpanSingleton_apply]
    refine hA.trans_le ?_
    calc ‖(iteratedFDeriv ℝ (b + 1) F (x + ξ • v)) (fun _ : Fin (b + 1) => v)‖
        ≤ ‖iteratedFDeriv ℝ (b + 1) F (x + ξ • v)‖ * (∏ _ : Fin (b + 1), ‖v‖) :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ = ‖iteratedFDeriv ℝ (b + 1) F (x + ξ • v)‖ * ‖v‖ ^ (b + 1) := by
          simp [Finset.prod_const]
      _ ≤ C * ‖v‖ ^ (b + 1) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact hC ξ hξI
  have hg1F : g 1 = F y := by
    have hthis : x + (1 : ℝ) • v = y := by
      rw [hv, one_smul]; abel
    rw [hg]; exact congrArg F hthis
  have hg1 : g 1 = taylorWithinEval g b (Set.uIcc (0 : ℝ) 1) 0 1
      + iteratedDeriv (b + 1) g ξ / ((b + 1).factorial : ℝ) := by
    have h := hξeq
    rw [sub_zero, one_pow, mul_one] at h
    rw [sub_eq_iff_eq_add] at h
    rw [add_comm] at h
    exact h
  have hrem : |iteratedDeriv (b + 1) g ξ / ((b + 1).factorial : ℝ)|
      ≤ C / (((b + 1).factorial : ℕ) : ℝ) * ‖v‖ ^ (b + 1) := by
    rw [abs_div, abs_of_pos hfact]
    have hb := hbound
    rw [Real.norm_eq_abs] at hb
    calc |iteratedDeriv (b + 1) g ξ| / ((b + 1).factorial : ℝ)
        ≤ (C * ‖v‖ ^ (b + 1)) / ((b + 1).factorial : ℝ) :=
          div_le_div_of_nonneg_right hb hfact.le
      _ = C / (((b + 1).factorial : ℕ) : ℝ) * ‖v‖ ^ (b + 1) := by
          rw [div_eq_mul_inv]; ring
  have hfinal : |F y| ≤ (∑ k ∈ Finset.range (b + 1), β * ‖v‖ ^ k / ((k.factorial : ℕ) : ℝ))
      + C / (((b + 1).factorial : ℕ) : ℝ) * ‖v‖ ^ (b + 1) := by
    rw [← hg1F, hg1]
    exact (abs_add_le _ _).trans (add_le_add hTay_bound hrem)
  have hS : (∑ k ∈ Finset.range (b + 1), β * ‖v‖ ^ k / ((k.factorial : ℕ) : ℝ))
      = β * (∑ j ∈ Finset.range (b + 1), ‖y - x‖ ^ j / ((j.factorial : ℕ) : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [mul_div_assoc]
  have hR : C / (((b + 1).factorial : ℕ) : ℝ) * ‖v‖ ^ (b + 1)
      = C / (((b + 1).factorial : ℕ) : ℝ) * ‖y - x‖ ^ (b + 1) := by
    rw [hv]
  calc |F y| ≤ (∑ k ∈ Finset.range (b + 1), β * ‖v‖ ^ k / ((k.factorial : ℕ) : ℝ))
        + C / (((b + 1).factorial : ℕ) : ℝ) * ‖v‖ ^ (b + 1) := hfinal
    _ = β * (∑ j ∈ Finset.range (b + 1), ‖y - x‖ ^ j / ((j.factorial : ℕ) : ℝ))
        + C / (((b + 1).factorial : ℕ) : ℝ) * ‖y - x‖ ^ (b + 1) := by rw [hS, hR]

end Work.WilkiesH.Interp
