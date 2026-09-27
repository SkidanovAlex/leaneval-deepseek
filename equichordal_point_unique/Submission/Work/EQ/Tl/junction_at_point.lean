import Mathlib
import Submission.Work.EQ.TailGlueDefs

namespace Work.EQ.Tl

open Complex Filter _root_.Topology
open scoped Topology

/-- **The junction identity, spread out.**  Over the annulus, every chain of `S` close to `z₀` (within
the `2^(2*dep)`-th power of the F3 radius) is a glued chain `tailGlue a h c z₀ dep σ t` of an
admissible sign function whose junction identity holds at the parameter `t`.

The parameter `t` is a `2^(2*dep)`-th root of `q.2.1 - z₀` (its existence with `‖t‖ < rhoFin'` is
exactly the hypothesis `hqr`, cf. `backward_puiseux`); the F3 coverage (`Work.EQ.coverage`, bp_aux)
identifies the `2*dep+1` middle entries of `q` with the branch family `branchPt`; the tail
identities identify the remaining entries of `q` with the glued tails; and the junction identity at
the index `-dep` is the `IsChain` condition of `q` at the index `-dep`, using that the tail
identity of `q` at depth `dep ≥ N` pins its entry there. -/
theorem junction_at_point {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {S : Set ChainData} {c : ℂ} (hS : S ⊆ H0 a h) (hc : c ≠ 0)
    (hval : ∀ q ∈ S, q.2.1 * q.2.2 = c)
    {r₁ r₂ : ℝ} {N : ℕ} (hr₁ : 0 < r₁) (hr₂ : r₁ < r₂)
    (htail : ∀ q ∈ S, q.2.1 ∈ Ann r₁ r₂ →
      (∀ n : ℕ, N ≤ n → q.1 (n : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ n * q.2.1)) ∧
      (∀ n : ℕ, N ≤ n → q.1 (-(n : ℤ)) = ugermC a h (((eqLam a : ℝ) : ℂ) ^ n * q.2.2)))
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ann r₁ r₂) {dep : ℕ} (hdepN : N ≤ dep) (hdep1 : 1 ≤ dep)
    (hend : AnalyticOnNhd ℂ (endFun a h dep) (Metric.ball z₀ 1))
    {q : ChainData} (hq : q ∈ S) (hqA : q.2.1 ∈ Ann r₁ r₂) (hqne : q.2.1 ≠ z₀)
    (hqr : ‖q.2.1 - z₀‖ < (rhoFin' a (endFun a h dep) z₀ 1 (2 * dep)) ^ (2 ^ (2 * dep))) :
    ∃ (σ : Fin (2 * dep) → Bool) (t : ℂ), Adm a (endFun a h dep) z₀ 1 σ ∧
      t ^ (2 ^ (2 * dep)) = q.2.1 - z₀ ∧ 0 < ‖t‖ ∧
      ‖t‖ < rhoFin' a (endFun a h dep) z₀ 1 (2 * dep) ∧
      q = tailGlue a h c z₀ dep σ t ∧
      branchPt a (endFun a h dep) z₀ 1 σ t ⟨0, by omega⟩ =
        ugermC a h (((eqLam a : ℝ) : ℂ) ^ dep * (c / (z₀ + t ^ (2 ^ (2 * dep))))) := by
  -- the chain datum `q` is a chain, and its two tails are the germs from depth `N`
  have hchain : IsChain a h q := isChain_of_mem_H0 (hS hq)
  obtain ⟨hfwt, hbwt⟩ := htail q hq hqA
  -- `ψ₁ = q.2.1 ≠ 0`, hence `ψ₂ = c / ψ₁`
  have hq1pos : 0 < ‖q.2.1‖ := lt_of_lt_of_le hr₁ hqA.1
  have hq1ne : q.2.1 ≠ 0 := norm_pos_iff.mp hq1pos
  have hq2 : q.2.2 = c / q.2.1 := by
    rw [eq_div_iff hq1ne, mul_comm]
    exact hval q hq
  have hρpos : 0 < rhoFin' a (endFun a h dep) z₀ 1 (2 * dep) := rhoFin'_pos one_pos hend
  -- the `2^(2*dep)`-th root `t` of `q.2.1 - z₀`
  obtain ⟨t, htk, ht0, htρ⟩ := bp_root_aux (w := q.2.1 - z₀)
    (ρ := rhoFin' a (endFun a h dep) z₀ 1 (2 * dep)) (k := 2 ^ (2 * dep))
    (by positivity) hρpos (sub_ne_zero.mpr hqne) hqr
  have hψ1 : z₀ + t ^ (2 ^ (2 * dep)) = q.2.1 := by rw [htk]; ring
  have hψ2 : c / (z₀ + t ^ (2 ^ (2 * dep))) = q.2.2 := by rw [hψ1, ← hq2]
  -- the F3 coverage applied to the `2*dep+1` middle entries of `q`
  have hP : q.1 ((((Fin.last (2 * dep) : Fin (2 * dep + 1)) : ℕ) : ℤ) - (dep : ℤ))
      = endFun a h dep q.2.1 := by
    rw [show (((Fin.last (2 * dep) : Fin (2 * dep + 1)) : ℕ) : ℤ) = ((2 * dep : ℕ) : ℤ) by simp,
      show (((2 * dep : ℕ) : ℤ) - (dep : ℤ)) = (dep : ℤ) by push_cast; ring]
    exact hfwt dep hdepN
  have hreg : ∀ j : Fin (2 * dep), RegPair a
      (q.1 ((((Fin.castSucc j : Fin (2 * dep + 1)) : ℕ) : ℤ) - (dep : ℤ)))
      (q.1 ((((Fin.succ j : Fin (2 * dep + 1)) : ℕ) : ℤ) - (dep : ℤ))) := by
    intro j
    have h2 : (((Fin.castSucc j : Fin (2 * dep + 1)) : ℕ) : ℤ) = ((j : ℕ) : ℤ) := by simp
    have h3 : (((Fin.succ j : Fin (2 * dep + 1)) : ℕ) : ℤ) = (((j : ℕ) + 1 : ℕ) : ℤ) := by simp
    have h1 : ((((j : ℕ) + 1 : ℕ) : ℤ) - (dep : ℤ)) = (((j : ℕ) : ℤ) - (dep : ℤ)) + 1 := by
      push_cast; ring
    rw [h2, h3, h1]
    exact hchain.1 (((j : ℕ) : ℤ) - (dep : ℤ))
  obtain ⟨σ, hAdm, hPj⟩ := coverage (a := a) (u₀ := z₀) (R := 1) one_pos
    (c := endFun a h dep) hend (N := 2 * dep) (u := q.2.1) (t := t) htk
    (norm_ne_zero_iff.mp (ne_of_gt ht0)) htρ
    (fun j : Fin (2 * dep + 1) => q.1 (((j : ℕ) : ℤ) - (dep : ℤ))) hP hreg
  refine ⟨σ, t, hAdm, htk, ht0, htρ, ?_, ?_⟩
  · -- `q` is the glued chain
    refine Prod.ext (funext ?_) (Prod.ext ?_ ?_)
    · intro j
      by_cases h1 : (dep : ℤ) ≤ j
      · -- forward tail
        rw [tailGlue_fwd (j := j) h1]
        have hj0 : (0 : ℤ) ≤ j := by
          have : (0 : ℤ) ≤ (dep : ℤ) := by exact_mod_cast Nat.zero_le dep
          omega
        have hjnat : (((j.toNat : ℕ)) : ℤ) = j := Int.toNat_of_nonneg hj0
        have hNj : N ≤ j.toNat := by
          have : (N : ℤ) ≤ ((j.toNat : ℕ) : ℤ) := by rw [hjnat]; omega
          exact_mod_cast this
        have hfw' : q.1 j = germC a h (((eqLam a : ℝ) : ℂ) ^ j.toNat * q.2.1) := by
          conv_lhs => rw [← hjnat]
          exact hfwt j.toNat hNj
        have hpow : ((eqLam a : ℝ) : ℂ) ^ j.toNat = ((eqLam a : ℝ) : ℂ) ^ j := by
          conv_rhs => rw [← hjnat, zpow_natCast]
        rw [hfw', hψ1, hpow]
      · by_cases h2 : -((dep : ℤ)) ≤ j
        · -- middle segment: the F3 branch family
          rw [tailGlue_mid (j := j) h1 h2]
          have hpos : (0 : ℤ) ≤ j + (dep : ℤ) := by omega
          have hlt : (j + (dep : ℤ)).toNat < 2 * dep + 1 := by
            rw [Int.toNat_lt hpos]; push_cast; omega
          have hidx :
              ((((⟨(j + (dep : ℤ)).toNat, hlt⟩ : Fin (2 * dep + 1)) : ℕ) : ℤ) - (dep : ℤ)) = j := by
            simp only [Int.toNat_of_nonneg hpos]
            ring
          have hmid : q.1 j =
              branchPt a (endFun a h dep) z₀ 1 σ t ⟨(j + (dep : ℤ)).toNat, hlt⟩ := by
            conv_lhs => rw [← hidx]
            exact hPj ⟨(j + (dep : ℤ)).toNat, hlt⟩
          rw [hmid]
        · -- backward tail
          rw [tailGlue_bwd (j := j) (by omega : j < -((dep : ℤ)))]
          have hj0 : (0 : ℤ) ≤ -j := by omega
          have hjnat : ((((-j).toNat : ℕ)) : ℤ) = -j := Int.toNat_of_nonneg hj0
          have hNj : N ≤ (-j).toNat := by
            have : (N : ℤ) ≤ (((-j).toNat : ℕ) : ℤ) := by rw [hjnat]; omega
            exact_mod_cast this
          have hbw' : q.1 j = ugermC a h (((eqLam a : ℝ) : ℂ) ^ (-j).toNat * q.2.2) := by
            conv_lhs => rw [show j = -((((-j).toNat : ℕ)) : ℤ) by rw [hjnat]; ring]
            exact hbwt (-j).toNat hNj
          have hpow : ((eqLam a : ℝ) : ℂ) ^ (-j).toNat = ((eqLam a : ℝ) : ℂ) ^ (-j) := by
            conv_rhs => rw [← hjnat, zpow_natCast]
          rw [hbw', hpow, hψ2]
    · rw [tailGlue_psi1]; exact hψ1.symm
    · rw [tailGlue_psi2]; exact hψ2.symm
  · -- the junction identity at the index `-dep`
    have h0 := hPj (⟨0, by omega⟩ : Fin (2 * dep + 1))
    have h0' : branchPt a (endFun a h dep) z₀ 1 σ t (⟨0, by omega⟩ : Fin (2 * dep + 1)) =
        q.1 (-(dep : ℤ)) := by
      rw [← h0]
      simp
    rw [h0', hbwt dep hdepN, hψ2]

end Work.EQ.Tl
