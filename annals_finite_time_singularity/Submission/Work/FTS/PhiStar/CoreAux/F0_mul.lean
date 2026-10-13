import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.PhiStar.CoreAux.Defs
import Submission.Work.FTS.NonlinRows.sqm_pz_DthIter_mul_le_4_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.CoreAux

/-- **The flat class `F0` is closed under pointwise products**, with the constant
`2^n · K · K'`.  The proof is the two-operator Leibniz rule

`∂_z^k D_θ^i (f·g) = ∑_{a≤i} ∑_{c≤k} C(i,a) C(k,c) ∂_z^c D_θ^a f · ∂_z^{k-c} D_θ^{i-a} g`

(`Work.FTS.NonlinRows.sqo_pz_DthIter_mul_eq`), together with the split
`(z+1)^k = (z+1)^c · (z+1)^{k-c}`: every summand inherits the bound `K` from `f` and
`K'` from `g`, and the total coefficient is
`∑_{a≤i} ∑_{c≤k} C(i,a)C(k,c) = 2^i · 2^k ≤ 2^{i+k} ≤ 2^n`. -/
theorem F0_mul {n : ℕ} {K K' : ℝ} {f g : ℝ → ℝ → ℝ} (hK : 0 ≤ K) (hK' : 0 ≤ K') (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hsg : Work.FTS.EllipticEst.SmoothOpen g) (hf : Work.FTS.PhiStar.F0 n K f) (hg : Work.FTS.PhiStar.F0 n K' g) : Work.FTS.PhiStar.F0 n ((2 : ℝ) ^ n * K * K') (fun z θ => f z θ * g z θ) := by
  intro k i hki z θ hz hθ hθ'
  have hz1 : (0 : ℝ) < z + 1 := by linarith
  rw [Work.FTS.NonlinRows.sqo_pz_DthIter_mul_eq k i f g hsf hsg z hz θ ⟨hθ, hθ'⟩]
  simp only [Finset.mul_sum]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum fun a ha => Finset.abs_sum_le_sum_abs _ _) ?_
  calc ∑ a ∈ Finset.range (i + 1), ∑ c ∈ Finset.range (k + 1),
        |(z + 1) ^ k * (↑(i.choose a) * ↑(k.choose c) *
          (Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ *
            Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (i - a) g) z θ))|
      ≤ ∑ a ∈ Finset.range (i + 1), ∑ c ∈ Finset.range (k + 1),
          ↑(i.choose a) * ↑(k.choose c) * K * K' := by
        refine Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun c hc => ?_
        have hai : a ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
        have hck : c ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hc)
        have hA : (z + 1) ^ c * |Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ| ≤ K := by
          have h := hf c a (by omega) z θ hz hθ hθ'
          rwa [abs_mul, abs_of_pos (pow_pos hz1 c)] at h
        have hB : (z + 1) ^ (k - c) * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (i - a) g) z θ| ≤ K' := by
          have h := hg (k - c) (i - a) (by omega) z θ hz hθ hθ'
          rwa [abs_mul, abs_of_pos (pow_pos hz1 (k - c))] at h
        have hcoef : (0 : ℝ) ≤ ↑(i.choose a) * ↑(k.choose c) := by positivity
        have hpow : (z + 1) ^ k = (z + 1) ^ c * (z + 1) ^ (k - c) := by
          rw [← pow_add, Nat.add_sub_of_le hck]
        have heq : |(z + 1) ^ k * (↑(i.choose a) * ↑(k.choose c) *
            (Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ *
              Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (i - a) g) z θ))|
            = (↑(i.choose a) * ↑(k.choose c)) *
                ((z + 1) ^ c * |Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ|) *
                ((z + 1) ^ (k - c) * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (i - a) g) z θ|) := by
          simp only [abs_mul, abs_of_pos (pow_pos hz1 c), abs_of_pos (pow_pos hz1 (k - c)),
            abs_of_nonneg hcoef, hpow]
          ring
        rw [heq]
        calc (↑(i.choose a) * ↑(k.choose c)) *
                ((z + 1) ^ c * |Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ|) *
                ((z + 1) ^ (k - c) * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (i - a) g) z θ|)
            ≤ ((↑(i.choose a) * ↑(k.choose c)) * K) * K' :=
              mul_le_mul (mul_le_mul_of_nonneg_left hA hcoef) hB
                (mul_nonneg (pow_nonneg (le_of_lt hz1) _) (abs_nonneg _))
                (mul_nonneg hcoef hK)
          _ = ↑(i.choose a) * ↑(k.choose c) * K * K' := by ring
    _ ≤ 2 ^ n * K * K' := by
        have hSi : (∑ a ∈ Finset.range (i + 1), ((i.choose a : ℝ))) = (2 : ℝ) ^ i := by
          exact_mod_cast Nat.sum_range_choose i
        have hSk : (∑ c ∈ Finset.range (k + 1), ((k.choose c : ℝ))) = (2 : ℝ) ^ k := by
          exact_mod_cast Nat.sum_range_choose k
        have hstep0 : (∑ a ∈ Finset.range (i + 1), ∑ c ∈ Finset.range (k + 1),
              ((i.choose a : ℝ) * (k.choose c : ℝ)) * K * K')
            = (∑ a ∈ Finset.range (i + 1), ∑ c ∈ Finset.range (k + 1),
                ((i.choose a : ℝ) * (k.choose c : ℝ)) * (K * K')) := by
          refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun c hc => ?_
          ring
        have hstep1 : (∑ a ∈ Finset.range (i + 1), ∑ c ∈ Finset.range (k + 1),
                ((i.choose a : ℝ) * (k.choose c : ℝ)) * (K * K'))
            = (∑ a ∈ Finset.range (i + 1), ∑ c ∈ Finset.range (k + 1),
                ((i.choose a : ℝ) * (k.choose c : ℝ))) * (K * K') := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.sum_mul]
        have hstep2 : (∑ a ∈ Finset.range (i + 1), ∑ c ∈ Finset.range (k + 1),
                ((i.choose a : ℝ) * (k.choose c : ℝ)))
            = (∑ a ∈ Finset.range (i + 1), (i.choose a : ℝ)) * (∑ c ∈ Finset.range (k + 1), (k.choose c : ℝ)) := by
          rw [Finset.sum_mul_sum]
        have hS : (∑ a ∈ Finset.range (i + 1), ∑ c ∈ Finset.range (k + 1),
              ((i.choose a : ℝ) * (k.choose c : ℝ)) * K * K')
            = ((2 : ℝ) ^ i * (2 : ℝ) ^ k) * (K * K') := by
          rw [hstep0, hstep1, hstep2, hSi, hSk]
        refine le_trans (le_of_eq hS) ?_
        have hik : i + k ≤ n := by omega
        have hpow2 : (2 : ℝ) ^ i * (2 : ℝ) ^ k ≤ (2 : ℝ) ^ n := by
          rw [← pow_add]
          exact pow_le_pow_right₀ (by norm_num) hik
        have hKK' : 0 ≤ K * K' := mul_nonneg hK hK'
        calc ((2 : ℝ) ^ i * (2 : ℝ) ^ k) * (K * K') ≤ (2 : ℝ) ^ n * (K * K') :=
              mul_le_mul_of_nonneg_right hpow2 hKK'
          _ = (2 : ℝ) ^ n * K * K' := by ring

end Work.FTS.PhiStar.CoreAux
