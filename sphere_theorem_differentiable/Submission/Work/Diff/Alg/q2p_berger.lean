import Mathlib
import Submission.Work.Diff.Alg.q2p_defs
import Submission.Work.Diff.Alg.Q2PB.Defs
import Submission.Work.Diff.Alg.Q2PB.on_pair_norm_b
import Submission.Work.Diff.Alg.Q2PB.on_pair_norm_c
import Submission.Work.Diff.Alg.Q2PB.mix_diff
import Submission.Work.Diff.Alg.Q2PB.secK_smul
import Submission.Work.Diff.Alg.Q2PB.r4_bianchi

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Berger's inequality on an orthonormal four-frame (Brendle-Schoen, Corollary 22)

For an algebraic curvature tensor `R` all of whose sectional curvatures lie between `a` and `b`,
and any orthonormal four-frame `e1, e2, e3, e4`,

`|R(e1,e2,e3,e4)| <= (2/3) (b - a)`.

This is the sharp (`2/3`) form of Berger's inequality; the constant is attained by complex space
forms. It is the algebraic input that turns strict `1/4`-pinching into nonnegative complex
sectional curvature (`PIC2`, contract `A0`, `Work.Diff.Alg.quarter_to_pic2`).

## Proof

Write `K(u,v) = secK R u v` (defined for arbitrary `u`, `v`) and let `ρ = 1/sqrt 2`. For the two
"diagonal" families of planes

* `P_B^{±±} = span(ρ(e1 ± e3), ρ(e2 ± e4))`,   `P_C^{±±} = span(ρ(e1 ± e4), ρ(e2 ± e3))`

the pairs `(ρ(e1±e3), ρ(e2±e4))` and `(ρ(e1±e4), ρ(e2±e3))` are orthonormal whenever
`e1,…,e4` are (`Q2PB.on_pair_norm_b`, `Q2PB.on_pair_norm_c`), so all eight sectional curvatures lie
in `[a,b]`. The mixed second differences

`mixDiff R a b c d = R4 R (a+b) (c+d) (a+b) (c+d) - R4 R (a+b) (c-d) (a+b) (c-d)
                     - R4 R (a-b) (c+d) (a-b) (c+d) + R4 R (a-b) (c-d) (a-b) (c-d)`

expand as `8 (R4 R a c b d + R4 R a d b c)` (`Q2PB.mix_diff`), and since scaling both vectors by `ρ`
multiplies `secK` by `ρ^4 = 1/4` (`Q2PB.secK_smul`), each of the four `R4`-terms of `mixDiff` lies in
`[4a, 4b]`; hence `8(a-b) <= mixDiff R e1 e3 e2 e4 <= 8(b-a)` and likewise for `(e1,e4,e2,e3)`.

Finally the cyclic Bianchi identity (`Q2PB.r4_bianchi`) applied to `(e1,e3,e4,e2)` says
`R4 R e1 e3 e4 e2 + R4 R e1 e2 e3 e4 - R4 R e1 e4 e3 e2 = 0`, which combines with the expansions to

`6 * R4 R e1 e2 e3 e4 = (1/4) * (mixDiff R e1 e3 e2 e4 - mixDiff R e1 e4 e2 e3)`.

Bounding the two mixed differences by `± 8 (b-a)` gives `6 |R4 R e1 e2 e3 e4| <= 8 (b-a)`.
-/

namespace Work.Diff.Alg

open Submission.Diff.Alg

theorem q2p_berger {n : ℕ} (R : Submission.Diff.Alg.Curv4 n) (hR : Submission.Diff.Alg.IsAlgCurv R)
    (a b : ℝ)
    (hsec : ∀ u v : Fin n → ℝ, Submission.Diff.Alg.IsONPair u v →
      a ≤ Submission.Diff.Alg.secK R u v ∧ Submission.Diff.Alg.secK R u v ≤ b)
    {e1 e2 e3 e4 : Fin n → ℝ} (h : Work.Diff.Alg.Q2P.IsON4 e1 e2 e3 e4) :
    |Submission.Diff.Alg.R4 R e1 e2 e3 e4| ≤ (2 / 3) * (b - a) := by
  have hsq : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := by
    rw [← sq]; exact Real.sq_sqrt (by norm_num)
  have hρ : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1 / 2 := by
    rw [← mul_inv_rev, hsq]; norm_num
  have hρ4 : ((Real.sqrt 2)⁻¹) ^ 4 = 1 / 4 := by
    have h : ((Real.sqrt 2)⁻¹) ^ 4 = ((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹) ^ 2 := by ring
    rw [h, hρ]; norm_num
  have key : ∀ u v : Fin n → ℝ, IsONPair ((Real.sqrt 2)⁻¹ • u) ((Real.sqrt 2)⁻¹ • v) →
      4 * a ≤ R4 R u v u v ∧ R4 R u v u v ≤ 4 * b := by
    intro u v huv
    have hb := hsec _ _ huv
    have hk : secK R ((Real.sqrt 2)⁻¹ • u) ((Real.sqrt 2)⁻¹ • v) = (1 / 4) * R4 R u v u v := by
      rw [Q2PB.secK_smul, hρ4]
      simp only [secK]
    constructor <;> linarith [hb.1, hb.2, hk]
  -- B family: (e1 ± e3), (e2 ± e4)
  have hBpp : 4 * a ≤ R4 R (e1 + e3) (e2 + e4) (e1 + e3) (e2 + e4) ∧
      R4 R (e1 + e3) (e2 + e4) (e1 + e3) (e2 + e4) ≤ 4 * b :=
    key (e1 + e3) (e2 + e4) (by
      simpa only [one_smul] using
        (Q2PB.on_pair_norm_b h (Real.sqrt 2)⁻¹ 1 1 hρ (by norm_num) (by norm_num)))
  have hBpm : 4 * a ≤ R4 R (e1 + e3) (e2 - e4) (e1 + e3) (e2 - e4) ∧
      R4 R (e1 + e3) (e2 - e4) (e1 + e3) (e2 - e4) ≤ 4 * b :=
    key (e1 + e3) (e2 - e4) (by
      simpa only [one_smul, sub_eq_add_neg, neg_one_smul] using
        (Q2PB.on_pair_norm_b h (Real.sqrt 2)⁻¹ 1 (-1) hρ (by norm_num) (by norm_num)))
  have hBmp : 4 * a ≤ R4 R (e1 - e3) (e2 + e4) (e1 - e3) (e2 + e4) ∧
      R4 R (e1 - e3) (e2 + e4) (e1 - e3) (e2 + e4) ≤ 4 * b :=
    key (e1 - e3) (e2 + e4) (by
      simpa only [one_smul, sub_eq_add_neg, neg_one_smul] using
        (Q2PB.on_pair_norm_b h (Real.sqrt 2)⁻¹ (-1) 1 hρ (by norm_num) (by norm_num)))
  have hBmm : 4 * a ≤ R4 R (e1 - e3) (e2 - e4) (e1 - e3) (e2 - e4) ∧
      R4 R (e1 - e3) (e2 - e4) (e1 - e3) (e2 - e4) ≤ 4 * b :=
    key (e1 - e3) (e2 - e4) (by
      simpa only [one_smul, sub_eq_add_neg, neg_one_smul] using
        (Q2PB.on_pair_norm_b h (Real.sqrt 2)⁻¹ (-1) (-1) hρ (by norm_num) (by norm_num)))
  -- C family: (e1 ± e4), (e2 ± e3)
  have hCpp : 4 * a ≤ R4 R (e1 + e4) (e2 + e3) (e1 + e4) (e2 + e3) ∧
      R4 R (e1 + e4) (e2 + e3) (e1 + e4) (e2 + e3) ≤ 4 * b :=
    key (e1 + e4) (e2 + e3) (by
      simpa only [one_smul] using
        (Q2PB.on_pair_norm_c h (Real.sqrt 2)⁻¹ 1 1 hρ (by norm_num) (by norm_num)))
  have hCpm : 4 * a ≤ R4 R (e1 + e4) (e2 - e3) (e1 + e4) (e2 - e3) ∧
      R4 R (e1 + e4) (e2 - e3) (e1 + e4) (e2 - e3) ≤ 4 * b :=
    key (e1 + e4) (e2 - e3) (by
      simpa only [one_smul, sub_eq_add_neg, neg_one_smul] using
        (Q2PB.on_pair_norm_c h (Real.sqrt 2)⁻¹ 1 (-1) hρ (by norm_num) (by norm_num)))
  have hCmp : 4 * a ≤ R4 R (e1 - e4) (e2 + e3) (e1 - e4) (e2 + e3) ∧
      R4 R (e1 - e4) (e2 + e3) (e1 - e4) (e2 + e3) ≤ 4 * b :=
    key (e1 - e4) (e2 + e3) (by
      simpa only [one_smul, sub_eq_add_neg, neg_one_smul] using
        (Q2PB.on_pair_norm_c h (Real.sqrt 2)⁻¹ (-1) 1 hρ (by norm_num) (by norm_num)))
  have hCmm : 4 * a ≤ R4 R (e1 - e4) (e2 - e3) (e1 - e4) (e2 - e3) ∧
      R4 R (e1 - e4) (e2 - e3) (e1 - e4) (e2 - e3) ≤ 4 * b :=
    key (e1 - e4) (e2 - e3) (by
      simpa only [one_smul, sub_eq_add_neg, neg_one_smul] using
        (Q2PB.on_pair_norm_c h (Real.sqrt 2)⁻¹ (-1) (-1) hρ (by norm_num) (by norm_num)))
  -- bounds on the two mixed differences
  have hMB : Q2PB.mixDiff R e1 e3 e2 e4 ≤ 8 * (b - a) := by
    rw [Q2PB.mixDiff]
    linarith [hBpp.2, hBpm.1, hBmp.1, hBmm.2]
  have hMB' : 8 * (a - b) ≤ Q2PB.mixDiff R e1 e3 e2 e4 := by
    rw [Q2PB.mixDiff]
    linarith [hBpp.1, hBpm.2, hBmp.2, hBmm.1]
  have hMC : Q2PB.mixDiff R e1 e4 e2 e3 ≤ 8 * (b - a) := by
    rw [Q2PB.mixDiff]
    linarith [hCpp.2, hCpm.1, hCmp.1, hCmm.2]
  have hMC' : 8 * (a - b) ≤ Q2PB.mixDiff R e1 e4 e2 e3 := by
    rw [Q2PB.mixDiff]
    linarith [hCpp.1, hCpm.2, hCmp.2, hCmm.1]
  -- the algebraic identity
  have hid : 6 * R4 R e1 e2 e3 e4 =
      (1 / 4) * (Q2PB.mixDiff R e1 e3 e2 e4 - Q2PB.mixDiff R e1 e4 e2 e3) := by
    rw [Q2PB.mix_diff R hR e1 e3 e2 e4, Q2PB.mix_diff R hR e1 e4 e2 e3]
    have hb := Q2PB.r4_bianchi R hR e1 e3 e4 e2
    have h1 : R4 R e3 e4 e1 e2 = R4 R e1 e2 e3 e4 := Q2P.R4_pair_symm R hR e1 e2 e3 e4
    have h2 : R4 R e4 e1 e3 e2 = - R4 R e1 e4 e3 e2 := Q2P.R4_antisym₁₂ R hR e1 e4 e3 e2
    have h3 : R4 R e1 e2 e4 e3 = - R4 R e1 e2 e3 e4 := Q2P.R4_antisym₃₄ R hR e1 e2 e3 e4
    rw [h1, h2] at hb
    linarith [hb, h3]
  have h1 : 6 * R4 R e1 e2 e3 e4 ≤ 4 * (b - a) := by
    rw [hid]; linarith [hMB, hMC']
  have h2 : -(6 * R4 R e1 e2 e3 e4) ≤ 4 * (b - a) := by
    have hid2 : -(6 * R4 R e1 e2 e3 e4) =
        (1 / 4) * (Q2PB.mixDiff R e1 e4 e2 e3 - Q2PB.mixDiff R e1 e3 e2 e4) := by
      rw [hid]; ring
    rw [hid2]; linarith [hMC, hMB']
  rw [abs_le]
  constructor <;> linarith

end Work.Diff.Alg
