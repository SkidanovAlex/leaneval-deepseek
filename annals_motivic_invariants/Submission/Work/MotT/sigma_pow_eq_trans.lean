import Mathlib
import Submission.Work.MotT.T4Setup
import Submission.Work.MotT.AM2_descent
import Submission.Work.MotT.c2_over_ML2
import Submission.Work.MotT.algEquiv_eq_one_of_kleinCoord_ratio
import Submission.Work.MotC2.Translation
import Submission.Work.MotC2.Negation
import Submission.Work.MotC2.negAlgEquiv_mul_transAlgEquiv

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotT

open WeierstrassCurve WeierstrassCurve.Affine

/-- The `K`-linear automorphism `AM2_sigmaK` of `M = L(E)` is the restriction of scalars of the
`L`-linear `AM2_sigma`, so their powers agree on the nose. -/
theorem AM2_sigmaK_pow_apply {K : Type} [Field K] (D : Work.MotV.KleinData K) (hD : D.Good)
    (h₁ h₂ : K) (hk : ringChar K ≠ 5) :
    ∀ (m : ℕ) (x : ML2 D h₁ h₂ hk),
      ((AM2_sigmaK D hD h₁ h₂ hk) ^ m) x = ((AM2_sigma D hD h₁ h₂ hk) ^ m) x := by
  intro m
  induction m with
  | zero => intro x; rfl
  | succ m ih =>
    intro x
    rw [pow_succ, pow_succ, AlgEquiv.mul_apply, AlgEquiv.mul_apply, AM2_sigmaK_apply]
    exact ih _

/-- Purely group-theoretic: if `b` conjugates `a` to `c`, `a * c = 1` and `b ^ 2 = 1`, then
`(a * b) ^ 2 = 1`. -/
theorem mul_self_mul_self_eq_one_of_conj_mul {G : Type*} [Group G] {a b c : G}
    (hab : b * a = c * b) (hac : a * c = 1) (hbb : b * b = 1) : (a * b) * (a * b) = 1 := by
  calc (a * b) * (a * b) = a * (b * a) * b := by group
    _ = a * (c * b) * b := by rw [hab]
    _ = (a * c) * (b * b) := by group
    _ = 1 := by rw [hac, hbb, one_mul]

/-- Purely group-theoretic: in a group, `g ^ 2 = 1` and `g ^ 5 = 1` force `g = 1`. -/
theorem eq_one_of_sq_eq_one_of_pow_five_eq_one {G : Type*} [Group G] {g : G}
    (h2 : g ^ 2 = 1) (h5 : g ^ 5 = 1) : g = 1 := by
  have hg : g ^ 5 = g := by
    rw [show (5 : ℕ) = 2 * 2 + 1 by norm_num, pow_add, pow_mul, h2, one_pow, one_mul, pow_one]
  rw [← hg]; exact h5

/-- **Every power of the diagonal automorphism is a pure translation.**

`AM2_sigma D hD h₁ h₂ hk` is the diagonal automorphism `Δ_ζ` of `M = L(E)` given by
`KleinData.Good.T_diag` at the primitive fifth root of unity `zL2 K h₁ h₂ hk` (`L = K(ζ, w₁, w₂)`);
it scales the Klein ratios by `ζ^i` (`Work.MotT.AM2_sigma_kleinCoord`).  For every `k : ℕ` its
`k`-th power is a *pure translation* of the curve: there is a point `A` of `E(L)` with
`Δ_ζ^k = τ_A`.

This is the fact that makes the LAM arithmetic step work: the twisted Galois action is
`ρ_γ = Δ_{c(γ)} ∘ γ̃` (`Work.MotT.AM2_rhoFun`) and the LAM comparison
`Θ ρ_γ^{(1)} = ρ_γ^{(2)} Θ` can only be turned into a *point* relation
(`γQ - Q = ...`) if the `[-1]`-part of `Δ_{c(γ)}` is known to be trivial.

Route.  Let `S := (AM2_sigma)^k`.
1. `S ^ 5 = 1`.  By induction from `AM2_sigma_kleinCoord`, `S` acts on every Klein ratio
   `κ_i/κ_0` by multiplication by `ζ^{k*5*i} = 1` (`(zL2)^5 = 1`), and an `L`-algebra automorphism
   of `M = L(E)` acting trivially on all the ratios `κ_i/κ_0` is the identity: the ratios generate
   `M` over `L` directly from `KleinData.Good.spans` and `KleinData.Good.coord0_ne`
   (`kleinBas D L m = ∑_i e m i • kleinCoord D L i`, so `genX = κ_0 · ∑_i e 1 i • (κ_i/κ_0)`
   lies in `L(κ_i/κ_0)`, and likewise `genY`); no twisting fifth root `w` and hence no
   `h₁ ≠ 0` hypothesis is needed.
2. Node C2 over `L` (`Work.MotT.c2_over_ML2`) gives `S = τ_Q * [-1]^ε` with `ε : Fin 2`.
3. If `ε = 1` then `S ^ 2 = (τ_Q * [-1]) ^ 2 = 1`: `[-1] * τ_A = τ_{-A} * [-1]`
   (conjugation, `Work.MotC2.negAlgEquiv_mul_transAlgEquiv` / the `TransData` laws) and
   `τ_A * τ_{-A} = 1` (`Work.MotC2.transAlgEquiv_add`, `transAlgEquiv_zero`); combined with
   `S ^ 5 = 1` this forces `S = S ^ 6 * (S ^ 5)⁻¹ = 1 = τ_0` (`transAlgEquiv_zero`).
4. If `ε = 0` then `S = τ_Q`. -/
theorem sigma_pow_eq_trans {K : Type} [Field K] (D : Work.MotV.KleinData K) (hD : D.Good)
    (h₁ h₂ : K) (hk : ringChar K ≠ 5)
    [instDec : DecidableEq ↥(KummerField2 K h₁ h₂ hk)]
    [instEll : (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)).IsElliptic] (k : ℕ) :
    ∃ A : (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)).toAffine.Point,
      (AM2_sigma D hD h₁ h₂ hk) ^ k =
        Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) A := by
  -- Step 1: the `5`-th power of the diagonal automorphism is the identity.
  have hσ5k : (AM2_sigma D hD h₁ h₂ hk) ^ (5 * k) = 1 := by
    refine algEquiv_eq_one_of_kleinCoord_ratio D hD h₁ h₂ hk _ (fun i => ?_)
    rw [← AM2_sigmaK_pow_apply D hD h₁ h₂ hk (5 * k)]
    rw [AM2_sigmaK_pow_ratio D hD h₁ h₂ hk (5 * k) i]
    have hζ : (algebraMap ↥(KummerField2 K h₁ h₂ hk) (ML2 D h₁ h₂ hk)
        (zL2 K h₁ h₂ hk)) ^ 5 = 1 := by
      rw [← map_pow, (zL2_isPrimitiveRoot K h₁ h₂ hk).pow_eq_one, map_one]
    rw [show (i : ℕ) * (5 * k) = 5 * ((i : ℕ) * k) by ring, pow_mul, hζ, one_pow, one_mul]
  -- hence also `S ^ 5 = 1` for `S = (AM2_sigma) ^ k`.
  have hS5 : ((AM2_sigma D hD h₁ h₂ hk) ^ k) ^ 5 = 1 := by
    rw [← pow_mul, Nat.mul_comm k 5, hσ5k]
  -- Step 2: node C2 over `L`.
  obtain ⟨Q, ε, hQ⟩ := c2_over_ML2 D hD h₁ h₂ hk ((AM2_sigma D hD h₁ h₂ hk) ^ k)
  have hnn : Work.MotC2.negAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) *
      Work.MotC2.negAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) = 1 :=
    Work.MotC2.negAlgEquiv_mul_self _
  fin_cases ε
  · -- Step 4: `ε = 0`, so `S = τ_Q` is a pure translation.
    refine ⟨Q, ?_⟩
    rw [hQ]
    norm_num
  · -- Step 3: `ε = 1`, so `S = τ_Q * [-1]`; then `S ^ 2 = 1`, and `S ^ 5 = 1` forces `S = 1`.
    have hconj : Work.MotC2.negAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) *
        Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) Q =
        Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) (-Q) *
        Work.MotC2.negAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) :=
      Work.MotC2.negAlgEquiv_mul_transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) Q
    have h1 : Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) Q *
        Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) (-Q) = 1 := by
      rw [← Work.MotC2.transAlgEquiv_add, add_neg_cancel, Work.MotC2.transAlgEquiv_zero]
    have hQ' : (AM2_sigma D hD h₁ h₂ hk) ^ k =
        Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) Q *
        Work.MotC2.negAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) := by
      simpa using hQ
    have h2 : ((AM2_sigma D hD h₁ h₂ hk) ^ k) ^ 2 = 1 := by
      rw [hQ', pow_two]
      exact mul_self_mul_self_eq_one_of_conj_mul hconj h1 hnn
    have hS1 : (AM2_sigma D hD h₁ h₂ hk) ^ k = 1 :=
      eq_one_of_sq_eq_one_of_pow_five_eq_one h2 hS5
    exact ⟨0, by rw [hS1, Work.MotC2.transAlgEquiv_zero]⟩

end Work.MotT
