import Mathlib
import Submission.Work.ORLyndon.CLDirect.cldDefs
import Submission.Work.ORLyndon.CLDirect.presentAlg_foxD_conj
import Submission.Work.ORLyndon.CLDirect.clPhi_mul
import Submission.Work.ORLyndon.CLDirect.clPhi_conj_pow
import Submission.Work.ORLyndon.CLDirect.clPhi_conj
import Submission.Work.ORLyndon.CLDirect.foxKernel_vanish
import Submission.Work.ORLyndon.CLDirect.orderOf_presentRho_of_clData
import Submission.Work.ORLyndon.CLDirect.coeffs_zero_of_sum_mul_normElem

/-!
# The Cohen--Lyndon basis implies `LyndonIndependence` (unit D3)

`Work.ORLyndon.CLDirect.lyndonIndependence_of_clData`: from the Cohen--Lyndon data `CLData u`
(N4's basis theorem) and `1 ≤ l`, the classes `g • (∂(u^l)/∂x)_x` attached to pairwise distinct
`⟨u⟩`-cosets are `K`-linearly independent — the module form of the Cohen--Lyndon theorem.

The proof uses the crossed homomorphism `clPhi` of `cldDefs.lean` (additive on `⟪u^l⟫` by
`clPhi_mul`, equivariant under conjugation by `clPhi_conj`, and satisfying
`clPhi (f u^l f⁻¹) = f̄ · N_w` by `clPhi_conj_pow`), the Fox-kernel (Magnus embedding) lemma
`foxKernel_vanish`, the order statement `orderOf_presentRho_of_clData` and the coefficient count
`coeffs_zero_of_sum_mul_normElem`.
-/

set_option autoImplicit false

namespace Work.ORLyndon.CLDirect

open MonoidAlgebra

universe u v

variable {X : Type u} [DecidableEq X] {K : Type v} [Field K]

theorem lyndonIndependence_of_clData {u : FreeGroup X} (D : CLData u) (l : ℕ) (hl : 1 ≤ l) :
    Work.ORLyndon.LyndonIndependence K (u ^ l) u := by
  classical
  intro ι _ g c hdist hsum
  -- Lifts of the `g i` along the presentation, and the corresponding conjugates of the relator.
  let f : ι → FreeGroup X := fun i => presentSec (u ^ l) (g i)
  let ρ : ι → FreeGroup X := fun i => f i * u ^ l * (f i)⁻¹
  have hf : ∀ i, presentRho (u ^ l) (f i) = g i := fun i =>
    Function.surjInv_eq (PresentedGroup.mk_surjective ({u ^ l} : Set (FreeGroup X))) (g i)
  have hρ : ∀ i, ρ i ∈ Subgroup.normalClosure ({u ^ l} : Set (FreeGroup X)) := fun i =>
    (Subgroup.normalClosure_normal (s := ({u ^ l} : Set (FreeGroup X)))).conj_mem (u ^ l)
      (Subgroup.subset_normalClosure (Set.mem_singleton _)) (f i)
  -- The hypothesis of the Fox-kernel lemma, obtained from `hsum` by evaluating at `x`.
  have hx : ∀ x : X,
      ∑ i, c i • presentAlg K (u ^ l) (foxD (K := K) x (ρ i)) = 0 := by
    intro x
    have h1 : (∑ i, c i • (MonoidAlgebra.of K (OneRelatorGroup (u ^ l)) (g i) •
        relatorVec K (u ^ l))) x = 0 := by
      rw [hsum]
      simp
    simp only [Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul] at h1
    calc ∑ i, c i • presentAlg K (u ^ l) (foxD (K := K) x (ρ i))
        = ∑ i, c i • (MonoidAlgebra.of K (OneRelatorGroup (u ^ l)) (g i) *
            relatorVec K (u ^ l) x) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [presentAlg_foxD_conj (K := K) (u ^ l) (f i) x, hf i]
      _ = 0 := h1
  -- The Fox-kernel lemma.
  have hphi : ∑ i, c i • clPhi (K := K) D l (ρ i) = 0 :=
    foxKernel_vanish (K := K) (u ^ l) (clPhi (K := K) D l)
      (fun n n' hn hn' => clPhi_mul (K := K) D l hn hn')
      (fun f' n hn => clPhi_conj (K := K) D l f' hn)
      ι ρ hρ c hx
  -- Rewrite with `clPhi_conj_pow` to obtain the product with the norm element.
  have hnorm : (∑ i, c i • MonoidAlgebra.of K (OneRelatorGroup (u ^ l)) (g i)) *
      Work.ORLyndon.normElem K l (presentRho (u ^ l) u) = 0 := by
    have key : (∑ i, c i • MonoidAlgebra.of K (OneRelatorGroup (u ^ l)) (g i)) *
        Work.ORLyndon.normElem K l (presentRho (u ^ l) u) =
        ∑ i, c i • clPhi (K := K) D l (ρ i) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      show (c i • MonoidAlgebra.of K (OneRelatorGroup (u ^ l)) (g i)) *
          Work.ORLyndon.normElem K l (presentRho (u ^ l) u) = c i • clPhi (K := K) D l (ρ i)
      rw [Algebra.smul_mul_assoc]
      congr 1
      rw [show ρ i = f i * u ^ l * (f i)⁻¹ from rfl, clPhi_conj_pow (K := K) D l (f i), hf i]
    rw [key, hphi]
  exact coeffs_zero_of_sum_mul_normElem (u ^ l) u l hl (orderOf_presentRho_of_clData D l hl)
    ι g c hdist hnorm

end Work.ORLyndon.CLDirect
