import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.garding_estimate
import Submission.Work.Diff.STE.garding_vec_direct
import Submission.Work.Diff.STE.commutator_estimate
import Submission.Work.Diff.STE.pdVec_contDiff_periodic
import Submission.Work.Diff.STE.ENormSq_succ_eq
import Submission.Work.Diff.STE.continuous_pdVec

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The multi-index (vector-valued) Gårding estimate

`Work.Diff.STE.garding_estimate_vec` is the `Hᵏ` form of the scalar Gårding estimate
(`DESIGN.md`, Layer A9): for a smooth periodic coefficient matrix `A` on the flat torus which is
elliptic with constant `lam`, whose first derivatives are bounded by `K₁` and whose `k`-fold
iterated derivatives are bounded by `K`, one has

  `Σ_{l : Fin k → ι} ⟨∂^l (Σ_{cd} A_{cd} ∂_c∂_d u), ∂^l u⟩_{L²}
      ≤ -(lam/4) ‖u‖²_{k+1} + C ‖u‖²_k`,

with `‖u‖²_s = ENormSq s u = Σ_{|l|=s} ∫ ‖∂^l u‖²` and `⟨f,g⟩ = L2re f g = Re ∫ f · conj g`.

The proof splits the `L²` pairing into the *direct* term, in which the `k` derivatives are put on
`u` instead of on the operator, and the *commutator*:

  `∂^l (Σ A ∂∂u) = Σ A ∂∂(∂^l u) + (∂^l (Σ A ∂∂u) - Σ A ∂∂(∂^l u))`.

* `Work.Diff.STE.garding_vec_direct` (proved in the sibling file) applies the *scalar* estimate
  `garding_estimate` to each `∂^l u` and sums: this gives the good `-(lam/2) ENormSq (k+1) u`
  term for the direct part.
* `Work.Diff.STE.commutator_estimate` bounds the commutator pairing by
  `(lam/4) ENormSq (k+1) u + C ENormSq k u`; this is where the higher derivative bounds `hK` on
  the coefficients are used.
* Adding the two bounds leaves `-(lam/4) ENormSq (k+1) u + C ENormSq k u`, as claimed.

The only glue needed is the additivity of `L2re` in its first argument (`cm_L2re_add`), which
requires the three functions involved to be continuous; this is the content of
`cont_pdVec_operator` below.
-/

namespace Work.Diff.STE

open MeasureTheory BigOperators

/-- Continuity of the three functions occurring in the `L²` pairing of the `Hᵏ` Gårding estimate:
the `k`-fold derivative of the operator applied to `u`, the `k`-fold derivative with the operator
applied outside, and the `k`-fold derivative of `u` itself.  These are exactly the hypotheses
needed to apply the additivity of `L2re` in its first argument (`cm_L2re_add`). -/
lemma cont_pdVec_operator {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ)
    (A : ι → ι → (ι → ℝ) → ℝ)
    (hA : ∀ c d, ContDiff ℝ (⊤ : ℕ∞) (A c d))
    (u : (ι → ℝ) → ℂ) (hu : ContDiff ℝ (k + 2) u) :
    ∀ l : Fin k → ι,
      Continuous (fun x => pdVec k l (fun y => ∑ c, ∑ d, A c d y * pd c (pd d u) y) x)
      ∧ Continuous (fun x => ∑ c, ∑ d, A c d x * pd c (pd d (pdVec k l u)) x)
      ∧ Continuous (pdVec k l u) := by
  intro l
  -- the `k`-fold derivative of `u` is `C²`
  have hcdl : ContDiff ℝ 2 (pdVec k l u) :=
    cm_contDiff_pdList (List.ofFn l) 2 u (by simpa using hu)
  -- the operator `y ↦ Σ_{cd} A_{cd}(y) ∂_c∂_d u(y)` is `C^k`
  have hg : ContDiff ℝ (k : ℕ) (fun y => ∑ c, ∑ d, (A c d y : ℂ) * pd c (pd d u) y) := by
    refine ContDiff.sum (fun c _ => ContDiff.sum (fun d _ => ?_))
    have h1 : ContDiff ℝ (k : ℕ) (fun y => (A c d y : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp ((hA c d).of_le (WithTop.coe_le_coe.mpr le_top))
    have h2 : ContDiff ℝ (k : ℕ) (pd c (pd d u)) :=
      cm_contDiff_pdList [c, d] k u (by simpa [Nat.add_comm] using hu)
    exact h1.mul h2
  refine ⟨continuous_pdVec k l _ hg, ?_, hcdl.continuous⟩
  -- the finite sum of the products with the operator applied outside
  refine continuous_finsetSum _ (fun c _ => continuous_finsetSum _ (fun d _ => ?_))
  have hcont : Continuous (pd c (pd d (pdVec k l u))) := by
    have h3 : Continuous (pdList [c, d] (pdVec k l u)) :=
      (cm_contDiff_pdList [c, d] 0 (pdVec k l u) (by simpa using hcdl)).continuous
    simpa [pdList] using h3
  exact (Complex.ofRealCLM.continuous.comp (hA c d).continuous).mul hcont

theorem garding_estimate_vec {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ)
    (A : ι → ι → (ι → ℝ) → ℝ)
    (hA : ∀ c d, ContDiff ℝ (⊤ : ℕ∞) (A c d)) (hAper : ∀ c d, Work.Diff.STE.Periodic1 (A c d))
    (hsym : ∀ c d x, A c d x = A d c x)
    (lam : ℝ) (hlam : 0 < lam)
    (hpos : ∀ x (ξ : ι → ℝ), lam * ∑ i, (ξ i) ^ 2 ≤ ∑ c, ∑ d, A c d x * ξ c * ξ d)
    (K₁ : ℝ) (hK₁ : ∀ c d i x, |Work.Diff.STE.pdR i (A c d) x| ≤ K₁)
    (K : ℝ) (hK : ∀ c d (l : Fin k → ι) x, |Work.Diff.STE.pdRVec k l (A c d) x| ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : (ι → ℝ) → ℂ, ContDiff ℝ (k + 2) u → Work.Diff.STE.Periodic1 u →
      (∑ l : Fin k → ι,
        Work.Diff.STE.L2re
          (fun x => Work.Diff.STE.pdVec k l
            (fun y => ∑ c, ∑ d, A c d y * Work.Diff.STE.pd c (Work.Diff.STE.pd d u) y) x)
          (Work.Diff.STE.pdVec k l u))
        ≤ -((lam / 4) * Work.Diff.STE.ENormSq (k + 1) u) + C * Work.Diff.STE.ENormSq k u := by
  obtain ⟨C1, hC1, hdir⟩ :=
    Work.Diff.STE.garding_vec_direct k A hA hAper hsym lam hlam hpos K₁ hK₁
  obtain ⟨C2, hC2, hcomm⟩ :=
    Work.Diff.STE.commutator_estimate k A hA hAper lam hlam K hK
  refine ⟨C1 + C2, by linarith, ?_⟩
  intro u hu hup
  have hcl := cont_pdVec_operator k A hA u hu
  have hcomm' := hcomm u hu hup
  -- ## The splitting of each summand into its direct part and its commutator
  have hsplit : ∀ l : Fin k → ι,
      L2re (fun x => pdVec k l (fun y => ∑ c, ∑ d, A c d y * pd c (pd d u) y) x)
          (pdVec k l u)
      = L2re (fun x => pdVec k l (fun y => ∑ c, ∑ d, A c d y * pd c (pd d u) y) x
                       - ∑ c, ∑ d, A c d x * pd c (pd d (pdVec k l u)) x) (pdVec k l u)
        + L2re (fun x => ∑ c, ∑ d, A c d x * pd c (pd d (pdVec k l u)) x) (pdVec k l u) := by
    intro l
    obtain ⟨hcF, hcH, hcg⟩ := hcl l
    have h := cm_L2re_add
      (fun x => pdVec k l (fun y => ∑ c, ∑ d, A c d y * pd c (pd d u) y) x
                        - ∑ c, ∑ d, A c d x * pd c (pd d (pdVec k l u)) x)
      (fun x => ∑ c, ∑ d, A c d x * pd c (pd d (pdVec k l u)) x) (pdVec k l u)
      (hcF.sub hcH) hcH hcg
    rw [show (fun x => (pdVec k l (fun y => ∑ c, ∑ d, A c d y * pd c (pd d u) y) x
                        - ∑ c, ∑ d, A c d x * pd c (pd d (pdVec k l u)) x)
                       + (∑ c, ∑ d, A c d x * pd c (pd d (pdVec k l u)) x))
             = fun x => pdVec k l (fun y => ∑ c, ∑ d, A c d y * pd c (pd d u) y) x from
          funext (fun x => by ring)] at h
    exact h
  have hsumsplit : (∑ l : Fin k → ι,
        L2re (fun x => pdVec k l (fun y => ∑ c, ∑ d, A c d y * pd c (pd d u) y) x)
          (pdVec k l u))
      = (∑ l : Fin k → ι,
          L2re (fun x => pdVec k l (fun y => ∑ c, ∑ d, A c d y * pd c (pd d u) y) x
                       - ∑ c, ∑ d, A c d x * pd c (pd d (pdVec k l u)) x) (pdVec k l u))
        + (∑ l : Fin k → ι,
          L2re (fun x => ∑ c, ∑ d, A c d x * pd c (pd d (pdVec k l u)) x) (pdVec k l u)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun l _ => hsplit l)
  -- ## The commutator is small (this is `commutator_estimate`)
  have hdiff_le : (∑ l : Fin k → ι,
          L2re (fun x => pdVec k l (fun y => ∑ c, ∑ d, A c d y * pd c (pd d u) y) x
                       - ∑ c, ∑ d, A c d x * pd c (pd d (pdVec k l u)) x) (pdVec k l u))
      ≤ (lam / 4) * ENormSq (k + 1) u + C2 * ENormSq k u :=
    le_trans (le_abs_self _) hcomm'
  -- ## The direct part is `-(lam/2) ENormSq (k+1) u + C₁ ENormSq k u`
  have hdir_le := hdir u hu hup
  calc (∑ l : Fin k → ι,
        L2re (fun x => pdVec k l (fun y => ∑ c, ∑ d, A c d y * pd c (pd d u) y) x)
          (pdVec k l u))
      = (∑ l : Fin k → ι,
          L2re (fun x => pdVec k l (fun y => ∑ c, ∑ d, A c d y * pd c (pd d u) y) x
                       - ∑ c, ∑ d, A c d x * pd c (pd d (pdVec k l u)) x) (pdVec k l u))
        + (∑ l : Fin k → ι,
          L2re (fun x => ∑ c, ∑ d, A c d x * pd c (pd d (pdVec k l u)) x) (pdVec k l u)) :=
        hsumsplit
    _ ≤ ((lam / 4) * ENormSq (k + 1) u + C2 * ENormSq k u)
          + (-((lam / 2) * ENormSq (k + 1) u) + C1 * ENormSq k u) :=
        add_le_add hdiff_le hdir_le
    _ = -((lam / 4) * ENormSq (k + 1) u) + (C1 + C2) * ENormSq k u := by ring

end Work.Diff.STE
