import Mathlib
import Submission.Work.BW.DefsB
import Submission.Work.BW.transl_basic
import Submission.Work.BW.vanish_span
import Submission.Work.BW.bwScale
import Submission.Work.BW.bwExtract
import Submission.Work.BW.eval_scale_homPiece
import Submission.Work.BW.ZGbigAux.eval_scalePoint_mem

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD NOTES (BW block B, phase-4 fix). Your node is `ZG_bigGen_sub_Hset`. Definitions:
Submission.Work.BW.DefsB. PHASE4_FIXES.md gives the verdicts and the proof routes.

===== PHASE4_FIXES.md (excerpt) =====

### H186 on `mem_of_vanish_ZG`: "a cone point of Z(𝔓) scaled by arbitrary λ lands back in ZG 𝔓"

**The statement is true (the owner agrees). The route claim is false only in its literal
"arbitrary λ" form.**
* **What is true and needed.** Take `𝔓` multihomogeneous and a cone point `x ∈ Z(𝔓)` with `OnG x`.
  Scale **factor by factor** by the **nonzero** `λ_i = x(i,0)⁻¹`. Each multihomogeneous component
  `G_d` of an element of `𝔓` satisfies `G_d(λx) = λ^d G_d(x) = 0`. So `λx = conePt y` with
  `y_i = x(i,1)/x(i,0) ≠ 0`, and `y ∈ ZG 𝔓`.
* **What is false.** With `λ_i = 0` the scaled point leaves `G`. With different scalars on the two
  coordinates of one `P¹` factor, the claim fails: take `𝔓 = (X₀₁ − X₀₀)` and scale only `X₀₁`.
* Points with `¬OnG x` are killed by `Π = X₀₀∏X_{i0}X_{i1}`.

### H185 on `coset_minimalPrime`

2. `ZG p ⊆ Z_G(J') ⊆ H_V(0)`, by **`ZG_bigGen_sub_Hset`** (new; this is where `mem_of_vanish_ZG`
   enters). -/

namespace Work.BW

open MvPolynomial

/-! ## Auxiliary lemmas -/

/-- `List.foldr` of the constant identity function. -/
private lemma list_foldr_id {α β : Type*} (l : List α) (b : β) :
    l.foldr (fun _ x => x) b = b := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.foldr_cons]; exact ih

/-- `applyH` at the zero multi-index is the identity. -/
private lemma applyH_zero_pt {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (F : MR N) :
    applyH w (0 : Fin q → ℕ) F = F := by
  rw [applyH]
  have hf : (fun (m : Fin q) (Q : MR N) => (derH (w m))^[((0 : Fin q → ℕ) m)] Q)
      = fun _ Q => Q := by
    funext m Q
    simp
  rw [hf]
  exact list_foldr_id _ _

/-- `gmul` is commutative. -/
private lemma gmul_comm {N : ℕ} (a b : Fin (N + 1) → ℂ) : gmul a b = gmul b a := by
  funext j
  refine Fin.cases ?_ ?_ j
  · simp only [gmul, Fin.cons_zero]; ring
  · intro i; simp only [gmul, Fin.cons_succ]; ring

/-- A right fold of maps preserving a set stays in the set. -/
private lemma foldr_mem {N : ℕ} {α : Type*} (f : α → MR N → MR N) (S : Set (MR N))
    (hf : ∀ a, ∀ x ∈ S, f a x ∈ S) (l : List α) {x : MR N} (hx : x ∈ S) :
    l.foldr f x ∈ S := by
  induction l with
  | nil => exact hx
  | cons a l ih => rw [List.foldr_cons]; exact hf a _ ih

/-- The multidegree `a • eᵢ + b • eᵢ` is `(a+b) • eᵢ`. -/
private lemma smul_single_add {N : ℕ} (i : Fin (N + 1)) (a b : ℕ) :
    a • (Finsupp.single i 1 : Fin (N + 1) →₀ ℕ) + b • Finsupp.single i 1
      = Finsupp.single i (a + b) := by
  rw [← add_smul, Finsupp.smul_single]
  simp

/-- Pointwise application of `fsD`. -/
private lemma fsD_apply {N : ℕ} (D : Fin (N + 1) → ℕ) (j : Fin (N + 1)) :
    (fsD D) j = D j :=
  congrFun (Finsupp.coe_equivFunOnFinite_symm D) j

/-- `fsD D` is the sum of the single multidegrees `D i • eᵢ`. -/
private lemma sum_single_fsD {N : ℕ} (D : Fin (N + 1) → ℕ) :
    (∑ i : Fin (N + 1), Finsupp.single i (D i)) = fsD D := by
  apply Finsupp.ext
  intro j
  rw [fsD_apply, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single j]
  · rw [Finsupp.single_eq_same]
  · intro b _ hb
    rw [Finsupp.single_eq_of_ne (Ne.symm hb)]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- The homogenisation of `P` to multidegree `D` is multihomogeneous of multidegree `D`
(only true when `P` is of multidegree `≤ D`). -/
private lemma homog_mem_homPiece {N : ℕ} (D : Fin (N + 1) → ℕ)
    (P : MvPolynomial (Fin (N + 1)) ℂ) (hdeg : ∀ i, P.degreeOf i ≤ D i) :
    homog D P ∈ homPiece N (fsD D) := by
  rw [← sum_single_fsD D, homPiece, MvPolynomial.mem_weightedHomogeneousSubmodule, homog]
  refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ ?_
  intro s hs
  refine MvPolynomial.IsWeightedHomogeneous.C_mul ?_ _
  refine MvPolynomial.IsWeightedHomogeneous.prod _ _ _ ?_
  intro i _
  have hs' : s i ≤ D i := (MvPolynomial.degreeOf_le_iff.mp (hdeg i)) s hs
  have h1 : MvPolynomial.IsWeightedHomogeneous (mdeg N)
      ((MvPolynomial.X ((i : Fin (N + 1)), (1 : Fin 2)) : MR N) ^ (s i))
      (s i • (Finsupp.single i 1 : Fin (N + 1) →₀ ℕ)) := by
    simpa [mdeg] using
      ((MvPolynomial.isWeightedHomogeneous_X (R := ℂ) (mdeg N)
        ((i : Fin (N + 1)), (1 : Fin 2))).pow (s i))
  have h0 : MvPolynomial.IsWeightedHomogeneous (mdeg N)
      ((MvPolynomial.X ((i : Fin (N + 1)), (0 : Fin 2)) : MR N) ^ (D i - s i))
      ((D i - s i) • (Finsupp.single i 1 : Fin (N + 1) →₀ ℕ)) := by
    simpa [mdeg] using
      ((MvPolynomial.isWeightedHomogeneous_X (R := ℂ) (mdeg N)
        ((i : Fin (N + 1)), (0 : Fin 2))).pow (D i - s i))
  have hwt : s i • (Finsupp.single i 1 : Fin (N + 1) →₀ ℕ)
      + (D i - s i) • Finsupp.single i 1 = Finsupp.single i (D i) := by
    rw [smul_single_add, Nat.add_sub_cancel' hs']
  have h := h1.mul h0
  rwa [hwt] at h

/-- `X_{0,0} ∂/∂X_{0,1}` maps a monomial to a monomial of the same multidegree. -/
private lemma X00_pderiv01_monomial_isWH {N : ℕ} (m : (Fin (N + 1) × Fin 2) →₀ ℕ) (c : ℂ) :
    MvPolynomial.IsWeightedHomogeneous (mdeg N)
      (MvPolynomial.X ((0 : Fin (N + 1)), (0 : Fin 2)) *
        MvPolynomial.pderiv ((0 : Fin (N + 1)), (1 : Fin 2)) (MvPolynomial.monomial m c))
      (Finsupp.weight (mdeg N) m) := by
  by_cases h : m ((0 : Fin (N + 1)), (1 : Fin 2)) = 0
  · rw [MvPolynomial.pderiv_monomial, h, Nat.cast_zero, mul_zero,
      MvPolynomial.monomial_zero, mul_zero]
    exact MvPolynomial.isWeightedHomogeneous_zero ℂ (mdeg N) _
  · have hX : MvPolynomial.X ((0 : Fin (N + 1)), (0 : Fin 2)) =
        MvPolynomial.monomial (Finsupp.single ((0 : Fin (N + 1)), (0 : Fin 2)) 1) (1 : ℂ) := by
      simpa using (MvPolynomial.X_pow_eq_monomial (R := ℂ)
        (n := ((0 : Fin (N + 1)), (0 : Fin 2))) (e := 1))
    rw [MvPolynomial.pderiv_monomial, hX, MvPolynomial.monomial_mul_monomial, one_mul]
    refine MvPolynomial.isWeightedHomogeneous_monomial _ _ _ ?_
    have hwe : Finsupp.weight (mdeg N) (Finsupp.single ((0 : Fin (N + 1)), (0 : Fin 2)) 1) =
        Finsupp.weight (mdeg N) (Finsupp.single ((0 : Fin (N + 1)), (1 : Fin 2)) 1) := by
      rw [Finsupp.weight_single, Finsupp.weight_single]
      simp [mdeg]
    have h1 : Finsupp.weight (mdeg N)
          (m - Finsupp.single ((0 : Fin (N + 1)), (1 : Fin 2)) 1)
        + Finsupp.weight (mdeg N) (Finsupp.single ((0 : Fin (N + 1)), (1 : Fin 2)) 1)
        = Finsupp.weight (mdeg N) m := by
      rw [← map_add, Finsupp.sub_add_single_one_cancel h]
    rw [map_add, hwe, add_comm (Finsupp.weight (mdeg N)
      (Finsupp.single ((0 : Fin (N + 1)), (1 : Fin 2)) 1)), h1]

/-- `derH` is additive. -/
private lemma derH_add {N : ℕ} (v : Fin (N + 1) → ℂ) (a b : MR N) :
    derH v (a + b) = derH v a + derH v b := by
  simp only [derH, map_add, mul_add, Finset.sum_add_distrib]
  abel

/-- The invariant derivation `derH v` preserves every multidegree piece. -/
private lemma derH_mem_homPiece {N : ℕ} (v : Fin (N + 1) → ℂ) {d : Fin (N + 1) →₀ ℕ}
    {F : MR N} (hF : F ∈ homPiece N d) : derH v F ∈ homPiece N d := by
  rw [homPiece, MvPolynomial.mem_weightedHomogeneousSubmodule] at hF ⊢
  induction hF using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero =>
    rw [show derH v (0 : MR N) = 0 from by simp [derH]]
    exact MvPolynomial.isWeightedHomogeneous_zero ℂ (mdeg N) d
  | add p q hp hq ihp ihq =>
    rw [derH_add]
    exact ihp.add ihq
  | monomial m c hm =>
    rw [← hm]
    simp only [derH, mul_assoc]
    refine MvPolynomial.IsWeightedHomogeneous.add ?_ ?_
    · refine MvPolynomial.IsWeightedHomogeneous.C_mul ?_ _
      exact X00_pderiv01_monomial_isWH m c
    · refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ ?_
      intro i _
      refine MvPolynomial.IsWeightedHomogeneous.C_mul ?_ _
      rw [MvPolynomial.X_mul_pderiv_monomial, MvPolynomial.smul_monomial]
      exact MvPolynomial.isWeightedHomogeneous_monomial _ _ _ rfl

/-- Iterated `derH` preserves every multidegree piece. -/
private lemma derH_iterate_mem {N : ℕ} (v : Fin (N + 1) → ℂ) (k : ℕ)
    {d : Fin (N + 1) →₀ ℕ} {F : MR N} (hF : F ∈ homPiece N d) :
    (derH v)^[k] F ∈ homPiece N d := by
  induction k with
  | zero => simpa using hF
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact derH_mem_homPiece v ih

/-- `applyH` preserves every multidegree piece. -/
private lemma applyH_mem_homPiece {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (t : Fin q → ℕ)
    {d : Fin (N + 1) →₀ ℕ} {F : MR N} (hF : F ∈ homPiece N d) :
    applyH w t F ∈ homPiece N d := by
  rw [applyH]
  exact foldr_mem (fun m Q => (derH (w m))^[t m] Q) (homPiece N d : Set (MR N))
    (fun m x hx => derH_iterate_mem (w m) (t m) hx) (List.finRange q) hF

/-- Every generator of Philippon's `I_r` is multihomogeneous of multidegree `D`. -/
private theorem chainGen_mem_homPiece {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (θ : Fin N → ℂ)
    (D : Fin (N + 1) → ℕ) (P : MvPolynomial (Fin (N + 1)) ℂ) (A B : ℕ)
    (hdeg : ∀ i, P.degreeOf i ≤ D i) {Q : MR N} (hQ : Q ∈ chainGen w θ D P A B) :
    Q ∈ homPiece N (fsD D) := by
  obtain ⟨s, t, hs, ht, rfl⟩ := hQ
  exact (transl_basic (ptTheta θ s) (ptTheta θ s)).2.2.2.1 (fsD D) _
    (applyH_mem_homPiece w t (homog_mem_homPiece D P hdeg))

/-- The product `X₀₀ ∏_{i ≥ 1} X_{i0} X_{i1}`, which vanishes at every point of `(P¹)^{N+1}`
having a vanishing coordinate. -/
private noncomputable def PiP {N : ℕ} : MR N :=
  MvPolynomial.X ((0 : Fin (N + 1)), (0 : Fin 2)) *
    ∏ i : Fin N,
      (MvPolynomial.X ((i.succ : Fin (N + 1)), (0 : Fin 2)) *
        MvPolynomial.X ((i.succ : Fin (N + 1)), (1 : Fin 2)))

/-- `Π` vanishes at points off the affine cone over `G`. -/
private lemma eval_PiP_eq_zero_of_not_OnG {N : ℕ} {x : Fin (N + 1) × Fin 2 → ℂ}
    (hx : ¬ OnG N x) : MvPolynomial.eval x (PiP (N := N)) = 0 := by
  have hprod : MvPolynomial.eval x (PiP (N := N)) =
      x (0, 0) * ∏ i : Fin N, (x (i.succ, 0) * x (i.succ, 1)) := by
    simp only [PiP, map_mul, map_prod, MvPolynomial.eval_X]
  rw [hprod]
  rcases eq_or_ne (x (0, 0)) 0 with h0 | h0
  · rw [h0, zero_mul]
  · have hg : ∃ i : Fin N, x (i.succ, 0) * x (i.succ, 1) = 0 := by
      by_contra h
      push_neg at h
      exact hx ⟨h0, fun i => mul_ne_zero_iff.mp (h i)⟩
    obtain ⟨i, hi⟩ := hg
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hi, mul_zero]

/-- `Π` does not lie in a prime ideal meeting `G` on the cone. -/
private lemma PiP_notMem_of_meetsG {N : ℕ} (𝔓 : Ideal (MR N)) (hG : MeetsG N 𝔓) :
    PiP (N := N) ∉ 𝔓 := by
  obtain ⟨x, hxG, hxle⟩ := hG
  intro hP
  have hzero : MvPolynomial.eval x (PiP (N := N)) = 0 := by
    have h1 : PiP (N := N) ∈ ptIdeal N x := hxle hP
    rwa [ptIdeal, RingHom.mem_ker] at h1
  have hne : MvPolynomial.eval x (PiP (N := N)) ≠ 0 := by
    have hprod : MvPolynomial.eval x (PiP (N := N)) =
        x (0, 0) * ∏ i : Fin N, (x (i.succ, 0) * x (i.succ, 1)) := by
      simp only [PiP, map_mul, map_prod, MvPolynomial.eval_X]
    rw [hprod]
    exact mul_ne_zero hxG.1
      (Finset.prod_ne_zero_iff.mpr fun i _ => mul_ne_zero (hxG.2 i).1 (hxG.2 i).2)
  exact hne hzero

/-- B1e (Nullstellensatz on the cone, relative to `G`). A multihomogeneous `F` over a
multihomogeneous prime `𝔓` meeting `G`, vanishing at all cone points over `ZG 𝔓`, lies in `𝔓`. -/
private theorem mem_of_vanish_ZG_aux {N : ℕ} (𝔓 : Ideal (MR N)) (h𝔓 : 𝔓.IsPrime)
    (hH : MultiHom N 𝔓) (hG : MeetsG N 𝔓) (F : MR N) (hFh : ∃ d, F ∈ homPiece N d)
    (hFv : ∀ v ∈ ZG 𝔓, MvPolynomial.eval (conePt N v) F = 0) : F ∈ 𝔓 := by
  haveI : 𝔓.IsPrime := h𝔓
  have hvan : PiP (N := N) * F ∈ 𝔓 := by
    have hmem : PiP (N := N) * F ∈
        MvPolynomial.vanishingIdeal ℂ (MvPolynomial.zeroLocus ℂ 𝔓) := by
      rw [MvPolynomial.mem_vanishingIdeal_iff]
      intro x hx
      rw [MvPolynomial.aeval_eq_eval]
      by_cases hxG : OnG N x
      · obtain ⟨dF, hFmem⟩ := hFh
        have hx0 : ∀ i : Fin (N + 1), x (i, 0) ≠ 0 := by
          intro i
          obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ i
          · exact hxG.1
          · exact (hxG.2 j).1
        have hcone : ∀ v : Fin (N + 1) × Fin 2,
            conePt N (fun i : Fin (N + 1) => x (i, 1) / x (i, 0)) v
              = (x (v.1, 0))⁻¹ * x v := by
          intro v
          obtain ⟨i, b⟩ := v
          fin_cases b <;> simp [conePt, div_eq_inv_mul, inv_mul_cancel₀ (hx0 i)]
        have hxval : ∀ H ∈ 𝔓, MvPolynomial.eval x H = 0 := by
          intro H hHmem
          have h := (MvPolynomial.mem_zeroLocus_iff.mp hx) H hHmem
          simpa [MvPolynomial.aeval_eq_eval] using h
        have hyvZG : (fun i : Fin (N + 1) => x (i, 1) / x (i, 0)) ∈ ZG 𝔓 := by
          refine ⟨fun i => div_ne_zero (hxG.2 i).2 (hxG.2 i).1, ?_⟩
          intro G hGmem
          have hfun : conePt N (fun i : Fin (N + 1) => x (i, 1) / x (i, 0)) =
              fun v : Fin (N + 1) × Fin 2 => (x (v.1, 0))⁻¹ * x v := funext hcone
          rw [hfun]
          exact ZGbigAux.eval_scalePoint_mem 𝔓 hH (fun i : Fin (N + 1) => (x (i, 0))⁻¹)
            x hxval G hGmem
        have hx_eq : x = fun v : Fin (N + 1) × Fin 2 =>
            x (v.1, 0) * conePt N (fun i : Fin (N + 1) => x (i, 1) / x (i, 0)) v := by
          funext v
          rw [hcone v, ← mul_assoc, mul_inv_cancel₀ (hx0 v.1), one_mul]
        rw [MvPolynomial.eval_mul, hx_eq,
          eval_scale_homPiece dF F hFmem (fun i : Fin (N + 1) => x (i, 0))
            (conePt N (fun i : Fin (N + 1) => x (i, 1) / x (i, 0))),
          hFv (fun i : Fin (N + 1) => x (i, 1) / x (i, 0)) hyvZG, mul_zero, mul_zero]
      · rw [MvPolynomial.eval_mul, eval_PiP_eq_zero_of_not_OnG hxG, zero_mul]
    rwa [MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := ℂ) 𝔓] at hmem
  rcases h𝔓.mem_or_mem hvan with h | h
  · exact absurd h (PiP_notMem_of_meetsG 𝔓 hG)
  · exact h

/-- Phase 4 helper for `coset_minimalPrime` (`Z(J') ∩ G ⊆ H_V(0)`, the density step H185 asked
for). If every generator `τ_v Q` of `J'` vanishes at the cone point over `y ∈ G`, then for each
`Q ∈ chainGen` the multihomogeneous `τ_y Q` vanishes on the cone points over `ZG 𝔓`, so
`τ_y Q ∈ 𝔓` by `mem_of_vanish_ZG` (this is where Zariski density of `ZG 𝔓` enters); pass to the
span since `τ_y` is a ring map. Size 0.5–0.8k. -/
theorem ZG_bigGen_sub_Hset {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (θ : Fin N → ℂ)
    (D : Fin (N + 1) → ℕ) (P : MvPolynomial (Fin (N + 1)) ℂ) (hdeg : ∀ i, P.degreeOf i ≤ D i)
    (A B : ℕ) (𝔓 : Ideal (MR N)) (h𝔓 : 𝔓.IsPrime) (hH : MultiHom N 𝔓) (hG : MeetsG N 𝔓)
    (y : Fin (N + 1) → ℂ) (hy : InG y)
    (h : ∀ F ∈ bigGen w θ D P A B 𝔓, MvPolynomial.eval (conePt N y) F = 0) :
    y ∈ Hset w 𝔓 (chainIdeal w θ D P A B) 0 := by
  refine ⟨hy, ?_⟩
  intro F hF t ht
  refine vanish_span w y 0 𝔓 (chainGen w θ D P A B) ?_ F hF t ht
  intro Q hQ t ht
  have ht0 : t = 0 := by
    funext k
    exact Nat.eq_zero_of_le_zero
      (le_trans (Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ k)) ht)
  rw [ht0, applyH_zero_pt]
  refine mem_of_vanish_ZG_aux 𝔓 h𝔓 hH hG (transl y Q) ⟨fsD D, ?_⟩ ?_
  · exact (transl_basic y y).2.2.2.1 (fsD D) Q (chainGen_mem_homPiece w θ D P A B hdeg hQ)
  · intro v hv
    have hbig : transl v Q ∈ bigGen w θ D P A B 𝔓 := ⟨v, hv, Q, hQ, rfl⟩
    have h1 : MvPolynomial.eval (conePt N v) (transl y Q) =
        MvPolynomial.eval (conePt N (gmul y v)) Q := by
      rw [(transl_basic y y).1 (conePt N v) Q, (transl_basic y y).2.1 v]
    have h2 : MvPolynomial.eval (conePt N y) (transl v Q) =
        MvPolynomial.eval (conePt N (gmul v y)) Q := by
      rw [(transl_basic v v).1 (conePt N y) Q, (transl_basic v v).2.1 y]
    rw [h1, gmul_comm y v, ← h2]
    exact h (transl v Q) hbig

end Work.BW
