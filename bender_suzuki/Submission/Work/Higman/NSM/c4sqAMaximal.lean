import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.Basic
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.lemma9_maximal_abelian
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.RedAux.abelian_case

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped commutatorElement

namespace Work.Higman.NSM

variable {P : Type} [Group P] [Finite P]

/-- **The dichotomy for the `C₄` configuration.**  If `A` is abelian, `ξ`-invariant, with
`A² = Ω₁(P)` and `A⁴ = ⊥`, then every `ξ`-invariant subgroup of `A` is `⊥`, `A²` or `A`.

This is Higman's Lemma 1 (`Work.Higman.homogeneous_structure`): the `ξ`-invariant subgroups of
`A` are the power subgroups `A ^ (2 ^ i)`, and only `i = 0`, `i = 1` and `i ≥ 2` occur, the last
giving `⊥` because `A ^ 4 = ⊥`. -/
theorem c4_xi_inv_trichotomy (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    {B : Subgroup P} (hBA : B ≤ A) (hBin : B.map (h.xi : MulAut P).toMonoidHom = B) :
    B = ⊥ ∨ B = Work.Higman.powSub A 2 ∨ B = A := by
  obtain ⟨e, -, -, -, hsub⟩ := Work.Higman.homogeneous_structure h hAab hAxi
  obtain ⟨i, hi⟩ := hsub B hBA hBin
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · refine Or.inr (Or.inr ?_)
    rw [hi, h0, pow_zero, Work.Higman.powSub_one_eq]
  · rcases Nat.lt_or_ge i 2 with hlt | hge
    · refine Or.inr (Or.inl ?_)
      have hi1 : i = 1 := by omega
      rw [hi, hi1]; norm_num
    · refine Or.inl ?_
      rw [hi]
      have hdvd : 4 ∣ 2 ^ i := ⟨2 ^ (i - 2), by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega⟩
      exact le_bot_iff.mp (hA4 ▸ Work.Higman.powSub_le_of_dvd hAab hdvd)

/-- **`A` is a maximal `ξ`-invariant abelian normal subgroup in the `C₄` configuration.**

If `A` is abelian, `ξ`-invariant, `[P,P] = A`, `Ω₁(P) ≤ A`, every square of `P` lies in `A`,
`A⁴ = ⊥`, `A² = Ω₁(P)` and `|A| = |Ω₁(P)|²`, then `A` is maximal among the `ξ`-invariant abelian
normal subgroups of `P`.

The proof is the centraliser argument in its simplest form.  Let `B ≥ A` be `ξ`-invariant,
abelian and normal and suppose `B > A`; pick a minimal `ξ`-invariant normal cover `A < F ≤ B`
(`MSA.exists_minimal_covering`).  Then `F` is abelian (it lies in `B`) and `F² ⊆ A`.  By the
dichotomy `F² ∈ {⊥, A², A}`:

* `F² = ⊥`: then `F ≤ Ω₁(P) ≤ A`, contradicting `F > A`;
* `F² = A²`: for `x ∈ F` we have `x² = a²` with `a ∈ A`, and since `F` is abelian
  `(x a⁻¹)² = x² a⁻² = 1`, so `x a⁻¹ ∈ Ω₁(P) ≤ A` and `x ∈ A`: again `F ≤ A`;
* `F² = A`: this is Higman's Lemma 8 abelian case, excluded by `RedAux.abelian_case`. -/
theorem c4sqAMaximal {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {A : Subgroup P}
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hNA : Work.Higman.omega1 P ≤ A)
    (hGs : Bracket.bracket (⊤ : Subgroup P) ⊤ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2) :
    ∀ B : Subgroup P, Work.Higman.IsXiAbelNormal h B → A ≤ B → B = A := by
  classical
  intro B hB hAB
  refine le_antisymm ?_ hAB
  by_contra hnot
  have hBAne : B ≠ A := fun hEq => hnot (le_of_eq hEq)
  obtain ⟨F, -, hFinv, hAF, hFB, hFAne, hcover⟩ :=
    Work.Higman.MSA.exists_minimal_covering h hB.normal hB.map_eq hAB hBAne
  have hFab : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x :=
    fun x hx y hy => hB.abelian x (hFB hx) y (hFB hy)
  have hF2leA : Work.Higman.powSub F 2 ≤ A := by
    rw [Work.Higman.powSub, Subgroup.closure_le]
    rintro y ⟨x, -, rfl⟩
    exact hsq x
  have hF2inv : (Work.Higman.powSub F 2).map (h.xi : MulAut P).toMonoidHom
      = Work.Higman.powSub F 2 :=
    Work.Higman.map_powSub (h.xi : MulAut P) hFinv 2
  -- any subgroup containing `A` is normal, because `P/A` is abelian (`[P,P] = A`)
  have hnorm_of_le : ∀ G : Subgroup P, A ≤ G → G.Normal := by
    intro G hAG
    refine Subgroup.Normal.mk fun n hn g => ?_
    have h1 : ⁅g, n⁆ ∈ A := by
      rw [← hGs]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n)
    rw [show g * n * g⁻¹ = ⁅g, n⁆ * n from by rw [commutatorElement_def]; group]
    exact G.mul_mem (hAG h1) hn
  rcases c4_xi_inv_trichotomy h hAab hAxi htop hA4 hF2leA hF2inv with hb | hm | ht
  · -- `F² = ⊥`: then `F ≤ Ω₁(P) ≤ A`
    refine hFAne (le_antisymm ?_ hAF)
    intro x hx
    refine hNA ?_
    rw [h.mem_omega1]
    have hx2 : x ^ 2 ∈ Work.Higman.powSub F 2 := Work.Higman.pow_mem_powSub hx
    rw [hb] at hx2
    exact Subgroup.mem_bot.mp hx2
  · -- `F² = A²`: the `(x a⁻¹)² = 1` trick
    refine hFAne (le_antisymm ?_ hAF)
    intro x hx
    have hx2 : x ^ 2 ∈ Work.Higman.powSub A 2 := by
      have h' : x ^ 2 ∈ Work.Higman.powSub F 2 := Work.Higman.pow_mem_powSub hx
      rwa [hm] at h'
    obtain ⟨a, ha, haeq⟩ := (Work.Higman.mem_powSub_iff hAab).mp hx2
    have hca : Commute x a := hFab x hx a (hAF ha)
    have hsq1 : (x * a⁻¹) ^ 2 = 1 := by
      rw [hca.inv_right.mul_pow, inv_pow, haeq, mul_inv_cancel]
    have hmem : x * a⁻¹ ∈ A := hNA (h.mem_omega1.mpr hsq1)
    have hxeq : x = (x * a⁻¹) * a := by group
    rw [hxeq]
    exact A.mul_mem hmem ha
  · -- `F² = A`: Higman's Lemma 8, abelian case
    exact Work.Higman.RedAux.abelian_case h hAxi hAab hNA hGs hsq hA4 htop hcard hAF hFAne
      hFinv hFab ht (fun G hAG hGF hGinv => hcover G (hnorm_of_le G hAG) hGinv hAG hGF)

end Work.Higman.NSM
