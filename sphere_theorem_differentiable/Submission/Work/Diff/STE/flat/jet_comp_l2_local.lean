import Mathlib
import Submission.Work.Diff.STE.flat.jet_comp_l2_unif

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `jet_comp_l2_local`: the local form of the flat composition `L²` estimate

`Work.Diff.STE.flat.jet_comp_l2_unif` bounds the `L²` norm of the `(s+1)`-st spatial jet of
`x ↦ Ψ (x, P x)` under the assumption that `Ψ` is **globally** `C^∞`.  In the applications the
nonlinearity `Ψ` is only known to be smooth at the points `(x, P x)` of the graph of `P` (these
are exactly the points at which the jet of `Ψ` is evaluated and bounded).

This file proves the same estimate under the weaker hypothesis
`hΨsm : ∀ x, ContDiffAt ℝ ⊤ Ψ (x, P x)`.  The only two places in the proof of the uniform version
where smoothness of `Ψ` enters are

* the construction of the composite `x ↦ Ψ (x, P x)` as a globally `C^∞` function (used for
  continuity/integrability and for `pdVec = iteratedFDeriv`) — here `ContDiffAt` at *every* point
  suffices, since `ContDiff 𝕜 n f = ContDiffOn 𝕜 n f univ = ∀ x, ContDiffAt 𝕜 n f x` unfolds
  definitionally;
* the *pointwise* Faà di Bruno expansion, which only ever needs `ContDiffAt ℝ ⊤ Ψ (x, P x)`
  (`iteratedFDeriv_comp` is a `ContDiffAt` statement) — this is
  `iteratedFDeriv_comp_sum_gen_local` below.

Everything else is verbatim the proof of `jet_comp_l2_unif`.
-/

noncomputable section

namespace Work.Diff.STE.flat

open MeasureTheory BigOperators

/-! ## The local Faà di Bruno expansion -/

/-- **Faà di Bruno formula**, local (i.e. `ContDiffAt`) form: the iterated Fréchet derivative of a
composition `Φ ∘ V` evaluated at an `s`-tuple of vectors is the sum over the ordered set
partitions of `Fin s` (this is `iteratedFDeriv_comp_sum_gen` with the two global smoothness
hypotheses replaced by the pointwise ones actually consumed by `iteratedFDeriv_comp`). -/
theorem iteratedFDeriv_comp_sum_gen_local {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (s : ℕ) (Φ : G → H) (V : E → G) (x : E)
    (hΦ : ContDiffAt ℝ (⊤ : ℕ∞) Φ (V x)) (hV : ContDiffAt ℝ (⊤ : ℕ∞) V x) (v : Fin s → E) :
    iteratedFDeriv ℝ s (fun y => Φ (V y)) x v
      = ∑ c : OrderedFinpartition s,
          (iteratedFDeriv ℝ c.length Φ (V x))
            (fun i => iteratedFDeriv ℝ (c.partSize i) V x (v ∘ c.emb i)) := by
  have h1 : iteratedFDeriv ℝ s (fun y => Φ (V y)) x
      = (ftaylorSeries ℝ Φ (V x)).taylorComp (ftaylorSeries ℝ V x) s :=
    iteratedFDeriv_comp (g := Φ) (f := V) hΦ hV
      (WithTop.coe_le_coe.mpr le_top : ((s : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))
  rw [h1]
  simp only [FormalMultilinearSeries.taylorComp, ftaylorSeries, sum_apply,
    FormalMultilinearSeries.compAlongOrderedFinpartition_apply,
    OrderedFinpartition.applyOrderedFinpartition_apply]

/-- Smoothness of the composite `x ↦ Ψ (x, P x)`: pointwise smoothness of `Ψ` along the graph of
`P`, together with global smoothness of `P`, gives global smoothness of the composite, because
`ContDiff 𝕜 n f = ContDiffOn 𝕜 n f univ = ∀ x, ContDiffAt 𝕜 n f x` unfolds definitionally. -/
lemma contDiff_comp_pair_of_contDiffAt {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (Ψ : (Fin n → ℝ) × F → ℂ) (P : (Fin n → ℝ) → F)
    (hΨsm : ∀ x : Fin n → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) Ψ (x, P x))
    (hPsm : ContDiff ℝ (⊤ : ℕ∞) P) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => Ψ (x, P x)) :=
  contDiffOn_univ.mp fun x _ => (contDiffWithinAt_univ).mpr
    ((hΨsm x).comp x ((contDiff_id.prodMk hPsm).contDiffAt (x := x)))

theorem jet_comp_l2_local {n s M : ℕ} (hM : (s + 1) / 2 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
      (Ψ : (Fin n → ℝ) × F → ℂ) (P : (Fin n → ℝ) → F) (K A Etop : ℝ)
      (hA : 0 ≤ A) (hK : 0 ≤ K)
      (hΨsm : ∀ x : Fin n → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) Ψ (x, P x))
      (hPsm : ContDiff ℝ (⊤ : ℕ∞) P)
      (hΨ : ∀ j ≤ s + 1, ∀ x : Fin n → ℝ, ‖iteratedFDeriv ℝ j Ψ (x, P x)‖ ≤ K)
      (hPsup : ∀ m ≤ M, ∀ x : Fin n → ℝ, ‖iteratedFDeriv ℝ m P x‖ ≤ A)
      (hPl2 : ∀ m ≤ s + 1,
        ∫ x in Work.Diff.STE.unitCube (ι := Fin n), ‖iteratedFDeriv ℝ m P x‖ ^ 2 ≤ Etop)
      (l : Fin (s + 1) → Fin n),
      ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
        ‖Work.Diff.STE.pdVec (s + 1) l (fun x => Ψ (x, P x)) x‖ ^ 2
        ≤ C * K ^ 2 * (1 + A) ^ (2 * (s + 2)) * (1 + Etop) := by
  classical
  refine ⟨(Fintype.card (OrderedFinpartition (s + 1)) : ℝ) ^ 2, by positivity, ?_⟩
  intro F _ _ Ψ P K A Etop hA hK hΨsm hPsm hΨ hPsup hPl2 l
  set N : ℝ := (Fintype.card (OrderedFinpartition (s + 1)) : ℝ) with hNdef
  have hN0 : 0 ≤ N := by rw [hNdef]; positivity
  -- `Etop ≥ 0`
  have hEtop : 0 ≤ Etop := by
    have h := integral_nonneg
      (μ := volume.restrict (unitCube (ι := Fin n)))
      (f := fun x : Fin n → ℝ => ‖iteratedFDeriv ℝ 0 P x‖ ^ 2) (fun x => by positivity)
    exact h.trans (hPl2 0 (Nat.zero_le _))
  -- smoothness of the composite: this is the only place where smoothness of `Ψ` is used, and
  -- pointwise smoothness along the graph of `P` is enough
  have hcomp_sm : ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => Ψ (x, P x)) :=
    contDiff_comp_pair_of_contDiffAt Ψ P hΨsm hPsm
  -- `pdVec` versus `iteratedFDeriv`
  have hpd : ∀ x : Fin n → ℝ,
      pdVec (s + 1) l (fun x => Ψ (x, P x)) x
        = iteratedFDeriv ℝ (s + 1) (fun x : Fin n → ℝ => Ψ (x, P x)) x
            (fun j => Pi.single (l j) (1 : ℝ)) :=
    fun x => Comp.pdVec_eq_iteratedFDeriv (s + 1) _ hcomp_sm x l
  -- Faà di Bruno
  have hfab : ∀ x : Fin n → ℝ,
      iteratedFDeriv ℝ (s + 1) (fun x : Fin n → ℝ => Ψ (x, P x)) x
          (fun j => Pi.single (l j) (1 : ℝ))
        = ∑ c : OrderedFinpartition (s + 1),
            (iteratedFDeriv ℝ c.length Ψ (x, P x))
              (fun i => iteratedFDeriv ℝ (c.partSize i) (fun y : Fin n → ℝ => (y, P y)) x
                ((fun j => Pi.single (l j) (1 : ℝ)) ∘ c.emb i)) := by
    intro x
    have h := iteratedFDeriv_comp_sum_gen_local (s + 1) Ψ (fun y : Fin n → ℝ => (y, P y)) x
      (hΨsm x) ((contDiff_id.prodMk hPsm).contDiffAt (x := x))
      (fun j => Pi.single (l j) (1 : ℝ))
    simpa using h
  -- the pointwise Cauchy–Schwarz + term bound
  have hpt : ∀ x : Fin n → ℝ,
      ‖iteratedFDeriv ℝ (s + 1) (fun x : Fin n → ℝ => Ψ (x, P x)) x
          (fun j => Pi.single (l j) (1 : ℝ))‖ ^ 2
        ≤ N * ∑ c : OrderedFinpartition (s + 1),
            K ^ 2 * (∏ i : Fin c.length,
              (if c.partSize i ≤ M then max 1 A
               else max 1 ‖iteratedFDeriv ℝ (c.partSize i) P x‖)) ^ 2 := by
    intro x
    rw [hfab x]
    have h1 : ‖∑ c : OrderedFinpartition (s + 1),
          (iteratedFDeriv ℝ c.length Ψ (x, P x))
            (fun i => iteratedFDeriv ℝ (c.partSize i) (fun y : Fin n → ℝ => (y, P y)) x
              ((fun j => Pi.single (l j) (1 : ℝ)) ∘ c.emb i))‖ ^ 2
        ≤ N * ∑ c : OrderedFinpartition (s + 1),
            ‖(iteratedFDeriv ℝ c.length Ψ (x, P x))
              (fun i => iteratedFDeriv ℝ (c.partSize i) (fun y : Fin n → ℝ => (y, P y)) x
                ((fun j => Pi.single (l j) (1 : ℝ)) ∘ c.emb i))‖ ^ 2 := by
      have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
        (f := fun c : OrderedFinpartition (s + 1) =>
          ‖(iteratedFDeriv ℝ c.length Ψ (x, P x))
            (fun i => iteratedFDeriv ℝ (c.partSize i) (fun y : Fin n → ℝ => (y, P y)) x
              ((fun j => Pi.single (l j) (1 : ℝ)) ∘ c.emb i))‖)
      refine (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans ?_
      simpa [hNdef, Finset.card_univ] using h
    refine h1.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ => ?_) hN0)
    calc ‖(iteratedFDeriv ℝ c.length Ψ (x, P x))
            (fun i => iteratedFDeriv ℝ (c.partSize i) (fun y : Fin n → ℝ => (y, P y)) x
              ((fun j => Pi.single (l j) (1 : ℝ)) ∘ c.emb i))‖ ^ 2
        ≤ (K * ∏ i : Fin c.length,
              (if c.partSize i ≤ M then max 1 A
               else max 1 ‖iteratedFDeriv ℝ (c.partSize i) P x‖)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _)
            (norm_chainTerm_le Ψ P K A hPsm hΨ hPsup l c x) 2
      _ = K ^ 2 * (∏ i : Fin c.length,
              (if c.partSize i ≤ M then max 1 A
               else max 1 ‖iteratedFDeriv ℝ (c.partSize i) P x‖)) ^ 2 := by ring
  -- continuity / integrability
  have hcontL : Continuous fun x : Fin n → ℝ =>
      ‖iteratedFDeriv ℝ (s + 1) (fun x : Fin n → ℝ => Ψ (x, P x)) x
        (fun j => Pi.single (l j) (1 : ℝ))‖ ^ 2 := by
    have h1 : Continuous (iteratedFDeriv ℝ (s + 1) (fun x : Fin n → ℝ => Ψ (x, P x))) :=
      hcomp_sm.continuous_iteratedFDeriv (m := s + 1) (by simp)
    fun_prop
  have hfacs : ∀ c : OrderedFinpartition (s + 1), Continuous fun x : Fin n → ℝ =>
      K ^ 2 * (∏ i : Fin c.length,
        (if c.partSize i ≤ M then max 1 A
         else max 1 ‖iteratedFDeriv ℝ (c.partSize i) P x‖)) ^ 2 := by
    intro c
    have hf : ∀ i : Fin c.length, Continuous fun x : Fin n → ℝ =>
        (if c.partSize i ≤ M then max 1 A
         else max 1 ‖iteratedFDeriv ℝ (c.partSize i) P x‖) := by
      intro i
      by_cases h : c.partSize i ≤ M
      · exact (continuous_const : Continuous fun _ : Fin n → ℝ => max 1 A).congr
          (fun x => by rw [if_pos h])
      · exact (continuous_max_one_norm_iteratedFDeriv P hPsm (c.partSize i)).congr
          (fun x => by rw [if_neg h])
    exact continuous_const.mul ((continuous_finsetProd Finset.univ fun i _ => hf i).pow 2)
  have hcontR : Continuous fun x : Fin n → ℝ =>
      N * ∑ c : OrderedFinpartition (s + 1),
        K ^ 2 * (∏ i : Fin c.length,
          (if c.partSize i ≤ M then max 1 A
           else max 1 ‖iteratedFDeriv ℝ (c.partSize i) P x‖)) ^ 2 :=
    continuous_const.mul (continuous_finsetSum _ fun c _ => hfacs c)
  -- the final estimate
  have hper : ∀ c : OrderedFinpartition (s + 1),
      ∫ x in unitCube (ι := Fin n), K ^ 2 * (∏ i : Fin c.length,
          (if c.partSize i ≤ M then max 1 A
           else max 1 ‖iteratedFDeriv ℝ (c.partSize i) P x‖)) ^ 2
        ≤ K ^ 2 * ((max 1 A) ^ (2 * (s + 1)) * (1 + Etop)) := by
    intro c
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left
      (integral_prod_block_bound hM P hPsm A Etop hEtop hPl2 c) (by positivity)
  calc ∫ x in unitCube (ι := Fin n),
        ‖pdVec (s + 1) l (fun x => Ψ (x, P x)) x‖ ^ 2
      = ∫ x in unitCube (ι := Fin n),
          ‖iteratedFDeriv ℝ (s + 1) (fun x : Fin n → ℝ => Ψ (x, P x)) x
            (fun j => Pi.single (l j) (1 : ℝ))‖ ^ 2 :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => congrArg (fun z => ‖z‖ ^ 2) (hpd x))
    _ ≤ ∫ x in unitCube (ι := Fin n),
          N * ∑ c : OrderedFinpartition (s + 1),
            K ^ 2 * (∏ i : Fin c.length,
              (if c.partSize i ≤ M then max 1 A
               else max 1 ‖iteratedFDeriv ℝ (c.partSize i) P x‖)) ^ 2 :=
        integral_mono_ae (el_integrableOn_unitCube_of_continuous_real hcontL)
          (el_integrableOn_unitCube_of_continuous_real hcontR)
          (Filter.Eventually.of_forall hpt)
    _ = N * ∫ x in unitCube (ι := Fin n),
          ∑ c : OrderedFinpartition (s + 1),
            K ^ 2 * (∏ i : Fin c.length,
              (if c.partSize i ≤ M then max 1 A
               else max 1 ‖iteratedFDeriv ℝ (c.partSize i) P x‖)) ^ 2 :=
        integral_const_mul _ _
    _ = N * ∑ c : OrderedFinpartition (s + 1),
          ∫ x in unitCube (ι := Fin n), K ^ 2 * (∏ i : Fin c.length,
            (if c.partSize i ≤ M then max 1 A
             else max 1 ‖iteratedFDeriv ℝ (c.partSize i) P x‖)) ^ 2 := by
        rw [integral_finsetSum _ fun c _ =>
          el_integrableOn_unitCube_of_continuous_real (hfacs c)]
    _ ≤ N * ∑ _c : OrderedFinpartition (s + 1),
          K ^ 2 * ((max 1 A) ^ (2 * (s + 1)) * (1 + Etop)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ => hper c) hN0
    _ = N * ((Fintype.card (OrderedFinpartition (s + 1)) : ℝ)
          * (K ^ 2 * ((max 1 A) ^ (2 * (s + 1)) * (1 + Etop)))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ (Fintype.card (OrderedFinpartition (s + 1)) : ℝ) ^ 2 * K ^ 2
          * (1 + A) ^ (2 * (s + 2)) * (1 + Etop) := by
        rw [hNdef] at *
        have hmax : max 1 A ≤ 1 + A := by
          rcases le_total 1 A with h | h
          · rw [max_eq_right h]; linarith
          · rw [max_eq_left h]; linarith
        have hmax0 : 0 ≤ max 1 A := by positivity
        have h1A : 1 ≤ 1 + A := by linarith
        have hpow : (max 1 A) ^ (2 * (s + 1)) ≤ (1 + A) ^ (2 * (s + 2)) := by
          calc (max 1 A) ^ (2 * (s + 1)) ≤ (1 + A) ^ (2 * (s + 1)) :=
                pow_le_pow_left₀ hmax0 hmax _
            _ ≤ (1 + A) ^ (2 * (s + 2)) :=
                pow_le_pow_right₀ h1A (by omega)
        have hK2 : 0 ≤ K ^ 2 := sq_nonneg K
        have hEt : 0 ≤ 1 + Etop := by linarith
        have hNc : 0 ≤ (Fintype.card (OrderedFinpartition (s + 1)) : ℝ) := Nat.cast_nonneg _
        have hmain : (Fintype.card (OrderedFinpartition (s + 1)) : ℝ) ^ 2 * K ^ 2
              * ((max 1 A) ^ (2 * (s + 1)) * (1 + Etop))
            ≤ (Fintype.card (OrderedFinpartition (s + 1)) : ℝ) ^ 2 * K ^ 2
              * ((1 + A) ^ (2 * (s + 2)) * (1 + Etop)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hEt) (by positivity)
        calc (Fintype.card (OrderedFinpartition (s + 1)) : ℝ)
              * ((Fintype.card (OrderedFinpartition (s + 1)) : ℝ)
                * (K ^ 2 * ((max 1 A) ^ (2 * (s + 1)) * (1 + Etop))))
            = (Fintype.card (OrderedFinpartition (s + 1)) : ℝ) ^ 2 * K ^ 2
              * ((max 1 A) ^ (2 * (s + 1)) * (1 + Etop)) := by ring
          _ ≤ (Fintype.card (OrderedFinpartition (s + 1)) : ℝ) ^ 2 * K ^ 2
              * ((1 + A) ^ (2 * (s + 2)) * (1 + Etop)) := hmain
          _ = (Fintype.card (OrderedFinpartition (s + 1)) : ℝ) ^ 2 * K ^ 2
              * (1 + A) ^ (2 * (s + 2)) * (1 + Etop) := by ring


end Work.Diff.STE.flat
