/-
  WilE5 — the state invariant at the *initial* states of the recursion, and the vanishing of the
  flatness sources there.

  `initStates X` enumerates the pairs (disjunct `A ∈ X.basics`, face pattern `(Fy, ε)`), and the
  corresponding state is

      initSt X A Fy ε = ⟨Fy.attach.toList.map (fun l ↦ (facePoly l (±1), l)),
                          A.eqs, A.eqs, A.pos ++ {1 - y_l² : l ∉ Fy}⟩

  (see `Sys.lean`).  For such a state:

  * the disjunct bookkeeping holds with `A` itself (`A.eqs ⊆ Ξ = Φ`, `A.pos ⊆ ν`);
  * `Φ = Ξ = A.eqs`, so the two inclusions are trivial;
  * the cube bookkeeping: for `l ∈ Fy` the face equation `y_l - c_l` is in `B` (with the sign
    pattern `c_l = if ε l then 1 else -1`), and for `l ∉ Fy` the interior inequality `1 - y_l²`
    is in `ν`;
  * the pivot minor is nonzero: the pivots are the distinct directions `l ∈ Fy` and the equations
    are `y_l - c_l`, so `∂_{y_{l'}} (y_l - c_l) = δ_{l l'}` and the minor is the identity matrix
    (`initSt_pivotDet`);
  * the flatness sources (`A.eqs`) are among the state's equations, so they vanish on the state's
    set (`Strat.PhiInXi_holds`).
-/
import Mathlib
import Submission.Work.WilE5.Sys
import Submission.Work.WilE5.Strat.InvariantDef
import Submission.Work.WilE5.Strat.InitCover
import Submission.Work.WilE5.Strat.cover
import Submission.Work.WilE5.Basic

set_option autoImplicit false
noncomputable section
open Classical Filter
open scoped Topology

namespace Work.WilE5

open WilkiesDesign WilkiesDesign.E

/-- The `i`-th entry of a mapped list, in terms of the original list. -/
theorem get_map_get {α β : Type*} (f : α → β) (l : List α) (hlen : (l.map f).length = l.length)
    (a : Fin (l.map f).length) : (l.map f).get a = f (l.get (Fin.cast hlen a)) := by
  simp only [List.get_eq_getElem, List.getElem_map, Fin.val_cast]

variable {p q : ℕ}

/-- `eaD` is additive. -/
theorem eaD_sub (X : SemiPf (p + q)) (i : Fin (p + q)) (A B : EAPoly (p + q) X.r) :
    eaD X.c i (A - B) = eaD X.c i A - eaD X.c i B := by
  simp only [eaD, map_sub, mul_sub]
  rw [Finset.sum_sub_distrib]
  ring

/-- The derivative of a face equation `y_l - c`: `∂_i (y_l - c) = δ_{i, y_l}`. -/
theorem eaD_facePoly (X : SemiPf (p + q)) (i : Fin (p + q)) (l : Fin q) (cc : ℝ) :
    eaD X.c i (facePoly (p := p) (r := X.r) l cc) =
      (if i = yDir p l then 1 else 0 : EAPoly (p + q) X.r) := by
  have hface : (facePoly (p := p) (r := X.r) l cc : EAPoly (p + q) X.r)
      = MvPolynomial.X (Sum.inl (yDir p l)) - MvPolynomial.C cc := rfl
  rw [hface, eaD_sub]
  have hz : (eaD X.c i (MvPolynomial.C cc : EAPoly (p + q) X.r)) = 0 := by
    rw [eaD]
    have hC : ∀ k : Fin X.r,
        MvPolynomial.C (X.c.a k i) * MvPolynomial.X (Sum.inr k)
          * MvPolynomial.pderiv (Sum.inr k) (MvPolynomial.C cc : EAPoly (p + q) X.r) = 0 := by
      intro k; rw [MvPolynomial.pderiv_C, mul_zero]
    rw [MvPolynomial.pderiv_C, Finset.sum_eq_zero (fun k _ => hC k), add_zero]
  rw [hz, sub_zero]
  have h2 : ∀ k : Fin X.r,
      MvPolynomial.pderiv (Sum.inr k)
        (MvPolynomial.X (Sum.inl (yDir p l)) : EAPoly (p + q) X.r) = 0 :=
    fun k => MvPolynomial.pderiv_X_of_ne (by simp)
  rw [eaD, Finset.sum_eq_zero (fun k _ => by rw [h2 k, mul_zero]), add_zero,
    MvPolynomial.pderiv_X]
  by_cases h : i = yDir p l
  · subst h; simp
  · rw [Pi.single_apply, if_neg (fun hh => h (Sum.inl_injective hh).symm), if_neg h]

/-- The pivot minor of an initial state is the identity matrix (in particular nonzero): the
equations of `initSt X A Fy ε` are the face equations `y_l ∓ 1` for `l ∈ Fy`, one for each
(distinct) pivot direction, and `∂_{y_{l'}} (y_l - c) = δ_{l l'}`. -/
theorem initSt_pivotDet (X : SemiPf (p + q)) (A : Basic (p + q) X.r) (Fy : Finset (Fin q))
    (ε : {l // l ∈ Fy} → Bool) (z : Fin (p + q) → ℝ) :
    (Matrix.of fun (a b : Fin (initSt X A Fy ε).B.length) =>
      eaEval X.c (eaD X.c (pivFun (initSt X A Fy ε).B b)
        (hFun (initSt X A Fy ε).B a)) z).det ≠ 0 := by
  have hlen : ((Fy.attach.toList).map (fun l : {x // x ∈ Fy} =>
      (facePoly (p := p) (r := X.r) l.1 (if ε l then (1 : ℝ) else -1), l.1))).length
      = (Fy.attach.toList).length := List.length_map _
  have hH : ∀ a : Fin (initSt X A Fy ε).B.length,
      hFun (initSt X A Fy ε).B a =
        facePoly (p := p) (r := X.r) (Fy.attach.toList.get (Fin.cast hlen a)).1
          (if ε (Fy.attach.toList.get (Fin.cast hlen a)) then (1 : ℝ) else -1) := by
    intro a
    show (((Fy.attach.toList).map (fun l : {x // x ∈ Fy} =>
      (facePoly (p := p) (r := X.r) l.1 (if ε l then (1 : ℝ) else -1), l.1))).get a).1 =
      facePoly (p := p) (r := X.r) (Fy.attach.toList.get (Fin.cast hlen a)).1
        (if ε (Fy.attach.toList.get (Fin.cast hlen a)) then (1 : ℝ) else -1)
    rw [get_map_get (fun l : {x // x ∈ Fy} =>
      (facePoly (p := p) (r := X.r) l.1 (if ε l then (1 : ℝ) else -1), l.1))
      (Fy.attach.toList) hlen a]
  have hP : ∀ b : Fin (initSt X A Fy ε).B.length,
      pivFun (initSt X A Fy ε).B b = yDir p (Fy.attach.toList.get (Fin.cast hlen b)).1 := by
    intro b
    show yDir p (((Fy.attach.toList).map (fun l : {x // x ∈ Fy} =>
      (facePoly (p := p) (r := X.r) l.1 (if ε l then (1 : ℝ) else -1), l.1))).get b).2 =
      yDir p (Fy.attach.toList.get (Fin.cast hlen b)).1
    rw [get_map_get (fun l : {x // x ∈ Fy} =>
      (facePoly (p := p) (r := X.r) l.1 (if ε l then (1 : ℝ) else -1), l.1))
      (Fy.attach.toList) hlen b]
  have key : ∀ a b : Fin (initSt X A Fy ε).B.length,
      (a = b) ↔ yDir p (Fy.attach.toList.get (Fin.cast hlen b)).1
        = yDir p (Fy.attach.toList.get (Fin.cast hlen a)).1 := by
    intro a b
    constructor
    · intro hab; rw [hab]
    · intro hy
      have h1 : Fy.attach.toList.get (Fin.cast hlen b)
          = Fy.attach.toList.get (Fin.cast hlen a) := Subtype.ext (yDir_injective p hy)
      have h2 : (Fin.cast hlen b : Fin (Fy.attach.toList).length) = Fin.cast hlen a :=
        (List.Nodup.get_inj_iff (Finset.nodup_toList _)).mp h1
      exact (Fin.cast_injective hlen h2).symm
  have hentry : ∀ a b : Fin (initSt X A Fy ε).B.length,
      eaEval X.c (eaD X.c (pivFun (initSt X A Fy ε).B b)
        (hFun (initSt X A Fy ε).B a)) z = (if a = b then 1 else 0 : ℝ) := by
    intro a b
    rw [hH a, hP b, eaD_facePoly]
    by_cases h : yDir p (Fy.attach.toList.get (Fin.cast hlen b)).1
        = yDir p (Fy.attach.toList.get (Fin.cast hlen a)).1
    · rw [if_pos h, eaEval_one, if_pos ((key a b).mpr h)]
    · rw [if_neg h, if_neg (fun hab => h ((key a b).mp hab))]
      simp only [eaEval_eq_hom, map_zero]
  have hone : (Matrix.of fun (a b : Fin (initSt X A Fy ε).B.length) =>
      eaEval X.c (eaD X.c (pivFun (initSt X A Fy ε).B b)
        (hFun (initSt X A Fy ε).B a)) z) = 1 := by
    ext a b
    rw [Matrix.of_apply, hentry a b, Matrix.one_apply]
  rw [hone, Matrix.det_one]
  exact one_ne_zero

/-- The initial states satisfy the state invariant, and the flatness sources of an initial state
vanish on its set. -/
theorem initSt_inv {p q : ℕ} (X : WilkiesDesign.E.SemiPf (p + q)) (σ : Work.WilE5.St p q X.r)
    (hσ : σ ∈ Work.WilE5.initStates X) :
    Work.WilE5.Strat.Inv X σ ∧
      (∀ ψ ∈ σ.Φ, ∀ w ∈ (Work.WilE5.stSemiPf X σ).set,
        WilkiesDesign.E.eaEval X.c ψ w = 0) := by
  obtain ⟨A, hA, Fy, ε, rfl⟩ := exists_of_mem_initStates X hσ
  refine ⟨⟨⟨A, hA, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩,
    Strat.PhiInXi_holds X (Strat.PhiInXi_initSt X A Fy ε)⟩
  · intro f hf
    show f ∈ (stCond (initSt X A Fy ε)).eqs
    simp only [stCond, initSt, List.mem_append]
    exact Or.inr hf
  · intro g hg
    show g ∈ (stCond (initSt X A Fy ε)).pos
    simp only [stCond, initSt, List.mem_append]
    exact Or.inl hg
  · intro f hf
    exact hf
  · intro ψ hψ
    exact hψ
  · intro ψ hψ
    exact hψ
  · intro l
    by_cases hl : l ∈ Fy
    · refine Or.inr ⟨(if ε ⟨l, hl⟩ then (1 : ℝ) else -1), ?_, ?_⟩
      · cases hb : ε ⟨l, hl⟩ <;> simp
      · exact List.mem_map.mpr ⟨(facePoly (p := p) (r := X.r) l
            (if ε ⟨l, hl⟩ then (1 : ℝ) else -1), l),
          List.mem_map.mpr ⟨⟨l, hl⟩,
            Finset.mem_toList.mpr (Finset.mem_attach Fy ⟨l, hl⟩), rfl⟩, rfl⟩
    · refine Or.inl ?_
      exact List.mem_append_right _ (List.mem_map.mpr
        ⟨⟨l, Finset.mem_compl.mpr hl⟩, Finset.mem_toList.mpr (Finset.mem_attach _ _), rfl⟩)
  · exact fun z _ => initSt_pivotDet X A Fy ε z

end Work.WilE5
