/-
  WilE7, `Work.WilE7.fiber_card_bound`: the cardinality of a finite fibre of a semi-Pfaffian
  set is polynomial in the degree.

  The argument: specialize the semi-Pfaffian set `X ⊆ ℝ^{p+q}` at the base point `x`; the
  resulting semi-Pfaffian set `speSemiPfAt x X ⊆ ℝ^q` has `set` *equal* to the fibre
  `fiber X.set x` (`Work.WilE7.speAt_set`) and `deg ≤ X.deg` (`speSemiPfAt_deg_le`), and
  `fmt = q + X.r ≤ X.fmt`.  Applying the component bound `hE2` to it gives a finite set `s`
  of `≤ p (deg)` points meeting every connected component of the fibre.  The fibre is finite,
  hence (being a finite subset of `ℝ^q`) totally disconnected: its components are singletons,
  so `s` already contains the whole fibre and `ncard (fiber) ≤ s.card ≤ p (deg) ≤ p (X.deg)`.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.SpeAt
import Submission.Work.WilE7.speAt_set

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-! ## Two elementary tools -/

/-- `Polynomial.eval` is monotone for polynomials over `ℕ`. -/
theorem eval_mono_nat {p : Polynomial ℕ} {a b : ℕ} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.eval_add, Polynomial.eval_add]; exact Nat.add_le_add hp hq
  | monomial n c => rw [Polynomial.eval_monomial, Polynomial.eval_monomial]
                    exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left h n)

/-- A finite set in a T1 space is totally disconnected: its components are singletons. -/
theorem connectedComponentIn_eq_singleton_of_finite {α : Type*} [TopologicalSpace α] [T1Space α]
    {T : Set α} (hT : T.Finite) {y : α} (hy : y ∈ T) :
    connectedComponentIn T y = {y} := by
  rw [connectedComponentIn_eq_image hy]
  haveI : Finite T := hT.to_subtype
  rw [connectedComponent_eq_singleton]
  simp

/-- If every connected component of a finite set `T` is met by a finite set `s`
(represented by a point of `s`), then `T ⊆ s`. -/
theorem subset_finset_of_cover_components {α : Type*} [TopologicalSpace α] [T1Space α]
    {T : Set α} (hT : T.Finite) {s : Finset α}
    (hcov : ∀ x ∈ T, ∃ y ∈ s, connectedComponentIn T x = connectedComponentIn T y) :
    T ⊆ (↑s : Set α) := by
  intro x hx
  obtain ⟨y, hy, heq⟩ := hcov x hx
  have hxmem : x ∈ connectedComponentIn T x := mem_connectedComponentIn hx
  rw [heq] at hxmem
  have hyT : y ∈ T := connectedComponentIn_nonempty_iff.mp ⟨x, hxmem⟩
  have hsing := connectedComponentIn_eq_singleton_of_finite hT hyT
  rw [hsing, Set.mem_singleton_iff] at hxmem
  rw [hxmem]
  simpa using hy

/-! ## The degree of the specialization does not exceed the degree -/

/-- Substitution of variables by polynomials of total degree `≤ 1` does not increase the total
degree. -/
lemma totalDegree_eval₂Hom_le {σ τ : Type*} (φ : σ → MvPolynomial τ ℝ)
    (hφ : ∀ v, (φ v).totalDegree ≤ 1) (P : MvPolynomial σ ℝ) :
    (MvPolynomial.eval₂Hom MvPolynomial.C φ P).totalDegree ≤ P.totalDegree := by
  have hsum : MvPolynomial.eval₂Hom MvPolynomial.C φ P
      = ∑ m ∈ P.support, MvPolynomial.C (P.coeff m) * (m.prod fun i k => φ i ^ k) := by
    conv_lhs => rw [MvPolynomial.as_sum P]
    rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.eval₂Hom_monomial]
  rw [hsum]
  refine MvPolynomial.totalDegree_finsetSum_le fun m hm => ?_
  have hprod : (m.prod fun i k => φ i ^ k).totalDegree
      ≤ ∑ i ∈ m.support, m i * (φ i).totalDegree := by
    rw [Finsupp.prod]
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    exact (MvPolynomial.totalDegree_pow (φ i) (m i)).trans (le_of_eq (by ring))
  calc (MvPolynomial.C (P.coeff m) * (m.prod fun i k => φ i ^ k)).totalDegree
      ≤ (MvPolynomial.C (P.coeff m)).totalDegree + (m.prod fun i k => φ i ^ k).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
    _ ≤ 0 + ∑ i ∈ m.support, m i * (φ i).totalDegree := by
        rw [MvPolynomial.totalDegree_C]; exact add_le_add le_rfl hprod
    _ ≤ ∑ i ∈ m.support, m i := by
        rw [Nat.zero_add]
        exact Finset.sum_le_sum fun i _ => by
          calc m i * (φ i).totalDegree ≤ m i * 1 := Nat.mul_le_mul_left _ (hφ i)
            _ = m i := Nat.mul_one _
    _ ≤ P.totalDegree := MvPolynomial.le_totalDegree hm

/-- The variables of the specialization have total degree `≤ 1`. -/
lemma speVarAt_totalDegree_le {p q r : ℕ} (x : Fin p → ℝ) (v : Fin (p + q) ⊕ Fin r) :
    (speVarAt (q := q) (r := r) x v).totalDegree ≤ 1 := by
  rcases v with i | j
  · refine Fin.addCases
      (motive := fun i => (speVarAt (q := q) (r := r) x (Sum.inl i)).totalDegree ≤ 1)
      (fun i₀ => ?_) (fun l => ?_) i
    · simp only [speVarAt, Sum.elim_inl, Fin.addCases_left, MvPolynomial.totalDegree_C]
      norm_num
    · simp only [speVarAt, Sum.elim_inl, Fin.addCases_right, MvPolynomial.totalDegree_X]
      exact le_rfl
  · simp only [speVarAt, Sum.elim_inr, MvPolynomial.totalDegree_X]
    exact le_rfl

/-- The substitution underlying `speSemiPfAt` does not increase the total degree. -/
lemma spePolyAt_totalDegree_le {p q r : ℕ} (x : Fin p → ℝ) (Q : EAPoly (p + q) r) :
    (spePolyAt (q := q) (r := r) x Q).totalDegree ≤ Q.totalDegree := by
  rw [spePolyAt]
  exact totalDegree_eval₂Hom_le (speVarAt (q := q) (r := r) x) (speVarAt_totalDegree_le x) Q

/-- The atom degree does not increase under the specialization. -/
lemma atomDeg_spePolyAt_le {p q r : ℕ} (x : Fin p → ℝ) (Q : EAPoly (p + q) r) :
    atomDeg (spePolyAt (q := q) (r := r) x Q) ≤ atomDeg Q := by
  unfold atomDeg
  exact Nat.add_le_add_right (spePolyAt_totalDegree_le x Q) 1

/-- Termwise comparison of sums of `ℕ`-valued maps on a list. -/
lemma List.sum_map_le {α : Type*} (l : List α) {f g : α → ℕ} (h : ∀ a ∈ l, f a ≤ g a) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (h a (by simp)) (ih fun b hb => h b (by simp [hb]))

/-- The degree of a specialized basic set does not exceed the original degree. -/
lemma speBasicAt_deg_le {p q r : ℕ} (x : Fin p → ℝ) (B : Basic (p + q) r) :
    (speBasicAt (q := q) x B).deg ≤ B.deg := by
  show ((B.eqs.map (spePolyAt (q := q) x) ++ B.pos.map (spePolyAt (q := q) x)).map atomDeg).sum
      ≤ ((B.eqs ++ B.pos).map atomDeg).sum
  rw [List.map_append, List.sum_append, List.map_append, List.sum_append]
  refine Nat.add_le_add ?_ ?_
  · rw [List.map_map]
    exact List.sum_map_le B.eqs (fun Q _ => atomDeg_spePolyAt_le x Q)
  · rw [List.map_map]
    exact List.sum_map_le B.pos (fun Q _ => atomDeg_spePolyAt_le x Q)

/-- The degree of the specialization does not exceed the degree. -/
theorem speSemiPfAt_deg_le {p q : ℕ} (x : Fin p → ℝ) (X : WilkiesDesign.E.SemiPf (p + q)) :
    (Work.WilE7.speSemiPfAt x X).deg ≤ X.deg := by
  show ((X.basics.map (speBasicAt (q := q) x)).map Basic.deg).sum ≤ (X.basics.map Basic.deg).sum
  rw [List.map_map]
  exact List.sum_map_le X.basics (fun B _ => speBasicAt_deg_le x B)

/-! ## The target -/

theorem fiber_card_bound
    (hE2 : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : WilkiesDesign.E.SemiPf k), X.fmt ≤ F →
      ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ (↑s : Set (Fin k → ℝ)) ⊆ X.set ∧
        ∀ x ∈ X.set, ∃ y ∈ s,
          connectedComponentIn X.set x = connectedComponentIn X.set y)
    (F : ℕ) : ∃ p : Polynomial ℕ, ∀ (p' q : ℕ) (X : WilkiesDesign.E.SemiPf (p' + q))
      (x : Fin p' → ℝ), X.fmt ≤ F → (WilkiesDesign.E.fiber X.set x).Finite →
      (WilkiesDesign.E.fiber X.set x).ncard ≤ p.eval X.deg := by
  obtain ⟨p, hp⟩ := hE2 F
  refine ⟨p, fun p' q X x hFmt hfin => ?_⟩
  by_cases hx : x ∈ cubeC p'
  · -- The fibre is the set of the specialization of `X` at `x`.
    have hset := speAt_set x X hx
    have hfmt : (speSemiPfAt x X).fmt ≤ F := by
      have h := hFmt
      simp only [SemiPf.fmt, speSemiPfAt] at h ⊢
      omega
    obtain ⟨s, hscard, -, hcov⟩ := hp q (speSemiPfAt x X) hfmt
    have hfinT : (speSemiPfAt x X).set.Finite := hset ▸ hfin
    -- A finite discrete set has singleton components, so the covering family contains all of it.
    have hsub : (speSemiPfAt x X).set ⊆ (↑s : Set (Fin q → ℝ)) :=
      subset_finset_of_cover_components hfinT hcov
    have hdeg : (speSemiPfAt x X).deg ≤ X.deg := speSemiPfAt_deg_le x X
    calc (fiber X.set x).ncard = (speSemiPfAt x X).set.ncard := by rw [hset]
      _ ≤ (↑s : Set (Fin q → ℝ)).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet s)
      _ = s.card := Set.ncard_coe_finset s
      _ ≤ p.eval (speSemiPfAt x X).deg := hscard
      _ ≤ p.eval X.deg := eval_mono_nat hdeg
  · -- `x` is outside the cube, so the fibre is empty.
    have hempty : fiber X.set x = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro y hy
      exact hx fun i => by
        have h1 : |Fin.append x y (Fin.castAdd q i)| ≤ 1 := hy.1 (Fin.castAdd q i)
        rwa [Fin.append_left] at h1
    rw [hempty, Set.ncard_empty]
    exact Nat.zero_le _

end Work.WilE7
