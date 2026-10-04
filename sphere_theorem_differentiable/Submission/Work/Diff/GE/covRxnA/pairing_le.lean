import Mathlib
import Submission.Work.Diff.GE.covRxn.Defs
import Submission.Work.Diff.L.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The contraction bound for the four-fold pairing (`pairing_le`)

`pairing g x a b c d X = ∑ i j k l, (⟨e i,a⟩⟨e j,b⟩⟨e k,c⟩⟨e l,d⟩) X i j k l` in the orthonormal frame
`e = onFrame g x` is bounded by `‖X‖²` times the product of the `g`-norms of `a b c d`.

The proof is Cauchy–Schwarz for the product weight array `W i j k l = A i * B j * C k * D l`
(`cs4`, pure real analysis), together with Parseval's identity `∑ i, ⟨e i,v⟩² = ⟨v,v⟩` for an
orthonormal frame (`parseval_aux`, which also covers `finrank ℝ E = 0`).
-/

set_option maxHeartbeats 800000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.Diff.GE.covRxnA

open scoped Manifold ContDiff Bundle Topology
open Bundle

/-! ## Helpers -/

/-- Merge two nested sums into a sum over the product index type. -/
private lemma sum_curry {α β γ : Type*} [Fintype α] [Fintype β] [AddCommMonoid γ]
    (f : α → β → γ) : (∑ a, ∑ b, f a b) = ∑ p : α × β, f p.1 p.2 :=
  (Fintype.sum_prod_type (f := fun p : α × β => f p.1 p.2)).symm

/-- The squared product weight array factors over the four one-variable factors. -/
private lemma prod_sq_eq_sum {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (A : α → ℝ) (B : β → ℝ) (C : γ → ℝ) (D : δ → ℝ) :
    (∑ i, A i ^ 2) * (∑ j, B j ^ 2) * (∑ k, C k ^ 2) * (∑ l, D l ^ 2)
      = ∑ r : ((α × β) × γ) × δ,
          (A r.1.1.1 * B r.1.1.2 * C r.1.2 * D r.2) ^ 2 := by
  have h1 : (∑ i : α, A i ^ 2) * (∑ j : β, B j ^ 2)
      = ∑ q : α × β, A q.1 ^ 2 * B q.2 ^ 2 := by
    rw [Fintype.sum_mul_sum]
    exact sum_curry (fun i j => A i ^ 2 * B j ^ 2)
  have h2 : (∑ q : α × β, A q.1 ^ 2 * B q.2 ^ 2) * (∑ k : γ, C k ^ 2)
      = ∑ p : (α × β) × γ, (A p.1.1 ^ 2 * B p.1.2 ^ 2) * C p.2 ^ 2 := by
    rw [Fintype.sum_mul_sum]
    exact sum_curry (fun (q : α × β) (k : γ) => (A q.1 ^ 2 * B q.2 ^ 2) * C k ^ 2)
  have h3 : (∑ p : (α × β) × γ, (A p.1.1 ^ 2 * B p.1.2 ^ 2) * C p.2 ^ 2) * (∑ l : δ, D l ^ 2)
      = ∑ r : ((α × β) × γ) × δ,
          ((A r.1.1.1 ^ 2 * B r.1.1.2 ^ 2) * C r.1.2 ^ 2) * D r.2 ^ 2 := by
    rw [Fintype.sum_mul_sum]
    exact sum_curry (fun (p : (α × β) × γ) (l : δ) =>
      ((A p.1.1 ^ 2 * B p.1.2 ^ 2) * C p.2 ^ 2) * D l ^ 2)
  rw [h1, h2, h3]
  exact Finset.sum_congr rfl (fun r _ => by ring)

/-- A real `√` of a product of three nonnegative factors splits. -/
private lemma sqrt_mul4 {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    Real.sqrt (a * b * c * d) = Real.sqrt a * Real.sqrt b * Real.sqrt c * Real.sqrt d := by
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  have habc : 0 ≤ a * b * c := mul_nonneg hab hc
  rw [Real.sqrt_mul habc, Real.sqrt_mul hab, Real.sqrt_mul ha]

/-- **Four-fold Cauchy–Schwarz** with a rank-one product weight. -/
private lemma cs4 {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (A : α → ℝ) (B : β → ℝ) (C : γ → ℝ) (D : δ → ℝ) (X : α → β → γ → δ → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, (A i * B j * C k * D l) * X i j k l)
      ≤ Real.sqrt (∑ i, ∑ j, ∑ k, ∑ l, X i j k l ^ 2)
        * (Real.sqrt (∑ i, A i ^ 2) * Real.sqrt (∑ j, B j ^ 2)
          * Real.sqrt (∑ k, C k ^ 2) * Real.sqrt (∑ l, D l ^ 2)) := by
  have hCS := Real.sum_mul_le_sqrt_mul_sqrt
      (Finset.univ : Finset (((α × β) × γ) × δ))
      (fun r : ((α × β) × γ) × δ => A r.1.1.1 * B r.1.1.2 * C r.1.2 * D r.2)
      (fun r : ((α × β) × γ) × δ => X r.1.1.1 r.1.1.2 r.1.2 r.2)
  have hL : (∑ i, ∑ j, ∑ k, ∑ l, (A i * B j * C k * D l) * X i j k l)
      = ∑ r : ((α × β) × γ) × δ,
          (A r.1.1.1 * B r.1.1.2 * C r.1.2 * D r.2) * X r.1.1.1 r.1.1.2 r.1.2 r.2 := by
    rw [sum_curry, sum_curry, sum_curry]
  have hR : (∑ i, ∑ j, ∑ k, ∑ l, X i j k l ^ 2)
      = ∑ r : ((α × β) × γ) × δ, X r.1.1.1 r.1.1.2 r.1.2 r.2 ^ 2 := by
    rw [sum_curry, sum_curry, sum_curry]
  rw [hL, hR]
  refine hCS.trans ?_
  rw [← prod_sq_eq_sum A B C D,
    sqrt_mul4 (Finset.sum_nonneg (fun i _ => sq_nonneg (A i)))
      (Finset.sum_nonneg (fun j _ => sq_nonneg (B j)))
      (Finset.sum_nonneg (fun k _ => sq_nonneg (C k)))]
  exact le_of_eq (mul_comm _ _)

/-- **Parseval in a `g`-orthonormal frame.**  `∑ i, (g.inner x (e i) v) ^ 2 = g.inner x v v`.
The case `finrank ℝ E = 0` is trivial. -/
private lemma parseval_aux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    (g : Submission.Diff.SMet I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (he : Submission.Diff.IsONFrame g x e) (v : TangentSpace I x) :
    ∑ i, (g.inner x (e i) v) ^ 2 = g.inner x v v := by
  by_cases hn : 0 < Module.finrank ℝ E
  · letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
    haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
    haveI : Nonempty (Fin (Module.finrank ℝ E)) := Fin.pos_iff_nonempty.mp hn
    classical
    have hon : Orthonormal ℝ e := by
      rw [orthonormal_iff_ite]
      intro i j
      exact he i j
    let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
      basisOfOrthonormalOfCardEqFinrank hon (by rw [Fintype.card_fin]; rfl)
    have hb : (b : Fin (Module.finrank ℝ E) → TangentSpace I x) = e :=
      coe_basisOfOrthonormalOfCardEqFinrank hon _
    have honb : Orthonormal ℝ (b : Fin (Module.finrank ℝ E) → TangentSpace I x) := by
      rw [hb]; exact hon
    have h := (b.toOrthonormalBasis honb).sum_sq_inner_right v
    rw [Module.Basis.coe_toOrthonormalBasis, hb] at h
    rw [show ((g.inner x) v) v = ‖v‖ ^ 2 from real_inner_self_eq_norm_sq v, ← h]
    rfl
  · have h0 : Module.finrank ℝ E = 0 := Nat.eq_zero_of_not_pos hn
    haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
    have hv : v = 0 := finrank_zero_iff_forall_zero.mp h0 v
    rw [hv]
    have hsum : (∑ i : Fin (Module.finrank ℝ E),
        (g.inner x (e i) (0 : TangentSpace I x)) ^ 2) = 0 :=
      Finset.sum_eq_zero (fun i _ => by simp)
    rw [hsum]
    simp

/-! ## The contraction bound -/

/-- **The contraction bound.**  `pairing g x a b c d X = ∑ i j k l, (⟨e i,a⟩⟨e j,b⟩⟨e k,c⟩⟨e l,d⟩) X i j k l`
in the orthonormal frame `e = onFrame g x` is bounded by the `ℓ²` norm of `X` times the product of
the `g`-norms of the four vectors.  Cauchy–Schwarz in the four-tuple, using
`∑ i ⟨e i,u⟩² = ⟨u,u⟩` for an orthonormal frame (that Parseval identity may be stated and proved as
a private helper here; `Work.Diff.GE.sum_inner_smul_eq_self` in `Submission/Work/Diff/GE/curvbasic.lean`
gives `∑ i, ⟨e i,v⟩ • e i = v` under the extra hypothesis `0 < finrank ℝ E`, the case
`finrank = 0` being trivial). -/
theorem pairing_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    (g : Submission.Diff.SMet I M) (x : M)
    (a b c d : TangentSpace I x) (X : Submission.Diff.Alg.Curv4 (Module.finrank ℝ E)) :
    Work.Diff.GE.Rxn.pairing g x a b c d X
      ≤ Real.sqrt (∑ i, ∑ j, ∑ k, ∑ l, (X i j k l) ^ 2)
        * (Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b)
          * Real.sqrt (g.inner x c c) * Real.sqrt (g.inner x d d)) := by
  have he : Submission.Diff.IsONFrame g x (Submission.Diff.onFrame g x) :=
    Work.Diff.L.onFrame_isONFrame g x
  have hA := parseval_aux g x (Submission.Diff.onFrame g x) he a
  have hB := parseval_aux g x (Submission.Diff.onFrame g x) he b
  have hC := parseval_aux g x (Submission.Diff.onFrame g x) he c
  have hD := parseval_aux g x (Submission.Diff.onFrame g x) he d
  have hmain := cs4 (fun i => g.inner x (Submission.Diff.onFrame g x i) a)
    (fun j => g.inner x (Submission.Diff.onFrame g x j) b)
    (fun k => g.inner x (Submission.Diff.onFrame g x k) c)
    (fun l => g.inner x (Submission.Diff.onFrame g x l) d) X
  have hpair : Work.Diff.GE.Rxn.pairing g x a b c d X
      = ∑ i, ∑ j, ∑ k, ∑ l,
          (g.inner x (Submission.Diff.onFrame g x i) a
            * g.inner x (Submission.Diff.onFrame g x j) b
            * g.inner x (Submission.Diff.onFrame g x k) c
            * g.inner x (Submission.Diff.onFrame g x l) d) * X i j k l := rfl
  rw [hpair]
  rw [hA, hB, hC, hD] at hmain
  exact hmain

end Work.Diff.GE.covRxnA
