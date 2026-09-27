import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Basic
import Submission.Work.KT.cls_eq_stable_mvN
import Submission.Work.KT.k0_rep
import Submission.Work.KT.Bott.GlueAux
import Submission.Work.KT.Bott.mvN_glue

/-!
# Injectivity of `K₀ P → K₀ P₁ ⊕ K₀ P₂` for a cartesian square with stable lifting

The main theorem is `Work.KT.Bott.k0_mv_inj`.  The proof is Milnor's argument: a kernel element
`w = [e] - [1]` has `[e ⊗ Pᵢ] = [1]` over both `Pᵢ`; by `cls_eq_stable_mvN` the images of `e`
are stably isomorphic to free modules, and the gluing data (rectangular matrices `Aᵢ`, `Bᵢ` with
`Bᵢ Aᵢ = eᵢ`, `Aᵢ Bᵢ = 1`) can be glued over `P` after using the stable lifting hypothesis to
make the two trivializations agree over `Q` (`Work.KT.Bott.mvN_glue`, in the module
`Submission.Work.KT.Bott.mvN_glue`).
-/

namespace Work.KT.Bott

open Matrix

noncomputable section

/-! ## Stable freeness -/

/-- If an idempotent `E` over `P` becomes stably free over both `P₁` and `P₂`, then it is stably
free over `P` — the injectivity of `K₀` on idempotents, given the stable unit lifting hypothesis
over `P₂`. -/
theorem stable_free {P P₁ P₂ Q : Type} [Ring P] [Ring P₁] [Ring P₂] [Ring Q]
    (ρ₁ : P →+* P₁) (ρ₂ : P →+* P₂) (σ₁ : P₁ →+* Q) (σ₂ : P₂ →+* Q)
    (hcomm : σ₁.comp ρ₁ = σ₂.comp ρ₂)
    (hpb : ∀ x₁ x₂, σ₁ x₁ = σ₂ x₂ → ∃! x, ρ₁ x = x₁ ∧ ρ₂ x = x₂)
    (hlift : ∀ (n : ℕ) (u : Matrix (Fin n) (Fin n) Q), IsUnit u →
        ∃ (k : ℕ) (v : Matrix (Fin (n + k)) (Fin (n + k)) P₂), IsUnit v ∧
          v.map σ₂ = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks u 0 0 1))
    {E : Mat P} (hE : E.IsIdem) (N : ℕ)
    (h₁ : cls (E.map ρ₁) = cls (Mat.one P₁ N)) (h₂ : cls (E.map ρ₂) = cls (Mat.one P₂ N)) :
    cls E = cls (Mat.one P N) := by
  obtain ⟨a₁, ha₁⟩ :=
    (cls_eq_stable_mvN (E.map ρ₁) (Mat.one P₁ N) (Mat.map_idem ρ₁ hE)
      (Mat.one_isIdem P₁ N)).mp h₁
  obtain ⟨a₂, ha₂⟩ :=
    (cls_eq_stable_mvN (E.map ρ₂) (Mat.one P₂ N) (Mat.map_idem ρ₂ hE)
      (Mat.one_isIdem P₂ N)).mp h₂
  -- enlarge the two stabilising free blocks to a common one
  have hF₁ : Mat.MvN ⟨E.1 + max a₁ a₂, blk (max a₁ a₂) (E.2.map ρ₁)⟩
      (Mat.one P₁ (N + max a₁ a₂)) := by
    have h := k2_mvN_add_one_right (p := E.map ρ₁) (q := Mat.one P₁ N) (Mat.map_idem ρ₁ hE)
      (Mat.one_isIdem P₁ N) ha₁ (max a₁ a₂ - a₁)
    rw [Nat.add_sub_of_le (le_max_left a₁ a₂), k2_one_sum_one P₁ N (max a₁ a₂)] at h
    exact h
  have hF₂ : Mat.MvN ⟨E.1 + max a₁ a₂, blk (max a₁ a₂) (E.2.map ρ₂)⟩
      (Mat.one P₂ (N + max a₁ a₂)) := by
    have h := k2_mvN_add_one_right (p := E.map ρ₂) (q := Mat.one P₂ N) (Mat.map_idem ρ₂ hE)
      (Mat.one_isIdem P₂ N) ha₂ (max a₁ a₂ - a₂)
    rw [Nat.add_sub_of_le (le_max_right a₁ a₂), k2_one_sum_one P₂ N (max a₁ a₂)] at h
    exact h
  obtain ⟨A₁, B₁, hB₁A₁, hA₁B₁⟩ := exists_factor_of_mvN (E.2.map ρ₁) N (max a₁ a₂) hF₁
  obtain ⟨A₂, B₂, hB₂A₂, hA₂B₂⟩ := exists_factor_of_mvN (E.2.map ρ₂) N (max a₁ a₂) hF₂
  -- the two factorisations of `e = (E ⊕ 1_a)`
  have key₁ : ((E.sum (Mat.one P (max a₁ a₂))).2).map ρ₁ = blk (max a₁ a₂) (E.2.map ρ₁) := by
    rw [← blk_mat_sum E (max a₁ a₂)]
    exact blk_map ρ₁ (max a₁ a₂) E.2
  have key₂ : ((E.sum (Mat.one P (max a₁ a₂))).2).map ρ₂ = blk (max a₁ a₂) (E.2.map ρ₂) := by
    rw [← blk_mat_sum E (max a₁ a₂)]
    exact blk_map ρ₂ (max a₁ a₂) E.2
  have heρ₁ : B₁ * A₁ = ((E.sum (Mat.one P (max a₁ a₂))).2).map ρ₁ := hB₁A₁.trans key₁.symm
  have heρ₂ : B₂ * A₂ = ((E.sum (Mat.one P (max a₁ a₂))).2).map ρ₂ := hB₂A₂.trans key₂.symm
  -- the two images of `e` in `Q` agree
  have hEσ : (((E.sum (Mat.one P (max a₁ a₂))).2).map ρ₁).map σ₁ =
      (((E.sum (Mat.one P (max a₁ a₂))).2).map ρ₂).map σ₂ := by
    rw [matrix_map_map, matrix_map_map, hcomm]
  -- glue the two factorisations (using the stable lifting hypothesis)
  obtain ⟨t, X, Y, hXY, hYX₁, hYX₂⟩ :=
    mvN_glue ρ₁ ρ₂ σ₁ σ₂ hcomm hpb hlift
      (A₁ := A₁) (B₁ := B₁) (A₂ := A₂) (B₂ := B₂)
      (E₁ := ((E.sum (Mat.one P (max a₁ a₂))).2).map ρ₁)
      (E₂ := ((E.sum (Mat.one P (max a₁ a₂))).2).map ρ₂)
      hA₁B₁ heρ₁ hA₂B₂ heρ₂ hEσ
  -- the glued Murray–von Neumann equivalence
  have hcrit : Mat.MvN (Mat.sum (E.sum (Mat.one P (max a₁ a₂))) (Mat.one P t))
      (Mat.one P (N + max a₁ a₂ + t)) := by
    refine ⟨X, Y, ?_, ?_⟩
    · have hYX : Y * X = blk t ((E.sum (Mat.one P (max a₁ a₂))).2) := by
        refine mat_ext_of_maps ρ₁ ρ₂ σ₁ σ₂ hcomm hpb ?_ ?_
        · exact hYX₁.trans (blk_map ρ₁ t ((E.sum (Mat.one P (max a₁ a₂))).2)).symm
        · exact hYX₂.trans (blk_map ρ₂ t ((E.sum (Mat.one P (max a₁ a₂))).2)).symm
      exact hYX.trans (blk_mat_sum (E.sum (Mat.one P (max a₁ a₂))) t).symm
    · exact hXY
  -- compare `K₀`-classes
  have hep : (Mat.sum (E.sum (Mat.one P (max a₁ a₂))) (Mat.one P t)).IsIdem :=
    Mat.sum_idem (Mat.sum_idem hE (Mat.one_isIdem P (max a₁ a₂))) (Mat.one_isIdem P t)
  have hcls : cls (Mat.sum (E.sum (Mat.one P (max a₁ a₂))) (Mat.one P t)) =
      cls (Mat.one P (N + max a₁ a₂ + t)) :=
    cls_eq_of_mvN hep (Mat.one_isIdem P (N + max a₁ a₂ + t)) hcrit
  have hsplit : cls (Mat.sum (E.sum (Mat.one P (max a₁ a₂))) (Mat.one P t)) =
      cls E + cls (Mat.one P (max a₁ a₂)) + cls (Mat.one P t) := by
    rw [cls_sum (Mat.sum_idem hE (Mat.one_isIdem P (max a₁ a₂))) (Mat.one_isIdem P t),
      cls_sum hE (Mat.one_isIdem P (max a₁ a₂))]
  have hrhs : cls (Mat.one P (N + max a₁ a₂ + t)) =
      cls (Mat.one P N) + cls (Mat.one P (max a₁ a₂)) + cls (Mat.one P t) := by
    rw [← k2_one_sum_one P (N + max a₁ a₂) t,
      cls_sum (Mat.one_isIdem P (N + max a₁ a₂)) (Mat.one_isIdem P t),
      ← k2_one_sum_one P N (max a₁ a₂),
      cls_sum (Mat.one_isIdem P N) (Mat.one_isIdem P (max a₁ a₂))]
  rw [hsplit, hrhs] at hcls
  exact add_right_cancel (add_right_cancel hcls)

/-- **Injectivity half of the Mayer–Vietoris sequence for `K₀`** (Bass–Milnor–Murthy): in a cartesian square of rings with `σ₂ : P₂ → Q` surjective, if every invertible matrix over `Q` stably lifts to an invertible matrix over `P₂`, then `K₀ P → K₀ P₁ ⊕ K₀ P₂` is injective. (The kernel is the image of the connecting map `∂ : K₁(Q) → K₀ P`, `∂[S] = [M(P₁^n,P₂^n,S)] - [P^n]` (Land Lemma 4.56), which vanishes on matrices coming from `P₂` since `M(P₁^n,P₂^n,S) ≅ P^n` is free for `S` the `σ₂`-image of an invertible matrix (Land Remark 4.52); the lifting hypothesis makes `K₁(P₂) → K₁(Q)` onto. Cf. Land §4.3 Thm 4.57.) -/
theorem k0_mv_inj {P P₁ P₂ Q : Type} [Ring P] [Ring P₁] [Ring P₂] [Ring Q]
    (ρ₁ : P →+* P₁) (ρ₂ : P →+* P₂) (σ₁ : P₁ →+* Q) (σ₂ : P₂ →+* Q)
    (hs : Function.Surjective σ₂) (hcomm : σ₁.comp ρ₁ = σ₂.comp ρ₂)
    (hpb : ∀ x₁ x₂, σ₁ x₁ = σ₂ x₂ → ∃! x, ρ₁ x = x₁ ∧ ρ₂ x = x₂)
    (hlift : ∀ (n : ℕ) (u : Matrix (Fin n) (Fin n) Q), IsUnit u →
        ∃ (k : ℕ) (v : Matrix (Fin (n + k)) (Fin (n + k)) P₂), IsUnit v ∧
          v.map σ₂ = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks u 0 0 1)) :
    ∀ w : K0 P, K0.map ρ₁ w = 0 → K0.map ρ₂ w = 0 → w = 0 := by
  intro w hw₁ hw₂
  obtain ⟨F, n, hF, hw⟩ := k0_rep w
  have hc₁ : cls (F.map ρ₁) = cls (Mat.one P₁ n) := by
    have h : K0.map ρ₁ (cls F - cls (Mat.one P n)) = 0 := by rw [← hw]; exact hw₁
    rw [map_sub, k0map_cls ρ₁ hF, k0map_cls ρ₁ (Mat.one_isIdem P n), Mat.map_one' ρ₁ n] at h
    exact sub_eq_zero.mp h
  have hc₂ : cls (F.map ρ₂) = cls (Mat.one P₂ n) := by
    have h : K0.map ρ₂ (cls F - cls (Mat.one P n)) = 0 := by rw [← hw]; exact hw₂
    rw [map_sub, k0map_cls ρ₂ hF, k0map_cls ρ₂ (Mat.one_isIdem P n), Mat.map_one' ρ₂ n] at h
    exact sub_eq_zero.mp h
  have hfree := stable_free ρ₁ ρ₂ σ₁ σ₂ hcomm hpb hlift hF n hc₁ hc₂
  rw [hw, hfree, sub_self]

end

end Work.KT.Bott
