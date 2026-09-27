import Mathlib
import Submission.Work.Engulf.Auxi.exists_far_piece
import Submission.Work.Engulf.Auxi.exists_far_placement
import Submission.Work.Engulf.Auxi.exists_cx_adjunction

namespace Work.Engulf.E1g

/-- Sums over a subtype `↥q` of `f` coincide with sums over the finite set `q`. -/
private lemma sum_subtype_eq_sum {N : ℕ} {β : Type*} [AddCommMonoid β] (q : Finset (PL.E N))
    (f : PL.E N → β) : (∑ v : ↥q, f ↑v) = ∑ v ∈ q, f v := by
  rw [Finset.univ_eq_attach q, Finset.sum_attach]

/-- **`far_piece`**: as `Work.Engulf.Aux.exists_far_piece`, but the far vertex set `q` is affinely independent and the affine map `A` is injective on the simplex on `q`.  Needed by `E1_group`: a piece of a chart group is added as a far face `q` with `g' = ψ ∘ A` on `simp q`, and the overlap-control condition of the engulfing argument needs `g'` injective there.  Both extra facts follow from the rest: `A '' q = Δ` with `q.card = Δ.card` makes `A` bijective on `q`, whence `q` is affinely independent (apply the linear part of `A` to a dependence) and `A` is injective on `simp q` (a surjective affine map from `simp q` onto the equidimensional simplex `simp Δ`).  The explicit construction of `Work.Engulf.Aux.exists_far_placement` (`q = w + {e_{σ v}}`, `A x = L (x - w)`) makes this concrete: on `simp q` the map `A` is the barycentric-coordinate map for the affinely independent set `Δ`. -/
theorem far_piece {N m : ℕ} (Γ : PL.Cx N) (hfin : Γ.faces.Finite) (Δ : Finset (PL.E m))
    (hne : Δ.Nonempty) (hind : AffineIndependent ℝ (fun v : ↥Δ => (v : PL.E m)))
    (hcard : Δ.card ≤ N) :
    ∃ (Γ' : PL.Cx N) (q : Finset (PL.E N)) (A : PL.E N →ᵃ[ℝ] PL.E m),
      Γ'.faces.Finite ∧ Γ.faces ⊆ Γ'.faces ∧ q ∈ Γ'.faces ∧
      (∀ t ∈ Γ'.faces, t ∈ Γ.faces ∨ t ⊆ q) ∧
      Γ'.space = Γ.space ∪ PL.simp q ∧ PL.simp q ∩ Γ.space = ∅ ∧
      q.card = Δ.card ∧ A '' (q : Set (PL.E N)) = (Δ : Set (PL.E m)) ∧
      A '' PL.simp q = PL.simp Δ ∧ Set.InjOn A (PL.simp q) := by
  classical
  obtain ⟨Γ', q, A, hfin', hsub, hmem, hfaces, hspace, hdisj, hqcard, hAq, hAsimp⟩ :=
    Work.Engulf.Aux.exists_far_piece Γ hfin Δ hne hind hcard
  -- `A` is a bijection `q ≃ Δ`, because `A '' q = Δ` and the two sets have the same cardinality.
  have hqimage : q.image A = Δ := by
    apply Finset.coe_injective
    rw [Finset.coe_image]
    exact hAq
  have hinjOn_q : Set.InjOn A (q : Set (PL.E N)) := by
    rw [← Finset.card_image_iff]
    rw [hqimage, hqcard]
  -- The corresponding embedding `↥q ↪ ↥Δ`.
  let e : ↥q ↪ ↥Δ :=
    { toFun := fun v => ⟨A ↑v, by
        have h : A ↑v ∈ (A '' (q : Set (PL.E N))) := Set.mem_image_of_mem A v.2
        rwa [hAq] at h⟩
      inj' := by
        intro v w h
        exact Subtype.ext (hinjOn_q v.2 w.2 (congrArg Subtype.val h)) }
  -- Hence the image family `A ∘ (↑ : ↥q → ℝᴺ)` is affinely independent, being a reindexing of `Δ`.
  have h2 : ((fun δ : ↥Δ => (δ : PL.E m)) ∘ (e : ↥q → ↥Δ)) = fun v : ↥q => A ↑v := rfl
  have hp'_aff : AffineIndependent ℝ (fun v : ↥q => A (v : PL.E N)) :=
    h2 ▸ hind.comp_embedding e
  have hq_aff : AffineIndependent ℝ (fun v : ↥q => (v : PL.E N)) :=
    AffineIndependent.of_comp A hp'_aff
  refine ⟨Γ', q, A, hfin', hsub, hmem, hfaces, hspace, hdisj, hqcard, hAq, hAsimp, ?_⟩
  -- Injectivity of `A` on `simp q`: both points have barycentric coordinates on `q`, and `A`
  -- carries those to the (unique) barycentric coordinates on the affinely independent set `Δ`.
  intro x hx y hy hxy
  rw [PL.simp] at hx hy
  rw [Finset.mem_convexHull'] at hx hy
  obtain ⟨w, hw0, hw1, hwx⟩ := hx
  obtain ⟨w', hw0', hw1', hwy⟩ := hy
  have hmapsum : A (∑ v ∈ q, w v • v) = ∑ v ∈ q, w v • A v := by
    have key := Finset.map_affineCombination q id w hw1 A
    rw [Finset.affineCombination_eq_linear_combination q id w hw1] at key
    rw [Finset.affineCombination_eq_linear_combination q (A ∘ id) w hw1] at key
    simpa using key
  have hmapsum' : A (∑ v ∈ q, w' v • v) = ∑ v ∈ q, w' v • A v := by
    have key := Finset.map_affineCombination q id w' hw1' A
    rw [Finset.affineCombination_eq_linear_combination q id w' hw1'] at key
    rw [Finset.affineCombination_eq_linear_combination q (A ∘ id) w' hw1'] at key
    simpa using key
  have hEqNm : ∑ v ∈ q, w v • A v = ∑ v ∈ q, w' v • A v := by
    rw [← hmapsum, ← hmapsum', hwx, hwy, hxy]
  have hsum1 : ∑ v : ↥q, w ↑v = 1 := by
    rw [show (∑ v : ↥q, w ↑v) = ∑ v ∈ q, w v from sum_subtype_eq_sum q w, hw1]
  have hsum1' : ∑ v : ↥q, w' ↑v = 1 := by
    rw [show (∑ v : ↥q, w' ↑v) = ∑ v ∈ q, w' v from sum_subtype_eq_sum q w', hw1']
  have hEqSub : (∑ v : ↥q, w ↑v • (A ↑v)) = ∑ v : ↥q, w' ↑v • (A ↑v) := by
    rw [show (∑ v : ↥q, w ↑v • (A ↑v)) = ∑ v ∈ q, w v • A v
          from sum_subtype_eq_sum q (fun v => w v • A v),
        show (∑ v : ↥q, w' ↑v • (A ↑v)) = ∑ v ∈ q, w' v • A v
          from sum_subtype_eq_sum q (fun v => w' v • A v)]
    exact hEqNm
  have heq : (Finset.affineCombination ℝ Finset.univ (fun v : ↥q => A (v : PL.E N)))
        (fun v : ↥q => w ↑v)
      = (Finset.affineCombination ℝ Finset.univ (fun v : ↥q => A (v : PL.E N)))
        (fun v : ↥q => w' ↑v) := by
    rw [Finset.affineCombination_eq_linear_combination Finset.univ
          (fun v : ↥q => A (v : PL.E N)) (fun v : ↥q => w ↑v) hsum1,
        Finset.affineCombination_eq_linear_combination Finset.univ
          (fun v : ↥q => A (v : PL.E N)) (fun v : ↥q => w' ↑v) hsum1']
    exact hEqSub
  have hkey := (affineIndependent_iff_indicator_eq_of_affineCombination_eq ℝ
    (fun v : ↥q => A (v : PL.E N))).mp hp'_aff Finset.univ Finset.univ
    (fun v : ↥q => w ↑v) (fun v : ↥q => w' ↑v) hsum1 hsum1' heq
  have hWeq : ∀ v : ↥q, w ↑v = w' ↑v := by
    intro v
    have hv := congrFun hkey v
    simp only [Finset.coe_univ] at hv
    simpa using hv
  rw [← hwx, ← hwy]
  refine Finset.sum_congr rfl (fun v hv => ?_)
  rw [show w v = w' v from hWeq ⟨v, hv⟩]

end Work.Engulf.E1g
