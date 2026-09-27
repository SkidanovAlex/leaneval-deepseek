import Mathlib
import Submission.Work.PL.Defs

/-!
# Placing a simplex far from a compact set

A finite affinely independent vertex set `Δ` of `ℝᵐ` with at most `N` vertices can be placed in
`ℝᴺ` as the vertex set `Δ'` of a simplex which is disjoint from a prescribed compact set
(`Γ.space`), in such a way that some affine map `A : ℝᴺ →ᵃ[ℝ] ℝᵐ` maps `Δ'` onto `Δ` and the
simplex on `Δ'` onto the simplex on `Δ`.
-/

open Set Metric
open PL

namespace Work.Engulf.Aux

/-- The translation `x ↦ x + v` of `ℝᴺ`, as an affine map. -/
def trAff' {N : ℕ} (v : PL.E N) : PL.E N →ᵃ[ℝ] PL.E N where
  toFun := fun x => x + v
  linear := LinearMap.id
  map_vadd' := by intro p w; simp [add_assoc]

@[simp] lemma trAff'_apply {N : ℕ} (v x : PL.E N) : trAff' v x = x + v := rfl

lemma trAff'_injective {N : ℕ} (v : PL.E N) : Function.Injective (trAff' v) :=
  fun x y h => add_right_cancel (show x + v = y + v from h)

theorem exists_far_placement {N m : ℕ} (Γ : PL.Cx N) (hK : IsCompact Γ.space) (Δ : Finset (PL.E m))
    (hne : Δ.Nonempty) (hind : AffineIndependent ℝ (fun v : ↥Δ => (v : PL.E m)))
    (hcard : Δ.card ≤ N) :
    ∃ (Δ' : Finset (PL.E N)) (A : PL.E N →ᵃ[ℝ] PL.E m),
      Δ'.Nonempty ∧ Δ'.card = Δ.card ∧
      AffineIndependent ℝ (fun v : ↥Δ' => (v : PL.E N)) ∧
      A '' (Δ' : Set (PL.E N)) = (Δ : Set (PL.E m)) ∧
      A '' PL.simp Δ' = PL.simp Δ ∧ PL.simp Δ' ∩ Γ.space = ∅ := by
  classical
  have hNpos : 0 < N := (Finset.card_pos.mpr hne).trans_le hcard
  haveI : Nonempty ↥Δ := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  -- An injection of the vertex set into `Fin N`.
  have hcardι : Fintype.card (↥Δ) = Δ.card := Fintype.card_coe Δ
  have hle : Fintype.card (↥Δ) ≤ N := by rw [hcardι]; exact hcard
  let σ : ↥Δ → Fin N := fun v => Fin.castLE hle (Fintype.equivFin (↥Δ) v)
  have hσ : Function.Injective σ := fun a c h =>
    (Fintype.equivFin (↥Δ)).injective (Fin.castLE_injective hle h)
  let B : Module.Basis (Fin N) ℝ (PL.E N) := (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
  let b : ↥Δ → PL.E N := fun v => EuclideanSpace.single (σ v) 1
  have hBb : b = fun v => B (σ v) := by
    funext v
    exact (EuclideanSpace.basisFun_apply (Fin N) ℝ (σ v)).symm
  have hb_lin : LinearIndependent ℝ b := by
    rw [hBb]
    exact B.linearIndependent.comp σ hσ
  have hb_aff : AffineIndependent ℝ b := hb_lin.affineIndependent ℝ
  have hb_inj : Function.Injective b := hb_lin.injective
  -- A point of `ℝᴺ` far outside the compact `Γ.space`.
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : PL.E N)
  let c : PL.E N := EuclideanSpace.single ⟨0, hNpos⟩ 1
  let w : PL.E N := (|R| + 2) • c
  have hcnorm : ‖c‖ = 1 := by
    have hc : c = EuclideanSpace.single (⟨0, hNpos⟩ : Fin N) (1 : ℝ) := rfl
    rw [hc, EuclideanSpace.norm_single]
    norm_num
  have hwnorm : ‖w‖ = |R| + 2 := by
    have hpos : (0 : ℝ) ≤ |R| + 2 := by positivity
    simp only [w, norm_smul, hcnorm, mul_one]
    rw [Real.norm_eq_abs, abs_of_nonneg hpos]
  -- The linear map sending the basis vectors of `b` to the vertices of `Δ`.
  let f : Fin N → PL.E m := Function.extend σ (fun v : ↥Δ => (v : PL.E m)) 0
  let L : PL.E N →ₗ[ℝ] PL.E m := B.constr ℝ f
  have hLb : ∀ v : ↥Δ, L (b v) = (v : PL.E m) := by
    intro v
    have h1 : b v = B (σ v) := congrFun hBb v
    rw [h1]
    show (B.constr ℝ f) (B (σ v)) = (v : PL.E m)
    have h2 : (B.constr ℝ f) (B (σ v)) = f (σ v) := by simp
    rw [h2]
    exact Function.Injective.extend_apply hσ (fun u : ↥Δ => (u : PL.E m)) (0 : Fin N → PL.E m) v
  -- The affine map `A x = L (x - w)`.
  let A : PL.E N →ᵃ[ℝ] PL.E m :=
    { toFun := fun x => L (x - w)
      linear := L
      map_vadd' := by
        intro p v
        simp only [vadd_eq_add]
        rw [show v + p - w = v + (p - w) by abel, map_add] }
  let b' : ↥Δ → PL.E N := fun v => b v + w
  let Δ' : Finset (PL.E N) := Finset.univ.image b'
  let Δ₀ : Finset (PL.E N) := Finset.univ.image b
  have hb'_inj : Function.Injective b' := fun a c h => hb_inj (add_right_cancel h)
  have hb'_aff : AffineIndependent ℝ b' := by
    have h := hb_aff.map' (trAff' w) (trAff'_injective w)
    simpa only [b', Function.comp_def, trAff'_apply] using h
  have hΔ'coe : (Δ' : Set (PL.E N)) = Set.range b' := by
    simp only [Δ', Finset.coe_image, Finset.coe_univ, Set.image_univ]
  have hΔ₀coe : (Δ₀ : Set (PL.E N)) = Set.range b := by
    simp only [Δ₀, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  have hcoe' : (Δ' : Set (PL.E N)) = b' '' Set.univ := by
    simp only [Δ', Finset.coe_image, Finset.coe_univ]
  have hΔ'ne : Δ'.Nonempty := by
    show (Finset.image b' Finset.univ).Nonempty
    exact Finset.image_nonempty.mpr Finset.univ_nonempty
  have hΔ'card : Δ'.card = Δ.card := by
    show (Finset.image b' Finset.univ).card = Δ.card
    rw [Finset.card_image_of_injective _ hb'_inj, Finset.card_univ, Fintype.card_coe]
  have hΔ'aff : AffineIndependent ℝ (fun v : ↥Δ' => (v : PL.E N)) := by
    have h := hb'_aff.range
    rw [← hΔ'coe] at h
    exact h
  have hAapp : ∀ x : PL.E N, A x = L (x - w) := fun x => rfl
  have hAΔ' : A '' (Δ' : Set (PL.E N)) = (Δ : Set (PL.E m)) := by
    have h1 : ∀ v : ↥Δ, A (b' v) = (v : PL.E m) := by
      intro v
      rw [hAapp]
      have hb'v : b' v - w = b v := by
        simp only [b']
        rw [add_sub_cancel_right]
      rw [hb'v, hLb v]
    rw [hcoe', Set.image_image]
    rw [show (fun x : ↥Δ => A (b' x)) = (fun v : ↥Δ => (v : PL.E m)) from funext h1,
      Set.image_univ]
    exact Subtype.range_val
  have hAsimp : A '' PL.simp Δ' = PL.simp Δ := by
    simp only [PL.simp]
    rw [AffineMap.image_convexHull, hAΔ']
  have hΔ₀ball : PL.simp Δ₀ ⊆ closedBall (0 : PL.E N) 1 := by
    simp only [PL.simp]
    apply convexHull_min _ (convex_closedBall 0 1)
    intro y hy
    rw [hΔ₀coe] at hy
    obtain ⟨v, rfl⟩ := hy
    rw [mem_closedBall, dist_eq_norm, sub_zero]
    change ‖(EuclideanSpace.single (σ v) (1 : ℝ) : PL.E N)‖ ≤ 1
    rw [EuclideanSpace.norm_single]
    norm_num
  have hsimpΔ' : PL.simp Δ' = trAff' w '' PL.simp Δ₀ := by
    simp only [PL.simp]
    rw [hΔ'coe, hΔ₀coe]
    have hrange' : Set.range b' = trAff' w '' Set.range b := by
      ext y
      constructor
      · rintro ⟨v, rfl⟩
        exact ⟨b v, ⟨v, rfl⟩, rfl⟩
      · rintro ⟨z, ⟨v, rfl⟩, hz⟩
        exact ⟨v, hz⟩
    rw [hrange', AffineMap.image_convexHull]
  refine ⟨Δ', A, hΔ'ne, hΔ'card, hΔ'aff, hAΔ', hAsimp, ?_⟩
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨hx1, hx2⟩
  rw [hsimpΔ'] at hx1
  obtain ⟨t, ht, rfl⟩ := hx1
  have ht1 : ‖t‖ ≤ 1 := by
    have h' := hΔ₀ball ht
    rwa [mem_closedBall, dist_eq_norm, sub_zero] at h'
  have hx2R : ‖trAff' w t‖ ≤ R := by
    have h' := hR hx2
    rwa [mem_closedBall, dist_eq_norm, sub_zero] at h'
  have hbound : ‖w‖ ≤ ‖trAff' w t‖ + ‖t‖ := by
    have hwt : w = trAff' w t - t := by
      rw [trAff'_apply, add_sub_cancel_left]
    calc ‖w‖ = ‖trAff' w t - t‖ := congrArg (fun z => ‖z‖) hwt
      _ ≤ ‖trAff' w t‖ + ‖t‖ := norm_sub_le _ _
  rw [hwnorm] at hbound
  linarith [le_abs_self R, ht1, hx2R, hbound]

end Work.Engulf.Aux
