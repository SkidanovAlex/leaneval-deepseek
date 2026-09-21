import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Splitting a Euclidean space into one coordinate and the rest

We prove that for every coordinate `i : Fin n` of `EuclideanSpace ℝ (Fin n)` there is a
linear isometric equivalence
`EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] WithLp 2 (ℝ × EuclideanSpace ℝ {j : Fin n // j ≠ i})`
sending `x` to the pair `(x i, x restricted to the coordinates different from i)`.
-/

open scoped BigOperators RealInnerProductSpace
open Module WithLp

noncomputable section

namespace Commons.Analysis.InnerProductSpace

abbrev One : Type := PUnit.{1}

/-- Maps the `PUnit`-component to the coordinate `i` and the subtype component to itself. -/
def finSplitTo (n : ℕ) (i : Fin n) : One ⊕ {j : Fin n // j ≠ i} → Fin n
  | Sum.inl _ => i
  | Sum.inr j => j.1

/-- The inverse of `finSplitTo`. -/
def finSplitInv (n : ℕ) (i : Fin n) : Fin n → One ⊕ {j : Fin n // j ≠ i} :=
  fun j => if h : j = i then Sum.inl PUnit.unit else Sum.inr ⟨j, h⟩

/-- The equivalence `One ⊕ {j // j ≠ i} ≃ Fin n` singling out the coordinate `i`. -/
def finSplitEquiv (n : ℕ) (i : Fin n) : (One ⊕ {j : Fin n // j ≠ i}) ≃ Fin n where
  toFun := finSplitTo n i
  invFun := finSplitInv n i
  left_inv := by
    intro t
    cases t with
    | inl u =>
        simp [finSplitTo, finSplitInv]
    | inr j =>
        simp [finSplitTo, finSplitInv, j.2]
  right_inv := by
    intro j
    by_cases h : j = i
    · simp [finSplitTo, finSplitInv, h]
    · simp [finSplitTo, finSplitInv, h]

@[simp] theorem finSplitEquiv_inl (n : ℕ) (i : Fin n) :
    finSplitEquiv n i (Sum.inl PUnit.unit) = i := by
  rfl

@[simp] theorem finSplitEquiv_inr (n : ℕ) (i : Fin n) (j : {j : Fin n // j ≠ i}) :
    finSplitEquiv n i (Sum.inr j) = j.1 := by
  rfl

/-- Evaluation at the unique element: a linear equivalence `EuclideanSpace ℝ One ≃ₗ ℝ`. -/
def punitCoordLE : EuclideanSpace ℝ One ≃ₗ[ℝ] ℝ :=
  (WithLp.linearEquiv 2 ℝ (One → ℝ)).trans (LinearEquiv.funUnique One ℝ ℝ)

theorem punitCoordLE_apply (x : EuclideanSpace ℝ One) : punitCoordLE x = x PUnit.unit := by
  simp [punitCoordLE]

theorem punitCoord_norm (x : EuclideanSpace ℝ One) : ‖x PUnit.unit‖ = ‖x‖ := by
  have hx : ‖x‖₊ = ‖x PUnit.unit‖₊ := by
    calc
      ‖x‖₊ = NNReal.sqrt (∑ p : One, ‖x.ofLp p‖₊ ^ 2) := PiLp.nnnorm_eq_of_L2 x
      _ = NNReal.sqrt (‖x.ofLp PUnit.unit‖₊ ^ 2) := by
        rw [Finset.univ_unique]
        simp
      _ = ‖x.ofLp PUnit.unit‖₊ := NNReal.sqrt_sq _
  calc
    ‖x PUnit.unit‖ = ↑‖x PUnit.unit‖₊ := (coe_nnnorm _).symm
    _ = ↑‖x‖₊ := by rw [← hx]
    _ = ‖x‖ := coe_nnnorm _

/-- Evaluation at the unique element of `One` is a linear isometric equivalence
`EuclideanSpace ℝ One ≃ₗᵢ ℝ`. -/
def punitCoordIso : EuclideanSpace ℝ One ≃ₗᵢ[ℝ] ℝ where
  toLinearEquiv := punitCoordLE
  norm_map' := by
    intro x
    rw [punitCoordLE_apply]
    exact punitCoord_norm x

@[simp] theorem punitCoordIso_apply (x : EuclideanSpace ℝ One) : punitCoordIso x = x PUnit.unit := by
  rw [show punitCoordIso x = punitCoordLE x by rfl]
  exact punitCoordLE_apply x

/-- A congruence for the `L²`-product: applying isometries to each factor gives an isometry
of the wrapped product spaces. -/
def withLpProdCongr {A₁ A₂ B₁ B₂ : Type*}
    [SeminormedAddCommGroup A₁] [SeminormedAddCommGroup A₂]
    [SeminormedAddCommGroup B₁] [SeminormedAddCommGroup B₂]
    [Module ℝ A₁] [Module ℝ A₂] [Module ℝ B₁] [Module ℝ B₂]
    (e₁ : A₁ ≃ₗᵢ[ℝ] A₂) (e₂ : B₁ ≃ₗᵢ[ℝ] B₂) :
    WithLp 2 (A₁ × B₁) ≃ₗᵢ[ℝ] WithLp 2 (A₂ × B₂) where
  toFun := fun x => WithLp.toLp 2 (e₁ x.fst, e₂ x.snd)
  invFun := fun y => WithLp.toLp 2 (e₁.symm y.fst, e₂.symm y.snd)
  map_add' := by
    intro x y
    apply WithLp.ofLp_injective 2
    simp
  map_smul' := by
    intro c x
    apply WithLp.ofLp_injective 2
    simp
  left_inv := by
    intro x
    apply WithLp.ofLp_injective 2
    simp only [WithLp.toLp_fst, WithLp.toLp_snd]
    rw [e₁.symm_apply_apply, e₂.symm_apply_apply]
    apply Prod.ext
    · simp [WithLp.ofLp_fst]
    · simp [WithLp.ofLp_snd]
  right_inv := by
    intro y
    apply WithLp.ofLp_injective 2
    simp only [WithLp.toLp_fst, WithLp.toLp_snd]
    rw [e₁.apply_symm_apply, e₂.apply_symm_apply]
    apply Prod.ext
    · simp [WithLp.ofLp_fst]
    · simp [WithLp.ofLp_snd]
  norm_map' := by
    intro x
    calc
      ‖toLp 2 (e₁ x.fst, e₂ x.snd)‖ = ↑‖toLp 2 (e₁ x.fst, e₂ x.snd)‖₊ := (coe_nnnorm _).symm
      _ = ↑‖x‖₊ := by
        congr 1
        calc
          ‖toLp 2 (e₁ x.fst, e₂ x.snd)‖₊ =
              NNReal.sqrt (‖(toLp 2 (e₁ x.fst, e₂ x.snd)).fst‖₊ ^ 2 +
                ‖(toLp 2 (e₁ x.fst, e₂ x.snd)).snd‖₊ ^ 2) := WithLp.prod_nnnorm_eq_of_L2 _
          _ = NNReal.sqrt (‖e₁ x.fst‖₊ ^ 2 + ‖e₂ x.snd‖₊ ^ 2) := by simp
          _ = NNReal.sqrt (‖x.fst‖₊ ^ 2 + ‖x.snd‖₊ ^ 2) := by
            rw [e₁.nnnorm_map, e₂.nnnorm_map]
          _ = ‖x‖₊ := (WithLp.prod_nnnorm_eq_of_L2 x).symm
      _ = ‖x‖ := coe_nnnorm _

@[simp] theorem withLpProdCongr_apply {A₁ A₂ B₁ B₂ : Type*}
    [SeminormedAddCommGroup A₁] [SeminormedAddCommGroup A₂]
    [SeminormedAddCommGroup B₁] [SeminormedAddCommGroup B₂]
    [Module ℝ A₁] [Module ℝ A₂] [Module ℝ B₁] [Module ℝ B₂]
    (e₁ : A₁ ≃ₗᵢ[ℝ] A₂) (e₂ : B₁ ≃ₗᵢ[ℝ] B₂) (x : WithLp 2 (A₁ × B₁)) :
    withLpProdCongr e₁ e₂ x = WithLp.toLp 2 (e₁ x.fst, e₂ x.snd) := by
  rfl

/-- The linear isometric equivalence splitting the coordinate `i` from the rest of
`EuclideanSpace ℝ (Fin n)`. -/
def finSplitCoordIso (n : ℕ) (i : Fin n) :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ]
      WithLp 2 (ℝ × EuclideanSpace ℝ {j : Fin n // j ≠ i}) := by
  let S := {j : Fin n // j ≠ i}
  let c : EuclideanSpace ℝ (One ⊕ S) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finSplitEquiv n i)
  let sumIso : EuclideanSpace ℝ (One ⊕ S) ≃ₗᵢ[ℝ]
      WithLp 2 (EuclideanSpace ℝ One × EuclideanSpace ℝ S) :=
    PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : One ⊕ S => ℝ)
  let prodIso : WithLp 2 (EuclideanSpace ℝ One × EuclideanSpace ℝ S) ≃ₗᵢ[ℝ]
      WithLp 2 (ℝ × EuclideanSpace ℝ S) :=
    withLpProdCongr punitCoordIso (LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ S))
  exact (c.symm.trans sumIso).trans prodIso

theorem fin_split_coord_isometry {n : ℕ} (i : Fin n) :
    ∃ L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ]
        WithLp 2 (ℝ × EuclideanSpace ℝ {j : Fin n // j ≠ i}),
      (∀ x : EuclideanSpace ℝ (Fin n), (L x).ofLp.1 = x i) ∧
      (∀ x : EuclideanSpace ℝ (Fin n), ∀ j : {j : Fin n // j ≠ i},
        (((L x).ofLp.2 : EuclideanSpace ℝ {j : Fin n // j ≠ i}) j) = x j.1) := by
  refine ⟨finSplitCoordIso n i, ?_, ?_⟩
  · intro x
    unfold finSplitCoordIso
    simp [PiLp.sumPiLpEquivProdLpPiLp]
  · intro x j
    unfold finSplitCoordIso
    simp [PiLp.sumPiLpEquivProdLpPiLp]

end Commons.Analysis.InnerProductSpace