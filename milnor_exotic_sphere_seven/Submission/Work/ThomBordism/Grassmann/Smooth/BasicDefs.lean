import Mathlib
import Submission.Work.ThomBordism.Grassmann.Grassmannian
import Submission.Work.ThomBordism.Grassmann.GrassmannianTopology

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

/-!
# Coordinate projections and sections on `ℝ^{k+m}`

For a `k`-element set `S` of coordinates of `ℝ^{k+m}` (a `ChartIdx k m`) we set up

* the projections `projS S : ℝ^{k+m} → ℝ^k` (coordinates in `S`) and `projC S : ℝ^{k+m} → ℝ^m`
  (coordinates outside `S`);
* their sections `inclS S`, `inclC S` (the vectors supported on `S`, resp. on the complement).

These are the raw material of the charts of the oriented Grassmannian `G̃r_k(ℝ^{k+m})`: an oriented
plane `P` on which `projS S` is injective is the graph of `projC S ∘ (projS S |_P)⁻¹ : ℝ^k → ℝ^m`,
and the chart coordinate of `P` is that linear map.
-/

open scoped Topology

namespace Work.ThomBordism.Grassmann.Smooth

noncomputable section

variable {k m : ℕ}

/-! ## The coordinate index data -/

/-- The complement of the coordinate set `S` has `m` elements. -/
theorem card_compl (S : ChartIdx k m) : S.1ᶜ.card = m := by
  rw [Finset.card_compl, Fintype.card_fin, S.2]
  omega

/-- The `i`-th element of the coordinate set `S`. -/
def idxS (S : ChartIdx k m) (i : Fin k) : Fin (k + m) :=
  ((S.1.equivFinOfCardEq S.2).symm i : Fin (k + m))

/-- The `j`-th element of the complement of the coordinate set `S`. -/
def idxC (S : ChartIdx k m) (j : Fin m) : Fin (k + m) :=
  ((S.1ᶜ.equivFinOfCardEq (card_compl S)).symm j : Fin (k + m))

theorem idxS_mem (S : ChartIdx k m) (i : Fin k) : idxS S i ∈ S.1 :=
  ((S.1.equivFinOfCardEq S.2).symm i).2

theorem idxC_not_mem (S : ChartIdx k m) (j : Fin m) : idxC S j ∉ S.1 := by
  have h : idxC S j ∈ S.1ᶜ := ((S.1ᶜ.equivFinOfCardEq (card_compl S)).symm j).2
  simpa [Finset.mem_compl] using h

theorem idxS_apply (S : ChartIdx k m) (y : Fin (k + m)) (hy : y ∈ S.1) :
    idxS S ((S.1.equivFinOfCardEq S.2) ⟨y, hy⟩) = y := by
  simp only [idxS]
  rw [Equiv.symm_apply_apply]

theorem idxC_apply (S : ChartIdx k m) (y : Fin (k + m)) (hy : y ∈ S.1ᶜ) :
    idxC S ((S.1ᶜ.equivFinOfCardEq (card_compl S)) ⟨y, hy⟩) = y := by
  simp only [idxC]
  rw [Equiv.symm_apply_apply]

theorem idxS_injective (S : ChartIdx k m) : Function.Injective (idxS S) := by
  intro i j h
  have h2 : ((S.1.equivFinOfCardEq S.2).symm i) = ((S.1.equivFinOfCardEq S.2).symm j) :=
    Subtype.ext h
  simpa [idxS] using congrArg (S.1.equivFinOfCardEq S.2) h2

theorem idxC_injective (S : ChartIdx k m) : Function.Injective (idxC S) := by
  intro i j h
  have h2 : ((S.1ᶜ.equivFinOfCardEq (card_compl S)).symm i)
      = ((S.1ᶜ.equivFinOfCardEq (card_compl S)).symm j) := Subtype.ext h
  simpa [idxC] using congrArg (S.1ᶜ.equivFinOfCardEq (card_compl S)) h2

/-! ## The transfer between `ℝ^n` and `(Fin n → ℝ)` -/

/-- `WithLp.ofLp` as a continuous linear map. -/
def ofLpCLM (n : ℕ) : Amb n →L[ℝ] (Fin n → ℝ) :=
  (EuclideanSpace.equiv (Fin n) ℝ : Amb n →L[ℝ] (Fin n → ℝ))

/-- `WithLp.toLp` as a continuous linear map. -/
def toLpCLM (n : ℕ) : (Fin n → ℝ) →L[ℝ] Amb n :=
  ((EuclideanSpace.equiv (Fin n) ℝ).symm : (Fin n → ℝ) →L[ℝ] Amb n)

@[simp] theorem ofLpCLM_apply (n : ℕ) (x : Amb n) : ofLpCLM n x = x.ofLp := rfl

@[simp] theorem toLpCLM_apply (n : ℕ) (v : Fin n → ℝ) : toLpCLM n v = WithLp.toLp 2 v := rfl

theorem toLp_comp_ofLp (n : ℕ) : toLpCLM n ∘SL ofLpCLM n = 1 := by
  ext x; simp

theorem ofLp_comp_toLp (n : ℕ) : ofLpCLM n ∘SL toLpCLM n = 1 := by
  ext v; simp

/-- Transport a continuous linear map between function spaces to the corresponding map between
`Amb` spaces (i.e. conjugate by `WithLp`). -/
def ambify {n n' : ℕ} (F : (Fin n → ℝ) →L[ℝ] (Fin n' → ℝ)) : Amb n →L[ℝ] Amb n' :=
  (toLpCLM n').comp (F.comp (ofLpCLM n))

theorem ambify_comp {n n' n'' : ℕ} (F : (Fin n' → ℝ) →L[ℝ] (Fin n'' → ℝ))
    (G : (Fin n → ℝ) →L[ℝ] (Fin n' → ℝ)) :
    ambify (F.comp G) = (ambify F).comp (ambify G) := by
  ext x; simp [ambify]

theorem ambify_one (n : ℕ) : ambify (1 : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) = 1 := by
  ext x; simp [ambify]

theorem ambify_zero {n n' : ℕ} : ambify (0 : (Fin n → ℝ) →L[ℝ] (Fin n' → ℝ)) = 0 := by
  ext x; simp [ambify]

theorem ofLpCLM_ambify {n n' : ℕ} (F : (Fin n → ℝ) →L[ℝ] (Fin n' → ℝ)) (x : Amb n) :
    ofLpCLM n' (ambify F x) = F (ofLpCLM n x) := by
  simp [ambify]

/-! ## The projections and their sections -/

/-- The projection onto the coordinates of `S`, on the function space. -/
def projSFun (S : ChartIdx k m) : (Fin (k + m) → ℝ) →L[ℝ] (Fin k → ℝ) :=
  ContinuousLinearMap.pi fun i =>
    ContinuousLinearMap.proj (φ := fun _ : Fin (k+m) => ℝ) (idxS S i)

/-- The projection onto the coordinates outside `S`, on the function space. -/
def projCFun (S : ChartIdx k m) : (Fin (k + m) → ℝ) →L[ℝ] (Fin m → ℝ) :=
  ContinuousLinearMap.pi fun j =>
    ContinuousLinearMap.proj (φ := fun _ : Fin (k+m) => ℝ) (idxC S j)

/-- The section of `projS S`, on the function space. -/
def inclSFun (S : ChartIdx k m) : (Fin k → ℝ) →L[ℝ] (Fin (k + m) → ℝ) :=
  ∑ i : Fin k, (ContinuousLinearMap.proj (φ := fun _ : Fin k => ℝ) i).smulRight
    (Pi.single (idxS S i) 1)

/-- The section of `projC S`, on the function space. -/
def inclCFun (S : ChartIdx k m) : (Fin m → ℝ) →L[ℝ] (Fin (k + m) → ℝ) :=
  ∑ j : Fin m, (ContinuousLinearMap.proj (φ := fun _ : Fin m => ℝ) j).smulRight
    (Pi.single (idxC S j) 1)

@[simp] theorem projSFun_apply (S : ChartIdx k m) (x : Fin (k + m) → ℝ) (i : Fin k) :
    projSFun S x i = x (idxS S i) := rfl

@[simp] theorem projCFun_apply (S : ChartIdx k m) (x : Fin (k + m) → ℝ) (j : Fin m) :
    projCFun S x j = x (idxC S j) := rfl

/-- The projection of `ℝ^{k+m}` onto the coordinates of `S`. -/
def projS (S : ChartIdx k m) : Amb (k + m) →L[ℝ] Amb k := ambify (projSFun S)

/-- The projection of `ℝ^{k+m}` onto the coordinates outside `S`. -/
def projC (S : ChartIdx k m) : Amb (k + m) →L[ℝ] Amb m := ambify (projCFun S)

/-- The section of `projS S`. -/
def inclS (S : ChartIdx k m) : Amb k →L[ℝ] Amb (k + m) := ambify (inclSFun S)

/-- The section of `projC S`. -/
def inclC (S : ChartIdx k m) : Amb m →L[ℝ] Amb (k + m) := ambify (inclCFun S)

/-- The value of the section `inclS S`, read in the coordinates. -/
theorem inclS_ofLp (S : ChartIdx k m) (v : Amb k) :
    ofLpCLM (k + m) (inclS S v) = inclSFun S (ofLpCLM k v) :=
  ofLpCLM_ambify (inclSFun S) v

/-- The value of the section `inclC S`, read in the coordinates. -/
theorem inclC_ofLp (S : ChartIdx k m) (w : Amb m) :
    ofLpCLM (k + m) (inclC S w) = inclCFun S (ofLpCLM m w) :=
  ofLpCLM_ambify (inclCFun S) w

end

end Work.ThomBordism.Grassmann.Smooth
