import Submission.Work.ThomBordism.Grassmann.Linear
import Submission.Work.ThomBordism.PontryaginThom.Item1

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The complement of an immersed rank-`8` plane in `ℝ^{k+8}`

This file is the *first step of the construction of `NormalBundleExists k`* (the normal bundle of an
embedding of a closed `8`-manifold into `ℝ^{k+8}`): the pointwise linear algebra of the complement.

Let `f : Fin 8 → ℝ^{k+8}` be a linearly independent family (the images of a basis of the tangent
space under the derivative of an immersion) and let `S : ChartIdx 8 k` be a set of `8` coordinates
on which the frame projects invertibly (`(frameMatrix S f).det ≠ 0`; such an `S` exists by
`Work.ThomBordism.Grassmann.exists_chartIdx_det_ne_zero`).  Then, splitting the coordinates of
`ℝ^{k+8}` into `S` and `Sᶜ` (`|S| = 8`, `|Sᶜ| = k`):

* `complProj S` / `complInj S` are the coordinate projection onto `Sᶜ` and the insertion of the
  `Sᶜ`-coordinates;
* `sMono f S` is the `S`-coordinate projection of the plane, `(coordProj S) ∘ (coeffMap f)`, and it
  is invertible (`sMonoEquiv`) exactly when `(frameMatrix S f).det ≠ 0`;
* `graphMap f S h` is the graph of the plane over the `S`-coordinates,
  `u ↦ (Sᶜ-coordinates of the plane vector with S-coordinates u)`;
* **`planeProj f S h`** is the projection onto the complement of the plane
  (`y ↦ y_{Sᶜ} - graph(y_S)`) and **`planeInj f S h = complInj S`** is the insertion of the
  complement (the `Sᶜ`-coordinates), so that
  `planeProj ∘ planeInj = 1`, `planeProj ∘ coeffMap f = 0`, and `ker (planeProj) = im (coeffMap f)`:
  the plane is a *direct summand* of `ℝ^{k+8}`.

The remaining statements of this file (the two identities, the kernel computation, the resulting
direct-sum decomposition `ℝ^8 × ℝ^k ≅ ℝ^{k+8}`, and the *continuity* in the parameter for a
continuous family of frames) are the interface that the bundle construction consumes: the transition
functions of the complement bundle `ν` are the composites `planeProj (A_i x) S ∘ planeInj (A_j x) T`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped Topology

namespace Work.ThomBordism.PontryaginThom

open Work.ThomBordism.Grassmann

noncomputable section

variable {k : ℕ}

/-- **The complement of a chart index**: `|Sᶜ| = k` for `S : ChartIdx 8 k` (an `8`-subset of
`Fin (8 + k)`). -/
theorem chartIdx_compl_card (S : ChartIdx 8 k) : S.1ᶜ.card = k := by
  rw [Finset.card_compl, Fintype.card_fin, S.2]
  omega

/-- The **complement coordinate projection** `y ↦ (y_j)_{j ∉ S}`. -/
def complProj (S : ChartIdx 8 k) : (Fin (8 + k) → ℝ) →ₗ[ℝ] (Fin k → ℝ) :=
  LinearMap.pi fun i =>
    LinearMap.proj (((S.1ᶜ.equivFinOfCardEq (chartIdx_compl_card S)).symm i : ↥S.1ᶜ) : Fin (8 + k))

/-- The **complement coordinate insertion**: the vector with the given `Sᶜ`-coordinates and
`S`-coordinates `0`. -/
def complInj (S : ChartIdx 8 k) : (Fin k → ℝ) →ₗ[ℝ] (Fin (8 + k) → ℝ) :=
  LinearMap.pi fun j =>
    if h : j ∈ S.1 then 0
    else LinearMap.proj ((S.1ᶜ.equivFinOfCardEq (chartIdx_compl_card S))
      ⟨j, Finset.mem_compl.mpr h⟩)

/-- The computation rule of `complProj`. -/
theorem complProj_apply (S : ChartIdx 8 k) (w : Fin (8 + k) → ℝ) (i : Fin k) :
    complProj S w i
      = w (((S.1ᶜ.equivFinOfCardEq (chartIdx_compl_card S)).symm i : ↥S.1ᶜ) : Fin (8 + k)) := by
  simp [complProj]

/-- The computation rule of `complInj`. -/
theorem complInj_apply (S : ChartIdx 8 k) (v : Fin k → ℝ) (j : Fin (8 + k)) :
    complInj S v j = if h : j ∈ S.1 then 0
      else v ((S.1ᶜ.equivFinOfCardEq (chartIdx_compl_card S))
        ⟨j, Finset.mem_compl.mpr h⟩) := by
  by_cases h : j ∈ S.1
  · simp [complInj, h]
  · simp only [complInj, LinearMap.pi_apply, dif_neg h, LinearMap.proj_apply]

/-- `complProj` is a left inverse of `complInj`. -/
theorem complProj_complInj (S : ChartIdx 8 k) :
    (complProj S).comp (complInj S) = LinearMap.id := by
  apply LinearMap.ext
  intro v
  funext i
  rw [LinearMap.comp_apply, LinearMap.id_apply, complProj_apply, complInj_apply]
  set e := S.1ᶜ.equivFinOfCardEq (chartIdx_compl_card S) with he
  have hnot : ¬ (((e.symm i : ↥S.1ᶜ)) : Fin (8 + k)) ∈ S.1 := Finset.mem_compl.mp (e.symm i).2
  rw [dif_neg hnot]
  have heq : (⟨↑(e.symm i), Finset.mem_compl.mpr hnot⟩ : ↥S.1ᶜ) = e.symm i := Subtype.ext rfl
  rw [heq, Equiv.apply_symm_apply]

/-- The `S`-coordinates of a vector in the image of `complInj` vanish. -/
theorem coordProj_complInj (S : ChartIdx 8 k) :
    (coordProj S).comp (complInj S) = 0 := by
  apply LinearMap.ext
  intro v
  funext i
  rw [LinearMap.comp_apply, LinearMap.zero_apply, coordProj_apply, complInj_apply]
  have hmem : (((S.1.equivFinOfCardEq S.2).symm i : ↥S.1) : Fin (8 + k)) ∈ S.1 :=
    ((S.1.equivFinOfCardEq S.2).symm i).2
  rw [dif_pos hmem]
  rfl

/-- The `S`-coordinate projection of the plane spanned by the frame `f`. -/
def sMono (f : Fin 8 → Amb (8 + k)) (S : ChartIdx 8 k) : (Fin 8 → ℝ) →ₗ[ℝ] (Fin 8 → ℝ) :=
  (coordProj S).comp (coeffMap f)

noncomputable def sMonoEquiv (f : Fin 8 → Amb (8 + k)) (S : ChartIdx 8 k)
    (h : (frameMatrix S f).det ≠ 0) : (Fin 8 → ℝ) ≃ₗ[ℝ] (Fin 8 → ℝ) :=
  LinearEquiv.ofBijective (sMono f S) (by
    have hker : LinearMap.ker (sMono f S) = ⊥ := (det_ne_zero_iff_ker S f).mp h
    have hinj : Function.Injective (sMono f S) := LinearMap.ker_eq_bot.mp hker
    exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hinj⟩)

/-- The plane vector with prescribed `S`-coordinates: `u ↦ (Sᶜ-coordinates of the plane vector whose
S-coordinates are u)`, i.e. the graph of the plane over the `S`-coordinates. -/
def graphMap (f : Fin 8 → Amb (8 + k)) (S : ChartIdx 8 k) (h : (frameMatrix S f).det ≠ 0) :
    (Fin 8 → ℝ) →ₗ[ℝ] (Fin k → ℝ) :=
  (complProj S).comp ((coeffMap f).comp
    ((sMonoEquiv f S h).symm : (Fin 8 → ℝ) →ₗ[ℝ] (Fin 8 → ℝ)))

/-- The **projection onto the complement of the plane** `im (coeffMap f)`:
`y ↦ y_{Sᶜ} - graph(y_S)`. -/
def planeProj (f : Fin 8 → Amb (8 + k)) (S : ChartIdx 8 k) (h : (frameMatrix S f).det ≠ 0) :
    (Fin (8 + k) → ℝ) →ₗ[ℝ] (Fin k → ℝ) :=
  complProj S - (graphMap f S h).comp (coordProj S)

/-- The **insertion of the complement** of the plane `im (coeffMap f)`: the `Sᶜ`-coordinates. -/
def planeInj (f : Fin 8 → Amb (8 + k)) (S : ChartIdx 8 k) (_h : (frameMatrix S f).det ≠ 0) :
    (Fin k → ℝ) →ₗ[ℝ] (Fin (8 + k) → ℝ) :=
  complInj S

/-- The computation rule of `planeProj`. -/
theorem planeProj_apply (f : Fin 8 → Amb (8 + k)) (S : ChartIdx 8 k)
    (h : (frameMatrix S f).det ≠ 0) (y : Fin (8 + k) → ℝ) :
    planeProj f S h y = complProj S y - graphMap f S h (coordProj S y) := rfl

/-- The computation rule of `planeInj`. -/
theorem planeInj_apply (f : Fin 8 → Amb (8 + k)) (S : ChartIdx 8 k)
    (h : (frameMatrix S f).det ≠ 0) (w : Fin k → ℝ) :
    planeInj f S h w = complInj S w := rfl

/-- `planeProj` is a left inverse of `planeInj`: the complement is really a complement. -/
theorem planeProj_planeInj (f : Fin 8 → Amb (8 + k)) (S : ChartIdx 8 k)
    (h : (frameMatrix S f).det ≠ 0) :
    (planeProj f S h).comp (planeInj f S h) = LinearMap.id := by
  rw [planeInj, planeProj, LinearMap.sub_comp, LinearMap.comp_assoc,
    coordProj_complInj, LinearMap.comp_zero, sub_zero, complProj_complInj]

/-- The graph map, composed with the `S`-coordinate projection of the plane, is the composition of
the complement projection with the plane. -/
theorem graphMap_comp_sMono (f : Fin 8 → Amb (8 + k)) (S : ChartIdx 8 k)
    (h : (frameMatrix S f).det ≠ 0) :
    (graphMap f S h).comp (sMono f S) = (complProj S).comp (coeffMap f) := by
  rw [graphMap, LinearMap.comp_assoc, LinearMap.comp_assoc]
  have hcomp : (((sMonoEquiv f S h).symm : (Fin 8 → ℝ) →ₗ[ℝ] (Fin 8 → ℝ)).comp (sMono f S))
      = LinearMap.id := by
    apply LinearMap.ext
    intro u
    rw [LinearMap.comp_apply, LinearMap.id_apply]
    exact LinearEquiv.symm_apply_apply (sMonoEquiv f S h) u
  rw [hcomp, LinearMap.comp_id]

/-- The plane is killed by the complement projection. -/
theorem planeProj_coeffMap (f : Fin 8 → Amb (8 + k)) (S : ChartIdx 8 k)
    (h : (frameMatrix S f).det ≠ 0) :
    (planeProj f S h).comp (coeffMap f) = 0 := by
  rw [planeProj, LinearMap.sub_comp, LinearMap.comp_assoc, ← sMono, graphMap_comp_sMono, sub_self]

/-- **The kernel of the complement projection is the plane**: the plane spanned by the frame `f` is
a direct summand of `ℝ^{k+8}`, with complement `im (complInj S)`. -/
theorem ker_planeProj {k : ℕ} (f : Fin 8 → Amb (8 + k)) (S : ChartIdx 8 k)
    (h : (frameMatrix S f).det ≠ 0) :
    LinearMap.ker (planeProj f S h) = LinearMap.range (coeffMap f) := by
  have hle : LinearMap.range (coeffMap f) ≤ LinearMap.ker (planeProj f S h) := by
    rintro y ⟨v, rfl⟩
    rw [LinearMap.mem_ker]
    have h0 := congrArg (fun g => g v) (planeProj_coeffMap f S h)
    simpa [LinearMap.comp_apply] using h0
  have hsurj : LinearMap.range (planeProj f S h) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro w
    refine ⟨complInj S w, ?_⟩
    have hA := congrArg (fun g => g w) (complProj_complInj S)
    have hB := congrArg (fun g => g w) (coordProj_complInj S)
    simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.zero_apply] at hA hB
    rw [planeProj_apply, hA, hB, map_zero, sub_zero]
  have hinj : Function.Injective (coeffMap f) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    have hv' : v ∈ LinearMap.ker (sMono f S) := by
      rw [LinearMap.mem_ker]
      show (coordProj S) (coeffMap f v) = 0
      rw [hv, map_zero]
    have hker : LinearMap.ker (sMono f S) = ⊥ := (det_ne_zero_iff_ker S f).mp h
    rw [hker] at hv'
    simpa using hv'
  have h1 : Module.finrank ℝ ↥(LinearMap.ker (planeProj f S h)) = 8 := by
    have hrn := LinearMap.finrank_range_add_finrank_ker (planeProj f S h)
    rw [hsurj, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at hrn
    omega
  have h2 : Module.finrank ℝ ↥(LinearMap.range (coeffMap f)) = 8 := by
    have hfin := (LinearEquiv.ofInjective (coeffMap f) hinj).finrank_eq
    rw [Module.finrank_fin_fun] at hfin
    exact hfin.symm
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [h1, h2])).symm

end

end Work.ThomBordism.PontryaginThom
