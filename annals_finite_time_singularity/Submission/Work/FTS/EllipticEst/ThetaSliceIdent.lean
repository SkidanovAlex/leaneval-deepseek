/-
Copyright: work module for the Elgindi finite-time singularity project.

# Characteristic loci: the angular slices of the mixed derivatives

The per-`z` comparison of the angular integrals relates, for a fixed radial level `z`, the
`j`-th group of the `H^k`-integrand of `∂_θ f` to the one-dimensional slice
`u_j(θ) = D_z^j f z θ`:

`(D_z^j (∂_θ f) z θ · w/sin^{η/2})² + ∑_i (D_z^j D_θ^i (∂_θ f) z θ · W)²`
`  = (w z)² · [ (u_j'(θ))² sin^{-η} + ∑_i (L^i (u_j')(θ))² sin^{-γ} ]`,

and similarly the group of `∂_θ² f` is `(w z)²` times `slicePhi` of `u_j`.  Both
identifications rest on the same two facts about the one-dimensional slices:

* `LopIter m (deriv (slice of D_z^j f)) θ = mixed j m (∂_θ f) z θ` (`LopIter_deriv_DzIter_eq_mixed`),
* `LopIter m (sliceV (slice of D_z^j f)) θ = mixed j m (∂_θ² f) z θ`
  (`LopIter_sliceV_DzIter_eq_mixed`),

where `LopIter` is the iterated action of `L = D_θ` on a *one-variable* function.  The point
of the two lemmas above is that they hold on the whole closed quadrant, at the boundary
points `θ = 0, π/2` included, where `deriv` and the higher iterates know nothing a priori:
this is achieved by replacing the derivative identities (which hold only on the *open*
neighbourhood `nbhU` of `SmoothNbhd`, `Work.Elliptic.pth_DzIter_eqOn`,
`Work.Spaces.DthIter_DzIter_comm_eqOn`) by the *local* form `LopIter_congr_nhds`, valid at
every point of `Iθ` because the neighbourhood of a point of `Iθ` lies in `nbhU`.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllipticEst.SliceAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false

/-! ## Locality of the iterated angular operator on one-variable functions -/

/-- If two functions of one variable agree near `θ`, then each of them is equal to the other
on a neighbourhood of every point of a neighbourhood of `θ`. -/
lemma eventuallyEq_nhds_mono {u v : ℝ → ℝ} {θ : ℝ} (h : u =ᶠ[𝓝 θ] v) :
    ∀ᶠ θ' in 𝓝 θ, u =ᶠ[𝓝 θ'] v := by
  obtain ⟨t, hts, htopen, hθt⟩ := mem_nhds_iff.mp h
  filter_upwards [htopen.mem_nhds hθt] with θ' hθ'
  exact eventually_of_mem (htopen.mem_nhds hθ') hts

/-- `Lop = L` only sees the germ of its argument. -/
lemma Lop_eventuallyEq {u v : ℝ → ℝ} {θ : ℝ} (h : u =ᶠ[𝓝 θ] v) :
    ∀ᶠ θ' in 𝓝 θ, Work.Spaces.Lop u θ' = Work.Spaces.Lop v θ' := by
  filter_upwards [eventuallyEq_nhds_mono h] with θ' hθ'
  simp only [Work.Spaces.Lop]
  rw [hθ'.deriv_eq]

/-- All the iterates of `Lop = L` only see the germ of their argument. -/
lemma LopIter_eventuallyEq {u v : ℝ → ℝ} {θ : ℝ} (h : u =ᶠ[𝓝 θ] v) (m : ℕ) :
    ∀ᶠ θ' in 𝓝 θ, LopIter m u θ' = LopIter m v θ' := by
  induction m with
  | zero => exact h
  | succ m ih =>
      have h' : LopIter m u =ᶠ[𝓝 θ] LopIter m v := ih
      simpa only [LopIter_succ] using Lop_eventuallyEq h'

/-- The iterates of `Lop = L` take the same value at `θ` on functions that agree near `θ`. -/
lemma LopIter_congr_nhds {u v : ℝ → ℝ} {θ : ℝ} (h : u =ᶠ[𝓝 θ] v) (m : ℕ) :
    LopIter m u θ = LopIter m v θ :=
  (LopIter_eventuallyEq h m).self_of_nhds

/-! ## The slices of `D_z^j f` on the open neighbourhood `nbhU` -/

/-- `sliceV` of the slice of `D_z^j f` is the slice of `D_z^j (∂_θ² f)`, on the open
neighbourhood `(-1,∞) × (-1, π/2+1)` of the quadrant (not only on `Iz × Iθ`). -/
lemma sliceV_DzIter_of_mem_nbhU {f : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd f) (j : ℕ)
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Set.Ioo (-1) (Real.pi / 2 + 1)) :
    sliceV (fun θ' => Work.Spaces.DzIter j f z θ') θ
      = Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ := by
  have hz1 : (-1 : ℝ) < z := by
    have h := hz; rw [Work.Spaces.Iz, Set.mem_Ici] at h; linarith
  have hnb : ∀ θ' ∈ Set.Ioo (-1) (Real.pi / 2 + 1), (z, θ') ∈ Work.Spaces.nbhU :=
    fun θ' hθ' => ⟨Set.mem_Ioi.mpr hz1, hθ'⟩
  have hU1 : ∀ θ' ∈ Set.Ioo (-1) (Real.pi / 2 + 1),
      Work.Spaces.pth (Work.Spaces.DzIter j f) z θ'
        = Work.Spaces.DzIter j (Work.Spaces.pth f) z θ' :=
    fun θ' hθ' => Work.Elliptic.pth_DzIter_eqOn f hsm j (hnb θ' hθ')
  have hev1 : (fun θ' => Work.Spaces.pth (Work.Spaces.DzIter j f) z θ')
      =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.DzIter j (Work.Spaces.pth f) z θ') := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    exact hU1 θ' hθ'
  have e1 : sliceV (fun θ' => Work.Spaces.DzIter j f z θ') θ
      = deriv (fun θ' => Work.Spaces.pth (Work.Spaces.DzIter j f) z θ') θ := rfl
  rw [e1, hev1.deriv_eq]
  have e2 : deriv (fun θ' => Work.Spaces.DzIter j (Work.Spaces.pth f) z θ') θ
      = Work.Spaces.pth (Work.Spaces.DzIter j (Work.Spaces.pth f)) z θ := rfl
  rw [e2]
  have hsm1 : Work.Spaces.SmoothNbhd (Work.Spaces.pth f) := Work.Spaces.SmoothNbhd.pth hsm
  have hU2 := Work.Elliptic.pth_DzIter_eqOn (Work.Spaces.pth f) hsm1 j (hnb θ hθ)
  have h2 : Work.Spaces.pthIter 2 f = Work.Spaces.pth (Work.Spaces.pth f) := rfl
  rw [h2]
  exact hU2

/-- Near a point of the closed quadrant, the second angular derivative of the slices of
`D_z^j f` is the slice of `D_z^j (∂_θ² f)`. -/
lemma sliceV_DzIter_nhds {f : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd f) (j : ℕ)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (fun θ' => sliceV (fun θ'' => Work.Spaces.DzIter j f z θ'') θ')
      =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ') := by
  have hmem : θ ∈ Set.Ioo (-1) (Real.pi / 2 + 1) :=
    ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  filter_upwards [isOpen_Ioo.mem_nhds hmem] with θ' hθ'
  exact sliceV_DzIter_of_mem_nbhU hsm j hz hθ'

/-- Near a point of the closed quadrant, the angular derivative of the slices of `D_z^j f`
is the slice of `D_z^j (∂_θ f)`. -/
lemma deriv_DzIter_nhds {f : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd f) (j : ℕ)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (fun θ' => deriv (fun θ'' => Work.Spaces.DzIter j f z θ'') θ')
      =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.DzIter j (Work.Spaces.pth f) z θ') := by
  have hz1 : (-1 : ℝ) < z := by
    have h := hz; rw [Work.Spaces.Iz, Set.mem_Ici] at h; linarith
  have hmem : θ ∈ Set.Ioo (-1) (Real.pi / 2 + 1) :=
    ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  filter_upwards [isOpen_Ioo.mem_nhds hmem] with θ' hθ'
  have hmem' : (z, θ') ∈ Work.Spaces.nbhU := Set.mem_prod.mpr ⟨Set.mem_Ioi.mpr hz1, hθ'⟩
  exact Work.Elliptic.pth_DzIter_eqOn f hsm j hmem'

/-! ## The two slice identities -/

/-- The `m`-th iterate of `L` applied to the derivative of the slice of `D_z^j f` is the
`(j,m)`-mixed derivative of `∂_θ f`. -/
lemma LopIter_deriv_DzIter_eq_mixed {f : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd f)
    (j m : ℕ) {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    LopIter m (deriv (fun θ' => Work.Spaces.DzIter j f z θ')) θ
      = Work.Spaces.mixed j m (Work.Spaces.pth f) z θ := by
  have h1 : LopIter m (deriv (fun θ' => Work.Spaces.DzIter j f z θ')) θ
      = LopIter m (fun θ' => Work.Spaces.DzIter j (Work.Spaces.pth f) z θ') θ :=
    LopIter_congr_nhds (deriv_DzIter_nhds hsm j hz hθ) m
  rw [h1]
  have h2 : LopIter m (fun θ' => Work.Spaces.DzIter j (Work.Spaces.pth f) z θ') θ
      = Work.Spaces.DthIter m
          (fun z' θ' => Work.Spaces.DzIter j (Work.Spaces.pth f) z' θ') z θ :=
    congrFun (LopIter_slice m
      (fun z' θ' => Work.Spaces.DzIter j (Work.Spaces.pth f) z' θ') z) θ
  rw [h2]
  have h3 : Work.Spaces.DthIter m
        (fun z' θ' => Work.Spaces.DzIter j (Work.Spaces.pth f) z' θ') z θ
      = Work.Spaces.DthIter m (Work.Spaces.DzIter j (Work.Spaces.pth f)) z θ := rfl
  rw [h3]
  exact DthIter_DzIter (Work.Spaces.SmoothNbhd.pth hsm) j m hz hθ

/-- The `m`-th iterate of `L` applied to the second derivative of the slice of `D_z^j f` is
the `(j,m)`-mixed derivative of `∂_θ² f`. -/
lemma LopIter_sliceV_DzIter_eq_mixed {f : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd f)
    (j m : ℕ) {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    LopIter m (sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ
      = Work.Spaces.mixed j m (Work.Spaces.pthIter 2 f) z θ := by
  have h1 : LopIter m (sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ
      = LopIter m (fun θ' => Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ') θ :=
    LopIter_congr_nhds (sliceV_DzIter_nhds hsm j hz hθ) m
  rw [h1]
  have h2 : LopIter m (fun θ' => Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ') θ
      = Work.Spaces.DthIter m
          (fun z' θ' => Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z' θ') z θ :=
    congrFun (LopIter_slice m
      (fun z' θ' => Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z' θ') z) θ
  rw [h2]
  have h3 : Work.Spaces.DthIter m
        (fun z' θ' => Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z' θ') z θ
      = Work.Spaces.DthIter m (Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f)) z θ := rfl
  rw [h3]
  have hsm2 : Work.Spaces.SmoothNbhd (Work.Spaces.pthIter 2 f) := by
    have : Work.Spaces.pthIter 2 f = Work.Spaces.pth (Work.Spaces.pth f) := rfl
    rw [this]
    exact Work.Spaces.SmoothNbhd.pth (Work.Spaces.SmoothNbhd.pth hsm)
  exact DthIter_DzIter hsm2 j m hz hθ

end Work.FTS.EllipticEst
