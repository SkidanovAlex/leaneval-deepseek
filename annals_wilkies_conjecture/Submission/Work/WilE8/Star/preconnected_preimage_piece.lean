/-
  WilE8 / Star — a `StarPiece` in one variable is connected, and so is its `psiV`-preimage.

  `P.set` is the image of a connected component under the (continuous) coordinate projection
  `projFirst`, hence preconnected.  For `n = 1` the map `psiV : ℝ → ℝ` is merely the monotone
  map `psi`, so it cannot tear a set apart: over `Fin 1 → ℝ` (which is `ℝ` up to the
  homeomorphism `Homeomorph.funUnique`) the ψ-transported piece is again preconnected.

  The mathematical content is the one-variable monotonicity of `psi`, proved via the
  identities `psi x = tanh (arsinh x)` and `artanh (tanh x) = x`.
-/
import Mathlib
import Submission.Work.WilE8.Basic

noncomputable section
open Classical Topology

namespace Work.WilE8.Star
open WilkiesDesign WilkiesDesign.E

/-! ## Monotonicity of `psi` -/

/-- `Real.tanh` is strictly increasing.  (`tanh` is the left inverse of the strictly increasing
`artanh` on `(-1,1)`, which forces it to be strictly increasing too.) -/
lemma strictMono_tanh : StrictMono Real.tanh := by
  intro x y hxy
  have hx : Real.tanh x ∈ Set.Ioo (-1 : ℝ) 1 := ⟨Real.neg_one_lt_tanh x, Real.tanh_lt_one x⟩
  have hy : Real.tanh y ∈ Set.Ioo (-1 : ℝ) 1 := ⟨Real.neg_one_lt_tanh y, Real.tanh_lt_one y⟩
  refine (Real.strictMonoOn_artanh.lt_iff_lt hx hy).mp ?_
  rw [Real.artanh_tanh, Real.artanh_tanh]
  exact hxy

/-- The frozen `psi` is monotone, being `tanh ∘ arsinh`. -/
lemma monotone_psi : Monotone WilkiesDesign.E.psi := by
  have h : WilkiesDesign.E.psi = fun x => Real.tanh (Real.arsinh x) := by
    funext x
    exact (Real.tanh_arsinh x).symm
  rw [h]
  exact strictMono_tanh.monotone.comp Real.arsinh_strictMono.monotone

/-! ## The target -/

theorem preconnected_preimage_piece (P : WilkiesDesign.E.StarPiece 1) :
    IsPreconnected (WilkiesDesign.E.psiV ⁻¹' P.set) := by
  -- `projFirst` is continuous (it just reads coordinates).
  have hcont : Continuous (WilkiesDesign.E.projFirst 1 P.m) := by
    unfold WilkiesDesign.E.projFirst
    exact continuous_pi fun i => continuous_apply _
  -- `P.set` is the image of a connected component under that projection.
  have hP : IsPreconnected P.set := by
    rw [WilkiesDesign.E.StarPiece.set]
    exact IsPreconnected.image isPreconnected_connectedComponentIn
      (WilkiesDesign.E.projFirst 1 P.m) hcont.continuousOn
  -- Read `Fin 1 → ℝ` as `ℝ`.
  set e : (Fin 1 → ℝ) ≃ₜ ℝ := Homeomorph.funUnique (Fin 1) ℝ
  have hev : ∀ x : Fin 1 → ℝ, e (WilkiesDesign.E.psiV x) = WilkiesDesign.E.psi (e x) :=
    fun x => rfl
  -- In `ℝ`, the preimage under the monotone map `psi` of the (order-)connected `e '' P.set`
  -- is order-connected, hence preconnected.
  have hT : IsPreconnected (WilkiesDesign.E.psi ⁻¹' (e '' P.set)) := by
    apply Set.OrdConnected.isPreconnected
    exact (hP.image e e.continuous.continuousOn).ordConnected.preimage_mono monotone_psi
  -- Transporting back along the homeomorphism `e` preserves preconnectedness (as it is a
  -- continuous image of `e.symm`).
  have hTe : IsPreconnected (e ⁻¹' (WilkiesDesign.E.psi ⁻¹' (e '' P.set))) := by
    have himg : e ⁻¹' (WilkiesDesign.E.psi ⁻¹' (e '' P.set))
        = e.symm '' (WilkiesDesign.E.psi ⁻¹' (e '' P.set)) := by
      ext y
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · intro hy; exact ⟨e y, hy, e.symm_apply_apply y⟩
      · rintro ⟨z, hz, rfl⟩; rwa [e.apply_symm_apply]
    rw [himg]
    exact hT.image e.symm e.symm.continuous.continuousOn
  -- Identifications `e (psiV x) = psi (e x)` turn the two sides into the same set.
  have key : WilkiesDesign.E.psiV ⁻¹' P.set
      = e ⁻¹' (WilkiesDesign.E.psi ⁻¹' (e '' P.set)) := by
    ext x
    constructor
    · intro hx
      exact ⟨WilkiesDesign.E.psiV x, hx, hev x⟩
    · rintro ⟨z, hz, hze⟩
      have h1 : e z = e (WilkiesDesign.E.psiV x) := by rw [hze, ← hev x]
      have h2 : z = WilkiesDesign.E.psiV x := e.injective h1
      rw [h2] at hz
      exact hz
  rw [key]
  exact hTe

end Work.WilE8.Star
