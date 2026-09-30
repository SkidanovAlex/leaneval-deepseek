import Mathlib
import Submission.Work.SSS.Transport.Geometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.SSS

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- **The transport along a path, expressed through the corners of the homotopy square.**  The
transport along the `t₀`-slice of a homotopy square `G` is the composite of the corner
isomorphisms of the square pullback along that slice. -/
theorem transportIsoPath_eq_corners (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    (G : C(unitInterval × unitInterval, B)) (t₀ : unitInterval) {b b' : B} (γ : Path b b')
    (hγ : ∀ s, G (t₀, s) = γ.toContinuousMap s)
    (h0 : G (t₀, 0) = b) (h1 : G (t₀, 1) = b') (j : ℕ) :
    transportIsoPath p hp γ j =
      fibreCornerIso p G (t₀, 0) h0 j ≪≫ cornerIso p hp G (t₀, 0) j ≪≫
        (cornerIso p hp G (t₀, 1) j).symm ≪≫ (fibreCornerIso p G (t₀, 1) h1 j).symm := by
  simp only [transportIsoPath]
  rw [eqToIso_fibre_eq p γ.source'.symm j, eqToIso_fibre_eq p γ.target' j]
  rw [edgeCore_eq_conj p hp G t₀ γ.toContinuousMap hγ b b' γ.source' γ.target' h0 h1 j
    (HZHomeoIso (homeoFibreEq p γ.target') j)]
  simp only [Iso.trans_assoc, Iso.self_symm_id_assoc, Iso.symm_self_id_assoc, Iso.self_symm_id,
    Iso.symm_self_id, Iso.refl_trans, Iso.trans_refl]

/-- The canonical fibre transport of a Serre fibration depends only on the homotopy class of the
path relative to the endpoints.  The proof compares the transports along `γ` and `γ'` through the
pullback over the square `I × I` along the homotopy: the fibre inclusions of the pullbacks of `γ`
and `γ'` are identified with the inclusions of the corresponding edge-fibres of the square, and the
corner inclusions of the square pullback are homotopic maps (free homotopies, no lifting needed),
hence agree on homology by homotopy invariance of singular homology. -/
theorem transportIsoPath_homotopic {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (j : ℕ)
    {b b' : B} (γ γ' : Path b b') (H : Path.Homotopic γ γ') :
    Work.SSS.transportIsoPath p hp γ j = Work.SSS.transportIsoPath p hp γ' j := by
  obtain ⟨F⟩ := H
  have hleft : ∀ u, F.toContinuousMap (u, 0) = b :=
    fun u => (F.prop' u 0 (by simp)).trans γ.source'
  have hright : ∀ u, F.toContinuousMap (u, 1) = b' :=
    fun u => (F.prop' u 1 (by simp)).trans γ.target'
  have hγid := transportIsoPath_eq_corners p hp F.toContinuousMap 0 γ
    (fun s => F.map_zero_left s) (hleft 0) (hright 0) j
  have hγ'id := transportIsoPath_eq_corners p hp F.toContinuousMap 1 γ'
    (fun s => F.map_one_left s) (hleft 1) (hright 1) j
  rw [hγid, hγ'id]
  rw [square_corner_identity p hp F.toContinuousMap (hleft 0) (hleft 1) (hright 0) (hright 1)
    hleft hright j]

end

end Work.SSS
