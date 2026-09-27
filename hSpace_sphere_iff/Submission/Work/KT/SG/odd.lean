import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.BallKFrame
import Submission.Work.KT.SG.BottSusp
import Submission.Work.KT.SG.transfer
import Submission.Work.KT.SG.kpair_R_vanishing
import Submission.Work.KT.ext_product
import Submission.Work.KT.ExtGen.pairIso_of_linearEquiv

/-!
# `Work.KT.SG.oddKpair_vanishing` — the reduced `K`-theory of an odd sphere vanishes

For `finrank ℝ V = 2j+1` the augmentation `K₀(Kpair V) → K₀(ℂ)` is injective, i.e.
`K̃(S^{2j+1}) = 0`.  This is the *odd* clause of `Work.KT.ball_K`, proved here directly, without any
Adams operation:

* **Base** (`j = 0`, `dim V = 1`): `K̃(S¹) = 0` (`SG.kpair_R_vanishing`), transported to `Euc 1`
  along a linear isomorphism (`SG.kpair_vanishing_transfer`).
* **Step** (`dim V → dim V + 2`): by `SG.bott_susp_hopf` (which rests on `Work.KT.fund_product`),
  the external product with the reduced Hopf class of `Kpair (Euc 2)` is an isomorphism
  `K̃(Kpair V) ≅ K̃(Kpair (V × Euc 2))`; hence vanishing for odd-dimensional `V` gives vanishing
  for `V × Euc 2`, and one transports back to `Euc (2j+3)` along a linear isomorphism.

The external product `μx` used in the step is the one supplied by `Work.KT.ext_product`.
Consequently the vanishing below depends on `fund_product` alone (and on the library of the Bott
chain), not on the ψ-chain `Psi/*`.
-/

namespace Work.KT
namespace SG

open Matrix

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

/-- `K̃(S^{2j+1}) = 0`: for `finrank ℝ V = 2j+1` the augmentation is injective on `K₀(Kpair V)`. -/
theorem oddKpair_vanishing (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (j : ℕ) (hV : Module.finrank ℝ V = 2 * j + 1)
    (y0 : Ball V) (hy0 : y0 ∈ bdry V) :
    ∀ z : K0 (Kpair V), K0.mapA (augPair V y0) z = 0 → z = 0 := by
  have hfr : Module.finrank ℝ (Euc (2 * j + 1)) = Module.finrank ℝ V := by
    rw [finrank_euclideanSpace_fin]
    exact hV.symm
  obtain ⟨e⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq hfr
  intro z hz
  exact kpair_vanishing_transfer e y0 hy0 (euc_odd_vanishing j) z hz
where
  /-- The vanishing on the Euclidean model spaces `Euc (2j+1)`, by induction on `j`. -/
  euc_odd_vanishing : ∀ j : ℕ, ∀ (y0 : Ball (Euc (2 * j + 1))),
      y0 ∈ bdry (Euc (2 * j + 1)) →
      ∀ z : K0 (Kpair (Euc (2 * j + 1))), K0.mapA (augPair (Euc (2 * j + 1)) y0) z = 0 → z = 0
  | 0 => by
    intro y0 hy0 z hz
    have hfr : Module.finrank ℝ ℝ = Module.finrank ℝ (Euc 1) := by
      rw [finrank_euclideanSpace_fin, Module.finrank_self]
    obtain ⟨e⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq hfr
    exact kpair_vanishing_transfer e y0 hy0 (fun y hy => kpair_R_vanishing y hy) z hz
  | j + 1 => by
    intro y0 hy0 z hz
    haveI : Nonempty (Fin (2 * j + 1)) := ⟨⟨0, by omega⟩⟩
    have hprod : ∀ (y : Ball (Euc (2 * j + 1) × Euc 2)),
        y ∈ bdry (Euc (2 * j + 1) × Euc 2) →
        ∀ w : K0 (Kpair (Euc (2 * j + 1) × Euc 2)),
          K0.mapA (augPair (Euc (2 * j + 1) × Euc 2) y) w = 0 → w = 0 := by
      intro y hy w hw
      obtain ⟨y0V, hy0V⟩ := bdry_nonempty (E := Euc (2 * j + 1))
      obtain ⟨y0W, hy0W⟩ := bdry_nonempty (E := Euc 2)
      obtain ⟨μx, hμx⟩ := (ext_product (Euc (2 * j + 1)) (Euc 2) y0V hy0V y0W hy0W y hy).1
      obtain ⟨H, _hH0, hsurj, _hinj⟩ :=
        bott_susp_hopf (Euc (2 * j + 1)) (Euc 2) y0V hy0V y0W hy0W y hy
          (by rw [finrank_euclideanSpace_fin]; omega)
          (by rw [finrank_euclideanSpace_fin]) μx hμx
      obtain ⟨s, hs, hsz⟩ := hsurj w hw
      have hs0 : s = 0 := euc_odd_vanishing j y0V hy0V s hs
      rw [hs0, map_zero, AddMonoidHom.zero_apply] at hsz
      exact hsz.symm
    have hfr : Module.finrank ℝ (Euc (2 * j + 1) × Euc 2)
        = Module.finrank ℝ (Euc (2 * (j + 1) + 1)) := by
      rw [Module.finrank_prod, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin,
        finrank_euclideanSpace_fin]
      omega
    obtain ⟨e⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq hfr
    exact kpair_vanishing_transfer e y0 hy0 hprod z hz

end

end SG

end Work.KT
