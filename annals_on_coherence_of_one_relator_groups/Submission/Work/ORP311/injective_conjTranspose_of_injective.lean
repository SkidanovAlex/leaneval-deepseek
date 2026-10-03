import Mathlib
import Submission.Work.ORP311.P311Defs
import Submission.Work.ORP311.eq_bot_of_hdim_eq_zero

namespace Work.ORP311

/-- **Injectivity is preserved by the conjugate transpose.**

For a square matrix `Z` over the group von Neumann algebra `N(G)`, injectivity of the matrix
operator `matOp Z` implies injectivity of `matOp Z†`.

The point is that `N(G)` is a *finite* von Neumann algebra, so its von Neumann dimension is
faithful: the kernel of a matrix operator and the kernel of its adjoint have the same dimension
(`Work.ORVonNeumann.Rep.vnKeyRank`), and a subspace of vanishing dimension is trivial
(`Work.ORP311.eq_bot_of_hdim_eq_zero`).

Concretely, `hZ` says that `ker (matOp Z) = ⊥`, hence `hdim (ker (matOp Z)) = 0`.  The key rank
identity `vnKeyRank Z`, together with `vnMatOpAdjoint` (`(matOp Z)† = matOp Z.conjTranspose`),
then identifies `hdim (ker (matOp Z†)) = hdim (ker (matOp Z)) = 0`.  Since `matOp Z†` is
equivariant (`vnMatOpEquivariant`), its kernel is invariant under the block diagonal right
regular action `diagOp`, so faithfulness of the dimension (`eq_bot_of_hdim_eq_zero`) forces
`ker (matOp Z†) = ⊥`, i.e. injectivity. -/
theorem injective_conjTranspose_of_injective {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] {n : ℕ} (Z : Matrix (Fin n) (Fin n) ↥(Work.ORVonNeumann.groupVonNeumann G)) (hZ : Function.Injective (Work.ORVonNeumann.Rep.matOp (G := G) Z)) : Function.Injective (Work.ORVonNeumann.Rep.matOp (G := G) Z.conjTranspose) := by
  classical
  -- Injectivity of `matOp Z` says that its kernel is the trivial subspace.
  have hker : (Work.ORVonNeumann.Rep.matOp (G := G) Z).ker = ⊥ := LinearMap.ker_eq_bot.mpr hZ
  -- Hence the von Neumann dimension of that kernel vanishes.
  have h0 : Work.ORVonNeumann.Rep.hdim (Work.ORVonNeumann.Rep.matOp (G := G) Z).ker = 0 :=
    (Work.ORVonNeumann.Rep.hdim_congr hker).trans (Work.ORVonNeumann.Rep.hdim_bot n)
  -- The key rank identity compares the dimensions of the kernels of `matOp Z` and of its adjoint,
  -- and the adjoint of `matOp Z` is `matOp Z†`.
  have hkey := Work.ORVonNeumann.Rep.vnKeyRank (G := G) Z
  rw [Work.ORVonNeumann.Rep.vnMatOpAdjoint] at hkey
  have h0' : Work.ORVonNeumann.Rep.hdim (Work.ORVonNeumann.Rep.matOp (G := G) Z.conjTranspose).ker
      = 0 := by linarith
  -- The kernel of the equivariant operator `matOp Z†` is `diagOp`-invariant.
  have hinv : ∀ g : G, ∀ x ∈ (Work.ORVonNeumann.Rep.matOp (G := G) Z.conjTranspose).ker,
      Work.ORVonNeumann.Rep.diagOp (G := G) n g x
        ∈ (Work.ORVonNeumann.Rep.matOp (G := G) Z.conjTranspose).ker := by
    intro g x hx
    exact Work.ORVonNeumann.Rep.equivariant_ker (G := G)
      (Work.ORVonNeumann.Rep.vnMatOpEquivariant (G := G) Z.conjTranspose) g x
      (LinearMap.mem_ker.mp hx)
  -- Faithfulness of the dimension at zero turns the vanishing dimension into a trivial kernel.
  have hbot : (Work.ORVonNeumann.Rep.matOp (G := G) Z.conjTranspose).ker = ⊥ :=
    eq_bot_of_hdim_eq_zero (K := (Work.ORVonNeumann.Rep.matOp (G := G) Z.conjTranspose).ker)
      hinv h0'
  exact LinearMap.ker_eq_bot.mp hbot

end Work.ORP311
