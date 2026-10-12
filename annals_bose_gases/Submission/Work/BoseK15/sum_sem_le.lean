import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseK15.lattice_sum_scaled
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseK15.sum_sem_le` — the scaled momentum sum over the box modes

FS §10 sums `(1+‖k‖)^{-4}` over the *excited* modes of the box and needs the
result to be of order `ℓ³`, the box volume (`K15Input.sum_sem`).  This file
supplies that bound, with the explicit absolute constant `520`.

The two ingredients are:

* **the mode/lattice transfer** (below).  `OnDualLattice ℓ kmom` says that every
  mode label is a *distinct* dual-lattice momentum `kmom q = ℓ⁻¹ • vec n_q`
  (`Work.BoseB4.vec n = 2πn`).  Choosing the lattice index `n_q = hlat.lift q`
  (injective) turns the mode sum into a lattice sum,
  `∑_q (1+‖kmom q‖)^{-4} = ∑_{n ∈ image} (1 + ‖vec n‖/ℓ)^{-4}`;
* **the pure lattice bound** `Work.BoseK15.lattice_sum_scaled`, which needs no
  mode data at all: for *every* finite set `S` of lattice indices,
  `∑_{n ∈ S} (1 + ‖vec n‖/ℓ)^{-4} ≤ 520 ℓ³`.

The crude count `card_le_of_vec_norm_le` bounds the number of lattice points in
a ball of radius `ℓ` by `(ℓ/π+1)³ ≤ 8ℓ³`, and the tail
`sum_inv_one_add_norm_tail` bounds the part with `‖vec n‖ > ℓ`; the two
contributions `8ℓ³` and `512ℓ³` add up to `520ℓ³`.  Only the *existence* of an
absolute constant is used downstream (`K15Input.K₀_sem`), so `520` is not sharp
— the true asymptotics are the integral `ℓ³∫(1+‖k‖)^{-4}dk = ℓ³/(6π²)`.
-/

noncomputable section

open scoped BigOperators
open Classical

namespace Work.BoseK15

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The mode/lattice transfer -/

/-- **The norm of a mode label, read off its lattice index.**  `hlat.lift q` is
the lattice index of the mode `q`, i.e. `kmom q = ℓ⁻¹ • vec (hlat.lift q)`, so
`‖kmom q‖ = ‖vec (hlat.lift q)‖ / ℓ` for `ℓ > 0`. -/
private lemma norm_lift_of_dualLattice {Mode : Type*} {ℓ : ℝ} {kmom : Mode → ℝ³}
    (h : OnDualLattice ℓ kmom) (hℓpos : 0 < ℓ) (q : Mode) :
    ‖kmom q‖ = ‖Work.BoseB4.vec (h.lift q)‖ / ℓ := by
  rw [h.lift_spec q, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hℓpos)]
  ring

/-- **The mode sum as a lattice sum.**  Because the mode labels are *distinct*
dual-lattice points, the sum over the excited modes of any function of `‖kmom ·‖`
equals the corresponding sum over the set of lattice indices of those modes. -/
private lemma sum_excited_eq_sum_lattice {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] {ℓ : ℝ} {kmom : Mode → ℝ³} (h : OnDualLattice ℓ kmom)
    (hℓpos : 0 < ℓ) :
    (∑ q ∈ Work.BoseB7.excited Mode, (1 + ‖kmom q‖) ^ (-(4 : ℝ)))
      = ∑ n ∈ (Work.BoseB7.excited Mode).image h.lift,
          (1 + ‖Work.BoseB4.vec n‖ / ℓ) ^ (-(4 : ℝ)) := by
  rw [Finset.sum_image (fun x _ y _ hxy => h.lift_injective hxy)]
  exact Finset.sum_congr rfl (fun q _ => by rw [norm_lift_of_dualLattice h hℓpos q])

/-! ## 2. The momentum sum -/

/-- **The scaled momentum sum over the box modes is `O(ℓ³)`** (FS §10,
`K15Input.sum_sem`): the sum of `(1+‖k‖)^{-4}` over the excited modes of the box
of side `ℓ ≥ 1` is bounded by `520 ℓ³`, with an *absolute* constant. -/
theorem sum_sem_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
      (ℓ : ℝ) (hℓ : 1 ≤ ℓ) (kmom : Mode → EuclideanSpace ℝ (Fin 3))
      (hlat : Work.BoseK15.OnDualLattice ℓ kmom),
      (∑ q ∈ Work.BoseB7.excited Mode, (1 + ‖kmom q‖) ^ (-(4 : ℝ))) ≤ C * ℓ ^ 3 := by
  refine ⟨520, by norm_num, ?_⟩
  intro Mode _ _ _ ℓ hℓ kmom hlat
  have hℓpos : 0 < ℓ := lt_of_lt_of_le one_pos hℓ
  rw [sum_excited_eq_sum_lattice hlat hℓpos]
  exact lattice_sum_scaled ℓ hℓ _

end Work.BoseK15
