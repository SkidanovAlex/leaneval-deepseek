import Mathlib
import Submission.Work.DSM5b.HCF.Complex
import Submission.Work.DSM5b.HCF.surj_cohomology
import Submission.Work.DSM5b.HCF.GenSurj
import Submission.Work.DSM5b.HCF.gsurjD_exact_high
import Submission.Work.DSM5b.HCF.HtcAboveAux

namespace Work.DSM5b.HCF

universe u

/-- **The existence of a primitive in a single block.**  For `ℰ = exactlyCoeff 𝒜 k`, a cocycle `z`
of the honest tuple complex in degree `m+1 ≥ k`, and a `k`-element subset `S₀`, the block of `z` at
`S₀` (`Work.DSM5b.HCF.zBlk`, a cochain of the surjection complex on `S₀`) is a coboundary in the
surjection complex on `S₀`.  This is `Work.DSM5b.HCF.gsurjD_exact_high` applied to the block, whose
cocycle condition is `Work.DSM5b.HCF.gsurjD_zBlk_eq_zero`. -/
theorem htcD_exists_block_primitive {R : Type u} [CommRing R] {ι : Type u} [DecidableEq ι]
    (𝒜 : CoeffSys R ι) (k m : ℕ) (hm : k ≤ m + 1)
    (z : (CoeffSys.exactlyCoeff 𝒜 k).Htc (m + 1))
    (hz : (CoeffSys.exactlyCoeff 𝒜 k).htcD (m + 1) z = 0)
    (S₀ : Finset ι) (hS : S₀.card = k) :
    ∃ y : GSurjTerm S₀ ((CoeffSys.exactlyCoeff 𝒜 k).M S₀) m,
      gsurjD (R := R) S₀ ((CoeffSys.exactlyCoeff 𝒜 k).M S₀) m y = zBlk 𝒜 k m z S₀ :=
  gsurjD_exact_high S₀ ((CoeffSys.exactlyCoeff 𝒜 k).M S₀) m (by omega)
    (zBlk 𝒜 k m z S₀) (gsurjD_zBlk_eq_zero 𝒜 k m z hz S₀ hS)

/-- **Exactness of the honest complex of the size-`k` graded piece above its top degree.**
Let `ℰ = Work.DSM5b.CoeffSys.exactlyCoeff 𝒜 k` (the coefficient system supported on the subsets of
size exactly `k`). Then the honest tuple complex `Htc ℰ` with differential
`Work.DSM5b.CoeffSys.htcD` is exact in every degree `m+1 ≥ k`:
`range (htcD m) = ker (htcD (m+1))`.

Route: group the tuples `τ : Fin (m+1) → ι` by `S₀ := tupRng τ`.  For `card S₀ ≠ k` the coefficient
module `ℰ.M S₀` is a subsingleton (for `card S₀ < k` the module is `↥⊥` quotiented, for
`card S₀ > k` it is `⊤ ⧸ ⊤`), so that block of the complex is zero.  For `card S₀ = k` the block
`{τ | tupRng τ = S₀}` is the surjection complex `Work.DSM5b.HCF.GSurjTerm S₀ (ℰ.M S₀)` with
differential `Work.DSM5b.HCF.gsurjD` (a deletion that fixes the range has `ℰ.res` equal to the
identity by `htcAbove_res_eq_cast`; one that changes the range lands in a subsingleton coefficient module,
matching the `else 0` branch of `gsurjD`).  The surjection complex on `S₀` is exact in every degree
`≥ ♯S₀` (`Work.DSM5b.HCF.gsurjD_exact_high`).  Since `m+1 ≥ k`, the relevant degree is never the
top degree `k-1`.  A function into a product is killed by a differential iff each block is, so
exactness is termwise in `S₀`; the assembly of the block primitives into an element of the honest
complex whose differential is `z` is `Work.DSM5b.HCF.htcD_eq_of_block_prims`
(`Submission/Work/DSM5b/HCF/HtcAboveAux.lean`).

The inclusion `range (htcD m) ⊆ ker (htcD (m+1))` is `d² = 0`
(`Work.DSM5b.CoeffSys.htcD_comp`). -/
theorem htcD_exact_above {R : Type u} [CommRing R] {ι : Type u} [DecidableEq ι] [LinearOrder ι]
    (𝒜 : Work.DSM5b.CoeffSys R ι) (k m : ℕ) (hm : k ≤ m + 1) :
    LinearMap.range (Work.DSM5b.CoeffSys.htcD (𝒜 := Work.DSM5b.CoeffSys.exactlyCoeff 𝒜 k) m) =
      LinearMap.ker (Work.DSM5b.CoeffSys.htcD (𝒜 := Work.DSM5b.CoeffSys.exactlyCoeff 𝒜 k) (m + 1)) := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨u, rfl⟩
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, CoeffSys.htcD_comp]
    rfl
  · intro z hz
    rw [LinearMap.mem_ker] at hz
    obtain ⟨w, hw⟩ := htcD_eq_of_block_prims 𝒜 k m hm z hz
      (fun S₀ hS => Classical.choose (htcD_exists_block_primitive 𝒜 k m hm z hz S₀ hS))
      (fun S₀ hS => Classical.choose_spec (htcD_exists_block_primitive 𝒜 k m hm z hz S₀ hS))
    exact LinearMap.mem_range.mpr ⟨w, hw⟩

end Work.DSM5b.HCF
