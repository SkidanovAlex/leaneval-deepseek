import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Sig2.GamTwoDefs
import Submission.Work.HP.detgam_span_coords_detL
import Submission.Work.HP.detgam_span_pair_wedgeNorm
import Submission.Work.HP.detgam_gcdMinors2_basis_prim
import Submission.Work.HP.Lat.gcdMinors2_linear
import Submission.Work.HP.Lat.detL_basis_gram
import Submission.Work.HP.MinkDefs

/-!
# `dmin 2 {c,d} ≤ wedgeNorm c d / gcdMinors2 c d`

For `ℤ`-linearly independent `c, d ∈ ℤ^ι` the least determinant `dmin 2 {c,d}` of a rank-`2`
sublattice of `ℤ^ι` containing both `c` and `d` is at most the covolume `wedgeNorm c d` of
`ℤc ⊕ ℤd` divided by the gcd `gcdMinors2 c d` of the `2 × 2` minors, and `gcdMinors2 c d` is
positive.

The admissible lattice exhibited is the saturation `K = satSpan {c,d} = span_ℝ{toR c,toR d} ∩ ℤ^ι`.
Its rank is two, it contains `c` and `d`, and its determinant is `wedgeNorm c d / gcdMinors2 c d`:

* `detgam_span_coords_detL` writes `detL (span ℤ {c,d}) = |det T| · detL K`, where `T` is the
  coordinate matrix of `c, d` in any `ℤ`-basis `b` of `K`;
* `detgam_span_pair_wedgeNorm` identifies `detL (span ℤ {c,d}) = wedgeNorm c d`;
* `gcdMinors2` of a basis of the saturated lattice `K` is `1` (`detgam_gcdMinors2_basis_prim`), so
  multiplicativity of `gcdMinors2` under the change of coordinates expressing `c, d` in the basis
  `b` gives `gcdMinors2 c d = |det T|`.

Combining, `wedgeNorm c d = gcdMinors2 c d · detL K`.
-/

set_option autoImplicit false
noncomputable section

namespace Work.HP.Sig2

open Work.HP

theorem DminPairLe {ι : Type*} [Fintype ι] [DecidableEq ι] (c d : ι → ℤ)
    (h : LinearIndependent ℤ ![c, d]) :
    dmin 2 ({c, d} : Set (ι → ℤ)) ≤ wedgeNorm c d / (gcdMinors2 c d : ℝ)
      ∧ 0 < gcdMinors2 c d := by
  classical
  -- The saturation of the span of `c` and `d`: an admissible rank-two lattice.
  let K : Submodule ℤ (ι → ℤ) := satSpan ({c, d} : Set (ι → ℤ))
  have hKdef : K = satSpan ({c, d} : Set (ι → ℤ)) := rfl
  -- `K` is saturated, hence primitive.
  have hKprim : IsPrimLat K := fun v m hm hmv => isSat_satSpan _ v ⟨m, hm, hmv⟩
  have hc : c ∈ K := by
    rw [hKdef, mem_satSpan, span_intCast_pair]
    exact Submodule.subset_span (by simp)
  have hd : d ∈ K := by
    rw [hKdef, mem_satSpan, span_intCast_pair]
    exact Submodule.subset_span (by simp)
  -- The rank of `K` is two.
  have hKspan : Submodule.span ℝ (intCastPi '' (K : Set (ι → ℤ)))
      = Submodule.span ℝ ({toR c, toR d} : Set (ι → ℝ)) := by
    rw [hKdef, span_intCast_satSpan, span_intCast_pair]
    simp only [toR_eq_intCastPi]
  have hliR : LinearIndependent ℝ ![toR c, toR d] := by
    have h1 := Vero.linInd_intCastPi h
    have hfun : (fun j : Fin 2 => intCastPi (![c, d] j)) = ![toR c, toR d] := by
      funext j
      fin_cases j <;> rfl
    rwa [hfun] at h1
  have hfin2 : Module.finrank ℝ (Submodule.span ℝ ({toR c, toR d} : Set (ι → ℝ))) = 2 := by
    have hrange : (Set.range ![toR c, toR d]) = ({toR c, toR d} : Set (ι → ℝ)) := by
      ext z
      simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨j, rfl⟩
        fin_cases j <;> simp
      · rintro (rfl | rfl)
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
    rw [← hrange, finrank_span_eq_card hliR]
    simp
  have hrk : rk K = 2 := by
    rw [rk, ← Vero.finrank_span_image_intCastPi K, hKspan, hfin2]
  -- A `ℤ`-basis of `K` indexed by `Fin 2`.
  obtain ⟨n, bn⟩ := Submodule.basisOfPid (Pi.basisFun ℤ ι) K
  have hn : n = 2 := by
    have h1 : Module.finrank ℤ K = n := by
      rw [Module.finrank_eq_card_basis bn]
      simp
    rw [← h1]
    simpa [rk] using hrk
  let b : Module.Basis (Fin 2) ℤ K := bn.reindex (finCongr hn)
  -- The gcd of the `2 × 2` minors of a basis of a saturated rank-two lattice is `1`.
  have hg : gcdMinors2 (b 0 : ι → ℤ) (b 1 : ι → ℤ) = 1 :=
    detgam_gcdMinors2_basis_prim K hKprim b
  -- Expansion of `c` and `d` in the basis `b`.
  have hc_exp : (b.repr ⟨c, hc⟩) 0 • (b 0 : ι → ℤ)
      + (b.repr ⟨c, hc⟩) 1 • (b 1 : ι → ℤ) = c := by
    have hh := congrArg (fun w : K => (w : ι → ℤ)) (Module.Basis.sum_repr b ⟨c, hc⟩)
    rw [Fin.sum_univ_two] at hh
    simpa using hh
  have hd_exp : (b.repr ⟨d, hd⟩) 0 • (b 0 : ι → ℤ)
      + (b.repr ⟨d, hd⟩) 1 • (b 1 : ι → ℤ) = d := by
    have hh := congrArg (fun w : K => (w : ι → ℤ)) (Module.Basis.sum_repr b ⟨d, hd⟩)
    rw [Fin.sum_univ_two] at hh
    simpa using hh
  -- `gcdMinors2 c d` is the absolute value of the determinant of the coordinate matrix.
  have hlin := Work.HP.Lat.gcdMinors2_linear (b 0 : ι → ℤ) (b 1 : ι → ℤ)
    ((b.repr ⟨c, hc⟩) 0) ((b.repr ⟨c, hc⟩) 1) ((b.repr ⟨d, hd⟩) 0) ((b.repr ⟨d, hd⟩) 1)
  have hgcd : gcdMinors2 c d = ↑(((b.repr ⟨c, hc⟩) 0 * (b.repr ⟨d, hd⟩) 1
      - (b.repr ⟨c, hc⟩) 1 * (b.repr ⟨d, hd⟩) 0).natAbs) := by
    rw [hc_exp, hd_exp, hg, mul_one] at hlin
    exact hlin
  have habs : (((|(b.repr ⟨c, hc⟩) 0 * (b.repr ⟨d, hd⟩) 1
      - (b.repr ⟨c, hc⟩) 1 * (b.repr ⟨d, hd⟩) 0| : ℤ)) : ℝ) = (gcdMinors2 c d : ℝ) := by
    rw [hgcd, Int.abs_eq_natAbs]
  -- Determinant of `K` via the covolume-scaling formula.
  have hspan : detL (Submodule.span ℤ ({c, d} : Set (ι → ℤ))) = wedgeNorm c d :=
    detgam_span_pair_wedgeNorm c d h
  have hcoord : detL (Submodule.span ℤ ({c, d} : Set (ι → ℤ)))
      = (((|(b.repr ⟨c, hc⟩) 0 * (b.repr ⟨d, hd⟩) 1
          - (b.repr ⟨c, hc⟩) 1 * (b.repr ⟨d, hd⟩) 0| : ℤ)) : ℝ) * detL K :=
    detgam_span_coords_detL K b c d hc hd h
  have hwedge : wedgeNorm c d = (gcdMinors2 c d : ℝ) * detL K := by
    rw [← hspan, hcoord, habs]
  -- Positivity of `gcdMinors2 c d`.
  have hposint : 0 < gcdMinors2 c d := by
    have hnn : 0 ≤ gcdMinors2 c d := by
      rw [gcdMinors2]
      exact int_finset_gcd_nonneg' _ _
    rcases lt_or_eq_of_le hnn with hlt | heq
    · exact hlt
    · exfalso
      have hcne : c ≠ 0 := by
        have hne := LinearIndependent.ne_zero (0 : Fin 2) h
        simpa using hne
      obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hcne
      have heq' : Finset.univ.gcd (fun ij : ι × ι => c ij.1 * d ij.2 - c ij.2 * d ij.1) = 0 := by
        rw [gcdMinors2] at heq
        exact heq.symm
      have hmin : ∀ j, c i0 * d j - c j * d i0 = 0 := fun j =>
        Finset.gcd_eq_zero_iff.mp heq' (i0, j) (Finset.mem_univ _)
      have hdep : (-(d i0)) • c + (c i0) • d = 0 := by
        funext j
        have hj := hmin j
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        rw [show (-(d i0)) * c j + c i0 * d j = c i0 * d j - c j * d i0 by ring, hj]
      have hc0 : c i0 = 0 := (LinearIndependent.eq_zero_of_pair h hdep).2
      exact hi0 hc0
  have hgpos : (0 : ℝ) < (gcdMinors2 c d : ℝ) := by exact_mod_cast hposint
  have hdetK : detL K = wedgeNorm c d / (gcdMinors2 c d : ℝ) := by
    rw [hwedge, mul_comm (gcdMinors2 c d : ℝ)]
    rw [mul_div_cancel_right₀ _ (ne_of_gt hgpos)]
  -- `K` is admissible for `dmin 2 {c,d}`, so the `sInf` is at most its determinant.
  have hsub : ({c, d} : Set (ι → ℤ)) ⊆ K := by
    intro z hz
    rcases hz with rfl | rfl
    · exact hc
    · exact hd
  have hbdd : BddBelow {D : ℝ | ∃ L : Submodule ℤ (ι → ℤ),
      rk L = 2 ∧ ({c, d} : Set (ι → ℤ)) ⊆ L ∧ detL L = D} :=
    ⟨0, fun D hD => by obtain ⟨L, _, _, rfl⟩ := hD; exact detL_nonneg L⟩
  refine ⟨?_, hposint⟩
  unfold dmin
  exact csInf_le hbdd ⟨K, hrk, hsub, hdetK⟩

end Work.HP.Sig2
