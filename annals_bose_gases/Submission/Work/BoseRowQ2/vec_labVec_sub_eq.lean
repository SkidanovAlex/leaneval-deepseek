import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Int.Star
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.BoseRowQ2.maskTailDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowQ2.vec_labVec_sub_eq`: `vec` is additive on the non-wrapping lattice window

The lattice label group is `Lab N = (ZMod (2N+1))^3` and `labVec N n = ((n i).valMinAbs)_i`
is the *centred* integer representative of each residue; `Work.BoseB4.vec m = (2π m_i)_i` is the
dual-lattice momentum.

`labVec` is not additive: the centred representative of `n' - n` is the difference of the centred
representatives only as long as no wrap-around occurs, i.e. as long as both momenta stay inside
the "half-cube" `‖2π m‖ ≤ π N`.  That is exactly the hypothesis set of the statement
(`‖vec (labVec N s)‖ ≤ L`, `‖vec (labVec N s')‖ ≤ L`, `L / π ≤ N`), and the proof is the
uniqueness of the centred representative: both `(s' i - s i).valMinAbs` and
`(s' i).valMinAbs - (s i).valMinAbs` lie in the canonical window `[-N, N]` of `ZMod (2N+1)` and
are congruent modulo `2N+1`, hence equal (`ZMod.valMinAbs_spec`).

This is the lattice-additivity brick used by the sharp mask row (`Mc i j = χ̂²(vec (K i - K j))`:
the entries are computed from the *difference* label). -/

noncomputable section

namespace Work.BoseRowQ2

/-- The components of `Work.BoseB4.vec`: `vec m i = 2π m i`. -/
private lemma vec_component (v : Fin 3 → ℤ) (i : Fin 3) :
    (Work.BoseB4.vec v) i = 2 * Real.pi * (v i : ℝ) := by
  simp [Work.BoseB4.vec]

/-- **The non-wrapping window.**  If the momentum of `u ∈ Lab N` has norm at most `L` and
`L / π ≤ N`, then every centred coordinate of `u` satisfies `|2 * valMinAbs| ≤ N`, i.e.
`2 * (u i).valMinAbs` lies in the canonical window `[-N, N]` of `ZMod (2N+1)`. -/
private lemma two_valMinAbs_mem {N : ℕ} {L : ℝ} {u : Work.BoseBoxFock.Lab N} (i : Fin 3)
    (hu : ‖Work.BoseB4.vec (Work.BoseBoxFock.labVec N u)‖ ≤ L)
    (hN : L / Real.pi ≤ (N : ℝ)) :
    -((N : ℤ)) ≤ 2 * (u i).valMinAbs ∧ 2 * (u i).valMinAbs ≤ (N : ℤ) := by
  have h1 : ‖(Work.BoseB4.vec (Work.BoseBoxFock.labVec N u)) i‖ ≤ L :=
    le_trans (PiLp.norm_apply_le (Work.BoseB4.vec (Work.BoseBoxFock.labVec N u)) i) hu
  rw [vec_component, Real.norm_eq_abs, abs_mul,
    abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)] at h1
  simp only [Work.BoseBoxFock.labVec] at h1
  have h2 : 2 * |((u i).valMinAbs : ℝ)| ≤ L / Real.pi := by
    rw [le_div_iff₀ Real.pi_pos]
    nlinarith [h1]
  have hm : |((u i).valMinAbs : ℝ)| ≤ (N : ℝ) / 2 := by
    have := le_trans h2 hN; linarith
  constructor
  · have h : -(((N : ℤ) : ℝ)) ≤ ((2 * (u i).valMinAbs : ℤ) : ℝ) := by
      push_cast
      linarith [neg_abs_le ((u i).valMinAbs : ℝ)]
    exact_mod_cast h
  · have h : ((2 * (u i).valMinAbs : ℤ) : ℝ) ≤ ((N : ℤ) : ℝ) := by
      push_cast
      linarith [le_abs_self ((u i).valMinAbs : ℝ)]
    exact_mod_cast h

/-- **Uniqueness of the centred representative.**  If the doubled centred representatives of
`a b : ZMod (2N+1)` both lie in the window `[-N, N]`, then the centred representative of the
difference is the difference of the centred representatives. -/
private lemma valMinAbs_sub_eq {N : ℕ} (a b : ZMod (2 * N + 1))
    (ha1 : -((N : ℤ)) ≤ 2 * a.valMinAbs) (ha2 : 2 * a.valMinAbs ≤ (N : ℤ))
    (hb1 : -((N : ℤ)) ≤ 2 * b.valMinAbs) (hb2 : 2 * b.valMinAbs ≤ (N : ℤ)) :
    (a - b).valMinAbs = a.valMinAbs - b.valMinAbs := by
  have : NeZero (2 * N + 1) := ⟨by omega⟩
  refine (ZMod.valMinAbs_spec (a - b) (a.valMinAbs - b.valMinAbs)).2 ⟨?_, ?_, ?_⟩
  · rw [Int.cast_sub, ZMod.coe_valMinAbs, ZMod.coe_valMinAbs]
  · push_cast; linarith
  · push_cast; linarith

theorem vec_labVec_sub_eq {N : ℕ} {s s' : Work.BoseBoxFock.Lab N} {L : ℝ} (hL : 0 ≤ L)
    (hs : ‖Work.BoseB4.vec (Work.BoseBoxFock.labVec N s)‖ ≤ L)
    (hs' : ‖Work.BoseB4.vec (Work.BoseBoxFock.labVec N s')‖ ≤ L)
    (hN : L / Real.pi ≤ (N : ℝ)) :
    Work.BoseB4.vec (Work.BoseBoxFock.labVec N (s' - s))
      = Work.BoseB4.vec (Work.BoseBoxFock.labVec N s') - Work.BoseB4.vec (Work.BoseBoxFock.labVec N s) := by
  rw [Work.BoseB4.vec, Work.BoseB4.vec, Work.BoseB4.vec, ← WithLp.toLp_sub]
  congr 1
  funext i
  simp only [Work.BoseBoxFock.labVec, Pi.sub_apply]
  rw [valMinAbs_sub_eq (s' i) (s i) (two_valMinAbs_mem i hs' hN).1 (two_valMinAbs_mem i hs' hN).2
    (two_valMinAbs_mem i hs hN).1 (two_valMinAbs_mem i hs hN).2]
  push_cast
  ring

end Work.BoseRowQ2
