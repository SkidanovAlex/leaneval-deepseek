import Mathlib
import Submission.Work.RatHurewicz.LensSpace.Basic

set_option synthInstance.maxHeartbeats 400000

/-!
# Uniform separation of the `ZMod n`-orbit on the lens sphere

The free action of `μₙ = ZMod n` on the unit sphere `S^{2N+3} ⊆ ℂ^{N+2}` (scalar multiplication by
the character `φ : ZMod n →* ℂˣ`) is `1`-Lipschitz-invertible, and for `k ≠ 1` every point `x`
satisfies `dist (k • x) x = ‖φ k - 1‖`, a quantity that depends on `n` and `k` but **not** on the
dimension `N` and **not** on `x`.  Since the value set is finite and consists of strictly positive
numbers, it has a positive minimum `δ`; this is the uniform separation used to build the lens space
range models.

The main statement `Work.EMFG.lensSeparation` is the resulting uniform lower bound.
-/

open scoped Topology

namespace Work.EMFG

noncomputable section

/-- **The orbit distance is a character value.**  For any `N`, any `k : Multiplicative (ZMod n)`
and any `x` on the lens sphere, `dist (k • x) x` equals `‖φ k - 1‖`, computed in `ℂ`. -/
theorem dist_smul_lens (n N : ℕ) [NeZero n] (k : Multiplicative (ZMod n))
    (x : Work.RatHurewicz.lensTotal N) :
    dist (k • x) x = ‖(Work.RatHurewicz.phi n (NeZero.ne n) k : ℂ) - 1‖ := by
  rw [Subtype.dist_eq]
  show dist (Work.RatHurewicz.lensAct n N k x.1) x.1 = _
  rw [Work.RatHurewicz.lensAct]
  set y : EuclideanSpace ℂ (Fin (N + 2)) := (Work.RatHurewicz.cIso N).symm x.1 with hy
  have hx : Work.RatHurewicz.cIso N y = x.1 := by
    rw [hy]; exact (Work.RatHurewicz.cIso N).apply_symm_apply x.1
  rw [← hx, (Work.RatHurewicz.cIso N).dist_map, dist_eq_norm]
  have hsub : (Work.RatHurewicz.phi n (NeZero.ne n) k : ℂ) • y - y
      = ((Work.RatHurewicz.phi n (NeZero.ne n) k : ℂ) - 1) • y := by
    rw [sub_smul, one_smul]
  rw [hsub, norm_smul]
  have hy1 : ‖y‖ = 1 := by
    rw [hy, (Work.RatHurewicz.cIso N).symm.norm_map,
      Work.RatHurewicz.norm_eq_one_of_mem_lensTotal x]
  rw [hy1, mul_one]

/-- **Uniform separation of the free `ZMod n`-action on `S^{2N+3}`.**  There is a positive
`δ`, depending only on `n`, with `dist (k • x) x ≥ δ` for every `k ≠ 1`, every dimension `N` and
every point `x` of the lens sphere. -/
theorem lensSeparation (n : ℕ) [NeZero n] :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (N : ℕ) (k : Multiplicative (ZMod n)), k ≠ 1 →
      ∀ x : Work.RatHurewicz.lensTotal N, δ ≤ dist (k • x) x := by
  classical
  -- The finite set of the characters' distances from `1`; empty exactly when `n = 1`.
  set T : Finset ℝ :=
    ((Finset.univ : Finset (Multiplicative (ZMod n))).filter (fun k => k ≠ 1)).image
      (fun k => ‖(Work.RatHurewicz.phi n (NeZero.ne n) k : ℂ) - 1‖) with hT
  refine ⟨if h : T.Nonempty then T.min' h else 1, ?_, ?_⟩
  · -- positivity: either the empty case (`δ = 1`) or the minimum of a set of positive numbers
    split_ifs with h
    · obtain ⟨a, ha, ha'⟩ := Finset.mem_image.mp (Finset.min'_mem T h)
      rw [← ha', norm_pos_iff]
      intro hzero
      have ha1 : a ≠ 1 := (Finset.mem_filter.mp ha).2
      apply ha1
      apply Work.RatHurewicz.phi_injective n (NeZero.ne n)
      simpa using sub_eq_zero.mp hzero
    · norm_num
  · -- the bound: `dist` is one of the finitely many values whose minimum is `δ`
    intro N k hk x
    have hk' : ‖(Work.RatHurewicz.phi n (NeZero.ne n) k : ℂ) - 1‖ ∈ T := by
      rw [hT]
      exact Finset.mem_image.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩, rfl⟩
    have hne : T.Nonempty := ⟨_, hk'⟩
    rw [dif_pos hne, dist_smul_lens]
    exact Finset.min'_le T _ hk'

end

end Work.EMFG
