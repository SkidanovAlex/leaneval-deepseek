import Mathlib
import Submission.Work.DSM1p.Family
import Submission.Work.DSM1p.Family.flat_closure

/-!
# Divisibility by `p ^ k` descends from the stages of the root tower to the closure

The root closure `FamClosure R p x = colim_n FamTower R p x n` is a filtered colimit of the
stages.  This file proves that the "`p`-power divisibility" statement

  `b ^ p = p ^ (k * p) * c  ⟹  b = p ^ k * w`

— which we assume stagewise (`hstage`) — descends to the closure.  The only ingredient is the
standard description of zero in a filtered direct limit of rings: an element of a stage which
maps to zero in the colimit already maps to zero at some later stage
(`Ring.DirectLimit.of.zero_exact`).

Since `FamClosure` is defined as a filtered colimit indexed by `ℕ`, every element comes from
some stage (`Ring.DirectLimit.exists_of`) and two such descriptions may be compared after
pushing to a common later stage.
-/

namespace Work.DSM1p.Family

theorem closure_dvd_pow (R : Type*) [CommRing R] (p : ℕ) [Fact p.Prime] {d : ℕ} (x : Fin d → R)
    (hinj : ∀ {m n : ℕ} (h : m ≤ n),
      Function.Injective (Work.DSM1p.FamTower.stepMap R p x m n h))
    (hstage : ∀ (n : ℕ) (b : Work.DSM1p.FamTower R p x n) (k : ℕ),
      (∃ c : Work.DSM1p.FamTower R p x n,
        b ^ p = (p : Work.DSM1p.FamTower R p x n) ^ (k * p) * c) →
      ∃ w : Work.DSM1p.FamTower R p x n, b = (p : Work.DSM1p.FamTower R p x n) ^ k * w) :
    ∀ (b : Work.DSM1p.FamClosure R p x) (k : ℕ),
      (∃ c : Work.DSM1p.FamClosure R p x,
        b ^ p = (p : Work.DSM1p.FamClosure R p x) ^ (k * p) * c) →
      ∃ w : Work.DSM1p.FamClosure R p x, b = (p : Work.DSM1p.FamClosure R p x) ^ k * w := by
  intro b k hb
  obtain ⟨c, hc⟩ := hb
  -- lift `b` and `c` to a common stage `N`
  obtain ⟨n₁, b₁, hb₁⟩ := Ring.DirectLimit.exists_of b
  obtain ⟨n₂, c₁, hc₁⟩ := Ring.DirectLimit.exists_of c
  let N : ℕ := max n₁ n₂
  have h1 : n₁ ≤ N := le_max_left n₁ n₂
  have h2 : n₂ ≤ N := le_max_right n₁ n₂
  let bN : Work.DSM1p.FamTower R p x N := Work.DSM1p.FamTower.stepMap R p x n₁ N h1 b₁
  let cN : Work.DSM1p.FamTower R p x N := Work.DSM1p.FamTower.stepMap R p x n₂ N h2 c₁
  have hofbN : Work.DSM1p.FamClosure.of R p x N bN = b := by
    rw [Ring.DirectLimit.of_f h1 b₁, hb₁]
  have hofcN : Work.DSM1p.FamClosure.of R p x N cN = c := by
    rw [Ring.DirectLimit.of_f h2 c₁, hc₁]
  -- the relation, seen in the stage `N`
  have hzero : Work.DSM1p.FamClosure.of R p x N
      (bN ^ p - (p : Work.DSM1p.FamTower R p x N) ^ (k * p) * cN) = 0 := by
    rw [map_sub, map_mul, map_pow, map_pow, map_natCast, hofbN, hofcN, sub_eq_zero]
    exact hc
  -- a stage element whose class is zero in the colimit already vanishes in a later stage
  obtain ⟨j, hij, hj⟩ := Ring.DirectLimit.of.zero_exact
    (G := Work.DSM1p.FamTower R p x) (f' := Work.DSM1p.FamTower.stepMap R p x) hzero
  have hrel : (Work.DSM1p.FamTower.stepMap R p x N j hij bN) ^ p =
      (p : Work.DSM1p.FamTower R p x j) ^ (k * p) *
        Work.DSM1p.FamTower.stepMap R p x N j hij cN := by
    have h := hj
    rw [map_sub, map_mul, map_pow, map_pow, map_natCast] at h
    exact sub_eq_zero.mp h
  -- the stage hypothesis at the later stage `j`
  obtain ⟨wj, hwj⟩ := hstage j (Work.DSM1p.FamTower.stepMap R p x N j hij bN) k
    ⟨Work.DSM1p.FamTower.stepMap R p x N j hij cN, hrel⟩
  refine ⟨Work.DSM1p.FamClosure.of R p x j wj, ?_⟩
  calc b = Work.DSM1p.FamClosure.of R p x N bN := hofbN.symm
    _ = Work.DSM1p.FamClosure.of R p x j (Work.DSM1p.FamTower.stepMap R p x N j hij bN) :=
        (Ring.DirectLimit.of_f hij bN).symm
    _ = Work.DSM1p.FamClosure.of R p x j
          ((p : Work.DSM1p.FamTower R p x j) ^ k * wj) := by rw [hwj]
    _ = (p : Work.DSM1p.FamClosure R p x) ^ k * Work.DSM1p.FamClosure.of R p x j wj := by
        rw [map_mul, map_pow, map_natCast]

end Work.DSM1p.Family
