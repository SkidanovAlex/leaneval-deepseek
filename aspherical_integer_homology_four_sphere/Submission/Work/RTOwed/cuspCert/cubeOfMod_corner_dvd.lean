/-
# The corner of `cubeOfMod v p` is congruent to `p` modulo the cusp lattice

This file proves `Work.RTOwed.cuspCert.cubeOfMod_corner_dvd`: for every cusp `v`, every integer
vector `p : Fin 3 → ℤ` and every coordinate `i`, the lower corner of the cube selected by the
lookup table `Work.Cusp.cubeOfMod v p` is congruent to `p` modulo `latMod v i`:

  `latMod v i ∣ p i - cubeCorner (cubeOfMod v p) i`.

Equivalently: the lower corners `cubeCorner a` of the cubes `a` of cusp `v` are a complete residue
system for `ℤ³ / diag (latMod v)`, and `cubeOfMod` picks the class representative.

## Method

The lookup table `cubeOfMod v p` inspects only the residues `p i % latMod v i` (the table branches
test `p i % 2` and `p i % 4`, and `latMod v i ≤ 4`).  So

* the cube index is invariant under subtracting a lattice vector (`cubeOfMod_add_latMod`, in
  `Submission/Work/RTOwed/cuspCert/lattice_bridge.lean`), which reduces to `p i % latMod v i`;
* after that reduction the residue is a `Fin 4` value, and the resulting claim is a finite check on
  the tables (`decide`);
* the passage back from divisibility of `p i % latMod v i - corner` to divisibility of
  `p i - corner` uses `p i = latMod v i * (p i / latMod v i) + p i % latMod v i`
  (`Int.mul_ediv_add_emod`).
-/
import Mathlib
import Submission.Work.RTOwed.cuspDev
import Submission.Work.RTOwed.cuspCert.lattice_bridge

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

noncomputable section

namespace Work.RTOwed.cuspCert

/-- **The finite check.**  For a residue class `q : Fin 3 → Fin 4` (the residues of `⌊x⌋` modulo
`latMod v`) the corner of its cube is congruent to `q` modulo `latMod v`.  This is a finite
verification on the tables `Work.Cusp.latMod`, `Work.Cusp.cubeOfMod` and `Work.Cusp.cubeCorner`. -/
theorem cubeOfMod_corner_dvd_aux (v : Fin 5) (q : Fin 3 → Fin 4) (i : Fin 3) :
    (Work.Cusp.latMod v i : ℤ) ∣
      ((q i : ℤ) - Work.Cusp.cubeCorner (Work.Cusp.cubeOfMod v (fun j => (q j : ℤ))) i) := by
  revert q i
  fin_cases v <;> decide +kernel

/-- Divisibility of `p - c` follows from divisibility of `p % d - c`, because
`p = d * (p / d) + p % d`. -/
theorem dvd_sub_of_dvd_emod {d p c : ℤ} (h : d ∣ p % d - c) : d ∣ p - c := by
  have hsplit : p - c = d * (p / d) + (p % d - c) := by
    have := Int.mul_ediv_add_emod p d
    linarith
  rw [hsplit]
  exact dvd_add (dvd_mul_right d (p / d)) h

theorem cubeOfMod_corner_dvd (v : Fin 5) (p : Fin 3 → ℤ) (i : Fin 3) :
    (Work.Cusp.latMod v i : ℤ) ∣ (p i - Work.Cusp.cubeCorner (Work.Cusp.cubeOfMod v p) i) := by
  have hb : ∀ i : Fin 3, 0 < (Work.Cusp.latMod v i : ℤ) := by
    intro i; fin_cases v <;> fin_cases i <;> decide +kernel
  have hm : ∀ i : Fin 3, (Work.Cusp.latMod v i : ℤ) ≤ 4 := by
    intro i; fin_cases v <;> fin_cases i <;> decide +kernel
  -- the cube index depends only on the residues of `p` modulo `latMod v`
  have hp : Work.Cusp.cubeOfMod v p
      = Work.Cusp.cubeOfMod v (fun i => p i % (Work.Cusp.latMod v i : ℤ)) := by
    have h : p = (fun i => p i % (Work.Cusp.latMod v i : ℤ)) +
        (fun i => (Work.Cusp.latMod v i : ℤ) * (p i / (Work.Cusp.latMod v i : ℤ))) := by
      funext i
      simp only [Pi.add_apply]
      have h' := Int.mul_ediv_add_emod (p i) (Work.Cusp.latMod v i : ℤ)
      linarith
    conv_lhs => rw [h]
    exact cubeOfMod_add_latMod v _ _
  rw [hp]
  -- view the residues as `Fin 4` values
  obtain ⟨q, hq⟩ : ∃ q : Fin 3 → Fin 4,
      ∀ i : Fin 3, (q i : ℤ) = p i % (Work.Cusp.latMod v i : ℤ) := by
    refine ⟨fun i => ⟨(p i % (Work.Cusp.latMod v i : ℤ)).toNat, ?_⟩, fun i => ?_⟩
    · have h1 : 0 ≤ p i % (Work.Cusp.latMod v i : ℤ) := Int.emod_nonneg _ (ne_of_gt (hb i))
      have h2 : p i % (Work.Cusp.latMod v i : ℤ) < 4 :=
        lt_of_lt_of_le (Int.emod_lt_of_pos _ (hb i)) (hm i)
      have h3 := Int.toNat_of_nonneg h1
      omega
    · exact Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt (hb i)))
  rw [show (fun i => p i % (Work.Cusp.latMod v i : ℤ)) = fun i => (q i : ℤ) from
    funext fun i => (hq i).symm]
  have hfin : (Work.Cusp.latMod v i : ℤ) ∣
      ((q i : ℤ) - Work.Cusp.cubeCorner (Work.Cusp.cubeOfMod v (fun j => (q j : ℤ))) i) :=
    cubeOfMod_corner_dvd_aux v q i
  rw [hq i] at hfin
  exact dvd_sub_of_dvd_emod hfin

end Work.RTOwed.cuspCert
