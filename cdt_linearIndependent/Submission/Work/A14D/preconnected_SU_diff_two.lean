import Mathlib
import Submission.Work.A14D.H_cont

/-!
# `Work.A14D.preconnected_SU_diff_two`

`SU = {z : ℂ | (1 - z.re)/8 < z.im}` is the open half-plane `re z + 8 * im z > 1`
(`Work.A14D.mem_SU_iff`), a convex (hence preconnected) open set containing `2`
(`re 2 = 2`, `im 2 = 0`, and `1 < 8 * 0 + 2`).

Here we show that `SU \ {2}` is still preconnected.  The four sets

* `SU ∩ {z | z.re < 2}`,  * `SU ∩ {z | 0 < z.im}`,
* `SU ∩ {z | 2 < z.re}`,  * `SU ∩ {z | z.im < 0}`

are convex (intersections of the convex half-plane `SU` with the preimages under the `ℝ`-linear
maps `reLm` and `imLm` of the convex sets `Iio 2`, `Ioi 0`, `Ioi 2`, `Iio 0`), hence
preconnected, and none of them contains `2` (whose real part is `2` and imaginary part is `0`).
Their union is exactly `SU \ {2}`: a point `z ∈ SU` with `z.re = 2` satisfies `2 + 8 * z.im > 1`,
i.e. `-1/8 < z.im`, and `z ≠ 2` forces `z.im ≠ 0`.  Finally the pieces are glued pairwise, using
the three explicit points `3/2 + i/10` (in the first two pieces), `3 + i` (in the second and third)
and `3 - i/10` (in the third and fourth).
-/

namespace Work.A14D

open Set Metric Complex
open scoped Topology

theorem preconnected_SU_diff_two : IsPreconnected (SU \ ({2} : Set ℂ)) := by
  -- the four convex pieces
  have hE : IsPreconnected (SU ∩ {z : ℂ | z.re < 2}) :=
    ((convex_SU).inter ((convex_Iio (2 : ℝ)).linear_preimage Complex.reLm)).isPreconnected
  have hU : IsPreconnected (SU ∩ {z : ℂ | (0 : ℝ) < z.im}) :=
    ((convex_SU).inter ((convex_Ioi (0 : ℝ)).linear_preimage Complex.imLm)).isPreconnected
  have hC : IsPreconnected (SU ∩ {z : ℂ | (2 : ℝ) < z.re}) :=
    ((convex_SU).inter ((convex_Ioi (2 : ℝ)).linear_preimage Complex.reLm)).isPreconnected
  have hD : IsPreconnected (SU ∩ {z : ℂ | z.im < 0}) :=
    ((convex_SU).inter ((convex_Iio (0 : ℝ)).linear_preimage Complex.imLm)).isPreconnected
  -- the three gluing points
  have hpE : ((3 / 2 : ℝ) : ℂ) + ((1 / 10 : ℝ) : ℂ) * Complex.I ∈ SU ∩ {z : ℂ | z.re < 2} := by
    refine ⟨?_, ?_⟩
    · rw [mem_SU_iff]; norm_num [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
    · norm_num [Complex.add_re, Complex.mul_re]
  have hpU : ((3 / 2 : ℝ) : ℂ) + ((1 / 10 : ℝ) : ℂ) * Complex.I ∈ SU ∩ {z : ℂ | (0 : ℝ) < z.im} := by
    refine ⟨?_, ?_⟩
    · rw [mem_SU_iff]; norm_num [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
    · norm_num [Complex.add_im, Complex.mul_im]
  have hqU : ((3 : ℂ) + Complex.I) ∈ SU ∩ {z : ℂ | (0 : ℝ) < z.im} := by
    refine ⟨?_, ?_⟩
    · rw [mem_SU_iff]; norm_num [Complex.add_re, Complex.add_im]
    · norm_num
  have hqC : ((3 : ℂ) + Complex.I) ∈ SU ∩ {z : ℂ | (2 : ℝ) < z.re} := by
    refine ⟨?_, ?_⟩
    · rw [mem_SU_iff]; norm_num [Complex.add_re, Complex.add_im]
    · norm_num
  have hrC : ((3 : ℂ) - ((1 / 10 : ℝ) : ℂ) * Complex.I) ∈ SU ∩ {z : ℂ | (2 : ℝ) < z.re} := by
    refine ⟨?_, ?_⟩
    · rw [mem_SU_iff]; norm_num [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
    · norm_num [Complex.sub_re, Complex.mul_re]
  have hrD : ((3 : ℂ) - ((1 / 10 : ℝ) : ℂ) * Complex.I) ∈ SU ∩ {z : ℂ | z.im < 0} := by
    refine ⟨?_, ?_⟩
    · rw [mem_SU_iff]; norm_num [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
    · norm_num [Complex.sub_im, Complex.mul_im]
  -- glue them
  have g1 : IsPreconnected
      ((SU ∩ {z : ℂ | z.re < 2}) ∪ (SU ∩ {z : ℂ | (0 : ℝ) < z.im})) :=
    IsPreconnected.union _ hpE hpU hE hU
  have g2 : IsPreconnected
      (((SU ∩ {z : ℂ | z.re < 2}) ∪ (SU ∩ {z : ℂ | (0 : ℝ) < z.im}))
        ∪ (SU ∩ {z : ℂ | (2 : ℝ) < z.re})) :=
    IsPreconnected.union _ (Or.inr hqU) hqC g1 hC
  have g3 : IsPreconnected
      ((((SU ∩ {z : ℂ | z.re < 2}) ∪ (SU ∩ {z : ℂ | (0 : ℝ) < z.im}))
        ∪ (SU ∩ {z : ℂ | (2 : ℝ) < z.re})) ∪ (SU ∩ {z : ℂ | z.im < 0})) :=
    IsPreconnected.union _ (Or.inr hrC) hrD g2 hD
  -- the union is `SU \ {2}`
  have hset : SU \ ({2} : Set ℂ)
      = (((SU ∩ {z : ℂ | z.re < 2}) ∪ (SU ∩ {z : ℂ | (0 : ℝ) < z.im}))
          ∪ (SU ∩ {z : ℂ | (2 : ℝ) < z.re})) ∪ (SU ∩ {z : ℂ | z.im < 0}) := by
    ext z
    simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_union, Set.mem_ofPred_eq,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨hzSU, hz2⟩
      rcases lt_trichotomy z.re 2 with h | h | h
      · exact Or.inl (Or.inl (Or.inl ⟨hzSU, h⟩))
      · have him : z.im ≠ 0 := by
          intro h0
          refine hz2 ?_
          rw [Complex.ext_iff]
          exact ⟨by simp [h], by simp [h0]⟩
        rcases lt_trichotomy z.im 0 with h' | h' | h'
        · exact Or.inr ⟨hzSU, h'⟩
        · exact absurd h' him
        · exact Or.inl (Or.inl (Or.inr ⟨hzSU, h'⟩))
      · exact Or.inl (Or.inr ⟨hzSU, h⟩)
    · rintro (((⟨hzSU, h⟩ | ⟨hzSU, h⟩) | ⟨hzSU, h⟩) | ⟨hzSU, h⟩)
      · exact ⟨hzSU, by intro hz; rw [hz] at h; norm_num at h⟩
      · exact ⟨hzSU, by intro hz; rw [hz] at h; norm_num at h⟩
      · exact ⟨hzSU, by intro hz; rw [hz] at h; norm_num at h⟩
      · exact ⟨hzSU, by intro hz; rw [hz] at h; norm_num at h⟩
  rw [hset]
  exact g3

end Work.A14D
