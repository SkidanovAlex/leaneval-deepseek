import Mathlib
import Submission.Work.HP.kwin_spec
import Submission.Work.HP.FM.schmidt_bound
import Submission.Work.HP.PairsAux
import Submission.Work.HP.lam_basic
import Submission.Work.HP.Q44Child.ballCount_le

/-!
# Per-lattice ball count in a dyadic window (`Work.HP.Q44Main.latS_perlat_branch`)

For a rank-`3` integral lattice `L ⊆ ℤ^5` and `Z ≥ 1`, the number of lattice points of `L`
of Euclidean norm at most `Z` is controlled by the first three successive minima

`λᵢ = lam L i`,  `2^{kwin 3 L (i-1)} = 2^{⌈log₂ λᵢ⌉}` (`λᵢ ≤ 2^{kwin} ≤ 2λᵢ`).

There are two branches, depending on whether the third dyadic window still meets `[1, Z]`:

* if `2^{kwin 3 L 2} ≤ 2 Z` (so `λ₃ ≲ Z`) the count is `≪ Z³ / (∏ᵢ 2^{kwin 3 L (i-1)})`;
* if `2 Z < 2^{kwin 3 L 2}` (so `λ₃ > Z`) the count is `≪ Z² / (2^{kwin} 2^{kwin})`.

Both follow from the explicit lattice-point bound
`#(L ∩ B_Z) ≤ 27 ∏ᵢ (1 + Z/λᵢ)` (`Work.HP.Q44Child.ballCount_le`) together with the elementary
real inequality `1 + Z/λᵢ ≤ 4 Z / 2^{kwin 3 L (i-1)}` (which uses `λᵢ ≥ Aᵢ/2` and, in the
first branch, `A₃ ≤ 2Z`, resp. in the second branch `λ₃ > Z`).
-/

namespace Work.HP.Q44Main

/-- Elementary arithmetic bound, first branch.  If `1 ≤ Z`, the `λᵢ` are positive with
`λ₁, λ₂ ≤ Z` and the dyadic windows `Aᵢ` satisfy `Aᵢ ≤ 2λᵢ`, and if `A₂ ≤ 2Z`, then
`∏ᵢ (1 + Z/λᵢ) ≤ 64 Z³ / (A₀ A₁ A₂)`. -/
private lemma perlat_case1_arith (Z l1 l2 l3 A0 A1 A2 : ℝ)
    (hZ : 1 ≤ Z) (hl1 : 0 < l1) (hl2 : 0 < l2) (hl3 : 0 < l3)
    (hA0 : 0 < A0) (hA1 : 0 < A1) (hA2 : 0 < A2)
    (hz1 : l1 ≤ Z) (hz2 : l2 ≤ Z)
    (hm1 : A0 ≤ 2 * l1) (hm2 : A1 ≤ 2 * l2) (hm3 : A2 ≤ 2 * l3)
    (hc : A2 ≤ 2 * Z) :
    (1 + Z / l1) * (1 + Z / l2) * (1 + Z / l3) ≤ 64 * Z ^ 3 / (A0 * A1 * A2) := by
  have hZ0 : (0:ℝ) < Z := by linarith
  have hf1 : 1 + Z / l1 ≤ 4 * Z / A0 := by
    have hle1 : 1 ≤ Z / l1 := by rw [le_div_iff₀ hl1]; linarith
    have hhalf : A0 / 2 ≤ l1 := by linarith
    have h2 : Z / l1 ≤ Z / (A0 / 2) :=
      div_le_div_of_nonneg_left (le_of_lt hZ0) (by linarith) hhalf
    have h3 : 4 * Z / A0 = 2 * (Z / (A0 / 2)) := by field_simp; ring
    linarith
  have hf2 : 1 + Z / l2 ≤ 4 * Z / A1 := by
    have hle1 : 1 ≤ Z / l2 := by rw [le_div_iff₀ hl2]; linarith
    have hhalf : A1 / 2 ≤ l2 := by linarith
    have h2 : Z / l2 ≤ Z / (A1 / 2) :=
      div_le_div_of_nonneg_left (le_of_lt hZ0) (by linarith) hhalf
    have h3 : 4 * Z / A1 = 2 * (Z / (A1 / 2)) := by field_simp; ring
    linarith
  have hf3 : 1 + Z / l3 ≤ 4 * Z / A2 := by
    have hle1 : 1 ≤ Z / (A2 / 2) := by rw [le_div_iff₀ (by linarith)]; linarith
    have hhalf : A2 / 2 ≤ l3 := by linarith
    have h2 : Z / l3 ≤ Z / (A2 / 2) :=
      div_le_div_of_nonneg_left (le_of_lt hZ0) (by linarith) hhalf
    have h3 : 4 * Z / A2 = 2 * (Z / (A2 / 2)) := by field_simp; ring
    linarith
  have hp2 : (0:ℝ) ≤ 1 + Z / l2 := by positivity
  have hA0pos : (0:ℝ) ≤ 4 * Z / A0 := by positivity
  have hprod1 : (1 + Z / l1) * (1 + Z / l2) ≤ (4 * Z / A0) * (4 * Z / A1) :=
    mul_le_mul hf1 hf2 hp2 hA0pos
  have hm : (1 + Z / l1) * (1 + Z / l2) * (1 + Z / l3) ≤
      (4 * Z / A0) * (4 * Z / A1) * (4 * Z / A2) := by
    have hp : (0:ℝ) ≤ (4 * Z / A0) * (4 * Z / A1) := by positivity
    have hp3 : (0:ℝ) ≤ 1 + Z / l3 := by positivity
    have := mul_le_mul hprod1 hf3 hp3 hp
    simpa using this
  have heq : (4 * Z / A0) * (4 * Z / A1) * (4 * Z / A2) = 64 * Z ^ 3 / (A0 * A1 * A2) := by
    field_simp; ring
  linarith

/-- Elementary arithmetic bound, second branch.  If `1 ≤ Z`, the `λᵢ` are positive with
`λ₁, λ₂ ≤ Z`, the dyadic windows satisfy `Aᵢ ≤ 2λᵢ`, and if `2Z < A₂` (so `λ₃ > Z`), then
`∏ᵢ (1 + Z/λᵢ) ≤ 32 Z² / (A₀ A₁)`. -/
private lemma perlat_case2_arith (Z l1 l2 l3 A0 A1 A2 : ℝ)
    (hZ : 1 ≤ Z) (hl1 : 0 < l1) (hl2 : 0 < l2) (hl3 : 0 < l3)
    (hA0 : 0 < A0) (hA1 : 0 < A1)
    (hz1 : l1 ≤ Z) (hz2 : l2 ≤ Z)
    (hm1 : A0 ≤ 2 * l1) (hm2 : A1 ≤ 2 * l2) (hm3 : A2 ≤ 2 * l3)
    (hc : 2 * Z < A2) :
    (1 + Z / l1) * (1 + Z / l2) * (1 + Z / l3) ≤ 32 * Z ^ 2 / (A0 * A1) := by
  have hZ0 : (0:ℝ) < Z := by linarith
  have hf1 : 1 + Z / l1 ≤ 4 * Z / A0 := by
    have hle1 : 1 ≤ Z / l1 := by rw [le_div_iff₀ hl1]; linarith
    have hhalf : A0 / 2 ≤ l1 := by linarith
    have h2 : Z / l1 ≤ Z / (A0 / 2) :=
      div_le_div_of_nonneg_left (le_of_lt hZ0) (by linarith) hhalf
    have h3 : 4 * Z / A0 = 2 * (Z / (A0 / 2)) := by field_simp; ring
    linarith
  have hf2 : 1 + Z / l2 ≤ 4 * Z / A1 := by
    have hle1 : 1 ≤ Z / l2 := by rw [le_div_iff₀ hl2]; linarith
    have hhalf : A1 / 2 ≤ l2 := by linarith
    have h2 : Z / l2 ≤ Z / (A1 / 2) :=
      div_le_div_of_nonneg_left (le_of_lt hZ0) (by linarith) hhalf
    have h3 : 4 * Z / A1 = 2 * (Z / (A1 / 2)) := by field_simp; ring
    linarith
  have hf3 : 1 + Z / l3 ≤ (2:ℝ) := by
    have hlt : Z / l3 < 1 := by rw [div_lt_iff₀ hl3]; linarith
    linarith
  have hp2 : (0:ℝ) ≤ 1 + Z / l2 := by positivity
  have hA0pos : (0:ℝ) ≤ 4 * Z / A0 := by positivity
  have hprod1 : (1 + Z / l1) * (1 + Z / l2) ≤ (4 * Z / A0) * (4 * Z / A1) :=
    mul_le_mul hf1 hf2 hp2 hA0pos
  have hm : (1 + Z / l1) * (1 + Z / l2) * (1 + Z / l3) ≤
      (4 * Z / A0) * (4 * Z / A1) * 2 := by
    have hp : (0:ℝ) ≤ (4 * Z / A0) * (4 * Z / A1) := by positivity
    have hp3 : (0:ℝ) ≤ 1 + Z / l3 := by positivity
    have := mul_le_mul hprod1 hf3 hp3 hp
    simpa using this
  have heq : (4 * Z / A0) * (4 * Z / A1) * 2 = 32 * Z ^ 2 / (A0 * A1) := by
    field_simp; ring
  linarith

theorem latS_perlat_branch :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : Submodule ℤ (Fin 5 → ℤ)), rk L = 3 → ∀ (Z : ℝ), 1 ≤ Z →
      lam L 1 ≤ Z → lam L 2 ≤ Z →
      ((2 : ℝ) ^ (kwin 3 L 2) ≤ 2 * Z →
        (ballCount L Z : ℝ) ≤ C * Z ^ 3 /
          ((2 : ℝ) ^ (kwin 3 L 0) * (2 : ℝ) ^ (kwin 3 L 1) * (2 : ℝ) ^ (kwin 3 L 2)))
      ∧ (2 * Z < (2 : ℝ) ^ (kwin 3 L 2) →
        (ballCount L Z : ℝ) ≤ C * Z ^ 2 /
          ((2 : ℝ) ^ (kwin 3 L 0) * (2 : ℝ) ^ (kwin 3 L 1))) := by
  refine ⟨1728, by norm_num, ?_⟩
  intro L hrk Z hZ h1 h2
  have hZ0 : (0:ℝ) ≤ Z := by linarith
  have hspec := kwin_spec (Fin 5) 3 L (by norm_num) hrk
  obtain ⟨hkle, hkge, -, -⟩ := hspec
  have hl1pos : 0 < lam L 1 := lam_pos L (by norm_num) (by omega)
  have hl2pos : 0 < lam L 2 := lam_pos L (by norm_num) (by omega)
  have hl3pos : 0 < lam L 3 := lam_pos L (by norm_num) (by omega)
  have hA0pos : 0 < (2:ℝ) ^ (kwin 3 L 0) := by positivity
  have hA1pos : 0 < (2:ℝ) ^ (kwin 3 L 1) := by positivity
  have hA2pos : 0 < (2:ℝ) ^ (kwin 3 L 2) := by positivity
  have hm1 : (2:ℝ) ^ (kwin 3 L 0) ≤ 2 * lam L 1 := hkge (0 : Fin 3)
  have hm2 : (2:ℝ) ^ (kwin 3 L 1) ≤ 2 * lam L 2 := hkge (1 : Fin 3)
  have hm3 : (2:ℝ) ^ (kwin 3 L 2) ≤ 2 * lam L 3 := hkge (2 : Fin 3)
  have hbc := Work.HP.Q44Child.ballCount_le L hrk Z hZ0
  constructor
  · intro hc1
    have hprod : (∏ j : Fin 3, (1 + Z / lam L (j.val + 1))) ≤
        64 * Z ^ 3 / ((2:ℝ)^(kwin 3 L 0) * (2:ℝ)^(kwin 3 L 1) * (2:ℝ)^(kwin 3 L 2)) := by
      rw [Fin.prod_univ_three]
      exact perlat_case1_arith Z (lam L 1) (lam L 2) (lam L 3)
        ((2:ℝ)^(kwin 3 L 0)) ((2:ℝ)^(kwin 3 L 1)) ((2:ℝ)^(kwin 3 L 2))
        hZ hl1pos hl2pos hl3pos hA0pos hA1pos hA2pos h1 h2 hm1 hm2 hm3 hc1
    calc (ballCount L Z : ℝ) ≤ 27 * ∏ j : Fin 3, (1 + Z / lam L (j.val + 1)) := hbc
      _ ≤ 27 * (64 * Z ^ 3 / ((2:ℝ)^(kwin 3 L 0) * (2:ℝ)^(kwin 3 L 1) * (2:ℝ)^(kwin 3 L 2))) :=
          mul_le_mul_of_nonneg_left hprod (by norm_num)
      _ = 1728 * Z ^ 3 / ((2:ℝ)^(kwin 3 L 0) * (2:ℝ)^(kwin 3 L 1) * (2:ℝ)^(kwin 3 L 2)) := by ring
  · intro hc2
    have hprod : (∏ j : Fin 3, (1 + Z / lam L (j.val + 1))) ≤
        32 * Z ^ 2 / ((2:ℝ)^(kwin 3 L 0) * (2:ℝ)^(kwin 3 L 1)) := by
      rw [Fin.prod_univ_three]
      exact perlat_case2_arith Z (lam L 1) (lam L 2) (lam L 3)
        ((2:ℝ)^(kwin 3 L 0)) ((2:ℝ)^(kwin 3 L 1)) ((2:ℝ)^(kwin 3 L 2))
        hZ hl1pos hl2pos hl3pos hA0pos hA1pos h1 h2 hm1 hm2 hm3 hc2
    calc (ballCount L Z : ℝ) ≤ 27 * ∏ j : Fin 3, (1 + Z / lam L (j.val + 1)) := hbc
      _ ≤ 27 * (32 * Z ^ 2 / ((2:ℝ)^(kwin 3 L 0) * (2:ℝ)^(kwin 3 L 1))) :=
          mul_le_mul_of_nonneg_left hprod (by norm_num)
      _ = 864 * Z ^ 2 / ((2:ℝ)^(kwin 3 L 0) * (2:ℝ)^(kwin 3 L 1)) := by ring
      _ ≤ 1728 * Z ^ 2 / ((2:ℝ)^(kwin 3 L 0) * (2:ℝ)^(kwin 3 L 1)) := by
          have hpos : (0:ℝ) < (2:ℝ)^(kwin 3 L 0) * (2:ℝ)^(kwin 3 L 1) := by positivity
          rw [div_le_div_iff_of_pos_right hpos]
          nlinarith [sq_nonneg Z]

end Work.HP.Q44Main
