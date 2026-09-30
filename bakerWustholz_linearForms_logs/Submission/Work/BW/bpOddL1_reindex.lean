import Mathlib
import Submission.Work.BW.bpOddDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

theorem bpOddL1_reindex {η : ℝ} {m : ℕ} (hm : 1 ≤ m) {i₀ : ℤ} (hi : -(m:ℤ) ≤ i₀)
    (hi' : i₀ ≤ (m:ℤ) - 1) :
    ∏ k ∈ (oddIdx (2*m)).erase (2*i₀+1), (|(k:ℝ) - ((2*i₀+1 : ℤ) : ℝ)| - η)
      = ∏ d ∈ (Finset.Icc (-(((m:ℤ)+i₀).toNat : ℤ)) ((((m:ℤ)-1-i₀).toNat : ℤ))).erase 0,
          (2*|(d:ℝ)| - η) := by
  have hc : 0 ≤ (m:ℤ) + i₀ := by omega
  have hd : 0 ≤ (m:ℤ) - 1 - i₀ := by omega
  have eA : -(((m:ℤ)+i₀).toNat : ℤ) = -((m:ℤ)+i₀) := by rw [Int.toNat_of_nonneg hc]
  have eB : ((((m:ℤ)-1-i₀).toNat : ℤ)) = (m:ℤ)-1-i₀ := Int.toNat_of_nonneg hd
  rw [eA, eB]
  have himg : oddIdx (2*m) =
      (Finset.Icc (-((m:ℤ)+i₀)) ((m:ℤ)-1-i₀)).image (fun d : ℤ => 2*i₀+1+2*d) := by
    ext k
    rw [mem_oddIdx_iff, Finset.mem_image]
    simp only [Finset.mem_Icc]
    constructor
    · rintro ⟨⟨j, rfl⟩, h1, h2⟩
      exact ⟨j - i₀, ⟨by omega, by omega⟩, by ring⟩
    · rintro ⟨d, ⟨h1, h2⟩, heq⟩
      rw [← heq]
      exact ⟨⟨i₀ + d, by ring⟩, by omega, by omega⟩
  have hinj : Function.Injective (fun d : ℤ => 2*i₀+1+2*d) := by
    intro a b hab
    have h2 : 2*a = 2*b := by linarith
    exact mul_left_cancel₀ (by norm_num : (2:ℤ) ≠ 0) h2
  have herase : (oddIdx (2*m)).erase (2*i₀+1)
      = ((Finset.Icc (-((m:ℤ)+i₀)) ((m:ℤ)-1-i₀)).erase 0).image (fun d : ℤ => 2*i₀+1+2*d) := by
    rw [himg, Finset.image_erase hinj (Finset.Icc (-((m:ℤ)+i₀)) ((m:ℤ)-1-i₀)) 0]
    simp only [mul_zero, add_zero]
  rw [herase, Finset.prod_image hinj.injOn]
  apply Finset.prod_congr rfl
  intro d hdmem
  have hterm : ((2*i₀+1+2*d : ℤ) : ℝ) - ((2*i₀+1 : ℤ) : ℝ) = 2*(d:ℝ) := by push_cast; ring
  rw [hterm, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]

end Work.BW
