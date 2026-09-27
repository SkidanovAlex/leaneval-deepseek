import Mathlib
import Submission.Work.Mostow.euclidBlockDefs
import Submission.Work.Mostow.nearId_rotN_bound

/-!
# `Work.Mostow.geeSVblkRotN`

The rotation norm of the block map `vblk r hr R` (identity on the first `r` coordinates and
`R` on the last `m - r` of the chart `E m`) dominates the rotation norm of `R`:

`rotN R ≤ rotN RB` whenever `RB = vblk r hr R` pointwise.

The content is purely linear-algebraic.  The "tail embedding"
`svblkTail r hr : E (m - r) → E m` (first `r` coordinates zero, the last `m - r` equal to `w`) is a
linear isometric embedding and `vblk r hr R` intertwines it with `R`:
`vblk r hr R (svblkTail r hr y) = svblkTail r hr (R y)`.  Hence for unit `y`

`‖R y - y‖ = ‖RB (svblkTail r hr y) - svblkTail r hr y‖ ≤ rotN RB * ‖svblkTail r hr y‖ = rotN RB`,

which is `rotN R ≤ rotN RB` by the pointwise criterion `nib_rotN_le_of_unit`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

/-! ### The tail embedding of `E (n - k)` into `E n` -/

/-- The tail embedding of `E (n - k)` into `E n`: the first `k` coordinates vanish and the last
`n - k` coordinates are those of `w`. -/
def svblkTail (k : ℕ) {n : ℕ} (hk : k ≤ n) (w : E (n - k)) : E n :=
  WithLp.toLp 2 (fun i : Fin n =>
    if _ : (i : ℕ) < k then 0
    else w ⟨i.val - k, by have := i.isLt; omega⟩)

theorem svblk_ofLp_of_lt (k : ℕ) {n : ℕ} (hk : k ≤ n) (w : E (n - k)) (i : Fin n)
    (h : (i : ℕ) < k) : (svblkTail k hk w).ofLp i = 0 := by
  simp [svblkTail, h]

theorem svblk_ofLp_of_ge (k : ℕ) {n : ℕ} (hk : k ≤ n) (w : E (n - k)) (i : Fin n)
    (h : ¬ (i : ℕ) < k) :
    (svblkTail k hk w).ofLp i = w.ofLp ⟨i.val - k, by have := i.isLt; omega⟩ := by
  simp only [svblkTail, WithLp.ofLp_toLp, dite_eq_right h]

theorem tailOf_svblk (k : ℕ) {n : ℕ} (hk : k ≤ n) (w : E (n - k)) :
    tailOf k (svblkTail k hk w) = w := by
  apply WithLp.ofLp_injective
  funext j
  have h1 : (tailOf k (svblkTail k hk w)).ofLp j
      = (svblkTail k hk w).ofLp ⟨k + j.val, by have := j.isLt; omega⟩ :=
    tailOf_ofLp k (svblkTail k hk w) j
  have h2 : (svblkTail k hk w).ofLp ⟨k + j.val, by have := j.isLt; omega⟩
      = w.ofLp ⟨(k + j.val) - k, by have := j.isLt; omega⟩ :=
    svblk_ofLp_of_ge k hk w ⟨k + j.val, by have := j.isLt; omega⟩ (by simp)
  rw [h1, h2]
  have hfin : (⟨(k + j.val) - k, by have := j.isLt; omega⟩ : Fin (n - k)) = j := by
    apply Fin.ext
    dsimp only
    omega
  rw [hfin]

theorem svblk_add (k : ℕ) {n : ℕ} (hk : k ≤ n) (u v : E (n - k)) :
    svblkTail k hk (u + v) = svblkTail k hk u + svblkTail k hk v := by
  apply WithLp.ofLp_injective
  funext i
  rw [WithLp.ofLp_add, Pi.add_apply]
  by_cases h : (i : ℕ) < k
  · rw [svblk_ofLp_of_lt k hk (u + v) i h, svblk_ofLp_of_lt k hk u i h,
      svblk_ofLp_of_lt k hk v i h]
    simp
  · rw [svblk_ofLp_of_ge k hk (u + v) i h, svblk_ofLp_of_ge k hk u i h,
      svblk_ofLp_of_ge k hk v i h, WithLp.ofLp_add, Pi.add_apply]

theorem svblk_sub (k : ℕ) {n : ℕ} (hk : k ≤ n) (u v : E (n - k)) :
    svblkTail k hk (u - v) = svblkTail k hk u - svblkTail k hk v := by
  apply WithLp.ofLp_injective
  funext i
  rw [WithLp.ofLp_sub, Pi.sub_apply]
  by_cases h : (i : ℕ) < k
  · rw [svblk_ofLp_of_lt k hk (u - v) i h, svblk_ofLp_of_lt k hk u i h,
      svblk_ofLp_of_lt k hk v i h]
    simp
  · rw [svblk_ofLp_of_ge k hk (u - v) i h, svblk_ofLp_of_ge k hk u i h,
      svblk_ofLp_of_ge k hk v i h, WithLp.ofLp_sub, Pi.sub_apply]

/-! ### The tail embedding is isometric -/

theorem svblk_symm_splitEquiv_inl (k n : ℕ) (hk : k ≤ n) (a : Fin k) :
    ((splitEquiv k n hk).symm (Sum.inl a) : Fin n) = ⟨a.val, by omega⟩ := by
  rw [Equiv.symm_apply_eq, splitEquiv_apply, splitFun_of_lt k n hk _ (by simpa using a.isLt)]

theorem svblk_symm_splitEquiv_inr (k n : ℕ) (hk : k ≤ n) (b : Fin (n - k)) :
    ((splitEquiv k n hk).symm (Sum.inr b) : Fin n) = ⟨k + b.val, by omega⟩ := by
  rw [Equiv.symm_apply_eq, splitEquiv_apply, splitFun_of_ge k n hk _ (by simp)]
  congr 1
  apply Fin.ext
  dsimp only
  omega

theorem svblk_norm (k : ℕ) {n : ℕ} (hk : k ≤ n) (w : E (n - k)) :
    ‖svblkTail k hk w‖ = ‖w‖ := by
  have hsq : ‖svblkTail k hk w‖ ^ 2 = ‖w‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq (svblkTail k hk w), EuclideanSpace.real_norm_sq_eq w]
    rw [← Equiv.sum_comp (splitEquiv k n hk).symm
      (fun i : Fin n => (svblkTail k hk w).ofLp i ^ 2)]
    rw [Fintype.sum_sum_type]
    have hle : ∀ a : Fin k,
        ((svblkTail k hk w).ofLp ((splitEquiv k n hk).symm (Sum.inl a))) ^ 2 = 0 := by
      intro a
      rw [svblk_symm_splitEquiv_inl k n hk a,
        svblk_ofLp_of_lt k hk w _ (by simpa using a.isLt)]
      ring
    have hge : ∀ b : Fin (n - k),
        ((svblkTail k hk w).ofLp ((splitEquiv k n hk).symm (Sum.inr b))) ^ 2
          = (w.ofLp b) ^ 2 := by
      intro b
      rw [svblk_symm_splitEquiv_inr k n hk b,
        svblk_ofLp_of_ge k hk w _ (by dsimp only; omega)]
      apply congrArg (fun t : ℝ => t ^ 2)
      apply congrArg (fun t : Fin (n - k) => w.ofLp t)
      apply Fin.ext
      dsimp only
      omega
    rw [Finset.sum_congr rfl (fun a _ => hle a), Finset.sum_congr rfl (fun b _ => hge b)]
    simp
  calc ‖svblkTail k hk w‖ = Real.sqrt (‖svblkTail k hk w‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖w‖ ^ 2) := by rw [hsq]
    _ = ‖w‖ := Real.sqrt_sq (norm_nonneg w)

/-! ### `vblk` intertwines the tail embedding with `R` -/

theorem vblk_svblk (k : ℕ) {n : ℕ} (hk : k ≤ n)
    (R : E (n - k) ≃ₗᵢ[ℝ] E (n - k)) (w : E (n - k)) :
    vblk k hk R (svblkTail k hk w) = svblkTail k hk (R w) := by
  apply WithLp.ofLp_injective
  funext i
  by_cases h : (i : ℕ) < k
  · rw [vblk_ofLp_of_lt k hk R (svblkTail k hk w) i h, svblk_ofLp_of_lt k hk w i h,
      svblk_ofLp_of_lt k hk (R w) i h]
  · rw [vblk_ofLp_of_ge k hk R (svblkTail k hk w) i h, tailOf_svblk,
      svblk_ofLp_of_ge k hk (R w) i h]

theorem svblk_rotN_nonneg {m : ℕ} (R : E m ≃ₗᵢ[ℝ] E m) : 0 ≤ rotN R := by
  rw [Submission.Mostow.rotN]
  exact norm_nonneg _

/-! ### The theorem -/

theorem geeSVblkRotN (m r : ℕ) (hr : r ≤ m)
    (R : Submission.Mostow.E (m - r) ≃ₗᵢ[ℝ] Submission.Mostow.E (m - r))
    (RB : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)
    (h : ∀ u : Submission.Mostow.E m, RB u = Work.Mostow.vblk r hr R u) :
    Submission.Mostow.rotN R ≤ Submission.Mostow.rotN RB := by
  refine nib_rotN_le_of_unit (svblk_rotN_nonneg RB) ?_
  intro y hy
  have hRu : RB (svblkTail r hr y) = svblkTail r hr (R y) := by
    rw [h (svblkTail r hr y), vblk_svblk]
  have hdiff : RB (svblkTail r hr y) - svblkTail r hr y = svblkTail r hr (R y - y) := by
    rw [hRu, svblk_sub]
  have hnorm : ‖R y - y‖ = ‖RB (svblkTail r hr y) - svblkTail r hr y‖ := by
    rw [hdiff, svblk_norm]
  have hu : ‖svblkTail r hr y‖ = 1 := by rw [svblk_norm, hy]
  calc ‖R y - y‖ = ‖RB (svblkTail r hr y) - svblkTail r hr y‖ := hnorm
    _ ≤ rotN RB * ‖svblkTail r hr y‖ := nib_apply_le_rotN m RB _
    _ = rotN RB := by rw [hu, mul_one]

end

end Work.Mostow
