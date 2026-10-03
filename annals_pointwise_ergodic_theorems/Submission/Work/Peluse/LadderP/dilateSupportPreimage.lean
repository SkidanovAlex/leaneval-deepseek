import Mathlib
import Submission.Work.Peluse.Basic

namespace Work.Peluse.LadderP

theorem dilateSupportPreimage {c : ℤ} (hc : 0 < c) {N : ℕ} {r : ℕ}
    (hr : r < c.natAbs) {f : ℤ → ℂ} (hsup : Work.Peluse.SupportIn f N) :
    ∀ ξ : ℤ, ξ ∉ ((Work.Peluse.symIcc N).filter (fun x : ℤ => x % c = (r : ℤ))).image
        (fun x : ℤ => (x - (r : ℤ)) / c) → f ((r : ℤ) + c * ξ) = 0 := by
  -- The preimage of the support under the dilation `x ↦ r + c·ξ` is exactly the set of `ξ` for
  -- which `r + c·ξ` lies in `[-N,N]` with `(r + c·ξ) % c = r`; that set is the image shown.
  intro ξ hξ
  set y : ℤ := (r : ℤ) + c * ξ with hy
  change f y = 0
  by_contra hf
  -- `f y ≠ 0` forces `y ∈ [-N,N]` by the support hypothesis.
  have hle : y.natAbs ≤ N := by
    by_contra h
    exact hf (hsup y (not_le.mp h))
  have hrc : (r : ℤ) < c := by
    have h1 : (r : ℤ) < ((c.natAbs : ℕ) : ℤ) := by exact_mod_cast hr
    rwa [Int.natAbs_of_nonneg hc.le] at h1
  have hyN : y ∈ Work.Peluse.symIcc N := by
    have hcast : (y.natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast hle
    have habs : |y| ≤ (N : ℤ) := by rw [Int.abs_eq_natAbs]; exact hcast
    exact Finset.mem_Icc.mpr ⟨(abs_le.mp habs).1, (abs_le.mp habs).2⟩
  -- `r + c·ξ ≡ r (mod c)` and `0 ≤ r < c`, so its residue is `r`.
  have hmod : y % c = (r : ℤ) := by
    rw [hy, Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt (Int.natCast_nonneg r) hrc
  have hmem : y ∈ (Work.Peluse.symIcc N).filter (fun x : ℤ => x % c = (r : ℤ)) :=
    Finset.mem_filter.mpr ⟨hyN, hmod⟩
  -- and `(y - r)/c = ξ` recovers `ξ`.
  have hdiv : (y - (r : ℤ)) / c = ξ := by
    have : y - (r : ℤ) = c * ξ := by rw [hy]; ring
    rw [this, Int.mul_ediv_cancel_left ξ (ne_of_gt hc)]
  exact hξ (Finset.mem_image.mpr ⟨y, hmem, hdiv⟩)

end Work.Peluse.LadderP
