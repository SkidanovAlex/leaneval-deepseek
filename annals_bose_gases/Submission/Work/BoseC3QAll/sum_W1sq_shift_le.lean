import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Submission.Work.BoseC3QAll.PH_subset_PHq_sub
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseC3QAll.sum_W1sq_shift_le` — the shifted `Ŵ₁²/‖k‖²` lattice sum

The lattice bound `Q3KernelFSAll.sum_W1sq` controls the sum of `Ŵ₁(q)²/‖q‖²` over the
quarter region `P_H^q = {|q| ≥ ¼K_H⁻¹a⁻¹}`.  The `Q₃` word, however, carries the
`k`-weights `Ŵ₁(s − k)` over `k ∈ P_H` (`s ∈ supp f_L`) and every one of those
shifted modes lands in `P_H^q` (`PH_subset_PHq_sub.sub_mem_PHq`, using the scale
separation `K_L√(μa) ≤ ¼K_H⁻¹a⁻¹` at diluteness `μa³ ≤ 4^{-24}`).

Since `k ↦ s − k` is injective, the shifted sum is the sum over the image set,
which is contained in the `P_H^q`-filtered sum, and the extra terms are
nonnegative (`Ŵ₁²/‖·‖² ≥ 0`).  Multiplying the lattice bound by `ℓ³ > 0` gives
the stated `ℓ³K₀a`.

Nothing about the shift `s` is used beyond `hfL : f_L s ≠ 0` (through
`f_L_supp`); in particular no threshold on `t` other than the diluteness
hypothesis `hle` appears.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseC3QAll

open Work.BoseB7

/-- `kmom 0 = 0`, from the oddness `kmom (-i) = -kmom i` at `i = 0`. -/
lemma kmom_zero_shift {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (F : FockData Mode) : F.kmom 0 = 0 := by
  have h2 := F.kmom_neg 0
  rw [neg_zero] at h2
  have h : F.kmom 0 + F.kmom 0 = 0 := by
    nth_rewrite 1 [h2]
    abel
  have h3 : (2 : ℝ) • F.kmom 0 = 0 := by
    rw [two_smul]
    exact h
  exact (smul_eq_zero.mp h3).resolve_left (by norm_num)

theorem sum_W1sq_shift_le (K₀ : ℝ)
    {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (T : Work.BoseC3QAll.TildeData F)
    (E : Work.BoseB7.Q3Env Mode) (hv : Work.BoseB7.FSParamsView E)
    (hle : hv.t ≤ (1 / 4 : ℝ) ^ 36) (hK : Work.BoseC3QAll.Q3KernelFSAll K₀ F T E)
    (s : Mode) (hfL : E.fL s ≠ 0) :
    ∑ k ∈ ((F.PHset E).filter (fun k => E.W1 k ≠ 0)),
        E.W1 (s - k) ^ 2 / ‖F.kmom (s - k)‖ ^ 2
      ≤ E.ell ^ 3 * (K₀ * E.aScat) := by
  have hell : 0 < E.ell := ell_pos E hv
  have hsmall8 := ratio_small8 E hv hle
  -- every `s − k` with `k ∈ P_H` **and** `Ŵ₁ k ≠ 0` lies in the quarter region
  have hq : ∀ k ∈ ((F.PHset E).filter (fun k => E.W1 k ≠ 0)),
      F.PHq E.KH E.aScat (s - k) :=
    fun k hk => sub_mem_PHq F E hv hsmall8 (fun a b hf hk hW => hK.kmom_subW a b hf hk hW)
      (fun s hf => hK.fL_supp2 s hf) hfL (Finset.mem_filter.mp hk).1
      (Finset.mem_filter.mp hk).2
  have hcutpos : 0 < 1 / (4 * E.KH * E.aScat) := by
    have hKH : 0 < E.KH := lt_of_lt_of_le zero_lt_one hv.one_le_KH
    have ha : 0 < E.aScat := hv.a_pos
    positivity
  -- hence `s − k ≠ 0` and the shifted modes are excited
  have hne : ∀ k ∈ ((F.PHset E).filter (fun k => E.W1 k ≠ 0)), s - k ≠ 0 := by
    intro k hk h0
    have hphq : (1 : ℝ) / (4 * E.KH * E.aScat) ≤ ‖F.kmom (s - k)‖ := hq k hk
    rw [h0, kmom_zero_shift F, norm_zero] at hphq
    linarith
  have himage : ((F.PHset E).filter (fun k => E.W1 k ≠ 0)).image (fun k => s - k) ⊆
      (excited Mode).filter (F.PHq E.KH E.aScat) := by
    intro q hqmem
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hqmem
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_erase.mpr ⟨hne k hk, Finset.mem_univ _⟩, hq k hk⟩
  -- `k ↦ s − k` is injective on the lattice
  have hinj : ∀ k1 ∈ ((F.PHset E).filter (fun k => E.W1 k ≠ 0)),
      ∀ k2 ∈ ((F.PHset E).filter (fun k => E.W1 k ≠ 0)), s - k1 = s - k2 → k1 = k2 := by
    intro k1 _ k2 _ h
    exact sub_right_inj.mp h
  have hsum_img : ∑ k ∈ ((F.PHset E).filter (fun k => E.W1 k ≠ 0)),
        E.W1 (s - k) ^ 2 / ‖F.kmom (s - k)‖ ^ 2
      = ∑ q ∈ ((F.PHset E).filter (fun k => E.W1 k ≠ 0)).image (fun k => s - k),
          E.W1 q ^ 2 / ‖F.kmom q‖ ^ 2 :=
    (Finset.sum_image (f := fun q => E.W1 q ^ 2 / ‖F.kmom q‖ ^ 2)
      (g := fun k => s - k) hinj).symm
  have hmono : ∑ q ∈ ((F.PHset E).filter (fun k => E.W1 k ≠ 0)).image (fun k => s - k),
        E.W1 q ^ 2 / ‖F.kmom q‖ ^ 2
      ≤ ∑ q ∈ (excited Mode).filter (F.PHq E.KH E.aScat), E.W1 q ^ 2 / ‖F.kmom q‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg himage
      (fun q _ _ => div_nonneg (sq_nonneg _) (sq_nonneg _))
  -- the lattice bound, multiplied by `ℓ³ > 0`
  have hbound : ∑ q ∈ (excited Mode).filter (F.PHq E.KH E.aScat),
        E.W1 q ^ 2 / ‖F.kmom q‖ ^ 2 ≤ E.ell ^ 3 * (K₀ * E.aScat) := by
    have hinv : E.ell ^ 3 * E.ell ^ (-(3 : ℝ)) = 1 := by
      rw [← Real.rpow_natCast E.ell 3, ← Real.rpow_add hell]
      norm_num
    have h3nn : 0 ≤ E.ell ^ 3 := (pow_pos hell 3).le
    have h4 := mul_le_mul_of_nonneg_left hK.sum_W1sq h3nn
    rw [← mul_assoc, hinv, one_mul] at h4
    exact h4
  calc ∑ k ∈ ((F.PHset E).filter (fun k => E.W1 k ≠ 0)),
        E.W1 (s - k) ^ 2 / ‖F.kmom (s - k)‖ ^ 2
      = ∑ q ∈ ((F.PHset E).filter (fun k => E.W1 k ≠ 0)).image (fun k => s - k),
          E.W1 q ^ 2 / ‖F.kmom q‖ ^ 2 :=
        hsum_img
    _ ≤ ∑ q ∈ (excited Mode).filter (F.PHq E.KH E.aScat), E.W1 q ^ 2 / ‖F.kmom q‖ ^ 2 :=
        hmono
    _ ≤ E.ell ^ 3 * (K₀ * E.aScat) := hbound

end Work.BoseC3QAll
