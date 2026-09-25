/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Seeley extension for a polydisc pair `pd n ρ 1 ⊂ pd n ρ 2`

Assembly of the Seeley extension theorem for the pair `pd n ρ 1 ⊂ pd n ρ 2` in the `C^{k,α}` scale
(`α < 1`).

* `Work.NN.Final.exists_extension_polar` provides the polar Seeley operator `E` for the polydisc pair:
  a single real-linear operator which is the identity on `pd n ρ 1`, depends only on the values on
  `pd n ρ 1`, and satisfies `holderNorm k α (E v) (pd n ρ 2) ≤ ofReal (C k) * holderNorm k α v (pd n ρ 1)`
  for every `v` which is `C^k` on the larger polydisc `pd n ρ 3`.
* `Work.NN.Final.one_sided_extension_le` upgrades a function `v` which is smooth on the *open*
  polydisc `pd n ρ 1` with finite `C^{k,α}`-norm there to a function `ṽ` which is `C^k` on `pd n ρ 3`,
  agrees with `v` on `pd n ρ 1`, and whose `C^{k,α}`-norm on `pd n ρ 3` is controlled by the norm of
  `v` on `pd n ρ 1`.

The estimate for a `v` with finite `C^{k,α}`-norm then follows by replacing `v` with `ṽ` (locality:
`E v = E ṽ`, since the two agree on `pd n ρ 1`) and applying the polar estimate to `ṽ`.  For a `v`
whose `C^{k,α}`-norm on `pd n ρ 1` is infinite the estimate is vacuous.
-/
import Mathlib
import Submission.Work.NN.Final.Defs
import Submission.Work.CR.Flat.Holder
import Submission.Work.NN.Final.one_sided_extension_le
import Submission.Work.NN.Final.exists_extension_polar

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.Final

open Work.CR.Flat

theorem exists_extension {n : ℕ} {α : ℝ} {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (hα0 : 0 < α) (hα1 : α < 1) : ∃ E : ((Fin n → ℂ) → ℂ) →ₗ[ℝ] ((Fin n → ℂ) → ℂ), ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧ (∀ v : (Fin n → ℂ) → ℂ, (∀ m : ℕ, ContDiffOn ℝ m v (Work.NN.Final.pd n ρ 1)) → ∀ z, z ∈ Work.NN.Final.pd n ρ 1 → E v z = v z) ∧ (∀ (k : ℕ) (v : (Fin n → ℂ) → ℂ), (∀ m : ℕ, ContDiffOn ℝ m v (Work.NN.Final.pd n ρ 1)) → Work.CR.Flat.holderNorm k α (E v) (Work.NN.Final.pd n ρ 2) ≤ ENNReal.ofReal (C k) * Work.CR.Flat.holderNorm k α v (Work.NN.Final.pd n ρ 1)) := by
  obtain ⟨E, C1, hC1, hident, hloc, hest⟩ :=
    exists_extension_polar (n := n) (α := α) (ρ := ρ) hρ hα0 hα1
  obtain ⟨C2, hC2, hext⟩ :=
    one_sided_extension_le (n := n) (α := α) (ρ := ρ) hρ hα0 hα1 (c := 3) (by norm_num)
  refine ⟨E, fun k => C1 k * C2 k, fun k => mul_pos (hC1 k) (hC2 k), hident, ?_⟩
  intro k v hv
  by_cases htop : Work.CR.Flat.holderNorm k α v (Work.NN.Final.pd n ρ 1) = ⊤
  · rw [htop,
      ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos (hC1 k) (hC2 k))))]
    exact le_top
  · obtain ⟨vt, hvt_smooth, hvt_eq, hvt_bound⟩ := hext k v hv htop
    have hEv : E v = E vt := hloc v vt (fun z hz => (hvt_eq z hz).symm)
    rw [hEv]
    have h1 : Work.CR.Flat.holderNorm k α (E vt) (Work.NN.Final.pd n ρ 2)
        ≤ ENNReal.ofReal (C1 k) * Work.CR.Flat.holderNorm k α vt (Work.NN.Final.pd n ρ 1) :=
      hest k vt hvt_smooth
    have h2 : Work.CR.Flat.holderNorm k α vt (Work.NN.Final.pd n ρ 1)
        ≤ Work.CR.Flat.holderNorm k α vt (Work.NN.Final.pd n ρ 3) :=
      Work.CR.Flat.holderNorm_mono_set (isOpen_pd ρ 3) (isOpen_pd ρ 1)
        (pd_mono hρ (by norm_num : (1 : ℝ) ≤ 3)) k α vt
    calc Work.CR.Flat.holderNorm k α (E vt) (Work.NN.Final.pd n ρ 2)
        ≤ ENNReal.ofReal (C1 k) * Work.CR.Flat.holderNorm k α vt (Work.NN.Final.pd n ρ 1) := h1
      _ ≤ ENNReal.ofReal (C1 k)
            * (ENNReal.ofReal (C2 k) * Work.CR.Flat.holderNorm k α v (Work.NN.Final.pd n ρ 1)) :=
          mul_le_mul' le_rfl (h2.trans hvt_bound)
      _ = ENNReal.ofReal (C1 k * C2 k) * Work.CR.Flat.holderNorm k α v (Work.NN.Final.pd n ρ 1) := by
          rw [show ENNReal.ofReal (C1 k * C2 k)
                = ENNReal.ofReal (C1 k) * ENNReal.ofReal (C2 k)
              from ENNReal.ofReal_mul (le_of_lt (hC1 k))]
          ring

end Work.NN.Final
