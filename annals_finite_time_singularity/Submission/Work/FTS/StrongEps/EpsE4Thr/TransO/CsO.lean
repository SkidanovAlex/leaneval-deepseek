/-
Copyright: work module for the Elgindi finite-time singularity project.

# `EpsE4Thr/TransO/CsO.lean` — the Cauchy–Schwarz clause of the transfer step, open class

`Submission/Work/FTS/StrongEps/EpsE4Thr/step2_data_ge_O.lean` proves the open-class induction
step of the *clean* coercivity (`CoerData2O α n → CoerData2O α (n+1)`) and, on the way, the two
private helpers `normSub_O` (the three one-sided `ℋ`-norm comparisons of the slots) and
`cs_clause_succ_O` (the level-`(n+1)` Cauchy–Schwarz bound for `HkIPStep`).  Private helpers
cannot be imported, and the *transfer* step (`TransO/StepTO.lean`) consumes exactly the second
one, so this module re-derives both under public names.

Everything is proved outright and rests on `[propext, Classical.choice, Quot.sound]` only.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.StrongEps.EpsE4Thr.regQo_dth_dz
import Submission.Work.FTS.CoercivityFix.Assembly.HkSq_Dth_le_ge
import Submission.Work.FTS.CoercivityFix.Transfer.HkSq_Dz_le_Q0Sm
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_mono_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.TransO

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The open-class `normSub`.**  For `f` which is `C^∞` on the open quadrant and honest at
order `n+1`, the level-`n` norms of the three slots `f`, `D_θ f`, `D_z f` are dominated by the
level-`(n+1)` norm of `f`. -/
theorem normSub_O (α : ℝ) (hα : 0 < α) (n : ℕ) (f : Fn)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α (n + 1) f) :
    Work.Spaces.HkSq α n f ≤ Work.Spaces.HkSq α (n + 1) f
      ∧ Work.Spaces.HkSq α n (Work.Spaces.Dth f) ≤ Work.Spaces.HkSq α (n + 1) f
      ∧ Work.Spaces.HkSq α n (Work.Spaces.Dz f) ≤ Work.Spaces.HkSq α (n + 1) f :=
  ⟨Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (Nat.le_succ n) hmem,
   Work.FTS.CoercivityFix.Assembly.HkSq_Dth_le_ge α (by linarith) n hmem,
   Work.FTS.CoercivityFix.Transfer.HkSq_Dz_le_Q0Sm α n
     ((Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hsm (n + 1)) hmem⟩

/-- **The Cauchy–Schwarz clause of the step, at level `n+1`** (open class).  From the level-`n`
Cauchy–Schwarz bound of `IP` and the three one-sided norm comparisons
(`|f|_n ≤ |f|_{n+1}`, `|D_θ f|_n ≤ |f|_{n+1}`, `|D_z f|_n ≤ |f|_{n+1}`) one obtains the
level-`(n+1)` bound for `HkIPStep c₁ c₂ IP = IP + c₁ IP(D_θ·, D_θ·) + c₂ IP(D_z·, D_z·)`, with
the constant `3 * max 1 (max c₁ c₂) * CC`.

This is the public copy of the private helper of `step2_data_ge_O`. -/
theorem cs_clause_succ_O (α : ℝ) (hα : 0 < α) (n : ℕ)
    {IP : Fn → Fn → ℝ} {CC : ℝ}
    (hcs : ∀ f g : Fn, RegQo α n f → RegQo α n g →
      |IP f g| ≤ CC * Work.Spaces.HkNorm α n f * Work.Spaces.HkNorm α n g)
    (hCC : 0 ≤ CC)
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    ∀ f g : Fn, RegQo α (n + 1) f → RegQo α (n + 1) g →
      |Work.Coercivity.HkIPStep c₁ c₂ IP f g|
        ≤ 3 * max 1 (max c₁ c₂) * CC * Work.Spaces.HkNorm α (n + 1) f
            * Work.Spaces.HkNorm α (n + 1) g := by
  intro f g hf hg
  have hfn : RegQo α n f := regQo_mono (Nat.le_succ n) hf
  have hgn : RegQo α n g := regQo_mono (Nat.le_succ n) hg
  have hdfn : RegQo α n (Work.Spaces.Dth f) := (regQo_dth_dz hα hf).1
  have hdgn : RegQo α n (Work.Spaces.Dth g) := (regQo_dth_dz hα hg).1
  have hdzn : RegQo α n (Work.Spaces.Dz f) := (regQo_dth_dz hα hf).2
  have hdzn' : RegQo α n (Work.Spaces.Dz g) := (regQo_dth_dz hα hg).2
  have e0 := hcs f g hfn hgn
  have e1 := hcs (Work.Spaces.Dth f) (Work.Spaces.Dth g) hdfn hdgn
  have e2 := hcs (Work.Spaces.Dz f) (Work.Spaces.Dz g) hdzn hdzn'
  obtain ⟨ns0f, ns1f, ns2f⟩ := normSub_O α hα n f hf.1 hf.2.1
  obtain ⟨ns0g, ns1g, ns2g⟩ := normSub_O α hα n g hg.1 hg.2.1
  have n0f : Work.Spaces.HkNorm α n f ≤ Work.Spaces.HkNorm α (n + 1) f := Real.sqrt_le_sqrt ns0f
  have n0g : Work.Spaces.HkNorm α n g ≤ Work.Spaces.HkNorm α (n + 1) g := Real.sqrt_le_sqrt ns0g
  have n1f : Work.Spaces.HkNorm α n (Work.Spaces.Dth f) ≤ Work.Spaces.HkNorm α (n + 1) f :=
    Real.sqrt_le_sqrt ns1f
  have n1g : Work.Spaces.HkNorm α n (Work.Spaces.Dth g) ≤ Work.Spaces.HkNorm α (n + 1) g :=
    Real.sqrt_le_sqrt ns1g
  have n2f : Work.Spaces.HkNorm α n (Work.Spaces.Dz f) ≤ Work.Spaces.HkNorm α (n + 1) f :=
    Real.sqrt_le_sqrt ns2f
  have n2g : Work.Spaces.HkNorm α n (Work.Spaces.Dz g) ≤ Work.Spaces.HkNorm α (n + 1) g :=
    Real.sqrt_le_sqrt ns2g
  have hF : 0 ≤ Work.Spaces.HkNorm α (n + 1) f := Real.sqrt_nonneg _
  have hG : 0 ≤ Work.Spaces.HkNorm α (n + 1) g := Real.sqrt_nonneg _
  have b0 : |IP f g|
      ≤ CC * Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g := by
    calc |IP f g| ≤ CC * Work.Spaces.HkNorm α n f * Work.Spaces.HkNorm α n g := e0
      _ = CC * (Work.Spaces.HkNorm α n f * Work.Spaces.HkNorm α n g) := by ring
      _ ≤ CC * (Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul n0f n0g (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hCC
      _ = CC * Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g := by ring
  have b1 : |IP (Work.Spaces.Dth f) (Work.Spaces.Dth g)|
      ≤ CC * Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g := by
    calc |IP (Work.Spaces.Dth f) (Work.Spaces.Dth g)|
        ≤ CC * Work.Spaces.HkNorm α n (Work.Spaces.Dth f)
            * Work.Spaces.HkNorm α n (Work.Spaces.Dth g) := e1
      _ = CC * (Work.Spaces.HkNorm α n (Work.Spaces.Dth f)
            * Work.Spaces.HkNorm α n (Work.Spaces.Dth g)) := by ring
      _ ≤ CC * (Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul n1f n1g (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hCC
      _ = CC * Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g := by ring
  have b2 : |IP (Work.Spaces.Dz f) (Work.Spaces.Dz g)|
      ≤ CC * Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g := by
    calc |IP (Work.Spaces.Dz f) (Work.Spaces.Dz g)|
        ≤ CC * Work.Spaces.HkNorm α n (Work.Spaces.Dz f)
            * Work.Spaces.HkNorm α n (Work.Spaces.Dz g) := e2
      _ = CC * (Work.Spaces.HkNorm α n (Work.Spaces.Dz f)
            * Work.Spaces.HkNorm α n (Work.Spaces.Dz g)) := by ring
      _ ≤ CC * (Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul n2f n2g (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hCC
      _ = CC * Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g := by ring
  have key : |Work.Coercivity.HkIPStep c₁ c₂ IP f g|
      ≤ CC * (Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g)
        + c₁ * (CC * Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g)
        + c₂ * (CC * Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g) := by
    have h1 : Work.Coercivity.HkIPStep c₁ c₂ IP f g
        = IP f g + c₁ * IP (Work.Spaces.Dth f) (Work.Spaces.Dth g)
          + c₂ * IP (Work.Spaces.Dz f) (Work.Spaces.Dz g) := rfl
    have main : |IP f g + c₁ * IP (Work.Spaces.Dth f) (Work.Spaces.Dth g)
          + c₂ * IP (Work.Spaces.Dz f) (Work.Spaces.Dz g)|
        ≤ |IP f g| + c₁ * |IP (Work.Spaces.Dth f) (Work.Spaces.Dth g)|
          + c₂ * |IP (Work.Spaces.Dz f) (Work.Spaces.Dz g)| := by
      have t1 := abs_add_le (IP f g + c₁ * IP (Work.Spaces.Dth f) (Work.Spaces.Dth g))
        (c₂ * IP (Work.Spaces.Dz f) (Work.Spaces.Dz g))
      have t2 := abs_add_le (IP f g) (c₁ * IP (Work.Spaces.Dth f) (Work.Spaces.Dth g))
      have E1 : |c₁ * IP (Work.Spaces.Dth f) (Work.Spaces.Dth g)|
          = c₁ * |IP (Work.Spaces.Dth f) (Work.Spaces.Dth g)| := by
        rw [abs_mul, abs_of_pos hc₁]
      have E2 : |c₂ * IP (Work.Spaces.Dz f) (Work.Spaces.Dz g)|
          = c₂ * |IP (Work.Spaces.Dz f) (Work.Spaces.Dz g)| := by
        rw [abs_mul, abs_of_pos hc₂]
      linarith
    have A1 := mul_le_mul_of_nonneg_left b1 hc₁.le
    have A2 := mul_le_mul_of_nonneg_left b2 hc₂.le
    rw [h1]
    calc |IP f g + c₁ * IP (Work.Spaces.Dth f) (Work.Spaces.Dth g)
            + c₂ * IP (Work.Spaces.Dz f) (Work.Spaces.Dz g)|
        ≤ |IP f g| + c₁ * |IP (Work.Spaces.Dth f) (Work.Spaces.Dth g)|
            + c₂ * |IP (Work.Spaces.Dz f) (Work.Spaces.Dz g)| := main
      _ ≤ CC * (Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g)
            + c₁ * (CC * Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g)
            + c₂ * (CC * Work.Spaces.HkNorm α (n + 1) f
                * Work.Spaces.HkNorm α (n + 1) g) := by linarith [b0, A1, A2]
  have hcoef : 1 + c₁ + c₂ ≤ 3 * max 1 (max c₁ c₂) := by
    have h1 : (1 : ℝ) ≤ max 1 (max c₁ c₂) := le_max_left _ _
    have h2 : c₁ ≤ max 1 (max c₁ c₂) := le_trans (le_max_left _ _) (le_max_right _ _)
    have h3 : c₂ ≤ max 1 (max c₁ c₂) := le_trans (le_max_right _ _) (le_max_right _ _)
    linarith
  have hmax : 0 ≤ max 1 (max c₁ c₂) := le_trans zero_le_one (le_max_left _ _)
  have hpos : (0 : ℝ) ≤ 1 + c₁ + c₂ := by linarith
  have hfin : CC * (1 + c₁ + c₂) ≤ 3 * max 1 (max c₁ c₂) * CC := by
    nlinarith [hcoef, hCC, hmax, hpos]
  calc |Work.Coercivity.HkIPStep c₁ c₂ IP f g|
      ≤ CC * (Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g)
        + c₁ * (CC * Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g)
        + c₂ * (CC * Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g) := key
    _ = (CC * (1 + c₁ + c₂))
          * (Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g) := by
        ring
    _ ≤ (3 * max 1 (max c₁ c₂) * CC)
          * (Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g) :=
        mul_le_mul_of_nonneg_right hfin (mul_nonneg hF hG)
    _ = 3 * max 1 (max c₁ c₂) * CC * Work.Spaces.HkNorm α (n + 1) f
          * Work.Spaces.HkNorm α (n + 1) g := by
        ring

end Work.FTS.StrongEps.EpsE4Thr.TransO
