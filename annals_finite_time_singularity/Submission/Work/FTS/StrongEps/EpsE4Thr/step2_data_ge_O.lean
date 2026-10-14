import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.CoercivityFix.Assembly.step2_data
import Submission.Work.FTS.EllipticEst.TT.ESW.Tk_B_le_chain_uniform
import Submission.Work.FTS.StrongPersist.N6Trans.LeibMajor.EasyLeib_le_EasyMajor
import Submission.Work.FTS.StrongPersist.N6Trans.T1Hon.EasyLeibIntBound
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS_MuLamOK.Rows.Rl1Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The one-sided norm comparison of the three slots, in the open class -/

/-- **The open-class `normSub`.**  For `f` which is `C^∞` on the open quadrant and honest at
order `n+1`, the level-`n` norms of the three slots `f`, `D_θ f`, `D_z f` are dominated by the
level-`(n+1)` norm of `f`.

* the `f`-slot is the monotonicity of the `ℋ`-norm in the order;
* the `D_θ`-slot is `Assembly.HkSq_Dth_le_ge` (the sharp range `α ≥ -1/10`);
* the `D_z`-slot is the finite-order open-quadrant shift `Transfer.HkSq_Dz_le_Q0Sm`, whose
  smoothness input `Q0Sm (n+1) f` is exactly `SmoothOpen f` at order `n+1`. -/
private theorem normSub_O (α : ℝ) (hα : 0 < α) (n : ℕ) (f : Fn)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α (n + 1) f) :
    Work.Spaces.HkSq α n f ≤ Work.Spaces.HkSq α (n + 1) f
      ∧ Work.Spaces.HkSq α n (Work.Spaces.Dth f) ≤ Work.Spaces.HkSq α (n + 1) f
      ∧ Work.Spaces.HkSq α n (Work.Spaces.Dz f) ≤ Work.Spaces.HkSq α (n + 1) f :=
  ⟨Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (Nat.le_succ n) hmem,
   Work.FTS.CoercivityFix.Assembly.HkSq_Dth_le_ge α (by linarith) n hmem,
   Work.FTS.CoercivityFix.Transfer.HkSq_Dz_le_Q0Sm α n
     ((Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hsm (n + 1)) hmem⟩

/-! ## The Cauchy–Schwarz clause of the step -/

/-- **The Cauchy–Schwarz clause of the step, at level `n+1`.**  From the level-`n`
Cauchy–Schwarz bound of `IP` and the three one-sided norm comparisons
(`|f|_n ≤ |f|_{n+1}`, `|D_θ f|_n ≤ |f|_{n+1}`, `|D_z f|_n ≤ |f|_{n+1}`) one obtains the
level-`(n+1)` bound for `HkIPStep c₁ c₂ IP = IP + c₁ IP(D_θ·, D_θ·) + c₂ IP(D_z·, D_z·)`, with
the constant `3 * max 1 (max c₁ c₂) * CC`: three slots, each costing the factor
`max 1 (max c₁ c₂)`.

This is the open-class twin of `Assembly.cs_clause_succ`; the regularity descents are
`regQo_mono` and the open-class port `regQo_dth_dz` (which needs `0 < α`, the range here). -/
private theorem cs_clause_succ_O (α : ℝ) (hα : 0 < α) (n : ℕ)
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
  -- the level-`n` memberships of the three slots
  have hfn : RegQo α n f := regQo_mono (Nat.le_succ n) hf
  have hgn : RegQo α n g := regQo_mono (Nat.le_succ n) hg
  have hdfn : RegQo α n (Work.Spaces.Dth f) := (regQo_dth_dz hα hf).1
  have hdgn : RegQo α n (Work.Spaces.Dth g) := (regQo_dth_dz hα hg).1
  have hdzn : RegQo α n (Work.Spaces.Dz f) := (regQo_dth_dz hα hf).2
  have hdzn' : RegQo α n (Work.Spaces.Dz g) := (regQo_dth_dz hα hg).2
  -- Cauchy–Schwarz at level `n`
  have e0 := hcs f g hfn hgn
  have e1 := hcs (Work.Spaces.Dth f) (Work.Spaces.Dth g) hdfn hdgn
  have e2 := hcs (Work.Spaces.Dz f) (Work.Spaces.Dz g) hdzn hdzn'
  -- the three one-sided norm comparisons
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

/-! ## The coercivity clause of the step -/

/-- **Young's inequality in the form used by the induction step.**  If `0 < lam` and
`p ^ 2 ≤ A * (4 * lam)`, then `p √x √y ≤ lam x + A y` for `x, y ≥ 0`.  (The same as the
private helper of `Assembly.coer_clause_succ`, which is not importable.) -/
private lemma young_absorb_O {lam p x y A : ℝ} (hlam : 0 < lam) (hx : 0 ≤ x)
    (hy : 0 ≤ y) (hA : p ^ 2 ≤ A * (4 * lam)) :
    p * (Real.sqrt x * Real.sqrt y) ≤ lam * x + A * y := by
  have h4 : 0 < 4 * lam := by linarith
  have hsx : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx
  have hsy : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt hy
  have h1 : 4 * lam * (p * (Real.sqrt x * Real.sqrt y)) ≤ 4 * lam ^ 2 * x + p ^ 2 * y := by
    nlinarith [sq_nonneg (2 * lam * Real.sqrt x - p * Real.sqrt y), hsx, hsy]
  have h2 : p ^ 2 * y ≤ A * (4 * lam) * y := mul_le_mul_of_nonneg_right hA hy
  have key : 4 * lam * (p * (Real.sqrt x * Real.sqrt y)) ≤ 4 * lam * (lam * x + A * y) := by
    nlinarith [h1, h2]
  exact le_of_mul_le_mul_left key h4

/-- **The coercivity clause of the corrected step, on the open class.**  This is
`Assembly.coer_clause_succ` with `RegQ → RegQo`: the source class is `RegQo α (n+2)`, the
level-`n` data live on `RegQo α (n+1)`, and the regularity ports of `StepReg2O` supply the
membership descents (`mono2`, `dth1`/`dz1`, `ldz`, `e2r`, `dz2`).

The numerical argument (Young/AM–GM absorption of the `Ê₂`-pairing into the level-`n`
coercivity slack, then the coefficient bookkeeping `cc·min 1 (min c₁ c₂)/2`) is the paper's,
transcribed from the frozen proof. -/
private theorem coer_clause_succ_O (α : ℝ) (n : ℕ) {IP : Fn → Fn → ℝ}
    {cc CC κ c₁ c₂ D : ℝ}
    (hdata : CoerData2O α n IP cc CC)
    (hκ : 0 ≤ κ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hD : 0 < D)
    (hsmall : Work.FTS.CoercivityFix.StepSmall cc CC κ c₁ c₂)
    (hr : StepReg2O α n)
    (hc : Comm2O α n IP)
    (hE2 : ∀ f : Fn, RegQo α (n + 1) f →
      Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.E2hat f)
        ≤ κ * (Work.Spaces.HkNorm α n f + Work.Spaces.HkNorm α n (Work.Spaces.Dth f)))
    (hnormD : ∀ f : Fn, RegQo α (n + 1) f →
      Work.Spaces.HkSq α (n + 1) f
        ≤ D * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)
            + Work.Spaces.HkSq α n (Work.Spaces.Dz f))) :
    ∀ f : Fn, RegQo α (n + 2) f →
      cc * min 1 (min c₁ c₂) / (2 * D) * Work.Spaces.HkSq α (n + 1) f
        ≤ Work.Coercivity.HkIPStep c₁ c₂ IP (Work.FTS.CoercivityFix.Lhat f) f := by
  intro f hf
  -- the regularity ports of `StepReg2O`
  have hf0 : RegQo α (n + 1) f := hr.mono2 f hf
  have hf1 : RegQo α (n + 1) (Work.Spaces.Dth f) := hr.dth1 f hf
  have hf2 : RegQo α (n + 1) (Work.Spaces.Dz f) := hr.dz1 f hf
  have hf2n : RegQo α n (Work.Spaces.Dz f) := hr.dz2 f hf
  have hL2 : RegQo α n (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f)) := hr.ldz f hf
  have hE2r : RegQo α n (Work.FTS.CoercivityFix.E2hat f) := hr.e2r f hf0
  -- the two commutator identities transfer the operator onto the differentiated slot
  have e1 : IP (Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f)) (Work.Spaces.Dth f)
      = IP (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f)) (Work.Spaces.Dth f) :=
    hc.congr _ _ _ (fun z θ h => hc.dthC f hf.1 z θ h)
  have e2 : IP (Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f)) (Work.Spaces.Dz f)
      = IP (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f)) (Work.Spaces.Dz f)
        + IP (Work.FTS.CoercivityFix.E2hat f) (Work.Spaces.Dz f) := by
    rw [hc.congr (Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f))
      (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f) + Work.FTS.CoercivityFix.E2hat f)
      (Work.Spaces.Dz f) (fun z θ h => by
        have hh := hc.dzC f hf.1 z θ h
        simpa using hh)]
    exact hc.add _ _ _ hL2 hE2r hf2n
  set X0 : ℝ := Work.Spaces.HkSq α n f with hX0
  set X1 : ℝ := Work.Spaces.HkSq α n (Work.Spaces.Dth f) with hX1
  set X2 : ℝ := Work.Spaces.HkSq α n (Work.Spaces.Dz f) with hX2
  set Y : ℝ := Work.Spaces.HkSq α (n + 1) f with hY
  set m : ℝ := min 1 (min c₁ c₂) with hm
  have hX0nn : 0 ≤ X0 := by rw [hX0]; exact Work.Spaces.HkSq_nonneg α n f
  have hX1nn : 0 ≤ X1 := by rw [hX1]; exact Work.Spaces.HkSq_nonneg α n _
  have hX2nn : 0 ≤ X2 := by rw [hX2]; exact Work.Spaces.HkSq_nonneg α n _
  have hNf : Work.Spaces.HkNorm α n f = Real.sqrt X0 := by rw [Work.Spaces.HkNorm, ← hX0]
  have hN1 : Work.Spaces.HkNorm α n (Work.Spaces.Dth f) = Real.sqrt X1 := by
    rw [Work.Spaces.HkNorm, ← hX1]
  have hN2 : Work.Spaces.HkNorm α n (Work.Spaces.Dz f) = Real.sqrt X2 := by
    rw [Work.Spaces.HkNorm, ← hX2]
  -- the smallness of the step coefficient in the two binomial forms used below
  have hp1 : (c₂ * CC * κ) ^ 2 ≤ (c₂ * cc / 4) * (4 * (cc / 4)) := by
    have h := mul_le_mul_of_nonneg_left hsmall.1 hc₂.le
    nlinarith [h]
  have hp2 : (c₂ * CC * κ) ^ 2 ≤ (c₂ * cc / 4) * (4 * (c₁ * cc / 4)) := by
    have h := mul_le_mul_of_nonneg_left hsmall.2 hc₂.le
    nlinarith [h]
  -- the `Ê₂`-pairing, absorbed into the level-`n` coercivity slack
  have hS : (c₂ * CC * κ) * (Real.sqrt X0 + Real.sqrt X1) * Real.sqrt X2
      ≤ cc / 4 * X0 + (c₁ * cc / 4) * X1 + (c₂ * cc / 2) * X2 := by
    have hccpos : 0 < cc := hdata.hcc
    have hy0 := young_absorb_O (lam := cc / 4) (p := c₂ * CC * κ) (x := X0) (y := X2)
      (A := c₂ * cc / 4) (by positivity) hX0nn hX2nn hp1
    have hy1 := young_absorb_O (lam := c₁ * cc / 4) (p := c₂ * CC * κ) (x := X1) (y := X2)
      (A := c₂ * cc / 4) (by positivity) hX1nn hX2nn hp2
    have heq : (c₂ * CC * κ) * (Real.sqrt X0 + Real.sqrt X1) * Real.sqrt X2
        = (c₂ * CC * κ) * (Real.sqrt X0 * Real.sqrt X2)
          + (c₂ * CC * κ) * (Real.sqrt X1 * Real.sqrt X2) := by ring
    rw [heq]
    linarith [hy0, hy1]
  have hE2norm : Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.E2hat f)
      ≤ κ * (Real.sqrt X0 + Real.sqrt X1) := by
    have h := hE2 f hf0
    rw [hNf, hN1] at h
    exact h
  have hcsE : c₂ * |IP (Work.FTS.CoercivityFix.E2hat f) (Work.Spaces.Dz f)|
      ≤ (c₂ * CC * κ) * (Real.sqrt X0 + Real.sqrt X1) * Real.sqrt X2 := by
    have h1 := hdata.cs (Work.FTS.CoercivityFix.E2hat f) (Work.Spaces.Dz f) hE2r hf2n
    have hnn : 0 ≤ κ * (Real.sqrt X0 + Real.sqrt X1) := by positivity
    have h3 : CC * Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.E2hat f)
          * Work.Spaces.HkNorm α n (Work.Spaces.Dz f)
        ≤ CC * (κ * (Real.sqrt X0 + Real.sqrt X1)) * Real.sqrt X2 := by
      rw [hN2]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hE2norm hdata.hCC.le) le_rfl
        (Real.sqrt_nonneg X2) (mul_nonneg hdata.hCC.le hnn)
    calc c₂ * |IP (Work.FTS.CoercivityFix.E2hat f) (Work.Spaces.Dz f)|
        ≤ c₂ * (CC * Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.E2hat f)
            * Work.Spaces.HkNorm α n (Work.Spaces.Dz f)) := mul_le_mul_of_nonneg_left h1 hc₂.le
      _ ≤ c₂ * (CC * (κ * (Real.sqrt X0 + Real.sqrt X1)) * Real.sqrt X2) :=
          mul_le_mul_of_nonneg_left h3 hc₂.le
      _ = (c₂ * CC * κ) * (Real.sqrt X0 + Real.sqrt X1) * Real.sqrt X2 := by ring
  have hEB : -(c₂ * IP (Work.FTS.CoercivityFix.E2hat f) (Work.Spaces.Dz f))
      ≤ cc / 4 * X0 + (c₁ * cc / 4) * X1 + (c₂ * cc / 2) * X2 := by
    have hle : - IP (Work.FTS.CoercivityFix.E2hat f) (Work.Spaces.Dz f)
        ≤ |IP (Work.FTS.CoercivityFix.E2hat f) (Work.Spaces.Dz f)| := neg_le_abs _
    have h := mul_le_mul_of_nonneg_left hle hc₂.le
    linarith [h, hcsE, hS]
  -- level-`n` coercivity of `𝓛̂` applied to `f`, `D_θ f`, `D_z f`
  have hRlow : cc * X0 + c₁ * (cc * X1) + c₂ * (cc * X2)
      - (cc / 4 * X0 + (c₁ * cc / 4) * X1 + (c₂ * cc / 2) * X2)
      ≤ IP (Work.FTS.CoercivityFix.Lhat f) f
        + c₁ * IP (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f)) (Work.Spaces.Dth f)
        + c₂ * (IP (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f)) (Work.Spaces.Dz f)
            + IP (Work.FTS.CoercivityFix.E2hat f) (Work.Spaces.Dz f)) := by
    have hc0 := hdata.coer f hf0
    have hc1 := hdata.coer (Work.Spaces.Dth f) hf1
    have hc2 := hdata.coer (Work.Spaces.Dz f) hf2
    rw [← hX0] at hc0
    rw [← hX1] at hc1
    rw [← hX2] at hc2
    have hc1' : c₁ * (cc * X1)
        ≤ c₁ * IP (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f)) (Work.Spaces.Dth f) :=
      mul_le_mul_of_nonneg_left hc1 hc₁.le
    have hc2' : c₂ * (cc * X2)
        ≤ c₂ * IP (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f)) (Work.Spaces.Dz f) :=
      mul_le_mul_of_nonneg_left hc2 hc₂.le
    have he : IP (Work.FTS.CoercivityFix.Lhat f) f
        + c₁ * IP (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f)) (Work.Spaces.Dth f)
        + c₂ * (IP (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f)) (Work.Spaces.Dz f)
            + IP (Work.FTS.CoercivityFix.E2hat f) (Work.Spaces.Dz f))
        = IP (Work.FTS.CoercivityFix.Lhat f) f
        + c₁ * IP (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f)) (Work.Spaces.Dth f)
        + c₂ * IP (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f)) (Work.Spaces.Dz f)
        + c₂ * IP (Work.FTS.CoercivityFix.E2hat f) (Work.Spaces.Dz f) := by ring
    rw [he]
    linarith [hc0, hc1', hc2', hEB]
  have hm1 : m ≤ 1 := by rw [hm]; exact min_le_left _ _
  have hmc₁ : m ≤ c₁ := by rw [hm]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hmc₂ : m ≤ c₂ := by rw [hm]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  -- the coefficient bookkeeping: what survives of the level-`n` coercivity dominates
  -- `(cc · min 1 (min c₁ c₂) / 2) · (X₀ + X₁ + X₂)`
  have hcoef : (cc * m / 2) * (X0 + X1 + X2)
      ≤ cc * X0 + c₁ * (cc * X1) + c₂ * (cc * X2)
        - (cc / 4 * X0 + (c₁ * cc / 4) * X1 + (c₂ * cc / 2) * X2) := by
    have e0 : (cc * m / 2) * X0 ≤ (3 * cc / 4) * X0 := by
      have h : m / 2 ≤ (3:ℝ) / 4 := by linarith
      calc (cc * m / 2) * X0 = cc * (m / 2) * X0 := by ring
        _ ≤ cc * ((3:ℝ) / 4) * X0 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h hdata.hcc.le) hX0nn
        _ = (3 * cc / 4) * X0 := by ring
    have e1 : (cc * m / 2) * X1 ≤ (3 * c₁ * cc / 4) * X1 := by
      have h : m / 2 ≤ 3 * c₁ / 4 := by linarith
      calc (cc * m / 2) * X1 = cc * (m / 2) * X1 := by ring
        _ ≤ cc * (3 * c₁ / 4) * X1 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h hdata.hcc.le) hX1nn
        _ = (3 * c₁ * cc / 4) * X1 := by ring
    have e2 : (cc * m / 2) * X2 ≤ (c₂ * cc / 2) * X2 := by
      have h : m / 2 ≤ c₂ / 2 := by linarith
      calc (cc * m / 2) * X2 = cc * (m / 2) * X2 := by ring
        _ ≤ cc * (c₂ / 2) * X2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h hdata.hcc.le) hX2nn
        _ = (c₂ * cc / 2) * X2 := by ring
    have hexp : (cc * m / 2) * (X0 + X1 + X2)
        = (cc * m / 2) * X0 + (cc * m / 2) * X1 + (cc * m / 2) * X2 := by ring
    have hexp2 : cc * X0 + c₁ * (cc * X1) + c₂ * (cc * X2)
          - (cc / 4 * X0 + (c₁ * cc / 4) * X1 + (c₂ * cc / 2) * X2)
        = (3 * cc / 4) * X0 + (3 * c₁ * cc / 4) * X1 + (c₂ * cc / 2) * X2 := by ring
    rw [hexp, hexp2]
    linarith [e0, e1, e2]
  -- the one-sided norm comparison, rescaled by `cc · min 1 (min c₁ c₂) / (2D)`
  have hYL : cc * m / (2 * D) * Y ≤ (cc * m / 2) * (X0 + X1 + X2) := by
    have hYD : Y ≤ D * (X0 + X1 + X2) := by
      rw [hY, hX0, hX1, hX2]
      exact hnormD f hf0
    have hcnonneg : 0 ≤ cc * m / (2 * D) := by
      have hp : 0 < cc * m :=
        mul_pos hdata.hcc (by rw [hm]; exact lt_min one_pos (lt_min hc₁ hc₂))
      positivity
    calc cc * m / (2 * D) * Y ≤ cc * m / (2 * D) * (D * (X0 + X1 + X2)) :=
          mul_le_mul_of_nonneg_left hYD hcnonneg
      _ = (cc * m / 2) * (X0 + X1 + X2) := by field_simp
  have hmain := le_trans hYL (le_trans hcoef hRlow)
  rw [Work.Coercivity.HkIPStep, e1, e2]
  exact hmain

/-! ## The induction step -/

theorem step2_data_ge_O (α : ℝ) (n : ℕ) (hα : 0 < α)
    {IP : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ} {cc CC κ c₁ c₂ D : ℝ}
    (hdata : Work.FTS.StrongEps.EpsE4Thr.CoerData2O α n IP cc CC)
    (hκ : 0 ≤ κ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hD : 0 < D)
    (hsmall : Work.FTS.CoercivityFix.StepSmall cc CC κ c₁ c₂)
    (hr : Work.FTS.StrongEps.EpsE4Thr.StepReg2O α n)
    (hc : Work.FTS.StrongEps.EpsE4Thr.Comm2O α n IP)
    (hE2 : ∀ f : Work.FTS.Galerkin.Fn, Work.FTS.StrongEps.EpsE4Thr.RegQo α (n + 1) f →
      Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.E2hat f)
        ≤ κ * (Work.Spaces.HkNorm α n f + Work.Spaces.HkNorm α n (Work.Spaces.Dth f)))
    (hnormD : ∀ f : Work.FTS.Galerkin.Fn, Work.FTS.StrongEps.EpsE4Thr.RegQo α (n + 1) f →
      Work.Spaces.HkSq α (n + 1) f
        ≤ D * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)
            + Work.Spaces.HkSq α n (Work.Spaces.Dz f))) :
    Work.FTS.StrongEps.EpsE4Thr.CoerData2O α (n + 1)
      (Work.Coercivity.HkIPStep c₁ c₂ IP)
      (cc * min 1 (min c₁ c₂) / (2 * D)) (3 * max 1 (max c₁ c₂) * CC) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the coercivity constant is positive
    have hmin : 0 < min 1 (min c₁ c₂) := lt_min one_pos (lt_min hc₁ hc₂)
    exact div_pos (mul_pos hdata.hcc hmin) (by positivity)
  · -- the Cauchy–Schwarz constant is positive
    exact mul_pos (mul_pos (by norm_num) (lt_of_lt_of_le one_pos (le_max_left _ _)))
      hdata.hCC
  · -- Cauchy–Schwarz: the three slots, each bounded through the level-`(n+1)` norm of `f`
    exact cs_clause_succ_O α hα n hdata.cs (le_of_lt hdata.hCC) hc₁ hc₂
  · -- coercivity of `𝓛̂`: the paper's arithmetic, with the `StepReg2O`-ports of `hr`
    exact coer_clause_succ_O α n hdata hκ hc₁ hc₂ hD hsmall hr hc hE2 hnormD

end Work.FTS.StrongEps.EpsE4Thr
