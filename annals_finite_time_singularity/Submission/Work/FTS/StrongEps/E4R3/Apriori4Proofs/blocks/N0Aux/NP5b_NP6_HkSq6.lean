import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.Maj6Split
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.N0row_defs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.N0PieceHelpers
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12Sup4
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12Sup6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.c2mJets
import Submission.Work.FTS.StrongPersist.L3Rhs.c2m_mul_HkSq_le
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.HkMem_radial_mul6
import Submission.Work.FTS.StrongPersist.H6Aux.Facts
import Submission.Work.FTS.StrongEps.HkSq_const_mul
import Submission.Work.FTS.OpenPkg.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The `α`-uniform jet bound of the radial factor `L₁₂(F_*)`

`H6N0Aux.nzl12Fstar_zop` bounds the `Zop`-iterates of `L₁₂(F_*)` by `(2α/3)·K₃ + 1`, a constant
which the proof obtains for a *fixed* `α`.  The level-six estimate of `NP6` needs one constant
that works for **every** `α ∈ (0,1]`: since `L₁₂(F_*) = 2α/(1+z)` on `(0,∞)` and only the factor
`α ≤ 1` matters, the same argument gives the `α`-free constant `(2/3)·K₃ + 1`. -/
theorem l12Fstar_dzdIter_uniform :
    ∃ Kφ : ℝ, 0 < Kφ ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∀ b : ℕ, b ≤ 6 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter b (fun y => Work.Construction.L12 (Work.Construction.Fstar α) y) z|
        ≤ Kφ := by
  obtain ⟨K3, hK3pos, hK3⟩ := Work.FTS.StrongPersist.L6Aux.PhiZopBound6
  refine ⟨(2 / 3) * K3 + 1, by linarith, ?_⟩
  intro α hαI b hb z hz
  have hα0 : 0 < α := hαI.1
  have hα1 : α ≤ 1 := hαI.2
  have hcongr : Work.Elliptic.DzdIter b
        (fun y => Work.Construction.L12 (Work.Construction.Fstar α) y) z
      = Work.Elliptic.DzdIter b (fun y => 2 * α / (1 + y)) z :=
    Work.FTS.StrongPersist.DzdIter_congr_Ioi
      (fun y hy => Work.Construction.L12_Fstar_eq hα0 hα1 hy.le) b z hz
  rw [hcongr, ← Work.FTS.StrongPersist.H6Pair6Aux.Zop_iter_eq_DzdIter]
  rw [show (fun y : ℝ => 2 * α / (1 + y))
      = fun y : ℝ => (2 * α / 3) * (3 / (1 + y)) from by
    funext y; ring]
  rw [Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.nzZop_iter_const_mul]
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * α / 3)]
  have h := hK3 b hb z (le_of_lt hz)
  have hmono : (2 * α / 3) * |Work.Spaces.Zop^[b] (fun z => 3 / (1 + z)) z|
      ≤ (2 * α / 3) * K3 := mul_le_mul_of_nonneg_left h (by positivity)
  have hstep : (2 * α / 3) * K3 ≤ (2 / 3) * K3 := by nlinarith
  linarith [hmono, hstep]

/-!
Route hint.  `NP5b α w = (-1) • (c₂ₘ(θ) · (Lᵢ·D_z w))` and `NP6 α w = (-1) • (c₂ₘ(θ) · (L⋆·D_z w))`
with `Lᵢ z = L₁₂ w z` and `L⋆ z = L₁₂ (F_* α) z` (radial).  Use
`L3Rhs.ang_mul_HkSq_le 6` with `a := Work.Construction.c2m` (its hypotheses: `SmoothOpen` of
the angular profile, `|c2m| ≤ Cc` on `Iθ`, and `|D_θ^i c2m| ≤ Cc·sin(2θ)` for `1 ≤ i ≤ 6`; all
three are the bundle `H6Pair6Aux.T5bAux.c2mJets`), which reduces the claim to
`HkMem α 6 (L·D_z w)` (obtain it with `H6Rows.N0pair6Aux.HkMem_radial_mul6` for `NP5b`, and for
`NP6` with the same tool applied to the *bounded* radial factor `L⋆` — its jets are bounded by
a constant independent of α, see `H6Pair6Aux.H6N0Aux.nzl12Fstar_zop`).
Then the engine `Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.radialMaj6_split` at `X := L`,
`f := D_z w` gives `HkSq α 6 (L·D_z w) ≤ C (Blo² HkSq α 6 (D_z w) + Bhi² HkSq α 2 (D_z w))`,
with `Blo := CL4·Xn α w ≤ CL4·C₀·α²` (`L12Sup4`; for `NP6` take the constant jet bound `Kφ`
instead) and `Bhi := CL6·HkNorm α 6 w` (`L12Sup6`).  Finish with
`HkSq α 6 (D_z w) ≤ HkSq α 7 w`, `HkSq α 2 (D_z w) ≤ HkSq α 3 w ≤ HkSq α 4 w = (Xn α w)² ≤ C₀²α⁴`
(`H6Aux.HkSq_Dz_le_succ'`, `H6Aux.HkSq_mono_order`) and `HkSq_const_mul` for the scalar `-1`.

Note on the exact bracketing used here: the angular factor `c₂ₘ` is *commuted past* the radial
factor, so the engine is applied to `X z = L(z)` and the honest (angular × `D_z w`) field
`f z θ = -c₂ₘ(θ)·D_z w(z,θ)`.  This is what makes `SmoothOpen f` (needed by `ang_mul_HkSq_le`)
available from the open-quadrant smoothness of `w` alone: the radial factor `z ↦ L₁₂ w z` is
a priori only `C⁶` on `(0,∞)` (its `C^k`-regularity is bought with `HkMem α k w`, and the class
supplies that only up to `k = 10`).  The price is that the level-`2` angular estimate must be
run separately, at level `2`, where the small factor `|D_z w|_{ℋ²} ≤ C₀²` is available.
-/
theorem NP5b_NP6_HkSq6 : ∀ C₀ : ℝ, ∃ K : ℝ, 0 < K ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ w : Work.FTS.Galerkin.Fn,
    Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
    Work.Spaces.HkSq α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NP5b α w)
        ≤ K * (1 + Work.Spaces.HkSq α 7 w) ∧
    Work.Spaces.HkSq α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NP6 α w)
        ≤ K * (1 + Work.Spaces.HkSq α 7 w) := by
  obtain ⟨Cmaj, hCmajpos, hCmaj⟩ :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.radialMaj6_split
  obtain ⟨Cang, hCangpos, hCang⟩ := Work.FTS.StrongPersist.L3Rhs.ang_mul_HkSq_le 6
  obtain ⟨Cang2, hCang2pos, hCang2⟩ := Work.FTS.StrongPersist.L3Rhs.ang_mul_HkSq_le 2
  obtain ⟨Cc, hCcpos, hCcsm, hCcabs, hCcjet⟩ :=
    Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.c2mJets
  obtain ⟨CL4, hCL4pos, hCL4⟩ := Work.FTS.StrongPersist.H6Pair6Aux.L12Sup4
  obtain ⟨CL6, hCL6pos, hCL6⟩ := Work.FTS.StrongPersist.H6Pair6Aux.L12Sup6
  obtain ⟨Kφ, hKφpos, hKφ⟩ := l12Fstar_dzdIter_uniform
  intro C₀
  have hKbpos : 0 < Cmaj * Cc ^ 2 * (CL4 ^ 2 * Cang + CL6 ^ 2 * Cang2) * C₀ ^ 2 + 1 := by
    have h : 0 ≤ Cmaj * Cc ^ 2 * (CL4 ^ 2 * Cang + CL6 ^ 2 * Cang2) * C₀ ^ 2 := by positivity
    linarith
  refine ⟨max (Cmaj * Cc ^ 2 * (CL4 ^ 2 * Cang + CL6 ^ 2 * Cang2) * C₀ ^ 2 + 1)
    (Cmaj * Kφ ^ 2 * Cc ^ 2 * (Cang + Cang2 * C₀ ^ 2) + 1), lt_max_of_lt_left hKbpos, ?_⟩
  intro α hαI w hcls hXw
  have hα0 : 0 < α := hαI.1
  have hα1 : α ≤ 1 := hαI.2
  have hsmw : Work.FTS.EllipticEst.SmoothOpen w := hcls.reg
  have hm7 : Work.Spaces.HkMem α 7 w := hcls.mem
  have hm6 : Work.Spaces.HkMem α 6 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hsmw 6 (by norm_num) hm7
  have hm4 : Work.Spaces.HkMem α 4 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hsmw 4 (by norm_num) hm7
  have hL12zero : Work.Construction.L12 w 0 = 0 := hcls.l12
  have hsmDz : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz w) := hsmw.Dz
  have hm6Dz : Work.Spaces.HkMem α 6 (Work.Spaces.Dz w) :=
    Work.FTS.EllipticEst.UopHk.HkMem_Dz_of_smoothOpen α 6 hsmw hm7
  have hm2Dz : Work.Spaces.HkMem α 2 (Work.Spaces.Dz w) :=
    Work.FTS.OpenPkg.HkMem_mono_open hsmDz 2 (by norm_num) hm6Dz
  have hm3 : Work.Spaces.HkMem α 3 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hsmw 3 (by norm_num) hm7
  -- the side bounds on `D_z w`
  have hS6 : Work.Spaces.HkSq α 6 (Work.Spaces.Dz w) ≤ Work.Spaces.HkSq α 7 w :=
    Work.FTS.StrongPersist.H6Aux.HkSq_Dz_le_succ' α 6 hsmw hm7
  have hS2a : Work.Spaces.HkSq α 2 (Work.Spaces.Dz w) ≤ Work.Spaces.HkSq α 3 w :=
    Work.FTS.StrongPersist.H6Aux.HkSq_Dz_le_succ' α 2 hsmw hm3
  have h34 : Work.Spaces.HkSq α 3 w ≤ Work.Spaces.HkSq α 4 w :=
    Work.FTS.StrongPersist.H6Aux.HkSq_mono_order α (by norm_num) hm4
  have h4eq : Work.Spaces.HkSq α 4 w = (Work.FTS.Nonlin.Xn α w) ^ 2 := by
    change Work.Spaces.HkSq α 4 w = (Work.Spaces.HkNorm α 4 w) ^ 2
    rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 w)]
  have hx2 : (Work.FTS.Nonlin.Xn α w) ^ 2 ≤ C₀ ^ 2 * α ^ 4 := by
    have h0 : 0 ≤ Work.FTS.Nonlin.Xn α w := Work.Spaces.HkNorm_nonneg α 4 w
    calc (Work.FTS.Nonlin.Xn α w) ^ 2 ≤ (C₀ * α ^ 2) ^ 2 := pow_le_pow_left₀ h0 hXw 2
      _ = C₀ ^ 2 * α ^ 4 := by ring
  have hα4le : α ^ 4 ≤ 1 := pow_le_one₀ hα0.le hα1
  have hx2' : (Work.FTS.Nonlin.Xn α w) ^ 2 ≤ C₀ ^ 2 :=
    hx2.trans (by simpa using mul_le_of_le_one_right (sq_nonneg C₀) hα4le)
  have hS2 : Work.Spaces.HkSq α 2 (Work.Spaces.Dz w) ≤ C₀ ^ 2 := by
    have h : Work.Spaces.HkSq α 3 w ≤ (Work.FTS.Nonlin.Xn α w) ^ 2 := by
      rw [← h4eq]; exact h34
    exact hS2a.trans (h.trans hx2')
  -- the angular profile `c₂ₘ`
  have hCcjet6 : ∀ i : ℕ, 1 ≤ i → i ≤ 6 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun x (θ' : ℝ) => Work.Construction.c2m θ') 0 θ|
        ≤ Cc * Real.sin (2 * θ) :=
    fun i hi1 hi6 θ hθ => hCcjet i hi1 (by omega) 0 θ hθ
  have hCcjet2 : ∀ i : ℕ, 1 ≤ i → i ≤ 2 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun x (θ' : ℝ) => Work.Construction.c2m θ') 0 θ|
        ≤ Cc * Real.sin (2 * θ) :=
    fun i hi1 hi2 θ hθ => hCcjet i hi1 (by omega) 0 θ hθ
  -- the angular factor, at levels `6` and `2`
  obtain ⟨hfa_mem, hfa_bd⟩ := hCang α hα0 hα1 Work.Construction.c2m Cc hCcpos hCcsm hCcabs
    hCcjet6 (Work.Spaces.Dz w) hsmDz hm6Dz
  obtain ⟨-, hfb_bd⟩ := hCang2 α hα0 hα1 Work.Construction.c2m Cc hCcpos hCcsm hCcabs
    hCcjet2 (Work.Spaces.Dz w) hsmDz hm2Dz
  set f : ℝ → ℝ → ℝ := fun z θ => (-1) * (Work.Construction.c2m θ * Work.Spaces.Dz w z θ)
    with hfdef
  have hfsm : Work.FTS.EllipticEst.SmoothOpen f := by
    rw [hfdef]
    exact Work.FTS.StrongPersist.H6Pair6Aux.so_const_mul (-1)
      (Work.FTS.StrongPersist.H6Pair6Aux.so_mul
        (Work.FTS.StrongPersist.H6Pair6Aux.so_snd Work.FTS.StrongPersist.H6Pair6Aux.contDiff_c2m)
        hsmDz)
  have hfmem : Work.Spaces.HkMem α 6 f := by
    rw [hfdef]
    exact Work.FTS.LocData.HkMem_const_mul α 6 (-1) hfa_mem
  have hS6f : Work.Spaces.HkSq α 6 f ≤ Cang * Cc ^ 2 * Work.Spaces.HkSq α 7 w := by
    have hval : Work.Spaces.HkSq α 6 f
        = Work.Spaces.HkSq α 6 (fun z θ => Work.Construction.c2m θ * Work.Spaces.Dz w z θ) := by
      rw [hfdef, Work.FTS.StrongEps.HkSq_const_mul]
      ring
    rw [hval]
    exact hfa_bd.trans (mul_le_mul_of_nonneg_left hS6 (by positivity))
  have hS2f : Work.Spaces.HkSq α 2 f ≤ Cang2 * Cc ^ 2 * C₀ ^ 2 := by
    have hval : Work.Spaces.HkSq α 2 f
        = Work.Spaces.HkSq α 2 (fun z θ => Work.Construction.c2m θ * Work.Spaces.Dz w z θ) := by
      rw [hfdef, Work.FTS.StrongEps.HkSq_const_mul]
      ring
    rw [hval]
    exact hfb_bd.trans (mul_le_mul_of_nonneg_left hS2 (by positivity))
  -- smoothness of the radial factor `z ↦ L₁₂(w)(z)`
  have hL12cd10 : ContDiffOn ℝ 10 (fun z => Work.Construction.L12 w z) (Set.Ioi 0) := by
    have h := Work.FTS.EllipticEst.UopHk.contDiffOn_L12_k α 10 w hα0 hα1 hsmw hcls.mem10
      (by norm_num)
    refine h.congr (fun z _ => ?_)
    exact congrFun (Work.FTS.H2.constructionL12_eq_ellipticL12 w) z
  have hL12cd6 : ContDiffOn ℝ 6 (fun z => Work.Construction.L12 w z) (Set.Ioi 0) :=
    hL12cd10.of_le (by exact_mod_cast (by norm_num : 6 ≤ 10))
  have hnn7 : 0 ≤ Work.Spaces.HkSq α 7 w := Work.Spaces.HkSq_nonneg α 7 w
  have hB6eq : (Work.Spaces.HkNorm α 6 w) ^ 2 = Work.Spaces.HkSq α 6 w := by
    rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 w)]
  have h67 : Work.Spaces.HkSq α 6 w ≤ Work.Spaces.HkSq α 7 w :=
    Work.FTS.StrongPersist.H6Aux.HkSq_mono_order α (by norm_num) hm7
  have hBlon : 0 ≤ CL4 * Work.FTS.Nonlin.Xn α w :=
    mul_nonneg hCL4pos.le (Work.Spaces.HkNorm_nonneg α 4 w)
  have hBhin : 0 ≤ CL6 * Work.Spaces.HkNorm α 6 w :=
    mul_nonneg hCL6pos.le (Work.Spaces.HkNorm_nonneg α 6 w)
  have hLo6 : ∀ j : ℕ, j ≤ 4 → ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 w z) z|
        ≤ CL4 * Work.FTS.Nonlin.Xn α w :=
    fun j hj z hz => hCL4 α w hα0 hα1 hsmw hm6 hL12zero j hj z hz
  have hHi6 : ∀ j : ℕ, j ≤ 6 → ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 w z) z|
        ≤ CL6 * Work.Spaces.HkNorm α 6 w :=
    fun j hj z hz => hCL6 α w hα0 hα1 hsmw hm6 hm7 hL12zero j hj z hz
  constructor
  · -- ## `NP5b`
    have heq : Work.FTS.StrongPersist.H6Pair6Aux.NP5b α w
        = fun z θ => (fun z => Work.Construction.L12 w z) z * f z θ := by
      rw [hfdef]
      funext z θ
      simp only [Work.FTS.StrongPersist.H6Pair6Aux.NP5b]
      ring
    have hmain := hCmaj α (fun z => Work.Construction.L12 w z) f
      (CL4 * Work.FTS.Nonlin.Xn α w) (CL6 * Work.Spaces.HkNorm α 6 w)
      hL12cd6 hfsm hfmem hBlon hBhin hLo6 hHi6
    have hfin : Work.Spaces.HkSq α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NP5b α w)
        ≤ (Cmaj * Cc ^ 2 * (CL4 ^ 2 * Cang + CL6 ^ 2 * Cang2) * C₀ ^ 2 + 1)
            * (1 + Work.Spaces.HkSq α 7 w) := by
      have hstep : (CL4 * Work.FTS.Nonlin.Xn α w) ^ 2 * Work.Spaces.HkSq α 6 f
          + (CL6 * Work.Spaces.HkNorm α 6 w) ^ 2 * Work.Spaces.HkSq α 2 f
          ≤ (CL4 ^ 2 * Cang + CL6 ^ 2 * Cang2) * Cc ^ 2 * C₀ ^ 2
              * Work.Spaces.HkSq α 7 w := by
        have t1 : (CL4 * Work.FTS.Nonlin.Xn α w) ^ 2 * Work.Spaces.HkSq α 6 f
            ≤ CL4 ^ 2 * (Cang * Cc ^ 2 * Work.Spaces.HkSq α 7 w) * C₀ ^ 2 := by
          have hmul := mul_le_mul (mul_le_mul_of_nonneg_left hx2' (sq_nonneg CL4)) hS6f
            (Work.Spaces.HkSq_nonneg α 6 f) (mul_nonneg (sq_nonneg CL4) (sq_nonneg C₀))
          calc (CL4 * Work.FTS.Nonlin.Xn α w) ^ 2 * Work.Spaces.HkSq α 6 f
              = (CL4 ^ 2 * (Work.FTS.Nonlin.Xn α w) ^ 2) * Work.Spaces.HkSq α 6 f := by ring
            _ ≤ (CL4 ^ 2 * C₀ ^ 2) * (Cang * Cc ^ 2 * Work.Spaces.HkSq α 7 w) := hmul
            _ = CL4 ^ 2 * (Cang * Cc ^ 2 * Work.Spaces.HkSq α 7 w) * C₀ ^ 2 := by ring
        have t2 : (CL6 * Work.Spaces.HkNorm α 6 w) ^ 2 * Work.Spaces.HkSq α 2 f
            ≤ CL6 ^ 2 * (Cang2 * Cc ^ 2 * C₀ ^ 2) * Work.Spaces.HkSq α 7 w := by
          rw [mul_pow, hB6eq]
          have hmul := mul_le_mul (mul_le_mul_of_nonneg_left h67 (sq_nonneg CL6)) hS2f
            (Work.Spaces.HkSq_nonneg α 2 f) (mul_nonneg (sq_nonneg CL6) hnn7)
          calc CL6 ^ 2 * Work.Spaces.HkSq α 6 w * Work.Spaces.HkSq α 2 f
              ≤ (CL6 ^ 2 * Work.Spaces.HkSq α 7 w) * (Cang2 * Cc ^ 2 * C₀ ^ 2) := hmul
            _ = CL6 ^ 2 * (Cang2 * Cc ^ 2 * C₀ ^ 2) * Work.Spaces.HkSq α 7 w := by ring
        have hsum := add_le_add t1 t2
        have hnn1 : 0 ≤ CL4 ^ 2 * (Cang * Cc ^ 2 * Work.Spaces.HkSq α 7 w) * C₀ ^ 2 := by
          positivity
        have hnn2 : 0 ≤ CL6 ^ 2 * (Cang2 * Cc ^ 2 * C₀ ^ 2) * Work.Spaces.HkSq α 7 w := by
          positivity
        nlinarith [hsum, hnn1, hnn2]
      have hlast : Cmaj * ((CL4 ^ 2 * Cang + CL6 ^ 2 * Cang2) * Cc ^ 2 * C₀ ^ 2
            * Work.Spaces.HkSq α 7 w)
          ≤ (Cmaj * Cc ^ 2 * (CL4 ^ 2 * Cang + CL6 ^ 2 * Cang2) * C₀ ^ 2 + 1)
            * (1 + Work.Spaces.HkSq α 7 w) := by
        have hcoef : 0 ≤ Cmaj * Cc ^ 2 * (CL4 ^ 2 * Cang + CL6 ^ 2 * Cang2) * C₀ ^ 2 := by
          positivity
        nlinarith [hcoef, hnn7]
      calc Work.Spaces.HkSq α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NP5b α w)
          = Work.Spaces.HkSq α 6 (fun z θ => (fun z => Work.Construction.L12 w z) z * f z θ) :=
            by rw [heq]
        _ ≤ Cmaj * ((CL4 * Work.FTS.Nonlin.Xn α w) ^ 2 * Work.Spaces.HkSq α 6 f
              + (CL6 * Work.Spaces.HkNorm α 6 w) ^ 2 * Work.Spaces.HkSq α 2 f) := hmain
        _ ≤ Cmaj * ((CL4 ^ 2 * Cang + CL6 ^ 2 * Cang2) * Cc ^ 2 * C₀ ^ 2
              * Work.Spaces.HkSq α 7 w) := mul_le_mul_of_nonneg_left hstep hCmajpos.le
        _ ≤ _ := hlast
    exact hfin.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith [hnn7]))
  · -- ## `NP6`
    have heq6 : Work.FTS.StrongPersist.H6Pair6Aux.NP6 α w
        = fun z θ =>
            (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) z * f z θ := by
      rw [hfdef]
      funext z θ
      simp only [Work.FTS.StrongPersist.H6Pair6Aux.NP6,
        Work.FTS.StrongPersist.H6Pair6Aux.NA6]
      ring
    have hFjet : ∀ j : ℕ, j ≤ 6 → ∀ z ∈ Set.Ioi (0 : ℝ),
        |Work.Elliptic.DzdIter j
          (fun y => Work.Construction.L12 (Work.Construction.Fstar α) y) z| ≤ Kφ :=
      fun j hj z hz => hKφ α hαI j hj z hz
    have hFjet4 : ∀ j : ℕ, j ≤ 4 → ∀ z ∈ Set.Ioi (0 : ℝ),
        |Work.Elliptic.DzdIter j
          (fun y => Work.Construction.L12 (Work.Construction.Fstar α) y) z| ≤ Kφ :=
      fun j hj z hz => hKφ α hαI j (by omega) z hz
    have hL12Fcd : ∀ n : ℕ,
        ContDiffOn ℝ n (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z)
          (Set.Ioi 0) := by
      intro n
      have hnum : ContDiffOn ℝ n (fun _ : ℝ => 2 * α) (Set.Ioi 0) := contDiffOn_const
      have hden : ContDiffOn ℝ n (fun z : ℝ => 1 + z) (Set.Ioi 0) :=
        (contDiffOn_const (c := (1 : ℝ)) (s := Set.Ioi 0)).add contDiffOn_id
      have hbase : ContDiffOn ℝ n (fun z : ℝ => 2 * α / (1 + z)) (Set.Ioi 0) :=
        hnum.div hden (fun z hz => by
          have hz' : (0 : ℝ) < 1 + z := by linarith [Set.mem_Ioi.mp hz]
          positivity)
      exact hbase.congr (fun z hz =>
        Work.Construction.L12_Fstar_eq hα0 hα1 (le_of_lt (Set.mem_Ioi.mp hz)))
    have hL12Fcd6 : ContDiffOn ℝ 6
        (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) (Set.Ioi 0) :=
      hL12Fcd 6
    have hmain6 := hCmaj α (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) f
      Kφ Kφ hL12Fcd6 hfsm hfmem hKφpos.le hKφpos.le hFjet4 hFjet
    have hfin6 : Work.Spaces.HkSq α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NP6 α w)
        ≤ (Cmaj * Kφ ^ 2 * Cc ^ 2 * (Cang + Cang2 * C₀ ^ 2) + 1)
            * (1 + Work.Spaces.HkSq α 7 w) := by
      have hstep6 : Kφ ^ 2 * Work.Spaces.HkSq α 6 f + Kφ ^ 2 * Work.Spaces.HkSq α 2 f
          ≤ Kφ ^ 2 * Cc ^ 2 * (Cang + Cang2 * C₀ ^ 2)
              * (1 + Work.Spaces.HkSq α 7 w) := by
        have h1 : Kφ ^ 2 * Work.Spaces.HkSq α 6 f
            ≤ Kφ ^ 2 * (Cang * Cc ^ 2 * Work.Spaces.HkSq α 7 w) :=
          mul_le_mul_of_nonneg_left hS6f (by positivity)
        have h2 : Kφ ^ 2 * Work.Spaces.HkSq α 2 f ≤ Kφ ^ 2 * (Cang2 * Cc ^ 2 * C₀ ^ 2) :=
          mul_le_mul_of_nonneg_left hS2f (by positivity)
        have hnn1 : 0 ≤ Kφ ^ 2 * Cc ^ 2 * Cang := by positivity
        have hnn2 : 0 ≤ Kφ ^ 2 * Cc ^ 2 * Cang2 * C₀ ^ 2 * Work.Spaces.HkSq α 7 w := by
          positivity
        nlinarith [h1, h2, hnn1, hnn2]
      have hlast : Cmaj * (Kφ ^ 2 * Cc ^ 2 * (Cang + Cang2 * C₀ ^ 2)
            * (1 + Work.Spaces.HkSq α 7 w))
          ≤ (Cmaj * Kφ ^ 2 * Cc ^ 2 * (Cang + Cang2 * C₀ ^ 2) + 1)
            * (1 + Work.Spaces.HkSq α 7 w) := by
        have hcoef : 0 ≤ Cmaj * Kφ ^ 2 * Cc ^ 2 * (Cang + Cang2 * C₀ ^ 2) := by positivity
        nlinarith [hcoef, hnn7]
      calc Work.Spaces.HkSq α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NP6 α w)
          = Work.Spaces.HkSq α 6 (fun z θ =>
              (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) z * f z θ) :=
            by rw [heq6]
        _ ≤ Cmaj * (Kφ ^ 2 * Work.Spaces.HkSq α 6 f
              + Kφ ^ 2 * Work.Spaces.HkSq α 2 f) := hmain6
        _ ≤ Cmaj * (Kφ ^ 2 * Cc ^ 2 * (Cang + Cang2 * C₀ ^ 2)
              * (1 + Work.Spaces.HkSq α 7 w)) := mul_le_mul_of_nonneg_left hstep6 hCmajpos.le
        _ ≤ _ := hlast
    exact hfin6.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith [hnn7]))

end

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux
