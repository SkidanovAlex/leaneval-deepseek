import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.Defs
import Submission.Work.FTS.StrongPersist.H6Rows.AK6Row
import Submission.Work.FTS.StrongEps.E4R3.RawE6Aux.bdata_blkLin
import Submission.Work.FTS.StrongEps.E4R3.RawE6Aux.EpsWPSemitameAux.BlkMu
import Submission.Work.FTS.StrongEps.E4R3.RawE6Aux.EpsWPSemitameAux.BlkNstar
import Submission.Work.FTS.StrongEps.E4R3.RawE6Aux.EpsWPSemitameAux.Assembly
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.L6Ctx_JfamP_proof
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0_BData
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_BData

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-!
# `epsWP_semitame_proof` — the semi-tame size of the projected right-hand side

The target is the level-`6` semi-tame estimate of the pre-mollified right-hand side
`epsWP α ρ ε Φs E g τ` of the projected scheme.  Everything happens on the projected slice
`w = slice (JfamP ρ ε g) τ`: by `epsWP_eq_epsWBlk`, `epsWP … = epsWBlk α Φs w (E w) μ lam` with
`μ = muBlk α Φs w (E w)` and `lam = lamfun μ`, both bounded by `MuLamOK`.

Each of the five blocks of `epsWBlk` supplies `BData` (see `blocks/`), and the assembly
`semitame_blk_of_blocks` turns the five `BData`'s into the three conjuncts.
-/

/-- `√(1+x) ≤ 1 + √x` for `x ≥ 0`. -/
theorem sqrt_one_add_le {x : ℝ} (hx : 0 ≤ x) : Real.sqrt (1 + x) ≤ 1 + Real.sqrt x := by
  have hnn : 0 ≤ 1 + Real.sqrt x := by linarith [Real.sqrt_nonneg x]
  rw [← Real.sqrt_sq hnn]
  refine Real.sqrt_le_sqrt ?_
  have hsq : (1 + Real.sqrt x) ^ 2 = 1 + 2 * Real.sqrt x + x := by
    rw [add_sq, one_pow, Real.sq_sqrt hx]; ring
  rw [hsq]
  linarith [Real.sqrt_nonneg x]

/-- `√(a+b) ≤ √a + √b` for `a, b ≥ 0`. -/
theorem sqrt_add_le' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have hnn : 0 ≤ Real.sqrt a + Real.sqrt b := by
    linarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]
  rw [← Real.sqrt_sq hnn]
  refine Real.sqrt_le_sqrt ?_
  have hsq : (Real.sqrt a + Real.sqrt b) ^ 2 = a + 2 * (Real.sqrt a * Real.sqrt b) + b := by
    rw [add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]; ring
  rw [hsq]
  have h2 : 0 ≤ 2 * (Real.sqrt a * Real.sqrt b) := by positivity
  linarith

/-- **The assembly.**  If the five blocks of `epsWBlk` satisfy `BData` with constants
`KL, KM, K0, KN, KS`, then `epsWBlk` itself satisfies the three conjuncts of the semi-tame
estimate with the single constant `√(16·(KL+KM+K0+KN+KS+1)) + 1`. -/
theorem semitame_blk_of_blocks {C₀ Ce Cs α : ℝ} (hα : α ∈ Set.Ioc 0 1)
    {KL KM K0 KN KS : ℝ} (hKL : 0 < KL) (hKM : 0 < KM) (hK0 : 0 < K0) (hKN : 0 < KN)
    (hKS : 0 < KS)
    (hL : ∀ {w : Fn}, Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      BData α w KL (blkLin α w))
    (hM : ∀ {Φs w Φg : Fn}, Work.FTS.ClassC.ClassC α w →
      Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 → Work.FTS.VocabO.EllPkgGo α Ce w Φg →
      Work.FTS.ClassC.EllPkgK α 6 Ce w Φg → Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
      BData α w KM (blkMu α Φs w Φg))
    (h0 : ∀ {w : Fn}, Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      BData α w K0 (blkN0 α w))
    (hN : ∀ {Φs w Φg : Fn}, Work.FTS.ClassC.ClassC α w →
      Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 → Work.FTS.VocabO.EllPkgGo α Ce w Φg →
      Work.FTS.ClassC.EllPkgK α 6 Ce w Φg → Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
      BData α w KN (blkN α Φs w Φg))
    (hS : ∀ {w : Fn} {μ lam : ℝ}, Work.FTS.ClassC.ClassC α w →
      Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 → |μ| ≤ 1 / 2 → |lam| ≤ 1 →
      BData α w KS (blkNstar w μ lam)) :
    ∀ {Φs w Φg : Fn} {μ lam : ℝ}, Work.FTS.ClassC.ClassC α w →
      Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 → |μ| ≤ 1 / 2 → |lam| ≤ 1 →
      Work.FTS.VocabO.EllPkgGo α Ce w Φg → Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
      Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
      Work.FTS.VocabO.HQo α 6 (epsWBlk α Φs w Φg μ lam) ∧
      Work.Spaces.HkNorm α 4 (epsWBlk α Φs w Φg μ lam)
          ≤ (Real.sqrt (16 * (KL + KM + K0 + KN + KS + 1)) + 1)
            * (1 + Work.Spaces.HkNorm α 5 w) ∧
      Work.Spaces.HkNorm α 6 (epsWBlk α Φs w Φg μ lam)
          ≤ (Real.sqrt (16 * (KL + KM + K0 + KN + KS + 1)) + 1)
              * (1 + Work.Spaces.HkNorm α 7 w)
            + (Real.sqrt (16 * (KL + KM + K0 + KN + KS + 1)) + 1)
              * (1 + Work.Spaces.HkNorm α 6 w) ^ 2 := by
  set Ktot : ℝ := KL + KM + K0 + KN + KS + 1 with hKtot
  have hKtot0 : 0 < Ktot := by rw [hKtot]; linarith
  set C : ℝ := Real.sqrt (16 * Ktot) + 1 with hC
  have hCsq : Real.sqrt (16 * Ktot) ≤ C := by rw [hC]; linarith [Real.sqrt_nonneg (16 * Ktot)]
  intro Φs w Φg μ lam hcls hXw hμ hlam hgo hK hstar
  have hα0 : 0 < α := hα.1
  -- the five signed summands
  set A1 : Fn := fun z θ => - blkLin α w z θ with hA1
  set A2 : Fn := fun z θ => - blkMu α Φs w Φg z θ with hA2
  set A3 : Fn := blkN0 α w with hA3
  set A4 : Fn := blkN α Φs w Φg with hA4
  set A5 : Fn := blkNstar w μ lam with hA5
  have hsum : epsWBlk α Φs w Φg μ lam = sum5 A1 A2 A3 A4 A5 := by
    rw [epsWBlk_eq_sum5, ← hA1, ← hA2, ← hA3, ← hA4, ← hA5]
  have eL : BData α w KL A1 := by rw [hA1]; exact (hL hcls hXw).neg
  have eM : BData α w KM A2 := by rw [hA2]; exact (hM hcls hXw hgo hK hstar).neg
  have e0 : BData α w K0 A3 := by rw [hA3]; exact h0 hcls hXw
  have eN : BData α w KN A4 := by rw [hA4]; exact hN hcls hXw hgo hK hstar
  have eS : BData α w KS A5 := by rw [hA5]; exact hS hcls hXw hμ hlam
  have hm6 : Work.Spaces.HkMem α 6 (epsWBlk α Φs w Φg μ lam) := by
    rw [hsum]
    exact hkMem_sum5 eL.sm eM.sm e0.sm eN.sm eS.sm eL.hm eM.hm e0.hm eN.hm eS.hm
  have hsm : Work.FTS.EllipticEst.SmoothOpen (epsWBlk α Φs w Φg μ lam) := by
    rw [hsum]
    exact smoothOpen_sum5 eL.sm eM.sm e0.sm eN.sm eS.sm
  have m4 : ∀ {B : Fn}, Work.FTS.EllipticEst.SmoothOpen B → Work.Spaces.HkMem α 6 B →
      Work.Spaces.HkMem α 4 B := fun hs hm =>
    Work.FTS.OpenPkg.HkMem_mono_open hs 4 (by norm_num) hm
  have hsq4 : Work.Spaces.HkSq α 4 (epsWBlk α Φs w Φg μ lam)
      ≤ 16 * Ktot * (1 + Work.Spaces.HkSq α 5 w) := by
    rw [hsum]
    have hs := hkSq_sum5 hα0 eL.sm eM.sm e0.sm eN.sm eS.sm
      (m4 eL.sm eL.hm) (m4 eM.sm eM.hm) (m4 e0.sm e0.hm) (m4 eN.sm eN.hm) (m4 eS.sm eS.hm)
    have hS5 := Work.Spaces.HkSq_nonneg α 5 w
    have hbound : Work.Spaces.HkSq α 4 A1 + Work.Spaces.HkSq α 4 A2 + Work.Spaces.HkSq α 4 A3
        + Work.Spaces.HkSq α 4 A4 + Work.Spaces.HkSq α 4 A5
        ≤ Ktot * (1 + Work.Spaces.HkSq α 5 w) := by
      rw [hKtot]
      nlinarith [eL.b4, eM.b4, e0.b4, eN.b4, eS.b4, hS5, hKL, hKM, hK0, hKN, hKS]
    calc Work.Spaces.HkSq α 4 (sum5 A1 A2 A3 A4 A5)
        ≤ 16 * (Work.Spaces.HkSq α 4 A1 + Work.Spaces.HkSq α 4 A2 + Work.Spaces.HkSq α 4 A3
            + Work.Spaces.HkSq α 4 A4 + Work.Spaces.HkSq α 4 A5) := hs
      _ ≤ 16 * (Ktot * (1 + Work.Spaces.HkSq α 5 w)) :=
          mul_le_mul_of_nonneg_left hbound (by norm_num)
      _ = 16 * Ktot * (1 + Work.Spaces.HkSq α 5 w) := by ring
  have hsq6 : Work.Spaces.HkSq α 6 (epsWBlk α Φs w Φg μ lam)
      ≤ 16 * Ktot * ((1 + Work.Spaces.HkSq α 7 w) + (1 + Work.Spaces.HkSq α 6 w) ^ 2) := by
    rw [hsum]
    have hs := hkSq_sum5 hα0 eL.sm eM.sm e0.sm eN.sm eS.sm eL.hm eM.hm e0.hm eN.hm eS.hm
    have hS7 := Work.Spaces.HkSq_nonneg α 7 w
    have hS6 := Work.Spaces.HkSq_nonneg α 6 w
    have hbound : Work.Spaces.HkSq α 6 A1 + Work.Spaces.HkSq α 6 A2 + Work.Spaces.HkSq α 6 A3
        + Work.Spaces.HkSq α 6 A4 + Work.Spaces.HkSq α 6 A5
        ≤ Ktot * ((1 + Work.Spaces.HkSq α 7 w) + (1 + Work.Spaces.HkSq α 6 w) ^ 2) := by
      rw [hKtot]
      nlinarith [eL.b6, eM.b6, e0.b6, eN.b6, eS.b6, hS7, hS6,
        sq_nonneg (1 + Work.Spaces.HkSq α 6 w), hKL, hKM, hK0, hKN, hKS]
    calc Work.Spaces.HkSq α 6 (sum5 A1 A2 A3 A4 A5)
        ≤ 16 * (Work.Spaces.HkSq α 6 A1 + Work.Spaces.HkSq α 6 A2 + Work.Spaces.HkSq α 6 A3
            + Work.Spaces.HkSq α 6 A4 + Work.Spaces.HkSq α 6 A5) := hs
      _ ≤ 16 * (Ktot * ((1 + Work.Spaces.HkSq α 7 w) + (1 + Work.Spaces.HkSq α 6 w) ^ 2)) :=
          mul_le_mul_of_nonneg_left hbound (by norm_num)
      _ = 16 * Ktot * ((1 + Work.Spaces.HkSq α 7 w) + (1 + Work.Spaces.HkSq α 6 w) ^ 2) := by ring
  have hHQ : Work.FTS.VocabO.HQo α 6 (epsWBlk α Φs w Φg μ lam) := ⟨hsm, hm6⟩
  have hN5 : Work.Spaces.HkNorm α 5 w = Real.sqrt (Work.Spaces.HkSq α 5 w) := rfl
  have hN6 : Work.Spaces.HkNorm α 6 w = Real.sqrt (Work.Spaces.HkSq α 6 w) := rfl
  have hN7 : Work.Spaces.HkNorm α 7 w = Real.sqrt (Work.Spaces.HkSq α 7 w) := rfl
  refine ⟨hHQ, ?_, ?_⟩
  · rw [Work.Spaces.HkNorm]
    have hS5 := Work.Spaces.HkSq_nonneg α 5 w
    calc Real.sqrt (Work.Spaces.HkSq α 4 (epsWBlk α Φs w Φg μ lam))
        ≤ Real.sqrt (16 * Ktot * (1 + Work.Spaces.HkSq α 5 w)) := Real.sqrt_le_sqrt hsq4
      _ = Real.sqrt (16 * Ktot) * Real.sqrt (1 + Work.Spaces.HkSq α 5 w) := by
          rw [Real.sqrt_mul (by positivity)]
      _ ≤ Real.sqrt (16 * Ktot) * (1 + Real.sqrt (Work.Spaces.HkSq α 5 w)) :=
          mul_le_mul_of_nonneg_left (sqrt_one_add_le hS5) (Real.sqrt_nonneg _)
      _ = Real.sqrt (16 * Ktot) * (1 + Work.Spaces.HkNorm α 5 w) := by rw [hN5]
      _ ≤ C * (1 + Work.Spaces.HkNorm α 5 w) :=
          mul_le_mul_of_nonneg_right hCsq (by linarith [Work.Spaces.HkNorm_nonneg α 5 w])
  · rw [Work.Spaces.HkNorm]
    have hS6 := Work.Spaces.HkSq_nonneg α 6 w
    have hS7 := Work.Spaces.HkSq_nonneg α 7 w
    have hsq : Real.sqrt ((1 + Work.Spaces.HkSq α 7 w) + (1 + Work.Spaces.HkSq α 6 w) ^ 2)
        ≤ (1 + Work.Spaces.HkNorm α 7 w) + (1 + Work.Spaces.HkNorm α 6 w) ^ 2 := by
      have h1 : Real.sqrt (1 + Work.Spaces.HkSq α 7 w) ≤ 1 + Work.Spaces.HkNorm α 7 w := by
        refine le_trans (sqrt_one_add_le hS7) (le_of_eq ?_)
        rw [hN7]
      have h2 : Real.sqrt ((1 + Work.Spaces.HkSq α 6 w) ^ 2)
          = 1 + Work.Spaces.HkSq α 6 w := Real.sqrt_sq (by linarith)
      have h3 : 1 + Work.Spaces.HkSq α 6 w ≤ (1 + Work.Spaces.HkNorm α 6 w) ^ 2 := by
        rw [hN6]
        nlinarith [Real.sq_sqrt hS6, Real.sqrt_nonneg (Work.Spaces.HkSq α 6 w)]
      calc Real.sqrt ((1 + Work.Spaces.HkSq α 7 w) + (1 + Work.Spaces.HkSq α 6 w) ^ 2)
          ≤ Real.sqrt (1 + Work.Spaces.HkSq α 7 w)
              + Real.sqrt ((1 + Work.Spaces.HkSq α 6 w) ^ 2) :=
            sqrt_add_le' (by linarith) (by positivity)
        _ = Real.sqrt (1 + Work.Spaces.HkSq α 7 w) + (1 + Work.Spaces.HkSq α 6 w) := by rw [h2]
        _ ≤ (1 + Work.Spaces.HkNorm α 7 w) + (1 + Work.Spaces.HkNorm α 6 w) ^ 2 := by
            linarith [h1, h3]
    calc Real.sqrt (Work.Spaces.HkSq α 6 (epsWBlk α Φs w Φg μ lam))
        ≤ Real.sqrt (16 * Ktot * ((1 + Work.Spaces.HkSq α 7 w)
            + (1 + Work.Spaces.HkSq α 6 w) ^ 2)) := Real.sqrt_le_sqrt hsq6
      _ = Real.sqrt (16 * Ktot) * Real.sqrt ((1 + Work.Spaces.HkSq α 7 w)
            + (1 + Work.Spaces.HkSq α 6 w) ^ 2) := by rw [Real.sqrt_mul (by positivity)]
      _ ≤ Real.sqrt (16 * Ktot) * ((1 + Work.Spaces.HkNorm α 7 w)
            + (1 + Work.Spaces.HkNorm α 6 w) ^ 2) :=
          mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg _)
      _ ≤ C * ((1 + Work.Spaces.HkNorm α 7 w) + (1 + Work.Spaces.HkNorm α 6 w) ^ 2) :=
          mul_le_mul_of_nonneg_right hCsq (by
            have h7 := Work.Spaces.HkNorm_nonneg α 7 w
            have h6 := Work.Spaces.HkNorm_nonneg α 6 w
            positivity)
      _ = C * (1 + Work.Spaces.HkNorm α 7 w) + C * (1 + Work.Spaces.HkNorm α 6 w) ^ 2 := by ring

/-- The `BData` of the `N₀`-block, in the `∃ α₀` shape needed by the assembly: the all-scale
producer `blocks.N0_BData` is used verbatim, and the off-quadrant-vanishing hypothesis of the
assembly is specialised to its `z > 0` half (the part the norms see). -/
theorem blkN0_BData_blocks (C₀ : ℝ) :
    ∃ a : ℝ, 0 < a ∧ ∀ α ∈ Set.Ioc (0 : ℝ) a, ∃ K : ℝ, 0 < K ∧ ∀ {w : Fn},
      Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      (∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (Real.pi / 2)) → w z θ = 0) →
      BData α w K (blkN0 α w) := by
  obtain ⟨K, hK, h⟩ := blocks.N0_BData C₀
  exact ⟨1, one_pos, fun α hα => ⟨K, hK, fun {w} hc hx hzero =>
    h α hα w hc hx (fun z θ hz hth => hzero z θ (fun hh => hth hh.2))⟩⟩

/-- The `BData` of the `N`-block, in the `∃ α₀` shape needed by the assembly. -/
theorem blkN_BData_blocks (C₀ Ce Cs : ℝ) :
    ∃ a : ℝ, 0 < a ∧ ∀ α ∈ Set.Ioc (0 : ℝ) a, ∃ K : ℝ, 0 < K ∧ ∀ {Φs w Φg : Fn},
      Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      (∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (Real.pi / 2)) → w z θ = 0) →
      Work.FTS.VocabO.EllPkgGo α Ce w Φg → Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
      Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
      BData α w K (blkN α Φs w Φg) := by
  obtain ⟨K, hK, h⟩ := blocks.N_BData C₀ Ce Cs
  exact ⟨1, one_pos, fun α hα => ⟨K, hK, fun {Φs w Φg} hc hx hzero hgo hK' hstar =>
    h α hα Φs w Φg hc hx (fun z θ hz hth => hzero z θ (fun hh => hth hh.2)) hgo hK' hstar⟩⟩

theorem epsWP_semitame_proof :
    ∀ C₀ Ce Cs : ℝ, ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α ∈ Set.Ioc 0 α₀, ∃ Ct : ℝ, 0 ≤ Ct ∧
    ∀ {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn},
    Work.FTS.StrongEps.IsSmoothKernel ρ →
    (∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u)) →
    Work.FTS.StrongPersist.StarPkg6 α Cs Φs → Work.FTS.StrongEps.MuLamOK α C₀ Φs E →
    ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ (g : Work.FTS.Galerkin.Fam) (τ : ℝ),
      Work.FTS.ClassC.ClassC α (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) →
      Work.FTS.Nonlin.Xn α (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) ≤ C₀ * α ^ 2 →
      Work.FTS.VocabO.HQo α 6 (Work.FTS.StrongEps.epsWP α ρ ε Φs E g τ) ∧
      Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.epsWP α ρ ε Φs E g τ)
        ≤ Ct * (1 + Work.Spaces.HkNorm α 5 (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)) ∧
      Work.Spaces.HkNorm α 6 (Work.FTS.StrongEps.epsWP α ρ ε Φs E g τ)
        ≤ Ct * (1 + Work.Spaces.HkNorm α 7 (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ))
          + Ct * (1 + Work.Spaces.HkNorm α 6 (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)) ^ 2 := by
  intro C₀ Ce Cs
  obtain ⟨aL, haL, hLall⟩ := Work.FTS.StrongEps.E4R3.RawE6Aux.bdata_blkLin C₀
  obtain ⟨a0, ha0, h0all⟩ := blkN0_BData_blocks C₀
  obtain ⟨aN, haN, hNall⟩ := blkN_BData_blocks C₀ Ce Cs
  refine ⟨min (min aL (min 1 a0)) (min aN 1),
    lt_min (lt_min haL (lt_min one_pos ha0)) (lt_min haN one_pos), ?_⟩
  intro α hα
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := le_trans hα.2 (le_trans (min_le_right _ _) (min_le_right _ _))
  have hαL : α ∈ Set.Ioc 0 aL :=
    ⟨hα0, le_trans hα.2 (le_trans (min_le_left _ _) (min_le_left _ _))⟩
  have hα0' : α ∈ Set.Ioc 0 a0 :=
    ⟨hα0, le_trans hα.2 (le_trans (min_le_left _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _)))⟩
  have hαN : α ∈ Set.Ioc 0 aN :=
    ⟨hα0, le_trans hα.2 (le_trans (min_le_right _ _) (min_le_left _ _))⟩
  obtain ⟨KL, hKL, hL⟩ := hLall α hαL
  obtain ⟨K0, hK0, h0⟩ := h0all α hα0'
  obtain ⟨KN, hKN, hN⟩ := hNall α hαN
  obtain ⟨KM, hKM, hM⟩ := Work.FTS.StrongEps.E4R3.RawE6Aux.bdata_blkMu C₀ α
    ⟨hα0, hα1⟩
  obtain ⟨KS, hKS, hS⟩ := Work.FTS.StrongEps.E4R3.RawE6Aux.bdata_blkNstar C₀ α
    ⟨hα0, hα1⟩
  refine ⟨Real.sqrt (16 * (KL + KM + K0 + KN + KS + 1)) + 1, by positivity, ?_⟩
  intro ρ Φs E hρ hEll hstar hml ε hε g τ hcls hXw
  set w : Fn := Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ with hw
  have hzero : ∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (Real.pi / 2)) → w z θ = 0 := by
    intro z θ hzq
    rw [hw]
    exact Pz_Jeps_eq_zero_of_not_mem_quadrant (ρ := ρ) (ε := ε)
      (h := Work.FTS.Galerkin.slice g τ) hzq
  have hml' := hml w hcls hXw
  have hμ : |muBlk α Φs w (E w)| ≤ 1 / 2 := by
    have h := hml'.1
    rwa [muDyn_const_eq α Φs E w] at h
  have hlam : |Work.Construction.lamfun (muBlk α Φs w (E w))| ≤ 1 := by
    have h := hml'.2
    rwa [lamDyn_const_eq α Φs E w] at h
  have key := Work.FTS.StrongEps.E4R3.RawE6Aux.semitame_of_bdata
    (C₀ := C₀) (Ce := Ce) (Cs := Cs) (α := α) ⟨hα0, hα1⟩ hKL hKM hK0 hKN hKS
    hL hM h0 hN hS hcls hXw hμ hlam hμ hzero (hEll w hcls).1 (hEll w hcls).2 hstar
  have hwp : Work.FTS.StrongEps.epsWP α ρ ε Φs E g τ
      = epsWBlk α Φs w (E w) (muBlk α Φs w (E w))
          (Work.Construction.lamfun (muBlk α Φs w (E w))) := by
    rw [hw]
    exact epsWP_eq_epsWBlk α ρ ε Φs E g τ
  rw [hwp]
  exact key

end Work.FTS.StrongEps.E4R3.Apriori4Proofs
