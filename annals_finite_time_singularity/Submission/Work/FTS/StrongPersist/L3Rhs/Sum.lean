import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.ProdRadSup
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.AuxProof
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs

open Work.FTS.Galerkin (Fn)
open Work.Spaces (HkMem HkSq HkNorm)
open Work.FTS.Nonlin (Xn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

/-- The open quadrant `Q0` of the elliptic estimates, written out. -/
abbrev OQ : Set (ℝ × ℝ) := Work.FTS.EllipticEst.Q0

private theorem min_left_trans {a b c : ℝ} (h : a ≤ c) : min a b ≤ c :=
  le_trans (min_le_left a b) h

private theorem min_right_trans {a b c : ℝ} (h : b ≤ c) : min a b ≤ c :=
  le_trans (min_le_right a b) h

theorem L3RhsSum
    -- ## the blocks of `N₀`, `N` and `Nstar`
    (CN : ℝ) (hCN : 0 < CN)
    (hNstar : ∀ α ∈ Set.Ioc 0 1, ∀ (f : Fn) (μ lam M : ℝ), H6Adm α f → Xn α f ≤ M →
      |μ| ≤ 1 / 2 → |lam| ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Nstar μ lam f) ∧
      HkMem α 3 (Work.Construction.Nstar μ lam f) ∧
      HkNorm α 3 (Work.Construction.Nstar μ lam f) ≤ CN * (1 + M))
    (C0 : ℝ) (hC0 : 0 < C0)
    (hN0fix : ∀ α ∈ Set.Ioc 0 1,
      Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N0fix α) ∧
      HkMem α 3 (Work.FTS.Nonlin.N0fix α) ∧
      HkNorm α 3 (Work.FTS.Nonlin.N0fix α) ≤ C0 * α ^ 2)
    (Cg Cpg a2g : ℝ) (hCg : 0 < Cg) (hCpg : 0 ≤ Cpg) (ha2g : 0 < a2g)
    (hN0g : ∀ α ∈ Set.Ioc 0 a2g, ∀ (f : Fn) (M : ℝ), H6Adm α f → Xn α f ≤ M →
      ContDiffOn ℝ 3 (Function.uncurry (N0gSum α f)) OQ ∧
      HkMem α 3 (N0gSum α f) ∧
      HkNorm α 3 (N0gSum α f) ≤ Cg * α ^ (-Cpg) * (1 + M) ^ 4 * (1 + Xn6 α f) ^ 2)
    (Cs1 Cps1 a2s1 : ℝ) (hCs1 : 0 < Cs1) (hCps1 : 0 ≤ Cps1) (ha2s1 : 0 < a2s1)
    (hNss : ∀ α ∈ Set.Ioc 0 a2s1, ∀ (Cs : ℝ) (Φs : Fn), Work.FTS.VocabO2.StarPkgo2 α Cs Φs →
      ContDiffOn ℝ 3 (Function.uncurry (NSsSum α Φs)) OQ ∧
      HkMem α 3 (NSsSum α Φs) ∧
      HkNorm α 3 (NSsSum α Φs) ≤ Cs1 * (1 + |Cs|) ^ 4 * α ^ (-Cps1))
    (Cs2 Cps2 a2s2 : ℝ) (hCs2 : 0 < Cs2) (hCps2 : 0 ≤ Cps2) (ha2s2 : 0 < a2s2)
    (hNsg : ∀ α ∈ Set.Ioc 0 a2s2, ∀ (Cs : ℝ) (Φs f : Fn) (M : ℝ),
      Work.FTS.VocabO2.StarPkgo2 α Cs Φs → H6Adm α f → Xn α f ≤ M →
      ContDiffOn ℝ 3 (Function.uncurry (NSgSum α Φs f)) OQ ∧
      HkMem α 3 (NSgSum α Φs f) ∧
      HkNorm α 3 (NSgSum α Φs f) ≤ Cs2 * (1 + |Cs|) ^ 4 * α ^ (-Cps2) * (1 + M) ^ 4)
    (Ce1 Cpe1 a2e1 : ℝ) (hCe1 : 0 < Ce1) (hCpe1 : 0 ≤ Cpe1) (ha2e1 : 0 < a2e1)
    (hNgs : ∀ α ∈ Set.Ioc 0 a2e1, ∀ (Ce M : ℝ) (f Φg : Fn),
      EllPkgK α 6 Ce f Φg → H6Adm α f → Xn α f ≤ M →
      ContDiffOn ℝ 3 (Function.uncurry (NGsSum α f Φg)) OQ ∧
      HkMem α 3 (NGsSum α f Φg) ∧
      HkNorm α 3 (NGsSum α f Φg)
        ≤ Ce1 * (1 + |Ce|) ^ 4 * α ^ (-Cpe1) * (1 + M) ^ 4 * (1 + Xn6 α f) ^ 2)
    (Ce2 Cpe2 a2e2 : ℝ) (hCe2 : 0 < Ce2) (hCpe2 : 0 ≤ Cpe2) (ha2e2 : 0 < a2e2)
    (hNgg : ∀ α ∈ Set.Ioc 0 a2e2, ∀ (Ce M : ℝ) (f Φg : Fn),
      EllPkgK α 6 Ce f Φg → H6Adm α f → Xn α f ≤ M →
      ContDiffOn ℝ 3 (Function.uncurry (NGgSum α f Φg)) OQ ∧
      HkMem α 3 (NGgSum α f Φg) ∧
      HkNorm α 3 (NGgSum α f Φg)
        ≤ Ce2 * (1 + |Ce|) ^ 4 * α ^ (-Cpe2) * (1 + M) ^ 4 * (1 + Xn6 α f) ^ 2)
    (Cf Cpf a2f : ℝ) (hCf : 0 < Cf) (hCpf : 0 ≤ Cpf) (ha2f : 0 < a2f)
    (hNfk : ∀ α ∈ Set.Ioc 0 a2f, ∀ (f : Fn) (M : ℝ), H6Adm α f → Xn α f ≤ M →
      ContDiffOn ℝ 3 (Function.uncurry (NFkSum α f)) OQ ∧
      HkMem α 3 (NFkSum α f) ∧
      HkNorm α 3 (NFkSum α f) ≤ Cf * α ^ (-Cpf) * (1 + M) ^ 4 * (1 + Xn6 α f) ^ 2)
    -- ## the structural inputs
    (CL : ℝ) (hCL : 0 < CL)
    (hL12z : ∀ α ∈ Set.Ioc 0 1, ∀ (u : Fn), HkMem α 0 u →
      |Work.Construction.L12 u 0| ≤ CL * HkNorm α 0 u)
    (hL12add : ∀ α ∈ Set.Ioc 0 1, ∀ (f : Fn), H6Adm α f → ∀ z : ℝ, 0 < z →
      Work.Construction.L12 (Work.Construction.Ftot α f) z
        = Work.Construction.L12 (Work.Construction.Fstar α) z + Work.Construction.L12 f z)
    (hFKadd : ∀ α ∈ Set.Ioc 0 1, ∀ (f : Fn), H6Adm α f → ∀ z : ℝ, 0 < z →
      Work.Construction.FK (Work.Construction.Ftot α f) z
        = Work.Construction.FK (Work.Construction.Fstar α) z + Work.Construction.FK f z)
    (KAK : ℝ) (hKAK : 0 < KAK)
    (hAKb : ∀ α ∈ Set.Ioc 0 1, Work.FTS.Nonlin.Xn α (Work.Construction.AK α) ≤ KAK) :
    ∃ α₂ C3 Cpow : ℝ, 0 < α₂ ∧ 0 < C3 ∧ 0 ≤ Cpow ∧
      ∀ α ∈ Set.Ioc 0 α₂, ∀ (Ce Cs : ℝ) (E : Fn → Fn) (Φs Φ f : Fn) (μ lam M : ℝ),
        Ell6Ctx α Ce Cs E Φs f Φ → H6Adm α f → Xn α f ≤ M → |μ| ≤ 1 / 2 → |lam| ≤ 1 →
        HkMem α 3 (rhsOf α μ lam (Work.Construction.Ftot α f) Φ f) ∧
        HkNorm α 3 (rhsOf α μ lam (Work.Construction.Ftot α f) Φ f)
          ≤ C3 * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-Cpow) * (1 + M) ^ 4
              * (1 + HkNorm α 6 f) ^ 2 := by
  -- ## the constants
  set α₂ : ℝ := min 1 (min a2g (min a2s1 (min a2s2 (min a2e1 (min a2e2 a2f))))) with hα2def
  set Cpow : ℝ := Cpg + Cps1 + Cps2 + Cpe1 + Cpe2 + Cpf + 1 with hCpowdef
  set KN0 : ℝ := 2 * (C0 + Cg) with hKN0def
  set KN : ℝ := 32 * (Cs1 + Cs2 + Ce1 + Ce2 + Cf) with hKNdef
  set KMU : ℝ := 2 * CL * (KN0 + KN) * KAK + KAK with hKMUdef
  set C3 : ℝ := 4096 * (KN0 + KN + KMU + CN + 1) with hC3def
  have hKN00 : 0 < KN0 := by rw [hKN0def]; linarith
  have hKN0 : 0 < KN := by rw [hKNdef]; linarith
  have hKMU0 : 0 < KMU := by
    rw [hKMUdef]
    have h1 : 0 < 2 * CL * (KN0 + KN) * KAK :=
      mul_pos (mul_pos (mul_pos (by norm_num) hCL) (by linarith)) hKAK
    linarith
  have hα21 : α₂ ≤ 1 := by rw [hα2def]; exact min_left_trans le_rfl
  have hα2g : α₂ ≤ a2g := by
    rw [hα2def]; exact min_right_trans (min_left_trans le_rfl)
  have hα2s1 : α₂ ≤ a2s1 := by
    rw [hα2def]; exact min_right_trans (min_right_trans (min_left_trans le_rfl))
  have hα2s2 : α₂ ≤ a2s2 := by
    rw [hα2def]
    exact min_right_trans (min_right_trans (min_right_trans (min_left_trans le_rfl)))
  have hα2e1 : α₂ ≤ a2e1 := by
    rw [hα2def]
    exact min_right_trans
      (min_right_trans (min_right_trans (min_right_trans (min_left_trans le_rfl))))
  have hα2e2 : α₂ ≤ a2e2 := by
    rw [hα2def]
    exact min_right_trans
      (min_right_trans (min_right_trans (min_right_trans
        (min_right_trans (min_left_trans le_rfl)))))
  have hα2f : α₂ ≤ a2f := by
    rw [hα2def]
    exact min_right_trans
      (min_right_trans (min_right_trans (min_right_trans
        (min_right_trans (min_right_trans le_rfl)))))
  refine ⟨α₂, C3, Cpow, ?_, ?_, ?_, ?_⟩
  · rw [hα2def]
    exact lt_min one_pos (lt_min ha2g (lt_min ha2s1 (lt_min ha2s2
      (lt_min ha2e1 (lt_min ha2e2 ha2f)))))
  · rw [hC3def]; linarith
  · rw [hCpowdef]; linarith
  · intro α hαIoc Ce Cs E Φs Φ f μ lam M hctx h6 hM hμ hlam
    have hα : 0 < α := hαIoc.1
    have hα1 : α ≤ 1 := le_trans hαIoc.2 hα21
    have hαIoc1 : α ∈ Set.Ioc 0 1 := ⟨hα, hα1⟩
    have hαg : α ∈ Set.Ioc 0 a2g := ⟨hα, le_trans hαIoc.2 hα2g⟩
    have hαs1 : α ∈ Set.Ioc 0 a2s1 := ⟨hα, le_trans hαIoc.2 hα2s1⟩
    have hαs2 : α ∈ Set.Ioc 0 a2s2 := ⟨hα, le_trans hαIoc.2 hα2s2⟩
    have hαe1 : α ∈ Set.Ioc 0 a2e1 := ⟨hα, le_trans hαIoc.2 hα2e1⟩
    have hαe2 : α ∈ Set.Ioc 0 a2e2 := ⟨hα, le_trans hαIoc.2 hα2e2⟩
    have hαf : α ∈ Set.Ioc 0 a2f := ⟨hα, le_trans hαIoc.2 hα2f⟩
    obtain ⟨hstar, hell, hsum⟩ := hctx
    have hsmf : Work.FTS.EllipticEst.SmoothOpen f := h6.reg.1
    have hmem6 : HkMem α 6 f := h6.reg.2
    have hΦs : Work.FTS.EllipticEst.SmoothOpen Φs := hstar.smooth
    have hΦg : Work.FTS.EllipticEst.SmoothOpen (E f) := hell.smooth
    have hM0 : 0 ≤ M := le_trans (Real.sqrt_nonneg (HkSq α 4 f)) hM
    have hX60 : 0 ≤ Xn6 α f := Real.sqrt_nonneg _
    -- the common pricing factor
    set R : ℝ := pricedR α Cpow M (Xn6 α f) Ce Cs with hRdef
    have hR1 : 1 ≤ R := one_le_pricedR hα hα1 (by rw [hCpowdef]; linarith) hM0 hX60
    have hR0 : 0 ≤ R := le_trans (by norm_num) hR1
    -- ## the summands
    set b1 : Fn := fun z θ =>
      -(Work.Construction.mubar (Work.Construction.N0 α (Work.Construction.Ftot α f) f)
        (Work.Construction.N α (Work.Construction.Ftot α f) (fun z θ => Φs z θ + E f z θ))
        * Work.Construction.AK α z θ)
      with hb1
    set b2 : Fn := Work.FTS.Nonlin.N0fix α with hb2
    set b3 : Fn := N0gSum α f with hb3
    set b4 : Fn := NSsSum α Φs with hb4
    set b5 : Fn := NSgSum α Φs f with hb5
    set b6 : Fn := NGsSum α f (E f) with hb6
    set b7 : Fn := NGgSum α f (E f) with hb7
    set b8 : Fn := NFkSum α f with hb8
    set b9 : Fn := Work.Construction.Nstar μ lam f with hb9
    -- ## the per-summand data
    -- b2
    obtain ⟨hb2sm, hb2m, hb2b⟩ := hN0fix α hαIoc1
    have hb2c : ContDiffOn ℝ 3 (Function.uncurry b2) OQ := by
      rw [hb2]; exact hb2sm.forall 3
    have hb2R : HkNorm α 3 b2 ≤ C0 * R := by
      rw [hb2]
      exact le_trans hb2b (mul_shape_alpha2 hα hα1
        (by rw [hCpowdef]; linarith) hM0 hX60 hC0.le)
    -- b3
    obtain ⟨hb3c, hb3m, hb3b⟩ := hN0g α hαg f M h6 hM
    have hb3R : HkNorm α 3 b3 ≤ Cg * R := by
      rw [hb3]
      exact le_trans hb3b (mul_shape_MX hα hα1 hCpg
        (by rw [hCpowdef]; linarith) (by rw [hCpowdef]; linarith) hM0 hX60 hCg.le)
    -- b4
    obtain ⟨hb4c, hb4m, hb4b⟩ := hNss α hαs1 Cs Φs hstar
    have hb4R : HkNorm α 3 b4 ≤ Cs1 * R := by
      rw [hb4]
      exact le_trans hb4b (mul_shape_s hα hα1 hCps1
        (by rw [hCpowdef]; linarith) (by rw [hCpowdef]; linarith) hM0 hX60 hCs1.le)
    -- b5
    obtain ⟨hb5c, hb5m, hb5b⟩ := hNsg α hαs2 Cs Φs f M hstar h6 hM
    have hb5R : HkNorm α 3 b5 ≤ Cs2 * R := by
      rw [hb5]
      exact le_trans hb5b (mul_shape_sM hα hα1 hCps2
        (by rw [hCpowdef]; linarith) (by rw [hCpowdef]; linarith) hM0 hX60 hCs2.le)
    -- b6
    obtain ⟨hb6c, hb6m, hb6b⟩ := hNgs α hαe1 Ce M f (E f) hell h6 hM
    have hb6R : HkNorm α 3 b6 ≤ Ce1 * R := by
      rw [hb6]
      exact le_trans hb6b (mul_shape_e hα hα1 hCpe1
        (by rw [hCpowdef]; linarith) (by rw [hCpowdef]; linarith) hM0 hX60 hCe1.le)
    -- b7
    obtain ⟨hb7c, hb7m, hb7b⟩ := hNgg α hαe2 Ce M f (E f) hell h6 hM
    have hb7R : HkNorm α 3 b7 ≤ Ce2 * R := by
      rw [hb7]
      exact le_trans hb7b (mul_shape_e hα hα1 hCpe2
        (by rw [hCpowdef]; linarith) (by rw [hCpowdef]; linarith) hM0 hX60 hCe2.le)
    -- b8
    obtain ⟨hb8c, hb8m, hb8b⟩ := hNfk α hαf f M h6 hM
    have hb8R : HkNorm α 3 b8 ≤ Cf * R := by
      rw [hb8]
      exact le_trans hb8b (mul_shape_MX hα hα1 hCpf
        (by rw [hCpowdef]; linarith) (by rw [hCpowdef]; linarith) hM0 hX60 hCf.le)
    -- ## the `N₀` chain (b2 + b3)
    obtain ⟨hm23, hb23⟩ := HkNorm_add_le2 α hb2m hb3m hb2c hb3c hb2R hb3R
      (by positivity) (by positivity)
    -- ## the `N` chain (b4 + … + b8)
    have hb4c5 : ContDiffOn ℝ 3 (Function.uncurry (fun z θ => b4 z θ + b5 z θ)) OQ :=
      hb4c.add hb5c
    obtain ⟨hm45, hb45⟩ := HkNorm_add_le2 α hb4m hb5m hb4c hb5c hb4R hb5R
      (by positivity) (by positivity)
    have hb45c : ContDiffOn ℝ 3 (Function.uncurry (fun z θ => b4 z θ + b5 z θ)) OQ := hb4c5
    obtain ⟨hm456, hb456⟩ := HkNorm_add_le2 α hm45 hb6m hb45c hb6c hb45 hb6R
      (by positivity) (by positivity)
    have hb456c : ContDiffOn ℝ 3 (Function.uncurry (fun z θ => (b4 z θ + b5 z θ) + b6 z θ)) OQ :=
      hb4c5.add hb6c
    obtain ⟨hm4567, hb4567⟩ := HkNorm_add_le2 α hm456 hb7m hb456c hb7c hb456 hb7R
      (by positivity) (by positivity)
    have hb4567c : ContDiffOn ℝ 3
        (Function.uncurry (fun z θ => ((b4 z θ + b5 z θ) + b6 z θ) + b7 z θ)) OQ :=
      hb456c.add hb7c
    obtain ⟨hmN, hbN⟩ := HkNorm_add_le2 α hm4567 hb8m hb4567c hb8c hb4567 hb8R
      (by positivity) (by positivity)
    -- ## the `ℋ³`-facts of `N₀` and `N`
    have hN0mem : HkMem α 3 (Work.Construction.N0 α (Work.Construction.Ftot α f) f) :=
      Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 3 hm23
        (fun z hz θ hθ => (N0split hsmf hz hθ.1 hθ.2).symm)
    have hN0b : HkNorm α 3 (Work.Construction.N0 α (Work.Construction.Ftot α f) f) ≤ KN0 * R := by
      have heq : HkSq α 3 (Work.Construction.N0 α (Work.Construction.Ftot α f) f)
          = HkSq α 3 (fun z θ => b2 z θ + b3 z θ) :=
        Work.FTS.EllipticEst.HkSq_congr_open α 3 (fun z θ hz hθ hθ2 => N0split hsmf hz hθ hθ2)
      rw [Work.Spaces.HkNorm, heq]
      have hb23' : HkNorm α 3 (fun z θ => b2 z θ + b3 z θ) ≤ 2 * (C0 * R + Cg * R) := hb23
      calc Real.sqrt (HkSq α 3 (fun z θ => b2 z θ + b3 z θ))
          = HkNorm α 3 (fun z θ => b2 z θ + b3 z θ) := rfl
        _ ≤ 2 * (C0 * R + Cg * R) := hb23'
        _ = KN0 * R := by rw [hKN0def]; ring
    have hNs := fun z θ (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) =>
      Work.FTS.NonlinRows.Rl1.splitOpen hα hα1 hsmf hΦs hΦg
        (fun z hz => hL12add α hαIoc1 f h6 z hz)
        (fun z hz => hFKadd α hαIoc1 f h6 z hz)
        (fun z hz => L12_differentiableAt hsmf hmem6 hz) z θ ⟨hz, hθ, hθ2⟩
    have hNmem : HkMem α 3 (Work.Construction.N α (Work.Construction.Ftot α f) (fun z θ => Φs z θ + E f z θ)) :=
      Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 3 hmN
        (fun z hz θ hθ => by
          rw [hNs z θ hz hθ.1 hθ.2]
          try simp only [hb4, hb5, hb6, hb7, hb8, NSsSum, NSgSum, NGsSum, NGgSum, NFkSum]
          try beta_reduce
          ring_nf)
    have hNb : HkNorm α 3 (Work.Construction.N α (Work.Construction.Ftot α f) (fun z θ => Φs z θ + E f z θ)) ≤ KN * R := by
      have heq : HkSq α 3 (Work.Construction.N α (Work.Construction.Ftot α f) (fun z θ => Φs z θ + E f z θ))
          = HkSq α 3 (fun z θ => ((b4 z θ + b5 z θ) + b6 z θ + b7 z θ) + b8 z θ) := by
        refine Work.FTS.EllipticEst.HkSq_congr_open α 3 (fun z θ hz hθ hθ2 => ?_)
        rw [hNs z θ hz hθ hθ2]
        try simp only [hb4, hb5, hb6, hb7, hb8, NSsSum, NSgSum, NGsSum, NGgSum, NFkSum]
        try beta_reduce
        ring_nf
      rw [Work.Spaces.HkNorm, heq]
      have hbN' : HkNorm α 3 (fun z θ => ((b4 z θ + b5 z θ) + b6 z θ + b7 z θ) + b8 z θ)
          ≤ 2 * (2 * (2 * (2 * (Cs1 * R + Cs2 * R) + Ce1 * R) + Ce2 * R) + Cf * R) := hbN
      calc Real.sqrt (HkSq α 3 (fun z θ => ((b4 z θ + b5 z θ) + b6 z θ + b7 z θ) + b8 z θ))
          = HkNorm α 3 (fun z θ => ((b4 z θ + b5 z θ) + b6 z θ + b7 z θ) + b8 z θ) := rfl
        _ ≤ 2 * (2 * (2 * (2 * (Cs1 * R + Cs2 * R) + Ce1 * R) + Ce2 * R) + Cf * R) := hbN'
        _ ≤ KN * R := by
            rw [hKNdef]
            have hnorm : 2 * (2 * (2 * (2 * (Cs1 * R + Cs2 * R) + Ce1 * R) + Ce2 * R) + Cf * R)
                = (16 * Cs1 + 16 * Cs2 + 8 * Ce1 + 4 * Ce2 + 2 * Cf) * R := by ring
            rw [hnorm]
            exact mul_le_mul_of_nonneg_right
              (by linarith [hCs1.le, hCs2.le, hCe1.le, hCe2.le, hCf.le]) (by positivity)
    -- ## the level-zero facts of `N₀` and `N` (for the zero-mode bound)
    have hb2c0 : ContDiffOn ℝ 0 (Function.uncurry b2) OQ := hb2c.of_le (by norm_num)
    have hb3c0 : ContDiffOn ℝ 0 (Function.uncurry b3) OQ := hb3c.of_le (by norm_num)
    have hb2m0 : HkMem α 0 b2 :=
      HkMem_descend_of_contDiffOn (k := 0) (k' := 3) (by norm_num) hb2c0 hb2m
    have hb3m0 : HkMem α 0 b3 :=
      HkMem_descend_of_contDiffOn (k := 0) (k' := 3) (by norm_num) hb3c0 hb3m
    have hm23_0 : HkMem α 0 (fun z θ => b2 z θ + b3 z θ) :=
      (HkMem_HkSq_add2 (α := α) (k := 0) (f := b2) (g := b3) hb2c0 hb3c0 hb2m0 hb3m0).1
    have hmN_0 : HkMem α 0 (fun z θ => ((b4 z θ + b5 z θ) + b6 z θ + b7 z θ) + b8 z θ) := by
      have hb4c0 : ContDiffOn ℝ 0 (Function.uncurry b4) OQ := hb4c.of_le (by norm_num)
      have hb5c0 : ContDiffOn ℝ 0 (Function.uncurry b5) OQ := hb5c.of_le (by norm_num)
      have hb6c0 : ContDiffOn ℝ 0 (Function.uncurry b6) OQ := hb6c.of_le (by norm_num)
      have hb7c0 : ContDiffOn ℝ 0 (Function.uncurry b7) OQ := hb7c.of_le (by norm_num)
      have hb8c0 : ContDiffOn ℝ 0 (Function.uncurry b8) OQ := hb8c.of_le (by norm_num)
      have h4 : HkMem α 0 b4 :=
        HkMem_descend_of_contDiffOn (k := 0) (k' := 3) (by norm_num) hb4c0 hb4m
      have h5 : HkMem α 0 b5 :=
        HkMem_descend_of_contDiffOn (k := 0) (k' := 3) (by norm_num) hb5c0 hb5m
      have h6₀ : HkMem α 0 b6 :=
        HkMem_descend_of_contDiffOn (k := 0) (k' := 3) (by norm_num) hb6c0 hb6m
      have h7 : HkMem α 0 b7 :=
        HkMem_descend_of_contDiffOn (k := 0) (k' := 3) (by norm_num) hb7c0 hb7m
      have h8 : HkMem α 0 b8 :=
        HkMem_descend_of_contDiffOn (k := 0) (k' := 3) (by norm_num) hb8c0 hb8m
      have h45 : HkMem α 0 (fun z θ => b4 z θ + b5 z θ) :=
        (HkMem_HkSq_add2 (α := α) (k := 0) (f := b4) (g := b5) hb4c0 hb5c0 h4 h5).1
      have h456 : HkMem α 0 (fun z θ => (b4 z θ + b5 z θ) + b6 z θ) :=
        (HkMem_HkSq_add2 (α := α) (k := 0) (f := fun z θ => b4 z θ + b5 z θ) (g := b6)
          (hb4c0.add hb5c0) hb6c0 h45 h6₀).1
      have h4567 : HkMem α 0 (fun z θ => ((b4 z θ + b5 z θ) + b6 z θ) + b7 z θ) :=
        (HkMem_HkSq_add2 (α := α) (k := 0) (f := fun z θ => (b4 z θ + b5 z θ) + b6 z θ)
          (g := b7) ((hb4c0.add hb5c0).add hb6c0) hb7c0 h456 h7).1
      exact (HkMem_HkSq_add2 (α := α) (k := 0)
        (f := fun z θ => ((b4 z θ + b5 z θ) + b6 z θ) + b7 z θ) (g := b8)
        (((hb4c0.add hb5c0).add hb6c0).add hb7c0) hb8c0 h4567 h8).1
    have hN0mem0 : HkMem α 0 (Work.Construction.N0 α (Work.Construction.Ftot α f) f) :=
      Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 0 hm23_0
        (fun z hz θ hθ => (N0split hsmf hz hθ.1 hθ.2).symm)
    have hNmem0 : HkMem α 0 (Work.Construction.N α (Work.Construction.Ftot α f) (fun z θ => Φs z θ + E f z θ)) :=
      Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 0 hmN_0
        (fun z hz θ hθ => by
          rw [hNs z θ hz hθ.1 hθ.2]
          try simp only [hb4, hb5, hb6, hb7, hb8, NSsSum, NSgSum, NGsSum, NGgSum, NFkSum]
          try beta_reduce
          ring_nf)
    -- ## the `μ̄·AK` summand
    have hAK4 : HkMem α 4 (Work.Construction.AK α) := Work.FTS.NonlinRows.HkMem_AK α hα hα1
    have hAKb4 : HkNorm α 4 (Work.Construction.AK α) ≤ KAK := hAKb α hαIoc1
    have hb1dat := muAK_mem α hα hα1
      (N0v := Work.Construction.N0 α (Work.Construction.Ftot α f) f)
      (Nv := Work.Construction.N α (Work.Construction.Ftot α f) (fun z θ => Φs z θ + E f z θ))
      (CL := CL) (C0 := max KN0 KN * R) (CA := KAK)
      hCL.le (mul_nonneg (le_max_of_le_left hKN00.le) hR0) hKAK.le
      (fun u hu => hL12z α hαIoc1 u hu) hN0mem0 hNmem0 hN0mem hNmem
      (le_trans hN0b (mul_le_mul_of_nonneg_right (le_max_left _ _) hR0))
      (le_trans hNb (mul_le_mul_of_nonneg_right (le_max_right _ _) hR0))
      hAK4 hAKb4
    have hb1m : HkMem α 3 b1 := by rw [hb1]; exact HkMem_neg α 3 hb1dat.1
    have hb1R : HkNorm α 3 b1 ≤ KMU * R := by
      rw [hb1, HkNorm_neg, hKMUdef]
      refine le_trans hb1dat.2 ?_
      have hMS : max KN0 KN ≤ KN0 + KN :=
        max_le (by linarith [hKN0.le]) (by linarith [hKN00.le])
      have hKAKR : KAK ≤ KAK * R := by nlinarith [hKAK.le, hR1]
      have hMle : max KN0 KN * R ≤ (KN0 + KN) * R := mul_le_mul_of_nonneg_right hMS hR0
      have hfac : (0 : ℝ) ≤ 2 * CL * KAK := by positivity
      have hkey : 2 * CL * (max KN0 KN * R) * KAK ≤ 2 * CL * (KN0 + KN) * KAK * R := by
        calc 2 * CL * (max KN0 KN * R) * KAK = (2 * CL * KAK) * (max KN0 KN * R) := by ring
          _ ≤ (2 * CL * KAK) * ((KN0 + KN) * R) := mul_le_mul_of_nonneg_left hMle hfac
          _ = 2 * CL * (KN0 + KN) * KAK * R := by ring
      calc (2 * CL * (max KN0 KN * R) + 1) * KAK
          = 2 * CL * (max KN0 KN * R) * KAK + KAK := by ring
        _ ≤ 2 * CL * (KN0 + KN) * KAK * R + KAK * R := add_le_add hkey hKAKR
        _ = (2 * CL * (KN0 + KN) * KAK + KAK) * R := by ring
    have hb1c : ContDiffOn ℝ 3 (Function.uncurry b1) OQ := by
      rw [hb1]
      exact (((Work.FTS.OpenPkg.contDiffOn_four_AK α hα hα1).const_smul
        (Work.Construction.mubar _ _)).neg).of_le (by norm_num)
    -- ## the `Nstar` summand
    obtain ⟨hb9sm, hb9m, hb9b⟩ := hNstar α hαIoc1 f μ lam M h6 hM hμ hlam
    have hb9c : ContDiffOn ℝ 3 (Function.uncurry b9) OQ := by
      rw [hb9]; exact hb9sm.forall 3
    have hb9R : HkNorm α 3 b9 ≤ CN * R := by
      rw [hb9]
      exact le_trans hb9b (mul_shape_M hα hα1
        (by rw [hCpowdef]; linarith) hM0 hX60 hCN.le)
    -- ## the final chain
    have hu23c : ContDiffOn ℝ 3
        (Function.uncurry (fun z θ => b2 z θ + b3 z θ)) OQ := hb2c.add hb3c
    have huNc : ContDiffOn ℝ 3 (Function.uncurry (fun z θ =>
        ((b4 z θ + b5 z θ) + b6 z θ + b7 z θ) + b8 z θ)) OQ := hb4567c.add hb8c
    have hAc : ContDiffOn ℝ 3
        (Function.uncurry (fun z θ => (b2 z θ + b3 z θ)
          + (((b4 z θ + b5 z θ) + b6 z θ + b7 z θ) + b8 z θ))) OQ :=
      hu23c.add huNc
    obtain ⟨hmA, hbA⟩ := HkNorm_add_le2 α hm23 hmN hu23c huNc hb23 hbN
      (by positivity) (by positivity)
    have hBc : ContDiffOn ℝ 3 (Function.uncurry (fun z θ => ((b2 z θ + b3 z θ)
        + (((b4 z θ + b5 z θ) + b6 z θ + b7 z θ) + b8 z θ)) + b1 z θ)) OQ := hAc.add hb1c
    obtain ⟨hmB, hbB⟩ := HkNorm_add_le2 α hmA hb1m hAc hb1c hbA hb1R
      (by positivity) (by positivity)
    have hFc : ContDiffOn ℝ 3 (Function.uncurry (fun z θ => (((b2 z θ + b3 z θ)
        + (((b4 z θ + b5 z θ) + b6 z θ + b7 z θ) + b8 z θ)) + b1 z θ) + b9 z θ)) OQ :=
      hBc.add hb9c
    obtain ⟨hmF, hbF⟩ := HkNorm_add_le2 α hmB hb9m hBc hb9c hbB hb9R
      (by positivity) (by positivity)
    set uF : Fn := fun z θ => (((b2 z θ + b3 z θ)
      + (((b4 z θ + b5 z θ) + b6 z θ + b7 z θ) + b8 z θ)) + b1 z θ) + b9 z θ with huF
    have hmFu : HkMem α 3 uF := by rw [huF]; exact hmF
    have hbFu : HkNorm α 3 uF ≤ C3 * R := by
      rw [huF, hC3def]
      refine le_trans hbF ?_
      have hB23 : 2 * (C0 * R + Cg * R) ≤ 8 * (KN0 * R) := by
        have h1 : C0 * R ≤ KN0 * R :=
          mul_le_mul_of_nonneg_right (by rw [hKN0def]; linarith) hR0
        have h2 : Cg * R ≤ KN0 * R :=
          mul_le_mul_of_nonneg_right (by rw [hKN0def]; linarith) hR0
        linarith
      have hBN : 2 * (2 * (2 * (2 * (Cs1 * R + Cs2 * R) + Ce1 * R) + Ce2 * R) + Cf * R)
          ≤ 64 * (KN * R) := by
        have h1 : Cs1 * R ≤ KN * R :=
          mul_le_mul_of_nonneg_right (by rw [hKNdef]; linarith) hR0
        have h2 : Cs2 * R ≤ KN * R :=
          mul_le_mul_of_nonneg_right (by rw [hKNdef]; linarith) hR0
        have h3 : Ce1 * R ≤ KN * R :=
          mul_le_mul_of_nonneg_right (by rw [hKNdef]; linarith) hR0
        have h4 : Ce2 * R ≤ KN * R :=
          mul_le_mul_of_nonneg_right (by rw [hKNdef]; linarith) hR0
        have h5 : Cf * R ≤ KN * R :=
          mul_le_mul_of_nonneg_right (by rw [hKNdef]; linarith) hR0
        linarith
      have hA0 : 0 ≤ KN0 * R := mul_nonneg hKN00.le hR0
      have hN0' : 0 ≤ KN * R := mul_nonneg hKN0.le hR0
      have hMu0 : 0 ≤ KMU * R := mul_nonneg hKMU0.le hR0
      have hCn0 : 0 ≤ CN * R := mul_nonneg hCN.le hR0
      linarith [hbF, hB23, hBN, hR0, hKN00.le, hKN0.le, hKMU0.le, hCN.le,
        hA0, hN0', hMu0, hCn0]
    -- ## the identification of `gRHS` with the sum on the open quadrant
    have hident : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
        rhsOf α μ lam (Work.Construction.Ftot α f) Φ f z θ = uF z θ := by
      intro z θ hz hθ hθ2
      rw [huF]
      rw [hsum]
      simp only [rhsOf, Work.Construction.gRHS]
      rw [N0split hsmf hz hθ hθ2, hNs z θ hz hθ hθ2]
      try simp only [hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9,
        NSsSum, NSgSum, NGsSum, NGgSum, NFkSum]
      try beta_reduce
      ring_nf
    refine ⟨Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 3 hmFu
      (fun z hz θ hθ => (hident z θ hz hθ.1 hθ.2).symm), ?_⟩
    have hsq : HkSq α 3 (rhsOf α μ lam (Work.Construction.Ftot α f) Φ f) = HkSq α 3 uF :=
      (Work.FTS.EllipticEst.HkSq_congr_open α 3
        (fun z θ hz hθ hθ2 => (hident z θ hz hθ hθ2).symm)).symm
    have hgoal : C3 * R = C3 * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-Cpow) * (1 + M) ^ 4
        * (1 + HkNorm α 6 f) ^ 2 := by
      rw [hRdef, pricedR]; ring
    rw [Work.Spaces.HkNorm, hsq, ← hgoal]
    exact hbFu

end Work.FTS.StrongPersist.L3Rhs
