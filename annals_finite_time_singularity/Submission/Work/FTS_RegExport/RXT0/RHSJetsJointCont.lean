import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS_RegExport.RXT0.DtauAux
import Submission.Work.FTS_RegExport.RXT0.slotJetsJointCont
import Submission.Work.FTS_RegExport.RXT0.L12FKJetsJointCont
import Submission.Work.FTS_RegExport.RXT.Sys.JetCalc.RHSDefs
import Submission.Work.FTS_RegExport.RXT.Sys.JetCalc.RHSSmooth
import Submission.Work.FTS_RegExport.RXT.Sys.GdotAux.mixed_mul_le2
import Submission.Work.FTS_RegExport.RXT.Sys.GdotAux.mixed_Dz_shift
import Submission.Work.FTS_RegExport.RXT.Sys.GdotCore
import Submission.Work.FTS_RegExport.RXT.Sys.CoeffBnd
import Submission.Work.FTS_RegExport.RXT.Sys.CoeffCont
import Submission.Work.FTS_RegExport.RXT.velVanish2Aux
import Submission.Work.FTS_RegExport.RXT.jc3
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.StrongEps.HkMem_of_tendsto
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc
import Submission.Work.FTS_RegExport.RXT0.RXJets.coeffJetsJointCont
import Submission.Work.FTS_RegExport.RXT0.RXJets.L12FKJetsJointCont

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT0.RHSJetsJointCont` — joint continuity of the `RHS` jets (RX-T0)

The target: for a family `g` satisfying the RX-T0 hypotheses, the mixed jets
`D_z^b D_θ^a (RHS α Φs E g σ)`, `a + b ≤ 2`, are jointly continuous on the slab
`z > 0`, `θ ∈ (0,π/2)`, `σ ∈ [0,S]`, for every `S > 0`.

The route is the Leibniz expansion of the three summands of
`RHS σ = -(VR σ · D_zF(σ) + bR σ · D_θF(σ) + cR σ · F(σ))`:

* the *profile* jets `mixed k l (FtauS α g σ)` (`k + l ≤ 3`) are jointly continuous by
  `jc3` (joint continuity of the order-`≤ 3` slice jets) plus the explicit smooth term `F_*`
  (`profileJetsJointCont` below);
* `productJetsCont` turns the profile jets and the (jointly continuous) coefficient jets into
  the continuity of the Leibniz sum;
* the coefficient jets come from the leaves `RXJets.L12FKJetsJointCont` and
  `RXJets.coeffJetsJointCont` (whose input is the proved `RXT0.slotJetsJointCont`);
* `mixed_RHS_eq_Icc` (the `σ ∈ [0,S]` version of `Sys.mixed_RHS_eq`) splits `RHS` into its
  three summands `Afun`, `Bfun`, `Cfun` on the slab, so the result follows from the continuity
  of the three Leibniz products.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT0

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.Regularity (pExp)
open Work.FTS.FinalV2 (Sol DynOK' EllLimOK3)
open Work.FTS.RegExportIface.RXT (GR ΦR μR VR bR cR)

set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}

/-- The RX-T0 slab `(0,∞) × (0,π/2) × [0,S]`. -/
abbrev Slab (S : ℝ) : Set (ℝ × ℝ × ℝ) :=
  Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)

/-! ## §1 The profile jets `mixed k l (F(σ))` are jointly continuous (`k + l ≤ 3`) -/

/-- `FtauS α g σ` agrees with `F_* + slice g σ` on the open quadrant, for `σ ≥ 0`. -/
theorem ftauS_eq_star_add {σ z θ : ℝ} (hσ : 0 ≤ σ) (hz : 0 < z) (hθ : 0 < θ)
    (hθπ : θ < Real.pi / 2) :
    Work.FTS_RegExport.RXT.Sys.FtauS α g σ z θ
      = Work.Construction.Fstar (pExp α) z θ + slice g σ z θ := by
  rw [Work.FTS_RegExport.RXT.Sys.FtauS_apply, Work.FTS.Galerkin.slice_apply]
  rw [Work.FTS_RegExport.RXT.ftau_GR_of_quad (α := α) (g := g) hσ hz hθ.le hθπ.le]

/-- **Joint continuity of the profile jets.**  The mixed jets `mixed k l (FtauS α g σ)` of the
full profile `F(σ) = F_* + g(σ)`, of total order `≤ 3`, are jointly continuous on the slab. -/
theorem profileJetsJointCont (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : DynOK' (pExp α) C₀ Φs E g) :
    ∀ S > 0, ∀ k l : ℕ, k + l ≤ 3 →
      ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        Work.Spaces.mixed k l (Work.FTS_RegExport.RXT.Sys.FtauS α g p.2.2) p.1 p.2.1)
        (Slab S) := by
  intro S hS k l hkl
  have hβ : 0 < pExp α := Work.FTS.Regularity.pExp_pos hα
  have hβ1 : pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  -- the slice jets
  have hjc := Work.FTS_RegExport.RXT.jc3 (C₀ := C₀) (Φs := Φs) (E := E)
    hα hα13 hOK S hS k l hkl
  -- the fixed star term is smooth on the quadrant
  have hF3 : ContDiffOn ℝ 3 (Function.uncurry (Work.Construction.Fstar (pExp α)))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS_RegExport.RXT.Sys.contDiffOn_Fstar_Q0 3 hβ hβ1
  have hstarQ : ContinuousOn (fun q : ℝ × ℝ =>
      Work.Spaces.mixed k l (Work.Construction.Fstar (pExp α)) q.1 q.2)
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongEps.continuousOn_mixed_of_contDiffOn (k := 3) (j := k) (i := l) hF3
      (by omega)
  have hstar : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      Work.Spaces.mixed k l (Work.Construction.Fstar (pExp α)) p.1 p.2.1) (Slab S) :=
    hstarQ.comp ((continuous_fst.prodMk (continuous_fst.comp continuous_snd)).continuousOn)
      (fun p hp => ⟨hp.1, hp.2.1.1, hp.2.1.2⟩)
  -- the pointwise identity on the quadrant
  have hid : Set.EqOn
      (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed k l
        (Work.FTS_RegExport.RXT.Sys.FtauS α g p.2.2) p.1 p.2.1)
      (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed k l (Work.Construction.Fstar (pExp α)) p.1 p.2.1
        + Work.Spaces.mixed k l (slice g p.2.2) p.1 p.2.1) (Slab S) := by
    intro p hp
    obtain ⟨hpz, hpθ, hpσ⟩ := hp
    obtain ⟨hθ0, hθ1⟩ := hpθ
    have hzθ : (p.1, p.2.1) ∈ Work.FTS.EllipticEst.Q0 := ⟨hpz, hθ0, hθ1⟩
    show Work.Spaces.mixed k l (Work.FTS_RegExport.RXT.Sys.FtauS α g p.2.2) p.1 p.2.1
      = Work.Spaces.mixed k l (Work.Construction.Fstar (pExp α)) p.1 p.2.1
        + Work.Spaces.mixed k l (slice g p.2.2) p.1 p.2.1
    have hEqOn : Set.EqOn (Function.uncurry (Work.FTS_RegExport.RXT.Sys.FtauS α g p.2.2))
        (Function.uncurry (fun z θ => Work.Construction.Fstar (pExp α) z θ
          + slice g p.2.2 z θ)) Work.FTS.EllipticEst.Q0 := by
      intro q hq
      obtain ⟨hz, hθ, hθ2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hq
      exact ftauS_eq_star_add (α := α) (g := g) hpσ.1 hz hθ hθ2
    rw [Work.FTS_RegExport.RXT.Sys.mixed_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0
      hEqOn k l p.1 p.2.1 hzθ]
    refine Work.FTS.CoercivityFix.Transfer.E2pkg.mixed_add_of_contDiffOn (n := 3)
      Work.FTS.EllipticEst.isOpen_Q0 hF3 ?_ l k (by omega) (p.1, p.2.1) hzθ
    exact (hOK.1.1.c4 p.2.2 hpσ.1).of_le (by norm_num)
  exact ContinuousOn.congr (hstar.add hjc) hid

/-! ## §2 The generic Leibniz product -/

/-- **Leibniz continuity.**  If a family `V` has jointly continuous jets of order `≤ 2` and a
family `Y` has jointly continuous jets of order `≤ 2`, and both are `C²` in `(z,θ)` for every
`σ ∈ [0,S]`, then the family `V σ · Y σ` has jointly continuous jets of order `≤ 2` on the slab
(the Leibniz sum of jointly continuous products). -/
theorem productJetsCont {V Y : ℝ → ℝ → ℝ → ℝ} {S : ℝ}
    (hVsm : ∀ σ ∈ Set.Icc (0:ℝ) S,
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => V z θ σ)) Work.FTS.EllipticEst.Q0)
    (hYsm : ∀ σ ∈ Set.Icc (0:ℝ) S,
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Y z θ σ)) Work.FTS.EllipticEst.Q0)
    (hVjet : ∀ k l : ℕ, k + l ≤ 2 → ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      Work.Spaces.mixed k l (fun z θ => V z θ p.2.2) p.1 p.2.1) (Slab S))
    (hYjet : ∀ k l : ℕ, k + l ≤ 2 → ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      Work.Spaces.mixed k l (fun z θ => Y z θ p.2.2) p.1 p.2.1) (Slab S))
    {b a : ℕ} (hba : a + b ≤ 2) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      Work.Spaces.mixed b a (fun z θ => V z θ p.2.2 * Y z θ p.2.2) p.1 p.2.1) (Slab S) := by
  -- the Leibniz sum is the continuous object
  have hsum : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      ∑ a' ∈ Finset.range (a + 1), ∑ b' ∈ Finset.range (b + 1),
        ((a.choose a' : ℝ) * (b.choose b' : ℝ))
          * (Work.Spaces.mixed b' a' (fun z θ => V z θ p.2.2) p.1 p.2.1
              * Work.Spaces.mixed (b - b') (a - a') (fun z θ => Y z θ p.2.2) p.1 p.2.1))
      (Slab S) := by
    refine continuousOn_finsetSum _ (fun a' ha' => continuousOn_finsetSum _ (fun b' hb' => ?_))
    have ha'm : a' ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha')
    have hb'm : b' ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb')
    have h1 : (b - b') + (a - a') ≤ 2 := by omega
    have h2 : b' + a' ≤ 2 := by omega
    exact ContinuousOn.const_mul ((hVjet b' a' h2).mul (hYjet (b - b') (a - a') h1)) _
  refine ContinuousOn.congr hsum (fun p hp => ?_)
  exact Work.FTS_RegExport.RXT.Sys.GdotAux.mixed_mul_le2 (j := b) (i := a)
    (hVsm p.2.2 hp.2.2) (hYsm p.2.2 hp.2.2) (by omega) hp.1 hp.2.1.1 hp.2.1.2

/-! ## §3 The `σ ∈ [0,S]` split of `RHS` into its three summands -/

/-- The three summands `Afun`, `Bfun`, `Cfun` of `RHS σ` are `C²` on the open quadrant for every
`σ ≥ 0` (the `σ ∈ (0,S]` version is `Sys.contDiffOn_Afun`). -/
theorem contDiffOn_Afun_Icc (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEL3 : EllLimOK3 (pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (pExp α) Cs Φs)
    (hOK : DynOK' (pExp α) C₀ Φs E g) {σ : ℝ} (hσ : 0 ≤ σ) :
    ContDiffOn ℝ 2 (Function.uncurry (Work.FTS_RegExport.RXT.Sys.Afun α Φs E g σ))
      Work.FTS.EllipticEst.Q0 ∧
    ContDiffOn ℝ 2 (Function.uncurry (Work.FTS_RegExport.RXT.Sys.Bfun α Φs E g σ))
      Work.FTS.EllipticEst.Q0 ∧
    ContDiffOn ℝ 2 (Function.uncurry (Work.FTS_RegExport.RXT.Sys.Cfun α Φs E g σ))
      Work.FTS.EllipticEst.Q0 := by
  obtain ⟨h1, h2, h3⟩ := Work.FTS_RegExport.RXT.coeff_C2 (C₀ := C₀) (Φs := Φs) (E := E)
    (g := g) hα hα13 hEL3 hStar hOK σ hσ
  have hQ3 : ContDiffOn ℝ 3 (Function.uncurry (Work.FTS_RegExport.RXT.Sys.FtauS α g σ))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS_RegExport.RXT.Sys.contDiffOn_FtauS_Q0 hα hα13 hOK (by norm_num) σ hσ
  have hQ2 : ContDiffOn ℝ 2 (Function.uncurry (Work.FTS_RegExport.RXT.Sys.FtauS α g σ))
      Work.FTS.EllipticEst.Q0 := hQ3.of_le (by norm_num)
  have hDz : ContDiffOn ℝ 2
      (Function.uncurry (Work.Spaces.Dz (Work.FTS_RegExport.RXT.Sys.FtauS α g σ)))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongEps.contDiffOn_uncurry_Dz_fin Work.FTS.EllipticEst.isOpen_Q0 hQ3
  have hDth : ContDiffOn ℝ 2
      (Function.uncurry (Work.Spaces.Dth (Work.FTS_RegExport.RXT.Sys.FtauS α g σ)))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongEps.contDiffOn_uncurry_Dth_fin Work.FTS.EllipticEst.isOpen_Q0 hQ3
  exact ⟨(h1.mul hDz).congr (fun _ _ => rfl), (h2.mul hDth).congr (fun _ _ => rfl),
    (h3.mul hQ2).congr (fun _ _ => rfl)⟩

/-- **The pointwise split of the `RHS` jets into the three summands** for `σ ≥ 0`
(the `σ ∈ (0,S]` version is `Sys.mixed_RHS_eq`). -/
theorem mixed_RHS_eq_Icc (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEL3 : EllLimOK3 (pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (pExp α) Cs Φs)
    (hOK : DynOK' (pExp α) C₀ Φs E g) {σ : ℝ} (hσ : 0 ≤ σ) {j i : ℕ} (hji : j + i ≤ 2)
    {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθπ : θ < Real.pi / 2) :
    Work.Spaces.mixed j i (Work.FTS_RegExport.RXT.Sys.RHS α Φs E g σ) z θ
      = - ((Work.Spaces.mixed j i (Work.FTS_RegExport.RXT.Sys.Afun α Φs E g σ) z θ
            + Work.Spaces.mixed j i (Work.FTS_RegExport.RXT.Sys.Bfun α Φs E g σ) z θ)
          + Work.Spaces.mixed j i (Work.FTS_RegExport.RXT.Sys.Cfun α Φs E g σ) z θ) := by
  obtain ⟨hA2, hB2, hC2'⟩ := contDiffOn_Afun_Icc (C₀ := C₀) hα hα13 hEL3 hStar hOK hσ
  have hAB : ContDiffOn ℝ 2 (Function.uncurry
      (Work.FTS_RegExport.RXT.Sys.Afun α Φs E g σ + Work.FTS_RegExport.RXT.Sys.Bfun α Φs E g σ))
      Work.FTS.EllipticEst.Q0 := hA2.add hB2
  have hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ, hθπ⟩
  have hji' : i + j ≤ 2 := by omega
  have hsum : Work.Spaces.mixed j i
      ((Work.FTS_RegExport.RXT.Sys.Afun α Φs E g σ + Work.FTS_RegExport.RXT.Sys.Bfun α Φs E g σ)
        + Work.FTS_RegExport.RXT.Sys.Cfun α Φs E g σ) z θ
      = (Work.Spaces.mixed j i (Work.FTS_RegExport.RXT.Sys.Afun α Φs E g σ) z θ
          + Work.Spaces.mixed j i (Work.FTS_RegExport.RXT.Sys.Bfun α Φs E g σ) z θ)
        + Work.Spaces.mixed j i (Work.FTS_RegExport.RXT.Sys.Cfun α Φs E g σ) z θ := by
    have h1 := Work.FTS.CoercivityFix.Transfer.E2pkg.mixed_add_of_contDiffOn (n := 2)
      Work.FTS.EllipticEst.isOpen_Q0 hAB hC2' i j hji' (z, θ) hp
    have h2 := Work.FTS.CoercivityFix.Transfer.E2pkg.mixed_add_of_contDiffOn (n := 2)
      Work.FTS.EllipticEst.isOpen_Q0 hA2 hB2 i j hji' (z, θ) hp
    rw [h1, h2]
  have hneg := congrFun (congrFun (Work.FTS_RegExport.RXT.Sys.mixed_neg j i
    ((Work.FTS_RegExport.RXT.Sys.Afun α Φs E g σ + Work.FTS_RegExport.RXT.Sys.Bfun α Φs E g σ)
      + Work.FTS_RegExport.RXT.Sys.Cfun α Φs E g σ)) z) θ
  rw [Work.FTS_RegExport.RXT.Sys.RHS_eq_neg_sum_fun, hneg, hsum]

/-! ## §4 The assembly -/

/-- **The `RHS` jets from the coefficient jets.**  If the order-`≤ 2` mixed jets of the three
coefficients `VR`, `bR`, `cR` are jointly continuous on the slab, so are those of `RHS`. -/
theorem RHSJetsJointCont_of_coeff
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEL3 : EllLimOK3 (pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (pExp α) Cs Φs)
    (hOK : DynOK' (pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S) {b a : ℕ} (hba : a + b ≤ 2)
    (hVR : ∀ k l : ℕ, k + l ≤ 2 → ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      Work.Spaces.mixed k l (fun z θ => VR α Φs E g z θ p.2.2) p.1 p.2.1) (Slab S))
    (hbR : ∀ k l : ℕ, k + l ≤ 2 → ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      Work.Spaces.mixed k l (fun z θ => bR α Φs E g z θ p.2.2) p.1 p.2.1) (Slab S))
    (hcR : ∀ k l : ℕ, k + l ≤ 2 → ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      Work.Spaces.mixed k l (fun z θ => cR α Φs E g z θ p.2.2) p.1 p.2.1) (Slab S)) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      Work.Spaces.mixed b a (Work.FTS_RegExport.RXT.Sys.RHS α Φs E g p.2.2) p.1 p.2.1)
      (Slab S) := by
  have hC2 := Work.FTS_RegExport.RXT.coeff_C2 (C₀ := C₀) (Φs := Φs) (E := E) (g := g)
    hα hα13 hEL3 hStar hOK
  -- the profile is `C³` on the quadrant at every `σ ∈ [0,S]`
  have hW3 : ∀ σ ∈ Set.Icc (0:ℝ) S, ContDiffOn ℝ 3
      (Function.uncurry (Work.FTS_RegExport.RXT.Sys.FtauS α g σ))
      Work.FTS.EllipticEst.Q0 :=
    fun σ hσ => Work.FTS_RegExport.RXT.Sys.contDiffOn_FtauS_Q0 hα hα13 hOK (by norm_num) σ hσ.1
  -- the shifted profile jets
  have hYjetDz : ∀ k l : ℕ, k + l ≤ 2 → ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      Work.Spaces.mixed k l (fun z θ =>
        Work.Spaces.Dz (Work.FTS_RegExport.RXT.Sys.FtauS α g p.2.2) z θ) p.1 p.2.1)
      (Slab S) := by
    intro k l hkl
    refine ContinuousOn.congr (profileJetsJointCont (C₀ := C₀) hα hα13 hOK S hS (k + 1) l
      (by omega)) (fun p hp => ?_)
    show Work.Spaces.mixed k l (fun z θ =>
        Work.Spaces.Dz (Work.FTS_RegExport.RXT.Sys.FtauS α g p.2.2) z θ) p.1 p.2.1
      = Work.Spaces.mixed (k + 1) l (Work.FTS_RegExport.RXT.Sys.FtauS α g p.2.2) p.1 p.2.1
    exact Work.FTS_RegExport.RXT.Sys.GdotAux.mixed_Dz_shift (hW3 p.2.2 hp.2.2) (by omega)
      hp.1 hp.2.1.1 hp.2.1.2
  have hYjetDth : ∀ k l : ℕ, k + l ≤ 2 → ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      Work.Spaces.mixed k l (fun z θ =>
        Work.Spaces.Dth (Work.FTS_RegExport.RXT.Sys.FtauS α g p.2.2) z θ) p.1 p.2.1)
      (Slab S) := by
    intro k l hkl
    refine ContinuousOn.congr (profileJetsJointCont (C₀ := C₀) hα hα13 hOK S hS k (l + 1)
      (by omega)) (fun p hp => ?_)
    show Work.Spaces.mixed k l (fun z θ =>
        Work.Spaces.Dth (Work.FTS_RegExport.RXT.Sys.FtauS α g p.2.2) z θ) p.1 p.2.1
      = Work.Spaces.mixed k (l + 1) (Work.FTS_RegExport.RXT.Sys.FtauS α g p.2.2) p.1 p.2.1
    rw [Work.FTS_RegExport.RXT.Sys.mixed_Dth_succ]
  have hYjetF : ∀ k l : ℕ, k + l ≤ 2 → ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      Work.Spaces.mixed k l (fun z θ =>
        Work.FTS_RegExport.RXT.Sys.FtauS α g p.2.2 z θ) p.1 p.2.1) (Slab S) :=
    fun k l hkl => profileJetsJointCont (C₀ := C₀) hα hα13 hOK S hS k l (by omega)
  -- the three Leibniz products
  have hA : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      Work.Spaces.mixed b a (fun z θ => VR α Φs E g z θ p.2.2
        * Work.Spaces.Dz (Work.FTS_RegExport.RXT.Sys.FtauS α g p.2.2) z θ) p.1 p.2.1)
      (Slab S) :=
    productJetsCont (V := fun z θ σ => VR α Φs E g z θ σ)
      (Y := fun z θ σ => Work.Spaces.Dz (Work.FTS_RegExport.RXT.Sys.FtauS α g σ) z θ)
      (fun σ hσ => (hC2 σ hσ.1).1)
      (fun σ hσ => Work.FTS.StrongEps.contDiffOn_uncurry_Dz_fin
        Work.FTS.EllipticEst.isOpen_Q0 (hW3 σ hσ))
      hVR hYjetDz hba
  have hB : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      Work.Spaces.mixed b a (fun z θ => bR α Φs E g z θ p.2.2
        * Work.Spaces.Dth (Work.FTS_RegExport.RXT.Sys.FtauS α g p.2.2) z θ) p.1 p.2.1)
      (Slab S) :=
    productJetsCont (V := fun z θ σ => bR α Φs E g z θ σ)
      (Y := fun z θ σ => Work.Spaces.Dth (Work.FTS_RegExport.RXT.Sys.FtauS α g σ) z θ)
      (fun σ hσ => (hC2 σ hσ.1).2.1)
      (fun σ hσ => Work.FTS.StrongEps.contDiffOn_uncurry_Dth_fin
        Work.FTS.EllipticEst.isOpen_Q0 (hW3 σ hσ))
      hbR hYjetDth hba
  have hC : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      Work.Spaces.mixed b a (fun z θ => cR α Φs E g z θ p.2.2
        * Work.FTS_RegExport.RXT.Sys.FtauS α g p.2.2 z θ) p.1 p.2.1) (Slab S) :=
    productJetsCont (V := fun z θ σ => cR α Φs E g z θ σ)
      (Y := fun z θ σ => Work.FTS_RegExport.RXT.Sys.FtauS α g σ z θ)
      (fun σ hσ => (hC2 σ hσ.1).2.2)
      (fun σ hσ => (hW3 σ hσ).of_le (by norm_num))
      hcR hYjetF hba
  refine ContinuousOn.congr ((hA.add hB).add hC).neg (fun p hp => ?_)
  show Work.Spaces.mixed b a (Work.FTS_RegExport.RXT.Sys.RHS α Φs E g p.2.2) p.1 p.2.1
    = - ((Work.Spaces.mixed b a (Work.FTS_RegExport.RXT.Sys.Afun α Φs E g p.2.2) p.1 p.2.1
          + Work.Spaces.mixed b a (Work.FTS_RegExport.RXT.Sys.Bfun α Φs E g p.2.2) p.1 p.2.1)
        + Work.Spaces.mixed b a (Work.FTS_RegExport.RXT.Sys.Cfun α Φs E g p.2.2) p.1 p.2.1)
  exact mixed_RHS_eq_Icc (C₀ := C₀) (j := b) (i := a) hα hα13 hEL3 hStar hOK hp.2.2.1
    (by omega) hp.1 hp.2.1.1 hp.2.1.2

theorem RHSJetsJointCont {α C₀ Ce Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hμ : Work.FTS.RegExportIface.ClockBd α Φs E g) :
    ∀ S > 0, ∀ b a : ℕ, a + b ≤ 2 →
      ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        Work.Spaces.mixed b a
          (Work.FTS_RegExport.RXT.Sys.RHS α Φs E g p.2.2) p.1 p.2.1)
        (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)) := by
  intro S hS b a hba
  -- the two inputs of the coefficient-jet leaf
  have hL12 := Work.FTS_RegExport.RXT0.RXJets.L12FKJetsJointCont (C₀ := C₀) (Φs := Φs) (E := E)
    (g := g) hα hα13 hOK
  have hSlot := Work.FTS_RegExport.RXT0.slotJetsJointCont (C₀ := C₀) (Ce := Ce) (Cs := Cs)
    (Φs := Φs) (E := E) (g := g) hα hα13 hEll hEL3 hSol hOK
  -- the coefficient jets
  have hcoeff := Work.FTS_RegExport.RXT0.RXJets.coeffJetsJointCont (C₀ := C₀) (Ce := Ce) (Cs := Cs)
    (Φs := Φs) (E := E) (g := g) hα hα13 hEll hEL3 hStar hSol hOK hμ hL12 hSlot
  exact RHSJetsJointCont_of_coeff (C₀ := C₀) (Cs := Cs) (Φs := Φs) (E := E) (g := g)
    hα hα13 hEL3 hStar hOK hS hba
    (fun k l hkl => (hcoeff S hS k l hkl).1)
    (fun k l hkl => (hcoeff S hS k l hkl).2.1)
    (fun k l hkl => (hcoeff S hS k l hkl).2.2)

end Work.FTS_RegExport.RXT0
