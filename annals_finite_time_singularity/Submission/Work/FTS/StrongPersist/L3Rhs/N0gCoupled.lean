import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.StrongEps.EpsE4Thr.JepsJoint.Jeps_fam_continuous
import Submission.Work.FTS.StrongPersist.L3Rhs.CoupledVf
import Submission.Work.FTS.StrongPersist.L3Rhs.CoupledVfs
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.L3Rhs.N0gAuxDefs
import Submission.Work.FTS.StrongPersist.L3Rhs.VfsAngMass
import Submission.Work.FTS.StrongPersist.L3Rhs.VfsSep
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.leibnizRem6
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS_MuLamOK.Rows.Rl1Defs

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
open Work.Spaces (HkIntegrand HkMem HkNorm HkSq Dz Dth pth)

set_option autoImplicit false
set_option maxHeartbeats 3900000

/-! ## The assembly -/

/-- The pure arithmetic of the final bound: from the two halves of the energy estimate,

`2 (Zc (1 + Cjet a)² CV t) Nx²` and `4 Km (2 Cs a²)` (with `t = (α^{-1})²`, `1 ≤ t`),

one reaches the square of the stated bound, where the losses are `(1+a)² ≤ (1+M)²`,
`Nx² ≤ (1+Nx)²`, `a² ≤ (1+M)²`, `1 ≤ t`, `C ≤ (C+1)²` and
`(1+M)²(1+Nx)² ≤ (1+M)^8(1+Nx)^4`. -/
private theorem coupled_arith {Zc CV Cjet Km Cs t α M Nx a : ℝ}
    (hZc : 0 ≤ Zc) (hCV : 0 ≤ CV) (hCjet : 0 ≤ Cjet) (hKm : 0 ≤ Km) (hCs : 0 ≤ Cs)
    (hM : 0 ≤ M) (hNx : 0 ≤ Nx) (ha : 0 ≤ a) (haM : a ≤ M) (hα : 0 < α)
    (ht : t = (α ^ (-(1 : ℝ))) ^ 2) (ht1 : 1 ≤ t) :
    2 * (Zc * (1 + Cjet * a) ^ 2 * CV * t) * Nx ^ 2 + 4 * Km * (2 * Cs * a ^ 2)
      ≤ ((2 * (Zc * (1 + Cjet) ^ 2 * CV) + 8 * Km * Cs + 1) * α ^ (-(1 : ℝ))
          * (1 + M) ^ 4 * (1 + Nx) ^ 2) ^ 2 := by
  set A1 : ℝ := 2 * (Zc * (1 + Cjet) ^ 2 * CV) with hA1
  set A2 : ℝ := 8 * Km * Cs with hA2
  set CC : ℝ := A1 + A2 + 1 with hCC
  set tY : ℝ := t * ((1 + M) ^ 2 * (1 + Nx) ^ 2) with htY
  have hA1nn : 0 ≤ A1 := by rw [hA1]; positivity
  have hA2nn : 0 ≤ A2 := by rw [hA2]; positivity
  have hCCnn : 0 ≤ CC := by rw [hCC]; linarith [hA1nn, hA2nn]
  have htnn : 0 ≤ t := le_trans zero_le_one ht1
  have hYnn : 0 ≤ (1 + M) ^ 2 * (1 + Nx) ^ 2 := by positivity
  have htYnn : 0 ≤ tY := by rw [htY]; positivity
  -- the `Vf`-half
  have e1 : 2 * (Zc * (1 + Cjet * a) ^ 2 * CV * t) * Nx ^ 2 ≤ A1 * tY := by
    have h1 : (1 + Cjet * a) ^ 2 ≤ (1 + Cjet) ^ 2 * (1 + a) ^ 2 := by
      have hle : 1 + Cjet * a ≤ (1 + Cjet) * (1 + a) := by nlinarith [ha, hCjet]
      calc (1 + Cjet * a) ^ 2 ≤ ((1 + Cjet) * (1 + a)) ^ 2 :=
            pow_le_pow_left₀ (by positivity) hle 2
        _ = (1 + Cjet) ^ 2 * (1 + a) ^ 2 := by ring
    have h2 : (1 + a) ^ 2 ≤ (1 + M) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    have h4 : Nx ^ 2 ≤ (1 + Nx) ^ 2 := pow_le_pow_left₀ hNx (by linarith) 2
    have h1' : (1 + Cjet * a) ^ 2 ≤ (1 + Cjet) ^ 2 * (1 + M) ^ 2 :=
      le_trans h1 (mul_le_mul_of_nonneg_left h2 (sq_nonneg _))
    have hK : 0 ≤ 2 * Zc * CV * t := by positivity
    calc 2 * (Zc * (1 + Cjet * a) ^ 2 * CV * t) * Nx ^ 2
        = (2 * Zc * CV * t) * ((1 + Cjet * a) ^ 2 * Nx ^ 2) := by ring
      _ ≤ (2 * Zc * CV * t)
            * (((1 + Cjet) ^ 2 * (1 + M) ^ 2) * (1 + Nx) ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ hK
          exact mul_le_mul h1' h4 (sq_nonneg _) (by positivity)
      _ = A1 * tY := by rw [hA1, htY]; ring
  -- the `Vfs`-half
  have e2 : 4 * Km * (2 * Cs * a ^ 2) ≤ A2 * tY := by
    have hb2 : a ^ 2 ≤ (1 + M) ^ 2 * (1 + Nx) ^ 2 := by
      have h2 : a ^ 2 ≤ (1 + M) ^ 2 :=
        pow_le_pow_left₀ ha (by linarith) 2
      have h5 : (1 : ℝ) ≤ (1 + Nx) ^ 2 := by nlinarith [hNx]
      calc a ^ 2 ≤ (1 + M) ^ 2 := h2
        _ = (1 + M) ^ 2 * 1 := by ring
        _ ≤ (1 + M) ^ 2 * (1 + Nx) ^ 2 := mul_le_mul_of_nonneg_left h5 (by positivity)
    have h1 : 4 * Km * (2 * Cs * a ^ 2) ≤ 4 * Km * (2 * Cs * ((1 + M) ^ 2 * (1 + Nx) ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb2 (by positivity)) (by positivity)
    have h2 : 4 * Km * (2 * Cs * ((1 + M) ^ 2 * (1 + Nx) ^ 2)) ≤ A2 * tY := by
      have h6 : (1 : ℝ) ≤ t := ht1
      calc 4 * Km * (2 * Cs * ((1 + M) ^ 2 * (1 + Nx) ^ 2))
          = A2 * ((1 + M) ^ 2 * (1 + Nx) ^ 2) := by rw [hA2]; ring
        _ = A2 * ((1 + M) ^ 2 * (1 + Nx) ^ 2) * 1 := by ring
        _ ≤ A2 * ((1 + M) ^ 2 * (1 + Nx) ^ 2) * t :=
            mul_le_mul_of_nonneg_left h6 (by positivity)
        _ = A2 * tY := by rw [htY]; ring
    linarith [h1, h2]
  -- combine and square
  have hsum : 2 * (Zc * (1 + Cjet * a) ^ 2 * CV * t) * Nx ^ 2 + 4 * Km * (2 * Cs * a ^ 2)
      ≤ (A1 + A2) * tY := by
    have h := add_le_add e1 e2
    rw [add_mul]
    linarith [h]
  have hfinal : (A1 + A2) * tY ≤ (CC * α ^ (-(1 : ℝ)) * (1 + M) ^ 4 * (1 + Nx) ^ 2) ^ 2 := by
    have hle : A1 + A2 ≤ CC ^ 2 := by rw [hCC]; nlinarith [hA1nn, hA2nn]
    have hpow : (1 + M) ^ 2 * (1 + Nx) ^ 2 ≤ (1 + M) ^ 8 * (1 + Nx) ^ 4 := by
      have h1 : (1 + M) ^ 2 ≤ (1 + M) ^ 8 :=
        pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + M) (by norm_num)
      have h2 : (1 + Nx) ^ 2 ≤ (1 + Nx) ^ 4 :=
        pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + Nx) (by norm_num)
      exact mul_le_mul h1 h2 (by positivity) (by positivity)
    have hsq : (CC * α ^ (-(1 : ℝ)) * (1 + M) ^ 4 * (1 + Nx) ^ 2) ^ 2
        = CC ^ 2 * t * (1 + M) ^ 8 * (1 + Nx) ^ 4 := by
      rw [ht]
      ring
    rw [hsq, htY]
    calc (A1 + A2) * (t * ((1 + M) ^ 2 * (1 + Nx) ^ 2))
        ≤ CC ^ 2 * (t * ((1 + M) ^ 2 * (1 + Nx) ^ 2)) := by
          refine mul_le_mul_of_nonneg_right hle ?_
          exact mul_nonneg htnn hYnn
      _ ≤ CC ^ 2 * (t * ((1 + M) ^ 8 * (1 + Nx) ^ 4)) := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg CC)
          exact mul_le_mul_of_nonneg_left hpow htnn
      _ = CC ^ 2 * t * (1 + M) ^ 8 * (1 + Nx) ^ 4 := by ring
  linarith [hsum, hfinal]

/-- **The assembly of `N0gCoupled`** from the four ingredients (the uniform jet bound for
`L₁₂ f`, the angular mass bound, the radial slot bound and the separation identity). -/
theorem N0gCoupled_aux
    (hjetAll : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ g : ℝ → ℝ → ℝ,
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
      Work.Construction.L12 g 0 = 0 → ∀ b ≤ 3, ∀ z ∈ Set.Ioi (0 : ℝ),
        |Work.Spaces.Zop^[b] (fun z => Work.Construction.L12 g z) z|
          ≤ C * Work.Spaces.HkNorm α 4 g)
    (hmassAll : ∃ K : ℝ, 0 < K ∧ ∀ α ∈ Set.Ioc 0 1,
      MeasureTheory.IntegrableOn (VfsAngMaj α) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, VfsAngMaj α θ) ≤ K)
    (hslotAll : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (B : ℝ → ℝ),
      0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      Work.Construction.L12 f 0 = 0 → ContDiffOn ℝ 4 B (Set.Ioi (0 : ℝ)) →
      (∀ b ≤ 3, ∀ z ∈ Work.Spaces.Iz, |Work.Spaces.Zop^[b] B z| ≤ 24000) →
      MeasureTheory.IntegrableOn (fun z => ∑ q ∈ Finset.range 4,
          (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z * B z) z 0) ^ 2
            * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
        (∫ z in Work.Spaces.Iz, ∑ q ∈ Finset.range 4,
          (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z * B z) z 0) ^ 2
            * (Work.Spaces.w z) ^ 2) ≤ C * Work.Spaces.HkSq α 4 f)
    (hsep : ∀ α z θ : ℝ, Vfs α z θ = VfsA1 α θ * VfsRad z + VfsA2 α θ * VfsRadZ z) :
    ∃ C Cpow α₂ : ℝ, 0 < C ∧ 0 ≤ Cpow ∧ 0 < α₂ ∧
      ∀ α ∈ Set.Ioc 0 α₂, ∀ (f : Fn) (M : ℝ),
        Work.FTS.StrongPersist.H6Adm α f → Work.FTS.Nonlin.Xn α f ≤ M →
        Work.Spaces.HkMem α 3 (fun z θ => Mf f z θ * Bf α f z θ) ∧
        Work.Spaces.HkNorm α 3 (fun z θ => Mf f z θ * Bf α f z θ)
          ≤ C * α ^ (-Cpow) * (1 + M) ^ 4 * (1 + Work.FTS.StrongPersist.Xn6 α f) ^ 2 := by
  obtain ⟨Cjet, hCjetpos, hjet⟩ := hjetAll
  obtain ⟨Kmass, hKmasspos, hmass⟩ := hmassAll
  obtain ⟨Cslot, hCslotpos, hslot⟩ := hslotAll
  obtain ⟨CV, hCVpos, hVfb⟩ := Vf_integrand_le
  have hZcpos : 0 < Work.FTS.StrongPersist.L3Aux.zmulConst 3 :=
    Work.FTS.StrongPersist.L3Aux.zmulConst_pos 3
  refine ⟨2 * (Work.FTS.StrongPersist.L3Aux.zmulConst 3 * (1 + Cjet) ^ 2 * CV)
      + 8 * Kmass * Cslot + 1, 1, 1, by positivity, by norm_num, one_pos, ?_⟩
  intro α hαIoc f M hadm hM
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  have hso : Work.FTS.EllipticEst.SmoothOpen f := hadm.reg.1
  have hmem6 : Work.Spaces.HkMem α 6 f := hadm.reg.2
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hso 4 (by norm_num) hmem6
  have hl12 : Work.Construction.L12 f 0 = 0 := hadm.l12
  have hAM : Work.Spaces.HkNorm α 4 f ≤ M := hM
  have hAnn : 0 ≤ Work.Spaces.HkNorm α 4 f := Real.sqrt_nonneg _
  have hMnn : 0 ≤ M := le_trans hAnn hAM
  have hXn6nn : 0 ≤ Work.FTS.StrongPersist.Xn6 α f := Real.sqrt_nonneg _
  have hAN : Work.Spaces.HkNorm α 4 f ≤ Work.FTS.StrongPersist.Xn6 α f :=
    Work.FTS.StrongLWP.HkNorm_mono_of_mem (α := α) (k := 6) (k' := 4) (by norm_num) hmem6
  -- ### the four ingredients
  have hjetf : ∀ b ≤ 3, ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Spaces.Zop^[b] (fun z => Work.Construction.L12 f z) z|
        ≤ Cjet * Work.Spaces.HkNorm α 4 f :=
    fun b hb z hz => hjet α hα hα1 f hso hmem4 hl12 b hb z hz
  have hVfbd : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 3 (Vf α f) z θ
        ≤ CV * (1 / α) ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ := hVfb α hα hα1 f hso
  have hP1bd : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 3 (fun z θ => Mf f z θ * Vf α f z θ) z θ
        ≤ Work.FTS.StrongPersist.L3Aux.zmulConst 3
            * (1 + Cjet * Work.Spaces.HkNorm α 4 f) ^ 2 * CV * (1 / α) ^ 2
              * Work.Spaces.HkIntegrand α 6 f z θ :=
    fun z hz θ hθ => P1_integrand_le hα hα1 hso hmem4 hl12 hCjetpos.le hjetf hVfbd z hz θ hθ
  have hP2bd : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 3 (fun z θ => Mf f z θ * Vfs α z θ) z θ
        ≤ 2 * (angMaj α (VfsA1 α) θ * Sz f VfsRad z
            + angMaj α (VfsA2 α) θ * Sz f VfsRadZ z) :=
    fun z hz θ hθ => P2_integrand_le hα hα1 hso hmem4 (hsep α) z hz θ hθ
  have hsz1 : MeasureTheory.IntegrableOn (fun z => Sz f VfsRad z) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, Sz f VfsRad z) ≤ Cslot * Work.Spaces.HkSq α 4 f :=
    hslot α f VfsRad hα hα1 hso hmem4 hl12 (contDiffOn_VfsRad 4)
      (fun b hb z hz => jets_VfsRad b (by omega) z hz)
  have hsz2 : MeasureTheory.IntegrableOn (fun z => Sz f VfsRadZ z) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, Sz f VfsRadZ z) ≤ Cslot * Work.Spaces.HkSq α 4 f :=
    hslot α f VfsRadZ hα hα1 hso hmem4 hl12 (contDiffOn_VfsRadZ 4)
      (fun b hb z hz => jets_VfsRadZ b hb z hz)
  have hmassα := hmass α hαIoc
  -- ### the majorant
  set C1 : ℝ := Work.FTS.StrongPersist.L3Aux.zmulConst 3
      * (1 + Cjet * Work.Spaces.HkNorm α 4 f) ^ 2 * CV * (1 / α) ^ 2 with hC1def
  have hC1nn : 0 ≤ C1 := by rw [hC1def]; positivity
  set Mj : ℝ → ℝ → ℝ := fun z θ => 2 * C1 * Work.Spaces.HkIntegrand α 6 f z θ
      + 4 * (VfsAngMaj α θ * (Sz f VfsRad z + Sz f VfsRadZ z)) with hMjdef
  -- ### smoothness of the two halves
  have hVfso : Work.FTS.EllipticEst.SmoothOpen (Vf α f) := smoothOpen_Vf hso
  have hVfsso : Work.FTS.EllipticEst.SmoothOpen (Vfs α) := smoothOpen_Vfs α
  have hBfso : Work.FTS.EllipticEst.SmoothOpen (Bf α f) := smoothOpen_Bf hso
  have hL124 : ContDiffOn ℝ 4 (fun z : ℝ => Work.Construction.L12 f z) (Set.Ioi (0 : ℝ)) :=
    Work.FTS.EllipticEst.UopHk.contDiffOn_L12_k α 4 f hα hα1 hso hmem4 (by norm_num)
  have hMf4 : ContDiffOn ℝ 4 (fun p : ℝ × ℝ => Work.Construction.L12 f p.1)
      Work.FTS.EllipticEst.Q0 :=
    hL124.comp ((contDiff_fst.contDiffOn).of_le le_top)
      (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
  have hMf3 : ContDiffOn ℝ 3 (Function.uncurry (Mf f)) Work.FTS.EllipticEst.Q0 :=
    hMf4.of_le (by norm_num)
  have hVf3 : ContDiffOn ℝ 3 (Function.uncurry (fun z θ => Mf f z θ * Vf α f z θ))
      Work.FTS.EllipticEst.Q0 := hMf3.mul (hVfso.forall 3)
  have hVfs3 : ContDiffOn ℝ 3 (Function.uncurry (fun z θ => Mf f z θ * Vfs α z θ))
      Work.FTS.EllipticEst.Q0 := hMf3.mul (hVfsso.forall 3)
  have hBfeq : (fun z θ => Mf f z θ * Bf α f z θ)
      = fun z θ => Mf f z θ * Vf α f z θ + Mf f z θ * Vfs α z θ := by
    funext z θ
    simp only [Bf]
    ring
  have hsum3 : ContDiffOn ℝ 3 (Function.uncurry (fun z θ => Mf f z θ * Bf α f z θ))
      Work.FTS.EllipticEst.Q0 := by
    rw [hBfeq]
    exact hVf3.add hVfs3
  -- ### the pointwise majorisation
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 3 (fun z θ => Mf f z θ * Bf α f z θ) z θ ≤ Mj z θ := by
    intro z hz θ hθ
    have hadd := Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.HkIntegrand_add_le_domain α 3
      hVf3 hVfs3 z hz θ hθ
    have h1 := hP1bd z hz θ hθ
    have h2 := hP2bd z hz θ hθ
    have hAmaj : angMaj α (VfsA1 α) θ * Sz f VfsRad z
          + angMaj α (VfsA2 α) θ * Sz f VfsRadZ z
        ≤ VfsAngMaj α θ * (Sz f VfsRad z + Sz f VfsRadZ z) := by
      have h1' : 0 ≤ angMaj α (VfsA1 α) θ := angMaj_nonneg α _ hθ
      have h2' : 0 ≤ angMaj α (VfsA2 α) θ := angMaj_nonneg α _ hθ
      have h3' : 0 ≤ Sz f VfsRad z := Sz_nonneg f VfsRad z
      have h4' : 0 ≤ Sz f VfsRadZ z := Sz_nonneg f VfsRadZ z
      rw [VfsAngMaj]
      nlinarith [h1', h2', h3', h4']
    have key : 2 * Work.Spaces.HkIntegrand α 3 (fun z θ => Mf f z θ * Vf α f z θ) z θ
          + 2 * Work.Spaces.HkIntegrand α 3 (fun z θ => Mf f z θ * Vfs α z θ) z θ
        ≤ Mj z θ := by
      rw [hMjdef]
      nlinarith [h1, h2, hAmaj, Work.Spaces.HkIntegrand_nonneg α 6 f z θ]
    rw [hBfeq]
    exact le_trans hadd key
  -- ### integrability of the majorant
  have hinner : ∀ z ∈ Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ, Mj z θ)
      = 2 * C1 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ)
        + 4 * ((∫ θ in Work.Spaces.Iθ, VfsAngMaj α θ)
            * (Sz f VfsRad z + Sz f VfsRadZ z)) := by
    intro z hz
    rw [hMjdef]
    have ha : MeasureTheory.IntegrableOn
        (fun θ => 2 * C1 * Work.Spaces.HkIntegrand α 6 f z θ) Work.Spaces.Iθ :=
      (hmem6.1 z hz).const_mul _
    have hb : MeasureTheory.IntegrableOn
        (fun θ => 4 * (VfsAngMaj α θ * (Sz f VfsRad z + Sz f VfsRadZ z))) Work.Spaces.Iθ :=
      (hmassα.1.mul_const _).const_mul 4
    rw [MeasureTheory.integral_add ha hb, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const]
  have hMjslice : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ => Mj z θ)
      Work.Spaces.Iθ := by
    intro z hz
    have h1 : MeasureTheory.IntegrableOn (fun θ => 2 * C1 * Work.Spaces.HkIntegrand α 6 f z θ)
        Work.Spaces.Iθ := (hmem6.1 z hz).const_mul _
    have h2 : MeasureTheory.IntegrableOn
        (fun θ => 4 * (VfsAngMaj α θ * (Sz f VfsRad z + Sz f VfsRadZ z))) Work.Spaces.Iθ :=
      (hmassα.1.mul_const _).const_mul 4
    rw [show (fun θ => Mj z θ) = fun θ => 2 * C1 * Work.Spaces.HkIntegrand α 6 f z θ
        + 4 * (VfsAngMaj α θ * (Sz f VfsRad z + Sz f VfsRadZ z)) from by
      funext θ; rw [hMjdef]]
    exact h1.add h2
  have hMjz : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, Mj z θ)
      Work.Spaces.Iz := by
    have hbase : MeasureTheory.IntegrableOn (fun z =>
        2 * C1 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ)
          + 4 * ((∫ θ in Work.Spaces.Iθ, VfsAngMaj α θ)
              * (Sz f VfsRad z + Sz f VfsRadZ z))) Work.Spaces.Iz :=
      (hmem6.2.const_mul _).add (((hsz1.1.add hsz2.1).const_mul _).const_mul _)
    refine hbase.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_Ici (a := (0 : ℝ)))] with z hz
    exact (hinner z hz).symm
  -- ### the value of the integral of the majorant
  have houter : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Mj z θ)
      = 2 * C1 * Work.Spaces.HkSq α 6 f
        + 4 * ((∫ θ in Work.Spaces.Iθ, VfsAngMaj α θ)
            * (∫ z in Work.Spaces.Iz, (Sz f VfsRad z + Sz f VfsRadZ z))) := by
    have hae : (fun z => ∫ θ in Work.Spaces.Iθ, Mj z θ)
        =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
        (fun z => 2 * C1 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ)
          + 4 * ((∫ θ in Work.Spaces.Iθ, VfsAngMaj α θ)
              * (Sz f VfsRad z + Sz f VfsRadZ z))) := by
      filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_Ici (a := (0 : ℝ)))]
        with z hz
      exact hinner z hz
    rw [MeasureTheory.integral_congr_ae hae]
    have ha : MeasureTheory.IntegrableOn
        (fun z => 2 * C1 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ))
        Work.Spaces.Iz := hmem6.2.const_mul _
    have hb : MeasureTheory.IntegrableOn (fun z =>
        4 * ((∫ θ in Work.Spaces.Iθ, VfsAngMaj α θ)
            * (Sz f VfsRad z + Sz f VfsRadZ z))) Work.Spaces.Iz :=
      ((hsz1.1.add hsz2.1).const_mul _).const_mul 4
    rw [MeasureTheory.integral_add ha hb]
    have h1 : (∫ z in Work.Spaces.Iz,
          2 * C1 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ))
        = 2 * C1 * Work.Spaces.HkSq α 6 f := by
      rw [MeasureTheory.integral_const_mul]
      rfl
    have h2 : (∫ z in Work.Spaces.Iz,
          4 * ((∫ θ in Work.Spaces.Iθ, VfsAngMaj α θ)
            * (Sz f VfsRad z + Sz f VfsRadZ z)))
        = 4 * ((∫ θ in Work.Spaces.Iθ, VfsAngMaj α θ)
            * (∫ z in Work.Spaces.Iz, (Sz f VfsRad z + Sz f VfsRadZ z))) := by
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    rw [h1, h2]
  -- ### the two slot/mass bounds
  have hSzbound : (∫ z in Work.Spaces.Iz, (Sz f VfsRad z + Sz f VfsRadZ z))
      ≤ 2 * (Cslot * Work.Spaces.HkSq α 4 f) := by
    rw [MeasureTheory.integral_add hsz1.1 hsz2.1]
    linarith [hsz1.2, hsz2.2]
  have hHkSq6 : Work.Spaces.HkSq α 6 f = (Work.FTS.StrongPersist.Xn6 α f) ^ 2 :=
    (Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 f)).symm
  have hHkSq4 : Work.Spaces.HkSq α 4 f = (Work.Spaces.HkNorm α 4 f) ^ 2 :=
    (Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 f)).symm
  have hWnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, VfsAngMaj α θ :=
    setIntegral_nonneg measurableSet_Icc (fun θ hθ => VfsAngMaj_nonneg (α := α) hθ)
  have hSznn : 0 ≤ ∫ z in Work.Spaces.Iz, (Sz f VfsRad z + Sz f VfsRadZ z) :=
    setIntegral_nonneg measurableSet_Ici (fun z _ => by
      have h1 := Sz_nonneg f VfsRad z
      have h2 := Sz_nonneg f VfsRadZ z
      linarith)
  have ht1 : (1 : ℝ) ≤ (1 / α) ^ 2 := by
    rw [div_pow, one_pow]
    exact one_le_one_div (by positivity) (by nlinarith [hα1, hα])
  have hNn1 : (1 : ℝ) ≤ (1 + Work.FTS.StrongPersist.Xn6 α f) ^ 2 := by nlinarith [hXn6nn]
  -- ### the energy estimate and the norm bound
  have hW1 : (∫ θ in Work.Spaces.Iθ, VfsAngMaj α θ) ≤ Kmass := hmassα.2
  have hcomb : 4 * ((∫ θ in Work.Spaces.Iθ, VfsAngMaj α θ)
        * (∫ z in Work.Spaces.Iz, (Sz f VfsRad z + Sz f VfsRadZ z)))
      ≤ 4 * Kmass * (2 * Cslot * (Work.Spaces.HkNorm α 4 f) ^ 2) := by
    have h1 : (∫ θ in Work.Spaces.Iθ, VfsAngMaj α θ)
          * (∫ z in Work.Spaces.Iz, (Sz f VfsRad z + Sz f VfsRadZ z))
        ≤ Kmass * (2 * (Cslot * Work.Spaces.HkSq α 4 f)) :=
      mul_le_mul hW1 hSzbound hSznn hKmasspos.le
    rw [hHkSq4] at h1
    nlinarith [h1]
  have hHkSq : Work.Spaces.HkSq α 3 (fun z θ => Mf f z θ * Bf α f z θ)
      ≤ 2 * (Work.FTS.StrongPersist.L3Aux.zmulConst 3
          * (1 + Cjet * Work.Spaces.HkNorm α 4 f) ^ 2 * CV * (1 / α) ^ 2)
          * (Work.FTS.StrongPersist.Xn6 α f) ^ 2
        + 4 * Kmass * (2 * Cslot * (Work.Spaces.HkNorm α 4 f) ^ 2) := by
    have hmain : Work.Spaces.HkSq α 3 (fun z θ => Mf f z θ * Bf α f z θ)
        ≤ 2 * C1 * Work.Spaces.HkSq α 6 f
          + 4 * ((∫ θ in Work.Spaces.Iθ, VfsAngMaj α θ)
              * (∫ z in Work.Spaces.Iz, (Sz f VfsRad z + Sz f VfsRadZ z))) := by
      rw [Work.Spaces.HkSq, ← houter]
      refine MeasureTheory.integral_mono_of_nonneg ?_ hMjz ?_
      · exact Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
          Work.Spaces.HkIntegrand_nonneg α 3 _ z θ
      · filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_Ici (a := (0 : ℝ)))]
          with z hz
        refine MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 3 _ z θ)
          (hMjslice z hz) ?_
        exact (MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc).mpr
          (Filter.Eventually.of_forall fun θ hθ => hpt z hz θ hθ)
    have hC1eq : C1 = Work.FTS.StrongPersist.L3Aux.zmulConst 3
        * (1 + Cjet * Work.Spaces.HkNorm α 4 f) ^ 2 * CV * (1 / α) ^ 2 := hC1def
    calc Work.Spaces.HkSq α 3 (fun z θ => Mf f z θ * Bf α f z θ)
        ≤ 2 * C1 * Work.Spaces.HkSq α 6 f
          + 4 * ((∫ θ in Work.Spaces.Iθ, VfsAngMaj α θ)
              * (∫ z in Work.Spaces.Iz, (Sz f VfsRad z + Sz f VfsRadZ z))) := hmain
      _ = 2 * (Work.FTS.StrongPersist.L3Aux.zmulConst 3
            * (1 + Cjet * Work.Spaces.HkNorm α 4 f) ^ 2 * CV * (1 / α) ^ 2)
            * (Work.FTS.StrongPersist.Xn6 α f) ^ 2
          + 4 * ((∫ θ in Work.Spaces.Iθ, VfsAngMaj α θ)
              * (∫ z in Work.Spaces.Iz, (Sz f VfsRad z + Sz f VfsRadZ z))) := by
          rw [hC1eq, hHkSq6]
      _ ≤ 2 * (Work.FTS.StrongPersist.L3Aux.zmulConst 3
            * (1 + Cjet * Work.Spaces.HkNorm α 4 f) ^ 2 * CV * (1 / α) ^ 2)
            * (Work.FTS.StrongPersist.Xn6 α f) ^ 2
          + 4 * Kmass * (2 * Cslot * (Work.Spaces.HkNorm α 4 f) ^ 2) := by
          linarith [hcomb]
  refine ⟨?_, ?_⟩
  · refine Work.FTS.LocData.HkMem_of_majorant α 3 ?_ hMjslice hMjz hpt
    rw [hBfeq]
    exact Work.FTS.EllipticEst.Cores.DiagEstEllT.continuousOn_HkIntegrand_of_contDiffOn
      (hVf3.add hVfs3) α
  · have harith := coupled_arith (Zc := Work.FTS.StrongPersist.L3Aux.zmulConst 3)
      (CV := CV) (Cjet := Cjet) (Km := Kmass) (Cs := Cslot) (t := (1 / α) ^ 2)
      (α := α) (M := M) (Nx := Work.FTS.StrongPersist.Xn6 α f)
      (a := Work.Spaces.HkNorm α 4 f)
      (le_of_lt hZcpos) (le_of_lt hCVpos) (le_of_lt hCjetpos) (le_of_lt hKmasspos)
      (le_of_lt hCslotpos) hMnn hXn6nn hAnn hAM hα
      (by rw [Real.rpow_neg_one, one_div]) ht1
    have hsq : Work.Spaces.HkSq α 3 (fun z θ => Mf f z θ * Bf α f z θ)
        ≤ ((2 * (Work.FTS.StrongPersist.L3Aux.zmulConst 3 * (1 + Cjet) ^ 2 * CV)
            + 8 * Kmass * Cslot + 1) * α ^ (-(1 : ℝ)) * (1 + M) ^ 4
              * (1 + Work.FTS.StrongPersist.Xn6 α f) ^ 2) ^ 2 :=
      le_trans hHkSq harith
    have hLnn : 0 ≤ (2 * (Work.FTS.StrongPersist.L3Aux.zmulConst 3 * (1 + Cjet) ^ 2 * CV)
        + 8 * Kmass * Cslot + 1) * α ^ (-(1 : ℝ)) * (1 + M) ^ 4
          * (1 + Work.FTS.StrongPersist.Xn6 α f) ^ 2 := by
      have h1 : 0 ≤ α ^ (-(1 : ℝ)) := Real.rpow_nonneg hα.le _
      have h2 : 0 ≤ (1 + M) ^ 4 := by positivity
      have h3 : 0 ≤ (1 + Work.FTS.StrongPersist.Xn6 α f) ^ 2 := by positivity
      have h4 : 0 ≤ 2 * (Work.FTS.StrongPersist.L3Aux.zmulConst 3 * (1 + Cjet) ^ 2 * CV)
          + 8 * Kmass * Cslot + 1 := by positivity
      exact mul_nonneg (mul_nonneg (mul_nonneg h4 h1) h2) h3
    rw [show Work.Spaces.HkNorm α 3 (fun z θ => Mf f z θ * Bf α f z θ)
        = Real.sqrt (Work.Spaces.HkSq α 3 (fun z θ => Mf f z θ * Bf α f z θ)) from rfl]
    calc Real.sqrt (Work.Spaces.HkSq α 3 (fun z θ => Mf f z θ * Bf α f z θ))
        ≤ Real.sqrt (((2 * (Work.FTS.StrongPersist.L3Aux.zmulConst 3 * (1 + Cjet) ^ 2 * CV)
            + 8 * Kmass * Cslot + 1) * α ^ (-(1 : ℝ)) * (1 + M) ^ 4
              * (1 + Work.FTS.StrongPersist.Xn6 α f) ^ 2) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = (2 * (Work.FTS.StrongPersist.L3Aux.zmulConst 3 * (1 + Cjet) ^ 2 * CV)
            + 8 * Kmass * Cslot + 1) * α ^ (-(1 : ℝ)) * (1 + M) ^ 4
              * (1 + Work.FTS.StrongPersist.Xn6 α f) ^ 2 := Real.sqrt_sq hLnn

/-- **The coupled half of the `N0gSum`-estimate** — the requested statement. -/
theorem N0gCoupled : ∃ C Cpow α₂ : ℝ, 0 < C ∧ 0 ≤ Cpow ∧ 0 < α₂ ∧
    ∀ α ∈ Set.Ioc 0 α₂, ∀ (f : Work.FTS.Galerkin.Fn) (M : ℝ),
      Work.FTS.StrongPersist.H6Adm α f → Work.FTS.Nonlin.Xn α f ≤ M →
      Work.Spaces.HkMem α 3
          (fun z θ => Work.FTS.StrongPersist.L3Rhs.Mf f z θ
            * Work.FTS.StrongPersist.L3Rhs.Bf α f z θ) ∧
      Work.Spaces.HkNorm α 3
          (fun z θ => Work.FTS.StrongPersist.L3Rhs.Mf f z θ
            * Work.FTS.StrongPersist.L3Rhs.Bf α f z θ)
        ≤ C * α ^ (-Cpow) * (1 + M) ^ 4 * (1 + Work.FTS.StrongPersist.Xn6 α f) ^ 2 := by
  obtain ⟨Cjet, hCjet, hjet⟩ := Work.FTS.StrongPersist.L3Rhs.L12fJetUniform
  obtain ⟨Kmass, hKmass, hmass⟩ := Work.FTS.StrongPersist.L3Rhs.VfsAngMass
  obtain ⟨Cslot, hCslot, hslot⟩ := Work.FTS.StrongPersist.L3Rhs.VfsRadSlotBound
  exact N0gCoupled_aux ⟨Cjet, hCjet, hjet⟩ ⟨Kmass, hKmass, hmass⟩ ⟨Cslot, hCslot, hslot⟩
    Work.FTS.StrongPersist.L3Rhs.VfsSep

end Work.FTS.StrongPersist.L3Rhs
