/-
# `CoupledVfs` — the `ℋ³`-bound for `Mf f · Vfs α`

Part of the assembly of `Work.FTS.StrongPersist.L3Rhs.N0gCoupled`.  The star part `Vfs α` of
`Bf α f` is *separated*: `Vfs α z θ = VfsA1 α θ · VfsRad z + VfsA2 α θ · VfsRadZ z`
(`N0gAuxDefs`), and `Mf f · Vfs α` is estimated by the separated-majorant estimate
`HkIntegrand_sep_le` together with the angular mass bound `VfsAngMass` and the radial slot
bound `VfsRadSlotBound`.

Here: the smoothness of the two angular profiles and of the two radial profiles, the
nonnegativity of the angular majorants, the radial slot functional `Sz`, and the pointwise
bound `P2_integrand_le`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongPersist.L3Rhs.N0gDecomp
import Submission.Work.FTS.StrongPersist.L3Rhs.N0gAuxDefs
import Submission.Work.FTS.StrongPersist.L3Rhs.CoupledVf
import Submission.Work.FTS.StrongPersist.Degen.FstarSqAux
import Submission.Work.FTS.StrongPersist.Basic
import Submission.Work.FTS.StrongPersist.L3Aux.HkIntegrand_sep_le
import Submission.Work.FTS.StrongPersist.L3Aux.acoef_gamCoef_slots_le
import Submission.Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.PthIter2VftsAux
import Submission.Work.FTS.EllipticEst.EllHyp_certificates

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
set_option maxHeartbeats 1600000

theorem contDiffOn_gc_top (α : ℝ) :
    ContDiffOn ℝ ⊤ (fun θ : ℝ => Work.Spaces.Gam α θ / Work.Spaces.c α) (Set.Ioo 0 (π / 2)) := by
  have hbase : ContDiffOn ℝ ⊤ (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2)
      (Set.Ioo (0 : ℝ) (π / 2)) :=
    (Real.contDiff_sin.contDiffOn).mul ((Real.contDiff_cos.contDiffOn).pow 2)
  have hne : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), Real.sin θ * Real.cos θ ^ 2 ≠ 0 := by
    intro θ hθ
    have h1 : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have h2 : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    positivity
  have hgam : ContDiffOn ℝ ⊤ (fun θ : ℝ => Work.Spaces.Gam α θ) (Set.Ioo (0 : ℝ) (π / 2)) :=
    hbase.rpow_const_of_ne hne
  simpa only [VfsGc] using hgam.div_const (Work.Spaces.c α)

theorem contDiffOn_VfsA1 (α : ℝ) :
    ContDiffOn ℝ 3 (VfsA1 α) (Set.Ioo (0 : ℝ) (π / 2)) := by
  have hgc : ContDiffOn ℝ 4 (fun θ : ℝ => VfsGc α θ) (Set.Ioo (0 : ℝ) (π / 2)) :=
    (contDiffOn_gc_top α).of_le (by norm_num : ((4 : ℕ) : WithTop ℕ∞) ≤ ⊤)
  have hd : ContDiffOn ℝ 3 (deriv (fun θ : ℝ => VfsGc α θ)) (Set.Ioo (0 : ℝ) (π / 2)) :=
    hgc.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hs2 : ContDiffOn ℝ 3 (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo (0 : ℝ) (π / 2)) := by
    fun_prop
  have hprod : ContDiffOn ℝ 3 (fun θ : ℝ =>
      deriv (fun θ : ℝ => VfsGc α θ) θ * Real.sin (2 * θ)) (Set.Ioo (0 : ℝ) (π / 2)) :=
    hd.mul hs2
  have hcs := (contDiffOn_const (c := (3 / 2 : ℝ)) (s := Set.Ioo (0 : ℝ) (π / 2))).mul hprod
  refine hcs.congr (fun θ _ => ?_)
  simp only [VfsA1, Work.Spaces.dthU]
  ring

theorem contDiffOn_VfsA2 (α : ℝ) :
    ContDiffOn ℝ 3 (VfsA2 α) (Set.Ioo (0 : ℝ) (π / 2)) := by
  have hc2m : ContDiffOn ℝ 3 (fun θ : ℝ => Real.cos (2 * θ) - Real.sin θ ^ 2)
      (Set.Ioo (0 : ℝ) (π / 2)) := by fun_prop
  have hgc : ContDiffOn ℝ 3 (fun θ : ℝ => VfsGc α θ) (Set.Ioo (0 : ℝ) (π / 2)) :=
    (contDiffOn_gc_top α).of_le (by norm_num : ((3 : ℕ) : WithTop ℕ∞) ≤ ⊤)
  have hprod : ContDiffOn ℝ 3 (fun θ : ℝ =>
      (Real.cos (2 * θ) - Real.sin θ ^ 2) * VfsGc α θ) (Set.Ioo (0 : ℝ) (π / 2)) :=
    hc2m.mul hgc
  have hcs := (contDiffOn_const (c := -α) (s := Set.Ioo (0 : ℝ) (π / 2))).mul hprod
  refine hcs.congr (fun θ _ => ?_)
  simp only [VfsA2, Work.Construction.c2m_eq]
  ring

theorem contDiffOn_VfsRad (n : ℕ) : ContDiffOn ℝ n VfsRad (Set.Ioi (0 : ℝ)) := by
  have h : ContDiffOn ℝ n (fun z : ℝ => (2 * z) / (1 + z) ^ 2) (Set.Ioi (0 : ℝ)) := by
    refine ContDiffOn.div (by fun_prop) (by fun_prop) (fun z hz => ?_)
    have hz' : (0 : ℝ) < z := Set.mem_Ioi.mp hz
    have h4 : (0 : ℝ) < (1 + z) ^ 2 := by positivity
    exact ne_of_gt h4
  refine ContDiffOn.congr h (fun z _ => ?_)
  simp only [VfsRad]

theorem contDiffOn_VfsRadZ (n : ℕ) : ContDiffOn ℝ n VfsRadZ (Set.Ioi (0 : ℝ)) := by
  have hd : ContDiffOn ℝ n (deriv VfsRad) (Set.Ioi (0 : ℝ)) :=
    (contDiffOn_VfsRad (n + 1)).deriv_of_isOpen isOpen_Ioi (by simp)
  have hm : ContDiffOn ℝ n (fun z : ℝ => z * deriv VfsRad z) (Set.Ioi (0 : ℝ)) :=
    contDiffOn_id.mul hd
  refine ContDiffOn.congr hm (fun z _ => ?_)
  simp only [VfsRadZ, Work.Spaces.Zop]

theorem angMaj_nonneg (α : ℝ) (C : ℝ → ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ angMaj α C θ := by
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  simp only [angMaj]
  refine add_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs _)) ?_
  refine Finset.sum_nonneg fun i _ => ?_
  split_ifs with hi
  · exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs _)
  · exact le_refl 0

theorem VfsAngMaj_nonneg {α : ℝ} {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ VfsAngMaj α θ := by
  simp only [VfsAngMaj]
  exact add_nonneg (angMaj_nonneg α (VfsA1 α) hθ) (angMaj_nonneg α (VfsA2 α) hθ)

/-- The weighted radial slot sum attached to the radial factor `B`. -/
def Sz (f : Fn) (B : ℝ → ℝ) (z : ℝ) : ℝ :=
  ∑ q ∈ Finset.range 4, (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z * B z) z 0) ^ 2
    * (Work.Spaces.w z) ^ 2

/-- **The pointwise bound for `Mf f · Vfs α`.** -/
theorem P2_integrand_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : Fn}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (hsep : ∀ z θ : ℝ, Vfs α z θ = VfsA1 α θ * VfsRad z + VfsA2 α θ * VfsRadZ z) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 3 (fun z θ => Mf f z θ * Vfs α z θ) z θ
        ≤ 2 * (angMaj α (VfsA1 α) θ * Sz f VfsRad z + angMaj α (VfsA2 α) θ * Sz f VfsRadZ z) := by
  intro z hz θ hθ
  have hVfsep : (fun z θ => Mf f z θ * Vfs α z θ)
      = fun z θ => VfsA1 α θ * (Work.Construction.L12 f z * VfsRad z)
          + VfsA2 α θ * (Work.Construction.L12 f z * VfsRadZ z) := by
    funext z θ
    rw [hsep z θ, Mf]
    ring
  -- smoothness of the two separated terms
  have hL12 : ContDiffOn ℝ 3 (fun z : ℝ => Work.Construction.L12 f z) (Set.Ioi (0 : ℝ)) :=
    (Work.FTS.EllipticEst.UopHk.contDiffOn_L12_k α 4 f hα hα1 hso hmem
      (by norm_num)).of_le (by norm_num)
  have hB1 : ContDiffOn ℝ 3 (fun z : ℝ => Work.Construction.L12 f z * VfsRad z)
      (Set.Ioi (0 : ℝ)) := hL12.mul (contDiffOn_VfsRad 3)
  have hB2 : ContDiffOn ℝ 3 (fun z : ℝ => Work.Construction.L12 f z * VfsRadZ z)
      (Set.Ioi (0 : ℝ)) := hL12.mul (contDiffOn_VfsRadZ 3)
  have hA1 : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => VfsA1 α p.2) Work.FTS.EllipticEst.Q0 :=
    (contDiffOn_VfsA1 α).comp contDiffOn_snd
      (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).2)
  have hA2 : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => VfsA2 α p.2) Work.FTS.EllipticEst.Q0 :=
    (contDiffOn_VfsA2 α).comp contDiffOn_snd
      (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).2)
  have hB1q : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => Work.Construction.L12 f p.1 * VfsRad p.1)
      Work.FTS.EllipticEst.Q0 :=
    hB1.comp contDiffOn_fst (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
  have hB2q : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => Work.Construction.L12 f p.1 * VfsRadZ p.1)
      Work.FTS.EllipticEst.Q0 :=
    hB2.comp contDiffOn_fst (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
  have hT1 : ContDiffOn ℝ 3 (Function.uncurry
      (fun z θ => VfsA1 α θ * (Work.Construction.L12 f z * VfsRad z)))
      Work.FTS.EllipticEst.Q0 := hA1.mul hB1q
  have hT2 : ContDiffOn ℝ 3 (Function.uncurry
      (fun z θ => VfsA2 α θ * (Work.Construction.L12 f z * VfsRadZ z)))
      Work.FTS.EllipticEst.Q0 := hA2.mul hB2q
  rw [hVfsep]
  have hadd : Work.Spaces.HkIntegrand α 3 (fun z θ =>
        VfsA1 α θ * (Work.Construction.L12 f z * VfsRad z)
          + VfsA2 α θ * (Work.Construction.L12 f z * VfsRadZ z)) z θ
      ≤ 2 * Work.Spaces.HkIntegrand α 3
          (fun z θ => VfsA1 α θ * (Work.Construction.L12 f z * VfsRad z)) z θ
        + 2 * Work.Spaces.HkIntegrand α 3
          (fun z θ => VfsA2 α θ * (Work.Construction.L12 f z * VfsRadZ z)) z θ :=
    Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.HkIntegrand_add_le_domain α 3 hT1 hT2 z hz θ hθ
  have hS1 : Work.Spaces.HkIntegrand α 3
        (fun z θ => VfsA1 α θ * (Work.Construction.L12 f z * VfsRad z)) z θ
      ≤ angMaj α (VfsA1 α) θ * Sz f VfsRad z :=
    Work.FTS.StrongPersist.L3Aux.HkIntegrand_sep_le (α := α) (C := VfsA1 α)
      (B := fun z => Work.Construction.L12 f z * VfsRad z) (z := z) (θ := θ) hθ
  have hS2 : Work.Spaces.HkIntegrand α 3
        (fun z θ => VfsA2 α θ * (Work.Construction.L12 f z * VfsRadZ z)) z θ
      ≤ angMaj α (VfsA2 α) θ * Sz f VfsRadZ z :=
    Work.FTS.StrongPersist.L3Aux.HkIntegrand_sep_le (α := α) (C := VfsA2 α)
      (B := fun z => Work.Construction.L12 f z * VfsRadZ z) (z := z) (θ := θ) hθ
  calc Work.Spaces.HkIntegrand α 3 (fun z θ =>
        VfsA1 α θ * (Work.Construction.L12 f z * VfsRad z)
          + VfsA2 α θ * (Work.Construction.L12 f z * VfsRadZ z)) z θ
      ≤ 2 * Work.Spaces.HkIntegrand α 3
          (fun z θ => VfsA1 α θ * (Work.Construction.L12 f z * VfsRad z)) z θ
        + 2 * Work.Spaces.HkIntegrand α 3
          (fun z θ => VfsA2 α θ * (Work.Construction.L12 f z * VfsRadZ z)) z θ := hadd
    _ ≤ 2 * (angMaj α (VfsA1 α) θ * Sz f VfsRad z)
        + 2 * (angMaj α (VfsA2 α) θ * Sz f VfsRadZ z) :=
        add_le_add (mul_le_mul_of_nonneg_left hS1 (by norm_num))
          (mul_le_mul_of_nonneg_left hS2 (by norm_num))
    _ = 2 * (angMaj α (VfsA1 α) θ * Sz f VfsRad z
        + angMaj α (VfsA2 α) θ * Sz f VfsRadZ z) := by ring

theorem Sz_nonneg (f : Fn) (B : ℝ → ℝ) (z : ℝ) : 0 ≤ Sz f B z := by
  simp only [Sz]
  exact Finset.sum_nonneg fun q _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)

theorem jets_VfsRad : ∀ b ≤ 4, ∀ z ∈ Work.Spaces.Iz,
    |Work.Spaces.Zop^[b] VfsRad z| ≤ 24000 := by
  intro b hb z hz
  have h2 : |Work.Spaces.DzIter b (fun z (_ : ℝ) => 2 * z / (1 + z) ^ 2) z 0| ≤ 24000 :=
    Work.FTS.StrongPersist.L3Aux.zslot_supBound b hb z hz 0
      ⟨le_refl 0, by linarith [Real.pi_pos]⟩
  have hfun : (fun z => Work.Spaces.DzIter b (fun z (_ : ℝ) => 2 * z / (1 + z) ^ 2) z 0)
      = Work.Spaces.Zop^[b] VfsRad := by
    rw [Work.Spaces.Zop_slice b (fun z (_ : ℝ) => 2 * z / (1 + z) ^ 2) 0]
    rfl
  rw [← congrFun hfun z]
  exact h2

theorem jets_VfsRadZ : ∀ b ≤ 3, ∀ z ∈ Work.Spaces.Iz,
    |Work.Spaces.Zop^[b] VfsRadZ z| ≤ 24000 := by
  intro b hb z hz
  have h1 : Work.Spaces.Zop^[b] VfsRadZ = Work.Spaces.Zop^[b + 1] VfsRad := by
    have hz0 : VfsRadZ = Work.Spaces.Zop VfsRad := rfl
    rw [hz0]
    exact (Function.iterate_succ_apply Work.Spaces.Zop b VfsRad).symm
  rw [h1]
  exact jets_VfsRad (b + 1) (by omega) z hz

/-- `Vfs α` is `C^∞` on the open quadrant. -/
theorem smoothOpen_Vfs (α : ℝ) : Work.FTS.EllipticEst.SmoothOpen (Vfs α) := by
  have hF : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.StrongPersist.Degen.smoothOpen_Fstar α
  have ha : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (3 / (2 * α)) * (Real.sin (2 * θ)
        * Work.Spaces.pth (Work.Construction.Fstar α) z θ)) :=
    contDiffOn_const.mul (smoothOpen_sin_two.mul hF.pth)
  have hb : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (Real.cos (2 * θ) - Real.sin θ ^ 2)
        * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) :=
    smoothOpen_c2m.mul hF.Dz
  have hmain : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      (3 / (2 * α)) * (Real.sin (2 * θ) * Work.Spaces.pth (Work.Construction.Fstar α) z θ)
        - (Real.cos (2 * θ) - Real.sin θ ^ 2)
          * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) := ha.sub hb
  have hfun : (fun z θ =>
      (3 / (2 * α)) * (Real.sin (2 * θ) * Work.Spaces.pth (Work.Construction.Fstar α) z θ)
        - (Real.cos (2 * θ) - Real.sin θ ^ 2)
          * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) = Vfs α := by
    funext z θ
    simp only [Vfs, Work.Construction.s2_eq, Work.Construction.c2m_eq]
    ring
  rwa [hfun] at hmain

/-- `Bf α f` is `C^∞` on the open quadrant for `f` smooth there. -/
theorem smoothOpen_Bf {α : ℝ} {f : Fn} (hso : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (Bf α f) := by
  have hmain : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Vf α f z θ + Vfs α z θ) :=
    (smoothOpen_Vf hso).add (smoothOpen_Vfs α)
  have hfun : (fun z θ => Vf α f z θ + Vfs α z θ) = Bf α f := by
    funext z θ
    simp only [Bf]
  rwa [hfun] at hmain

end Work.FTS.StrongPersist.L3Rhs
