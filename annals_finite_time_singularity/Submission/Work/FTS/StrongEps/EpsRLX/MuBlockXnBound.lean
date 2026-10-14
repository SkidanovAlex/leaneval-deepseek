import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.GalFields.RHS.HkSum
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.radA_traces
import Submission.Work.FTS.StrongEps.EpsE4Thr.regQo_const_mul
import Submission.Work.FTS.StrongEps.EpsSqTools.HkSqJepsPzPre
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundR
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_RegExport.RXT.Slots.v2_theta_sup_uniform
import Submission.Work.FTS_RegExport.RXT.starVop
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.H2.T1Q.SupAbsThOAesm
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.Slot_eq_of_source =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EComparison

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn)

/-- **The slots of the packages depend only on the source** — the assembled form of the comparison
that the `EpsLocal` reduction (`EComparison.E_slots_diff_eq`) consumes.

`EComparison.EllPkgCls α Ce F Ψ` is the membership half of the packages `EllPkgGo`/`EllPkgK`
(`SmoothOpen Ψ`, `IsBslSol α F Ψ`, and `HQo α 6` of the three slots `SlotR/SlotU/SlotV` — the
modifications `Rop α (PhiTil α F Ψ)`, `Uop α (PhiTil α F Ψ)/sin 2θ`, `Vop (PhiTil α F Ψ)`).  The
assertion is that two elements of the class with the *same* source have the same slots **on the open
quadrant** `0 < z`, `θ ∈ (0, π/2)`.

The quadrant restriction is essential and was required by two reviews: `SmoothOpen` is smoothness on
`Q0 = (0,∞) × (0,π/2)` only, `IsBslSol` constrains the law only there, and `HkMem` integrates only
over `Iz × Iθ = [0,∞) × [0,π/2]`, so `EllPkgCls` is blind to the values of `Ψ` outside the closed
quadrant (a bump supported in `θ > π/2` is invisible to every hypothesis yet changes the slots).
Nothing is lost downstream: the slots are consumed only through `HkSq`/`HkMem`, whose integrands see
`z > 0`, `θ ∈ (0,π/2)` a.e. and vanish at `z = 0`.

Both ingredients are already proved in this workspace, `sorry`-free:
* `Work.FTS.StrongEps.EComparison.EllPkgCls_sub` — the class is closed under differences, so
  `(fun z θ => F z θ - F z θ, fun z θ => Ψ₁ z θ - Ψ₂ z θ)` is in the class (its `hΘ` hypothesis is
  discharged by `Theta α (fun z θ => F z θ - F z θ) = Theta α 0`, which follows from
  `L12dens`-congruence of the identically zero integrand plus
  `MeasureTheory.setIntegral_congr_fun`);
* `Work.FTS.StrongEps.EComparison.HomClsSlotsZero` — a *homogeneous* element of the class
  (`IsBslSol α 0 w`, `SmoothOpen w`, `HkMem α 6` of the three slots of `w`) has all three slots
  vanishing on the open quadrant.

The remaining formal step is the identification of the degenerate source `fun z θ => F z θ - F z θ`
with `fun _ _ => 0`: the pointwise law becomes `bslOp α (Ψ₁ - Ψ₂) = 0` by `sub_self`, the Dirichlet
and decay conjuncts are source-free, and `PhiTil α (F - F) (Ψ₁ - Ψ₂)` agrees with
`PhiTil α 0 (Ψ₁ - Ψ₂)` because `PhiTil α F' Ψ = Ψ - Theta α F'` and the two `Theta`s are equal. -/
theorem Slot_eq_of_source {α Ce : ℝ} {F Ψ₁ Ψ₂ : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (h₁ : Work.FTS.StrongEps.EComparison.EllPkgCls α Ce F Ψ₁)
    (h₂ : Work.FTS.StrongEps.EComparison.EllPkgCls α Ce F Ψ₂) :
    (∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2),
        Work.FTS.StrongEps.EComparison.SlotR α F Ψ₁ z θ
          = Work.FTS.StrongEps.EComparison.SlotR α F Ψ₂ z θ) ∧
    (∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2),
        Work.FTS.StrongEps.EComparison.SlotU α F Ψ₁ z θ
          = Work.FTS.StrongEps.EComparison.SlotU α F Ψ₂ z θ) ∧
    (∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2),
        Work.FTS.StrongEps.EComparison.SlotV α F Ψ₁ z θ
          = Work.FTS.StrongEps.EComparison.SlotV α F Ψ₂ z θ) := by
  have hαne : α ≠ 0 := ne_of_gt hα
  -- ## The degenerate source `F - F` has vanishing `L₁₂` and `Θ`
  have hL12z : ∀ z, Work.Construction.L12 (fun z θ => F z θ - F z θ) z = 0 := by
    intro z
    have hfun : (fun z θ => F z θ - F z θ) = (fun _ _ => (0 : ℝ)) := by
      funext z θ
      ring
    rw [hfun]
    simp [Work.Construction.L12, Work.FM.L12, Work.FM.L12dens]
  have hThetaG : Work.Construction.Theta α (fun z θ => F z θ - F z θ) = fun _ _ => (0 : ℝ) := by
    funext z θ
    simp only [Work.Construction.Theta]
    rw [hL12z z]
    ring
  have hΘ : ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      Work.Construction.Theta α (fun z θ => F z θ - F z θ) z θ
        = Work.Construction.Theta α F z θ - Work.Construction.Theta α F z θ := by
    intro z _ θ
    rw [hThetaG]
    simp
  -- ## The difference lies in the class
  have hsub : EllPkgCls α Ce (fun z θ => F z θ - F z θ) (fun z θ => Ψ₁ z θ - Ψ₂ z θ) :=
    EllPkgCls_sub h₁ h₂ hΘ
  have hPhiTilG : Work.Construction.PhiTil α (fun z θ => F z θ - F z θ)
      (fun z θ => Ψ₁ z θ - Ψ₂ z θ) = fun z θ => Ψ₁ z θ - Ψ₂ z θ := by
    funext z θ
    simp only [Work.Construction.PhiTil, hThetaG, sub_zero]
  -- ## the hypotheses of `HomClsSlotsZero` for the stream function difference
  have hsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Ψ₁ z θ - Ψ₂ z θ) := hsub.1
  have hsol : Work.Elliptic.IsBslSol α (fun _ _ => (0 : ℝ)) (fun z θ => Ψ₁ z θ - Ψ₂ z θ) := by
    refine ⟨?_, hsub.2.1.2.1, hsub.2.1.2.2.1, hsub.2.1.2.2.2⟩
    intro z hz θ h0 h1
    simpa using hsub.2.1.1 z hz θ h0 h1
  have hR : Work.Spaces.HkMem α 6
      (Work.Construction.Rop α (fun z θ => Ψ₁ z θ - Ψ₂ z θ)) := by
    simpa only [hPhiTilG] using hsub.2.2.1.2
  have hU : Work.Spaces.HkMem α 6
      (fun z θ => Work.Construction.Uop α (fun z θ => Ψ₁ z θ - Ψ₂ z θ) z θ
        / Work.Construction.s2 θ) := by
    simpa only [hPhiTilG] using hsub.2.2.2.1.2
  have hV : Work.Spaces.HkMem α 6
      (Work.Construction.Vop (fun z θ => Ψ₁ z θ - Ψ₂ z θ)) := by
    simpa only [hPhiTilG] using hsub.2.2.2.2.2
  -- ## all three slots of the difference vanish on the open quadrant
  obtain ⟨hRz, hUz, hVz⟩ :=
    HomClsSlotsZero (w := fun z θ => Ψ₁ z θ - Ψ₂ z θ) hα hα1 hsm hsol hR hU hV
  -- ## the slots of the two elements differ by the slots of the difference
  have hu : ∀ z, 0 < z → DifferentiableAt ℝ
      (fun z' => (1 / (4 * α)) * Work.Construction.L12 F z') z :=
    fun z hz => (differentiableAt_L12_of_Vop hαne h₁.1 h₁.2.2.2.2.1 hz).const_mul (1 / (4 * α))
  have hpz_sub : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.pz (fun z θ => Ψ₁ z θ - Ψ₂ z θ) z θ
        = Work.Spaces.pz (Work.Construction.PhiTil α F Ψ₁) z θ
          - Work.Spaces.pz (Work.Construction.PhiTil α F Ψ₂) z θ := by
    intro z θ hz h0 h1
    rw [pz_sub h₁.1 h₂.1 hz h0 h1,
      pz_PhiTil_eq (F := F) (Ψ := Ψ₁) h₁.1 (hu z hz) hz h0 h1,
      pz_PhiTil_eq (F := F) (Ψ := Ψ₂) h₂.1 (hu z hz) hz h0 h1]
    ring
  have hpth_sub : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.pth (fun z θ => Ψ₁ z θ - Ψ₂ z θ) z θ
        = Work.Spaces.pth (Work.Construction.PhiTil α F Ψ₁) z θ
          - Work.Spaces.pth (Work.Construction.PhiTil α F Ψ₂) z θ := by
    intro z θ hz h0 h1
    rw [pth_sub h₁.1 h₂.1 hz h0 h1,
      pth_PhiTil_eq (F := F) (Ψ := Ψ₁) h₁.1 hz h0 h1,
      pth_PhiTil_eq (F := F) (Ψ := Ψ₂) h₂.1 hz h0 h1]
    ring
  have hval : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      (fun z θ => Ψ₁ z θ - Ψ₂ z θ) z θ
        = Work.Construction.PhiTil α F Ψ₁ z θ - Work.Construction.PhiTil α F Ψ₂ z θ := by
    intro z θ _ _ _
    simp only [Work.Construction.PhiTil, Work.Construction.Theta, Work.Construction.s2]
    ring
  obtain ⟨hsR, hsU, hsV⟩ := slot_identities (α := α)
    (A := fun z θ => Ψ₁ z θ - Ψ₂ z θ)
    (P₁ := Work.Construction.PhiTil α F Ψ₁)
    (P₂ := Work.Construction.PhiTil α F Ψ₂) hval hpz_sub hpth_sub
  refine ⟨?_, ?_, ?_⟩
  · intro z hz θ hθ
    have h := hsR z θ hz hθ.1 hθ.2
    have h0 := hRz z hz θ hθ
    simp only [SlotR]
    linarith
  · intro z hz θ hθ
    have h := hsU z θ hz hθ.1 hθ.2
    have h0 := hUz z hz θ hθ
    have hUeq : Work.Construction.Uop α (Work.Construction.PhiTil α F Ψ₁) z θ
        = Work.Construction.Uop α (Work.Construction.PhiTil α F Ψ₂) z θ := by linarith
    simp only [SlotU]
    rw [hUeq]
  · intro z hz θ hθ
    have h := hsV z θ hz hθ.1 hθ.2
    have h0 := hVz z hz θ hθ
    simp only [SlotV]
    linarith

end Work.FTS.StrongEps.EComparison
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRLX.MuBlockXnBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsRLX

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Elementary tools for `Xn` -/

/-- `Xn` only sees the values on the open quadrant. -/
private theorem Xn_congr_open (α : ℝ) {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → f z θ = g z θ) :
    Work.FTS.Nonlin.Xn α f = Work.FTS.Nonlin.Xn α g := by
  rw [show Work.FTS.Nonlin.Xn α f = Work.Spaces.HkNorm α 4 f from rfl,
    show Work.FTS.Nonlin.Xn α g = Work.Spaces.HkNorm α 4 g from rfl,
    Work.Spaces.HkNorm, Work.Spaces.HkNorm,
    Work.FTS.EllipticEst.HkSq_congr_open α 4 h]

/-- `Xn` is homogeneous for the multiplication by a scalar. -/
private theorem Xn_const_mul (α : ℝ) (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.FTS.Nonlin.Xn α (fun z θ => c * f z θ) = |c| * Work.FTS.Nonlin.Xn α f := by
  have h1 : (fun z θ : ℝ => c * f z θ) = c • f := by
    funext z θ; simp [Pi.smul_apply, smul_eq_mul]
  rw [h1]
  exact Work.FTS.EllipticEst.HkNorm_smul c α 4 f

/-- `Xn` is invariant under negation. -/
private theorem Xn_neg (α : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.FTS.Nonlin.Xn α (fun z θ => - f z θ) = Work.FTS.Nonlin.Xn α f := by
  show Work.Spaces.HkNorm α 4 (fun z θ : ℝ => - f z θ) = Work.Spaces.HkNorm α 4 f
  have h2 : (fun z θ : ℝ => - f z θ) = (-1 : ℝ) • f := by
    funext z θ; simp [Pi.smul_apply]
  rw [h2, Work.FTS.EllipticEst.HkNorm_smul]
  norm_num

/-- **Subadditivity of `Xn` on the open-quadrant class**, in the difference form. -/
private theorem Xn_sub_le (α : ℝ) (hα : 0 < α) {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hmf : Work.Spaces.HkMem α 4 f) (hmg : Work.Spaces.HkMem α 4 g) :
    Work.FTS.Nonlin.Xn α (fun z θ => f z θ - g z θ)
      ≤ 2 * (Work.FTS.Nonlin.Xn α f + Work.FTS.Nonlin.Xn α g) := by
  have hgs : Work.FTS.EllipticEst.SmoothOpen (fun z θ => - g z θ) :=
    Work.FTS.GalFields.Tail.SmoothOpen.neg hg
  have hgm : Work.Spaces.HkMem α 4 (fun z θ => - g z θ) :=
    Work.FTS.NonlinRows.HkMem_neg' α 4 hmg
  have h1 := Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα hf hgs hmf hgm
  have hneg : Work.Spaces.HkNorm α 4 (fun z θ : ℝ => - g z θ) = Work.Spaces.HkNorm α 4 g :=
    Xn_neg α g
  rw [hneg] at h1
  rw [Xn_congr_open α (f := fun z θ => f z θ - g z θ) (g := fun z θ => f z θ + - g z θ)
    (fun z θ _ _ _ => by ring)]
  simpa only [Work.FTS.Nonlin.Xn] using h1

/-! ## The bound -/

theorem MuBlockXnBound {α Km KAK : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hKm : 0 ≤ Km) :
    ∃ C : ℝ, 0 < C ∧ ∀ {W₁ W₂ : Work.FTS.Galerkin.Fn},
      Work.FTS.ClassC.ClassC α W₁ → Work.FTS.ClassC.ClassC α W₂ →
      |Work.FTS.StrongEps.EpsRLX.muOf α Φs E W₁| ≤ 1 / 2 →
      |Work.FTS.StrongEps.EpsRLX.muOf α Φs E W₂| ≤ 1 / 2 →
      |Work.FTS.StrongEps.EpsRLX.mubarOf α Φs E W₁
          - Work.FTS.StrongEps.EpsRLX.mubarOf α Φs E W₂|
        ≤ Km * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) →
      |Work.FTS.StrongEps.EpsRLX.muOf α Φs E W₁
          - Work.FTS.StrongEps.EpsRLX.muOf α Φs E W₂|
        ≤ Km * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) →
      Work.FTS.Nonlin.Xn α (Work.Construction.AK α) ≤ KAK →
      Work.FTS.Nonlin.Xn α (fun z θ =>
        Work.FTS.StrongEps.EpsRLX.muBlock α Φs E W₁ z θ
          - Work.FTS.StrongEps.EpsRLX.muBlock α Φs E W₂ z θ)
        ≤ C * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂) ^ 2
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by
  refine ⟨2 * |Km| * (|KAK| + 8) + 20, by positivity, ?_⟩
  intro W₁ W₂ hW₁ hW₂ hμ₁ hμ₂ hbdμb hbdμ hAKb
  -- ## the abbreviations
  set μ₁ : ℝ := muOf α Φs E W₁ with hμ₁def
  set μ₂ : ℝ := muOf α Φs E W₂ with hμ₂def
  set mb₁ : ℝ := mubarOf α Φs E W₁ with hmb₁def
  set mb₂ : ℝ := mubarOf α Φs E W₂ with hmb₂def
  set d : Fn := fun z θ => W₁ z θ - W₂ z θ with hddef
  set Y : ℝ := Work.FTS.GalFields.Xn5 α W₁ with hYdef
  set Y' : ℝ := Work.FTS.GalFields.Xn5 α W₂ with hY'def
  set Z : ℝ := Work.FTS.GalFields.Xn5 α d with hZdef
  set P : ℝ := 1 + Y + Y' with hPdef
  set S : ℝ := P * Z with hSdef
  set T : ℝ := P ^ 2 * Z with hTdef
  set Cc : ℝ := 2 * |Km| * (|KAK| + 8) + 20 with hCdef
  -- ## the four converted hypotheses
  have hμ₁b : |μ₁| ≤ 1 / 2 := hμ₁
  have hμ₂b : |μ₂| ≤ 1 / 2 := hμ₂
  have hmbdb : |mb₁ - mb₂| ≤ Km * P * Z := hbdμb
  have hmudb : |μ₁ - μ₂| ≤ Km * P * Z := hbdμ
  have hAKb' : Work.FTS.Nonlin.Xn α (Work.Construction.AK α) ≤ |KAK| :=
    le_trans hAKb (le_abs_self KAK)
  have hμ₁ne : μ₁ ≠ -1 := by
    intro hcon; rw [hcon] at hμ₁b; norm_num at hμ₁b
  have hμ₂ne : μ₂ ≠ -1 := by
    intro hcon; rw [hcon] at hμ₂b; norm_num at hμ₂b
  -- ## the smoothness / honesty data
  have hsm₁ : Work.FTS.EllipticEst.SmoothOpen W₁ := hW₁.reg
  have hsm₂ : Work.FTS.EllipticEst.SmoothOpen W₂ := hW₂.reg
  have hdC : Work.FTS.ClassC.ClassC α d := by
    rw [hddef]
    exact Work.FTS.StrongEps.EComparison.classC_sub hW₁ hW₂
  have hdsm : Work.FTS.EllipticEst.SmoothOpen d := hdC.reg
  have h5₁ : Work.Spaces.HkMem α 5 W₁ :=
    Work.FTS.OpenPkg.HkMem_mono_open hsm₁ 5 (by norm_num) hW₁.mem
  have h5₂ : Work.Spaces.HkMem α 5 W₂ :=
    Work.FTS.OpenPkg.HkMem_mono_open hsm₂ 5 (by norm_num) hW₂.mem
  have h5d : Work.Spaces.HkMem α 5 d :=
    Work.FTS.OpenPkg.HkMem_mono_open hdsm 5 (by norm_num) hdC.mem
  have h4d : Work.Spaces.HkMem α 4 d :=
    Work.FTS.OpenPkg.HkMem_mono_open hdsm 4 (by norm_num) hdC.mem
  have h4₂ : Work.Spaces.HkMem α 4 W₂ :=
    Work.FTS.OpenPkg.HkMem_mono_open hsm₂ 4 (by norm_num) hW₂.mem
  have hDzd4 : Work.Spaces.HkMem α 4 (Work.Spaces.Dz d) :=
    Work.FTS.IPGen.HkMem_Dz_le hdsm h5d
  have hDz₂4 : Work.Spaces.HkMem α 4 (Work.Spaces.Dz W₂) :=
    Work.FTS.IPGen.HkMem_Dz_le hsm₂ h5₂
  -- the `ℋ⁴`-honesty of the fixed profile `AK α` (valid for every `α > 0`)
  have hAKmem : Work.Spaces.HkMem α 4 (Work.Construction.AK α) :=
    Work.FTS.StrongEps.EpsRLX.HkMemAKGeneral α hα
  have hAKsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.AK α) :=
    Work.FTS.StrongPersist.AK_smoothO α
  -- ## the five pieces
  set m1 : Fn := fun z θ => -(mb₁ - mb₂) * Work.Construction.AK α z θ with hm1def
  set m2 : Fn := fun z θ => μ₁ * (Work.Spaces.Dz d z θ - d z θ) with hm2def
  set m3 : Fn := fun z θ => (μ₁ - μ₂) * (Work.Spaces.Dz W₂ z θ - W₂ z θ) with hm3def
  set m23 : Fn := fun z θ => m2 z θ + m3 z θ with hm23def
  set nice : Fn := fun z θ => m1 z θ + m23 z θ with hnicedef
  -- ## smoothness of the pieces
  have hsm1 : Work.FTS.EllipticEst.SmoothOpen m1 := by
    rw [hm1def]
    exact Work.FTS.NonlinRows.smoothOpen_const_mul (-(mb₁ - mb₂)) hAKsm
  have hsm2 : Work.FTS.EllipticEst.SmoothOpen m2 := by
    rw [hm2def]
    exact Work.FTS.NonlinRows.smoothOpen_const_mul μ₁
      (Work.FTS.NonlinRows.smoothOpen_sub hdsm.Dz hdsm)
  have hsm3 : Work.FTS.EllipticEst.SmoothOpen m3 := by
    rw [hm3def]
    exact Work.FTS.NonlinRows.smoothOpen_const_mul (μ₁ - μ₂)
      (Work.FTS.NonlinRows.smoothOpen_sub hsm₂.Dz hsm₂)
  have hsm23 : Work.FTS.EllipticEst.SmoothOpen m23 := by
    rw [hm23def]
    exact Work.FTS.NonlinRows.smoothOpen_add hsm2 hsm3
  have hsmNice : Work.FTS.EllipticEst.SmoothOpen nice := by
    rw [hnicedef]
    exact Work.FTS.NonlinRows.smoothOpen_add hsm1 hsm23
  -- ## honesty of the pieces
  have hmemSubd : Work.Spaces.HkMem α 4 (fun z θ => Work.Spaces.Dz d z θ - d z θ) := by
    have h := Work.FTS.CoercivityFix.Assembly.HkMem_add_open α 4 hdsm.Dz
      (Work.FTS.GalFields.Tail.SmoothOpen.neg hdsm) hDzd4
      (Work.FTS.NonlinRows.HkMem_neg' α 4 h4d)
    exact Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4 h
      (fun z _ θ _ => by ring)
  have hmemSub2 : Work.Spaces.HkMem α 4 (fun z θ => Work.Spaces.Dz W₂ z θ - W₂ z θ) := by
    have h := Work.FTS.CoercivityFix.Assembly.HkMem_add_open α 4 hsm₂.Dz
      (Work.FTS.GalFields.Tail.SmoothOpen.neg hsm₂) hDz₂4
      (Work.FTS.NonlinRows.HkMem_neg' α 4 h4₂)
    exact Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4 h
      (fun z _ θ _ => by ring)
  have hm1mem : Work.Spaces.HkMem α 4 m1 := by
    rw [hm1def]
    exact Work.FTS.LocData.HkMem_const_mul α 4 (-(mb₁ - mb₂)) hAKmem
  have hm2mem : Work.Spaces.HkMem α 4 m2 := by
    rw [hm2def]
    exact Work.FTS.LocData.HkMem_const_mul α 4 μ₁ hmemSubd
  have hm3mem : Work.Spaces.HkMem α 4 m3 := by
    rw [hm3def]
    exact Work.FTS.LocData.HkMem_const_mul α 4 (μ₁ - μ₂) hmemSub2
  have hm23mem : Work.Spaces.HkMem α 4 m23 := by
    rw [hm23def]
    exact Work.FTS.CoercivityFix.Assembly.HkMem_add_open α 4 hsm2 hsm3 hm2mem hm3mem
  have hmNicemem : Work.Spaces.HkMem α 4 nice := by
    rw [hnicedef]
    exact Work.FTS.CoercivityFix.Assembly.HkMem_add_open α 4 hsm1 hsm23 hm1mem hm23mem
  -- ## the sizes
  have hY0 : 0 ≤ Y := by rw [hYdef]; exact Work.Spaces.HkNorm_nonneg α 5 W₁
  have hY'0 : 0 ≤ Y' := by rw [hY'def]; exact Work.Spaces.HkNorm_nonneg α 5 W₂
  have hZ0 : 0 ≤ Z := by rw [hZdef]; exact Work.Spaces.HkNorm_nonneg α 5 d
  have hP1 : 1 ≤ P := by rw [hPdef]; linarith
  have hS0 : 0 ≤ S := by
    rw [hSdef]; exact mul_nonneg (by rw [hPdef]; linarith) hZ0
  have hT0 : 0 ≤ T := by
    rw [hTdef]; exact mul_nonneg (sq_nonneg _) hZ0
  have hY'P : Y' ≤ P := by rw [hPdef]; linarith
  have hST : S ≤ T := by
    rw [hSdef, hTdef]
    exact mul_le_mul_of_nonneg_right (by nlinarith [hP1]) hZ0
  have hZT : Z ≤ T := by
    rw [hTdef]; nlinarith [hP1, hZ0]
  have hSY' : S * Y' ≤ T := by
    rw [hSdef, hTdef]; nlinarith [hP1, hZ0, hY'P]
  have hbdSZ : Km * P * Z = |Km| * S := by
    rw [hSdef, abs_of_nonneg hKm]; ring
  have hmbdb' : |mb₁ - mb₂| ≤ |Km| * S := by rw [← hbdSZ]; exact hmbdb
  have hmudb' : |μ₁ - μ₂| ≤ |Km| * S := by rw [← hbdSZ]; exact hmudb
  -- ## the three `Xn`-bounds
  have hX1 : Work.FTS.Nonlin.Xn α m1 ≤ |Km| * S * |KAK| := by
    rw [hm1def, Xn_const_mul, abs_neg]
    exact mul_le_mul hmbdb' hAKb'
      (Work.Spaces.HkNorm_nonneg α 4 (Work.Construction.AK α))
      (mul_nonneg (abs_nonneg Km) hS0)
  have hsubDb : Work.FTS.Nonlin.Xn α (fun z θ => Work.Spaces.Dz d z θ - d z θ) ≤ 4 * Z := by
    have h1 := Xn_sub_le α hα hdsm.Dz hdsm hDzd4 h4d
    have h2 : Work.FTS.Nonlin.Xn α (Work.Spaces.Dz d) ≤ Z := by
      rw [hZdef]; exact Work.FTS.GalFields.Xn_Dz_le_Xn5 hα hdsm h5d
    have h3 : Work.FTS.Nonlin.Xn α d ≤ Z := by
      rw [hZdef]
      exact Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 5) (k' := 4) (by norm_num) h5d
    linarith
  have hsub2b : Work.FTS.Nonlin.Xn α (fun z θ => Work.Spaces.Dz W₂ z θ - W₂ z θ) ≤ 4 * Y' := by
    have h1 := Xn_sub_le α hα hsm₂.Dz hsm₂ hDz₂4 h4₂
    have h2 : Work.FTS.Nonlin.Xn α (Work.Spaces.Dz W₂) ≤ Y' := by
      rw [hY'def]; exact Work.FTS.GalFields.Xn_Dz_le_Xn5 hα hsm₂ h5₂
    have h3 : Work.FTS.Nonlin.Xn α W₂ ≤ Y' := by
      rw [hY'def]
      exact Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 5) (k' := 4) (by norm_num) h5₂
    linarith
  have hX2 : Work.FTS.Nonlin.Xn α m2 ≤ 2 * Z := by
    rw [hm2def, Xn_const_mul]
    calc |μ₁| * Work.FTS.Nonlin.Xn α (fun z θ => Work.Spaces.Dz d z θ - d z θ)
        ≤ (1 / 2) * (4 * Z) :=
          mul_le_mul hμ₁b hsubDb
            (Work.Spaces.HkNorm_nonneg α 4 (fun z θ => Work.Spaces.Dz d z θ - d z θ))
            (by norm_num)
      _ = 2 * Z := by ring
  have hX3 : Work.FTS.Nonlin.Xn α m3 ≤ |Km| * S * (4 * Y') := by
    rw [hm3def, Xn_const_mul]
    exact mul_le_mul hmudb' hsub2b
      (Work.Spaces.HkNorm_nonneg α 4 (fun z θ => Work.Spaces.Dz W₂ z θ - W₂ z θ))
      (mul_nonneg (abs_nonneg Km) hS0)
  -- ## the assembly
  have hXn23 : Work.FTS.Nonlin.Xn α m23 ≤ 2 * (Work.FTS.Nonlin.Xn α m2 + Work.FTS.Nonlin.Xn α m3) := by
    rw [hm23def]
    exact Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα hsm2 hsm3 hm2mem hm3mem
  have hXnNice : Work.FTS.Nonlin.Xn α nice ≤ 2 * (Work.FTS.Nonlin.Xn α m1 + Work.FTS.Nonlin.Xn α m23) := by
    rw [hnicedef]
    exact Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα hsm1 hsm23 hm1mem hm23mem
  have hstep1 : 2 * (Work.FTS.Nonlin.Xn α m1 + Work.FTS.Nonlin.Xn α m23)
      ≤ 2 * (|Km| * S * |KAK| + 2 * (2 * Z + |Km| * S * (4 * Y'))) := by
    have h2 : Work.FTS.Nonlin.Xn α m23 ≤ 2 * (2 * Z + |Km| * S * (4 * Y')) := by
      linarith [hXn23, hX2, hX3]
    linarith [hX1, h2]
  have hstep2 : 2 * (|Km| * S * |KAK| + 2 * (2 * Z + |Km| * S * (4 * Y'))) ≤ Cc * T := by
    have e0 : 2 * (|Km| * S * |KAK| + 2 * (2 * Z + |Km| * S * (4 * Y')))
        = 2 * (|Km| * (S * |KAK|)) + 8 * Z + 16 * (|Km| * (S * Y')) := by ring
    have e1 : 2 * (|Km| * (S * |KAK|)) ≤ 2 * (|Km| * (T * |KAK|)) := by
      have h := mul_le_mul_of_nonneg_right hST (abs_nonneg KAK)
      have h2 := mul_le_mul_of_nonneg_left h (abs_nonneg Km)
      linarith
    have e2 : 8 * Z ≤ 8 * T := by linarith [hZT]
    have e3 : 16 * (|Km| * (S * Y')) ≤ 16 * (|Km| * T) := by
      have h := mul_le_mul_of_nonneg_left hSY' (abs_nonneg Km)
      linarith
    have e4 : Cc * T = 2 * (|Km| * (T * |KAK|)) + 8 * T + 16 * (|Km| * T) + 12 * T := by
      rw [hCdef]; ring
    rw [e0, e4]
    linarith [e1, e2, e3, hT0]
  have hgoal : Cc * P ^ 2 * Z = Cc * T := by rw [hTdef]; ring
  rw [hgoal]
  refine le_trans ?_ (le_trans hXnNice (le_trans hstep1 hstep2))
  refine le_of_eq (Xn_congr_open α (fun z θ hz hθ0 hθ1 => ?_))
  rw [muBlock_sub_eq hsm₁ hsm₂ (by rw [← hμ₁def]; exact hμ₁ne) (by rw [← hμ₂def]; exact hμ₂ne)
    z θ hz hθ0 hθ1]
  simp only [hnicedef, hm23def, hm1def, hm2def, hm3def, hddef]
  ring

end Work.FTS.StrongEps.EpsRLX
end
