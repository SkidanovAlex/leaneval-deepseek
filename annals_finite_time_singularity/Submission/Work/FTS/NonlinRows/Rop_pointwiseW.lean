import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.Nonlinear.Pieces.RNP.Rop_pointwiseU
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row11Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.WlInf_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.NonlinRows

open Work.FTS.Nonlinear.Pieces.RNP.row10aux (deweight_leibniz_sum_le contDiffAt_phi
  wlInf_nonneg_of_mem DthIter_mul_radial DthIter_congr_nhds DthIter_mul_phi)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The smoothness of the weighted star coefficient on the open quadrant

These are the `Q0`-analogues of the `SmoothQuad`-level algebra of
`Work.FTS.LocData`/`row10aux`; keeping them here makes the file self-contained
(`SmoothOpen` is `C^∞` on the *open* quadrant `(0,∞) × (0,π/2)` only, which is all the
primed rows provide). -/

/-- `SmoothOpen` is closed under subtraction. -/
theorem RopW_sub {F G : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => F z θ - G z θ) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => F z θ - G z θ)) Work.FTS.EllipticEst.Q0
  have h : Function.uncurry (fun z θ => F z θ - G z θ)
      = fun p : ℝ × ℝ => Function.uncurry F p - Function.uncurry G p := rfl
  rw [h]
  exact hF.sub hG

/-- `SmoothOpen` is closed under products. -/
theorem RopW_mul {F G : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => F z θ * G z θ) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => F z θ * G z θ)) Work.FTS.EllipticEst.Q0
  have h : Function.uncurry (fun z θ => F z θ * G z θ)
      = fun p : ℝ × ℝ => Function.uncurry F p * Function.uncurry G p := rfl
  rw [h]
  exact hF.mul hG

/-- The radial factor `(z+1)/z` is `C^∞` on the open quadrant. -/
theorem RopW_zdiv :
    Work.FTS.EllipticEst.SmoothOpen (fun z (_ : ℝ) => (z + 1) / z) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z (_ : ℝ) => (z + 1) / z)) Work.FTS.EllipticEst.Q0
  have h : Function.uncurry (fun z (_ : ℝ) => (z + 1) / z)
      = fun p : ℝ × ℝ => (p.1 + 1) / p.1 := rfl
  rw [h]
  refine ContDiffOn.div (contDiffOn_fst.add contDiffOn_const) contDiffOn_fst ?_
  intro p hp
  exact ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1

/-- The singular part `Θ_*(α) = Θ α (F_*) = sin(2θ)/(2(1+z))` of `Φ̃_*` is `C^∞` on the open
quadrant (its `SmoothQuad`-smoothness restricts, since `Q0 ⊆ quadU`). -/
theorem RopW_ThetaFstar {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Theta α (Work.Construction.Fstar α)) := by
  have hquad : Work.FTS.LocData.SmoothQuad
      (Work.Construction.Theta α (Work.Construction.Fstar α)) :=
    Work.FTS.Nonlinear.Pieces.RNP.row10aux.smoothQuad_Theta_Fstar hα hα1
  refine hquad.mono ?_
  intro p hp
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  exact ⟨Set.mem_Ioi.mpr (by linarith), Set.mem_Ioo.mpr ⟨hθ0, hθ1⟩⟩

/-- **`ℛ(Ψ)` is `C^∞` on the open quadrant when `Ψ` is.**  The division by `cos θ` is legitimate
because `cos θ > 0` for `θ ∈ (0,π/2)`, and `∂_zΨ`, `∂_θΨ` are `C^∞` there. -/
theorem RopW_Rop {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Rop α Ψ) := by
  have hQ : IsOpen Work.FTS.EllipticEst.Q0 := Work.FTS.EllipticEst.isOpen_Q0
  have hpz : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pz Ψ)) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.LocData.contDiffOn_pz hQ hΨ
  have hpth : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pth Ψ)) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.LocData.contDiffOn_pth hQ hΨ
  have hsin : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.sin p.2) Work.FTS.EllipticEst.Q0 :=
    (Real.contDiff_sin.comp contDiff_snd).contDiffOn
  have hcos : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.cos p.2) Work.FTS.EllipticEst.Q0 :=
    (Real.contDiff_cos.comp contDiff_snd).contDiffOn
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => 2 * Real.sin p.2 * Function.uncurry Ψ p)
      Work.FTS.EllipticEst.Q0 :=
    (contDiffOn_const.mul hsin).mul hΨ
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => α * Real.sin p.2 * p.1 * Function.uncurry (Work.Spaces.pz Ψ) p)
      Work.FTS.EllipticEst.Q0 :=
    ((contDiffOn_const.mul hsin).mul contDiffOn_fst).mul hpz
  have h3 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.cos p.2 * Function.uncurry (Work.Spaces.pth Ψ) p)
      Work.FTS.EllipticEst.Q0 :=
    hcos.mul hpth
  have hnum : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => 2 * Real.sin p.2 * Function.uncurry Ψ p
        + α * Real.sin p.2 * p.1 * Function.uncurry (Work.Spaces.pz Ψ) p
        + Real.cos p.2 * Function.uncurry (Work.Spaces.pth Ψ) p)
      Work.FTS.EllipticEst.Q0 :=
    (h1.add h2).add h3
  have hne : ∀ p ∈ Work.FTS.EllipticEst.Q0, Real.cos p.2 ≠ 0 := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩)
  refine (hnum.div hcos hne).congr ?_
  intro p _
  obtain ⟨z, θ⟩ := p
  rfl

/-- **The smoothness input of the main estimate**: the weighted star coefficient
`((z+1)/z)·ℛ(Φ̃_*)` is `C^∞` on the open quadrant, from `SmoothOpen Φs`, `0 < α ≤ 1`.

The only role of `α ≤ 1` is the profile identity `L₁₂(F_*) = 2α/(1+z)` which identifies
`Θ_*(α)` with the explicit smooth function `sin(2θ)/(2(1+z))`. -/
theorem RopW_smoothOpen_local {α : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hs : Work.FTS.EllipticEst.SmoothOpen Φs) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => (z + 1) / z
      * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ) := by
  have hΘ : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Theta α (Work.Construction.Fstar α)) :=
    RopW_ThetaFstar hα hα1
  have hPhi : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.PhiTs α Φs) := by
    show Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Φs z θ - Work.Construction.Theta α (Work.Construction.Fstar α) z θ)
    exact RopW_sub hs hΘ
  have hR : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) :=
    RopW_Rop hPhi
  exact RopW_mul RopW_zdiv hR

/-! ## The core estimate -/

/-- **The core estimate.**  From the weighted `𝒲^{4,∞}`-control of `Rv = ((z+1)/z)·ℛ(Φ̃_*)`
(`WlInfMem α 4 Rv`, `WlInf α 4 Rv ≤ Cs α`) and the *open-quadrant* smoothness of `Rv`, the four
pointwise bounds hold with the universal constant `100`.

The only use made of the smoothness hypothesis is to legitimise the Leibniz rule for `∂_z^k`
on the product `Rv = ψ · ℛ` with `ψ = (1+z)/z` (equivalently `ℛ = (z/(1+z))·Rv`), so that
`∂_z^k ℛ = ∑_{i≤k} C(k,i) ∂_z^i(z/(1+z))·∂_z^{k-i} Rv`; the weighted derivatives of the
de-weighting factor are bounded by `i!` (`phi_deriv_bound`), and the de-weighting Leibniz bound
`deweight_leibniz_sum_le` then converts `|(1+z)^j ∂_z^j Rv| ≤ W` into
`|(1+z)^k ∂_z^k ℛ| ≤ 65·W`. -/
theorem Rop_pointwiseW_aux {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hRvs : Work.FTS.EllipticEst.SmoothOpen (fun z θ => (z + 1) / z
      * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ))
    (hmem : Work.Spaces.WlInfMem α 4 (fun z θ => (z + 1) / z
      * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ))
    (hle : Work.Spaces.WlInf α 4 (fun z θ => (z + 1) / z
      * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ) ≤ Cs * α) :
    (∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ|
        ≤ 100 * (max Cs 1 * α) * z / (1 + z)) ∧
    (∀ c : ℕ, c ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Spaces.pzIter c (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ|
        ≤ 100 * (max Cs 1 * α) / (1 + z) ^ c) ∧
    (∀ a c : ℕ, 1 ≤ a → a + c ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Spaces.pzIter c (Work.Spaces.DthIter a
          (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs))) z θ|
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        ≤ 100 * (max Cs 1 * α) / (1 + z) ^ c) ∧
    (∀ a : ℕ, 1 ≤ a → a ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Spaces.DthIter a (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ|
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        ≤ 100 * (max Cs 1 * α) * z / (1 + z)) := by
  let R : ℝ → ℝ → ℝ := Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)
  let Rv : ℝ → ℝ → ℝ := fun z θ => (z + 1) / z * R z θ
  have hmemR : Work.Spaces.WlInfMem α 4 Rv := hmem
  have hleR : Work.Spaces.WlInf α 4 Rv ≤ Cs * α := hle
  have hRvsS : Work.FTS.EllipticEst.SmoothOpen Rv := hRvs
  have hW0 : 0 ≤ Work.Spaces.WlInf α 4 Rv := wlInf_nonneg_of_mem hmemR
  have hWmax : Work.Spaces.WlInf α 4 Rv ≤ max Cs 1 * α :=
    le_trans hleR (mul_le_mul_of_nonneg_right (le_max_left Cs 1) hα.le)
  have hCM0 : 0 ≤ max Cs 1 * α :=
    mul_nonneg (le_trans zero_le_one (le_max_right Cs 1)) hα.le
  -- the de-weighting identity `ℛ = (z/(1+z))·Rv` on `z > 0`
  have hRQ : ∀ z θ : ℝ, 0 < z → R z θ = z / (1 + z) * Rv z θ := by
    intro z θ hz
    have hz0 : z ≠ 0 := ne_of_gt hz
    have hz1 : (1 : ℝ) + z ≠ 0 := by positivity
    simp only [Rv]
    field_simp
    ring
  -- smoothness of the `z`-slices of `Rv`
  have hRvsSlice : ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      ContDiffAt ℝ Work.Stability.smoothOrder (fun z' => Rv z' θ) z :=
    fun z hz θ hθ =>
      (hRvsS.curry_z hθ).contDiffAt (isOpen_Ioi.mem_nhds hz)
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (1) the plain pointwise bound
    intro z hz θ hθ
    show |R z θ| ≤ 100 * (max Cs 1 * α) * z / (1 + z)
    have hzIz : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
    have hθIz : θ ∈ Work.Spaces.Iθ := Set.mem_Icc.mpr ⟨hθ.1.le, hθ.2.le⟩
    have hφnn : 0 ≤ z / (1 + z) := by positivity
    have hWpt : |Rv z θ| ≤ Work.Spaces.WlInf α 4 Rv := by
      have h := Work.Spaces.WlInf_z_bound α 4 Rv hmemR 0 (by norm_num) z θ hzIz hθIz
      simpa using h
    calc |R z θ| = z / (1 + z) * |Rv z θ| := by
          rw [hRQ z θ hz, abs_mul, abs_of_nonneg hφnn]
      _ ≤ z / (1 + z) * (max Cs 1 * α) :=
          mul_le_mul_of_nonneg_left (le_trans hWpt hWmax) hφnn
      _ ≤ 100 * (max Cs 1 * α) * z / (1 + z) := by
          have hX : 0 ≤ (max Cs 1 * α) * (z / (1 + z)) := mul_nonneg hCM0 hφnn
          calc z / (1 + z) * (max Cs 1 * α)
              = 1 * ((max Cs 1 * α) * (z / (1 + z))) := by ring
            _ ≤ 100 * ((max Cs 1 * α) * (z / (1 + z))) :=
                mul_le_mul_of_nonneg_right (by norm_num) hX
            _ = 100 * (max Cs 1 * α) * z / (1 + z) := by ring
  · -- (2) the radial derivatives `∂_z^c ℛ`
    intro c hc z hz θ hθ
    show |Work.Spaces.pzIter c R z θ| ≤ 100 * (max Cs 1 * α) / (1 + z) ^ c
    rw [show (1 : ℝ) + z = z + 1 from by ring]
    have hzIz : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
    have hθIz : θ ∈ Work.Spaces.Iθ := Set.mem_Icc.mpr ⟨hθ.1.le, hθ.2.le⟩
    have hz1 : (0 : ℝ) < z + 1 := by linarith
    have hEq : Work.Spaces.pzIter c R z θ
        = ∑ i ∈ Finset.range (c + 1), (c.choose i : ℝ)
            * (Work.Spaces.pzIter i (fun z θ => z / (1 + z)) z θ
              * Work.Spaces.pzIter (c - i) Rv z θ) := by
      have hcongr : Work.Spaces.pzIter c R z θ
          = Work.Spaces.pzIter c (fun z θ => z / (1 + z) * Rv z θ) z θ := by
        rw [Work.Spaces.pzIter_eq_iteratedDeriv, Work.Spaces.pzIter_eq_iteratedDeriv]
        refine Filter.EventuallyEq.iteratedDeriv_eq c ?_
        refine Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hz) (fun z' hz' => ?_)
        exact hRQ z' θ (Set.mem_Ioi.mp hz')
      rw [hcongr]
      exact Work.FTS.H2.Q.pzIter_mul_local_sm c (contDiffAt_phi hz)
        ((hRvsS.curry_z hθ).contDiffAt (isOpen_Ioi.mem_nhds hz))
    have hkey : |(z + 1) ^ c * Work.Spaces.pzIter c R z θ| ≤ 65 * Work.Spaces.WlInf α 4 Rv := by
      rw [hEq]
      simpa using deweight_leibniz_sum_le (X := Rv) (W := Work.Spaces.WlInf α 4 Rv) (σ := 1)
        hc zero_le_one hz.le hW0 (fun i hi => by
          have hic : i ≤ c := hi
          have h := Work.Spaces.WlInf_z_bound α 4 Rv hmemR (c - i) (by omega) z θ hzIz hθIz
          simpa using h)
    rw [abs_mul, abs_of_nonneg (pow_nonneg hz1.le c)] at hkey
    have hfinal : |Work.Spaces.pzIter c R z θ| ≤ 65 * (max Cs 1 * α) / (z + 1) ^ c := by
      rw [le_div_iff₀ (pow_pos hz1 c)]
      calc |Work.Spaces.pzIter c R z θ| * (z + 1) ^ c
          = (z + 1) ^ c * |Work.Spaces.pzIter c R z θ| := by ring
        _ ≤ 65 * Work.Spaces.WlInf α 4 Rv := hkey
        _ ≤ 65 * (max Cs 1 * α) := mul_le_mul_of_nonneg_left hWmax (by norm_num)
    calc |Work.Spaces.pzIter c R z θ| ≤ 65 * (max Cs 1 * α) / (z + 1) ^ c := hfinal
      _ ≤ 100 * (max Cs 1 * α) / (z + 1) ^ c :=
          div_le_div_of_nonneg_right (by linarith [hCM0]) (pow_nonneg hz1.le c)
  · -- (3) the mixed derivatives `∂_z^c D_θ^a ℛ`, `a ≥ 1`
    intro a c ha hac z hz θ hθ
    show |Work.Spaces.pzIter c (Work.Spaces.DthIter a R) z θ|
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
      ≤ 100 * (max Cs 1 * α) / (1 + z) ^ c
    rw [show (1 : ℝ) + z = z + 1 from by ring]
    have hzIz : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
    have hθIz : θ ∈ Work.Spaces.Iθ := Set.mem_Icc.mpr ⟨hθ.1.le, hθ.2.le⟩
    have hz1 : (0 : ℝ) < z + 1 := by linarith
    have hsin0 : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2])
    have hσnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) :=
      div_nonneg (Real.rpow_nonneg hsin0 _) (by linarith)
    -- `D_θ^a ℛ = (z/(1+z))·D_θ^a Rv` on the open quadrant
    have hDth : ∀ z' : ℝ, 0 < z' → Work.Spaces.DthIter a R z' θ
        = z' / (1 + z') * Work.Spaces.DthIter a Rv z' θ := by
      intro z' hz'
      have hV : ∀ p ∈ (Set.Ioi 0 ×ˢ Set.Ioo (0 : ℝ) (π / 2)),
          R p.1 p.2 = p.1 / (1 + p.1) * Rv p.1 p.2 := by
        rintro ⟨z'', θ''⟩ ⟨hz'', -⟩
        exact hRQ z'' θ'' hz''
      rw [DthIter_congr_nhds (u := R) (v := fun z θ => z / (1 + z) * Rv z θ)
        (V := Set.Ioi 0 ×ˢ Set.Ioo (0 : ℝ) (π / 2)) (isOpen_Ioi.prod isOpen_Ioo) hV a z' θ
        ⟨hz', hθ⟩, DthIter_mul_phi]
    have hEq : Work.Spaces.pzIter c (Work.Spaces.DthIter a R) z θ
        = ∑ i ∈ Finset.range (c + 1), (c.choose i : ℝ)
            * (Work.Spaces.pzIter i (fun z θ => z / (1 + z)) z θ
              * Work.Spaces.pzIter (c - i) (Work.Spaces.DthIter a Rv) z θ) := by
      have hcongr : Work.Spaces.pzIter c (Work.Spaces.DthIter a R) z θ
          = Work.Spaces.pzIter c
              (fun z θ => z / (1 + z) * Work.Spaces.DthIter a Rv z θ) z θ := by
        rw [Work.Spaces.pzIter_eq_iteratedDeriv, Work.Spaces.pzIter_eq_iteratedDeriv]
        refine Filter.EventuallyEq.iteratedDeriv_eq c ?_
        refine Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hz) (fun z' hz' => ?_)
        exact hDth z' (Set.mem_Ioi.mp hz')
      rw [hcongr]
      exact Work.FTS.H2.Q.pzIter_mul_local_sm c (contDiffAt_phi hz)
        (((hRvsS.DthIter a).curry_z hθ).contDiffAt (isOpen_Ioi.mem_nhds hz))
    have hkey : |(z + 1) ^ c * Work.Spaces.pzIter c (Work.Spaces.DthIter a R) z θ
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))|
        ≤ 65 * Work.Spaces.WlInf α 4 Rv := by
      rw [hEq]
      simpa using deweight_leibniz_sum_le (X := Work.Spaces.DthIter a Rv)
        (W := Work.Spaces.WlInf α 4 Rv)
        (σ := (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        (by omega : c ≤ 4) hσnn hz.le hW0 (fun i hi => by
          have hic : i ≤ c := hi
          have h := Work.Spaces.WlInf_mixed_bound α 4 Rv hmemR a (c - i) ha (by omega) z θ
            hzIz hθIz
          simpa only [← mul_div_assoc] using h)
    have hkey2 : (z + 1) ^ c * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a R) z θ|
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))))
        ≤ 65 * Work.Spaces.WlInf α 4 Rv := by
      have h := hkey
      rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hz1.le c), abs_of_nonneg hσnn] at h
      calc (z + 1) ^ c * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a R) z θ|
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))))
          = ((z + 1) ^ c * |Work.Spaces.pzIter c (Work.Spaces.DthIter a R) z θ|)
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) := by ring
        _ ≤ 65 * Work.Spaces.WlInf α 4 Rv := h
    have hfinal : |Work.Spaces.pzIter c (Work.Spaces.DthIter a R) z θ|
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        ≤ 65 * (max Cs 1 * α) / (z + 1) ^ c := by
      rw [le_div_iff₀ (pow_pos hz1 c)]
      calc (|Work.Spaces.pzIter c (Work.Spaces.DthIter a R) z θ|
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))) * (z + 1) ^ c
          = (z + 1) ^ c * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a R) z θ|
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))) := by ring
        _ ≤ 65 * Work.Spaces.WlInf α 4 Rv := hkey2
        _ ≤ 65 * (max Cs 1 * α) := mul_le_mul_of_nonneg_left hWmax (by norm_num)
    calc |Work.Spaces.pzIter c (Work.Spaces.DthIter a R) z θ|
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        ≤ 65 * (max Cs 1 * α) / (z + 1) ^ c := hfinal
      _ ≤ 100 * (max Cs 1 * α) / (z + 1) ^ c :=
          div_le_div_of_nonneg_right (by linarith [hCM0]) (pow_nonneg hz1.le c)
  · -- (4) the angular derivatives `D_θ^a ℛ`, `a ≥ 1`
    intro a ha ha4 z hz θ hθ
    show |Work.Spaces.DthIter a R z θ|
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
      ≤ 100 * (max Cs 1 * α) * z / (1 + z)
    have hzIz : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
    have hθIz : θ ∈ Work.Spaces.Iθ := Set.mem_Icc.mpr ⟨hθ.1.le, hθ.2.le⟩
    have hsin0 : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2])
    have hφnn : 0 ≤ z / (1 + z) := by positivity
    have hDth : Work.Spaces.DthIter a R z θ = z / (1 + z) * Work.Spaces.DthIter a Rv z θ := by
      have hV : ∀ p ∈ (Set.Ioi 0 ×ˢ Set.Ioo (0 : ℝ) (π / 2)),
          R p.1 p.2 = p.1 / (1 + p.1) * Rv p.1 p.2 := by
        rintro ⟨z'', θ''⟩ ⟨hz'', -⟩
        exact hRQ z'' θ'' hz''
      rw [DthIter_congr_nhds (u := R) (v := fun z θ => z / (1 + z) * Rv z θ)
        (V := Set.Ioi 0 ×ˢ Set.Ioo (0 : ℝ) (π / 2)) (isOpen_Ioi.prod isOpen_Ioo) hV a z θ
        ⟨hz, hθ⟩, DthIter_mul_phi]
    have hmix : |Work.Spaces.DthIter a Rv z θ|
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        ≤ Work.Spaces.WlInf α 4 Rv := by
      have h := Work.Spaces.WlInf_mixed_bound α 4 Rv hmemR a 0 ha (by omega) z θ hzIz hθIz
      have hσ2 : 0 ≤ (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) :=
        div_nonneg (Real.rpow_nonneg hsin0 _) (by linarith)
      have hden2 : 0 < α + Real.sin (2 * θ) := by linarith
      rw [pow_zero, one_mul, Work.Spaces.pzIter_zero, abs_div, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg hsin0 _), abs_of_pos hden2] at h
      simpa only [mul_div_assoc] using h
    calc |Work.Spaces.DthIter a R z θ|
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        = z / (1 + z) * (|Work.Spaces.DthIter a Rv z θ|
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))) := by
          rw [hDth, abs_mul, abs_of_nonneg hφnn]; ring
      _ ≤ z / (1 + z) * (max Cs 1 * α) :=
          mul_le_mul_of_nonneg_left (le_trans hmix hWmax) hφnn
      _ ≤ 100 * (max Cs 1 * α) * z / (1 + z) := by
          have hX : 0 ≤ (max Cs 1 * α) * (z / (1 + z)) := mul_nonneg hCM0 hφnn
          calc z / (1 + z) * (max Cs 1 * α)
              = 1 * ((max Cs 1 * α) * (z / (1 + z))) := by ring
            _ ≤ 100 * ((max Cs 1 * α) * (z / (1 + z))) :=
                mul_le_mul_of_nonneg_right (by norm_num) hX
            _ = 100 * (max Cs 1 * α) * z / (1 + z) := by ring

/- The pointwise `𝒲^{4,∞}`-bounds for the star coefficient `ℛ(Φ̃_*)` in the primed
(open-quadrant) setting, from the *weighted* field `WlInfMem α 4 Rv ∧ WlInf α 4 Rv ≤ Cs α`
(`Rv = ((z+1)/z)·ℛ(Φ̃_*)`): the exact analogue of the proved `Rop_pointwiseU`
(`Submission/Work/FTS/Nonlinear/Pieces/RNP/Rop_pointwiseU.lean`, which derives the same four
conjuncts from `StarPkg`), with the package hypothesis replaced by the two `WlInf` conjuncts of
`StarPkg.R`.  This is the bridge that turns the (missing) weighted decay of the star coefficient
into the pointwise inputs of the primed rows 10, 11, 15, 19; the proof is `Rop = z/(1+z)·Rv` plus
`WlInf_z_bound`/`WlInf_mixed_bound` and the Leibniz rule in `z` (with `|∂_z^j(z/(1+z))| ≤ j!/(1+z)^{j+1}`),
so no truncation of the angular boundary lines is needed and `SmoothOpen` (not `SmoothQuad`)
suffices. -/
theorem Rop_pointwiseW : ∃ C : ℝ, 0 < C ∧ ∀ {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn},
    0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen Φs →
    Work.Spaces.WlInfMem α 4 (fun z θ => (z + 1) / z
        * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ) →
    Work.Spaces.WlInf α 4 (fun z θ => (z + 1) / z
        * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ) ≤ Cs * α →
    (∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ|
        ≤ C * (max Cs 1 * α) * z / (1 + z)) ∧
    (∀ c : ℕ, c ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Spaces.pzIter c (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ|
        ≤ C * (max Cs 1 * α) / (1 + z) ^ c) ∧
    (∀ a c : ℕ, 1 ≤ a → a + c ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Spaces.pzIter c (Work.Spaces.DthIter a
          (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs))) z θ|
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        ≤ C * (max Cs 1 * α) / (1 + z) ^ c) ∧
    (∀ a : ℕ, 1 ≤ a → a ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Spaces.DthIter a (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ|
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        ≤ C * (max Cs 1 * α) * z / (1 + z)) := by
  refine ⟨100, by norm_num, ?_⟩
  intro α Cs Φs hα hα1 hSmooth hmem hle
  exact Rop_pointwiseW_aux hα hα1 (RopW_smoothOpen_local hα hα1 hSmooth) hmem hle

end Work.FTS.NonlinRows
