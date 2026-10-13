import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Submission.Work.FTS.NonlinRows.NRow1_7Aux
import Submission.Work.Coercivity.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalFields.RHS

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-!
# `L_Γ^T` is `C^∞` on the open quadrant

The transport-modified linearized operator of the paper is

`LGammaT α g = 𝓛 g − (2zΓ(θ)/(c(1+z)²))·L₁₂(g)(z)
                − 3 sin(2θ)∂_θg/(1+z)
                + (Γ(θ)/c)(2z²/(1+z)³)·L₁₂(Transport g)(0)`.

Two observations make this `C^∞` on the open quadrant `Q0 = (0,∞) × (0,π/2)`:

* the second and fourth terms involve the *radial* object `L₁₂(·)` — of `g`, and the *constant*
  value `L₁₂(Transport g)(0)` — times a rational factor of `z` and the angular profile `Γ`; the
  hypothesis `SmoothOpen (L₁₂ g)` handles the first and the second is constant, so no
  integrability or further nonlocal information is used;
* every remaining division is by `(1+z)^k` (`k = 1,2,3`), which does not vanish for `z > 0`; the
  division by `c α` is pulled out as a *constant* multiplier `1/c α`, so `c α ≠ 0` is not needed.

The statement follows from the pointwise identity `LGammaT_eq_Nice` and the closure of
`SmoothOpen` under sums, differences, products and multiplication by constants.
-/

/-- **`Γ(θ) = (sinθ·cos²θ)^{α/3}` is `C^∞` on the open quadrant.** -/
private theorem smoothOpen_Gam (α : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (fun (_ : ℝ) (θ : ℝ) => Work.Spaces.Gam α θ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (fun p : ℝ × ℝ => Work.Spaces.Gam α p.2) Work.FTS.EllipticEst.Q0
  have hbase : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.sin p.2 * Real.cos p.2 ^ 2) Work.FTS.EllipticEst.Q0 :=
    ((Real.contDiff_sin.comp contDiff_snd).mul
      ((Real.contDiff_cos.comp contDiff_snd).pow 2)).contDiffOn
  have hpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, Real.sin p.2 * Real.cos p.2 ^ 2 ≠ 0 := by
    intro p hp
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    have hs : 0 < Real.sin p.2 :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    have hc : 0 < Real.cos p.2 := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩
    positivity
  simpa only [Work.Spaces.Gam] using hbase.rpow_const_of_ne hpos

/-- A constant function is `SmoothOpen`. -/
private theorem smoothOpen_const (c : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (fun (_ : ℝ) (_ : ℝ) => c) :=
  Work.FTS.NonlinRows.smoothOpen_radial (r := fun _ => c) (fun _n => contDiffOn_const)

/-- The radial factor `z ↦ 1/(1+z)` (positive denominator on `(0,∞)`). -/
private theorem smoothOpen_inv_one_add :
    Work.FTS.EllipticEst.SmoothOpen (fun z (_ : ℝ) => 1 / (1 + z)) := by
  refine Work.FTS.NonlinRows.smoothOpen_radial (r := fun z => 1 / (1 + z)) (fun _n => ?_)
  exact (contDiffOn_const (c := (1 : ℝ))).div
    ((contDiffOn_const (c := (1 : ℝ))).add contDiffOn_id)
    (fun z hz => by
      have hz' : (0 : ℝ) < z := hz
      positivity)

/-- The radial factor `z ↦ 2z/(1+z)²`. -/
private theorem smoothOpen_zdz :
    Work.FTS.EllipticEst.SmoothOpen (fun z (_ : ℝ) => 2 * z * (1 / (1 + z) ^ 2)) := by
  refine Work.FTS.NonlinRows.smoothOpen_radial
    (r := fun z => 2 * z * (1 / (1 + z) ^ 2)) (fun _n => ?_)
  exact ((contDiffOn_const (c := (2 : ℝ))).mul contDiffOn_id).mul
    ((contDiffOn_const (c := (1 : ℝ))).div
      (((contDiffOn_const (c := (1 : ℝ))).add contDiffOn_id).pow 2)
      (fun z hz => by
        have hz' : (0 : ℝ) < z := hz
        exact pow_ne_zero 2 (by positivity)))

/-- The radial factor `z ↦ 2z²/(1+z)³`. -/
private theorem smoothOpen_zsqdz :
    Work.FTS.EllipticEst.SmoothOpen (fun z (_ : ℝ) => 2 * z ^ 2 * (1 / (1 + z) ^ 3)) := by
  refine Work.FTS.NonlinRows.smoothOpen_radial
    (r := fun z => 2 * z ^ 2 * (1 / (1 + z) ^ 3)) (fun _n => ?_)
  exact ((contDiffOn_const (c := (2 : ℝ))).mul (contDiffOn_id.pow 2)).mul
    ((contDiffOn_const (c := (1 : ℝ))).div
      (((contDiffOn_const (c := (1 : ℝ))).add contDiffOn_id).pow 3)
      (fun z hz => by
        have hz' : (0 : ℝ) < z := hz
        exact pow_ne_zero 3 (by positivity)))

/-- The normalised form of `LGammaT α g`: the constants `1/c α` are pulled in front of explicit
smooth factors and every division is by a power of `1+z`.  It is `C^∞` on the open quadrant as
soon as `g` and `z ↦ L₁₂(g)(z)` are (see `smoothOpen_Nice`), and it agrees with `LGammaT α g`
pointwise (`LGammaT_eq_Nice`). -/
private noncomputable def Nice (α : ℝ) (g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ =>
    (g z θ + Work.Spaces.Dz g z θ - 2 * (g z θ * (1 / (1 + z))))
      - (1 / Work.Spaces.c α)
          * ((2 * z * (1 / (1 + z) ^ 2)) * (Work.Spaces.Gam α θ * Work.Construction.L12 g z))
      - (3 * (Work.Spaces.Dth g z θ * (1 / (1 + z))))
      + (1 / Work.Spaces.c α)
          * (Work.Spaces.Gam α θ
            * ((2 * z ^ 2 * (1 / (1 + z) ^ 3))
              * Work.Coercivity.L12f (Work.Coercivity.Transport g) 0))

/-- **The pointwise identity**: `LGammaT α g` equals its normalised form `Nice α g`. -/
private theorem LGammaT_eq_Nice (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Coercivity.LGammaT α g z θ = Nice α g z θ := by
  simp only [Nice, Work.Coercivity.LGammaT, Work.Coercivity.LGamma, Work.Coercivity.L,
    Work.Coercivity.Proj, Work.Coercivity.Transport, Work.Coercivity.L12f,
    Work.Construction.L12, div_eq_mul_inv, mul_inv]
  ring_nf

/-- **`Nice α g` is `C^∞` on the open quadrant**, from the two hypotheses on `g`. -/
private theorem smoothOpen_Nice {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hL12 : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 g z))
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (Nice α g) := by
  have hGam := smoothOpen_Gam α
  have hz_inv := smoothOpen_inv_one_add
  have hz_sq := smoothOpen_zdz
  have hz_cu := smoothOpen_zsqdz
  have hC := smoothOpen_const (Work.Coercivity.L12f (Work.Coercivity.Transport g) 0)
  have hP1 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => g z θ + Work.Spaces.Dz g z θ - 2 * (g z θ * (1 / (1 + z)))) :=
    Work.FTS.NonlinRows.smoothOpen_sub
      (Work.FTS.NonlinRows.smoothOpen_add hg (Work.FTS.EllipticEst.SmoothOpen.Dz hg))
      (Work.FTS.NonlinRows.smoothOpen_const_mul 2
        (Work.FTS.NonlinRows.smoothOpen_mul hg hz_inv))
  have hA : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (1 / Work.Spaces.c α) * ((2 * z * (1 / (1 + z) ^ 2))
        * (Work.Spaces.Gam α θ * Work.Construction.L12 g z))) :=
    Work.FTS.NonlinRows.smoothOpen_const_mul (1 / Work.Spaces.c α)
      (Work.FTS.NonlinRows.smoothOpen_mul hz_sq
        (Work.FTS.NonlinRows.smoothOpen_mul hGam hL12))
  have hT : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => 3 * (Work.Spaces.Dth g z θ * (1 / (1 + z)))) :=
    Work.FTS.NonlinRows.smoothOpen_const_mul 3
      (Work.FTS.NonlinRows.smoothOpen_mul (Work.FTS.EllipticEst.SmoothOpen.Dth hg) hz_inv)
  have hB : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (1 / Work.Spaces.c α) * (Work.Spaces.Gam α θ
        * ((2 * z ^ 2 * (1 / (1 + z) ^ 3))
          * Work.Coercivity.L12f (Work.Coercivity.Transport g) 0))) :=
    Work.FTS.NonlinRows.smoothOpen_const_mul (1 / Work.Spaces.c α)
      (Work.FTS.NonlinRows.smoothOpen_mul hGam (Work.FTS.NonlinRows.smoothOpen_mul hz_cu hC))
  unfold Nice
  exact Work.FTS.NonlinRows.smoothOpen_add
    (Work.FTS.NonlinRows.smoothOpen_sub (Work.FTS.NonlinRows.smoothOpen_sub hP1 hA) hT) hB

theorem smoothOpen_LGammaT_of_L12 {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hL12 : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 g z))
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Coercivity.LGammaT α g) := by
  have hNice : Work.FTS.EllipticEst.SmoothOpen (Nice α g) := smoothOpen_Nice hL12 hg
  refine ContDiffOn.congr hNice ?_
  intro p _hp
  obtain ⟨z, θ⟩ := p
  exact LGammaT_eq_Nice α g z θ

end Work.FTS.GalFields.RHS
