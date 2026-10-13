import Mathlib
import Submission.Work.WilE3.Taylor.CaseII.PertShear
import Submission.Work.WilE3.Taylor.CaseII.contDiffOn_shear_data
import Submission.Work.WilE3.API.hasFDerivAt_eaEval

namespace Work.WilE3.Taylor.CaseII

/-!
  The derivative form of the shear identity.

  On the open set `Ush = {G · ∂_{i₀}Φ ≠ 0}` the perturbed polar minor factors as
  `pertMinor(v)ᵢ = G · ∂_{i₀}Φ · (aᵢ + bᵢ · v_{i₀} + vᵢ)` (`PertShear.aSh_add_bSh_mul_add`).
  At a point `x ∈ Ush` where the shear equation `aᵢ + bᵢ · v_{i₀} + vᵢ = 0` holds, the second
  factor vanishes, so the product rule for `fderiv` kills the term in which it is differentiated:
  the derivative of the perturbed minor is the (nonzero) scalar `G · ∂_{i₀}Φ (x)` times the
  derivative of the shear row `aᵢ + bᵢ · v_{i₀}`.  This is the "differentiate the shear identity"
  step of node T4 (`pertSys_det_ne`): it shows that the rows `∇ pertMinor(v)ᵢ` of the perturbed
  system are the rows `∇(aᵢ + bᵢ · v_{i₀})` rescaled by the common nonzero factor `G · ∂_{i₀}Φ (x)`.
-/

/-- **Derivative of a product whose second factor vanishes at the point, the second factor being a
function plus a constant.**  If `D` and `h` are differentiable at `x` with `h x + c = 0`, then
`fderiv (D · (h + c)) x = D x • fderiv h x`.  This is the product rule in which the term
`(h x + c) • fderiv D x` drops out. -/
private lemma fderiv_mul_add_const_eq {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {D h : G → ℝ} {x : G} {c : ℝ}
    (hD : HasFDerivAt D (fderiv ℝ D x) x) (hh : HasFDerivAt h (fderiv ℝ h x) x)
    (hz : h x + c = 0) :
    fderiv ℝ (fun z => D z * (h z + c)) x = D x • fderiv ℝ h x := by
  have hc : HasFDerivAt (fun z => h z + c) (fderiv ℝ h x) x := hh.add_const c
  have hprod : HasFDerivAt (fun z : G => D z * (h z + c))
      (D x • fderiv ℝ h x + (h x + c) • fderiv ℝ D x) x := by
    have := hD.mul hc
    convert this using 1
  rw [hprod.fderiv]
  simp only [hz, zero_smul, add_zero]

theorem fderiv_pertMinor_eq_smul_fderiv_shear {k r : ℕ} (c : WilkiesDesign.E.EAChain k r)
    (Φ : WilkiesDesign.E.EAPoly k r) (i₀ : Fin k) (v : Fin k → ℝ) (x : Fin k → ℝ)
    (hx : x ∈ Work.WilE3.Taylor.CaseII.Ush c Φ i₀) (i : Fin k) (hi : i ≠ i₀)
    (hcon : Work.WilE3.Taylor.CaseII.aSh c Φ i₀ x i
        + Work.WilE3.Taylor.CaseII.bSh c Φ i₀ x i * v i₀ + v i = 0) :
    fderiv ℝ (fun z : Fin k → ℝ =>
        WilkiesDesign.E.eaEval c (Work.WilE3.Taylor.CaseII.pertMinor c Φ v i₀ i) z) x
      = WilkiesDesign.E.eaEval c (Work.WilE3.Taylor.CaseII.denP c Φ i₀) x •
        fderiv ℝ (fun z : Fin k → ℝ =>
          Work.WilE3.Taylor.CaseII.aSh c Φ i₀ z i
          + Work.WilE3.Taylor.CaseII.bSh c Φ i₀ z i * v i₀) x := by
  -- The shear data `aSh`, `bSh` are `C¹` on the open set `Ush`, hence differentiable at `x`.
  obtain ⟨haSh, hbSh, _⟩ := Work.WilE3.Taylor.CaseII.contDiffOn_shear_data c Φ i₀
  have hxU : Work.WilE3.Taylor.CaseII.Ush c Φ i₀ ∈ nhds x :=
    (Work.WilE3.Taylor.CaseII.isOpen_Ush c Φ i₀).mem_nhds hx
  have ha_i : HasFDerivAt (fun z : Fin k → ℝ => Work.WilE3.Taylor.CaseII.aSh c Φ i₀ z i)
      (fderiv ℝ (fun z : Fin k → ℝ => Work.WilE3.Taylor.CaseII.aSh c Φ i₀ z i) x) x :=
    (((contDiffOn_pi.mp haSh) i).contDiffAt hxU).differentiableAt one_ne_zero |>.hasFDerivAt
  have hb_i : HasFDerivAt (fun z : Fin k → ℝ => Work.WilE3.Taylor.CaseII.bSh c Φ i₀ z i)
      (fderiv ℝ (fun z : Fin k → ℝ => Work.WilE3.Taylor.CaseII.bSh c Φ i₀ z i) x) x :=
    (((contDiffOn_pi.mp hbSh) i).contDiffAt hxU).differentiableAt one_ne_zero |>.hasFDerivAt
  -- The shear row `aᵢ + bᵢ · v_{i₀}` is differentiable at `x`.
  have hS' : HasFDerivAt (fun z : Fin k → ℝ =>
        Work.WilE3.Taylor.CaseII.aSh c Φ i₀ z i + Work.WilE3.Taylor.CaseII.bSh c Φ i₀ z i * v i₀)
      (fderiv ℝ (fun z : Fin k → ℝ => Work.WilE3.Taylor.CaseII.aSh c Φ i₀ z i) x
        + (v i₀) • fderiv ℝ (fun z : Fin k → ℝ => Work.WilE3.Taylor.CaseII.bSh c Φ i₀ z i) x) x :=
    ha_i.add (hb_i.mul_const (v i₀))
  have hS : HasFDerivAt (fun z : Fin k → ℝ =>
        Work.WilE3.Taylor.CaseII.aSh c Φ i₀ z i + Work.WilE3.Taylor.CaseII.bSh c Φ i₀ z i * v i₀)
      (fderiv ℝ (fun z : Fin k → ℝ =>
        Work.WilE3.Taylor.CaseII.aSh c Φ i₀ z i + Work.WilE3.Taylor.CaseII.bSh c Φ i₀ z i * v i₀) x) x := by
    rw [hS'.fderiv]; exact hS'
  -- The denominator `G · ∂_{i₀}Φ` is differentiable at `x` (it is an `eaEval`).
  have hD : HasFDerivAt (fun z : Fin k → ℝ =>
        WilkiesDesign.E.eaEval c (Work.WilE3.Taylor.CaseII.denP c Φ i₀) z)
      (fderiv ℝ (fun z : Fin k → ℝ =>
        WilkiesDesign.E.eaEval c (Work.WilE3.Taylor.CaseII.denP c Φ i₀) z) x) x :=
    (Work.WilE3.API.hasFDerivAt_eaEval c (Work.WilE3.Taylor.CaseII.denP c Φ i₀)
      x).differentiableAt.hasFDerivAt
  -- The perturbed minor agrees, on the neighbourhood `Ush` of `x`, with the product of the
  -- denominator and the shear row (the latter augmented by the constant `v i`).
  have hFE : (fun z : Fin k → ℝ =>
        WilkiesDesign.E.eaEval c (Work.WilE3.Taylor.CaseII.pertMinor c Φ v i₀ i) z)
      =ᶠ[nhds x] (fun z : Fin k → ℝ =>
        WilkiesDesign.E.eaEval c (Work.WilE3.Taylor.CaseII.denP c Φ i₀) z *
        (Work.WilE3.Taylor.CaseII.aSh c Φ i₀ z i
          + Work.WilE3.Taylor.CaseII.bSh c Φ i₀ z i * v i₀ + v i)) := by
    filter_upwards [hxU] with z hz
    have hden : WilkiesDesign.E.eaEval c (Work.WilE3.Taylor.CaseII.denP c Φ i₀) z ≠ 0 := hz
    have h := Work.WilE3.Taylor.CaseII.aSh_add_bSh_mul_add c Φ i₀ v z hz i hi
    rw [h, mul_div_cancel₀ _ hden]
  rw [hFE.fderiv_eq]
  -- Product rule with the vanishing factor `h x + c = 0`, i.e. the hypothesis `hcon`.
  exact fderiv_mul_add_const_eq hD hS (by simpa using hcon)

end Work.WilE3.Taylor.CaseII
