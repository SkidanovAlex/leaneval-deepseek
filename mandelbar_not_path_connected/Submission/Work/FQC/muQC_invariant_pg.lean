/-
# `Work.FQC.muQC_invariant_pg` — invariance of the deformation coefficient

`muQC d fl Pg t` is built from the pull-back of the coefficient of the MNS twist `ℓ_t` along the
Fatou coordinate on the fundamental domain `Pg`, and then spread over the parabolic basin by the
*least* iterate of the dynamics that reaches `Pg`.  For this coefficient to be the dilatation of a
quasiconformal conjugacy of `T_c` it must be invariant:

  `μ (z) = star (μ (T_c z)) · ∂̄T_c z / star (∂̄T_c z)`  for a.e. `z`,

which is what this file proves.

The proof has three parts.

* *Off the basin* both sides vanish pointwise: the basin is backward invariant.

* *Inside the basin, at a point whose least entry time `n` is positive*, the identity is
  definitional: the least entry time of `T_c z` is `n - 1` and one step of `pullAntiIter`
  (`pullAntiIter_succ`) is exactly the formula for `pullAnti (muQC ·) (T_c) z`.

* *On the fundamental domain `Pg` itself* (`n = 0`) one has to check the return invariance of the
  coefficient
  `ν = pullHoloOn (beltramiOf (ℓ_t)) φa Pg` of the petal:
  `ν z = pullAntiIter (T_c) 5 ν z`.
  This is the substantive step.  Expanding the five-fold pull-back
  (`Work.FQC.pullAntiIter_five_Tantibar`) it becomes
  `ν z = star (ν (g z)) · (∂̄g z / star (∂̄g z))`, `g = T_c^[5]`, which in turn reduces to the
  three inputs
  * the anti-equivariance `φa (g z) = star (φa z) + 1/2` of the Fatou coordinate,
  * the reflection identity `beltramiOf (ℓ_t) (star w + 1/2) = star (beltramiOf (ℓ_t) w)`
    (`Work.FQC.beltramiOf_ell_iota`),
  * the differentiated Fatou relation `φa' (g z) · ∂̄g z = star (φa' z)`
    (`Work.FQC.fatou_deriv_relation`), which is the Wirtinger `∂̄`-chain rule applied to the
    anti-equivariance.
-/
import Mathlib
import Submission.Work.FQC.Defs
import Submission.Work.FQC.Petal
import Submission.Work.FQC.Ell
import Submission.Work.FQC.pullAntiIter_five_Tantibar
import Submission.Work.FQC.beltramiOf_ell_iota
import Submission.Work.MRMT.Wirtinger.dz_comp
import Submission.Work.MRMT.Wirtinger.dzbar_comp
import Submission.Work.MRMT.Wirtinger.beltramiOf_comp_antiholo

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology ComplexConjugate
open MeasureTheory Filter Set Function
open Classical

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

noncomputable section

namespace Work.FQC

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Work.EL (RootParabolic F K)

/-! ## 1. Local Wirtinger facts -/

/-- For a holomorphic `h`, the Wirtinger derivative `∂h` is the complex derivative. -/
theorem dz_eq_deriv_of_holo {h : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ h z) :
    Work.MRMT.dz h z = deriv h z := by
  have hd : HasDerivAt h (deriv h z) z := by simpa using hf.hasFDerivAt.hasDerivAt
  have hf' : fderiv ℝ h z = deriv h z • (1 : ℂ →L[ℝ] ℂ) := hd.complexToReal_fderiv.fderiv
  simp only [Work.MRMT.dz, hf']
  simp only [smul_apply, one_apply_eq_self, smul_eq_mul, mul_one]
  ring_nf
  rw [pow_two, Complex.I_mul_I]
  ring

/-- `∂̄ (star ∘ G) = star ∘ (∂G)`. -/
theorem dzbar_star_comp_fqc {G : ℂ → ℂ} {z : ℂ} (hG : DifferentiableAt ℝ G z) :
    Work.MRMT.dzbar (star ∘ G) z = star (Work.MRMT.dz G z) := by
  rw [Work.MRMT.Wirtinger.dzbar_comp (g := (star : ℂ → ℂ)) (f := G)
      (Work.MRMT.Wirtinger.differentiableAt_star (G z)) hG,
    Work.MRMT.Wirtinger.dz_star, Work.MRMT.Wirtinger.dzbar_star]
  simp

/-- Adding a constant does not change `∂̄`. -/
theorem dzbar_add_const_fqc {F : ℂ → ℂ} {c z : ℂ} :
    Work.MRMT.dzbar (fun w => F w + c) z = Work.MRMT.dzbar F z := by
  simp only [Work.MRMT.dzbar, fderiv_add_const]

/-! ## 2. The differentiated Fatou relation -/

/-- **The differentiated anti-equivariance of the Fatou coordinate.**  For `z` in the fundamental
domain `Pg` of the return map `g = T_c^[5]`, the Wirtinger `∂̄`-chain rule applied to
`φa ∘ g = star ∘ φa + 1/2` gives

  `φa'(g z) · ∂̄g z = star (φa' z)`.

The point is that `φa ∘ g` and `star ∘ φa + 1/2` agree on the petal, which is a neighbourhood of
`z`, so their real Fréchet derivatives at `z` agree; computing `∂̄` of both by the chain rules
(`Work.MRMT.Wirtinger.dzbar_comp`, `∂̄φa = 0` because `φa` is holomorphic, `∂g = 0` because `g` is
antiholomorphic) gives the identity. -/
theorem fatou_deriv_relation {c : ℂ} (d : RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁)
    (hfl : PetalInput d fl) {z : ℂ} (hz : z ∈ hfl.Pg) :
    deriv fl.φa ((Tantibar c)^[5] z) * Work.MRMT.dzbar ((Tantibar c)^[5]) z =
      star (deriv fl.φa z) := by
  have hzPa : z ∈ fl.Pa := hfl.Pg_sub hz
  have hgzPa : (Tantibar c)^[5] z ∈ fl.Pa := hfl.Pg_sub (hfl.mapsTo_g_Pg z hz)
  have hanti : DifferentiableAt ℂ (star ∘ (Tantibar c)^[5]) z :=
    fl.φa_fatou.1.1.differentiableAt (fl.isOpen_Pa.mem_nhds hzPa)
  have hga : DifferentiableAt ℝ ((Tantibar c)^[5]) z :=
    Work.MRMT.Wirtinger.differentiableAt_of_antiholo hanti
  have hφz : DifferentiableAt ℂ fl.φa z :=
    fl.φa_fatou.1.2.1.differentiableAt (fl.isOpen_Pa.mem_nhds hzPa)
  have hφgz : DifferentiableAt ℂ fl.φa ((Tantibar c)^[5] z) :=
    fl.φa_fatou.1.2.1.differentiableAt (fl.isOpen_Pa.mem_nhds hgzPa)
  have hφzR : DifferentiableAt ℝ fl.φa z := hφz.restrictScalars ℝ
  have hφgzR : DifferentiableAt ℝ fl.φa ((Tantibar c)^[5] z) := hφgz.restrictScalars ℝ
  have hEq : (fun w => fl.φa ((Tantibar c)^[5] w)) =ᶠ[𝓝 z]
      (fun w => star (fl.φa w) + 1 / 2) := by
    filter_upwards [fl.isOpen_Pa.mem_nhds hzPa] with w hw
    exact fl.φa_fatou.1.2.2 w hw
  have h1 : Work.MRMT.dzbar (fun w => fl.φa ((Tantibar c)^[5] w)) z =
      Work.MRMT.dzbar (fun w => star (fl.φa w) + 1 / 2) z := by
    simp only [Work.MRMT.dzbar, hEq.fderiv_eq]
  have h2 : Work.MRMT.dzbar (fun w => fl.φa ((Tantibar c)^[5] w)) z =
      Work.MRMT.dz fl.φa ((Tantibar c)^[5] z) * Work.MRMT.dzbar ((Tantibar c)^[5]) z := by
    have h := Work.MRMT.Wirtinger.dzbar_comp (f := (Tantibar c)^[5]) (g := fl.φa) hφgzR hga
    simpa only [Function.comp_def, Work.MRMT.Wirtinger.dzbar_of_holo hφgz, zero_mul,
      add_zero] using h
  have h5 : Work.MRMT.dzbar (fun w => star (fl.φa w) + 1 / 2) z = star (deriv fl.φa z) := by
    have hA : Work.MRMT.dzbar (star ∘ fl.φa) z = star (deriv fl.φa z) := by
      rw [dzbar_star_comp_fqc hφzR, dz_eq_deriv_of_holo hφz]
    have hB : Work.MRMT.dzbar (fun w => star (fl.φa w) + 1 / 2) z =
        Work.MRMT.dzbar (star ∘ fl.φa) z := by
      rw [show (fun w => star (fl.φa w) + 1 / 2) = (fun w => (star ∘ fl.φa) w + 1 / 2)
          from rfl, dzbar_add_const_fqc]
    rw [hB, hA]
  rw [h5] at h1
  rw [h2, dz_eq_deriv_of_holo hφgz] at h1
  exact h1

/-! ## 3. The coefficient on the fundamental domain is invariant under the return map -/

/-- **Return invariance on the fundamental domain.**  For `z ∈ Pg`, the coefficient
`ν = pullHoloOn (beltramiOf (ℓ_t)) φa Pg` of the twist on the petal is fixed by the five-fold
pull-back along `T_c`:

  `ν z = pullAntiIter (T_c) 5 ν z`.

This is the identity `ν = pullAnti^5 ν` on the petal, which combines
* the `5`-fold pull-back formula `Work.FQC.pullAntiIter_five_Tantibar`,
* the reflection identity `ν (conj w + 1/2) = conj (ν w)` of the twist
  (`Work.FQC.beltramiOf_ell_iota`),
* the differentiated Fatou relation `φa'(g z) · ∂̄g z = conj (φa'(z))`
  (`Work.FQC.fatou_deriv_relation`). -/
theorem pullHoloOn_eq_pullAntiIter_five {c : ℂ} (d : RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁)
    (hfl : PetalInput d fl) (t : ℝ) {z : ℂ} (hz : z ∈ hfl.Pg) :
    pullHoloOn (Work.MRMT.beltramiOf (ell t)) fl.φa hfl.Pg z =
      pullAntiIter (Tantibar c) 5 (pullHoloOn (Work.MRMT.beltramiOf (ell t)) fl.φa hfl.Pg) z := by
  classical
  have hgz : (Tantibar c)^[5] z ∈ hfl.Pg := hfl.mapsTo_g_Pg z hz
  have hzPa : z ∈ fl.Pa := hfl.Pg_sub hz
  have hφgz : fl.φa ((Tantibar c)^[5] z) = star (fl.φa z) + 1 / 2 :=
    fl.φa_fatou.1.2.2 z hzPa
  have hβι : Work.MRMT.beltramiOf (ell t) (star (fl.φa z) + 1 / 2) =
      star (Work.MRMT.beltramiOf (ell t) (fl.φa z)) := beltramiOf_ell_iota t (fl.φa z)
  have hE : deriv fl.φa ((Tantibar c)^[5] z) * Work.MRMT.dzbar ((Tantibar c)^[5]) z =
      star (deriv fl.φa z) := fatou_deriv_relation d fl hfl hz
  have hsplit : star (Work.MRMT.beltramiOf (ell t) (fl.φa ((Tantibar c)^[5] z))) =
      Work.MRMT.beltramiOf (ell t) (fl.φa z) := by
    rw [hφgz, hβι, star_star]
  have hνz : pullHoloOn (Work.MRMT.beltramiOf (ell t)) fl.φa hfl.Pg z =
      Work.MRMT.beltramiOf (ell t) (fl.φa z) * star (deriv fl.φa z) / deriv fl.φa z := by
    simp only [pullHoloOn, if_pos hz]
  have hνgz : pullHoloOn (Work.MRMT.beltramiOf (ell t)) fl.φa hfl.Pg ((Tantibar c)^[5] z) =
      Work.MRMT.beltramiOf (ell t) (fl.φa ((Tantibar c)^[5] z)) *
        star (deriv fl.φa ((Tantibar c)^[5] z)) / deriv fl.φa ((Tantibar c)^[5] z) := by
    simp only [pullHoloOn, if_pos hgz]
  have hmain := pullAntiIter_five_Tantibar c
    (pullHoloOn (Work.MRMT.beltramiOf (ell t)) fl.φa hfl.Pg) z
  have hA : star (pullHoloOn (Work.MRMT.beltramiOf (ell t)) fl.φa hfl.Pg ((Tantibar c)^[5] z)) =
      Work.MRMT.beltramiOf (ell t) (fl.φa z) * deriv fl.φa ((Tantibar c)^[5] z) /
        star (deriv fl.φa ((Tantibar c)^[5] z)) := by
    rw [hνgz]
    simp only [star_div₀, star_mul, star_star]
    rw [hsplit]
    ring
  have key : deriv fl.φa ((Tantibar c)^[5] z) / star (deriv fl.φa ((Tantibar c)^[5] z)) *
        (Work.MRMT.dzbar ((Tantibar c)^[5]) z / star (Work.MRMT.dzbar ((Tantibar c)^[5]) z)) =
      star (deriv fl.φa z) / deriv fl.φa z := by
    rw [div_mul_div_comm, show star (deriv fl.φa ((Tantibar c)^[5] z)) *
        star (Work.MRMT.dzbar ((Tantibar c)^[5]) z) =
        star (deriv fl.φa ((Tantibar c)^[5] z) * Work.MRMT.dzbar ((Tantibar c)^[5]) z)
        from by rw [← star_mul, mul_comm (Work.MRMT.dzbar ((Tantibar c)^[5]) z)
          (deriv fl.φa ((Tantibar c)^[5] z))]]
    rw [hE, star_star]
  rw [hA] at hmain
  have hgoal : pullHoloOn (Work.MRMT.beltramiOf (ell t)) fl.φa hfl.Pg z =
      pullAntiIter (Tantibar c) 5 (pullHoloOn (Work.MRMT.beltramiOf (ell t)) fl.φa hfl.Pg) z := by
    rw [hνz, hmain]
    rw [show Work.MRMT.beltramiOf (ell t) (fl.φa z) *
            deriv fl.φa ((Tantibar c)^[5] z) / star (deriv fl.φa ((Tantibar c)^[5] z)) *
            (Work.MRMT.dzbar ((Tantibar c)^[5]) z / star (Work.MRMT.dzbar ((Tantibar c)^[5]) z)) =
          Work.MRMT.beltramiOf (ell t) (fl.φa z) *
            (deriv fl.φa ((Tantibar c)^[5] z) / star (deriv fl.φa ((Tantibar c)^[5] z)) *
              (Work.MRMT.dzbar ((Tantibar c)^[5]) z /
                star (Work.MRMT.dzbar ((Tantibar c)^[5]) z))) by ring, key]
    ring
  exact hgoal

/-! ## 4. Bookkeeping of the least entry time into `Pg` -/

/-- Applying `T_c` decreases the least entry time into `Pg` by one, as long as it is positive. -/
theorem nat_find_basin_forward {c : ℂ} (d : RootParabolic c) {P : Set ℂ}
    (hP : ∀ z ∈ P, (Tantibar c)^[5] z ∈ P) {z : ℂ} (hz : z ∈ basin d P)
    (hn : 1 ≤ Nat.find hz) :
    Nat.find (basin_forward d hP hz) = Nat.find hz - 1 := by
  classical
  apply le_antisymm
  · apply Nat.find_le
    have hiter : (Tantibar c)^[Nat.find hz - 1] (Tantibar c z) = (Tantibar c)^[Nat.find hz] z := by
      conv_rhs => rw [← Nat.sub_add_cancel hn]
      rw [Function.iterate_succ_apply]
    rw [hiter]
    exact Nat.find_spec hz
  · set k := Nat.find (basin_forward d hP hz) with hk_def
    have hkspec : (Tantibar c)^[k] (Tantibar c z) ∈ P :=
      Nat.find_spec (basin_forward d hP hz)
    have hle : Nat.find hz ≤ k + 1 := by
      apply Nat.find_le
      have hiter : (Tantibar c)^[k + 1] z = (Tantibar c)^[k] (Tantibar c z) :=
        Function.iterate_succ_apply (Tantibar c) k z
      rw [hiter]
      exact hkspec
    omega

/-- For a point of the fundamental domain `Pg`, the least entry time of `T_c z` into `Pg` is
exactly `4`: `Pg` is a fundamental domain for the return map `T_c^[5]`. -/
theorem nat_find_basin_forward_eq_four {c : ℂ} (d : RootParabolic c) {P : Set ℂ}
    (hP : ∀ z ∈ P, (Tantibar c)^[5] z ∈ P)
    (hne : ∀ z ∈ P, ∀ r : ℕ, 1 ≤ r → r < 5 → (Tantibar c)^[r] z ∉ P)
    {z : ℂ} (hz : z ∈ basin d P) (hzP : z ∈ P) :
    Nat.find (basin_forward d hP hz) = 4 := by
  classical
  apply le_antisymm
  · apply Nat.find_le
    have hiter : (Tantibar c)^[4] (Tantibar c z) = (Tantibar c)^[5] z :=
      (Function.iterate_succ_apply (Tantibar c) 4 z).symm
    rw [hiter]
    exact hP z hzP
  · by_contra hcon
    push_neg at hcon
    set k := Nat.find (basin_forward d hP hz) with hk_def
    have hkspec : (Tantibar c)^[k] (Tantibar c z) ∈ P :=
      Nat.find_spec (basin_forward d hP hz)
    have hiter : (Tantibar c)^[k + 1] z = (Tantibar c)^[k] (Tantibar c z) :=
      Function.iterate_succ_apply (Tantibar c) k z
    have hmem : (Tantibar c)^[k + 1] z ∈ P := by rw [hiter]; exact hkspec
    exact hne z hzP (k + 1) (by omega) (by omega) hmem

/-! ## 5. The invariance of `muQC` -/

theorem muQC_invariant_pg {c : ℂ} (d : Work.EL.RootParabolic c) (fl : Work.FatouCoord.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁) (hfl : Work.FQC.PetalInput d fl) (t : ℝ) : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), Work.FQC.muQC d fl hfl.Pg t z = Work.FQC.pullAnti (Work.FQC.muQC d fl hfl.Pg t) (LeanEval.ComplexAnalysis.Tantibar c) z := by
  classical
  refine Filter.Eventually.of_forall (fun z => ?_)
  by_cases hz : z ∈ basin d hfl.Pg
  · by_cases hn0 : Nat.find hz = 0
    · have hzP : z ∈ hfl.Pg := by
        have h := Nat.find_spec hz
        rw [hn0] at h
        simpa using h
      have h5 := pullHoloOn_eq_pullAntiIter_five d fl hfl t hzP
      have hz2 : pullAnti (muQC d fl hfl.Pg t) (Tantibar c) z =
          pullAntiIter (Tantibar c) 5
            (pullHoloOn (Work.MRMT.beltramiOf (ell t)) fl.φa hfl.Pg) z := by
        have hfind : Nat.find (basin_forward d hfl.mapsTo_g_Pg hz) = 4 :=
          nat_find_basin_forward_eq_four d hfl.mapsTo_g_Pg hfl.no_early hz hzP
        have hsucc : pullAntiIter (Tantibar c) 5
            (pullHoloOn (Work.MRMT.beltramiOf (ell t)) fl.φa hfl.Pg) =
            pullAnti (pullAntiIter (Tantibar c) 4
              (pullHoloOn (Work.MRMT.beltramiOf (ell t)) fl.φa hfl.Pg)) (Tantibar c) :=
          pullAntiIter_succ (Tantibar c) 4
            (pullHoloOn (Work.MRMT.beltramiOf (ell t)) fl.φa hfl.Pg)
        simp only [pullAnti]
        rw [muQC_of_mem d (basin_forward d hfl.mapsTo_g_Pg hz), hfind, hsucc]
        rfl
      rw [muQC_of_mem d hz, hn0, pullAntiIter_zero, hz2]
      exact h5
    · have hn1 : 1 ≤ Nat.find hz := by omega
      have hfind := nat_find_basin_forward d hfl.mapsTo_g_Pg hz hn1
      have hsplit : Nat.find hz = (Nat.find hz - 1) + 1 := (Nat.sub_add_cancel hn1).symm
      have hsucc := pullAntiIter_succ (Tantibar c) (Nat.find hz - 1)
        (pullHoloOn (Work.MRMT.beltramiOf (ell t)) fl.φa hfl.Pg)
      simp only [pullAnti]
      rw [muQC_of_mem d hz, muQC_of_mem d (basin_forward d hfl.mapsTo_g_Pg hz), hfind]
      conv_lhs => rw [hsplit]
      rw [hsucc]
      rfl
  · have hTz : Tantibar c z ∉ basin d hfl.Pg :=
      fun h => hz ((basin_invariant d hfl.mapsTo_g_Pg).mp h)
    simp only [pullAnti]
    rw [muQC_of_notMem d hz, muQC_of_notMem d hTz]
    simp

end Work.FQC

end
