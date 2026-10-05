import Mathlib
import Submission.Work.RPB.Defs
import Submission.Work.RPB.B5.kappaDefs
import Submission.Work.RPB.B5.chartJets_oneSided
import Submission.Work.RPB.B5.noL_A0_jets

/-!
# B5: the specification of the phase constant `kA0` of the `κ`-parametrised collar

`Work.RPB.B5.kA0` is the constant of integration of the phase of the collar of
`collar_exists_kappa`:

`kA0 W ρh δ k τ σ = (kphc δ k σ + π/2 + 2πk) + ∑_{j<9} (kcj τ j - kcj 0 j) · (σ^j/j!) · kjbump δ σ`

We prove the three properties asked of it:

* its `σ`-jets at `σ = 0`, up to order `8`, are the `σ`-jets `kcj τ j` of the chart phase
  `σ ↦ (W τ 0 (ρh τ 0 σ)).1.2` (`kA0_jets`);
* it vanishes for `σ ≥ 2δ` (`kA0_far_zero`);
* on the `τ = 0` slice it reduces to `kphc δ k σ + π/2 + 2πk` (`kA0_tau_zero`).

## The jet computation

The first property is the only substantial one.  The definitions in `kappaDefs` are *identical*
to the corresponding no-`L` definitions (`A0`, `phc`, `jbump`, `cj`), so `kA0 = A0` up to
definitional equality; the jet statement for `A0` is `Work.RPB.B5.noL_A0_jets_aux`, whose proof
shows that `kA0` equals the truncated Taylor polynomial
`(π/2 + 2πk) + ∑_{j<9} (kcj τ j - kcj 0 j) σ^j/j!`
plus a `C^8` remainder vanishing on `(-∞,0]`, hence flat at `0`.  Combining the Taylor jets with
the hypothesis `h0` (which pins the jets of the `τ = 0` chart phase to the constant `π/2 + 2πk`)
yields the claim.
-/

set_option autoImplicit false

namespace Work.RPB.B5

/-- The `σ`-jets of `kA0` at `σ = 0`, up to order `8`, are the jets `kcj W ρh τ j` of the chart
phase at `t = 0`. -/
theorem kA0_jets (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ)
    (δ : ℝ) (hδ : 0 < δ) (k : ℤ) (τ : ℝ)
    (h0 : ∀ j : ℕ, j ≤ 8 → kcj W ρh 0 j
        = iteratedDeriv j (fun _ : ℝ => Real.pi / 2 + 2 * Real.pi * k) 0) :
    ∀ j : ℕ, j ≤ 8 → iteratedDeriv j (fun σ : ℝ => kA0 W ρh δ k τ σ) 0
        = kcj W ρh τ j := by
  intro j hj
  -- `kA0` is definitionally the no-`L` constant `A0`
  have hfun : (fun σ : ℝ => kA0 W ρh δ k τ σ) = (fun σ : ℝ => A0 W ρh δ k τ σ) := by
    funext σ; rfl
  rw [hfun, noL_A0_jets_aux W ρh hδ k τ j hj]
  -- the jets of the `τ = 0` chart phase are those of the constant `π/2 + 2πk`
  have hkcj0 : kcj W ρh 0 j
      = (if j = 0 then (Real.pi / 2 + 2 * Real.pi * k) else 0) := by
    rw [h0 j hj, iteratedDeriv_const]
  simp only [show cj W ρh τ j = kcj W ρh τ j from rfl,
    show cj W ρh 0 j = kcj W ρh 0 j from rfl]
  rw [hkcj0]
  by_cases h : j = 0 <;> simp [h]

/-- `kA0` vanishes for `σ ≥ 2δ`: the bump `kjbump` is `0` there and the phase offset `kphc`
cancels the constant `π/2 + 2πk`. -/
theorem kA0_far_zero (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ)
    (δ : ℝ) (hδ : 0 < δ) (k : ℤ) (τ : ℝ) :
    ∀ σ : ℝ, 2 * δ ≤ σ → kA0 W ρh δ k τ σ = 0 := by
  intro σ hσ
  have hphc : kphc δ k σ = -(Real.pi / 2) - 2 * Real.pi * k := by
    rw [kphc, kstp_one (by rw [le_div_iff₀ hδ]; linarith)]
    ring
  have hjb : kjbump δ σ = 0 := by
    rw [kjbump, kstp_one (by rw [le_div_iff₀ hδ]; linarith)]
    ring
  rw [kA0, hphc, hjb]
  simp
  ring

/-- On the `τ = 0` slice the jet-difference sum of `kA0` vanishes identically. -/
theorem kA0_tau_zero (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ)
    (δ : ℝ) (k : ℤ) (σ : ℝ) :
    kA0 W ρh δ k 0 σ = kphc δ k σ + Real.pi / 2 + 2 * Real.pi * k := by
  rw [kA0]
  simp

/-- The specification of the phase constant `kA0` of the `κ`-parametrised collar. -/
theorem kA0_spec (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ)
    (δ : ℝ) (hδ : 0 < δ) (k : ℤ) (τ : ℝ)
    (h0 : ∀ j : ℕ, j ≤ 8 → Work.RPB.B5.kcj W ρh 0 j
        = iteratedDeriv j (fun _ : ℝ => Real.pi / 2 + 2 * Real.pi * k) 0) :
    (∀ j : ℕ, j ≤ 8 → iteratedDeriv j (fun σ : ℝ => Work.RPB.B5.kA0 W ρh δ k τ σ) 0
        = Work.RPB.B5.kcj W ρh τ j) ∧
    (∀ σ : ℝ, 2 * δ ≤ σ → Work.RPB.B5.kA0 W ρh δ k τ σ = 0) ∧
    (∀ σ : ℝ, Work.RPB.B5.kA0 W ρh δ k 0 σ
        = Work.RPB.B5.kphc δ k σ + Real.pi / 2 + 2 * Real.pi * k) := by
  exact ⟨kA0_jets W ρh δ hδ k τ h0, kA0_far_zero W ρh δ hδ k τ,
    kA0_tau_zero W ρh δ k⟩

end Work.RPB.B5
