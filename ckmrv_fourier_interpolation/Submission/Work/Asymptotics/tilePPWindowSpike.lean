import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.AfunFun_crossed_vanish
import Submission.Work.Asymptotics.Kaxis_principal_part_bound
import Submission.Work.Asymptotics.PGWide.MMPHoles
import Submission.Work.Asymptotics.KfunClear_vanish_of_phiPair
import Submission.Work.Asymptotics.SpikeTile.orbit_dist_one_le
import Submission.Work.Asymptotics.SpikeTile.jprime_ne_zero_KEpsilon
import Submission.Work.Asymptotics.SpikeTile.Kfun_pp_bounded_near_pole
import Submission.Work.Asymptotics.SpikeTile.Kfun_pp_bounded_near_crossed

/-!
# The spike of the tile principal-part window on the cusp-`±1` tiles

The contour point `ζ = i t` of the tile window `t ∈ [Im w / 2, 1]` is *on the spike* when its
`S`-image `z = i/t` comes within `1/8` of a lattice translate of `u = S • w`, i.e. when
`dist(z, u + ℤ) < 1/8`.  There the elementary (off-spike) bound
`Work.Asymptotics.offspike_bound_E` does not apply, because `z` approaches an `SL(2,ℤ)`-orbit
point of `w`, where `ζ ↦ K^{(d)}(n +ᵥ w, ζ)` has (at worst) a pole, cancelled by the principal
part `(n/2π)/(ζ - w)`.

The point of this file is that the *off-spike* hypothesis `hoff` (a bound for the kernel
remainder on the off-spike region) already implies the *on-spike* bound, by the maximum modulus
principle applied to the function

  `F(z) = K^{(d)}(n +ᵥ w, ofComplex (-z⁻¹)) + (n/2π)·z/(1 + w z)`

on the disc `{‖z - c‖ < 1/2}`, `c = S • w + k` (`k` the index of the spike).  The apparent pole
of `F` at the centre `z = c` is removable: the centre is the *only* `SL(2,ℤ)`-orbit point of `w`
in the disc (orbit separation), and at that point the kernel either has the principal part
`(n/2π)/(ζ - w)` (the case `k = 0`, where `ζ = w`) or is regular with vanishing numerator
(`k = ±1`, the crossed orbit points, `Work.Asymptotics.AfunFun_crossed_vanish`).

## Main results

* `Work.Asymptotics.tilePPWindowSpike` : the target.
-/

noncomputable section

open UpperHalfPlane ModularGroup
open scoped MatrixGroups Manifold Topology

namespace Work.Asymptotics

/-- The spike centre `c = S • w + k` in the `z = S ζ`-plane (as a complex number). -/
def spikeC (w : UpperHalfPlane) (k : ℤ) : ℂ := ((ModularGroup.S • w : UpperHalfPlane) : ℂ) + (k : ℂ)

/-- The `ℍ`-point of the spike centre (the translate `T^k • (S • w)`). -/
def spikeU (w : UpperHalfPlane) (k : ℤ) : UpperHalfPlane :=
  (ModularGroup.T ^ k) • (ModularGroup.S • w)

/-- The spike point in the `ζ`-plane, the `S`-image of the spike centre. -/
def spikeP (w : UpperHalfPlane) (k : ℤ) : UpperHalfPlane :=
  ModularGroup.S • spikeU w k

lemma coe_spikeU (w : UpperHalfPlane) (k : ℤ) : ((spikeU w k : UpperHalfPlane) : ℂ) = spikeC w k := by
  rw [spikeU, spikeC, UpperHalfPlane.modular_T_zpow_smul, UpperHalfPlane.coe_vadd]
  push_cast
  ring

lemma coe_spikeP (w : UpperHalfPlane) (k : ℤ) :
    ((spikeP w k : UpperHalfPlane) : ℂ) = (-(spikeC w k))⁻¹ := by
  rw [spikeP, UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, coe_spikeU]

lemma spikeC_im_pos (w : UpperHalfPlane) (k : ℤ) : 0 < (spikeC w k).im := by
  have h1 : ((k : ℂ)).im = 0 := by simp
  have h2 : (((ModularGroup.S • w : UpperHalfPlane) : ℂ)).im = (ModularGroup.S • w).im :=
    UpperHalfPlane.coe_im _
  rw [spikeC, Complex.add_im, h1, add_zero, h2]
  exact (ModularGroup.S • w).im_pos

lemma ofComplex_spikeC (w : UpperHalfPlane) (k : ℤ) :
    UpperHalfPlane.ofComplex (spikeC w k) = spikeU w k := by
  refine UpperHalfPlane.ext ?_
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos (spikeC_im_pos w k), coe_spikeU]

lemma coe_spikeP' (w : UpperHalfPlane) (k : ℤ) :
    spikeP w k = ModularGroup.S • UpperHalfPlane.ofComplex (spikeC w k) := by
  rw [spikeP, ofComplex_spikeC]

/-! ## Elementary geometry of the spike -/

/-- On the cusp-`0` tile `E = KEpsilon` the `S`-image has real part in `(-1,1)`. -/
lemma abs_re_S_smul_lt_one {w : UpperHalfPlane} (hw : w ∈ KEpsilon) :
    |(ModularGroup.S • w).re| < 1 := by
  have h := S_smul_mem_DomainD hw.1
  rw [abs_lt]
  exact ⟨h.1, h.2.1⟩

/-- **The index of the spike.**  If the contour image `z` (of real part `0`) is within `1/8` of
`S • w + k`, then `k ∈ {-1, 0, 1}`.  Indeed `|Re (S • w)| < 1`, so `|Re (S • w) + k| < 1/8`
forces `|k| ≤ 1`. -/
lemma spike_int_index {w : UpperHalfPlane} (hw : w ∈ KEpsilon) (z : ℂ) (hz : z.re = 0) (k : ℤ)
    (h : ‖z - ((ModularGroup.S • w : UpperHalfPlane) : ℂ) - (k : ℂ)‖ < 1 / 8) :
    k = 0 ∨ k = 1 ∨ k = -1 := by
  have hre := abs_re_S_smul_lt_one hw
  have h1 : ((k : ℂ)).re = (k : ℝ) := by simp
  have h2 : (((ModularGroup.S • w : UpperHalfPlane) : ℂ)).re = (ModularGroup.S • w).re :=
    UpperHalfPlane.coe_re _
  have hrc : (z - ((ModularGroup.S • w : UpperHalfPlane) : ℂ) - (k : ℂ)).re
      = -((ModularGroup.S • w).re + (k : ℝ)) := by
    rw [Complex.sub_re, Complex.sub_re, hz, h1, h2]
    ring
  have hkey : |(ModularGroup.S • w).re + (k : ℝ)| < 1 / 8 := by
    have hle : |(z - ((ModularGroup.S • w : UpperHalfPlane) : ℂ) - (k : ℂ)).re| ≤
        ‖z - ((ModularGroup.S • w : UpperHalfPlane) : ℂ) - (k : ℂ)‖ := Complex.abs_re_le_norm _
    rw [hrc, abs_neg] at hle
    linarith
  have hkR : |((k : ℝ))| < 9 / 8 := by
    have hab : |((k : ℝ))| ≤ |(ModularGroup.S • w).re + (k : ℝ)| + |(ModularGroup.S • w).re| := by
      have h2' := abs_add_le ((ModularGroup.S • w).re + (k : ℝ)) (-(ModularGroup.S • w).re)
      have heq : ((ModularGroup.S • w).re + (k : ℝ)) + (-(ModularGroup.S • w).re) = ((k : ℝ)) := by
        ring
      rw [heq, abs_neg] at h2'
      exact h2'
    linarith
  have hk_le : k ≤ 1 := by
    by_contra hc
    have h2' : (2 : ℤ) ≤ k := by omega
    have h3 : (2 : ℝ) ≤ ((k : ℤ) : ℝ) := by exact_mod_cast h2'
    have h4 : ((k : ℤ) : ℝ) < 9 / 8 := (abs_lt.mp hkR).2
    linarith
  have hk_ge : -1 ≤ k := by
    by_contra hc
    have h2' : k ≤ -2 := by omega
    have h3 : ((k : ℤ) : ℝ) ≤ (-2 : ℝ) := by exact_mod_cast h2'
    have h4 : (-(9 / 8) : ℝ) < ((k : ℤ) : ℝ) := (abs_lt.mp hkR).1
    linarith
  omega

section SpikeOrbit

/-- **The only `j`-coincidence in the spike disc.**  For `w ∈ E`, `n = ±1` and `z ∈ ℍ` with
`‖z - (S • w + k)‖ < 1/2`, the point `ζ = ofComplex (-z⁻¹)` of the `ζ`-plane is
`j`-equivalent to `n +ᵥ w` only if `z` *is* the spike centre. -/
lemma eq_spikeC_of_jInvariantFun_eq {w : UpperHalfPlane} (hw : w ∈ KEpsilon) (n : ℤ)
    (hn : n = 1 ∨ n = -1) (k : ℤ) {z : ℂ} (hz : 0 < z.im)
    (hball : ‖z - spikeC w k‖ < 1)
    (h : Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex (-(z)⁻¹))
      = Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)) :
    z = spikeC w k := by
  have hzn : (0 : ℝ) < ‖z‖ ^ 2 := by
    have hz0 : z ≠ 0 := by rintro rfl; simp at hz
    positivity
  have himinv : 0 < (-(z)⁻¹).im := by
    rw [Complex.neg_im, Complex.inv_im, Complex.normSq_eq_norm_sq, neg_div, neg_neg]
    exact div_pos hz hzn
  set ζ : UpperHalfPlane := UpperHalfPlane.ofComplex (-(z)⁻¹) with hζdef
  have hζcoe : (ζ : ℂ) = -(z)⁻¹ := by
    rw [hζdef]
    exact congrArg (fun x : UpperHalfPlane => (x : ℂ))
      (UpperHalfPlane.ofComplex_apply_of_im_pos himinv)
  obtain ⟨γ, hγ⟩ := jInvariantFun_eq_smul_of_eq h
  set u : UpperHalfPlane := ModularGroup.S • w with hudef
  set zH : UpperHalfPlane := UpperHalfPlane.ofComplex z with hzHdef
  have hzHcoe : (zH : ℂ) = z := by
    rw [hzHdef]
    exact congrArg (fun x : UpperHalfPlane => (x : ℂ))
      (UpperHalfPlane.ofComplex_apply_of_im_pos hz)
  have hSζ : (ModularGroup.S • ζ : UpperHalfPlane) = zH := by
    refine UpperHalfPlane.ext ?_
    rw [hzHcoe, UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, hζcoe]
    field_simp
  set η : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
    ModularGroup.S * γ * ModularGroup.T ^ n with hηdef
  have hzH1 : zH = η • w := by
    rw [← hSζ, ← hγ, ← UpperHalfPlane.modular_T_zpow_smul w n, hηdef]
    simp only [mul_smul]
  set η' : Matrix.SpecialLinearGroup (Fin 2) ℤ := η * ModularGroup.S with hη'def
  have hWu : η' • u = η • w := by
    rw [hη'def, hudef]
    simp only [mul_smul, S_smul_S_smul]
  have hzH2 : zH = η' • u := hzH1.trans hWu.symm
  have hcoe1 : (((ModularGroup.T ^ (-k) * η') • u : UpperHalfPlane) : ℂ) = z - (k : ℂ) := by
    rw [mul_smul, ← hzH2, UpperHalfPlane.modular_T_zpow_smul, UpperHalfPlane.coe_vadd, hzHcoe]
    push_cast
    ring
  have hdist : ‖(((ModularGroup.T ^ (-k) * η') • u : UpperHalfPlane) : ℂ) - (u : ℂ)‖
      = ‖z - spikeC w k‖ := by
    have hu : ((u : UpperHalfPlane) : ℂ) = ((ModularGroup.S • w : UpperHalfPlane) : ℂ) := by
      rw [hudef]
    have harg : (((ModularGroup.T ^ (-k) * η') • u : UpperHalfPlane) : ℂ) - (u : ℂ)
        = z - spikeC w k := by
      rw [hcoe1, hu, spikeC]
      ring
    rw [harg]
  by_contra hne
  have hbig : 1 ≤ ‖(((ModularGroup.T ^ (-k) * η') • u : UpperHalfPlane) : ℂ) - (u : ℂ)‖ :=
    SpikeTile.orbit_dist_one_le hw.2 (ModularGroup.T ^ (-k) * η') (fun hcon => hne (by
      have h1 : (ModularGroup.T ^ (-k)) • zH = u := by
        rw [hzH2, ← mul_smul]
        exact hcon
      have h2 : zH = (ModularGroup.T ^ k) • u := by
        rw [← h1, ← mul_smul, ← zpow_add, add_neg_cancel, zpow_zero, one_smul]
      calc z = (zH : ℂ) := hzHcoe.symm
        _ = (((ModularGroup.T ^ k) • u : UpperHalfPlane) : ℂ) := by rw [h2]
        _ = spikeC w k := by
            rw [UpperHalfPlane.modular_T_zpow_smul, UpperHalfPlane.coe_vadd, hudef, spikeC]
            push_cast
            ring))
  rw [hdist] at hbig
  linarith

end SpikeOrbit


/-! ## The crossed orbit points

For `k = ±1` the spike centre `S • (T^k • (S • w))` is the *crossed* orbit point
`(S T^k S) • w` of `Work.Asymptotics.AfunFun_crossed_vanish`: the kernel numerator vanishes
there, so the kernel has no pole. -/

section Crossed

lemma coe_ofComplex_of_pos {c : ℂ} (hc : 0 < c.im) :
    ((UpperHalfPlane.ofComplex c : UpperHalfPlane) : ℂ) = c :=
  congrArg (fun x : UpperHalfPlane => (x : ℂ)) (UpperHalfPlane.ofComplex_apply_of_im_pos hc)

lemma neg_inv_im_pos {z : ℂ} (hz : 0 < z.im) : 0 < (-(z)⁻¹).im := by
  have hzn : (0 : ℝ) < ‖z‖ ^ 2 := by
    have hz0 : z ≠ 0 := by rintro rfl; simp at hz
    positivity
  rw [Complex.neg_im, Complex.inv_im, Complex.normSq_eq_norm_sq, neg_div, neg_neg]
  exact div_pos hz hzn

lemma spikeP_eq (w : UpperHalfPlane) (k : ℤ) :
    spikeP w k = (ModularGroup.S * ModularGroup.T ^ k * ModularGroup.S) • w := by
  rw [spikeP, spikeU, mul_smul, mul_smul]

lemma spikeP_zero (w : UpperHalfPlane) : spikeP w 0 = w := by
  rw [spikeP_eq, zpow_zero, mul_one, mul_smul, S_smul_S_smul]

/-- **The crossed spike points carry no pole.** -/
lemma spikeP_afun_zero (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (w : UpperHalfPlane) (hw : w ∈ KEpsilon) (n : ℤ) (hn : n = 1 ∨ n = -1) {k : ℤ}
    (hk : k = 1 ∨ k = -1) :
    AfunFun ℓ d ((n : ℝ) +ᵥ w) (spikeP w k) = 0 := by
  have hjpw : Work.Residues.jprime w ≠ 0 := SpikeTile.jprime_ne_zero_KEpsilon hw
  have hj : (-k) = 1 ∨ (-k) = -1 ∨ (-k) = 3 ∨ (-k) = -3 := by omega
  have h := AfunFun_crossed_vanish ℓ d hd n (-k) hn hj w hjpw
  rw [show (ModularGroup.S * ModularGroup.T ^ (-(-k)) * ModularGroup.S) • w
      = spikeP w k by rw [neg_neg, spikeP_eq]] at h
  exact h

lemma spikeP_j_eq (w : UpperHalfPlane) (n : ℤ) (hn : n = 1 ∨ n = -1) (k : ℤ) :
    Work.Kernels.jInvariantFun (spikeP w k) = Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w) := by
  have hjn : Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w) = Work.Kernels.jInvariantFun w := by
    rw [← UpperHalfPlane.modular_T_zpow_smul w n]
    exact jInvariantFun_smul_of_slash (ModularGroup.T ^ n) w
  rw [hjn, spikeP_eq]
  exact jInvariantFun_smul_of_slash _ w

lemma spikeP_jprime_ne_zero (w : UpperHalfPlane) (hw : w ∈ KEpsilon) (k : ℤ) :
    Work.Residues.jprime (spikeP w k) ≠ 0 := by
  have hjpw : Work.Residues.jprime w ≠ 0 := SpikeTile.jprime_ne_zero_KEpsilon hw
  have h := jprime_smul_ne_zero_of_slash
    (ModularGroup.S * ModularGroup.T ^ k * ModularGroup.S) w hjpw
  rwa [← spikeP_eq] at h

lemma spikeP_ne_w (w : UpperHalfPlane) {k : ℤ} (hk : k = 1 ∨ k = -1) : spikeP w k ≠ w := by
  intro h
  have h2 : ModularGroup.S • spikeP w k = ModularGroup.S • w := by rw [h]
  rw [spikeP, S_smul_S_smul] at h2
  have h4 : spikeC w k = (((ModularGroup.S • w : UpperHalfPlane)) : ℂ) + 0 := by
    rw [add_zero, ← h2, coe_spikeU]
  rw [spikeC] at h4
  have h3 : ((k : ℂ)) = 0 := add_left_cancel h4
  have hk0 : ((k : ℝ)) = 0 := by
    have h5 : (((k : ℤ) : ℝ) : ℂ) = 0 := by push_cast; exact h3
    exact Complex.ofReal_eq_zero.mp h5
  have : k = 0 := by exact_mod_cast hk0
  omega

end Crossed

/-! ## Temporary local copies of the delegated lemmas -/


/-- The `z`-plane picture of the kernel remainder: with `ζ = ofComplex (-z⁻¹)`,
`F(z) = K(n +ᵥ w, ζ) - (n/2π)/(ζ - w)`. -/
def spikeF (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (w : UpperHalfPlane) (n : ℤ) : ℂ → ℂ :=
  fun z => Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (UpperHalfPlane.ofComplex (-(z)⁻¹))
    + ((n : ℂ) / (2 * (Real.pi : ℂ))) * (z * (1 + (w : ℂ) * z)⁻¹)

@[simp] lemma spikeF_apply (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (w : UpperHalfPlane)
    (n : ℤ) (z : ℂ) :
    spikeF ℓ d w n z = Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (UpperHalfPlane.ofComplex (-(z)⁻¹))
      + ((n : ℂ) / (2 * (Real.pi : ℂ))) * (z * (1 + (w : ℂ) * z)⁻¹) := rfl

/-- `1 + wz = 0` forces `z = -1/w`. -/
lemma one_add_mul_eq_zero {w : UpperHalfPlane} {z : ℂ} (h : 1 + (w : ℂ) * z = 0) :
    z = -((w : ℂ))⁻¹ := by
  have hw0 : (w : ℂ) ≠ 0 := w.ne_zero
  have h2 : (w : ℂ) * z = -1 := by linear_combination h
  calc z = ((w : ℂ))⁻¹ * ((w : ℂ) * z) := by rw [← mul_assoc, inv_mul_cancel₀ hw0, one_mul]
    _ = ((w : ℂ))⁻¹ * (-1) := by rw [h2]
    _ = -((w : ℂ))⁻¹ := by ring

/-! ## Translation of a punctured-disc bound from the `ζ`-plane to the `z`-plane -/

/-- **Translation of the local bound to the `z`-plane.**  A bound for the kernel remainder
`ζ ↦ K(τ,ζ) - (n/2π)/(ζ - w)` on a `ζ`-disc around `ζc = S c` gives a bound for
`z ↦ K(τ, ofComplex (-z⁻¹)) + (n/2π)·z/(1 + wz)` on a punctured `z`-disc around `c`. -/
lemma exists_bound_of_zeta_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (τ w : UpperHalfPlane) (n : ℤ)
    {c : ℂ} (hc : 0 < c.im) {ζc : UpperHalfPlane} (hζc : (ζc : ℂ) = -((c)⁻¹))
    (hcz : ∀ z : ℂ, ‖z - c‖ < 1 / 2 → z ≠ c → 1 + (w : ℂ) * z ≠ 0)
    {δ₁ B : ℝ} (hδ₁ : 0 < δ₁) (hB : 0 ≤ B)
    (hbdd : ∀ ζ : UpperHalfPlane, ‖(ζ : ℂ) - (ζc : ℂ)‖ < δ₁ → ζ ≠ ζc →
      ‖Work.Kernels.Kfun ℓ d τ ζ - ((n : ℂ) / (2 * (Real.pi : ℂ))) * (((ζ : ℂ) - (w : ℂ))⁻¹)‖
        ≤ B) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ 0 ≤ B ∧ ∀ z : ℂ, ‖z - c‖ < δ → z ≠ c →
      ‖Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex (-(z)⁻¹))
        + ((n : ℂ) / (2 * (Real.pi : ℂ))) * (z * (1 + (w : ℂ) * z)⁻¹)‖ ≤ B := by
  have hc0 : c ≠ 0 := by
    intro h; rw [h] at hc; simp at hc
  have hcont : ContinuousAt (fun z : ℂ => -(z)⁻¹) c :=
    continuousAt_neg.comp (continuousAt_inv₀ hc0)
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hcont δ₁ hδ₁
  refine ⟨min δ (min (1 / 4) (c.im / 2)), ?_, ?_, hB, ?_⟩
  · exact lt_min hδpos (lt_min (by norm_num) (by linarith))
  · exact lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_left _ _))
      (by norm_num : (1 : ℝ) / 4 < 1 / 2)
  · intro z hz hzne
    have hzlt : ‖z - c‖ < δ := lt_of_lt_of_le hz (le_trans (min_le_left _ _) le_rfl)
    have hzsmall : ‖z - c‖ < min (1 / 4) (c.im / 2) :=
      lt_of_lt_of_le hz (min_le_right _ _)
    have hzhalf : ‖z - c‖ < 1 / 2 :=
      lt_trans (lt_of_lt_of_le hzsmall (min_le_left _ _)) (by norm_num : (1 : ℝ) / 4 < 1 / 2)
    have hzcim : ‖z - c‖ < c.im / 2 := lt_of_lt_of_le hzsmall (min_le_right _ _)
    have hzim : 0 < z.im := by
      have h1 : |z.im - c.im| ≤ ‖z - c‖ := by
        have h2 := Complex.abs_im_le_norm (z - c)
        rwa [Complex.sub_im] at h2
      have h3 : -(‖z - c‖) ≤ z.im - c.im := (abs_le.mp h1).1
      linarith
    have hzdist : dist (-(z)⁻¹) (-(c)⁻¹) < δ₁ := hδ (by simpa [dist_eq_norm] using hzlt)
    have hζz : ((UpperHalfPlane.ofComplex (-(z)⁻¹) : UpperHalfPlane) : ℂ) = -(z)⁻¹ :=
      coe_ofComplex_of_pos (neg_inv_im_pos hzim)
    have hdist : ‖((UpperHalfPlane.ofComplex (-(z)⁻¹) : UpperHalfPlane) : ℂ) - (ζc : ℂ)‖
        < δ₁ := by
      rw [hζz, hζc]
      simpa [dist_eq_norm] using hzdist
    have hneζ : UpperHalfPlane.ofComplex (-(z)⁻¹) ≠ ζc := by
      intro h
      have h1 : (z)⁻¹ = (c)⁻¹ := by
        have h1' : -(z)⁻¹ = -(c)⁻¹ := by rw [← hζz, h, hζc]
        simpa using (neg_injective h1')
      have h2 : z = c := inv_injective h1
      exact hzne h2
    have hb := hbdd _ hdist hneζ
    have hzp : z ≠ 0 := by
      intro h; rw [h] at hzim; simp at hzim
    have hkey : (((UpperHalfPlane.ofComplex (-(z)⁻¹) : UpperHalfPlane) : ℂ) - (w : ℂ))⁻¹
        = -(z * (1 + (w : ℂ) * z)⁻¹) := by
      rw [hζz]
      have h1 : -(z)⁻¹ - (w : ℂ) = -((1 + (w : ℂ) * z) / z) := by
        field_simp
        ring
      rw [h1, inv_neg, inv_div]
      ring
    rw [show Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex (-(z)⁻¹))
          + ((n : ℂ) / (2 * (Real.pi : ℂ))) * (z * (1 + (w : ℂ) * z)⁻¹)
        = Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex (-(z)⁻¹))
          - ((n : ℂ) / (2 * (Real.pi : ℂ)))
            * ((((UpperHalfPlane.ofComplex (-(z)⁻¹) : UpperHalfPlane) : ℂ) - (w : ℂ))⁻¹) from by
      rw [hkey]; ring]
    exact hb

/-! ## Boundedness of the kernel remainder on a punctured disc around the spike centre -/

/-- **Boundedness near the spike centre.**  For `w ∈ E`, `n = ±1` and the spike index
`k ∈ {-1,0,1}`, the kernel remainder is bounded on a punctured disc around the spike centre
`c = S • w + k`, with radius `< 1/2`. -/
lemma exists_bound_punctured_ball (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (w : UpperHalfPlane) (hw : w ∈ KEpsilon) (n : ℤ)
    (hn : n = 1 ∨ n = -1) (k : ℤ) (hk : k = 0 ∨ k = 1 ∨ k = -1) :
    ∃ δ B : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ 0 ≤ B ∧ ∀ z : ℂ, ‖z - spikeC w k‖ < δ →
      z ≠ spikeC w k →
      ‖spikeF ℓ d w n z‖ ≤ B := by
  have hjpw : Work.Residues.jprime w ≠ 0 := SpikeTile.jprime_ne_zero_KEpsilon hw
  have hcpos : 0 < (spikeC w k).im := spikeC_im_pos w k
  have hw0 : (w : ℂ) ≠ 0 := w.ne_zero
  have hS : (((ModularGroup.S • w : UpperHalfPlane)) : ℂ) = -((w : ℂ))⁻¹ := by
    rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, inv_neg]
  have hrec : ∀ z : ℂ, 1 + (w : ℂ) * z = 0 → z = -((w : ℂ))⁻¹ := by
    intro z h0
    have h2 : (w : ℂ) * z = -1 := by linear_combination h0
    calc z = ((w : ℂ))⁻¹ * ((w : ℂ) * z) := by rw [← mul_assoc, inv_mul_cancel₀ hw0, one_mul]
      _ = ((w : ℂ))⁻¹ * (-1) := by rw [h2]
      _ = -((w : ℂ))⁻¹ := by ring
  rcases hk with rfl | hk'
  · -- `k = 0`: the spike centre is the translate pole `w`
    obtain ⟨δ₁, B, hδ₁, hB, hbdd⟩ := SpikeTile.Kfun_pp_bounded_near_pole ℓ d hd w n hn hjpw
    have hζc : ((w : UpperHalfPlane) : ℂ) = -(((spikeC w 0))⁻¹) := by
      rw [spikeC, Int.cast_zero, add_zero, hS, inv_neg, inv_inv, neg_neg]
    have hcz : ∀ z : ℂ, ‖z - spikeC w 0‖ < 1 / 2 → z ≠ spikeC w 0 →
        1 + (w : ℂ) * z ≠ 0 := by
      intro z _ hzne h0
      refine hzne ?_
      rw [spikeC, Int.cast_zero, add_zero, hS, hrec z h0]
    obtain ⟨δ₂, hδ₂pos, hδ₂lt, hB', hb₂⟩ :=
      exists_bound_of_zeta_bound ℓ d ((n : ℝ) +ᵥ w) w n (c := spikeC w 0) (ζc := w)
        hcpos hζc hcz hδ₁ hB hbdd
    exact ⟨δ₂, B, hδ₂pos, hδ₂lt, hB, hb₂⟩
  · -- `k = ±1`: the spike centre is a crossed orbit point
    have hknn : k = 1 ∨ k = -1 := hk'
    have hζc : ((spikeP w k : UpperHalfPlane) : ℂ) = -(((spikeC w k))⁻¹) := by
      rw [coe_spikeP, inv_neg]
    have hcz : ∀ z : ℂ, ‖z - spikeC w k‖ < 1 / 2 → z ≠ spikeC w k →
        1 + (w : ℂ) * z ≠ 0 := by
      intro z hz _ h0
      have h1 : z = -((w : ℂ))⁻¹ := hrec z h0
      have h2 : spikeC w k = -((w : ℂ))⁻¹ + (k : ℂ) := by rw [spikeC, hS]
      have h3 : ‖(k : ℂ)‖ = 1 := by rcases hknn with h | h <;> rw [h] <;> norm_num
      have h4 : z - spikeC w k = -(k : ℂ) := by rw [h1, h2]; ring
      rw [h4, norm_neg, h3] at hz
      norm_num at hz
    obtain ⟨δ₁, B, hδ₁, hB, hbdd⟩ :=
      SpikeTile.Kfun_pp_bounded_near_crossed ℓ d hd w n hn (spikeP w k)
        (spikeP_j_eq w n hn k) (spikeP_afun_zero ℓ d hd w hw n hn hknn)
        (spikeP_jprime_ne_zero w hw k) (spikeP_ne_w w hknn)
    obtain ⟨δ₂, hδ₂pos, hδ₂lt, hB', hb₂⟩ :=
      exists_bound_of_zeta_bound ℓ d ((n : ℝ) +ᵥ w) w n (c := spikeC w k) (ζc := spikeP w k)
        hcpos hζc hcz hδ₁ hB hbdd
    exact ⟨δ₂, B, hδ₂pos, hδ₂lt, hB, hb₂⟩

/-- The rational identity behind the `z`-plane picture: for `ζ = -z⁻¹`,
`(ζ - w)⁻¹ = -z(1+wz)⁻¹`. -/
lemma inv_sub_eq_neg (z w : ℂ) (hz : z ≠ 0) (hw : 1 + w * z ≠ 0) :
    (-(z)⁻¹ - w)⁻¹ = -(z * (1 + w * z)⁻¹) := by
  have h1 : -(z)⁻¹ - w = -((1 + w * z) / z) := by
    field_simp
    ring
  rw [h1, inv_neg, inv_div]
  ring

lemma norm_neg_inv_sub_add_one (w : ℂ) : ‖-(w)⁻¹ - (-(w)⁻¹ + 1)‖ = 1 := by
  have h : -(w)⁻¹ - (-(w)⁻¹ + 1) = -(1 : ℂ) := by ring
  rw [h, norm_neg, norm_one]

lemma norm_neg_inv_sub_add_neg_one (w : ℂ) : ‖-(w)⁻¹ - (-(w)⁻¹ + (-1))‖ = 1 := by
  have h : -(w)⁻¹ - (-(w)⁻¹ + (-1)) = (1 : ℂ) := by ring
  rw [h, norm_one]

/-! ## The spike bound -/

theorem tilePPWindowSpike (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hoff : ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon →
      ∀ (n : ℤ), (n = 1 ∨ n = -1) → ∀ (ζ : UpperHalfPlane),
        1 ≤ ((ModularGroup.S • ζ : UpperHalfPlane)).im →
        (∀ k : ℤ, (1 / 8 : ℝ) ≤
          ‖((ModularGroup.S • ζ : UpperHalfPlane) : ℂ)
            - ((ModularGroup.S • w : UpperHalfPlane) : ℂ) - ((k : ℤ) : ℂ)‖) →
        ‖Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) ζ
            - ((n : ℂ) / (2 * (Real.pi : ℂ))) * (((ζ : ℂ) - (w : ℂ))⁻¹)‖
          ≤ C * (Work.Kernels.scale w) ^ N) :
    ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon →
      ∀ (n : ℤ), (n = 1 ∨ n = -1) → ∀ (t : ℝ) (ht : 0 < t), w.im / 2 ≤ t → t ≤ 1 →
        (∃ k : ℤ, ‖((ModularGroup.S • (Work.Kernels.imagAxis t ht) : UpperHalfPlane) : ℂ)
            - ((ModularGroup.S • w : UpperHalfPlane) : ℂ) - ((k : ℤ) : ℂ)‖ < 1 / 8) →
        ((t : ℂ) * Complex.I) ≠ (w : ℂ) →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
            - ((n : ℂ) / (2 * (Real.pi : ℂ))) * (((t : ℂ) * Complex.I - (w : ℂ))⁻¹)‖
          ≤ C * (Work.Kernels.scale w) ^ N := by
  obtain ⟨Ch, Nh, hCh, hNh, hoff⟩ := hoff
  refine ⟨Ch, Nh, hCh, hNh, ?_⟩
  intro w hw n hn t ht h1 h2 hspike hne
  obtain ⟨k, hk⟩ := hspike
  -- ### the contour image and the spike centre
  set z₀ : ℂ := ((ModularGroup.S • (Work.Kernels.imagAxis t ht) : UpperHalfPlane) : ℂ) with hz₀def
  have hkball : ‖z₀ - spikeC w k‖ < 1 / 8 := by
    rw [hz₀def, spikeC]
    convert hk using 2
    ring
  have hz₀re : z₀.re = 0 := by
    rw [hz₀def, UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, inv_neg, Complex.neg_re,
      Complex.inv_re]
    have hcast : ((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ) = (t : ℂ) * Complex.I := rfl
    rw [hcast]
    have : ((t : ℂ) * Complex.I).re = 0 := by simp
    rw [this, zero_div, neg_zero]
  have hkidx : k = 0 ∨ k = 1 ∨ k = -1 := by
    refine spike_int_index hw z₀ hz₀re k ?_
    rw [spikeC] at hkball
    convert hkball using 2
    ring
  have hsc1 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
  have hsc0 : (0 : ℝ) ≤ Work.Kernels.scale w := le_trans zero_le_one hsc1
  have hCt : (0 : ℝ) ≤ Ch * (Work.Kernels.scale w) ^ Nh :=
    mul_nonneg hCh (Real.rpow_nonneg hsc0 _)
  have hcim : (2 : ℝ) ≤ (spikeC w k).im := by
    have h1 : ((k : ℂ)).im = 0 := by simp
    rw [spikeC, Complex.add_im, h1, add_zero, UpperHalfPlane.coe_im]
    exact hw.2
  have hScoe : (((ModularGroup.S • w : UpperHalfPlane)) : ℂ) = -((w : ℂ))⁻¹ := by
    rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, inv_neg]
  -- ### the punctured-disc bound and its holomorphy
  obtain ⟨δ, B, hδpos, hδhalf, hB, hbdd⟩ := exists_bound_punctured_ball ℓ d hd w hw n hn k hkidx
  have hz₀ne : z₀ ≠ spikeC w k := by
    intro h
    rcases hkidx with hk0 | hk1 | hkm1
    · subst hk0
      apply hne
      have h1 : z₀ = -(((Work.Kernels.imagAxis t ht : UpperHalfPlane)) : ℂ)⁻¹ := by
        rw [hz₀def, UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, inv_neg]
      have h2 : spikeC w 0 = -((w : ℂ))⁻¹ := by rw [spikeC, Int.cast_zero, add_zero, hScoe]
      rw [h1, h2] at h
      have h3 : ((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ) = (w : ℂ) :=
        inv_injective (neg_injective h)
      rwa [show ((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ)
        = (t : ℂ) * Complex.I from rfl] at h3
    · have hre : (spikeC w 1).re = (ModularGroup.S • w).re + 1 := by
        rw [spikeC, Complex.add_re, UpperHalfPlane.coe_re]
        have hz : ((((1 : ℤ)) : ℂ)).re = 1 := by norm_num
        rw [hz]
      have hzr : z₀.re = (spikeC w 1).re := by rw [h, hk1]
      rw [hz₀re, hre] at hzr
      have := abs_re_S_smul_lt_one hw
      rw [abs_lt] at this
      linarith [this.1]
    · have hre : (spikeC w (-1)).re = (ModularGroup.S • w).re - 1 := by
        rw [spikeC, Complex.add_re, UpperHalfPlane.coe_re]
        have hz : ((((-1 : ℤ)) : ℂ)).re = -1 := by norm_num
        rw [hz]; ring
      have hzr : z₀.re = (spikeC w (-1)).re := by rw [h, hkm1]
      rw [hz₀re, hre] at hzr
      have := abs_re_S_smul_lt_one hw
      rw [abs_lt] at this
      linarith [this.2]
  -- the pole of the rational correction is avoided on the ball of radius `1/2` around `c`
  have hwz_of_dist : ∀ z : ℂ, ‖z - spikeC w k‖ = 1 / 2 → 1 + (w : ℂ) * z ≠ 0 := by
    intro z hz h0
    have h1 : z = -((w : ℂ))⁻¹ := one_add_mul_eq_zero h0
    rcases hkidx with hk0 | hk1 | hkm1
    · subst hk0
      rw [h1, spikeC, Int.cast_zero, add_zero, hScoe] at hz
      simp only [sub_self, norm_zero] at hz
      norm_num at hz
    · subst hk1
      have h2 : spikeC w 1 = -((w : ℂ))⁻¹ + (1 : ℂ) := by rw [spikeC, hScoe, Int.cast_one]
      rw [h1, h2] at hz
      rw [norm_neg_inv_sub_add_one] at hz
      norm_num at hz
    · subst hkm1
      have h2 : spikeC w (-1) = -((w : ℂ))⁻¹ + (-1 : ℂ) := by
        rw [spikeC, hScoe]; push_cast; ring
      rw [h1, h2] at hz
      rw [norm_neg_inv_sub_add_neg_one] at hz
      norm_num at hz
  have hFdiffBig : DifferentiableOn ℂ (spikeF ℓ d w n)
      (Metric.ball (spikeC w k) (3 / 4) \ {spikeC w k}) := by
    intro z hz
    simp only [Set.mem_sdiff, Set.mem_singleton_iff] at hz
    obtain ⟨hzball, hzne⟩ := hz
    rw [Metric.mem_ball, dist_eq_norm] at hzball
    have hzim : 0 < z.im := by
      have h2 := Complex.abs_im_le_norm (z - spikeC w k)
      rw [Complex.sub_im] at h2
      have h3 : -(‖z - spikeC w k‖) ≤ z.im - (spikeC w k).im := (abs_le.mp h2).1
      linarith
    have hjc : Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex (-(z)⁻¹))
        ≠ Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w) := by
      intro hcon
      exact hzne (eq_spikeC_of_jInvariantFun_eq hw n hn k hzim
        (lt_trans hzball (by norm_num)) hcon)
    have hζcoe : ((UpperHalfPlane.ofComplex (-(z)⁻¹) : UpperHalfPlane) : ℂ) = -(z)⁻¹ :=
      coe_ofComplex_of_pos (neg_inv_im_pos hzim)
    have hmd : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
        (fun ζ : UpperHalfPlane => Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) ζ)
        (UpperHalfPlane.ofComplex (-(z)⁻¹)) :=
      Work.Residues.mdifferentiableAt_Kfun_snd ℓ d hd ((n : ℝ) +ᵥ w) _ hjc
    have hK : DifferentiableAt ℂ
        ((fun ζ : UpperHalfPlane => Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) ζ)
          ∘ (↑UpperHalfPlane.ofComplex)) (-(z)⁻¹) := by
      have h' := (UpperHalfPlane.mdifferentiableAt_iff).mp hmd
      simpa only [hζcoe] using h'
    have hz0 : z ≠ 0 := by
      intro hh; rw [hh] at hzim; simp at hzim
    have hcomp : DifferentiableAt ℂ
        ((fun u : ℂ => Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (UpperHalfPlane.ofComplex u))
          ∘ (fun z : ℂ => -(z)⁻¹)) z :=
      hK.comp z ((differentiableAt_id.neg).comp z (differentiableAt_inv hz0))
    have hwz : 1 + (w : ℂ) * z ≠ 0 := by
      intro h0
      have h1 : z = -((w : ℂ))⁻¹ := one_add_mul_eq_zero h0
      rcases hkidx with hk0 | hk1 | hkm1
      · subst hk0
        refine hzne ?_
        rw [h1, spikeC, Int.cast_zero, add_zero, hScoe]
      · exfalso
        subst hk1
        have h2 : spikeC w 1 = -((w : ℂ))⁻¹ + (1 : ℂ) := by rw [spikeC, hScoe, Int.cast_one]
        rw [h1, h2] at hzball
        rw [norm_neg_inv_sub_add_one] at hzball
        norm_num at hzball
      · exfalso
        subst hkm1
        have h2 : spikeC w (-1) = -((w : ℂ))⁻¹ + (-1 : ℂ) := by
          rw [spikeC, hScoe]; push_cast; ring
        rw [h1, h2] at hzball
        rw [norm_neg_inv_sub_add_neg_one] at hzball
        norm_num at hzball
    have hpp : DifferentiableAt ℂ
        (fun z : ℂ => ((n : ℂ) / (2 * (Real.pi : ℂ))) * (z * (1 + (w : ℂ) * z)⁻¹)) z := by
      have hd1 : DifferentiableAt ℂ (fun z : ℂ => 1 + (w : ℂ) * z) z :=
        (differentiableAt_const (1 : ℂ)).add ((differentiableAt_const (w : ℂ)).mul differentiableAt_id)
      exact (differentiableAt_const _).mul (differentiableAt_id.mul (hd1.inv hwz))
    show DifferentiableWithinAt ℂ (fun z : ℂ =>
        Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (UpperHalfPlane.ofComplex (-(z)⁻¹))
          + ((n : ℂ) / (2 * (Real.pi : ℂ))) * (z * (1 + (w : ℂ) * z)⁻¹)) _ z
    exact (hcomp.add hpp).differentiableWithinAt
  -- ### the off-spike bound on the outer sphere
  have houter : ∀ z : ℂ, ‖z - spikeC w k‖ = 1 / 2 →
      ‖spikeF ℓ d w n z‖ ≤ Ch * (Work.Kernels.scale w) ^ Nh := by
    intro z hz
    have hzim : 0 < z.im := by
      have h2 := Complex.abs_im_le_norm (z - spikeC w k)
      rw [Complex.sub_im] at h2
      have h3 : -(‖z - spikeC w k‖) ≤ z.im - (spikeC w k).im := (abs_le.mp h2).1
      rw [hz] at h3
      linarith
    set ζ : UpperHalfPlane := UpperHalfPlane.ofComplex (-(z)⁻¹) with hζdef
    have hζcoe : (ζ : ℂ) = -(z)⁻¹ := coe_ofComplex_of_pos (neg_inv_im_pos hzim)
    have hSζ : (((ModularGroup.S • ζ : UpperHalfPlane)) : ℂ) = z := by
      rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, hζcoe]
      simp only [inv_neg, inv_inv, neg_neg]
    have him : 1 ≤ ((ModularGroup.S • ζ : UpperHalfPlane)).im := by
      rw [← UpperHalfPlane.coe_im, hSζ]
      have h2 := Complex.abs_im_le_norm (z - spikeC w k)
      rw [Complex.sub_im] at h2
      have h3 : -(‖z - spikeC w k‖) ≤ z.im - (spikeC w k).im := (abs_le.mp h2).1
      rw [hz] at h3
      linarith
    have hsep : ∀ k' : ℤ, (1 / 8 : ℝ) ≤
        ‖((ModularGroup.S • ζ : UpperHalfPlane) : ℂ)
          - ((ModularGroup.S • w : UpperHalfPlane) : ℂ) - ((k' : ℤ) : ℂ)‖ := by
      intro k'
      rw [hSζ]
      have h1 : ‖z - ((ModularGroup.S • w : UpperHalfPlane) : ℂ) - (k : ℂ)‖ = 1 / 2 := by
        have hsub : z - spikeC w k = z - ((ModularGroup.S • w : UpperHalfPlane) : ℂ) - (k : ℂ) := by
          rw [spikeC]; ring
        rw [← hsub]; exact hz
      by_cases hkk : k' = k
      · subst hkk
        rw [h1]; norm_num
      · have hne0 : k - k' ≠ 0 := by
          intro h0
          exact hkk (by omega)
        have h7 : (1 : ℝ) ≤ ‖((k : ℂ) - ((k' : ℤ) : ℂ))‖ := by
          rw [← Int.cast_sub, Complex.norm_intCast]
          exact_mod_cast Int.one_le_abs hne0
        have h8 : ‖z - ((ModularGroup.S • w : UpperHalfPlane) : ℂ) - ((k' : ℤ) : ℂ)‖
            ≥ ‖((k : ℂ) - ((k' : ℤ) : ℂ))‖
              - ‖z - ((ModularGroup.S • w : UpperHalfPlane) : ℂ) - (k : ℂ)‖ := by
          have h9 := norm_sub_le
            (z - ((ModularGroup.S • w : UpperHalfPlane) : ℂ) - ((k' : ℤ) : ℂ))
            (z - ((ModularGroup.S • w : UpperHalfPlane) : ℂ) - (k : ℂ))
          have he : (z - ((ModularGroup.S • w : UpperHalfPlane) : ℂ) - ((k' : ℤ) : ℂ))
              - (z - ((ModularGroup.S • w : UpperHalfPlane) : ℂ) - (k : ℂ))
              = ((k : ℂ) - ((k' : ℤ) : ℂ)) := by ring
          rw [he] at h9
          linarith
        linarith
    have hb := hoff w hw n hn ζ him hsep
    have hwz : 1 + (w : ℂ) * z ≠ 0 := hwz_of_dist z hz
    have hkey : (((ζ : ℂ) - (w : ℂ))⁻¹) = -(z * (1 + (w : ℂ) * z)⁻¹) := by
      have hz0 : z ≠ 0 := by
        intro hh; rw [hh] at hzim; simp at hzim
      rw [hζcoe]
      exact inv_sub_eq_neg z (w : ℂ) hz0 hwz
    rw [spikeF_apply]
    have hkey2 : Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) ζ
          - ((n : ℂ) / (2 * (Real.pi : ℂ))) * (((ζ : ℂ) - (w : ℂ))⁻¹)
        = Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (UpperHalfPlane.ofComplex (-(z)⁻¹))
          + ((n : ℂ) / (2 * (Real.pi : ℂ))) * (z * (1 + (w : ℂ) * z)⁻¹) := by
      rw [hζdef]
      rw [hkey]
      ring
    rw [← hkey2]
    exact hb
  -- ### the maximum modulus argument
  set δh : ℝ := δ / 2 with hδhdef
  have hδhpos : 0 < δh := by rw [hδhdef]; linarith
  have hδhne : δh ≠ 0 := ne_of_gt hδhpos
  have hδhlt : δh < δ := by rw [hδhdef]; linarith
  have hann : ∀ z ∈ Metric.ball (spikeC w k) (1 / 2) \ Metric.closedBall (spikeC w k) δh,
      ‖spikeF ℓ d w n z‖ ≤ max (Ch * (Work.Kernels.scale w) ^ Nh) B := by
    intro z hz
    simp only [Set.mem_sdiff] at hz
    obtain ⟨hzball, hznot⟩ := hz
    refine Complex.norm_le_of_forall_mem_frontier_norm_le
      (Metric.isBounded_ball.subset Set.sdiff_subset) ?_ ?_ (subset_closure ⟨hzball, hznot⟩)
    · refine DifferentiableOn.diffContOnCl (hFdiffBig.mono ?_)
      intro y hy
      have h1 : y ∈ Metric.closedBall (spikeC w k) (1 / 2) :=
        Metric.closure_ball_subset_closedBall (closure_mono Set.sdiff_subset hy)
      have h2 : y ∉ Metric.ball (spikeC w k) δh := by
        intro hy'
        have hyint : y ∈ interior (Metric.closedBall (spikeC w k) δh) :=
          Metric.ball_subset_interior_closedBall hy'
        obtain ⟨x, hxint', hxann⟩ := mem_closure_iff.mp hy
          (interior (Metric.closedBall (spikeC w k) δh)) isOpen_interior hyint
        exact hxann.2 (interior_subset hxint')
      have hyc : y ≠ spikeC w k := by
        intro hc
        exact h2 (hc ▸ Metric.mem_ball_self hδhpos)
      refine ⟨?_, hyc⟩
      rw [Metric.mem_ball, dist_eq_norm]
      have h4 := Metric.mem_closedBall.mp h1
      rw [dist_eq_norm] at h4
      linarith
    · intro y hy
      rcases PGWide.frontier_sdiff_closedBall_subset hδhne hy with hout | hin
      · refine le_trans (houter y ?_) (le_max_left _ _)
        have h1 := Metric.frontier_ball_subset_sphere hout
        rwa [Metric.mem_sphere, dist_eq_norm] at h1
      · have h1 : ‖y - spikeC w k‖ = δh := by
          rwa [Metric.mem_sphere, dist_eq_norm] at hin
        have hne : y ≠ spikeC w k := by
          intro hc; rw [hc] at h1
          simp only [sub_self, norm_zero] at h1
          linarith
        exact le_trans (hbdd y (by rw [h1]; exact hδhlt) hne) (le_max_right _ _)
  -- ### boundedness on the punctured disc
  have hBdd : BddAbove (norm ∘ spikeF ℓ d w n ''
      (Metric.ball (spikeC w k) (1 / 2) \ {spikeC w k})) := by
    refine ⟨max (Ch * (Work.Kernels.scale w) ^ Nh) B, ?_⟩
    rintro y ⟨z, hz, rfl⟩
    simp only [Set.mem_sdiff, Set.mem_singleton_iff] at hz
    obtain ⟨hzball, hzne⟩ := hz
    by_cases hcase : z ∈ Metric.closedBall (spikeC w k) δh
    · have hzlt : ‖z - spikeC w k‖ < δ := by
        have h1 := Metric.mem_closedBall.mp hcase
        rw [dist_eq_norm] at h1
        linarith
      exact le_trans (hbdd z hzlt hzne) (le_max_right _ _)
    · exact hann z ⟨hzball, hcase⟩
  -- ### the maximal function and the maximum modulus principle
  set G : ℂ → ℂ := Function.update (spikeF ℓ d w n) (spikeC w k)
    ((𝓝[≠] (spikeC w k)).limUnder (spikeF ℓ d w n)) with hGdef
  have hGdiff : DifferentiableOn ℂ G (Metric.ball (spikeC w k) (1 / 2)) := by
    rw [hGdef]
    refine Complex.differentiableOn_update_limUnder_of_bddAbove
      (Metric.ball_mem_nhds _ (by norm_num)) (hFdiffBig.mono ?_) hBdd
    intro z hz
    simp only [Set.mem_sdiff] at hz ⊢
    exact ⟨Metric.ball_subset_ball (by norm_num) hz.1, hz.2⟩
  have hGcont : ContinuousOn G (closure (Metric.ball (spikeC w k) (1 / 2))) := by
    refine ContinuousOn.mono ?_ Metric.closure_ball_subset_closedBall
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    by_cases hzc : z = spikeC w k
    · subst hzc
      rw [hGdef]
      exact (hGdiff.differentiableAt
        (Metric.ball_mem_nhds _ (by norm_num))).continuousAt.continuousWithinAt
    · have hev : G =ᶠ[𝓝 z] spikeF ℓ d w n := by
        filter_upwards [isOpen_ne.mem_nhds hzc] with y hy
        rw [hGdef]
        exact Function.update_of_ne hy _ _
      have hy3 : z ∈ Metric.ball (spikeC w k) (3 / 4) \ {spikeC w k} := by
        refine ⟨?_, hzc⟩
        rw [Metric.mem_ball, dist_eq_norm]; linarith
      have hmem : Metric.ball (spikeC w k) (3 / 4) \ {spikeC w k} ∈ 𝓝 z :=
        Metric.isOpen_ball.sdiff isClosed_singleton |>.mem_nhds hy3
      have hFd : DifferentiableAt ℂ (spikeF ℓ d w n) z :=
        (hFdiffBig z hy3).differentiableAt hmem
      exact (hFd.continuousAt.congr_of_eventuallyEq hev).continuousWithinAt
  have hGfront : ∀ z ∈ frontier (Metric.ball (spikeC w k) (1 / 2)),
      ‖G z‖ ≤ Ch * (Work.Kernels.scale w) ^ Nh := by
    intro z hz
    have hzsphere : ‖z - spikeC w k‖ = 1 / 2 := by
      have h1 := Metric.frontier_ball_subset_sphere hz
      rwa [Metric.mem_sphere, dist_eq_norm] at h1
    have hzne : z ≠ spikeC w k := by
      intro hc; rw [hc] at hzsphere
      simp only [sub_self, norm_zero] at hzsphere
      norm_num at hzsphere
    rw [hGdef, Function.update_of_ne hzne]
    exact houter z hzsphere
  have hz₀clos : z₀ ∈ closure (Metric.ball (spikeC w k) (1 / 2)) :=
    subset_closure (by rw [Metric.mem_ball, dist_eq_norm]; linarith [hkball])
  have hfinal : ‖G z₀‖ ≤ Ch * (Work.Kernels.scale w) ^ Nh :=
    Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball
      ⟨hGdiff, hGcont⟩ hGfront hz₀clos
  have hGz₀ : G z₀ = spikeF ℓ d w n z₀ := by
    rw [hGdef, Function.update_of_ne hz₀ne]
  rw [hGz₀] at hfinal
  -- ### identification with the target
  have hz₀im : 0 < z₀.im := by
    rw [hz₀def, UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk]
    rw [show ((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ) = (t : ℂ) * Complex.I from rfl]
    simp [ht]
  have hz₀coec : z₀ = -(((Work.Kernels.imagAxis t ht : UpperHalfPlane)) : ℂ)⁻¹ := by
    rw [hz₀def, UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, inv_neg]
  have hζ₀ : ((UpperHalfPlane.ofComplex (-(z₀)⁻¹) : UpperHalfPlane)) = Work.Kernels.imagAxis t ht := by
    refine UpperHalfPlane.ext ?_
    rw [coe_ofComplex_of_pos (neg_inv_im_pos hz₀im)]
    have hc1 : (z₀)⁻¹ = -(((Work.Kernels.imagAxis t ht : UpperHalfPlane)) : ℂ) := by
      rw [hz₀coec, inv_neg, inv_inv]
    rw [hc1]
    simp
  have hz₀w : 1 + (w : ℂ) * z₀ ≠ 0 := by
    intro h0
    have h1 : z₀ = -((w : ℂ))⁻¹ := one_add_mul_eq_zero h0
    rcases hkidx with hk0 | hk1 | hkm1
    · subst hk0
      exact hz₀ne (by rw [h1, spikeC, Int.cast_zero, add_zero, hScoe])
    · subst hk1
      have h2 : spikeC w 1 = -((w : ℂ))⁻¹ + (1 : ℂ) := by rw [spikeC, hScoe, Int.cast_one]
      rw [h1, h2] at hkball
      rw [norm_neg_inv_sub_add_one] at hkball
      norm_num at hkball
    · subst hkm1
      have h2 : spikeC w (-1) = -((w : ℂ))⁻¹ + (-1 : ℂ) := by
        rw [spikeC, hScoe]; push_cast; ring
      rw [h1, h2] at hkball
      rw [norm_neg_inv_sub_add_neg_one] at hkball
      norm_num at hkball
  have hz₀0 : z₀ ≠ 0 := by
    intro hh; rw [hh] at hz₀im; simp at hz₀im
  have hkey₀ : z₀ * (1 + (w : ℂ) * z₀)⁻¹
      = -((((Work.Kernels.imagAxis t ht : UpperHalfPlane)) : ℂ) - (w : ℂ))⁻¹ := by
    have ha' : ((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ) = -(z₀)⁻¹ := by
      rw [hz₀coec, inv_neg, inv_inv, neg_neg]
    have h := inv_sub_eq_neg z₀ (w : ℂ) hz₀0 hz₀w
    rw [← ha'] at h
    rw [h, neg_neg]
  rw [spikeF_apply, hζ₀, hkey₀] at hfinal
  have hKax : Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
      = Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht) := by
    rw [Work.Kernels.Kaxis, dif_pos ht]
  rw [hKax]
  have hgoal : ‖Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)
        - ((n : ℂ) / (2 * (Real.pi : ℂ))) * (((t : ℂ) * Complex.I - (w : ℂ))⁻¹)‖
      = ‖Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)
        + ((n : ℂ) / (2 * (Real.pi : ℂ)))
          * (-((((Work.Kernels.imagAxis t ht : UpperHalfPlane)) : ℂ) - (w : ℂ))⁻¹)‖ := by
    have harg : Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)
          - ((n : ℂ) / (2 * (Real.pi : ℂ))) * (((t : ℂ) * Complex.I - (w : ℂ))⁻¹)
        = Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)
          + ((n : ℂ) / (2 * (Real.pi : ℂ)))
            * (-((((Work.Kernels.imagAxis t ht : UpperHalfPlane)) : ℂ) - (w : ℂ))⁻¹) := by
      rw [show ((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ) = (t : ℂ) * Complex.I from rfl]
      ring
    rw [harg]
  rw [hgoal]
  exact hfinal
