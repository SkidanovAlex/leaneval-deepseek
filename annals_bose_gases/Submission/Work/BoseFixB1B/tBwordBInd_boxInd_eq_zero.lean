import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1B.sectorCountBoxAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.tBwordBInd_boxInd_eq_zero` — the box word vanishes at the sharp box state

`Work.UBBInputs8.tBwordBInd` is the FS-faithful small-box kinetic word

`𝒯_{B(u)} = ½ε_T(1+π⁻²)⁻¹(dℓ)⁻² n₊(B(u)) + Q_{B(u)}χ_{B(u)}[√−Δ−(dℓ)⁻¹]₊²χ_{B(u)}Q_{B(u)}`

built from FS's *box* projection `Q_B = 1_B − P_B` (`Work.UBBInputs8.boxQInd`, with the box
indicator in **both** terms, unlike the older corpus `Work.SmallBoxTBWord.boxQ`).
`A.tBwordBInd_const_zero` proves that this word vanishes at the constant state — the
mathematical statement that the repaired residual is the inequality FS meant.

This module proves the same vanishing at the **sharp box state**
`Ψ_B = 1_{B(u)^k}·1` (`= Work.BoseFixB1B.sharpBoxState B (const 1)`, the state appearing in the
fibre decomposition `sharpBoxState (dlBox L d u) ψ`): for the sliding box `B(u) = dlBox L d u`
and *every* `k, L > 0, d > 0, u, ε, c`,

`tBwordBInd k L d ε c u (1_{B(u)^k}) = 0`.

The two terms are treated separately, by measure rather than pointwise identity (the box
`dlBox L d u` may be a degenerate face, of zero volume, in which case `1/|B(u)| = 0` and the
`Q_B`-projection is *not* zero):

* off the set `slotBox B(u) = B(u)^k` the projection `Q_{B(u),i}Ψ_B` vanishes **pointwise**
  (`boxQInd_slotBox_indicator_eq_zero_of_notMem`): either `x i ∉ B(u)`, and the box indicators
  in both terms of `Q_B` kill them, or `x i ∈ B(u)` while some `x j ∉ B(u)` (`j ≠ i`), and then
  both `Ψ_B x` and the whole slot-`i` fibre integral `∫_{B(u)} Ψ_B(x_{i←z})dz` vanish.
* if `|B(u)| ≠ 0` this upgrades to `Q_{B(u),i}Ψ_B = 0` **everywhere**
  (`boxQInd_slotBox_indicator_eq_zero`): on `B(u)^k` the fibre integral is `∫_{B(u)}1_{B(u)}
  = |B(u)|`, so `Q_B x = 1 − |B(u)|⁻¹·|B(u)| = 0`.  Both halves of `𝒯_B` are sums/integrals of
  squares of `Q_B`, so both vanish.
* if `|B(u)| = 0` the window vanishes, `χ_{B(u)} = 0` (`A.chiB_eq_zero_of_volume_dlBox_eq_zero`),
  and the gap half is an integral of a function supported in the **null** set `B(u)^k`
  (`volume_slotBox_eq_zero`), hence zero.
-/

namespace Work.BoseFixB1B

open MeasureTheory

local notation "𝔼" => EuclideanSpace ℝ (Fin 3)

/-! ## 1  Pointwise vanishing of the box projection off the sharp support -/

/-- Off the sharp support `B^N = slotBox B` the box projection `Q_{B,i}` annihilates the sharp
state `1_{B^N}`: if `x i ∉ B` both terms of `Q_B` carry the indicator `1_B(x i)`, and if
`x i ∈ B` but some other coordinate lies outside `B`, then the state and its whole slot-`i`
fibre integral vanish at `x`. -/
theorem boxQInd_slotBox_indicator_eq_zero_of_notMem {volA : ℝ}
    {B : Set 𝔼} {N : ℕ} {i : Fin N} (x : Submission.BoseGases.X N)
    (hx : x ∉ Work.PerSector.slotBox (ι := Fin N) B) :
    Work.UBBInputs8.boxQInd volA B i
      ((Work.PerSector.slotBox (ι := Fin N) B).indicator (fun _ => (1 : ℝ))) x = 0 := by
  rw [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd]
  by_cases hxi : x i ∈ B
  · rw [Set.indicator_of_mem hxi, Set.indicator_of_notMem hx]
    have hf : (fun z : 𝔼 => (Work.PerSector.slotBox (ι := Fin N) B).indicator
        (fun _ => (1 : ℝ)) (Function.update x i z)) = fun _ => (0 : ℝ) := by
      funext z
      by_cases hmem : Function.update x i z ∈ Work.PerSector.slotBox (ι := Fin N) B
      · exfalso
        apply hx
        rw [Work.PerSector.mem_slotBox_iff] at hmem ⊢
        intro j
        by_cases hj : j = i
        · subst hj; simpa using hxi
        · have h := hmem j
          rwa [Function.update_of_ne hj] at h
      · rw [Set.indicator_of_notMem hmem]
    rw [hf]
    simp
  · rw [Set.indicator_of_notMem hxi]
    ring

/-! ## 2  Vanishing of the box projection on the sharp state, positive-volume box -/

/-- For a positive-volume box `B`, the projection `Q_{B,i}` annihilates the sharp state
`1_{B^N}` **everywhere**: on `B^N` the slot-`i` fibre integral of the state is `∫_B 1_B = |B|`,
so `Q_B x = 1 − |B|⁻¹|B| = 0`. -/
theorem boxQInd_slotBox_indicator_eq_zero {volA : ℝ} {B : Set 𝔼} (hB : MeasurableSet B)
    (hvol : (volume : Measure 𝔼).real B = volA) (hne : volA ≠ 0) {N : ℕ} (i : Fin N) :
    Work.UBBInputs8.boxQInd volA B i
      ((Work.PerSector.slotBox (ι := Fin N) B).indicator (fun _ => (1 : ℝ))) = 0 := by
  funext x
  by_cases hx : x ∈ Work.PerSector.slotBox (ι := Fin N) B
  · rw [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd]
    have hxi : x i ∈ B := by
      have h := hx; rw [Work.PerSector.mem_slotBox_iff] at h; exact h i
    rw [Set.indicator_of_mem hxi, Set.indicator_of_mem hx]
    have hf : (fun z : 𝔼 => (Work.PerSector.slotBox (ι := Fin N) B).indicator
        (fun _ => (1 : ℝ)) (Function.update x i z)) = B.indicator (fun _ => (1 : ℝ)) := by
      funext z
      by_cases hz : z ∈ B
      · rw [Set.indicator_of_mem hz]
        apply Set.indicator_of_mem
        rw [Work.PerSector.mem_slotBox_iff] at hx ⊢
        intro j
        by_cases hj : j = i
        · subst hj; simpa [Function.update_apply] using hz
        · rw [Function.update_of_ne hj]; exact hx j
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem]
        intro hmem
        apply hz
        have h := hmem
        rw [Work.PerSector.mem_slotBox_iff] at h
        simpa [Function.update_apply] using h i
    rw [hf]
    have hint : (∫ z in B, B.indicator (fun _ => (1 : ℝ)) z) = volA := by
      rw [MeasureTheory.setIntegral_congr_fun hB (fun z hz => Set.indicator_of_mem hz _),
        MeasureTheory.setIntegral_const, hvol]
      simp
    rw [hint, div_mul_cancel₀ 1 hne]
    simp
  · rw [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd]
    by_cases hxi : x i ∈ B
    · rw [Set.indicator_of_mem hxi, Set.indicator_of_notMem hx]
      have hf : (fun z : 𝔼 => (Work.PerSector.slotBox (ι := Fin N) B).indicator
          (fun _ => (1 : ℝ)) (Function.update x i z)) = fun _ => (0 : ℝ) := by
        funext z
        by_cases hmem : Function.update x i z ∈ Work.PerSector.slotBox (ι := Fin N) B
        · exfalso
          apply hx
          rw [Work.PerSector.mem_slotBox_iff] at hmem ⊢
          intro j
          by_cases hj : j = i
          · subst hj; simpa using hxi
          · have h := hmem j
            rwa [Function.update_of_ne hj] at h
        · rw [Set.indicator_of_notMem hmem]
      rw [hf]
      simp
    · rw [Set.indicator_of_notMem hxi]
      simp

/-! ## 3  The sharp support of a null box is null -/

/-- A null box `B ⊆ ℝ³` has null sharp support `B^N = slotBox B` in the product space: the
Pi-measure of the product `∏_i B` is the finite product of the factors `|B| = 0`. -/
theorem volume_slotBox_eq_zero {B : Set 𝔼} (hvol : (volume : Measure 𝔼) B = 0)
    {N : ℕ} (i : Fin N) :
    (volume : Measure (Submission.BoseGases.X N))
      (Work.PerSector.slotBox (ι := Fin N) B) = 0 := by
  have h : Work.PerSector.slotBox (ι := Fin N) B = Set.univ.pi (fun _ : Fin N => B) := by
    ext x; rw [Work.PerSector.mem_slotBox_iff, Set.mem_univ_pi]
  rw [h, MeasureTheory.volume_pi, MeasureTheory.Measure.pi_pi]
  exact Finset.prod_eq_zero (Finset.mem_univ i) hvol

/-! ## 4  The target -/

theorem tBwordBInd_boxInd_eq_zero {L d ε c : ℝ} (hL : 0 < L) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) (k : ℕ) :
    Work.UBBInputs8.tBwordBInd k L d ε c u
      (Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox L d u)
        (fun _ : Submission.BoseGases.X k => (1 : ℝ))) = 0 := by
  classical
  simp only [Work.UBBInputs8.tBwordBInd, Work.UBBInputs8.tBwordInd,
    Work.UBBInputs8.tBwordKinInd, Work.BoseFixB1B.sharpBoxState]
  set B : Set 𝔼 := Submission.BoseGases.dlBox L d u with hBdef
  have hBmeas : MeasurableSet B := by
    rw [hBdef]; exact Work.SmallBoxSliding.measurableSet_dlBox L d u
  have hBfin : (volume : Measure 𝔼) B < ⊤ := by
    rw [hBdef]; exact Work.SmallBoxSliding.volume_dlBox_lt_top hL d u
  set Ψ : Submission.BoseGases.X k → ℝ :=
    (Work.PerSector.slotBox (ι := Fin k) B).indicator (fun _ => (1 : ℝ)) with hΨdef
  by_cases hvolB : Work.SmallBoxSliding.boxMass L d u = 0
  · -- degenerate box: the window vanishes; the gap term sees only the null sharp support.
    have hvol0 : (volume : Measure 𝔼) B = 0 := by
      have hreal : (volume : Measure 𝔼).real B = 0 := by
        rw [hBdef, ← Work.SmallBoxSliding.boxMass_eq_measureReal L d u, hvolB]
      rw [Measure.real] at hreal
      rcases (ENNReal.toReal_eq_zero_iff _).mp hreal with h0 | htop
      · exact h0
      · exact absurd htop (ne_of_lt hBfin)
    have hχ0 : Submission.BoseGases.chiB L d u = 0 :=
      Work.UBBInputs8.A.chiB_eq_zero_of_volume_dlBox_eq_zero hL hd u
        (by rw [← hBdef]; exact hvol0)
    have hkin : Work.UBBInputs8.tBdiagFormInd L B (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.chiB L d u) (Submission.BoseGases.fsKinCoeff c) Ψ = 0 := by
      rw [hχ0]
      exact Work.UBBInputs8.A.TBAux.tBdiagFormInd_eq_zero_of_chi_zero _ _
    have hcn : Work.UBBInputs8.cnPlusBoxInd L B (Work.SmallBoxSliding.boxMass L d u)
        Ψ = 0 := by
      by_cases hk : k = 0
      · subst hk
        simp [Work.UBBInputs8.cnPlusBoxInd]
      · have hnull : (volume : Measure (Submission.BoseGases.X k))
            (Work.PerSector.slotBox (ι := Fin k) B) = 0 :=
          volume_slotBox_eq_zero hvol0 ⟨0, Nat.pos_of_ne_zero hk⟩
        simp only [Work.UBBInputs8.cnPlusBoxInd]
        refine Finset.sum_eq_zero (fun i _ => ?_)
        refine MeasureTheory.setIntegral_eq_zero_of_ae_eq_zero (μ := volume) ?_
        rw [MeasureTheory.ae_iff]
        refine MeasureTheory.measure_mono_null ?_ hnull
        intro x hx
        by_contra hxS
        refine hx (fun _ => ?_)
        rw [hΨdef, boxQInd_slotBox_indicator_eq_zero_of_notMem x hxS]
        simp
    rw [hcn, hkin]
    ring
  · -- positive-volume box: the projection vanishes identically.
    have hvolA : (volume : Measure 𝔼).real B = Work.SmallBoxSliding.boxMass L d u := by
      rw [hBdef]; exact (Work.SmallBoxSliding.boxMass_eq_measureReal L d u).symm
    have hQ : ∀ i : Fin k, Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u) B i Ψ = 0 :=
      fun i => by
        rw [hΨdef]
        exact boxQInd_slotBox_indicator_eq_zero hBmeas hvolA hvolB i
    rw [Work.UBBInputs8.A.TBAux.cnPlusBoxInd_eq_zero_of_boxQ_eq_zero hQ,
      Work.UBBInputs8.A.TBAux.tBdiagFormInd_eq_zero_of_boxQ_eq_zero
        (Submission.BoseGases.chiB L d u) (Submission.BoseGases.fsKinCoeff c) hQ]
    ring

end Work.BoseFixB1B
