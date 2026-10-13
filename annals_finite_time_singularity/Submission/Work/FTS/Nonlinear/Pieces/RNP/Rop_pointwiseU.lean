import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row10aux.Rstar_WlInf
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row10aux.Rop_PhiTs_smoothQuad

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Rop_pointwiseU`: the pointwise bounds for `ℛ(Φ̃_*)` with a **constant uniform in `α`, `Cs`,
`Φs`**

`Work.FTS.Nonlinear.Pieces.RNP.Rop_pointwise` establishes the four pointwise bounds for
`ℛ(Φ̃_*) = Rop α (PhiTs α Φs)` with a constant `C` that is allowed to depend on `α`, `Cs`, `Φs`.
Its proof, however, only ever uses

* the `𝒲^{4,∞}`-bound `WlInf α 4 ((z+1)/z·ℛ(Φ̃_*)) ≤ Cs·α` of `StarPkg`, and
* the truncated bound `WlInf α 4 (χ_{Iθ}·ℛ(Φ̃_*)) ≤ K·(max Cs 0·α)` of
  `row10aux.Rstar_WlInf`, whose constant `K` is *universal*,

so the same constant `2K+1` works for every admissible `(α, Cs, Φs)`.  This file makes that
explicit: `Rop_uK` is the universal constant extracted from `Rstar_WlInf` (via
`Classical.choose`, so that it is a genuine global constant rather than a bound variable), and
the proof of `Rop_pointwise` goes through verbatim with `C = 2·Rop_uK + 1`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP

set_option autoImplicit false

/-- The universal constant supplied by `row10aux.Rstar_WlInf`, made into a global constant. -/
noncomputable def Rop_uK : ℝ :=
  Classical.choose Work.FTS.Nonlinear.Pieces.RNP.row10aux.Rstar_WlInf

theorem Rop_uK_pos : 0 < Rop_uK :=
  (Classical.choose_spec Work.FTS.Nonlinear.Pieces.RNP.row10aux.Rstar_WlInf).1

/-- The specification of `Rop_uK`: the truncated `ℛ(Φ̃_*)` is `𝒲^{4,∞}`-bounded by
`Rop_uK·(max Cs 0·α)`, uniformly in the data. -/
theorem Rop_uK_spec {α Cs : ℝ} {Φs : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hstar : Work.FTS.Nonlin.StarPkg α Cs Φs)
    (hsq : Work.FTS.LocData.SmoothQuad
      (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs))) :
    Work.Spaces.WlInfMem α 4 (fun z θ => if θ ∈ Set.Ioo (0 : ℝ) (π / 2)
        then Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ else 0) ∧
    Work.Spaces.WlInf α 4 (fun z θ => if θ ∈ Set.Ioo (0 : ℝ) (π / 2)
        then Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ else 0)
      ≤ Rop_uK * (max Cs 0 * α) :=
  (Classical.choose_spec Work.FTS.Nonlinear.Pieces.RNP.row10aux.Rstar_WlInf).2
    hα hα1 hstar hsq

theorem Rop_pointwiseU :
    ∃ C : ℝ, 0 < C ∧ ∀ {α Cs : ℝ} {Φs : ℝ → ℝ → ℝ}, 0 < α → α ≤ 1 →
      Work.FTS.Nonlin.StarPkg α Cs Φs →
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
        |Work.Spaces.DthIter a
            (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ|
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
          ≤ C * (max Cs 1 * α) * z / (1 + z)) := by
  -- `Rop_uK` is the universal constant of `Rstar_WlInf`; the proof below is exactly the proof
  -- of `Rop_pointwise` with `K` replaced by `Rop_uK`.
  refine ⟨2 * Rop_uK + 1, by linarith [Rop_uK_pos], ?_⟩
  intro α Cs Φs hα hα1 hstar
  let R : ℝ → ℝ → ℝ := Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)
  let H : ℝ → ℝ → ℝ := fun z θ => (z + 1) / z * R z θ
  -- the same function truncated off the open angular interval: this is what is
  -- compatible with the angular weight `sin(2θ)^{-α/5}/(α + sin(2θ))`
  let Rc : ℝ → ℝ → ℝ := fun z θ => if θ ∈ Set.Ioo (0 : ℝ) (π / 2) then R z θ else 0
  have hHmem : Work.Spaces.WlInfMem α 4 H := hstar.R.1
  have hHle : Work.Spaces.WlInf α 4 H ≤ Cs * α := hstar.R.2
  have hWle : Work.Spaces.WlInf α 4 H ≤ max Cs 1 * α :=
    le_trans hHle (mul_le_mul_of_nonneg_right (le_max_left Cs 1) hα.le)
  have hsq : Work.FTS.LocData.SmoothQuad R :=
    Work.FTS.Nonlinear.Pieces.RNP.row10aux.Rop_PhiTs_smoothQuad hα hα1 hstar.smooth
  have hRc : Work.Spaces.WlInfMem α 4 Rc ∧
      Work.Spaces.WlInf α 4 Rc ≤ Rop_uK * (max Cs 0 * α) := Rop_uK_spec hα hα1 hstar hsq
  have hCM1nn : 0 ≤ max Cs 1 * α := mul_nonneg (by linarith [le_max_right Cs 1]) hα.le
  have hCM0le : max Cs 0 * α ≤ max Cs 1 * α :=
    mul_le_mul_of_nonneg_right
      (max_le (le_max_left Cs 1) (by linarith [le_max_right Cs 1])) hα.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (1) the plain pointwise bound: `ℛ = (z/(1+z))·H` with `H` bounded
    intro z hz θ hθ
    show |R z θ| ≤ (2 * Rop_uK + 1) * (max Cs 1 * α) * z / (1 + z)
    have hzIz : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
    have hθIz : θ ∈ Work.Spaces.Iθ := Set.mem_Icc.mpr ⟨hθ.1.le, hθ.2.le⟩
    have hRH : R z θ = z / (1 + z) * H z θ := by
      show R z θ = z / (1 + z) * ((z + 1) / z * R z θ)
      have hzne : z ≠ 0 := ne_of_gt hz
      have hz1ne : (1 : ℝ) + z ≠ 0 := by positivity
      field_simp
      ring
    have hHpt : |H z θ| ≤ Work.Spaces.WlInf α 4 H := by
      have h := Work.Spaces.WlInf_z_bound α 4 H hHmem 0 (Nat.zero_le 4) z θ hzIz hθIz
      simpa using h
    have haz : 0 ≤ z / (1 + z) := by positivity
    calc |R z θ| = z / (1 + z) * |H z θ| := by rw [hRH, abs_mul, abs_of_nonneg haz]
      _ ≤ z / (1 + z) * (max Cs 1 * α) :=
          mul_le_mul_of_nonneg_left (le_trans hHpt hWle) haz
      _ ≤ (2 * Rop_uK + 1) * (max Cs 1 * α) * z / (1 + z) := by
          have h1 : (1 : ℝ) ≤ 2 * Rop_uK + 1 := by linarith [Rop_uK_pos]
          have hX : 0 ≤ (max Cs 1 * α) * (z / (1 + z)) := mul_nonneg hCM1nn haz
          calc z / (1 + z) * (max Cs 1 * α)
              = 1 * ((max Cs 1 * α) * (z / (1 + z))) := by ring
            _ ≤ (2 * Rop_uK + 1) * ((max Cs 1 * α) * (z / (1 + z))) :=
                mul_le_mul_of_nonneg_right h1 hX
            _ = (2 * Rop_uK + 1) * (max Cs 1 * α) * z / (1 + z) := by ring
  · -- (2) the radial derivatives `∂_z^c ℛ`, `c ≤ 4`
    intro c hc4 z hz θ hθ
    rw [show (1 : ℝ) + z = z + 1 from by ring]
    have hzIz : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
    have hθIz : θ ∈ Work.Spaces.Iθ := Set.mem_Icc.mpr ⟨hθ.1.le, hθ.2.le⟩
    have hz1 : (0 : ℝ) < z + 1 := by linarith
    have hcpos : (0 : ℝ) < (z + 1) ^ c := pow_pos hz1 c
    have hpe : Work.Spaces.pzIter c Rc z θ = Work.Spaces.pzIter c R z θ := by
      rw [Work.Spaces.pzIter_eq_iteratedDeriv, Work.Spaces.pzIter_eq_iteratedDeriv]
      congr 1
      funext z'
      show (if θ ∈ Set.Ioo (0 : ℝ) (π / 2) then R z' θ else 0) = R z' θ
      rw [if_pos hθ]
    rw [← hpe]
    calc |Work.Spaces.pzIter c Rc z θ|
        ≤ Work.Spaces.WlInf α 4 Rc / (z + 1) ^ c :=
          Work.Spaces.pz_sup_bound α 4 Rc hRc.1 c hc4 z θ hzIz hθIz
      _ ≤ (Rop_uK * (max Cs 0 * α)) / (z + 1) ^ c :=
          div_le_div_of_nonneg_right hRc.2 hcpos.le
      _ ≤ (Rop_uK * (max Cs 1 * α)) / (z + 1) ^ c :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hCM0le Rop_uK_pos.le) hcpos.le
      _ ≤ ((2 * Rop_uK + 1) * (max Cs 1 * α)) / (z + 1) ^ c :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by linarith [Rop_uK_pos] :
              Rop_uK ≤ 2 * Rop_uK + 1) hCM1nn) hcpos.le
  · -- (3) the mixed derivatives `∂_z^c D_θ^a ℛ`, `a ≥ 1`, `a + c ≤ 4`
    intro a c ha hac z hz θ hθ
    rw [show (1 : ℝ) + z = z + 1 from by ring]
    have hzIz : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
    have hθIz : θ ∈ Work.Spaces.Iθ := Set.mem_Icc.mpr ⟨hθ.1.le, hθ.2.le⟩
    have hz1 : (0 : ℝ) < z + 1 := by linarith
    have hcpos : (0 : ℝ) < (z + 1) ^ c := pow_pos hz1 c
    have hsin0 : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2])
    have hden : 0 < α + Real.sin (2 * θ) := by linarith
    have hpe : Work.Spaces.pzIter c (Work.Spaces.DthIter a Rc) z θ
        = Work.Spaces.pzIter c (Work.Spaces.DthIter a R) z θ := by
      rw [Work.Spaces.pzIter_eq_iteratedDeriv, Work.Spaces.pzIter_eq_iteratedDeriv]
      congr 1
      funext z'
      exact Work.FTS.Nonlinear.Pieces.RNP.row10aux.DthIter_congr_nhds (u := Rc) (v := R)
        (V := Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) (isOpen_univ.prod isOpen_Ioo)
        (fun p hp => by
          show (if p.2 ∈ Set.Ioo (0 : ℝ) (π / 2) then R p.1 p.2 else 0) = R p.1 p.2
          rw [if_pos hp.2]) a z' θ ⟨Set.mem_univ _, hθ⟩
    have hb := Work.Spaces.WlInf_mixed_bound α 4 Rc hRc.1 a c ha (by omega : c + a ≤ 4)
      z θ hzIz hθIz
    have hb' : (z + 1) ^ c * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a R) z θ|
        * (Real.sin (2 * θ) ^ (-(α / 5)) / (α + Real.sin (2 * θ))))
        ≤ Work.Spaces.WlInf α 4 Rc := by
      have h := hb
      rw [hpe] at h
      rw [abs_div, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hz1.le c),
        abs_of_nonneg (Real.rpow_nonneg hsin0 _), abs_of_pos hden] at h
      calc (z + 1) ^ c * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a R) z θ|
          * (Real.sin (2 * θ) ^ (-(α / 5)) / (α + Real.sin (2 * θ))))
          = ((z + 1) ^ c * |Work.Spaces.pzIter c (Work.Spaces.DthIter a R) z θ|)
              * Real.sin (2 * θ) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) := by ring
        _ ≤ Work.Spaces.WlInf α 4 Rc := h
    have hmain : |Work.Spaces.pzIter c (Work.Spaces.DthIter a R) z θ|
        * (Real.sin (2 * θ) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        ≤ Work.Spaces.WlInf α 4 Rc / (z + 1) ^ c := by
      rw [le_div_iff₀ hcpos]
      calc (|Work.Spaces.pzIter c (Work.Spaces.DthIter a R) z θ|
          * (Real.sin (2 * θ) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))) * (z + 1) ^ c
          = (z + 1) ^ c * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a R) z θ|
          * (Real.sin (2 * θ) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))) := by ring
        _ ≤ Work.Spaces.WlInf α 4 Rc := hb'
    calc |Work.Spaces.pzIter c (Work.Spaces.DthIter a R) z θ|
        * (Real.sin (2 * θ) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        ≤ Work.Spaces.WlInf α 4 Rc / (z + 1) ^ c := hmain
      _ ≤ Rop_uK * (max Cs 0 * α) / (z + 1) ^ c :=
          div_le_div_of_nonneg_right hRc.2 hcpos.le
      _ ≤ Rop_uK * (max Cs 1 * α) / (z + 1) ^ c :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hCM0le Rop_uK_pos.le) hcpos.le
      _ ≤ (2 * Rop_uK + 1) * (max Cs 1 * α) / (z + 1) ^ c :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by linarith [Rop_uK_pos] :
              Rop_uK ≤ 2 * Rop_uK + 1) hCM1nn) hcpos.le
  · -- (4) the angular derivatives `D_θ^a ℛ`, `a ≥ 1`: here the de-weighting
    -- `D_θ^a ℛ = (z/(1+z))·D_θ^a H` supplies the extra factor `z/(1+z)`
    intro a ha ha4 z hz θ hθ
    have hzIz : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
    have hθIz : θ ∈ Work.Spaces.Iθ := Set.mem_Icc.mpr ⟨hθ.1.le, hθ.2.le⟩
    have hsin0 : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2])
    have hden : 0 < α + Real.sin (2 * θ) := by linarith
    have hD : Work.Spaces.DthIter a R z θ = z / (1 + z) * Work.Spaces.DthIter a H z θ := by
      have hmul : Work.Spaces.DthIter a (fun z θ => z / (1 + z) * H z θ) z θ
          = z / (1 + z) * Work.Spaces.DthIter a H z θ := by
        rw [Work.FTS.Nonlinear.Pieces.RNP.row10aux.DthIter_mul_phi]
      rw [← hmul]
      refine Work.FTS.Nonlinear.Pieces.RNP.row10aux.DthIter_congr_nhds (u := R)
        (v := fun z θ => z / (1 + z) * H z θ) (V := Set.Ioi 0 ×ˢ Set.univ)
        (isOpen_Ioi.prod isOpen_univ) ?_ a z θ ⟨hz, trivial⟩
      rintro ⟨z', θ'⟩ hp
      have hzne : z' ≠ 0 := ne_of_gt hp.1
      have hz1ne : (1 : ℝ) + z' ≠ 0 := by
        have hz' : (0 : ℝ) < z' := hp.1
        positivity
      show R z' θ' = z' / (1 + z') * ((z' + 1) / z' * R z' θ')
      field_simp
      ring
    have hσnn : 0 ≤ Real.sin (2 * θ) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) :=
      div_nonneg (Real.rpow_nonneg hsin0 _) hden.le
    have hHmix : |Work.Spaces.DthIter a H z θ|
        * (Real.sin (2 * θ) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        ≤ Work.Spaces.WlInf α 4 H := by
      have h := Work.Spaces.WlInf_mixed_bound α 4 H hHmem a 0 ha (by omega : 0 + a ≤ 4)
        z θ hzIz hθIz
      have hconv : |(z + 1) ^ 0 * Work.Spaces.pzIter 0 (Work.Spaces.DthIter a H) z θ
            * Real.sin (2 * θ) ^ (-(α / 5)) / (α + Real.sin (2 * θ))|
          = |Work.Spaces.DthIter a H z θ|
            * (Real.sin (2 * θ) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) := by
        rw [abs_div, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hsin0 _),
          abs_of_pos hden]
        simp only [pow_zero, one_mul, Work.Spaces.pzIter_zero, abs_one]
        rw [mul_div_assoc]
      rwa [hconv] at h
    have haz : 0 ≤ z / (1 + z) := by positivity
    calc |Work.Spaces.DthIter a R z θ|
        * (Real.sin (2 * θ) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        = z / (1 + z) * (|Work.Spaces.DthIter a H z θ|
            * (Real.sin (2 * θ) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))) := by
          rw [hD, abs_mul, abs_of_nonneg haz]; ring
      _ ≤ z / (1 + z) * (max Cs 1 * α) :=
          mul_le_mul_of_nonneg_left (le_trans hHmix hWle) haz
      _ ≤ (2 * Rop_uK + 1) * (max Cs 1 * α) * z / (1 + z) := by
          have h1 : (1 : ℝ) ≤ 2 * Rop_uK + 1 := by linarith [Rop_uK_pos]
          have hX : 0 ≤ (max Cs 1 * α) * (z / (1 + z)) := mul_nonneg hCM1nn haz
          calc z / (1 + z) * (max Cs 1 * α)
              = 1 * ((max Cs 1 * α) * (z / (1 + z))) := by ring
            _ ≤ (2 * Rop_uK + 1) * ((max Cs 1 * α) * (z / (1 + z))) :=
                mul_le_mul_of_nonneg_right h1 hX
            _ = (2 * Rop_uK + 1) * (max Cs 1 * α) * z / (1 + z) := by ring

end Work.FTS.Nonlinear.Pieces.RNP
