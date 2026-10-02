import Mathlib
import Submission.Work.Stems.Hur2.PsiCont
import Submission.Work.Stems.Hur2b.K1_homotopicRel_edge

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Cancelling the `K₁`-fillings of `Ψ(σ)` onto the edges

`Ψ(σ) = psiFun x₀ σ` is built from the four `K₁`-fillings of the edges of `σ` on the four sectors of
the square, and from `σ` itself (rescaled) on the middle quarter-square.  `K1_homotopicRel_edge`
deformation-retracts `K₁ e` onto its `e`-face `{r = 1}`; applying that rescaling to the *radial*
coordinate `r` in the four sector formulas gives an explicit homotopy

* at parameter `0` from `psiFun x₀ σ`, to
* at parameter `1` the map `sigmaClamp σ`, the "clamp collapse" of `σ` onto its core: the same
  `c (pair2 (clamp (2 t₀ - 1/2)) (clamp (2 t₁ - 1/2)))` on the whole square.

The point of the file is the *explicit family* `psiFunCancel`, with its values on the five regions,
its continuity in `(s, t)` and its two endpoints, so that it can be glued along the shared edges of
a `3`-cube (this is the "cancellation" in Hutchings' proof of `(2.5)`).  The agreement of the two
sector formulas on a shared ray survives the interpolation because it is already an agreement of the
*arguments*.
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2b

open Work.Stems.Cubical
open Work.Stems.Hur2

noncomputable section

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]

/-! ## The interpolated sector formulas (and the unchanged inner value) -/

/-- The value on the top sector with the radial `K₁`-coordinate interpolated at parameter `s`. -/
def topValC (x₀ : X) (c : C(IC 2, X)) (s : unitInterval) (t : IC 2) : X :=
  K₁ x₀ (c.comp (faceCM (1 : Fin 2) (1 : unitInterval)))
    (pair2 (interp s (clamp (4 - 4 * (t 1 : ℝ)))) (clamp (2 * (t 0 : ℝ) - 1/2)))

/-- The value on the right sector with the radial `K₁`-coordinate interpolated. -/
def rightValC (x₀ : X) (c : C(IC 2, X)) (s : unitInterval) (t : IC 2) : X :=
  K₁ x₀ (c.comp (faceCM (0 : Fin 2) (1 : unitInterval)))
    (pair2 (interp s (clamp (4 - 4 * (t 0 : ℝ)))) (clamp (2 * (t 1 : ℝ) - 1/2)))

/-- The value on the bottom sector with the radial `K₁`-coordinate interpolated. -/
def botValC (x₀ : X) (c : C(IC 2, X)) (s : unitInterval) (t : IC 2) : X :=
  K₁ x₀ (c.comp (faceCM (1 : Fin 2) (0 : unitInterval)))
    (pair2 (interp s (clamp (4 * (t 1 : ℝ)))) (clamp (2 * (t 0 : ℝ) - 1/2)))

/-- The value on the left sector with the radial `K₁`-coordinate interpolated. -/
def leftValC (x₀ : X) (c : C(IC 2, X)) (s : unitInterval) (t : IC 2) : X :=
  K₁ x₀ (c.comp (faceCM (0 : Fin 2) (0 : unitInterval)))
    (pair2 (interp s (clamp (4 * (t 0 : ℝ)))) (clamp (2 * (t 1 : ℝ) - 1/2)))

/-- **The cancellation family**: `Ψ(σ)` with the radial `K₁`-coordinates interpolated at `s`. -/
def psiFunCancel (x₀ : X) (c : C(IC 2, X)) (s : unitInterval) (t : IC 2) : X := by
  classical
  exact if _h1 : t ∈ topSet then topValC x₀ c s t
  else if _h2 : t ∈ rightSet then rightValC x₀ c s t
  else if _h3 : t ∈ botSet then botValC x₀ c s t
  else if _h4 : t ∈ leftSet then leftValC x₀ c s t
  else innerVal c t

/-- The "clamp collapse" of a cube onto its core: `σ` composed with the collapse of the square onto
the middle quarter-square.  This is the endpoint of the cancellation at `s = 1`. -/
def sigmaClamp (c : C(IC 2, X)) : C(IC 2, X) :=
  c.comp ⟨fun t => pair2 (clamp (2 * (t 0 : ℝ) - 1/2)) (clamp (2 * (t 1 : ℝ) - 1/2)),
    continuous_pair2 (continuous_clamp.comp (by fun_prop))
      (continuous_clamp.comp (by fun_prop))⟩

theorem sigmaClamp_apply (c : C(IC 2, X)) (t : IC 2) : sigmaClamp c t = innerVal c t := rfl

/-! ## The value lemmas at the five regions -/

theorem psiFunCancel_eq_topValC {x₀ : X} {c : C(IC 2, X)} {s : unitInterval} {t : IC 2}
    (h : t ∈ topSet) : psiFunCancel x₀ c s t = topValC x₀ c s t := by
  classical
  rw [psiFunCancel]
  exact dif_pos h

theorem psiFunCancel_eq_rightValC {x₀ : X} {c : C(IC 2, X)} {s : unitInterval} {t : IC 2}
    (h1 : t ∉ topSet) (h : t ∈ rightSet) : psiFunCancel x₀ c s t = rightValC x₀ c s t := by
  classical
  rw [psiFunCancel]
  rw [dif_neg h1]
  exact dif_pos h

theorem psiFunCancel_eq_botValC {x₀ : X} {c : C(IC 2, X)} {s : unitInterval} {t : IC 2}
    (h1 : t ∉ topSet) (h2 : t ∉ rightSet) (h : t ∈ botSet) :
    psiFunCancel x₀ c s t = botValC x₀ c s t := by
  classical
  rw [psiFunCancel]
  rw [dif_neg h1, dif_neg h2]
  exact dif_pos h

theorem psiFunCancel_eq_leftValC {x₀ : X} {c : C(IC 2, X)} {s : unitInterval} {t : IC 2}
    (h1 : t ∉ topSet) (h2 : t ∉ rightSet) (h3 : t ∉ botSet) (h : t ∈ leftSet) :
    psiFunCancel x₀ c s t = leftValC x₀ c s t := by
  classical
  rw [psiFunCancel]
  rw [dif_neg h1, dif_neg h2, dif_neg h3]
  exact dif_pos h

theorem psiFunCancel_eq_innerVal {x₀ : X} {c : C(IC 2, X)} {s : unitInterval} {t : IC 2}
    (h1 : t ∉ topSet) (h2 : t ∉ rightSet) (h3 : t ∉ botSet) (h4 : t ∉ leftSet) :
    psiFunCancel x₀ c s t = innerVal c t := by
  classical
  rw [psiFunCancel]
  rw [dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4]

/-! ## Agreement of the sector formulas on the overlaps (with the interpolation) -/

theorem topValC_eq_rightValC_of_mem {x₀ : X} {c : C(IC 2, X)} {s : unitInterval} {t : IC 2}
    (ht : t ∈ topSet) (hr : t ∈ rightSet) : topValC x₀ c s t = rightValC x₀ c s t := by
  obtain ⟨hb, hc, hab⟩ := ht
  obtain ⟨ha, hd, hba⟩ := hr
  have hab' : (t 0 : ℝ) = (t 1 : ℝ) := le_antisymm hab hba
  have h2a : (1 : ℝ) ≤ 2 * (t 0 : ℝ) - 1/2 := by linarith
  have h2b : (1 : ℝ) ≤ 2 * (t 1 : ℝ) - 1/2 := by linarith
  rw [topValC, rightValC, clamp_of_ge_one h2a, clamp_of_ge_one h2b, K₁_pair2_eq_one,
    K₁_pair2_eq_one,
    show (c.comp (faceCM (1 : Fin 2) (1 : unitInterval))) (1 : IC 1) = c (pair2 1 1) from by
      rw [show (1 : IC 1) = iota 1 from rfl, comp_faceCM_11_apply],
    show (c.comp (faceCM (0 : Fin 2) (1 : unitInterval))) (1 : IC 1) = c (pair2 1 1) from by
      rw [show (1 : IC 1) = iota 1 from rfl, comp_faceCM_01_apply],
    show 4 - 4 * (t 0 : ℝ) = 4 - 4 * (t 1 : ℝ) by rw [hab']]

theorem topValC_eq_leftValC_of_mem {x₀ : X} {c : C(IC 2, X)} {s : unitInterval} {t : IC 2}
    (ht : t ∈ topSet) (hl : t ∈ leftSet) : topValC x₀ c s t = leftValC x₀ c s t := by
  obtain ⟨hb, hc, hab⟩ := ht
  obtain ⟨ha, hd, hba⟩ := hl
  have h' : 1 - (t 1 : ℝ) = (t 0 : ℝ) := by linarith
  have h2a : 2 * (t 0 : ℝ) - 1/2 ≤ 0 := by linarith
  have h2b : (1 : ℝ) ≤ 2 * (t 1 : ℝ) - 1/2 := by linarith
  rw [topValC, leftValC, clamp_of_le_zero h2a, clamp_of_ge_one h2b, K₁_pair2_eq_zero,
    K₁_pair2_eq_one,
    show (c.comp (faceCM (1 : Fin 2) (1 : unitInterval))) (0 : IC 1) = c (pair2 0 1) from by
      rw [show (0 : IC 1) = iota 0 from rfl, comp_faceCM_11_apply],
    show (c.comp (faceCM (0 : Fin 2) (0 : unitInterval))) (1 : IC 1) = c (pair2 0 1) from by
      rw [show (1 : IC 1) = iota 1 from rfl, comp_faceCM_00_apply],
    show 4 - 4 * (t 1 : ℝ) = 4 * (t 0 : ℝ) by rw [← h']; ring]

theorem rightValC_eq_botValC_of_mem {x₀ : X} {c : C(IC 2, X)} {s : unitInterval} {t : IC 2}
    (hr : t ∈ rightSet) (hb : t ∈ botSet) : rightValC x₀ c s t = botValC x₀ c s t := by
  obtain ⟨ha, hd, hba⟩ := hr
  obtain ⟨hb', hba', hc'⟩ := hb
  have h' : (t 1 : ℝ) = 1 - (t 0 : ℝ) := by linarith
  have h2b : 2 * (t 1 : ℝ) - 1/2 ≤ 0 := by linarith
  have h2a : (1 : ℝ) ≤ 2 * (t 0 : ℝ) - 1/2 := by linarith
  rw [rightValC, botValC, clamp_of_le_zero h2b, clamp_of_ge_one h2a, K₁_pair2_eq_zero,
    K₁_pair2_eq_one,
    show (c.comp (faceCM (0 : Fin 2) (1 : unitInterval))) (0 : IC 1) = c (pair2 1 0) from by
      rw [show (0 : IC 1) = iota 0 from rfl, comp_faceCM_01_apply],
    show (c.comp (faceCM (1 : Fin 2) (0 : unitInterval))) (1 : IC 1) = c (pair2 1 0) from by
      rw [show (1 : IC 1) = iota 1 from rfl, comp_faceCM_10_apply],
    show 4 - 4 * (t 0 : ℝ) = 4 * (t 1 : ℝ) by rw [h']; ring]

theorem botValC_eq_leftValC_of_mem {x₀ : X} {c : C(IC 2, X)} {s : unitInterval} {t : IC 2}
    (hb : t ∈ botSet) (hl : t ∈ leftSet) : botValC x₀ c s t = leftValC x₀ c s t := by
  obtain ⟨hb', hba', hc'⟩ := hb
  obtain ⟨ha, hab, hd⟩ := hl
  have h' : (t 0 : ℝ) = (t 1 : ℝ) := le_antisymm hab hba'
  have h2a : 2 * (t 1 : ℝ) - 1/2 ≤ 0 := by linarith
  have h2a' : 2 * (t 0 : ℝ) - 1/2 ≤ 0 := by linarith
  rw [botValC, leftValC, clamp_of_le_zero h2a', clamp_of_le_zero h2a, K₁_pair2_eq_zero,
    K₁_pair2_eq_zero,
    show (c.comp (faceCM (1 : Fin 2) (0 : unitInterval))) (0 : IC 1) = c (pair2 0 0) from by
      rw [show (0 : IC 1) = iota 0 from rfl, comp_faceCM_10_apply],
    show (c.comp (faceCM (0 : Fin 2) (0 : unitInterval))) (0 : IC 1) = c (pair2 0 0) from by
      rw [show (0 : IC 1) = iota 0 from rfl, comp_faceCM_00_apply],
    h']

theorem topValC_eq_innerVal_of_mem {x₀ : X} {c : C(IC 2, X)} {s : unitInterval} {t : IC 2}
    (ht : t ∈ topSet) (hi : t ∈ innerSet) : topValC x₀ c s t = innerVal c t := by
  obtain ⟨hb, hc, hab⟩ := ht
  obtain ⟨hi1, hi2, hi3, hi4⟩ := hi
  have hb' : (t 1 : ℝ) = 3/4 := le_antisymm hi4 hb
  rw [topValC, innerVal, show 4 - 4 * (t 1 : ℝ) = 1 by rw [hb']; ring, clamp_one,
    interp_of_eq_one rfl, K₁_pair2_one, comp_faceCM_11_apply,
    show 2 * (t 1 : ℝ) - 1/2 = 1 by rw [hb']; ring, clamp_one]

theorem rightValC_eq_innerVal_of_mem {x₀ : X} {c : C(IC 2, X)} {s : unitInterval} {t : IC 2}
    (hr : t ∈ rightSet) (hi : t ∈ innerSet) : rightValC x₀ c s t = innerVal c t := by
  obtain ⟨ha, hd, hba⟩ := hr
  obtain ⟨hi1, hi2, hi3, hi4⟩ := hi
  have ha' : (t 0 : ℝ) = 3/4 := le_antisymm hi2 ha
  rw [rightValC, innerVal, show 4 - 4 * (t 0 : ℝ) = 1 by rw [ha']; ring, clamp_one,
    interp_of_eq_one rfl, K₁_pair2_one, comp_faceCM_01_apply,
    show 2 * (t 0 : ℝ) - 1/2 = 1 by rw [ha']; ring, clamp_one]

theorem botValC_eq_innerVal_of_mem {x₀ : X} {c : C(IC 2, X)} {s : unitInterval} {t : IC 2}
    (hb : t ∈ botSet) (hi : t ∈ innerSet) : botValC x₀ c s t = innerVal c t := by
  obtain ⟨hb', hba', hc'⟩ := hb
  obtain ⟨hi1, hi2, hi3, hi4⟩ := hi
  have hb'' : (t 1 : ℝ) = 1/4 := le_antisymm hb' hi3
  rw [botValC, innerVal, show 4 * (t 1 : ℝ) = 1 by rw [hb'']; ring, clamp_one,
    interp_of_eq_one rfl, K₁_pair2_one, comp_faceCM_10_apply,
    show 2 * (t 1 : ℝ) - 1/2 = 0 by rw [hb'']; ring, clamp_zero]

theorem leftValC_eq_innerVal_of_mem {x₀ : X} {c : C(IC 2, X)} {s : unitInterval} {t : IC 2}
    (hl : t ∈ leftSet) (hi : t ∈ innerSet) : leftValC x₀ c s t = innerVal c t := by
  obtain ⟨ha, hab, hd⟩ := hl
  obtain ⟨hi1, hi2, hi3, hi4⟩ := hi
  have ha' : (t 0 : ℝ) = 1/4 := le_antisymm ha hi1
  rw [leftValC, innerVal, show 4 * (t 0 : ℝ) = 1 by rw [ha']; ring, clamp_one,
    interp_of_eq_one rfl, K₁_pair2_one, comp_faceCM_00_apply,
    show 2 * (t 0 : ℝ) - 1/2 = 0 by rw [ha']; ring, clamp_zero]

/-! ## The unconditional values on each region -/

theorem psiFunCancel_eq_rightValC' {x₀ : X} {c : C(IC 2, X)} {s : unitInterval} {t : IC 2}
    (ht : t ∈ rightSet) : psiFunCancel x₀ c s t = rightValC x₀ c s t := by
  by_cases h : t ∈ topSet
  · rw [psiFunCancel_eq_topValC h, topValC_eq_rightValC_of_mem h ht]
  · exact psiFunCancel_eq_rightValC h ht

theorem psiFunCancel_eq_botValC' {x₀ : X} {c : C(IC 2, X)} {s : unitInterval} {t : IC 2}
    (ht : t ∈ botSet) : psiFunCancel x₀ c s t = botValC x₀ c s t := by
  by_cases h1 : t ∈ topSet
  · exfalso
    obtain ⟨hb, _, _⟩ := h1
    obtain ⟨hb', _, _⟩ := ht
    linarith
  · by_cases h2 : t ∈ rightSet
    · rw [psiFunCancel_eq_rightValC h1 h2, rightValC_eq_botValC_of_mem h2 ht]
    · exact psiFunCancel_eq_botValC h1 h2 ht

theorem psiFunCancel_eq_leftValC' {x₀ : X} {c : C(IC 2, X)} {s : unitInterval} {t : IC 2}
    (ht : t ∈ leftSet) : psiFunCancel x₀ c s t = leftValC x₀ c s t := by
  by_cases h1 : t ∈ topSet
  · rw [psiFunCancel_eq_topValC h1, topValC_eq_leftValC_of_mem h1 ht]
  · by_cases h2 : t ∈ rightSet
    · exfalso
      obtain ⟨ha, _, _⟩ := h2
      obtain ⟨hb, _, _⟩ := ht
      linarith
    · by_cases h3 : t ∈ botSet
      · rw [psiFunCancel_eq_botValC h1 h2 h3, botValC_eq_leftValC_of_mem h3 ht]
      · exact psiFunCancel_eq_leftValC h1 h2 h3 ht

theorem psiFunCancel_eq_innerVal' {x₀ : X} {c : C(IC 2, X)} {s : unitInterval} {t : IC 2}
    (ht : t ∈ innerSet) : psiFunCancel x₀ c s t = innerVal c t := by
  by_cases h1 : t ∈ topSet
  · rw [psiFunCancel_eq_topValC h1, topValC_eq_innerVal_of_mem h1 ht]
  · by_cases h2 : t ∈ rightSet
    · rw [psiFunCancel_eq_rightValC h1 h2, rightValC_eq_innerVal_of_mem h2 ht]
    · by_cases h3 : t ∈ botSet
      · rw [psiFunCancel_eq_botValC h1 h2 h3, botValC_eq_innerVal_of_mem h3 ht]
      · by_cases h4 : t ∈ leftSet
        · rw [psiFunCancel_eq_leftValC h1 h2 h3 h4, leftValC_eq_innerVal_of_mem h4 ht]
        · exact psiFunCancel_eq_innerVal h1 h2 h3 h4

/-! ## The endpoints -/

/-- **The cancellation starts at `Ψ(σ)`.** -/
theorem psiFunCancel_zero (x₀ : X) (c : C(IC 2, X)) (t : IC 2) :
    psiFunCancel x₀ c 0 t = psiFun x₀ c t := by
  rcases mem_regions t with ht | ht | ht | ht | ht
  · rw [psiFunCancel_eq_topValC ht, psiFun_eq_topVal ht, topValC, topVal, interp_zero]
  · rw [psiFunCancel_eq_rightValC' ht, psiFun_eq_rightVal' ht, rightValC, rightVal,
      interp_zero]
  · rw [psiFunCancel_eq_botValC' ht, psiFun_eq_botVal' ht, botValC, botVal, interp_zero]
  · rw [psiFunCancel_eq_leftValC' ht, psiFun_eq_leftVal' ht, leftValC, leftVal, interp_zero]
  · rw [psiFunCancel_eq_innerVal' ht, psiFun_eq_innerVal' ht]

/-- **The cancellation ends at the clamp collapse `σ ∘ ρ`.** -/
theorem psiFunCancel_one (x₀ : X) (c : C(IC 2, X)) (t : IC 2) :
    psiFunCancel x₀ c 1 t = sigmaClamp c t := by
  rcases mem_regions t with ht | ht | ht | ht | ht
  · have ht1 : (1 : ℝ) ≤ 2 * (t 1 : ℝ) - 1/2 := by
      obtain ⟨hb, _, _⟩ := ht; linarith
    rw [psiFunCancel_eq_topValC ht, sigmaClamp_apply, topValC, innerVal, interp_one,
      K₁_pair2_one, comp_faceCM_11_apply, clamp_of_ge_one ht1]
  · have ht0 : (1 : ℝ) ≤ 2 * (t 0 : ℝ) - 1/2 := by
      obtain ⟨ha, _, _⟩ := ht; linarith
    rw [psiFunCancel_eq_rightValC' ht, sigmaClamp_apply, rightValC, innerVal, interp_one,
      K₁_pair2_one, comp_faceCM_01_apply, clamp_of_ge_one ht0]
  · have ht1 : 2 * (t 1 : ℝ) - 1/2 ≤ 0 := by
      obtain ⟨hb, _, _⟩ := ht; linarith
    rw [psiFunCancel_eq_botValC' ht, sigmaClamp_apply, botValC, innerVal, interp_one,
      K₁_pair2_one, comp_faceCM_10_apply, clamp_of_le_zero ht1]
  · have ht0 : 2 * (t 0 : ℝ) - 1/2 ≤ 0 := by
      obtain ⟨ha, _, _⟩ := ht; linarith
    rw [psiFunCancel_eq_leftValC' ht, sigmaClamp_apply, leftValC, innerVal, interp_one,
      K₁_pair2_one, comp_faceCM_00_apply, clamp_of_le_zero ht0]
  · rw [psiFunCancel_eq_innerVal' ht, sigmaClamp_apply]

/-- **The cancellation fixes the core**: on the middle quarter-square the homotopy is constant. -/
theorem psiFunCancel_of_mem_inner {x₀ : X} {c : C(IC 2, X)} {s : unitInterval} {t : IC 2}
    (ht : t ∈ innerSet) : psiFunCancel x₀ c s t = psiFun x₀ c t := by
  rw [psiFunCancel_eq_innerVal' ht, psiFun_eq_innerVal' ht]

/-! ## Continuity in `(s, t)` -/

theorem continuous_interp_apply {f : unitInterval × IC 2 → unitInterval} (hf : Continuous f) :
    Continuous fun z : unitInterval × IC 2 => interp z.1 (f z) := by
  unfold interp
  exact continuous_projIcc.comp
    (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      (continuous_subtype_val.comp hf)).add
      (continuous_subtype_val.comp continuous_fst))

theorem continuous_topValC (x₀ : X) (c : C(IC 2, X)) :
    Continuous fun z : unitInterval × IC 2 => topValC x₀ c z.1 z.2 :=
  (K₁ x₀ (c.comp (faceCM (1 : Fin 2) (1 : unitInterval)))).continuous.comp
    (continuous_pair2
      (continuous_interp_apply (continuous_clamp.comp (by fun_prop)))
      (continuous_clamp.comp (by fun_prop)))

theorem continuous_rightValC (x₀ : X) (c : C(IC 2, X)) :
    Continuous fun z : unitInterval × IC 2 => rightValC x₀ c z.1 z.2 :=
  (K₁ x₀ (c.comp (faceCM (0 : Fin 2) (1 : unitInterval)))).continuous.comp
    (continuous_pair2
      (continuous_interp_apply (continuous_clamp.comp (by fun_prop)))
      (continuous_clamp.comp (by fun_prop)))

theorem continuous_botValC (x₀ : X) (c : C(IC 2, X)) :
    Continuous fun z : unitInterval × IC 2 => botValC x₀ c z.1 z.2 :=
  (K₁ x₀ (c.comp (faceCM (1 : Fin 2) (0 : unitInterval)))).continuous.comp
    (continuous_pair2
      (continuous_interp_apply (continuous_clamp.comp (by fun_prop)))
      (continuous_clamp.comp (by fun_prop)))

theorem continuous_leftValC (x₀ : X) (c : C(IC 2, X)) :
    Continuous fun z : unitInterval × IC 2 => leftValC x₀ c z.1 z.2 :=
  (K₁ x₀ (c.comp (faceCM (0 : Fin 2) (0 : unitInterval)))).continuous.comp
    (continuous_pair2
      (continuous_interp_apply (continuous_clamp.comp (by fun_prop)))
      (continuous_clamp.comp (by fun_prop)))

theorem continuous_innerVal' (c : C(IC 2, X)) :
    Continuous fun z : unitInterval × IC 2 => innerVal c z.2 :=
  (continuous_innerVal c).comp continuous_snd

/-- **Continuity of the cancellation family in `(s, t)`.** -/
theorem continuous_psiFunCancel (x₀ : X) (c : C(IC 2, X)) :
    Continuous fun z : unitInterval × IC 2 => psiFunCancel x₀ c z.1 z.2 := by
  rw [← continuousOn_univ]
  rw [show (Set.univ : Set (unitInterval × IC 2)) =
      ((Prod.snd ⁻¹' topSet ∪ Prod.snd ⁻¹' rightSet) ∪ Prod.snd ⁻¹' botSet) ∪
        (Prod.snd ⁻¹' leftSet ∪ Prod.snd ⁻¹' innerSet) from by
    ext z
    simp only [Set.mem_univ, Set.mem_union, Set.mem_preimage, true_iff]
    rcases mem_regions z.2 with h | h | h | h | h <;> tauto]
  rw [continuousOn_union_iff_of_isClosed
      (((isClosed_topSet.preimage continuous_snd).union
        (isClosed_rightSet.preimage continuous_snd)).union
        (isClosed_botSet.preimage continuous_snd))
      ((isClosed_leftSet.preimage continuous_snd).union
        (isClosed_innerSet.preimage continuous_snd))]
  constructor
  · rw [continuousOn_union_iff_of_isClosed
        ((isClosed_topSet.preimage continuous_snd).union
          (isClosed_rightSet.preimage continuous_snd))
        (isClosed_botSet.preimage continuous_snd)]
    constructor
    · rw [continuousOn_union_iff_of_isClosed
          (isClosed_topSet.preimage continuous_snd)
          (isClosed_rightSet.preimage continuous_snd)]
      exact ⟨(continuous_topValC x₀ c).continuousOn.congr
          (fun z hz => psiFunCancel_eq_topValC hz),
        (continuous_rightValC x₀ c).continuousOn.congr
          (fun z hz => psiFunCancel_eq_rightValC' hz)⟩
    · exact (continuous_botValC x₀ c).continuousOn.congr
        (fun z hz => psiFunCancel_eq_botValC' hz)
  · rw [continuousOn_union_iff_of_isClosed
        (isClosed_leftSet.preimage continuous_snd)
        (isClosed_innerSet.preimage continuous_snd)]
    exact ⟨(continuous_leftValC x₀ c).continuousOn.congr
        (fun z hz => psiFunCancel_eq_leftValC' hz),
      (continuous_innerVal' c).continuousOn.congr (fun z hz => psiFunCancel_eq_innerVal' hz)⟩

/-- **The `K₁`-cancellation homotopy**, packaged as a continuous map `I × I² → X`: it deforms
`Ψ(σ)` to the clamp collapse `σ ∘ ρ`, and is constant on the middle quarter-square. -/
def psiCancelHom (x₀ : X) (c : C(IC 2, X)) : C(unitInterval × IC 2, X) :=
  ⟨fun z => psiFunCancel x₀ c z.1 z.2, continuous_psiFunCancel x₀ c⟩

@[simp] theorem psiCancelHom_apply (x₀ : X) (c : C(IC 2, X)) (z : unitInterval × IC 2) :
    psiCancelHom x₀ c z = psiFunCancel x₀ c z.1 z.2 := rfl

/-- The cancellation starts at `Ψ(σ)`. -/
theorem psiCancelHom_zero (x₀ : X) (c : C(IC 2, X)) (t : IC 2) :
    psiCancelHom x₀ c (0, t) = PsiCube x₀ c t := by
  rw [psiCancelHom_apply, psiFunCancel_zero]; rfl

/-- The cancellation ends at the clamp collapse `σ ∘ ρ`. -/
theorem psiCancelHom_one (x₀ : X) (c : C(IC 2, X)) (t : IC 2) :
    psiCancelHom x₀ c (1, t) = sigmaClamp c t := by
  rw [psiCancelHom_apply, psiFunCancel_one]

end

end Work.Stems.Hur2b
