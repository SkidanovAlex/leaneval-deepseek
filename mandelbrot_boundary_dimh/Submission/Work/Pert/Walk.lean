import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Pert.orbit_reduce
import Submission.Work.Pert.MaxDom
import Submission.Work.Pert.walk_defect_sum
import Submission.Work.Pert.DphiP_open

/-!
# `Work.Pert.Walk` — the repaired PERT contract: forward invariance of the return-map domain

This file formalises the contract repair that the R-block needs, and proves the glue that turns it
into the interface's `PertData.orbit` field.  Nothing here changes `Interfaces/Parabolic.lean`:
`PertDataWalk` is a *new* structure in this directory, `PertData` extended by the two fields the
return-map construction provides and the interface currently does not ask for:

* `DR_walk : ∀ w ∈ DR, R w ∈ DR` — **forward invariance of the return-map domain**.  This is what
  the paper's maximal domain gives (its `R̃_f` is defined on the `+1`-saturated waist image), and
  it is exactly what `Submission/Work/Repel/chain_returns_v2.lean` independently derives as
  missing: with it, the walk hypothesis `∀ j < m, R^[j] w ∈ DR` of `PertData.orbit` is
  *automatic* from `w ∈ DR`.
* `DR_sub_Dφ : DR ⊆ Dφ` — the return-map domain lies in the coordinate's domain (for the
  return-map construction `DR = T-sat (Φ '' Wa)` and `Dφ = DphiP` this holds because every point of
  `DR` is a legal level of the coordinate; it is *not* automatic from the interface, where `Dφ` is
  only pinned by `D_sub`/`Dφ_strip`).

Together with the two facts about the *constructed* return map

* `φ (R x) = φ x` for `x ∈ Dφ` (the level-preserving return map; proved in
  `Work.Pert.RBlock7.retP_phi_eq` / `Work.Pert.RBlock3.comp_retOf_eq`), and
* the accumulated-defect bound `‖m/α + (R^[m] w - w)‖ < m/(20‖α‖)` on the walks,

they give the whole `orbit` field by `Work.Pert.orbit_reduce` (`orbit_of_phi_inv` below).

See `Submission/Work/Pert/NOTES_pert2_session15.md` §4 for the refereed diagnosis that forces this
repair: with `R := d.E - 1/rotOf f` (the only choice for which `DR_sub` is free) the invariance
`φ ∘ R = φ` is false, and with the `φ`-invariant return map `R̃_f` the interface's `DR_sub` cannot
hold because `R̃_f` is undefined below the gate height `Ξ`.
-/

namespace Work.Pert

open MandelDim Complex Set Filter
open scoped Topology

noncomputable section

/-- **The repaired PERT data**: `PertData` plus forward invariance of `DR` and `DR ⊆ Dφ`. -/
structure PertDataWalk {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : ParabData f₀ D₀) (f : ℂ → ℂ)
    (Df : Set ℂ) (η y₁ : ℝ) (K K' : Set ℂ) (δ : ℝ)
    extends PertData d f Df η y₁ K K' δ where
  /-- forward invariance of the return-map domain (the paper's maximal domain) -/
  DR_walk : ∀ w ∈ DR, R w ∈ DR
  /-- the return-map domain lies in the coordinate's domain -/
  DR_sub_Dφ : DR ⊆ Dφ

namespace PertDataWalk

variable {f₀ : ℂ → ℂ} {D₀ : Set ℂ} {d : ParabData f₀ D₀} {f : ℂ → ℂ} {Df : Set ℂ} {η y₁ : ℝ}
  {K K' : Set ℂ} {δ : ℝ} (P : PertDataWalk d f Df η y₁ K K' δ)

/-- Under forward invariance, every iterate of a point of `DR` is in `DR`. -/
theorem iterate_mem {w : ℂ} (hw : w ∈ P.DR) : ∀ j : ℕ, P.R^[j] w ∈ P.DR := by
  intro j
  induction j with
  | zero => simpa using hw
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact P.DR_walk _ ih

/-- **The walk hypothesis of `PertData.orbit` is free** once `DR` is forward invariant: it holds
for every `w ∈ DR` and every `m`. -/
theorem walk_free {w : ℂ} (hw : w ∈ P.DR) (m : ℕ) : ∀ j : ℕ, j < m → P.R^[j] w ∈ P.DR :=
  fun j _ => P.iterate_mem hw j

/-- Under the repair, the walk stays in `Dφ` as well. -/
theorem walk_mem_Dφ {w : ℂ} (hw : w ∈ P.DR) : ∀ j : ℕ, P.R^[j] w ∈ P.Dφ :=
  fun j => P.DR_sub_Dφ (P.iterate_mem hw j)

end PertDataWalk

/-- **The glue**: the `orbit` field of `PertData` follows from the `φ`-invariance of `R`, the Abel
walk of `φ`, forward invariance of `DR` and `DR ⊆ Dφ`, and the accumulated-defect bound.  No
two-piece gluing, no crux, no walk identity is needed.

The proof is `Work.Pert.orbit_reduce`: `DR_walk` upgrades the walk hypothesis
`∀ j < m, R^[j] w ∈ DR` to *all* iterates (so `R^[j] w ∈ DR ⊆ Dφ` for every `j ≤ m`), and the
conclusion then follows from the fibre relation `piExp (R^[m] w) = piExp w'`, the defect bound and
the sector condition. -/
theorem orbit_of_phi_inv {f φ R : ℂ → ℂ} {Dφ DR Df : Set ℂ} {α : ℂ}
    (hα : MandelDim.InF1 α)
    (hDRwalk : ∀ w ∈ DR, R w ∈ DR) (hDRDφ : DR ⊆ Dφ)
    (hphi : ∀ x ∈ Dφ, φ (R x) = φ x)
    (habel : ∀ x ∈ Dφ, ∀ k : ℕ, x + (k : ℂ) ∈ Dφ →
      φ (x + (k : ℂ)) = f^[k] (φ x) ∧ ∀ i : ℕ, i < k → f^[i] (φ x) ∈ Df)
    (hsmall : ∀ w ∈ Dφ, w ∈ DR → ∀ m : ℕ, 1 ≤ m →
      ‖(m : ℂ) / α + (R^[m] w - w)‖ < (m : ℝ) / (20 * ‖α‖)) :
    ∀ w ∈ Dφ, ∀ w' ∈ Dφ, ∀ m : ℕ, 1 ≤ m → (∀ j : ℕ, j < m → R^[j] w ∈ DR) →
      MandelDim.piExp (R^[m] w) = MandelDim.piExp w' →
      |Complex.arg (w' + 1 / (2 * α) - w)| < 2 * Real.pi / 3 →
      ∃ n : ℕ, 1 ≤ n ∧ f^[n] (φ w) = φ w' ∧ ∀ i : ℕ, i < n → f^[i] (φ w) ∈ Df := by
  intro w hwDφ w' hw'Dφ m hm hwalk hpi harg
  have hwDR : w ∈ DR := hwalk 0 hm
  have hRall : ∀ j : ℕ, R^[j] w ∈ DR := by
    intro j
    induction j with
    | zero => simpa using hwDR
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact hDRwalk _ ih
  exact orbit_reduce hα hm hphi habel hwDφ (fun j _ => hDRDφ (hRall j)) hw'Dφ hpi
    (hsmall w hwDφ hwDR m hm) harg


/-- **Base case of the `DR ⊆ Dφ` row**: every point of the gate image `Φ '' Q` is a legal level of
`DphiP` (level `0`, vacuous walk).  The general row needs the gate walks in both directions and the
long `Df`-orbits — see `NOTES_pert2_session15.md` §5.2. -/
theorem mem_DphiP_of_mem_image {f τ Φ : ℂ → ℂ} {Df : Set ℂ} {Q : Set ℂ} {ζ : ℂ} (hζ : ζ ∈ Q) :
    Φ ζ ∈ DphiP f Df τ Φ Q :=
  ⟨0, ⟨ζ, hζ, by simp⟩, fun j hj => absurd hj (Nat.not_lt_zero j)⟩


/-! ## The §5.2 definition change: `DR := DphiP ∩ T-sat (Φ '' Wa)`

`GoodP` (`MaxDom`) is `Φ '' Q + ℕ` *with* a walk condition, while the `ℤ`-saturation of the gate
image is `Φ '' Wa + ℤ`.  Taking `DR` to be the *intersection* makes `DR ⊆ Dφ` definitional
(`retDR_sub_Dphi`) and keeps the band coverage `waist_cover_window` usable
(`mem_retDR_of_mem_wa`).  The two facts the return-map construction must still check are recorded
in `NOTES_pert2_session15.md` §5.2/§5.3. -/

/-- The waist of a gate: the points `z` with `z` and `Tt α z` both in `Q`. -/
def retWa (Q : Set ℂ) (α : ℂ) : Set ℂ := {z : ℂ | z ∈ Q ∧ Tt α z ∈ Q}

/-- **The repaired return-map domain**: the coordinate's domain intersected with the `ℤ`-saturation
of the waist image. -/
def retDR (f : ℂ → ℂ) (Df : Set ℂ) (τ Φ : ℂ → ℂ) (Q : Set ℂ) (α : ℂ) : Set ℂ :=
  DphiP f Df τ Φ Q ∩ ⋃ n : ℤ, (fun z : ℂ => z + (n : ℂ)) '' (Φ '' retWa Q α)

/-- **`DR ⊆ Dφ` is definitional for the repaired `DR`** (the §5.2 row, closed). -/
theorem retDR_sub_Dphi {f : ℂ → ℂ} {Df : Set ℂ} {τ Φ : ℂ → ℂ} {Q : Set ℂ} {α : ℂ} :
    retDR f Df τ Φ Q α ⊆ DphiP f Df τ Φ Q :=
  Set.inter_subset_left

/-- **The gate image lands in the repaired domain**: for `ζ` in the waist, `Φ ζ` is in the
`0`-th piece of the saturation and in `DphiP` (the base case `mem_DphiP_of_mem_image`), hence in
`retDR` by `Set.subset_iUnion`. -/
theorem mem_retDR_of_mem_wa {f : ℂ → ℂ} {Df : Set ℂ} {τ Φ : ℂ → ℂ} {Q : Set ℂ} {α : ℂ} {ζ : ℂ}
    (hζ : ζ ∈ Q) (hTζ : Tt α ζ ∈ Q) : Φ ζ ∈ retDR f Df τ Φ Q α := by
  have h0 : Φ ζ ∈ (fun z : ℂ => z + ((0 : ℤ) : ℂ)) '' (Φ '' retWa Q α) := by
    simpa using Set.mem_image_of_mem (fun z : ℂ => z + ((0 : ℤ) : ℂ))
      (Set.mem_image_of_mem Φ (show ζ ∈ retWa Q α from ⟨hζ, hTζ⟩))
  exact ⟨mem_DphiP_of_mem_image hζ,
    Set.subset_iUnion (fun n : ℤ => (fun z : ℂ => z + (n : ℂ)) '' (Φ '' retWa Q α)) 0 h0⟩

/-- **The `hsmall` wire**: a per-step defect bound on `DR` plus `A < 1/(20||α||)` gives the
accumulated-defect hypothesis that `orbit_of_phi_inv` consumes, along any walk that stays in
`DR`.  This is the composition of `Work.Pert.walk_defect_sum` (the telescoping) with the caller's
per-step estimate (in the intended application the per-step estimate is `R_close`-type data,
`R x + 1/α ≈ d.E x`, together with the boundedness of `d.E - id`). -/
theorem hsmall_of_step {R : ℂ → ℂ} {DR : Set ℂ} {α : ℂ} {A : ℝ}
    (hstep : ∀ x ∈ DR, ‖R x - x + 1 / α‖ ≤ A) (hA : A < 1 / (20 * ‖α‖)) :
    ∀ w ∈ DR, ∀ m : ℕ, 1 ≤ m → (∀ j : ℕ, j < m → R^[j] w ∈ DR) →
      ‖(m : ℂ) / α + (R^[m] w - w)‖ < (m : ℝ) / (20 * ‖α‖) := by
  intro w hwDR m hm hwalk
  have h := walk_defect_sum (R := R) (α := α) (w := w) (m := m) (A := A)
    (fun j hj => hstep (R^[j] w) (hwalk j hj))
  refine lt_of_le_of_lt h ?_
  have hpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  calc (m : ℝ) * A < (m : ℝ) * (1 / (20 * ‖α‖)) := by
        exact mul_lt_mul_of_pos_left hA hpos
    _ = (m : ℝ) / (20 * ‖α‖) := by ring

/-- **The glue instantiated at `retDR`.**  `orbit_of_phi_inv` with `DR := retDR f Df τ Φ Q α` and
the membership `retDR ⊆ Dphi` **discharged** by `retDR_sub_Dphi` (it is definitional), so a caller
of the construction supplies only the four real inputs: `DR_walk` (from `Work.Pert.tSat_walk`),
the `φ`-invariance (`RBlock7.retP_phi_eq`), the Abel walk (`coordP_add_nat`) and `hsmall`
(`Work.Pert.hsmall_of_step`). -/
theorem orbit_of_retDR {f τ Φ R φ : ℂ → ℂ} {Df Dφ Q : Set ℂ} {α : ℂ}
    (hα : MandelDim.InF1 α)
    (hDRwalk : ∀ w ∈ retDR f Df τ Φ Q α, R w ∈ retDR f Df τ Φ Q α)
    (hDRDφ : retDR f Df τ Φ Q α ⊆ Dφ)
    (hphi : ∀ x ∈ Dφ, φ (R x) = φ x)
    (habel : ∀ x ∈ Dφ, ∀ k : ℕ, x + (k : ℂ) ∈ Dφ →
      φ (x + (k : ℂ)) = f^[k] (φ x) ∧ ∀ i : ℕ, i < k → f^[i] (φ x) ∈ Df)
    (hsmall : ∀ w ∈ Dφ, w ∈ retDR f Df τ Φ Q α → ∀ m : ℕ, 1 ≤ m →
      ‖(m : ℂ) / α + (R^[m] w - w)‖ < (m : ℝ) / (20 * ‖α‖)) :
    ∀ w ∈ Dφ, ∀ w' ∈ Dφ, ∀ m : ℕ, 1 ≤ m →
      (∀ j : ℕ, j < m → R^[j] w ∈ retDR f Df τ Φ Q α) →
      MandelDim.piExp (R^[m] w) = MandelDim.piExp w' →
      |Complex.arg (w' + 1 / (2 * α) - w)| < 2 * Real.pi / 3 →
      ∃ n : ℕ, 1 ≤ n ∧ f^[n] (φ w) = φ w' ∧ ∀ i : ℕ, i < n → f^[i] (φ w) ∈ Df :=
  orbit_of_phi_inv (f := f) (φ := φ) (R := R) (Dφ := Dφ) (DR := retDR f Df τ Φ Q α) (Df := Df)
    (α := α) hα hDRwalk hDRDφ hphi habel hsmall

/-- **`R_equiv`'s `IsTInvariant retDR`** (§5.20): `retDR = DphiP ∩ S` with
`S = ⋃ n : ℤ, (·+n) '' (Φ '' retWa Q α)` `T`-invariant for free, so the field is
`and_congr (hDphi w) hS`. -/
theorem retDR_isTInvariant {f τ Φ : ℂ → ℂ} {Df Q : Set ℂ} {α : ℂ}
    (hDphi : MandelDim.IsTInvariant (DphiP f Df τ Φ Q)) :
    MandelDim.IsTInvariant (retDR f Df τ Φ Q α) := by
  intro w
  have hS : (w ∈ ⋃ n : ℤ, (fun z : ℂ => z + (n : ℂ)) '' (Φ '' retWa Q α)) ↔
      (w + 1 ∈ ⋃ n : ℤ, (fun z : ℂ => z + (n : ℂ)) '' (Φ '' retWa Q α)) := by
    constructor
    · simp only [Set.mem_iUnion, Set.mem_image] at *
      rintro ⟨n, z, hz, hzw⟩
      refine ⟨n + 1, z, hz, ?_⟩
      have hcast : (((n + 1 : ℤ)) : ℂ) = (n : ℂ) + 1 := by push_cast; ring
      rw [hcast]
      linear_combination hzw
    · simp only [Set.mem_iUnion, Set.mem_image] at *
      rintro ⟨n, z, hz, hzw⟩
      refine ⟨n - 1, z, hz, ?_⟩
      have hcast : (((n - 1 : ℤ)) : ℂ) = (n : ℂ) - 1 := by push_cast; ring
      rw [hcast]
      linear_combination hzw
  exact and_congr (hDphi w) hS

/-- **Row 2: `IsOpen (retDR ...)`** (§5.22).  Composition of `DphiP_open` with the openness of the
`ZZ`-saturation of the gate image, the latter being `isOpen_image_of_deriv_ne_zero` on the open
waist `retWa Q α = Q ∩ (Tt α)^{-1} Q` plus `isOpen_iUnion` over the translates
(`asm.lean`'s `hQpOpen` is the template). -/
theorem isOpen_retDR {f : ℂ → ℂ} {Df Q : Set ℂ} {τ Φ : ℂ → ℂ} {α : ℂ}
    (hDf : IsOpen Df) (hQ : IsOpen Q) (hΦ : DifferentiableOn ℂ Φ Q)
    (hτ : DifferentiableOn ℂ τ Q) (hinj : Set.InjOn Φ Q) (hder : ∀ z ∈ Q, deriv Φ z ≠ 0)
    (hf : DifferentiableOn ℂ f Df) :
    IsOpen (retDR f Df τ Φ Q α) := by
  have hWa : IsOpen (retWa Q α) := by
    have h1 : IsOpen (Tt α ⁻¹' Q) :=
      hQ.preimage (by show Continuous fun z : ℂ => z - 1 / α; continuity)
    exact hQ.inter h1
  have hImg : IsOpen (Φ '' retWa Q α) :=
    isOpen_image_of_deriv_ne_zero hWa (hΦ.mono (fun z hz => hz.1))
      (fun z hz => hder z hz.1)
  have hS : IsOpen (⋃ n : ℤ, (fun z : ℂ => z + (n : ℂ)) '' (Φ '' retWa Q α)) :=
    isOpen_iUnion fun n : ℤ => (Homeomorph.addRight ((n : ℤ) : ℂ)).isOpen_image.mpr hImg
  exact (DphiP_open hDf hQ hΦ hτ hinj hder hf).inter hS

end

end Work.Pert
