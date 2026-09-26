import Mathlib.Analysis.Normed.Order.Lattice
import Submission.Commons.Analysis.RealIntervals.open_preconnected_nonempty_subset_unit_Ioo_shape

open Set
open scoped Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false

noncomputable section

namespace Commons.Topology.OneManifold
/-
# Record of the received request (quoted verbatim)

This commons file was requested with the declaration quoted below, but the
request text wrapped it in the module skeleton and glued the proof placeholder
after the closing `end Commons.Topology.OneManifold` (as `:= by` plus the
proof placeholder).  The
received text is kept here exactly as sent, truncated just before the
placeholder, for the record; the declaration is then stated afresh below with
the identical header and proved.
theorem chart_pullback_interval_shape {X : Type*} [TopologicalSpace X] {U W : Set X}
    (hUopen : IsOpen U) (hUconn : ConnectedSpace {x : X // x ∈ U}) (hUW : U ⊆ W)
    (χ : ({t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1}) ≃ₜ {x : X // x ∈ W}) :
    ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧
      ∀ t : {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1}, ((χ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo a b

end Commons.Topology.OneManifold := by
-/

/-- Inside an open arc `W` (with chart `χ : (0,1) ≃ₜ {x : X // x ∈ W}`), a
connected open subset `U ⊆ W` occupies a coordinate interval: there are
`0 ≤ a < b ≤ 1` such that a chart point `t ∈ (0,1)` lies over `U` iff
`t ∈ (a,b)`.  Proof: the pullback `{t | (χ t : X) ∈ U}` is open, nonempty
and preconnected in `(0,1)` (U is connected and open), hence by the shape
classification of open preconnected subsets of ℝ it is an interval `(a,b)`;
the bounds `0 ≤ a`, `b ≤ 1` follow from it being a subset of `(0,1)`. -/
theorem chart_pullback_interval_shape {X : Type*} [TopologicalSpace X] {U W : Set X}
    (hUopen : IsOpen U) (hUconn : ConnectedSpace {x : X // x ∈ U}) (hUW : U ⊆ W)
    (χ : ({t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1}) ≃ₜ {x : X // x ∈ W}) :
    ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧
      ∀ t : {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1}, ((χ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo a b := by
  -- `S` is the coordinate set: the chart points lying over `U`.
  let S : Set {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1} := {t | (χ t : X) ∈ U}
  -- the chart map is continuous into X
  have hfcont : Continuous (fun t : {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1} => (χ t : X)) :=
    continuous_subtype_val.comp χ.continuous
  -- S is open
  have hSopen : IsOpen S := by
    have hpre : IsOpen ((fun t : {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1} => (χ t : X)) ⁻¹' U) :=
      hUopen.preimage hfcont
    change IsOpen ((fun t : {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1} => (χ t : X)) ⁻¹' U)
    exact hpre
  -- S is nonempty (U is nonempty, as it carries a ConnectedSpace)
  have hU_nonempty : Nonempty {x : X // x ∈ U} := hUconn.toNonempty
  rcases hU_nonempty with ⟨xU⟩
  let a₀ : {x : X // x ∈ W} := ⟨xU.1, hUW xU.2⟩
  have ht₀S : χ.symm a₀ ∈ S := by
    dsimp [S]
    rw [χ.apply_symm_apply]
    dsimp [a₀]
    exact xU.2
  have hSne : S.Nonempty := ⟨χ.symm a₀, ht₀S⟩
  -- preconnectedness of the set of W-points lying over U, via the connected
  -- subtype {x // x ∈ U} mapping continuously onto it
  have hU'pc : IsPreconnected ({a : {x : X // x ∈ W} | (a : X) ∈ U} :
      Set {x : X // x ∈ W}) := by
    letI : PreconnectedSpace {x : X // x ∈ U} := hUconn.toPreconnectedSpace
    let g : {x : X // x ∈ U} → X := fun c => (c : X)
    let h : {x : X // x ∈ U} → {x : X // x ∈ W} := Set.codRestrict g W (fun c => hUW c.2)
    have hgcont : Continuous g := by
      simpa [g] using (continuous_subtype_val : Continuous (fun c : {x : X // x ∈ U} => (c : X)))
    have hhcont : Continuous h := hgcont.codRestrict (fun c => hUW c.2)
    have hrng : IsPreconnected (Set.range h) := isPreconnected_range hhcont
    have hrng_eq : Set.range h = {a : {x : X // x ∈ W} | (a : X) ∈ U} := by
      ext a
      constructor
      · rintro ⟨c, rfl⟩
        simpa [h, g] using c.2
      · intro ha
        refine ⟨⟨(a : X), ha⟩, ?_⟩
        apply Subtype.ext
        simp [h, g]
    rw [← hrng_eq]
    exact hrng
  -- S is the image of that set under the inverse chart, hence preconnected
  have hSpc : IsPreconnected S := by
    have hS_eq : S = χ.symm '' {a : {x : X // x ∈ W} | (a : X) ∈ U} := by
      ext t
      constructor
      · intro ht
        refine ⟨χ t, ?_, ?_⟩
        · simpa [S] using ht
        · exact χ.symm_apply_apply t
      · rintro ⟨a, haU, ht⟩
        have hχt : χ t = a := by
          calc
            χ t = χ (χ.symm a) := by rw [ht]
            _ = a := χ.apply_symm_apply a
        simpa [S, hχt] using haU
    rw [hS_eq]
    exact hU'pc.image χ.symm (χ.symm.continuous.continuousOn : ContinuousOn χ.symm
      ({a : {x : X // x ∈ W} | (a : X) ∈ U} : Set {x : X // x ∈ W}))
  -- the real set of coordinate values lying over U
  let valT : {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1} → ℝ := fun t => (t : ℝ)
  let V : Set ℝ := valT '' S
  have hvalT_cont : Continuous valT := continuous_subtype_val
  have hV01 : V ⊆ Set.Ioo (0 : ℝ) 1 := by
    rintro y ⟨t, htS, rfl⟩
    exact t.2
  have hVopen : IsOpen V := by
    have hOpenMap : IsOpenMap (fun t : {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1} => (t : ℝ)) :=
      (isOpen_Ioo : IsOpen (Set.Ioo (0 : ℝ) 1)).isOpenMap_subtype_val
    have : IsOpen (valT '' S) := hOpenMap S hSopen
    simpa [V] using this
  have hVne : V.Nonempty := by
    have : (valT '' S).Nonempty := hSne.image valT
    simpa [V] using this
  have hVpc : IsPreconnected V := by
    have : IsPreconnected (valT '' S) := hSpc.image valT hvalT_cont.continuousOn
    simpa [V] using this
  -- shape classification of open preconnected nonempty subsets of (0,1)
  rcases Commons.Analysis.RealIntervals.open_preconnected_nonempty_subset_unit_Ioo_shape
      hV01 hVopen hVne hVpc with ⟨a, b, hab, hVeq⟩
  have h0a : 0 ≤ a := by
    have hsub : Set.Ioo a b ⊆ Set.Ioo (0 : ℝ) 1 := by
      simpa [hVeq] using hV01
    exact ((Ioo_subset_Ioo_iff hab).mp hsub).1
  have hb1 : b ≤ 1 := by
    have hsub : Set.Ioo a b ⊆ Set.Ioo (0 : ℝ) 1 := by
      simpa [hVeq] using hV01
    exact ((Ioo_subset_Ioo_iff hab).mp hsub).2
  refine ⟨a, b, h0a, hab, hb1, ?_⟩
  intro t
  constructor
  · intro htU
    have htS : t ∈ S := by simpa [S] using htU
    have hv : (t : ℝ) ∈ V := by
      change valT t ∈ V
      simpa [V] using (mem_image_of_mem valT htS : valT t ∈ valT '' S)
    simpa [hVeq] using hv
  · intro htIoo
    have hv : (t : ℝ) ∈ V := by simpa [hVeq] using htIoo
    rcases hv with ⟨s, hsS, hEq⟩
    have hs_eq : s = t := Subtype.val_injective hEq
    have htS : t ∈ S := by simpa [hs_eq] using hsS
    simpa [S] using htS

end Commons.Topology.OneManifold