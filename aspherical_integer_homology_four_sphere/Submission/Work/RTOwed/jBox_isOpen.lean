/-
# Openness of the box of a junction filling chart

`Work.RTOwed.jBox v cU k W kx δ` is the box of a junction chart in the polar coordinates
`(r,θ,w₁,w₂)`:

* `1/4 < r < rBig` — the radial window;
* the `w`-section condition `(q₂,q₃) ∈ W`;
* the wedge pinning `uqOf v q − cU ∈ [0,1)` with `fract (uqOf v q − cU) ∈ (k/4,(k+1)/4)`;
* the collar box condition `∀ i, |x(polarToUHS v q) i − kx i| < δ`.

Every one of these is an *open* condition on `q`:

* the radial window is the preimage of the open interval `(1/4, rBig)` under the continuous
  coordinate `q ↦ q 0`;
* the section condition is the preimage of the open `W` under the continuous projection
  `q ↦ (q₂,q₃)` (this is where `hW : IsOpen W` is used);
* the wedge pinning is *equivalent* to the single open condition `uqOf v q − cU ∈ (k/4,(k+1)/4)`
  (`jBox_wedge_iff`): for `k : Fin 4` the interval `(k/4,(k+1)/4)` is contained in `[0,1)`, so
  `fract` is the identity there; `uqOf v` is continuous, so the preimage of the open interval is
  open;
* the collar box condition is a finite intersection of preimages of `(−δ,δ)` under the continuous
  functions `q ↦ x(polarToUHS v q) i − kx i`.

Hence `jBox` is an intersection of open sets, i.e. open.
-/
import Mathlib
import Submission.Work.RTOwed.FillBigDefs
import Submission.Work.Cusp.isOpen_polarTargetS
import Submission.Work.Cusp.isOpen_polarBox
import Submission.Work.Cusp.isOpen_cuspBoxInterior

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RTOWed

open Set Topology

/-- **The wedge pinning of `jBox` is a single open condition.**  The conjunction
`uqOf v q − cU ∈ [0,1)` and `fract (uqOf v q − cU) ∈ (k/4,(k+1)/4)` is equivalent to
`uqOf v q − cU ∈ (k/4,(k+1)/4)`, because `(k/4,(k+1)/4) ⊆ [0,1)` for `k : Fin 4` (so that `fract`
is the identity on it). -/
theorem jBox_wedge_iff (a : ℝ) (k : Fin 4) :
    (a ∈ Set.Ico (0 : ℝ) 1 ∧ Int.fract a ∈ Set.Ioo ((k : ℝ) / 4) (((k : ℝ) + 1) / 4))
      ↔ a ∈ Set.Ioo ((k : ℝ) / 4) (((k : ℝ) + 1) / 4) := by
  have hk0 : (0 : ℝ) ≤ (k : ℝ) / 4 := by positivity
  have hk1 : ((k : ℝ) + 1) / 4 ≤ 1 := by
    have hk3 : (k : ℝ) ≤ 3 := by exact_mod_cast Nat.le_of_lt_succ k.isLt
    linarith
  constructor
  · rintro ⟨hu, hf⟩
    rwa [Int.fract_eq_self.mpr hu] at hf
  · intro hf
    have h0 : 0 ≤ a := by linarith [hf.1, hk0]
    have h1 : a < 1 := by linarith [hf.2, hk1]
    exact ⟨⟨h0, h1⟩, by rw [Int.fract_eq_self.mpr ⟨h0, h1⟩]; exact hf⟩

/-- **The `i`-th horizontal coordinate of `polarToUHS v q` is continuous in `q`** (for `i : Fin 3`
it is a coordinate of the linear part of `polarToUHS`). -/
theorem continuous_xOf_polarToUHS_apply (v : Fin 5) (i : Fin 3) :
    Continuous (fun q : Work.Cusp.E4 => Work.Cusp.xOf (Work.Cusp.polarToUHS v q) i) := by
  unfold Work.Cusp.xOf Work.Cusp.polarToUHS
  fun_prop

/-- **The box of a junction chart is open** (for an open section box `W`). -/
theorem jBox_isOpen (v : Work.Space.Cusp) (cU : ℝ) (k : Fin 4) (W : Set Work.Cusp.E2)
    (kx : Work.Cusp.E3) (δ : ℝ) (hW : IsOpen W) :
    IsOpen (Work.RTOwed.jBox v cU k W kx δ) := by
  -- the radial window `1/4 < q 0 ∧ q 0 < Work.RTOwed.rBig`
  have h1 : IsOpen {q : Work.Cusp.E4 | 1/4 < q 0 ∧ q 0 < Work.RTOwed.rBig} := by
    have hcont : Continuous (fun q : Work.Cusp.E4 => q 0) :=
      PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) 0
    have h : {q : Work.Cusp.E4 | 1/4 < q 0 ∧ q 0 < Work.RTOwed.rBig}
        = (fun q : Work.Cusp.E4 => q 0) ⁻¹' Set.Ioo (1/4) Work.RTOwed.rBig := rfl
    rw [h]
    exact isOpen_Ioo.preimage hcont
  -- the section condition `(q₂,q₃) ∈ W`
  have h2 : IsOpen {q : Work.Cusp.E4 | (!₂[q 2, q 3] : Work.Cusp.E2) ∈ W} :=
    hW.preimage (by fun_prop)
  -- the wedge pinning
  have h3 : IsOpen {q : Work.Cusp.E4 |
      Work.Cusp.uqOf v q - cU ∈ Set.Ioo ((k : ℝ) / 4) (((k : ℝ) + 1) / 4)} :=
    isOpen_Ioo.preimage ((Work.Cusp.polarTargetS_continuous_uqOf v).sub continuous_const)
  -- the collar box condition
  have h4 : IsOpen {q : Work.Cusp.E4 |
      ∀ i, |Work.Cusp.xOf (Work.Cusp.polarToUHS v q) i - kx i| < δ} := by
    rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_lt (((continuous_xOf_polarToUHS_apply v i).sub continuous_const).abs) continuous_const
  -- decompose the box
  have hdecomp : Work.RTOwed.jBox v cU k W kx δ =
      {q : Work.Cusp.E4 | 1/4 < q 0 ∧ q 0 < Work.RTOwed.rBig}
        ∩ {q : Work.Cusp.E4 | (!₂[q 2, q 3] : Work.Cusp.E2) ∈ W}
        ∩ {q : Work.Cusp.E4 |
            Work.Cusp.uqOf v q - cU ∈ Set.Ioo ((k : ℝ) / 4) (((k : ℝ) + 1) / 4)}
        ∩ {q : Work.Cusp.E4 | ∀ i, |Work.Cusp.xOf (Work.Cusp.polarToUHS v q) i - kx i| < δ} := by
    ext q
    simp only [Work.RTOwed.jBox, Set.mem_ofPred_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨a, b, c, d, e, f⟩
      exact ⟨⟨⟨⟨a, b⟩, c⟩, (jBox_wedge_iff (Work.Cusp.uqOf v q - cU) k).mp ⟨d, e⟩⟩, f⟩
    · rintro ⟨⟨⟨a, b⟩, c⟩, d⟩
      exact ⟨a.1, a.2, b, ((jBox_wedge_iff (Work.Cusp.uqOf v q - cU) k).mpr c).1,
        ((jBox_wedge_iff (Work.Cusp.uqOf v q - cU) k).mpr c).2, d⟩
  rw [hdecomp]
  exact (((h1.inter h2).inter h3).inter h4)

end Work.RTOWed
