import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Repel.Setup
import Submission.Work.Repel.Spec
import Submission.Work.Repel.orbit_ne_zero_f0
import Submission.Work.Repel.orbit_ne_zero_g0germ
import Submission.Work.Repel.setup_exists
import Submission.Work.Repel.deriv_germ1_apply
import Submission.Work.Repel.step1_point
import Submission.Work.Repel.rescale_orbit
import Submission.Work.Repel.not_mem_DE_scaled
import Submission.Work.Repel.disj_mod_one
import Submission.Work.L62.basin_iface

/-!
# REPEL: the §6 setup data WITH the two level-1 facts the assembly needs

`Work.Repel.setup_exists` produces *some* `Work.Repel.Setup`.  The §6 composite (see
`NOTES_REPEL3_design.md`, and the consumer `Work.Repel.chain_setup_v2`) needs the two extra facts
about the chosen starting point `ζa` of the level-1 Fatou coordinate:

* `ζa ∈ d₁.Dφ` — so that a ball around `ζa` fits in `d₁.Dφ` (Lemma 5.1 = `ParabData.invOrbit`
  produces `ζa` together with its membership in `Dφ`, but the `Setup` structure does not record
  it);
* `deriv d₁.φ ζa ≠ 0` — the inverse function theorem is applied to `d₁.φ` at `ζa` (the source
  region `W 0` of the Lemma 6.2 chain is a disc around `ζa`, on which `d₁.φ` must be injective).

Both are available *free* at the construction site, from the last conjunct of
`ParabData.invOrbit`: the level-1 inverse orbit `va = s₀ · wa` consists of non-critical points,
because `g₀ = germ1 s₀ Ẽ_{f₀}` is the rescaling of the unperturbed horn map `pushdown d₀.E`
(`deriv (g0germ d) (s₀ · w) = deriv (pushdown d.E) w`) and Lemma 6.1 (`hL61`) supplies the
non-criticality of `wa j`, `wb j` for `j ≥ 1`.

So the proof repeats the construction of `setup_exists` and keeps two additional outputs.
-/

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology
open LeanEval.Dynamics.MandelbrotBoundary

noncomputable section

/-- The derivative of the level-1 base germ `ǧ₀ = g0germ d` along the radial line through `ζ`:
`deriv (g0germ d) (s₀ · ζ) = deriv (pushdown d.E) ζ`.  This is the bridge which transfers the
non-criticality of the unperturbed horn map `pushdown d.E` (Lemma 6.1) to the level-1 germ. -/
lemma deriv_g0germ_mul {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hd : MandelDim.HornData d) (ζ : ℂ) :
    deriv (Work.Repel.g0germ d) (Work.Repel.s0 d * ζ) = deriv (MandelDim.pushdown d.E) ζ := by
  have hs : Work.Repel.s0 d ≠ 0 := Work.Repel.s0_ne_zero d hd
  have h := Work.Repel.deriv_germ1_apply (MandelDim.ParabData.E d) (Work.Repel.s0 d) hs
    (Work.Repel.s0 d * ζ)
  rw [mul_div_cancel_left₀ ζ hs] at h
  exact h

/-- **§6 setup with the two level-1 facts** (`ζa ∈ d₁.Dφ` and `(d₁.φ)'(ζa) ≠ 0`). -/
theorem setup_exists_v2 (hParab : MandelDim.ParabStatement) (hHorn : MandelDim.HornStatement)
    (hL61 : MandelDim.L61Statement) (hF0 : MandelDim.F0FactsStatement) :
    ∃ S : Work.Repel.Setup, S.ζa ∈ S.d₁.Dφ ∧ deriv S.d₁.φ S.ζa ≠ 0 := by
  -- Step 0: `f₀ = x + x²` is in `𝓕₀` with an inverse orbit `z` of `0` avoiding `-1/2`
  obtain ⟨hF0in, z, hz0, hzrec, hzne, hztend, _⟩ := hF0
  -- level 0: §4.1 data and horn data of `f₀`
  let d₀ : MandelDim.ParabData MandelDim.f0 univ := (hParab MandelDim.f0 univ hF0in.1 Work.Repel.orbit_ne_zero_f0).some
  have hd₀ : MandelDim.HornData d₀ := (hHorn MandelDim.f0 univ hF0in d₀).some
  -- level 1: the base germ `ǧ₀ = g0germ d₀` (Lemma 5.4) with its data
  let d₁ : MandelDim.ParabData (Work.Repel.g0germ d₀) (Work.Repel.Dg0germ d₀ hd₀) :=
    (hParab (Work.Repel.g0germ d₀) (Work.Repel.Dg0germ d₀ hd₀)
      (Work.Repel.isParabolicGerm_g0germ d₀ hd₀)
      (Work.Repel.orbit_ne_zero_g0germ d₀ hd₀)).some
  have hd₁ : MandelDim.HornData d₁ :=
    (hHorn (Work.Repel.g0germ d₀) (Work.Repel.Dg0germ d₀ hd₀)
      (Work.Repel.inF0_g0germ d₀ hd₀) d₁).some
  -- Step 1: the initial point `w` of the lifted inverse orbit of `0`
  obtain ⟨w, _hwDφ, _hwinv, hwnd⟩ :=
    Work.Repel.step1_point d₀ hd₀ hF0in.1 z hz0 hzrec hztend (fun j _ => trivial)
      ⟨1, hzne 1 le_rfl⟩
  -- Lemma 6.1 at LEVEL 0: two disjoint non-critical inverse orbits through `π w`
  obtain ⟨wa, wb, hwa0, hwb0, hwarec, hwbrec, hwatend, hwbtend, hwdisj⟩ :=
    hL61 MandelDim.f0 univ hF0in d₀ hd₀ (MandelDim.piExp w)
      (Work.Horn.MandelDim.piExp_ne_zero w) hwnd
  have hwa : ∀ j, wa (j + 1) ∈ MandelDim.piExp '' (hd₀.Bu ∪ hd₀.Bl) ∧
      MandelDim.pushdown d₀.E (wa (j + 1)) = wa j := fun j => ⟨(hwarec j).1, (hwarec j).2.1⟩
  have hwb : ∀ j, wb (j + 1) ∈ MandelDim.piExp '' (hd₀.Bu ∪ hd₀.Bl) ∧
      MandelDim.pushdown d₀.E (wb (j + 1)) = wb j := fun j => ⟨(hwbrec j).1, (hwbrec j).2.1⟩
  -- the rescaling: `va = s₀ · wa` (resp. `vb = s₀ · wb`) is an inverse orbit of `ǧ₀`
  obtain ⟨hvaD, hvarec, hvatend, hvane⟩ :=
    Work.Repel.rescale_orbit d₀ hd₀ (Work.Repel.s0 d₀) rfl wa hwa hwatend
      (by rw [hwa0]; exact Work.Horn.MandelDim.piExp_ne_zero w)
  obtain ⟨hvbD, hvbrec, hvbtend, hvbne⟩ :=
    Work.Repel.rescale_orbit d₀ hd₀ (Work.Repel.s0 d₀) rfl wb hwb hwbtend
      (by rw [hwb0]; exact Work.Horn.MandelDim.piExp_ne_zero w)
  -- non-criticality of `ǧ₀` along the rescaled inverse orbits (Lemma 6.1 transported by
  -- `deriv_g0germ_mul`); this is the hypothesis needed by the last conjunct of Lemma 5.1
  have hderA : ∀ j, 1 ≤ j → deriv (Work.Repel.g0germ d₀) (Work.Repel.s0 d₀ * wa j) ≠ 0 := by
    intro j hj
    rw [deriv_g0germ_mul d₀ hd₀ (wa j)]
    have hshift : j - 1 + 1 = j := Nat.succ_pred_eq_of_pos hj
    rw [← hshift]
    exact (hwarec (j - 1)).2.2
  have hderB : ∀ j, 1 ≤ j → deriv (Work.Repel.g0germ d₀) (Work.Repel.s0 d₀ * wb j) ≠ 0 := by
    intro j hj
    rw [deriv_g0germ_mul d₀ hd₀ (wb j)]
    have hshift : j - 1 + 1 = j := Nat.succ_pred_eq_of_pos hj
    rw [← hshift]
    exact (hwbrec (j - 1)).2.2
  -- Lemma 5.1 at LEVEL 1: the lifted Fatou-coordinate preimages `ζa, ζb`
  obtain ⟨ζa, hζaDφ, hζaprop, hζad⟩ :=
    d₁.invOrbit (fun j => Work.Repel.s0 d₀ * wa j) hvaD hvarec hvatend hvane
  obtain ⟨ζb, hζbDφ, hζbprop, hζbd⟩ :=
    d₁.invOrbit (fun j => Work.Repel.s0 d₀ * wb j) hvbD hvbrec hvbtend hvbne
  -- the two extra facts
  have hζaderiv : deriv d₁.φ ζa ≠ 0 := hζad (fun j hj => hderA j hj)
  -- `ζa, ζb` are outside the lifted horn-map domain `d₁.DE`
  have hζa : ζa ∉ d₁.DE := by
    have h : d₁.φ ζa = Work.Repel.s0 d₀ * MandelDim.piExp w := by
      have h0 := (hζaprop 0).2
      simpa [hwa0] using h0
    exact Work.Repel.not_mem_DE_scaled d₀ hd₀ d₁ w ζa hwnd h
  have hζb : ζb ∉ d₁.DE := by
    have h : d₁.φ ζb = Work.Repel.s0 d₀ * MandelDim.piExp w := by
      have h0 := (hζbprop 0).2
      simpa [hwb0] using h0
    exact Work.Repel.not_mem_DE_scaled d₀ hd₀ d₁ w ζb hwnd h
  -- `ζa ≢ ζb` modulo `ℤ`
  have hdisj : ∀ k : ℤ, ζa ≠ ζb + k :=
    Work.Repel.disj_mod_one d₀ hd₀ d₁ (Work.Repel.s0 d₀) (Work.Repel.s0_ne_zero d₀ hd₀) wa wb
      hwdisj ζa ζb (fun j => (hζaprop j).2) (fun j => (hζbprop j).2)
  exact ⟨{ d₀ := d₀, hd₀ := hd₀, d₁ := d₁, hd₁ := hd₁, s₀ := Work.Repel.s0 d₀, hs₀ := rfl,
           hne := Work.Repel.s0_ne_zero d₀ hd₀, ζa := ζa, ζb := ζb, hζa := hζa, hζb := hζb,
           hdisj := hdisj }, hζaDφ, hζaderiv⟩

end

end Work.Repel
