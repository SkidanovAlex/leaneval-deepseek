import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Repel.Setup
import Submission.Work.Repel.Spec
import Submission.Work.Repel.orbit_ne_zero_f0
import Submission.Work.Repel.orbit_ne_zero_g0germ
import Submission.Work.Repel.step1_point
import Submission.Work.Repel.rescale_orbit
import Submission.Work.Repel.not_mem_DE_scaled
import Submission.Work.Repel.disj_mod_one
import Submission.Work.L62.basin_iface

/-!
# REPEL: existence of the §6 setup data (`Work.Repel.Setup`)

This assembles the first stage of Shishikura's §6 from the area hypotheses `hParab`, `hHorn`,
`hL61`, `hF0`, following the recipe in `Submission/Work/Repel/Setup.lean`:

* level 0: `f₀ = x + x²` with `§4.1` data `d₀` (`hParab`) and horn data `hd₀` (`hHorn`);
* Step 1 (`Work.Repel.step1_point`): the lift `w` of an inverse orbit of `0` with
  `π w ∉ insert 0 (π '' (Bu ∪ Bl))`;
* Lemma 6.1 AT LEVEL 0 (`hL61`): two disjoint non-critical inverse orbits `wa, wb` of `pushdown d₀.E`
  through `π w`, and their rescaling `va = s₀ · wa`, `vb = s₀ · wb` (`Work.Repel.rescale_orbit`);
* level 1: the base germ `ǧ₀ = g0germ d₀` with data `d₁` (`hParab`), `hd₁` (`hHorn`);
* Lemma 5.1 at level 1 (`ParabData.invOrbit`): the Fatou-coordinate preimages `ζa, ζb`;
* `ζa, ζb ∉ d₁.DE` (`Work.Repel.not_mem_DE_scaled`), because `d₁.φ ζa = s₀ · π w` lies outside
  `Dg0germ d₀ hd₀ ⊇ ParabolicBasin (g0germ d₀) (Dg0germ d₀ hd₀)`;
* `ζa ≢ ζb (mod ℤ)` (`Work.Repel.disj_mod_one`), from Lemma 6.1's disjointness.
-/

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology
open LeanEval.Dynamics.MandelbrotBoundary

theorem setup_exists (hParab : MandelDim.ParabStatement) (hHorn : MandelDim.HornStatement)
    (hL61 : MandelDim.L61Statement) (hF0 : MandelDim.F0FactsStatement) :
    Nonempty Work.Repel.Setup := by
  -- Step 0: `f₀ = x + x²` is in `𝓕₀` with an inverse orbit `z` of `0` avoiding `-1/2`
  obtain ⟨hF0in, z, hz0, hzrec, hzne, hztend, _⟩ := hF0
  -- level 0: §4.1 data and horn data of `f₀`
  let d₀ : ParabData f0 univ := (hParab f0 univ hF0in.1 Work.Repel.orbit_ne_zero_f0).some
  have hd₀ : HornData d₀ := (hHorn f0 univ hF0in d₀).some
  -- level 1: the base germ `ǧ₀ = g0germ d₀` (Lemma 5.4) with its data
  let d₁ : ParabData (g0germ d₀) (Dg0germ d₀ hd₀) :=
    (hParab (g0germ d₀) (Dg0germ d₀ hd₀) (isParabolicGerm_g0germ d₀ hd₀)
      (Work.Repel.orbit_ne_zero_g0germ d₀ hd₀)).some
  have hd₁ : HornData d₁ :=
    (hHorn (g0germ d₀) (Dg0germ d₀ hd₀) (inF0_g0germ d₀ hd₀) d₁).some
  -- the rescaling constant `s₀ = (pushdown Ẽ_{f₀})''(0)/2`
  let s₀ : ℂ := s0 d₀
  have hs₀ : s₀ = s0 d₀ := rfl
  have hne : s₀ ≠ 0 := by rw [hs₀]; exact s0_ne_zero d₀ hd₀
  -- Step 1: the initial point `w` of the lifted inverse orbit of `0`
  obtain ⟨w, _hwDφ, _hwinv, hwnd⟩ :=
    step1_point d₀ hd₀ hF0in.1 z hz0 hzrec hztend (fun j _ => trivial) ⟨1, hzne 1 le_rfl⟩
  -- Lemma 6.1 at LEVEL 0: two disjoint non-critical inverse orbits through `π w`
  obtain ⟨wa, wb, hwa0, hwb0, hwarec, hwbrec, hwatend, hwbtend, hwdisj⟩ :=
    hL61 f0 univ hF0in d₀ hd₀ (piExp w) (Work.Horn.MandelDim.piExp_ne_zero w) hwnd
  -- the rescaling: `va = s₀ · wa` (resp. `vb = s₀ · wb`) is an inverse orbit of `ǧ₀`
  have hwa : ∀ j, wa (j + 1) ∈ piExp '' (hd₀.Bu ∪ hd₀.Bl) ∧ pushdown d₀.E (wa (j + 1)) = wa j :=
    fun j => ⟨(hwarec j).1, (hwarec j).2.1⟩
  have hwb : ∀ j, wb (j + 1) ∈ piExp '' (hd₀.Bu ∪ hd₀.Bl) ∧ pushdown d₀.E (wb (j + 1)) = wb j :=
    fun j => ⟨(hwbrec j).1, (hwbrec j).2.1⟩
  obtain ⟨hvaD, hvarec, hvatend, hvane⟩ :=
    rescale_orbit d₀ hd₀ s₀ rfl wa hwa hwatend
      (by rw [hwa0]; exact Work.Horn.MandelDim.piExp_ne_zero w)
  obtain ⟨hvbD, hvbrec, hvbtend, hvbne⟩ :=
    rescale_orbit d₀ hd₀ s₀ rfl wb hwb hwbtend
      (by rw [hwb0]; exact Work.Horn.MandelDim.piExp_ne_zero w)
  -- Lemma 5.1 at LEVEL 1: the lifted Fatou-coordinate preimages `ζa, ζb`
  obtain ⟨ζa, _hζaDφ, hζaprop, _⟩ := d₁.invOrbit (fun j => s₀ * wa j) hvaD hvarec hvatend hvane
  obtain ⟨ζb, _hζbDφ, hζbprop, _⟩ := d₁.invOrbit (fun j => s₀ * wb j) hvbD hvbrec hvbtend hvbne
  -- `ζa, ζb` are outside the lifted horn-map domain `d₁.DE`
  have hζa : ζa ∉ d₁.DE := by
    have h : d₁.φ ζa = s0 d₀ * piExp w := by
      have h0 := (hζaprop 0).2
      simpa [hs₀, hwa0] using h0
    exact not_mem_DE_scaled d₀ hd₀ d₁ w ζa hwnd h
  have hζb : ζb ∉ d₁.DE := by
    have h : d₁.φ ζb = s0 d₀ * piExp w := by
      have h0 := (hζbprop 0).2
      simpa [hs₀, hwb0] using h0
    exact not_mem_DE_scaled d₀ hd₀ d₁ w ζb hwnd h
  -- `ζa ≢ ζb` modulo `ℤ`
  have hdisj : ∀ k : ℤ, ζa ≠ ζb + k :=
    disj_mod_one d₀ hd₀ d₁ s₀ hne wa wb hwdisj ζa ζb
      (fun j => (hζaprop j).2) (fun j => (hζbprop j).2)
  exact ⟨{ d₀ := d₀, hd₀ := hd₀, d₁ := d₁, hd₁ := hd₁, s₀ := s₀, hs₀ := hs₀, hne := hne,
           ζa := ζa, ζb := ζb, hζa := hζa, hζb := hζb, hdisj := hdisj }⟩

end Work.Repel
