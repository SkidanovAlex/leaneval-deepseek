import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Repel.Setup
import Submission.Work.Repel.setup_exists_v2
import Submission.Work.Repel.step1_point
import Submission.Work.Repel.orbit_ne_zero_f0
import Submission.Work.Repel.orbit_ne_zero_g0germ
import Submission.Work.F0Facts.Basic

/-!
# REPEL: `setup_exists_v4` — the §6 setup with the level-0 Step-1 point `wt₀`

`Work.Repel.setup_exists_v2` produces a `Work.Repel.Setup` together with the two level-1 facts
(`ζa ∈ d₁.Dφ` and `deriv d₁.φ ζa ≠ 0`).  The §6 consumer `Work.Repel.chain_returns_v3` needs in
addition the **level-0** Step-1 point: Shishikura's `w̃₀ ∈ d₀.Dφ` with `d₀.φ w̃₀ = 0`, which serves
as the centre of the level-0 target disc of the perturbation (4.2.3), together with
`deriv d₀.φ w̃₀ ≠ 0` (needed to apply the inverse function theorem to `d₀.φ` at `w̃₀`).

The point `w̃₀` is exactly the `w` of `Work.Repel.step1_point`, and the derivative fact is the last
conjunct of `ParabData.invOrbit` applied to the inverse orbit `z` of `0` under `f₀ = x + x²`:
`deriv f₀ (z j) = 1 + 2 z j ≠ 0` because `F0FactsStatement` supplies `z j ≠ -1/2` for every `j`.

The content of this file is therefore

* `step1_point_deriv`: `step1_point` with the two extra outputs `d.φ w = 0` and
  `deriv d.φ w ≠ 0`;
* `setup_exists_v4`: the construction of `setup_exists_v2`, recording in addition the level-0
  point.
-/

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology
open scoped Topology
open LeanEval.Dynamics.MandelbrotBoundary

noncomputable section

/-- **REPEL Step 1, with the extra level-0 outputs.**  The lifted inverse orbit `{w - j}` of the
inverse orbit `{z j}` of `0` avoiding the parabolic basin, together with `d.φ w = 0` (because
`z 0 = 0`) and the non-criticality `deriv d.φ w ≠ 0` (from `ParabData.invOrbit`'s last conjunct,
fed by the non-criticality of the orbit `{z j}` of `f₀`). -/
theorem step1_point_deriv {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : ParabData f₀ D₀) (hd : HornData d)
    (hinf : IsParabolicGerm f₀ D₀)
    (z : ℕ → ℂ) (hz0 : z 0 = 0) (hzrec : ∀ j : ℕ, f₀ (z (j + 1)) = z j)
    (hztend : Tendsto z atTop (nhds 0)) (hzD : ∀ j : ℕ, 1 ≤ j → z j ∈ D₀)
    (hzcrit : ∀ j : ℕ, 1 ≤ j → deriv f₀ (z j) ≠ 0)
    (hzne : ∃ j : ℕ, z j ≠ 0) :
    ∃ w : ℂ, w ∈ d.Dφ ∧ (∀ j : ℕ, w - j ∈ d.Dφ ∧ d.φ (w - j) = z j) ∧
      piExp w ∉ insert 0 (piExp '' (hd.Bu ∪ hd.Bl)) ∧ d.φ w = 0 ∧ deriv d.φ w ≠ 0 := by
  -- Lemma 5.1: the lifted inverse orbit, with the non-criticality clause
  obtain ⟨w, hwDφ, hw, hwcrit⟩ := d.invOrbit z hzD hzrec hztend hzne
  -- `φ w = z 0 = 0`
  have hφw : d.φ w = 0 := by
    have h := (hw 0).2
    rw [hz0] at h
    simpa using h
  have hwderiv : deriv d.φ w ≠ 0 := hwcrit hzcrit
  -- `w ∉ d.DE`, since `0` is not in the parabolic basin
  have hwDE : w ∉ d.DE := by
    intro hmem
    rw [Work.Horn.MandelDim.ParabData.mem_DE] at hmem
    have hb : d.φ w ∈ ParabolicBasin f₀ D₀ := hmem.2
    rw [hφw] at hb
    exact Work.Parab.basinEnters.zero_not_mem_parabolicBasin hinf hb
  refine ⟨w, hwDφ, hw, ?_, hφw, hwderiv⟩
  rw [Set.mem_insert_iff, not_or]
  refine ⟨Work.Horn.MandelDim.piExp_ne_zero w, ?_⟩
  -- a `π`-preimage in `Bu ∪ Bl` would put `w` itself in `Bu ∪ Bl ⊆ d.DE`
  rintro ⟨w', hw', hπ⟩
  obtain ⟨k, hk⟩ := Work.Horn.MandelDim.piExp_eq_iff.mp hπ
  have hT : MandelDim.IsTInvariant (hd.Bu ∪ hd.Bl) := fun v => by
    simp only [Set.mem_union, hd.Bu_T v, hd.Bl_T v]
  have hmem' : w' + ((-k : ℤ) : ℂ) ∈ hd.Bu ∪ hd.Bl :=
    Work.Horn.MandelDim.IsTInvariant.add_int hT hw' (-k)
  have heq : w' + ((-k : ℤ) : ℂ) = w := by
    rw [hk]; push_cast; ring
  exact hwDE (hd.sub (heq ▸ hmem'))

/-- **§6 setup with the level-1 facts AND the level-0 Step-1 point.** -/
theorem setup_exists_v4 (hParab : MandelDim.ParabStatement) (hHorn : MandelDim.HornStatement)
    (hL61 : MandelDim.L61Statement) (hF0 : MandelDim.F0FactsStatement) :
    ∃ S : Work.Repel.Setup, S.ζa ∈ S.d₁.Dφ ∧ deriv S.d₁.φ S.ζa ≠ 0 ∧
      S.ζb ∈ S.d₁.Dφ ∧ deriv S.d₁.φ S.ζb ≠ 0 ∧
      ∃ wt₀ ∈ S.d₀.Dφ, S.d₀.φ wt₀ = 0 ∧ deriv S.d₀.φ wt₀ ≠ 0 ∧
        S.d₁.φ S.ζa = S.s₀ * MandelDim.piExp wt₀ ∧
        S.d₁.φ S.ζb = S.s₀ * MandelDim.piExp wt₀ := by
  -- Step 0: `f₀ = x + x²` is in `𝓕₀` with an inverse orbit `z` of `0` avoiding `-1/2`
  obtain ⟨hF0in, z, hz0, hzrec, hzne, hztend, hzneghalf⟩ := hF0
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
  -- the inverse orbit `z` of `0` is non-critical for `f₀ = x + x²` (it avoids `-1/2`)
  have hzder : ∀ j : ℕ, 1 ≤ j → deriv MandelDim.f0 (z j) ≠ 0 := by
    intro j _ hdj
    apply hzneghalf j
    have h1 : (1 : ℂ) + 2 * z j = 0 := by
      have := hdj
      rw [Work.F0Facts.deriv_f0] at this
      simpa using this
    linear_combination (norm := ring_nf) (1 / 2 : ℂ) * h1
  -- Step 1: the level-0 point `wt₀ = w ∈ d₀.Dφ` with `d₀.φ w = 0`, `deriv d₀.φ w ≠ 0`
  obtain ⟨w, hwDφ, hwinv, hwnd, hφw, hwderiv⟩ :=
    step1_point_deriv d₀ hd₀ hF0in.1 z hz0 hzrec hztend (fun j _ => trivial) hzder
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
  -- non-criticality of `ǧ₀` along the rescaled inverse orbits (Lemma 6.1 transported)
  have hderA : ∀ j, 1 ≤ j → deriv (Work.Repel.g0germ d₀) (Work.Repel.s0 d₀ * wa j) ≠ 0 := by
    intro j hj
    rw [Work.Repel.deriv_g0germ_mul d₀ hd₀ (wa j)]
    have hshift : j - 1 + 1 = j := Nat.succ_pred_eq_of_pos hj
    rw [← hshift]
    exact (hwarec (j - 1)).2.2
  have hderB : ∀ j, 1 ≤ j → deriv (Work.Repel.g0germ d₀) (Work.Repel.s0 d₀ * wb j) ≠ 0 := by
    intro j hj
    rw [Work.Repel.deriv_g0germ_mul d₀ hd₀ (wb j)]
    have hshift : j - 1 + 1 = j := Nat.succ_pred_eq_of_pos hj
    rw [← hshift]
    exact (hwbrec (j - 1)).2.2
  -- Lemma 5.1 at LEVEL 1: the lifted Fatou-coordinate preimages `ζa, ζb`
  obtain ⟨ζa, hζaDφ, hζaprop, hζad⟩ :=
    d₁.invOrbit (fun j => Work.Repel.s0 d₀ * wa j) hvaD hvarec hvatend hvane
  obtain ⟨ζb, hζbDφ, hζbprop, hζbd⟩ :=
    d₁.invOrbit (fun j => Work.Repel.s0 d₀ * wb j) hvbD hvbrec hvbtend hvbne
  -- the two level-1 facts
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
  have hζbderiv : deriv d₁.φ ζb ≠ 0 := hζbd (fun j hj => hderB j hj)
  have hζaφ : d₁.φ ζa = Work.Repel.s0 d₀ * MandelDim.piExp w := by
    have h0 := (hζaprop 0).2
    simpa [hwa0] using h0
  have hζbφ : d₁.φ ζb = Work.Repel.s0 d₀ * MandelDim.piExp w := by
    have h0 := (hζbprop 0).2
    simpa [hwb0] using h0
  exact ⟨{ d₀ := d₀, hd₀ := hd₀, d₁ := d₁, hd₁ := hd₁, s₀ := Work.Repel.s0 d₀,
           hs₀ := rfl, hne := Work.Repel.s0_ne_zero d₀ hd₀, ζa := ζa, ζb := ζb,
           hζa := hζa, hζb := hζb, hdisj := hdisj },
         hζaDφ, hζaderiv, hζbDφ, hζbderiv, w, hwDφ, hφw, hwderiv, hζaφ, hζbφ⟩

end

end Work.Repel
