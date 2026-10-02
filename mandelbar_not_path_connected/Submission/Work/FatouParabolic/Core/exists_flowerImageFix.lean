/-
Copyright: subproject `Submission/Work/FatouParabolic/` of `mandelbar_not_path_connected`.

# `exists_flowerImageFix`: the Leau–Fatou flower with the petal-image (strip) property

`Work.FatouParabolic.FlowerImageFix F g z₀` is the Leau–Fatou flower of a simple parabolic fixed
point `z₀` of `F` (with antiholomorphic square root `g`) together with the *petal image property*
`image_strip`: the image of the attracting petal under the Fatou coordinate `φa` contains the tail
of every horizontal strip.  This is a by-product of the **explicit** construction of the Fatou
coordinate in `Submission/Work/FatouCoord/` (`Work.FatouCoord.Exist.fatouCoordW_image_bdd`), and it
is *not* a consequence of the abstract flower interface (the interface only exports the flower up
to `Classical.choice`, so `φa` is opaque there).

This file therefore re-runs the construction of the repaired flower
(`Work.FatouCoordFix.FlowerFix.germ_parabolicFlowerFix_small` and
`...transfer_parabolicFlowerFix`) keeping the petal and the coordinate visible, and adds the strip
property in the two places where it is produced:

* `petal_image_strip` — the explicit coordinate `fatouCoord f (1 - a)` of the petal
  `Petal r M` (for *any* level `M` above the thresholds, not only the one chosen by
  `exists_petal_fatouCoord`) maps the petal onto the tail of every horizontal strip;
* `exists_phia_pushforward_image` — the orbit-coordinate push-forward of a Fatou coordinate from a
  sub-petal `P ⊆ Pa` to all of `Pa` preserves the strip property (the pushed-forward coordinate
  agrees with `φ₀` on `P`).

The main theorem

`Work.FatouParabolic.Core.exists_flowerImageFix F g z₀ hF hg hgg hfix h1 h2 hgz hδ`

then delivers a flower with the image property whose petal lies in `Metric.ball z₀ δ`.

Everything is a proof, no `sorry`, no new axiom.
-/
import Mathlib
import Submission.Work.FatouParabolic.Core.Defs
import Submission.Work.FatouCoordFix.FlowerFix.ExistsFix
import Submission.Work.FatouCoord.Main

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouParabolic.Core

open scoped Topology
open Set Filter Metric Function
open Work.FatouCoord
open Work.FatouCoord.Flower
open Work.FatouCoordFix.FlowerFix
open Classical

noncomputable section

/-! ## The explicit Fatou coordinate of a petal exhausts strip tails -/

/-- **Petals of *every* level `M ≥ 1` (with `1 / r < M`) have the strip image property** for the
explicit coordinate `fatouCoord f (1 - a)`.  This is the statement
`Work.FatouCoord.Exist.fatouCoordW_image_bdd` transported from the chart `w = -1 / z` to the
petal: the preimage of `τ` constructed there has chart real part `> M`, hence lies in the petal as
soon as `1 / r ≤ M` (so that its modulus exceeds `1 / r`). -/
theorem petal_image_strip {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}
    (hb : ParabolicBounds f h a r A A') {M : ℝ} (hM1 : 1 ≤ M) (hMr : 1 / r < M) :
    ∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, ∀ τ : ℂ, C < τ.re → |τ.im| ≤ B →
      ∃ z ∈ Petal r M, fatouCoord f (1 - a) z = τ := by
  intro B _
  obtain ⟨C, hC⟩ := Work.FatouCoord.Exist.fatouCoordW_image_bdd hb M B
  refine ⟨C, fun τ hτ hτB => ?_⟩
  obtain ⟨w, hw, hψ⟩ := hC τ hτ hτB
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  have hw0 : w ≠ 0 := by
    intro h0
    rw [h0] at hw
    simp at hw
    linarith
  have hwr : 1 / r < ‖w‖ :=
    lt_of_lt_of_le hMr (le_trans (le_of_lt hw) (Complex.re_le_norm w))
  refine ⟨chart w, ?_, ?_⟩
  · rw [chart_mem_Petal_iff hb.hr (chart_ne_zero hw0), chart_chart hw0]
    exact ⟨hw, hwr⟩
  · rw [fatouCoord_eq, chart_chart hw0]
    exact hψ

/-! ## Push-forward of an antiholomorphic Fatou coordinate along the orbit -/

/-- **The push-forward of an antiholomorphic Fatou coordinate, with the value on `Pa` visible.**

This is `Work.FatouCoord.Flower.exists_antiFatou_of_pushforward` with the additional conclusion
that the pushed-forward coordinate agrees with `Φ` on `Pa` (that is what the proof constructs:
on `Pa` the coordinate is `Φ`, off `Pa` it is extended by the forced value
`Φ (gU z) = conj (Φ z) + 1/2`). -/
theorem exists_antiFatou_pushforward_eq {gU Φ : ℂ → ℂ} {Pa : Set ℂ}
    (hanti : Work.FatouCoord.IsAntiholomorphicOn gU Pa)
    (hΦdiff : DifferentiableOn ℂ Φ Pa) (hΦinj : Set.InjOn Φ Pa)
    (hgUinj : Set.InjOn gU Pa)
    (hkey : ∀ z ∈ Pa, gU z ∈ Pa → Φ (gU z) = star (Φ z) + 1 / 2) :
    ∃ φa : ℂ → ℂ, Work.FatouCoord.IsAntiholomorphicFatouOn gU φa Pa ∧ Set.InjOn φa Pa ∧
      ∀ z ∈ Pa, φa z = Φ z := by
  classical
  let φa : ℂ → ℂ := fun z =>
    if hz : z ∈ Pa then Φ z
    else if hzA : z ∈ gU '' Pa then star (Φ (Classical.choose hzA)) + 1 / 2
    else 0
  have hφa_on : ∀ z ∈ Pa, φa z = Φ z := by
    intro z hz
    simp only [φa, dite_eq_left hz]
  have hrel : ∀ z ∈ Pa, φa (gU z) = star (φa z) + 1 / 2 := by
    intro z hz
    rw [hφa_on z hz]
    by_cases hgz : gU z ∈ Pa
    · rw [hφa_on (gU z) hgz, hkey z hz hgz]
    · have hmem : gU z ∈ gU '' Pa := ⟨z, hz, rfl⟩
      simp only [φa, dite_eq_right hgz, dite_eq_left hmem]
      have hspec := Classical.choose_spec hmem
      have hchoose : Classical.choose hmem = z := hgUinj hspec.1 hz hspec.2
      rw [hchoose]
  refine ⟨φa, ⟨hanti, ?_, hrel⟩, ?_, fun z hz => hφa_on z hz⟩
  · exact hΦdiff.congr hφa_on
  · intro a ha b hb hab
    have h1 : φa a = Φ a := hφa_on a ha
    have h2 : φa b = Φ b := hφa_on b hb
    exact hΦinj ha hb (by rw [← h1, ← h2, hab])

/-- **The orbit-coordinate push-forward carries the strip property.**  If the Fatou coordinate
`φ₀` on a sub-petal `P ⊆ Pa` exhausts strip tails, then so does the pushed-forward coordinate on
all of `Pa` (on `P` the pushed-forward coordinate is `φ₀` itself). -/
theorem exists_phia_pushforward_image {f gU φ₀ : ℂ → ℂ} {P Pa : Set ℂ}
    (hf : Differentiable ℂ f)
    (hgU_anti : ∀ z : ℂ, DifferentiableAt ℂ (fun z => star (gU z)) z)
    (hPopen : IsOpen P) (hPmaps : Set.MapsTo f P P)
    (hφ : Work.FatouCoord.IsFatouCoordinateOn f φ₀ P) (hφinj : Set.InjOn φ₀ P)
    (hanti : Work.FatouCoord.IsAntiholomorphicFatouOn gU φ₀ P)
    (hgg : gU ∘ gU = f) (hgU0 : gU 0 = 0)
    (hPamaps : Set.MapsTo f Pa Pa) (hPa0 : (0 : ℂ) ∉ Pa)
    (hPalim : ∀ z ∈ Pa, Filter.Tendsto (fun n : ℕ => f^[n] z) Filter.atTop (nhds 0))
    (hPa_ne : ∀ z ∈ Pa, ∀ n : ℕ, f^[n] z ≠ 0)
    (hfinj : Set.InjOn f Pa)
    (hPentry : ∀ x : ℂ, Filter.Tendsto (fun n : ℕ => f^[n] x) Filter.atTop (nhds 0) →
      (∀ n : ℕ, f^[n] x ≠ 0) → ∃ n : ℕ, f^[n] x ∈ P)
    (hPsub : P ⊆ Pa)
    (hstrip : ∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, ∀ τ : ℂ, C < τ.re → |τ.im| ≤ B →
      ∃ z ∈ P, φ₀ z = τ) :
    ∃ φa : ℂ → ℂ, Work.FatouCoord.IsAntiholomorphicFatouOn gU φa Pa ∧ Set.InjOn φa Pa ∧
      (∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, ∀ τ : ℂ, C < τ.re → |τ.im| ≤ B →
        ∃ z ∈ Pa, φa z = τ) := by
  have hex : ∀ z : ℂ, z ∈ Pa → ∃ n : ℕ, f^[n] z ∈ P :=
    fun z hz => hPentry z (hPalim z hz) (hPa_ne z hz)
  let sel : ℂ → ℕ := fun z =>
    dite (z ∈ Pa) (fun hz => Classical.choose (hex z hz)) (fun _ => 0)
  have hsel : ∀ z : ℂ, z ∈ Pa → f^[sel z] z ∈ P := by
    intro z hz
    have hselz : sel z = Classical.choose (hex z hz) := dite_eq_left hz
    rw [hselz]
    exact Classical.choose_spec (hex z hz)
  have hΦdiff : DifferentiableOn ℂ (orbitCoord f φ₀ P Pa sel) Pa :=
    differentiableOn_orbitCoord hsel hf hPopen hPmaps hφ
  have hΦinj : Set.InjOn (orbitCoord f φ₀ P Pa sel) Pa :=
    injOn_orbitCoord hsel hPmaps hφ hφinj hfinj hPamaps
  have hkey : ∀ z ∈ Pa, gU z ∈ Pa →
      orbitCoord f φ₀ P Pa sel (gU z) = star (orbitCoord f φ₀ P Pa sel z) + 1 / 2 :=
    fun z hz hz' => orbitCoord_map_gU hsel hPmaps hφ hanti hgg hz hz'
  have hantiPa : Work.FatouCoord.IsAntiholomorphicOn gU Pa :=
    fun z _ => (hgU_anti z).differentiableWithinAt
  have hgUinj : Set.InjOn gU Pa := injOn_of_comp_self hgg hfinj
  obtain ⟨φa, hantiφa, hinjφa, hφa_eq⟩ :=
    exists_antiFatou_pushforward_eq hantiPa hΦdiff hΦinj hgUinj hkey
  refine ⟨φa, hantiφa, hinjφa, ?_⟩
  intro B hB
  obtain ⟨C, hC⟩ := hstrip B hB
  refine ⟨C, fun τ hτ hτB => ?_⟩
  obtain ⟨z, hzP, hzτ⟩ := hC τ hτ hτB
  have hzPa : z ∈ Pa := hPsub hzP
  refine ⟨z, hzPa, ?_⟩
  have h0 : orbitCoord f φ₀ P Pa sel z = φ₀ z := by
    have h := orbitCoord_eq_of_mem_iterate (m := 0) hsel hPmaps hφ hzPa (by simpa using hzP)
    simpa using h
  rw [hφa_eq z hzPa, h0, hzτ]

/-! ## The flower germ with the strip property -/

/-- **The Leau–Fatou flower germ, with the petal image property.**  A simple parabolic germ
`f z = z + z ^ 2 * h z` together with an antiholomorphic square root `gU` has a `FlowerImageFix`
at `0` whose petal lies in `ball 0 δ`.  The construction is that of
`Work.FatouCoordFix.FlowerFix.germ_parabolicFlowerFix_small`, but the Fatou coordinate is kept
visible so that the strip property produced by `Work.FatouCoord.Exist.fatouCoordW_image_bdd` can be
attached to it. -/
theorem germ_flowerImageFix_small {f gU h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ} {G₀ ρ δ : ℝ}
    (hf : Differentiable ℂ f) (hb : Work.FatouCoord.ParabolicBounds f h a r A A') (hρ : 0 < ρ) (hρr : ρ ≤ r)
    (hδpos : 0 < δ)
    (hgl : ∀ z : ℂ, ‖z‖ < ρ → ‖gU z - star z‖ ≤ G₀ * ‖z‖ ^ 2)
    (hgU_anti : ∀ z : ℂ, DifferentiableAt ℂ (fun z => star (gU z)) z)
    (hgg : gU ∘ gU = f) (hgU0 : gU 0 = 0) (ha : star a = a) :
    ∃ fl : FlowerImageFix f gU 0,
      fl.toParabolicFlowerFix.Pa ⊆ Metric.ball 0 δ := by
  -- the bounds at the smaller radius
  have hbρ : ParabolicBounds f h a ρ A A' := Work.FatouCoordFix.FlowerFix.gpf_bounds_mono hb hρ hρr
  -- local injectivity of `f` at `0`, in a ball of radius at most `δ` (so that the whole
  -- petal, and hence its half-plane sub-petal, sits in `ball 0 δ`)
  obtain ⟨ε₀, hε₀, hε₀inj⟩ := Work.FatouCoordFix.FlowerFix.gpf_localInjOn hb
  set ε : ℝ := min ε₀ δ with hεdef
  have hε_le_delta : ε ≤ δ := min_le_right _ _
  have hε_le_ε₀ : ε ≤ ε₀ := min_le_left _ _
  have hε : 0 < ε := lt_min hε₀ hδpos
  have hεinj : Set.InjOn f (Metric.ball 0 ε) :=
    hε₀inj.mono (Metric.ball_subset_ball hε_le_ε₀)
  -- the chart conjugacy `V`
  obtain ⟨R, hRpos, hRr, Z, V, hZdiff, hZbd, hVZ, hVdiff, hVshift, hVbd, hVne, hVinj, hVref⟩ :=
    Work.FatouCoord.Flower.Rep.exists_conjugacy hb
  have hZfun : ∀ w : ℂ, w.re < -R → V w - w - (1 - a) * Petal.Lambda w = Z w := by
    intro w hw
    have h1 := hVZ w hw
    rw [h1]; ring
  have hZdiff' : DifferentiableOn ℂ (fun w : ℂ => V w - w - (1 - a) * Petal.Lambda w)
      {w : ℂ | w.re < -R} := hZdiff.congr hZfun
  have hZbd' : ∀ w : ℂ, w.re < -R → ‖V w - w - (1 - a) * Petal.Lambda w‖ ≤ 1 / 2 :=
    fun w hw => by rw [hZfun w hw]; exact hZbd w hw
  have hVinv : ∃ R₁ : ℝ, 0 < R₁ ∧ ∀ Y : ℂ, R₁ ≤ ‖Y‖ →
      (Y - (1 - a) * Petal.Lambda Y).re < -R₁ →
      ∃ x : ℂ, x.re < -R ∧ V x = Y ∧ ‖x - (Y - (1 - a) * Petal.Lambda Y)‖ ≤ 4 :=
    V_preimage hb V hVdiff hZdiff' hZbd' hVinj
  -- the local repelling coordinate and its entire extension
  have hΨ₀coord : IsRepellingCoord f 0 R (Petal.repPsi f V R) :=
    Work.FatouCoordFix.FlowerFix.gpf_isRepellingCoord_repPsi hRpos hVdiff hVshift hVbd hVne hVinj
  set Ψ₀ : ℂ → ℂ := Petal.repPsi f V R with hΨ₀def
  have hΨ₀mem : ∀ u : ℂ, u.re < -R → Ψ₀ u = -1 / V u :=
    fun u hu => Petal.repPsi_of_mem hu
  set Ψb : ℂ → ℂ := EntireRepelling.rΨ f Ψ₀ R with hΨbdef
  have hΨbshift : ∀ w : ℂ, Ψb (w + 1) = f (Ψb w) :=
    fun w => EntireRepelling.rΨ_shift hΨ₀coord.shift
  have hΨbdiff : Differentiable ℂ Ψb :=
    EntireRepelling.rΨ_differentiable hf hΨ₀coord.shift hΨ₀coord.diff
  have hΨbrV : ∀ w : ℂ, Ψb w = -1 / rV f V R w := rΨ_eq_neg_inv_rV hVshift hΨ₀mem
  have hΨb_eq : ∀ w : ℂ, w.re < -R → Ψb w = -1 / V w := by
    intro w hw
    rw [hΨbrV w, rV_eq_of_re_lt hVshift hw]
  have hΨb_ne : ∀ w : ℂ, w.re < -R → Ψb w ≠ 0 := by
    intro w hw
    rw [hΨb_eq w hw]
    exact div_ne_zero (by norm_num) (hVne w hw)
  have hΨbsmall : ∀ ε' : ℝ, 0 < ε' → ∃ R' : ℝ, ∀ w : ℂ, w.re < -R' → ‖Ψb w‖ < ε' := by
    intro ε' hε'
    obtain ⟨R', hR'⟩ := hΨ₀coord.small ε' hε'
    refine ⟨max R' R, fun w hw => ?_⟩
    have hwR : w.re < -R := lt_of_lt_of_le hw (neg_le_neg (le_max_right R' R))
    have hwR' : w.re < -R' := lt_of_lt_of_le hw (neg_le_neg (le_max_left R' R))
    have h3 : Ψb w = Ψ₀ w := (hΨb_eq w hwR).trans (hΨ₀mem w hwR).symm
    rw [h3]
    simpa using hR' w hwR'
  have hΨbinj : ∃ R₀' : ℝ, Set.InjOn Ψb {w : ℂ | w.re < -R₀'} := by
    refine ⟨R, fun a ha b hb' hab => ?_⟩
    exact hΨ₀coord.inj ha hb' (by
      rw [← EntireRepelling.rΨ_eq_Ψ₀ hΨ₀coord.shift ha,
        ← EntireRepelling.rΨ_eq_Ψ₀ hΨ₀coord.shift hb']
      exact hab)
  -- the antiholomorphic shift constant
  obtain ⟨c, hc_real, hc_anti⟩ :=
    exists_anti_shift (f := f) (gU := gU) (h := h) (a := a) (r := r) hb hgU_anti hgg hgU0 ha
      (R := R) (V := V) hRr hVdiff hVshift hVbd hVref hVinj hVinv
      (Ψ := Ψb) hΨbdiff hΨbshift hΨb_eq
  have hcre : c.re = 0 := by
    have h := congrArg Complex.re hc_real
    simp at h
    linarith
  have hc_re : ∀ w : ℂ, (w + c).re = w.re := by
    intro w
    simp [Complex.add_re, hcre]
  -- the shifted repelling coordinate
  set Ψ : ℂ → ℂ := fun w => Ψb (w + c) with hΨdef
  have hΨ_shift : ∀ w : ℂ, Ψ (w + 1) = f (Ψ w) := by
    intro w
    have h1 : (w + 1) + c = (w + c) + 1 := by ring
    show Ψb ((w + 1) + c) = f (Ψb (w + c))
    rw [h1, hΨbshift]
  have hΨ_anti : ∀ w : ℂ, Ψ (star w + 1 / 2) = gU (Ψ w) := by
    intro w
    exact hc_anti w
  have hΨ_diff : Differentiable ℂ Ψ := hΨbdiff.comp (differentiable_id.add_const c)
  have hΨ_rV : ∀ w : ℂ, Ψ w = -1 / rV f V R (w + c) := fun w => hΨbrV (w + c)
  have hΨ_small : ∀ ε' : ℝ, 0 < ε' → ∃ R' : ℝ, ∀ w : ℂ,
      w.re < -R' → Ψ w ≠ 0 ∧ ‖Ψ w - 0‖ < ε' := by
    intro ε' hε'
    obtain ⟨R', hR'⟩ := hΨbsmall ε' hε'
    refine ⟨max R' R, fun w hw => ?_⟩
    have hwR : w.re < -R := lt_of_lt_of_le hw (neg_le_neg (le_max_right R' R))
    have hwR' : w.re < -R' := lt_of_lt_of_le hw (neg_le_neg (le_max_left R' R))
    have h1 : ‖Ψb (w + c)‖ < ε' := by
      refine hR' (w + c) ?_
      rw [hc_re]; exact hwR'
    have h2 : Ψb (w + c) ≠ 0 := hΨb_ne (w + c) (by rw [hc_re]; exact hwR)
    have h1' : ‖Ψ w - 0‖ < ε' := by
      show ‖Ψb (w + c) - 0‖ < ε'
      rwa [sub_zero]
    exact ⟨h2, h1'⟩
  have hΨ_inj : ∃ R₀' : ℝ, Set.InjOn Ψ {w : ℂ | w.re < -R₀'} := by
    obtain ⟨R₀', hR₀'⟩ := hΨbinj
    refine ⟨R₀', fun a ha b hb' hab => ?_⟩
    have ha' : (a + c).re < -R₀' := by rw [hc_re]; exact ha
    have hb'' : (b + c).re < -R₀' := by rw [hc_re]; exact hb'
    exact add_right_cancel (hR₀' ha' hb'' hab)
  -- ### thresholds
  obtain ⟨M₀w, hgr⟩ := Work.FatouCoordFix.FlowerFix.gpf_widePetal_growth_mono hb
  obtain ⟨Mpet, _hMpetpos, hMpet_maps, hMpet_lim, hMpet_fatou, hMpet_inj, _hMpet_img⟩ :=
    exists_petal_fatouCoord hbρ
  obtain ⟨M₀p, hM₀p⟩ := Petal.petal_mapsTo_tendsto_of_le hbρ
  obtain ⟨Manti, s, _hMantipos, hAntiF, hAntiInj⟩ :=
    Anti.antiholomorphic_fatou_real (g := gU) hbρ ha (fun z _ => hgU_anti z)
      (fun z _ => congrFun hgg z) hgU0 (fun z hz => hgl z (mem_ball_zero_iff.mp hz))
  have hAntiF' : IsAntiholomorphicFatouOn gU (fun z => fatouCoord f (1 - a) z + s)
      (Petal ρ Manti) := hAntiF
  have hAntiInj' : Set.InjOn (fun z => fatouCoord f (1 - a) z + s) (Petal ρ Manti) := hAntiInj
  set δinv : ℝ := 1 / ε with hδinvdef
  have hδinv_pos : 0 < δinv := by rw [hδinvdef]; exact one_div_pos.mpr hε
  have hδ : ε * δinv = 1 := by rw [hδinvdef]; field_simp
  set Ms : ℝ := max (max (max M₀w (1 / ρ + 1)) (Real.sqrt 2 * δinv + 1)) 1 with hMsdef
  have hMs_1 : 1 ≤ Ms := le_max_right _ _
  have hMs_pos : 0 < Ms := lt_of_lt_of_le one_pos hMs_1
  have hMs_ge_M₀w : M₀w ≤ Ms :=
    (le_max_left M₀w (1 / ρ + 1)).trans
      ((le_max_left (max M₀w (1 / ρ + 1)) (Real.sqrt 2 * δinv + 1)).trans (le_max_left _ _))
  have hMs_ρ' : 1 / ρ + 1 ≤ Ms :=
    (le_max_right M₀w (1 / ρ + 1)).trans
      ((le_max_left (max M₀w (1 / ρ + 1)) (Real.sqrt 2 * δinv + 1)).trans (le_max_left _ _))
  have hMs_sqrt : Real.sqrt 2 * δinv + 1 ≤ Ms :=
    (le_max_right (max M₀w (1 / ρ + 1)) (Real.sqrt 2 * δinv + 1)).trans (le_max_left _ _)
  have hMs_ρ : 1 / ρ < Ms := lt_of_lt_of_le (by linarith) hMs_ρ'
  have hMs_sqrt' : Real.sqrt 2 * δinv ≤ Ms :=
    le_trans (le_add_of_nonneg_right zero_le_one) hMs_sqrt
  set M : ℝ := max (max (max Ms Mpet) (max M₀p Manti)) 1 with hMdef
  have hM_1 : 1 ≤ M := le_max_right _ _
  have hM_Ms : Ms ≤ M :=
    (le_max_left Ms Mpet).trans
      ((le_max_left (max Ms Mpet) (max M₀p Manti)).trans (le_max_left _ _))
  have hM_Mpet : Mpet ≤ M :=
    (le_max_right Ms Mpet).trans
      ((le_max_left (max Ms Mpet) (max M₀p Manti)).trans (le_max_left _ _))
  have hM_M₀p : M₀p ≤ M :=
    (le_max_left M₀p Manti).trans
      ((le_max_right (max Ms Mpet) (max M₀p Manti)).trans (le_max_left _ _))
  have hM_Manti : Manti ≤ M :=
    (le_max_right M₀p Manti).trans
      ((le_max_right (max Ms Mpet) (max M₀p Manti)).trans (le_max_left _ _))
  have hM_ρ : 1 / ρ < M := lt_of_lt_of_le hMs_ρ hM_Ms
  have hgrMs : ∀ W : ℂ, Ms < sgauge W →
      Ms < sgauge (wMap f W) ∧ (wMap f W).re ≥ W.re + 1 / 2 := hgr Ms hMs_ge_M₀w
  -- ### the Fatou coordinate on the petal
  have hW6 := Work.FatouCoord.Flower.WPA.widePetal_props hbρ hMs_1 hMs_ρ hgrMs
  have hWide : IsOpen (WidePetal Ms) ∧ IsPreconnected (WidePetal Ms) ∧ (0 : ℂ) ∉ WidePetal Ms ∧
      MapsTo f (WidePetal Ms) (WidePetal Ms) ∧
      (∀ u ∈ WidePetal Ms, Tendsto (fun n : ℕ => f^[n] u) atTop (nhds 0)) :=
    ⟨hW6.1, hW6.2.1, hW6.2.2.1, hW6.2.2.2.1, hW6.2.2.2.2.1⟩
  have hWide_ball : WidePetal Ms ⊆ ball 0 ε :=
    le_trans hW6.2.2.2.2.2 (ball_subset_ball (by
      rw [div_le_iff₀ hMs_pos]
      have h2 : ε * (Real.sqrt 2 * δinv) ≤ ε * Ms := mul_le_mul_of_nonneg_left hMs_sqrt' hε.le
      have h3 : ε * (Real.sqrt 2 * δinv) = Real.sqrt 2 := by
        rw [← mul_assoc, mul_comm ε (Real.sqrt 2), mul_assoc, hδ, mul_one]
      linarith))
  -- the petal sits inside the wide petal
  have hsub_petal : Petal ρ M ⊆ WidePetal Ms := by
    intro z hz
    have hz0 : z ≠ 0 := ne_zero_of_mem_Petal hz
    have hns : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz0
    rw [mem_WidePetal]
    refine ⟨hz0, ?_⟩
    have h1 : Ms < ((-1 : ℂ) / z).re := by
      show Ms < (chart z).re
      rw [re_chart hz0, lt_div_iff₀ hns]
      have h2 := hz.2
      have h3 : Ms ≤ M := hM_Ms
      nlinarith [h2, hns, h3]
    have h2 : ((-1 : ℂ) / z).re ≤ sgauge ((-1 : ℂ) / z) := by
      rw [sgauge]
      have := abs_nonneg (((-1 : ℂ) / z).im)
      linarith
    linarith
  -- the Fatou coordinate pushed forward from a half-plane petal
  have hsub_M : Petal ρ M ⊆ Petal ρ Mpet := Petal_mono le_rfl hM_Mpet
  have hsub_Ma : Petal ρ M ⊆ Petal ρ Manti := Petal_mono le_rfl hM_Manti
  have hφ : IsFatouCoordinateOn f (fun z => fatouCoord f (1 - a) z + s) (Petal ρ M) := by
    refine ⟨(hMpet_fatou.1.mono hsub_M).add_const s, fun z hz => ?_⟩
    have h1 := hMpet_fatou.2 z (hsub_M hz)
    show fatouCoord f (1 - a) (f z) + s = (fatouCoord f (1 - a) z + s) + 1
    rw [h1]; ring
  have hφinj : Set.InjOn (fun z => fatouCoord f (1 - a) z + s) (Petal ρ M) := by
    intro x hx y hy hxy
    exact hMpet_inj (hsub_M hx) (hsub_M hy) (add_right_cancel hxy)
  have hanti : IsAntiholomorphicFatouOn gU (fun z => fatouCoord f (1 - a) z + s) (Petal ρ M) :=
    ⟨hAntiF'.1.mono hsub_Ma, hAntiF'.2.1.mono hsub_Ma,
      fun z hz => hAntiF'.2.2 z (hsub_Ma hz)⟩
  have hPmaps : MapsTo f (Petal ρ M) (Petal ρ M) := (hM₀p M hM_M₀p).1
  have hPentry : ∀ x : ℂ, Tendsto (fun n : ℕ => f^[n] x) atTop (nhds 0) →
      (∀ n : ℕ, f^[n] x ≠ 0) → ∃ n : ℕ, f^[n] x ∈ Petal ρ M :=
    exists_iterate_mem_Petal hbρ hMs_1 hMs_ρ hgrMs hM_1 hM_ρ
  -- ### the window thresholds
  have hR₀_ge : R + 1 ≤ R + 1 := le_refl _
  obtain ⟨T₁, hT₁pos, hT₁⟩ :=
    rV_window hb V hVdiff hVshift hVbd hVref (M := Ms) (R₀ := R + 1) (le_of_lt hMs_pos) hR₀_ge
  obtain ⟨T₂, hT₂pos, hT₂⟩ := rV_tendsto_atTop hb hRpos hRr V hVshift hVbd
  set T : ℝ := max (max (T₁ + |c.im| + 1) (T₂ + |c.im| + 1))
      (max (|c.im| + 2 * δinv + 1) 1) with hTdef
  have hT_pos : 0 < T :=
    lt_of_lt_of_le one_pos
      ((le_max_right (|c.im| + 2 * δinv + 1) 1).trans (le_max_right _ _))
  have hT₁_le : T₁ + |c.im| ≤ T := by
    have h : T₁ + |c.im| + 1 ≤ T :=
      (le_max_left (T₁ + |c.im| + 1) (T₂ + |c.im| + 1)).trans (le_max_left _ _)
    linarith
  have hT₂_le : T₂ + |c.im| ≤ T := by
    have h : T₂ + |c.im| + 1 ≤ T :=
      (le_max_right (T₁ + |c.im| + 1) (T₂ + |c.im| + 1)).trans (le_max_left _ _)
    linarith
  have hTδ_le : |c.im| + 2 * δinv ≤ T := by
    have h : |c.im| + 2 * δinv + 1 ≤ T :=
      (le_max_left (|c.im| + 2 * δinv + 1) 1).trans (le_max_right _ _)
    linarith
  -- the "large imaginary part" bounds
  have him_ge : ∀ w : ℂ, |w.im| - |c.im| ≤ |(w + c).im| := by
    intro w
    have h1 : (w + c).im = w.im + c.im := by simp
    rw [h1]
    have h3 : |(w.im + c.im) - c.im| ≤ |w.im + c.im| + |c.im| := abs_sub _ _
    have h4 : (w.im + c.im) - c.im = w.im := by ring
    rw [h4] at h3
    linarith
  -- ### `Pa`
  set Pa : Set ℂ := WidePetal Ms ∪ Ψ '' {w : ℂ | w.re < -(R + 1) ∧ T < |w.im|} with hPadef
  have hne : ∀ w : ℂ, w.re < -(R + 1) → T < |w.im| → Ψ w ≠ 0 := by
    intro w hw1 _hw2 h0
    have hwre : (w + c).re < -R := by
      have := hc_re w
      rw [this] at *
      linarith
    have hwave : Ψ w = -1 / V (w + c) := by rw [hΨ_rV w, rV_eq_of_re_lt hVshift hwre]
    rw [hwave] at h0
    rcases div_eq_zero_iff.mp h0 with h | h
    · norm_num at h
    · exact hVne (w + c) hwre h
  have hwin : ∀ w : ℂ, -(R + 1) - 1 ≤ w.re → w.re < -(R + 1) + 1 → T < |w.im| →
      Ψ w ∈ WidePetal Ms := by
    intro w h1 h2 h3
    have h1' : -(R + 1) - 1 ≤ (w + c).re := by rw [hc_re]; exact h1
    have h2' : (w + c).re < -(R + 1) + 1 := by rw [hc_re]; exact h2
    have h3' : T₁ < |(w + c).im| := by
      have := him_ge w
      linarith
    obtain ⟨hne', hsg⟩ := hT₁ (w + c) h1' h2' h3'
    rw [hΨ_rV w, mem_WidePetal]
    refine ⟨?_, ?_⟩
    · intro h0
      rcases div_eq_zero_iff.mp h0 with h | h
      · norm_num at h
      · exact hne' h
    · rw [neg_one_div_neg_one_div]
      exact hsg
  have hlim : ∀ w : ℂ, w.re < -(R + 1) → T < |w.im| →
      Tendsto (fun n : ℕ => f^[n] (Ψ w)) atTop (nhds 0) := by
    intro w _hw1 hw2
    have him : T₂ < |(w + c).im| := by
      have := him_ge w
      linarith
    have hten := hT₂ (w + c) him
    have h1 : Tendsto (fun n : ℕ => ((‖rV f V R ((w + c) + (n : ℂ))‖ : ℝ))⁻¹) atTop (nhds 0) :=
      hten.inv_tendsto_atTop
    have h2 : Tendsto (fun n : ℕ => Ψb (w + c + (n : ℂ))) atTop (nhds 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have heq : (fun n : ℕ => ‖Ψb (w + c + (n : ℂ))‖)
          = fun n : ℕ => (‖rV f V R (w + c + (n : ℂ))‖)⁻¹ := by
        funext n
        have hA : Ψb (w + c + (n : ℂ)) = (-1 : ℂ) / rV f V R (w + c + (n : ℂ)) := hΨbrV _
        rw [hA, norm_div, norm_neg, norm_one, one_div]
      rw [heq]
      exact h1
    have h3 : (fun n : ℕ => f^[n] (Ψ w)) = fun n : ℕ => Ψb (w + c + (n : ℂ)) := by
      funext n
      show f^[n] (Ψb (w + c)) = Ψb (w + c + (n : ℂ))
      exact (Psi_add_nat hΨbshift n (w + c)).symm
    rw [h3]
    exact h2
  obtain ⟨hPa_open, hPa_pre, hPa_zero, hPa_maps, hPa_tend⟩ :=
    Pa_basic hΨ_diff (by
      have han : AnalyticOnNhd ℂ Ψ Set.univ := hΨ_diff.differentiableOn.analyticOnNhd isOpen_univ
      rcases han.is_constant_or_isOpenMap with hcst | hop
      · exfalso
        obtain ⟨k, hk⟩ := hcst
        obtain ⟨R₀', hR₀'⟩ := hΨ_inj
        have h1 : Ψ (((-R₀' - 1 : ℝ)) : ℂ) = Ψ (((-R₀' - 2 : ℝ)) : ℂ) := by rw [hk, hk]
        have h2 : (((-R₀' - 1 : ℝ)) : ℂ) = (((-R₀' - 2 : ℝ)) : ℂ) :=
          hR₀' (by simp [Complex.ofReal_re]) (by simp [Complex.ofReal_re]) h1
        have h3 : (-R₀' - 1 : ℝ) = (-R₀' - 2 : ℝ) := Complex.ofReal_injective h2
        linarith
      · exact hop)
      hPadef hne hWide hwin hΨ_shift hlim
  -- `Pa` is small, so `f` is injective on it
  have hPa_ball : Pa ⊆ ball 0 ε := by
    intro z hz
    rcases hz with hz | ⟨w, hw, rfl⟩
    · exact hWide_ball hz
    · rw [mem_ball_zero_iff]
      have hwre : (w + c).re < -R := by
        have := hc_re w
        rw [this] at *
        linarith [hw.1]
      have hwave : Ψ w = -1 / V (w + c) := by rw [hΨ_rV w, rV_eq_of_re_lt hVshift hwre]
      rw [hwave]
      have hV2 : ‖w + c‖ / 2 ≤ ‖V (w + c)‖ := by
        have h3 := hVbd (w + c) hwre
        have h4 : ‖w + c‖ ≤ ‖V (w + c)‖ + ‖V (w + c) - (w + c)‖ := by
          calc ‖w + c‖ = ‖V (w + c) - (V (w + c) - (w + c))‖ := by ring_nf
            _ ≤ ‖V (w + c)‖ + ‖V (w + c) - (w + c)‖ := norm_sub_le _ _
        linarith
      have hbig : 2 * δinv < ‖w + c‖ := by
        have h5 : |c.im| + 2 * δinv < |w.im| := by linarith [hTδ_le, hw.2]
        have h6 : |w.im| - |c.im| ≤ |(w + c).im| := him_ge w
        have h7 : |(w + c).im| ≤ ‖w + c‖ := Complex.abs_im_le_norm _
        linarith
      have hVpos : 0 < ‖V (w + c)‖ := by linarith
      have h3 : δinv < ‖V (w + c)‖ := by linarith
      have h4 : ε * δinv < ε * ‖V (w + c)‖ := mul_lt_mul_of_pos_left h3 hε
      rw [norm_div, norm_neg, norm_one, div_lt_iff₀ hVpos]
      linarith
  have hfinj : Set.InjOn f Pa := fun x hx y hy hxy => hεinj (hPa_ball hx) (hPa_ball hy) hxy
  have hPa_ne : ∀ z ∈ Pa, ∀ n : ℕ, f^[n] z ≠ 0 := by
    intro z hz n hn
    have hmem : (0 : ℂ) ∈ Pa := by
      rw [← hn]
      exact mapsTo_iterate_of_mapsTo hPa_maps n hz
    exact hPa_zero hmem
  -- ### the antiholomorphic Fatou coordinate on `Pa`
  have hstrip₀ : ∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, ∀ τ : ℂ, C < τ.re → |τ.im| ≤ B →
      ∃ z ∈ Petal ρ M, fatouCoord f (1 - a) z + s = τ := by
    intro B hB
    obtain ⟨C, hC⟩ := petal_image_strip hbρ hM_1 hM_ρ (B + |s.im|) (by positivity)
    refine ⟨C + s.re, fun τ hτ hτB => ?_⟩
    have him : |(τ - s).im| ≤ B + |s.im| := by
      have h1 : (τ - s).im = τ.im - s.im := by simp
      rw [h1]
      calc |τ.im - s.im| ≤ |τ.im| + |s.im| := abs_sub _ _
        _ ≤ B + |s.im| := by linarith
    have hre : C < (τ - s).re := by
      have h1 : (τ - s).re = τ.re - s.re := by simp
      rw [h1]; linarith
    obtain ⟨z, hzP, hz⟩ := hC (τ - s) hre him
    exact ⟨z, hzP, by rw [hz]; ring⟩
  have hPsub : Petal ρ M ⊆ Pa := fun z hz => Or.inl (hsub_petal hz)
  obtain ⟨φa, hφa_anti, hφa_inj, hφa_strip⟩ :=
    exists_phia_pushforward_image (f := f) (gU := gU) (φ₀ := fun z => fatouCoord f (1 - a) z + s)
      (P := Petal ρ M) (Pa := Pa) hf hgU_anti isOpen_Petal hPmaps hφ hφinj hanti hgg hgU0
      hPa_maps hPa_zero hPa_tend hPa_ne hfinj hPentry hPsub hstrip₀
  -- ### the remaining fields
  have hΨ_ends : ∃ R₀' : ℝ, ∀ w : ℂ, w.re < -R₀' → R₀' < |w.im| → Ψ w ∈ Pa := by
    refine ⟨max (R + 1) T, fun w hw1 hw2 => ?_⟩
    have h1 : w.re < -(R + 1) := by
      have : (R + 1) ≤ max (R + 1) T := le_max_left _ _
      linarith
    have h2 : T < |w.im| := lt_of_le_of_lt (le_max_right (R + 1) T) hw2
    exact Or.inr ⟨w, ⟨h1, h2⟩, rfl⟩
  have hcover : ∀ Rpar : ℝ, ∃ rr : ℝ, 0 < rr ∧ ∀ z : ℂ, 0 < ‖z - 0‖ → ‖z - 0‖ < rr →
      z ∈ Pa ∨ ∃ w : ℂ, w.re < -Rpar ∧ Ψ w = z := by
    intro Rpar
    obtain ⟨rr, hrr, hspec⟩ :=
      Psi_cover hbρ V hVshift hVinv hMs_1 hMs_ρ hc_real hΨ_rV Rpar
    refine ⟨rr, hrr, fun z hz0 hzlt => ?_⟩
    rcases hspec z (by simpa using hz0) (by simpa using hzlt) with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
  have hEnter : ∀ z : ℂ, Tendsto (fun n : ℕ => f^[n] z) atTop (nhds 0) →
      (∀ n : ℕ, f^[n] z ≠ 0) → ∃ n : ℕ, f^[n] z ∈ Pa := by
    intro z ht hnz
    obtain ⟨n, hn⟩ := hPentry z ht hnz
    exact ⟨n, Or.inl (hsub_petal hn)⟩
  -- ### the `gU`-invariant half-plane sub-petal `Pg`
  -- The chart dynamics of `gU` grows the real part by at least `1/4` past a threshold, and the
  -- chart dynamics of `f` grows it by at least `1/2` past `M₀w`.  Taking the level `Mh` above
  -- both thresholds and above `1/δ` makes `HPlanePetal Mh` a small `f`- and `gU`-invariant
  -- sub-petal of `Pa`.
  obtain ⟨Mgr, hMgr_nn, hgrG⟩ :=
    Work.FatouCoordFix.FlowerFix.gChart_re_growth hbρ hgU_anti hgg hgU0
  set Mh : ℝ := max (max M₀w Mgr) (max (Ms + 1) (1 / δ + 1)) with hMhdef
  have hMh_M₀w : M₀w ≤ Mh := le_trans (le_max_left _ _) (le_max_left _ _)
  have hMh_Mgr : Mgr ≤ Mh := le_trans (le_max_right _ _) (le_max_left _ _)
  have hMh_Ms : Ms + 1 ≤ Mh := le_trans (le_max_left _ _) (le_max_right _ _)
  have hMh_δ : 1 / δ + 1 ≤ Mh := le_trans (le_max_right _ _) (le_max_right _ _)
  have hMs_lt_Mh : Ms < Mh := by linarith
  have hMh_nn : 0 ≤ Mh := le_trans hMgr_nn hMh_Mgr
  set Pg : Set ℂ := Work.FatouCoordFix.HPlanePetal Mh with hPgdef
  have hPg_sub : Pg ⊆ Pa := by
    rw [hPgdef]
    intro u hu
    rw [hPadef]
    exact Or.inl (Work.FatouCoordFix.HPetal.HPlanePetal_subset_WidePetal (le_of_lt hMs_lt_Mh) hu)
  have hPg_open : IsOpen Pg := by
    rw [hPgdef]; exact Work.FatouCoordFix.HPetal.HPlanePetal_isOpen Mh
  have hPg_ne : Pg.Nonempty := by
    rw [hPgdef]; exact Work.FatouCoordFix.HPetal.HPlanePetal_nonempty Mh
  have hPg_pre : IsPreconnected Pg := by
    rw [hPgdef]; exact Work.FatouCoordFix.HPetal.HPlanePetal_preconnected hMh_nn
  have hPg_Fmaps : MapsTo f Pg Pg := by
    rw [hPgdef]
    refine Work.FatouCoordFix.HPetal.HPlanePetal_mapsTo_wMap hMh_nn (fun W hW => ?_)
    have h1 := (hgr Mh hMh_M₀w W (lt_of_lt_of_le hW (le_add_of_nonneg_right (abs_nonneg W.im)))).2
    linarith
  have hPg_gmaps : MapsTo gU Pg Pg := by
    rw [hPgdef]
    refine Work.FatouCoordFix.HPetal.HPlanePetal_mapsTo_gChart hMh_nn (fun W hW => ?_)
    have h := hgrG W (lt_of_le_of_lt hMh_Mgr hW)
    linarith
  have hPg_enters : ∀ z : ℂ, Tendsto (fun n : ℕ => f^[n] z) atTop (nhds 0) →
      (∀ n : ℕ, f^[n] z ≠ 0) → ∃ n : ℕ, f^[n] z ∈ Pg := by
    intro z ht hne
    obtain ⟨n₀, hn₀⟩ := hPentry z ht hne
    have h1 : f^[n₀] z ∈ WidePetal M :=
      Work.FatouCoordFix.HPetal.Petal_subset_WidePetal (by linarith) hn₀
    obtain ⟨k, hk⟩ := Work.FatouCoordFix.HPetal.exists_iterate_mem_HPlanePetal
      (f := f) (M := Mh) (M' := M) (hgr M (le_trans hMs_ge_M₀w hM_Ms)) h1
    refine ⟨n₀ + k, ?_⟩
    have h2 : f^[n₀ + k] z = f^[k] (f^[n₀] z) :=
      (Function.iterate_add_apply f n₀ k z).trans (Work.FatouCoord.iterate_comm f k n₀ z).symm
    rw [h2]
    exact hk
  have hφa_shift : ∀ z ∈ Pa, φa (f z) = φa z + 1 :=
    Work.FatouCoordFix.φa_shift_of_halfPetal hPa_open hPa_pre hPg_open hPg_ne hPg_sub
      hφa_anti.2.1 hf hPa_maps hgg hPg_gmaps (fun z hz => hφa_anti.2.2 z (hPg_sub hz))
  have hPa_ball_δ : Pa ⊆ Metric.ball 0 δ :=
    le_trans hPa_ball (Metric.ball_subset_ball hε_le_delta)
  refine ⟨⟨⟨{
    Pa := Pa
    φa := φa
    Ψ := Ψ
    isOpen_Pa := hPa_open
    isPreconnected_Pa := hPa_pre
    z₀_not_mem := hPa_zero
    mapsTo_Pa := hPa_maps
    tendsto_Pa := hPa_tend
    enters_Pa := hEnter
    φa_fatou := ⟨hφa_anti, hφa_inj⟩
    Ψ_diff := hΨ_diff
    Ψ_shift := hΨ_shift
    Ψ_anti := hΨ_anti
    Ψ_small := hΨ_small
    Ψ_inj := hΨ_inj
    Ψ_ends := hΨ_ends
    cover := hcover },
    Pg, hPg_sub, hPg_open, hPg_ne, hPg_pre, hPg_Fmaps, hPg_gmaps, hPg_enters, hφa_shift⟩,
    hφa_strip⟩, hPa_ball_δ⟩

/-- **The flower, with its image property, transfers along an affine chart.**  This is
`Work.FatouCoordFix.FlowerFix.transfer_parabolicFlowerFix` for a `FlowerImageFix`: the petal is
carried along by `u ↦ z₀ + lam * u` and the coordinate is composed with the inverse chart, so the
image property is transported verbatim. -/
theorem transfer_flowerImageFix {F g f gU : ℂ → ℂ} {z₀ lam : ℂ} {δ : ℝ} (hlam : lam ≠ 0)
    (hg_anti : ∀ z : ℂ, DifferentiableAt ℂ (fun z => star (g z)) z)
    (hFf : ∀ u : ℂ, F (z₀ + lam * u) = z₀ + lam * f u)
    (hGg : ∀ u : ℂ, g (z₀ + lam * u) = z₀ + lam * gU u)
    (hδ : 0 < δ)
    (h : FlowerImageFix f gU 0)
    (hPa_small : h.toParabolicFlowerFix.Pa ⊆ Metric.ball 0 (δ / ‖lam‖)) :
    ∃ fl : FlowerImageFix F g z₀, fl.toParabolicFlowerFix.Pa ⊆ Metric.ball z₀ δ := by
  have hFf' : ∀ u : ℂ, F (trChart z₀ lam u) = trChart z₀ lam (f u) := fun u => hFf u
  have hGg' : ∀ u : ℂ, g (trChart z₀ lam u) = trChart z₀ lam (gU u) := fun u => hGg u
  have hnorm : 0 < ‖lam‖ := norm_pos_iff.mpr hlam
  refine ⟨⟨⟨{
    Pa := trChart z₀ lam '' h.Pa
    φa := fun z => h.φa (trChartInv z₀ lam z)
    Ψ := fun w => trChart z₀ lam (h.Ψ w)
    isOpen_Pa := ?_
    isPreconnected_Pa := ?_
    z₀_not_mem := ?_
    mapsTo_Pa := ?_
    tendsto_Pa := ?_
    enters_Pa := ?_
    φa_fatou := ?_
    Ψ_diff := ?_
    Ψ_shift := ?_
    Ψ_anti := ?_
    Ψ_small := ?_
    Ψ_inj := ?_
    Ψ_ends := ?_
    cover := ?_ }, trChart z₀ lam '' h.Pg, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  -- `Pa` is open, being the preimage of the open `Pa` of `h` under the continuous inverse chart
  · rw [show trChart z₀ lam '' h.Pa = trChartInv z₀ lam ⁻¹' h.Pa from by
        ext z; exact mem_trChart_image hlam]
    exact h.isOpen_Pa.preimage (continuous_trChartInv z₀ lam)
  -- `Pa` is preconnected, being the image of the preconnected `Pa` of `h`
  · exact h.isPreconnected_Pa.image _ (continuous_trChart z₀ lam).continuousOn
  -- the centre of the flower of `h` is `0`, which is not in `h.Pa`
  · intro hmem
    rw [mem_trChart_image hlam] at hmem
    have h0 : trChartInv z₀ lam z₀ = 0 := by simp [trChartInv]
    rw [h0] at hmem
    exact h.z₀_not_mem hmem
  · rintro z ⟨u, hu, rfl⟩
    rw [hFf']
    exact ⟨f u, h.mapsTo_Pa hu, rfl⟩
  -- orbits in the new petal converge to `z₀`, by continuity of the chart
  · rintro z ⟨u, hu, rfl⟩
    have hiter : ∀ n : ℕ, F^[n] (trChart z₀ lam u) = trChart z₀ lam (f^[n] u) :=
      fun n => iterate_trChart hFf' u n
    have h1 : Tendsto (fun v : ℂ => trChart z₀ lam v) (nhds 0) (nhds (trChart z₀ lam 0)) :=
      (continuous_trChart z₀ lam).tendsto 0
    have h2 : trChart z₀ lam (0 : ℂ) = z₀ := by simp [trChart]
    rw [h2] at h1
    exact Tendsto.congr (fun n => (hiter n).symm) (h1.comp (h.tendsto_Pa u hu))
  -- an orbit converging to `z₀` and avoiding it is, in the chart, an orbit converging to `0`
  -- and avoiding it, hence eventually enters the petal
  · intro z hzlim hzne
    set u := trChartInv z₀ lam z with hu
    have hz_eq : z = trChart z₀ lam u := by rw [hu]; exact (trChart_trChartInv hlam z).symm
    have hiter : ∀ n : ℕ, F^[n] z = trChart z₀ lam (f^[n] u) := by
      intro n; rw [hz_eq]; exact iterate_trChart hFf' u n
    have hlim : Tendsto (fun n : ℕ => f^[n] u) atTop (nhds 0) := by
      have h1 : Tendsto (fun n : ℕ => trChartInv z₀ lam (F^[n] z)) atTop
          (nhds (trChartInv z₀ lam z₀)) :=
        ((continuous_trChartInv z₀ lam).tendsto z₀).comp hzlim
      have h2 : trChartInv z₀ lam z₀ = 0 := by simp [trChartInv]
      rw [h2] at h1
      refine Tendsto.congr (fun n => ?_) h1
      rw [hiter n, trChartInv_trChart hlam]
    have hne' : ∀ n : ℕ, f^[n] u ≠ 0 := by
      intro n h0
      refine hzne n ?_
      rw [hiter n, h0]
      simp [trChart]
    obtain ⟨n, hn⟩ := h.enters_Pa u hlim hne'
    exact ⟨n, by rw [hiter n]; exact ⟨f^[n] u, hn, rfl⟩⟩
  · refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · exact fun z _ => (hg_anti z).differentiableWithinAt
    · exact h.φa_fatou.1.2.1.comp (differentiable_trChartInv z₀ lam).differentiableOn
        (fun z hz => (mem_trChart_image hlam).mp hz)
    · intro z hz
      obtain ⟨u, hu, rfl⟩ := hz
      show h.φa (trChartInv z₀ lam (g (trChart z₀ lam u))) =
        star (h.φa (trChartInv z₀ lam (trChart z₀ lam u))) + 1 / 2
      rw [hGg', trChartInv_trChart hlam, trChartInv_trChart hlam]
      exact h.φa_fatou.1.2.2 u hu
    · intro a ha b hb hab
      have h1 := h.φa_fatou.2 ((mem_trChart_image hlam).mp ha)
        ((mem_trChart_image hlam).mp hb) hab
      have h2 := congrArg (trChart z₀ lam) h1
      rwa [trChart_trChartInv hlam, trChart_trChartInv hlam] at h2
  · exact (differentiable_trChart z₀ lam).comp h.Ψ_diff
  · intro w
    rw [h.Ψ_shift, hFf']
  · intro w
    rw [h.Ψ_anti, ← hGg']
  · intro ε hε
    obtain ⟨R, hR⟩ := h.Ψ_small (ε / ‖lam‖) (div_pos hε hnorm)
    refine ⟨R, fun w hw => ⟨?_, ?_⟩⟩
    · intro hcontra
      have h1 : trChartInv z₀ lam (trChart z₀ lam (h.Ψ w)) = trChartInv z₀ lam z₀ :=
        congrArg (trChartInv z₀ lam) hcontra
      rw [trChartInv_trChart hlam] at h1
      have h0 : trChartInv z₀ lam z₀ = 0 := by simp [trChartInv]
      rw [h0] at h1
      exact (hR w hw).1 h1
    · have h2 : ‖h.Ψ w‖ < ε / ‖lam‖ := by simpa using (hR w hw).2
      have hlt : ‖h.Ψ w‖ * ‖lam‖ < ε := (lt_div_iff₀ hnorm).mp h2
      show ‖trChart z₀ lam (h.Ψ w) - z₀‖ < ε
      rw [trChart_apply]
      calc ‖z₀ + lam * h.Ψ w - z₀‖ = ‖lam * h.Ψ w‖ := by rw [add_sub_cancel_left]
        _ = ‖lam‖ * ‖h.Ψ w‖ := norm_mul lam (h.Ψ w)
        _ = ‖h.Ψ w‖ * ‖lam‖ := mul_comm _ _
        _ < ε := hlt
  · obtain ⟨R₀, hR₀⟩ := h.Ψ_inj
    exact ⟨R₀, fun a ha b hb hab => hR₀ ha hb (trChart_injective hlam hab)⟩
  · obtain ⟨R₀, hR₀⟩ := h.Ψ_ends
    exact ⟨R₀, fun w hw hwim => ⟨h.Ψ w, hR₀ w hw hwim, rfl⟩⟩
  -- the covering property rescales by `‖lam‖`
  · intro R
    obtain ⟨r, hr_pos, hr⟩ := h.cover R
    refine ⟨‖lam‖ * r, mul_pos hnorm hr_pos, ?_⟩
    intro z hz0 hzlt
    set u := trChartInv z₀ lam z with hu
    have hu_norm : ‖u‖ = ‖z - z₀‖ / ‖lam‖ := by rw [hu]; simp only [trChartInv, norm_div]
    have hu_pos : 0 < ‖u‖ := by rw [hu_norm]; exact div_pos hz0 hnorm
    have hu_lt : ‖u‖ < r := by
      rw [hu_norm]
      exact (div_lt_iff₀ hnorm).mpr (by rw [mul_comm]; exact hzlt)
    have hmem := hr u (by simpa using hu_pos) (by simpa using hu_lt)
    rcases hmem with hu_Pa | ⟨w, hw, hwΨ⟩
    · exact Or.inl ⟨u, hu_Pa, by rw [hu]; exact trChart_trChartInv hlam z⟩
    · exact Or.inr ⟨w, hw, by rw [hwΨ]; rw [hu]; exact trChart_trChartInv hlam z⟩
  -- ## the extra fields of the repaired flower: the `g`-invariant half-petal `Pg`
  · -- `Pg ⊆ Pa`
    exact Set.image_mono h.Pg_sub
  · -- openness of the image
    rw [show trChart z₀ lam '' h.Pg = trChartInv z₀ lam ⁻¹' h.Pg from by
        ext z; exact mem_trChart_image hlam]
    exact h.isOpen_Pg.preimage (continuous_trChartInv z₀ lam)
  · -- nonemptiness
    exact h.Pg_nonempty.image _
  · -- preconnectedness
    exact h.isPreconnected_Pg.image _ (continuous_trChart z₀ lam).continuousOn
  · -- `F`-invariance
    rintro z ⟨u, hu, rfl⟩
    rw [hFf']
    exact ⟨f u, h.mapsTo_F_Pg hu, rfl⟩
  · -- `g`-invariance
    rintro z ⟨u, hu, rfl⟩
    rw [hGg']
    exact ⟨gU u, h.mapsTo_g_Pg hu, rfl⟩
  · -- entry: an orbit converging to `z₀` enters the half-petal
    intro z hzlim hzne
    set u := trChartInv z₀ lam z with hu
    have hz_eq : z = trChart z₀ lam u := by rw [hu]; exact (trChart_trChartInv hlam z).symm
    have hiter : ∀ n : ℕ, F^[n] z = trChart z₀ lam (f^[n] u) := by
      intro n; rw [hz_eq]; exact iterate_trChart hFf' u n
    have hlim : Tendsto (fun n : ℕ => f^[n] u) atTop (nhds 0) := by
      have h1 : Tendsto (fun n : ℕ => trChartInv z₀ lam (F^[n] z)) atTop
          (nhds (trChartInv z₀ lam z₀)) :=
        ((continuous_trChartInv z₀ lam).tendsto z₀).comp hzlim
      have h2 : trChartInv z₀ lam z₀ = 0 := by simp [trChartInv]
      rw [h2] at h1
      refine Tendsto.congr (fun n => ?_) h1
      rw [hiter n, trChartInv_trChart hlam]
    have hne' : ∀ n : ℕ, f^[n] u ≠ 0 := by
      intro n h0
      refine hzne n ?_
      rw [hiter n, h0]
      simp [trChart]
    obtain ⟨n, hn⟩ := h.enters_Pg u hlim hne'
    exact ⟨n, by rw [hiter n]; exact ⟨f^[n] u, hn, rfl⟩⟩
  · -- the Abel equation for the second return map
    rintro z ⟨u, hu, rfl⟩
    show h.φa (trChartInv z₀ lam (F (trChart z₀ lam u))) = h.φa (trChartInv z₀ lam (trChart z₀ lam u)) + 1
    rw [hFf', trChartInv_trChart hlam, trChartInv_trChart hlam]
    exact h.φa_shift u hu  -- ## the image of the flower lives in the ball of radius `δ` around `z₀`
  · -- the image of the transferred petal contains the tails of horizontal strips
    intro B hB
    obtain ⟨C, hC⟩ := h.image_strip B hB
    refine ⟨C, fun τ hτ hτB => ?_⟩
    obtain ⟨u, hu, hτ⟩ := hC τ hτ hτB
    exact ⟨trChart z₀ lam u, ⟨u, hu, rfl⟩, by
      show h.φa (trChartInv z₀ lam (trChart z₀ lam u)) = τ
      rw [trChartInv_trChart hlam]
      exact hτ⟩
  · rintro z ⟨u, hu, rfl⟩
    rw [Metric.mem_ball, dist_eq_norm, trChart_apply, add_sub_cancel_left, norm_mul]
    have h1 : ‖u‖ < δ / ‖lam‖ := by
      have := hPa_small hu
      rwa [Metric.mem_ball, dist_zero_right] at this
    rw [mul_comm]
    exact (lt_div_iff₀ hnorm).mp h1

/-! ## The flower with the image property at a simple parabolic fixed point -/

/-- **`exists_flowerImageFix`**: at a simple parabolic fixed point `z₀` of a holomorphic map `F`
with an antiholomorphic square root `g`, and for every `δ > 0`, there is a Leau–Fatou flower
carrying the petal image (strip) property whose petal lies in `Metric.ball z₀ δ`. -/
theorem exists_flowerImageFix (F g : ℂ → ℂ) (z₀ : ℂ) (hF : Differentiable ℂ F)
    (hg : ∀ z, DifferentiableAt ℂ (fun z => star (g z)) z) (hgg : g ∘ g = F) (hfix : F z₀ = z₀)
    (h1 : deriv F z₀ = 1) (h2 : iteratedDeriv 2 F z₀ ≠ 0) (hgz : g z₀ = z₀) {δ : ℝ} (hδ : 0 < δ) :
    ∃ fl : Work.FatouParabolic.FlowerImageFix F g z₀,
      fl.toParabolicFlowerFix.Pa ⊆ Metric.ball z₀ δ := by
  obtain ⟨f, h, a, r, A, A', lam, hlam, hb, hfeq⟩ :=
    Work.FatouCoord.Flower.germ_bounds hF hfix h1 h2
  set f' : ℂ → ℂ := fun u => (F (z₀ + lam * u) - z₀) / lam with hf'def
  have hf'ent : Differentiable ℂ f' := by rw [hf'def]; fun_prop
  have hb' : ParabolicBounds f' h a r A A' :=
    Work.FatouCoordFix.FlowerFix.epf_Bounds_of_eqOn hb (fun u hu => by
      show (F (z₀ + lam * u) - z₀) / lam = f u
      exact (hfeq u (mem_ball_zero_iff.mpr hu)).symm)
  set gU : ℂ → ℂ := fun u => (g (z₀ + lam * u) - z₀) / lam with hgUdef
  have hstar_gU : ∀ u : ℂ, star (gU u) = (star (g (z₀ + lam * u)) - star z₀) / star lam := by
    intro u; rw [hgUdef, star_div₀, star_sub]
  have hGdiff : Differentiable ℂ (fun u : ℂ => star (gU u)) := by
    have h0 : Differentiable ℂ (fun z : ℂ => star (g z)) := fun z => hg z
    have h1' : Differentiable ℂ (fun u : ℂ => star (g (z₀ + lam * u))) :=
      h0.comp (by fun_prop)
    have h2' : Differentiable ℂ (fun u : ℂ => (star (g (z₀ + lam * u)) - star z₀) / star lam) :=
      (h1'.sub_const _).div_const _
    have he : (fun u : ℂ => star (gU u))
        = fun u : ℂ => (star (g (z₀ + lam * u)) - star z₀) / star lam := funext hstar_gU
    rw [he]; exact h2'
  have hgU_anti : ∀ z : ℂ, DifferentiableAt ℂ (fun z => star (gU z)) z :=
    fun z => hGdiff.differentiableAt
  have hggU : gU ∘ gU = f' := by
    funext u
    show (g (z₀ + lam * ((g (z₀ + lam * u) - z₀) / lam)) - z₀) / lam
        = (F (z₀ + lam * u) - z₀) / lam
    rw [show z₀ + lam * ((g (z₀ + lam * u) - z₀) / lam) = g (z₀ + lam * u) from by
          field_simp; ring,
      show g (g (z₀ + lam * u)) = F (z₀ + lam * u) from congrFun hgg (z₀ + lam * u)]
  have hgU0 : gU 0 = 0 := by
    show (g (z₀ + lam * 0) - z₀) / lam = 0
    rw [mul_zero, add_zero, hgz, sub_self, zero_div]
  set G : ℂ → ℂ := fun u => star (gU u) with hGdef
  have hGan : AnalyticAt ℂ G 0 := by rw [hGdef]; exact hGdiff.analyticAt 0
  have hG0 : G 0 = 0 := by show star (gU 0) = 0; rw [hgU0, star_zero]
  have hGstar : ∀ u : ℂ, star (G u) = gU u := by intro u; rw [hGdef]; simp
  have hhf : ∀ u : ℂ, ‖u‖ < r → f' u = star (G (star (G u))) := by
    intro u hu
    rw [← congrFun hggU u, Function.comp_apply, hGstar, hGstar]
  have hh0 : h 0 = 1 := by
    have hcl := hb.h_close 0 (mem_ball_zero_iff.mpr (by simpa using hb.hr))
    have : ‖h 0 - 1‖ ≤ 0 := by simpa using hcl
    exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
  have hha : deriv h 0 = a := epf_deriv_h_eq_a hb
  have hhd : DifferentiableAt ℂ h 0 := hb.h_diff.differentiableAt (Metric.ball_mem_nhds 0 hb.hr)
  obtain ⟨hG1, ha_sym⟩ :=
    Work.FatouCoord.Flower.tangency_of_antiholomorphic_root hb.hr hGan hG0 hhf
      (fun u hu => hb'.f_eq u (mem_ball_zero_iff.mpr hu)) hhd hh0 hha
  obtain ⟨C, ρ', hρ', hC⟩ := Work.FatouCoord.Flower.norm_star_sub_le hGan hG0 hG1
  set ρ : ℝ := min ρ' r with hρdef
  have hρpos : 0 < ρ := lt_min hρ' hb.hr
  have hρr : ρ ≤ r := min_le_right _ _
  have hb'' : ParabolicBounds f' h a ρ A A' := Work.FatouCoordFix.FlowerFix.epf_Bounds_mono hb' hρpos hρr
  have hgl : ∀ z : ℂ, ‖z‖ < ρ → ‖gU z - star z‖ ≤ C * ‖z‖ ^ 2 := by
    intro z hz
    have h1' := hC z (lt_of_lt_of_le hz (min_le_left _ _))
    rw [← hGstar z]
    exact h1'
  have hδ' : 0 < δ / ‖lam‖ := div_pos hδ (norm_pos_iff.mpr hlam)
  obtain ⟨fl₀, hPa₀⟩ :=
    germ_flowerImageFix_small hf'ent hb'' hρpos (le_refl ρ) hδ' hgl hgU_anti hggU hgU0 ha_sym
  refine transfer_flowerImageFix (F := F) (g := g) (f := f') (gU := gU) (z₀ := z₀) (lam := lam)
    (δ := δ) hlam (fun z => hg z) ?_ ?_ hδ fl₀ hPa₀
  · intro u
    rw [hf'def]
    field_simp
    ring
  · intro u
    rw [hgUdef]
    field_simp
    ring

end

end Work.FatouParabolic.Core
