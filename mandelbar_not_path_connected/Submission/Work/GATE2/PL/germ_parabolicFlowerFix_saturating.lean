import Mathlib
import Submission.Work.FatouCoordFix.FlowerFix.GermFix
import Submission.Work.GATE2.PL.fatouCoordW_saturates_petal

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The germ flower whose Fatou coordinate saturates a right half-plane

`Work.FatouCoordFix.FlowerFix.germ_parabolicFlowerFix_small` produces a repaired Leau–Fatou
flower of a simple parabolic germ `f z = z + z ^ 2 h z` with antiholomorphic square root `gU`,
small enough to sit in a prescribed ball `ball 0 δ`.  Its antiholomorphic Fatou coordinate
`φa` is an opaque `∃`-witness, so nothing can be said about its image from the statement alone.

Here we re-run the *same* construction (all the estimates are imported lemmas of the
`FatouCoord` / `FatouCoordFix` areas), but with the strengthened push-forward lemma
`exists_phia_pushforward_agree`, which additionally records that the extended coordinate agrees
with the *orbit coordinate* on the petal `P` used for the push-forward.  Choosing `P` so small
that the `gU`-invariant half-plane sub-petal `Pg ⊆ P` sits inside it, we obtain a flower whose
Fatou coordinate on `Pg` is the explicit function `z ↦ fatouCoord f (1 - a) z + s`.

For that function the *saturation* statement of `fatouCoordW_saturates_petal` applies: the
chart Fatou coordinate `w ↦ fatouCoordW f (1 - a) w` surjects onto a right half-plane
`{Re τ > X}` with preimages of arbitrarily large real part, hence on the half-plane petal `Pg`
the coordinate `φa` takes every value of a right half-plane.  This is exactly the extra
statement the tricorn (Mandelbar) path-connectivity proof needs.
-/

open scoped Topology
open Set Filter Metric Function

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace Work.GATE2.PL

noncomputable section

open Work.FatouCoord
open Work.FatouCoord.Flower

/-! ## The strengthened push-forward lemmas -/

/-- **`exists_antiFatou_of_pushforward`, with the agreement on `Pa` made explicit.**

The extension of a partially defined antiholomorphic Fatou coordinate produced by
`Work.FatouCoord.Flower.exists_antiFatou_of_pushforward` agrees with the input function `Φ` on
`Pa`; we record this, because the consumers need to know *which* function the `∃`-witness is. -/
theorem exists_antiFatou_of_pushforward_agree {gU Φ : ℂ → ℂ} {Pa : Set ℂ}
    (hanti : Work.FatouCoord.IsAntiholomorphicOn gU Pa)
    (hΦdiff : DifferentiableOn ℂ Φ Pa) (hΦinj : Set.InjOn Φ Pa)
    (hgUinj : Set.InjOn gU Pa)
    (hkey : ∀ z ∈ Pa, gU z ∈ Pa → Φ (gU z) = star (Φ z) + 1 / 2) :
    ∃ φa : ℂ → ℂ, Work.FatouCoord.IsAntiholomorphicFatouOn gU φa Pa ∧ Set.InjOn φa Pa ∧
      ∀ z ∈ Pa, φa z = Φ z := by
  classical
  -- Extend `Φ` off `Pa`: on `Pa` keep `Φ`, on the extra points `gU '' Pa \ Pa` define the
  -- forced value `Φ (gU z) = star (Φ z) + 1/2` (well defined by injectivity of `gU` on `Pa`),
  -- and arbitrarily elsewhere.
  let φa : ℂ → ℂ := fun z =>
    if hz : z ∈ Pa then Φ z
    else if hzA : z ∈ gU '' Pa then star (Φ (Classical.choose hzA)) + 1 / 2
    else 0
  have hφa_on : ∀ z ∈ Pa, φa z = Φ z := by
    intro z hz
    simp only [φa, dite_eq_left hz]
  -- The key relation: on `Pa` the map `φa` satisfies `φa (gU z) = star (φa z) + 1/2`.
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
  refine ⟨φa, ⟨hanti, ?_, hrel⟩, ?_, hφa_on⟩
  · exact hΦdiff.congr hφa_on
  · intro a ha b hb hab
    have h1 : φa a = Φ a := hφa_on a ha
    have h2 : φa b = Φ b := hφa_on b hb
    exact hΦinj ha hb (by rw [← h1, ← h2, hab])

/-- **`exists_phia_pushforward`, with the orbit coordinate made explicit.**

Same statement as `Work.FatouCoord.Flower.exists_phia_pushforward`, with the extra information
that the witness `φa` coincides on the small petal `P` with the antiholomorphic Fatou
coordinate `φ₀` that the push-forward starts from.  This is what lets us compute `φa` on the
half-plane sub-petal. -/
theorem exists_phia_pushforward_agree {f gU φ₀ : ℂ → ℂ} {P Pa : Set ℂ}
    (hf : Differentiable ℂ f)
    (hgU_anti : ∀ z : ℂ, DifferentiableAt ℂ (fun z => star (gU z)) z)
    (hPopen : IsOpen P) (hPmaps : Set.MapsTo f P P) (hPsubPa : P ⊆ Pa)
    (hφ : Work.FatouCoord.IsFatouCoordinateOn f φ₀ P) (hφinj : Set.InjOn φ₀ P)
    (hanti : Work.FatouCoord.IsAntiholomorphicFatouOn gU φ₀ P)
    (hgg : gU ∘ gU = f) (hgU0 : gU 0 = 0)
    (hPamaps : Set.MapsTo f Pa Pa) (hPa0 : (0 : ℂ) ∉ Pa)
    (hPalim : ∀ z ∈ Pa, Filter.Tendsto (fun n : ℕ => f^[n] z) Filter.atTop (nhds 0))
    (hPa_ne : ∀ z ∈ Pa, ∀ n : ℕ, f^[n] z ≠ 0)
    (hfinj : Set.InjOn f Pa)
    (hPentry : ∀ x : ℂ, Filter.Tendsto (fun n : ℕ => f^[n] x) Filter.atTop (nhds 0) →
      (∀ n : ℕ, f^[n] x ≠ 0) → ∃ n : ℕ, f^[n] x ∈ P) :
    ∃ φa : ℂ → ℂ, Work.FatouCoord.IsAntiholomorphicFatouOn gU φa Pa ∧ Set.InjOn φa Pa ∧
      ∀ z ∈ P, φa z = φ₀ z := by
  classical
  -- an orbit of a point of `Pa` always meets `P`
  have hex : ∀ z : ℂ, z ∈ Pa → ∃ n : ℕ, f^[n] z ∈ P :=
    fun z hz => hPentry z (hPalim z hz) (hPa_ne z hz)
  -- select the entry time
  let sel : ℂ → ℕ := fun z =>
    dite (z ∈ Pa) (fun hz => Classical.choose (hex z hz)) (fun _ => 0)
  have hsel : ∀ z : ℂ, z ∈ Pa → f^[sel z] z ∈ P := by
    intro z hz
    have hselz : sel z = Classical.choose (hex z hz) := dite_eq_left hz
    rw [hselz]
    exact Classical.choose_spec (hex z hz)
  -- the orbit coordinate
  have hΦdiff : DifferentiableOn ℂ (orbitCoord f φ₀ P Pa sel) Pa :=
    differentiableOn_orbitCoord hsel hf hPopen hPmaps hφ
  have hΦinj : Set.InjOn (orbitCoord f φ₀ P Pa sel) Pa :=
    injOn_orbitCoord hsel hPmaps hφ hφinj hfinj hPamaps
  have hkey : ∀ z ∈ Pa, gU z ∈ Pa →
      orbitCoord f φ₀ P Pa sel (gU z) = star (orbitCoord f φ₀ P Pa sel z) + 1 / 2 :=
    fun z hz hz' => orbitCoord_map_gU hsel hPmaps hφ hanti hgg hz hz'
  have hantiPa : IsAntiholomorphicOn gU Pa :=
    fun z _ => (hgU_anti z).differentiableWithinAt
  have hgUinj : Set.InjOn gU Pa := injOn_of_comp_self hgg hfinj
  obtain ⟨φa, hφa_anti, hφa_inj, hφa_on⟩ :=
    exists_antiFatou_of_pushforward_agree hantiPa hΦdiff hΦinj hgUinj hkey
  refine ⟨φa, hφa_anti, hφa_inj, fun z hz => ?_⟩
  rw [hφa_on z (hPsubPa hz)]
  have h0 := orbitCoord_eq_of_mem_iterate (f := f) (φ₀ := φ₀) (P := P) (Pa := Pa) (sel := sel)
    hsel hPmaps hφ (hPsubPa hz) (m := 0) (by simpa using hz)
  simpa using h0


/-! ## The flower with a saturating Fatou coordinate -/

/-- **The germ flower whose Fatou coordinate saturates a right half-plane.**

Same construction as `Work.FatouCoordFix.FlowerFix.germ_parabolicFlowerFix_small`, but with the
push-forward applied to a petal `P = Petal ρ M` that is small enough to contain the
`gU`-invariant half-plane sub-petal `Pg = HPlanePetal Mh` (this only needs `Mh ≥ M`).
The strengthened push-forward `exists_phia_pushforward_agree` then says that the flower's Fatou
coordinate `φa` coincides with `z ↦ fatouCoord f (1 - a) z + s` on `Pg`, and
`fatouCoordW_saturates_petal` says that the chart coordinate `w ↦ fatouCoordW f (1 - a) w`
surjects onto a right half-plane with preimages of arbitrarily large real part.  Pulling back
through the chart `W ↦ -1/W` (which identifies the right half-plane `{Re W > Mh}` with `Pg`)
gives the saturation of `φa` on `Pg`. -/
theorem germ_parabolicFlowerFix_saturating {f gU h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ} {G₀ ρ δ : ℝ}
    (hf : Differentiable ℂ f) (hb : Work.FatouCoord.ParabolicBounds f h a r A A') (hρ : 0 < ρ)
    (hρr : ρ ≤ r)
    (hδpos : 0 < δ) (ha1 : a.re < 1)
    (hgl : ∀ z : ℂ, ‖z‖ < ρ → ‖gU z - star z‖ ≤ G₀ * ‖z‖ ^ 2)
    (hgU_anti : ∀ z : ℂ, DifferentiableAt ℂ (fun z => star (gU z)) z)
    (hgg : gU ∘ gU = f) (hgU0 : gU 0 = 0) (ha : star a = a) :
    ∃ fl : Work.FatouCoordFix.ParabolicFlowerFix f gU 0,
      fl.Pa ⊆ Metric.ball 0 δ ∧ fl.Pg ⊆ Metric.ball 0 δ ∧
      ∃ X : ℝ, ∀ w : ℂ, X < w.re → ∃ z ∈ fl.Pg, fl.φa z = w := by
  -- the bounds at the smaller radius
  have hbρ : ParabolicBounds f h a ρ A A' :=
    Work.FatouCoordFix.FlowerFix.gpf_bounds_mono hb hρ hρr
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
  -- the Fatou coordinate pushed forward from the petal
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
  obtain ⟨φa, hφa_anti, hφa_inj, hφa_on⟩ :=
    exists_phia_pushforward_agree (f := f) (gU := gU)
      (φ₀ := fun z => fatouCoord f (1 - a) z + s) (P := Petal ρ M) (Pa := Pa)
      hf hgU_anti isOpen_Petal hPmaps (fun z hz => Or.inl (hsub_petal hz))
      hφ hφinj hanti hgg hgU0 hPa_maps hPa_zero hPa_tend hPa_ne hfinj hPentry
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
  -- both thresholds, above the petal level `M` needed to compute `φa` on `Pg`, and above `1/δ`
  -- makes `HPlanePetal Mh` a small `f`- and `gU`-invariant sub-petal of `Pa` on which `φa` is
  -- the explicit coordinate `z ↦ fatouCoord f (1 - a) z + s`.
  obtain ⟨Mgr, hMgr_nn, hgrG⟩ :=
    Work.FatouCoordFix.FlowerFix.gChart_re_growth hbρ hgU_anti hgg hgU0
  set Mh : ℝ := max (max (max M₀w Mgr) (max (Ms + 1) (1 / δ + 1))) (max M 1) with hMhdef
  have hMh_M₀w : M₀w ≤ Mh := by
    have h1 : M₀w ≤ max M₀w Mgr := le_max_left _ _
    have h2 : max M₀w Mgr ≤ max (max M₀w Mgr) (max (Ms + 1) (1 / δ + 1)) := le_max_left _ _
    have h3 : max (max M₀w Mgr) (max (Ms + 1) (1 / δ + 1)) ≤ Mh := by
      rw [hMhdef]; exact le_max_left _ _
    linarith
  have hMh_Mgr : Mgr ≤ Mh := by
    have h1 : Mgr ≤ max M₀w Mgr := le_max_right _ _
    have h2 : max M₀w Mgr ≤ max (max M₀w Mgr) (max (Ms + 1) (1 / δ + 1)) := le_max_left _ _
    have h3 : max (max M₀w Mgr) (max (Ms + 1) (1 / δ + 1)) ≤ Mh := by
      rw [hMhdef]; exact le_max_left _ _
    linarith
  have hMh_Ms : Ms + 1 ≤ Mh := by
    have h1 : Ms + 1 ≤ max (Ms + 1) (1 / δ + 1) := le_max_left _ _
    have h2 : max (Ms + 1) (1 / δ + 1)
        ≤ max (max M₀w Mgr) (max (Ms + 1) (1 / δ + 1)) := le_max_right _ _
    have h3 : max (max M₀w Mgr) (max (Ms + 1) (1 / δ + 1)) ≤ Mh := by
      rw [hMhdef]; exact le_max_left _ _
    linarith
  have hMh_δ : 1 / δ + 1 ≤ Mh := by
    have h1 : 1 / δ + 1 ≤ max (Ms + 1) (1 / δ + 1) := le_max_right _ _
    have h2 : max (Ms + 1) (1 / δ + 1)
        ≤ max (max M₀w Mgr) (max (Ms + 1) (1 / δ + 1)) := le_max_right _ _
    have h3 : max (max M₀w Mgr) (max (Ms + 1) (1 / δ + 1)) ≤ Mh := by
      rw [hMhdef]; exact le_max_left _ _
    linarith
  have hMh_M : M ≤ Mh := by
    have h1 : M ≤ max M 1 := le_max_left _ _
    have h2 : max M 1 ≤ Mh := by rw [hMhdef]; exact le_max_right _ _
    linarith
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
    intro z ht hne'
    obtain ⟨n₀, hn₀⟩ := hPentry z ht hne'
    have h1 : f^[n₀] z ∈ WidePetal M :=
      Work.FatouCoordFix.HPetal.Petal_subset_WidePetal (by linarith) hn₀
    obtain ⟨k, hk⟩ := Work.FatouCoordFix.HPetal.exists_iterate_mem_HPlanePetal
      (f := f) (M := Mh) (M' := M) (hgr M (le_trans hMs_ge_M₀w hM_Ms)) h1
    refine ⟨n₀ + k, ?_⟩
    have h2 : f^[n₀ + k] z = f^[k] (f^[n₀] z) :=
      (Function.iterate_add_apply f n₀ k z).trans (Work.FatouCoord.iterate_comm f k n₀ z).symm
    rw [h2]
    exact hk
  -- `Pg` sits inside the petal `Petal ρ M` on which the coordinate is computed explicitly
  have hPg_sub_M : Pg ⊆ Petal ρ M := by
    intro u hu
    rw [hPgdef] at hu
    rw [Work.FatouCoordFix.mem_HPlanePetal] at hu
    obtain ⟨hu0, huM⟩ := hu
    rw [Work.FatouCoord.chart_mem_Petal_iff hρ hu0]
    refine ⟨?_, ?_⟩
    · show M < (Work.FatouCoord.chart u).re
      exact lt_of_le_of_lt hMh_M huM
    · have h2 : (1 / ρ : ℝ) < Mh := lt_trans hMs_ρ hMs_lt_Mh
      exact lt_of_lt_of_le (lt_trans h2 huM) (Complex.re_le_norm _)
  -- on `Pg` the flower's Fatou coordinate is the explicit function
  have hφa_Pg : ∀ z ∈ Pg, φa z = fatouCoord f (1 - a) z + s := by
    intro z hz
    exact hφa_on z (hPg_sub_M hz)
  have hφa_shift : ∀ z ∈ Pa, φa (f z) = φa z + 1 :=
    Work.FatouCoordFix.φa_shift_of_halfPetal hPa_open hPa_pre hPg_open hPg_ne hPg_sub
      hφa_anti.2.1 hf hPa_maps hgg hPg_gmaps (fun z hz => hφa_anti.2.2 z (hPg_sub hz))
  have hPa_ball_δ : Pa ⊆ Metric.ball 0 δ :=
    le_trans hPa_ball (Metric.ball_subset_ball hε_le_delta)
  have hPg_ball : Pg ⊆ Metric.ball 0 δ := by
    intro u hu
    rw [Metric.mem_ball, dist_zero_right]
    have h1 : Mh * ‖u‖ < 1 := by
      rw [hPgdef] at hu
      exact Work.FatouCoordFix.HPetal.HPlanePetal_mul_norm_lt hu
    have h2 : 1 / δ < Mh := by linarith
    rw [div_lt_iff₀ hδpos] at h2
    nlinarith [h1, h2]
  -- ### saturation: `φa` on `Pg` takes every value of a right half-plane
  have hsat : ∃ X : ℝ, ∀ w : ℂ, X < w.re → ∃ z ∈ Pg, φa z = w := by
    obtain ⟨X, hX⟩ := fatouCoordW_saturates_petal (f := f) (h := h) (a := a) (r := r)
      (A := A) (A' := A') hb ha1 Mh
    refine ⟨X + s.re, fun w hw => ?_⟩
    have hτ : X < (w - s).re := by rw [Complex.sub_re]; linarith
    obtain ⟨W, hWre, hWψ⟩ := hX (w - s) hτ
    have hWne : W ≠ 0 := by
      intro h0
      rw [h0] at hWre
      simp at hWre
      linarith
    have hchart : Work.FatouCoord.chart (-1 / W) = W := by
      show (-1 : ℂ) / (-1 / W) = W
      exact Work.FatouCoordFix.neg_one_div_neg_one_div' hWne
    have hmem : (-1 / W) ∈ Pg := by
      rw [hPgdef, Work.FatouCoordFix.mem_HPlanePetal]
      refine ⟨div_ne_zero (by norm_num) hWne, ?_⟩
      show Mh < (Work.FatouCoord.chart (-1 / W)).re
      rw [hchart]; exact hWre
    refine ⟨-1 / W, hmem, ?_⟩
    have h1 : φa (-1 / W) = fatouCoord f (1 - a) (-1 / W) + s := hφa_Pg (-1 / W) hmem
    rw [h1, Work.FatouCoord.fatouCoord_eq, hchart, hWψ]
    ring
  refine ⟨⟨{
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
    hPa_ball_δ, hPg_ball, hsat⟩

end
end Work.GATE2.PL
