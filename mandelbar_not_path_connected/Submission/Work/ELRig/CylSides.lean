/-
# ELRig — R-a3 from the two-sidedness of the lifted ray pair

`NOTES_LEAD_mandelbar_EL.md` §2 (R-a): under the contradiction hypothesis `E ⊆ K` the equator
tail must lie on the *near* (band) side of the `α`-pair.  The two ingredients are

* **the curves**: `Work.ELRig.RayCylLift` (`CylLift.lean`) — the two `1`-periodic lifts of the
  root rays in the repelling coordinate, with `TailId` (proved in `exists_rayCylLift`), the
  anti-symmetry `γ₂ = ι γ₁` and the far-left avoidance of `z₁`; and
* **the plane topology** `Work.EL.LiftSides` (`Inputs.lean`) — the three preconnected regions
  `U`, `M`, `L` cut out by the two curves in the left half plane, `M` containing the real axis.

`exists_liftSides_of_cylGraph` produces the topology from the *graph property* of the lifts
(`StrictMono (Re ∘ γ₁)`, which by the anti-symmetry is the same condition for `γ₂`); the
derivation itself is `Work.ELRig.exists_liftSides_of_anti`, and the counterexample of
`ELRig/NOTES.md` §6.1 shows that the graph property — or an equivalent separation input — cannot
be dropped.

`equatorTail_mem_near_of_liftSides` is R-a3: `Ψ` of the far-left real axis lies in
`pairSideNear P`.  The proof is the exhaustion argument of `equatorTail_mem_near` with the
`RayLift` replaced by the `RayCylLift` + `LiftSides` pair (so that the false `RayStrand` field
disappears from the chain).
-/
import Mathlib
import Submission.Work.ELRig.Inputs
import Submission.Work.ELRig.Sides
import Submission.Work.ELRig.Flower
import Submission.Work.ELRig.CylLift
import Submission.Work.ELRig.exists_rayCylLift
import Submission.Work.ELRig.exists_liftSidesV2
import Submission.Work.ELRig.exists_liftSides_of_anti
import Submission.Work.ELRig.LocalInverse.exists_analytic_localInverse
import Submission.Work.ELRig.deriv_ne_zero_of_injOn

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

noncomputable section

namespace Work.ELRig

open Work.EL

/-! ## The `Ψ`-preimages of the pair curve are the two lifts -/

/-- For a pair `P` of the root portrait (`P.a = α₁`, `P.b = α₂`, `P.y = z₁`), the
`Ψ`-preimages of its curve in the far-left half plane `{Re < -R}` are exactly the two lifts.

* `⟹`: a preimage of the ray `R(α₁)` is on `γ₁` (`TailId`), and `Ψ w = z₁` is excluded by
  `hzne`;
* `⟸`: the lifts map into the two rays (`img₁`, `img₂`), the ray `R(α_i)` is contained in the
  pair curve. -/
theorem RayCylLift.preimage_pairCurve {c : ℂ} {d : Work.EL.RootParabolic c}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁}
    (L : RayCylLift d fl) (P : Work.EL.CoPair d.hN)
    (hPa1 : P.a = Work.EL.alpha1) (hPb1 : P.b = Work.EL.alpha2) (hPy : P.y = d.z₁) :
    ∀ w : ℂ, w.re < -L.R →
      (fl.Ψ w ∈ Work.EL.pairCurve P ↔ w ∈ Set.range L.γ₁ ∪ Set.range L.γ₂) := by
  intro w hw
  constructor
  · intro hmem
    rw [Work.EL.mem_pairCurve_iff] at hmem
    rcases hmem with h | h | h
    · exact Or.inl (L.tailId₁ w hw (hPa1 ▸ h))
    · exact absurd (h.trans hPy) (L.hzne w hw)
    · exact Or.inr (L.tailId₂ w hw (hPb1 ▸ h))
  · rintro (⟨s, rfl⟩ | ⟨s, rfl⟩)
    · rw [Work.EL.mem_pairCurve_iff]
      refine Or.inl ?_
      rw [hPa1, L.hΨ₁ s]
      exact Work.EL.rayPt_mem_paramRay d.hN (L.hτ1 s)
    · rw [Work.EL.mem_pairCurve_iff]
      exact Or.inr (Or.inr (hPb1 ▸ L.img₂ s))

/-! ## The local biholomorphy of `Ψ` in the far-left half plane

The flower's `Ψ` is entire (`Ψ_diff`) and injective on a far-left half plane (`Ψ_inj`); hence its
derivative is nonvanishing there and it is a local biholomorphism.  This is the local
invertibility used by the crossing argument of `NOTES.md` §8 (the lead's point (ii)): at every
crossing point of a lift with a vertical line the map `Ψ` is a local bijection. -/

/-- **`Ψ` is a local biholomorphism on the injectivity half plane.** -/
theorem exists_localInverseAt_of_inj {c : ℂ} {z₁ : ℂ}
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) z₁)
    {R : ℝ} (hinj : Set.InjOn fl.Ψ {w : ℂ | w.re < -R}) {x : ℂ} (hx : x.re < -R) :
    ∃ δ > 0, ∃ σ : ℂ → ℂ,
      AnalyticOnNhd ℂ σ (Metric.ball (fl.Ψ x) δ) ∧
      (∀ z ∈ Metric.ball (fl.Ψ x) δ, fl.Ψ (σ z) = z) ∧
      (∀ w ∈ Metric.ball x δ, σ (fl.Ψ w) = w) := by
  have hδ : ∃ δ > 0, Metric.ball x δ ⊆ {w : ℂ | w.re < -R} := by
    refine ⟨(-R - x.re) / 2, by linarith, fun w hw => ?_⟩
    have h1 : ‖w - x‖ < (-R - x.re) / 2 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hw
    have h2 : (w - x).re ≤ ‖w - x‖ := Complex.re_le_norm _
    have h3 : (w - x).re = w.re - x.re := Complex.sub_re w x
    rw [h3] at h2
    simp only [Set.mem_setOf_eq]
    linarith
  obtain ⟨δ, hδpos, hδsub⟩ := hδ
  obtain ⟨δ₁, hδ₁pos, δ₂, hδ₂pos, σ, han, hright, hleft, -⟩ :=
    Work.ELRig.LocalInverse.exists_analytic_localInverse fl.Ψ_diff
      ⟨δ, hδpos, fun a ha b hb hab => hinj (hδsub ha) (hδsub hb) hab⟩
  refine ⟨min δ₁ δ₂, lt_min hδ₁pos hδ₂pos, σ, ?_, ?_, ?_⟩
  · exact han.mono (Metric.ball_subset_ball (min_le_right _ _))
  · intro z hz
    exact hright z (Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hz)
      (min_le_right _ _)))
  · intro w hw
    exact hleft w (Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hw)
      (min_le_left _ _)))

/-- **The derivative of `Ψ` is nonvanishing on the injectivity half plane.** -/
theorem deriv_psi_ne_zero_of_inj {c : ℂ} {z₁ : ℂ}
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) z₁)
    {R : ℝ} (hinj : Set.InjOn fl.Ψ {w : ℂ | w.re < -R}) {x : ℂ} (hx : x.re < -R) :
    deriv fl.Ψ x ≠ 0 :=
  Work.ELRig.deriv_ne_zero_of_injOn fl.Ψ_diff.differentiableOn
    (isOpen_lt Complex.continuous_re continuous_const) hinj hx

/-! ## The plane topology from the graph property -/

/-- **R-a2 (iii) from the graph property.**  If the first lift is a graph over the real axis
(`StrictMono (Re ∘ γ₁)`; by the anti-symmetry `γ₂ s = γ₁ s‾ + ½` this is the same statement for
`γ₂`), then the two curves cut the left half plane into the three regions of
`Work.EL.LiftSides`, with the real axis in the middle one.

The argument is `exists_liftSides_of_anti`: the anti-symmetry of the two curves turns the
zero-freeness of the heights on `(-∞,-R)` (`RayCylLift.hreal_of hE`) into the two sign conditions
"`γ₁` above, `γ₂` below the real axis". -/
theorem exists_liftSides_of_cylGraph {c : ℂ} {d : Work.EL.RootParabolic c}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁}
    (L : RayCylLift d fl) {R₀ : ℝ} (hRR₀ : R₀ < L.R)
    (hmono : StrictMono fun s : ℝ => (L.γ₁ s).re)
    (hE : ∀ x : ℝ, fl.Ψ (x : ℂ) ∈ Work.EL.K c) :
    Nonempty (Work.EL.LiftSides d.hN d.z₁ L.γ₁ L.γ₂ L.R R₀) := by
  have hmono₂ : StrictMono fun s : ℝ => (L.γ₂ s).re := by
    intro a b hab
    have h := hmono hab
    have ha : (L.γ₂ a).re = (L.γ₁ a).re + 1 / 2 := by rw [L.anti a]; simp
    have hb : (L.γ₂ b).re = (L.γ₁ b).re + 1 / 2 := by rw [L.anti b]; simp
    change (L.γ₂ a).re < (L.γ₂ b).re
    rw [ha, hb]; linarith
  have hanti : Set.range L.γ₂ = (fun w : ℂ => star w + 1 / 2) '' Set.range L.γ₁ := by
    ext z
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨L.γ₁ s, ⟨s, rfl⟩, (L.anti s).symm⟩
    · rintro ⟨w, ⟨s, rfl⟩, hw⟩
      exact ⟨s, by rw [← hw, L.anti s]⟩
  exact Work.ELRig.exists_liftSides_of_anti hRR₀ L.cont₁ L.cont₂ hmono hmono₂ L.per₁ L.per₂
    hanti (L.hreal_of hE)

/-! ## R-a3 -/

/-- **R-a3.**  Under the contradiction hypothesis `E ⊆ K c` the equator tail `Ψ x`, `x < -R'`,
lies on the *near* side (the band side, away from the attracting petal) of the `α`-pair `P`.

The proof is the exhaustion argument of the two-sides lemma: the images of the two regions `U`,
`L` (which reach `|Im| > R₀`) are `Pa`, hence lie on the far side `pairSide P`; a point of the
near side near `z₁` exists (`z₁` is on the frontier of `pairSideNear P`), and by the flower's
`cover` it is the `Ψ`-image of a point of the left half plane; that point avoids the two lifts
(its image is off the pair curve, and the `Ψ`-preimages of the pair curve are the lifts), hence
lies in `U ∪ M ∪ L`, and since `U`, `L` map into the far side it lies in `M`; so `Ψ '' M` is a
preconnected set avoiding the pair curve which meets the near side, hence lies in
`pairSideNear P`; and the real axis below `-R` lies in `M`. -/
theorem equatorTail_mem_near_of_liftSides {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (P : Work.EL.CoPair d.hN) (hPy : P.y = d.z₁) (hPa1 : P.a = Work.EL.alpha1)
    (hPb1 : P.b = Work.EL.alpha2) (hside : Work.EL.PairSides d.hN P)
    (L : RayCylLift d fl) {R₀ : ℝ}
    (lift : Work.EL.LiftSides d.hN d.z₁ L.γ₁ L.γ₂ L.R R₀)
    (hγ : ∀ w : ℂ, w.re < -R₀ → R₀ < |w.im| → fl.Ψ w ∈ fl.Pa)
    (hPa_far : fl.Pa ⊆ Work.EL.pairSide P) (hPa_ne : fl.Pa.Nonempty)
    (hE : ∀ x : ℝ, fl.Ψ (x : ℂ) ∈ Work.EL.K c) :
    ∃ R' : ℝ, ∀ x : ℝ, x < -R' → fl.Ψ (x : ℂ) ∈ Work.EL.pairSideNear P := by
  -- the two sides of the pair are disjoint
  have hdisj : ∀ z, z ∈ Work.EL.pairSide P → z ∈ Work.EL.pairSideNear P → False := by
    intro z h1 h2
    have hm : z ∈ Work.EL.pairSide P ∩ Work.EL.pairSideNear P := ⟨h1, h2⟩
    rw [Set.disjoint_iff_inter_eq_empty.mp hside.disjoint] at hm
    exact hm
  -- a point of the left half plane off the two lifts has `Ψ`-image off the pair curve
  have hunter : ∀ w : ℂ, w.re < -L.R → w ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ →
      fl.Ψ w ∉ Work.EL.pairCurve P := by
    intro w hwR hwγ hmem
    exact hwγ ((L.preimage_pairCurve P hPa1 hPb1 hPy w hwR).mp hmem)
  -- a preconnected set of the left half plane off the lifts whose `Ψ`-image reaches `|Im| > R₀`
  -- maps into the far side
  have far_of : ∀ T : Set ℂ, IsPreconnected T → T ⊆ {w : ℂ | w.re < -L.R} →
      T ∩ (Set.range L.γ₁ ∪ Set.range L.γ₂) = ∅ → (∃ w ∈ T, R₀ < |w.im|) →
      fl.Ψ '' T ⊆ Work.EL.pairSide P := by
    intro T hTconn hTsub hToff hex
    have hTγ : ∀ w ∈ T, w ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ := by
      intro w hw hmem
      have hmem' : w ∈ T ∩ (Set.range L.γ₁ ∪ Set.range L.γ₂) := ⟨hw, hmem⟩
      rw [hToff] at hmem'
      exact hmem'
    have himg : IsPreconnected (fl.Ψ '' T) :=
      hTconn.image fl.Ψ (fl.Ψ_diff.continuous.continuousOn)
    have havoid : fl.Ψ '' T ⊆ (Work.EL.pairCurve P)ᶜ := by
      rintro z ⟨w, hwT, rfl⟩
      exact hunter w (hTsub hwT) (hTγ w hwT)
    rcases hside.subset_of_preconnected himg havoid with h | h
    · exact h
    · obtain ⟨w₀, hw₀T, hw₀abs⟩ := hex
      have hw₀R : w₀.re < -L.R := hTsub hw₀T
      have hw₀re : w₀.re < -R₀ := by linarith [lift.hRR₀]
      have hpa : fl.Ψ w₀ ∈ fl.Pa := hγ w₀ hw₀re hw₀abs
      exact (hdisj _ (hPa_far hpa) (h ⟨w₀, hw₀T, rfl⟩)).elim
  -- `U` and `L` map into the far side
  have hUabs : ∃ w ∈ lift.U, R₀ < |w.im| := by
    obtain ⟨w, hwU, hwim⟩ := lift.top_mem_U
    exact ⟨w, hwU, lt_of_lt_of_le hwim (le_abs_self _)⟩
  have hUfar : fl.Ψ '' lift.U ⊆ Work.EL.pairSide P :=
    far_of lift.U lift.U_conn lift.U_sub lift.U_off hUabs
  have hLabs : ∃ w ∈ lift.L, R₀ < |w.im| := by
    obtain ⟨w, hwL, hwim⟩ := lift.bottom_mem_L
    exact ⟨w, hwL, lt_of_lt_of_le (by linarith) (neg_le_abs w.im)⟩
  have hLfar : fl.Ψ '' lift.L ⊆ Work.EL.pairSide P :=
    far_of lift.L lift.L_conn lift.L_sub lift.L_off hLabs
  -- a point of the near side near `z₁` is the image of a point of the middle region `M`
  have hM_avoid : ∀ w ∈ lift.M, w ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ := by
    intro w hw hmem
    have hmem' : w ∈ lift.M ∩ (Set.range L.γ₁ ∪ Set.range L.γ₂) := ⟨hw, hmem⟩
    rw [lift.M_off] at hmem'
    exact hmem'
  have hz1_curve : d.z₁ ∈ Work.EL.pairCurve P :=
    (Work.EL.mem_pairCurve_iff P d.z₁).mpr (Or.inr (Or.inl hPy.symm))
  have hz1_cl : d.z₁ ∈ closure (Work.EL.pairSideNear P) := by
    have hfr : d.z₁ ∈ frontier (Work.EL.pairSideNear P) := by
      rw [hside.frontier_near]
      exact hz1_curve
    exact frontier_subset_closure hfr
  obtain ⟨r, hrpos, hcover⟩ := fl.cover L.R
  obtain ⟨q, hq_near, hq_dist⟩ := Metric.mem_closure_iff.mp hz1_cl r hrpos
  have hq_dist' : ‖q - d.z₁‖ < r := by
    simpa [dist_eq_norm, norm_sub_rev] using hq_dist
  have hq_ne : q ≠ d.z₁ := by
    intro hq
    rw [hq] at hq_near
    exact (hside.notMem_curve_of_mem_near hq_near) hz1_curve
  have hq_pos : 0 < ‖q - d.z₁‖ := by
    rw [norm_pos_iff]
    exact sub_ne_zero.mpr hq_ne
  have hq_img : q ∈ fl.Ψ '' lift.M := by
    rcases hcover q hq_pos hq_dist' with hqPa | ⟨w, hwR, hwq⟩
    · exact (hdisj q (hPa_far hqPa) hq_near).elim
    · have hw_cover : w ∈ lift.U ∨ w ∈ lift.M ∨ w ∈ lift.L ∨
          w ∈ Set.range L.γ₁ ∨ w ∈ Set.range L.γ₂ := by
        have h := lift.cover hwR
        simpa only [Set.mem_union, or_assoc] using h
      rcases hw_cover with hwU | hwM | hwL | hwγ1 | hwγ2
      · exact (hdisj q (by rw [← hwq]; exact hUfar ⟨w, hwU, rfl⟩) hq_near).elim
      · exact ⟨w, hwM, hwq⟩
      · exact (hdisj q (by rw [← hwq]; exact hLfar ⟨w, hwL, rfl⟩) hq_near).elim
      · obtain ⟨s, rfl⟩ := hwγ1
        have hcur : q ∈ Work.EL.pairCurve P := by
          rw [← hwq, Work.EL.mem_pairCurve_iff]
          exact Or.inl (hPa1.symm ▸ L.img₁ s)
        exact ((hside.notMem_curve_of_mem_near hq_near) hcur).elim
      · obtain ⟨s, rfl⟩ := hwγ2
        have hcur : q ∈ Work.EL.pairCurve P := by
          rw [← hwq, Work.EL.mem_pairCurve_iff]
          exact Or.inr (Or.inr (hPb1.symm ▸ L.img₂ s))
        exact ((hside.notMem_curve_of_mem_near hq_near) hcur).elim
  -- hence the whole `Ψ`-image of `M` lies in the near side
  have himgM : IsPreconnected (fl.Ψ '' lift.M) :=
    lift.M_conn.image fl.Ψ (fl.Ψ_diff.continuous.continuousOn)
  have havoidM : fl.Ψ '' lift.M ⊆ (Work.EL.pairCurve P)ᶜ := by
    rintro z ⟨w, hwM, rfl⟩
    exact hunter w (lift.M_sub hwM) (hM_avoid w hwM)
  have hMnear : fl.Ψ '' lift.M ⊆ Work.EL.pairSideNear P := by
    rcases hside.subset_of_preconnected himgM havoidM with h | h
    · exact (hdisj q (h hq_img) hq_near).elim
    · exact h
  refine ⟨L.R, fun x hx => hMnear ⟨(x : ℂ), lift.real_mem_M x hx, rfl⟩⟩

/-! ## The two entry points: the graph property, or the topology directly -/

/-- **R-a3 from the graph property of the lifts.** -/
theorem htail_of_cylGraph {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (P : Work.EL.CoPair d.hN) (hPy : P.y = d.z₁) (hPa1 : P.a = Work.EL.alpha1)
    (hPb1 : P.b = Work.EL.alpha2) (hside : Work.EL.PairSides d.hN P)
    (L : RayCylLift d fl) {R₀ : ℝ} (hRR₀ : R₀ < L.R)
    (hmono : StrictMono fun s : ℝ => (L.γ₁ s).re)
    (hγ : ∀ w : ℂ, w.re < -R₀ → R₀ < |w.im| → fl.Ψ w ∈ fl.Pa)
    (hPa_far : fl.Pa ⊆ Work.EL.pairSide P) (hPa_ne : fl.Pa.Nonempty)
    (hE : ∀ x : ℝ, fl.Ψ (x : ℂ) ∈ Work.EL.K c) :
    ∃ R' : ℝ, ∀ x : ℝ, x < -R' → fl.Ψ (x : ℂ) ∈ Work.EL.pairSideNear P := by
  obtain ⟨lift⟩ := exists_liftSides_of_cylGraph L hRR₀ hmono hE
  exact equatorTail_mem_near_of_liftSides d fl P hPy hPa1 hPb1 hside L lift hγ hPa_far hPa_ne hE

end Work.ELRig
