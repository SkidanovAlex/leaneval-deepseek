import Mathlib
import Submission.Work.Mostow.geodDeps
import Submission.Work.Mostow.axisDichotomy
import Submission.Work.Mostow.volH_le_fundamentalDomain
import Submission.Work.Mostow.volH_le_card_mul_of_ae_count
import Submission.Work.Mostow.gapA.volH1Ico

/-!
# `Work.Mostow.geeFdTop`: a fixed-point-rich subgroup of `PO 1 1` has infinite covolume

Let `G ≤ PO 1 1` be discrete and suppose every element of `G` has a fixed point in `ℍ¹ = E 1`.
Then any fundamental domain of `G` has infinite hyperbolic volume.

`PO 1 1` is the full isometry group of the geodesic line `ℍ¹`, i.e. the group of maps
`x ↦ ± x + c` in the signed-distance coordinate `sc u = arsinh (u 0)` of the chart (`AxisDich.Phi`).
An isometry has a fixed point only if it is the identity or a reflection `x ↦ c - x`; since the
product of two distinct reflections is a nontrivial translation, `G` contains at most one
nontrivial element.  Hence `G` is finite of cardinality at most `2`, and the standard counting
bound `Work.Mostow.volH_le_card_mul_of_ae_count` turns the identity

`volH 1 univ ≤ 2 * volH 1 DY`

into `volH 1 DY = ⊤`, as `ℍ¹` has infinite volume (the slabs
`{u | u 0 ∈ Ico (-N) N}` have volume `ofReal (2 * arsinh N) → ⊤`).
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

open AxisDich

/-- Two elements of `PO 1 1` inducing the same map of the chart coordinate are equal. -/
private lemma po11_Phi_injective (hA : POBasic 1) (hI : HypIsoData 1) {g h : PO 1 1}
    (hh : ∀ x : ℝ, Phi g x = Phi h x) : g = h := by
  have hsc : ∀ u : E 1, sc (g • u) = sc (h • u) := by
    intro u
    have h1 : Phi g (sc u) = sc (g • u) := by
      rw [show Phi g (sc u) = sc (g • pt (sc u)) from rfl, pt_sc u]
    have h2 : Phi h (sc u) = sc (h • u) := by
      rw [show Phi h (sc u) = sc (h • pt (sc u)) from rfl, pt_sc u]
    rw [← h1, ← h2, hh]
  have hact : ∀ u : E 1, g • u = h • u := fun u => sc_inj hI (hsc u)
  have hg : g⁻¹ * h = 1 := hA.faithful _ (fun u => by
    rw [hA.mul_smul, ← hact u, ← hA.mul_smul, inv_mul_cancel, hA.one_smul])
  calc g = g * 1 := (mul_one g).symm
    _ = g * (g⁻¹ * h) := by rw [hg]
    _ = h := by group

/-- `ℍ¹` has infinite hyperbolic volume. -/
private lemma volH1_univ_eq_top : (volH 1) (Set.univ : Set (E 1)) = ⊤ := by
  -- the vertical slabs `{u | u 0 ∈ Ico (-N) N}` have volume `ofReal (2 * arsinh N)`
  have hslab : ∀ N : ℕ,
      ENNReal.ofReal (2 * Real.arsinh (N : ℝ)) ≤ (volH 1) (Set.univ : Set (E 1)) := by
    intro N
    have hsub : ({v : E 1 | v 0 ∈ Set.Ico (-(N : ℝ)) (N : ℝ)} : Set (E 1)) ⊆ Set.univ :=
      Set.subset_univ _
    have hmono : (volH 1) {v : E 1 | v 0 ∈ Set.Ico (-(N : ℝ)) (N : ℝ)}
        ≤ (volH 1) (Set.univ : Set (E 1)) := measure_mono hsub
    have hAB : -(N : ℝ) ≤ (N : ℝ) := by
      have := Nat.cast_nonneg (α := ℝ) N
      linarith
    rw [gapA.volH1Ico (-(N : ℝ)) (N : ℝ) hAB] at hmono
    have harg : Real.arsinh (N : ℝ) - Real.arsinh (-(N : ℝ)) = 2 * Real.arsinh (N : ℝ) := by
      rw [Real.arsinh_neg]; ring
    rw [harg] at hmono
    exact hmono
  by_contra hne
  have htoReal : ENNReal.ofReal ((volH 1) (Set.univ : Set (E 1))).toReal
      = (volH 1) (Set.univ : Set (E 1)) := ENNReal.ofReal_toReal hne
  obtain ⟨N, hN⟩ :=
    exists_nat_ge (Real.sinh (((volH 1) (Set.univ : Set (E 1))).toReal + 1))
  have hge : ((volH 1) (Set.univ : Set (E 1))).toReal < 2 * Real.arsinh (N : ℝ) := by
    have h1 : Real.arsinh (Real.sinh (((volH 1) (Set.univ : Set (E 1))).toReal + 1))
        ≤ Real.arsinh (N : ℝ) := Real.arsinh_le_arsinh.mpr hN
    rw [Real.arsinh_sinh] at h1
    have ht : (0:ℝ) ≤ ((volH 1) (Set.univ : Set (E 1))).toReal := ENNReal.toReal_nonneg
    linarith
  have hlt : ENNReal.ofReal (((volH 1) (Set.univ : Set (E 1))).toReal)
      < ENNReal.ofReal (2 * Real.arsinh (N : ℝ)) :=
    ENNReal.ofReal_lt_ofReal_iff'.mpr
      ⟨hge, by linarith [ENNReal.toReal_nonneg (a := (volH 1) (Set.univ : Set (E 1)))]⟩
  rw [htoReal] at hlt
  exact absurd (hlt.trans_le (hslab N)) (lt_irrefl _)

theorem geeFdTop
    (hA : Submission.Mostow.POActionProp 1) (hI : Submission.Mostow.HypIsometryProp 1)
    (G : Subgroup (LeanEval.Geometry.MostowRigidity.PO 1 1))
    (hdisc : _root_.IsDiscrete (G : Set (LeanEval.Geometry.MostowRigidity.PO 1 1)))
    (hnone : ∀ g ∈ G, ∃ x : Submission.Mostow.E 1, g • x = x)
    (DY : Set (Submission.Mostow.E 1))
    (hDY : MeasureTheory.IsFundamentalDomain G DY (Submission.Mostow.volH 1)) :
    Submission.Mostow.volH 1 DY = ⊤ := by
  classical
  have hA' : POBasic 1 := POBasic.ofProp hA
  have hI' : HypIsoData 1 := HypIsoData.ofProp hI
  -- Every element of `G` is the identity or a "reflection" `x ↦ c - x` in the chart coordinate.
  have hclass : ∀ g : PO 1 1, g ∈ G → g = 1 ∨ ∃ c : ℝ, ∀ x : ℝ, Phi g x = c - x := by
    intro g hg
    obtain ⟨x, hx⟩ := hnone g hg
    have hfx : Phi g (sc x) = sc x := (Phi_fix_iff hI' g x).mp hx
    rcases Phi_form hI' g with ⟨c, hc | hc⟩
    · left
      have hc0 : c = 0 := by
        have hcx := hc (sc x)
        linarith [hfx]
      refine (Phi_eq_one_iff hA' hI' g).mp (fun y => ?_)
      rw [hc y, hc0, zero_add]
    · exact Or.inr ⟨c, hc⟩
  -- Two nontrivial elements of `G` coincide: a product of two distinct reflections is a
  -- nontrivial translation, which has no fixed point.
  have huniq : ∀ g ∈ G, ∀ h ∈ G, g ≠ 1 → h ≠ 1 → g = h := by
    intro g hg h hh hg1 hh1
    obtain ⟨cg, hcg⟩ : ∃ c, ∀ x, Phi g x = c - x := by
      rcases hclass g hg with h' | h'
      · exact absurd h' hg1
      · exact h'
    obtain ⟨ch, hch⟩ : ∃ c, ∀ x, Phi h x = c - x := by
      rcases hclass h hh with h' | h'
      · exact absurd h' hh1
      · exact h'
    have hce : cg = ch := by
      have hkG : g * h ∈ G := G.mul_mem hg hh
      obtain ⟨z, hz⟩ := hnone (g * h) hkG
      have hfz : Phi (g * h) (sc z) = sc z := (Phi_fix_iff hI' (g * h) z).mp hz
      have hcomp : Phi (g * h) (sc z) = Phi g (Phi h (sc z)) := by
        rw [Phi_mul hA' g h]; rfl
      rw [hcomp, hch (sc z), hcg (ch - sc z)] at hfz
      linarith
    exact po11_Phi_injective hA' hI' (fun x => by rw [hcg x, hch x, hce])
  -- Consequently every point of `ℍ¹` has at most two `G`-translates, i.e. the counting
  -- hypothesis of `volH_le_card_mul_of_ae_count` holds with `N = 2`.
  have hcount : ∀ᵐ z ∂((volH 1).restrict DY),
      ∃ s : Finset G, s.card ≤ 2 ∧
        ∀ γ : G, (γ : PO 1 1) • z ∈ (Set.univ : Set (E 1)) → γ ∈ s := by
    filter_upwards with z
    by_cases hnt : ∃ r ∈ G, r ≠ 1
    · obtain ⟨r, hrG, hrne⟩ := hnt
      refine ⟨({(1 : G), (⟨r, hrG⟩ : G)} : Finset G), Finset.card_le_two, ?_⟩
      intro γ _
      have hγ : (γ : PO 1 1) = 1 ∨ (γ : PO 1 1) = r := by
        rcases hclass γ γ.2 with h1 | _
        · exact Or.inl h1
        · by_cases hγ1 : γ = 1
          · exact Or.inl (by rw [hγ1]; rfl)
          · have hγ1' : (γ : PO 1 1) ≠ 1 := fun h => hγ1 (Subtype.ext h)
            exact Or.inr (huniq γ γ.2 r hrG hγ1' hrne)
      rcases hγ with h' | h'
      · have : γ = 1 := Subtype.ext h'
        rw [this]; simp
      · have : γ = (⟨r, hrG⟩ : G) := Subtype.ext h'
        rw [this]; simp
    · refine ⟨({(1 : G)} : Finset G), by simp, ?_⟩
      intro γ _
      have h1 : (γ : PO 1 1) = 1 := by
        by_contra hne
        exact hnt ⟨(γ : PO 1 1), γ.2, hne⟩
      have : γ = 1 := Subtype.ext h1
      rw [this]; simp
  have hle2 : (volH 1) (Set.univ : Set (E 1)) ≤ 2 * (volH 1) DY :=
    volH_le_card_mul_of_ae_count 1 hA hI G hdisc hDY MeasurableSet.univ 2 hcount
  -- `ℍ¹` has infinite volume, so `2 * volH 1 DY = ⊤`, hence `volH 1 DY = ⊤`.
  have htop : ⊤ ≤ 2 * (volH 1) DY := by
    rw [← volH1_univ_eq_top]
    exact hle2
  by_contra hne
  have hlt : (2 : ℝ≥0∞) * (volH 1) DY < ⊤ :=
    ENNReal.mul_lt_top (by norm_num) (lt_top_iff_ne_top.mpr hne)
  rw [top_le_iff.mp htop] at hlt
  exact absurd hlt (lt_irrefl ⊤)

end

end Work.Mostow
