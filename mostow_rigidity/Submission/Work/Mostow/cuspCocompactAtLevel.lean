import Mathlib
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.cuspCocoDefs
import Submission.Work.Mostow.horSpec
import Submission.Work.Mostow.hptOf_level
import Submission.Work.Mostow.hptOf_yc
import Submission.Work.Mostow.hptOf_hdist
import Submission.Work.Mostow.levYcFormula
import Submission.Work.Mostow.VolDefs
import Submission.Work.Mostow.cuspCocompactAllLevels
import Submission.Work.Mostow.cuspHoro.packingCount
import Submission.Work.Mostow.cuspHoro.voronoiDefs
import Submission.Work.Mostow.cuspHoro.voronoiData
import Submission.Work.Mostow.cuspHoro.innerBodySeparated
import Submission.Work.Mostow.cuspHoro.existsTrivialStabilizer
import Submission.Work.Mostow.cuspHoro.horoballDisjointOfSum
import Submission.Work.Mostow.stabFlatAction
import Submission.Work.Mostow.cuspBieberbach
import Submission.Work.Mostow.flatEmbCocompact

/-!
# Area C1 (geomFinite) — `cuspCocompactAtLevel` (chapter G7)

The cusp stabiliser of a lattice acts cocompactly on the horospheres at its fixed point.

This file sets up the horospherical infrastructure used by the classical proof: the stabiliser of
`ξ` preserves the level function `lev ξ = exp ∘ busemann ξ`, the induced action of the stabiliser on
the flat coordinate `yc ξ` of the level-`D` horosphere is *level independent* (so the horospherical
boxes are equivariant for a single Euclidean isometry), and hyperbolic balls have the same volume
everywhere.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {n : ℕ}

/-- The stabiliser of `ξ` preserves the horospherical levels at `ξ` (Busemann cocycle identity plus
the vanishing of the cocycle on the stabiliser). -/
theorem lev_smul_of_bd (hA : POActionProp n) (hI : HypIsometryProp n) (Γ : Subgroup (PO n 1))
    (ξ : E n) (hξ : ξ ∈ Sph n)
    (hstab : ∀ (γ : Γ), bd (γ : PO n 1) ξ = ξ → bCocy (γ : PO n 1) ξ = 0)
    (γ : Γ) (hγ : bd (γ : PO n 1) ξ = ξ) (u : E n) :
    lev ξ ((γ : PO n 1) • u) = lev ξ u := by
  have hI' : HypIsoData n := HypIsoData.ofProp hI
  have h := hI'.busemann_cocycle (γ : PO n 1) ξ u hξ
  rw [hγ] at h
  have hb : busemann ξ ((γ : PO n 1) • (0 : E n)) = bCocy (γ : PO n 1) ξ := by
    rw [bCocy, hγ]
  have key : busemann ξ ((γ : PO n 1) • u) = busemann ξ u := by
    rw [h, hb, hstab γ hγ, add_zero]
  rw [lev_eq_exp hξ ((γ : PO n 1) • u), lev_eq_exp hξ u, key]

/-- The stabiliser of `ξ` preserves every horoball at `ξ`. -/
theorem horoball_smul_iff (hA : POActionProp n) (hI : HypIsometryProp n) (Γ : Subgroup (PO n 1))
    (ξ : E n) (hξ : ξ ∈ Sph n)
    (hstab : ∀ (γ : Γ), bd (γ : PO n 1) ξ = ξ → bCocy (γ : PO n 1) ξ = 0)
    (γ : Γ) (hγ : bd (γ : PO n 1) ξ = ξ) (t : ℝ) (u : E n) :
    (γ : PO n 1) • u ∈ horoball ξ t ↔ u ∈ horoball ξ t := by
  have h := lev_smul_of_bd hA hI Γ ξ hξ hstab γ hγ u
  have key : busemann ξ ((γ : PO n 1) • u) = busemann ξ u := by
    have h' : Real.exp (busemann ξ ((γ : PO n 1) • u)) = Real.exp (busemann ξ u) := by
      rw [← lev_eq_exp hξ ((γ : PO n 1) • u), ← lev_eq_exp hξ u, h]
    exact Real.exp_injective h'
  simp only [horoball, Set.mem_ofPred_eq]
  rw [key]

/-- **Level independence of the induced flat action.**  If `g` fixes `ξ` and preserves the levels
then the flat coordinate of `g • hptOf ξ y E` does not depend on the level `E`. -/
theorem yc_smul_hptOf_levelIndep (hA : POActionProp n) (hI : HypIsometryProp n)
    (ξ : E n) (hξ : ξ ∈ Sph n) (g : PO n 1) (hg : bd g ξ = ξ)
    (hlev : ∀ u : E n, lev ξ (g • u) = lev ξ u) (y : E n) (hy : inner ℝ y ξ = 0)
    (E₁ E₂ : ℝ) (h₁ : 0 < E₁) (h₂ : 0 < E₂) :
    yc ξ (g • hptOf ξ y E₁) = yc ξ (g • hptOf ξ y E₂) := by
  have hI' : HypIsoData n := HypIsoData.ofProp hI
  have hlev₁ : lev ξ (g • hptOf ξ y E₁) = E₁ := by
    rw [hlev, (hptOf_level ξ hξ E₁ h₁ y hy).1]
  have hlev₂ : lev ξ (g • hptOf ξ y E₂) = E₂ := by
    rw [hlev, (hptOf_level ξ hξ E₂ h₂ y hy).1]
  have hdist_g : hdist (g • hptOf ξ y E₁) (g • hptOf ξ y E₂)
      = hdist (hptOf ξ y E₁) (hptOf ξ y E₂) := hI'.isom_smul g _ _
  have hform₁ := levYcFormula hξ (g • hptOf ξ y E₁) (g • hptOf ξ y E₂)
  have hform₂ := levYcFormula hξ (hptOf ξ y E₁) (hptOf ξ y E₂)
  rw [hlev₁, hlev₂] at hform₁
  rw [(hptOf_level ξ hξ E₁ h₁ y hy).1, (hptOf_level ξ hξ E₂ h₂ y hy).1,
    (hptOf_level ξ hξ E₁ h₁ y hy).2, (hptOf_level ξ hξ E₂ h₂ y hy).2] at hform₂
  rw [hdist_g, hform₂] at hform₁
  simp only [sub_self, norm_zero, mul_zero, add_zero] at hform₁
  have hE : (0:ℝ) < E₁ * E₂ / 2 := by positivity
  have hkey : ‖yc ξ (g • hptOf ξ y E₁) - yc ξ (g • hptOf ξ y E₂)‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖yc ξ (g • hptOf ξ y E₁) - yc ξ (g • hptOf ξ y E₂)‖ ^ 2 :=
      pow_pos (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)) 2
    nlinarith [hform₁]
  exact sub_eq_zero.mp (norm_eq_zero.mp hkey)


/-- Sharpening of `horSpec`: the induced flat action of a level preserving isometry fixing `ξ` is
valid at *every* level. -/
theorem exists_rho_levelIndep (hA : POActionProp n) (hI : HypIsometryProp n) (ξ : E n)
    (hξ : ξ ∈ Sph n) (g : PO n 1) (hg : bd g ξ = ξ)
    (hlev : ∀ u : E n, lev ξ (g • u) = lev ξ u) :
    ∃ ρ : E n → E n,
      (∀ y : E n, inner ℝ y ξ = 0 → inner ℝ (ρ y) ξ = 0) ∧
      (∀ y : E n, inner ℝ y ξ = 0 → ∀ E : ℝ, 0 < E →
        hptOf ξ (ρ y) E = g • hptOf ξ y E) ∧
      (∀ y y' : E n, inner ℝ y ξ = 0 → inner ℝ y' ξ = 0 → ‖ρ y - ρ y'‖ = ‖y - y'‖) ∧
      (∀ y : E n, inner ℝ y ξ = 0 → ∃ y₀ : E n, inner ℝ y₀ ξ = 0 ∧ ρ y₀ = y) := by
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      have h1 : ‖ξ‖ = 1 := by
        simpa [Sph, Metric.mem_sphere, dist_eq_norm] using hξ
      have h2 : ‖ξ‖ = (0 : ℝ) := by
        have hz : ξ = 0 := Subsingleton.elim ξ 0
        rw [hz]; simp
      rw [h2] at h1
      norm_num at h1
    · exact h
  obtain ⟨-, -, -, ρ, hρ, hdistρ, hsurj⟩ :=
    horSpec n hn1 hA hI ξ hξ 1 one_pos g hg hlev
  refine ⟨ρ, fun y hy => (hρ y hy).1, ?_, hdistρ, hsurj⟩
  intro y hy E hE
  have h1 : yc ξ (g • hptOf ξ y E) = yc ξ (g • hptOf ξ y 1) :=
    yc_smul_hptOf_levelIndep hA hI ξ hξ g hg hlev y hy E 1 hE one_pos
  have h2 : yc ξ (g • hptOf ξ y E) = ρ y := by
    rw [h1, ← (hρ y hy).2]
    exact (hptOf_level ξ hξ 1 one_pos (ρ y) (hρ y hy).1).2
  have hlevE : lev ξ (g • hptOf ξ y E) = E := by
    rw [hlev, (hptOf_level ξ hξ E hE y hy).1]
  have hu := hptOf_yc ξ hξ (lev ξ (g • hptOf ξ y E))
    (lev_pos ξ hξ (g • hptOf ξ y E)) (g • hptOf ξ y E) rfl
  rw [h2, hlevE] at hu
  exact hu


/-- The induced flat action computes the flat coordinate of the image: `yc ξ (g • u) = ρ (yc ξ u)`. -/
theorem yc_smul_eq (hA : POActionProp n) (hI : HypIsometryProp n) (ξ : E n) (hξ : ξ ∈ Sph n)
    (g : PO n 1) (ρ : E n → E n)
    (hρ : ∀ y : E n, inner ℝ y ξ = 0 → ∀ E : ℝ, 0 < E → hptOf ξ (ρ y) E = g • hptOf ξ y E)
    (hρorth : ∀ y : E n, inner ℝ y ξ = 0 → inner ℝ (ρ y) ξ = 0) (u : E n) :
    yc ξ (g • u) = ρ (yc ξ u) := by
  have hlevu : 0 < lev ξ u := lev_pos ξ hξ u
  have hu : hptOf ξ (yc ξ u) (lev ξ u) = u :=
    hptOf_yc ξ hξ (lev ξ u) hlevu u rfl
  have hrepr : g • u = hptOf ξ (ρ (yc ξ u)) (lev ξ u) := by
    calc g • u = g • hptOf ξ (yc ξ u) (lev ξ u) := by rw [hu]
      _ = hptOf ξ (ρ (yc ξ u)) (lev ξ u) :=
        (hρ (yc ξ u) (yc_inner_orth hξ) (lev ξ u) hlevu).symm
  rw [hrepr, (hptOf_level ξ hξ (lev ξ u) hlevu (ρ (yc ξ u))
    (hρorth (yc ξ u) (yc_inner_orth hξ))).2]

/-- The horospherical boxes are equivariant for the induced flat action: the translate of the box
over `A` is the box over the preimage of `A`. -/
theorem mem_hbox_smul (hA : POActionProp n) (hI : HypIsometryProp n) (ξ : E n) (hξ : ξ ∈ Sph n)
    (g : PO n 1) (hg : bd g ξ = ξ) (hlev : ∀ u : E n, lev ξ (g • u) = lev ξ u)
    (ρ : E n → E n)
    (hρ : ∀ y : E n, inner ℝ y ξ = 0 → ∀ E : ℝ, 0 < E → hptOf ξ (ρ y) E = g • hptOf ξ y E)
    (hρorth : ∀ y : E n, inner ℝ y ξ = 0 → inner ℝ (ρ y) ξ = 0)
    (A : Set (E n)) (I : Set ℝ) (u : E n) :
    g • u ∈ hbox ξ A I ↔ u ∈ hbox ξ {y : E n | ρ y ∈ A} I := by
  simp only [hbox, Set.mem_ofPred_eq]
  rw [yc_smul_eq hA hI ξ hξ g ρ hρ hρorth u, hlev u]


namespace cuspHoro

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

set_option maxHeartbeats 1600000

theorem packingCountStab (n : ℕ) (hA : POActionProp n) (hI : HypIsometryProp n)
    (Γ : Subgroup (PO n 1)) (ξ : E n) (hξ : ξ ∈ Sph n) (hξP : ξ ∈ parFixed Γ)
    (hstab : ∀ (γ : Γ), bd (γ : PO n 1) ξ = ξ → bCocy (γ : PO n 1) ξ = 0)
    (hdisc : IsDiscrete (SetLike.coe Γ))
    (D τ r δ : ℝ) (hD : 0 < D) (hr : 0 < r) (hδ : 0 < δ)
    (hemb : ∀ (γ : Γ), bd (γ : PO n 1) ξ ≠ ξ →
      Disjoint (horoball ξ τ) (horoball (bd (γ : PO n 1) ξ) (τ + bCocy (γ : PO n 1) ξ)))
    (hleτ : Real.log D + r ≤ τ)
    (hsep : 2 * r ≤ Real.arcosh (1 + (D * δ) ^ 2 / 2))
    (Df : Set (E n)) (hDfm : IsFundamentalDomain Γ Df (volH n)) (hDfin : volH n Df ≠ ⊤)
    (S : Finset (xiPerp ξ))
    (hS : ∀ (s : xiPerp ξ), s ∈ S → ∀ (s' : xiPerp ξ), s' ∈ S →
        ∀ g : ↥(stabSub (POBasic.ofProp hA) Γ ξ hξ), (s, g) ≠ (s', 1) →
        δ ≤ dist s (cuspFlatHom (POBasic.ofProp hA) (HypIsoData.ofProp hI) hξ D hD
          (stabSub (POBasic.ofProp hA) Γ ξ hξ)
          (fun g hg u => lev_smul_of_bd hA hI Γ ξ hξ hstab ⟨g, hg.1⟩ hg.2 u)
          g s')) :
    (S.card : ℝ≥0∞) * volH n (hBall (0 : E n) r) ≤ volH n Df := by
  have hA' : POBasic n := POBasic.ofProp hA
  have hI' : HypIsoData n := HypIsoData.ofProp hI
  let G : Subgroup (PO n 1) := stabSub hA' Γ ξ hξ
  let hlev : ∀ g ∈ G, ∀ u : E n, lev ξ (g • u) = lev ξ u :=
    fun g hg u => lev_smul_of_bd hA hI Γ ξ hξ hstab ⟨g, hg.1⟩ hg.2 u
  let ρ : G →* (xiPerp ξ ≃ᵢ xiPerp ξ) := cuspFlatHom hA' hI' hξ D hD G hlev
  -- basic geometry of the level-`D` horosphere
  have hcentre_lev : ∀ s : xiPerp ξ, lev ξ (hptOf ξ (s : E n) D) = D := fun s =>
    (hptOf_level ξ hξ D hD (s : E n)
      (by rw [real_inner_comm]; exact mem_xiPerp_iff.mp s.2)).1
  have hcentre_bus : ∀ s : xiPerp ξ, busemann ξ (hptOf ξ (s : E n) D) = Real.log D := by
    intro s
    have h := lev_eq_exp hξ (hptOf ξ (s : E n) D)
    rw [hcentre_lev s] at h
    have h2 := congrArg Real.log h
    rw [Real.log_exp] at h2
    exact h2.symm
  have hsubtype_dist : ∀ s s' : xiPerp ξ, dist s s' = ‖(s : E n) - (s' : E n)‖ := by
    intro s s'; rw [Subtype.dist_eq, dist_eq_norm]
  have hhyp : ∀ s s' : xiPerp ξ,
      hdist (hptOf ξ (s : E n) D) (hptOf ξ (s' : E n) D)
        = Real.arcosh (1 + (D * ‖(s : E n) - (s' : E n)‖) ^ 2 / 2) := by
    intro s s'
    rw [hptOf_hdist ξ hξ D hD (s : E n) (s' : E n)
      (by rw [real_inner_comm]; exact mem_xiPerp_iff.mp s.2)
      (by rw [real_inner_comm]; exact mem_xiPerp_iff.mp s'.2)]
  have hmono : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b →
      2 * r ≤ Real.arcosh (1 + (D * a) ^ 2 / 2) → 2 * r ≤ Real.arcosh (1 + (D * b) ^ 2 / 2) := by
    intro a b ha hab h
    have h2 : (D * a) ^ 2 ≤ (D * b) ^ 2 := by
      have h3 : D * a ≤ D * b := mul_le_mul_of_nonneg_left hab (le_of_lt hD)
      nlinarith [h3, mul_nonneg (le_of_lt hD) ha, mul_nonneg (le_of_lt hD) (le_trans ha hab)]
    exact le_trans h ((Real.arcosh_le_arcosh (by positivity) (by positivity)).mpr (by linarith))
  -- separation of the centres
  have hcentres : ∀ (s : xiPerp ξ) (hs : s ∈ S) (s' : xiPerp ξ) (hs' : s' ∈ S) (g : ↥G),
      (s, g) ≠ (s', 1) →
      2 * r ≤ hdist (hptOf ξ (s : E n) D) (hptOf ξ ((ρ g s' : xiPerp ξ) : E n) D) := by
    intro s hs s' hs' g hcond
    have hd : δ ≤ ‖(s : E n) - (ρ g s' : xiPerp ξ)‖ := by
      have h := hS s hs s' hs' g hcond
      rwa [hsubtype_dist s (ρ g s')] at h
    rw [hhyp s (ρ g s')]
    exact hmono (le_of_lt hδ) hd hsep
  -- a translate of a ball is a ball
  have hsmul_ball : ∀ (s : xiPerp ξ) (g : ↥G),
      (g : PO n 1) • hBall (hptOf ξ (s : E n) D) r
        = hBall (hptOf ξ ((ρ g s : xiPerp ξ) : E n) D) r := by
    intro s g
    rw [smul_hBall hA' hI']
    exact congrArg (fun w : E n => hBall w r) (smul_hptOf hA' hI' D hD G hlev g.2 s)
  -- the set
  let A : Set (E n) := ⋃ s ∈ (S : Set (xiPerp ξ)), hBall (hptOf ξ (s : E n) D) r
  have hA_sub : A ⊆ horoball ξ τ := by
    intro u hu
    simp only [A, Set.mem_iUnion, Set.mem_setOf_eq] at hu
    obtain ⟨s, -, hus⟩ := hu
    simp only [hBall, Set.mem_ofPred_eq] at hus
    simp only [horoball, Set.mem_ofPred_eq]
    have h := BusemannLipschitz n ξ hξ (hptOf ξ (s : E n) D) u
    have h2 : busemann ξ u - busemann ξ (hptOf ξ (s : E n) D)
        ≤ hdist (hptOf ξ (s : E n) D) u := by
      have h3 : busemann ξ u - busemann ξ (hptOf ξ (s : E n) D)
          ≤ |busemann ξ u - busemann ξ (hptOf ξ (s : E n) D)| := le_abs_self _
      rw [abs_sub_comm] at h3
      linarith
    rw [hcentre_bus s] at h2
    linarith
  have hAmeas : NullMeasurableSet A (volH n) := by
    have hopen : ∀ s : xiPerp ξ, IsOpen (hBall (hptOf ξ (s : E n) D) r) := fun s =>
      isOpen_lt (hdist_continuous_left (hptOf ξ (s : E n) D)) continuous_const
    have h1 : A = ⋃ s ∈ (S : Set (xiPerp ξ)), hBall (hptOf ξ (s : E n) D) r := rfl
    rw [h1]
    exact (isOpen_biUnion fun s _ => hopen s).measurableSet.nullMeasurableSet
  have hdisj : ∀ γ : Γ, γ ≠ 1 →
      AEDisjoint (volH n) ((fun x => (γ : PO n 1) • x) '' A) A := by
    intro γ hγ1
    by_cases hgG : (γ : PO n 1) ∈ G
    · refine Disjoint.aedisjoint ?_
      rw [Set.disjoint_left]
      intro x hx hxA
      obtain ⟨y, hyA, hyx⟩ := hx
      have hx1 := hxA
      simp only [A, Set.mem_iUnion, Set.mem_ofPred_eq] at hx1
      obtain ⟨s', hs', hs'x⟩ := hx1
      have hy1 := hyA
      simp only [A, Set.mem_iUnion, Set.mem_ofPred_eq] at hy1
      obtain ⟨s, hs, hys⟩ := hy1
      have hsS : s ∈ S := by simpa using hs
      have hs'S : s' ∈ S := by simpa using hs'
      have h3 : (γ : PO n 1) • y
          ∈ hBall (hptOf ξ ((ρ ⟨(γ : PO n 1), hgG⟩ s : xiPerp ξ) : E n) D) r := by
        have h := Set.smul_mem_smul_set (a := (γ : PO n 1)) hys
        rw [smul_hBall hA' hI', smul_hptOf hA' hI' D hD G hlev hgG s] at h
        exact h
      have hne : (s', (⟨(γ : PO n 1), hgG⟩ : ↥G)) ≠ (s, 1) := by
        intro h
        have h2 : (γ : PO n 1) = 1 := by
          have := congrArg (fun z : xiPerp ξ × ↥G => ((z.2 : ↥G) : PO n 1)) h
          simpa using this
        exact hγ1 (Subtype.ext h2)
      have h2r := hcentres s' hs'S s hsS ⟨(γ : PO n 1), hgG⟩ hne
      have h3' : x ∈ hBall (hptOf ξ ((ρ ⟨(γ : PO n 1), hgG⟩ s : xiPerp ξ) : E n) D) r := by
        rw [← hyx]; exact h3
      exact Set.disjoint_left.mp (hBall_disjoint hI' h2r) hs'x h3'
    · refine Disjoint.aedisjoint ?_
      have hbd : bd (γ : PO n 1) ξ ≠ ξ := fun h => hgG ⟨γ.2, h⟩
      have hdisj : Disjoint (horoball ξ τ)
          (horoball (bd (γ : PO n 1) ξ) (τ + bCocy (γ : PO n 1) ξ)) := hemb γ hbd
      have hsub : (γ : PO n 1) • A ⊆ horoball (bd (γ : PO n 1) ξ) (τ + bCocy (γ : PO n 1) ξ) := by
        intro u hu
        obtain ⟨v, hv, rfl⟩ := hu
        have hv' : busemann ξ v < τ := hA_sub hv
        have hcoc := hI'.busemann_cocycle (γ : PO n 1) ξ v hξ
        simp only [horoball, Set.mem_ofPred_eq, bCocy]
        rw [hcoc]
        linarith
      exact ((hdisj.symm).mono_left hsub).mono_right hA_sub
  have hbound : volH n A ≤ volH n Df :=
    volH_le_of_isFundamentalDomain hA hI hdisc hDfm hAmeas hdisj
  have hpairwise : ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' →
      Disjoint (hBall (hptOf ξ (s : E n) D) r) (hBall (hptOf ξ (s' : E n) D) r) := by
    intro s hs s' hs' hne
    refine hBall_disjoint hI' ?_
    have h := hcentres s hs s' hs' 1 (by
      intro hcon
      exact hne (congrArg Prod.fst hcon))
    have h1 : (ρ 1 : xiPerp ξ ≃ᵢ xiPerp ξ) s' = s' := by rw [map_one]; rfl
    rw [h1] at h
    exact h
  have hvol_le : (S.card : ℝ≥0∞) * volH n (hBall (0 : E n) r) ≤ volH n A := by
    have hopen : ∀ s : xiPerp ξ, MeasurableSet (hBall (hptOf ξ (s : E n) D) r) := fun s =>
      (isOpen_lt (hdist_continuous_left (hptOf ξ (s : E n) D)) continuous_const).measurableSet
    have h1 : A = ⋃ s ∈ (S : Set (xiPerp ξ)), hBall (hptOf ξ (s : E n) D) r := rfl
    rw [h1]
    rw [measure_biUnion (μ := volH n) S.finite_toSet.countable
      (fun s hs s' hs' hne => hpairwise s (by simpa using hs) s' (by simpa using hs') hne)
      (fun s hs => hopen s)]
    rw [tsum_fintype]
    simp only [volH_hBall_homogeneous hA hI, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Finset.coe_sort_coe]
    rw [Fintype.card_coe]
  exact le_trans hvol_le hbound


theorem flatCocompactStab (n : ℕ) (hn : 2 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (Γ : Subgroup (PO n 1)) (hΓ : HypLattice Γ) (ξ : E n) (hξP : ξ ∈ parFixed Γ)
    (hstab : ∀ (γ : Γ), bd (γ : PO n 1) ξ = ξ → bCocy (γ : PO n 1) ξ = 0)
    (τ : ℝ)
    (hemb : ∀ (γ : Γ), bd (γ : PO n 1) ξ ≠ ξ →
      Disjoint (horoball ξ τ) (horoball (bd (γ : PO n 1) ξ) (τ + bCocy (γ : PO n 1) ξ))) :
    ∃ K : Set (E n), IsCompact K ∧ ∀ u : E n, lev ξ u = 1 →
      ∃ γ : Γ, bd (γ : PO n 1) ξ = ξ ∧ (γ : PO n 1) • u ∈ K := by
  classical
  have hA' : POBasic n := POBasic.ofProp hA
  have hI' : HypIsoData n := HypIsoData.ofProp hI
  have hξ : ξ ∈ Sph n := hξP.1
  have hdisc : IsDiscrete (SetLike.coe Γ) := hΓ.1
  obtain ⟨Df, hDfm, hDfin⟩ := hΓ.2
  -- the cusp stabiliser and its level preservation
  let G : Subgroup (PO n 1) := stabSub hA' Γ ξ hξ
  let hlev : ∀ g ∈ G, ∀ u : E n, lev ξ (g • u) = lev ξ u :=
    fun g hg u => lev_smul_of_bd hA hI Γ ξ hξ hstab ⟨g, hg.1⟩ hg.2 u
  -- the level of the flat action and the flat action itself
  let D : ℝ := Real.exp (τ - 1)
  have hDpos : 0 < D := Real.exp_pos _
  let ρ : G →* (E (CuspB.fdim ξ) ≃ᵢ E (CuspB.fdim ξ)) := CuspB.rhoHom hA' hI ξ hξ D hDpos G hlev
  -- properness of the flat action
  have hpropΓ : ∀ u₀ : E n, lev ξ u₀ = D → ∀ K : Set (E n), IsCompact K →
      {g : G | (g : PO n 1) • u₀ ∈ K}.Finite := by
    intro u₀ _ K hK
    exact (properActionChartEmb n hA hI Γ hdisc u₀ K hK).preimage
      (f := fun g : G => (⟨(g : PO n 1), g.2.1⟩ : Γ))
      (fun a _ b _ hab => Subtype.ext (congrArg (fun z : Γ => (z : PO n 1)) hab))
  have hproper : ∀ K : Set (E (CuspB.fdim ξ)), IsCompact K →
      {g : G | ((ρ g) '' K ∩ K).Nonempty}.Finite :=
    CuspB.rhoHom_proper hA' hI ξ hξ D hDpos G hlev hpropΓ
  -- faithfulness of the flat action
  have hinj : ∀ g : G, ρ g = 1 → g = 1 := fun g => CuspB.rhoHom_ker hA' hI ξ hξ D hDpos G hlev g
  -- countability of the cusp stabiliser
  haveI : Countable Γ := (countable_of_isDiscrete (PO n 1) hdisc).to_subtype
  haveI : Countable G := Function.Injective.countable
    (f := fun g : G => (⟨(g : PO n 1), g.2.1⟩ : Γ))
    (fun a b hab => Subtype.ext (congrArg (fun z : Γ => (z : PO n 1)) hab))
  -- a base point with trivial stabiliser
  obtain ⟨x₀, hx₀⟩ := existsTrivialStabilizer (ρ := ρ) hinj
  -- the Dirichlet cell of `x₀` and the separation properties
  obtain ⟨hconv, hcover, hsep⟩ := voronoiData ρ hproper x₀ hx₀
  -- ----------------------------------------------------------------------
  -- Step 1: the injectivity radius of the orbit of `x₀`
  -- ----------------------------------------------------------------------
  have hSfin : {g : G | dist x₀ (ρ g x₀) ≤ 1}.Finite := by
    refine (hproper (Metric.closedBall x₀ 1) (isCompact_closedBall x₀ 1)).subset ?_
    intro g hg
    refine ⟨ρ g x₀, ⟨⟨x₀, Metric.mem_closedBall_self (by norm_num), rfl⟩, ?_⟩⟩
    rw [Metric.mem_closedBall, dist_comm]
    exact hg
  obtain ⟨r₀, hr₀pos, hr₀le⟩ : ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ g : G, g ≠ 1 → r₀ ≤ dist x₀ (ρ g x₀) := by
    by_cases hne : (hSfin.toFinset.filter (fun g => g ≠ 1)).Nonempty
    · set T : Finset ℝ := (hSfin.toFinset.filter (fun g => g ≠ 1)).image
          (fun g => dist x₀ (ρ g x₀)) with hT
      have hTne : T.Nonempty := by rw [hT]; exact Finset.image_nonempty.mpr hne
      have hTmem : ∀ v ∈ T, ∃ g : G, g ≠ 1 ∧ v = dist x₀ (ρ g x₀) ∧
          dist x₀ (ρ g x₀) ≤ 1 := by
        intro v hv
        rw [hT, Finset.mem_image] at hv
        obtain ⟨g, hg, hgv⟩ := hv
        rw [Finset.mem_filter] at hg
        exact ⟨g, hg.2, hgv.symm, (Set.Finite.mem_toFinset hSfin).1 hg.1⟩
      refine ⟨T.min' hTne, ?_, ?_⟩
      · obtain ⟨g, hg1, hgv, -⟩ := hTmem _ (Finset.min'_mem T hTne)
        rw [hgv]
        refine lt_of_le_of_ne dist_nonneg (Ne.symm ?_)
        intro h0
        exact hx₀ g hg1 (dist_eq_zero.mp h0).symm
      · intro g hg1
        by_cases hle : dist x₀ (ρ g x₀) ≤ 1
        · have hmem : dist x₀ (ρ g x₀) ∈ T := by
            rw [hT, Finset.mem_image]
            exact ⟨g, by rw [Finset.mem_filter, Set.Finite.mem_toFinset]; exact ⟨hle, hg1⟩, rfl⟩
          exact Finset.min'_le T _ hmem
        · obtain ⟨g', hg'1, hg'v, hg'le⟩ := hTmem _ (Finset.min'_mem T hTne)
          have h1 : T.min' hTne ≤ 1 := by rw [hg'v]; exact hg'le
          exact le_trans h1 (le_of_lt (not_le.mp hle))
    · refine ⟨1, one_pos, ?_⟩
      intro g hg1
      by_contra hlt
      exact hne ⟨g, by
        rw [Finset.mem_filter, Set.Finite.mem_toFinset]
        exact ⟨le_of_lt (not_le.mp hlt), hg1⟩⟩
  have hr₀half : 0 < r₀ / 2 := by linarith
  have hr₀quarter : 0 < r₀ / 4 := by linarith
  -- ----------------------------------------------------------------------
  -- Step 2: the inner parallel body of the Dirichlet cell is nonempty
  -- ----------------------------------------------------------------------
  have hne_ib : (innerBody (r₀ / 2) (cell ρ x₀)).Nonempty := by
    refine ⟨x₀, fun z hz g => ?_⟩
    by_cases hg1 : g = 1
    · rw [hg1, map_one]
      exact le_refl _
    · have h1 : r₀ ≤ dist x₀ (ρ g x₀) := hr₀le g hg1
      have h2 : dist x₀ (ρ g x₀) ≤ dist z x₀ + dist z (ρ g x₀) := by
        have h := dist_triangle x₀ z (ρ g x₀)
        rwa [dist_comm x₀ z] at h
      have h3 : dist z x₀ < r₀ / 2 := by rw [dist_comm]; exact hz
      linarith
  -- ----------------------------------------------------------------------
  -- Step 3: the flat action is cocompact
  -- ----------------------------------------------------------------------
  set r : ℝ := min (1 / 2) ((1 / 2) * Real.arcosh (1 + (D * (r₀ / 2)) ^ 2 / 2)) with hrdef
  have hrpos : 0 < r := by
    rw [hrdef]
    refine lt_min (by norm_num) ?_
    refine mul_pos (by norm_num) ?_
    refine Real.arcosh_pos ?_
    have hDne : D * (r₀ / 2) ≠ 0 := mul_ne_zero (ne_of_gt hDpos) (by linarith)
    nlinarith [sq_pos_of_ne_zero hDne]
  have hlogD : Real.log D = τ - 1 := by
    rw [show D = Real.exp (τ - 1) from rfl, Real.log_exp]
  have hleτ : Real.log D + r ≤ τ := by
    rw [hlogD]
    have hr1 : r ≤ 1 / 2 := by rw [hrdef]; exact min_le_left _ _
    linarith
  have hsep2 : 2 * r ≤ Real.arcosh (1 + (D * (r₀ / 2)) ^ 2 / 2) := by
    have hr2 : r ≤ (1 / 2) * Real.arcosh (1 + (D * (r₀ / 2)) ^ 2 / 2) := by
      rw [hrdef]; exact min_le_right _ _
    linarith
  have hcoc : ∃ R : ℝ, ∀ x : E (CuspB.fdim ξ), ∃ g : G, dist (ρ g x) x₀ ≤ R := by
    by_contra hcon
    push Not at hcon
    have hunbdd : ¬ Bornology.IsBounded (cell ρ x₀) := by
      intro hbdd
      obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall x₀).1 hbdd
      obtain ⟨x, hx⟩ := hcon R
      obtain ⟨g, hg⟩ := hcover x
      exact absurd (hR hg) (not_le.mpr (hx g))
    -- the packing bound for every `N`
    have hpack : ∀ N : ℕ, (N : ℝ≥0∞) * volH n (hBall (0 : E n) r) ≤ volH n Df := by
      intro N
      obtain ⟨S, hScard, hSsub, hSsep⟩ :=
        innerBodySeparated (cell ρ x₀) hconv (η := r₀ / 2) hr₀half hne_ib hunbdd
          (ε := r₀ / 4) hr₀quarter N
      have hmem : ∀ w ∈ S, w ∈ innerBody (r₀ / 4) (cell ρ x₀) := by
        intro w hw
        have h := hSsub w hw
        rwa [show r₀ / 2 / 2 = r₀ / 4 by ring] at h
      have hpc := packingCountStab n hA hI Γ ξ hξ hξP hstab hdisc D τ r (r₀ / 2) hDpos hrpos
        hr₀half hemb hleτ hsep2 Df hDfm hDfin (S.image (CuspB.fIso ξ)) ?_
      · rwa [Finset.card_image_of_injective S (CuspB.fIso ξ).injective, hScard] at hpc
      · intro s hs s' hs' g hne
        obtain ⟨y, hyS, hy⟩ := Finset.mem_image.mp hs
        obtain ⟨y', hyS', hy'⟩ := Finset.mem_image.mp hs'
        rw [← hy, ← hy']
        by_cases hg1 : g = 1
        · subst hg1
          have hne' : CuspB.fIso ξ y ≠ CuspB.fIso ξ y' := by
            intro h
            exact hne (by rw [← hy, ← hy', h])
          have hyy' : y ≠ y' := fun h => hne' (by rw [h])
          have hs' := hSsep y hyS y' hyS' hyy'
          have hone : cuspFlatHom hA' (HypIsoData.ofProp hI) hξ D hDpos G hlev (1 : G)
              (CuspB.fIso ξ y') = CuspB.fIso ξ y' := by
            rw [map_one]
            rfl
          rw [hone, IsometryEquiv.dist_eq]
          linarith
        · have hsep' := hsep (ε := r₀ / 4) hr₀quarter (g := g) hg1 (hmem y hyS) (hmem y' hyS')
          have hρg : cuspFlatHom hA' (HypIsoData.ofProp hI) hξ D hDpos G hlev g (CuspB.fIso ξ y')
              = CuspB.fIso ξ (ρ g y') := by
            rw [CuspB.rhoHom_apply_eq hA' hI ξ hξ D hDpos G hlev g,
              IsometryEquiv.apply_symm_apply]
            rfl
          have hkey : dist (CuspB.fIso ξ y)
              (cuspFlatHom hA' (HypIsoData.ofProp hI) hξ D hDpos G hlev g (CuspB.fIso ξ y'))
              = dist y (ρ g y') := by
            rw [hρg]
            exact IsometryEquiv.dist_eq (CuspB.fIso ξ) y (ρ g y')
          rw [hkey]
          linarith
    -- the packing bound contradicts finite volume
    obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, volH n Df < (N₀ : ℝ≥0∞) * volH n (hBall (0 : E n) r) := by
      by_cases hvtop : volH n (hBall (0 : E n) r) = ⊤
      · refine ⟨1, ?_⟩
        rw [hvtop]
        simpa using (lt_top_iff_ne_top.mpr hDfin : volH n Df < ⊤)
      · have hvpos : volH n (hBall (0 : E n) r) ≠ 0 :=
          (volHPosOpen n (isOpen_lt (hdist_continuous_left 0) continuous_const)
            ⟨0, by
              simp only [hBall, Set.mem_ofPred_eq]
              rw [hdist_self]
              exact hrpos⟩).ne'
        obtain ⟨N₀, hN₀⟩ := ENNReal.exists_nat_gt
          (r := volH n Df * (volH n (hBall (0 : E n) r))⁻¹)
          (ENNReal.mul_ne_top hDfin (ENNReal.inv_ne_top.mpr hvpos))
        refine ⟨N₀, ?_⟩
        have hmul := ENNReal.mul_lt_mul_left hvpos hvtop hN₀
        have hL : volH n Df * (volH n (hBall (0 : E n) r))⁻¹ * volH n (hBall (0 : E n) r)
            = volH n Df := by
          rw [mul_assoc, ENNReal.inv_mul_cancel hvpos hvtop, mul_one]
        rwa [hL] at hmul
    exact absurd (hpack N₀) (not_le.mpr hN₀)
  obtain ⟨R, hR⟩ := hcoc
  -- ----------------------------------------------------------------------
  -- Step 4: reduction to the level-one horosphere
  -- ----------------------------------------------------------------------
  set M : ℝ := R + ‖x₀‖ with hMdef
  refine ⟨Metric.closedBall (0 : E n) (M + M ^ 2 / 2), isCompact_closedBall _ _, ?_⟩
  intro u hu
  have hyc0 : inner ℝ (yc ξ u) ξ = 0 := inner_yc hξ u
  let y : xiPerp ξ := ⟨yc ξ u, mem_xiPerp_iff.mpr (by rw [real_inner_comm]; exact hyc0)⟩
  obtain ⟨g, hg⟩ := hR ((CuspB.fIso ξ).symm y)
  refine ⟨⟨(g : PO n 1), g.2.1⟩, g.2.2, ?_⟩
  have hbC : bCocy (g : PO n 1) ξ = 0 := hstab ⟨(g : PO n 1), g.2.1⟩ g.2.2
  have hβ : busemann ξ ((g : PO n 1) • (0 : E n)) = 0 := by
    have h1 : busemann ξ ((g : PO n 1) • (0 : E n)) = bCocy (g : PO n 1) ξ := by
      rw [bCocy, g.2.2]
    rw [h1, hbC]
  obtain ⟨A, v, hv, hAperp, hAnorm, hpt⟩ :=
    stabFlatAction n hA hI ξ hξ (g : PO n 1) g.2.2 hβ
  have heq1 : yc ξ ((g : PO n 1) • hptOf ξ (yc ξ u) D) = A (yc ξ u) + v :=
    (hpt (yc ξ u) D hyc0 hDpos).2
  have heq2 : yc ξ ((g : PO n 1) • hptOf ξ (yc ξ u) 1) = A (yc ξ u) + v :=
    (hpt (yc ξ u) 1 hyc0 one_pos).2
  have hu_hpt : hptOf ξ (yc ξ u) 1 = u := by
    have h := hptOf_yc_lev hξ u
    rwa [hu] at h
  have hyc_eq : yc ξ ((g : PO n 1) • u) = yc ξ ((g : PO n 1) • hptOf ξ (yc ξ u) D) := by
    have h2' : yc ξ ((g : PO n 1) • u) = yc ξ ((g : PO n 1) • hptOf ξ (yc ξ u) 1) := by
      rw [hu_hpt]
    rw [h2', heq2, heq1]
  have hflat : ((flatFun hξ D (g : PO n 1) y : xiPerp ξ) : E n) = yc ξ ((g : PO n 1) • u) := by
    rw [flatFun_coe]
    show yc ξ ((g : PO n 1) • hptOf ξ (yc ξ u) D) = yc ξ ((g : PO n 1) • u)
    exact hyc_eq.symm
  have hycbound : ‖yc ξ ((g : PO n 1) • u)‖ ≤ M := by
    rw [← hflat, Submodule.norm_coe]
    have h1 : ρ g ((CuspB.fIso ξ).symm y) = (CuspB.fIso ξ).symm (flatFun hξ D (g : PO n 1) y) := by
      rw [CuspB.rhoHom_apply_eq hA' hI ξ hξ D hDpos G hlev g, IsometryEquiv.apply_symm_apply]
    have h2 : ‖ρ g ((CuspB.fIso ξ).symm y)‖ ≤ M := by
      have h3 := dist_triangle (ρ g ((CuspB.fIso ξ).symm y)) x₀ (0 : E (CuspB.fdim ξ))
      rw [dist_zero_right, dist_zero_right] at h3
      rw [hMdef]
      linarith [h3, hg]
    rwa [h1, CuspB.fIso_symm_norm] at h2
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  have hlevg : lev ξ ((g : PO n 1) • u) = 1 := by
    rw [hlev g g.2 u, hu]
  have hptg : hptOf ξ (yc ξ ((g : PO n 1) • u)) 1 = (g : PO n 1) • u := by
    rw [← hlevg]
    exact hptOf_yc_lev hξ ((g : PO n 1) • u)
  have hξn : ‖ξ‖ = 1 := by
    simpa [Sph, Metric.mem_sphere, dist_eq_norm] using hξ
  rw [← hptg]
  have hptOf_one : hptOf ξ (yc ξ ((g : PO n 1) • u)) 1
      = (‖yc ξ ((g : PO n 1) • u)‖ ^ 2 / 2) • ξ + yc ξ ((g : PO n 1) • u) := by
    unfold hptOf
    have : (1 + 1 ^ 2 * ‖yc ξ ((g : PO n 1) • u)‖ ^ 2) / (2 * 1) - 1 / 2
        = ‖yc ξ ((g : PO n 1) • u)‖ ^ 2 / 2 := by ring
    rw [this, one_smul]
  rw [hptOf_one]
  calc ‖(‖yc ξ ((g : PO n 1) • u)‖ ^ 2 / 2) • ξ + yc ξ ((g : PO n 1) • u)‖
      ≤ ‖(‖yc ξ ((g : PO n 1) • u)‖ ^ 2 / 2) • ξ‖ + ‖yc ξ ((g : PO n 1) • u)‖ :=
        norm_add_le _ _
    _ = ‖yc ξ ((g : PO n 1) • u)‖ ^ 2 / 2 + ‖yc ξ ((g : PO n 1) • u)‖ := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity), hξn, mul_one]
    _ ≤ M + M ^ 2 / 2 := by
        have hM0 : 0 ≤ M := le_trans (norm_nonneg _) hycbound
        nlinarith [hycbound, norm_nonneg (yc ξ ((g : PO n 1) • u)), hM0,
          sq_nonneg (M - ‖yc ξ ((g : PO n 1) • u)‖),
          mul_nonneg (sub_nonneg.mpr hycbound)
            (add_nonneg hM0 (norm_nonneg (yc ξ ((g : PO n 1) • u))))]


end

end cuspHoro

/-- **G7 (the target).**  The stabiliser of `ξ` acts cocompactly on the level set of the horospheres
at `ξ`.  The classical proof bounds the volume of the cusp region `H/Γ_ξ` from above by the volume
of the fundamental domain of `Γ` and from below by the flat covolume of `Γ_ξ` on `ξ^⊥`; finiteness
of the flat covolume implies that the flat action of `Γ_ξ` is cocompact. -/
theorem cuspCocompactAtLevel (n : ℕ) (hn : 2 ≤ n) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n) (hBb : ∀ m, Submission.Mostow.BieberbachProp m)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)) (hΓ : Submission.Mostow.HypLattice Γ)
    (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Work.Mostow.parFixed Γ)
    (hstab : ∀ (γ : Γ), Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
      Work.Mostow.bCocy (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = 0)
    (τ : ℝ) (hemb : ∀ γ : Γ, Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ ≠ ξ →
      Disjoint (Submission.Mostow.horoball ξ τ)
        (Submission.Mostow.horoball (Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ)
          (τ + Work.Mostow.bCocy (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ))) :
    ∃ K : Set (Submission.Mostow.E n), IsCompact K ∧ ∀ u : Submission.Mostow.E n,
      Submission.Mostow.busemann ξ u = τ → ∃ γ : Γ,
        Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ ∧
          (γ : LeanEval.Geometry.MostowRigidity.PO n 1) • u ∈ K := by
  have hξS : ξ ∈ Sph n := hξ.1
  -- Shimizu's lemma is *given* to us as `hemb`: the horoball at level `τ` embeds modulo `Γ`.
  -- Cocompactness of the stabiliser on the level-one horosphere then follows from the
  -- packing/volume argument (`flatCocompactStab`, a restatement of `cuspHoro.flatCocompact`
  -- in which the level preservation of `Γ_ξ` is taken directly from `hstab` instead of from a
  -- global cocycle-vanishing hypothesis).
  obtain ⟨K, hKc, hK⟩ := cuspHoro.flatCocompactStab n hn hA hI Γ hΓ ξ hξ hstab τ hemb
  -- Upgrade the single level (level `0` in the Busemann normalisation) to every level.
  have h0 : ∃ K : Set (E n), IsCompact K ∧ ∀ u : E n, busemann ξ u = 0 →
      ∃ γ : Γ, bd (γ : PO n 1) ξ = ξ ∧ (γ : PO n 1) • u ∈ K := by
    refine ⟨K, hKc, fun u hu => hK u ?_⟩
    rw [lev_eq_exp hξS, hu, Real.exp_zero]
  exact cuspCocompactAllLevels n hA hI Γ ξ hξS hstab 0 h0 τ

end

end Work.Mostow
