import Mathlib
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.cuspHoroDefs
import Submission.Work.Mostow.cuspZ2Defs
import Submission.Work.Mostow.flatActBasic
import Submission.Work.Mostow.BusemannLipschitz
import Submission.Work.Mostow.thickPart_cocompact

/-!
# The packing count in a cusp quotient

Let `Γ ≤ PO(n,1)` be a lattice, `ξ ∈ Sph n` a parabolic fixed point whose stabiliser preserves
all horospheres at `ξ` (`hvan`), and suppose that the horoball at `ξ` of level `τ` is *embedded*:
its translates by elements of `Γ` not fixing `ξ` are disjoint from it.

Fix a level `D > 0` and a radius `r > 0` small enough that the horoball of level `τ` contains the
hyperbolic ball of radius `r` about every point of the level-`D` horosphere (this holds when
`log D + r < τ`), and such that `δ`-separated points of the flat space have hyperbolic distance
at least `2r` (this holds when `D δ ≥ 2√(cosh 2r - 1)`).

Then the finite subsets of the flat space which are `δ`-separated modulo the flat action of the
cusp stabiliser — i.e. such that the `ρ`-orbits of two distinct points, and the `ρ`-orbit of a
single point under nontrivial elements, are `δ`-apart — have bounded cardinality: the translates
of the union of the corresponding hyperbolic balls are pairwise disjoint, so the packing bound
`volH_le_of_isFundamentalDomain` applies.
-/

namespace Work.Mostow.cuspHoro

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped ENNReal Pointwise

set_option maxHeartbeats 1600000

noncomputable section

variable {n : ℕ}

/-- The stabiliser of a boundary point in `Γ`, viewed as a subgroup of `PO n 1`. -/
def stabSub (hA : POBasic n) (Γ : Subgroup (PO n 1)) (ξ : E n) (hξ : ξ ∈ Sph n) :
    Subgroup (PO n 1) where
  carrier := {g | g ∈ Γ ∧ bd g ξ = ξ}
  mul_mem' := by
    rintro a b ⟨haΓ, ha⟩ ⟨hbΓ, hb⟩
    exact ⟨Γ.mul_mem haΓ hbΓ, by rw [hA.bd_mul a b ξ hξ, hb, ha]⟩
  one_mem' := ⟨Γ.one_mem, hA.bd_one ξ hξ⟩
  inv_mem' := by
    rintro a ⟨haΓ, ha⟩
    refine ⟨Γ.inv_mem haΓ, ?_⟩
    have h2 : bd (a⁻¹ * a) ξ = ξ := by rw [inv_mul_cancel, hA.bd_one ξ hξ]
    rw [hA.bd_mul a⁻¹ a ξ hξ, ha] at h2
    exact h2

@[simp] lemma mem_stabSub {hA : POBasic n} {Γ : Subgroup (PO n 1)} {ξ : E n} {hξ : ξ ∈ Sph n}
    {g : PO n 1} : g ∈ stabSub hA Γ ξ hξ ↔ g ∈ Γ ∧ bd g ξ = ξ := Iff.rfl

/-- The elements of the cusp stabiliser preserve every horosphere at `ξ`. -/
lemma stabSub_lev (hA : POBasic n) (hI : HypIsoData n) {Γ : Subgroup (PO n 1)} {ξ : E n}
    {hξ : ξ ∈ Sph n}
    (hvan : ∀ (γ : Γ) η, η ∈ parFixed Γ → bd (γ : PO n 1) η = η → bCocy (γ : PO n 1) η = 0)
    {g : PO n 1} (hg : g ∈ stabSub hA Γ ξ hξ) (hξP : ξ ∈ parFixed Γ) (u : E n) :
    lev ξ (g • u) = lev ξ u := by
  obtain ⟨hgΓ, hgξ⟩ := hg
  have hbc : bCocy g ξ = 0 := hvan ⟨g, hgΓ⟩ ξ hξP hgξ
  have h0 : lev ξ (g • (0 : E n)) = 1 := by
    rw [lev_eq_exp hξ (g • 0), show busemann ξ (g • (0 : E n)) = bCocy g ξ from by
      rw [bCocy, hgξ], hbc, Real.exp_zero]
  rw [lev_smul_self hI hA ξ hξ g u hgξ, h0, mul_one]

/-- The horosphere action of the cusp stabiliser: an element `g` of the stabiliser maps the point
of level `D` with flat coordinate `s` to the point of level `D` with flat coordinate `ρ g s`,
where `ρ` is the flat action of the stabiliser on `ξ^⊥`. -/
lemma smul_hptOf (hA : POBasic n) (hI : HypIsoData n) {ξ : E n}
    {hξ : ξ ∈ Sph n} (D : ℝ) (hD : 0 < D)
    (G : Subgroup (PO n 1)) (hlev : ∀ g ∈ G, ∀ u : E n, lev ξ (g • u) = lev ξ u)
    {g : PO n 1} (hg : g ∈ G) (s : xiPerp ξ) :
    g • hptOf ξ (s : E n) D
      = hptOf ξ (((cuspFlatHom hA hI hξ D hD G hlev ⟨g, hg⟩ s : xiPerp ξ)) : E n) D := by
  refine (hptOf_yc ξ hξ D hD _ ?_).symm
  rw [hlev g hg, (hptOf_level ξ hξ D hD (s : E n)
    (by rw [real_inner_comm]; exact mem_xiPerp_iff.mp s.2)).1]

/-- A translate of a hyperbolic ball by an isometry of `PO n 1`. -/
lemma smul_hBall (hA : POBasic n) (hI : HypIsoData n) (g : PO n 1) (u : E n) (r : ℝ) :
    g • hBall u r = hBall (g • u) r := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    show hdist (g • u) (g • y) < r
    rwa [hI.isom_smul]
  · intro hx
    refine ⟨g⁻¹ • x, ?_, ?_⟩
    · show hdist u (g⁻¹ • x) < r
      rw [← hI.isom_smul g u (g⁻¹ • x), ← hA.mul_smul, mul_inv_cancel, hA.one_smul]
      exact hx
    · show g • (g⁻¹ • x) = x
      rw [← hA.mul_smul, mul_inv_cancel, hA.one_smul]

/-- **The packing count.** -/
theorem packingCount (n : ℕ) (hA : POActionProp n) (hI : HypIsometryProp n)
    (Γ : Subgroup (PO n 1)) (ξ : E n) (hξ : ξ ∈ Sph n) (hξP : ξ ∈ parFixed Γ)
    (hvan : ∀ (γ : Γ) η, η ∈ parFixed Γ → bd (γ : PO n 1) η = η → bCocy (γ : PO n 1) η = 0)
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
          (fun g hg u => stabSub_lev (POBasic.ofProp hA) (HypIsoData.ofProp hI) hvan hg hξP u)
          g s')) :
    (S.card : ℝ≥0∞) * volH n (hBall (0 : E n) r) ≤ volH n Df := by
  have hA' : POBasic n := POBasic.ofProp hA
  have hI' : HypIsoData n := HypIsoData.ofProp hI
  let G : Subgroup (PO n 1) := stabSub hA' Γ ξ hξ
  let hlev : ∀ g ∈ G, ∀ u : E n, lev ξ (g • u) = lev ξ u :=
    fun g hg u => stabSub_lev (hA := hA') (hI := hI') (hvan := hvan) (hg := hg) (hξP := hξP) u
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

end

end Work.Mostow.cuspHoro
