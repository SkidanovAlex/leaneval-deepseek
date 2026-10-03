import Mathlib
import Submission.Work.Interfaces.HornParts
import Submission.Work.Parab.Setup
import Submission.Work.Horn.Basin.simplyConnectedSpace_of_hulls
import Submission.Lib.Unif2.Work.Analysis.Complex.hull_simplyConnected_of_isCompact
import Submission.Work.HornSC.plane_of_sc_TInvariant
import Submission.Work.HornSC.false_of_univ_subset_Btil

/-! Guidance from the project lead (the requester):

AREA HORN-SC: prove HornSCStatement from HornTopo, BasinSC and PlanarInterSC (all given as hypotheses).
Contracts: Submission/Work/Interfaces/HornParts.lean (namespace MandelDim; imports Parabolic.lean). Lead route: NOTES_LEAD_horn.md at the workspace root (read it). Paper: REFS/shishikura_math9201282/hdim5.tex (Lemma 5.2, Prop 5.3). Reusable in the workspace: Submission/Work/Horn/* (basic.lean: piExp facts, E_add_one; basin.lean; flower_q.lean), Submission/Work/Parab/basinEnters/zero_not_mem_basin.lean, Submission/Work/Normal (Montel, Hurwitz), Submission/Work/L62/{lift_section,cartan}.lean. Never edit the interface files; if a statement is false, report a counterexample and the corrected statement. Go wide.

## HornSC (Bu, Bl simply connected, disjoint)
- Bu = ⋃_n (A + n) with A := Bu ∩ QLeft-part.
- A ≅ (via ψ) a component of φ(QLeft) ∩ B. φ(QLeft) ≅ QLeft (convex-ish sector, simply connected) and B is simply connected (BasinSC), so A is simply connected (PlanarInterSC).
- The increasing union is simply connected.
- Disjointness (paper): if Bu ∩ Bl ≠ ∅ then Bu = Bl is T-invariant, simply connected and contains both half planes. Then φ(Bu) ⊇ punctured neighbourhood pieces on both sides of 0, so B ⊇ Ωp ∪ φ(QLeft) ⊇ a punctured neighbourhood of 0. B is simply connected with 0 ∉ B, so a small circle around 0 is null-homotopic in B ⊆ ℂ ∖ {0}, contradicting winding number 1 (Mathlib has the winding / circle-integral facts).


## Basic facts used everywhere (prove once, e.g. in HornTopo)
(F0) 0 ∉ basin (Work.Parab.basinEnters.zero_not_mem_parabolicBasin). Orbits in B never hit 0.
(F1) Ωp ⊆ B: Ωp ⊆ basin, connected; some orbit from B enters Ωp (basin_enter) and stays in B (MapsTo f B B); component maximality of B.
(F2) f: B → B is proper and surjective (IsImmediateBasin), a local homeomorphism off f⁻¹... off c; B is a component of f⁻¹(B) (maximality). The critical values of f^N on B are f^k c, 1 ≤ k ≤ N.
(F3) P⁺ has no accumulation point in B (f^k c → 0 ∉ B), so every y ∈ B ∖ P⁺ has a ball ⊆ B ∖ P⁺.
(F4) Proper local homeomorphism over a simply connected open W: every component of the preimage maps homeomorphically onto W. (Proper + local homeo ⇒ covering; a covering of a simply connected, locally path-connected space is trivial on components: Mathlib lifting, IsCoveringMap(On).existsUnique_continuousMap_lifts.)
-/

namespace Work.HornSC

open MandelDim
open Complex Set Metric Filter Topology
open scoped Topology

noncomputable section

variable {f₀ : ℂ → ℂ} {D₀ B : Set ℂ} {c : ℂ}

/-- The left half plane `{w | w.re + ξ₀ < 0}` is contained in Shishikura's sector `QLeft ξ₀`. -/
lemma halfplane_sub_QLeft' (d : ParabData f₀ D₀) :
    {w : ℂ | w.re + d.ξ₀ < 0} ⊆ QLeft d.ξ₀ := by
  intro w hw
  have hw0 : w.re + d.ξ₀ < 0 := hw
  have hw1 : w.re < -d.ξ₀ := by linarith
  exact Work.Parab.halfplane_subset_QLeft d.ξ₀ hw1

/-- The left half plane lies in the maximal domain of the Fatou coordinate. -/
lemma halfplane_sub_Dφ (d : ParabData f₀ D₀) :
    {w : ℂ | w.re + d.ξ₀ < 0} ⊆ d.Dφ :=
  (halfplane_sub_QLeft' d).trans d.Q_sub

/-- The Fatou coordinate is injective on the left half plane. -/
lemma phi_injOn_halfplane (d : ParabData f₀ D₀) :
    InjOn d.φ {w : ℂ | w.re + d.ξ₀ < 0} :=
  d.φ_inj.mono (halfplane_sub_QLeft' d)

/-- The left half plane is convex. -/
lemma convex_halfplane (d : ParabData f₀ D₀) : Convex ℝ {w : ℂ | w.re + d.ξ₀ < 0} := by
  intro x hx y hy a b ha hb hab
  have hx' : x.re + d.ξ₀ < 0 := hx
  have hy' : y.re + d.ξ₀ < 0 := hy
  have hkey : (a • x + b • y).re + d.ξ₀ = a * (x.re + d.ξ₀) + b * (y.re + d.ξ₀) := by
    have h1 : (a • x + b • y).re = a * x.re + b * y.re := by simp [smul_eq_mul]
    rw [h1]
    have hlin : a * (x.re + d.ξ₀) + b * (y.re + d.ξ₀)
        = a * x.re + b * y.re + (a + b) * d.ξ₀ := by ring
    rw [hlin, hab, one_mul]
  show (a • x + b • y).re + d.ξ₀ < 0
  rw [hkey]
  rcases eq_or_lt_of_le ha with ha0 | hapos
  · have hb1 : b = 1 := by linarith
    rw [← ha0, hb1, zero_mul, zero_add, one_mul]; exact hy'
  · have h1 : a * (x.re + d.ξ₀) < 0 := mul_neg_of_pos_of_neg hapos hx'
    have h2 : b * (y.re + d.ξ₀) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb hy'.le
    linarith

lemma nonempty_halfplane (d : ParabData f₀ D₀) : {w : ℂ | w.re + d.ξ₀ < 0}.Nonempty :=
  ⟨((-d.ξ₀ - 1 : ℝ) : ℂ), by simp [Complex.ofReal_re]; linarith⟩

lemma isOpen_halfplane (d : ParabData f₀ D₀) : IsOpen {w : ℂ | w.re + d.ξ₀ < 0} :=
  isOpen_lt (continuous_re.add continuous_const) continuous_const

/-- The left half plane is simply connected. -/
lemma isSimplyConnected_halfplane (d : ParabData f₀ D₀) :
    IsSimplyConnected {w : ℂ | w.re + d.ξ₀ < 0} :=
  Work.Analysis.Complex.isSimplyConnected_of_convex (convex_halfplane d) (nonempty_halfplane d)

/-- φ is not constant on the left half plane. -/
lemma not_const_halfplane (d : ParabData f₀ D₀) :
    ¬ ∃ v : ℂ, ∀ z ∈ {w : ℂ | w.re + d.ξ₀ < 0}, d.φ z = v := by
  rintro ⟨v, hv⟩
  have h1 : ((-d.ξ₀ - 1 : ℝ) : ℂ) ∈ {w : ℂ | w.re + d.ξ₀ < 0} := by
    simp [Complex.ofReal_re]; linarith
  have h2 : ((-d.ξ₀ - 2 : ℝ) : ℂ) ∈ {w : ℂ | w.re + d.ξ₀ < 0} := by
    simp [Complex.ofReal_re]; linarith
  have heq : d.φ (((-d.ξ₀ - 1 : ℝ)) : ℂ) = d.φ (((-d.ξ₀ - 2 : ℝ)) : ℂ) := by
    rw [hv _ h1, hv _ h2]
  have hw := phi_injOn_halfplane d h1 h2 heq
  norm_num at hw

/-- An open subset of the left half plane is mapped to an open set by the Fatou coordinate:
φ is holomorphic and injective on the half plane, hence a local homeomorphism onto its image. -/
lemma isOpen_image_of_subset (d : ParabData f₀ D₀) {s : Set ℂ} (hs : IsOpen s)
    (hsH : s ⊆ {w : ℂ | w.re + d.ξ₀ < 0}) : IsOpen (d.φ '' s) := by
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨x, hx, rfl⟩
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp hs x hx
  have hbH : Metric.ball x ρ ⊆ {w : ℂ | w.re + d.ξ₀ < 0} := hρsub.trans hsH
  have hana : AnalyticOnNhd ℂ d.φ (Metric.ball x ρ) :=
    ((d.φ_holo.mono (halfplane_sub_Dφ d)).mono hbH).analyticOnNhd (Metric.isOpen_ball)
  have hx₂ : x ∈ Metric.ball x ρ := Metric.mem_ball_self hρ
  have hnc : ¬ ∃ v : ℂ, ∀ z ∈ Metric.ball x ρ, d.φ z = v := by
    rintro ⟨v, hv⟩
    have hx₁ : x + ((ρ / 2 : ℝ) : ℂ) ∈ Metric.ball x ρ := by
      rw [Metric.mem_ball, dist_eq_norm]
      have hsub : x + ((ρ / 2 : ℝ) : ℂ) - x = ((ρ / 2 : ℝ) : ℂ) := by ring
      rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    have heq : d.φ x = d.φ (x + ((ρ / 2 : ℝ) : ℂ)) := by rw [hv _ hx₂, hv _ hx₁]
    have hxe : x = x + ((ρ / 2 : ℝ) : ℂ) := phi_injOn_halfplane d (hbH hx₂) (hbH hx₁) heq
    have hre := congrArg Complex.re hxe
    simp only [Complex.add_re, Complex.ofReal_re] at hre
    linarith
  rcases hana.is_constant_or_isOpen (convex_ball x ρ).isPreconnected with hconst | hopen
  · exact absurd hconst hnc
  · have hnhds : d.φ '' Metric.ball x ρ ∈ nhds (d.φ x) :=
      (hopen _ (Metric.ball_subset_ball le_rfl) Metric.isOpen_ball).mem_nhds ⟨x, hx₂, rfl⟩
    exact Filter.mem_of_superset hnhds (Set.image_mono hρsub)

/-- The image of the left half plane under the Fatou coordinate is open. -/
lemma isOpen_image_halfplane (d : ParabData f₀ D₀) :
    IsOpen (d.φ '' {w : ℂ | w.re + d.ξ₀ < 0}) :=
  isOpen_image_of_subset d (isOpen_halfplane d) (subset_refl _)

/-- φ restricted to the left half plane is an open embedding into `ℂ`. -/
lemma isEmbedding_halfplane (d : ParabData f₀ D₀) :
    Topology.IsEmbedding (fun w : ↥{w : ℂ | w.re + d.ξ₀ < 0} => d.φ w) := by
  have hH : IsOpen {w : ℂ | w.re + d.ξ₀ < 0} := isOpen_halfplane d
  have hsub : {w : ℂ | w.re + d.ξ₀ < 0} ⊆ d.Dφ := halfplane_sub_Dφ d
  have hcont : Continuous (fun w : ↥{w : ℂ | w.re + d.ξ₀ < 0} => d.φ w) :=
    (d.φ_holo.mono hsub).continuousOn.domRestrict
  have hinj : Function.Injective (fun w : ↥{w : ℂ | w.re + d.ξ₀ < 0} => d.φ w) :=
    fun x y hxy => Subtype.ext (phi_injOn_halfplane d x.2 y.2 hxy)
  have hopenmap : IsOpenMap (fun w : ↥{w : ℂ | w.re + d.ξ₀ < 0} => d.φ w) := by
    intro s hs
    obtain ⟨V, hV, hVs⟩ := isOpen_induced_iff.mp hs
    have himg : (fun w : ↥{w : ℂ | w.re + d.ξ₀ < 0} => d.φ w) '' s
        = d.φ '' (V ∩ {w : ℂ | w.re + d.ξ₀ < 0}) := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        have hw' : (w : ℂ) ∈ V := by
          have h : w ∈ Subtype.val ⁻¹' V := by rw [hVs]; exact hw
          exact h
        exact ⟨w, ⟨hw', w.2⟩, rfl⟩
      · rintro ⟨u, ⟨huV, huH⟩, rfl⟩
        have hu : (⟨u, huH⟩ : ↥{w : ℂ | w.re + d.ξ₀ < 0}) ∈ s := by rw [← hVs]; exact huV
        exact ⟨⟨u, huH⟩, hu, rfl⟩
    rw [himg]
    exact isOpen_image_of_subset d (hV.inter hH) inter_subset_right
  exact (Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hcont hinj hopenmap).toIsEmbedding

/-- The image of the left half plane under the Fatou coordinate is simply connected: it is
homeomorphic to the (convex, hence simply connected) half plane. -/
lemma isSimplyConnected_image_halfplane (d : ParabData f₀ D₀) :
    IsSimplyConnected (d.φ '' {w : ℂ | w.re + d.ξ₀ < 0}) := by
  have hemb := isEmbedding_halfplane d
  have hset : Subtype.val '' (Set.univ : Set ↥{w : ℂ | w.re + d.ξ₀ < 0})
      = {w : ℂ | w.re + d.ξ₀ < 0} := by
    rw [Set.image_univ, Subtype.range_coe]
  have huniv : IsSimplyConnected (Set.univ : Set ↥{w : ℂ | w.re + d.ξ₀ < 0}) := by
    rw [← Work.Analysis.Complex.isSimplyConnected_image_subtype_val (U := {w : ℂ | w.re + d.ξ₀ < 0})
      (S := Set.univ), hset]
    exact isSimplyConnected_halfplane d
  have h1 : IsSimplyConnected
      ((fun w : ↥{w : ℂ | w.re + d.ξ₀ < 0} => d.φ w) '' Set.univ) :=
    (Topology.IsEmbedding.isSimplyConnected_image hemb (s := Set.univ)).mpr huniv
  have h2 : (fun w : ↥{w : ℂ | w.re + d.ξ₀ < 0} => d.φ w) '' Set.univ
      = d.φ '' {w : ℂ | w.re + d.ξ₀ < 0} := by
    ext z
    constructor
    · rintro ⟨w, -, rfl⟩; exact ⟨w.1, w.2, rfl⟩
    · rintro ⟨u, hu, rfl⟩; exact ⟨⟨u, hu⟩, trivial, rfl⟩
  rw [h2] at h1
  exact h1


/-- Shift the base point into the left half plane. -/
private lemma mem_sub_nat {F : Set ℂ} (hF : IsTInvariant F) {w : ℂ} (hw : w ∈ F) :
    ∀ m : ℕ, w - (m : ℂ) ∈ F := by
  intro m
  induction m with
  | zero => simpa using hw
  | succ n ih =>
    have h : w - ((n : ℕ) : ℂ) - 1 ∈ F :=
      (hF (w - ((n : ℕ) : ℂ) - 1)).mpr (by
        have he : w - ((n : ℕ) : ℂ) - 1 + 1 = w - ((n : ℕ) : ℂ) := by ring
        rwa [he])
    have he : w - (((n + 1 : ℕ)) : ℂ) = w - ((n : ℕ) : ℂ) - 1 := by push_cast; ring
    rwa [he]

private lemma mem_add_nat {F : Set ℂ} (hF : IsTInvariant F) {w : ℂ} (hw : w ∈ F) :
    ∀ m : ℕ, w + (m : ℂ) ∈ F := by
  intro m
  induction m with
  | zero => simpa using hw
  | succ n ih =>
    have h : w + ((n : ℕ) : ℂ) + 1 ∈ F := (hF (w + ((n : ℕ) : ℂ))).mp ih
    have he : w + (((n + 1 : ℕ)) : ℂ) = w + ((n : ℕ) : ℂ) + 1 := by push_cast; ring
    rwa [he]

/-- **Simple connectivity of one end of the cylinder.**  Let `C` be a component of
`B̃ = φ⁻¹(B) ∩ Dφ` which is open and `T`-invariant (both are supplied by
`HornTopoStatement`), and let `a ∈ C` be a point whose backward translates eventually enter
the left half plane `{re w < -ξ₀}` (where `φ` is injective and holomorphic).

Then `C` is simply connected: a loop of `C` is shifted into the left half plane, its
`φ`-image lies in a component of `φ '' QLeft ∩ B`, and that component is simply connected by
`PlanarInterSC` (using that `B` is simply connected, `BasinSC`); the inverse branch of `φ`
carries the contraction back. -/
theorem simplyConnected_of_component (hB : BasinSCStatement) (hP : PlanarInterSCStatement)
    (d : ParabData f₀ D₀) (hsetup : IsF0Setup f₀ D₀ B c) (a : ℂ)
    (hCopen : IsOpen (connectedComponentIn (Btil d B) a))
    (hCT : IsTInvariant (connectedComponentIn (Btil d B) a))
    (haC : a ∈ connectedComponentIn (Btil d B) a)
    (hNa : ∃ M : ℕ, (a - (M : ℂ)).re + d.ξ₀ < 0) :
    SimplyConnectedSpace ↥(connectedComponentIn (Btil d B) a) := by
  have hBopen : IsOpen B := hsetup.2.1.1
  have hBsc : SimplyConnectedSpace ↥B := hB f₀ D₀ B c d hsetup
  have hφB : ∀ {w : ℂ}, w ∈ connectedComponentIn (Btil d B) a → d.φ w ∈ B :=
    fun {w} hw => (connectedComponentIn_subset (Btil d B) a hw).2
  -- the hull statement for loops: preconnected compacta
  have aux : ∀ K : Set ℂ, IsCompact K → IsPreconnected K → K.Nonempty →
      K ⊆ connectedComponentIn (Btil d B) a →
      ∃ V : Set ℂ, IsSimplyConnected V ∧ K ⊆ V ∧ V ⊆ connectedComponentIn (Btil d B) a := by
    intro K hK hKp hKne hKC
    obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, K ⊆ Metric.ball (0 : ℂ) ρ := hK.isBounded.subset_ball 0
    have hc₀ : ∀ w ∈ K, w.re ≤ ρ := by
      intro w hw
      have h1 : ‖w‖ < ρ := by
        have := hρ hw
        simpa [Metric.mem_ball, dist_zero_right] using this
      exact le_trans (Complex.re_le_norm w) h1.le
    obtain ⟨M, hM⟩ := hNa
    obtain ⟨N, hNK, hNbase⟩ : ∃ N : ℕ, ρ + d.ξ₀ < (N : ℝ) ∧ (a - (N : ℂ)).re + d.ξ₀ < 0 := by
      refine ⟨max (⌈ρ + d.ξ₀⌉₊ + 1) M, ?_, ?_⟩
      · have h1 : ρ + d.ξ₀ ≤ (⌈ρ + d.ξ₀⌉₊ : ℝ) := Nat.le_ceil _
        have h2 : ((⌈ρ + d.ξ₀⌉₊ + 1 : ℕ) : ℝ) ≤ (max (⌈ρ + d.ξ₀⌉₊ + 1) M : ℕ) := by
          exact_mod_cast le_max_left _ _
        push_cast at h1 h2 ⊢
        linarith
      · have h1 : (a - (M : ℂ)).re = a.re - (M : ℝ) := by simp
        have h2 : (a - ((max (⌈ρ + d.ξ₀⌉₊ + 1) M : ℕ) : ℂ)).re
            = a.re - ((max (⌈ρ + d.ξ₀⌉₊ + 1) M : ℕ) : ℝ) := by simp
        have h3 : ((M : ℕ) : ℝ) ≤ ((max (⌈ρ + d.ξ₀⌉₊ + 1) M : ℕ) : ℝ) := by
          exact_mod_cast le_max_right _ _
        rw [h2]
        linarith
    obtain ⟨w₀, hw₀⟩ := hKne
    have hshift : ∀ w ∈ K, (w - (N : ℂ)).re + d.ξ₀ < 0 := by
      intro w hw
      have h1 : (w - (N : ℂ)).re = w.re - (N : ℝ) := by simp
      rw [h1]; linarith [hc₀ w hw]
    have hw₀N : w₀ - (N : ℂ) ∈ connectedComponentIn (Btil d B) a := mem_sub_nat hCT (hKC hw₀) N
    have hφmem : d.φ (w₀ - (N : ℂ)) ∈ d.φ '' {w : ℂ | w.re + d.ξ₀ < 0} ∩ B :=
      ⟨⟨w₀ - (N : ℂ), hshift w₀ hw₀, rfl⟩, hφB hw₀N⟩
    set Cc : Set ℂ := connectedComponentIn (d.φ '' {w : ℂ | w.re + d.ξ₀ < 0} ∩ B)
      (d.φ (w₀ - (N : ℂ))) with hCcdef
    have hCcpre : IsPreconnected Cc := hCcdef ▸ isPreconnected_connectedComponentIn
    have hCcsc : IsSimplyConnected Cc := hCcdef ▸
      (hP (d.φ '' {w : ℂ | w.re + d.ξ₀ < 0}) B (isOpen_image_halfplane d) hBopen
        (isSimplyConnected_image_halfplane d) hBsc (d.φ (w₀ - (N : ℂ))) hφmem)
    -- the preimage in the subtype
    set S : Set ↥{w : ℂ | w.re + d.ξ₀ < 0} :=
      (fun w : ↥{w : ℂ | w.re + d.ξ₀ < 0} => d.φ w) ⁻¹' Cc with hSdef
    set W : Set ℂ := Subtype.val '' S with hWdef
    have hrange : Set.range (fun w : ↥{w : ℂ | w.re + d.ξ₀ < 0} => d.φ w)
        = d.φ '' {w : ℂ | w.re + d.ξ₀ < 0} := by
      ext z; constructor
      · rintro ⟨w, rfl⟩; exact ⟨w.1, w.2, rfl⟩
      · rintro ⟨u, hu, rfl⟩; exact ⟨⟨u, hu⟩, rfl⟩
    have himgS : (fun w : ↥{w : ℂ | w.re + d.ξ₀ < 0} => d.φ w) '' S = Cc := by
      rw [hSdef, Set.image_preimage_eq_inter_range, hrange]
      exact Set.inter_eq_left.mpr fun z hz => (connectedComponentIn_subset _ _ hz).1
    have hWeq : W = d.φ ⁻¹' Cc ∩ {w : ℂ | w.re + d.ξ₀ < 0} := by
      rw [hWdef, hSdef]
      ext z; constructor
      · rintro ⟨w, hw, rfl⟩; exact ⟨hw, w.2⟩
      · rintro ⟨hz, hzH⟩; exact ⟨⟨z, hzH⟩, hz, rfl⟩
    have hSpre : IsPreconnected S := by
      have h1 : IsPreconnected
          ((fun w : ↥{w : ℂ | w.re + d.ξ₀ < 0} => d.φ w) '' S) := by
        rw [himgS]; exact hCcpre
      exact ((isEmbedding_halfplane d).isInducing.isPreconnected_image (s := S)).mp h1
    have hSsc : IsSimplyConnected S := by
      have h1 : IsSimplyConnected
          ((fun w : ↥{w : ℂ | w.re + d.ξ₀ < 0} => d.φ w) '' S) := by
        rw [himgS]; exact hCcsc
      exact (Topology.IsEmbedding.isSimplyConnected_image (isEmbedding_halfplane d)
        (s := S)).mp h1
    have hWpre : IsPreconnected W := by
      rw [hWdef]
      exact (Topology.IsInducing.isPreconnected_image Topology.IsInducing.subtypeVal
        (s := S)).mpr hSpre
    have hWsc : IsSimplyConnected W := by
      rw [hWdef]
      exact (Work.Analysis.Complex.isSimplyConnected_image_subtype_val
        (U := {w : ℂ | w.re + d.ξ₀ < 0}) (S := S)).mpr hSsc
    have hWsub : W ⊆ Btil d B := by
      rw [hWeq]
      rintro w ⟨hw, hwH⟩
      exact ⟨halfplane_sub_Dφ d hwH, (connectedComponentIn_subset _ _ hw).2⟩
    have hWmeet : (W ∩ connectedComponentIn (Btil d B) a).Nonempty := by
      refine ⟨w₀ - (N : ℂ), ?_, hw₀N⟩
      rw [hWeq]
      exact ⟨mem_connectedComponentIn hφmem, hshift w₀ hw₀⟩
    have hWC : W ⊆ connectedComponentIn (Btil d B) a := by
      obtain ⟨w, hwW, hwC⟩ := hWmeet
      have h1 : W ⊆ connectedComponentIn (Btil d B) w := hWpre.subset_connectedComponentIn hwW hWsub
      have h2 : connectedComponentIn (Btil d B) w = connectedComponentIn (Btil d B) a :=
        (connectedComponentIn_eq (F := Btil d B) (x := a) (y := w) hwC).symm
      rwa [h2] at h1
    -- assemble the hull
    refine ⟨(fun z : ℂ => z + (N : ℂ)) '' W, ?_, ?_, ?_⟩
    · exact (Homeomorph.isSimplyConnected_image (Homeomorph.addRight (N : ℂ)) (s := W)).mpr hWsc
    · rintro z hz
      refine ⟨z - (N : ℂ), ?_, by ring⟩
      have hzW : z - (N : ℂ) ∈ W := by
        rw [hWeq]
        refine ⟨?_, hshift z hz⟩
        have hpre : IsPreconnected ((fun w : ℂ => w - (N : ℂ)) '' K) :=
          hKp.image _ (continuous_id.sub continuous_const).continuousOn
        have hφpre : IsPreconnected (d.φ '' ((fun w : ℂ => w - (N : ℂ)) '' K)) := by
          refine hpre.image d.φ ?_
          refine (d.φ_holo.mono ?_).continuousOn
          rintro u ⟨v, hv, rfl⟩
          exact halfplane_sub_Dφ d (hshift v hv)
        have hφsub : d.φ '' ((fun w : ℂ => w - (N : ℂ)) '' K) ⊆
            d.φ '' {w : ℂ | w.re + d.ξ₀ < 0} ∩ B := by
          rintro u ⟨v, ⟨k, hk, rfl⟩, rfl⟩
          exact ⟨⟨k - (N : ℂ), hshift k hk, rfl⟩, hφB (mem_sub_nat hCT (hKC hk) N)⟩
        have hmem : d.φ (w₀ - (N : ℂ)) ∈ d.φ '' ((fun w : ℂ => w - (N : ℂ)) '' K) :=
          ⟨w₀ - (N : ℂ), ⟨w₀, hw₀, rfl⟩, rfl⟩
        have h := hφpre.subset_connectedComponentIn hmem hφsub
        exact h ⟨z - (N : ℂ), ⟨z, hz, rfl⟩, rfl⟩
      exact hzW
    · rintro z ⟨y, hy, rfl⟩
      exact mem_add_nat hCT (hWC hy) N
  -- conclude
  have hUconn : IsConnected (connectedComponentIn (Btil d B) a) :=
    ⟨⟨a, haC⟩, isPreconnected_connectedComponentIn⟩
  rw [show SimplyConnectedSpace ↥(connectedComponentIn (Btil d B) a) ↔
      IsSimplyConnected (connectedComponentIn (Btil d B) a) from Iff.rfl,
    isSimplyConnected_iff_exists_homotopy_refl_forall_mem]
  constructor
  · exact (hCopen.isConnected_iff_isPathConnected).mp hUconn
  · intro x p hp
    have hK : IsCompact (Set.range p) := isCompact_range p.continuous
    have hKp : IsPreconnected (Set.range p) := by
      rw [← Set.image_univ]
      exact isPreconnected_univ.image p p.continuous.continuousOn
    have hKne : (Set.range p).Nonempty := ⟨p 0, ⟨0, rfl⟩⟩
    have hKC : Set.range p ⊆ connectedComponentIn (Btil d B) a := by
      rintro z ⟨t, rfl⟩
      exact hp t
    obtain ⟨V, hVsc, hKV, hVU⟩ := aux (Set.range p) hK hKp hKne hKC
    obtain ⟨F, hF⟩ := (isSimplyConnected_iff_exists_homotopy_refl_forall_mem.mp hVsc).2 x p
      (fun t => hKV ⟨t, rfl⟩)
    exact ⟨F, fun t => hVU (hF t)⟩


/-- A useful form of the shift bound for the two base points `± i (η₀ + 1)`. -/
private lemma exists_shift (d : ParabData f₀ D₀) (y : ℂ) (hy : y.re = 0) :
    ∃ M : ℕ, (y - (M : ℂ)).re + d.ξ₀ < 0 := by
  refine ⟨⌈d.ξ₀⌉₊ + 1, ?_⟩
  have h1 : (y - (((⌈d.ξ₀⌉₊ + 1 : ℕ)) : ℂ)).re = -(((⌈d.ξ₀⌉₊ + 1 : ℕ)) : ℝ) := by
    rw [Complex.sub_re, hy, zero_sub]
    rw [show (((⌈d.ξ₀⌉₊ + 1 : ℕ)) : ℂ) = ((((⌈d.ξ₀⌉₊ + 1 : ℕ)) : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.ofReal_re]
  rw [h1]
  have h2 : d.ξ₀ ≤ (⌈d.ξ₀⌉₊ : ℝ) := Nat.le_ceil _
  push_cast
  linarith

/-- **The upper end `B̃ᵘ` is simply connected** (Shishikura, Prop. 5.3). -/
theorem simplyConnected_BuOf (hT : HornTopoStatement) (hB : BasinSCStatement)
    (hP : PlanarInterSCStatement) (d : ParabData f₀ D₀) (hsetup : IsF0Setup f₀ D₀ B c) :
    SimplyConnectedSpace ↥(BuOf d B) := by
  obtain ⟨hBuOpen, -, hBuT, -, hUp, -, -⟩ := hT f₀ D₀ B c d hsetup
  have hbase : (I * ((d.η₀ : ℂ) + 1)) ∈ BuOf d B := hUp (by simp)
  have hre : (I * ((d.η₀ : ℂ) + 1)).re = 0 := by simp
  exact simplyConnected_of_component hB hP d hsetup _
    hBuOpen hBuT hbase (exists_shift d _ hre)

/-- **The lower end `B̃ˡ` is simply connected** (Shishikura, Prop. 5.3). -/
theorem simplyConnected_BlOf (hT : HornTopoStatement) (hB : BasinSCStatement)
    (hP : PlanarInterSCStatement) (d : ParabData f₀ D₀) (hsetup : IsF0Setup f₀ D₀ B c) :
    SimplyConnectedSpace ↥(BlOf d B) := by
  obtain ⟨-, hBlOpen, -, hBlT, -, hLow, -⟩ := hT f₀ D₀ B c d hsetup
  have hbase : (-(I * ((d.η₀ : ℂ) + 1))) ∈ BlOf d B := hLow (by simp)
  have hre : (-(I * ((d.η₀ : ℂ) + 1))).re = 0 := by simp
  exact simplyConnected_of_component hB hP d hsetup _
    hBlOpen hBlT hbase (exists_shift d _ hre)


/-- **Shishikura, Prop. 5.3 (last part)**: the two ends `B̃ᵘ`, `B̃ˡ` of the lift of the immediate
parabolic basin are simply connected and disjoint. -/
theorem horn_sc (hT : HornTopoStatement) (hB : BasinSCStatement) (hP : PlanarInterSCStatement) :
    HornSCStatement := by
  intro f₀ D₀ B c d hsetup
  obtain ⟨hBuOpen, hBlOpen, hBuT, hBlT, hUp, hLow, hDE⟩ := hT f₀ D₀ B c d hsetup
  have hbase : (I * ((d.η₀ : ℂ) + 1)) ∈ BuOf d B := hUp (by simp)
  refine ⟨simplyConnected_BuOf hT hB hP d hsetup, simplyConnected_BlOf hT hB hP d hsetup, ?_⟩
  by_contra hdisj
  rw [Set.not_disjoint_iff] at hdisj
  obtain ⟨x, hx⟩ := hdisj
  -- the two components coincide
  have heq : BuOf d B = BlOf d B := by
    have h1 : BuOf d B = connectedComponentIn (Btil d B) x :=
      connectedComponentIn_eq (F := Btil d B) (x := I * ((d.η₀ : ℂ) + 1)) (y := x) hx.1
    have h2 : BlOf d B = connectedComponentIn (Btil d B) x :=
      connectedComponentIn_eq (F := Btil d B) (x := -(I * ((d.η₀ : ℂ) + 1))) (y := x) hx.2
    rw [h1, h2]
  -- `BuOf` is open, connected, simply connected, `T`-invariant and contains both half planes
  have hCconn : IsConnected (BuOf d B) := ⟨⟨_, hbase⟩, isPreconnected_connectedComponentIn⟩
  have hCsc : SimplyConnectedSpace ↥(BuOf d B) := simplyConnected_BuOf hT hB hP d hsetup
  have hsub : {w : ℂ | d.η₀ < |w.im|} ⊆ BuOf d B := by
    intro w hw
    have hw' : d.η₀ < |w.im| := hw
    rcases lt_abs.mp hw' with h | h
    · exact hUp h
    · rw [heq]
      have h2 : w.im < -d.η₀ := by linarith
      exact hLow h2
  have huniv : BuOf d B = Set.univ :=
    plane_of_sc_TInvariant (BuOf d B) hBuOpen hCconn hCsc hBuT d.η₀ hsub
  -- hence `B̃ = φ⁻¹(B) ∩ Dφ` is all of `ℂ`, which is impossible
  refine false_of_univ_subset_Btil d hsetup ?_
  rw [← huniv]
  exact connectedComponentIn_subset (Btil d B) (I * ((d.η₀ : ℂ) + 1))

end

end Work.HornSC
