import Mathlib
import Submission.Work.WilE9G.Sard.morseCoverDefs
import Submission.Work.WilE9G.Sard.exists_countable_subcover

/-!
# Morse's criticality theorem: the induction

This file proves the inductive statement behind `Work.WilE9G.Sard.morseCriticality`: for every
`s ≥ 0`, every dimension `d`, every open set `R ⊆ ℝ^d` and every `B ⊆ R` there is a countable
chart cover of `B` inside `R` such that every `C^s` function on `R` vanishing on `B` is flat of
order `s` along each piece (in the coordinates of the chart).

The proof is Morse's induction on `s + d`:

* write `B = α ∪ β`, where `α` is the set of points at which the gradient of every `C^s` function
  vanishing on `B` is forced to vanish, and `β = B \ α` the rest;
* on `α`: the coefficient functions of any such `G` are `C^{s-1}` and vanish on `α`, so the
  induction hypothesis at level `s - 1` makes them flat of order `s - 1` along a chart cover of
  `α`; Morse's Lemma 3.2 (`FlatAt.comp_of_fderiv`) upgrades this to flatness of order `s` of `G`;
* on `β`: at each point `x ∈ β` some `G` vanishing on `B` has nonzero gradient, so the level set
  `{G = 0}` is locally a `C^s` graph; parametrising it by an *expanding* map `Ψ` (Morse's
  Lemma 3.3, `LevelSetParam` below) and applying the induction hypothesis in dimension `d - 1` to
  `Ψ⁻¹ B` transfers the cover to the ambient space.

Morse's Lemma 3.3 is *not* proved here: it is the hypothesis `LevelSetParam` of `morseCover_all`,
discharged in `Work.WilE9G.Sard.morseCriticality` by the separately proved
`levelSetExpandingParam`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

namespace Work.WilE9G.Sard

open Set Metric Filter
open scoped Topology

noncomputable section

/-! ## Morse's Lemma 3.3 (taken as a hypothesis) -/

/-- **Morse's Lemma 3.3.**  If `h : ℝ^d → ℝ` is `C^m` at `y` with `h y = 0` and `∇h y ≠ 0`, then a
neighbourhood of `y` in the level set `{h = 0}` is the image of an expanding `C^m`
parametrisation `Ψ` from an open set of `ℝ^{d-1}`. -/
def LevelSetParam : Prop :=
  ∀ (d : ℕ) (_ : 1 ≤ d) (m : ℕ) (_ : 1 ≤ m) (h : (Fin d → ℝ) → ℝ) (y : Fin d → ℝ),
    ContDiffAt ℝ m h y → h y = 0 → fderiv ℝ h y ≠ 0 →
    ∃ (u₀ : Fin (d - 1) → ℝ) (V : Set (Fin (d - 1) → ℝ))
      (Ψ : (Fin (d - 1) → ℝ) → (Fin d → ℝ)) (U : Set (Fin d → ℝ)),
      IsOpen V ∧ u₀ ∈ V ∧ ContDiffOn ℝ m Ψ V ∧
      (∀ x ∈ V, ∀ z ∈ V, dist x z ≤ dist (Ψ x) (Ψ z)) ∧
      (∀ u ∈ V, h (Ψ u) = 0) ∧ Ψ u₀ = y ∧ IsOpen U ∧ y ∈ U ∧
      (∀ z ∈ U, h z = 0 → z ∈ Ψ '' V)

/-! ## The inductive statement -/

/-- `MorseCover s d R B`: `B` (a subset of the open set `R ⊆ ℝ^d`) admits a chart cover inside `R`
with flatness for the class of `C^s` functions on `R` vanishing on `B`. -/
abbrev MorseCover (s d : ℕ) (R B : Set (Fin d → ℝ)) : Prop :=
  ChartCover s d R B (fun G => ContDiffOn ℝ s G R ∧ ∀ x ∈ B, G x = 0)

/-- Points of `B` at which the gradient of every `C^s` function on `R` that vanishes on `B`
vanishes. -/
def morseAlpha (s d : ℕ) (R B : Set (Fin d → ℝ)) : Set (Fin d → ℝ) :=
  {y | y ∈ B ∧ ∀ G : (Fin d → ℝ) → ℝ, ContDiffOn ℝ s G R → (∀ x ∈ B, G x = 0) →
    fderiv ℝ G y = 0}

lemma morseAlpha_subset (s d : ℕ) (R B : Set (Fin d → ℝ)) : morseAlpha s d R B ⊆ B :=
  fun _ hy => hy.1

lemma morseAlpha_grad {s d : ℕ} {R B : Set (Fin d → ℝ)} {G : (Fin d → ℝ) → ℝ}
    (hG : ContDiffOn ℝ s G R) (hG0 : ∀ x ∈ B, G x = 0) {y : Fin d → ℝ}
    (hy : y ∈ morseAlpha s d R B) : fderiv ℝ G y = 0 := hy.2 G hG hG0

/-! ## Union of a countable family of chart covers -/

/-- Union of a countable family of chart covers of pieces, all contained in the covered set. -/
theorem chartCover_iUnion {s d : ℕ} {R B : Set (Fin d → ℝ)} {P : ((Fin d → ℝ) → ℝ) → Prop}
    {ι : Type} (hι : Countable ι) (Z : ι → Set (Fin d → ℝ))
    (hZ : ∀ i, ChartCover s d R (Z i) P) (hZB : ∀ i, Z i ⊆ B) (hB : B ⊆ ⋃ i, Z i) :
    ChartCover s d R B P := by
  choose I hI c A hrest using hZ
  refine ⟨(Σ i, I i), ?_, (fun p => c p.1 p.2), (fun p => A p.1 p.2), ?_, ?_, ?_, ?_, ?_⟩
  · haveI := hι
    haveI : ∀ i, Countable (I i) := hI
    infer_instance
  · rintro ⟨i, j⟩
    exact (hrest i).1 j
  · rintro ⟨i, j⟩
    exact ((hrest i).2.1 j).trans (hZB i)
  · rintro y hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hB hy)
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp ((hrest i).2.2.1 hi)
    exact Set.mem_iUnion.mpr ⟨⟨i, j⟩, hj⟩
  · rintro ⟨i, j⟩
    exact (hrest i).2.2.2.1 j
  · rintro G hG ⟨i, j⟩ u hu hgu
    exact (hrest i).2.2.2.2 G hG j u hu hgu

/-! ## The base case `s = 0`: identity charts -/

/-- For `s = 0` the identity charts cover everything: a continuous function on `R` vanishing on `B`
is (tautologically) flat of order `0` at every point of `B`. -/
theorem morseCover_zero {d : ℕ} {R B : Set (Fin d → ℝ)} (hR : IsOpen R) (hBR : B ⊆ R) :
    MorseCover 0 d R B := by
  classical
  have hrad : ∀ x ∈ B, ∃ r : ℝ, 0 < r ∧ Metric.closedBall x (2 * r) ⊆ R := by
    intro x hx
    obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp (hR.mem_nhds (hBR hx))
    refine ⟨r / 4, by linarith, fun y hy => hrsub ?_⟩
    rw [Metric.mem_ball]
    rw [Metric.mem_closedBall] at hy
    linarith
  have hex : ∀ x : Fin d → ℝ, ∃ r : ℝ, x ∈ B → 0 < r ∧ Metric.closedBall x (2 * r) ⊆ R := by
    intro x
    by_cases hx : x ∈ B
    · obtain ⟨r, hr, hsub⟩ := hrad x hx
      exact ⟨r, fun _ => ⟨hr, hsub⟩⟩
    · exact ⟨1, fun h => absurd h hx⟩
  choose r hr using hex
  obtain ⟨T, hTcount, hTcov⟩ := exists_countable_subcover
    (fun x : Fin d → ℝ => if x ∈ B then Metric.ball x (r x) else ∅)
    (fun x => by
      by_cases hx : x ∈ B
      · simpa [hx] using Metric.isOpen_ball (x := x) (r := r x)
      · simpa [hx] using isOpen_empty)
    (fun x hx => by
      rw [if_pos hx]
      exact Metric.mem_ball_self (hr x hx).1)
  set T' : Set (Fin d → ℝ) := T ∩ B with hT'def
  have hT'count : T'.Countable := hTcount.mono Set.inter_subset_left
  refine ⟨T', hT'count.to_subtype, (fun x => ChartDatum.id d x.1 (r x.1) (hr x.1 x.2.2).1),
    (fun x => B ∩ Metric.ball x.1 (r x.1)), ?_, ?_, ?_, ?_, ?_⟩
  · -- the closed ball image stays inside `R`
    intro x
    have h1 : (r x.1) ≤ 2 * r x.1 := by
      have hpos := (hr x.1 x.2.2).1
      linarith
    rintro z ⟨w, hw, rfl⟩
    exact (Metric.closedBall_subset_closedBall h1).trans (hr x.1 x.2.2).2 hw
  · exact fun x => Set.inter_subset_left
  · -- covering
    intro y hy
    obtain ⟨x, hxT, hxy⟩ := Set.mem_iUnion₂.mp (hTcov hy)
    have hxB : x ∈ B := by
      by_contra hx
      rw [if_neg hx] at hxy
      exact hxy
    exact Set.mem_iUnion.mpr ⟨⟨x, hxT, hxB⟩, hy, by simpa [if_pos hxB] using hxy⟩
  · intro x y hy
    exact ⟨y, hy.2, rfl⟩
  · -- flatness of order `0`
    rintro G ⟨hGcd, hG0⟩ x u hu ⟨huB, -⟩ ε hε
    have huR : u ∈ R := hBR huB
    have hcont : ContinuousAt G u := hGcd.continuousOn.continuousAt (hR.mem_nhds huR)
    obtain ⟨ρ, hρ, hρ'⟩ := Metric.continuousAt_iff.mp hcont ε hε
    refine ⟨ρ / 2, by linarith, fun y hy => ?_⟩
    have hy' : dist y u < ρ := by
      rw [dist_eq_norm]; linarith
    have h1 : dist (G y) (G u) < ε := hρ' hy'
    rw [dist_eq_norm, hG0 u huB, sub_zero] at h1
    simpa [ChartDatum.id] using h1.le

/-! ## The `α`-step: upgrading the flatness order -/

/-- **Morse's Lemma 3.2 (upgrade).**  If every `C^s` function vanishing on `B` has vanishing
gradient at every point of `α`, then a chart cover of `α` for `C^{s-1}`-functions vanishing on `α`
(the induction hypothesis at level `s - 1`) upgrades to a chart cover of `α` with flatness of order
`s` for `C^s`-functions vanishing on `B`. -/
theorem chartCover_upgrade {s d : ℕ} (hs : 1 ≤ s) {R B α : Set (Fin d → ℝ)} (hR : IsOpen R)
    (hαB : α ⊆ B)
    (T : ChartCover (s - 1) d R α (fun G => ContDiffOn ℝ (s - 1) G R ∧ ∀ x ∈ α, G x = 0))
    (hgrad : ∀ G : (Fin d → ℝ) → ℝ, ContDiffOn ℝ s G R → (∀ x ∈ B, G x = 0) →
      ∀ y ∈ α, fderiv ℝ G y = 0) :
    ChartCover s d R α (fun G => ContDiffOn ℝ s G R ∧ ∀ x ∈ B, G x = 0) := by
  obtain ⟨ι, hcnt, cc, AA, hinR, hsub, hcov, himg, hflat⟩ := T
  refine ⟨ι, hcnt, cc, AA, hinR, hsub, hcov, himg, ?_⟩
  intro G hG i u hu hgu
  obtain ⟨hGcd, hG0⟩ := hG
  have hsne : ((s : ℕ) : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (by omega : s ≠ 0)
  have hcoeff : ∀ a : Fin d,
      FlatAt (fun z => fderiv ℝ G ((cc i).γ z) (Pi.single a 1)) (s - 1) u := by
    intro a
    have hcd : ContDiffOn ℝ (s - 1) (fun y => fderiv ℝ G y (Pi.single a 1)) R :=
      contDiffOn_fderiv_coord hR hs hGcd a
    have hzero : ∀ x ∈ α, (fun y => fderiv ℝ G y (Pi.single a 1)) x = 0 := by
      intro x hx
      show fderiv ℝ G x (Pi.single a 1) = 0
      rw [hgrad G hGcd hG0 x hx, zero_apply]
    exact hflat _ ⟨hcd, hzero⟩ i u hu hgu
  have hflat_deriv : FlatAt (fun z => fderiv ℝ G ((cc i).γ z)) (s - 1) u :=
    flatAt_fderiv_scalar_of_coeffs hcoeff
  obtain ⟨L, ρ₀, hL, hρ₀, hball, hdiff, hbound⟩ :=
    exists_fderiv_norm_bound (cc i).contdiffOn (cc i).rad_pos hu
  refine FlatAt.comp_of_fderiv (F := G) (γ := (cc i).γ) (x₀ := u) (L := L) (ρ₀ := ρ₀)
    (by omega) ?_ ?_ ?_ hL hρ₀ hbound hflat_deriv
  · intro z hz
    have hzR : (cc i).γ z ∈ R := hinR i ⟨z, hball hz, rfl⟩
    exact (hGcd.differentiableOn hsne).differentiableAt (hR.mem_nhds hzR)
  · intro z hz
    exact hdiff z hz
  · exact hG0 _ (hαB (hsub i hgu))

/-! ## The `β`-step: reduction to the level set -/

/-- **Morse's Lemma 3.3 applied.**  If at `x ∈ B` some `C^s` function `G` on `R` vanishing on `B`
has non-vanishing gradient, then a neighbourhood of `x` in `B` can be covered by charts obtained by
composing a `C^s` expanding parametrisation `Ψ` of the level set `{G = 0}` with the chart cover of
`Ψ⁻¹ B` supplied by the induction hypothesis in dimension `d - 1`. -/
theorem cover_beta (h333 : LevelSetParam) {s d : ℕ} (hd : 1 ≤ d) (hs : 1 ≤ s)
    {R B : Set (Fin d → ℝ)} (hR : IsOpen R)
    (hmain : ∀ (R' : Set (Fin (d - 1) → ℝ)) (B' : Set (Fin (d - 1) → ℝ)), IsOpen R' → B' ⊆ R' →
      ChartCover s (d - 1) R' B' (fun F => ContDiffOn ℝ s F R' ∧ ∀ y ∈ B', F y = 0))
    {x : Fin d → ℝ} (hxB : x ∈ B) (hxR : x ∈ R)
    {G : (Fin d → ℝ) → ℝ} (hG : ContDiffOn ℝ s G R) (hG0 : ∀ y ∈ B, G y = 0)
    (hgrad : fderiv ℝ G x ≠ 0) :
    ∃ (U Z : Set (Fin d → ℝ)), IsOpen U ∧ x ∈ U ∧ Z ⊆ B ∧
      (∀ y ∈ U, y ∈ B → y ∈ R → G y = 0 → y ∈ Z) ∧
      ChartCover s d R Z (fun G' => ContDiffOn ℝ s G' R ∧ ∀ y ∈ B, G' y = 0) := by
  classical
  obtain ⟨u₀, V, Ψ, U, hVopen, -, hΨcd, hΨexp, hΨG, hΨu₀, hUopen, hxU, hlev⟩ :=
    h333 d hd s hs G x (hG.contDiffAt (hR.mem_nhds hxR)) (hG0 x hxB) hgrad
  -- the piece of the parametrisation whose image stays inside `R`
  set V' : Set (Fin (d - 1) → ℝ) := V ∩ Ψ ⁻¹' R with hV'def
  have hV'open : IsOpen V' := by
    rw [hV'def]
    refine isOpen_iff_mem_nhds.mpr (fun u hu => ?_)
    have hcont : ContinuousAt Ψ u :=
      hΨcd.continuousOn.continuousAt (hVopen.mem_nhds hu.1)
    exact Filter.inter_mem (hVopen.mem_nhds hu.1)
      (hcont.preimage_mem_nhds (hR.mem_nhds hu.2))
  have hΨV'R : Ψ '' V' ⊆ R := by rintro y ⟨u, hu, rfl⟩; exact hu.2
  have hΨinj : Set.InjOn Ψ V := injOn_of_expanding hΨexp
  have hΨ1 : ContDiffOn ℝ 1 Ψ V' :=
    (hΨcd.mono Set.inter_subset_left).of_le (by exact_mod_cast (by omega : 1 ≤ s))
  have hΨexp' : ∀ a ∈ V', ∀ b ∈ V', dist a b ≤ dist (Ψ a) (Ψ b) :=
    fun a ha b hb => hΨexp a ha.1 b hb.1
  -- the set to be covered, in the parametrising space
  set γ : Set (Fin (d - 1) → ℝ) := Ψ ⁻¹' (B ∩ U) ∩ V' with hγdef
  have hγV' : γ ⊆ V' := Set.inter_subset_right
  -- the cover in the parametrising space
  obtain ⟨ι, hcnt, cc, AA, hccR, hccsub, hcccov, hccimg, hccflat⟩ := hmain V' γ hV'open hγV'
  -- the composite charts
  let c' : ι → ChartDatum d := fun i => ChartDatum.comp hΨ1 hΨexp' (cc i) (hccR i)
  have hmemγ : ∀ y ∈ U, y ∈ B → y ∈ R → G y = 0 → y ∈ Ψ '' γ := by
    intro y hyU hyB hyR hyG
    have hyV : y ∈ Ψ '' V := hlev y hyU hyG
    have h1 : Ψ '' (V ∩ Ψ ⁻¹' R) = Ψ '' V ∩ R := by
      ext z
      constructor
      · rintro ⟨u, ⟨huV, huR⟩, rfl⟩
        exact ⟨⟨u, huV, rfl⟩, huR⟩
      · rintro ⟨⟨u, huV, rfl⟩, huR⟩
        exact ⟨u, ⟨huV, huR⟩, rfl⟩
    have hy' : y ∈ Ψ '' V' := by
      rw [hV'def, h1]
      exact ⟨hyV, hyR⟩
    have h2 : Ψ '' (Ψ ⁻¹' (B ∩ U) ∩ V') = (B ∩ U) ∩ Ψ '' V' := by
      ext z
      constructor
      · rintro ⟨u, ⟨hu1, hu2⟩, rfl⟩
        exact ⟨hu1, ⟨u, hu2, rfl⟩⟩
      · rintro ⟨hz1, u, hu2, rfl⟩
        exact ⟨u, ⟨hz1, hu2⟩, rfl⟩
    rw [hγdef, h2]
    exact ⟨⟨hyB, hyU⟩, hy'⟩
  refine ⟨U, Ψ '' γ, hUopen, hxU, ?_, hmemγ, ?_⟩
  · rintro y ⟨u, hu, rfl⟩
    exact hu.1.1
  · refine ⟨ι, hcnt, c', fun i => Ψ '' AA i, ?_, ?_, ?_, ?_, ?_⟩
    · -- images of closed balls stay inside `R`
      intro i
      show (Ψ ∘ (cc i).γ) '' Metric.closedBall (cc i).base (cc i).rad ⊆ R
      rw [Set.image_comp]
      exact (Set.image_mono (hccR i)).trans hΨV'R
    · -- pieces inside the covered set
      intro i
      exact Set.image_mono (hccsub i)
    · -- pieces cover the covered set
      rintro y ⟨u, hu, rfl⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcccov hu)
      exact Set.mem_iUnion.mpr ⟨i, ⟨u, hi, rfl⟩⟩
    · -- pieces inside the images of the open balls
      intro i
      show Ψ '' AA i ⊆ (Ψ ∘ (cc i).γ) '' Metric.ball (cc i).base (cc i).rad
      rw [Set.image_comp]
      exact Set.image_mono (hccimg i)
    · -- flatness
      intro G' hG' i u hu hgu
      obtain ⟨hG'cd, hG'0⟩ := hG'
      have hFcd : ContDiffOn ℝ s (fun z => G' (Ψ z)) V' :=
        hG'cd.comp (hΨcd.mono Set.inter_subset_left) (fun z hz => hΨV'R ⟨z, hz, rfl⟩)
      have hF0 : ∀ z ∈ γ, (fun z => G' (Ψ z)) z = 0 := fun z hz => hG'0 (Ψ z) hz.1.1
      have hne : (cc i).γ u ∈ AA i := by
        change (Ψ ∘ (cc i).γ) u ∈ Ψ '' AA i at hgu
        obtain ⟨a, haA, haeq⟩ := hgu
        have haV : a ∈ V := (hγV' (hccsub i haA)).1
        have huV : (cc i).γ u ∈ V := by
          have h1 : u ∈ Metric.closedBall (cc i).base (cc i).rad := Metric.ball_subset_closedBall hu
          exact (hccR i ⟨u, h1, rfl⟩).1
        have haeq' : Ψ a = Ψ ((cc i).γ u) := haeq
        exact (hΨinj haV huV haeq') ▸ haA
      exact hccflat (fun z => G' (Ψ z)) ⟨hFcd, hF0⟩ i u hu hne

/-! ## The induction -/

/-- **Morse's criticality theorem, inductive form.**  For every `s ≥ 0`, every dimension `d`, every
open set `R ⊆ ℝ^d` and every `B ⊆ R` there is a countable chart cover of `B` inside `R` such that
every `C^s` function on `R` vanishing on `B` is flat of order `s` along each piece. -/
theorem morseCover_all (h333 : LevelSetParam) :
    ∀ s d (R B : Set (Fin d → ℝ)), IsOpen R → B ⊆ R → MorseCover s d R B := by
  intro s
  refine Nat.strongRecOn (motive := fun s' => ∀ d (R B : Set (Fin d → ℝ)), IsOpen R → B ⊆ R →
      MorseCover s' d R B) s ?_
  intro s ihs d
  refine Nat.strongRecOn (motive := fun d' => ∀ (R B : Set (Fin d' → ℝ)), IsOpen R → B ⊆ R →
      MorseCover s d' R B) d ?_
  intro d ihd R B hR hBR
  classical
  rcases Nat.eq_zero_or_pos s with hs0 | hs
  · subst hs0
    exact morseCover_zero hR hBR
  · -- the `α`/`β` decomposition
    set α : Set (Fin d → ℝ) := morseAlpha s d R B with hαdef
    have hαB : α ⊆ B := morseAlpha_subset s d R B
    have hαR : α ⊆ R := hαB.trans hBR
    have hgrad : ∀ G : (Fin d → ℝ) → ℝ, ContDiffOn ℝ s G R → (∀ x ∈ B, G x = 0) →
        ∀ y ∈ α, fderiv ℝ G y = 0 := fun G hG hG0 y hy => morseAlpha_grad hG hG0 hy
    have hprev : ChartCover (s - 1) d R α
        (fun G => ContDiffOn ℝ (s - 1) G R ∧ ∀ x ∈ α, G x = 0) :=
      ihs (s - 1) (by omega) d R α hR hαR
    have hαcover : ChartCover s d R α (fun G => ContDiffOn ℝ s G R ∧ ∀ x ∈ B, G x = 0) :=
      chartCover_upgrade hs hR hαB hprev hgrad
    set β : Set (Fin d → ℝ) := B \ α with hβdef
    have hβempty0 : d = 0 → β = ∅ := by
      intro hd0
      subst hd0
      rw [hβdef]
      refine Set.eq_empty_iff_forall_notMem.mpr (fun y hy => hy.2 ?_)
      refine ⟨hy.1, fun G hG hG0 => ?_⟩
      ext v
      rw [Subsingleton.elim v 0, map_zero, zero_apply]
    by_cases hβ : β = ∅
    · -- everything is `α`
      have hBα : B ⊆ α := by
        intro y hy
        by_contra hcon
        have hmem : y ∈ β := by rw [hβdef]; exact ⟨hy, hcon⟩
        rw [hβ] at hmem
        exact hmem
      have hαeq : α = B := Set.Subset.antisymm hαB hBα
      exact hαeq ▸ hαcover
    · have hd : 1 ≤ d := by
        rcases Nat.eq_zero_or_pos d with h | h
        · exact absurd (hβempty0 h) hβ
        · exact h
      -- witnesses for the points of `β`
      have hwit : ∀ x ∈ β, ∃ G : (Fin d → ℝ) → ℝ, ContDiffOn ℝ s G R ∧
          (∀ y ∈ B, G y = 0) ∧ fderiv ℝ G x ≠ 0 := by
        intro x hx
        by_contra hcon
        exact hx.2 ⟨hx.1, fun G hG hG0 => by
          by_contra hgrad'
          exact hcon ⟨G, hG, hG0, hgrad'⟩⟩
      have hex : ∀ x : Fin d → ℝ, ∃ G : (Fin d → ℝ) → ℝ,
          x ∈ β → ContDiffOn ℝ s G R ∧ (∀ y ∈ B, G y = 0) ∧ fderiv ℝ G x ≠ 0 := by
        intro x
        by_cases hx : x ∈ β
        · obtain ⟨G, h1, h2, h3⟩ := hwit x hx
          exact ⟨G, fun _ => ⟨h1, h2, h3⟩⟩
        · exact ⟨fun _ => 0, fun h => absurd h hx⟩
      choose Gx hGx using hex
      -- the local covers
      have hex2 : ∀ x : Fin d → ℝ, ∃ (U Z : Set (Fin d → ℝ)),
          x ∈ β → IsOpen U ∧ x ∈ U ∧ Z ⊆ B ∧
            (∀ y ∈ U, y ∈ B → y ∈ R → Gx x y = 0 → y ∈ Z) ∧
            ChartCover s d R Z (fun G' => ContDiffOn ℝ s G' R ∧ ∀ y ∈ B, G' y = 0) := by
        intro x
        by_cases hx : x ∈ β
        · obtain ⟨U, Z, hUo, hxU, hZB, hZU, hcov⟩ :=
            cover_beta h333 hd hs hR (fun R' B' hR' hB' => ihd (d - 1) (by omega) R' B' hR' hB')
              hx.1 (hBR hx.1) (hGx x hx).1 (hGx x hx).2.1 (hGx x hx).2.2
          exact ⟨U, Z, fun _ => ⟨hUo, hxU, hZB, hZU, hcov⟩⟩
        · exact ⟨univ, ∅, fun h => absurd h hx⟩
      choose U Z hUZ using hex2
      -- a countable subcover of `β`
      obtain ⟨T, hTcount, hTcov⟩ := exists_countable_subcover
        (fun x : Fin d → ℝ => if x ∈ β then U x else ∅)
        (fun x => by
          by_cases hx : x ∈ β
          · simpa [hx] using (hUZ x hx).1
          · simpa [hx] using isOpen_empty)
        (fun x hx => by
          rw [if_pos hx]
          exact (hUZ x hx).2.1)
      set C : Set (Fin d → ℝ) := {x | x ∈ T ∧ x ∈ β} with hCdef
      have hCcount : C.Countable := hTcount.mono (fun x hx => hx.1)
      have hCcov : β ⊆ ⋃ x ∈ C, U x := by
        intro y hy
        obtain ⟨x, hxT, hxy⟩ := Set.mem_iUnion₂.mp (hTcov hy)
        have hxβ : x ∈ β := by
          by_contra hx
          rw [if_neg hx] at hxy
          exact hxy
        exact Set.mem_iUnion₂.mpr ⟨x, ⟨hxT, hxβ⟩, by simpa [if_pos hxβ] using hxy⟩
      -- the cover of `β`
      have hβcover : ChartCover s d R β
          (fun G' => ContDiffOn ℝ s G' R ∧ ∀ y ∈ B, G' y = 0) :=
        chartCover_iUnion (B := β) hCcount.to_subtype (fun x : C => Z x.1 ∩ β)
          (fun x => ChartCover.restrict (hUZ x.1 x.2.2).2.2.2.2 Set.inter_subset_left)
          (fun x => Set.inter_subset_right)
          (fun y hy => by
            obtain ⟨x, hxC, hxy⟩ := Set.mem_iUnion₂.mp (hCcov hy)
            have hxβ : x ∈ β := hxC.2
            have hzero : Gx x y = 0 := (hGx x hxβ).2.1 y hy.1
            have hyZ : y ∈ Z x := (hUZ x hxβ).2.2.2.1 y hxy hy.1 (hBR hy.1) hzero
            exact Set.mem_iUnion.mpr ⟨⟨x, hxC⟩, hyZ, hy⟩)
      -- assemble
      exact ChartCover.union hαcover hβcover hαB (fun y hy => (hβdef ▸ hy).1)
        (fun y hy => by
          by_cases h : y ∈ α
          · exact Or.inl h
          · exact Or.inr (by rw [hβdef]; exact ⟨hy, h⟩))

/-- The target form of the inductive statement (with the ambient space all of `ℝ^d`). -/
theorem morseCover_univ (h333 : LevelSetParam) (s d : ℕ) (B : Set (Fin d → ℝ)) :
    ChartCover s d univ B (fun G => ContDiffOn ℝ s G univ ∧ ∀ x ∈ B, G x = 0) :=
  morseCover_all h333 s d univ B isOpen_univ (Set.subset_univ B)

end

end Work.WilE9G.Sard
