import Mathlib
import Submission.Work.Drive.endsHomotopy

open Manifold
open scoped Manifold ContDiff

namespace Work.Drive

open Set Filter
open scoped Topology

noncomputable section

/-!
## The two bad sets of the perturbation paths are the rays `ℝ • V y`, `ℝ • W y`

The material the target needs beyond `Submission/Work/Drive/endsHomotopy.lean`: the perturbation
path `t ↦ V y + (t χ y) • p` can only vanish (for `t ∈ [0,1]`, `y` in the box) at a vector `p`
lying on one of the lines `ℝ • V y` over the compact box; and each of these two line-cones is
*closed* with *empty interior*.  The complement of their union is therefore a nonempty open set,
and the missing interior of the interpolation's bad set can be removed from it.

(`Eucl 3 = ℝ⁴` here, i.e. `Eucl n = ℝ^{n+1}`: the codimension `1` is what makes the argument work.)
-/

/-- The union of the lines `ℝ • V y` over the parameter box `□ = [0,1]²`: the set of perturbation
vectors `p` for which the path `t ↦ V y + (t χ y) • p` can vanish somewhere on `[0,1] × □`. -/
def rayCone (V : EuclideanSpace ℝ (Fin 2) → Eucl 3) : Set (Eucl 3) :=
  {p | ∃ (c : ℝ) (y : EuclideanSpace ℝ (Fin 2)),
    y ∈ Submission.Drive.unitBox 1 ∧ p = c • V y}

/-- The bad set of the perturbed straight-line interpolation: the image of the solving map
`pertSolve` over the parameters at which `p` is actually determined by the vanishing condition. -/
def interpBad (V W : EuclideanSpace ℝ (Fin 2) → Eucl 3) (χ : EuclideanSpace ℝ (Fin 2) → ℝ) :
    Set (Eucl 3) :=
  pertSolve V W χ '' {q : ℝ × EuclideanSpace ℝ (Fin 2) |
    q.1 ∈ Set.Icc (0 : ℝ) 1 ∧ q.2 ∈ Submission.Drive.unitBox 1 ∧ χ q.2 ≠ 0}

/-- **The line-cone over the box is closed.**  `hVne` on the compact box gives a uniform lower bound
`‖V y‖ ≥ δ > 0`, hence the parameter of a converging sequence `cₙ • V yₙ → p` is bounded. -/
theorem rayCone_isClosed (V : EuclideanSpace ℝ (Fin 2) → Eucl 3) (hV : Continuous V)
    (hVne : ∀ y ∈ Submission.Drive.unitBox 1, V y ≠ 0) : IsClosed (rayCone V) := by
  have hne : (Submission.Drive.unitBox 1).Nonempty :=
    ⟨0, by intro i; simp⟩
  obtain ⟨y₀, hy₀, hmin⟩ := (isCompact_unitBox 1).exists_isMinOn hne hV.norm.continuousOn
  have hδpos : 0 < ‖V y₀‖ := norm_pos_iff.mpr (hVne y₀ hy₀)
  have hδ : ∀ y ∈ Submission.Drive.unitBox 1, ‖V y₀‖ ≤ ‖V y‖ := hmin
  refine IsSeqClosed.isClosed ?_
  intro u p hu hpu
  have hex : ∀ n, ∃ c : ℝ, ∃ y, y ∈ Submission.Drive.unitBox 1 ∧ u n = c • V y :=
    fun n => hu n
  choose c y hy huy using hex
  obtain ⟨a, ha, φ, hφ, hφt⟩ := (isCompact_unitBox 1).tendsto_subseq hy
  have hyφ : Tendsto (fun n => y (φ n)) atTop (𝓝 a) := by
    simpa [Function.comp_def] using hφt
  have huφ : Tendsto (fun n => u (φ n)) atTop (𝓝 p) := hpu.comp hφ.tendsto_atTop
  have hVyφ : Tendsto (fun n => V (y (φ n))) atTop (𝓝 (V a)) := (hV.tendsto a).comp hyφ
  set K : ℝ := (‖p‖ + 1) / ‖V y₀‖ with hK
  have hev : ∀ᶠ n in atTop, c (φ n) ∈ Set.Icc (-K) K := by
    filter_upwards
      [huφ.norm.eventually (isOpen_Iio.mem_nhds (show ‖p‖ < ‖p‖ + 1 by linarith))] with n hn
    have hnorm : ‖u (φ n)‖ = |c (φ n)| * ‖V (y (φ n))‖ := by
      rw [huy (φ n), norm_smul, Real.norm_eq_abs]
    have hle : ‖V y₀‖ ≤ ‖V (y (φ n))‖ := hδ _ (hy (φ n))
    have hmul : |c (φ n)| * ‖V y₀‖ ≤ |c (φ n)| * ‖V (y (φ n))‖ :=
      mul_le_mul_of_nonneg_left hle (abs_nonneg _)
    rw [hnorm] at hn
    have h2 : |c (φ n)| * ‖V y₀‖ ≤ ‖p‖ + 1 := by linarith
    have h3 : |c (φ n)| ≤ K := by
      rw [hK]
      exact (le_div_iff₀ hδpos).mpr h2
    exact ⟨by linarith [neg_abs_le (c (φ n))], le_trans (le_abs_self _) h3⟩
  obtain ⟨b, _hb, ψ, hψ, hψt⟩ := tendsto_subseq_of_frequently_bounded (X := ℝ)
    (s := Set.Icc (-K) K) isCompact_Icc.isBounded hev.frequently
  have hψt' : Tendsto (fun m => c (φ (ψ m))) atTop (𝓝 b) := by
    simpa [Function.comp_def] using hψt
  have hnum : Tendsto (fun m => c (φ (ψ m)) • V (y (φ (ψ m)))) atTop (𝓝 (b • V a)) :=
    hψt'.smul (hVyφ.comp hψ.tendsto_atTop)
  have hu2 : Tendsto (fun m => u (φ (ψ m))) atTop (𝓝 p) := huφ.comp hψ.tendsto_atTop
  have hnum' : Tendsto (fun m => u (φ (ψ m))) atTop (𝓝 (b • V a)) :=
    hnum.congr' (Filter.Eventually.of_forall fun m => (huy (φ (ψ m))).symm)
  exact ⟨b, a, ha, tendsto_nhds_unique hu2 hnum'⟩

/-- **The line-cone over the box has empty interior**: it is the image of the smooth map
`(c, y) ↦ c • V y` from the three-dimensional `ℝ × ℝ²` into the four-dimensional `Eucl 3`. -/
theorem rayCone_interior_eq_empty (V : EuclideanSpace ℝ (Fin 2) → Eucl 3)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) : interior (rayCone V) = ∅ := by
  have hfin : Module.finrank ℝ (ℝ × EuclideanSpace ℝ (Fin 2)) < Module.finrank ℝ (Eucl 3) := by
    rw [Module.finrank_prod, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]
    norm_num
  have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × EuclideanSpace ℝ (Fin 2) => q.1 • V q.2) :=
    contDiff_fst.smul (hV.comp contDiff_snd)
  have h := interior_image_empty_of_contDiffOn hfin isOpen_univ hf.contDiffOn
    (K := Set.univ ×ˢ Submission.Drive.unitBox 1) (fun q _ => trivial)
  have heq : (fun q : ℝ × EuclideanSpace ℝ (Fin 2) => q.1 • V q.2) ''
      (Set.univ ×ˢ Submission.Drive.unitBox 1) = rayCone V := by
    ext p
    constructor
    · rintro ⟨q, ⟨-, hq⟩, rfl⟩
      exact ⟨q.1, q.2, hq, rfl⟩
    · rintro ⟨c, y, hy, rfl⟩
      exact ⟨(c, y), ⟨trivial, hy⟩, rfl⟩
  rw [heq] at h
  exact h

/-- **The bad set of the interpolation has empty interior**: it is the image of the smooth solving
map `pertSolve` over a three-dimensional parameter set. -/
theorem interior_interpBad_eq_empty {V W : EuclideanSpace ℝ (Fin 2) → Eucl 3}
    {χ : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) :
    interior (interpBad V W χ) = ∅ := by
  have hfin : Module.finrank ℝ (ℝ × EuclideanSpace ℝ (Fin 2)) < Module.finrank ℝ (Eucl 3) := by
    rw [Module.finrank_prod, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]
    norm_num
  set Vset : Set (ℝ × EuclideanSpace ℝ (Fin 2)) := {q | χ q.2 ≠ 0} with hVset
  have hVopen : IsOpen Vset := by
    rw [hVset]
    exact (isOpen_ne (x := (0 : ℝ))).preimage (hχ.continuous.comp continuous_snd)
  have hsmooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pertSolve V W χ) Vset := by
    refine ContDiffOn.neg ?_
    have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℝ × EuclideanSpace ℝ (Fin 2) => (χ q.2)⁻¹) Vset :=
      ContDiffOn.inv (hχ.comp_contDiffOn contDiffOn_snd) (fun q hq => hq)
    have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℝ × EuclideanSpace ℝ (Fin 2) => interpLiftP V W q.1 q.2) Vset :=
      (contDiff_interpLiftP hV hW).contDiffOn
    exact h1.smul h2
  have hKV : {q : ℝ × EuclideanSpace ℝ (Fin 2) |
      q.1 ∈ Set.Icc (0 : ℝ) 1 ∧ q.2 ∈ Submission.Drive.unitBox 1 ∧ χ q.2 ≠ 0} ⊆ Vset :=
    fun q hq => hq.2.2
  exact interior_image_empty_of_contDiffOn hfin hVopen hsmooth hKV

/-! ### The three avoidance lemmas

`p` outside `interpBad V W χ` kills the perturbed interpolation; `p` outside `rayCone V` (resp.
`rayCone W`) kills the perturbation path of `V` (resp. `W`). -/

/-- A perturbation vector outside the interpolation's bad set makes the perturbed straight-line
interpolation nonvanishing (the zeros of `χ` are handled by `hgood`). -/
theorem interpLiftP_ne_zero_of_notMem_interpBad
    (V W : EuclideanSpace ℝ (Fin 2) → Eucl 3) (χ : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hgood : ∀ y ∈ Submission.Drive.unitBox 1, χ y = 0 →
      ∀ s ∈ Set.Icc (0 : ℝ) 1, interpLiftP V W s y ≠ 0)
    {p : Eucl 3} (hp : p ∉ interpBad V W χ) :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Submission.Drive.unitBox 1,
      interpLiftP V W s y + (χ y) • p ≠ 0 := by
  intro s hs y hy hzero
  by_cases hχ : χ y = 0
  · refine hgood y hy hχ s hs ?_
    rw [hχ, zero_smul, add_zero] at hzero
    exact hzero
  · refine hp ⟨(s, y), ⟨hs, hy, hχ⟩, ?_⟩
    have h1 : interpLiftP V W s y = -((χ y) • p) := by
      rw [eq_neg_iff_add_eq_zero]
      exact hzero
    have h2 : (χ y) • pertSolve V W χ (s, y) = (χ y) • p := by
      rw [pertSolve_smul_eq V W χ s y hχ, h1, neg_neg]
    have h3 : pertSolve V W χ (s, y) = p := by
      have := congrArg (fun v : Eucl 3 => (χ y)⁻¹ • v) h2
      simpa [smul_smul, inv_mul_cancel₀ hχ] using this
    exact h3

/-- A perturbation vector outside the line-cone of `V` makes the whole perturbation path
`t ↦ V y + (t χ y) • p` of `V` nonvanishing on `[0,1] × □`. -/
theorem path_ne_zero_of_notMem_rayCone (V : EuclideanSpace ℝ (Fin 2) → Eucl 3)
    (χ : EuclideanSpace ℝ (Fin 2) → ℝ) (hVne : ∀ y, V y ≠ 0) {p : Eucl 3}
    (hp : p ∉ rayCone V) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Submission.Drive.unitBox 1,
      V y + (t * χ y) • p ≠ 0 := by
  intro t _ y hy hzero
  by_cases htc : t * χ y = 0
  · have h0 : V y = 0 := by
      rw [htc, zero_smul, add_zero] at hzero
      exact hzero
    exact hVne y h0
  · refine hp ⟨(-((t * χ y)⁻¹)), y, hy, ?_⟩
    have h1 : (t * χ y) • p = -(V y) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact hzero
    have h2 : p = (-((t * χ y)⁻¹)) • V y := by
      have hc := congrArg (fun v : Eucl 3 => (t * χ y)⁻¹ • v) h1
      simp only [smul_neg, smul_smul, inv_mul_cancel₀ htc, one_smul] at hc
      rw [hc, neg_smul]
    exact h2

/-! ### Generic topological avoidance lemmas -/

/-- A nonempty open set can never be contained in a set of empty interior. -/
theorem exists_mem_notMem_of_isOpen_nonempty {X : Type*} [TopologicalSpace X] {s t : Set X}
    (hs : IsOpen s) (hne : s.Nonempty) (ht : interior t = ∅) : ∃ p ∈ s, p ∉ t := by
  by_contra h
  have hsub : s ⊆ t := fun p hp => by
    by_contra hpt
    exact h ⟨p, hp, hpt⟩
  have hsub' : s ⊆ interior t := by
    intro p hp
    exact mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset (hs.mem_nhds hp) hsub)
  rw [ht] at hsub'
  exact hne.ne_empty (Set.eq_empty_iff_forall_notMem.mpr fun p hp => hsub' hp)

/-- A point outside a closed set of empty interior and a set of empty interior, in the complement of
two closed sets of empty interior. -/
theorem exists_notMem_three_of_isClosed_interior_eq_empty {X : Type*} [TopologicalSpace X]
    [Nonempty X] {s t u : Set X} (hs : IsClosed s) (hsi : interior s = ∅) (ht : IsClosed t) (hti : interior t = ∅)
    (hu : interior u = ∅) : ∃ p, p ∉ s ∧ p ∉ t ∧ p ∉ u := by
  have hsne : s ≠ Set.univ := by
    intro h
    rw [h, interior_univ] at hsi
    exact Set.univ_nonempty.ne_empty hsi
  obtain ⟨p₀, hp₀⟩ := Set.nonempty_compl.mpr hsne
  have hne : (sᶜ ∩ tᶜ).Nonempty := by
    obtain ⟨p, hp1, hp2⟩ :=
      exists_mem_notMem_of_isOpen_nonempty (s := sᶜ) hs.isOpen_compl ⟨p₀, hp₀⟩ hti
    exact ⟨p, hp1, hp2⟩
  obtain ⟨p, hp, hpu⟩ := exists_mem_notMem_of_isOpen_nonempty
    (s := sᶜ ∩ tᶜ) (hs.isOpen_compl.inter ht.isOpen_compl) hne hu
  exact ⟨p, hp.1, hp.2, hpu⟩

/-- **The single perturbation that makes the two perturbation paths and the perturbed
straight-line interpolation of two lifts simultaneously nonvanishing.**

`V` and `W` are nonvanishing `C^∞` lifts of two class maps on the parameter square, `χ` is a `C^∞`
weight which is allowed to vanish only where the *unperturbed* interpolation `(1-s) • V y + s • W y`
is nonvanishing (`hgood`; the one place where the essentiality of the two class maps enters).  Then
there is one vector `p : Eucl 3 = ℝ⁴` for which all three families
`(1-s) • V + s • W + χ • p`, `V + t • χ • p`, `W + t • χ • p` are nonvanishing on `[0,1] × □`.

This turns the two end class maps `[V]`, `[W]` into the endpoints of a single homotopy through
seam-invariant class maps: with this `p` the three families above are the three pieces of that
homotopy (see `Submission/Work/Drive/ENDS_HOMOTOPY_NOTES.md`).

Proof ingredients (already on disk): the solving maps `Work.Drive.pertSolve` / `Work.Drive.pathSolve`
(`Drive/endsHomotopy.lean`) turn the nonvanishing conditions into *avoidance* conditions on `p`; each
bad set is the image of a smooth map from a `3`-dimensional source into the `4`-dimensional `Eucl 3`,
hence has empty interior (`Work.Drive.interior_image_empty_of_contDiffOn`, proved); the two *path* bad
sets are contained in closed sets of empty interior (the cones `⋃_y ℝ • V y`, `⋃_y ℝ • W y` over the
compact box; closedness is the bounded-`λ` argument, and for the empty interior the cone is covered by
the bounded pieces `|λ| ≤ n`), so the complement of their union is dense open, and removing the
interpolation's bad set (empty interior) keeps that complement nonempty. -/
theorem exists_perturbation_all_ne_zero
    (V W : EuclideanSpace ℝ (Fin 2) → Eucl 3) (χ : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hVne : ∀ y, V y ≠ 0) (hWne : ∀ y, W y ≠ 0)
    (hgood : ∀ y ∈ Submission.Drive.unitBox 1, χ y = 0 →
      ∀ s ∈ Set.Icc (0 : ℝ) 1, (1 - s) • V y + s • W y ≠ 0) :
    ∃ p : Eucl 3,
      (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Submission.Drive.unitBox 1,
          (1 - s) • V y + s • W y + (χ y) • p ≠ 0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Submission.Drive.unitBox 1, V y + (t * χ y) • p ≠ 0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Submission.Drive.unitBox 1, W y + (t * χ y) • p ≠ 0) := by
  obtain ⟨p, hpCV, hpCW, hpB⟩ :=
    exists_notMem_three_of_isClosed_interior_eq_empty (s := rayCone V) (t := rayCone W)
      (u := interpBad V W χ)
      (rayCone_isClosed V hV.continuous fun y _ => hVne y) (rayCone_interior_eq_empty V hV)
      (rayCone_isClosed W hW.continuous fun y _ => hWne y) (rayCone_interior_eq_empty W hW)
      (interior_interpBad_eq_empty hV hW hχ)
  refine ⟨p, ?_, ?_, ?_⟩
  · intro s hs y hy
    have hgood' : ∀ y ∈ Submission.Drive.unitBox 1, χ y = 0 →
        ∀ s ∈ Set.Icc (0 : ℝ) 1, interpLiftP V W s y ≠ 0 := by
      intro y hy h0 s hs
      simpa only [interpLiftP] using hgood y hy h0 s hs
    have h := interpLiftP_ne_zero_of_notMem_interpBad V W χ hgood' hpB s hs y hy
    simpa only [interpLiftP] using h
  · exact path_ne_zero_of_notMem_rayCone V χ hVne hpCV
  · exact path_ne_zero_of_notMem_rayCone W χ hWne hpCW

end

end Work.Drive
