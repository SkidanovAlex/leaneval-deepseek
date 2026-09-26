import Mathlib
import Submission.Work.Smooth.OneManifold.Plane.Basic
import Submission.Work.Smooth.Morse.Surface.isOpenInCarrier_image_of_isOpen

/-!
# Transport of a plane model to the surface

Let `ψ` be a diffeomorphism, `F = torus ψ` its surface, `param ψ : ℝ × ℝ → ℝ³` the parametrisation,
`Z ⊆ F` a subset of the surface, `B` an open set of parameters and `P ⊆ B` a "plane model": a
subset of the parameter plane such that, on `B`, the parameter point `q` lies in `P` exactly when
`param ψ q` lies in `Z`.  Equivalently (and this is the form used below)
`param ψ '' (B' ∩ P) = param ψ '' B' ∩ Z` for every open `B' ⊆ B`.

If `param ψ` is injective on `B` and the plane model `B ∩ P` is locally an arc
(`Work.Smooth.OneManifold.IsLocallyArcP`), then the part `param ψ '' B ∩ Z` of the surface is
locally Euclidean of dimension one — the local `1`-manifold structure
`Work.Smooth.OneManifold.IsLocallyEuclidean` needed by the classification of compact one-manifolds.

The proof transports the arc charts of the plane model along the parametrisation: the image of an
open piece of a chart is open in `F` (`Work.Smooth.Morse.Surface.isOpenInCarrier_image_of_isOpen`,
using that the parametrisation is an open map onto the surface), and it is identified with a
relatively open piece of `Z` by the model correspondence; hence `param ψ ∘ e` is a homeomorphism
of `ℝ` onto a neighbourhood of the corresponding point of `Z`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.OneManifold

noncomputable section

open scoped Topology

/-- An identity of surface pieces: intersecting `param ψ '' B₁` with `Z` is the same as
intersecting it with the whole `param ψ '' B ∩ Z`, for `B₁ ⊆ B`. -/
private theorem image_inter_eq {ψ : Submission.Diffeo} {B B₁ : Set (ℝ × ℝ)} {Z : Set R3}
    (h : B₁ ⊆ B) :
    Work.Smooth.Morse.param ψ '' B₁ ∩ Z
      = Work.Smooth.Morse.param ψ '' B₁ ∩ (Work.Smooth.Morse.param ψ '' B ∩ Z) := by
  ext z
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨w, hw, hwz⟩ := h1
    rw [← hwz] at h2 ⊢
    exact ⟨⟨w, hw, rfl⟩, ⟨⟨w, h hw, rfl⟩, h2⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2.2⟩

/-- **Transport of a plane model to the surface.**

Let `B` be an open set of parameters, `P ⊆ B` a plane model for the subset `Z` of the surface
(`param ψ '' (B' ∩ P) = param ψ '' B' ∩ Z` for every open `B' ⊆ B`), `param ψ` injective on `B` and
`B ∩ P` locally an arc.  Then `param ψ '' B ∩ Z` is locally Euclidean of dimension one. -/
theorem isLocallyEuclidean_image_of_param {ψ : Submission.Diffeo} {Z : Set R3}
    {B P : Set (ℝ × ℝ)} (hZc : Z ⊆ (Work.Smooth.Morse.torus ψ).carrier) (hB : IsOpen B)
    (hPB : P ⊆ B)
    (hident : ∀ B' : Set (ℝ × ℝ), IsOpen B' → B' ⊆ B →
      Work.Smooth.Morse.param ψ '' (B' ∩ P) = Work.Smooth.Morse.param ψ '' B' ∩ Z)
    (hinj : Set.InjOn (Work.Smooth.Morse.param ψ) B)
    (hloc : IsLocallyArcP (B ∩ P)) :
    IsLocallyEuclidean (Work.Smooth.Morse.param ψ '' B ∩ Z) := by
  classical
  have hXc : (Work.Smooth.Morse.param ψ '' B ∩ Z) ⊆ (Work.Smooth.Morse.torus ψ).carrier :=
    fun z hz => hZc hz.2
  intro y
  -- `y` is the image of a parameter point of `B ∩ P`
  have hyX : (y : R3) ∈ Work.Smooth.Morse.param ψ '' (B ∩ P) := by
    rw [hident B hB subset_rfl]
    exact y.2
  obtain ⟨q, hq, hqy⟩ := hyX
  obtain ⟨hqB, hqP⟩ := hq
  have hqBP : q ∈ B ∩ P := ⟨hqB, hqP⟩
  -- a chart of the plane model `B ∩ P` at `q`
  obtain ⟨c⟩ := hloc ⟨q, hqBP⟩
  -- its source is the trace of an open set of parameters
  obtain ⟨B₀, hB₀open, hB₀eq⟩ := isOpen_induced_iff.mp c.isOpen_V
  have hqB₀ : q ∈ B₀ := by
    have h1 : c.map 0 ∈ c.V := c.map_mem 0
    rw [← hB₀eq] at h1
    have h2 : (c.map 0 : ℝ × ℝ) ∈ B₀ := h1
    rw [c.map_zero] at h2
    exact h2
  -- the parameter set of the surface chart
  set C : Set (ℝ × ℝ) := (B₀ ∩ B) ∩ P with hCdef
  have hCsub : C ⊆ B ∩ P := fun z hz => ⟨hz.1.2, hz.2⟩
  have hCe : {z : ↥(B ∩ P) | (z : ℝ × ℝ) ∈ C} = c.V := by
    rw [← hB₀eq]
    ext z
    rw [hCdef]
    exact ⟨fun h => h.1.1, fun h => ⟨⟨h, z.2.1⟩, z.2.2⟩⟩
  -- the homeomorphism `ℝ ≃ₜ ↥C`
  let q' : ↥{z : ↥(B ∩ P) | (z : ℝ × ℝ) ∈ C} := ⟨⟨q, hqBP⟩, by rw [hCe]; exact c.mem_V⟩
  set e : ℝ ≃ₜ ↥C := c.homeo.trans ((Homeomorph.setCongr hCe.symm).trans
    (Work.Smooth.SphereJordan.LocalArc.subtypeSubtypeHomeomorph hCsub).symm) with he
  have he0 : ((e 0 : ↥C) : ℝ × ℝ) = q := by
    have h1 : (Homeomorph.setCongr hCe.symm (c.homeo 0) :
        ↥{z : ↥(B ∩ P) | (z : ℝ × ℝ) ∈ C}) = q' := by
      apply Subtype.ext
      show ((c.homeo 0 : ↥c.V) : ↥(B ∩ P)) = (⟨q, hqBP⟩ : ↥(B ∩ P))
      rw [show c.homeo 0 = ⟨⟨q, hqBP⟩, c.mem_V⟩ from c.homeo_zero]
    rw [he, Homeomorph.trans_apply, Homeomorph.trans_apply, h1]
    rfl
  -- the corresponding piece of the surface
  set V : Set R3 := Work.Smooth.Morse.param ψ '' C with hVdef
  have hVsub : V ⊆ Work.Smooth.Morse.param ψ '' B ∩ Z := by
    rintro z ⟨w, hw, rfl⟩
    refine ⟨⟨w, hw.1.2, rfl⟩, ?_⟩
    have h2 : Work.Smooth.Morse.param ψ w
        ∈ Work.Smooth.Morse.param ψ '' ((B ∩ B₀) ∩ P) :=
      ⟨w, ⟨⟨hw.1.2, hw.1.1⟩, hw.2⟩, rfl⟩
    rw [hident (B ∩ B₀) (hB.inter hB₀open) (fun t ht => ht.1)] at h2
    exact h2.2
  have hyV : (y : R3) ∈ V := ⟨q, ⟨⟨hqB₀, hqB⟩, hqP⟩, hqy⟩
  -- the openness of `V`
  have hVopen : IsOpenInSet (Work.Smooth.Morse.param ψ '' B ∩ Z) V := by
    have hVeq : V = Work.Smooth.Morse.param ψ '' (B ∩ B₀) ∩ Z := by
      rw [hVdef, hCdef]
      have hset : (B₀ ∩ B) ∩ P = (B ∩ B₀) ∩ P := by
        ext z
        exact ⟨fun h => ⟨⟨h.1.2, h.1.1⟩, h.2⟩, fun h => ⟨⟨h.1.2, h.1.1⟩, h.2⟩⟩
      rw [hset]
      exact hident (B ∩ B₀) (hB.inter hB₀open) (fun t ht => ht.1)
    rw [hVeq, image_inter_eq (show B ∩ B₀ ⊆ B from fun t ht => ht.1)]
    exact isOpenInSet_inter_of_isOpenInCarrier hXc
      (Work.Smooth.Morse.Surface.isOpenInCarrier_image_of_isOpen ψ (hB.inter hB₀open))
  -- the parametrisation of the piece
  let F : ℝ → ↥V := fun u =>
    ⟨Work.Smooth.Morse.param ψ (e u : ℝ × ℝ), ⟨(e u : ℝ × ℝ), (e u).2, rfl⟩⟩
  have hFinj : Function.Injective F := by
    intro u v huv
    have h1 : Work.Smooth.Morse.param ψ (e u : ℝ × ℝ)
        = Work.Smooth.Morse.param ψ (e v : ℝ × ℝ) := by
      have h := congrArg (fun z : ↥V => (z : R3)) huv
      simpa using h
    have h2 : (e u : ℝ × ℝ) = (e v : ℝ × ℝ) :=
      hinj (e u).2.1.2 (e v).2.1.2 h1
    exact e.injective (Subtype.ext h2)
  have hFsurj : Function.Surjective F := by
    intro z
    obtain ⟨w, hw, hwz⟩ := z.2
    refine ⟨e.symm ⟨w, hw⟩, ?_⟩
    apply Subtype.ext
    show Work.Smooth.Morse.param ψ (e (e.symm ⟨w, hw⟩) : ℝ × ℝ) = (z : R3)
    rw [Homeomorph.apply_symm_apply]
    exact hwz
  have hFcont : Continuous F :=
    Continuous.subtype_mk
      ((Work.Smooth.Morse.param_continuous ψ).comp
        (continuous_subtype_val.comp e.continuous)) _
  have hFopen : IsOpenMap F := by
    intro O hO
    have hOS : IsOpen (e '' O) := e.isOpenMap O hO
    obtain ⟨B₁, hB₁open, hB₁eq⟩ := isOpen_induced_iff.mp hOS
    have hB₁char : ∀ w : ↥C, (w : ℝ × ℝ) ∈ B₁ ↔ w ∈ e '' O := by
      intro w
      have := congrArg (fun s : Set ↥C => w ∈ s) hB₁eq
      simpa using this
    have hB₁eq' : Subtype.val '' (e '' O) = B₁ ∩ C := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨(hB₁char w).mpr hw, w.2⟩
      · rintro ⟨hzB₁, hzC⟩
        exact ⟨⟨z, hzC⟩, (hB₁char ⟨z, hzC⟩).mp hzB₁, rfl⟩
    have hbase : ∀ z : ℝ × ℝ, z ∈ (B ∩ B₁) ∩ C ↔ z ∈ Subtype.val '' (e '' O) := by
      intro z
      rw [hB₁eq']
      constructor
      · rintro ⟨⟨-, hzB₁⟩, hzC⟩
        exact ⟨hzB₁, hzC⟩
      · rintro ⟨hzB₁, hzC⟩
        exact ⟨⟨hzC.1.2, hzB₁⟩, hzC⟩
    have hFim : F '' O
        = Subtype.val ⁻¹' (Work.Smooth.Morse.param ψ '' ((B ∩ B₁) ∩ C)) := by
      ext z
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨(e u : ℝ × ℝ), (hbase (e u : ℝ × ℝ)).mpr ⟨e u, ⟨u, hu, rfl⟩, rfl⟩, rfl⟩
      · rintro ⟨w, hw, hwz⟩
        obtain ⟨w', hw', hw'w⟩ := (hbase w).mp hw
        obtain ⟨u, hu, huw'⟩ := hw'
        have hzF : F u = z := by
          apply Subtype.ext
          show Work.Smooth.Morse.param ψ (e u : ℝ × ℝ) = (z : R3)
          rw [huw', hw'w, hwz]
        exact ⟨u, hu, hzF⟩
    rw [hFim]
    have hpiece : Work.Smooth.Morse.param ψ '' ((B ∩ B₁) ∩ C)
        = Work.Smooth.Morse.param ψ '' ((B ∩ B₁) ∩ B₀) ∩ Z := by
      have hset : (B ∩ B₁) ∩ C = ((B ∩ B₁) ∩ B₀) ∩ P := by
        rw [hCdef]
        ext z
        constructor
        · rintro ⟨⟨hzB, hzB₁⟩, ⟨⟨hzB₀, -⟩, hzP⟩⟩
          exact ⟨⟨⟨hzB, hzB₁⟩, hzB₀⟩, hzP⟩
        · rintro ⟨⟨⟨hzB, hzB₁⟩, hzB₀⟩, hzP⟩
          exact ⟨⟨hzB, hzB₁⟩, ⟨⟨hzB₀, hzB⟩, hzP⟩⟩
      rw [hset]
      exact hident ((B ∩ B₁) ∩ B₀) ((hB.inter hB₁open).inter hB₀open)
        (fun t ht => ht.1.1)
    have hZopen : IsOpenInSet (Work.Smooth.Morse.param ψ '' B ∩ Z)
        (Work.Smooth.Morse.param ψ '' ((B ∩ B₁) ∩ C)) := by
      rw [hpiece, image_inter_eq (show (B ∩ B₁) ∩ B₀ ⊆ B from fun t ht => ht.1.1)]
      exact isOpenInSet_inter_of_isOpenInCarrier hXc
        (Work.Smooth.Morse.Surface.isOpenInCarrier_image_of_isOpen ψ
          ((hB.inter hB₁open).inter hB₀open))
    have hcont : Continuous (fun z : ↥V =>
        (⟨(z : R3), hVsub z.2⟩ : ↥(Work.Smooth.Morse.param ψ '' B ∩ Z))) :=
      Continuous.subtype_mk continuous_subtype_val _
    convert hZopen.preimage hcont using 1
    ext z
    rfl
  -- assemble the arc chart
  have h0 : (Equiv.ofBijective F ⟨hFinj, hFsurj⟩).toHomeomorphOfContinuousOpen hFcont hFopen 0
      = (⟨(y : R3), hyV⟩ : ↥V) := by
    apply Subtype.ext
    show Work.Smooth.Morse.param ψ (e 0 : ℝ × ℝ) = (y : R3)
    rw [he0]
    exact hqy
  refine ⟨{ V := Subtype.val ⁻¹' V
            isOpen_V := hVopen
            mem_V := hyV
            homeo := ((Equiv.ofBijective F ⟨hFinj, hFsurj⟩).toHomeomorphOfContinuousOpen
                hFcont hFopen).trans
              (Work.Smooth.SphereJordan.LocalArc.subtypeSubtypeHomeomorph hVsub)
            homeo_zero := ?_ }⟩
  rw [Homeomorph.trans_apply, h0]
  apply Subtype.ext
  apply Subtype.ext
  rfl

end

end Work.Smooth.OneManifold
