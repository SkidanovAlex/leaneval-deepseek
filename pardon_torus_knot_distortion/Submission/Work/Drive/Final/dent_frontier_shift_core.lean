import Mathlib
import Submission.Work.Drive.Final.AnyEventDefs
import Submission.Work.Drive.Mono.TiltedTraceData

namespace Work.Drive.Final

noncomputable section

/-- **Frontier is a local notion, transported by a homeomorphism.**  Let `φ` be a homeomorphism of
a topological space, `V` an open neighbourhood of `x` on which two sets `A'` and `A` correspond
under `φ` (`z ∈ A' ↔ φ z ∈ A`).  Then `x` lies on the frontier of `A'` exactly when `φ x` lies on
the frontier of `A`.

Both inclusions only use points near `x`, so the local agreement suffices: `φ` carries every
neighbourhood of `x` onto one of `φ x` and the correspondence of memberships is inherited by the
complements. -/
private theorem frontier_mem_iff_of_local_homeomorph {X : Type*} [TopologicalSpace X]
    (φ : X ≃ₜ X) {A A' : Set X} {x : X} {V : Set X} (hV : IsOpen V) (hxV : x ∈ V)
    (h : ∀ z ∈ V, (z ∈ A' ↔ φ z ∈ A)) :
    (x ∈ frontier A' ↔ φ x ∈ frontier A) := by
  rw [frontier_eq_closure_inter_closure, frontier_eq_closure_inter_closure]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [mem_closure_iff] at h1 ⊢
      intro O hO hxO
      have hopen : IsOpen (φ ⁻¹' O ∩ V) := (hO.preimage φ.continuous).inter hV
      have hxmem : x ∈ φ ⁻¹' O ∩ V := ⟨hxO, hxV⟩
      obtain ⟨z, ⟨hzO, hzV⟩, hzA'⟩ := h1 _ hopen hxmem
      exact ⟨φ z, hzO, (h z hzV).mp hzA'⟩
    · rw [mem_closure_iff] at h2 ⊢
      intro O hO hxO
      have hopen : IsOpen (φ ⁻¹' O ∩ V) := (hO.preimage φ.continuous).inter hV
      have hxmem : x ∈ φ ⁻¹' O ∩ V := ⟨hxO, hxV⟩
      obtain ⟨z, ⟨hzO, hzV⟩, hzA'⟩ := h2 _ hopen hxmem
      exact ⟨φ z, hzO, fun hc => hzA' ((h z hzV).mpr hc)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [mem_closure_iff] at h1 ⊢
      intro O hO hxO
      have hOV : IsOpen (O ∩ V) := hO.inter hV
      have hxOV : φ x ∈ φ '' (O ∩ V) := ⟨x, ⟨hxO, hxV⟩, rfl⟩
      obtain ⟨y, hyO, hyA⟩ := h1 _ (φ.isOpenMap _ hOV) hxOV
      obtain ⟨z, ⟨hzO, hzV⟩, rfl⟩ := hyO
      exact ⟨z, hzO, (h z hzV).mpr hyA⟩
    · rw [mem_closure_iff] at h2 ⊢
      intro O hO hxO
      have hOV : IsOpen (O ∩ V) := hO.inter hV
      have hxOV : φ x ∈ φ '' (O ∩ V) := ⟨x, ⟨hxO, hxV⟩, rfl⟩
      obtain ⟨y, hyO, hyA⟩ := h2 _ (φ.isOpenMap _ hOV) hxOV
      obtain ⟨z, ⟨hzO, hzV⟩, rfl⟩ := hyO
      exact ⟨z, hzO, fun hc => hyA ((h z hzV).mp hc)⟩

open LeanEval.KnotTheory.PardonDistortion in
/-- **The frontier of the shifted level is the translate of the frontier of the original level**, in
the core of the dent.  Writing `λ' = ℓ D.centre - D.a' * ℓ D.d`, for every point `x` of the open ball
`‖x - D.centre‖ < D.r / 2` (where the dent cutoff is constantly `1`, so the deformation is the
translation by `D.a' • D.d`, and where the box is preserved by the deformation): `x` is in the
frontier of the removed set at level `λ'` if and only if its translate `x + D.a' • D.d` is in the
frontier of the removed set at level `ℓ D.centre`. -/
theorem dent_frontier_shift_core {ψ : Submission.Diffeo} {K : Knot} {s u h R : ℝ}
    {c v : R3} {σ : Equiv.Perm (Fin 3)} {ℓ : R3 →L[ℝ] ℝ} {U : Set R3}
    (D : Work.Drive.Final.AnyDentDatum ψ K s c σ u v h R ℓ U)
    (hχ1 : ∀ t : ℝ, |t| ≤ 1 / 2 → D.χ t = 1) {x : R3}
    (hx : ‖x - D.centre‖ < D.r / 2) :
    (x ∈ frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ
        (ℓ D.centre - D.a' * ℓ D.d)) ↔
      x + D.a' • D.d ∈ frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ
        (ℓ D.centre))) := by
  classical
  -- the deformation on the core of the dent is the translation `T`
  set T : R3 ≃ₜ R3 := Homeomorph.addRight (D.a' • D.d) with hT
  have hTcoe : ∀ z : R3, T z = z + D.a' • D.d := fun z => by rw [hT]; rfl
  -- on the core, membership in the shifted removed set is membership of the translate in the
  -- removed set at the level of the centre
  have hloc : ∀ z ∈ Metric.ball D.centre (D.r / 2),
      (z ∈ Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre - D.a' * ℓ D.d) ↔
        T z ∈ Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre)) := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have hzr : ‖z - D.centre‖ ≤ D.r := by linarith [D.r_pos]
    -- the cutoff is `1` throughout the core
    have hchi : D.χ (‖z - D.centre‖ / D.r) = 1 := by
      apply hχ1
      have hlt : ‖z - D.centre‖ / D.r < 1 / 2 := by
        rw [div_lt_iff₀ D.r_pos]; linarith
      rw [abs_of_nonneg (div_nonneg (norm_nonneg _) (le_of_lt D.r_pos))]
      exact le_of_lt hlt
    have hdef : D.deform z = T z := by
      rw [hTcoe, AnyDentDatum.deform, dentDeform, hchi, mul_one]
    -- the box is preserved (a datum property)
    have hbox : (z ∈ Submission.PBox s c σ ↔ T z ∈ Submission.PBox s c σ) := by
      rw [← hdef]; exact D.box_pres z hzr
    -- the slab coordinate is unchanged (`d ⟂ v`)
    have hslab : (|inner ℝ v z - (inner ℝ v c + u)| ≤ h ↔
        |inner ℝ v (T z) - (inner ℝ v c + u)| ≤ h) := by
      have hv : inner ℝ v (T z) = inner ℝ v z := by
        rw [hTcoe, inner_add_right, inner_smul_right, D.d_orth_v, mul_zero, add_zero]
      rw [hv]
    -- the wall coordinate shifts by the constant `a' * ℓ d`
    have hlev : (ℓ z < ℓ D.centre - D.a' * ℓ D.d ↔ ℓ (T z) < ℓ D.centre) := by
      have hl : ℓ (T z) = ℓ z + D.a' * ℓ D.d := by
        rw [hTcoe, map_add, map_smul, smul_eq_mul]
      rw [hl]; constructor <;> intro hh <;> linarith
    simp only [Work.Drive.Mono.tiltedLevelRemoved, Set.mem_sdiff, Set.mem_inter_iff,
      Set.mem_ofPred_eq, Work.Drive.EpsForm.tiltedSlabClosed]
    rw [hbox, hslab, hlev]
  -- the frontier is local, and the correspondence holds on the whole open core
  have h := frontier_mem_iff_of_local_homeomorph T (Metric.isOpen_ball) (x := x)
      (V := Metric.ball D.centre (D.r / 2)) (by rw [Metric.mem_ball, dist_eq_norm]; exact hx) hloc
  simpa [hTcoe x] using h

end

end Work.Drive.Final
