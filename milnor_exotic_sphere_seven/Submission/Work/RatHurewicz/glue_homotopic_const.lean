import Mathlib
import Submission.Work.RatHurewicz.AssemblyDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The gluing of the pieces of a cube is freely null-homotopic

`Work.RatHurewicz.glue` glues the based-ifications `Ψ (τ ∘ faceCM i (cval b))` of the faces of an
`(m+3)`-cube along `∂I^{m+3}`.  This file completes the "cancellation" half of Hutchings' `(2.5)`:
the gluing is *freely* null-homotopic.

The three stages of the classical argument are already pointwise in
`Submission/Work/RatHurewicz/assembly_null.lean`:

* `glueCancel`: sweep the dome of each piece (the `r`-sweep of the `K`-fillings) — it runs from
  `glue` to the clamped map `z ↦ τ (faceCM i (cval b) (radialPt (delG i z)))` (`glueCancel_zero`,
  `glueCancel_one_apply_face`);
* `clampFamily`: replace `radialPt` by the identity via `radialHom` — it runs from the clamped map
  to `τ|∂I^{m+3}` (`clampFamily_zero`, `clampFamily_one_apply`);
* `shrinkFamily`: collapse `τ|∂I^{m+3}` to the constant `τ 0` (`shrinkFamily_zero`,
  `shrinkFamily_one`).

What is missing there is the *joint continuity* in the boundary point and the time parameter: the
families are produced by `Classical.choose` from `exists_cubeBoundary`, which gives no information
about dependence on the parameter.  The remedy here is:

* `exists_cubeBoundary_prod`: the family version of `exists_cubeBoundary`, which glues finitely many
  continuous maps on the *products* `E i × Y` along a closed cover of `∂I^{n+1}`;
* the two families are then re-glued with it (`continuous_glueCancelVal_prod`,
  `continuous_clampFamilyVal_prod`), and the third stage is replaced by the explicitly defined
  `coneMap`, whose continuity is immediate;
* finally the three stages are concatenated in the time direction.
-/

open scoped unitInterval Topology
open Work.Stems.Cubical

namespace Work.RatHurewicz

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X}

/-! ## Gluing a family of continuous maps on a closed cover of the boundary of a cube

This is `exists_cubeBoundary` with an extra parameter `Y`: the functions to be glued are defined on
`↓E i × Y` and the resulting map on `∂I^{n+1} × Y`. -/

theorem exists_cubeBoundary_prod (n : ℕ) {X : Type} [TopologicalSpace X]
    {Y : Type} [TopologicalSpace Y] {ι : Type*} [Fintype ι]
    (E : ι → Set (IC (n + 1))) (hE : ∀ i, IsClosed (E i))
    (hcover : ∀ z : IC (n + 1), z ∈ Cube.boundary (Fin (n + 1)) → ∃ i, z ∈ E i)
    (f : ι → ↥(Cube.boundary (Fin (n + 1))) × Y → X)
    (hf : ∀ i, ContinuousOn (f i)
      {p : ↥(Cube.boundary (Fin (n + 1))) × Y | (p.1 : IC (n + 1)) ∈ E i})
    (hagree : ∀ (i j : ι) (p : ↥(Cube.boundary (Fin (n + 1))) × Y),
      (p.1 : IC (n + 1)) ∈ E i → (p.1 : IC (n + 1)) ∈ E j → f i p = f j p) :
    ∃ F : C(↥(Cube.boundary (Fin (n + 1))) × Y, X),
      ∀ (p : ↥(Cube.boundary (Fin (n + 1))) × Y) (i : ι),
        (p.1 : IC (n + 1)) ∈ E i → F p = f i p := by
  classical
  have hwit : ∀ z : ↥(Cube.boundary (Fin (n + 1))), ∃ i, (z : IC (n + 1)) ∈ E i :=
    fun z => hcover z.1 z.2
  let Ffun : ↥(Cube.boundary (Fin (n + 1))) × Y → X :=
    fun p => f (Classical.choose (hwit p.1)) p
  have hFval : ∀ (p : ↥(Cube.boundary (Fin (n + 1))) × Y) (i : ι),
      (p.1 : IC (n + 1)) ∈ E i → Ffun p = f i p :=
    fun p i hi => hagree _ i p (Classical.choose_spec (hwit p.1)) hi
  have hcont : Continuous Ffun := by
    rw [continuous_iff_isClosed]
    intro T hT
    have hsub : Ffun ⁻¹' T =
        ⋃ (i : ι), {p : ↥(Cube.boundary (Fin (n + 1))) × Y |
          (p.1 : IC (n + 1)) ∈ E i ∧ f i p ∈ T} := by
      ext p; constructor
      · intro hp
        exact Set.mem_iUnion.mpr ⟨Classical.choose (hwit p.1),
          Classical.choose_spec (hwit p.1), hp⟩
      · intro hp
        obtain ⟨i, hi, hT'⟩ := Set.mem_iUnion.mp hp
        rw [Set.mem_preimage, hFval p i hi]; exact hT'
    rw [hsub]
    refine isClosed_iUnion_of_finite fun i => ?_
    obtain ⟨U, hU, hUeq⟩ := (continuousOn_iff_isClosed.mp (hf i)) T hT
    have hC : IsClosed {p : ↥(Cube.boundary (Fin (n + 1))) × Y | (p.1 : IC (n + 1)) ∈ E i} :=
      (hE i).preimage (continuous_subtype_val.comp continuous_fst)
    have hpiece : {p : ↥(Cube.boundary (Fin (n + 1))) × Y |
          (p.1 : IC (n + 1)) ∈ E i ∧ f i p ∈ T}
        = U ∩ {p : ↥(Cube.boundary (Fin (n + 1))) × Y | (p.1 : IC (n + 1)) ∈ E i} := by
      ext p; constructor
      · rintro ⟨hpE, hpT⟩
        have hmem : p ∈ f i ⁻¹' T ∩
            {p : ↥(Cube.boundary (Fin (n + 1))) × Y | (p.1 : IC (n + 1)) ∈ E i} :=
          ⟨hpT, hpE⟩
        rw [hUeq] at hmem
        exact hmem
      · rintro ⟨hU', hpE⟩
        have hmem : p ∈ U ∩
            {p : ↥(Cube.boundary (Fin (n + 1))) × Y | (p.1 : IC (n + 1)) ∈ E i} := ⟨hU', hpE⟩
        rw [← hUeq] at hmem
        exact ⟨hpE, hmem.1⟩
    rw [hpiece]
    exact hU.inter hC
  exact ⟨⟨Ffun, hcont⟩, hFval⟩

/-! ## Joint continuity of the two `Classical.choose`-based families -/

theorem continuous_glueCancelVal_prod (N m : ℕ) (K : Tower x₀ N) (hN : m + 1 ≤ N)
    (τ : C(IC (m + 3), X)) (ib : Fin (m + 3) × Fin 2) :
    Continuous fun p : ↥(Cube.boundary (Fin (m + 3))) × unitInterval =>
      glueCancelVal N m K hN τ p.2 ib (p.1 : IC (m + 3)) :=
  (PsiB N m K hN (τ.comp (faceCM ib.1 (cval ib.2)))).continuous.comp
    (Continuous.subtype_mk ((continuous_unpinPt m).comp
      (((delG (m + 2) ib.1).continuous.comp
        (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd)) _)

theorem continuous_clampFamilyVal_prod (m : ℕ) (τ : C(IC (m + 3), X))
    (ib : Fin (m + 3) × Fin 2) :
    Continuous fun p : ↥(Cube.boundary (Fin (m + 3))) × unitInterval =>
      clampFamilyVal m τ p.2 ib (p.1 : IC (m + 3)) :=
  τ.continuous.comp ((faceCM ib.1 (cval ib.2)).continuous.comp
    ((radialHom (m + 2) (by omega)).continuous.comp
      (((delG (m + 2) ib.1).continuous.comp
        (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd)))

/-! ## The cone family collapsing `τ|∂I^{m+3}` to the constant `τ 0` -/

/-- The map `(z, s) ↦ τ ((1 - s) · z)`: the cone from `τ|∂I^{m+3}` to the constant `τ 0`. -/
def coneMap (m : ℕ) (τ : C(IC (m + 3), X)) :
    C(↥(Cube.boundary (Fin (m + 3))) × unitInterval, X) where
  toFun p := τ fun k => ⟨(1 - (p.2 : ℝ)) * (((p.1 : IC (m + 3)) k : unitInterval) : ℝ), by
    have h1 := (((p.1 : IC (m + 3)) k : unitInterval)).2.1
    have h2 := (((p.1 : IC (m + 3)) k : unitInterval)).2.2
    have hs0 := (p.2).2.1
    have hs1 := (p.2).2.2
    have hc : (0 : ℝ) ≤ 1 - (p.2 : ℝ) := by linarith
    constructor
    · nlinarith
    · nlinarith⟩
  continuous_toFun := by
    apply τ.continuous.comp
    apply continuous_pi
    intro k
    apply Continuous.subtype_mk
    have hz : Continuous fun p : ↥(Cube.boundary (Fin (m + 3))) × unitInterval =>
        (((p.1 : IC (m + 3)) k : unitInterval) : ℝ) :=
      continuous_subtype_val.comp ((continuous_apply k).comp
        (continuous_subtype_val.comp continuous_fst))
    have hs : Continuous fun p : ↥(Cube.boundary (Fin (m + 3))) × unitInterval =>
        (1 : ℝ) - (p.2 : ℝ) := by fun_prop
    exact hs.mul hz

theorem coneMap_zero (m : ℕ) (τ : C(IC (m + 3), X))
    (z : ↥(Cube.boundary (Fin (m + 3)))) :
    coneMap m τ (z, 0) = τ (z : IC (m + 3)) := by
  show τ (fun k => ⟨(1 - ((0 : unitInterval) : ℝ)) * ((z.1 k : unitInterval) : ℝ), _⟩) = τ z.1
  congr 1
  funext k
  exact Subtype.ext (by simp)

theorem coneMap_one (m : ℕ) (τ : C(IC (m + 3), X))
    (z : ↥(Cube.boundary (Fin (m + 3)))) :
    coneMap m τ (z, 1) = τ (0 : IC (m + 3)) := by
  show τ (fun k => ⟨(1 - ((1 : unitInterval) : ℝ)) * ((z.1 k : unitInterval) : ℝ), _⟩)
    = τ (0 : IC (m + 3))
  congr 1
  funext k
  exact Subtype.ext (by simp)

/-! ## The main theorem -/

theorem glue_homotopic_const {X : Type} [TopologicalSpace X] {x₀ : X}
    (N m : ℕ) (K : Work.RatHurewicz.Tower x₀ N) (hN : m + 1 ≤ N)
    (τ : C(Work.Stems.Cubical.IC (m + 3), X)) :
    ∃ (H : C(↥(Cube.boundary (Fin (m + 3))) × unitInterval, X)) (z : X),
      (∀ p, H (p, 0) = Work.RatHurewicz.glue N m K hN τ p) ∧ (∀ p, H (p, 1) = z) := by
  classical
  have hE : ∀ ib : Fin (m + 3) × Fin 2, IsClosed (faceSet m ib.1 ib.2) :=
    fun ib => isClosed_faceSet m ib.1 ib.2
  have hcover : ∀ z : IC (m + 3), z ∈ Cube.boundary (Fin (m + 3)) →
      ∃ ib : Fin (m + 3) × Fin 2, z ∈ faceSet m ib.1 ib.2 := by
    intro z hz
    obtain ⟨i, b, hb⟩ := exists_faceSet_of_mem_boundary m hz
    exact ⟨(i, b), hb⟩
  -- the cancellation family of the gluing, as a map on `∂I^{m+3} × I`
  obtain ⟨A, hA⟩ := exists_cubeBoundary_prod (m + 2)
    (fun ib : Fin (m + 3) × Fin 2 => faceSet m ib.1 ib.2) hE hcover
    (fun ib p => glueCancelVal N m K hN τ p.2 ib (p.1 : IC (m + 3)))
    (fun ib => (continuous_glueCancelVal_prod N m K hN τ ib).continuousOn)
    (fun ib ib' p hz hz' => by
      rcases ib with ⟨i, b⟩
      rcases ib' with ⟨i', b'⟩
      rcases eq_or_ne i i' with h | h
      · subst h
        have hb : b = b' := by
          have hc : cval b = cval b' := by rw [← hz, hz']
          fin_cases b <;> fin_cases b' <;> simp_all [cval]
        subst hb; rfl
      · exact unpinB_agree N m K hN τ i i' b b' h p.1 hz hz' p.2)
  -- the clamped family
  obtain ⟨B, hB⟩ := exists_cubeBoundary_prod (m + 2)
    (fun ib : Fin (m + 3) × Fin 2 => faceSet m ib.1 ib.2) hE hcover
    (fun ib p => clampFamilyVal m τ p.2 ib (p.1 : IC (m + 3)))
    (fun ib => (continuous_clampFamilyVal_prod m τ ib).continuousOn)
    (fun ib ib' p hz hz' => by
      rcases ib with ⟨i, b⟩
      rcases ib' with ⟨i', b'⟩
      rcases eq_or_ne i i' with h | h
      · subst h
        have hb : b = b' := by
          have hc : cval b = cval b' := by rw [← hz, hz']
          fin_cases b <;> fin_cases b' <;> simp_all [cval]
        subst hb; rfl
      · exact clampFamilyVal_agree m τ p.2 hz hz')
  -- the cone family
  let Cm : C(↥(Cube.boundary (Fin (m + 3))) × unitInterval, X) := coneMap m τ
  -- endpoints of the three stages
  have hA0 : ∀ z : ↥(Cube.boundary (Fin (m + 3))),
      A (z, (0 : unitInterval)) = glue N m K hN τ z := by
    intro z
    obtain ⟨i, b, hb⟩ := exists_faceSet_of_mem_boundary m z.2
    rw [hA (z, (0 : unitInterval)) (i, b) hb, glue_apply_face N m K hN τ (i, b) z hb]
    change PsiB N m K hN (τ.comp (faceCM i (cval b)))
        (unpinB m 0 (delG (m + 2) i (z : IC (m + 3))))
      = (piece N m K hN τ (i, b)) (delG (m + 2) i (z : IC (m + 3)))
    rw [Psi_unpinB_zero N m K hN (τ.comp (faceCM i (cval b)))
      (delG (m + 2) i (z : IC (m + 3)))]
    rfl
  have hA1 : ∀ z : ↥(Cube.boundary (Fin (m + 3))),
      A (z, (1 : unitInterval)) = glueCancel N m K hN τ 1 z := by
    intro z
    obtain ⟨i, b, hb⟩ := exists_faceSet_of_mem_boundary m z.2
    rw [hA (z, (1 : unitInterval)) (i, b) hb]
    exact (glueCancel_apply_face N m K hN τ 1 (i, b) z hb).symm
  have hB0 : ∀ z : ↥(Cube.boundary (Fin (m + 3))),
      B (z, (0 : unitInterval)) = clampFamily N m K hN τ 0 z := by
    intro z
    obtain ⟨i, b, hb⟩ := exists_faceSet_of_mem_boundary m z.2
    rw [hB (z, (0 : unitInterval)) (i, b) hb, clampFamily_apply_face N m K hN τ 0 (i, b) z hb]
  have hB1 : ∀ z : ↥(Cube.boundary (Fin (m + 3))),
      B (z, (1 : unitInterval)) = clampFamily N m K hN τ 1 z := by
    intro z
    obtain ⟨i, b, hb⟩ := exists_faceSet_of_mem_boundary m z.2
    rw [hB (z, (1 : unitInterval)) (i, b) hb, clampFamily_apply_face N m K hN τ 1 (i, b) z hb]
  have hC0 : ∀ z : ↥(Cube.boundary (Fin (m + 3))),
      Cm (z, (0 : unitInterval)) = shrinkFamily N m K hN τ 0 z := by
    intro z
    rw [coneMap_zero m τ z, shrinkFamily_zero]
    exact (clampFamily_one_apply N m K hN τ z).symm
  have hC1 : ∀ z : ↥(Cube.boundary (Fin (m + 3))),
      Cm (z, (1 : unitInterval)) = shrinkFamily N m K hN τ 1 z := by
    intro z
    rw [coneMap_one m τ z, shrinkFamily_one]
    rfl
  -- the three homotopies
  let H1 : ContinuousMap.Homotopy (glue N m K hN τ) (glueCancel N m K hN τ 1) :=
    { toContinuousMap :=
        ⟨fun q : unitInterval × ↥(Cube.boundary (Fin (m + 3))) => A (q.2, q.1),
          A.continuous.comp (continuous_snd.prodMk continuous_fst)⟩
      map_zero_left := fun z => hA0 z
      map_one_left := fun z => hA1 z }
  let H2 : ContinuousMap.Homotopy (clampFamily N m K hN τ 0) (clampFamily N m K hN τ 1) :=
    { toContinuousMap :=
        ⟨fun q : unitInterval × ↥(Cube.boundary (Fin (m + 3))) => B (q.2, q.1),
          B.continuous.comp (continuous_snd.prodMk continuous_fst)⟩
      map_zero_left := fun z => hB0 z
      map_one_left := fun z => hB1 z }
  let H3 : ContinuousMap.Homotopy (shrinkFamily N m K hN τ 0) (shrinkFamily N m K hN τ 1) :=
    { toContinuousMap :=
        ⟨fun q : unitInterval × ↥(Cube.boundary (Fin (m + 3))) => Cm (q.2, q.1),
          Cm.continuous.comp (continuous_snd.prodMk continuous_fst)⟩
      map_zero_left := fun z => hC0 z
      map_one_left := fun z => hC1 z }
  -- concatenation, using that the stages meet pointwise
  let Htot : ContinuousMap.Homotopy (glue N m K hN τ) (shrinkFamily N m K hN τ 1) :=
    (H1.trans (clampFamily_zero N m K hN τ ▸ H2)).trans
      (shrinkFamily_zero N m K hN τ ▸ H3)
  have hHtot0 : ∀ z : ↥(Cube.boundary (Fin (m + 3))),
      Htot ((0 : unitInterval), z) = glue N m K hN τ z := fun z => Htot.map_zero_left z
  have hHtot1 : ∀ z : ↥(Cube.boundary (Fin (m + 3))),
      Htot ((1 : unitInterval), z) = τ (0 : IC (m + 3)) := fun z =>
    (Htot.map_one_left z).trans (by rw [shrinkFamily_one]; rfl)
  exact ⟨⟨fun p => Htot (p.2, p.1),
      Htot.toContinuousMap.continuous.comp (continuous_snd.prodMk continuous_fst)⟩,
    τ (0 : IC (m + 3)), fun p => hHtot0 p, fun p => hHtot1 p⟩

end

end Work.RatHurewicz
