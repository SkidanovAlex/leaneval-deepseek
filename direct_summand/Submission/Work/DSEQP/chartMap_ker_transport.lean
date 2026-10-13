import Mathlib
import Submission.Work.DSEQP.gf_defs

/-!
# `Work.DSEQP.chartMap_ker_transport`

Transport of the kernel of the chart comparison map `chartMap` along the localisation
`awayRes (S ⊆ T) : Away 𝒜 (x_S) →+* Away 𝒜 (x_T)`.

For `S ⊆ T` two nonempty finite sets of coordinates, the kernel of the chart comparison at the
chart `D₊(x_T) ⊆ ℙᴺ_A` is the extension of the kernel at the chart `D₊(x_S)`:

`ker (chartMap i T) = (ker (chartMap i S)) · Away 𝒜 (x_T)`.

The mathematical content is the compatibility of the chart comparison maps with restriction
(naturality of Mathlib's `Proj.basicOpenIsoAway` under `Proj.awayMap_awayToSection`), together
with the quasi-coherence of the ideal sheaf `i.ker` of `X ⊆ ℙᴺ_A`
(`Scheme.IdealSheafData.map_ideal`).
-/

namespace Work.DSEQP

open CategoryTheory AlgebraicGeometry

universe a

/-! ## 1. A ring-theoretic translation lemma -/

section RingHelpers

variable {R S : Type*} [CommRing R] [CommRing S]

/-- For a ring equivalence `e : R ≃+* S` and an ideal `J` of `S`, the preimage `e⁻¹(J)` is the
image `e.symm(J)`. -/
lemma comap_ringEquiv_eq_map_symm (e : R ≃+* S) (J : Ideal S) :
    Ideal.comap e.toRingHom J = Ideal.map e.symm.toRingHom J := by
  refine le_antisymm ?_ ?_
  · intro x hx
    have hx' : e x ∈ J := hx
    have h : e.symm (e x) ∈ Ideal.map e.symm.toRingHom J :=
      Ideal.mem_map_of_mem e.symm.toRingHom hx'
    rwa [e.symm_apply_apply x] at h
  · intro x hx
    have h : e x ∈ Ideal.map e.toRingHom (Ideal.map e.symm.toRingHom J) :=
      Ideal.mem_map_of_mem e.toRingHom hx
    rw [Ideal.map_map, show e.toRingHom.comp e.symm.toRingHom = RingHom.id S from by
      ext y; simp, Ideal.map_id] at h
    exact h

end RingHelpers

/-! ## 2. The chart vocabulary of `ℙᴺ_A` in the `x_S` presentation -/

section ChartTransport

variable {A : Type a} [CommRing A] {N : ℕ}

/-- The underlying ring hom of the chart isomorphism `awayIso S` is Mathlib's `awayToSection`. -/
lemma awayIso_toRingHom (S : Finset (Fin (N + 1))) (hS : S.Nonempty) :
    (awayIso (A := A) (N := N) S hS).toRingHom
      = CommRingCat.Hom.hom (Proj.awayToSection (DSMap.PGr A N) (xS (A := A) S)) := by
  rw [awayIso]; rfl

/-- The restriction map of the structure sheaf of `ℙᴺ_A`,
`Γ(D₊(x_S)) →+* Γ(D₊(x_T))` for `S ⊆ T`, expressed through the explicit divisibility
`x_T = x_S · x_{T \ S}`. -/
noncomputable def resST {S T : Finset (Fin (N + 1))} (h : S ⊆ T) :
    Γ(DSMap.PSpace A N, Dcmp (A := A) (N := N) S) →+*
      Γ(DSMap.PSpace A N, Dcmp (A := A) (N := N) T) :=
  CommRingCat.Hom.hom ((DSMap.PSpace A N).presheaf.map
    (homOfLE (Proj.basicOpen_mono (DSMap.PGr A N) (xS (A := A) S) (xS (A := A) T)
      ⟨xS (A := A) (T \ S), xS_mul_diff (A := A) (N := N) h⟩)).op)

/-- **Naturality of the chart isomorphism under restriction.**  The square

`Γ(D₊(x_S)) --res--> Γ(D₊(x_T))`
`     ^                 ^`
`  awayIso S         awayIso T`
`     |                 |`
`Away x_S --awayRes--> Away x_T`

commutes. -/
lemma chartMap_awayRes_comm {S T : Finset (Fin (N + 1))} (h : S ⊆ T)
    (hS : S.Nonempty) (hT : T.Nonempty) :
    (awayIso (A := A) (N := N) T hT).toRingHom.comp (awayRes (A := A) (N := N) h)
      = (resST (A := A) (N := N) h).comp (awayIso (A := A) (N := N) S hS).toRingHom := by
  have hsq := Proj.awayMap_awayToSection (𝒜 := DSMap.PGr A N) (f := xS (A := A) S)
    (g := xS (A := A) (T \ S)) (g_deg := xS_mem_homSub (A := A) (N := N) (T \ S))
    (hx := xS_mul_diff (A := A) (N := N) h)
  have h2 := congrArg CommRingCat.Hom.hom hsq
  rw [CommRingCat.hom_comp, CommRingCat.hom_comp, CommRingCat.hom_ofHom] at h2
  rw [awayIso_toRingHom (A := A) (N := N) T hT, awayIso_toRingHom (A := A) (N := N) S hS]
  unfold awayRes resST
  exact h2

/-- The commutation square of `chartMap_awayRes_comm`, solved for `awayIso T` (i.e. composed on
the left with `(awayIso T).symm`). -/
lemma chartMap_awayRes_comm_symm {S T : Finset (Fin (N + 1))} (h : S ⊆ T)
    (hS : S.Nonempty) (hT : T.Nonempty) :
    (awayIso (A := A) (N := N) T hT).symm.toRingHom.comp (resST (A := A) (N := N) h)
      = (awayRes (A := A) (N := N) h).comp
          (awayIso (A := A) (N := N) S hS).symm.toRingHom := by
  have hsq := chartMap_awayRes_comm (A := A) (N := N) h hS hT
  refine RingHom.ext fun y => ?_
  have h1 := DFunLike.congr_fun hsq ((awayIso (A := A) (N := N) S hS).symm y)
  simp only [RingHom.comp_apply] at h1
  have h2 : (awayIso (A := A) (N := N) S hS).toRingHom
      ((awayIso (A := A) (N := N) S hS).symm y) = y :=
    RingEquiv.apply_symm_apply _ _
  rw [h2] at h1
  change (awayIso (A := A) (N := N) T hT).symm (resST (A := A) (N := N) h y)
      = awayRes (A := A) (N := N) h ((awayIso (A := A) (N := N) S hS).symm y)
  rw [← h1]
  exact RingEquiv.symm_apply_apply _ _

/-- Quasi-coherence of the ideal sheaf `i.ker` of `X ⊆ ℙᴺ_A`: the ideal of `X` in the chart
`D₊(x_T)` is the extension of the ideal of `X` in the chart `D₊(x_S)`, for `S ⊆ T`. -/
lemma ker_ideal_chart_transport {X : AlgebraicGeometry.Scheme.{a}} (i : X ⟶ DSMap.PSpace A N)
    {S T : Finset (Fin (N + 1))} (h : S ⊆ T) (hS : S.Nonempty) (hT : T.Nonempty) :
    Ideal.map (resST (A := A) (N := N) h)
        (i.ker.ideal ⟨Dcmp (A := A) (N := N) S, Dcmp_affine (A := A) (N := N) S hS⟩)
      = i.ker.ideal ⟨Dcmp (A := A) (N := N) T, Dcmp_affine (A := A) (N := N) T hT⟩ := by
  rw [resST]
  exact Scheme.IdealSheafData.map_ideal i.ker
    (U := ⟨Dcmp (A := A) (N := N) T, Dcmp_affine (A := A) (N := N) T hT⟩)
    (V := ⟨Dcmp (A := A) (N := N) S, Dcmp_affine (A := A) (N := N) S hS⟩)
    (Proj.basicOpen_mono (DSMap.PGr A N) (xS (A := A) S) (xS (A := A) T)
      ⟨xS (A := A) (T \ S), xS_mul_diff (A := A) (N := N) h⟩)

end ChartTransport

/-! ## 3. The transport of the kernel -/

theorem chartMap_ker_transport (A : Type a) [CommRing A] {N : ℕ} {X : AlgebraicGeometry.Scheme.{a}}
    (i : X ⟶ DSMap.PSpace A N) (hi : AlgebraicGeometry.IsClosedImmersion i)
    {S T : Finset (Fin (N + 1))} (h : S ⊆ T) (hS : S.Nonempty) (hT : T.Nonempty) :
    RingHom.ker (Work.DSEQP.chartMap i T hT) =
      Ideal.map (Work.DSEQP.awayRes (A := A) (N := N) h)
        (RingHom.ker (Work.DSEQP.chartMap i S hS)) := by
  rw [chartMap_ker i hi T hT, chartMap_ker i hi S hS]
  have hmap := ker_ideal_chart_transport (A := A) (N := N) i h hS hT
  have hsq := chartMap_awayRes_comm_symm (A := A) (N := N) h hS hT
  calc Ideal.comap (awayIso (A := A) (N := N) T hT).toRingHom
        (i.ker.ideal ⟨Dcmp (A := A) (N := N) T, Dcmp_affine (A := A) (N := N) T hT⟩)
      = Ideal.map (awayIso (A := A) (N := N) T hT).symm.toRingHom
          (i.ker.ideal ⟨Dcmp (A := A) (N := N) T, Dcmp_affine (A := A) (N := N) T hT⟩) := by
        rw [comap_ringEquiv_eq_map_symm]
    _ = Ideal.map (awayIso (A := A) (N := N) T hT).symm.toRingHom
          (Ideal.map (resST (A := A) (N := N) h)
            (i.ker.ideal ⟨Dcmp (A := A) (N := N) S, Dcmp_affine (A := A) (N := N) S hS⟩)) := by
        rw [← hmap]
    _ = Ideal.map ((awayIso (A := A) (N := N) T hT).symm.toRingHom.comp (resST (A := A) (N := N) h))
          (i.ker.ideal ⟨Dcmp (A := A) (N := N) S, Dcmp_affine (A := A) (N := N) S hS⟩) := by
        rw [Ideal.map_map]
    _ = Ideal.map ((awayRes (A := A) (N := N) h).comp
            (awayIso (A := A) (N := N) S hS).symm.toRingHom)
          (i.ker.ideal ⟨Dcmp (A := A) (N := N) S, Dcmp_affine (A := A) (N := N) S hS⟩) := by
        rw [hsq]
    _ = Ideal.map (awayRes (A := A) (N := N) h)
          (Ideal.map (awayIso (A := A) (N := N) S hS).symm.toRingHom
            (i.ker.ideal ⟨Dcmp (A := A) (N := N) S, Dcmp_affine (A := A) (N := N) S hS⟩)) := by
        rw [Ideal.map_map]
    _ = Ideal.map (awayRes (A := A) (N := N) h)
          (Ideal.comap (awayIso (A := A) (N := N) S hS).toRingHom
            (i.ker.ideal ⟨Dcmp (A := A) (N := N) S, Dcmp_affine (A := A) (N := N) S hS⟩)) := by
        rw [comap_ringEquiv_eq_map_symm]

end Work.DSEQP
