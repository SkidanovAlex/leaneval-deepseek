import Mathlib
import Submission.Work.MotC2.CoordPreserved
import Submission.Work.MotC2.Places
import Submission.Work.MotC2.IsRatPlaceMap

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The affine coordinate ring is preserved by an isomorphism of function fields
fixing the place at infinity

`Work.MotC2.CoordPreserved` proves that an `L`-algebra *automorphism* `Θ` of the function field
`L(E)` of a single elliptic curve which maps the local ring `infPlace E` of the point at infinity
onto itself maps the affine coordinate ring `affRing E = L[x,y]` onto itself.  The key input is
the identification `affRing E = placeInter E`, the intersection of all places of `L(E)/L` other
than `O` (and other than the whole field), proved there via integral closedness of `L[x,y]`.

Here we record the *cross-curve* version, needed downstream to compare the function fields of two
different elliptic curves: for an `L`-algebra isomorphism `Θ : L(E) ≃ₐ[L] L(E')` with
`Θ (infPlace E) = infPlace E'`, the affine coordinate rings correspond.

The proof transplants the argument of `Work.MotC2.CoordPreserved` along `Θ`: a valuation subring
`V` of `L(E')` pulls back to the valuation subring `pullVal Θ V` of `L(E)`, the pullback of the
place at infinity is the place at infinity (`placeAtO` is characterised by its underlying ring,
namely `infPlace`), and hence `Θ` maps the intersection of all the other places into the
intersection of all the other places.  Applying the same to `Θ.symm` gives the reverse inclusion.
-/

namespace Work.MotK.TwRuling

open Work.MotC2

variable {L : Type*} [Field L]

/-- The pullback of a valuation subring along an `L`-algebra isomorphism of function fields:
`{x : L(E) | Θ x ∈ V}`.

This is the cross-curve analogue of `Work.MotC2.preimVal` (which handles automorphisms of a
single function field). -/
noncomputable def pullVal (E E' : WeierstrassCurve L)
    (Θ : Func E ≃ₐ[L] Func E') (V : ValuationSubring (Func E')) :
    ValuationSubring (Func E) :=
  ValuationSubring.ofSubring (V.toSubring.comap Θ.toRingHom) (fun x => by
    rcases V.mem_or_inv_mem (Θ x) with h | h
    · exact Or.inl (Subring.mem_comap.mpr h)
    · refine Or.inr (Subring.mem_comap.mpr ?_)
      rw [show Θ.toRingHom x⁻¹ = (Θ.toRingHom x)⁻¹ from map_inv₀ Θ.toRingHom x]
      exact h)

/-- An `L`-algebra isomorphism of function fields which maps the place at infinity of `E` onto the
place at infinity of `E'` maps the intersection of all the other places of `E` into the
intersection of all the other places of `E'`.

This is the cross-curve version of `Work.MotC2.mem_placeInter_map`. -/
theorem mem_placeInter_map' (E E' : WeierstrassCurve L)
    [E.IsElliptic] [E'.IsElliptic]
    (Θ : Func E ≃ₐ[L] Func E')
    (hO : Subalgebra.map Θ.toAlgHom (infPlace E) = infPlace E')
    {f : Func E} (hf : f ∈ placeInter E) : Θ f ∈ placeInter E' := by
  rw [placeInter, Algebra.mem_iInf] at hf ⊢
  intro W
  obtain ⟨V, hL, hVtop, hVO, hWeq⟩ := W.2
  rw [hWeq]
  have hL' : ∀ c : L, algebraMap L (Func E) c ∈ pullVal E E' Θ V := fun c => by
    rw [pullVal, ValuationSubring.mem_ofSubring, Subring.mem_comap]
    simpa using hL c
  have hPtop : pullVal E E' Θ V ≠ ⊤ := by
    intro htop
    apply hVtop
    apply ValuationSubring.ext
    intro y
    refine ⟨fun _ => ValuationSubring.mem_top y, fun _ => ?_⟩
    have h1 : Θ.symm y ∈ pullVal E E' Θ V := by rw [htop]; exact ValuationSubring.mem_top _
    rw [pullVal, ValuationSubring.mem_ofSubring, Subring.mem_comap] at h1
    simpa using h1
  have hPO : pullVal E E' Θ V ≠ placeAtO E := by
    intro hPeq
    apply hVO
    apply ValuationSubring.ext
    intro y
    constructor
    · intro hy
      have h1 : Θ.symm y ∈ pullVal E E' Θ V := by
        rw [pullVal, ValuationSubring.mem_ofSubring, Subring.mem_comap]
        simpa using hy
      rw [hPeq, placeAtO, ValuationSubring.mem_ofSubring] at h1
      have h2 : Θ.symm y ∈ infPlace E := Subalgebra.mem_toSubring.mp h1
      have h3 : y ∈ Subalgebra.map Θ.toAlgHom (infPlace E) :=
        Subalgebra.mem_map.mpr ⟨Θ.symm y, h2, by simp⟩
      rwa [hO] at h3
    · intro hy
      have hy' : y ∈ Subalgebra.map Θ.toAlgHom (infPlace E) := by rw [hO]; exact hy
      obtain ⟨z, hz, hzy⟩ := Subalgebra.mem_map.mp hy'
      have h1 : z ∈ pullVal E E' Θ V := by
        rw [hPeq, placeAtO, ValuationSubring.mem_ofSubring]
        exact Subalgebra.mem_toSubring.mpr hz
      rw [pullVal, ValuationSubring.mem_ofSubring, Subring.mem_comap] at h1
      rw [← hzy]
      simpa using h1
  have hgood : valSub E (pullVal E E' Θ V) hL' ∈ placeFamily E :=
    ⟨pullVal E E' Θ V, hL', hPtop, hPO, rfl⟩
  have hmem : f ∈ valSub E (pullVal E E' Θ V) hL' := hf ⟨_, hgood⟩
  change Θ f ∈ V.toSubring
  have h : f ∈ (pullVal E E' Θ V).toSubring := hmem
  rw [pullVal, ValuationSubring.ofSubring_toSubring, Subring.mem_comap] at h
  simpa using h

/-- The intersection of all the places other than the point at infinity is transported by an
`L`-algebra isomorphism of function fields which maps the place at infinity to the place at
infinity. -/
theorem map_placeInter_eq (E E' : WeierstrassCurve L) [E.IsElliptic] [E'.IsElliptic]
    (Θ : Func E ≃ₐ[L] Func E')
    (hO : Subalgebra.map Θ.toAlgHom (infPlace E) = infPlace E') :
    Subalgebra.map Θ.toAlgHom (placeInter E) = placeInter E' := by
  have hOsymm : Subalgebra.map Θ.symm.toAlgHom (infPlace E') = infPlace E := by
    apply le_antisymm
    · intro x hx
      obtain ⟨y, hy, hyx⟩ := Subalgebra.mem_map.mp hx
      have hy' : y ∈ Subalgebra.map Θ.toAlgHom (infPlace E) := by rw [hO]; exact hy
      obtain ⟨z, hz, hzy⟩ := Subalgebra.mem_map.mp hy'
      rw [← hzy] at hyx
      have hxz : x = z := by rw [← hyx]; simp
      rw [hxz]
      exact hz
    · intro x hx
      have hx' : Θ x ∈ Subalgebra.map Θ.toAlgHom (infPlace E) :=
        Subalgebra.mem_map.mpr ⟨x, hx, rfl⟩
      rw [hO] at hx'
      exact Subalgebra.mem_map.mpr ⟨Θ x, hx', by simp⟩
  have hmap : Subalgebra.map Θ.toAlgHom (placeInter E) ≤ placeInter E' := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subalgebra.mem_map.mp hx
    exact mem_placeInter_map' E E' Θ hO hy
  have hmap' : Subalgebra.map Θ.symm.toAlgHom (placeInter E') ≤ placeInter E := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subalgebra.mem_map.mp hx
    exact mem_placeInter_map' E' E Θ.symm hOsymm hy
  refine le_antisymm hmap ?_
  intro f hf
  have h1 : Θ.symm f ∈ placeInter E :=
    hmap' (Subalgebra.mem_map.mpr ⟨f, hf, rfl⟩)
  exact Subalgebra.mem_map.mpr ⟨Θ.symm f, h1, by simp⟩

theorem affRing_map_eq (L : Type*) [Field L] (E E' : WeierstrassCurve L) [E.IsElliptic] [E'.IsElliptic]
    (Θ : Work.MotC2.Func E ≃ₐ[L] Work.MotC2.Func E')
    (hO : Subalgebra.map Θ.toAlgHom (Work.MotC2.infPlace E) = Work.MotC2.infPlace E') :
    Subalgebra.map Θ.toAlgHom (Work.MotC2.affRing E) = Work.MotC2.affRing E' := by
  have hPE : placeInter E = affRing E :=
    le_antisymm (placeInter_le_affRing E) (affRing_le_placeInter E)
  have hPE' : placeInter E' = affRing E' :=
    le_antisymm (placeInter_le_affRing E') (affRing_le_placeInter E')
  rw [← hPE, ← hPE']
  exact map_placeInter_eq E E' Θ hO

end Work.MotK.TwRuling
