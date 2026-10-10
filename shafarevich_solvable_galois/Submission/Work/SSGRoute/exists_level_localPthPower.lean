import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Submission.NK.GlobalCFTdeep.NormIndex.localNormAt
import Submission.NK.NUV2.LC.RouteB.locUnits_tower_eq_zero
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.adicCompletion_units_mul_pow
import Submission.Work.SSGRoute.exists_level_globalUnit_pthPower
import Submission.Work.SSGRoute.infinitePlace_units_mul_pow

set_option linter.style.haveILetI false

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

/-- **Z3 (a level on which a given local unit becomes a `p`-th power).**  For `b ∈ K_wˣ` there are
a level `L ⊇ K` (Galois over `k`) and `w' ∣ w` with `b` a `p`-th power in `L_{w'}ˣ`.
Route: weak approximation gives `β ∈ Kˣ` with `b/β` in a small principal-unit neighbourhood, which
consists of `p`-th powers (`Work.SSGRoute` `LocalFieldArith/principalUnits_deep_mem_pow`; at
archimedean `w` use `b/|b|`-type approximations, every positive real being a `p`-th power); adjoin a
`p`-th root of `β` and take the Galois closure over `k` (cf. `Work.SSGRoute.exists_level_pthRoot`,
`NK.GlobalCFT` `exists_place_liesOver`). -/
theorem exists_level_localPthPower (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K) (b : (NK.GlobalCFT.Place.localField K w)ˣ) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra k L) (_ : Algebra K L)
      (_ : IsScalarTower k K L) (_ : FiniteDimensional k L) (_ : IsGalois k L)
      (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w)
      (c : (NK.GlobalCFT.Place.localField L w')ˣ),
      NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' b = c ^ p := by
  -- Reduce to writing `b = β · c₀ ^ p` in `K_wˣ` with `β` a *global* unit and then adjoining a
  -- `p`-th root of `β` at a level over `k`.
  have key : ∀ (β : Kˣ) (c₀ : (NK.GlobalCFT.Place.localField K w)ˣ),
      Units.map (algebraMap K (NK.GlobalCFT.Place.localField K w)).toMonoidHom β * c₀ ^ p = b →
      ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra k L) (_ : Algebra K L)
        (_ : IsScalarTower k K L) (_ : FiniteDimensional k L) (_ : IsGalois k L)
        (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w)
        (c : (NK.GlobalCFT.Place.localField L w')ˣ),
        NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' b = c ^ p := by
    intro β c₀ hβ
    -- a level on which the global unit `β` becomes a `p`-th power
    obtain ⟨L, hFL, hNFL, hAkL, hAKL, hSTL, hFDL, hGalL, c, hc⟩ :=
      exists_level_globalUnit_pthPower p k K β
    letI : Algebra k L := hAkL
    letI : Algebra K L := hAKL
    letI : IsScalarTower k K L := hSTL
    letI : FiniteDimensional k L := hFDL
    letI : IsGalois k L := hGalL
    -- a place of `L` above `w`
    obtain ⟨w', hw'⟩ := NK.GlobalCFTdeep.NormIndex.exists_place_liesOver (K := K) (L := L) w
    refine ⟨L, hFL, hNFL, hAkL, hAKL, hSTL, hFDL, hGalL, w', hw',
      Units.map (algebraMap L (NK.GlobalCFT.Place.localField L w')).toMonoidHom c *
        NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' c₀, ?_⟩
    -- the image of `β` in `L_{w'}` is the image of the `p`-th power `c ^ p`
    have hcompat := NK.NUV2.LC.RouteB.localAlgebraMapUnits_algebraMap_units (L := K) (M := L)
      hw' β
    have h1 : NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw'
          (Units.map (algebraMap K (NK.GlobalCFT.Place.localField K w)).toMonoidHom β)
        = (Units.map (algebraMap L (NK.GlobalCFT.Place.localField L w')).toMonoidHom c) ^ p := by
      rw [hcompat, hc, map_pow]
    have hb : NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' b
        = NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw'
            (Units.map (algebraMap K (NK.GlobalCFT.Place.localField K w)).toMonoidHom β)
          * (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' c₀) ^ p := by
      rw [← hβ, map_mul, map_pow]
    rw [hb, h1, mul_pow]
  -- split off the archimedean places
  rcases w with w₀ | Q
  · obtain ⟨β, c₀, hβ⟩ := infinitePlace_units_mul_pow K p w₀ b
    exact key β c₀ hβ
  · obtain ⟨β, c₀, hβ⟩ := adicCompletion_units_mul_pow K Q p b
    exact key β c₀ hβ

end Work.SSGRoute
