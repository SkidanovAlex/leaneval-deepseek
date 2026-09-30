import Mathlib
import Submission.Work.BW.BWGradedBase

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Length additivity for the colon of an ideal by a principal ideal: the short exact
sequence `0 → S/(I : y) --·y--> S/I → S/(I + (y)) → 0` gives
`length(S/I) = length(S/(I:y)) + length(S/(I+(y)))`. -/
theorem length_quotient_colon_span_add {S : Type*} [CommRing S] (I : Ideal S) (y : S) :
    Module.length S (S ⧸ I) =
      Module.length S (S ⧸ Submodule.colon I ↑(Ideal.span {y}))
      + Module.length S (S ⧸ (I ⊔ Ideal.span {y})) := by
  have hcomap : Submodule.comap (LinearMap.mulRight S y) (I : Submodule S S)
      = Submodule.colon I ↑(Ideal.span {y}) := by
    ext r
    rw [Submodule.mem_comap, LinearMap.mulRight_apply, Ideal.mem_colon_span_singleton]
  have hf : Function.Injective
      (Submodule.mapQ (Submodule.colon I ↑(Ideal.span {y})) I (LinearMap.mulRight S y)
        (le_of_eq hcomap.symm)) := by
    rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ, hcomap, Submodule.mkQ_map_self]
  have hg : Function.Surjective
      (Submodule.factor (le_sup_left : I ≤ I ⊔ Ideal.span {y})) := by
    intro z
    obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective (I ⊔ Ideal.span {y}) z
    exact ⟨Submodule.mkQ I w,
      Submodule.factor_mk (le_sup_left : I ≤ I ⊔ Ideal.span {y}) w⟩
  have hmr : (LinearMap.mulRight S y).range = Ideal.span {y} := by
    ext z
    rw [LinearMap.mem_range, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a, by rw [← ha, LinearMap.mulRight_apply]⟩
    · rintro ⟨a, ha⟩
      exact ⟨a, by rw [LinearMap.mulRight_apply, ha]⟩
  have hex : Function.Exact
      (Submodule.mapQ (Submodule.colon I ↑(Ideal.span {y})) I (LinearMap.mulRight S y)
        (le_of_eq hcomap.symm))
      (Submodule.factor (le_sup_left : I ≤ I ⊔ Ideal.span {y})) := by
    rw [LinearMap.exact_iff, Submodule.ker_mapQ, Submodule.comap_id, Submodule.range_mapQ, hmr,
      Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq]
  exact Module.length_eq_add_of_exact
    (Submodule.mapQ (Submodule.colon I ↑(Ideal.span {y})) I (LinearMap.mulRight S y)
      (le_of_eq hcomap.symm))
    (Submodule.factor (le_sup_left : I ≤ I ⊔ Ideal.span {y})) hf hg hex

/-- Localization commutes with the colon of an ideal by a principal ideal. -/
theorem map_colon_span_singleton_of_isLocalization {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (M : Submonoid R) [IsLocalization M S] (I : Ideal R) (x : R) :
    (Submodule.colon I ↑(Ideal.span {x})).map (algebraMap R S) =
      Submodule.colon (I.map (algebraMap R S)) ↑(Ideal.span {(algebraMap R S) x}) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_colon_span_singleton] at hr
    rw [Ideal.mem_comap, Ideal.mem_colon_span_singleton]
    rw [← map_mul]
    exact Ideal.mem_map_of_mem (algebraMap R S) hr
  · intro s hs
    rw [Ideal.mem_colon_span_singleton] at hs
    obtain ⟨⟨a, b⟩, hb⟩ := IsLocalization.surj M s
    have h1 : algebraMap R S a * algebraMap R S x ∈ I.map (algebraMap R S) := by
      rw [← hb, mul_assoc, mul_comm (algebraMap R S ↑b) (algebraMap R S x), ← mul_assoc]
      exact Ideal.mul_mem_right (algebraMap R S ↑b) (I.map (algebraMap R S)) hs
    have hmem : algebraMap R S (a * x) ∈ I.map (algebraMap R S) := by
      rw [map_mul]
      exact h1
    obtain ⟨m, hm, hmi⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff M S I (a * x)).mp hmem
    have hkey : IsLocalization.mk' S (m * a) ⟨m * b, M.mul_mem hm b.2⟩ ∈
        (Submodule.colon I ↑(Ideal.span {x})).map (algebraMap R S) := by
      rw [IsLocalization.mk'_mem_map_algebraMap_iff]
      exact ⟨1, M.one_mem, by
        rw [one_mul, Ideal.mem_colon_span_singleton, mul_assoc]; exact hmi⟩
    have heq : s = IsLocalization.mk' S (m * a) ⟨m * b, M.mul_mem hm b.2⟩ := by
      rw [IsLocalization.eq_mk'_iff_mul_eq]
      simp only [map_mul]
      rw [← hb]
      ring
    rw [heq]
    exact hkey

theorem colon_localize_length_add {R : Type*} [CommRing R] (q : Ideal R) (hq : q.IsPrime)
    (J : Ideal R) (x : R) :
    locLenAt q hq J = locLenAt q hq (Submodule.colon J ↑(Ideal.span {x}))
      + locLenAt q hq (J ⊔ Ideal.span {x}) := by
  letI := hq
  have hmap_colon := map_colon_span_singleton_of_isLocalization (R := R)
    (S := Localization.AtPrime q) q.primeCompl (I := J) (x := x)
  have hmap_sup : (J ⊔ Ideal.span {x}).map (algebraMap R (Localization.AtPrime q)) =
      J.map (algebraMap R (Localization.AtPrime q))
        ⊔ Ideal.span {(algebraMap R (Localization.AtPrime q)) x} := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  have hmain := length_quotient_colon_span_add
    (J.map (algebraMap R (Localization.AtPrime q)))
    ((algebraMap R (Localization.AtPrime q)) x)
  rw [← hmap_colon, ← hmap_sup] at hmain
  exact hmain

end Work.BW
