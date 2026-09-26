import Mathlib
import Submission.Work.Spike.crosscutAtMostTwoDomain_of_compactTwoPoints
import Submission.Work.Spike.nonSeparatingContinuaSeparate
import Submission.Work.SphereJordan.twoPointJaniszewskiCover
import Submission.Work.Spike.annulusCoverPigeonhole
import Submission.Work.Smooth.SphereJordan.janiszewskiChain.SphereDisjoint

namespace Work.SphereJordan

open Set

noncomputable section

/-- **The compact two-point pigeonhole from the sphere cover form.** -/
theorem h2p_of_sphereCover
    (H : ∀ {U V : Set (OnePoint ℂ)}, IsOpen U → IsOpen V → IsPreconnected U → IsPreconnected V →
      ∀ {p q : OnePoint ℂ}, p ≠ q → U ∪ V = ({p, q} : Set (OnePoint ℂ))ᶜ →
      ∀ x y z : OnePoint ℂ, x ∈ U ∩ V → y ∈ U ∩ V → z ∈ U ∩ V →
        connectedComponentIn (U ∩ V) x = connectedComponentIn (U ∩ V) y ∨
        connectedComponentIn (U ∩ V) x = connectedComponentIn (U ∩ V) z ∨
        connectedComponentIn (U ∩ V) y = connectedComponentIn (U ∩ V) z)
    {A B : Set ℂ} (hA : IsCompact A) (hB : IsCompact B)
    (hAc : IsPreconnected Aᶜ) (hBc : IsPreconnected Bᶜ)
    {p q : ℂ} (hpq : p ≠ q) (hint : A ∩ B = {p, q}) :
    ∀ x y z : ℂ, x ∉ A ∪ B → y ∉ A ∪ B → z ∉ A ∪ B →
      connectedComponentIn (A ∪ B)ᶜ x = connectedComponentIn (A ∪ B)ᶜ y ∨
      connectedComponentIn (A ∪ B)ᶜ x = connectedComponentIn (A ∪ B)ᶜ z ∨
      connectedComponentIn (A ∪ B)ᶜ y = connectedComponentIn (A ∪ B)ᶜ z := by
  set K : Set (OnePoint ℂ) := (↑) '' A with hKdef
  set L : Set (OnePoint ℂ) := (↑) '' B with hLdef
  have hKcl : IsClosed K := OnePoint.isClosed_image_coe.mpr ⟨hA.isClosed, hA⟩
  have hLcl : IsClosed L := OnePoint.isClosed_image_coe.mpr ⟨hB.isClosed, hB⟩
  have hKpre : IsPreconnected Kᶜ := Work.Spike.isPreconnected_compl_image_coe hA hAc
  have hLpre : IsPreconnected Lᶜ := Work.Spike.isPreconnected_compl_image_coe hB hBc
  have hKL : K ∩ L = ({(↑p : OnePoint ℂ), (↑q : OnePoint ℂ)} : Set (OnePoint ℂ)) := by
    rw [hKdef, hLdef, ← Set.image_inter OnePoint.coe_injective, hint]
    ext w
    simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨s, (hsp | hsq), hws⟩
      · left; rw [← hsp, hws]
      · right; rw [← hsq, hws]
    · rintro (h | h)
      · exact ⟨p, Or.inl rfl, h.symm⟩
      · exact ⟨q, Or.inr rfl, h.symm⟩
  have hpq' : (↑p : OnePoint ℂ) ≠ (↑q : OnePoint ℂ) := fun h => hpq (OnePoint.coe_injective h)
  have hUnion : K ∪ L = (↑) '' (A ∪ B) := by rw [hKdef, hLdef, Set.image_union]
  have hKLc : Kᶜ ∩ Lᶜ = (K ∪ L)ᶜ := (Set.compl_union K L).symm
  -- the component conversion between the plane and the sphere
  have hcomp : ∀ u v : ℂ, (↑u : OnePoint ℂ) ∈
      connectedComponentIn ((OnePoint.some '' (A ∪ B))ᶜ) (↑v) ↔
      u ∈ connectedComponentIn ((A ∪ B)ᶜ : Set ℂ) v := fun u v =>
    Set.ext_iff.mp (Work.Smooth.SphereJordan.Chain.connectedComponentIn_compl_coe
      (hA.union hB) v) u
  intro x y z hx hy hz
  have hxK : (↑x : OnePoint ℂ) ∈ Kᶜ ∩ Lᶜ := by
    refine ⟨?_, ?_⟩
    · rintro ⟨w, hw, hwx⟩
      exact hx (Or.inl (OnePoint.coe_injective hwx ▸ hw))
    · rintro ⟨w, hw, hwx⟩
      exact hx (Or.inr (OnePoint.coe_injective hwx ▸ hw))
  have hyK : (↑y : OnePoint ℂ) ∈ Kᶜ ∩ Lᶜ := by
    refine ⟨?_, ?_⟩
    · rintro ⟨w, hw, hwy⟩
      exact hy (Or.inl (OnePoint.coe_injective hwy ▸ hw))
    · rintro ⟨w, hw, hwy⟩
      exact hy (Or.inr (OnePoint.coe_injective hwy ▸ hw))
  have hzK : (↑z : OnePoint ℂ) ∈ Kᶜ ∩ Lᶜ := by
    refine ⟨?_, ?_⟩
    · rintro ⟨w, hw, hwz⟩
      exact hz (Or.inl (OnePoint.coe_injective hwz ▸ hw))
    · rintro ⟨w, hw, hwz⟩
      exact hz (Or.inr (OnePoint.coe_injective hwz ▸ hw))
  have key := H (U := Kᶜ) (V := Lᶜ) hKcl.isOpen_compl hLcl.isOpen_compl hKpre hLpre hpq'
    (by rw [← Set.compl_inter, hKL]) (↑x) (↑y) (↑z) hxK hyK hzK
  rw [hKLc] at key
  have key' : connectedComponentIn ((OnePoint.some '' (A ∪ B))ᶜ) (↑x) =
        connectedComponentIn ((OnePoint.some '' (A ∪ B))ᶜ) (↑y) ∨
      connectedComponentIn ((OnePoint.some '' (A ∪ B))ᶜ) (↑x) =
        connectedComponentIn ((OnePoint.some '' (A ∪ B))ᶜ) (↑z) ∨
      connectedComponentIn ((OnePoint.some '' (A ∪ B))ᶜ) (↑y) =
        connectedComponentIn ((OnePoint.some '' (A ∪ B))ᶜ) (↑z) := by
    simpa only [hUnion] using key
  rcases key' with h | h | h
  · left
    apply Set.ext
    intro w
    rw [(hcomp w x).symm, (hcomp w y).symm, h]
  · right; left
    apply Set.ext
    intro w
    rw [(hcomp w x).symm, (hcomp w z).symm, h]
  · right; right
    apply Set.ext
    intro w
    rw [(hcomp w y).symm, (hcomp w z).symm, h]

/-- **The two-point Janiszewski theorem in sphere-cover form**, obtained from the plane annulus
pigeonhole `Work.Spike.annulusCoverPigeonhole` (which is proved independently, without the
Mayer--Vietoris cyclic-kernel input) via the Möbius reduction `twoPointJaniszewskiCover_of_plane`. -/
theorem twoPointJaniszewskiCoverClean {U V : Set (OnePoint ℂ)} (hUo : IsOpen U) (hVo : IsOpen V)
    (hUp : IsPreconnected U) (hVp : IsPreconnected V) {p q : OnePoint ℂ} (hpq : p ≠ q)
    (hUV : U ∪ V = ({p, q} : Set (OnePoint ℂ))ᶜ) :
    ∀ x y z : OnePoint ℂ, x ∈ U ∩ V → y ∈ U ∩ V → z ∈ U ∩ V →
      connectedComponentIn (U ∩ V) x = connectedComponentIn (U ∩ V) y ∨
      connectedComponentIn (U ∩ V) x = connectedComponentIn (U ∩ V) z ∨
      connectedComponentIn (U ∩ V) y = connectedComponentIn (U ∩ V) z :=
  Work.SphereJordan.twoPointJaniszewskiCover_of_plane
    (fun hUo' hVo' hUp' hVp' hcov' =>
      Work.Spike.annulusCoverPigeonhole hUo' hVo' hUp' hVp' hcov')
    hUo hVo hUp hVp hpq hUV

/-- **The two-point Janiszewski pigeonhole** in the compact plane form consumed by
`Work.Spike.crosscutAtMostTwoDomain_of_compactTwoPoints`. -/
theorem twoPointPigeonhole {A B : Set ℂ} (hA : IsCompact A) (hB : IsCompact B)
    (hAc : IsPreconnected Aᶜ) (hBc : IsPreconnected Bᶜ)
    {p q : ℂ} (hpq : p ≠ q) (hint : A ∩ B = {p, q}) :
    ∀ x y z : ℂ, x ∉ A ∪ B → y ∉ A ∪ B → z ∉ A ∪ B →
      connectedComponentIn (A ∪ B)ᶜ x = connectedComponentIn (A ∪ B)ᶜ y ∨
      connectedComponentIn (A ∪ B)ᶜ x = connectedComponentIn (A ∪ B)ᶜ z ∨
      connectedComponentIn (A ∪ B)ᶜ y = connectedComponentIn (A ∪ B)ᶜ z :=
  h2p_of_sphereCover twoPointJaniszewskiCoverClean hA hB hAc hBc hpq hint

/-- **The crosscut theorem for a plane domain**: an arc whose endpoints lie outside an open
preconnected set `D` and whose interior lies in `D` cuts `D` into at most two components. -/
theorem crosscutAtMostTwoDomain {D : Set ℂ} (hDopen : IsOpen D) (hDconn : IsPreconnected D)
    {β : C(Set.Icc (0 : ℝ) 1, ℂ)} (hβ : Function.Injective β)
    (h₀ : β ⟨0, by norm_num⟩ ∉ D) (h₁ : β ⟨1, by norm_num⟩ ∉ D)
    (hint : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → β t ∈ D) :
    ∀ x y z : ℂ, x ∈ D \ Set.range β → y ∈ D \ Set.range β → z ∈ D \ Set.range β →
      connectedComponentIn (D \ Set.range β) x = connectedComponentIn (D \ Set.range β) y ∨
      connectedComponentIn (D \ Set.range β) x = connectedComponentIn (D \ Set.range β) z ∨
      connectedComponentIn (D \ Set.range β) y = connectedComponentIn (D \ Set.range β) z :=
  Work.Spike.crosscutAtMostTwoDomain_of_compactTwoPoints
    (fun hA hB hAc hBc => twoPointPigeonhole hA hB hAc hBc)
    hDopen hDconn hβ h₀ h₁ hint

end

end Work.SphereJordan
