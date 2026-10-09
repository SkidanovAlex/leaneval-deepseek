import Mathlib
import Submission.Work.SSGRoute.EulerSymm.BaseAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Group-theoretic setup of the prime-to-`p` Hochschild–Serre degeneracy

For `G = DC k Ω K A C = decomp k A ⊓ res⁻¹ C` and `N = UD k Ω K A = decomp k A ⊓ Gal(Ω/K)`,
we have `N = ker(res|_G)`, so `N ◁ G` and `G/N ≅ D := res(G) ≤ C`, a finite group of order
prime to `p`.  This file collects

* `Dsub` (the image `res(G) ≤ Gal(K/k)`), `Dsub_le_C`, `Dsub_card_coprime`;
* the section `sectD : ↥Dsub → G` of the restriction, with `sectG` its "coset representative of
  `g`" version, and the elementary membership lemmas used by the two halves of the degeneracy.

Nothing here uses the locally constant cochain model.
-/

open Classical

namespace Work.SSGRoute.EulerSymm

noncomputable section

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]

/-- `D = res(D_C) ≤ Gal(K/k)`. -/
def Dsub (A : ValuationSubring Ω) (C : Subgroup (K ≃ₐ[k] K)) : Subgroup (K ≃ₐ[k] K) :=
  Subgroup.map (SSGRoute.res k K) (DC k Ω K A C)

lemma mem_Dsub {A : ValuationSubring Ω} {C : Subgroup (K ≃ₐ[k] K)} {x : K ≃ₐ[k] K} :
    x ∈ Dsub k Ω K A C ↔ ∃ g ∈ DC k Ω K A C, SSGRoute.res k K g = x := Iff.rfl

lemma Dsub_le_C (A : ValuationSubring Ω) (C : Subgroup (K ≃ₐ[k] K)) :
    Dsub k Ω K A C ≤ C := by
  intro x hx
  rw [mem_Dsub] at hx
  obtain ⟨g, hg, rfl⟩ := hx
  rw [DC, Subgroup.mem_inf, Subgroup.mem_comap] at hg
  exact hg.2

instance (A : ValuationSubring Ω) (C : Subgroup (K ≃ₐ[k] K)) :
    Fintype ↥(Dsub k Ω K A C) := inferInstance

/-- `|res(D_C)|` divides `|C|`, hence is prime to `p`. -/
lemma Dsub_card_coprime (A : ValuationSubring Ω) (C : Subgroup (K ≃ₐ[k] K))
    (hC : (Nat.card ↥C).Coprime p) :
    Nat.Coprime (Nat.card ↥(Dsub k Ω K A C)) p :=
  Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le (Dsub_le_C k Ω K A C)) hC

/-! ## The section of the restriction `G → D` -/

/-- A (non-canonical) section `D → G` of `res`, normalised by `sectD 1 = 1`. -/
def sectD (A : ValuationSubring Ω) (C : Subgroup (K ≃ₐ[k] K)) :
    ↥(Dsub k Ω K A C) → Ω ≃ₐ[k] Ω :=
  fun d => if h : d = 1 then 1 else Classical.choose (Subgroup.mem_map.mp d.2)

lemma res_sectD (A : ValuationSubring Ω) (C : Subgroup (K ≃ₐ[k] K))
    (d : ↥(Dsub k Ω K A C)) :
    SSGRoute.res k K (sectD k Ω K A C d) = (d : K ≃ₐ[k] K) := by
  unfold sectD
  by_cases h : d = 1
  · rw [dif_pos h, h]; exact map_one _
  · rw [dif_neg h]
    exact (Classical.choose_spec (Subgroup.mem_map.mp d.2)).2

lemma sectD_mem (A : ValuationSubring Ω) (C : Subgroup (K ≃ₐ[k] K))
    (d : ↥(Dsub k Ω K A C)) :
    sectD k Ω K A C d ∈ DC k Ω K A C := by
  unfold sectD
  by_cases h : d = 1
  · rw [dif_pos h]; exact (DC k Ω K A C).one_mem
  · rw [dif_neg h]
    exact (Classical.choose_spec (Subgroup.mem_map.mp d.2)).1

@[simp] lemma sectD_one (A : ValuationSubring Ω) (C : Subgroup (K ≃ₐ[k] K)) :
    sectD k Ω K A C 1 = 1 := by
  unfold sectD; rw [dif_pos rfl]

/-- The coset representative of `g ∈ D_C`, i.e. `sectD` applied to `res g`. -/
def sectG (A : ValuationSubring Ω) (C : Subgroup (K ≃ₐ[k] K)) (g : Ω ≃ₐ[k] Ω)
    (hg : g ∈ DC k Ω K A C) : Ω ≃ₐ[k] Ω :=
  sectD k Ω K A C ⟨SSGRoute.res k K g, Subgroup.mem_map.mpr ⟨g, hg, rfl⟩⟩

lemma res_sectG (A : ValuationSubring Ω) (C : Subgroup (K ≃ₐ[k] K)) (g : Ω ≃ₐ[k] Ω)
    (hg : g ∈ DC k Ω K A C) :
    SSGRoute.res k K (sectG k Ω K A C g hg) = SSGRoute.res k K g :=
  res_sectD k Ω K A C _

lemma sectG_mem (A : ValuationSubring Ω) (C : Subgroup (K ≃ₐ[k] K)) (g : Ω ≃ₐ[k] Ω)
    (hg : g ∈ DC k Ω K A C) :
    sectG k Ω K A C g hg ∈ DC k Ω K A C :=
  sectD_mem k Ω K A C _

/-- `sectG` depends only on `res g`. -/
lemma sectG_eq_of_res_eq (A : ValuationSubring Ω) (C : Subgroup (K ≃ₐ[k] K))
    {g g' : Ω ≃ₐ[k] Ω} (hg : g ∈ DC k Ω K A C) (hg' : g' ∈ DC k Ω K A C)
    (h : SSGRoute.res k K g = SSGRoute.res k K g') :
    sectG k Ω K A C g hg = sectG k Ω K A C g' hg' := by
  unfold sectG
  congr 1
  exact Subtype.ext h

lemma sectG_conj_mem (A : ValuationSubring Ω) (C : Subgroup (K ≃ₐ[k] K)) (g : Ω ≃ₐ[k] Ω)
    (hg : g ∈ DC k Ω K A C) {n : Ω ≃ₐ[k] Ω} (hn : n ∈ UD k Ω K A) :
    sectG k Ω K A C g hg * n * (sectG k Ω K A C g hg)⁻¹ ∈ UD k Ω K A :=
  UD_conj_mem k Ω K A C (sectG_mem k Ω K A C g hg) hn

/-! ## Membership calculus on `N = UD = ker(res|_G)` -/

lemma mem_UD_of_mem_DC (A : ValuationSubring Ω) (C : Subgroup (K ≃ₐ[k] K))
    {g : Ω ≃ₐ[k] Ω} (hg : g ∈ DC k Ω K A C) :
    g ∈ UD k Ω K A ↔ SSGRoute.res k K g = 1 := by
  rw [mem_UD_iff]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  rw [DC, Subgroup.mem_inf] at hg
  exact hg.1

/-- `g · (sectG g)⁻¹ ∈ N`. -/
lemma mul_sectG_inv_mem (A : ValuationSubring Ω) (C : Subgroup (K ≃ₐ[k] K)) (g : Ω ≃ₐ[k] Ω)
    (hg : g ∈ DC k Ω K A C) :
    g * (sectG k Ω K A C g hg)⁻¹ ∈ UD k Ω K A := by
  rw [mem_UD_of_mem_DC k Ω K A C
    ((DC k Ω K A C).mul_mem hg ((DC k Ω K A C).inv_mem (sectG_mem k Ω K A C g hg)))]
  rw [map_mul, map_inv, res_sectG k Ω K A C g hg, mul_inv_cancel]

/-- The factor set `sectG g · sectG h · (sectG (g h))⁻¹` lies in `N`. -/
lemma factor_set_mem (A : ValuationSubring Ω) (C : Subgroup (K ≃ₐ[k] K))
    {g h : Ω ≃ₐ[k] Ω} (hg : g ∈ DC k Ω K A C) (hh : h ∈ DC k Ω K A C) :
    sectG k Ω K A C g hg * sectG k Ω K A C h hh *
        (sectG k Ω K A C (g * h) ((DC k Ω K A C).mul_mem hg hh))⁻¹ ∈ UD k Ω K A := by
  have hmem : sectG k Ω K A C g hg * sectG k Ω K A C h hh *
        (sectG k Ω K A C (g * h) ((DC k Ω K A C).mul_mem hg hh))⁻¹ ∈ DC k Ω K A C :=
    (DC k Ω K A C).mul_mem ((DC k Ω K A C).mul_mem (sectG_mem k Ω K A C g hg)
      (sectG_mem k Ω K A C h hh))
      ((DC k Ω K A C).inv_mem (sectG_mem k Ω K A C (g * h) _))
  rw [mem_UD_of_mem_DC k Ω K A C hmem]
  rw [map_mul, map_mul, map_inv, res_sectG k Ω K A C g hg, res_sectG k Ω K A C h hh,
    res_sectG k Ω K A C (g * h) _, map_mul]
  group

end

end Work.SSGRoute.EulerSymm
