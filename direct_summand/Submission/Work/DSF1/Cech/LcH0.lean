import Mathlib
import Submission.Work.DSF1.Cech.CechDefs
import Submission.Work.DSF1.Cech.CoaugCycle
import Submission.Work.DSF1.Cech.basicOpen_localization_facts
import Submission.Work.DSF1.Cech.exists_pow_smul_mem_range_loc
import Submission.Work.DSF1.Cech.eq_zero_of_loc_eq_zero
import Submission.Work.DSF1.Cech.loc_coaug_naturality

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

universe u

namespace Work.DSF1.Cech

variable {R : Type u} [CommRing R] {ι : Type u} [Fintype ι]

/-- `unitTop R` is the inverse of the identification `R ≅ Γ(Spec R, ⊤)`. -/
lemma unitTop_gammaSpecIso (t : Γ(spec R, ⊤)) :
    (unitTop R).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom t) = t := by
  have h1 : ∀ x : Γ(spec R, ⊤),
      ((Spec (CommRingCat.of R)).presheaf.map
        (homOfLE (le_top : (⊤ : (spec R).Opens) ≤ ⊤)).op).hom x = x := by
    intro x
    rw [show (homOfLE (le_top : (⊤ : (spec R).Opens) ≤ ⊤)) = 𝟙 (⊤ : (spec R).Opens)
      from Subsingleton.elim _ _]
    simp
  have h2 : ⇑(unitTop R).hom = ⇑((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) := by
    funext a
    rw [show (unitTop R).hom a = algebraMap R ↑(secRing R (⊤ : (spec R).Opens)) a from rfl]
    rw [← resSection_le_top_GammaSpecIso_inv R (⊤ : (spec R).Opens) a]
    exact h1 _
  rw [h2, ← RingHom.comp_apply, ← CommRingCat.hom_comp, Iso.hom_inv_id]
  rfl

/-- **Surjectivity up to powers for the restriction `Γ(⊤) ⟶ Γ(D (f i))`.**  Every
section of the structure sheaf of `Spec R` over `D (f i)` is, after multiplying by a
power of `f i`, the restriction of a global section. -/
lemma specPresheaf_top_surj (f : ι → R) (i : ι)
    (z : (specPresheaf R).obj (op ((⊤ : (spec R).Opens) ⊓ basicOpens f i))) :
    ∃ (k : ℕ) (t : (specPresheaf R).obj (op (⊤ : (spec R).Opens))),
      ((specPresheaf R).map (homOfLE (inf_le_left :
        (⊤ : (spec R).Opens) ⊓ basicOpens f i ≤ ⊤)).op).hom t = f i ^ k • z := by
  revert z
  rw [show (⊤ : (spec R).Opens) = PrimeSpectrum.basicOpen (1 : R)
    from PrimeSpectrum.basicOpen_one.symm]
  intro z
  exact specPresheaf_basicOpen_surj (1 : R) (f i) z

/-- **`H⁰ (𝒞) = R`.**  Every `0`-cocycle of the Čech complex `𝒞` of the structure sheaf
of `Spec R` along a family `f` of principal opens generating the unit ideal is the
coaugmentation of a global section.  This is deduced from the localized statements `H`
by clearing denominators and the partition of unity. -/
lemma coaug0_surjective_of_localized (f : ι → R) (h : Ideal.span (Set.range f) = ⊤)
    (H : ∀ i : ι, ∀ s : (cechSpecQi f i).X 0, ((cechSpecQi f i).d 0 1).hom s = 0 →
      ∃ q : (Qi (basicOpens f) (specPresheaf R) i).obj (op (⊤ : (spec R).Opens)),
        (coaugQi f i).hom q = s) :
    ∀ s : (cechSpec f).X 0, ((cechSpec f).d 0 1).hom s = 0 →
      ∃ q : R, (coaug0 f).hom q = s := by
  intro s hs
  have key : ∀ i : ι, ∃ (k : ℕ) (b : R), (coaug0 f).hom b = f i ^ k • s := by
    intro i
    -- `(loc f i) s` is a cycle in `𝒞ᵢ`
    have hcyc : ((cechSpecQi f i).d 0 1).hom ((loc f i).f 0 s) = 0 := by
      have hcomm := (loc f i).comm' 0 1 (by simp)
      have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hcomm) s
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
      rw [h, hs, map_zero]
    obtain ⟨q, hq⟩ := H i _ hcyc
    -- clear denominators in `q`
    obtain ⟨k, t, ht⟩ := specPresheaf_top_surj f i q
    have hq' : (coaugQi f i).hom q = ((loc f i).f 0).hom s := hq
    have ht' : (etaITop f i).hom t = f i ^ k • q := ht
    -- naturality of the coaugmentation
    have hnat : ((loc f i).f 0).hom ((coaugQ f).hom t) =
        (coaugQi f i).hom ((etaITop f i).hom t) := by
      have h := congrArg (fun φ => φ.hom t) (loc_coaug_naturality f i)
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
    have hker : ((loc f i).f 0).hom ((f i ^ k • s) - (coaugQ f).hom t) = 0 := by
      rw [map_sub, map_smul, ← hq', ← map_smul, ← ht', hnat, sub_self]
    obtain ⟨l, hl⟩ := eq_zero_of_loc_eq_zero f i 0 _ hker
    have hsplit : f i ^ l • (f i ^ k • s) = f i ^ l • (coaugQ f).hom t := by
      have h2 := hl
      rw [smul_sub] at h2
      exact sub_eq_zero.mp h2
    have hsmul : f i ^ l • (f i ^ k • s) = f i ^ (k + l) • s := by
      rw [smul_smul, ← pow_add, Nat.add_comm]
    have hlin : f i ^ l • (coaugQ f).hom t = (coaugQ f).hom (f i ^ l • t) := by
      rw [map_smul]
    have hmain : f i ^ (k + l) • s = (coaugQ f).hom (f i ^ l • t) := by
      rw [← hsmul, hsplit, hlin]
    refine ⟨k + l, (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (f i ^ l • t), ?_⟩
    rw [hmain]
    have hc : (coaug0 f).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (f i ^ l • t)) =
        (coaugQ f).hom ((unitTop R).hom
          ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (f i ^ l • t))) := by
      rw [← unitTop_comp_coaugQ f]
      rfl
    rw [hc, unitTop_gammaSpecIso]
  have hmem : s ∈ LinearMap.range (coaug0 f).hom :=
    Submodule.mem_of_span_eq_top_of_smul_pow_mem _ (Set.range f) h s (fun r => by
      obtain ⟨i, hi⟩ := Set.mem_range.mp r.2
      obtain ⟨k, b, hb⟩ := key i
      refine ⟨k, b, ?_⟩
      rw [← hi]
      exact hb)
  obtain ⟨q, hq⟩ := hmem
  exact ⟨q, hq⟩

end Work.DSF1.Cech
