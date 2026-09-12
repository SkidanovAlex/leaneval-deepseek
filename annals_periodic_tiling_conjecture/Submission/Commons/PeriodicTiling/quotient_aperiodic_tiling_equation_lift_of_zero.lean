import Mathlib
import Submission.Commons.PeriodicTiling.isContinuousTiling_of_isTiling_lift
import Submission.Commons.PeriodicTiling.periodicTilingSet_lattice_period
import Submission.Commons.PeriodicTiling.IsAperiodicTilingEquation_map_addEquiv
import Submission.Commons.PeriodicTiling.quotient_tiling_lift_tile0

open scoped Pointwise

namespace Commons.PeriodicTiling

private lemma periodic_of_zsmul_image_injective
    {G : Type*} [AddCommGroup G] [IsAddTorsionFree G]
    {N : ℤ} (hN : N ≠ 0) {S : Set G}
    (hper : IsPeriodicTilingSet (Set.image (fun x : G => N • x) S)) :
    IsPeriodicTilingSet S := by
  classical
  let μ : G →+ G := AddMonoidHom.mk' (fun x => N • x) (by
    intro x y
    exact zsmul_add x y N)
  have hμinj : Function.Injective μ := by
    simpa [μ] using (zsmul_right_injective (G := G) hN)
  rcases hper with ⟨H, hHfin, s, hs⟩
  have hsμ : μ '' S = (s : Set G) + H := by
    simpa [μ] using hs
  let K : AddSubgroup G := H.comap μ
  have hHleK : H ≤ K := by
    intro x hx
    rw [AddSubgroup.mem_comap]
    exact H.zsmul_mem hx N
  have hKfin : K.FiniteIndex := AddSubgroup.finiteIndex_of_le (H := H) (K := K) hHleK
  have hpre : μ ⁻¹' ((s : Set G) + H) = S := by
    calc
      μ ⁻¹' ((s : Set G) + H) = μ ⁻¹' (μ '' S) := by rw [hsμ]
      _ = S := Function.Injective.preimage_image hμinj S
  let hasRep (t : G) : Prop := ∃ y : G, μ y ∈ (({t} : Finset G) : Set G) + H
  let rep (t : G) : G := if h : hasRep t then Classical.choose h else 0
  let s' : Finset G := (s.filter (fun t => hasRep t)).image rep
  have hpre' : μ ⁻¹' ((s : Set G) + H) = (s' : Set G) + K := by
    ext x
    constructor
    · intro hx
      rw [Set.mem_preimage] at hx
      rw [Set.mem_add] at hx
      rcases hx with ⟨a, ha, b, hb, hsum⟩
      have htrep : hasRep a := by
        refine ⟨x, ?_⟩
        rw [Set.mem_add]
        exact ⟨a, by simp, b, by simpa using hb, hsum⟩
      have ht_in_filter : a ∈ s.filter (fun t => hasRep t) := by
        exact Finset.mem_filter.mpr ⟨by simpa using ha, htrep⟩
      have hrep_mem : rep a ∈ s' := by
        exact Finset.mem_image.mpr ⟨a, ht_in_filter, rfl⟩
      have hrep : μ (rep a) ∈ (({a} : Finset G) : Set G) + H := by
        dsimp [rep]
        rw [dif_pos htrep]
        exact Classical.choose_spec htrep
      rw [Set.mem_add]
      refine ⟨rep a, by simpa [Finset.mem_coe] using hrep_mem, x - rep a, ?_, ?_⟩
      · change μ (x - rep a) ∈ H
        rw [Set.mem_add] at hrep
        rcases hrep with ⟨a', ha', b', hb', hsum'⟩
        have ha' : a' = a := by simpa using ha'
        subst a'
        have hdiff : μ x - μ (rep a) ∈ H := by
          rw [← hsum, ← hsum']
          have hsub : b - b' ∈ H := H.sub_mem (by simpa using hb) (by simpa using hb')
          convert hsub using 1
          abel
        have hdiff' : μ (x - rep a) ∈ H := by
          rw [map_sub]
          exact hdiff
        simpa [μ] using hdiff'
      · abel
    · intro hx
      rw [Set.mem_add] at hx
      rcases hx with ⟨a, ha, b, hb, hsum⟩
      rw [Set.mem_preimage]
      rw [Set.mem_add]
      rcases Finset.mem_image.mp ha with ⟨t, ht, rfl⟩
      have htfilter : t ∈ s.filter (fun t => hasRep t) := ht
      have ht : t ∈ s := (Finset.mem_filter.mp htfilter).1
      have htrep : hasRep t := (Finset.mem_filter.mp htfilter).2
      have hrep : μ (rep t) ∈ (({t} : Finset G) : Set G) + H := by
        dsimp [rep]
        rw [dif_pos htrep]
        exact Classical.choose_spec htrep
      rw [Set.mem_add] at hrep
      rcases hrep with ⟨t', ht', b', hb', hsum'⟩
      have ht' : t' = t := by simpa using ht'
      subst t'
      have hbK : b ∈ K := hb
      have hb_prod : μ b ∈ H := by
        simpa [K, AddSubgroup.mem_comap] using hbK
      refine ⟨t, by simpa using ht, μ b + b', H.add_mem hb_prod hb', ?_⟩
      calc
        t + (μ b + b') = (t + b') + μ b := by abel
        _ = μ (rep t) + μ b := by rw [hsum']
        _ = μ (rep t + b) := by rw [map_add]
        _ = μ x := by rw [← hsum]
  refine ⟨K, hKfin, s', ?_⟩
  rw [← hpre, hpre']

private lemma finite_of_isPeriodicTilingSet_zero
    {G : Type*} [AddCommGroup G]
    (h : IsPeriodicTilingSet ({0} : Set G)) : Finite G := by
  classical
  rcases h with ⟨H, hHfin, s, hs⟩
  have h0mem : (0 : G) ∈ (s : Set G) + H := by
    rw [← hs]
    simp
  rw [Set.mem_add] at h0mem
  rcases h0mem with ⟨t, ht, h, hh, hsum⟩
  have htH : t ∈ H := by
    have htneg : t = -h := by
      apply add_eq_zero_iff_eq_neg.mp
      simpa [add_comm] using hsum
    rw [htneg]
    exact H.neg_mem hh
  have hH_bot : H = ⊥ := by
    ext x
    constructor
    · intro hx
      have hxmem : x ∈ (s : Set G) + H := by
        rw [Set.mem_add]
        refine ⟨t, by simpa using ht, x - t, H.sub_mem hx htH, ?_⟩
        abel
      have hx0 : x ∈ ({0} : Set G) := by
        rw [hs]
        exact hxmem
      simpa using hx0
    · intro hx
      rw [AddSubgroup.mem_bot] at hx
      simp [hx]
  have hHfinite : Finite ↥H := by
    rw [hH_bot]
    exact Set.Finite.to_subtype (Set.finite_singleton (0 : G))
  exact (AddSubgroup.finite_iff_finite_and_finiteIndex H).mpr ⟨hHfinite, hHfin⟩

private lemma periodic_of_zsmul_image_zero
    {G : Type*} [AddCommGroup G] {S : Set G}
    (hper : IsPeriodicTilingSet (Set.image (fun x : G => (0 : ℤ) • x) S)) :
    IsPeriodicTilingSet S := by
  classical
  by_cases hS : S.Nonempty
  · have hzero : Set.image (fun x : G => (0 : ℤ) • x) S = ({0} : Set G) := by
      have := Set.Nonempty.image_const hS (0 : G)
      simpa using this
    have hsing : IsPeriodicTilingSet ({0} : Set G) := by
      rw [← hzero]
      exact hper
    have hGfinite : Finite G := finite_of_isPeriodicTilingSet_zero hsing
    let H : AddSubgroup G := ⊥
    have hHfin : H.FiniteIndex := @AddSubgroup.finiteIndex_of_finite G _ H hGfinite
    have hSfin : S.Finite := (@Set.finite_univ G hGfinite).subset (Set.subset_univ S)
    let s : Finset G := hSfin.toFinset
    have hs : (s : Set G) = S := hSfin.coe_toFinset
    refine ⟨H, hHfin, s, ?_⟩
    calc
      S = (s : Set G) := by rw [hs]
      _ = (s : Set G) + H := by
        ext y
        simp [H]
  · have hSempty : S = ∅ := by
      rw [Set.not_nonempty_iff_eq_empty] at hS
      exact hS
    refine ⟨(⊤ : AddSubgroup G), inferInstance, (∅ : Finset G), ?_⟩
    rw [hSempty]
    ext y
    simp

private lemma IsPeriodicTilingSet.map_surjective
    {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (π : G →+ H) (hπ : Function.Surjective π) {A : Set G}
    (h : IsPeriodicTilingSet A) : IsPeriodicTilingSet (π '' A) := by
  classical
  rcases h with ⟨L, hLfin, s, rfl⟩
  let L' : AddSubgroup H := L.map π
  have hL_le_comap : L ≤ L'.comap π := by
    intro x hx
    rw [AddSubgroup.mem_comap]
    exact AddSubgroup.mem_map.mpr ⟨x, hx, rfl⟩
  have hcomap_fin : (L'.comap π).FiniteIndex :=
    AddSubgroup.finiteIndex_of_le (H := L) (K := L'.comap π) hL_le_comap
  have hidx : (L'.comap π).index = L'.index := by
    exact AddSubgroup.index_comap_of_surjective L' hπ
  have hL'fin : L'.FiniteIndex := by
    rw [AddSubgroup.finiteIndex_iff]
    rw [← hidx]
    exact AddSubgroup.finiteIndex_iff.mp hcomap_fin
  refine ⟨L', hL'fin, s.image π, ?_⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Set.mem_add] at hx
    rcases hx with ⟨a, ha, b, hb, hsum⟩
    rw [Set.mem_add]
    refine ⟨π a, ?_, π b, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨a, by simpa using ha, rfl⟩
    · exact AddSubgroup.mem_map.mpr ⟨b, by simpa using hb, rfl⟩
    · simpa [map_add] using congrArg π hsum
  · intro hy
    rw [Set.mem_add] at hy
    rcases hy with ⟨a, ha, b, hb, hy⟩
    rw [Finset.mem_coe, Finset.mem_image] at ha
    rcases ha with ⟨a0, ha0, rfl⟩
    rcases AddSubgroup.mem_map.mp hb with ⟨b0, hb0, rfl⟩
    rw [Set.mem_image]
    refine ⟨a0 + b0, ?_, ?_⟩
    · rw [Set.mem_add]
      exact ⟨a0, by simpa using ha0, b0, by simpa using hb0, rfl⟩
    · simpa [map_add] using hy

lemma periodic_of_scaled_preimage_image
    {G : Type*} [AddCommGroup G] {d : ℕ}
    (π : (Fin d → ℤ) →+ G) (hπ : Function.Surjective π)
    (N : ℕ) {A : Set G}
    (hper : IsPeriodicTilingSet
      (Set.image (fun x : Fin d → ℤ => (N : ℤ) • x) (π ⁻¹' A))) :
    IsPeriodicTilingSet A := by
  classical
  let S : Set (Fin d → ℤ) := π ⁻¹' A
  have hSper : IsPeriodicTilingSet S := by
    by_cases hN : N = 0
    · subst N
      simpa [S] using periodic_of_zsmul_image_zero (G := Fin d → ℤ) (S := S) hper
    · have hNz : (N : ℤ) ≠ 0 := by
        exact_mod_cast hN
      exact periodic_of_zsmul_image_injective (G := Fin d → ℤ) (N := (N : ℤ)) hNz hper
  have hAper : IsPeriodicTilingSet (π '' S) :=
    IsPeriodicTilingSet.map_surjective π hπ hSper
  have hπA : π '' S = A := by
    dsimp [S]
    exact Set.image_preimage_eq A hπ
  simpa [hπA] using hAper


lemma IsTiling.translate {G : Type*} [AddCommGroup G] {F A : Set G}
    (h : IsTiling F A) (t : G) : IsTiling F (A + {t}) := by
  rw [IsTiling, AddSubgroup.isComplement_iff_existsUnique]
  intro g
  obtain ⟨p, hp, huniq⟩ :=
    AddSubgroup.IsComplement.existsUnique (S := A) (T := F) h (g - t)
  rcases p with ⟨a, f⟩
  refine ⟨(⟨a.1 + t, by
      rw [Set.mem_add]
      exact ⟨a.1, a.2, t, by simp, rfl⟩⟩, f), ?_, ?_⟩
  · have h1 : (a : G) + (f : G) + t = g := by
      simpa [add_assoc] using congrArg (fun x => x + t) hp
    simpa [add_assoc, add_comm, add_left_comm] using h1
  · rintro y hy
    rcases y with ⟨a', f'⟩
    have hg : (a' : G) + (f' : G) = g := hy
    rcases Set.mem_add.mp a'.2 with ⟨a0, ha0, t0, ht0, ha'_eq⟩
    have ht0' : t0 = t := Set.mem_singleton_iff.mp ht0
    subst t0
    have htmp : a0 + t + (f' : G) = g := by
      simpa [ha'_eq] using hg
    have htmp2 : a0 + (f' : G) + t = g := by
      simpa [add_assoc, add_comm, add_left_comm] using htmp
    have hsum' : a0 + (f' : G) = g - t := by
      exact eq_sub_iff_add_eq.mpr htmp2
    have hpair := huniq (⟨a0, ha0⟩, f') hsum'
    have ha0eq : a0 = (a : G) := by
      have hfst := congrArg Prod.fst hpair
      exact Subtype.ext_iff.mp hfst
    have hf'eq : f' = f := by
      exact congrArg Prod.snd hpair
    apply Prod.ext
    · apply Subtype.ext
      rw [← ha'_eq, ha0eq]
    · exact hf'eq

lemma IsPeriodicTilingSet.translate {G : Type*} [AddCommGroup G] {A : Set G}
    (h : IsPeriodicTilingSet A) (t : G) : IsPeriodicTilingSet (A + {t}) := by
  classical
  rcases h with ⟨H, hHfin, s, hs⟩
  refine ⟨H, hHfin, s.image (fun a => a + t), ?_⟩
  ext x
  constructor
  · intro hx
    rw [Set.mem_add] at hx ⊢
    rcases hx with ⟨a, ha, b, hb, hsum⟩
    have hb' : b = t := Set.mem_singleton_iff.mp hb
    subst b
    have haA : a ∈ (s : Set G) + H := by simpa [hs] using ha
    rw [Set.mem_add] at haA
    rcases haA with ⟨u, hu, h, hh, ha_eq⟩
    refine ⟨u + t, ?_, h, hh, ?_⟩
    · exact Finset.mem_image.mpr ⟨u, by simpa [Finset.mem_coe] using hu, rfl⟩
    · calc
        u + t + h = u + h + t := by abel
        _ = a + t := by rw [ha_eq]
        _ = x := hsum
  · intro hx
    rw [Set.mem_add] at hx ⊢
    rcases hx with ⟨a, ha, h, hh, hsum⟩
    rcases Finset.mem_image.mp ha with ⟨u, hu, rfl⟩
    refine ⟨u + h, ?_, t, by simp, ?_⟩
    · rw [hs]
      exact Set.add_mem_add (by simpa [Finset.mem_coe] using hu) hh
    · calc
        u + h + t = u + t + h := by abel
        _ = x := hsum

theorem quotient_aperiodic_tiling_equation_lift_of_zero
    {G : Type*} [AddCommGroup G] {d : ℕ}
    (π : (Fin d → ℤ) →+ G) (hπ : Function.Surjective π)
    {F : Set G} (hFfin : F.Finite) (hF0 : (0 : G) ∈ F)
    (hF : IsAperiodicTilingEquation F) :
    ∃ F' : Set (Fin d → ℤ), F'.Finite ∧ F'.Nonempty ∧ IsAperiodicTilingEquation F' := by
  classical
  obtain ⟨D, hD, hD0⟩ := AddSubgroup.exists_isComplement_left (π.ker) (0 : Fin d → ℤ)
  obtain ⟨N, T₁, T₂, hT₁fin, hT₂fin, hT₂zero, hcorr⟩ :=
    quotient_tiling_lift_tile0 π hπ D hD
  let F' : Set (Fin d → ℤ) :=
    ((Set.image (fun x : Fin d → ℤ => (N : ℤ) • x)
        ((π ⁻¹' (F \ {0})) ∩ D)) + T₁) ∪ T₂
  have hF' := hcorr hFfin hF0
  refine ⟨F', hF'.1, hF'.2.1, ?_⟩
  constructor
  · rcases hF.solvable with ⟨A, hA⟩
    have hAne : A.Nonempty := by
      simpa [IsTiling] using AddSubgroup.IsComplement.nonempty_left
        (by simpa [IsTiling] using hA)
    rcases hAne with ⟨a₀, ha₀⟩
    let A₀ : Set G := A + {-a₀}
    have hA₀tile : IsTiling F A₀ := IsTiling.translate hA (-a₀)
    have hA₀zero : (0 : G) ∈ A₀ := by
      rw [Set.mem_add]
      exact ⟨a₀, ha₀, -a₀, by simp, by simp⟩
    have hA₀lift := hF'.2.2.1 A₀ hA₀tile hA₀zero
    exact ⟨Set.image (fun x : Fin d → ℤ => (N : ℤ) • x) (π ⁻¹' A₀), hA₀lift⟩
  · intro A' hA' hA'per
    have hA'ne : A'.Nonempty := by
      simpa [IsTiling] using AddSubgroup.IsComplement.nonempty_left
        (by simpa [IsTiling] using hA')
    rcases hA'ne with ⟨a₀, ha₀⟩
    let A₀' : Set (Fin d → ℤ) := A' + {-a₀}
    have hA₀'tile : IsTiling F' A₀' := IsTiling.translate hA' (-a₀)
    have hA₀'zero : (0 : Fin d → ℤ) ∈ A₀' := by
      rw [Set.mem_add]
      exact ⟨a₀, ha₀, -a₀, by simp, by simp⟩
    have hA₀'per : IsPeriodicTilingSet A₀' := IsPeriodicTilingSet.translate hA'per (-a₀)
    rcases hF'.2.2.2 A₀' hA₀'tile hA₀'zero with ⟨A₀, hA₀tile, hA₀zero, hA₀eq⟩
    have hA₀per : IsPeriodicTilingSet A₀ :=
      periodic_of_scaled_preimage_image π hπ N (by
        simpa [hA₀eq] using hA₀'per)
    exact hF.aperiodic A₀ hA₀tile hA₀per

end Commons.PeriodicTiling
