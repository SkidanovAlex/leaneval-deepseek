import Mathlib
import Submission.Work.DSG4b.gonfPerfect.Basic
import Submission.Work.DSG4b.gonfPerfect.pbAux
import Submission.Work.DSG4b.gonfPerfect.integral.integral_S
import Submission.Work.DSG4b.gonfPerfect.maxstep.maximalityStep
import Submission.Work.DSG4b.gonfPerfect.flat.flat_S
import Submission.Work.DSG4b.gonfPerfect.surj.psi_surjective
import Submission.Work.DSG4b.gonfPerfect.key.ker_tauN

namespace Work.DSG4b.gonfPerfect

universe u

open IsLocalRing

/-- **The colimit of the tower perfectifies `R`.**  Given the tower data `D : PData R p` of a local
ring `R` whose residue field has characteristic a prime `p`, the colimit `S = D.S` is a flat local
`R`-algebra with `𝔪_R S = 𝔪_S` and perfect residue field `k^{perf} = PerfectClosure k p`. -/
theorem main_of_PData (R : Type u) [CommRing R] [IsLocalRing R] (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField R) p] (D : PData R p) :
    ∃ (S : Type u) (_ : CommRing S) (_ : IsLocalRing S) (φ : R →+* S),
      φ.Flat ∧ (IsLocalRing.maximalIdeal R).map φ = IsLocalRing.maximalIdeal S ∧
        PerfectField (IsLocalRing.ResidueField S) := by
  -- input: flatness of the colimit
  have hflat : D.phi.Flat := Work.DSG4b.gonfPerfect.flat.flat_S R p D
  -- input: integrality of the colimit over `R`
  have hint : D.phi.IsIntegral := Work.DSG4b.gonfPerfect.integral.integral_S R p D
  -- input: surjectivity of `psi`
  have hsurj : Function.Surjective D.psi := Work.DSG4b.gonfPerfect.surj.psi_surjective R p D
  -- input: the fibre of each stage
  have hkey : ∀ N : ℕ, RingHom.ker (D.tauN N) =
      Ideal.map (algebraMap R (D.AN N)) (IsLocalRing.maximalIdeal R) :=
    fun N => Work.DSG4b.gonfPerfect.key.ker_tauN R p D N
  -- the kernel of `psi` is `𝔪 · S`
  have hcomp : ∀ N : ℕ, (D.incl N).comp (algebraMap R (D.AN N)) = D.phi := fun N => by
    ext r
    exact D.incl_eq_phi_algebraMap N r
  have hker : RingHom.ker D.psi = Ideal.map D.phi (IsLocalRing.maximalIdeal R) := by
    refine le_antisymm ?_ ?_
    · intro s hs
      obtain ⟨N, x, rfl⟩ := Ring.DirectLimit.exists_of s
      have hx0 : D.tauN N x = 0 := by
        rw [← D.psi_incl N x]
        exact hs
      have hx : x ∈ Ideal.map (algebraMap R (D.AN N)) (IsLocalRing.maximalIdeal R) := by
        rw [← hkey N, RingHom.mem_ker]
        exact hx0
      have hmem : D.incl N x ∈ Ideal.map (D.incl N)
          (Ideal.map (algebraMap R (D.AN N)) (IsLocalRing.maximalIdeal R)) :=
        Ideal.mem_map_of_mem (D.incl N) hx
      rw [Ideal.map_map, hcomp N] at hmem
      exact hmem
    · rw [Ideal.map_le_iff_le_comap]
      intro r hr
      rw [Ideal.mem_comap, RingHom.mem_ker, D.psi_comp_phi r,
        (IsLocalRing.residue_eq_zero_iff r).mpr hr, map_zero]
  -- `𝔪 · S` is maximal, because `S ⧸ 𝔪S ≅ k^{perf}` is a field
  have hmax : (Ideal.map D.phi (IsLocalRing.maximalIdeal R)).IsMaximal := by
    rw [← hker]
    exact RingHom.ker_isMaximal_of_surjective D.psi hsurj
  -- `S` is local: every maximal ideal lies over `𝔪` (integrality) and contains `𝔪 · S`
  have huniq : ∃! I : Ideal D.S, I.IsMaximal := by
    refine ⟨Ideal.map D.phi (IsLocalRing.maximalIdeal R), hmax, fun J hJ => ?_⟩
    haveI : J.IsMaximal := hJ
    have hcomap : (J.comap D.phi).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal D.phi hint J
    have hcomap_eq : J.comap D.phi = IsLocalRing.maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal hcomap
    have hle : Ideal.map D.phi (IsLocalRing.maximalIdeal R) ≤ J :=
      Ideal.map_le_iff_le_comap.mpr hcomap_eq.ge
    exact (Ideal.IsMaximal.eq_of_le hmax hJ.ne_top hle).symm
  haveI hlocS : IsLocalRing D.S := IsLocalRing.of_unique_max_ideal huniq
  have hmaxIdeal : IsLocalRing.maximalIdeal D.S = Ideal.map D.phi (IsLocalRing.maximalIdeal R) :=
    (IsLocalRing.eq_maximalIdeal hmax).symm
  -- the residue field of `S` is `k ^ perf`
  -- the residue field of `S` is the perfect closure of the residue field of `R`
  have eF : IsLocalRing.ResidueField D.S ≃+* D.PC :=
    (Ideal.quotEquivOfEq hmaxIdeal).trans
      ((Ideal.quotEquivOfEq hker).symm.trans (RingHom.quotientKerEquivOfSurjective hsurj))
  refine ⟨D.S, inferInstance, hlocS, D.phi, hflat, ?_, ?_⟩
  · rw [hmaxIdeal]
  · exact PerfectField.of_ringEquiv eF.symm

/-- The tower data exist: take a `p`-basis of the residue field (whose existence is the classical
`p`-basis theorem, proved in `Work.DSG4b.gonfPerfect.pbAux` + `...maxstep`) and lift it to `R`. -/
theorem existsPData (R : Type u) [CommRing R] [IsLocalRing R] (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField R) p] : Nonempty (PData R p) := by
  obtain ⟨Λ, b, hb⟩ := pbAux.exists_pBasis_of_relation (IsLocalRing.ResidueField R) p
    (Work.DSG4b.gonfPerfect.maxstep.maximalityStep (IsLocalRing.ResidueField R) p)
  choose lift hlift using fun x : Λ =>
    IsLocalRing.residue_surjective (R := R) (x : IsLocalRing.ResidueField R)
  exact ⟨⟨Λ, b, hb, lift, hlift⟩⟩

/-- **Perfectification of a commutative local ring.**  Every commutative local ring `R` admits a
flat local `R`-algebra `S` with `𝔪_R S = 𝔪_S` (the maximal ideal of `S` is the extension of that of
`R`) and *perfect* residue field.

No Noetherian hypothesis is needed (and must not be added).  Intended construction: let
`k = ResidueField R`; take a `p`-basis `Λ` of `k` over `k^p` when `char k = p > 0` (Zorn; `Λ = ∅`
in characteristic `0`), let `b̃ ∈ R` lift `b ∈ Λ`, and set `S := colim_N R[T_b : b ∈ Λ]/(T_b^{p^N} -
b̃)` with transitions `T_b ↦ T_b^p`.  Each stage is free over `R`, its `𝔪`-fibre is the field
`k^{1/p^N}` (a `p`-basis is a `p^N`-basis), so each stage is a flat local `R`-algebra with maximal
ideal `𝔪S`; the filtered colimit is again flat (and local), and its residue field is `k^{perf}`.
In characteristic `0` one takes `S = R`. -/
theorem exists_flat_local_perfect_residue (R : Type u) [CommRing R] [IsLocalRing R] :
    ∃ (S : Type u) (_ : CommRing S) (_ : IsLocalRing S) (φ : R →+* S),
      φ.Flat ∧ (IsLocalRing.maximalIdeal R).map φ = IsLocalRing.maximalIdeal S ∧
        PerfectField (IsLocalRing.ResidueField S) := by
  by_cases hzero : CharZero (IsLocalRing.ResidueField R)
  · -- characteristic zero: `S = R` and the residue field is already perfect
    refine ⟨R, inferInstance, inferInstance, RingHom.id R, RingHom.Flat.id R, ?_, ?_⟩
    · rw [Ideal.map_id]
    · exact PerfectField.ofCharZero
  · -- positive characteristic: perfectify the residue field
    have hex : ∃ q : ℕ, q.Prime ∧ CharP (IsLocalRing.ResidueField R) q := by
      obtain ⟨q, hq⟩ := CharP.exists (IsLocalRing.ResidueField R)
      rcases CharP.char_is_prime_or_zero (IsLocalRing.ResidueField R) q with hprime | h0
      · exact ⟨q, hprime, hq⟩
      · exact absurd ((CharP.charP_zero_iff_charZero (IsLocalRing.ResidueField R)).mp (h0 ▸ hq)) hzero
    obtain ⟨q, hq, hch⟩ := hex
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (IsLocalRing.ResidueField R) q := hch
    obtain ⟨D⟩ := existsPData R q
    exact main_of_PData R q D

end Work.DSG4b.gonfPerfect
