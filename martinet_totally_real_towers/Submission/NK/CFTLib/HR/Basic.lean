import Mathlib
import Submission.NK.CFTLib.hilbertReciprocityCyclicAux
import Submission.NK.CFTLib.Arl.exists_monoidHom_ideleArtin
import Submission.NK.CFTLib.Arl.normIdeles_mem_ker_of_ideleArtin
import Submission.NK.CFTLib.Arl.exists_norm_mul_mem_congruenceSubgroup
import Submission.NK.CFTLib.ARL.artinReciprocity_cyclotomic
import Submission.NK.CFTLib.ArtinReciprocityIdeal.Conductor
import Submission.NK.CFTLib.ArtinReciprocityIdeal.AbelianReduction
import Submission.NK.GlobalCFT.IdeleClassGroup.globalCFT_idealClassMap_exists
import Submission.NK.GlobalCFT.Place

/-!
# Auxiliaries for the Hilbert-reciprocity crux `NK.CFTLib.HilbertReciprocityOnePlace`

Two proved ingredients of the design in
`Submission/Work/CFTLib/HR/hilbertReciprocityOnePlace_proof.lean` (lemmas L3):

* `NK.CFTLib.HR.exists_artin_of_cyclotomic`: for a **cyclotomic** extension `L = K(ζ_q)`
  (`q` prime) the ideal-theoretic Artin law `NK.CFTLib.ARL.artinReciprocity_cyclotomic`
  (Milne, *CFT*, VII Example 8.2, the only reciprocity law available **sorry-free** in this
  workspace) produces an idèlic Artin map `art : 𝕀_K →* Gal(L/K)` with the four classical
  clauses: it kills the principal idèles `Kˣ`, kills the idèle norms `N_{L/K}𝕀_L`, is
  Frobenius-normalised at every prime not dividing the modulus `m = q·|N(𝔡_{L/K})|`, and is
  surjective.  (The modulus is chosen to be a multiple of both `q` and the norm of the different,
  which is exactly the shape the congruence-subgroup machinery
  `NK.CFTLib.Arl.exists_monoidHom_ideleArtin` consumes.)

* `NK.CFTLib.HR.exists_zpow_unifUnit_mul_mem_localUnits`: the local decomposition
  `K_Qˣ = ⟨ϖ_Q⟩ · 𝒪_Qˣ` at a finite place, in the form `b = ϖ^n·u` with `u` a local unit.
  This is what turns the value `art(onePlace Q b) = Frob_Q ^ (exp_Q b)` into the local-norm
  criterion `b ∈ N_Q(L) ⟺ f_Q ∣ v_Q(b)` at an unramified place.

Everything in this file is `sorry`-free and depends only on `sorry`-free imports.
-/

set_option maxHeartbeats 1600000
open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.HR

open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The Galois group of a cyclotomic extension is commutative: the cyclotomic character
`ζ ↦ ζ ^ _` embeds it into `(ZMod q)ˣ`. -/
theorem hcomm_of_isCyclotomic (q : ℕ) [Fact q.Prime] [IsCyclotomicExtension {q} K L] :
    ∀ a b : Gal(L/K), a * b = b * a := by
  have hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta q K L) q :=
    IsCyclotomicExtension.zeta_spec q K L
  have hχinj : Function.Injective (hζ.autToPow K) := IsPrimitiveRoot.autToPow_injective K hζ
  intro a b
  exact hχinj (by rw [map_mul, map_mul, mul_comm])

/-- **The idèlic Artin map of a cyclotomic extension**, built from the proved cyclotomic
reciprocity law `NK.CFTLib.ARL.artinReciprocity_cyclotomic`.

There is a monoid homomorphism `art : 𝕀_K →* Gal(K(ζ_q)/K)` which
* kills the principal idèles `Kˣ`,
* kills the idèle norms `N_{L/K} 𝕀_L`,
* sends the idèle of a prime `𝔭 ∤ q·|N(𝔡_{L/K})|` to its Frobenius,
* is surjective. -/
theorem exists_artin_of_cyclotomic (q : ℕ) [Fact q.Prime] [IsCyclotomicExtension {q} K L] :
    ∃ art : Idele K →* Gal(L/K),
      (∀ a : Kˣ, art (Idele.principalIdele K a) = 1) ∧
      (∀ y : Idele L, art (Idele.normIdeleHom K L y) = 1) ∧
      (∀ (𝔭 : HeightOneSpectrum (𝓞 K)),
        ((q * Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L)) : ℕ) : 𝓞 K) ∉ 𝔭.asIdeal →
        art (NK.HeckeL.ideleOfPrime K 𝔭) = NK.Chebotarev.frobAtPrime 𝔭) ∧
      Function.Surjective art := by
  classical
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hcomm : ∀ a b : Gal(L/K), a * b = b * a := hcomm_of_isCyclotomic (K := K) (L := L) q
  set m : ℕ := q * Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L)) with hmdef
  have hdiff_ne : Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L)) ≠ 0 := by
    rw [Ideal.absNorm_ne_zero_iff]
    exact Ring.HasFiniteQuotients.finiteQuotient (differentIdeal_ne_bot (A := 𝓞 K) (B := 𝓞 L))
  have hm : 0 < m := Nat.mul_pos (Fact.out : q.Prime).pos (Nat.pos_of_ne_zero hdiff_ne)
  have hram : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), (m : 𝓞 K) ∉ 𝔭.asIdeal →
      Ideal.ramificationIdxIn 𝔭.asIdeal (𝓞 L) = 1 := by
    intro 𝔭 h𝔭
    refine NK.CFTLib.ramificationIdxIn_eq_one_of_absNorm_differentIdeal_notMem 𝔭 ?_
    intro hmem
    exact h𝔭 (by
      have hmc : (m : 𝓞 K) = (q : 𝓞 K)
          * ((Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L)) : ℕ) : 𝓞 K) := by
        rw [hmdef]; push_cast; ring
      rw [hmc]
      exact Ideal.mul_mem_left _ _ hmem)
  have hkillq : NK.CFTLib.artinKillsPrincipal K L q := by
    intro a ha hpos s e σ hs hfac hfrob
    exact NK.CFTLib.ARL.artinReciprocity_cyclotomic K L q a ha hpos s e σ hs hfac hfrob
  have hprinc : NK.CFTLib.artinKillsPrincipal K L m :=
    hkillq.mono (by rw [hmdef]; exact dvd_mul_right q _)
  obtain ⟨U, hU, hadj⟩ := NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust K m hm
  obtain ⟨art, hval, hprin, hfrob, hsurj⟩ :=
    NK.CFTLib.Arl.exists_monoidHom_ideleArtin (K := K) (L := L) hcomm m hm hram hprinc U hU hadj
  have hUeq : U = NK.CFTLib.Arl.congruenceSubgroup K m :=
    SetLike.ext fun x => (hU.1 x).trans Iff.rfl
  have hadjN : ∀ y : Idele L, ∃ d : Lˣ,
      Idele.normIdeleHom K L (y * Idele.principalIdele L d) ∈ U := by
    intro y
    obtain ⟨d, hd⟩ := NK.CFTLib.Arl.exists_norm_mul_mem_congruenceSubgroup K L m hm y
    exact ⟨d, hUeq ▸ hd⟩
  have hnorm : ∀ y : Idele L, art (Idele.normIdeleHom K L y) = 1 := by
    intro y
    rw [hval (Idele.normIdeleHom K L y)]
    exact NK.CFTLib.Arl.normIdeles_mem_ker_of_ideleArtin hcomm m hm hram hprinc U hU hadj hadjN y
  exact ⟨art, hprin, hnorm, hfrob, hsurj⟩

/-- **Decomposition of a local element into a power of a uniformiser times a local unit:**
for `b ∈ K_Qˣ` there are `n : ℤ` and a local unit `u` with `b = ϖ_Q ^ n · u`. -/
theorem exists_zpow_unifUnit_mul_mem_localUnits
    {K : Type} [Field K] [NumberField K] (q : HeightOneSpectrum (𝓞 K))
    (b : (q.adicCompletion K)ˣ) :
    ∃ (n : ℤ) (u : (q.adicCompletion K)ˣ),
      u ∈ Place.localUnits K (Place.ofFinite q) ∧
        b = NK.GlobalCFT.IdeleClassGroup.unifUnit K q ^ n * u := by
  classical
  have hb : Valued.v (b : q.adicCompletion K) ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact Units.ne_zero b
  let L : ℤ := WithZero.log (Valued.v (b : q.adicCompletion K))
  refine ⟨-L, b * (NK.GlobalCFT.IdeleClassGroup.unifUnit K q) ^ L, ?_, ?_⟩
  · rw [Place.mem_localUnits_ofFinite_iff_valued_eq_one]
    have hcoe : ((b * (NK.GlobalCFT.IdeleClassGroup.unifUnit K q) ^ L :
        (q.adicCompletion K)ˣ) : q.adicCompletion K)
        = (b : q.adicCompletion K)
          * (((NK.GlobalCFT.IdeleClassGroup.unifUnit K q) ^ L : (q.adicCompletion K)ˣ) :
              q.adicCompletion K) := Units.val_mul _ _
    rw [hcoe, map_mul, NK.GlobalCFT.IdeleClassGroup.valued_unifUnit_zpow]
    have hL : WithZero.exp L = Valued.v (b : q.adicCompletion K) := by
      show WithZero.exp (WithZero.log (Valued.v (b : q.adicCompletion K))) = _
      exact WithZero.exp_log hb
    rw [← hL, ← WithZero.exp_add]
    simp
  · rw [mul_comm b ((NK.GlobalCFT.IdeleClassGroup.unifUnit K q) ^ L), ← mul_assoc,
      ← zpow_add, neg_add_cancel, zpow_zero, one_mul]

end NK.CFTLib.HR

namespace NK.CFTLib.HR

/-- **A subgroup containment which is an equality by index.**  If `N ≤ ker φ` has finite index,
`range φ` has non-zero cardinality, and `g ∈ range φ` has `orderOf g = N.index`, then
`ker φ = N`: indeed `orderOf g` divides `Nat.card (range φ) = (ker φ).index`, while `N ≤ ker φ`
forces `(ker φ).index ≤ N.index`. -/
theorem ker_eq_of_le_of_orderOf_eq_index {A G : Type*} [Group A] [Group G] (φ : A →* G)
    (N : Subgroup A) [N.FiniteIndex] (hle : N ≤ MonoidHom.ker φ)
    (hcard : Nat.card ↥φ.range ≠ 0) {g : G} (hg : g ∈ φ.range)
    (hord : orderOf g = N.index) : MonoidHom.ker φ = N := by
  have hN : N.index ≠ 0 := Subgroup.finiteIndex_iff.mp inferInstance
  have hker_ne : (MonoidHom.ker φ).index ≠ 0 := by
    rw [Subgroup.index_ker φ]; exact hcard
  have hle_index : (MonoidHom.ker φ).index ≤ N.index := Subgroup.index_antitone hle
  have hdvd : orderOf g ∣ (MonoidHom.ker φ).index := by
    rw [Subgroup.index_ker φ]
    exact (Subgroup.orderOf_coe (⟨g, hg⟩ : ↥φ.range)).symm ▸ orderOf_dvd_natCard _
  have heq : (MonoidHom.ker φ).index = N.index := by
    refine le_antisymm hle_index ?_
    rw [← hord]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero hker_ne) hdvd
  have hone : N.relIndex (MonoidHom.ker φ) = 1 := by
    have h := Subgroup.relIndex_mul_index hle
    rw [heq] at h
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hN) (by rw [h, one_mul])
  exact le_antisymm (Subgroup.relIndex_eq_one.mp hone) hle

end NK.CFTLib.HR
