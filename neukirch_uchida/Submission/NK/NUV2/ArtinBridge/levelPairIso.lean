import Mathlib
import Submission.NK.NUV2.ArtinBridge.Datum

/-!
# The levelwise norm-group/Galois-subgroup correspondence behind `CanonicalArtinDatum`

`NK.NUV2.ArtinBridge.CanonicalArtinDatum` (file `Datum.lean`) asks for a *coherent* system of
Artin maps `C_K → Γ_{L,ℓ}` on the `ℓ`-power levels `L/K of `Ω`, whose kernels are the norm groups
`N_{L/K}C_L` and which is compatible with the transition maps `ellRestrict` (the restriction of the
abelianised Galois groups).  Its own docstring records that the levelwise reciprocity isomorphisms
produced on disk from `hFC : FundamentalClassElement` are obtained by `Classical.choice` from
`Nonempty`/`∃`-statements, hence carry *no* information about their behaviour at different levels,
and that the datum is the *canonical* (Frobenius- or local-invariant-normalised) Artin map.

This file isolates that content in a citable form.  For an `ℓ`-level `M` (a finite normal level of
`Ω/K` whose Galois group is an `ℓ`-group, so that the `ℓ`-part of `Gal(M/K)^ab` is all of it) any
coherent system induces an isomorphism

`e : C_K ⧸ N_{M/K}C_M ≅ Gal(M/K)^ab`

which carries the image of the norm subgroup `N_{L/K}C_L` of each `ℓ`-sublevel `L ⊆ M` onto the
kernel of the restriction `Gal(M/K)^ab → Gal(L/K)^ab` — i.e. onto the image of
`Gal(M/L)^ab`.  This is **Neukirch, *Algebraic Number Theory*, V.5.5–V.5.6** / **Milne, *CFT*,
Lemma 9.1** (the Artin isomorphism is compatible with the passage to subextensions and the
fixed-field correspondence), restricted to the `ℓ`-power levels; equivalently, it is the
norm-group/Galois-subgroup correspondence `N_{L/K}C_L ↔ Gal(M/L)^ab` of class field theory.

* `LevelPairIso K Ω ℓ` — the statement in question, as a `Prop` (the "pair isomorphism" input).
* `levelPairIso_of_canonicalArtinDatum` — **`CanonicalArtinDatum K Ω ℓ` implies `LevelPairIso`
  `K Ω ℓ`**: a proof of the datum from `hFC` alone would in particular prove the above classical
  correspondence for `ℓ`-levels.

For the converse direction see the remarks at the end of the file: given a pair-compatible
isomorphism at every `ℓ`-level, a coherent system is produced by a finite-intersection argument,
because every finite set of levels has a common upper bound `N` (with `Gal(N/K)` an `ℓ`-group) and
an isomorphism at `N` induces a coherent system on all its `ℓ`-sublevels.  So `LevelPairIso` is the
exact content of `CanonicalArtinDatum`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NK.NUV2.ArtinBridge

open NK.GlobalCFT (IdeleClassGroup)

/-- **The `ℓ`-part of the abelianisation of a finite `ℓ`-group is everything**: if every element of
`G` has `ℓ`-power order, then every element of `Abelianization G` does.  Consequently, for an
`ℓ`-level `M` (i.e. `IsPGroup ℓ Gal(M/K)`) the subgroup `LevelEllPart M.L ℓ` is `⊤`, and a hom
`C_K →* ↥(LevelEllPart M.L ℓ)` is just a hom `C_K →* Gal(M/K)^ab`. -/
theorem ellPart_abelianization_eq_top {G : Type*} [Group G] (ℓ : ℕ) (h : IsPGroup ℓ G) :
    NK.Reconstruct.ellPart (Abelianization G) ℓ = ⊤ := by
  refine (Subgroup.eq_top_iff' _).mpr fun x => ?_
  refine QuotientGroup.induction_on x fun g => ?_
  obtain ⟨k, hk⟩ := h g
  refine (NK.Reconstruct.mem_ellPart_iff ℓ (Abelianization.of g)).mpr ⟨k, ?_⟩
  change Abelianization.of g ^ ℓ ^ k = 1
  rw [← map_pow, hk, map_one]

/-- **The levelwise Artin isomorphism with the norm-group/Galois-subgroup correspondence.**  For
every `ℓ`-level `M` of `Ω/K` there is an isomorphism
`C_K ⧸ N_{M/K}C_M ≅ Gal(M/K)^ab` which, for every `ℓ`-sublevel `L ⊆ M`, carries the image of the
norm subgroup `N_{L/K}C_L` onto the kernel of the restriction map
`levelRestrict L M h : Gal(M/K)^ab → Gal(L/K)^ab` (i.e. onto `Gal(M/L)^ab`).

This is the "pair (norm group, Galois subgroup) correspondence" of Neukirch V.5.5–V.5.6 / Milne
*CFT* Lemma 9.1 at the `ℓ`-power levels. -/
def LevelPairIso (K : Type) [Field K] [NumberField K] (Ω : Type) [Field Ω] [Algebra K Ω]
    [IsGalois K Ω] (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∀ (M : NK.Reconstruct.FrobLevel K Ω), IsPGroup ℓ (↥M.L ≃ₐ[K] ↥M.L) →
    ∃ e : IdeleClassGroup K ⧸
          NK.GlobalCFT.Idele.normClassSubgroup K ↥M.L ≃* NK.Reconstruct.LevelAbelianization M.L,
      ∀ (L : NK.Reconstruct.FrobLevel K Ω) (hL : IsPGroup ℓ (↥L.L ≃ₐ[K] ↥L.L))
        (h : L.L ≤ M.L),
        Subgroup.map e.toMonoidHom
            (Subgroup.map (QuotientGroup.mk' (NK.GlobalCFT.Idele.normClassSubgroup K ↥M.L))
              (NK.GlobalCFT.Idele.normClassSubgroup K ↥L.L)) =
          (NK.Reconstruct.levelRestrict L M h).ker

/-- **The canonical Artin datum implies the levelwise norm-group/Galois-subgroup
correspondence.**  For an `ℓ`-level `M`, the map `art M : C_K → Γ_{M,ℓ} = Gal(M/K)^ab` of a
coherent system descends to an isomorphism `C_K ⧸ N_{M/K}C_M ≅ Gal(M/K)^ab` (surjectivity plus the
kernel condition, and the `ℓ`-part being everything because `M` is an `ℓ`-level), and the coherence
condition `art L = ellRestrict ∘ art M` identifies the image of `N_{L/K}C_L` with the kernel of the
restriction map to `L`.

Consequently, proving `CanonicalArtinDatum` from `hFC` alone would prove the classical
norm-group/Galois-subgroup correspondence for `ℓ`-levels, which is *not* available in this
workspace (cf. the licensed input in `NUV2/ArtinBridge/normGroupCorrespondence.lean`). -/
theorem levelPairIso_of_canonicalArtinDatum {K : Type} [Field K] [NumberField K] {Ω : Type}
    [Field Ω] [Algebra K Ω] [IsGalois K Ω] {ℓ : ℕ} [Fact ℓ.Prime]
    (h : CanonicalArtinDatum K Ω ℓ) : LevelPairIso K Ω ℓ := by
  classical
  obtain ⟨art, hcoh, hker, hsurj⟩ := h
  intro M hM
  set NM : Subgroup (IdeleClassGroup K) :=
    NK.GlobalCFT.Idele.normClassSubgroup K ↥M.L with hNM
  -- the underlying map `C_K → Gal(M/K)^ab`
  let f : IdeleClassGroup K →* NK.Reconstruct.LevelAbelianization M.L :=
    (Subgroup.subtype (NK.Reconstruct.LevelEllPart M.L ℓ)).comp (art M hM)
  have hfx : ∀ x : IdeleClassGroup K,
      f x = ((art M hM x : ↥(NK.Reconstruct.LevelEllPart M.L ℓ)) :
        NK.Reconstruct.LevelAbelianization M.L) := fun x => rfl
  have hfker : f.ker = NM := by
    rw [hNM, MonoidHom.ker_comp_of_injective _ _ (Subgroup.subtype_injective _)]
    exact hker M hM
  have hfsurj : Function.Surjective f := by
    intro y
    have htop : NK.Reconstruct.LevelEllPart M.L ℓ = ⊤ :=
      ellPart_abelianization_eq_top (G := ↥M.L ≃ₐ[K] ↥M.L) ℓ hM
    have hy : y ∈ NK.Reconstruct.LevelEllPart M.L ℓ := by
      rw [htop]
      exact Subgroup.mem_top y
    obtain ⟨x, hx⟩ := hsurj M hM ⟨y, hy⟩
    exact ⟨x, by rw [hfx]; exact congrArg Subtype.val hx⟩
  let lift : IdeleClassGroup K ⧸ NM →* NK.Reconstruct.LevelAbelianization M.L :=
    QuotientGroup.lift NM f (le_of_eq hfker.symm)
  have hlift : ∀ x : IdeleClassGroup K, lift (QuotientGroup.mk' NM x) = f x :=
    fun x => QuotientGroup.lift_mk' _ _ x
  have hker_lift : lift.ker = ⊥ := by
    rw [QuotientGroup.ker_lift, hfker, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hlift_inj : Function.Injective lift := (MonoidHom.ker_eq_bot_iff lift).mp hker_lift
  have hlift_surj : Function.Surjective lift := by
    intro y
    obtain ⟨x, hx⟩ := hfsurj y
    exact ⟨QuotientGroup.mk' NM x, by rw [hlift, hx]⟩
  let e : IdeleClassGroup K ⧸ NM ≃* NK.Reconstruct.LevelAbelianization M.L :=
    MulEquiv.ofBijective lift ⟨hlift_inj, hlift_surj⟩
  have he : e.toMonoidHom = lift := MonoidHom.ext fun a => MulEquiv.ofBijective_apply lift _ a
  refine ⟨e, ?_⟩
  intro L hL h
  -- the coercion computation at `x`
  have key : ∀ x : IdeleClassGroup K,
      NK.Reconstruct.levelRestrict L M h (f x) = 1 ↔
        x ∈ NK.GlobalCFT.Idele.normClassSubgroup K ↥L.L := by
    intro x
    have h1 : (NK.Reconstruct.ellRestrict ℓ L M h) (art M hM x) = art L hL x := by
      have h2 := congrArg
        (fun φ : IdeleClassGroup K →* ↥(NK.Reconstruct.LevelEllPart L.L ℓ) => φ x)
        (hcoh L M hL hM h)
      simpa only [MonoidHom.comp_apply] using h2.symm
    have hcoe : NK.Reconstruct.levelRestrict L M h (f x) =
        ((art L hL x : ↥(NK.Reconstruct.LevelEllPart L.L ℓ)) :
          NK.Reconstruct.LevelAbelianization L.L) := by
      rw [hfx x, ← h1]
      exact (NK.Reconstruct.ellRestrict_coe ℓ L M h (art M hM x)).symm
    rw [← hker L hL, MonoidHom.mem_ker, hcoe]
    exact ⟨fun hx => Subtype.ext hx, fun hx => congrArg Subtype.val hx⟩
  have hcomp : lift.comp (QuotientGroup.mk' NM) = f := MonoidHom.ext fun x => hlift x
  rw [he, Subgroup.map_map, hcomp]
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, hxy⟩
    rw [MonoidHom.mem_ker, ← hxy]
    exact (key x).mpr hx
  · intro hy
    rw [MonoidHom.mem_ker] at hy
    obtain ⟨x, rfl⟩ := hfsurj y
    exact ⟨x, (key x).mp hy, rfl⟩

end NK.NUV2.ArtinBridge
