import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Submission.Work.SSGRoute.PT.exists_glue_extLoc
import Submission.Work.SSGRoute.e9_glue_phiAt
import Submission.Work.SSGRoute.e9_local_decomposition
import Submission.Work.SSGRoute.e9_vanish_off_finite
import Submission.Work.SSGRoute.local_phi_realization_in
import Submission.Work.SSGRoute.phi1_mono_sylow_in
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

LEAD NOTES (SSG E9 pt_sha2_core, re-dispatch). The statement is unchanged (ssg4). Its proof uses the Ω versions (ssg5 DESIGN_FIX §4):
- E6Ω: Work.SSGRoute.phi1_mono_sylow_in, PROVED and axiom-clean. Import Submission.Work.SSGRoute.phi1_mono_sylow_in.
- E7cΩ: Work.SSGRoute.local_phi_realization_in, in flight (H968, waiting on the E7b redesign). Import Submission.Work.SSGRoute.local_phi_realization_in and use its statement; the missing proof disappears when it lands.
- E1b: ext_sha1_bridge (PROVED). E2: ext_idele_shapiro (PROVED). E4Ω phi0_trivial_epi_in and E5Ω phi1_mono_pgroup_in are also PROVED.
- Take Ω := AlgebraicClosure K. The vanishing to establish is PhiOneVanishesIn Ω (x − extToClasses z); this is weaker than the old E6 form.
- The proved reduction (∃ z, extToClasses z = x) ↔ extDelta x = 0 is exactness of the class-formation sequence.
Do NOT reprove any of these, and do not restate them under other names. Do NOT route through tatePoitouEmbedding / poitouTate_pairing_var / sha_card_euler: this E-core route replaces them.

===== ssg4/pt_sha2_core.md =====
# E9 `pt_sha2_core` — the Poitou–Tate core in `Ext` form (`Ш² ↪ (Ш¹)^∨`)

**Statement.** `μ_p ⊆ K` and `M` is finite `p`-torsion. Let `x ∈ Ext¹_G(M, C_K)` with
`pairK x h = 0` for every `h ∈ H¹(Gal(K/k), M)` that is locally trivial at every place. Then `x`
comes from `Ext¹_G(M, 𝕀_K)`.

**Route.** Write `ψ = φ¹(x)`. It is a compatible family over levels.
1. **`ψ` kills `Ш¹(k,M)` at every level.** ...
2. **Finite-`S` continuity.** ...
3. **Extend and decompose.** ...
4. **Realise each `ψ_v`** by `z_v` (E7c), unramified for `v ∉ S` (E7c's unramified clause).
   Assemble `z ∈ Ext¹_G(M, 𝕀_K)` (E2). Then `φ¹(x − extToClasses z) = 0`, and E6 gives
   `x = extToClasses z`.

This file is the **assembly** of that route: it imports the three sub-nodes E9a/E9b/E9c
(`e9_vanish_off_finite`, `e9_local_decomposition`, `e9_glue_phiAt`), the local realisation E7cΩ
(`local_phi_realization_in`), the injectivity E6Ω (`phi1_mono_sylow_in`) and the gluing map of E2
(`PT.exists_glue_extLoc`), and proves `pt_sha2_core` from them, together with the two trivial
helpers `phiAt_add_aux`/`phiAt_sub_aux` (additivity of the pairing in its `Extʳ` variable) and
`pts2_exists_orbit_transversal` (a choice of one place per `Gal(K/k)`-orbit).
-/

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

/-- **Additivity of the level pairing in its `Extʳ` variable.**  `phiAt x h` is the Yoneda product
of `h` with the image of `x`, hence additive in `x`. -/
theorem phiAt_add_aux {k K L : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k K] [IsGalois k K]
    {M : Rep Coeff (K ≃ₐ[k] K)} {r s : ℕ}
    (x x' : Abelian.Ext.{0} M (classesK k K) r)
    (h : extH (Rep.res (galRes k K L) M) s) :
    phiAt (k := k) (K := K) (L := L) (x + x') h =
      phiAt (k := k) (K := K) (L := L) x h + phiAt (k := k) (K := K) (L := L) x' h := by
  simp only [phiAt, levelPair, extRes, Abelian.Ext.mapExactFunctor_add,
    Abelian.Ext.add_comp, Abelian.Ext.comp_add]

/-- **Subtraction form of `phiAt_add_aux`.** -/
theorem phiAt_sub_aux {k K L : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k K] [IsGalois k K]
    {M : Rep Coeff (K ≃ₐ[k] K)} {r s : ℕ}
    (x y : Abelian.Ext.{0} M (classesK k K) r)
    (h : extH (Rep.res (galRes k K L) M) s) :
    phiAt (k := k) (K := K) (L := L) (x - y) h =
      phiAt (k := k) (K := K) (L := L) x h - phiAt (k := k) (K := K) (L := L) y h := by
  have h1 := phiAt_add_aux (k := k) (K := K) (L := L) (M := M) (x - y) y h
  rw [sub_add_cancel] at h1
  exact eq_sub_iff_add_eq.mpr h1.symm

/-- **A transversal of the `Gal(K/k)`-orbits of the places of `K`.**  Existence only: pick one
representative per orbit of the action of the finite group `Gal(K/k)` on the places of `K`. -/
theorem pts2_exists_orbit_transversal (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] :
    ∃ R : Set (NK.GlobalCFT.Place K), ∀ w : NK.GlobalCFT.Place K,
      ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1 := by
  classical
  let f : Quotient (MulAction.orbitRel (K ≃ₐ[k] K) (NK.GlobalCFT.Place K)) →
      NK.GlobalCFT.Place K := fun q => Classical.choose (Quotient.exists_rep q)
  have hspec : ∀ q, Quotient.mk _ (f q) = q :=
    fun q => Classical.choose_spec (Quotient.exists_rep q)
  refine ⟨Set.range f, fun w => ?_⟩
  refine ⟨⟨f (Quotient.mk _ w), Set.mem_range.mpr ⟨Quotient.mk _ w, rfl⟩⟩, ?_, ?_⟩
  · have h : MulAction.orbitRel (K ≃ₐ[k] K) (NK.GlobalCFT.Place K) (f (Quotient.mk _ w)) w :=
      Quotient.exact (hspec (Quotient.mk _ w))
    rw [MulAction.orbitRel_apply] at h
    obtain ⟨g, hg⟩ := h
    exact ⟨g, hg⟩
  · intro y hy
    obtain ⟨q, hq⟩ := Set.mem_range.mp y.2
    obtain ⟨σ, hσ⟩ := hy
    apply Subtype.ext
    have h1 : Quotient.mk (MulAction.orbitRel (K ≃ₐ[k] K) (NK.GlobalCFT.Place K)) (f q) =
        Quotient.mk (MulAction.orbitRel (K ≃ₐ[k] K) (NK.GlobalCFT.Place K)) w := by
      apply Quotient.sound
      exact MulAction.orbitRel_apply.mpr ⟨σ, by change σ • w = f q; rw [hσ, hq]⟩
    have h2 : q = Quotient.mk (MulAction.orbitRel (K ≃ₐ[k] K) (NK.GlobalCFT.Place K)) w :=
      (hspec q).symm.trans h1
    show y.1 = f (Quotient.mk (MulAction.orbitRel (K ≃ₐ[k] K) (NK.GlobalCFT.Place K)) w)
    rw [← hq, h2]


/-- **Galois closure of a finite place set.**  Every finite set `S` of places of `K` is contained in
a finite `Gal(K/k)`-stable set: its closure under the (finite) action of `Gal(K/k)`.  The assembly
of `pt_sha2_core` applies this to the output `S` of E9a, so that every consumer may assume the
`Gal(K/k)`-stability of the place set it is handed. -/
theorem exists_galois_stable_superset (k K : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (S : Finset (NK.GlobalCFT.Place K)) :
    ∃ T : Finset (NK.GlobalCFT.Place K), S ⊆ T ∧ ∀ v ∈ T, ∀ σ : K ≃ₐ[k] K, σ • v ∈ T := by
  classical
  refine ⟨S.biUnion (fun v => Finset.univ.image (fun σ : K ≃ₐ[k] K => σ • v)), ?_, ?_⟩
  · intro v hv
    exact Finset.mem_biUnion.mpr ⟨v, hv,
      Finset.mem_image.mpr ⟨1, Finset.mem_univ 1, one_smul _ v⟩⟩
  · intro v hv σ
    obtain ⟨w, hwS, hvw⟩ : ∃ w ∈ S, v ∈ Finset.univ.image (fun σ : K ≃ₐ[k] K => σ • w) :=
      Finset.mem_biUnion.mp hv
    obtain ⟨σ₀, -, hσ₀⟩ : ∃ σ₀ ∈ (Finset.univ : Finset (K ≃ₐ[k] K)), σ₀ • w = v :=
      Finset.mem_image.mp hvw
    exact Finset.mem_biUnion.mpr ⟨w, hwS,
      Finset.mem_image.mpr ⟨σ * σ₀, Finset.mem_univ _, by rw [mul_smul, hσ₀]⟩⟩

/-- **E9 (the Poitou–Tate core, `Ext` form).** If `μ_p ⊆ K` and `M` is a finite `p`-torsion
`Gal(K/k)`-module, a class `x ∈ Ext¹_G(M, C_K)` whose pairing with every everywhere-locally-trivial
`h ∈ H¹(Gal(K/k), M)` vanishes (in `H²(Gal(K/k), C_K)`) comes from the idèles.  Via the class
formation, this is `Ш²(k, M^∨(1)) ↪ Ш¹(k, M)^∨`. -/
theorem pt_sha2_core (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K]
    (ζ : K) (hζ : IsPrimitiveRoot ζ p)
    (M : Rep Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (x : Abelian.Ext M (classesK k K) 1)
    (hx : ∀ h : extH M 1, IsLocTrivial h → pairK x h = 0) :
    ∃ z : Abelian.Ext M (idelesK k K) 1, extToClasses z = x := by
  classical
  obtain ⟨S₀, hS₀arch, hS₀bad, hS₀van⟩ :=
    e9_vanish_off_finite p k K (AlgebraicClosure K) ζ hζ M hM x hx
  -- enlarge `S₀` to a `Gal(K/k)`-stable finite set; all the properties of E9a's output are
  -- monotone in the place set, so they transfer to the closure
  obtain ⟨S, hS₀S, hSstab⟩ := exists_galois_stable_superset k K S₀
  have hSarch : ∀ v : NK.GlobalCFT.Place K,
      (∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        v ≠ NK.GlobalCFT.Place.ofFinite q) → v ∈ S :=
    fun v hv => hS₀S (hS₀arch v hv)
  have hSbad : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      NK.GlobalCFT.Place.ofFinite q ∉ S →
        (p : NumberField.RingOfIntegers K) ∉ q.asIdeal ∧
        ∀ σ : K ≃ₐ[k] K, IsInertiaAt q σ → ∀ m : M, M.ρ σ m = m :=
    fun q hq => hS₀bad q (fun hmem => hq (hS₀S hmem))
  have hSvan : ∀ (L : IntermediateField K (AlgebraicClosure K)) [NumberField L]
      [FiniteDimensional k L] [IsGalois k L]
      (h : extH (Rep.res (galRes k K L) M) 1),
      (∀ w' : NK.GlobalCFT.Place L, (∃ v ∈ S, NK.GlobalCFT.Place.LiesOver w' v) →
        extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w') h = 0) →
      (∀ q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
        IsUnramifiedClassAt q' h) →
      phiAt (k := k) (K := K) (L := L) x h = 0 :=
    fun L _ _ _ h h1 h2 => hS₀van L h (fun w' hw' => h1 w' (by
      obtain ⟨v, hv, hl⟩ := hw'
      exact ⟨v, hS₀S hv, hl⟩)) h2
  obtain ⟨R, hR⟩ := pts2_exists_orbit_transversal k K
  obtain ⟨lam, hlam_p, hlam_compat, hlam_loc, hlam_unr, hlam_sum⟩ :=
    e9_local_decomposition (p := p) (k := k) (K := K) (Ω := AlgebraicClosure K) (ζ := ζ)
      (hζ := hζ) (M := M) (hM := hM) (R := R) (hR := hR) (x := x) (S := S)
      (hSarch := hSarch) (hSbad := hSbad) (hSstab := hSstab) (hS := hSvan)
  -- E7cΩ: each local family is realised by an idèle class supported on the orbit of `v`
  have hzv : ∀ v : R, ∃ z : Abelian.Ext M (idelesK k K) 1,
      (∀ u : NK.GlobalCFT.Place K, (∀ σ : K ≃ₐ[k] K, σ • v.1 ≠ u) → extLoc u z = 0) ∧
      (∀ (L : IntermediateField K (AlgebraicClosure K)) [NumberField L]
        [FiniteDimensional k L] [IsGalois k L]
        (h : extH (Rep.res (galRes k K L) M) 1),
        phiAt (k := k) (K := K) (L := L) (extToClasses z) h = lam v L h) ∧
      (∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        v.1 = NK.GlobalCFT.Place.ofFinite q →
        ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal) →
        (∀ σ : K ≃ₐ[k] K, IsInertiaAt q σ → ∀ m : M, M.ρ σ m = m) →
        (∀ (L : IntermediateField K (AlgebraicClosure K)) [NumberField L]
          [FiniteDimensional k L] [IsGalois k L]
          (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
          (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') v.1)
          (h : extH (Rep.res (galRes k K L) M) 1),
          IsUnramifiedClassAt q' h → lam v L h = 0) →
        IsUnramifiedExt v.1 (extLoc v.1 z)) := by
    intro v
    -- E7cΩ, from its two proved halves: `local_phi_realization_in_aux` (the constructive half,
    -- proved in `local_phi_realization_in.lean`) and the unramified half
    -- `Work.SSGRoute.isUnramifiedExt_of_levelPair_unramified` (proved in the module of that name).
    -- (The wrapper `Work.SSGRoute.local_phi_realization_in` in `local_phi_realization_in.lean` has
    -- exactly this body, but still carries the statement of the unramified half as an internal
    -- missing proof; the assembly below reuses the proved inputs directly so that this file is
    -- free of unfinished obligations.)
    obtain ⟨z, hz1, hz2⟩ :=
      local_phi_realization_in_aux (p := p) (k := k) (K := K) (Ω := AlgebraicClosure K)
        (ζ := ζ) (hζ := hζ) (M := M) (hM := hM) (w := v.1) (lam := fun L => lam v L)
        (hp := hlam_p v) (hcompat := hlam_compat v) (hloc := hlam_loc v)
    refine ⟨z, hz1, hz2, ?_⟩
    intro q hwq hpq hI hkill
    refine isUnramifiedExt_of_levelPair_unramified (p := p) (k := k) (K := K)
      (Ω := AlgebraicClosure K) (M := M) (hM := hM) (w := v.1) (q := q) (hwq := hwq)
      (hpq := hpq) (hI := hI) (y := extLoc v.1 z) ?_
    intro L hnf hfd hgal q' hq' h hunr
    have hphi : phiAt (k := k) (K := K) (L := L) (extToClasses z) h = 0 := by
      rw [hz2 L h]
      exact hkill L q' hq' h hunr
    rw [levelPair_extLoc_eq_push (k := k) (K := K) (L := ↥L) (M := M) z h v.1
      (NK.GlobalCFT.Place.ofFinite q') hq']
    refine extLoc_eq_zero_of_locTrivial_off_orbit k ↥L (NK.GlobalCFT.Place.ofFinite q') _ ?_ ?_
    · intro v' hv'
      rw [extLoc_levelPair_idleRepMap_eq (k := k) (K := K) (L := ↥L) M z h v']
      obtain ⟨u, hu⟩ := exists_place_under (L := K) (L' := ↥L) v'
      have hzu : extLoc (k := k) (K := K) u z = 0 := by
        refine hz1 u (fun σ hσ => ?_)
        have hlies : NK.GlobalCFT.Place.LiesOver v' (σ • v.1) := by rw [hσ]; exact hu
        obtain ⟨τ, hτ⟩ := SSG.exists_smul_eq_of_liesOver_under (k := k) (K := K)
          (Ω := AlgebraicClosure K) L v.1 (NK.GlobalCFT.Place.ofFinite q') hq' v' (σ • v.1)
          hlies σ rfl
        exact hv' τ hτ
      have hpush : extLoc (k := k) (K := ↥L) v'
          ((extRes (galRes k K ↥L) z).comp (Abelian.Ext.mk₀ (idleRepMap k K ↥L))
            (add_zero 1)) = 0 :=
        e9c_transport_zero z u v' hu hzu
      rw [hpush]
      exact yonedaPair_zero_right _
    · have hkey := phiAt_extToClasses_eq_idleRepMap (k := k) (K := K) (L := ↥L) M z h
      rw [hkey] at hphi
      simpa only [extToClasses] using hphi
  choose zv hsupp hpair hunr0 using hzv
  -- E2: glue the local components into a global idèle class
  obtain ⟨glue, hglue_comp, hglue_recon⟩ := PT.exists_glue_extLoc k K M 1 R hR
  have hfinS : {w : R | w.1 ∈ (S : Set (NK.GlobalCFT.Place K))}.Finite :=
    S.finite_toSet.preimage (f := fun w : R => w.1) (fun a _ b _ h => Subtype.ext h)
  -- E7cΩ's unramified clause: `zv v` is unramified at `v` for `v ∉ S`
  have hunr : ∀ v : R, v.1 ∉ S → IsUnramifiedExt v.1 (extLoc v.1 (zv v)) := by
    intro v hv
    have hlr := hlam_unr v
    have hc := hunr0 v
    have hex : ∃ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        v.1 = NK.GlobalCFT.Place.ofFinite q := by
      by_contra h
      exact hv (hSarch v.1 (fun q hq => h ⟨q, hq⟩))
    obtain ⟨q₀, hq₀⟩ := hex
    rw [hq₀] at hv hlr hc ⊢
    exact hc q₀ rfl (hSbad q₀ hv).1 (hSbad q₀ hv).2
      (fun L _ _ _ q' hq' h hunr' => hlr hv L q' hq' h hunr')
  have hfin : {w : R | ¬ IsUnramifiedExt (k := k) w.1
      (extLoc (k := k) w.1 (zv w))}.Finite :=
    hfinS.subset (fun w hw => by
      by_contra hwS
      exact hw (hunr w hwS))
  let z : Abelian.Ext M (idelesK k K) 1 := glue (fun w => extLoc w.1 (zv w))
  have hz : ∀ v : R, extLoc v.1 z = extLoc v.1 (zv v) :=
    fun v => hglue_comp (fun w => extLoc w.1 (zv w)) hfin v
  -- the corrected class has vanishing level values, so E6Ω forces it to vanish
  have hvanish : PhiOneVanishesIn (AlgebraicClosure K) (x - extToClasses z) := by
    intro L _ _ _ h
    have hxsum := (hlam_sum L h).2
    have hzsum := (e9_glue_phiAt p k K (AlgebraicClosure K) M hM R hR S hSarch
      (fun q hq => (hSbad q hq).2) zv hsupp hunr z hz L h).2
    rw [phiAt_sub_aux, hxsum, hzsum, sub_eq_zero]
    exact finsum_congr (fun v => (hpair v L h).symm)
  have h0 : x - extToClasses z = 0 :=
    phi1_mono_sylow_in p k K (AlgebraicClosure K) ζ hζ M hM (x - extToClasses z) hvanish
  exact ⟨z, (sub_eq_zero.mp h0).symm⟩

end Work.SSGRoute
