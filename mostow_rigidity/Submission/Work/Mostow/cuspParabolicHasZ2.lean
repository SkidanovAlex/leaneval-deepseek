import Mathlib
import Submission.Work.Mostow.cuspDefs
import Submission.Work.Mostow.Hyper
import Submission.Work.Mostow.BaryBase
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.properAction
import Submission.Work.Mostow.horSpec
import Submission.Work.Mostow.paraUniqueFixed
import Submission.Work.Mostow.cuspStabFlatAction
import Submission.Work.Mostow.horoActTrivId
import Submission.Work.Mostow.finite_translates_inter_compact

/-!
# Half A of cusp recognition: a parabolic element of a lattice has `HasZ2`

`Work.Mostow.cuspParabolicHasZ2`: in a lattice `Γ ≤ PO(n,1)` with `n ≥ 3`, every parabolic
element has the group-theoretic property `HasZ2` of `cuspDefs`: some positive power of it
centralises two independent commuting elements.

Let `γ ∈ Γ` be parabolic and `ξ` its (unique) fixed boundary point.  The stabiliser
`Γ_ξ = cuspStab Γ ξ` acts properly discontinuously and cocompactly on the level-`D` horosphere
of `ξ` (`hprop` of geometric finiteness, `properAction`), which is a Euclidean space of dimension
`flatDim ξ = n - 1 ≥ 2` (`cuspStabFlatAction`, `horSpec`).  Bieberbach's theorem (`hBb`) applied
to the resulting flat action `rhoHom` produces a finite-index subgroup `T ≤ Γ_ξ` acting by
translations whose vectors span `E (flatDim ξ)`; since the flat action is faithful
(`horoActTrivId`) `T` is free abelian in its translation vectors, and any two independent
translation vectors give two independent commuting elements centralising a power of `γ`.
-/

set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

namespace Work.Mostow

open LeanEval.Geometry.MostowRigidity Submission.Mostow MeasureTheory

noncomputable section

variable {n : ℕ}

/-! ## Inlined helpers (from `cuspCorr`, to keep the dependency footprint small) -/

lemma cph_busemann_sinh_smul {ξ : E n} (hξ : ξ ∈ Sph n) (t : ℝ) :
    busemann ξ (Real.sinh t • ξ) = -t := by
  have hξn : ‖ξ‖ = 1 := by
    simpa [Sph, Metric.mem_sphere, dist_eq_norm] using hξ
  have h1 : tpart (Real.sinh t • ξ) = Real.cosh t := by
    have hnorm : ‖Real.sinh t • ξ‖ ^ 2 = Real.sinh t ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, hξn, mul_one, sq_abs]
    rw [tpart, hnorm]
    have h2 : 1 + Real.sinh t ^ 2 = Real.cosh t ^ 2 := by rw [Real.cosh_sq]; ring
    rw [h2, Real.sqrt_sq (le_of_lt (Real.cosh_pos t))]
  have h3 : inner ℝ (Real.sinh t • ξ) ξ = Real.sinh t := by
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq, hξn]
    ring
  rw [busemann, h1, h3]
  rw [← Real.log_exp (-t)]
  congr 1
  rw [Real.cosh_eq, Real.sinh_eq]
  ring

lemma cph_busemann_surjective {ξ : E n} (hξ : ξ ∈ Sph n) (y : ℝ) :
    ∃ u : E n, busemann ξ u = y :=
  ⟨Real.sinh (-y) • ξ, by rw [cph_busemann_sinh_smul hξ]; ring⟩

lemma cph_cocycle_zero_of_horoball (hA : POActionProp n) (hI : HypIsometryProp n)
    (g : PO n 1) (ξ : E n) (hξ : ξ ∈ Sph n) (hg : bd g ξ = ξ) (t c : ℝ)
    (hhor : ∀ u : E n, g • u ∈ horoball ξ t ↔ u ∈ horoball ξ t)
    (hc : ∀ u : E n, busemann ξ (g • u) = busemann ξ u + c) : c = 0 := by
  by_contra hne
  have hkey : ∀ u : E n, (busemann ξ u < t - c) ↔ (busemann ξ u < t) := by
    intro u
    have h1 : busemann ξ u + c < t ↔ busemann ξ u < t := by
      have h2 := hhor u
      simpa only [horoball, Set.mem_ofPred_eq, hc u] using h2
    rw [← h1]
    constructor <;> intro h <;> linarith
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨u, hu⟩ := cph_busemann_surjective hξ (t - c / 2)
    have h1 : busemann ξ u < t - c := by rw [hu]; linarith
    have h2 : ¬ (busemann ξ u < t) := by rw [hu]; linarith
    exact h2 ((hkey u).mp h1)
  · obtain ⟨u, hu⟩ := cph_busemann_surjective hξ (t - c / 2)
    have h1 : busemann ξ u < t := by rw [hu]; linarith
    have h2 : ¬ (busemann ξ u < t - c) := by rw [hu]; linarith
    exact h2 ((hkey u).mpr h1)

lemma cph_cuspStab_levels (hA : POActionProp n) (hI : HypIsometryProp n)
    (hG : GeomFiniteProp n) (Γ : Subgroup (PO n 1)) (hΓ : HypLattice Γ)
    {ξ : E n} (hξ : ξ ∈ parFixSet Γ) {γ : Γ} (hγ : bd (γ : PO n 1) ξ = ξ) :
    ∀ u : E n, lev ξ ((γ : PO n 1) • u) = lev ξ u := by
  have hA' : POBasic n := POBasic.ofProp hA
  have hI' : HypIsoData n := HypIsoData.ofProp hI
  obtain ⟨hξS, δ, hδpar, hδfix⟩ := hξ
  obtain ⟨P, ht, hPsub, hPinv, hHeq, hPdisj, hKc, hCuspC, hPpar, hPall⟩ := hG Γ hΓ
  have hξP : ξ ∈ P := by
    obtain ⟨ξ₀, hξ₀P, hξ₀fix⟩ := hPall δ hδpar
    have h1 : ξ₀ = ξ :=
      paraUniqueFixed hA' hI' hδpar hξS hδfix (hPsub hξ₀P) hξ₀fix
    rwa [h1] at hξ₀P
  have hhor : ∀ u : E n, (γ : PO n 1) • u ∈ horoball ξ (ht ξ) ↔ u ∈ horoball ξ (ht ξ) := by
    intro u
    have h := hHeq γ ξ hξP u
    rwa [hγ] at h
  have hcoc : ∀ u : E n, busemann ξ ((γ : PO n 1) • u)
      = busemann ξ u + busemann ξ ((γ : PO n 1) • (0 : E n)) := by
    intro u
    have h := hI'.busemann_cocycle (γ : PO n 1) ξ u hξS
    rwa [hγ] at h
  have hc := cph_cocycle_zero_of_horoball hA hI (γ : PO n 1) ξ hξS hγ (ht ξ)
    (busemann ξ ((γ : PO n 1) • (0 : E n))) hhor hcoc
  intro u
  rw [lev_eq_exp hξS ((γ : PO n 1) • u), lev_eq_exp hξS u, hcoc u, hc, add_zero]


/-! ## The dimension of the flat space -/

lemma flatDim_eq (hn : 1 ≤ n) {ξ : E n} (hξ : ξ ∈ Sph n) : flatDim ξ = n - 1 := by
  have hξ0 : ξ ≠ 0 := by
    intro h
    have h1 : ‖ξ‖ = 1 := (mem_Sph_iff ξ).mp hξ
    rw [h, norm_zero] at h1
    exact one_ne_zero h1.symm
  have hdim : Module.finrank ℝ (ℝ ∙ ξ) + (n - 1) = Module.finrank ℝ (E n) := by
    rw [finrank_span_singleton hξ0, finrank_euclideanSpace_fin]
    omega
  have hmain : Module.finrank ℝ ((ℝ ∙ ξ)ᗮ) = n - 1 :=
    Submodule.finrank_add_finrank_orthogonal' hdim
  show Module.finrank ℝ ↥(horoSub ξ) = n - 1
  exact hmain

lemma flatDim_ge_two (hn : 3 ≤ n) {ξ : E n} (hξ : ξ ∈ Sph n) : 2 ≤ flatDim ξ := by
  rw [flatDim_eq (by omega) hξ]
  omega

/-! ## Continuity of the horospherical parametrisation -/

lemma continuous_hptOf (ξ : E n) (D : ℝ) : Continuous (fun y : E n => hptOf ξ y D) := by
  have h1 : Continuous fun y : E n => ‖y‖ ^ 2 := continuous_norm.pow 2
  have h2 : Continuous fun y : E n => (1 + D ^ 2 * ‖y‖ ^ 2) / (2 * D) - D / 2 :=
    ((continuous_const.add (continuous_const.mul h1)).div_const _).sub continuous_const
  have h3 : Continuous fun y : E n => ((1 + D ^ 2 * ‖y‖ ^ 2) / (2 * D) - D / 2) • ξ :=
    h2.smul continuous_const
  have h4 : Continuous fun y : E n => D • y := continuous_id.const_smul D
  have h5 : Continuous fun y : E n =>
      ((1 + D ^ 2 * ‖y‖ ^ 2) / (2 * D) - D / 2) • ξ + D • y := by
    apply Continuous.add
    · exact h3
    · exact h4
  exact h5

/-! ## Integer powers of a translation -/

lemma zpow_apply_add {m : ℕ} {G : Type*} [Group G] (ρ : G →* (E m ≃ᵢ E m)) (t : G) (w : E m)
    (hw : ∀ x : E m, ρ t x = x + w) :
    ∀ (k : ℤ) (x : E m), (ρ t ^ k) x = x + (k : ℝ) • w := by
  have hnat : ∀ (k : ℕ) (x : E m), (ρ t ^ (k : ℤ)) x = x + (k : ℝ) • w := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ j ih =>
      intro x
      rw [show ((j + 1 : ℕ) : ℤ) = (j : ℤ) + 1 from by omega, zpow_add_one,
        IsometryEquiv.mul_apply, ih, hw]
      push_cast
      rw [add_smul, one_smul]
      abel
  have hneg : ∀ (k : ℕ) (x : E m), (ρ t ^ (-(k : ℤ))) x = x + ((-(k : ℤ) : ℤ) : ℝ) • w := by
    intro k x
    have h2 : ∀ y : E m, (ρ t ^ (k : ℤ)) y = y + (k : ℝ) • w := fun y => hnat k y
    have h3 : (ρ t ^ (k : ℤ)) (x - (k : ℝ) • w) = x := by rw [h2]; abel
    have h4 : (ρ t ^ (k : ℤ)).symm x = x - (k : ℝ) • w := by
      conv_lhs => rw [← h3]
      rw [IsometryEquiv.symm_apply_apply]
    rw [zpow_neg]
    change (ρ t ^ (k : ℤ)).symm x = x + ((-(k : ℤ) : ℤ) : ℝ) • w
    rw [h4, show ((-(k : ℤ) : ℤ) : ℝ) = -(k : ℝ) from by push_cast; ring, neg_smul,
      sub_eq_add_neg]
  intro k x
  obtain ⟨k', rfl | rfl⟩ := Int.eq_nat_or_neg k
  · exact hnat k' x
  · exact hneg k' x

/-! ## The flat action `rhoHom`: cocompactness, properness, faithfulness -/

lemma rhoHom_cocompact {n : ℕ} (hA : POActionProp n) (hI : HypIsometryProp n) (hn1 : 1 ≤ n)
    {Γ : Subgroup (PO n 1)} {ξ : E n} (hξS : ξ ∈ Sph n) (D : ℝ) (hD : 0 < D)
    (hlev : ∀ (δ : Γ) (u : E n), bd (δ : PO n 1) ξ = ξ → lev ξ ((δ : PO n 1) • u) = lev ξ u)
    (hcoc : ∃ K : Set (E n), IsCompact K ∧ ∀ u : E n, lev ξ u = D →
      ∃ δ : Γ, bd (δ : PO n 1) ξ = ξ ∧ (δ : PO n 1) • u ∈ K) :
    ∃ K' : Set (E (flatDim ξ)), IsCompact K' ∧ ∀ x : E (flatDim ξ),
      ∃ g : cuspStab (POBasic.ofProp hA) Γ ξ hξS,
        rhoHom (hξ := hξS) hA hI hn1 D hD hlev g x ∈ K' := by
  obtain ⟨K, hKc, hK⟩ := hcoc
  refine ⟨flatPhi ξ '' (ycH hξS '' K), ?_, ?_⟩
  · exact (hKc.image (continuous_ycH hξS)).image (flatPhi ξ).continuous
  · intro x
    set y : ↥(horoSub ξ) := (flatPhi ξ).symm x with hy
    have hlevy : lev ξ (hptOf ξ (y : E n) D) = D :=
      (hptOf_level ξ hξS D hD (y : E n) (mem_horoSub_comm.mp y.2)).1
    obtain ⟨δ, hδbd, hδK⟩ := hK (hptOf ξ (y : E n) D) hlevy
    refine ⟨(⟨δ, hδbd⟩ : cuspStab (POBasic.ofProp hA) Γ ξ hξS), ?_⟩
    rw [rhoHom_apply]
    rw [← hy]
    refine ⟨ycH hξS ((δ : PO n 1) • hptOf ξ (y : E n) D),
      ⟨(δ : PO n 1) • hptOf ξ (y : E n) D, hδK, rfl⟩, ?_⟩
    rfl

lemma rhoHom_proper {n : ℕ} (hA : POActionProp n) (hI : HypIsometryProp n) (hn1 : 1 ≤ n)
    {Γ : Subgroup (PO n 1)} {ξ : E n} (hξS : ξ ∈ Sph n) (D : ℝ) (hD : 0 < D)
    (hlev : ∀ (δ : Γ) (u : E n), bd (δ : PO n 1) ξ = ξ → lev ξ ((δ : PO n 1) • u) = lev ξ u)
    (hdisc : IsDiscrete (Γ : Set (PO n 1)))
    (K : Set (E (flatDim ξ))) (hK : IsCompact K) :
    {g : cuspStab (POBasic.ofProp hA) Γ ξ hξS |
      ((rhoHom (hξ := hξS) hA hI hn1 D hD hlev g) '' K ∩ K).Nonempty}.Finite := by
  set K₁ : Set (E n) := (fun y : E n => hptOf ξ y D) ''
      ((fun z : ↥(horoSub ξ) => (z : E n)) '' ((flatPhi ξ).symm '' K)) with hK₁
  have hK₁c : IsCompact K₁ :=
    ((hK.image (flatPhi ξ).symm.continuous).image continuous_subtype_val).image
      (continuous_hptOf ξ D)
  have hfin := finite_translates_inter_compact n hA hI hdisc hK₁c hK₁c
  refine (hfin.preimage (f := fun g : cuspStab (POBasic.ofProp hA) Γ ξ hξS => (g : Γ))
    (fun a _ b _ hab => Subtype.ext hab)).subset ?_
  rintro g ⟨w, ⟨x, hxK, hxw⟩, hwK⟩
  set a : ↥(horoSub ξ) := (flatPhi ξ).symm x with ha
  set b : ↥(horoSub ξ) := (flatPhi ξ).symm w with hb
  have hfl : flatMap hξS D (((g : Γ)) : PO n 1) a = b := by
    have h2 : flatPhi ξ (flatMap hξS D (((g : Γ)) : PO n 1) a) = w := by
      rw [← hxw, rhoHom_apply]
    have h2' : flatPhi ξ (flatMap hξS D (((g : Γ)) : PO n 1) a) = flatPhi ξ b := by
      rw [h2, hb, IsometryEquiv.apply_symm_apply]
    exact (flatPhi ξ).injective h2'
  have hlevu : lev ξ ((((g : Γ)) : PO n 1) • hptOf ξ (a : E n) D) = D := by
    rw [hlev (g : Γ) _ g.2, (hptOf_level ξ hξS D hD (a : E n) (mem_horoSub_comm.mp a.2)).1]
  have hptw : (((g : Γ)) : PO n 1) • hptOf ξ (a : E n) D = hptOf ξ (b : E n) D := by
    rw [← hptOf_yc ξ hξS D hD _ hlevu]
    congr 1
    have h3 := congrArg (fun z : ↥(horoSub ξ) => (z : E n)) hfl
    simpa only [flatMap, ycH_coe] using h3
  refine ⟨hptOf ξ (b : E n) D, ⟨⟨hptOf ξ (a : E n) D, ?_, hptw⟩, ?_⟩⟩
  · exact ⟨(a : E n), ⟨(flatPhi ξ).symm x, ⟨x, hxK, rfl⟩, rfl⟩, rfl⟩
  · exact ⟨(b : E n), ⟨(flatPhi ξ).symm w, ⟨w, hwK, rfl⟩, rfl⟩, rfl⟩

lemma rhoHom_injective {n : ℕ} (hA : POActionProp n) (hI : HypIsometryProp n) (hn1 : 1 ≤ n)
    {Γ : Subgroup (PO n 1)} {ξ : E n} (hξS : ξ ∈ Sph n) (D : ℝ) (hD : 0 < D)
    (hlev : ∀ (δ : Γ) (u : E n), bd (δ : PO n 1) ξ = ξ → lev ξ ((δ : PO n 1) • u) = lev ξ u) :
    Function.Injective (rhoHom (hξ := hξS) hA hI hn1 D hD hlev) := by
  have heq1 : ∀ g : cuspStab (POBasic.ofProp hA) Γ ξ hξS,
      rhoHom (hξ := hξS) hA hI hn1 D hD hlev g = 1 → g = 1 := by
    intro g hg
    have htriv : ∀ u : E n, lev ξ u = D → (((g : Γ)) : PO n 1) • u = u := by
      intro u hu
      have h1 : rhoHom (hξ := hξS) hA hI hn1 D hD hlev g (flatPhi ξ (ycH hξS u))
          = flatPhi ξ (ycH hξS u) := by rw [hg]; rfl
      rw [rhoHom_apply] at h1
      simp only [IsometryEquiv.symm_apply_apply] at h1
      have h2 : flatMap hξS D (((g : Γ)) : PO n 1) (ycH hξS u) = ycH hξS u :=
        (flatPhi ξ).injective h1
      have h3 : yc ξ ((((g : Γ)) : PO n 1) • hptOf ξ (yc ξ u) D) = yc ξ u := by
        have h4 := congrArg (fun z : ↥(horoSub ξ) => (z : E n)) h2
        simpa only [flatMap, ycH_coe] using h4
      have hptu : hptOf ξ (yc ξ u) D = u := hptOf_yc ξ hξS D hD u hu
      have hlevgu : lev ξ ((((g : Γ)) : PO n 1) • u) = D := by rw [hlev (g : Γ) u g.2, hu]
      have hlevgu' : lev ξ ((((g : Γ)) : PO n 1) • hptOf ξ (yc ξ u) D) = D := by
        rw [hptu]; exact hlevgu
      calc (((g : Γ)) : PO n 1) • u
          = (((g : Γ)) : PO n 1) • hptOf ξ (yc ξ u) D := by rw [hptu]
        _ = hptOf ξ (yc ξ ((((g : Γ)) : PO n 1) • hptOf ξ (yc ξ u) D)) D :=
              (hptOf_yc ξ hξS D hD _ hlevgu').symm
        _ = hptOf ξ (yc ξ u) D := by rw [h3]
        _ = u := hptu
    have hg1 : (((g : Γ)) : PO n 1) = 1 :=
      horoActTrivId hA (((g : Γ)) : PO n 1) ξ hξS D hD g.2 (fun u => hlev (g : Γ) u g.2) htriv
    exact Subtype.ext (Subtype.ext (by simpa using hg1))
  intro a b hab
  have h1 : rhoHom (hξ := hξS) hA hI hn1 D hD hlev (a * b⁻¹) = 1 := by
    rw [map_mul, map_inv, hab, mul_inv_cancel]
  have h2 := heq1 (a * b⁻¹) h1
  rwa [mul_inv_eq_one] at h2

/-! ## Two independent vectors in a spanning set -/

lemma exists_pair_linearIndependent {m : ℕ} (hm : 2 ≤ m) {α : Type*} (f : α → E m) (S : Set α)
    (hspan : Submodule.span ℝ (f '' S) = ⊤) :
    ∃ a ∈ S, ∃ b ∈ S, LinearIndependent ℝ ![f a, f b] := by
  by_contra h
  push_neg at h
  have hle : ∃ x : E m, Submodule.span ℝ (f '' S) ≤ ℝ ∙ x := by
    by_cases hcase : ∃ a ∈ S, f a ≠ 0
    · obtain ⟨a, ha, ha0⟩ := hcase
      refine ⟨f a, ?_⟩
      apply Submodule.span_le.mpr
      rintro z ⟨b, hb, rfl⟩
      have hdep : ¬ LinearIndependent ℝ ![f a, f b] := h a ha b hb
      rw [LinearIndependent.pair_iff' ha0] at hdep
      push_neg at hdep
      obtain ⟨t, ht⟩ := hdep
      rw [← ht]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · push_neg at hcase
      refine ⟨0, ?_⟩
      apply Submodule.span_le.mpr
      rintro z ⟨b, hb, rfl⟩
      rw [hcase b hb]
      exact Submodule.zero_mem _
  obtain ⟨x, hx⟩ := hle
  have h1 : Module.finrank ℝ ↥(Submodule.span ℝ (f '' S)) ≤
      Module.finrank ℝ ↥(ℝ ∙ x) := Submodule.finrank_mono hx
  have h2 : Module.finrank ℝ ↥(ℝ ∙ x) ≤ 1 := by
    by_cases hx0 : x = 0
    · subst hx0
      rw [Submodule.span_singleton_eq_bot.mpr rfl, finrank_bot]
      omega
    · rw [finrank_span_singleton hx0]
  have h3 : Module.finrank ℝ ↥(Submodule.span ℝ (f '' S)) ≤ 1 := le_trans h1 h2
  have h4 : Module.finrank ℝ ↥(Submodule.span ℝ (f '' S)) = m := by
    rw [hspan, finrank_top, finrank_euclideanSpace_fin]
  omega

theorem cuspParabolicHasZ2 (n : ℕ) (hn : 3 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (hBb : ∀ m, BieberbachProp m) (hG : GeomFiniteProp n) (Γ : Subgroup (PO n 1))
    (hΓ : HypLattice Γ) (γ : Γ) (hpar : IsParabolic (γ : PO n 1)) : HasZ2 γ := by
  obtain ⟨P, ht, hPsub, hPinv, hHeq, hPdisj, hKc0, hCuspC, hPpar, hPall⟩ := hG Γ hΓ
  obtain ⟨ξ, hξP, hξfix⟩ := hPall γ hpar
  have hξS : ξ ∈ Sph n := hPsub hξP
  set D : ℝ := Real.exp (ht ξ) with hDdef
  have hD : 0 < D := Real.exp_pos _
  have hn1 : 1 ≤ n := by omega
  have hξpf : ξ ∈ parFixSet Γ := ⟨hξS, γ, hpar, hξfix⟩
  have hlev : ∀ (δ : Γ) (u : E n), bd (δ : PO n 1) ξ = ξ → lev ξ ((δ : PO n 1) • u) = lev ξ u :=
    fun δ u hδ => cph_cuspStab_levels hA hI hG Γ hΓ hξpf hδ u
  have hcoc : ∃ K : Set (E n), IsCompact K ∧ ∀ u : E n, lev ξ u = D →
      ∃ δ : Γ, bd (δ : PO n 1) ξ = ξ ∧ (δ : PO n 1) • u ∈ K := by
    obtain ⟨K, hKc, hK⟩ := hCuspC ξ hξP
    refine ⟨K, hKc, fun u hu => ?_⟩
    have hbus : busemann ξ u = ht ξ := by
      have h1 := lev_eq_exp hξS u
      rw [hu, hDdef] at h1
      exact (Real.exp_injective h1).symm
    obtain ⟨δ, hδbd, hδK⟩ := hK u hbus
    exact ⟨δ, hδbd, hδK⟩
  have hproper := rhoHom_proper hA hI hn1 hξS D hD hlev hΓ.1
  have hcocomp := rhoHom_cocompact hA hI hn1 hξS D hD hlev hcoc
  have hinj := rhoHom_injective hA hI hn1 hξS D hD hlev
  have hm2 : 2 ≤ flatDim ξ := flatDim_ge_two hn hξS
  obtain ⟨T, v, hTfin, hv, hspan⟩ :=
    hBb (flatDim ξ) (cuspStab (POBasic.ofProp hA) Γ ξ hξS)
      (rhoHom (hξ := hξS) hA hI hn1 D hD hlev) hproper hcocomp
  haveI : T.FiniteIndex := hTfin
  let T' : Subgroup (cuspStab (POBasic.ofProp hA) Γ ξ hξS) := T.normalCore
  haveI : T'.FiniteIndex := inferInstance
  haveI : T'.Normal := T.normalCore_normal
  have hT'le : T' ≤ T := T.normalCore_le
  have hspan' : Submodule.span ℝ (v '' (T' : Set (cuspStab (POBasic.ofProp hA) Γ ξ hξS))) = ⊤ := by
    rw [eq_top_iff, ← hspan]
    apply Submodule.span_le.mpr
    rintro z ⟨t, ht, rfl⟩
    have hN : (T'.index : ℝ) ≠ 0 := by
      exact_mod_cast (Subgroup.FiniteIndex.index_ne_zero (H := T'))
    have hmem : t ^ T'.index ∈ T' := Subgroup.pow_index_mem T' t
    have hz : v (t ^ T'.index) = (T'.index : ℝ) • v t := by
      have h1 := hv (t ^ T'.index) (hT'le hmem) 0
      have h2 : (rhoHom (hξ := hξS) hA hI hn1 D hD hlev) (t ^ T'.index) 0 = (T'.index : ℝ) • v t := by
        rw [map_pow]
        have hzw := zpow_apply_add (rhoHom (hξ := hξS) hA hI hn1 D hD hlev) t (v t) (hv t ht)
          (T'.index : ℤ) 0
        simpa using hzw
      rw [h1] at h2
      simpa using h2
    have hmemspan : v t ∈ Submodule.span ℝ (v '' (T' : Set _)) := by
      have hsub : (T'.index : ℝ) • v t ∈ Submodule.span ℝ (v '' (T' : Set _)) :=
        Submodule.subset_span ⟨t ^ T'.index, hmem, hz⟩
      have hv' : v t = (T'.index : ℝ)⁻¹ • ((T'.index : ℝ) • v t) := by
        rw [smul_smul, inv_mul_cancel₀ hN, one_smul]
      rw [hv']
      exact Submodule.smul_mem _ _ hsub
    simpa using hmemspan
  obtain ⟨a, haT', b, hbT', hab_ind⟩ :=
    exists_pair_linearIndependent hm2 v (T' : Set _) hspan'
  have haT : a ∈ T := hT'le haT'
  have hbT : b ∈ T := hT'le hbT'
  have hcommT : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s := by
    intro s hs t ht
    apply hinj
    rw [map_mul, map_mul]
    ext x
    rw [IsometryEquiv.mul_apply, IsometryEquiv.mul_apply, hv t ht, hv s hs, hv s hs, hv t ht]
    abel
  set γ₀ : cuspStab (POBasic.ofProp hA) Γ ξ hξS := ⟨γ, hξfix⟩ with hγ₀def
  have hk : γ₀ ^ T'.index ∈ T' := Subgroup.pow_index_mem T' γ₀
  have hkpos : 0 < T'.index := Nat.pos_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := T'))
  refine ⟨T'.index, hkpos, a.1, b.1, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    have h := congrArg (fun z : cuspStab (POBasic.ofProp hA) Γ ξ hξS => (z : Γ))
      (hcommT a haT (γ₀ ^ T'.index) (hT'le hk))
    simp only [Subgroup.coe_mul, Subgroup.coe_pow] at h
    rw [show ((γ₀ : cuspStab (POBasic.ofProp hA) Γ ξ hξS) : Γ) = γ from rfl] at h
    have h' := congrArg (fun z : Γ => (z : PO n 1)) h
    simp only [Subgroup.coe_mul, Subgroup.coe_pow] at h' ⊢
    exact h'
  · apply Subtype.ext
    have h := congrArg (fun z : cuspStab (POBasic.ofProp hA) Γ ξ hξS => (z : Γ))
      (hcommT b hbT (γ₀ ^ T'.index) (hT'le hk))
    simp only [Subgroup.coe_mul, Subgroup.coe_pow] at h
    rw [show ((γ₀ : cuspStab (POBasic.ofProp hA) Γ ξ hξS) : Γ) = γ from rfl] at h
    have h' := congrArg (fun z : Γ => (z : PO n 1)) h
    simp only [Subgroup.coe_mul, Subgroup.coe_pow] at h' ⊢
    exact h'
  · apply Subtype.ext
    have h := congrArg (fun z : cuspStab (POBasic.ofProp hA) Γ ξ hξS => (z : Γ))
      (hcommT a haT b hbT)
    simp only [Subgroup.coe_mul] at h
    have h' := congrArg (fun z : Γ => (z : PO n 1)) h
    simp only [Subgroup.coe_mul] at h' ⊢
    exact h'
  · intro i j hij
    have hG1 : a ^ i * b ^ j = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      have h := congrArg (fun z : Γ => (z : PO n 1)) hij
      simp only [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_one] at h ⊢
      exact h
    have hsum : (i : ℝ) • v a + (j : ℝ) • v b = 0 := by
      have h0 : (rhoHom (hξ := hξS) hA hI hn1 D hD hlev (a ^ i * b ^ j)) 0 = 0 := by
        rw [hG1, map_one]; rfl
      rw [map_mul, map_zpow, map_zpow, IsometryEquiv.mul_apply] at h0
      rw [zpow_apply_add (rhoHom (hξ := hξS) hA hI hn1 D hD hlev) b (v b) (hv b hbT) j 0] at h0
      rw [zpow_apply_add (rhoHom (hξ := hξS) hA hI hn1 D hD hlev) a (v a) (hv a haT) i] at h0
      simp only [zero_add] at h0
      rw [add_comm] at h0
      exact h0
    have hp := (LinearIndependent.pair_iff.mp hab_ind) (i : ℝ) (j : ℝ) hsum
    exact ⟨Int.cast_eq_zero.mp hp.1, Int.cast_eq_zero.mp hp.2⟩

end

end Work.Mostow
