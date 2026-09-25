import Mathlib
import Submission.Work.Tower.Shafarevich.Defs
import Submission.Work.CFT.Kummer.Hypotheses
import Submission.Work.CFT.KochTransfer.Defs
import Submission.Work.CFT.KochTransfer.auxFun_d12_eq
import Submission.Work.CFT.KochTransfer.finrank_invariantHoms_le

/-!
# Koch's transfer lemma

Let `π : G →* Q` be a surjective group homomorphism with kernel `N`, and let `σ : Q → G` be a
section of `π`.  The *inflation* map `inf : H²(Q, 𝔽_p) → H²(G, 𝔽_p)` has kernel of `𝔽_p`-dimension
at most the minimal number of generators of `N`; consequently, if `G` is finite and `N` is the
normal closure of `k` elements, then

`dim H²(G ⧸ N, 𝔽_p) ≤ dim H²(G, 𝔽_p) + k`.

This is the "Koch transfer" estimate, the group-theoretic input of Shafarevich's tower argument.

The proof is the transgression of the low-degree exact sequence of the extension
`1 → N → G → Q → 1`: for `t ∈ H¹(N, 𝔽_p)^Q = Hom(N, 𝔽_p)^G` the transgression
`tg t ∈ H²(Q, 𝔽_p)` is the class of the `2`-cocycle `(x, y) ↦ -t (σ x σ y σ (xy)⁻¹)`
(`Work.CFT.KochTransfer.candidate`), and the kernel of the inflation is contained in the image of
`tg`, which has dimension at most the number of generators of `N`.
-/

namespace Work.CFT.KochTransfer

open groupCohomology
open CategoryTheory

set_option linter.style.haveILetI false

/-- Finiteness of `H^n(G, 𝔽_p)` for a finite group `G`. -/
theorem module_finite_groupCohomology (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G]
    (n : ℕ) :
    Module.Finite (ZMod p) ↥(groupCohomology (Rep.trivial (ZMod p) G (ZMod p)) n) := by
  let A := Rep.trivial (ZMod p) G (ZMod p)
  have hC : groupCohomology (Rep.trivial (ZMod p) G (ZMod p)) n =
      (inhomogeneousCochains A).homology n := rfl
  rw [hC]
  set S := (inhomogeneousCochains A).sc n with hS
  have hH : Module.Finite (ZMod p) ↥(S.moduleCatLeftHomologyData.H) := by
    have hX : Module.Finite (ZMod p) ↥S.X₂ := by
      show Module.Finite (ZMod p) ↥(ModuleCat.of (ZMod p) ((Fin n → G) → ↥A))
      infer_instance
    have hNoeth : IsNoetherian (ZMod p) ↥S.X₂ :=
      isNoetherian_of_isNoetherianRing_of_finite (ZMod p) _
    have hker : Module.Finite (ZMod p) ↥(LinearMap.ker S.g.hom) :=
      Module.Finite.of_fg (IsNoetherian.noetherian _)
    show Module.Finite (ZMod p) (S.g.hom.ker ⧸ S.moduleCatToCycles.range)
    exact Module.Finite.quotient (ZMod p) S.moduleCatToCycles.range
  exact Module.Finite.equiv (CategoryTheory.ShortComplex.moduleCatHomologyIso S).symm.toLinearEquiv

lemma candidate_mem_cocycles (p : ℕ) {G : Type} [Group G] {Q : Type} [Group Q]
    (π : G →* Q) (σ : Q → G) (hσ : ∀ q, π (σ q) = q) (hπ : Function.Surjective π)
    (t : invariantHoms p π) :
    candidate p π σ hσ t ∈ cocycles₂ (Rep.trivial (ZMod p) Q (ZMod p)) := by
  rw [← precompFun_mem_cocycles_iff π hπ (candidate p π σ hσ t), ← auxFun_d12_eq π σ hσ t]
  exact coboundaries₂_le_cocycles₂ _ ⟨auxFun p π σ hσ t, rfl⟩

/-- The `𝔽_p`-linear map `f ↦ ((x,y) ↦ -f (σ x σ y σ (xy)⁻¹))`, the transgression candidate
as a function of the invariant hom. -/
noncomputable def candidateLinFun (p : ℕ) {G : Type} [Group G] {Q : Type} [Group Q]
    (π : G →* Q) (σ : Q → G) (hσ : ∀ q, π (σ q) = q) :
    (π.ker → ZMod p) →ₗ[ZMod p] (Q × Q → ZMod p) where
  toFun f := fun x => - f ⟨σ x.1 * σ x.2 * (σ (x.1 * x.2))⁻¹, by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, hσ, hσ, hσ]
    simp⟩
  map_add' f g := by
    funext x
    simp only [Pi.add_apply]
    abel
  map_smul' r f := by
    funext x
    simp only [Pi.smul_apply]
    exact (smul_neg r (f ⟨σ x.1 * σ x.2 * (σ (x.1 * x.2))⁻¹, by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, hσ, hσ, hσ]
      simp⟩)).symm

lemma candidateLinFun_apply (p : ℕ) {G : Type} [Group G] {Q : Type} [Group Q]
    (π : G →* Q) (σ : Q → G) (hσ : ∀ q, π (σ q) = q)
    (f : π.ker → ZMod p) (x y : Q) :
    candidateLinFun p π σ hσ f (x, y) = - f ⟨σ x * σ y * (σ (x * y))⁻¹, by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, hσ, hσ, hσ]
      simp⟩ := rfl

lemma candidate_eq_candidateLinFun (p : ℕ) {G : Type} [Group G] {Q : Type} [Group Q]
    (π : G →* Q) (σ : Q → G) (hσ : ∀ q, π (σ q) = q) (t : invariantHoms p π) :
    candidate p π σ hσ t = candidateLinFun p π σ hσ ((t : π.ker → ZMod p)) := rfl

/-- The transgression candidate, as a linear map into the `2`-cocycles. -/
noncomputable def candidateLin (p : ℕ) {G : Type} [Group G] {Q : Type} [Group Q]
    (π : G →* Q) (σ : Q → G) (hσ : ∀ q, π (σ q) = q) (hπ : Function.Surjective π) :
    invariantHoms p π →ₗ[ZMod p] cocycles₂ (Rep.trivial (ZMod p) Q (ZMod p)) :=
  ((candidateLinFun p π σ hσ).comp (invariantHoms p π).subtype).codRestrict _
    (fun t => by
      rw [LinearMap.comp_apply, Submodule.subtype_apply,
        ← candidate_eq_candidateLinFun p π σ hσ t]
      exact candidate_mem_cocycles p π σ hσ hπ t)

@[simp] lemma candidateLin_apply (p : ℕ) {G : Type} [Group G] {Q : Type} [Group Q]
    (π : G →* Q) (σ : Q → G) (hσ : ∀ q, π (σ q) = q) (hπ : Function.Surjective π)
    (t : invariantHoms p π) :
    ((candidateLin p π σ hσ hπ t : cocycles₂ (Rep.trivial (ZMod p) Q (ZMod p))) :
        Q × Q → ZMod p) = candidate p π σ hσ t := by
  funext x
  obtain ⟨a, b⟩ := x
  rw [candidateLin, candidate_eq_candidateLinFun]
  exact candidateLinFun_apply p π σ hσ (↑t) a b

/-- The transgression `H¹(ker π, 𝔽_p)^Q → H²(Q, 𝔽_p)` of the extension
`1 → ker π → G → Q → 1`, computed with the section `σ`. -/
noncomputable def transgression (p : ℕ) {G : Type} [Group G] {Q : Type} [Group Q]
    (π : G →* Q) (σ : Q → G) (hσ : ∀ q, π (σ q) = q) (hπ : Function.Surjective π) :
    invariantHoms p π →ₗ[ZMod p] H2 (Rep.trivial (ZMod p) Q (ZMod p)) :=
  (H2π (Rep.trivial (ZMod p) Q (ZMod p))).hom.comp (candidateLin p π σ hσ hπ)

lemma transgression_apply (p : ℕ) {G : Type} [Group G] {Q : Type} [Group Q]
    (π : G →* Q) (σ : Q → G) (hσ : ∀ q, π (σ q) = q) (hπ : Function.Surjective π)
    (t : invariantHoms p π) :
    transgression p π σ hσ hπ t =
      (H2π (Rep.trivial (ZMod p) Q (ZMod p))).hom (candidateLin p π σ hσ hπ t) := rfl

/-- **The kernel of the inflation is contained in the image of the transgression.**

Given a `2`-cocycle `c` on `Q` whose inflation `precompFun π c` is a coboundary on `G`, say
`precompFun π c = d₁₂ b`, the function `n ↦ b n - c (1,1)` on `ker π` is an additive,
conjugation-invariant hom `t`, and `c` differs from the candidate cocycle of `t` by a coboundary
(namely `d₁₂` of `q ↦ -b (σ q⁻¹) + c (q, q⁻¹) + c (1,1)`).  Hence the class of `c` lies in the
range of the transgression. -/
lemma ker_infl_le_range_transgression (p : ℕ) {G : Type} [Group G] {Q : Type} [Group Q]
    (π : G →* Q) (σ : Q → G) (hσ : ∀ q, π (σ q) = q) (hπ : Function.Surjective π) :
    LinearMap.ker (infl π) ≤ LinearMap.range (transgression p π σ hσ hπ) := by
  intro x hx
  rw [LinearMap.mem_ker] at hx
  obtain ⟨c, hc⟩ := (ModuleCat.epi_iff_surjective
    (H2π (Rep.trivial (ZMod p) Q (ZMod p)))).mp inferInstance x
  -- the inflation of `c` is a coboundary on `G`
  have hΦ : precompFun π (⇑c) ∈ coboundaries₂ (Rep.trivial (ZMod p) G (ZMod p)) := by
    have h0 : (H2π (Rep.trivial (ZMod p) G (ZMod p))).hom (precompCocycle π c) = 0 := by
      rw [← infl_H2π π c, hc, hx]
    have h1 := (H2π_eq_zero_iff (precompCocycle π c)).mp h0
    simpa [precompCocycle_apply] using h1
  obtain ⟨b, hb⟩ := LinearMap.mem_range.mp hΦ
  set cf : Q × Q → ZMod p := ⇑c with hcf
  set c11 : ZMod p := cf (1, 1) with hc11
  have hb_pt : ∀ u v : G, b v - b (u * v) + b u = cf (π u, π v) := by
    intro u v
    have h := congr_fun hb (u, v)
    simpa [d₁₂_hom_apply, precompFun_apply] using h
  have hone_fst : ∀ q : Q, cf (1, q) = c11 := by
    intro q; rw [hc11]; exact cocycles₂_map_one_fst c q
  have hone_snd : ∀ q : Q, cf (q, 1) = c11 := by
    intro q; rw [hc11]; simpa using cocycles₂_map_one_snd c q
  -- `b` restricted to `ker π` is additive and conjugation-invariant
  have hadd : ∀ u v : π.ker, b ((u * v : π.ker) : G) = b (u : G) + b (v : G) - c11 := by
    intro u v
    have h := hb_pt (u : G) (v : G)
    rw [MonoidHom.mem_ker.mp u.2, MonoidHom.mem_ker.mp v.2, hone_fst] at h
    linear_combination -h
  have hinv : ∀ (a : G) (u : π.ker), b (a * (u : G) * a⁻¹) = b (u : G) := by
    intro a u
    have h1 := hb_pt a (u : G)
    rw [MonoidHom.mem_ker.mp u.2, hone_snd] at h1
    have h2 := hb_pt (a * (u : G) * a⁻¹) a
    rw [show π (a * (u : G) * a⁻¹) = 1 by
      rw [map_mul, map_mul, map_inv, MonoidHom.mem_ker.mp u.2, mul_one, mul_inv_cancel],
      hone_fst] at h2
    have h2' : b (a * (u : G) * a⁻¹) = c11 + b (a * (u : G)) - b a := by
      have h2'' : b a - b ((a * (u : G) * a⁻¹) * a) + b (a * (u : G) * a⁻¹) = c11 := h2
      rw [show (a * (u : G) * a⁻¹) * a = a * (u : G) by group] at h2''
      linear_combination h2''
    have h1' : b (a * (u : G)) = b (u : G) + b a - c11 := by linear_combination -h1
    rw [h2', h1']
    ring
  have ht'mem : (fun n : π.ker => b (n : G) - c11) ∈ invariantHoms p π := by
    rw [invariantHoms_mem_iff]
    refine ⟨?_, ?_⟩
    · intro u v
      show b ((u * v : π.ker) : G) - c11 = (b (u : G) - c11) + (b (v : G) - c11)
      rw [hadd u v]; abel
    · intro a u
      show b ((conjKer π a u : π.ker) : G) - c11 = b (u : G) - c11
      rw [conjKer_coe, hinv a u]
  let t' : invariantHoms p π := ⟨fun n : π.ker => b (n : G) - c11, ht'mem⟩
  -- the correction term
  let Dbar : Q → ZMod p := fun q => -b ((σ q)⁻¹) + cf (q, q⁻¹) + c11
  let Dfun : G → ZMod p := fun u => Dbar (π u)
  have hD : ∀ u : G, b u - auxFun p π σ hσ t' u = Dfun u := by
    intro u
    have h2 := hb_pt u ((σ (π u))⁻¹)
    have h2' : b (u * (σ (π u))⁻¹) = b u + b ((σ (π u))⁻¹) - cf (π u, (π u)⁻¹) := by
      rw [show π ((σ (π u))⁻¹) = (π u)⁻¹ by rw [map_inv, hσ]] at h2
      linear_combination -h2
    have haux : auxFun p π σ hσ t' u = b (u * (σ (π u))⁻¹) - c11 := rfl
    rw [haux, h2']
    simp only [Dfun, Dbar]
    ring_nf
  have hstep1 : precompFun π (cf - candidate p π σ hσ t') =
      (d₁₂ (Rep.trivial (ZMod p) G (ZMod p))).hom (b - auxFun p π σ hσ t') := by
    have hd12 : (d₁₂ (Rep.trivial (ZMod p) G (ZMod p))).hom (auxFun p π σ hσ t') =
        precompFun π (candidate p π σ hσ t') :=
      auxFun_d12_eq (p := p) (π := π) (σ := σ) (hσ := hσ) (t := t')
    rw [map_sub, map_sub, hb, hd12]
  have hstep2 : (d₁₂ (Rep.trivial (ZMod p) G (ZMod p))).hom (b - auxFun p π σ hσ t') =
      (d₁₂ (Rep.trivial (ZMod p) G (ZMod p))).hom Dfun := by
    congr 1
    funext u
    exact hD u
  have hstep3 : (d₁₂ (Rep.trivial (ZMod p) G (ZMod p))).hom Dfun =
      precompFun π ((d₁₂ (Rep.trivial (ZMod p) Q (ZMod p))).hom Dbar) := by
    funext y
    obtain ⟨u, v⟩ := y
    simp only [d₁₂_hom_apply, precompFun_apply, Dfun, Dbar, map_mul,
      Representation.trivial_apply]
  have hmain : precompFun π (cf - candidate p π σ hσ t') =
      precompFun π ((d₁₂ (Rep.trivial (ZMod p) Q (ZMod p))).hom Dbar) :=
    hstep1.trans (hstep2.trans hstep3)
  have hcf_eq : cf - candidate p π σ hσ t' =
      (d₁₂ (Rep.trivial (ZMod p) Q (ZMod p))).hom Dbar :=
    precompFun_injective π hπ hmain
  have hmem : candidate p π σ hσ t' - cf ∈
      coboundaries₂ (Rep.trivial (ZMod p) Q (ZMod p)) := by
    have hcob : (d₁₂ (Rep.trivial (ZMod p) Q (ZMod p))).hom Dbar ∈
        coboundaries₂ (Rep.trivial (ZMod p) Q (ZMod p)) :=
      LinearMap.mem_range.mpr ⟨Dbar, rfl⟩
    have hneg : -(cf - candidate p π σ hσ t') ∈
        coboundaries₂ (Rep.trivial (ZMod p) Q (ZMod p)) := by
      rw [hcf_eq]; exact Submodule.neg_mem _ hcob
    rwa [neg_sub] at hneg
  refine ⟨t', ?_⟩
  rw [transgression_apply, ← hc]
  refine (H2π_eq_iff (candidateLin p π σ hσ hπ t') c).mpr ?_
  simpa [hcf] using hmem

/-- **The dimension bound for the kernel of the inflation.**

If `G` is finite, `π : G →* Q` is surjective with kernel the normal closure of `k` elements, then
`dim H²(Q, 𝔽_p) ≤ dim H²(G, 𝔽_p) + k`. -/
theorem infl_finrank_le (p : ℕ) [Fact p.Prime] {G : Type} [Group G] [Fintype G]
    {Q : Type} [Group Q] [Fintype Q] (π : G →* Q) (σ : Q → G) (hσ : ∀ q, π (σ q) = q)
    (hπ : Function.Surjective π) (k : ℕ) (g : Fin k → G)
    (hg : π.ker = Subgroup.normalClosure (Set.range g)) :
    Module.finrank (ZMod p) (H2 (Rep.trivial (ZMod p) Q (ZMod p))) ≤
      Module.finrank (ZMod p) (H2 (Rep.trivial (ZMod p) G (ZMod p))) + k := by
  haveI : Module.Finite (ZMod p) (H2 (Rep.trivial (ZMod p) Q (ZMod p))) :=
    module_finite_groupCohomology p Q 2
  haveI : Module.Finite (ZMod p) (H2 (Rep.trivial (ZMod p) G (ZMod p))) :=
    module_finite_groupCohomology p G 2
  have hker : Module.finrank (ZMod p) ↥(LinearMap.ker (infl π)) ≤ k :=
    le_trans (Submodule.finrank_mono (ker_infl_le_range_transgression p π σ hσ hπ))
      (le_trans (LinearMap.finrank_range_le (transgression p π σ hσ hπ))
        (finrank_invariantHoms_le (p := p) π k g hg))
  have hrange : Module.finrank (ZMod p) ↥(LinearMap.range (infl π)) ≤
      Module.finrank (ZMod p) (H2 (Rep.trivial (ZMod p) G (ZMod p))) :=
    Submodule.finrank_le _
  have hsum := LinearMap.finrank_range_add_finrank_ker (infl (p := p) π)
  omega

/-- **Koch's transfer lemma.**  If `G` is a finite group, `p` a prime and `N` the normal closure
of `k` elements of `G`, then

`dim_{𝔽_p} H²(G ⧸ N, 𝔽_p) ≤ dim_{𝔽_p} H²(G, 𝔽_p) + k`

for the second cohomology with trivial `𝔽_p` coefficients.  This is the group-theoretic input of
Shafarevich's tower argument: killing `k` elements of `G` adds at most `k` relations. -/
theorem kochTransfer (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G] (k : ℕ)
    (g : Fin k → G) :
    Module.finrank (ZMod p)
        (Work.Tower.Shafarevich.H2Fp p (G ⧸ Subgroup.normalClosure (Set.range g)))
      ≤ Module.finrank (ZMod p) (Work.Tower.Shafarevich.H2Fp p G) + k := by
  haveI : (Subgroup.normalClosure (Set.range g)).Normal := Subgroup.normalClosure_normal
  haveI : Fintype (G ⧸ Subgroup.normalClosure (Set.range g)) := Fintype.ofFinite _
  exact infl_finrank_le p (QuotientGroup.mk' (Subgroup.normalClosure (Set.range g)))
    Quotient.out (fun q => Quotient.out_eq' q) (QuotientGroup.mk'_surjective _) k g
    (QuotientGroup.ker_mk' _)

end Work.CFT.KochTransfer
