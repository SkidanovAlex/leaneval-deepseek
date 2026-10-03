import Mathlib
import Submission.Work.ORHughesFree.Section6.Thm61Step
import Submission.Work.Section6.StepA
import Submission.Work.Section6.prop51Data_of_data
import Submission.Work.Section6.seriesEnvelope_exists
import Submission.Work.ORHughesFree.Section3.envelopeUniqueness_star
import Submission.Work.ORHughesFree.HughesFree.skewLaurentDecomp_exists2
import Submission.Work.ORHughesFree.HughesFree.exists_normal_cyclic_quotient
import Submission.Work.ORHughesFree.Section6.skewMonoidAlgebra_mapRingHom
import Submission.Work.ORHughesFree.Section6.HughesFreeEnv
import Submission.Work.ORHughesFree.Section6.ConjKN
import Submission.Work.ORHughesFree.Section6.StepAux
import Submission.Work.ORHughesFree.Section6.StarSkewL
import Submission.Work.ORHughesFree.Section6.exists_theta_gen
import Submission.Work.ORHughesFree.Section6.isNaturalExtension_pullback_theta
import Submission.Work.ORHughesFree.Section6.exists_ringEquiv_of_ranks_gen
import Submission.Work.ORHughesFree.Section6.exists_laurentEmbed
import Submission.Work.ORHughesFree.Section6.skewL_const_smul_eq
import Submission.Work.ORHughesFree.Section6.Phi_comp_ringEquiv
import Submission.Work.ORHughesFree.Section6.uUnit_pow_val
import Submission.Work.ORHughesFree.Section6.conjUN_phiNcod
import Submission.Work.ORHughesFree.Section6.toRingHom_skewLaurentT_pow
import Submission.Work.ORHughesFree.Section6.skewL_single_one_smul
import Submission.Work.Section6.skewLaurentSeries_mapRingHom
import Submission.Work.ORHughesFree.HughesFree.skewLaurentDecomp_exists2_iso_single
import Submission.Work.ORHughesFree.HughesFree.skewLaurentDecompAux
import Submission.Work.DivisionClosure.divisionClosure_map_subtype
import Submission.Work.DivisionClosure.divisionClosure_transport
import Submission.Work.DivisionClosure.divisionClosure_ringEquiv
import Submission.Work.Section6.prop51Data_of_data_strong
import Submission.Work.Section6.isUnit_of_isUnit_map_of_vonNeumannRegular
import Submission.Work.ORHughesFree.HughesFree.skewLaurentDecompAux
import Submission.Work.ORHughesFree.DivisionClosure.divisionClosure_map_of_ringEquiv
import Submission.Work.ORHughesFree.DivisionClosure.inverse_mem_divisionClosure
import Submission.Work.RankAPI.rk_eq_of_isUnit
import Submission.Work.RankAPI.isUnit_of_rk_oneByOne_eq_one

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.ORHughesFree.Section6

open Work.ORHughesFree

theorem thm61Step_nonempty {K : Type} [Field K] {G : Type} [Group G]
    [Work.ORHughesFree.LocallyIndicable G] {U : Type} [Ring U]
    [StarRing U] [Work.ORHughesFree.IsStarRegular U]
    (hpos : Work.ORHughesFree.IsPositiveDefiniteStarRegular U)
    (φ : MonoidAlgebra K G →+* U) (rkU : Work.ORHughesFree.SylvesterRank U)
    (hfaith : rkU.IsFaithful) (hφ : Work.ORHughesFree.IsEpic φ)
    (hstar : Work.ORHughesFree.StarCompatible φ)
    (hHF : Work.ORHughesFree.IsHughesFreeEnv φ)
    (H : Subgroup G) (hfg : H.FG) (hne : H ≠ ⊥) :
    Nonempty (Work.ORHughesFree.Thm61Step K G U φ H) := by
  classical
  -- ## Step 0: the group-theoretic input
  obtain ⟨N, hNnorm, t, hNne, htop, htinf₀⟩ :=
    Work.ORHughesFree.HughesFree.exists_normal_cyclic_quotient H hfg hne
  have htinf : ∀ k : ℤ, t ^ k ∈ N → k = 0 := by
    intro k hk
    by_contra hk0
    exact htinf₀ k hk0 hk
  have htN : ∀ (k : ℤ) (n : N), t ^ k * (n : H) * t ^ (-k) ∈ N := normal_conj_zpow hNnorm
  have hdecomp : ∀ h : H, ∃ (n : N) (k : ℤ), h = (n : H) * t ^ k := decomp_of_sup hNnorm htop
  have hstar_t : star ((φ.comp (inducedMapRing (K := K) H)) (MonoidAlgebra.single t (1 : K))) =
      (φ.comp (inducedMapRing (K := K) H)) (MonoidAlgebra.single t⁻¹ (1 : K)) := by
    have h := hstar t
    simpa [Work.ORHughesFree.StarCompatible, inducedMapRing,
      MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single] using h
  -- ## Step A: the ambient ring `P = P^{U_N}_{ω,τ}`
  letI : MulSemiringAction (Multiplicative ℤ) (Work.Section6.UNty φ H N) :=
    Work.Section6.tauAction φ H N hNnorm t hstar_t
  have hstarτ : ∀ (m : Multiplicative ℤ) (x : Work.Section6.UNty φ H N),
      star (m • x) = m • star x :=
    Work.Section6.tauAction_star φ H N hNnorm t hstar_t
  have hτ : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) (Work.Section6.UNty φ H N)),
      (Work.Section6.rkN φ H N rkU).rk n m (A.map (fun a => (Multiplicative.ofAdd (1 : ℤ)) • a)) =
        (Work.Section6.rkN φ H N rkU).rk n m A :=
    Work.Section6.rkN_tauCompatible φ H N hNnorm t hstar_t rkU
  obtain ⟨rkE, hE, ⟨env⟩⟩ := Work.Section6.stepA_envelope_exists hpos φ H N hNnorm t hstar_t
    rkU hfaith hstarτ hτ
  haveI : NaturalExtension.StarAction (Work.Section6.UNty φ H N) := ⟨hstarτ⟩
  letI : Ring env.P := env.ringP
  letI : StarRing env.P := env.starP
  letI : IsStarRegular env.P := env.isStarRegularP
  letI : IsPositiveDefiniteStarRegular env.P := env.positiveDefiniteP
  -- ## Step C.1: the evaluation `θ : U_N[t^{±1};τ] → U`
  obtain ⟨θ, hθ_single, hθ_star, hθ_const, hθ_onePlus⟩ :=
    exists_theta_gen (A := Work.Section6.UNty φ H N)
      (Subring.subtype (Work.Section6.UNsub φ H N)) (fun x => rfl)
      (Work.Section6.uUnit φ H t) (Work.Section6.uUnit_star φ H t hstar_t)
      (fun k x => tauAction_smulU φ H N hNnorm t hstar_t k x)
  have hθnat : IsNaturalExtension (Work.Section6.rkN φ H N rkU)
      (SylvesterRank.pullback θ rkU) :=
    isNaturalExtension_pullback_theta φ H hfg hne N hNnorm t hstar_t rkU hfaith hHF hdecomp htinf
      θ hθ_single
  -- ## Step C.2: the ranks of `θ` and `f_ω` agree
  have hrank : ∀ (n m : ℕ)
      (A : Matrix (Fin n) (Fin m) (SkewMonoidAlgebra (Work.Section6.UNty φ H N)
        (Multiplicative ℤ))),
      rkU.rk n m (A.map θ) = env.rkP.rk n m (A.map env.fω) := by
    intro n m A
    have h1 : (SylvesterRank.pullback θ rkU).rk n m A = rkE.rk n m A :=
      NaturalExtension.naturalExtension_unique (Work.Section6.rkN φ H N rkU) hτ hθnat hE n m A
    have h2 : (SylvesterRank.pullback θ rkU).rk n m A = rkU.rk n m (A.map θ) := rfl
    rw [← h2, h1, env.rank_compat]
  -- ## Step C.3: the isomorphism of the two `∗`-regular envelopes
  obtain ⟨e', he'_theta, he'_rank⟩ :=
    exists_ringEquiv_of_ranks_gen (A := Work.Section6.UNty φ H N) (U := U) (P := env.P)
      rkU hfaith env.rkP env.faithfulP θ hθ_star env.fω env.fω_star hrank
  -- ## Step B: the source twist, the decomposition `K[H] ≅ K[N][t^{±1};τ]`, and `ρ`, `φP`
  letI : MulSemiringAction (Multiplicative ℤ) (MonoidAlgebra K N) := conjAction (K := K) htN
  haveI hscN : SMulCommClass (Multiplicative ℤ) K (MonoidAlgebra K N) :=
    conjAction_smulCommClass (K := K) htN
  obtain ⟨d, hd_iso, hd_symm⟩ := exists_skewLaurentDecomp (K := K) hNnorm htN hdecomp htinf₀
  -- the equivariance of `φ_N` for the two twists
  have hcomm : ∀ (k : ℤ) (x : MonoidAlgebra K N),
      Work.Section6.phiNcod φ H N ((Multiplicative.ofAdd k) • x) =
        (Multiplicative.ofAdd k) • (Work.Section6.phiNcod φ H N x) := by
    intro k x
    have h1 : Work.ORHughesFree.HughesFree.inclN K H N ((Multiplicative.ofAdd k) • x) =
        MonoidAlgebra.single (t ^ k) (1 : K) * Work.ORHughesFree.HughesFree.inclN K H N x *
          MonoidAlgebra.single (t ^ (-k)) (1 : K) :=
      Work.ORHughesFree.HughesFree.inclN_smul (K := K) htN (conjAction_hact (K := K) htN) k x
    apply Subtype.ext
    rw [Work.Section6.phiNcod_apply,
      tauAction_smulU φ H N hNnorm t hstar_t k (Work.Section6.phiNcod φ H N x),
      uUnit_pow_val φ H t k, uUnit_pow_val φ H t (-k), Work.Section6.phiNcod_apply]
    rw [show Work.Section6.phiN φ H N ((Multiplicative.ofAdd k) • x) =
      (φ.comp (inducedMapRing (K := K) H))
        (Work.ORHughesFree.HughesFree.inclN K H N ((Multiplicative.ofAdd k) • x)) from rfl]
    rw [h1, map_mul, map_mul]
    rw [show Work.Section6.phiN φ H N x =
      (φ.comp (inducedMapRing (K := K) H))
        (Work.ORHughesFree.HughesFree.inclN K H N x) from rfl]
  obtain ⟨ψ, hψ_single, hψ_inj⟩ :=
    skewMonoidAlgebra_mapRingHom (Work.Section6.phiNcod φ H N) hcomm
  let ρ : MonoidAlgebra K H →+* SkewMonoidAlgebra (Work.Section6.UNty φ H N)
      (Multiplicative ℤ) :=
    ψ.comp d.iso.symm.toRingHom
  let φP : MonoidAlgebra K H →+* env.P := env.fω.comp ρ
  -- the monomial formulae for `d.iso.symm`
  have hd_symm_inclN : ∀ b : MonoidAlgebra K N, d.iso.symm (d.inclN b) =
      SkewMonoidAlgebra.single (1 : Multiplicative ℤ) b := by
    intro b
    have h1 : Work.ORHughesFree.HughesFree.genT K t (1 : Multiplicative ℤ) = 1 := by
      rw [show (1 : Multiplicative ℤ) = Multiplicative.ofAdd 0 from rfl,
        Work.ORHughesFree.HughesFree.genT_ofAdd]
      simp [MonoidAlgebra.one_def]
    have h2 : d.iso (SkewMonoidAlgebra.single (1 : Multiplicative ℤ) b) = d.inclN b := by
      rw [hd_iso 1 b, h1, mul_one]
    rw [← h2, RingEquiv.symm_apply_apply]
  have hd_symm_t : d.iso.symm (MonoidAlgebra.single t (1 : K)) =
      SkewMonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) (1 : MonoidAlgebra K N) := by
    have h2 : d.iso (SkewMonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ))
        (1 : MonoidAlgebra K N)) = MonoidAlgebra.single t (1 : K) := by
      rw [hd_iso (Multiplicative.ofAdd 1) 1, Work.ORHughesFree.HughesFree.genT_ofAdd]
      simp
    rw [← h2, RingEquiv.symm_apply_apply]
  have hP_N : ∀ b : MonoidAlgebra K N, φP (d.inclN b) =
      env.fω (SkewMonoidAlgebra.single (1 : Multiplicative ℤ)
        (Work.Section6.phiNcod φ H N b)) := by
    intro b
    show env.fω (ψ (d.iso.symm (d.inclN b))) = _
    rw [hd_symm_inclN b, hψ_single]
  have hP_t : φP (MonoidAlgebra.single t (1 : K)) =
      env.Ψ ((skewLaurentSeriesT (Work.Section6.UNty φ H N) :
        (SkewLaurentSeries (Work.Section6.UNty φ H N))ˣ) :
        SkewLaurentSeries (Work.Section6.UNty φ H N)) := by
    show env.fω (ψ (d.iso.symm (MonoidAlgebra.single t (1 : K)))) = _
    rw [hd_symm_t, hψ_single]
    have h1 : (Work.Section6.phiNcod φ H N) (1 : MonoidAlgebra K N) = 1 := map_one _
    rw [h1]
    rw [← env.Ψ_extends (SkewMonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ))
      (1 : Work.Section6.UNty φ H N))]
    congr 1
    rw [toRingHom_skewLaurentT_pow (A := Work.Section6.UNty φ H N) 1, zpow_one]
  -- ## Step C.4: `θ ∘ ρ = φ_H`
  have theta_psi : ∀ p : SkewMonoidAlgebra (MonoidAlgebra K N) (Multiplicative ℤ),
      θ (ψ p) = (φ.comp (inducedMapRing (K := K) H)) (d.iso p) := by
    intro p
    induction p using SkewMonoidAlgebra.induction_on with
    | zero => simp
    | single m a =>
        obtain ⟨k, rfl⟩ := Multiplicative.ofAdd.surjective m
        rw [hψ_single, hθ_single, hd_iso, map_mul, Work.ORHughesFree.HughesFree.genT_ofAdd,
          uUnit_pow_val φ H t k]
        rw [show (φ.comp (inducedMapRing (K := K) H)) (d.inclN a) =
          (Work.Section6.phiNcod φ H N a : U) from rfl]
        rfl
    | add p q ihp ihq =>
        simp only [map_add, ihp, ihq]
  have theta_rho : ∀ x : MonoidAlgebra K H,
      θ (ρ x) = (φ.comp (inducedMapRing (K := K) H)) x := by
    intro x
    show θ (ψ (d.iso.symm x)) = _
    rw [theta_psi, RingEquiv.apply_symm_apply]
  -- ## Step B.3: the division closure `D_{N,U_N} ⊆ U_N` and its image `DN ⊆ P`
  let DN0 : Subring (Work.Section6.UNty φ H N) :=
    divisionClosure (Set.range (Work.Section6.phiNcod φ H N))
  let fc : Work.Section6.UNty φ H N →+* env.P :=
    env.fω.comp (SkewMonoidAlgebra.singleOneRingHom (G := Multiplicative ℤ))
  let DN : Subring env.P := DN0.map fc
  have hfc : Function.Injective fc := by
    intro x y hxy
    have h1 : SkewMonoidAlgebra.single (1 : Multiplicative ℤ) x =
        SkewMonoidAlgebra.single (1 : Multiplicative ℤ) y := env.fω_injective hxy
    have h2 := congrArg (fun z : SkewMonoidAlgebra (Work.Section6.UNty φ H N)
      (Multiplicative ℤ) => z.coeff (1 : Multiplicative ℤ)) h1
    simpa using h2
  -- the range of `φ_N` is invariant under the twist, hence so is `DN0`
  have hrange : (Work.Section6.conjUN φ H N hNnorm t hstar_t) ''
      Set.range (Work.Section6.phiNcod φ H N) = Set.range (Work.Section6.phiNcod φ H N) := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro y ⟨x, ⟨b, rfl⟩, rfl⟩
      exact ⟨(Multiplicative.ofAdd (1 : ℤ)) • b,
        (conjUN_phiNcod φ H N hNnorm t htN hstar_t b).symm⟩
    · rintro y ⟨b, rfl⟩
      refine ⟨Work.Section6.phiNcod φ H N ((Multiplicative.ofAdd (-1 : ℤ)) • b), ⟨_, rfl⟩, ?_⟩
      rw [conjUN_phiNcod φ H N hNnorm t htN hstar_t ((Multiplicative.ofAdd (-1 : ℤ)) • b)]
      congr 1
      rw [smul_smul, ← ofAdd_add, show (1 : ℤ) + (-1) = 0 from by norm_num, ofAdd_zero,
        one_smul]
  have hDN0 : ∀ (k : ℤ) (x : Work.Section6.UNty φ H N), x ∈ DN0 →
      (Multiplicative.ofAdd k) • x ∈ DN0 := by
    have hmap : (DN0).map (Work.Section6.conjUN φ H N hNnorm t hstar_t).toRingHom = DN0 := by
      rw [DivisionClosure.divisionClosure_map_of_ringEquiv, hrange]
    have hmap' : (DN0).map (Work.Section6.conjUN φ H N hNnorm t hstar_t).symm.toRingHom = DN0 := by
      have h := congrArg (fun D => D.map (Work.Section6.conjUN φ H N hNnorm t hstar_t).symm.toRingHom) hmap
      rw [Subring.map_map] at h
      have h2 : (Work.Section6.conjUN φ H N hNnorm t hstar_t).symm.toRingHom.comp
          (Work.Section6.conjUN φ H N hNnorm t hstar_t).toRingHom = RingHom.id _ := by
        ext y
        simp
      rw [h2, Subring.map_id] at h
      exact h.symm
    have hbase : ∀ y : Work.Section6.UNty φ H N, y ∈ DN0 →
        ((Work.Section6.conjUN φ H N hNnorm t hstar_t) ^ (0 : ℤ)) y ∈ DN0 := by
      intro y hy
      simpa using hy
    have hsucc : ∀ (i : ℕ), (∀ y : Work.Section6.UNty φ H N, y ∈ DN0 →
          ((Work.Section6.conjUN φ H N hNnorm t hstar_t) ^ (i : ℤ)) y ∈ DN0) →
        ∀ y : Work.Section6.UNty φ H N, y ∈ DN0 →
          ((Work.Section6.conjUN φ H N hNnorm t hstar_t) ^ ((i : ℤ) + 1)) y ∈ DN0 := by
      intro i ih y hy
      rw [zpow_add_one]
      show ((Work.Section6.conjUN φ H N hNnorm t hstar_t) ^ (i : ℤ))
        ((Work.Section6.conjUN φ H N hNnorm t hstar_t) y) ∈ DN0
      refine ih _ ?_
      rw [← hmap]
      exact Subring.mem_map.mpr ⟨y, hy, rfl⟩
    have hpred : ∀ (i : ℕ), (∀ y : Work.Section6.UNty φ H N, y ∈ DN0 →
          ((Work.Section6.conjUN φ H N hNnorm t hstar_t) ^ (-(i : ℤ))) y ∈ DN0) →
        ∀ y : Work.Section6.UNty φ H N, y ∈ DN0 →
          ((Work.Section6.conjUN φ H N hNnorm t hstar_t) ^ (-(i : ℤ) - 1)) y ∈ DN0 := by
      intro i ih y hy
      rw [zpow_sub_one]
      show ((Work.Section6.conjUN φ H N hNnorm t hstar_t) ^ (-(i : ℤ)))
        ((Work.Section6.conjUN φ H N hNnorm t hstar_t)⁻¹ y) ∈ DN0
      refine ih _ ?_
      rw [← hmap']
      exact Subring.mem_map.mpr ⟨y, hy, rfl⟩
    have hpow : ∀ (k : ℤ) (y : Work.Section6.UNty φ H N),
        y ∈ DN0 → ((Work.Section6.conjUN φ H N hNnorm t hstar_t) ^ k) y ∈ DN0 := by
      intro k
      refine Int.induction_on k ?_ ?_ ?_
      · exact hbase
      · intro i ih
        exact hsucc i ih
      · intro i ih
        exact hpred i ih
    intro k x hx
    rw [Work.Section6.tauAction_smul_eq φ H N hNnorm t hstar_t k x]
    exact hpow k x hx
  -- the series embedding `D_{N,P}((t;τ)) ⊆ P` and its twist
  have hlam : ((Units.map env.Ψ.toMonoidHom (skewLaurentSeriesT (Work.Section6.UNty φ H N)) :
      env.Pˣ) : env.P) = env.fω (SkewMonoidAlgebra.single (Multiplicative.ofAdd 1)
        (1 : Work.Section6.UNty φ H N)) := by
    show env.Ψ ((skewLaurentSeriesT (Work.Section6.UNty φ H N) :
      (SkewLaurentSeries (Work.Section6.UNty φ H N))ˣ) :
        SkewLaurentSeries (Work.Section6.UNty φ H N)) = _
    rw [← env.Ψ_extends (SkewMonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ))
      (1 : Work.Section6.UNty φ H N))]
    congr 1
    rw [toRingHom_skewLaurentT_pow (A := Work.Section6.UNty φ H N) 1, zpow_one]
  obtain ⟨instDN, L, hL_inj, hL_coeff, hL_T⟩ :=
    exists_laurentEmbed env.fω env.Ψ env.Ψ_extends env.Ψ_injective hfc
      (Units.map env.Ψ.toMonoidHom (skewLaurentSeriesT (Work.Section6.UNty φ H N))) hlam
      (fun k x => skewL_const_smul_eq env.fω env.Ψ env.Ψ_extends
        (Units.map env.Ψ.toMonoidHom (skewLaurentSeriesT (Work.Section6.UNty φ H N))) hlam k x)
      DN0 hDN0
  letI : MulSemiringAction (Multiplicative ℤ) ↥DN := instDN
  -- ## Step C.5: the isomorphism `D_{H,U} ≃+* D_{H,P}`
  let U1 : StarSubring U := starRegularClosure (starSubringClosure (Set.range θ))
  let U2 : StarSubring env.P := starRegularClosure (starSubringClosure (Set.range env.fω))
  have hrange1 : Set.range (φ.comp (inducedMapRing (K := K) H)) ⊆ (U1 : Set U) := by
    rintro y ⟨x, rfl⟩
    rw [← theta_rho x]
    exact subset_starRegularClosure _ (subset_starSubringClosure _ (Set.mem_range_self (ρ x)))
  let φ1 : MonoidAlgebra K H →+* ↥U1 :=
    (φ.comp (inducedMapRing (K := K) H)).codRestrict U1.toSubring (fun x => hrange1 ⟨x, rfl⟩)
  have hrange2 : Set.range φP ⊆ (U2 : Set env.P) := by
    rintro y ⟨x, rfl⟩
    exact subset_starRegularClosure _ (subset_starSubringClosure _ (Set.mem_range_self (ρ x)))
  let φ2 : MonoidAlgebra K H →+* ↥U2 := φP.codRestrict U2.toSubring (fun x => hrange2 ⟨x, rfl⟩)
  haveI : VonNeumannRegularRing ↥U1.toSubring := inferInstanceAs (VonNeumannRegularRing ↥U1)
  haveI : VonNeumannRegularRing ↥U2.toSubring := inferInstanceAs (VonNeumannRegularRing ↥U2)
  have hDHU : (divisionClosure (Set.range (φ.comp (inducedMapRing (K := K) H))) : Subring U) =
      (divisionClosure (Set.range φ1) : Subring ↥U1).map (Subring.subtype U1.toSubring) := by
    rw [← Work.DivisionClosure.divisionClosure_map_subtype (Set.range φ1)]
    congr 1
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨φ1 x, ⟨x, rfl⟩, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨x, rfl⟩ := hz
      exact ⟨x, rfl⟩
  have hDHP : (divisionClosure (Set.range φP) : Subring env.P) =
      (divisionClosure (Set.range φ2) : Subring ↥U2).map (Subring.subtype U2.toSubring) := by
    rw [← Work.DivisionClosure.divisionClosure_map_subtype (Set.range φ2)]
    congr 1
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨φ2 x, ⟨x, rfl⟩, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨x, rfl⟩ := hz
      exact ⟨x, rfl⟩
  have he' : ∀ x : MonoidAlgebra K H, e' (φ1 x) = φ2 x := by
    intro x
    apply Subtype.ext
    show ((e' (φ1 x) : ↥U2) : env.P) = φP x
    have h1 : (φ1 x : ↥U1) = ⟨θ (ρ x),
        subset_starRegularClosure _ (subset_starSubringClosure _ (Set.mem_range_self _))⟩ :=
      Subtype.ext (theta_rho x).symm
    rw [h1, he'_theta]
    rfl
  have hrange_e' : e' '' Set.range φ1 = Set.range φ2 := by
    ext y
    constructor
    · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, (he' x).symm⟩
    · rintro ⟨x, rfl⟩
      exact ⟨φ1 x, ⟨x, rfl⟩, he' x⟩
  have hmap : (divisionClosure (Set.range φ1) : Subring ↥U1).map e'.toRingHom =
      (divisionClosure (Set.range φ2) : Subring ↥U2) := by
    rw [DivisionClosure.divisionClosure_map_of_ringEquiv, hrange_e']
  obtain ⟨ê₁, hê₁⟩ := Work.DivisionClosure.divisionClosure_ringEquiv φ1 φ2 e' he'
  obtain ⟨ê₂, hê₂⟩ := Work.DivisionClosure.divisionClosure_transport (V := U1.toSubring) φ1
  obtain ⟨ê₃, hê₃⟩ := Work.DivisionClosure.divisionClosure_transport (V := U2.toSubring) φ2
  have hê₂' : ∀ x : MonoidAlgebra K H,
      ê₂ ⟨(φ.comp (inducedMapRing (K := K) H)) x, subset_divisionClosure _ ⟨x, rfl⟩⟩ =
        ⟨φ1 x, subset_divisionClosure _ ⟨x, rfl⟩⟩ := fun x => hê₂ x
  have hê₃' : ∀ x : MonoidAlgebra K H,
      ê₃ ⟨φP x, subset_divisionClosure _ ⟨x, rfl⟩⟩ =
        ⟨φ2 x, subset_divisionClosure _ ⟨x, rfl⟩⟩ := fun x => hê₃ x
  let e0 : ↥(divisionClosure (Set.range (φ.comp (inducedMapRing (K := K) H)))) ≃+*
      ↥(divisionClosure (Set.range φP)) := ê₂.trans (ê₁.trans ê₃.symm)
  have he0 : ∀ x : MonoidAlgebra K H,
      e0 ⟨(φ.comp (inducedMapRing (K := K) H)) x, subset_divisionClosure _ ⟨x, rfl⟩⟩ =
        ⟨φP x, subset_divisionClosure _ ⟨x, rfl⟩⟩ := by
    intro x
    show (ê₃.symm (ê₁ (ê₂ ⟨(φ.comp (inducedMapRing (K := K) H)) x, _⟩))) = _
    rw [hê₂' x, hê₁ x, ← hê₃' x]
    exact RingEquiv.symm_apply_apply ê₃ _
  -- ## Step B.4: the `Prop51Data` of [JZLA20, Proposition 5.1]
  haveI hU_nontriv : Nontrivial U := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    have h10 : (1 : Matrix (Fin 1) (Fin 1) U) = 0 := by
      ext i j
      exact Subsingleton.elim _ _
    have h : rkU.rk 1 1 (1 : Matrix (Fin 1) (Fin 1) U) = rkU.rk 1 1 0 := by rw [h10]
    rw [rkU.rk_one, rkU.rk_zero] at h
    exact one_ne_zero h
  haveI hP_nontriv : Nontrivial env.P := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    have h10 : (1 : Matrix (Fin 1) (Fin 1) env.P) = 0 := by
      ext i j
      exact Subsingleton.elim _ _
    have h : env.rkP.rk 1 1 (1 : Matrix (Fin 1) (Fin 1) env.P) = env.rkP.rk 1 1 0 := by rw [h10]
    rw [env.rkP.rk_one, env.rkP.rk_zero] at h
    exact one_ne_zero h
  haveI hUN_nontriv : Nontrivial (Work.Section6.UNty φ H N) :=
    ⟨⟨1, 0, fun h => (one_ne_zero : (1 : U) ≠ 0) (by
      have h1 : ((1 : Work.Section6.UNty φ H N) : U) = ((0 : Work.Section6.UNty φ H N) : U) :=
        congrArg Subtype.val h
      simpa using h1)⟩⟩
  haveI hDN0_nontriv : Nontrivial ↥DN0 :=
    ⟨⟨1, 0, fun h => (one_ne_zero : (1 : U) ≠ 0) (by
      have h1 : ((1 : ↥DN0) : Work.Section6.UNty φ H N) =
          ((0 : ↥DN0) : Work.Section6.UNty φ H N) := congrArg Subtype.val h
      simpa using h1)⟩⟩
  haveI hNontrivDN : Nontrivial ↥DN :=
    ⟨⟨1, 0, fun h => (one_ne_zero : (1 : env.P) ≠ 0) (by
      have h1 : ((1 : ↥DN) : env.P) = ((0 : ↥DN) : env.P) := congrArg Subtype.val h
      simpa using h1)⟩⟩
  have hDN_inv : ∀ y ∈ DN, IsUnit y → ∃ z ∈ DN, y * z = 1 ∧ z * y = 1 := by
    intro y hy hu
    obtain ⟨x, hx, rfl⟩ := Subring.mem_map.mp hy
    have hxu : IsUnit x := by
      have hscalar : ∀ a : env.P, Work.ORHughesFree.oneByOne a = Matrix.scalar (Fin 1) a := by
        intro a
        ext i j
        obtain rfl : i = j := Subsingleton.elim i j
        simp [Work.ORHughesFree.oneByOne, Matrix.scalar_apply]
      have hu' : IsUnit (Work.ORHughesFree.oneByOne (fc x)) := by
        rw [hscalar]
        exact hu.map (Matrix.scalar (Fin 1))
      have h1 : env.rkP.rk 1 1 (Work.ORHughesFree.oneByOne (fc x)) = 1 := by
        simpa using Work.RankAPI.rk_eq_of_isUnit env.rkP
          (Work.ORHughesFree.oneByOne (fc x)) hu'
      have h2 : rkE.rk 1 1 (Work.ORHughesFree.oneByOne
          (SkewMonoidAlgebra.single (1 : Multiplicative ℤ) x)) = 1 := by
        rw [env.rank_compat 1 1 (Work.ORHughesFree.oneByOne
          (SkewMonoidAlgebra.single (1 : Multiplicative ℤ) x))]
        exact h1
      have h3 : (Work.Section6.rkN φ H N rkU).rk 1 1 (Work.ORHughesFree.oneByOne x) = 1 := by
        rw [← hE.1 1 1 (Work.ORHughesFree.oneByOne x)]
        exact h2
      haveI : VonNeumannRegularRing ↥(Work.Section6.UNsub φ H N) :=
        inferInstanceAs (VonNeumannRegularRing (Work.Section6.UNty φ H N))
      exact Work.Section6.isUnit_of_isUnit_map_of_vonNeumannRegular
        (Subring.subtype (Work.Section6.UNsub φ H N)) Subtype.val_injective
        (Work.RankAPI.isUnit_of_rk_oneByOne_eq_one rkU hfaith h3)
    obtain ⟨u, hu⟩ := hxu
    refine ⟨fc ↑u⁻¹, Subring.mem_map.mpr ⟨↑u⁻¹,
      Work.ORHughesFree.DivisionClosure.inverse_mem_divisionClosure (hu ▸ hx)
        (by simp) (by simp), rfl⟩, ?_, ?_⟩
    · rw [← hu, ← map_mul, Units.mul_inv, map_one]
    · rw [← hu, ← map_mul, Units.inv_mul, map_one]
  have hleDN : DN ≤ divisionClosure (Set.range φP) := by
    have hmono : fc '' Set.range (Work.Section6.phiNcod φ H N) ⊆ Set.range φP := by
      rintro y ⟨b, hb, rfl⟩
      obtain ⟨b', rfl⟩ := hb
      exact ⟨d.inclN b', hP_N b'⟩
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subring.mem_map.mp hy
    have h1 : fc x ∈ (DN0).map fc := Subring.mem_map.mpr ⟨x, hx, rfl⟩
    have h2 : (DN0).map fc ≤ divisionClosure (fc '' Set.range (Work.Section6.phiNcod φ H N)) :=
      Work.ORHughesFree.DivisionClosure.divisionClosure_map_le fc _
    exact Work.ORHughesFree.DivisionClosure.divisionClosure_mono hmono (h2 h1)
  have hNmem : ∀ b : MonoidAlgebra K N,
      φP (MonoidAlgebra.mapDomainRingHom K N.subtype b) ∈ DN := by
    intro b
    have h1 : MonoidAlgebra.mapDomainRingHom K N.subtype b = d.inclN b := rfl
    rw [h1, hP_N b]
    exact Subring.mem_map.mpr ⟨Work.Section6.phiNcod φ H N b,
      subset_divisionClosure _ ⟨b, rfl⟩, rfl⟩
  have ht : φP (MonoidAlgebra.single t (1 : K)) =
      L (skewLaurentSeriesT ↥DN : SkewLaurentSeries ↥DN) := by
    rw [hP_t, hL_T, Units.coe_map]
    rfl
  obtain ⟨data, hdata_N, hdata_t, hdata_DH, hdata_Phi⟩ :=
    Work.Section6.prop51Data_of_data_strong (K := K) N t hNontrivDN hDN_inv L hL_inj hL_coeff φP hleDN hNmem
      ht hdecomp htN
  have hPhi : (e0.toRingHom.comp (Work.ORHughesFree.Phi (φ.comp (inducedMapRing (K := K) H)))) =
      Work.ORHughesFree.Phi φP :=
    Phi_comp_ringEquiv (φ.comp (inducedMapRing (K := K) H)) φP e0 he0
  refine ⟨{ N := N
            N_normal := hNnorm
            N_ne_top := hNne
            t := t
            decomp := hdecomp
            P := env.P
            ringP := env.ringP
            DN := DN
            smulDN := instDN
            data := data
            data_N := hdata_N
            data_t := hdata_t
            e := e0.trans (RingEquiv.subringCongr hdata_DH).symm
            e_Phi := fun β => ?_ }⟩
  apply Subtype.ext
  show ((e0 ⟨Work.ORHughesFree.Phi (φ.comp (inducedMapRing (K := K) H)) β, _⟩ :
    ↥(divisionClosure (Set.range φP))) : env.P) = (data.Φ β : env.P)
  rw [hdata_Phi]
  exact congrArg (fun f : RatU (Kˣ × H) →+* ↥(divisionClosure (Set.range φP)) =>
    ((f β : ↥(divisionClosure (Set.range φP))) : env.P)) hPhi

end Work.ORHughesFree.Section6
