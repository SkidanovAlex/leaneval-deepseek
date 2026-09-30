import Mathlib
import Submission.Work.BW.BWGradedBase
import Submission.Work.BW.primLen_ne_top
import Submission.Work.BW.cut_rank_one
import Submission.Work.BW.rank_one_cut_bound
import Submission.Work.BW.smul_mem_map_of_mul_smul_mem
import Submission.Work.BW.mem_map_prime_of_mul_mem_map
import Submission.Work.BW.isFiniteLength_quot_span_of_torsion
import Submission.Work.BW.hmin_cut_artinian

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

namespace Work.BW.RB

/-! ## Auxiliary lemmas (local copies, self-contained) -/

/-- `locLenAt` is antitone in the ideal: a smaller ideal gives a longer local length. -/
theorem rb_locLenAt_le_of_le {R : Type*} [CommRing R] (q : Ideal R) (hq : q.IsPrime)
    {K L : Ideal R} (h : K ≤ L) : locLenAt q hq L ≤ locLenAt q hq K := by
  letI := hq
  have hmap : K.map (algebraMap R (Localization.AtPrime q)) ≤
      L.map (algebraMap R (Localization.AtPrime q)) := Ideal.map_mono h
  exact Module.length_le_of_surjective (Submodule.factor hmap) (Submodule.factor_surjective _)

/-- Length additivity for ideals `K ≤ L` of a ring `R`: `ℓ(R ⧸ K) = ℓ(R ⧸ L) + ℓ(L ⧸ K)`, the last
term written as the image of `L` in `R ⧸ K`. -/
theorem rb_length_quotient_add_map {R : Type*} [CommRing R] {K L : Ideal R} (h : K ≤ L) :
    Module.length R (R ⧸ K) =
      Module.length R (R ⧸ L)
        + Module.length R (Submodule.map (Submodule.mkQ (K : Submodule R R))
            (L : Submodule R R)) := by
  let f : (Submodule.map (Submodule.mkQ (K : Submodule R R)) (L : Submodule R R)) →ₗ[R] (R ⧸ K) :=
    (Submodule.map (Submodule.mkQ (K : Submodule R R)) (L : Submodule R R)).subtype
  let g : (R ⧸ K) →ₗ[R] (R ⧸ L) :=
    Submodule.mapQ (K : Submodule R R) (L : Submodule R R) LinearMap.id (by simpa using h)
  have hf : Function.Injective f := Submodule.subtype_injective _
  have hker : g.ker = Submodule.map (Submodule.mkQ (K : Submodule R R)) (L : Submodule R R) := by
    rw [Submodule.ker_mapQ]
    simp
  have hex : Function.Exact f g := by
    rw [LinearMap.exact_iff, hker, Submodule.range_subtype]
  have hg : Function.Surjective g := by
    intro x
    obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective (L : Submodule R R) x
    exact ⟨Submodule.Quotient.mk b, by rw [Submodule.mapQ_apply]; rfl⟩
  have hlen := Module.length_eq_add_of_exact f g hf hg hex
  rw [hlen, add_comm]

/-- The image in `J ⧸ I` of `(I + (x)) ∩ J` is contained in the `B`-span of the class of `x`. -/
theorem rb_map_sub_comap_le_span {B : Type*} [CommRing B] {I J : Ideal B} {x : B} (hxJ : x ∈ J) :
    Submodule.map (Submodule.mkQ (Submodule.comap (J : Submodule B B).subtype I))
        (Submodule.comap (J : Submodule B B).subtype (I ⊔ Ideal.span {x}))
      ≤ Submodule.span B {Submodule.Quotient.mk (⟨x, hxJ⟩ : ↥J)} := by
  rintro z ⟨g, hg, rfl⟩
  have hg' : (J : Submodule B B).subtype g ∈ (I ⊔ Ideal.span {x}) := Submodule.mem_comap.mp hg
  obtain ⟨i, hi, w, hw, hiw⟩ := Submodule.mem_sup.mp hg'
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hw
  have hwJ : w ∈ J := hc ▸ Submodule.smul_mem J c hxJ
  have h1 : i = (J : Submodule B B).subtype g - w := by rw [← hiw]; abel
  have hiJ : i ∈ J := by rw [h1]; exact Submodule.sub_mem J g.2 hwJ
  have hg_eq : g = (⟨i, hiJ⟩ : ↥J) + c • (⟨x, hxJ⟩ : ↥J) := by
    apply Subtype.ext
    show (g : B) = i + c • x
    rw [hc, hiw]
    rfl
  rw [hg_eq, map_add, map_smul]
  have h0 : Submodule.mkQ (Submodule.comap (J : Submodule B B).subtype I) (⟨i, hiJ⟩ : ↥J) = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.mem_comap.mpr hi
  rw [h0, zero_add]
  exact Submodule.mem_span_singleton.mpr ⟨c, rfl⟩

/-! ## The cut step -/

/-- **One rank-one cut step, localised form.**

Let `R` be Noetherian, `p ≤ q` primes, `P ∉ p`, and `I ≤ J` ideals forming a *rank-one
`p`-primary step*: both are `p`-saturated (`I = (I·R_p) ∩ R`, same for `J`), the step is annihilated
by `p` (`p * J ≤ I`), `J` is `p`-primary (or `J = ⊤`), the `p`-local length drops by exactly one
(`locLenAt p hp I = locLenAt p hp J + 1`), and every `r ∉ p` lying in `q` satisfies
`q ∈ (p ⊔ (r)).minimalPrimes`. Then cutting by `P` adds at most `locLenAt q hq (p ⊔ (P))` to the
`q`-local length. -/
theorem cut_step_le_loc {R : Type*} [CommRing R] [IsNoetherianRing R]
    (p q : Ideal R) (hp : p.IsPrime) (hq : q.IsPrime) (hpq : p ≤ q)
    (P : R) (hPp : P ∉ p) (I J : Ideal R) (hIJ : I ≤ J)
    (hsatI : ((I.map (algebraMap R (Localization.AtPrime p))).comap
      (algebraMap R (Localization.AtPrime p))) = I)
    (hsatJ : ((J.map (algebraMap R (Localization.AtPrime p))).comap
      (algebraMap R (Localization.AtPrime p))) = J)
    (hpJ : p * J ≤ I)
    (hJ : (J.IsPrimary ∧ J.radical = p) ∨ J = ⊤)
    (hmin : ∀ r : R, r ∉ p → r ∈ q → q ∈ (p ⊔ Ideal.span {r}).minimalPrimes)
    (hrank : Work.BW.locLenAt p hp I = Work.BW.locLenAt p hp J + 1) :
    Work.BW.locLenAt q hq (I ⊔ Ideal.span {P}) ≤
      Work.BW.locLenAt q hq (J ⊔ Ideal.span {P}) +
        Work.BW.locLenAt q hq (p ⊔ Ideal.span {P}) := by
  haveI := hp
  haveI := hq
  let B := Localization.AtPrime q
  let 𝔭 : Ideal B := Ideal.map (algebraMap R B) p
  let IL : Ideal B := Ideal.map (algebraMap R B) I
  let JL : Ideal B := Ideal.map (algebraMap R B) J
  let PL : Ideal B := Ideal.span {algebraMap R B P}
  -- `𝔭` is prime
  have h𝔭prime : 𝔭.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (M := q.primeCompl) (S := B) p hp
      (by rw [Set.disjoint_left]; exact fun t htq htp => htq (hpq htp))
  -- the contraction of `𝔭` is `p`
  have hunder : 𝔭.comap (algebraMap R B) = p :=
    IsLocalization.under_map_of_isPrime_disjoint (M := q.primeCompl) (S := B) hp
      (by rw [Set.disjoint_left]; exact fun t htq htp => htq (hpq htp))
  -- rewrite the goal in terms of lengths in `B`
  have key : ∀ (K : Ideal R) (y : R),
      locLenAt q hq (K ⊔ Ideal.span {y}) =
        Module.length B (B ⧸ (K.map (algebraMap R B) ⊔ Ideal.span {algebraMap R B y})) := by
    intro K y
    show Module.length B (B ⧸ (K ⊔ Ideal.span {y}).map (algebraMap R B)) = _
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  rw [key I P, key J P, key p P]
  -- `𝔭 · JL ≤ IL`
  have hmul : 𝔭 * JL ≤ IL := by
    have h1 : (p * J).map (algebraMap R B) ≤ IL := Ideal.map_mono hpJ
    rwa [Ideal.map_mul] at h1
  rcases hJ with hprim | hJtop
  · -- ## main case: `J` is `p`-primary with radical `p`
    obtain ⟨hJpri, hJrad⟩ := hprim
    obtain ⟨x, hxJ, hxprop⟩ := cut_rank_one p hp I J hIJ (Or.inl ⟨hJpri, hJrad⟩) hrank
    -- `J·R_p` has finite length over `R_p`
    have hJfin : locLenAt p hp J ≠ ⊤ := by
      have hpmin : p ∈ J.minimalPrimes := by
        rw [← Ideal.radical_minimalPrimes (I := J), hJrad,
          Ideal.minimalPrimes_eq_subsingleton_self]
        exact Set.mem_singleton p
      exact primLen_ne_top_aux J p hpmin
    -- `x ∉ I`: otherwise `J·R_p ≤ I·R_p`, contradicting the rank-one hypothesis
    have hxI : x ∉ I := by
      intro hxmem
      have hfy : ∀ y ∈ J, algebraMap R (Localization.AtPrime p) y ∈
          I.map (algebraMap R (Localization.AtPrime p)) := by
        intro y hyJ
        obtain ⟨d, hdp, hdy⟩ := hxprop y hyJ
        have hsub : Ideal.span {x} ≤ I :=
          Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hxmem)
        rw [sup_eq_left.mpr hsub] at hdy
        have hunit : IsUnit (algebraMap R (Localization.AtPrime p) d) :=
          (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime p) p d).mpr hdp
        have hmem : algebraMap R (Localization.AtPrime p) d *
            algebraMap R (Localization.AtPrime p) y ∈
            I.map (algebraMap R (Localization.AtPrime p)) := by
          rw [← map_mul]
          exact Ideal.mem_map_of_mem _ hdy
        obtain ⟨u, hu⟩ := hunit
        have h3 : (↑u⁻¹ : Localization.AtPrime p) *
            (algebraMap R (Localization.AtPrime p) d *
              algebraMap R (Localization.AtPrime p) y) ∈
            I.map (algebraMap R (Localization.AtPrime p)) := Ideal.mul_mem_left _ _ hmem
        rw [← hu, ← mul_assoc, Units.inv_mul, one_mul] at h3
        exact h3
      have hmap : J.map (algebraMap R (Localization.AtPrime p)) ≤
          I.map (algebraMap R (Localization.AtPrime p)) := by
        rw [Ideal.map_le_iff_le_comap]
        intro y hyJ
        rw [Ideal.mem_comap]
        exact hfy y hyJ
      have hmono : locLenAt p hp I ≤ locLenAt p hp J :=
        Module.length_le_of_surjective (Submodule.factor hmap)
          (Submodule.factor_surjective hmap)
      rw [hrank] at hmono
      obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hJfin
      rw [← hn] at hmono
      have hle : n + 1 ≤ n := by exact_mod_cast hmono
      omega
    -- the module `M := JL ⧸ IL` over `B`, and the class `m₀` of `x`
    let ML : Submodule B ↥JL := Submodule.comap (JL : Submodule B B).subtype IL
    let M := ↥JL ⧸ ML
    have hxJL : algebraMap R B x ∈ JL := Ideal.mem_map_of_mem _ hxJ
    let m₀ : M := Submodule.Quotient.mk (⟨algebraMap R B x, hxJL⟩ : ↥JL)
    -- `M ⧸ B·m₀` is `𝔭`-torsion
    have htor : ∀ m : M, ∃ d : B, d ∉ 𝔭 ∧ d • m ∈ Submodule.span B {m₀} := by
      intro m
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective ML m
      obtain ⟨xw, hxw⟩ := (IsLocalization.mem_map_algebraMap_iff q.primeCompl B).mp
          (show (y : B) ∈ JL from y.2)
      obtain ⟨d, hdp, hdy⟩ := hxprop xw.1 xw.1.2
      refine ⟨algebraMap R B d, ?_, ?_⟩
      · intro hmem
        have h2 : d ∈ 𝔭.comap (algebraMap R B) := hmem
        rw [hunder] at h2
        exact hdp h2
      · have hmem : (algebraMap R B d) • y ∈
            Submodule.comap (JL : Submodule B B).subtype
              (IL ⊔ Ideal.span {algebraMap R B x}) := by
          rw [Submodule.mem_comap]
          change (algebraMap R B d) * (y : B) ∈
            IL ⊔ Ideal.span {algebraMap R B x}
          have h1 : algebraMap R B (d * xw.1) ∈ IL ⊔ Ideal.span {algebraMap R B x} := by
            have h2 := Ideal.mem_map_of_mem (algebraMap R B) hdy
            simpa [IL, Ideal.map_sup, Ideal.map_span] using h2
          have h2 : algebraMap R B (d * xw.1) =
              algebraMap R B (xw.2 : R) * ((algebraMap R B d) * (y : B)) := by
            rw [map_mul, ← hxw]
            ring
          rw [h2] at h1
          have hunit : IsUnit (algebraMap R B (xw.2 : R)) := IsLocalization.map_units B xw.2
          obtain ⟨u, hu⟩ := hunit
          have h4 : (algebraMap R B d) * (y : B) =
              ↑(u⁻¹) * (algebraMap R B (xw.2 : R) * ((algebraMap R B d) * (y : B))) := by
            rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]
          rw [h4]
          exact Ideal.mul_mem_left _ _ h1
        rw [Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul]
        exact rb_map_sub_comap_le_span (I := IL) (J := JL) hxJL
          (Submodule.mem_map_of_mem hmem)
    -- `P` is a non-zero-divisor on `M`
    have hPnd : ∀ m : M, algebraMap R B P • m = 0 → m = 0 := by
      intro m hm
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective ML m
      rw [Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hm
      have hm' : algebraMap R B P * (y : B) ∈ I.map (algebraMap R B) := hm
      have hyIL : (y : B) ∈ IL :=
        smul_mem_map_of_mul_smul_mem hpq I hsatI P hPp (by simpa using hm')
      exact (Submodule.Quotient.mk_eq_zero ML).mpr (Submodule.mem_comap.mpr hyIL)
    -- the annihilator of `m₀` is `𝔭`
    have hann₀ : ∀ b : B, b • m₀ = 0 → b ∈ 𝔭 := by
      intro b hb
      have hmem : b * algebraMap R B x ∈ IL := by
        have h2 : b • Submodule.Quotient.mk (⟨algebraMap R B x, hxJL⟩ : ↥JL) = 0 := hb
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h2
        simpa [ML] using h2
      exact mem_map_prime_of_mul_mem_map hpq I hsatI x hxI (by simpa [IL] using hmem)
    -- `M ⧸ B·m₀` has finite length
    have hfin : IsFiniteLength B (M ⧸ (Submodule.span B {m₀})) := by
      refine isFiniteLength_quot_span_of_torsion 𝔭 h𝔭prime m₀ ?_ ?_ htor ?_
      · intro b hb m
        obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective ML m
        rw [Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
        exact Submodule.mem_comap.mpr (hmul (Ideal.mul_mem_mul hb y.2))
      · infer_instance
      · intro r hr
        have h3 := hmin_cut_artinian p q hpq hmin r (by simpa [𝔭] using hr)
        simpa [𝔭] using h3
    -- the rank-one cut bound
    have hbound : Module.length B (M ⧸ (Ideal.span {algebraMap R B P} • (⊤ : Submodule B M))) =
        Module.length B (B ⧸ (𝔭 ⊔ PL)) :=
      rank_one_cut_bound 𝔭 (algebraMap R B P) m₀
        (by intro b hb m
            obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective ML m
            rw [Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
            exact Submodule.mem_comap.mpr (hmul (Ideal.mul_mem_mul hb y.2)))
        hPnd hann₀ hfin
    -- the surjection `M ⧸ P·M → (JL + PL) ⧸ (IL + PL)`
    let K : Ideal B := IL ⊔ PL
    let ψ : M →ₗ[B] (B ⧸ K) :=
      ML.mapQ K (JL : Submodule B B).subtype
        (by intro z hz
            exact Submodule.mem_comap.mpr (Submodule.mem_sup_left (Submodule.mem_comap.mp hz)))
    have hψrange : ψ.range = Submodule.map (Submodule.mkQ (K : Submodule B B))
        ((JL ⊔ PL : Ideal B) : Submodule B B) := by
      apply le_antisymm
      · rintro z ⟨m, rfl⟩
        obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective ML m
        rw [Submodule.mkQ_apply]
        simp only [ψ, Submodule.mapQ_apply]
        exact Submodule.mem_map_of_mem (Submodule.mem_sup_left y.2)
      · intro z hz
        obtain ⟨w, hw, rfl⟩ := hz
        obtain ⟨j, hj, pl, hpl, hjpl⟩ := Submodule.mem_sup.mp hw
        have hplK : pl ∈ K := Submodule.mem_sup_right hpl
        refine ⟨Submodule.Quotient.mk (⟨j, hj⟩ : ↥JL), ?_⟩
        rw [← hjpl]
        have h1 : Submodule.mkQ (K : Submodule B B) (j + pl) =
            Submodule.mkQ (K : Submodule B B) j := by
          rw [map_add]
          simp only [Submodule.mkQ_apply]
          rw [(Submodule.Quotient.mk_eq_zero (K : Submodule B B)).mpr hplK, add_zero]
        rw [h1]
        simp only [ψ, Submodule.mapQ_apply]
        rfl
    have hle_ker : (Ideal.span {algebraMap R B P} • (⊤ : Submodule B M)) ≤ ψ.ker := by
      rw [Submodule.smul_le]
      intro a ha m _
      rw [LinearMap.mem_ker, map_smul]
      have haK : a ∈ K := Submodule.mem_sup_right ha
      obtain ⟨b, hb⟩ := Submodule.mkQ_surjective (K : Submodule B B) (ψ m)
      rw [← hb, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      simpa [smul_eq_mul, mul_comm] using K.mul_mem_left b haK
    have hsurj : Module.length B (Submodule.map (Submodule.mkQ (K : Submodule B B))
          ((JL ⊔ PL : Ideal B) : Submodule B B))
        ≤ Module.length B (M ⧸ (Ideal.span {algebraMap R B P} • (⊤ : Submodule B M))) :=
      calc Module.length B (Submodule.map (Submodule.mkQ (K : Submodule B B))
              ((JL ⊔ PL : Ideal B) : Submodule B B))
          = Module.length B ψ.range := by rw [hψrange]
        _ = Module.length B (M ⧸ ψ.ker) := (LinearMap.quotKerEquivRange ψ).length_eq.symm
        _ ≤ Module.length B (M ⧸ (Ideal.span {algebraMap R B P} • (⊤ : Submodule B M))) :=
            Module.length_le_of_surjective (Submodule.factor hle_ker)
              (Submodule.factor_surjective hle_ker)
    -- assembly
    have hKL : K ≤ JL ⊔ PL := sup_le_sup_right (Ideal.map_mono hIJ) PL
    have h1 := rb_length_quotient_add_map (K := K) (L := JL ⊔ PL) hKL
    rw [h1]
    exact add_le_add_right (hsurj.trans (le_of_eq hbound)) _
  · -- ## degenerate case `J = ⊤`
    have hpI : p ≤ I := by
      intro y hy
      have h1 : (1 : R) ∈ J := by rw [hJtop]; trivial
      have h2 : y * 1 ∈ p * J := Ideal.mul_mem_mul hy h1
      rw [mul_one] at h2
      exact hpJ h2
    have hJLtop : JL = ⊤ := by
      show Ideal.map (algebraMap R B) J = ⊤
      rw [hJtop, Ideal.map_top]
    have hle : 𝔭 ⊔ PL ≤ IL ⊔ PL := sup_le_sup_right (Ideal.map_mono hpI) PL
    have h0 : Module.length B (B ⧸ (JL ⊔ PL)) = 0 := by
      rw [hJLtop, top_sup_eq, Module.length_eq_zero_iff]
      infer_instance
    rw [h0, zero_add]
    exact Module.length_le_of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle)

end Work.BW.RB
