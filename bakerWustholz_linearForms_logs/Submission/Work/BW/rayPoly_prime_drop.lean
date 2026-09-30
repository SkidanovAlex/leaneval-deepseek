import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.BW.rayPoly_eq
import Submission.Work.BW.rayHilb_cut
import Submission.Work.BW.rayHilb_cut_aux
import Submission.Work.BW.poly_shift_natDegree
import Submission.Work.BW.poly_natDegree_eventually_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open MvPolynomial

variable {N : ℕ}

/-! ### Multidegree bookkeeping for monomials

The weight function `mdeg N` gives both variables `X_{i0}, X_{i1}` of the `i`-th factor the weight
`eᵢ`, so a monomial has multidegree `d` exactly when its exponent vector `m` satisfies
`Finsupp.weight (mdeg N) m = d`. The first group of lemmas makes this explicit. -/

private lemma mdeg_apply_ (v : Fin (N + 1) × Fin 2) (i : Fin (N + 1)) :
    mdeg N v i = if v.1 = i then 1 else 0 := by
  by_cases h : v.1 = i <;> simp [mdeg, h]

private lemma weight_apply_ (m : Fin (N + 1) × Fin 2 →₀ ℕ) (i : Fin (N + 1)) :
    Finsupp.weight (mdeg N) m i = ∑ v, m v * (if v.1 = i then 1 else 0) := by
  rw [Finsupp.weight_eq_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finsupp.smul_apply, mdeg_apply_, smul_eq_mul]

/-- If the multidegree of `m` has a positive `i`-th coordinate, some variable of the `i`-th factor
divides the monomial `m`. -/
private lemma exists_support_of_weight_apply_pos_ {m : Fin (N + 1) × Fin 2 →₀ ℕ}
    {e : Fin (N + 1) →₀ ℕ} (h : Finsupp.weight (mdeg N) m = e) {i : Fin (N + 1)}
    (hi : 1 ≤ e i) : ∃ j : Fin 2, m (i, j) ≠ 0 := by
  have hsum : e i = ∑ v, m v * (if v.1 = i then 1 else 0) := by
    rw [← h]; exact weight_apply_ m i
  have hne : (∑ v, m v * (if v.1 = i then 1 else 0)) ≠ 0 := by omega
  obtain ⟨v, -, hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hmv : m v ≠ 0 := fun h0 => hv (by rw [h0, zero_mul])
  have hvi : v.1 = i := by
    by_contra hc
    exact hv (by rw [ite_eq_right hc, mul_zero])
  refine ⟨v.2, ?_⟩
  rwa [show (i, v.2) = v from by rw [← hvi]]

private lemma sum_smul_mdeg_apply_ (a : Fin (N + 1) → ℕ) (j : Fin (N + 1) → Fin 2)
    (i : Fin (N + 1)) :
    (∑ i' : Fin (N + 1), a i' • mdeg N (i', j i')) i = a i := by
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single i]
  · rw [Finsupp.smul_apply, mdeg_apply_, ite_eq_left rfl, smul_eq_mul, mul_one]
  · intro i' _ hne
    rw [Finsupp.smul_apply, mdeg_apply_, ite_eq_right hne, smul_zero]
  · intro hi; exact absurd (Finset.mem_univ i) hi

/-! ### The multihomogeneous pieces as spans of monomials -/

private lemma monomial_mem_homPiece_ {e : Fin (N + 1) →₀ ℕ}
    {m : Fin (N + 1) × Fin 2 →₀ ℕ} (h : Finsupp.weight (mdeg N) m = e) :
    (monomial m (1 : ℂ)) ∈ homPiece N e := by
  rw [homPiece, MvPolynomial.mem_weightedHomogeneousSubmodule]
  exact MvPolynomial.isWeightedHomogeneous_monomial _ _ _ h

private lemma homPiece_eq_span_ (e : Fin (N + 1) →₀ ℕ) :
    homPiece N e = Submodule.span ℂ ((fun m => MvPolynomial.monomial m (1 : ℂ)) ''
      {m | Finsupp.weight (mdeg N) m = e}) := by
  rw [homPiece, MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported]
  exact MvPolynomial.restrictSupport_eq_span ℂ _

/-- If both variables of the `i`-th factor lie in an ideal `I`, and the `i`-th multidegree is
nonzero, then `I` contains the whole multihomogeneous piece. -/
private lemma homPiece_le_of_both_X_mem_ {I : Ideal (MR N)} {i : Fin (N + 1)}
    (h0 : MvPolynomial.X (i, 0) ∈ I) (h1 : MvPolynomial.X (i, 1) ∈ I)
    {e : Fin (N + 1) →₀ ℕ} (he : 1 ≤ e i) : homPiece N e ≤ I.restrictScalars ℂ := by
  rw [homPiece_eq_span_, Submodule.span_le]
  rintro _ ⟨m, hm, rfl⟩
  obtain ⟨j, hj⟩ := exists_support_of_weight_apply_pos_ hm he
  have hX : MvPolynomial.X (i, j) ∈ I := by
    fin_cases j
    · exact h0
    · exact h1
  have hdvd : MvPolynomial.X (i, j) ∣ MvPolynomial.monomial m (1 : ℂ) :=
    MvPolynomial.X_dvd_monomial.mpr (Or.inr hj)
  obtain ⟨c, hc⟩ := hdvd
  simpa [hc] using Ideal.mul_mem_right c I hX

private lemma prod_notMem_of_notMem_ {I : Ideal (MR N)} (hp : I.IsPrime) {ι : Type*}
    {s : Finset ι} {f : ι → MR N} (h : ∀ i ∈ s, f i ∉ I) : ∏ i ∈ s, f i ∉ I := by
  classical
  refine Finset.prod_induction _ (fun x => x ∉ I) ?_ ?_ h
  · intro a b ha hb hab
    exact (hp.mem_or_mem hab).elim ha hb
  · intro h1
    exact (Ideal.ne_top_iff_one I).mp hp.ne_top h1

/-! ### Producing a multihomogeneous cut element -/

/-- **Existence of a multihomogeneous element of `q \ p` on a prescribed ray.** If `p < q` are
multihomogeneous primes and the ray Hilbert polynomial of `q` is not identically zero, then for some
`k ≥ 1` there is `Q ∈ homPiece N (k • D) ∩ q` with `Q ∉ p`; `Q` is then a non-zerodivisor modulo the
prime `p`. -/
private theorem exists_cut_element_ (D : Fin (N + 1) →₀ ℕ) (hD : ∀ i, 1 ≤ D i)
    (p q : Ideal (MR N)) (hp : p.IsPrime) (hq : q.IsPrime) (hpH : MultiHom N p)
    (hqH : MultiHom N q) (hpq : p < q) (hq0 : rayPoly N D q ≠ 0) :
    ∃ k : ℕ, 1 ≤ k ∧ ∃ Q ∈ homPiece N (k • D), Q ∈ q ∧ Q ∉ p := by
  classical
  have hne : p ≠ q := hpq.ne
  have hle : p ≤ q := hpq.le
  have hnotsub : ¬ (q : Set (MR N)) ⊆ p := by
    intro hsub
    exact hne (le_antisymm hle fun x hx => hsub hx)
  obtain ⟨f, hfq, hfp⟩ := Set.not_subset.mp hnotsub
  obtain ⟨d, hd⟩ : ∃ d : Fin (N + 1) →₀ ℕ,
      MvPolynomial.weightedHomogeneousComponent (mdeg N) d f ∉ p := by
    by_contra hc
    push Not at hc
    have hfin := MvPolynomial.weightedHomogeneousComponent_finsupp (w := mdeg N) f
    have hsum := MvPolynomial.sum_weightedHomogeneousComponent (mdeg N) f
    rw [finsum_eq_sum _ hfin] at hsum
    refine hfp (hsum ▸ Submodule.sum_mem _ fun d _ => hc d)
  set g : MR N := MvPolynomial.weightedHomogeneousComponent (mdeg N) d f with hgdef
  have hgq : g ∈ q := hqH f hfq d
  have hgne : g ≠ 0 := fun h => hd (h ▸ p.zero_mem)
  have hghom : MvPolynomial.IsWeightedHomogeneous (mdeg N) g d :=
    MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous d f
  have hvar : ∀ i : Fin (N + 1), ∃ j : Fin 2, MvPolynomial.X (i, j) ∉ p := by
    intro i
    by_contra hc
    push Not at hc
    have hzero : ∀ t : ℕ, 1 ≤ t → rayHilb N D q t = 0 := by
      intro t ht
      have hpiece : homPiece N (t • D) ≤ q.restrictScalars ℂ := fun x hx =>
        hle (homPiece_le_of_both_X_mem_ (hc 0) (hc 1) (by
          rw [Finsupp.smul_apply, smul_eq_mul]
          simpa using Nat.mul_le_mul ht (hD i)) hx)
      unfold rayHilb
      have htop : Submodule.comap (homPiece N (t • D)).subtype (q.restrictScalars ℂ) = ⊤ := by
        rw [eq_top_iff]
        intro x _
        exact hpiece x.2
      rw [htop]
      haveI : Subsingleton (↥(homPiece N (t • D)) ⧸
          (⊤ : Submodule ℂ ↥(homPiece N (t • D)))) :=
        Submodule.Quotient.subsingleton_iff.mpr rfl
      exact Module.finrank_zero_of_subsingleton
    have hpoly : IsRayPoly N D q 0 := by
      filter_upwards [Filter.eventually_ge_atTop 1] with t ht
      rw [hzero t ht]; simp
    exact hq0 (rayPoly_eq hpoly)
  choose j hj using hvar
  let k : ℕ := 1 + ∑ i : Fin (N + 1), d i
  have hk : 1 ≤ k := by simp [k]
  have hkD : ∀ i, d i ≤ k * D i := by
    intro i
    have h1 : k ≤ k * D i := Nat.le_mul_of_pos_right k (by have := hD i; omega)
    have h2 : d i ≤ k := by
      have h3 : d i ≤ ∑ i : Fin (N + 1), d i :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      simp only [k]
      omega
    exact le_trans h2 h1
  let M : MR N := ∏ i : Fin (N + 1), MvPolynomial.X (i, j i) ^ (k * D i - d i)
  have hMhom : MvPolynomial.IsWeightedHomogeneous (mdeg N) M
      (∑ i : Fin (N + 1), (k * D i - d i) • mdeg N (i, j i)) := by
    refine MvPolynomial.IsWeightedHomogeneous.prod Finset.univ _ _ ?_
    intro i _
    exact (MvPolynomial.isWeightedHomogeneous_X ℂ (mdeg N) (i, j i)).pow _
  have hdeg : d + (∑ i : Fin (N + 1), (k * D i - d i) • mdeg N (i, j i)) = k • D := by
    ext i
    rw [Finsupp.add_apply, sum_smul_mdeg_apply_, Finsupp.smul_apply, smul_eq_mul]
    have := hkD i
    omega
  have hQhom : MvPolynomial.IsWeightedHomogeneous (mdeg N) (g * M) (k • D) := by
    have h := hghom.mul hMhom
    rwa [hdeg] at h
  have hMp : M ∉ p := by
    refine prod_notMem_of_notMem_ hp ?_
    intro i _
    rcases Nat.eq_zero_or_pos (k * D i - d i) with h | h
    · rw [h, pow_zero]
      exact fun h1 => (Ideal.ne_top_iff_one p).mp hp.ne_top h1
    · exact fun hpow => hj i (hp.mem_of_pow_mem _ hpow)
  have hQmem : g * M ∈ homPiece N (k • D) := by
    rw [homPiece, MvPolynomial.mem_weightedHomogeneousSubmodule]
    exact hQhom
  have hQq : g * M ∈ q := Ideal.mul_mem_right M q hgq
  have hQp : g * M ∉ p := fun hab => (hp.mem_or_mem hab).elim hd hMp
  exact ⟨k, hk, g * M, hQmem, hQq, hQp⟩

/-! ### Basic facts about the ray Hilbert polynomial -/

/-- A nonzero `rayPoly` is an `IsRayPoly`. -/
private lemma isRayPoly_rayPoly_of_ne_zero_ {D : Fin (N + 1) →₀ ℕ} {I : Ideal (MR N)}
    (h : rayPoly N D I ≠ 0) : IsRayPoly N D I (rayPoly N D I) := by
  by_cases hh : ∃ q, IsRayPoly N D I q
  · unfold rayPoly
    rw [dite_eq_left hh]
    exact Classical.choose_spec hh
  · exact absurd (show rayPoly N D I = 0 from by
      unfold rayPoly; rw [dite_eq_right hh]) h

/-- The ray Hilbert function is antitone in the ideal. -/
private lemma rayHilb_anti_ (D : Fin (N + 1) →₀ ℕ) {I J : Ideal (MR N)} (hIJ : I ≤ J)
    (t : ℕ) : rayHilb N D J t ≤ rayHilb N D I t := by
  haveI := moduleFinite_homPiece N (t • D)
  unfold rayHilb
  have hmono : Submodule.comap (homPiece N (t • D)).subtype (I.restrictScalars ℂ) ≤
      Submodule.comap (homPiece N (t • D)).subtype (J.restrictScalars ℂ) :=
    Submodule.comap_mono fun x hx => hIJ hx
  have h1 := Submodule.finrank_quotient_add_finrank
    (Submodule.comap (homPiece N (t • D)).subtype (I.restrictScalars ℂ))
  have h2 := Submodule.finrank_quotient_add_finrank
    (Submodule.comap (homPiece N (t • D)).subtype (J.restrictScalars ℂ))
  have h3 : Module.finrank ℂ
        ↥(Submodule.comap (homPiece N (t • D)).subtype (I.restrictScalars ℂ)) ≤
      Module.finrank ℂ
        ↥(Submodule.comap (homPiece N (t • D)).subtype (J.restrictScalars ℂ)) :=
    Submodule.finrank_mono hmono
  omega

/-- Cutting a multihomogeneous ideal `I` by a multihomogeneous non-zerodivisor `Q` of multidegree
`k • D`: the ray Hilbert polynomial of `I ⊔ (Q)` is the first difference `P - P(X - k)` of that
of `I`. -/
private lemma isRayPoly_cut_ {D : Fin (N + 1) →₀ ℕ} {k : ℕ} (hk : 1 ≤ k) {I : Ideal (MR N)}
    (hI : MultiHom N I) {Q : MR N} (hQ : Q ∈ homPiece N (k • D))
    (hreg : ∀ f, Q * f ∈ I → f ∈ I) {P : Polynomial ℚ} (hP : IsRayPoly N D I P) :
    IsRayPoly N D (I ⊔ Ideal.span {Q})
      (P - P.comp (Polynomial.X - Polynomial.C (k : ℚ))) := by
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hP
  refine Filter.eventually_atTop.mpr ⟨T + k, fun t ht => ?_⟩
  have hkt : k ≤ t := by omega
  have hTt : T ≤ t := by omega
  have hTtk : T ≤ t - k := by omega
  have hcut := rayHilb_cut D k hk I hI Q hQ hreg (t - k)
  rw [Nat.sub_add_cancel hkt] at hcut
  have hsub : rayHilb N D (I ⊔ Ideal.span {Q}) t =
      rayHilb N D I t - rayHilb N D I (t - k) := by omega
  have hble : rayHilb N D I (t - k) ≤ rayHilb N D I t := by omega
  rw [hsub, Nat.cast_sub hble, hT t hTt, hT (t - k) hTtk]
  rw [Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, Nat.cast_sub hkt]

/-- Strict dimension drop for strictly larger multihomogeneous primes, in a hypothesis-free form:
if `p < q` are multihomogeneous primes and `P0` is a polynomial eventually equal to the ray Hilbert
function of `p`, then either the ray Hilbert polynomial of `q` vanishes identically, or its degree is
strictly smaller. Case split on `rayPoly N D q = 0`; in the other case, cut `p` by a
multihomogeneous element `Q ∈ q \ p` of multidegree `k • D` (such a `Q` exists exactly when
`(R/p)_{kD} ≠ 0`, which holds for suitable `k` because `rayPoly q ≠ 0`), use the exact sequence
`0 → (R/p)(-kD) → R/p → R/(p+(Q)) → 0` to express the ray function of `p + (Q)` as `P0 - P0(· - k)`
(`rayHilb_cut`), bound the ray function of `q` by it (`p + (Q) ≤ q`) and conclude with
`poly_natDegree_eventually_le` and `poly_shift_natDegree`. CONVENIENT BUT FORBIDDEN:
`Submission.Work.BW.rayDim_lt_of_lt` states the same conclusion under the extra hypothesis
`rayPoly N D q ≠ 0`, but its proof goes through `rayHilb_poly`, which still contains a `sorry`; a
proof resting on it would not be sorry-free. Do not import it. -/
theorem rayPoly_prime_drop {N : ℕ} (D : Fin (N + 1) →₀ ℕ) (hD : ∀ i, 1 ≤ D i)
    (p q : Ideal (MR N)) (hp : p.IsPrime) (hq : q.IsPrime) (hpH : MultiHom N p)
    (hqH : MultiHom N q) (hpq : p < q) (P0 : Polynomial ℚ) (hP0 : IsRayPoly N D p P0) :
    rayPoly N D q = 0 ∨ rayDim N D q < rayDim N D p := by
  classical
  by_cases hq0 : rayPoly N D q = 0
  · exact Or.inl hq0
  · refine Or.inr ?_
    -- a multihomogeneous element of multidegree `k • D` in `q \ p`
    obtain ⟨k, hk, Q, hQmem, hQq, hQp⟩ :=
      exists_cut_element_ D hD p q hp hq hpH hqH hpq hq0
    -- `Q` is a non-zerodivisor modulo `p`
    have hreg : ∀ f, Q * f ∈ p → f ∈ p := fun f hf =>
      (hp.mem_or_mem hf).elim (fun h => absurd h hQp) id
    -- the cut ideal sits between `p` and `q`
    have hIQ : p ⊔ Ideal.span {Q} ≤ q :=
      sup_le hpq.le (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hQq))
    -- the exact sequence gives the ray Hilbert polynomial of the cut ideal
    have hcut : IsRayPoly N D (p ⊔ Ideal.span {Q})
        (P0 - P0.comp (Polynomial.X - Polynomial.C (k : ℚ))) :=
      isRayPoly_cut_ hk hpH hQmem hreg hP0
    have hqpoly : IsRayPoly N D q (rayPoly N D q) := isRayPoly_rayPoly_of_ne_zero_ hq0
    have hdimp : rayDim N D p = P0.natDegree := by rw [rayDim, rayPoly_eq hP0]
    by_cases hr : P0.natDegree = 0
    · -- degenerate case: `P0` is a constant, so the cut ideal has vanishing ray Hilbert function
      exfalso
      have hz : P0 - P0.comp (Polynomial.X - Polynomial.C (k : ℚ)) = 0 := by
        rw [Polynomial.eq_C_of_natDegree_eq_zero hr, Polynomial.C_comp, sub_self]
      rw [hz] at hcut
      have hqzero : IsRayPoly N D q 0 := by
        filter_upwards [hcut] with t ht
        have hI0 : rayHilb N D (p ⊔ Ideal.span {Q}) t = 0 := by
          have h := ht
          simp only [Polynomial.eval_zero] at h
          exact_mod_cast h
        have hle := rayHilb_anti_ D hIQ t
        rw [hI0] at hle
        rw [Nat.eq_zero_of_le_zero hle]
        simp
      exact hq0 (rayPoly_eq hqzero)
    · -- main case: the degree of the ray Hilbert polynomial drops by one
      have hr1 : 0 < P0.natDegree := Nat.pos_of_ne_zero hr
      have hanti : ∀ᶠ t : ℕ in Filter.atTop,
          (rayPoly N D q).eval (t : ℚ) ≤
            (P0 - P0.comp (Polynomial.X - Polynomial.C (k : ℚ))).eval (t : ℚ) := by
        filter_upwards [hqpoly, hcut] with t ht1 ht2
        rw [← ht1, ← ht2]
        exact_mod_cast rayHilb_anti_ D hIQ t
      have hnonneg : ∀ᶠ t : ℕ in Filter.atTop, 0 ≤ (rayPoly N D q).eval (t : ℚ) := by
        filter_upwards [hqpoly] with t ht
        rw [← ht]
        exact Nat.cast_nonneg _
      have hle := poly_natDegree_eventually_le hanti hnonneg
      rw [poly_shift_natDegree P0 k hk] at hle
      rw [rayDim, hdimp]
      omega

end Work.BW
