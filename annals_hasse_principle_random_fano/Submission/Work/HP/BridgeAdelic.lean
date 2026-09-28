import Mathlib
import Submission.Work.HP.BridgeDefs
import Submission.Work.HP.BridgeEval

/-!
# Adelic solubility implies real and `p`-adic solubility

The adele ring of `ℚ` is the product of the infinite adele ring and the finite adele ring
(`NumberField.AdeleRing`).  Hence an adelic point of `formOf d n a` maps to

* a real point, under the projection onto the unique infinite place of `ℚ` (whose completion
  is `ℝ`), and
* a `p`-adic point for every prime `p`, under the projection onto the finite place above `p`,
  composed with `Padic.adicCompletionEquiv`.

From a non-zero `p`-adic point we then extract a *primitive* zero modulo `p ^ r`: normalise the
point by a power of `p` so that it becomes integral with a unit coordinate, reduce modulo
`p ^ r` and lift to integer coordinates using `PadicInt.toZModPow`.
-/

set_option autoImplicit false

noncomputable section

open MvPolynomial Filter NumberField

namespace Work.HP

variable {d n : ℕ}

/-! ## `formEval` and ring homs -/

/-- `formEval` commutes with ring homomorphisms. -/
lemma formEval_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (d n : ℕ)
    (a : Mon d n → ℤ) (x : Fin (n + 1) → R) :
    φ (formEval d n a x) = formEval d n a (fun i => φ (x i)) := by
  simp only [formEval, veronese]
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [map_mul, map_intCast, map_prod, map_pow]

/-- Any ring hom from `ℚ` agrees with the structure map of a `ℚ`-algebra. -/
lemma comp_algebraMap_eq {K : Type*} [Semiring K] [Algebra ℚ K]
    (ψ : HassePrincipleRandomFano.𝔸 →+* K) :
    ψ.comp (algebraMap ℚ HassePrincipleRandomFano.𝔸) = algebraMap ℚ K :=
  RingHom.ext_rat _ _

/-! ## Pushing an adelic point to one place -/

/-- Evaluation of a polynomial commutes with a ring hom out of the adele ring. -/
lemma map_aeval_adele {K : Type*} [CommRing K] [Algebra ℚ K]
    (ψ : HassePrincipleRandomFano.𝔸 →+* K)
    (y : Fin (n + 1) → HassePrincipleRandomFano.𝔸) (p : MvPolynomial (Fin (n + 1)) ℚ) :
    ψ (aeval y p) = aeval (fun i => ψ (y i)) p := by
  rw [MvPolynomial.map_aeval, comp_algebraMap_eq ψ, ← MvPolynomial.aeval_eq_eval₂Hom]

/-- An adelic solution pushes forward to a solution over any field receiving the adele ring. -/
lemma exists_local_of_adelic {K : Type*} [Field K] [Algebra ℚ K]
    (ψ : HassePrincipleRandomFano.𝔸 →+* K) (a : Mon d n → ℤ) (h : AdelicSol d n a) :
    ∃ z : Fin (n + 1) → K, z ≠ 0 ∧ aeval z (formOf d n a) = 0 := by
  obtain ⟨y, hy, hf⟩ := h
  have hz : (fun i => ψ (y i)) ≠ 0 := by
    intro h0
    obtain ⟨i, hi⟩ := exists_map_ne_zero_of_span_range_eq_top ψ y hy
    exact hi (congrFun h0 i)
  exact ⟨fun i => ψ (y i), hz,
    by rw [← map_aeval_adele ψ y (formOf d n a), hf, map_zero]⟩

/-! ## The real place -/

lemma infinitePlace_isReal (w : InfinitePlace ℚ) : w.IsReal := by
  have h : ComplexEmbedding.IsReal (Rat.castHom ℂ) := by ext x; simp
  exact ⟨Rat.castHom ℂ, h, Subsingleton.elim _ w⟩

/-- The projection of the adele ring of `ℚ` onto its unique infinite place, identified with `ℝ`. -/
noncomputable def realPlace : HassePrincipleRandomFano.𝔸 →+* ℝ :=
  (InfinitePlace.Completion.ringEquivRealOfIsReal (v := (default : InfinitePlace ℚ))
      (infinitePlace_isReal _)).toRingHom.comp
    ((Pi.evalRingHom (fun v : InfinitePlace ℚ => v.Completion) (default : InfinitePlace ℚ)).comp
      (RingHom.fst (InfiniteAdeleRing ℚ) (IsDedekindDomain.FiniteAdeleRing ℤ ℚ)))

theorem adelic_real (d n : ℕ) (a : Mon d n → ℤ) (h : AdelicSol d n a) : RealSol d n a := by
  obtain ⟨x, hx, hf⟩ := exists_local_of_adelic (d := d) (n := n) realPlace a h
  refine ⟨x, hx, ?_⟩
  rw [← aeval_formOf]
  exact hf

/-! ## The `p`-adic places -/

/-- The projection of the adele ring of `ℚ` onto the `p`-adic place. -/
noncomputable def padicPlace (p : ℕ) [Fact p.Prime] :
    HassePrincipleRandomFano.𝔸 →+* Padic p :=
  ((Padic.adicCompletionEquiv ℤ (⟨p, Fact.out⟩ : Nat.Primes)).symm.toRingHom).comp
    ((RestrictedProduct.evalRingHom
        (fun v : IsDedekindDomain.HeightOneSpectrum ℤ => v.adicCompletion ℚ)
        ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm ⟨p, Fact.out⟩)).comp
      (RingHom.snd (InfiniteAdeleRing ℚ) (IsDedekindDomain.FiniteAdeleRing ℤ ℚ)))

theorem adelic_padic (d n : ℕ) (a : Mon d n → ℤ) (p : ℕ) [Fact p.Prime]
    (h : AdelicSol d n a) :
    ∃ z : Fin (n + 1) → Padic p, z ≠ 0 ∧ MvPolynomial.aeval z (formOf d n a) = 0 :=
  exists_local_of_adelic (d := d) (n := n) (padicPlace p) a h

/-! ## A `p`-adic point gives a primitive zero modulo `p ^ r` -/

/-- A non-zero `p`-adic point of `formOf d n a` yields a primitive zero modulo `p ^ r`. -/
theorem padic_point_primModZero (d n : ℕ) (a : Mon d n → ℤ) (p r : ℕ) [Fact p.Prime]
    (h : ∃ z : Fin (n + 1) → Padic p, z ≠ 0 ∧ MvPolynomial.aeval z (formOf d n a) = 0) :
    PrimModZero d n a p r := by
  classical
  rcases r with _ | r
  · refine ⟨fun i => if i = 0 then 1 else 0, ⟨0, ?_⟩, ?_⟩
    · show ¬ (p : ℤ) ∣ (if (0 : Fin (n + 1)) = 0 then 1 else 0)
      rw [if_pos rfl]
      intro hdvd
      have hle : (p : ℤ) ≤ 1 := Int.le_of_dvd (by norm_num) hdvd
      have h2 : (2 : ℤ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
      omega
    · rw [pow_zero]
      exact one_dvd _
  obtain ⟨z, hz0, hf⟩ := h
  rw [aeval_formOf] at hf
  obtain ⟨j, hj⟩ : ∃ j, z j ≠ 0 := Function.ne_iff.1 hz0
  let T : Finset (Fin (n + 1)) := Finset.univ.filter (fun i => z i ≠ 0)
  have hTne : T.Nonempty := ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ j, hj⟩⟩
  have hTmem : ∀ i, z i ≠ 0 → i ∈ T := fun i hi =>
    Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩
  have hTz : ∀ i ∈ T, z i ≠ 0 := fun i hi => (Finset.mem_filter.1 hi).2
  obtain ⟨i₀, hi₀T, hk_le⟩ := Finset.exists_max_image T (fun i => -Padic.valuation (z i)) hTne
  have hzi₀ : z i₀ ≠ 0 := hTz i₀ hi₀T
  have hp0 : (p : Padic p) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hcne : (p : Padic p) ^ (-Padic.valuation (z i₀)) ≠ 0 := zpow_ne_zero _ hp0
  -- integrality of the normalised point
  have hnorm : ∀ i, ‖(p : Padic p) ^ (-Padic.valuation (z i₀)) * z i‖ ≤ 1 := by
    intro i
    refine (Padic.norm_le_one_iff_val_nonneg _).2 ?_
    by_cases hzi : z i = 0
    · rw [hzi, mul_zero, Padic.valuation_zero]
    · have h1 := hk_le i (hTmem i hzi)
      rw [Padic.valuation_mul hcne hzi, Padic.valuation_zpow, Padic.valuation_p, mul_one]
      linarith
  -- the integral point
  let u : Fin (n + 1) → ℤ_[p] := fun i => ⟨(p : Padic p) ^ (-Padic.valuation (z i₀)) * z i, hnorm i⟩
  have hu_coe : ∀ i, ((u i : ℤ_[p]) : Padic p) = (p : Padic p) ^ (-Padic.valuation (z i₀)) * z i := fun i => rfl
  have hformQ : formEval d n a (fun i => ((u i : ℤ_[p]) : Padic p)) = 0 := by
    have hfun : (fun i => ((u i : ℤ_[p]) : Padic p)) = fun i => (p : Padic p) ^ (-Padic.valuation (z i₀)) * z i :=
      funext hu_coe
    rw [hfun, formEval_mul, hf, mul_zero]
  have hcoe : ((formEval d n a u : ℤ_[p]) : Padic p)
      = formEval d n a (fun i => ((u i : ℤ_[p]) : Padic p)) :=
    formEval_map (algebraMap ℤ_[p] (Padic p)) d n a u
  have hform : formEval d n a u = 0 := Subtype.ext (hcoe.trans hformQ)
  -- the `i₀`-th coordinate is a unit
  have hval₀ : Padic.valuation ((p : Padic p) ^ (-Padic.valuation (z i₀)) * z i₀) = 0 := by
    rw [Padic.valuation_mul hcne hzi₀, Padic.valuation_zpow, Padic.valuation_p, mul_one]
    linarith
  have hnorm₀ : ‖(u i₀ : ℤ_[p])‖ = 1 := by
    rw [PadicInt.norm_def, hu_coe i₀, Padic.norm_eq_zpow_neg_valuation (mul_ne_zero hcne hzi₀),
      hval₀, neg_zero, zpow_zero]
  -- integer representatives, chosen through `ZMod.val`
  let yN : Fin (n + 1) → ℕ := fun i => (PadicInt.toZModPow (r + 1) (u i)).val
  have hyN_cast : ∀ i, PadicInt.toZModPow (r + 1) (u i)
      = ((yN i : ℕ) : ZMod (p ^ (r + 1))) := fun i => (ZMod.natCast_zmod_val _).symm
  have hfun_mod : (fun i => PadicInt.toZModPow (r + 1) (u i))
      = (fun i => Int.castRingHom (ZMod (p ^ (r + 1))) (yN i : ℤ)) := by
    funext i
    rw [hyN_cast i, congrFun (Int.coe_castRingHom (α := ZMod (p ^ (r + 1)))) (yN i : ℤ)]
    push_cast
    rfl
  have hcast : Int.castRingHom (ZMod (p ^ (r + 1))) (formEval d n a (fun i => (yN i : ℤ)))
      = formEval d n a (fun i => Int.castRingHom (ZMod (p ^ (r + 1))) (yN i : ℤ)) :=
    formEval_map (Int.castRingHom (ZMod (p ^ (r + 1)))) d n a (fun i => (yN i : ℤ))
  have hcongr : PadicInt.toZModPow (r + 1) (formEval d n a u)
      = Int.castRingHom (ZMod (p ^ (r + 1))) (formEval d n a (fun i => (yN i : ℤ))) := by
    rw [formEval_map (PadicInt.toZModPow (r + 1)), hfun_mod, hcast]
  have hdiv : ((p : ℤ) ^ (r + 1)) ∣ formEval d n a (fun i => (yN i : ℤ)) := by
    have h0 : ((formEval d n a (fun i => (yN i : ℤ)) : ℤ) : ZMod (p ^ (r + 1))) = 0 := by
      rw [← congrFun (Int.coe_castRingHom (α := ZMod (p ^ (r + 1))))
        (formEval d n a (fun i => (yN i : ℤ)))]
      rw [← hcongr, hform, map_zero]
    have h2 := (ZMod.intCast_zmod_eq_zero_iff_dvd (formEval d n a (fun i => (yN i : ℤ)))
      (p ^ (r + 1))).1 h0
    simpa using h2
  have hcop : Nat.Coprime (yN i₀) (p ^ (r + 1)) := by
    have hu₀ : IsUnit (u i₀) := by
      rw [PadicInt.isUnit_iff]
      exact hnorm₀
    have h1 : IsUnit (PadicInt.toZModPow (r + 1) (u i₀)) := hu₀.map _
    rw [hyN_cast i₀] at h1
    exact (ZMod.isUnit_iff_coprime (yN i₀) (p ^ (r + 1))).1 h1
  have hprim : ¬ (p : ℤ) ∣ (yN i₀ : ℤ) := by
    intro hdvd
    have hdvd' : p ∣ yN i₀ := by exact_mod_cast hdvd
    have h3 : p ∣ p ^ (r + 1) := dvd_pow_self p (Nat.succ_ne_zero r)
    have h4 : p ∣ Nat.gcd (yN i₀) (p ^ (r + 1)) := Nat.dvd_gcd hdvd' h3
    rw [hcop] at h4
    exact (Fact.out : p.Prime).not_dvd_one h4
  exact ⟨fun i => (yN i : ℤ), ⟨i₀, hprim⟩, hdiv⟩

end Work.HP
