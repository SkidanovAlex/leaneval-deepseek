import Mathlib
import Submission.Work.MotAS.ASRulV2.RouteZAux
import Submission.Work.MotAS.ASRulV2M.hparam_kernel
import Submission.Work.MotAS.ASRulV2M.fwVecAS2_three_notMem_x
import Submission.Work.MotAS.Nodes.ASResidualPrimeInputs.ziasMinimalPrimes_height
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.MotAS.RouteZ

open MvPolynomial

/-- **Route Z**: `Frac (A[T]) ≅ k` for the residue field `k` of a height-one prime `x` containing
`sAS2`. -/
theorem routeZ_gen {K : Type} [Field K] [CharP K 5] (a b g : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : b ≠ 2 * a) (hA : a ^ 2 - a * b - b ^ 2 ≠ 0) (hg : g ≠ 0)
    (x : Work.MotA.polySpec K 3)
    (hx : sAS2 a b g ∈ x.asIdeal)
    (hfw : fwVecAS2 a b g 0 ∉ x.asIdeal)
    (hw3 : fwVecAS2 a b g 3 ∉ x.asIdeal)
    (hDZ : IsDomain (MvPolynomial (Fin 3) K ⧸ Ideal.radical (ZIAS a b g)))
    (hAtr : Algebra.trdeg K (FractionRing (MvPolynomial (Fin 3) K ⧸
      Ideal.radical (ZIAS a b g))) ≤ 1)
    (htr : Algebra.trdeg K (FractionRing (MvPolynomial (Fin 3) K ⧸ x.asIdeal)) = 2) :
    Nonempty (Work.MotV.resF K x ≃ₐ[K]
      FractionRing (Polynomial (MvPolynomial (Fin 3) K ⧸ Ideal.radical (ZIAS a b g)))) := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  let I : Ideal (MvPolynomial (Fin 3) K) := x.asIdeal
  haveI hIprime : I.IsPrime := x.isPrime
  haveI hcharA : CharP (MvPolynomial (Fin 3) K ⧸ I) 5 := by
    refine (CharP.charP_iff_prime_eq_zero (R := MvPolynomial (Fin 3) K ⧸ I)
      (by norm_num)).mpr ?_
    show ((5 : ℕ) : MvPolynomial (Fin 3) K ⧸ I) = 0
    have h : ((5 : ℕ) : MvPolynomial (Fin 3) K) = 0 := CharP.cast_eq_zero _ 5
    exact (map_natCast (Ideal.Quotient.mk I) 5).symm.trans (by rw [h, map_zero])
  let k := FractionRing (MvPolynomial (Fin 3) K ⧸ I)
  haveI hkdom : IsDomain (MvPolynomial (Fin 3) K ⧸ I) := Ideal.Quotient.isDomain I
  haveI hkfr : IsFractionRing (MvPolynomial (Fin 3) K ⧸ I) k := inferInstance
  let f : MvPolynomial (Fin 3) K →+* k :=
    (algebraMap (MvPolynomial (Fin 3) K ⧸ I) k).comp (Ideal.Quotient.mk I)
  have hfker : ∀ q : MvPolynomial (Fin 3) K, f q = 0 ↔ q ∈ I := by
    intro q
    constructor
    · intro h
      have hq : (Ideal.Quotient.mk I q) = 0 := by
        apply IsFractionRing.injective (MvPolynomial (Fin 3) K ⧸ I) k
        rw [map_zero]
        exact h
      exact (Ideal.Quotient.eq_zero_iff_mem).mp hq
    · intro h
      change (algebraMap (MvPolynomial (Fin 3) K ⧸ I) k) ((Ideal.Quotient.mk I) q) = 0
      rw [(Ideal.Quotient.eq_zero_iff_mem).mpr h, map_zero]
  have hfC : ∀ c : K, f (MvPolynomial.C c) = algebraMap K k c := by
    intro c
    rw [← MvPolynomial.algebraMap_eq K (Fin 3)]
    change (algebraMap (MvPolynomial (Fin 3) K ⧸ I) k)
      ((Ideal.Quotient.mk I) ((algebraMap K (MvPolynomial (Fin 3) K)) c)) = algebraMap K k c
    rw [Ideal.Quotient.mk_algebraMap]
    exact (IsScalarTower.algebraMap_apply K (MvPolynomial (Fin 3) K ⧸ I) k c).symm
  have h5k : (5 : k) = 0 := by
    rw [← map_ofNat (algebraMap K k) 5, h5, map_zero]
  set Yv : Fin 5 → MvPolynomial (Fin 3) K := ASrulYv K a b with hYv
  set y : Fin 5 → k := fun i => f (Yv i) with hy
  set c : Fin 5 → k := fun i => f (fwVecAS2 a b g i) with hc
  have hsec : kleinSecAS (algebraMap K k a) (algebraMap K k b) (algebraMap K k g) y = 0 := by
    have hnat := KleinTwScalarAS_map_kleinSecAS
      (φ := f) (a := MvPolynomial.C a)
      (b := MvPolynomial.C b) (g := MvPolynomial.C g) (y := Yv)
    rw [hfC a, hfC b, hfC g] at hnat
    have h0 : f (sAS2 a b g) = 0 := (hfker _).mpr hx
    rw [show sAS2 a b g = kleinSecAS (MvPolynomial.C a)
        (MvPolynomial.C b) (MvPolynomial.C g) Yv from rfl] at h0
    rw [← hnat] at h0
    exact h0
  have hc_eq : c = kleinPAS (algebraMap K k a) (algebraMap K k b)
      (algebraMap K k g) y := by
    have hnat := KleinTwScalarAS_map_kleinPAS
      (φ := f) (a := MvPolynomial.C a)
      (b := MvPolynomial.C b) (g := MvPolynomial.C g) (y := Yv)
    rw [hfC a, hfC b, hfC g] at hnat
    funext i
    show f (kleinPAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g) Yv i)
      = kleinPAS (algebraMap K k a) (algebraMap K k b) (algebraMap K k g)
          (fun j => f (Yv j)) i
    rw [← congrFun hnat i]
  have hkleinRAS : kleinRAS (algebraMap K k a) (algebraMap K k b) (algebraMap K k g) c = 0 := by
    have hv := KleinTwScalarASv (algebraMap K k a) (algebraMap K k b)
      (algebraMap K k g) y h5k
    rw [← hc_eq] at hv
    rw [hsec] at hv
    funext i
    simpa using congrFun hv i
  have hc0 : c 0 ≠ 0 := fun h => hfw ((hfker (fwVecAS2 a b g 0)).mp h)
  have hc3 : c 3 ≠ 0 := fun h => hw3 ((hfker (fwVecAS2 a b g 3)).mp h)
  have hc4 : c 4 = 0 := by
    show f (fwVecAS2 a b g 4) = 0
    rw [fwVecAS2_four_zero a b g, map_zero]
  set u : k := c 1 / c 0 with hu
  set v : k := c 2 / c 0 with hv'
  set w : k := c 3 / c 0 with hw'
  have hw0 : w ≠ 0 := by
    rw [hw']
    exact div_ne_zero hc3 hc0
  have hcvec : c = c 0 • (![1, u, v, w, 0] : Fin 5 → k) := by
    funext i
    fin_cases i
    · show c 0 = c 0 * 1
      refl_ring1
    · show c 1 = c 0 * u
      rw [hu, mul_comm]
      exact (div_mul_cancel₀ _ hc0).symm
    · show c 2 = c 0 * v
      rw [hv', mul_comm]
      exact (div_mul_cancel₀ _ hc0).symm
    · show c 3 = c 0 * w
      rw [hw', mul_comm]
      exact (div_mul_cancel₀ _ hc0).symm
    · show c 4 = c 0 * 0
      rw [hc4, mul_zero]
  have hvec4 : (![c 0, c 1, c 2, c 3, 0] : Fin 5 → k) = c := by
    funext i
    fin_cases i <;> simp [hc4]
  have hbaseRAS : kleinRAS (algebraMap K k a) (algebraMap K k b) (algebraMap K k g)
      ![1, u, v, w, 0] = 0 := by
    refine kleinRAS_chart_eq_zero (algebraMap K k a) (algebraMap K k b)
      (algebraMap K k g) (c 0) (c 1) (c 2) (c 3) hc0 ?_
    rw [hvec4]
    exact hkleinRAS
  have hbase : ∀ j : Fin 5, MvPolynomial.eval ![u, v, w]
      (zcubAS (algebraMap K k a) (algebraMap K k b) (algebraMap K k g) j) = 0 := by
    intro j
    rw [zcubAS_eval_eq]
    exact congrFun hbaseRAS j
  have hker : Matrix.mulVec (AmatAS2 (algebraMap K k a) (algebraMap K k b)
      (algebraMap K k g) ![1, u, v, w, 0]) y = 0 := by
    have h1 := AmatAS2_mulVec_of_kleinPAS (algebraMap K k a) (algebraMap K k b)
      (algebraMap K k g) h5k y
    rw [← hc_eq] at h1
    rw [hcvec] at h1
    rw [AmatAS2_mulVec_smul] at h1
    exact (smul_eq_zero.mp h1).resolve_left hc0
  have h2ne : (2 : K) ≠ 0 := by
    intro h
    have hdvd : 5 ∣ 2 := (CharP.cast_eq_zero_iff K 5 2).mp h
    norm_num at hdvd
  have hunit : ∀ c' : K, c' ≠ 0 → IsUnit (MvPolynomial.C c' : MvPolynomial (Fin 3) K) := by
    intro c' hc'
    refine ⟨⟨MvPolynomial.C c', MvPolynomial.C c'⁻¹, ?_, ?_⟩, rfl⟩
    · rw [← map_mul, mul_inv_cancel₀ hc', map_one]
    · rw [← map_mul, inv_mul_cancel₀ hc', map_one]
  have hCmem : ∀ c' : K, (MvPolynomial.C c' : MvPolynomial (Fin 3) K) ∈ I ↔ c' = 0 := by
    intro c'
    constructor
    · intro hc'
      by_contra hne
      exact hIprime.ne_top (Ideal.eq_top_of_isUnit_mem I hc' (hunit c' hne))
    · intro h
      rw [h, map_zero]
      exact I.zero_mem
  have hmap0 : ∀ c' : K, algebraMap K k c' = 0 ↔ c' = 0 := by
    intro c'
    rw [← hfC c', hfker]
    exact hCmem c'
  have ha' : algebraMap K k a ≠ 0 := fun h => ha ((hmap0 a).mp h)
  have hb' : algebraMap K k b ≠ 0 := fun h => hb ((hmap0 b).mp h)
  have hg' : algebraMap K k g ≠ 0 := fun h => hg ((hmap0 g).mp h)
  have hA' : algebraMap K k a ^ 2 - algebraMap K k a * algebraMap K k b
      - algebraMap K k b ^ 2 ≠ 0 := by
    intro h
    apply hA
    refine (hmap0 (a ^ 2 - a * b - b ^ 2)).mp ?_
    rw [map_sub, map_sub, map_mul, map_pow, map_pow]
    exact h
  have hab' : algebraMap K k b ≠ 2 * algebraMap K k a := by
    intro h
    apply hab
    have h0 : b - 2 * a = 0 := by
      refine (hmap0 (b - 2 * a)).mp ?_
      rw [map_sub, map_mul, map_ofNat, h]
      refl_ring1
    linear_combination (norm := refl_ring1) h0
  have hAne : 2 * algebraMap K k a - algebraMap K k b ≠ 0 := by
    intro h
    exact hab' (by linear_combination (-1) * h)
  have hBne : algebraMap K k a + 2 * algebraMap K k b ≠ 0 := by
    intro h
    apply hAne
    linear_combination (norm := refl_ring1) 2 * h + (-(algebraMap K k b)) * h5k
  have hy4 : y 4 ≠ 0 := by
    show f (Yv 4) ≠ 0
    rw [hYv, ASrulYv_four, hfC]
    intro h
    rcases mul_eq_zero.mp ((hmap0 (2 * (a ^ 2 - a * b - b ^ 2))).mp h) with h' | h'
    · exact h2ne h'
    · exact hA h'
  have hchart : ∀ j : Fin 3, y (asCh3 j) = y 4 * f (MvPolynomial.X j) := by
    intro j
    show f (Yv (asCh3 j)) = f (Yv 4) * f (MvPolynomial.X j)
    rw [hYv, ASrulYv_ch3 K a b j, map_mul]
  have hrat := ASRulV2M.hparam_kernel (algebraMap K k a) (algebraMap K k b)
    (algebraMap K k g) u v w y ha' hb' hab' hg' hw0 hy4 hbase hker
  have hRv3 : MvPolynomial.eval ![u, v, w]
      (ASRul.kbRv (algebraMap K k a) (algebraMap K k b) (algebraMap K k g) 3)
      = (2 * algebraMap K k a - algebraMap K k b)
          * (algebraMap K k a + 2 * algebraMap K k b) * w ^ 2 :=
    eval_kbRv_three _ _ _ u v w
  have hRw4 : MvPolynomial.eval ![u, v, w]
      (ASRul.kbRw (algebraMap K k a) (algebraMap K k b) (algebraMap K k g) 4)
      = (2 * algebraMap K k a - algebraMap K k b)
          * (algebraMap K k a + 2 * algebraMap K k b) ^ 2 * w ^ 2 :=
    eval_kbRw_four _ _ _ u v w
  let τ : k := (algebraMap K k a + 2 * algebraMap K k b) * (y 3 / y 4)
  have hcleared : ∀ j : Fin 3,
      (MvPolynomial.eval ![u, v, w] (ASRul.kbRw (algebraMap K k a) (algebraMap K k b)
          (algebraMap K k g) 4)) * f (MvPolynomial.X j)
        = (MvPolynomial.eval ![u, v, w] (ASRul.kbRv (algebraMap K k a)
            (algebraMap K k b) (algebraMap K k g) (asCh3 j))) * τ
          + (MvPolynomial.eval ![u, v, w] (ASRul.kbRw (algebraMap K k a)
              (algebraMap K k b) (algebraMap K k g) (asCh3 j))) := by
    intro j
    have hxj : f (MvPolynomial.X j) = y (asCh3 j) / y 4 := by
      rw [hchart j, eq_div_iff hy4]
      refl_ring1
    rw [hxj, hrat j, hRv3, hRw4]
    simp only [τ]
    exact div_key_s (2 * algebraMap K k a - algebraMap K k b)
      (algebraMap K k a + 2 * algebraMap K k b) (w ^ 2) (y 3 / y 4)
      (MvPolynomial.eval ![u, v, w] (ASRul.kbRv (algebraMap K k a) (algebraMap K k b)
        (algebraMap K k g) (asCh3 j)))
      (MvPolynomial.eval ![u, v, w] (ASRul.kbRw (algebraMap K k a) (algebraMap K k b)
        (algebraMap K k g) (asCh3 j)))
      hAne hBne (pow_ne_zero 2 hw0)
  let ev : MvPolynomial (Fin 3) K →+* k :=
    (MvPolynomial.eval ![u, v, w]).comp (MvPolynomial.map (algebraMap K k))
  have hev_C : ∀ c' : K, ev (MvPolynomial.C c') = algebraMap K k c' := fun c' => by simp [ev]
  have hev_kbRv : ∀ i : Fin 5, ev (ASRul.kbRv a b g i)
      = MvPolynomial.eval ![u, v, w] (ASRul.kbRv (algebraMap K k a)
          (algebraMap K k b) (algebraMap K k g) i) := by
    intro i
    simp only [ev, RingHom.comp_apply]
    rw [map_kbRv_s]
  have hev_kbRw : ∀ i : Fin 5, ev (ASRul.kbRw a b g i)
      = MvPolynomial.eval ![u, v, w] (ASRul.kbRw (algebraMap K k a)
          (algebraMap K k b) (algebraMap K k g) i) := by
    intro i
    simp only [ev, RingHom.comp_apply]
    rw [map_kbRw_s]
  have hev_zcub : ∀ j : Fin 5, ev (zcubAS a b g j) = 0 := by
    intro j
    simp only [ev, RingHom.comp_apply]
    rw [map_zcubAS_s]
    exact hbase j
  have hleev : Ideal.radical (ZIAS a b g) ≤ RingHom.ker ev := by
    refine (RingHom.ker_isPrime ev).isRadical.radical_le_iff.mpr ?_
    rw [ZIAS, Ideal.span_le]
    rintro q ⟨j, rfl⟩
    exact RingHom.mem_ker.mpr (hev_zcub j)
  haveI hAdom : IsDomain (RZA K a b g) := hDZ
  let ψ : RZA K a b g →+* k := Ideal.Quotient.lift (Ideal.radical (ZIAS a b g)) ev hleev
  have hψ_mk : ∀ q : MvPolynomial (Fin 3) K,
      ψ (Ideal.Quotient.mk (Ideal.radical (ZIAS a b g)) q) = ev q :=
    fun q => Ideal.Quotient.lift_mk _ ev hleev
  let φ : Polynomial (RZA K a b g) →+* k := Polynomial.eval₂RingHom ψ τ
  have hφC : ∀ q : RZA K a b g, φ (Polynomial.C q) = ψ q := fun q => by
    rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
  have hφX : φ Polynomial.X = τ := by
    rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  have hψK : ∀ r : K, ψ (algebraMap K (RZA K a b g) r) = algebraMap K k r := by
    intro r
    rw [show algebraMap K (RZA K a b g) r = Ideal.Quotient.mk (Ideal.radical (ZIAS a b g))
        (algebraMap K (MvPolynomial (Fin 3) K) r) from
      (Ideal.Quotient.mk_algebraMap K (Ideal.radical (ZIAS a b g)) r).symm]
    rw [hψ_mk, MvPolynomial.algebraMap_eq K (Fin 3)]
    exact hev_C r
  let φa : Polynomial (RZA K a b g) →ₐ[K] k :=
    { toRingHom := φ
      commutes' := fun r => by
        have h1 : algebraMap K (Polynomial (RZA K a b g)) r
            = Polynomial.C (algebraMap K (RZA K a b g) r) :=
          (IsScalarTower.algebraMap_apply K (RZA K a b g) (Polynomial (RZA K a b g)) r).trans
            (Polynomial.C_eq_algebraMap (algebraMap K (RZA K a b g) r)).symm
        show φ (algebraMap K (Polynomial (RZA K a b g)) r) = algebraMap K k r
        rw [h1]
        exact (hφC _).trans (hψK r) }
  have hdiv_mem : ∀ {x y : k}, x ∈ Subfield.closure (Set.range φ) →
      y ∈ Subfield.closure (Set.range φ) → x / y ∈ Subfield.closure (Set.range φ) := by
    intro x y hx hy
    rw [div_eq_mul_inv]
    exact Subfield.mul_mem (s := Subfield.closure (Set.range φ)) hx
      (Subfield.inv_mem (s := Subfield.closure (Set.range φ)) hy)
  -- ## `ev` lands in the range of `φ`
  have hev_range : ∀ q : MvPolynomial (Fin 3) K, ev q = φ (Polynomial.C
      (Ideal.Quotient.mk (Ideal.radical (ZIAS a b g)) q)) := fun q =>
    (hψ_mk q).symm.trans (hφC _).symm
  have hev_mem : ∀ q : MvPolynomial (Fin 3) K,
      ev q ∈ Subfield.closure (Set.range φ) := fun q => (hev_range q).symm ▸
    Subfield.subset_closure (Set.mem_range_self (Polynomial.C
      (Ideal.Quotient.mk (Ideal.radical (ZIAS a b g)) q)))
  -- ## `y 3 / y 4` lies in the closure of the range
  have ht_mem : y 3 / y 4 ∈ Subfield.closure (Set.range φ) := by
    have h1 : y 3 / y 4 = τ * (algebraMap K k a + 2 * algebraMap K k b)⁻¹ := by
      show y 3 / y 4 = ((algebraMap K k a + 2 * algebraMap K k b) * (y 3 / y 4))
        * (algebraMap K k a + 2 * algebraMap K k b)⁻¹
      rw [mul_assoc, mul_comm (y 3 / y 4) ((algebraMap K k a + 2 * algebraMap K k b)⁻¹),
        ← mul_assoc, mul_inv_cancel₀ hBne, one_mul]
    rw [h1]
    refine Subfield.mul_mem (s := Subfield.closure (Set.range φ)) ?_
      (Subfield.inv_mem (s := Subfield.closure (Set.range φ)) ?_)
    · exact hφX ▸ Subfield.subset_closure (Set.mem_range_self Polynomial.X)
    · have h2 : algebraMap K k (a + 2 * b)
          = algebraMap K k a + 2 * algebraMap K k b := by
        rw [map_add, map_mul, map_ofNat]
      rw [← h2, ← hev_C (a + 2 * b)]
      exact hev_mem (MvPolynomial.C (a + 2 * b))
  -- ## the generators of `B` lie in the closure of the range
  have hfX : ∀ i : Fin 3, f (MvPolynomial.X i) ∈ Subfield.closure (Set.range φ) := by
    intro i
    have h1 : f (MvPolynomial.X i) = y (asCh3 i) / y 4 := by
      rw [eq_div_iff hy4, hchart i]
      refl_ring1
    rw [h1, hrat i, ← hev_kbRv (asCh3 i), ← hev_kbRv 3, ← hev_kbRw (asCh3 i),
      ← hev_kbRw 4]
    refine Subfield.add_mem (s := Subfield.closure (Set.range φ)) ?_ ?_
    · exact hdiv_mem (Subfield.mul_mem (s := Subfield.closure (Set.range φ)) ht_mem
        (hev_mem (ASRul.kbRv a b g (asCh3 i)))) (hev_mem (ASRul.kbRv a b g 3))
    · exact hdiv_mem (hev_mem (ASRul.kbRw a b g (asCh3 i))) (hev_mem (ASRul.kbRw a b g 4))
  have hf_mem : ∀ q : MvPolynomial (Fin 3) K, f q ∈ Subfield.closure (Set.range f) := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C r => exact Subfield.subset_closure (Set.mem_range_self (MvPolynomial.C r))
    | add p q hp hq =>
        rw [map_add]
        exact Subfield.add_mem (s := Subfield.closure (Set.range f)) hp hq
    | mul_X p i hp =>
        rw [map_mul]
        exact Subfield.mul_mem (s := Subfield.closure (Set.range f)) hp
          (Subfield.subset_closure (Set.mem_range_self (MvPolynomial.X i)))
  have hf_closure : Subfield.closure (Set.range f) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj (nonZeroDivisors (MvPolynomial (Fin 3) K ⧸ I)) z
    obtain ⟨p', hp'⟩ := Ideal.Quotient.mk_surjective (p : MvPolynomial (Fin 3) K ⧸ I)
    obtain ⟨q', hq'⟩ := Ideal.Quotient.mk_surjective (q : MvPolynomial (Fin 3) K ⧸ I)
    have hfp : f p' = algebraMap (MvPolynomial (Fin 3) K ⧸ I) k p := by
      show algebraMap (MvPolynomial (Fin 3) K ⧸ I) k (Ideal.Quotient.mk I p') = _
      rw [hp']
    have hfq' : f q' = algebraMap (MvPolynomial (Fin 3) K ⧸ I) k q := by
      show algebraMap (MvPolynomial (Fin 3) K ⧸ I) k (Ideal.Quotient.mk I q') = _
      rw [hq']
    have hfq : f q' ≠ 0 := by
      rw [hfq']
      intro h0
      exact (mem_nonZeroDivisors_iff_ne_zero.mp q.2)
        (IsFractionRing.injective (MvPolynomial (Fin 3) K ⧸ I) k (by rw [h0, map_zero]))
    have hz2 : z = algebraMap (MvPolynomial (Fin 3) K ⧸ I) k p *
        (algebraMap (MvPolynomial (Fin 3) K ⧸ I) k q)⁻¹ := by
      rw [← hpq, mul_assoc, mul_inv_cancel₀ (by rw [← hfq']; exact hfq), mul_one]
    rw [hz2, ← hfp, ← hfq']
    exact Subfield.mul_mem (s := Subfield.closure (Set.range f)) (hf_mem p')
      (Subfield.inv_mem (s := Subfield.closure (Set.range f)) (hf_mem q'))
  have hrange_f_sub : Set.range f ⊆ Subfield.closure (Set.range φ) := by
    rintro _ ⟨q, rfl⟩
    induction q using MvPolynomial.induction_on with
    | C r => rw [hfC r, ← hev_C r]; exact hev_mem (MvPolynomial.C r)
    | add p q hp hq =>
        rw [map_add]
        exact Subfield.add_mem (s := Subfield.closure (Set.range φ)) hp hq
    | mul_X p i hp =>
        rw [map_mul]
        exact Subfield.mul_mem (s := Subfield.closure (Set.range φ)) hp (hfX i)
  have hφclosure : Subfield.closure (Set.range φ) = ⊤ := by
    rw [eq_top_iff, ← hf_closure]
    exact Subfield.closure_le.mpr hrange_f_sub
  have hcl : Subfield.closure (Set.range (algebraMap ↥φa.range k)) = ⊤ := by
    rw [eq_top_iff, ← hφclosure]
    refine Subfield.closure_le.mpr ?_
    rintro x ⟨r, rfl⟩
    exact Subfield.subset_closure (Set.mem_range_self (⟨φa r, ⟨r, rfl⟩⟩ : ↥φa.range))
  obtain ⟨e1⟩ := fractionRing_algEquiv_of_closure_eq_top_s (K := K) (L := k) φa.range hcl
  have hφa_closure : Subfield.closure (Set.range φa) = ⊤ := hφclosure
  have hfinj : Function.Injective φa :=
    ASRulV2M.injective_of_trdeg_of_subfield_closure (A := RZA K a b g) hAtr φa hφa_closure htr
  have hiso : Nonempty (Polynomial (RZA K a b g) ≃ₐ[K] ↥φa.range) :=
    ⟨AlgEquiv.ofBijective (AlgHom.rangeRestrict φa)
      ⟨fun x y h => hfinj (congrArg Subtype.val h),
       AlgHom.rangeRestrict_surjective φa⟩⟩
  obtain ⟨e2⟩ : Nonempty (FractionRing (Polynomial (RZA K a b g)) ≃ₐ[K]
      FractionRing ↥φa.range) :=
    ⟨IsFractionRing.algEquivOfAlgEquiv (R := K) (A := Polynomial (RZA K a b g))
      (B := ↥φa.range) hiso.some⟩
  exact ⟨(e2.trans e1).symm⟩

/-! ## Instantiation for `𝕜` of characteristic `5` and the AS Klein data `D` -/

theorem fAS_ne_zero_s {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5] : Work.MotV.fAS 𝕜 ≠ 0 := by
  have hX : (Polynomial.X : Polynomial 𝕜) ≠ 0 := Polynomial.monic_X.ne_zero
  have h2 : (Polynomial.X ^ 2 + 1 : Polynomial 𝕜) ≠ 0 := by
    simpa using (Polynomial.monic_X_pow_add_C (a := (1 : 𝕜)) (n := 2) (by norm_num)).ne_zero
  have hfac : (Polynomial.X ^ 3 + Polynomial.X : Polynomial 𝕜)
      = Polynomial.X * (Polynomial.X ^ 2 + 1) := by ring
  have hpoly : (Polynomial.X ^ 3 + Polynomial.X : Polynomial 𝕜) ≠ 0 := by
    rw [hfac]
    exact mul_ne_zero hX h2
  have hfAS : Work.MotV.fAS 𝕜
      = algebraMap (Polynomial 𝕜) (RatFunc 𝕜) (Polynomial.X ^ 3 + Polynomial.X) := by
    show RatFunc.X ^ 3 + RatFunc.X
      = algebraMap (Polynomial 𝕜) (RatFunc 𝕜) (Polynomial.X ^ 3 + Polynomial.X)
    rw [← RatFunc.algebraMap_X, ← map_pow, ← map_add]
  intro h
  exact hpoly (IsFractionRing.injective (Polynomial 𝕜) (RatFunc 𝕜)
    (by rw [← hfAS, h, map_zero]))

/-- **Route Z, specialised**: the residue field of a height-one prime containing `sAS2` is the
function field of `residual curve × 𝔸¹`. -/
theorem routeZ_AS (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (x : Work.MotA.polySpec (RatFunc 𝕜) 3)
    (hcoh : Order.coheight x = 1)
    (hx : sAS2 (aK D) (bK D) (Work.MotV.fAS 𝕜) ∈ x.asIdeal)
    (hfw : fwVecAS2 (aK D) (bK D) (Work.MotV.fAS 𝕜) 0 ∉ x.asIdeal)
    (hDZ : IsDomain (MvPolynomial (Fin 3) (RatFunc 𝕜) ⧸
      Ideal.radical (ZIAS (aK D) (bK D) (Work.MotV.fAS 𝕜)))) :
    Nonempty (Work.MotV.resF (RatFunc 𝕜) x ≃ₐ[RatFunc 𝕜]
      FractionRing (Polynomial (MvPolynomial (Fin 3) (RatFunc 𝕜) ⧸
        Ideal.radical (ZIAS (aK D) (bK D) (Work.MotV.fAS 𝕜))))) := by
  have ha : aK D ≠ 0 := by
    intro h
    have h0 : D.a = 0 := FaithfulSMul.algebraMap_injective 𝕜 (RatFunc 𝕜)
      (by rw [show (algebraMap 𝕜 (RatFunc 𝕜)) D.a = 0 from h, map_zero])
    exact hD.1.ab_ne (by rw [h0, zero_mul])
  have hb : bK D ≠ 0 := by
    intro h
    have h0 : D.b = 0 := FaithfulSMul.algebraMap_injective 𝕜 (RatFunc 𝕜)
      (by rw [show (algebraMap 𝕜 (RatFunc 𝕜)) D.b = 0 from h, map_zero])
    exact hD.1.ab_ne (by rw [h0, mul_zero])
  have hA : aK D ^ 2 - aK D * bK D - bK D ^ 2 ≠ 0 := aK_sq_sub_ne D hD
  have hg : Work.MotV.fAS 𝕜 ≠ 0 := fAS_ne_zero_s
  have h5 : (5 : RatFunc 𝕜) = 0 := CharP.cast_eq_zero _ 5
  have hab : bK D ≠ 2 * aK D := by
    intro h
    apply hA
    rw [h]
    linear_combination (norm := refl_ring1 (mod := 5))
  have hw3 : fwVecAS2 (aK D) (bK D) (Work.MotV.fAS 𝕜) 3 ∉ x.asIdeal :=
    Work.MotAS.ASRulV2M.fwVecAS2_three_notMem_x 𝕜 D hD x hcoh hx
  have hAtr : Algebra.trdeg (RatFunc 𝕜) (FractionRing (MvPolynomial (Fin 3) (RatFunc 𝕜) ⧸
      Ideal.radical (ZIAS (aK D) (bK D) (Work.MotV.fAS 𝕜)))) ≤ 1 := by
    haveI hIprime : (Ideal.radical (ZIAS (aK D) (bK D) (Work.MotV.fAS 𝕜))).IsPrime :=
      (Ideal.Quotient.isDomain_iff_prime
        (Ideal.radical (ZIAS (aK D) (bK D) (Work.MotV.fAS 𝕜)))).mp hDZ
    have h2 : (2 : ℕ) ≤
        (Ideal.radical (ZIAS (aK D) (bK D) (Work.MotV.fAS 𝕜))).height := by
      rw [Ideal.height_eq_inf_minimalPrimes, Ideal.radical_minimalPrimes]
      exact le_iInf₂ fun 𝔭 h𝔭 =>
        Work.MotAS.Nodes.ASResidualPrimeInputs.ziasMinimalPrimes_height 𝕜 D hD 𝔭 h𝔭
    have h3 := Work.MotAS.ASRulV2M.trdeg_quotient_add_height (K := RatFunc 𝕜) 3
      (Ideal.radical (ZIAS (aK D) (bK D) (Work.MotV.fAS 𝕜))) 2 h2
    have h4 : Algebra.trdeg (RatFunc 𝕜) (FractionRing (MvPolynomial (Fin 3) (RatFunc 𝕜) ⧸
        Ideal.radical (ZIAS (aK D) (bK D) (Work.MotV.fAS 𝕜)))) + (2 : ℕ) ≤
        (1 : Cardinal) + (2 : ℕ) := by
      rw [show (1 : Cardinal) + (2 : ℕ) = (3 : Cardinal) by norm_num]
      exact h3
    exact (Cardinal.add_nat_le_add_nat_iff 2).mp h4
  have htr : Algebra.trdeg (RatFunc 𝕜) (FractionRing (MvPolynomial (Fin 3) (RatFunc 𝕜) ⧸
      x.asIdeal)) = 2 := by
    obtain ⟨p, hpprime, hxeq⟩ := (Work.MotA.coheight_eq_one_iff (RatFunc 𝕜) 3 x).mp hcoh
    rw [hxeq]
    exact Work.MotAS.ASRulV2M.trdeg_span_prime_eq_two (K := RatFunc 𝕜) p hpprime
  exact routeZ_gen (aK D) (bK D) (Work.MotV.fAS 𝕜) ha hb hab hA hg x hx hfw hw3 hDZ hAtr htr

end Work.MotAS.RouteZ
