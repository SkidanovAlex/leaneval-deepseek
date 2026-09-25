import Mathlib
import Submission.NK.NUV2.RouteB.RayModulus.Defs
import Submission.NK.HeckeL.Basic
import Submission.NK.HeckeL.Basic.ideleOfIdeal_mul
import Submission.NK.HeckeL.Basic.ideal_eq_prod_finsupp
import Submission.NK.CFTLib.Arl.Defs
import Submission.NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust
import Submission.NK.GlobalCFT.IdeleClassGroup.globalCFT_idealClassMap_exists
import Submission.NK.NUV2.RouteB.RayModulus.exists_mem_fractionalIdeal_cong_pos

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open NumberField IsDedekindDomain
open scoped NumberField nonZeroDivisors
open NK.GlobalCFT (Idele IdeleClassGroup Place)

noncomputable section

namespace NK.NUV2.RouteB.RayModulus

variable {K : Type} [Field K] [NumberField K]

/-! ## Idèles attached to fractional ideals -/

/-- The exponent of the inverse idèle is the negative of the exponent. -/
theorem exp_inv (q : HeightOneSpectrum (𝓞 K)) (x : Idele K) :
    Idele.exp q x⁻¹ = -Idele.exp q x := by
  have h := Idele.exp_mul q x x⁻¹
  rw [mul_inv_cancel, Idele.exp_one] at h
  linarith [h]

/-- An idèle is a local unit at `q` iff its exponent at `q` vanishes. -/
theorem mem_localUnits_iff_exp_eq_zero (q : HeightOneSpectrum (𝓞 K)) (x : Idele K) :
    x (Place.ofFinite q) ∈ Place.localUnits K (Place.ofFinite q) ↔ Idele.exp q x = 0 := by
  rw [Place.mem_localUnits_ofFinite_iff_valued_eq_one, Idele.exp_val, WithZero.exp_eq_one]
  simp

/-- The idèle attached to a fractional ideal: `1` at the archimedean places and the `f q`-th
power of a local uniformiser at the finite place `q`. -/
abbrev fracIdele (T : FractionalIdeal (𝓞 K)⁰ K) : Idele K :=
  IdeleClassGroup.ideleOfFun K (fun q => FractionalIdeal.count K q T)
    (FractionalIdeal.finite_factors T)

theorem ideleOfIdeal_eq_fracIdele (I : Ideal (𝓞 K)) :
    NK.HeckeL.ideleOfIdeal K I = fracIdele (I : FractionalIdeal (𝓞 K)⁰ K) := rfl

theorem fracIdele_idealOf (x : Idele K) :
    fracIdele (Idele.idealOf x)
      = IdeleClassGroup.ideleOfFun K (fun q => Idele.exp q x)
          (Filter.eventually_cofinite.mpr (Idele.finite_exp_support x)) := by
  refine NK.HeckeL.Basic.IdeleFun.congr _ _ ?_
  funext q
  exact Idele.count_idealOf x q

theorem fracIdele_mul {I J : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0) :
    fracIdele (I * J) = fracIdele I * fracIdele J := by
  have hsum : ∀ᶠ q in Filter.cofinite,
      ((fun q => FractionalIdeal.count K q I) + (fun q => FractionalIdeal.count K q J)) q = 0 :=
    ((FractionalIdeal.finite_factors I).and (FractionalIdeal.finite_factors J)).mono
      (fun q hq => by simp [Pi.add_apply, hq.1, hq.2])
  have key : (fun q => FractionalIdeal.count K q (I * J))
      = (fun q => FractionalIdeal.count K q I) + (fun q => FractionalIdeal.count K q J) := by
    funext q
    rw [Pi.add_apply, FractionalIdeal.count_mul K q hI hJ]
  change IdeleClassGroup.ideleOfFun K (fun q => FractionalIdeal.count K q (I * J)) _ = _
  trans IdeleClassGroup.ideleOfFun K
      ((fun q => FractionalIdeal.count K q I) + (fun q => FractionalIdeal.count K q J)) hsum
  · exact NK.HeckeL.Basic.IdeleFun.congr _ _ key
  · exact (NK.HeckeL.Basic.IdeleFun.mul _ _ _ _ hsum).symm

/-! ## The "unit part" of an idèle modulo a congruence subgroup -/

/-- If an idèle `a` has the same exponents as `ideleOfFun g`, if `g` vanishes at the primes
carrying the modulus, if `a` is congruent to `1` at those primes and positive at the real
places of `𝔪.pos`, then `a · (ideleOfFun g)⁻¹` lies in the congruence subgroup. -/
theorem mul_inv_ideleOfFun_mem_congSubgroup (𝔪 : Modulus K) (a : Idele K)
    {g : HeightOneSpectrum (𝓞 K) → ℤ} (hg : ∀ᶠ q in Filter.cofinite, g q = 0)
    (hideal : ∀ q, Idele.exp q a = g q)
    (hzero : ∀ q, 𝔪.exps q ≠ 0 → g q = 0)
    (hcong : ∀ q, 𝔪.exps q ≠ 0 →
      NK.NUV2.RouteB.IsCongAt K 𝔪.exps q (a (Place.ofFinite q)))
    (hpos : ∀ (w : InfinitePlace K) (hw : w.IsReal), w ∈ 𝔪.pos →
      0 < (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
        ((a (Place.ofInfinite w) : (w.Completion)ˣ) : w.Completion)) :
    a * (IdeleClassGroup.ideleOfFun K g hg)⁻¹ ∈ CongSubgroup K 𝔪 := by
  classical
  set z : Idele K := a * (IdeleClassGroup.ideleOfFun K g hg)⁻¹ with hz
  have hzexp : ∀ q, Idele.exp q z = 0 := by
    intro q
    rw [hz, Idele.exp_mul, exp_inv, IdeleClassGroup.exp_ideleOfFun, hideal q]
    ring
  have hunit : ∀ q, z (Place.ofFinite q) ∈ Place.localUnits K (Place.ofFinite q) := by
    intro q
    rw [mem_localUnits_iff_exp_eq_zero, hzexp]
  rw [Modulus.mem_congSubgroup_iff]
  refine ⟨fun q => ⟨?_, ?_⟩, ?_⟩
  · rw [← Place.mem_localUnits_ofFinite_iff_valued_eq_one]; exact hunit q
  · by_cases hq : 𝔪.exps q = 0
    · have hv : Valued.v (((z (Place.ofFinite q) : (q.adicCompletion K)ˣ) : q.adicCompletion K))
          = 1 := Place.mem_localUnits_ofFinite_iff_valued_eq_one.mp (hunit q)
      have hle : Valued.v (((z (Place.ofFinite q) : (q.adicCompletion K)ˣ) : q.adicCompletion K) - 1)
          ≤ 1 := Valuation.map_sub_le (v := Valued.v) (g := (1 : WithZero (Multiplicative ℤ)))
            (by rw [hv]) (by rw [Valuation.map_one])
      simpa [NK.NUV2.RouteB.IsCongAt, hq] using hle
    · have hcomp : z (Place.ofFinite q) = a (Place.ofFinite q) := by
        rw [hz, Idele.mul_apply, Idele.inv_apply, NK.HeckeL.Basic.IdeleFun.apply_ofFinite,
          hzero q hq, zpow_zero, inv_one, mul_one]
      rw [hcomp]
      exact hcong q hq
  · intro w hw hmem
    have hcomp : z (Place.ofInfinite w) = a (Place.ofInfinite w) := by
      rw [hz, Idele.mul_apply, Idele.inv_apply,
        show IdeleClassGroup.ideleOfFun K g hg (Place.ofInfinite w) = 1 from rfl, inv_one, mul_one]
    rw [hcomp]
    exact hpos w hw hmem


/-- **Every ray class modulo `𝔪` contains an integral ideal coprime to `𝔪`.**

This is the surjectivity of `I ↦ classOfIdeal K U(𝔪) I` from the integral ideals coprime to the
support of `𝔪` onto the ray class group `𝕀 K ⧸ (Kˣ · U(𝔪))`. -/
theorem exists_ideal_of_class (K : Type) [Field K] [NumberField K] (𝔪 : NK.NUV2.RouteB.Modulus K)
    (c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K (NK.NUV2.RouteB.CongSubgroup K 𝔪)) :
    ∃ I : Ideal (NumberField.RingOfIntegers K), I ≠ 0 ∧
      (∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K), 𝔪.exps q ≠ 0 → ¬ q.asIdeal ∣ I) ∧
      NK.HeckeL.classOfIdeal K (NK.NUV2.RouteB.CongSubgroup K 𝔪) I = c := by
  classical
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective
    (s := Idele.principalSubgroup K ⊔ NK.NUV2.RouteB.CongSubgroup K 𝔪) c
  set M : ℕ := ∏ q ∈ 𝔪.supportFinset, (Ideal.absNorm q.asIdeal) ^ (𝔪.exps q) with hM
  have hMpos : 0 < M := by
    rw [hM]
    refine Finset.prod_pos fun q hq => ?_
    exact pow_pos (Ideal.absNorm_pos_iff_mem_nonZeroDivisors.mpr (by
      rw [mem_nonZeroDivisors_iff_ne_zero]
      simpa using HeightOneSpectrum.ne_bot q)) _
  obtain ⟨V, hV, hadj⟩ := NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust K M hMpos
  obtain ⟨b, hb⟩ := hadj x
  set y : Idele K := x * Idele.principalIdele K b with hy
  have hmem_pow : ∀ q ∈ 𝔪.supportFinset, ((M : ℕ) : 𝓞 K) ∈ q.asIdeal ^ (𝔪.exps q) := by
    intro q hq
    have hcast : ((M : ℕ) : 𝓞 K) =
        ∏ q' ∈ 𝔪.supportFinset, (((Ideal.absNorm q'.asIdeal) ^ (𝔪.exps q') : ℕ) : 𝓞 K) := by
      rw [hM]; push_cast; rfl
    rw [hcast, ← Finset.mul_prod_erase 𝔪.supportFinset _ hq]
    have hbase : (((Ideal.absNorm q.asIdeal) ^ (𝔪.exps q) : ℕ) : 𝓞 K) ∈
        q.asIdeal ^ (𝔪.exps q) := by
      rw [Nat.cast_pow]
      exact Ideal.pow_mem_pow (Ideal.absNorm_mem q.asIdeal) _
    exact Ideal.mul_mem_right _ _ hbase
  have hyV := (hV.1 y).mp hb
  have hmem𝔭 : ∀ q : HeightOneSpectrum (𝓞 K), 𝔪.exps q ≠ 0 → (M : 𝓞 K) ∈ q.asIdeal := by
    intro q hq
    exact (Ideal.pow_le_self hq) (hmem_pow q (Modulus.mem_supportFinset 𝔪 hq))
  have hcong_y : ∀ q, 𝔪.exps q ≠ 0 →
      Valued.v (((y (Place.ofFinite q) : (q.adicCompletion K)ˣ) : q.adicCompletion K) - 1)
        ≤ WithZero.exp (-(𝔪.exps q : ℤ)) := by
    intro q hq
    have h1 : Valued.v (((y (Place.ofFinite q) : (q.adicCompletion K)ˣ) : q.adicCompletion K) - 1)
        ≤ Valued.v (((M : ℕ) : q.adicCompletion K)) := hyV.1 q (hmem𝔭 q hq)
    refine le_trans h1 ?_
    have h2 : (((M : ℕ)) : q.adicCompletion K) =
        algebraMap K (q.adicCompletion K) ((M : K)) := (map_natCast _ M).symm
    rw [h2, Commons.NumberTheory.NumberField.Completion.valued_alg_eq]
    have h3 : ((M : K)) = algebraMap (𝓞 K) K ((M : 𝓞 K)) := (map_natCast _ M).symm
    rw [h3, HeightOneSpectrum.valuation_of_algebraMap]
    exact (HeightOneSpectrum.intValuation_le_pow_iff_mem q ((M : ℕ) : 𝓞 K) (𝔪.exps q)).mpr
      (hmem_pow q (Modulus.mem_supportFinset 𝔪 hq))
  have hzero_y : ∀ q, 𝔪.exps q ≠ 0 → Idele.exp q y = 0 := by
    intro q hq
    have hmlt : Valued.v (((y (Place.ofFinite q) : (q.adicCompletion K)ˣ) : q.adicCompletion K) - 1)
        < 1 := by
      refine lt_of_le_of_lt (hcong_y q hq) ?_
      rw [← WithZero.exp_zero]
      exact WithZero.exp_lt_exp.mpr (by omega)
    have h := Valuation.map_add_eq_of_lt_left (v := Valued.v) (x := (1 : q.adicCompletion K))
      (y := (((y (Place.ofFinite q) : (q.adicCompletion K)ˣ) : q.adicCompletion K) - 1))
      (by rw [Valuation.map_one]; exact hmlt)
    have h2 : (1 : q.adicCompletion K)
        + (((y (Place.ofFinite q) : (q.adicCompletion K)ˣ) : q.adicCompletion K) - 1)
        = ((y (Place.ofFinite q) : (q.adicCompletion K)ˣ) : q.adicCompletion K) := by ring
    rw [h2, Valuation.map_one] at h
    exact (mem_localUnits_iff_exp_eq_zero q y).mp
      (Place.mem_localUnits_ofFinite_iff_valued_eq_one.mpr h)
  have hpos_y : ∀ (w : InfinitePlace K) (hw : w.IsReal), w ∈ 𝔪.pos →
      0 < (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
        ((y (Place.ofInfinite w) : (w.Completion)ˣ) : w.Completion) := by
    intro w hw _
    exact hyV.2 w hw
  have hgyfin : ∀ᶠ q in Filter.cofinite, Idele.exp q y = 0 :=
    Filter.eventually_cofinite.mpr (Idele.finite_exp_support y)
  have hu1 : y * (fracIdele (Idele.idealOf y))⁻¹ ∈ CongSubgroup K 𝔪 := by
    rw [fracIdele_idealOf]
    exact mul_inv_ideleOfFun_mem_congSubgroup 𝔪 y hgyfin (fun q => rfl) hzero_y hcong_y hpos_y
  have h𝔞ne : Idele.idealOf y ≠ 0 := Idele.idealOf_ne_zero y
  obtain ⟨δ, hδmem, hδne, hδcong, hδpos⟩ :=
    exists_mem_fractionalIdeal_cong_pos K 𝔪 (Idele.idealOf y)⁻¹ (inv_ne_zero h𝔞ne)
      (by
        intro q hq
        rw [FractionalIdeal.count_inv, Idele.count_idealOf, hzero_y q hq, neg_zero])
  set δu : Kˣ := Units.mk0 δ hδne with hδu
  have hδuval : (δu : K) = δ := by rw [hδu, Units.val_mk0]
  have hunitδ : ∀ q, 𝔪.exps q ≠ 0 → Valued.v (algebraMap K (q.adicCompletion K) δ) = 1 := by
    intro q hq
    have hlt : Valued.v (algebraMap K (q.adicCompletion K) (δ - 1)) < 1 := by
      refine lt_of_le_of_lt (hδcong q hq) ?_
      rw [← WithZero.exp_zero]
      exact WithZero.exp_lt_exp.mpr (by omega)
    have hop : algebraMap K (q.adicCompletion K) δ
        = (1 : q.adicCompletion K) + algebraMap K (q.adicCompletion K) (δ - 1) := by
      rw [← map_one (algebraMap K (q.adicCompletion K)), ← map_add]
      congr 1
      ring
    rw [hop, Valuation.map_add_eq_of_lt_left (v := Valued.v)
      (x := (1 : q.adicCompletion K))
      (y := algebraMap K (q.adicCompletion K) (δ - 1)) (by rw [Valuation.map_one]; exact hlt),
      Valuation.map_one]
  have hcountδ : ∀ q, 𝔪.exps q ≠ 0 →
      FractionalIdeal.count K q (FractionalIdeal.spanSingleton (𝓞 K)⁰ δ) = 0 := by
    intro q hq
    rw [NK.GlobalCFT.IdeleClassGroup.count_spanSingleton_eq q hδne,
      ← Commons.NumberTheory.NumberField.Completion.valued_alg_eq q δ, hunitδ q hq,
      WithZero.log_one, neg_zero]
  have hδle : FractionalIdeal.spanSingleton (𝓞 K)⁰ δ ≤ (Idele.idealOf y)⁻¹ :=
    FractionalIdeal.spanSingleton_le_iff_mem.mpr hδmem
  have hIle : FractionalIdeal.spanSingleton (𝓞 K)⁰ δ * Idele.idealOf y ≤ 1 := by
    calc FractionalIdeal.spanSingleton (𝓞 K)⁰ δ * Idele.idealOf y
        ≤ (Idele.idealOf y)⁻¹ * Idele.idealOf y := by gcongr
      _ = 1 := inv_mul_cancel₀ h𝔞ne
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hIle
  have hFne : FractionalIdeal.spanSingleton (𝓞 K)⁰ δ * Idele.idealOf y ≠ 0 :=
    mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hδne) h𝔞ne
  have hIne : I ≠ 0 := by
    intro h0
    have h1 : ((I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) = 0 :=
      FractionalIdeal.coeIdeal_eq_zero.mpr (by simpa using h0)
    rw [hI] at h1
    exact hFne h1
  have hcopI : ∀ q, 𝔪.exps q ≠ 0 → ¬ q.asIdeal ∣ I := by
    intro q hq hdvd
    have hc := (NK.HeckeL.Basic.IdealProdFinsupp.count_coe_ne_zero_iff_dvd hIne q).mpr hdvd
    rw [hI, FractionalIdeal.count_mul K q (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hδne) h𝔞ne,
      Idele.count_idealOf, hcountδ q hq, hzero_y q hq, add_zero] at hc
    exact hc rfl
  have hgy2fin : ∀ᶠ q in Filter.cofinite, Idele.exp q (Idele.principalIdele K δu) = 0 :=
    Filter.eventually_cofinite.mpr (Idele.finite_exp_support _)
  have hzeroδ : ∀ q, 𝔪.exps q ≠ 0 → Idele.exp q (Idele.principalIdele K δu) = 0 := by
    intro q hq
    rw [Idele.exp_principalIdele, hδuval,
      ← Commons.NumberTheory.NumberField.Completion.valued_alg_eq q δ, hunitδ q hq,
      WithZero.log_one, neg_zero]
  have hcongδ : ∀ q, 𝔪.exps q ≠ 0 →
      NK.NUV2.RouteB.IsCongAt K 𝔪.exps q (Idele.principalIdele K δu (Place.ofFinite q)) := by
    intro q hq
    have hx : ((Idele.principalIdele K δu (Place.ofFinite q) : (q.adicCompletion K)ˣ) :
        q.adicCompletion K) = algebraMap K (q.adicCompletion K) (δu : K) := by
      rw [Idele.principalIdele_apply, Units.coe_map]
      rfl
    rw [NK.NUV2.RouteB.IsCongAt, hx]
    have h : algebraMap K (q.adicCompletion K) (δu : K) - 1
        = algebraMap K (q.adicCompletion K) (δ - 1) := by
      rw [hδuval, ← map_one (algebraMap K (q.adicCompletion K)), ← map_sub]
    rw [h]
    exact hδcong q hq
  have hposδ : ∀ (w : InfinitePlace K) (hw : w.IsReal), w ∈ 𝔪.pos →
      0 < (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
        ((Idele.principalIdele K δu (Place.ofInfinite w) : (w.Completion)ˣ) : w.Completion) := by
    intro w hw hwpos
    have hx : ((Idele.principalIdele K δu (Place.ofInfinite w) : (w.Completion)ˣ) :
        w.Completion) = algebraMap K w.Completion δ := by
      rw [Idele.principalIdele_apply, Units.coe_map, hδuval]
      rfl
    rw [hx]
    exact hδpos w hw hwpos
  have hu2 : Idele.principalIdele K δu
      * (fracIdele (FractionalIdeal.spanSingleton (𝓞 K)⁰ δ))⁻¹ ∈ CongSubgroup K 𝔪 := by
    have hspan : FractionalIdeal.spanSingleton (𝓞 K)⁰ δ
        = Idele.idealOf (Idele.principalIdele K δu) := by
      rw [Idele.idealOf_principalIdele, hδuval]
    rw [hspan, fracIdele_idealOf]
    exact mul_inv_ideleOfFun_mem_congSubgroup 𝔪 (Idele.principalIdele K δu) hgy2fin (fun q => rfl)
      hzeroδ hcongδ hposδ
  have hFval : (Idele.principalIdele K δu
      * (fracIdele (FractionalIdeal.spanSingleton (𝓞 K)⁰ δ))⁻¹)⁻¹
      * Idele.principalIdele K δu = fracIdele (FractionalIdeal.spanSingleton (𝓞 K)⁰ δ) := by
    rw [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
  have hAval : (y * (fracIdele (Idele.idealOf y))⁻¹)⁻¹ * y = fracIdele (Idele.idealOf y) := by
    rw [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
  have hvalI : (Idele.principalIdele K δu
      * (fracIdele (FractionalIdeal.spanSingleton (𝓞 K)⁰ δ))⁻¹)⁻¹
      * Idele.principalIdele K δu
      * ((y * (fracIdele (Idele.idealOf y))⁻¹)⁻¹ * y)
      = NK.HeckeL.ideleOfIdeal K I := by
    rw [hFval, hAval, ideleOfIdeal_eq_fracIdele, hI,
      ← fracIdele_mul (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hδne) h𝔞ne]
  refine ⟨I, hIne, hcopI, ?_⟩
  show QuotientGroup.mk (NK.HeckeL.ideleOfIdeal K I) = QuotientGroup.mk x
  have hqP : QuotientGroup.mk (Idele.principalIdele K δu)
      = (1 : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K
          (NK.NUV2.RouteB.CongSubgroup K 𝔪)) :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_sup_left ⟨δu, rfl⟩)
  have hqu2 : QuotientGroup.mk ((Idele.principalIdele K δu
      * (fracIdele (FractionalIdeal.spanSingleton (𝓞 K)⁰ δ))⁻¹)⁻¹)
      = (1 : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K
          (NK.NUV2.RouteB.CongSubgroup K 𝔪)) :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_sup_right (Subgroup.inv_mem _ hu2))
  have hqu1 : QuotientGroup.mk ((y * (fracIdele (Idele.idealOf y))⁻¹)⁻¹)
      = (1 : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K
          (NK.NUV2.RouteB.CongSubgroup K 𝔪)) :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_sup_right (Subgroup.inv_mem _ hu1))
  have hqPb : QuotientGroup.mk (Idele.principalIdele K b)
      = (1 : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K
          (NK.NUV2.RouteB.CongSubgroup K 𝔪)) :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_sup_left ⟨b, rfl⟩)
  have hqy : (QuotientGroup.mk y : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K
      (NK.NUV2.RouteB.CongSubgroup K 𝔪)) = QuotientGroup.mk x := by
    rw [hy, QuotientGroup.mk_mul, hqPb, mul_one]
  rw [← hvalI, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
    hqu2, hqP, hqu1, hqy]
  simp


end NK.NUV2.RouteB.RayModulus
