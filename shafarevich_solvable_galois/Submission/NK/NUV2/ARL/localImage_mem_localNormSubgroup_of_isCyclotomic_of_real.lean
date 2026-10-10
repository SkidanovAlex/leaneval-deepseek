import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm_of_finiteDimensional
import Submission.NK.NUV2.ARL.autToPow_artinSym_spanSingleton_natAbs
import Submission.NK.NUV2.ARL.cyclotomic_isComplex
import Submission.NK.NUV2.ARL.norm_neg_of_one_negative_real_place
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Hilbert reciprocity for a cyclotomic prime level at a real place

Let `L = K(ζ_q)` with `q > 2` a prime (so every infinite place of `L` is complex), let `w` be a
*real* place of `K` and `b ∈ Kˣ` an element which is a local norm at every place `v ≠ w`.  Then
`b` is a local norm at `w` as well.

The proof is the archimedean companion of
`NK.NUV2.ARL.localImage_mem_localNormSubgroup_of_isCyclotomic_of_unramified`.  By
`NK.NUV2.ARL.mem_localNormSubgroup_ofInfinite_iff_pos` the local norm group at the real place
`w` is the group of *positive* elements, so the task is to show that `b` is positive at `w`.

* The idèlic Artin map `art : 𝕀 K →* Gal(L/K)` of modulus `q` kills the principal idèles and the
  idèle norms (`NK.NUV2.ARL.exists_artin_of_cyclotomic_prime`), whence
  `art (onePlace w b_w) = 1` (the idèle `P(b)·(onePlace w b_w)⁻¹` has local-norm components).
* The remaining input is the *non*-vanishing `art (onePlace w (-1)) ≠ 1`, which is proved with the
  congruence subgroup `U(q)`: for an integral `c ≡ 1 (mod q)` which is *negative* at `w` and
  positive at every other real place (`NK.CFTLib.Arl.exists_integral_sign_adjust`), the idèle
  `onePlace w (-1) · P(c)` lies in `U(q)`, so by the independence of the adjustment
  `art (onePlace w (-1)) = artinSym ((c))`; evaluating the cyclotomic character of both sides
  (`NK.NUV2.ARL.autToPow_artinSym_spanSingleton_natAbs`) gives `|N(c)| ≡ -1 (mod q)` on the one
  hand and `|N(c)| ≡ 1 (mod q)` (`NK.CFTLib.ARL.norm_sub_one_mem_span`, `N(c) = 1 + q·…`)
  on the other, together with `N(c) < 0`
  (`NK.NUV2.ARL.norm_lt_zero_of_neg_at_one_real_place`); this is a contradiction for `q > 2`.
* Hence `b_w ∈ ker (art ∘ onePlace w) ⊆ {x | x > 0}`, i.e. `b` is positive at `w`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

open scoped NumberField RestrictedProduct nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace NK.NUV2.ARL

open NK.GlobalCFT

section Helpers

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-! ## Auxiliary lemmas -/

/-- The real value of `algebraMap K w.Completion x` is the value of `x` at the real embedding
attached to `w`. -/
theorem ringEquivReal_completion_bridge_aux {w : InfinitePlace K} (hw : w.IsReal) (x : K) :
    InfinitePlace.Completion.ringEquivRealOfIsReal hw (algebraMap K w.Completion x)
      = InfinitePlace.embedding_of_isReal hw x := by
  rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
    InfinitePlace.Completion.algebraMap_apply,
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe]
  simp

/-- Same bridge, for the `MonoidHom` coercion of `algebraMap` (the form in which
`Units.map` presents the image of a principal idèle). -/
theorem ringEquivReal_completion_bridge_monoidHom_aux {w : InfinitePlace K} (hw : w.IsReal) (x : K) :
    InfinitePlace.Completion.ringEquivRealOfIsReal hw
        ((algebraMap K w.Completion : K →* w.Completion) x)
      = InfinitePlace.embedding_of_isReal hw x := by
  change InfinitePlace.Completion.ringEquivRealOfIsReal hw (algebraMap K w.Completion x) = _
  exact ringEquivReal_completion_bridge_aux hw x

/-- **The ideal of a one-place idèle at an infinite place is trivial**: the idèle is `1` at every
finite place. -/
theorem idealOf_onePlace_ofInfinite_aux (w : InfinitePlace K) (a : (w.Completion)ˣ) :
    Idele.idealOf (NK.HassePrinciple.onePlace (Place.ofInfinite w) a) = 1 := by
  rw [Idele.idealOf_eq_one_iff, Idele.mem_integralIdeles]
  intro v hv
  obtain ⟨q, rfl⟩ := Place.isFinite_iff.mp hv
  rw [NK.HassePrinciple.onePlace_apply_ne (Place.ofInfinite_ne_ofFinite w q).symm]
  exact Subgroup.one_mem _

/-- **Independence of the adjustment** (light copy of
`NK.NUV2.ARL.artinSym_idealOf_congr_aux`): if `x * (b)` and `x * (b')` both lie in `U`, then the
Artin symbols of the fractional ideals of `x * (b)` and `x * (b')` agree. -/
theorem artinSym_idealOf_congr_aux_light (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (U : Subgroup (Idele K)) (hstep : NK.CFTLib.Arl.Crux (K := K) (L := L) hcomm U)
    {x : Idele K} {b b' : Kˣ}
    (hb : x * Idele.principalIdele K b ∈ U)
    (hb' : x * Idele.principalIdele K b' ∈ U) :
    NK.CFTLib.Arl.artinSym hcomm (Idele.idealOf (x * Idele.principalIdele K b))
      = NK.CFTLib.Arl.artinSym hcomm (Idele.idealOf (x * Idele.principalIdele K b')) := by
  have hmem : Idele.principalIdele K (b * b'⁻¹) ∈ U := by
    have h1 : (x * Idele.principalIdele K b) * (x * Idele.principalIdele K b')⁻¹ ∈ U :=
      U.mul_mem hb (U.inv_mem hb')
    have h2 : (x * Idele.principalIdele K b) * (x * Idele.principalIdele K b')⁻¹
        = Idele.principalIdele K (b * b'⁻¹) := by
      rw [map_mul, map_inv, mul_inv_rev]
      rw [mul_comm (Idele.principalIdele K b')⁻¹ x⁻¹]
      rw [← mul_assoc, mul_assoc x (Idele.principalIdele K b) x⁻¹,
        mul_comm (Idele.principalIdele K b) x⁻¹, ← mul_assoc, mul_inv_cancel, one_mul]
    rwa [h2] at h1
  have hid : Idele.idealOf (x * Idele.principalIdele K b)
      = Idele.idealOf (x * Idele.principalIdele K b')
        * FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) ((b * b'⁻¹ : Kˣ) : K) := by
    have hbval : (b : K) = (b' : K) * ((b * b'⁻¹ : Kˣ) : K) := by
      rw [← Units.val_mul]
      congr 1
      rw [← mul_assoc, mul_comm b' b, mul_assoc, mul_inv_cancel, mul_one]
    rw [Idele.idealOf_mul, Idele.idealOf_mul, Idele.idealOf_principalIdele,
      Idele.idealOf_principalIdele, hbval, ← FractionalIdeal.spanSingleton_mul_spanSingleton]
    ac_rfl
  rw [hid, NK.CFTLib.Arl.artinSym_mul (K := K) (L := L) hcomm
      (Idele.idealOf_ne_zero _)
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr (Units.ne_zero _)),
    hstep _ hmem, mul_one]

/-- **The value of the idèlic Artin map at any valid adjustment** (light copy of
`NK.NUV2.ARL.ideleArtin_eq_artinSym_of_mem`). -/
theorem ideleArtin_eq_artinSym_of_mem_light (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    {U : Subgroup (Idele K)} (hUc : NK.CFTLib.Arl.Crux (K := K) (L := L) hcomm U)
    (hadj : ∀ x : Idele K, ∃ b : Kˣ, x * Idele.principalIdele K b ∈ U)
    (x : Idele K) {b : Kˣ} (hb : x * Idele.principalIdele K b ∈ U) :
    NK.CFTLib.Arl.ideleArtin hcomm U hadj x
      = NK.CFTLib.Arl.artinSym hcomm (Idele.idealOf (x * Idele.principalIdele K b)) := by
  show NK.CFTLib.Arl.artinSym hcomm
      (Idele.idealOf (x * Idele.principalIdele K (NK.CFTLib.Arl.adjust U hadj x))) = _
  exact artinSym_idealOf_congr_aux_light hcomm U hUc
    (NK.CFTLib.Arl.adjust_spec U hadj x) hb

end Helpers

theorem localImage_mem_localNormSubgroup_of_isCyclotomic_of_real {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (q : ℕ) [Fact q.Prime] (hq : 2 < q) [IsCyclotomicExtension {q} K L] (w : NumberField.InfinitePlace K) (hw : w.IsReal) (b : Kˣ) (h : ∀ v : NK.GlobalCFT.Place K, v ≠ NK.GlobalCFT.Place.ofInfinite w → NK.CFTLib.localImageHom v b ∈ NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v) : NK.CFTLib.localImageHom (NK.GlobalCFT.Place.ofInfinite w) b ∈ NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) (NK.GlobalCFT.Place.ofInfinite w) := by
  classical
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hqpos : 0 < q := (Fact.out : q.Prime).pos
  have hcomm : ∀ a b : Gal(L/K), a * b = b * a :=
    NK.CFTLib.HR.hcomm_of_isCyclotomic (K := K) (L := L) q
  have hram : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), (q : 𝓞 K) ∉ 𝔭.asIdeal →
      Ideal.ramificationIdxIn 𝔭.asIdeal (𝓞 L) = 1 := by
    intro 𝔭 h𝔭
    obtain ⟨P, hP⟩ := NK.Chebotarev.exists_primeIdeal_liesOver (K := K) (L := L) 𝔭
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx (A := 𝓞 K) (B := 𝓞 L) 𝔭.asIdeal P.asIdeal
      (Gal(L/K))]
    exact NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension (n := q) 𝔭 h𝔭 P hP
  have hprinc : NK.CFTLib.artinKillsPrincipal K L q :=
    fun a ha hpos s e σ hs hfac hfrob =>
      NK.CFTLib.ARL.artinReciprocity_cyclotomic K L q a ha hpos s e σ hs hfac hfrob
  obtain ⟨U, hU, hadj⟩ := NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust K q hqpos
  obtain ⟨art, hart, hprin, hfrob, -⟩ :=
    NK.CFTLib.Arl.exists_monoidHom_ideleArtin (K := K) (L := L) hcomm q hqpos hram hprinc
      U hU hadj
  have hUeq : U = NK.CFTLib.Arl.congruenceSubgroup K q :=
    SetLike.ext fun x => (hU.1 x).trans Iff.rfl
  have hnorm : ∀ y : Idele L, art (Idele.normIdeleHom K L y) = 1 := by
    intro y
    rw [hart]
    refine NK.CFTLib.Arl.normIdeles_mem_ker_of_ideleArtin (K := K) (L := L) hcomm q hqpos hram
      hprinc U hU hadj ?_ y
    intro z
    obtain ⟨d, hd⟩ := NK.CFTLib.Arl.exists_norm_mul_mem_congruenceSubgroup K L q hqpos z
    exact ⟨d, hUeq ▸ hd⟩
  have hUc : NK.CFTLib.Arl.Crux (K := K) (L := L) hcomm U :=
    fun b hb => NK.CFTLib.Arl.artinSym_spanSingleton_eq_one hcomm q hqpos hram hprinc b
      ((hU.2 b).mp hb).1 ((hU.2 b).mp hb).2
  -- ## The non-vanishing of `art (onePlace w (-1))`
  have hne : art (NK.HassePrinciple.onePlace (Place.ofInfinite w) (-1 : (w.Completion)ˣ)) ≠ 1 := by
    intro hone
    have hr : ∀ w' : InfinitePlace K, w'.IsReal → (if w' = w then (-1:ℝ) else 1) ≠ 0 := by
      intro w' _
      by_cases h : w' = w <;> simp [h]
    obtain ⟨u, hu⟩ := NK.CFTLib.Arl.exists_integral_sign_adjust K q hqpos
      (fun w' => if w' = w then (-1:ℝ) else 1) hr
    set c : 𝓞 K := 1 + (q : 𝓞 K) * u with hc_def
    have hcK : ((c : 𝓞 K) : K) = (1 : K) + (q : K) * ((u : 𝓞 K) : K) := by
      rw [hc_def]; push_cast; ring
    have hsign : ∀ (w' : InfinitePlace K) (hw' : w'.IsReal),
        0 < (if w' = w then (-1:ℝ) else 1)
          * (InfinitePlace.embedding_of_isReal hw') ((c : 𝓞 K) : K) := by
      intro w' hw'
      have h' := hu w' hw'
      rw [← hcK, ringEquivReal_completion_bridge_aux hw' ((c : 𝓞 K) : K)] at h'
      exact h'
    have hneg : (InfinitePlace.embedding_of_isReal hw) ((c : 𝓞 K) : K) < 0 := by
      have h' := hsign w hw
      rw [if_pos rfl] at h'
      linarith
    have hpos : ∀ (w' : InfinitePlace K) (hw' : w'.IsReal), w' ≠ w →
        0 < (InfinitePlace.embedding_of_isReal hw') ((c : 𝓞 K) : K) := by
      intro w' hw' hne'
      have h' := hsign w' hw'
      rw [if_neg hne'] at h'
      linarith
    have hc_ne : ((c : 𝓞 K) : K) ≠ 0 := by
      intro h0
      have h' := hneg
      rw [h0, map_zero] at h'
      exact absurd h' (lt_irrefl 0)
    have hc_ne' : c ≠ 0 := fun h0 => hc_ne (by rw [h0]; simp)
    have hNnegQ : Algebra.norm ℚ ((c : 𝓞 K) : K) < 0 :=
      norm_lt_zero_of_neg_at_one_real_place ((c : 𝓞 K) : K) hc_ne w hw hneg hpos
    have hNneg : Algebra.norm ℤ c < 0 := by
      have h' := hNnegQ
      rw [← Algebra.coe_norm_int] at h'
      exact_mod_cast h'
    have hcmem : c - 1 ∈ Ideal.span {(q : 𝓞 K)} := by
      rw [Ideal.mem_span_singleton']
      exact ⟨u, by rw [hc_def]; ring⟩
    have hNmem : Algebra.norm ℤ c - 1 ∈ Ideal.span {(q : ℤ)} :=
      NK.CFTLib.ARL.norm_sub_one_mem_span q c hcmem
    have hkey : ((Algebra.norm ℤ c).natAbs : ZMod q) = -1 := by
      obtain ⟨k, hk⟩ := Ideal.mem_span_singleton.mp hNmem
      have hmod : ((Algebra.norm ℤ c : ℤ) : ZMod q) = 1 := by
        rw [← Int.cast_one, ZMod.intCast_eq_intCast_iff]
        exact Int.modEq_iff_dvd.mpr ⟨-k, by linarith⟩
      have hnatAbs : ((Algebra.norm ℤ c).natAbs : ℤ) = -(Algebra.norm ℤ c) := by
        rw [← Int.natAbs_neg (Algebra.norm ℤ c)]
        exact Int.natAbs_of_nonneg (by linarith)
      have hcast : ((Algebra.norm ℤ c).natAbs : ZMod q)
          = (((Algebra.norm ℤ c).natAbs : ℤ) : ZMod q) := by
        norm_num
      rw [hcast, hnatAbs]
      push_cast
      rw [hmod]
    have hcop : ∀ p : NK.Chebotarev.PrimeIdeal K, p.asIdeal ∣ Ideal.span {c} →
        (q : 𝓞 K) ∉ p.asIdeal := by
      intro p hpd hpq
      have hc_mem : c ∈ p.asIdeal := Ideal.le_of_dvd hpd (Ideal.mem_span_singleton_self c)
      have hsub_mem : c - 1 ∈ p.asIdeal :=
        (Ideal.span_singleton_le_iff_mem p.asIdeal).mpr hpq hcmem
      have h1 : (1 : 𝓞 K) ∈ p.asIdeal := by
        have := sub_mem hc_mem hsub_mem
        simpa using this
      exact (inferInstance : p.asIdeal.IsPrime).ne_top (Ideal.eq_top_iff_one _ |>.mpr h1)
    have hchar : ((IsPrimitiveRoot.autToPow K (IsCyclotomicExtension.zeta_spec q K L)
        (NK.CFTLib.Arl.artinSym hcomm
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) ((c : 𝓞 K) : K))) : (ZMod q)ˣ)
          : ZMod q) = -1 :=
      (NK.NUV2.ARL.autToPow_artinSym_spanSingleton_natAbs (K := K) (L := L) q hcomm c hc_ne'
        hcop).trans hkey
    set cu : Kˣ := Units.mk0 ((c : 𝓞 K) : K) hc_ne with hcu
    have hcu_val : (cu : K) = ((c : 𝓞 K) : K) := Units.val_mk0 hc_ne
    have hprim : (1 : K) + (q : K) * ((u : 𝓞 K) : K) ≠ 0 := by
      rw [← hcK]; exact hc_ne
    have hcu_eq : cu = Units.mk0 ((1 : K) + (q : K) * ((u : 𝓞 K) : K)) hprim := by
      refine Units.ext ?_
      rw [hcu_val, Units.val_mk0, hcK]
    have hcompC : ∀ w' : InfinitePlace K,
        ((Idele.principalIdele K cu) (Place.ofInfinite w') : w'.Completion)
          = algebraMap K w'.Completion ((c : 𝓞 K) : K) := by
      intro w'
      rw [Idele.principalIdele_apply, Units.coe_map, hcu_val]
      change (algebraMap K w'.Completion : K →* w'.Completion) (((c : 𝓞 K) : K))
        = algebraMap K w'.Completion ((c : 𝓞 K) : K)
      rfl
    have hcU : NK.HassePrinciple.onePlace (Place.ofInfinite w) (-1 : (w.Completion)ˣ)
        * Idele.principalIdele K cu ∈ U := by
      rw [hU.1]
      refine ⟨?_, ?_⟩
      · intro 𝔭 h𝔭
        have hx : (NK.HassePrinciple.onePlace (Place.ofInfinite w) (-1 : (w.Completion)ˣ)
              * Idele.principalIdele K cu) (Place.ofFinite 𝔭)
            = (Idele.principalIdele K cu) (Place.ofFinite 𝔭) := by
          rw [Idele.mul_apply, NK.HassePrinciple.onePlace_apply_ne
            (Place.ofInfinite_ne_ofFinite w 𝔭).symm, one_mul]
        rw [hx]
        have h2 : (Idele.principalIdele K cu) (Place.ofFinite 𝔭)
            = Units.map (algebraMap K (𝔭.adicCompletion K) : K →* (𝔭.adicCompletion K))
                (Units.mk0 ((1 : K) + (q : K) * ((u : 𝓞 K) : K)) hprim) := by
          rw [Idele.principalIdele_apply, hcu_eq]
        rw [h2]
        exact NK.CFTLib.Arl.congrAt_unitsMap_add_one 𝔭 q u hprim
      · intro w'
        by_cases h : w' = w
        · subst w'
          intro hw'
          rw [Subsingleton.elim hw' hw]
          simp only [Idele.mul_apply, NK.HassePrinciple.onePlace_apply_self, Units.val_mul,
            Units.val_neg, Units.val_one, map_mul, map_neg, map_one]
          change 0 < (-1 : ℝ) * (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
              (((Idele.principalIdele K cu) (Place.ofInfinite w) : w.Completion))
          rw [hcompC w, ringEquivReal_completion_bridge_aux hw ((c : 𝓞 K) : K)]
          linarith
        · intro hw'
          simp only [Idele.mul_apply, NK.HassePrinciple.onePlace_apply_ne
              (by intro hh; exact h (Sum.inl.inj hh)), Units.val_mul, Units.val_one, one_mul]
          change 0 < (InfinitePlace.Completion.ringEquivRealOfIsReal hw')
              (((Idele.principalIdele K cu) (Place.ofInfinite w') : w'.Completion))
          rw [hcompC w', ringEquivReal_completion_bridge_aux hw' ((c : 𝓞 K) : K)]
          exact hpos w' hw' h
    have has1 : NK.CFTLib.Arl.artinSym hcomm
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) ((c : 𝓞 K) : K)) = 1 := by
      have heq : art (NK.HassePrinciple.onePlace (Place.ofInfinite w) (-1 : (w.Completion)ˣ))
          = NK.CFTLib.Arl.artinSym hcomm
              (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) ((c : 𝓞 K) : K)) := by
        rw [hart,
          ideleArtin_eq_artinSym_of_mem_light (K := K) (L := L) hcomm hUc hadj _ hcU,
          Idele.idealOf_mul, idealOf_onePlace_ofInfinite_aux, Idele.idealOf_principalIdele,
          one_mul]
        congr 1
      rw [← heq]
      exact hone
    have hcontr : ((IsPrimitiveRoot.autToPow K (IsCyclotomicExtension.zeta_spec q K L)
        (NK.CFTLib.Arl.artinSym hcomm
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) ((c : 𝓞 K) : K))) : (ZMod q)ˣ)
          : ZMod q) = 1 := by
      rw [has1]
      simp
    rw [hchar] at hcontr
    have h2 : (2 : ZMod q) = 0 := by
      have hh := congrArg (fun x : ZMod q => x + 1) hcontr
      simp only [neg_add_cancel] at hh
      rw [hh]; norm_num
    haveI : CharP (ZMod q) q := ZMod.charP q
    have hdvd : q ∣ 2 := (CharP.cast_eq_zero_iff (ZMod q) q 2).mp h2
    exact absurd (Nat.le_of_dvd (by norm_num) hdvd) (by omega)
  -- ## `art (onePlace w b_w) = 1`
  set bw : (w.Completion)ˣ := NK.CFTLib.localImageHom (Place.ofInfinite w) b with hbw
  set z : Idele K := Idele.principalIdele K b
    * (NK.HassePrinciple.onePlace (Place.ofInfinite w) bw)⁻¹ with hz
  have hzmem : z ∈ Idele.normImage K L := by
    rw [NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm_of_finiteDimensional]
    intro v
    by_cases hv : v = Place.ofInfinite w
    · subst hv
      refine NK.CFTLib.exists_normIdeleFun_eq_of_mem_localNormSubgroup (K := K) (L := L) ?_
      have hbQeq : (Idele.principalIdele K b) (Place.ofInfinite w) = bw := by
        rw [hbw, NK.CFTLib.localImageHom_apply, Idele.principalIdele_apply]
        rfl
      rw [hz, Idele.mul_apply, Idele.inv_apply, NK.HassePrinciple.onePlace_apply_self,
        hbQeq, mul_inv_cancel]
      exact Subgroup.one_mem _
    · refine NK.CFTLib.exists_normIdeleFun_eq_of_mem_localNormSubgroup (K := K) (L := L) ?_
      rw [hz, Idele.mul_apply, Idele.inv_apply, NK.HassePrinciple.onePlace_apply_ne hv,
        inv_one, mul_one, Idele.principalIdele_apply]
      exact h v hv
  obtain ⟨y, hy⟩ := Idele.mem_normImage.mp hzmem
  have hzy : z = Idele.normIdeleHom K L y := by
    ext v
    rw [Idele.normIdeleHom_apply]
    exact congrArg Units.val (hy v)
  have hz1 : art z = 1 := by
    rw [hzy]
    exact hnorm y
  have hw1 : art (NK.HassePrinciple.onePlace (Place.ofInfinite w) bw) = 1 := by
    have h2 : art z = (art (NK.HassePrinciple.onePlace (Place.ofInfinite w) bw))⁻¹ := by
      rw [hz, map_mul, map_inv, hprin b, one_mul]
    rw [hz1] at h2
    exact inv_eq_one.mp h2.symm
  -- ## `b_w > 0`
  have hpos_bw : NK.CFTLib.Arl.PosAtReal w bw := by
    by_contra hnp
    have hnlt : ¬ 0 < (InfinitePlace.Completion.ringEquivRealOfIsReal hw) ((bw : w.Completion)) := by
      intro hh
      exact hnp (fun hw' => by rw [Subsingleton.elim hw' hw]; exact hh)
    have hfne : (InfinitePlace.Completion.ringEquivRealOfIsReal hw) ((bw : w.Completion)) ≠ 0 := by
      intro h0
      refine Units.ne_zero bw ?_
      refine (InfinitePlace.Completion.ringEquivRealOfIsReal hw).injective ?_
      rw [h0, map_zero]
    have hvalu : (InfinitePlace.Completion.ringEquivRealOfIsReal hw) ((bw : w.Completion)) < 0 :=
      lt_of_le_of_ne (le_of_not_gt hnlt) hfne
    have hpos_neg : NK.CFTLib.Arl.PosAtReal w (bw * (-1 : (w.Completion)ˣ)) := by
      intro hw'
      rw [Subsingleton.elim hw' hw]
      rw [Units.val_mul, Units.val_neg, Units.val_one, map_mul, map_neg, map_one]
      linarith
    have hmem_neg : (bw * (-1 : (w.Completion)ˣ))
        ∈ NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) (Place.ofInfinite w) :=
      (mem_localNormSubgroup_ofInfinite_iff_pos (K := K) (L := L) (q := q) hq w hw
        (bw * (-1))).mpr hpos_neg
    have hval_prod : art (NK.HassePrinciple.onePlace (Place.ofInfinite w)
        (bw * (-1 : (w.Completion)ˣ))) = 1 := by
      have hmem := (NK.CFTLib.IdeleHasse.onePlace_mem_normImage_iff (K := K) (L := L)
        (Place.ofInfinite w) (bw * (-1))).mpr hmem_neg
      obtain ⟨y', hy'⟩ := Idele.mem_normImage.mp hmem
      have hEq : NK.HassePrinciple.onePlace (Place.ofInfinite w) (bw * (-1))
          = Idele.normIdeleHom K L y' := by
        ext v
        rw [Idele.normIdeleHom_apply]
        exact congrArg Units.val (hy' v)
      rw [hEq]
      exact hnorm y'
    have hprod : art (NK.HassePrinciple.onePlace (Place.ofInfinite w) (bw * (-1)))
        = art (NK.HassePrinciple.onePlace (Place.ofInfinite w) bw)
          * art (NK.HassePrinciple.onePlace (Place.ofInfinite w) (-1)) := by
      rw [← NK.CFTLib.IdeleHasse.onePlaceHom_apply, ← NK.CFTLib.IdeleHasse.onePlaceHom_apply,
        ← NK.CFTLib.IdeleHasse.onePlaceHom_apply]
      simp only [map_mul]
    have hconj : art (NK.HassePrinciple.onePlace (Place.ofInfinite w) (-1 : (w.Completion)ˣ)) = 1 := by
      have h := hprod
      rw [hval_prod, hw1, one_mul] at h
      exact h.symm
    exact hne hconj
  change bw ∈ NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) (Place.ofInfinite w)
  exact (mem_localNormSubgroup_ofInfinite_iff_pos (K := K) (L := L) (q := q) hq w hw bw).mpr
    hpos_bw

end NK.NUV2.ARL
