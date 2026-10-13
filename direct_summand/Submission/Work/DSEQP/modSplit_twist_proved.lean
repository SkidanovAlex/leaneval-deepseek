import Mathlib
import Submission.Work.DSMap.Gaps
import Submission.Work.DSAM3.Api
import Submission.Work.DSEQP.TwistDefs
import Submission.Work.DSEQP.TwistAux

open CategoryTheory
open DSMap.Mix
open scoped TensorProduct

namespace Work.DSEQP

universe a

/-- **TWIST** (`DSMap.Gaps.modSplit_twist`): an almost splitting over the perfection `W` of `B`
with value `c^{1/p^k}` gives one over any perfect `A`-algebra `S` with value `(c·φ(1))^{1/p^k}`,
for any `A`-linear `φ : B → A`.

The construction: restrict the `W`-splitting to `P⁰`; its (finitely generated) image lies in a
single level `W_N = ψW(B)^{1/p^N}` with `N ≥ k`.  The level-`N` transfer map
`ψW(b)^{1/p^N} ↦ ψS(φ b)^{1/p^N}` (`twistBeta_exists`) is `A`-linear, so it produces a splitting
over `S` with value `c^{1/p^k}·(φ 1)^{1/p^N}`; multiplying the `S`-linear form by
`((φ 1)^{1/p^N})^{p^{N-k}-1}` (`modSplitA_mul`, AM1) corrects the value to `(c·φ(1))^{1/p^k}`. -/
theorem modSplit_twist_proved {A B W S : Type a} [CommRing A] [CommRing B] [Algebra A B] [CommRing W]
    [CommRing S] (p : ℕ) [Fact p.Prime] [CharP W p] [PerfectRing W p] [CharP S p]
    [PerfectRing S p] (ψW : B →+* W) (hψW : Function.Injective ψW)
    (hW : ∀ w : W, ∃ (n : ℕ) (x : B), w = ((frobeniusEquiv W p).symm^[n]) (ψW x))
    (ψS : A →+* S) (φ : B →ₗ[A] A) (P : CochainComplex (ModuleCat.{a} A) ℤ)
    (hP : IsBddFinFree P) (ε : ModuleCat.of A A ⟶ P.X 0) (c : A) (k : ℕ)
    (h : ModSplit P ε (ψW.comp (algebraMap A B)) ⊥
      (((frobeniusEquiv W p).symm^[k]) (ψW (algebraMap A B c)))) :
    ModSplit P ε ψS ⊥ (((frobeniusEquiv S p).symm^[k]) (ψS (c * φ 1))) := by
  -- the two `A`-algebra structures in play
  letI : Algebra A W := (ψW.comp (algebraMap A B)).toAlgebra
  letI : Algebra A S := ψS.toAlgebra
  have hAW : algebraMap A W = ψW.comp (algebraMap A B) := RingHom.algebraMap_toAlgebra _
  have hAS : algebraMap A S = ψS := RingHom.algebraMap_toAlgebra _
  -- pass to the `A`-linear form of the splitting
  rw [DSAM3.modSplit_iff_ModSplitA] at h
  rw [DSAM3.modSplit_iff_ModSplitA]
  obtain ⟨tWq, htWq_d, htWq_u⟩ := h
  -- the honest `A`-linear map `P⁰ → W`
  let tW : P.X 0 →ₗ[A] W := (AlgEquiv.quotientBot A W).toLinearMap.comp tWq
  have htW_u : tW (ε.hom 1) = ((frobeniusEquiv W p).symm^[k]) (ψW (algebraMap A B c)) := by
    show (AlgEquiv.quotientBot A W) (tWq (ε.hom 1)) = _
    rw [htWq_u, AlgEquiv.quotientBot_mk]
  have htW_d : tW.comp (P.d (-1) 0).hom = 0 := by
    change ((AlgEquiv.quotientBot A W).toLinearMap.comp tWq).comp (P.d (-1) 0).hom = 0
    rw [LinearMap.comp_assoc, htWq_d, LinearMap.comp_zero]
  -- a level containing the image, with `N ≥ k`
  haveI : Module.Finite A (P.X 0) := (hP.1 0).2
  obtain ⟨N, hkN, hN⟩ := twistLevel_large p ψW hAW hW (P.X 0) tW k
  -- the transfer map on that level
  obtain ⟨β, hβ⟩ := twistBeta_exists p ψW hAW hψW ψS hAS φ N
  set tS : P.X 0 →ₗ[A] S := β.comp (tW.codRestrict (twistLevel p ψW hAW N) hN) with htSdef
  -- `tS` kills `d⁻¹`
  have htS_d : tS.comp (P.d (-1) 0).hom = 0 := by
    ext x
    have h0 : tW ((P.d (-1) 0).hom x) = 0 := by
      have h1 := LinearMap.congr_fun htW_d x
      simpa [LinearMap.comp_apply] using h1
    have hz : (tW.codRestrict (twistLevel p ψW hAW N) hN ((P.d (-1) 0).hom x)) = 0 := by
      ext
      simpa [LinearMap.codRestrict_apply] using h0
    rw [LinearMap.comp_apply, LinearMap.zero_apply, htSdef, LinearMap.comp_apply, hz, map_zero]
  -- the value of `tS` at the unit
  have hval : tS (ε.hom 1) = ((frobeniusEquiv S p).symm^[k]) (ψS c) *
      ((frobeniusEquiv S p).symm^[N]) (ψS (φ 1)) := by
    have hb : ((tW.codRestrict (twistLevel p ψW hAW N) hN (ε.hom 1) :
        twistLevel p ψW hAW N) : W) ^ (p ^ N) = ψW ((algebraMap A B c) ^ (p ^ (N - k))) := by
      rw [LinearMap.codRestrict_apply, htW_u]
      rw [iterateFrobeniusEquiv_symm_pow_pow p (ψW (algebraMap A B c)) hkN, map_pow]
    rw [htSdef, LinearMap.comp_apply, hβ _ _ hb]
    rw [iterateFrobeniusEquiv_symm_apply, ← map_pow (algebraMap A B) c (p ^ (N - k)),
      apply_algebraMap_one φ (c ^ (p ^ (N - k))), map_mul ψS, map_pow ψS,
      iterateFrobeniusEquiv_symm_mul, iterateFrobeniusEquiv_symm_eq p (ψS c) hkN]
  -- the correction factor
  set u : S := (((frobeniusEquiv S p).symm^[N]) (ψS (φ 1))) ^ (p ^ (N - k) - 1) with hu
  have hu_corr : tS (ε.hom 1) * u = ((frobeniusEquiv S p).symm^[k]) (ψS (c * φ 1)) := by
    have he : 1 ≤ p ^ (N - k) := one_le_pow₀ (Fact.out : p.Prime).one_le
    have hz : ((frobeniusEquiv S p).symm^[N]) (ψS (φ 1)) *
        (((frobeniusEquiv S p).symm^[N]) (ψS (φ 1))) ^ (p ^ (N - k) - 1) =
        (((frobeniusEquiv S p).symm^[N]) (ψS (φ 1))) ^ (p ^ (N - k)) := by
      rw [mul_comm, ← pow_succ, Nat.sub_add_cancel he]
    rw [hval, hu, mul_assoc, hz, iterateFrobeniusEquiv_symm_pow_eq p (ψS (φ 1)) hkN,
      ← iterateFrobeniusEquiv_symm_mul, ← map_mul]
  -- assembly: a splitting over `S` with value `tS (ε 1)`, then AM1
  have hsplit : DSAM3.ModSplitA P ε ψS ⊥ (tS (ε.hom 1)) := by
    refine ⟨(AlgEquiv.quotientBot A S).symm.toLinearMap.comp tS, ?_, ?_⟩
    · rw [LinearMap.comp_assoc, htS_d, LinearMap.comp_zero]
    · rw [LinearMap.comp_apply]
      exact AlgEquiv.quotientBot_symm_mk _
  have hfinal : DSAM3.ModSplitA P ε ψS ⊥ (((frobeniusEquiv S p).symm^[k]) (ψS (c * φ 1))) := by
    have h1 := DSAM3.modSplitA_mul P ε ψS ⊥ (tS (ε.hom 1)) u hsplit
    rwa [hu_corr] at h1
  exact hfinal

end Work.DSEQP
