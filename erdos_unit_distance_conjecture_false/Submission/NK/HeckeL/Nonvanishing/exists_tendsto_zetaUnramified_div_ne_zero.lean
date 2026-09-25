/-
# Non-vanishing of the limit of the quotient of the two truncated Euler products

The analytic input of the Čebotarev chapter: for a finite set `S` of primes of `K` and a finite
extension `L/K`, the quotient

`ζ^{S}_{L}(s) / ζ^{S}_{K}(s) = ∏_{𝔮 ∤ S} (1 - N𝔮^{-s})⁻¹ / ∏_{𝔭 ∉ S} (1 - N𝔭^{-s})⁻¹`

of the two Euler products with the Euler factors above `S` deleted has a **non-zero** limit as
`s → 1⁺`.

No hypothesis on `S` is needed.  The argument is the standard one:

* For `s > 1` both truncated products are the full Euler product of the corresponding Dedekind zeta
  function divided by the *finite* product of the deleted factors
  (`zetaUnramified_notMem_eq`): if `T` is the (finite) set of primes of `L` lying over `S`, then
  `ζ^{S}_{L}(s) = ζ_L(s) · ∏_{𝔮 ∈ T} (1 - N𝔮^{-s})` and similarly for `K`.
* Hence the quotient is `(ζ_L(s)/ζ_K(s)) · (∏_{𝔭 ∈ S}(1 - N𝔭^{-s}) / ∏_{𝔮 ∈ T}(1 - N𝔮^{-s}))`.
* `ζ_L(s)/ζ_K(s) → Res_{s=1} ζ_L / Res_{s=1} ζ_K > 0`
  (`tendsto_dedekindZeta_re_div_aux`), and the correction is a finite product of continuous
  functions, tending to a positive real number.
* The product of the two limits is the required non-zero `c`.
-/
import Mathlib
import Submission.NK.HeckeL.Zeta
import Submission.NK.HeckeL.Product.dedekindZeta_eulerProduct
import Submission.Commons.NumberTheory.NumberField.DedekindZeta.log_eulerProduct_primeIdeal

open NumberField IsDedekindDomain Filter Topology
open scoped BigOperators Topology
open Commons.NumberTheory.NumberField.DedekindZeta

noncomputable section

namespace NK.HeckeL.Nonvanishing

/-! ## The finite set of primes lying over the modulus -/

/-- Only finitely many primes of `L` lie over a given prime of `K`. -/
theorem finite_setOf_liesOver {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] (Q : NK.HeckeL.PrimeIdeal K) :
    Set.Finite {𝔮 : NK.HeckeL.PrimeIdeal L | 𝔮.asIdeal.LiesOver Q.asIdeal} := by
  have hfin : (Q.asIdeal.primesOver (𝓞 L)).Finite :=
    IsDedekindDomain.primesOver_finite Q.asIdeal (𝓞 L)
  exact Set.Finite.of_finite_image (f := fun 𝔮 : NK.HeckeL.PrimeIdeal L => 𝔮.asIdeal)
    (hfin.subset fun P hP => by
      obtain ⟨𝔮, h𝔮, rfl⟩ := hP
      exact ⟨𝔮.isPrime, h𝔮⟩)
    (fun a _ b _ h => IsDedekindDomain.HeightOneSpectrum.ext h)

/-- The primes of `L` above the modulus can be listed by a finset. -/
theorem exists_primesOver_finset {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (S : Finset (NK.HeckeL.PrimeIdeal K)) :
    ∃ T : Finset (NK.HeckeL.PrimeIdeal L),
      ∀ 𝔮 : NK.HeckeL.PrimeIdeal L, 𝔮 ∈ T ↔ ∃ Q ∈ S, 𝔮.asIdeal.LiesOver Q.asIdeal := by
  have hfin : ((⋃ Q ∈ (S : Set (NK.HeckeL.PrimeIdeal K)),
      {𝔮 : NK.HeckeL.PrimeIdeal L | 𝔮.asIdeal.LiesOver Q.asIdeal})).Finite :=
    (S.finite_toSet).biUnion fun Q _ => finite_setOf_liesOver (K := K) (L := L) Q
  refine ⟨hfin.toFinset, fun 𝔮 => ?_⟩
  rw [Set.Finite.mem_toFinset]
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_coe, exists_prop]

/-! ## The finite correction factors -/

/-- The finite product `∏_{𝔭 ∈ T} (1 - N𝔭^{-s})` of Euler factors over a finset of primes; for
`T = S` it is the correction at the primes of the modulus, for `T` the primes of `L` above `S` it
is the correction on the `L`-side. -/
noncomputable def eulerCorr (F : Type*) [Field F] [NumberField F]
    (T : Finset (NK.HeckeL.PrimeIdeal F)) (s : ℝ) : ℂ :=
  ∏ 𝔭 ∈ T, (1 - (((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))

/-- Each local factor `1 - N𝔭^{-s}` is continuous at `s = 1`, hence so is the finite product. -/
theorem continuousAt_eulerCorr_one (F : Type*) [Field F] [NumberField F]
    (T : Finset (NK.HeckeL.PrimeIdeal F)) :
    ContinuousAt (fun s : ℝ => eulerCorr F T s) 1 := by
  refine tendsto_finsetProd T (fun 𝔭 _ => ?_)
  refine continuousAt_const.sub ?_
  refine Complex.continuous_ofReal.continuousAt.comp ?_
  refine (Real.continuousAt_const_rpow ?_).comp continuous_neg.continuousAt
  have h := NumberField.HeightOneSpectrum.absNorm_ne_zero 𝔭
  exact_mod_cast h

/-- The local factor `1 - N𝔭^{-1}` is strictly positive, so the finite correction does not
vanish at `s = 1`. -/
theorem eulerCorr_one_ne_zero (F : Type*) [Field F] [NumberField F]
    (T : Finset (NK.HeckeL.PrimeIdeal F)) : eulerCorr F T 1 ≠ 0 := by
  rw [eulerCorr, Finset.prod_ne_zero_iff]
  intro 𝔭 _
  have hlt := rpow_neg_absNorm_primeIdeal_lt_one (K := F) zero_lt_one 𝔭
  have hr : (1 : ℝ) - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-(1 : ℝ)) ≠ 0 := by linarith
  rwa [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.ofReal_ne_zero]

/-! ## The truncated Euler products -/

/-- **The truncated Euler product is the full Euler product times the finite correction.** For a
number field `F`, a finite set `T` of primes of `F` and a real `s > 1`, the Euler product over the
primes outside `T` equals `ζ_F(s)` multiplied by the deleted factors
`∏_{𝔭 ∈ T}(1 - N𝔭^{-s})`. -/
theorem zetaUnramified_notMem_eq (F : Type*) [Field F] [NumberField F]
    (T : Finset (NK.HeckeL.PrimeIdeal F))
    {s : ℝ} (hs : 1 < s) :
    (∏' 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal F // 𝔭 ∉ T},
        (1 - (((Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹)
      = ((NumberField.dedekindZeta F (s : ℂ)).re : ℂ) * eulerCorr F T s := by
  classical
  have hs0 : (0 : ℝ) < s := lt_trans zero_lt_one hs
  have hpos : ∀ 𝔭 : NK.HeckeL.PrimeIdeal F, 0 < localFactor F s 𝔭.asIdeal := by
    intro 𝔭
    rw [localFactor]
    exact inv_pos.mpr (sub_pos.mpr (rpow_neg_absNorm_primeIdeal_lt_one (K := F) hs0 𝔭))
  have hsumm' : Summable (fun 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal F // 𝔭 ∉ T} =>
      Real.log (localFactor F s 𝔭.1.asIdeal)) := (summable_log_localFactor (K := F) hs).subtype _
  have hmulR : Multipliable (fun 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal F // 𝔭 ∉ T} =>
      localFactor F s 𝔭.1.asIdeal) :=
    Real.multipliable_of_summable_log (fun 𝔭 => hpos 𝔭.1) hsumm'
  have hmulC : Multipliable (fun 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal F // 𝔭 ∉ T} =>
      ((localFactor F s 𝔭.1.asIdeal : ℝ) : ℂ)) :=
    hmulR.map Complex.ofRealHom Complex.continuous_ofReal
  have hcomp : Multipliable (fun 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal F // 𝔭 ∉ T} =>
      (1 - (((Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹) := by
    refine hmulC.congr (fun 𝔭 => ?_)
    rw [localFactor, Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_one]
  have hfinM : Multipliable (fun 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal F // 𝔭 ∈ T} =>
      (1 - (((Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹) :=
    (hasProd_fintype (fun 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal F // 𝔭 ∈ T} =>
      (1 - (((Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹)).multipliable
  have hsplit0 := Multipliable.tprod_mul_tprod_compl
    (f := fun 𝔭 : NK.HeckeL.PrimeIdeal F =>
      (1 - (((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹)
    (s := (T : Set (NK.HeckeL.PrimeIdeal F))) hfinM hcomp
  rw [Finset.tprod_subtype' T (fun 𝔭 : NK.HeckeL.PrimeIdeal F =>
      (1 - (((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹)] at hsplit0
  have hset : ((T : Set (NK.HeckeL.PrimeIdeal F))ᶜ : Set (NK.HeckeL.PrimeIdeal F)) =
      {x | x ∉ T} := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Finset.mem_coe]
  have hconv : (∏' x : ↑((T : Set (NK.HeckeL.PrimeIdeal F))ᶜ),
      (1 - (((Ideal.absNorm (x : NK.HeckeL.PrimeIdeal F).asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹) =
      (∏' x : {x : NK.HeckeL.PrimeIdeal F // x ∉ T},
      (1 - (((Ideal.absNorm (x : NK.HeckeL.PrimeIdeal F).asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹) :=
    tprod_congr_set_coe (fun 𝔭 : NK.HeckeL.PrimeIdeal F =>
      (1 - (((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹) hset
  have hsplit : (∏ 𝔭 ∈ T, (1 - (((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹) *
      (∏' 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal F // 𝔭 ∉ T},
        (1 - (((Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹) =
      ∏' 𝔭 : NK.HeckeL.PrimeIdeal F,
        (1 - (((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ := by
    rw [← hconv]
    exact hsplit0
  have hAne : (∏ 𝔭 ∈ T, (1 - (((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro 𝔭 _
    refine inv_ne_zero ?_
    have hlt := rpow_neg_absNorm_primeIdeal_lt_one (K := F) hs0 𝔭
    have hr : (1 : ℝ) - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) ≠ 0 := by linarith
    rwa [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.ofReal_ne_zero]
  have hD : (∏' 𝔭 : NK.HeckeL.PrimeIdeal F,
      (1 - (((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹)
      = ((NumberField.dedekindZeta F (s : ℂ)).re : ℂ) :=
    NK.HeckeL.Product.dedekindZeta_eulerProduct (K := F) hs
  calc (∏' 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal F // 𝔭 ∉ T},
        (1 - (((Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹)
      = (∏ 𝔭 ∈ T, (1 - (((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹)⁻¹ *
          ∏' 𝔭 : NK.HeckeL.PrimeIdeal F,
            (1 - (((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ := by
          rw [← hsplit]
          rw [inv_mul_cancel_left₀ hAne]
    _ = (∏ 𝔭 ∈ T, (1 - (((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹)⁻¹ *
          ((NumberField.dedekindZeta F (s : ℂ)).re : ℂ) := by rw [hD]
    _ = ((NumberField.dedekindZeta F (s : ℂ)).re : ℂ) * eulerCorr F T s := by
          rw [Finset.prod_inv_distrib, inv_inv, mul_comm]
          rfl

/-! ## The ratio of the Dedekind zeta functions -/

/-- **The quotient of the Dedekind zeta functions tends to the quotient of the residues at
`s = 1`.** -/
theorem tendsto_dedekindZeta_re_div_aux (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] :
    Filter.Tendsto
      (fun s : ℝ =>
        (NumberField.dedekindZeta L (s : ℂ)).re / (NumberField.dedekindZeta K (s : ℂ)).re)
      (nhdsWithin (1 : ℝ) (Set.Ioi 1))
      (nhds (NumberField.dedekindZeta_residue L / NumberField.dedekindZeta_residue K)) := by
  have hL : Tendsto (fun s : ℝ => (s - 1) * (NumberField.dedekindZeta L (s : ℂ)).re)
      (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (𝓝 (NumberField.dedekindZeta_residue L)) := by
    have h := (Complex.continuous_re.tendsto ((NumberField.dedekindZeta_residue L : ℝ) : ℂ)).comp
        (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT L)
    simp only [Complex.ofReal_re] at h
    refine h.congr fun s => ?_
    simp only [Function.comp_apply, Complex.mul_re, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im, sub_zero]
    ring
  have hK : Tendsto (fun s : ℝ => (s - 1) * (NumberField.dedekindZeta K (s : ℂ)).re)
      (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (𝓝 (NumberField.dedekindZeta_residue K)) := by
    have h := (Complex.continuous_re.tendsto ((NumberField.dedekindZeta_residue K : ℝ) : ℂ)).comp
        (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K)
    simp only [Complex.ofReal_re] at h
    refine h.congr fun s => ?_
    simp only [Function.comp_apply, Complex.mul_re, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im, sub_zero]
    ring
  refine (hL.div hK (ne_of_gt (NumberField.dedekindZeta_residue_pos K))).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [Set.mem_Ioi] at hs
  have hs1 : s - 1 ≠ 0 := by linarith
  exact mul_div_mul_left _ _ hs1

/-! ## The main theorem -/

theorem exists_tendsto_zetaUnramified_div_ne_zero {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (S : Finset (NK.HeckeL.PrimeIdeal K)) :
    ∃ c : ℂ, c ≠ 0 ∧ Filter.Tendsto
      (fun s : ℝ => NK.HeckeL.zetaUnramified K L S s / NK.HeckeL.zetaUnramifiedK K S s)
      (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds c) := by
  classical
  obtain ⟨T, hT⟩ := exists_primesOver_finset (K := K) (L := L) S
  refine ⟨((NumberField.dedekindZeta_residue L / NumberField.dedekindZeta_residue K : ℝ) : ℂ) *
      (eulerCorr L T 1 * (eulerCorr K S 1)⁻¹), ?_, ?_⟩
  · refine mul_ne_zero ?_ ?_
    · rw [Complex.ofReal_ne_zero]
      exact ne_of_gt (div_pos (NumberField.dedekindZeta_residue_pos L)
        (NumberField.dedekindZeta_residue_pos K))
    · exact mul_ne_zero (eulerCorr_one_ne_zero L T) (inv_ne_zero (eulerCorr_one_ne_zero K S))
  · have hζ : Tendsto
        (fun s : ℝ => (((NumberField.dedekindZeta L (s : ℂ)).re /
          (NumberField.dedekindZeta K (s : ℂ)).re : ℝ) : ℂ))
        (nhdsWithin (1 : ℝ) (Set.Ioi 1))
        (𝓝 (((NumberField.dedekindZeta_residue L / NumberField.dedekindZeta_residue K : ℝ) : ℂ))) :=
      (Complex.continuous_ofReal.tendsto _).comp (tendsto_dedekindZeta_re_div_aux K L)
    have hA : Tendsto (fun s : ℝ => eulerCorr L T s) (nhdsWithin (1 : ℝ) (Set.Ioi 1))
        (𝓝 (eulerCorr L T 1)) :=
      (continuousAt_eulerCorr_one L T).tendsto.mono_left nhdsWithin_le_nhds
    have hB : Tendsto (fun s : ℝ => eulerCorr K S s) (nhdsWithin (1 : ℝ) (Set.Ioi 1))
        (𝓝 (eulerCorr K S 1)) :=
      (continuousAt_eulerCorr_one K S).tendsto.mono_left nhdsWithin_le_nhds
    have hlim : Tendsto (fun s : ℝ =>
        ((((NumberField.dedekindZeta L (s : ℂ)).re /
            (NumberField.dedekindZeta K (s : ℂ)).re : ℝ) : ℂ) *
          (eulerCorr L T s * (eulerCorr K S s)⁻¹)))
        (nhdsWithin (1 : ℝ) (Set.Ioi 1))
        (𝓝 ((((NumberField.dedekindZeta_residue L /
            NumberField.dedekindZeta_residue K : ℝ) : ℂ) *
          (eulerCorr L T 1 * (eulerCorr K S 1)⁻¹)))) :=
      hζ.mul (hA.mul (hB.inv₀ (eulerCorr_one_ne_zero K S)))
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hL : NK.HeckeL.zetaUnramified K L S s =
        ((NumberField.dedekindZeta L (s : ℂ)).re : ℂ) * eulerCorr L T s := by
      have hconv : NK.HeckeL.zetaUnramified K L S s =
          (∏' 𝔮 : {𝔮 : NK.HeckeL.PrimeIdeal L // 𝔮 ∉ T},
            (1 - (((Ideal.absNorm 𝔮.1.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹) :=
        tprod_congr_subtype (fun 𝔮 : NK.HeckeL.PrimeIdeal L =>
            (1 - (((Ideal.absNorm 𝔮.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹)
          (fun 𝔮 => by simp only [hT 𝔮, not_exists, not_and])
      exact hconv.trans (zetaUnramified_notMem_eq L T hs)
    have hK : NK.HeckeL.zetaUnramifiedK K S s =
        ((NumberField.dedekindZeta K (s : ℂ)).re : ℂ) * eulerCorr K S s :=
      zetaUnramified_notMem_eq K S hs
    rw [hL, hK]
    push_cast
    ring

end NK.HeckeL.Nonvanishing
