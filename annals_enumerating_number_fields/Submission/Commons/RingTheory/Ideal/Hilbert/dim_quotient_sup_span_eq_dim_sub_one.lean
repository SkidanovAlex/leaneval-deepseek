import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Submission.Commons.RingTheory.KrullDimension.ringKrullDim_eq_of_isIntegral

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-!
# Dimension of quotients of a polynomial ring by a hypersurface

We prove that if `A` is a finitely generated domain over a field `K` and `0 ≠ g ∈ A` is a
nonunit, then the quotient `A ⧸ (g)` has Krull dimension exactly one less than `A`:

`ringKrullDim (A ⧸ span {g}) + 1 = ringKrullDim A`.

The proof combines two ingredients:
* an upper bound: a quotient by a non-zero-divisor drops the dimension by at least one
  (`ringKrullDim_quotient_succ_le_of_nonZeroDivisor`);
* a lower bound, which uses the fact that every maximal ideal of a finitely generated domain over
  a field has height equal to the Krull dimension ("equidimensionality"), obtained from Noether
  normalization and going-down.
-/

namespace Commons.RingTheory.Ideal.Hilbert

open MvPolynomial

/-- Every maximal ideal of the polynomial ring `K[X₁, …, Xₛ]` over a field `K` has height `s`. -/
theorem height_maximal_mvPolynomial {k : Type*} [Field k] (s : ℕ)
    (m : Ideal (MvPolynomial (Fin s) k)) [m.IsMaximal] : m.height = s := by
  induction s with
  | zero =>
    obtain ⟨e⟩ : Nonempty (MvPolynomial (Fin 0) k ≃+* k) :=
      ⟨MvPolynomial.isEmptyRingEquiv k (Fin 0)⟩
    have hmap : (Ideal.map e m).height = m.height := RingEquiv.height_map e m
    have hmax : (Ideal.map e m).IsMaximal := Ideal.map_isMaximal_of_equiv e
    have hbot : (⊥ : Ideal k).IsMaximal := (Ring.isField_iff_maximal_bot).mp (Field.toIsField k)
    have : Ideal.map e m = ⊥ := (hbot.eq_of_le hmax.ne_top bot_le).symm
    rw [this, Ideal.height_bot] at hmap
    exact hmap.symm
  | succ n ih =>
    set e := MvPolynomial.finSuccEquiv k n with he
    let P : Ideal (Polynomial (MvPolynomial (Fin n) k)) :=
      Ideal.map (e : MvPolynomial (Fin (n + 1)) k →+* _) m
    haveI : P.IsMaximal := Ideal.map_isMaximal_of_equiv e.toRingEquiv
    have h1 : P.height = m.height := RingEquiv.height_map e.toRingEquiv m
    let p : Ideal (MvPolynomial (Fin n) k) := P.under (MvPolynomial (Fin n) k)
    have hp : p = Ideal.comap Polynomial.C P := rfl
    haveI : p.IsMaximal := by rw [hp]; exact Polynomial.isMaximal_comap_C_of_isJacobsonRing P
    have h2 : P.height = p.height + 1 := Polynomial.height_eq_height_add_one p P
    have h3 : p.height = n := ih p
    rw [h3] at h2
    rw [h1] at h2
    rw [h2]
    push_cast
    ring

/-- **Equidimensionality.** Every maximal ideal of a finitely generated domain over a field has
height equal to the Krull dimension of the ring. -/
theorem height_eq_ringKrullDim_of_isMaximal {K A : Type*} [Field K] [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A] (M : Ideal A) [M.IsMaximal] :
    M.height = ringKrullDim A := by
  obtain ⟨s, φ, hφinj, hφfin⟩ := exists_finite_inj_algHom_of_fg K A
  let B := MvPolynomial (Fin s) K
  letI : Algebra B A := φ.toRingHom.toAlgebra
  have hmap : algebraMap B A = φ.toRingHom := rfl
  haveI : IsScalarTower K B A := IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  haveI : Module.Finite B A := hφfin
  haveI : Algebra.IsIntegral B A := Algebra.IsIntegral.of_finite B A
  haveI : FaithfulSMul B A :=
    (faithfulSMul_iff_algebraMap_injective B A).mpr (by rw [hmap]; exact hφinj)
  have hdim : ringKrullDim A = (s : WithBot ℕ∞) := by
    rw [Commons.RingTheory.KrullDimension.ringKrullDim_eq_of_isIntegral
        (by rw [hmap]; exact hφinj),
      MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  have hle : M.height ≤ (s : ℕ∞) := by
    have h := Ideal.height_le_ringKrullDim_of_isPrime (R := A) (I := M)
    rw [hdim] at h
    exact WithBot.coe_le_coe.mp h
  have hm : (M.under B).height = (s : ℕ∞) := height_maximal_mvPolynomial s (M.under B)
  have hge : (s : ℕ∞) ≤ M.height := by
    obtain ⟨l, hlast, hlen⟩ := Ideal.exists_ltSeries_length_eq_height (M.under B)
    rw [hm] at hlen
    have hlen' : l.length = s := by exact_mod_cast hlen
    haveI : M.LiesOver l.last.asIdeal := by
      rw [hlast]; exact ⟨rfl⟩
    obtain ⟨L, hLlen, hLlast, -⟩ := Ideal.exists_ltSeries_of_hasGoingDown l M
    rw [hlen'] at hLlen
    have h1 : (s : ℕ∞) ≤ Order.height (⟨M, inferInstance⟩ : PrimeSpectrum A) := by
      rw [← hLlen]
      exact Order.length_le_height (le_of_eq hLlast)
    rw [← PrimeSpectrum.height_eq_orderHeight (⟨M, inferInstance⟩ : PrimeSpectrum A)] at h1
    exact h1
  rw [hdim]
  exact le_antisymm (WithBot.coe_le_coe.mpr hle) (WithBot.coe_le_coe.mpr hge)

/-- If `A` is a finitely generated domain over a field and `0 ≠ g ∈ A` is a nonunit, then
`ringKrullDim (A ⧸ span {g}) + 1 = ringKrullDim A`. -/
theorem ringKrullDim_quotient_span_singleton_add_one {K A : Type*} [Field K] [CommRing A]
    [IsDomain A] [Algebra K A] [Algebra.FiniteType K A] {g : A} (hg : g ≠ 0)
    (hgu : ¬ IsUnit g) :
    ringKrullDim (A ⧸ Ideal.span {g}) + 1 = ringKrullDim A := by
  refine le_antisymm ?_ ?_
  · exact ringKrullDim_quotient_succ_le_of_nonZeroDivisor
      (by rwa [mem_nonZeroDivisors_iff_ne_zero])
  · obtain ⟨M, hMmax, hleM⟩ :=
      Ideal.exists_le_maximal (Ideal.span {g}) (Ideal.span_singleton_eq_top.not.mpr hgu)
    haveI : M.IsMaximal := hMmax
    haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
    have hht : (M.height : WithBot ℕ∞) = ringKrullDim A :=
      height_eq_ringKrullDim_of_isMaximal (K := K) M
    rw [← hht]
    exact Ideal.height_le_ringKrullDim_quotient_add_one
      (hleM (Ideal.subset_span (Set.mem_singleton g)))

/-- If `A` is a finitely generated domain over a field and `0 ≠ g ∈ A` is a nonunit, then there
is `d ≠ 0` with `dim A = d` and `dim (A ⧸ (g)) = d - 1`. -/
theorem exists_ringKrullDim_quotient_span_singleton_add_one {K A : Type*} [Field K] [CommRing A]
    [IsDomain A] [Algebra K A] [Algebra.FiniteType K A] {g : A} (hg : g ≠ 0)
    (hgu : ¬ IsUnit g) :
    ∃ d : ℕ, 0 < d ∧ ringKrullDim A = (d : WithBot ℕ∞) ∧
      ringKrullDim (A ⧸ Ideal.span {g}) = ((d - 1 : ℕ) : WithBot ℕ∞) := by
  obtain ⟨s, φ, hφinj, hφfin⟩ := exists_finite_inj_algHom_of_fg K A
  let B := MvPolynomial (Fin s) K
  letI : Algebra B A := φ.toRingHom.toAlgebra
  have hmap : algebraMap B A = φ.toRingHom := rfl
  haveI : IsScalarTower K B A := IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  haveI : Module.Finite B A := hφfin
  haveI : Algebra.IsIntegral B A := Algebra.IsIntegral.of_finite B A
  haveI : FaithfulSMul B A :=
    (faithfulSMul_iff_algebraMap_injective B A).mpr (by rw [hmap]; exact hφinj)
  have hdim : ringKrullDim A = (s : WithBot ℕ∞) := by
    rw [Commons.RingTheory.KrullDimension.ringKrullDim_eq_of_isIntegral
        (by rw [hmap]; exact hφinj),
      MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  have hdrop : ringKrullDim (A ⧸ Ideal.span {g}) + 1 = ringKrullDim A :=
    ringKrullDim_quotient_span_singleton_add_one (K := K) hg hgu
  haveI : Nontrivial (A ⧸ Ideal.span {g}) :=
    Ideal.Quotient.nontrivial_iff.mpr (Ideal.span_singleton_eq_top.not.mpr hgu)
  have hpos : 0 < s := by
    have h1 : (1 : WithBot ℕ∞) ≤ ringKrullDim A := by
      rw [← hdrop]
      calc (1 : WithBot ℕ∞) = 0 + 1 := by simp
        _ ≤ ringKrullDim (A ⧸ Ideal.span {g}) + 1 := by
            gcongr; exact ringKrullDim_nonneg_of_nontrivial
    rw [hdim] at h1
    have h2 : (1 : ℕ∞) ≤ (s : ℕ∞) := WithBot.coe_le_coe.mp h1
    have h2' : (1 : ℕ) ≤ s := ENat.natCast_le_natCast.mp h2
    omega
  have hquot : ringKrullDim (A ⧸ Ideal.span {g}) = ((s - 1 : ℕ) : WithBot ℕ∞) := by
    have hne : ringKrullDim (A ⧸ Ideal.span {g}) ≠ ⊥ := by
      intro h0
      rw [h0, WithBot.bot_add, hdim] at hdrop
      exact WithBot.bot_ne_coe hdrop
    obtain ⟨D, hD⟩ := WithBot.ne_bot_iff_exists.mp hne
    have hD1 : D + 1 = (s : ℕ∞) := by
      have h' : ((D + 1 : ℕ∞) : WithBot ℕ∞) = ((s : ℕ∞) : WithBot ℕ∞) := by
        rw [← hD, hdim] at hdrop
        rw [WithBot.coe_add, WithBot.coe_one]
        exact hdrop
      exact WithBot.coe_inj.mp h'
    have hDtop : D ≠ ⊤ := by
      intro htop
      rw [htop, top_add] at hD1
      exact ENat.natCast_ne_top s hD1.symm
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hDtop
    have hn1 : n + 1 = s := by
      have h := hD1
      rw [← hn] at h
      have h' : ((n + 1 : ℕ) : ℕ∞) = (s : ℕ∞) := by push_cast; exact h
      exact_mod_cast h'
    have hn2 : n = s - 1 := by omega
    rw [← hD, ← hn, hn2]
    push_cast
    rfl
  exact ⟨s, hpos, hdim, hquot⟩

/-- If `p` is a homogeneous prime ideal of the polynomial ring `k[X₁,…,Xₘ]` over a field `k`,
`f ∉ p` is a nonzero polynomial with `p + (f) ≠ ⊤`, then the dimension of `R ⧸ p` is `d ≠ 0`
and the dimension of `R ⧸ (p + (f))` is `d - 1`. -/
theorem dim_quotient_sup_span_eq_dim_sub_one {k : Type} [Field k] {m : ℕ}
    (p : Ideal (MvPolynomial (Fin m) k)) [p.IsPrime]
    (hp : ∀ x ∈ p, ∀ j, MvPolynomial.homogeneousComponent j x ∈ p)
    {f : MvPolynomial (Fin m) k} (hf : f ∉ p) (hf0 : f ≠ 0)
    (hproper : p ⊔ Ideal.span {f} ≠ ⊤) :
    ∃ d : ℕ, ringKrullDim (MvPolynomial (Fin m) k ⧸ p) = (d : WithBot ℕ∞) ∧ d ≠ 0 ∧
      ringKrullDim (MvPolynomial (Fin m) k ⧸ (p ⊔ Ideal.span {f})) = ((d - 1 : ℕ) : WithBot ℕ∞) := by
  let A := MvPolynomial (Fin m) k ⧸ p
  let g : A := Ideal.Quotient.mk p f
  haveI : IsDomain A := Ideal.Quotient.isDomain p
  have hg : g ≠ 0 := by
    change Ideal.Quotient.mk p f ≠ 0
    exact fun h => hf (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hspan : (Ideal.span {f}).map (Ideal.Quotient.mk p) = Ideal.span {g} := by
    rw [Ideal.map_span, Set.image_singleton]
  have hgu : ¬ IsUnit g := by
    rw [← Ideal.span_singleton_eq_top]
    intro htop
    have hdom : Subsingleton ((MvPolynomial (Fin m) k ⧸ p) ⧸
        (Ideal.span {f}).map (Ideal.Quotient.mk p)) := by
      rw [hspan, htop]
      infer_instance
    have hsub : Subsingleton ((MvPolynomial (Fin m) k) ⧸ (p ⊔ Ideal.span {f})) := by
      haveI := hdom
      refine ⟨fun x y => ?_⟩
      have hxy : (DoubleQuot.quotQuotEquivQuotSup p (Ideal.span {f})).symm x
          = (DoubleQuot.quotQuotEquivQuotSup p (Ideal.span {f})).symm y :=
        Subsingleton.elim _ _
      simpa using congrArg (DoubleQuot.quotQuotEquivQuotSup p (Ideal.span {f})) hxy
    exact hproper (Ideal.Quotient.subsingleton_iff.mp hsub)
  obtain ⟨d, hd0, hdA, hdquot⟩ :=
    exists_ringKrullDim_quotient_span_singleton_add_one (K := k) (A := A) hg hgu
  refine ⟨d, ?_, hd0.ne', ?_⟩
  · exact hdA
  · have he : (A ⧸ Ideal.span {g}) ≃+* (MvPolynomial (Fin m) k) ⧸ (p ⊔ Ideal.span {f}) :=
      (Ideal.quotEquivOfEq hspan.symm).trans
        (DoubleQuot.quotQuotEquivQuotSup p (Ideal.span {f}))
    have heq2 : ringKrullDim (MvPolynomial (Fin m) k ⧸ (p ⊔ Ideal.span {f}))
        = ringKrullDim (A ⧸ Ideal.span {g}) :=
      (ringKrullDim_eq_of_ringEquiv
        (R := A ⧸ Ideal.span {g})
        (S := MvPolynomial (Fin m) k ⧸ (p ⊔ Ideal.span {f})) he).symm
    rw [heq2, hdquot]

end Commons.RingTheory.Ideal.Hilbert