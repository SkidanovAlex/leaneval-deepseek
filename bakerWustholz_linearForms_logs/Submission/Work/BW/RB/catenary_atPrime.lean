import Mathlib
import Submission.Work.BW.RB.localization_quotient_height
import Submission.Work.BW.RB.finite_extension_domain_height
import Submission.Work.BW.RB.mvpoly_dim_formula


namespace Work.BW.RB

/-!
# The catenary inequality at a maximal ideal of a polynomial ring over `ℂ`

For `R = ℂ[σ]_𝔪` (`σ` finite, `𝔪` a maximal ideal of `ℂ[σ]`, the local ring of a `ℂ`-point of
affine space) and prime ideals `P ≤ Q` of `R`,

  `ht Q ≤ ht P + ht (Q / P)`,

the nontrivial (catenary) direction; the reverse inequality is the elementary concatenation of
chains and holds in any ring.

The argument transports everything to the polynomial ring `A = ℂ[σ]`: primes of `R` are the
extensions of the primes of `A` contained in `𝔪`, and heights (including the relative height,
i.e. the height in `R ⧸ P ≅ (A ⧸ 𝔭)_{𝔪 ⧸ 𝔭}`) are preserved by localization.  The inequality for
`A` is the dimension formula for finitely generated domains over `ℂ`,

  `ht q + dim (D ⧸ q) = dim D`   (`q` prime, `D` a f.g. `ℂ`-domain),

proved here from the two ingredients supplied in this workspace:
`Work.BW.RB.mvpoly_dim_formula` (the polynomial case, via the local dimension formula at a
maximal ideal) and `Work.BW.RB.finite_extension_domain_height` (a finite injective extension of
domains with integrally closed base preserves heights and Krull dimension, applied to a Noether
normalization `ℂ[X₁,…,X_s] ↪ D`).
-/

/-- Cancellation in `ℕ∞ = ENat` when the common summand is finite. -/
private lemma enat_cancel {x y e : ℕ∞} (he : e ≠ ⊤) (h : x + e = y + e) : x ≤ y := by
  rcases eq_or_ne x (⊤ : ℕ∞) with hx | hx
  · have hy : y = ⊤ := by
      rw [hx, top_add] at h
      by_contra hy
      obtain ⟨y', hy'⟩ := ENat.ne_top_iff_exists.mp hy
      obtain ⟨e', he'⟩ := ENat.ne_top_iff_exists.mp he
      rw [← hy', ← he'] at h
      have hne : (↑y' + ↑e' : ℕ∞) ≠ ⊤ := by
        rw [← Nat.cast_add]
        exact ne_of_lt (ENat.natCast_lt_top (y' + e'))
      exact hne h.symm
    rw [hy]
    exact le_top
  · rcases eq_or_ne y (⊤ : ℕ∞) with hy | hy
    · rw [hy]; exact le_top
    · obtain ⟨x', hx'⟩ := ENat.ne_top_iff_exists.mp hx
      obtain ⟨y', hy'⟩ := ENat.ne_top_iff_exists.mp hy
      obtain ⟨e', he'⟩ := ENat.ne_top_iff_exists.mp he
      rw [← hx', ← hy', ← he'] at h
      have h2 : x' + e' = y' + e' := by exact_mod_cast h
      rw [← hx', ← hy']
      exact_mod_cast (le_of_eq (Nat.add_right_cancel h2))

/-- Cancellation in `WithBot ℕ∞` when the common summand is finite and nonbottom:
`↑x + z = ↑y + z` with `⊥ ≠ z ≠ ⊤` implies `x ≤ y`. -/
private lemma wbot_cancel {x y : ℕ∞} {z : WithBot ℕ∞} (hzb : z ≠ ⊥) (hz : z ≠ ⊤)
    (h : ((x : ℕ∞) : WithBot ℕ∞) + z = ((y : ℕ∞) : WithBot ℕ∞) + z) : x ≤ y := by
  rcases z with _ | e
  · exact absurd rfl hzb
  · have he : e ≠ ⊤ := fun hc => hz (by rw [hc]; rfl)
    exact enat_cancel he (WithBot.coe_inj.mp h)

/-- **The dimension formula for finitely generated domains over `ℂ`.**  For a finitely generated
`ℂ`-domain `D` and a prime ideal `q`, `ht q + dim (D ⧸ q) = dim D`.

Choose a Noether normalization `C = ℂ[Fin s] ↪ D` (`D` is a finite `C`-module and the map is
injective).  A finite injective extension of domains with integrally closed base preserves both
the height of a prime and the dimension of the quotient by it, so the statement for `D` at `q` is
exactly the statement for `C` at `q ∩ C`, which is `mvpoly_dim_formula`. -/
private lemma fg_domain_dim_formula_aux {D : Type*} [CommRing D] [IsDomain D] [Algebra ℂ D]
    [Algebra.FiniteType ℂ D] (q : Ideal D) [q.IsPrime] :
    ((q.height : ℕ∞) : WithBot ℕ∞) + ringKrullDim (D ⧸ q) = ringKrullDim D := by
  obtain ⟨s, g, hg_inj, hg_fin⟩ := exists_finite_inj_algHom_of_fg ℂ D
  letI : Algebra (MvPolynomial (Fin s) ℂ) D := g.toRingHom.toAlgebra
  haveI : Module.Finite (MvPolynomial (Fin s) ℂ) D := hg_fin
  haveI : FaithfulSMul (MvPolynomial (Fin s) ℂ) D :=
    (faithfulSMul_iff_algebraMap_injective (MvPolynomial (Fin s) ℂ) D).mpr
      (by simpa [RingHom.algebraMap_toAlgebra] using hg_inj)
  haveI : IsDomain (MvPolynomial (Fin s) ℂ) := inferInstance
  haveI : IsIntegrallyClosed (MvPolynomial (Fin s) ℂ) := inferInstance
  obtain ⟨hht, hdim, hdimS⟩ :=
    finite_extension_domain_height (C := MvPolynomial (Fin s) ℂ) (S := D)
  haveI : (q.under (MvPolynomial (Fin s) ℂ)).IsPrime := Ideal.IsPrime.comap _
  have hmv := mvpoly_dim_formula (q.under (MvPolynomial (Fin s) ℂ))
  rw [hht q, hdim q, hdimS]
  exact hmv

theorem catenary_atPrime {σ : Type*} [Fintype σ]
    (𝔪 : Ideal (MvPolynomial σ ℂ)) [𝔪.IsMaximal]
    {P Q : Ideal (Localization.AtPrime 𝔪)} [P.IsPrime] [Q.IsPrime] (h : P ≤ Q) :
    Q.height ≤ P.height + (Q.map (Ideal.Quotient.mk P)).height := by
  have h1 : Q.height = (Q.under (MvPolynomial σ ℂ)).height :=
    (IsLocalization.height_under (𝔪.primeCompl) Q).symm
  have h2 : P.height = (P.under (MvPolynomial σ ℂ)).height :=
    (IsLocalization.height_under (𝔪.primeCompl) P).symm
  have h3 : (Q.map (Ideal.Quotient.mk P)).height =
      ((Q.under (MvPolynomial σ ℂ)).map (Ideal.Quotient.mk (P.under (MvPolynomial σ ℂ)))).height :=
    localization_quotient_height 𝔪 h
  rw [h1, h2, h3]
  set 𝔭 : Ideal (MvPolynomial σ ℂ) := P.under (MvPolynomial σ ℂ) with h𝔭def
  set 𝔮 : Ideal (MvPolynomial σ ℂ) := Q.under (MvPolynomial σ ℂ) with h𝔮def
  have hpq : 𝔭 ≤ 𝔮 := Ideal.comap_mono h
  haveI : 𝔭.IsPrime := Ideal.IsPrime.comap _
  haveI : 𝔮.IsPrime := Ideal.IsPrime.comap _
  haveI : (𝔮.map (Ideal.Quotient.mk 𝔭)).IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hpq
  have e1 : ((𝔮.height : ℕ∞) : WithBot ℕ∞) +
      ringKrullDim (MvPolynomial σ ℂ ⧸ 𝔮) = ringKrullDim (MvPolynomial σ ℂ) :=
    fg_domain_dim_formula_aux 𝔮
  have e2 : ((𝔭.height : ℕ∞) : WithBot ℕ∞) +
      ringKrullDim (MvPolynomial σ ℂ ⧸ 𝔭) = ringKrullDim (MvPolynomial σ ℂ) :=
    fg_domain_dim_formula_aux 𝔭
  have e3 : (((𝔮.map (Ideal.Quotient.mk 𝔭)).height : ℕ∞) : WithBot ℕ∞) +
      ringKrullDim ((MvPolynomial σ ℂ ⧸ 𝔭) ⧸ (𝔮.map (Ideal.Quotient.mk 𝔭))) =
      ringKrullDim (MvPolynomial σ ℂ ⧸ 𝔭) :=
    fg_domain_dim_formula_aux (𝔮.map (Ideal.Quotient.mk 𝔭))
  have e4 : ringKrullDim ((MvPolynomial σ ℂ ⧸ 𝔭) ⧸ (𝔮.map (Ideal.Quotient.mk 𝔭))) =
      ringKrullDim (MvPolynomial σ ℂ ⧸ 𝔮) :=
    ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hpq)
  have key : ((𝔮.height : ℕ∞) : WithBot ℕ∞) + ringKrullDim (MvPolynomial σ ℂ ⧸ 𝔮) =
      (((𝔭.height + (𝔮.map (Ideal.Quotient.mk 𝔭)).height : ℕ∞)) : WithBot ℕ∞) +
        ringKrullDim (MvPolynomial σ ℂ ⧸ 𝔮) := by
    rw [e1, ← e2, ← e3, e4, WithBot.coe_add]
    ring
  have hD3le : ringKrullDim (MvPolynomial σ ℂ ⧸ 𝔮) ≤ ringKrullDim (MvPolynomial σ ℂ) :=
    ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective
  have hA : ringKrullDim (MvPolynomial σ ℂ) = ((Fintype.card σ : ℕ) : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
    simp [Nat.card_eq_fintype_card]
  have hD3top : ringKrullDim (MvPolynomial σ ℂ ⧸ 𝔮) ≠ ⊤ := by
    rw [hA] at hD3le
    exact ne_of_lt (lt_of_le_of_lt hD3le
      (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top (Fintype.card σ))))
  have hD3bot : ringKrullDim (MvPolynomial σ ℂ ⧸ 𝔮) ≠ ⊥ := by
    intro hbot
    haveI : Nontrivial (MvPolynomial σ ℂ ⧸ 𝔮) :=
      Ideal.Quotient.nontrivial_iff.mpr (Ideal.IsPrime.ne_top ‹𝔮.IsPrime›)
    exact (not_subsingleton_iff_nontrivial.mpr inferInstance)
      (ringKrullDim_eq_bot_iff_subsingleton.mp hbot)
  exact wbot_cancel hD3bot hD3top key

end Work.BW.RB
