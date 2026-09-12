import Mathlib
import Submission.Commons.Algebra.MvPolynomial.finite_adjoin_range_of_finite_quotient
import Submission.Commons.Algebra.MvPolynomial.quotient_span_range_X_castLE_algEquiv
import Submission.Commons.Algebra.MvPolynomial.isPrime_span_range_X_castLE
import Submission.Commons.Algebra.MvPolynomial.height_idealOfVars

set_option linter.ambiguousOpen false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

namespace Commons.Algebra.MvPolynomial

open _root_.MvPolynomial

theorem ringKrullDim_le_of_isIntegral {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.IsIntegral R A] : ringKrullDim A ≤ ringKrullDim R :=
  Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R A))
    (fun _ _ h => Ideal.IsIntegral.comap_lt_comap h)

theorem ringKrullDim_le_of_adjoin_range_eq_top {m : ℕ} {A : Type*} [CommRing A] [Algebra ℂ A]
    (a : Fin m → A) (h : Algebra.adjoin ℂ (Set.range a) = ⊤) : ringKrullDim A ≤ (m : ℕ) := by
  let ψ : MvPolynomial (Fin m) ℂ →ₐ[ℂ] A := MvPolynomial.aeval a
  have hsurj : Function.Surjective ψ := by
    rw [← AlgHom.range_eq_top, MvPolynomial.aeval_range a, h]
  have h1 : ringKrullDim A ≤ ringKrullDim (MvPolynomial (Fin m) ℂ) :=
    ringKrullDim_le_of_surjective ψ.toRingHom hsurj
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
    Nat.card_eq_fintype_card, Fintype.card_fin] at h1
  exact_mod_cast h1

theorem LTSeries_length_le_ringKrullDim_quotient {R : Type*} [CommRing R] {J : Ideal R}
    (l : LTSeries (PrimeSpectrum R)) (h : J ≤ (l 0).asIdeal) :
    (l.length : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ J) := by
  have hall : ∀ i : Fin (l.length + 1), J ≤ (l i).asIdeal := fun i =>
    le_trans h (l.monotone (Fin.zero_le i))
  let l₁ : LTSeries ↥(PrimeSpectrum.zeroLocus (J : Set R)) :=
    { length := l.length
      toFun := fun i => ⟨l i, by rw [PrimeSpectrum.mem_zeroLocus]; exact hall i⟩
      step := fun i => l.step i }
  have hlen : l₁.length = l.length := rfl
  have h1 := Order.LTSeries.length_le_krullDim l₁
  rw [hlen] at h1
  have h2 : Order.krullDim ↥(PrimeSpectrum.zeroLocus (J : Set R)) = ringKrullDim (R ⧸ J) := by
    rw [ringKrullDim, Order.krullDim_eq_of_orderIso
      (Ideal.primeSpectrumQuotientOrderIsoZeroLocus J)]
  rwa [h2] at h1

private lemma nat_sub_le_of_le_add {d : ℕ∞} {k n : ℕ} (hkn : k ≤ n)
    (h : (n : ℕ∞) ≤ d + (k : ℕ∞)) : ((n - k : ℕ) : ℕ∞) ≤ d := by
  rw [ENat.natCast_sub, tsub_le_iff_right]
  exact h

private lemma idealOfVars_ne_top (n : ℕ) :
    MvPolynomial.idealOfVars (Fin n) ℂ ≠ ⊤ := by
  intro htop
  have hle : MvPolynomial.idealOfVars (Fin n) ℂ ≤ RingHom.ker MvPolynomial.constantCoeff := by
    rw [MvPolynomial.idealOfVars, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp [RingHom.mem_ker, MvPolynomial.constantCoeff_eq]
  have : (1 : MvPolynomial (Fin n) ℂ) ∈ RingHom.ker MvPolynomial.constantCoeff :=
    hle (htop ▸ Submodule.mem_top)
  simp [RingHom.mem_ker, MvPolynomial.constantCoeff_eq] at this

theorem ringKrullDim_quotient_of_homogeneous_mprimary {n e : ℕ} (g : Fin n → MvPolynomial (Fin n) ℂ)
    (hg : ∀ i, (g i).IsHomogeneous e) (he : 1 ≤ e)
    (hfin : Module.rank ℂ (MvPolynomial (Fin n) ℂ ⧸ Ideal.span (Set.range g)) < Cardinal.aleph0)
    (k : ℕ) (hk : k ≤ n) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸
        Ideal.span (Set.range (fun j : Fin k => g (Fin.castLE hk j)))) = (n - k : ℕ) := by
  have hB := finite_adjoin_range_of_finite_quotient g hg he hfin
  let φ : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ := MvPolynomial.aeval g
  have hrange : φ.range = Algebra.adjoin ℂ (Set.range g) := MvPolynomial.aeval_range g
  have hInt : Algebra.IsIntegral ↥φ.range (MvPolynomial (Fin n) ℂ) := by
    rw [hrange]; exact Algebra.IsIntegral.of_finite _ _
  have hcomp : φ.toRingHom = (algebraMap ↥φ.range (MvPolynomial (Fin n) ℂ)).comp
      (AlgHom.rangeRestrict φ).toRingHom := by
    ext x
    · rfl
    · simp [AlgHom.rangeRestrict]
  have hstrict : StrictMono (PrimeSpectrum.comap φ.toRingHom) := by
    have h1 : StrictMono (PrimeSpectrum.comap (algebraMap ↥φ.range (MvPolynomial (Fin n) ℂ))) :=
      fun P Q h => Ideal.IsIntegral.comap_lt_comap h
    have h2 : StrictMono (PrimeSpectrum.comap (AlgHom.rangeRestrict φ).toRingHom) :=
      RingHom.strictMono_comap_of_surjective (AlgHom.rangeRestrict_surjective φ)
    rw [hcomp, PrimeSpectrum.comap_comp]
    exact h2.comp h1
  have hchain : ∀ l : LTSeries (PrimeSpectrum (MvPolynomial (Fin n) ℂ)),
      Ideal.span (Set.range (fun j : Fin k => g (Fin.castLE hk j))) ≤ (l 0).asIdeal →
      l.length ≤ n - k := by
    intro l hl
    haveI : Algebra.IsIntegral ↥φ.range (MvPolynomial (Fin n) ℂ) := hInt
    let l' : LTSeries (PrimeSpectrum (MvPolynomial (Fin n) ℂ)) :=
      l.map (PrimeSpectrum.comap φ.toRingHom) hstrict
    have hlen : l'.length = l.length := LTSeries.map_length _ _ _
    have hJk : (Ideal.span (Set.range (fun i : Fin k =>
        (MvPolynomial.X (Fin.castLE hk i) : MvPolynomial (Fin n) ℂ)))) ≤ (l' 0).asIdeal := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rw [show (l' 0).asIdeal = Ideal.comap φ.toRingHom (l 0).asIdeal from
        PrimeSpectrum.comap_asIdeal φ.toRingHom (l 0)]
      change φ.toRingHom (MvPolynomial.X (Fin.castLE hk i)) ∈ (l 0).asIdeal
      rw [show φ.toRingHom (MvPolynomial.X (Fin.castLE hk i)) = g (Fin.castLE hk i) from
        MvPolynomial.aeval_X g _]
      exact hl (Ideal.subset_span ⟨i, rfl⟩)
    have h1 := LTSeries_length_le_ringKrullDim_quotient l' hJk
    have h2 : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸
        Ideal.span (Set.range (fun i : Fin k =>
          (MvPolynomial.X (Fin.castLE hk i) : MvPolynomial (Fin n) ℂ)))) =
        ((n - k : ℕ) : WithBot ℕ∞) := by
      obtain ⟨ee⟩ := quotient_span_range_X_castLE_algEquiv hk
      rw [ringKrullDim_eq_of_ringEquiv ee.toRingEquiv,
        MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
        Nat.card_eq_fintype_card, Fintype.card_fin]
    rw [hlen, h2] at h1
    exact_mod_cast h1
  have hIVle : Ideal.span (Set.range (fun j : Fin k => g (Fin.castLE hk j))) ≤
      MvPolynomial.idealOfVars (Fin n) ℂ := by
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    rw [MvPolynomial.idealOfVars,
      show Set.range (MvPolynomial.X) = MvPolynomial.X '' (Set.univ : Set (Fin n)) from by simp]
    change g (Fin.castLE hk j) ∈ Ideal.span (MvPolynomial.X '' (Set.univ : Set (Fin n)))
    rw [MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    have hmdeg : Finsupp.degree m = e := by
      by_contra hc
      exact (MvPolynomial.mem_support_iff.mp hm) ((hg (Fin.castLE hk j)).coeff_eq_zero hc)
    have hne0 : m ≠ 0 := by
      intro h0
      have h1 : Finsupp.degree m = 0 := by rw [h0, Finsupp.degree_eq_zero_iff]
      omega
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hne0
    exact ⟨i, Set.mem_univ i, hi⟩
  haveI : Nontrivial (MvPolynomial (Fin n) ℂ ⧸
      Ideal.span (Set.range (fun j : Fin k => g (Fin.castLE hk j)))) :=
    Ideal.Quotient.nontrivial_iff.mpr (fun htop =>
      idealOfVars_ne_top n (top_le_iff.mp (htop ▸ hIVle)))
  have hup : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸
      Ideal.span (Set.range (fun j : Fin k => g (Fin.castLE hk j)))) ≤ ((n - k : ℕ) : WithBot ℕ∞) := by
    rw [ringKrullDim, Order.krullDim_eq_iSup_length,
      ← WithBot.coe_natCast, WithBot.coe_le_coe, iSup_le_iff]
    intro l
    let J : Ideal (MvPolynomial (Fin n) ℂ) :=
      Ideal.span (Set.range (fun j : Fin k => g (Fin.castLE hk j)))
    let l₁ : LTSeries ↥(PrimeSpectrum.zeroLocus (J : Set (MvPolynomial (Fin n) ℂ))) :=
      l.map (Ideal.primeSpectrumQuotientOrderIsoZeroLocus J) (OrderIso.strictMono _)
    let l₂ : LTSeries (PrimeSpectrum (MvPolynomial (Fin n) ℂ)) :=
      l₁.map Subtype.val (fun _ _ h => h)
    have hlen : l₂.length = l.length := by
      calc l₂.length = l₁.length := LTSeries.map_length _ _ _
        _ = l.length := LTSeries.map_length _ _ _
    have hJ : J ≤ (l₂ 0).asIdeal := by
      simp only [l₂, l₁]
      exact (l.map (Ideal.primeSpectrumQuotientOrderIsoZeroLocus J)
        (OrderIso.strictMono _) 0).2
    have hmain := hchain l₂ (by simpa only [J] using hJ)
    rw [hlen] at hmain
    exact_mod_cast hmain
  have hlow : ((n - k : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸
      Ideal.span (Set.range (fun j : Fin k => g (Fin.castLE hk j)))) := by
    set J : Ideal (MvPolynomial (Fin n) ℂ) :=
      Ideal.span (Set.range (fun j : Fin k => g (Fin.castLE hk j))) with hJdef
    have hJle : J ≤ MvPolynomial.idealOfVars (Fin n) ℂ := by
      rw [hJdef]; exact hIVle
    haveI hIVprime : (MvPolynomial.idealOfVars (Fin n) ℂ).IsPrime := by
      rw [← Commons.Algebra.MvPolynomial.ker_aeval_zero_eq_idealOfVars n]
      exact RingHom.ker_isPrime _
    have hK := Ideal.height_le_ringKrullDim_quotient_add_encard (R := MvPolynomial (Fin n) ℂ)
      (p := MvPolynomial.idealOfVars (Fin n) ℂ)
      (s := Set.range (fun j : Fin k => g (Fin.castLE hk j)))
      (by rintro _ ⟨j, rfl⟩; exact hJle (Ideal.subset_span ⟨j, rfl⟩))
    rw [height_idealOfVars] at hK
    rw [show Ideal.span (Set.range (fun j : Fin k => g (Fin.castLE hk j))) = J from hJdef.symm] at hK
    -- arithmetic
    have hne : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≠ ⊥ := by
      intro hbot
      have h0 := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Fin n) ℂ ⧸ J)
      rw [hbot] at h0
      exact not_le_of_gt (WithBot.bot_lt_coe (0 : ℕ∞)) h0
    obtain ⟨e', he'⟩ := WithBot.ne_bot_iff_exists.mp hne
    · have hK' : (n : ℕ∞) ≤ e' +
          (Set.range (fun j : Fin k => g (Fin.castLE hk j))).encard := by
        have := hK
        rw [← he'] at this
        rw [← WithBot.coe_add, WithBot.coe_le_coe] at this
        exact this
      have henc : (Set.range (fun j : Fin k => g (Fin.castLE hk j))).encard ≤ (k : ℕ∞) := by
        have h1 : (Set.range (fun j : Fin k => g (Fin.castLE hk j))).encard
            ≤ (Set.univ : Set (Fin k)).encard := by
          rw [show Set.range (fun j : Fin k => g (Fin.castLE hk j))
              = (fun j : Fin k => g (Fin.castLE hk j)) '' Set.univ from by simp]
          exact Set.encard_image_le _ _
        rw [Set.encard_univ, ENat.card_eq_coe_natCard, Nat.card_eq_fintype_card,
          Fintype.card_fin] at h1
        exact h1
      have h2 : (n : ℕ∞) ≤ e' + (k : ℕ∞) := hK'.trans (add_le_add (le_refl e') henc)
      have h3 : ((n - k : ℕ) : ℕ∞) ≤ e' := nat_sub_le_of_le_add hk h2
      rw [← he', ← WithBot.coe_natCast, WithBot.coe_le_coe]
      exact h3

  exact le_antisymm hup hlow

end Commons.Algebra.MvPolynomial
