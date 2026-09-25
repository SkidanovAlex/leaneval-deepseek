import Mathlib
import Submission.NK.UchidaKummer.Defs
import Submission.NK.UchidaKummer.Approximation.isWeakApproximation
import Submission.NK.UchidaKummer.Approximation.isOpenEllPowSubgroup
import Submission.NK.UchidaKummer.Approximation.isKummerSurjective_of_weakApproximation
import Submission.NK.UchidaKummer.Approximation.exists_not_ellPow_unit_adicCompletion

namespace NK.UchidaKummer.Embedding

open scoped Classical

noncomputable section

theorem exists_localPowClass_family {L : Type*} [Field L] [NumberField L] (ℓ : ℕ) (hℓ : ℓ.Prime)
    (T S : Finset (NK.Chebotarev.PrimeIdeal L)) (hdisj : ∀ 𝔮 ∈ S, 𝔮 ∉ T) :
    ∃ b : NK.Chebotarev.PrimeIdeal L → Lˣ,
      (∀ P ∈ T, NK.UchidaKummer.localPowClass L ℓ P (b P) ≠ 1) ∧
      (∀ P ∈ T, ∀ 𝔮 ∈ S ∪ T, 𝔮 ≠ P →
        NK.UchidaKummer.localPowClass L ℓ 𝔮 (b P) = 1) := by
  classical
  -- Weak approximation plus openness of the local `ℓ`-th power subgroups give the Kummer
  -- surjection at `S ∪ T`.
  have hsurj : NK.UchidaKummer.IsKummerSurjective L ℓ (S ∪ T) :=
    NK.UchidaKummer.Approximation.isKummerSurjective_of_weakApproximation (K := L) ℓ (S ∪ T)
      (NK.UchidaKummer.Approximation.isWeakApproximation L (S ∪ T))
      (NK.UchidaKummer.Approximation.isOpenEllPowSubgroup L ℓ hℓ)
  -- At each prime of `T`, a local unit which is not an `ℓ`-th power.
  choose u hu using fun P : ↥T =>
    NK.UchidaKummer.Approximation.exists_not_ellPow_unit_adicCompletion (K := L) ℓ hℓ P.1
  -- For `P ∈ T`, the prescribed tuple of local `ℓ`-power classes: the class of `u P` at `P`,
  -- and the trivial class at every other prime of `S ∪ T`.
  have hfamily : ∀ P : ↥T, ∃ b : Lˣ, ∀ 𝔮 : ↥(S ∪ T),
      NK.UchidaKummer.localPowClass L ℓ 𝔮.1 b =
        (if h : 𝔮.1 = P.1 then
          QuotientGroup.mk' (NK.UchidaKummer.ellPowSubgroup (𝔮.1.adicCompletion L) ℓ)
            (if h' : 𝔮.1 ∈ T then (u ⟨𝔮.1, h'⟩ : (𝔮.1.adicCompletion L)ˣ) else 1)
        else 1) := fun P => hsurj _
  choose b hb using hfamily
  have hbval : ∀ (P : NK.Chebotarev.PrimeIdeal L) (hP : P ∈ T),
      (fun Q => if h : Q ∈ T then b ⟨Q, h⟩ else 1) P = b ⟨P, hP⟩ :=
    fun P hP => dif_pos hP
  refine ⟨fun Q => if h : Q ∈ T then b ⟨Q, h⟩ else 1, ?_, ?_⟩
  · -- Non-triviality of the class at the primes of `T`.
    intro P hP
    rw [hbval P hP]
    intro h1
    have h2 := hb ⟨P, hP⟩ ⟨P, Finset.mem_union_right S hP⟩
    rw [h1] at h2
    have h3 : QuotientGroup.mk' (NK.UchidaKummer.ellPowSubgroup (P.adicCompletion L) ℓ)
        (u ⟨P, hP⟩) = 1 := by
      simpa [dif_pos hP, dif_pos rfl] using h2.symm
    have hmem : u ⟨P, hP⟩ ∈ NK.UchidaKummer.ellPowSubgroup (P.adicCompletion L) ℓ :=
      (QuotientGroup.eq_one_iff _).mp (by rwa [QuotientGroup.mk'_apply] at h3)
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hmem
    exact hu ⟨P, hP⟩ c hc
  · -- Triviality of the class at all the other primes of `S ∪ T`.
    intro P hP 𝔮 h𝔮 hne
    rw [hbval P hP]
    have h2 := hb ⟨P, hP⟩ ⟨𝔮, h𝔮⟩
    have hne' : ¬ (((⟨𝔮, h𝔮⟩ : ↥(S ∪ T)) : NK.Chebotarev.PrimeIdeal L) = P) := hne
    simpa [dif_neg hne'] using h2

end

end NK.UchidaKummer.Embedding
