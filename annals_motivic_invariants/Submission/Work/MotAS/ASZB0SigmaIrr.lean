import Mathlib
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

namespace Work.MotAS

section Helpers

private lemma erase_sdiff_eq (a : ZMod 5) (s : Finset (ZMod 5)) :
    (Finset.univ \ s).erase a = Finset.univ \ insert a s := by
  ext x
  simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
    not_or]

private lemma not_dvd_prod {L : Type*} [Field L] (G : ZMod 5 → MvPolynomial (Fin 2) L)
    (hirr : ∀ i, Irreducible (G i)) (hne : ∀ i j, i ≠ j → ¬ Associated (G i) (G j))
    (i : ZMod 5) : ∀ s : Finset (ZMod 5), i ∉ s → ¬ G i ∣ ∏ j ∈ s, G j := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro _ h
      rw [Finset.prod_empty] at h
      exact (hirr i).not_isUnit (isUnit_iff_dvd_one.mpr h)
  | insert a s has ih =>
      intro his h
      rw [Finset.prod_insert has] at h
      rcases ((hirr i).prime.dvd_mul).mp h with h' | h'
      · refine (hne i a ?_) ((hirr i).associated_of_dvd (hirr a) h')
        intro hia
        rw [hia] at his
        exact his (Finset.mem_insert_self a s)
      · exact ih (fun hmem => his (Finset.mem_insert_of_mem hmem)) h'

private lemma key {L : Type*} [Field L] (G : ZMod 5 → MvPolynomial (Fin 2) L)
    (hirr : ∀ i, Irreducible (G i)) (hne : ∀ i j, i ≠ j → ¬ Associated (G i) (G j))
    (hne0 : ∀ i, G i ≠ 0) (u : L) (hu : IsUnit u) (P Q : MvPolynomial (Fin 2) L)
    (hPQ : P * Q = MvPolynomial.C u * ∏ i, G i) (hPi : ∀ i, G i ∣ P) : IsUnit Q := by
  classical
  have hCu : IsUnit (MvPolynomial.C u : MvPolynomial (Fin 2) L) :=
    IsUnit.map (MvPolynomial.C : L →+* MvPolynomial (Fin 2) L) hu
  have hmain : ∀ t : Finset (ZMod 5), ∃ P' : MvPolynomial (Fin 2) L,
      P = (∏ i ∈ t, G i) * P' ∧
        P' * Q = MvPolynomial.C u * ∏ i ∈ (Finset.univ \ t), G i := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        exact ⟨P, by simp, by rw [Finset.sdiff_empty]; simpa using hPQ⟩
    | insert a s has ih =>
        obtain ⟨P', hP1, hP2⟩ := ih
        have hmem : a ∈ Finset.univ \ s := by simp [has]
        have hnotdvd : ¬ G a ∣ ∏ i ∈ s, G i := not_dvd_prod G hirr hne a s has
        have hdvd : G a ∣ P' := by
          have h : G a ∣ (∏ i ∈ s, G i) * P' := hP1 ▸ hPi a
          rcases ((hirr a).prime.dvd_mul).mp h with h' | h'
          · exact absurd h' hnotdvd
          · exact h'
        obtain ⟨P'', rfl⟩ := hdvd
        refine ⟨P'', ?_, ?_⟩
        · rw [Finset.prod_insert has, hP1]
          first | refl_ring1 | ring
        · have hprod : (∏ i ∈ Finset.univ \ s, G i)
              = G a * ∏ i ∈ Finset.univ \ insert a s, G i := by
            rw [← Finset.mul_prod_erase (Finset.univ \ s) G hmem, erase_sdiff_eq a s]
          refine mul_left_cancel₀ (hne0 a) ?_
          calc G a * (P'' * Q)
              = (G a * P'') * Q := (mul_assoc _ _ _).symm
            _ = MvPolynomial.C u * ∏ i ∈ Finset.univ \ s, G i := hP2
            _ = MvPolynomial.C u * (G a * ∏ i ∈ Finset.univ \ insert a s, G i) := by rw [hprod]
            _ = G a * (MvPolynomial.C u * ∏ i ∈ Finset.univ \ insert a s, G i) := by ring
  obtain ⟨P', _, hP2⟩ := hmain Finset.univ
  rw [Finset.sdiff_self, Finset.prod_empty, mul_one] at hP2
  have hQdvd : Q ∣ MvPolynomial.C u := ⟨P', by rw [← hP2, mul_comm]⟩
  exact isUnit_iff_dvd_one.mpr (dvd_trans hQdvd (isUnit_iff_dvd_one.mp hCu))

private lemma map_sigma_map_algebraMap {K L : Type*} [Field K] [Field L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (p : MvPolynomial (Fin 2) K) :
    MvPolynomial.map (σ : L →+* L) (MvPolynomial.map (algebraMap K L) p)
      = MvPolynomial.map (algebraMap K L) p := by
  rw [MvPolynomial.map_map]
  have h : (σ : L →+* L).comp (algebraMap K L) = algebraMap K L := by
    ext x
    exact σ.commutes x
  rw [h]

private lemma dvd_all_of_dvd_zero {K L : Type*} [Field K] [Field L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (G : ZMod 5 → MvPolynomial (Fin 2) L)
    (hconj : ∀ i, MvPolynomial.map (σ : L →+* L) (G i) = G (i + 1))
    (P : MvPolynomial (Fin 2) L) (hσP : MvPolynomial.map (σ : L →+* L) P = P)
    (h0 : G 0 ∣ P) : ∀ i, G i ∣ P := by
  have hstep : ∀ i : ZMod 5, G i ∣ P → G (i + 1) ∣ P := by
    intro i hi
    obtain ⟨c, hc⟩ := hi
    refine ⟨MvPolynomial.map (σ : L →+* L) c, ?_⟩
    calc P = MvPolynomial.map (σ : L →+* L) P := hσP.symm
      _ = MvPolynomial.map (σ : L →+* L) (G i * c) := by rw [hc]
      _ = MvPolynomial.map (σ : L →+* L) (G i) * MvPolynomial.map (σ : L →+* L) c :=
            (MvPolynomial.map (σ : L →+* L)).map_mul _ _
      _ = G (i + 1) * MvPolynomial.map (σ : L →+* L) c := by rw [hconj i]
  have hchain : ∀ n : ℕ, G ((n : ℕ) : ZMod 5) ∣ P := by
    intro n
    induction n with
    | zero => simpa using h0
    | succ k ih =>
        have := hstep ((k : ℕ) : ZMod 5) ih
        simpa [Nat.cast_succ, Nat.cast_add, Nat.cast_one] using this
  intro i
  simpa [ZMod.natCast_zmod_val] using hchain i.val

private lemma isUnit_of_map_isUnit {K L : Type*} [Field K] [Field L] [Algebra K L]
    (p : MvPolynomial (Fin 2) K) (h : IsUnit (MvPolynomial.map (algebraMap K L) p)) :
    IsUnit p := by
  have hinj : Function.Injective (algebraMap K L) := by
    intro a b hab
    have h1 : algebraMap K L (a - b) = 0 := by rw [map_sub, hab, sub_self]
    by_cases h' : a - b = 0
    · exact sub_eq_zero.mp h'
    · have h3 : algebraMap K L ((a - b)⁻¹ * (a - b)) = 0 := by
        rw [(algebraMap K L).map_mul, h1, mul_zero]
      have h4 : (1 : L) = 0 := by rwa [inv_mul_cancel₀ h', map_one] at h3
      exact absurd h4 one_ne_zero
  obtain ⟨r, hr, hp⟩ :=
    (MvPolynomial.isUnit_iff_eq_C_of_isReduced (P := MvPolynomial.map (algebraMap K L) p)).mp h
  have hcoeff : ∀ m : Fin 2 →₀ ℕ, algebraMap K L (p.coeff m) = (MvPolynomial.C r).coeff m := by
    intro m
    rw [← hp, MvPolynomial.coeff_map]
  have h0 : p.coeff 0 ≠ 0 := by
    intro hc
    have hr0 : r = 0 := by
      have hh := hcoeff 0
      rw [hc, map_zero] at hh
      simpa [MvPolynomial.coeff_C] using hh.symm
    exact hr.ne_zero hr0
  have hconst : p = MvPolynomial.C (p.coeff 0) := by
    ext m
    by_cases hm : m = 0
    · subst hm
      simp [MvPolynomial.coeff_C]
    · have hm' : algebraMap K L (p.coeff m) = 0 := by
        have hh := hcoeff m
        rw [MvPolynomial.coeff_C, if_neg (Ne.symm hm)] at hh
        exact hh
      have hz : p.coeff m = 0 := hinj (by simpa using hm')
      rw [hz, MvPolynomial.coeff_C, if_neg (Ne.symm hm)]
  rw [hconst]
  exact IsUnit.map (MvPolynomial.C : K →+* MvPolynomial (Fin 2) K) (isUnit_iff_ne_zero.mpr h0)

end Helpers

theorem ASZB0SigmaIrr (K : Type) [Field K] (L : Type) [Field L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (f : MvPolynomial (Fin 2) K) (u : L) (hu : IsUnit u)
    (G : ZMod 5 → MvPolynomial (Fin 2) L)
    (hirr : ∀ i, Irreducible (G i))
    (hconj : ∀ i, MvPolynomial.map (σ : L →+* L) (G i) = G (i + 1))
    (hfac : MvPolynomial.map (algebraMap K L) f = MvPolynomial.C u * ∏ i, G i)
    (hne : ∀ i j, i ≠ j → ¬ Associated (G i) (G j)) :
    Irreducible f := by
  classical
  have hne0 : ∀ i, G i ≠ 0 := fun i => (hirr i).ne_zero
  refine ⟨?_, ?_⟩
  · intro hf
    have h1 : IsUnit (MvPolynomial.map (algebraMap K L) f) :=
      IsUnit.map (MvPolynomial.map (algebraMap K L)) hf
    rw [hfac] at h1
    have hdiv : (∏ i, G i) ∣ (1 : MvPolynomial (Fin 2) L) :=
      dvd_trans ⟨MvPolynomial.C u, mul_comm _ _⟩ (isUnit_iff_dvd_one.mp h1)
    have h3 : G 0 ∣ (1 : MvPolynomial (Fin 2) L) :=
      dvd_trans (Finset.dvd_prod_of_mem G (Finset.mem_univ 0)) hdiv
    exact (hirr 0).not_isUnit (isUnit_iff_dvd_one.mpr h3)
  · intro p q hpq
    have hPQ : MvPolynomial.map (algebraMap K L) p * MvPolynomial.map (algebraMap K L) q
        = MvPolynomial.C u * ∏ i, G i := by
      rw [← (MvPolynomial.map (algebraMap K L)).map_mul, ← hpq]
      exact hfac
    have hσp : MvPolynomial.map (σ : L →+* L) (MvPolynomial.map (algebraMap K L) p)
        = MvPolynomial.map (algebraMap K L) p := map_sigma_map_algebraMap σ p
    have hσq : MvPolynomial.map (σ : L →+* L) (MvPolynomial.map (algebraMap K L) q)
        = MvPolynomial.map (algebraMap K L) q := map_sigma_map_algebraMap σ q
    have hsplit : ∀ i, G i ∣ MvPolynomial.map (algebraMap K L) p ∨
        G i ∣ MvPolynomial.map (algebraMap K L) q := by
      intro i
      have h1 : G i ∣ MvPolynomial.map (algebraMap K L) p * MvPolynomial.map (algebraMap K L) q := by
        rw [hPQ]
        exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem G (Finset.mem_univ i))
          (MvPolynomial.C u)
      exact ((hirr i).prime.dvd_mul).mp h1
    by_cases h0 : G 0 ∣ MvPolynomial.map (algebraMap K L) p
    · have hall := dvd_all_of_dvd_zero σ G hconj _ hσp h0
      have hkey := key G hirr hne hne0 u hu _ _ hPQ hall
      exact Or.inr (isUnit_of_map_isUnit q hkey)
    · have h0' : G 0 ∣ MvPolynomial.map (algebraMap K L) q := by
        rcases hsplit 0 with h | h
        · exact absurd h h0
        · exact h
      have hall := dvd_all_of_dvd_zero σ G hconj _ hσq h0'
      have hPQ' : MvPolynomial.map (algebraMap K L) q * MvPolynomial.map (algebraMap K L) p
          = MvPolynomial.C u * ∏ i, G i := by rw [mul_comm]; exact hPQ
      have hkey := key G hirr hne hne0 u hu _ _ hPQ' hall
      exact Or.inl (isUnit_of_map_isUnit p hkey)

end Work.MotAS
