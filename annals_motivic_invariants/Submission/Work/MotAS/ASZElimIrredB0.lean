import Mathlib
import Submission.Work.MotAS.ASZElimData
import Submission.Work.MotAS.ASZB0ASAut
import Submission.Work.MotAS.ASZB0FacL
import Submission.Work.MotAS.ASZB0Homog
import Submission.Work.MotAS.ASZB0LinearIrred
import Submission.Work.MotAS.ASZB0SigmaIrr
import Submission.Work.TorsorExistence.ArtinSchreier.Irreducible
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotAS

open MvPolynomial

private lemma asz_algebraMap_injective (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] :
    Function.Injective (algebraMap K L) := by
  intro x y hxy
  have h0 : algebraMap K L (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  rw [Algebra.algebraMap_eq_smul_one] at h0
  rcases smul_eq_zero.mp h0 with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h one_ne_zero

/-- Two linear polynomials `C a * X 0 + C b * X 1 + C c` and `C a * X 0 + C b' * X 1 + C c'` with the
same nonzero `X 0`-coefficient: if the second is the first multiplied by the constant `C r`, then
`r = 1` and `b = b'`.  Proved by evaluating at the three points `(X0,X1) = (0,0), (1,0), (0,1)`. -/
private lemma asz_mv_linear {L : Type} [Field L] (a b b' c c' r : L) (ha : a ≠ 0)
    (h : (MvPolynomial.C a * MvPolynomial.X (0 : Fin 2) + MvPolynomial.C b * MvPolynomial.X (1 : Fin 2)
            + MvPolynomial.C c : MvPolynomial (Fin 2) L) * MvPolynomial.C r
          = MvPolynomial.C a * MvPolynomial.X (0 : Fin 2) + MvPolynomial.C b' * MvPolynomial.X (1 : Fin 2)
            + MvPolynomial.C c') :
    r = 1 ∧ b = b' := by
  have h0 := congrArg (MvPolynomial.eval (fun _ : Fin 2 => (0 : L))) h
  have h1 := congrArg (MvPolynomial.eval (fun k : Fin 2 => if k = 0 then (1 : L) else 0)) h
  have h2 := congrArg (MvPolynomial.eval (fun k : Fin 2 => if k = 0 then (0 : L) else 1)) h
  simp only [map_add, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X] at h0 h1 h2
  simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, mul_one, mul_zero, add_zero, zero_add] at h0 h1 h2
  have h0' : c * r = c' := h0
  have h1' : (a + c) * r = a + c' := h1
  have h2' : (b + c) * r = b' + c' := h2
  have h1e : a * r + c * r = a + c' := by linear_combination h1'
  rw [h0'] at h1e
  have har : a * r = a := add_right_cancel h1e
  have hr : r = 1 := mul_left_cancel₀ ha (by rw [har, mul_one])
  refine ⟨hr, ?_⟩
  have h2e : b * r + c * r = b' + c' := by linear_combination h2'
  rw [h0'] at h2e
  have hbr : b * r = b' := add_right_cancel h2e
  rwa [hr, mul_one] at hbr

/-- The five conjugate linear factors of `P 1 0 g` over the Artin–Schreier root field are pairwise
non-associated. -/
private lemma asz_hne_data (K : Type) [Field K] [CharP K 5] (L : Type) [Field L] [Algebra K L]
    (g : K) (hg : g ≠ 0) (θ : L) (i j : ZMod 5) (hij : i ≠ j) :
    ¬ Associated
      (MvPolynomial.C (algebraMap K L g) * MvPolynomial.X (0 : Fin 2)
        + MvPolynomial.C (2 * algebraMap K L g * (θ + algebraMap K L (ZMod.castHom (dvd_refl 5) K i))) * MvPolynomial.X (1 : Fin 2)
        + MvPolynomial.C (4 * ((θ + algebraMap K L (ZMod.castHom (dvd_refl 5) K i)) ^ 3 - (θ + algebraMap K L (ZMod.castHom (dvd_refl 5) K i)))))
      (MvPolynomial.C (algebraMap K L g) * MvPolynomial.X (0 : Fin 2)
        + MvPolynomial.C (2 * algebraMap K L g * (θ + algebraMap K L (ZMod.castHom (dvd_refl 5) K j))) * MvPolynomial.X (1 : Fin 2)
        + MvPolynomial.C (4 * ((θ + algebraMap K L (ZMod.castHom (dvd_refl 5) K j)) ^ 3 - (θ + algebraMap K L (ZMod.castHom (dvd_refl 5) K j))))) := by
  intro h
  obtain ⟨u, hu⟩ := h
  obtain ⟨r, -, hur⟩ := (MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp (Units.isUnit u))
  rw [hur] at hu
  have hinjK : Function.Injective (algebraMap K L) := asz_algebraMap_injective K L
  have hgL : algebraMap K L g ≠ 0 := fun h0 => hg (hinjK (by rw [h0, map_zero]))
  have h2K : (2 : K) ≠ 0 := by
    intro h2
    have hd : (5 : ℕ) ∣ 2 := (CharP.cast_eq_zero_iff K 5 2).mp h2
    norm_num at hd
  have h2L : (2 : L) ≠ 0 := by
    intro h2
    refine h2K (hinjK ?_)
    have h3 : algebraMap K L (2 : K) = 0 := by rw [map_ofNat]; exact h2
    rw [h3, map_zero]
  have hchi : Function.Injective
      (fun i : ZMod 5 => algebraMap K L (ZMod.castHom (dvd_refl 5) K i)) :=
    hinjK.comp (ZMod.castHom_injective K)
  have hmain := asz_mv_linear (algebraMap K L g)
    (2 * algebraMap K L g * (θ + algebraMap K L (ZMod.castHom (dvd_refl 5) K i)))
    (2 * algebraMap K L g * (θ + algebraMap K L (ZMod.castHom (dvd_refl 5) K j)))
    (4 * ((θ + algebraMap K L (ZMod.castHom (dvd_refl 5) K i)) ^ 3 - (θ + algebraMap K L (ZMod.castHom (dvd_refl 5) K i))))
    (4 * ((θ + algebraMap K L (ZMod.castHom (dvd_refl 5) K j)) ^ 3 - (θ + algebraMap K L (ZMod.castHom (dvd_refl 5) K j))))
    r hgL hu
  have hb : θ + algebraMap K L (ZMod.castHom (dvd_refl 5) K i)
      = θ + algebraMap K L (ZMod.castHom (dvd_refl 5) K j) :=
    mul_left_cancel₀ (mul_ne_zero h2L hgL) hmain.2
  exact hij (hchi (add_left_cancel hb))

theorem ASZElimIrredB0 (K : Type) [Field K] [CharP K 5] (a g : K)
    (ha : a ≠ 0) (hg : ¬ ∃ c : K, c ^ 5 - c = g) :
    Irreducible (Work.MotAS.ASZElim.P a 0 g) := by
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact hg ⟨0, by ring⟩
  -- the Artin–Schreier polynomial and its root field
  let p : Polynomial K := Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g
  have hpirr : Irreducible p := by
    have h := Work.TorsorExistence.ArtinSchreier.irreducible_X_pow_five_sub_X_sub_C g hg
    simpa only [p] using h
  haveI : Fact (Irreducible p) := ⟨hpirr⟩
  let L := AdjoinRoot p
  let θ : L := AdjoinRoot.root p
  have hθ : θ ^ 5 - θ = algebraMap K L g := by
    have h1 : Polynomial.aeval θ p = 0 := by
      rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
    have h2 : Polynomial.aeval θ (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g) = 0 := by
      simpa only [p] using h1
    simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C] at h2
    linear_combination (norm := first | refl_ring1 | ring1) h2
  -- the Artin–Schreier automorphism θ ↦ θ + 1
  obtain ⟨σ, hσθ⟩ := ASZB0ASAut K g hg
  have hσθ' : σ θ = θ + 1 := hσθ
  -- the five conjugate linear factors
  let χ : ZMod 5 → L := fun i => algebraMap K L (ZMod.castHom (dvd_refl 5) K i)
  let G : ZMod 5 → MvPolynomial (Fin 2) L := fun i =>
    C (algebraMap K L g) * X (0 : Fin 2)
      + C (2 * algebraMap K L g * (θ + χ i)) * X (1 : Fin 2)
      + C (4 * ((θ + χ i) ^ 3 - (θ + χ i)))
  have hgL : algebraMap K L g ≠ 0 := by
    intro h
    rw [Algebra.algebraMap_eq_smul_one] at h
    rcases smul_eq_zero.mp h with h' | h'
    · exact hg0 h'
    · exact one_ne_zero h'
  have hirr : ∀ i : ZMod 5, Irreducible (G i) := by
    intro i
    exact ASZB0LinearIrred L (algebraMap K L g) (2 * algebraMap K L g * (θ + χ i))
      (4 * ((θ + χ i) ^ 3 - (θ + χ i))) (Or.inl hgL)
  have hne : ∀ i j : ZMod 5, i ≠ j → ¬ Associated (G i) (G j) :=
    fun i j hij => asz_hne_data K L g hg0 θ i j hij
  have hσχ : ∀ i : ZMod 5, σ (χ i) = χ i := by
    intro i
    exact σ.commutes (ZMod.castHom (dvd_refl 5) K i)
  have hχsucc : ∀ i : ZMod 5, χ (i + 1) = χ i + 1 := by
    intro i
    simp only [χ, map_add, map_one]
  have hconj : ∀ i : ZMod 5, MvPolynomial.map (σ : L →+* L) (G i) = G (i + 1) := by
    intro i
    have h1 : σ (θ + χ i) = θ + χ (i + 1) := by
      rw [map_add, hσθ', hσχ i, hχsucc i]
      first | refl_ring1 | ring
    have e1 : σ (algebraMap K L g) = algebraMap K L g := σ.commutes g
    have e2 : σ (2 * algebraMap K L g * (θ + χ i)) = 2 * algebraMap K L g * (θ + χ (i + 1)) := by
      simp only [map_mul, map_ofNat, e1, h1]
    have e3 : σ (4 * ((θ + χ i) ^ 3 - (θ + χ i)))
        = 4 * ((θ + χ (i + 1)) ^ 3 - (θ + χ (i + 1))) := by
      simp only [map_mul, map_sub, map_pow, map_ofNat, h1]
    have key : ∀ x y z : L, MvPolynomial.map (σ : L →+* L)
        (C x * X (0 : Fin 2) + C y * X (1 : Fin 2) + C z)
        = C (σ x) * X (0 : Fin 2) + C (σ y) * X (1 : Fin 2) + C (σ z) := by
      intro x y z
      simp only [map_add, map_mul, MvPolynomial.map_C, MvPolynomial.map_X]
      rfl
    show MvPolynomial.map (σ : L →+* L)
        (C (algebraMap K L g) * X (0 : Fin 2) + C (2 * algebraMap K L g * (θ + χ i)) * X (1 : Fin 2)
          + C (4 * ((θ + χ i) ^ 3 - (θ + χ i))))
        = C (algebraMap K L g) * X (0 : Fin 2) + C (2 * algebraMap K L g * (θ + χ (i + 1))) * X (1 : Fin 2)
          + C (4 * ((θ + χ (i + 1)) ^ 3 - (θ + χ (i + 1))))
    rw [key, e1, e2, e3]
  have hfac : MvPolynomial.map (algebraMap K L) (ASZElim.P 1 0 g)
      = MvPolynomial.C ((algebraMap K L g) ^ 3)⁻¹ * ∏ i : ZMod 5, G i := by
    have h := ASZB0FacL K L g θ hθ
    have hne0 : (algebraMap K L g) ^ 3 ≠ 0 := pow_ne_zero 3 hgL
    rw [h, ← mul_assoc, ← MvPolynomial.C_mul, inv_mul_cancel₀ hne0, MvPolynomial.C_1, one_mul]
  have hP1 : Irreducible (ASZElim.P 1 0 g) :=
    ASZB0SigmaIrr K L σ (ASZElim.P 1 0 g) ((algebraMap K L g) ^ 3)⁻¹
      (isUnit_iff_ne_zero.mpr (inv_ne_zero (pow_ne_zero 3 hgL))) G hirr hconj hfac hne
  -- transport along the (a,b)-homogeneity and the unit C (a^5)
  have hhom := ASZB0Homog K a g
  rw [hhom]
  have hassoc : Associated (MvPolynomial.C (a ^ 5) * ASZElim.P 1 0 g) (ASZElim.P 1 0 g) := by
    have h1 : Associated (MvPolynomial.C (a ^ 5) : MvPolynomial (Fin 2) K) 1 :=
      associated_one_of_mul_eq_one (MvPolynomial.C ((a ^ 5)⁻¹))
        (by rw [← MvPolynomial.C_mul, mul_inv_cancel₀ (pow_ne_zero 5 ha), MvPolynomial.C_1])
    simpa using Associated.mul_right h1 (ASZElim.P 1 0 g)
  exact (Associated.irreducible_iff hassoc).mpr hP1

end Work.MotAS
