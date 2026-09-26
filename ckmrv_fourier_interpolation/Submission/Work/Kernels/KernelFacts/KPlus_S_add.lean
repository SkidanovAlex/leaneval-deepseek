/-
# `S`-invariance of the coefficients of the kernel `K_+^{(d)}`

CKMRV (Cohn--Kumar--Miller--Radchenko--Viazovska, Ann. of Math. 196 (2022), Theorem 4.9)
define the kernel `K_+^{(d)}(τ,z) = φ⃗(τ)ᵗ · Υ_+^{(d)}(τ,z) · φ̃⃗(z)` for `d = 8, 24`, and
`K_+^{(d)}` is the element of `Ann_{d/2}(𝓘₊, 𝒫)` (as a function of `τ`), i.e. it is annihilated
by the right ideal `𝓘₊ = (S+I)R + (T-I)²R` of `R = ℂ[SL(2,ℤ)]` at weight `d/2`.

This file proves the `S + I` half of that statement, in the form recorded by
`Work.Kernels.Sop`:

  `Sop (d/2) (fun τ ↦ K_+^{(d)}(τ,z)) = 0`,  i.e.  `(K_+^{(d)}(·,z) ∣[d/2] S) = - K_+^{(d)}(·,z)`.

The proof is a direct computation.  Its ingredients are

* the modularity of `f_k` of the list `f_{-2} = E₁₀/Δ, f_0 = 1, f_2 = E₁₄/Δ, f_4 = E₄, …`
  (each `f_k` is modular of weight `k`), which gives `f_k(S•τ) = τ^k f_k(τ)`;
* the `S`-invariance of the modular `j`-invariant, hence of every rational expression in
  `j(τ)` (this is what the entries of `Υ_+^{(d)}` are, up to the diagonal factors `f_k`);
* the transformation laws `φ_j(S•τ) = -τ^{w_j} φ_j(τ)` for the basis `(φ_{-2}, φ_0, φ_2)`
  of Proposition 4.2, proved in `Work.Kernels.PhiAnnihilation`.

The upshot is `Υ_+^{(d)}(S•τ,z) = diag(τ^{d/2+2-2i}) · Υ_+^{(d)}(τ,z)` and
`φ_j(S•τ) = -τ^{-2+2j} φ_j(τ)`; since `(d/2+2-2i) + (-2+2i) = d/2` for every `i`, the two
exponents combine to `τ^{d/2}` with the overall minus sign, giving
`K_+^{(d)}(S•τ,z) = -τ^{d/2} K_+^{(d)}(τ,z)`.

## Main result

* `Work.Kernels.KernelFacts.KPlus_S_add` : `Sop (d/2) (K_+^{(d)}(·,z)) = 0` for `d = 8, 24`.
-/
import Mathlib
import Submission.Work.Kernels.KernelEquations
import Submission.Work.Kernels.PhiAnnihilation

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Kernels.KernelFacts

open Work.Kernels

/-! ## Elementary consequences of the slash definition -/

/-- A function which is `S`-invariant of weight `k` satisfies `F(S•τ) = τ^k F(τ)`. -/
lemma smul_of_slash_inv {k : ℤ} {F : ℍ → ℂ}
    (hF : SlashAction.map k ModularGroup.S F = F) (τ : ℍ) :
    F (ModularGroup.S • τ) = (τ : ℂ) ^ k * F τ := by
  have h := congr_fun hF τ
  rw [slash_S_apply] at h
  have hτ : (τ : ℂ) ≠ 0 := fun hh => τ.im_ne_zero (by rw [← coe_im τ, hh]; simp)
  have h2 : F (ModularGroup.S • τ) = F τ * (τ : ℂ) ^ k := by
    calc F (ModularGroup.S • τ) = F (ModularGroup.S • τ) * 1 := by rw [mul_one]
      _ = F (ModularGroup.S • τ) * ((τ:ℂ)^(-k) * (τ:ℂ)^k) := by
            rw [← zpow_add₀ hτ, neg_add_cancel, zpow_zero]
      _ = (F (ModularGroup.S • τ) * (τ:ℂ)^(-k)) * (τ:ℂ)^k := by rw [mul_assoc]
      _ = F τ * (τ:ℂ)^k := by rw [h]
  rw [h2, mul_comm]

/-- The product of two `S`-invariant functions is `S`-invariant in the sum of the weights. -/
lemma slash_inv_mul {k1 k2 : ℤ} {f g : ℍ → ℂ}
    (hf : SlashAction.map k1 ModularGroup.S f = f)
    (hg : SlashAction.map k2 ModularGroup.S g = g) :
    SlashAction.map (k1 + k2) ModularGroup.S (f * g) = f * g := by
  rw [ModularForm.mul_slash_SL2, hf, hg]

/-- The quotient of two `S`-invariant functions is `S`-invariant in the difference of the
weights. -/
lemma slash_inv_div {k1 k2 : ℤ} {f g : ℍ → ℂ}
    (hf : SlashAction.map k1 ModularGroup.S f = f)
    (hg : SlashAction.map k2 ModularGroup.S g = g) :
    SlashAction.map (k1 - k2) ModularGroup.S (f / g) = f / g := by
  rw [ModularForm.div_slash_SL2, hf, hg]

/-! ## The modularity of the functions `f_k` of CKMRV Section 4.4 -/

lemma one_slash_S : SlashAction.map (0:ℤ) ModularGroup.S (1 : ℍ → ℂ) = 1 :=
  ModularForm.is_invariant_one ModularGroup.S

lemma E4Fun_S_slash : SlashAction.map (4:ℤ) ModularGroup.S E4Fun = E4Fun :=
  SlashInvariantForm.slash_action_eqn (ModularForm.E₄)
    (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S)
    (MonoidHom.mem_range.mpr ⟨ModularGroup.S, rfl⟩)

lemma E6Fun_S_slash : SlashAction.map (6:ℤ) ModularGroup.S E6Fun = E6Fun :=
  SlashInvariantForm.slash_action_eqn (ModularForm.E₆)
    (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S)
    (MonoidHom.mem_range.mpr ⟨ModularGroup.S, rfl⟩)

lemma DeltaFun_S_slash : SlashAction.map (12:ℤ) ModularGroup.S DeltaFun = DeltaFun :=
  SlashInvariantForm.slash_action_eqn (CuspForm.discriminant)
    (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S)
    (MonoidHom.mem_range.mpr ⟨ModularGroup.S, rfl⟩)

lemma E8Fun_S_slash : SlashAction.map (8:ℤ) ModularGroup.S E8Fun = E8Fun := by
  have h : E8Fun = E4Fun * E4Fun := by funext τ; simp [E8Fun, pow_two]
  rw [h]
  exact slash_inv_mul (k1 := 4) (k2 := 4) E4Fun_S_slash E4Fun_S_slash

lemma E10Fun_S_slash : SlashAction.map (10:ℤ) ModularGroup.S E10Fun = E10Fun := by
  have h : E10Fun = E4Fun * E6Fun := by funext τ; simp [E10Fun]
  rw [h]
  exact slash_inv_mul (k1 := 4) (k2 := 6) E4Fun_S_slash E6Fun_S_slash

lemma E14Fun_S_slash : SlashAction.map (14:ℤ) ModularGroup.S E14Fun = E14Fun := by
  have h : E14Fun = E8Fun * E6Fun := by funext τ; simp [E14Fun, E8Fun, pow_two]
  rw [h]
  exact slash_inv_mul (k1 := 8) (k2 := 6) E8Fun_S_slash E6Fun_S_slash

lemma E10DivDelta_S_slash :
    SlashAction.map (-2:ℤ) ModularGroup.S (E10Fun / DeltaFun) = E10Fun / DeltaFun :=
  slash_inv_div (k1 := 10) (k2 := 12) E10Fun_S_slash DeltaFun_S_slash

lemma E14DivDelta_S_slash :
    SlashAction.map (2:ℤ) ModularGroup.S (E14Fun / DeltaFun) = E14Fun / DeltaFun :=
  slash_inv_div (k1 := 14) (k2 := 12) E14Fun_S_slash DeltaFun_S_slash

lemma fk_neg_two : fk (-2) = E10Fun / DeltaFun := by funext τ; simp [fk]
lemma fk_zero : fk (0:ℤ) = (1 : ℍ → ℂ) := by funext τ; simp [fk]
lemma fk_two : fk (2:ℤ) = E14Fun / DeltaFun := by funext τ; simp [fk]
lemma fk_four : fk (4:ℤ) = E4Fun := by funext τ; simp [fk]
lemma fk_six : fk (6:ℤ) = E6Fun := by funext τ; simp [fk]
lemma fk_eight : fk (8:ℤ) = E8Fun := by funext τ; simp [fk]
lemma fk_ten : fk (10:ℤ) = E10Fun := by funext τ; simp [fk]
lemma fk_twelve : fk (12:ℤ) = DeltaFun := by funext τ; simp [fk]
lemma fk_fourteen : fk (14:ℤ) = E14Fun := by funext τ; simp [fk]

/-- Each of the functions `f_k`, `k ∈ {-2,0,2,4,6,8,10,12,14}`, is modular of weight `k`,
hence `S`-invariant of weight `k`. -/
lemma fk_S_slash (k : ℤ)
    (hk : k = -2 ∨ k = 0 ∨ k = 2 ∨ k = 4 ∨ k = 6 ∨ k = 8 ∨ k = 10 ∨ k = 12 ∨ k = 14) :
    SlashAction.map k ModularGroup.S (fk k) = fk k := by
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [fk_neg_two]; exact E10DivDelta_S_slash
  · rw [fk_zero]; exact one_slash_S
  · rw [fk_two]; exact E14DivDelta_S_slash
  · rw [fk_four]; exact E4Fun_S_slash
  · rw [fk_six]; exact E6Fun_S_slash
  · rw [fk_eight]; exact E8Fun_S_slash
  · rw [fk_ten]; exact E10Fun_S_slash
  · rw [fk_twelve]; exact DeltaFun_S_slash
  · rw [fk_fourteen]; exact E14Fun_S_slash

/-- Pointwise form: `f_k(S•τ) = τ^k f_k(τ)`. -/
lemma fk_S_smul (k : ℤ)
    (hk : k = -2 ∨ k = 0 ∨ k = 2 ∨ k = 4 ∨ k = 6 ∨ k = 8 ∨ k = 10 ∨ k = 12 ∨ k = 14)
    (τ : ℍ) : fk k (ModularGroup.S • τ) = (τ : ℂ) ^ k * fk k τ :=
  smul_of_slash_inv (fk_S_slash k hk) τ

/-! ## The `j`-invariant is `S`-invariant -/

lemma jInvariantFun_S_slash :
    SlashAction.map (0:ℤ) ModularGroup.S jInvariantFun = jInvariantFun := by
  have h : jInvariantFun = (E4Fun * E4Fun * E4Fun) / DeltaFun := by
    funext τ; simp only [jInvariantFun, Pi.div_apply, Pi.mul_apply]; ring
  rw [h]
  have h8 : SlashAction.map (8:ℤ) ModularGroup.S (E4Fun * E4Fun) = E4Fun * E4Fun := by
    simpa using slash_inv_mul (k1 := 4) (k2 := 4) E4Fun_S_slash E4Fun_S_slash
  have h12 : SlashAction.map (12:ℤ) ModularGroup.S (E4Fun * E4Fun * E4Fun) =
      E4Fun * E4Fun * E4Fun := by
    simpa using slash_inv_mul (k1 := 8) (k2 := 4) h8 E4Fun_S_slash
  simpa using slash_inv_div (k1 := 12) (k2 := 12) h12 DeltaFun_S_slash

lemma jInvariantFun_S_smul (τ : ℍ) :
    jInvariantFun (ModularGroup.S • τ) = jInvariantFun τ := by
  have h := smul_of_slash_inv jInvariantFun_S_slash τ
  simpa using h

/-! ## The transformation of `PiMat v` under `τ ↦ S•τ` -/

/-- The diagonal matrices `PiMat v` transform under `S` by the diagonal matrix of the
weights `v i`. -/
lemma PiMat_S_smul (v : Fin 3 → ℤ)
    (hv : ∀ i, v i = -2 ∨ v i = 0 ∨ v i = 2 ∨ v i = 4 ∨ v i = 6 ∨ v i = 8 ∨ v i = 10 ∨
      v i = 12 ∨ v i = 14)
    (τ : ℍ) :
    PiMat v (ModularGroup.S • τ) =
      Matrix.diagonal (fun i : Fin 3 => (τ : ℂ) ^ (v i)) * PiMat v τ := by
  simp only [PiMat]
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact fk_S_smul (v i) (hv i) τ

/-! ## The transformation of `Υ_+` under `τ ↦ S•τ` -/

/-- The coefficient matrix `Υ_+^{(8)}` transforms under `S` by the diagonal matrix of the
weights `6, 4, 2 = d/2 + 2 - 2i`. -/
lemma UpsilonPlus_eight_S (z τ : ℍ) :
    UpsilonPlus 8 (ModularGroup.S • τ) z =
      Matrix.diagonal (fun i : Fin 3 => (τ : ℂ) ^ ((![6,4,2] : Fin 3 → ℤ) i)) *
        UpsilonPlus 8 τ z := by
  have hJ : jInvariantFun (ModularGroup.S • τ) = jInvariantFun τ := jInvariantFun_S_smul τ
  have hPi := PiMat_S_smul (![6,4,2] : Fin 3 → ℤ) (by intro i; fin_cases i <;> simp) τ
  simp only [UpsilonPlus, reduceIte]
  rw [hJ, hPi]
  simp only [Matrix.mul_assoc]
  rw [Matrix.mul_smul]

/-- The coefficient matrix `Υ_+^{(24)}` transforms under `S` by the diagonal matrix of the
weights `14, 12, 10 = d/2 + 2 - 2i`. -/
lemma UpsilonPlus_twentyfour_S (z τ : ℍ) :
    UpsilonPlus 24 (ModularGroup.S • τ) z =
      Matrix.diagonal (fun i : Fin 3 => (τ : ℂ) ^ ((![14,12,10] : Fin 3 → ℤ) i)) *
        UpsilonPlus 24 τ z := by
  have hJ : jInvariantFun (ModularGroup.S • τ) = jInvariantFun τ := jInvariantFun_S_smul τ
  have hPi := PiMat_S_smul (![14,12,10] : Fin 3 → ℤ) (by intro i; fin_cases i <;> simp) τ
  simp only [UpsilonPlus, reduceIte]
  simp only [if_neg (show ¬ ((24:ℕ) = 8) by decide)]
  rw [hJ, hPi]
  simp only [Matrix.mul_assoc]
  rw [Matrix.mul_smul]

/-! ## The transformation of `phiVec` under `τ ↦ S•τ` -/

/-- The basis `(φ_{-2}, φ_0, φ_2)` of Proposition 4.2 satisfies
`φ_j(S•τ) = -τ^{-2+2j} φ_j(τ)`. -/
lemma phiVec_S_smul (τ : ℍ) (i : Fin 3) :
    phiVec (ModularGroup.S • τ) i =
      -((τ : ℂ) ^ ((![(-2:ℤ),0,2] : Fin 3 → ℤ) i)) * phiVec τ i := by
  have hτ : (τ : ℂ) ≠ 0 := fun hh => τ.im_ne_zero (by rw [← coe_im τ, hh]; simp)
  fin_cases i
  · show phiNeg2 (ModularGroup.S • τ) = -((τ : ℂ) ^ (-2:ℤ)) * (τ : ℂ)
    have h : (τ : ℂ) ^ (-2:ℤ) * (τ : ℂ) = (τ : ℂ)⁻¹ := by
      calc (τ : ℂ) ^ (-2:ℤ) * (τ : ℂ)
          = (τ : ℂ) ^ (-2:ℤ) * (τ : ℂ) ^ (1:ℤ) := by rw [zpow_one]
        _ = (τ : ℂ) ^ ((-2:ℤ) + 1) := by rw [zpow_add₀ hτ]
        _ = (τ : ℂ) ^ (-1:ℤ) := by congr 1
        _ = (τ : ℂ)⁻¹ := zpow_neg_one (τ : ℂ)
    rw [phiNeg2_S_smul, neg_mul, h]
  · show phi0 (ModularGroup.S • τ) = -((τ : ℂ) ^ (0:ℤ)) * phi0 τ
    rw [phi0_S_smul, zpow_zero, neg_one_mul]
  · show phi2 (ModularGroup.S • τ) = -((τ : ℂ) ^ (2:ℤ)) * phi2 τ
    rw [phi2_S_smul, mul_neg, neg_mul]
    norm_num

/-! ## The transformation of `K_+` as a function of `τ` -/

/-- `K_+^{(d)}(S•τ,z) = -τ^{d/2} K_+^{(d)}(τ,z)` for `d = 8` and `d = 24`. -/
lemma KPlus_S_smul (d : ℕ) (hd : d = 8 ∨ d = 24) (z τ : ℍ) :
    KPlus d (ModularGroup.S • τ) z = -((τ : ℂ) ^ ((d : ℤ) / 2)) * KPlus d τ z := by
  have hτ : (τ : ℂ) ≠ 0 := fun hh => τ.im_ne_zero (by rw [← coe_im τ, hh]; simp)
  rcases hd with rfl | rfl
  · show KPlus 8 (ModularGroup.S • τ) z = -((τ : ℂ) ^ (4:ℤ)) * KPlus 8 τ z
    simp only [KPlus]
    have hU : ∀ (i j : Fin 3), UpsilonPlus 8 (ModularGroup.S • τ) z i j =
        (τ : ℂ) ^ ((![6,4,2] : Fin 3 → ℤ) i) * UpsilonPlus 8 τ z i j := by
      intro i j
      rw [UpsilonPlus_eight_S, Matrix.diagonal_mul]
    have hsum : ∀ i : Fin 3,
        (∑ j : Fin 3, phiVec (ModularGroup.S • τ) i *
            UpsilonPlus 8 (ModularGroup.S • τ) z i j * phitVec z j)
          = -((τ : ℂ) ^ (4:ℤ)) *
              (∑ j : Fin 3, phiVec τ i * UpsilonPlus 8 τ z i j * phitVec z j) := by
      intro i
      have hφ := phiVec_S_smul τ i
      have hpow : (τ : ℂ) ^ ((![(-2:ℤ),0,2] : Fin 3 → ℤ) i) *
            (τ : ℂ) ^ ((![6,4,2] : Fin 3 → ℤ) i) = (τ : ℂ) ^ (4:ℤ) := by
        rw [← zpow_add₀ hτ]
        congr 1
        fin_cases i <;> norm_num
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hU i j, hφ, ← hpow]
      ring
    rw [Finset.sum_congr rfl (fun i _ => hsum i)]
    rw [Finset.mul_sum]
  · show KPlus 24 (ModularGroup.S • τ) z = -((τ : ℂ) ^ (12:ℤ)) * KPlus 24 τ z
    simp only [KPlus]
    have hU : ∀ (i j : Fin 3), UpsilonPlus 24 (ModularGroup.S • τ) z i j =
        (τ : ℂ) ^ ((![14,12,10] : Fin 3 → ℤ) i) * UpsilonPlus 24 τ z i j := by
      intro i j
      rw [UpsilonPlus_twentyfour_S, Matrix.diagonal_mul]
    have hsum : ∀ i : Fin 3,
        (∑ j : Fin 3, phiVec (ModularGroup.S • τ) i *
            UpsilonPlus 24 (ModularGroup.S • τ) z i j * phitVec z j)
          = -((τ : ℂ) ^ (12:ℤ)) *
              (∑ j : Fin 3, phiVec τ i * UpsilonPlus 24 τ z i j * phitVec z j) := by
      intro i
      have hφ := phiVec_S_smul τ i
      have hpow : (τ : ℂ) ^ ((![(-2:ℤ),0,2] : Fin 3 → ℤ) i) *
            (τ : ℂ) ^ ((![14,12,10] : Fin 3 → ℤ) i) = (τ : ℂ) ^ (12:ℤ) := by
        rw [← zpow_add₀ hτ]
        congr 1
        fin_cases i <;> norm_num
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hU i j, hφ, ← hpow]
      ring
    rw [Finset.sum_congr rfl (fun i _ => hsum i)]
    rw [Finset.mul_sum]

/-! ## The main theorem -/

theorem KPlus_S_add (d : ℕ) (hd : d = 8 ∨ d = 24) (z : UpperHalfPlane) :
    Work.Kernels.Sop ((d : ℤ) / 2) (fun τ : UpperHalfPlane => Work.Kernels.KPlus d τ z) = 0 := by
  ext τ
  simp only [Sop, Pi.zero_apply]
  rw [slash_S_apply, KPlus_S_smul d hd z τ]
  have hτ : (τ : ℂ) ≠ 0 := fun hh => τ.im_ne_zero (by rw [← coe_im τ, hh]; simp)
  have h1 : (τ : ℂ) ^ ((d : ℤ) / 2) * (τ : ℂ) ^ (-((d : ℤ) / 2)) = 1 := by
    rw [← zpow_add₀ hτ, add_neg_cancel, zpow_zero]
  have h2 : (-((τ : ℂ) ^ ((d : ℤ) / 2)) * KPlus d τ z) * (τ : ℂ) ^ (-((d : ℤ) / 2)) =
      -(KPlus d τ z) := by
    rw [show (-((τ : ℂ) ^ ((d : ℤ) / 2)) * KPlus d τ z) * (τ : ℂ) ^ (-((d : ℤ) / 2)) =
        (-((τ : ℂ) ^ ((d : ℤ) / 2)) * (τ : ℂ) ^ (-((d : ℤ) / 2))) * KPlus d τ z by ring,
      show -((τ : ℂ) ^ ((d : ℤ) / 2)) * (τ : ℂ) ^ (-((d : ℤ) / 2)) = -1 by
        rw [neg_mul, h1],
      neg_one_mul]
  rw [h2, neg_add_cancel]

end Work.Kernels.KernelFacts
