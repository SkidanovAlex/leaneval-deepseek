import Mathlib
import Submission.Work.Mostow.geodDeps
import Submission.Work.Mostow.resStd_hom_discrete
import Submission.Work.Mostow.normConjIsom
import Submission.Work.Mostow.orthSmallCommute
import Submission.Work.Mostow.finite_nearStab
import Submission.Work.Mostow.Margulis.ComplexifyOrth
import Submission.Work.Mostow.axisGenFiniteAbelian

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

noncomputable section

/-! ## The complexification of a finite-dimensional real inner product space

`Margulis.ComplexifyOrth` models the complexification of a real inner product space `W` as `W × W`
with the `ℂ`-module structure `(a + bi) • (x, y) = (a • x - b • y, b • x + a • y)` and the action of
`W ≃ₗᵢ[ℝ] W` through `Margulis.cActHom`.  Two bookkeeping facts are needed below: the `ℂ`-dimension
of the complexification is the `ℝ`-dimension of `W`, and `cActHom` is injective. -/

/-- The complexification `W × W` has `ℂ`-dimension `finrank ℝ W`. -/
theorem finrank_prod_complex {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] :
    Module.finrank ℂ (W × W) = Module.finrank ℝ W := by
  have h1 : Module.finrank ℝ ℂ * Module.finrank ℂ (W × W) = Module.finrank ℝ (W × W) :=
    Module.finrank_mul_finrank ℝ ℂ (W × W)
  have h2 : Module.finrank ℝ (W × W) = Module.finrank ℝ W + Module.finrank ℝ W :=
    Module.finrank_prod
  have h3 : (2 : ℕ) * Module.finrank ℂ (W × W) = (2 : ℕ) * Module.finrank ℝ W := by
    rw [Complex.finrank_real_complex] at h1
    rw [h1, h2]
    ring
  exact Nat.mul_left_cancel (by norm_num : 0 < 2) h3

/-- The action of the orthogonal group on the complexification is faithful. -/
theorem cActHom_injective' {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] :
    Function.Injective (Margulis.cActHom (V := W)) := by
  intro p q hpq
  ext x
  have h := congrArg (fun (e : (W × W) ≃ₗ[ℂ] (W × W)) => (e (x, 0) : W × W)) hpq
  have h2 : (p x, p 0) = (q x, q 0) := h
  exact (Prod.ext_iff.mp h2).1

/-! ## The Fourier-idempotent argument

`ftfourierMain` is the linear-algebra core: if a finite abelian group `G` acts on a finite-dimensional
complex vector space `V` through an injective representation `ρ`, and `R ∈ GL(V)` normalises the
image (`R * ρ g * R⁻¹ = ρ (φ g)`), then `R ^ (finrank ℂ V)!` centralises `ρ G`.  The proof uses the
Fourier projectors `E_ψ = |G|⁻¹ ∑_g χ_ψ(g)⁻¹ ρ(g)`, which are orthogonal idempotents summing to `1`;
there are at most `finrank ℂ V` of them with non-zero image, and conjugation by `R` permutes them.

-/

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]

/-- Character values `χ_ψ(g) = ψ g`. -/
private def ftchi (ψ : AddChar (Additive G) ℂ) (g : G) : ℂ := ψ (Additive.ofMul g)

private lemma ftchi_mul (ψ : AddChar (Additive G) ℂ) (a b : G) :
    ftchi ψ (a * b) = ftchi ψ a * ftchi ψ b := by
  simp [ftchi, AddChar.map_add_eq_mul]

private lemma ftchi_inv (ψ : AddChar (Additive G) ℂ) (a : G) :
    ftchi ψ a⁻¹ = (ftchi ψ a)⁻¹ := by
  simp [ftchi, AddChar.map_neg_eq_inv]

private lemma ftchi_one (ψ : AddChar (Additive G) ℂ) : ftchi ψ 1 = 1 := by
  simp [ftchi]

private lemma ftchi_ne_zero (ψ : AddChar (Additive G) ℂ) (a : G) : ftchi ψ a ≠ 0 := by
  intro h0
  have h := ftchi_mul ψ a a⁻¹
  rw [mul_inv_cancel, ftchi_one, h0, zero_mul] at h
  exact one_ne_zero h

/-- The Fourier projector `E_ψ = |G|⁻¹ ∑_g χ_ψ(g)⁻¹ ρ(g)`. -/
private noncomputable def ftproj (ρ : G →* (V ≃ₗ[ℂ] V)) (ψ : AddChar (Additive G) ℂ) : V →ₗ[ℂ] V :=
  ((Fintype.card G : ℂ))⁻¹ • ∑ g : G, (ftchi ψ g)⁻¹ • (ρ g : V →ₗ[ℂ] V)

private lemma ftcoe_map_mul (ρ : G →* (V ≃ₗ[ℂ] V)) (a b : G) :
    (ρ a : V →ₗ[ℂ] V) * (ρ b : V →ₗ[ℂ] V) = (ρ (a * b) : V →ₗ[ℂ] V) := by
  rw [map_mul]
  ext x
  simp [LinearEquiv.mul_apply]

private lemma ftsum_reindex_inv (F : G → V →ₗ[ℂ] V) (b : G) :
    (∑ a : G, F a) = ∑ a : G, F (a * b⁻¹) :=
  (Equiv.sum_comp (Equiv.mulRight b⁻¹) F).symm

/-- **Key relation**: `E_ψ * ρ(b) = χ_ψ(b) • E_ψ`. -/
private lemma ftproj_mul (ρ : G →* (V ≃ₗ[ℂ] V)) (ψ : AddChar (Additive G) ℂ) (b : G) :
    ftproj ρ ψ * (ρ b : V →ₗ[ℂ] V) = ftchi ψ b • ftproj ρ ψ := by
  classical
  have hmain : (∑ a : G, ((ftchi ψ a)⁻¹ • (ρ a : V →ₗ[ℂ] V)) * (ρ b : V →ₗ[ℂ] V))
      = ftchi ψ b • ∑ a : G, (ftchi ψ a)⁻¹ • (ρ a : V →ₗ[ℂ] V) := by
    calc (∑ a : G, ((ftchi ψ a)⁻¹ • (ρ a : V →ₗ[ℂ] V)) * (ρ b : V →ₗ[ℂ] V))
        = ∑ a : G, (ftchi ψ a)⁻¹ • (ρ (a * b) : V →ₗ[ℂ] V) :=
          Finset.sum_congr rfl (fun a _ => by rw [smul_mul_assoc, ftcoe_map_mul])
      _ = ∑ a : G, (ftchi ψ (a * b⁻¹))⁻¹ • (ρ a : V →ₗ[ℂ] V) := by
          rw [ftsum_reindex_inv (fun a : G => (ftchi ψ a)⁻¹ • (ρ (a * b) : V →ₗ[ℂ] V)) b]
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [mul_assoc, inv_mul_cancel, mul_one]
      _ = ∑ a : G, ftchi ψ b • ((ftchi ψ a)⁻¹ • (ρ a : V →ₗ[ℂ] V)) :=
          Finset.sum_congr rfl (fun a _ => by rw [ftchi_mul, ftchi_inv, mul_inv_rev, inv_inv, smul_smul])
      _ = ftchi ψ b • ∑ a : G, (ftchi ψ a)⁻¹ • (ρ a : V →ₗ[ℂ] V) := by
          rw [Finset.smul_sum]
  unfold ftproj
  rw [smul_mul_assoc, Finset.sum_mul, hmain, smul_comm]

private lemma ftdouble_sum (ρ : G →* (V ≃ₗ[ℂ] V)) (f : AddChar (Additive G) ℂ → G → ℂ) :
    (∑ ψ : AddChar (Additive G) ℂ, ∑ a : G, f ψ a • (ρ a : V →ₗ[ℂ] V))
      = ∑ a : G, (∑ ψ : AddChar (Additive G) ℂ, f ψ a) • (ρ a : V →ₗ[ℂ] V) := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun a _ => (Finset.sum_smul).symm)

private def ftofMulEquiv : G ≃ Additive G where
  toFun := Additive.ofMul
  invFun := Additive.toMul
  left_inv _ := rfl
  right_inv _ := rfl

private lemma ftcard_additive : Fintype.card (Additive G) = Fintype.card G :=
  Fintype.card_congr ftofMulEquiv

private lemma ftinv_smul_smul_self (x : V →ₗ[ℂ] V) :
    ((Fintype.card G : ℂ))⁻¹ • ((Fintype.card G : ℂ) • x) = x := by
  rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ (by simp : (Fintype.card G : ℂ) ≠ 0), one_smul]

private lemma ftsum_psi_inv (a : G) :
    (∑ ψ : AddChar (Additive G) ℂ, (ftchi ψ a)⁻¹) = if a = 1 then (Fintype.card G : ℂ) else 0 := by
  classical
  have h1 : ∀ ψ : AddChar (Additive G) ℂ, (ftchi ψ a)⁻¹ = ψ (Additive.ofMul a⁻¹) := by
    intro ψ
    rw [← ftchi_inv]
    rfl
  simp only [h1]
  rw [AddChar.sum_apply_eq_ite, ftcard_additive]
  by_cases ha : a = 1
  · rw [if_pos ha, if_pos (show (Additive.ofMul a⁻¹ : Additive G) = 0 from by rw [ha]; simp)]
  · rw [if_neg ha, if_neg]
    intro h
    apply ha
    have h2 := congrArg Additive.toMul h
    simpa using h2

private lemma ftsum_chi_ratio (a b : G) :
    (∑ ψ : AddChar (Additive G) ℂ, ftchi ψ a * (ftchi ψ b)⁻¹)
      = if a = b then (Fintype.card G : ℂ) else 0 := by
  classical
  have h1 : ∀ ψ : AddChar (Additive G) ℂ, ftchi ψ a * (ftchi ψ b)⁻¹ = ψ (Additive.ofMul (a * b⁻¹)) := by
    intro ψ
    rw [← ftchi_inv, ← ftchi_mul]
    rfl
  simp only [h1]
  rw [AddChar.sum_apply_eq_ite, ftcard_additive]
  by_cases hab : a = b
  · rw [if_pos hab, if_pos (show (Additive.ofMul (a * b⁻¹) : Additive G) = 0 from by
      rw [hab, mul_inv_cancel]; simp)]
  · rw [if_neg hab, if_neg]
    intro h
    apply hab
    have h2 : a * b⁻¹ = 1 := by
      have h3 := congrArg Additive.toMul h
      simpa using h3
    exact mul_inv_eq_one.mp h2

private lemma ftsum_group_chi (ψ ψ' : AddChar (Additive G) ℂ) :
    (∑ b : G, (ftchi ψ' b)⁻¹ * ftchi ψ b) = if ψ = ψ' then (Fintype.card G : ℂ) else 0 := by
  classical
  have h1 : ∀ b : G, (ftchi ψ' b)⁻¹ * ftchi ψ b = (ψ - ψ') (Additive.ofMul b) := by
    intro b
    simp only [ftchi]
    rw [AddChar.sub_apply, AddChar.map_neg_eq_inv]
    ring
  simp only [h1]
  have hconv : (∑ b : G, (ψ - ψ') (Additive.ofMul b)) = ∑ x : Additive G, (ψ - ψ') x :=
    Equiv.sum_comp ftofMulEquiv (fun x : Additive G => (ψ - ψ') x)
  rw [hconv, AddChar.sum_eq_ite, ftcard_additive]
  by_cases h : ψ = ψ'
  · rw [if_pos h, if_pos (show ψ - ψ' = 0 from by rw [h, sub_self])]
  · rw [if_neg h, if_neg (fun hc => h (sub_eq_zero.mp hc))]

private lemma fthproj (ρ : G →* (V ≃ₗ[ℂ] V)) (ψ : AddChar (Additive G) ℂ) :
    ftproj ρ ψ = ((Fintype.card G : ℂ))⁻¹ • ∑ g : G, (ftchi ψ g)⁻¹ • (ρ g : V →ₗ[ℂ] V) := rfl

private lemma ftproj_mul_proj (ρ : G →* (V ≃ₗ[ℂ] V)) (ψ ψ' : AddChar (Additive G) ℂ) :
    ftproj ρ ψ * ftproj ρ ψ' = if ψ = ψ' then ftproj ρ ψ else 0 := by
  classical
  calc ftproj ρ ψ * ftproj ρ ψ'
      = ftproj ρ ψ * (((Fintype.card G : ℂ))⁻¹ •
          ∑ b : G, (ftchi ψ' b)⁻¹ • (ρ b : V →ₗ[ℂ] V)) := by rw [fthproj ρ ψ']
    _ = ((Fintype.card G : ℂ))⁻¹ • (ftproj ρ ψ *
          ∑ b : G, (ftchi ψ' b)⁻¹ • (ρ b : V →ₗ[ℂ] V)) := by rw [mul_smul_comm]
    _ = ((Fintype.card G : ℂ))⁻¹ • ∑ b : G,
          ftproj ρ ψ * ((ftchi ψ' b)⁻¹ • (ρ b : V →ₗ[ℂ] V)) := by rw [Finset.mul_sum]
    _ = ((Fintype.card G : ℂ))⁻¹ • ∑ b : G,
          (ftchi ψ' b)⁻¹ • (ftproj ρ ψ * (ρ b : V →ₗ[ℂ] V)) := by
          congr 1
          exact Finset.sum_congr rfl (fun b _ => by rw [mul_smul_comm])
    _ = ((Fintype.card G : ℂ))⁻¹ • ∑ b : G,
          ((ftchi ψ' b)⁻¹ * ftchi ψ b) • ftproj ρ ψ := by
          congr 1
          exact Finset.sum_congr rfl (fun b _ => by rw [ftproj_mul, smul_smul])
    _ = ((Fintype.card G : ℂ))⁻¹ •
          ((∑ b : G, (ftchi ψ' b)⁻¹ * ftchi ψ b) • ftproj ρ ψ) := by
          congr 1
          exact (Finset.sum_smul).symm
    _ = if ψ = ψ' then ftproj ρ ψ else 0 := by
          rw [ftsum_group_chi]
          by_cases h : ψ = ψ'
          · rw [if_pos h, if_pos h]
            exact ftinv_smul_smul_self (ftproj ρ ψ)
          · rw [if_neg h, if_neg h, zero_smul, smul_zero]

private lemma ftsum_proj (ρ : G →* (V ≃ₗ[ℂ] V)) :
    (∑ ψ : AddChar (Additive G) ℂ, ftproj ρ ψ) = 1 := by
  classical
  have hsingle : (∑ a : G, (∑ ψ : AddChar (Additive G) ℂ, (ftchi ψ a)⁻¹) • (ρ a : V →ₗ[ℂ] V))
      = (Fintype.card G : ℂ) • (ρ 1 : V →ₗ[ℂ] V) := by
    rw [Finset.sum_eq_single (1 : G)]
    · rw [ftsum_psi_inv, if_pos rfl]
    · intro b _ hb
      rw [ftsum_psi_inv, if_neg hb, zero_smul]
    · intro h
      exact absurd (Finset.mem_univ (1 : G)) h
  calc (∑ ψ : AddChar (Additive G) ℂ, ftproj ρ ψ)
      = ∑ ψ : AddChar (Additive G) ℂ, ((Fintype.card G : ℂ))⁻¹ •
          ∑ a : G, (ftchi ψ a)⁻¹ • (ρ a : V →ₗ[ℂ] V) :=
        Finset.sum_congr rfl (fun ψ _ => fthproj ρ ψ)
    _ = ((Fintype.card G : ℂ))⁻¹ • ∑ ψ : AddChar (Additive G) ℂ, ∑ a : G,
          (ftchi ψ a)⁻¹ • (ρ a : V →ₗ[ℂ] V) := by rw [Finset.smul_sum]
    _ = ((Fintype.card G : ℂ))⁻¹ • ∑ a : G,
          (∑ ψ : AddChar (Additive G) ℂ, (ftchi ψ a)⁻¹) • (ρ a : V →ₗ[ℂ] V) := by
        rw [ftdouble_sum]
    _ = ((Fintype.card G : ℂ))⁻¹ • ((Fintype.card G : ℂ) • (ρ 1 : V →ₗ[ℂ] V)) := by
        rw [hsingle]
    _ = 1 := by
        rw [show ((ρ 1 : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V) = 1 from by
          rw [map_one]
          ext x
          rfl]
        exact ftinv_smul_smul_self 1

private lemma ftsum_chi_proj (ρ : G →* (V ≃ₗ[ℂ] V)) (g : G) :
    (∑ ψ : AddChar (Additive G) ℂ, ftchi ψ g • ftproj ρ ψ) = (ρ g : V →ₗ[ℂ] V) := by
  classical
  have hsingle : (∑ a : G, (∑ ψ : AddChar (Additive G) ℂ, ftchi ψ g * (ftchi ψ a)⁻¹) •
        (ρ a : V →ₗ[ℂ] V)) = (Fintype.card G : ℂ) • (ρ g : V →ₗ[ℂ] V) := by
    rw [Finset.sum_eq_single g]
    · rw [ftsum_chi_ratio, if_pos rfl]
    · intro b _ hb
      rw [ftsum_chi_ratio, if_neg (Ne.symm hb), zero_smul]
    · intro h
      exact absurd (Finset.mem_univ g) h
  calc (∑ ψ : AddChar (Additive G) ℂ, ftchi ψ g • ftproj ρ ψ)
      = ∑ ψ : AddChar (Additive G) ℂ, ftchi ψ g • (((Fintype.card G : ℂ))⁻¹ •
          ∑ a : G, (ftchi ψ a)⁻¹ • (ρ a : V →ₗ[ℂ] V)) :=
        Finset.sum_congr rfl (fun ψ _ => by rw [fthproj ρ ψ])
    _ = ∑ ψ : AddChar (Additive G) ℂ, ((Fintype.card G : ℂ))⁻¹ •
          (ftchi ψ g • ∑ a : G, (ftchi ψ a)⁻¹ • (ρ a : V →ₗ[ℂ] V)) := by
        exact Finset.sum_congr rfl (fun ψ _ => by rw [smul_comm])
    _ = ((Fintype.card G : ℂ))⁻¹ • ∑ ψ : AddChar (Additive G) ℂ,
          ftchi ψ g • ∑ a : G, (ftchi ψ a)⁻¹ • (ρ a : V →ₗ[ℂ] V) := by rw [Finset.smul_sum]
    _ = ((Fintype.card G : ℂ))⁻¹ • ∑ ψ : AddChar (Additive G) ℂ, ∑ a : G,
          (ftchi ψ g * (ftchi ψ a)⁻¹) • (ρ a : V →ₗ[ℂ] V) := by
        congr 1
        exact Finset.sum_congr rfl (fun ψ _ => by
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl (fun a _ => by rw [smul_smul]))
    _ = ((Fintype.card G : ℂ))⁻¹ • ∑ a : G,
          (∑ ψ : AddChar (Additive G) ℂ, ftchi ψ g * (ftchi ψ a)⁻¹) • (ρ a : V →ₗ[ℂ] V) := by
        rw [ftdouble_sum]
    _ = ((Fintype.card G : ℂ))⁻¹ • ((Fintype.card G : ℂ) • (ρ g : V →ₗ[ℂ] V)) := by
        rw [hsingle]
    _ = (ρ g : V →ₗ[ℂ] V) := ftinv_smul_smul_self (ρ g : V →ₗ[ℂ] V)

/-! ## Conjugation by the normaliser -/

private lemma ftcoe_mul_coe (A B : V ≃ₗ[ℂ] V) :
    (A : V →ₗ[ℂ] V) * (B : V →ₗ[ℂ] V) = ((A * B : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V) := by
  ext x
  simp [LinearEquiv.mul_apply]

private def ftconj (R : V ≃ₗ[ℂ] V) (T : V →ₗ[ℂ] V) : V →ₗ[ℂ] V :=
  (R : V →ₗ[ℂ] V) * T * ((R⁻¹ : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V)

private lemma ftconj_smul (R : V ≃ₗ[ℂ] V) (c : ℂ) (T : V →ₗ[ℂ] V) :
    ftconj R (c • T) = c • ftconj R T := by
  simp only [ftconj, mul_smul_comm, smul_mul_assoc]

private lemma ftconj_sum {ι : Type*} (R : V ≃ₗ[ℂ] V) (s : Finset ι) (T : ι → V →ₗ[ℂ] V) :
    ftconj R (∑ i ∈ s, T i) = ∑ i ∈ s, ftconj R (T i) := by
  rw [ftconj, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun i _ => by rw [ftconj])

private lemma ftconj_conj (R S : V ≃ₗ[ℂ] V) (T : V →ₗ[ℂ] V) :
    ftconj R (ftconj S T) = ftconj (R * S) T := by
  ext x
  simp only [ftconj, Module.End.mul_apply, mul_inv_rev, ← ftcoe_mul_coe R S, ← ftcoe_mul_coe S⁻¹ R⁻¹]

private lemma ftconj_pow (R : V ≃ₗ[ℂ] V) (k : ℕ) (T : V →ₗ[ℂ] V) :
    ftconj (R ^ k) T = (ftconj R)^[k] T := by
  induction k with
  | zero => ext x; simp [ftconj]
  | succ k ih =>
      rw [pow_succ', ← ftconj_conj R (R ^ k) T, ih, Function.iterate_succ_apply']

private lemma ftconj_rho (ρ : G →* (V ≃ₗ[ℂ] V)) (R : V ≃ₗ[ℂ] V) (φ : G → G)
    (hφ : ∀ g : G, R * ρ g * R⁻¹ = ρ (φ g)) (g : G) :
    ftconj R (ρ g : V →ₗ[ℂ] V) = (ρ (φ g) : V →ₗ[ℂ] V) := by
  rw [ftconj, ftcoe_mul_coe, ftcoe_mul_coe, hφ g]

/-- The pullback of a character along an automorphism of `G`. -/
private noncomputable def ftpullChar (φ : G ≃* G) (ψ : AddChar (Additive G) ℂ) :
    AddChar (Additive G) ℂ :=
  ψ.compAddMonoidHom (φ.symm : G →* G).toAdditive

private lemma ftchi_pullChar (φ : G ≃* G) (ψ : AddChar (Additive G) ℂ) (g : G) :
    ftchi (ftpullChar φ ψ) g = ftchi ψ (φ.symm g) := by
  simp [ftchi, ftpullChar]

private lemma ftpullChar_injective (φ : G ≃* G) : Function.Injective (ftpullChar φ) := by
  intro ψ ψ' h
  have h2 : ∀ g : G, ftchi ψ g = ftchi ψ' g := by
    intro g
    have h3 := congrArg (fun χ : AddChar (Additive G) ℂ => ftchi χ (φ g)) h
    simpa [ftchi_pullChar] using h3
  ext x
  have h4 := h2 (Additive.toMul x)
  simpa [ftchi] using h4

private lemma ftpullChar_bijective (φ : G ≃* G) : Function.Bijective (ftpullChar φ) :=
  ⟨ftpullChar_injective φ, Finite.injective_iff_surjective.mp (ftpullChar_injective φ)⟩

private lemma ftsum_conj_smul (R : V ≃ₗ[ℂ] V) (f : G → ℂ) (T : G → V →ₗ[ℂ] V) :
    (∑ g : G, ftconj R (f g • T g)) = ∑ g : G, f g • ftconj R (T g) :=
  Finset.sum_congr rfl (fun g _ => by rw [ftconj_smul])

private lemma ftsum_conj_rho (ρ : G →* (V ≃ₗ[ℂ] V)) (R : V ≃ₗ[ℂ] V) (φ : G → G)
    (hφ : ∀ g : G, R * ρ g * R⁻¹ = ρ (φ g)) (f : G → ℂ) :
    (∑ g : G, f g • ftconj R (ρ g : V →ₗ[ℂ] V)) = ∑ g : G, f g • (ρ (φ g) : V →ₗ[ℂ] V) :=
  Finset.sum_congr rfl (fun g _ => by rw [ftconj_rho ρ R φ hφ])

private lemma ftsum_chi_pull (φ : G ≃* G) (ψ : AddChar (Additive G) ℂ) (F : G → V →ₗ[ℂ] V) :
    (∑ h : G, (ftchi ψ (φ.symm h))⁻¹ • F h) = ∑ h : G, (ftchi (ftpullChar φ ψ) h)⁻¹ • F h :=
  Finset.sum_congr rfl (fun h _ => by rw [ftchi_pullChar])

private lemma ftconj_proj (ρ : G →* (V ≃ₗ[ℂ] V)) (R : V ≃ₗ[ℂ] V) (φ : G ≃* G)
    (hφ : ∀ g : G, R * ρ g * R⁻¹ = ρ (φ g)) (ψ : AddChar (Additive G) ℂ) :
    ftconj R (ftproj ρ ψ) = ftproj ρ (ftpullChar φ ψ) := by
  classical
  have hreindex : (∑ g : G, (ftchi ψ g)⁻¹ • (ρ (φ g) : V →ₗ[ℂ] V))
      = ∑ h : G, (ftchi ψ (φ.symm h))⁻¹ • (ρ h : V →ₗ[ℂ] V) :=
    by
      have h := Equiv.sum_comp (φ : G ≃ G)
        (fun h : G => (ftchi ψ (φ.symm h))⁻¹ • (ρ h : V →ₗ[ℂ] V))
      simpa using h
  calc ftconj R (ftproj ρ ψ)
      = ftconj R (((Fintype.card G : ℂ))⁻¹ • ∑ g : G, (ftchi ψ g)⁻¹ • (ρ g : V →ₗ[ℂ] V)) := by
        rw [fthproj ρ ψ]
    _ = ((Fintype.card G : ℂ))⁻¹ • ∑ g : G, (ftchi ψ g)⁻¹ • ftconj R (ρ g : V →ₗ[ℂ] V) := by
        rw [ftconj_smul, ftconj_sum, ftsum_conj_smul]
    _ = ((Fintype.card G : ℂ))⁻¹ • ∑ g : G, (ftchi ψ g)⁻¹ • (ρ (φ g) : V →ₗ[ℂ] V) := by
        rw [ftsum_conj_rho ρ R φ hφ]
    _ = ((Fintype.card G : ℂ))⁻¹ • ∑ h : G, (ftchi ψ (φ.symm h))⁻¹ • (ρ h : V →ₗ[ℂ] V) := by
        rw [hreindex]
    _ = ((Fintype.card G : ℂ))⁻¹ • ∑ h : G, (ftchi (ftpullChar φ ψ) h)⁻¹ • (ρ h : V →ₗ[ℂ] V) := by
        rw [ftsum_chi_pull]
    _ = ftproj ρ (ftpullChar φ ψ) := by rw [fthproj ρ (ftpullChar φ ψ)]

private lemma ftconj_pow_proj (ρ : G →* (V ≃ₗ[ℂ] V)) (R : V ≃ₗ[ℂ] V) (φ : G ≃* G)
    (hφ : ∀ g : G, R * ρ g * R⁻¹ = ρ (φ g)) (k : ℕ) (ψ : AddChar (Additive G) ℂ) :
    (ftconj R)^[k] (ftproj ρ ψ) = ftproj ρ ((ftpullChar φ)^[k] ψ) := by
  induction k with
  | zero => rw [Function.iterate_zero, id_eq, Function.iterate_zero, id_eq]
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, ftconj_proj ρ R φ hφ, Function.iterate_succ_apply']


/-! ## The count of characters and the final argument -/

private lemma ftconj_zero (R : V ≃ₗ[ℂ] V) : ftconj R 0 = 0 := by simp [ftconj]

private lemma ftconj_one (T : V →ₗ[ℂ] V) : ftconj 1 T = T := by
  ext x
  simp [ftconj]

private lemma ftcoe_one_lin : ((1 : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V) = 1 := by
  ext x
  rfl

private lemma ftconj_eq_zero_iff (R : V ≃ₗ[ℂ] V) (T : V →ₗ[ℂ] V) : ftconj R T = 0 ↔ T = 0 := by
  constructor
  · intro h
    have h2 : ftconj R⁻¹ (ftconj R T) = ftconj R⁻¹ 0 := by rw [h]
    rw [ftconj_conj, inv_mul_cancel, ftconj_one, ftconj_zero] at h2
    exact h2
  · intro h
    rw [h]
    exact ftconj_zero R

private lemma ftconj_injective (R : V ≃ₗ[ℂ] V) : Function.Injective (ftconj R) := by
  intro T T' h
  have h2 : ftconj R⁻¹ (ftconj R T) = ftconj R⁻¹ (ftconj R T') := congrArg (ftconj R⁻¹) h
  simpa [ftconj_conj, ftconj_one] using h2

private lemma ftproj_apply_self (ρ : G →* (V ≃ₗ[ℂ] V)) (ψ : AddChar (Additive G) ℂ) (w : V) :
    ftproj ρ ψ (ftproj ρ ψ w) = ftproj ρ ψ w := by
  rw [show ftproj ρ ψ (ftproj ρ ψ w) = (ftproj ρ ψ * ftproj ρ ψ) w from rfl, ftproj_mul_proj,
    if_pos rfl]

private lemma ftproj_apply_other (ρ : G →* (V ≃ₗ[ℂ] V)) {ψ ψ' : AddChar (Additive G) ℂ}
    (h : ψ ≠ ψ') (w : V) : ftproj ρ ψ (ftproj ρ ψ' w) = 0 := by
  rw [show ftproj ρ ψ (ftproj ρ ψ' w) = (ftproj ρ ψ * ftproj ρ ψ') w from rfl, ftproj_mul_proj, if_neg h]
  rfl

private lemma ftcard_sigSet_le (ρ : G →* (V ≃ₗ[ℂ] V)) [Module.Finite ℂ V]
    [Fintype {ψ : AddChar (Additive G) ℂ // ftproj ρ ψ ≠ 0}] :
    Fintype.card {ψ : AddChar (Additive G) ℂ // ftproj ρ ψ ≠ 0} ≤ Module.finrank ℂ V := by
  classical
  have hw : ∀ ψ : {ψ : AddChar (Additive G) ℂ // ftproj ρ ψ ≠ 0}, ∃ w : V, ftproj ρ ψ.1 w ≠ 0 := by
    intro ψ
    by_contra h
    push_neg at h
    exact ψ.2 (LinearMap.ext fun w => by simpa using h w)
  let f : {ψ : AddChar (Additive G) ℂ // ftproj ρ ψ ≠ 0} → V :=
    fun ψ => ftproj ρ ψ.1 (Classical.choose (hw ψ))
  have hf : ∀ ψ, ftproj ρ ψ.1 (f ψ) ≠ 0 := fun ψ => by
    show ftproj ρ ψ.1 (ftproj ρ ψ.1 (Classical.choose (hw ψ))) ≠ 0
    rw [ftproj_apply_self]
    exact Classical.choose_spec (hw ψ)
  have hind : LinearIndependent ℂ f := by
    rw [linearIndependent_iff']
    intro s g hg ψ hψ
    have h1 : ftproj ρ ψ.1 (∑ j ∈ s, g j • f j) = 0 := by rw [hg, map_zero]
    have h2 : ftproj ρ ψ.1 (∑ j ∈ s, g j • f j) = g ψ • ftproj ρ ψ.1 (f ψ) := by
      rw [map_sum, Finset.sum_eq_single ψ]
      · rw [map_smul]
      · intro j _ hji
        rw [map_smul]
        have hzero : ftproj ρ ψ.1 (f j) = 0 := by
          show ftproj ρ ψ.1 (ftproj ρ j.1 (Classical.choose (hw j))) = 0
          exact ftproj_apply_other ρ (fun hc => hji (Subtype.ext hc.symm)) _
        rw [hzero, smul_zero]
      · intro h
        exact absurd hψ h
    rw [h2] at h1
    by_contra hg0
    exact smul_ne_zero hg0 (hf ψ) h1
  exact hind.fintype_card_le_finrank

private noncomputable def ftconjAut (ρ : G →* (V ≃ₗ[ℂ] V)) (hinj : Function.Injective ρ)
    (R : V ≃ₗ[ℂ] V) (hR : ∀ g : G, ∃ g' : G, R * ρ g * R⁻¹ = ρ g') : G →* G where
  toFun g := Classical.choose (hR g)
  map_one' := hinj (by
    have h1 : ρ (Classical.choose (hR 1)) = R * ρ 1 * R⁻¹ :=
      (Classical.choose_spec (hR 1)).symm
    rw [h1, map_one]
    group)
  map_mul' g g' := hinj (by
    have h1 : ρ (Classical.choose (hR (g * g'))) = R * ρ (g * g') * R⁻¹ :=
      (Classical.choose_spec (hR (g * g'))).symm
    have h2 : ρ (Classical.choose (hR g)) = R * ρ g * R⁻¹ :=
      (Classical.choose_spec (hR g)).symm
    have h3 : ρ (Classical.choose (hR g')) = R * ρ g' * R⁻¹ :=
      (Classical.choose_spec (hR g')).symm
    calc ρ (Classical.choose (hR (g * g')))
        = R * ρ (g * g') * R⁻¹ := h1
      _ = R * (ρ g * ρ g') * R⁻¹ := by rw [map_mul]
      _ = (R * ρ g * R⁻¹) * (R * ρ g' * R⁻¹) := by group
      _ = ρ (Classical.choose (hR g)) * ρ (Classical.choose (hR g')) := by rw [h2, h3]
      _ = ρ (Classical.choose (hR g) * Classical.choose (hR g')) := by rw [map_mul])

private lemma ftconjAut_injective (ρ : G →* (V ≃ₗ[ℂ] V)) (hinj : Function.Injective ρ)
    (R : V ≃ₗ[ℂ] V) (hR : ∀ g : G, ∃ g' : G, R * ρ g * R⁻¹ = ρ g') :
    Function.Injective (ftconjAut ρ hinj R hR) := by
  intro g g' h
  apply hinj
  have h1 : ρ (Classical.choose (hR g)) = R * ρ g * R⁻¹ := (Classical.choose_spec (hR g)).symm
  have h2 : ρ (Classical.choose (hR g')) = R * ρ g' * R⁻¹ :=
    (Classical.choose_spec (hR g')).symm
  have h3 : R * ρ g * R⁻¹ = R * ρ g' * R⁻¹ := by
    calc R * ρ g * R⁻¹ = ρ (Classical.choose (hR g)) := h1.symm
      _ = ρ (Classical.choose (hR g')) := congrArg ρ h
      _ = R * ρ g' * R⁻¹ := h2
  have h4 := congrArg (fun T : V ≃ₗ[ℂ] V => R⁻¹ * T * R) h3
  simpa [mul_assoc] using h4

private theorem ftfourierMain (ρ : G →* (V ≃ₗ[ℂ] V)) [Module.Finite ℂ V]
    (hinj : Function.Injective ρ) (R : V ≃ₗ[ℂ] V)
    (hR : ∀ g : G, ∃ g' : G, R * ρ g * R⁻¹ = ρ g') :
    ∀ g : G, R ^ (Nat.factorial (Module.finrank ℂ V)) * ρ g
      = ρ g * R ^ (Nat.factorial (Module.finrank ℂ V)) := by
  classical
  let φ0 : G →* G := ftconjAut ρ hinj R hR
  have hinjφ : Function.Injective φ0 := ftconjAut_injective ρ hinj R hR
  let φ : G ≃* G := MulEquiv.ofBijective φ0
    ⟨hinjφ, Finite.injective_iff_surjective.mp hinjφ⟩
  have hφ : ∀ g : G, R * ρ g * R⁻¹ = ρ (φ g) := fun g => Classical.choose_spec (hR g)
  set d : ℕ := Module.finrank ℂ V with hd
  let Sig := {ψ : AddChar (Additive G) ℂ // ftproj ρ ψ ≠ 0}
  let σ : Sig → Sig := fun ψ => ⟨ftpullChar φ ψ.1, by
    rw [← ftconj_proj ρ R φ hφ ψ.1]
    exact fun h => ψ.2 ((ftconj_eq_zero_iff R (ftproj ρ ψ.1)).mp h)⟩
  have hinjσ : Function.Injective σ := fun a b h =>
    Subtype.ext (ftpullChar_injective φ (congrArg Subtype.val h))
  have hσval : ∀ (k : ℕ) (ψ : Sig),
      ((σ^[k] ψ : Sig) : AddChar (Additive G) ℂ) = (ftpullChar φ)^[k] ψ.1 := by
    intro k ψ
    induction k with
    | zero => rw [Function.iterate_zero, id_eq, Function.iterate_zero, id_eq]
    | succ k ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        show ftpullChar φ ↑(σ^[k] ψ) = ftpullChar φ ((ftpullChar φ)^[k] ↑ψ)
        rw [ih]
  have hbound : Fintype.card Sig ≤ d := by
    rw [hd]
    exact ftcard_sigSet_le ρ
  have horbit : ∀ ψ : Sig, (σ^[Nat.factorial d]) ψ = ψ := by
    intro ψ
    obtain ⟨a, b, hab, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun k : Fin (Fintype.card Sig + 1) => (σ^[k.1]) ψ) (by simp)
    rcases lt_or_gt_of_ne hab with hij | hij
    · have hpos : 0 < b.1 - a.1 := by omega
      have hle : b.1 - a.1 ≤ d := by have := b.2; omega
      have hstep : (σ^[b.1 - a.1]) ψ = ψ := by
        have h1 : (σ^[a.1]) ((σ^[b.1 - a.1]) ψ) = (σ^[a.1]) ψ := by
          rw [← Function.iterate_add_apply, Nat.add_sub_of_le (le_of_lt hij), heq]
        exact (Function.Injective.iterate hinjσ a.1) h1
      obtain ⟨t, ht⟩ := Nat.dvd_factorial hpos hle
      have hfac : Nat.factorial d = (b.1 - a.1) * t := by rw [ht]
      rw [hfac, Function.iterate_mul, Function.iterate_fixed hstep]
    · have hpos : 0 < a.1 - b.1 := by omega
      have hle : a.1 - b.1 ≤ d := by have := a.2; omega
      have hstep : (σ^[a.1 - b.1]) ψ = ψ := by
        have h1 : (σ^[b.1]) ((σ^[a.1 - b.1]) ψ) = (σ^[b.1]) ψ := by
          rw [← Function.iterate_add_apply, Nat.add_sub_of_le (le_of_lt hij), heq]
        exact (Function.Injective.iterate hinjσ b.1) h1
      obtain ⟨t, ht⟩ := Nat.dvd_factorial hpos hle
      have hfac : Nat.factorial d = (a.1 - b.1) * t := by rw [ht]
      rw [hfac, Function.iterate_mul, Function.iterate_fixed hstep]
  have hfix : ∀ ψ : AddChar (Additive G) ℂ, ftconj (R ^ Nat.factorial d) (ftproj ρ ψ) = ftproj ρ ψ := by
    intro ψ
    by_cases hψ : ftproj ρ ψ = 0
    · rw [hψ, ftconj_zero]
    · have h2 : (σ^[Nat.factorial d]) ⟨ψ, hψ⟩ = ⟨ψ, hψ⟩ := horbit ⟨ψ, hψ⟩
      have h3 := congrArg Subtype.val h2
      rw [hσval] at h3
      rw [ftconj_pow, ftconj_pow_proj ρ R φ hφ, h3]
  intro g
  have hconj_rho : ftconj (R ^ Nat.factorial d) (ρ g : V →ₗ[ℂ] V) = (ρ g : V →ₗ[ℂ] V) := by
    rw [← ftsum_chi_proj ρ g]
    rw [ftconj_sum, ftsum_conj_smul]
    exact Finset.sum_congr rfl (fun ψ _ => by rw [hfix ψ])
  have h2 : (R ^ Nat.factorial d : V ≃ₗ[ℂ] V) * ρ g
      = ρ g * (R ^ Nat.factorial d : V ≃ₗ[ℂ] V) := by
    refine LinearEquiv.ext (fun x => ?_)
    have h3 : ((R ^ Nat.factorial d : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V) * (ρ g : V →ₗ[ℂ] V)
        = (ρ g : V →ₗ[ℂ] V) * ((R ^ Nat.factorial d : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V) := by
      have h4 := congrArg (fun T : V →ₗ[ℂ] V =>
        T * ((R ^ Nat.factorial d : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V)) hconj_rho
      rw [ftconj, mul_assoc,
        ftcoe_mul_coe ((R ^ Nat.factorial d)⁻¹) (R ^ Nat.factorial d),
        inv_mul_cancel, ftcoe_one_lin, mul_one] at h4
      exact h4
    simpa [LinearEquiv.mul_apply] using LinearMap.congr_fun h3 x
  rw [hd]
  exact h2

/-! ## The target theorem -/

set_option maxHeartbeats 1000000 in
theorem axisTranslationCentralises (m : ℕ) (hm : 0 < m)
    (hA1 : Submission.Mostow.POActionProp 1) (hI1 : Submission.Mostow.HypIsometryProp 1)
    (hA : Submission.Mostow.POActionProp (1 + m)) (hI : Submission.Mostow.HypIsometryProp (1 + m))
    (N : Subgroup (LeanEval.Geometry.MostowRigidity.PO (1 + m) 1)) (hdisc : IsDiscrete (SetLike.coe N))
    (hN : ∀ n ∈ N, n ∈ Submission.Mostow.SetStabStd 1 m)
    (g : LeanEval.Geometry.MostowRigidity.PO (1 + m) 1) (hg : g ∈ N)
    (P : Subgroup (LeanEval.Geometry.MostowRigidity.PO (1 + m) 1))
    (hP : ∀ p ∈ P, p ∈ N ∧ Submission.Mostow.resStd 1 m p = 1)
    (hPnorm : ∀ n ∈ N, ∀ p : LeanEval.Geometry.MostowRigidity.PO (1 + m) 1, p ∈ P → n * p * n⁻¹ ∈ P)
    (A : Subgroup (Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m))
    (hAdef : ∀ x : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m, x ∈ A ↔
      x ∈ Subgroup.closure (Submission.Mostow.nrmStd 1 m ''
        {p : LeanEval.Geometry.MostowRigidity.PO (1 + m) 1 |
          p ∈ P ∧ Submission.Mostow.rotN (Submission.Mostow.nrmStd 1 m p) ≤ 1 / 4})) :
    ∀ a ∈ A, (Submission.Mostow.nrmStd 1 m g) ^ (Nat.factorial m) * a =
      a * (Submission.Mostow.nrmStd 1 m g) ^ (Nat.factorial m) := by
  classical
  obtain ⟨hAfin, hAcomm, hAnorm⟩ :=
    axisGenFiniteAbelian m hm hA1 hI1 hA hI N hdisc hN g hg P hP hPnorm A hAdef
  have hfinC : Module.finrank ℂ (Submission.Mostow.E m × Submission.Mostow.E m) = m := by
    rw [finrank_prod_complex, finrank_euclideanSpace_fin]
  let ρC : ↥A →* ((Submission.Mostow.E m × Submission.Mostow.E m) ≃ₗ[ℂ]
      (Submission.Mostow.E m × Submission.Mostow.E m)) :=
    Margulis.cActHom.comp (Subgroup.subtype A)
  have hinjC : Function.Injective ρC := by
    intro a b h
    refine Subtype.ext (cActHom_injective' ?_)
    simpa [ρC] using h
  have hRC : ∀ a : ↥A, ∃ a' : ↥A,
      Margulis.cActHom (Submission.Mostow.nrmStd 1 m g) * ρC a *
        (Margulis.cActHom (Submission.Mostow.nrmStd 1 m g))⁻¹ = ρC a' := by
    intro a
    refine ⟨⟨Submission.Mostow.nrmStd 1 m g * (a : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m) *
      (Submission.Mostow.nrmStd 1 m g)⁻¹, hAnorm a a.2⟩, ?_⟩
    simp only [ρC, MonoidHom.comp_apply, Subgroup.coe_subtype]
    rw [map_mul, map_mul, map_inv]
  haveI : Fintype ↥A := Fintype.ofFinite ↥A
  letI : CommGroup ↥A := { (inferInstance : Group ↥A) with
    mul_comm := fun a b => Subtype.ext (hAcomm a a.2 b b.2) }
  have hkey := ftfourierMain (V := Submission.Mostow.E m × Submission.Mostow.E m) (G := ↥A)
    (ρ := ρC) (hinj := hinjC) (R := Margulis.cActHom (Submission.Mostow.nrmStd 1 m g)) (hR := hRC)
  intro a ha
  have h1 := hkey ⟨a, ha⟩
  rw [hfinC] at h1
  have h2 : Margulis.cActHom ((Submission.Mostow.nrmStd 1 m g) ^ (Nat.factorial m) * a)
      = Margulis.cActHom (a * (Submission.Mostow.nrmStd 1 m g) ^ (Nat.factorial m)) := by
    simp only [ρC, MonoidHom.comp_apply, Subgroup.coe_subtype] at h1
    simp only [map_mul, map_pow]
    exact h1
  exact cActHom_injective' h2

end

end Work.Mostow
