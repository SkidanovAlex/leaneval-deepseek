import Mathlib
import Submission.Commons.Algebra.Lie.E8_Msub_weight_finrank
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_denom_mul_Kostant
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_weyl_denom_support
import Submission.Commons.Algebra.Lie.E8_Kostant_secondOrder
import Submission.Commons.Algebra.Lie.E8_Kostant_crux_convolved
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_root_pairing_summation

/-!
# The Kostant–Freudenthal recursion for the `E₈` Verma module

`E8_Kostant_freudenthal` is the Freudenthal recursion for the weight multiplicities of the Verma
module over `e₈`: with `K` the Kostant partition function and `⟪·,·⟫` the lattice form,

  `(⟪ν+ρ,ν+ρ⟫ - ⟪μ+ρ,μ+ρ⟫) * K (ν - μ) = 2 Σ_{α>0} Σ_{k ≥ 1} (⟪μ,α⟫ + 2k) * K (ν - μ - kα)`.

Proof outline.  Writing `δ = ν - μ` and `K` for the Kostant count, the left-hand side is
`(⟪δ,δ⟫ + 2⟪μ,δ⟫ + 2 ht δ) * K δ`, and the three inputs are
* the **marking identity** `⟪μ,δ⟫ K δ = Σ_β Σ_n ⟪μ,β⟫ K (δ - nβ)`,
* the **second-order identity** `⟪δ,δ⟫ K δ = Σ_{β,β',n,m} ⟪β,β'⟫ K (δ-nβ-mβ') + 2 Σ n K (δ-nβ)`,
* the `μ`-independent **Casimir-null part** `(⟪δ,δ⟫ + 2 ht δ) K δ = 4 Σ n K (δ - nβ)`, which is the
  Freudenthal recursion for the Verma module's Casimir eigenvalue; it follows from the Weyl
  denominator's support being contained in the Casimir-null set (`E8_weyl_denom_support`), via the
  root-system identity `E8_root_pairing_summation` convolved with `K`
  (`E8_Kostant_crux_convolved`).
-/

namespace Commons.LinearAlgebra.Matrix.Cartan

open scoped BigOperators

noncomputable section

/-- The height-bounded Kostant count appearing in the statement. -/
noncomputable def Kbd (γ : Fin 8 → ℤ) : ℕ :=
  ((Fintype.piFinset (fun _ : ↥E8posRoots.P => Finset.range ((E8NormTwo.e8ht γ).toNat + 1))).filter
    (fun f => ∑ α : ↥E8posRoots.P, f α • (α : Fin 8 → ℤ) = γ)).card

/-- Height of a natural multiple. -/
lemma e8ht_nsmul' (n : ℕ) (v : Fin 8 → ℤ) :
    E8NormTwo.e8ht (n • v) = (n : ℤ) * E8NormTwo.e8ht v := by
  induction n with
  | zero => rw [zero_nsmul, e8ht_eq_sum_coords]; simp [coords]
  | succ k ih =>
      rw [add_nsmul, one_nsmul, e8ht_add, ih]
      push_cast
      ring

/-- Additivity of the height over a `↥P`-indexed sum. -/
lemma e8ht_sum_P (g : ↥E8posRoots.P → (Fin 8 → ℤ)) :
    E8NormTwo.e8ht (∑ α : ↥E8posRoots.P, g α) =
      ∑ α : ↥E8posRoots.P, E8NormTwo.e8ht (g α) := by
  simp only [e8ht_eq_sum_coords, coords, Matrix.mulVec_sum, Finset.sum_apply]
  rw [Finset.sum_comm]

/-- **The height-bounded Kostant count is the honest Kostant partition function.** -/
theorem Kbd_eq_KcountP (γ : Fin 8 → ℤ) : Kbd γ = Commons.Algebra.Lie.E8KostantId.KcountP γ := by
  classical
  have hγ : ∀ f : ↥E8posRoots.P → ℕ,
      (∑ α : ↥E8posRoots.P, f α • (α : Fin 8 → ℤ)) = γ →
      E8NormTwo.e8ht γ = ∑ α : ↥E8posRoots.P, (f α : ℤ) * E8NormTwo.e8ht (α : Fin 8 → ℤ) := by
    intro f hf
    have hsum : E8NormTwo.e8ht (∑ α : ↥E8posRoots.P, f α • (α : Fin 8 → ℤ)) =
        ∑ α : ↥E8posRoots.P, E8NormTwo.e8ht (f α • (α : Fin 8 → ℤ)) := e8ht_sum_P _
    rw [← hf, hsum]
    refine Finset.sum_congr rfl ?_
    intro α _
    rw [e8ht_nsmul']
  have hbound : ∀ f : ↥E8posRoots.P → ℕ,
      (∑ α : ↥E8posRoots.P, f α • (α : Fin 8 → ℤ)) = γ →
      ∀ α, f α < (E8NormTwo.e8ht γ).toNat + 1 := by
    intro f hf α
    have h1 : (f α : ℤ) ≤ (f α : ℤ) * E8NormTwo.e8ht (α : Fin 8 → ℤ) := by
      have := one_le_e8ht_of_mem_P α.2
      nlinarith [Nat.cast_nonneg (α := ℤ) (f α)]
    have h2 : (f α : ℤ) * E8NormTwo.e8ht (α : Fin 8 → ℤ) ≤ E8NormTwo.e8ht γ := by
      rw [hγ f hf]
      exact Finset.single_le_sum (f := fun α : ↥E8posRoots.P =>
          (f α : ℤ) * E8NormTwo.e8ht (α : Fin 8 → ℤ))
        (fun β _ => mul_nonneg (Nat.cast_nonneg _)
          (le_trans (by norm_num) (one_le_e8ht_of_mem_P β.2))) (Finset.mem_univ α)
    have h3 : (f α : ℤ) ≤ E8NormTwo.e8ht γ := le_trans h1 h2
    have hnt : 0 ≤ E8NormTwo.e8ht γ := by
      rw [hγ f hf]
      exact Finset.sum_nonneg fun β _ => mul_nonneg (Nat.cast_nonneg _)
        (le_trans (by norm_num) (one_le_e8ht_of_mem_P β.2))
    have h5 : f α ≤ (E8NormTwo.e8ht γ).toNat := by
      have h4 : (f α : ℤ) ≤ ((E8NormTwo.e8ht γ).toNat : ℤ) := by
        rwa [Int.toNat_of_nonneg hnt]
      exact_mod_cast h4
    omega
  have hset : {f : ↥E8posRoots.P → ℕ |
        ∑ α : ↥E8posRoots.P, f α • (α : Fin 8 → ℤ) = γ} =
      ↑(((Fintype.piFinset (fun _ : ↥E8posRoots.P =>
          Finset.range ((E8NormTwo.e8ht γ).toNat + 1))).filter
        (fun f => ∑ α : ↥E8posRoots.P, f α • (α : Fin 8 → ℤ) = γ)) : Finset (↥E8posRoots.P → ℕ)) := by
    ext f
    simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset,
      Finset.mem_range, Nat.lt_add_one_iff]
    constructor
    · intro hf
      exact ⟨fun α => Nat.lt_succ_iff.mp (hbound f hf α), hf⟩
    · rintro ⟨-, hf⟩
      exact hf
  have h1 : Nat.card {f : ↥E8posRoots.P → ℕ //
        ∑ α : ↥E8posRoots.P, f α • (α : Fin 8 → ℤ) = γ} = Nat.card {f : ↥E8posRoots.P → ℕ |
        ∑ α : ↥E8posRoots.P, f α • (α : Fin 8 → ℤ) = γ} := rfl
  rw [Kbd, Commons.Algebra.Lie.E8KostantId.KcountP, h1, hset]
  exact ((Nat.card_coe_set_eq (↑((Fintype.piFinset (fun _ : ↥E8posRoots.P =>
      Finset.range ((E8NormTwo.e8ht γ).toNat + 1))).filter
      (fun f => ∑ α : ↥E8posRoots.P, f α • (α : Fin 8 → ℤ) = γ)) : Set (↥E8posRoots.P → ℕ))).trans
    (Set.ncard_coe_finset _)).symm

/-! ## Transfers of the delegated combinatorial identities to the bounded count -/

/-- The marking identity, with the bounded Kostant count. -/
lemma E8inv_symm' (i j : Fin 8) : E8NormTwo.E8inv i j = E8NormTwo.E8inv j i := by
  fin_cases i <;> fin_cases j <;> norm_num [E8NormTwo.E8inv]

lemma bil_eq' (v w : Fin 8 → ℤ) : bil v w = ∑ i, ∑ j, v i * E8NormTwo.E8inv i j * w j := by
  simp only [bil, coords_apply, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma qZ_eq_bil' (v : Fin 8 → ℤ) : E8NormTwo.qZ v = bil v v := by
  simp only [E8NormTwo.qZ, bil_eq', coords_apply, dotProduct, Finset.mul_sum]

lemma bil_comm'' (v w : Fin 8 → ℤ) : bil v w = bil w v := by
  rw [bil_eq', bil_eq']
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [E8inv_symm' j i]
  ring

lemma bil_rho' (v : Fin 8 → ℤ) : bil v rhoZ = E8NormTwo.e8ht v := by
  rw [bil_eq']
  simp only [rhoZ, mul_one, e8ht_eq_sum_coords, coords_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [E8inv_symm' j i]
  ring

lemma qZ_add' (a b : Fin 8 → ℤ) :
    E8NormTwo.qZ (a + b) = E8NormTwo.qZ a + 2 * bil a b + E8NormTwo.qZ b := by
  have key : E8NormTwo.qZ (a + b) = bil (a + b) (a + b) := qZ_eq_bil' _
  have e1 : bil (a + b) (a + b) = bil a a + bil a b + bil b a + bil b b := by
    rw [bil_add_left, bil_add_right, bil_add_right]; ring
  rw [key, e1, qZ_eq_bil' a, qZ_eq_bil' b, bil_comm'' b a]
  ring

lemma qZ_shift (ν μ : Fin 8 → ℤ) :
    E8NormTwo.qZ (ν + rhoZ) - E8NormTwo.qZ (μ + rhoZ)
      = bil (ν - μ) (ν - μ) + 2 * bil (ν - μ) μ + 2 * bil (ν - μ) rhoZ := by
  have h1 := qZ_add' ν rhoZ
  have h2 := qZ_add' μ rhoZ
  have h3 := qZ_add' (ν - μ) μ
  have h4 : ν - μ + μ = ν := by abel
  rw [h4] at h3
  have h5 : bil (ν - μ) rhoZ = bil ν rhoZ - bil μ rhoZ := by
    rw [← bil_sub_left]
  have h6 : E8NormTwo.qZ (ν - μ) = bil (ν - μ) (ν - μ) := qZ_eq_bil' _
  linarith [h1, h2, h3, h5, h6]



lemma qZ_eq_sum' (v : Fin 8 → ℤ) :
    E8NormTwo.qZ v = ∑ i, v i * (E8NormTwo.E8inv.mulVec v) i := by
  rw [E8NormTwo.qZ]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  try exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma bil_eq_dot' (v w : Fin 8 → ℤ) :
    bil v w = ∑ i, v i * (E8NormTwo.E8inv.mulVec w) i := by
  rw [bil_eq']
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring


lemma marking_Kbd (v δ : Fin 8 → ℤ) :
    (∑ i, v i * (E8NormTwo.E8inv.mulVec δ) i) * (Kbd δ : ℤ)
      = ∑ β ∈ E8posRoots.P,
          ∑ n ∈ Finset.Icc 1 ((E8NormTwo.e8ht δ).toNat),
          (∑ i, v i * (E8NormTwo.E8inv.mulVec β) i) * (Kbd (δ - n • β) : ℤ) := by
  simp only [Kbd_eq_KcountP]
  have h := Commons.Algebra.Lie.bil_marking_PR v δ ((E8NormTwo.e8ht δ).toNat)
    (Int.self_le_toNat (E8NormTwo.e8ht δ))
  simp only [bil_eq_dot'] at h
  rw [← Finset.sum_subtype E8posRoots.P (fun x => Iff.rfl)
    (fun β : Fin 8 → ℤ => ∑ n ∈ Finset.Icc 1 ((E8NormTwo.e8ht δ).toNat),
      (∑ i, v i * (E8NormTwo.E8inv.mulVec β) i) *
        (Commons.Algebra.Lie.E8KostantId.KcountP (δ - n • β) : ℤ))] at h
  exact h

/-- The second-order identity, with the bounded Kostant count. -/
lemma secondOrder_Kbd (δ : Fin 8 → ℤ) :
    (∑ i, δ i * (E8NormTwo.E8inv.mulVec δ) i) * (Kbd δ : ℤ)
      = (∑ β ∈ E8posRoots.P, ∑ β' ∈ E8posRoots.P,
          ∑ n ∈ Finset.Icc 1 ((E8NormTwo.e8ht δ).toNat),
          ∑ m ∈ Finset.Icc 1 ((E8NormTwo.e8ht δ).toNat),
          (∑ i, β i * (E8NormTwo.E8inv.mulVec β') i) * (Kbd (δ - n • β - m • β') : ℤ))
        + 2 * (∑ β ∈ E8posRoots.P,
            ∑ n ∈ Finset.Icc 1 ((E8NormTwo.e8ht δ).toNat),
            (n : ℤ) * (Kbd (δ - n • β) : ℤ)) := by
  simp only [Kbd_eq_KcountP]
  exact Commons.Algebra.Lie.E8_Kostant_secondOrder δ

/-- The root-system identity convolved with the Kostant function (bounded form). -/
lemma convolved (δ : Fin 8 → ℤ) :
    (∑ β ∈ E8posRoots.P, ∑ β' ∈ E8posRoots.P,
      ∑ n ∈ Finset.Icc 1 ((E8NormTwo.e8ht δ).toNat),
      ∑ m ∈ Finset.Icc 1 ((E8NormTwo.e8ht δ).toNat),
      (∑ i, β i * (E8NormTwo.E8inv.mulVec β') i) * (Kbd (δ - n • β - m • β') : ℤ))
      + 2 * (∑ β ∈ E8posRoots.P,
          ∑ n ∈ Finset.Icc 1 ((E8NormTwo.e8ht δ).toNat),
          (E8NormTwo.e8ht β) * (Kbd (δ - n • β) : ℤ))
      = 2 * (∑ β ∈ E8posRoots.P,
          ∑ n ∈ Finset.Icc 1 ((E8NormTwo.e8ht δ).toNat),
          (n : ℤ) * (Kbd (δ - n • β) : ℤ)) := by
  have h := Commons.Algebra.Lie.E8_Kostant_crux_convolved
    (fun γ => E8_root_pairing_summation γ) δ
  simpa only [Kbd_eq_KcountP] using h

noncomputable def S2s (δ : Fin 8 → ℤ) : ℤ :=
  ∑ β ∈ E8posRoots.P, ∑ β' ∈ E8posRoots.P,
    ∑ n ∈ Finset.Icc 1 ((E8NormTwo.e8ht δ).toNat),
    ∑ m ∈ Finset.Icc 1 ((E8NormTwo.e8ht δ).toNat),
    (∑ i, β i * (E8NormTwo.E8inv.mulVec β') i) * (Kbd (δ - n • β - m • β') : ℤ)

noncomputable def HtS (δ : Fin 8 → ℤ) : ℤ :=
  ∑ β ∈ E8posRoots.P, ∑ n ∈ Finset.Icc 1 ((E8NormTwo.e8ht δ).toNat),
    (E8NormTwo.e8ht β) * (Kbd (δ - n • β) : ℤ)

noncomputable def NS (δ : Fin 8 → ℤ) : ℤ :=
  ∑ β ∈ E8posRoots.P, ∑ n ∈ Finset.Icc 1 ((E8NormTwo.e8ht δ).toNat),
    (n : ℤ) * (Kbd (δ - n • β) : ℤ)

noncomputable def DD (δ : Fin 8 → ℤ) : ℤ :=
  (∑ i, δ i * (E8NormTwo.E8inv.mulVec δ) i) * (Kbd δ : ℤ)

noncomputable def MM (v δ : Fin 8 → ℤ) : ℤ :=
  ∑ β ∈ E8posRoots.P, ∑ n ∈ Finset.Icc 1 ((E8NormTwo.e8ht δ).toNat),
    (∑ i, v i * (E8NormTwo.E8inv.mulVec β) i) * (Kbd (δ - n • β) : ℤ)

-- (star'') : S2s + 2 HtS = 2 NS
lemma star'' (δ : Fin 8 → ℤ) : S2s δ + 2 * HtS δ = 2 * NS δ := by
  simpa only [S2s, HtS, NS] using convolved δ

lemma e8ht_sum_E8inv (v : Fin 8 → ℤ) :
    (∑ i, (E8NormTwo.E8inv.mulVec v) i) = E8NormTwo.e8ht v := by
  rw [e8ht_eq_sum_coords]; rfl

lemma ht_mul_Kbd (δ : Fin 8 → ℤ) : E8NormTwo.e8ht δ * (Kbd δ : ℤ) = HtS δ := by
  have h := marking_Kbd rhoZ δ
  simp only [rhoZ, Pi.one_apply, one_mul] at h
  rw [e8ht_sum_E8inv] at h
  rw [HtS]
  refine h.trans ?_
  refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun n _ => ?_
  rw [e8ht_sum_E8inv]

-- (star star) : (qZ δ + 2 ht δ) * Kbd δ = 4 NS δ
lemma starstar (δ : Fin 8 → ℤ) :
    ((∑ i, δ i * (E8NormTwo.E8inv.mulVec δ) i) + 2 * E8NormTwo.e8ht δ) * (Kbd δ : ℤ)
      = 4 * NS δ := by
  have hid2 : DD δ = S2s δ + 2 * NS δ := by
    unfold DD S2s NS
    simpa using secondOrder_Kbd δ
  have hs := star'' δ
  have hrho := ht_mul_Kbd δ
  have := hid2
  unfold DD at this
  linarith [this, hs, hrho]



theorem E8_Kostant_freudenthal_Kbd (ν μ : Fin 8 → ℤ) :
    (E8NormTwo.qZ (ν + rhoZ) - E8NormTwo.qZ (μ + rhoZ)) *
        (Kbd (ν - μ) : ℤ)
      = 2 * ∑ α ∈ E8posRoots.P,
          ∑ k ∈ Finset.Icc 1 ((E8NormTwo.e8ht (ν - μ)).toNat),
          ((∑ i, μ i * (E8NormTwo.E8inv.mulVec (α : Fin 8 → ℤ)) i) + 2 * (k : ℤ)) *
            (Kbd (ν - μ - k • (α : Fin 8 → ℤ)) : ℤ) := by
  set δ := ν - μ with hδ
  have hq : E8NormTwo.qZ (ν + rhoZ) - E8NormTwo.qZ (μ + rhoZ)
      = E8NormTwo.qZ δ + 2 * bil μ δ + 2 * E8NormTwo.e8ht δ := by
    rw [qZ_shift ν μ, bil_rho', bil_comm'' (ν - μ) μ]
    rw [qZ_eq_bil']
  have hss : (E8NormTwo.qZ δ + 2 * E8NormTwo.e8ht δ) * (Kbd δ : ℤ) = 4 * NS δ := by
    simpa only [qZ_eq_sum'] using starstar δ
  have hm : bil μ δ * (Kbd δ : ℤ) = MM μ δ := by
    simp only [MM, bil_eq_dot']
    exact marking_Kbd μ δ
  have hmain : (E8NormTwo.qZ δ + 2 * bil μ δ + 2 * E8NormTwo.e8ht δ) * (Kbd δ : ℤ)
      = 4 * NS δ + 2 * MM μ δ := by
    have h : (E8NormTwo.qZ δ + 2 * bil μ δ + 2 * E8NormTwo.e8ht δ) * (Kbd δ : ℤ)
        = (E8NormTwo.qZ δ + 2 * E8NormTwo.e8ht δ) * (Kbd δ : ℤ) + 2 * (bil μ δ * (Kbd δ : ℤ)) := by
      ring
    rw [h, hss, hm]
  rw [hq, hmain]
  simp only [NS, MM, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring



/-- **The Kostant–Freudenthal recursion for the `E₈` Verma module.** -/
theorem E8_Kostant_freudenthal (ν μ : Fin 8 → ℤ) :
    (E8NormTwo.qZ (ν + rhoZ) - E8NormTwo.qZ (μ + rhoZ)) *
        (((Fintype.piFinset (fun _ : ↥E8posRoots.P =>
            Finset.range ((E8NormTwo.e8ht (ν - μ)).toNat + 1))).filter
          (fun f => ∑ α : ↥E8posRoots.P, f α • (α : Fin 8 → ℤ) = ν - μ)).card : ℤ)
      = 2 * ∑ α ∈ E8posRoots.P,
          ∑ k ∈ Finset.Icc 1 ((E8NormTwo.e8ht (ν - μ)).toNat),
          ((∑ i, μ i * (E8NormTwo.E8inv.mulVec (α : Fin 8 → ℤ)) i) + 2 * (k : ℤ)) *
            (((Fintype.piFinset (fun _ : ↥E8posRoots.P =>
              Finset.range ((E8NormTwo.e8ht (ν - μ - k • (α : Fin 8 → ℤ))).toNat + 1))).filter
              (fun f => ∑ β : ↥E8posRoots.P, f β • (β : Fin 8 → ℤ)
                = ν - μ - k • (α : Fin 8 → ℤ))).card : ℤ) := by
  simpa only [Kbd] using E8_Kostant_freudenthal_Kbd ν μ

end

end Commons.LinearAlgebra.Matrix.Cartan
