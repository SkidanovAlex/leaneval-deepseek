import Mathlib
import Submission.Work.BW.DefsB
import Submission.Work.BW.wuestholzDefs
import Submission.Work.BW.uGen_defs
import Submission.Work.BW.prodX_mem_homPiece
import Submission.Work.BW.eval_prodX_conePt
import Submission.Work.BW.prod_zpow_eq_prod_toNat

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! # The generators of `𝔓 = subIdeal N ρ ε M` (Wüstholz's route)

This file proves `Work.BW.uGen_facts`, the bundle of elementary facts about the generators
`uGen M ε j` of `𝔓 = subIdeal N ρ ε M` on which the Wüstholz length bound rests:

* `derH w (uGen M ε j) ≡ chiFun M w j · chiMon M ε j  (mod 𝔓)`;
* `uGen M ε j ∈ 𝔓`;
* `chiMon M ε j ∉ 𝔓` for the indices that occur (`j < ρ`, or `ε = false` and `j` the last index);
* every element of `𝔓` vanishes at the cone point over every point of `G'`.

The technical heart is the eigenvector identity `derH w (genMul a b) = (∑ i, a i · w_{i+1}) · genMul a b`
for the torus monomials `genMul a b = ∏ i, X_{i+1,1}^{a i} X_{i+1,0}^{b i}`, of which `unitMon`
and `dualMon` are the two instances `(M⁺,M⁻)` and `(M⁻,M⁺)`.  It is proved by writing `genMul`
as a single monomial `monomial (ugGexp a b) 1` and using the logarithmic-derivative identity
`X_v · ∂_v (monomial m 1) = (m v) • monomial m 1`. -/

namespace Work.BW

/-- `(0 : Fin 2) ≠ 1`, a `decide`-free form usable inside `absurd`-style arguments. -/
lemma ug_fin2_zero_ne_one : ¬((0 : Fin 2) = 1) := by decide

/-! ## `genMul` as a monomial -/

/-- The exponent vector of the torus monomial `genMul a b`: the sum of the single-variable
exponents `a i` (on `X_{i+1,1}`) and `b i` (on `X_{i+1,0}`). -/
noncomputable def ugGexp {N : ℕ} (a b : Fin N → ℕ) : Fin (N + 1) × Fin 2 →₀ ℕ :=
  ∑ i : Fin N,
    (Finsupp.single (((i.succ : Fin (N + 1)), (1 : Fin 2))) (a i) +
      Finsupp.single (((i.succ : Fin (N + 1)), (0 : Fin 2))) (b i))

lemma ug_genMul_eq_monomial {N : ℕ} (a b : Fin N → ℕ) :
    genMul a b = MvPolynomial.monomial (ugGexp a b) 1 := by
  have hfac : ∀ i : Fin N,
      (MvPolynomial.X (((i.succ : Fin (N + 1)), (1 : Fin 2))) : MR N) ^ (a i) *
        MvPolynomial.X (((i.succ : Fin (N + 1)), (0 : Fin 2))) ^ (b i) =
      MvPolynomial.monomial
        (Finsupp.single (((i.succ : Fin (N + 1)), (1 : Fin 2))) (a i) +
          Finsupp.single (((i.succ : Fin (N + 1)), (0 : Fin 2))) (b i)) 1 := by
    intro i
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial,
      MvPolynomial.monomial_mul_monomial]
    simp
  rw [genMul, ugGexp]
  rw [Finset.prod_congr rfl (fun i _ => hfac i)]
  rw [← MvPolynomial.monomial_sum_one Finset.univ (fun i : Fin N =>
    (Finsupp.single (((i.succ : Fin (N + 1)), (1 : Fin 2))) (a i) +
      Finsupp.single (((i.succ : Fin (N + 1)), (0 : Fin 2))) (b i)))]

/-- The exponent of `X_{0,1}` in `ugGexp a b` is `0`: `genMul` has no `X_{0,·}` factor. -/
lemma ug_gexp_zero {N : ℕ} (a b : Fin N → ℕ) :
    ugGexp a b (((0 : Fin (N + 1)), (1 : Fin 2))) = 0 := by
  rw [ugGexp, Finsupp.finsetSum_apply]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  simp only [Finsupp.add_apply, Finsupp.single_apply]
  have h1 : ¬(((i.succ : Fin (N + 1)), (1 : Fin 2)) = (((0 : Fin (N + 1)), (1 : Fin 2)))) :=
    fun h => Fin.succ_ne_zero i (Prod.ext_iff.mp h).1
  have h2 : ¬(((i.succ : Fin (N + 1)), (0 : Fin 2)) = (((0 : Fin (N + 1)), (1 : Fin 2)))) :=
    fun h => Fin.succ_ne_zero i (Prod.ext_iff.mp h).1
  simp [h1, h2]

/-- The exponent of `X_{i+1,1}` in `ugGexp a b` is `a i`. -/
lemma ug_gexp_succ_one {N : ℕ} (a b : Fin N → ℕ) (i : Fin N) :
    ugGexp a b (((i.succ : Fin (N + 1)), (1 : Fin 2))) = a i := by
  rw [ugGexp, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single i]
  · simp only [Finsupp.add_apply, Finsupp.single_apply]
    have h2 : ¬(((i.succ : Fin (N + 1)), (0 : Fin 2)) = (((i.succ : Fin (N + 1)), (1 : Fin 2)))) :=
      fun h => ug_fin2_zero_ne_one (by simpa using (Prod.ext_iff.mp h).2)
    simp [h2]
  · intro j _ hj
    simp only [Finsupp.add_apply, Finsupp.single_apply]
    have h1 : ¬(((j.succ : Fin (N + 1)), (1 : Fin 2)) = (((i.succ : Fin (N + 1)), (1 : Fin 2)))) :=
      fun h => hj (Fin.succ_inj.mp (Prod.ext_iff.mp h).1)
    have h2 : ¬(((j.succ : Fin (N + 1)), (0 : Fin 2)) = (((i.succ : Fin (N + 1)), (1 : Fin 2)))) :=
      fun h => ug_fin2_zero_ne_one (by simpa using (Prod.ext_iff.mp h).2)
    simp [h1, h2]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-! ## The eigenvector identity for `derH` on a monomial -/

/-- Collecting a sum of scalar multiples of a fixed monomial into a single multiple. -/
lemma ug_sum_smul_monomial {N : ℕ} (w : Fin (N + 1) → ℂ) (m : Fin (N + 1) × Fin 2 →₀ ℕ) :
    (∑ i : Fin N, (w i.succ * (m (((i.succ : Fin (N + 1)), (1 : Fin 2))) : ℂ)) •
        (MvPolynomial.monomial m 1 : MR N)) =
      (∑ i : Fin N, w i.succ * (m (((i.succ : Fin (N + 1)), (1 : Fin 2))) : ℂ)) •
        (MvPolynomial.monomial m 1 : MR N) :=
  Finset.sum_smul.symm

/-- `derH` on a monomial: since `derH w = w₀ X₀₀ ∂_{X₀₁} + ∑_i w_{i+1} X_{i+1,1} ∂_{X_{i+1,1}}`
and `m` has no `X_{0,1}`, only the logarithmic derivatives of the `X_{i+1,1}` survive. -/
lemma ug_derH_monomial {N : ℕ} (w : Fin (N + 1) → ℂ) (m : Fin (N + 1) × Fin 2 →₀ ℕ)
    (hm : m (((0 : Fin (N + 1)), (1 : Fin 2))) = 0) :
    derH w (MvPolynomial.monomial m 1) =
      (∑ i : Fin N, w i.succ * (m (((i.succ : Fin (N + 1)), (1 : Fin 2))) : ℂ)) •
        MvPolynomial.monomial m 1 := by
  rw [derH]
  have h0 : MvPolynomial.C (w 0) * MvPolynomial.X (((0 : Fin (N + 1)), (0 : Fin 2))) *
      MvPolynomial.pderiv (((0 : Fin (N + 1)), (1 : Fin 2))) (MvPolynomial.monomial m 1) = 0 := by
    rw [MvPolynomial.pderiv_monomial, hm]
    simp
  rw [h0, zero_add]
  have hterm : ∀ i : Fin N,
      MvPolynomial.C (w i.succ) * MvPolynomial.X (((i.succ : Fin (N + 1)), (1 : Fin 2))) *
        MvPolynomial.pderiv (((i.succ : Fin (N + 1)), (1 : Fin 2)))
          (MvPolynomial.monomial m 1) =
      (w i.succ * (m (((i.succ : Fin (N + 1)), (1 : Fin 2))) : ℂ)) •
        MvPolynomial.monomial m 1 := by
    intro i
    rw [mul_assoc, MvPolynomial.X_mul_pderiv_monomial, MvPolynomial.C_mul',
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  simp only [hterm]
  rw [ug_sum_smul_monomial w m]

/-- The logarithmic derivative of the torus monomial `genMul a b` along `w`. -/
lemma ug_derH_genMul {N : ℕ} (w : Fin (N + 1) → ℂ) (a b : Fin N → ℕ) :
    derH w (genMul a b) = (∑ i : Fin N, (a i : ℂ) * w i.succ) • genMul a b := by
  rw [ug_genMul_eq_monomial, ug_derH_monomial w (ugGexp a b) (ug_gexp_zero a b)]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [ug_gexp_succ_one]
  ring

lemma ug_derH_unitMon {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) (j : Fin ρ) (w : Fin (N + 1) → ℂ) :
    derH w (unitMon M j) = (∑ i : Fin N, ((M j i).toNat : ℂ) * w i.succ) • unitMon M j := by
  rw [unitMon_eq_genMul]
  exact ug_derH_genMul w (fun i => (M j i).toNat) (fun i => (-(M j i)).toNat)

lemma ug_derH_dualMon {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) (j : Fin ρ) (w : Fin (N + 1) → ℂ) :
    derH w (dualMon M j) = (∑ i : Fin N, ((-(M j i)).toNat : ℂ) * w i.succ) • dualMon M j := by
  rw [dualMon_eq_genMul]
  exact ug_derH_genMul w (fun i => (-(M j i)).toNat) (fun i => (M j i).toNat)

/-! ## Linearity of `derH` -/

lemma derH_add_ug {N : ℕ} (w : Fin (N + 1) → ℂ) (F G : MR N) :
    derH w (F + G) = derH w F + derH w G := by
  simp only [derH, map_add, mul_add, Finset.sum_add_distrib]
  abel

lemma derH_neg_ug {N : ℕ} (w : Fin (N + 1) → ℂ) (F : MR N) : derH w (-F) = - derH w F := by
  simp only [derH, map_neg, mul_neg, Finset.sum_neg_distrib]
  abel

/-- `derH` on the homogenised binomial `χ^{M_j} - 1 = unitMon M j - dualMon M j`. -/
lemma ug_derH_homogChi {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) (j : Fin ρ) (w : Fin (N + 1) → ℂ) :
    derH w (homogChi M j) =
      (∑ i : Fin N, ((M j i).toNat : ℂ) * w i.succ) • unitMon M j -
      (∑ i : Fin N, ((-(M j i)).toNat : ℂ) * w i.succ) • dualMon M j := by
  rw [homogChi, sub_eq_add_neg, derH_add_ug, derH_neg_ug, ug_derH_unitMon, ug_derH_dualMon,
    sub_eq_add_neg]

/-- `derH w` of the last generator `X_{0,1}` (`ε = false`). -/
lemma derH_X01_ug {N : ℕ} (w : Fin (N + 1) → ℂ) :
    derH w (MvPolynomial.X (((0 : Fin (N + 1)), (1 : Fin 2))) : MR N) =
      w 0 • (MvPolynomial.X (((0 : Fin (N + 1)), (0 : Fin 2))) : MR N) := by
  rw [derH, MvPolynomial.pderiv_X_self, Finset.sum_eq_zero]
  · simp [MvPolynomial.smul_eq_C_mul]
  · intro i _
    rw [MvPolynomial.pderiv_X_of_ne (fun h => Fin.succ_ne_zero i (Prod.ext_iff.mp h).1.symm)]
    simp

/-! ## The generators lie in `𝔓` -/

lemma genMul_mem_homPiece_ug {N : ℕ} (a b : Fin N → ℕ) :
    genMul a b ∈ homPiece N (gdeg a b) := by
  simpa only [genMul, gdeg] using prodX_mem_homPiece (N := N) a b

lemma eval_conePt_genMul_ug {N : ℕ} (a b : Fin N → ℕ) (y : Fin (N + 1) → ℂ) :
    MvPolynomial.eval (conePt N y) (genMul a b) = ∏ i : Fin N, (y i.succ) ^ (a i) := by
  simpa only [genMul] using eval_prodX_conePt (N := N) a b y

lemma homogChi_mem_homPiece_ug {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) (j : Fin ρ) :
    homogChi M j ∈ homPiece N (gdeg (fun i => (M j i).toNat) (fun i => (-(M j i)).toNat)) := by
  have h1 := genMul_mem_homPiece_ug (N := N) (fun i => (M j i).toNat) (fun i => (-(M j i)).toNat)
  have h2 := genMul_mem_homPiece_ug (N := N) (fun i => (-(M j i)).toNat) (fun i => (M j i).toNat)
  rw [gdeg_comm (fun i => (-(M j i)).toNat) (fun i => (M j i).toNat)] at h2
  rw [homogChi, unitMon_eq_genMul, dualMon_eq_genMul]
  exact Submodule.sub_mem _ h1 h2

/-- The homogenised binomial `χ^{M_j} - 1` lies in `𝔓 = subIdeal N ρ ε M`: it is
multihomogeneous of multidegree `∑_i ((M_j i)⁺ + (M_j i)⁻) e_{i+1}` and vanishes on `G'`
(the lattice equation `∏_i y_{i+1}^{M_j i} = 1` splits into its nonnegative parts). -/
lemma homogChi_mem_subIdeal_ug {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) (ε : Bool) (j : Fin ρ) :
    homogChi M j ∈ subIdeal N ρ ε M := by
  refine Ideal.subset_span ⟨⟨_, homogChi_mem_homPiece_ug M j⟩, ?_⟩
  intro y hy
  have e1 : MvPolynomial.eval (conePt N y) (unitMon M j)
      = ∏ i : Fin N, (y i.succ) ^ ((M j i).toNat) := by
    rw [unitMon_eq_genMul, eval_conePt_genMul_ug]
  have e2 : MvPolynomial.eval (conePt N y) (dualMon M j)
      = ∏ i : Fin N, (y i.succ) ^ ((-(M j i)).toNat) := by
    rw [dualMon_eq_genMul, eval_conePt_genMul_ug]
  rw [homogChi, MvPolynomial.eval_sub, e1, e2, sub_eq_zero]
  exact prod_zpow_eq_prod_toNat (fun i => M j i) (fun i => y i.succ)
    (fun i => hy.2.1 i) (hy.2.2 j)

/-- The last generator `X_{0,1}` (used when `ε = false`) lies in `𝔓`. -/
lemma X01_mem_subIdeal_ug {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) (ε : Bool) (hε : ε = false) :
    MvPolynomial.X (((0 : Fin (N + 1)), (1 : Fin 2))) ∈ subIdeal N ρ ε M := by
  subst hε
  refine Ideal.subset_span ⟨⟨Finsupp.single (0 : Fin (N + 1)) 1,
    MvPolynomial.isWeightedHomogeneous_X ℂ (mdeg N) _⟩, ?_⟩
  intro y' hy'
  rw [MvPolynomial.eval_X]
  simpa [conePt] using hy'.1 rfl

/-! ## Vanishing of `𝔓` on `G'` and evaluation at the identity -/

/-- The identity `(0,1,…,1)` of `G` lies in `G'` for every `ε`, `M`. -/
lemma gone_mem_InSub_ug {N ρ : ℕ} (ε : Bool) (M : Fin ρ → Fin N → ℤ) :
    InSub N ρ ε M (gone N) := by
  refine ⟨fun _ => by simp [gone], fun i => by simp [gone], fun j => by simp [gone]⟩

/-- Every element of `𝔓 = subIdeal N ρ ε M` vanishes at the cone point over every point of `G'`. -/
lemma subIdeal_le_eval_ker_ug {N ρ : ℕ} (ε : Bool) (M : Fin ρ → Fin N → ℤ)
    {y : Fin (N + 1) → ℂ} (hy : InSub N ρ ε M y) :
    subIdeal N ρ ε M ≤ RingHom.ker (MvPolynomial.eval (conePt N y)) := by
  rw [subIdeal]
  exact Ideal.span_le.mpr (fun F hF => RingHom.mem_ker.mpr (hF.2 y hy))

lemma eval_zero_of_mem_subIdeal_ug {N ρ : ℕ} (ε : Bool) (M : Fin ρ → Fin N → ℤ)
    {F : MR N} (hF : F ∈ subIdeal N ρ ε M) {y : Fin (N + 1) → ℂ}
    (hy : InSub N ρ ε M y) : MvPolynomial.eval (conePt N y) F = 0 :=
  RingHom.mem_ker.mp (subIdeal_le_eval_ker_ug ε M hy hF)

lemma eval_gone_unitMon_ug {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) (j : Fin ρ) :
    MvPolynomial.eval (conePt N (gone N)) (unitMon M j) = 1 := by
  rw [unitMon_eq_genMul, eval_conePt_genMul_ug]
  simp [gone]

lemma eval_gone_X00_ug {N : ℕ} :
    MvPolynomial.eval (conePt N (gone N))
      (MvPolynomial.X (((0 : Fin (N + 1)), (0 : Fin 2))) : MR N) = 1 := by
  rw [MvPolynomial.eval_X]
  simp [conePt]

/-! ## The congruence `derH w (uGen j) ≡ chiFun w j · chiMon j (mod 𝔓)` -/

/-- The first conjunct in the case `j < ρ`: `derH w (χ^{M_j}-1) - (M_j·w)·unitMon M j`
equals `(∑_i (M_j i)⁻ w_{i+1}) · (unitMon M j - dualMon M j)` up to the identity
`M_j i = (M_j i)⁺ - (M_j i)⁻`, hence lies in `𝔓`. -/
lemma ug_uGen_chi_lt {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) (ε : Bool) (j : Fin (ρ + 1))
    (h : (j : ℕ) < ρ) (w : Fin (N + 1) → ℂ) :
    derH w (uGen M ε j) - chiFun M w j • chiMon M ε j ∈ subIdeal N ρ ε M := by
  have hu : uGen M ε j = homogChi M ⟨(j : ℕ), h⟩ := by simp [uGen, h]
  have hc : chiMon M ε j = unitMon M ⟨(j : ℕ), h⟩ := by simp [chiMon, h]
  have hf : chiFun M w j = ∑ i : Fin N, (M ⟨(j : ℕ), h⟩ i : ℂ) * w i.succ := by
    simp [chiFun, h]
  have hd := ug_derH_homogChi M ⟨(j : ℕ), h⟩ w
  have hcast : ∀ i : Fin N,
      (M ⟨(j : ℕ), h⟩ i : ℂ) =
        ((M ⟨(j : ℕ), h⟩ i).toNat : ℂ) - ((-(M ⟨(j : ℕ), h⟩ i)).toNat : ℂ) := by
    intro i
    have hZ : (((M ⟨(j : ℕ), h⟩ i).toNat : ℤ) : ℂ) -
        (((-(M ⟨(j : ℕ), h⟩ i)).toNat : ℤ) : ℂ) = ((M ⟨(j : ℕ), h⟩ i : ℤ) : ℂ) := by
      rw [← Int.cast_sub, Int.toNat_sub_toNat_neg]
    simpa only [Int.cast_natCast] using hZ.symm
  have hAB : (∑ i : Fin N, (M ⟨(j : ℕ), h⟩ i : ℂ) * w i.succ) =
      (∑ i : Fin N, ((M ⟨(j : ℕ), h⟩ i).toNat : ℂ) * w i.succ) -
      (∑ i : Fin N, ((-(M ⟨(j : ℕ), h⟩ i)).toNat : ℂ) * w i.succ) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← sub_mul]
    congr 1
    exact hcast i
  have hkey : derH w (uGen M ε j) - chiFun M w j • chiMon M ε j =
      (∑ i : Fin N, ((-(M ⟨(j : ℕ), h⟩ i)).toNat : ℂ) * w i.succ) •
        homogChi M ⟨(j : ℕ), h⟩ := by
    rw [hu, hc, hf, hAB, hd, homogChi]
    rw [sub_smul, smul_sub]
    abel
  rw [hkey, MvPolynomial.smul_eq_C_mul]
  exact Ideal.mul_mem_left _ _ (homogChi_mem_subIdeal_ug M ε ⟨(j : ℕ), h⟩)

/-- The generators of `𝔓 = subIdeal N ρ ε M` used in the Wüstholz argument lie in `𝔓`; their
`derH`-derivatives agree with the linear forms `chiFun` times the unit monomials `chiMon`
*modulo* `𝔓` (the exact identity fails when some `M j i < 0`, since `unitMon` and `dualMon` have
different `derH`-eigenvalues there); and those monomials are units at `𝔓` (not in it) for the
indices that can occur. -/
theorem uGen_facts {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) (ε : Bool) :
    (∀ (j : Fin (ρ + 1)) (w : Fin (N + 1) → ℂ),
        derH w (uGen M ε j) - chiFun M w j • chiMon M ε j ∈ subIdeal N ρ ε M) ∧
    (∀ j : Fin (ρ + 1), uGen M ε j ∈ subIdeal N ρ ε M) ∧
    (∀ (j : Fin (ρ + 1)), (j : ℕ) < ρ ∨ ε = false →
        chiMon M ε j ∉ subIdeal N ρ ε M) ∧
    (∀ F ∈ subIdeal N ρ ε M, ∀ y : Fin (N + 1) → ℂ, InSub N ρ ε M y →
        MvPolynomial.eval (conePt N y) F = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j w
    by_cases h : (j : ℕ) < ρ
    · exact ug_uGen_chi_lt M ε j h w
    · cases ε
      · have hu : uGen M false j = MvPolynomial.X (((0 : Fin (N + 1)), (1 : Fin 2))) := by
          simp [uGen, h]
        have hc : chiMon M false j = MvPolynomial.X (((0 : Fin (N + 1)), (0 : Fin 2))) := by
          simp [chiMon, h]
        have hf : chiFun M w j = w 0 := by simp [chiFun, h]
        rw [hu, hc, hf, derH_X01_ug, sub_self]
        exact Ideal.zero_mem _
      · have hu : uGen M true j = 0 := by simp [uGen, h]
        have hc : chiMon M true j = 0 := by simp [chiMon, h]
        rw [hu, hc]
        simp [derH]
  · intro j
    by_cases h : (j : ℕ) < ρ
    · have hu : uGen M ε j = homogChi M ⟨(j : ℕ), h⟩ := by simp [uGen, h]
      rw [hu]
      exact homogChi_mem_subIdeal_ug M ε ⟨(j : ℕ), h⟩
    · cases ε
      · have hu : uGen M false j = MvPolynomial.X (((0 : Fin (N + 1)), (1 : Fin 2))) := by
          simp [uGen, h]
        rw [hu]
        exact X01_mem_subIdeal_ug M false rfl
      · have hu : uGen M true j = 0 := by simp [uGen, h]
        rw [hu]
        exact Ideal.zero_mem _
  · intro j hj
    by_cases h : (j : ℕ) < ρ
    · have hc : chiMon M ε j = unitMon M ⟨(j : ℕ), h⟩ := by simp [chiMon, h]
      intro hmem
      have h0 := eval_zero_of_mem_subIdeal_ug ε M hmem (gone_mem_InSub_ug ε M)
      rw [hc, eval_gone_unitMon_ug] at h0
      exact one_ne_zero h0
    · have hε : ε = false := hj.resolve_left h
      subst hε
      have hc : chiMon M false j = MvPolynomial.X (((0 : Fin (N + 1)), (0 : Fin 2))) := by
        simp [chiMon, h]
      intro hmem
      have h0 := eval_zero_of_mem_subIdeal_ug false M hmem (gone_mem_InSub_ug false M)
      rw [hc, eval_gone_X00_ug] at h0
      exact one_ne_zero h0
  · intro F hF y hy
    exact eval_zero_of_mem_subIdeal_ug ε M hF hy

end Work.BW
