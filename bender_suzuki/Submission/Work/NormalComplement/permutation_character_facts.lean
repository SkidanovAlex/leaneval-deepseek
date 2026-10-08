import Mathlib
import Submission.Work.CharCore.Defs
import Submission.Work.Induction.Defs
import Submission.Work.Induction.frobenius_reciprocity
import Submission.Work.CharCore.irr_orthonormal
import Submission.Work.CharCore.CFun
import Submission.Work.Induction.indFun_apply_one
import Submission.Work.Induction.indFun_apply_eq_zero
import Submission.Work.Induction.Basic
import Submission.Work.Induction.isClassFun_indFun
import Submission.Work.Induction.exists_nat_cfInner_indFun
import Submission.Work.Induction.exists_nat_cfInner_resFun
import Submission.Work.CharCore.principalChar_mem_Irr
import Submission.Work.CharCore.cfInner_regularChar
import Submission.Work.CharCore.irrDeg_eq_one_of_commutative
import Submission.Work.CharCore.classFun_eq_sum_irr

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement

open Classical

variable {W : Type*} [Group W] [Fintype W] {I : Type*} [Fintype I] [MulAction W I]

/-- An element of a regular (sharply transitive) subgroup `K` fixes no nonempty set of points:
`(k : W) • i = i` forces `k = 1`. -/
theorem stabilizer_smul_eq_self_iff {K : Subgroup W}
    (hreg : ∀ i j : I, ∃! k : K, (k : W) • i = j) (k : K) (i : I) :
    (k : W) • i = i ↔ k = 1 := by
  constructor
  · intro h; exact (hreg i i).unique h (by simp)
  · intro h; subst h; simp

/-- The index of the point stabiliser of a regular action equals `|K|`. -/
theorem stabilizer_index_eq_card {K : Subgroup W} (α : I)
    (hreg : ∀ i j : I, ∃! k : K, (k : W) • i = j) :
    (MulAction.stabilizer W α).index = Nat.card K := by
  haveI : MulAction.IsPretransitive W I :=
    MulAction.isPretransitive_iff W I |>.mpr fun i j =>
      ⟨(Classical.choose (hreg i j).exists : K), Classical.choose_spec (hreg i j).exists⟩
  have hidx : (MulAction.stabilizer W α).index = Nat.card I :=
    MulAction.index_stabilizer_of_transitive W α
  have hbij : Function.Bijective (fun k : K => (k : W) • α) := by
    constructor
    · intro k k' h
      have hkk' : (k : W) • α = (k' : W) • α := h
      have h2 : ((k⁻¹ * k' : K) : W) • α = α := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, ← hkk', inv_smul_smul]
      have h3 : k⁻¹ * k' = 1 := (stabilizer_smul_eq_self_iff hreg (k⁻¹ * k') α).mp h2
      exact inv_mul_eq_one.mp h3
    · intro i
      exact ⟨Classical.choose (hreg α i).exists, Classical.choose_spec (hreg α i).exists⟩
  have hKI : Nat.card I = Nat.card K :=
    (Nat.card_congr (Equiv.ofBijective _ hbij)).symm
  exact hidx.trans hKI

/-- The permutation character `π = Ind_{W_α}^W 1` of an action with a regular subgroup `K`
vanishes at every nontrivial element of `K`. -/
theorem indFun_triv_apply_eq_zero {K : Subgroup W} (α : I)
    (hreg : ∀ i j : I, ∃! k : K, (k : W) • i = j) (k : K) (hk : k ≠ 1) :
    Work.CharCore.indFun (MulAction.stabilizer W α)
        (fun _ : MulAction.stabilizer W α => (1 : ℂ)) (k : W) = 0 := by
  rw [← Work.Induction.indFun_eq_charCore]
  apply Work.Induction.indFun_apply_eq_zero
  intro x hx
  have hfix : (x * (k : W) * x⁻¹) • α = α := MulAction.mem_stabilizer_iff.mp hx
  have h2 : (k : W) • (x⁻¹ • α) = x⁻¹ • α := by
    have hc := congrArg (fun t => x⁻¹ • t) hfix
    simpa only [mul_smul, inv_smul_smul] using hc
  exact hk ((stabilizer_smul_eq_self_iff hreg k (x⁻¹ • α)).mp h2)

/-- The permutation character takes the value `|K|` at `1` (the action being transitive). -/
theorem indFun_triv_apply_one {K : Subgroup W} (α : I)
    (hreg : ∀ i j : I, ∃! k : K, (k : W) • i = j) :
    Work.CharCore.indFun (MulAction.stabilizer W α)
        (fun _ : MulAction.stabilizer W α => (1 : ℂ)) 1 = (Nat.card K : ℂ) := by
  rw [← Work.Induction.indFun_eq_charCore]
  rw [Work.Induction.indFun_apply_one]
  rw [stabilizer_index_eq_card α hreg]
  simp

/-- **The permutation character of an action with a regular (sharply transitive) subgroup.**

`K ≤ W` acts regularly on `I` (`∀ i j, ∃! k : K, (k : W) • i = j`) and `C_W(k) = K` for
`k ∈ K^#`.  Let `π = Ind_{W_α}^W 1` be the permutation character of the action at a point `α`
(the character of `ℂ[I]`).  Then

* `π k = 0` for every `k ∈ K^#` and `π 1 = |K|`, i.e. `Res_K π` is the regular character of `K`;
* `⟨π, 1_W⟩ = 1` (the action is transitive);
* every irreducible character occurring in `π` occurs with multiplicity one. -/
theorem permutation_character_facts {W : Type*} [Group W] [Fintype W] {I : Type*} [Fintype I]
    [MulAction W I] {K : Subgroup W} (α : I)
    (hreg : ∀ i j : I, ∃! k : K, (k : W) • i = j)
    (hcent : ∀ k ∈ K, k ≠ 1 → Subgroup.centralizer ({k} : Set W) = K) :
    (∀ k : K, k ≠ 1 →
        Work.CharCore.indFun (MulAction.stabilizer W α)
          (fun _ : MulAction.stabilizer W α => (1 : ℂ)) (k : W) = 0) ∧
      Work.CharCore.indFun (MulAction.stabilizer W α)
          (fun _ : MulAction.stabilizer W α => (1 : ℂ)) 1 = (Nat.card K : ℂ) ∧
      Work.CharCore.cfInner
        (Work.CharCore.indFun (MulAction.stabilizer W α)
          (fun _ : MulAction.stabilizer W α => (1 : ℂ))) (1 : W → ℂ) = 1 ∧
      (∀ chi ∈ Work.CharCore.Irr W,
        Work.CharCore.cfInner
          (Work.CharCore.indFun (MulAction.stabilizer W α)
            (fun _ : MulAction.stabilizer W α => (1 : ℂ))) chi ≠ 0 →
        Work.CharCore.cfInner
          (Work.CharCore.indFun (MulAction.stabilizer W α)
            (fun _ : MulAction.stabilizer W α => (1 : ℂ))) chi = 1)
    := by
  classical
  haveI hne_stab : Nonempty { x : W // x • α = α } := ⟨⟨1, one_smul W α⟩⟩
  -- `K` is abelian: every nontrivial element of `K` has centraliser `K`
  have hKcomm : ∀ a b : ↥K, a * b = b * a := by
    intro a b
    by_cases ha : a = 1
    · subst ha; simp
    · have hmem : (b : W) ∈ Subgroup.centralizer ({(a : W)} : Set W) := by
        rw [hcent (a : W) a.2 (fun h => ha (Subtype.ext h))]
        exact b.2
      have hcab : (b : W) * (a : W) = (a : W) * (b : W) :=
        Subgroup.mem_centralizer_singleton_iff.mp hmem
      exact Subtype.ext hcab.symm
  haveI : IsMulCommutative ↥K := IsMulCommutative.of_comm hKcomm
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k hk
    exact indFun_triv_apply_eq_zero α hreg k hk
  · exact indFun_triv_apply_one α hreg
  · -- `⟨π, 1_W⟩ = 1`, by Frobenius reciprocity
    change Work.CharCore.cfInner
        (Work.Induction.indFun (MulAction.stabilizer W α) (fun _ => (1 : ℂ)))
        (1 : W → ℂ) = 1
    rw [Work.Induction.frobenius_reciprocity (MulAction.stabilizer W α) (fun _ => (1 : ℂ))
        (1 : W → ℂ) (Work.CharCore.isClassFun_const 1)]
    rw [Work.CharCore.cfInner_apply]
    simp [Work.Induction.resFun, Work.Induction.resFunHom]
  · -- multiplicity one
    let P : W → ℂ := Work.CharCore.indFun (MulAction.stabilizer W α)
      (fun _ : MulAction.stabilizer W α => (1 : ℂ))
    change ∀ χ ∈ Work.CharCore.Irr W,
      Work.CharCore.cfInner P χ ≠ 0 → Work.CharCore.cfInner P χ = 1
    have hPclass : Work.CharCore.IsClassFun P :=
      Work.Induction.isClassFun_indFun (MulAction.stabilizer W α) (fun _ => (1 : ℂ))
    -- the trivial character of the stabiliser is irreducible
    have htrivH : (fun _ : MulAction.stabilizer W α => (1 : ℂ))
        ∈ Work.CharCore.Irr (MulAction.stabilizer W α) := Work.CharCore.principalChar_mem_Irr
    -- multiplicities of the irreducibles of `W` in `P`
    let n : ↥(Work.CharCore.Irr W) → ℕ := fun χ =>
      Classical.choose (Work.Induction.exists_nat_cfInner_indFun
        (H := MulAction.stabilizer W α) (θ := fun _ : MulAction.stabilizer W α => (1 : ℂ))
        htrivH χ.2)
    have hn : ∀ χ : ↥(Work.CharCore.Irr W),
        Work.CharCore.cfInner P (χ : W → ℂ) = (n χ : ℂ) := fun χ =>
      Classical.choose_spec (Work.Induction.exists_nat_cfInner_indFun
        (H := MulAction.stabilizer W α) (θ := fun _ : MulAction.stabilizer W α => (1 : ℂ))
        htrivH χ.2)
    -- multiplicities of the irreducibles of `K` in the restrictions
    let m : ↥(Work.CharCore.Irr W) → ↥(Work.CharCore.Irr K) → ℕ := fun χ lam =>
      Classical.choose (Work.Induction.exists_nat_cfInner_resFun
        (H := K) (χ := (χ : W → ℂ)) χ.2 (θ := (lam : K → ℂ)) lam.2)
    have hm : ∀ (χ : ↥(Work.CharCore.Irr W)) (lam : ↥(Work.CharCore.Irr K)),
        Work.CharCore.cfInner (Work.Induction.resFun K (χ : W → ℂ)) (lam : K → ℂ)
          = (m χ lam : ℂ) := fun χ lam =>
      Classical.choose_spec (Work.Induction.exists_nat_cfInner_resFun
        (H := K) (χ := (χ : W → ℂ)) χ.2 (θ := (lam : K → ℂ)) lam.2)
    -- `Res_K P` is the regular character of `K`
    have hresFun : Work.Induction.resFun K P = Work.CharCore.regularChar K := by
      funext k
      rw [Work.Induction.resFun_apply]
      simp only [Work.CharCore.regularChar]
      by_cases hk : k = 1
      · rw [if_pos hk]
        have hk1 : (k : W) = 1 := by
          have := congrArg (fun x : ↥K => (x : W)) hk
          simpa using this
        rw [hk1]
        exact indFun_triv_apply_one α hreg
      · rw [if_neg hk]
        exact indFun_triv_apply_eq_zero α hreg k hk
    -- `⟨reg_K, λ⟩ = λ(1) = 1` for `λ ∈ Irr K`
    have hstabilizer : ∀ lam : ↥(Work.CharCore.Irr K),
        Work.CharCore.cfInner (Work.CharCore.regularChar K) (lam : K → ℂ) = 1 := by
      intro lam
      rw [Work.CharCore.cfInner_regularChar lam.2,
        Work.CharCore.irrDeg_eq_one_of_commutative lam.2]
      norm_num
    -- expansion of `⟨Res_K P, λ⟩`
    have hexp : ∀ lam : ↥(Work.CharCore.Irr K),
        Work.CharCore.cfInner (Work.Induction.resFun K P) (lam : K → ℂ)
          = ∑ χ : ↥(Work.CharCore.Irr W),
              (n χ : ℂ)
                * Work.CharCore.cfInner (Work.Induction.resFun K (χ : W → ℂ)) (lam : K → ℂ) := by
      intro lam
      have h1 : Work.Induction.resFun K P
          = ∑ χ ∈ Work.CharCore.Irr W,
              (Work.CharCore.cfInner P χ) • Work.Induction.resFun K χ := by
        conv_lhs => rw [Work.CharCore.classFun_eq_sum_irr hPclass]
        rw [Work.Induction.resFun_sum]
        refine Finset.sum_congr rfl (fun χ _ => ?_)
        rw [Work.Induction.resFun_smul]
      rw [h1, Work.CharCore.cfInner_sum_smul_left]
      rw [← Finset.sum_attach (Work.CharCore.Irr W)
            (fun χ => Work.CharCore.cfInner P χ
              * Work.CharCore.cfInner (Work.Induction.resFun K χ) (lam : K → ℂ))]
      refine Finset.sum_congr rfl (fun χ _ => ?_)
      rw [hn χ]
    -- the counting identity `∑_χ n_χ m_{χλ} = 1`
    have hcount : ∀ lam : ↥(Work.CharCore.Irr K),
        (∑ χ : ↥(Work.CharCore.Irr W), n χ * m χ lam) = 1 := by
      intro lam
      have hlamC : (∑ χ : ↥(Work.CharCore.Irr W), (n χ : ℂ) * (m χ lam : ℂ)) = 1 := by
        have heq : (∑ χ : ↥(Work.CharCore.Irr W), (n χ : ℂ) * (m χ lam : ℂ))
            = ∑ χ : ↥(Work.CharCore.Irr W),
                (n χ : ℂ)
                  * Work.CharCore.cfInner (Work.Induction.resFun K (χ : W → ℂ)) (lam : K → ℂ) := by
          refine Finset.sum_congr rfl (fun χ _ => ?_)
          rw [hm χ lam]
        rw [heq, ← hexp lam, hresFun, hstabilizer lam]
      apply Nat.cast_injective (R := ℂ)
      push_cast
      exact hlamC
    -- conclusion
    intro χ₀ hχ₀ hne
    let x0 : ↥(Work.CharCore.Irr W) := ⟨χ₀, hχ₀⟩
    change Work.CharCore.cfInner P (x0 : W → ℂ) = 1
    have hn0 : n x0 ≠ 0 := by
      intro h0
      exact hne (by rw [hn x0, h0]; norm_num)
    -- the restriction of `χ₀` is nonzero, so some `m x0 lam ≠ 0`
    have hresχ0 : Work.Induction.resFun K (χ₀ : W → ℂ)
        = ∑ lam ∈ Work.CharCore.Irr K,
            (Work.CharCore.cfInner (Work.Induction.resFun K (χ₀ : W → ℂ)) lam) • lam :=
      Work.CharCore.classFun_eq_sum_irr
        (Work.Induction.isClassFun_resFun (Work.CharCore.isClassFun_of_mem_Irr hχ₀))
    have hne0 : Work.Induction.resFun K (χ₀ : W → ℂ) ≠ 0 := by
      intro hzero
      have h1 : χ₀ (1 : W) = 0 := by
        have := congrFun hzero (1 : ↥K)
        simpa using this
      have hthis : (Work.CharCore.irrDeg χ₀ : ℂ) = 0 := by
        rw [← Work.CharCore.irrDeg_spec hχ₀]; exact h1
      exact Work.CharCore.irrDeg_ne_zero hχ₀ hthis
    have hexists : ∃ lam : ↥(Work.CharCore.Irr K), m x0 lam ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hne0
      rw [hresχ0]
      apply Finset.sum_eq_zero
      intro lam hlam
      have hz : Work.CharCore.cfInner (Work.Induction.resFun K (χ₀ : W → ℂ)) lam = 0 := by
        rw [hm x0 ⟨lam, hlam⟩, hcon ⟨lam, hlam⟩]
        simp
      rw [hz, zero_smul]
    obtain ⟨lam0, hlam0⟩ := hexists
    have hle : n x0 * m x0 lam0 ≤ 1 := by
      rw [← hcount lam0]
      exact Finset.single_le_sum (s := Finset.univ)
        (f := fun χ : ↥(Work.CharCore.Irr W) => n χ * m χ lam0)
        (fun i _ => Nat.zero_le _) (Finset.mem_univ x0)
    have hn1 : 1 ≤ n x0 := Nat.one_le_iff_ne_zero.mpr hn0
    have hm1 : 1 ≤ m x0 lam0 := Nat.one_le_iff_ne_zero.mpr hlam0
    have hle' : n x0 ≤ 1 := by
      have hstep : n x0 ≤ n x0 * m x0 lam0 := by
        calc n x0 = n x0 * 1 := (Nat.mul_one _).symm
          _ ≤ n x0 * m x0 lam0 := Nat.mul_le_mul_left _ hm1
      exact le_trans hstep hle
    have hnx0 : n x0 = 1 := le_antisymm hle' hn1
    rw [hn x0, hnx0]
    norm_num

end Work.NormalComplement
