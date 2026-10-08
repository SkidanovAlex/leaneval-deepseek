import Mathlib
import Submission.Work.CharCore.Defs
import Submission.Work.CharCore.vchar_norm_one
import Submission.Work.CharCore.irr_orthonormal
import Submission.Work.CharCore.classFun_eq_sum_irr
import Submission.Work.CharCore.Coherence
import Submission.Work.CharCore.irrDeg_eq_one_of_commutative
import Submission.Work.Induction.Defs
import Submission.Work.Induction.Basic
import Submission.Work.Induction.indFun_apply_one
import Submission.Work.Induction.frobenius_reciprocity
import Submission.Work.Induction.isVChar_indFun
import Submission.Work.Clifford.All
import Submission.Work.Frobenius.Induced.conjChar_ne_self_of_fpf
import Submission.Work.Frobenius.Bridge.isVChar_iff_coherence

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement

open Classical

/-! ## `Work.CharCore`-vocabulary restatements of the induction lemmas

The induction library states its results for `Work.Induction.indFun`/`resFun`, which are
*definitionally* but not *syntactically* equal to the `Work.CharCore` versions used in the
statements below.  These restatements let `rw` fire. -/

/-- `Work.CharCore`-vocabulary form of `Work.Induction.indFun_apply_one`. -/
theorem indFun_apply_one_cc {G : Type*} [Group G] [Fintype G] (H : Subgroup G) (φ : H → ℂ) :
    Work.CharCore.indFun H φ 1 = (H.index : ℂ) * φ 1 :=
  Work.Induction.indFun_apply_one H φ

/-- `Work.CharCore`-vocabulary form of `Work.Induction.frobenius_reciprocity`. -/
theorem frobenius_reciprocity_cc {G : Type*} [Group G] [Fintype G] (H : Subgroup G) (φ : H → ℂ)
    (ψ : G → ℂ) (hψ : Work.CharCore.IsClassFun ψ) :
    Work.CharCore.cfInner (Work.CharCore.indFun H φ) ψ
      = Work.CharCore.cfInner φ (Work.CharCore.resFun H ψ) :=
  Work.Induction.frobenius_reciprocity H φ ψ hψ

/-- `Work.CharCore`-vocabulary form of `Work.Induction.isVChar_indFun`. -/
theorem isVChar_indFun_cc {G : Type*} [Group G] [Fintype G] {H : Subgroup G} {φ : H → ℂ}
    (hφ : Work.CharCore.IsVChar φ) :
    Work.CharCore.IsVChar (Work.CharCore.indFun H φ) :=
  Work.Induction.isVChar_indFun hφ

/-! ## Auxiliary lemmas about a Frobenius kernel `K` with `C_L(k) = K` for `k ∈ K^#` -/

/-- **Fixed-point-free conjugation fixes no non-principal irreducible character.**
Let `K` be a normal subgroup of a finite group `L` such that `C_L(k) = K` for every
`1 ≠ k ∈ K`.  Then for every `t ∉ K`, the conjugate `θ^t` of a non-principal irreducible
character `θ` of `K` is different from `θ`.

This is the restriction to the present situation of
`Work.Frobenius.Induced.conjChar_ne_self_of_fpf`, which needs the fixed-point-freeness
`∀ k ∈ K, t * k * t⁻¹ = k → k = 1` together with `θ ∈ Work.Frobenius.Irr K`; the bridge
`Work.CharCore.mem_Irr_iff_coherence` / `Work.Frobenius.Bridge.mem_Irr_bridge` supplies the
latter, and `Work.Frobenius.Induced.conjChar K t θ` is definitionally
`Work.Clifford.conjFun K t θ`. -/
theorem conjFun_ne_self_of_notMem {L : Type*} [Group L] [Fintype L] {K : Subgroup L} [K.Normal]
    (hKc : ∀ k ∈ K, k ≠ 1 → Subgroup.centralizer ({k} : Set L) = K)
    {θ : K → ℂ} (hθ : θ ∈ Work.CharCore.Irr K) (hθ1 : θ ≠ 1)
    {t : L} (ht : t ∉ K) : Work.Clifford.conjFun K t θ ≠ θ := by
  have hθf : θ ∈ Work.Frobenius.Irr K :=
    (Work.Frobenius.Bridge.mem_Irr_bridge (G := K)).mpr
      ((Work.CharCore.mem_Irr_iff_coherence (G := K)).mp hθ)
  have hfpf : ∀ k : L, k ∈ K → t * k * t⁻¹ = k → k = 1 := by
    intro k hk hfix
    by_contra hk1
    have hmem : t ∈ Subgroup.centralizer ({k} : Set L) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hfix)
    rw [hKc k hk hk1] at hmem
    exact ht hmem
  exact Work.Frobenius.Induced.conjChar_ne_self_of_fpf hθf hθ1 hfpf

/-- **The inertia group of a non-principal character of the kernel is the kernel.**
Under the hypotheses of `conjFun_ne_self_of_notMem`, `I_L(θ) = K` for every non-principal
`θ ∈ Irr K`: it contains `K` because `θ` is a class function, and it is contained in `K` by
`conjFun_ne_self_of_notMem`. -/
theorem inertia_eq_of_hKc {L : Type*} [Group L] [Fintype L] {K : Subgroup L} [K.Normal]
    (hKc : ∀ k ∈ K, k ≠ 1 → Subgroup.centralizer ({k} : Set L) = K)
    {θ : K → ℂ} (hθ : θ ∈ Work.CharCore.Irr K) (hθ1 : θ ≠ 1) :
    Work.Clifford.inertia K θ = K := by
  refine le_antisymm ?_ (Work.Clifford.le_inertia_of_mem_Irr
    ((Work.Clifford.mem_Irr_charCore_iff (G := K)).mpr hθ))
  intro t ht
  by_contra htnK
  exact conjFun_ne_self_of_notMem hKc hθ hθ1 htnK ((Work.Clifford.mem_inertia K θ t).mp ht)

/-- **Norm of the induced character.**  With `I_L(θ) = K`, the inner product
`⟪Ind_K^L θ, Ind_K^L θ⟫_L` equals `1`. -/
theorem cfInner_indFun_self_eq_one {L : Type*} [Group L] [Fintype L] {K : Subgroup L} [K.Normal]
    {θ : K → ℂ} (hθ : θ ∈ Work.CharCore.Irr K)
    (hI : Work.Clifford.inertia K θ = K) :
    Work.CharCore.cfInner (Work.CharCore.indFun K θ) (Work.CharCore.indFun K θ) = 1 := by
  have hCl : θ ∈ Work.Clifford.Irr K := (Work.Clifford.mem_Irr_charCore_iff (G := K)).mpr hθ
  have hc : Work.CharCore.cfInner (Work.CharCore.indFun K θ) (Work.CharCore.indFun K θ)
      = (Nat.card ↥(Work.Clifford.inertia K θ) : ℂ) * (Nat.card ↥K : ℂ)⁻¹ :=
    Work.Clifford.cfInner_indFun_normal (H := L) (N := K) hCl
  rw [hI] at hc
  rw [hc]
  refine mul_inv_cancel₀ ?_
  rw [Nat.card_eq_fintype_card]
  exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero

/-- **`Ind_K^L θ` is irreducible** for a non-principal `θ ∈ Irr K`.  Its norm is `1`
(`cfInner_indFun_self_eq_one`) and it is a virtual character, so by
`Work.CharCore.vchar_norm_one` it is `±` an irreducible character; positivity of the degree
rules out the negative sign. -/
theorem indFun_mem_Irr_of_hKc {L : Type*} [Group L] [Fintype L] {K : Subgroup L} [K.Normal]
    (hKc : ∀ k ∈ K, k ≠ 1 → Subgroup.centralizer ({k} : Set L) = K)
    {θ : K → ℂ} (hθ : θ ∈ Work.CharCore.Irr K) (hθ1 : θ ≠ 1) :
    Work.CharCore.indFun K θ ∈ Work.CharCore.Irr L := by
  have hI : Work.Clifford.inertia K θ = K := inertia_eq_of_hKc hKc hθ hθ1
  have hnorm : Work.CharCore.cfInner (Work.CharCore.indFun K θ) (Work.CharCore.indFun K θ) = 1 :=
    cfInner_indFun_self_eq_one hθ hI
  have hV : Work.CharCore.IsVChar (Work.CharCore.indFun K θ) :=
    isVChar_indFun_cc (Work.CharCore.IsVChar.of_mem_Irr hθ)
  obtain ⟨χ, hχ, hcase⟩ := Work.CharCore.vchar_norm_one hV hnorm
  rcases hcase with h | h
  · rw [h]; exact hχ
  · exfalso
    have h1 := congrFun h 1
    rw [indFun_apply_one_cc, Work.CharCore.irrDeg_spec hθ, Pi.neg_apply,
      Work.CharCore.irrDeg_spec hχ] at h1
    have h2 : ((K.index * Work.CharCore.irrDeg θ + Work.CharCore.irrDeg χ : ℕ) : ℂ) = 0 := by
      push_cast
      rw [h1]; ring
    have h3 : K.index * Work.CharCore.irrDeg θ + Work.CharCore.irrDeg χ = 0 := by
      exact_mod_cast h2
    have hθpos := Work.CharCore.irrDeg_pos hθ
    have hχpos := Work.CharCore.irrDeg_pos hχ
    omega

/-- **Degree of the induced character.**  For an abelian `K` and `θ ∈ Irr K`,
`Ind_K^L θ 1 = |L| / |K|`. -/
theorem indFun_apply_one_eq_card_div {L : Type*} [Group L] [Fintype L] {K : Subgroup L}
    (hKcomm : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a) {θ : K → ℂ}
    (hθ : θ ∈ Work.CharCore.Irr K) :
    Work.CharCore.indFun K θ 1 = (Nat.card L : ℂ) / (Nat.card K : ℂ) := by
  haveI : IsMulCommutative K :=
    IsMulCommutative.of_comm (fun a b => Subtype.ext (hKcomm a a.2 b b.2))
  have hdeg : θ 1 = 1 := by
    rw [Work.CharCore.irrDeg_spec hθ, Work.CharCore.irrDeg_eq_one_of_commutative hθ]
    norm_num
  have hidx : Work.CharCore.indFun K θ 1 = (K.index : ℂ) := by
    rw [indFun_apply_one_cc, hdeg, mul_one]
  rw [hidx]
  have hcard : Nat.card K * K.index = Nat.card L := Subgroup.card_mul_index K
  have hK0 : (Nat.card K : ℂ) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hL : (Nat.card L : ℂ) = (Nat.card K : ℂ) * (K.index : ℂ) := by
    rw [← Nat.cast_mul, hcard]
  rw [hL, mul_div_cancel_left₀ _ hK0]

/-- **The induced character vanishes off the kernel.**  For a normal subgroup `K ⊴ L`,
`Ind_K^L θ x = 0` for every `x ∉ K`: a conjugate `y * x * y⁻¹` lies in `K` only if `x` does,
so every summand of the defining sum vanishes. -/
theorem indFun_apply_eq_zero_of_notMem {L : Type*} [Group L] [Fintype L] {K : Subgroup L}
    [K.Normal]
    (θ : K → ℂ) {x : L} (hx : x ∉ K) : Work.CharCore.indFun K θ x = 0 := by
  apply Work.Induction.indFun_apply_eq_zero_of_not_conj
  intro y hy
  exact hx (by
    have h := (inferInstance : K.Normal).conj_mem (y * x * y⁻¹) hy y⁻¹
    have he : y⁻¹ * (y * x * y⁻¹) * (y⁻¹)⁻¹ = x := by group
    rwa [he] at h)

/-- **A non-constant class function has a non-principal irreducible constituent.**
Expanding `f = ∑_{χ ∈ Irr G} ⟪f, χ⟫ • χ` (`Work.CharCore.classFun_eq_sum_irr`), if every
non-principal `θ` satisfied `⟪f, θ⟫ = 0` then `f` would be a scalar multiple of the
constant-one function, hence constant. -/
theorem exists_mem_Irr_ne_one_cfInner_ne_zero {G : Type*} [Group G] [Fintype G] {f : G → ℂ}
    (hf : Work.CharCore.IsClassFun f) (hne : f ≠ fun _ => f 1) :
    ∃ θ ∈ Work.CharCore.Irr G, θ ≠ 1 ∧ Work.CharCore.cfInner f θ ≠ 0 := by
  by_contra hcon
  have hzero : ∀ θ ∈ Work.CharCore.Irr G, θ ≠ 1 → Work.CharCore.cfInner f θ = 0 := by
    intro θ hθ hθ1
    by_contra hc
    exact hcon ⟨θ, hθ, hθ1, hc⟩
  have hprincipal : (1 : G → ℂ) ∈ Work.CharCore.Irr G :=
    Work.CharCore.principalChar_mem_Irr
  have hsum : (∑ χ ∈ Work.CharCore.Irr G, (Work.CharCore.cfInner f χ) • χ)
      = (Work.CharCore.cfInner f 1) • (1 : G → ℂ) := by
    refine Finset.sum_eq_single (1 : G → ℂ) ?_ ?_
    · intro b hb hb1
      rw [hzero b hb hb1, zero_smul]
    · intro hnot
      exact absurd hprincipal hnot
  have hconst : f = (Work.CharCore.cfInner f 1) • (1 : G → ℂ) := by
    conv_lhs => rw [Work.CharCore.classFun_eq_sum_irr hf]
    rw [hsum]
  refine hne ?_
  funext x
  have h1 : f 1 = Work.CharCore.cfInner f 1 := by
    conv_lhs => rw [hconst]
    simp
  conv_lhs => rw [hconst]
  simp only [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
  exact h1.symm

/-- **Frobenius-group character theory for an abelian kernel with freely acting quotient.**

Let `L` be a finite group and `K ◁ L` a nontrivial abelian normal subgroup such that
`C_L(k) = K` for every `k ∈ K^#`.  Then every element of `L - K` acts fixed point freely on
`K#`, and:

* for every nonprincipal `θ ∈ Irr K`, the induced character `Ind_K^L θ` is irreducible, is not
  trivial on `K`, has degree `|L| / |K|`, and vanishes off `K`;
* conversely every irreducible character of `L` that is not trivial on `K` is induced from some
  nonprincipal irreducible of `K`. -/
theorem frobenius_kernel_irr {L : Type*} [Group L] [Fintype L] {K : Subgroup L}
    (hKn : K.Normal) (hKne : K ≠ ⊥)
    (hKc : ∀ k ∈ K, k ≠ 1 → Subgroup.centralizer ({k} : Set L) = K)
    (hKcomm : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a) :
    (∀ (theta : K → ℂ), theta ∈ Work.CharCore.Irr K → theta ≠ 1 →
      Work.CharCore.indFun K theta ∈ Work.CharCore.Irr L ∧
      (∃ k ∈ K, Work.CharCore.indFun K theta k ≠ Work.CharCore.indFun K theta 1) ∧
      Work.CharCore.indFun K theta 1 = ((Nat.card L : ℂ) / (Nat.card K : ℂ)) ∧
      (∀ x : L, x ∉ K → Work.CharCore.indFun K theta x = 0)) ∧
    (∀ chi : L → ℂ, chi ∈ Work.CharCore.Irr L → (∃ k ∈ K, chi k ≠ chi 1) →
      ∃ (theta : K → ℂ), theta ∈ Work.CharCore.Irr K ∧ theta ≠ 1 ∧
        chi = Work.CharCore.indFun K theta) := by
  letI : K.Normal := hKn
  constructor
  · intro theta htheta htheta1
    refine ⟨indFun_mem_Irr_of_hKc hKc htheta htheta1, ?_,
      indFun_apply_one_eq_card_div hKcomm htheta, ?_⟩
    · -- non-triviality on `K`, from the norm computation and Frobenius reciprocity
      by_contra hcon
      push Not at hcon
      have hI : Work.Clifford.inertia K theta = K := inertia_eq_of_hKc hKc htheta htheta1
      have hnorm : Work.CharCore.cfInner (Work.CharCore.indFun K theta)
          (Work.CharCore.indFun K theta) = 1 := cfInner_indFun_self_eq_one htheta hI
      have hclass : Work.CharCore.IsClassFun (Work.CharCore.indFun K theta) :=
        Work.CharCore.IsVChar.isClassFun
          (isVChar_indFun_cc (Work.CharCore.IsVChar.of_mem_Irr htheta))
      have hrec := frobenius_reciprocity_cc K theta (Work.CharCore.indFun K theta) hclass
      rw [hnorm] at hrec
      have hconst : Work.CharCore.resFun K (Work.CharCore.indFun K theta)
          = (Work.CharCore.indFun K theta 1) • (1 : K → ℂ) := by
        funext k
        rw [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
        exact hcon (k : L) k.2
      rw [hconst] at hrec
      rw [Work.CharCore.cfInner_smul_right] at hrec
      have hprincipal_mem : (1 : K → ℂ) ∈ Work.CharCore.Irr K :=
        Work.CharCore.principalChar_mem_Irr
      have hprincipal : Work.CharCore.cfInner theta (1 : K → ℂ) = 0 := by
        rw [Work.CharCore.irr_orthonormal theta 1 htheta hprincipal_mem, if_neg htheta1]
      rw [hprincipal, mul_zero] at hrec
      exact one_ne_zero hrec
    · intro x hx
      exact indFun_apply_eq_zero_of_notMem theta hx
  · intro chi hchi hkern
    have hcf : Work.CharCore.IsClassFun (Work.CharCore.resFun K chi) :=
      Work.Induction.isClassFun_resFun (Work.CharCore.isClassFun_of_mem_Irr hchi)
    have hne : Work.CharCore.resFun K chi ≠ fun _ => (Work.CharCore.resFun K chi) 1 := by
      intro hc
      obtain ⟨k, hkK, hkne⟩ := hkern
      have h2 := congrFun hc ⟨k, hkK⟩
      exact hkne (show chi k = chi 1 from h2)
    obtain ⟨theta, htheta, htheta1, hpair⟩ := exists_mem_Irr_ne_one_cfInner_ne_zero hcf hne
    refine ⟨theta, htheta, htheta1, ?_⟩
    have hirr : Work.CharCore.indFun K theta ∈ Work.CharCore.Irr L :=
      indFun_mem_Irr_of_hKc hKc htheta htheta1
    have hrec := frobenius_reciprocity_cc K theta chi
      (Work.CharCore.isClassFun_of_mem_Irr hchi)
    have hpair' : Work.CharCore.cfInner (Work.CharCore.indFun K theta) chi ≠ 0 := by
      rw [hrec]
      intro h0
      exact hpair (by
        have h2 := Work.CharCore.cfInner_conj_symm (Work.CharCore.resFun K chi) theta
        rw [h0] at h2
        simpa using h2)
    have heq : Work.CharCore.indFun K theta = chi := by
      by_contra hne'
      rw [Work.CharCore.irr_orthonormal _ _ hirr hchi, if_neg hne'] at hpair'
      exact hpair' rfl
    exact heq.symm

end Work.NormalComplement
