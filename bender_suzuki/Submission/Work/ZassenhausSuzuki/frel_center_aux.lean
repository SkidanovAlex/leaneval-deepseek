import Mathlib
import Submission.Work.ZassenhausSuzuki.CoreV3
import Submission.Work.ZassenhausSuzuki.suzukiFProp
import Submission.Work.ZassenhausSuzuki.frel_torus_all
import Submission.Work.ZassenhausSuzuki.twoPoint_card_eq_involutions
import Submission.Work.ZassenhausSuzuki.twoPoint_inverted
import Submission.Work.ZassenhausPSL2.ZData.dStab_fpf_on_Q
import Submission.Work.ThmF.ChV12.structureIdentity
import Submission.Work.RankOneUniqueness.f_exists
import Submission.Work.RankOneUniqueness.f_unique
import Submission.Work.ZassenhausSuzuki.SzA.mem_center_iff
import Submission.Work.ZassenhausSuzuki.SzA.sq_eq
import Submission.Work.ZassenhausSuzuki.unitMulTheta

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `frel_center_aux`: the shared lower layers of `frel_center`

This module holds everything that the two sibling modules
`Submission/Work/ZassenhausSuzuki/frel_center.lean` (the target `frel_center`, BG 5.20 (a)) and
the ported lemmas about the *structure-identity pair* need, so that those ports can be built
without an import cycle:

* the structure-identity pair `structPair` of Peterfalvi II Ch. V §2 Lemma 1 b)
  (`t s t = ρ t ρ⁻¹`) with its elementary properties (`structPair_spec`, `structPair_fst_sq`,
  …), and the explicit coordinate lemmas in `A(K,θ)`;
* **`frel_center_of_structure`** — the reduction of BG 5.20 (a) to the value of `f` at the
  structure element `ρ`: if `e ρ` is `Λ`-conjugate to `⟨1,0⟩⁻¹ = ⟨1,1⟩`, then
  `f ⟨0,b⟩ = ⟨ν · b / θ b, 0⟩` for a single `ν ∈ Kˣ`, because the whole centre is the
  `D`-orbit of the structure involution `s` (`t s t = ρ t ρ⁻¹`), on which `f` is computed by
  the torus equivariance (`Work.ZassenhausSuzuki.frel_torus_all`);
* `structPair_conj_st`, `odd_orderOf_struct_st` (HB XI 10.6 (c)) and
  `structure_value_of_normalized` — the normalisation that reduces `structure_value` to the
  case `e s = ⟨0,1⟩`.
-/

namespace Work.ZassenhausSuzuki

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-- The structure-identity pair `(s, ρ)` of Peterfalvi II Ch. V §2 Lemma 1 b)
(`Work.ThmF.ChV12.structureIdentity`): `s ∈ Inv(Q)` is the distinguished involution and
`ρ ∈ Q` satisfies `t s t = ρ t ρ⁻¹`. -/
noncomputable def structPair (hsplit : IsSplitRankOne H Q t) : G × G :=
  (Work.ThmF.ChV12.structureIdentity (Work.ThmF.IsSplitRankOne.toData hsplit)).choose

/-- The defining property of the structure-identity pair. -/
theorem structPair_spec (hsplit : IsSplitRankOne H Q t) :
    (structPair hsplit).1 ∈ Q ∧ orderOf (structPair hsplit).1 = 2 ∧
      (structPair hsplit).2 ∈ Q ∧
      t * (structPair hsplit).1 * t⁻¹ = (structPair hsplit).2 * t * (structPair hsplit).2⁻¹ :=
  (Work.ThmF.ChV12.structureIdentity (Work.ThmF.IsSplitRankOne.toData hsplit)).choose_spec.1

/-- `t` is an involution. -/
theorem ht_mul_self (hsplit : IsSplitRankOne H Q t) : t * t = 1 := by
  have h2 := pow_orderOf_eq_one t
  rw [hsplit.invol] at h2
  simpa [pow_two] using h2

/-- The structure involution is not `1`. -/
theorem structPair_fst_ne_one (hsplit : IsSplitRankOne H Q t) : (structPair hsplit).1 ≠ 1 := by
  intro h
  have h2 := (structPair_spec hsplit).2.1
  rw [h, orderOf_one] at h2
  exact absurd h2 (by norm_num)

/-- The structure involution is an involution. -/
theorem structPair_fst_sq (hsplit : IsSplitRankOne H Q t) :
    (structPair hsplit).1 * (structPair hsplit).1 = 1 := by
  have h' := pow_orderOf_eq_one (structPair hsplit).1
  rw [(structPair_spec hsplit).2.1] at h'
  simpa [pow_two] using h'

/-- The structure element is not `1`. -/
theorem structPair_snd_ne_one (hsplit : IsSplitRankOne H Q t) : (structPair hsplit).2 ≠ 1 := by
  intro h1
  have hsQ := (structPair_spec hsplit).1
  have hspec := (structPair_spec hsplit).2.2.2
  have htm : t * t = 1 := ht_mul_self hsplit
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htm
  rw [h1] at hspec
  simp only [mul_one, inv_one] at hspec
  have hst : t * (structPair hsplit).1 * t = t := by simpa [hti] using hspec
  have hs_eq_t : (structPair hsplit).1 = t := by
    have h2 : t * (structPair hsplit).1 = t * t := by
      calc t * (structPair hsplit).1 = t * (structPair hsplit).1 * (t * t) := by
            rw [htm, mul_one]
        _ = (t * (structPair hsplit).1 * t) * t := by group
        _ = t * t := by rw [hst]
    exact mul_left_cancel h2
  exact hsplit.not_mem (hsplit.le (hs_eq_t ▸ hsQ))

/-! ## Explicit coordinate lemmas in `A(K,θ)` -/

/-- `⟨1,1⟩·⟨1,0⟩ = 1` in `A(K,θ)`. -/
theorem hLam_one_one_mul_one_zero {K : Type} [Field K] [CharP K 2] (θ : K ≃+* K) :
    (⟨1, 1⟩ : SzA K θ) * (⟨1, 0⟩ : SzA K θ) = 1 := by
  ext <;> simp [SzA.mul_a, SzA.mul_b, SzA.one_a, SzA.one_b, CharTwo.add_self_eq_zero]

/-- `⟨1,1⟩ = ⟨1,0⟩⁻¹`. -/
theorem hLam_inv_one_one {K : Type} [Field K] [CharP K 2] (θ : K ≃+* K) :
    (⟨1, 1⟩ : SzA K θ) = (⟨1, 0⟩ : SzA K θ)⁻¹ := by
  ext <;> simp [SzA.inv_a, SzA.inv_b, CharTwo.neg_eq]

/-- `h_λ ⟨1,0⟩ = ⟨λ,0⟩`. -/
theorem hLam_apply_one_zero {K : Type} [Field K] (θ : K ≃+* K) (μ : Kˣ) :
    SzA.hLam θ (μ : K) (⟨1, 0⟩ : SzA K θ) = ⟨(μ : K), 0⟩ := by
  ext <;> simp [SzA.hLam]

/-- `(h_λ ⟨1,1⟩)⁻¹ = ⟨λ,0⟩`. -/
theorem hLam_one_one_inv {K : Type} [Field K] [CharP K 2] (θ : K ≃+* K) (μ : Kˣ) :
    (SzA.hLam θ (μ : K) (⟨1, 1⟩ : SzA K θ))⁻¹ = (⟨(μ : K), 0⟩ : SzA K θ) := by
  ext <;> simp [SzA.hLam, SzA.inv_a, SzA.inv_b, CharTwo.neg_eq, CharTwo.add_self_eq_zero]

/-- An element of `A(K,θ)` whose square is `1` has zero first coordinate. -/
theorem a_eq_zero_of_sq_eq_one {K : Type} [Field K] [CharP K 2] (θ : K ≃+* K)
    (x : SzA K θ) (hx : x * x = 1) : x.a = 0 := by
  have h : (⟨0, x.a * θ x.a⟩ : SzA K θ) = 1 := by
    rw [← SzA.sq_eq θ x]; exact hx
  have hb : x.a * θ x.a = 0 := by simpa using congrArg SzA.b h
  rcases mul_eq_zero.mp hb with h0 | h0
  · exact h0
  · exact θ.injective (by rw [h0, map_zero])

/-- `θ b ≠ 0` for `b ≠ 0`. -/
theorem theta_ne_zero {K : Type} [Field K] (θ : K ≃+* K) {b : K} (hb : b ≠ 0) :
    θ b ≠ 0 := fun h => hb (θ.injective (by simpa using h))

/-- **The reduction.**  If the structure-identity element `ρ` has coordinates in the
`Λ`-orbit of `⟨1,1⟩ = ⟨1,0⟩⁻¹`, then the claim holds. -/
theorem frel_center_of_structure (hsplit : IsSplitRankOne H Q t) (hzass : IsZassenhaus H)
    {K : Type} [Field K] [CharP K 2] {θ : K ≃+* K} (hθ : IsTitsTheta θ)
    (e : Q ≃* SzA K θ) (htorus : TorusCoords K θ H Q t e)
    (hρ : ∃ μ : Kˣ, e (⟨(structPair hsplit).2, (structPair_spec hsplit).2.2.1⟩ : Q)
      = SzA.hLam θ (μ : K) (⟨1, 1⟩ : SzA K θ)) :
    ∃ ν : Kˣ, ∀ b : K, b ≠ 0 →
      Work.RankOneUniqueness.FRel H t
        (((e.symm (⟨0, b⟩ : SzA K θ)) : Q) : G)
        (((e.symm (⟨ν * b / θ b, 0⟩ : SzA K θ)) : Q) : G) := by
  classical
  obtain ⟨μ, hμ⟩ := hρ
  obtain ⟨hsQ, hs2, hρQ, hstruct⟩ := structPair_spec hsplit
  have htm : t * t = 1 := ht_mul_self hsplit
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htm
  -- `s` is an involution, so in the coordinates `e` it reads `⟨0,b₀⟩`
  have hsq : (⟨(structPair hsplit).1, hsQ⟩ : Q) * ⟨(structPair hsplit).1, hsQ⟩ = 1 := by
    apply Subtype.ext
    show (structPair hsplit).1 * (structPair hsplit).1 = ((1 : Q) : G)
    rw [structPair_fst_sq hsplit]
    rfl
  have hsa : (e ⟨(structPair hsplit).1, hsQ⟩).a = 0 := by
    refine a_eq_zero_of_sq_eq_one θ _ ?_
    rw [← map_mul, hsq, map_one]
  set b₀ : K := (e ⟨(structPair hsplit).1, hsQ⟩).b with hb₀
  have hes : e ⟨(structPair hsplit).1, hsQ⟩ = (⟨0, b₀⟩ : SzA K θ) := by
    ext <;> simp [hsa, hb₀]
  have hb₀ne : b₀ ≠ 0 := by
    intro h0
    have h1 : e ⟨(structPair hsplit).1, hsQ⟩ = 1 := by rw [hes, h0]; rfl
    have h2 : (⟨(structPair hsplit).1, hsQ⟩ : Q) = 1 :=
      (MulEquiv.injective e) (by rw [h1, map_one])
    exact structPair_fst_ne_one hsplit (Subtype.ext_iff.mp h2)
  -- `FRel s ρ⁻¹`
  have hsfrel : Work.RankOneUniqueness.FRel H t ((structPair hsplit).1)
      ((structPair hsplit).2)⁻¹ := by
    refine ⟨(structPair hsplit).2, hsplit.le hρQ, ?_⟩
    calc t * (structPair hsplit).1 * t
        = t * (structPair hsplit).1 * t⁻¹ := by rw [hti]
      _ = (structPair hsplit).2 * t * (structPair hsplit).2⁻¹ := hstruct
  -- `e (ρ⁻¹) = ⟨μ,0⟩`
  have hρinv : e ⟨((structPair hsplit).2)⁻¹, Q.inv_mem hρQ⟩ = (⟨(μ : K), 0⟩ : SzA K θ) := by
    have h1 : (⟨((structPair hsplit).2)⁻¹, Q.inv_mem hρQ⟩ : Q)
        = (⟨(structPair hsplit).2, hρQ⟩ : Q)⁻¹ := rfl
    rw [h1, map_inv, hμ, hLam_one_one_inv θ μ]
  -- the `λ` with `λ·θλ = b / b₀`
  refine ⟨Units.mk0 ((μ : K) * θ b₀ / b₀) (div_ne_zero (mul_ne_zero (Units.ne_zero μ)
    (theta_ne_zero θ hb₀ne)) hb₀ne), fun b hb => ?_⟩
  obtain ⟨lam, hlam⟩ := exists_unit_mul_theta hθ (Units.mk0 (b / b₀) (div_ne_zero hb hb₀ne))
  have hlam' : (lam : K) * θ (lam : K) = b / b₀ := hlam
  have hlam'' : (lam : K) * θ (lam : K) * b₀ = b := by
    rw [hlam', div_mul_cancel₀ _ hb₀ne]
  -- the torus equivariance
  have hmain := frel_torus_all hsplit hzass hθ e htorus (lam := lam)
    (x := (⟨(structPair hsplit).1, hsQ⟩ : Q)) (y := (⟨((structPair hsplit).2)⁻¹,
      Q.inv_mem hρQ⟩ : Q)) hsfrel
  -- the first argument of `hmain` is `e.symm ⟨0,b⟩`
  have hA : (e.symm (SzA.hLam θ (lam : K) (e (⟨(structPair hsplit).1, hsQ⟩ : Q))) : Q)
      = e.symm (⟨0, b⟩ : SzA K θ) := by
    congr 1
    rw [hes, SzA.hLam]
    ext <;> simp [hlam'']
  rw [hA] at hmain
  -- the field identity `λ⁻¹μ = ν·b/θb`
  have hθlam : θ (lam : K) ≠ 0 := theta_ne_zero θ (Units.ne_zero lam)
  have hθb : θ b ≠ 0 := theta_ne_zero θ hb
  have hfield : (lam : K)⁻¹ * (μ : K)
      = ((μ : K) * θ b₀ / b₀) * b / θ b := by
    have hb_eq : b = (lam : K) * θ (lam : K) * b₀ := hlam''.symm
    have hθb_eq : θ b = θ (lam : K) * (lam : K) ^ 2 * θ b₀ := by
      rw [hb_eq, map_mul, map_mul, hθ.2]
    rw [hθb_eq, hb_eq]
    have hθb₀ne : θ b₀ ≠ 0 := theta_ne_zero θ hb₀ne
    field_simp
  -- the second argument of `hmain` is `e.symm ⟨ν·b/θb, 0⟩`
  have hB : (e.symm (SzA.hLam θ (((lam⁻¹ : Kˣ)) : K) (e (⟨((structPair hsplit).2)⁻¹,
        Q.inv_mem hρQ⟩ : Q))) : Q) = e.symm (⟨((Units.mk0 ((μ : K) * θ b₀ / b₀)
          (div_ne_zero (mul_ne_zero (Units.ne_zero μ) (theta_ne_zero θ hb₀ne))
            hb₀ne) : Kˣ) : K) * b / θ b, 0⟩ : SzA K θ) := by
    congr 1
    rw [hρinv, SzA.hLam]
    ext <;> simp [hfield]
  rw [hB] at hmain
  exact hmain

/-- **HB XI 10.6 (c)** in our framework.  The structure element conjugates `s * t` to its
square; the only inputs are the structure identity `t s t = ρ t ρ⁻¹` and the centrality of `s`
in `Q` (available from the coordinates of `s`: it is an involution of `A(K,θ)`). -/
theorem structPair_conj_st (hsplit : IsSplitRankOne H Q t) {K : Type} [Field K] [CharP K 2]
    {θ : K ≃+* K} (e : Q ≃* SzA K θ)
    (hsa : (e ⟨(structPair hsplit).1, (structPair_spec hsplit).1⟩).a = 0) :
    (structPair hsplit).2 * ((structPair hsplit).1 * t) * (structPair hsplit).2⁻¹
      = ((structPair hsplit).1 * t) * ((structPair hsplit).1 * t) := by
  obtain ⟨hsQ, hs2, hρQ, hstruct⟩ := structPair_spec hsplit
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right (ht_mul_self hsplit)
  have hcommG : (structPair hsplit).1 * (structPair hsplit).2
      = (structPair hsplit).2 * (structPair hsplit).1 := by
    have h2 : e ⟨(structPair hsplit).1, hsQ⟩
        = (⟨0, (e ⟨(structPair hsplit).1, hsQ⟩).b⟩ : SzA K θ) := by
      ext <;> simp [hsa]
    have hcen : (⟨(structPair hsplit).1, hsQ⟩ : Q) * ⟨(structPair hsplit).2, hρQ⟩
        = ⟨(structPair hsplit).2, hρQ⟩ * ⟨(structPair hsplit).1, hsQ⟩ := by
      apply e.injective
      rw [map_mul, map_mul, h2]
      ext <;> simp [add_comm]
    simpa using congrArg (fun z : Q => (z : G)) hcen
  have hst : t * (structPair hsplit).1 * t
      = (structPair hsplit).2 * t * (structPair hsplit).2⁻¹ := by
    rw [← hstruct, hti]
  calc (structPair hsplit).2 * ((structPair hsplit).1 * t) * (structPair hsplit).2⁻¹
      = (structPair hsplit).1 * (structPair hsplit).2 * t * (structPair hsplit).2⁻¹ := by
        rw [hcommG]
        group
    _ = (structPair hsplit).1
          * ((structPair hsplit).2 * t * (structPair hsplit).2⁻¹) := by group
    _ = (structPair hsplit).1 * (t * (structPair hsplit).1 * t) := by rw [← hst]
    _ = ((structPair hsplit).1 * t) * ((structPair hsplit).1 * t) := by group

/-- **HB XI 10.6 (c).**  `s * t` has odd order: it follows from `ρ (s * t) ρ⁻¹ = (s * t) ^ 2`,
since conjugation preserves the order and `orderOf (w ^ 2) = orderOf w / gcd (orderOf w) 2`. -/
theorem odd_orderOf_struct_st (hsplit : IsSplitRankOne H Q t) {K : Type} [Field K] [CharP K 2]
    {θ : K ≃+* K} (e : Q ≃* SzA K θ)
    (hsa : (e ⟨(structPair hsplit).1, (structPair_spec hsplit).1⟩).a = 0) :
    Odd (orderOf ((structPair hsplit).1 * t)) := by
  have h := structPair_conj_st hsplit e hsa
  set w : G := (structPair hsplit).1 * t with hw
  set r : G := (structPair hsplit).2 with hr
  have hconj : orderOf (r * w * r⁻¹) = orderOf w := by
    rw [show r * w * r⁻¹ = (MulAut.conj r) w from (MulAut.conj_apply r w).symm]
    exact orderOf_injective (MulAut.conj r).toMonoidHom (MulAut.conj r).injective w
  rw [h] at hconj
  have hpow : orderOf (w * w) = orderOf w / Nat.gcd (orderOf w) 2 := by
    rw [← pow_two, orderOf_pow]
  rw [hpow] at hconj
  have hpos : 0 < orderOf w := orderOf_pos w
  have hdvd : Nat.gcd (orderOf w) 2 ∣ orderOf w := Nat.gcd_dvd_left _ _
  have h3 : orderOf w / Nat.gcd (orderOf w) 2 = orderOf w := hconj
  have hd1 : Nat.gcd (orderOf w) 2 = 1 := by
    have h4 : orderOf w * Nat.gcd (orderOf w) 2 = orderOf w := by
      conv_rhs => rw [← Nat.div_mul_cancel hdvd, h3]
    exact Nat.eq_of_mul_eq_mul_left hpos (by rw [h4, mul_one])
  rw [← Nat.not_even_iff_odd]
  intro hEven
  have h2 : Nat.gcd (orderOf w) 2 = 2 := Nat.gcd_eq_right (even_iff_two_dvd.mp hEven)
  omega

/-- **Normalisation for `structure_value`.**  The claim `e ρ ∈ Λ·⟨1,1⟩` is invariant under
`D`-twists `e ↦ h_μ ∘ e` of the coordinates (which preserve `TorusCoords`), so it suffices to
prove it in the normalised form `e s = ⟨0,1⟩ ⟹ e ρ = ⟨1,1⟩`. -/
theorem structure_value_of_normalized (hsplit : IsSplitRankOne H Q t) (hzass : IsZassenhaus H)
    {K : Type} [Field K] [CharP K 2] {θ : K ≃+* K} (hθ : IsTitsTheta θ)
    (e : Q ≃* SzA K θ) (htorus : TorusCoords K θ H Q t e)
    (h : ∀ (e' : Q ≃* SzA K θ), TorusCoords K θ H Q t e' →
      e' (⟨(structPair hsplit).1, (structPair_spec hsplit).1⟩ : Q) = (⟨0, 1⟩ : SzA K θ) →
      e' (⟨(structPair hsplit).2, (structPair_spec hsplit).2.2.1⟩ : Q) = (⟨1, 1⟩ : SzA K θ)) :
    ∃ μ : Kˣ, e (⟨(structPair hsplit).2, (structPair_spec hsplit).2.2.1⟩ : Q)
      = SzA.hLam θ (μ : K) (⟨1, 1⟩ : SzA K θ) := by
  classical
  obtain ⟨hsQ, hs2, hρQ, -⟩ := structPair_spec hsplit
  have hsa : (e ⟨(structPair hsplit).1, hsQ⟩).a = 0 := by
    refine a_eq_zero_of_sq_eq_one θ _ ?_
    have hsq : (⟨(structPair hsplit).1, hsQ⟩ : Q) * ⟨(structPair hsplit).1, hsQ⟩ = 1 := by
      apply Subtype.ext
      show (structPair hsplit).1 * (structPair hsplit).1 = ((1 : Q) : G)
      rw [structPair_fst_sq hsplit]
      rfl
    rw [← map_mul, hsq, map_one]
  set b₀ : K := (e ⟨(structPair hsplit).1, hsQ⟩).b with hb₀
  have hes : e ⟨(structPair hsplit).1, hsQ⟩ = (⟨0, b₀⟩ : SzA K θ) := by
    ext <;> simp [hsa, hb₀]
  have hb₀ne : b₀ ≠ 0 := by
    intro h0
    have h1 : e ⟨(structPair hsplit).1, hsQ⟩ = 1 := by rw [hes, h0]; rfl
    have h2 : (⟨(structPair hsplit).1, hsQ⟩ : Q) = 1 :=
      (MulEquiv.injective e) (by rw [h1, map_one])
    exact structPair_fst_ne_one hsplit (Subtype.ext_iff.mp h2)
  -- the twist `μ` with `μ·θμ·b₀ = 1`
  obtain ⟨μ, hμ⟩ := exists_unit_mul_theta hθ (Units.mk0 b₀ hb₀ne)⁻¹
  have hμb : (μ : K) * θ (μ : K) * b₀ = 1 := by
    have h1 : (μ : K) * θ (μ : K) = (b₀)⁻¹ := hμ
    rw [h1, inv_mul_cancel₀ hb₀ne]
  -- the twisted coordinates
  have ht' : TorusCoords K θ H Q t (e.trans (SzA.hLamHom θ μ)) := torusCoords_twist htorus μ
  have hes' : (e.trans (SzA.hLamHom θ μ)) (⟨(structPair hsplit).1, hsQ⟩ : Q)
      = (⟨0, 1⟩ : SzA K θ) := by
    rw [MulEquiv.trans_apply, SzA.hLamHom_apply, hes, SzA.hLam]
    ext <;> simp [hμb]
  have hρ' := h (e.trans (SzA.hLamHom θ μ)) ht' hes'
  -- undo the twist: `h_μ (e ρ) = ⟨1,1⟩`
  have hρ'' : SzA.hLam θ (μ : K) (e (⟨(structPair hsplit).2,
      (structPair_spec hsplit).2.2.1⟩ : Q)) = (⟨1, 1⟩ : SzA K θ) := by
    have hh := hρ'
    rwa [MulEquiv.trans_apply, SzA.hLamHom_apply] at hh
  refine ⟨μ⁻¹, ?_⟩
  have hinv : SzA.hLam θ ((μ⁻¹ : Kˣ) : K) (SzA.hLam θ (μ : K)
      (e (⟨(structPair hsplit).2, (structPair_spec hsplit).2.2.1⟩ : Q)))
      = e (⟨(structPair hsplit).2, (structPair_spec hsplit).2.2.1⟩ : Q) := by
    rw [← SzA.hLam_mul]
    have h1 : ((μ⁻¹ : Kˣ) : K) * (μ : K) = 1 := by simp
    rw [h1, SzA.hLam_one]
  rw [← hinv, hρ'']


end Work.ZassenhausSuzuki
