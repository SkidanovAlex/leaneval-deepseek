import Mathlib
import Submission.Work.Higman.MSA.l8_local
import Submission.Work.Higman.MSA.l8_BV
import Submission.Work.Higman.commutator_powSub_A_C
import Submission.Work.Higman.Fq_structure

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped commutatorElement

namespace Work.Higman.MSA.L8

variable {P : Type} [Group P] [Finite P]

/-- Conjugates of elements of `A ^ n` lie in `A ^ n`. -/
theorem conj_mem_powSub {A : Subgroup P} [hAn : A.Normal] (n : ℕ) (g : P) {δ : P}
    (hδ : δ ∈ powSub A n) : g * δ * g⁻¹ ∈ powSub A n := by
  have hAconj : A.map (MulAut.conj g).toMonoidHom = A :=
    Subgroup.normal_iff_map_conj_eq.mp hAn g
  have hmap := map_powSub (MulAut.conj g) hAconj n
  have hmem : (MulAut.conj g) δ ∈ (powSub A n).map (MulAut.conj g).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hδ
  rw [hmap] at hmem
  simpa [MulAut.conj_apply] using hmem

/-- The `2 ^ (e-2)`-nd power kills `A ^ 4`. -/
theorem pow_two_pow_sub_two_eq_one_of_mem_powSub_four {h : IsSuzuki2Grp P}
    {A C : Subgroup P} [hAn : A.Normal] (S : D h A C) {δ : P} (hδ : δ ∈ powSub A 4) :
    δ ^ 2 ^ (S.e - 2) = 1 := by
  have he : 2 ≤ S.e := S.he2
  obtain ⟨a, ha, rfl⟩ := (mem_powSub_iff S.hA.abelian).mp hδ
  rw [← pow_mul, show (4 : ℕ) * 2 ^ (S.e - 2) = 2 ^ S.e from by
    rw [show (4 : ℕ) = 2 ^ 2 from by norm_num, ← pow_add]; congr 1; omega]
  exact S.he1 a ha

/-- If `α, β ∈ A` and `α ≡ β` mod `A ^ 4`, then the `2 ^ (e-2)`-nd powers agree. -/
theorem pow_eq_of_mul_inv_mem_powSub_four {h : IsSuzuki2Grp P} {A C : Subgroup P}
    [hAn : A.Normal] (S : D h A C) {α β : P} (hα : α ∈ A) (hβ : β ∈ A)
    (h : α * β⁻¹ ∈ powSub A 4) :
    α ^ 2 ^ (S.e - 2) = β ^ 2 ^ (S.e - 2) := by
  have hδA : α * β⁻¹ ∈ A := powSub_le (by norm_num) h
  have heq : α = β * (α * β⁻¹) := by
    have hc : β * α = α * β := S.hA.abelian β hβ α hα
    rw [← mul_assoc, hc, mul_assoc, mul_inv_cancel, mul_one]
  have hcβδ : Commute β (α * β⁻¹) := S.hA.abelian β hβ (α * β⁻¹) hδA
  rw [heq, Commute.mul_pow hcβδ (2 ^ (S.e - 2)),
    pow_two_pow_sub_two_eq_one_of_mem_powSub_four S h, mul_one]

/-- Two lifts of `w ∈ Ω₁(P)` in `A` differ by an element of `A ^ 2`. -/
theorem liftA_congr {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal] (S : D h A C)
    {w : ↥(omega1 P)} {a : ↥A} (ha : (a : P) ^ 2 ^ (S.e - 1) = (w : P)) :
    ((liftA S w : ↥A) : P) * (a : P)⁻¹ ∈ powSub A 2 := by
  have hmem : ((liftA S w : ↥A) : P) * (a : P)⁻¹ ∈ A :=
    A.mul_mem (liftA S w).2 (A.inv_mem a.2)
  have hkey := S.hkey _ hmem
  rw [hkey]
  have hcomm : Commute ((liftA S w : ↥A) : P) ((a : P)⁻¹) :=
    S.hA.abelian _ (liftA S w).2 _ (A.inv_mem a.2)
  rw [hcomm.mul_pow, liftA_spec S w, inv_pow, ha, mul_inv_cancel]

/-- Changing the lift of `w` changes `⁅x, ·⁆` only by an element of `A ^ 4`. -/
theorem comm_lift_congr {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal]
    (S : D h A C) {x : P} (hx : x ∈ C) {a : ↥A} {w : ↥(omega1 P)}
    (ha : (a : P) ^ 2 ^ (S.e - 1) = (w : P)) :
    ∃ δ ∈ powSub A 4, ⁅x, ((liftA S w : ↥A) : P)⁆ = ⁅x, (a : P)⁆ * δ := by
  have hz : ((liftA S w : ↥A) : P) * (a : P)⁻¹ ∈ powSub A 2 := liftA_congr S ha
  have hzA2 : (a : P)⁻¹ * ((liftA S w : ↥A) : P) ∈ powSub A 2 := by
    have h2 : (a : P)⁻¹ * (((liftA S w : ↥A) : P) * (a : P)⁻¹) * ((a : P)⁻¹)⁻¹ ∈ powSub A 2 :=
      conj_mem_powSub 2 (a : P)⁻¹ hz
    rw [inv_inv] at h2
    have heq : (a : P)⁻¹ * (((liftA S w : ↥A) : P) * (a : P)⁻¹) * (a : P)
        = (a : P)⁻¹ * ((liftA S w : ↥A) : P) := by group
    rwa [heq] at h2
  have hlift : ((liftA S w : ↥A) : P)
      = (a : P) * ((a : P)⁻¹ * ((liftA S w : ↥A) : P)) := by group
  have hδ : (a : P) * ⁅x, (a : P)⁻¹ * ((liftA S w : ↥A) : P)⁆ * (a : P)⁻¹ ∈ powSub A 4 := by
    have hxz : ⁅x, (a : P)⁻¹ * ((liftA S w : ↥A) : P)⁆ ∈ powSub A 4 := by
      have hmem' : ⁅(a : P)⁻¹ * ((liftA S w : ↥A) : P), x⁆ ∈ powSub A 4 := by
        have hmem : ⁅(a : P)⁻¹ * ((liftA S w : ↥A) : P), x⁆ ∈ ⁅powSub A (2 ^ 1), C⁆ := by
          simpa using Subgroup.commutator_mem_commutator hzA2 hx
        rw [commutator_powSub_A_C h S.hA S.hCn S.hC2 S.hCd 1] at hmem
        simpa using hmem
      have hsym : ⁅x, (a : P)⁻¹ * ((liftA S w : ↥A) : P)⁆
          = ⁅(a : P)⁻¹ * ((liftA S w : ↥A) : P), x⁆⁻¹ := by
        rw [commutatorElement_def, commutatorElement_def]; group
      rw [hsym]
      exact (powSub A 4).inv_mem hmem'
    exact conj_mem_powSub 4 (a : P) hxz
  refine ⟨(a : P) * ⁅x, (a : P)⁻¹ * ((liftA S w : ↥A) : P)⁆ * (a : P)⁻¹, hδ, ?_⟩
  conv_lhs => rw [hlift]
  rw [commutator_mul_right_eq x (a : P) ((a : P)⁻¹ * ((liftA S w : ↥A) : P))]

/-- Changing `x` by an element of `A` does not change `⁅x, a⁆` (for `a ∈ A`). -/
theorem comm_mul_abelian_eq {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal]
    (S : D h A C) {x : P} (hx : x ∈ C) {c : P} (hc : c ∈ A) (a : ↥A) :
    ⁅x * c, (a : P)⁆ = ⁅x, (a : P)⁆ := by
  rw [commutator_mul_left_eq]
  have h1 : ⁅c, (a : P)⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (S.hA.abelian c hc (a : P) a.2)
  rw [h1]; group

/-- If `δ ∈ A ^ 4` then inserting it between two elements of `A` does not change the
`2 ^ (e-2)`-nd power. -/
theorem pow_mul_mem_powSub_four {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal]
    (S : D h A C) {δ : P} (hδ : δ ∈ powSub A 4) {α β : P} (hα : α ∈ A) (hβ : β ∈ A) :
    (α * δ * β) ^ 2 ^ (S.e - 2) = (α * β) ^ 2 ^ (S.e - 2) := by
  have hδA : δ ∈ A := powSub_le (by norm_num) hδ
  have hc1 : Commute α δ := S.hA.abelian α hα δ hδA
  have hc2 : Commute δ β := S.hA.abelian δ hδA β hβ
  have hc3 : Commute α β := S.hA.abelian α hα β hβ
  have hc23 : Commute β δ := hc2.symm
  have hmove : (α * δ) * β = (α * β) * δ := by rw [mul_assoc, hc2, ← mul_assoc]
  rw [show α * δ * β = (α * δ) * β from rfl, hmove,
    Commute.mul_pow (Commute.mul_left hc1 hc23) (2 ^ (S.e - 2)),
    Commute.mul_pow hc3 (2 ^ (S.e - 2)),
    pow_two_pow_sub_two_eq_one_of_mem_powSub_four S hδ, mul_one]

/-- The representative formula for `betaV`. -/
theorem betaV_rep {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal] (S : D h A C)
    {x : ↥C ⧸ (A.subgroupOf C)} {u : ↥C} {w : ↥(omega1 P)} {a : ↥A}
    (hu : QuotientGroup.mk u = x) (ha : (a : P) ^ 2 ^ (S.e - 1) = (w : P)) :
    ((betaV S x w : ↥(omega1 P)) : P)
      = ((u : P) * (a : P) * (u : P)⁻¹ * (a : P)⁻¹) ^ 2 ^ (S.e - 2) := by
  rw [betaV_apply]
  conv_rhs => rw [← commutatorElement_def]
  have hcA : ((((repC (A := A) (C := C) x)⁻¹ * u : ↥C) : P)) ∈ A :=
    repC_mul_inv_mem (A := A) (C := C) hu
  have hu_eq : (u : P) = ((repC (A := A) (C := C) x : ↥C) : P)
      * ((((repC (A := A) (C := C) x)⁻¹ * u : ↥C) : P)) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [hu_eq, comm_mul_abelian_eq S (repC (A := A) (C := C) x).2 hcA a]
  obtain ⟨δ, hδ, hδeq⟩ := comm_lift_congr S (repC (A := A) (C := C) x).2 ha
  rw [hδeq]
  have h1A : ⁅((repC (A := A) (C := C) x : ↥C) : P), (a : P)⁆ ∈ A := by
    have hmem : ⁅((repC (A := A) (C := C) x : ↥C) : P), (a : P)⁆ ∈ ⁅C, A⁆ :=
      Subgroup.commutator_mem_commutator (repC (A := A) (C := C) x).2 a.2
    rw [Subgroup.commutator_comm] at hmem
    rw [commutator_A_C_eq S] at hmem
    exact powSub_le (by norm_num) hmem
  have hδA : δ ∈ A := powSub_le (by norm_num) hδ
  have hcomm : Commute ⁅((repC (A := A) (C := C) x : ↥C) : P), (a : P)⁆ δ :=
    S.hA.abelian _ h1A δ hδA
  rw [Commute.mul_pow hcomm (2 ^ (S.e - 2)),
    pow_two_pow_sub_two_eq_one_of_mem_powSub_four S hδ, mul_one]


/-- `X * Z * X⁻¹ = Z * ⁅Z⁻¹, X⁆`. -/
theorem mul_commutator_inv_eq (X Z : P) : X * Z * X⁻¹ = Z * ⁅Z⁻¹, X⁆ := by
  rw [commutatorElement_def]; group

/-- The `2 ^ (e-2)`-nd power of an element of `A ^ 2` lies in `Ω₁(P)`. -/
theorem mem_omega1_pow_two_pow_sub_two {h : IsSuzuki2Grp P} {A C : Subgroup P}
    [hAn : A.Normal] (S : D h A C) {z : P} (hz : z ∈ powSub A 2) :
    z ^ 2 ^ (S.e - 2) ∈ omega1 P := by
  have he2 : 2 ≤ S.e := S.he2
  obtain ⟨d, hd, rfl⟩ := (mem_powSub_iff S.hA.abelian).mp hz
  rw [← pow_mul,
    show (2 : ℕ) * 2 ^ (S.e - 2) = 2 ^ (S.e - 1) from by rw [← pow_succ']; congr 1; omega]
  exact mem_omega1_pow_two_pow_sub_one h S.hA S.he1 S.he hd

/-- **Higman's Lemma 8, the bracket pairing.**  Collected properties of
`betaV : C/A × Ω₁(P) → Ω₁(P)`. -/
theorem l8_betaV {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal] (S : D h A C) :
    (∀ (x : ↥C ⧸ (A.subgroupOf C)) (u : ↥C) (w : ↥(omega1 P)) (a : ↥A),
      QuotientGroup.mk u = x → (a : P) ^ 2 ^ (S.e - 1) = (w : P) →
      ((betaV S x w : ↥(omega1 P)) : P)
        = ((u : P) * (a : P) * (u : P)⁻¹ * (a : P)⁻¹) ^ 2 ^ (S.e - 2)) ∧
    (∀ x x' : ↥C ⧸ (A.subgroupOf C), ∀ w : ↥(omega1 P),
      betaV S (x * x') w = betaV S x w * betaV S x' w) ∧
    (∀ x : ↥C ⧸ (A.subgroupOf C), ∀ w w' : ↥(omega1 P),
      betaV S x (w * w') = betaV S x w * betaV S x w') ∧
    (∀ x : ↥C ⧸ (A.subgroupOf C), ∀ w : ↥(omega1 P),
      xiZ h (betaV S x w) = betaV S (xiQuot h S.hA.map_eq S.hCinv x) (xiZ h w)) ∧
    (∀ x : ↥C ⧸ (A.subgroupOf C), betaV S x (sV S x) = 1) ∧
    (∃ x : ↥C ⧸ (A.subgroupOf C), ∃ w : ↥(omega1 P), betaV S x w ≠ 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x u w a hu ha
    exact betaV_rep S hu ha
  · intro x x' w
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨u', rfl⟩ := QuotientGroup.mk_surjective x'
    rw [← QuotientGroup.mk_mul]
    apply Subtype.ext
    rw [Subgroup.coe_mul,
      betaV_rep S (u := u * u') (w := w) (a := liftA S w) rfl (liftA_spec S w),
      betaV_rep S (u := u) (w := w) (a := liftA S w) rfl (liftA_spec S w),
      betaV_rep S (u := u') (w := w) (a := liftA S w) rfl (liftA_spec S w)]
    simp only [Subgroup.coe_mul]
    set X : P := ((u : ↥C) : P) with hXdef
    set Y : P := ((u' : ↥C) : P) with hYdef
    set Aa : P := ((liftA S w : ↥A) : P) with hAdef
    have hXc : X ∈ C := u.2
    have hYc : Y ∈ C := u'.2
    have hAa : Aa ∈ A := (liftA S w).2
    have hZ2 : ⁅Y, Aa⁆ ∈ powSub A 2 := by
      have hmem : ⁅Y, Aa⁆ ∈ ⁅C, A⁆ := Subgroup.commutator_mem_commutator hYc hAa
      rw [Subgroup.commutator_comm] at hmem
      rwa [commutator_A_C_eq S] at hmem
    have hW2 : ⁅X, Aa⁆ ∈ powSub A 2 := by
      have hmem : ⁅X, Aa⁆ ∈ ⁅C, A⁆ := Subgroup.commutator_mem_commutator hXc hAa
      rw [Subgroup.commutator_comm] at hmem
      rwa [commutator_A_C_eq S] at hmem
    have hZ : ⁅Y, Aa⁆ ∈ A := powSub_le (by norm_num) hZ2
    have hW : ⁅X, Aa⁆ ∈ A := powSub_le (by norm_num) hW2
    have hδ : ⁅⁅Y, Aa⁆⁻¹, X⁆ ∈ powSub A 4 := by
      have hmem : ⁅⁅Y, Aa⁆⁻¹, X⁆ ∈ ⁅powSub A (2 ^ 1), C⁆ := by
        simpa using Subgroup.commutator_mem_commutator ((powSub A 2).inv_mem hZ2) hXc
      rw [commutator_powSub_A_C h S.hA S.hCn S.hC2 S.hCd 1] at hmem
      simpa using hmem
    have hfold : X * Y * Aa * (X * Y)⁻¹ * Aa⁻¹ = (⁅Y, Aa⁆ * ⁅⁅Y, Aa⁆⁻¹, X⁆) * ⁅X, Aa⁆ := by
      rw [show X * Y * Aa * (X * Y)⁻¹ * Aa⁻¹ = ⁅X * Y, Aa⁆ from rfl,
        commutator_mul_left_eq X Y Aa,
        mul_commutator_inv_eq X ⁅Y, Aa⁆]
    rw [hfold, pow_mul_mem_powSub_four S hδ hZ hW,
      show X * Aa * X⁻¹ * Aa⁻¹ = ⁅X, Aa⁆ from rfl,
      show Y * Aa * Y⁻¹ * Aa⁻¹ = ⁅Y, Aa⁆ from rfl,
      Commute.mul_pow (S.hA.abelian ⁅Y, Aa⁆ hZ ⁅X, Aa⁆ hW) (2 ^ (S.e - 2))]
    exact h.omega1_comm (mem_omega1_pow_two_pow_sub_two S hZ2)
      (mem_omega1_pow_two_pow_sub_two S hW2)
  · intro x w w'
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
    apply Subtype.ext
    rw [Subgroup.coe_mul,
      betaV_rep S (u := u) (w := w * w')
        (a := ⟨((liftA S w : ↥A) : P) * ((liftA S w' : ↥A) : P),
          A.mul_mem (liftA S w).2 (liftA S w').2⟩) rfl ?_,
      betaV_rep S (u := u) (w := w) (a := liftA S w) rfl (liftA_spec S w),
      betaV_rep S (u := u) (w := w') (a := liftA S w') rfl (liftA_spec S w')]
    swap
    · have hc : Commute ((liftA S w : ↥A) : P) ((liftA S w' : ↥A) : P) :=
        S.hA.abelian _ (liftA S w).2 _ (liftA S w').2
      rw [hc.mul_pow, liftA_spec S w, liftA_spec S w', Subgroup.coe_mul]
    simp only [Subgroup.coe_mul]
    set X : P := ((u : ↥C) : P) with hXdef
    set Z : P := ((liftA S w : ↥A) : P) with hZdef
    set Z' : P := ((liftA S w' : ↥A) : P) with hZ'def
    have hXc : X ∈ C := u.2
    have hZ : Z ∈ A := (liftA S w).2
    have hZ' : Z' ∈ A := (liftA S w').2
    have hW1 : ⁅X, Z⁆ ∈ A := by
      have hmem : ⁅X, Z⁆ ∈ ⁅C, A⁆ := Subgroup.commutator_mem_commutator hXc hZ
      rw [Subgroup.commutator_comm] at hmem
      rw [commutator_A_C_eq S] at hmem
      exact powSub_le (by norm_num) hmem
    have hW2 : ⁅X, Z'⁆ ∈ A := by
      have hmem : ⁅X, Z'⁆ ∈ ⁅C, A⁆ := Subgroup.commutator_mem_commutator hXc hZ'
      rw [Subgroup.commutator_comm] at hmem
      rw [commutator_A_C_eq S] at hmem
      exact powSub_le (by norm_num) hmem
    have hfold : X * (Z * Z') * X⁻¹ * (Z * Z')⁻¹ = ⁅X, Z⁆ * ⁅X, Z'⁆ := by
      rw [show X * (Z * Z') * X⁻¹ * (Z * Z')⁻¹ = ⁅X, Z * Z'⁆ from rfl,
        commutator_mul_right_eq X Z Z']
      have hconj : Z * ⁅X, Z'⁆ * Z⁻¹ = ⁅X, Z'⁆ := by
        have hc : Z * ⁅X, Z'⁆ = ⁅X, Z'⁆ * Z := S.hA.abelian Z hZ _ hW2
        rw [hc]; group
      rw [hconj]
    rw [hfold, show X * Z * X⁻¹ * Z⁻¹ = ⁅X, Z⁆ from rfl,
      show X * Z' * X⁻¹ * Z'⁻¹ = ⁅X, Z'⁆ from rfl,
      Commute.mul_pow (S.hA.abelian ⁅X, Z⁆ hW1 ⁅X, Z'⁆ hW2) (2 ^ (S.e - 2))]
  · intro x w
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
    apply Subtype.ext
    rw [xiZ_apply,
      betaV_rep S (u := u) (w := w) (a := liftA S w) rfl (liftA_spec S w),
      betaV_rep S (u := xiSubAut h S.hCinv u) (w := xiZ h w)
        (a := ⟨h.xi ((liftA S w : ↥A) : P),
          (Subgroup.mem_map_of_mem (h.xi : MulAut P).toMonoidHom (liftA S w).2) |> fun hh =>
            by rwa [S.hA.map_eq] at hh⟩)
        (xiQuot_mk S.hA.map_eq S.hCinv u).symm ?_, map_pow]
    swap
    · rw [xiZ_apply]
      show (h.xi ((liftA S w : ↥A) : P)) ^ 2 ^ (S.e - 1) = h.xi (w : P)
      rw [← map_pow, liftA_spec S w]
    congr 1
    simp only [map_mul, map_inv]
    simp only [xiSubAut_apply]
  · intro x
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
    apply Subtype.ext
    rw [betaV_rep S (u := u) (w := sV S (QuotientGroup.mk u))
      (a := ⟨((u : ↥C) : P) ^ 2, S.hC2 (pow_mem_powSub (A := C) u.2)⟩) rfl ?_]
    swap
    · have he : 1 ≤ S.e := S.he
      have h1 : 2 * 2 ^ (S.e - 1) = (2 : ℕ) ^ S.e := by
        rw [← pow_succ', show S.e - 1 + 1 = S.e from by omega]
      rw [← pow_mul, h1, sV_mk]
    rw [show ((u : P) * ((u : P) ^ 2) * (u : P)⁻¹ * ((u : P) ^ 2)⁻¹) = 1 from by group,
      one_pow]
    rfl
  · by_contra hcon
    push_neg at hcon
    have he : 1 ≤ S.e := S.he
    have he2 : 2 ≤ S.e := S.he2
    have hle : ⁅A, C⁆ ≤ powSub A 4 := by
      rw [Subgroup.commutator_le]
      intro a ha u hu
      have ha' : (⟨a, ha⟩ : ↥A) ^ 2 ^ (S.e - 1)
          = (⟨a ^ 2 ^ (S.e - 1),
              mem_omega1_pow_two_pow_sub_one h S.hA S.he1 S.he ha⟩ : ↥(omega1 P)).1 := rfl
      have h1 := hcon (QuotientGroup.mk ⟨u, hu⟩)
        ⟨a ^ 2 ^ (S.e - 1), mem_omega1_pow_two_pow_sub_one h S.hA S.he1 S.he ha⟩
      have h2 := congrArg (fun t : ↥(omega1 P) => (t : P)) h1
      rw [betaV_rep S (u := ⟨u, hu⟩) (a := ⟨a, ha⟩) rfl ha'] at h2
      have hmem : ⁅a, u⁆ ∈ powSub A 2 := by
        have hmem : ⁅a, u⁆ ∈ ⁅A, C⁆ := Subgroup.commutator_mem_commutator ha hu
        rwa [commutator_A_C_eq S] at hmem
      have hk1 : (⁅a, u⁆) ^ 2 ^ (S.e - 2) = 1 := by
        have h2' : (⁅u, a⁆) ^ 2 ^ (S.e - 2) = 1 := by simpa [commutatorElement_def] using h2
        have hsym : ⁅a, u⁆ = ⁅u, a⁆⁻¹ := by
          rw [commutatorElement_def, commutatorElement_def]; group
        rw [hsym, inv_pow, h2', inv_one]
      exact (powSub_four_ker h S.hA S.he1 S.hkey hmem).mpr hk1
    have hsq : powSub A 2 = powSub A 4 := by
      rw [commutator_A_C_eq S] at hle
      exact le_antisymm hle (powSub_le_of_dvd S.hA.abelian ⟨2, by norm_num⟩)
    have hiter : ∀ k, powSub A 2 = powSub A (2 ^ (k + 1)) := by
      intro k
      induction k with
      | zero => rw [show (2 : ℕ) ^ (0 + 1) = 2 from by norm_num]
      | succ k ih =>
          rw [show (2 : ℕ) ^ (k + 1 + 1) = 2 ^ (k + 1) * 2 from by rw [pow_succ],
            ← powSub_powSub S.hA.abelian, ← ih,
            show powSub (powSub A 2) 2 = powSub A 4 from by
              rw [powSub_powSub S.hA.abelian],
            ← hsq]
    have hbot : powSub A 2 = ⊥ := by
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp (h.isPGroup.to_subgroup A)
      rw [hiter n]
      refine powSub_eq_bot_of_exp S.hA.abelian (by omega : n ≤ n + 1) fun x hx => ?_
      haveI : Fintype ↥A := Fintype.ofFinite _
      have hxA : orderOf (⟨x, hx⟩ : ↥A) ∣ 2 ^ n := by
        have hh := orderOf_dvd_card (x := (⟨x, hx⟩ : ↥A))
        rwa [← Nat.card_eq_fintype_card, hn] at hh
      have h1 : (⟨x, hx⟩ : ↥A) ^ 2 ^ n = 1 := orderOf_dvd_iff_pow_eq_one.mp hxA
      simpa [Subgroup.coe_pow] using congrArg (fun t : ↥A => (t : P)) h1
    have hOm : omega1 P = ⊥ := by
      rw [← S.htopA]
      refine le_bot_iff.mp (le_trans ?_ (le_of_eq hbot))
      exact powSub_le_of_dvd S.hA.abelian (Nat.pow_dvd_pow 2 (by omega : 1 ≤ S.e - 1))
    exact absurd hOm (fun hh => by
      have h4 := h.omega1_card_ge_four
      rw [hh] at h4
      simp at h4)

end Work.Higman.MSA.L8
