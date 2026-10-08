/-
# An odd-order subgroup of `GL(2,p)` of order prime to `p` is abelian

(`Work.SmallRank.isMulCommutative_of_odd_coprime_le_GL2`.)

This is lemma **G2** of `NOTES_LEAD_ft_smallrank.md` §5.  The proof is elementary
(`Submission/Work/SmallRank/GL2Defs.lean` develops the needed algebra of `𝔽_p[a] ⊆ M₂(𝔽_p)`):

* every `a ∈ A` is semisimple (`disc_ne_zero_of_pow_eq_one`), so for non-scalar `a` the centraliser
  of `a` in `M₂(𝔽_p)` is the commutative algebra `𝔽_p[a] = polySet a` (`mem_polySet_of_mul_eq_mul`);
* consequently `M_a := A ∩ 𝔽_p[a]ˣ` is abelian and is its own normaliser in `A`
  (`mem_polyUnitSub_of_conj_mem`);
* two such `M_a` either coincide or meet in `Z := A ∩ (scalars)` (`polySet_eq_of_mem_inter`), and the
  `M_a` cover `A`;
* the counting lemma `isMulCommutative_of_member_family` (the "Miller–Moreno" argument) then forces
  `A` to be abelian.

The case `p = 2` is separate: `GL(2,𝔽₂)` has order `6`, so an odd-order subgroup has order `1` or
`3` and is cyclic.
-/
import Mathlib
import Submission.Work.SmallRank.GL2Defs
import Submission.Work.SmallRank.mem_polySet_of_mul_eq_mul
import Submission.Work.SmallRank.disc_ne_zero_of_pow_eq_one
import Submission.Work.SmallRank.isMulCommutative_of_member_family

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Classical
open Matrix

noncomputable section

namespace Work.SmallRank

variable {p : ℕ} [Fact p.Prime]

/-! ## Elementary matrix algebra -/

/-- Scalar matrices commute with every matrix. -/
lemma scalar_mul_eq_mul_scalar (α : ZMod p) (x : M2 p) : (α • 1) * x = x * (α • 1) := by
  rw [Matrix.smul_mul, one_mul, Matrix.mul_smul, mul_one]

/-- Conjugation of `α + β Y` by a unit. -/
lemma unit_mul_add_mul_inv (g : (M2 p)ˣ) (α β : ZMod p) (Y : M2 p) :
    (↑g : M2 p) * (α • 1 + β • Y) * (↑g⁻¹ : M2 p)
      = α • 1 + β • ((↑g : M2 p) * Y * (↑g⁻¹ : M2 p)) := by
  simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.add_mul, Matrix.smul_mul,
    Units.mul_inv]

/-- Membership in `polySet` is equivariant under conjugation by units. -/
lemma mem_polySet_conj_iff (g X v : (M2 p)ˣ) :
    (v : M2 p) ∈ polySet (X : M2 p) ↔
      ((g * v * g⁻¹ : (M2 p)ˣ) : M2 p) ∈ polySet ((g * X * g⁻¹ : (M2 p)ˣ) : M2 p) := by
  constructor
  · rintro ⟨α, β, h⟩
    refine ⟨α, β, ?_⟩
    rw [Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, h]
    exact unit_mul_add_mul_inv g α β (X : M2 p)
  · rintro ⟨α, β, h⟩
    refine ⟨α, β, ?_⟩
    have hg : (↑(g⁻¹) : M2 p) * (↑((g * v * g⁻¹ : (M2 p)ˣ)) : M2 p) * (↑g : M2 p)
        = (↑v : M2 p) := by
      rw [← Units.val_mul, ← Units.val_mul,
        show g⁻¹ * (g * v * g⁻¹) * g = v from by group]
    have hY : (↑(g⁻¹) : M2 p) * (↑((g * X * g⁻¹ : (M2 p)ˣ)) : M2 p) * (↑g : M2 p)
        = (↑X : M2 p) := by
      rw [← Units.val_mul, ← Units.val_mul,
        show g⁻¹ * (g * X * g⁻¹) * g = X from by group]
    have key := unit_mul_add_mul_inv (g⁻¹) α β ((↑((g * X * g⁻¹ : (M2 p)ˣ)) : M2 p))
    simp only [inv_inv] at key
    rw [← hg, h, key, hY]

/-- Conjugation of `polyUnitSub`. -/
lemma map_conj_polyUnitSub (g X : (M2 p)ˣ) :
    (polyUnitSub (X : M2 p)).map (MulAut.conj g).toMonoidHom
      = polyUnitSub ((g * X * g⁻¹ : (M2 p)ˣ) : M2 p) := by
  ext u
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨v, hv, hvu⟩
    have hv' : (v : M2 p) ∈ polySet (X : M2 p) := hv
    rw [← hvu, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (mem_polySet_conj_iff g X v).mp hv'
  · intro hu
    refine ⟨(g⁻¹ * u * g : (M2 p)ˣ), ?_, ?_⟩
    · refine (mem_polySet_conj_iff g X (g⁻¹ * u * g)).mpr ?_
      rwa [show g * (g⁻¹ * u * g) * g⁻¹ = u from by group]
    · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

/-! ## The scalar subgroup and the members -/

/-- The scalar matrices inside `GL(2,p)`. -/
abbrev scalarSub (p : ℕ) [Fact p.Prime] : Subgroup (GL (Fin 2) (ZMod p)) := polyUnitSub (0 : M2 p)

lemma mem_scalarSub_iff {u : GL (Fin 2) (ZMod p)} : u ∈ scalarSub p ↔ IsScalar (u : M2 p) := by
  rw [scalarSub, mem_polyUnitSub_iff]
  constructor
  · rintro ⟨α, β, h⟩
    exact ⟨α, by rw [h]; simp⟩
  · rintro ⟨α, h⟩
    exact ⟨α, 0, by rw [h]; simp⟩

/-- `Z = A ∩ {scalar matrices}`, as a subgroup of `A`. -/
def Zsub (A : Subgroup (GL (Fin 2) (ZMod p))) : Subgroup ↥A := (scalarSub p).comap A.subtype

/-- The "member" `M x = A ∩ 𝔽_p[x]ˣ` attached to `x : A`. -/
def memberSub (A : Subgroup (GL (Fin 2) (ZMod p))) (x : ↥A) : Subgroup ↥A :=
  (polyUnitSub ((x : GL (Fin 2) (ZMod p)) : M2 p)).comap A.subtype

lemma mem_Zsub_iff {A : Subgroup (GL (Fin 2) (ZMod p))} {x : ↥A} :
    x ∈ Zsub A ↔ IsScalar ((x : GL (Fin 2) (ZMod p)) : M2 p) := by
  rw [Zsub, Subgroup.mem_comap, mem_scalarSub_iff]
  rfl

lemma mem_memberSub_iff {A : Subgroup (GL (Fin 2) (ZMod p))} {x y : ↥A} :
    y ∈ memberSub A x ↔
      ((y : GL (Fin 2) (ZMod p)) : M2 p) ∈ polySet ((x : GL (Fin 2) (ZMod p)) : M2 p) := by
  rw [memberSub, Subgroup.mem_comap, mem_polyUnitSub_iff]
  rfl

/-! ## The normaliser of `𝔽_p[x]ˣ` -/

/-- If `n` conjugates the unit `X` into `𝔽_p[X]ˣ` then `n ∈ 𝔽_p[X]ˣ`, provided `X` is non-scalar of
order invertible in `𝔽_p` and `n` has odd order.  This is the key "self-normalising" step: every
element of `𝔽_p[X]` that is conjugate to `X` is `X` itself or `(tr X) - X`, and in the latter case
`n²` centralises `X`, whence `n` does as `n` has odd order. -/
theorem mem_polyUnitSub_of_conj_mem (hp2 : p ≠ 2) {X : (M2 p)ˣ} (hX : NonScalar (X : M2 p))
    {m : ℕ} (hm : (m : ZMod p) ≠ 0) (hXm : (X : M2 p) ^ m = 1) {n : (M2 p)ˣ}
    (hconj : n * X * n⁻¹ ∈ polyUnitSub (X : M2 p)) (hoddn : Odd (orderOf n)) :
    n ∈ polyUnitSub (X : M2 p) := by
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdiv : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
    have hge : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
    omega
  obtain ⟨α, β, hab⟩ := (mem_polyUnitSub_iff.mp hconj)
  -- trace and determinant are conjugation invariant
  have htr : Matrix.trace (((n * X * n⁻¹ : (M2 p)ˣ) : M2 p)) = Matrix.trace (X : M2 p) := by
    rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, Units.inv_mul, one_mul]
  have hdet : (((n * X * n⁻¹ : (M2 p)ˣ) : M2 p)).det = (X : M2 p).det := by
    have h1 : ((↑n : M2 p)).det * ((↑n⁻¹ : M2 p)).det = 1 := by
      rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul]
    calc ((↑n : M2 p).det * (X : M2 p).det) * ((↑n⁻¹ : M2 p)).det
        = (X : M2 p).det * (((↑n : M2 p)).det * ((↑n⁻¹ : M2 p)).det) := by ring
      _ = (X : M2 p).det * 1 := by rw [h1]
      _ = (X : M2 p).det := mul_one _
  have htr' : 2 * α + β * Matrix.trace (X : M2 p) = Matrix.trace (X : M2 p) := by
    have h := congrArg Matrix.trace hab
    rw [trace_smul_one_add_smul] at h
    rw [htr] at h
    exact h.symm
  have hdet' : α ^ 2 + α * β * Matrix.trace (X : M2 p) + β ^ 2 * (X : M2 p).det
      = (X : M2 p).det := by
    have h := congrArg Matrix.det hab
    rw [det_smul_one_add_smul] at h
    rw [hdet] at h
    exact h.symm
  have hdisc : 4 * (X : M2 p).det - (Matrix.trace (X : M2 p)) ^ 2 ≠ 0 :=
    disc_ne_zero_of_pow_eq_one hX hm hXm
  have hβ2 : β ^ 2 = 1 := by
    have h := sq_sub_one_mul_disc_eq_zero (X : M2 p) α β htr' hdet'
    rcases mul_eq_zero.mp h with h1 | h1
    · linear_combination h1
    · exact absurd h1 hdisc
  rcases sq_eq_one_iff.mp hβ2 with hβ | hβ
  · -- `β = 1`: then `α = 0` and `n` centralises `X`
    have hα : α = 0 := by
      have h := htr'
      rw [hβ] at h
      have h2 : 2 * α = 0 := by linear_combination h
      exact (mul_eq_zero.mp h2).resolve_left htwo
    have hb : ((n * X * n⁻¹ : (M2 p)ˣ) : M2 p) = (X : M2 p) := by
      rw [hab, hβ, hα]
      simp
    have hcomm : (↑n : M2 p) * (X : M2 p) = (X : M2 p) * (↑n : M2 p) := by
      rw [Units.val_mul, Units.val_mul] at hb
      have key : (↑n : M2 p) * (X : M2 p) * (↑n⁻¹ : M2 p) * (↑n : M2 p)
          = (↑n : M2 p) * (X : M2 p) := by
        rw [mul_assoc, Units.inv_mul, mul_one]
      rw [hb] at key
      exact key.symm
    exact mem_polySet_of_mul_eq_mul hX hcomm
  · -- `β = -1`: then `n²` centralises `X`, and since `n` has odd order `n ∈ ⟨n²⟩`
    have hα : α = Matrix.trace (X : M2 p) := by
      have h := htr'
      rw [hβ] at h
      have h2 : 2 * (α - Matrix.trace (X : M2 p)) = 0 := by linear_combination h
      have h3 := (mul_eq_zero.mp h2).resolve_left htwo
      linear_combination h3
    have hb2 : ((n * X * n⁻¹ : (M2 p)ˣ) : M2 p)
        = Matrix.trace (X : M2 p) • 1 - (X : M2 p) := by
      rw [hab, hβ, hα]
      module
    have hmain : ((n ^ 2 * X * (n ^ 2)⁻¹ : (M2 p)ˣ) : M2 p) = (X : M2 p) := by
      have hcoe1 : ((n ^ 2 * X * (n ^ 2)⁻¹ : (M2 p)ˣ) : M2 p)
          = (↑n : M2 p) * (((n * X * n⁻¹ : (M2 p)ˣ)) : M2 p) * (↑n⁻¹ : M2 p) := by
        rw [show n ^ 2 * X * (n ^ 2)⁻¹ = n * (n * X * n⁻¹) * n⁻¹ from by rw [pow_two]; group,
          Units.val_mul, Units.val_mul]
      rw [hcoe1, hb2]
      have htriple : (↑n : M2 p) * (Matrix.trace (X : M2 p) • 1 - (X : M2 p)) * (↑n⁻¹ : M2 p)
          = Matrix.trace (X : M2 p) • 1
            - ((↑n : M2 p) * (X : M2 p) * (↑n⁻¹ : M2 p)) := by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
          Matrix.mul_one, Units.mul_inv]
      rw [htriple]
      have hcoe2 : (↑n : M2 p) * (X : M2 p) * (↑n⁻¹ : M2 p)
          = ((n * X * n⁻¹ : (M2 p)ˣ) : M2 p) := by
        rw [← Units.val_mul, ← Units.val_mul]
      rw [hcoe2, hb2]
      module
    have hcomm2 : ((n ^ 2 : (M2 p)ˣ) : M2 p) * (X : M2 p)
        = (X : M2 p) * ((n ^ 2 : (M2 p)ˣ) : M2 p) := by
      have h2 : (↑(n ^ 2 : (M2 p)ˣ) : M2 p) * (X : M2 p)
          * (↑((n ^ 2 : (M2 p)ˣ)⁻¹) : M2 p) = (X : M2 p) := by
        have h := hmain
        rw [Units.val_mul, Units.val_mul] at h
        exact h
      have key : (↑(n ^ 2 : (M2 p)ˣ) : M2 p) * (X : M2 p)
          * (↑((n ^ 2 : (M2 p)ˣ)⁻¹) : M2 p) * (↑(n ^ 2 : (M2 p)ˣ) : M2 p)
          = (↑(n ^ 2 : (M2 p)ˣ) : M2 p) * (X : M2 p) := by
        rw [mul_assoc, Units.inv_mul, mul_one]
      rw [h2] at key
      exact key.symm
    have hn2 : n ^ 2 ∈ polyUnitSub (X : M2 p) := mem_polySet_of_mul_eq_mul hX hcomm2
    obtain ⟨k, hk⟩ := hoddn
    have hn : n = (n ^ 2) ^ (k + 1) := by
      rw [← pow_mul, show 2 * (k + 1) = orderOf n + 1 by rw [hk]; ring, pow_succ,
        pow_orderOf_eq_one, one_mul]
    rw [hn]
    exact pow_mem hn2 (k + 1)



/-! ## The member family and the counting lemma -/

/-- The matrix of a product in `↥A`. -/
lemma coe_mul_matrix (A : Subgroup (GL (Fin 2) (ZMod p))) (u v : ↥A) :
    (((u * v : ↥A) : GL (Fin 2) (ZMod p)) : M2 p)
      = ((u : GL (Fin 2) (ZMod p)) : M2 p) * ((v : GL (Fin 2) (ZMod p)) : M2 p) := by
  rw [Subgroup.coe_mul, Units.val_mul]

/-- The matrix of an inverse in `↥A`. -/
lemma coe_inv_matrix (A : Subgroup (GL (Fin 2) (ZMod p))) (u : ↥A) :
    (((u⁻¹ : ↥A) : GL (Fin 2) (ZMod p)) : M2 p)
      = ((((u : (M2 p)ˣ))⁻¹ : (M2 p)ˣ) : M2 p) := by
  rw [Subgroup.coe_inv]

/-- Coercion of a product of three units. -/
lemma val_mul_three (u v w : (M2 p)ˣ) :
    (((u * v * w : (M2 p)ˣ) : M2 p)) = (u : M2 p) * (v : M2 p) * (w : M2 p) := by
  rw [Units.val_mul, Units.val_mul]

/-- Matrix form of conjugation in `↥A`. -/
lemma coe_conj_matrix (A : Subgroup (GL (Fin 2) (ZMod p))) (g x : ↥A) :
    ((((g : (M2 p)ˣ) * (x : (M2 p)ˣ) * (((g : (M2 p)ˣ))⁻¹ : (M2 p)ˣ) : (M2 p)ˣ) : M2 p))
      = (((g * x * g⁻¹ : ↥A) : GL (Fin 2) (ZMod p)) : M2 p) := by
  rw [Units.val_mul, Units.val_mul, coe_mul_matrix, coe_mul_matrix, coe_inv_matrix]

/-- Matrix form of conjugation by an inverse in `↥A`. -/
lemma coe_conj_inv_matrix (A : Subgroup (GL (Fin 2) (ZMod p))) (g y : ↥A) :
    (((((g : (M2 p)ˣ))⁻¹ * (y : (M2 p)ˣ) * (g : (M2 p)ˣ) : (M2 p)ˣ) : M2 p))
      = (((g⁻¹ * y * g : ↥A) : GL (Fin 2) (ZMod p)) : M2 p) := by
  rw [Units.val_mul, Units.val_mul, coe_mul_matrix, coe_mul_matrix, coe_inv_matrix]

/-- `M x = A ⊓ 𝔽_p[x]ˣ` is its own normaliser in `A` (for `x ∉ Z`, `p ≠ 2`). -/
lemma normalizer_memberSub (hp2 : p ≠ 2) (A : Subgroup (GL (Fin 2) (ZMod p)))
    (hodd : Odd (Nat.card A)) (hcop : ¬ p ∣ Nat.card A) {x : ↥A} (hx : x ∉ Zsub A) :
    Subgroup.normalizer ((memberSub A x : Subgroup ↥A) : Set ↥A) = memberSub A x := by
  haveI : Fintype ↥A := Fintype.ofFinite ↥A
  have hm : ((Nat.card ↥A : ℕ) : ZMod p) ≠ 0 := by
    intro h
    exact hcop ((CharP.cast_eq_zero_iff (ZMod p) p (Nat.card ↥A)).mp h)
  have hxns : NonScalar (((x : GL (Fin 2) (ZMod p))) : M2 p) := fun h => hx ((mem_Zsub_iff).mpr h)
  have hxm : (((x : (M2 p)ˣ)) : M2 p) ^ Nat.card ↥A = 1 := by
    have h1 : x ^ Nat.card ↥A = (1 : ↥A) := by
      rw [Nat.card_eq_fintype_card]
      exact pow_card_eq_one
    have h2 : (((x ^ Nat.card ↥A : ↥A) : GL (Fin 2) (ZMod p)) : M2 p) = 1 := by
      rw [h1]
      rfl
    rwa [Subgroup.coe_pow, Units.val_pow_eq_pow_val] at h2
  refine le_antisymm ?_ ?_
  · intro n hn
    have hxmem : x ∈ memberSub A x := (mem_memberSub_iff).mpr (self_mem_polySet _)
    have hnm : n * x * n⁻¹ ∈ memberSub A x := (Subgroup.mem_normalizer_iff.mp hn x).mp hxmem
    have hnm' : ((((n * x * n⁻¹ : ↥A) : GL (Fin 2) (ZMod p)) : M2 p))
        ∈ polySet (((x : GL (Fin 2) (ZMod p))) : M2 p) := hnm
    have hconj : (n : (M2 p)ˣ) * (x : (M2 p)ˣ) * (((n : (M2 p)ˣ))⁻¹ : (M2 p)ˣ)
        ∈ polyUnitSub (((x : (M2 p)ˣ)) : M2 p) := by
      have h2 : ((((n : (M2 p)ˣ) * (x : (M2 p)ˣ) * (((n : (M2 p)ˣ))⁻¹ : (M2 p)ˣ) : (M2 p)ˣ)
          : M2 p)) ∈ polySet (((x : (M2 p)ˣ)) : M2 p) := by
        rw [coe_conj_matrix A n x]
        exact hnm'
      exact h2
    have hoddn : Odd (orderOf (n : (M2 p)ˣ)) := by
      have h1 : (((n : ↥A) : GL (Fin 2) (ZMod p))) ^ Nat.card ↥A = 1 := by
        have h0 : n ^ Nat.card ↥A = (1 : ↥A) := by
          rw [Nat.card_eq_fintype_card]
          exact pow_card_eq_one
        have h2 : (((n ^ Nat.card ↥A : ↥A) : GL (Fin 2) (ZMod p))) = 1 := by
          rw [h0]
          rfl
        rwa [Subgroup.coe_pow] at h2
      exact hodd.of_dvd_nat (orderOf_dvd_iff_pow_eq_one.mpr h1)
    exact mem_polyUnitSub_of_conj_mem hp2 hxns hm hxm hconj hoddn
  · rw [Subgroup.le_normalizer_iff]
    intro m hm y hy
    have hm' : ((m : (M2 p)ˣ) : M2 p) ∈ polySet (((x : (M2 p)ˣ)) : M2 p) := hm
    have hy' : ((y : (M2 p)ˣ) : M2 p) ∈ polySet (((x : (M2 p)ˣ)) : M2 p) := hy
    have hcomm : m * y = y * m :=
      Subtype.ext (Units.ext (mul_comm_of_mem_polySet hm' hy'))
    have hmy : m * y * m⁻¹ = y := by rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    rw [hmy]
    exact hy

/-- The member family is conjugation-equivariant. -/
lemma map_conj_memberSub (A : Subgroup (GL (Fin 2) (ZMod p))) (g x : ↥A) :
    (memberSub A x).map (MulAut.conj g).toMonoidHom = memberSub A (g * x * g⁻¹) := by
  have hmem : ∀ w : ↥A, MulAut.conj g w ∈ memberSub A (g * x * g⁻¹) ↔ w ∈ memberSub A x := by
    intro w
    have hcoe : (((MulAut.conj g w : ↥A) : GL (Fin 2) (ZMod p)) : M2 p)
        = (((g : (M2 p)ˣ) * (w : (M2 p)ˣ) * (((g : (M2 p)ˣ))⁻¹ : (M2 p)ˣ) : (M2 p)ˣ)
          : M2 p) := by
      rw [MulAut.conj_apply, ← coe_conj_matrix A g w]
    have hxcoe : (((g * x * g⁻¹ : ↥A) : GL (Fin 2) (ZMod p)) : M2 p)
        = (((g : (M2 p)ˣ) * (x : (M2 p)ˣ) * (((g : (M2 p)ˣ))⁻¹ : (M2 p)ˣ) : (M2 p)ˣ)
          : M2 p) := by
      rw [← coe_conj_matrix A g x]
    rw [mem_memberSub_iff, mem_memberSub_iff, hcoe, hxcoe]
    exact (mem_polySet_conj_iff (g : (M2 p)ˣ) (x : (M2 p)ˣ) (w : (M2 p)ˣ)).symm
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨z, hz, hzy⟩
    rw [← hzy]
    exact (hmem z).mpr hz
  · intro hy
    refine ⟨g⁻¹ * y * g, ?_, ?_⟩
    · have h : MulAut.conj g (g⁻¹ * y * g : ↥A) = y := by
        rw [MulAut.conj_apply]
        group
      exact (hmem (g⁻¹ * y * g)).mp (by rw [h]; exact hy)
    · show MulAut.conj g (g⁻¹ * y * g : ↥A) = y
      rw [MulAut.conj_apply]
      group

/-- The case `p ≠ 2`. -/
theorem isMulCommutative_of_odd_coprime_le_GL2_odd (hp2 : p ≠ 2)
    (A : Subgroup (GL (Fin 2) (ZMod p))) (hodd : Odd (Nat.card A)) (hcop : ¬ p ∣ Nat.card A) :
    IsMulCommutative A := by
  refine isMulCommutative_of_member_family hodd (Zsub A) ?_ (memberSub A) ?_ ?_ ?_ ?_ ?_ ?_
  · -- the scalars are central
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    apply Units.ext
    have hz' : IsScalar (((z : GL (Fin 2) (ZMod p))) : M2 p) := mem_Zsub_iff.mp hz
    obtain ⟨α, hα⟩ := hz'
    rw [coe_mul_matrix, coe_mul_matrix, hα]
    exact (scalar_mul_eq_mul_scalar α _).symm
  · -- `Z ≤ M x`
    intro x hx z hz
    refine (mem_memberSub_iff).mpr ?_
    obtain ⟨α, hα⟩ := mem_Zsub_iff.mp hz
    rw [hα]
    exact smul_one_mem_polySet _ α
  · -- `x ∈ M x`
    intro x hx
    exact (mem_memberSub_iff).mpr (self_mem_polySet _)
  · -- `M x` is abelian
    intro x hx
    rw [isMulCommutative_iff]
    intro y z
    exact Subtype.ext (Subtype.ext (Units.ext (mul_comm_of_mem_polySet y.2 z.2)))
  · -- two members are equal or meet in `Z`
    intro x y hx hy
    by_cases h : ∃ z : ↥A, z ∈ memberSub A x ⊓ memberSub A y ∧ z ∉ Zsub A
    · left
      obtain ⟨z, hz, hznz⟩ := h
      have hzns : NonScalar (((z : GL (Fin 2) (ZMod p))) : M2 p) :=
        fun hs => hznz ((mem_Zsub_iff).mpr hs)
      have hzx : ((z : GL (Fin 2) (ZMod p))) ∈ polyUnitSub (((x : GL (Fin 2) (ZMod p))) : M2 p) :=
        hz.1
      have hzy : ((z : GL (Fin 2) (ZMod p))) ∈ polyUnitSub (((y : GL (Fin 2) (ZMod p))) : M2 p) :=
        hz.2
      have hp : polySet (((x : GL (Fin 2) (ZMod p))) : M2 p)
          = polySet (((y : GL (Fin 2) (ZMod p))) : M2 p) :=
        polySet_eq_of_mem_inter hzx hzy hzns
      refine le_antisymm ?_ ?_
      · intro w hw
        refine (mem_memberSub_iff).mpr ?_
        rw [← hp]
        exact hw
      · intro w hw
        refine (mem_memberSub_iff).mpr ?_
        rw [hp]
        exact hw
    · right
      push_neg at h
      refine le_antisymm ?_ ?_
      · intro w hw
        exact h w hw
      · intro w hw
        refine ⟨?_, ?_⟩
        · refine (mem_memberSub_iff).mpr ?_
          obtain ⟨α, hα⟩ := mem_Zsub_iff.mp hw
          rw [hα]
          exact smul_one_mem_polySet _ α
        · refine (mem_memberSub_iff).mpr ?_
          obtain ⟨α, hα⟩ := mem_Zsub_iff.mp hw
          rw [hα]
          exact smul_one_mem_polySet _ α
  · -- self-normalising
    intro x hx
    exact normalizer_memberSub hp2 A hodd hcop hx
  · -- conjugation-equivariance
    intro x hx g
    exact map_conj_memberSub A g x

/-! ## The case `p = 2` -/

/-- A subgroup of `GL(2,𝔽₂)` of odd order is abelian (`|GL(2,𝔽₂)| = 6`). -/
theorem isMulCommutative_of_odd_subgroup_GL2_zmod_two (A : Subgroup (GL (Fin 2) (ZMod 2)))
    (hodd : Odd (Nat.card A)) : IsMulCommutative A := by
  have hcard : Nat.card (GL (Fin 2) (ZMod 2)) = 6 := by
    rw [Matrix.card_GL_field]
    simp only [Fin.prod_univ_two, ZMod.card]
    norm_num
  have hdvd : Nat.card A ∣ 6 := by
    rw [← hcard]
    exact Subgroup.card_subgroup_dvd_card A
  have hA13 : Nat.card A = 1 ∨ Nat.card A = 3 := by
    have hle : Nat.card A ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
    have hge : 1 ≤ Nat.card A := Nat.card_pos
    interval_cases h : Nat.card A
    · exact Or.inl rfl
    · exact absurd hodd (by decide)
    · exact Or.inr rfl
    · exact absurd hodd (by decide)
    · exact absurd hdvd (by decide)
    · exact absurd hodd (by decide)
  rcases hA13 with h1 | h3
  · haveI : Subsingleton ↥A := Finite.card_le_one_iff_subsingleton.mp (by omega)
    rw [isMulCommutative_iff]
    intro x y
    exact Subsingleton.elim _ _
  · haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    haveI : IsCyclic ↥A := isCyclic_of_prime_card (p := 3) (by simpa using h3)
    exact IsCyclic.isMulCommutative

/-- An odd-order subgroup of `GL(2, p)` of order prime to `p` is abelian.  Proof (elementary, no
representation theory, as in `NOTES_LEAD_ft_smallrank.md` §5): every `a ∈ A` is semisimple; for
non-scalar `a`, `C_{M₂(F_p)}(a) = F_p[a]` is a commutative subfield ('a 2×2 non-scalar matrix is
cyclic'), so the centraliser `C_A(a)` is abelian; two such centralisers are equal or meet in
`A ∩ scalars`; use the characterisation `n a n⁻¹ ∈ {a, tr(a) - a}` for `n ∈ N_A(C_A(a))` to see that
each `C_A(a)/Z` is self-normalising in `A/Z`, and count conjugacy classes. -/
theorem isMulCommutative_of_odd_coprime_le_GL2 {p : ℕ} [Fact p.Prime]
    (A : Subgroup (GL (Fin 2) (ZMod p))) (hodd : Odd (Nat.card A)) (hcop : ¬ p ∣ Nat.card A) :
    IsMulCommutative A := by
  rcases eq_or_ne p 2 with hp | hp2
  · subst hp
    exact isMulCommutative_of_odd_subgroup_GL2_zmod_two A hodd
  · exact isMulCommutative_of_odd_coprime_le_GL2_odd hp2 A hodd hcop

end Work.SmallRank
