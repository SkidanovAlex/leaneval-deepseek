/-
# The Singer/field model of the layer `Ω₁(P)`

`Work.Higman.HS.omega1_singer_iso`: in a Suzuki 2-group `P`, the `𝔽₂`-vector space `Ω₁(P)` is,
together with the action of `ξ`, the field `GF(2 ^ n)` with `ξ` acting as multiplication by a
primitive element `ν` of order `2 ^ n - 1`.

This is the first of the `𝔽_q`-identifications needed by the `C₄` residual
(`Submission/Work/Higman/HS/NOTES_hard_two_cover.md`, ADDENDUM 16): `Ω₁(P) = A² = Z(P)` carries
the commutator pairing's value space and, through the (equivariant) squaring isomorphism, also the
layer `A/A²`.

The statement is phrased multiplicatively (`ζ : F ≃ Ω₁(P)` with `ζ (x + y) = ζ x * ζ y`) to avoid
having to expose the `ZMod 2`-module structure in the signature, exactly as
`Work.Higman.L1_iso_field` does for `P ⧸ A`.
-/
import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.exists_singer_iso
import Submission.Work.Higman.core_alt_pairing_new
import Submission.Work.Higman.omega1_iso_field
import Submission.Work.Higman.H8.frob_component

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.Higman.HS

open Work.Higman

variable {P : Type} [Group P] [Finite P]

/-- `ZMod 2` has just the two elements `0` and `1`. -/
private lemma zmod_two_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have hv : a.val = 0 ∨ a.val = 1 := by
    have h := ZMod.val_lt a
    omega
  rcases hv with hv | hv
  · left
    have h0 : (0 : ZMod 2).val = 0 := by simp
    exact ZMod.val_injective 2 (by rw [hv, h0])
  · right
    have h1 : (1 : ZMod 2).val = 1 := ZMod.val_one 2
    exact ZMod.val_injective 2 (by rw [hv, h1])

/-- **The Singer/field model of `Ω₁(P)`.**  There is a field `F` with `2 ^ n` elements (`n ≥ 2`)
and a bijection `ζ : F ≃ Ω₁(P)` which is additive (`ζ (x + y) = ζ x * ζ y`) and which intertwines
multiplication by a primitive element `ν` (of order `2 ^ n - 1`) with the action of `ξ`. -/
theorem omega1_singer_iso (h : IsSuzuki2Grp P) :
    ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (_ : DecidableEq F) (_ : CharP F 2)
      (ν : F),
      Fintype.card F = 2 ^ n ∧ 2 ≤ n ∧ orderOf ν = 2 ^ n - 1 ∧
      ∃ ζ : F ≃ ↥(Work.Higman.omega1 P),
        (∀ x y : F, ζ (x + y) = ζ x * ζ y) ∧
        (∀ x : F, ζ (ν * x) = Work.Higman.xiZ h (ζ x)) := by
  classical
  -- ## the `𝔽₂`-vector space `V = Ω₁(P)`
  let V := Additive ↥(Work.Higman.omega1 P)
  letI : AddCommGroup V :=
    { (inferInstance : AddGroup V) with
      add_comm := fun a b => by
        show Additive.ofMul (Additive.toMul a * Additive.toMul b)
          = Additive.ofMul (Additive.toMul b * Additive.toMul a)
        congr 1
        exact Subtype.ext (h.omega1_comm (Additive.toMul a).2 (Additive.toMul b).2) }
  have h2zero : ∀ x : V, 2 • x = 0 := by
    intro x
    obtain ⟨z, rfl⟩ : ∃ z : ↥(Work.Higman.omega1 P), Additive.ofMul z = x :=
      ⟨Additive.toMul x, rfl⟩
    have hzz : z * z = 1 := by
      refine Subtype.ext ?_
      show (z : P) * (z : P) = 1
      rw [← pow_two]
      exact h.mem_omega1.mp z.2
    calc 2 • (Additive.ofMul z) = Additive.ofMul z + Additive.ofMul z := two_nsmul _
      _ = Additive.ofMul (z * z) := (ofMul_mul z z).symm
      _ = 0 := by rw [hzz]; rfl
  letI : Module (ZMod 2) V := AddCommGroup.zmodModule h2zero
  -- ## the action of `ξ`
  let ξZ : ↥(Work.Higman.omega1 P) ≃* ↥(Work.Higman.omega1 P) := Work.Higman.xiZ h
  let ξVadd : V ≃+ V :=
    { toFun := fun v => Additive.ofMul (ξZ (Additive.toMul v))
      invFun := fun v => Additive.ofMul (ξZ.symm (Additive.toMul v))
      left_inv := by intro v; simp
      right_inv := by intro v; simp
      map_add' := by
        intro v w
        show Additive.ofMul (ξZ (Additive.toMul (v + w)))
          = Additive.ofMul (ξZ (Additive.toMul v)) + Additive.ofMul (ξZ (Additive.toMul w))
        rw [show Additive.toMul (v + w) = Additive.toMul v * Additive.toMul w from toMul_add v w,
          ← ofMul_mul]
        congr 1
        exact map_mul ξZ _ _ }
  have hξVadd_apply : ∀ v : V, ξVadd v = Additive.ofMul (ξZ (Additive.toMul v)) := fun v => rfl
  let σlin : V →ₗ[ZMod 2] V := AddMonoidHom.toZModLinearMap 2 (ξVadd : V →+ V)
  have hσlin_apply : ∀ v : V, σlin v = ξVadd v := fun v => rfl
  have hσlin : Function.Bijective σlin :=
    ⟨fun a b hab => ξVadd.injective (by rw [← hσlin_apply, ← hσlin_apply]; exact hab),
      fun b => ⟨ξVadd.symm b, by rw [hσlin_apply]; exact ξVadd.apply_symm_apply b⟩⟩
  let ξV : V ≃ₗ[ZMod 2] V := LinearEquiv.ofBijective σlin hσlin
  have hξV_apply : ∀ v : V, ξV v = Additive.ofMul (ξZ (Additive.toMul v)) := by
    intro v; show σlin v = _; rw [hσlin_apply]; rfl
  have hξV_pow : ∀ (k : ℕ) (v : V),
      (ξV ^ k) v = Additive.ofMul ((ξZ ^ k) (Additive.toMul v)) := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
        intro v
        rw [pow_succ', LinearEquiv.mul_apply, ih, hξV_apply, toMul_ofMul]
        congr 1
        rw [pow_succ']
        rfl
  -- ## transitivity of `ξ` on the non-zero vectors
  have hord_z : ∀ z : ↥(Work.Higman.omega1 P), z ≠ 1 → orderOf ((z : P)) = 2 := by
    intro z hz
    have hz2 : (z : P) ^ 2 = 1 := h.mem_omega1.mp z.2
    have hd : orderOf ((z : P)) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hz2
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h1
    · exact absurd (Subtype.ext (orderOf_eq_one_iff.mp h1)) hz
    · exact h1
  have htrans : ∀ a b : V, a ≠ 0 → b ≠ 0 → ∃ k : ℕ, (ξV ^ k) a = b := by
    intro a b ha hb
    have ha' : Additive.toMul a ≠ 1 := by
      intro h1; exact ha (by rw [← ofMul_toMul a, h1]; rfl)
    have hb' : Additive.toMul b ≠ 1 := by
      intro h1; exact hb (by rw [← ofMul_toMul b, h1]; rfl)
    obtain ⟨k, hk⟩ := h.trans ((Additive.toMul a : ↥(Work.Higman.omega1 P)) : P)
      ((Additive.toMul b : ↥(Work.Higman.omega1 P)) : P)
      (hord_z (Additive.toMul a) ha') (hord_z (Additive.toMul b) hb')
    refine ⟨k, ?_⟩
    rw [hξV_pow, ← ofMul_toMul b]
    congr 1
    refine Subtype.ext ?_
    rw [Work.Higman.xiZ_pow_coe h k (Additive.toMul a)]
    exact hk
  -- ## cardinality
  obtain ⟨n, hn⟩ := h.exists_card_omega1_eq_two_pow
  have hVcard : Nat.card V = 2 ^ n := hn
  have hn2 : 2 ≤ n := by
    by_contra hcon
    push_neg at hcon
    have h1 : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega : n ≤ 1)
    have h4 : 4 ≤ 2 ^ n := by rw [← hn]; exact h.omega1_card_ge_four
    norm_num at h1
    omega
  -- ## the Singer isomorphism
  obtain ⟨hVord, hVfree⟩ := Work.Higman.singer_data_of_transitive hn2 hVcard ξV htrans
  obtain ⟨φ, lam, hlamord, hφ⟩ :=
    Work.Higman.exists_singer_iso (n := n) (V := V) (by omega) hVcard ξV hVord hVfree
  letI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hFcard : Fintype.card (GaloisField 2 n) = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact Work.Higman.H8.card_galois (by omega)
  have hνord : orderOf ((lam : (GaloisField 2 n)ˣ) : GaloisField 2 n) = 2 ^ n - 1 := by
    rw [← hlamord]
    exact (orderOf_units : orderOf ((lam : (GaloisField 2 n)ˣ) : GaloisField 2 n) = orderOf lam)
  refine ⟨n, GaloisField 2 n, inferInstance, inferInstance, inferInstance, inferInstance,
    ((lam : (GaloisField 2 n)ˣ) : GaloisField 2 n), hFcard, hn2, hνord,
    φ.symm.toEquiv.trans Additive.toMul, ?_, ?_⟩
  · intro x y
    show Additive.toMul (φ.symm (x + y))
      = Additive.toMul (φ.symm x) * Additive.toMul (φ.symm y)
    rw [map_add, toMul_add]
  · intro x
    have h1 : ξV (φ.symm x) = φ.symm (((lam : (GaloisField 2 n)ˣ) : GaloisField 2 n) * x) := by
      apply φ.injective
      rw [hφ (φ.symm x), LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    show Additive.toMul (φ.symm (((lam : (GaloisField 2 n)ˣ) : GaloisField 2 n) * x))
      = ξZ (Additive.toMul (φ.symm x))
    rw [← h1, hξV_apply, toMul_ofMul]

end Work.Higman.HS
