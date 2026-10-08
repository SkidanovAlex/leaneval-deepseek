import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.A_quot_irreducible
import Submission.Work.Higman.exists_singer_iso
import Submission.Work.Higman.singer_count

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.Higman

variable {P : Type} [Group P] [Finite P]

/-! ## The automorphism `ξ` restricted to `Ω₁(P)` -/

/-- `ξ` maps `Ω₁(P)` to itself, also for the inverse automorphism. -/
theorem map_xi_inv_omega1 (h : IsSuzuki2Grp P) :
    (omega1 P).map ((h.xi : MulAut P)⁻¹).toMonoidHom = omega1 P := by
  have hcomp : (((h.xi : MulAut P)⁻¹).toMonoidHom).comp (h.xi : MulAut P).toMonoidHom
      = MonoidHom.id P := by ext x; simp
  calc (omega1 P).map ((h.xi : MulAut P)⁻¹).toMonoidHom
      = ((omega1 P).map (h.xi : MulAut P).toMonoidHom).map ((h.xi : MulAut P)⁻¹).toMonoidHom := by
        rw [map_xi_omega1 h]
    _ = (omega1 P).map ((((h.xi : MulAut P)⁻¹).toMonoidHom).comp
          (h.xi : MulAut P).toMonoidHom) := Subgroup.map_map (omega1 P) _ _
    _ = (omega1 P).map (MonoidHom.id P) := by rw [hcomp]
    _ = omega1 P := Subgroup.map_id (omega1 P)

/-- The restriction of `ξ` to `Ω₁(P)`. -/
noncomputable def xiZ (h : IsSuzuki2Grp P) : ↥(omega1 P) ≃* ↥(omega1 P) where
  toFun z := ⟨h.xi (z : P), by
    have hz : h.xi (z : P) ∈ (omega1 P).map (h.xi : MulAut P).toMonoidHom :=
      Subgroup.mem_map_of_mem _ z.2
    rwa [map_xi_omega1 h] at hz⟩
  invFun z := ⟨(h.xi : MulAut P)⁻¹ (z : P), by
    have hz : (h.xi : MulAut P)⁻¹ (z : P) ∈
        (omega1 P).map ((h.xi : MulAut P)⁻¹).toMonoidHom :=
      Subgroup.mem_map_of_mem _ z.2
    rwa [map_xi_inv_omega1 h] at hz⟩
  left_inv z := by
    apply Subtype.ext
    show (h.xi : MulAut P)⁻¹ (h.xi (z : P)) = (z : P)
    simp
  right_inv z := by
    apply Subtype.ext
    show h.xi ((h.xi : MulAut P)⁻¹ (z : P)) = (z : P)
    simp
  map_mul' z w := by
    apply Subtype.ext
    show h.xi ((z : P) * (w : P)) = h.xi (z : P) * h.xi (w : P)
    rw [map_mul]

theorem xiZ_apply (h : IsSuzuki2Grp P) (z : ↥(omega1 P)) :
    ((xiZ h z : ↥(omega1 P)) : P) = h.xi (z : P) := rfl

theorem xiZ_pow_coe (h : IsSuzuki2Grp P) (k : ℕ) (z : ↥(omega1 P)) :
    ((((xiZ h) ^ k) z : ↥(omega1 P)) : P) = (h.xi ^ k) (z : P) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ']
    change (((xiZ h) (((xiZ h) ^ k) z) : ↥(omega1 P)) : P) = (h.xi ^ (k + 1)) (z : P)
    rw [xiZ_apply, ih, pow_succ', MulAut.mul_apply]

theorem xi_pow_mul_self_eq (h : IsSuzuki2Grp P) (k : ℕ) :
    (h.xi : MulAut P) ^ k * (h.xi : MulAut P)
      = (h.xi : MulAut P) * (h.xi : MulAut P) ^ k := by
  rw [← pow_succ, pow_succ']

theorem xi_pow_mul_inv_eq (h : IsSuzuki2Grp P) (k : ℕ) :
    (h.xi : MulAut P) ^ k * (h.xi : MulAut P)⁻¹
      = (h.xi : MulAut P)⁻¹ * (h.xi : MulAut P) ^ k := by
  have hc : Commute ((h.xi : MulAut P) ^ k) ((h.xi : MulAut P)⁻¹) :=
    ((Commute.refl (h.xi : MulAut P)).pow_left k).inv_right
  exact hc.eq

/-- A non-identity element of `Ω₁(P)` has order `2`. -/
theorem omega1_orderOf_eq_two (h : IsSuzuki2Grp P) {z : P} (hz : z ∈ omega1 P) (hz1 : z ≠ 1) :
    orderOf z = 2 := by
  have hd : orderOf z ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (h.mem_omega1.mp hz)
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
  · exact absurd (orderOf_eq_one_iff.mp h1) hz1
  · exact h2

/-- **Key lemma.**  If `ξ ^ k` fixes one non-identity element of `Ω₁(P)`, then it fixes `Ω₁(P)`
pointwise: the fixed points form a non-trivial `ξ`-invariant subgroup of `Ω₁(P)`, which must be
all of `Ω₁(P)` since `ξ` acts transitively on the involutions. -/
theorem xi_pow_fixed_omega1 (h : IsSuzuki2Grp P) {k : ℕ} {z : P}
    (hz : z ∈ omega1 P) (hz1 : z ≠ 1) (hfix : (h.xi ^ k) z = z) :
    ∀ y ∈ omega1 P, (h.xi ^ k) y = y := by
  let S : Subgroup P :=
    { carrier := {y | y ∈ omega1 P ∧ (h.xi ^ k) y = y}
      one_mem' := ⟨Subgroup.one_mem _, map_one _⟩
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by rw [map_mul, ha.2, hb.2]⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [map_inv, ha.2]⟩ }
  have hSle : S ≤ omega1 P := fun y hy => hy.1
  have hSne : S ≠ ⊥ := by
    intro hbot
    have hzS : z ∈ S := ⟨hz, hfix⟩
    rw [hbot] at hzS
    exact hz1 (Subgroup.mem_bot.mp hzS)
  have hSinv : S.map (h.xi : MulAut P).toMonoidHom = S := by
    apply le_antisymm
    · rintro y ⟨x, hx, rfl⟩
      refine ⟨?_, ?_⟩
      · have hmem : h.xi x ∈ (omega1 P).map (h.xi : MulAut P).toMonoidHom :=
          Subgroup.mem_map_of_mem _ hx.1
        rwa [map_xi_omega1 h] at hmem
      · change (h.xi ^ k) (h.xi x) = h.xi x
        rw [← MulAut.mul_apply, xi_pow_mul_self_eq h k, MulAut.mul_apply, hx.2]
    · intro y hy
      refine ⟨(h.xi : MulAut P)⁻¹ y, ⟨?_, ?_⟩, by simp⟩
      · have hmem : (h.xi : MulAut P)⁻¹ y ∈
            (omega1 P).map ((h.xi : MulAut P)⁻¹).toMonoidHom :=
          Subgroup.mem_map_of_mem _ hy.1
        rwa [map_xi_inv_omega1 h] at hmem
      · rw [← MulAut.mul_apply, xi_pow_mul_inv_eq h k, MulAut.mul_apply, hy.2]
  have hSeq : S = omega1 P := by
    rcases inf_omega1_eq_bot_or_top h (A := ⊤) (by simpa using hSle) hSinv with h | h
    · exact absurd h hSne
    · simpa using h
  intro y hy
  have : y ∈ S := by rw [hSeq]; exact hy
  exact this.2

/-- **`Ω₁(P)` is a finite field with a Singer cycle.**

Let `P` be a Suzuki 2-group and put `Z := Ω₁(P)`, the elementary abelian `ξ`-invariant subgroup
generated by the involutions, on which `ξ` acts transitively on the non-identity elements
(`Work.Higman.IsSuzuki2Grp.trans`).  Then there are `n ≥ 2`, a finite field `F` of characteristic
`2` with `|F| = 2 ^ n`, an element `μ ∈ F` of multiplicative order `2 ^ n - 1`, and a bijection
`ζ : F ≃ Z` with `ζ (x + y) = ζ x * ζ y` and `ζ (μ * x) = ξ (ζ x)` (the latter read in `P`,
`ζ (μ*x)` coerced to `P`).

Route: `Z` has order `2 ^ n` for a unique `n` (`Work.Higman.exists_card_omega1_eq_two_pow`), and
`n ≥ 2` (`Work.Higman.omega1_card_ge_four`).  View `Z` as a `ZMod 2`-module
(`AddCommGroup.zmodModule`, using `Work.Higman.IsSuzuki2Grp.mem_omega1`) and let `ξ` act on it as
a linear equivalence (`MulEquiv.toAdditive` + `AddEquiv.toLinearEquiv`).  Then `orderOf ξ = 2^n-1`
(it is transitive on `Z \ {1}`, and any fixed point of `ξ ^ k` other than `1` generates the whole
irreducible module, so `ξ ^ k = 1`), and `ξ` is fixed-point free (`v ≠ 0` generates `Z` because
`Z` has no proper non-trivial `ξ`-invariant subgroup,
`Work.Higman.eq_omega1_of_ne_bot_of_map_eq`).  Apply `Work.Higman.exists_singer_iso`
(`Submission/Work/Higman/exists_singer_iso.lean`) to get the linear equivalence
`V ≃ₗ[ZMod 2] GaloisField 2 n` intertwining `ξ` with multiplication by a generator `λ`;  transport
it along `Z ≅ Additive Z` to obtain `ζ`, and take `μ := λ`. -/
theorem omega1_iso_field {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P) :
    ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (_ : DecidableEq F) (_ : CharP F 2)
      (mu : F),
      Fintype.card F = 2 ^ n ∧ 2 ≤ n ∧ orderOf mu = 2 ^ n - 1 ∧ mu ≠ 0 ∧
      ∃ ζ : F ≃ ↥(Work.Higman.omega1 P), (∀ x y : F, ζ (x + y) = ζ x * ζ y) ∧
        (∀ x : F, ζ (mu * x) = h.xi (ζ x)) := by
  classical
  -- ## Step 0: `|Ω₁(P)| = 2 ^ n` with `n ≥ 2`
  obtain ⟨n, hcardZ⟩ := h.exists_card_omega1_eq_two_pow
  have hcard4 : 4 ≤ Nat.card (omega1 P) := h.omega1_card_ge_four
  have hn2 : 2 ≤ n := by
    by_contra hcon
    have h1 : n ≤ 1 := by omega
    have h2 : 2 ^ n ≤ 2 := by
      calc 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
        _ = 2 := by norm_num
    omega
  have hnpos : 0 < n := by omega
  -- ## Step 1: `Ω₁(P)` as a `ZMod 2`-module
  letI : CommGroup ↥(omega1 P) :=
    { (inferInstance : Group ↥(omega1 P)) with
      mul_comm := fun a b => Subtype.ext (h.omega1_comm a.2 b.2) }
  let V := Additive ↥(omega1 P)
  letI : Module (ZMod 2) V := AddCommGroup.zmodModule (fun x => by
    obtain ⟨z, rfl⟩ : ∃ z : ↥(omega1 P), Additive.ofMul z = x := ⟨Additive.toMul x, rfl⟩
    rw [two_nsmul, ← ofMul_mul, ofMul_eq_zero]
    apply Subtype.ext
    show (z : P) * (z : P) = (1 : P)
    rw [← pow_two, h.omega1_sq_eq_one z.2])
  -- ## Step 2: `ξ` on `V` as a linear equivalence
  let lamH : V →ₗ[ZMod 2] V := AddMonoidHom.toZModLinearMap 2 ((xiZ h).toAdditive : V →+ V)
  let lam : V ≃ₗ[ZMod 2] V := LinearEquiv.ofBijective lamH (by
    have hb : Function.Bijective ((xiZ h).toAdditive : V → V) := (xiZ h).toAdditive.bijective
    simpa [lamH, AddMonoidHom.coe_toZModLinearMap] using hb)
  have lam_ofMul : ∀ z : ↥(omega1 P), lam (Additive.ofMul z) = Additive.ofMul (xiZ h z) := by
    intro z
    show lamH (Additive.ofMul z) = Additive.ofMul (xiZ h z)
    simp only [lamH, AddMonoidHom.coe_toZModLinearMap]
    rfl
  have lam_pow_ofMul : ∀ (k : ℕ) (z : ↥(omega1 P)),
      (lam ^ k) (Additive.ofMul z) = Additive.ofMul (((xiZ h) ^ k) z) := by
    intro k
    induction k with
    | zero => intro z; simp
    | succ k ih =>
      intro z
      rw [pow_succ', LinearEquiv.mul_apply, ih, lam_ofMul, pow_succ']
      rfl
  -- ## Step 3: cardinality of `V`
  have hV : Nat.card V = 2 ^ n := by
    show Nat.card (Additive ↥(omega1 P)) = 2 ^ n
    rw [← Nat.card_congr Additive.ofMul]
    exact hcardZ
  haveI : Fintype V := Fintype.ofFinite V
  haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by
    rw [← Nat.card_eq_fintype_card, hV]
    calc (1 : ℕ) < 4 := by norm_num
      _ ≤ 2 ^ n := by
        calc (4 : ℕ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2)
  obtain ⟨w₀, hw₀⟩ := exists_ne (0 : V)
  -- ## Step 4: `lam` is transitive on the non-zero vectors
  have htrans : ∀ u w : V, u ≠ 0 → w ≠ 0 → ∃ k : ℕ, (lam ^ k) u = w := by
    intro u w hu hw
    obtain ⟨x, rfl⟩ : ∃ x : ↥(omega1 P), Additive.ofMul x = u := ⟨Additive.toMul u, rfl⟩
    obtain ⟨y, rfl⟩ : ∃ y : ↥(omega1 P), Additive.ofMul y = w := ⟨Additive.toMul w, rfl⟩
    have hx1 : (x : P) ≠ 1 := fun hc => hu (ofMul_eq_zero.mpr (Subtype.ext hc))
    have hy1 : (y : P) ≠ 1 := fun hc => hw (ofMul_eq_zero.mpr (Subtype.ext hc))
    have hx2 : orderOf (x : P) = 2 := omega1_orderOf_eq_two h x.2 hx1
    have hy2 : orderOf (y : P) = 2 := omega1_orderOf_eq_two h y.2 hy1
    obtain ⟨k, hk⟩ := h.trans (x : P) (y : P) hx2 hy2
    exact ⟨k, by
      rw [lam_pow_ofMul]
      exact congrArg Additive.ofMul (Subtype.ext (by rw [xiZ_pow_coe]; exact hk))⟩
  -- ## Step 5: the stabiliser of a non-zero vector is trivial
  have hfix : ∀ k : ℕ, (lam ^ k) w₀ = w₀ → lam ^ k = 1 := by
    intro k hk
    obtain ⟨z, rfl⟩ : ∃ z : ↥(omega1 P), Additive.ofMul z = w₀ := ⟨Additive.toMul w₀, rfl⟩
    have hz1 : (z : P) ≠ 1 := fun hc => hw₀ (ofMul_eq_zero.mpr (Subtype.ext hc))
    have hkeq : ((xiZ h) ^ k) z = z := by
      have h1 := congrArg Additive.toMul hk
      rw [lam_pow_ofMul] at h1
      simpa using h1
    have hfixP : (h.xi ^ k) (z : P) = (z : P) := by
      have h1 := congrArg (fun w : ↥(omega1 P) => (w : P)) hkeq
      rwa [xiZ_pow_coe] at h1
    have hfixall := xi_pow_fixed_omega1 h z.2 hz1 hfixP
    have hxiZk : (xiZ h) ^ k = 1 := by
      apply MulEquiv.ext
      intro w
      apply Subtype.ext
      rw [xiZ_pow_coe]
      exact hfixall (w : P) w.2
    apply LinearEquiv.ext
    intro v
    obtain ⟨y, rfl⟩ : ∃ y : ↥(omega1 P), Additive.ofMul y = v := ⟨Additive.toMul v, rfl⟩
    rw [lam_pow_ofMul, hxiZk]
    rfl
  -- ## Step 6: order and fixed-point-freeness
  obtain ⟨hord, hfree⟩ := singer_count hn2 hV lam w₀ hw₀ htrans hfix
  -- ## Step 7: the Singer-cycle field isomorphism
  obtain ⟨φ, lam0, hlam0ord, hφ⟩ := exists_singer_iso hnpos hV lam hord hfree
  let ζ : GaloisField 2 n ≃ ↥(omega1 P) :=
    { toFun := fun y => Additive.toMul (φ.symm y)
      invFun := fun z => φ (Additive.ofMul z)
      left_inv := fun y => by simp
      right_inv := fun z => by simp }
  have hζadd : ∀ x y : GaloisField 2 n, ζ (x + y) = ζ x * ζ y := by
    intro x y
    show Additive.toMul (φ.symm (x + y)) = Additive.toMul (φ.symm x) * Additive.toMul (φ.symm y)
    rw [map_add, toMul_add]
  have hζmul : ∀ x : GaloisField 2 n, ζ ((lam0 : GaloisField 2 n) * x) = h.xi (ζ x) := by
    intro x
    have hsym : φ.symm ((lam0 : GaloisField 2 n) * x) = lam (φ.symm x) := by
      have h1 : φ (lam (φ.symm x)) = (lam0 : GaloisField 2 n) * x := by
        rw [hφ (φ.symm x), LinearEquiv.apply_symm_apply]
      rw [← h1, LinearEquiv.symm_apply_apply]
    have key : Additive.toMul (lam (φ.symm x)) = xiZ h (Additive.toMul (φ.symm x)) := by
      rw [show φ.symm x = Additive.ofMul (Additive.toMul (φ.symm x)) from rfl, lam_ofMul]
      rfl
    show ((ζ ((lam0 : GaloisField 2 n) * x) : ↥(omega1 P)) : P)
        = h.xi ((ζ x : ↥(omega1 P)) : P)
    show ((Additive.toMul (φ.symm ((lam0 : GaloisField 2 n) * x)) : ↥(omega1 P)) : P)
        = h.xi ((Additive.toMul (φ.symm x) : ↥(omega1 P)) : P)
    rw [hsym, key]
    exact xiZ_apply h (Additive.toMul (φ.symm x))
  -- ## Step 8: assembly
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  refine ⟨n, GaloisField 2 n, inferInstance, inferInstance, inferInstance, inferInstance,
    (lam0 : GaloisField 2 n), ?_, hn2, ?_, ?_, ζ, hζadd, hζmul⟩
  · rw [← Nat.card_eq_fintype_card]; exact GaloisField.card 2 n hnpos.ne'
  · rw [orderOf_units]; exact hlam0ord
  · exact Units.ne_zero lam0

end Work.Higman
