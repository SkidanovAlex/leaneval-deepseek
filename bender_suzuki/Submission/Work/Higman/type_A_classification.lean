import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.CoordDefs
import Submission.Work.Higman.cocy_props
import Submission.Work.Higman.nonempty_twoStepModel
import Submission.Work.Higman.exists_additive_coboundary
import Submission.Work.Higman.no_equivariant_linearEquiv
import Submission.Work.Higman.exists_linearEquiv_monomial
import Submission.Work.Higman.invol_ncard_dvd_orderOf_xi
import Submission.Work.Higman.q2_squaring_coordinates
import Submission.Work.Higman.type_A_chain
import Submission.Work.Higman.center_eq_omega1_of_sq_mem_center

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
open IsMulCommutative

namespace Work.Higman

variable {P : Type} [Group P] [Finite P]

/-- Local notation for the centre, to keep the assembly below readable. -/
local notation "Z" => Subgroup.center P

/-! ## Assembly of the type-`A` normal form

Downstream of the coordinate data of `Work.Higman.q2_squaring_coordinates`: group coordinates `Φ`
on the quotient `P ⧸ Z(P)` and `Ψ` on the centre `Z(P)`, in which the squaring map is the twisted
product `α ↦ α * θ α`.

The remaining step is a two-step cocycle computation.  Choose a section `s` of `P → P ⧸ Z(P)` with
`s 0 = 1` and let `b u v = s u * s v * (s (u + v))⁻¹` be its cocycle.  Then `b` is biadditive and
`b v v` is the square of `s v`, so `c u v = Ψ (b u v) + Φ u * θ (Φ v)` is an alternating
biadditive form; by `Work.Higman.exists_additive_coboundary` it is a coboundary, and the
corresponding `x ↦ (Φ (xZ), Ψ (…) + f (xZ))` is the required equivalence. -/

/-- Every commutator is central when every square is central. -/
theorem commutator_mem_center_of_sq (hb : ∀ x : P, x ^ 2 ∈ Subgroup.center P) (a b : P) :
    ⁅a, b⁆ ∈ Subgroup.center P := by
  have h := commutator_mem_center_of_sq_mem_center hb a b
  simpa [commutatorElement_def] using h

/-- The quotient of `P` by its centre has exponent dividing two when every square is central. -/
theorem quot_mul_self_eq_one (hb : ∀ x : P, x ^ 2 ∈ Subgroup.center P)
    (v : P ⧸ Subgroup.center P) : v * v = 1 := by
  induction v using QuotientGroup.induction_on with
  | H x =>
      rw [← QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (x * x)).mpr]
      simpa [pow_two] using hb x

/-- **Assembly.**  Given group coordinates `Φ` on `P ⧸ Z(P)` and `Ψ` on `Z(P)` in which the
squaring map is the twisted product `α * θ α`, the group `P` is `A(n, θ)`. -/
theorem type_A_assembly
    (hb : ∀ x : P, x ^ 2 ∈ Subgroup.center P)
    (hexp : ∀ z ∈ Subgroup.center P, z ^ 2 = 1)
    {n : ℕ} {θ : GaloisField 2 n ≃+* GaloisField 2 n}
    (Φ : (P ⧸ Subgroup.center P) ≃ GaloisField 2 n)
    (hΦ : ∀ v w : P ⧸ Subgroup.center P, Φ (v * w) = Φ v + Φ w)
    (Ψ : ↥(Subgroup.center P) ≃ GaloisField 2 n)
    (hΨ : ∀ z w : ↥(Subgroup.center P), Ψ (z * w) = Ψ z + Ψ w)
    (hsq : ∀ x : P, Ψ ⟨x ^ 2, hb x⟩ = Φ (QuotientGroup.mk x) * θ (Φ (QuotientGroup.mk x))) :
    ∃ e : P ≃ GaloisField 2 n × GaloisField 2 n,
      ∀ x y : P, e (x * y) =
        ((e x).1 + (e y).1, (e x).2 + (e y).2 + (e x).1 * θ (e y).1) := by
  classical
  have hcomm : ∀ a b : P, ⁅a, b⁆ ∈ Z := fun a b => commutator_mem_center_of_sq hb a b
  -- ## the additive group `V = P ⧸ Z`
  haveI hcommq : IsMulCommutative (P ⧸ Z) := by
    refine IsMulCommutative.of_comm ?_
    intro x y
    have hx : x⁻¹ = x := inv_eq_of_mul_eq_one_right (quot_mul_self_eq_one hb x)
    have hy : y⁻¹ = y := inv_eq_of_mul_eq_one_right (quot_mul_self_eq_one hb y)
    have hxy : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right (quot_mul_self_eq_one hb (x * y))
    rw [← hxy, mul_inv_rev, hx, hy]
  have hV2 : ∀ v : Additive (P ⧸ Z), v + v = 0 := by
    intro v
    apply Additive.ext
    rw [toMul_add, toMul_zero]
    exact quot_mul_self_eq_one hb (Additive.toMul v)
  haveI hVmod : Module (ZMod 2) (Additive (P ⧸ Z)) :=
    AddCommGroup.zmodModule (by intro x; rw [two_nsmul]; exact hV2 x)
  haveI hVmodfin : Module.Finite (ZMod 2) (Additive (P ⧸ Z)) := Module.Finite.of_finite
  -- ## a section of `P → V` with `s 0 = 1`, built from a basis
  let nV : ℕ := Module.finrank (ZMod 2) (Additive (P ⧸ Z))
  let bb : Module.Basis (Fin nV) (ZMod 2) (Additive (P ⧸ Z)) :=
    Module.finBasis (ZMod 2) (Additive (P ⧸ Z))
  let eq : Additive (P ⧸ Z) ≃ₗ[ZMod 2] (Fin nV → ZMod 2) := bb.equivFun
  have hsurj : ∀ i : Fin nV, ∃ x : P,
      (QuotientGroup.mk x : P ⧸ Z) = Additive.toMul (bb i) :=
    fun i => QuotientGroup.mk'_surjective Z (Additive.toMul (bb i))
  let A : Fin nV → P := fun i => Classical.choose (hsurj i)
  have hA : ∀ i, (QuotientGroup.mk (A i) : P ⧸ Z) = Additive.toMul (bb i) :=
    fun i => Classical.choose_spec (hsurj i)
  let π' : P → Additive (P ⧸ Z) := fun x => Additive.ofMul (QuotientGroup.mk x)
  have hπ : ∀ x y : P, π' (x * y) = π' x + π' y := by
    intro x y
    simp only [π', QuotientGroup.mk_mul, ofMul_mul]
  have hπ1 : π' 1 = 0 := by
    simp only [π', QuotientGroup.mk_one, ofMul_one]
  have hπcenter : ∀ z ∈ Z, π' z = 0 := by
    intro z hz
    simp only [π']
    rw [(QuotientGroup.eq_one_iff z).mpr hz, ofMul_one]
  have hπA : ∀ i, π' (A i) = bb i := by
    intro i
    simp only [π', hA i, ofMul_toMul]
  let s : Additive (P ⧸ Z) → P := fun v => coordSec nV A (eq v)
  have hs : ∀ v : Additive (P ⧸ Z), π' (s v) = v := by
    intro v
    rw [pi_coordSec π' hπ hπ1 nV A bb hπA (eq v)]
    rw [← Module.Basis.equivFun_symm_apply bb (eq v)]
    exact eq.symm_apply_apply v
  have hsmk : ∀ v : Additive (P ⧸ Z), (QuotientGroup.mk (s v) : P ⧸ Z) = Additive.toMul v := by
    intro v
    have h := congrArg Additive.toMul (hs v)
    simpa [π'] using h
  have hs0 : s 0 = 1 := by
    simp only [s, map_zero]
    exact coordSec_zero_fun nV A
  -- ## the cocycle of the section `s`
  have hcocy : (∀ a b : P, a * b * a⁻¹ * b⁻¹ ∈ Z) := by
    intro a b
    simpa [commutatorElement_def] using hcomm a b
  obtain ⟨hL, hR, hMem⟩ := cocy_props hcocy hb hexp nV A
  let b : Additive (P ⧸ Z) → Additive (P ⧸ Z) → ↥Z :=
    fun v w => ⟨cocy nV A (eq v) (eq w), hMem (eq v) (eq w)⟩
  have hbL : ∀ a a' c : Additive (P ⧸ Z), b (a + a') c = b a c * b a' c := by
    intro a a' c
    apply Subtype.ext
    simp only [b]
    rw [map_add]
    exact hL (eq a) (eq a') (eq c)
  have hbR : ∀ a c c' : Additive (P ⧸ Z), b a (c + c') = b a c * b a c' := by
    intro a c c'
    apply Subtype.ext
    simp only [b]
    rw [map_add]
    exact hR (eq a) (eq c) (eq c')
  have hsvw : ∀ v w : Additive (P ⧸ Z),
      s v * s w = ((b v w : ↥Z) : P) * s (v + w) := by
    intro v w
    simp only [b, s, cocy]
    rw [map_add]
    group
  have hbdiag : ∀ v : Additive (P ⧸ Z), ((b v v : ↥Z) : P) = s v ^ 2 := by
    intro v
    have h2 : eq v + eq v = 0 := by
      ext i
      exact CharTwo.add_self_eq_zero _
    have h3 : coordSec nV A (eq v + eq v) = 1 := by
      rw [h2]
      exact coordSec_zero_fun nV A
    simp only [b, cocy, s, h3, inv_one, mul_one]
    rw [pow_two]
  -- ## the alternating biadditive form `cd` and its coboundary
  let Φv : Additive (P ⧸ Z) → GaloisField 2 n := fun v => Φ (Additive.toMul v)
  have hΦv : ∀ a c : Additive (P ⧸ Z), Φv (a + c) = Φv a + Φv c := by
    intro a c
    simp only [Φv, toMul_add]
    exact hΦ _ _
  have hΦ1 : Φ 1 = 0 := by
    have h := hΦ 1 1
    rw [one_mul] at h
    rw [h]
    exact CharTwo.add_self_eq_zero _
  let cd : Additive (P ⧸ Z) → Additive (P ⧸ Z) → GaloisField 2 n :=
    fun a c => Ψ (b a c) + Φv a * θ (Φv c)
  have hcd1 : ∀ a a' c : Additive (P ⧸ Z), cd (a + a') c = cd a c + cd a' c := by
    intro a a' c
    simp only [cd, hbL a a' c, hΨ, hΦv a a']
    ring
  have hcd2 : ∀ a c c' : Additive (P ⧸ Z), cd a (c + c') = cd a c + cd a c' := by
    intro a c c'
    simp only [cd, hbR a c c', hΨ, hΦv c c', map_add, mul_add]
    ring
  have hcdalt : ∀ a : Additive (P ⧸ Z), cd a a = 0 := by
    intro a
    have h2 : b a a = ⟨s a ^ 2, by rw [← hbdiag a]; exact (b a a).2⟩ :=
      Subtype.ext (by simpa using hbdiag a)
    have h1 : Ψ (b a a) = Φv a * θ (Φv a) := by
      rw [h2, hsq (s a)]
      simp only [Φv]
      rw [hsmk a]
    simp only [cd, h1]
    exact CharTwo.add_self_eq_zero _
  obtain ⟨f, hf⟩ := exists_additive_coboundary cd hcd1 hcd2 hcdalt
  -- ## the coordinate equivalence
  have hzmem : ∀ x : P, (s (π' x))⁻¹ * x ∈ Z := by
    intro x
    have h1 : QuotientGroup.mk' Z ((s (π' x))⁻¹ * x) = 1 := by
      rw [map_mul, map_inv]
      have h2 : QuotientGroup.mk' Z (s (π' x)) = QuotientGroup.mk' Z x := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, hsmk]
        rfl
      rw [h2, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).mp (by simpa [QuotientGroup.mk'_apply] using h1)
  let Φe : Additive (P ⧸ Z) ≃ GaloisField 2 n :=
    { toFun := Φv
      invFun := fun a => Additive.ofMul (Φ.symm a)
      left_inv := fun a => by simp only [Φv, Equiv.symm_apply_apply, ofMul_toMul]
      right_inv := fun a => by simp only [Φv, Equiv.apply_symm_apply, toMul_ofMul] }
  let efun : P → GaloisField 2 n × GaloisField 2 n :=
    fun u => (Φv (π' u), Ψ ⟨(s (π' u))⁻¹ * u, hzmem u⟩ + f (π' u))
  have hinj : Function.Injective efun := by
    intro u u' h
    have h1 : Φv (π' u) = Φv (π' u') := congrArg Prod.fst h
    have h2 : Ψ ⟨(s (π' u))⁻¹ * u, hzmem u⟩ + f (π' u)
        = Ψ ⟨(s (π' u'))⁻¹ * u', hzmem u'⟩ + f (π' u') := congrArg Prod.snd h
    have h1' : Φe (π' u) = Φe (π' u') := h1
    have h3 : π' u = π' u' := by
      rw [← Equiv.symm_apply_apply Φe (π' u), h1', Equiv.symm_apply_apply Φe (π' u')]
    have hc : f (π' u) = f (π' u') := congrArg f h3
    have h4 : Ψ ⟨(s (π' u))⁻¹ * u, hzmem u⟩ = Ψ ⟨(s (π' u'))⁻¹ * u', hzmem u'⟩ := by
      have h2c := h2
      rw [hc] at h2c
      exact add_right_cancel h2c
    have h5 : (s (π' u))⁻¹ * u = (s (π' u'))⁻¹ * u' := by
      have hv := congrArg (fun z : ↥Z => (z : P)) (Ψ.injective h4)
      simpa using hv
    rw [h3] at h5
    exact mul_left_cancel h5
  have hsurj : Function.Surjective efun := by
    rintro ⟨a, b⟩
    refine ⟨s (Φe.symm a) * ((Ψ.symm (b - f (Φe.symm a))) : P), ?_⟩
    have hπv : π' (s (Φe.symm a) * ((Ψ.symm (b - f (Φe.symm a))) : P)) = Φe.symm a := by
      rw [hπ, hs (Φe.symm a), hπcenter _ (Ψ.symm (b - f (Φe.symm a))).2, add_zero]
    have hze : (⟨(s (π' (s (Φe.symm a) * ((Ψ.symm (b - f (Φe.symm a))) : P))))⁻¹ *
        (s (Φe.symm a) * ((Ψ.symm (b - f (Φe.symm a))) : P)),
        hzmem (s (Φe.symm a) * ((Ψ.symm (b - f (Φe.symm a))) : P))⟩ : ↥Z) =
        Ψ.symm (b - f (Φe.symm a)) := by
      apply Subtype.ext
      show (s (π' (s (Φe.symm a) * ((Ψ.symm (b - f (Φe.symm a))) : P))))⁻¹ *
        (s (Φe.symm a) * ((Ψ.symm (b - f (Φe.symm a))) : P)) =
        ((Ψ.symm (b - f (Φe.symm a))) : P)
      rw [hπv]
      group
    have hpt : π' (s (Φe.symm a) * ((Ψ.symm (b - f (Φe.symm a))) : P)) = Φe.symm a := hπv
    refine Prod.ext ?_ ?_
    · show Φv (π' (s (Φe.symm a) * ((Ψ.symm (b - f (Φe.symm a))) : P))) = a
      rw [hpt]
      exact Φe.apply_symm_apply a
    · show Ψ ⟨(s (π' (s (Φe.symm a) * ((Ψ.symm (b - f (Φe.symm a))) : P))))⁻¹ *
          (s (Φe.symm a) * ((Ψ.symm (b - f (Φe.symm a))) : P)),
          hzmem (s (Φe.symm a) * ((Ψ.symm (b - f (Φe.symm a))) : P))⟩ +
          f (π' (s (Φe.symm a) * ((Ψ.symm (b - f (Φe.symm a))) : P))) = b
      rw [hze, hpt, Ψ.apply_symm_apply, sub_add_cancel]
  have hcent : ∀ (z : ↥Z) (u : P), ((z : P)) * u = u * z := fun z u =>
    (Subgroup.mem_center_iff.mp z.2 u).symm
  -- the theorem
  refine ⟨Equiv.ofBijective efun ⟨hinj, hsurj⟩, ?_⟩
  intro x y
  set zx : ↥Z := ⟨(s (π' x))⁻¹ * x, hzmem x⟩ with hzx
  set zy : ↥Z := ⟨(s (π' y))⁻¹ * y, hzmem y⟩ with hzy
  have hx : x = s (π' x) * (zx : P) := by rw [hzx]; group
  have hy : y = s (π' y) * (zy : P) := by rw [hzy]; group
  have hx' : s (π' x) * (zx : P) = x := hx.symm
  have hy' : s (π' y) * (zy : P) = y := hy.symm
  have hZcomp : (⟨(s (π' (x * y)))⁻¹ * (x * y), hzmem (x * y)⟩ : ↥Z)
      = b (π' x) (π' y) * zx * zy := by
    apply Subtype.ext
    show (s (π' (x * y)))⁻¹ * (x * y) = ((b (π' x) (π' y) : ↥Z) : P) * (zx : P) * (zy : P)
    have step1 : (s (π' (x * y)))⁻¹ * (x * y)
        = (s (π' x + π' y))⁻¹ * ((s (π' x) * (zx : P)) * (s (π' y) * (zy : P))) := by
      rw [hx', hy', ← hπ x y]
    have step2 : (s (π' x) * (zx : P)) * (s (π' y) * (zy : P))
        = (s (π' x) * s (π' y)) * ((zx : P) * (zy : P)) := by
      calc (s (π' x) * (zx : P)) * (s (π' y) * (zy : P))
          = s (π' x) * ((zx : P) * (s (π' y) * (zy : P))) := by group
        _ = s (π' x) * (((zx : P) * s (π' y)) * (zy : P)) := by group
        _ = s (π' x) * ((s (π' y) * (zx : P)) * (zy : P)) := by rw [hcent zx (s (π' y))]
        _ = (s (π' x) * s (π' y)) * ((zx : P) * (zy : P)) := by group
    have step3 : (s (π' x + π' y))⁻¹ * ((s (π' x) * s (π' y)) * ((zx : P) * (zy : P)))
        = ((b (π' x) (π' y) : ↥Z) : P) * (zx : P) * (zy : P) := by
      rw [hsvw (π' x) (π' y), hcent (b (π' x) (π' y)) (s (π' x + π' y))]
      group
    rw [step1, step2, step3]
  have hkey : f (π' x + π' y) =
      (f (π' x) + f (π' y)) + (Ψ (b (π' x) (π' y)) + Φv (π' x) * θ (Φv (π' y))) := by
    have h := hf (π' x) (π' y)
    simp only [cd] at h
    calc f (π' x + π' y)
        = (f (π' x + π' y) + (f (π' x) + f (π' y))) + (f (π' x) + f (π' y)) := by
            rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      _ = (Ψ (b (π' x) (π' y)) + Φv (π' x) * θ (Φv (π' y))) + (f (π' x) + f (π' y)) := by
            rw [h]
      _ = (f (π' x) + f (π' y)) + (Ψ (b (π' x) (π' y)) + Φv (π' x) * θ (Φv (π' y))) := by
            abel
  show efun (x * y) = ((efun x).1 + (efun y).1, (efun x).2 + (efun y).2 + (efun x).1 * θ (efun y).1)
  simp only [efun]
  rw [hZcomp, ← hzx, ← hzy, hπ x y, hkey]
  refine Prod.ext (hΦv (π' x) (π' y)) ?_
  simp only [hΨ]
  rw [show (Ψ (b (π' x) (π' y)) + Ψ zx) + Ψ zy +
        ((f (π' x) + f (π' y)) + (Ψ (b (π' x) (π' y)) + Φv (π' x) * θ (Φv (π' y))))
      = (Ψ zx + f (π' x) + (Ψ zy + f (π' y))) +
        (Ψ (b (π' x) (π' y)) + Ψ (b (π' x) (π' y))) + (Φv (π' x) * θ (Φv (π' y))) from by
        abel]
  rw [CharTwo.add_self_eq_zero, add_zero]

/-! ## The regularity input

`Work.Higman.xi_regular` produces an automorphism of order `|Invol P|` permuting the involutions
transitively; its proof needs the "crux" that an automorphism fixing `Ω₁(P)` pointwise has order
coprime to `|Invol P|`.  In the `|P| = |Z(P)|²` case that crux is elementary (and in fact the
order is a power of `2`), as shown below. -/

/-- A non-identity element of `Ω₁(P)` has order two. -/
theorem q2_orderOf_eq_two_of_mem_omega1 (h : Work.Higman.IsSuzuki2Grp P) {x : P}
    (hx : x ∈ Work.Higman.omega1 P) (hx1 : x ≠ 1) : orderOf x = 2 := by
  have hd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (h.mem_omega1.mp hx)
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
  · exact absurd (orderOf_eq_one_iff.mp h1) hx1
  · exact h2

/-- The orbit of an involution under `⟨ξ⟩` is the set of all involutions. -/
theorem q2_orbit_zpowers_eq_Invol (h : Work.Higman.IsSuzuki2Grp P) {x : P}
    (hx : orderOf x = 2) :
    (MulAction.orbit (Subgroup.zpowers h.xi) x : Set P) = Work.Higman.Invol P := by
  ext z
  rw [MulAction.mem_orbit_iff, mem_Invol]
  refine ⟨?_, ?_⟩
  · rintro ⟨ψ, rfl⟩
    show orderOf (ψ • x) = 2
    rw [show ψ • x = (ψ : MulAut P) x from rfl, MulEquiv.orderOf_eq, hx]
  · intro hz
    obtain ⟨k, hk⟩ := h.trans x z hx hz
    exact ⟨⟨h.xi ^ k, Subgroup.pow_mem (Subgroup.zpowers h.xi)
      (Subgroup.mem_zpowers h.xi) k⟩, hk⟩

/-- If an element of `⟨ξ⟩` fixes one involution it fixes `Ω₁(P)` pointwise. -/
theorem q2_fixes_omega1_of_mem_zpowers_fixes_invol (h : Work.Higman.IsSuzuki2Grp P) {z₀ : P}
    (hz₀ : orderOf z₀ = 2) {φ : MulAut P} (hφK : φ ∈ Subgroup.zpowers h.xi)
    (hφz : φ z₀ = z₀) : ∀ w : P, w ∈ Work.Higman.omega1 P → φ w = w := by
  intro w hw
  rcases eq_or_ne w 1 with rfl | hw1
  · simp
  · have hw2 : orderOf w = 2 := q2_orderOf_eq_two_of_mem_omega1 h hw hw1
    have hworb : w ∈ MulAction.orbit (Subgroup.zpowers h.xi) z₀ := by
      rw [q2_orbit_zpowers_eq_Invol h hz₀, mem_Invol]; exact hw2
    rw [MulAction.mem_orbit_iff] at hworb
    obtain ⟨ψ, hψw⟩ := hworb
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hφK
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp ψ.2
    have hψz : ψ.1 z₀ = w := hψw
    calc φ w = φ (ψ.1 z₀) := by rw [hψz]
      _ = (φ * ψ.1) z₀ := by rw [MulAut.mul_apply]
      _ = ((h.xi ^ i) * (h.xi ^ j)) z₀ := by rw [← hi, ← hj]
      _ = (h.xi ^ (i + j)) z₀ := by rw [zpow_add]
      _ = (h.xi ^ (j + i)) z₀ := by rw [add_comm]
      _ = ((h.xi ^ j) * (h.xi ^ i)) z₀ := by rw [zpow_add]
      _ = (ψ.1 * φ) z₀ := by rw [← hi, ← hj]
      _ = ψ.1 (φ z₀) := by rw [MulAut.mul_apply]
      _ = ψ.1 z₀ := by rw [hφz]
      _ = w := hψz

/-- **The `Ω₁`-fixer has `2`-power order.**  If `|P| = |Z(P)| ^ 2`, every square of `P` is
central and `Z(P) = Ω₁(P)`, then any automorphism of `P` fixing `Ω₁(P)` pointwise has order
dividing `2`.

Indeed the squaring map descends to `Q : P ⧸ Z(P) → Z(P)` (well defined because the centre is
elementary abelian and squares are central).  The image of `Q` is `ξ`-invariant, contains `1` and
meets `Ω₁(P) ∖ {1}`; since `Ω₁(P) ∖ {1}` is a single `ξ`-orbit, `Q` is onto `Ω₁(P) = Z(P)`, and
as `|P ⧸ Z(P)| = |Z(P)|` it is a bijection.  An automorphism `φ` fixing `Z(P)` pointwise
satisfies `(φ x)² = φ (x²) = x²`, i.e. `Q (φ x Z(P)) = Q (x Z(P))`, so `φ x ∈ x Z(P)`, and then
`φ² = 1` because every central element squares to `1`. -/
theorem orderOf_dvd_two_of_fixes_omega1 {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P)
    (hcard : Nat.card P = Nat.card ↥(Subgroup.center P) ^ 2)
    (hb : ∀ x : P, x ^ 2 ∈ Subgroup.center P)
    (hZ : Subgroup.center P = Work.Higman.omega1 P)
    (φ : MulAut P) (hφ : ∀ z : P, z ∈ Work.Higman.omega1 P → φ z = z) :
    orderOf φ ∣ 2 := by
  classical
  have hZ2 : ∀ z : P, z ∈ Subgroup.center P → z * z = 1 := by
    intro z hz
    have h1 : z ∈ Work.Higman.omega1 P := hZ ▸ hz
    have h2 : z ^ 2 = 1 := h.mem_omega1.mp h1
    rwa [pow_two] at h2
  have hsqO : ∀ x : P, x ^ 2 ∈ Work.Higman.omega1 P := fun x => hZ ▸ hb x
  -- ## the squaring map `Q` on the quotient by the centre
  have hwd : ∀ a b : P, (QuotientGroup.leftRel (Subgroup.center P)) a b →
      (⟨a ^ 2, hb a⟩ : ↥(Subgroup.center P)) = ⟨b ^ 2, hb b⟩ := by
    intro a b hab
    obtain ⟨z, hz, rfl⟩ : ∃ z ∈ Subgroup.center P, b = a * z :=
      ⟨a⁻¹ * b, QuotientGroup.leftRel_apply.mp hab, by group⟩
    apply Subtype.ext
    show a ^ 2 = (a * z) ^ 2
    have hza : z * a = a * z := (Subgroup.mem_center_iff.mp hz a).symm
    have hc : Commute a z := hza.symm
    have h1 : (a * z) ^ 2 = a ^ 2 := by
      rw [hc.mul_pow 2, show z ^ 2 = 1 by rw [pow_two]; exact hZ2 z hz, mul_one]
    exact h1.symm
  let Q : P ⧸ Subgroup.center P → ↥(Subgroup.center P) :=
    fun q => Quotient.liftOn q (fun x : P => (⟨x ^ 2, hb x⟩ : ↥(Subgroup.center P))) hwd
  have Q_mk : ∀ x : P, Q (QuotientGroup.mk x) = (⟨x ^ 2, hb x⟩ : ↥(Subgroup.center P)) :=
    fun x => Quotient.liftOn_mk (s := QuotientGroup.leftRel (Subgroup.center P))
      (fun x : P => (⟨x ^ 2, hb x⟩ : ↥(Subgroup.center P))) hwd x
  -- ## every element of `Ω₁(P)` is a square
  have hsurj_sq : ∀ z : P, z ∈ Work.Higman.omega1 P → ∃ x : P, x ^ 2 = z := by
    intro z hz
    rcases eq_or_ne z 1 with rfl | hz1
    · exact ⟨1, by simp⟩
    · have hz2 : orderOf z = 2 := by
        have hd : orderOf z ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (h.mem_omega1.mp hz)
        rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
        · exact absurd (orderOf_eq_one_iff.mp h1) hz1
        · exact h2
      have hxZ : ∃ x : P, x ∉ Subgroup.center P := by
        by_contra hc
        push_neg at hc
        obtain ⟨a, b, hab⟩ := h.noncomm
        exact hab ((Subgroup.mem_center_iff.mp (hc a) b).symm)
      obtain ⟨x, hxZ⟩ := hxZ
      have hx2O : x ^ 2 ∈ Work.Higman.omega1 P := hsqO x
      have hx2ne : x ^ 2 ≠ 1 := fun hcon => hxZ (hZ ▸ h.mem_omega1.mpr hcon)
      have hord : orderOf (x ^ 2) = 2 := by
        have hd : orderOf (x ^ 2) ∣ 2 :=
          orderOf_dvd_iff_pow_eq_one.mpr (h.mem_omega1.mp hx2O)
        rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
        · exact absurd (orderOf_eq_one_iff.mp h1) hx2ne
        · exact h2
      obtain ⟨k, hk⟩ := h.trans (x ^ 2) z hord hz2
      refine ⟨(h.xi ^ k) x, ?_⟩
      show ((h.xi ^ k) x) ^ 2 = z
      rw [← map_pow]
      exact hk
  have Q_surj : Function.Surjective Q := by
    intro y
    obtain ⟨x, hx⟩ := hsurj_sq y.1 (hZ ▸ y.2)
    exact ⟨QuotientGroup.mk x, by rw [Q_mk x]; exact Subtype.ext hx⟩
  -- ## cardinalities: `|P ⧸ Z(P)| = |Z(P)|`
  have hcard' : Nat.card (P ⧸ Subgroup.center P) = Nat.card ↥(Subgroup.center P) := by
    have h1 : Nat.card P = Nat.card (P ⧸ Subgroup.center P) * Nat.card ↥(Subgroup.center P) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup _
    have h2 : Nat.card ↥(Subgroup.center P) * Nat.card ↥(Subgroup.center P) =
        Nat.card (P ⧸ Subgroup.center P) * Nat.card ↥(Subgroup.center P) := by
      rw [← h1, hcard, pow_two]
    exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos h2).symm
  have Q_inj : Function.Injective Q := by
    haveI : Fintype (P ⧸ Subgroup.center P) := Fintype.ofFinite _
    haveI : Fintype ↥(Subgroup.center P) := Fintype.ofFinite _
    exact ((Fintype.bijective_iff_surjective_and_card Q).mpr
      ⟨Q_surj, by rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]; exact hcard'⟩).1
  -- ## an automorphism fixing `Z(P)` pointwise induces the identity on the quotient
  have key : ∀ x : P, (QuotientGroup.mk (φ x) : P ⧸ Subgroup.center P) = QuotientGroup.mk x := by
    intro x
    apply Q_inj
    rw [Q_mk (φ x), Q_mk x]
    apply Subtype.ext
    show (φ x) ^ 2 = x ^ 2
    have h1 : φ (x ^ 2) = x ^ 2 := hφ (x ^ 2) (hsqO x)
    have h2 : φ (x ^ 2) = (φ x) ^ 2 := map_pow φ x 2
    rw [← h2, h1]
  have hfin : ∀ x : P, x⁻¹ * φ x ∈ Subgroup.center P := by
    intro x
    exact (QuotientGroup.eq (s := Subgroup.center P) (a := x) (b := φ x)).mp (key x).symm
  -- ## hence `φ ^ 2 = 1`
  have hsq_eq : φ ^ 2 = 1 := by
    rw [pow_two]
    ext x
    obtain ⟨z, hz, hzx⟩ : ∃ z ∈ Subgroup.center P, φ x = x * z :=
      ⟨x⁻¹ * φ x, hfin x, by group⟩
    calc φ (φ x) = φ (x * z) := by rw [hzx]
      _ = φ x * φ z := map_mul φ x z
      _ = x * z * z := by rw [hzx, hφ z (hZ ▸ hz)]
      _ = x * (z * z) := by group
      _ = x := by rw [hZ2 z hz, mul_one]
  exact orderOf_dvd_iff_pow_eq_one.mpr hsq_eq

/-- **The regularity input, `q ^ 2` case.**  If `|P| = |Z(P)| ^ 2`, every square of `P` is
central and `Z(P) = Ω₁(P)`, then `P` carries an automorphism of order `|Invol P|` permuting the
involutions transitively.

Let `g = ξ`, `m = orderOf g`, `n = |Invol P|`.  The stabiliser of an involution `u` under `⟨g⟩`
consists of elements fixing `Ω₁(P)` pointwise (they commute with `g`, and `⟨g⟩` is transitive on
the involutions), so by `orderOf_dvd_two_of_fixes_omega1` it has order dividing `2`; hence the
stabiliser of `u` in `⟨g ^ (m / n)⟩` (a group of order `n`, which is odd) is trivial, `g ^
(m / n)` has order `n`, and it is transitive. -/
theorem exists_xi_order_ncard_of_q2 {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P)
    (hcard : Nat.card P = Nat.card ↥(Subgroup.center P) ^ 2)
    (hb : ∀ x : P, x ^ 2 ∈ Subgroup.center P)
    (hZ : Subgroup.center P = Work.Higman.omega1 P) :
    ∃ ξ : MulAut P, orderOf ξ = (Work.Higman.Invol P).ncard ∧
      ∀ x y : P, orderOf x = 2 → orderOf y = 2 → ∃ k : ℕ, (ξ ^ k) x = y := by
  classical
  set n : ℕ := (Work.Higman.Invol P).ncard with hn
  set g : MulAut P := h.xi with hg
  set m : ℕ := orderOf g with hm
  have hdiv : n ∣ m := by
    rw [hn, hm, hg]
    exact Work.Higman.invol_ncard_dvd_orderOf_xi h
  set s : ℕ := m / n with hs
  have hns : n * s = m := Nat.mul_div_cancel' hdiv
  have hnpos : 0 < n := by
    obtain ⟨a, c, ha2, hc2, hac⟩ := h.manyInvol
    have hsub : ({a, c} : Set P) ⊆ Work.Higman.Invol P := by
      intro w hw
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · exact mem_Invol.mpr ha2
      · exact mem_Invol.mpr hc2
    have hcard2 : ({a, c} : Set P).ncard = 2 := by
      rw [Set.ncard_insert_of_notMem (by simpa using hac) (Set.toFinite _),
        Set.ncard_singleton]
    calc 0 < 2 := by norm_num
      _ = ({a, c} : Set P).ncard := hcard2.symm
      _ ≤ n := by rw [hn]; exact Set.ncard_le_ncard hsub (Set.toFinite _)
  have hspos : 0 < s := by
    rw [hs, Nat.div_pos_iff]
    exact ⟨hnpos, Nat.le_of_dvd (by rw [hm]; exact orderOf_pos_iff.mpr (isOfFinOrder_of_finite g)) hdiv⟩
  -- `n` is odd
  have hnodd : Odd n := by
    obtain ⟨d, hd⟩ := h.exists_card_omega1_eq_two_pow
    have h1 : n + 1 = 2 ^ d := by rw [hn, ← h.card_omega1, hd]
    have hd2 : 2 ≤ d := by
      by_contra hcon
      push_neg at hcon
      have h4 : Nat.card (Work.Higman.omega1 P) < 4 := by
        interval_cases d <;> norm_num [hd]
      exact absurd h.omega1_card_ge_four (by omega)
    have heven : Even (2 ^ d) := ⟨2 ^ (d - 1), by
      rw [← two_mul, ← pow_succ']
      congr 1
      omega⟩
    have h3 : Odd (2 ^ d - 1) := Nat.Even.sub_odd Nat.one_le_two_pow heven odd_one
    rwa [← h1, Nat.add_sub_cancel] at h3
  have hξord : orderOf (g ^ s) = n := by
    have hsdvd : s ∣ m := ⟨n, by rw [← hns, mul_comm]⟩
    rw [orderOf_pow, ← hm, Nat.gcd_eq_right hsdvd, ← hns]
    exact Nat.mul_div_cancel n hspos
  obtain ⟨u, -, hu2, -⟩ := h.manyInvol
  -- any element of `⟨g ^ s⟩` fixing an involution is trivial
  have key : ∀ w : P, orderOf w = 2 → ∀ ψ : MulAut P,
      ψ ∈ Subgroup.zpowers (g ^ s) → ψ w = w → ψ = 1 := by
    intro w hw ψ hψ hfix
    have hψK : ψ ∈ Subgroup.zpowers g :=
      Subgroup.zpowers_le.mpr
        (Subgroup.pow_mem (Subgroup.zpowers g) (Subgroup.mem_zpowers g) s) hψ
    have hfixall : ∀ y : P, y ∈ Work.Higman.omega1 P → ψ y = y :=
      q2_fixes_omega1_of_mem_zpowers_fixes_invol h hw hψK hfix
    have h1 : orderOf ψ ∣ 2 := orderOf_dvd_two_of_fixes_omega1 h hcard hb hZ ψ hfixall
    have h2 : orderOf ψ ∣ n := by
      rw [← hξord]
      exact orderOf_dvd_of_mem_zpowers hψ
    have h3 : orderOf ψ ∣ Nat.gcd 2 n := Nat.dvd_gcd h1 h2
    have h4 : Nat.gcd 2 n = 1 := (Nat.coprime_two_left.mpr hnodd).gcd_eq_one
    rw [h4] at h3
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  refine ⟨g ^ s, hξord, ?_⟩
  intro x y hx hy
  have hstabbot : ∀ z : P, orderOf z = 2 →
      MulAction.stabilizer (Subgroup.zpowers (g ^ s)) z = ⊥ := by
    intro z hz
    rw [Subgroup.eq_bot_iff_forall]
    intro ψ hψ
    rw [MulAction.mem_stabilizer_iff] at hψ
    exact Subtype.ext (key z hz ψ.1 ψ.2 hψ)
  have hxorbit : (MulAction.orbit (Subgroup.zpowers (g ^ s)) x : Set P)
      = Work.Higman.Invol P := by
    refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
    · intro w hw
      rw [MulAction.mem_orbit_iff] at hw
      obtain ⟨ψ, hψw⟩ := hw
      rw [mem_Invol, ← hψw]
      rw [show ψ • x = (ψ : MulAut P) x from rfl, MulEquiv.orderOf_eq, hx]
    · have hcard2 : (MulAction.orbit (Subgroup.zpowers (g ^ s)) x).ncard = n := by
        rw [← Nat.card_coe_set_eq]
        have hos := Nat.card_congr
          (MulAction.orbitProdStabilizerEquivGroup (Subgroup.zpowers (g ^ s)) x)
        rw [Nat.card_prod, Nat.card_zpowers, hξord] at hos
        rw [hstabbot x hx, Subgroup.card_bot, mul_one] at hos
        exact hos
      rw [hcard2, hn]
  have hy' : y ∈ MulAction.orbit (Subgroup.zpowers (g ^ s)) x := by
    rw [hxorbit]
    exact mem_Invol.mpr hy
  rw [MulAction.mem_orbit_iff] at hy'
  obtain ⟨ψ, hψ⟩ := hy'
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (g ^ s) ^ k = ψ.1 := by
    have hfin := isOfFinOrder_of_finite (g ^ s)
    have h2 := (IsOfFinOrder.mem_zpowers_iff_mem_range_orderOf hfin).mp ψ.2
    rcases Finset.mem_image.mp h2 with ⟨k, -, hk⟩
    exact ⟨k, hk⟩
  exact ⟨k, by rw [hk]; exact hψ⟩

/-- **Higman (1963), Theorem 1, type `A`** (Lemma 11 of the paper): a Suzuki 2-group whose
order equals `q ^ 2` (`q = |Z(P)|`) is `A(n,θ)`. -/
theorem type_A_classification {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P)
    (hcard : Nat.card P = Nat.card ↥(Subgroup.center P) ^ 2) :
    ∃ (n : ℕ) (e : P ≃ GaloisField 2 n × GaloisField 2 n)
      (θ : GaloisField 2 n ≃+* GaloisField 2 n),
      Nat.card ↥(Subgroup.center P) = 2 ^ n ∧ θ ≠ RingEquiv.refl _ ∧ Odd (orderOf θ) ∧
      ∀ x y : P, e (x * y) =
        ((e x).1 + (e y).1, (e x).2 + (e y).2 + (e x).1 * θ (e y).1) := by
  have hb : ∀ x : P, x ^ 2 ∈ Subgroup.center P :=
    Work.Higman.sq_mem_center_wired h hcard
  have hZ : Subgroup.center P = Work.Higman.omega1 P :=
    Work.Higman.center_eq_omega1_of_sq_mem_center h hcard hb
  obtain ⟨ξ, hξ1, hξ2⟩ := exists_xi_order_ncard_of_q2 h hcard hb hZ
  have hreg : ∃ ξ : MulAut P, orderOf ξ = (Invol P).ncard ∧
      ∀ x y : P, orderOf x = 2 → orderOf y = 2 → ∃ k : ℕ, (ξ ^ k) x = y := ⟨ξ, hξ1, hξ2⟩
  obtain ⟨n, θ, Φ, Ψ, hn, hθ, hodd, hΦ, hΨ, hsq⟩ :=
    q2_squaring_coordinates h hcard hb hZ hreg
  have hexp : ∀ z ∈ Subgroup.center P, z ^ 2 = 1 := by
    intro z hz
    rw [hZ] at hz
    exact h.mem_omega1.mp hz
  obtain ⟨e, he⟩ := type_A_assembly hb hexp Φ hΦ Ψ hΨ hsq
  exact ⟨n, e, θ, hn, hθ, hodd, he⟩

end Work.Higman
