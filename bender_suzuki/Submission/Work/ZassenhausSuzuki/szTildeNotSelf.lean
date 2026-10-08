import Mathlib
import Submission.Work.ZassenhausSuzuki.szTildeAux
import Submission.Work.ZassenhausSuzuki.frel_center_aux
import Submission.Work.RankOneUniqueness.f_unique
import Submission.Work.ZassenhausSuzuki.SzA.isSuzukiTwoGroup
import Submission.Work.ZassenhausSuzuki.QSZ_false_of_order_three_suz

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausSuzuki.szTildeNotSelf` — no central involution is fixed by `∼`

Route (Suzuki 1962 Thm. 1 / BG §5.13–5.14, reduced to the structure identity of
Peterfalvi II Ch. V §2):

* `hself` together with `tildeOf_eq` (`∼ x = h x⁻¹ · f x · h x`) gives `f c = h c · c · h c⁻¹`
  for every central involution `c`: **`f` maps the centre of `Q` into itself**.
* The structure-identity involution `s` (`FRel H t s ρ⁻¹`, `t s t = ρ t ρ⁻¹`) is a central
  involution, so `f s = ρ⁻¹` is central, i.e. `ρ` is central too — in the coordinates `e` both
  `s` and `ρ` are central involutions.
* Then `(s * t)² = ρ (s * t) ρ⁻¹` and `ρ² = 1`, so `(s * t)⁴ = s * t`, i.e. `(s * t)³ = 1`.
* But `(s * t)³ = 1` with `s ∈ Q` an involution and `Q` a Suzuki 2-group forces `Q` abelian
  (Suzuki 1962, Theorem 1, in the form `QSZ_false_of_order_three_suz`), contradicting
  `Q ≃* A(K,θ)` with `θ ≠ 1`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausSuzuki

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-- If `x` is an involution and `y * y = x * y * x`, then `y ^ 4 = y` (`y` has order dividing
`3` whenever `y ≠ 1`). -/
private theorem pow_four_of_conj {G : Type} [Group G] {x y : G} (hx : x * x = 1)
    (hy : y * y = x * y * x) : y ^ 4 = y := by
  have h : (y * y) * (y * y) = y := by
    have e1 : (x * y * x) * (x * y * x) = x * (y * y) * x := by
      have e1' : (x * y * x) * (x * y * x) = x * y * (x * x) * y * x := by group
      rw [e1', hx]
      group
    have e2 : x * (x * y * x) * x = y := by
      have e2' : x * (x * y * x) * x = (x * x) * y * (x * x) := by group
      rw [e2', hx]
      group
    calc (y * y) * (y * y) = (x * y * x) * (x * y * x) := by rw [hy]
      _ = x * (y * y) * x := e1
      _ = x * (x * y * x) * x := by rw [hy]
      _ = y := e2
  calc y ^ 4 = y ^ (2 + 2) := by norm_num
    _ = y ^ 2 * y ^ 2 := by rw [pow_add]
    _ = (y * y) * (y * y) := by rw [pow_two]
    _ = y := h

/-- **`A(K,θ)` is non-abelian for `θ ≠ 1`.**  Two elements `⟨1,0⟩`, `⟨a,0⟩` with `θ a ≠ a` do not
commute; transporting along `e` gives the non-abelianness of `Q`. -/
private theorem not_isAbelianSubgroup_of_mulEquiv {G : Type} [Group G] {Q : Subgroup G}
    {K : Type} [Field K] {θ : K ≃+* K}
    (hθ : θ ≠ 1) {e : Q ≃* SzA K θ} : ¬ IsAbelianSubgroup Q := by
  intro hab
  have hne : ∃ a : K, θ a ≠ a := by
    by_contra h
    exact hθ (RingEquiv.ext (fun a => by simpa using not_not.mp (not_exists.mp h a)))
  obtain ⟨a, ha⟩ := hne
  have ha0 : a ≠ 0 := fun h => ha (by rw [h, map_zero])
  have hkey : (⟨1, 0⟩ : SzA K θ) * ⟨a, 0⟩ ≠ ⟨a, 0⟩ * (⟨1, 0⟩ : SzA K θ) := by
    intro h
    apply ha
    have h' := congrArg SzA.b h
    simpa using h'
  have hQ : (e.symm (⟨1, 0⟩ : SzA K θ)) * (e.symm (⟨a, 0⟩ : SzA K θ))
      = (e.symm (⟨a, 0⟩ : SzA K θ)) * (e.symm (⟨1, 0⟩ : SzA K θ)) :=
    Subtype.ext (hab (e.symm (⟨1, 0⟩ : SzA K θ)) (e.symm (⟨1, 0⟩ : SzA K θ)).2
      (e.symm (⟨a, 0⟩ : SzA K θ)) (e.symm (⟨a, 0⟩ : SzA K θ)).2)
  have h' := congrArg e hQ
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h'
  exact hkey h'

/-- **BG 5.13/5.14, the "no special involution" step.**  If every central involution of `Q` is
fixed by the reflection `∼`, then the configuration `Q ≃* A(GF(2^m),θ)` (`θ ≠ 1`, `Odd (orderOf θ)`)
with the two-point stabiliser acting through the torus `Λ` is impossible. -/
theorem szTildeNotSelf {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    {m : ℕ} {θ : GaloisField 2 m ≃+* GaloisField 2 m} (hθ1 : θ ≠ 1) (hθodd : Odd (orderOf θ))
    {e : Q ≃* Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ}
    (htorus : ∀ d : G, d ∈ Submission.Blueprint.twoPoint H t →
      ∃ lam : (GaloisField 2 m)ˣ, ∀ x : Q,
        ∃ y : Q, (y : G) = d * (x : G) * d⁻¹ ∧
          e y = Work.ZassenhausSuzuki.SzA.hLam θ (lam : GaloisField 2 m) (e x))
    (hself : ∀ c : Q, (e c).a = 0 → e c ≠ 1 →
      Work.ZassenhausSuzuki.szTilde hsplit c = c) :
    False := by
  classical
  obtain ⟨hsQ, hs2, hρQ, hstruct⟩ := structPair_spec hsplit
  -- ## `t` is an involution
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [hsplit.invol] at h
    simpa [pow_two] using h
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  -- ## the structure involution `s` and the structure element `ρ`, as elements of `Q`
  set sQ : Q := ⟨(structPair hsplit).1, hsQ⟩ with hsQdef
  set rQ : Q := ⟨(structPair hsplit).2, hρQ⟩ with hrQdef
  have hs2' : orderOf (sQ : G) = 2 := by simpa [hsQdef] using hs2
  have hs2mul : (sQ : G) * (sQ : G) = 1 := by
    have h := pow_orderOf_eq_one (sQ : G)
    rw [hs2'] at h
    simpa [pow_two] using h
  have hs_ne1 : (sQ : G) ≠ 1 := by
    intro h
    have h1 : orderOf (sQ : G) = 1 := by rw [h, orderOf_one]
    rw [hs2'] at h1
    exact absurd h1 (by norm_num)
  have hsQne : sQ ≠ 1 := by
    intro h
    exact hs_ne1 (by simpa using congrArg (fun z : Q => (z : G)) h)
  have hseq : sQ * sQ = 1 := Subtype.ext (by simpa [Subgroup.coe_mul, Subgroup.coe_one] using hs2mul)
  -- ## `(e s).a = 0`
  have hsa : (e sQ).a = 0 := by
    refine a_eq_zero_of_sq_eq_one θ (e sQ) ?_
    rw [← map_mul, hseq, map_one]
  have hes1 : e sQ ≠ 1 := by
    intro h
    exact hsQne (e.injective (by simpa using h))
  -- ## `hself` at `s`, via `tildeOf_eq`:  `f s = h s · s · h s⁻¹`
  have hself_s : szTilde hsplit sQ = sQ := hself sQ hsa hes1
  have htilde : ((szTilde hsplit sQ : Q) : G)
      = (hG (szCanon hsplit) sQ)⁻¹ * fG (szCanon hsplit) sQ * hG (szCanon hsplit) sQ := by
    rw [szTilde_eq_tildeOf]
    exact tildeOf_eq hsplit hzass h2 (szCanon hsplit) hs_ne1
  have hf_eq : fG (szCanon hsplit) sQ
      = hG (szCanon hsplit) sQ * (sQ : G) * (hG (szCanon hsplit) sQ)⁻¹ := by
    have h1 : (hG (szCanon hsplit) sQ)⁻¹ * fG (szCanon hsplit) sQ * hG (szCanon hsplit) sQ
        = (sQ : G) := by
      rw [← htilde, hself_s]
    calc fG (szCanon hsplit) sQ
        = hG (szCanon hsplit) sQ
            * ((hG (szCanon hsplit) sQ)⁻¹ * fG (szCanon hsplit) sQ * hG (szCanon hsplit) sQ)
            * (hG (szCanon hsplit) sQ)⁻¹ := by group
      _ = hG (szCanon hsplit) sQ * (sQ : G) * (hG (szCanon hsplit) sQ)⁻¹ := by rw [h1]
  -- ## `htorus` at `d = h s`:  the conjugate of `s` has zero first coordinate
  obtain ⟨lam, hlam⟩ := htorus ((szCanon hsplit).h sQ : G) ((szCanon hsplit).h sQ).2
  obtain ⟨y, hy, hye⟩ := hlam sQ
  have hya : (e y).a = 0 := by
    rw [hye, SzA.hLam_a, hsa, mul_zero]
  have hyf : (y : G) = fG (szCanon hsplit) sQ := by rw [hy, hf_eq]
  have hyeq : y = (szCanon hsplit).f sQ := Subtype.ext hyf
  have hfa : (e ((szCanon hsplit).f sQ)).a = 0 := by rw [← hyeq]; exact hya
  -- ## uniqueness of the `f`-relation:  `f s = ρ⁻¹`
  have hfs_eq : ((szCanon hsplit).f sQ) = rQ⁻¹ := by
    apply Subtype.ext
    refine Work.RankOneUniqueness.f_unique hsplit (x := (sQ : G))
      ((szCanon hsplit).f sQ).2 (Q.inv_mem hρQ) ?_ ?_
    · refine ⟨((szCanon hsplit).g sQ : G) * ((szCanon hsplit).h sQ : G), ?_, ?_⟩
      · exact H.mul_mem (hsplit.le ((szCanon hsplit).g sQ).2)
          (Subgroup.mem_inf.mp ((szCanon hsplit).h sQ).2).1
      · exact (szCanon hsplit).spec sQ hs_ne1
    · refine ⟨(structPair hsplit).2, hsplit.le hρQ, ?_⟩
      have h' := hstruct
      rw [hti] at h'
      simpa [hrQdef, Subgroup.coe_inv] using h'
  -- ## `ρ` has zero first coordinate, so `ρ² = 1`
  have hrQa : (e rQ).a = 0 := by
    have h : (e (rQ⁻¹)).a = 0 := by rw [← hfs_eq]; exact hfa
    rw [map_inv, SzA.inv_a] at h
    exact neg_eq_zero.mp h
  have hrQ2 : rQ * rQ = 1 := by
    apply e.injective
    rw [map_mul, map_one, SzA.sq_eq, hrQa]
    ext <;> simp
  have hrG2 : (rQ : G) * (rQ : G) = 1 := by
    have := congrArg (fun z : Q => (z : G)) hrQ2
    simpa [Subgroup.coe_mul, Subgroup.coe_one] using this
  have hrinv : (rQ : G)⁻¹ = (rQ : G) := inv_eq_of_mul_eq_one_right hrG2
  -- ## `s` and `ρ` commute (both are central: both have zero first coordinate)
  have hcomm : (sQ : G) * (rQ : G) = (rQ : G) * (sQ : G) := by
    have hQ : sQ * rQ = rQ * sQ := by
      apply e.injective
      rw [map_mul, map_mul]
      exact ((Subgroup.mem_center_iff.mp
        ((SzA.mem_center_iff θ hθ1 (e sQ)).mpr hsa)) (e rQ)).symm
    simpa [Subgroup.coe_mul] using congrArg (fun z : Q => (z : G)) hQ
  -- ## `t s t = ρ t ρ`
  have hstruct2 : t * (sQ : G) * t = (rQ : G) * t * (rQ : G) := by
    have h1 : t * (sQ : G) * t = (rQ : G) * t * (rQ : G)⁻¹ := by
      have h' := hstruct
      rw [hti] at h'
      simpa [hsQdef, hrQdef, Subgroup.coe_inv] using h'
    rwa [hrinv] at h1
  -- ## `w = s t` satisfies `w² = ρ w ρ⁻¹`, hence `w⁴ = w` and `w³ = 1`
  set w : G := (sQ : G) * t with hwdef
  have hw2 : w * w = (rQ : G) * w * (rQ : G) := by
    have h1 : w * w = ((sQ : G) * (rQ : G)) * t * (rQ : G) := by
      calc w * w = (sQ : G) * (t * (sQ : G) * t) := by rw [hwdef]; group
        _ = (sQ : G) * ((rQ : G) * t * (rQ : G)) := by rw [hstruct2]
        _ = ((sQ : G) * (rQ : G)) * t * (rQ : G) := by group
    rw [h1, hcomm, hwdef]
    group
  have hw4 : w ^ 4 = w := pow_four_of_conj hrG2 hw2
  have hw3 : w ^ 3 = 1 := by
    have h : w ^ 3 * w = w := by rw [← pow_succ]; exact hw4
    have h' := congrArg (fun z : G => z * w⁻¹) h
    simpa [mul_assoc] using h'
  have hwne : w ≠ 1 := by
    intro hw1
    have h2 : (sQ : G) * t = 1 := by rw [← hwdef]; exact hw1
    have h3 : (sQ : G) = t := by
      have h4 : (sQ : G) = t⁻¹ := by
        have := congrArg (fun z : G => z * t⁻¹) h2
        simpa [mul_assoc] using this
      rwa [hti] at h4
    exact hsplit.not_mem (by rw [← h3]; exact hsplit.le sQ.2)
  have hst_pow : ((sQ : G) * t) ^ 3 = 1 := by rw [← hwdef]; exact hw3
  -- ## the Suzuki 2-group input and Suzuki's Theorem 1
  have hfinQ : Finite ↥Q := Subtype.finite
  have hfinSzA : Finite (SzA (GaloisField 2 m) θ) := inferInstance
  have hSuz : IsSuzukiTwoGroup ↥Q :=
    isSuzukiTwoGroup_of_mulEquiv e (SzA.isSuzukiTwoGroup θ hθ1 hθodd)
  exact QSZ_false_of_order_three_suz H Q t hsplit hzass h2 hSuz sQ.2 hs2' hst_pow

end Work.ZassenhausSuzuki
