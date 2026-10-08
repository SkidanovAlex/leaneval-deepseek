import Mathlib
import Submission.Work.CharCore.Main
import Submission.Work.Induction.All
import Submission.Work.ZassenhausTwoGroup.Defs
import Submission.Work.ZassenhausTwoGroup.normalizer_twoPoint
import Submission.Work.ZassenhausTwoGroup.card_quotient_eq
import Submission.Work.ZassenhausTwoGroup.card_H_eq
import Submission.Work.ZassenhausTwoGroup.zetaStar_aux
import Submission.Work.ZassenhausTwoGroup.doubleCoset_cover
import Submission.Work.ZassenhausTwoGroup.conj_mem_H_of_mem_Q
import Submission.Work.ZassenhausTwoGroup.cfInner_indFun_twoClassFun_twoDoubleCoset
import Submission.Work.ZassenhausPSL2.Basic
import Submission.Work.ZassenhausPSL2.ZData.t_conj_eq_inv

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausTwoGroup.etaStar_data` (Feit 1960, §3, displays (18) and (19))

In the split rank-one Zassenhaus set-up `IsSplitRankOne H Q t` (so `H = Q ⋊ D` with
`D = twoPoint H t = H ∩ Hᵗ`, `Q ⊴ H`, `Q ∩ Qˣ = 1` for `x ∉ H`, and `H` transitive on
`Ω ∖ {∞}`, `Ω = G ⧸ H`) let `η ∈ Irr H` be a non-trivial irreducible character of `H` which
is trivial on `Q`.  Then `Ind_H^G η` is irreducible of degree `|Q| + 1`, takes the value `1`
on `Q ∖ 1`, and is orthogonal to `Ind_H^G η'` for every other such `η'` which is not the
complex conjugate of `η`.

The mathematical content is Mackey's formula in the two-double-coset situation
`G = H ⊔ H t H` (the rank-one Bruhat decomposition, here `doubleCoset_cover`):

`⟨Ind η, Ind η'⟩_G = ⟨η,η'⟩_H + |D|⁻¹ ∑_{d ∈ D} η d · conj (η' (t d t))`,

combined with `t d t = d⁻¹` for `d ∈ D` (`twoPoint_conj_t_eq_inv`, from the Zassenhaus
condition and Burnside's lemma) and the elementary computation of `∑_{d ∈ D} η d · η' d`
through the decomposition `x = d · q` of an element of `H`.

Everything is reduced to the following two facts about the linear characters
`φ, ψ : ↥H →* ℂˣ` affording `η, η'` (they are linear because `hηQ` applied at `x = 1` gives
`η 1 = 1`):

* the homomorphism `(φ * ψ) ∘ (D ↪ H)` is trivial if and only if `η'` is the complex
  conjugate of `η` (`eq_star_of_comp_dToH_eq_one`, `comp_dToH_eq_one_of_eq_star`), and
* `(φ * φ) ∘ (D ↪ H)` is non-trivial (`sq_comp_dToH_ne_one`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open Classical
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausTwoGroup

/-! ## Elementary auxiliary lemmas -/

/-- In a monoid, an element of odd power `1` whose square is `1` is `1`. -/
theorem eq_one_of_sq_eq_one_of_odd_pow_eq_one {M : Type*} [Monoid M] {u : M} (h2 : u ^ 2 = 1)
    {N : ℕ} (hN : Odd N) (hN1 : u ^ N = 1) : u = 1 := by
  obtain ⟨k, hk⟩ := hN
  rw [hk] at hN1
  have h : u ^ (2 * k + 1) = u := by
    rw [pow_succ, pow_mul, h2, one_pow, one_mul]
  rw [h] at hN1
  exact hN1

/-- **The sum of the values of a homomorphism into `ℂˣ` over a finite group.**  It is `|X|` for
the trivial homomorphism and `0` otherwise (orthogonality of linear characters; proved here by
the substitution `x ↦ y * x`). -/
theorem sum_coe_units_eq_ite {X : Type*} [Group X] [Fintype X] (ρ : X →* ℂˣ) :
    (∑ x : X, (ρ x : ℂ)) = if ρ = 1 then (Fintype.card X : ℂ) else 0 := by
  classical
  by_cases hρ : ρ = 1
  · rw [if_pos hρ, hρ]
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  · rw [if_neg hρ]
    obtain ⟨y, hy⟩ : ∃ y : X, ρ y ≠ 1 := by
      by_contra h
      push_neg at h
      exact hρ (MonoidHom.ext h)
    have hval : (ρ y : ℂ) ≠ 1 := fun h => hy (Units.val_eq_one.mp h)
    have h1 : (ρ y : ℂ) * (∑ x : X, (ρ x : ℂ)) = ∑ x : X, (ρ x : ℂ) := by
      rw [Finset.mul_sum]
      calc ∑ x : X, (ρ y : ℂ) * (ρ x : ℂ) = ∑ x : X, (ρ (y * x) : ℂ) := by
            exact Finset.sum_congr rfl (fun x _ => by rw [map_mul, Units.val_mul])
        _ = ∑ x : X, (ρ x : ℂ) :=
            Fintype.sum_bijective (fun x : X => y * x) (Group.mulLeft_bijective y)
              (fun x : X => (ρ (y * x) : ℂ)) (fun x : X => (ρ x : ℂ)) (fun _ => rfl)
    have h2 : ((ρ y : ℂ) - 1) * (∑ x : X, (ρ x : ℂ)) = 0 := by
      rw [sub_mul, one_mul, h1, sub_self]
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hval)

/-- The normalised version of `sum_coe_units_eq_ite`. -/
theorem inv_natCard_mul_sum_coe_eq_ite {X : Type*} [Group X] [Fintype X] (ρ : X →* ℂˣ) :
    (Nat.card X : ℂ)⁻¹ * (∑ x : X, (ρ x : ℂ)) = if ρ = 1 then 1 else 0 := by
  classical
  rw [sum_coe_units_eq_ite]
  by_cases h : ρ = 1
  · rw [if_pos h, if_pos h, ← Nat.card_eq_fintype_card]
    exact inv_mul_cancel₀ (by
      rw [Nat.cast_ne_zero]
      exact Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩)
  · rw [if_neg h, if_neg h, mul_zero]

/-- Membership in `Work.CharCore.Irr` does not depend on the chosen `Fintype` instance. -/
theorem mem_Irr_of_fintype_iff {T : Type*} [Group T] (i j : Fintype T) {χ : T → ℂ} :
    χ ∈ @Work.CharCore.Irr T _ i ↔ χ ∈ @Work.CharCore.Irr T _ j := by
  rw [@Work.CharCore.mem_Irr_iff_fdrep T _ i χ, @Work.CharCore.mem_Irr_iff_fdrep T _ j χ]

/-- `Work.CharCore.Irr` does not depend on the chosen `Fintype` instance. -/
theorem Irr_eq_of_fintype (T : Type*) [Group T] (i j : Fintype T) :
    (@Work.CharCore.Irr T _ i : Set (T → ℂ)) = (@Work.CharCore.Irr T _ j : Set (T → ℂ)) := by
  ext χ
  exact mem_Irr_of_fintype_iff i j

/-- `Work.CharCore.IsVChar` does not depend on the chosen `Fintype` instance. -/
theorem isVChar_of_fintype_congr {T : Type*} [Group T] {i j : Fintype T} {f : T → ℂ} :
    @Work.CharCore.IsVChar T _ i f ↔ @Work.CharCore.IsVChar T _ j f := by
  have hset : (@Work.CharCore.Irr T _ i : Set (T → ℂ))
      = (@Work.CharCore.Irr T _ j : Set (T → ℂ)) := Irr_eq_of_fintype T i j
  show f ∈ AddSubgroup.closure (@Work.CharCore.Irr T _ i : Set (T → ℂ)) ↔
    f ∈ AddSubgroup.closure (@Work.CharCore.Irr T _ j : Set (T → ℂ))
  rw [hset]

/-- `t` inverts the two-point stabiliser `D = H ∩ Hᵗ` in the split rank-one Zassenhaus
set-up.  (This is `Work.ZassenhausPSL2.ZData.t_conj_eq_inv` without its redundant hypotheses
`Q ≠ ⊥` and `IsPGroup 2 Q`.) -/
theorem twoPoint_conj_t_eq_inv {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t)
    (hz : Submission.Blueprint.IsZassenhaus H) :
    ∀ d : G, d ∈ Submission.Blueprint.twoPoint H t → t * d * t = d⁻¹ := by
  have hV : Submission.Blueprint.centD H t = ⊥ :=
    Work.ZassenhausPSL2.ZData.centD_eq_bot_aux H Q t h hz
  let φhom : ↥(Submission.Blueprint.twoPoint H t) →* ↥(Submission.Blueprint.twoPoint H t) :=
    { toFun := fun x => ⟨(MulAut.conj t) (x : G), by
        rw [MulAut.conj_apply, Work.ZassenhausPSL2.t_inv h]
        exact Work.ZassenhausPSL2.dStab_conj_mem h x.2⟩
      map_one' := by ext; simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        show (MulAut.conj t) (↑(x * y) : G) = (MulAut.conj t) ↑x * (MulAut.conj t) ↑y
        rw [Subgroup.coe_mul, map_mul] }
  have hcoe_apply : ∀ x : ↥(Submission.Blueprint.twoPoint H t),
      (φhom x : G) = t * (x : G) * t⁻¹ := by
    intro x
    show (MulAut.conj t) (x : G) = t * (x : G) * t⁻¹
    rw [MulAut.conj_apply]
  have hφ2 : ∀ x : ↥(Submission.Blueprint.twoPoint H t), φhom (φhom x) = x := by
    intro x
    apply Subtype.ext
    show (MulAut.conj t) ((MulAut.conj t) (x : G)) = (x : G)
    rw [MulAut.conj_apply, MulAut.conj_apply, Work.ZassenhausPSL2.t_inv h]
    exact Work.ZassenhausPSL2.t_conj_invol h (x : G)
  have hφfpf : ∀ x : ↥(Submission.Blueprint.twoPoint H t), φhom x = x → x = 1 := by
    intro x hx
    have h1 : t * (x : G) * t⁻¹ = (x : G) := by
      rw [← hcoe_apply x]
      exact congrArg Subtype.val hx
    rw [Work.ZassenhausPSL2.t_inv h] at h1
    have hcoe : (x : G) * t = t * (x : G) := by
      have h2' : t * (x : G) = (x : G) * t := by
        calc t * (x : G) = t * (x : G) * (t * t) := by
              rw [Work.ZassenhausPSL2.t_mul_t h, mul_one]
          _ = (t * (x : G) * t) * t := by group
          _ = (x : G) * t := by rw [h1]
      exact h2'.symm
    have hmem : (x : G) ∈ Submission.Blueprint.centD H t := by
      rw [Work.ThreePoints.mem_centD]
      exact ⟨(Subgroup.mem_inf.mp x.2).1, (Work.ThreePoints.mem_twoPoint.mp x.2).2, hcoe⟩
    have : (x : G) = 1 := Subgroup.mem_bot.mp (hV ▸ hmem)
    exact Subtype.ext this
  have key := Work.ZassenhausPSL2.ZData.eq_inv_of_fpf_order_two φhom hφ2 hφfpf
  intro d hd
  have hx := key ⟨d, hd⟩
  have h1 : (φhom ⟨d, hd⟩ : G) = (⟨d, hd⟩ : ↥(Submission.Blueprint.twoPoint H t))⁻¹ :=
    congrArg Subtype.val hx
  rw [hcoe_apply ⟨d, hd⟩, Subgroup.coe_inv, Work.ZassenhausPSL2.t_inv h] at h1
  exact h1

/-- The two-point stabiliser `D = H ∩ Hᵗ`, viewed inside `H`. -/
abbrev dToH {G : Type*} [Group G] {H : Subgroup G} {t : G} :
    ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom : Subgroup G) →* ↥H where
  toFun d := ⟨(d : G), (Subgroup.mem_inf.mp d.2).1⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Every element of `H = Q ⋊ D` is a product `d * q` with `d ∈ D = H ∩ Hᵗ` and `q ∈ Q`. -/
theorem dToH_mul_Q {G : Type} [Group G] [Fintype G] {H Q : Subgroup G} {t : G}
    (h : IsSplitRankOne H Q t) (x : ↥H) :
    ∃ (d : ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom : Subgroup G)) (q : ↥Q),
      x = dToH (H := H) (t := t) d * ⟨(q : G), h.le q.2⟩ := by
  obtain ⟨d, q, hdq⟩ := Work.ZassenhausPSL2.mem_eq_dStab_mul_Q h x
  refine ⟨⟨(d : G), ?_⟩, q, ?_⟩
  · simpa only [Submission.Blueprint.twoPoint, Submission.Blueprint.conj] using d.2
  · apply Subtype.ext
    rw [Subgroup.coe_mul]
    exact hdq.symm

/-- The value of the inclusion `↥(H ∩ Hᵗ) →* ↥H`. -/
theorem dToH_coe {G : Type*} [Group G] {H : Subgroup G} {t : G}
    (d : ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom : Subgroup G)) :
    (dToH (H := H) (t := t) d : ↥H) = ⟨(d : G), (Subgroup.mem_inf.mp d.2).1⟩ := rfl

/-- The Mackey term of the two-double-coset formula, computed with linear characters
`η = φ`, `η' = ψ` on `H`: the `D`-indexed sum is the sum of the values of
`(φ * ψ) ∘ (D ↪ H)`. -/
theorem sum_term_eq_sum_coe {G : Type} [Group G] [Fintype G] {H : Subgroup G} [Fintype ↥H]
    {t : G} [Fintype ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom : Subgroup G)]
    (ht : t * t = 1)
    (hinv : ∀ d : G, d ∈ (H ⊓ H.map (MulAut.conj t).toMonoidHom : Subgroup G) →
      t * d * t = d⁻¹)
    (hDmap : ∀ d : ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom : Subgroup G),
        (MulAut.conj t) (d : G) ∈ (H ⊓ H.map (MulAut.conj t).toMonoidHom : Subgroup G))
    {η η' : ↥H → ℂ} {φ ψ : ↥H →* ℂˣ}
    (hφ : ∀ x : ↥H, η x = (φ x : ℂ)) (hψ : ∀ x : ↥H, η' x = (ψ x : ℂ))
    (hη' : η' ∈ Work.CharCore.Irr ↥H) :
    (∑ d : ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom : Subgroup G),
        η ⟨(d : G), (Subgroup.mem_inf.mp d.2).1⟩ *
          star (η' ⟨(MulAut.conj t) (d : G), (Subgroup.mem_inf.mp (hDmap d)).1⟩))
      = ∑ d : ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom : Subgroup G),
          (((φ * ψ).comp (dToH (H := H) (t := t))) d : ℂ) := by
  classical
  refine Finset.sum_congr rfl (fun d _ => ?_)
  have h1 : η ⟨(d : G), (Subgroup.mem_inf.mp d.2).1⟩ = (φ (dToH (H := H) (t := t) d) : ℂ) := by
    rw [dToH_coe]
    exact hφ ⟨(d : G), (Subgroup.mem_inf.mp d.2).1⟩
  have h2 : star (η' ⟨(MulAut.conj t) (d : G), (Subgroup.mem_inf.mp (hDmap d)).1⟩)
      = (ψ (dToH (H := H) (t := t) d) : ℂ) := by
    rw [← starRingEnd_apply,
      Work.CharCore.star_Irr η' hη'
        ⟨(MulAut.conj t) (d : G), (Subgroup.mem_inf.mp (hDmap d)).1⟩,
      hψ]
    refine congrArg (fun u : ↥H => (ψ u : ℂ)) ?_
    rw [dToH_coe]
    apply Subtype.ext
    simp only [Subgroup.coe_inv]
    rw [MulAut.conj_apply, show t⁻¹ = t from inv_eq_of_mul_eq_one_right ht,
      hinv (d : G) d.2, inv_inv]
  rw [h1, h2, MonoidHom.comp_apply, MonoidHom.mul_apply, Units.val_mul]

/-- **The homomorphism `(φ * φ) ∘ (D ↪ H)` is non-trivial.**  Otherwise `φ` would be trivial
on all of `H = Q ⋊ D`, contradicting `η ≠ 1`. -/
theorem sq_comp_dToH_ne_one {G : Type} [Group G] [Fintype G] {H Q : Subgroup G} [Fintype ↥H]
    {t : G} [Fintype ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom : Subgroup G)]
    (h : IsSplitRankOne H Q t)
    (hKodd : Odd (Nat.card ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom : Subgroup G)))
    {η : ↥H → ℂ} (hηQ : ∀ x : ↥H, (x : G) ∈ Q → η x = 1)
    (hη1 : η ≠ (fun _ : ↥H => (1 : ℂ))) {φ : ↥H →* ℂˣ}
    (hφ : ∀ x : ↥H, η x = (φ x : ℂ)) :
    (φ * φ).comp (dToH (H := H) (t := t)) ≠ 1 := by
  classical
  intro hcon
  have hφK : ∀ d : ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom : Subgroup G),
      φ (dToH (H := H) (t := t) d) = 1 := by
    intro d
    have hsq : (φ (dToH (H := H) (t := t) d)) ^ 2 = 1 := by
      have h1 : (((φ * φ).comp (dToH (H := H) (t := t))) d) = 1 := by rw [hcon]; rfl
      rw [MonoidHom.comp_apply, MonoidHom.mul_apply] at h1
      rw [pow_two]
      exact h1
    have hpow : (φ (dToH (H := H) (t := t) d)) ^
        (Nat.card ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom : Subgroup G)) = 1 := by
      have hd : d ^ (Nat.card ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom : Subgroup G)) = 1 := by
        rw [Nat.card_eq_fintype_card]
        exact pow_card_eq_one
      have h2 : (dToH (H := H) (t := t) d) ^
          (Nat.card ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom : Subgroup G)) = 1 := by
        rw [← map_pow, hd, map_one]
      have h3 := congrArg φ h2
      rwa [map_pow, map_one] at h3
    exact eq_one_of_sq_eq_one_of_odd_pow_eq_one hsq hKodd hpow
  have hφH : ∀ x : ↥H, φ x = 1 := by
    intro x
    obtain ⟨d, q, hx⟩ := dToH_mul_Q h x
    rw [hx, map_mul, hφK d]
    have hq : φ (⟨(q : G), h.le q.2⟩ : ↥H) = 1 := by
      refine Units.val_eq_one.mp ?_
      rw [← hφ (⟨(q : G), h.le q.2⟩ : ↥H)]
      exact hηQ _ q.2
    rw [hq, mul_one]
  refine hη1 (funext fun x => ?_)
  rw [hφ x, hφH x]
  simp

/-- If `η'` is the complex conjugate of `η`, then `(φ * ψ) ∘ (D ↪ H)` is trivial. -/
theorem comp_dToH_eq_one_of_eq_star {G : Type} [Group G] [Fintype G] {H : Subgroup G}
    [Fintype ↥H] {t : G} {η η' : ↥H → ℂ}
    (hη : η ∈ Work.CharCore.Irr ↥H) {φ ψ : ↥H →* ℂˣ}
    (hφ : ∀ x : ↥H, η x = (φ x : ℂ)) (hψ : ∀ x : ↥H, η' x = (ψ x : ℂ))
    (hconj : η' = (fun x : ↥H => star (η x))) :
    (φ * ψ).comp (dToH (H := H) (t := t)) = 1 := by
  classical
  refine MonoidHom.ext (fun d => ?_)
  have hd : ψ (dToH (H := H) (t := t) d) = (φ (dToH (H := H) (t := t) d))⁻¹ := by
    apply Units.ext
    have h1 : (ψ (dToH (H := H) (t := t) d) : ℂ)
        = star (η (dToH (H := H) (t := t) d)) := by
      rw [← hψ (dToH (H := H) (t := t) d), hconj]
    rw [← starRingEnd_apply, Work.CharCore.star_Irr η hη (dToH (H := H) (t := t) d),
      hφ ((dToH (H := H) (t := t) d)⁻¹), map_inv] at h1
    exact h1
  rw [MonoidHom.comp_apply, MonoidHom.mul_apply, hd]
  exact mul_inv_cancel _

/-- If `(φ * ψ) ∘ (D ↪ H)` is trivial then `η'` is the complex conjugate of `η`: both sides
are computed on a decomposition `x = d * q`. -/
theorem eq_star_of_comp_dToH_eq_one {G : Type} [Group G] [Fintype G] {H Q : Subgroup G}
    [Fintype ↥H] {t : G} (h : IsSplitRankOne H Q t) {η η' : ↥H → ℂ}
    (hη : η ∈ Work.CharCore.Irr ↥H)
    (hηQ : ∀ x : ↥H, (x : G) ∈ Q → η x = 1)
    (hη'Q : ∀ x : ↥H, (x : G) ∈ Q → η' x = 1) {φ ψ : ↥H →* ℂˣ}
    (hφ : ∀ x : ↥H, η x = (φ x : ℂ)) (hψ : ∀ x : ↥H, η' x = (ψ x : ℂ))
    (hcon : (φ * ψ).comp (dToH (H := H) (t := t)) = 1) :
    η' = (fun x : ↥H => star (η x)) := by
  classical
  have hmulη : ∀ x y : ↥H, η (x * y) = η x * η y := by
    intro x y
    rw [hφ (x * y), map_mul, Units.val_mul, ← hφ x, ← hφ y]
  have hmulψ : ∀ x y : ↥H, η' (x * y) = η' x * η' y := by
    intro x y
    rw [hψ (x * y), map_mul, Units.val_mul, ← hψ x, ← hψ y]
  funext x
  obtain ⟨d, q, hx⟩ := dToH_mul_Q h x
  have hd : φ (dToH (H := H) (t := t) d) * ψ (dToH (H := H) (t := t) d) = 1 := by
    have h1 : (((φ * ψ).comp (dToH (H := H) (t := t))) d) = 1 := by rw [hcon]; rfl
    rwa [MonoidHom.comp_apply, MonoidHom.mul_apply] at h1
  have hψd : ψ (dToH (H := H) (t := t) d) = (φ (dToH (H := H) (t := t) d))⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, mul_comm]
    exact hd
  have hq' : η' ⟨(q : G), h.le q.2⟩ = 1 := hη'Q _ q.2
  have hηq : η ⟨(q : G), h.le q.2⟩ = 1 := hηQ _ q.2
  have hL : η' (dToH (H := H) (t := t) d * ⟨(q : G), h.le q.2⟩)
      = ((φ (dToH (H := H) (t := t) d))⁻¹ : ℂ) := by
    rw [hmulψ, hq', mul_one, hψ (dToH (H := H) (t := t) d), hψd]
    simp only [Units.val_inv_eq_inv_val]
  have hR : star (η (dToH (H := H) (t := t) d * ⟨(q : G), h.le q.2⟩))
      = ((φ (dToH (H := H) (t := t) d))⁻¹ : ℂ) := by
    rw [hmulη, hηq, mul_one, ← starRingEnd_apply,
      Work.CharCore.star_Irr η hη (dToH (H := H) (t := t) d),
      hφ ((dToH (H := H) (t := t) d)⁻¹), map_inv]
    simp only [Units.val_inv_eq_inv_val]
  rw [hx, hL, hR]

/-- **Feit (18), the values.**  For `y ∈ Q ∖ 1` the induced function `Ind_H^G η` takes the
value `1`: the conjugates of `y` lying in `H` are exactly the `H`-conjugates. -/
theorem indFun_apply_mem_Q {G : Type} [Group G] [Fintype G] {H Q : Subgroup G} [Fintype ↥H]
    {t : G} (h : IsSplitRankOne H Q t) {η : ↥H → ℂ} (hη : η ∈ Work.CharCore.Irr ↥H)
    (hηQ : ∀ x : ↥H, (x : G) ∈ Q → η x = 1) (y : ↥Q) (hy1 : (y : G) ≠ 1) :
    Work.Induction.indFun H η (y : G) = 1 := by
  classical
  have hcl : Work.CharCore.IsClassFun η := Work.CharCore.isClassFun_of_mem_Irr hη
  have hcond : ∀ x : G, (x * (y : G) * x⁻¹ ∈ H) ↔ x ∈ H := fun x =>
    ⟨fun hx => conj_mem_H_of_mem_Q h y.2 hy1 x hx,
     fun hx => H.mul_mem (H.mul_mem hx (h.le y.2)) (H.inv_mem hx)⟩
  have hstep : ∀ x : G, (if hx : x * (y : G) * x⁻¹ ∈ H then η ⟨x * (y : G) * x⁻¹, hx⟩ else 0)
      = if x ∈ H then η ⟨(y : G), h.le y.2⟩ else 0 := by
    intro x
    by_cases hxH : x ∈ H
    · rw [dif_pos ((hcond x).mpr hxH), if_pos hxH]
      have he : (⟨x * (y : G) * x⁻¹, (hcond x).mpr hxH⟩ : ↥H)
          = (⟨x, hxH⟩ : ↥H) * ⟨(y : G), h.le y.2⟩ * (⟨x, hxH⟩ : ↥H)⁻¹ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]
      rw [he, hcl ⟨(y : G), h.le y.2⟩ (⟨x, hxH⟩ : ↥H)]
    · rw [dif_neg (fun hc => hxH ((hcond x).mp hc)), if_neg hxH]
  rw [Work.Induction.indFun_apply_def]
  have hsum : (∑ x : G, (if hx : x * (y : G) * x⁻¹ ∈ H then η ⟨x * (y : G) * x⁻¹, hx⟩ else 0))
      = (Nat.card ↥H : ℂ) * η ⟨(y : G), h.le y.2⟩ := by
    rw [Finset.sum_congr rfl (fun x _ => hstep x)]
    have h1 : (∑ x : G, (if x ∈ H then η ⟨(y : G), h.le y.2⟩ else 0))
        = ∑ x : ↥H, η ⟨(y : G), h.le y.2⟩ := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype (Finset.univ.filter (fun x : G => x ∈ H)) (fun x => by simp)
        (fun _ => η ⟨(y : G), h.le y.2⟩)
    rw [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
  rw [hsum, ← mul_assoc]
  have hne : (Nat.card ↥H : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  rw [inv_mul_cancel₀ hne, one_mul]
  exact hηQ _ y.2

/-- **The degree.**  `(Ind_H^G η) 1 = |Ω| · η 1 = |Q| + 1` because `Ω = G ⧸ H` has `|Q| + 1`
elements and `η 1 = 1`. -/
theorem indFun_apply_one_eq {G : Type} [Group G] [Fintype G] {H Q : Subgroup G} [Fintype ↥H]
    {t : G} (h : IsSplitRankOne H Q t) {η : ↥H → ℂ}
    (hηQ : ∀ x : ↥H, (x : G) ∈ Q → η x = 1) :
    (Work.Induction.indFun H η) 1 = (Nat.card Q : ℂ) + 1 := by
  rw [Work.Induction.indFun_apply_one]
  have h1 : η 1 = 1 := hηQ 1 (by simp)
  rw [h1, mul_one, Subgroup.index_eq_card, card_quotient_eq h, Nat.cast_add, Nat.cast_one]

/-! ## The main statement -/

theorem etaStar_data {G : Type} [Group G] [Fintype G] {H Q : Subgroup G} [Fintype ↥H] {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hz : Submission.Blueprint.IsZassenhaus H)
    (hQ : Q ≠ ⊥) {η : ↥H → ℂ} (hη : η ∈ Work.CharCore.Irr ↥H)
    (hηQ : ∀ x : ↥H, (x : G) ∈ Q → η x = 1) (hη1 : η ≠ (fun _ : ↥H => (1 : ℂ))) :
    Work.Induction.indFun H η ∈ Work.CharCore.Irr G ∧
    (Work.Induction.indFun H η) 1 = (Nat.card Q : ℂ) + 1 ∧
    (∀ y : ↥Q, (y : G) ≠ 1 → Work.Induction.indFun H η (y : G) = 1) ∧
    (∀ η' : ↥H → ℂ, η' ∈ Work.CharCore.Irr ↥H →
      (∀ x : ↥H, (x : G) ∈ Q → η' x = 1) → η' ≠ (fun _ : ↥H => (1 : ℂ)) →
      η' ≠ (fun x : ↥H => star (η x)) →
      Work.CharCore.cfInner (Work.Induction.indFun H η) (Work.Induction.indFun H η') =
        (if η = η' then 1 else 0)) := by
  classical
  -- `η` is linear with `η 1 = 1`
  have hηone : η 1 = 1 := hηQ 1 (by simp)
  have hηdeg : Work.CharCore.irrDeg η = 1 := by
    have hh := Work.CharCore.irrDeg_spec hη
    rw [hηone] at hh
    exact_mod_cast hh.symm
  obtain ⟨φ, hφ⟩ := (Work.CharCore.linear_char_iff_deg_one hη).mp hηdeg
  -- the set-up
  have ht2 : t * t = 1 := Work.ZassenhausPSL2.t_mul_t h
  have hinv : ∀ d : G, d ∈ (H ⊓ H.map (MulAut.conj t).toMonoidHom : Subgroup G) →
      t * d * t = d⁻¹ := by
    intro d hd
    exact twoPoint_conj_t_eq_inv h hz d (by
      simpa only [Submission.Blueprint.twoPoint, Submission.Blueprint.conj] using hd)
  have hcover : ∀ g : G, g ∈ H ∨ ∃ a b : H, g = (a : G) * t * (b : G) := doubleCoset_cover h
  have hDmap : ∀ d : ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom : Subgroup G),
      (MulAut.conj t) (d : G) ∈ (H ⊓ H.map (MulAut.conj t).toMonoidHom : Subgroup G) := by
    intro d
    have hd : (d : G) ∈ Submission.Blueprint.twoPoint H t := by
      simpa only [Submission.Blueprint.twoPoint, Submission.Blueprint.conj] using d.2
    have hh := Work.ZassenhausPSL2.dStab_conj_mem h hd
    simpa only [Submission.Blueprint.twoPoint, Submission.Blueprint.conj, MulAut.conj_apply,
      Work.ZassenhausPSL2.t_inv h] using hh
  have hKodd : Odd (Nat.card ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom : Subgroup G)) := by
    have hh := h.stronglyEmbedded.2.2 t h.not_mem
    simpa only [Submission.Blueprint.conj] using hh
  have hηc : Work.CharCore.IsClassFun η := Work.CharCore.isClassFun_of_mem_Irr hη
  -- the two-double-coset computation
  have key : ∀ η' : ↥H → ℂ, η' ∈ Work.CharCore.Irr ↥H →
      (∀ x : ↥H, (x : G) ∈ Q → η' x = 1) →
      Work.CharCore.cfInner (Work.Induction.indFun H η) (Work.Induction.indFun H η') =
        (if η = η' then 1 else 0) + (if η' = (fun x : ↥H => star (η x)) then 1 else 0) := by
    intro η' hη' hη'Q
    have hη'one : η' 1 = 1 := hη'Q 1 (by simp)
    have hη'deg : Work.CharCore.irrDeg η' = 1 := by
      have hh := Work.CharCore.irrDeg_spec hη'
      rw [hη'one] at hh
      exact_mod_cast hh.symm
    obtain ⟨ψ, hψ⟩ := (Work.CharCore.linear_char_iff_deg_one hη').mp hη'deg
    have hη'c : Work.CharCore.IsClassFun η' := Work.CharCore.isClassFun_of_mem_Irr hη'
    have hmackey := cfInner_indFun_twoClassFun_twoDoubleCoset (H := H) (t := t)
      ht2 h.not_mem
      hcover hDmap η η' hηc hη'c
    rw [hmackey]
    have hsum := sum_term_eq_sum_coe (H := H) (t := t) ht2 hinv hDmap hφ hψ hη'
    rw [hsum, inv_natCard_mul_sum_coe_eq_ite, Work.CharCore.irr_orthonormal η η' hη hη']
    by_cases hcase : η' = (fun x : ↥H => star (η x))
    · have hχ1 : ((φ * ψ).comp (dToH (H := H) (t := t))) = 1 :=
        comp_dToH_eq_one_of_eq_star hη hφ hψ hcase
      rw [if_pos hcase, if_pos hχ1]
    · have hχ1 : ((φ * ψ).comp (dToH (H := H) (t := t))) ≠ 1 := fun hc =>
        hcase (eq_star_of_comp_dToH_eq_one h hη hηQ hη'Q hφ hψ hc)
      rw [if_neg hcase, if_neg hχ1]
  -- `η` is not its own complex conjugate
  have hne_star : η ≠ (fun x : ↥H => star (η x)) := fun hconj =>
    sq_comp_dToH_ne_one h hKodd hηQ hη1 hφ (comp_dToH_eq_one_of_eq_star hη hφ hφ hconj)
  -- the norm of `Ind η`
  have hself : Work.CharCore.cfInner (Work.Induction.indFun H η) (Work.Induction.indFun H η)
      = 1 := by
    rw [key η hη hηQ]
    have h1 : (if η = η then (1 : ℂ) else 0) = 1 := if_pos rfl
    have h2 : (if η = (fun x : ↥H => star (η x)) then (1 : ℂ) else 0) = 0 := if_neg hne_star
    rw [h1, h2, add_zero]
  -- `Ind η` is an irreducible character of `G`
  have hvchar : Work.CharCore.IsVChar (Work.Induction.indFun H η) :=
    Work.Induction.isVChar_indFun (H := H) (φ := η)
      ((isVChar_of_fintype_congr (f := η)).mpr
        (Work.CharCore.IsChar.toVChar (Work.CharCore.IsChar.of_mem_Irr hη)))
  have hindIrr : Work.Induction.indFun H η ∈ Work.CharCore.Irr G := by
    obtain ⟨χ, hχ, hcase⟩ := Work.CharCore.vchar_norm_one hvchar hself
    rcases hcase with hcase | hcase
    · rwa [hcase]
    · exfalso
      have hdeg : (Work.Induction.indFun H η) 1 = (Nat.card Q : ℂ) + 1 :=
        indFun_apply_one_eq h hηQ
      have hzero : ((Nat.card Q + 1 + Work.CharCore.irrDeg χ : ℕ) : ℂ) = 0 := by
        have h1 : (Nat.card Q : ℂ) + 1 = -(χ 1) := by
          have hh := congrFun hcase 1
          rw [hdeg] at hh
          simpa using hh
        have h2 : (Nat.card Q : ℂ) + 1 + (Work.CharCore.irrDeg χ : ℂ) = 0 := by
          rw [Work.CharCore.irrDeg_spec hχ] at h1
          rw [h1]
          ring
        simpa using h2
      have hnat : Nat.card Q + 1 + Work.CharCore.irrDeg χ = 0 := Nat.cast_eq_zero.mp hzero
      omega
  refine ⟨hindIrr, indFun_apply_one_eq h hηQ, fun y hy => indFun_apply_mem_Q h hη hηQ y hy, ?_⟩
  intro η' hη' hη'Q hη'1 hη'conj
  rw [key η' hη' hη'Q]
  have h2 : (if η' = (fun x : ↥H => star (η x)) then (1 : ℂ) else 0) = 0 := if_neg hη'conj
  rw [h2, add_zero]

end Work.ZassenhausTwoGroup
